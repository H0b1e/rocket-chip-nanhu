// See LICENSE.SiFive for license details.

package freechips.rocketchip.devices.tilelink

import chisel3._
import chisel3.experimental._
import chisel3.util._

import org.chipsalliance.cde.config._
import org.chipsalliance.diplomacy.lazymodule._

import freechips.rocketchip.diplomacy.{AddressSet}
import freechips.rocketchip.resources.{Description, Resource, ResourceBinding, ResourceBindings, ResourceInt, SimpleDevice}
import freechips.rocketchip.interrupts.{IntNexusNode, IntSinkParameters, IntSinkPortParameters, IntSourceParameters, IntSourcePortParameters}
import freechips.rocketchip.regmapper.{RegField, RegFieldDesc, RegFieldRdAction, RegFieldWrType, RegReadFn, RegWriteFn}
import freechips.rocketchip.subsystem.{BaseSubsystem, CBUS, TLBusWrapperLocation}
import freechips.rocketchip.tilelink.{TLFragmenter, TLRegisterNode}
import freechips.rocketchip.util.{MuxT, property}

import scala.math.min

import freechips.rocketchip.util.UIntToAugmentedUInt
import freechips.rocketchip.util.SeqToAugmentedSeq

class GatewayPLICIO extends Bundle {
  val valid = Output(Bool())
  val ready = Input(Bool())
  val complete = Input(Bool())
}

class LevelGateway extends Module {
  val io = IO(new Bundle {
    val interrupt = Input(Bool())
    val plic = new GatewayPLICIO
  })

  val inFlight = RegInit(false.B)
  when (io.interrupt && io.plic.ready) { inFlight := true.B }
  when (io.plic.complete) { inFlight := false.B }
  io.plic.valid := io.interrupt && !inFlight
}

object PLICConsts
{
  def maxDevices = 1023
  def maxMaxHarts = 15872
  def priorityBase = 0x0
  def pendingBase = 0x1000
  def enableBase = 0x2000
  def hartBase = 0x200000

  def claimOffset = 4
  def priorityBytes = 4

  def enableOffset(i: Int) = i * ((maxDevices+7)/8)
  def hartOffset(i: Int) = i * 0x1000
  def enableBase(i: Int):Int = enableOffset(i) + enableBase
  def hartBase(i: Int):Int = hartOffset(i) + hartBase

  def size(maxHarts: Int): Int = {
    require(maxHarts > 0 && maxHarts <= maxMaxHarts, s"Must be: maxHarts=$maxHarts > 0 && maxHarts <= PLICConsts.maxMaxHarts=${PLICConsts.maxMaxHarts}")
    1 << log2Ceil(hartBase(maxHarts))
  }

  require(hartBase >= enableBase(maxMaxHarts))
}

/* Secure interrupt extension register offsets (PLIC_S_IRQ spec).
 * Carved out of the unused TL window between the enable array and hartBase.
 * All registers are M-mode only by convention; software protection comes from PMP.
 * Capacity limits (<=1023 sources, <=64 contexts / 32 harts) bound the reserved
 * address ranges only: registers are instantiated per actual config (2-core
 * tapeout gets 2 world_state / 4 irq_track regs). Offsets are deliberately
 * config-independent so one set of software constants covers all SoCs. */
object PLICSecConsts
{
  def secSrcBase     = 0x4000  // security attribute bitmap, 1 bit per source
  def secCtrlOffset  = 0x4100  // {lock, secure_routing_en}
  def worldStateBase = 0x4200  // per hart, 8-byte stride, up to 32 harts
  def wsAckBase      = 0x4400  // per hart, 8-byte stride, up to 32 harts
  def irqTrackBase   = 0x4600  // per context, 8-byte stride, up to 64 contexts
  def secStatusOffset= 0x4E00  // sticky error flags, W1C
}

case class PLICParams(baseAddress: BigInt = 0xC000000, maxPriorities: Int = 7, intStages: Int = 0, maxHarts: Int = PLICConsts.maxMaxHarts)
{
  require (maxPriorities >= 0)
  def address = AddressSet(baseAddress, PLICConsts.size(maxHarts)-1)
}

case object PLICKey extends Field[Option[PLICParams]](None)

case class PLICAttachParams(
  slaveWhere: TLBusWrapperLocation = CBUS
)

case object PLICAttachKey extends Field(PLICAttachParams())

/** Platform-Level Interrupt Controller */
class TLPLIC(params: PLICParams, beatBytes: Int)(implicit p: Parameters) extends LazyModule
{
  // plic0 => max devices 1023
  val device: SimpleDevice = new SimpleDevice("interrupt-controller", Seq("riscv,plic0")) {
    override val alwaysExtended = true
    override def describe(resources: ResourceBindings): Description = {
      val Description(name, mapping) = super.describe(resources)
      val extra = Map(
        "interrupt-controller" -> Nil,
        "riscv,ndev" -> Seq(ResourceInt(nDevices)),
        "riscv,max-priority" -> Seq(ResourceInt(nPriorities)),
        "#interrupt-cells" -> Seq(ResourceInt(1)))
      Description(name, mapping ++ extra)
    }
  }

  val node : TLRegisterNode = TLRegisterNode(
    address   = Seq(params.address),
    device    = device,
    beatBytes = beatBytes,
    undefZero = true,
    concurrency = 1) // limiting concurrency handles RAW hazards on claim registers

  val intnode: IntNexusNode = IntNexusNode(
    sourceFn = { _ => IntSourcePortParameters(Seq(IntSourceParameters(1, Seq(Resource(device, "int"))))) },
    sinkFn   = { _ => IntSinkPortParameters(Seq(IntSinkParameters())) },
    outputRequiresInput = false,
    inputRequiresOutput = false)

  /* Negotiated sizes */
  def nDevices: Int = intnode.edges.in.map(_.source.num).sum
  def minPriorities = min(params.maxPriorities, nDevices)
  def nPriorities = (1 << log2Ceil(minPriorities+1)) - 1 // round up to next 2^n-1
  def nHarts = intnode.edges.out.map(_.source.num).sum

  // Assign all the devices unique ranges
  lazy val sources = intnode.edges.in.map(_.source)
  lazy val flatSources = (sources zip sources.map(_.num).scanLeft(0)(_+_).init).map {
    case (s, o) => s.sources.map(z => z.copy(range = z.range.offset(o)))
  }.flatten

  ResourceBinding {
    flatSources.foreach { s => s.resources.foreach { r =>
      // +1 because interrupt 0 is reserved
      (s.range.start until s.range.end).foreach { i => r.bind(device, ResourceInt(i+1)) }
    } }
  }

  lazy val module = new Impl
  class Impl extends LazyModuleImp(this) {
    val (io_devices, edgesIn) = intnode.in.unzip
    val (io_harts, _) = intnode.out.unzip

    // Compact the interrupt vector the same way
    val interrupts = intnode.in.map { case (i, e) => i.take(e.source.num) }.flatten
    // This flattens the harts into an MSMSMSMSMS... or MMMMM.... sequence
    val harts = io_harts.flatten

    def getNInterrupts = interrupts.size

    println(s"Interrupt map (${nHarts} harts ${nDevices} interrupts):")
    flatSources.foreach { s =>
      // +1 because 0 is reserved, +1-1 because the range is half-open
      println(s"  [${s.range.start+1}, ${s.range.end}] => ${s.name}")
    }
    println("")

    require (nDevices == interrupts.size, s"Must be: nDevices=$nDevices == interrupts.size=${interrupts.size}")
    require (nHarts == harts.size, s"Must be: nHarts=$nHarts == harts.size=${harts.size}")

    require(nDevices <= PLICConsts.maxDevices, s"Must be: nDevices=$nDevices <= PLICConsts.maxDevices=${PLICConsts.maxDevices}")
    require(nHarts > 0 && nHarts <= params.maxHarts, s"Must be: nHarts=$nHarts > 0 && nHarts <= PLICParams.maxHarts=${params.maxHarts}")

    // For now, use LevelGateways for all TL2 interrupts
    val gateways = interrupts.map { case i =>
      val gateway = Module(new LevelGateway)
      gateway.io.interrupt := i
      gateway.io.plic
    }

    val prioBits = log2Ceil(nPriorities+1)
    val priority =
      if (nPriorities > 0) RegInit(VecInit(Seq.fill(nDevices)(0.U(prioBits.W))))
      else WireDefault(VecInit.fill(nDevices max 1)(1.U))
    val threshold =
      if (nPriorities > 0) RegInit(VecInit(Seq.fill(nHarts)(0.U(prioBits.W))))
      else WireDefault(VecInit.fill(nHarts)(0.U))
    val pending = RegInit(VecInit.fill(nDevices max 1){false.B})

    /* Construct the enable registers, chunked into 8-bit segments to reduce verilog size */
    val firstEnable = nDevices min 7
    val fullEnables = (nDevices - firstEnable) / 8
    val tailEnable  = nDevices - firstEnable - 8*fullEnables
    def enableRegs = (RegInit(0.U(firstEnable.W)) +:
                      Seq.fill(fullEnables) { RegInit(0.U(8.W)) }) ++
                     (if (tailEnable > 0) Some(RegInit(0.U(tailEnable.W))) else None)
    val enables = Seq.fill(nHarts) { enableRegs }
    val enableVec = VecInit(enables.map(x => Cat(x.reverse)))
    val enableVec0 = VecInit(enableVec.map(x => Cat(x, 0.U(1.W))))

    /* ------------------------------------------------------------------ *
     * Secure interrupt extension (PLIC_S_IRQ spec):
     *  - secSrc(i)   : security attribute of source i+1 (0=NS, 1=secure)
     *  - secCtrl     : {lock, secure_routing_en}; routing is legacy
     *                  pass-through until secure_routing_en is set
     *  - worldState  : per-hart S-world mirror (0=REE, 1=TEE); hart h's
     *                  M-context (2h) and S-context (2h+1) share entry h
     *  - irqTrack(c) : per-context in-service state {15:2 irq_id, 1 req_sec, 0 in_service}
     *  - secStatus   : sticky error flags for rejected completes
     * ------------------------------------------------------------------ */
    val nRealHarts    = (nHarts + 1) / 2
    // sec_src is stored as fixed 8-bit chunks (mirrors the enables layout) so
    // every write path is a whole-chunk connect; the lock freezes all chunks
    require(nDevices % 8 == 0,
      s"Must be: nDevices=${nDevices} must be a multiple of 8 (sec_src byte-chunk layout)")
    val secSrcChunks     = Seq.fill(nDevices / 8) { RegInit(0.U(8.W)) }
    val secSrcChunksNext = secSrcChunks.map(c => WireDefault(c))
    (secSrcChunks zip secSrcChunksNext).foreach { case (c, n) => c := n }
    val secSrc        = Cat(secSrcChunks.reverse)  // bit i <-> source i+1
    val secCtrl       = RegInit(0.U(2.W))
    val secEnable     = secCtrl(0)  // 1: security routing active, 0: legacy pass-through
    val secLocked     = secCtrl(1)  // 1: security config frozen until reset (W1T)
    val secCtrlNext   = WireDefault(secCtrl)
    secCtrl := secCtrlNext
    // decoupled write port filled by the sec_ctrl register field below
    val secCtrlWrValid = WireDefault(false.B)
    val secCtrlWrData  = WireDefault(0.U(2.W))
    when (secCtrlWrValid) {
      // bit1 (lock) is W1T sticky; bit0 (routing enable) is writable until locked
      secCtrlNext := Cat(secCtrl(1) | secCtrlWrData(1),
                         Mux(secLocked, secCtrl(0), secCtrlWrData(0)))
    }
    // world_state resets to TEE, matching core-side mws: boot order is
    // OpenSBI -> TEE init -> REE init, so the machine comes up secure.
    val worldState    = RegInit(VecInit(Seq.fill(nRealHarts)(true.B)))
    val irqTrack      = RegInit(VecInit(Seq.fill(nHarts)(0.U(32.W))))
    val secStatus     = RegInit(0.U(4.W))
    val secCompleteReject = WireDefault(false.B)
    // sticky bit0 latches rejected completes (whole-word form: Chisel 6 forbids
    // bit-slice reassignment); W1C clears via the register field below
    val secStatusNext = WireDefault(Cat(secStatus(3, 1), secStatus(0) | secCompleteReject))
    secStatus := secStatusNext

    require (log2Ceil(nDevices + 1) <= 14,
      s"Must be: log2Ceil(nDevices+1)=${log2Ceil(nDevices + 1)} <= 14 (irqTrack irq_id field)")
    require (PLICConsts.enableBase(nHarts) <= PLICSecConsts.secSrcBase,
      s"Must be: PLICConsts.enableBase(${nHarts})=${PLICConsts.enableBase(nHarts)} <= PLICSecConsts.secSrcBase=${PLICSecConsts.secSrcBase}")
    require (PLICSecConsts.irqTrackBase + 8 * nHarts <= PLICSecConsts.secStatusOffset,
      s"irq_track region must not overlap sec_status (nHarts=${nHarts} too large)")
    require (PLICSecConsts.worldStateBase + 8 * nRealHarts <= PLICSecConsts.wsAckBase,
      s"world_state region must not overlap ws_ack (nRealHarts=${nRealHarts} too large)")

    val maxDevs = Reg(Vec(nHarts, UInt(log2Ceil(nDevices+1).W)))
    val pendingUInt = Cat(pending.reverse)
    // Security attribute indexed by PLIC id; bit 0 (reserved id 0) reads 0
    val secSrcById = Cat(0.U(1.W), secSrc)
    // Hart-wide secure busy: any context (M=2h, S=2h+1) of hart h servicing a
    // secure interrupt. The M-context mask uses it so that non-secure sources
    // cannot even trap into M while TEE services a secure interrupt claimed
    // directly on the S-context (hardware non-preemption, PLIC_S_IRQ §5).
    val secBusyOfCtx = VecInit((0 until nHarts).map(c => irqTrack(c)(0) && irqTrack(c)(1)))
    val secBusyHart  = VecInit(Seq.tabulate(nRealHarts) { h =>
      val mBusy = secBusyOfCtx(2 * h)
      val sBusy = if (2 * h + 1 < nHarts) secBusyOfCtx(2 * h + 1) else false.B
      mBusy || sBusy
    })
    if(nDevices > 0) {
      for (hart <- 0 until nHarts) {
        val fanin = Module(new PLICFanIn(nDevices, prioBits))
        fanin.io.prio := priority
        // Route mask per PLIC_S_IRQ §5:
        //   S-world ctx (odd):  to_S  = (sec_src == world_state)
        //   M ctx (even):       to_M  = ~to_S & ~(sec_busy_hart & ~sec_src)
        // When secure routing is disabled every source passes (legacy PLIC).
        val hartIdx     = hart / 2
        val isSecureCtx = (hart % 2) == 1
        val toS = Mux(worldState(hartIdx), secSrc, ~secSrc)
        // to_M = ~to_S & ~(sec_busy_hart & ~sec_src): while any context of
        // this hart services a secure interrupt, non-secure sources are
        // blocked at M (no M-mode trap until the matching complete)
        val toM = ~toS & Mux(secBusyHart(hartIdx), secSrc, Fill(nDevices, 1.U(1.W)))
        val ctxRoute = if (isSecureCtx) toS else toM
        fanin.io.ip := enableVec(hart) & pendingUInt &
                       Mux(secEnable, ctxRoute, Fill(nDevices, 1.U(1.W)))
        maxDevs(hart) := fanin.io.dev
        harts(hart) := ShiftRegister(RegNext(fanin.io.max) > threshold(hart), params.intStages)
      }
    }

    // Priority registers are 32-bit aligned so treat each as its own group.
    // Otherwise, the off-by-one nature of the priority registers gets confusing.
    require(PLICConsts.priorityBytes == 4,
      s"PLIC Priority register descriptions assume 32-bits per priority, not ${PLICConsts.priorityBytes}")

    def priorityRegDesc(i: Int) =
      RegFieldDesc(
        name      = s"priority_$i",
        desc      = s"Acting priority of interrupt source $i",
        group     = Some(s"priority_${i}"),
        groupDesc = Some(s"Acting priority of interrupt source ${i}"),
        reset     = if (nPriorities > 0) None else Some(1))

    def pendingRegDesc(i: Int) =
      RegFieldDesc(
        name      = s"pending_$i",
        desc      = s"Set to 1 if interrupt source $i is pending, regardless of its enable or priority setting.",
        group     = Some("pending"),
        groupDesc = Some("Pending Bit Array. 1 Bit for each interrupt source."),
        volatile = true)

    def enableRegDesc(i: Int, j: Int, wide: Int) = {
      val low = if (j == 0) 1 else j*8
      val high = low + wide - 1
      RegFieldDesc(
        name      = s"enables_${j}",
        desc      = s"Targets ${low}-${high}. Set bits to 1 if interrupt should be enabled.",
        group     = Some(s"enables_${i}"),
        groupDesc = Some(s"Enable bits for each interrupt source for target $i. 1 bit for each interrupt source."))
    }

    def priorityRegField(x: UInt, i: Int) =
      if (nPriorities > 0) {
        RegField(prioBits, x, priorityRegDesc(i))
      } else {
        RegField.r(prioBits, x, priorityRegDesc(i))
      }

    val priorityRegFields = priority.zipWithIndex.map { case (p, i) =>
      PLICConsts.priorityBase+PLICConsts.priorityBytes*(i+1) ->
      Seq(priorityRegField(p, i+1)) }
    val pendingRegFields = Seq(PLICConsts.pendingBase ->
      (RegField(1) +: pending.zipWithIndex.map { case (b, i) => RegField.r(1, b, pendingRegDesc(i+1))}))
    val enableRegFields = enables.zipWithIndex.map { case (e, i) =>
      PLICConsts.enableBase(i) -> (RegField(1) +: e.zipWithIndex.map { case (x, j) =>
        RegField(x.getWidth, x, enableRegDesc(i, j, x.getWidth)) }) }

    // When a hart reads a claim/complete register, then the
    // device which is currently its highest priority is no longer pending.
    // This code exploits the fact that, practically, only one claim/complete
    // register can be read at a time. We check for this because if the address map
    // were to change, it may no longer be true.
    // Note: PLIC doesn't care which hart reads the register.
    val claimer = Wire(Vec(nHarts, Bool()))
    assert((claimer.asUInt & (claimer.asUInt - 1.U)) === 0.U) // One-Hot
    val claiming = Seq.tabulate(nHarts){i => Mux(claimer(i), maxDevs(i), 0.U)}.reduceLeft(_|_)
    val claimedDevs = VecInit(UIntToOH(claiming, nDevices+1).asBools)

    // Latch per-context in-service state on claim (PLIC_S_IRQ §7).
    // {15:2 irq_id, 1 req_sec, 0 in_service}; id 0 (nothing claimable) does not latch.
    val trackIdBits = log2Ceil(nDevices + 1)
    for (i <- 0 until nHarts) {
      when (claimer(i) && maxDevs(i) =/= 0.U) {
        irqTrack(i) := Cat(0.U((30 - trackIdBits).W), maxDevs(i),
                           secSrcById(maxDevs(i)), 1.U(1.W))
      }
    }

    ((pending zip gateways) zip claimedDevs.tail) foreach { case ((p, g), c) =>
      g.ready := !p
      when (c || g.valid) { p := !c }
    }

    // When a hart writes a claim/complete register, then
    // the written device (as long as it is actually enabled for that
    // hart) is marked complete.
    // This code exploits the fact that, practically, only one claim/complete register
    // can be written at a time. We check for this because if the address map
    // were to change, it may no longer be true.
    // Note -- PLIC doesn't care which hart writes the register.
    val completer = Wire(Vec(nHarts, Bool()))
    assert((completer.asUInt & (completer.asUInt - 1.U)) === 0.U) // One-Hot
    val completerDev = Wire(UInt(log2Up(nDevices + 1).W))
    val completedDevs = Mux(completer.reduce(_ || _), UIntToOH(completerDev, nDevices+1), 0.U)
    (gateways zip completedDevs.asBools.tail) foreach { case (g, c) =>
       g.complete := c
    }

    def thresholdRegDesc(i: Int) =
      RegFieldDesc(
        name = s"threshold_$i",
        desc = s"Interrupt & claim threshold for target $i. Maximum value is ${nPriorities}.",
        reset    = if (nPriorities > 0) None else Some(1))

    def thresholdRegField(x: UInt, i: Int) =
      if (nPriorities > 0) {
        RegField(prioBits, x, thresholdRegDesc(i))
      } else {
        RegField.r(prioBits, x, thresholdRegDesc(i))
      }

    val hartRegFields = Seq.tabulate(nHarts) { i =>
      PLICConsts.hartBase(i) -> Seq(
        thresholdRegField(threshold(i), i),
        RegField(32-prioBits),
        RegField(32,
          RegReadFn { valid =>
            claimer(i) := valid
            (true.B, maxDevs(i))
          },
          RegWriteFn { (valid, data) =>
            assert(Mux(valid, completerDev === data.extract(log2Ceil(nDevices+1)-1, 0), true.B),
                   "completerDev should be consistent for all harts")
            completerDev := data.extract(log2Ceil(nDevices+1)-1, 0)
            // Complete check (PLIC_S_IRQ §7): data bit31 carries the NS/S flag
            // supplied by the completer. The write is honored only when it
            // matches the state latched at claim time (in_service, id, sec).
            // Legacy (secure routing disabled) keeps the unfiltered behavior.
            val completeReqSec = data(31)
            val trackOk = irqTrack(i)(0) &&
                          irqTrack(i)(15, 2) === completerDev &&
                          irqTrack(i)(1) === completeReqSec
            val completeAccept = valid && enableVec0(i)(completerDev) &&
                                 (!secEnable || trackOk)
            completer(i) := completeAccept
            when (completeAccept) {
              irqTrack(i) := irqTrack(i) & ~1.U(32.W) // clear in_service
            }
            when (valid && !completeAccept && secEnable) {
              secCompleteReject := true.B // empty / replay / id or flag mismatch
            }
            true.B
          },
          Some(RegFieldDesc(s"claim_complete_$i",
            s"Claim/Complete register for Target $i. Reading this register returns the claimed interrupt number and makes it no longer pending." +
            s"Writing the interrupt number back completes the interrupt.",
            reset = None,
            wrType = Some(RegFieldWrType.MODIFY),
            rdAction = Some(RegFieldRdAction.MODIFY),
            volatile = true))
        )
      )
    }

    /* ------------------ Security extension fields (PLIC_S_IRQ) ------------------ */

    // sec_src bitmap, one 8-bit field per chunk; writes ignored once locked
    def secSrcField(b: Int): RegField = {
      val lo = b * 8
      RegField(8,
        RegReadFn { _ => (true.B, secSrcChunks(b)) },
        RegWriteFn { (valid, data) =>
          when (valid && !secLocked) { secSrcChunksNext(b) := data }
          true.B
        },
        Some(RegFieldDesc(s"sec_src_$b",
          s"Security attribute of interrupt sources ${lo+1}-${lo+8}. 1=secure, 0=non-secure. Read-only after lock.",
          group = Some("sec_src"),
          groupDesc = Some("Security attribute per interrupt source."))))
    }
    val secSrcRegField = PLICSecConsts.secSrcBase ->
      (0 until nDevices / 8).map(secSrcField)

    // sec_ctrl: routing enable is lockable, lock itself is W1T sticky
    val secCtrlRegField = PLICSecConsts.secCtrlOffset -> Seq(RegField(2,
      RegReadFn { _ => (true.B, secCtrl) },
      RegWriteFn { (valid, data) =>
        when (valid) {
          secCtrlWrValid := true.B
          secCtrlWrData  := data(1, 0)
        }
        true.B
      },
      Some(RegFieldDesc("sec_ctrl",
        "bit0: enable security routing (0=legacy pass-through). bit1: lock security config (W1T).",
        group = Some("security"),
        groupDesc = Some("Secure interrupt routing control.")))))

    // world_state per hart; ws_ack echoes the committed value one cycle later
    val wsEcho = RegNext(worldState)
    val wsDone = VecInit((0 until nRealHarts).map(h => RegNext(wsEcho(h) === worldState(h))))
    val worldStateRegFields = Seq.tabulate(nRealHarts) { h =>
      PLICSecConsts.worldStateBase + 8 * h -> Seq(RegField(1, worldState(h),
        RegFieldDesc(s"world_state_$h",
          s"S-world of hart $h mirrored in PLIC (0=REE, 1=TEE). Write only on a real world switch.",
          group = Some("security"))))
    }
    val wsAckRegFields = Seq.tabulate(nRealHarts) { h =>
      PLICSecConsts.wsAckBase + 8 * h -> Seq(RegField.r(8, Cat(wsDone(h), 0.U(6.W), wsEcho(h)),
        RegFieldDesc(s"ws_ack_$h",
          "bit0: committed world_state echo; bit7: echo stable (hardware ACK for the world switch).",
          group = Some("security"),
          volatile = true)))
    }

    // irq_track read-only debug/observability per context
    val irqTrackRegFields = Seq.tabulate(nHarts) { i =>
      PLICSecConsts.irqTrackBase + 8 * i -> Seq(RegField.r(32, irqTrack(i),
        RegFieldDesc(s"irq_track_$i",
          s"In-service tracking of context $i: {15:2 irq_id, 1 req_sec, 0 in_service}.",
          group = Some("security"),
          volatile = true)))
    }

    // sec_status: sticky error flags, write-1-to-clear.
    // Reads the register (not secStatusNext) to avoid a combinational loop
    // through the regmapper write path; a reject coincident with the W1C
    // write is dropped, which is harmless.
    val secStatusRegField = PLICSecConsts.secStatusOffset -> Seq(RegField(4,
      RegReadFn { _ => (true.B, secStatus) },
      RegWriteFn { (valid, data) =>
        when (valid) { secStatusNext := secStatus & ~data(3, 0) }
        true.B
      },
      Some(RegFieldDesc("sec_status",
        "bit0: complete rejected (no in-service interrupt / id or security mismatch / replay). W1C.",
        group = Some("security"),
        volatile = true))))

    node.regmap((priorityRegFields ++ pendingRegFields ++ enableRegFields ++ hartRegFields ++
      Seq(secSrcRegField, secCtrlRegField) ++ worldStateRegFields ++ wsAckRegFields ++
      irqTrackRegFields :+ secStatusRegField):_*)

    if (nDevices >= 2) {
      val claimed = claimer(0) && maxDevs(0) > 0.U
      val completed = completer(0)
      property.cover(claimed && RegEnable(claimed, false.B, claimed || completed), "TWO_CLAIMS", "two claims with no intervening complete")
      property.cover(completed && RegEnable(completed, false.B, claimed || completed), "TWO_COMPLETES", "two completes with no intervening claim")

      val ep = enables(0).asUInt & pending.asUInt
      val ep2 = RegNext(ep)
      val diff = ep & ~ep2
      property.cover((diff & (diff - 1.U)) =/= 0.U, "TWO_INTS_PENDING", "two enabled interrupts became pending on same cycle")

      if (nPriorities > 0)
        ccover(maxDevs(0) > (1.U << priority(0).getWidth) && maxDevs(0) <= Cat(1.U, threshold(0)),
               "THRESHOLD", "interrupt pending but less than threshold")
    }

    def ccover(cond: Bool, label: String, desc: String)(implicit sourceInfo: SourceInfo) =
      property.cover(cond, s"PLIC_$label", "Interrupts;;" + desc)
  }
}

class PLICFanIn(nDevices: Int, prioBits: Int) extends Module {
  val io = IO(new Bundle {
    val prio = Flipped(Vec(nDevices, UInt(prioBits.W)))
    val ip   = Flipped(UInt(nDevices.W))
    val dev  = UInt(log2Ceil(nDevices+1).W)
    val max  = UInt(prioBits.W)
  })

  def findMax(x: Seq[UInt]): (UInt, UInt) = {
    if (x.length > 1) {
      val half = 1 << (log2Ceil(x.length) - 1)
      val left = findMax(x take half)
      val right = findMax(x drop half)
      MuxT(left._1 >= right._1, left, (right._1, half.U | right._2))
    } else (x.head, 0.U)
  }

  val effectivePriority = (1.U << prioBits) +: (io.ip.asBools zip io.prio).map { case (p, x) => Cat(p, x) }
  val (maxPri, maxDev) = findMax(effectivePriority)
  io.max := maxPri // strips the always-constant high '1' bit
  io.dev := maxDev
}

/** Trait that will connect a PLIC to a subsystem */
trait CanHavePeripheryPLIC { this: BaseSubsystem =>
  val (plicOpt, plicDomainOpt) = p(PLICKey).map { params =>
    val tlbus = locateTLBusWrapper(p(PLICAttachKey).slaveWhere)
    val plicDomainWrapper = tlbus.generateSynchronousDomain("PLIC").suggestName("plic_domain")

    val plic = plicDomainWrapper { LazyModule(new TLPLIC(params, tlbus.beatBytes)) }
    plicDomainWrapper { plic.node := tlbus.coupleTo("plic") { TLFragmenter(tlbus, Some("PLIC")) := _ } }
    plicDomainWrapper { plic.intnode :=* ibus.toPLIC }

    (plic, plicDomainWrapper)
  }.unzip
}
