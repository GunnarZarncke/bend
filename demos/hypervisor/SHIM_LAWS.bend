# hypervisor: the laws of the trap shim (hv_state.c), over Isa.bend. The
# human states them; SHIM_PROOF.bend proves them by running the shim's
# words on the semantics. Every register and memory value is a variable;
# the addresses are the layout's: the area of guest g in the persist
# region, the host stack at Shim.stack().
#
# DRAFT: stated by the AI for PLAN.md, workstream 3, for the human's
# review. `bend SHIM_PROOF.bend --verdict` checks them: the kernel spends
# only its fuel per def, so each run is cut into segments in
# Segments.bend, which gen_seg.sh writes (SPEC.md, section 14).

import Base
import ./main.bend as Hv
import ./Isa.bend as Isa
import ./Shim.bend as Shim

# LAW: hv_enter, from its call with guest g's area, reaches the guest at
# the EL and PSTATE its SPSR names, its pc at ELR, x0..x30, SP_EL1,
# SP_EL0 and the 17 EL1 registers loaded from the area, TPIDR_EL2 naming
# the area, and the host's callee-saved registers and stack pointer saved
law shim_enter:
  for +g   : U32
  for sg   : Hv.Slot(g)
  for +h   : Shim.Host
  for +nzcv: U32
  for +daif: U32
  for +sys : List<&2, Isa.Sr>
  for +mem : List<&2, Isa.Cell>
  for +f   : Shim.Saved
  for +s2  : Hv.Tree<Bool>
  {Shim.entered(Isa.steps(68n, Isa.Run{Shim.enter_state(g, h, nzcv, daif, sys, mem, f, s2)})) == Shim.entered.want(g, h, f) : Maybe<&2, Shim.Entered>}

# LAW: a synchronous exception from guest g, from the vector through the
# save and hv_exit, stores the guest's registers and the exception's
# syndrome in the area, restores the host's registers and stack, and
# returns to hv_enter's caller with kind 0
law shim_exit_sync:
  for +g   : U32
  for sg   : Hv.Slot(g)
  for +h   : Shim.Host
  for +nzcv: U32
  for +sys : List<&2, Isa.Sr>
  for +mem : List<&2, Isa.Cell>
  for +f   : Shim.Saved
  for +s2  : Hv.Tree<Bool>
  {Shim.exited(g, Isa.steps(80n, Isa.Run{Shim.exit_state(g, 1024, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(0, h, f) : Maybe<&2, Shim.Exited>}

# LAW: the same for an interrupt, with kind 1
law shim_exit_irq:
  for +g   : U32
  for sg   : Hv.Slot(g)
  for +h   : Shim.Host
  for +nzcv: U32
  for +sys : List<&2, Isa.Sr>
  for +mem : List<&2, Isa.Cell>
  for +f   : Shim.Saved
  for +s2  : Hv.Tree<Bool>
  {Shim.exited(g, Isa.steps(80n, Isa.Run{Shim.exit_state(g, 1152, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(1, h, f) : Maybe<&2, Shim.Exited>}

# The decode
# ----------
# hv_decide, from its call with the ESR, the FAR, the HPFAR and the area,
# answers the exit's kind in x0 and, for a stage-2 abort, the address it
# faulted at in x1, and returns. Its five arms are five laws, because the
# run branches on the exception class the ESR holds, and the class is
# what each law assumes. The four here read no memory and write none, so
# they hold for any area; the fifth is below.

# LAW: an HVC from the guest is kind 1, and no address
law shim_decide_hvc:
  for +esr  : Hv.W64
  for +cls  : {Hv.W64{0, 22} == Isa.W.shr_by(esr, 26) : Hv.W64}
  for +fault: Hv.W64
  for +hpfar: Hv.W64
  for +ar   : Hv.W64
  for +h    : Shim.Host
  for +nzcv : U32
  for +daif : U32
  for +sys  : List<&2, Isa.Sr>
  for +mem  : List<&2, Isa.Cell>
  for +s2   : Hv.Tree<Bool>
  for +lr   : Hv.W64
  {Shim.decided(Isa.steps(10n, Isa.Run{Shim.decide_state(esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr)})) == Shim.decided.want(1, Isa.W.of(0), lr) : Maybe<&2, Shim.Decided>}

# LAW: a stage-2 abort on a load or store is kind 2, and the address is
# the block HPFAR names with the offset FAR holds
law shim_decide_data:
  for +esr  : Hv.W64
  for +cls  : {Hv.W64{0, 36} == Isa.W.shr_by(esr, 26) : Hv.W64}
  for +fault: Hv.W64
  for +hpfar: Hv.W64
  for +ar   : Hv.W64
  for +h    : Shim.Host
  for +nzcv : U32
  for +daif : U32
  for +sys  : List<&2, Isa.Sr>
  for +mem  : List<&2, Isa.Cell>
  for +s2   : Hv.Tree<Bool>
  for +lr   : Hv.W64
  {Shim.decided(Isa.steps(18n, Isa.Run{Shim.decide_state(esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr)})) == Shim.decided.want(2, Shim.fault_at(fault, hpfar), lr) : Maybe<&2, Shim.Decided>}

# LAW: a stage-2 abort on a fetch is kind 3, and the same address
law shim_decide_inst:
  for +esr  : Hv.W64
  for +cls  : {Hv.W64{0, 32} == Isa.W.shr_by(esr, 26) : Hv.W64}
  for +fault: Hv.W64
  for +hpfar: Hv.W64
  for +ar   : Hv.W64
  for +h    : Shim.Host
  for +nzcv : U32
  for +daif : U32
  for +sys  : List<&2, Isa.Sr>
  for +mem  : List<&2, Isa.Cell>
  for +s2   : Hv.Tree<Bool>
  for +lr   : Hv.W64
  {Shim.decided(Isa.steps(20n, Isa.Run{Shim.decide_state(esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr)})) == Shim.decided.want(3, Shim.fault_at(fault, hpfar), lr) : Maybe<&2, Shim.Decided>}

# LAW: any other class is kind 5, the kind the kernel stops a guest for,
# and no address
law shim_decide_other:
  for +esr  : Hv.W64
  for +cls  : {Hv.W64{0, 24} == Isa.W.shr_by(esr, 26) : Hv.W64}
  for +fault: Hv.W64
  for +hpfar: Hv.W64
  for +ar   : Hv.W64
  for +h    : Shim.Host
  for +nzcv : U32
  for +daif : U32
  for +sys  : List<&2, Isa.Sr>
  for +mem  : List<&2, Isa.Cell>
  for +s2   : Hv.Tree<Bool>
  for +lr   : Hv.W64
  {Shim.decided(Isa.steps(15n, Isa.Run{Shim.decide_state(esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr)})) == Shim.decided.want(5, Isa.W.of(0), lr) : Maybe<&2, Shim.Decided>}

# LAW: a trapped instruction of the guest's own (class 1) is kind 4, and
# the one arm that writes: it steps the guest's ELR in its area past the
# instruction that trapped, so that the guest resumes after it
law shim_decide_own:
  for +g    : U32
  for sg    : Hv.Slot(g)
  for +esr  : Hv.W64
  for +cls  : {Hv.W64{0, 1} == Isa.W.shr_by(esr, 26) : Hv.W64}
  for +fault: Hv.W64
  for +hpfar: Hv.W64
  for +elr  : Hv.W64
  for +h    : Shim.Host
  for +nzcv : U32
  for +daif : U32
  for +sys  : List<&2, Isa.Sr>
  for +mem  : List<&2, Isa.Cell>
  for +s2   : Hv.Tree<Bool>
  for +lr   : Hv.W64
  {Shim.stepped(g, Isa.steps(19n, Isa.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(g), h, nzcv, daif, sys, Isa.Cell{Shim.at(Shim.area(g), 264), elr} <> mem, s2, lr)})) == Shim.stepped.want(elr, lr) : Maybe<&2, Shim.Stepped>}
