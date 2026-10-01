# The hypervisor laws.
# PROOF.bend proves them.
#
# The kernel laws are over main.bend: a saved window per slot, and a static partition. 
# The three guest-step laws are over Isa.bend: one instruction of a guest at EL1. 
# The kernel model records an owner per block; the instruction model has one stage-2 mask.
# What the hardware does under that mask and a saved register file is the axiom the model rests on (SPEC.md, section 2).
#
# A block has one owner. Two guests' masks share no block, and a Free or
# Hyp block is in no guest's mask. An exit, a schedule, a handoff, and a
# run leave the owners where they were.
#
# An exit changes the current guest's window by a function of that exit
# and that window. Every other slot stays, and scheduling writes no
# window. At the end of a run a guest's window is its own exits, in
# order, applied to the window it started with. The schedule may change
# which guest runs. A guest's window follows that guest's exits.
#
# A decision's action list is closed: one Enter, and it is last, or End
# and no Enter. The guest entered is the one put on the core, it is live,
# and the window is that vCPU's. Changing who is on the core commits that
# guest. A Stop names the guest who exited. A put prints that window's x0
# and stops no one. The guest count and the slice stay; the round-robin
# cursor may move. A handoff record round-trips.
#
# One instruction at EL1 writes no memory outside the guest's stage-2
# map, no system register but the guest's own and those an exception
# entry to EL2 writes, and not the map.

import Base
import ./main.bend as Hv
import ./Isa.bend as Isa

# LAW: two guests' stage-2 maps share no block: for every ownership tree
# and every two distinct guests, the masks the kernel commits are
# disjoint
law masks_disjoint:
  for +ps: Hv.Tree<Hv.Owner>
  for +g : U32
  for +h : U32
  for +ne: {U32.is_ne(g, h) == True{} : Bool}
  {Hv.disjoint(Hv.mask(ps, g), Hv.mask(ps, h)) == True{} : Bool}

# LAW: a decision changes only the current guest'ss vCPU. 
# Whatever exit the current guest takes, every other guest's saved window and live bit
# stay unchanged
law handle_frame:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +e : Hv.Exit
  for +g : U32
  for +ok: Hv.Machine.ok(m)
  for +sg: Hv.Slot(g)
  for ne : {U32.is_ne(g, Hv.Machine.cur(m)) == True{} : Bool}
  {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, m, e)), g) == Hv.vcpu_at(Hv.Machine.vcpus(m), g) : Hv.VCpu}

# LAW: the handoff record loses nothing: a well-formed machine, encoded
# and decoded, is the machine and kernel it was
law record_roundtrip:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +ok: Hv.Machine.ok(m)
  {Hv.decode_record(Hv.encode(k, m)) == Some{(k, m)} : Maybe<(Hv.Kernel & Hv.Machine)>}

# LAW: a decision keeps the machine well-formed, and keeps the partition:
# the blocks' owners after any exit stay the same
law handle_ok:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +e : Hv.Exit
  for +ok: Hv.Machine.ok(m)
  Hv.Machine.ok(Hv.Step.m(Hv.handle(k, m, e)))

law handle_pages:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +e : Hv.Exit
  for +ok: Hv.Machine.ok(m)
  {Hv.Machine.pages(Hv.Step.m(Hv.handle(k, m, e))) == Hv.Machine.pages(m) : Hv.Tree<Hv.Owner>}

# LAW: the current guest's exit changes its vCPU by VCpu.step, a function
# of the exit and that vCPU alone
law handle_own:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +e : Hv.Exit
  for +ok: Hv.Machine.ok(m)
  {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, m, e)), Hv.Machine.cur(m)) == Hv.VCpu.step(Hv.vcpu_at(Hv.Machine.vcpus(m), Hv.Machine.cur(m)), e) : Hv.VCpu}

# LAW: a decision enters the guest it puts on the core, with the window
# of that guest's vCPU, and nothing when no guest is live
law sched_enters_saved:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +ok: Hv.Machine.ok(m)
  {Hv.Step.entry(Hv.sched(k, m)) == Hv.Step.saved(Hv.sched(k, m)) : Maybe<&2, Hv.Entry>}

law handle_enters_saved:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +e : Hv.Exit
  for +ok: Hv.Machine.ok(m)
  {Hv.Step.entry(Hv.handle(k, m, e)) == Hv.Step.saved(Hv.handle(k, m, e)) : Maybe<&2, Hv.Entry>}

# LAW: a guest's vCPU at the end of a run is its vCPU at boot, stepped by
# the exits it took itself, in order: nothing another guest does, no
# timing and no handoff reaches it. Together with the entry laws, what a
# guest is entered with is a function of its own exits.
law run_view:
  for +fuel : Nat
  for +k    : Hv.Kernel
  for  m    : Hv.Machine
  for +ok   : Hv.Machine.ok(m)
  for +tr   : List<&2, Hv.Ev>
  for +a    : U32
  for +sa   : Hv.Slot(a)
  {Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(fuel, Hv.sched(k, m), tr))), a)
    == Hv.VCpu.steps(Hv.own_exits(a, Hv.Run.log(Hv.run(fuel, Hv.sched(k, m), tr))), Hv.vcpu_at(Hv.Machine.vcpus(m), a)) : Hv.VCpu}

# LAW: noninterference: two runs, from any two machines and over any two
# traces, in which guest A starts with the same vCPU and takes the same
# exits, end with the same vCPU for A
law noninterference:
  for +f1 : Nat
  for +k1 : Hv.Kernel
  for  m1 : Hv.Machine
  for +ok1: Hv.Machine.ok(m1)
  for +t1 : List<&2, Hv.Ev>
  for +f2 : Nat
  for +k2 : Hv.Kernel
  for  m2 : Hv.Machine
  for +ok2: Hv.Machine.ok(m2)
  for +t2 : List<&2, Hv.Ev>
  for +a  : U32
  for +sa : Hv.Slot(a)
  for same: {Hv.vcpu_at(Hv.Machine.vcpus(m1), a) == Hv.vcpu_at(Hv.Machine.vcpus(m2), a) : Hv.VCpu}
  for own : {Hv.own_exits(a, Hv.Run.log(Hv.run(f1, Hv.sched(k1, m1), t1))) == Hv.own_exits(a, Hv.Run.log(Hv.run(f2, Hv.sched(k2, m2), t2))) : List<&2, Hv.Exit>}
  {Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(f1, Hv.sched(k1, m1), t1))), a)
    == Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(f2, Hv.sched(k2, m2), t2))), a) : Hv.VCpu}

# LAW: a Free or Hyp block is in no guest's mask
law mask_skips_host:
  for +ps: Hv.Tree<Hv.Owner>
  for +g : U32
  {Hv.mask_skips(ps, g) == True{} : Bool}

# LAW: scheduling leaves the partition and every saved vCPU unchanged
law sched_pages:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +ok: Hv.Machine.ok(m)
  {Hv.Machine.pages(Hv.Step.m(Hv.sched(k, m))) == Hv.Machine.pages(m) : Hv.Tree<Hv.Owner>}

law sched_frame:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +ok: Hv.Machine.ok(m)
  for +g : U32
  for +sg: Hv.Slot(g)
  {Hv.vcpu_at(Hv.Step.vcpus(Hv.sched(k, m)), g) == Hv.vcpu_at(Hv.Machine.vcpus(m), g) : Hv.VCpu}

# LAW: a handoff of a well-formed machine, and a whole run, keep the partition
law handoff_pages:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +ok: Hv.Machine.ok(m)
  {Hv.Machine.pages(Hv.Step.m(Hv.handoff(k, m))) == Hv.Machine.pages(m) : Hv.Tree<Hv.Owner>}

law run_pages:
  for +fuel: Nat
  for +k   : Hv.Kernel
  for  m   : Hv.Machine
  for +ok  : Hv.Machine.ok(m)
  for +tr  : List<&2, Hv.Ev>
  {Hv.Machine.pages(Hv.Step.m(Hv.Run.s(Hv.run(fuel, Hv.sched(k, m), tr)))) == Hv.Machine.pages(m) : Hv.Tree<Hv.Owner>}

# LAW: a decision keeps the guest count and the slice. 
# The round-robin cursor is not part of the claim: scheduling advances it.
law sched_budget:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +ok: Hv.Machine.ok(m)
  {Hv.Step.budget(Hv.sched(k, m)) == Hv.Kernel.budget(k) : U32 & U32}

law handle_budget:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +e : Hv.Exit
  for +ok: Hv.Machine.ok(m)
  {Hv.Step.budget(Hv.handle(k, m, e)) == Hv.Kernel.budget(k) : U32 & U32}

# LAW: the guest a schedule puts on the core is live.
# A schedule that enters no one is vacuously so.
# This establishes the invariant, with no liveness hypothesis: first_live
# answers Some only after reading that slot's live bit, and otherwise
# the step is Fin. With sched_enters_saved, the Enter names that guest.
law sched_enters_live:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +ok: Hv.Machine.ok(m)
  {Hv.on_core_live(Hv.sched(k, m)) == True{} : Bool}

# LAW: a decision preserves it, when the guest on the core was live.
# A put and an unknown call resume that guest and do not read the live
# bit, so the hypothesis is the one that makes them hold. Every other
# exit schedules or halts, and those establish it again. Fin is live by
# the predicate.
law handle_enters_live:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +e : Hv.Exit
  for +ok: Hv.Machine.ok(m)
  for lv : {Hv.VCpu.live(Hv.vcpu_at(Hv.Machine.vcpus(m), Hv.Machine.cur(m))) == True{} : Bool}
  {Hv.on_core_live(Hv.handle(k, m, e)) == True{} : Bool}

# LAW: a Go action list has one Enter and it is last; a Fin list has no Enter and ends in End
law sched_closed:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +ok: Hv.Machine.ok(m)
  {Hv.Step.closed(Hv.sched(k, m)) == True{} : Bool}

law handle_closed:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +e : Hv.Exit
  for +ok: Hv.Machine.ok(m)
  {Hv.Step.closed(Hv.handle(k, m, e)) == True{} : Bool}

# LAW: a decision that changes who is on the core commits that guest's map
law commit_on_switch:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +e : Hv.Exit
  for +ok: Hv.Machine.ok(m)
  for ne : {U32.is_ne(Hv.Machine.cur(m), Hv.Machine.cur(Hv.Step.m(Hv.handle(k, m, e)))) == True{} : Bool}
  {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.handle(k, m, e))), Hv.Step.acts(Hv.handle(k, m, e))) == True{} : Bool}

# LAW: a Stop names the guest who was current at the exit
law stop_self:
  for +k : Hv.Kernel
  for  m : Hv.Machine
  for +e : Hv.Exit
  for +ok: Hv.Machine.ok(m)
  {Hv.stops_self(Hv.Machine.cur(m), Hv.Step.acts(Hv.handle(k, m, e))) == True{} : Bool}

# LAW: a put prints the exiting window's x0 and does not stop a guest
law put_prints:
  for +k  : Hv.Kernel
  for  m  : Hv.Machine
  for +imm: U32
  for +r  : Hv.Regs
  for +ok : Hv.Machine.ok(m)
  for one : {U32.is_eq(imm, 1) == True{} : Bool}
  {Hv.put_obs(Hv.handle(k, m, Hv.Hvc{imm, r})) == (Some{Hv.char_of(Hv.Regs.x0(r))}, False{}) : Maybe<&2, String> & Bool}

# Obligations the kernel does not meet yet. The statements are the laws;
# the functions move until a proof can fill them. No proof is given here.
#
# LAW: a record decodes only as the encoding of an ok machine. Today an
# owner word other than 0 or 1 becomes Of of that word minus 2, a short
# list is already None, and words after a well-sized record are ignored.
# An owner word outside Free, Hyp, and slots 0..3 is None, and so is a
# list with anything after the record. record_roundtrip stays the other
# direction, for an ok machine.
law record_closed:
  for  ws : List<&2, U32>
  for +k  : Hv.Kernel
  for  m  : Hv.Machine
  for got : {Hv.decode_record(ws) == Some{(k, m)} : Maybe<(Hv.Kernel & Hv.Machine)>}
  Hv.Machine.ok(m) & {ws == Hv.encode(k, m) : List<&2, U32>}

# LAW: the boot the demo and the proofs run isolates its guests. For
# fewer than four guests, the machine is ok, and a guest id at or above
# that count owns no block. mask_skips_host already says a Free or Hyp
# block is in no guest's mask.
law boot_isolates:
  for +n : U32
  for +h : U32
  for lt : {U32.is_lt(n, 4) == True{} : Bool}
  for ge : {U32.is_lt(h, n) == False{} : Bool}
  Hv.Machine.ok(Hv.boot_machine(n)) & {Hv.disjoint(Hv.mask(Hv.Machine.pages(Hv.boot_machine(n)), h), Hv.mask(Hv.Machine.pages(Hv.boot_machine(n)), h)) == True{} : Bool}

# LAWS: the hardware axiom, now over Isa.bend (the ARM64 semantics that
# diff.sh checks against QEMU): one step of a guest at EL1 changes no
# doubleword of memory outside the guest's stage-2 map, no system register but the
# guest's own and those an exception entry to EL2 writes, and not the
# stage-2 map
law guest_step_memory:
  for +s  : Isa.State
  for +el1: {Isa.State.el(s) == 1 : U32}
  for +x  : Hv.W64
  for +ux : {Isa.mapped(Isa.State.s2(s), x) == False{} : Bool}
  {Isa.mem_read(Isa.State.mem(Isa.Out.s(Isa.step(s))), x) == Isa.mem_read(Isa.State.mem(s), x) : Hv.W64}

law guest_step_registers:
  for +s  : Isa.State
  for +el1: {Isa.State.el(s) == 1 : U32}
  for +e  : U32
  for +uo : {Isa.own_reg(e) == False{} : Bool}
  for +en : {Isa.entry_reg(e) == False{} : Bool}
  {Isa.sys_read(Isa.State.sys(Isa.Out.s(Isa.step(s))), e) == Isa.sys_read(Isa.State.sys(s), e) : Hv.W64}

law guest_step_stage2:
  for +s  : Isa.State
  for +el1: {Isa.State.el(s) == 1 : U32}
  {Isa.State.s2(Isa.Out.s(Isa.step(s))) == Isa.State.s2(s) : Hv.Tree<Bool>}
