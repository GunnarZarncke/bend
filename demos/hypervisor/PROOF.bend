# hypervisor: the proofs of LAWS.bend, by induction on the ownership
# list, the vCPU list and the guest indices. A computed value cannot be
# matched in place, so each decision is taken apart in a lemma of its
# own that receives the value as a parameter.

import Base
import ./main.bend as Hv
import ./LAWS.bend as Laws

# Masks
# -----

def and_false_r(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# a Bool clash: False is not True
def BoolT(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : BoolT(_)
  Unit{}

# x equals at most one of two distinct guests
def is_eq_both(x: Nat, g: Nat, h: Nat, +ne: {Nat.is_ne(g, h) == True{} : Bool}) -> {Bool.and(Nat.is_eq(x, g), Nat.is_eq(x, h)) == False{} : Bool}:
  match x g h:
    case 0n 0n 0n:
      Empty.absurd({Bool.and(Nat.is_eq(0n, 0n), Nat.is_eq(0n, 0n)) == False{} : Bool}, false_true(ne))
    case 0n 0n 1n+hp:
      {==}
    case 0n 1n+gp hh:
      {==}
    case 1n+xp 0n hh:
      {==}
    case 1n+xp 1n+gp 0n:
      and_false_r(Nat.is_eq(xp, gp))
    case 1n+xp 1n+gp 1n+hp:
      is_eq_both(xp, gp, hp, ne)

# no block owner is of two distinct guests
def is_of_none(o: Hv.Owner, g: Nat, h: Nat, +ne: {Nat.is_ne(g, h) == True{} : Bool}) -> {Bool.and(Bool.not(Bool.and(Hv.Owner.is_of(o, g), Hv.Owner.is_of(o, h))), True{}) == True{} : Bool}:
  match o:
    case Hv.Free{}:
      {==}
    case Hv.Hyp{}:
      {==}
    case Hv.Of{x}:
      %Equal.sym(Bool, Bool.and(Nat.is_eq(x, g), Nat.is_eq(x, h)), False{}, is_eq_both(x, g, h, ne)) : {Bool.and(Bool.not(_), True{}) == True{} : Bool}
      {==}

def Laws.masks_disjoint(ps, g, h, ne):
  match ps:
    case Nil{}:
      {==}
    case o <> t:
      %Equal.sym(Bool, Hv.disjoint(Hv.mask_of(t, g), Hv.mask_of(t, h)), True{}, Laws.masks_disjoint(t, g, h, ne)) : {Bool.and(Bool.not(Bool.and(Hv.Owner.is_of(o, g), Hv.Owner.is_of(o, h))), _) == True{} : Bool}
      is_of_none(o, g, h, ne)

# Frame
# -----
# every lemma says: a step that maps guest i's vCPU leaves guest j's as it
# was, for j != i; the law composes them along handle's branches

def vcpu_map_other(vs: List<&2, Hv.VCpu>, i: Nat, j: Nat, f: Hv.VCpu -> Hv.VCpu, +ne: {Nat.is_ne(j, i) == True{} : Bool}) -> {List.get(&2, Hv.VCpu, Hv.vcpu_map(vs, i, f), j) == List.get(&2, Hv.VCpu, vs, j) : Maybe<&2, Hv.VCpu>}:
  match vs i j:
    case Nil{} ii jj:
      {==}
    case h <> t 0n 0n:
      Empty.absurd({List.get(&2, Hv.VCpu, Hv.vcpu_map(h <> t, 0n, f), 0n) == List.get(&2, Hv.VCpu, h <> t, 0n) : Maybe<&2, Hv.VCpu>}, false_true(ne))
    case h <> t 0n 1n+jp:
      {==}
    case h <> t 1n+ip 0n:
      {==}
    case h <> t 1n+ip 1n+jp:
      vcpu_map_other(t, ip, jp, f, ne)

def vcpu_at_map(vs: List<&2, Hv.VCpu>, i: Nat, +j: Nat, f: Hv.VCpu -> Hv.VCpu, +ne: {Nat.is_ne(j, i) == True{} : Bool}) -> {Hv.vcpu_at(Hv.vcpu_map(vs, i, f), j) == Hv.vcpu_at(vs, j) : Hv.VCpu}:
  Equal.cong(Maybe<&2, Hv.VCpu>, Hv.VCpu, mb => Maybe.default(&2, Hv.VCpu, mb, Hv.VCpu.dead()),
    List.get(&2, Hv.VCpu, Hv.vcpu_map(vs, i, f), j), List.get(&2, Hv.VCpu, vs, j),
    vcpu_map_other(vs, i, j, f, ne))

# the same fact seen through vcpu_at
def at_g(+g: Nat, a: List<&2, Hv.VCpu>, b: List<&2, Hv.VCpu>, e: {a == b : List<&2, Hv.VCpu>}) -> {Hv.vcpu_at(a, g) == Hv.vcpu_at(b, g) : Hv.VCpu}:
  Equal.cong(List<&2, Hv.VCpu>, Hv.VCpu, vs => Hv.vcpu_at(vs, g), a, b, e)

def save_frame(m: Hv.Machine, r: Hv.Regs, +g: Nat, +ne: {Nat.is_ne(g, Hv.Machine.cur(m)) == True{} : Bool}) -> {Hv.vcpu_at(Hv.Machine.vcpus(Hv.Machine.save(m, r)), g) == Hv.vcpu_at(Hv.Machine.vcpus(m), g) : Hv.VCpu}:
  match m:
    case Hv.Machine{ps, vs, cur}:
      vcpu_at_map(vs, cur, g, v => Hv.VCpu.save(v, r), ne)

def stop_frame(m: Hv.Machine, +g: Nat, +ne: {Nat.is_ne(g, Hv.Machine.cur(m)) == True{} : Bool}) -> {Hv.vcpu_at(Hv.Machine.vcpus(Hv.Machine.stop(m)), g) == Hv.vcpu_at(Hv.Machine.vcpus(m), g) : Hv.VCpu}:
  match m:
    case Hv.Machine{ps, vs, cur}:
      vcpu_at_map(vs, cur, g, v => Hv.VCpu.stop(v), ne)

# a schedule keeps every vCPU: it only moves the core
def sched_at_vcpus(k: Hv.Kernel, m: Hv.Machine, pick: Maybe<&2, Nat>) -> {Hv.Step.vcpus(Hv.sched.at(k, m, pick)) == Hv.Machine.vcpus(m) : List<&2, Hv.VCpu>}:
  match k m pick:
    case Hv.Kernel{n, next, slice} Hv.Machine{ps, vs, cur} None{}:
      {==}
    case Hv.Kernel{n, next, slice} Hv.Machine{ps, vs, cur} Some{g}:
      {==}

def sched_vcpus(+k: Hv.Kernel, +m: Hv.Machine) -> {Hv.Step.vcpus(Hv.sched(k, m)) == Hv.Machine.vcpus(m) : List<&2, Hv.VCpu>}:
  sched_at_vcpus(k, m, Hv.first_live(Hv.rotation(Hv.Kernel.n(k), Hv.Kernel.next(k)), Hv.Machine.vcpus(m)))

def prepend_vcpus(a: Hv.Action, s: Hv.Step) -> {Hv.Step.vcpus(Hv.prepend(a, s)) == Hv.Step.vcpus(s) : List<&2, Hv.VCpu>}:
  match s:
    case Hv.Go{k, m, acts}:
      {==}
    case Hv.Fin{k, m, acts}:
      {==}

def sched_frame(+k: Hv.Kernel, +m: Hv.Machine, +g: Nat) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.sched(k, m)), g) == Hv.vcpu_at(Hv.Machine.vcpus(m), g) : Hv.VCpu}:
  at_g(g, Hv.Step.vcpus(Hv.sched(k, m)), Hv.Machine.vcpus(m), sched_vcpus(k, m))

def halt_frame(+k: Hv.Kernel, +m: Hv.Machine, +g: Nat, +ne: {Nat.is_ne(g, Hv.Machine.cur(m)) == True{} : Bool}) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.halt(k, m)), g) == Hv.vcpu_at(Hv.Machine.vcpus(m), g) : Hv.VCpu}:
  Equal.trans(Hv.VCpu, Hv.vcpu_at(Hv.Step.vcpus(Hv.halt(k, m)), g), Hv.vcpu_at(Hv.Machine.vcpus(Hv.Machine.stop(m)), g), Hv.vcpu_at(Hv.Machine.vcpus(m), g),
    at_g(g, Hv.Step.vcpus(Hv.halt(k, m)), Hv.Machine.vcpus(Hv.Machine.stop(m)),
      Equal.trans(List<&2, Hv.VCpu>, Hv.Step.vcpus(Hv.halt(k, m)), Hv.Step.vcpus(Hv.sched(k, Hv.Machine.stop(m))), Hv.Machine.vcpus(Hv.Machine.stop(m)),
        prepend_vcpus(Hv.Stop{Hv.Machine.cur(m)}, Hv.sched(k, Hv.Machine.stop(m))),
        sched_vcpus(k, Hv.Machine.stop(m)))),
    stop_frame(m, g, ne))

def resume_frame(k: Hv.Kernel, m: Hv.Machine, r: Hv.Regs, v: U32, +g: Nat, +ne: {Nat.is_ne(g, Hv.Machine.cur(m)) == True{} : Bool}) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.resume(k, m, r, v)), g) == Hv.vcpu_at(Hv.Machine.vcpus(m), g) : Hv.VCpu}:
  save_frame(m, Hv.Regs.set_x0(r, Hv.W64.of(v)), g, ne)

def hvc_frame(+k: Hv.Kernel, +m: Hv.Machine, c: Hv.Call, +r: Hv.Regs, +g: Nat, +ne: {Nat.is_ne(g, Hv.Machine.cur(m)) == True{} : Bool}) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.hvc(k, m, c, r)), g) == Hv.vcpu_at(Hv.Machine.vcpus(m), g) : Hv.VCpu}:
  match c:
    case Hv.Yield{}:
      sched_frame(k, m, g)
    case Hv.Put{}:
      Equal.trans(Hv.VCpu, Hv.vcpu_at(Hv.Step.vcpus(Hv.hvc(k, m, Hv.Put{}, r)), g), Hv.vcpu_at(Hv.Step.vcpus(Hv.resume(k, m, r, 0)), g), Hv.vcpu_at(Hv.Machine.vcpus(m), g),
        at_g(g, Hv.Step.vcpus(Hv.hvc(k, m, Hv.Put{}, r)), Hv.Step.vcpus(Hv.resume(k, m, r, 0)),
          prepend_vcpus(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, m, r, 0))),
        resume_frame(k, m, r, 0, g, ne))
    case Hv.Quit{}:
      halt_frame(k, m, g, ne)
    case Hv.Bad{}:
      resume_frame(k, m, r, 4294967295, g, ne)

# after a save the core is where it was, so the frame's hypothesis holds
# of the saved machine too; matching m makes that computation visible
def Laws.handle_frame(k, m, e, g, ne):
  match m e:
    case Hv.Machine{ps, vs, cur} Hv.Timer{regs}:
      Equal.trans(Hv.VCpu, Hv.vcpu_at(Hv.Step.vcpus(Hv.sched(k, Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs))), g), Hv.vcpu_at(Hv.Machine.vcpus(Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs)), g), Hv.vcpu_at(vs, g),
        sched_frame(k, Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs), g),
        save_frame(Hv.Machine{ps, vs, cur}, regs, g, ne))
    case Hv.Machine{ps, vs, cur} Hv.Wfi{regs}:
      Equal.trans(Hv.VCpu, Hv.vcpu_at(Hv.Step.vcpus(Hv.sched(k, Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs))), g), Hv.vcpu_at(Hv.Machine.vcpus(Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs)), g), Hv.vcpu_at(vs, g),
        sched_frame(k, Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs), g),
        save_frame(Hv.Machine{ps, vs, cur}, regs, g, ne))
    case Hv.Machine{ps, vs, cur} Hv.Hvc{imm, regs}:
      Equal.trans(Hv.VCpu, Hv.vcpu_at(Hv.Step.vcpus(Hv.hvc(k, Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs), Hv.decode(imm), regs)), g), Hv.vcpu_at(Hv.Machine.vcpus(Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs)), g), Hv.vcpu_at(vs, g),
        hvc_frame(k, Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs), Hv.decode(imm), regs, g, ne),
        save_frame(Hv.Machine{ps, vs, cur}, regs, g, ne))
    case Hv.Machine{ps, vs, cur} Hv.DataAbort{ipa, write, regs}:
      Equal.trans(Hv.VCpu, Hv.vcpu_at(Hv.Step.vcpus(Hv.halt(k, Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs))), g), Hv.vcpu_at(Hv.Machine.vcpus(Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs)), g), Hv.vcpu_at(vs, g),
        halt_frame(k, Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs), g, ne),
        save_frame(Hv.Machine{ps, vs, cur}, regs, g, ne))
    case Hv.Machine{ps, vs, cur} Hv.InstAbort{ipa, regs}:
      Equal.trans(Hv.VCpu, Hv.vcpu_at(Hv.Step.vcpus(Hv.halt(k, Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs))), g), Hv.vcpu_at(Hv.Machine.vcpus(Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs)), g), Hv.vcpu_at(vs, g),
        halt_frame(k, Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs), g, ne),
        save_frame(Hv.Machine{ps, vs, cur}, regs, g, ne))
    case Hv.Machine{ps, vs, cur} Hv.Fault{esr, regs}:
      Equal.trans(Hv.VCpu, Hv.vcpu_at(Hv.Step.vcpus(Hv.halt(k, Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs))), g), Hv.vcpu_at(Hv.Machine.vcpus(Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs)), g), Hv.vcpu_at(vs, g),
        halt_frame(k, Hv.Machine.save(Hv.Machine{ps, vs, cur}, regs), g, ne),
        save_frame(Hv.Machine{ps, vs, cur}, regs, g, ne))
