# hypervisor: a separation kernel on ARM64, as a pure function over a
# machine model. The kernel handles one guest exit at a time and answers
# with the next machine state and the actions the hardware must take.
# Two drivers consume the actions: sim (below) applies them to the model
# from a trace of exits; bare.bend applies them through effects at EL2.
# LAWS.bend states the isolation laws; PROOF.bend proves them. main
# runs sim on a trace of three guests and prints the log.
#
#   bend demos/hypervisor/main.bend

import Base

# Words
# -----

# a 64-bit register value, as two U32 halves
type W64 is Data:
  W64{hi: U32, lo: U32}

def W64.zero() -> W64:
  W64{0, 0}

def W64.of(lo: U32) -> W64:
  W64{0, lo}

def W64.show(w: W64) -> String:
  match w:
    case W64{hi, lo}:
      U32.show(hi) ++ ":" ++ U32.show(lo)

# Model
# -----

# who may touch a 2 MiB block of physical memory
type Owner is Data:
  Free{}
  Hyp{}
  Of{g: Nat}

# the hypercall window: the guest registers the kernel reads and writes;
# the rest of a guest's register file is saved and restored by the trap
# shim, per guest, and the kernel never sees it
type Regs is Data:
  Regs{x0: W64, x1: W64, x2: W64, x3: W64, pc: W64}

type VCpu is Data:
  VCpu{regs: Regs, live: Bool}

# the machine: block ownership, one vCPU per guest, the guest on the core
type Machine is Data:
  Machine{pages: List<&2, Owner>, vcpus: List<&2, VCpu>, cur: Nat}

# the exits the trap shim reports, each with the window at the exit
type Exit is Data:
  Timer{regs: Regs}
  Hvc{imm: U32, regs: Regs}
  DataAbort{ipa: W64, write: Bool, regs: Regs}
  InstAbort{ipa: W64, regs: Regs}
  Wfi{regs: Regs}
  Fault{esr: W64, regs: Regs}

# what the hardware must do; Enter is always last, and answers an Exit
type Action is Data:
  Commit{g: Nat}
  Arm{ticks: U32}
  Stop{g: Nat}
  Print{s: String}
  Enter{g: Nat, regs: Regs}
  End{}

# the kernel's own state: guest count, the round-robin cursor, the slice
type Kernel is Data:
  Kernel{n: Nat, next: Nat, slice: U32}

# a decision: Go ends in Enter and the guest runs; Fin ends in End
type Step is Data:
  Go{k: Kernel, m: Machine, acts: List<&2, Action>}
  Fin{k: Kernel, m: Machine, acts: List<&2, Action>}

# the hypercalls: 0 yields, 1 prints x0 as a character, 2 stops
type Call is Data:
  Yield{}
  Put{}
  Quit{}
  Bad{}

# Access
# ------

def Step.m(s: Step) -> Machine:
  match s:
    case Go{k, m, acts}:
      m
    case Fin{k, m, acts}:
      m

def Step.acts(s: Step) -> List<&2, Action>:
  match s:
    case Go{k, m, acts}:
      acts
    case Fin{k, m, acts}:
      acts

def Regs.zero() -> Regs:
  Regs{W64.zero(), W64.zero(), W64.zero(), W64.zero(), W64.zero()}

def Regs.x0(r: Regs) -> W64:
  match r:
    case Regs{x0, x1, x2, x3, pc}:
      x0

def Regs.set_x0(r: Regs, v: W64) -> Regs:
  match r:
    case Regs{x0, x1, x2, x3, pc}:
      Regs{v, x1, x2, x3, pc}

def Regs.show(r: Regs) -> String:
  match r:
    case Regs{x0, x1, x2, x3, pc}:
      "x0=" ++ W64.show(x0) ++ " pc=" ++ W64.show(pc)

def VCpu.dead() -> VCpu:
  VCpu{Regs.zero(), False{}}

def VCpu.regs(v: VCpu) -> Regs:
  match v:
    case VCpu{regs, live}:
      regs

def VCpu.live(v: VCpu) -> Bool:
  match v:
    case VCpu{regs, live}:
      live

def VCpu.save(v: VCpu, r: Regs) -> VCpu:
  match v:
    case VCpu{regs, live}:
      VCpu{r, live}

def VCpu.stop(v: VCpu) -> VCpu:
  match v:
    case VCpu{regs, live}:
      VCpu{regs, False{}}

# the vCPU of guest g, or a dead one past the end
def vcpu_at(vs: List<&2, VCpu>, g: Nat) -> VCpu:
  Maybe.default(&2, VCpu, List.get(&2, VCpu, vs, g), VCpu.dead())

def vcpu_map(vs: List<&2, VCpu>, g: Nat, f: VCpu -> VCpu) -> List<&2, VCpu>:
  match vs g:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      f(h) <> t
    case h <> t 1n+p:
      h <> vcpu_map(t, p, f)

def Exit.regs(e: Exit) -> Regs:
  match e:
    case Timer{regs}:
      regs
    case Hvc{imm, regs}:
      regs
    case DataAbort{ipa, write, regs}:
      regs
    case InstAbort{ipa, regs}:
      regs
    case Wfi{regs}:
      regs
    case Fault{esr, regs}:
      regs

def Exit.show(e: Exit) -> String:
  match e:
    case Timer{regs}:
      "timer"
    case Hvc{imm, regs}:
      "hvc " ++ U32.show(imm) ++ " " ++ Regs.show(regs)
    case DataAbort{ipa, write, regs}:
      "data abort at " ++ W64.show(ipa)
    case InstAbort{ipa, regs}:
      "inst abort at " ++ W64.show(ipa)
    case Wfi{regs}:
      "wfi"
    case Fault{esr, regs}:
      "fault esr=" ++ W64.show(esr)

def Action.show(a: Action) -> String:
  match a:
    case Commit{g}:
      "commit " ++ Nat.show(g)
    case Arm{ticks}:
      "arm " ++ U32.show(ticks)
    case Stop{g}:
      "stop " ++ Nat.show(g)
    case Print{s}:
      "print " ++ s
    case Enter{g, regs}:
      "enter " ++ Nat.show(g) ++ " " ++ Regs.show(regs)
    case End{}:
      "end"

def Action.is_end(a: Action) -> Bool:
  match a:
    case End{}:
      True{}
    case other:
      False{}

def Action.enters(a: Action) -> Maybe<&2, Nat>:
  match a:
    case Enter{g, regs}:
      Some{g}
    case other:
      None{}

# Ownership
# ---------

def Owner.is_of(o: Owner, g: Nat) -> Bool:
  match o:
    case Free{}:
      False{}
    case Hyp{}:
      False{}
    case Of{h}:
      Nat.is_eq(h, g)

# the stage-2 map of guest g: one Bool per block, true where g owns it
def mask_of(ps: List<&2, Owner>, +g: Nat) -> List<&2, Bool>:
  match ps:
    case Nil{}:
      Nil{}
    case o <> t:
      Owner.is_of(o, g) <> mask_of(t, g)

# no block is in both masks
def disjoint(a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  match a b:
    case Nil{} _:
      True{}
    case x <> xs Nil{}:
      True{}
    case x <> xs y <> ys:
      Bool.and(Bool.not(Bool.and(x, y)), disjoint(xs, ys))

# Kernel
# ------

def Machine.save(m: Machine, r: Regs) -> Machine:
  match m:
    case Machine{pages, vcpus, +cur}:
      Machine{pages, vcpu_map(vcpus, cur, v => VCpu.save(v, r)), cur}

def Machine.stop(m: Machine) -> Machine:
  match m:
    case Machine{pages, vcpus, +cur}:
      Machine{pages, vcpu_map(vcpus, cur, v => VCpu.stop(v)), cur}

def Machine.enter(m: Machine, g: Nat) -> Machine:
  match m:
    case Machine{pages, vcpus, cur}:
      Machine{pages, vcpus, g}

def Machine.cur(m: Machine) -> Nat:
  match m:
    case Machine{pages, vcpus, cur}:
      cur

def Machine.vcpus(m: Machine) -> List<&2, VCpu>:
  match m:
    case Machine{pages, vcpus, cur}:
      vcpus

def Machine.pages(m: Machine) -> List<&2, Owner>:
  match m:
    case Machine{pages, vcpus, cur}:
      pages

def Step.vcpus(s: Step) -> List<&2, VCpu>:
  Machine.vcpus(Step.m(s))

def Kernel.next(k: Kernel) -> Nat:
  match k:
    case Kernel{n, next, slice}:
      next

def Kernel.n(k: Kernel) -> Nat:
  match k:
    case Kernel{n, next, slice}:
      n

def Kernel.slice(k: Kernel) -> U32:
  match k:
    case Kernel{n, next, slice}:
      slice

# the guests from `from` on, wrapping: from, from+1, .. n-1, 0, .. from-1
def rotation.go(k: Nat, +i: Nat, +n: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      Nat.mod(i, n) <> rotation.go(p, Nat.add(i, 1n), n)

def rotation(+n: Nat, from: Nat) -> List<&2, Nat>:
  rotation.go(n, from, n)

def pick_live(vs: List<&2, VCpu>, +g: Nat) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, VCpu.live(vcpu_at(vs, g)), Some{g}, None{})

# the first live guest in the order given
def first_live(order: List<&2, Nat>, +vs: List<&2, VCpu>) -> Maybe<&2, Nat>:
  match order:
    case Nil{}:
      None{}
    case g <> t:
      Maybe.or(&2, Nat, pick_live(vs, g), first_live(t, vs))

# hand the core to guest g: map its blocks, arm the slice, enter it
def sched.at(k: Kernel, +m: Machine, pick: Maybe<&2, Nat>) -> Step:
  match k pick:
    case Kernel{n, next, slice} None{}:
      Fin{Kernel{n, next, slice}, m, [End{}]}
    case Kernel{+n, next, +slice} Some{+g}:
      +r = VCpu.regs(vcpu_at(Machine.vcpus(m), g))
      Go{Kernel{n, Nat.mod(Nat.add(g, 1n), n), slice}, Machine.enter(m, g),
        [Commit{g}, Arm{slice}, Enter{g, r}]}

# the next live guest after the cursor, or End
def sched(+k: Kernel, +m: Machine) -> Step:
  sched.at(k, m, first_live(rotation(Kernel.n(k), Kernel.next(k)), Machine.vcpus(m)))

def decode(+imm: U32) -> Call:
  Bool.pick(Call, U32.is_eq(imm, 0), Yield{},
    Bool.pick(Call, U32.is_eq(imm, 1), Put{},
      Bool.pick(Call, U32.is_eq(imm, 2), Quit{}, Bad{})))

def char_of(w: W64) -> String:
  match w:
    case W64{hi, lo}:
      String.from_list([Char.from_u32(lo)])

# an action before a decision's actions
def prepend(a: Action, s: Step) -> Step:
  match s:
    case Go{k, m, acts}:
      Go{k, m, a <> acts}
    case Fin{k, m, acts}:
      Fin{k, m, a <> acts}

# the current guest stops; the core goes to the next
def halt(+k: Kernel, +m: Machine) -> Step:
  prepend(Stop{Machine.cur(m)}, sched(k, Machine.stop(m)))

# the current guest resumes at once with x0 = v, no new slice
def resume(k: Kernel, +m: Machine, r: Regs, v: U32) -> Step:
  +r2 = Regs.set_x0(r, W64.of(v))
  +g  = Machine.cur(m)
  Go{k, Machine.save(m, r2), [Enter{g, r2}]}

def hvc(+k: Kernel, +m: Machine, c: Call, +r: Regs) -> Step:
  match c:
    case Yield{}:
      sched(k, m)
    case Put{}:
      prepend(Print{char_of(Regs.x0(r))}, resume(k, m, r, 0))
    case Quit{}:
      halt(k, m)
    case Bad{}:
      resume(k, m, r, 4294967295)

# one exit of the current guest: save its window, then decide
def handle(+k: Kernel, +m: Machine, e: Exit) -> Step:
  match e:
    case Timer{regs}:
      sched(k, Machine.save(m, regs))
    case Wfi{regs}:
      sched(k, Machine.save(m, regs))
    case Hvc{imm, +regs}:
      hvc(k, Machine.save(m, regs), decode(imm), regs)
    case DataAbort{ipa, write, regs}:
      halt(k, Machine.save(m, regs))
    case InstAbort{ipa, regs}:
      halt(k, Machine.save(m, regs))
    case Fault{esr, regs}:
      halt(k, Machine.save(m, regs))

# Record
# ------
# the handoff record: the kernel and the machine as a list of words, so an
# instance can end and the next one can go on from it

def Owner.encode(o: Owner) -> U32:
  match o:
    case Free{}:
      0
    case Hyp{}:
      1
    case Of{g}:
      U32.add(2, U32.from_nat(g))

def Owner.decode(+w: U32) -> Owner:
  Bool.pick(Owner, U32.is_eq(w, 0), Free{},
    Bool.pick(Owner, U32.is_eq(w, 1), Hyp{}, Of{U32.to_nat(U32.sub(w, 2))}))

def W64.encode(w: W64) -> List<&2, U32>:
  match w:
    case W64{hi, lo}:
      [hi, lo]

def Regs.encode(r: Regs) -> List<&2, U32>:
  match r:
    case Regs{x0, x1, x2, x3, pc}:
      List.concat(&2, U32, [W64.encode(x0), W64.encode(x1), W64.encode(x2),
        W64.encode(x3), W64.encode(pc)])

def Bool.encode(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1

def VCpu.encode(v: VCpu) -> List<&2, U32>:
  match v:
    case VCpu{regs, live}:
      List.append(&2, U32, Regs.encode(regs), [Bool.encode(live)])

def owners_encode(ps: List<&2, Owner>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case o <> t:
      Owner.encode(o) <> owners_encode(t)

def vcpus_encode(vs: List<&2, VCpu>) -> List<&2, U32>:
  match vs:
    case Nil{}:
      Nil{}
    case v <> t:
      List.append(&2, U32, VCpu.encode(v), vcpus_encode(t))

def encode(k: Kernel, m: Machine) -> List<&2, U32>:
  match k m:
    case Kernel{n, next, slice} Machine{+pages, +vcpus, cur}:
      List.concat(&2, U32, [
        [U32.from_nat(n), U32.from_nat(next), slice, U32.from_nat(cur),
          U32.from_nat(List.length(&2, Owner, pages)),
          U32.from_nat(List.length(&2, VCpu, vcpus))],
        owners_encode(pages),
        vcpus_encode(vcpus)])

# the decoders take the words and answer the value beside the rest; each
# continues in a .fin def that matches the previous step's answer

def take_vcpus.cons(v: VCpu, r: Maybe<(List<&2, VCpu> & List<&2, U32>)>) -> Maybe<(List<&2, VCpu> & List<&2, U32>)>:
  match r:
    case None{}:
      None{}
    case Some{(vs, rest)}:
      Some{(v <> vs, rest)}

def take_vcpus(n: Nat, ws: List<&2, U32>) -> Maybe<(List<&2, VCpu> & List<&2, U32>)>:
  match n ws:
    case 0n rest:
      Some{(Nil{}, rest)}
    case 1n+p a0 <> a1 <> b0 <> b1 <> c0 <> c1 <> d0 <> d1 <> e0 <> e1 <> b <> rest:
      take_vcpus.cons(VCpu{Regs{W64{a0, a1}, W64{b0, b1}, W64{c0, c1}, W64{d0, d1}, W64{e0, e1}}, U32.is_ne(b, 0)},
        take_vcpus(p, rest))
    case 1n+p other:
      None{}

def take_owners.fin(w: U32, r: Maybe<(List<&2, Owner> & List<&2, U32>)>) -> Maybe<(List<&2, Owner> & List<&2, U32>)>:
  match r:
    case None{}:
      None{}
    case Some{(os, rest)}:
      Some{(Owner.decode(w) <> os, rest)}

def take_owners(n: Nat, ws: List<&2, U32>) -> Maybe<(List<&2, Owner> & List<&2, U32>)>:
  match n ws:
    case 0n rest:
      Some{(Nil{}, rest)}
    case 1n+p Nil{}:
      None{}
    case 1n+p w <> rest:
      take_owners.fin(w, take_owners(p, rest))

def decode_record.vcs(n: U32, next: U32, slice: U32, cur: U32, pages: List<&2, Owner>, r: Maybe<(List<&2, VCpu> & List<&2, U32>)>) -> Maybe<(Kernel & Machine)>:
  match r:
    case None{}:
      None{}
    case Some{(vcpus, rest)}:
      Some{(Kernel{U32.to_nat(n), U32.to_nat(next), slice},
        Machine{pages, vcpus, U32.to_nat(cur)})}

def decode_record.fin(n: U32, next: U32, slice: U32, cur: U32, nv: U32, r: Maybe<(List<&2, Owner> & List<&2, U32>)>) -> Maybe<(Kernel & Machine)>:
  match r:
    case None{}:
      None{}
    case Some{(pages, rest)}:
      decode_record.vcs(n, next, slice, cur, pages, take_vcpus(U32.to_nat(nv), rest))

def decode_record(ws: List<&2, U32>) -> Maybe<(Kernel & Machine)>:
  match ws:
    case n <> next <> slice <> cur <> np <> nv <> rest:
      decode_record.fin(n, next, slice, cur, nv, take_owners(U32.to_nat(np), rest))
    case other:
      None{}

# Simulator
# ---------
# sim applies the actions to the model: Enter takes the next exit of the
# trace as the guest's step. The log holds one line per exit and per
# action. Fuel counts exits, as the real driver's does.

def acts_show(acts: List<&2, Action>) -> List<&2, String>:
  match acts:
    case Nil{}:
      Nil{}
    case a <> t:
      ("  " ++ Action.show(a)) <> acts_show(t)

def acts_end(acts: List<&2, Action>) -> Bool:
  List.any(~&2, ~Action, ~Action.is_end, acts)

# the sim after a decision: log its actions, then take the next exit of
# the trace as the entered guest's step, until Fin, no fuel or no trace
def sim.go(fuel: Nat, s: Step, trace: List<&2, Exit>, log: List<&2, String>) -> Kernel & Machine & List<&2, String>:
  match fuel s trace:
    case _ Fin{k, m, acts} _:
      (k, m, List.append(&2, String, log, List.append(&2, String, acts_show(acts), ["halt: no guest runs"])))
    case 0n Go{k, m, acts} _:
      (k, m, List.append(&2, String, log, List.append(&2, String, acts_show(acts), ["halt: out of fuel"])))
    case 1n+f Go{k, m, acts} Nil{}:
      (k, m, List.append(&2, String, log, List.append(&2, String, acts_show(acts), ["halt: end of trace"])))
    case 1n+f Go{k, +m, acts} +e <> rest:
      sim.go(f, handle(k, m, e), rest,
        List.append(&2, String, log, List.append(&2, String, acts_show(acts),
          [Nat.show(Machine.cur(m)) ++ ": " ++ Exit.show(e)])))

def sim(fuel: Nat, k: Kernel, m: Machine, trace: List<&2, Exit>) -> Kernel & Machine & List<&2, String>:
  sim.go(fuel, sched(k, m), trace, ["boot"])

# Demo
# ----
# three guests over eight blocks each; guest 2 faults on its second exit

def blocks(n: Nat, +g: Nat, +per: Nat) -> List<&2, Owner>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, Owner, List.replicate(Owner, per, Of{g}), blocks(p, Nat.add(g, 1n), per))

def boot_machine(+n: Nat) -> Machine:
  Machine{List.append(&2, Owner, List.replicate(Owner, 8n, Hyp{}), blocks(n, 0n, 8n)),
    List.replicate(VCpu, n, VCpu{Regs.zero(), True{}}), 0n}

def hvc_put(c: U32, pc: U32) -> Exit:
  Hvc{1, Regs{W64.of(c), W64.zero(), W64.zero(), W64.zero(), W64.of(pc)}}

def hvc_at(imm: U32, pc: U32) -> Exit:
  Hvc{imm, Regs{W64.zero(), W64.zero(), W64.zero(), W64.zero(), W64.of(pc)}}

def demo_trace() -> List<&2, Exit>:
  [hvc_put(65, 4), hvc_at(0, 8),
   hvc_put(66, 4), hvc_at(0, 8),
   DataAbort{W64.of(2048), True{}, Regs.zero()},
   hvc_put(65, 12), hvc_at(0, 16),
   Timer{Regs{W64.zero(), W64.zero(), W64.zero(), W64.zero(), W64.of(20)}},
   hvc_at(2, 20),
   hvc_at(2, 24)]

def report(r: Kernel & Machine & List<&2, String>) -> IO(Unit):
  match r:
    case (k, +m, log):
      do IO<Unit>:
        List.for_each(~&2, ~String, ~IO.print, log)
        IO.print("masks: " ++ List.show(~&2, ~Bool, ~Bool.show, mask_of(Machine.pages(m), 1n)))
        IO.print("disjoint 0 1: " ++ Bool.show(disjoint(mask_of(Machine.pages(m), 0n), mask_of(Machine.pages(m), 1n))))
        IO.print("record: " ++ U32.show(U32.from_nat(List.length(&2, U32, encode(k, m)))) ++ " words")

def main() -> IO(Unit):
  report(sim(64n, Kernel{3n, 0n, 1000}, boot_machine(3n), demo_trace()))
