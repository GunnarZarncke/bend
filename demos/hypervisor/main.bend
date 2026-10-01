# hypervisor: a separation kernel on ARM64, as a pure function over a
# machine model. The kernel handles one guest exit at a time and answers
# with the next machine state and the actions the hardware must take.
# run (below) is the semantics: it folds the kernel over a trace of
# exits and handoffs. Two drivers consume the actions: sim renders run's
# log; bare.bend applies them through effects at EL2. LAWS.bend states
# the isolation laws; PROOF.bend proves them. main runs sim on a trace
# of three guests and prints the log.
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

# who may touch a 2 MiB block of physical memory; a guest is its vCPU's
# slot, the VMID the hardware sees less one
type Owner is Data:
  Free{}
  Hyp{}
  Of{g: U32}

# the hypercall window: the guest registers the kernel reads and writes;
# the rest of a guest's register file is saved and restored by the trap
# shim, per guest, and the kernel never sees it
type Regs is Data:
  Regs{x0: W64, x1: W64, x2: W64, x3: W64, pc: W64}

type VCpu is Data:
  VCpu{regs: Regs, live: Bool}

# a full binary tree of Data: the blocks' owners and the masks. The
# partition never changes and every decision reads it, so it is Data,
# shared rather than threaded; the vCPUs change in place, so they are an
# Array.
type Tree<-A: Data> is Data:
  Leaf{x: A}
  Node{lo: Tree<A>, hi: Tree<A>}

# the machine: the owner of each of 64 blocks (a tree of depth 6), four
# vCPU slots (an array of depth 2), the guest on the core. Machine.ok
# says so.
type Machine is Type:
  Machine{pages: Tree<Owner>, vcpus: Array<VCpu>, cur: U32}

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
  Commit{g: U32}
  Arm{ticks: U32}
  Stop{g: U32}
  Print{s: String}
  Enter{g: U32, regs: Regs}
  End{}

# the kernel's own state: guest count, the round-robin cursor, the slice
type Kernel is Data:
  Kernel{n: U32, next: U32, slice: U32}

# a decision: Go ends in Enter and the guest runs; Fin ends in End
type Step is Type:
  Go{k: Kernel, m: Machine, acts: List<&2, Action>}
  Fin{k: Kernel, m: Machine, acts: List<&2, Action>}

# the hypercalls: 0 yields, 1 prints x0 as a character, 2 stops
type Call is Data:
  Yield{}
  Put{}
  Quit{}
  Bad{}

# Shape
# -----
# the sizes the model fixes: a machine is ok when its arrays are full
# trees of 64 blocks and four slots, every owner and the core name a slot

def page_depth() -> Nat:
  6n

def vcpu_depth() -> Nat:
  2n

# the conjunction the predicates below are built from. `A & B` is a
# Sigma at &1, so a Type, so a proof of it is affine and a lemma that
# needs one twice must copy it by hand; at &2 it is Data, and `+` is
# enough. Bend's affine core is by design and higher-order contraction
# is to come, but a lower-order fact like these needs none of that.
type Both<-A: Data, -B: Data> is Data:
  Both{fst: A, snd: B}

def Tree.shape(-A: Data, t: Tree<A>, d: Nat) -> Data:
  match t d:
    case Leaf{x} 0n:
      Unit
    case Node{lo, hi} 0n:
      Empty
    case Leaf{x} 1n+p:
      Empty
    case Node{lo, hi} 1n+p:
      Both<Tree.shape(A, lo, p), Tree.shape(A, hi, p)>

def Shape(-T: Type, a: Array<T>, d: Nat) -> Data:
  match a d:
    case ALeaf{x} 0n:
      Unit
    case ANode{xs, ys} 0n:
      Empty
    case ALeaf{x} 1n+p:
      Empty
    case ANode{xs, ys} 1n+p:
      Both<Shape(T, xs, p), Shape(T, ys, p)>

def Slot(+g: U32) -> Data:
  {U32.is_lt(g, 4) == True{} : Bool}

def Owner.ok(o: Owner) -> Data:
  match o:
    case Free{}:
      Unit
    case Hyp{}:
      Unit
    case Of{g}:
      Slot(g)

def Owners.ok(t: Tree<Owner>) -> Data:
  match t:
    case Leaf{o}:
      Owner.ok(o)
    case Node{lo, hi}:
      Both<Owners.ok(lo), Owners.ok(hi)>

def Machine.ok(m: Machine) -> Data:
  match m:
    case Machine{ps, vs, cur}:
      Both<Tree.shape(Owner, ps, page_depth()), Both<Owners.ok(ps),
        Both<Shape(VCpu, vs, vcpu_depth()), Slot(cur)>>>

# Access
# ------
# the accessors that consume a machine or a step name a part for the
# laws; the kernel takes its values apart by matching instead

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

def Machine.pages(m: Machine) -> Tree<Owner>:
  match m:
    case Machine{pages, vcpus, cur}:
      pages

def Machine.vcpus(m: Machine) -> Array<VCpu>:
  match m:
    case Machine{pages, vcpus, cur}:
      vcpus

def Machine.cur(m: Machine) -> U32:
  match m:
    case Machine{pages, vcpus, cur}:
      cur

def Kernel.n(k: Kernel) -> U32:
  match k:
    case Kernel{n, next, slice}:
      n

def Kernel.slice(k: Kernel) -> U32:
  match k:
    case Kernel{n, next, slice}:
      slice

def Step.k(s: Step) -> Kernel:
  match s:
    case Go{k, m, acts}:
      k
    case Fin{k, m, acts}:
      k

# n and the slice, the kernel fields a decision does not change
def Kernel.budget(k: Kernel) -> U32 & U32:
  match k:
    case Kernel{n, next, slice}:
      (n, slice)

def Step.budget(s: Step) -> U32 & U32:
  Kernel.budget(Step.k(s))

def Step.vcpus(s: Step) -> Array<VCpu>:
  Machine.vcpus(Step.m(s))

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

# the vCPU in slot g
def vcpu_at(vs: Array<VCpu>, +g: U32) -> VCpu:
  Pair.snd(Array<VCpu>, VCpu, Array.get(VCpu, vs, g))

def vcpu_map.fin(+g: U32, f: VCpu -> VCpu, r: Array<VCpu> & VCpu) -> Array<VCpu>:
  (vs, v) = r
  Array.set(VCpu, vs, g, f(v))

# slot g through f: a set of a get
def vcpu_map(vs: Array<VCpu>, +g: U32, f: VCpu -> VCpu) -> Array<VCpu>:
  vcpu_map.fin(g, f, Array.get(VCpu, vs, g))

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
      "commit " ++ U32.show(g)
    case Arm{ticks}:
      "arm " ++ U32.show(ticks)
    case Stop{g}:
      "stop " ++ U32.show(g)
    case Print{s}:
      "print " ++ s
    case Enter{g, regs}:
      "enter " ++ U32.show(g) ++ " " ++ Regs.show(regs)
    case End{}:
      "end"

# Ownership
# ---------

def Owner.is_of(o: Owner, g: U32) -> Bool:
  match o:
    case Free{}:
      False{}
    case Hyp{}:
      False{}
    case Of{h}:
      U32.is_eq(h, g)

# the stage-2 map of guest g: one Bool per block, true where g owns it
def mask(ps: Tree<Owner>, +g: U32) -> Tree<Bool>:
  match ps:
    case Leaf{o}:
      Leaf{Owner.is_of(o, g)}
    case Node{lo, hi}:
      Node{mask(lo, g), mask(hi, g)}

def Tree.to_list(-A: Data, t: Tree<A>, rest: List<&2, A>) -> List<&2, A>:
  match t:
    case Leaf{x}:
      x <> rest
    case Node{lo, hi}:
      Tree.to_list(A, lo, Tree.to_list(A, hi, rest))

# no block is in both masks
def disjoint(a: Tree<Bool>, b: Tree<Bool>) -> Bool:
  match a b:
    case Leaf{x} Leaf{y}:
      Bool.not(Bool.and(x, y))
    case Node{xs, ys} Node{zs, ws}:
      Bool.and(disjoint(xs, zs), disjoint(ys, ws))
    case Leaf{x} Node{zs, ws}:
      True{}
    case Node{xs, ys} Leaf{y}:
      True{}

# a Free or Hyp block is false in every guest's mask; a guest's own
# block is not the claim
def mask_skips(ps: Tree<Owner>, +g: U32) -> Bool:
  match ps:
    case Leaf{o}:
      match o:
        case Free{}:
          Bool.not(Owner.is_of(o, g))
        case Hyp{}:
          Bool.not(Owner.is_of(o, g))
        case Of{h}:
          True{}
    case Node{lo, hi}:
      Bool.and(mask_skips(lo, g), mask_skips(hi, g))

# Kernel
# ------

def decode(+imm: U32) -> Call:
  Bool.pick(Call, U32.is_eq(imm, 0), Yield{},
    Bool.pick(Call, U32.is_eq(imm, 1), Put{},
      Bool.pick(Call, U32.is_eq(imm, 2), Quit{}, Bad{})))

def VCpu.call(v: VCpu, c: Call, +r: Regs) -> VCpu:
  match v c:
    case VCpu{regs, live} Yield{}:
      VCpu{r, live}
    case VCpu{regs, live} Put{}:
      VCpu{Regs.set_x0(r, W64.of(0)), live}
    case VCpu{regs, live} Quit{}:
      VCpu{r, False{}}
    case VCpu{regs, live} Bad{}:
      VCpu{Regs.set_x0(r, W64.of(4294967295)), live}

# what an exit does to the current guest's vCPU: its window is saved; a
# put or an unknown call answers in x0; a quit or a fault stops it
def VCpu.step(v: VCpu, e: Exit) -> VCpu:
  match v e:
    case VCpu{regs, live} Timer{r}:
      VCpu{r, live}
    case VCpu{regs, live} Wfi{r}:
      VCpu{r, live}
    case v Hvc{+imm, +r}:
      VCpu.call(v, decode(imm), r)
    case VCpu{regs, live} DataAbort{ipa, write, r}:
      VCpu{r, False{}}
    case VCpu{regs, live} InstAbort{ipa, r}:
      VCpu{r, False{}}
    case VCpu{regs, live} Fault{esr, r}:
      VCpu{r, False{}}

# slot x of the round
def slot(+x: U32) -> U32:
  U32.and(x, 3)

# the four slots from `next` on, wrapping
def rotation(+next: U32) -> List<&2, U32>:
  [slot(next), slot(U32.add(next, 1)), slot(U32.add(next, 2)), slot(U32.add(next, 3))]

def first_live.pick(+g: U32, rest: Maybe<&2, U32>, r: Array<VCpu> & VCpu) -> Array<VCpu> & Maybe<&2, U32>:
  (vs, v) = r
  (vs, Bool.pick(Maybe<&2, U32>, VCpu.live(v), Some{g}, rest))

def first_live.fin(+g: U32, r: Array<VCpu> & Maybe<&2, U32>) -> Array<VCpu> & Maybe<&2, U32>:
  (vs, rest) = r
  first_live.pick(g, rest, Array.get(VCpu, vs, g))

# the first live slot in the order given, beside the slots
def first_live(order: List<&2, U32>, vs: Array<VCpu>) -> Array<VCpu> & Maybe<&2, U32>:
  match order:
    case Nil{}:
      (vs, None{})
    case +g <> t:
      first_live.fin(g, first_live(t, vs))

def sched.go(k: Kernel, ps: Tree<Owner>, +g: U32, r: Array<VCpu> & VCpu) -> Step:
  Kernel{n, next, +slice} = k
  (vs, v) = r
  Go{Kernel{n, slot(U32.add(g, 1)), slice}, Machine{ps, vs, g},
    [Commit{g}, Arm{slice}, Enter{g, VCpu.regs(v)}]}

# hand the core to guest g: map its blocks, arm the slice, enter it with
# its saved window
def sched.at(k: Kernel, ps: Tree<Owner>, cur: U32, pick: Maybe<&2, U32>, vs: Array<VCpu>) -> Step:
  match pick:
    case None{}:
      Fin{k, Machine{ps, vs, cur}, [End{}]}
    case Some{+g}:
      sched.go(k, ps, g, Array.get(VCpu, vs, g))

def sched.fin(k: Kernel, ps: Tree<Owner>, cur: U32, r: Array<VCpu> & Maybe<&2, U32>) -> Step:
  (vs, pick) = r
  sched.at(k, ps, cur, pick, vs)

# the next live guest after the cursor, or End
def sched(+k: Kernel, m: Machine) -> Step:
  match k m:
    case Kernel{n, +next, slice} Machine{ps, vs, cur}:
      sched.fin(Kernel{n, next, slice}, ps, cur, first_live(rotation(next), vs))

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

# the current guest resumes at once with its saved window, no new slice
def resume.fin(k: Kernel, ps: Tree<Owner>, +g: U32, r: Array<VCpu> & VCpu) -> Step:
  (vs, v) = r
  Go{k, Machine{ps, vs, g}, [Enter{g, VCpu.regs(v)}]}

def resume(k: Kernel, m: Machine) -> Step:
  match m:
    case Machine{ps, vs, +cur}:
      resume.fin(k, ps, cur, Array.get(VCpu, vs, cur))

# the current guest has stopped; the core goes to the next
def halt(+k: Kernel, m: Machine) -> Step:
  match m:
    case Machine{ps, vs, +cur}:
      prepend(Stop{cur}, sched(k, Machine{ps, vs, cur}))

def hvc(+k: Kernel, m: Machine, c: Call, r: Regs) -> Step:
  match c:
    case Yield{}:
      sched(k, m)
    case Put{}:
      prepend(Print{char_of(Regs.x0(r))}, resume(k, m))
    case Quit{}:
      halt(k, m)
    case Bad{}:
      resume(k, m)

# the decision after the current guest's vCPU took the exit
def decide(+k: Kernel, m: Machine, e: Exit) -> Step:
  match e:
    case Timer{regs}:
      sched(k, m)
    case Wfi{regs}:
      sched(k, m)
    case Hvc{+imm, regs}:
      hvc(k, m, decode(imm), regs)
    case DataAbort{ipa, write, regs}:
      halt(k, m)
    case InstAbort{ipa, regs}:
      halt(k, m)
    case Fault{esr, regs}:
      halt(k, m)

# one exit of the current guest: its vCPU takes the exit, then decide
def handle(+k: Kernel, m: Machine, +e: Exit) -> Step:
  match m:
    case Machine{ps, vs, +cur}:
      decide(k, Machine{ps, vcpu_map(vs, cur, v => VCpu.step(v, e)), cur}, e)

# What a guest is entered with
# ----------------------------
# the Enter among a decision's actions, and what the laws expect of it:
# the guest on the core, with the window its vCPU holds

type Entry is Data:
  Entry{g: U32, regs: Regs}

def acts_entry(acts: List<&2, Action>) -> Maybe<&2, Entry>:
  match acts:
    case Nil{}:
      None{}
    case Enter{g, r} <> t:
      Maybe.or(&2, Entry, acts_entry(t), Some{Entry{g, r}})
    case other <> t:
      acts_entry(t)

def Step.entry(s: Step) -> Maybe<&2, Entry>:
  match s:
    case Go{k, m, acts}:
      acts_entry(acts)
    case Fin{k, m, acts}:
      acts_entry(acts)

def Step.saved(s: Step) -> Maybe<&2, Entry>:
  match s:
    case Go{k, Machine{ps, vs, +cur}, acts}:
      Some{Entry{cur, VCpu.regs(vcpu_at(vs, cur))}}
    case Fin{k, m, acts}:
      None{}

# a Go list has one Enter and it is last; a Fin list has no Enter and
# ends in End. A Commit, Arm, Stop or Print may precede that close.
def acts_enter_last(acts: List<&2, Action>) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case Enter{g, r} <> Nil{}:
      True{}
    case Enter{g, r} <> t:
      False{}
    case End{} <> t:
      False{}
    case other <> t:
      acts_enter_last(t)

def acts_end_last(acts: List<&2, Action>) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case End{} <> Nil{}:
      True{}
    case End{} <> t:
      False{}
    case Enter{g, r} <> t:
      False{}
    case other <> t:
      acts_end_last(t)

def Step.closed(s: Step) -> Bool:
  match s:
    case Go{k, m, acts}:
      acts_enter_last(acts)
    case Fin{k, m, acts}:
      acts_end_last(acts)

# the guest on the core is live; a step that enters no one is vacuously so
def on_core_live(s: Step) -> Bool:
  match s:
    case Go{k, Machine{ps, vs, +cur}, acts}:
      VCpu.live(vcpu_at(vs, cur))
    case Fin{k, m, acts}:
      True{}

# Commit of g occurs in the list
def acts_commits(+g: U32, acts: List<&2, Action>) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case Commit{+h} <> t:
      Bool.or(U32.is_eq(h, g), acts_commits(g, t))
    case other <> t:
      acts_commits(g, t)

# every Stop names cur
def stops_self(+cur: U32, acts: List<&2, Action>) -> Bool:
  match acts:
    case Nil{}:
      True{}
    case Stop{+g} <> t:
      Bool.and(U32.is_eq(g, cur), stops_self(cur, t))
    case other <> t:
      stops_self(cur, t)

# the first Print, and whether any Stop occurs
def acts_print(acts: List<&2, Action>) -> Maybe<&2, String>:
  match acts:
    case Nil{}:
      None{}
    case Print{s} <> t:
      Some{s}
    case other <> t:
      acts_print(t)

def acts_stops(acts: List<&2, Action>) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case Stop{g} <> t:
      True{}
    case other <> t:
      acts_stops(t)

# what a put shows: the first print, and whether a guest was stopped
def put_obs.acts(acts: List<&2, Action>) -> Maybe<&2, String> & Bool:
  match acts:
    case Nil{}:
      (None{}, False{})
    case Print{s} <> t:
      (Some{s}, acts_stops(t))
    case Stop{g} <> t:
      (acts_print(t), True{})
    case other <> t:
      put_obs.acts(t)

def put_obs(s: Step) -> Maybe<&2, String> & Bool:
  match s:
    case Go{k, m, acts}:
      put_obs.acts(acts)
    case Fin{k, m, acts}:
      put_obs.acts(acts)

# Record
# ------
# the handoff record: the kernel and the machine as a list of words, so an
# instance can end and the next one can go on from it: six header words,
# the 64 owners, eleven words per slot

def Owner.encode(o: Owner) -> U32:
  match o:
    case Free{}:
      0
    case Hyp{}:
      1
    case Of{g}:
      U32.add(2, g)

def Owner.decode(+w: U32) -> Owner:
  Bool.pick(Owner, U32.is_eq(w, 0), Free{},
    Bool.pick(Owner, U32.is_eq(w, 1), Hyp{}, Of{U32.sub(w, 2)}))

def W64.encode(w: W64, rest: List<&2, U32>) -> List<&2, U32>:
  match w:
    case W64{hi, lo}:
      hi <> lo <> rest

def Regs.encode(r: Regs, rest: List<&2, U32>) -> List<&2, U32>:
  match r:
    case Regs{x0, x1, x2, x3, pc}:
      W64.encode(x0, W64.encode(x1, W64.encode(x2, W64.encode(x3, W64.encode(pc, rest)))))

def Bool.encode(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1

def VCpu.encode(v: VCpu, rest: List<&2, U32>) -> List<&2, U32>:
  match v:
    case VCpu{regs, live}:
      Regs.encode(regs, Bool.encode(live) <> rest)

# the arrays in slot order, onto the rest
def owners_encode(ps: Tree<Owner>, rest: List<&2, U32>) -> List<&2, U32>:
  match ps:
    case Leaf{o}:
      Owner.encode(o) <> rest
    case Node{lo, hi}:
      owners_encode(lo, owners_encode(hi, rest))

def vcpus_encode(vs: Array<VCpu>, rest: List<&2, U32>) -> List<&2, U32>:
  match vs:
    case ALeaf{v}:
      VCpu.encode(v, rest)
    case ANode{xs, ys}:
      vcpus_encode(xs, vcpus_encode(ys, rest))

def encode(k: Kernel, m: Machine) -> List<&2, U32>:
  match k m:
    case Kernel{n, next, slice} Machine{ps, vs, cur}:
      n <> next <> slice <> cur <> 64 <> 4 <> owners_encode(ps, vcpus_encode(vs, Nil{}))

# the decoders read a full tree of the given depth off the words and
# answer it beside the rest; each continues in a .fin def that matches
# the previous read's answer

def four(a: VCpu, b: VCpu, c: VCpu, d: VCpu) -> Array<VCpu>:
  ANode{ANode{ALeaf{a}, ALeaf{b}}, ANode{ALeaf{c}, ALeaf{d}}}


# Validation
# ----------
# the record comes out of the persist region, which nothing guarantees.
# A decoded machine is taken only when it is well formed and the words
# are exactly what it encodes, so a corrupt record is refused rather
# than believed. The checks read the decoded value, not the words, so
# they need no induction over a record.

def Owner.okb(o: Owner) -> Bool:
  match o:
    case Free{}:
      True{}
    case Hyp{}:
      True{}
    case Of{g}:
      U32.is_lt(g, 4)

def Owners.okb(t: Tree<Owner>) -> Bool:
  match t:
    case Leaf{o}:
      Owner.okb(o)
    case Node{lo, hi}:
      Bool.and(Owners.okb(lo), Owners.okb(hi))

def Tree.shapeb(t: Tree<Owner>, +d: Nat) -> Bool:
  match t d:
    case Leaf{o} 0n:
      True{}
    case Node{lo, hi} 0n:
      False{}
    case Leaf{o} 1n+p:
      False{}
    case Node{lo, hi} 1n+p:
      Bool.and(Tree.shapeb(lo, p), Tree.shapeb(hi, p))

def U32.list_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> ys:
      False{}
    case x <> xs Nil{}:
      False{}
    case x <> xs y <> ys:
      Bool.and(U32.is_eq(x, y), U32.list_eq(xs, ys))

def owners_take.fin(xs: Tree<Owner>, r: Maybe<(Tree<Owner> & List<&2, U32>)>) -> Maybe<(Tree<Owner> & List<&2, U32>)>:
  match r:
    case None{}:
      None{}
    case Some{(ys, rest)}:
      Some{(Node{xs, ys}, rest)}

def owners_take.node(r: Maybe<(Tree<Owner> & List<&2, U32>)>, f: List<&2, U32> -> Maybe<(Tree<Owner> & List<&2, U32>)>) -> Maybe<(Tree<Owner> & List<&2, U32>)>:
  match r:
    case None{}:
      None{}
    case Some{(xs, rest)}:
      owners_take.fin(xs, f(rest))

def owners_take(+d: Nat, ws: List<&2, U32>) -> Maybe<(Tree<Owner> & List<&2, U32>)>:
  match d ws:
    case 0n Nil{}:
      None{}
    case 0n w <> rest:
      Some{(Leaf{Owner.decode(w)}, rest)}
    case 1n+p ws:
      owners_take.node(owners_take(p, ws), rest => owners_take(p, rest))

def vcpus_take.fin(xs: Array<VCpu>, r: Maybe<(Array<VCpu> & List<&2, U32>)>) -> Maybe<(Array<VCpu> & List<&2, U32>)>:
  match r:
    case None{}:
      None{}
    case Some{(ys, rest)}:
      Some{(ANode{xs, ys}, rest)}

def vcpus_take.node(r: Maybe<(Array<VCpu> & List<&2, U32>)>, f: List<&2, U32> -> Maybe<(Array<VCpu> & List<&2, U32>)>) -> Maybe<(Array<VCpu> & List<&2, U32>)>:
  match r:
    case None{}:
      None{}
    case Some{(xs, rest)}:
      vcpus_take.fin(xs, f(rest))

def vcpus_take(+d: Nat, ws: List<&2, U32>) -> Maybe<(Array<VCpu> & List<&2, U32>)>:
  match d ws:
    case 0n a0 <> a1 <> b0 <> b1 <> c0 <> c1 <> d0 <> d1 <> e0 <> e1 <> b <> rest:
      Some{(ALeaf{VCpu{Regs{W64{a0, a1}, W64{b0, b1}, W64{c0, c1}, W64{d0, d1}, W64{e0, e1}}, U32.is_ne(b, 0)}}, rest)}
    case 0n other:
      None{}
    case 1n+p ws:
      vcpus_take.node(vcpus_take(p, ws), rest => vcpus_take(p, rest))

# one vCPU: ten words of window and a live bit
def vcpu_take(ws: List<&2, U32>) -> Maybe<(VCpu & List<&2, U32>)>:
  match ws:
    case a0 <> a1 <> b0 <> b1 <> c0 <> c1 <> d0 <> d1 <> e0 <> e1 <> b <> rest:
      Some{(VCpu{Regs{W64{a0, a1}, W64{b0, b1}, W64{c0, c1}, W64{d0, d1}, W64{e0, e1}}, U32.is_ne(b, 0)}, rest)}
    case other:
      None{}

# the words a record holds, from the parts rather than from a machine:
# the check below needs them while the vCPUs are still values, since an
# Array has one owner and the machine wants it
def encode_parts(k: Kernel, ps: Tree<Owner>, v0: VCpu, v1: VCpu, v2: VCpu, v3: VCpu, cur: U32) -> List<&2, U32>:
  match k:
    case Kernel{n, next, slice}:
      n <> next <> slice <> cur <> 64 <> 4 <>
        owners_encode(ps, VCpu.encode(v0, VCpu.encode(v1, VCpu.encode(v2, VCpu.encode(v3, Nil{})))))

def decode_record.take(k: Kernel, +cur: U32, ps: Tree<Owner>, v0: VCpu, v1: VCpu, v2: VCpu, v3: VCpu, ok: Bool) -> Maybe<(Kernel & Machine)>:
  match ok:
    case False{}:
      None{}
    case True{}:
      Some{(k, Machine{ps, four(v0, v1, v2, v3), cur})}

def decode_record.v3(+k: Kernel, +cur: U32, +ps: Tree<Owner>, ws: List<&2, U32>, +v0: VCpu, +v1: VCpu, +v2: VCpu, r: Maybe<(VCpu & List<&2, U32>)>) -> Maybe<(Kernel & Machine)>:
  match r:
    case None{}:
      None{}
    case Some{(+v3, Nil{})}:
      decode_record.take(k, cur, ps, v0, v1, v2, v3,
        Bool.and(Bool.and(Owners.okb(ps), Tree.shapeb(ps, page_depth())),
          Bool.and(U32.is_lt(cur, 4), U32.list_eq(ws, encode_parts(k, ps, v0, v1, v2, v3, cur)))))
    case Some{(v3, w <> more)}:
      None{}

def decode_record.v2(+k: Kernel, +cur: U32, +ps: Tree<Owner>, ws: List<&2, U32>, +v0: VCpu, +v1: VCpu, r: Maybe<(VCpu & List<&2, U32>)>) -> Maybe<(Kernel & Machine)>:
  match r:
    case None{}:
      None{}
    case Some{(+v2, rest)}:
      decode_record.v3(k, cur, ps, ws, v0, v1, v2, vcpu_take(rest))

def decode_record.v1(+k: Kernel, +cur: U32, +ps: Tree<Owner>, ws: List<&2, U32>, +v0: VCpu, r: Maybe<(VCpu & List<&2, U32>)>) -> Maybe<(Kernel & Machine)>:
  match r:
    case None{}:
      None{}
    case Some{(+v1, rest)}:
      decode_record.v2(k, cur, ps, ws, v0, v1, vcpu_take(rest))

def decode_record.vcs(+k: Kernel, +cur: U32, +ps: Tree<Owner>, ws: List<&2, U32>, r: Maybe<(VCpu & List<&2, U32>)>) -> Maybe<(Kernel & Machine)>:
  match r:
    case None{}:
      None{}
    case Some{(+v0, rest)}:
      decode_record.v1(k, cur, ps, ws, v0, vcpu_take(rest))

def decode_record.fin(+k: Kernel, +cur: U32, ws: List<&2, U32>, r: Maybe<(Tree<Owner> & List<&2, U32>)>) -> Maybe<(Kernel & Machine)>:
  match r:
    case None{}:
      None{}
    case Some{(ps, rest)}:
      decode_record.vcs(k, cur, ps, ws, vcpu_take(rest))

def decode_record.sized(+k: Kernel, +cur: U32, ok: Bool, ws: List<&2, U32>, rest: List<&2, U32>) -> Maybe<(Kernel & Machine)>:
  match ok:
    case False{}:
      None{}
    case True{}:
      decode_record.fin(k, cur, ws, owners_take(page_depth(), rest))

def decode_record(ws: List<&2, U32>) -> Maybe<(Kernel & Machine)>:
  match ws:
    case +n <> +next <> +slice <> +cur <> +np <> +nv <> +rest:
      decode_record.sized(Kernel{n, next, slice}, cur,
        Bool.and(U32.is_eq(np, 64), U32.is_eq(nv, 4)),
        n <> next <> slice <> cur <> np <> nv <> rest, rest)
    case other:
      None{}

# Semantics
# ---------
# run folds the kernel over a trace. An event is an exit of the guest the
# last decision entered, or a handoff: the instance ends, the record is
# stored, and the next instance decodes it and schedules afresh. The log
# holds, per event, the actions before it and the guest on the core.

type Ev is Data:
  Ex{e: Exit}
  Handoff{}

type Tick is Data:
  Tick{acts: List<&2, Action>, g: U32, ev: Ev}

type Why is Data:
  NoGuest{}
  NoFuel{}
  NoTrace{}

type Run is Type:
  Run{s: Step, log: List<&2, Tick>, why: Why}

def Run.s(r: Run) -> Step:
  match r:
    case Run{s, log, why}:
      s

def Run.log(r: Run) -> List<&2, Tick>:
  match r:
    case Run{s, log, why}:
      log

def empty_machine() -> Machine:
  Machine{Leaf{Free{}}, ALeaf{VCpu.dead()}, 0}

def handoff.fin(k: Kernel, r: Maybe<(Kernel & Machine)>) -> Step:
  match r:
    case None{}:
      Fin{k, empty_machine(), [End{}]}
    case Some{(k2, m2)}:
      sched(k2, m2)

# the next instance, from the record of this one
def handoff(+k: Kernel, m: Machine) -> Step:
  handoff.fin(k, decode_record(encode(k, m)))

def event(+k: Kernel, m: Machine, ev: Ev) -> Step:
  match ev:
    case Ex{+e}:
      handle(k, m, e)
    case Handoff{}:
      handoff(k, m)

def run.cons(t: Tick, r: Run) -> Run:
  match r:
    case Run{s, log, why}:
      Run{s, t <> log, why}

def run(fuel: Nat, s: Step, trace: List<&2, Ev>) -> Run:
  match fuel s trace:
    case _ Fin{k, m, acts} _:
      Run{Fin{k, m, acts}, Nil{}, NoGuest{}}
    case 0n Go{k, m, acts} _:
      Run{Go{k, m, acts}, Nil{}, NoFuel{}}
    case 1n+f Go{k, m, acts} Nil{}:
      Run{Go{k, m, acts}, Nil{}, NoTrace{}}
    case 1n+f Go{+k, Machine{ps, vs, +cur}, acts} +ev <> rest:
      run.cons(Tick{acts, cur, ev}, run(f, event(k, Machine{ps, vs, cur}, ev), rest))

# the exits guest a took in a run's log, in order, and what they do to
# a vCPU: the view of a run that noninterference is about
def own_exits(+a: U32, log: List<&2, Tick>) -> List<&2, Exit>:
  match log:
    case Nil{}:
      Nil{}
    case Tick{acts, +g, Ex{e}} <> rest:
      List.append(&2, Exit, Bool.pick(List<&2, Exit>, U32.is_eq(a, g), [e], Nil{}), own_exits(a, rest))
    case Tick{acts, g, Handoff{}} <> rest:
      own_exits(a, rest)

def VCpu.steps(es: List<&2, Exit>, v: VCpu) -> VCpu:
  match es:
    case Nil{}:
      v
    case e <> rest:
      VCpu.steps(rest, VCpu.step(v, e))

# Simulator
# ---------
# sim renders a run: one line per event and per action. Fuel counts
# events, as the real driver's counts exits.

def acts_show(acts: List<&2, Action>) -> List<&2, String>:
  match acts:
    case Nil{}:
      Nil{}
    case a <> t:
      ("  " ++ Action.show(a)) <> acts_show(t)

def Ev.show(ev: Ev) -> String:
  match ev:
    case Ex{e}:
      Exit.show(e)
    case Handoff{}:
      "handoff"

def Why.show(w: Why) -> String:
  match w:
    case NoGuest{}:
      "halt: no guest runs"
    case NoFuel{}:
      "halt: out of fuel"
    case NoTrace{}:
      "halt: end of trace"

def ticks_show(log: List<&2, Tick>, rest: List<&2, String>) -> List<&2, String>:
  match log:
    case Nil{}:
      rest
    case Tick{acts, g, ev} <> t:
      List.append(&2, String, acts_show(acts), (U32.show(g) ++ ": " ++ Ev.show(ev)) <> ticks_show(t, rest))

def sim.last(log: List<&2, Tick>, why: Why, s: Step) -> Step & List<&2, String>:
  match s:
    case Go{k, m, +acts}:
      (Go{k, m, acts}, "boot" <> ticks_show(log, List.append(&2, String, acts_show(acts), [Why.show(why)])))
    case Fin{k, m, +acts}:
      (Fin{k, m, acts}, "boot" <> ticks_show(log, List.append(&2, String, acts_show(acts), [Why.show(why)])))

def sim.show(r: Run) -> Step & List<&2, String>:
  match r:
    case Run{s, log, why}:
      sim.last(log, why, s)

def sim(fuel: Nat, +k: Kernel, m: Machine, trace: List<&2, Ev>) -> Step & List<&2, String>:
  sim.show(run(fuel, sched(k, m), trace))

# Demo
# ----
# three guests over eight blocks each; guest 2 faults on its second exit

def blocks.at(+b: Nat, +n: Nat) -> Owner:
  Bool.pick(Owner, Nat.is_lt(b, 8n), Hyp{},
    Bool.pick(Owner, Nat.is_lt(b, Nat.add(8n, Nat.mul(8n, n))), Of{U32.from_nat(Nat.div(Nat.sub(b, 8n), 8n))}, Free{}))

# the blocks from b on, a full tree of depth d: eight for the kernel,
# then eight per guest, the rest free
def blocks(+d: Nat, +b: Nat, +n: Nat) -> Tree<Owner>:
  match d:
    case 0n:
      Leaf{blocks.at(b, n)}
    case 1n+p:
      Node{blocks(p, b, n), blocks(p, Nat.add(b, Nat.pow(2n, p)), n)}

def live_if(+g: U32, +n: U32) -> VCpu:
  VCpu{Regs.zero(), U32.is_lt(g, n)}

def boot_machine(+n: U32) -> Machine:
  Machine{blocks(page_depth(), 0n, U32.to_nat(n)),
    four(live_if(0, n), live_if(1, n), live_if(2, n), live_if(3, n)), 0}

def hvc_put(c: U32, pc: U32) -> Ev:
  Ex{Hvc{1, Regs{W64.of(c), W64.zero(), W64.zero(), W64.zero(), W64.of(pc)}}}

def hvc_at(imm: U32, pc: U32) -> Ev:
  Ex{Hvc{imm, Regs{W64.zero(), W64.zero(), W64.zero(), W64.zero(), W64.of(pc)}}}

def demo_trace() -> List<&2, Ev>:
  [hvc_put(65, 4), hvc_at(0, 8),
   hvc_put(66, 4), hvc_at(0, 8),
   Ex{DataAbort{W64.of(2048), True{}, Regs.zero()}},
   hvc_put(65, 12), hvc_at(0, 16),
   Ex{Timer{Regs{W64.zero(), W64.zero(), W64.zero(), W64.zero(), W64.of(20)}}},
   hvc_at(2, 20),
   hvc_at(2, 24)]

def bools_show(t: Tree<Bool>) -> String:
  List.show(~&2, ~Bool, ~Bool.show, Tree.to_list(Bool, t, Nil{}))

def report.masks(m: Machine) -> List<&2, String>:
  match m:
    case Machine{+ps, vs, cur}:
      ["masks: " ++ bools_show(mask(ps, 1)),
       "disjoint 0 1: " ++ Bool.show(disjoint(mask(ps, 0), mask(ps, 1)))]

def report.record(k: Kernel, m: Machine) -> String:
  "record: " ++ U32.show(U32.from_nat(List.length(&2, U32, encode(k, m)))) ++ " words"

def report.step(s: Step) -> List<&2, String>:
  match s:
    case Go{k, m, acts}:
      report.masks(m)
    case Fin{k, m, acts}:
      report.masks(m)

def report(r: Step & List<&2, String>) -> IO(Unit):
  (s, log) = r
  do IO<Unit>:
    List.for_each(~&2, ~String, ~IO.print, log)
    List.for_each(~&2, ~String, ~IO.print, report.step(s))
    IO.print(report.record(Kernel{3, 0, 1000}, boot_machine(3)))

def main() -> IO(Unit):
  report(sim(64n, Kernel{3, 0, 1000}, boot_machine(3), demo_trace()))

#|boot
#|  commit 0
#|  arm 1000
#|  enter 0 x0=0:0 pc=0:0
#|0: hvc 1 x0=0:65 pc=0:4
#|  print A
#|  enter 0 x0=0:0 pc=0:4
#|0: hvc 0 x0=0:0 pc=0:8
#|  commit 1
#|  arm 1000
#|  enter 1 x0=0:0 pc=0:0
#|1: hvc 1 x0=0:66 pc=0:4
#|  print B
#|  enter 1 x0=0:0 pc=0:4
#|1: hvc 0 x0=0:0 pc=0:8
#|  commit 2
#|  arm 1000
#|  enter 2 x0=0:0 pc=0:0
#|2: data abort at 0:2048
#|  stop 2
#|  commit 0
#|  arm 1000
#|  enter 0 x0=0:0 pc=0:8
#|0: hvc 1 x0=0:65 pc=0:12
#|  print A
#|  enter 0 x0=0:0 pc=0:12
#|0: hvc 0 x0=0:0 pc=0:16
#|  commit 1
#|  arm 1000
#|  enter 1 x0=0:0 pc=0:8
#|1: timer
#|  commit 0
#|  arm 1000
#|  enter 0 x0=0:0 pc=0:16
#|0: hvc 2 x0=0:0 pc=0:20
#|  stop 0
#|  commit 1
#|  arm 1000
#|  enter 1 x0=0:0 pc=0:20
#|1: hvc 2 x0=0:0 pc=0:24
#|  stop 1
#|  end
#|halt: no guest runs
#|masks: [False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, True, True, True, True, True, True, True, True, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False]
#|disjoint 0 1: True
#|record: 114 words
