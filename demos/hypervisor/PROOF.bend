# hypervisor: the proofs of LAWS.bend. A computed value cannot be matched
# in place, so each decision is taken apart in a lemma of its own that
# receives the value as a parameter. An array is affine even in a proof:
# a law takes the vCPU array apart once, by four_view, into four Data
# leaves, and the lemmas after it speak of four(a, b, c, d), which they
# may write as often as they need; a slot index is turned into a literal
# by Lemmas.lt4, after which an access computes.

import Base
import ./main.bend as Hv
import ./Isa.bend as I
import ./Lemmas.bend as L
import ./LAWS.bend as Laws

# Masks
# -----

# an owner of a block is at most one of two distinct guests
def is_of_none.go(+x: U32, +g: U32, +h: U32, +b: Bool, eb: {U32.is_eq(x, g) == b : Bool}, +ne: {U32.is_ne(g, h) == True{} : Bool}) -> {Bool.not(Bool.and(b, U32.is_eq(x, h))) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(U32, x, g, L.u32_eq(x, g, eb)) : {Bool.not(U32.is_eq(_, h)) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(g, h), False{}, L.u32_ne(g, h, ne)) : {Bool.not(_) == True{} : Bool}
      {==}

def is_of_none(o: Hv.Owner, +g: U32, +h: U32, +ne: {U32.is_ne(g, h) == True{} : Bool}) -> {Bool.not(Bool.and(Hv.Owner.is_of(o, g), Hv.Owner.is_of(o, h))) == True{} : Bool}:
  match o:
    case Hv.Free{}:
      {==}
    case Hv.Hyp{}:
      {==}
    case Hv.Of{+x}:
      is_of_none.go(x, g, h, U32.is_eq(x, g), {==}, ne)

def Laws.masks_disjoint(ps, g, h, ne):
  match ps:
    case Hv.Leaf{o}:
      is_of_none(o, g, h, ne)
    case Hv.Node{lo, hi}:
      %Equal.sym(Bool, Hv.disjoint(Hv.mask(lo, g), Hv.mask(lo, h)), True{}, Laws.masks_disjoint(lo, g, h, ne)) : {Bool.and(_, Hv.disjoint(Hv.mask(hi, g), Hv.mask(hi, h))) == True{} : Bool}
      %Equal.sym(Bool, Hv.disjoint(Hv.mask(hi, g), Hv.mask(hi, h)), True{}, Laws.masks_disjoint(hi, g, h, ne)) : {Bool.and(True{}, _) == True{} : Bool}
      {==}

# Four slots
# ----------
# a vCPU array of depth 2 is four(a, b, c, d)

type Two<-xs: Array<Hv.VCpu>> is Data:
  IsTwo{a: Hv.VCpu, b: Hv.VCpu, e: {ANode{ALeaf{a}, ALeaf{b}} == xs : Array<Hv.VCpu>}}

type Four<-vs: Array<Hv.VCpu>> is Data:
  IsFour{a: Hv.VCpu, b: Hv.VCpu, c: Hv.VCpu, d: Hv.VCpu, e: {Hv.four(a, b, c, d) == vs : Array<Hv.VCpu>}}

def two_view(xs: Array<Hv.VCpu>, sx: Hv.Shape(Hv.VCpu, xs, 1n)) -> Two<xs>:
  match xs:
    case ALeaf{x}:
      Empty.absurd(Two<ALeaf{x}>, sx)
    case ANode{ALeaf{a}, ALeaf{b}}:
      IsTwo{a, b, {==}}
    case ANode{ANode{p, q}, y}:
      Hv.Both{e, r} = sx
      Empty.absurd(Two<ANode{ANode{p, q}, y}>, e)
    case ANode{ALeaf{a}, ANode{p, q}}:
      Hv.Both{l, e} = sx
      Empty.absurd(Two<ANode{ALeaf{a}, ANode{p, q}}>, e)

def four_view.fin(-xs: Array<Hv.VCpu>, -ys: Array<Hv.VCpu>, tx: Two<xs>, ty: Two<ys>) -> Four<ANode{xs, ys}>:
  match tx ty:
    case IsTwo{a, b, ex} IsTwo{c, d, ey}:
      IsFour{a, b, c, d, (%ex : {Hv.four(a, b, c, d) == ANode{_, ys} : Array<Hv.VCpu>}; %ey : {Hv.four(a, b, c, d) == ANode{ANode{ALeaf{a}, ALeaf{b}}, _} : Array<Hv.VCpu>}; {==})}

def four_view.node(xs: Array<Hv.VCpu>, ys: Array<Hv.VCpu>, sv: Hv.Both<Hv.Shape(Hv.VCpu, xs, 1n), Hv.Shape(Hv.VCpu, ys, 1n)>) -> Four<ANode{xs, ys}>:
  Hv.Both{sx, sy} = sv
  four_view.fin(xs, ys, two_view(xs, sx), two_view(ys, sy))

def four_view(vs: Array<Hv.VCpu>, sv: Hv.Shape(Hv.VCpu, vs, 2n)) -> Four<vs>:
  match vs:
    case ALeaf{x}:
      Empty.absurd(Four<ALeaf{x}>, sv)
    case ANode{xs, ys}:
      four_view.node(xs, ys, sv)

def get_eta4(+a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +i: U32) -> {Array.get(Hv.VCpu, Hv.four(a, b, c, d), i) == (Hv.four(a, b, c, d), Pair.snd(Array<Hv.VCpu>, Hv.VCpu, Array.get(Hv.VCpu, Hv.four(a, b, c, d), i))) : Array<Hv.VCpu> & Hv.VCpu}:
  L.get_go_eta(Hv.VCpu, Hv.four(a, b, c, d), 4, U32.and(i, 3), U32.is_lt(U32.and(i, 3), 2))

def get_eta4.sym(+a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +i: U32) -> {(Hv.four(a, b, c, d), Pair.snd(Array<Hv.VCpu>, Hv.VCpu, Array.get(Hv.VCpu, Hv.four(a, b, c, d), i))) == Array.get(Hv.VCpu, Hv.four(a, b, c, d), i) : Array<Hv.VCpu> & Hv.VCpu}:
  Equal.sym(Array<Hv.VCpu> & Hv.VCpu, Array.get(Hv.VCpu, Hv.four(a, b, c, d), i), (Hv.four(a, b, c, d), Pair.snd(Array<Hv.VCpu>, Hv.VCpu, Array.get(Hv.VCpu, Hv.four(a, b, c, d), i))), get_eta4(a, b, c, d, i))

# Decisions keep the vCPUs
# ------------------------
# every decision hands the vCPU array on as it received it: the kernel
# writes a vCPU only in handle, before it decides

def first_live_eta4(order: List<&2, U32>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu) -> {Hv.first_live(order, Hv.four(a, b, c, d)) == (Hv.four(a, b, c, d), Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(order, Hv.four(a, b, c, d)))) : Array<Hv.VCpu> & Maybe<&2, U32>}:
  match order:
    case Nil{}:
      {==}
    case +g <> t:
      %Equal.sym(Array<Hv.VCpu> & Maybe<&2, U32>, Hv.first_live(t, Hv.four(a, b, c, d)), (Hv.four(a, b, c, d), Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(t, Hv.four(a, b, c, d)))), first_live_eta4(t, a, b, c, d)) : {Hv.first_live.fin(g, _) == (Hv.four(a, b, c, d), Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live.fin(g, _))) : Array<Hv.VCpu> & Maybe<&2, U32>}
      %get_eta4.sym(a, b, c, d, g) : {Hv.first_live.pick(g, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(t, Hv.four(a, b, c, d))), _) == (Hv.four(a, b, c, d), Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live.pick(g, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(t, Hv.four(a, b, c, d))), _))) : Array<Hv.VCpu> & Maybe<&2, U32>}
      {==}

def first_live_eta4.sym(+order: List<&2, U32>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu) -> {(Hv.four(a, b, c, d), Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(order, Hv.four(a, b, c, d)))) == Hv.first_live(order, Hv.four(a, b, c, d)) : Array<Hv.VCpu> & Maybe<&2, U32>}:
  Equal.sym(Array<Hv.VCpu> & Maybe<&2, U32>, Hv.first_live(order, Hv.four(a, b, c, d)), (Hv.four(a, b, c, d), Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(order, Hv.four(a, b, c, d)))), first_live_eta4(order, a, b, c, d))

def sched_at_vcpus4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, pick: Maybe<&2, U32>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu) -> {Hv.Step.vcpus(Hv.sched.at(k, ps, cur, pick, Hv.four(a, b, c, d))) == Hv.four(a, b, c, d) : Array<Hv.VCpu>}:
  match k pick:
    case kk None{}:
      {==}
    case Hv.Kernel{+n, +next, +slice} Some{+g}:
      %get_eta4.sym(a, b, c, d, g) : {Hv.Step.vcpus(Hv.sched.go(Hv.Kernel{n, next, slice}, ps, g, _)) == Hv.four(a, b, c, d) : Array<Hv.VCpu>}
      {==}

def sched_vcpus4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> {Hv.Step.vcpus(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) == Hv.four(a, b, c, d) : Array<Hv.VCpu>}:
  match k:
    case Hv.Kernel{+n, +next, +slice}:
      %first_live_eta4.sym(Hv.rotation(next), a, b, c, d) : {Hv.Step.vcpus(Hv.sched.fin(Hv.Kernel{n, next, slice}, ps, cur, _)) == Hv.four(a, b, c, d) : Array<Hv.VCpu>}
      sched_at_vcpus4(Hv.Kernel{n, next, slice}, ps, cur, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(Hv.rotation(next), Hv.four(a, b, c, d))), a, b, c, d)

def prepend_vcpus(x: Hv.Action, s: Hv.Step) -> {Hv.Step.vcpus(Hv.prepend(x, s)) == Hv.Step.vcpus(s) : Array<Hv.VCpu>}:
  match s:
    case Hv.Go{k, m, acts}:
      {==}
    case Hv.Fin{k, m, acts}:
      {==}

def resume_vcpus4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> {Hv.Step.vcpus(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) == Hv.four(a, b, c, d) : Array<Hv.VCpu>}:
  %get_eta4.sym(a, b, c, d, cur) : {Hv.Step.vcpus(Hv.resume.fin(k, ps, cur, _)) == Hv.four(a, b, c, d) : Array<Hv.VCpu>}
  {==}

def halt_vcpus4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> {Hv.Step.vcpus(Hv.halt(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) == Hv.four(a, b, c, d) : Array<Hv.VCpu>}:
  Equal.trans(Array<Hv.VCpu>, Hv.Step.vcpus(Hv.prepend(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Step.vcpus(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), Hv.four(a, b, c, d),
    prepend_vcpus(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})),
    sched_vcpus4(k, ps, a, b, c, d, cur))

def hvc_vcpus4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, call: Hv.Call, +r: Hv.Regs) -> {Hv.Step.vcpus(Hv.hvc(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, call, r)) == Hv.four(a, b, c, d) : Array<Hv.VCpu>}:
  match call:
    case Hv.Yield{}:
      sched_vcpus4(k, ps, a, b, c, d, cur)
    case Hv.Put{}:
      Equal.trans(Array<Hv.VCpu>, Hv.Step.vcpus(Hv.prepend(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Step.vcpus(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), Hv.four(a, b, c, d),
        prepend_vcpus(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})),
        resume_vcpus4(k, ps, a, b, c, d, cur))
    case Hv.Quit{}:
      halt_vcpus4(k, ps, a, b, c, d, cur)
    case Hv.Bad{}:
      resume_vcpus4(k, ps, a, b, c, d, cur)

def decide_vcpus4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, e: Hv.Exit) -> {Hv.Step.vcpus(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)) == Hv.four(a, b, c, d) : Array<Hv.VCpu>}:
  match e:
    case Hv.Timer{r}:
      sched_vcpus4(k, ps, a, b, c, d, cur)
    case Hv.Wfi{r}:
      sched_vcpus4(k, ps, a, b, c, d, cur)
    case Hv.Hvc{+imm, +r}:
      hvc_vcpus4(k, ps, a, b, c, d, cur, Hv.decode(imm), r)
    case Hv.DataAbort{ipa, w, r}:
      halt_vcpus4(k, ps, a, b, c, d, cur)
    case Hv.InstAbort{ipa, r}:
      halt_vcpus4(k, ps, a, b, c, d, cur)
    case Hv.Fault{esr, r}:
      halt_vcpus4(k, ps, a, b, c, d, cur)

# Slot updates
# ------------
# at_upd<K>: writing slot K leaves every other slot as it was

def at_upd0.go(+x: Hv.VCpu, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -g: U32, vg: L.Lt4<g>, ne: {U32.is_ne(g, 0) == True{} : Bool}) -> {Hv.vcpu_at(Hv.four(x, b, c, d), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  match vg:
    case L.K0{e}:
      Empty.absurd({Hv.vcpu_at(Hv.four(x, b, c, d), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}, L.false_true((%Equal.sym(U32, 0, g, e) : {U32.is_ne(_, 0) == True{} : Bool}; ne)))
    case L.K1{e}:
      %e : {Hv.vcpu_at(Hv.four(x, b, c, d), _) == Hv.vcpu_at(Hv.four(a, b, c, d), _) : Hv.VCpu}
      {==}
    case L.K2{e}:
      %e : {Hv.vcpu_at(Hv.four(x, b, c, d), _) == Hv.vcpu_at(Hv.four(a, b, c, d), _) : Hv.VCpu}
      {==}
    case L.K3{e}:
      %e : {Hv.vcpu_at(Hv.four(x, b, c, d), _) == Hv.vcpu_at(Hv.four(a, b, c, d), _) : Hv.VCpu}
      {==}

def at_upd0(+x: Hv.VCpu, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +g: U32, sg: Hv.Slot(g), ne: {U32.is_ne(g, 0) == True{} : Bool}) -> {Hv.vcpu_at(Hv.four(x, b, c, d), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  at_upd0.go(x, a, b, c, d, g, L.lt4(g, sg), ne)

def at_upd1.go(+x: Hv.VCpu, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -g: U32, vg: L.Lt4<g>, ne: {U32.is_ne(g, 1) == True{} : Bool}) -> {Hv.vcpu_at(Hv.four(a, x, c, d), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  match vg:
    case L.K0{e}:
      %e : {Hv.vcpu_at(Hv.four(a, x, c, d), _) == Hv.vcpu_at(Hv.four(a, b, c, d), _) : Hv.VCpu}
      {==}
    case L.K1{e}:
      Empty.absurd({Hv.vcpu_at(Hv.four(a, x, c, d), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}, L.false_true((%Equal.sym(U32, 1, g, e) : {U32.is_ne(_, 1) == True{} : Bool}; ne)))
    case L.K2{e}:
      %e : {Hv.vcpu_at(Hv.four(a, x, c, d), _) == Hv.vcpu_at(Hv.four(a, b, c, d), _) : Hv.VCpu}
      {==}
    case L.K3{e}:
      %e : {Hv.vcpu_at(Hv.four(a, x, c, d), _) == Hv.vcpu_at(Hv.four(a, b, c, d), _) : Hv.VCpu}
      {==}

def at_upd1(+x: Hv.VCpu, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +g: U32, sg: Hv.Slot(g), ne: {U32.is_ne(g, 1) == True{} : Bool}) -> {Hv.vcpu_at(Hv.four(a, x, c, d), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  at_upd1.go(x, a, b, c, d, g, L.lt4(g, sg), ne)

def at_upd2.go(+x: Hv.VCpu, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -g: U32, vg: L.Lt4<g>, ne: {U32.is_ne(g, 2) == True{} : Bool}) -> {Hv.vcpu_at(Hv.four(a, b, x, d), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  match vg:
    case L.K0{e}:
      %e : {Hv.vcpu_at(Hv.four(a, b, x, d), _) == Hv.vcpu_at(Hv.four(a, b, c, d), _) : Hv.VCpu}
      {==}
    case L.K1{e}:
      %e : {Hv.vcpu_at(Hv.four(a, b, x, d), _) == Hv.vcpu_at(Hv.four(a, b, c, d), _) : Hv.VCpu}
      {==}
    case L.K2{e}:
      Empty.absurd({Hv.vcpu_at(Hv.four(a, b, x, d), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}, L.false_true((%Equal.sym(U32, 2, g, e) : {U32.is_ne(_, 2) == True{} : Bool}; ne)))
    case L.K3{e}:
      %e : {Hv.vcpu_at(Hv.four(a, b, x, d), _) == Hv.vcpu_at(Hv.four(a, b, c, d), _) : Hv.VCpu}
      {==}

def at_upd2(+x: Hv.VCpu, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +g: U32, sg: Hv.Slot(g), ne: {U32.is_ne(g, 2) == True{} : Bool}) -> {Hv.vcpu_at(Hv.four(a, b, x, d), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  at_upd2.go(x, a, b, c, d, g, L.lt4(g, sg), ne)

def at_upd3.go(+x: Hv.VCpu, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -g: U32, vg: L.Lt4<g>, ne: {U32.is_ne(g, 3) == True{} : Bool}) -> {Hv.vcpu_at(Hv.four(a, b, c, x), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  match vg:
    case L.K0{e}:
      %e : {Hv.vcpu_at(Hv.four(a, b, c, x), _) == Hv.vcpu_at(Hv.four(a, b, c, d), _) : Hv.VCpu}
      {==}
    case L.K1{e}:
      %e : {Hv.vcpu_at(Hv.four(a, b, c, x), _) == Hv.vcpu_at(Hv.four(a, b, c, d), _) : Hv.VCpu}
      {==}
    case L.K2{e}:
      %e : {Hv.vcpu_at(Hv.four(a, b, c, x), _) == Hv.vcpu_at(Hv.four(a, b, c, d), _) : Hv.VCpu}
      {==}
    case L.K3{e}:
      Empty.absurd({Hv.vcpu_at(Hv.four(a, b, c, x), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}, L.false_true((%Equal.sym(U32, 3, g, e) : {U32.is_ne(_, 3) == True{} : Bool}; ne)))

def at_upd3(+x: Hv.VCpu, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +g: U32, sg: Hv.Slot(g), ne: {U32.is_ne(g, 3) == True{} : Bool}) -> {Hv.vcpu_at(Hv.four(a, b, c, x), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  at_upd3.go(x, a, b, c, d, g, L.lt4(g, sg), ne)

# Frame
# -----

def frame.k0(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, +g: U32, sg: Hv.Slot(g), ne: {U32.is_ne(g, 0) == True{} : Bool}) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 0}, e)), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  %Equal.sym(Array<Hv.VCpu>, Hv.Step.vcpus(Hv.decide(k, Hv.Machine{ps, Hv.four(Hv.VCpu.step(a, e), b, c, d), 0}, e)), Hv.four(Hv.VCpu.step(a, e), b, c, d), decide_vcpus4(k, ps, Hv.VCpu.step(a, e), b, c, d, 0, e)) : {Hv.vcpu_at(_, g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}
  at_upd0(Hv.VCpu.step(a, e), a, b, c, d, g, sg, ne)

def frame.k1(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, +g: U32, sg: Hv.Slot(g), ne: {U32.is_ne(g, 1) == True{} : Bool}) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 1}, e)), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  %Equal.sym(Array<Hv.VCpu>, Hv.Step.vcpus(Hv.decide(k, Hv.Machine{ps, Hv.four(a, Hv.VCpu.step(b, e), c, d), 1}, e)), Hv.four(a, Hv.VCpu.step(b, e), c, d), decide_vcpus4(k, ps, a, Hv.VCpu.step(b, e), c, d, 1, e)) : {Hv.vcpu_at(_, g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}
  at_upd1(Hv.VCpu.step(b, e), a, b, c, d, g, sg, ne)

def frame.k2(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, +g: U32, sg: Hv.Slot(g), ne: {U32.is_ne(g, 2) == True{} : Bool}) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 2}, e)), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  %Equal.sym(Array<Hv.VCpu>, Hv.Step.vcpus(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, Hv.VCpu.step(c, e), d), 2}, e)), Hv.four(a, b, Hv.VCpu.step(c, e), d), decide_vcpus4(k, ps, a, b, Hv.VCpu.step(c, e), d, 2, e)) : {Hv.vcpu_at(_, g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}
  at_upd2(Hv.VCpu.step(c, e), a, b, c, d, g, sg, ne)

def frame.k3(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, +g: U32, sg: Hv.Slot(g), ne: {U32.is_ne(g, 3) == True{} : Bool}) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 3}, e)), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  %Equal.sym(Array<Hv.VCpu>, Hv.Step.vcpus(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, Hv.VCpu.step(d, e)), 3}, e)), Hv.four(a, b, c, Hv.VCpu.step(d, e)), decide_vcpus4(k, ps, a, b, c, Hv.VCpu.step(d, e), 3, e)) : {Hv.vcpu_at(_, g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}
  at_upd3(Hv.VCpu.step(d, e), a, b, c, d, g, sg, ne)

def frame.c(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -cur: U32, +e: Hv.Exit, +g: U32, vc: L.Lt4<cur>, sg: Hv.Slot(g), ne: {U32.is_ne(g, cur) == True{} : Bool}) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  match vc:
    case L.K0{+ec}:
      %ec : {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}
      frame.k0(k, ps, a, b, c, d, e, g, sg, (%Equal.sym(U32, 0, cur, ec) : {U32.is_ne(g, _) == True{} : Bool}; ne))
    case L.K1{+ec}:
      %ec : {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}
      frame.k1(k, ps, a, b, c, d, e, g, sg, (%Equal.sym(U32, 1, cur, ec) : {U32.is_ne(g, _) == True{} : Bool}; ne))
    case L.K2{+ec}:
      %ec : {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}
      frame.k2(k, ps, a, b, c, d, e, g, sg, (%Equal.sym(U32, 2, cur, ec) : {U32.is_ne(g, _) == True{} : Bool}; ne))
    case L.K3{+ec}:
      %ec : {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}
      frame.k3(k, ps, a, b, c, d, e, g, sg, (%Equal.sym(U32, 3, cur, ec) : {U32.is_ne(g, _) == True{} : Bool}; ne))

def frame.b(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, -vs: Array<Hv.VCpu>, +cur: U32, +e: Hv.Exit, +g: U32, v4: Four<vs>, sc: Hv.Slot(cur), sg: Hv.Slot(g), ne: {U32.is_ne(g, cur) == True{} : Bool}) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, vs, cur}, e)), g) == Hv.vcpu_at(vs, g) : Hv.VCpu}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev}:
      %ev : {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, _, cur}, e)), g) == Hv.vcpu_at(_, g) : Hv.VCpu}
      frame.c(k, ps, a, b, c, d, cur, e, g, L.lt4(cur, sc), sg, ne)

def frame.a(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, vs: Array<Hv.VCpu>, +cur: U32, +e: Hv.Exit, +g: U32, ok: Hv.Machine.ok(Hv.Machine{ps, vs, cur}), sg: Hv.Slot(g), ne: {U32.is_ne(g, cur) == True{} : Bool}) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, vs, cur}, e)), g) == Hv.vcpu_at(vs, g) : Hv.VCpu}:
  Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
  frame.b(k, ps, vs, cur, e, g, four_view(vs, sv), sc, sg, ne)

def Laws.handle_frame(k, m, e, g, ok, sg, ne):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      frame.a(k, ps, vs, cur, e, g, ok, sg, ne)

# Slots of a decision
# -------------------
# the guest a decision enters is a slot: it comes from the rotation, and
# every entry of the rotation is masked to two bits

def slot_and.go(-x: U32, v: L.Low2<x>) -> Hv.Slot(U32.and(x, 3)):
  match v:
    case L.L0{e}:
      %e : {U32.is_lt(_, 4) == True{} : Bool}
      {==}
    case L.L1{e}:
      %e : {U32.is_lt(_, 4) == True{} : Bool}
      {==}
    case L.L2{e}:
      %e : {U32.is_lt(_, 4) == True{} : Bool}
      {==}
    case L.L3{e}:
      %e : {U32.is_lt(_, 4) == True{} : Bool}
      {==}

def slot_and(x: U32) -> Hv.Slot(U32.and(x, 3)):
  slot_and.go(x, L.low2(x))

def AllSlots(order: List<&2, U32>) -> Data:
  match order:
    case Nil{}:
      Unit
    case g <> t:
      Hv.Both<Hv.Slot(g), AllSlots(t)>

def MSlot(p: Maybe<&2, U32>) -> Data:
  match p:
    case None{}:
      Unit
    case Some{g}:
      Hv.Slot(g)

def rot_slots(+next: U32) -> AllSlots(Hv.rotation(next)):
  Hv.Both{slot_and(next), Hv.Both{slot_and(U32.add(next, 1)),
    Hv.Both{slot_and(U32.add(next, 2)), Hv.Both{slot_and(U32.add(next, 3)), Unit{}}}}}

def mslot_pick(b: Bool, -g: U32, -r: Maybe<&2, U32>, sg: Hv.Slot(g), sr: MSlot(r)) -> MSlot(Bool.pick(Maybe<&2, U32>, b, Some{g}, r)):
  match b:
    case False{}:
      sr
    case True{}:
      sg

def first_live_slot(order: List<&2, U32>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, al: AllSlots(order)) -> MSlot(Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(order, Hv.four(a, b, c, d)))):
  match order:
    case Nil{}:
      Unit{}
    case +g <> +t:
      Hv.Both{sg, st} = al
      %first_live_eta4.sym(t, a, b, c, d) : MSlot(Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live.fin(g, _)))
      %get_eta4.sym(a, b, c, d, g) : MSlot(Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live.pick(g, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(t, Hv.four(a, b, c, d))), _)))
      mslot_pick(Hv.VCpu.live(Pair.snd(Array<Hv.VCpu>, Hv.VCpu, Array.get(Hv.VCpu, Hv.four(a, b, c, d), g))), g, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(t, Hv.four(a, b, c, d))), sg, first_live_slot(t, a, b, c, d, st))

# Decisions keep the machine
# --------------------------
# the machine a decision hands on has the pages and the vCPUs it got, and
# a slot on the core

def Keeps(+ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, m: Hv.Machine) -> Data:
  match m:
    case Hv.Machine{ps2, vs2, cur2}:
      Hv.Both<{ps2 == ps : Hv.Tree<Hv.Owner>},
        Hv.Both<{vs2 == Hv.four(a, b, c, d) : Array<Hv.VCpu>}, Hv.Slot(cur2)>>

def prepend_m(x: Hv.Action, s: Hv.Step) -> {Hv.Step.m(Hv.prepend(x, s)) == Hv.Step.m(s) : Hv.Machine}:
  match s:
    case Hv.Go{k, m, acts}:
      {==}
    case Hv.Fin{k, m, acts}:
      {==}

def sched_at_keeps4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, pick: Maybe<&2, U32>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, sc: Hv.Slot(cur), mp: MSlot(pick)) -> Keeps(ps, a, b, c, d, Hv.Step.m(Hv.sched.at(k, ps, cur, pick, Hv.four(a, b, c, d)))):
  match k pick:
    case kk None{}:
      Hv.Both{{==}, Hv.Both{{==}, sc}}
    case Hv.Kernel{+n, +next, +slice} Some{+g}:
      %get_eta4.sym(a, b, c, d, g) : Keeps(ps, a, b, c, d, Hv.Step.m(Hv.sched.go(Hv.Kernel{n, next, slice}, ps, g, _)))
      Hv.Both{{==}, Hv.Both{{==}, mp}}

def sched_keeps4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, sc: Hv.Slot(cur)) -> Keeps(ps, a, b, c, d, Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))):
  match k:
    case Hv.Kernel{+n, +next, +slice}:
      %first_live_eta4.sym(Hv.rotation(next), a, b, c, d) : Keeps(ps, a, b, c, d, Hv.Step.m(Hv.sched.fin(Hv.Kernel{n, next, slice}, ps, cur, _)))
      sched_at_keeps4(Hv.Kernel{n, next, slice}, ps, cur, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(Hv.rotation(next), Hv.four(a, b, c, d))), a, b, c, d, sc,
        first_live_slot(Hv.rotation(next), a, b, c, d, rot_slots(next)))

def resume_keeps4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, sc: Hv.Slot(cur)) -> Keeps(ps, a, b, c, d, Hv.Step.m(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))):
  %get_eta4.sym(a, b, c, d, cur) : Keeps(ps, a, b, c, d, Hv.Step.m(Hv.resume.fin(k, ps, cur, _)))
  Hv.Both{{==}, Hv.Both{{==}, sc}}

def halt_keeps4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, sc: Hv.Slot(cur)) -> Keeps(ps, a, b, c, d, Hv.Step.m(Hv.halt(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))):
  %Equal.sym(Hv.Machine, Hv.Step.m(Hv.prepend(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), prepend_m(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) : Keeps(ps, a, b, c, d, _)
  sched_keeps4(k, ps, a, b, c, d, cur, sc)

def hvc_keeps4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, call: Hv.Call, +r: Hv.Regs, sc: Hv.Slot(cur)) -> Keeps(ps, a, b, c, d, Hv.Step.m(Hv.hvc(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, call, r))):
  match call:
    case Hv.Yield{}:
      sched_keeps4(k, ps, a, b, c, d, cur, sc)
    case Hv.Put{}:
      %Equal.sym(Hv.Machine, Hv.Step.m(Hv.prepend(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Step.m(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), prepend_m(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) : Keeps(ps, a, b, c, d, _)
      resume_keeps4(k, ps, a, b, c, d, cur, sc)
    case Hv.Quit{}:
      halt_keeps4(k, ps, a, b, c, d, cur, sc)
    case Hv.Bad{}:
      resume_keeps4(k, ps, a, b, c, d, cur, sc)

def decide_keeps4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, e: Hv.Exit, sc: Hv.Slot(cur)) -> Keeps(ps, a, b, c, d, Hv.Step.m(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e))):
  match e:
    case Hv.Timer{r}:
      sched_keeps4(k, ps, a, b, c, d, cur, sc)
    case Hv.Wfi{r}:
      sched_keeps4(k, ps, a, b, c, d, cur, sc)
    case Hv.Hvc{+imm, +r}:
      hvc_keeps4(k, ps, a, b, c, d, cur, Hv.decode(imm), r, sc)
    case Hv.DataAbort{ipa, w, r}:
      halt_keeps4(k, ps, a, b, c, d, cur, sc)
    case Hv.InstAbort{ipa, r}:
      halt_keeps4(k, ps, a, b, c, d, cur, sc)
    case Hv.Fault{esr, r}:
      halt_keeps4(k, ps, a, b, c, d, cur, sc)

def keeps_ok(+ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, m: Hv.Machine, kp: Keeps(ps, a, b, c, d, m), sp: Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()), op: Hv.Owners.ok(ps)) -> Hv.Machine.ok(m):
  match m:
    case Hv.Machine{+ps2, vs2, cur2}:
      Hv.Both{+ep, Hv.Both{ev, sc}} = kp
      Hv.Both{(%Equal.sym(Hv.Tree<Hv.Owner>, ps2, ps, ep) : Hv.Tree.shape(Hv.Owner, _, Hv.page_depth()); sp),
        Hv.Both{(%Equal.sym(Hv.Tree<Hv.Owner>, ps2, ps, ep) : Hv.Owners.ok(_); op),
          Hv.Both{(%Equal.sym(Array<Hv.VCpu>, vs2, Hv.four(a, b, c, d), ev) : Hv.Shape(Hv.VCpu, _, Hv.vcpu_depth()); Hv.Both{Hv.Both{Unit{}, Unit{}}, Hv.Both{Unit{}, Unit{}}}),
            sc}}}

def keeps_pages(-ps: Hv.Tree<Hv.Owner>, -a: Hv.VCpu, -b: Hv.VCpu, -c: Hv.VCpu, -d: Hv.VCpu, m: Hv.Machine, kp: Keeps(ps, a, b, c, d, m)) -> {Hv.Machine.pages(m) == ps : Hv.Tree<Hv.Owner>}:
  match m:
    case Hv.Machine{ps2, vs2, cur2}:
      Hv.Both{ep, r} = kp
      ep

# Entries
# -------

def Entered(s: Hv.Step) -> Type:
  {Hv.Step.entry(s) == Hv.Step.saved(s) : Maybe<&2, Hv.Entry>}

def sched_at_entry4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, pick: Maybe<&2, U32>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu) -> Entered(Hv.sched.at(k, ps, cur, pick, Hv.four(a, b, c, d))):
  match k pick:
    case kk None{}:
      {==}
    case Hv.Kernel{+n, +next, +slice} Some{+g}:
      %get_eta4.sym(a, b, c, d, g) : Entered(Hv.sched.go(Hv.Kernel{n, next, slice}, ps, g, _))
      {==}

def sched_entry4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> Entered(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})):
  match k:
    case Hv.Kernel{+n, +next, +slice}:
      %first_live_eta4.sym(Hv.rotation(next), a, b, c, d) : Entered(Hv.sched.fin(Hv.Kernel{n, next, slice}, ps, cur, _))
      sched_at_entry4(Hv.Kernel{n, next, slice}, ps, cur, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(Hv.rotation(next), Hv.four(a, b, c, d))), a, b, c, d)

# a Stop or a Print before a decision enters no one
def prepend_stop_entry(+g: U32, s: Hv.Step, e: Entered(s)) -> Entered(Hv.prepend(Hv.Stop{g}, s)):
  match s:
    case Hv.Go{k, Hv.Machine{ps, vs, cur}, acts}:
      e
    case Hv.Fin{k, m, acts}:
      e

def prepend_print_entry(t: String, s: Hv.Step, e: Entered(s)) -> Entered(Hv.prepend(Hv.Print{t}, s)):
  match s:
    case Hv.Go{k, Hv.Machine{ps, vs, cur}, acts}:
      e
    case Hv.Fin{k, m, acts}:
      e

def resume_entry4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> Entered(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})):
  %get_eta4.sym(a, b, c, d, cur) : Entered(Hv.resume.fin(k, ps, cur, _))
  {==}

def halt_entry4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> Entered(Hv.halt(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})):
  prepend_stop_entry(cur, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), sched_entry4(k, ps, a, b, c, d, cur))

def hvc_entry4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, call: Hv.Call, +r: Hv.Regs) -> Entered(Hv.hvc(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, call, r)):
  match call:
    case Hv.Yield{}:
      sched_entry4(k, ps, a, b, c, d, cur)
    case Hv.Put{}:
      prepend_print_entry(Hv.char_of(Hv.Regs.x0(r)), Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), resume_entry4(k, ps, a, b, c, d, cur))
    case Hv.Quit{}:
      halt_entry4(k, ps, a, b, c, d, cur)
    case Hv.Bad{}:
      resume_entry4(k, ps, a, b, c, d, cur)

def decide_entry4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, e: Hv.Exit) -> Entered(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)):
  match e:
    case Hv.Timer{r}:
      sched_entry4(k, ps, a, b, c, d, cur)
    case Hv.Wfi{r}:
      sched_entry4(k, ps, a, b, c, d, cur)
    case Hv.Hvc{+imm, +r}:
      hvc_entry4(k, ps, a, b, c, d, cur, Hv.decode(imm), r)
    case Hv.DataAbort{ipa, w, r}:
      halt_entry4(k, ps, a, b, c, d, cur)
    case Hv.InstAbort{ipa, r}:
      halt_entry4(k, ps, a, b, c, d, cur)
    case Hv.Fault{esr, r}:
      halt_entry4(k, ps, a, b, c, d, cur)

# Record
# ------

def owner_rt.of(-g: U32, v: L.Lt4<g>) -> {Hv.Owner.decode(Hv.Owner.encode(Hv.Of{g})) == Hv.Of{g} : Hv.Owner}:
  match v:
    case L.K0{e}:
      %e : {Hv.Owner.decode(Hv.Owner.encode(Hv.Of{_})) == Hv.Of{_} : Hv.Owner}
      {==}
    case L.K1{e}:
      %e : {Hv.Owner.decode(Hv.Owner.encode(Hv.Of{_})) == Hv.Of{_} : Hv.Owner}
      {==}
    case L.K2{e}:
      %e : {Hv.Owner.decode(Hv.Owner.encode(Hv.Of{_})) == Hv.Of{_} : Hv.Owner}
      {==}
    case L.K3{e}:
      %e : {Hv.Owner.decode(Hv.Owner.encode(Hv.Of{_})) == Hv.Of{_} : Hv.Owner}
      {==}

def owner_rt(o: Hv.Owner, ok: Hv.Owner.ok(o)) -> {Hv.Owner.decode(Hv.Owner.encode(o)) == o : Hv.Owner}:
  match o:
    case Hv.Free{}:
      {==}
    case Hv.Hyp{}:
      {==}
    case Hv.Of{g}:
      owner_rt.of(g, L.lt4(g, ok))

def owners_rt(+ps: Hv.Tree<Hv.Owner>, +d: Nat, sh: Hv.Tree.shape(Hv.Owner, ps, d), ok: Hv.Owners.ok(ps), -r: List<&2, U32>) -> {Hv.owners_take(d, Hv.owners_encode(ps, r)) == Some{(ps, r)} : Maybe<(Hv.Tree<Hv.Owner> & List<&2, U32>)>}:
  match ps d:
    case Hv.Leaf{+o} 0n:
      %Equal.sym(Hv.Owner, Hv.Owner.decode(Hv.Owner.encode(o)), o, owner_rt(o, ok)) : {Some{(Hv.Leaf{_}, r)} == Some{(Hv.Leaf{o}, r)} : Maybe<(Hv.Tree<Hv.Owner> & List<&2, U32>)>}
      {==}
    case Hv.Node{lo, hi} 0n:
      Empty.absurd({Hv.owners_take(0n, Hv.owners_encode(Hv.Node{lo, hi}, r)) == Some{(Hv.Node{lo, hi}, r)} : Maybe<(Hv.Tree<Hv.Owner> & List<&2, U32>)>}, sh)
    case Hv.Leaf{o} 1n+p:
      Empty.absurd({Hv.owners_take(1n+p, Hv.owners_encode(Hv.Leaf{o}, r)) == Some{(Hv.Leaf{o}, r)} : Maybe<(Hv.Tree<Hv.Owner> & List<&2, U32>)>}, sh)
    case Hv.Node{+lo, +hi} 1n+p:
      Hv.Both{shl, shh} = sh
      Hv.Both{okl, okh} = ok
      %Equal.sym(Maybe<(Hv.Tree<Hv.Owner> & List<&2, U32>)>, Hv.owners_take(p, Hv.owners_encode(lo, Hv.owners_encode(hi, r))), Some{(lo, Hv.owners_encode(hi, r))}, owners_rt(lo, p, shl, okl, Hv.owners_encode(hi, r))) : {Hv.owners_take.node(_, rest => Hv.owners_take(p, rest)) == Some{(Hv.Node{lo, hi}, r)} : Maybe<(Hv.Tree<Hv.Owner> & List<&2, U32>)>}
      %Equal.sym(Maybe<(Hv.Tree<Hv.Owner> & List<&2, U32>)>, Hv.owners_take(p, Hv.owners_encode(hi, r)), Some{(hi, r)}, owners_rt(hi, p, shh, okh, r)) : {Hv.owners_take.fin(lo, _) == Some{(Hv.Node{lo, hi}, r)} : Maybe<(Hv.Tree<Hv.Owner> & List<&2, U32>)>}
      {==}

def vcpu_rt(v: Hv.VCpu, -r: List<&2, U32>) -> {Hv.vcpus_take(0n, Hv.VCpu.encode(v, r)) == Some{(ALeaf{v}, r)} : Maybe<(Array<Hv.VCpu> & List<&2, U32>)>}:
  match v:
    case Hv.VCpu{Hv.Regs{Hv.W64{a0, a1}, Hv.W64{b0, b1}, Hv.W64{c0, c1}, Hv.W64{d0, d1}, Hv.W64{e0, e1}}, False{}}:
      {==}
    case Hv.VCpu{Hv.Regs{Hv.W64{a0, a1}, Hv.W64{b0, b1}, Hv.W64{c0, c1}, Hv.W64{d0, d1}, Hv.W64{e0, e1}}, True{}}:
      {==}

def vcpus_rt(vs: Array<Hv.VCpu>, +d: Nat, sh: Hv.Shape(Hv.VCpu, vs, d), -r: List<&2, U32>) -> {Hv.vcpus_take(d, Hv.vcpus_encode(vs, r)) == Some{(vs, r)} : Maybe<(Array<Hv.VCpu> & List<&2, U32>)>}:
  match vs d:
    case ALeaf{v} 0n:
      vcpu_rt(v, r)
    case ANode{xs, ys} 0n:
      Empty.absurd({Hv.vcpus_take(0n, Hv.vcpus_encode(ANode{xs, ys}, r)) == Some{(ANode{xs, ys}, r)} : Maybe<(Array<Hv.VCpu> & List<&2, U32>)>}, sh)
    case ALeaf{v} 1n+p:
      Empty.absurd({Hv.vcpus_take(1n+p, Hv.vcpus_encode(ALeaf{v}, r)) == Some{(ALeaf{v}, r)} : Maybe<(Array<Hv.VCpu> & List<&2, U32>)>}, sh)
    case ANode{xs, ys} 1n+p:
      Hv.Both{shx, shy} = sh
      %Equal.sym(Maybe<(Array<Hv.VCpu> & List<&2, U32>)>, Hv.vcpus_take(p, Hv.vcpus_encode(xs, Hv.vcpus_encode(ys, r))), Some{(xs, Hv.vcpus_encode(ys, r))}, vcpus_rt(xs, p, shx, Hv.vcpus_encode(ys, r))) : {Hv.vcpus_take.node(_, rest => Hv.vcpus_take(p, rest)) == Some{(ANode{xs, ys}, r)} : Maybe<(Array<Hv.VCpu> & List<&2, U32>)>}
      %Equal.sym(Maybe<(Array<Hv.VCpu> & List<&2, U32>)>, Hv.vcpus_take(p, Hv.vcpus_encode(ys, r)), Some{(ys, r)}, vcpus_rt(ys, p, shy, r)) : {Hv.vcpus_take.fin(xs, _) == Some{(ANode{xs, ys}, r)} : Maybe<(Array<Hv.VCpu> & List<&2, U32>)>}
      {==}

# Validation, both ways
# ---------------------
# the decoder's checks are Bools; these are the two directions between
# them and the facts Machine.ok is made of

def okb_of_owner(o: Hv.Owner, ok: Hv.Owner.ok(o)) -> {Hv.Owner.okb(o) == True{} : Bool}:
  match o:
    case Hv.Free{}:
      {==}
    case Hv.Hyp{}:
      {==}
    case Hv.Of{g}:
      ok

def okb_of_ok(t: Hv.Tree<Hv.Owner>, ok: Hv.Owners.ok(t)) -> {Hv.Owners.okb(t) == True{} : Bool}:
  match t:
    case Hv.Leaf{o}:
      okb_of_owner(o, ok)
    case Hv.Node{lo, hi}:
      Hv.Both{okl, okh} = ok
      %Equal.sym(Bool, Hv.Owners.okb(lo), True{}, okb_of_ok(lo, okl)) : {Bool.and(_, Hv.Owners.okb(hi)) == True{} : Bool}
      okb_of_ok(hi, okh)

def shapeb_of_shape(t: Hv.Tree<Hv.Owner>, +d: Nat, sh: Hv.Tree.shape(Hv.Owner, t, d)) -> {Hv.Tree.shapeb(t, d) == True{} : Bool}:
  match t d:
    case Hv.Leaf{o} 0n:
      {==}
    case Hv.Node{lo, hi} 0n:
      Empty.absurd({Hv.Tree.shapeb(Hv.Node{lo, hi}, 0n) == True{} : Bool}, sh)
    case Hv.Leaf{o} 1n+p:
      Empty.absurd({Hv.Tree.shapeb(Hv.Leaf{o}, 1n+p) == True{} : Bool}, sh)
    case Hv.Node{lo, hi} 1n+p:
      Hv.Both{shl, shh} = sh
      %Equal.sym(Bool, Hv.Tree.shapeb(lo, p), True{}, shapeb_of_shape(lo, p, shl)) : {Bool.and(_, Hv.Tree.shapeb(hi, p)) == True{} : Bool}
      shapeb_of_shape(hi, p, shh)

# a list of words equals itself
def list_eq_refl(xs: List<&2, U32>) -> {Hv.U32.list_eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %Equal.sym(Bool, U32.is_eq(x, x), True{}, L.u32_refl(x)) : {Bool.and(_, Hv.U32.list_eq(t, t)) == True{} : Bool}
      list_eq_refl(t)

# and a list the decoder accepted is the one it re-encoded
def list_eq_sound(+a: List<&2, U32>, +b: List<&2, U32>, +e: {Hv.U32.list_eq(a, b) == True{} : Bool}) -> {a == b : List<&2, U32>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> ys:
      Empty.absurd({Nil{} == y <> ys : List<&2, U32>}, L.false_true(e))
    case x <> xs Nil{}:
      Empty.absurd({x <> xs == Nil{} : List<&2, U32>}, L.false_true(e))
    case +x <> +xs +y <> +ys:
      %L.u32_eq(x, y, L.and_l(U32.is_eq(x, y), Hv.U32.list_eq(xs, ys), e)) : {x <> xs == _ <> ys : List<&2, U32>}
      %list_eq_sound(xs, ys, L.and_r(U32.is_eq(x, y), Hv.U32.list_eq(xs, ys), e)) : {x <> xs == x <> _ : List<&2, U32>}
      {==}

# one vCPU's words are taken back as that vCPU
def vcpu_take_rt(v: Hv.VCpu, -r: List<&2, U32>) -> {Hv.vcpu_take(Hv.VCpu.encode(v, r)) == Some{(v, r)} : Maybe<(Hv.VCpu & List<&2, U32>)>}:
  match v:
    case Hv.VCpu{Hv.Regs{Hv.W64{a0, a1}, Hv.W64{b0, b1}, Hv.W64{c0, c1}, Hv.W64{d0, d1}, Hv.W64{e0, e1}}, False{}}:
      {==}
    case Hv.VCpu{Hv.Regs{Hv.W64{a0, a1}, Hv.W64{b0, b1}, Hv.W64{c0, c1}, Hv.W64{d0, d1}, Hv.W64{e0, e1}}, True{}}:
      {==}

def roundtrip4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, +sp: Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()), +op: Hv.Owners.ok(ps), +sc: Hv.Slot(cur)) -> {Hv.decode_record(Hv.encode(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) == Some{(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})} : Maybe<(Hv.Kernel & Hv.Machine)>}:
  match k:
    case Hv.Kernel{+n, +next, +slice}:
      %Equal.sym(Maybe<(Hv.Tree<Hv.Owner> & List<&2, U32>)>, Hv.owners_take(Hv.page_depth(), Hv.owners_encode(ps, Hv.vcpus_encode(Hv.four(a, b, c, d), Nil{}))), Some{(ps, Hv.VCpu.encode(a, Hv.VCpu.encode(b, Hv.VCpu.encode(c, Hv.VCpu.encode(d, Nil{})))))}, owners_rt(ps, Hv.page_depth(), sp, op, Hv.VCpu.encode(a, Hv.VCpu.encode(b, Hv.VCpu.encode(c, Hv.VCpu.encode(d, Nil{})))))) : {Hv.decode_record.fin(Hv.Kernel{n, next, slice}, cur, Hv.encode(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), _) == Some{(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur})} : Maybe<(Hv.Kernel & Hv.Machine)>}
      %Equal.sym(Maybe<(Hv.VCpu & List<&2, U32>)>, Hv.vcpu_take(Hv.VCpu.encode(a, Hv.VCpu.encode(b, Hv.VCpu.encode(c, Hv.VCpu.encode(d, Nil{}))))), Some{(a, Hv.VCpu.encode(b, Hv.VCpu.encode(c, Hv.VCpu.encode(d, Nil{}))))}, vcpu_take_rt(a, Hv.VCpu.encode(b, Hv.VCpu.encode(c, Hv.VCpu.encode(d, Nil{}))))) : {Hv.decode_record.vcs(Hv.Kernel{n, next, slice}, cur, ps, Hv.encode(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), _) == Some{(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur})} : Maybe<(Hv.Kernel & Hv.Machine)>}
      %Equal.sym(Maybe<(Hv.VCpu & List<&2, U32>)>, Hv.vcpu_take(Hv.VCpu.encode(b, Hv.VCpu.encode(c, Hv.VCpu.encode(d, Nil{})))), Some{(b, Hv.VCpu.encode(c, Hv.VCpu.encode(d, Nil{})))}, vcpu_take_rt(b, Hv.VCpu.encode(c, Hv.VCpu.encode(d, Nil{})))) : {Hv.decode_record.v1(Hv.Kernel{n, next, slice}, cur, ps, Hv.encode(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), a, _) == Some{(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur})} : Maybe<(Hv.Kernel & Hv.Machine)>}
      %Equal.sym(Maybe<(Hv.VCpu & List<&2, U32>)>, Hv.vcpu_take(Hv.VCpu.encode(c, Hv.VCpu.encode(d, Nil{}))), Some{(c, Hv.VCpu.encode(d, Nil{}))}, vcpu_take_rt(c, Hv.VCpu.encode(d, Nil{}))) : {Hv.decode_record.v2(Hv.Kernel{n, next, slice}, cur, ps, Hv.encode(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), a, b, _) == Some{(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur})} : Maybe<(Hv.Kernel & Hv.Machine)>}
      %Equal.sym(Maybe<(Hv.VCpu & List<&2, U32>)>, Hv.vcpu_take(Hv.VCpu.encode(d, Nil{})), Some{(d, Nil{})}, vcpu_take_rt(d, Nil{})) : {Hv.decode_record.v3(Hv.Kernel{n, next, slice}, cur, ps, Hv.encode(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), a, b, c, _) == Some{(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur})} : Maybe<(Hv.Kernel & Hv.Machine)>}
      %Equal.sym(Bool, Hv.Owners.okb(ps), True{}, okb_of_ok(ps, op)) : {Hv.decode_record.take(Hv.Kernel{n, next, slice}, cur, ps, a, b, c, d, Bool.and(Bool.and(_, Hv.Tree.shapeb(ps, Hv.page_depth())), Bool.and(U32.is_lt(cur, 4), Hv.U32.list_eq(Hv.encode(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), Hv.encode_parts(Hv.Kernel{n, next, slice}, ps, a, b, c, d, cur))))) == Some{(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur})} : Maybe<(Hv.Kernel & Hv.Machine)>}
      %Equal.sym(Bool, Hv.Tree.shapeb(ps, Hv.page_depth()), True{}, shapeb_of_shape(ps, Hv.page_depth(), sp)) : {Hv.decode_record.take(Hv.Kernel{n, next, slice}, cur, ps, a, b, c, d, Bool.and(Bool.and(True{}, _), Bool.and(U32.is_lt(cur, 4), Hv.U32.list_eq(Hv.encode(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), Hv.encode_parts(Hv.Kernel{n, next, slice}, ps, a, b, c, d, cur))))) == Some{(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur})} : Maybe<(Hv.Kernel & Hv.Machine)>}
      %Equal.sym(Bool, U32.is_lt(cur, 4), True{}, sc) : {Hv.decode_record.take(Hv.Kernel{n, next, slice}, cur, ps, a, b, c, d, Bool.and(Bool.and(True{}, True{}), Bool.and(_, Hv.U32.list_eq(Hv.encode(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), Hv.encode_parts(Hv.Kernel{n, next, slice}, ps, a, b, c, d, cur))))) == Some{(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur})} : Maybe<(Hv.Kernel & Hv.Machine)>}
      %Equal.sym(Bool, Hv.U32.list_eq(Hv.encode(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), Hv.encode_parts(Hv.Kernel{n, next, slice}, ps, a, b, c, d, cur)), True{}, list_eq_refl(Hv.encode(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) : {Hv.decode_record.take(Hv.Kernel{n, next, slice}, cur, ps, a, b, c, d, Bool.and(Bool.and(True{}, True{}), Bool.and(True{}, _))) == Some{(Hv.Kernel{n, next, slice}, Hv.Machine{ps, Hv.four(a, b, c, d), cur})} : Maybe<(Hv.Kernel & Hv.Machine)>}
      {==}

def handle_ok.k0(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, sp: Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()), op: Hv.Owners.ok(ps)) -> Hv.Machine.ok(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 0}, e))):
  keeps_ok(ps, Hv.VCpu.step(a, e), b, c, d, Hv.Step.m(Hv.decide(k, Hv.Machine{ps, Hv.four(Hv.VCpu.step(a, e), b, c, d), 0}, e)), decide_keeps4(k, ps, Hv.VCpu.step(a, e), b, c, d, 0, e, {==}), sp, op)

def handle_ok.k1(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, sp: Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()), op: Hv.Owners.ok(ps)) -> Hv.Machine.ok(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 1}, e))):
  keeps_ok(ps, a, Hv.VCpu.step(b, e), c, d, Hv.Step.m(Hv.decide(k, Hv.Machine{ps, Hv.four(a, Hv.VCpu.step(b, e), c, d), 1}, e)), decide_keeps4(k, ps, a, Hv.VCpu.step(b, e), c, d, 1, e, {==}), sp, op)

def handle_ok.k2(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, sp: Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()), op: Hv.Owners.ok(ps)) -> Hv.Machine.ok(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 2}, e))):
  keeps_ok(ps, a, b, Hv.VCpu.step(c, e), d, Hv.Step.m(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, Hv.VCpu.step(c, e), d), 2}, e)), decide_keeps4(k, ps, a, b, Hv.VCpu.step(c, e), d, 2, e, {==}), sp, op)

def handle_ok.k3(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, sp: Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()), op: Hv.Owners.ok(ps)) -> Hv.Machine.ok(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 3}, e))):
  keeps_ok(ps, a, b, c, Hv.VCpu.step(d, e), Hv.Step.m(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, Hv.VCpu.step(d, e)), 3}, e)), decide_keeps4(k, ps, a, b, c, Hv.VCpu.step(d, e), 3, e, {==}), sp, op)

def handle_ok.c(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -cur: U32, +e: Hv.Exit, vc: L.Lt4<cur>, sp: Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()), op: Hv.Owners.ok(ps)) -> Hv.Machine.ok(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e))):
  match vc:
    case L.K0{ec}:
      %ec : Hv.Machine.ok(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)))
      handle_ok.k0(k, ps, a, b, c, d, e, sp, op)
    case L.K1{ec}:
      %ec : Hv.Machine.ok(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)))
      handle_ok.k1(k, ps, a, b, c, d, e, sp, op)
    case L.K2{ec}:
      %ec : Hv.Machine.ok(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)))
      handle_ok.k2(k, ps, a, b, c, d, e, sp, op)
    case L.K3{ec}:
      %ec : Hv.Machine.ok(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)))
      handle_ok.k3(k, ps, a, b, c, d, e, sp, op)

def handle_pages.k0(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.Machine.pages(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 0}, e))) == ps : Hv.Tree<Hv.Owner>}:
  keeps_pages(ps, Hv.VCpu.step(a, e), b, c, d, Hv.Step.m(Hv.decide(k, Hv.Machine{ps, Hv.four(Hv.VCpu.step(a, e), b, c, d), 0}, e)), decide_keeps4(k, ps, Hv.VCpu.step(a, e), b, c, d, 0, e, {==}))

def handle_pages.k1(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.Machine.pages(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 1}, e))) == ps : Hv.Tree<Hv.Owner>}:
  keeps_pages(ps, a, Hv.VCpu.step(b, e), c, d, Hv.Step.m(Hv.decide(k, Hv.Machine{ps, Hv.four(a, Hv.VCpu.step(b, e), c, d), 1}, e)), decide_keeps4(k, ps, a, Hv.VCpu.step(b, e), c, d, 1, e, {==}))

def handle_pages.k2(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.Machine.pages(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 2}, e))) == ps : Hv.Tree<Hv.Owner>}:
  keeps_pages(ps, a, b, Hv.VCpu.step(c, e), d, Hv.Step.m(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, Hv.VCpu.step(c, e), d), 2}, e)), decide_keeps4(k, ps, a, b, Hv.VCpu.step(c, e), d, 2, e, {==}))

def handle_pages.k3(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.Machine.pages(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 3}, e))) == ps : Hv.Tree<Hv.Owner>}:
  keeps_pages(ps, a, b, c, Hv.VCpu.step(d, e), Hv.Step.m(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, Hv.VCpu.step(d, e)), 3}, e)), decide_keeps4(k, ps, a, b, c, Hv.VCpu.step(d, e), 3, e, {==}))

def handle_pages.c(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -cur: U32, +e: Hv.Exit, vc: L.Lt4<cur>) -> {Hv.Machine.pages(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e))) == ps : Hv.Tree<Hv.Owner>}:
  match vc:
    case L.K0{ec}:
      %ec : {Hv.Machine.pages(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))) == ps : Hv.Tree<Hv.Owner>}
      handle_pages.k0(k, ps, a, b, c, d, e)
    case L.K1{ec}:
      %ec : {Hv.Machine.pages(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))) == ps : Hv.Tree<Hv.Owner>}
      handle_pages.k1(k, ps, a, b, c, d, e)
    case L.K2{ec}:
      %ec : {Hv.Machine.pages(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))) == ps : Hv.Tree<Hv.Owner>}
      handle_pages.k2(k, ps, a, b, c, d, e)
    case L.K3{ec}:
      %ec : {Hv.Machine.pages(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))) == ps : Hv.Tree<Hv.Owner>}
      handle_pages.k3(k, ps, a, b, c, d, e)

def handle_own.k0(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 0}, e)), 0) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), 0), e) : Hv.VCpu}:
  %Equal.sym(Array<Hv.VCpu>, Hv.Step.vcpus(Hv.decide(k, Hv.Machine{ps, Hv.four(Hv.VCpu.step(a, e), b, c, d), 0}, e)), Hv.four(Hv.VCpu.step(a, e), b, c, d), decide_vcpus4(k, ps, Hv.VCpu.step(a, e), b, c, d, 0, e)) : {Hv.vcpu_at(_, 0) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), 0), e) : Hv.VCpu}
  {==}

def handle_own.k1(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 1}, e)), 1) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), 1), e) : Hv.VCpu}:
  %Equal.sym(Array<Hv.VCpu>, Hv.Step.vcpus(Hv.decide(k, Hv.Machine{ps, Hv.four(a, Hv.VCpu.step(b, e), c, d), 1}, e)), Hv.four(a, Hv.VCpu.step(b, e), c, d), decide_vcpus4(k, ps, a, Hv.VCpu.step(b, e), c, d, 1, e)) : {Hv.vcpu_at(_, 1) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), 1), e) : Hv.VCpu}
  {==}

def handle_own.k2(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 2}, e)), 2) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), 2), e) : Hv.VCpu}:
  %Equal.sym(Array<Hv.VCpu>, Hv.Step.vcpus(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, Hv.VCpu.step(c, e), d), 2}, e)), Hv.four(a, b, Hv.VCpu.step(c, e), d), decide_vcpus4(k, ps, a, b, Hv.VCpu.step(c, e), d, 2, e)) : {Hv.vcpu_at(_, 2) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), 2), e) : Hv.VCpu}
  {==}

def handle_own.k3(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 3}, e)), 3) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), 3), e) : Hv.VCpu}:
  %Equal.sym(Array<Hv.VCpu>, Hv.Step.vcpus(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, Hv.VCpu.step(d, e)), 3}, e)), Hv.four(a, b, c, Hv.VCpu.step(d, e)), decide_vcpus4(k, ps, a, b, c, Hv.VCpu.step(d, e), 3, e)) : {Hv.vcpu_at(_, 3) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), 3), e) : Hv.VCpu}
  {==}

def handle_own.c(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -cur: U32, +e: Hv.Exit, vc: L.Lt4<cur>) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)), cur) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), cur), e) : Hv.VCpu}:
  match vc:
    case L.K0{ec}:
      %ec : {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)), _) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), _), e) : Hv.VCpu}
      handle_own.k0(k, ps, a, b, c, d, e)
    case L.K1{ec}:
      %ec : {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)), _) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), _), e) : Hv.VCpu}
      handle_own.k1(k, ps, a, b, c, d, e)
    case L.K2{ec}:
      %ec : {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)), _) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), _), e) : Hv.VCpu}
      handle_own.k2(k, ps, a, b, c, d, e)
    case L.K3{ec}:
      %ec : {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)), _) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), _), e) : Hv.VCpu}
      handle_own.k3(k, ps, a, b, c, d, e)

def handle_entry.k0(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> Entered(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 0}, e)):
  decide_entry4(k, ps, Hv.VCpu.step(a, e), b, c, d, 0, e)

def handle_entry.k1(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> Entered(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 1}, e)):
  decide_entry4(k, ps, a, Hv.VCpu.step(b, e), c, d, 1, e)

def handle_entry.k2(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> Entered(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 2}, e)):
  decide_entry4(k, ps, a, b, Hv.VCpu.step(c, e), d, 2, e)

def handle_entry.k3(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> Entered(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 3}, e)):
  decide_entry4(k, ps, a, b, c, Hv.VCpu.step(d, e), 3, e)

def handle_entry.c(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -cur: U32, +e: Hv.Exit, vc: L.Lt4<cur>) -> Entered(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)):
  match vc:
    case L.K0{ec}:
      %ec : Entered(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))
      handle_entry.k0(k, ps, a, b, c, d, e)
    case L.K1{ec}:
      %ec : Entered(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))
      handle_entry.k1(k, ps, a, b, c, d, e)
    case L.K2{ec}:
      %ec : Entered(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))
      handle_entry.k2(k, ps, a, b, c, d, e)
    case L.K3{ec}:
      %ec : Entered(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))
      handle_entry.k3(k, ps, a, b, c, d, e)

def handle_ok.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +e: Hv.Exit, sc: Hv.Slot(cur), sp: Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()), op: Hv.Owners.ok(ps), -vs: Array<Hv.VCpu>, v4: Four<vs>) -> Hv.Machine.ok(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, vs, cur}, e))):
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : Hv.Machine.ok(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, _, cur}, e)))
      handle_ok.c(k, ps, a, b, c, d, cur, e, L.lt4(cur, sc), sp, op)

def Laws.handle_ok(k, m, e, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      handle_ok.v(k, ps, cur, e, sc, sp, op, vs, four_view(vs, sv))

def handle_pages.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +e: Hv.Exit, sc: Hv.Slot(cur), -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.Machine.pages(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, vs, cur}, e))) == ps : Hv.Tree<Hv.Owner>}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.Machine.pages(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, _, cur}, e))) == ps : Hv.Tree<Hv.Owner>}
      handle_pages.c(k, ps, a, b, c, d, cur, e, L.lt4(cur, sc))

def Laws.handle_pages(k, m, e, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      handle_pages.v(k, ps, cur, e, sc, vs, four_view(vs, sv))

def handle_own.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +e: Hv.Exit, sc: Hv.Slot(cur), -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, vs, cur}, e)), cur) == Hv.VCpu.step(Hv.vcpu_at(vs, cur), e) : Hv.VCpu}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, _, cur}, e)), cur) == Hv.VCpu.step(Hv.vcpu_at(_, cur), e) : Hv.VCpu}
      handle_own.c(k, ps, a, b, c, d, cur, e, L.lt4(cur, sc))

def Laws.handle_own(k, m, e, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      handle_own.v(k, ps, cur, e, sc, vs, four_view(vs, sv))

def handle_enters_saved.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +e: Hv.Exit, sc: Hv.Slot(cur), -vs: Array<Hv.VCpu>, v4: Four<vs>) -> Entered(Hv.handle(k, Hv.Machine{ps, vs, cur}, e)):
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : Entered(Hv.handle(k, Hv.Machine{ps, _, cur}, e))
      handle_entry.c(k, ps, a, b, c, d, cur, e, L.lt4(cur, sc))

def Laws.handle_enters_saved(k, m, e, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      handle_enters_saved.v(k, ps, cur, e, sc, vs, four_view(vs, sv))

def sched_enters_saved.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, -vs: Array<Hv.VCpu>, v4: Four<vs>) -> Entered(Hv.sched(k, Hv.Machine{ps, vs, cur})):
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : Entered(Hv.sched(k, Hv.Machine{ps, _, cur}))
      sched_entry4(k, ps, a, b, c, d, cur)

def Laws.sched_enters_saved(k, m, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      sched_enters_saved.v(k, ps, cur, vs, four_view(vs, sv))

def record_roundtrip.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +sp: Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()), +op: Hv.Owners.ok(ps), +sc: Hv.Slot(cur), -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.decode_record(Hv.encode(k, Hv.Machine{ps, vs, cur})) == Some{(k, Hv.Machine{ps, vs, cur})} : Maybe<(Hv.Kernel & Hv.Machine)>}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.decode_record(Hv.encode(k, Hv.Machine{ps, _, cur})) == Some{(k, Hv.Machine{ps, _, cur})} : Maybe<(Hv.Kernel & Hv.Machine)>}
      roundtrip4(k, ps, a, b, c, d, cur, sp, op, sc)

def Laws.record_roundtrip(k, m, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, +sc}}} = ok
      record_roundtrip.v(k, ps, cur, sp, op, sc, vs, four_view(vs, sv))

# Runs
# ----
# replay folds a run's log into guest x's vCPU: only x's own exits step
# it. The run's final vCPU of x is the replay of its log (run_view.go),
# and the replay is VCpu.steps over x's own exits (replay_steps).

def Tick.own(+x: U32, t: Hv.Tick, +v: Hv.VCpu) -> Hv.VCpu:
  match t:
    case Hv.Tick{acts, g, Hv.Ex{e}}:
      Bool.pick(Hv.VCpu, U32.is_eq(x, g), Hv.VCpu.step(v, e), v)
    case Hv.Tick{acts, g, Hv.Handoff{}}:
      v

def replay(+x: U32, log: List<&2, Hv.Tick>, v: Hv.VCpu) -> Hv.VCpu:
  match log:
    case Nil{}:
      v
    case t <> rest:
      replay(x, rest, Tick.own(x, t, v))

def replay_steps.ex(+x: U32, +e: Hv.Exit, +rest: List<&2, Hv.Tick>, +v: Hv.VCpu, b: Bool,
  ht: {replay(x, rest, Hv.VCpu.step(v, e)) == Hv.VCpu.steps(Hv.own_exits(x, rest), Hv.VCpu.step(v, e)) : Hv.VCpu},
  hf: {replay(x, rest, v) == Hv.VCpu.steps(Hv.own_exits(x, rest), v) : Hv.VCpu})
  -> {replay(x, rest, Bool.pick(Hv.VCpu, b, Hv.VCpu.step(v, e), v)) == Hv.VCpu.steps(List.append(&2, Hv.Exit, Bool.pick(List<&2, Hv.Exit>, b, [e], Nil{}), Hv.own_exits(x, rest)), v) : Hv.VCpu}:
  match b:
    case False{}:
      hf
    case True{}:
      ht

def replay_steps(+x: U32, log: List<&2, Hv.Tick>, +v: Hv.VCpu) -> {replay(x, log, v) == Hv.VCpu.steps(Hv.own_exits(x, log), v) : Hv.VCpu}:
  match log:
    case Nil{}:
      {==}
    case Hv.Tick{acts, +g, Hv.Ex{+e}} <> +rest:
      replay_steps.ex(x, e, rest, v, U32.is_eq(x, g), replay_steps(x, rest, Hv.VCpu.step(v, e)), replay_steps(x, rest, v))
    case Hv.Tick{acts, g, Hv.Handoff{}} <> rest:
      replay_steps(x, rest, v)

def cons_s(t: Hv.Tick, r: Hv.Run) -> {Hv.Run.s(Hv.run.cons(t, r)) == Hv.Run.s(r) : Hv.Step}:
  match r:
    case Hv.Run{s, log, why}:
      {==}

def cons_log(t: Hv.Tick, r: Hv.Run) -> {Hv.Run.log(Hv.run.cons(t, r)) == t <> Hv.Run.log(r) : List<&2, Hv.Tick>}:
  match r:
    case Hv.Run{s, log, why}:
      {==}

def StepOk(s: Hv.Step) -> Data:
  Hv.Machine.ok(Hv.Step.m(s))

def SView(s: Hv.Step) -> Data:
  match s:
    case Hv.Go{k, Hv.Machine{ps, vs, cur}, acts}:
      Four<vs>
    case Hv.Fin{k, m, acts}:
      Unit

def sview(s: Hv.Step, ok: StepOk(s)) -> SView(s):
  match s:
    case Hv.Go{k, Hv.Machine{ps, vs, cur}, acts}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      four_view(vs, sv)
    case Hv.Fin{k, m, acts}:
      Unit{}

# a machine's well-formedness, less its vCPUs (which are four(..) by
# now). It is Data, so a step may name it as often as it needs: the
# earlier proof carried copies of it by hand, which is what an affine
# hypothesis costs when its type is a Sigma at &1 rather than Data.
def Pre(+ps: Hv.Tree<Hv.Owner>, +cur: U32) -> Data:
  Hv.Both<Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()),
    Hv.Both<Hv.Owners.ok(ps), Hv.Slot(cur)>>

def event_ok4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, ev: Hv.Ev, +pre: Pre(ps, cur)) -> StepOk(Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev)):
  match ev:
    case Hv.Ex{+e}:
      Hv.Both{+sp, Hv.Both{+op, +sc}} = pre
      handle_ok.c(k, ps, a, b, c, d, cur, e, L.lt4(cur, sc), sp, op)
    case Hv.Handoff{}:
      Hv.Both{+sp, Hv.Both{+op, +sc}} = pre
      %Equal.sym(Maybe<(Hv.Kernel & Hv.Machine)>, Hv.decode_record(Hv.encode(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), Some{(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})}, roundtrip4(k, ps, a, b, c, d, cur, sp, op, sc)) : StepOk(Hv.handoff.fin(k, _))
      keeps_ok(ps, a, b, c, d, Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), sched_keeps4(k, ps, a, b, c, d, cur, sc), sp, op)

def event_view4.ex(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, +e: Hv.Exit, +x: U32, sx: Hv.Slot(x), sc: Hv.Slot(cur), bx: Bool, eb: {U32.is_eq(x, cur) == bx : Bool})
  -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)), x) == Bool.pick(Hv.VCpu, bx, Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), x), e), Hv.vcpu_at(Hv.four(a, b, c, d), x)) : Hv.VCpu}:
  match bx:
    case True{}:
      %Equal.sym(U32, x, cur, L.u32_eq(x, cur, eb)) : {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)), _) == Hv.VCpu.step(Hv.vcpu_at(Hv.four(a, b, c, d), _), e) : Hv.VCpu}
      handle_own.c(k, ps, a, b, c, d, cur, e, L.lt4(cur, sc))
    case False{}:
      frame.c(k, ps, a, b, c, d, cur, e, x, L.lt4(cur, sc), sx, (%Equal.sym(Bool, U32.is_eq(x, cur), False{}, eb) : {Bool.not(_) == True{} : Bool}; {==}))

def event_view4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, ev: Hv.Ev, -acts: List<&2, Hv.Action>, +x: U32, sx: Hv.Slot(x), +pre: Pre(ps, cur))
  -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev)), x) == Tick.own(x, Hv.Tick{acts, cur, ev}, Hv.vcpu_at(Hv.four(a, b, c, d), x)) : Hv.VCpu}:
  match ev:
    case Hv.Ex{+e}:
      Hv.Both{+sp, Hv.Both{+op, +sc}} = pre
      event_view4.ex(k, ps, a, b, c, d, cur, e, x, sx, sc, U32.is_eq(x, cur), {==})
    case Hv.Handoff{}:
      Hv.Both{+sp, Hv.Both{+op, +sc}} = pre
      %Equal.sym(Maybe<(Hv.Kernel & Hv.Machine)>, Hv.decode_record(Hv.encode(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), Some{(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})}, roundtrip4(k, ps, a, b, c, d, cur, sp, op, sc)) : {Hv.vcpu_at(Hv.Step.vcpus(Hv.handoff.fin(k, _)), x) == Hv.vcpu_at(Hv.four(a, b, c, d), x) : Hv.VCpu}
      Equal.cong(Array<Hv.VCpu>, Hv.VCpu, w => Hv.vcpu_at(w, x), Hv.Step.vcpus(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), Hv.four(a, b, c, d), sched_vcpus4(k, ps, a, b, c, d, cur))

def run_view.go(+fuel: Nat, s: Hv.Step, +tr: List<&2, Hv.Ev>, +x: U32, +sx: {U32.is_lt(x, 4) == True{} : Bool}, v: SView(s), +ok: StepOk(s))
  -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(fuel, s, tr))), x) == replay(x, Hv.Run.log(Hv.run(fuel, s, tr)), Hv.vcpu_at(Hv.Step.vcpus(s), x)) : Hv.VCpu}:
  match fuel s tr:
    case _ Hv.Fin{k, m, acts} _:
      {==}
    case 0n Hv.Go{k, m, acts} _:
      {==}
    case 1n+f Hv.Go{k, m, acts} Nil{}:
      {==}
    case 1n+f Hv.Go{+k, Hv.Machine{+ps, vs, +cur}, +acts} +ev <> +rest:
      match v:
        case IsFour{+a, +b, +c, +d, ev4}:
          Hv.Both{+sp, Hv.Both{+op, Hv.Both{sv, +sc}}} = ok
          %ev4 : {Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(1n+f, Hv.Go{k, Hv.Machine{ps, _, cur}, acts}, ev <> rest))), x) == replay(x, Hv.Run.log(Hv.run(1n+f, Hv.Go{k, Hv.Machine{ps, _, cur}, acts}, ev <> rest)), Hv.vcpu_at(Hv.Step.vcpus(Hv.Go{k, Hv.Machine{ps, _, cur}, acts}), x)) : Hv.VCpu}
          %Equal.sym(Hv.Step, Hv.Run.s(Hv.run.cons(Hv.Tick{acts, cur, ev}, Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest))), Hv.Run.s(Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest)), cons_s(Hv.Tick{acts, cur, ev}, Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest))) : {Hv.vcpu_at(Hv.Step.vcpus(_), x) == replay(x, Hv.Run.log(Hv.run.cons(Hv.Tick{acts, cur, ev}, Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest))), Hv.vcpu_at(Hv.four(a, b, c, d), x)) : Hv.VCpu}
          %Equal.sym(List<&2, Hv.Tick>, Hv.Run.log(Hv.run.cons(Hv.Tick{acts, cur, ev}, Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest))), Hv.Tick{acts, cur, ev} <> Hv.Run.log(Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest)), cons_log(Hv.Tick{acts, cur, ev}, Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest))) : {Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest))), x) == replay(x, _, Hv.vcpu_at(Hv.four(a, b, c, d), x)) : Hv.VCpu}
          Equal.trans(Hv.VCpu,
            Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest))), x),
            replay(x, Hv.Run.log(Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest)), Hv.vcpu_at(Hv.Step.vcpus(Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev)), x)),
            replay(x, Hv.Run.log(Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest)), Tick.own(x, Hv.Tick{acts, cur, ev}, Hv.vcpu_at(Hv.four(a, b, c, d), x))),
            run_view.go(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest, x, sx,
              sview(Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev),
                event_ok4(k, ps, a, b, c, d, cur, ev, Hv.Both{sp, Hv.Both{op, sc}})),
              event_ok4(k, ps, a, b, c, d, cur, ev, Hv.Both{sp, Hv.Both{op, sc}})),
            Equal.cong(Hv.VCpu, Hv.VCpu, w => replay(x, Hv.Run.log(Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest)), w),
              Hv.vcpu_at(Hv.Step.vcpus(Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev)), x),
              Tick.own(x, Hv.Tick{acts, cur, ev}, Hv.vcpu_at(Hv.four(a, b, c, d), x)),
              event_view4(k, ps, a, b, c, d, cur, ev, acts, x, sx, Hv.Both{sp, Hv.Both{op, sc}})))

def run_view.fin(+fuel: Nat, +k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, +tr: List<&2, Hv.Ev>, +x: U32, sx: Hv.Slot(x), +q: Pre(ps, cur))
  -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr))), x)
    == Hv.VCpu.steps(Hv.own_exits(x, Hv.Run.log(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr))), Hv.vcpu_at(Hv.four(a, b, c, d), x)) : Hv.VCpu}:
  Hv.Both{+sp1, Hv.Both{+op1, +sc1}} = q
  Equal.trans(Hv.VCpu,
    Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr))), x),
    replay(x, Hv.Run.log(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr)), Hv.vcpu_at(Hv.four(a, b, c, d), x)),
    Hv.VCpu.steps(Hv.own_exits(x, Hv.Run.log(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr))), Hv.vcpu_at(Hv.four(a, b, c, d), x)),
    Equal.trans(Hv.VCpu,
      Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr))), x),
      replay(x, Hv.Run.log(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr)), Hv.vcpu_at(Hv.Step.vcpus(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), x)),
      replay(x, Hv.Run.log(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr)), Hv.vcpu_at(Hv.four(a, b, c, d), x)),
      run_view.go(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr, x, sx,
          sview(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), keeps_ok(ps, a, b, c, d, Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), sched_keeps4(k, ps, a, b, c, d, cur, sc1), sp1, op1)),
          keeps_ok(ps, a, b, c, d, Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), sched_keeps4(k, ps, a, b, c, d, cur, sc1), sp1, op1)),
      Equal.cong(Array<Hv.VCpu>, Hv.VCpu, w => replay(x, Hv.Run.log(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr)), Hv.vcpu_at(w, x)),
        Hv.Step.vcpus(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), Hv.four(a, b, c, d), sched_vcpus4(k, ps, a, b, c, d, cur))),
    replay_steps(x, Hv.Run.log(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr)), Hv.vcpu_at(Hv.four(a, b, c, d), x)))

def run_view.v(+fuel: Nat, +k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +tr: List<&2, Hv.Ev>, +x: U32, sx: Hv.Slot(x), sp: Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()), op: Hv.Owners.ok(ps), sc: Hv.Slot(cur), -vs: Array<Hv.VCpu>, v4: Four<vs>)
  -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, vs, cur}), tr))), x)
    == Hv.VCpu.steps(Hv.own_exits(x, Hv.Run.log(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, vs, cur}), tr))), Hv.vcpu_at(vs, x)) : Hv.VCpu}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, _, cur}), tr))), x) == Hv.VCpu.steps(Hv.own_exits(x, Hv.Run.log(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, _, cur}), tr))), Hv.vcpu_at(_, x)) : Hv.VCpu}
      run_view.fin(fuel, k, ps, a, b, c, d, cur, tr, x, sx, Hv.Both{sp, Hv.Both{op, sc}})

def Laws.run_view(fuel, k, m, ok, tr, x, sx):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      run_view.v(fuel, k, ps, cur, tr, x, sx, sp, op, sc, vs, four_view(vs, sv))

def Laws.noninterference(f1, k1, m1, ok1, t1, f2, k2, m2, ok2, t2, x, sx, same, own):
  Equal.trans(Hv.VCpu,
    Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(f1, Hv.sched(k1, m1), t1))), x),
    Hv.VCpu.steps(Hv.own_exits(x, Hv.Run.log(Hv.run(f1, Hv.sched(k1, m1), t1))), Hv.vcpu_at(Hv.Machine.vcpus(m1), x)),
    Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(f2, Hv.sched(k2, m2), t2))), x),
    Laws.run_view(f1, k1, m1, ok1, t1, x, sx),
    (%Equal.sym(List<&2, Hv.Exit>, Hv.own_exits(x, Hv.Run.log(Hv.run(f1, Hv.sched(k1, m1), t1))), Hv.own_exits(x, Hv.Run.log(Hv.run(f2, Hv.sched(k2, m2), t2))), own) : {Hv.VCpu.steps(_, Hv.vcpu_at(Hv.Machine.vcpus(m1), x)) == Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(f2, Hv.sched(k2, m2), t2))), x) : Hv.VCpu};
     %Equal.sym(Hv.VCpu, Hv.vcpu_at(Hv.Machine.vcpus(m1), x), Hv.vcpu_at(Hv.Machine.vcpus(m2), x), same) : {Hv.VCpu.steps(Hv.own_exits(x, Hv.Run.log(Hv.run(f2, Hv.sched(k2, m2), t2))), _) == Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(f2, Hv.sched(k2, m2), t2))), x) : Hv.VCpu};
     Equal.sym(Hv.VCpu, Hv.vcpu_at(Hv.Step.vcpus(Hv.Run.s(Hv.run(f2, Hv.sched(k2, m2), t2))), x), Hv.VCpu.steps(Hv.own_exits(x, Hv.Run.log(Hv.run(f2, Hv.sched(k2, m2), t2))), Hv.vcpu_at(Hv.Machine.vcpus(m2), x)), Laws.run_view(f2, k2, m2, ok2, t2, x, sx))))

# Partition, budget, and the action list
# --------------------------------------
# the laws above the hardware axiom: what sched, handle, handoff and run keep, stated so a reader can see it without opening the decision lemmas

def Laws.mask_skips_host(ps, g):
  match ps:
    case Hv.Leaf{o}:
      match o:
        case Hv.Free{}:
          {==}
        case Hv.Hyp{}:
          {==}
        case Hv.Of{h}:
          {==}
    case Hv.Node{lo, hi}:
      %Equal.sym(Bool, Hv.mask_skips(lo, g), True{}, Laws.mask_skips_host(lo, g)) : {Bool.and(_, Hv.mask_skips(hi, g)) == True{} : Bool}
      %Equal.sym(Bool, Hv.mask_skips(hi, g), True{}, Laws.mask_skips_host(hi, g)) : {Bool.and(True{}, _) == True{} : Bool}
      {==}

def sched_pages4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, sc: Hv.Slot(cur)) -> {Hv.Machine.pages(Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) == ps : Hv.Tree<Hv.Owner>}:
  keeps_pages(ps, a, b, c, d, Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), sched_keeps4(k, ps, a, b, c, d, cur, sc))

def sched_pages.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, sc: Hv.Slot(cur), -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.Machine.pages(Hv.Step.m(Hv.sched(k, Hv.Machine{ps, vs, cur}))) == ps : Hv.Tree<Hv.Owner>}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.Machine.pages(Hv.Step.m(Hv.sched(k, Hv.Machine{ps, _, cur}))) == ps : Hv.Tree<Hv.Owner>}
      sched_pages4(k, ps, a, b, c, d, cur, sc)

def Laws.sched_pages(k, m, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      sched_pages.v(k, ps, cur, sc, vs, four_view(vs, sv))

def sched_frame4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, +g: U32) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), g) == Hv.vcpu_at(Hv.four(a, b, c, d), g) : Hv.VCpu}:
  Equal.cong(Array<Hv.VCpu>, Hv.VCpu, w => Hv.vcpu_at(w, g), Hv.Step.vcpus(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), Hv.four(a, b, c, d), sched_vcpus4(k, ps, a, b, c, d, cur))

def sched_frame.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +g: U32, -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.vcpu_at(Hv.Step.vcpus(Hv.sched(k, Hv.Machine{ps, vs, cur})), g) == Hv.vcpu_at(vs, g) : Hv.VCpu}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.vcpu_at(Hv.Step.vcpus(Hv.sched(k, Hv.Machine{ps, _, cur})), g) == Hv.vcpu_at(_, g) : Hv.VCpu}
      sched_frame4(k, ps, a, b, c, d, cur, g)

def Laws.sched_frame(k, m, ok, g, sg):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      sched_frame.v(k, ps, cur, g, vs, four_view(vs, sv))

def handoff_pages4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, sp: Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()), op: Hv.Owners.ok(ps), +sc: Hv.Slot(cur)) -> {Hv.Machine.pages(Hv.Step.m(Hv.handoff(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) == ps : Hv.Tree<Hv.Owner>}:
  %Equal.sym(Maybe<(Hv.Kernel & Hv.Machine)>, Hv.decode_record(Hv.encode(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), Some{(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})}, roundtrip4(k, ps, a, b, c, d, cur, sp, op, sc)) : {Hv.Machine.pages(Hv.Step.m(Hv.handoff.fin(k, _))) == ps : Hv.Tree<Hv.Owner>}
  keeps_pages(ps, a, b, c, d, Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), sched_keeps4(k, ps, a, b, c, d, cur, sc))

def handoff_pages.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, sp: Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()), op: Hv.Owners.ok(ps), sc: Hv.Slot(cur), -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.Machine.pages(Hv.Step.m(Hv.handoff(k, Hv.Machine{ps, vs, cur}))) == ps : Hv.Tree<Hv.Owner>}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.Machine.pages(Hv.Step.m(Hv.handoff(k, Hv.Machine{ps, _, cur}))) == ps : Hv.Tree<Hv.Owner>}
      handoff_pages4(k, ps, a, b, c, d, cur, sp, op, sc)

def Laws.handoff_pages(k, m, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      handoff_pages.v(k, ps, cur, sp, op, sc, vs, four_view(vs, sv))

def event_pages4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, ev: Hv.Ev, +pre: Pre(ps, cur)) -> {Hv.Machine.pages(Hv.Step.m(Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev))) == ps : Hv.Tree<Hv.Owner>}:
  match ev:
    case Hv.Ex{+e}:
      Hv.Both{+sp, Hv.Both{+op, +sc}} = pre
      handle_pages.c(k, ps, a, b, c, d, cur, e, L.lt4(cur, sc))
    case Hv.Handoff{}:
      Hv.Both{+sp, Hv.Both{+op, +sc}} = pre
      handoff_pages4(k, ps, a, b, c, d, cur, sp, op, sc)

def run_pages.go(+fuel: Nat, s: Hv.Step, +tr: List<&2, Hv.Ev>, v: SView(s), +ok: StepOk(s)) -> {Hv.Machine.pages(Hv.Step.m(Hv.Run.s(Hv.run(fuel, s, tr)))) == Hv.Machine.pages(Hv.Step.m(s)) : Hv.Tree<Hv.Owner>}:
  match fuel s tr:
    case _ Hv.Fin{k, m, acts} _:
      {==}
    case 0n Hv.Go{k, m, acts} _:
      {==}
    case 1n+f Hv.Go{k, m, acts} Nil{}:
      {==}
    case 1n+f Hv.Go{+k, Hv.Machine{+ps, vs, +cur}, +acts} +ev <> +rest:
      match v:
        case IsFour{+a, +b, +c, +d, ev4}:
          Hv.Both{+sp, Hv.Both{+op, Hv.Both{sv, +sc}}} = ok
          %ev4 : {Hv.Machine.pages(Hv.Step.m(Hv.Run.s(Hv.run(1n+f, Hv.Go{k, Hv.Machine{ps, _, cur}, acts}, ev <> rest)))) == ps : Hv.Tree<Hv.Owner>}
          %Equal.sym(Hv.Step, Hv.Run.s(Hv.run.cons(Hv.Tick{acts, cur, ev}, Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest))), Hv.Run.s(Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest)), cons_s(Hv.Tick{acts, cur, ev}, Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest))) : {Hv.Machine.pages(Hv.Step.m(_)) == ps : Hv.Tree<Hv.Owner>}
          Equal.trans(Hv.Tree<Hv.Owner>,
            Hv.Machine.pages(Hv.Step.m(Hv.Run.s(Hv.run(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest)))),
            Hv.Machine.pages(Hv.Step.m(Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev))),
            ps,
            run_pages.go(f, Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), rest,
              sview(Hv.event(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, ev), event_ok4(k, ps, a, b, c, d, cur, ev, Hv.Both{sp, Hv.Both{op, sc}})),
              event_ok4(k, ps, a, b, c, d, cur, ev, Hv.Both{sp, Hv.Both{op, sc}})),
            event_pages4(k, ps, a, b, c, d, cur, ev, Hv.Both{sp, Hv.Both{op, sc}}))

def run_pages.fin(+fuel: Nat, +k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, +tr: List<&2, Hv.Ev>, +pre: Pre(ps, cur)) -> {Hv.Machine.pages(Hv.Step.m(Hv.Run.s(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr)))) == ps : Hv.Tree<Hv.Owner>}:
  Hv.Both{+sp, Hv.Both{+op, +sc}} = pre
  Equal.trans(Hv.Tree<Hv.Owner>,
    Hv.Machine.pages(Hv.Step.m(Hv.Run.s(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr)))),
    Hv.Machine.pages(Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))),
    ps,
    run_pages.go(fuel, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), tr,
      sview(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), keeps_ok(ps, a, b, c, d, Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), sched_keeps4(k, ps, a, b, c, d, cur, sc), sp, op)),
      keeps_ok(ps, a, b, c, d, Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), sched_keeps4(k, ps, a, b, c, d, cur, sc), sp, op)),
    sched_pages4(k, ps, a, b, c, d, cur, sc))

def run_pages.v(+fuel: Nat, +k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +tr: List<&2, Hv.Ev>, sp: Hv.Tree.shape(Hv.Owner, ps, Hv.page_depth()), op: Hv.Owners.ok(ps), sc: Hv.Slot(cur), -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.Machine.pages(Hv.Step.m(Hv.Run.s(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, vs, cur}), tr)))) == ps : Hv.Tree<Hv.Owner>}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.Machine.pages(Hv.Step.m(Hv.Run.s(Hv.run(fuel, Hv.sched(k, Hv.Machine{ps, _, cur}), tr)))) == ps : Hv.Tree<Hv.Owner>}
      run_pages.fin(fuel, k, ps, a, b, c, d, cur, tr, Hv.Both{sp, Hv.Both{op, sc}})

def Laws.run_pages(fuel, k, m, ok, tr):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      run_pages.v(fuel, k, ps, cur, tr, sp, op, sc, vs, four_view(vs, sv))

def sched_at_budget(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, pick: Maybe<&2, U32>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu) -> {Hv.Step.budget(Hv.sched.at(k, ps, cur, pick, Hv.four(a, b, c, d))) == Hv.Kernel.budget(k) : U32 & U32}:
  match k pick:
    case Hv.Kernel{+n, +next, +slice} None{}:
      {==}
    case Hv.Kernel{+n, +next, +slice} Some{+g}:
      %get_eta4.sym(a, b, c, d, g) : {Hv.Step.budget(Hv.sched.go(Hv.Kernel{n, next, slice}, ps, g, _)) == (n, slice) : U32 & U32}
      {==}

def sched_budget4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> {Hv.Step.budget(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) == Hv.Kernel.budget(k) : U32 & U32}:
  match k:
    case Hv.Kernel{+n, +next, +slice}:
      %first_live_eta4.sym(Hv.rotation(next), a, b, c, d) : {Hv.Step.budget(Hv.sched.fin(Hv.Kernel{n, next, slice}, ps, cur, _)) == (n, slice) : U32 & U32}
      sched_at_budget(Hv.Kernel{n, next, slice}, ps, cur, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(Hv.rotation(next), Hv.four(a, b, c, d))), a, b, c, d)

def sched_budget.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.Step.budget(Hv.sched(k, Hv.Machine{ps, vs, cur})) == Hv.Kernel.budget(k) : U32 & U32}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.Step.budget(Hv.sched(k, Hv.Machine{ps, _, cur})) == Hv.Kernel.budget(k) : U32 & U32}
      sched_budget4(k, ps, a, b, c, d, cur)

def Laws.sched_budget(k, m, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      sched_budget.v(k, ps, cur, vs, four_view(vs, sv))

def prepend_budget(x: Hv.Action, s: Hv.Step) -> {Hv.Step.budget(Hv.prepend(x, s)) == Hv.Step.budget(s) : U32 & U32}:
  match s:
    case Hv.Go{k, m, acts}:
      {==}
    case Hv.Fin{k, m, acts}:
      {==}

def resume_budget4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> {Hv.Step.budget(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) == Hv.Kernel.budget(k) : U32 & U32}:
  %get_eta4.sym(a, b, c, d, cur) : {Hv.Step.budget(Hv.resume.fin(k, ps, cur, _)) == Hv.Kernel.budget(k) : U32 & U32}
  {==}

def halt_budget4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> {Hv.Step.budget(Hv.halt(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) == Hv.Kernel.budget(k) : U32 & U32}:
  Equal.trans(U32 & U32, Hv.Step.budget(Hv.prepend(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Step.budget(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), Hv.Kernel.budget(k),
    prepend_budget(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})),
    sched_budget4(k, ps, a, b, c, d, cur))

def hvc_budget4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, call: Hv.Call, +r: Hv.Regs) -> {Hv.Step.budget(Hv.hvc(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, call, r)) == Hv.Kernel.budget(k) : U32 & U32}:
  match call:
    case Hv.Yield{}:
      sched_budget4(k, ps, a, b, c, d, cur)
    case Hv.Put{}:
      Equal.trans(U32 & U32, Hv.Step.budget(Hv.prepend(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Step.budget(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), Hv.Kernel.budget(k),
        prepend_budget(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})),
        resume_budget4(k, ps, a, b, c, d, cur))
    case Hv.Quit{}:
      halt_budget4(k, ps, a, b, c, d, cur)
    case Hv.Bad{}:
      resume_budget4(k, ps, a, b, c, d, cur)

def decide_budget4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, e: Hv.Exit) -> {Hv.Step.budget(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)) == Hv.Kernel.budget(k) : U32 & U32}:
  match e:
    case Hv.Timer{r}:
      sched_budget4(k, ps, a, b, c, d, cur)
    case Hv.Wfi{r}:
      sched_budget4(k, ps, a, b, c, d, cur)
    case Hv.Hvc{+imm, +r}:
      hvc_budget4(k, ps, a, b, c, d, cur, Hv.decode(imm), r)
    case Hv.DataAbort{ipa, w, r}:
      halt_budget4(k, ps, a, b, c, d, cur)
    case Hv.InstAbort{ipa, r}:
      halt_budget4(k, ps, a, b, c, d, cur)
    case Hv.Fault{esr, r}:
      halt_budget4(k, ps, a, b, c, d, cur)

def handle_budget.k0(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.Step.budget(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 0}, e)) == Hv.Kernel.budget(k) : U32 & U32}:
  decide_budget4(k, ps, Hv.VCpu.step(a, e), b, c, d, 0, e)

def handle_budget.k1(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.Step.budget(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 1}, e)) == Hv.Kernel.budget(k) : U32 & U32}:
  decide_budget4(k, ps, a, Hv.VCpu.step(b, e), c, d, 1, e)

def handle_budget.k2(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.Step.budget(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 2}, e)) == Hv.Kernel.budget(k) : U32 & U32}:
  decide_budget4(k, ps, a, b, Hv.VCpu.step(c, e), d, 2, e)

def handle_budget.k3(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.Step.budget(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 3}, e)) == Hv.Kernel.budget(k) : U32 & U32}:
  decide_budget4(k, ps, a, b, c, Hv.VCpu.step(d, e), 3, e)

def handle_budget.c(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -cur: U32, +e: Hv.Exit, vc: L.Lt4<cur>) -> {Hv.Step.budget(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)) == Hv.Kernel.budget(k) : U32 & U32}:
  match vc:
    case L.K0{ec}:
      %ec : {Hv.Step.budget(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)) == Hv.Kernel.budget(k) : U32 & U32}
      handle_budget.k0(k, ps, a, b, c, d, e)
    case L.K1{ec}:
      %ec : {Hv.Step.budget(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)) == Hv.Kernel.budget(k) : U32 & U32}
      handle_budget.k1(k, ps, a, b, c, d, e)
    case L.K2{ec}:
      %ec : {Hv.Step.budget(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)) == Hv.Kernel.budget(k) : U32 & U32}
      handle_budget.k2(k, ps, a, b, c, d, e)
    case L.K3{ec}:
      %ec : {Hv.Step.budget(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)) == Hv.Kernel.budget(k) : U32 & U32}
      handle_budget.k3(k, ps, a, b, c, d, e)

def handle_budget.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +e: Hv.Exit, sc: Hv.Slot(cur), -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.Step.budget(Hv.handle(k, Hv.Machine{ps, vs, cur}, e)) == Hv.Kernel.budget(k) : U32 & U32}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.Step.budget(Hv.handle(k, Hv.Machine{ps, _, cur}, e)) == Hv.Kernel.budget(k) : U32 & U32}
      handle_budget.c(k, ps, a, b, c, d, cur, e, L.lt4(cur, sc))

def Laws.handle_budget(k, m, e, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      handle_budget.v(k, ps, cur, e, sc, vs, four_view(vs, sv))

# a pick is live when it names a guest
def Live(+a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, p: Maybe<&2, U32>) -> Type:
  match p:
    case None{}:
      Unit
    case Some{+h}:
      {Hv.VCpu.live(Hv.vcpu_at(Hv.four(a, b, c, d), h)) == True{} : Bool}

def pick_live(+g: U32, +rest: Maybe<&2, U32>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +live: Bool, el: {Hv.VCpu.live(Hv.vcpu_at(Hv.four(a, b, c, d), g)) == live : Bool}, sr: Live(a, b, c, d, rest)) -> Live(a, b, c, d, Bool.pick(Maybe<&2, U32>, live, Some{g}, rest)):
  match live:
    case True{}:
      el
    case False{}:
      sr

def first_live_live(order: List<&2, U32>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, al: AllSlots(order)) -> Live(a, b, c, d, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(order, Hv.four(a, b, c, d)))):
  match order:
    case Nil{}:
      Unit{}
    case +g <> +t:
      Hv.Both{sg, st} = al
      %first_live_eta4.sym(t, a, b, c, d) : Live(a, b, c, d, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live.fin(g, _)))
      %get_eta4.sym(a, b, c, d, g) : Live(a, b, c, d, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live.pick(g, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(t, Hv.four(a, b, c, d))), _)))
      pick_live(g, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(t, Hv.four(a, b, c, d))), a, b, c, d, Hv.VCpu.live(Hv.vcpu_at(Hv.four(a, b, c, d), g)), {==}, first_live_live(t, a, b, c, d, st))

def sched_at_live(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, pick: Maybe<&2, U32>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, lp: Live(a, b, c, d, pick)) -> {Hv.on_core_live(Hv.sched.at(k, ps, cur, pick, Hv.four(a, b, c, d))) == True{} : Bool}:
  match k pick:
    case kk None{}:
      {==}
    case Hv.Kernel{+n, +next, +slice} Some{+g}:
      %get_eta4.sym(a, b, c, d, g) : {Hv.on_core_live(Hv.sched.go(Hv.Kernel{n, next, slice}, ps, g, _)) == True{} : Bool}
      lp

def sched_live4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> {Hv.on_core_live(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) == True{} : Bool}:
  match k:
    case Hv.Kernel{+n, +next, +slice}:
      %first_live_eta4.sym(Hv.rotation(next), a, b, c, d) : {Hv.on_core_live(Hv.sched.fin(Hv.Kernel{n, next, slice}, ps, cur, _)) == True{} : Bool}
      sched_at_live(Hv.Kernel{n, next, slice}, ps, cur, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(Hv.rotation(next), Hv.four(a, b, c, d))), a, b, c, d, first_live_live(Hv.rotation(next), a, b, c, d, rot_slots(next)))

def sched_enters_live.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.on_core_live(Hv.sched(k, Hv.Machine{ps, vs, cur})) == True{} : Bool}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.on_core_live(Hv.sched(k, Hv.Machine{ps, _, cur})) == True{} : Bool}
      sched_live4(k, ps, a, b, c, d, cur)

def Laws.sched_enters_live(k, m, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      sched_enters_live.v(k, ps, cur, vs, four_view(vs, sv))

def sched_at_closed(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, pick: Maybe<&2, U32>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu) -> {Hv.Step.closed(Hv.sched.at(k, ps, cur, pick, Hv.four(a, b, c, d))) == True{} : Bool}:
  match k pick:
    case kk None{}:
      {==}
    case Hv.Kernel{+n, +next, +slice} Some{+g}:
      %get_eta4.sym(a, b, c, d, g) : {Hv.Step.closed(Hv.sched.go(Hv.Kernel{n, next, slice}, ps, g, _)) == True{} : Bool}
      {==}

def sched_closed4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> {Hv.Step.closed(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) == True{} : Bool}:
  match k:
    case Hv.Kernel{+n, +next, +slice}:
      %first_live_eta4.sym(Hv.rotation(next), a, b, c, d) : {Hv.Step.closed(Hv.sched.fin(Hv.Kernel{n, next, slice}, ps, cur, _)) == True{} : Bool}
      sched_at_closed(Hv.Kernel{n, next, slice}, ps, cur, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(Hv.rotation(next), Hv.four(a, b, c, d))), a, b, c, d)

def sched_closed.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.Step.closed(Hv.sched(k, Hv.Machine{ps, vs, cur})) == True{} : Bool}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.Step.closed(Hv.sched(k, Hv.Machine{ps, _, cur})) == True{} : Bool}
      sched_closed4(k, ps, a, b, c, d, cur)

def Laws.sched_closed(k, m, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      sched_closed.v(k, ps, cur, vs, four_view(vs, sv))

def prepend_stop_closed(+g: U32, s: Hv.Step, c: {Hv.Step.closed(s) == True{} : Bool}) -> {Hv.Step.closed(Hv.prepend(Hv.Stop{g}, s)) == True{} : Bool}:
  match s:
    case Hv.Go{k, m, acts}:
      c
    case Hv.Fin{k, m, acts}:
      c

def prepend_print_closed(t: String, s: Hv.Step, c: {Hv.Step.closed(s) == True{} : Bool}) -> {Hv.Step.closed(Hv.prepend(Hv.Print{t}, s)) == True{} : Bool}:
  match s:
    case Hv.Go{k, m, acts}:
      c
    case Hv.Fin{k, m, acts}:
      c

def resume_closed4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> {Hv.Step.closed(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) == True{} : Bool}:
  %get_eta4.sym(a, b, c, d, cur) : {Hv.Step.closed(Hv.resume.fin(k, ps, cur, _)) == True{} : Bool}
  {==}

def halt_closed4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> {Hv.Step.closed(Hv.halt(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) == True{} : Bool}:
  prepend_stop_closed(cur, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), sched_closed4(k, ps, a, b, c, d, cur))

def hvc_closed4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, call: Hv.Call, +r: Hv.Regs) -> {Hv.Step.closed(Hv.hvc(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, call, r)) == True{} : Bool}:
  match call:
    case Hv.Yield{}:
      sched_closed4(k, ps, a, b, c, d, cur)
    case Hv.Put{}:
      prepend_print_closed(Hv.char_of(Hv.Regs.x0(r)), Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), resume_closed4(k, ps, a, b, c, d, cur))
    case Hv.Quit{}:
      halt_closed4(k, ps, a, b, c, d, cur)
    case Hv.Bad{}:
      resume_closed4(k, ps, a, b, c, d, cur)

def decide_closed4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, e: Hv.Exit) -> {Hv.Step.closed(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)) == True{} : Bool}:
  match e:
    case Hv.Timer{r}:
      sched_closed4(k, ps, a, b, c, d, cur)
    case Hv.Wfi{r}:
      sched_closed4(k, ps, a, b, c, d, cur)
    case Hv.Hvc{+imm, +r}:
      hvc_closed4(k, ps, a, b, c, d, cur, Hv.decode(imm), r)
    case Hv.DataAbort{ipa, w, r}:
      halt_closed4(k, ps, a, b, c, d, cur)
    case Hv.InstAbort{ipa, r}:
      halt_closed4(k, ps, a, b, c, d, cur)
    case Hv.Fault{esr, r}:
      halt_closed4(k, ps, a, b, c, d, cur)

def handle_closed.k0(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.Step.closed(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 0}, e)) == True{} : Bool}:
  decide_closed4(k, ps, Hv.VCpu.step(a, e), b, c, d, 0, e)

def handle_closed.k1(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.Step.closed(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 1}, e)) == True{} : Bool}:
  decide_closed4(k, ps, a, Hv.VCpu.step(b, e), c, d, 1, e)

def handle_closed.k2(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.Step.closed(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 2}, e)) == True{} : Bool}:
  decide_closed4(k, ps, a, b, Hv.VCpu.step(c, e), d, 2, e)

def handle_closed.k3(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.Step.closed(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 3}, e)) == True{} : Bool}:
  decide_closed4(k, ps, a, b, c, Hv.VCpu.step(d, e), 3, e)

def handle_closed.c(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -cur: U32, +e: Hv.Exit, vc: L.Lt4<cur>) -> {Hv.Step.closed(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)) == True{} : Bool}:
  match vc:
    case L.K0{ec}:
      %ec : {Hv.Step.closed(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)) == True{} : Bool}
      handle_closed.k0(k, ps, a, b, c, d, e)
    case L.K1{ec}:
      %ec : {Hv.Step.closed(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)) == True{} : Bool}
      handle_closed.k1(k, ps, a, b, c, d, e)
    case L.K2{ec}:
      %ec : {Hv.Step.closed(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)) == True{} : Bool}
      handle_closed.k2(k, ps, a, b, c, d, e)
    case L.K3{ec}:
      %ec : {Hv.Step.closed(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)) == True{} : Bool}
      handle_closed.k3(k, ps, a, b, c, d, e)

def handle_closed.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +e: Hv.Exit, sc: Hv.Slot(cur), -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.Step.closed(Hv.handle(k, Hv.Machine{ps, vs, cur}, e)) == True{} : Bool}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.Step.closed(Hv.handle(k, Hv.Machine{ps, _, cur}, e)) == True{} : Bool}
      handle_closed.c(k, ps, a, b, c, d, cur, e, L.lt4(cur, sc))

def Laws.handle_closed(k, m, e, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      handle_closed.v(k, ps, cur, e, sc, vs, four_view(vs, sv))

# a list that opens with Commit of g commits g
def commits_head(+g: U32, +rest: List<&2, Hv.Action>) -> {Hv.acts_commits(g, Hv.Commit{g} <> rest) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(g, g), True{}, L.u32_refl(g)) : {Bool.or(_, Hv.acts_commits(g, rest)) == True{} : Bool}
  {==}

def same_cur_absurd(+cur: U32, ne: {U32.is_ne(cur, cur) == True{} : Bool}, -goal: Type) -> goal:
  Empty.absurd(goal, L.u32_ne_eq(cur, ne))

def sched_at_commit(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, pick: Maybe<&2, U32>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, ne: {U32.is_ne(cur, Hv.Machine.cur(Hv.Step.m(Hv.sched.at(k, ps, cur, pick, Hv.four(a, b, c, d))))) == True{} : Bool}) -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.sched.at(k, ps, cur, pick, Hv.four(a, b, c, d)))), Hv.Step.acts(Hv.sched.at(k, ps, cur, pick, Hv.four(a, b, c, d)))) == True{} : Bool}:
  match k pick:
    case kk None{}:
      same_cur_absurd(cur, ne, {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.sched.at(k, ps, cur, None{}, Hv.four(a, b, c, d)))), Hv.Step.acts(Hv.sched.at(k, ps, cur, None{}, Hv.four(a, b, c, d)))) == True{} : Bool})
    case Hv.Kernel{+n, +next, +slice} Some{+g}:
      %get_eta4.sym(a, b, c, d, g) : {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.sched.go(Hv.Kernel{n, next, slice}, ps, g, _))), Hv.Step.acts(Hv.sched.go(Hv.Kernel{n, next, slice}, ps, g, _))) == True{} : Bool}
      commits_head(g, [Hv.Arm{slice}, Hv.Enter{g, Hv.VCpu.regs(Pair.snd(Array<Hv.VCpu>, Hv.VCpu, Array.get(Hv.VCpu, Hv.four(a, b, c, d), g)))}])

def sched_commit4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, ne: {U32.is_ne(cur, Hv.Machine.cur(Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})))) == True{} : Bool}) -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Step.acts(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) == True{} : Bool}:
  match k:
    case Hv.Kernel{+n, +next, +slice}:
      %first_live_eta4.sym(Hv.rotation(next), a, b, c, d) : {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.sched.fin(Hv.Kernel{n, next, slice}, ps, cur, _))), Hv.Step.acts(Hv.sched.fin(Hv.Kernel{n, next, slice}, ps, cur, _))) == True{} : Bool}
      sched_at_commit(Hv.Kernel{n, next, slice}, ps, cur, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(Hv.rotation(next), Hv.four(a, b, c, d))), a, b, c, d, (%first_live_eta4(Hv.rotation(next), a, b, c, d) : {U32.is_ne(cur, Hv.Machine.cur(Hv.Step.m(Hv.sched.fin(Hv.Kernel{n, next, slice}, ps, cur, _)))) == True{} : Bool}; ne))

def resume_commit(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, ne: {U32.is_ne(cur, Hv.Machine.cur(Hv.Step.m(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})))) == True{} : Bool}) -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Step.acts(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) == True{} : Bool}:
  %get_eta4.sym(a, b, c, d, cur) : {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.resume.fin(k, ps, cur, _))), Hv.Step.acts(Hv.resume.fin(k, ps, cur, _))) == True{} : Bool}
  same_cur_absurd(cur, (%get_eta4(a, b, c, d, cur) : {U32.is_ne(cur, Hv.Machine.cur(Hv.Step.m(Hv.resume.fin(k, ps, cur, _)))) == True{} : Bool}; ne), {Hv.acts_commits(cur, [Hv.Enter{cur, Hv.VCpu.regs(Pair.snd(Array<Hv.VCpu>, Hv.VCpu, Array.get(Hv.VCpu, Hv.four(a, b, c, d), cur)))}]) == True{} : Bool})

def prepend_acts(x: Hv.Action, s: Hv.Step) -> {Hv.Step.acts(Hv.prepend(x, s)) == x <> Hv.Step.acts(s) : List<&2, Hv.Action>}:
  match s:
    case Hv.Go{k, m, acts}:
      {==}
    case Hv.Fin{k, m, acts}:
      {==}

def halt_commit(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, ne: {U32.is_ne(cur, Hv.Machine.cur(Hv.Step.m(Hv.halt(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})))) == True{} : Bool}) -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.halt(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Step.acts(Hv.halt(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) == True{} : Bool}:
  %Equal.sym(Hv.Machine, Hv.Step.m(Hv.prepend(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), prepend_m(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) : {Hv.acts_commits(Hv.Machine.cur(_), Hv.Step.acts(Hv.prepend(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})))) == True{} : Bool}
  %Equal.sym(List<&2, Hv.Action>, Hv.Step.acts(Hv.prepend(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Stop{cur} <> Hv.Step.acts(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), prepend_acts(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) : {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), _) == True{} : Bool}
  sched_commit4(k, ps, a, b, c, d, cur, (%prepend_m(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) : {U32.is_ne(cur, Hv.Machine.cur(_)) == True{} : Bool}; ne))

def hvc_commit(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, call: Hv.Call, +r: Hv.Regs, ne: {U32.is_ne(cur, Hv.Machine.cur(Hv.Step.m(Hv.hvc(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, call, r)))) == True{} : Bool}) -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.hvc(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, call, r))), Hv.Step.acts(Hv.hvc(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, call, r))) == True{} : Bool}:
  match call:
    case Hv.Yield{}:
      sched_commit4(k, ps, a, b, c, d, cur, ne)
    case Hv.Put{}:
      %Equal.sym(Hv.Machine, Hv.Step.m(Hv.prepend(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Step.m(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), prepend_m(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) : {Hv.acts_commits(Hv.Machine.cur(_), Hv.Step.acts(Hv.prepend(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})))) == True{} : Bool}
      %Equal.sym(List<&2, Hv.Action>, Hv.Step.acts(Hv.prepend(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Print{Hv.char_of(Hv.Regs.x0(r))} <> Hv.Step.acts(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), prepend_acts(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) : {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), _) == True{} : Bool}
      resume_commit(k, ps, a, b, c, d, cur, (%prepend_m(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) : {U32.is_ne(cur, Hv.Machine.cur(_)) == True{} : Bool}; ne))
    case Hv.Quit{}:
      halt_commit(k, ps, a, b, c, d, cur, ne)
    case Hv.Bad{}:
      resume_commit(k, ps, a, b, c, d, cur, ne)

def decide_commit(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, e: Hv.Exit, ne: {U32.is_ne(cur, Hv.Machine.cur(Hv.Step.m(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)))) == True{} : Bool}) -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e))), Hv.Step.acts(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e))) == True{} : Bool}:
  match e:
    case Hv.Timer{r}:
      sched_commit4(k, ps, a, b, c, d, cur, ne)
    case Hv.Wfi{r}:
      sched_commit4(k, ps, a, b, c, d, cur, ne)
    case Hv.Hvc{+imm, +r}:
      hvc_commit(k, ps, a, b, c, d, cur, Hv.decode(imm), r, ne)
    case Hv.DataAbort{ipa, w, r}:
      halt_commit(k, ps, a, b, c, d, cur, ne)
    case Hv.InstAbort{ipa, r}:
      halt_commit(k, ps, a, b, c, d, cur, ne)
    case Hv.Fault{esr, r}:
      halt_commit(k, ps, a, b, c, d, cur, ne)

def handle_commit.k0(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, ne: {U32.is_ne(0, Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 0}, e)))) == True{} : Bool}) -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 0}, e))), Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 0}, e))) == True{} : Bool}:
  decide_commit(k, ps, Hv.VCpu.step(a, e), b, c, d, 0, e, ne)

def handle_commit.k1(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, ne: {U32.is_ne(1, Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 1}, e)))) == True{} : Bool}) -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 1}, e))), Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 1}, e))) == True{} : Bool}:
  decide_commit(k, ps, a, Hv.VCpu.step(b, e), c, d, 1, e, ne)

def handle_commit.k2(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, ne: {U32.is_ne(2, Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 2}, e)))) == True{} : Bool}) -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 2}, e))), Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 2}, e))) == True{} : Bool}:
  decide_commit(k, ps, a, b, Hv.VCpu.step(c, e), d, 2, e, ne)

def handle_commit.k3(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, ne: {U32.is_ne(3, Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 3}, e)))) == True{} : Bool}) -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 3}, e))), Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 3}, e))) == True{} : Bool}:
  decide_commit(k, ps, a, b, c, Hv.VCpu.step(d, e), 3, e, ne)

def handle_commit.c(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -cur: U32, +e: Hv.Exit, vc: L.Lt4<cur>, ne: {U32.is_ne(cur, Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)))) == True{} : Bool}) -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e))), Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e))) == True{} : Bool}:
  match vc:
    case L.K0{+ec}:
      %ec : {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))), Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))) == True{} : Bool}
      handle_commit.k0(k, ps, a, b, c, d, e, (%Equal.sym(U32, 0, cur, ec) : {U32.is_ne(_, Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)))) == True{} : Bool}; ne))
    case L.K1{+ec}:
      %ec : {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))), Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))) == True{} : Bool}
      handle_commit.k1(k, ps, a, b, c, d, e, (%Equal.sym(U32, 1, cur, ec) : {U32.is_ne(_, Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)))) == True{} : Bool}; ne))
    case L.K2{+ec}:
      %ec : {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))), Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))) == True{} : Bool}
      handle_commit.k2(k, ps, a, b, c, d, e, (%Equal.sym(U32, 2, cur, ec) : {U32.is_ne(_, Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)))) == True{} : Bool}; ne))
    case L.K3{+ec}:
      %ec : {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))), Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))) == True{} : Bool}
      handle_commit.k3(k, ps, a, b, c, d, e, (%Equal.sym(U32, 3, cur, ec) : {U32.is_ne(_, Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)))) == True{} : Bool}; ne))

def commit_on_switch.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +e: Hv.Exit, sc: Hv.Slot(cur), -vs: Array<Hv.VCpu>, ne: {U32.is_ne(cur, Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, vs, cur}, e)))) == True{} : Bool}, v4: Four<vs>) -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, vs, cur}, e))), Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, vs, cur}, e))) == True{} : Bool}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      moved : ({U32.is_ne(cur, Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, vs, cur}, e)))) == True{} : Bool} -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, vs, cur}, e))), Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, vs, cur}, e))) == True{} : Bool}) = %ev4 : ({U32.is_ne(cur, Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, _, cur}, e)))) == True{} : Bool} -> {Hv.acts_commits(Hv.Machine.cur(Hv.Step.m(Hv.handle(k, Hv.Machine{ps, _, cur}, e))), Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, _, cur}, e))) == True{} : Bool})
        n => handle_commit.c(k, ps, a, b, c, d, cur, e, L.lt4(cur, sc), n)
      moved(ne)

def Laws.commit_on_switch(k, m, e, ok, ne):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      commit_on_switch.v(k, ps, cur, e, sc, vs, ne, four_view(vs, sv))

def sched_at_stops(+cur: U32, +k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, pick: Maybe<&2, U32>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu) -> {Hv.stops_self(cur, Hv.Step.acts(Hv.sched.at(k, ps, cur, pick, Hv.four(a, b, c, d)))) == True{} : Bool}:
  match k pick:
    case kk None{}:
      {==}
    case Hv.Kernel{+n, +next, +slice} Some{+g}:
      %get_eta4.sym(a, b, c, d, g) : {Hv.stops_self(cur, Hv.Step.acts(Hv.sched.go(Hv.Kernel{n, next, slice}, ps, g, _))) == True{} : Bool}
      {==}

def sched_stops4(+cur: U32, +k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu) -> {Hv.stops_self(cur, Hv.Step.acts(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) == True{} : Bool}:
  match k:
    case Hv.Kernel{+n, +next, +slice}:
      %first_live_eta4.sym(Hv.rotation(next), a, b, c, d) : {Hv.stops_self(cur, Hv.Step.acts(Hv.sched.fin(Hv.Kernel{n, next, slice}, ps, cur, _))) == True{} : Bool}
      sched_at_stops(cur, Hv.Kernel{n, next, slice}, ps, Pair.snd(Array<Hv.VCpu>, Maybe<&2, U32>, Hv.first_live(Hv.rotation(next), Hv.four(a, b, c, d))), a, b, c, d)

def stop_head(+cur: U32, +rest: List<&2, Hv.Action>, hr: {Hv.stops_self(cur, rest) == True{} : Bool}) -> {Hv.stops_self(cur, Hv.Stop{cur} <> rest) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(cur, cur), True{}, L.u32_refl(cur)) : {Bool.and(_, Hv.stops_self(cur, rest)) == True{} : Bool}
  %Equal.sym(Bool, Hv.stops_self(cur, rest), True{}, hr) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

def halt_stops(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> {Hv.stops_self(cur, Hv.Step.acts(Hv.halt(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) == True{} : Bool}:
  %Equal.sym(List<&2, Hv.Action>, Hv.Step.acts(Hv.prepend(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Stop{cur} <> Hv.Step.acts(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), prepend_acts(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) : {Hv.stops_self(cur, _) == True{} : Bool}
  stop_head(cur, Hv.Step.acts(Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), sched_stops4(cur, k, ps, a, b, c, d))

def resume_stops(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> {Hv.stops_self(cur, Hv.Step.acts(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) == True{} : Bool}:
  %get_eta4.sym(a, b, c, d, cur) : {Hv.stops_self(cur, Hv.Step.acts(Hv.resume.fin(k, ps, cur, _))) == True{} : Bool}
  {==}

def hvc_stops(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, call: Hv.Call, +r: Hv.Regs) -> {Hv.stops_self(cur, Hv.Step.acts(Hv.hvc(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, call, r))) == True{} : Bool}:
  match call:
    case Hv.Yield{}:
      sched_stops4(cur, k, ps, a, b, c, d)
    case Hv.Put{}:
      %Equal.sym(List<&2, Hv.Action>, Hv.Step.acts(Hv.prepend(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))), Hv.Print{Hv.char_of(Hv.Regs.x0(r))} <> Hv.Step.acts(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})), prepend_acts(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}))) : {Hv.stops_self(cur, _) == True{} : Bool}
      resume_stops(k, ps, a, b, c, d, cur)
    case Hv.Quit{}:
      halt_stops(k, ps, a, b, c, d, cur)
    case Hv.Bad{}:
      resume_stops(k, ps, a, b, c, d, cur)

def decide_stops(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, e: Hv.Exit) -> {Hv.stops_self(cur, Hv.Step.acts(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e))) == True{} : Bool}:
  match e:
    case Hv.Timer{r}:
      sched_stops4(cur, k, ps, a, b, c, d)
    case Hv.Wfi{r}:
      sched_stops4(cur, k, ps, a, b, c, d)
    case Hv.Hvc{+imm, +r}:
      hvc_stops(k, ps, a, b, c, d, cur, Hv.decode(imm), r)
    case Hv.DataAbort{ipa, w, r}:
      halt_stops(k, ps, a, b, c, d, cur)
    case Hv.InstAbort{ipa, r}:
      halt_stops(k, ps, a, b, c, d, cur)
    case Hv.Fault{esr, r}:
      halt_stops(k, ps, a, b, c, d, cur)

def handle_stops.k0(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.stops_self(0, Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 0}, e))) == True{} : Bool}:
  decide_stops(k, ps, Hv.VCpu.step(a, e), b, c, d, 0, e)

def handle_stops.k1(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.stops_self(1, Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 1}, e))) == True{} : Bool}:
  decide_stops(k, ps, a, Hv.VCpu.step(b, e), c, d, 1, e)

def handle_stops.k2(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.stops_self(2, Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 2}, e))) == True{} : Bool}:
  decide_stops(k, ps, a, b, Hv.VCpu.step(c, e), d, 2, e)

def handle_stops.k3(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit) -> {Hv.stops_self(3, Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 3}, e))) == True{} : Bool}:
  decide_stops(k, ps, a, b, c, Hv.VCpu.step(d, e), 3, e)

def handle_stops.c(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -cur: U32, +e: Hv.Exit, vc: L.Lt4<cur>) -> {Hv.stops_self(cur, Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e))) == True{} : Bool}:
  match vc:
    case L.K0{ec}:
      %ec : {Hv.stops_self(_, Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))) == True{} : Bool}
      handle_stops.k0(k, ps, a, b, c, d, e)
    case L.K1{ec}:
      %ec : {Hv.stops_self(_, Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))) == True{} : Bool}
      handle_stops.k1(k, ps, a, b, c, d, e)
    case L.K2{ec}:
      %ec : {Hv.stops_self(_, Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))) == True{} : Bool}
      handle_stops.k2(k, ps, a, b, c, d, e)
    case L.K3{ec}:
      %ec : {Hv.stops_self(_, Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e))) == True{} : Bool}
      handle_stops.k3(k, ps, a, b, c, d, e)

def stop_self.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +e: Hv.Exit, sc: Hv.Slot(cur), -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.stops_self(cur, Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, vs, cur}, e))) == True{} : Bool}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.stops_self(cur, Hv.Step.acts(Hv.handle(k, Hv.Machine{ps, _, cur}, e))) == True{} : Bool}
      handle_stops.c(k, ps, a, b, c, d, cur, e, L.lt4(cur, sc))

def Laws.stop_self(k, m, e, ok):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      stop_self.v(k, ps, cur, e, sc, vs, four_view(vs, sv))

def decode_put(+imm: U32, one: {U32.is_eq(imm, 1) == True{} : Bool}) -> {Hv.decode(imm) == Hv.Put{} : Hv.Call}:
  %Equal.sym(U32, imm, 1, L.u32_eq(imm, 1, one)) : {Hv.decode(_) == Hv.Put{} : Hv.Call}
  {==}

def put_want(+r: Hv.Regs) -> Maybe<&2, String> & Bool:
  (Some{Hv.char_of(Hv.Regs.x0(r))}, False{})

def hvc_put(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, +r: Hv.Regs) -> {Hv.put_obs(Hv.hvc(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, Hv.Put{}, r)) == put_want(r) : Maybe<&2, String> & Bool}:
  %get_eta4.sym(a, b, c, d, cur) : {Hv.put_obs(Hv.prepend(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume.fin(k, ps, cur, _))) == put_want(r) : Maybe<&2, String> & Bool}
  {==}

def decide_put(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, +imm: U32, +r: Hv.Regs, one: {U32.is_eq(imm, 1) == True{} : Bool}) -> {Hv.put_obs(Hv.decide(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, Hv.Hvc{imm, r})) == put_want(r) : Maybe<&2, String> & Bool}:
  %Equal.sym(Hv.Call, Hv.decode(imm), Hv.Put{}, decode_put(imm, one)) : {Hv.put_obs(Hv.hvc(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, _, r)) == put_want(r) : Maybe<&2, String> & Bool}
  hvc_put(k, ps, a, b, c, d, cur, r)

def handle_put.k0(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +imm: U32, +r: Hv.Regs, one: {U32.is_eq(imm, 1) == True{} : Bool}) -> {Hv.put_obs(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 0}, Hv.Hvc{imm, r})) == put_want(r) : Maybe<&2, String> & Bool}:
  decide_put(k, ps, Hv.VCpu.step(a, Hv.Hvc{imm, r}), b, c, d, 0, imm, r, one)

def handle_put.k1(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +imm: U32, +r: Hv.Regs, one: {U32.is_eq(imm, 1) == True{} : Bool}) -> {Hv.put_obs(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 1}, Hv.Hvc{imm, r})) == put_want(r) : Maybe<&2, String> & Bool}:
  decide_put(k, ps, a, Hv.VCpu.step(b, Hv.Hvc{imm, r}), c, d, 1, imm, r, one)

def handle_put.k2(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +imm: U32, +r: Hv.Regs, one: {U32.is_eq(imm, 1) == True{} : Bool}) -> {Hv.put_obs(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 2}, Hv.Hvc{imm, r})) == put_want(r) : Maybe<&2, String> & Bool}:
  decide_put(k, ps, a, b, Hv.VCpu.step(c, Hv.Hvc{imm, r}), d, 2, imm, r, one)

def handle_put.k3(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +imm: U32, +r: Hv.Regs, one: {U32.is_eq(imm, 1) == True{} : Bool}) -> {Hv.put_obs(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 3}, Hv.Hvc{imm, r})) == put_want(r) : Maybe<&2, String> & Bool}:
  decide_put(k, ps, a, b, c, Hv.VCpu.step(d, Hv.Hvc{imm, r}), 3, imm, r, one)

def handle_put.c(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -cur: U32, +imm: U32, +r: Hv.Regs, vc: L.Lt4<cur>, one: {U32.is_eq(imm, 1) == True{} : Bool}) -> {Hv.put_obs(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, Hv.Hvc{imm, r})) == put_want(r) : Maybe<&2, String> & Bool}:
  match vc:
    case L.K0{ec}:
      %ec : {Hv.put_obs(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, Hv.Hvc{imm, r})) == put_want(r) : Maybe<&2, String> & Bool}
      handle_put.k0(k, ps, a, b, c, d, imm, r, one)
    case L.K1{ec}:
      %ec : {Hv.put_obs(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, Hv.Hvc{imm, r})) == put_want(r) : Maybe<&2, String> & Bool}
      handle_put.k1(k, ps, a, b, c, d, imm, r, one)
    case L.K2{ec}:
      %ec : {Hv.put_obs(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, Hv.Hvc{imm, r})) == put_want(r) : Maybe<&2, String> & Bool}
      handle_put.k2(k, ps, a, b, c, d, imm, r, one)
    case L.K3{ec}:
      %ec : {Hv.put_obs(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, Hv.Hvc{imm, r})) == put_want(r) : Maybe<&2, String> & Bool}
      handle_put.k3(k, ps, a, b, c, d, imm, r, one)

def put_prints.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +imm: U32, +r: Hv.Regs, sc: Hv.Slot(cur), one: {U32.is_eq(imm, 1) == True{} : Bool}, -vs: Array<Hv.VCpu>, v4: Four<vs>) -> {Hv.put_obs(Hv.handle(k, Hv.Machine{ps, vs, cur}, Hv.Hvc{imm, r})) == put_want(r) : Maybe<&2, String> & Bool}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      %ev4 : {Hv.put_obs(Hv.handle(k, Hv.Machine{ps, _, cur}, Hv.Hvc{imm, r})) == put_want(r) : Maybe<&2, String> & Bool}
      handle_put.c(k, ps, a, b, c, d, cur, imm, r, L.lt4(cur, sc), one)

def Laws.put_prints(k, m, imm, r, ok, one):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      put_prints.v(k, ps, cur, imm, r, sc, one, vs, four_view(vs, sv))

def put_step_live.go(+regs: Hv.Regs, +live: Bool, +imm: U32, +r: Hv.Regs, one: {U32.is_eq(imm, 1) == True{} : Bool}, lv: {live == True{} : Bool}) -> {Hv.VCpu.live(Hv.VCpu.step(Hv.VCpu{regs, live}, Hv.Hvc{imm, r})) == True{} : Bool}:
  %Equal.sym(Hv.Call, Hv.decode(imm), Hv.Put{}, decode_put(imm, one)) : {Hv.VCpu.live(Hv.VCpu.call(Hv.VCpu{regs, live}, _, r)) == True{} : Bool}
  lv

def put_step_live(+v: Hv.VCpu, +imm: U32, +r: Hv.Regs, one: {U32.is_eq(imm, 1) == True{} : Bool}, lv: {Hv.VCpu.live(v) == True{} : Bool}) -> {Hv.VCpu.live(Hv.VCpu.step(v, Hv.Hvc{imm, r})) == True{} : Bool}:
  match v:
    case Hv.VCpu{+regs, +live}:
      put_step_live.go(regs, live, imm, r, one, lv)

def bad_step_live.go(+regs: Hv.Regs, +live: Bool, +imm: U32, +r: Hv.Regs, z0: {U32.is_eq(imm, 0) == False{} : Bool}, z1: {U32.is_eq(imm, 1) == False{} : Bool}, z2: {U32.is_eq(imm, 2) == False{} : Bool}, lv: {live == True{} : Bool}) -> {Hv.VCpu.live(Hv.VCpu.step(Hv.VCpu{regs, live}, Hv.Hvc{imm, r})) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(imm, 0), False{}, z0) : {Hv.VCpu.live(Hv.VCpu.call(Hv.VCpu{regs, live}, Bool.pick(Hv.Call, _, Hv.Yield{}, Bool.pick(Hv.Call, U32.is_eq(imm, 1), Hv.Put{}, Bool.pick(Hv.Call, U32.is_eq(imm, 2), Hv.Quit{}, Hv.Bad{}))), r)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(imm, 1), False{}, z1) : {Hv.VCpu.live(Hv.VCpu.call(Hv.VCpu{regs, live}, Bool.pick(Hv.Call, _, Hv.Put{}, Bool.pick(Hv.Call, U32.is_eq(imm, 2), Hv.Quit{}, Hv.Bad{})), r)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(imm, 2), False{}, z2) : {Hv.VCpu.live(Hv.VCpu.call(Hv.VCpu{regs, live}, Bool.pick(Hv.Call, _, Hv.Quit{}, Hv.Bad{}), r)) == True{} : Bool}
  lv

def bad_step_live(+v: Hv.VCpu, +imm: U32, +r: Hv.Regs, z0: {U32.is_eq(imm, 0) == False{} : Bool}, z1: {U32.is_eq(imm, 1) == False{} : Bool}, z2: {U32.is_eq(imm, 2) == False{} : Bool}, lv: {Hv.VCpu.live(v) == True{} : Bool}) -> {Hv.VCpu.live(Hv.VCpu.step(v, Hv.Hvc{imm, r})) == True{} : Bool}:
  match v:
    case Hv.VCpu{+regs, +live}:
      bad_step_live.go(regs, live, imm, r, z0, z1, z2, lv)

def prepend_live(x: Hv.Action, s: Hv.Step) -> {Hv.on_core_live(Hv.prepend(x, s)) == Hv.on_core_live(s) : Bool}:
  match s:
    case Hv.Go{k, Hv.Machine{ps, vs, +cur}, acts}:
      {==}
    case Hv.Fin{k, m, acts}:
      {==}

def prepend_live_true(x: Hv.Action, s: Hv.Step, p: {Hv.on_core_live(s) == True{} : Bool}) -> {Hv.on_core_live(Hv.prepend(x, s)) == True{} : Bool}:
  %Equal.sym(Bool, Hv.on_core_live(Hv.prepend(x, s)), Hv.on_core_live(s), prepend_live(x, s)) : {_ == True{} : Bool}
  p

def resume_live4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32, lv: {Hv.VCpu.live(Hv.vcpu_at(Hv.four(a, b, c, d), cur)) == True{} : Bool}) -> {Hv.on_core_live(Hv.resume(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) == True{} : Bool}:
  %get_eta4.sym(a, b, c, d, cur) : {Hv.on_core_live(Hv.resume.fin(k, ps, cur, _)) == True{} : Bool}
  lv

def halt_live4(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +cur: U32) -> {Hv.on_core_live(Hv.halt(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur})) == True{} : Bool}:
  prepend_live_true(Hv.Stop{cur}, Hv.sched(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}), sched_live4(k, ps, a, b, c, d, cur))

def hvc_b2(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +sa: Hv.VCpu, +sb: Hv.VCpu, +sc: Hv.VCpu, +sd: Hv.VCpu, +cur: U32, +v: Hv.VCpu, +imm: U32, +r: Hv.Regs, slot: {Hv.vcpu_at(Hv.four(sa, sb, sc, sd), cur) == Hv.VCpu.step(v, Hv.Hvc{imm, r}) : Hv.VCpu}, lv: {Hv.VCpu.live(v) == True{} : Bool}, z0: {U32.is_eq(imm, 0) == False{} : Bool}, z1: {U32.is_eq(imm, 1) == False{} : Bool}, b2: Bool, eb2: {U32.is_eq(imm, 2) == b2 : Bool}) -> {Hv.on_core_live(Hv.hvc(k, Hv.Machine{ps, Hv.four(sa, sb, sc, sd), cur}, Bool.pick(Hv.Call, b2, Hv.Quit{}, Hv.Bad{}), r)) == True{} : Bool}:
  match b2:
    case True{}:
      halt_live4(k, ps, sa, sb, sc, sd, cur)
    case False{}:
      resume_live4(k, ps, sa, sb, sc, sd, cur, (%Equal.sym(Hv.VCpu, Hv.vcpu_at(Hv.four(sa, sb, sc, sd), cur), Hv.VCpu.step(v, Hv.Hvc{imm, r}), slot) : {Hv.VCpu.live(_) == True{} : Bool}; bad_step_live(v, imm, r, z0, z1, eb2, lv)))

def hvc_b1(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +sa: Hv.VCpu, +sb: Hv.VCpu, +sc: Hv.VCpu, +sd: Hv.VCpu, +cur: U32, +v: Hv.VCpu, +imm: U32, +r: Hv.Regs, slot: {Hv.vcpu_at(Hv.four(sa, sb, sc, sd), cur) == Hv.VCpu.step(v, Hv.Hvc{imm, r}) : Hv.VCpu}, lv: {Hv.VCpu.live(v) == True{} : Bool}, z0: {U32.is_eq(imm, 0) == False{} : Bool}, b1: Bool, eb1: {U32.is_eq(imm, 1) == b1 : Bool}) -> {Hv.on_core_live(Hv.hvc(k, Hv.Machine{ps, Hv.four(sa, sb, sc, sd), cur}, Bool.pick(Hv.Call, b1, Hv.Put{}, Bool.pick(Hv.Call, U32.is_eq(imm, 2), Hv.Quit{}, Hv.Bad{})), r)) == True{} : Bool}:
  match b1:
    case True{}:
      prepend_live_true(Hv.Print{Hv.char_of(Hv.Regs.x0(r))}, Hv.resume(k, Hv.Machine{ps, Hv.four(sa, sb, sc, sd), cur}), resume_live4(k, ps, sa, sb, sc, sd, cur, (%Equal.sym(Hv.VCpu, Hv.vcpu_at(Hv.four(sa, sb, sc, sd), cur), Hv.VCpu.step(v, Hv.Hvc{imm, r}), slot) : {Hv.VCpu.live(_) == True{} : Bool}; put_step_live(v, imm, r, eb1, lv))))
    case False{}:
      hvc_b2(k, ps, sa, sb, sc, sd, cur, v, imm, r, slot, lv, z0, eb1, U32.is_eq(imm, 2), {==})

def hvc_live(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +sa: Hv.VCpu, +sb: Hv.VCpu, +sc: Hv.VCpu, +sd: Hv.VCpu, +cur: U32, +v: Hv.VCpu, +imm: U32, +r: Hv.Regs, slot: {Hv.vcpu_at(Hv.four(sa, sb, sc, sd), cur) == Hv.VCpu.step(v, Hv.Hvc{imm, r}) : Hv.VCpu}, lv: {Hv.VCpu.live(v) == True{} : Bool}, b0: Bool, eb0: {U32.is_eq(imm, 0) == b0 : Bool}) -> {Hv.on_core_live(Hv.hvc(k, Hv.Machine{ps, Hv.four(sa, sb, sc, sd), cur}, Bool.pick(Hv.Call, b0, Hv.Yield{}, Bool.pick(Hv.Call, U32.is_eq(imm, 1), Hv.Put{}, Bool.pick(Hv.Call, U32.is_eq(imm, 2), Hv.Quit{}, Hv.Bad{}))), r)) == True{} : Bool}:
  match b0:
    case True{}:
      sched_live4(k, ps, sa, sb, sc, sd, cur)
    case False{}:
      hvc_b1(k, ps, sa, sb, sc, sd, cur, v, imm, r, slot, lv, eb0, U32.is_eq(imm, 1), {==})

def handle_live.k0(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, lv: {Hv.VCpu.live(a) == True{} : Bool}) -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 0}, e)) == True{} : Bool}:
  match e:
    case Hv.Timer{r}:
      sched_live4(k, ps, Hv.VCpu.step(a, Hv.Timer{r}), b, c, d, 0)
    case Hv.Wfi{r}:
      sched_live4(k, ps, Hv.VCpu.step(a, Hv.Wfi{r}), b, c, d, 0)
    case Hv.Hvc{+imm, +r}:
      hvc_live(k, ps, Hv.VCpu.step(a, Hv.Hvc{imm, r}), b, c, d, 0, a, imm, r, {==}, lv, U32.is_eq(imm, 0), {==})
    case Hv.DataAbort{ipa, w, r}:
      halt_live4(k, ps, Hv.VCpu.step(a, Hv.DataAbort{ipa, w, r}), b, c, d, 0)
    case Hv.InstAbort{ipa, r}:
      halt_live4(k, ps, Hv.VCpu.step(a, Hv.InstAbort{ipa, r}), b, c, d, 0)
    case Hv.Fault{esr, r}:
      halt_live4(k, ps, Hv.VCpu.step(a, Hv.Fault{esr, r}), b, c, d, 0)

def handle_live.k1(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, lv: {Hv.VCpu.live(b) == True{} : Bool}) -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 1}, e)) == True{} : Bool}:
  match e:
    case Hv.Timer{r}:
      sched_live4(k, ps, a, Hv.VCpu.step(b, Hv.Timer{r}), c, d, 1)
    case Hv.Wfi{r}:
      sched_live4(k, ps, a, Hv.VCpu.step(b, Hv.Wfi{r}), c, d, 1)
    case Hv.Hvc{+imm, +r}:
      hvc_live(k, ps, a, Hv.VCpu.step(b, Hv.Hvc{imm, r}), c, d, 1, b, imm, r, {==}, lv, U32.is_eq(imm, 0), {==})
    case Hv.DataAbort{ipa, w, r}:
      halt_live4(k, ps, a, Hv.VCpu.step(b, Hv.DataAbort{ipa, w, r}), c, d, 1)
    case Hv.InstAbort{ipa, r}:
      halt_live4(k, ps, a, Hv.VCpu.step(b, Hv.InstAbort{ipa, r}), c, d, 1)
    case Hv.Fault{esr, r}:
      halt_live4(k, ps, a, Hv.VCpu.step(b, Hv.Fault{esr, r}), c, d, 1)

def handle_live.k2(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, lv: {Hv.VCpu.live(c) == True{} : Bool}) -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 2}, e)) == True{} : Bool}:
  match e:
    case Hv.Timer{r}:
      sched_live4(k, ps, a, b, Hv.VCpu.step(c, Hv.Timer{r}), d, 2)
    case Hv.Wfi{r}:
      sched_live4(k, ps, a, b, Hv.VCpu.step(c, Hv.Wfi{r}), d, 2)
    case Hv.Hvc{+imm, +r}:
      hvc_live(k, ps, a, b, Hv.VCpu.step(c, Hv.Hvc{imm, r}), d, 2, c, imm, r, {==}, lv, U32.is_eq(imm, 0), {==})
    case Hv.DataAbort{ipa, w, r}:
      halt_live4(k, ps, a, b, Hv.VCpu.step(c, Hv.DataAbort{ipa, w, r}), d, 2)
    case Hv.InstAbort{ipa, r}:
      halt_live4(k, ps, a, b, Hv.VCpu.step(c, Hv.InstAbort{ipa, r}), d, 2)
    case Hv.Fault{esr, r}:
      halt_live4(k, ps, a, b, Hv.VCpu.step(c, Hv.Fault{esr, r}), d, 2)

def handle_live.k3(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, +e: Hv.Exit, lv: {Hv.VCpu.live(d) == True{} : Bool}) -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), 3}, e)) == True{} : Bool}:
  match e:
    case Hv.Timer{r}:
      sched_live4(k, ps, a, b, c, Hv.VCpu.step(d, Hv.Timer{r}), 3)
    case Hv.Wfi{r}:
      sched_live4(k, ps, a, b, c, Hv.VCpu.step(d, Hv.Wfi{r}), 3)
    case Hv.Hvc{+imm, +r}:
      hvc_live(k, ps, a, b, c, Hv.VCpu.step(d, Hv.Hvc{imm, r}), 3, d, imm, r, {==}, lv, U32.is_eq(imm, 0), {==})
    case Hv.DataAbort{ipa, w, r}:
      halt_live4(k, ps, a, b, c, Hv.VCpu.step(d, Hv.DataAbort{ipa, w, r}), 3)
    case Hv.InstAbort{ipa, r}:
      halt_live4(k, ps, a, b, c, Hv.VCpu.step(d, Hv.InstAbort{ipa, r}), 3)
    case Hv.Fault{esr, r}:
      halt_live4(k, ps, a, b, c, Hv.VCpu.step(d, Hv.Fault{esr, r}), 3)

def handle_live.c(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +a: Hv.VCpu, +b: Hv.VCpu, +c: Hv.VCpu, +d: Hv.VCpu, -cur: U32, +e: Hv.Exit, vc: L.Lt4<cur>, lv: {Hv.VCpu.live(Hv.vcpu_at(Hv.four(a, b, c, d), cur)) == True{} : Bool}) -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)) == True{} : Bool}:
  match vc:
    case L.K0{ec}:
      moved : ({Hv.VCpu.live(Hv.vcpu_at(Hv.four(a, b, c, d), cur)) == True{} : Bool} -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)) == True{} : Bool}) = %ec : ({Hv.VCpu.live(Hv.vcpu_at(Hv.four(a, b, c, d), _)) == True{} : Bool} -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)) == True{} : Bool})
        n => handle_live.k0(k, ps, a, b, c, d, e, n)
      moved(lv)
    case L.K1{ec}:
      moved : ({Hv.VCpu.live(Hv.vcpu_at(Hv.four(a, b, c, d), cur)) == True{} : Bool} -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)) == True{} : Bool}) = %ec : ({Hv.VCpu.live(Hv.vcpu_at(Hv.four(a, b, c, d), _)) == True{} : Bool} -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)) == True{} : Bool})
        n => handle_live.k1(k, ps, a, b, c, d, e, n)
      moved(lv)
    case L.K2{ec}:
      moved : ({Hv.VCpu.live(Hv.vcpu_at(Hv.four(a, b, c, d), cur)) == True{} : Bool} -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)) == True{} : Bool}) = %ec : ({Hv.VCpu.live(Hv.vcpu_at(Hv.four(a, b, c, d), _)) == True{} : Bool} -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)) == True{} : Bool})
        n => handle_live.k2(k, ps, a, b, c, d, e, n)
      moved(lv)
    case L.K3{ec}:
      moved : ({Hv.VCpu.live(Hv.vcpu_at(Hv.four(a, b, c, d), cur)) == True{} : Bool} -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), cur}, e)) == True{} : Bool}) = %ec : ({Hv.VCpu.live(Hv.vcpu_at(Hv.four(a, b, c, d), _)) == True{} : Bool} -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, Hv.four(a, b, c, d), _}, e)) == True{} : Bool})
        n => handle_live.k3(k, ps, a, b, c, d, e, n)
      moved(lv)

def handle_enters_live.v(+k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +cur: U32, +e: Hv.Exit, sc: Hv.Slot(cur), -vs: Array<Hv.VCpu>, lv: {Hv.VCpu.live(Hv.vcpu_at(vs, cur)) == True{} : Bool}, v4: Four<vs>) -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, vs, cur}, e)) == True{} : Bool}:
  match v4:
    case IsFour{+a, +b, +c, +d, ev4}:
      moved : ({Hv.VCpu.live(Hv.vcpu_at(vs, cur)) == True{} : Bool} -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, vs, cur}, e)) == True{} : Bool}) = %ev4 : ({Hv.VCpu.live(Hv.vcpu_at(_, cur)) == True{} : Bool} -> {Hv.on_core_live(Hv.handle(k, Hv.Machine{ps, _, cur}, e)) == True{} : Bool})
        n => handle_live.c(k, ps, a, b, c, d, cur, e, L.lt4(cur, sc), n)
      moved(lv)

def Laws.handle_enters_live(k, m, e, ok, lv):
  match m:
    case Hv.Machine{+ps, vs, +cur}:
      Hv.Both{sp, Hv.Both{op, Hv.Both{sv, sc}}} = ok
      handle_enters_live.v(k, ps, cur, e, sc, vs, lv, four_view(vs, sv))

# The hypotheses hold
# -------------------
# the laws assume Machine.ok; the boot machines satisfy it, so no law is
# vacuous. The owners and the shape are checked by computing a Bool.

def owner_okb(o: Hv.Owner, e: {Hv.Owner.okb(o) == True{} : Bool}) -> Hv.Owner.ok(o):
  match o:
    case Hv.Free{}:
      Unit{}
    case Hv.Hyp{}:
      Unit{}
    case Hv.Of{g}:
      e

def owners_okb(+t: Hv.Tree<Hv.Owner>, +e: {Hv.Owners.okb(t) == True{} : Bool}) -> Hv.Owners.ok(t):
  match t:
    case Hv.Leaf{o}:
      owner_okb(o, e)
    case Hv.Node{+lo, +hi}:
      Hv.Both{owners_okb(lo, L.and_l(Hv.Owners.okb(lo), Hv.Owners.okb(hi), e)), owners_okb(hi, L.and_r(Hv.Owners.okb(lo), Hv.Owners.okb(hi), e))}

def shapeb(+t: Hv.Tree<Hv.Owner>, +d: Nat, +e: {Hv.Tree.shapeb(t, d) == True{} : Bool}) -> Hv.Tree.shape(Hv.Owner, t, d):
  match t d:
    case Hv.Leaf{o} 0n:
      Unit{}
    case Hv.Node{lo, hi} 0n:
      Empty.absurd(Hv.Tree.shape(Hv.Owner, Hv.Node{lo, hi}, 0n), L.false_true(e))
    case Hv.Leaf{o} 1n+p:
      Empty.absurd(Hv.Tree.shape(Hv.Owner, Hv.Leaf{o}, 1n+p), L.false_true(e))
    case Hv.Node{+lo, +hi} 1n+p:
      Hv.Both{shapeb(lo, p, L.and_l(Hv.Tree.shapeb(lo, p), Hv.Tree.shapeb(hi, p), e)), shapeb(hi, p, L.and_r(Hv.Tree.shapeb(lo, p), Hv.Tree.shapeb(hi, p), e))}

# the simulator's machine of three guests, and the real driver's of four
def boot_ok.of(+n: U32, +es: {Hv.Tree.shapeb(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(n)), Hv.page_depth()) == True{} : Bool}, +eo: {Hv.Owners.okb(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(n))) == True{} : Bool}) -> Hv.Machine.ok(Hv.boot_machine(n)):
  Hv.Both{shapeb(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(n)), Hv.page_depth(), es),
    Hv.Both{owners_okb(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(n)), eo),
      Hv.Both{Hv.Both{Hv.Both{Unit{}, Unit{}}, Hv.Both{Unit{}, Unit{}}}, {==}}}}

def boot_ok3() -> Hv.Machine.ok(Hv.boot_machine(3)):
  boot_ok.of(3, {==}, {==})

def boot_ok4() -> Hv.Machine.ok(Hv.boot_machine(4)):
  boot_ok.of(4, {==}, {==})

# The guest step
# --------------
# the hardware axiom, from Isa.bend. Every case of a step builds the
# next state with `out` or with `halt`, and the only fields it can write
# that the axiom speaks of are the system registers and memory. So there
# is one lemma for a step that writes them (ax.wr, which takes what the
# write does to the two of them), the facts that discharge it (a write
# of the guest's own register, of a register an entry writes, or of a
# block stage 2 maps, changes nothing the axiom watches), and a line per
# instruction form.

# what a guest step keeps: the doubleword at an address it is not
# mapped to, a system register that is neither its own nor one an
# exception entry writes, and the stage-2 map
def ax.G(+a: Hv.W64, +e: U32, +s: I.State, o: I.Out) -> Type:
  {I.mem_read(I.State.mem(I.Out.s(o)), a) == I.mem_read(I.State.mem(s), a) : Hv.W64} &
  {I.sys_read(I.State.sys(I.Out.s(o)), e) == I.sys_read(I.State.sys(s), e) : Hv.W64} &
  {I.State.s2(I.Out.s(o)) == I.State.s2(s) : Hv.Tree<Bool>}

# the state a step starts from, as its fields; the level is EL1
def ax.S(+x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>) -> I.State:
  I.State{I.Cpu{x, pc, 1, spsel, nzcv, daif, sys}, mem, rom, s2}

def ax.Sys(+sys2: List<&2, I.Sr>, +sys: List<&2, I.Sr>, +e: U32) -> Type:
  {I.sys_read(sys2, e) == I.sys_read(sys, e) : Hv.W64}

def ax.Mem(+mem2: List<&2, I.Cell>, +mem: List<&2, I.Cell>, +a: Hv.W64) -> Type:
  {I.mem_read(mem2, a) == I.mem_read(mem, a) : Hv.W64}

# Writers
# -------

# a step whose next state keeps the map, and whose system registers and
# memory are what the two proofs say
def ax.wr(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +x2: List<&2, Hv.W64>, +pc2: Hv.W64, +el2: U32, +spsel2: U32, +nzcv2: U32, +daif2: U32, +sys2: List<&2, I.Sr>, +mem2: List<&2, I.Cell>, ps: ax.Sys(sys2, sys, e), pm: ax.Mem(mem2, mem, a))
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.out(x2, pc2, el2, spsel2, nzcv2, daif2, sys2, mem2, rom, s2)):
  (pm, (ps, {==}))

def ax.stop(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +why: String)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.halt(why, x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2)):
  ({==}, ({==}, {==}))

# Side conditions
# ---------------

def ax.skip(+k: U32, +v: Hv.W64, +rest: List<&2, I.Sr>, +e: U32, ne: {U32.is_eq(k, e) == False{} : Bool}) -> ax.Sys(I.sys_write(rest, k, v), rest, e):
  %Equal.sym(Bool, U32.is_eq(k, e), False{}, ne) : {Bool.pick(Hv.W64, _, v, I.sys_read(rest, e)) == I.sys_read(rest, e) : Hv.W64}
  {==}

# a register the guest may write is not one the axiom watches
def ax.not_own.go(+k: U32, +e: U32, ek: {I.own_reg(k) == True{} : Bool}, ue: {I.own_reg(e) == False{} : Bool}, +b: Bool, eb: {U32.is_eq(k, e) == b : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_true(Equal.trans(Bool, False{}, I.own_reg(e), True{},
        Equal.sym(Bool, I.own_reg(e), False{}, ue),
        (%L.u32_eq(k, e, eb) : {I.own_reg(_) == True{} : Bool}; ek))))

def ax.not_own(+k: U32, +e: U32, ek: {I.own_reg(k) == True{} : Bool}, ue: {I.own_reg(e) == False{} : Bool}) -> {U32.is_eq(k, e) == False{} : Bool}:
  ax.not_own.go(k, e, ek, ue, U32.is_eq(k, e), {==})

# the stack pointer a guest uses is its own
def ax.sp_own.go(+spsel: U32, +b: Bool, eb: {U32.is_eq(spsel, 0) == b : Bool}) -> {I.own_reg(Bool.pick(U32, b, I.SP_EL0(), I.SP_EL1())) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def ax.sp_own(+spsel: U32) -> {I.own_reg(I.sp_enc(1, spsel)) == True{} : Bool}:
  ax.sp_own.go(spsel, U32.is_eq(spsel, 0), {==})

def ax.sp_skip(+spsel: U32, +v: Hv.W64, +sys: List<&2, I.Sr>, +e: U32, ue: {I.own_reg(e) == False{} : Bool}) -> ax.Sys(I.sys_write(sys, I.sp_enc(1, spsel), v), sys, e):
  ax.skip(I.sp_enc(1, spsel), v, sys, e, ax.not_own(I.sp_enc(1, spsel), e, ax.sp_own(spsel), ue))

# a write to a block stage 2 maps is not at an address it does not
def ax.mskip.go(+b: Hv.W64, +v: Hv.W64, +m: List<&2, I.Cell>, +a: Hv.W64, +s2: Hv.Tree<Bool>, eb: {I.mapped(s2, b) == True{} : Bool}, ua: {I.mapped(s2, a) == False{} : Bool}, +q: Bool, eq: {I.W.is_eq(b, a) == q : Bool}) -> {Bool.pick(Hv.W64, q, v, I.mem_read(m, a)) == I.mem_read(m, a) : Hv.W64}:
  match q:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({v == I.mem_read(m, a) : Hv.W64}, L.false_true(Equal.trans(Bool, False{}, I.mapped(s2, a), True{},
        Equal.sym(Bool, I.mapped(s2, a), False{}, ua),
        (%L.w64_eq(b, a, eq) : {I.mapped(s2, _) == True{} : Bool}; eb))))

def ax.mskip(+b: Hv.W64, +v: Hv.W64, +m: List<&2, I.Cell>, +a: Hv.W64, +s2: Hv.Tree<Bool>, eb: {I.mapped(s2, b) == True{} : Bool}, ua: {I.mapped(s2, a) == False{} : Bool}) -> ax.Mem(I.mem_write(m, b, v), m, a):
  ax.mskip.go(b, v, m, a, s2, eb, ua, I.W.is_eq(b, a), {==})

# at EL1 a store may write only where stage 2 maps
def ax.wr_maps(+s2: Hv.Tree<Bool>, +b: Hv.W64, ok: {I.writable(1, s2, b) == True{} : Bool}) -> {I.mapped(s2, b) == True{} : Bool}:
  ok

# Entries
# -------

def ax.tfar(+sys3: List<&2, I.Sr>, +e: U32, far: Maybe<&2, Hv.W64>, e4: {U32.is_eq(I.FAR_EL2(), e) == False{} : Bool}, e5: {U32.is_eq(I.HPFAR_EL2(), e) == False{} : Bool}) -> ax.Sys(I.take.far(sys3, far), sys3, e):
  match far:
    case None{}:
      {==}
    case Some{+aa}:
      Equal.trans(Hv.W64,
        I.sys_read(I.sys_write(I.sys_write(sys3, I.FAR_EL2(), aa), I.HPFAR_EL2(), I.hpfar(aa)), e),
        I.sys_read(I.sys_write(sys3, I.FAR_EL2(), aa), e),
        I.sys_read(sys3, e),
        ax.skip(I.HPFAR_EL2(), I.hpfar(aa), I.sys_write(sys3, I.FAR_EL2(), aa), e, e5),
        ax.skip(I.FAR_EL2(), aa, sys3, e, e4))

def ax.take_sys(+sys: List<&2, I.Sr>, +e: U32, +ret: Hv.W64, +esr: U32, +sp: Hv.W64, +far: Maybe<&2, Hv.W64>, e1: {U32.is_eq(I.ELR_EL2(), e) == False{} : Bool}, e2: {U32.is_eq(I.SPSR_EL2(), e) == False{} : Bool}, e3: {U32.is_eq(I.ESR_EL2(), e) == False{} : Bool}, e4: {U32.is_eq(I.FAR_EL2(), e) == False{} : Bool}, e5: {U32.is_eq(I.HPFAR_EL2(), e) == False{} : Bool})
  -> ax.Sys(I.take.far(I.sys_write(I.sys_write(I.sys_write(sys, I.ELR_EL2(), ret), I.SPSR_EL2(), sp), I.ESR_EL2(), I.W.of(esr)), far), sys, e):
  +w1 = I.sys_write(sys, I.ELR_EL2(), ret)
  +w2 = I.sys_write(w1, I.SPSR_EL2(), sp)
  +w3 = I.sys_write(w2, I.ESR_EL2(), I.W.of(esr))
  Equal.trans(Hv.W64, I.sys_read(I.take.far(w3, far), e), I.sys_read(w3, e), I.sys_read(sys, e),
    ax.tfar(w3, e, far, e4, e5),
    Equal.trans(Hv.W64, I.sys_read(w3, e), I.sys_read(w2, e), I.sys_read(sys, e),
      ax.skip(I.ESR_EL2(), I.W.of(esr), w2, e, e3),
      Equal.trans(Hv.W64, I.sys_read(w2, e), I.sys_read(w1, e), I.sys_read(sys, e),
        ax.skip(I.SPSR_EL2(), sp, w1, e, e2),
        ax.skip(I.ELR_EL2(), ret, sys, e, e1))))

# the five an entry writes, from the one hypothesis
def ax.take(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +off: U32, +ret: Hv.W64, +esr: U32, +far: Maybe<&2, Hv.W64>, +vh: U32, +vl: U32, +en: {I.entry_reg(e) == False{} : Bool})
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.take.go(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, ret, esr, far, off, vh, vl)):
  +r1 = L.or_r(U32.is_eq(I.ELR_EL2(), e), Bool.or(U32.is_eq(I.SPSR_EL2(), e), Bool.or(U32.is_eq(I.ESR_EL2(), e), Bool.or(U32.is_eq(I.FAR_EL2(), e), U32.is_eq(I.HPFAR_EL2(), e)))), en)
  +r2 = L.or_r(U32.is_eq(I.SPSR_EL2(), e), Bool.or(U32.is_eq(I.ESR_EL2(), e), Bool.or(U32.is_eq(I.FAR_EL2(), e), U32.is_eq(I.HPFAR_EL2(), e))), r1)
  +r3 = L.or_r(U32.is_eq(I.ESR_EL2(), e), Bool.or(U32.is_eq(I.FAR_EL2(), e), U32.is_eq(I.HPFAR_EL2(), e)), r2)
  ax.wr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, x, I.W.add(Hv.W64{vh, vl}, I.W.of(off)), 2, 1, nzcv, 15,
    I.take.far(I.sys_write(I.sys_write(I.sys_write(sys, I.ELR_EL2(), ret), I.SPSR_EL2(), I.spsr_of(1, spsel, nzcv, daif)), I.ESR_EL2(), I.W.of(esr)), far), mem,
    ax.take_sys(sys, e, ret, esr, I.spsr_of(1, spsel, nzcv, daif), far,
      L.or_l(U32.is_eq(I.ELR_EL2(), e), Bool.or(U32.is_eq(I.SPSR_EL2(), e), Bool.or(U32.is_eq(I.ESR_EL2(), e), Bool.or(U32.is_eq(I.FAR_EL2(), e), U32.is_eq(I.HPFAR_EL2(), e)))), en),
      L.or_l(U32.is_eq(I.SPSR_EL2(), e), Bool.or(U32.is_eq(I.ESR_EL2(), e), Bool.or(U32.is_eq(I.FAR_EL2(), e), U32.is_eq(I.HPFAR_EL2(), e))), r1),
      L.or_l(U32.is_eq(I.ESR_EL2(), e), Bool.or(U32.is_eq(I.FAR_EL2(), e), U32.is_eq(I.HPFAR_EL2(), e)), r2),
      L.or_l(U32.is_eq(I.FAR_EL2(), e), U32.is_eq(I.HPFAR_EL2(), e), r3),
      L.or_r(U32.is_eq(I.FAR_EL2(), e), U32.is_eq(I.HPFAR_EL2(), e), r3)),
    {==})

# Writes to a register
# --------------------

def ax.wx(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +n: U32, v: Hv.W64) -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.wx(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, n, v)):
  match v:
    case Hv.W64{+hi, +lo}:
      ax.wr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, I.xw(x, n, Hv.W64{hi, lo}), I.W.add(pc, I.W.of(4)), 1, spsel, nzcv, daif, sys, mem, {==}, {==})

def ax.wx2(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +n1: U32, +n2: U32, v1: Hv.W64, v2: Hv.W64) -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.wx2(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, n1, n2, v1, v2)):
  match v1 v2:
    case Hv.W64{+h1, +l1} Hv.W64{+h2, +l2}:
      ax.wr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, I.xw(I.xw(x, n1, Hv.W64{h1, l1}), n2, Hv.W64{h2, l2}), I.W.add(pc, I.W.of(4)), 1, spsel, nzcv, daif, sys, mem, {==}, {==})

# a write to a register or, for 31, to the stack pointer, over a memory
# the caller may already have written

def ax.spw_go(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +x2: List<&2, Hv.W64>, +mem2: List<&2, I.Cell>, pm: ax.Mem(mem2, mem, a), +n: U32, +hi: U32, +lo: U32, +sp: Bool)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.spw.go(x2, pc, 1, spsel, nzcv, daif, sys, mem2, rom, s2, n, hi, lo, sp)):
  match sp:
    case True{}:
      ax.wr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, x2, I.W.add(pc, I.W.of(4)), 1, spsel, nzcv, daif,
        I.sys_write(sys, I.sp_enc(1, spsel), Hv.W64{hi, lo}), mem2,
        ax.sp_skip(spsel, Hv.W64{hi, lo}, sys, e, uo), pm)
    case False{}:
      ax.wr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, I.xw(x2, n, Hv.W64{hi, lo}), I.W.add(pc, I.W.of(4)), 1, spsel, nzcv, daif, sys, mem2, {==}, pm)

# Entries, again
# --------------

def ax.take_at(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +off: U32, +ret: Hv.W64, +esr: U32, +far: Maybe<&2, Hv.W64>, vbar: Hv.W64)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.take.at(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, ret, esr, far, off, vbar)):
  match vbar:
    case Hv.W64{+vh, +vl}:
      ax.take(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, off, ret, esr, far, vh, vl, en)

def ax.take_(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +off: U32, +ret: Hv.W64, +esr: U32, +far: Maybe<&2, Hv.W64>)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.take(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, off, ret, esr, far)):
  ax.take_at(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, off, ret, esr, far, I.sys_read(sys, I.VBAR_EL2()))

def ax.dabt(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +ipa: Hv.W64, +write: Bool, +single: Maybe<&2, U32>)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.dabt(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, ipa, write, single)):
  ax.take_(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, 1024, pc, I.syndrome(I.EC_DABT(), I.dabt_iss(single, write, I.fault_level(ipa))), Some{ipa})

# Arithmetic and branches
# -----------------------

def ax.do_addsub_fin(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +fl: Bool, +sp: Bool, +rd: U32, +r: Hv.W64, +nz: U32)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_addsub.fin(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, fl, sp, rd, r, nz)):
  match fl r:
    case True{} Hv.W64{+hi, +lo}:
      ax.wr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, I.xw(x, rd, Hv.W64{hi, lo}), I.W.add(pc, I.W.of(4)), 1, spsel, nz, daif, sys, mem, {==}, {==})
    case False{} rr:
      ax.spw_go(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, x, mem, {==}, rd, I.W.hi(rr), I.W.lo(rr), sp)

def ax.do_addsub(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +fl: Bool, +sp: Bool, +rd: U32, res: I.AddRes)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_addsub(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, fl, sp, rd, res)):
  match res:
    case I.AddRes{+r, +nz}:
      ax.do_addsub_fin(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, fl, sp, rd, r, nz)

def ax.do_jump_at(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, v: Hv.W64) -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_jump.at(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, v)):
  match v:
    case Hv.W64{+hi, +lo}:
      ax.wr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, x, Hv.W64{hi, lo}, 1, spsel, nzcv, daif, sys, mem, {==}, {==})

def ax.do_bcond(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +off: Hv.W64, +take: Bool) -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_bcond(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, off, take)):
  match take:
    case True{}:
      ax.do_jump_at(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, I.W.add(pc, off))
    case False{}:
      ax.wr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, x, I.W.add(pc, I.W.of(4)), 1, spsel, nzcv, daif, sys, mem, {==}, {==})

def ax.do_bl(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +off: Hv.W64) -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_bl(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, off)):
  ax.wr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, I.xw(x, 30, I.W.add(pc, I.W.of(4))), I.W.add(pc, off), 1, spsel, nzcv, daif, sys, mem, {==}, {==})

# System registers
# ----------------

def ax.do_mrs(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +k: U32, +ok: Bool) -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_mrs(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, k, ok)):
  match ok:
    case False{}:
      ax.stop(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, "mrs of an EL2 register at EL1")
    case True{}:
      ax.wx(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, I.sys_read(sys, k))

def ax.do_msr_go(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +k: U32, +hi: U32, +lo: U32, ke: {I.el1_ok(k) == True{} : Bool})
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_msr.go(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, k, hi, lo)):
  ax.wr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, x, I.W.add(pc, I.W.of(4)), 1, spsel, nzcv, daif, I.sys_write(sys, k, Hv.W64{hi, lo}), mem,
    ax.skip(k, Hv.W64{hi, lo}, sys, e,
      ax.not_own(k, e, L.or_true_r(U32.is_eq(I.SP_EL1(), k), I.el1_ok(k), ke), uo)), {==})

def ax.do_msr_at(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +k: U32, v: Hv.W64, ke: {I.el1_ok(k) == True{} : Bool})
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_msr.at(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, k, v)):
  match v:
    case Hv.W64{+hi, +lo}:
      ax.do_msr_go(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, k, hi, lo, ke)

def ax.do_msr(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +k: U32, +rt: U32, +ok: Bool, ke: {I.el1_ok(k) == ok : Bool})
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_msr(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, k, rt, ok)):
  match ok:
    case False{}:
      ax.stop(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, "msr of an EL2 register at EL1")
    case True{}:
      ax.do_msr_at(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, k, I.xr(x, rt), ke)

# Loads and stores
# ----------------

def ax.do_ldr_back(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +rn: U32, v: Hv.W64, b: Hv.W64)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_ldr.back(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, rn, v, b)):
  match v b:
    case Hv.W64{+h, +l} Hv.W64{+bh, +bl}:
      ax.spw_go(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, I.xw(x, rt, Hv.W64{h, l}), mem, {==}, rn, bh, bl, U32.is_eq(rn, 31))

def ax.do_ldr_wb(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +rn: U32, +off: Hv.W64, mode: I.Mode, v: Hv.W64)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_ldr.wb(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, rn, off, mode, v)):
  match mode:
    case I.Off{}:
      ax.wx(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, v)
    case I.Pre{}:
      ax.do_ldr_back(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rn, v, I.W.add(I.spr(x, sys, 1, spsel, rn), off))
    case I.Post{}:
      ax.do_ldr_back(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rn, v, I.W.add(I.spr(x, sys, 1, spsel, rn), off))

def ax.do_ldr(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +rn: U32, +off: Hv.W64, mode: I.Mode, +a2: Hv.W64, r: I.Acc)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_ldr(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, rn, off, mode, a2, r)):
  match r:
    case I.Got{v}:
      ax.do_ldr_wb(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rn, off, mode, v)
    case I.Abort{+ipa}:
      ax.dabt(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, ipa, False{}, Some{rt})
    case I.Odd{}:
      ax.stop(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, "an unaligned load")

def ax.at_ldr(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +rn: U32, +off: Hv.W64, mode: I.Mode, a2: Hv.W64)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.at_ldr(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, rn, off, mode, a2)):
  match a2:
    case Hv.W64{+ah, +al}:
      ax.do_ldr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rn, off, mode, Hv.W64{ah, al}, I.load(1, mem, rom, s2, Hv.W64{ah, al}))

def ax.do_str_back(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rn: U32, +off: Hv.W64, mode: I.Mode, +a2: Hv.W64, +v: Hv.W64, ok: {I.mapped(s2, a2) == True{} : Bool}, b: Hv.W64)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_str.back(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rn, off, mode, a2, v, b)):
  match b:
    case Hv.W64{+bh, +bl}:
      ax.spw_go(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, x, I.mem_write(mem, a2, v), ax.mskip(a2, v, mem, a, s2, ok, ua), rn, bh, bl, U32.is_eq(rn, 31))

def ax.do_str_at(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rn: U32, +off: Hv.W64, mode: I.Mode, +a2: Hv.W64, +v: Hv.W64, ok: {I.mapped(s2, a2) == True{} : Bool})
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_str.at(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rn, off, mode, a2, v)):
  match mode:
    case I.Off{}:
      ax.wr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, x, I.W.add(pc, I.W.of(4)), 1, spsel, nzcv, daif, sys, I.mem_write(mem, a2, v), {==},
        ax.mskip(a2, v, mem, a, s2, ok, ua))
    case I.Pre{}:
      ax.do_str_back(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rn, off, I.Pre{}, a2, v, ok, I.W.add(I.spr(x, sys, 1, spsel, rn), off))
    case I.Post{}:
      ax.do_str_back(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rn, off, I.Post{}, a2, v, ok, I.W.add(I.spr(x, sys, 1, spsel, rn), off))

def ax.do_str_wb(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rn: U32, +off: Hv.W64, mode: I.Mode, a2: Hv.W64, v: Hv.W64, ok: {I.mapped(s2, a2) == True{} : Bool})
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_str.wb(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rn, off, mode, a2, v)):
  match a2 v:
    case Hv.W64{+ah, +al} Hv.W64{+vh, +vl}:
      ax.do_str_at(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rn, off, mode, Hv.W64{ah, al}, Hv.W64{vh, vl}, ok)

def ax.do_str(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +rn: U32, +off: Hv.W64, mode: I.Mode, +a2: Hv.W64, +v: Hv.W64, +ok: Bool, +odd: Bool, eok: {I.writable(1, s2, a2) == ok : Bool})
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_str(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, rn, off, mode, a2, v, ok, odd)):
  match ok odd:
    case any False{}:
      ax.stop(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, "an unaligned store")
    case False{} True{}:
      ax.dabt(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, a2, True{}, Some{rt})
    case True{} True{}:
      ax.do_str_wb(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rn, off, mode, a2, v, eok)

def ax.at_str(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +rn: U32, +off: Hv.W64, mode: I.Mode, a2: Hv.W64)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.at_str(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, rn, off, mode, a2)):
  match a2:
    case Hv.W64{+ah, +al}:
      ax.do_str(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rn, off, mode, Hv.W64{ah, al}, I.xr(x, rt),
        I.writable(1, s2, Hv.W64{ah, al}), I.aligned(Hv.W64{ah, al}), {==})

# two writes, neither at an address stage 2 does not map
def ax.mskip2(+b1: Hv.W64, +v1: Hv.W64, +b2: Hv.W64, +v2: Hv.W64, +m: List<&2, I.Cell>, +a: Hv.W64, +s2: Hv.Tree<Bool>, e1: {I.mapped(s2, b1) == True{} : Bool}, e2: {I.mapped(s2, b2) == True{} : Bool}, +ua: {I.mapped(s2, a) == False{} : Bool})
  -> ax.Mem(I.mem_write(I.mem_write(m, b1, v1), b2, v2), m, a):
  Equal.trans(Hv.W64,
    I.mem_read(I.mem_write(I.mem_write(m, b1, v1), b2, v2), a),
    I.mem_read(I.mem_write(m, b1, v1), a), I.mem_read(m, a),
    ax.mskip(b2, v2, I.mem_write(m, b1, v1), a, s2, e2, ua),
    ax.mskip(b1, v1, m, a, s2, e1, ua))

# Pairs
# -----

def ax.do_ldp_back(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +rt2: U32, +rn: U32, v1: Hv.W64, v2: Hv.W64, b: Hv.W64)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_ldp.back(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, v1, v2, b)):
  match v1 v2 b:
    case Hv.W64{+h1, +l1} Hv.W64{+h2, +l2} Hv.W64{+bh, +bl}:
      ax.spw_go(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, I.xw(I.xw(x, rt, Hv.W64{h1, l1}), rt2, Hv.W64{h2, l2}), mem, {==}, rn, bh, bl, U32.is_eq(rn, 31))

def ax.do_ldp_wb(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +rt2: U32, +rn: U32, +off: Hv.W64, mode: I.Mode, v1: Hv.W64, v2: Hv.W64)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_ldp.wb(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, off, mode, v1, v2)):
  match mode:
    case I.Off{}:
      ax.wx2(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rt2, v1, v2)
    case I.Pre{}:
      ax.do_ldp_back(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rt2, rn, v1, v2, I.W.add(I.spr(x, sys, 1, spsel, rn), off))
    case I.Post{}:
      ax.do_ldp_back(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rt2, rn, v1, v2, I.W.add(I.spr(x, sys, 1, spsel, rn), off))

def ax.do_ldp(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +rt2: U32, +rn: U32, +off: Hv.W64, mode: I.Mode, +a2: Hv.W64, r1: I.Acc, r2: I.Acc)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_ldp(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, off, mode, a2, r1, r2)):
  match r1 r2:
    case I.Got{v1} I.Got{v2}:
      ax.do_ldp_wb(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rt2, rn, off, mode, v1, v2)
    case I.Abort{+ipa} any:
      ax.dabt(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, ipa, False{}, None{})
    case I.Got{v1} I.Abort{+ipa}:
      ax.dabt(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, ipa, False{}, None{})
    case I.Odd{} any:
      ax.stop(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, "an unaligned load")
    case I.Got{v1} I.Odd{}:
      ax.stop(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, "an unaligned load")

def ax.at_ldp(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +rt2: U32, +rn: U32, +off: Hv.W64, mode: I.Mode, a2: Hv.W64)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.at_ldp(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, off, mode, a2)):
  match a2:
    case Hv.W64{+ah, +al}:
      ax.do_ldp(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rt2, rn, off, mode, Hv.W64{ah, al},
        I.load(1, mem, rom, s2, Hv.W64{ah, al}), I.load(1, mem, rom, s2, I.W.add(Hv.W64{ah, al}, I.W.of(8))))

def ax.do_stp_back(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rn: U32, +off: Hv.W64, mode: I.Mode, +a2: Hv.W64, +v1: Hv.W64, +v2: Hv.W64, k1: {I.mapped(s2, a2) == True{} : Bool}, k2: {I.mapped(s2, I.W.add(a2, I.W.of(8))) == True{} : Bool}, b: Hv.W64)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_stp.back(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rn, off, mode, a2, v1, v2, b)):
  match b:
    case Hv.W64{+bh, +bl}:
      ax.spw_go(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, x, I.mem_write(I.mem_write(mem, a2, v1), I.W.add(a2, I.W.of(8)), v2),
        ax.mskip2(a2, v1, I.W.add(a2, I.W.of(8)), v2, mem, a, s2, k1, k2, ua), rn, bh, bl, U32.is_eq(rn, 31))

def ax.do_stp_at(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rn: U32, +off: Hv.W64, mode: I.Mode, +a2: Hv.W64, +v1: Hv.W64, +v2: Hv.W64, k1: {I.mapped(s2, a2) == True{} : Bool}, k2: {I.mapped(s2, I.W.add(a2, I.W.of(8))) == True{} : Bool})
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_stp.at(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rn, off, mode, a2, v1, v2)):
  match mode:
    case I.Off{}:
      ax.wr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, x, I.W.add(pc, I.W.of(4)), 1, spsel, nzcv, daif, sys, I.mem_write(I.mem_write(mem, a2, v1), I.W.add(a2, I.W.of(8)), v2), {==},
        ax.mskip2(a2, v1, I.W.add(a2, I.W.of(8)), v2, mem, a, s2, k1, k2, ua))
    case I.Pre{}:
      ax.do_stp_back(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rn, off, I.Pre{}, a2, v1, v2, k1, k2, I.W.add(I.spr(x, sys, 1, spsel, rn), off))
    case I.Post{}:
      ax.do_stp_back(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rn, off, I.Post{}, a2, v1, v2, k1, k2, I.W.add(I.spr(x, sys, 1, spsel, rn), off))

def ax.do_stp_wb(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +rt2: U32, +rn: U32, +off: Hv.W64, mode: I.Mode, a2: Hv.W64, v1: Hv.W64, v2: Hv.W64, k1: {I.mapped(s2, a2) == True{} : Bool}, k2: {I.mapped(s2, I.W.add(a2, I.W.of(8))) == True{} : Bool})
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_stp.wb(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, off, mode, a2, v1, v2)):
  match a2 v1 v2:
    case Hv.W64{+ah, +al} Hv.W64{+h1, +l1} Hv.W64{+h2, +l2}:
      ax.do_stp_at(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rn, off, mode, Hv.W64{ah, al}, Hv.W64{h1, l1}, Hv.W64{h2, l2}, k1, k2)

def ax.do_stp(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +rt2: U32, +rn: U32, +off: Hv.W64, mode: I.Mode, +a2: Hv.W64, +v1: Hv.W64, +v2: Hv.W64, +ok: Bool, +odd: Bool, +eok: {Bool.and(I.writable(1, s2, a2), I.writable(1, s2, I.W.add(a2, I.W.of(8)))) == ok : Bool})
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.do_stp(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, off, mode, a2, v1, v2, ok, odd)):
  match ok odd:
    case any False{}:
      ax.stop(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, "an unaligned store")
    case False{} True{}:
      ax.dabt(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, a2, True{}, None{})
    case True{} True{}:
      ax.do_stp_wb(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rt2, rn, off, mode, a2, v1, v2,
        L.and_l(I.writable(1, s2, a2), I.writable(1, s2, I.W.add(a2, I.W.of(8))), eok),
        L.and_r(I.writable(1, s2, a2), I.writable(1, s2, I.W.add(a2, I.W.of(8))), eok))

def ax.at_stp(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, +rt: U32, +rt2: U32, +rn: U32, +off: Hv.W64, mode: I.Mode, a2: Hv.W64)
  -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.at_stp(x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, off, mode, a2)):
  match a2:
    case Hv.W64{+ah, +al}:
      ax.do_stp(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rt2, rn, off, mode, Hv.W64{ah, al}, I.xr(x, rt), I.xr(x, rt2),
        Bool.and(I.writable(1, s2, Hv.W64{ah, al}), I.writable(1, s2, I.W.add(Hv.W64{ah, al}, I.W.of(8)))), I.aligned(Hv.W64{ah, al}), {==})

# The step
# --------

def ax.exec(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, i: I.Instr) -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.exec(i, x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2)):
  match i:
    case I.Nop{}:
      ax.wr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, x, I.W.add(pc, I.W.of(4)), 1, spsel, nzcv, daif, sys, mem, {==}, {==})
    case I.Wfi{}:
      ax.take_(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, 1024, pc, I.syndrome(I.EC_WFI(), 31457280), None{})
    case I.Eret{}:
      ax.stop(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, "eret at EL1")
    case I.Ret{+rn}:
      ax.do_jump_at(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, I.xr(x, rn))
    case I.Hvc{+imm}:
      ax.take_(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, 1024, I.W.add(pc, I.W.of(4)), I.syndrome(I.EC_HVC(), imm), None{})
    case I.Mrs{+k, +rt}:
      ax.do_mrs(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, k, Bool.or(U32.is_eq(1, 2), I.el1_ok(k)))
    case I.Msr{+k, +rt}:
      ax.do_msr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, k, rt, Bool.or(U32.is_eq(1, 2), I.el1_ok(k)), {==})
    case I.B{+off}:
      ax.do_jump_at(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, I.W.add(pc, off))
    case I.Bl{+off}:
      ax.do_bl(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, off)
    case I.BCond{+cond, +off}:
      ax.do_bcond(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, off, I.cond_holds(cond, nzcv))
    case I.Movz{sf, +rd, +imm}:
      ax.wx(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rd, imm)
    case I.AddImm{+sf, +sub, +fl, +rd, +rn, +imm}:
      ax.do_addsub(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, fl, U32.is_eq(rd, 31), rd, I.addsub(sf, sub, I.spr(x, sys, 1, spsel, rn), imm))
    case I.AddReg{+sf, +sub, +fl, +rd, +rn, +rm}:
      ax.do_addsub(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, fl, False{}, rd, I.addsub(sf, sub, I.xr(x, rn), I.xr(x, rm)))
    case I.OrrReg{+sf, +rd, +rn, +rm}:
      ax.wx(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rd, Bool.pick(Hv.W64, sf, I.W.or(I.xr(x, rn), I.xr(x, rm)), I.W.w(I.W.or(I.xr(x, rn), I.xr(x, rm)))))
    case I.AndReg{+sf, +rd, +rn, +rm}:
      ax.wx(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rd, Bool.pick(Hv.W64, sf, I.W.and(I.xr(x, rn), I.xr(x, rm)), I.W.w(I.W.and(I.xr(x, rn), I.xr(x, rm)))))
    case I.Movk{+sf, +rd, +hw, +imm}:
      ax.wx(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rd, Bool.pick(Hv.W64, sf, I.movk_at(I.xr(x, rd), hw, imm), I.W.w(I.movk_at(I.W.w(I.xr(x, rd)), hw, imm))))
    case I.Lsl{+sf, +rd, +rn, +sh}:
      ax.wx(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rd, Bool.pick(Hv.W64, sf, I.W.shl_by(I.xr(x, rn), sh), I.W.w(I.W.shl_by(I.W.w(I.xr(x, rn)), sh))))
    case I.Lsr{+sf, +rd, +rn, +sh}:
      ax.wx(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rd, Bool.pick(Hv.W64, sf, I.W.shr_by(I.xr(x, rn), sh), I.W.w(I.W.shr_by(I.W.w(I.xr(x, rn)), sh))))
    case I.Ldr{+rt, +rn, +off, +mode}:
      ax.at_ldr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rn, off, mode, I.ea(I.spr(x, sys, 1, spsel, rn), off, mode))
    case I.Str{+rt, +rn, +off, +mode}:
      ax.at_str(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rn, off, mode, I.ea(I.spr(x, sys, 1, spsel, rn), off, mode))
    case I.LdrLit{+rt, +off}:
      ax.at_ldr(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, 31, I.W.of(0), I.Off{}, I.W.add(pc, off))
    case I.Ldp{+rt, +rt2, +rn, +off, +mode}:
      ax.at_ldp(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rt2, rn, off, mode, I.ea(I.spr(x, sys, 1, spsel, rn), off, mode))
    case I.Stp{+rt, +rt2, +rn, +off, +mode}:
      ax.at_stp(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, rt, rt2, rn, off, mode, I.ea(I.spr(x, sys, 1, spsel, rn), off, mode))
    case I.Undef{w}:
      ax.stop(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, "an instruction the model lacks: " ++ I.U32.hex(w))

def ax.step_at(+a: Hv.W64, +e: U32, +x: List<&2, Hv.W64>, +pc: Hv.W64, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +rom: I.Rom, +s2: Hv.Tree<Bool>, +ua: {I.mapped(s2, a) == False{} : Bool}, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool}, w: Maybe<&2, U32>) -> ax.G(a, e, ax.S(x, pc, spsel, nzcv, daif, sys, mem, rom, s2), I.step.at(w, x, pc, 1, spsel, nzcv, daif, sys, mem, rom, s2)):
  match w:
    case None{}:
      ax.take_(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, 1024, pc, I.syndrome(I.EC_IABT(), U32.or(4, I.fault_level(pc))), Some{pc})
    case Some{+i}:
      ax.exec(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua, uo, en, I.decode(i))

def ax.guest_step(s: I.State, el1: {I.State.el(s) == 1 : U32}, +a: Hv.W64, +ua2: {I.mapped(I.State.s2(s), a) == False{} : Bool}, +e: U32, +uo: {I.own_reg(e) == False{} : Bool}, +en: {I.entry_reg(e) == False{} : Bool})
  -> ax.G(a, e, s, I.step(s)):
  match s:
    case I.State{I.Cpu{x, +pc, +el, +spsel, +nzcv, +daif, sys}, +mem, +rom, +s2}:
      %Equal.sym(U32, el, 1, el1) : ax.G(a, e, I.State{I.Cpu{x, pc, _, spsel, nzcv, daif, sys}, mem, rom, s2}, I.step(I.State{I.Cpu{x, pc, _, spsel, nzcv, daif, sys}, mem, rom, s2}))
      ax.step_at(a, e, x, pc, spsel, nzcv, daif, sys, mem, rom, s2, ua2, uo, en, I.fetch(1, pc, mem, rom, s2))

# the three laws are the three parts of ax.G; the hypotheses the other
# parts want are met by an address outside every guest's blocks and by
# VBAR_EL2, which is neither the guest's register nor one an entry writes

def Laws.guest_step_memory(s, el1, x, ux):
  Pair.fst(ax.Mem(I.State.mem(I.Out.s(I.step(s))), I.State.mem(s), x),
    ax.Sys(I.State.sys(I.Out.s(I.step(s))), I.State.sys(s), I.VBAR_EL2()) & {I.State.s2(I.Out.s(I.step(s))) == I.State.s2(s) : Hv.Tree<Bool>},
    ax.guest_step(s, el1, x, ux, I.VBAR_EL2(), {==}, {==}))

def Laws.guest_step_registers(s, el1, e, uo, en):
  Pair.fst(ax.Sys(I.State.sys(I.Out.s(I.step(s))), I.State.sys(s), e),
    {I.State.s2(I.Out.s(I.step(s))) == I.State.s2(s) : Hv.Tree<Bool>},
    Pair.snd(ax.Mem(I.State.mem(I.Out.s(I.step(s))), I.State.mem(s), Hv.W64{1, 0}),
      ax.Sys(I.State.sys(I.Out.s(I.step(s))), I.State.sys(s), e) & {I.State.s2(I.Out.s(I.step(s))) == I.State.s2(s) : Hv.Tree<Bool>},
      ax.guest_step(s, el1, Hv.W64{1, 0}, {==}, e, uo, en)))

def Laws.guest_step_stage2(s, el1):
  Pair.snd(ax.Sys(I.State.sys(I.Out.s(I.step(s))), I.State.sys(s), I.VBAR_EL2()),
    {I.State.s2(I.Out.s(I.step(s))) == I.State.s2(s) : Hv.Tree<Bool>},
    Pair.snd(ax.Mem(I.State.mem(I.Out.s(I.step(s))), I.State.mem(s), Hv.W64{1, 0}),
      ax.Sys(I.State.sys(I.Out.s(I.step(s))), I.State.sys(s), I.VBAR_EL2()) & {I.State.s2(I.Out.s(I.step(s))) == I.State.s2(s) : Hv.Tree<Bool>},
      ax.guest_step(s, el1, Hv.W64{1, 0}, {==}, I.VBAR_EL2(), {==}, {==})))

# Record, the other way
# ---------------------
# decode_record answers Some only for a record it could itself have
# written: it re-encodes what it read and refuses anything else. So a
# machine it answers is well formed and the words are that machine's
# encoding, and a corrupt persist region cannot become a machine.

def MaybeT(a, -A: Kind(a), m: Maybe<a, A>) -> Data:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(a, -A: Kind(a), -x: A, e: {None{} == Some{x} : Maybe<a, A>}) -> Empty:
  %e : MaybeT(a, A, _)
  Unit{}

def some_eq(a, -A: Kind(a), -x: A, -y: A, e: {Some{x} == Some{y} : Maybe<a, A>}) -> {x == y : A}:
  Equal.cong(Maybe<a, A>, A, mb => Maybe.default(a, A, mb, y), Some{x}, Some{y}, e)

def Closed(+ws: List<&2, U32>, -k2: Hv.Kernel, -m: Hv.Machine) -> Type:
  Hv.Machine.ok(m) & {ws == Hv.encode(k2, m) : List<&2, U32>}

# the decoder's four checks, taken apart
def Checks(+ps: Hv.Tree<Hv.Owner>, +cur: U32, +ws: List<&2, U32>, +pw: List<&2, U32>) -> Data:
  Hv.Both<{Hv.Owners.okb(ps) == True{} : Bool}, Hv.Both<{Hv.Tree.shapeb(ps, Hv.page_depth()) == True{} : Bool},
    Hv.Both<{U32.is_lt(cur, 4) == True{} : Bool}, {Hv.U32.list_eq(ws, pw) == True{} : Bool}>>>

def checks(+ps: Hv.Tree<Hv.Owner>, +cur: U32, +ws: List<&2, U32>, +v0: Hv.VCpu, +v1: Hv.VCpu, +v2: Hv.VCpu, +v3: Hv.VCpu, +k: Hv.Kernel, +e: {Bool.and(Bool.and(Hv.Owners.okb(ps), Hv.Tree.shapeb(ps, Hv.page_depth())), Bool.and(U32.is_lt(cur, 4), Hv.U32.list_eq(ws, Hv.encode_parts(k, ps, v0, v1, v2, v3, cur)))) == True{} : Bool}) -> Checks(ps, cur, ws, Hv.encode_parts(k, ps, v0, v1, v2, v3, cur)):
  Hv.Both{L.and_l(Hv.Owners.okb(ps), Hv.Tree.shapeb(ps, Hv.page_depth()), L.and_l(Bool.and(Hv.Owners.okb(ps), Hv.Tree.shapeb(ps, Hv.page_depth())), Bool.and(U32.is_lt(cur, 4), Hv.U32.list_eq(ws, Hv.encode_parts(k, ps, v0, v1, v2, v3, cur))), e)),
    Hv.Both{L.and_r(Hv.Owners.okb(ps), Hv.Tree.shapeb(ps, Hv.page_depth()), L.and_l(Bool.and(Hv.Owners.okb(ps), Hv.Tree.shapeb(ps, Hv.page_depth())), Bool.and(U32.is_lt(cur, 4), Hv.U32.list_eq(ws, Hv.encode_parts(k, ps, v0, v1, v2, v3, cur))), e)),
      Hv.Both{L.and_l(U32.is_lt(cur, 4), Hv.U32.list_eq(ws, Hv.encode_parts(k, ps, v0, v1, v2, v3, cur)), L.and_r(Bool.and(Hv.Owners.okb(ps), Hv.Tree.shapeb(ps, Hv.page_depth())), Bool.and(U32.is_lt(cur, 4), Hv.U32.list_eq(ws, Hv.encode_parts(k, ps, v0, v1, v2, v3, cur))), e)),
        L.and_r(U32.is_lt(cur, 4), Hv.U32.list_eq(ws, Hv.encode_parts(k, ps, v0, v1, v2, v3, cur)), L.and_r(Bool.and(Hv.Owners.okb(ps), Hv.Tree.shapeb(ps, Hv.page_depth())), Bool.and(U32.is_lt(cur, 4), Hv.U32.list_eq(ws, Hv.encode_parts(k, ps, v0, v1, v2, v3, cur))), e))}}}

# the machine the decoder built, once its checks have held
def encode_parts_eq(k: Hv.Kernel, +ps: Hv.Tree<Hv.Owner>, +v0: Hv.VCpu, +v1: Hv.VCpu, +v2: Hv.VCpu, +v3: Hv.VCpu, +cur: U32) -> {Hv.encode_parts(k, ps, v0, v1, v2, v3, cur) == Hv.encode(k, Hv.Machine{ps, Hv.four(v0, v1, v2, v3), cur}) : List<&2, U32>}:
  match k:
    case Hv.Kernel{n, next, slice}:
      {==}

def closed.at(+k: Hv.Kernel, +cur: U32, +ps: Hv.Tree<Hv.Owner>, +ws: List<&2, U32>, +v0: Hv.VCpu, +v1: Hv.VCpu, +v2: Hv.VCpu, +v3: Hv.VCpu, c: Checks(ps, cur, ws, Hv.encode_parts(k, ps, v0, v1, v2, v3, cur)))
  -> Closed(ws, k, Hv.Machine{ps, Hv.four(v0, v1, v2, v3), cur}):
  Hv.Both{okb, Hv.Both{shb, Hv.Both{slb, leb}}} = c
  (Hv.Both{shapeb(ps, Hv.page_depth(), shb),
    Hv.Both{owners_okb(ps, okb),
      Hv.Both{Hv.Both{Hv.Both{Unit{}, Unit{}}, Hv.Both{Unit{}, Unit{}}}, slb}}},
    (%encode_parts_eq(k, ps, v0, v1, v2, v3, cur) : {ws == _ : List<&2, U32>}; list_eq_sound(ws, Hv.encode_parts(k, ps, v0, v1, v2, v3, cur), leb)))

# the last step: the check held
def closed.pair(+k: Hv.Kernel, +cur: U32, +ps: Hv.Tree<Hv.Owner>, +ws: List<&2, U32>, +v0: Hv.VCpu, +v1: Hv.VCpu, +v2: Hv.VCpu, +v3: Hv.VCpu, -k2: Hv.Kernel, -m: Hv.Machine, +eo: {Bool.and(Bool.and(Hv.Owners.okb(ps), Hv.Tree.shapeb(ps, Hv.page_depth())), Bool.and(U32.is_lt(cur, 4), Hv.U32.list_eq(ws, Hv.encode_parts(k, ps, v0, v1, v2, v3, cur)))) == True{} : Bool}, +e: {(k, Hv.Machine{ps, Hv.four(v0, v1, v2, v3), cur}) == (k2, m) : (Hv.Kernel & Hv.Machine)})
  -> Closed(ws, k2, m):
  %Equal.cong((Hv.Kernel & Hv.Machine), Hv.Kernel, p => Pair.fst(Hv.Kernel, Hv.Machine, p), (k, Hv.Machine{ps, Hv.four(v0, v1, v2, v3), cur}), (k2, m), e) : Closed(ws, _, m)
  %Equal.cong((Hv.Kernel & Hv.Machine), Hv.Machine, p => Pair.snd(Hv.Kernel, Hv.Machine, p), (k, Hv.Machine{ps, Hv.four(v0, v1, v2, v3), cur}), (k2, m), e) : Closed(ws, k, _)
  closed.at(k, cur, ps, ws, v0, v1, v2, v3, checks(ps, cur, ws, v0, v1, v2, v3, k, eo))

def closed.take(+k: Hv.Kernel, +cur: U32, +ps: Hv.Tree<Hv.Owner>, +ws: List<&2, U32>, +v0: Hv.VCpu, +v1: Hv.VCpu, +v2: Hv.VCpu, +v3: Hv.VCpu, -k2: Hv.Kernel, -m: Hv.Machine, +ok: Bool, +eo: {Bool.and(Bool.and(Hv.Owners.okb(ps), Hv.Tree.shapeb(ps, Hv.page_depth())), Bool.and(U32.is_lt(cur, 4), Hv.U32.list_eq(ws, Hv.encode_parts(k, ps, v0, v1, v2, v3, cur)))) == ok : Bool}, got: {Hv.decode_record.take(k, cur, ps, v0, v1, v2, v3, ok) == Some{(k2, m)} : Maybe<(Hv.Kernel & Hv.Machine)>})
  -> Closed(ws, k2, m):
  match ok:
    case False{}:
      Empty.absurd(Closed(ws, k2, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k2, m), got))
    case True{}:
      closed.pair(k, cur, ps, ws, v0, v1, v2, v3, k2, m, eo,
        some_eq(&1, (Hv.Kernel & Hv.Machine), (k, Hv.Machine{ps, Hv.four(v0, v1, v2, v3), cur}), (k2, m), got))

def closed.v3(+k: Hv.Kernel, +cur: U32, +ps: Hv.Tree<Hv.Owner>, +ws: List<&2, U32>, +v0: Hv.VCpu, +v1: Hv.VCpu, +v2: Hv.VCpu, -k2: Hv.Kernel, -m: Hv.Machine, r: Maybe<(Hv.VCpu & List<&2, U32>)>, got: {Hv.decode_record.v3(k, cur, ps, ws, v0, v1, v2, r) == Some{(k2, m)} : Maybe<(Hv.Kernel & Hv.Machine)>})
  -> Closed(ws, k2, m):
  match r:
    case None{}:
      Empty.absurd(Closed(ws, k2, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k2, m), got))
    case Some{(+v3, Nil{})}:
      closed.take(k, cur, ps, ws, v0, v1, v2, v3, k2, m, Bool.and(Bool.and(Hv.Owners.okb(ps), Hv.Tree.shapeb(ps, Hv.page_depth())), Bool.and(U32.is_lt(cur, 4), Hv.U32.list_eq(ws, Hv.encode_parts(k, ps, v0, v1, v2, v3, cur)))), {==}, got)
    case Some{(v3, w <> more)}:
      Empty.absurd(Closed(ws, k2, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k2, m), got))

def closed.v2(+k: Hv.Kernel, +cur: U32, +ps: Hv.Tree<Hv.Owner>, +ws: List<&2, U32>, +v0: Hv.VCpu, +v1: Hv.VCpu, -k2: Hv.Kernel, -m: Hv.Machine, r: Maybe<(Hv.VCpu & List<&2, U32>)>, got: {Hv.decode_record.v2(k, cur, ps, ws, v0, v1, r) == Some{(k2, m)} : Maybe<(Hv.Kernel & Hv.Machine)>})
  -> Closed(ws, k2, m):
  match r:
    case None{}:
      Empty.absurd(Closed(ws, k2, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k2, m), got))
    case Some{(+v2, +rest)}:
      closed.v3(k, cur, ps, ws, v0, v1, v2, k2, m, Hv.vcpu_take(rest), got)

def closed.v1(+k: Hv.Kernel, +cur: U32, +ps: Hv.Tree<Hv.Owner>, +ws: List<&2, U32>, +v0: Hv.VCpu, -k2: Hv.Kernel, -m: Hv.Machine, r: Maybe<(Hv.VCpu & List<&2, U32>)>, got: {Hv.decode_record.v1(k, cur, ps, ws, v0, r) == Some{(k2, m)} : Maybe<(Hv.Kernel & Hv.Machine)>})
  -> Closed(ws, k2, m):
  match r:
    case None{}:
      Empty.absurd(Closed(ws, k2, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k2, m), got))
    case Some{(+v1, +rest)}:
      closed.v2(k, cur, ps, ws, v0, v1, k2, m, Hv.vcpu_take(rest), got)

def closed.vcs(+k: Hv.Kernel, +cur: U32, +ps: Hv.Tree<Hv.Owner>, +ws: List<&2, U32>, -k2: Hv.Kernel, -m: Hv.Machine, r: Maybe<(Hv.VCpu & List<&2, U32>)>, got: {Hv.decode_record.vcs(k, cur, ps, ws, r) == Some{(k2, m)} : Maybe<(Hv.Kernel & Hv.Machine)>})
  -> Closed(ws, k2, m):
  match r:
    case None{}:
      Empty.absurd(Closed(ws, k2, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k2, m), got))
    case Some{(+v0, +rest)}:
      closed.v1(k, cur, ps, ws, v0, k2, m, Hv.vcpu_take(rest), got)

def closed.fin(+k: Hv.Kernel, +cur: U32, +ws: List<&2, U32>, -k2: Hv.Kernel, -m: Hv.Machine, r: Maybe<(Hv.Tree<Hv.Owner> & List<&2, U32>)>, got: {Hv.decode_record.fin(k, cur, ws, r) == Some{(k2, m)} : Maybe<(Hv.Kernel & Hv.Machine)>})
  -> Closed(ws, k2, m):
  match r:
    case None{}:
      Empty.absurd(Closed(ws, k2, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k2, m), got))
    case Some{(+ps, +rest)}:
      closed.vcs(k, cur, ps, ws, k2, m, Hv.vcpu_take(rest), got)

def closed.sized(+k: Hv.Kernel, +cur: U32, +ws: List<&2, U32>, +rest: List<&2, U32>, -k2: Hv.Kernel, -m: Hv.Machine, ok: Bool, got: {Hv.decode_record.sized(k, cur, ok, ws, rest) == Some{(k2, m)} : Maybe<(Hv.Kernel & Hv.Machine)>})
  -> Closed(ws, k2, m):
  match ok:
    case False{}:
      Empty.absurd(Closed(ws, k2, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k2, m), got))
    case True{}:
      closed.fin(k, cur, ws, k2, m, Hv.owners_take(Hv.page_depth(), rest), got)

def Laws.record_closed(ws, k, m, got):
  match ws:
    case Nil{}:
      Empty.absurd(Closed(ws, k, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k, m), got))
    case w0 <> Nil{}:
      Empty.absurd(Closed(ws, k, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k, m), got))
    case w0 <> w1 <> Nil{}:
      Empty.absurd(Closed(ws, k, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k, m), got))
    case w0 <> w1 <> w2 <> Nil{}:
      Empty.absurd(Closed(ws, k, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k, m), got))
    case w0 <> w1 <> w2 <> w3 <> Nil{}:
      Empty.absurd(Closed(ws, k, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k, m), got))
    case w0 <> w1 <> w2 <> w3 <> w4 <> Nil{}:
      Empty.absurd(Closed(ws, k, m), none_some(&1, (Hv.Kernel & Hv.Machine), (k, m), got))
    case +n <> +next <> +slice <> +cur <> +np <> +nv <> +rest:
      closed.sized(Hv.Kernel{n, next, slice}, cur, n <> next <> slice <> cur <> np <> nv <> rest, rest, k, m,
        Bool.and(U32.is_eq(np, 64), U32.is_eq(nv, 4)), got)

# Boot
# ----
# a guest the boot machine never made owns no block, so its mask is
# empty and disjoint from itself. The owners of a boot machine of n
# guests are all below n, and a guest at or past n is none of them.

# a slot below n is not one at or past n: if the two were equal, the one
# below n would be at or past it
def ne_of_ge.go(+g: U32, +h: U32, +n: U32, +ltg: {U32.is_lt(g, n) == True{} : Bool}, +ge: {U32.is_lt(h, n) == False{} : Bool}, +b: Bool, eb: {U32.is_eq(g, h) == b : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, U32.is_lt(h, n), False{},
        Equal.sym(Bool, U32.is_lt(h, n), True{}, Equal.trans(Bool, U32.is_lt(h, n), U32.is_lt(g, n), True{},
          Equal.cong(U32, Bool, w => U32.is_lt(w, n), h, g, Equal.sym(U32, g, h, L.u32_eq(g, h, eb))), ltg)), ge)))

def ne_of_ge(+g: U32, +h: U32, +n: U32, +ltg: {U32.is_lt(g, n) == True{} : Bool}, +ge: {U32.is_lt(h, n) == False{} : Bool}) -> {U32.is_eq(g, h) == False{} : Bool}:
  ne_of_ge.go(g, h, n, ltg, ge, U32.is_eq(g, h), {==})

# every owner of the tree names a guest below n
def OwnerBelow(o: Hv.Owner, +n: U32) -> Data:
  match o:
    case Hv.Free{}:
      Unit
    case Hv.Hyp{}:
      Unit
    case Hv.Of{g}:
      {U32.is_lt(g, n) == True{} : Bool}

def OwnedBelow(t: Hv.Tree<Hv.Owner>, +n: U32) -> Data:
  match t:
    case Hv.Leaf{o}:
      OwnerBelow(o, n)
    case Hv.Node{lo, hi}:
      Hv.Both<OwnedBelow(lo, n), OwnedBelow(hi, n)>

def owner_below_b(o: Hv.Owner, +n: U32) -> Bool:
  match o:
    case Hv.Free{}:
      True{}
    case Hv.Hyp{}:
      True{}
    case Hv.Of{g}:
      U32.is_lt(g, n)

def owned_below_b(t: Hv.Tree<Hv.Owner>, +n: U32) -> Bool:
  match t:
    case Hv.Leaf{o}:
      owner_below_b(o, n)
    case Hv.Node{lo, hi}:
      Bool.and(owned_below_b(lo, n), owned_below_b(hi, n))

def owner_below(o: Hv.Owner, +n: U32, e: {owner_below_b(o, n) == True{} : Bool}) -> OwnerBelow(o, n):
  match o:
    case Hv.Free{}:
      Unit{}
    case Hv.Hyp{}:
      Unit{}
    case Hv.Of{g}:
      e

def owned_below(t: Hv.Tree<Hv.Owner>, +n: U32, +e: {owned_below_b(t, n) == True{} : Bool}) -> OwnedBelow(t, n):
  match t:
    case Hv.Leaf{o}:
      owner_below(o, n, e)
    case Hv.Node{+lo, +hi}:
      Hv.Both{owned_below(lo, n, L.and_l(owned_below_b(lo, n), owned_below_b(hi, n), e)),
        owned_below(hi, n, L.and_r(owned_below_b(lo, n), owned_below_b(hi, n), e))}

# so no block of it is the guest's
def NotOwned(t: Hv.Tree<Hv.Owner>, +h: U32) -> Data:
  match t:
    case Hv.Leaf{o}:
      {Hv.Owner.is_of(o, h) == False{} : Bool}
    case Hv.Node{lo, hi}:
      Hv.Both<NotOwned(lo, h), NotOwned(hi, h)>

def not_owner(o: Hv.Owner, +h: U32, +n: U32, ob: OwnerBelow(o, n), +ge: {U32.is_lt(h, n) == False{} : Bool}) -> {Hv.Owner.is_of(o, h) == False{} : Bool}:
  match o:
    case Hv.Free{}:
      {==}
    case Hv.Hyp{}:
      {==}
    case Hv.Of{+g}:
      ne_of_ge(g, h, n, ob, ge)

def not_owned(t: Hv.Tree<Hv.Owner>, +h: U32, +n: U32, ob: OwnedBelow(t, n), +ge: {U32.is_lt(h, n) == False{} : Bool}) -> NotOwned(t, h):
  match t:
    case Hv.Leaf{o}:
      not_owner(o, h, n, ob, ge)
    case Hv.Node{lo, hi}:
      Hv.Both{obl, obh} = ob
      Hv.Both{not_owned(lo, h, n, obl, ge), not_owned(hi, h, n, obh, ge)}

# an empty mask is disjoint from itself
def mask_none(t: Hv.Tree<Hv.Owner>, +h: U32, no: NotOwned(t, h)) -> {Hv.disjoint(Hv.mask(t, h), Hv.mask(t, h)) == True{} : Bool}:
  match t:
    case Hv.Leaf{+o}:
      %Equal.sym(Bool, Hv.Owner.is_of(o, h), False{}, no) : {Bool.not(Bool.and(_, _)) == True{} : Bool}
      {==}
    case Hv.Node{lo, hi}:
      Hv.Both{nl, nh} = no
      %Equal.sym(Bool, Hv.disjoint(Hv.mask(lo, h), Hv.mask(lo, h)), True{}, mask_none(lo, h, nl)) : {Bool.and(_, Hv.disjoint(Hv.mask(hi, h), Hv.mask(hi, h))) == True{} : Bool}
      mask_none(hi, h, nh)

def boot_isolates.go(-n: U32, +h: U32, v: L.Lt4<n>, +ge: {U32.is_lt(h, n) == False{} : Bool})
  -> Hv.Machine.ok(Hv.boot_machine(n)) & {Hv.disjoint(Hv.mask(Hv.Machine.pages(Hv.boot_machine(n)), h), Hv.mask(Hv.Machine.pages(Hv.boot_machine(n)), h)) == True{} : Bool}:
  match v:
    case L.K0{+e}:
      %e : Hv.Machine.ok(Hv.boot_machine(_)) & {Hv.disjoint(Hv.mask(Hv.Machine.pages(Hv.boot_machine(_)), h), Hv.mask(Hv.Machine.pages(Hv.boot_machine(_)), h)) == True{} : Bool}
      (boot_ok.of(0, {==}, {==}),
        mask_none(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(0)), h, not_owned(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(0)), h, 0,
          owned_below(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(0)), 0, {==}),
          (%Equal.sym(U32, 0, n, e) : {U32.is_lt(h, _) == False{} : Bool}; ge))))
    case L.K1{+e}:
      %e : Hv.Machine.ok(Hv.boot_machine(_)) & {Hv.disjoint(Hv.mask(Hv.Machine.pages(Hv.boot_machine(_)), h), Hv.mask(Hv.Machine.pages(Hv.boot_machine(_)), h)) == True{} : Bool}
      (boot_ok.of(1, {==}, {==}),
        mask_none(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(1)), h, not_owned(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(1)), h, 1,
          owned_below(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(1)), 1, {==}),
          (%Equal.sym(U32, 1, n, e) : {U32.is_lt(h, _) == False{} : Bool}; ge))))
    case L.K2{+e}:
      %e : Hv.Machine.ok(Hv.boot_machine(_)) & {Hv.disjoint(Hv.mask(Hv.Machine.pages(Hv.boot_machine(_)), h), Hv.mask(Hv.Machine.pages(Hv.boot_machine(_)), h)) == True{} : Bool}
      (boot_ok.of(2, {==}, {==}),
        mask_none(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(2)), h, not_owned(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(2)), h, 2,
          owned_below(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(2)), 2, {==}),
          (%Equal.sym(U32, 2, n, e) : {U32.is_lt(h, _) == False{} : Bool}; ge))))
    case L.K3{+e}:
      %e : Hv.Machine.ok(Hv.boot_machine(_)) & {Hv.disjoint(Hv.mask(Hv.Machine.pages(Hv.boot_machine(_)), h), Hv.mask(Hv.Machine.pages(Hv.boot_machine(_)), h)) == True{} : Bool}
      (boot_ok.of(3, {==}, {==}),
        mask_none(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(3)), h, not_owned(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(3)), h, 3,
          owned_below(Hv.blocks(Hv.page_depth(), 0n, U32.to_nat(3)), 3, {==}),
          (%Equal.sym(U32, 3, n, e) : {U32.is_lt(h, _) == False{} : Bool}; ge))))

def Laws.boot_isolates(n, h, lt, ge):
  boot_isolates.go(n, h, L.lt4(n, lt), ge)
