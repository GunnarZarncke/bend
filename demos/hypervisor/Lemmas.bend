# hypervisor: the lemmas the proofs need and Base lacks: Bool clashes and
# connectives, U32 and W64 equality, views of a small U32 as one of four
# literals, and Array.get's descent handing its array back. Candidates
# for Base once their statements settle.

import Base
import ./main.bend as Hv
import ./Isa.bend as Isa

# Bool
# ----

def BoolT(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def BoolF(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

# False is not True
def false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : BoolT(_)
  Unit{}

def true_false(e: {True{} == False{} : Bool}) -> Empty:
  %e : BoolF(_)
  Unit{}

def not_true(+b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(e))

# Words
# -----

def CmpT(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Empty
    case o:
      Unit

def bool_eq(+a: Bool, +b: Bool, e: {Bool.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, (%e : CmpT(_); Unit{}))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, (%e : CmpT(_); Unit{}))
    case True{} True{}:
      {==}

def fin_tail(ab: Bool, bb: Bool, t: Cmp, e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}) -> {t == EQ{} : Cmp}:
  match t:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, (%e : CmpT(_); Unit{}))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, (%e : CmpT(_); Unit{}))

def fin_head(+ab: Bool, +bb: Bool, t: Cmp, e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}) -> {Bool.cmp(ab, bb) == EQ{} : Cmp}:
  match t:
    case LT{}:
      Empty.absurd({Bool.cmp(ab, bb) == EQ{} : Cmp}, (%e : CmpT(_); Unit{}))
    case EQ{}:
      e
    case GT{}:
      Empty.absurd({Bool.cmp(ab, bb) == EQ{} : Cmp}, (%e : CmpT(_); Unit{}))

# a word comparison answers EQ only for equal words
def word_eq(+n: Nat, +a: Word(n), +b: Word(n), +e: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          %bool_eq(ab, bb, fin_head(ab, bb, Word.cmp(p, at, bt), e)) : {WCon{ab, at} == WCon{_, bt} : Word.Con<p>}
          %word_eq(p, at, bt, fin_tail(ab, bb, Word.cmp(p, at, bt), e)) : {WCon{ab, at} == WCon{ab, _} : Word.Con<p>}
          {==}

def word_refl(+n: Nat, +w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, word_refl(p, t)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}
        case WCon{True{}, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, word_refl(p, t)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
          {==}

def cmp_is_eq(+c: Cmp, e: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, false_true(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, false_true(e))

# U32.is_eq is sound and reflexive
def u32_eq(+a: U32, +b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      %word_eq(32n, x, y, cmp_is_eq(Word.cmp(32n, x, y), e)) : {U32{x} == U32{_} : U32}
      {==}

def u32_refl(+a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{x}:
      %Equal.sym(Cmp, Word.cmp(32n, x, x), EQ{}, word_refl(32n, x)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# distinct words are not equal
def u32_ne(+g: U32, +h: U32, e: {U32.is_ne(g, h) == True{} : Bool}) -> {U32.is_eq(g, h) == False{} : Bool}:
  not_true(U32.is_eq(g, h), e)

# the contrapositive: equal words are not distinct
def u32_ne_eq(+g: U32, e: {U32.is_ne(g, g) == True{} : Bool}) -> Empty:
  false_true((%u32_refl(g) : {Bool.not(_) == True{} : Bool}; e))

# Slots
# -----
# a U32 below four is one of four literals, and any U32 masked to its
# two low bits is too: the views turn a symbolic index into a literal, so
# an access to a four-slot array computes

def and_zero(+n: Nat, w: Word(n)) -> {Word.and(n, w, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          %Equal.sym(Word(p), Word.and(p, t, Word.zero(p)), Word.zero(p), and_zero(p, t)) : {WCon{False{}, _} == WCon{False{}, Word.zero(p)} : Word.Con<p>}
          {==}
        case WCon{True{}, t}:
          %Equal.sym(Word(p), Word.and(p, t, Word.zero(p)), Word.zero(p), and_zero(p, t)) : {WCon{False{}, _} == WCon{False{}, Word.zero(p)} : Word.Con<p>}
          {==}

type Low2<-i: U32> is Data:
  L0{e: {0 == U32.and(i, 3) : U32}}
  L1{e: {1 == U32.and(i, 3) : U32}}
  L2{e: {2 == U32.and(i, 3) : U32}}
  L3{e: {3 == U32.and(i, 3) : U32}}

def low2(i: U32) -> Low2<i>:
  match i:
    case U32{WCon{False{}, WCon{False{}, r}}}:
      L0{(%Equal.sym(Word(30n), Word.and(30n, r, Word.zero(30n)), Word.zero(30n), and_zero(30n, r)) : {0 == U32{WCon{False{}, WCon{False{}, _}}} : U32}; {==})}
    case U32{WCon{True{}, WCon{False{}, r}}}:
      L1{(%Equal.sym(Word(30n), Word.and(30n, r, Word.zero(30n)), Word.zero(30n), and_zero(30n, r)) : {1 == U32{WCon{True{}, WCon{False{}, _}}} : U32}; {==})}
    case U32{WCon{False{}, WCon{True{}, r}}}:
      L2{(%Equal.sym(Word(30n), Word.and(30n, r, Word.zero(30n)), Word.zero(30n), and_zero(30n, r)) : {2 == U32{WCon{False{}, WCon{True{}, _}}} : U32}; {==})}
    case U32{WCon{True{}, WCon{True{}, r}}}:
      L3{(%Equal.sym(Word(30n), Word.and(30n, r, Word.zero(30n)), Word.zero(30n), and_zero(30n, r)) : {3 == U32{WCon{True{}, WCon{True{}, _}}} : U32}; {==})}

def cmp_zero.fin(b: Bool, c: Cmp, e: {Cmp.is_lt(c) == False{} : Bool}) -> {Cmp.is_lt(Word.cmp.fin(b, False{}, c)) == False{} : Bool}:
  match b c:
    case bb LT{}:
      Empty.absurd({Cmp.is_lt(Word.cmp.fin(bb, False{}, LT{})) == False{} : Bool}, true_false(e))
    case False{} EQ{}:
      {==}
    case True{} EQ{}:
      {==}
    case bb GT{}:
      {==}

# a word compared with zero is never below it
def cmp_zero(+n: Nat, +w: Word(n)) -> {Cmp.is_lt(Word.cmp(n, w, Word.zero(n))) == False{} : Bool}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          cmp_zero.fin(b, Word.cmp(p, t, Word.zero(p)), cmp_zero(p, t))


type Lt4<-i: U32> is Data:
  K0{e: {0 == i : U32}}
  K1{e: {1 == i : U32}}
  K2{e: {2 == i : U32}}
  K3{e: {3 == i : U32}}

def lt4.eq(b0: Bool, b1: Bool, b2: Bool, +c: Cmp, lt: {Cmp.is_lt(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, False{}, Word.cmp.fin(b2, True{}, c)))) == True{} : Bool}, nl: {Cmp.is_lt(c) == False{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, true_false(nl))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, false_true(lt))

def lt4.b2(+b0: Bool, +b1: Bool, +b2: Bool, lt: {Cmp.is_lt(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, False{}, Word.cmp.fin(b2, True{}, EQ{})))) == True{} : Bool}) -> {b2 == False{} : Bool}:
  match b0 b1 b2:
    case x y False{}:
      {==}
    case False{} False{} True{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(lt))
    case True{} False{} True{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(lt))
    case False{} True{} True{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(lt))
    case True{} True{} True{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(lt))

def lt4.fin(+b0: Bool, +b1: Bool, b2: Bool, r: Word(29n), eb2: {False{} == b2 : Bool}, rz: {Word.zero(29n) == r : Word(29n)}) -> Lt4<U32{WCon{b0, WCon{b1, WCon{b2, r}}}}>:
  match b0 b1:
    case False{} False{}:
      K0{(%eb2 : {0 == U32{WCon{False{}, WCon{False{}, WCon{_, r}}}} : U32}; %rz : {0 == U32{WCon{False{}, WCon{False{}, WCon{False{}, _}}}} : U32}; {==})}
    case True{} False{}:
      K1{(%eb2 : {1 == U32{WCon{True{}, WCon{False{}, WCon{_, r}}}} : U32}; %rz : {1 == U32{WCon{True{}, WCon{False{}, WCon{False{}, _}}}} : U32}; {==})}
    case False{} True{}:
      K2{(%eb2 : {2 == U32{WCon{False{}, WCon{True{}, WCon{_, r}}}} : U32}; %rz : {2 == U32{WCon{False{}, WCon{True{}, WCon{False{}, _}}}} : U32}; {==})}
    case True{} True{}:
      K3{(%eb2 : {3 == U32{WCon{True{}, WCon{True{}, WCon{_, r}}}} : U32}; %rz : {3 == U32{WCon{True{}, WCon{True{}, WCon{False{}, _}}}} : U32}; {==})}

# a U32 below four is 0, 1, 2 or 3
def lt4(i: U32, +lt: {U32.is_lt(i, 4) == True{} : Bool}) -> Lt4<i>:
  match i:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, +r}}}}:
      +er = lt4.eq(b0, b1, b2, Word.cmp(29n, r, Word.zero(29n)), lt, cmp_zero(29n, r))
      lt4.fin(b0, b1, b2, r,
        Equal.sym(Bool, b2, False{}, lt4.b2(b0, b1, b2, (%er : {Cmp.is_lt(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, False{}, Word.cmp.fin(b2, True{}, _)))) == True{} : Bool}; lt))),
        Equal.sym(Word(29n), r, Word.zero(29n), word_eq(29n, r, Word.zero(29n), er)))

# Arrays
# ------
# a read hands back the array it read: Array.size and Array.get's
# descent rebuild every node they open. An array is affine even in a
# proof, so a lemma that needs both facts of one array takes it apart
# into its Data leaves first (PROOF.bend's four_view).

def size_eta(-T: Type, a: Array<T>) -> {Array.size(T, a) == (a, Pair.snd(Array<T>, U32, Array.size(T, a))) : Array<T> & U32}:
  match a:
    case ALeaf{x}:
      {==}
    case ANode{xs, ys}:
      %Equal.sym(Array<T> & U32, Array.size(T, xs), (xs, Pair.snd(Array<T>, U32, Array.size(T, xs))), size_eta(T, xs)) : {Array.size.node(T, ys, _) == (ANode{xs, ys}, Pair.snd(Array<T>, U32, Array.size.node(T, ys, _))) : Array<T> & U32}
      {==}

def get_go_eta(-T: Data, a: Array<T>, +n: U32, +i: U32, z: Bool) -> {Array.get.go(T, a, n, i, z) == (a, Pair.snd(Array<T>, T, Array.get.go(T, a, n, i, z))) : Array<T> & T}:
  match a z:
    case ALeaf{x} zz:
      {==}
    case ANode{xs, ys} True{}:
      +h = U32.shr(n)
      %Equal.sym(Array<T> & T, Array.get.go(T, xs, h, i, U32.is_lt(i, U32.shr(h))), (xs, Pair.snd(Array<T>, T, Array.get.go(T, xs, h, i, U32.is_lt(i, U32.shr(h))))), get_go_eta(T, xs, h, i, U32.is_lt(i, U32.shr(h)))) : {Array.swap.lo(T, ys, _) == (ANode{xs, ys}, Pair.snd(Array<T>, T, Array.swap.lo(T, ys, _))) : Array<T> & T}
      {==}
    case ANode{xs, ys} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      %Equal.sym(Array<T> & T, Array.get.go(T, ys, h, j, U32.is_lt(j, U32.shr(h))), (ys, Pair.snd(Array<T>, T, Array.get.go(T, ys, h, j, U32.is_lt(j, U32.shr(h))))), get_go_eta(T, ys, h, j, U32.is_lt(j, U32.shr(h)))) : {Array.swap.hi(T, xs, _) == (ANode{xs, ys}, Pair.snd(Array<T>, T, Array.swap.hi(T, xs, _))) : Array<T> & T}
      {==}

# Bool connectives
# ----------------

def and_l(+x: Bool, y: Bool, e: {Bool.and(x, y) == True{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(e))
    case True{}:
      {==}

def and_r(x: Bool, y: Bool, e: {Bool.and(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case False{}:
      Empty.absurd({y == True{} : Bool}, false_true(e))
    case True{}:
      e

def or_l(+x: Bool, y: Bool, e: {Bool.or(x, y) == False{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_false(e))

def or_r(x: Bool, y: Bool, e: {Bool.or(x, y) == False{} : Bool}) -> {y == False{} : Bool}:
  match x:
    case False{}:
      e
    case True{}:
      Empty.absurd({y == False{} : Bool}, true_false(e))

def or_true_r(x: Bool, -y: Bool, e: {y == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case False{}:
      e
    case True{}:
      {==}

# two 64-bit words the model calls equal are equal
def w64_eq(+a: Hv.W64, +b: Hv.W64, +e: {Isa.W.is_eq(a, b) == True{} : Bool}) -> {a == b : Hv.W64}:
  match a b:
    case Hv.W64{ah, al} Hv.W64{bh, bl}:
      %u32_eq(ah, bh, and_l(U32.is_eq(ah, bh), U32.is_eq(al, bl), e)) : {Hv.W64{ah, al} == Hv.W64{_, bl} : Hv.W64}
      %u32_eq(al, bl, and_r(U32.is_eq(ah, bh), U32.is_eq(al, bl), e)) : {Hv.W64{ah, al} == Hv.W64{ah, _} : Hv.W64}
      {==}

# a U32 below six is one of six literals: an owner word names Free, Hyp,
# or one of the four slots, and nothing else
type Lt6<-i: U32> is Data:
  K60{e: {0 == i : U32}}
  K61{e: {1 == i : U32}}
  K62{e: {2 == i : U32}}
  K63{e: {3 == i : U32}}
  K64{e: {4 == i : U32}}
  K65{e: {5 == i : U32}}

def lt6.eq(b0: Bool, b1: Bool, b2: Bool, +c: Cmp, lt: {Cmp.is_lt(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, True{}, Word.cmp.fin(b2, True{}, c)))) == True{} : Bool}, nl: {Cmp.is_lt(c) == False{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, true_false(nl))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, false_true(lt))

def lt6.b(+b0: Bool, +b1: Bool, +b2: Bool, lt: {Cmp.is_lt(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, True{}, Word.cmp.fin(b2, True{}, EQ{})))) == True{} : Bool}) -> {Bool.and(b1, b2) == False{} : Bool}:
  match b0 b1 b2:
    case x y False{}:
      {==}
    case x False{} True{}:
      {==}
    case False{} True{} True{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(lt))
    case True{} True{} True{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(lt))

def lt6.fin(b0: Bool, b1: Bool, b2: Bool, +r: Word(29n), no6: {Bool.and(b1, b2) == False{} : Bool}, +rz: {Word.zero(29n) == r : Word(29n)}) -> Lt6<U32{WCon{b0, WCon{b1, WCon{b2, r}}}}>:
  match b0 b1 b2:
    case False{} False{} False{}:
      K60{(%rz : {0 == U32{WCon{False{}, WCon{False{}, WCon{False{}, _}}}} : U32}; {==})}
    case True{} False{} False{}:
      K61{(%rz : {1 == U32{WCon{True{}, WCon{False{}, WCon{False{}, _}}}} : U32}; {==})}
    case False{} True{} False{}:
      K62{(%rz : {2 == U32{WCon{False{}, WCon{True{}, WCon{False{}, _}}}} : U32}; {==})}
    case True{} True{} False{}:
      K63{(%rz : {3 == U32{WCon{True{}, WCon{True{}, WCon{False{}, _}}}} : U32}; {==})}
    case False{} False{} True{}:
      K64{(%rz : {4 == U32{WCon{False{}, WCon{False{}, WCon{True{}, _}}}} : U32}; {==})}
    case True{} False{} True{}:
      K65{(%rz : {5 == U32{WCon{True{}, WCon{False{}, WCon{True{}, _}}}} : U32}; {==})}
    case False{} True{} True{}:
      Empty.absurd(Lt6<U32{WCon{False{}, WCon{True{}, WCon{True{}, r}}}}>, true_false(no6))
    case True{} True{} True{}:
      Empty.absurd(Lt6<U32{WCon{True{}, WCon{True{}, WCon{True{}, r}}}}>, true_false(no6))

def lt6(i: U32, +lt: {U32.is_lt(i, 6) == True{} : Bool}) -> Lt6<i>:
  match i:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, +r}}}}:
      +er = lt6.eq(b0, b1, b2, Word.cmp(29n, r, Word.zero(29n)), lt, cmp_zero(29n, r))
      lt6.fin(b0, b1, b2, r,
        lt6.b(b0, b1, b2, (%er : {Cmp.is_lt(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, True{}, Word.cmp.fin(b2, True{}, _)))) == True{} : Bool}; lt)),
        Equal.sym(Word(29n), r, Word.zero(29n), word_eq(29n, r, Word.zero(29n), er)))
