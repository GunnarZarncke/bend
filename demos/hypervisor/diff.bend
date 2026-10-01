# hypervisor: the real side of diff.sh. It runs guest set 1 (hv.c) under
# the kernel of main.bend at EL2 on QEMU, as bare.bend does, with a slice
# long enough that no timer fires, and prints every action and, at every
# exit, the register file the trap shim saved. model.bend prints the same
# from Isa.bend; diff.sh compares the two.

import Base
import ./main.bend as M

# Effects
# -------

def Hv.select(set: U32) -> IO(Unit):
  import "./hv_diff.c"

def Hv.init(n: U32) -> IO(Unit):
  import "./hv.c"

def Hv.commit(g: U32, mask: List<&2, U32>) -> IO(Unit):
  import "./hv.c"

def Hv.arm(us: U32) -> IO(Unit):
  import "./hv.c"

def Hv.enter(g: U32, win: List<&2, U32>) -> IO(List<&2, U32>):
  import "./hv.c"

def Hv.snap() -> IO(List<&2, U32>):
  import "./hv_diff.c"

def Hv.load() -> IO(List<&2, U32>):
  import "./hv.c"

def Hv.store(ws: List<&2, U32>) -> IO(Unit):
  import "./hv.c"

def Hv.again() -> IO(Unit):
  import "./hv.c"

def Hv.instance() -> IO(U32):
  import "./hv_state.c"

# Words
# -----

def mask_words(m: List<&2, Bool>) -> List<&2, U32>:
  match m:
    case Nil{}:
      Nil{}
    case b <> t:
      M.Bool.encode(b) <> mask_words(t)

def hex.digit(+d: U32) -> Char:
  Bool.pick(Char, U32.is_lt(d, 10), Char.from_u32(U32.add(48, d)), Char.from_u32(U32.add(87, d)))

def hex.go(n: Nat, +v: U32, acc: List<&2, Char>) -> List<&2, Char>:
  match n:
    case 0n:
      acc
    case 1n+p:
      hex.go(p, U32.shrn(v, 4n), hex.digit(U32.and(v, 15)) <> acc)

def U32.hex(v: U32) -> String:
  String.from_list(hex.go(8n, v, Nil{}))

# the saved file, as sixteen-digit registers
def file_show(ws: List<&2, U32>) -> String:
  match ws:
    case hi <> lo <> rest:
      " " ++ U32.hex(hi) ++ U32.hex(lo) ++ file_show(rest)
    case other:
      ""

def bit6(+w: U32) -> Bool:
  U32.is_ne(U32.and(w, 64), 0)

def W64.lo(w: M.W64) -> U32:
  match w:
    case M.W64{hi, lo}:
      lo

def exit_kind(+k: U32, +esr: M.W64, +far: M.W64, +regs: M.Regs) -> M.Exit:
  Bool.pick(M.Exit, U32.is_eq(k, 0), M.Timer{regs},
    Bool.pick(M.Exit, U32.is_eq(k, 1), M.Hvc{U32.and(W64.lo(esr), 65535), regs},
      Bool.pick(M.Exit, U32.is_eq(k, 2), M.DataAbort{far, bit6(W64.lo(esr)), regs},
        Bool.pick(M.Exit, U32.is_eq(k, 3), M.InstAbort{far, regs},
          Bool.pick(M.Exit, U32.is_eq(k, 4), M.Wfi{regs}, M.Fault{esr, regs})))))

def exit_of(ws: List<&2, U32>) -> M.Exit:
  match ws:
    case k <> eh <> el <> fh <> fl <> a0 <> a1 <> b0 <> b1 <> c0 <> c1 <> d0 <> d1 <> p0 <> p1 <> rest:
      exit_kind(k, M.W64{eh, el}, M.W64{fh, fl},
        M.Regs{M.W64{a0, a1}, M.W64{b0, b1}, M.W64{c0, c1}, M.W64{d0, d1}, M.W64{p0, p1}})
    case other:
      M.Fault{M.W64.zero(), M.Regs.zero()}

# Drive
# -----

def no_exit() -> M.Exit:
  M.Fault{M.W64.zero(), M.Regs.zero()}

def act(a: M.Action) -> IO(Unit):
  IO.print("act " ++ M.Action.show(a))

def drive(acts: List<&2, M.Action>, +ps: M.Tree<M.Owner>) -> IO(M.Exit):
  match acts:
    case Nil{}:
      IO.pure(M.Exit, no_exit())
    case M.Commit{+g} <> rest:
      do IO<M.Exit>:
        act(M.Commit{g})
        Hv.commit(g, mask_words(M.Tree.to_list(Bool, M.mask(ps, g), Nil{})))
        drive(rest, ps)
    case M.Arm{+us} <> rest:
      do IO<M.Exit>:
        act(M.Arm{us})
        Hv.arm(us)
        drive(rest, ps)
    case M.Enter{+g, +regs} <> rest:
      do IO<M.Exit>:
        act(M.Enter{g, regs})
        ws : List<&2, U32> <- Hv.enter(g, M.Regs.encode(regs, Nil{}))
        fs : List<&2, U32> <- Hv.snap()
        IO.print("file" ++ file_show(fs))
        return exit_of(ws)
    case +a <> rest:
      do IO<M.Exit>:
        act(a)
        drive(rest, ps)

def run(fuel: Nat, s: M.Step) -> IO(Unit):
  match fuel s:
    case _ M.Fin{k, m, acts}:
      do IO<Unit>:
        List.for_each(~&2, ~M.Action, ~act, acts)
        IO.print("halt")
    case 0n M.Go{k, m, acts}:
      IO.print("out of fuel")
    case 1n+f M.Go{+k, M.Machine{+ps, vs, +cur}, acts}:
      do IO<Unit>:
        +e : M.Exit <- drive(acts, ps)
        IO.print(U32.show(cur) ++ ": " ++ M.Exit.show(e))
        run(f, M.handle(k, M.Machine{ps, vs, cur}, e))

def guest(+g: U32) -> M.VCpu:
  M.VCpu{M.Regs{M.W64.zero(), M.W64.zero(), M.W64.zero(), M.W64.zero(),
    M.W64{0, U32.add(2701131776, U32.mul(g, 16777216))}}, True{}}

# hv.c registers the handoff's effects too, so main must reach them; a
# second instance never comes, as run never asks for one
def handoff(later: Bool) -> IO(Unit):
  match later:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      do IO<Unit>:
        ws : List<&2, U32> <- Hv.load()
        Hv.store(ws)
        Hv.again()

def main() -> IO(Unit):
  do IO<Unit>:
    i : U32 <- Hv.instance()
    handoff(U32.is_gt(i, 1))
    Hv.select(1)
    Hv.init(4)
    IO.print("diff: start")
    run(64n, M.sched(M.Kernel{4, 0, 2000000},
      M.Machine{M.blocks(M.page_depth(), 0n, 4n), M.four(guest(0), guest(1), guest(2), guest(3)), 0}))
