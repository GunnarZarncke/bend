# hypervisor: the real driver. It applies the kernel's actions through
# effects at EL2 (hv.c), one instance at a time: an instance handles
# FUEL exits, stores the handoff record and asks the boot for the next.
# Build and run it under QEMU with run.sh.
#
#   bend demos/hypervisor/bare.bend -o hv.elf

import Base
import ./main.bend as M

# Effects
# -------
# each implements one action of the model, or the handoff; hv_state.c (the
# state and the switch, spliced first: main calls Hv.instance first) and
# hv.c (the guests and the effects) are the whole C side

def Hv.init(n: U32) -> IO(Unit):
  import "./hv.c"

def Hv.commit(g: U32, mask: List<&2, U32>) -> IO(Unit):
  import "./hv.c"

def Hv.arm(us: U32) -> IO(Unit):
  import "./hv.c"

def Hv.enter(g: U32, win: List<&2, U32>) -> IO(List<&2, U32>):
  import "./hv.c"

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

# the exit words hv.c answers: kind, esr, far, x0..x3, pc, high half first
def exit_of(ws: List<&2, U32>) -> M.Exit:
  match ws:
    case k <> eh <> el <> fh <> fl <> a0 <> a1 <> b0 <> b1 <> c0 <> c1 <> d0 <> d1 <> p0 <> p1 <> rest:
      exit_kind(k, M.W64{eh, el}, M.W64{fh, fl},
        M.Regs{M.W64{a0, a1}, M.W64{b0, b1}, M.W64{c0, c1}, M.W64{d0, d1}, M.W64{p0, p1}})
    case other:
      M.Fault{M.W64.zero(), M.Regs.zero()}

# Drive
# -----
# runs a decision's actions; Enter is last and answers the guest's exit

def no_exit() -> M.Exit:
  M.Fault{M.W64.zero(), M.Regs.zero()}

def drive(acts: List<&2, M.Action>, +ps: M.Tree<M.Owner>) -> IO(M.Exit):
  match acts:
    case Nil{}:
      IO.pure(M.Exit, no_exit())
    case M.Commit{+g} <> rest:
      do IO<M.Exit>:
        Hv.commit(g, mask_words(M.Tree.to_list(Bool, M.mask(ps, g), Nil{})))
        drive(rest, ps)
    case M.Arm{us} <> rest:
      do IO<M.Exit>:
        Hv.arm(us)
        drive(rest, ps)
    case M.Stop{g} <> rest:
      do IO<M.Exit>:
        IO.print("")
        IO.print("[guest " ++ U32.show(g) ++ " stopped]")
        drive(rest, ps)
    case M.Print{s} <> rest:
      do IO<M.Exit>:
        IO.write(s)
        drive(rest, ps)
    case M.Enter{g, regs} <> rest:
      do IO<M.Exit>:
        ws : List<&2, U32> <- Hv.enter(g, M.Regs.encode(regs, Nil{}))
        return exit_of(ws)
    case M.End{} <> rest:
      IO.pure(M.Exit, no_exit())

# Instance
# --------
# an instance handles FUEL exits; then it settles the pending decision
# (every action but Enter), stores the record and asks for the next
# instance. When no guest is live, main returns and QEMU exits.

def fuel() -> Nat:
  12n

# the actions of a decision that will not enter: prints and stops
def settle(acts: List<&2, M.Action>) -> IO(Unit):
  match acts:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case M.Stop{g} <> rest:
      do IO<Unit>:
        IO.print("")
        IO.print("[guest " ++ U32.show(g) ++ " stopped]")
        settle(rest)
    case M.Print{s} <> rest:
      do IO<Unit>:
        IO.write(s)
        settle(rest)
    case other <> rest:
      settle(rest)

def instance(fuel: Nat, s: M.Step) -> IO(Unit):
  match fuel s:
    case _ M.Fin{k, m, acts}:
      do IO<Unit>:
        settle(acts)
        IO.print("")
        IO.print("halt: no guest runs")
    case 0n M.Go{k, m, acts}:
      do IO<Unit>:
        settle(acts)
        Hv.store(M.encode(k, m))
        IO.print("")
        IO.print("[instance ends: handoff]")
        Hv.again()
    case 1n+f M.Go{+k, M.Machine{+ps, vs, +cur}, acts}:
      do IO<Unit>:
        +e : M.Exit <- drive(acts, ps)
        IO.print("")
        IO.print(U32.show(cur) ++ ": " ++ M.Exit.show(e))
        instance(f, M.handle(k, M.Machine{ps, vs, cur}, e))

# Boot
# ----
# guest g starts at its first block, 16 MiB apart from 0xA1000000

def guest(+g: U32) -> M.VCpu:
  M.VCpu{M.Regs{M.W64.zero(), M.W64.zero(), M.W64.zero(), M.W64.zero(),
    M.W64{0, U32.add(2701131776, U32.mul(g, 16777216))}}, True{}}

def boot_machine() -> M.Machine:
  M.Machine{M.blocks(M.page_depth(), 0n, 4n), M.four(guest(0), guest(1), guest(2), guest(3)), 0}

def boot(i: U32, r: Maybe<(M.Kernel & M.Machine)>) -> IO(Unit):
  match r:
    case None{}:
      do IO<Unit>:
        IO.print("bend hypervisor: boot, 4 guests")
        Hv.init(4)
        instance(fuel(), M.sched(M.Kernel{4, 0, 10000}, boot_machine()))
    case Some{(k, m)}:
      do IO<Unit>:
        IO.print("[instance " ++ U32.show(i) ++ ": from the record]")
        instance(fuel(), M.sched(k, m))

def main() -> IO(Unit):
  do IO<Unit>:
    i : U32 <- Hv.instance()
    ws : List<&2, U32> <- Hv.load()
    boot(i, M.decode_record(ws))
