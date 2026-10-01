# hypervisor: the model's side of diff.sh. It runs guest set 1 under the
# kernel of main.bend, as diff.bend does on QEMU, but steps each guest on
# Isa.bend and takes the trap shim's word for its effect: an entry loads
# the saved file into the core and ERETs (PROOF.bend's enter law), an
# exit saves the core into the file (its exit law). It prints what
# diff.bend prints.
#
#   bend demos/hypervisor/model.bend

import Base
import ./main.bend as M
import ./Isa.bend as I

# the words of guest set 1, as hv.c holds them (gen_guests.sh)
def guest_code(+g: U32) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, U32.is_eq(g, 0),
    [3531604129, 3531603970, 2432699458, 4043310113, 1426063297, 2852258784, 2432747520, 3556769826, 3535798243, 285213796, 1795424389, 1409286208, 3556770082, 3556770018, 4043310086, 1409286212, 3556770082, 3531606176, 3556769826, 3533692936, 4070721160, 4074076584, 4074766568, 3546873097, 3546249514, 2315780427, 3544710412, 3548246413, 2315911598, 1392868623, 1394039280, 168296977, 2853241298, 3556769794, 3534225415, 4177528039, 335544320],
  Bool.pick(List<&2, U32>, U32.is_eq(g, 1),
    [2432697332, 3531753089, 3532312322, 2847869921, 4162818017, 4164978659, 2831226852, 3506504341, 4177527461, 4177528484, 4181722790, 2839552679, 4160818849, 4166977193, 2835490467, 2432696512, 3510633472, 3506936832, 3556769826, 3535077386, 4181721419, 3556769858, 335544320],
  Bool.pick(List<&2, U32>, U32.is_eq(g, 2),
    [3531743777, 3575173249, 3531883586, 3575369794, 3575369826, 3575173153, 3531997187, 3575169027, 3575144450, 3575140865, 3575161346, 3577270404, 3577466949, 2332360838, 3531606624, 3556769826, 3573751935, 3531606752, 3556769826, 3556769858, 335544320],
    [3531606304, 3556769826, 352321536, 3556769858])))

def base(+g: U32) -> M.W64:
  M.W64{0, U32.add(2701131776, U32.mul(g, 16777216))}

# the guest's words, two to a doubleword, as Isa.bend's memory holds them
def load(ws: List<&2, U32>, +a: M.W64, m: List<&2, I.Cell>) -> List<&2, I.Cell>:
  match ws:
    case Nil{}:
      m
    case lo <> Nil{}:
      I.Cell{a, M.W64{0, lo}} <> m
    case lo <> hi <> t:
      I.Cell{a, M.W64{hi, lo}} <> load(t, I.W.add(a, I.W.of(8)), m)

def memory() -> List<&2, I.Cell>:
  load(guest_code(0), base(0), load(guest_code(1), base(1), load(guest_code(2), base(2), load(guest_code(3), base(3), Nil{}))))

# The file
# --------
# the area hv_state.c saves, as a list of its 55 registers: x0..x30,
# sp_el1, sp_el0, elr, spsr, the EL1 registers in HV_SYS's order, esr,
# far, hpfar

def el1_file() -> List<&2, U32>:
  [49280, 49408, 49409, 49410, 50448, 50456, 50688, 49664, 49665, 49808,
   49920, 56962, 50820, 56963, 50817, 49282, 50080]

def zeros(n: Nat) -> List<&2, M.W64>:
  List.replicate(M.W64, n, I.W.of(0))

# hv_guest_load: a zero file, the pc at the guest's base, its stack 1 MiB
# above, EL1h with DAIF masked
def file0(+g: U32) -> List<&2, M.W64>:
  List.concat(&2, M.W64, [zeros(31n), [I.W.add(base(g), I.W.of(1048576)), I.W.of(0), base(g), I.W.of(965)], zeros(20n)])

def at(f: List<&2, M.W64>, +i: Nat) -> M.W64:
  Maybe.default(&2, M.W64, List.get(&2, M.W64, f, i), I.W.of(0))

def take(n: Nat, f: List<&2, M.W64>) -> List<&2, M.W64>:
  List.take(&2, M.W64, f, n)

# hv_enter_run's window: x0..x3 and elr
def window(f: List<&2, M.W64>, r: M.Regs) -> List<&2, M.W64>:
  match r:
    case M.Regs{x0, x1, x2, x3, pc}:
      List.set(&2, M.W64, x0 <> x1 <> x2 <> x3 <> List.drop(&2, M.W64, f, 4n), 33n, pc)

def sys_load(rs: List<&2, U32>, f: List<&2, M.W64>, sys: List<&2, I.Sr>) -> List<&2, I.Sr>:
  match rs f:
    case e <> t v <> u:
      sys_load(t, u, I.sys_write(sys, e, v))
    case other _:
      sys

# the ERET at the end of hv_enter: the pc from the file's ELR, the
# exception level and the flags from its SPSR
def enter.eret(x: List<&2, M.W64>, +elr: M.W64, +p: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, rom: I.Rom, s2: M.Tree<Bool>) -> I.State:
  I.State{I.Cpu{x, elr, I.bits(p, 2n, 3), I.bits(p, 0n, 1), I.bits(p, 28n, 15), I.bits(p, 6n, 15), sys}, mem, rom, s2}

# hv_enter: the file into the core, then ERET
def enter(+f: List<&2, M.W64>, s: I.State) -> I.State:
  match s:
    case I.State{I.Cpu{x, pc, el, spsel, nzcv, daif, sys}, mem, rom, s2}:
      +sys1 = I.sys_write(I.sys_write(I.sys_write(I.sys_write(sys, I.SP_EL1(), at(f, 31n)), I.SP_EL0(), at(f, 32n)), I.ELR_EL2(), at(f, 33n)), I.SPSR_EL2(), at(f, 34n))
      +sys2 = sys_load(el1_file(), List.drop(&2, M.W64, f, 35n), sys1)
      enter.eret(take(31n, f), at(f, 33n), I.W.lo(at(f, 34n)), sys2, mem, rom, s2)

def sys_save(rs: List<&2, U32>, +sys: List<&2, I.Sr>) -> List<&2, M.W64>:
  match rs:
    case Nil{}:
      Nil{}
    case +e <> t:
      I.sys_read(sys, e) <> sys_save(t, sys)

# the exception vector's save: the core into the file
def save(+s: I.State) -> List<&2, M.W64>:
  +sys = I.State.sys(s)
  List.concat(&2, M.W64, [I.State.x(s),
    [I.sys_read(sys, I.SP_EL1()), I.sys_read(sys, I.SP_EL0()), I.sys_read(sys, I.ELR_EL2()), I.sys_read(sys, I.SPSR_EL2())],
    sys_save(el1_file(), sys),
    [I.sys_read(sys, I.ESR_EL2()), I.sys_read(sys, I.FAR_EL2()), I.sys_read(sys, I.HPFAR_EL2())]])

def file_show(f: List<&2, M.W64>) -> String:
  match f:
    case Nil{}:
      ""
    case w <> t:
      " " ++ I.W.hex(w) ++ file_show(t)

# hv_enter_run's reading of the exit: the kind from ESR's class, the
# fault address from HPFAR and FAR, and a WFI's ELR moved past it
def ec_kind(+ec: U32) -> U32:
  Bool.pick(U32, U32.is_eq(ec, 22), 1,
    Bool.pick(U32, U32.is_eq(ec, 36), 2,
      Bool.pick(U32, U32.is_eq(ec, 32), 3,
        Bool.pick(U32, U32.is_eq(ec, 1), 4, 5))))

def fault_addr(+hpfar: M.W64, +far: M.W64) -> M.W64:
  M.W64{U32.shrn(I.W.lo(hpfar), 24n), U32.or(U32.shln(U32.and(I.W.lo(hpfar), 4294967280), 8n), U32.and(I.W.lo(far), 4095))}

def exit_of(+k: U32, +f: List<&2, M.W64>) -> M.Exit:
  +esr = at(f, 52n)
  +addr = fault_addr(at(f, 54n), at(f, 53n))
  +regs = {M.Regs{at(f, 0n), at(f, 1n), at(f, 2n), at(f, 3n), at(f, 33n)} : M.Regs}
  Bool.pick(M.Exit, U32.is_eq(k, 1), M.Hvc{U32.and(I.W.lo(esr), 65535), regs},
    Bool.pick(M.Exit, U32.is_eq(k, 2), M.DataAbort{addr, U32.is_ne(U32.and(I.W.lo(esr), 64), 0), regs},
      Bool.pick(M.Exit, U32.is_eq(k, 3), M.InstAbort{addr, regs},
        Bool.pick(M.Exit, U32.is_eq(k, 4), M.Wfi{M.Regs{at(f, 0n), at(f, 1n), at(f, 2n), at(f, 3n), I.W.add(at(f, 33n), I.W.of(4))}}, M.Fault{esr, regs}))))

def after(+k: U32, +f: List<&2, M.W64>) -> List<&2, M.W64>:
  Bool.pick(List<&2, M.W64>, U32.is_eq(k, 4), List.set(&2, M.W64, f, 33n, I.W.add(at(f, 33n), I.W.of(4))), f)

# Drive
# -----
# the machine the drivers share: the Isa state and the four files

type Sys is Data:
  Sys{s: I.State, files: List<&2, List<&2, M.W64>>}

type Went is Data:
  Went{sys: Sys, e: M.Exit, lines: List<&2, String>}

def act(a: M.Action) -> String:
  "act " ++ M.Action.show(a)

def set_s2(s: I.State, m: M.Tree<Bool>) -> I.State:
  match s:
    case I.State{cpu, mem, rom, s2}:
      I.State{cpu, mem, rom, m}

def no_exit() -> M.Exit:
  M.Fault{M.W64.zero(), M.Regs.zero()}

def enter.fin(+g: U32, +files: List<&2, List<&2, M.W64>>, +lines: List<&2, String>, o: I.Out) -> Went:
  match o:
    case I.Run{+s}:
      +f = I.State.x(s)
      +file = save(s)
      +k = ec_kind(U32.shrn(I.W.lo(at(file, 52n)), 26n))
      Went{Sys{s, List.set(&2, List<&2, M.W64>, files, U32.to_nat(g), after(k, file))}, exit_of(k, file),
        List.append(&2, String, lines, ["file" ++ file_show(file)])}
    case I.Stop{why, s}:
      Went{Sys{s, files}, no_exit(), List.append(&2, String, lines, ["model stops: " ++ why])}

def drive.enter(+g: U32, regs: M.Regs, sy: Sys, lines: List<&2, String>) -> Went:
  match sy:
    case Sys{s, +files}:
      +f = window(Maybe.default(&2, List<&2, M.W64>, List.get(&2, List<&2, M.W64>, files, U32.to_nat(g)), Nil{}), regs)
      enter.fin(g, List.set(&2, List<&2, M.W64>, files, U32.to_nat(g), f), lines, I.run_guest(100000n, enter(f, s)))

def drive(acts: List<&2, M.Action>, +ps: M.Tree<M.Owner>, sy: Sys, lines: List<&2, String>) -> Went:
  match acts sy:
    case Nil{} sy:
      Went{sy, no_exit(), lines}
    case M.Commit{+g} <> rest Sys{s, files}:
      drive(rest, ps, Sys{set_s2(s, M.mask(ps, g)), files}, List.append(&2, String, lines, [act(M.Commit{g})]))
    case M.Enter{+g, +regs} <> rest sy:
      drive.enter(g, regs, sy, List.append(&2, String, lines, [act(M.Enter{g, regs})]))
    case +a <> rest sy:
      drive(rest, ps, sy, List.append(&2, String, lines, [act(a)]))

def acts_lines(acts: List<&2, M.Action>) -> List<&2, String>:
  match acts:
    case Nil{}:
      Nil{}
    case a <> t:
      act(a) <> acts_lines(t)

def run.fin(w: Went, k: Sys -> M.Exit -> List<&2, String> -> List<&2, String>) -> List<&2, String>:
  match w:
    case Went{sy, e, lines}:
      k(sy, e, lines)

def run(fuel: Nat, s: M.Step, sy: Sys, lines: List<&2, String>) -> List<&2, String>:
  match fuel s:
    case _ M.Fin{k, m, acts}:
      List.append(&2, String, lines, List.append(&2, String, acts_lines(acts), ["halt"]))
    case 0n M.Go{k, m, acts}:
      List.append(&2, String, lines, ["out of fuel"])
    case 1n+f M.Go{+k, M.Machine{+ps, vs, +cur}, acts}:
      run.fin(drive(acts, ps, sy, lines), sy2 => +e => ls =>
        run(f, M.handle(k, M.Machine{ps, vs, cur}, e), sy2, List.append(&2, String, ls, [U32.show(cur) ++ ": " ++ M.Exit.show(e)])))

def guest(+g: U32) -> M.VCpu:
  M.VCpu{M.Regs{M.W64.zero(), M.W64.zero(), M.W64.zero(), M.W64.zero(), base(g)}, True{}}

def boot() -> Sys:
  Sys{I.State{I.Cpu{zeros(31n), I.W.of(0), 2, 1, 0, 15, Nil{}}, memory(), I.Rom{I.W.of(0), 0, Nil{}}, M.Leaf{False{}}},
    [file0(0), file0(1), file0(2), file0(3)]}

def main() -> IO(Unit):
  List.for_each(~&2, ~String, ~IO.print,
    run(64n, M.sched(M.Kernel{4, 0, 2000000}, M.Machine{M.blocks(M.page_depth(), 0n, 4n), M.four(guest(0), guest(1), guest(2), guest(3)), 0}),
      boot(), ["diff: start"]))
