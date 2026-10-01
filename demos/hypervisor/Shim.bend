# hypervisor: the trap shim run on Isa.bend. The states the shim's laws
# start from, and the views they end in: a guest's saved file (the area
# of hv_state.c, 55 registers) and the host's registers, every value a
# variable; the addresses are the layout's (the area of guest g in the
# persist region, the host stack at a fixed address). LAWS.bend states
# the laws, PROOF.bend proves them by running the shim's words
# (shim_words.bend, gen_shim.sh) on the semantics.

import Base
import ./main.bend as Hv
import ./Isa.bend as I
import ./shim_words.bend as S

# the file hv_state.c saves per guest: x0..x30, SP_EL1, SP_EL0, ELR_EL2,
# SPSR_EL2, the 17 EL1 registers of HV_SYS, ESR_EL2, FAR_EL2, HPFAR_EL2
type Saved is Data:
  Saved{x0: Hv.W64, x1: Hv.W64, x2: Hv.W64, x3: Hv.W64, x4: Hv.W64, x5: Hv.W64, x6: Hv.W64, x7: Hv.W64, x8: Hv.W64, x9: Hv.W64, x10: Hv.W64, x11: Hv.W64, x12: Hv.W64, x13: Hv.W64, x14: Hv.W64, x15: Hv.W64, x16: Hv.W64, x17: Hv.W64, x18: Hv.W64, x19: Hv.W64, x20: Hv.W64, x21: Hv.W64, x22: Hv.W64, x23: Hv.W64, x24: Hv.W64, x25: Hv.W64, x26: Hv.W64, x27: Hv.W64, x28: Hv.W64, x29: Hv.W64, x30: Hv.W64, sp1: Hv.W64, sp0: Hv.W64, elr: Hv.W64, spsr: Hv.W64, r0: Hv.W64, r1: Hv.W64, r2: Hv.W64, r3: Hv.W64, r4: Hv.W64, r5: Hv.W64, r6: Hv.W64, r7: Hv.W64, r8: Hv.W64, r9: Hv.W64, r10: Hv.W64, r11: Hv.W64, r12: Hv.W64, r13: Hv.W64, r14: Hv.W64, r15: Hv.W64, r16: Hv.W64, esr: Hv.W64, far: Hv.W64, hpfar: Hv.W64}

# the host's registers at the call of hv_enter: x0 and x1 are its
# arguments, the rest the caller's
type Host is Data:
  Host{x2: Hv.W64, x3: Hv.W64, x4: Hv.W64, x5: Hv.W64, x6: Hv.W64, x7: Hv.W64, x8: Hv.W64, x9: Hv.W64, x10: Hv.W64, x11: Hv.W64, x12: Hv.W64, x13: Hv.W64, x14: Hv.W64, x15: Hv.W64, x16: Hv.W64, x17: Hv.W64, x18: Hv.W64, x19: Hv.W64, x20: Hv.W64, x21: Hv.W64, x22: Hv.W64, x23: Hv.W64, x24: Hv.W64, x25: Hv.W64, x26: Hv.W64, x27: Hv.W64, x28: Hv.W64, x29: Hv.W64, x30: Hv.W64}

# Layout
# ------

def persist() -> Hv.W64:
  Hv.W64{0, 2415919104}

# guest g's area: HvState's host_sp and four words, then area[g], 448
# bytes apart. The four are written out rather than computed: a kernel
# without sharing reduces a multiply of a word at every use of it.
def area(+g: U32) -> Hv.W64:
  Bool.pick(Hv.W64, U32.is_eq(g, 0), Hv.W64{0, 2415919128},
    Bool.pick(Hv.W64, U32.is_eq(g, 1), Hv.W64{0, 2415919576},
      Bool.pick(Hv.W64, U32.is_eq(g, 2), Hv.W64{0, 2415920024}, Hv.W64{0, 2415920472})))

# the host's stack pointer at the call
def stack() -> Hv.W64:
  Hv.W64{0, 1075314688}

def at(+a: Hv.W64, +off: U32) -> Hv.W64:
  I.W.add(a, I.W.of(off))

def rom() -> I.Rom:
  I.Rom{I.W.of(S.hv_enter()), S.size(), S.words()}

def el1_regs() -> List<&2, U32>:
  [49280, 49408, 49409, 49410, 50448, 50456, 50688, 49664, 49665, 49808, 49920, 56962, 50820, 56963, 50817, 49282, 50080]

def cell2(+a: Hv.W64, +v: Hv.W64, m: List<&2, I.Cell>) -> List<&2, I.Cell>:
  I.Cell{a, v} <> m

def Saved.list(f: Saved) -> List<&2, Hv.W64>:
  match f:
    case Saved{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, sp1, sp0, elr, spsr, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, esr, far, hpfar}:
      [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, sp1, sp0, elr, spsr, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, esr, far, hpfar]

def Saved.x(f: Saved) -> List<&2, Hv.W64>:
  match f:
    case Saved{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, sp1, sp0, elr, spsr, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, esr, far, hpfar}:
      [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30]

def Saved.el1(f: Saved) -> List<&2, Hv.W64>:
  match f:
    case Saved{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, sp1, sp0, elr, spsr, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, esr, far, hpfar}:
      [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16]

# a list of registers, as memory cells from address a on. The address is
# forced before it is stored and before the next is computed from it, so
# a cell's address is a word and not a chain of adds over the ones
# before it: the kernel reduces such a chain again at every access.
# the offsets of a run of doublewords, as words: an address is the base
# plus one of these, never the address before it plus eight. The kernel
# forces a value only to its constructor, so a half built from the half
# before it stays a chain of adds, and reading the nth cell would cost n.
def offs() -> List<&2, U32>:
  [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128,
   136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240,
   248, 256, 264, 272, 280, 288, 296, 304, 312, 320, 328, 336, 344, 352,
   360, 368, 376, 384, 392, 400, 408, 416, 424, 432]

def cells.go(vs: List<&2, Hv.W64>, os: List<&2, U32>, +a: Hv.W64, m: List<&2, I.Cell>) -> List<&2, I.Cell>:
  match vs os:
    case Nil{} oo:
      m
    case v <> t Nil{}:
      m
    case v <> t +o <> ot:
      I.Cell{at(a, o), v} <> cells.go(t, ot, a, m)

def cells(vs: List<&2, Hv.W64>, +a: Hv.W64, m: List<&2, I.Cell>) -> List<&2, I.Cell>:
  cells.go(vs, offs(), a, m)

# a list read back from memory at a
def read.go(n: Nat, os: List<&2, U32>, +m: List<&2, I.Cell>, +a: Hv.W64) -> List<&2, Hv.W64>:
  match n os:
    case 0n oo:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p +o <> ot:
      I.mem_read(m, at(a, o)) <> read.go(p, ot, m, a)

def read(n: Nat, +m: List<&2, I.Cell>, +a: Hv.W64) -> List<&2, Hv.W64>:
  read.go(n, offs(), m, a)

def sys_list(rs: List<&2, U32>, vs: List<&2, Hv.W64>, m: List<&2, I.Sr>) -> List<&2, I.Sr>:
  match rs vs:
    case e <> t v <> u:
      I.Sr{e, v} <> sys_list(t, u, m)
    case other _:
      m

def sys_read_all(rs: List<&2, U32>, +m: List<&2, I.Sr>) -> List<&2, Hv.W64>:
  match rs:
    case Nil{}:
      Nil{}
    case +e <> t:
      I.sys_read(m, e) <> sys_read_all(t, m)

def Host.saved(h: Host) -> List<&2, Hv.W64>:
  match h:
    case Host{x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30}:
      [x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30]

# Enter
# -----
# the core at hv_enter's call: x0 the area, x1 the host_sp slot, the stack
# at stack(); memory holds the file at the area

def enter_state(+g: U32, h: Host, +nzcv: U32, +daif: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, +f: Saved, s2: Hv.Tree<Bool>) -> I.State:
  match h:
    case Host{x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30}:
      I.State{I.Cpu{[area(g), persist(), x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30],
          I.W.of(S.hv_enter()), 2, 1, nzcv, daif, I.Sr{I.SP_EL2(), stack()} <> sys},
        cells(Saved.list(f), area(g), mem), rom(), s2}

# what hv_enter leaves: the core as the guest's file says, at the EL and
# with the PSTATE its SPSR names, and the host's registers on its stack
type Entered is Data:
  Entered{x: List<&2, Hv.W64>, pc: Hv.W64, el: U32, spsel: U32, nzcv: U32, daif: U32,
    sp1: Hv.W64, sp0: Hv.W64, el1: List<&2, Hv.W64>, tpidr: Hv.W64, sp2: Hv.W64,
    saved: List<&2, Hv.W64>, host_sp: Hv.W64}

def entered(o: I.Out) -> Maybe<&2, Entered>:
  match o:
    case I.Run{I.State{I.Cpu{x, pc, el, spsel, nzcv, daif, +sys}, +mem, rom, s2}}:
      Some{Entered{x, pc, el, spsel, nzcv, daif, I.sys_read(sys, I.SP_EL1()), I.sys_read(sys, I.SP_EL0()),
        sys_read_all(el1_regs(), sys), I.sys_read(sys, I.TPIDR_EL2()), I.sys_read(sys, I.SP_EL2()),
        read(12n, mem, I.W.sub(stack(), I.W.of(96))), I.mem_read(mem, persist())}}
    case I.Stop{why, s}:
      None{}

def entered.want(+g: U32, h: Host, +f: Saved) -> Maybe<&2, Entered>:
  match f:
    case Saved{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, sp1, sp0, elr, +spsr, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, esr, far, hpfar}:
      Some{Entered{[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30], elr,
        I.bits(I.W.lo(spsr), 2n, 3), I.bits(I.W.lo(spsr), 0n, 1), I.bits(I.W.lo(spsr), 28n, 15), I.bits(I.W.lo(spsr), 6n, 15),
        sp1, sp0, [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16], area(g), I.W.sub(stack(), I.W.of(96)),
        Host.saved(h), I.W.sub(stack(), I.W.of(96))}}

# Exit
# ----
# the core at the vector of an exception from the guest: the guest's
# registers, the exception's ELR, SPSR, ESR, FAR and HPFAR, SP_EL2 where
# hv_enter left it, TPIDR_EL2 the area; the host's registers on its stack

def exit_state(+g: U32, +vec: U32, h: Host, +nzcv: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, +f: Saved, s2: Hv.Tree<Bool>) -> I.State:
  match f:
    case Saved{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, sp1, sp0, elr, spsr, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, esr, far, hpfar}:
      I.State{I.Cpu{[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30], I.W.of(U32.add(S.hv_vectors(), vec)), 2, 1, nzcv, 15,
          I.Sr{I.SP_EL2(), I.W.sub(stack(), I.W.of(96))} <> I.Sr{I.TPIDR_EL2(), area(g)} <> I.Sr{I.SP_EL1(), sp1} <> I.Sr{I.SP_EL0(), sp0} <>
          I.Sr{I.ELR_EL2(), elr} <> I.Sr{I.SPSR_EL2(), spsr} <> I.Sr{I.ESR_EL2(), esr} <> I.Sr{I.FAR_EL2(), far} <> I.Sr{I.HPFAR_EL2(), hpfar} <>
          sys_list(el1_regs(), [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16], sys)},
        cells(Host.saved(h), I.W.sub(stack(), I.W.of(96)), cell2(persist(), I.W.sub(stack(), I.W.of(96)), mem)), rom(), s2}

# what the exit path leaves: the file in the area, the host's registers
# back, the exit's kind in x0, the return to hv_enter's caller
type Exited is Data:
  Exited{file: List<&2, Hv.W64>, saved: List<&2, Hv.W64>, x0: Hv.W64, pc: Hv.W64, sp2: Hv.W64, el: U32}

def exited(+g: U32, o: I.Out) -> Maybe<&2, Exited>:
  match o:
    case I.Run{I.State{I.Cpu{+x, pc, el, spsel, nzcv, daif, sys}, +mem, rom, s2}}:
      Some{Exited{read(55n, mem, area(g)), List.drop(&2, Hv.W64, x, 19n), I.xr(x, 0), pc, I.sys_read(sys, I.SP_EL2()), el}}
    case I.Stop{why, s}:
      None{}

def exited.want(+kind: U32, h: Host, f: Saved) -> Maybe<&2, Exited>:
  match h:
    case Host{x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, +x30}:
      Some{Exited{Saved.list(f), [x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30], I.W.of(kind), x30, stack(), 2}}

# Decide
# ------
# the core at the call of hv_decide, which hv_enter_run makes once the
# shim has saved the guest's file: x0 the ESR, x1 the FAR, x2 the HPFAR,
# x3 the area, the stack where hv_enter left it, x30 the return. It
# answers the exit's kind in x0 and the faulting address in x1, and the
# words it reads are its arguments, so only the class that steps the
# guest's ELR past its instruction touches memory at all.
#
# The class is a literal and the ESR a variable: the decode branches on
# the class, and Bend's U32 has no algebra, so a shift of a variable
# stays a shift. decide_mid is the state one instruction in, the class in
# x4, and SHIM_LAWS puts the two together.

def decide_state(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +ar: Hv.W64, h: Host, +nzcv: U32, +daif: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, s2: Hv.Tree<Bool>, +lr: Hv.W64) -> I.State:
  match h:
    case Host{x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30}:
      I.State{I.Cpu{[esr, fault, hpfar, ar, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, lr],
          I.W.of(S.hv_decide()), 2, 1, nzcv, daif, I.Sr{I.SP_EL2(), I.W.sub(stack(), I.W.of(96))} <> sys},
        mem, rom(), s2}

def decide_mid(+cls: Hv.W64, +esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +ar: Hv.W64, h: Host, +nzcv: U32, +daif: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, s2: Hv.Tree<Bool>, +lr: Hv.W64) -> I.State:
  match h:
    case Host{x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30}:
      I.State{I.Cpu{[esr, fault, hpfar, ar, cls, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, lr],
          I.W.of(U32.add(S.hv_decide(), 4)), 2, 1, nzcv, daif, I.Sr{I.SP_EL2(), I.W.sub(stack(), I.W.of(96))} <> sys},
        mem, rom(), s2}

# what hv_decide leaves: the kind in x0, the faulting address in x1, the
# return taken, and the stack as it found it
type Decided is Data:
  Decided{kind: Hv.W64, far: Hv.W64, pc: Hv.W64, el: U32, sp2: Hv.W64}

def decided(o: I.Out) -> Maybe<&2, Decided>:
  match o:
    case I.Run{I.State{I.Cpu{+x, pc, el, spsel, nzcv, daif, sys}, mem, rom, s2}}:
      Some{Decided{I.xr(x, 0), I.xr(x, 1), pc, el, I.sys_read(sys, I.SP_EL2())}}
    case I.Stop{why, s}:
      None{}

def decided.want(+kind: U32, +far: Hv.W64, +lr: Hv.W64) -> Maybe<&2, Decided>:
  Some{Decided{I.W.of(kind), far, lr, 2, I.W.sub(stack(), I.W.of(96))}}

# the address a stage-2 abort faulted at: HPFAR's block, FAR's offset in it
def fault_at(+fault: Hv.W64, +hpfar: Hv.W64) -> Hv.W64:
  I.W.or(I.W.shl_by(I.W.and(hpfar, Hv.W64{255, 4294967280}), 8),
    I.W.and(fault, Hv.W64{0, 4095}))

# the one class that writes: it steps the guest's ELR in the area past
# the instruction that trapped, so its law names the guest
type Stepped is Data:
  Stepped{kind: Hv.W64, far: Hv.W64, pc: Hv.W64, el: U32, sp2: Hv.W64, elr: Hv.W64}

def stepped(+g: U32, o: I.Out) -> Maybe<&2, Stepped>:
  match o:
    case I.Run{I.State{I.Cpu{+x, pc, el, spsel, nzcv, daif, sys}, +mem, rom, s2}}:
      Some{Stepped{I.xr(x, 0), I.xr(x, 1), pc, el, I.sys_read(sys, I.SP_EL2()), I.mem_read(mem, at(area(g), 264))}}
    case I.Stop{why, s}:
      None{}

def stepped.want(+elr: Hv.W64, +lr: Hv.W64) -> Maybe<&2, Stepped>:
  Some{Stepped{I.W.of(4), I.W.of(0), lr, 2, I.W.sub(stack(), I.W.of(96)), I.W.add(elr, I.W.of(4))}}
