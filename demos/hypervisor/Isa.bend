# hypervisor: the ARM64 subset the hypervisor runs on, as a Bend
# semantics: a state, the instruction forms the trap shim and the test
# guests use, exception entry to EL2 and the stage-2 map. It is the
# trusted spec of the hardware from here on (PLAN.md, workstream 3):
# LAWS.bend states the guest-step laws over it, SHIM_LAWS.bend what the
# shim's words do on it, and diff.sh checks it against QEMU, exit by exit
# (model.bend is its side).
#
# Scope: one core, AArch64 only, EL1 guests with their MMU off (a guest
# address is an IPA) under stage 2, EL2 with an identity map. Memory is
# doublewords at 8-aligned addresses, little-endian, so every access the
# model has is one read or one write; an unaligned one is a Stop, as is
# anything else the model does not cover (an unknown instruction, a
# system register an EL1 guest may not touch, an exception to EL1): no
# step is claimed for it.
#
# A step takes the state apart once, matches every value it reads on its
# constructor before that value enters the next state, and builds the
# next state once, so no state ever holds a call on the state before it.
# A proof that runs the shim's words is checked by the BendTT kernel,
# which substitutes without sharing: under this shape a symbolic run
# grows with its steps, and under the plainer one (the next state named
# inside its own update) it grows as a power of them.

import Base
import ./main.bend as Hv

# Words
# -----
# 64-bit arithmetic over Hv.W64, the halves high first

def W.of(+lo: U32) -> Hv.W64:
  Hv.W64{0, lo}

def W.lo(+w: Hv.W64) -> U32:
  match w:
    case Hv.W64{hi, lo}:
      lo

def W.hi(+w: Hv.W64) -> U32:
  match w:
    case Hv.W64{hi, lo}:
      hi

def W.add(+a: Hv.W64, +b: Hv.W64) -> Hv.W64:
  match a b:
    case Hv.W64{ah, +al} Hv.W64{bh, bl}:
      +lo = U32.add(al, bl)
      Hv.W64{U32.add(U32.add(ah, bh), Bool.to_u32(U32.is_lt(lo, al))), lo}

def W.not(+a: Hv.W64) -> Hv.W64:
  match a:
    case Hv.W64{hi, lo}:
      Hv.W64{U32.not(hi), U32.not(lo)}

def W.and(+a: Hv.W64, +b: Hv.W64) -> Hv.W64:
  match a b:
    case Hv.W64{ah, al} Hv.W64{bh, bl}:
      Hv.W64{U32.and(ah, bh), U32.and(al, bl)}

def W.or(+a: Hv.W64, +b: Hv.W64) -> Hv.W64:
  match a b:
    case Hv.W64{ah, al} Hv.W64{bh, bl}:
      Hv.W64{U32.or(ah, bh), U32.or(al, bl)}

def W.sub(+a: Hv.W64, +b: Hv.W64) -> Hv.W64:
  W.add(a, W.add(W.not(b), W.of(1)))

def W.is_eq(+a: Hv.W64, +b: Hv.W64) -> Bool:
  match a b:
    case Hv.W64{ah, al} Hv.W64{bh, bl}:
      Bool.and(U32.is_eq(ah, bh), U32.is_eq(al, bl))

# unsigned a >= b
def W.is_ge(+a: Hv.W64, +b: Hv.W64) -> Bool:
  match a b:
    case Hv.W64{+ah, +al} Hv.W64{+bh, +bl}:
      Bool.or(U32.is_gt(ah, bh), Bool.and(U32.is_eq(ah, bh), U32.is_ge(al, bl)))

# a left shift by three: a scaled doubleword offset
def W.shl3(+a: Hv.W64) -> Hv.W64:
  match a:
    case Hv.W64{hi, +lo}:
      Hv.W64{U32.or(U32.shln(hi, 3n), U32.shrn(lo, 29n)), U32.shln(lo, 3n)}

def W.shl2(+a: Hv.W64) -> Hv.W64:
  match a:
    case Hv.W64{hi, +lo}:
      Hv.W64{U32.or(U32.shln(hi, 2n), U32.shrn(lo, 30n)), U32.shln(lo, 2n)}

# a shift by an amount the instruction word names. Bend shifts by a Nat,
# and the amount is a U32, so it is written as the six fixed shifts its
# bits name: in a symbolic run the word comes from the rom and the
# amount is a literal, so every pick below reduces away.
def W.shln(+a: Hv.W64, +n: Nat) -> Hv.W64:
  match a:
    case Hv.W64{+hi, +lo}:
      Hv.W64{U32.or(U32.shln(hi, n), U32.shrn(lo, Nat.sub(32n, n))), U32.shln(lo, n)}

def W.shrn(+a: Hv.W64, +n: Nat) -> Hv.W64:
  match a:
    case Hv.W64{+hi, +lo}:
      Hv.W64{U32.shrn(hi, n), U32.or(U32.shrn(lo, n), U32.shln(hi, Nat.sub(32n, n)))}

def W.shl_at(+a: Hv.W64, +k: U32, +b: U32, +n: Nat) -> Hv.W64:
  Bool.pick(Hv.W64, U32.is_eq(U32.and(k, b), b), W.shln(a, n), a)

def W.shr_at(+a: Hv.W64, +k: U32, +b: U32, +n: Nat) -> Hv.W64:
  Bool.pick(Hv.W64, U32.is_eq(U32.and(k, b), b), W.shrn(a, n), a)

# the step of 32 moves a half over whole, which W.shln cannot say
def W.shl_by(+a: Hv.W64, +k: U32) -> Hv.W64:
  W.shl_at(W.shl_at(W.shl_at(W.shl_at(W.shl_at(
    Bool.pick(Hv.W64, U32.is_eq(U32.and(k, 32), 32), Hv.W64{W.lo(a), 0}, a),
    k, 16, 16n), k, 8, 8n), k, 4, 4n), k, 2, 2n), k, 1, 1n)

def W.shr_by(+a: Hv.W64, +k: U32) -> Hv.W64:
  W.shr_at(W.shr_at(W.shr_at(W.shr_at(W.shr_at(
    Bool.pick(Hv.W64, U32.is_eq(U32.and(k, 32), 32), Hv.W64{0, W.hi(a)}, a),
    k, 16, 16n), k, 8, 8n), k, 4, 4n), k, 2, 2n), k, 1, 1n)

# the low `bits` bits of v, sign-extended to 64
def W.sext(+v: U32, +bits: Nat) -> Hv.W64:
  +m = U32.sub(U32.shln(1, bits), 1)
  Bool.pick(Hv.W64, U32.is_eq(U32.and(U32.shrn(v, Nat.sub(bits, 1n)), 1), 1),
    Hv.W64{4294967295, U32.or(v, U32.not(m))},
    Hv.W64{0, U32.and(v, m)})

# the low half, zero-extended: a W register
def W.w(+a: Hv.W64) -> Hv.W64:
  Hv.W64{0, W.lo(a)}

def hex.digit(+d: U32) -> Char:
  Bool.pick(Char, U32.is_lt(d, 10), Char.from_u32(U32.add(48, d)), Char.from_u32(U32.add(87, d)))

def hex.go(+n: Nat, +v: U32, +acc: List<&2, Char>) -> List<&2, Char>:
  match n:
    case 0n:
      acc
    case 1n+p:
      hex.go(p, U32.shrn(v, 4n), hex.digit(U32.and(v, 15)) <> acc)

def U32.hex(+v: U32) -> String:
  String.from_list(hex.go(8n, v, Nil{}))

def W.hex(+w: Hv.W64) -> String:
  match w:
    case Hv.W64{hi, lo}:
      U32.hex(hi) ++ U32.hex(lo)

# a field of an instruction word
def bits(+w: U32, +at: Nat, +mask: U32) -> U32:
  U32.and(U32.shrn(w, at), mask)

def bit(+w: U32, +at: Nat) -> Bool:
  U32.is_eq(bits(w, at, 1), 1)

# System registers
# ----------------
# a system register is named by its encoding, op0:op1:CRn:CRm:op2, as the
# MRS and MSR words carry it in bits 20..5

def SP_EL0() -> U32:
  49672
def SP_EL1() -> U32:
  57864
def SP_EL2() -> U32:
  61960
def ELR_EL2() -> U32:
  57857
def SPSR_EL2() -> U32:
  57856
def ESR_EL2() -> U32:
  58000
def FAR_EL2() -> U32:
  58112
def HPFAR_EL2() -> U32:
  58116
def TPIDR_EL2() -> U32:
  59010
def VBAR_EL2() -> U32:
  58880

# the EL1 and EL0 registers a guest may read and write: the seventeen the
# shim switches, and SP_EL0
def el1_regs() -> List<&2, U32>:
  [49280, 49408, 49409, 49410, 50448, 50456, 50688, 49664, 49665, 49808,
   49920, 56962, 50820, 56963, 50817, 49282, 50080, 49672]

def U32.elem(+rs: List<&2, U32>, +e: U32) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      Bool.or(U32.is_eq(r, e), U32.elem(t, e))

def el1_ok(+e: U32) -> Bool:
  U32.elem(el1_regs(), e)

# a guest's own registers: those it may write with MSR, and SP_EL1,
# which it writes as its stack pointer
def own_reg(+e: U32) -> Bool:
  Bool.or(U32.is_eq(SP_EL1(), e), el1_ok(e))

# the registers an exception entry to EL2 writes
def entry_reg(+e: U32) -> Bool:
  Bool.or(U32.is_eq(ELR_EL2(), e), Bool.or(U32.is_eq(SPSR_EL2(), e),
    Bool.or(U32.is_eq(ESR_EL2(), e), Bool.or(U32.is_eq(FAR_EL2(), e), U32.is_eq(HPFAR_EL2(), e)))))

type Sr is Data:
  Sr{enc: U32, v: Hv.W64}

def sys_read(+rs: List<&2, Sr>, +e: U32) -> Hv.W64:
  match rs:
    case Nil{}:
      W.of(0)
    case Sr{+k, v} <> t:
      Bool.pick(Hv.W64, U32.is_eq(k, e), v, sys_read(t, e))

# a write is a new entry in front: the newest entry of an encoding wins
def sys_write(+rs: List<&2, Sr>, +e: U32, +v: Hv.W64) -> List<&2, Sr>:
  Sr{e, v} <> rs


# State
# -----

# memory: a doubleword by its 8-aligned address, the newest first;
# absent ones are zero
type Cell is Data:
  Cell{a: Hv.W64, v: Hv.W64}

def mem_read(+m: List<&2, Cell>, +a: Hv.W64) -> Hv.W64:
  match m:
    case Nil{}:
      W.of(0)
    case Cell{+b, v} <> t:
      Bool.pick(Hv.W64, W.is_eq(b, a), v, mem_read(t, a))

def mem_write(m: List<&2, Cell>, a: Hv.W64, v: Hv.W64) -> List<&2, Cell>:
  Cell{a, v} <> m

# the hypervisor's text: read-only words from base, fetched by index
type Rom is Data:
  Rom{base: Hv.W64, size: U32, words: List<&2, U32>}

# the core: x0..x30, the pc, PSTATE (EL, SP select, NZCV, DAIF) and the
# system registers (the stack pointers among them)
type Cpu is Data:
  Cpu{x: List<&2, Hv.W64>, pc: Hv.W64, el: U32, spsel: U32, nzcv: U32, daif: U32, sys: List<&2, Sr>}

# the machine: the core, memory, the text, and the stage-2 map of the
# guest the VTTBR names (the mask Commit writes; SPEC.md, section 9)
type State is Data:
  State{cpu: Cpu, mem: List<&2, Cell>, rom: Rom, s2: Hv.Tree<Bool>}

def State.el(+s: State) -> U32:
  match s:
    case State{Cpu{x, pc, el, spsel, nzcv, daif, sys}, mem, rom, s2}:
      el

def State.mem(+s: State) -> List<&2, Cell>:
  match s:
    case State{cpu, mem, rom, s2}:
      mem

def State.s2(+s: State) -> Hv.Tree<Bool>:
  match s:
    case State{cpu, mem, rom, s2}:
      s2

def State.sys(+s: State) -> List<&2, Sr>:
  match s:
    case State{Cpu{x, pc, el, spsel, nzcv, daif, sys}, mem, rom, s2}:
      sys

def State.pc(+s: State) -> Hv.W64:
  match s:
    case State{Cpu{x, pc, el, spsel, nzcv, daif, sys}, mem, rom, s2}:
      pc

def State.x(+s: State) -> List<&2, Hv.W64>:
  match s:
    case State{Cpu{x, pc, el, spsel, nzcv, daif, sys}, mem, rom, s2}:
      x

def State.cpu(+s: State) -> Cpu:
  match s:
    case State{cpu, mem, rom, s2}:
      cpu

# Stage 2
# -------
# block b of the guest region is the 2 MiB at 0xA0000000 + b * 2 MiB; the
# level-1 entry of the region's GiB is a table, the others are invalid

def Tree.at(-A: Data, +t: Hv.Tree<A>, +d: Nat, +i: U32, +dflt: A) -> A:
  match t d:
    case Hv.Leaf{x} _:
      x
    case Hv.Node{lo, hi} 0n:
      dflt
    case Hv.Node{lo, hi} 1n+p:
      Bool.pick(A, bit(i, p), Tree.at(A, hi, p, i, dflt), Tree.at(A, lo, p, i, dflt))

def in_region(+ipa: Hv.W64) -> Bool:
  Bool.and(U32.is_eq(W.hi(ipa), 0), U32.is_eq(U32.shrn(W.lo(ipa), 27n), 20))

def block_of(+ipa: Hv.W64) -> U32:
  bits(W.lo(ipa), 21n, 63)

# whether stage 2 maps an IPA: in the region, in a block of the mask
def mapped(+s2: Hv.Tree<Bool>, +ipa: Hv.W64) -> Bool:
  Bool.and(in_region(ipa), Tree.at(Bool, s2, Hv.page_depth(), block_of(ipa), False{}))

# the translation-fault level: 2 inside the region's GiB, 1 outside
def fault_level(+ipa: Hv.W64) -> U32:
  Bool.pick(U32, Bool.and(U32.is_eq(W.hi(ipa), 0), U32.is_eq(U32.shrn(W.lo(ipa), 30n), 2)), 2, 1)

# Instructions
# ------------

type Mode is Data:
  Off{}
  Pre{}
  Post{}

type Instr is Data:
  Nop{}
  Wfi{}
  Eret{}
  Ret{rn: U32}
  Hvc{imm: U32}
  Mrs{enc: U32, rt: U32}
  Msr{enc: U32, rt: U32}
  B{off: Hv.W64}
  Bl{off: Hv.W64}
  BCond{cond: U32, off: Hv.W64}
  Movz{sf: Bool, rd: U32, imm: Hv.W64}
  Movk{sf: Bool, rd: U32, hw: U32, imm: U32}
  AddImm{sf: Bool, sub: Bool, flags: Bool, rd: U32, rn: U32, imm: Hv.W64}
  OrrReg{sf: Bool, rd: U32, rn: U32, rm: U32}
  AndReg{sf: Bool, rd: U32, rn: U32, rm: U32}
  Lsl{sf: Bool, rd: U32, rn: U32, sh: U32}
  Lsr{sf: Bool, rd: U32, rn: U32, sh: U32}
  AddReg{sf: Bool, sub: Bool, flags: Bool, rd: U32, rn: U32, rm: U32}
  Ldr{rt: U32, rn: U32, off: Hv.W64, mode: Mode}
  Str{rt: U32, rn: U32, off: Hv.W64, mode: Mode}
  LdrLit{rt: U32, off: Hv.W64}
  Ldp{rt: U32, rt2: U32, rn: U32, off: Hv.W64, mode: Mode}
  Stp{rt: U32, rt2: U32, rn: U32, off: Hv.W64, mode: Mode}
  Undef{w: U32}

def has(+w: U32, +mask: U32, +val: U32) -> Bool:
  U32.is_eq(U32.and(w, mask), val)

def movz_imm(+hw: U32, +imm: U32) -> Hv.W64:
  Bool.pick(Hv.W64, U32.is_eq(hw, 0), Hv.W64{0, imm},
    Bool.pick(Hv.W64, U32.is_eq(hw, 1), Hv.W64{0, U32.shln(imm, 16n)},
      Bool.pick(Hv.W64, U32.is_eq(hw, 2), Hv.W64{imm, 0}, Hv.W64{U32.shln(imm, 16n), 0})))

# MOVK keeps the three halfwords it does not name
def half_set(+w: U32, +top: Bool, +imm: U32) -> U32:
  Bool.pick(U32, top, U32.or(U32.and(w, 65535), U32.shln(imm, 16n)),
    U32.or(U32.and(w, 4294901760), imm))

def movk_at(+old: Hv.W64, +hw: U32, +imm: U32) -> Hv.W64:
  Bool.pick(Hv.W64, U32.is_lt(hw, 2),
    Hv.W64{W.hi(old), half_set(W.lo(old), U32.is_eq(hw, 1), imm)},
    Hv.W64{half_set(W.hi(old), U32.is_eq(hw, 3), imm), W.lo(old)})

# the two aliases of UBFM the shim uses: a shift right is the bitfield
# that ends at the top bit, a shift left the one whose rotate is one
# past its width. Any other UBFM is a Stop, as is a width that does not
# match the operand size.
def decode.ubfm(+w: U32) -> Instr:
  +sf = bit(w, 31n)
  +immr = bits(w, 16n, 63)
  +imms = bits(w, 10n, 63)
  +top = Bool.pick(U32, sf, 63, 31)
  Bool.pick(Instr, Bool.xor(sf, bit(w, 22n)), Undef{w},
    Bool.pick(Instr, U32.is_eq(imms, top),
      Lsr{sf, bits(w, 0n, 31), bits(w, 5n, 31), immr},
      Bool.pick(Instr, U32.is_eq(immr, U32.add(imms, 1)),
        Lsl{sf, bits(w, 0n, 31), bits(w, 5n, 31), U32.sub(top, imms)},
        Undef{w})))

def decode.addimm(+w: U32) -> Instr:
  +imm = bits(w, 10n, 4095)
  AddImm{bit(w, 31n), bit(w, 30n), bit(w, 29n), bits(w, 0n, 31), bits(w, 5n, 31),
    Bool.pick(Hv.W64, bit(w, 22n), W.of(U32.shln(imm, 12n)), W.of(imm))}

def decode.pair(+w: U32, +mode: Mode, +load: Bool) -> Instr:
  +off = W.shl3(W.sext(bits(w, 15n, 127), 7n))
  Bool.pick(Instr, load,
    Ldp{bits(w, 0n, 31), bits(w, 10n, 31), bits(w, 5n, 31), off, mode},
    Stp{bits(w, 0n, 31), bits(w, 10n, 31), bits(w, 5n, 31), off, mode})

def decode.ldst(+w: U32) -> Instr:
  +rt = bits(w, 0n, 31)
  +rn = bits(w, 5n, 31)
  +uoff = W.of(U32.shln(bits(w, 10n, 4095), 3n))
  +soff = W.sext(bits(w, 12n, 511), 9n)
  Bool.pick(Instr, has(w, 4290772992, 4177526784), Str{rt, rn, uoff, Off{}},
  Bool.pick(Instr, has(w, 4290772992, 4181721088), Ldr{rt, rn, uoff, Off{}},
  Bool.pick(Instr, has(w, 4292873216, 4160750592), Str{rt, rn, soff, Post{}},
  Bool.pick(Instr, has(w, 4292873216, 4160752640), Str{rt, rn, soff, Pre{}},
  Bool.pick(Instr, has(w, 4292873216, 4164944896), Ldr{rt, rn, soff, Post{}},
  Bool.pick(Instr, has(w, 4292873216, 4164946944), Ldr{rt, rn, soff, Pre{}},
  Bool.pick(Instr, has(w, 4278190080, 1476395008), LdrLit{rt, W.shl2(W.sext(bits(w, 5n, 524287), 19n))},
  Bool.pick(Instr, has(w, 4290772992, 2835349504), decode.pair(w, Off{}, False{}),
  Bool.pick(Instr, has(w, 4290772992, 2843738112), decode.pair(w, Pre{}, False{}),
  Bool.pick(Instr, has(w, 4290772992, 2826960896), decode.pair(w, Post{}, False{}),
  Bool.pick(Instr, has(w, 4290772992, 2839543808), decode.pair(w, Off{}, True{}),
  Bool.pick(Instr, has(w, 4290772992, 2847932416), decode.pair(w, Pre{}, True{}),
  Bool.pick(Instr, has(w, 4290772992, 2831155200), decode.pair(w, Post{}, True{}),
    Undef{w})))))))))))))

def decode(+w: U32) -> Instr:
  Bool.pick(Instr, U32.is_eq(w, 3573751839), Nop{},
  Bool.pick(Instr, U32.is_eq(w, 3573751935), Wfi{},
  Bool.pick(Instr, has(w, 4294963231, 3573755935), Nop{},
  Bool.pick(Instr, U32.is_eq(w, 3600745440), Eret{},
  Bool.pick(Instr, has(w, 4294966303, 3596550144), Ret{bits(w, 5n, 31)},
  Bool.pick(Instr, has(w, 4292870175, 3556769794), Hvc{bits(w, 5n, 65535)},
  Bool.pick(Instr, has(w, 4293918720, 3576692736), Mrs{bits(w, 5n, 65535), bits(w, 0n, 31)},
  Bool.pick(Instr, has(w, 4293918720, 3574595584), Msr{bits(w, 5n, 65535), bits(w, 0n, 31)},
  Bool.pick(Instr, has(w, 4227858432, 335544320), B{W.shl2(W.sext(bits(w, 0n, 67108863), 26n))},
  Bool.pick(Instr, has(w, 4227858432, 2483027968), Bl{W.shl2(W.sext(bits(w, 0n, 67108863), 26n))},
  Bool.pick(Instr, has(w, 4278190096, 1409286144), BCond{bits(w, 0n, 15), W.shl2(W.sext(bits(w, 5n, 524287), 19n))},
  Bool.pick(Instr, has(w, 2139095040, 1384120320), Movz{bit(w, 31n), bits(w, 0n, 31), movz_imm(bits(w, 21n, 3), bits(w, 5n, 65535))},
  Bool.pick(Instr, has(w, 2139095040, 1920991232), Movk{bit(w, 31n), bits(w, 0n, 31), bits(w, 21n, 3), bits(w, 5n, 65535)},
  Bool.pick(Instr, has(w, 2139095040, 1392508928), decode.ubfm(w),
  Bool.pick(Instr, has(w, 528482304, 285212672), decode.addimm(w),
  Bool.pick(Instr, Bool.and(has(w, 2132803584, 704643072), has(w, 12647424, 0)), OrrReg{bit(w, 31n), bits(w, 0n, 31), bits(w, 5n, 31), bits(w, 16n, 31)},
  Bool.pick(Instr, Bool.and(has(w, 2132803584, 167772160), has(w, 12647424, 0)), AndReg{bit(w, 31n), bits(w, 0n, 31), bits(w, 5n, 31), bits(w, 16n, 31)},
  Bool.pick(Instr, Bool.and(has(w, 522190848, 184549376), has(w, 12647424, 0)), AddReg{bit(w, 31n), bit(w, 30n), bit(w, 29n), bits(w, 0n, 31), bits(w, 5n, 31), bits(w, 16n, 31)},
    decode.ldst(w)))))))))))))))))))


# the address a load or store uses: the base, or the base plus the
# offset unless the form writes back after the access
def ea(+base: Hv.W64, +off: Hv.W64, mode: Mode) -> Hv.W64:
  match mode:
    case Post{}:
      base
    case other:
      W.add(base, off)

# Execution
# ---------
# every def below takes the state as its ten fields and answers the next
# state built once: the fields it does not touch are named once, in the
# call to `out`, and every value it reads is matched before it goes
# there. The scalars (the levels and the flags) are words, so naming one
# twice costs nothing; the registers, the system registers, memory, the
# text and the map are the ones a step must name once.

type Out is Data:
  Run{s: State}
  Stop{why: String, s: State}

def Out.s(+o: Out) -> State:
  match o:
    case Run{s}:
      s
    case Stop{why, s}:
      s

# the next state, and the same with the pc past this instruction

def out(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>) -> Out:
  Run{State{Cpu{x, pc, el, spsel, nzcv, daif, sys}, mem, rom, s2}}

def step_on(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>) -> Out:
  out(x, W.add(pc, W.of(4)), el, spsel, nzcv, daif, sys, mem, rom, s2)

def halt(+why: String, +x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>) -> Out:
  Stop{why, State{Cpu{x, pc, el, spsel, nzcv, daif, sys}, mem, rom, s2}}

def sp_enc(+el: U32, +spsel: U32) -> U32:
  Bool.pick(U32, U32.is_eq(spsel, 0), SP_EL0(),
    Bool.pick(U32, U32.is_eq(el, 2), SP_EL2(), SP_EL1()))

# register n as a source: 31 is the zero register, or the stack pointer
# where the form says so

def xr(+x: List<&2, Hv.W64>, +n: U32) -> Hv.W64:
  Bool.pick(Hv.W64, U32.is_eq(n, 31), W.of(0),
    Maybe.default(&2, Hv.W64, List.get(&2, Hv.W64, x, U32.to_nat(n)), W.of(0)))

def spr(+x: List<&2, Hv.W64>, +sys: List<&2, Sr>, +el: U32, +spsel: U32, +n: U32) -> Hv.W64:
  Bool.pick(Hv.W64, U32.is_eq(n, 31), sys_read(sys, sp_enc(el, spsel)), xr(x, n))

def xw(+x: List<&2, Hv.W64>, +n: U32, v: Hv.W64) -> List<&2, Hv.W64>:
  Bool.pick(List<&2, Hv.W64>, U32.is_eq(n, 31), x, List.set(&2, Hv.W64, x, U32.to_nat(n), v))

# a write to register n, 31 the stack pointer: the value is forced, so
# the registers and the system registers are named once

def spw.go(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +n: U32, +hi: U32, +lo: U32, +sp: Bool) -> Out:
  match sp:
    case True{}:
      step_on(x, pc, el, spsel, nzcv, daif, sys_write(sys, sp_enc(el, spsel), Hv.W64{hi, lo}), mem, rom, s2)
    case False{}:
      step_on(xw(x, n, Hv.W64{hi, lo}), pc, el, spsel, nzcv, daif, sys, mem, rom, s2)

def spw(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +n: U32, v: Hv.W64) -> Out:
  match v:
    case Hv.W64{+hi, +lo}:
      spw.go(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, n, hi, lo, U32.is_eq(n, 31))

def wx(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +n: U32, v: Hv.W64) -> Out:
  match v:
    case Hv.W64{+hi, +lo}:
      step_on(xw(x, n, Hv.W64{hi, lo}), pc, el, spsel, nzcv, daif, sys, mem, rom, s2)

# two registers at once, for a pair

def wx2(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +n1: U32, +n2: U32, v1: Hv.W64, v2: Hv.W64) -> Out:
  match v1 v2:
    case Hv.W64{+h1, +l1} Hv.W64{+h2, +l2}:
      step_on(xw(xw(x, n1, Hv.W64{h1, l1}), n2, Hv.W64{h2, l2}), pc, el, spsel, nzcv, daif, sys, mem, rom, s2)

# PSTATE as an SPSR holds it

def spsr_of(+el: U32, +spsel: U32, +nzcv: U32, +daif: U32) -> Hv.W64:
  W.of(U32.or(U32.shln(nzcv, 28n), U32.or(U32.shln(daif, 6n), U32.or(U32.shln(el, 2n), spsel))))

# Exceptions
# ----------
# an entry to EL2 writes ELR, SPSR and ESR, and for an abort FAR and
# HPFAR; then EL2h with DAIF masked, at VBAR_EL2 plus the vector's offset

# HPFAR_EL2: the faulting IPA's page number, bits 51..12, at bit 4

def hpfar(+a: Hv.W64) -> Hv.W64:
  Hv.W64{U32.shrn(W.hi(a), 8n), U32.or(U32.shln(U32.shrn(W.lo(a), 12n), 4n), U32.shln(W.hi(a), 24n))}

def take.far(sys: List<&2, Sr>, far: Maybe<&2, Hv.W64>) -> List<&2, Sr>:
  match far:
    case None{}:
      sys
    case Some{+a}:
      sys_write(sys_write(sys, FAR_EL2(), a), HPFAR_EL2(), hpfar(a))

def take.go(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +ret: Hv.W64, +esr: U32, far: Maybe<&2, Hv.W64>, +off: U32, +vh: U32, +vl: U32) -> Out:
  out(x, W.add(Hv.W64{vh, vl}, W.of(off)), 2, 1, nzcv, 15,
    take.far(sys_write(sys_write(sys_write(sys, ELR_EL2(), ret), SPSR_EL2(),
      spsr_of(el, spsel, nzcv, daif)), ESR_EL2(), W.of(esr)), far), mem, rom, s2)

def take.at(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +ret: Hv.W64, +esr: U32, far: Maybe<&2, Hv.W64>, +off: U32, vbar: Hv.W64) -> Out:
  match vbar:
    case Hv.W64{+vh, +vl}:
      take.go(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, ret, esr, far, off, vh, vl)

def take(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +off: U32, +ret: Hv.W64, +esr: U32, far: Maybe<&2, Hv.W64>) -> Out:
  take.at(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, ret, esr, far, off, sys_read(sys, VBAR_EL2()))

def EC_WFI() -> U32:
  1

def EC_HVC() -> U32:
  22

def EC_IABT() -> U32:
  32

def EC_DABT() -> U32:
  36

def syndrome(+ec: U32, +iss: U32) -> U32:
  U32.or(U32.shln(ec, 26n), U32.or(33554432, iss))

# a stage-2 translation fault on a data access: WnR, and for a single
# register the valid syndrome: 64-bit (SAS 3), SF, the register

def dabt_iss(single: Maybe<&2, U32>, +write: Bool, +lvl: U32) -> U32:
  match single:
    case None{}:
      U32.or(Bool.pick(U32, write, 64, 0), U32.or(4, lvl))
    case Some{+rt}:
      U32.or(U32.or(16777216, U32.or(12582912, U32.or(U32.shln(rt, 16n), 32768))),
        U32.or(Bool.pick(U32, write, 64, 0), U32.or(4, lvl)))

def dabt(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +ipa: Hv.W64, +write: Bool, single: Maybe<&2, U32>) -> Out:
  take(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, 1024, pc, syndrome(EC_DABT(), dabt_iss(single, write, fault_level(ipa))), Some{ipa})

# Memory access
# -------------
# an access at EL1 goes through stage 2: an unmapped doubleword faults
# and nothing is written. At EL2 an address is physical, and the text
# reads from the rom. Every access is a doubleword and must be aligned.

type Acc is Data:
  Got{v: Hv.W64}
  Abort{ipa: Hv.W64}
  Odd{}

def rom_index(+base: Hv.W64, +size: U32, +a: Hv.W64) -> Maybe<&2, Nat>:
  +d = W.sub(a, base)
  Bool.pick(Maybe<&2, Nat>, Bool.and(U32.is_eq(W.hi(d), 0), U32.is_lt(W.lo(d), size)),
    Some{U32.to_nat(U32.shrn(W.lo(d), 2n))}, None{})

def rom_word(+ws: List<&2, U32>, +i: Nat) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, ws, i), 0)

def rom_pair(+ws: List<&2, U32>, i: Maybe<&2, Nat>) -> Maybe<&2, Hv.W64>:
  match i:
    case None{}:
      None{}
    case Some{+n}:
      Some{Hv.W64{rom_word(ws, Nat.add(n, 1n)), rom_word(ws, n)}}

def rom_read(+r: Rom, +a: Hv.W64) -> Maybe<&2, Hv.W64>:
  match r:
    case Rom{+base, +size, +words}:
      rom_pair(words, rom_index(base, size, a))

def aligned(+a: Hv.W64) -> Bool:
  U32.is_eq(U32.and(W.lo(a), 7), 0)

def load.at(+mem: List<&2, Cell>, +a: Hv.W64, r: Maybe<&2, Hv.W64>) -> Acc:
  match r:
    case None{}:
      Got{mem_read(mem, a)}
    case Some{v}:
      Got{v}

def load.el1(+mem: List<&2, Cell>, +a: Hv.W64, +ok: Bool) -> Acc:
  match ok:
    case False{}:
      Abort{a}
    case True{}:
      Got{mem_read(mem, a)}

def load.go(+el: U32, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +a: Hv.W64, +ok: Bool) -> Acc:
  match ok:
    case False{}:
      Odd{}
    case True{}:
      Bool.pick(Acc, U32.is_eq(el, 2), load.at(mem, a, rom_read(rom, a)),
        load.el1(mem, a, mapped(s2, a)))

# the doubleword at a, or why not

def load(+el: U32, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +a: Hv.W64) -> Acc:
  load.go(el, mem, rom, s2, a, aligned(a))

# whether a store may write a: always at EL2, through stage 2 at EL1

def writable(+el: U32, +s2: Hv.Tree<Bool>, +a: Hv.W64) -> Bool:
  Bool.or(U32.is_eq(el, 2), mapped(s2, a))

# the instruction at the pc: the rom's at EL2, else a half of the
# doubleword the pc names, by its bit 2

def fetch.half(+pc: Hv.W64, v: Hv.W64) -> Maybe<&2, U32>:
  match v:
    case Hv.W64{+hi, +lo}:
      Bool.pick(Maybe<&2, U32>, bit(W.lo(pc), 2n), Some{hi}, Some{lo})

def dword(+a: Hv.W64) -> Hv.W64:
  Hv.W64{W.hi(a), U32.and(W.lo(a), 4294967288)}

def fetch.rom(+mem: List<&2, Cell>, +pc: Hv.W64, i: Maybe<&2, Nat>, +ws: List<&2, U32>) -> Maybe<&2, U32>:
  match i:
    case None{}:
      fetch.half(pc, mem_read(mem, dword(pc)))
    case Some{+n}:
      Some{rom_word(ws, n)}

def fetch.go(+el: U32, +pc: Hv.W64, +mem: List<&2, Cell>, +base: Hv.W64, +size: U32, +ws: List<&2, U32>, +s2: Hv.Tree<Bool>) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, U32.is_eq(el, 2), fetch.rom(mem, pc, rom_index(base, size, pc), ws),
    Bool.pick(Maybe<&2, U32>, mapped(s2, pc), fetch.half(pc, mem_read(mem, dword(pc))), None{}))

def fetch(+el: U32, +pc: Hv.W64, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>) -> Maybe<&2, U32>:
  match rom:
    case Rom{+base, +size, +words}:
      fetch.go(el, pc, mem, base, size, words, s2)

# Arithmetic
# ----------

def flags.v(+sa: Bool, +sb: Bool, +sr: Bool) -> Bool:
  Bool.and(Bool.not(Bool.xor(sa, sb)), Bool.xor(sa, sr))

def flags(+n: Bool, +z: Bool, +c: Bool, +v: Bool) -> U32:
  U32.or(U32.shln(Bool.to_u32(n), 3n), U32.or(U32.shln(Bool.to_u32(z), 2n),
    U32.or(U32.shln(Bool.to_u32(c), 1n), Bool.to_u32(v))))

type AddRes is Data:
  AddRes{r: Hv.W64, nzcv: U32}

def addsub.fin(+sf: Bool, +sub: Bool, +a: Hv.W64, +b0: Hv.W64, +sb: Bool) -> AddRes:
  match sf:
    case True{}:
      +r = Bool.pick(Hv.W64, sub, W.sub(a, b0), W.add(a, b0))
      +carry = Bool.pick(Bool, sub, W.is_ge(a, b0), Bool.not(W.is_ge(r, a)))
      AddRes{r, flags(bit(W.hi(r), 31n), W.is_eq(r, W.of(0)), carry,
        flags.v(bit(W.hi(a), 31n), sb, bit(W.hi(r), 31n)))}
    case False{}:
      +al = W.lo(a)
      +bl = W.lo(b0)
      +r = Bool.pick(U32, sub, U32.sub(al, bl), U32.add(al, bl))
      +carry = Bool.pick(Bool, sub, U32.is_ge(al, bl), U32.is_lt(r, al))
      AddRes{W.of(r), flags(bit(r, 31n), U32.is_eq(r, 0), carry,
        flags.v(bit(al, 31n), sb, bit(r, 31n)))}

# a + b or a - b, 64 or 32 bits, with the flags NZCV

def addsub(+sf: Bool, +sub: Bool, +a: Hv.W64, +b0: Hv.W64) -> AddRes:
  addsub.fin(sf, sub, a, b0, Bool.xor(sub,
    Bool.pick(Bool, sf, bit(W.hi(b0), 31n), bit(W.lo(b0), 31n))))

# condition cond over NZCV

def cond_holds(+c: U32, +nzcv: U32) -> Bool:
  +n = bit(nzcv, 3n)
  +z = bit(nzcv, 2n)
  +cf = bit(nzcv, 1n)
  +v = bit(nzcv, 0n)
  +k = U32.shrn(c, 1n)
  +r = Bool.pick(Bool, U32.is_eq(k, 0), z,
    Bool.pick(Bool, U32.is_eq(k, 1), cf,
    Bool.pick(Bool, U32.is_eq(k, 2), n,
    Bool.pick(Bool, U32.is_eq(k, 3), v,
    Bool.pick(Bool, U32.is_eq(k, 4), Bool.and(cf, Bool.not(z)),
    Bool.pick(Bool, U32.is_eq(k, 5), Bool.not(Bool.xor(n, v)),
    Bool.pick(Bool, U32.is_eq(k, 6), Bool.and(Bool.not(z), Bool.not(Bool.xor(n, v))), True{})))))))
  Bool.pick(Bool, Bool.and(bit(c, 0n), U32.is_ne(c, 15)), Bool.not(r), r)

# Instructions
# ------------
# one def per form, each answering the next state built once

def do_addsub.fin(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +fl: Bool, +sp: Bool, +rd: U32, +r: Hv.W64, +nz: U32) -> Out:
  match fl:
    case True{}:
      match r:
        case Hv.W64{+hi, +lo}:
          step_on(xw(x, rd, Hv.W64{hi, lo}), pc, el, spsel, nz, daif, sys, mem, rom, s2)
    case False{}:
      spw.go(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rd, W.hi(r), W.lo(r), sp)

def do_addsub(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +fl: Bool, +sp: Bool, +rd: U32, res: AddRes) -> Out:
  match res:
    case AddRes{+r, +nz}:
      do_addsub.fin(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, fl, sp, rd, r, nz)

# the address is forced first and then used for the access and for the
# fault, so the registers and the system registers are read once

def do_ldr.back(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +rn: U32, v: Hv.W64, b: Hv.W64) -> Out:
  match v b:
    case Hv.W64{+h, +l} Hv.W64{+bh, +bl}:
      spw.go(xw(x, rt, Hv.W64{h, l}), pc, el, spsel, nzcv, daif, sys, mem, rom, s2,
        rn, bh, bl, U32.is_eq(rn, 31))

def do_ldr.wb(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +rn: U32, +off: Hv.W64, mode: Mode, v: Hv.W64) -> Out:
  match mode:
    case Off{}:
      wx(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, v)
    case other:
      do_ldr.back(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rn, v, W.add(spr(x, sys, el, spsel, rn), off))

def do_ldr(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +rn: U32, +off: Hv.W64, mode: Mode, +a: Hv.W64, r: Acc) -> Out:
  match r:
    case Got{v}:
      do_ldr.wb(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rn, off, mode, v)
    case Abort{+ipa}:
      dabt(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, ipa, False{}, Some{rt})
    case Odd{}:
      halt("an unaligned load", x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2)

# the write-back names the base register, where 31 is the stack pointer
# and not the zero register, so it goes through spw.go as the pair's does

def at_ldr(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +rn: U32, +off: Hv.W64, mode: Mode, a: Hv.W64) -> Out:
  match a:
    case Hv.W64{+ah, +al}:
      do_ldr(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rn, off, mode, Hv.W64{ah, al}, load(el, mem, rom, s2, Hv.W64{ah, al}))

def do_str.back(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rn: U32, +off: Hv.W64, mode: Mode, +a: Hv.W64, +v: Hv.W64, b: Hv.W64) -> Out:
  match b:
    case Hv.W64{+bh, +bl}:
      spw.go(x, pc, el, spsel, nzcv, daif, sys, mem_write(mem, a, v), rom, s2, rn, bh, bl, U32.is_eq(rn, 31))

# a pair: two loads or two stores, the second a doubleword on

def do_str.at(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rn: U32, +off: Hv.W64, mode: Mode, +a: Hv.W64, +v: Hv.W64) -> Out:
  match mode:
    case Off{}:
      step_on(x, pc, el, spsel, nzcv, daif, sys, mem_write(mem, a, v), rom, s2)
    case other:
      do_str.back(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rn, off, mode, a, v, W.add(spr(x, sys, el, spsel, rn), off))

def do_str.wb(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rn: U32, +off: Hv.W64, mode: Mode, a: Hv.W64, v: Hv.W64) -> Out:
  match a v:
    case Hv.W64{+ah, +al} Hv.W64{+vh, +vl}:
      do_str.at(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rn, off, mode, Hv.W64{ah, al}, Hv.W64{vh, vl})

def do_str(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +rn: U32, +off: Hv.W64, mode: Mode, +a: Hv.W64, +v: Hv.W64, +ok: Bool, +odd: Bool) -> Out:
  match ok odd:
    case any False{}:
      halt("an unaligned store", x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2)
    case False{} True{}:
      dabt(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, a, True{}, Some{rt})
    case True{} True{}:
      do_str.wb(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rn, off, mode, a, v)

def at_str(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +rn: U32, +off: Hv.W64, mode: Mode, a: Hv.W64) -> Out:
  match a:
    case Hv.W64{+ah, +al}:
      do_str(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rn, off, mode, Hv.W64{ah, al}, xr(x, rt),
        writable(el, s2, Hv.W64{ah, al}), aligned(Hv.W64{ah, al}))

def do_ldp.back(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +rt2: U32, +rn: U32, v1: Hv.W64, v2: Hv.W64, b: Hv.W64) -> Out:
  match v1 v2 b:
    case Hv.W64{+h1, +l1} Hv.W64{+h2, +l2} Hv.W64{+bh, +bl}:
      spw.go(xw(xw(x, rt, Hv.W64{h1, l1}), rt2, Hv.W64{h2, l2}), pc, el, spsel, nzcv, daif,
        sys, mem, rom, s2, rn, bh, bl, U32.is_eq(rn, 31))

def do_ldp.wb(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +rt2: U32, +rn: U32, +off: Hv.W64, mode: Mode, v1: Hv.W64, v2: Hv.W64) -> Out:
  match mode:
    case Off{}:
      wx2(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, v1, v2)
    case other:
      do_ldp.back(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, v1, v2, W.add(spr(x, sys, el, spsel, rn), off))

def do_ldp(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +rt2: U32, +rn: U32, +off: Hv.W64, mode: Mode, +a: Hv.W64, r1: Acc, r2: Acc) -> Out:
  match r1 r2:
    case Got{v1} Got{v2}:
      do_ldp.wb(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, off, mode, v1, v2)
    case Abort{+ipa} _:
      dabt(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, ipa, False{}, None{})
    case Got{v1} Abort{+ipa}:
      dabt(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, ipa, False{}, None{})
    case Odd{} _:
      halt("an unaligned load", x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2)
    case Got{v1} Odd{}:
      halt("an unaligned load", x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2)

def at_ldp(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +rt2: U32, +rn: U32, +off: Hv.W64, mode: Mode, a: Hv.W64) -> Out:
  match a:
    case Hv.W64{+ah, +al}:
      do_ldp(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, off, mode, Hv.W64{ah, al},
        load(el, mem, rom, s2, Hv.W64{ah, al}),
        load(el, mem, rom, s2, W.add(Hv.W64{ah, al}, W.of(8))))

def do_stp.back(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rn: U32, +off: Hv.W64, mode: Mode, +a: Hv.W64, +v1: Hv.W64, +v2: Hv.W64, b: Hv.W64) -> Out:
  match b:
    case Hv.W64{+bh, +bl}:
      spw.go(x, pc, el, spsel, nzcv, daif, sys,
        mem_write(mem_write(mem, a, v1), W.add(a, W.of(8)), v2), rom, s2, rn, bh, bl, U32.is_eq(rn, 31))

def do_stp.at(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rn: U32, +off: Hv.W64, mode: Mode, +a: Hv.W64, +v1: Hv.W64, +v2: Hv.W64) -> Out:
  match mode:
    case Off{}:
      step_on(x, pc, el, spsel, nzcv, daif, sys,
        mem_write(mem_write(mem, a, v1), W.add(a, W.of(8)), v2), rom, s2)
    case other:
      do_stp.back(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rn, off, mode, a, v1, v2, W.add(spr(x, sys, el, spsel, rn), off))

def do_stp.wb(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +rt2: U32, +rn: U32, +off: Hv.W64, mode: Mode, a: Hv.W64, v1: Hv.W64, v2: Hv.W64) -> Out:
  match a v1 v2:
    case Hv.W64{+ah, +al} Hv.W64{+h1, +l1} Hv.W64{+h2, +l2}:
      do_stp.at(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rn, off, mode, Hv.W64{ah, al}, Hv.W64{h1, l1}, Hv.W64{h2, l2})

def do_stp(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +rt2: U32, +rn: U32, +off: Hv.W64, mode: Mode, +a: Hv.W64, +v1: Hv.W64, +v2: Hv.W64, +ok: Bool, +odd: Bool) -> Out:
  match ok odd:
    case any False{}:
      halt("an unaligned store", x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2)
    case False{} True{}:
      dabt(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, a, True{}, None{})
    case True{} True{}:
      do_stp.wb(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, off, mode, a, v1, v2)

def at_stp(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +rt2: U32, +rn: U32, +off: Hv.W64, mode: Mode, a: Hv.W64) -> Out:
  match a:
    case Hv.W64{+ah, +al}:
      do_stp(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, off, mode, Hv.W64{ah, al}, xr(x, rt), xr(x, rt2),
        Bool.and(writable(el, s2, Hv.W64{ah, al}),
          writable(el, s2, W.add(Hv.W64{ah, al}, W.of(8)))),
        aligned(Hv.W64{ah, al}))

def do_mrs(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +rt: U32, +k: U32, +ok: Bool) -> Out:
  match ok:
    case False{}:
      halt("mrs of an EL2 register at EL1", x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2)
    case True{}:
      wx(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, sys_read(sys, k))

def do_msr.go(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +k: U32, +hi: U32, +lo: U32) -> Out:
  step_on(x, pc, el, spsel, nzcv, daif, sys_write(sys, k, Hv.W64{hi, lo}), mem, rom, s2)

def do_msr.at(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +k: U32, v: Hv.W64) -> Out:
  match v:
    case Hv.W64{+hi, +lo}:
      do_msr.go(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, k, hi, lo)

def do_msr(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +k: U32, +rt: U32, +ok: Bool) -> Out:
  match ok:
    case False{}:
      halt("msr of an EL2 register at EL1", x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2)
    case True{}:
      do_msr.at(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, k, xr(x, rt))

# ERET: the pc from ELR_EL2, PSTATE from SPSR_EL2, both forced

def do_eret.go(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +eh: U32, +el2: U32, +p: U32) -> Out:
  out(x, Hv.W64{eh, el2}, bits(p, 2n, 3), bits(p, 0n, 1), bits(p, 28n, 15), bits(p, 6n, 15), sys, mem, rom, s2)

def do_eret.at(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, e: Hv.W64, spsr: Hv.W64) -> Out:
  match e spsr:
    case Hv.W64{+eh, +el2} Hv.W64{ph, +pl}:
      do_eret.go(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, eh, el2, pl)

def do_eret(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>) -> Out:
  do_eret.at(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, sys_read(sys, ELR_EL2()), sys_read(sys, SPSR_EL2()))

def do_jump.at(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, v: Hv.W64) -> Out:
  match v:
    case Hv.W64{+hi, +lo}:
      out(x, Hv.W64{hi, lo}, el, spsel, nzcv, daif, sys, mem, rom, s2)

def do_bcond(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +off: Hv.W64, +take: Bool) -> Out:
  match take:
    case True{}:
      do_jump.at(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, W.add(pc, off))
    case False{}:
      step_on(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2)

def do_bl(+x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>, +off: Hv.W64) -> Out:
  out(xw(x, 30, W.add(pc, W.of(4))), W.add(pc, off), el, spsel, nzcv, daif, sys, mem, rom, s2)

def exec(i: Instr, +x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>) -> Out:
  match i:
    case Nop{}:
      step_on(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2)
    case Wfi{}:
      Bool.pick(Out, U32.is_eq(el, 2), halt("wfi at EL2", x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2),
        take(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, 1024, pc, syndrome(EC_WFI(), 31457280), None{}))
    case Eret{}:
      Bool.pick(Out, U32.is_eq(el, 2), do_eret(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2), halt("eret at EL1", x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2))
    case Ret{+rn}:
      do_jump.at(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, xr(x, rn))
    case Hvc{+imm}:
      Bool.pick(Out, U32.is_eq(el, 2), halt("hvc at EL2", x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2),
        take(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, 1024, W.add(pc, W.of(4)), syndrome(EC_HVC(), imm), None{}))
    case Mrs{+k, +rt}:
      do_mrs(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, k, Bool.or(U32.is_eq(el, 2), el1_ok(k)))
    case Msr{+k, +rt}:
      do_msr(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, k, rt, Bool.or(U32.is_eq(el, 2), el1_ok(k)))
    case B{+off}:
      do_jump.at(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, W.add(pc, off))
    case Bl{+off}:
      do_bl(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, off)
    case BCond{+cond, +off}:
      do_bcond(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, off, cond_holds(cond, nzcv))
    case Movz{sf, +rd, +imm}:
      wx(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rd, imm)
    case Movk{+sf, +rd, +hw, +imm}:
      wx(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rd, Bool.pick(Hv.W64, sf, movk_at(xr(x, rd), hw, imm), W.w(movk_at(W.w(xr(x, rd)), hw, imm))))
    case AddImm{+sf, +sub, +fl, +rd, +rn, +imm}:
      do_addsub(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, fl, U32.is_eq(rd, 31), rd, addsub(sf, sub, spr(x, sys, el, spsel, rn), imm))
    case AddReg{+sf, +sub, +fl, +rd, +rn, +rm}:
      do_addsub(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, fl, False{}, rd, addsub(sf, sub, xr(x, rn), xr(x, rm)))
    case OrrReg{+sf, +rd, +rn, +rm}:
      wx(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rd, Bool.pick(Hv.W64, sf, W.or(xr(x, rn), xr(x, rm)), W.w(W.or(xr(x, rn), xr(x, rm)))))
    case AndReg{+sf, +rd, +rn, +rm}:
      wx(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rd, Bool.pick(Hv.W64, sf, W.and(xr(x, rn), xr(x, rm)), W.w(W.and(xr(x, rn), xr(x, rm)))))
    case Lsl{+sf, +rd, +rn, +sh}:
      wx(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rd, Bool.pick(Hv.W64, sf, W.shl_by(xr(x, rn), sh), W.w(W.shl_by(W.w(xr(x, rn)), sh))))
    case Lsr{+sf, +rd, +rn, +sh}:
      wx(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rd, Bool.pick(Hv.W64, sf, W.shr_by(xr(x, rn), sh), W.w(W.shr_by(W.w(xr(x, rn)), sh))))
    case Ldr{+rt, +rn, +off, +mode}:
      at_ldr(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rn, off, mode, ea(spr(x, sys, el, spsel, rn), off, mode))
    case Str{+rt, +rn, +off, +mode}:
      at_str(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rn, off, mode, ea(spr(x, sys, el, spsel, rn), off, mode))
    case LdrLit{+rt, +off}:
      at_ldr(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, 31, W.of(0), Off{}, W.add(pc, off))
    case Ldp{+rt, +rt2, +rn, +off, +mode}:
      at_ldp(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, off, mode, ea(spr(x, sys, el, spsel, rn), off, mode))
    case Stp{+rt, +rt2, +rn, +off, +mode}:
      at_stp(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, rt, rt2, rn, off, mode, ea(spr(x, sys, el, spsel, rn), off, mode))
    case Undef{w}:
      halt("an instruction the model lacks: " ++ U32.hex(w), x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2)

# Step
# ----
# fetch at the pc (through stage 2 at EL1: an unmapped pc is an
# instruction abort), decode, execute

def step.at(w: Maybe<&2, U32>, +x: List<&2, Hv.W64>, +pc: Hv.W64, +el: U32, +spsel: U32, +nzcv: U32, +daif: U32, +sys: List<&2, Sr>, +mem: List<&2, Cell>, +rom: Rom, +s2: Hv.Tree<Bool>) -> Out:
  match w:
    case None{}:
      take(x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2, 1024, pc, syndrome(EC_IABT(), U32.or(4, fault_level(pc))), Some{pc})
    case Some{+i}:
      exec(decode(i), x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2)

def step(+s: State) -> Out:
  match s:
    case State{Cpu{x, +pc, +el, spsel, nzcv, daif, sys}, mem, rom, s2}:
      step.at(fetch(el, pc, mem, rom, s2), x, pc, el, spsel, nzcv, daif, sys, mem, rom, s2)

# steps until the core is at EL2 again (an exit), a Stop, or no fuel

def run_guest.fin(o: Out, k: State -> Out) -> Out:
  match o:
    case Run{+s}:
      Bool.pick(Out, U32.is_eq(State.el(s), 2), Run{s}, k(s))
    case Stop{why, s}:
      Stop{why, s}

def run_guest(fuel: Nat, +s: State) -> Out:
  match fuel:
    case 0n:
      Stop{"out of fuel", s}
    case 1n+f:
      run_guest.fin(step(s), s2 => run_guest(f, s2))

# n steps, at any EL, stopping early at a Stop

def steps(n: Nat, o: Out) -> Out:
  match n o:
    case 0n _:
      o
    case 1n+p Run{+s}:
      steps(p, step(s))
    case 1n+p Stop{why, s}:
      Stop{why, s}
