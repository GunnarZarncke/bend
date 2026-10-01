# hypervisor: the proofs of SHIM_LAWS.bend: the guest's slot is a
# literal, and each run is the whole of one path, which Segments.bend has
# already cut into segments the kernel can check (gen_seg.sh writes it;
# SPEC.md, section 14). See SHIM_LAWS.bend on the laws themselves.

import Base
import ./main.bend as Hv
import ./Isa.bend as I
import ./Lemmas.bend as L
import ./Shim.bend as Shim
import ./SHIM_LAWS.bend as Laws
import ./Chain.bend as C
import ./Segments.bend as S

def enter.k0(h: Shim.Host, +nzcv: U32, +daif: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, f: Shim.Saved, s2: Hv.Tree<Bool>) -> {Shim.entered(I.steps(68n, I.Run{Shim.enter_state(0, h, nzcv, daif, sys, mem, f, s2)})) == Shim.entered.want(0, h, f) : Maybe<&2, Shim.Entered>}:
  S.en0_law(h, nzcv, daif, sys, mem, f, s2)

def exit_sync.k0(h: Shim.Host, +nzcv: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, f: Shim.Saved, s2: Hv.Tree<Bool>) -> {Shim.exited(0, I.steps(80n, I.Run{Shim.exit_state(0, 1024, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(0, h, f) : Maybe<&2, Shim.Exited>}:
  S.xs0_law(h, nzcv, 0, sys, mem, f, s2)

def exit_irq.k0(h: Shim.Host, +nzcv: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, f: Shim.Saved, s2: Hv.Tree<Bool>) -> {Shim.exited(0, I.steps(80n, I.Run{Shim.exit_state(0, 1152, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(1, h, f) : Maybe<&2, Shim.Exited>}:
  S.xi0_law(h, nzcv, 0, sys, mem, f, s2)

def enter.k1(h: Shim.Host, +nzcv: U32, +daif: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, f: Shim.Saved, s2: Hv.Tree<Bool>) -> {Shim.entered(I.steps(68n, I.Run{Shim.enter_state(1, h, nzcv, daif, sys, mem, f, s2)})) == Shim.entered.want(1, h, f) : Maybe<&2, Shim.Entered>}:
  S.en1_law(h, nzcv, daif, sys, mem, f, s2)

def exit_sync.k1(h: Shim.Host, +nzcv: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, f: Shim.Saved, s2: Hv.Tree<Bool>) -> {Shim.exited(1, I.steps(80n, I.Run{Shim.exit_state(1, 1024, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(0, h, f) : Maybe<&2, Shim.Exited>}:
  S.xs1_law(h, nzcv, 0, sys, mem, f, s2)

def exit_irq.k1(h: Shim.Host, +nzcv: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, f: Shim.Saved, s2: Hv.Tree<Bool>) -> {Shim.exited(1, I.steps(80n, I.Run{Shim.exit_state(1, 1152, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(1, h, f) : Maybe<&2, Shim.Exited>}:
  S.xi1_law(h, nzcv, 0, sys, mem, f, s2)

def enter.k2(h: Shim.Host, +nzcv: U32, +daif: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, f: Shim.Saved, s2: Hv.Tree<Bool>) -> {Shim.entered(I.steps(68n, I.Run{Shim.enter_state(2, h, nzcv, daif, sys, mem, f, s2)})) == Shim.entered.want(2, h, f) : Maybe<&2, Shim.Entered>}:
  S.en2_law(h, nzcv, daif, sys, mem, f, s2)

def exit_sync.k2(h: Shim.Host, +nzcv: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, f: Shim.Saved, s2: Hv.Tree<Bool>) -> {Shim.exited(2, I.steps(80n, I.Run{Shim.exit_state(2, 1024, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(0, h, f) : Maybe<&2, Shim.Exited>}:
  S.xs2_law(h, nzcv, 0, sys, mem, f, s2)

def exit_irq.k2(h: Shim.Host, +nzcv: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, f: Shim.Saved, s2: Hv.Tree<Bool>) -> {Shim.exited(2, I.steps(80n, I.Run{Shim.exit_state(2, 1152, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(1, h, f) : Maybe<&2, Shim.Exited>}:
  S.xi2_law(h, nzcv, 0, sys, mem, f, s2)

def enter.k3(h: Shim.Host, +nzcv: U32, +daif: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, f: Shim.Saved, s2: Hv.Tree<Bool>) -> {Shim.entered(I.steps(68n, I.Run{Shim.enter_state(3, h, nzcv, daif, sys, mem, f, s2)})) == Shim.entered.want(3, h, f) : Maybe<&2, Shim.Entered>}:
  S.en3_law(h, nzcv, daif, sys, mem, f, s2)

def exit_sync.k3(h: Shim.Host, +nzcv: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, f: Shim.Saved, s2: Hv.Tree<Bool>) -> {Shim.exited(3, I.steps(80n, I.Run{Shim.exit_state(3, 1024, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(0, h, f) : Maybe<&2, Shim.Exited>}:
  S.xs3_law(h, nzcv, 0, sys, mem, f, s2)

def exit_irq.k3(h: Shim.Host, +nzcv: U32, sys: List<&2, I.Sr>, mem: List<&2, I.Cell>, f: Shim.Saved, s2: Hv.Tree<Bool>) -> {Shim.exited(3, I.steps(80n, I.Run{Shim.exit_state(3, 1152, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(1, h, f) : Maybe<&2, Shim.Exited>}:
  S.xi3_law(h, nzcv, 0, sys, mem, f, s2)

def enter.go(-g: U32, v: L.Lt4<g>, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +f: Shim.Saved, +s2: Hv.Tree<Bool>) -> {Shim.entered(I.steps(68n, I.Run{Shim.enter_state(g, h, nzcv, daif, sys, mem, f, s2)})) == Shim.entered.want(g, h, f) : Maybe<&2, Shim.Entered>}:
  match v:
    case L.K0{e}:
      %e : {Shim.entered(I.steps(68n, I.Run{Shim.enter_state(_, h, nzcv, daif, sys, mem, f, s2)})) == Shim.entered.want(_, h, f) : Maybe<&2, Shim.Entered>}
      enter.k0(h, nzcv, daif, sys, mem, f, s2)
    case L.K1{e}:
      %e : {Shim.entered(I.steps(68n, I.Run{Shim.enter_state(_, h, nzcv, daif, sys, mem, f, s2)})) == Shim.entered.want(_, h, f) : Maybe<&2, Shim.Entered>}
      enter.k1(h, nzcv, daif, sys, mem, f, s2)
    case L.K2{e}:
      %e : {Shim.entered(I.steps(68n, I.Run{Shim.enter_state(_, h, nzcv, daif, sys, mem, f, s2)})) == Shim.entered.want(_, h, f) : Maybe<&2, Shim.Entered>}
      enter.k2(h, nzcv, daif, sys, mem, f, s2)
    case L.K3{e}:
      %e : {Shim.entered(I.steps(68n, I.Run{Shim.enter_state(_, h, nzcv, daif, sys, mem, f, s2)})) == Shim.entered.want(_, h, f) : Maybe<&2, Shim.Entered>}
      enter.k3(h, nzcv, daif, sys, mem, f, s2)

def exit_sync.go(-g: U32, v: L.Lt4<g>, +h: Shim.Host, +nzcv: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +f: Shim.Saved, +s2: Hv.Tree<Bool>) -> {Shim.exited(g, I.steps(80n, I.Run{Shim.exit_state(g, 1024, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(0, h, f) : Maybe<&2, Shim.Exited>}:
  match v:
    case L.K0{e}:
      %e : {Shim.exited(_, I.steps(80n, I.Run{Shim.exit_state(_, 1024, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(0, h, f) : Maybe<&2, Shim.Exited>}
      exit_sync.k0(h, nzcv, sys, mem, f, s2)
    case L.K1{e}:
      %e : {Shim.exited(_, I.steps(80n, I.Run{Shim.exit_state(_, 1024, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(0, h, f) : Maybe<&2, Shim.Exited>}
      exit_sync.k1(h, nzcv, sys, mem, f, s2)
    case L.K2{e}:
      %e : {Shim.exited(_, I.steps(80n, I.Run{Shim.exit_state(_, 1024, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(0, h, f) : Maybe<&2, Shim.Exited>}
      exit_sync.k2(h, nzcv, sys, mem, f, s2)
    case L.K3{e}:
      %e : {Shim.exited(_, I.steps(80n, I.Run{Shim.exit_state(_, 1024, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(0, h, f) : Maybe<&2, Shim.Exited>}
      exit_sync.k3(h, nzcv, sys, mem, f, s2)

def exit_irq.go(-g: U32, v: L.Lt4<g>, +h: Shim.Host, +nzcv: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +f: Shim.Saved, +s2: Hv.Tree<Bool>) -> {Shim.exited(g, I.steps(80n, I.Run{Shim.exit_state(g, 1152, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(1, h, f) : Maybe<&2, Shim.Exited>}:
  match v:
    case L.K0{e}:
      %e : {Shim.exited(_, I.steps(80n, I.Run{Shim.exit_state(_, 1152, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(1, h, f) : Maybe<&2, Shim.Exited>}
      exit_irq.k0(h, nzcv, sys, mem, f, s2)
    case L.K1{e}:
      %e : {Shim.exited(_, I.steps(80n, I.Run{Shim.exit_state(_, 1152, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(1, h, f) : Maybe<&2, Shim.Exited>}
      exit_irq.k1(h, nzcv, sys, mem, f, s2)
    case L.K2{e}:
      %e : {Shim.exited(_, I.steps(80n, I.Run{Shim.exit_state(_, 1152, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(1, h, f) : Maybe<&2, Shim.Exited>}
      exit_irq.k2(h, nzcv, sys, mem, f, s2)
    case L.K3{e}:
      %e : {Shim.exited(_, I.steps(80n, I.Run{Shim.exit_state(_, 1152, h, nzcv, sys, mem, f, s2)})) == Shim.exited.want(1, h, f) : Maybe<&2, Shim.Exited>}
      exit_irq.k3(h, nzcv, sys, mem, f, s2)

def Laws.shim_enter(g, sg, h, nzcv, daif, sys, mem, f, s2):
  enter.go(g, L.lt4(g, sg), h, nzcv, daif, sys, mem, f, s2)

def Laws.shim_exit_sync(g, sg, h, nzcv, sys, mem, f, s2):
  exit_sync.go(g, L.lt4(g, sg), h, nzcv, sys, mem, f, s2)

def Laws.shim_exit_irq(g, sg, h, nzcv, sys, mem, f, s2):
  exit_irq.go(g, L.lt4(g, sg), h, nzcv, sys, mem, f, s2)

# Decide
# ------
# hv_decide's five answers. The run splits at the shift that reads the
# exception class out of the ESR: one step reaches it, and from a state
# whose class is a literal the branches below it reduce, which they
# cannot while it is a shift of a variable. Segments.bend holds the arms;
# these defs put the step in front of the arm. The class is the caller's
# to bring, which is what SHIM_LAWS asks for.

def decide.cut(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +ar: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lr: Hv.W64)
  -> {I.Run{Shim.decide_mid(I.W.shr_by(esr, 26), esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr)}
      == I.steps(1n, I.Run{Shim.decide_state(esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr)}) : I.Out}:
  match esr h:
    case Hv.W64{+eh, +el} Shim.Host{Hv.W64{+h2h, +h2l}, Hv.W64{+h3h, +h3l}, Hv.W64{+h4h, +h4l}, Hv.W64{+h5h, +h5l}, Hv.W64{+h6h, +h6l}, Hv.W64{+h7h, +h7l}, Hv.W64{+h8h, +h8l}, Hv.W64{+h9h, +h9l}, Hv.W64{+h10h, +h10l}, Hv.W64{+h11h, +h11l}, Hv.W64{+h12h, +h12l}, Hv.W64{+h13h, +h13l}, Hv.W64{+h14h, +h14l}, Hv.W64{+h15h, +h15l}, Hv.W64{+h16h, +h16l}, Hv.W64{+h17h, +h17l}, Hv.W64{+h18h, +h18l}, Hv.W64{+h19h, +h19l}, Hv.W64{+h20h, +h20l}, Hv.W64{+h21h, +h21l}, Hv.W64{+h22h, +h22l}, Hv.W64{+h23h, +h23l}, Hv.W64{+h24h, +h24l}, Hv.W64{+h25h, +h25l}, Hv.W64{+h26h, +h26l}, Hv.W64{+h27h, +h27l}, Hv.W64{+h28h, +h28l}, Hv.W64{+h29h, +h29l}, Hv.W64{+h30h, +h30l}}:
      {==}

def decide.hvc.at(+esr: Hv.W64, +fh: U32, +fl: U32, +ph: U32, +pl: U32, +ar: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lh: U32, +ll: U32, +cls: {Hv.W64{0, 22} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.decided(I.steps(10n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})) == Shim.decided.want(1, I.W.of(0), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}:
  %Equal.sym(I.Out, I.steps(10n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})}), I.steps(9n, I.steps(1n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})), C.steps_add(1n, 9n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})) : {Shim.decided(_) == Shim.decided.want(1, I.W.of(0), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}
  %decide.cut(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll}) : {Shim.decided(I.steps(9n, _)) == Shim.decided.want(1, I.W.of(0), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}
  %cls : {Shim.decided(I.steps(9n, I.Run{Shim.decide_mid(_, esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})) == Shim.decided.want(1, I.W.of(0), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}
  S.dh_law(esr, fh, fl, ph, pl, ar, h, nzcv, daif, sys, mem, s2, lh, ll)

def decide.hvc(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +ar: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lr: Hv.W64, +cls: {Hv.W64{0, 22} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.decided(I.steps(10n, I.Run{Shim.decide_state(esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr)})) == Shim.decided.want(1, I.W.of(0), lr) : Maybe<&2, Shim.Decided>}:
  match fault hpfar lr:
    case Hv.W64{+fh, +fl} Hv.W64{+ph, +pl} Hv.W64{+lh, +ll}:
      decide.hvc.at(esr, fh, fl, ph, pl, ar, h, nzcv, daif, sys, mem, s2, lh, ll, cls)

def decide.data.at(+esr: Hv.W64, +fh: U32, +fl: U32, +ph: U32, +pl: U32, +ar: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lh: U32, +ll: U32, +cls: {Hv.W64{0, 36} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.decided(I.steps(18n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})) == Shim.decided.want(2, Shim.fault_at(Hv.W64{fh, fl}, Hv.W64{ph, pl}), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}:
  %Equal.sym(I.Out, I.steps(18n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})}), I.steps(17n, I.steps(1n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})), C.steps_add(1n, 17n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})) : {Shim.decided(_) == Shim.decided.want(2, Shim.fault_at(Hv.W64{fh, fl}, Hv.W64{ph, pl}), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}
  %decide.cut(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll}) : {Shim.decided(I.steps(17n, _)) == Shim.decided.want(2, Shim.fault_at(Hv.W64{fh, fl}, Hv.W64{ph, pl}), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}
  %cls : {Shim.decided(I.steps(17n, I.Run{Shim.decide_mid(_, esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})) == Shim.decided.want(2, Shim.fault_at(Hv.W64{fh, fl}, Hv.W64{ph, pl}), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}
  S.dd_law(esr, fh, fl, ph, pl, ar, h, nzcv, daif, sys, mem, s2, lh, ll)

def decide.data(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +ar: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lr: Hv.W64, +cls: {Hv.W64{0, 36} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.decided(I.steps(18n, I.Run{Shim.decide_state(esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr)})) == Shim.decided.want(2, Shim.fault_at(fault, hpfar), lr) : Maybe<&2, Shim.Decided>}:
  match fault hpfar lr:
    case Hv.W64{+fh, +fl} Hv.W64{+ph, +pl} Hv.W64{+lh, +ll}:
      decide.data.at(esr, fh, fl, ph, pl, ar, h, nzcv, daif, sys, mem, s2, lh, ll, cls)

def decide.inst.at(+esr: Hv.W64, +fh: U32, +fl: U32, +ph: U32, +pl: U32, +ar: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lh: U32, +ll: U32, +cls: {Hv.W64{0, 32} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.decided(I.steps(20n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})) == Shim.decided.want(3, Shim.fault_at(Hv.W64{fh, fl}, Hv.W64{ph, pl}), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}:
  %Equal.sym(I.Out, I.steps(20n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})}), I.steps(19n, I.steps(1n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})), C.steps_add(1n, 19n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})) : {Shim.decided(_) == Shim.decided.want(3, Shim.fault_at(Hv.W64{fh, fl}, Hv.W64{ph, pl}), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}
  %decide.cut(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll}) : {Shim.decided(I.steps(19n, _)) == Shim.decided.want(3, Shim.fault_at(Hv.W64{fh, fl}, Hv.W64{ph, pl}), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}
  %cls : {Shim.decided(I.steps(19n, I.Run{Shim.decide_mid(_, esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})) == Shim.decided.want(3, Shim.fault_at(Hv.W64{fh, fl}, Hv.W64{ph, pl}), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}
  S.di_law(esr, fh, fl, ph, pl, ar, h, nzcv, daif, sys, mem, s2, lh, ll)

def decide.inst(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +ar: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lr: Hv.W64, +cls: {Hv.W64{0, 32} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.decided(I.steps(20n, I.Run{Shim.decide_state(esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr)})) == Shim.decided.want(3, Shim.fault_at(fault, hpfar), lr) : Maybe<&2, Shim.Decided>}:
  match fault hpfar lr:
    case Hv.W64{+fh, +fl} Hv.W64{+ph, +pl} Hv.W64{+lh, +ll}:
      decide.inst.at(esr, fh, fl, ph, pl, ar, h, nzcv, daif, sys, mem, s2, lh, ll, cls)

def decide.other.at(+esr: Hv.W64, +fh: U32, +fl: U32, +ph: U32, +pl: U32, +ar: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lh: U32, +ll: U32, +cls: {Hv.W64{0, 24} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.decided(I.steps(15n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})) == Shim.decided.want(5, I.W.of(0), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}:
  %Equal.sym(I.Out, I.steps(15n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})}), I.steps(14n, I.steps(1n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})), C.steps_add(1n, 14n, I.Run{Shim.decide_state(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})) : {Shim.decided(_) == Shim.decided.want(5, I.W.of(0), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}
  %decide.cut(esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll}) : {Shim.decided(I.steps(14n, _)) == Shim.decided.want(5, I.W.of(0), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}
  %cls : {Shim.decided(I.steps(14n, I.Run{Shim.decide_mid(_, esr, Hv.W64{fh, fl}, Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})})) == Shim.decided.want(5, I.W.of(0), Hv.W64{lh, ll}) : Maybe<&2, Shim.Decided>}
  S.do_law(esr, fh, fl, ph, pl, ar, h, nzcv, daif, sys, mem, s2, lh, ll)

def decide.other(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +ar: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lr: Hv.W64, +cls: {Hv.W64{0, 24} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.decided(I.steps(15n, I.Run{Shim.decide_state(esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr)})) == Shim.decided.want(5, I.W.of(0), lr) : Maybe<&2, Shim.Decided>}:
  match fault hpfar lr:
    case Hv.W64{+fh, +fl} Hv.W64{+ph, +pl} Hv.W64{+lh, +ll}:
      decide.other.at(esr, fh, fl, ph, pl, ar, h, nzcv, daif, sys, mem, s2, lh, ll, cls)

def decide.own0.at(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +eh: U32, +el: U32, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lh: U32, +ll: U32, +cls: {Hv.W64{0, 1} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.stepped(0, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(0), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(0), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}:
  %Equal.sym(I.Out, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(0), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(0), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})}), I.steps(18n, I.steps(1n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(0), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(0), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})), C.steps_add(1n, 18n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(0), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(0), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})) : {Shim.stepped(0, _) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}
  %decide.cut(esr, fault, hpfar, Shim.area(0), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(0), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll}) : {Shim.stepped(0, I.steps(18n, _)) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}
  %cls : {Shim.stepped(0, I.steps(18n, I.Run{Shim.decide_mid(_, esr, fault, hpfar, Shim.area(0), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(0), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}
  S.ow0_law(esr, fault, hpfar, eh, el, h, nzcv, daif, sys, mem, s2, lh, ll)

def decide.own0(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +elr: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lr: Hv.W64, +cls: {Hv.W64{0, 1} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.stepped(0, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(0), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(0), 264), elr} <> mem, s2, lr)})) == Shim.stepped.want(elr, lr) : Maybe<&2, Shim.Stepped>}:
  match elr lr:
    case Hv.W64{+eh, +el} Hv.W64{+lh, +ll}:
      decide.own0.at(esr, fault, hpfar, eh, el, h, nzcv, daif, sys, mem, s2, lh, ll, cls)

def decide.own1.at(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +eh: U32, +el: U32, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lh: U32, +ll: U32, +cls: {Hv.W64{0, 1} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.stepped(1, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(1), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(1), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}:
  %Equal.sym(I.Out, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(1), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(1), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})}), I.steps(18n, I.steps(1n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(1), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(1), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})), C.steps_add(1n, 18n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(1), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(1), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})) : {Shim.stepped(1, _) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}
  %decide.cut(esr, fault, hpfar, Shim.area(1), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(1), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll}) : {Shim.stepped(1, I.steps(18n, _)) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}
  %cls : {Shim.stepped(1, I.steps(18n, I.Run{Shim.decide_mid(_, esr, fault, hpfar, Shim.area(1), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(1), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}
  S.ow1_law(esr, fault, hpfar, eh, el, h, nzcv, daif, sys, mem, s2, lh, ll)

def decide.own1(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +elr: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lr: Hv.W64, +cls: {Hv.W64{0, 1} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.stepped(1, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(1), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(1), 264), elr} <> mem, s2, lr)})) == Shim.stepped.want(elr, lr) : Maybe<&2, Shim.Stepped>}:
  match elr lr:
    case Hv.W64{+eh, +el} Hv.W64{+lh, +ll}:
      decide.own1.at(esr, fault, hpfar, eh, el, h, nzcv, daif, sys, mem, s2, lh, ll, cls)

def decide.own2.at(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +eh: U32, +el: U32, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lh: U32, +ll: U32, +cls: {Hv.W64{0, 1} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.stepped(2, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(2), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(2), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}:
  %Equal.sym(I.Out, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(2), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(2), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})}), I.steps(18n, I.steps(1n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(2), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(2), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})), C.steps_add(1n, 18n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(2), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(2), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})) : {Shim.stepped(2, _) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}
  %decide.cut(esr, fault, hpfar, Shim.area(2), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(2), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll}) : {Shim.stepped(2, I.steps(18n, _)) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}
  %cls : {Shim.stepped(2, I.steps(18n, I.Run{Shim.decide_mid(_, esr, fault, hpfar, Shim.area(2), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(2), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}
  S.ow2_law(esr, fault, hpfar, eh, el, h, nzcv, daif, sys, mem, s2, lh, ll)

def decide.own2(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +elr: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lr: Hv.W64, +cls: {Hv.W64{0, 1} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.stepped(2, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(2), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(2), 264), elr} <> mem, s2, lr)})) == Shim.stepped.want(elr, lr) : Maybe<&2, Shim.Stepped>}:
  match elr lr:
    case Hv.W64{+eh, +el} Hv.W64{+lh, +ll}:
      decide.own2.at(esr, fault, hpfar, eh, el, h, nzcv, daif, sys, mem, s2, lh, ll, cls)

def decide.own3.at(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +eh: U32, +el: U32, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lh: U32, +ll: U32, +cls: {Hv.W64{0, 1} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.stepped(3, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(3), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(3), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}:
  %Equal.sym(I.Out, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(3), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(3), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})}), I.steps(18n, I.steps(1n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(3), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(3), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})), C.steps_add(1n, 18n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(3), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(3), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})) : {Shim.stepped(3, _) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}
  %decide.cut(esr, fault, hpfar, Shim.area(3), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(3), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll}) : {Shim.stepped(3, I.steps(18n, _)) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}
  %cls : {Shim.stepped(3, I.steps(18n, I.Run{Shim.decide_mid(_, esr, fault, hpfar, Shim.area(3), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(3), 264), Hv.W64{eh, el}} <> mem, s2, Hv.W64{lh, ll})})) == Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll}) : Maybe<&2, Shim.Stepped>}
  S.ow3_law(esr, fault, hpfar, eh, el, h, nzcv, daif, sys, mem, s2, lh, ll)

def decide.own3(+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +elr: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lr: Hv.W64, +cls: {Hv.W64{0, 1} == I.W.shr_by(esr, 26) : Hv.W64})
  -> {Shim.stepped(3, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(3), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(3), 264), elr} <> mem, s2, lr)})) == Shim.stepped.want(elr, lr) : Maybe<&2, Shim.Stepped>}:
  match elr lr:
    case Hv.W64{+eh, +el} Hv.W64{+lh, +ll}:
      decide.own3.at(esr, fault, hpfar, eh, el, h, nzcv, daif, sys, mem, s2, lh, ll, cls)

def decide.own.go(-g: U32, v: L.Lt4<g>, +esr: Hv.W64, +cls: {Hv.W64{0, 1} == I.W.shr_by(esr, 26) : Hv.W64}, +fault: Hv.W64, +hpfar: Hv.W64, +elr: Hv.W64, +h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>, +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lr: Hv.W64)
  -> {Shim.stepped(g, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(g), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(g), 264), elr} <> mem, s2, lr)})) == Shim.stepped.want(elr, lr) : Maybe<&2, Shim.Stepped>}:
  match v:
    case L.K0{e}:
      %e : {Shim.stepped(_, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(_), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(_), 264), elr} <> mem, s2, lr)})) == Shim.stepped.want(elr, lr) : Maybe<&2, Shim.Stepped>}
      decide.own0(esr, fault, hpfar, elr, h, nzcv, daif, sys, mem, s2, lr, cls)
    case L.K1{e}:
      %e : {Shim.stepped(_, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(_), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(_), 264), elr} <> mem, s2, lr)})) == Shim.stepped.want(elr, lr) : Maybe<&2, Shim.Stepped>}
      decide.own1(esr, fault, hpfar, elr, h, nzcv, daif, sys, mem, s2, lr, cls)
    case L.K2{e}:
      %e : {Shim.stepped(_, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(_), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(_), 264), elr} <> mem, s2, lr)})) == Shim.stepped.want(elr, lr) : Maybe<&2, Shim.Stepped>}
      decide.own2(esr, fault, hpfar, elr, h, nzcv, daif, sys, mem, s2, lr, cls)
    case L.K3{e}:
      %e : {Shim.stepped(_, I.steps(19n, I.Run{Shim.decide_state(esr, fault, hpfar, Shim.area(_), h, nzcv, daif, sys, I.Cell{Shim.at(Shim.area(_), 264), elr} <> mem, s2, lr)})) == Shim.stepped.want(elr, lr) : Maybe<&2, Shim.Stepped>}
      decide.own3(esr, fault, hpfar, elr, h, nzcv, daif, sys, mem, s2, lr, cls)

def Laws.shim_decide_hvc(esr, cls, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr):
  decide.hvc(esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr, cls)

def Laws.shim_decide_data(esr, cls, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr):
  decide.data(esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr, cls)

def Laws.shim_decide_inst(esr, cls, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr):
  decide.inst(esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr, cls)

def Laws.shim_decide_other(esr, cls, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr):
  decide.other(esr, fault, hpfar, ar, h, nzcv, daif, sys, mem, s2, lr, cls)

def Laws.shim_decide_own(g, sg, esr, cls, fault, hpfar, elr, h, nzcv, daif, sys, mem, s2, lr):
  decide.own.go(g, L.lt4(g, sg), esr, cls, fault, hpfar, elr, h, nzcv, daif, sys, mem, s2, lr)
