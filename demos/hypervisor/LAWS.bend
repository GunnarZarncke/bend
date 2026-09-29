# hypervisor: the laws. The human states them; PROOF.bend must prove
# them. They are stated over the model in main.bend: what the hardware
# does under a stage-2 map and a saved register file is the axiom the
# model rests on (SPEC.md, section 2).

import Base
import ./main.bend as Hv

# LAW: two guests' stage-2 maps share no block: for every ownership list
# and every two distinct guests, the masks the kernel commits are
# disjoint
law masks_disjoint:
  for  ps: List<&2, Hv.Owner>
  for +g : Nat
  for +h : Nat
  for +ne: {Nat.is_ne(g, h) == True{} : Bool}
  {Hv.disjoint(Hv.mask_of(ps, g), Hv.mask_of(ps, h)) == True{} : Bool}

# LAW: a decision changes no vCPU but the current guest's: whatever exit
# the current guest takes, every other guest's saved window and live bit
# are what they were
law handle_frame:
  for +k : Hv.Kernel
  for +m : Hv.Machine
  for +e : Hv.Exit
  for +g : Nat
  for +ne: {Nat.is_ne(g, Hv.Machine.cur(m)) == True{} : Bool}
  {Hv.vcpu_at(Hv.Step.vcpus(Hv.handle(k, m, e)), g) == Hv.vcpu_at(Hv.Machine.vcpus(m), g) : Hv.VCpu}
