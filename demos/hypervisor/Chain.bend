# hypervisor: the two facts that join the segments of a run. A run of
# m+n steps is a run of m and then a run of n, so a path cut into
# segments is the path.

import Base
import ./main.bend as Hv
import ./Isa.bend as I

# a stopped run stays stopped, however many steps are asked of it
def steps_stop(n: Nat, +why: String, +s: I.State) -> {I.steps(n, I.Stop{why, s}) == I.Stop{why, s} : I.Out}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def steps_add(m: Nat, +n: Nat, o: I.Out) -> {I.steps(Nat.add(m, n), o) == I.steps(n, I.steps(m, o)) : I.Out}:
  match m o:
    case 0n oo:
      {==}
    case 1n+p I.Run{+s}:
      steps_add(p, n, I.step(s))
    case 1n+p I.Stop{+why, +s}:
      Equal.sym(I.Out, I.steps(n, I.Stop{why, s}), I.Stop{why, s}, steps_stop(n, why, s))
