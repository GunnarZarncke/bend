# A string a program rebuilds, rather than consumes, kills the run past
# about twenty thousand characters: `bend: memory fault (machine stack
# overflow?)`. 11264 characters answer and so do 22528; 45056 do not.
# The C lane and the JS lane both die, at the same length. It is not the
# heap: the corpus reserves 8 GiB and the run stays near 180 MB of it,
# and `ulimit -s` does not move it. Consuming one is fine, however long:
# String.length of 180224 characters answers.
#
# String.split and String.to_upper have the same cliff, so a program
# that reads some tens of kilobytes and writes them back out cannot be
# Bend today. demos/hypervisor/gen_seg.sh is shell for this reason.
#
# This test FAILS, on purpose: it reproduces the fault rather than
# pinning it. When the runtime answers both lines it passes as it
# stands, and this paragraph goes.
import Base

law rep:
  for +n: Nat
  for +s: String
  String

def rep(n, s):
  match n:
    case 0n:
      s
    case 1n+p:
      rep(p, String.append(s, s))

law upto:
  for s: String
  String

def upto(s):
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      Bool.pick(String, Char.is_eq(c, 'x'), SNil{}, SCon{c, upto(t)})

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    IO.print(Nat.show(String.length(upto(rep(11n, "abcdefghijy")))))
    IO.print(Nat.show(String.length(upto(rep(12n, "abcdefghijy")))))

#|22528
#|45056
