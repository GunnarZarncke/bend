# A string a program rebuilds, rather than consumes, kills the JS lane
# past about twenty thousand characters: `bend: memory fault (machine
# stack overflow?)`, under bun and under node. 22528 characters answer;
# 45056 do not. It is the JS call stack, not memory: the runtime turns a
# RangeError into that message, and `node --stack-size=60000` answers
# both lines. The C lane answers both, and 1441792 characters as well.
# Consuming one is fine on every lane, however long: String.length of
# 180224 characters answers.
#
# String.to_upper has the same cliff, so a program
# that reads some tens of kilobytes and writes them back out cannot run
# under `bend` or as JS today.
#
# This test FAILS on the JS lane, on purpose: it reproduces the fault
# rather than pinning it. When that lane answers both lines it passes as
# it stands, and this paragraph goes.
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
