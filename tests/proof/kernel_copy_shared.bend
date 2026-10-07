# A term that names its input twice, n deep, is linear for bend2, which
# shares, and a power of two for the BendTT kernel, which substitutes
# without sharing. bend2 checks this claim at 24 steps, and at 60, in
# 0.06 s; --verdict takes 0.3 s at 16 steps, 4 s at 20, and from 22 the
# kernel runs out of its 400M fuel, which --verdict reports as a
# mismatch between the two checkers rather than as fuel. Nothing warns of
# it before then: a model a proof runs symbolically (a machine's state,
# each step reading the step before) meets it at a handful of steps.
#
# This test FAILS the verdict gate, on purpose: bend2 checks it and the
# kernel does not. When the kernel shares a copied argument, or bend2
# charges a proof the cost the kernel will pay, it passes as it stands,
# and this paragraph goes.
import Base

type P is Data:
  P{a: U32}

def step(s: P) -> P:
  match s:
    case P{+a}:
      P{U32.add(a, a)}

def run(+n: Nat, s: P) -> P:
  match n:
    case 0n:
      s
    case 1n+p:
      run(p, step(s))

def get(s: P) -> U32:
  match s:
    case P{+a}:
      a

def twice(+y: U32) -> U32:
  U32.add(y, y)

def dbl(+n: Nat, x: U32) -> U32:
  match n:
    case 0n:
      x
    case 1n+p:
      twice(dbl(p, x))

law doubles:
  for +x: U32
  {get(run(24n, P{x})) == dbl(24n, x) : U32}

def doubles(x):
  {==}

def main() -> U32:
  get(run(24n, P{1}))

#|16777216
