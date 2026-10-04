# CSTA over exact integers (gax's null basis: e1 e2 e3 square to 1, e4 to
# -1, eo . ei = -1; an event is x + (x²/2) ei + eo with the Minkowski
# square x² = x1² + x2² + x3² - x4²). Checks:
# - eo ei = -1 + eo ^ ei;
# - the event (1, 1, 0, 0) squares to zero;
# - the event (1, 1, 1, 1) (x² = 2, the time part counting negatively)
#   squares to zero too;
# - the translator 1 - e1i moves (1, 1, 0, 0) to (3, 1, 0, 0): x² = 10.
import Base
import ../src/int.bend as I
import ../algebras/csta/kinds.bend as K
import ../algebras/csta/ops.bend as O

def i(n: Nat) -> I.Int:
  I.IPos{n}

def z() -> I.Int:
  I.IPos{0n}

def m1() -> I.Int:
  I.Int.neg(I.IPos{1n})

def ev(a: Nat, b: Nat, c: Nat, t: Nat, h: Nat) -> K.Vector<I.Int>:
  K.Vector{i(a), i(b), i(c), i(t), i(1n), i(h)}

def Even.s_eoi(x: K.Even<I.Int>) -> String:
  match x:
    case K.Even{s, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, oi, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16}:
      "s " ++ I.Int.show(s) ++ ", eoi " ++ I.Int.show(oi)

def Odd.vec(x: K.Odd<I.Int>) -> String:
  match x:
    case K.Odd{a, b, c, t, o, h, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26}:
      "[" ++ I.Int.show(a) ++ ", " ++ I.Int.show(b) ++ ", " ++ I.Int.show(c) ++ ", " ++ I.Int.show(t) ++ "; o " ++ I.Int.show(o) ++ ", i " ++ I.Int.show(h) ++ "]"

def gp(a: K.Vector<I.Int>, b: K.Vector<I.Int>) -> K.Even<I.Int>:
  O.Vector.gp.Vector(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, a, b)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Even.s_eoi(gp(K.Vector{z(), z(), z(), z(), i(1n), z()}, K.Vector{z(), z(), z(), z(), z(), i(1n)})))
    IO.print(Even.s_eoi(gp(ev(1n, 1n, 0n, 0n, 1n), ev(1n, 1n, 0n, 0n, 1n))))
    IO.print(Even.s_eoi(gp(ev(1n, 1n, 1n, 1n, 1n), ev(1n, 1n, 1n, 1n, 1n))))
    IO.print(Odd.vec(O.Motor.transform.Vector(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg,
      K.Motor{i(1n), z(), z(), z(), z(), z(), z(), m1(), z(), z(), z(), z(), z(), z(), z(), z()}, ev(1n, 1n, 0n, 0n, 1n))))
#|s -1, eoi 1
#|s 0, eoi 0
#|s 0, eoi 0
#|[3, 1, 0, 0; o 1, i 5]
