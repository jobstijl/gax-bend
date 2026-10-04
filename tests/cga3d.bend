# CGA3D over exact integers (gax's null basis: eo . ei = -1, a point is
# x + (x²/2) ei + eo). Checks:
# - eo ei = -1 + eo ^ ei (the scalar part and the eoi part of the product);
# - the point (1, 1, 0), i.e. e1 + e2 + ei + eo, squares to zero;
# - the translator 1 - e1i (by (2, 0, 0)) moves it to (3, 1, 0): 3 e1 + e2 + 5 ei + eo;
# - the inner product of two points is minus half their squared distance:
#   (1, 1, 0) and (3, 1, 0) give -2.
import Base
import ../src/int.bend as I
import ../algebras/cga3d/kinds.bend as K
import ../algebras/cga3d/ops.bend as O

def i(n: Nat) -> I.Int:
  I.IPos{n}

def m(n: Nat) -> I.Int:
  I.Int.neg(I.IPos{n})

def z() -> I.Int:
  I.IPos{0n}

def eo() -> K.Vector<I.Int>:
  K.Vector{z(), z(), z(), i(1n), z()}

def ei() -> K.Vector<I.Int>:
  K.Vector{z(), z(), z(), z(), i(1n)}

def p() -> K.Vector<I.Int>:
  K.Vector{i(1n), i(1n), z(), i(1n), i(1n)}

def q() -> K.Vector<I.Int>:
  K.Vector{i(3n), i(1n), z(), i(1n), i(5n)}

def Vector.show(x: K.Vector<I.Int>) -> String:
  match x:
    case K.Vector{a, b, c, o, n}:
      "[" ++ I.Int.show(a) ++ ", " ++ I.Int.show(b) ++ ", " ++ I.Int.show(c) ++ "; o " ++ I.Int.show(o) ++ ", i " ++ I.Int.show(n) ++ "]"

# the vector part of an odd element, and whether the rest is zero
def Odd.show(x: K.Odd<I.Int>) -> String:
  match x:
    case K.Odd{a, b, c, o, n, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, ps}:
      "[" ++ I.Int.show(a) ++ ", " ++ I.Int.show(b) ++ ", " ++ I.Int.show(c) ++ "; o " ++ I.Int.show(o) ++ ", i " ++ I.Int.show(n) ++ "] rest "
        ++ I.Int.show(t1) ++ I.Int.show(t2) ++ I.Int.show(t3) ++ I.Int.show(t4) ++ I.Int.show(t5) ++ I.Int.show(t6) ++ I.Int.show(t7)
        ++ I.Int.show(t8) ++ I.Int.show(t9) ++ I.Int.show(t10) ++ I.Int.show(ps)

def Even.s_eoi(x: K.Even<I.Int>) -> String:
  match x:
    case K.Even{s, a1, a2, a3, a4, a5, a6, a7, a8, a9, oi, b1, b2, b3, b4, b5}:
      "s " ++ I.Int.show(s) ++ ", eoi " ++ I.Int.show(oi)

def Scalar.show(x: K.Scalar<I.Int>) -> String:
  match x:
    case K.Scalar{s}:
      I.Int.show(s)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Even.s_eoi(O.Vector.gp.Vector(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, eo(), ei())))
    IO.print(Even.s_eoi(O.Vector.gp.Vector(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, p(), p())))
    IO.print(Odd.show(O.Motor.transform.Vector(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg,
      K.Motor{i(1n), z(), z(), z(), m(1n), z(), z(), z()}, p())))
    IO.print(Scalar.show(O.Vector.dot.Vector(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, p(), q())))
#|s -1, eoi 1
#|s 0, eoi 0
#|[3, 1, 0; o 1, i 5] rest 00000000000
#|-2
