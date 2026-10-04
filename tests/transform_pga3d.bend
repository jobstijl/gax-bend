# Sandwiches on PGA3D over exact integers (gax's conventions: a point is
# x e032 + y e013 + z e021 + w e123; a translator is 1 - (d e0i)/2).
# Checks: a translation by (2, 0, 0) moves (1, 2, 3) to (3, 2, 3); a half
# turn about the z axis (the rotor e12) moves it to (-1, -2, 3); the plain
# sandwich by the plane x = 0 (e1) reflects it to (-1, 2, 3); the motor
# 1 - e01 moves the plane x - 1 = 0 to x - 3 = 0.
import Base
import ../src/int.bend as I
import ../algebras/pga3d/kinds.bend as K
import ../algebras/pga3d/ops.bend as O

def i(n: Nat) -> I.Int:
  I.IPos{n}

def m(n: Nat) -> I.Int:
  I.Int.neg(I.IPos{n})

def z() -> I.Int:
  I.IPos{0n}

def p() -> K.Point<I.Int>:
  K.Point{i(1n), i(2n), i(3n), i(1n)}

def Point.show(x: K.Point<I.Int>) -> String:
  match x:
    case K.Point{a, b, c, w}:
      "(" ++ I.Int.show(a) ++ ", " ++ I.Int.show(b) ++ ", " ++ I.Int.show(c) ++ "; " ++ I.Int.show(w) ++ ")"

def Plane.show(x: K.Plane<I.Int>) -> String:
  match x:
    case K.Plane{a, b, c, d}:
      "[" ++ I.Int.show(a) ++ ", " ++ I.Int.show(b) ++ ", " ++ I.Int.show(c) ++ "; " ++ I.Int.show(d) ++ "]"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Point.show(O.Translator.transform.Point(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg,
      K.Translator{i(1n), m(1n), z(), z()}, p())))
    IO.print(Point.show(O.Rotor.transform.Point(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg,
      K.Rotor{z(), z(), z(), i(1n)}, p())))
    IO.print(Point.show(O.Plane.transform.Point(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg,
      K.Plane{i(1n), z(), z(), z()}, p())))
    IO.print(Plane.show(O.Motor.transform.Plane(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg,
      K.Motor{i(1n), z(), z(), z(), m(1n), z(), z(), z()}, K.Plane{i(1n), z(), z(), m(1n)})))
#|(3, 2, 3; 1)
#|(-1, -2, 3; 1)
#|(-1, 2, 3; 1)
#|[1, 0, 0; -3]
