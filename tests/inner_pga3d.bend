# Inner products on PGA3D blades over exact integers, with gax's
# definitions: e1 | e1 = 1; e1 ⌋ e12 = e2; e12 ⌊ e2 = e1; e12 | e12 = -1;
# e1 | e123 = e23 (the fat dot of a vector and a trivector); the scalar
# product of e12 with itself is -1; e0 squares to 0, so e0 | e0 = 0.
# The halved products: e12 x e1 = (e12 e1 - e1 e12)/2 = -e2, and
# e1 o e1 = (e1 e1 + e1 e1)/2 = 1.
import Base
import ../src/int.bend as I
import ../algebras/pga3d/kinds.bend as K
import ../algebras/pga3d/ops.bend as O

def i(n: Nat) -> I.Int:
  I.IPos{n}

def z() -> I.Int:
  I.IPos{0n}

def e1() -> K.Plane<I.Int>:
  K.Plane{i(1n), z(), z(), z()}

def e2() -> K.Plane<I.Int>:
  K.Plane{z(), i(1n), z(), z()}

def e0() -> K.Plane<I.Int>:
  K.Plane{z(), z(), z(), i(1n)}

def e12() -> K.Line<I.Int>:
  K.Line{z(), z(), i(1n), z(), z(), z()}

def e123() -> K.Point<I.Int>:
  K.Point{z(), z(), z(), i(1n)}

def Scalar.show(x: K.Scalar<I.Int>) -> String:
  match x:
    case K.Scalar{s}:
      I.Int.show(s)

def Plane.show(x: K.Plane<I.Int>) -> String:
  match x:
    case K.Plane{a, b, c, d}:
      "[" ++ I.Int.show(a) ++ ", " ++ I.Int.show(b) ++ ", " ++ I.Int.show(c) ++ "; " ++ I.Int.show(d) ++ "]"

def Line.show(x: K.Line<I.Int>) -> String:
  match x:
    case K.Line{a, b, c, d, e, f}:
      "[" ++ I.Int.show(a) ++ ", " ++ I.Int.show(b) ++ ", " ++ I.Int.show(c) ++ "; " ++ I.Int.show(d) ++ ", " ++ I.Int.show(e) ++ ", " ++ I.Int.show(f) ++ "]"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Scalar.show(O.Plane.dot.Plane(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, e1(), e1())))
    IO.print(Plane.show(O.Plane.lc.Line(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, e1(), e12())))
    IO.print(Plane.show(O.Line.rc.Plane(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, e12(), e2())))
    IO.print(Scalar.show(O.Line.dot.Line(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, e12(), e12())))
    IO.print(Line.show(O.Plane.dot.Point(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, e1(), e123())))
    IO.print(Scalar.show(O.Line.scalar_product.Line(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, e12(), e12())))
    IO.print(Scalar.show(O.Plane.dot.Plane(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, e0(), e0())))
    IO.print(Plane.show(O.Line.commutator.Plane(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, e12(), e1())))
    IO.print(Scalar.show(O.Plane.anticommutator.Plane(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, e1(), e1())))
#|1
#|[0, 1, 0; 0]
#|[1, 0, 0; 0]
#|-1
#|[1, 0, 0; 0, 0, 0]
#|-1
#|0
#|[0, -1, 0; 0]
#|1
