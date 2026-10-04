# STAP over exact integers (gax's projective spacetime: an event is
# x e0324 + y e0134 + z e0214 + t e0123 + w e1234). Checks:
# - the translator 1 - e01 moves the event (1, 2, 3, 4) by 2 along x, and
#   the motor's other parts of the result vanish;
# - the boost generator e41 squares to +1, a rotation's e12 to -1.
import Base
import ../src/int.bend as I
import ../algebras/stap/kinds.bend as K
import ../algebras/stap/ops.bend as O

def i(n: Nat) -> I.Int:
  I.IPos{n}

def z() -> I.Int:
  I.IPos{0n}

def Motor.show(x: K.Motor<I.Int>) -> String:
  match x:
    case K.Motor{s, a1, a2, a3, a4, b1, b2, b3, c1, c2, c3, x0, x1, x2, x3, w}:
      "event (" ++ I.Int.show(x0) ++ ", " ++ I.Int.show(x1) ++ ", " ++ I.Int.show(x2) ++ ", " ++ I.Int.show(x3) ++ "; " ++ I.Int.show(w) ++ ") rest "
        ++ I.Int.show(s) ++ I.Int.show(a1) ++ I.Int.show(a2) ++ I.Int.show(a3) ++ I.Int.show(a4) ++ I.Int.show(b1) ++ I.Int.show(b2) ++ I.Int.show(b3)
        ++ I.Int.show(c1) ++ I.Int.show(c2) ++ I.Int.show(c3)

def Motor.s(x: K.Motor<I.Int>) -> String:
  match x:
    case K.Motor{s, a1, a2, a3, a4, b1, b2, b3, c1, c2, c3, x0, x1, x2, x3, w}:
      I.Int.show(s)

def bv(e41: Nat, e12: Nat) -> K.Bivector<I.Int>:
  K.Bivector{z(), z(), z(), z(), z(), z(), i(e12), i(e41), z(), z()}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Motor.show(O.Motor.transform.Quadvector(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg,
      K.Motor{i(1n), I.Int.neg(i(1n)), z(), z(), z(), z(), z(), z(), z(), z(), z(), z(), z(), z(), z(), z()},
      K.Quadvector{i(1n), i(2n), i(3n), i(4n), i(1n)})))
    IO.print(Motor.s(O.Bivector.gp.Bivector(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, bv(1n, 0n), bv(1n, 0n))))
    IO.print(Motor.s(O.Bivector.gp.Bivector(~I.Int, ~z(), ~I.Int.add, ~I.Int.mul, ~I.Int.neg, bv(0n, 1n), bv(0n, 1n))))
#|event (3, 2, 3, 4; 1) rest 00000000000
#|1
#|-1
