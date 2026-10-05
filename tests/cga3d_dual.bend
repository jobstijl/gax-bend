# CGA3D dual and undual are gax's metric-free complements on the null
# basis (algebras/cga3d: .ok against S.MV.rcomp/lcomp on the raw blade
# tree). Values against gax's generated code (gax-bend's reference,
# crates/gax/src/algebras/cga3d/conversions.rs): Vector -> [1, 2, 3, 5, -4];
# Twist -> [-4, -5, -6, 0, 0, 0, 1, 2, 3, 0]; Bivector -> [-7, -8, -9, 4,
# 5, 6, 1, 2, 3, 10]; Trivector -> [7, 8, 9, 4, 5, 6, -1, -2, -3, 10].
# Undual after dual is the identity.
import Base
import ../src/int.bend as I
import ../algebras/cga3d/kinds.bend as K
import ../algebras/cga3d/ops.bend as O

def shows(xs: List<&2, I.Int>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      I.Int.show(x) <> shows(t)

def show(xs: List<&2, I.Int>) -> String:
  "[" ++ String.join(shows(xs), ", ") ++ "]"

def n(k: Nat) -> I.Int:
  I.IPos{k}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show(K.Quadvector.fields(I.Int, O.Vector.dual(~I.Int, ~n(0n), ~I.Int.neg, K.Vector{n(1n), n(2n), n(3n), n(4n), n(5n)}))))
    IO.print(show(K.Trivector.fields(I.Int, O.Twist.dual(~I.Int, ~n(0n), ~I.Int.neg, K.Twist{n(1n), n(2n), n(3n), n(4n), n(5n), n(6n)}))))
    IO.print(show(K.Trivector.fields(I.Int, O.Bivector.dual(~I.Int, ~n(0n), ~I.Int.neg, K.Bivector{n(1n), n(2n), n(3n), n(4n), n(5n), n(6n), n(7n), n(8n), n(9n), n(10n)}))))
    IO.print(show(K.Bivector.fields(I.Int, O.Trivector.dual(~I.Int, ~n(0n), ~I.Int.neg, K.Trivector{n(1n), n(2n), n(3n), n(4n), n(5n), n(6n), n(7n), n(8n), n(9n), n(10n)}))))
    IO.print(show(K.Trivector.fields(I.Int, O.Bivector.undual(~I.Int, ~n(0n), ~I.Int.neg, O.Trivector.dual(~I.Int, ~n(0n), ~I.Int.neg, K.Trivector{n(1n), n(2n), n(3n), n(4n), n(5n), n(6n), n(7n), n(8n), n(9n), n(10n)})))))
#|[1, 2, 3, 5, -4]
#|[-4, -5, -6, 0, 0, 0, 1, 2, 3, 0]
#|[-7, -8, -9, 4, 5, 6, 1, 2, 3, 10]
#|[7, 8, 9, 4, 5, 6, -1, -2, -3, 10]
#|[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
