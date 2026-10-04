# NEGATIVE CONTROL: a kernel with one flipped sign must not prove equal to
# the spec. Same shape as the generated Scalar.gp.Plane.ok.
import Base
import ../../src/spec.bend as S
import ../../algebras/pga3d/kinds.bend as K

def wrong(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, a: K.Scalar<T>, b: K.Plane<T>) -> K.Plane<T>:
  match a b:
    case K.Scalar{+a_s} K.Plane{+b_e1, +b_e2, +b_e3, +b_e0}:
      K.Plane{mul(a_s, b_e1), mul(a_s, b_e2), neg(mul(a_s, b_e3)), mul(a_s, b_e0)}

def wrong.ok(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, a: K.Scalar<T>, b: K.Plane<T>)
  -> {K.Plane.of_tree(~T, ~zero, ~neg, S.MV.gp(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Scalar.tree(~T, ~neg, a), K.Plane.tree(~T, ~neg, b)))
      == wrong(~T, ~zero, ~add, ~mul, ~neg, a, b) : K.Plane<T>}:
  match a b:
    case K.Scalar{a_s} K.Plane{b_e1, b_e2, b_e3, b_e0}:
      {==}
