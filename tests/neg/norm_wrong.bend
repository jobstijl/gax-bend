# Negative control for the normaliser: (x + y)(x + y) = x x + y y is false,
# so the checker's cancellation must leave the two xy monomials and fail.
import Base
import ../../src/ring.bend as R
import ../../src/norm.bend as N
import ../../proofs/norm.bend as P

def v0() -> N.Tm:
  N.TVar{0n}

def v1() -> N.Tm:
  N.TVar{1n}

def v2() -> N.Tm:
  N.TVar{2n}

# wrong: (x + y)(x + y) = x x + y y (the 2xy is missing)
def sum_square_wrong(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg),
  +a: T, +b: T)
  -> {mul(add(a, b), add(a, b)) == add(mul(a, a), mul(b, b)) : T}:
  P.Norm.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a, b],
    N.TMul{N.TAdd{v0(), v1()}, N.TAdd{v0(), v1()}},
    N.TAdd{N.TMul{v0(), v0()}, N.TMul{v1(), v1()}},
    {==})
