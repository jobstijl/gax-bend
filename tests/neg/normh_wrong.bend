# Negative control for the half-aware normaliser: with h + h = 1,
# h a + h h a is (3/4) a, not a, so the lifted monomials must not cancel.
import Base
import ../../src/ring.bend as R
import ../../src/norm.bend as N
import ../../proofs/norm.bend as P

def v0() -> N.Tm:
  N.TVar{0n}

def v1() -> N.Tm:
  N.TVar{1n}

def wrong(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg),
  ~half: T, ~hh: {add(half, half) == one : T}, +a: T)
  -> {add(mul(half, a), mul(half, mul(half, a))) == a : T}:
  P.NormH.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a, half], 1n,
    N.TAdd{N.TMul{v1(), v0()}, N.TMul{v1(), N.TMul{v1(), v0()}}}, v0(), hh, {==})
