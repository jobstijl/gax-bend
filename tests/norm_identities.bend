# The cancellation normaliser at work: identities of every commutative ring,
# each proven by reifying both sides and letting the checker cancel them
# (proofs/norm.bend). The negative control tests/neg/norm_wrong.bend claims
# a false one.
import Base
import ../src/ring.bend as R
import ../src/norm.bend as N
import ../proofs/norm.bend as P

def v0() -> N.Tm:
  N.TVar{0n}

def v1() -> N.Tm:
  N.TVar{1n}

def v2() -> N.Tm:
  N.TVar{2n}

# (x + y)(x - y) = x x - y y
def diff_squares(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg),
  +a: T, +b: T)
  -> {mul(add(a, b), add(a, neg(b))) == add(mul(a, a), neg(mul(b, b))) : T}:
  P.Norm.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a, b],
    N.TMul{N.TAdd{v0(), v1()}, N.TAdd{v0(), N.TNeg{v1()}}},
    N.TAdd{N.TMul{v0(), v0()}, N.TNeg{N.TMul{v1(), v1()}}},
    {==})

# a cyclic sum that cancels: x(y - z) + y(z - x) + z(x - y) = 0
def cyclic(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg),
  +a: T, +b: T, +c: T)
  -> {add(add(mul(a, add(b, neg(c))), mul(b, add(c, neg(a)))), mul(c, add(a, neg(b)))) == zero : T}:
  P.Norm.zero(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a, b, c],
    N.TAdd{N.TAdd{N.TMul{v0(), N.TAdd{v1(), N.TNeg{v2()}}}, N.TMul{v1(), N.TAdd{v2(), N.TNeg{v0()}}}}, N.TMul{v2(), N.TAdd{v0(), N.TNeg{v1()}}}},
    {==})
# with h + h = 1: h a + h a = a
def half_double(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg),
  ~half: T, ~hh: {add(half, half) == one : T}, +a: T)
  -> {add(mul(half, a), mul(half, a)) == a : T}:
  P.NormH.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a, half], 1n,
    N.TAdd{N.TMul{v1(), v0()}, N.TMul{v1(), v0()}}, v0(), hh, {==})

# with h + h = 1: (h a)(b + b) = a b, as in CGA's eo . ei
def half_null(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg),
  ~half: T, ~hh: {add(half, half) == one : T}, +a: T, +b: T)
  -> {mul(mul(half, a), add(b, b)) == mul(a, b) : T}:
  P.NormH.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a, b, half], 2n,
    N.TMul{N.TMul{v2(), v0()}, N.TAdd{v1(), v1()}}, N.TMul{v0(), v1()}, hh, {==})
#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
