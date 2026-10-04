# Dual numbers over a commutative ring are a commutative ring
# (src/dual.bend): each law is two identities over T, one per part,
# proven by the normaliser under T's ring laws.

import Base
import ../src/ring.bend as R
import ../src/norm.bend as N
import ../src/dual.bend as DU
import ./norm.bend as NP

def V(i: Nat) -> N.Tm:
  N.TVar{i}

def Ml(a: N.Tm, b: N.Tm) -> N.Tm:
  N.TMul{a, b}

def Ad(a: N.Tm, b: N.Tm) -> N.Tm:
  N.TAdd{a, b}

def Ng(a: N.Tm) -> N.Tm:
  N.TNeg{a}

def Dual.ext(-T: Data, -a1: T, -a2: T, -b1: T, -b2: T, e1: {a1 == a2 : T}, e2: {b1 == b2 : T}) -> {DU.Dual{a1, b1} == DU.Dual{a2, b2} : DU.Dual<T>}:
  %e1 : {DU.Dual{a1, b1} == DU.Dual{_, b2} : DU.Dual<T>}
  %e2 : {DU.Dual{a1, b1} == DU.Dual{a1, _} : DU.Dual<T>}
  {==}

def Dual.add_assoc(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +x: DU.Dual<T>, +y: DU.Dual<T>, +w: DU.Dual<T>)
  -> {DU.Dual.add(~T, ~add, DU.Dual.add(~T, ~add, x, y), w) == DU.Dual.add(~T, ~add, x, DU.Dual.add(~T, ~add, y, w)) : DU.Dual<T>}:
  match x y w:
    case DU.Dual{+a, +b} DU.Dual{+c, +d} DU.Dual{+e, +f}:
      Dual.ext(T, add(add(a, c), e), add(a, add(c, e)), add(add(b, d), f), add(b, add(d, f)), aa(a, c, e), aa(b, d, f))

def Dual.add_comm(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +x: DU.Dual<T>, +y: DU.Dual<T>) -> {DU.Dual.add(~T, ~add, x, y) == DU.Dual.add(~T, ~add, y, x) : DU.Dual<T>}:
  match x y:
    case DU.Dual{+a, +b} DU.Dual{+c, +d}:
      Dual.ext(T, add(a, c), add(c, a), add(b, d), add(d, b), ac(a, c), ac(b, d))

def Dual.zero_l(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +x: DU.Dual<T>) -> {DU.Dual.add(~T, ~add, DU.Dual.zero(~T, ~zero), x) == x : DU.Dual<T>}:
  match x:
    case DU.Dual{+a, +b}:
      Dual.ext(T, add(zero, a), a, add(zero, b), b, z(a), z(b))

def Dual.add_inv(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +x: DU.Dual<T>) -> {DU.Dual.add(~T, ~add, x, DU.Dual.neg(~T, ~neg, x)) == DU.Dual.zero(~T, ~zero) : DU.Dual<T>}:
  match x:
    case DU.Dual{+a, +b}:
      Dual.ext(T, add(a, neg(a)), zero, add(b, neg(b)), zero, inv(a), inv(b))

def Dual.mul_assoc(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +x: DU.Dual<T>, +y: DU.Dual<T>, +w: DU.Dual<T>)
  -> {DU.Dual.mul(~T, ~add, ~mul, DU.Dual.mul(~T, ~add, ~mul, x, y), w) == DU.Dual.mul(~T, ~add, ~mul, x, DU.Dual.mul(~T, ~add, ~mul, y, w)) : DU.Dual<T>}:
  match x y w:
    case DU.Dual{+a, +b} DU.Dual{+c, +d} DU.Dual{+e, +f}:
      Dual.ext(T, mul(mul(a, c), e), mul(a, mul(c, e)),
        add(mul(mul(a, c), f), mul(add(mul(a, d), mul(b, c)), e)), add(mul(a, add(mul(c, f), mul(d, e))), mul(b, mul(c, e))),
        ma(a, c, e),
        NP.NormS.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a, b, c, d, e, f], Ad(Ml(Ml(V(0n), V(2n)), V(5n)), Ml(Ad(Ml(V(0n), V(3n)), Ml(V(1n), V(2n))), V(4n))), Ad(Ml(V(0n), Ad(Ml(V(2n), V(5n)), Ml(V(3n), V(4n)))), Ml(V(1n), Ml(V(2n), V(4n)))), {==}))

def Dual.mul_comm(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +x: DU.Dual<T>, +y: DU.Dual<T>) -> {DU.Dual.mul(~T, ~add, ~mul, x, y) == DU.Dual.mul(~T, ~add, ~mul, y, x) : DU.Dual<T>}:
  match x y:
    case DU.Dual{+a, +b} DU.Dual{+c, +d}:
      Dual.ext(T, mul(a, c), mul(c, a), add(mul(a, d), mul(b, c)), add(mul(c, b), mul(d, a)),
        mc(a, c), NP.NormS.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a, b, c, d], Ad(Ml(V(0n), V(3n)), Ml(V(1n), V(2n))), Ad(Ml(V(2n), V(1n)), Ml(V(3n), V(0n))), {==}))

def Dual.unit_r(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +x: DU.Dual<T>) -> {DU.Dual.mul(~T, ~add, ~mul, x, DU.Dual.one(~T, ~zero, ~one)) == x : DU.Dual<T>}:
  match x:
    case DU.Dual{+a, +b}:
      Dual.ext(T, mul(a, one), a, add(mul(a, zero), mul(b, one)), b, u(a),
        Equal.trans(T, add(mul(a, zero), mul(b, one)), add(zero, b), b,
          Equal.trans(T, add(mul(a, zero), mul(b, one)), add(zero, mul(b, one)), add(zero, b),
            Equal.cong(T, T, w => add(w, mul(b, one)), mul(a, zero), zero, NP.Alg.mul_zero_r(~T, ~zero, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~dl, a)),
            Equal.cong(T, T, w => add(zero, w), mul(b, one), b, u(b))),
          z(b)))

def Dual.dist_l(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +x: DU.Dual<T>, +y: DU.Dual<T>, +w: DU.Dual<T>)
  -> {DU.Dual.mul(~T, ~add, ~mul, x, DU.Dual.add(~T, ~add, y, w)) == DU.Dual.add(~T, ~add, DU.Dual.mul(~T, ~add, ~mul, x, y), DU.Dual.mul(~T, ~add, ~mul, x, w)) : DU.Dual<T>}:
  match x y w:
    case DU.Dual{+a, +b} DU.Dual{+c, +d} DU.Dual{+e, +f}:
      Dual.ext(T, mul(a, add(c, e)), add(mul(a, c), mul(a, e)),
        add(mul(a, add(d, f)), mul(b, add(c, e))), add(add(mul(a, d), mul(b, c)), add(mul(a, f), mul(b, e))),
        dl(a, c, e),
        NP.NormS.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a, b, c, d, e, f], Ad(Ml(V(0n), Ad(V(3n), V(5n))), Ml(V(1n), Ad(V(2n), V(4n)))), Ad(Ad(Ml(V(0n), V(3n)), Ml(V(1n), V(2n))), Ad(Ml(V(0n), V(5n)), Ml(V(1n), V(4n)))), {==}))

def Dual.neg_add(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +x: DU.Dual<T>, +y: DU.Dual<T>) -> {DU.Dual.neg(~T, ~neg, DU.Dual.add(~T, ~add, x, y)) == DU.Dual.add(~T, ~add, DU.Dual.neg(~T, ~neg, x), DU.Dual.neg(~T, ~neg, y)) : DU.Dual<T>}:
  match x y:
    case DU.Dual{+a, +b} DU.Dual{+c, +d}:
      Dual.ext(T, neg(add(a, c)), add(neg(a), neg(c)), neg(add(b, d)), add(neg(b), neg(d)), na(a, c), na(b, d))

def Dual.neg_mul_l(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +x: DU.Dual<T>, +y: DU.Dual<T>) -> {DU.Dual.mul(~T, ~add, ~mul, DU.Dual.neg(~T, ~neg, x), y) == DU.Dual.neg(~T, ~neg, DU.Dual.mul(~T, ~add, ~mul, x, y)) : DU.Dual<T>}:
  match x y:
    case DU.Dual{+a, +b} DU.Dual{+c, +d}:
      Dual.ext(T, mul(neg(a), c), neg(mul(a, c)), add(mul(neg(a), d), mul(neg(b), c)), neg(add(mul(a, d), mul(b, c))),
        nm(a, c), NP.NormS.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a, b, c, d], Ad(Ml(Ng(V(0n)), V(3n)), Ml(Ng(V(1n)), V(2n))), Ng(Ad(Ml(V(0n), V(3n)), Ml(V(1n), V(2n)))), {==}))

def Dual.neg_neg(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +x: DU.Dual<T>) -> {DU.Dual.neg(~T, ~neg, DU.Dual.neg(~T, ~neg, x)) == x : DU.Dual<T>}:
  match x:
    case DU.Dual{+a, +b}:
      Dual.ext(T, neg(neg(a)), a, neg(neg(b)), b, nn(a), nn(b))

# The instance: plain parameters, the types src/ring.bend names at T = Dual<T>

def Dual.r.add_assoc(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), x: DU.Dual<T>, y: DU.Dual<T>, w: DU.Dual<T>) -> {DU.Dual.add(~T, ~add, DU.Dual.add(~T, ~add, x, y), w) == DU.Dual.add(~T, ~add, x, DU.Dual.add(~T, ~add, y, w)) : DU.Dual<T>}:
  Dual.add_assoc(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, x, y, w)

def Dual.r.add_comm(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), x: DU.Dual<T>, y: DU.Dual<T>) -> {DU.Dual.add(~T, ~add, x, y) == DU.Dual.add(~T, ~add, y, x) : DU.Dual<T>}:
  Dual.add_comm(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, x, y)

def Dual.r.zero_l(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), x: DU.Dual<T>) -> {DU.Dual.add(~T, ~add, DU.Dual.zero(~T, ~zero), x) == x : DU.Dual<T>}:
  Dual.zero_l(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, x)

def Dual.r.add_inv(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), x: DU.Dual<T>) -> {DU.Dual.add(~T, ~add, x, DU.Dual.neg(~T, ~neg, x)) == DU.Dual.zero(~T, ~zero) : DU.Dual<T>}:
  Dual.add_inv(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, x)

def Dual.r.mul_assoc(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), x: DU.Dual<T>, y: DU.Dual<T>, w: DU.Dual<T>) -> {DU.Dual.mul(~T, ~add, ~mul, DU.Dual.mul(~T, ~add, ~mul, x, y), w) == DU.Dual.mul(~T, ~add, ~mul, x, DU.Dual.mul(~T, ~add, ~mul, y, w)) : DU.Dual<T>}:
  Dual.mul_assoc(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, x, y, w)

def Dual.r.mul_comm(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), x: DU.Dual<T>, y: DU.Dual<T>) -> {DU.Dual.mul(~T, ~add, ~mul, x, y) == DU.Dual.mul(~T, ~add, ~mul, y, x) : DU.Dual<T>}:
  Dual.mul_comm(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, x, y)

def Dual.r.unit_r(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), x: DU.Dual<T>) -> {DU.Dual.mul(~T, ~add, ~mul, x, DU.Dual.one(~T, ~zero, ~one)) == x : DU.Dual<T>}:
  Dual.unit_r(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, x)

def Dual.r.dist_l(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), x: DU.Dual<T>, y: DU.Dual<T>, w: DU.Dual<T>) -> {DU.Dual.mul(~T, ~add, ~mul, x, DU.Dual.add(~T, ~add, y, w)) == DU.Dual.add(~T, ~add, DU.Dual.mul(~T, ~add, ~mul, x, y), DU.Dual.mul(~T, ~add, ~mul, x, w)) : DU.Dual<T>}:
  Dual.dist_l(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, x, y, w)

def Dual.r.neg_add(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), x: DU.Dual<T>, y: DU.Dual<T>) -> {DU.Dual.neg(~T, ~neg, DU.Dual.add(~T, ~add, x, y)) == DU.Dual.add(~T, ~add, DU.Dual.neg(~T, ~neg, x), DU.Dual.neg(~T, ~neg, y)) : DU.Dual<T>}:
  Dual.neg_add(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, x, y)

def Dual.r.neg_mul_l(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), x: DU.Dual<T>, y: DU.Dual<T>) -> {DU.Dual.mul(~T, ~add, ~mul, DU.Dual.neg(~T, ~neg, x), y) == DU.Dual.neg(~T, ~neg, DU.Dual.mul(~T, ~add, ~mul, x, y)) : DU.Dual<T>}:
  Dual.neg_mul_l(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, x, y)

def Dual.r.neg_neg(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), x: DU.Dual<T>) -> {DU.Dual.neg(~T, ~neg, DU.Dual.neg(~T, ~neg, x)) == x : DU.Dual<T>}:
  Dual.neg_neg(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, x)
