# Soundness of the cancellation normaliser (src/norm.bend): a term whose
# monomials cancel in pairs is zero in every commutative ring, and so two
# terms whose difference cancels are equal. The ring is given by its
# operations and the laws below, as ~ parameters.

import Base
import ../src/ring.bend as R
import ../src/norm.bend as N
import ./base.bend as B

# Ring algebra
# ------------

def Alg.zero_r(~T: Data, ~zero: T, ~add: T -> T -> T, ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), +a: T)
  -> {add(a, zero) == a : T}:
  Equal.trans(T, add(a, zero), add(zero, a), a, ac(a, zero), z(a))

# a + (b + c) = b + (a + c)
def Alg.swap(~T: Data, ~add: T -> T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), +a: T, +b: T, +c: T)
  -> {add(a, add(b, c)) == add(b, add(a, c)) : T}:
  Equal.trans(T, add(a, add(b, c)), add(add(a, b), c), add(b, add(a, c)),
    Equal.sym(T, add(add(a, b), c), add(a, add(b, c)), aa(a, b, c)),
    Equal.trans(T, add(add(a, b), c), add(add(b, a), c), add(b, add(a, c)),
      Equal.cong(T, T, w => add(w, c), add(a, b), add(b, a), ac(a, b)),
      aa(b, a, c)))

def Alg.neg_zero(~T: Data, ~zero: T, ~add: T -> T -> T, ~neg: T -> T, ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero))
  -> {neg(zero) == zero : T}:
  Equal.trans(T, neg(zero), add(zero, neg(zero)), zero, Equal.sym(T, add(zero, neg(zero)), neg(zero), z(neg(zero))), inv(zero))

# a * 0 = a * (0 + 0) = a * 0 + a * 0, so a * 0 = 0
def Alg.mul_zero_r(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~dl: R.Ring.DistL(T, add, mul), +a: T)
  -> {mul(a, zero) == zero : T}:
  Equal.sym(T, zero, mul(a, zero),
    Equal.trans(T, zero, add(mul(a, zero), neg(mul(a, zero))), mul(a, zero),
      Equal.sym(T, add(mul(a, zero), neg(mul(a, zero))), zero, inv(mul(a, zero))),
      Equal.trans(T, add(mul(a, zero), neg(mul(a, zero))), add(add(mul(a, zero), mul(a, zero)), neg(mul(a, zero))), mul(a, zero),
        Equal.cong(T, T, x => add(x, neg(mul(a, zero))), mul(a, zero), add(mul(a, zero), mul(a, zero)),
          Equal.trans(T, mul(a, zero), mul(a, add(zero, zero)), add(mul(a, zero), mul(a, zero)),
            Equal.cong(T, T, x => mul(a, x), zero, add(zero, zero), Equal.sym(T, add(zero, zero), zero, z(zero))),
            dl(a, zero, zero))),
        Equal.trans(T, add(add(mul(a, zero), mul(a, zero)), neg(mul(a, zero))), add(mul(a, zero), add(mul(a, zero), neg(mul(a, zero)))), mul(a, zero),
          aa(mul(a, zero), mul(a, zero), neg(mul(a, zero))),
          Equal.trans(T, add(mul(a, zero), add(mul(a, zero), neg(mul(a, zero)))), add(mul(a, zero), zero), mul(a, zero),
            Equal.cong(T, T, x => add(mul(a, zero), x), add(mul(a, zero), neg(mul(a, zero))), zero, inv(mul(a, zero))),
            Alg.zero_r(~T, ~zero, ~add, ~ac, ~z, mul(a, zero)))))))

# (a + b) * c = a * c + b * c, from distributivity on the left
def Alg.dist_r(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~mc: R.Ring.Comm(T, mul), ~dl: R.Ring.DistL(T, add, mul), +a: T, +b: T, +c: T)
  -> {mul(add(a, b), c) == add(mul(a, c), mul(b, c)) : T}:
  Equal.trans(T, mul(add(a, b), c), mul(c, add(a, b)), add(mul(a, c), mul(b, c)),
    mc(add(a, b), c),
    Equal.trans(T, mul(c, add(a, b)), add(mul(c, a), mul(c, b)), add(mul(a, c), mul(b, c)),
      dl(c, a, b),
      B.Eq.cong2(T, T, T, x => y => add(x, y), mul(c, a), mul(a, c), mul(c, b), mul(b, c), mc(c, a), mc(c, b))))

# a * (b * c) = b * (a * c)
def Alg.mswap(~T: Data, ~mul: T -> T -> T, ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), +a: T, +b: T, +c: T)
  -> {mul(a, mul(b, c)) == mul(b, mul(a, c)) : T}:
  Equal.trans(T, mul(a, mul(b, c)), mul(mul(a, b), c), mul(b, mul(a, c)),
    Equal.sym(T, mul(mul(a, b), c), mul(a, mul(b, c)), ma(a, b, c)),
    Equal.trans(T, mul(mul(a, b), c), mul(mul(b, a), c), mul(b, mul(a, c)),
      Equal.cong(T, T, w => mul(w, c), mul(a, b), mul(b, a), mc(a, b)),
      ma(b, a, c)))

# a * (-b) = -(a * b)
def Alg.neg_mul_r(~T: Data, ~mul: T -> T -> T, ~neg: T -> T, ~mc: R.Ring.Comm(T, mul), ~nm: R.Ring.NegMulL(T, mul, neg), +a: T, +b: T)
  -> {mul(a, neg(b)) == neg(mul(a, b)) : T}:
  Equal.trans(T, mul(a, neg(b)), mul(neg(b), a), neg(mul(a, b)),
    mc(a, neg(b)),
    Equal.trans(T, mul(neg(b), a), neg(mul(b, a)), neg(mul(a, b)),
      nm(b, a),
      Equal.cong(T, T, w => neg(w), mul(b, a), mul(a, b), mc(b, a))))

# Signs
# -----

def Sgn.flip(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), s: Bool, +x: T) -> {N.Sgn.ap(~T, ~neg, Bool.not(s), x) == neg(N.Sgn.ap(~T, ~neg, s, x)) : T}:
  match s:
    case False{}:
      {==}
    case True{}:
      Equal.sym(T, neg(neg(x)), x, nn(x))

def Sgn.mul(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), s: Bool, t: Bool, +x: T, +y: T)
  -> {N.Sgn.ap(~T, ~neg, Bool.xor(s, t), mul(x, y)) == mul(N.Sgn.ap(~T, ~neg, s, x), N.Sgn.ap(~T, ~neg, t, y)) : T}:
  match s t:
    case False{} False{}:
      {==}
    case False{} True{}:
      Equal.sym(T, mul(x, neg(y)), neg(mul(x, y)), Alg.neg_mul_r(~T, ~mul, ~neg, ~mc, ~nm, x, y))
    case True{} False{}:
      Equal.sym(T, mul(neg(x), y), neg(mul(x, y)), nm(x, y))
    case True{} True{}:
      Equal.sym(T, mul(neg(x), neg(y)), mul(x, y),
        Equal.trans(T, mul(neg(x), neg(y)), neg(mul(x, neg(y))), mul(x, y), nm(x, neg(y)),
          Equal.trans(T, neg(mul(x, neg(y))), neg(neg(mul(x, y))), mul(x, y),
            Equal.cong(T, T, w => neg(w), mul(x, neg(y)), neg(mul(x, y)), Alg.neg_mul_r(~T, ~mul, ~neg, ~mc, ~nm, x, y)),
            nn(mul(x, y)))))

# Products of variables
# ---------------------

def Vs.ins.pick(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, c: Bool, +x: Nat, +y: Nat, +t: List<&2, Nat>,
  ih: {N.Vs.prod(~T, ~zero, ~mul, ~one, env, N.Vs.ins(x, t)) == mul(N.Env.at(~T, ~zero, env, x), N.Vs.prod(~T, ~zero, ~mul, ~one, env, t)) : T})
  -> {N.Vs.prod(~T, ~zero, ~mul, ~one, env, Bool.pick(List<&2, Nat>, c, x <> y <> t, y <> N.Vs.ins(x, t))) == mul(N.Env.at(~T, ~zero, env, x), N.Vs.prod(~T, ~zero, ~mul, ~one, env, y <> t)) : T}:
  match c:
    case True{}:
      {==}
    case False{}:
      Equal.trans(T, mul(N.Env.at(~T, ~zero, env, y), N.Vs.prod(~T, ~zero, ~mul, ~one, env, N.Vs.ins(x, t))), mul(N.Env.at(~T, ~zero, env, y), mul(N.Env.at(~T, ~zero, env, x), N.Vs.prod(~T, ~zero, ~mul, ~one, env, t))), mul(N.Env.at(~T, ~zero, env, x), mul(N.Env.at(~T, ~zero, env, y), N.Vs.prod(~T, ~zero, ~mul, ~one, env, t))),
        Equal.cong(T, T, w => mul(N.Env.at(~T, ~zero, env, y), w), N.Vs.prod(~T, ~zero, ~mul, ~one, env, N.Vs.ins(x, t)), mul(N.Env.at(~T, ~zero, env, x), N.Vs.prod(~T, ~zero, ~mul, ~one, env, t)), ih),
        Alg.mswap(~T, ~mul, ~ma, ~mc, N.Env.at(~T, ~zero, env, y), N.Env.at(~T, ~zero, env, x), N.Vs.prod(~T, ~zero, ~mul, ~one, env, t)))

# inserting a variable multiplies by it
def Vs.ins.prod(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, +x: Nat, ys: List<&2, Nat>)
  -> {N.Vs.prod(~T, ~zero, ~mul, ~one, env, N.Vs.ins(x, ys)) == mul(N.Env.at(~T, ~zero, env, x), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys)) : T}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      Vs.ins.pick(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, Nat.is_le(x, y), x, y, t, Vs.ins.prod(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, x, t))

def Vs.merge.prod(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, xs: List<&2, Nat>, +ys: List<&2, Nat>)
  -> {N.Vs.prod(~T, ~zero, ~mul, ~one, env, N.Vs.merge(xs, ys)) == mul(N.Vs.prod(~T, ~zero, ~mul, ~one, env, xs), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys)) : T}:
  match xs:
    case Nil{}:
      Equal.sym(T, mul(one, N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys)), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys),
        Equal.trans(T, mul(one, N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys)), mul(N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys), one), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys), mc(one, N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys)), u(N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys))))
    case +x <> +t:
      Equal.trans(T, N.Vs.prod(~T, ~zero, ~mul, ~one, env, N.Vs.ins(x, N.Vs.merge(t, ys))), mul(N.Env.at(~T, ~zero, env, x), N.Vs.prod(~T, ~zero, ~mul, ~one, env, N.Vs.merge(t, ys))), mul(mul(N.Env.at(~T, ~zero, env, x), N.Vs.prod(~T, ~zero, ~mul, ~one, env, t)), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys)),
        Vs.ins.prod(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, x, N.Vs.merge(t, ys)),
        Equal.trans(T, mul(N.Env.at(~T, ~zero, env, x), N.Vs.prod(~T, ~zero, ~mul, ~one, env, N.Vs.merge(t, ys))), mul(N.Env.at(~T, ~zero, env, x), mul(N.Vs.prod(~T, ~zero, ~mul, ~one, env, t), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys))), mul(mul(N.Env.at(~T, ~zero, env, x), N.Vs.prod(~T, ~zero, ~mul, ~one, env, t)), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys)),
          Equal.cong(T, T, w => mul(N.Env.at(~T, ~zero, env, x), w), N.Vs.prod(~T, ~zero, ~mul, ~one, env, N.Vs.merge(t, ys)), mul(N.Vs.prod(~T, ~zero, ~mul, ~one, env, t), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys)), Vs.merge.prod(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, t, ys)),
          Equal.sym(T, mul(mul(N.Env.at(~T, ~zero, env, x), N.Vs.prod(~T, ~zero, ~mul, ~one, env, t)), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys)), mul(N.Env.at(~T, ~zero, env, x), mul(N.Vs.prod(~T, ~zero, ~mul, ~one, env, t), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys))), ma(N.Env.at(~T, ~zero, env, x), N.Vs.prod(~T, ~zero, ~mul, ~one, env, t), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ys)))))

# Monomials
# ---------

def Mono.mul.eval(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, a: N.Mono, b: N.Mono)
  -> {N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, N.Mono.mul(a, b)) == mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, a), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, b)) : T}:
  match a b:
    case N.Mono{+s, +vs} N.Mono{+t, +ws}:
      Equal.trans(T, N.Sgn.ap(~T, ~neg, Bool.xor(s, t), N.Vs.prod(~T, ~zero, ~mul, ~one, env, N.Vs.merge(vs, ws))), N.Sgn.ap(~T, ~neg, Bool.xor(s, t), mul(N.Vs.prod(~T, ~zero, ~mul, ~one, env, vs), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ws))), mul(N.Sgn.ap(~T, ~neg, s, N.Vs.prod(~T, ~zero, ~mul, ~one, env, vs)), N.Sgn.ap(~T, ~neg, t, N.Vs.prod(~T, ~zero, ~mul, ~one, env, ws))),
        Equal.cong(T, T, w => N.Sgn.ap(~T, ~neg, Bool.xor(s, t), w), N.Vs.prod(~T, ~zero, ~mul, ~one, env, N.Vs.merge(vs, ws)), mul(N.Vs.prod(~T, ~zero, ~mul, ~one, env, vs), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ws)), Vs.merge.prod(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, vs, ws)),
        Sgn.mul(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, s, t, N.Vs.prod(~T, ~zero, ~mul, ~one, env, vs), N.Vs.prod(~T, ~zero, ~mul, ~one, env, ws)))

def Mono.flip.eval(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, a: N.Mono) -> {N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, N.Mono.flip(a)) == neg(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, a)) : T}:
  match a:
    case N.Mono{s, +vs}:
      Sgn.flip(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, s, N.Vs.prod(~T, ~zero, ~mul, ~one, env, vs))

# Sums of monomials
# -----------------

def Ms.app.sum(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, xs: List<&2, N.Mono>, +ys: List<&2, N.Mono>)
  -> {N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.app(xs, ys)) == add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, xs), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)) : T}:
  match xs:
    case Nil{}:
      Equal.sym(T, add(zero, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys), z(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)))
    case +x <> +t:
      Equal.trans(T, add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.app(t, ys))), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys))), add(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)),
        Equal.cong(T, T, w => add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), w), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.app(t, ys)), add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)), Ms.app.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, t, ys)),
        Equal.sym(T, add(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys))), aa(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys))))

def Ms.flip.sum(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, xs: List<&2, N.Mono>) -> {N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.flip(xs)) == neg(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, xs)) : T}:
  match xs:
    case Nil{}:
      Equal.sym(T, neg(zero), zero, Alg.neg_zero(~T, ~zero, ~add, ~neg, ~z, ~inv))
    case +x <> +t:
      Equal.trans(T, add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, N.Mono.flip(x)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.flip(t))), add(neg(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x)), neg(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))), neg(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))),
        B.Eq.cong2(T, T, T, p => q => add(p, q), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, N.Mono.flip(x)), neg(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.flip(t)), neg(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)),
          Mono.flip.eval(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, x), Ms.flip.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, t)),
        Equal.sym(T, neg(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))), add(neg(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x)), neg(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))), na(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))))

def Ms.scale.sum(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, +x: N.Mono, ys: List<&2, N.Mono>)
  -> {N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.scale(x, ys)) == mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)) : T}:
  match ys:
    case Nil{}:
      Equal.sym(T, mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), zero), zero, Alg.mul_zero_r(~T, ~zero, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~dl, N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x)))
    case +y <> +t:
      Equal.trans(T, add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, N.Mono.mul(x, y)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.scale(x, t))), add(mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, y)), mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))), mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, y), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))),
        B.Eq.cong2(T, T, T, p => q => add(p, q), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, N.Mono.mul(x, y)), mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, y)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.scale(x, t)), mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)),
          Mono.mul.eval(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, x, y), Ms.scale.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, x, t)),
        Equal.sym(T, mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, y), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))), add(mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, y)), mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))), dl(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, y), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))))

def Ms.mul.sum(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, xs: List<&2, N.Mono>, +ys: List<&2, N.Mono>)
  -> {N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.mul(xs, ys)) == mul(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, xs), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)) : T}:
  match xs:
    case Nil{}:
      Equal.sym(T, mul(zero, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)), zero,
        Equal.trans(T, mul(zero, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)), mul(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys), zero), zero, mc(zero, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)),
          Alg.mul_zero_r(~T, ~zero, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~dl, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys))))
    case +x <> +t:
      Equal.trans(T, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.app(N.Ms.scale(x, ys), N.Ms.mul(t, ys))), add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.scale(x, ys)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.mul(t, ys))), mul(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)),
        Ms.app.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, N.Ms.scale(x, ys), N.Ms.mul(t, ys)),
        Equal.trans(T, add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.scale(x, ys)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.mul(t, ys))), add(mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)), mul(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys))), mul(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)),
          B.Eq.cong2(T, T, T, p => q => add(p, q), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.scale(x, ys)), mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.mul(t, ys)), mul(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)),
            Ms.scale.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, x, ys), Ms.mul.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, t, ys)),
          Equal.sym(T, mul(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)), add(mul(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)), mul(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys))),
            Alg.dist_r(~T, ~add, ~mul, ~mc, ~dl, N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, x), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ys)))))

# a term is the sum of its monomials
def Tm.flat.sum(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, t: N.Tm) -> {N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(t)) == N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, t) : T}:
  match t:
    case N.TVar{+i}:
      Equal.trans(T, add(mul(N.Env.at(~T, ~zero, env, i), one), zero), mul(N.Env.at(~T, ~zero, env, i), one), N.Env.at(~T, ~zero, env, i),
        Alg.zero_r(~T, ~zero, ~add, ~ac, ~z, mul(N.Env.at(~T, ~zero, env, i), one)), u(N.Env.at(~T, ~zero, env, i)))
    case N.TZero{}:
      {==}
    case N.TAdd{+a, +b}:
      Equal.trans(T, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.app(N.Tm.flat(a), N.Tm.flat(b))), add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(a)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(b))), add(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)),
        Ms.app.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, N.Tm.flat(a), N.Tm.flat(b)),
        B.Eq.cong2(T, T, T, p => q => add(p, q), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(a)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(b)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b),
          Tm.flat.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, a), Tm.flat.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, b)))
    case N.TMul{+a, +b}:
      Equal.trans(T, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.mul(N.Tm.flat(a), N.Tm.flat(b))), mul(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(a)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(b))), mul(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)),
        Ms.mul.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, N.Tm.flat(a), N.Tm.flat(b)),
        B.Eq.cong2(T, T, T, p => q => mul(p, q), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(a)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(b)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b),
          Tm.flat.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, a), Tm.flat.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, b)))
    case N.TNeg{+a}:
      Equal.trans(T, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.flip(N.Tm.flat(a))), neg(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(a))), neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a)),
        Ms.flip.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, N.Tm.flat(a)),
        Equal.cong(T, T, w => neg(w), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(a)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), Tm.flat.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, a)))

# Cancellation
# ------------

def Nat.eq_sound(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      B.Bool.tf({0n == 1n+q : Nat}, Equal.sym(Bool, False{}, True{}, e))
    case 1n+p 0n:
      B.Bool.tf({1n+p == 0n : Nat}, Equal.sym(Bool, False{}, True{}, e))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, w => 1n+w, p, q, Nat.eq_sound(p, q, e))

def Bool.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      B.Bool.tf({False{} == True{} : Bool}, Equal.sym(Bool, False{}, True{}, e))

def Bool.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      B.Bool.tf({b == True{} : Bool}, Equal.sym(Bool, False{}, True{}, e))

def Vs.eq_sound(xs: List<&2, Nat>, ys: List<&2, Nat>, +e: {N.Vs.eq(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, Nat>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yt:
      B.Bool.tf({Nil{} == y <> yt : List<&2, Nat>}, Equal.sym(Bool, False{}, True{}, e))
    case x <> xt Nil{}:
      B.Bool.tf({x <> xt == Nil{} : List<&2, Nat>}, Equal.sym(Bool, False{}, True{}, e))
    case +x <> +xt +y <> +yt:
      B.Eq.cong2(Nat, List<&2, Nat>, List<&2, Nat>, p => q => p <> q, x, y, xt, yt,
        Nat.eq_sound(x, y, Bool.and_l(Nat.is_eq(x, y), N.Vs.eq(xt, yt), e)),
        Vs.eq_sound(xt, yt, Bool.and_r(Nat.is_eq(x, y), N.Vs.eq(xt, yt), e)))

def Mono.opp.signs(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), s: Bool, t: Bool, +x: T, h: {Bool.xor(s, t) == True{} : Bool})
  -> {add(N.Sgn.ap(~T, ~neg, s, x), N.Sgn.ap(~T, ~neg, t, x)) == zero : T}:
  match s t:
    case False{} False{}:
      B.Bool.tf({add(x, x) == zero : T}, Equal.sym(Bool, False{}, True{}, h))
    case False{} True{}:
      inv(x)
    case True{} False{}:
      Equal.trans(T, add(neg(x), x), add(x, neg(x)), zero, ac(neg(x), x), inv(x))
    case True{} True{}:
      B.Bool.tf({add(neg(x), neg(x)) == zero : T}, Equal.sym(Bool, False{}, True{}, h))

def Mono.opp.vars(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, +s: Bool, +t: Bool, +vs: List<&2, Nat>, -ws: List<&2, Nat>,
  h: {Bool.xor(s, t) == True{} : Bool}, e: {vs == ws : List<&2, Nat>})
  -> {add(N.Sgn.ap(~T, ~neg, s, N.Vs.prod(~T, ~zero, ~mul, ~one, env, vs)), N.Sgn.ap(~T, ~neg, t, N.Vs.prod(~T, ~zero, ~mul, ~one, env, ws))) == zero : T}:
  %e : {add(N.Sgn.ap(~T, ~neg, s, N.Vs.prod(~T, ~zero, ~mul, ~one, env, vs)), N.Sgn.ap(~T, ~neg, t, N.Vs.prod(~T, ~zero, ~mul, ~one, env, _))) == zero : T}
  Mono.opp.signs(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, s, t, N.Vs.prod(~T, ~zero, ~mul, ~one, env, vs), h)

# opposite monomials add to zero
def Mono.opp.sound(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, a: N.Mono, b: N.Mono, +e: {N.Mono.opp(a, b) == True{} : Bool})
  -> {add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, a), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, b)) == zero : T}:
  match a b:
    case N.Mono{+s, +vs} N.Mono{+t, +ws}:
      Mono.opp.vars(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, s, t, vs, ws,
        Bool.and_l(Bool.xor(s, t), N.Vs.eq(vs, ws), e),
        Vs.eq_sound(vs, ws, Bool.and_r(Bool.xor(s, t), N.Vs.eq(vs, ws), e)))

def Ms.ins.pick(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, c: Bool, +m: N.Mono, +p: N.Mono, +t: List<&2, N.Mono>,
  e: {N.Mono.opp(m, p) == c : Bool}, ih: {N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.ins(m, t)) == add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)) : T})
  -> {N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, Bool.pick(List<&2, N.Mono>, c, t, p <> N.Ms.ins(m, t))) == add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))) : T}:
  match c:
    case True{}:
      Equal.sym(T, add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t),
        Equal.trans(T, add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))), add(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t),
          Equal.sym(T, add(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))), aa(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))),
          Equal.trans(T, add(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), add(zero, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t),
            Equal.cong(T, T, w => add(w, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p)), zero, Mono.opp.sound(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, m, p, e)),
            z(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)))))
    case False{}:
      Equal.trans(T, add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.ins(m, t))), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))),
        Equal.cong(T, T, w => add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p), w), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.ins(m, t)), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), ih),
        Alg.swap(~T, ~add, ~aa, ~ac, N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, p), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)))

# inserting a monomial (or cancelling it against its opposite) adds it
def Ms.ins.sum(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, +m: N.Mono, ps: List<&2, N.Mono>)
  -> {N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.ins(m, ps)) == add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps)) : T}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      Ms.ins.pick(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, N.Mono.opp(m, p), m, p, t, {==}, Ms.ins.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, m, t))

def Ms.cancel.sum(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, l: List<&2, N.Mono>, +ps: List<&2, N.Mono>)
  -> {N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.cancel(l, ps)) == add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, l), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps)) : T}:
  match l:
    case Nil{}:
      Equal.sym(T, add(zero, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps), z(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps)))
    case +m <> +t:
      Equal.trans(T, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.cancel(t, N.Ms.ins(m, ps))), add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.ins(m, ps))), add(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps)),
        Ms.cancel.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, t, N.Ms.ins(m, ps)),
        Equal.trans(T, add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.ins(m, ps))), add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps))), add(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps)),
          Equal.cong(T, T, w => add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), w), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Ms.ins(m, ps)), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps)), Ms.ins.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, m, ps)),
          Equal.trans(T, add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps))), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps))), add(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps)),
            Alg.swap(~T, ~add, ~aa, ~ac, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps)),
            Equal.sym(T, add(add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t)), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps)), add(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps))), aa(N.Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, ps))))))

# The theorems
# ------------

# a term whose monomials cancel is zero
def Norm.zero(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, +t: N.Tm, ok: {N.Norm.left(t) == Nil{} : List<&2, N.Mono>})
  -> {N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, t) == zero : T}:
  Equal.trans(T, N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, t), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(t)), zero,
    Equal.sym(T, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(t)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, t), Tm.flat.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, t)),
    Equal.trans(T, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(t)), add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(t)), zero), zero,
      Equal.sym(T, add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(t)), zero), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(t)), Alg.zero_r(~T, ~zero, ~add, ~ac, ~z, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(t)))),
      Equal.trans(T, add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(t)), zero), N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Norm.left(t)), zero,
        Equal.sym(T, N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Norm.left(t)), add(N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, N.Tm.flat(t)), zero), Ms.cancel.sum(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, N.Tm.flat(t), Nil{})),
        Equal.cong(List<&2, N.Mono>, T, w => N.Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, w), N.Norm.left(t), Nil{}, ok))))

# two terms whose difference cancels are equal
def Norm.eq(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, +a: N.Tm, +b: N.Tm, ok: {N.Norm.left(N.Tm.diff(a, b)) == Nil{} : List<&2, N.Mono>})
  -> {N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a) == N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b) : T}:
  Equal.trans(T, N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), add(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), add(neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b))), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b),
    Equal.trans(T, N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), add(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), zero), add(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), add(neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b))),
      Equal.sym(T, add(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), zero), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), Alg.zero_r(~T, ~zero, ~add, ~ac, ~z, N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a))),
      Equal.cong(T, T, w => add(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), w), zero, add(neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)),
        Equal.sym(T, add(neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), zero,
          Equal.trans(T, add(neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), add(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b), neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b))), zero, ac(neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), inv(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)))))),
    Equal.trans(T, add(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), add(neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b))), add(add(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b))), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b),
      Equal.sym(T, add(add(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b))), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), add(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), add(neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b))), aa(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b))),
      Equal.trans(T, add(add(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b))), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), add(zero, N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b),
        Equal.cong(T, T, w => add(w, N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)), add(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), neg(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b))), zero,
          Norm.zero(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, N.Tm.diff(a, b), ok)),
        z(N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b)))))
