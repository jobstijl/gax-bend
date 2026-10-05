# Error-free transformations (num/df32.bend) on the binary formats of
# src/round.bend. Scaled by 2^k, a format's values are integers, and
# rounding them is the loop Tr (src/round.bend) on integers: round to
# nearest, ties to even, at p significant bits. Here, for any p:
#   - rounding is exact on representable integers, and its result is
#     representable (R(n) = n defines representable);
#   - it is nearest: no representable integer is closer;
#   - Sterbenz: a - b is representable when b/2 <= a <= 2b;
#   - the error of a rounded sum is representable;
#   - so Fast2Sum is exact.

import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/round.bend as RD
import ../src/norm.bend as N
import ./nat.bend as NL
import ./int.bend as Z
import ./dyadic.bend as Y
import ./round.bend as R
import ./big.bend as BP

# Rounding magnitudes
# -------------------

# R(n): n rounded to p significant bits
def Rn(+p: Nat, +n: Nat) -> Nat:
  RD.Tr.near(RD.Tr.of(p, n))

def Tr.wr(t: RD.Tr) -> Nat:
  match t:
    case RD.Tr{s, q, r, wr, wq}:
      wr

def Tr.wq(t: RD.Tr) -> Nat:
  match t:
    case RD.Tr{s, q, r, wr, wq}:
      wq

# the loop's shape: n = q 2^s + r with r < 2^s, and q >= 2^(p-1) once shifted
def Sh(pp: Nat, n: Nat, t: RD.Tr) -> Type:
  {n == Nat.add(Nat.mul(RD.Tr.q(t), RD.Nat.pow2(RD.Tr.s(t))), R.Tr.r(t)) : Nat} & {RD.Nat.pow2(RD.Tr.s(t)) == Nat.add(Nat.add(R.Tr.r(t), 1n), Tr.wr(t)) : Nat}

def Sh.of(+pp: Nat, +n: Nat, t: RD.Tr, inv: R.Inv(pp, n, t)) -> Sh(pp, n, t):
  match t:
    case RD.Tr{+s, +q, +r, +wr, +wq}:
      match s:
        case 0n:
          match inv:
            case (en, erw):
              match erw:
                case (er, ew):
                  +en2 : {n == q : Nat} = en
                  +er2 : {r == 0n : Nat} = er
                  +ew2 : {wr == 0n : Nat} = ew
                  (Equal.trans(Nat, n, q, Nat.add(Nat.mul(q, 1n), r), en2,
                     Equal.sym(Nat, Nat.add(Nat.mul(q, 1n), r), q, Equal.trans(Nat, Nat.add(Nat.mul(q, 1n), r), Nat.add(q, 0n), q,
                       Equal.trans(Nat, Nat.add(Nat.mul(q, 1n), r), Nat.add(q, r), Nat.add(q, 0n), Equal.cong(Nat, Nat, z => Nat.add(z, r), Nat.mul(q, 1n), q, NL.Nat.mul_one_r(q)), Equal.cong(Nat, Nat, z => Nat.add(q, z), r, 0n, er2)),
                       NL.Nat.add_zero_r(q)))),
                   Equal.sym(Nat, Nat.add(Nat.add(r, 1n), wr), 1n,
                     Equal.trans(Nat, Nat.add(Nat.add(r, 1n), wr), Nat.add(Nat.add(0n, 1n), 0n), 1n,
                       Equal.trans(Nat, Nat.add(Nat.add(r, 1n), wr), Nat.add(Nat.add(0n, 1n), wr), Nat.add(Nat.add(0n, 1n), 0n),
                         Equal.cong(Nat, Nat, z => Nat.add(Nat.add(z, 1n), wr), r, 0n, er2), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(0n, 1n), z), wr, 0n, ew2)),
                       {==})))
        case 1n+s1:
          match inv:
            case (en, erw):
              match erw:
                case (er, eq):
                  (en, er)

def Sh.n(+p1: Nat, +n: Nat) -> Sh(RD.Nat.pow2(p1), n, RD.Tr.of(1n+p1, n)):
  Sh.of(RD.Nat.pow2(p1), n, RD.Tr.of(1n+p1, n), R.Inv.of(p1, n))

# once shifted, q >= 2^(p-1)
def Sh.h(+pp: Nat, +n: Nat, t: RD.Tr, inv: R.Inv(pp, n, t), +s1: Nat, hs: {RD.Tr.s(t) == 1n+s1 : Nat}) -> {RD.Tr.q(t) == Nat.add(pp, Tr.wq(t)) : Nat}:
  match t:
    case RD.Tr{s, +q, +r, +wr, +wq}:
      match s:
        case 0n:
          Empty.absurd({q == Nat.add(pp, wq) : Nat}, Z.Bool.ft(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 1n+s1, 0n, Equal.sym(Nat, 0n, 1n+s1, hs))))
        case 1n+t1:
          match inv:
            case (en, erw):
              match erw:
                case (er, eq):
                  eq

# the quotient stays below 2^p (the fuel n suffices)
def TrQ.go(+f: Nat, +p: Nat, +n: Nat, lt: Bool, +el: {RD.Nat.lt(n, RD.Nat.pow2(p)) == lt : Bool}, +hf: {RD.Nat.lt(n, RD.Nat.pow2(Nat.add(p, f))) == True{} : Bool})
  -> {RD.Nat.lt(RD.Tr.q(RD.Tr.go(f, p, n, lt)), RD.Nat.pow2(p)) == True{} : Bool}:
  match f:
    case 0n:
      match lt:
        case True{}:
          el
        case False{}:
          Equal.trans(Bool, RD.Nat.lt(n, RD.Nat.pow2(p)), RD.Nat.lt(n, RD.Nat.pow2(Nat.add(p, 0n))), True{},
            Equal.cong(Nat, Bool, z => RD.Nat.lt(n, RD.Nat.pow2(z)), p, Nat.add(p, 0n), Equal.sym(Nat, Nat.add(p, 0n), p, NL.Nat.add_zero_r(p))), hf)
    case 1n+(+g):
      match lt:
        case True{}:
          el
        case False{}:
          +pw = RD.Nat.pow2(p)
          +hn = D.Nat.half(n)
          +qg = RD.Nat.pow2(Nat.add(p, g))
          +ef = Equal.trans(Bool, RD.Nat.lt(n, Nat.double(qg)), RD.Nat.lt(n, RD.Nat.pow2(Nat.add(p, 1n+g))), True{},
            Equal.cong(Nat, Bool, z => RD.Nat.lt(n, RD.Nat.pow2(z)), 1n+Nat.add(p, g), Nat.add(p, 1n+g), Equal.sym(Nat, Nat.add(p, 1n+g), 1n+Nat.add(p, g), NL.Nat.add_succ_r(p, g))), hf)
          Equal.trans(Bool, RD.Nat.lt(RD.Tr.q(RD.Tr.up(RD.Tr.go(g, p, hn, RD.Nat.lt(hn, pw)), RD.Nat.bit(n), RD.Nat.monus(n, pw))), pw), RD.Nat.lt(RD.Tr.q(RD.Tr.go(g, p, hn, RD.Nat.lt(hn, pw))), pw), True{},
            Equal.cong(Nat, Bool, z => RD.Nat.lt(z, pw), RD.Tr.q(RD.Tr.up(RD.Tr.go(g, p, hn, RD.Nat.lt(hn, pw)), RD.Nat.bit(n), RD.Nat.monus(n, pw))), RD.Tr.q(RD.Tr.go(g, p, hn, RD.Nat.lt(hn, pw))), BP.Up.q(RD.Tr.go(g, p, hn, RD.Nat.lt(hn, pw)), RD.Nat.bit(n), RD.Nat.monus(n, pw))),
            TrQ.go(g, p, hn, RD.Nat.lt(hn, pw), {==}, BP.Half.lt(qg, n, RD.Nat.monus(Nat.double(qg), 1n+n), BP.Lt.wit(n, Nat.double(qg))(ef))))

def TrQ(+p: Nat, +n: Nat) -> {RD.Nat.lt(RD.Tr.q(RD.Tr.of(p, n)), RD.Nat.pow2(p)) == True{} : Bool}:
  TrQ.go(n, p, n, RD.Nat.lt(n, RD.Nat.pow2(p)), {==}, BP.Lt.pw(n, p, n, BP.Lt.npow(n)))

# Scaling
# -------

def Lt.dd(+a: Nat, +b: Nat) -> {RD.Nat.lt(Nat.double(a), Nat.double(b)) == RD.Nat.lt(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      Lt.dd(ap, bp)

# a + k < c gives a < c
def Lt.le(+a: Nat, +k: Nat, +c: Nat, +h: {RD.Nat.lt(Nat.add(a, k), c) == True{} : Bool}) -> {RD.Nat.lt(a, c) == True{} : Bool}:
  +w = RD.Nat.monus(c, 1n+Nat.add(a, k))
  +e = Equal.trans(Nat, c, 1n+Nat.add(Nat.add(a, k), w), Nat.add(a, 1n+Nat.add(k, w)), BP.Lt.wit(Nat.add(a, k), c)(h),
    Equal.trans(Nat, 1n+Nat.add(Nat.add(a, k), w), 1n+Nat.add(a, Nat.add(k, w)), Nat.add(a, 1n+Nat.add(k, w)),
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(a, k), w), Nat.add(a, Nat.add(k, w)), NL.Nat.add_assoc(a, k, w)),
      Equal.sym(Nat, Nat.add(a, 1n+Nat.add(k, w)), 1n+Nat.add(a, Nat.add(k, w)), NL.Nat.add_succ_r(a, Nat.add(k, w)))))
  Equal.trans(Bool, RD.Nat.lt(a, c), RD.Nat.lt(a, Nat.add(a, 1n+Nat.add(k, w))), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(a, z), c, Nat.add(a, 1n+Nat.add(k, w)), e), BP.Lt.self(a, Nat.add(k, w)))

def Near.base(+m: Nat) -> {RD.Tr.near(RD.Tr{0n, m, 0n, 0n, 0n}) == m : Nat}:
  NL.Nat.mul_one_r(m)

def Pick.dbl(+b: Bool, +x: Nat, +y: Nat) -> {Nat.double(Bool.pick(Nat, b, x, y)) == Bool.pick(Nat, b, Nat.double(x), Nat.double(y)) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# one more halving with a zero bit doubles the rounded value
def Near.up0(t: RD.Tr, +w: Nat) -> {RD.Tr.near(RD.Tr.up(t, 0n, w)) == Nat.double(RD.Tr.near(t)) : Nat}:
  match t:
    case RD.Tr{+s, +q, +r, wr, wq}:
      +sv = RD.Nat.pow2(s)
      +r0 = Nat.add(Nat.double(r), 0n)
      +er = NL.Nat.add_zero_r(Nat.double(r))
      +u1 = Bool.and(Bool.not(RD.Nat.lt(Nat.double(r0), Nat.double(sv))), Bool.or(RD.Nat.lt(Nat.double(sv), Nat.double(r0)), Bool.not(D.Nat.even(q))))
      +u = Bool.and(Bool.not(RD.Nat.lt(Nat.double(r), sv)), Bool.or(RD.Nat.lt(sv, Nat.double(r)), Bool.not(D.Nat.even(q))))
      +eu = Equal.trans(Bool, u1, Bool.and(Bool.not(RD.Nat.lt(Nat.double(Nat.double(r)), Nat.double(sv))), Bool.or(RD.Nat.lt(Nat.double(sv), Nat.double(Nat.double(r))), Bool.not(D.Nat.even(q)))), u,
        Equal.cong(Nat, Bool, z => Bool.and(Bool.not(RD.Nat.lt(Nat.double(z), Nat.double(sv))), Bool.or(RD.Nat.lt(Nat.double(sv), Nat.double(z)), Bool.not(D.Nat.even(q)))), r0, Nat.double(r), er),
        BP.Rup.cong(RD.Nat.lt(Nat.double(Nat.double(r)), Nat.double(sv)), RD.Nat.lt(Nat.double(r), sv), RD.Nat.lt(Nat.double(sv), Nat.double(Nat.double(r))), RD.Nat.lt(sv, Nat.double(r)), D.Nat.even(q), D.Nat.even(q),
          Lt.dd(Nat.double(r), sv), Lt.dd(sv, Nat.double(r)), {==}))
      Equal.trans(Nat, Bool.pick(Nat, u1, Nat.mul(1n+q, Nat.double(sv)), Nat.mul(q, Nat.double(sv))), Bool.pick(Nat, u, Nat.double(Nat.mul(1n+q, sv)), Nat.double(Nat.mul(q, sv))), Nat.double(Bool.pick(Nat, u, Nat.mul(1n+q, sv), Nat.mul(q, sv))),
        Equal.trans(Nat, Bool.pick(Nat, u1, Nat.mul(1n+q, Nat.double(sv)), Nat.mul(q, Nat.double(sv))), Bool.pick(Nat, u, Nat.mul(1n+q, Nat.double(sv)), Nat.mul(q, Nat.double(sv))), Bool.pick(Nat, u, Nat.double(Nat.mul(1n+q, sv)), Nat.double(Nat.mul(q, sv))),
          Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, Nat.mul(1n+q, Nat.double(sv)), Nat.mul(q, Nat.double(sv))), u1, u, eu),
          Equal.trans(Nat, Bool.pick(Nat, u, Nat.mul(1n+q, Nat.double(sv)), Nat.mul(q, Nat.double(sv))), Bool.pick(Nat, u, Nat.double(Nat.mul(1n+q, sv)), Nat.mul(q, Nat.double(sv))), Bool.pick(Nat, u, Nat.double(Nat.mul(1n+q, sv)), Nat.double(Nat.mul(q, sv))),
            Equal.cong(Nat, Nat, z => Bool.pick(Nat, u, z, Nat.mul(q, Nat.double(sv))), Nat.mul(1n+q, Nat.double(sv)), Nat.double(Nat.mul(1n+q, sv)), R.Nat.mul_double(1n+q, sv)),
            Equal.cong(Nat, Nat, z => Bool.pick(Nat, u, Nat.double(Nat.mul(1n+q, sv)), z), Nat.mul(q, Nat.double(sv)), Nat.double(Nat.mul(q, sv)), R.Nat.mul_double(q, sv)))),
        Equal.sym(Nat, Nat.double(Bool.pick(Nat, u, Nat.mul(1n+q, sv), Nat.mul(q, sv))), Bool.pick(Nat, u, Nat.double(Nat.mul(1n+q, sv)), Nat.double(Nat.mul(q, sv))), Pick.dbl(u, Nat.mul(1n+q, sv), Nat.mul(q, sv))))

def Tr.of.lo(+p: Nat, +n: Nat, +h: {RD.Nat.lt(n, RD.Nat.pow2(p)) == True{} : Bool}) -> {RD.Tr.of(p, n) == RD.Tr{0n, n, 0n, 0n, 0n} : RD.Tr}:
  Equal.trans(RD.Tr, RD.Tr.go(n, p, n, RD.Nat.lt(n, RD.Nat.pow2(p))), RD.Tr.go(n, p, n, True{}), RD.Tr{0n, n, 0n, 0n, 0n},
    Equal.cong(Bool, RD.Tr, z => RD.Tr.go(n, p, n, z), RD.Nat.lt(n, RD.Nat.pow2(p)), True{}, h), BP.Go.base(n, p, n))

# 2n >= 2^p: rounding 2n is rounding n with one more halving
def Sc.hi(+p: Nat, +n: Nat, +h: {RD.Nat.lt(Nat.double(n), RD.Nat.pow2(p)) == False{} : Bool})
  -> {RD.Tr.of(p, Nat.double(n)) == RD.Tr.up(RD.Tr.of(p, n), 0n, RD.Nat.monus(Nat.double(n), RD.Nat.pow2(p))) : RD.Tr}:
  match n:
    case 0n:
      Empty.absurd({RD.Tr.of(p, 0n) == RD.Tr.up(RD.Tr.of(p, 0n), 0n, RD.Nat.monus(0n, RD.Nat.pow2(p))) : RD.Tr},
        Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(0n, RD.Nat.pow2(p)), True{}, Equal.sym(Bool, RD.Nat.lt(0n, RD.Nat.pow2(p)), False{}, h), BP.Pow2.pos(p))))
    case 1n+(+m):
      +pw = RD.Nat.pow2(p)
      +dm = Nat.double(m)
      +x : Nat = 2n+dm
      +nn : Nat = 1n+m
      +w = RD.Nat.monus(x, pw)
      # the loop's first step on 2n halves to n with a zero bit
      +e1 = Equal.cong(Bool, RD.Tr, z => RD.Tr.go(x, p, x, z), RD.Nat.lt(x, pw), False{}, h)
      +eh = Equal.cong(Nat, Nat, z => 1n+z, D.Nat.half(dm), m, Y.Nat.half_double(m))
      +eb = Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 0n, 1n), D.Nat.even(dm), True{}, Y.Nat.even_double(m))
      +e2 = Equal.trans(RD.Tr, RD.Tr.up(RD.Tr.go(1n+dm, p, 1n+D.Nat.half(dm), RD.Nat.lt(1n+D.Nat.half(dm), pw)), RD.Nat.bit(dm), w), RD.Tr.up(RD.Tr.go(1n+dm, p, nn, RD.Nat.lt(nn, pw)), RD.Nat.bit(dm), w), RD.Tr.up(RD.Tr.go(1n+dm, p, nn, RD.Nat.lt(nn, pw)), 0n, w),
        Equal.cong(Nat, RD.Tr, z => RD.Tr.up(RD.Tr.go(1n+dm, p, z, RD.Nat.lt(z, pw)), RD.Nat.bit(dm), w), 1n+D.Nat.half(dm), nn, eh),
        Equal.cong(Nat, RD.Tr, z => RD.Tr.up(RD.Tr.go(1n+dm, p, nn, RD.Nat.lt(nn, pw)), z, w), RD.Nat.bit(dm), 0n, eb))
      # and the fuel 1 + 2m does as well as n
      +hf = BP.Lt.pw(nn, p, 1n+dm, Lt.le(nn, m, RD.Nat.pow2(1n+dm), Equal.trans(Bool, RD.Nat.lt(Nat.add(nn, m), RD.Nat.pow2(1n+dm)), RD.Nat.lt(1n+dm, RD.Nat.pow2(1n+dm)), True{},
        Equal.cong(Nat, Bool, z => RD.Nat.lt(1n+z, RD.Nat.pow2(1n+dm)), Nat.add(m, m), dm, Equal.sym(Nat, dm, Nat.add(m, m), Y.Nat.double_add(m))), BP.Lt.npow(1n+dm))))
      +e3 = Equal.cong(RD.Tr, RD.Tr, z => RD.Tr.up(z, 0n, w), RD.Tr.go(1n+dm, p, nn, RD.Nat.lt(nn, pw)), RD.Tr.go(nn, p, nn, RD.Nat.lt(nn, pw)),
        BP.Fuel.go(1n+dm, nn, p, nn, RD.Nat.lt(nn, pw), {==}, hf, BP.Lt.pw(nn, p, nn, BP.Lt.npow(nn))))
      Equal.trans(RD.Tr, RD.Tr.go(x, p, x, RD.Nat.lt(x, pw)), RD.Tr.go(x, p, x, False{}), RD.Tr.up(RD.Tr.of(p, nn), 0n, w), e1,
        Equal.trans(RD.Tr, RD.Tr.go(x, p, x, False{}), RD.Tr.up(RD.Tr.go(1n+dm, p, nn, RD.Nat.lt(nn, pw)), 0n, w), RD.Tr.up(RD.Tr.of(p, nn), 0n, w), e2, e3))

def Lt.dlo(+n: Nat, +c: Nat, +h: {RD.Nat.lt(Nat.double(n), c) == True{} : Bool}) -> {RD.Nat.lt(n, c) == True{} : Bool}:
  Lt.le(n, n, c, Equal.trans(Bool, RD.Nat.lt(Nat.add(n, n), c), RD.Nat.lt(Nat.double(n), c), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, c), Nat.add(n, n), Nat.double(n), Equal.sym(Nat, Nat.double(n), Nat.add(n, n), Y.Nat.double_add(n))), h))

def Sc.near.go(+p: Nat, +n: Nat, b: Bool, +eb: {RD.Nat.lt(Nat.double(n), RD.Nat.pow2(p)) == b : Bool}) -> {Rn(p, Nat.double(n)) == Nat.double(Rn(p, n)) : Nat}:
  match b:
    case True{}:
      +pw = RD.Nat.pow2(p)
      Equal.trans(Nat, RD.Tr.near(RD.Tr.of(p, Nat.double(n))), Nat.double(n), Nat.double(RD.Tr.near(RD.Tr.of(p, n))),
        Equal.trans(Nat, RD.Tr.near(RD.Tr.of(p, Nat.double(n))), RD.Tr.near(RD.Tr{0n, Nat.double(n), 0n, 0n, 0n}), Nat.double(n),
          Equal.cong(RD.Tr, Nat, z => RD.Tr.near(z), RD.Tr.of(p, Nat.double(n)), RD.Tr{0n, Nat.double(n), 0n, 0n, 0n}, Tr.of.lo(p, Nat.double(n), eb)), Near.base(Nat.double(n))),
        Equal.cong(Nat, Nat, z => Nat.double(z), n, RD.Tr.near(RD.Tr.of(p, n)),
          Equal.sym(Nat, RD.Tr.near(RD.Tr.of(p, n)), n, Equal.trans(Nat, RD.Tr.near(RD.Tr.of(p, n)), RD.Tr.near(RD.Tr{0n, n, 0n, 0n, 0n}), n,
            Equal.cong(RD.Tr, Nat, z => RD.Tr.near(z), RD.Tr.of(p, n), RD.Tr{0n, n, 0n, 0n, 0n}, Tr.of.lo(p, n, Lt.dlo(n, pw, eb))), Near.base(n)))))
    case False{}:
      +w = RD.Nat.monus(Nat.double(n), RD.Nat.pow2(p))
      Equal.trans(Nat, RD.Tr.near(RD.Tr.of(p, Nat.double(n))), RD.Tr.near(RD.Tr.up(RD.Tr.of(p, n), 0n, w)), Nat.double(RD.Tr.near(RD.Tr.of(p, n))),
        Equal.cong(RD.Tr, Nat, z => RD.Tr.near(z), RD.Tr.of(p, Nat.double(n)), RD.Tr.up(RD.Tr.of(p, n), 0n, w), Sc.hi(p, n, eb)),
        Near.up0(RD.Tr.of(p, n), w))

# R(2n) = 2 R(n)
def Sc.near(+p: Nat, +n: Nat) -> {Rn(p, Nat.double(n)) == Nat.double(Rn(p, n)) : Nat}:
  Sc.near.go(p, n, RD.Nat.lt(Nat.double(n), RD.Nat.pow2(p)), {==})

# Representable magnitudes
# ------------------------

# m 2^j with m < 2^p rounds to itself
def G.lt(+p: Nat, +m: Nat, +j: Nat, +hm: {RD.Nat.lt(m, RD.Nat.pow2(p)) == True{} : Bool}) -> {Rn(p, Nat.mul(m, RD.Nat.pow2(j))) == Nat.mul(m, RD.Nat.pow2(j)) : Nat}:
  match j:
    case 0n:
      +e1 = NL.Nat.mul_one_r(m)
      Equal.trans(Nat, Rn(p, Nat.mul(m, 1n)), m, Nat.mul(m, 1n),
        Equal.trans(Nat, Rn(p, Nat.mul(m, 1n)), Rn(p, m), m, Equal.cong(Nat, Nat, z => Rn(p, z), Nat.mul(m, 1n), m, e1),
          Equal.trans(Nat, Rn(p, m), RD.Tr.near(RD.Tr{0n, m, 0n, 0n, 0n}), m, Equal.cong(RD.Tr, Nat, z => RD.Tr.near(z), RD.Tr.of(p, m), RD.Tr{0n, m, 0n, 0n, 0n}, Tr.of.lo(p, m, hm)), Near.base(m))),
        Equal.sym(Nat, Nat.mul(m, 1n), m, NL.Nat.mul_one_r(m)))
    case 1n+(+k):
      +x = Nat.mul(m, RD.Nat.pow2(k))
      +ed = R.Nat.mul_double(m, RD.Nat.pow2(k))
      Equal.trans(Nat, Rn(p, Nat.mul(m, Nat.double(RD.Nat.pow2(k)))), Nat.double(x), Nat.mul(m, Nat.double(RD.Nat.pow2(k))),
        Equal.trans(Nat, Rn(p, Nat.mul(m, Nat.double(RD.Nat.pow2(k)))), Rn(p, Nat.double(x)), Nat.double(x), Equal.cong(Nat, Nat, z => Rn(p, z), Nat.mul(m, Nat.double(RD.Nat.pow2(k))), Nat.double(x), ed),
          Equal.trans(Nat, Rn(p, Nat.double(x)), Nat.double(Rn(p, x)), Nat.double(x), Sc.near(p, x), Equal.cong(Nat, Nat, z => Nat.double(z), Rn(p, x), x, G.lt(p, m, k, hm)))),
        Equal.sym(Nat, Nat.mul(m, Nat.double(RD.Nat.pow2(k))), Nat.double(x), ed))

def Pow2.pos1(+k: Nat) -> {RD.Nat.lt(0n, RD.Nat.pow2(k)) == True{} : Bool}:
  BP.Pow2.pos(k)

# 1 < 2^(1+k)
def Lt.one(+k: Nat) -> {RD.Nat.lt(1n, RD.Nat.pow2(1n+k)) == True{} : Bool}:
  +w = RD.Nat.monus(RD.Nat.pow2(k), 1n)
  +e = BP.Lt.wit(0n, RD.Nat.pow2(k))(BP.Pow2.pos(k))
  # 2^(1+k) = 2 (1 + w) = 1 + (1 + 2w)
  Equal.trans(Bool, RD.Nat.lt(1n, Nat.double(RD.Nat.pow2(k))), RD.Nat.lt(1n, Nat.double(1n+w)), True{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(1n, Nat.double(z)), RD.Nat.pow2(k), 1n+w, e), {==})

# m 2^j with m <= 2^p (p >= 1) rounds to itself
def G.le(+p1: Nat, +m: Nat, +j: Nat, w: Nat, +hm: {RD.Nat.pow2(1n+p1) == Nat.add(m, w) : Nat}) -> {Rn(1n+p1, Nat.mul(m, RD.Nat.pow2(j))) == Nat.mul(m, RD.Nat.pow2(j)) : Nat}:
  match w:
    case 0n:
      +p : Nat = 1n+p1
      +pw = RD.Nat.pow2(p)
      +em = Equal.trans(Nat, m, Nat.add(m, 0n), pw, Equal.sym(Nat, Nat.add(m, 0n), m, NL.Nat.add_zero_r(m)), Equal.sym(Nat, pw, Nat.add(m, 0n), hm))
      # m 2^j = 2^(p+j) = 1 2^(p+j)
      +e1 = Equal.trans(Nat, Nat.mul(m, RD.Nat.pow2(j)), Nat.mul(pw, RD.Nat.pow2(j)), Nat.mul(1n, RD.Nat.pow2(Nat.add(p, j))),
        Equal.cong(Nat, Nat, z => Nat.mul(z, RD.Nat.pow2(j)), m, pw, em),
        Equal.trans(Nat, Nat.mul(pw, RD.Nat.pow2(j)), RD.Nat.pow2(Nat.add(p, j)), Nat.mul(1n, RD.Nat.pow2(Nat.add(p, j))),
          Equal.sym(Nat, RD.Nat.pow2(Nat.add(p, j)), Nat.mul(pw, RD.Nat.pow2(j)), BP.Pow2.add(p, j)),
          Equal.sym(Nat, Nat.mul(1n, RD.Nat.pow2(Nat.add(p, j))), RD.Nat.pow2(Nat.add(p, j)), NL.Nat.add_zero_r(RD.Nat.pow2(Nat.add(p, j))))))
      +h1 = Lt.one(p1)
      Equal.trans(Nat, Rn(p, Nat.mul(m, RD.Nat.pow2(j))), Nat.mul(1n, RD.Nat.pow2(Nat.add(p, j))), Nat.mul(m, RD.Nat.pow2(j)),
        Equal.trans(Nat, Rn(p, Nat.mul(m, RD.Nat.pow2(j))), Rn(p, Nat.mul(1n, RD.Nat.pow2(Nat.add(p, j)))), Nat.mul(1n, RD.Nat.pow2(Nat.add(p, j))),
          Equal.cong(Nat, Nat, z => Rn(p, z), Nat.mul(m, RD.Nat.pow2(j)), Nat.mul(1n, RD.Nat.pow2(Nat.add(p, j))), e1), G.lt(p, 1n, Nat.add(p, j), h1)),
        Equal.sym(Nat, Nat.mul(m, RD.Nat.pow2(j)), Nat.mul(1n, RD.Nat.pow2(Nat.add(p, j))), e1))
    case 1n+(+v):
      +pw = RD.Nat.pow2(1n+p1)
      +e = Equal.trans(Nat, pw, Nat.add(m, 1n+v), 1n+Nat.add(m, v), hm, NL.Nat.add_succ_r(m, v))
      +e2 = Equal.trans(Nat, pw, 1n+Nat.add(m, v), Nat.add(m, 1n+v), e, Equal.sym(Nat, Nat.add(m, 1n+v), 1n+Nat.add(m, v), NL.Nat.add_succ_r(m, v)))
      G.lt(1n+p1, m, j, Equal.trans(Bool, RD.Nat.lt(m, pw), RD.Nat.lt(m, Nat.add(m, 1n+v)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(m, z), pw, Nat.add(m, 1n+v), e2), BP.Lt.self(m, v)))

def RF.u(+p1: Nat, +q: Nat, +s: Nat, u: Bool, +hq: {RD.Nat.lt(q, RD.Nat.pow2(1n+p1)) == True{} : Bool})
  -> {Rn(1n+p1, Bool.pick(Nat, u, Nat.mul(1n+q, RD.Nat.pow2(s)), Nat.mul(q, RD.Nat.pow2(s)))) == Bool.pick(Nat, u, Nat.mul(1n+q, RD.Nat.pow2(s)), Nat.mul(q, RD.Nat.pow2(s))) : Nat}:
  match u:
    case True{}:
      G.le(p1, 1n+q, s, RD.Nat.monus(RD.Nat.pow2(1n+p1), 1n+q), BP.Lt.wit(q, RD.Nat.pow2(1n+p1))(hq))
    case False{}:
      G.lt(1n+p1, q, s, hq)

# a rounded value rounds to itself
def RF(+p1: Nat, +n: Nat) -> {Rn(1n+p1, Rn(1n+p1, n)) == Rn(1n+p1, n) : Nat}:
  +t = RD.Tr.of(1n+p1, n)
  RF.u(p1, RD.Tr.q(t), RD.Tr.s(t), RD.Tr.rup(t), TrQ(1n+p1, n))

# Nearest
# -------

def Dist(+a: Nat, +b: Nat) -> Nat:
  Nat.add(RD.Nat.monus(a, b), RD.Nat.monus(b, a))

def Mo.zero(+a: Nat, +k: Nat) -> {RD.Nat.monus(a, Nat.add(a, k)) == 0n : Nat}:
  match a:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case 1n+b:
      Mo.zero(b, k)

def Dist.up(+a: Nat, +k: Nat) -> {Dist(a, Nat.add(a, k)) == k : Nat}:
  Equal.trans(Nat, Nat.add(RD.Nat.monus(a, Nat.add(a, k)), RD.Nat.monus(Nat.add(a, k), a)), Nat.add(0n, RD.Nat.monus(Nat.add(a, k), a)), k,
    Equal.cong(Nat, Nat, z => Nat.add(z, RD.Nat.monus(Nat.add(a, k), a)), RD.Nat.monus(a, Nat.add(a, k)), 0n, Mo.zero(a, k)), R.Nat.monus_add(a, k))

def Dist.dn(+a: Nat, +k: Nat) -> {Dist(Nat.add(a, k), a) == k : Nat}:
  Equal.trans(Nat, Nat.add(RD.Nat.monus(Nat.add(a, k), a), RD.Nat.monus(a, Nat.add(a, k))), Nat.add(k, 0n), k,
    Equal.trans(Nat, Nat.add(RD.Nat.monus(Nat.add(a, k), a), RD.Nat.monus(a, Nat.add(a, k))), Nat.add(k, RD.Nat.monus(a, Nat.add(a, k))), Nat.add(k, 0n),
      Equal.cong(Nat, Nat, z => Nat.add(z, RD.Nat.monus(a, Nat.add(a, k))), RD.Nat.monus(Nat.add(a, k), a), k, R.Nat.monus_add(a, k)),
      Equal.cong(Nat, Nat, z => Nat.add(k, z), RD.Nat.monus(a, Nat.add(a, k)), 0n, Mo.zero(a, k))),
    NL.Nat.add_zero_r(k))

# x = e + k: x is not below e
def Ge.of(+x: Nat, +e: Nat, +k: Nat, +h: {x == Nat.add(e, k) : Nat}) -> {RD.Nat.lt(x, e) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(x, e), RD.Nat.lt(Nat.add(e, k), e), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, e), x, Nat.add(e, k), h), BP.Lt.ge(e, k))

def Lt.cancel.go(+a: Nat, +b: Nat, +x: Nat, +h: {RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)) == True{} : Bool}, l: Bool, +el: {RD.Nat.lt(a, b) == l : Bool}) -> {RD.Nat.lt(a, b) == True{} : Bool}:
  match l:
    case True{}:
      el
    case False{}:
      +w = RD.Nat.monus(a, b)
      +ea = R.Nat.lt_f(a, b)(el)
      +em = Equal.trans(Nat, Nat.mul(a, x), Nat.mul(Nat.add(b, w), x), Nat.add(Nat.mul(b, x), Nat.mul(w, x)), Equal.cong(Nat, Nat, z => Nat.mul(z, x), a, Nat.add(b, w), ea), NL.Nat.mul_dist_r(b, w, x))
      Empty.absurd({RD.Nat.lt(a, b) == True{} : Bool}, Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)), True{},
        Equal.sym(Bool, RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)), False{}, Ge.of(Nat.mul(a, x), Nat.mul(b, x), Nat.mul(w, x), em)), h)))

# aX < bX gives a < b
def Lt.cancel(+a: Nat, +b: Nat, +x: Nat, +h: {RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)) == True{} : Bool}) -> {RD.Nat.lt(a, b) == True{} : Bool}:
  Lt.cancel.go(a, b, x, h, RD.Nat.lt(a, b), {==})

# n = l + r in [l, l + S), e <= r and e <= S - r: every c outside (l, l + S)
# is at least e from n
def Near.pos.go(+n: Nat, +l: Nat, +sv: Nat, +r: Nat, +wr: Nat, +e: Nat, +k1: Nat, +k2: Nat, +c: Nat,
  +hn: {n == Nat.add(l, r) : Nat}, +hs: {sv == Nat.add(Nat.add(r, 1n), wr) : Nat}, +h1: {r == Nat.add(e, k1) : Nat}, +h2: {1n+wr == Nat.add(e, k2) : Nat},
  bl: Bool, +el: {RD.Nat.lt(l, c) == bl : Bool}, bu: Bool, +eu: {RD.Nat.lt(c, Nat.add(l, sv)) == bu : Bool},
  notin: {bl == True{} : Bool} -> {bu == True{} : Bool} -> Empty)
  -> {RD.Nat.lt(Dist(c, n), e) == False{} : Bool}:
  match bl:
    case False{}:
      +w1 = RD.Nat.monus(l, c)
      +hl = R.Nat.lt_f(l, c)(el)
      +en = Equal.trans(Nat, n, Nat.add(Nat.add(c, w1), r), Nat.add(c, Nat.add(w1, r)),
        Equal.trans(Nat, n, Nat.add(l, r), Nat.add(Nat.add(c, w1), r), hn, Equal.cong(Nat, Nat, z => Nat.add(z, r), l, Nat.add(c, w1), hl)), NL.Nat.add_assoc(c, w1, r))
      Ge.of(Dist(c, n), e, Nat.add(w1, k1),
        Equal.trans(Nat, Dist(c, n), Dist(c, Nat.add(c, Nat.add(w1, r))), Nat.add(e, Nat.add(w1, k1)), Equal.cong(Nat, Nat, z => Dist(c, z), n, Nat.add(c, Nat.add(w1, r)), en),
          Equal.trans(Nat, Dist(c, Nat.add(c, Nat.add(w1, r))), Nat.add(w1, r), Nat.add(e, Nat.add(w1, k1)), Dist.up(c, Nat.add(w1, r)),
            Equal.trans(Nat, Nat.add(w1, r), Nat.add(w1, Nat.add(e, k1)), Nat.add(e, Nat.add(w1, k1)), Equal.cong(Nat, Nat, z => Nat.add(w1, z), r, Nat.add(e, k1), h1), NL.Nat.add_swap(w1, e, k1)))))
    case True{}:
      match bu:
        case True{}:
          Empty.absurd({RD.Nat.lt(Dist(c, n), e) == False{} : Bool}, notin({==})({==}))
        case False{}:
          +w2 = RD.Nat.monus(c, Nat.add(l, sv))
          +hc = R.Nat.lt_f(c, Nat.add(l, sv))(eu)
          +kk = Nat.add(1n+wr, w2)
          +env : List<&2, Nat> = [0n, 1n, c, l, sv, w2, r, wr, n]
          +ec = R.NatN.eq2(env, R.V(2n), R.Ad(R.V(8n), R.Ad(R.Ad(R.V(1n), R.V(7n)), R.V(5n))), [], [],
            [R.Ad(R.V(2n), R.Ng(R.Ad(R.Ad(R.V(3n), R.V(4n)), R.V(5n)))), R.Ad(R.V(4n), R.Ng(R.Ad(R.Ad(R.V(6n), R.V(1n)), R.V(7n)))), R.Ad(R.Ad(R.V(3n), R.V(6n)), R.Ng(R.V(8n)))],
            {==}, Unit{}, (R.NatN.z(env, R.V(2n), R.Ad(R.Ad(R.V(3n), R.V(4n)), R.V(5n)), {==}, {==}, hc),
              (R.NatN.z(env, R.V(4n), R.Ad(R.Ad(R.V(6n), R.V(1n)), R.V(7n)), {==}, {==}, hs),
              (R.NatN.z(env, R.Ad(R.V(3n), R.V(6n)), R.V(8n), {==}, {==}, Equal.sym(Nat, n, Nat.add(l, r), hn)), Unit{}))), {==}, {==})
          Ge.of(Dist(c, n), e, Nat.add(k2, w2),
            Equal.trans(Nat, Dist(c, n), Dist(Nat.add(n, kk), n), Nat.add(e, Nat.add(k2, w2)), Equal.cong(Nat, Nat, z => Dist(z, n), c, Nat.add(n, kk), ec),
              Equal.trans(Nat, Dist(Nat.add(n, kk), n), kk, Nat.add(e, Nat.add(k2, w2)), Dist.dn(n, kk),
                Equal.trans(Nat, kk, Nat.add(Nat.add(e, k2), w2), Nat.add(e, Nat.add(k2, w2)), Equal.cong(Nat, Nat, z => Nat.add(z, w2), 1n+wr, Nat.add(e, k2), h2), NL.Nat.add_assoc(e, k2, w2)))))

# c = mc 2^sc with mc <= 2^p cannot lie strictly between q 2^s and (q + 1) 2^s
# (when s > 0, q >= 2^(p-1))
def NotIn.go(+p1: Nat, +q: Nat, +s: Nat, +wq: Nat, hq: @s1: Nat -> {s == 1n+s1 : Nat} -> {q == Nat.add(RD.Nat.pow2(p1), wq) : Nat},
  +mc: Nat, +sc: Nat, +wc: Nat, +hw: {RD.Nat.pow2(1n+p1) == Nat.add(mc, wc) : Nat}, +c: Nat, +hc: {c == Nat.mul(mc, RD.Nat.pow2(sc)) : Nat},
  +hl: {RD.Nat.lt(Nat.mul(q, RD.Nat.pow2(s)), c) == True{} : Bool}, +hu: {RD.Nat.lt(c, Nat.mul(1n+q, RD.Nat.pow2(s))) == True{} : Bool},
  b: Bool, +eb: {RD.Nat.lt(sc, s) == b : Bool}) -> Empty:
  match b:
    case False{}:
      # sc = s + j: c = (mc 2^j) 2^s
      +j = RD.Nat.monus(sc, s)
      +sv = RD.Nat.pow2(s)
      +k = Nat.mul(mc, RD.Nat.pow2(j))
      +es = R.Nat.lt_f(sc, s)(eb)
      +ep = Equal.trans(Nat, RD.Nat.pow2(sc), RD.Nat.pow2(Nat.add(s, j)), Nat.mul(sv, RD.Nat.pow2(j)), Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), sc, Nat.add(s, j), es), BP.Pow2.add(s, j))
      +env : List<&2, Nat> = [0n, c, mc, RD.Nat.pow2(sc), sv, RD.Nat.pow2(j)]
      +ek = R.NatN.eq2(env, R.V(1n), R.Ml(R.Ml(R.V(2n), R.V(5n)), R.V(4n)), [R.V(2n)], [R.Ad(R.V(3n), R.Ng(R.Ml(R.V(4n), R.V(5n))))], [R.Ad(R.V(1n), R.Ng(R.Ml(R.V(2n), R.V(3n))))],
        {==}, (R.NatN.z(env, R.V(3n), R.Ml(R.V(4n), R.V(5n)), {==}, {==}, ep), Unit{}), (R.NatN.z(env, R.V(1n), R.Ml(R.V(2n), R.V(3n)), {==}, {==}, hc), Unit{}), {==}, {==})
      +ql = Lt.cancel(q, k, sv, Equal.trans(Bool, RD.Nat.lt(Nat.mul(q, sv), Nat.mul(k, sv)), RD.Nat.lt(Nat.mul(q, sv), c), True{},
        Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.mul(q, sv), z), Nat.mul(k, sv), c, Equal.sym(Nat, c, Nat.mul(k, sv), ek)), hl))
      +qu = Lt.cancel(k, 1n+q, sv, Equal.trans(Bool, RD.Nat.lt(Nat.mul(k, sv), Nat.mul(1n+q, sv)), RD.Nat.lt(c, Nat.mul(1n+q, sv)), True{},
        Equal.cong(Nat, Bool, z => RD.Nat.lt(z, Nat.mul(1n+q, sv)), Nat.mul(k, sv), c, Equal.sym(Nat, c, Nat.mul(k, sv), ek)), hu))
      +w = RD.Nat.monus(k, 1n+q)
      Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(k, 1n+q), True{}, Equal.sym(Bool, RD.Nat.lt(k, 1n+q), False{}, Ge.of(k, 1n+q, w, BP.Lt.wit(q, k)(ql))), qu))
    case True{}:
      # s = 1 + sc + j: c <= 2^p 2^sc <= 2^(p-1) 2^s <= q 2^s
      +j = RD.Nat.monus(s, 1n+sc)
      +h = RD.Nat.pow2(p1)
      +x = RD.Nat.pow2(sc)
      +zj = RD.Nat.pow2(j)
      +y = RD.Nat.pow2(Nat.add(sc, j))
      +v = RD.Nat.monus(zj, 1n)
      +es = BP.Lt.wit(sc, s)(eb)
      +sv = RD.Nat.pow2(s)
      +ev = Equal.trans(Nat, sv, RD.Nat.pow2(1n+Nat.add(sc, j)), Nat.double(y), Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), s, 1n+Nat.add(sc, j), es), {==})
      +eq = hq(Nat.add(sc, j), es)
      +ww = Nat.add(Nat.add(Nat.mul(wc, x), Nat.mul(Nat.mul(Nat.double(h), x), v)), Nat.mul(wq, sv))
      +env : List<&2, Nat> = [0n, 1n, q, h, wq, sv, y, x, zj, v, mc, wc, c, Nat.double(h), Nat.double(y)]
      +r1 = R.NatN.z(env, R.V(2n), R.Ad(R.V(3n), R.V(4n)), {==}, {==}, eq)
      +r2 = R.NatN.z(env, R.V(5n), R.V(14n), {==}, {==}, ev)
      +r3 = R.NatN.z(env, R.V(14n), R.Ad(R.V(6n), R.V(6n)), {==}, {==}, Y.Nat.double_add(y))
      +r4 = R.NatN.z(env, R.V(6n), R.Ml(R.V(7n), R.V(8n)), {==}, {==}, BP.Pow2.add(sc, j))
      +r5 = R.NatN.z(env, R.V(8n), R.Ad(R.V(1n), R.V(9n)), {==}, {==}, BP.Lt.wit(0n, zj)(BP.Pow2.pos(j)))
      +r6 = R.NatN.z(env, R.V(13n), R.Ad(R.V(10n), R.V(11n)), {==}, {==}, hw)
      +r7 = R.NatN.z(env, R.V(13n), R.Ad(R.V(3n), R.V(3n)), {==}, {==}, Y.Nat.double_add(h))
      +r8 = R.NatN.z(env, R.Ml(R.V(10n), R.V(7n)), R.V(12n), {==}, {==}, Equal.sym(Nat, c, Nat.mul(mc, x), hc))
      +r9 = R.NatN.z(env, R.Ml(R.V(1n), R.V(7n)), R.V(7n), {==}, {==}, NL.Nat.add_zero_r(x))
      +hh = R.Ad(R.V(3n), R.V(3n))
      +el = R.NatN.eq2(env, R.Ml(R.V(2n), R.V(5n)), R.Ad(R.V(12n), R.Ad(R.Ad(R.Ml(R.V(11n), R.V(7n)), R.Ml(R.Ml(R.V(13n), R.V(7n)), R.V(9n))), R.Ml(R.V(4n), R.V(5n)))),
        [R.V(5n), R.V(3n), R.V(3n), hh, R.Ml(hh, R.V(7n)), hh, R.V(7n), R.Ng(R.Ad(R.V(7n), R.Ml(R.V(7n), R.V(9n))))],
        [R.Ad(R.V(2n), R.Ng(R.Ad(R.V(3n), R.V(4n)))), R.Ad(R.V(5n), R.Ng(R.V(14n))), R.Ad(R.V(14n), R.Ng(R.Ad(R.V(6n), R.V(6n)))), R.Ad(R.V(6n), R.Ng(R.Ml(R.V(7n), R.V(8n)))),
         R.Ad(R.V(8n), R.Ng(R.Ad(R.V(1n), R.V(9n)))), R.Ad(R.Ml(R.V(1n), R.V(7n)), R.Ng(R.V(7n))), R.Ad(R.V(13n), R.Ng(R.Ad(R.V(10n), R.V(11n)))), R.Ad(R.V(13n), R.Ng(R.Ad(R.V(3n), R.V(3n))))],
        [R.Ad(R.Ml(R.V(10n), R.V(7n)), R.Ng(R.V(12n)))],
        {==}, (r1, (r2, (r3, (r4, (r5, (r9, (r6, (r7, Unit{})))))))), (r8, Unit{}), {==}, {==})
      Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(Nat.mul(q, sv), c), True{}, Equal.sym(Bool, RD.Nat.lt(Nat.mul(q, sv), c), False{}, Ge.of(Nat.mul(q, sv), c, ww, el)), hl))

def NotIn.cu2(+p1: Nat, +q: Nat, +s: Nat, +wq: Nat, hq: @s1: Nat -> {s == 1n+s1 : Nat} -> {q == Nat.add(RD.Nat.pow2(p1), wq) : Nat},
  +c: Nat, +hl: {RD.Nat.lt(Nat.mul(q, RD.Nat.pow2(s)), c) == True{} : Bool}, +hu: {RD.Nat.lt(c, Nat.mul(1n+q, RD.Nat.pow2(s))) == True{} : Bool},
  +qc: Nat, +sc: Nat, +w: Nat, +hw0: {RD.Nat.pow2(1n+p1) == Nat.add(1n+qc, w) : Nat}, uc: Bool, +ec: {c == Bool.pick(Nat, uc, Nat.mul(1n+qc, RD.Nat.pow2(sc)), Nat.mul(qc, RD.Nat.pow2(sc))) : Nat}) -> Empty:
  match uc:
    case True{}:
      NotIn.go(p1, q, s, wq, hq, 1n+qc, sc, w, hw0, c, ec, hl, hu, RD.Nat.lt(sc, s), {==})
    case False{}:
      NotIn.go(p1, q, s, wq, hq, qc, sc, 1n+w, Equal.trans(Nat, RD.Nat.pow2(1n+p1), 1n+Nat.add(qc, w), Nat.add(qc, 1n+w), hw0, Equal.sym(Nat, Nat.add(qc, 1n+w), 1n+Nat.add(qc, w), NL.Nat.add_succ_r(qc, w))),
        c, ec, hl, hu, RD.Nat.lt(sc, s), {==})

# a representable c is m 2^sc with m <= 2^p: not strictly inside the bracket
def NotIn.cu(+p1: Nat, +q: Nat, +s: Nat, +wq: Nat, hq: @s1: Nat -> {s == 1n+s1 : Nat} -> {q == Nat.add(RD.Nat.pow2(p1), wq) : Nat},
  +c: Nat, +hc: {Rn(1n+p1, c) == c : Nat}, +hl: {RD.Nat.lt(Nat.mul(q, RD.Nat.pow2(s)), c) == True{} : Bool}, +hu: {RD.Nat.lt(c, Nat.mul(1n+q, RD.Nat.pow2(s))) == True{} : Bool},
  uc: Bool, +euc: {RD.Tr.rup(RD.Tr.of(1n+p1, c)) == uc : Bool}) -> Empty:
  +tc = RD.Tr.of(1n+p1, c)
  +qc = RD.Tr.q(tc)
  +sc = RD.Tr.s(tc)
  +pw = RD.Nat.pow2(1n+p1)
  +w = RD.Nat.monus(pw, 1n+qc)
  +hw0 = BP.Lt.wit(qc, pw)(TrQ(1n+p1, c))
  +ec = Equal.trans(Nat, c, Rn(1n+p1, c), Bool.pick(Nat, uc, Nat.mul(1n+qc, RD.Nat.pow2(sc)), Nat.mul(qc, RD.Nat.pow2(sc))), Equal.sym(Nat, Rn(1n+p1, c), c, hc),
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, Nat.mul(1n+qc, RD.Nat.pow2(sc)), Nat.mul(qc, RD.Nat.pow2(sc))), RD.Tr.rup(tc), uc, euc))
  NotIn.cu2(p1, q, s, wq, hq, c, hl, hu, qc, sc, w, hw0, uc, ec)

# rounding down: 2r <= 2^s; rounding up: 2r >= 2^s
def RupF.go(+a: Nat, +b: Nat, +q: Nat, +h: {Bool.and(Bool.not(RD.Nat.lt(a, b)), Bool.or(RD.Nat.lt(b, a), Bool.not(D.Nat.even(q)))) == False{} : Bool}, x: Bool, +ex: {RD.Nat.lt(a, b) == x : Bool})
  -> {RD.Nat.lt(b, a) == False{} : Bool}:
  match x:
    case True{}:
      BP.Lt.asym(a, b, ex)
    case False{}:
      +e = Equal.trans(Bool, Bool.or(RD.Nat.lt(b, a), Bool.not(D.Nat.even(q))), Bool.and(Bool.not(RD.Nat.lt(a, b)), Bool.or(RD.Nat.lt(b, a), Bool.not(D.Nat.even(q)))), False{},
        Equal.sym(Bool, Bool.and(Bool.not(RD.Nat.lt(a, b)), Bool.or(RD.Nat.lt(b, a), Bool.not(D.Nat.even(q)))), Bool.or(RD.Nat.lt(b, a), Bool.not(D.Nat.even(q))),
          Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), Bool.or(RD.Nat.lt(b, a), Bool.not(D.Nat.even(q)))), RD.Nat.lt(a, b), False{}, ex)), h)
      R.Bool.or_f(RD.Nat.lt(b, a), Bool.not(D.Nat.even(q)))(e)

def RupF(+a: Nat, +b: Nat, +q: Nat, +h: {Bool.and(Bool.not(RD.Nat.lt(a, b)), Bool.or(RD.Nat.lt(b, a), Bool.not(D.Nat.even(q)))) == False{} : Bool}) -> {RD.Nat.lt(b, a) == False{} : Bool}:
  RupF.go(a, b, q, h, RD.Nat.lt(a, b), {==})

def RupT(+a: Nat, +b: Nat, +q: Nat, +h: {Bool.and(Bool.not(RD.Nat.lt(a, b)), Bool.or(RD.Nat.lt(b, a), Bool.not(D.Nat.even(q)))) == True{} : Bool}) -> {RD.Nat.lt(a, b) == False{} : Bool}:
  Y.Bool.not_t(RD.Nat.lt(a, b))(R.Bool.and_t1(Bool.not(RD.Nat.lt(a, b)), Bool.or(RD.Nat.lt(b, a), Bool.not(D.Nat.even(q))))(h))

def Near.go(+p1: Nat, +n: Nat, +c: Nat, +hc: {Rn(1n+p1, c) == c : Nat}, u: Bool, +eu: {RD.Tr.rup(RD.Tr.of(1n+p1, n)) == u : Bool})
  -> {RD.Nat.lt(Dist(c, n), Dist(Rn(1n+p1, n), n)) == False{} : Bool}:
  match u:
    case False{}:
      +t = RD.Tr.of(1n+p1, n)
      +s = RD.Tr.s(t)
      +q = RD.Tr.q(t)
      +r = R.Tr.r(t)
      +wr = Tr.wr(t)
      +sv = RD.Nat.pow2(s)
      +l = Nat.mul(q, sv)
      +hn : {n == Nat.add(l, r) : Nat} = Pair.fst({n == Nat.add(l, r) : Nat}, {sv == Nat.add(Nat.add(r, 1n), wr) : Nat}, Sh.n(p1, n))
      +hs : {sv == Nat.add(Nat.add(r, 1n), wr) : Nat} = Pair.snd({n == Nat.add(l, r) : Nat}, {sv == Nat.add(Nat.add(r, 1n), wr) : Nat}, Sh.n(p1, n))
      +hR = Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, Nat.mul(1n+q, sv), l), RD.Tr.rup(t), False{}, eu)
      +e = Dist(Rn(1n+p1, n), n)
      +ed = Equal.trans(Nat, e, Dist(l, Nat.add(l, r)), r, Equal.trans(Nat, e, Dist(l, n), Dist(l, Nat.add(l, r)), Equal.cong(Nat, Nat, z => Dist(z, n), Rn(1n+p1, n), l, hR), Equal.cong(Nat, Nat, z => Dist(l, z), n, Nat.add(l, r), hn)), Dist.up(l, r))
      # 2r <= 2^s: 2^s = 2r + k
      +k = RD.Nat.monus(sv, Nat.double(r))
      +hk = R.Nat.lt_f(sv, Nat.double(r))(RupF(Nat.double(r), sv, q, Equal.trans(Bool, Bool.and(Bool.not(RD.Nat.lt(Nat.double(r), sv)), Bool.or(RD.Nat.lt(sv, Nat.double(r)), Bool.not(D.Nat.even(q)))), RD.Tr.rup(t), False{}, Equal.sym(Bool, RD.Tr.rup(t), Bool.and(Bool.not(RD.Nat.lt(Nat.double(r), sv)), Bool.or(RD.Nat.lt(sv, Nat.double(r)), Bool.not(D.Nat.even(q)))), BP.Rup.acc(t)), eu)))
      +env : List<&2, Nat> = [0n, 1n, r, wr, sv, k, Nat.double(r)]
      +h2r = R.NatN.eq2(env, R.Ad(R.V(1n), R.V(3n)), R.Ad(R.V(2n), R.V(5n)), [], [],
        [R.Ad(R.Ad(R.Ad(R.V(2n), R.V(1n)), R.V(3n)), R.Ng(R.V(4n))), R.Ad(R.V(4n), R.Ng(R.Ad(R.V(6n), R.V(5n)))), R.Ad(R.V(6n), R.Ng(R.Ad(R.V(2n), R.V(2n))))],
        {==}, Unit{}, (R.NatN.z(env, R.Ad(R.Ad(R.V(2n), R.V(1n)), R.V(3n)), R.V(4n), {==}, {==}, Equal.sym(Nat, sv, Nat.add(Nat.add(r, 1n), wr), hs)),
          (R.NatN.z(env, R.V(4n), R.Ad(R.V(6n), R.V(5n)), {==}, {==}, hk), (R.NatN.z(env, R.V(6n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, Y.Nat.double_add(r)), Unit{}))), {==}, {==})
      +h1 = Equal.trans(Nat, r, Nat.add(r, 0n), Nat.add(e, 0n), Equal.sym(Nat, Nat.add(r, 0n), r, NL.Nat.add_zero_r(r)), Equal.cong(Nat, Nat, z => Nat.add(z, 0n), r, e, Equal.sym(Nat, e, r, ed)))
      +h2 = Equal.trans(Nat, 1n+wr, Nat.add(r, k), Nat.add(e, k), h2r, Equal.cong(Nat, Nat, z => Nat.add(z, k), r, e, Equal.sym(Nat, e, r, ed)))
      Near.pos.go(n, l, sv, r, wr, e, 0n, k, c, hn, hs, h1, h2, RD.Nat.lt(l, c), {==}, RD.Nat.lt(c, Nat.add(l, sv)), {==},
        e1 => e2 => NotIn.cu(p1, q, s, Tr.wq(t), s1 => hs1 => Sh.h(RD.Nat.pow2(p1), n, t, R.Inv.of(p1, n), s1, hs1), c, hc, e1,
          Equal.trans(Bool, RD.Nat.lt(c, Nat.mul(1n+q, sv)), RD.Nat.lt(c, Nat.add(l, sv)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(c, z), Nat.add(sv, l), Nat.add(l, sv), NL.Nat.add_comm(sv, l)), e2),
          RD.Tr.rup(RD.Tr.of(1n+p1, c)), {==}))
    case True{}:
      +t = RD.Tr.of(1n+p1, n)
      +s = RD.Tr.s(t)
      +q = RD.Tr.q(t)
      +r = R.Tr.r(t)
      +wr = Tr.wr(t)
      +sv = RD.Nat.pow2(s)
      +l = Nat.mul(q, sv)
      +hn : {n == Nat.add(l, r) : Nat} = Pair.fst({n == Nat.add(l, r) : Nat}, {sv == Nat.add(Nat.add(r, 1n), wr) : Nat}, Sh.n(p1, n))
      +hs : {sv == Nat.add(Nat.add(r, 1n), wr) : Nat} = Pair.snd({n == Nat.add(l, r) : Nat}, {sv == Nat.add(Nat.add(r, 1n), wr) : Nat}, Sh.n(p1, n))
      +hR = Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, Nat.mul(1n+q, sv), l), RD.Tr.rup(t), True{}, eu)
      +e = Dist(Rn(1n+p1, n), n)
      # R = (q + 1) 2^s = n + (1 + wr)
      +env0 : List<&2, Nat> = [0n, 1n, n, l, r, sv, wr]
      +eR = R.NatN.eq2(env0, R.Ad(R.V(5n), R.V(3n)), R.Ad(R.V(2n), R.Ad(R.V(1n), R.V(6n))), [], [],
        [R.Ad(R.Ad(R.V(3n), R.V(4n)), R.Ng(R.V(2n))), R.Ad(R.V(5n), R.Ng(R.Ad(R.Ad(R.V(4n), R.V(1n)), R.V(6n))))],
        {==}, Unit{}, (R.NatN.z(env0, R.Ad(R.V(3n), R.V(4n)), R.V(2n), {==}, {==}, Equal.sym(Nat, n, Nat.add(l, r), hn)), (R.NatN.z(env0, R.V(5n), R.Ad(R.Ad(R.V(4n), R.V(1n)), R.V(6n)), {==}, {==}, hs), Unit{})), {==}, {==})
      +ed = Equal.trans(Nat, e, Dist(Nat.add(n, 1n+wr), n), 1n+wr, Equal.cong(Nat, Nat, z => Dist(z, n), Rn(1n+p1, n), Nat.add(n, 1n+wr), Equal.trans(Nat, Rn(1n+p1, n), Nat.add(sv, l), Nat.add(n, 1n+wr), hR, eR)), Dist.dn(n, 1n+wr))
      # 2r >= 2^s: 2r = 2^s + k
      +k = RD.Nat.monus(Nat.double(r), sv)
      +hk = R.Nat.lt_f(Nat.double(r), sv)(RupT(Nat.double(r), sv, q, Equal.trans(Bool, Bool.and(Bool.not(RD.Nat.lt(Nat.double(r), sv)), Bool.or(RD.Nat.lt(sv, Nat.double(r)), Bool.not(D.Nat.even(q)))), RD.Tr.rup(t), True{}, Equal.sym(Bool, RD.Tr.rup(t), Bool.and(Bool.not(RD.Nat.lt(Nat.double(r), sv)), Bool.or(RD.Nat.lt(sv, Nat.double(r)), Bool.not(D.Nat.even(q)))), BP.Rup.acc(t)), eu)))
      +env : List<&2, Nat> = [0n, 1n, r, wr, sv, k, Nat.double(r)]
      +h1r = R.NatN.eq2(env, R.V(2n), R.Ad(R.Ad(R.V(1n), R.V(3n)), R.V(5n)), [], [],
        [R.Ad(R.V(4n), R.Ng(R.Ad(R.Ad(R.V(2n), R.V(1n)), R.V(3n)))), R.Ad(R.V(6n), R.Ng(R.Ad(R.V(4n), R.V(5n)))), R.Ad(R.Ad(R.V(2n), R.V(2n)), R.Ng(R.V(6n)))],
        {==}, Unit{}, (R.NatN.z(env, R.V(4n), R.Ad(R.Ad(R.V(2n), R.V(1n)), R.V(3n)), {==}, {==}, hs),
          (R.NatN.z(env, R.V(6n), R.Ad(R.V(4n), R.V(5n)), {==}, {==}, hk), (R.NatN.z(env, R.Ad(R.V(2n), R.V(2n)), R.V(6n), {==}, {==}, Equal.sym(Nat, Nat.double(r), Nat.add(r, r), Y.Nat.double_add(r))), Unit{}))), {==}, {==})
      +h1 = Equal.trans(Nat, r, Nat.add(1n+wr, k), Nat.add(e, k), h1r, Equal.cong(Nat, Nat, z => Nat.add(z, k), 1n+wr, e, Equal.sym(Nat, e, 1n+wr, ed)))
      +h2 = Equal.trans(Nat, 1n+wr, Nat.add(1n+wr, 0n), Nat.add(e, 0n), Equal.sym(Nat, Nat.add(1n+wr, 0n), 1n+wr, NL.Nat.add_zero_r(1n+wr)), Equal.cong(Nat, Nat, z => Nat.add(z, 0n), 1n+wr, e, Equal.sym(Nat, e, 1n+wr, ed)))
      Near.pos.go(n, l, sv, r, wr, e, k, 0n, c, hn, hs, h1, h2, RD.Nat.lt(l, c), {==}, RD.Nat.lt(c, Nat.add(l, sv)), {==},
        e1 => e2 => NotIn.cu(p1, q, s, Tr.wq(t), s1 => hs1 => Sh.h(RD.Nat.pow2(p1), n, t, R.Inv.of(p1, n), s1, hs1), c, hc, e1,
          Equal.trans(Bool, RD.Nat.lt(c, Nat.mul(1n+q, sv)), RD.Nat.lt(c, Nat.add(l, sv)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(c, z), Nat.add(sv, l), Nat.add(l, sv), NL.Nat.add_comm(sv, l)), e2),
          RD.Tr.rup(RD.Tr.of(1n+p1, c)), {==}))

# rounding is nearest: no representable c is closer to n than R(n)
def Near(+p1: Nat, +n: Nat, +c: Nat, +hc: {Rn(1n+p1, c) == c : Nat}) -> {RD.Nat.lt(Dist(c, n), Dist(Rn(1n+p1, n), n)) == False{} : Bool}:
  Near.go(p1, n, c, hc, RD.Tr.rup(RD.Tr.of(1n+p1, n)), {==})

# Representable values are m 2^j with m <= 2^p
# --------------------------------------------

def Fm.m(+p: Nat, +c: Nat) -> Nat:
  Bool.pick(Nat, RD.Tr.rup(RD.Tr.of(p, c)), 1n+RD.Tr.q(RD.Tr.of(p, c)), RD.Tr.q(RD.Tr.of(p, c)))

def Fm.j(+p: Nat, +c: Nat) -> Nat:
  RD.Tr.s(RD.Tr.of(p, c))

def Fm.w(+p: Nat, +c: Nat) -> Nat:
  Bool.pick(Nat, RD.Tr.rup(RD.Tr.of(p, c)), RD.Nat.monus(RD.Nat.pow2(p), 1n+RD.Tr.q(RD.Tr.of(p, c))), 1n+RD.Nat.monus(RD.Nat.pow2(p), 1n+RD.Tr.q(RD.Tr.of(p, c))))

def Pick.mul(+u: Bool, +a: Nat, +b: Nat, +x: Nat) -> {Bool.pick(Nat, u, Nat.mul(a, x), Nat.mul(b, x)) == Nat.mul(Bool.pick(Nat, u, a, b), x) : Nat}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

# R(c) = m 2^j
def Fm.eq(+p: Nat, +c: Nat) -> {Rn(p, c) == Nat.mul(Fm.m(p, c), RD.Nat.pow2(Fm.j(p, c))) : Nat}:
  +t = RD.Tr.of(p, c)
  Pick.mul(RD.Tr.rup(t), 1n+RD.Tr.q(t), RD.Tr.q(t), RD.Nat.pow2(RD.Tr.s(t)))

def Fm.w.go(+p1: Nat, +q: Nat, +w: Nat, +hw: {RD.Nat.pow2(1n+p1) == Nat.add(1n+q, w) : Nat}, u: Bool)
  -> {RD.Nat.pow2(1n+p1) == Nat.add(Bool.pick(Nat, u, 1n+q, q), Bool.pick(Nat, u, w, 1n+w)) : Nat}:
  match u:
    case True{}:
      hw
    case False{}:
      Equal.trans(Nat, RD.Nat.pow2(1n+p1), 1n+Nat.add(q, w), Nat.add(q, 1n+w), hw, Equal.sym(Nat, Nat.add(q, 1n+w), 1n+Nat.add(q, w), NL.Nat.add_succ_r(q, w)))

# m <= 2^p
def Fm.le(+p1: Nat, +c: Nat) -> {RD.Nat.pow2(1n+p1) == Nat.add(Fm.m(1n+p1, c), Fm.w(1n+p1, c)) : Nat}:
  +t = RD.Tr.of(1n+p1, c)
  Fm.w.go(p1, RD.Tr.q(t), RD.Nat.monus(RD.Nat.pow2(1n+p1), 1n+RD.Tr.q(t)), BP.Lt.wit(RD.Tr.q(t), RD.Nat.pow2(1n+p1))(TrQ(1n+p1, c)), RD.Tr.rup(t))

# Scaling by 2^g
# --------------

def Sc.pow(+p: Nat, +n: Nat, +g: Nat) -> {Rn(p, Nat.mul(n, RD.Nat.pow2(g))) == Nat.mul(Rn(p, n), RD.Nat.pow2(g)) : Nat}:
  match g:
    case 0n:
      Equal.trans(Nat, Rn(p, Nat.mul(n, 1n)), Rn(p, n), Nat.mul(Rn(p, n), 1n), Equal.cong(Nat, Nat, z => Rn(p, z), Nat.mul(n, 1n), n, NL.Nat.mul_one_r(n)),
        Equal.sym(Nat, Nat.mul(Rn(p, n), 1n), Rn(p, n), NL.Nat.mul_one_r(Rn(p, n))))
    case 1n+(+k):
      +x = Nat.mul(n, RD.Nat.pow2(k))
      Equal.trans(Nat, Rn(p, Nat.mul(n, Nat.double(RD.Nat.pow2(k)))), Nat.double(Nat.mul(Rn(p, n), RD.Nat.pow2(k))), Nat.mul(Rn(p, n), Nat.double(RD.Nat.pow2(k))),
        Equal.trans(Nat, Rn(p, Nat.mul(n, Nat.double(RD.Nat.pow2(k)))), Rn(p, Nat.double(x)), Nat.double(Nat.mul(Rn(p, n), RD.Nat.pow2(k))),
          Equal.cong(Nat, Nat, z => Rn(p, z), Nat.mul(n, Nat.double(RD.Nat.pow2(k))), Nat.double(x), R.Nat.mul_double(n, RD.Nat.pow2(k))),
          Equal.trans(Nat, Rn(p, Nat.double(x)), Nat.double(Rn(p, x)), Nat.double(Nat.mul(Rn(p, n), RD.Nat.pow2(k))), Sc.near(p, x),
            Equal.cong(Nat, Nat, z => Nat.double(z), Rn(p, x), Nat.mul(Rn(p, n), RD.Nat.pow2(k)), Sc.pow(p, n, k)))),
        Equal.sym(Nat, Nat.mul(Rn(p, n), Nat.double(RD.Nat.pow2(k))), Nat.double(Nat.mul(Rn(p, n), RD.Nat.pow2(k))), R.Nat.mul_double(Rn(p, n), RD.Nat.pow2(k))))

# representable stays representable at 2^g times
def Fn.sc(+p: Nat, +n: Nat, +g: Nat, +h: {Rn(p, n) == n : Nat}) -> {Rn(p, Nat.mul(n, RD.Nat.pow2(g))) == Nat.mul(n, RD.Nat.pow2(g)) : Nat}:
  Equal.trans(Nat, Rn(p, Nat.mul(n, RD.Nat.pow2(g))), Nat.mul(Rn(p, n), RD.Nat.pow2(g)), Nat.mul(n, RD.Nat.pow2(g)), Sc.pow(p, n, g),
    Equal.cong(Nat, Nat, z => Nat.mul(z, RD.Nat.pow2(g)), Rn(p, n), n, h))

# monus and distances scale
def Mo.mul.go(+a: Nat, +b: Nat, +x: Nat, l: Bool, +el: {RD.Nat.lt(a, b) == l : Bool}) -> {RD.Nat.monus(Nat.mul(a, x), Nat.mul(b, x)) == Nat.mul(RD.Nat.monus(a, b), x) : Nat}:
  match l:
    case False{}:
      +w = RD.Nat.monus(a, b)
      +ea = R.Nat.lt_f(a, b)(el)
      +em = Equal.trans(Nat, Nat.mul(a, x), Nat.mul(Nat.add(b, w), x), Nat.add(Nat.mul(b, x), Nat.mul(w, x)), Equal.cong(Nat, Nat, z => Nat.mul(z, x), a, Nat.add(b, w), ea), NL.Nat.mul_dist_r(b, w, x))
      Equal.trans(Nat, RD.Nat.monus(Nat.mul(a, x), Nat.mul(b, x)), RD.Nat.monus(Nat.add(Nat.mul(b, x), Nat.mul(w, x)), Nat.mul(b, x)), Nat.mul(w, x),
        Equal.cong(Nat, Nat, z => RD.Nat.monus(z, Nat.mul(b, x)), Nat.mul(a, x), Nat.add(Nat.mul(b, x), Nat.mul(w, x)), em), R.Nat.monus_add(Nat.mul(b, x), Nat.mul(w, x)))
    case True{}:
      +w = RD.Nat.monus(b, 1n+a)
      +eb = BP.Lt.wit(a, b)(el)
      +eb2 = Equal.trans(Nat, b, 1n+Nat.add(a, w), Nat.add(a, 1n+w), eb, Equal.sym(Nat, Nat.add(a, 1n+w), 1n+Nat.add(a, w), NL.Nat.add_succ_r(a, w)))
      +em = Equal.trans(Nat, Nat.mul(b, x), Nat.mul(Nat.add(a, 1n+w), x), Nat.add(Nat.mul(a, x), Nat.mul(1n+w, x)), Equal.cong(Nat, Nat, z => Nat.mul(z, x), b, Nat.add(a, 1n+w), eb2), NL.Nat.mul_dist_r(a, 1n+w, x))
      Equal.trans(Nat, RD.Nat.monus(Nat.mul(a, x), Nat.mul(b, x)), 0n, Nat.mul(RD.Nat.monus(a, b), x),
        Equal.trans(Nat, RD.Nat.monus(Nat.mul(a, x), Nat.mul(b, x)), RD.Nat.monus(Nat.mul(a, x), Nat.add(Nat.mul(a, x), Nat.mul(1n+w, x))), 0n,
          Equal.cong(Nat, Nat, z => RD.Nat.monus(Nat.mul(a, x), z), Nat.mul(b, x), Nat.add(Nat.mul(a, x), Nat.mul(1n+w, x)), em), Mo.zero(Nat.mul(a, x), Nat.mul(1n+w, x))),
        Equal.cong(Nat, Nat, z => Nat.mul(z, x), 0n, RD.Nat.monus(a, b),
          Equal.sym(Nat, RD.Nat.monus(a, b), 0n, Equal.trans(Nat, RD.Nat.monus(a, b), RD.Nat.monus(a, Nat.add(a, 1n+w)), 0n, Equal.cong(Nat, Nat, z => RD.Nat.monus(a, z), b, Nat.add(a, 1n+w), eb2), Mo.zero(a, 1n+w)))))

def Mo.mul(+a: Nat, +b: Nat, +x: Nat) -> {RD.Nat.monus(Nat.mul(a, x), Nat.mul(b, x)) == Nat.mul(RD.Nat.monus(a, b), x) : Nat}:
  Mo.mul.go(a, b, x, RD.Nat.lt(a, b), {==})

def Dist.mul(+a: Nat, +b: Nat, +x: Nat) -> {Dist(Nat.mul(a, x), Nat.mul(b, x)) == Nat.mul(Dist(a, b), x) : Nat}:
  Equal.trans(Nat, Dist(Nat.mul(a, x), Nat.mul(b, x)), Nat.add(Nat.mul(RD.Nat.monus(a, b), x), Nat.mul(RD.Nat.monus(b, a), x)), Nat.mul(Dist(a, b), x),
    Equal.trans(Nat, Dist(Nat.mul(a, x), Nat.mul(b, x)), Nat.add(Nat.mul(RD.Nat.monus(a, b), x), RD.Nat.monus(Nat.mul(b, x), Nat.mul(a, x))), Nat.add(Nat.mul(RD.Nat.monus(a, b), x), Nat.mul(RD.Nat.monus(b, a), x)),
      Equal.cong(Nat, Nat, z => Nat.add(z, RD.Nat.monus(Nat.mul(b, x), Nat.mul(a, x))), RD.Nat.monus(Nat.mul(a, x), Nat.mul(b, x)), Nat.mul(RD.Nat.monus(a, b), x), Mo.mul(a, b, x)),
      Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(RD.Nat.monus(a, b), x), z), RD.Nat.monus(Nat.mul(b, x), Nat.mul(a, x)), Nat.mul(RD.Nat.monus(b, a), x), Mo.mul(b, a, x))),
    Equal.sym(Nat, Nat.mul(Dist(a, b), x), Nat.add(Nat.mul(RD.Nat.monus(a, b), x), Nat.mul(RD.Nat.monus(b, a), x)), NL.Nat.mul_dist_r(RD.Nat.monus(a, b), RD.Nat.monus(b, a), x)))

# Order
# -----

def Le(a: Nat, b: Nat) -> Type:
  {RD.Nat.lt(b, a) == False{} : Bool}

def Le.wit(+a: Nat, +b: Nat, h: Le(a, b)) -> {b == Nat.add(a, RD.Nat.monus(b, a)) : Nat}:
  R.Nat.lt_f(b, a)(h)

def Le.trans(+a: Nat, +b: Nat, +c: Nat, h1: Le(a, b), h2: Le(b, c)) -> Le(a, c):
  +k1 = RD.Nat.monus(b, a)
  +k2 = RD.Nat.monus(c, b)
  Ge.of(c, a, Nat.add(k1, k2), Equal.trans(Nat, c, Nat.add(b, k2), Nat.add(a, Nat.add(k1, k2)), Le.wit(b, c, h2),
    Equal.trans(Nat, Nat.add(b, k2), Nat.add(Nat.add(a, k1), k2), Nat.add(a, Nat.add(k1, k2)), Equal.cong(Nat, Nat, z => Nat.add(z, k2), b, Nat.add(a, k1), Le.wit(a, b, h1)), NL.Nat.add_assoc(a, k1, k2))))

def Le.add(+a: Nat, +k: Nat) -> Le(a, Nat.add(a, k)):
  BP.Lt.ge(a, k)

def Le.eq(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> Le(a, b):
  Ge.of(b, a, 0n, Equal.trans(Nat, b, a, Nat.add(a, 0n), Equal.sym(Nat, a, b, e), Equal.sym(Nat, Nat.add(a, 0n), a, NL.Nat.add_zero_r(a))))

# |u - v| <= u + v
def Dist.le_add(+u: Nat, +v: Nat) -> Le(Dist(u, v), Nat.add(u, v)):
  match u v:
    case 0n v2:
      Le.eq(Dist(0n, v2), Nat.add(0n, v2), Equal.trans(Nat, Dist(0n, v2), Nat.add(RD.Nat.monus(0n, Nat.add(0n, v2)), RD.Nat.monus(Nat.add(0n, v2), 0n)), v2, {==}, Dist.up(0n, v2)))
    case 1n+a 0n:
      Le.eq(Dist(1n+a, 0n), Nat.add(1n+a, 0n), Equal.trans(Nat, Dist(1n+a, 0n), Dist(Nat.add(0n, 1n+a), 0n), Nat.add(1n+a, 0n), {==},
        Equal.trans(Nat, Dist(Nat.add(0n, 1n+a), 0n), 1n+a, Nat.add(1n+a, 0n), Dist.dn(0n, 1n+a), Equal.sym(Nat, Nat.add(1n+a, 0n), 1n+a, NL.Nat.add_zero_r(1n+a)))))
    case 1n+(+a) 1n+(+b):
      # |a - b| <= a + b <= (1 + a) + (1 + b)
      +c : Nat = 1n+Nat.add(a, 1n+b)
      +ec = Equal.trans(Nat, c, 2n+Nat.add(a, b), Nat.add(Nat.add(a, b), 2n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(a, 1n+b), 1n+Nat.add(a, b), NL.Nat.add_succ_r(a, b)),
        Equal.sym(Nat, Nat.add(Nat.add(a, b), 2n), 2n+Nat.add(a, b), Equal.trans(Nat, Nat.add(Nat.add(a, b), 2n), Nat.add(2n, Nat.add(a, b)), 2n+Nat.add(a, b), NL.Nat.add_comm(Nat.add(a, b), 2n), {==})))
      Le.trans(Dist(a, b), Nat.add(a, b), c, Dist.le_add(a, b), Ge.of(c, Nat.add(a, b), 2n, ec))
# The error of a rounded sum
# --------------------------

def Fn.eq(+p: Nat, +x: Nat, +y: Nat, +e: {x == y : Nat}, +f: {Rn(p, y) == y : Nat}) -> {Rn(p, x) == x : Nat}:
  Equal.trans(Nat, Rn(p, x), y, x, Equal.trans(Nat, Rn(p, x), Rn(p, y), y, Equal.cong(Nat, Nat, z => Rn(p, z), x, y, e), f), Equal.sym(Nat, x, y, e))

# every integer up to 2^p is representable
def Small(+p1: Nat, +d: Nat, hd: Le(d, RD.Nat.pow2(1n+p1))) -> {Rn(1n+p1, d) == d : Nat}:
  Fn.eq(1n+p1, d, Nat.mul(d, 1n), Equal.sym(Nat, Nat.mul(d, 1n), d, NL.Nat.mul_one_r(d)),
    G.le(p1, d, 0n, RD.Nat.monus(RD.Nat.pow2(1n+p1), d), Le.wit(d, RD.Nat.pow2(1n+p1), hd)))

def FnS(+p1: Nat, +d: Nat, +a: Nat, +b: Nat, sel: Bool, hda: Le(d, a), hdb: Le(d, b), hs: Le(Bool.pick(Nat, sel, a, b), RD.Nat.pow2(1n+p1))) -> {Rn(1n+p1, d) == d : Nat}:
  match sel:
    case True{}:
      Small(p1, d, Le.trans(d, a, RD.Nat.pow2(1n+p1), hda, hs))
    case False{}:
      Small(p1, d, Le.trans(d, b, RD.Nat.pow2(1n+p1), hdb, hs))

# the error of a + b is at most b and at most a
def LA.s1(+p1: Nat, +a: Nat, +b: Nat, +fa: {Rn(1n+p1, a) == a : Nat}) -> Le(Dist(Rn(1n+p1, Nat.add(a, b)), Nat.add(a, b)), b):
  +x = Nat.add(a, b)
  Le.trans(Dist(Rn(1n+p1, x), x), Dist(a, x), b, Near(p1, x, a, fa), Le.eq(Dist(a, x), b, Dist.up(a, b)))

def LA.s2(+p1: Nat, +a: Nat, +b: Nat, +fb: {Rn(1n+p1, b) == b : Nat}) -> Le(Dist(Rn(1n+p1, Nat.add(a, b)), Nat.add(a, b)), a):
  +x = Nat.add(a, b)
  Le.trans(Dist(Rn(1n+p1, x), x), Dist(b, x), a, Near(p1, x, b, fb),
    Le.eq(Dist(b, x), a, Equal.trans(Nat, Dist(b, x), Dist(b, Nat.add(b, a)), a, Equal.cong(Nat, Nat, z => Dist(b, z), x, Nat.add(b, a), NL.Nat.add_comm(a, b)), Dist.up(b, a))))

# the error of x = a - b is at most b and at most a
def LA.d1(+p1: Nat, +a: Nat, +b: Nat, +x: Nat, +hx: {a == Nat.add(b, x) : Nat}, +fa: {Rn(1n+p1, a) == a : Nat}) -> Le(Dist(Rn(1n+p1, x), x), b):
  Le.trans(Dist(Rn(1n+p1, x), x), Dist(a, x), b, Near(p1, x, a, fa),
    Le.eq(Dist(a, x), b, Equal.trans(Nat, Dist(a, x), Dist(Nat.add(x, b), x), b, Equal.cong(Nat, Nat, z => Dist(z, x), a, Nat.add(x, b), Equal.trans(Nat, a, Nat.add(b, x), Nat.add(x, b), hx, NL.Nat.add_comm(b, x))), Dist.dn(x, b))))

def LA.d2(+p1: Nat, +a: Nat, +b: Nat, +x: Nat, +hx: {a == Nat.add(b, x) : Nat}, +fb: {Rn(1n+p1, b) == b : Nat}) -> Le(Dist(Rn(1n+p1, x), x), a):
  Le.trans(Dist(Rn(1n+p1, x), x), Dist(b, x), a, Near(p1, x, b, fb),
    Le.trans(Dist(b, x), Nat.add(b, x), a, Dist.le_add(b, x), Le.eq(Nat.add(b, x), a, Equal.sym(Nat, a, Nat.add(b, x), hx))))

# scaled: A = A' 2^g, B = B' 2^g with A' or B' at most 2^p
def LA.sc(+p1: Nat, +a: Nat, +b: Nat, +a2: Nat, +b2: Nat, +g: Nat, +ha: {a == Nat.mul(a2, RD.Nat.pow2(g)) : Nat}, +hb: {b == Nat.mul(b2, RD.Nat.pow2(g)) : Nat},
  +fa: {Rn(1n+p1, a2) == a2 : Nat}, +fb: {Rn(1n+p1, b2) == b2 : Nat}, sel: Bool, hs: Le(Bool.pick(Nat, sel, a2, b2), RD.Nat.pow2(1n+p1)))
  -> {Rn(1n+p1, Dist(Rn(1n+p1, Nat.add(a, b)), Nat.add(a, b))) == Dist(Rn(1n+p1, Nat.add(a, b)), Nat.add(a, b)) : Nat}:
  +p : Nat = 1n+p1
  +gg = RD.Nat.pow2(g)
  +x2 = Nat.add(a2, b2)
  +d2 = Dist(Rn(p, x2), x2)
  +ex = Equal.trans(Nat, Nat.add(a, b), Nat.add(Nat.mul(a2, gg), Nat.mul(b2, gg)), Nat.mul(x2, gg),
    Equal.trans(Nat, Nat.add(a, b), Nat.add(Nat.mul(a2, gg), b), Nat.add(Nat.mul(a2, gg), Nat.mul(b2, gg)), Equal.cong(Nat, Nat, z => Nat.add(z, b), a, Nat.mul(a2, gg), ha), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(a2, gg), z), b, Nat.mul(b2, gg), hb)),
    Equal.sym(Nat, Nat.mul(x2, gg), Nat.add(Nat.mul(a2, gg), Nat.mul(b2, gg)), NL.Nat.mul_dist_r(a2, b2, gg)))
  +ed = Equal.trans(Nat, Dist(Rn(p, Nat.add(a, b)), Nat.add(a, b)), Dist(Rn(p, Nat.mul(x2, gg)), Nat.mul(x2, gg)), Nat.mul(d2, gg),
    Equal.cong(Nat, Nat, z => Dist(Rn(p, z), z), Nat.add(a, b), Nat.mul(x2, gg), ex),
    Equal.trans(Nat, Dist(Rn(p, Nat.mul(x2, gg)), Nat.mul(x2, gg)), Dist(Nat.mul(Rn(p, x2), gg), Nat.mul(x2, gg)), Nat.mul(d2, gg),
      Equal.cong(Nat, Nat, z => Dist(z, Nat.mul(x2, gg)), Rn(p, Nat.mul(x2, gg)), Nat.mul(Rn(p, x2), gg), Sc.pow(p, x2, g)), Dist.mul(Rn(p, x2), x2, gg)))
  Fn.eq(p, Dist(Rn(p, Nat.add(a, b)), Nat.add(a, b)), Nat.mul(d2, gg), ed,
    Fn.sc(p, d2, g, FnS(p1, d2, a2, b2, sel, LA.s2(p1, a2, b2, fb), LA.s1(p1, a2, b2, fa), hs)))

# m 2^(j + k) = (m 2^k) 2^j
def Sh.mul(+m: Nat, +j: Nat, +k: Nat, +jj: Nat, +hj: {jj == Nat.add(j, k) : Nat}) -> {Nat.mul(m, RD.Nat.pow2(jj)) == Nat.mul(Nat.mul(m, RD.Nat.pow2(k)), RD.Nat.pow2(j)) : Nat}:
  +env : List<&2, Nat> = [0n, m, RD.Nat.pow2(jj), RD.Nat.pow2(j), RD.Nat.pow2(k)]
  +r = R.NatN.z(env, R.V(2n), R.Ml(R.V(3n), R.V(4n)), {==}, {==}, Equal.trans(Nat, RD.Nat.pow2(jj), RD.Nat.pow2(Nat.add(j, k)), Nat.mul(RD.Nat.pow2(j), RD.Nat.pow2(k)), Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), jj, Nat.add(j, k), hj), BP.Pow2.add(j, k)))
  R.NatN.eq(env, R.Ml(R.V(1n), R.V(2n)), R.Ml(R.Ml(R.V(1n), R.V(4n)), R.V(3n)), [R.V(1n)], [R.Ad(R.V(2n), R.Ng(R.Ml(R.V(3n), R.V(4n))))], {==}, (r, Unit{}), {==}, {==})

def Fm.le2(+p1: Nat, +c: Nat) -> Le(Fm.m(1n+p1, c), RD.Nat.pow2(1n+p1)):
  Ge.of(RD.Nat.pow2(1n+p1), Fm.m(1n+p1, c), Fm.w(1n+p1, c), Fm.le(p1, c))

def Fm.of(+p1: Nat, +c: Nat, +fc: {Rn(1n+p1, c) == c : Nat}) -> {c == Nat.mul(Fm.m(1n+p1, c), RD.Nat.pow2(Fm.j(1n+p1, c))) : Nat}:
  Equal.trans(Nat, c, Rn(1n+p1, c), Nat.mul(Fm.m(1n+p1, c), RD.Nat.pow2(Fm.j(1n+p1, c))), Equal.sym(Nat, Rn(1n+p1, c), c, fc), Fm.eq(1n+p1, c))

# two representable values over a common 2^g, one of them at most 2^p
def Dec.go(+p1: Nat, +a: Nat, +b: Nat, +fa: {Rn(1n+p1, a) == a : Nat}, +fb: {Rn(1n+p1, b) == b : Nat}, -Goal: Type,
  k: @a2: Nat -> @b2: Nat -> @g: Nat -> {a == Nat.mul(a2, RD.Nat.pow2(g)) : Nat} -> {b == Nat.mul(b2, RD.Nat.pow2(g)) : Nat} -> {Rn(1n+p1, a2) == a2 : Nat} -> {Rn(1n+p1, b2) == b2 : Nat} -> @sel: Bool -> Le(Bool.pick(Nat, sel, a2, b2), RD.Nat.pow2(1n+p1)) -> Goal,
  l: Bool, +el: {RD.Nat.lt(Fm.j(1n+p1, a), Fm.j(1n+p1, b)) == l : Bool}) -> Goal:
  match l:
    case False{}:
      +p : Nat = 1n+p1
      +ma = Fm.m(p, a)
      +mb = Fm.m(p, b)
      +ja = Fm.j(p, a)
      +jb = Fm.j(p, b)
      +kk = RD.Nat.monus(ja, jb)
      +ej = R.Nat.lt_f(ja, jb)(el)
      k(Nat.mul(ma, RD.Nat.pow2(kk)), mb, jb,
        Equal.trans(Nat, a, Nat.mul(ma, RD.Nat.pow2(ja)), Nat.mul(Nat.mul(ma, RD.Nat.pow2(kk)), RD.Nat.pow2(jb)), Fm.of(p1, a, fa), Sh.mul(ma, jb, kk, ja, ej)),
        Fm.of(p1, b, fb),
        G.le(p1, ma, kk, Fm.w(p, a), Fm.le(p1, a)),
        Small(p1, mb, Fm.le2(p1, b)),
        False{}, Fm.le2(p1, b))
    case True{}:
      +p : Nat = 1n+p1
      +ma = Fm.m(p, a)
      +mb = Fm.m(p, b)
      +ja = Fm.j(p, a)
      +jb = Fm.j(p, b)
      +w = RD.Nat.monus(jb, 1n+ja)
      +ej = Equal.trans(Nat, jb, 1n+Nat.add(ja, w), Nat.add(ja, 1n+w), BP.Lt.wit(ja, jb)(el), Equal.sym(Nat, Nat.add(ja, 1n+w), 1n+Nat.add(ja, w), NL.Nat.add_succ_r(ja, w)))
      k(ma, Nat.mul(mb, RD.Nat.pow2(1n+w)), ja,
        Fm.of(p1, a, fa),
        Equal.trans(Nat, b, Nat.mul(mb, RD.Nat.pow2(jb)), Nat.mul(Nat.mul(mb, RD.Nat.pow2(1n+w)), RD.Nat.pow2(ja)), Fm.of(p1, b, fb), Sh.mul(mb, ja, 1n+w, jb, ej)),
        Small(p1, ma, Fm.le2(p1, a)),
        G.le(p1, mb, 1n+w, Fm.w(p, b), Fm.le(p1, b)),
        True{}, Fm.le2(p1, a))

def Dec(+p1: Nat, +a: Nat, +b: Nat, +fa: {Rn(1n+p1, a) == a : Nat}, +fb: {Rn(1n+p1, b) == b : Nat}, -Goal: Type,
  k: @a2: Nat -> @b2: Nat -> @g: Nat -> {a == Nat.mul(a2, RD.Nat.pow2(g)) : Nat} -> {b == Nat.mul(b2, RD.Nat.pow2(g)) : Nat} -> {Rn(1n+p1, a2) == a2 : Nat} -> {Rn(1n+p1, b2) == b2 : Nat} -> @sel: Bool -> Le(Bool.pick(Nat, sel, a2, b2), RD.Nat.pow2(1n+p1)) -> Goal) -> Goal:
  Dec.go(p1, a, b, fa, fb, Goal, k, RD.Nat.lt(Fm.j(1n+p1, a), Fm.j(1n+p1, b)), {==})

# Lemma A: the error of a rounded sum of representable values is representable
def LA(+p1: Nat, +a: Nat, +b: Nat, +fa: {Rn(1n+p1, a) == a : Nat}, +fb: {Rn(1n+p1, b) == b : Nat})
  -> {Rn(1n+p1, Dist(Rn(1n+p1, Nat.add(a, b)), Nat.add(a, b))) == Dist(Rn(1n+p1, Nat.add(a, b)), Nat.add(a, b)) : Nat}:
  Dec(p1, a, b, fa, fb, {Rn(1n+p1, Dist(Rn(1n+p1, Nat.add(a, b)), Nat.add(a, b))) == Dist(Rn(1n+p1, Nat.add(a, b)), Nat.add(a, b)) : Nat},
    a2 => b2 => g => ha => hb => fa2 => fb2 => sel => hs => LA.sc(p1, a, b, a2, b2, g, ha, hb, fa2, fb2, sel, hs))

# a < b and x > 0 give a x < b x
def Lt.mono(+a: Nat, +b: Nat, +x: Nat, +hab: {RD.Nat.lt(a, b) == True{} : Bool}, +hx: {RD.Nat.lt(0n, x) == True{} : Bool}) -> {RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)) == True{} : Bool}:
  +w = RD.Nat.monus(b, 1n+a)
  +x1 = RD.Nat.monus(x, 1n)
  +kk = Nat.add(x1, Nat.mul(w, x))
  +env : List<&2, Nat> = [0n, 1n, a, b, x, w, x1]
  +e = R.NatN.eq2(env, R.Ml(R.V(3n), R.V(4n)), R.Ad(R.Ml(R.V(2n), R.V(4n)), R.Ad(R.V(1n), R.Ad(R.V(6n), R.Ml(R.V(5n), R.V(4n))))),
    [R.V(4n)], [R.Ad(R.V(3n), R.Ng(R.Ad(R.Ad(R.V(1n), R.V(2n)), R.V(5n))))], [R.Ad(R.V(4n), R.Ng(R.Ad(R.V(1n), R.V(6n)))), R.Ad(R.Ml(R.V(1n), R.V(4n)), R.Ng(R.V(4n)))],
    {==}, (R.NatN.z(env, R.V(3n), R.Ad(R.Ad(R.V(1n), R.V(2n)), R.V(5n)), {==}, {==}, BP.Lt.wit(a, b)(hab)), Unit{}),
    (R.NatN.z(env, R.V(4n), R.Ad(R.V(1n), R.V(6n)), {==}, {==}, BP.Lt.wit(0n, x)(hx)), (R.NatN.z(env, R.Ml(R.V(1n), R.V(4n)), R.V(4n), {==}, {==}, NL.Nat.add_zero_r(x)), Unit{})), {==}, {==})
  Equal.trans(Bool, RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)), RD.Nat.lt(Nat.mul(a, x), Nat.add(Nat.mul(a, x), 1n+kk)), True{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.mul(a, x), z), Nat.mul(b, x), Nat.add(Nat.mul(a, x), 1n+kk), e), BP.Lt.self(Nat.mul(a, x), kk))

def Le.cancel.go(+b: Nat, +a: Nat, +x: Nat, +hx: {RD.Nat.lt(0n, x) == True{} : Bool}, h: Le(Nat.mul(b, x), Nat.mul(a, x)), l: Bool, +el: {RD.Nat.lt(a, b) == l : Bool}) -> Le(b, a):
  match l:
    case False{}:
      el
    case True{}:
      Empty.absurd(Le(b, a), Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)), True{}, Equal.sym(Bool, RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)), False{}, h), Lt.mono(a, b, x, el, hx))))

def Le.cancel(+b: Nat, +a: Nat, +x: Nat, +hx: {RD.Nat.lt(0n, x) == True{} : Bool}, h: Le(Nat.mul(b, x), Nat.mul(a, x))) -> Le(b, a):
  Le.cancel.go(b, a, x, hx, h, RD.Nat.lt(a, b), {==})

# x = a - b, scaled: x = x' 2^g with a' = b' + x'
def Dif.sc(+a: Nat, +b: Nat, +x: Nat, +hx: {a == Nat.add(b, x) : Nat}, +a2: Nat, +b2: Nat, +g: Nat, +ha: {a == Nat.mul(a2, RD.Nat.pow2(g)) : Nat}, +hb: {b == Nat.mul(b2, RD.Nat.pow2(g)) : Nat})
  -> {x == Nat.mul(RD.Nat.monus(a2, b2), RD.Nat.pow2(g)) : Nat} & {a2 == Nat.add(b2, RD.Nat.monus(a2, b2)) : Nat}:
  +gg = RD.Nat.pow2(g)
  +ex = Equal.trans(Nat, x, RD.Nat.monus(a, b), Nat.mul(RD.Nat.monus(a2, b2), gg),
    Equal.sym(Nat, RD.Nat.monus(a, b), x, Equal.trans(Nat, RD.Nat.monus(a, b), RD.Nat.monus(Nat.add(b, x), b), x, Equal.cong(Nat, Nat, z => RD.Nat.monus(z, b), a, Nat.add(b, x), hx), R.Nat.monus_add(b, x))),
    Equal.trans(Nat, RD.Nat.monus(a, b), RD.Nat.monus(Nat.mul(a2, gg), Nat.mul(b2, gg)), Nat.mul(RD.Nat.monus(a2, b2), gg),
      Equal.trans(Nat, RD.Nat.monus(a, b), RD.Nat.monus(Nat.mul(a2, gg), b), RD.Nat.monus(Nat.mul(a2, gg), Nat.mul(b2, gg)), Equal.cong(Nat, Nat, z => RD.Nat.monus(z, b), a, Nat.mul(a2, gg), ha), Equal.cong(Nat, Nat, z => RD.Nat.monus(Nat.mul(a2, gg), z), b, Nat.mul(b2, gg), hb)),
      Mo.mul(a2, b2, gg)))
  hle = Le.trans(Nat.mul(b2, gg), b, Nat.mul(a2, gg), Le.eq(Nat.mul(b2, gg), b, Equal.sym(Nat, b, Nat.mul(b2, gg), hb)),
    Le.trans(b, a, Nat.mul(a2, gg), Ge.of(a, b, x, hx), Le.eq(a, Nat.mul(a2, gg), ha)))
  (ex, Le.wit(b2, a2, Le.cancel(b2, a2, gg, BP.Pow2.pos(g), hle)))

# Lemma A for a difference x = a - b of representable values
def LA.dsc(+p1: Nat, +a: Nat, +b: Nat, +x: Nat, +hx: {a == Nat.add(b, x) : Nat}, +a2: Nat, +b2: Nat, +g: Nat, +ha: {a == Nat.mul(a2, RD.Nat.pow2(g)) : Nat}, +hb: {b == Nat.mul(b2, RD.Nat.pow2(g)) : Nat},
  +fa: {Rn(1n+p1, a2) == a2 : Nat}, +fb: {Rn(1n+p1, b2) == b2 : Nat}, sel: Bool, hs: Le(Bool.pick(Nat, sel, a2, b2), RD.Nat.pow2(1n+p1)))
  -> {Rn(1n+p1, Dist(Rn(1n+p1, x), x)) == Dist(Rn(1n+p1, x), x) : Nat}:
  +p : Nat = 1n+p1
  +gg = RD.Nat.pow2(g)
  +x2 = RD.Nat.monus(a2, b2)
  +d2 = Dist(Rn(p, x2), x2)
  +ex : {x == Nat.mul(x2, gg) : Nat} = Pair.fst({x == Nat.mul(x2, gg) : Nat}, {a2 == Nat.add(b2, x2) : Nat}, Dif.sc(a, b, x, hx, a2, b2, g, ha, hb))
  +ea : {a2 == Nat.add(b2, x2) : Nat} = Pair.snd({x == Nat.mul(x2, gg) : Nat}, {a2 == Nat.add(b2, x2) : Nat}, Dif.sc(a, b, x, hx, a2, b2, g, ha, hb))
  +ed = Equal.trans(Nat, Dist(Rn(p, x), x), Dist(Rn(p, Nat.mul(x2, gg)), Nat.mul(x2, gg)), Nat.mul(d2, gg),
    Equal.cong(Nat, Nat, z => Dist(Rn(p, z), z), x, Nat.mul(x2, gg), ex),
    Equal.trans(Nat, Dist(Rn(p, Nat.mul(x2, gg)), Nat.mul(x2, gg)), Dist(Nat.mul(Rn(p, x2), gg), Nat.mul(x2, gg)), Nat.mul(d2, gg),
      Equal.cong(Nat, Nat, z => Dist(z, Nat.mul(x2, gg)), Rn(p, Nat.mul(x2, gg)), Nat.mul(Rn(p, x2), gg), Sc.pow(p, x2, g)), Dist.mul(Rn(p, x2), x2, gg)))
  Fn.eq(p, Dist(Rn(p, x), x), Nat.mul(d2, gg), ed,
    Fn.sc(p, d2, g, FnS(p1, d2, a2, b2, sel, LA.d2(p1, a2, b2, x2, ea, fb), LA.d1(p1, a2, b2, x2, ea, fa), hs)))

def LA.d(+p1: Nat, +a: Nat, +b: Nat, +x: Nat, +hx: {a == Nat.add(b, x) : Nat}, +fa: {Rn(1n+p1, a) == a : Nat}, +fb: {Rn(1n+p1, b) == b : Nat})
  -> {Rn(1n+p1, Dist(Rn(1n+p1, x), x)) == Dist(Rn(1n+p1, x), x) : Nat}:
  Dec(p1, a, b, fa, fb, {Rn(1n+p1, Dist(Rn(1n+p1, x), x)) == Dist(Rn(1n+p1, x), x) : Nat},
    a2 => b2 => g => ha => hb => fa2 => fb2 => sel => hs => LA.dsc(p1, a, b, x, hx, a2, b2, g, ha, hb, fa2, fb2, sel, hs))

# Sterbenz: b <= a <= 2b makes a - b representable
def St.sc(+p1: Nat, +a: Nat, +b: Nat, +x: Nat, +hx: {a == Nat.add(b, x) : Nat}, h2: Le(a, Nat.double(b)), +a2: Nat, +b2: Nat, +g: Nat, +ha: {a == Nat.mul(a2, RD.Nat.pow2(g)) : Nat}, +hb: {b == Nat.mul(b2, RD.Nat.pow2(g)) : Nat},
  +fa: {Rn(1n+p1, a2) == a2 : Nat}, +fb: {Rn(1n+p1, b2) == b2 : Nat}, sel: Bool, hs: Le(Bool.pick(Nat, sel, a2, b2), RD.Nat.pow2(1n+p1)))
  -> {Rn(1n+p1, x) == x : Nat}:
  +p : Nat = 1n+p1
  +gg = RD.Nat.pow2(g)
  +x2 = RD.Nat.monus(a2, b2)
  +ex : {x == Nat.mul(x2, gg) : Nat} = Pair.fst({x == Nat.mul(x2, gg) : Nat}, {a2 == Nat.add(b2, x2) : Nat}, Dif.sc(a, b, x, hx, a2, b2, g, ha, hb))
  +ea : {a2 == Nat.add(b2, x2) : Nat} = Pair.snd({x == Nat.mul(x2, gg) : Nat}, {a2 == Nat.add(b2, x2) : Nat}, Dif.sc(a, b, x, hx, a2, b2, g, ha, hb))
  # a' <= 2b', so x' <= b'
  +e2b = Equal.trans(Nat, Nat.double(b), Nat.double(Nat.mul(b2, gg)), Nat.mul(Nat.double(b2), gg), Equal.cong(Nat, Nat, z => Nat.double(z), b, Nat.mul(b2, gg), hb),
    Equal.sym(Nat, Nat.mul(Nat.double(b2), gg), Nat.double(Nat.mul(b2, gg)), BP.Mul.dbl_l(b2, gg)))
  h22 = Le.cancel(a2, Nat.double(b2), gg, BP.Pow2.pos(g), Le.trans(Nat.mul(a2, gg), a, Nat.mul(Nat.double(b2), gg), Le.eq(Nat.mul(a2, gg), a, Equal.sym(Nat, a, Nat.mul(a2, gg), ha)),
    Le.trans(a, Nat.double(b), Nat.mul(Nat.double(b2), gg), h2, Le.eq(Nat.double(b), Nat.mul(Nat.double(b2), gg), e2b))))
  hxb : Le(x2, b2) = Equal.trans(Bool, RD.Nat.lt(b2, x2), RD.Nat.lt(Nat.add(b2, b2), Nat.add(b2, x2)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.add(b2, b2), Nat.add(b2, x2)), RD.Nat.lt(b2, x2), BP.Lt.shift(b2, b2, x2)),
    Equal.trans(Bool, RD.Nat.lt(Nat.add(b2, b2), Nat.add(b2, x2)), RD.Nat.lt(Nat.double(b2), a2), False{},
      Equal.trans(Bool, RD.Nat.lt(Nat.add(b2, b2), Nat.add(b2, x2)), RD.Nat.lt(Nat.double(b2), Nat.add(b2, x2)), RD.Nat.lt(Nat.double(b2), a2),
        Equal.cong(Nat, Bool, z => RD.Nat.lt(z, Nat.add(b2, x2)), Nat.add(b2, b2), Nat.double(b2), Equal.sym(Nat, Nat.double(b2), Nat.add(b2, b2), Y.Nat.double_add(b2))),
        Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.double(b2), z), Nat.add(b2, x2), a2, Equal.sym(Nat, a2, Nat.add(b2, x2), ea))), h22))
  hxa : Le(x2, a2) = Ge.of(a2, x2, b2, Equal.trans(Nat, a2, Nat.add(b2, x2), Nat.add(x2, b2), ea, NL.Nat.add_comm(b2, x2)))
  Fn.eq(p, x, Nat.mul(x2, gg), ex, Fn.sc(p, x2, g, FnS(p1, x2, a2, b2, sel, hxa, hxb, hs)))

def Sterbenz(+p1: Nat, +a: Nat, +b: Nat, +x: Nat, +hx: {a == Nat.add(b, x) : Nat}, h2: Le(a, Nat.double(b)), +fa: {Rn(1n+p1, a) == a : Nat}, +fb: {Rn(1n+p1, b) == b : Nat})
  -> {Rn(1n+p1, x) == x : Nat}:
  Dec(p1, a, b, fa, fb, {Rn(1n+p1, x) == x : Nat},
    a2 => b2 => g => ha => hb => fa2 => fb2 => sel => hs => St.sc(p1, a, b, x, hx, h2, a2, b2, g, ha, hb, fa2, fb2, sel, hs))

# Monotonicity
# ------------

# c <= x, c representable: c <= R(x)
def Mono.lo.go(+p1: Nat, +x: Nat, +c: Nat, +fc: {Rn(1n+p1, c) == c : Nat}, h: Le(c, x), l: Bool, +el: {RD.Nat.lt(Rn(1n+p1, x), c) == l : Bool}) -> Le(c, Rn(1n+p1, x)):
  match l:
    case False{}:
      el
    case True{}:
      +rx = Rn(1n+p1, x)
      +w = RD.Nat.monus(c, 1n+rx)
      +k = RD.Nat.monus(x, c)
      +ec = BP.Lt.wit(rx, c)(el)
      +ex = Le.wit(c, x, h)
      # x = R + 1 + (w + k)
      +ex2 = Equal.trans(Nat, x, Nat.add(Nat.add(1n+rx, w), k), Nat.add(rx, 1n+Nat.add(w, k)),
        Equal.trans(Nat, x, Nat.add(c, k), Nat.add(Nat.add(1n+rx, w), k), ex, Equal.cong(Nat, Nat, z => Nat.add(z, k), c, Nat.add(1n+rx, w), ec)),
        Equal.trans(Nat, Nat.add(Nat.add(1n+rx, w), k), 1n+Nat.add(rx, Nat.add(w, k)), Nat.add(rx, 1n+Nat.add(w, k)),
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(rx, w), k), Nat.add(rx, Nat.add(w, k)), NL.Nat.add_assoc(rx, w, k)),
          Equal.sym(Nat, Nat.add(rx, 1n+Nat.add(w, k)), 1n+Nat.add(rx, Nat.add(w, k)), NL.Nat.add_succ_r(rx, Nat.add(w, k)))))
      +dr = Equal.trans(Nat, Dist(rx, x), Dist(rx, Nat.add(rx, 1n+Nat.add(w, k))), 1n+Nat.add(w, k), Equal.cong(Nat, Nat, z => Dist(rx, z), x, Nat.add(rx, 1n+Nat.add(w, k)), ex2), Dist.up(rx, 1n+Nat.add(w, k)))
      +dc = Equal.trans(Nat, Dist(c, x), Dist(c, Nat.add(c, k)), k, Equal.cong(Nat, Nat, z => Dist(c, z), x, Nat.add(c, k), ex), Dist.up(c, k))
      # Near says Dist(R, x) <= Dist(c, x), that is 1 + w + k <= k
      +nr = Near(p1, x, c, fc)
      +bad = Equal.trans(Bool, RD.Nat.lt(k, 1n+Nat.add(w, k)), RD.Nat.lt(Dist(c, x), Dist(rx, x)), False{},
        Equal.trans(Bool, RD.Nat.lt(k, 1n+Nat.add(w, k)), RD.Nat.lt(Dist(c, x), 1n+Nat.add(w, k)), RD.Nat.lt(Dist(c, x), Dist(rx, x)),
          Equal.cong(Nat, Bool, z => RD.Nat.lt(z, 1n+Nat.add(w, k)), k, Dist(c, x), Equal.sym(Nat, Dist(c, x), k, dc)),
          Equal.cong(Nat, Bool, z => RD.Nat.lt(Dist(c, x), z), 1n+Nat.add(w, k), Dist(rx, x), Equal.sym(Nat, Dist(rx, x), 1n+Nat.add(w, k), dr))), nr)
      +good = Equal.trans(Bool, RD.Nat.lt(k, 1n+Nat.add(w, k)), RD.Nat.lt(k, Nat.add(k, 1n+w)), True{},
        Equal.cong(Nat, Bool, z => RD.Nat.lt(k, z), 1n+Nat.add(w, k), Nat.add(k, 1n+w), Equal.trans(Nat, 1n+Nat.add(w, k), 1n+Nat.add(k, w), Nat.add(k, 1n+w), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(w, k), Nat.add(k, w), NL.Nat.add_comm(w, k)), Equal.sym(Nat, Nat.add(k, 1n+w), 1n+Nat.add(k, w), NL.Nat.add_succ_r(k, w)))),
        BP.Lt.self(k, w))
      Empty.absurd(Le(c, rx), Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(k, 1n+Nat.add(w, k)), True{}, Equal.sym(Bool, RD.Nat.lt(k, 1n+Nat.add(w, k)), False{}, bad), good)))

def Mono.lo(+p1: Nat, +x: Nat, +c: Nat, +fc: {Rn(1n+p1, c) == c : Nat}, h: Le(c, x)) -> Le(c, Rn(1n+p1, x)):
  Mono.lo.go(p1, x, c, fc, h, RD.Nat.lt(Rn(1n+p1, x), c), {==})

# x <= c, c representable: R(x) <= c
def Mono.hi.go(+p1: Nat, +x: Nat, +c: Nat, +fc: {Rn(1n+p1, c) == c : Nat}, h: Le(x, c), l: Bool, +el: {RD.Nat.lt(c, Rn(1n+p1, x)) == l : Bool}) -> Le(Rn(1n+p1, x), c):
  match l:
    case False{}:
      el
    case True{}:
      +rx = Rn(1n+p1, x)
      +w = RD.Nat.monus(rx, 1n+c)
      +k = RD.Nat.monus(c, x)
      +er = BP.Lt.wit(c, rx)(el)
      +ec = Le.wit(x, c, h)
      # R = x + 1 + (k + w)
      +er2 = Equal.trans(Nat, rx, Nat.add(1n+Nat.add(x, k), w), Nat.add(x, 1n+Nat.add(k, w)),
        Equal.trans(Nat, rx, Nat.add(1n+c, w), Nat.add(1n+Nat.add(x, k), w), er, Equal.cong(Nat, Nat, z => Nat.add(1n+z, w), c, Nat.add(x, k), ec)),
        Equal.trans(Nat, 1n+Nat.add(Nat.add(x, k), w), 1n+Nat.add(x, Nat.add(k, w)), Nat.add(x, 1n+Nat.add(k, w)),
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(x, k), w), Nat.add(x, Nat.add(k, w)), NL.Nat.add_assoc(x, k, w)),
          Equal.sym(Nat, Nat.add(x, 1n+Nat.add(k, w)), 1n+Nat.add(x, Nat.add(k, w)), NL.Nat.add_succ_r(x, Nat.add(k, w)))))
      +dr = Equal.trans(Nat, Dist(rx, x), Dist(Nat.add(x, 1n+Nat.add(k, w)), x), 1n+Nat.add(k, w), Equal.cong(Nat, Nat, z => Dist(z, x), rx, Nat.add(x, 1n+Nat.add(k, w)), er2), Dist.dn(x, 1n+Nat.add(k, w)))
      +dc = Equal.trans(Nat, Dist(c, x), Dist(Nat.add(x, k), x), k, Equal.cong(Nat, Nat, z => Dist(z, x), c, Nat.add(x, k), ec), Dist.dn(x, k))
      +nr = Near(p1, x, c, fc)
      +bad = Equal.trans(Bool, RD.Nat.lt(k, 1n+Nat.add(k, w)), RD.Nat.lt(Dist(c, x), Dist(rx, x)), False{},
        Equal.trans(Bool, RD.Nat.lt(k, 1n+Nat.add(k, w)), RD.Nat.lt(Dist(c, x), 1n+Nat.add(k, w)), RD.Nat.lt(Dist(c, x), Dist(rx, x)),
          Equal.cong(Nat, Bool, z => RD.Nat.lt(z, 1n+Nat.add(k, w)), k, Dist(c, x), Equal.sym(Nat, Dist(c, x), k, dc)),
          Equal.cong(Nat, Bool, z => RD.Nat.lt(Dist(c, x), z), 1n+Nat.add(k, w), Dist(rx, x), Equal.sym(Nat, Dist(rx, x), 1n+Nat.add(k, w), dr))), nr)
      +good = Equal.trans(Bool, RD.Nat.lt(k, 1n+Nat.add(k, w)), RD.Nat.lt(k, Nat.add(k, 1n+w)), True{},
        Equal.cong(Nat, Bool, z => RD.Nat.lt(k, z), 1n+Nat.add(k, w), Nat.add(k, 1n+w), Equal.sym(Nat, Nat.add(k, 1n+w), 1n+Nat.add(k, w), NL.Nat.add_succ_r(k, w))),
        BP.Lt.self(k, w))
      Empty.absurd(Le(rx, c), Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(k, 1n+Nat.add(k, w)), True{}, Equal.sym(Bool, RD.Nat.lt(k, 1n+Nat.add(k, w)), False{}, bad), good)))

def Mono.hi(+p1: Nat, +x: Nat, +c: Nat, +fc: {Rn(1n+p1, c) == c : Nat}, h: Le(x, c)) -> Le(Rn(1n+p1, x), c):
  Mono.hi.go(p1, x, c, fc, h, RD.Nat.lt(c, Rn(1n+p1, x)), {==})

# Fast2Sum, magnitudes
# --------------------

def Fn.dbl(+p1: Nat, +a: Nat, +fa: {Rn(1n+p1, a) == a : Nat}) -> {Rn(1n+p1, Nat.double(a)) == Nat.double(a) : Nat}:
  Fn.eq(1n+p1, Nat.double(a), Nat.mul(a, RD.Nat.pow2(1n)), Equal.sym(Nat, Nat.mul(a, 2n), Nat.double(a), R.Nat.mul2(a)), Fn.sc(1n+p1, a, 1n, fa))

def Le.dbl_add(+a: Nat, +b: Nat, h: Le(b, a)) -> Le(Nat.add(a, b), Nat.double(a)):
  Equal.trans(Bool, RD.Nat.lt(Nat.double(a), Nat.add(a, b)), RD.Nat.lt(Nat.add(a, a), Nat.add(a, b)), False{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(z, Nat.add(a, b)), Nat.double(a), Nat.add(a, a), Y.Nat.double_add(a)),
    Equal.trans(Bool, RD.Nat.lt(Nat.add(a, a), Nat.add(a, b)), RD.Nat.lt(a, b), False{}, BP.Lt.shift(a, a, b), h))

# same signs, b <= a: R(a + b) = a + d with d representable
def F2S.same(+p1: Nat, +a: Nat, +b: Nat, +fa: {Rn(1n+p1, a) == a : Nat}, hb: Le(b, a))
  -> {Rn(1n+p1, Nat.add(a, b)) == Nat.add(a, RD.Nat.monus(Rn(1n+p1, Nat.add(a, b)), a)) : Nat} & {Rn(1n+p1, RD.Nat.monus(Rn(1n+p1, Nat.add(a, b)), a)) == RD.Nat.monus(Rn(1n+p1, Nat.add(a, b)), a) : Nat}:
  +p : Nat = 1n+p1
  +s = Rn(p, Nat.add(a, b))
  +d = RD.Nat.monus(s, a)
  +es = Le.wit(a, s, Mono.lo(p1, Nat.add(a, b), a, fa, Le.add(a, b)))
  h2 = Mono.hi(p1, Nat.add(a, b), Nat.double(a), Fn.dbl(p1, a, fa), Le.dbl_add(a, b, hb))
  (es, Sterbenz(p1, s, a, d, es, h2, RF(p1, Nat.add(a, b)), fa))

# opposite signs, a = b + x. The result: a = R(x) + d with d representable
def F2S.exact(+p1: Nat, +a: Nat, +b: Nat, +x: Nat, +hx: {a == Nat.add(b, x) : Nat}, +fb: {Rn(1n+p1, b) == b : Nat}, +fx: {Rn(1n+p1, x) == x : Nat})
  -> {a == Nat.add(Rn(1n+p1, x), RD.Nat.monus(a, Rn(1n+p1, x))) : Nat} & {Rn(1n+p1, RD.Nat.monus(a, Rn(1n+p1, x))) == RD.Nat.monus(a, Rn(1n+p1, x)) : Nat}:
  +p : Nat = 1n+p1
  +eax = Equal.trans(Nat, a, Nat.add(b, x), Nat.add(x, b), hx, NL.Nat.add_comm(b, x))
  +em = Equal.trans(Nat, RD.Nat.monus(a, Rn(p, x)), RD.Nat.monus(Nat.add(x, b), x), b,
    Equal.trans(Nat, RD.Nat.monus(a, Rn(p, x)), RD.Nat.monus(a, x), RD.Nat.monus(Nat.add(x, b), x), Equal.cong(Nat, Nat, z => RD.Nat.monus(a, z), Rn(p, x), x, fx), Equal.cong(Nat, Nat, z => RD.Nat.monus(z, x), a, Nat.add(x, b), eax)),
    R.Nat.monus_add(x, b))
  (Equal.trans(Nat, a, Nat.add(x, b), Nat.add(Rn(p, x), RD.Nat.monus(a, Rn(p, x))), eax,
     Equal.trans(Nat, Nat.add(x, b), Nat.add(Rn(p, x), b), Nat.add(Rn(p, x), RD.Nat.monus(a, Rn(p, x))), Equal.cong(Nat, Nat, z => Nat.add(z, b), x, Rn(p, x), Equal.sym(Nat, Rn(p, x), x, fx)),
       Equal.cong(Nat, Nat, z => Nat.add(Rn(p, x), z), b, RD.Nat.monus(a, Rn(p, x)), Equal.sym(Nat, RD.Nat.monus(a, Rn(p, x)), b, em)))),
   Fn.eq(p, RD.Nat.monus(a, Rn(p, x)), b, em, fb))

def Le.dd(+a: Nat, +b: Nat, h: Le(a, b)) -> Le(Nat.double(a), Nat.double(b)):
  Equal.trans(Bool, RD.Nat.lt(Nat.double(b), Nat.double(a)), RD.Nat.lt(b, a), False{}, Lt.dd(b, a), h)

def F2S.opp.j(+p1: Nat, +a: Nat, +b: Nat, +x: Nat, +hx: {a == Nat.add(b, x) : Nat}, +fa: {Rn(1n+p1, a) == a : Nat}, +fb: {Rn(1n+p1, b) == b : Nat},
  +el: {RD.Nat.lt(Nat.double(b), a) == True{} : Bool}, j: Nat, +ej: {Fm.j(1n+p1, a) == j : Nat})
  -> {a == Nat.add(Rn(1n+p1, x), RD.Nat.monus(a, Rn(1n+p1, x))) : Nat} & {Rn(1n+p1, RD.Nat.monus(a, Rn(1n+p1, x))) == RD.Nat.monus(a, Rn(1n+p1, x)) : Nat}:
  match j:
    case 0n:
      +p : Nat = 1n+p1
      +ma = Fm.m(p, a)
      +ea = Equal.trans(Nat, a, Nat.mul(ma, RD.Nat.pow2(Fm.j(p, a))), ma, Fm.of(p1, a, fa),
        Equal.trans(Nat, Nat.mul(ma, RD.Nat.pow2(Fm.j(p, a))), Nat.mul(ma, 1n), ma, Equal.cong(Nat, Nat, z => Nat.mul(ma, RD.Nat.pow2(z)), Fm.j(p, a), 0n, ej), NL.Nat.mul_one_r(ma)))
      +hxa = Ge.of(a, x, b, Equal.trans(Nat, a, Nat.add(b, x), Nat.add(x, b), hx, NL.Nat.add_comm(b, x)))
      F2S.exact(p1, a, b, x, hx, fb, Small(p1, x, Le.trans(x, a, RD.Nat.pow2(p), hxa, Le.trans(a, ma, RD.Nat.pow2(p), Le.eq(a, ma, ea), Fm.le2(p1, a)))))
    case 1n+(+j1):
      +p : Nat = 1n+p1
      +ma = Fm.m(p, a)
      +a1 = Nat.mul(ma, RD.Nat.pow2(j1))
      +fa1 = G.le(p1, ma, j1, Fm.w(p, a), Fm.le(p1, a))
      # a = 2 a1
      +ea = Equal.trans(Nat, a, Nat.mul(ma, RD.Nat.pow2(Fm.j(p, a))), Nat.double(a1), Fm.of(p1, a, fa),
        Equal.trans(Nat, Nat.mul(ma, RD.Nat.pow2(Fm.j(p, a))), Nat.mul(ma, Nat.double(RD.Nat.pow2(j1))), Nat.double(a1), Equal.cong(Nat, Nat, z => Nat.mul(ma, RD.Nat.pow2(z)), Fm.j(p, a), 1n+j1, ej), R.Nat.mul_double(ma, RD.Nat.pow2(j1))))
      # b < a1, so a1 <= x
      +hb1 = Equal.trans(Bool, RD.Nat.lt(b, a1), RD.Nat.lt(Nat.double(b), Nat.double(a1)), True{}, Equal.sym(Bool, RD.Nat.lt(Nat.double(b), Nat.double(a1)), RD.Nat.lt(b, a1), Lt.dd(b, a1)),
        Equal.trans(Bool, RD.Nat.lt(Nat.double(b), Nat.double(a1)), RD.Nat.lt(Nat.double(b), a), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.double(b), z), Nat.double(a1), a, Equal.sym(Nat, a, Nat.double(a1), ea)), el))
      +w = RD.Nat.monus(a1, 1n+b)
      +env : List<&2, Nat> = [0n, 1n, a, b, x, a1, w, Nat.double(a1)]
      +ex = R.NatN.eq2(env, R.V(4n), R.Ad(R.V(5n), R.Ad(R.V(1n), R.V(6n))), [], [],
        [R.Ad(R.Ad(R.V(3n), R.V(4n)), R.Ng(R.V(2n))), R.Ad(R.V(2n), R.Ng(R.V(7n))), R.Ad(R.V(7n), R.Ng(R.Ad(R.V(5n), R.V(5n)))), R.Ad(R.V(5n), R.Ng(R.Ad(R.Ad(R.V(1n), R.V(3n)), R.V(6n))))],
        {==}, Unit{}, (R.NatN.z(env, R.Ad(R.V(3n), R.V(4n)), R.V(2n), {==}, {==}, Equal.sym(Nat, a, Nat.add(b, x), hx)),
          (R.NatN.z(env, R.V(2n), R.V(7n), {==}, {==}, ea), (R.NatN.z(env, R.V(7n), R.Ad(R.V(5n), R.V(5n)), {==}, {==}, Y.Nat.double_add(a1)),
          (R.NatN.z(env, R.V(5n), R.Ad(R.Ad(R.V(1n), R.V(3n)), R.V(6n)), {==}, {==}, BP.Lt.wit(b, a1)(hb1)), Unit{})))), {==}, {==})
      +rx = Rn(p, x)
      lo = Mono.lo(p1, x, a1, fa1, Ge.of(x, a1, 1n+w, ex))
      h2 = Le.trans(a, Nat.double(a1), Nat.double(rx), Le.eq(a, Nat.double(a1), ea), Le.dd(a1, rx, lo))
      +hxx = Le.wit(rx, a, Mono.hi(p1, x, a, fa, Ge.of(a, x, b, Equal.trans(Nat, a, Nat.add(b, x), Nat.add(x, b), hx, NL.Nat.add_comm(b, x)))))
      (hxx, Sterbenz(p1, a, rx, RD.Nat.monus(a, rx), hxx, h2, fa, RF(p1, x)))

def F2S.opp.go(+p1: Nat, +a: Nat, +b: Nat, +x: Nat, +hx: {a == Nat.add(b, x) : Nat}, +fa: {Rn(1n+p1, a) == a : Nat}, +fb: {Rn(1n+p1, b) == b : Nat}, l: Bool, +el: {RD.Nat.lt(Nat.double(b), a) == l : Bool})
  -> {a == Nat.add(Rn(1n+p1, x), RD.Nat.monus(a, Rn(1n+p1, x))) : Nat} & {Rn(1n+p1, RD.Nat.monus(a, Rn(1n+p1, x))) == RD.Nat.monus(a, Rn(1n+p1, x)) : Nat}:
  match l:
    case False{}:
      F2S.exact(p1, a, b, x, hx, fb, Sterbenz(p1, a, b, x, hx, el, fa, fb))
    case True{}:
      F2S.opp.j(p1, a, b, x, hx, fa, fb, el, Fm.j(1n+p1, a), {==})

# opposite signs, a = b + x: a = R(x) + d with d representable, so R(x) - a is
def F2S.opp(+p1: Nat, +a: Nat, +b: Nat, +x: Nat, +hx: {a == Nat.add(b, x) : Nat}, +fa: {Rn(1n+p1, a) == a : Nat}, +fb: {Rn(1n+p1, b) == b : Nat})
  -> {a == Nat.add(Rn(1n+p1, x), RD.Nat.monus(a, Rn(1n+p1, x))) : Nat} & {Rn(1n+p1, RD.Nat.monus(a, Rn(1n+p1, x))) == RD.Nat.monus(a, Rn(1n+p1, x)) : Nat}:
  F2S.opp.go(p1, a, b, x, hx, fa, fb, RD.Nat.lt(Nat.double(b), a), {==})

# Signed rounding
# ---------------

# z rounded: its sign, its magnitude rounded
def RNi(+p: Nat, +z: I.Int) -> I.Int:
  RD.Int.signed(z, Rn(p, RD.Int.mag(z)))

def Fi(p: Nat, z: I.Int) -> Type:
  {Rn(p, RD.Int.mag(z)) == RD.Int.mag(z) : Nat}

def Sgn.self(+n: I.Int) -> {RD.Int.signed(n, RD.Int.mag(n)) == n : I.Int}:
  match n:
    case I.IPos{a}:
      {==}
    case I.INeg{a}:
      {==}

def RNi.exact(+p: Nat, +z: I.Int, +f: {Rn(p, RD.Int.mag(z)) == RD.Int.mag(z) : Nat}) -> {RNi(p, z) == z : I.Int}:
  Equal.trans(I.Int, RD.Int.signed(z, Rn(p, RD.Int.mag(z))), RD.Int.signed(z, RD.Int.mag(z)), z, Equal.cong(Nat, I.Int, w => RD.Int.signed(z, w), Rn(p, RD.Int.mag(z)), RD.Int.mag(z), f), Sgn.self(z))

def Mag.neg(+z: I.Int) -> {RD.Int.mag(I.Int.neg(z)) == RD.Int.mag(z) : Nat}:
  match z:
    case I.IPos{a}:
      match a:
        case 0n:
          {==}
        case 1n+k:
          {==}
    case I.INeg{a}:
      {==}

def RNi.neg(+p: Nat, +z: I.Int) -> {RNi(p, I.Int.neg(z)) == I.Int.neg(RNi(p, z)) : I.Int}:
  match z:
    case I.IPos{a}:
      match a:
        case 0n:
          {==}
        case 1n+k:
          {==}
    case I.INeg{+a}:
      Equal.sym(I.Int, I.Int.neg(I.Int.neg(I.IPos{Rn(p, 1n+a)})), I.IPos{Rn(p, 1n+a)}, Z.Int.neg_neg(I.IPos{Rn(p, 1n+a)}))

# |A - B| as an integer
def Mag.diff.go(+a: Nat, +b: Nat, l: Bool, +el: {RD.Nat.lt(a, b) == l : Bool}) -> {RD.Int.mag(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b}))) == Dist(a, b) : Nat}:
  match l:
    case False{}:
      +k = RD.Nat.monus(a, b)
      +ea = R.Nat.lt_f(a, b)(el)
      +env : List<&2, I.Int> = [I.IPos{b}, I.IPos{k}]
      +ei = BP.IntN(env, R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(0n))), R.V(1n), [], [], {==}, Unit{})
      Equal.trans(Nat, RD.Int.mag(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b}))), RD.Int.mag(I.Int.add(I.IPos{Nat.add(b, k)}, I.Int.neg(I.IPos{b}))), Dist(a, b),
        Equal.cong(Nat, Nat, z => RD.Int.mag(I.Int.add(I.IPos{z}, I.Int.neg(I.IPos{b}))), a, Nat.add(b, k), ea),
        Equal.trans(Nat, RD.Int.mag(I.Int.add(I.IPos{Nat.add(b, k)}, I.Int.neg(I.IPos{b}))), k, Dist(a, b), Equal.cong(I.Int, Nat, z => RD.Int.mag(z), I.Int.add(I.IPos{Nat.add(b, k)}, I.Int.neg(I.IPos{b})), I.IPos{k}, ei),
          Equal.sym(Nat, Dist(a, b), k, Equal.trans(Nat, Dist(a, b), Dist(Nat.add(b, k), b), k, Equal.cong(Nat, Nat, z => Dist(z, b), a, Nat.add(b, k), ea), Dist.dn(b, k)))))
    case True{}:
      +w = RD.Nat.monus(b, 1n+a)
      +eb = Equal.trans(Nat, b, 1n+Nat.add(a, w), Nat.add(a, 1n+w), BP.Lt.wit(a, b)(el), Equal.sym(Nat, Nat.add(a, 1n+w), 1n+Nat.add(a, w), NL.Nat.add_succ_r(a, w)))
      +env : List<&2, I.Int> = [I.IPos{a}, I.IPos{1n+w}]
      +ei = BP.IntN(env, R.Ad(R.V(0n), R.Ng(R.Ad(R.V(0n), R.V(1n)))), R.Ng(R.V(1n)), [], [], {==}, Unit{})
      Equal.trans(Nat, RD.Int.mag(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b}))), RD.Int.mag(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{Nat.add(a, 1n+w)}))), Dist(a, b),
        Equal.cong(Nat, Nat, z => RD.Int.mag(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{z}))), b, Nat.add(a, 1n+w), eb),
        Equal.trans(Nat, RD.Int.mag(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{Nat.add(a, 1n+w)}))), 1n+w, Dist(a, b),
          Equal.cong(I.Int, Nat, z => RD.Int.mag(z), I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{Nat.add(a, 1n+w)})), I.Int.neg(I.IPos{1n+w}), ei),
          Equal.sym(Nat, Dist(a, b), 1n+w, Equal.trans(Nat, Dist(a, b), Dist(a, Nat.add(a, 1n+w)), 1n+w, Equal.cong(Nat, Nat, z => Dist(a, z), b, Nat.add(a, 1n+w), eb), Dist.up(a, 1n+w)))))

def Mag.diff(+a: Nat, +b: Nat) -> {RD.Int.mag(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b}))) == Dist(a, b) : Nat}:
  Mag.diff.go(a, b, RD.Nat.lt(a, b), {==})

# signed(z, A) - signed(z, B) has magnitude |A - B|
def Mag.sd(+z: I.Int, +a: Nat, +b: Nat) -> {RD.Int.mag(I.Int.add(RD.Int.signed(z, a), I.Int.neg(RD.Int.signed(z, b)))) == Dist(a, b) : Nat}:
  match z:
    case I.IPos{k}:
      Mag.diff(a, b)
    case I.INeg{k}:
      +env : List<&2, I.Int> = [I.IPos{a}, I.IPos{b}]
      +ei = BP.IntN(env, R.Ad(R.Ng(R.V(0n)), R.Ng(R.Ng(R.V(1n)))), R.Ng(R.Ad(R.V(0n), R.Ng(R.V(1n)))), [], [], {==}, Unit{})
      Equal.trans(Nat, RD.Int.mag(I.Int.add(I.Int.neg(I.IPos{a}), I.Int.neg(I.Int.neg(I.IPos{b})))), RD.Int.mag(I.Int.neg(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b})))), Dist(a, b),
        Equal.cong(I.Int, Nat, w => RD.Int.mag(w), I.Int.add(I.Int.neg(I.IPos{a}), I.Int.neg(I.Int.neg(I.IPos{b}))), I.Int.neg(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b}))), ei),
        Equal.trans(Nat, RD.Int.mag(I.Int.neg(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b})))), RD.Int.mag(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b}))), Dist(a, b), Mag.neg(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b}))), Mag.diff(a, b)))

def Dist.comm(+a: Nat, +b: Nat) -> {Dist(a, b) == Dist(b, a) : Nat}:
  NL.Nat.add_comm(RD.Nat.monus(a, b), RD.Nat.monus(b, a))

# x - RNi(x) is representable when its magnitude is: then rounding it is exact
def Err.i(+p: Nat, +x: I.Int, +f: {Rn(p, Dist(Rn(p, RD.Int.mag(x)), RD.Int.mag(x))) == Dist(Rn(p, RD.Int.mag(x)), RD.Int.mag(x)) : Nat})
  -> {RNi(p, I.Int.add(x, I.Int.neg(RNi(p, x)))) == I.Int.add(x, I.Int.neg(RNi(p, x))) : I.Int}:
  +m = RD.Int.mag(x)
  +r = Rn(p, m)
  +d = I.Int.add(x, I.Int.neg(RNi(p, x)))
  +em = Equal.trans(Nat, RD.Int.mag(d), RD.Int.mag(I.Int.add(RD.Int.signed(x, m), I.Int.neg(RD.Int.signed(x, r)))), Dist(r, m),
    Equal.cong(I.Int, Nat, w => RD.Int.mag(I.Int.add(w, I.Int.neg(RD.Int.signed(x, r)))), x, RD.Int.signed(x, m), Equal.sym(I.Int, RD.Int.signed(x, m), x, Sgn.self(x))),
    Equal.trans(Nat, RD.Int.mag(I.Int.add(RD.Int.signed(x, m), I.Int.neg(RD.Int.signed(x, r)))), Dist(m, r), Dist(r, m), Mag.sd(x, m, r), Dist.comm(m, r)))
  RNi.exact(p, d, Fn.eq(p, RD.Int.mag(d), Dist(r, m), em, f))

# Fast2Sum
# --------

def F2.s(+p: Nat, +a: I.Int, +b: I.Int) -> I.Int:
  RNi(p, I.Int.add(a, b))

def F2.z(+p: Nat, +a: I.Int, +b: I.Int) -> I.Int:
  RNi(p, I.Int.add(F2.s(p, a, b), I.Int.neg(a)))

def F2.t(+p: Nat, +a: I.Int, +b: I.Int) -> I.Int:
  RNi(p, I.Int.add(b, I.Int.neg(F2.z(p, a, b))))

# when s - a and the sum's error are representable, s + t = a + b
def F2.fin(+p: Nat, +a: I.Int, +b: I.Int,
  +fe: {Rn(p, RD.Int.mag(I.Int.add(F2.s(p, a, b), I.Int.neg(a)))) == RD.Int.mag(I.Int.add(F2.s(p, a, b), I.Int.neg(a))) : Nat},
  +fr: {Rn(p, Dist(Rn(p, RD.Int.mag(I.Int.add(a, b))), RD.Int.mag(I.Int.add(a, b)))) == Dist(Rn(p, RD.Int.mag(I.Int.add(a, b))), RD.Int.mag(I.Int.add(a, b))) : Nat})
  -> {I.Int.add(F2.s(p, a, b), F2.t(p, a, b)) == I.Int.add(a, b) : I.Int}:
  +x = I.Int.add(a, b)
  +s = F2.s(p, a, b)
  +e = I.Int.add(s, I.Int.neg(a))
  +ez = RNi.exact(p, e, fe)
  +env : List<&2, I.Int> = [a, b, s]
  +eb = Equal.trans(I.Int, I.Int.add(b, I.Int.neg(F2.z(p, a, b))), I.Int.add(b, I.Int.neg(e)), I.Int.add(x, I.Int.neg(s)),
    Equal.cong(I.Int, I.Int, w => I.Int.add(b, I.Int.neg(w)), F2.z(p, a, b), e, ez),
    BP.IntN(env, R.Ad(R.V(1n), R.Ng(R.Ad(R.V(2n), R.Ng(R.V(0n))))), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(2n))), [], [], {==}, Unit{}))
  +et = Equal.trans(I.Int, F2.t(p, a, b), RNi(p, I.Int.add(x, I.Int.neg(s))), I.Int.add(x, I.Int.neg(s)),
    Equal.cong(I.Int, I.Int, w => RNi(p, w), I.Int.add(b, I.Int.neg(F2.z(p, a, b))), I.Int.add(x, I.Int.neg(s)), eb), Err.i(p, x, fr))
  Equal.trans(I.Int, I.Int.add(s, F2.t(p, a, b)), I.Int.add(s, I.Int.add(x, I.Int.neg(s))), x, Equal.cong(I.Int, I.Int, w => I.Int.add(s, w), F2.t(p, a, b), I.Int.add(x, I.Int.neg(s)), et),
    BP.IntN(env, R.Ad(R.V(2n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(2n)))), R.Ad(R.V(0n), R.V(1n)), [], [], {==}, Unit{}))

def F2.pp(+p1: Nat, +a: Nat, +b: Nat, +fa: {Rn(1n+p1, a) == a : Nat}, +fb: {Rn(1n+p1, b) == b : Nat}, +hle: {RD.Nat.lt(a, b) == False{} : Bool})
  -> {I.Int.add(F2.s(1n+p1, I.IPos{a}, I.IPos{b}), F2.t(1n+p1, I.IPos{a}, I.IPos{b})) == I.Int.add(I.IPos{a}, I.IPos{b}) : I.Int}:
  +p : Nat = 1n+p1
  +r = Rn(p, Nat.add(a, b))
  +d = RD.Nat.monus(r, a)
  +er : {r == Nat.add(a, d) : Nat} = Pair.fst({r == Nat.add(a, d) : Nat}, {Rn(p, d) == d : Nat}, F2S.same(p1, a, b, fa, hle))
  +fd : {Rn(p, d) == d : Nat} = Pair.snd({r == Nat.add(a, d) : Nat}, {Rn(p, d) == d : Nat}, F2S.same(p1, a, b, fa, hle))
  +env : List<&2, I.Int> = [I.IPos{a}, I.IPos{d}]
  +ee = Equal.trans(I.Int, I.Int.add(I.IPos{r}, I.Int.neg(I.IPos{a})), I.Int.add(I.IPos{Nat.add(a, d)}, I.Int.neg(I.IPos{a})), I.IPos{d},
    Equal.cong(Nat, I.Int, w => I.Int.add(I.IPos{w}, I.Int.neg(I.IPos{a})), r, Nat.add(a, d), er),
    BP.IntN(env, R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(0n))), R.V(1n), [], [], {==}, Unit{}))
  +em = Equal.cong(I.Int, Nat, w => RD.Int.mag(w), I.Int.add(I.IPos{r}, I.Int.neg(I.IPos{a})), I.IPos{d}, ee)
  F2.fin(p, I.IPos{a}, I.IPos{b}, Fn.eq(p, RD.Int.mag(I.Int.add(I.IPos{r}, I.Int.neg(I.IPos{a}))), d, em, fd), LA(p1, a, b, fa, fb))

def F2.pn(+p1: Nat, +a: Nat, +bn: Nat, +fa: {Rn(1n+p1, a) == a : Nat}, +fb: {Rn(1n+p1, 1n+bn) == 1n+bn : Nat}, hle: Le(1n+bn, a))
  -> {I.Int.add(F2.s(1n+p1, I.IPos{a}, I.INeg{bn}), F2.t(1n+p1, I.IPos{a}, I.INeg{bn})) == I.Int.add(I.IPos{a}, I.INeg{bn}) : I.Int}:
  +p : Nat = 1n+p1
  +b : Nat = 1n+bn
  +x = RD.Nat.monus(a, b)
  +hx = Le.wit(b, a, hle)
  +env0 : List<&2, I.Int> = [I.IPos{b}, I.IPos{x}]
  +ex = Equal.trans(I.Int, I.Int.add(I.IPos{a}, I.INeg{bn}), I.Int.add(I.IPos{Nat.add(b, x)}, I.Int.neg(I.IPos{b})), I.IPos{x},
    Equal.cong(Nat, I.Int, w => I.Int.add(I.IPos{w}, I.Int.neg(I.IPos{b})), a, Nat.add(b, x), hx),
    BP.IntN(env0, R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(0n))), R.V(1n), [], [], {==}, Unit{}))
  +rx = Rn(p, x)
  +d = RD.Nat.monus(a, rx)
  +ea : {a == Nat.add(rx, d) : Nat} = Pair.fst({a == Nat.add(rx, d) : Nat}, {Rn(p, d) == d : Nat}, F2S.opp(p1, a, b, x, hx, fa, fb))
  +fd : {Rn(p, d) == d : Nat} = Pair.snd({a == Nat.add(rx, d) : Nat}, {Rn(p, d) == d : Nat}, F2S.opp(p1, a, b, x, hx, fa, fb))
  +es = Equal.cong(I.Int, I.Int, w => RNi(p, w), I.Int.add(I.IPos{a}, I.INeg{bn}), I.IPos{x}, ex)
  +env : List<&2, I.Int> = [I.IPos{rx}, I.IPos{d}]
  +ee = Equal.trans(I.Int, I.Int.add(F2.s(p, I.IPos{a}, I.INeg{bn}), I.Int.neg(I.IPos{a})), I.Int.add(I.IPos{rx}, I.Int.neg(I.IPos{Nat.add(rx, d)})), I.Int.neg(I.IPos{d}),
    Equal.trans(I.Int, I.Int.add(F2.s(p, I.IPos{a}, I.INeg{bn}), I.Int.neg(I.IPos{a})), I.Int.add(I.IPos{rx}, I.Int.neg(I.IPos{a})), I.Int.add(I.IPos{rx}, I.Int.neg(I.IPos{Nat.add(rx, d)})),
      Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.neg(I.IPos{a})), F2.s(p, I.IPos{a}, I.INeg{bn}), I.IPos{rx}, es),
      Equal.cong(Nat, I.Int, w => I.Int.add(I.IPos{rx}, I.Int.neg(I.IPos{w})), a, Nat.add(rx, d), ea)),
    BP.IntN(env, R.Ad(R.V(0n), R.Ng(R.Ad(R.V(0n), R.V(1n)))), R.Ng(R.V(1n)), [], [], {==}, Unit{}))
  +em = Equal.trans(Nat, RD.Int.mag(I.Int.add(F2.s(p, I.IPos{a}, I.INeg{bn}), I.Int.neg(I.IPos{a}))), RD.Int.mag(I.Int.neg(I.IPos{d})), d,
    Equal.cong(I.Int, Nat, w => RD.Int.mag(w), I.Int.add(F2.s(p, I.IPos{a}, I.INeg{bn}), I.Int.neg(I.IPos{a})), I.Int.neg(I.IPos{d}), ee), Mag.neg(I.IPos{d}))
  +emx = Equal.cong(I.Int, Nat, w => RD.Int.mag(w), I.Int.add(I.IPos{a}, I.INeg{bn}), I.IPos{x}, ex)
  F2.fin(p, I.IPos{a}, I.INeg{bn}, Fn.eq(p, RD.Int.mag(I.Int.add(F2.s(p, I.IPos{a}, I.INeg{bn}), I.Int.neg(I.IPos{a}))), d, em, fd),
    Fn.eq(p, Dist(Rn(p, RD.Int.mag(I.Int.add(I.IPos{a}, I.INeg{bn}))), RD.Int.mag(I.Int.add(I.IPos{a}, I.INeg{bn}))), Dist(rx, x),
      Equal.cong(Nat, Nat, w => Dist(Rn(p, w), w), RD.Int.mag(I.Int.add(I.IPos{a}, I.INeg{bn})), x, emx), LA.d(p1, a, b, x, hx, fa, fb)))

def F2.nonneg(+p1: Nat, +a: Nat, b: I.Int, +fa: {Rn(1n+p1, a) == a : Nat}, +fb: {Rn(1n+p1, RD.Int.mag(b)) == RD.Int.mag(b) : Nat}, hle: Le(RD.Int.mag(b), a))
  -> {I.Int.add(F2.s(1n+p1, I.IPos{a}, b), F2.t(1n+p1, I.IPos{a}, b)) == I.Int.add(I.IPos{a}, b) : I.Int}:
  match b:
    case I.IPos{+bb}:
      F2.pp(p1, a, bb, fa, fb, hle)
    case I.INeg{+bn}:
      F2.pn(p1, a, bn, fa, fb, hle)

# Fast2Sum commutes with negating both inputs
def F2.sym.s(+p: Nat, +a: I.Int, +b: I.Int) -> {F2.s(p, I.Int.neg(a), I.Int.neg(b)) == I.Int.neg(F2.s(p, a, b)) : I.Int}:
  +env : List<&2, I.Int> = [a, b]
  Equal.trans(I.Int, RNi(p, I.Int.add(I.Int.neg(a), I.Int.neg(b))), RNi(p, I.Int.neg(I.Int.add(a, b))), I.Int.neg(RNi(p, I.Int.add(a, b))),
    Equal.cong(I.Int, I.Int, w => RNi(p, w), I.Int.add(I.Int.neg(a), I.Int.neg(b)), I.Int.neg(I.Int.add(a, b)), BP.IntN(env, R.Ad(R.Ng(R.V(0n)), R.Ng(R.V(1n))), R.Ng(R.Ad(R.V(0n), R.V(1n))), [], [], {==}, Unit{})),
    RNi.neg(p, I.Int.add(a, b)))

def F2.sym.z(+p: Nat, +a: I.Int, +b: I.Int) -> {F2.z(p, I.Int.neg(a), I.Int.neg(b)) == I.Int.neg(F2.z(p, a, b)) : I.Int}:
  +s = F2.s(p, a, b)
  +env : List<&2, I.Int> = [a, s]
  Equal.trans(I.Int, RNi(p, I.Int.add(F2.s(p, I.Int.neg(a), I.Int.neg(b)), I.Int.neg(I.Int.neg(a)))), RNi(p, I.Int.neg(I.Int.add(s, I.Int.neg(a)))), I.Int.neg(RNi(p, I.Int.add(s, I.Int.neg(a)))),
    Equal.cong(I.Int, I.Int, w => RNi(p, w), I.Int.add(F2.s(p, I.Int.neg(a), I.Int.neg(b)), I.Int.neg(I.Int.neg(a))), I.Int.neg(I.Int.add(s, I.Int.neg(a))),
      Equal.trans(I.Int, I.Int.add(F2.s(p, I.Int.neg(a), I.Int.neg(b)), I.Int.neg(I.Int.neg(a))), I.Int.add(I.Int.neg(s), I.Int.neg(I.Int.neg(a))), I.Int.neg(I.Int.add(s, I.Int.neg(a))),
        Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.neg(I.Int.neg(a))), F2.s(p, I.Int.neg(a), I.Int.neg(b)), I.Int.neg(s), F2.sym.s(p, a, b)),
        BP.IntN(env, R.Ad(R.Ng(R.V(1n)), R.Ng(R.Ng(R.V(0n)))), R.Ng(R.Ad(R.V(1n), R.Ng(R.V(0n)))), [], [], {==}, Unit{}))),
    RNi.neg(p, I.Int.add(s, I.Int.neg(a))))

def F2.sym.t(+p: Nat, +a: I.Int, +b: I.Int) -> {F2.t(p, I.Int.neg(a), I.Int.neg(b)) == I.Int.neg(F2.t(p, a, b)) : I.Int}:
  +z = F2.z(p, a, b)
  +env : List<&2, I.Int> = [b, z]
  Equal.trans(I.Int, RNi(p, I.Int.add(I.Int.neg(b), I.Int.neg(F2.z(p, I.Int.neg(a), I.Int.neg(b))))), RNi(p, I.Int.neg(I.Int.add(b, I.Int.neg(z)))), I.Int.neg(RNi(p, I.Int.add(b, I.Int.neg(z)))),
    Equal.cong(I.Int, I.Int, w => RNi(p, w), I.Int.add(I.Int.neg(b), I.Int.neg(F2.z(p, I.Int.neg(a), I.Int.neg(b)))), I.Int.neg(I.Int.add(b, I.Int.neg(z))),
      Equal.trans(I.Int, I.Int.add(I.Int.neg(b), I.Int.neg(F2.z(p, I.Int.neg(a), I.Int.neg(b)))), I.Int.add(I.Int.neg(b), I.Int.neg(I.Int.neg(z))), I.Int.neg(I.Int.add(b, I.Int.neg(z))),
        Equal.cong(I.Int, I.Int, w => I.Int.add(I.Int.neg(b), I.Int.neg(w)), F2.z(p, I.Int.neg(a), I.Int.neg(b)), I.Int.neg(z), F2.sym.z(p, a, b)),
        BP.IntN(env, R.Ad(R.Ng(R.V(0n)), R.Ng(R.Ng(R.V(1n)))), R.Ng(R.Ad(R.V(0n), R.Ng(R.V(1n)))), [], [], {==}, Unit{}))),
    RNi.neg(p, I.Int.add(b, I.Int.neg(z))))

# Fast2Sum is exact: for representable a, b with |b| <= |a|, at any precision
# p, s = RN(a + b), z = RN(s - a), t = RN(b - z) give s + t = a + b
def Fast2Sum(+p1: Nat, a: I.Int, +b: I.Int, fa: Fi(1n+p1, a), +fb: {Rn(1n+p1, RD.Int.mag(b)) == RD.Int.mag(b) : Nat}, +hle: {RD.Nat.lt(RD.Int.mag(a), RD.Int.mag(b)) == False{} : Bool})
  -> {I.Int.add(F2.s(1n+p1, a, b), F2.t(1n+p1, a, b)) == I.Int.add(a, b) : I.Int}:
  match a:
    case I.IPos{+aa}:
      F2.nonneg(p1, aa, b, fa, fb, hle)
    case I.INeg{+an}:
      +p : Nat = 1n+p1
      +a2 : I.Int = I.INeg{an}
      +s = F2.s(p, a2, b)
      +t = F2.t(p, a2, b)
      +nb = I.Int.neg(b)
      +mb = Mag.neg(b)
      +h = F2.nonneg(p1, 1n+an, nb, fa, Fn.eq(p, RD.Int.mag(nb), RD.Int.mag(b), mb, fb),
        Equal.trans(Bool, RD.Nat.lt(1n+an, RD.Int.mag(nb)), RD.Nat.lt(1n+an, RD.Int.mag(b)), False{}, Equal.cong(Nat, Bool, w => RD.Nat.lt(1n+an, w), RD.Int.mag(nb), RD.Int.mag(b), mb), hle))
      # -s - t = -a - b
      +h2 = Equal.trans(I.Int, I.Int.add(I.Int.neg(s), I.Int.neg(t)), I.Int.add(F2.s(p, I.IPos{1n+an}, nb), F2.t(p, I.IPos{1n+an}, nb)), I.Int.add(I.IPos{1n+an}, nb),
        Equal.sym(I.Int, I.Int.add(F2.s(p, I.IPos{1n+an}, nb), F2.t(p, I.IPos{1n+an}, nb)), I.Int.add(I.Int.neg(s), I.Int.neg(t)),
          Y.Int.cong2(F2.s(p, I.IPos{1n+an}, nb), I.Int.neg(s), F2.t(p, I.IPos{1n+an}, nb), I.Int.neg(t), F2.sym.s(p, a2, b), F2.sym.t(p, a2, b))), h)
      +env : List<&2, I.Int> = [s, t, a2, b]
      Equal.trans(I.Int, I.Int.add(s, t), I.Int.neg(I.Int.add(I.Int.neg(s), I.Int.neg(t))), I.Int.add(a2, b),
        BP.IntN(env, R.Ad(R.V(0n), R.V(1n)), R.Ng(R.Ad(R.Ng(R.V(0n)), R.Ng(R.V(1n)))), [], [], {==}, Unit{}),
        Equal.trans(I.Int, I.Int.neg(I.Int.add(I.Int.neg(s), I.Int.neg(t))), I.Int.neg(I.Int.add(I.IPos{1n+an}, nb)), I.Int.add(a2, b),
          Equal.cong(I.Int, I.Int, w => I.Int.neg(w), I.Int.add(I.Int.neg(s), I.Int.neg(t)), I.Int.add(I.IPos{1n+an}, nb), h2),
          BP.IntN(env, R.Ng(R.Ad(R.Ng(R.V(2n)), R.Ng(R.V(3n)))), R.Ad(R.V(2n), R.V(3n)), [], [], {==}, Unit{})))
