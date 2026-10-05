# Veltkamp's split and Dekker's product (num/df32.bend) are exact, on the
# integers rounded to p bits of proofs/eft.bend (ADR-010). In order:
# - shifts: how many bits rounding drops bounds a value and its error;
# - the split: exact for every representable input (`Split`), and its
#   sizes on normalised inputs (`V.hi.grid`, `V.ah.le`, `V.lo.le`);
# - Dekker's product for p = 2s: on normalised inputs (`Dk.core`,
#   `TwoProd.norm`), then for all inputs by scaling and negation
#   (`TwoProd`);
# - the same in dyadic arithmetic (`DRf.split`, `DTwoProd`), which
#   tests/df32_exact.bend instantiates for binary32.

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
import ./equiv.bend as EQ
import ./eft.bend as E

# Shifts
# ------

def Shf(+p: Nat, +n: Nat) -> Nat:
  RD.Tr.s(RD.Tr.of(p, n))

# n < 2^p 2^shift
def S1(+p1: Nat, +n: Nat) -> {RD.Nat.lt(n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(Shf(1n+p1, n)))) == True{} : Bool}:
  +p : Nat = 1n+p1
  +t = RD.Tr.of(p, n)
  +q = RD.Tr.q(t)
  +r = R.Tr.r(t)
  +wr = E.Tr.wr(t)
  +sv = RD.Nat.pow2(RD.Tr.s(t))
  +pw = RD.Nat.pow2(p)
  +w = RD.Nat.monus(pw, 1n+q)
  +hn : {n == Nat.add(Nat.mul(q, sv), r) : Nat} = Pair.fst({n == Nat.add(Nat.mul(q, sv), r) : Nat}, {sv == Nat.add(Nat.add(r, 1n), wr) : Nat}, E.Sh.n(p1, n))
  +hs : {sv == Nat.add(Nat.add(r, 1n), wr) : Nat} = Pair.snd({n == Nat.add(Nat.mul(q, sv), r) : Nat}, {sv == Nat.add(Nat.add(r, 1n), wr) : Nat}, E.Sh.n(p1, n))
  +hq = BP.Lt.wit(q, pw)(E.TrQ(p, n))
  +k = Nat.add(wr, Nat.mul(w, sv))
  +env : List<&2, Nat> = [0n, 1n, n, q, sv, r, wr, pw, w]
  +e = R.NatN.eq2(env, R.Ml(R.V(7n), R.V(4n)), R.Ad(R.V(2n), R.Ad(R.V(1n), R.Ad(R.V(6n), R.Ml(R.V(8n), R.V(4n))))),
    [R.V(4n)], [R.Ad(R.V(7n), R.Ng(R.Ad(R.Ad(R.V(1n), R.V(3n)), R.V(8n))))],
    [R.Ad(R.Ad(R.Ml(R.V(3n), R.V(4n)), R.V(5n)), R.Ng(R.V(2n))), R.Ad(R.V(4n), R.Ng(R.Ad(R.Ad(R.V(5n), R.V(1n)), R.V(6n)))), R.Ad(R.Ml(R.V(1n), R.V(4n)), R.Ng(R.V(4n)))],
    {==}, (R.NatN.z(env, R.V(7n), R.Ad(R.Ad(R.V(1n), R.V(3n)), R.V(8n)), {==}, {==}, hq), Unit{}),
    (R.NatN.z(env, R.Ad(R.Ml(R.V(3n), R.V(4n)), R.V(5n)), R.V(2n), {==}, {==}, Equal.sym(Nat, n, Nat.add(Nat.mul(q, sv), r), hn)),
      (R.NatN.z(env, R.V(4n), R.Ad(R.Ad(R.V(5n), R.V(1n)), R.V(6n)), {==}, {==}, hs),
      (R.NatN.z(env, R.Ml(R.V(1n), R.V(4n)), R.V(4n), {==}, {==}, NL.Nat.add_zero_r(sv)), Unit{}))), {==}, {==})
  Equal.trans(Bool, RD.Nat.lt(n, Nat.mul(pw, sv)), RD.Nat.lt(n, Nat.add(n, 1n+k)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(n, z), Nat.mul(pw, sv), Nat.add(n, 1n+k), e), BP.Lt.self(n, k))

# once shifted, n >= 2^(p-1) 2^shift
def S2(+p1: Nat, +n: Nat, +s1: Nat, +hs: {Shf(1n+p1, n) == 1n+s1 : Nat}) -> E.Le(Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Shf(1n+p1, n))), n):
  +p : Nat = 1n+p1
  +t = RD.Tr.of(p, n)
  +q = RD.Tr.q(t)
  +r = R.Tr.r(t)
  +wq = E.Tr.wq(t)
  +sv = RD.Nat.pow2(RD.Tr.s(t))
  +h = RD.Nat.pow2(p1)
  +hn : {n == Nat.add(Nat.mul(q, sv), r) : Nat} = Pair.fst({n == Nat.add(Nat.mul(q, sv), r) : Nat}, {sv == Nat.add(Nat.add(r, 1n), E.Tr.wr(t)) : Nat}, E.Sh.n(p1, n))
  +hq = E.Sh.h(h, n, t, R.Inv.of(p1, n), s1, hs)
  +env : List<&2, Nat> = [0n, n, q, sv, r, h, wq]
  +e = R.NatN.eq2(env, R.V(1n), R.Ad(R.Ml(R.V(5n), R.V(3n)), R.Ad(R.Ml(R.V(6n), R.V(3n)), R.V(4n))),
    [R.V(3n)], [R.Ad(R.V(2n), R.Ng(R.Ad(R.V(5n), R.V(6n))))], [R.Ad(R.V(1n), R.Ng(R.Ad(R.Ml(R.V(2n), R.V(3n)), R.V(4n))))],
    {==}, (R.NatN.z(env, R.V(2n), R.Ad(R.V(5n), R.V(6n)), {==}, {==}, hq), Unit{}), (R.NatN.z(env, R.V(1n), R.Ad(R.Ml(R.V(2n), R.V(3n)), R.V(4n)), {==}, {==}, hn), Unit{}), {==}, {==})
  E.Ge.of(n, Nat.mul(h, sv), Nat.add(Nat.mul(wq, sv), r), e)

# 2^p 2^a <= 2^(p-1) 2^(1 + a + w)
def Pw.ge(+p1: Nat, +a: Nat, +w: Nat) -> E.Le(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(a)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(a, w)))):
  +h = RD.Nat.pow2(p1)
  +x = RD.Nat.pow2(a)
  +z = RD.Nat.pow2(w)
  +v = RD.Nat.monus(z, 1n)
  +y = RD.Nat.pow2(Nat.add(a, w))
  +env : List<&2, Nat> = [0n, 1n, h, x, z, v, y, Nat.double(h), Nat.double(y)]
  +k = Nat.mul(Nat.mul(Nat.double(h), x), v)
  +r1 = R.NatN.z(env, R.V(8n), R.Ad(R.V(6n), R.V(6n)), {==}, {==}, Y.Nat.double_add(y))
  +r2 = R.NatN.z(env, R.V(6n), R.Ml(R.V(3n), R.V(4n)), {==}, {==}, BP.Pow2.add(a, w))
  +r3 = R.NatN.z(env, R.V(4n), R.Ad(R.V(1n), R.V(5n)), {==}, {==}, BP.Lt.wit(0n, z)(BP.Pow2.pos(w)))
  +r5 = R.NatN.z(env, R.Ml(R.V(1n), R.V(3n)), R.V(3n), {==}, {==}, NL.Nat.add_zero_r(x))
  +r4 = R.NatN.z(env, R.V(7n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, Y.Nat.double_add(h))
  +e = R.NatN.eq(env, R.Ml(R.V(2n), R.V(8n)), R.Ad(R.Ml(R.V(7n), R.V(3n)), R.Ml(R.Ml(R.V(7n), R.V(3n)), R.V(5n))),
    [R.V(2n), R.Ad(R.V(2n), R.V(2n)), R.Ml(R.Ad(R.V(2n), R.V(2n)), R.V(3n)), R.Ad(R.V(2n), R.V(2n)), R.Ng(R.Ad(R.V(3n), R.Ml(R.V(3n), R.V(5n))))],
    [R.Ad(R.V(8n), R.Ng(R.Ad(R.V(6n), R.V(6n)))), R.Ad(R.V(6n), R.Ng(R.Ml(R.V(3n), R.V(4n)))), R.Ad(R.V(4n), R.Ng(R.Ad(R.V(1n), R.V(5n)))), R.Ad(R.Ml(R.V(1n), R.V(3n)), R.Ng(R.V(3n))), R.Ad(R.V(7n), R.Ng(R.Ad(R.V(2n), R.V(2n))))],
    {==}, (r1, (r2, (r3, (r5, (r4, Unit{}))))), {==}, {==})
  E.Ge.of(Nat.mul(h, Nat.double(y)), Nat.mul(Nat.double(h), x), k, e)

# n < 2^p 2^k gives shift <= k
def S3.go(+p1: Nat, +n: Nat, +k: Nat, +h: {RD.Nat.lt(n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k))) == True{} : Bool}, b: Bool, +eb: {RD.Nat.lt(k, Shf(1n+p1, n)) == b : Bool})
  -> E.Le(Shf(1n+p1, n), k):
  match b:
    case False{}:
      eb
    case True{}:
      +w = RD.Nat.monus(Shf(1n+p1, n), 1n+k)
      +es = BP.Lt.wit(k, Shf(1n+p1, n))(eb)
      +sh = Shf(1n+p1, n)
      # 2^p 2^k <= 2^(p-1) 2^shift <= n
      l1 = Pw.ge(p1, k, w)
      l2 = E.Le.trans(Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(k, w))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(sh)), n,
        E.Le.eq(Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(k, w))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(sh)), Equal.cong(Nat, Nat, z => Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(z)), 1n+Nat.add(k, w), sh, Equal.sym(Nat, sh, 1n+Nat.add(k, w), es))),
        S2(p1, n, Nat.add(k, w), es))
      l3 = E.Le.trans(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(k, w))), n, l1, l2)
      Empty.absurd(E.Le(sh, k), Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k))), True{}, Equal.sym(Bool, RD.Nat.lt(n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k))), False{}, l3), h)))

def S3(+p1: Nat, +n: Nat, +k: Nat, +h: {RD.Nat.lt(n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k))) == True{} : Bool}) -> E.Le(Shf(1n+p1, n), k):
  S3.go(p1, n, k, h, RD.Nat.lt(k, Shf(1n+p1, n)), {==})

# a < b and b <= c give a < c
def Lt.le_trans(+a: Nat, +b: Nat, +c: Nat, +h1: {RD.Nat.lt(a, b) == True{} : Bool}, h2: E.Le(b, c)) -> {RD.Nat.lt(a, c) == True{} : Bool}:
  +w = RD.Nat.monus(b, 1n+a)
  +k = RD.Nat.monus(c, b)
  +e = Equal.trans(Nat, c, Nat.add(b, k), Nat.add(a, 1n+Nat.add(w, k)), E.Le.wit(b, c, h2),
    Equal.trans(Nat, Nat.add(b, k), Nat.add(Nat.add(1n+a, w), k), Nat.add(a, 1n+Nat.add(w, k)), Equal.cong(Nat, Nat, z => Nat.add(z, k), b, Nat.add(1n+a, w), BP.Lt.wit(a, b)(h1)),
      Equal.trans(Nat, 1n+Nat.add(Nat.add(a, w), k), 1n+Nat.add(a, Nat.add(w, k)), Nat.add(a, 1n+Nat.add(w, k)), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(a, w), k), Nat.add(a, Nat.add(w, k)), NL.Nat.add_assoc(a, w, k)),
        Equal.sym(Nat, Nat.add(a, 1n+Nat.add(w, k)), 1n+Nat.add(a, Nat.add(w, k)), NL.Nat.add_succ_r(a, Nat.add(w, k))))))
  Equal.trans(Bool, RD.Nat.lt(a, c), RD.Nat.lt(a, Nat.add(a, 1n+Nat.add(w, k))), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(a, z), c, Nat.add(a, 1n+Nat.add(w, k)), e), BP.Lt.self(a, Nat.add(w, k)))

# n >= 2^(p-1) 2^k gives shift >= k
def S4.go(+p1: Nat, +n: Nat, +k: Nat, h: E.Le(Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(k)), n), b: Bool, +eb: {RD.Nat.lt(Shf(1n+p1, n), k) == b : Bool}) -> E.Le(k, Shf(1n+p1, n)):
  match b:
    case False{}:
      eb
    case True{}:
      +sh = Shf(1n+p1, n)
      +w = RD.Nat.monus(k, 1n+sh)
      +ek = BP.Lt.wit(sh, k)(eb)
      # n < 2^p 2^sh <= 2^(p-1) 2^k <= n
      l1 = E.Le.trans(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(sh)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(sh, w))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(k)), Pw.ge(p1, sh, w),
        E.Le.eq(Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(sh, w))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(k)), Equal.cong(Nat, Nat, z => Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(z)), 1n+Nat.add(sh, w), k, Equal.sym(Nat, k, 1n+Nat.add(sh, w), ek))))
      l2 = E.Le.trans(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(sh)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(k)), n, l1, h)
      Empty.absurd(E.Le(k, sh), Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(sh))), True{}, Equal.sym(Bool, RD.Nat.lt(n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(sh))), False{}, l2), S1(p1, n))))

def S4(+p1: Nat, +n: Nat, +k: Nat, h: E.Le(Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(k)), n)) -> E.Le(k, Shf(1n+p1, n)):
  S4.go(p1, n, k, h, RD.Nat.lt(Shf(1n+p1, n), k), {==})

# x <= y gives shift x <= shift y
def ShMono.go(+p1: Nat, +x: Nat, +y: Nat, h: E.Le(x, y), b: Bool, +eb: {RD.Nat.lt(Shf(1n+p1, y), Shf(1n+p1, x)) == b : Bool}) -> E.Le(Shf(1n+p1, x), Shf(1n+p1, y)):
  match b:
    case False{}:
      eb
    case True{}:
      +sx = Shf(1n+p1, x)
      +sy = Shf(1n+p1, y)
      +w = RD.Nat.monus(sx, 1n+sy)
      +es = BP.Lt.wit(sy, sx)(eb)
      # y < 2^p 2^sy <= 2^(p-1) 2^sx <= x <= y
      l1 = E.Le.trans(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(sy)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(sy, w))), x, Pw.ge(p1, sy, w),
        E.Le.trans(Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(sy, w))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(sx)), x,
          E.Le.eq(Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(sy, w))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(sx)), Equal.cong(Nat, Nat, z => Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(z)), 1n+Nat.add(sy, w), sx, Equal.sym(Nat, sx, 1n+Nat.add(sy, w), es))),
          S2(p1, x, Nat.add(sy, w), es)))
      l2 = E.Le.trans(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(sy)), x, y, l1, h)
      Empty.absurd(E.Le(sx, sy), Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(y, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(sy))), True{}, Equal.sym(Bool, RD.Nat.lt(y, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(sy))), False{}, l2), S1(p1, y))))

def ShMono(+p1: Nat, +x: Nat, +y: Nat, h: E.Le(x, y)) -> E.Le(Shf(1n+p1, x), Shf(1n+p1, y)):
  ShMono.go(p1, x, y, h, RD.Nat.lt(Shf(1n+p1, y), Shf(1n+p1, x)), {==})

# twice the rounding error is at most 2^shift
def ErrH.go(+p1: Nat, +n: Nat, u: Bool, +eu: {RD.Tr.rup(RD.Tr.of(1n+p1, n)) == u : Bool}) -> E.Le(Nat.double(E.Dist(E.Rn(1n+p1, n), n)), RD.Nat.pow2(Shf(1n+p1, n))):
  match u:
    case False{}:
      +t = RD.Tr.of(1n+p1, n)
      +q = RD.Tr.q(t)
      +r = R.Tr.r(t)
      +wr = E.Tr.wr(t)
      +sv = RD.Nat.pow2(RD.Tr.s(t))
      +l = Nat.mul(q, sv)
      +hn : {n == Nat.add(l, r) : Nat} = Pair.fst({n == Nat.add(l, r) : Nat}, {sv == Nat.add(Nat.add(r, 1n), wr) : Nat}, E.Sh.n(p1, n))
      +hR = Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, Nat.mul(1n+q, sv), l), RD.Tr.rup(t), False{}, eu)
      +e = E.Dist(E.Rn(1n+p1, n), n)
      +ed = Equal.trans(Nat, e, E.Dist(l, Nat.add(l, r)), r, Equal.trans(Nat, e, E.Dist(l, n), E.Dist(l, Nat.add(l, r)), Equal.cong(Nat, Nat, z => E.Dist(z, n), E.Rn(1n+p1, n), l, hR), Equal.cong(Nat, Nat, z => E.Dist(l, z), n, Nat.add(l, r), hn)), E.Dist.up(l, r))
      +A = Bool.and(Bool.not(RD.Nat.lt(Nat.double(r), sv)), Bool.or(RD.Nat.lt(sv, Nat.double(r)), Bool.not(D.Nat.even(q))))
      +k = RD.Nat.monus(sv, Nat.double(r))
      +hk = R.Nat.lt_f(sv, Nat.double(r))(E.RupF(Nat.double(r), sv, q, Equal.trans(Bool, A, RD.Tr.rup(t), False{}, Equal.sym(Bool, RD.Tr.rup(t), A, BP.Rup.acc(t)), eu)))
      E.Ge.of(sv, Nat.double(e), k, Equal.trans(Nat, sv, Nat.add(Nat.double(r), k), Nat.add(Nat.double(e), k), hk, Equal.cong(Nat, Nat, z => Nat.add(Nat.double(z), k), r, e, Equal.sym(Nat, e, r, ed))))
    case True{}:
      +t = RD.Tr.of(1n+p1, n)
      +q = RD.Tr.q(t)
      +r = R.Tr.r(t)
      +wr = E.Tr.wr(t)
      +sv = RD.Nat.pow2(RD.Tr.s(t))
      +l = Nat.mul(q, sv)
      +hn : {n == Nat.add(l, r) : Nat} = Pair.fst({n == Nat.add(l, r) : Nat}, {sv == Nat.add(Nat.add(r, 1n), wr) : Nat}, E.Sh.n(p1, n))
      +hs : {sv == Nat.add(Nat.add(r, 1n), wr) : Nat} = Pair.snd({n == Nat.add(l, r) : Nat}, {sv == Nat.add(Nat.add(r, 1n), wr) : Nat}, E.Sh.n(p1, n))
      +hR = Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, Nat.mul(1n+q, sv), l), RD.Tr.rup(t), True{}, eu)
      +e = E.Dist(E.Rn(1n+p1, n), n)
      +env0 : List<&2, Nat> = [0n, 1n, n, l, r, sv, wr]
      +eR = R.NatN.eq2(env0, R.Ad(R.V(5n), R.V(3n)), R.Ad(R.V(2n), R.Ad(R.V(1n), R.V(6n))), [], [],
        [R.Ad(R.Ad(R.V(3n), R.V(4n)), R.Ng(R.V(2n))), R.Ad(R.V(5n), R.Ng(R.Ad(R.Ad(R.V(4n), R.V(1n)), R.V(6n))))],
        {==}, Unit{}, (R.NatN.z(env0, R.Ad(R.V(3n), R.V(4n)), R.V(2n), {==}, {==}, Equal.sym(Nat, n, Nat.add(l, r), hn)), (R.NatN.z(env0, R.V(5n), R.Ad(R.Ad(R.V(4n), R.V(1n)), R.V(6n)), {==}, {==}, hs), Unit{})), {==}, {==})
      +ed = Equal.trans(Nat, e, E.Dist(Nat.add(n, 1n+wr), n), 1n+wr, Equal.cong(Nat, Nat, z => E.Dist(z, n), E.Rn(1n+p1, n), Nat.add(n, 1n+wr), Equal.trans(Nat, E.Rn(1n+p1, n), Nat.add(sv, l), Nat.add(n, 1n+wr), hR, eR)), E.Dist.dn(n, 1n+wr))
      +A = Bool.and(Bool.not(RD.Nat.lt(Nat.double(r), sv)), Bool.or(RD.Nat.lt(sv, Nat.double(r)), Bool.not(D.Nat.even(q))))
      +k = RD.Nat.monus(Nat.double(r), sv)
      +hk = R.Nat.lt_f(Nat.double(r), sv)(E.RupT(Nat.double(r), sv, q, Equal.trans(Bool, A, RD.Tr.rup(t), True{}, Equal.sym(Bool, RD.Tr.rup(t), A, BP.Rup.acc(t)), eu)))
      # 2 (1 + wr) + k = 2^s, from 2r = 2^s + k and 2^s = r + 1 + wr
      +env : List<&2, Nat> = [0n, 1n, r, wr, sv, k, Nat.double(r), Nat.double(1n+wr)]
      +es = R.NatN.eq2(env, R.V(4n), R.Ad(R.V(7n), R.V(5n)), [], [],
        [R.Ad(R.V(4n), R.Ng(R.Ad(R.Ad(R.V(2n), R.V(1n)), R.V(3n)))), R.Ad(R.V(4n), R.Ng(R.Ad(R.Ad(R.V(2n), R.V(1n)), R.V(3n)))), R.Ad(R.V(6n), R.Ng(R.Ad(R.V(4n), R.V(5n)))), R.Ad(R.Ad(R.V(2n), R.V(2n)), R.Ng(R.V(6n))), R.Ad(R.Ad(R.Ad(R.V(1n), R.V(3n)), R.Ad(R.V(1n), R.V(3n))), R.Ng(R.V(7n)))],
        {==}, Unit{}, (R.NatN.z(env, R.V(4n), R.Ad(R.Ad(R.V(2n), R.V(1n)), R.V(3n)), {==}, {==}, hs), (R.NatN.z(env, R.V(4n), R.Ad(R.Ad(R.V(2n), R.V(1n)), R.V(3n)), {==}, {==}, hs),
          (R.NatN.z(env, R.V(6n), R.Ad(R.V(4n), R.V(5n)), {==}, {==}, hk), (R.NatN.z(env, R.Ad(R.V(2n), R.V(2n)), R.V(6n), {==}, {==}, Equal.sym(Nat, Nat.double(r), Nat.add(r, r), Y.Nat.double_add(r))),
          (R.NatN.z(env, R.Ad(R.Ad(R.V(1n), R.V(3n)), R.Ad(R.V(1n), R.V(3n))), R.V(7n), {==}, {==}, Equal.sym(Nat, Nat.double(1n+wr), Nat.add(1n+wr, 1n+wr), Y.Nat.double_add(1n+wr))), Unit{}))))), {==}, {==})
      E.Ge.of(sv, Nat.double(e), k, Equal.trans(Nat, sv, Nat.add(Nat.double(1n+wr), k), Nat.add(Nat.double(e), k), es, Equal.cong(Nat, Nat, z => Nat.add(Nat.double(z), k), 1n+wr, e, Equal.sym(Nat, e, 1n+wr, ed))))

def ErrH(+p1: Nat, +n: Nat) -> E.Le(Nat.double(E.Dist(E.Rn(1n+p1, n), n)), RD.Nat.pow2(Shf(1n+p1, n))):
  ErrH.go(p1, n, RD.Tr.rup(RD.Tr.of(1n+p1, n)), {==})

# Veltkamp's split, exactness
# ----------------------------
# With C = 2^s + 1: g = R(C a), d = R(a - g), hi = R(g + d), lo = R(a - hi).
# For a = n > 0 representable: g = n + x, d = -R(x), and F2S.opp (the
# Fast2Sum step for opposite signs) makes g - R(x) representable, so hi is
# exact; lo = R(x) - x is a rounding error of g - n, representable by LA.d.

def Sp.c(+s: Nat) -> I.Int:
  I.IPos{1n+RD.Nat.pow2(s)}

def Sp.g(+p: Nat, +s: Nat, +a: I.Int) -> I.Int:
  E.RNi(p, I.Int.mul(Sp.c(s), a))

def Sp.d(+p: Nat, +s: Nat, +a: I.Int) -> I.Int:
  E.RNi(p, I.Int.add(a, I.Int.neg(Sp.g(p, s, a))))

def Sp.h(+p: Nat, +s: Nat, +a: I.Int) -> I.Int:
  E.RNi(p, I.Int.add(Sp.g(p, s, a), Sp.d(p, s, a)))

def Sp.l(+p: Nat, +s: Nat, +a: I.Int) -> I.Int:
  E.RNi(p, I.Int.add(a, I.Int.neg(Sp.h(p, s, a))))

# the same on magnitudes, for a = n >= 0
def V.g(+p: Nat, +s: Nat, +n: Nat) -> Nat:
  E.Rn(p, Nat.mul(1n+RD.Nat.pow2(s), n))

def V.x(+p: Nat, +s: Nat, +n: Nat) -> Nat:
  RD.Nat.monus(V.g(p, s, n), n)

def V.d(+p: Nat, +s: Nat, +n: Nat) -> Nat:
  E.Rn(p, V.x(p, s, n))

def V.hi(+p: Nat, +s: Nat, +n: Nat) -> Nat:
  RD.Nat.monus(V.g(p, s, n), V.d(p, s, n))

# g = n + x
def V.gx(+p1: Nat, +s: Nat, +n: Nat, +fn: {E.Rn(1n+p1, n) == n : Nat}) -> {V.g(1n+p1, s, n) == Nat.add(n, V.x(1n+p1, s, n)) : Nat}:
  +m = Nat.mul(1n+RD.Nat.pow2(s), n)
  E.Le.wit(n, V.g(1n+p1, s, n), E.Mono.lo(p1, m, n, fn, E.Ge.of(m, n, Nat.mul(RD.Nat.pow2(s), n), {==})))

# g = d + hi, hi representable
def V.hi.ok(+p1: Nat, +s: Nat, +n: Nat, +fn: {E.Rn(1n+p1, n) == n : Nat})
  -> {V.g(1n+p1, s, n) == Nat.add(V.d(1n+p1, s, n), V.hi(1n+p1, s, n)) : Nat} & {E.Rn(1n+p1, V.hi(1n+p1, s, n)) == V.hi(1n+p1, s, n) : Nat}:
  E.F2S.opp(p1, V.g(1n+p1, s, n), n, V.x(1n+p1, s, n), V.gx(p1, s, n, fn), E.RF(p1, Nat.mul(1n+RD.Nat.pow2(s), n)), fn)

# lo = n - hi has magnitude |d - x|, a rounding error: representable
def V.lo.ok(+p1: Nat, +s: Nat, +n: Nat, +fn: {E.Rn(1n+p1, n) == n : Nat})
  -> {E.Rn(1n+p1, E.Dist(V.d(1n+p1, s, n), V.x(1n+p1, s, n))) == E.Dist(V.d(1n+p1, s, n), V.x(1n+p1, s, n)) : Nat}:
  E.LA.d(p1, V.g(1n+p1, s, n), n, V.x(1n+p1, s, n), V.gx(p1, s, n, fn), E.RF(p1, Nat.mul(1n+RD.Nat.pow2(s), n)), fn)

# Int identities t = u + sum us, every us zero
def IntN2(+env: List<&2, I.Int>, +t: N.Tm, +u: N.Tm, +ls: List<&2, N.Tm>, +rs: List<&2, N.Tm>, +us: List<&2, N.Tm>,
  ok: {N.NormS.left(N.Tm.diff(t, N.TAdd{u, N.TAdd{EQ.Tm.lin(ls, rs), EQ.Tm.sum(us)}})) == Nil{} : List<&2, N.Mono>},
  hz: EQ.Zs(~I.Int, ~I.IPos{0n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, env, rs),
  hu: EQ.Zs(~I.Int, ~I.IPos{0n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, env, us))
  -> {N.Tm.eval(~I.Int, ~I.IPos{0n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, env, t) == N.Tm.eval(~I.Int, ~I.IPos{0n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, env, u) : I.Int}:
  EQ.Rel.many2(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg,
    env, t, u, ls, rs, us, ok, hz, hu)

def IntZ(+env: List<&2, I.Int>, +t: N.Tm, +u: N.Tm, +e: {N.Tm.eval(~I.Int, ~I.IPos{0n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, env, t) == N.Tm.eval(~I.Int, ~I.IPos{0n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, env, u) : I.Int})
  -> {N.Tm.eval(~I.Int, ~I.IPos{0n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, env, N.TAdd{t, N.TNeg{u}}) == I.IPos{0n} : I.Int}:
  Y.Rel.z(N.Tm.eval(~I.Int, ~I.IPos{0n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, env, t), N.Tm.eval(~I.Int, ~I.IPos{0n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, env, u), e)

# n - hi has magnitude |d - x|
def V.lo.mag(+p1: Nat, +s: Nat, +n: Nat, +fn: {E.Rn(1n+p1, n) == n : Nat})
  -> {RD.Int.mag(I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{V.hi(1n+p1, s, n)}))) == E.Dist(V.d(1n+p1, s, n), V.x(1n+p1, s, n)) : Nat}:
  +p : Nat = 1n+p1
  +g = V.g(p, s, n)
  +x = V.x(p, s, n)
  +d = V.d(p, s, n)
  +hi = V.hi(p, s, n)
  +hx = V.gx(p1, s, n, fn)
  +eg : {g == Nat.add(d, hi) : Nat} = Pair.fst({g == Nat.add(d, hi) : Nat}, {E.Rn(p, hi) == hi : Nat}, V.hi.ok(p1, s, n, fn))
  +lz = I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{hi}))
  +env3 : List<&2, I.Int> = [I.IPos{n}, I.IPos{hi}, I.IPos{d}, I.IPos{x}]
  +e3 = IntN2(env3, R.Ad(R.V(0n), R.Ng(R.V(1n))), R.Ad(R.V(2n), R.Ng(R.V(3n))), [], [], [R.Ad(R.Ad(R.V(0n), R.V(3n)), R.Ng(R.Ad(R.V(2n), R.V(1n))))],
    {==}, Unit{}, (IntZ(env3, R.Ad(R.V(0n), R.V(3n)), R.Ad(R.V(2n), R.V(1n)),
      Equal.cong(Nat, I.Int, w => I.IPos{w}, Nat.add(n, x), Nat.add(d, hi), Equal.trans(Nat, Nat.add(n, x), g, Nat.add(d, hi), Equal.sym(Nat, g, Nat.add(n, x), hx), eg))), Unit{}))
  Equal.trans(Nat, RD.Int.mag(lz), RD.Int.mag(I.Int.add(I.IPos{d}, I.Int.neg(I.IPos{x}))), E.Dist(d, x),
    Equal.cong(I.Int, Nat, w => RD.Int.mag(w), lz, I.Int.add(I.IPos{d}, I.Int.neg(I.IPos{x})), e3), E.Mag.diff(d, x))

# for a = n >= 0: hi = g - d exactly, lo = n - hi exactly
def Sp.pos(+p1: Nat, +s: Nat, +n: Nat, +fn: {E.Rn(1n+p1, n) == n : Nat})
  -> {Sp.h(1n+p1, s, I.IPos{n}) == I.IPos{V.hi(1n+p1, s, n)} : I.Int} & {Sp.l(1n+p1, s, I.IPos{n}) == I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{V.hi(1n+p1, s, n)})) : I.Int}:
  +p : Nat = 1n+p1
  +g = V.g(p, s, n)
  +x = V.x(p, s, n)
  +d = V.d(p, s, n)
  +hi = V.hi(p, s, n)
  +hx = V.gx(p1, s, n, fn)
  +eg : {g == Nat.add(d, hi) : Nat} = Pair.fst({g == Nat.add(d, hi) : Nat}, {E.Rn(p, hi) == hi : Nat}, V.hi.ok(p1, s, n, fn))
  +fh : {E.Rn(p, hi) == hi : Nat} = Pair.snd({g == Nat.add(d, hi) : Nat}, {E.Rn(p, hi) == hi : Nat}, V.hi.ok(p1, s, n, fn))
  # a - g = -x, so d = -R(x)
  +env1 : List<&2, I.Int> = [I.IPos{n}, I.IPos{x}]
  +e1 = Equal.trans(I.Int, I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{g})), I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{Nat.add(n, x)})), I.Int.neg(I.IPos{x}),
    Equal.cong(Nat, I.Int, w => I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{w})), g, Nat.add(n, x), hx),
    BP.IntN(env1, R.Ad(R.V(0n), R.Ng(R.Ad(R.V(0n), R.V(1n)))), R.Ng(R.V(1n)), [], [], {==}, Unit{}))
  +ed = Equal.trans(I.Int, Sp.d(p, s, I.IPos{n}), E.RNi(p, I.Int.neg(I.IPos{x})), I.Int.neg(I.IPos{d}),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{g})), I.Int.neg(I.IPos{x}), e1), E.RNi.neg(p, I.IPos{x}))
  # g + d = hi
  +env2 : List<&2, I.Int> = [I.IPos{d}, I.IPos{hi}]
  +e2 = Equal.trans(I.Int, I.Int.add(I.IPos{g}, I.Int.neg(I.IPos{d})), I.Int.add(I.IPos{Nat.add(d, hi)}, I.Int.neg(I.IPos{d})), I.IPos{hi},
    Equal.cong(Nat, I.Int, w => I.Int.add(I.IPos{w}, I.Int.neg(I.IPos{d})), g, Nat.add(d, hi), eg),
    BP.IntN(env2, R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(0n))), R.V(1n), [], [], {==}, Unit{}))
  +eh = Equal.trans(I.Int, Sp.h(p, s, I.IPos{n}), E.RNi(p, I.Int.add(I.IPos{g}, I.Int.neg(I.IPos{d}))), I.IPos{hi},
    Equal.cong(I.Int, I.Int, w => E.RNi(p, I.Int.add(I.IPos{g}, w)), Sp.d(p, s, I.IPos{n}), I.Int.neg(I.IPos{d}), ed),
    Equal.trans(I.Int, E.RNi(p, I.Int.add(I.IPos{g}, I.Int.neg(I.IPos{d}))), E.RNi(p, I.IPos{hi}), I.IPos{hi},
      Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(I.IPos{g}, I.Int.neg(I.IPos{d})), I.IPos{hi}, e2),
      Equal.cong(Nat, I.Int, w => I.IPos{w}, E.Rn(p, hi), hi, fh)))
  # n - hi = d - x, a rounding error
  +lz = I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{hi}))
  +em = V.lo.mag(p1, s, n, fn)
  +el = Equal.trans(I.Int, Sp.l(p, s, I.IPos{n}), E.RNi(p, lz), lz,
    Equal.cong(I.Int, I.Int, w => E.RNi(p, I.Int.add(I.IPos{n}, I.Int.neg(w))), Sp.h(p, s, I.IPos{n}), I.IPos{hi}, eh),
    E.RNi.exact(p, lz, E.Fn.eq(p, RD.Int.mag(lz), E.Dist(d, x), em, V.lo.ok(p1, s, n, fn))))
  (eh, el)

# the split commutes with negation
def Sp.sym.g(+p: Nat, +s: Nat, +a: I.Int) -> {Sp.g(p, s, I.Int.neg(a)) == I.Int.neg(Sp.g(p, s, a)) : I.Int}:
  +env : List<&2, I.Int> = [Sp.c(s), a]
  Equal.trans(I.Int, Sp.g(p, s, I.Int.neg(a)), E.RNi(p, I.Int.neg(I.Int.mul(Sp.c(s), a))), I.Int.neg(Sp.g(p, s, a)),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.mul(Sp.c(s), I.Int.neg(a)), I.Int.neg(I.Int.mul(Sp.c(s), a)), BP.IntN(env, R.Ml(R.V(0n), R.Ng(R.V(1n))), R.Ng(R.Ml(R.V(0n), R.V(1n))), [], [], {==}, Unit{})),
    E.RNi.neg(p, I.Int.mul(Sp.c(s), a)))

def Sp.sym.d(+p: Nat, +s: Nat, +a: I.Int) -> {Sp.d(p, s, I.Int.neg(a)) == I.Int.neg(Sp.d(p, s, a)) : I.Int}:
  +g = Sp.g(p, s, a)
  +env : List<&2, I.Int> = [a, g]
  Equal.trans(I.Int, Sp.d(p, s, I.Int.neg(a)), E.RNi(p, I.Int.neg(I.Int.add(a, I.Int.neg(g)))), I.Int.neg(Sp.d(p, s, a)),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(I.Int.neg(a), I.Int.neg(Sp.g(p, s, I.Int.neg(a)))), I.Int.neg(I.Int.add(a, I.Int.neg(g))),
      Equal.trans(I.Int, I.Int.add(I.Int.neg(a), I.Int.neg(Sp.g(p, s, I.Int.neg(a)))), I.Int.add(I.Int.neg(a), I.Int.neg(I.Int.neg(g))), I.Int.neg(I.Int.add(a, I.Int.neg(g))),
        Equal.cong(I.Int, I.Int, w => I.Int.add(I.Int.neg(a), I.Int.neg(w)), Sp.g(p, s, I.Int.neg(a)), I.Int.neg(g), Sp.sym.g(p, s, a)),
        BP.IntN(env, R.Ad(R.Ng(R.V(0n)), R.Ng(R.Ng(R.V(1n)))), R.Ng(R.Ad(R.V(0n), R.Ng(R.V(1n)))), [], [], {==}, Unit{}))),
    E.RNi.neg(p, I.Int.add(a, I.Int.neg(g))))

def Sp.sym.h(+p: Nat, +s: Nat, +a: I.Int) -> {Sp.h(p, s, I.Int.neg(a)) == I.Int.neg(Sp.h(p, s, a)) : I.Int}:
  +g = Sp.g(p, s, a)
  +d = Sp.d(p, s, a)
  +env : List<&2, I.Int> = [g, d]
  Equal.trans(I.Int, Sp.h(p, s, I.Int.neg(a)), E.RNi(p, I.Int.neg(I.Int.add(g, d))), I.Int.neg(Sp.h(p, s, a)),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(Sp.g(p, s, I.Int.neg(a)), Sp.d(p, s, I.Int.neg(a))), I.Int.neg(I.Int.add(g, d)),
      Equal.trans(I.Int, I.Int.add(Sp.g(p, s, I.Int.neg(a)), Sp.d(p, s, I.Int.neg(a))), I.Int.add(I.Int.neg(g), I.Int.neg(d)), I.Int.neg(I.Int.add(g, d)),
        Y.Int.cong2(Sp.g(p, s, I.Int.neg(a)), I.Int.neg(g), Sp.d(p, s, I.Int.neg(a)), I.Int.neg(d), Sp.sym.g(p, s, a), Sp.sym.d(p, s, a)),
        BP.IntN(env, R.Ad(R.Ng(R.V(0n)), R.Ng(R.V(1n))), R.Ng(R.Ad(R.V(0n), R.V(1n))), [], [], {==}, Unit{}))),
    E.RNi.neg(p, I.Int.add(g, d)))

def Sp.sym.l(+p: Nat, +s: Nat, +a: I.Int) -> {Sp.l(p, s, I.Int.neg(a)) == I.Int.neg(Sp.l(p, s, a)) : I.Int}:
  +h = Sp.h(p, s, a)
  +env : List<&2, I.Int> = [a, h]
  Equal.trans(I.Int, Sp.l(p, s, I.Int.neg(a)), E.RNi(p, I.Int.neg(I.Int.add(a, I.Int.neg(h)))), I.Int.neg(Sp.l(p, s, a)),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(I.Int.neg(a), I.Int.neg(Sp.h(p, s, I.Int.neg(a)))), I.Int.neg(I.Int.add(a, I.Int.neg(h))),
      Equal.trans(I.Int, I.Int.add(I.Int.neg(a), I.Int.neg(Sp.h(p, s, I.Int.neg(a)))), I.Int.add(I.Int.neg(a), I.Int.neg(I.Int.neg(h))), I.Int.neg(I.Int.add(a, I.Int.neg(h))),
        Equal.cong(I.Int, I.Int, w => I.Int.add(I.Int.neg(a), I.Int.neg(w)), Sp.h(p, s, I.Int.neg(a)), I.Int.neg(h), Sp.sym.h(p, s, a)),
        BP.IntN(env, R.Ad(R.Ng(R.V(0n)), R.Ng(R.Ng(R.V(1n)))), R.Ng(R.Ad(R.V(0n), R.Ng(R.V(1n)))), [], [], {==}, Unit{}))),
    E.RNi.neg(p, I.Int.add(a, I.Int.neg(h))))

def Split.nonneg(+p1: Nat, +s: Nat, +n: Nat, +fn: {E.Rn(1n+p1, n) == n : Nat})
  -> {Sp.l(1n+p1, s, I.IPos{n}) == I.Int.add(I.IPos{n}, I.Int.neg(Sp.h(1n+p1, s, I.IPos{n}))) : I.Int}:
  +p : Nat = 1n+p1
  +hi = V.hi(p, s, n)
  +eh = Pair.fst({Sp.h(p, s, I.IPos{n}) == I.IPos{hi} : I.Int}, {Sp.l(p, s, I.IPos{n}) == I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{hi})) : I.Int}, Sp.pos(p1, s, n, fn))
  +el = Pair.snd({Sp.h(p, s, I.IPos{n}) == I.IPos{hi} : I.Int}, {Sp.l(p, s, I.IPos{n}) == I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{hi})) : I.Int}, Sp.pos(p1, s, n, fn))
  Equal.trans(I.Int, Sp.l(p, s, I.IPos{n}), I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{hi})), I.Int.add(I.IPos{n}, I.Int.neg(Sp.h(p, s, I.IPos{n}))), el,
    Equal.cong(I.Int, I.Int, w => I.Int.add(I.IPos{n}, I.Int.neg(w)), I.IPos{hi}, Sp.h(p, s, I.IPos{n}), Equal.sym(I.Int, Sp.h(p, s, I.IPos{n}), I.IPos{hi}, eh)))

# Veltkamp's split is exact: for representable a, at any precision p and
# any s, lo = a - hi exactly, so hi + lo = a
def Split(+p1: Nat, +s: Nat, +a: I.Int, +fa: {E.Rn(1n+p1, RD.Int.mag(a)) == RD.Int.mag(a) : Nat}) -> {Sp.l(1n+p1, s, a) == I.Int.add(a, I.Int.neg(Sp.h(1n+p1, s, a))) : I.Int}:
  match a:
    case I.IPos{+n}:
      Split.nonneg(p1, s, n, fa)
    case I.INeg{+k}:
      +p : Nat = 1n+p1
      +b : I.Int = I.IPos{1n+k}
      +h = Sp.h(p, s, b)
      +env : List<&2, I.Int> = [b, h]
      Equal.trans(I.Int, Sp.l(p, s, I.Int.neg(b)), I.Int.neg(I.Int.add(b, I.Int.neg(h))), I.Int.add(I.Int.neg(b), I.Int.neg(Sp.h(p, s, I.Int.neg(b)))),
        Equal.trans(I.Int, Sp.l(p, s, I.Int.neg(b)), I.Int.neg(Sp.l(p, s, b)), I.Int.neg(I.Int.add(b, I.Int.neg(h))), Sp.sym.l(p, s, b),
          Equal.cong(I.Int, I.Int, w => I.Int.neg(w), Sp.l(p, s, b), I.Int.add(b, I.Int.neg(h)), Split.nonneg(p1, s, 1n+k, fa))),
        Equal.trans(I.Int, I.Int.neg(I.Int.add(b, I.Int.neg(h))), I.Int.add(I.Int.neg(b), I.Int.neg(I.Int.neg(h))), I.Int.add(I.Int.neg(b), I.Int.neg(Sp.h(p, s, I.Int.neg(b)))),
          BP.IntN(env, R.Ng(R.Ad(R.V(0n), R.Ng(R.V(1n)))), R.Ad(R.Ng(R.V(0n)), R.Ng(R.Ng(R.V(1n)))), [], [], {==}, Unit{}),
          Equal.cong(I.Int, I.Int, w => I.Int.add(I.Int.neg(b), I.Int.neg(w)), I.Int.neg(h), Sp.h(p, s, I.Int.neg(b)), Equal.sym(I.Int, Sp.h(p, s, I.Int.neg(b)), I.Int.neg(h), Sp.sym.h(p, s, b)))))

# Order
# -----

def Le.mulr(+a: Nat, +b: Nat, +x: Nat, h: E.Le(a, b)) -> E.Le(Nat.mul(a, x), Nat.mul(b, x)):
  +k = RD.Nat.monus(b, a)
  E.Ge.of(Nat.mul(b, x), Nat.mul(a, x), Nat.mul(k, x),
    Equal.trans(Nat, Nat.mul(b, x), Nat.mul(Nat.add(a, k), x), Nat.add(Nat.mul(a, x), Nat.mul(k, x)), Equal.cong(Nat, Nat, z => Nat.mul(z, x), b, Nat.add(a, k), E.Le.wit(a, b, h)), NL.Nat.mul_dist_r(a, k, x)))

def Le.mull(+x: Nat, +a: Nat, +b: Nat, h: E.Le(a, b)) -> E.Le(Nat.mul(x, a), Nat.mul(x, b)):
  E.Le.trans(Nat.mul(x, a), Nat.mul(a, x), Nat.mul(x, b), E.Le.eq(Nat.mul(x, a), Nat.mul(a, x), NL.Nat.mul_comm(x, a)),
    E.Le.trans(Nat.mul(a, x), Nat.mul(b, x), Nat.mul(x, b), Le.mulr(a, b, x, h), E.Le.eq(Nat.mul(b, x), Nat.mul(x, b), NL.Nat.mul_comm(b, x))))

def Le.addl(+k: Nat, +a: Nat, +b: Nat, h: E.Le(a, b)) -> E.Le(Nat.add(k, a), Nat.add(k, b)):
  Equal.trans(Bool, RD.Nat.lt(Nat.add(k, b), Nat.add(k, a)), RD.Nat.lt(b, a), False{}, BP.Lt.shift(k, b, a), h)

def Le.addr(+a: Nat, +b: Nat, +k: Nat, h: E.Le(a, b)) -> E.Le(Nat.add(a, k), Nat.add(b, k)):
  E.Le.trans(Nat.add(a, k), Nat.add(k, a), Nat.add(b, k), E.Le.eq(Nat.add(a, k), Nat.add(k, a), NL.Nat.add_comm(a, k)),
    E.Le.trans(Nat.add(k, a), Nat.add(k, b), Nat.add(b, k), Le.addl(k, a, b, h), E.Le.eq(Nat.add(k, b), Nat.add(b, k), NL.Nat.add_comm(k, b))))

def Le.add2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, h1: E.Le(a, b), h2: E.Le(c, d)) -> E.Le(Nat.add(a, c), Nat.add(b, d)):
  E.Le.trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), Le.addr(a, b, c, h1), Le.addl(b, c, d, h2))

def Lt.to_le(+a: Nat, +b: Nat, +h: {RD.Nat.lt(a, b) == True{} : Bool}) -> E.Le(a, b):
  BP.Lt.asym(a, b, h)

def Le.lt_trans(+a: Nat, +b: Nat, +c: Nat, h1: E.Le(a, b), +h2: {RD.Nat.lt(b, c) == True{} : Bool}) -> {RD.Nat.lt(a, c) == True{} : Bool}:
  E.Lt.le(a, RD.Nat.monus(b, a), c, Equal.trans(Bool, RD.Nat.lt(Nat.add(a, RD.Nat.monus(b, a)), c), RD.Nat.lt(b, c), True{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(z, c), Nat.add(a, RD.Nat.monus(b, a)), b, Equal.sym(Nat, b, Nat.add(a, RD.Nat.monus(b, a)), E.Le.wit(a, b, h1))), h2))

# a < b + 1 gives a <= b
def Le.of_lt1(+a: Nat, +b: Nat, +h: {RD.Nat.lt(a, 1n+b) == True{} : Bool}) -> E.Le(a, b):
  match a b:
    case 0n b2:
      BP.Lt.z(b2)
    case 1n+a2 0n:
      Empty.absurd({RD.Nat.lt(0n, 1n+a2) == False{} : Bool}, Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(a2, 0n), True{}, Equal.sym(Bool, RD.Nat.lt(a2, 0n), False{}, BP.Lt.z(a2)), h)))
    case 1n+a2 1n+b2:
      Le.of_lt1(a2, b2, h)

def Pow2.mono(+a: Nat, +b: Nat, h: E.Le(a, b)) -> E.Le(RD.Nat.pow2(a), RD.Nat.pow2(b)):
  +k = RD.Nat.monus(b, a)
  +w = RD.Nat.monus(RD.Nat.pow2(k), 1n)
  +pa = RD.Nat.pow2(a)
  +ek : {RD.Nat.pow2(k) == 1n+w : Nat} = BP.Lt.wit(0n, RD.Nat.pow2(k))(BP.Pow2.pos(k))
  E.Ge.of(RD.Nat.pow2(b), pa, Nat.mul(pa, w),
    Equal.trans(Nat, RD.Nat.pow2(b), Nat.mul(pa, RD.Nat.pow2(k)), Nat.add(pa, Nat.mul(pa, w)),
      Equal.trans(Nat, RD.Nat.pow2(b), RD.Nat.pow2(Nat.add(a, k)), Nat.mul(pa, RD.Nat.pow2(k)), Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), b, Nat.add(a, k), E.Le.wit(a, b, h)), BP.Pow2.add(a, k)),
      Equal.trans(Nat, Nat.mul(pa, RD.Nat.pow2(k)), Nat.mul(pa, 1n+w), Nat.add(pa, Nat.mul(pa, w)), Equal.cong(Nat, Nat, z => Nat.mul(pa, z), RD.Nat.pow2(k), 1n+w, ek), NL.Nat.mul_succ_r(pa, w))))

def Le.canl(+k: Nat, +a: Nat, +b: Nat, h: E.Le(Nat.add(k, a), Nat.add(k, b))) -> E.Le(a, b):
  Equal.trans(Bool, RD.Nat.lt(b, a), RD.Nat.lt(Nat.add(k, b), Nat.add(k, a)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.add(k, b), Nat.add(k, a)), RD.Nat.lt(b, a), BP.Lt.shift(k, b, a)), h)

def Mo.le.go(+a: Nat, +b: Nat, l: Bool, +el: {RD.Nat.lt(a, b) == l : Bool}) -> E.Le(b, Nat.add(a, RD.Nat.monus(b, a))):
  match l:
    case True{}:
      E.Le.eq(b, Nat.add(a, RD.Nat.monus(b, a)), R.Nat.lt_t(a, b)(el))
    case False{}:
      E.Le.trans(b, a, Nat.add(a, RD.Nat.monus(b, a)), E.Ge.of(a, b, RD.Nat.monus(a, b), R.Nat.lt_f(a, b)(el)), E.Le.add(a, RD.Nat.monus(b, a)))

# b <= a + (b - a)
def Mo.le(+a: Nat, +b: Nat) -> E.Le(b, Nat.add(a, RD.Nat.monus(b, a))):
  Mo.le.go(a, b, RD.Nat.lt(a, b), {==})

# b <= a + |a - b| and a <= b + |a - b|
def Dist.ge(+a: Nat, +b: Nat) -> E.Le(b, Nat.add(a, E.Dist(a, b))):
  E.Le.trans(b, Nat.add(a, RD.Nat.monus(b, a)), Nat.add(a, E.Dist(a, b)), Mo.le(a, b),
    Le.addl(a, RD.Nat.monus(b, a), E.Dist(a, b), E.Ge.of(E.Dist(a, b), RD.Nat.monus(b, a), RD.Nat.monus(a, b), NL.Nat.add_comm(RD.Nat.monus(a, b), RD.Nat.monus(b, a)))))

def Dist.ge2(+a: Nat, +b: Nat) -> E.Le(a, Nat.add(b, E.Dist(a, b))):
  E.Le.trans(a, Nat.add(b, E.Dist(b, a)), Nat.add(b, E.Dist(a, b)), Dist.ge(b, a), E.Le.eq(Nat.add(b, E.Dist(b, a)), Nat.add(b, E.Dist(a, b)), Equal.cong(Nat, Nat, z => Nat.add(b, z), E.Dist(b, a), E.Dist(a, b), E.Dist.comm(b, a))))

# 1 <= 2^k, 1 + 2^k <= 2^(k+1)
def Le.one(+k: Nat) -> E.Le(1n, RD.Nat.pow2(k)):
  E.Ge.of(RD.Nat.pow2(k), 1n, RD.Nat.monus(RD.Nat.pow2(k), 1n), BP.Lt.wit(0n, RD.Nat.pow2(k))(BP.Pow2.pos(k)))

def Le.one2(+k: Nat) -> E.Le(1n+RD.Nat.pow2(k), RD.Nat.pow2(1n+k)):
  +y = RD.Nat.pow2(k)
  E.Le.trans(1n+y, Nat.add(y, y), Nat.double(y), Le.addr(1n, y, y, Le.one(k)), E.Le.eq(Nat.add(y, y), Nat.double(y), Equal.sym(Nat, Nat.double(y), Nat.add(y, y), Y.Nat.double_add(y))))

# the split's sizes
# -----------------
# For n in [2^(p-1), 2^p): x = g - n lies in [2^(p-1) 2^s, 2^p 2^s].

# C n < 2^p 2^(s+1)
def V.cn(+p1: Nat, +s: Nat, +n: Nat, +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+p1)) == True{} : Bool})
  -> {RD.Nat.lt(Nat.mul(1n+RD.Nat.pow2(s), n), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+s))) == True{} : Bool}:
  +P = RD.Nat.pow2(1n+p1)
  +S = RD.Nat.pow2(s)
  +h1 = Equal.trans(Bool, RD.Nat.lt(Nat.mul(1n+S, n), Nat.mul(P, 1n+S)), RD.Nat.lt(Nat.mul(n, 1n+S), Nat.mul(P, 1n+S)), True{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(z, Nat.mul(P, 1n+S)), Nat.mul(1n+S, n), Nat.mul(n, 1n+S), NL.Nat.mul_comm(1n+S, n)), E.Lt.mono(n, P, 1n+S, hn, {==}))
  Lt.le_trans(Nat.mul(1n+S, n), Nat.mul(P, 1n+S), Nat.mul(P, RD.Nat.pow2(1n+s)), h1, Le.mull(P, 1n+S, RD.Nat.pow2(1n+s), Le.one2(s)))

# |g - C n| <= 2^s
def V.err(+p1: Nat, +s: Nat, +n: Nat, +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+p1)) == True{} : Bool})
  -> E.Le(E.Dist(V.g(1n+p1, s, n), Nat.mul(1n+RD.Nat.pow2(s), n)), RD.Nat.pow2(s)):
  +cn = Nat.mul(1n+RD.Nat.pow2(s), n)
  +dd = E.Dist(V.g(1n+p1, s, n), cn)
  h2 = E.Le.trans(Nat.double(dd), RD.Nat.pow2(Shf(1n+p1, cn)), RD.Nat.pow2(1n+s), ErrH(p1, cn), Pow2.mono(Shf(1n+p1, cn), 1n+s, S3(p1, cn, 1n+s, V.cn(p1, s, n, hn))))
  Equal.trans(Bool, RD.Nat.lt(RD.Nat.pow2(s), dd), RD.Nat.lt(Nat.double(RD.Nat.pow2(s)), Nat.double(dd)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.double(RD.Nat.pow2(s)), Nat.double(dd)), RD.Nat.lt(RD.Nat.pow2(s), dd), E.Lt.dd(RD.Nat.pow2(s), dd)), h2)

def Le.succ(+a: Nat, +b: Nat, +h: {RD.Nat.lt(a, b) == True{} : Bool}) -> E.Le(1n+a, b):
  E.Ge.of(b, 1n+a, RD.Nat.monus(b, 1n+a), BP.Lt.wit(a, b)(h))

# x <= 2^p 2^s
def V.xhi(+p1: Nat, +s: Nat, +n: Nat, +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+p1)) == True{} : Bool}) -> E.Le(V.x(1n+p1, s, n), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s))):
  +p : Nat = 1n+p1
  +P = RD.Nat.pow2(p)
  +S = RD.Nat.pow2(s)
  +g = V.g(p, s, n)
  +x = V.x(p, s, n)
  +sn = Nat.mul(S, n)
  +cn = Nat.mul(1n+S, n)
  +fn = E.Small(p1, n, Lt.to_le(n, P, hn))
  # n + x = g <= C n + 2^s = n + (S n + S)
  h1 = E.Le.trans(Nat.add(n, x), g, Nat.add(n, Nat.add(sn, S)), E.Le.eq(Nat.add(n, x), g, Equal.sym(Nat, g, Nat.add(n, x), V.gx(p1, s, n, fn))),
    E.Le.trans(g, Nat.add(cn, E.Dist(g, cn)), Nat.add(n, Nat.add(sn, S)), Dist.ge2(g, cn),
      E.Le.trans(Nat.add(cn, E.Dist(g, cn)), Nat.add(cn, S), Nat.add(n, Nat.add(sn, S)), Le.addl(cn, E.Dist(g, cn), S, V.err(p1, s, n, hn)), E.Le.eq(Nat.add(cn, S), Nat.add(n, Nat.add(sn, S)), NL.Nat.add_assoc(n, sn, S)))))
  h2 = Le.canl(n, x, Nat.add(sn, S), h1)
  # S n + S = S (n + 1) <= S 2^p
  E.Le.trans(x, Nat.add(sn, S), Nat.mul(P, S), h2,
    E.Le.trans(Nat.add(sn, S), Nat.mul(S, 1n+n), Nat.mul(P, S), E.Le.eq(Nat.add(sn, S), Nat.mul(S, 1n+n), Equal.trans(Nat, Nat.add(sn, S), Nat.add(S, sn), Nat.mul(S, 1n+n), NL.Nat.add_comm(sn, S), Equal.sym(Nat, Nat.mul(S, 1n+n), Nat.add(S, sn), NL.Nat.mul_succ_r(S, n)))),
      E.Le.trans(Nat.mul(S, 1n+n), Nat.mul(S, P), Nat.mul(P, S), Le.mull(S, 1n+n, P, Le.succ(n, P, hn)), E.Le.eq(Nat.mul(S, P), Nat.mul(P, S), NL.Nat.mul_comm(S, P)))))

def V.xlo.go(+p1: Nat, +s: Nat, +n: Nat, +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+p1)) == True{} : Bool}, hh: E.Le(RD.Nat.pow2(p1), n), hc: E.Le(1n+RD.Nat.pow2(s), RD.Nat.pow2(1n+p1)),
  l: Bool, +el: {RD.Nat.lt(RD.Nat.pow2(p1), n) == l : Bool}) -> E.Le(Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(s)), V.x(1n+p1, s, n)):
  match l:
    case True{}:
      +p : Nat = 1n+p1
      +P = RD.Nat.pow2(p)
      +H = RD.Nat.pow2(p1)
      +S = RD.Nat.pow2(s)
      +g = V.g(p, s, n)
      +x = V.x(p, s, n)
      +sh = Nat.mul(S, H)
      +cn = Nat.mul(1n+S, n)
      +fn = E.Small(p1, n, Lt.to_le(n, P, hn))
      +eg = Equal.sym(Nat, g, Nat.add(n, x), V.gx(p1, s, n, fn))
      hsh = E.Le.eq(Nat.mul(H, S), sh, NL.Nat.mul_comm(H, S))
      # n > H: S + S H <= S n <= x + S, from C n <= g + 2^s
      h1 = E.Le.trans(Nat.add(n, Nat.mul(S, n)), Nat.add(g, E.Dist(g, cn)), Nat.add(n, Nat.add(x, S)), Dist.ge(g, cn),
        E.Le.trans(Nat.add(g, E.Dist(g, cn)), Nat.add(g, S), Nat.add(n, Nat.add(x, S)), Le.addl(g, E.Dist(g, cn), S, V.err(p1, s, n, hn)),
          E.Le.eq(Nat.add(g, S), Nat.add(n, Nat.add(x, S)), Equal.trans(Nat, Nat.add(g, S), Nat.add(Nat.add(n, x), S), Nat.add(n, Nat.add(x, S)), Equal.cong(Nat, Nat, z => Nat.add(z, S), g, Nat.add(n, x), V.gx(p1, s, n, fn)), NL.Nat.add_assoc(n, x, S)))))
      h2 = Le.canl(n, Nat.mul(S, n), Nat.add(x, S), h1)
      h3 = E.Le.trans(Nat.add(S, sh), Nat.mul(S, n), Nat.add(S, x), E.Le.trans(Nat.add(S, sh), Nat.mul(S, 1n+H), Nat.mul(S, n), E.Le.eq(Nat.add(S, sh), Nat.mul(S, 1n+H), Equal.sym(Nat, Nat.mul(S, 1n+H), Nat.add(S, sh), NL.Nat.mul_succ_r(S, H))), Le.mull(S, 1n+H, n, Le.succ(H, n, el))),
        E.Le.trans(Nat.mul(S, n), Nat.add(x, S), Nat.add(S, x), h2, E.Le.eq(Nat.add(x, S), Nat.add(S, x), NL.Nat.add_comm(x, S))))
      E.Le.trans(Nat.mul(H, S), sh, x, hsh, Le.canl(S, sh, x, h3))
    case False{}:
      +p : Nat = 1n+p1
      +P = RD.Nat.pow2(p)
      +H = RD.Nat.pow2(p1)
      +S = RD.Nat.pow2(s)
      +g = V.g(p, s, n)
      +x = V.x(p, s, n)
      +sh = Nat.mul(S, H)
      +cn = Nat.mul(1n+S, n)
      +fn = E.Small(p1, n, Lt.to_le(n, P, hn))
      +eg = Equal.sym(Nat, g, Nat.add(n, x), V.gx(p1, s, n, fn))
      hsh = E.Le.eq(Nat.mul(H, S), sh, NL.Nat.mul_comm(H, S))
      # n = H: c = C H is representable and c <= C n, so H + S H <= g = n + x
      +c = Nat.mul(1n+S, H)
      +fc = E.G.le(p1, 1n+S, p1, RD.Nat.monus(P, 1n+S), E.Le.wit(1n+S, P, hc))
      h1 = E.Le.trans(c, g, Nat.add(n, x), E.Mono.lo(p1, cn, c, fc, Le.mull(1n+S, H, n, hh)), E.Le.eq(g, Nat.add(n, x), V.gx(p1, s, n, fn)))
      h2 = E.Le.trans(Nat.add(n, sh), c, Nat.add(n, x), Le.addr(n, H, sh, el), h1)
      E.Le.trans(Nat.mul(H, S), sh, x, hsh, Le.canl(n, sh, x, h2))

# 2^(p-1) 2^s <= x, when 1 + 2^s <= 2^p
def V.xlo(+p1: Nat, +s: Nat, +n: Nat, +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+p1)) == True{} : Bool}, hh: E.Le(RD.Nat.pow2(p1), n), hc: E.Le(1n+RD.Nat.pow2(s), RD.Nat.pow2(1n+p1)))
  -> E.Le(Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(s)), V.x(1n+p1, s, n)):
  V.xlo.go(p1, s, n, hn, hh, hc, RD.Nat.lt(RD.Nat.pow2(p1), n), {==})

def Le.anti(+a: Nat, +b: Nat, h1: E.Le(a, b), h2: E.Le(b, a)) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+b2:
      Empty.absurd({0n == 1n+b2 : Nat}, Z.Bool.ft(Equal.sym(Bool, True{}, False{}, h2)))
    case 1n+a2 0n:
      Empty.absurd({1n+a2 == 0n : Nat}, Z.Bool.ft(Equal.sym(Bool, True{}, False{}, h1)))
    case 1n+a2 1n+b2:
      Equal.cong(Nat, Nat, z => 1n+z, a2, b2, Le.anti(a2, b2, h1, h2))

def Lt.succ(+a: Nat) -> {RD.Nat.lt(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+a2:
      Lt.succ(a2)

def Le.dbl(+a: Nat) -> E.Le(a, Nat.double(a)):
  E.Ge.of(Nat.double(a), a, a, Y.Nat.double_add(a))

# above 2^(p-1) 2^s every rounded value is a multiple of 2^s
def Gq(+p: Nat, +c: Nat, +s: Nat) -> Nat:
  Nat.mul(E.Fm.m(p, c), RD.Nat.pow2(RD.Nat.monus(Shf(p, c), s)))

def Grid(+p1: Nat, +c: Nat, +s: Nat, h: E.Le(Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(s)), c)) -> {E.Rn(1n+p1, c) == Nat.mul(Gq(1n+p1, c, s), RD.Nat.pow2(s)) : Nat}:
  +p : Nat = 1n+p1
  +k = Shf(p, c)
  Equal.trans(Nat, E.Rn(p, c), Nat.mul(E.Fm.m(p, c), RD.Nat.pow2(k)), Nat.mul(Gq(p, c, s), RD.Nat.pow2(s)), E.Fm.eq(p, c),
    E.Sh.mul(E.Fm.m(p, c), s, RD.Nat.monus(k, s), k, E.Le.wit(s, k, S4(p1, c, s, h))))

# hi = Ah 2^s
def V.ah(+p: Nat, +s: Nat, +n: Nat) -> Nat:
  RD.Nat.monus(Gq(p, Nat.mul(1n+RD.Nat.pow2(s), n), s), Gq(p, V.x(p, s, n), s))

def V.hi.grid(+p1: Nat, +s: Nat, +n: Nat, +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +hh: {RD.Nat.lt(n, RD.Nat.pow2(p1)) == False{} : Bool}, +hc: {RD.Nat.lt(RD.Nat.pow2(1n+p1), 1n+RD.Nat.pow2(s)) == False{} : Bool})
  -> {V.hi(1n+p1, s, n) == Nat.mul(V.ah(1n+p1, s, n), RD.Nat.pow2(s)) : Nat}:
  +p : Nat = 1n+p1
  +H = RD.Nat.pow2(p1)
  +S = RD.Nat.pow2(s)
  +cn = Nat.mul(1n+S, n)
  +x = V.x(p, s, n)
  +gc = Gq(p, cn, s)
  +gx = Gq(p, x, s)
  hcn = E.Le.trans(Nat.mul(H, S), Nat.mul(S, H), cn, E.Le.eq(Nat.mul(H, S), Nat.mul(S, H), NL.Nat.mul_comm(H, S)),
    E.Le.trans(Nat.mul(S, H), Nat.mul(S, n), cn, Le.mull(S, H, n, hh), E.Ge.of(cn, Nat.mul(S, n), n, NL.Nat.add_comm(n, Nat.mul(S, n)))))
  +e1 = Equal.cong(Nat, Nat, z => RD.Nat.monus(z, E.Rn(p, x)), E.Rn(p, cn), Nat.mul(gc, S), Grid(p1, cn, s, hcn))
  +e2 = Equal.cong(Nat, Nat, z => RD.Nat.monus(Nat.mul(gc, S), z), E.Rn(p, x), Nat.mul(gx, S), Grid(p1, x, s, V.xlo(p1, s, n, hn, hh, hc)))
  Equal.trans(Nat, V.hi(p, s, n), RD.Nat.monus(Nat.mul(gc, S), E.Rn(p, x)), Nat.mul(V.ah(p, s, n), S), e1,
    Equal.trans(Nat, RD.Nat.monus(Nat.mul(gc, S), E.Rn(p, x)), RD.Nat.monus(Nat.mul(gc, S), Nat.mul(gx, S)), Nat.mul(V.ah(p, s, n), S), e2, E.Mo.mul(gc, gx, S)))

def V.lo.go(+p1: Nat, +s: Nat, +n: Nat, +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+p1)) == True{} : Bool}, l: Bool, +el: {RD.Nat.lt(V.x(1n+p1, s, n), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s))) == l : Bool})
  -> E.Le(Nat.double(E.Dist(V.d(1n+p1, s, n), V.x(1n+p1, s, n))), RD.Nat.pow2(s)):
  match l:
    case True{}:
      +x = V.x(1n+p1, s, n)
      E.Le.trans(Nat.double(E.Dist(V.d(1n+p1, s, n), x)), RD.Nat.pow2(Shf(1n+p1, x)), RD.Nat.pow2(s), ErrH(p1, x), Pow2.mono(Shf(1n+p1, x), s, S3(p1, x, s, el)))
    case False{}:
      # x = 2^p 2^s is representable
      +p : Nat = 1n+p1
      +x = V.x(p, s, n)
      +P = RD.Nat.pow2(p)
      +ps = Nat.mul(P, RD.Nat.pow2(s))
      +ex = Le.anti(x, ps, V.xhi(p1, s, n, hn), el)
      +fx = E.Fn.eq(p, x, ps, ex, E.Fn.sc(p, P, s, E.Small(p1, P, E.Lt.irr(P))))
      +e0 = Equal.trans(Nat, E.Dist(E.Rn(p, x), x), E.Dist(x, x), 0n, Equal.cong(Nat, Nat, z => E.Dist(z, x), E.Rn(p, x), x, fx),
        Equal.trans(Nat, E.Dist(x, x), E.Dist(x, Nat.add(x, 0n)), 0n, Equal.cong(Nat, Nat, z => E.Dist(x, z), x, Nat.add(x, 0n), Equal.sym(Nat, Nat.add(x, 0n), x, NL.Nat.add_zero_r(x))), E.Dist.up(x, 0n)))
      E.Le.trans(Nat.double(E.Dist(E.Rn(p, x), x)), 0n, RD.Nat.pow2(s), E.Le.eq(Nat.double(E.Dist(E.Rn(p, x), x)), 0n, Equal.cong(Nat, Nat, z => Nat.double(z), E.Dist(E.Rn(p, x), x), 0n, e0)), BP.Lt.z(RD.Nat.pow2(s)))

# 2 |lo| <= 2^s
def V.lo.le(+p1: Nat, +s: Nat, +n: Nat, +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+p1)) == True{} : Bool}) -> E.Le(Nat.double(E.Dist(V.d(1n+p1, s, n), V.x(1n+p1, s, n))), RD.Nat.pow2(s)):
  V.lo.go(p1, s, n, hn, RD.Nat.lt(V.x(1n+p1, s, n), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s))), {==})

# Ah <= 2^r, when 2^p = 2^r 2^s
def V.ah.le(+p1: Nat, +s: Nat, +r: Nat, +n: Nat, +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +hh: {RD.Nat.lt(n, RD.Nat.pow2(p1)) == False{} : Bool}, +hc: {RD.Nat.lt(RD.Nat.pow2(1n+p1), 1n+RD.Nat.pow2(s)) == False{} : Bool},
  +hp: {RD.Nat.pow2(1n+p1) == Nat.mul(RD.Nat.pow2(r), RD.Nat.pow2(s)) : Nat}) -> E.Le(V.ah(1n+p1, s, n), RD.Nat.pow2(r)):
  +p : Nat = 1n+p1
  +P = RD.Nat.pow2(p)
  +S = RD.Nat.pow2(s)
  +Rr = RD.Nat.pow2(r)
  +x = V.x(p, s, n)
  +d = V.d(p, s, n)
  +hi = V.hi(p, s, n)
  +g = V.g(p, s, n)
  +dx = E.Dist(d, x)
  +fn = E.Small(p1, n, Lt.to_le(n, P, hn))
  +eg : {g == Nat.add(d, hi) : Nat} = Pair.fst({g == Nat.add(d, hi) : Nat}, {E.Rn(p, hi) == hi : Nat}, V.hi.ok(p1, s, n, fn))
  # d + hi = n + x <= n + (d + |d - x|), so hi <= n + |d - x|
  +env : List<&2, Nat> = [n, d, dx]
  +er = R.NatN.eq(env, R.Ad(R.V(0n), R.Ad(R.V(1n), R.V(2n))), R.Ad(R.V(1n), R.Ad(R.V(0n), R.V(2n))), [], [], {==}, Unit{}, {==}, {==})
  h1 = E.Le.trans(Nat.add(d, hi), Nat.add(n, x), Nat.add(d, Nat.add(n, dx)),
    E.Le.eq(Nat.add(d, hi), Nat.add(n, x), Equal.trans(Nat, Nat.add(d, hi), g, Nat.add(n, x), Equal.sym(Nat, g, Nat.add(d, hi), eg), V.gx(p1, s, n, fn))),
    E.Le.trans(Nat.add(n, x), Nat.add(n, Nat.add(d, dx)), Nat.add(d, Nat.add(n, dx)), Le.addl(n, x, Nat.add(d, dx), Dist.ge(d, x)), E.Le.eq(Nat.add(n, Nat.add(d, dx)), Nat.add(d, Nat.add(n, dx)), er)))
  h2 = Le.canl(d, hi, Nat.add(n, dx), h1)
  hdx = E.Le.trans(dx, Nat.double(dx), S, Le.dbl(dx), V.lo.le(p1, s, n, hn))
  # 1 + hi <= 2^p + 2^s = (2^r + 1) 2^s
  h3 = E.Le.trans(1n+hi, 1n+Nat.add(n, dx), Nat.add(P, S), Le.addl(1n, hi, Nat.add(n, dx), h2),
    E.Le.trans(Nat.add(1n+n, dx), Nat.add(P, dx), Nat.add(P, S), Le.addr(1n+n, P, dx, Le.succ(n, P, hn)), Le.addl(P, dx, S, hdx)))
  +ep = Equal.trans(Nat, Nat.add(P, S), Nat.add(Nat.mul(Rr, S), S), Nat.mul(1n+Rr, S), Equal.cong(Nat, Nat, z => Nat.add(z, S), P, Nat.mul(Rr, S), hp), NL.Nat.add_comm(Nat.mul(Rr, S), S))
  +eh = V.hi.grid(p1, s, n, hn, hh, hc)
  +h4 = Equal.trans(Bool, RD.Nat.lt(Nat.mul(V.ah(p, s, n), S), Nat.mul(1n+Rr, S)), RD.Nat.lt(hi, Nat.add(P, S)), True{},
    Equal.sym(Bool, RD.Nat.lt(hi, Nat.add(P, S)), RD.Nat.lt(Nat.mul(V.ah(p, s, n), S), Nat.mul(1n+Rr, S)),
      Equal.trans(Bool, RD.Nat.lt(hi, Nat.add(P, S)), RD.Nat.lt(Nat.mul(V.ah(p, s, n), S), Nat.add(P, S)), RD.Nat.lt(Nat.mul(V.ah(p, s, n), S), Nat.mul(1n+Rr, S)),
        Equal.cong(Nat, Bool, z => RD.Nat.lt(z, Nat.add(P, S)), hi, Nat.mul(V.ah(p, s, n), S), eh),
        Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.mul(V.ah(p, s, n), S), z), Nat.add(P, S), Nat.mul(1n+Rr, S), ep))),
    Lt.le_trans(hi, 1n+hi, Nat.add(P, S), Lt.succ(hi), h3))
  Le.of_lt1(V.ah(p, s, n), Rr, E.Lt.cancel(V.ah(p, s, n), 1n+Rr, S, h4))

# Magnitudes
# ----------

def Pos.le.go(+x: Nat, +y: Nat, +h: {I.Int.pos(I.Int.add(I.IPos{x}, I.Int.neg(I.IPos{y}))) == True{} : Bool}, l: Bool, +el: {RD.Nat.lt(x, y) == l : Bool}) -> E.Le(y, x):
  match l:
    case False{}:
      el
    case True{}:
      +w = RD.Nat.monus(y, 1n+x)
      +ey = Equal.trans(Nat, y, 1n+Nat.add(x, w), Nat.add(x, 1n+w), BP.Lt.wit(x, y)(el), Equal.sym(Nat, Nat.add(x, 1n+w), 1n+Nat.add(x, w), NL.Nat.add_succ_r(x, w)))
      +env : List<&2, I.Int> = [I.IPos{x}, I.IPos{1n+w}]
      +e = Equal.trans(I.Int, I.Int.add(I.IPos{x}, I.Int.neg(I.IPos{y})), I.Int.add(I.IPos{x}, I.Int.neg(I.IPos{Nat.add(x, 1n+w)})), I.Int.neg(I.IPos{1n+w}),
        Equal.cong(Nat, I.Int, z => I.Int.add(I.IPos{x}, I.Int.neg(I.IPos{z})), y, Nat.add(x, 1n+w), ey),
        BP.IntN(env, R.Ad(R.V(0n), R.Ng(R.Ad(R.V(0n), R.V(1n)))), R.Ng(R.V(1n)), [], [], {==}, Unit{}))
      +hf = Equal.trans(Bool, I.Int.pos(I.Int.neg(I.IPos{1n+w})), I.Int.pos(I.Int.add(I.IPos{x}, I.Int.neg(I.IPos{y}))), True{},
        Equal.cong(I.Int, Bool, z => I.Int.pos(z), I.Int.neg(I.IPos{1n+w}), I.Int.add(I.IPos{x}, I.Int.neg(I.IPos{y})), Equal.sym(I.Int, I.Int.add(I.IPos{x}, I.Int.neg(I.IPos{y})), I.Int.neg(I.IPos{1n+w}), e)), h)
      Empty.absurd(E.Le(y, x), Z.Bool.ft(hf))

# x - y >= 0 gives y <= x
def Pos.le(+x: Nat, +y: Nat, +h: {I.Int.pos(I.Int.add(I.IPos{x}, I.Int.neg(I.IPos{y}))) == True{} : Bool}) -> E.Le(y, x):
  Pos.le.go(x, y, h, RD.Nat.lt(x, y), {==})

# |u + v| <= |u| + |v|
def Mag.tri(+u: I.Int, +v: I.Int) -> E.Le(RD.Int.mag(I.Int.add(u, v)), Nat.add(RD.Int.mag(u), RD.Int.mag(v))):
  +mu = RD.Int.mag(u)
  +mv = RD.Int.mag(v)
  +muv = RD.Int.mag(I.Int.add(u, v))
  +e = Y.Int.cong2(I.Int.add(I.Int.abs(u), I.Int.abs(v)), I.IPos{Nat.add(mu, mv)}, I.Int.neg(I.Int.abs(I.Int.add(u, v))), I.Int.neg(I.IPos{muv}),
    Y.Int.cong2(I.Int.abs(u), I.IPos{mu}, I.Int.abs(v), I.IPos{mv}, R.Int.abs_mag(u), R.Int.abs_mag(v)),
    Equal.cong(I.Int, I.Int, z => I.Int.neg(z), I.Int.abs(I.Int.add(u, v)), I.IPos{muv}, R.Int.abs_mag(I.Int.add(u, v))))
  Pos.le(Nat.add(mu, mv), muv, Equal.trans(Bool, I.Int.pos(I.Int.add(I.IPos{Nat.add(mu, mv)}, I.Int.neg(I.IPos{muv}))), I.Int.pos(I.Int.add(I.Int.add(I.Int.abs(u), I.Int.abs(v)), I.Int.neg(I.Int.abs(I.Int.add(u, v))))), True{},
    Equal.cong(I.Int, Bool, z => I.Int.pos(z), I.Int.add(I.IPos{Nat.add(mu, mv)}, I.Int.neg(I.IPos{muv})), I.Int.add(I.Int.add(I.Int.abs(u), I.Int.abs(v)), I.Int.neg(I.Int.abs(I.Int.add(u, v)))),
      Equal.sym(I.Int, I.Int.add(I.Int.add(I.Int.abs(u), I.Int.abs(v)), I.Int.neg(I.Int.abs(I.Int.add(u, v)))), I.Int.add(I.IPos{Nat.add(mu, mv)}, I.Int.neg(I.IPos{muv})), e)),
    Z.Int.tri(u, v)))

def Mag.mul.pn(+a: Nat, +b: Nat) -> {RD.Int.mag(I.Int.mul(I.IPos{a}, I.INeg{b})) == Nat.mul(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+a2):
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.mul(a2, 1n+b), b), Nat.add(b, Nat.mul(a2, 1n+b)), NL.Nat.add_comm(Nat.mul(a2, 1n+b), b))

def Mag.mul.np(+a: Nat, +b: Nat) -> {RD.Int.mag(I.Int.mul(I.INeg{a}, I.IPos{b})) == Nat.mul(1n+a, b) : Nat}:
  match b:
    case 0n:
      Equal.sym(Nat, Nat.mul(1n+a, 0n), 0n, NL.Nat.mul_zero_r(1n+a))
    case 1n+(+b2):
      +env : List<&2, Nat> = [b2, a, 1n]
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.mul(b2, 1n+a), a), Nat.add(b2, Nat.mul(a, 1n+b2)),
        R.NatN.eq2(env, R.Ad(R.Ml(R.V(0n), R.Ad(R.V(2n), R.V(1n))), R.V(1n)), R.Ad(R.V(0n), R.Ml(R.V(1n), R.Ad(R.V(2n), R.V(0n)))), [], [], [R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(0n))), R.Ad(R.V(1n), R.Ng(R.Ml(R.V(1n), R.V(2n))))], {==}, Unit{}, (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(0n), {==}, {==}, NL.Nat.mul_one_r(b2)), (R.NatN.z(env, R.V(1n), R.Ml(R.V(1n), R.V(2n)), {==}, {==}, Equal.sym(Nat, Nat.mul(a, 1n), a, NL.Nat.mul_one_r(a))), Unit{})), {==}, {==}))

def Mag.mul.pp(+a: Nat, +b: Nat) -> {RD.Int.mag(I.Int.mul(I.IPos{a}, I.IPos{b})) == Nat.mul(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+a2):
      {==}

def Mag.mul.nn(+a: Nat, +b: Nat) -> {RD.Int.mag(I.Int.mul(I.INeg{a}, I.INeg{b})) == Nat.mul(1n+a, 1n+b) : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+(+b2):
      {==}

# |u v| = |u| |v|
def Mag.mul(+u: I.Int, +v: I.Int) -> {RD.Int.mag(I.Int.mul(u, v)) == Nat.mul(RD.Int.mag(u), RD.Int.mag(v)) : Nat}:
  match u v:
    case I.IPos{+a} I.IPos{+b}:
      Mag.mul.pp(a, b)
    case I.IPos{+a} I.INeg{+b}:
      Mag.mul.pn(a, b)
    case I.INeg{+a} I.IPos{+b}:
      Mag.mul.np(a, b)
    case I.INeg{+a} I.INeg{+b}:
      Mag.mul.nn(a, b)

# z = w 2^k with |z| <= 2^p 2^k is representable
def Rep(+p1: Nat, +z: I.Int, +w: I.Int, +k: Nat, +hz: {z == D.Int.sh(k, w) : I.Int}, hb: E.Le(RD.Int.mag(z), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k))))
  -> {E.Rn(1n+p1, RD.Int.mag(z)) == RD.Int.mag(z) : Nat}:
  +p : Nat = 1n+p1
  +mw = RD.Int.mag(w)
  +em = Equal.trans(Nat, RD.Int.mag(z), RD.Int.mag(D.Int.sh(k, w)), Nat.mul(mw, RD.Nat.pow2(k)), Equal.cong(I.Int, Nat, x => RD.Int.mag(x), z, D.Int.sh(k, w), hz), E.Sh.mag(k, w))
  hw = E.Le.cancel(mw, RD.Nat.pow2(p), RD.Nat.pow2(k), BP.Pow2.pos(k), E.Le.trans(Nat.mul(mw, RD.Nat.pow2(k)), RD.Int.mag(z), Nat.mul(RD.Nat.pow2(p), RD.Nat.pow2(k)), E.Le.eq(Nat.mul(mw, RD.Nat.pow2(k)), RD.Int.mag(z), Equal.sym(Nat, RD.Int.mag(z), Nat.mul(mw, RD.Nat.pow2(k)), em)), hb))
  E.Fn.eq(p, RD.Int.mag(z), Nat.mul(mw, RD.Nat.pow2(k)), em, E.Fn.sc(p, mw, k, E.Small(p1, mw, hw)))

# |z| = m 2^k: z = sh(k, m with the sign of z)
def Grid.i(+z: I.Int, +m: Nat, +k: Nat, +h: {RD.Int.mag(z) == Nat.mul(m, RD.Nat.pow2(k)) : Nat}) -> {z == D.Int.sh(k, RD.Int.signed(z, m)) : I.Int}:
  Equal.trans(I.Int, z, RD.Int.signed(z, Nat.mul(m, RD.Nat.pow2(k))), D.Int.sh(k, RD.Int.signed(z, m)),
    Equal.trans(I.Int, z, RD.Int.signed(z, RD.Int.mag(z)), RD.Int.signed(z, Nat.mul(m, RD.Nat.pow2(k))), Equal.sym(I.Int, RD.Int.signed(z, RD.Int.mag(z)), z, E.Sgn.self(z)),
      Equal.cong(Nat, I.Int, x => RD.Int.signed(z, x), RD.Int.mag(z), Nat.mul(m, RD.Nat.pow2(k)), h)),
    Equal.sym(I.Int, D.Int.sh(k, RD.Int.signed(z, m)), RD.Int.signed(z, Nat.mul(m, RD.Nat.pow2(k))), E.Sh.signed(k, z, m)))

def Le.mul2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, h1: E.Le(a, b), h2: E.Le(c, d)) -> E.Le(Nat.mul(a, c), Nat.mul(b, d)):
  E.Le.trans(Nat.mul(a, c), Nat.mul(b, c), Nat.mul(b, d), Le.mulr(a, b, c, h1), Le.mull(b, c, d, h2))

# Bounds for Dekker's product
# ---------------------------
# With S = 2^s >= 4 (so S S >= 4 S) every bound below is a polynomial
# identity plus a remainder with nonnegative coefficients.

def Dbl.add(+a: Nat, +b: Nat) -> {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}:
  +env : List<&2, Nat> = [a, b, Nat.double(a), Nat.double(b), Nat.double(Nat.add(a, b))]
  R.NatN.eq2(env, R.V(4n), R.Ad(R.V(2n), R.V(3n)), [], [],
    [R.Ad(R.V(4n), R.Ng(R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(0n), R.V(1n))))), R.Ad(R.Ad(R.V(0n), R.V(0n)), R.Ng(R.V(2n))), R.Ad(R.Ad(R.V(1n), R.V(1n)), R.Ng(R.V(3n)))],
    {==}, Unit{}, (R.NatN.z(env, R.V(4n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(0n), R.V(1n))), {==}, {==}, Y.Nat.double_add(Nat.add(a, b))),
      (R.NatN.z(env, R.Ad(R.V(0n), R.V(0n)), R.V(2n), {==}, {==}, Equal.sym(Nat, Nat.double(a), Nat.add(a, a), Y.Nat.double_add(a))),
        (R.NatN.z(env, R.Ad(R.V(1n), R.V(1n)), R.V(3n), {==}, {==}, Equal.sym(Nat, Nat.double(b), Nat.add(b, b), Y.Nat.double_add(b))), Unit{}))), {==}, {==})

# 2 m <= X + X gives m <= X
def Le.half(+m: Nat, +x: Nat, h: E.Le(Nat.double(m), Nat.add(x, x))) -> E.Le(m, x):
  Equal.trans(Bool, RD.Nat.lt(x, m), RD.Nat.lt(Nat.double(x), Nat.double(m)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.double(x), Nat.double(m)), RD.Nat.lt(x, m), E.Lt.dd(x, m)),
    Equal.trans(Bool, RD.Nat.lt(Nat.double(x), Nat.double(m)), RD.Nat.lt(Nat.add(x, x), Nat.double(m)), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, Nat.double(m)), Nat.double(x), Nat.add(x, x), Y.Nat.double_add(x)), h))

# S^2 + S^3 + S^3 + S^2 <= S^4
def Poly1(+S: Nat, h4: E.Le(Nat.add(Nat.add(Nat.add(S, S), S), S), Nat.mul(S, S)))
  -> E.Le(Nat.add(Nat.mul(S, S), Nat.add(Nat.mul(Nat.mul(S, S), S), Nat.add(Nat.mul(S, Nat.mul(S, S)), Nat.mul(S, S)))), Nat.mul(Nat.mul(S, S), Nat.mul(S, S))):
  +w = RD.Nat.monus(Nat.mul(S, S), Nat.add(Nat.add(Nat.add(S, S), S), S))
  +hw = E.Le.wit(Nat.add(Nat.add(Nat.add(S, S), S), S), Nat.mul(S, S), h4)
  +env : List<&2, Nat> = [S, w]
  E.Ge.of(Nat.mul(Nat.mul(S, S), Nat.mul(S, S)), Nat.add(Nat.mul(S, S), Nat.add(Nat.mul(Nat.mul(S, S), S), Nat.add(Nat.mul(S, Nat.mul(S, S)), Nat.mul(S, S)))),
    R.NatN.eval(env, R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(0n))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(0n), R.V(1n))), R.Ml(R.Ml(R.V(0n), R.V(0n)), R.V(1n))))),
    R.NatN.eq(env, R.Ml(R.Ml(R.V(0n), R.V(0n)), R.Ml(R.V(0n), R.V(0n))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ml(R.Ml(R.V(0n), R.V(0n)), R.V(0n)), R.Ad(R.Ml(R.V(0n), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(0n))))), R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(0n))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(0n), R.V(1n))), R.Ml(R.Ml(R.V(0n), R.V(0n)), R.V(1n))))), [R.Ad(R.Ad(R.Ml(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n))], [R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(1n))))], {==}, (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(1n)), {==}, {==}, hw), Unit{}), {==}, {==}))

# S^2 + S^3 + S^2 <= S^3 + S^3
def Poly2(+S: Nat, h4: E.Le(Nat.add(Nat.add(Nat.add(S, S), S), S), Nat.mul(S, S)))
  -> E.Le(Nat.add(Nat.mul(S, S), Nat.add(Nat.mul(S, Nat.mul(S, S)), Nat.mul(S, S))), Nat.add(Nat.mul(Nat.mul(S, S), S), Nat.mul(Nat.mul(S, S), S))):
  +w = RD.Nat.monus(Nat.mul(S, S), Nat.add(Nat.add(Nat.add(S, S), S), S))
  +hw = E.Le.wit(Nat.add(Nat.add(Nat.add(S, S), S), S), Nat.mul(S, S), h4)
  +env : List<&2, Nat> = [S, w]
  E.Ge.of(Nat.add(Nat.mul(Nat.mul(S, S), S), Nat.mul(Nat.mul(S, S), S)), Nat.add(Nat.mul(S, S), Nat.add(Nat.mul(S, Nat.mul(S, S)), Nat.mul(S, S))),
    R.NatN.eval(env, R.Ad(R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(1n)))),
    R.NatN.eq(env, R.Ad(R.Ml(R.Ml(R.V(0n), R.V(0n)), R.V(0n)), R.Ml(R.Ml(R.V(0n), R.V(0n)), R.V(0n))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ml(R.V(0n), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(0n)))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(1n)))), [R.V(0n)], [R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(1n))))], {==}, (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(1n)), {==}, {==}, hw), Unit{}), {==}, {==}))

# 2|a b| bounds, from 2|err| <= S^2, |ah|, |bh| <= S^2, 2|al|, 2|bl| <= S
def Dbl.mr(+a: Nat, +b: Nat, +c: Nat, +d: Nat, h1: E.Le(a, c), h2: E.Le(Nat.double(b), d)) -> E.Le(Nat.double(Nat.mul(a, b)), Nat.mul(c, d)):
  E.Le.trans(Nat.double(Nat.mul(a, b)), Nat.mul(a, Nat.double(b)), Nat.mul(c, d), E.Le.eq(Nat.double(Nat.mul(a, b)), Nat.mul(a, Nat.double(b)), Equal.sym(Nat, Nat.mul(a, Nat.double(b)), Nat.double(Nat.mul(a, b)), R.Nat.mul_double(a, b))),
    Le.mul2(a, c, Nat.double(b), d, h1, h2))

def Dbl.ml(+a: Nat, +b: Nat, +c: Nat, +d: Nat, h1: E.Le(Nat.double(a), c), h2: E.Le(b, d)) -> E.Le(Nat.double(Nat.mul(a, b)), Nat.mul(c, d)):
  E.Le.trans(Nat.double(Nat.mul(a, b)), Nat.mul(Nat.double(a), b), Nat.mul(c, d), E.Le.eq(Nat.double(Nat.mul(a, b)), Nat.mul(Nat.double(a), b), Equal.sym(Nat, Nat.mul(Nat.double(a), b), Nat.double(Nat.mul(a, b)), BP.Mul.dbl_l(a, b))),
    Le.mul2(Nat.double(a), c, b, d, h1, h2))

def Le.of_dbl(+a: Nat, +c: Nat, h: E.Le(Nat.double(a), c)) -> E.Le(a, c):
  E.Le.trans(a, Nat.double(a), c, Le.dbl(a), h)

def B1(+S: Nat, +ee: Nat, +ma: Nat, +mb: Nat, +la: Nat, +lb: Nat, he: E.Le(Nat.double(ee), Nat.mul(S, S)), hma: E.Le(ma, Nat.mul(S, S)), hmb: E.Le(mb, Nat.mul(S, S)),
  +hla: {RD.Nat.lt(S, Nat.double(la)) == False{} : Bool}, +hlb: {RD.Nat.lt(S, Nat.double(lb)) == False{} : Bool}, h4: E.Le(Nat.add(Nat.add(Nat.add(S, S), S), S), Nat.mul(S, S)))
  -> E.Le(Nat.double(Nat.add(ee, Nat.add(Nat.mul(ma, lb), Nat.add(Nat.mul(la, mb), Nat.mul(la, lb))))), Nat.mul(Nat.mul(S, S), Nat.mul(S, S))):
  +t2 = Nat.mul(ma, lb)
  +t3 = Nat.mul(la, mb)
  +t4 = Nat.mul(la, lb)
  +ss = Nat.mul(S, S)
  +ed = Equal.trans(Nat, Nat.double(Nat.add(ee, Nat.add(t2, Nat.add(t3, t4)))), Nat.add(Nat.double(ee), Nat.double(Nat.add(t2, Nat.add(t3, t4)))), Nat.add(Nat.double(ee), Nat.add(Nat.double(t2), Nat.add(Nat.double(t3), Nat.double(t4)))),
    Dbl.add(ee, Nat.add(t2, Nat.add(t3, t4))),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.double(ee), z), Nat.double(Nat.add(t2, Nat.add(t3, t4))), Nat.add(Nat.double(t2), Nat.add(Nat.double(t3), Nat.double(t4))),
      Equal.trans(Nat, Nat.double(Nat.add(t2, Nat.add(t3, t4))), Nat.add(Nat.double(t2), Nat.double(Nat.add(t3, t4))), Nat.add(Nat.double(t2), Nat.add(Nat.double(t3), Nat.double(t4))), Dbl.add(t2, Nat.add(t3, t4)),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.double(t2), z), Nat.double(Nat.add(t3, t4)), Nat.add(Nat.double(t3), Nat.double(t4)), Dbl.add(t3, t4)))))
  hs = Le.add2(Nat.double(ee), ss, Nat.add(Nat.double(t2), Nat.add(Nat.double(t3), Nat.double(t4))), Nat.add(Nat.mul(ss, S), Nat.add(Nat.mul(S, ss), ss)), he,
    Le.add2(Nat.double(t2), Nat.mul(ss, S), Nat.add(Nat.double(t3), Nat.double(t4)), Nat.add(Nat.mul(S, ss), ss), Dbl.mr(ma, lb, ss, S, hma, hlb),
      Le.add2(Nat.double(t3), Nat.mul(S, ss), Nat.double(t4), ss, Dbl.ml(la, mb, S, ss, hla, hmb), Dbl.ml(la, lb, S, S, hla, Le.of_dbl(lb, S, hlb)))))
  E.Le.trans(Nat.double(Nat.add(ee, Nat.add(t2, Nat.add(t3, t4)))), Nat.add(ss, Nat.add(Nat.mul(ss, S), Nat.add(Nat.mul(S, ss), ss))), Nat.mul(ss, ss),
    E.Le.trans(Nat.double(Nat.add(ee, Nat.add(t2, Nat.add(t3, t4)))), Nat.add(Nat.double(ee), Nat.add(Nat.double(t2), Nat.add(Nat.double(t3), Nat.double(t4)))), Nat.add(ss, Nat.add(Nat.mul(ss, S), Nat.add(Nat.mul(S, ss), ss))),
      E.Le.eq(Nat.double(Nat.add(ee, Nat.add(t2, Nat.add(t3, t4)))), Nat.add(Nat.double(ee), Nat.add(Nat.double(t2), Nat.add(Nat.double(t3), Nat.double(t4)))), ed), hs),
    Poly1(S, h4))

def B2(+S: Nat, +ee: Nat, +mb: Nat, +la: Nat, +lb: Nat, he: E.Le(Nat.double(ee), Nat.mul(S, S)), hmb: E.Le(mb, Nat.mul(S, S)),
  +hla: {RD.Nat.lt(S, Nat.double(la)) == False{} : Bool}, +hlb: {RD.Nat.lt(S, Nat.double(lb)) == False{} : Bool}, h4: E.Le(Nat.add(Nat.add(Nat.add(S, S), S), S), Nat.mul(S, S)))
  -> E.Le(Nat.double(Nat.add(ee, Nat.add(Nat.mul(la, mb), Nat.mul(la, lb)))), Nat.add(Nat.mul(Nat.mul(S, S), S), Nat.mul(Nat.mul(S, S), S))):
  +t3 = Nat.mul(la, mb)
  +t4 = Nat.mul(la, lb)
  +ss = Nat.mul(S, S)
  +ed = Equal.trans(Nat, Nat.double(Nat.add(ee, Nat.add(t3, t4))), Nat.add(Nat.double(ee), Nat.double(Nat.add(t3, t4))), Nat.add(Nat.double(ee), Nat.add(Nat.double(t3), Nat.double(t4))),
    Dbl.add(ee, Nat.add(t3, t4)), Equal.cong(Nat, Nat, z => Nat.add(Nat.double(ee), z), Nat.double(Nat.add(t3, t4)), Nat.add(Nat.double(t3), Nat.double(t4)), Dbl.add(t3, t4)))
  hs = Le.add2(Nat.double(ee), ss, Nat.add(Nat.double(t3), Nat.double(t4)), Nat.add(Nat.mul(S, ss), ss), he,
    Le.add2(Nat.double(t3), Nat.mul(S, ss), Nat.double(t4), ss, Dbl.ml(la, mb, S, ss, hla, hmb), Dbl.ml(la, lb, S, S, hla, Le.of_dbl(lb, S, hlb))))
  E.Le.trans(Nat.double(Nat.add(ee, Nat.add(t3, t4))), Nat.add(ss, Nat.add(Nat.mul(S, ss), ss)), Nat.add(Nat.mul(ss, S), Nat.mul(ss, S)),
    E.Le.trans(Nat.double(Nat.add(ee, Nat.add(t3, t4))), Nat.add(Nat.double(ee), Nat.add(Nat.double(t3), Nat.double(t4))), Nat.add(ss, Nat.add(Nat.mul(S, ss), ss)),
      E.Le.eq(Nat.double(Nat.add(ee, Nat.add(t3, t4))), Nat.add(Nat.double(ee), Nat.add(Nat.double(t3), Nat.double(t4))), ed), hs),
    Poly2(S, h4))

def B3(+S: Nat, +ee: Nat, +la: Nat, +lb: Nat, he: E.Le(Nat.double(ee), Nat.mul(S, S)), +hla: {RD.Nat.lt(S, Nat.double(la)) == False{} : Bool}, +hlb: {RD.Nat.lt(S, Nat.double(lb)) == False{} : Bool})
  -> E.Le(Nat.double(Nat.add(ee, Nat.mul(la, lb))), Nat.add(Nat.mul(S, S), Nat.mul(S, S))):
  +t4 = Nat.mul(la, lb)
  E.Le.trans(Nat.double(Nat.add(ee, t4)), Nat.add(Nat.double(ee), Nat.double(t4)), Nat.add(Nat.mul(S, S), Nat.mul(S, S)), E.Le.eq(Nat.double(Nat.add(ee, t4)), Nat.add(Nat.double(ee), Nat.double(t4)), Dbl.add(ee, t4)),
    Le.add2(Nat.double(ee), Nat.mul(S, S), Nat.double(t4), Nat.mul(S, S), he, Dbl.ml(la, lb, S, S, hla, Le.of_dbl(lb, S, hlb))))

# Dekker's product
# ----------------
# p = 2s. For a, b in [2^(p-1), 2^p) split as a = ah + al, b = bh + bl
# (ah, bh multiples of 2^s at most 2^p, 2|al|, 2|bl| <= 2^s), and
# pi = R(a b) with error err = a b - pi:
#   e1 = ah bh - pi        = err - ah bl - al bh - al bl  (grid 2^(p-1))
#   e2 = e1 + ah bl        = err - al bh - al bl          (grid 2^s)
#   e3 = e2 + al bh        = err - al bl                  (|e3| <= 2^p)
#   e  = e3 + al bl        = err
# each rounding is exact, so pi + e = a b.

def Dk.e1(+p: Nat, +ah: I.Int, +bh: I.Int, +pi: I.Int) -> I.Int:
  E.RNi(p, I.Int.add(E.RNi(p, I.Int.mul(ah, bh)), I.Int.neg(pi)))

def Dk.e2(+p: Nat, +ah: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int) -> I.Int:
  E.RNi(p, I.Int.add(Dk.e1(p, ah, bh, pi), E.RNi(p, I.Int.mul(ah, bl))))

def Dk.e3(+p: Nat, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int) -> I.Int:
  E.RNi(p, I.Int.add(Dk.e2(p, ah, bh, bl, pi), E.RNi(p, I.Int.mul(al, bh))))

def Dk.e(+p: Nat, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int) -> I.Int:
  E.RNi(p, I.Int.add(Dk.e3(p, ah, al, bh, bl, pi), E.RNi(p, I.Int.mul(al, bl))))

# 2^p = 2^s 2^s for p = 2s
def Pw.P(+s1: Nat) -> {RD.Nat.pow2(1n+Nat.add(1n+s1, s1)) == Nat.mul(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)) : Nat}:
  Equal.trans(Nat, RD.Nat.pow2(1n+Nat.add(1n+s1, s1)), RD.Nat.pow2(Nat.add(1n+s1, 1n+s1)), Nat.mul(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)),
    Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), 1n+Nat.add(1n+s1, s1), Nat.add(1n+s1, 1n+s1), Equal.sym(Nat, Nat.add(1n+s1, 1n+s1), 1n+Nat.add(1n+s1, s1), NL.Nat.add_succ_r(1n+s1, s1))),
    BP.Pow2.add(1n+s1, 1n+s1))

# |z| = m 2^k with m <= 2^p: rounding z is exact
def Px(+p1: Nat, +z: I.Int, +m: Nat, +k: Nat, +hm: {RD.Int.mag(z) == Nat.mul(m, RD.Nat.pow2(k)) : Nat}, hb: E.Le(m, RD.Nat.pow2(1n+p1))) -> {E.RNi(1n+p1, z) == z : I.Int}:
  E.RNi.exact(1n+p1, z, E.Fn.eq(1n+p1, RD.Int.mag(z), Nat.mul(m, RD.Nat.pow2(k)), hm, E.Fn.sc(1n+p1, m, k, E.Small(p1, m, hb))))

def Pxs(+p1: Nat, +z: I.Int, hb: E.Le(RD.Int.mag(z), RD.Nat.pow2(1n+p1))) -> {E.RNi(1n+p1, z) == z : I.Int}:
  E.RNi.exact(1n+p1, z, E.Small(p1, RD.Int.mag(z), hb))

# |x y + v| <= |x| |y| + k and |-(x y) + v| <= |x| |y| + k, given |v| <= k
def Tri.m(+x: I.Int, +y: I.Int, +v: I.Int, +k: Nat, h: E.Le(RD.Int.mag(v), k)) -> E.Le(RD.Int.mag(I.Int.add(I.Int.mul(x, y), v)), Nat.add(Nat.mul(RD.Int.mag(x), RD.Int.mag(y)), k)):
  E.Le.trans(RD.Int.mag(I.Int.add(I.Int.mul(x, y), v)), Nat.add(RD.Int.mag(I.Int.mul(x, y)), RD.Int.mag(v)), Nat.add(Nat.mul(RD.Int.mag(x), RD.Int.mag(y)), k), Mag.tri(I.Int.mul(x, y), v),
    Le.add2(RD.Int.mag(I.Int.mul(x, y)), Nat.mul(RD.Int.mag(x), RD.Int.mag(y)), RD.Int.mag(v), k, E.Le.eq(RD.Int.mag(I.Int.mul(x, y)), Nat.mul(RD.Int.mag(x), RD.Int.mag(y)), Mag.mul(x, y)), h))

def Tri.nm(+x: I.Int, +y: I.Int, +v: I.Int, +k: Nat, h: E.Le(RD.Int.mag(v), k)) -> E.Le(RD.Int.mag(I.Int.add(I.Int.neg(I.Int.mul(x, y)), v)), Nat.add(Nat.mul(RD.Int.mag(x), RD.Int.mag(y)), k)):
  +xy = I.Int.mul(x, y)
  E.Le.trans(RD.Int.mag(I.Int.add(I.Int.neg(xy), v)), Nat.add(RD.Int.mag(I.Int.neg(xy)), RD.Int.mag(v)), Nat.add(Nat.mul(RD.Int.mag(x), RD.Int.mag(y)), k), Mag.tri(I.Int.neg(xy), v),
    Le.add2(RD.Int.mag(I.Int.neg(xy)), Nat.mul(RD.Int.mag(x), RD.Int.mag(y)), RD.Int.mag(v), k,
      E.Le.eq(RD.Int.mag(I.Int.neg(xy)), Nat.mul(RD.Int.mag(x), RD.Int.mag(y)), Equal.trans(Nat, RD.Int.mag(I.Int.neg(xy)), RD.Int.mag(xy), Nat.mul(RD.Int.mag(x), RD.Int.mag(y)), E.Mag.neg(xy), Mag.mul(x, y))), h))

def Tri.e(+u: I.Int, +v: I.Int, +k: Nat, h: E.Le(RD.Int.mag(v), k)) -> E.Le(RD.Int.mag(I.Int.add(u, v)), Nat.add(RD.Int.mag(u), k)):
  E.Le.trans(RD.Int.mag(I.Int.add(u, v)), Nat.add(RD.Int.mag(u), RD.Int.mag(v)), Nat.add(RD.Int.mag(u), k), Mag.tri(u, v), Le.addl(RD.Int.mag(u), RD.Int.mag(v), k, h))

def Mag.negm(+x: I.Int, +y: I.Int) -> E.Le(RD.Int.mag(I.Int.neg(I.Int.mul(x, y))), Nat.mul(RD.Int.mag(x), RD.Int.mag(y))):
  E.Le.eq(RD.Int.mag(I.Int.neg(I.Int.mul(x, y))), Nat.mul(RD.Int.mag(x), RD.Int.mag(y)), Equal.trans(Nat, RD.Int.mag(I.Int.neg(I.Int.mul(x, y))), RD.Int.mag(I.Int.mul(x, y)), Nat.mul(RD.Int.mag(x), RD.Int.mag(y)), E.Mag.neg(I.Int.mul(x, y)), Mag.mul(x, y)))

# grids add
def Sh.diff(+k: Nat, +x: I.Int, +y: I.Int) -> {I.Int.add(D.Int.sh(k, x), I.Int.neg(D.Int.sh(k, y))) == D.Int.sh(k, I.Int.add(x, I.Int.neg(y))) : I.Int}:
  Equal.trans(I.Int, I.Int.add(D.Int.sh(k, x), I.Int.neg(D.Int.sh(k, y))), I.Int.add(D.Int.sh(k, x), D.Int.sh(k, I.Int.neg(y))), D.Int.sh(k, I.Int.add(x, I.Int.neg(y))),
    Equal.cong(I.Int, I.Int, z => I.Int.add(D.Int.sh(k, x), z), I.Int.neg(D.Int.sh(k, y)), D.Int.sh(k, I.Int.neg(y)), Equal.sym(I.Int, D.Int.sh(k, I.Int.neg(y)), I.Int.neg(D.Int.sh(k, y)), Y.Int.sh_neg(k, y))),
    Equal.sym(I.Int, D.Int.sh(k, I.Int.add(x, I.Int.neg(y))), I.Int.add(D.Int.sh(k, x), D.Int.sh(k, I.Int.neg(y))), Y.Int.sh_add(k, x, I.Int.neg(y))))

# the products are exact; e1 = ah bh - pi exactly, on the grid 2^(p-1)
def Dk.c1(+s1: Nat, +a: I.Int, +b: I.Int, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int, +A: Nat, +B: Nat, +Q: Nat,
  +hal: {al == I.Int.add(a, I.Int.neg(ah)) : I.Int}, +hbl: {bl == I.Int.add(b, I.Int.neg(bh)) : I.Int},
  +hma: {RD.Int.mag(ah) == Nat.mul(A, RD.Nat.pow2(1n+s1)) : Nat}, +hmb: {RD.Int.mag(bh) == Nat.mul(B, RD.Nat.pow2(1n+s1)) : Nat},
  +hA: {RD.Nat.lt(RD.Nat.pow2(1n+s1), A) == False{} : Bool}, +hB: {RD.Nat.lt(RD.Nat.pow2(1n+s1), B) == False{} : Bool},
  +hla: {RD.Nat.lt(RD.Nat.pow2(1n+s1), Nat.double(RD.Int.mag(al))) == False{} : Bool}, +hlb: {RD.Nat.lt(RD.Nat.pow2(1n+s1), Nat.double(RD.Int.mag(bl))) == False{} : Bool},
  +hpi: {RD.Int.mag(pi) == Nat.mul(Q, RD.Nat.pow2(Nat.add(1n+s1, s1))) : Nat}, +herr: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)), Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))))) == False{} : Bool},
  +h4: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)), Nat.add(Nat.add(Nat.add(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)), RD.Nat.pow2(1n+s1)), RD.Nat.pow2(1n+s1))) == False{} : Bool})
  -> {Dk.e1(1n+Nat.add(1n+s1, s1), ah, bh, pi) == I.Int.add(I.Int.mul(ah, bh), I.Int.neg(pi)) : I.Int} & {I.Int.add(I.Int.mul(ah, bh), I.Int.neg(pi)) == D.Int.sh(Nat.add(1n+s1, s1), I.Int.add(RD.Int.signed(I.Int.mul(ah, bh), Nat.double(Nat.mul(A, B))), I.Int.neg(RD.Int.signed(pi, Q)))) : I.Int}:
  +s : Nat = 1n+s1
  +p1 = Nat.add(s, s1)
  +p : Nat = 1n+p1
  +S = RD.Nat.pow2(s)
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(p)
  +ss = Nat.mul(S, S)
  +hP : {P == ss : Nat} = Pw.P(s1)
  +ma = RD.Int.mag(ah)
  +mb = RD.Int.mag(bh)
  +la = RD.Int.mag(al)
  +lb = RD.Int.mag(bl)
  +err = I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))
  +ee = RD.Int.mag(err)
  +P1 = I.Int.mul(ah, bh)
  +P2 = I.Int.mul(ah, bl)
  +P3 = I.Int.mul(al, bh)
  +P4 = I.Int.mul(al, bl)
  +env : List<&2, I.Int> = [a, b, ah, al, bh, bl, pi]
  +hma2 : {RD.Nat.lt(ss, ma) == False{} : Bool} = E.Le.trans(ma, Nat.mul(A, S), ss, E.Le.eq(ma, Nat.mul(A, S), hma), Le.mulr(A, S, S, hA))
  +hmb2 : {RD.Nat.lt(ss, mb) == False{} : Bool} = E.Le.trans(mb, Nat.mul(B, S), ss, E.Le.eq(mb, Nat.mul(B, S), hmb), Le.mulr(B, S, S, hB))
  +hlb1 : {RD.Nat.lt(S, lb) == False{} : Bool} = Le.of_dbl(lb, S, hlb)
  +hla1 : {RD.Nat.lt(S, la) == False{} : Bool} = Le.of_dbl(la, S, hla)
  +hsp : {RD.Nat.lt(P, ss) == False{} : Bool} = E.Le.eq(ss, P, Equal.sym(Nat, P, ss, hP))
  +ab = Nat.mul(A, B)
  +em1 : {RD.Int.mag(P1) == Nat.mul(ab, P) : Nat} = Equal.trans(Nat, RD.Int.mag(P1), Nat.mul(ma, mb), Nat.mul(ab, P), Mag.mul(ah, bh),
    Equal.trans(Nat, Nat.mul(ma, mb), Nat.mul(Nat.mul(A, S), Nat.mul(B, S)), Nat.mul(ab, P),
      Equal.trans(Nat, Nat.mul(ma, mb), Nat.mul(Nat.mul(A, S), mb), Nat.mul(Nat.mul(A, S), Nat.mul(B, S)), Equal.cong(Nat, Nat, z => Nat.mul(z, mb), ma, Nat.mul(A, S), hma), Equal.cong(Nat, Nat, z => Nat.mul(Nat.mul(A, S), z), mb, Nat.mul(B, S), hmb)),
      Equal.trans(Nat, Nat.mul(Nat.mul(A, S), Nat.mul(B, S)), Nat.mul(ab, ss), Nat.mul(ab, P),
        R.NatN.eq([A, B, S], R.Ml(R.Ml(R.V(0n), R.V(2n)), R.Ml(R.V(1n), R.V(2n))), R.Ml(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(2n), R.V(2n))), [], [], {==}, Unit{}, {==}, {==}),
        Equal.cong(Nat, Nat, z => Nat.mul(ab, z), ss, P, Equal.sym(Nat, P, ss, hP)))))
  +x1 = Px(p1, P1, ab, p, em1, E.Le.trans(ab, ss, P, Le.mul2(A, S, B, S, hA, hB), hsp))
  +emh : {RD.Int.mag(P1) == Nat.mul(Nat.double(ab), H) : Nat} = Equal.trans(Nat, RD.Int.mag(P1), Nat.mul(ab, P), Nat.mul(Nat.double(ab), H), em1,
    Equal.trans(Nat, Nat.mul(ab, P), Nat.double(Nat.mul(ab, H)), Nat.mul(Nat.double(ab), H), R.Nat.mul_double(ab, H), Equal.sym(Nat, Nat.mul(Nat.double(ab), H), Nat.double(Nat.mul(ab, H)), BP.Mul.dbl_l(ab, H))))
  +x1g = RD.Int.signed(P1, Nat.double(ab))
  +xq = RD.Int.signed(pi, Q)
  +z1 = I.Int.add(P1, I.Int.neg(pi))
  +gz = Equal.trans(I.Int, z1, I.Int.add(D.Int.sh(p1, x1g), I.Int.neg(D.Int.sh(p1, xq))), D.Int.sh(p1, I.Int.add(x1g, I.Int.neg(xq))),
    Y.Int.cong2(P1, D.Int.sh(p1, x1g), I.Int.neg(pi), I.Int.neg(D.Int.sh(p1, xq)), Grid.i(P1, Nat.double(ab), p1, emh), Equal.cong(I.Int, I.Int, z => I.Int.neg(z), pi, D.Int.sh(p1, xq), Grid.i(pi, Q, p1, hpi))),
    Sh.diff(p1, x1g, xq))
  # |e1| <= |err| + |ah bl| + |al bh| + |al bl| <= 2^p 2^(p-1)
  +r1 = I.Int.add(err, I.Int.add(I.Int.neg(P2), I.Int.add(I.Int.neg(P3), I.Int.neg(P4))))
  +i1 : {z1 == r1 : I.Int} = BP.IntN(env, R.Ad(R.Ml(R.V(2n), R.V(4n)), R.Ng(R.V(6n))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ng(R.V(6n))), R.Ad(R.Ng(R.Ml(R.V(2n), R.V(5n))), R.Ad(R.Ng(R.Ml(R.V(3n), R.V(4n))), R.Ng(R.Ml(R.V(3n), R.V(5n)))))), [R.Ad(R.V(4n), R.V(5n)), R.V(0n)], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(0n), R.Ng(R.V(2n))))), R.Ad(R.V(5n), R.Ng(R.Ad(R.V(1n), R.Ng(R.V(4n)))))], {==}, (IntZ(env, R.V(3n), R.Ad(R.V(0n), R.Ng(R.V(2n))), hal), (IntZ(env, R.V(5n), R.Ad(R.V(1n), R.Ng(R.V(4n))), hbl), Unit{})))
  +bd = Nat.add(ee, Nat.add(Nat.mul(ma, lb), Nat.add(Nat.mul(la, mb), Nat.mul(la, lb))))
  hm = E.Le.trans(RD.Int.mag(z1), RD.Int.mag(r1), bd, E.Le.eq(RD.Int.mag(z1), RD.Int.mag(r1), Equal.cong(I.Int, Nat, z => RD.Int.mag(z), z1, r1, i1)),
    Tri.e(err, I.Int.add(I.Int.neg(P2), I.Int.add(I.Int.neg(P3), I.Int.neg(P4))), Nat.add(Nat.mul(ma, lb), Nat.add(Nat.mul(la, mb), Nat.mul(la, lb))),
      Tri.nm(ah, bl, I.Int.add(I.Int.neg(P3), I.Int.neg(P4)), Nat.add(Nat.mul(la, mb), Nat.mul(la, lb)), Tri.nm(al, bh, I.Int.neg(P4), Nat.mul(la, lb), Mag.negm(al, bl)))))
  +ph = Nat.mul(P, H)
  +eq4 : {Nat.mul(ss, ss) == Nat.add(ph, ph) : Nat} = Equal.trans(Nat, Nat.mul(ss, ss), Nat.mul(P, P), Nat.add(ph, ph),
    Equal.trans(Nat, Nat.mul(ss, ss), Nat.mul(P, ss), Nat.mul(P, P), Equal.cong(Nat, Nat, z => Nat.mul(z, ss), ss, P, Equal.sym(Nat, P, ss, hP)), Equal.cong(Nat, Nat, z => Nat.mul(P, z), ss, P, Equal.sym(Nat, P, ss, hP))),
    Equal.trans(Nat, Nat.mul(P, P), Nat.double(ph), Nat.add(ph, ph), R.Nat.mul_double(P, H), Y.Nat.double_add(ph)))
  hzb = Le.half(RD.Int.mag(z1), ph, E.Le.trans(Nat.double(RD.Int.mag(z1)), Nat.mul(ss, ss), Nat.add(ph, ph),
    E.Le.trans(Nat.double(RD.Int.mag(z1)), Nat.double(bd), Nat.mul(ss, ss), E.Le.dd(RD.Int.mag(z1), bd, hm), B1(S, ee, ma, mb, la, lb, herr, hma2, hmb2, hla, hlb, h4)),
    E.Le.eq(Nat.mul(ss, ss), Nat.add(ph, ph), eq4)))
  +ez = E.RNi.exact(p, z1, Rep(p1, z1, I.Int.add(x1g, I.Int.neg(xq)), p1, gz, hzb))
  +ee1 = Equal.trans(I.Int, Dk.e1(p, ah, bh, pi), E.RNi(p, z1), z1, Equal.cong(I.Int, I.Int, z => E.RNi(p, I.Int.add(z, I.Int.neg(pi))), E.RNi(p, P1), P1, x1), ez)
  (ee1, gz)

# e2 = e1 + ah bl exactly, on the grid 2^s
def Dk.c2(+s1: Nat, +a: I.Int, +b: I.Int, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int, +A: Nat, +B: Nat, +Q: Nat,
  +hal: {al == I.Int.add(a, I.Int.neg(ah)) : I.Int}, +hbl: {bl == I.Int.add(b, I.Int.neg(bh)) : I.Int},
  +hma: {RD.Int.mag(ah) == Nat.mul(A, RD.Nat.pow2(1n+s1)) : Nat}, +hmb: {RD.Int.mag(bh) == Nat.mul(B, RD.Nat.pow2(1n+s1)) : Nat},
  +hA: {RD.Nat.lt(RD.Nat.pow2(1n+s1), A) == False{} : Bool}, +hB: {RD.Nat.lt(RD.Nat.pow2(1n+s1), B) == False{} : Bool},
  +hla: {RD.Nat.lt(RD.Nat.pow2(1n+s1), Nat.double(RD.Int.mag(al))) == False{} : Bool}, +hlb: {RD.Nat.lt(RD.Nat.pow2(1n+s1), Nat.double(RD.Int.mag(bl))) == False{} : Bool},
  +hpi: {RD.Int.mag(pi) == Nat.mul(Q, RD.Nat.pow2(Nat.add(1n+s1, s1))) : Nat}, +herr: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)), Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))))) == False{} : Bool},
  +h4: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)), Nat.add(Nat.add(Nat.add(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)), RD.Nat.pow2(1n+s1)), RD.Nat.pow2(1n+s1))) == False{} : Bool})
  -> {Dk.e2(1n+Nat.add(1n+s1, s1), ah, bh, bl, pi) == I.Int.add(I.Int.add(I.Int.mul(ah, bh), I.Int.neg(pi)), I.Int.mul(ah, bl)) : I.Int}:
  +s : Nat = 1n+s1
  +p1 = Nat.add(s, s1)
  +p : Nat = 1n+p1
  +S = RD.Nat.pow2(s)
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(p)
  +ss = Nat.mul(S, S)
  +hP : {P == ss : Nat} = Pw.P(s1)
  +ma = RD.Int.mag(ah)
  +mb = RD.Int.mag(bh)
  +la = RD.Int.mag(al)
  +lb = RD.Int.mag(bl)
  +err = I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))
  +ee = RD.Int.mag(err)
  +P1 = I.Int.mul(ah, bh)
  +P2 = I.Int.mul(ah, bl)
  +P3 = I.Int.mul(al, bh)
  +P4 = I.Int.mul(al, bl)
  +env : List<&2, I.Int> = [a, b, ah, al, bh, bl, pi]
  +hma2 : {RD.Nat.lt(ss, ma) == False{} : Bool} = E.Le.trans(ma, Nat.mul(A, S), ss, E.Le.eq(ma, Nat.mul(A, S), hma), Le.mulr(A, S, S, hA))
  +hmb2 : {RD.Nat.lt(ss, mb) == False{} : Bool} = E.Le.trans(mb, Nat.mul(B, S), ss, E.Le.eq(mb, Nat.mul(B, S), hmb), Le.mulr(B, S, S, hB))
  +hlb1 : {RD.Nat.lt(S, lb) == False{} : Bool} = Le.of_dbl(lb, S, hlb)
  +hla1 : {RD.Nat.lt(S, la) == False{} : Bool} = Le.of_dbl(la, S, hla)
  +hsp : {RD.Nat.lt(P, ss) == False{} : Bool} = E.Le.eq(ss, P, Equal.sym(Nat, P, ss, hP))
  +z1 = I.Int.add(P1, I.Int.neg(pi))
  +w1 = I.Int.add(RD.Int.signed(I.Int.mul(ah, bh), Nat.double(Nat.mul(A, B))), I.Int.neg(RD.Int.signed(pi, Q)))
  +ec1 : {Dk.e1(p, ah, bh, pi) == z1 : I.Int} = Pair.fst({Dk.e1(p, ah, bh, pi) == z1 : I.Int}, {z1 == D.Int.sh(p1, w1) : I.Int}, Dk.c1(s1, a, b, ah, al, bh, bl, pi, A, B, Q, hal, hbl, hma, hmb, hA, hB, hla, hlb, hpi, herr, h4))
  +gz1 : {z1 == D.Int.sh(p1, w1) : I.Int} = Pair.snd({Dk.e1(p, ah, bh, pi) == z1 : I.Int}, {z1 == D.Int.sh(p1, w1) : I.Int}, Dk.c1(s1, a, b, ah, al, bh, bl, pi, A, B, Q, hal, hbl, hma, hmb, hA, hB, hla, hlb, hpi, herr, h4))
  +al2 = Nat.mul(A, lb)
  +em2 : {RD.Int.mag(P2) == Nat.mul(al2, S) : Nat} = Equal.trans(Nat, RD.Int.mag(P2), Nat.mul(ma, lb), Nat.mul(al2, S), Mag.mul(ah, bl),
    Equal.trans(Nat, Nat.mul(ma, lb), Nat.mul(Nat.mul(A, S), lb), Nat.mul(al2, S), Equal.cong(Nat, Nat, z => Nat.mul(z, lb), ma, Nat.mul(A, S), hma),
      R.NatN.eq([A, S, lb], R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(2n)), R.Ml(R.Ml(R.V(0n), R.V(2n)), R.V(1n)), [], [], {==}, Unit{}, {==}, {==})))
  +x2 = Px(p1, P2, al2, s, em2, E.Le.trans(al2, ss, P, Le.mul2(A, S, lb, S, hA, hlb1), hsp))
  +x2g = RD.Int.signed(P2, al2)
  +z2 = I.Int.add(z1, P2)
  +gz = Equal.trans(I.Int, z2, I.Int.add(D.Int.sh(s, D.Int.sh(s1, w1)), D.Int.sh(s, x2g)), D.Int.sh(s, I.Int.add(D.Int.sh(s1, w1), x2g)),
    Y.Int.cong2(z1, D.Int.sh(s, D.Int.sh(s1, w1)), P2, D.Int.sh(s, x2g),
      Equal.trans(I.Int, z1, D.Int.sh(p1, w1), D.Int.sh(s, D.Int.sh(s1, w1)), gz1, Equal.sym(I.Int, D.Int.sh(s, D.Int.sh(s1, w1)), D.Int.sh(p1, w1), Y.Int.sh_sh(s, s1, w1))),
      Grid.i(P2, al2, s, em2)),
    Equal.sym(I.Int, D.Int.sh(s, I.Int.add(D.Int.sh(s1, w1), x2g)), I.Int.add(D.Int.sh(s, D.Int.sh(s1, w1)), D.Int.sh(s, x2g)), Y.Int.sh_add(s, D.Int.sh(s1, w1), x2g)))
  # |e2| <= |err| + |al bh| + |al bl| <= 2^p 2^s
  +r2 = I.Int.add(err, I.Int.add(I.Int.neg(P3), I.Int.neg(P4)))
  +i2 : {z2 == r2 : I.Int} = BP.IntN(env, R.Ad(R.Ad(R.Ml(R.V(2n), R.V(4n)), R.Ng(R.V(6n))), R.Ml(R.V(2n), R.V(5n))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ng(R.V(6n))), R.Ad(R.Ng(R.Ml(R.V(3n), R.V(4n))), R.Ng(R.Ml(R.V(3n), R.V(5n))))), [R.Ad(R.V(4n), R.V(5n)), R.V(0n)], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(0n), R.Ng(R.V(2n))))), R.Ad(R.V(5n), R.Ng(R.Ad(R.V(1n), R.Ng(R.V(4n)))))], {==}, (IntZ(env, R.V(3n), R.Ad(R.V(0n), R.Ng(R.V(2n))), hal), (IntZ(env, R.V(5n), R.Ad(R.V(1n), R.Ng(R.V(4n))), hbl), Unit{})))
  +bd = Nat.add(ee, Nat.add(Nat.mul(la, mb), Nat.mul(la, lb)))
  hm = E.Le.trans(RD.Int.mag(z2), RD.Int.mag(r2), bd, E.Le.eq(RD.Int.mag(z2), RD.Int.mag(r2), Equal.cong(I.Int, Nat, z => RD.Int.mag(z), z2, r2, i2)),
    Tri.e(err, I.Int.add(I.Int.neg(P3), I.Int.neg(P4)), Nat.add(Nat.mul(la, mb), Nat.mul(la, lb)), Tri.nm(al, bh, I.Int.neg(P4), Nat.mul(la, lb), Mag.negm(al, bl))))
  hzb = E.Le.trans(RD.Int.mag(z2), Nat.mul(ss, S), Nat.mul(P, S),
    Le.half(RD.Int.mag(z2), Nat.mul(ss, S), E.Le.trans(Nat.double(RD.Int.mag(z2)), Nat.double(bd), Nat.add(Nat.mul(ss, S), Nat.mul(ss, S)), E.Le.dd(RD.Int.mag(z2), bd, hm), B2(S, ee, mb, la, lb, herr, hmb2, hla, hlb, h4))),
    Le.mulr(ss, P, S, hsp))
  +ez = E.RNi.exact(p, z2, Rep(p1, z2, I.Int.add(D.Int.sh(s1, w1), x2g), s, gz, hzb))
  Equal.trans(I.Int, Dk.e2(p, ah, bh, bl, pi), E.RNi(p, z2), z2,
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(Dk.e1(p, ah, bh, pi), E.RNi(p, P2)), z2, Y.Int.cong2(Dk.e1(p, ah, bh, pi), z1, E.RNi(p, P2), P2, ec1, x2)), ez)

# e3 = e2 + al bh exactly: |e3| <= 2^p
def Dk.c3(+s1: Nat, +a: I.Int, +b: I.Int, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int, +A: Nat, +B: Nat, +Q: Nat,
  +hal: {al == I.Int.add(a, I.Int.neg(ah)) : I.Int}, +hbl: {bl == I.Int.add(b, I.Int.neg(bh)) : I.Int},
  +hma: {RD.Int.mag(ah) == Nat.mul(A, RD.Nat.pow2(1n+s1)) : Nat}, +hmb: {RD.Int.mag(bh) == Nat.mul(B, RD.Nat.pow2(1n+s1)) : Nat},
  +hA: {RD.Nat.lt(RD.Nat.pow2(1n+s1), A) == False{} : Bool}, +hB: {RD.Nat.lt(RD.Nat.pow2(1n+s1), B) == False{} : Bool},
  +hla: {RD.Nat.lt(RD.Nat.pow2(1n+s1), Nat.double(RD.Int.mag(al))) == False{} : Bool}, +hlb: {RD.Nat.lt(RD.Nat.pow2(1n+s1), Nat.double(RD.Int.mag(bl))) == False{} : Bool},
  +hpi: {RD.Int.mag(pi) == Nat.mul(Q, RD.Nat.pow2(Nat.add(1n+s1, s1))) : Nat}, +herr: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)), Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))))) == False{} : Bool},
  +h4: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)), Nat.add(Nat.add(Nat.add(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)), RD.Nat.pow2(1n+s1)), RD.Nat.pow2(1n+s1))) == False{} : Bool})
  -> {Dk.e3(1n+Nat.add(1n+s1, s1), ah, al, bh, bl, pi) == I.Int.add(I.Int.add(I.Int.add(I.Int.mul(ah, bh), I.Int.neg(pi)), I.Int.mul(ah, bl)), I.Int.mul(al, bh)) : I.Int}:
  +s : Nat = 1n+s1
  +p1 = Nat.add(s, s1)
  +p : Nat = 1n+p1
  +S = RD.Nat.pow2(s)
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(p)
  +ss = Nat.mul(S, S)
  +hP : {P == ss : Nat} = Pw.P(s1)
  +ma = RD.Int.mag(ah)
  +mb = RD.Int.mag(bh)
  +la = RD.Int.mag(al)
  +lb = RD.Int.mag(bl)
  +err = I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))
  +ee = RD.Int.mag(err)
  +P1 = I.Int.mul(ah, bh)
  +P2 = I.Int.mul(ah, bl)
  +P3 = I.Int.mul(al, bh)
  +P4 = I.Int.mul(al, bl)
  +env : List<&2, I.Int> = [a, b, ah, al, bh, bl, pi]
  +hma2 : {RD.Nat.lt(ss, ma) == False{} : Bool} = E.Le.trans(ma, Nat.mul(A, S), ss, E.Le.eq(ma, Nat.mul(A, S), hma), Le.mulr(A, S, S, hA))
  +hmb2 : {RD.Nat.lt(ss, mb) == False{} : Bool} = E.Le.trans(mb, Nat.mul(B, S), ss, E.Le.eq(mb, Nat.mul(B, S), hmb), Le.mulr(B, S, S, hB))
  +hlb1 : {RD.Nat.lt(S, lb) == False{} : Bool} = Le.of_dbl(lb, S, hlb)
  +hla1 : {RD.Nat.lt(S, la) == False{} : Bool} = Le.of_dbl(la, S, hla)
  +hsp : {RD.Nat.lt(P, ss) == False{} : Bool} = E.Le.eq(ss, P, Equal.sym(Nat, P, ss, hP))
  +z2 = I.Int.add(I.Int.add(I.Int.mul(ah, bh), I.Int.neg(pi)), I.Int.mul(ah, bl))
  +la2 = Nat.mul(la, B)
  +em3 : {RD.Int.mag(P3) == Nat.mul(la2, S) : Nat} = Equal.trans(Nat, RD.Int.mag(P3), Nat.mul(la, mb), Nat.mul(la2, S), Mag.mul(al, bh),
    Equal.trans(Nat, Nat.mul(la, mb), Nat.mul(la, Nat.mul(B, S)), Nat.mul(la2, S), Equal.cong(Nat, Nat, z => Nat.mul(la, z), mb, Nat.mul(B, S), hmb),
      R.NatN.eq([la, B, S], R.Ml(R.V(0n), R.Ml(R.V(1n), R.V(2n))), R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(2n)), [], [], {==}, Unit{}, {==}, {==})))
  +x3 = Px(p1, P3, la2, s, em3, E.Le.trans(la2, ss, P, Le.mul2(la, S, B, S, hla1, hB), hsp))
  +z3 = I.Int.add(z2, P3)
  +r3 = I.Int.add(err, I.Int.neg(P4))
  +i3 : {z3 == r3 : I.Int} = BP.IntN(env, R.Ad(R.Ad(R.Ad(R.Ml(R.V(2n), R.V(4n)), R.Ng(R.V(6n))), R.Ml(R.V(2n), R.V(5n))), R.Ml(R.V(3n), R.V(4n))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ng(R.V(6n))), R.Ng(R.Ml(R.V(3n), R.V(5n)))), [R.Ad(R.V(4n), R.V(5n)), R.V(0n)], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(0n), R.Ng(R.V(2n))))), R.Ad(R.V(5n), R.Ng(R.Ad(R.V(1n), R.Ng(R.V(4n)))))], {==}, (IntZ(env, R.V(3n), R.Ad(R.V(0n), R.Ng(R.V(2n))), hal), (IntZ(env, R.V(5n), R.Ad(R.V(1n), R.Ng(R.V(4n))), hbl), Unit{})))
  +bd = Nat.add(ee, Nat.mul(la, lb))
  hm = E.Le.trans(RD.Int.mag(z3), RD.Int.mag(r3), bd, E.Le.eq(RD.Int.mag(z3), RD.Int.mag(r3), Equal.cong(I.Int, Nat, z => RD.Int.mag(z), z3, r3, i3)),
    Tri.e(err, I.Int.neg(P4), Nat.mul(la, lb), Mag.negm(al, bl)))
  hzb = E.Le.trans(RD.Int.mag(z3), ss, P,
    Le.half(RD.Int.mag(z3), ss, E.Le.trans(Nat.double(RD.Int.mag(z3)), Nat.double(bd), Nat.add(ss, ss), E.Le.dd(RD.Int.mag(z3), bd, hm), B3(S, ee, la, lb, herr, hla, hlb))), hsp)
  Equal.trans(I.Int, Dk.e3(p, ah, al, bh, bl, pi), E.RNi(p, z3), z3,
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(Dk.e2(p, ah, bh, bl, pi), E.RNi(p, P3)), z3, Y.Int.cong2(Dk.e2(p, ah, bh, bl, pi), z2, E.RNi(p, P3), P3, Dk.c2(s1, a, b, ah, al, bh, bl, pi, A, B, Q, hal, hbl, hma, hmb, hA, hB, hla, hlb, hpi, herr, h4), x3)),
    Pxs(p1, z3, hzb))

# e = e3 + al bl = err exactly, so pi + e = a b
def Dk.core(+s1: Nat, +a: I.Int, +b: I.Int, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int, +A: Nat, +B: Nat, +Q: Nat,
  +hal: {al == I.Int.add(a, I.Int.neg(ah)) : I.Int}, +hbl: {bl == I.Int.add(b, I.Int.neg(bh)) : I.Int},
  +hma: {RD.Int.mag(ah) == Nat.mul(A, RD.Nat.pow2(1n+s1)) : Nat}, +hmb: {RD.Int.mag(bh) == Nat.mul(B, RD.Nat.pow2(1n+s1)) : Nat},
  +hA: {RD.Nat.lt(RD.Nat.pow2(1n+s1), A) == False{} : Bool}, +hB: {RD.Nat.lt(RD.Nat.pow2(1n+s1), B) == False{} : Bool},
  +hla: {RD.Nat.lt(RD.Nat.pow2(1n+s1), Nat.double(RD.Int.mag(al))) == False{} : Bool}, +hlb: {RD.Nat.lt(RD.Nat.pow2(1n+s1), Nat.double(RD.Int.mag(bl))) == False{} : Bool},
  +hpi: {RD.Int.mag(pi) == Nat.mul(Q, RD.Nat.pow2(Nat.add(1n+s1, s1))) : Nat}, +herr: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)), Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))))) == False{} : Bool},
  +h4: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)), Nat.add(Nat.add(Nat.add(RD.Nat.pow2(1n+s1), RD.Nat.pow2(1n+s1)), RD.Nat.pow2(1n+s1)), RD.Nat.pow2(1n+s1))) == False{} : Bool})
  -> {I.Int.add(pi, Dk.e(1n+Nat.add(1n+s1, s1), ah, al, bh, bl, pi)) == I.Int.mul(a, b) : I.Int}:
  +s : Nat = 1n+s1
  +p1 = Nat.add(s, s1)
  +p : Nat = 1n+p1
  +S = RD.Nat.pow2(s)
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(p)
  +ss = Nat.mul(S, S)
  +hP : {P == ss : Nat} = Pw.P(s1)
  +ma = RD.Int.mag(ah)
  +mb = RD.Int.mag(bh)
  +la = RD.Int.mag(al)
  +lb = RD.Int.mag(bl)
  +err = I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))
  +ee = RD.Int.mag(err)
  +P1 = I.Int.mul(ah, bh)
  +P2 = I.Int.mul(ah, bl)
  +P3 = I.Int.mul(al, bh)
  +P4 = I.Int.mul(al, bl)
  +env : List<&2, I.Int> = [a, b, ah, al, bh, bl, pi]
  +hma2 : {RD.Nat.lt(ss, ma) == False{} : Bool} = E.Le.trans(ma, Nat.mul(A, S), ss, E.Le.eq(ma, Nat.mul(A, S), hma), Le.mulr(A, S, S, hA))
  +hmb2 : {RD.Nat.lt(ss, mb) == False{} : Bool} = E.Le.trans(mb, Nat.mul(B, S), ss, E.Le.eq(mb, Nat.mul(B, S), hmb), Le.mulr(B, S, S, hB))
  +hlb1 : {RD.Nat.lt(S, lb) == False{} : Bool} = Le.of_dbl(lb, S, hlb)
  +hla1 : {RD.Nat.lt(S, la) == False{} : Bool} = Le.of_dbl(la, S, hla)
  +hsp : {RD.Nat.lt(P, ss) == False{} : Bool} = E.Le.eq(ss, P, Equal.sym(Nat, P, ss, hP))
  +z3 = I.Int.add(I.Int.add(I.Int.add(I.Int.mul(ah, bh), I.Int.neg(pi)), I.Int.mul(ah, bl)), I.Int.mul(al, bh))
  +x4 = Pxs(p1, P4, E.Le.trans(RD.Int.mag(P4), ss, P, E.Le.trans(RD.Int.mag(P4), Nat.mul(la, lb), ss, E.Le.eq(RD.Int.mag(P4), Nat.mul(la, lb), Mag.mul(al, bl)), Le.mul2(la, S, lb, S, hla1, hlb1)), hsp))
  +z4 = I.Int.add(z3, P4)
  +i4 : {z4 == err : I.Int} = BP.IntN(env, R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.V(2n), R.V(4n)), R.Ng(R.V(6n))), R.Ml(R.V(2n), R.V(5n))), R.Ml(R.V(3n), R.V(4n))), R.Ml(R.V(3n), R.V(5n))), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ng(R.V(6n))), [R.Ad(R.V(4n), R.V(5n)), R.V(0n)], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(0n), R.Ng(R.V(2n))))), R.Ad(R.V(5n), R.Ng(R.Ad(R.V(1n), R.Ng(R.V(4n)))))], {==}, (IntZ(env, R.V(3n), R.Ad(R.V(0n), R.Ng(R.V(2n))), hal), (IntZ(env, R.V(5n), R.Ad(R.V(1n), R.Ng(R.V(4n))), hbl), Unit{})))
  hzb = E.Le.trans(RD.Int.mag(z4), ee, P, E.Le.eq(RD.Int.mag(z4), ee, Equal.cong(I.Int, Nat, z => RD.Int.mag(z), z4, err, i4)), E.Le.trans(ee, ss, P, Le.of_dbl(ee, ss, herr), hsp))
  +ez : {Dk.e(p, ah, al, bh, bl, pi) == err : I.Int} = Equal.trans(I.Int, Dk.e(p, ah, al, bh, bl, pi), z4, err,
    Equal.trans(I.Int, Dk.e(p, ah, al, bh, bl, pi), E.RNi(p, z4), z4,
      Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(Dk.e3(p, ah, al, bh, bl, pi), E.RNi(p, P4)), z4, Y.Int.cong2(Dk.e3(p, ah, al, bh, bl, pi), z3, E.RNi(p, P4), P4, Dk.c3(s1, a, b, ah, al, bh, bl, pi, A, B, Q, hal, hbl, hma, hmb, hA, hB, hla, hlb, hpi, herr, h4), x4)),
      Pxs(p1, z4, hzb)), i4)
  Equal.trans(I.Int, I.Int.add(pi, Dk.e(p, ah, al, bh, bl, pi)), I.Int.add(pi, err), I.Int.mul(a, b), Equal.cong(I.Int, I.Int, z => I.Int.add(pi, z), Dk.e(p, ah, al, bh, bl, pi), err, ez),
    BP.IntN([a, b, pi], R.Ad(R.V(2n), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ng(R.V(2n)))), R.Ml(R.V(0n), R.V(1n)), [], [], {==}, Unit{}))

# TwoProd as num/df32.bend computes it
def TP.p(+p: Nat, +a: I.Int, +b: I.Int) -> I.Int:
  E.RNi(p, I.Int.mul(a, b))

def TP.e(+p: Nat, +s: Nat, +a: I.Int, +b: I.Int) -> I.Int:
  Dk.e(p, Sp.h(p, s, a), Sp.l(p, s, a), Sp.h(p, s, b), Sp.l(p, s, b), TP.p(p, a, b))

def Int.mulpp(+n: Nat, +m: Nat) -> {I.Int.mul(I.IPos{n}, I.IPos{m}) == I.IPos{Nat.mul(n, m)} : I.Int}:
  match n:
    case 0n:
      {==}
    case 1n+(+n2):
      {==}

# 4 S <= S S for S = 2^(s2+2)
def Sq4(+s2: Nat) -> E.Le(Nat.add(Nat.add(Nat.add(RD.Nat.pow2(1n+1n+s2), RD.Nat.pow2(1n+1n+s2)), RD.Nat.pow2(1n+1n+s2)), RD.Nat.pow2(1n+1n+s2)), Nat.mul(RD.Nat.pow2(1n+1n+s2), RD.Nat.pow2(1n+1n+s2))):
  +S = RD.Nat.pow2(1n+1n+s2)
  +D = RD.Nat.pow2(1n+s2)
  +Q = RD.Nat.pow2(s2)
  +u = RD.Nat.monus(Q, 1n)
  +hq : {Q == Nat.add(1n, u) : Nat} = BP.Lt.wit(0n, Q)(BP.Pow2.pos(s2))
  +env : List<&2, Nat> = [S, D, Q, u, 1n]
  E.Ge.of(Nat.mul(S, S), Nat.add(Nat.add(Nat.add(S, S), S), S), Nat.add(Nat.add(Nat.add(Nat.mul(S, u), Nat.mul(S, u)), Nat.mul(S, u)), Nat.mul(S, u)),
    R.NatN.eq2(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ml(R.V(0n), R.V(3n)), R.Ml(R.V(0n), R.V(3n))), R.Ml(R.V(0n), R.V(3n))), R.Ml(R.V(0n), R.V(3n)))), [R.V(0n), R.Ad(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n))], [R.Ad(R.V(0n), R.Ng(R.Ad(R.V(1n), R.V(1n)))), R.Ad(R.V(1n), R.Ng(R.Ad(R.V(2n), R.V(2n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.V(4n), R.V(3n))))], [R.Ad(R.Ml(R.V(0n), R.V(4n)), R.Ng(R.V(0n))), R.Ad(R.Ml(R.V(0n), R.V(4n)), R.Ng(R.V(0n))), R.Ad(R.Ml(R.V(0n), R.V(4n)), R.Ng(R.V(0n))), R.Ad(R.Ml(R.V(0n), R.V(4n)), R.Ng(R.V(0n)))], {==}, (R.NatN.z(env, R.V(0n), R.Ad(R.V(1n), R.V(1n)), {==}, {==}, Y.Nat.double_add(D)), (R.NatN.z(env, R.V(1n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, Y.Nat.double_add(Q)), (R.NatN.z(env, R.V(2n), R.Ad(R.V(4n), R.V(3n)), {==}, {==}, hq), Unit{}))), (R.NatN.z(env, R.Ml(R.V(0n), R.V(4n)), R.V(0n), {==}, {==}, NL.Nat.mul_one_r(S)), (R.NatN.z(env, R.Ml(R.V(0n), R.V(4n)), R.V(0n), {==}, {==}, NL.Nat.mul_one_r(S)), (R.NatN.z(env, R.Ml(R.V(0n), R.V(4n)), R.V(0n), {==}, {==}, NL.Nat.mul_one_r(S)), (R.NatN.z(env, R.Ml(R.V(0n), R.V(4n)), R.V(0n), {==}, {==}, NL.Nat.mul_one_r(S)), Unit{})))), {==}, {==}))

# the split of a normalised n, as Dk.core needs it (p = 2s)
def Sp.facts.h(+s1: Nat, +n: Nat, +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+Nat.add(1n+s1, s1))) == True{} : Bool}, +hh: {RD.Nat.lt(n, RD.Nat.pow2(Nat.add(1n+s1, s1))) == False{} : Bool},
  +hc: {RD.Nat.lt(RD.Nat.pow2(1n+Nat.add(1n+s1, s1)), 1n+RD.Nat.pow2(1n+s1)) == False{} : Bool})
  -> {RD.Int.mag(Sp.h(1n+Nat.add(1n+s1, s1), 1n+s1, I.IPos{n})) == Nat.mul(V.ah(1n+Nat.add(1n+s1, s1), 1n+s1, n), RD.Nat.pow2(1n+s1)) : Nat}:
  +p1 = Nat.add(1n+s1, s1)
  +p : Nat = 1n+p1
  +s : Nat = 1n+s1
  +fn = E.Small(p1, n, Lt.to_le(n, RD.Nat.pow2(p), hn))
  +hi = V.hi(p, s, n)
  +eh = Pair.fst({Sp.h(p, s, I.IPos{n}) == I.IPos{hi} : I.Int}, {Sp.l(p, s, I.IPos{n}) == I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{hi})) : I.Int}, Sp.pos(p1, s, n, fn))
  Equal.trans(Nat, RD.Int.mag(Sp.h(p, s, I.IPos{n})), hi, Nat.mul(V.ah(p, s, n), RD.Nat.pow2(s)), Equal.cong(I.Int, Nat, z => RD.Int.mag(z), Sp.h(p, s, I.IPos{n}), I.IPos{hi}, eh), V.hi.grid(p1, s, n, hn, hh, hc))

def Sp.facts.l(+s1: Nat, +n: Nat, +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+Nat.add(1n+s1, s1))) == True{} : Bool})
  -> E.Le(Nat.double(RD.Int.mag(Sp.l(1n+Nat.add(1n+s1, s1), 1n+s1, I.IPos{n}))), RD.Nat.pow2(1n+s1)):
  +p1 = Nat.add(1n+s1, s1)
  +p : Nat = 1n+p1
  +s : Nat = 1n+s1
  +fn = E.Small(p1, n, Lt.to_le(n, RD.Nat.pow2(p), hn))
  +hi = V.hi(p, s, n)
  +el = Pair.snd({Sp.h(p, s, I.IPos{n}) == I.IPos{hi} : I.Int}, {Sp.l(p, s, I.IPos{n}) == I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{hi})) : I.Int}, Sp.pos(p1, s, n, fn))
  +em = Equal.trans(Nat, RD.Int.mag(Sp.l(p, s, I.IPos{n})), RD.Int.mag(I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{hi}))), E.Dist(V.d(p, s, n), V.x(p, s, n)),
    Equal.cong(I.Int, Nat, z => RD.Int.mag(z), Sp.l(p, s, I.IPos{n}), I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{hi})), el), V.lo.mag(p1, s, n, fn))
  E.Le.trans(Nat.double(RD.Int.mag(Sp.l(p, s, I.IPos{n}))), Nat.double(E.Dist(V.d(p, s, n), V.x(p, s, n))), RD.Nat.pow2(s),
    E.Le.eq(Nat.double(RD.Int.mag(Sp.l(p, s, I.IPos{n}))), Nat.double(E.Dist(V.d(p, s, n), V.x(p, s, n))), Equal.cong(Nat, Nat, z => Nat.double(z), RD.Int.mag(Sp.l(p, s, I.IPos{n})), E.Dist(V.d(p, s, n), V.x(p, s, n)), em)),
    V.lo.le(p1, s, n, hn))

# Dekker's product is exact on normalised positive inputs: for p = 2s,
# s >= 2, and n, m in [2^(p-1), 2^p), pi + e = n m
def TwoProd.norm(+s2: Nat, +n: Nat, +m: Nat,
  +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+Nat.add(1n+1n+s2, 1n+s2))) == True{} : Bool}, +hhn: {RD.Nat.lt(n, RD.Nat.pow2(Nat.add(1n+1n+s2, 1n+s2))) == False{} : Bool},
  +hm: {RD.Nat.lt(m, RD.Nat.pow2(1n+Nat.add(1n+1n+s2, 1n+s2))) == True{} : Bool}, +hhm: {RD.Nat.lt(m, RD.Nat.pow2(Nat.add(1n+1n+s2, 1n+s2))) == False{} : Bool})
  -> {I.Int.add(TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), I.IPos{n}, I.IPos{m}), TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, I.IPos{n}, I.IPos{m})) == I.Int.mul(I.IPos{n}, I.IPos{m}) : I.Int}:
  +s1 : Nat = 1n+s2
  +s : Nat = 1n+s1
  +p1 = Nat.add(s, s1)
  +p : Nat = 1n+p1
  +S = RD.Nat.pow2(s)
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(p)
  +ss = Nat.mul(S, S)
  +hP : {P == ss : Nat} = Pw.P(s1)
  +h4 : {RD.Nat.lt(ss, Nat.add(Nat.add(Nat.add(S, S), S), S)) == False{} : Bool} = Sq4(s2)
  +hc : {RD.Nat.lt(P, 1n+S) == False{} : Bool} = E.Le.trans(1n+S, Nat.add(Nat.add(Nat.add(S, S), S), S), P,
    E.Le.trans(1n+S, Nat.add(S, S), Nat.add(Nat.add(Nat.add(S, S), S), S), Le.addr(1n, S, S, Le.one(s)), E.Ge.of(Nat.add(Nat.add(Nat.add(S, S), S), S), Nat.add(S, S), Nat.add(S, S), NL.Nat.add_assoc(Nat.add(S, S), S, S))),
    E.Le.trans(Nat.add(Nat.add(Nat.add(S, S), S), S), ss, P, h4, E.Le.eq(ss, P, Equal.sym(Nat, P, ss, hP))))
  +a : I.Int = I.IPos{n}
  +b : I.Int = I.IPos{m}
  +nm = Nat.mul(n, m)
  +fn = E.Small(p1, n, Lt.to_le(n, P, hn))
  +fm = E.Small(p1, m, Lt.to_le(m, P, hm))
  +ep : {I.Int.mul(a, b) == I.IPos{nm} : I.Int} = Int.mulpp(n, m)
  +pi = TP.p(p, a, b)
  +epi : {pi == I.IPos{E.Rn(p, nm)} : I.Int} = Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.mul(a, b), I.IPos{nm}, ep)
  # pi on the grid 2^(p-1): n m >= 2^(p-1) 2^(p-1)
  +hpi : {RD.Int.mag(pi) == Nat.mul(Gq(p, nm, p1), H) : Nat} = Equal.trans(Nat, RD.Int.mag(pi), E.Rn(p, nm), Nat.mul(Gq(p, nm, p1), H), Equal.cong(I.Int, Nat, z => RD.Int.mag(z), pi, I.IPos{E.Rn(p, nm)}, epi),
    Grid(p1, nm, p1, Le.mul2(H, n, H, m, hhn, hhm)))
  # 2 |a b - pi| <= 2^(shift of n m) <= 2^p
  +hlt = Lt.le_trans(nm, Nat.mul(P, m), Nat.mul(P, P), E.Lt.mono(n, P, m, hn, Lt.le_trans(0n, H, m, BP.Pow2.pos(p1), hhm)), Le.mull(P, m, P, Lt.to_le(m, P, hm)))
  +eer : {RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))) == E.Dist(E.Rn(p, nm), nm) : Nat} = Equal.trans(Nat, RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))), RD.Int.mag(I.Int.add(I.IPos{nm}, I.Int.neg(I.IPos{E.Rn(p, nm)}))), E.Dist(E.Rn(p, nm), nm),
    Equal.cong(I.Int, Nat, z => RD.Int.mag(z), I.Int.add(I.Int.mul(a, b), I.Int.neg(pi)), I.Int.add(I.IPos{nm}, I.Int.neg(I.IPos{E.Rn(p, nm)})), Y.Int.cong2(I.Int.mul(a, b), I.IPos{nm}, I.Int.neg(pi), I.Int.neg(I.IPos{E.Rn(p, nm)}), ep, Equal.cong(I.Int, I.Int, z => I.Int.neg(z), pi, I.IPos{E.Rn(p, nm)}, epi))),
    Equal.trans(Nat, RD.Int.mag(I.Int.add(I.IPos{nm}, I.Int.neg(I.IPos{E.Rn(p, nm)}))), E.Dist(nm, E.Rn(p, nm)), E.Dist(E.Rn(p, nm), nm), E.Mag.diff(nm, E.Rn(p, nm)), E.Dist.comm(nm, E.Rn(p, nm))))
  +herr : {RD.Nat.lt(ss, Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))))) == False{} : Bool} = E.Le.trans(Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi)))), P, ss,
    E.Le.trans(Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi)))), Nat.double(E.Dist(E.Rn(p, nm), nm)), P, E.Le.eq(Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi)))), Nat.double(E.Dist(E.Rn(p, nm), nm)), Equal.cong(Nat, Nat, z => Nat.double(z), RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))), E.Dist(E.Rn(p, nm), nm), eer)),
      E.Le.trans(Nat.double(E.Dist(E.Rn(p, nm), nm)), RD.Nat.pow2(Shf(p, nm)), P, ErrH(p1, nm), Pow2.mono(Shf(p, nm), p, S3(p1, nm, p, hlt)))),
    E.Le.eq(P, ss, hP))
  Dk.core(s1, a, b, Sp.h(p, s, a), Sp.l(p, s, a), Sp.h(p, s, b), Sp.l(p, s, b), pi, V.ah(p, s, n), V.ah(p, s, m), Gq(p, nm, p1),
    Split(p1, s, a, fn), Split(p1, s, b, fm), Sp.facts.h(s1, n, hn, hhn, hc), Sp.facts.h(s1, m, hm, hhm, hc),
    V.ah.le(p1, s, s, n, hn, hhn, hc, hP), V.ah.le(p1, s, s, m, hm, hhm, hc, hP), Sp.facts.l(s1, n, hn), Sp.facts.l(s1, m, hm), hpi, herr, h4)

# Scaling by 2^k
# --------------
# Every step of the split and of Dekker's product commutes with sh.

def Sh.mulc(+k: Nat, +c: I.Int, +a: I.Int) -> {I.Int.mul(c, D.Int.sh(k, a)) == D.Int.sh(k, I.Int.mul(c, a)) : I.Int}:
  +pk = Y.P(k)
  +env : List<&2, I.Int> = [c, a, pk]
  Equal.trans(I.Int, I.Int.mul(c, D.Int.sh(k, a)), I.Int.mul(I.Int.mul(c, a), pk), D.Int.sh(k, I.Int.mul(c, a)),
    Equal.trans(I.Int, I.Int.mul(c, D.Int.sh(k, a)), I.Int.mul(c, I.Int.mul(a, pk)), I.Int.mul(I.Int.mul(c, a), pk), Equal.cong(I.Int, I.Int, z => I.Int.mul(c, z), D.Int.sh(k, a), I.Int.mul(a, pk), Y.Sh.p(k, a)),
      BP.IntN(env, R.Ml(R.V(0n), R.Ml(R.V(1n), R.V(2n))), R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(2n)), [], [], {==}, Unit{})),
    Equal.sym(I.Int, D.Int.sh(k, I.Int.mul(c, a)), I.Int.mul(I.Int.mul(c, a), pk), Y.Sh.p(k, I.Int.mul(c, a))))

def Sh.mul2(+i: Nat, +j: Nat, +x: I.Int, +y: I.Int) -> {I.Int.mul(D.Int.sh(i, x), D.Int.sh(j, y)) == D.Int.sh(Nat.add(i, j), I.Int.mul(x, y)) : I.Int}:
  +pi = Y.P(i)
  +pj = Y.P(j)
  +pij = Y.P(Nat.add(i, j))
  +eij : {pij == I.Int.mul(pj, pi) : I.Int} = Equal.trans(I.Int, pij, D.Int.sh(i, pj), I.Int.mul(pj, pi), Equal.sym(I.Int, D.Int.sh(i, pj), pij, Y.Int.sh_sh(i, j, I.IPos{1n})), Y.Sh.p(i, pj))
  +env : List<&2, I.Int> = [x, y, pi, pj]
  Equal.trans(I.Int, I.Int.mul(D.Int.sh(i, x), D.Int.sh(j, y)), I.Int.mul(I.Int.mul(x, y), pij), D.Int.sh(Nat.add(i, j), I.Int.mul(x, y)),
    Equal.trans(I.Int, I.Int.mul(D.Int.sh(i, x), D.Int.sh(j, y)), I.Int.mul(I.Int.mul(x, pi), I.Int.mul(y, pj)), I.Int.mul(I.Int.mul(x, y), pij),
      Equal.trans(I.Int, I.Int.mul(D.Int.sh(i, x), D.Int.sh(j, y)), I.Int.mul(I.Int.mul(x, pi), D.Int.sh(j, y)), I.Int.mul(I.Int.mul(x, pi), I.Int.mul(y, pj)),
        Equal.cong(I.Int, I.Int, z => I.Int.mul(z, D.Int.sh(j, y)), D.Int.sh(i, x), I.Int.mul(x, pi), Y.Sh.p(i, x)),
        Equal.cong(I.Int, I.Int, z => I.Int.mul(I.Int.mul(x, pi), z), D.Int.sh(j, y), I.Int.mul(y, pj), Y.Sh.p(j, y))),
      Equal.trans(I.Int, I.Int.mul(I.Int.mul(x, pi), I.Int.mul(y, pj)), I.Int.mul(I.Int.mul(x, y), I.Int.mul(pj, pi)), I.Int.mul(I.Int.mul(x, y), pij),
        BP.IntN(env, R.Ml(R.Ml(R.V(0n), R.V(2n)), R.Ml(R.V(1n), R.V(3n))), R.Ml(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(3n), R.V(2n))), [], [], {==}, Unit{}),
        Equal.cong(I.Int, I.Int, z => I.Int.mul(I.Int.mul(x, y), z), I.Int.mul(pj, pi), pij, Equal.sym(I.Int, pij, I.Int.mul(pj, pi), eij)))),
    Equal.sym(I.Int, D.Int.sh(Nat.add(i, j), I.Int.mul(x, y)), I.Int.mul(I.Int.mul(x, y), pij), Y.Sh.p(Nat.add(i, j), I.Int.mul(x, y))))

# R(sh x + sh y) = sh R(x + y), R(sh x - sh y) = sh R(x - y)
def RNi.shadd(+p: Nat, +k: Nat, +x: I.Int, +y: I.Int) -> {E.RNi(p, I.Int.add(D.Int.sh(k, x), D.Int.sh(k, y))) == D.Int.sh(k, E.RNi(p, I.Int.add(x, y))) : I.Int}:
  Equal.trans(I.Int, E.RNi(p, I.Int.add(D.Int.sh(k, x), D.Int.sh(k, y))), E.RNi(p, D.Int.sh(k, I.Int.add(x, y))), D.Int.sh(k, E.RNi(p, I.Int.add(x, y))),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(D.Int.sh(k, x), D.Int.sh(k, y)), D.Int.sh(k, I.Int.add(x, y)), Equal.sym(I.Int, D.Int.sh(k, I.Int.add(x, y)), I.Int.add(D.Int.sh(k, x), D.Int.sh(k, y)), Y.Int.sh_add(k, x, y))),
    E.RNi.sh(p, k, I.Int.add(x, y)))

def RNi.shsub(+p: Nat, +k: Nat, +x: I.Int, +y: I.Int) -> {E.RNi(p, I.Int.add(D.Int.sh(k, x), I.Int.neg(D.Int.sh(k, y)))) == D.Int.sh(k, E.RNi(p, I.Int.add(x, I.Int.neg(y)))) : I.Int}:
  Equal.trans(I.Int, E.RNi(p, I.Int.add(D.Int.sh(k, x), I.Int.neg(D.Int.sh(k, y)))), E.RNi(p, D.Int.sh(k, I.Int.add(x, I.Int.neg(y)))), D.Int.sh(k, E.RNi(p, I.Int.add(x, I.Int.neg(y)))),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(D.Int.sh(k, x), I.Int.neg(D.Int.sh(k, y))), D.Int.sh(k, I.Int.add(x, I.Int.neg(y))), Sh.diff(k, x, y)),
    E.RNi.sh(p, k, I.Int.add(x, I.Int.neg(y))))

def Sp.sh.g(+p: Nat, +s: Nat, +k: Nat, +a: I.Int) -> {Sp.g(p, s, D.Int.sh(k, a)) == D.Int.sh(k, Sp.g(p, s, a)) : I.Int}:
  Equal.trans(I.Int, Sp.g(p, s, D.Int.sh(k, a)), E.RNi(p, D.Int.sh(k, I.Int.mul(Sp.c(s), a))), D.Int.sh(k, Sp.g(p, s, a)),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.mul(Sp.c(s), D.Int.sh(k, a)), D.Int.sh(k, I.Int.mul(Sp.c(s), a)), Sh.mulc(k, Sp.c(s), a)),
    E.RNi.sh(p, k, I.Int.mul(Sp.c(s), a)))

def Sp.sh.d(+p: Nat, +s: Nat, +k: Nat, +a: I.Int) -> {Sp.d(p, s, D.Int.sh(k, a)) == D.Int.sh(k, Sp.d(p, s, a)) : I.Int}:
  Equal.trans(I.Int, Sp.d(p, s, D.Int.sh(k, a)), E.RNi(p, I.Int.add(D.Int.sh(k, a), I.Int.neg(D.Int.sh(k, Sp.g(p, s, a))))), D.Int.sh(k, Sp.d(p, s, a)),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, I.Int.add(D.Int.sh(k, a), I.Int.neg(z))), Sp.g(p, s, D.Int.sh(k, a)), D.Int.sh(k, Sp.g(p, s, a)), Sp.sh.g(p, s, k, a)),
    RNi.shsub(p, k, a, Sp.g(p, s, a)))

def Sp.sh.h(+p: Nat, +s: Nat, +k: Nat, +a: I.Int) -> {Sp.h(p, s, D.Int.sh(k, a)) == D.Int.sh(k, Sp.h(p, s, a)) : I.Int}:
  Equal.trans(I.Int, Sp.h(p, s, D.Int.sh(k, a)), E.RNi(p, I.Int.add(D.Int.sh(k, Sp.g(p, s, a)), D.Int.sh(k, Sp.d(p, s, a)))), D.Int.sh(k, Sp.h(p, s, a)),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(Sp.g(p, s, D.Int.sh(k, a)), Sp.d(p, s, D.Int.sh(k, a))), I.Int.add(D.Int.sh(k, Sp.g(p, s, a)), D.Int.sh(k, Sp.d(p, s, a))),
      Y.Int.cong2(Sp.g(p, s, D.Int.sh(k, a)), D.Int.sh(k, Sp.g(p, s, a)), Sp.d(p, s, D.Int.sh(k, a)), D.Int.sh(k, Sp.d(p, s, a)), Sp.sh.g(p, s, k, a), Sp.sh.d(p, s, k, a))),
    RNi.shadd(p, k, Sp.g(p, s, a), Sp.d(p, s, a)))

def Sp.sh.l(+p: Nat, +s: Nat, +k: Nat, +a: I.Int) -> {Sp.l(p, s, D.Int.sh(k, a)) == D.Int.sh(k, Sp.l(p, s, a)) : I.Int}:
  Equal.trans(I.Int, Sp.l(p, s, D.Int.sh(k, a)), E.RNi(p, I.Int.add(D.Int.sh(k, a), I.Int.neg(D.Int.sh(k, Sp.h(p, s, a))))), D.Int.sh(k, Sp.l(p, s, a)),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, I.Int.add(D.Int.sh(k, a), I.Int.neg(z))), Sp.h(p, s, D.Int.sh(k, a)), D.Int.sh(k, Sp.h(p, s, a)), Sp.sh.h(p, s, k, a)),
    RNi.shsub(p, k, a, Sp.h(p, s, a)))

# R(sh_i x sh_j y) = sh_(i+j) R(x y)
def RNi.shmul(+p: Nat, +i: Nat, +j: Nat, +x: I.Int, +y: I.Int) -> {E.RNi(p, I.Int.mul(D.Int.sh(i, x), D.Int.sh(j, y))) == D.Int.sh(Nat.add(i, j), E.RNi(p, I.Int.mul(x, y))) : I.Int}:
  Equal.trans(I.Int, E.RNi(p, I.Int.mul(D.Int.sh(i, x), D.Int.sh(j, y))), E.RNi(p, D.Int.sh(Nat.add(i, j), I.Int.mul(x, y))), D.Int.sh(Nat.add(i, j), E.RNi(p, I.Int.mul(x, y))),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.mul(D.Int.sh(i, x), D.Int.sh(j, y)), D.Int.sh(Nat.add(i, j), I.Int.mul(x, y)), Sh.mul2(i, j, x, y)),
    E.RNi.sh(p, Nat.add(i, j), I.Int.mul(x, y)))

def Dk.sh.e1(+p: Nat, +i: Nat, +j: Nat, +ah: I.Int, +bh: I.Int, +pi: I.Int)
  -> {Dk.e1(p, D.Int.sh(i, ah), D.Int.sh(j, bh), D.Int.sh(Nat.add(i, j), pi)) == D.Int.sh(Nat.add(i, j), Dk.e1(p, ah, bh, pi)) : I.Int}:
  +k = Nat.add(i, j)
  Equal.trans(I.Int, Dk.e1(p, D.Int.sh(i, ah), D.Int.sh(j, bh), D.Int.sh(k, pi)), E.RNi(p, I.Int.add(D.Int.sh(k, E.RNi(p, I.Int.mul(ah, bh))), I.Int.neg(D.Int.sh(k, pi)))), D.Int.sh(k, Dk.e1(p, ah, bh, pi)),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, I.Int.add(z, I.Int.neg(D.Int.sh(k, pi)))), E.RNi(p, I.Int.mul(D.Int.sh(i, ah), D.Int.sh(j, bh))), D.Int.sh(k, E.RNi(p, I.Int.mul(ah, bh))), RNi.shmul(p, i, j, ah, bh)),
    RNi.shsub(p, k, E.RNi(p, I.Int.mul(ah, bh)), pi))

def Dk.sh.e2(+p: Nat, +i: Nat, +j: Nat, +ah: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int)
  -> {Dk.e2(p, D.Int.sh(i, ah), D.Int.sh(j, bh), D.Int.sh(j, bl), D.Int.sh(Nat.add(i, j), pi)) == D.Int.sh(Nat.add(i, j), Dk.e2(p, ah, bh, bl, pi)) : I.Int}:
  +k = Nat.add(i, j)
  +x = Dk.e1(p, D.Int.sh(i, ah), D.Int.sh(j, bh), D.Int.sh(k, pi))
  +y = E.RNi(p, I.Int.mul(D.Int.sh(i, ah), D.Int.sh(j, bl)))
  Equal.trans(I.Int, E.RNi(p, I.Int.add(x, y)), E.RNi(p, I.Int.add(D.Int.sh(k, Dk.e1(p, ah, bh, pi)), D.Int.sh(k, E.RNi(p, I.Int.mul(ah, bl))))), D.Int.sh(k, Dk.e2(p, ah, bh, bl, pi)),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(x, y), I.Int.add(D.Int.sh(k, Dk.e1(p, ah, bh, pi)), D.Int.sh(k, E.RNi(p, I.Int.mul(ah, bl)))),
      Y.Int.cong2(x, D.Int.sh(k, Dk.e1(p, ah, bh, pi)), y, D.Int.sh(k, E.RNi(p, I.Int.mul(ah, bl))), Dk.sh.e1(p, i, j, ah, bh, pi), RNi.shmul(p, i, j, ah, bl))),
    RNi.shadd(p, k, Dk.e1(p, ah, bh, pi), E.RNi(p, I.Int.mul(ah, bl))))

def Dk.sh.e3(+p: Nat, +i: Nat, +j: Nat, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int)
  -> {Dk.e3(p, D.Int.sh(i, ah), D.Int.sh(i, al), D.Int.sh(j, bh), D.Int.sh(j, bl), D.Int.sh(Nat.add(i, j), pi)) == D.Int.sh(Nat.add(i, j), Dk.e3(p, ah, al, bh, bl, pi)) : I.Int}:
  +k = Nat.add(i, j)
  +x = Dk.e2(p, D.Int.sh(i, ah), D.Int.sh(j, bh), D.Int.sh(j, bl), D.Int.sh(k, pi))
  +y = E.RNi(p, I.Int.mul(D.Int.sh(i, al), D.Int.sh(j, bh)))
  Equal.trans(I.Int, E.RNi(p, I.Int.add(x, y)), E.RNi(p, I.Int.add(D.Int.sh(k, Dk.e2(p, ah, bh, bl, pi)), D.Int.sh(k, E.RNi(p, I.Int.mul(al, bh))))), D.Int.sh(k, Dk.e3(p, ah, al, bh, bl, pi)),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(x, y), I.Int.add(D.Int.sh(k, Dk.e2(p, ah, bh, bl, pi)), D.Int.sh(k, E.RNi(p, I.Int.mul(al, bh)))),
      Y.Int.cong2(x, D.Int.sh(k, Dk.e2(p, ah, bh, bl, pi)), y, D.Int.sh(k, E.RNi(p, I.Int.mul(al, bh))), Dk.sh.e2(p, i, j, ah, bh, bl, pi), RNi.shmul(p, i, j, al, bh))),
    RNi.shadd(p, k, Dk.e2(p, ah, bh, bl, pi), E.RNi(p, I.Int.mul(al, bh))))

def Dk.sh.e(+p: Nat, +i: Nat, +j: Nat, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int)
  -> {Dk.e(p, D.Int.sh(i, ah), D.Int.sh(i, al), D.Int.sh(j, bh), D.Int.sh(j, bl), D.Int.sh(Nat.add(i, j), pi)) == D.Int.sh(Nat.add(i, j), Dk.e(p, ah, al, bh, bl, pi)) : I.Int}:
  +k = Nat.add(i, j)
  +x = Dk.e3(p, D.Int.sh(i, ah), D.Int.sh(i, al), D.Int.sh(j, bh), D.Int.sh(j, bl), D.Int.sh(k, pi))
  +y = E.RNi(p, I.Int.mul(D.Int.sh(i, al), D.Int.sh(j, bl)))
  Equal.trans(I.Int, E.RNi(p, I.Int.add(x, y)), E.RNi(p, I.Int.add(D.Int.sh(k, Dk.e3(p, ah, al, bh, bl, pi)), D.Int.sh(k, E.RNi(p, I.Int.mul(al, bl))))), D.Int.sh(k, Dk.e(p, ah, al, bh, bl, pi)),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(x, y), I.Int.add(D.Int.sh(k, Dk.e3(p, ah, al, bh, bl, pi)), D.Int.sh(k, E.RNi(p, I.Int.mul(al, bl)))),
      Y.Int.cong2(x, D.Int.sh(k, Dk.e3(p, ah, al, bh, bl, pi)), y, D.Int.sh(k, E.RNi(p, I.Int.mul(al, bl))), Dk.sh.e3(p, i, j, ah, al, bh, bl, pi), RNi.shmul(p, i, j, al, bl))),
    RNi.shadd(p, k, Dk.e3(p, ah, al, bh, bl, pi), E.RNi(p, I.Int.mul(al, bl))))

def TP.sh.p(+p: Nat, +i: Nat, +j: Nat, +a: I.Int, +b: I.Int) -> {TP.p(p, D.Int.sh(i, a), D.Int.sh(j, b)) == D.Int.sh(Nat.add(i, j), TP.p(p, a, b)) : I.Int}:
  RNi.shmul(p, i, j, a, b)

def TP.sh.e(+p: Nat, +s: Nat, +i: Nat, +j: Nat, +a: I.Int, +b: I.Int) -> {TP.e(p, s, D.Int.sh(i, a), D.Int.sh(j, b)) == D.Int.sh(Nat.add(i, j), TP.e(p, s, a, b)) : I.Int}:
  +k = Nat.add(i, j)
  +ia = D.Int.sh(i, a)
  +jb = D.Int.sh(j, b)
  +ah = Sp.h(p, s, a)
  +al = Sp.l(p, s, a)
  +bh = Sp.h(p, s, b)
  +bl = Sp.l(p, s, b)
  +pi = TP.p(p, a, b)
  +e1 = Equal.cong(I.Int, I.Int, z => Dk.e(p, z, Sp.l(p, s, ia), Sp.h(p, s, jb), Sp.l(p, s, jb), TP.p(p, ia, jb)), Sp.h(p, s, ia), D.Int.sh(i, ah), Sp.sh.h(p, s, i, a))
  +e2 = Equal.cong(I.Int, I.Int, z => Dk.e(p, D.Int.sh(i, ah), z, Sp.h(p, s, jb), Sp.l(p, s, jb), TP.p(p, ia, jb)), Sp.l(p, s, ia), D.Int.sh(i, al), Sp.sh.l(p, s, i, a))
  +e3 = Equal.cong(I.Int, I.Int, z => Dk.e(p, D.Int.sh(i, ah), D.Int.sh(i, al), z, Sp.l(p, s, jb), TP.p(p, ia, jb)), Sp.h(p, s, jb), D.Int.sh(j, bh), Sp.sh.h(p, s, j, b))
  +e4 = Equal.cong(I.Int, I.Int, z => Dk.e(p, D.Int.sh(i, ah), D.Int.sh(i, al), D.Int.sh(j, bh), z, TP.p(p, ia, jb)), Sp.l(p, s, jb), D.Int.sh(j, bl), Sp.sh.l(p, s, j, b))
  +e5 = Equal.cong(I.Int, I.Int, z => Dk.e(p, D.Int.sh(i, ah), D.Int.sh(i, al), D.Int.sh(j, bh), D.Int.sh(j, bl), z), TP.p(p, ia, jb), D.Int.sh(k, pi), TP.sh.p(p, i, j, a, b))
  Equal.trans(I.Int, TP.e(p, s, ia, jb), Dk.e(p, D.Int.sh(i, ah), Sp.l(p, s, ia), Sp.h(p, s, jb), Sp.l(p, s, jb), TP.p(p, ia, jb)), D.Int.sh(k, TP.e(p, s, a, b)), e1,
    Equal.trans(I.Int, Dk.e(p, D.Int.sh(i, ah), Sp.l(p, s, ia), Sp.h(p, s, jb), Sp.l(p, s, jb), TP.p(p, ia, jb)), Dk.e(p, D.Int.sh(i, ah), D.Int.sh(i, al), Sp.h(p, s, jb), Sp.l(p, s, jb), TP.p(p, ia, jb)), D.Int.sh(k, TP.e(p, s, a, b)), e2,
      Equal.trans(I.Int, Dk.e(p, D.Int.sh(i, ah), D.Int.sh(i, al), Sp.h(p, s, jb), Sp.l(p, s, jb), TP.p(p, ia, jb)), Dk.e(p, D.Int.sh(i, ah), D.Int.sh(i, al), D.Int.sh(j, bh), Sp.l(p, s, jb), TP.p(p, ia, jb)), D.Int.sh(k, TP.e(p, s, a, b)), e3,
        Equal.trans(I.Int, Dk.e(p, D.Int.sh(i, ah), D.Int.sh(i, al), D.Int.sh(j, bh), Sp.l(p, s, jb), TP.p(p, ia, jb)), Dk.e(p, D.Int.sh(i, ah), D.Int.sh(i, al), D.Int.sh(j, bh), D.Int.sh(j, bl), TP.p(p, ia, jb)), D.Int.sh(k, TP.e(p, s, a, b)), e4,
          Equal.trans(I.Int, Dk.e(p, D.Int.sh(i, ah), D.Int.sh(i, al), D.Int.sh(j, bh), D.Int.sh(j, bl), TP.p(p, ia, jb)), Dk.e(p, D.Int.sh(i, ah), D.Int.sh(i, al), D.Int.sh(j, bh), D.Int.sh(j, bl), D.Int.sh(k, pi)), D.Int.sh(k, TP.e(p, s, a, b)), e5,
            Dk.sh.e(p, i, j, ah, al, bh, bl, pi))))))

# Negation
# --------

def RNi.nml(+p: Nat, +x: I.Int, +y: I.Int) -> {E.RNi(p, I.Int.mul(I.Int.neg(x), y)) == I.Int.neg(E.RNi(p, I.Int.mul(x, y))) : I.Int}:
  Equal.trans(I.Int, E.RNi(p, I.Int.mul(I.Int.neg(x), y)), E.RNi(p, I.Int.neg(I.Int.mul(x, y))), I.Int.neg(E.RNi(p, I.Int.mul(x, y))),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.mul(I.Int.neg(x), y), I.Int.neg(I.Int.mul(x, y)), BP.IntN([x, y], R.Ml(R.Ng(R.V(0n)), R.V(1n)), R.Ng(R.Ml(R.V(0n), R.V(1n))), [], [], {==}, Unit{})),
    E.RNi.neg(p, I.Int.mul(x, y)))

def RNi.nmr(+p: Nat, +x: I.Int, +y: I.Int) -> {E.RNi(p, I.Int.mul(x, I.Int.neg(y))) == I.Int.neg(E.RNi(p, I.Int.mul(x, y))) : I.Int}:
  Equal.trans(I.Int, E.RNi(p, I.Int.mul(x, I.Int.neg(y))), E.RNi(p, I.Int.neg(I.Int.mul(x, y))), I.Int.neg(E.RNi(p, I.Int.mul(x, y))),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.mul(x, I.Int.neg(y)), I.Int.neg(I.Int.mul(x, y)), BP.IntN([x, y], R.Ml(R.V(0n), R.Ng(R.V(1n))), R.Ng(R.Ml(R.V(0n), R.V(1n))), [], [], {==}, Unit{})),
    E.RNi.neg(p, I.Int.mul(x, y)))

def RNi.nadd(+p: Nat, +x: I.Int, +y: I.Int) -> {E.RNi(p, I.Int.add(I.Int.neg(x), I.Int.neg(y))) == I.Int.neg(E.RNi(p, I.Int.add(x, y))) : I.Int}:
  Equal.trans(I.Int, E.RNi(p, I.Int.add(I.Int.neg(x), I.Int.neg(y))), E.RNi(p, I.Int.neg(I.Int.add(x, y))), I.Int.neg(E.RNi(p, I.Int.add(x, y))),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(I.Int.neg(x), I.Int.neg(y)), I.Int.neg(I.Int.add(x, y)), BP.IntN([x, y], R.Ad(R.Ng(R.V(0n)), R.Ng(R.V(1n))), R.Ng(R.Ad(R.V(0n), R.V(1n))), [], [], {==}, Unit{})),
    E.RNi.neg(p, I.Int.add(x, y)))

def RNi.nsub(+p: Nat, +x: I.Int, +y: I.Int) -> {E.RNi(p, I.Int.add(I.Int.neg(x), I.Int.neg(I.Int.neg(y)))) == I.Int.neg(E.RNi(p, I.Int.add(x, I.Int.neg(y)))) : I.Int}:
  Equal.trans(I.Int, E.RNi(p, I.Int.add(I.Int.neg(x), I.Int.neg(I.Int.neg(y)))), E.RNi(p, I.Int.neg(I.Int.add(x, I.Int.neg(y)))), I.Int.neg(E.RNi(p, I.Int.add(x, I.Int.neg(y)))),
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(I.Int.neg(x), I.Int.neg(I.Int.neg(y))), I.Int.neg(I.Int.add(x, I.Int.neg(y))), BP.IntN([x, y], R.Ad(R.Ng(R.V(0n)), R.Ng(R.Ng(R.V(1n)))), R.Ng(R.Ad(R.V(0n), R.Ng(R.V(1n)))), [], [], {==}, Unit{})),
    E.RNi.neg(p, I.Int.add(x, I.Int.neg(y))))

# Dekker's steps commute with negating a's or b's half

def Dk.na.e1(+p: Nat, +ah: I.Int, +bh: I.Int, +pi: I.Int) -> {Dk.e1(p, I.Int.neg(ah), bh, I.Int.neg(pi)) == I.Int.neg(Dk.e1(p, ah, bh, pi)) : I.Int}:
  Equal.trans(I.Int, Dk.e1(p, I.Int.neg(ah), bh, I.Int.neg(pi)), E.RNi(p, I.Int.add(I.Int.neg(E.RNi(p, I.Int.mul(ah, bh))), I.Int.neg(I.Int.neg(pi)))), I.Int.neg(Dk.e1(p, ah, bh, pi)), Equal.cong(I.Int, I.Int, z => E.RNi(p, I.Int.add(z, I.Int.neg(I.Int.neg(pi)))), E.RNi(p, I.Int.mul(I.Int.neg(ah), bh)), I.Int.neg(E.RNi(p, I.Int.mul(ah, bh))), RNi.nml(p, ah, bh)), RNi.nsub(p, E.RNi(p, I.Int.mul(ah, bh)), pi))

def Dk.na.e2(+p: Nat, +ah: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int) -> {Dk.e2(p, I.Int.neg(ah), bh, bl, I.Int.neg(pi)) == I.Int.neg(Dk.e2(p, ah, bh, bl, pi)) : I.Int}:
  Equal.trans(I.Int, Dk.e2(p, I.Int.neg(ah), bh, bl, I.Int.neg(pi)), E.RNi(p, I.Int.add(I.Int.neg(Dk.e1(p, ah, bh, pi)), I.Int.neg(E.RNi(p, I.Int.mul(ah, bl))))), I.Int.neg(Dk.e2(p, ah, bh, bl, pi)), Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(Dk.e1(p, I.Int.neg(ah), bh, I.Int.neg(pi)), E.RNi(p, I.Int.mul(I.Int.neg(ah), bl))), I.Int.add(I.Int.neg(Dk.e1(p, ah, bh, pi)), I.Int.neg(E.RNi(p, I.Int.mul(ah, bl)))), Y.Int.cong2(Dk.e1(p, I.Int.neg(ah), bh, I.Int.neg(pi)), I.Int.neg(Dk.e1(p, ah, bh, pi)), E.RNi(p, I.Int.mul(I.Int.neg(ah), bl)), I.Int.neg(E.RNi(p, I.Int.mul(ah, bl))), Dk.na.e1(p, ah, bh, pi), RNi.nml(p, ah, bl))), RNi.nadd(p, Dk.e1(p, ah, bh, pi), E.RNi(p, I.Int.mul(ah, bl))))

def Dk.na.e3(+p: Nat, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int) -> {Dk.e3(p, I.Int.neg(ah), I.Int.neg(al), bh, bl, I.Int.neg(pi)) == I.Int.neg(Dk.e3(p, ah, al, bh, bl, pi)) : I.Int}:
  Equal.trans(I.Int, Dk.e3(p, I.Int.neg(ah), I.Int.neg(al), bh, bl, I.Int.neg(pi)), E.RNi(p, I.Int.add(I.Int.neg(Dk.e2(p, ah, bh, bl, pi)), I.Int.neg(E.RNi(p, I.Int.mul(al, bh))))), I.Int.neg(Dk.e3(p, ah, al, bh, bl, pi)), Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(Dk.e2(p, I.Int.neg(ah), bh, bl, I.Int.neg(pi)), E.RNi(p, I.Int.mul(I.Int.neg(al), bh))), I.Int.add(I.Int.neg(Dk.e2(p, ah, bh, bl, pi)), I.Int.neg(E.RNi(p, I.Int.mul(al, bh)))), Y.Int.cong2(Dk.e2(p, I.Int.neg(ah), bh, bl, I.Int.neg(pi)), I.Int.neg(Dk.e2(p, ah, bh, bl, pi)), E.RNi(p, I.Int.mul(I.Int.neg(al), bh)), I.Int.neg(E.RNi(p, I.Int.mul(al, bh))), Dk.na.e2(p, ah, bh, bl, pi), RNi.nml(p, al, bh))), RNi.nadd(p, Dk.e2(p, ah, bh, bl, pi), E.RNi(p, I.Int.mul(al, bh))))

def Dk.na.e(+p: Nat, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int) -> {Dk.e(p, I.Int.neg(ah), I.Int.neg(al), bh, bl, I.Int.neg(pi)) == I.Int.neg(Dk.e(p, ah, al, bh, bl, pi)) : I.Int}:
  Equal.trans(I.Int, Dk.e(p, I.Int.neg(ah), I.Int.neg(al), bh, bl, I.Int.neg(pi)), E.RNi(p, I.Int.add(I.Int.neg(Dk.e3(p, ah, al, bh, bl, pi)), I.Int.neg(E.RNi(p, I.Int.mul(al, bl))))), I.Int.neg(Dk.e(p, ah, al, bh, bl, pi)), Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(Dk.e3(p, I.Int.neg(ah), I.Int.neg(al), bh, bl, I.Int.neg(pi)), E.RNi(p, I.Int.mul(I.Int.neg(al), bl))), I.Int.add(I.Int.neg(Dk.e3(p, ah, al, bh, bl, pi)), I.Int.neg(E.RNi(p, I.Int.mul(al, bl)))), Y.Int.cong2(Dk.e3(p, I.Int.neg(ah), I.Int.neg(al), bh, bl, I.Int.neg(pi)), I.Int.neg(Dk.e3(p, ah, al, bh, bl, pi)), E.RNi(p, I.Int.mul(I.Int.neg(al), bl)), I.Int.neg(E.RNi(p, I.Int.mul(al, bl))), Dk.na.e3(p, ah, al, bh, bl, pi), RNi.nml(p, al, bl))), RNi.nadd(p, Dk.e3(p, ah, al, bh, bl, pi), E.RNi(p, I.Int.mul(al, bl))))

def Dk.nb.e1(+p: Nat, +ah: I.Int, +bh: I.Int, +pi: I.Int) -> {Dk.e1(p, ah, I.Int.neg(bh), I.Int.neg(pi)) == I.Int.neg(Dk.e1(p, ah, bh, pi)) : I.Int}:
  Equal.trans(I.Int, Dk.e1(p, ah, I.Int.neg(bh), I.Int.neg(pi)), E.RNi(p, I.Int.add(I.Int.neg(E.RNi(p, I.Int.mul(ah, bh))), I.Int.neg(I.Int.neg(pi)))), I.Int.neg(Dk.e1(p, ah, bh, pi)), Equal.cong(I.Int, I.Int, z => E.RNi(p, I.Int.add(z, I.Int.neg(I.Int.neg(pi)))), E.RNi(p, I.Int.mul(ah, I.Int.neg(bh))), I.Int.neg(E.RNi(p, I.Int.mul(ah, bh))), RNi.nmr(p, ah, bh)), RNi.nsub(p, E.RNi(p, I.Int.mul(ah, bh)), pi))

def Dk.nb.e2(+p: Nat, +ah: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int) -> {Dk.e2(p, ah, I.Int.neg(bh), I.Int.neg(bl), I.Int.neg(pi)) == I.Int.neg(Dk.e2(p, ah, bh, bl, pi)) : I.Int}:
  Equal.trans(I.Int, Dk.e2(p, ah, I.Int.neg(bh), I.Int.neg(bl), I.Int.neg(pi)), E.RNi(p, I.Int.add(I.Int.neg(Dk.e1(p, ah, bh, pi)), I.Int.neg(E.RNi(p, I.Int.mul(ah, bl))))), I.Int.neg(Dk.e2(p, ah, bh, bl, pi)), Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(Dk.e1(p, ah, I.Int.neg(bh), I.Int.neg(pi)), E.RNi(p, I.Int.mul(ah, I.Int.neg(bl)))), I.Int.add(I.Int.neg(Dk.e1(p, ah, bh, pi)), I.Int.neg(E.RNi(p, I.Int.mul(ah, bl)))), Y.Int.cong2(Dk.e1(p, ah, I.Int.neg(bh), I.Int.neg(pi)), I.Int.neg(Dk.e1(p, ah, bh, pi)), E.RNi(p, I.Int.mul(ah, I.Int.neg(bl))), I.Int.neg(E.RNi(p, I.Int.mul(ah, bl))), Dk.nb.e1(p, ah, bh, pi), RNi.nmr(p, ah, bl))), RNi.nadd(p, Dk.e1(p, ah, bh, pi), E.RNi(p, I.Int.mul(ah, bl))))

def Dk.nb.e3(+p: Nat, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int) -> {Dk.e3(p, ah, al, I.Int.neg(bh), I.Int.neg(bl), I.Int.neg(pi)) == I.Int.neg(Dk.e3(p, ah, al, bh, bl, pi)) : I.Int}:
  Equal.trans(I.Int, Dk.e3(p, ah, al, I.Int.neg(bh), I.Int.neg(bl), I.Int.neg(pi)), E.RNi(p, I.Int.add(I.Int.neg(Dk.e2(p, ah, bh, bl, pi)), I.Int.neg(E.RNi(p, I.Int.mul(al, bh))))), I.Int.neg(Dk.e3(p, ah, al, bh, bl, pi)), Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(Dk.e2(p, ah, I.Int.neg(bh), I.Int.neg(bl), I.Int.neg(pi)), E.RNi(p, I.Int.mul(al, I.Int.neg(bh)))), I.Int.add(I.Int.neg(Dk.e2(p, ah, bh, bl, pi)), I.Int.neg(E.RNi(p, I.Int.mul(al, bh)))), Y.Int.cong2(Dk.e2(p, ah, I.Int.neg(bh), I.Int.neg(bl), I.Int.neg(pi)), I.Int.neg(Dk.e2(p, ah, bh, bl, pi)), E.RNi(p, I.Int.mul(al, I.Int.neg(bh))), I.Int.neg(E.RNi(p, I.Int.mul(al, bh))), Dk.nb.e2(p, ah, bh, bl, pi), RNi.nmr(p, al, bh))), RNi.nadd(p, Dk.e2(p, ah, bh, bl, pi), E.RNi(p, I.Int.mul(al, bh))))

def Dk.nb.e(+p: Nat, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int) -> {Dk.e(p, ah, al, I.Int.neg(bh), I.Int.neg(bl), I.Int.neg(pi)) == I.Int.neg(Dk.e(p, ah, al, bh, bl, pi)) : I.Int}:
  Equal.trans(I.Int, Dk.e(p, ah, al, I.Int.neg(bh), I.Int.neg(bl), I.Int.neg(pi)), E.RNi(p, I.Int.add(I.Int.neg(Dk.e3(p, ah, al, bh, bl, pi)), I.Int.neg(E.RNi(p, I.Int.mul(al, bl))))), I.Int.neg(Dk.e(p, ah, al, bh, bl, pi)), Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(Dk.e3(p, ah, al, I.Int.neg(bh), I.Int.neg(bl), I.Int.neg(pi)), E.RNi(p, I.Int.mul(al, I.Int.neg(bl)))), I.Int.add(I.Int.neg(Dk.e3(p, ah, al, bh, bl, pi)), I.Int.neg(E.RNi(p, I.Int.mul(al, bl)))), Y.Int.cong2(Dk.e3(p, ah, al, I.Int.neg(bh), I.Int.neg(bl), I.Int.neg(pi)), I.Int.neg(Dk.e3(p, ah, al, bh, bl, pi)), E.RNi(p, I.Int.mul(al, I.Int.neg(bl))), I.Int.neg(E.RNi(p, I.Int.mul(al, bl))), Dk.nb.e3(p, ah, al, bh, bl, pi), RNi.nmr(p, al, bl))), RNi.nadd(p, Dk.e3(p, ah, al, bh, bl, pi), E.RNi(p, I.Int.mul(al, bl))))

def TP.na.e(+p: Nat, +s: Nat, +a: I.Int, +b: I.Int) -> {TP.e(p, s, I.Int.neg(a), b) == I.Int.neg(TP.e(p, s, a, b)) : I.Int}:
  Equal.trans(I.Int, Dk.e(p, Sp.h(p, s, I.Int.neg(a)), Sp.l(p, s, I.Int.neg(a)), Sp.h(p, s, b), Sp.l(p, s, b), TP.p(p, I.Int.neg(a), b)), Dk.e(p, I.Int.neg(Sp.h(p, s, a)), Sp.l(p, s, I.Int.neg(a)), Sp.h(p, s, b), Sp.l(p, s, b), TP.p(p, I.Int.neg(a), b)), I.Int.neg(TP.e(p, s, a, b)), Equal.cong(I.Int, I.Int, z => Dk.e(p, z, Sp.l(p, s, I.Int.neg(a)), Sp.h(p, s, b), Sp.l(p, s, b), TP.p(p, I.Int.neg(a), b)), Sp.h(p, s, I.Int.neg(a)), I.Int.neg(Sp.h(p, s, a)), Sp.sym.h(p, s, a)), Equal.trans(I.Int, Dk.e(p, I.Int.neg(Sp.h(p, s, a)), Sp.l(p, s, I.Int.neg(a)), Sp.h(p, s, b), Sp.l(p, s, b), TP.p(p, I.Int.neg(a), b)), Dk.e(p, I.Int.neg(Sp.h(p, s, a)), I.Int.neg(Sp.l(p, s, a)), Sp.h(p, s, b), Sp.l(p, s, b), TP.p(p, I.Int.neg(a), b)), I.Int.neg(TP.e(p, s, a, b)), Equal.cong(I.Int, I.Int, z => Dk.e(p, I.Int.neg(Sp.h(p, s, a)), z, Sp.h(p, s, b), Sp.l(p, s, b), TP.p(p, I.Int.neg(a), b)), Sp.l(p, s, I.Int.neg(a)), I.Int.neg(Sp.l(p, s, a)), Sp.sym.l(p, s, a)), Equal.trans(I.Int, Dk.e(p, I.Int.neg(Sp.h(p, s, a)), I.Int.neg(Sp.l(p, s, a)), Sp.h(p, s, b), Sp.l(p, s, b), TP.p(p, I.Int.neg(a), b)), Dk.e(p, I.Int.neg(Sp.h(p, s, a)), I.Int.neg(Sp.l(p, s, a)), Sp.h(p, s, b), Sp.l(p, s, b), I.Int.neg(TP.p(p, a, b))), I.Int.neg(TP.e(p, s, a, b)), Equal.cong(I.Int, I.Int, z => Dk.e(p, I.Int.neg(Sp.h(p, s, a)), I.Int.neg(Sp.l(p, s, a)), Sp.h(p, s, b), Sp.l(p, s, b), z), TP.p(p, I.Int.neg(a), b), I.Int.neg(TP.p(p, a, b)), RNi.nml(p, a, b)), Dk.na.e(p, Sp.h(p, s, a), Sp.l(p, s, a), Sp.h(p, s, b), Sp.l(p, s, b), TP.p(p, a, b)))))

def TP.nb.e(+p: Nat, +s: Nat, +a: I.Int, +b: I.Int) -> {TP.e(p, s, a, I.Int.neg(b)) == I.Int.neg(TP.e(p, s, a, b)) : I.Int}:
  Equal.trans(I.Int, Dk.e(p, Sp.h(p, s, a), Sp.l(p, s, a), Sp.h(p, s, I.Int.neg(b)), Sp.l(p, s, I.Int.neg(b)), TP.p(p, a, I.Int.neg(b))), Dk.e(p, Sp.h(p, s, a), Sp.l(p, s, a), I.Int.neg(Sp.h(p, s, b)), Sp.l(p, s, I.Int.neg(b)), TP.p(p, a, I.Int.neg(b))), I.Int.neg(TP.e(p, s, a, b)), Equal.cong(I.Int, I.Int, z => Dk.e(p, Sp.h(p, s, a), Sp.l(p, s, a), z, Sp.l(p, s, I.Int.neg(b)), TP.p(p, a, I.Int.neg(b))), Sp.h(p, s, I.Int.neg(b)), I.Int.neg(Sp.h(p, s, b)), Sp.sym.h(p, s, b)), Equal.trans(I.Int, Dk.e(p, Sp.h(p, s, a), Sp.l(p, s, a), I.Int.neg(Sp.h(p, s, b)), Sp.l(p, s, I.Int.neg(b)), TP.p(p, a, I.Int.neg(b))), Dk.e(p, Sp.h(p, s, a), Sp.l(p, s, a), I.Int.neg(Sp.h(p, s, b)), I.Int.neg(Sp.l(p, s, b)), TP.p(p, a, I.Int.neg(b))), I.Int.neg(TP.e(p, s, a, b)), Equal.cong(I.Int, I.Int, z => Dk.e(p, Sp.h(p, s, a), Sp.l(p, s, a), I.Int.neg(Sp.h(p, s, b)), z, TP.p(p, a, I.Int.neg(b))), Sp.l(p, s, I.Int.neg(b)), I.Int.neg(Sp.l(p, s, b)), Sp.sym.l(p, s, b)), Equal.trans(I.Int, Dk.e(p, Sp.h(p, s, a), Sp.l(p, s, a), I.Int.neg(Sp.h(p, s, b)), I.Int.neg(Sp.l(p, s, b)), TP.p(p, a, I.Int.neg(b))), Dk.e(p, Sp.h(p, s, a), Sp.l(p, s, a), I.Int.neg(Sp.h(p, s, b)), I.Int.neg(Sp.l(p, s, b)), I.Int.neg(TP.p(p, a, b))), I.Int.neg(TP.e(p, s, a, b)), Equal.cong(I.Int, I.Int, z => Dk.e(p, Sp.h(p, s, a), Sp.l(p, s, a), I.Int.neg(Sp.h(p, s, b)), I.Int.neg(Sp.l(p, s, b)), z), TP.p(p, a, I.Int.neg(b)), I.Int.neg(TP.p(p, a, b)), RNi.nmr(p, a, b)), Dk.nb.e(p, Sp.h(p, s, a), Sp.l(p, s, a), Sp.h(p, s, b), Sp.l(p, s, b), TP.p(p, a, b)))))

# Normalising
# -----------
# A representable n > 0 is N 2^j / 2^i with N in [2^(p-1), 2^p).

def Lt.dself(+x: Nat, +h: {RD.Nat.lt(0n, x) == True{} : Bool}) -> {RD.Nat.lt(x, Nat.double(x)) == True{} : Bool}:
  +w = RD.Nat.monus(x, 1n)
  +ex : {x == 1n+w : Nat} = BP.Lt.wit(0n, x)(h)
  Equal.trans(Bool, RD.Nat.lt(x, Nat.double(x)), RD.Nat.lt(x, Nat.add(x, 1n+w)), True{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(x, z), Nat.double(x), Nat.add(x, 1n+w), Equal.trans(Nat, Nat.double(x), Nat.add(x, x), Nat.add(x, 1n+w), Y.Nat.double_add(x), Equal.cong(Nat, Nat, z => Nat.add(x, z), x, 1n+w, ex))),
    BP.Lt.self(x, w))

def Nm.top(+p1: Nat, +m: Nat, +hm: {RD.Nat.lt(RD.Nat.pow2(1n+p1), m) == False{} : Bool}, +hh: {RD.Nat.lt(m, RD.Nat.pow2(p1)) == False{} : Bool}, -G: Type,
  k: @i: Nat -> @t: Nat -> @nn: Nat -> {Nat.mul(m, RD.Nat.pow2(i)) == Nat.mul(nn, RD.Nat.pow2(t)) : Nat} -> {RD.Nat.lt(nn, RD.Nat.pow2(1n+p1)) == True{} : Bool} -> {RD.Nat.lt(nn, RD.Nat.pow2(p1)) == False{} : Bool} -> G,
  l: Bool, +el: {RD.Nat.lt(m, RD.Nat.pow2(1n+p1)) == l : Bool}) -> G:
  match l:
    case True{}:
      k(0n, 0n, m, {==}, el, hh)
    case False{}:
      # m = 2^p = 2^(p-1) 2
      +H = RD.Nat.pow2(p1)
      +em : {m == RD.Nat.pow2(1n+p1) : Nat} = Le.anti(m, RD.Nat.pow2(1n+p1), hm, el)
      k(0n, 1n, H,
        Equal.trans(Nat, Nat.mul(m, 1n), m, Nat.mul(H, 2n), NL.Nat.mul_one_r(m),
          Equal.trans(Nat, m, Nat.double(H), Nat.mul(H, 2n), em, Equal.sym(Nat, Nat.mul(H, 2n), Nat.double(H), Equal.trans(Nat, Nat.mul(H, Nat.double(1n)), Nat.double(Nat.mul(H, 1n)), Nat.double(H), R.Nat.mul_double(H, 1n), Equal.cong(Nat, Nat, z => Nat.double(z), Nat.mul(H, 1n), H, NL.Nat.mul_one_r(H)))))),
        Lt.dself(H, BP.Pow2.pos(p1)), E.Lt.irr(H))

# m 2^(1+i) = (2m) 2^i
def Nm.step(+p1: Nat, +m: Nat, -G: Type, k: @i: Nat -> @t: Nat -> @nn: Nat -> {Nat.mul(m, RD.Nat.pow2(i)) == Nat.mul(nn, RD.Nat.pow2(t)) : Nat} -> {RD.Nat.lt(nn, RD.Nat.pow2(1n+p1)) == True{} : Bool} -> {RD.Nat.lt(nn, RD.Nat.pow2(p1)) == False{} : Bool} -> G, +i: Nat, +t: Nat, +nn: Nat,
  +e: {Nat.mul(Nat.double(m), RD.Nat.pow2(i)) == Nat.mul(nn, RD.Nat.pow2(t)) : Nat}, +h1: {RD.Nat.lt(nn, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +h2: {RD.Nat.lt(nn, RD.Nat.pow2(p1)) == False{} : Bool}) -> G:
  +m2 = Nat.double(m)
  k(1n+i, t, nn, Equal.trans(Nat, Nat.mul(m, RD.Nat.pow2(1n+i)), Nat.mul(m2, RD.Nat.pow2(i)), Nat.mul(nn, RD.Nat.pow2(t)),
    Equal.trans(Nat, Nat.mul(m, Nat.double(RD.Nat.pow2(i))), Nat.double(Nat.mul(m, RD.Nat.pow2(i))), Nat.mul(m2, RD.Nat.pow2(i)), R.Nat.mul_double(m, RD.Nat.pow2(i)), Equal.sym(Nat, Nat.mul(m2, RD.Nat.pow2(i)), Nat.double(Nat.mul(m, RD.Nat.pow2(i))), BP.Mul.dbl_l(m, RD.Nat.pow2(i)))), e), h1, h2)

def Nm.go(+p1: Nat, +f: Nat, +m: Nat, +hf: {RD.Nat.lt(Nat.mul(m, RD.Nat.pow2(f)), RD.Nat.pow2(p1)) == False{} : Bool}, +hm: {RD.Nat.lt(RD.Nat.pow2(1n+p1), m) == False{} : Bool}, -G: Type,
  k: @i: Nat -> @t: Nat -> @nn: Nat -> {Nat.mul(m, RD.Nat.pow2(i)) == Nat.mul(nn, RD.Nat.pow2(t)) : Nat} -> {RD.Nat.lt(nn, RD.Nat.pow2(1n+p1)) == True{} : Bool} -> {RD.Nat.lt(nn, RD.Nat.pow2(p1)) == False{} : Bool} -> G,
  l: Bool, +el: {RD.Nat.lt(m, RD.Nat.pow2(p1)) == l : Bool}) -> G:
  match f:
    case 0n:
      match l:
        case False{}:
          Nm.top(p1, m, hm, el, G, k, RD.Nat.lt(m, RD.Nat.pow2(1n+p1)), {==})
        case True{}:
          # m 2^0 >= 2^(p-1) > m
          +hh : {RD.Nat.lt(m, RD.Nat.pow2(p1)) == False{} : Bool} = E.Le.trans(RD.Nat.pow2(p1), Nat.mul(m, 1n), m, hf, E.Le.eq(Nat.mul(m, 1n), m, NL.Nat.mul_one_r(m)))
          Empty.absurd(G, Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(m, RD.Nat.pow2(p1)), True{}, Equal.sym(Bool, RD.Nat.lt(m, RD.Nat.pow2(p1)), False{}, hh), el)))
    case 1n+(+f2):
      match l:
        case False{}:
          Nm.top(p1, m, hm, el, G, k, RD.Nat.lt(m, RD.Nat.pow2(1n+p1)), {==})
        case True{}:
          +H = RD.Nat.pow2(p1)
          +m2 = Nat.double(m)
          +em : {Nat.mul(m, RD.Nat.pow2(1n+f2)) == Nat.mul(m2, RD.Nat.pow2(f2)) : Nat} = Equal.trans(Nat, Nat.mul(m, Nat.double(RD.Nat.pow2(f2))), Nat.double(Nat.mul(m, RD.Nat.pow2(f2))), Nat.mul(m2, RD.Nat.pow2(f2)),
            R.Nat.mul_double(m, RD.Nat.pow2(f2)), Equal.sym(Nat, Nat.mul(m2, RD.Nat.pow2(f2)), Nat.double(Nat.mul(m, RD.Nat.pow2(f2))), BP.Mul.dbl_l(m, RD.Nat.pow2(f2))))
          +hf2 : {RD.Nat.lt(Nat.mul(m2, RD.Nat.pow2(f2)), H) == False{} : Bool} = E.Le.trans(H, Nat.mul(m, RD.Nat.pow2(1n+f2)), Nat.mul(m2, RD.Nat.pow2(f2)), hf, E.Le.eq(Nat.mul(m, RD.Nat.pow2(1n+f2)), Nat.mul(m2, RD.Nat.pow2(f2)), em))
          +hm2 : {RD.Nat.lt(RD.Nat.pow2(1n+p1), m2) == False{} : Bool} = E.Le.dd(m, H, Lt.to_le(m, H, el))
          Nm.go(p1, f2, m2, hf2, hm2, G,
            i => t => nn => e => h1 => h2 => Nm.step(p1, m, G, k, i, t, nn, e, h1, h2),
            RD.Nat.lt(m2, H), {==})

# 1 <= m <= 2^p: m 2^i = N 2^t with N in [2^(p-1), 2^p)
def Nm(+p1: Nat, +m: Nat, +hm: {RD.Nat.lt(RD.Nat.pow2(1n+p1), m) == False{} : Bool}, +h1: {RD.Nat.lt(m, 1n) == False{} : Bool}, -G: Type,
  k: @i: Nat -> @t: Nat -> @nn: Nat -> {Nat.mul(m, RD.Nat.pow2(i)) == Nat.mul(nn, RD.Nat.pow2(t)) : Nat} -> {RD.Nat.lt(nn, RD.Nat.pow2(1n+p1)) == True{} : Bool} -> {RD.Nat.lt(nn, RD.Nat.pow2(p1)) == False{} : Bool} -> G) -> G:
  +H = RD.Nat.pow2(p1)
  +hf : {RD.Nat.lt(Nat.mul(m, H), H) == False{} : Bool} = E.Le.trans(H, Nat.mul(1n, H), Nat.mul(m, H), E.Le.eq(H, Nat.mul(1n, H), Equal.sym(Nat, Nat.mul(1n, H), H, NL.Nat.add_zero_r(H))), Le.mulr(1n, m, H, h1))
  Nm.go(p1, p1, m, hf, hm, G, k, RD.Nat.lt(m, H), {==})

def Nz.one(+n: Nat, +m: Nat, +j: Nat, +e: {n == Nat.mul(m, RD.Nat.pow2(j)) : Nat}, +h0: {RD.Nat.lt(0n, n) == True{} : Bool}) -> {RD.Nat.lt(m, 1n) == False{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({RD.Nat.lt(0n, 1n) == False{} : Bool}, Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(0n, n), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(0n, z), 0n, n, Equal.sym(Nat, n, 0n, e)), h0)))
    case 1n+(+m2):
      BP.Lt.z(m2)

def Nz.step(+p1: Nat, +n: Nat, +mm: Nat, +jj: Nat, +en: {n == Nat.mul(mm, RD.Nat.pow2(jj)) : Nat}, -G: Type, k: @i: Nat -> @j: Nat -> @nn: Nat -> {Nat.mul(n, RD.Nat.pow2(i)) == Nat.mul(nn, RD.Nat.pow2(j)) : Nat} -> {RD.Nat.lt(nn, RD.Nat.pow2(1n+p1)) == True{} : Bool} -> {RD.Nat.lt(nn, RD.Nat.pow2(p1)) == False{} : Bool} -> G, +i: Nat, +t: Nat, +nn: Nat,
  +e: {Nat.mul(mm, RD.Nat.pow2(i)) == Nat.mul(nn, RD.Nat.pow2(t)) : Nat}, +h1: {RD.Nat.lt(nn, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +h2: {RD.Nat.lt(nn, RD.Nat.pow2(p1)) == False{} : Bool}) -> G:
  k(i, Nat.add(t, jj), nn,
      Equal.trans(Nat, Nat.mul(n, RD.Nat.pow2(i)), Nat.mul(Nat.mul(mm, RD.Nat.pow2(jj)), RD.Nat.pow2(i)), Nat.mul(nn, RD.Nat.pow2(Nat.add(t, jj))),
        Equal.cong(Nat, Nat, z => Nat.mul(z, RD.Nat.pow2(i)), n, Nat.mul(mm, RD.Nat.pow2(jj)), en),
        Equal.trans(Nat, Nat.mul(Nat.mul(mm, RD.Nat.pow2(jj)), RD.Nat.pow2(i)), Nat.mul(Nat.mul(nn, RD.Nat.pow2(t)), RD.Nat.pow2(jj)), Nat.mul(nn, RD.Nat.pow2(Nat.add(t, jj))),
          R.NatN.eq2([mm, RD.Nat.pow2(jj), RD.Nat.pow2(i), nn, RD.Nat.pow2(t)], R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(2n)), R.Ml(R.Ml(R.V(3n), R.V(4n)), R.V(1n)), [R.V(1n)], [R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.Ml(R.V(3n), R.V(4n))))], [],
            {==}, (R.NatN.z([mm, RD.Nat.pow2(jj), RD.Nat.pow2(i), nn, RD.Nat.pow2(t)], R.Ml(R.V(0n), R.V(2n)), R.Ml(R.V(3n), R.V(4n)), {==}, {==}, e), Unit{}), Unit{}, {==}, {==}),
          Equal.sym(Nat, Nat.mul(nn, RD.Nat.pow2(Nat.add(t, jj))), Nat.mul(Nat.mul(nn, RD.Nat.pow2(t)), RD.Nat.pow2(jj)), E.Sh.mul(nn, jj, t, Nat.add(t, jj), NL.Nat.add_comm(t, jj))))),
      h1, h2)

# a representable n > 0: n 2^i = N 2^j, N in [2^(p-1), 2^p)
def Nz(+p1: Nat, +n: Nat, +fn: {E.Rn(1n+p1, n) == n : Nat}, +h0: {RD.Nat.lt(0n, n) == True{} : Bool}, -G: Type,
  k: @i: Nat -> @j: Nat -> @nn: Nat -> {Nat.mul(n, RD.Nat.pow2(i)) == Nat.mul(nn, RD.Nat.pow2(j)) : Nat} -> {RD.Nat.lt(nn, RD.Nat.pow2(1n+p1)) == True{} : Bool} -> {RD.Nat.lt(nn, RD.Nat.pow2(p1)) == False{} : Bool} -> G) -> G:
  +p : Nat = 1n+p1
  +mm = E.Fm.m(p, n)
  +jj = E.Fm.j(p, n)
  +en : {n == Nat.mul(mm, RD.Nat.pow2(jj)) : Nat} = E.Fm.of(p1, n, fn)
  Nm(p1, mm, E.Fm.le2(p1, n), Nz.one(n, mm, jj, en, h0), G,
    i => t => nn => e => h1 => h2 => Nz.step(p1, n, mm, jj, en, G, k, i, t, nn, e, h1, h2))

# Zero
# ----

def Rn.z(+p1: Nat) -> {E.Rn(1n+p1, 0n) == 0n : Nat}:
  E.Small(p1, 0n, BP.Lt.z(RD.Nat.pow2(1n+p1)))

def Z1(+p1: Nat, +x: I.Int, +h: {x == I.IPos{0n} : I.Int}) -> {E.RNi(1n+p1, x) == I.IPos{0n} : I.Int}:
  Equal.trans(I.Int, E.RNi(1n+p1, x), E.RNi(1n+p1, I.IPos{0n}), I.IPos{0n}, Equal.cong(I.Int, I.Int, z => E.RNi(1n+p1, z), x, I.IPos{0n}, h), Equal.cong(Nat, I.Int, z => I.IPos{z}, E.Rn(1n+p1, 0n), 0n, Rn.z(p1)))

def Int.mul0l(+x: I.Int) -> {I.Int.mul(I.IPos{0n}, x) == I.IPos{0n} : I.Int}:
  match x:
    case I.IPos{+n}:
      {==}
    case I.INeg{+n}:
      {==}

def Int.mul0r(+x: I.Int) -> {I.Int.mul(x, I.IPos{0n}) == I.IPos{0n} : I.Int}:
  match x:
    case I.IPos{+n}:
      Equal.trans(I.Int, I.Int.mul(I.IPos{n}, I.IPos{0n}), I.IPos{Nat.mul(n, 0n)}, I.IPos{0n}, Int.mulpp(n, 0n), Equal.cong(Nat, I.Int, z => I.IPos{z}, Nat.mul(n, 0n), 0n, NL.Nat.mul_zero_r(n)))
    case I.INeg{+n}:
      {==}

def V.z(+p1: Nat, +s: Nat) -> {V.hi(1n+p1, s, 0n) == 0n : Nat}:
  +p : Nat = 1n+p1
  +eg : {V.g(p, s, 0n) == 0n : Nat} = Equal.trans(Nat, V.g(p, s, 0n), E.Rn(p, 0n), 0n, Equal.cong(Nat, Nat, z => E.Rn(p, z), Nat.mul(1n+RD.Nat.pow2(s), 0n), 0n, NL.Nat.mul_zero_r(1n+RD.Nat.pow2(s))), Rn.z(p1))
  +ex : {V.x(p, s, 0n) == 0n : Nat} = Equal.cong(Nat, Nat, z => RD.Nat.monus(z, 0n), V.g(p, s, 0n), 0n, eg)
  +ed : {V.d(p, s, 0n) == 0n : Nat} = Equal.trans(Nat, V.d(p, s, 0n), E.Rn(p, 0n), 0n, Equal.cong(Nat, Nat, z => E.Rn(p, z), V.x(p, s, 0n), 0n, ex), Rn.z(p1))
  Equal.trans(Nat, V.hi(p, s, 0n), RD.Nat.monus(0n, V.d(p, s, 0n)), 0n, Equal.cong(Nat, Nat, z => RD.Nat.monus(z, V.d(p, s, 0n)), V.g(p, s, 0n), 0n, eg), Equal.cong(Nat, Nat, z => RD.Nat.monus(0n, z), V.d(p, s, 0n), 0n, ed))

def Sp.z.h(+p1: Nat, +s: Nat) -> {Sp.h(1n+p1, s, I.IPos{0n}) == I.IPos{0n} : I.Int}:
  +p : Nat = 1n+p1
  +hi = V.hi(p, s, 0n)
  Equal.trans(I.Int, Sp.h(p, s, I.IPos{0n}), I.IPos{hi}, I.IPos{0n}, Pair.fst({Sp.h(p, s, I.IPos{0n}) == I.IPos{hi} : I.Int}, {Sp.l(p, s, I.IPos{0n}) == I.Int.add(I.IPos{0n}, I.Int.neg(I.IPos{hi})) : I.Int}, Sp.pos(p1, s, 0n, Rn.z(p1))),
    Equal.cong(Nat, I.Int, z => I.IPos{z}, hi, 0n, V.z(p1, s)))

def Sp.z.l(+p1: Nat, +s: Nat) -> {Sp.l(1n+p1, s, I.IPos{0n}) == I.IPos{0n} : I.Int}:
  +p : Nat = 1n+p1
  +hi = V.hi(p, s, 0n)
  Equal.trans(I.Int, Sp.l(p, s, I.IPos{0n}), I.Int.add(I.IPos{0n}, I.Int.neg(I.IPos{hi})), I.IPos{0n}, Pair.snd({Sp.h(p, s, I.IPos{0n}) == I.IPos{hi} : I.Int}, {Sp.l(p, s, I.IPos{0n}) == I.Int.add(I.IPos{0n}, I.Int.neg(I.IPos{hi})) : I.Int}, Sp.pos(p1, s, 0n, Rn.z(p1))),
    Equal.cong(Nat, I.Int, z => I.Int.add(I.IPos{0n}, I.Int.neg(I.IPos{z})), hi, 0n, V.z(p1, s)))

def Dk.zl(+p1: Nat, +bh: I.Int, +bl: I.Int) -> {Dk.e(1n+p1, I.IPos{0n}, I.IPos{0n}, bh, bl, I.IPos{0n}) == I.IPos{0n} : I.Int}:
  +p : Nat = 1n+p1
  +h1 : {Dk.e1(p, I.IPos{0n}, bh, I.IPos{0n}) == I.IPos{0n} : I.Int} = Z1(p1, I.Int.add(E.RNi(p, I.Int.mul(I.IPos{0n}, bh)), I.Int.neg(I.IPos{0n})), Equal.cong(I.Int, I.Int, z => I.Int.add(z, I.Int.neg(I.IPos{0n})), E.RNi(p, I.Int.mul(I.IPos{0n}, bh)), I.IPos{0n}, Z1(p1, I.Int.mul(I.IPos{0n}, bh), Int.mul0l(bh))))
  +h2 : {Dk.e2(p, I.IPos{0n}, bh, bl, I.IPos{0n}) == I.IPos{0n} : I.Int} = Z1(p1, I.Int.add(Dk.e1(p, I.IPos{0n}, bh, I.IPos{0n}), E.RNi(p, I.Int.mul(I.IPos{0n}, bl))), Y.Int.cong2(Dk.e1(p, I.IPos{0n}, bh, I.IPos{0n}), I.IPos{0n}, E.RNi(p, I.Int.mul(I.IPos{0n}, bl)), I.IPos{0n}, h1, Z1(p1, I.Int.mul(I.IPos{0n}, bl), Int.mul0l(bl))))
  +h3 : {Dk.e3(p, I.IPos{0n}, I.IPos{0n}, bh, bl, I.IPos{0n}) == I.IPos{0n} : I.Int} = Z1(p1, I.Int.add(Dk.e2(p, I.IPos{0n}, bh, bl, I.IPos{0n}), E.RNi(p, I.Int.mul(I.IPos{0n}, bh))), Y.Int.cong2(Dk.e2(p, I.IPos{0n}, bh, bl, I.IPos{0n}), I.IPos{0n}, E.RNi(p, I.Int.mul(I.IPos{0n}, bh)), I.IPos{0n}, h2, Z1(p1, I.Int.mul(I.IPos{0n}, bh), Int.mul0l(bh))))
  Z1(p1, I.Int.add(Dk.e3(p, I.IPos{0n}, I.IPos{0n}, bh, bl, I.IPos{0n}), E.RNi(p, I.Int.mul(I.IPos{0n}, bl))), Y.Int.cong2(Dk.e3(p, I.IPos{0n}, I.IPos{0n}, bh, bl, I.IPos{0n}), I.IPos{0n}, E.RNi(p, I.Int.mul(I.IPos{0n}, bl)), I.IPos{0n}, h3, Z1(p1, I.Int.mul(I.IPos{0n}, bl), Int.mul0l(bl))))

def Dk.zr(+p1: Nat, +ah: I.Int, +al: I.Int) -> {Dk.e(1n+p1, ah, al, I.IPos{0n}, I.IPos{0n}, I.IPos{0n}) == I.IPos{0n} : I.Int}:
  +p : Nat = 1n+p1
  +h1 : {Dk.e1(p, ah, I.IPos{0n}, I.IPos{0n}) == I.IPos{0n} : I.Int} = Z1(p1, I.Int.add(E.RNi(p, I.Int.mul(ah, I.IPos{0n})), I.Int.neg(I.IPos{0n})), Equal.cong(I.Int, I.Int, z => I.Int.add(z, I.Int.neg(I.IPos{0n})), E.RNi(p, I.Int.mul(ah, I.IPos{0n})), I.IPos{0n}, Z1(p1, I.Int.mul(ah, I.IPos{0n}), Int.mul0r(ah))))
  +h2 : {Dk.e2(p, ah, I.IPos{0n}, I.IPos{0n}, I.IPos{0n}) == I.IPos{0n} : I.Int} = Z1(p1, I.Int.add(Dk.e1(p, ah, I.IPos{0n}, I.IPos{0n}), E.RNi(p, I.Int.mul(ah, I.IPos{0n}))), Y.Int.cong2(Dk.e1(p, ah, I.IPos{0n}, I.IPos{0n}), I.IPos{0n}, E.RNi(p, I.Int.mul(ah, I.IPos{0n})), I.IPos{0n}, h1, Z1(p1, I.Int.mul(ah, I.IPos{0n}), Int.mul0r(ah))))
  +h3 : {Dk.e3(p, ah, al, I.IPos{0n}, I.IPos{0n}, I.IPos{0n}) == I.IPos{0n} : I.Int} = Z1(p1, I.Int.add(Dk.e2(p, ah, I.IPos{0n}, I.IPos{0n}, I.IPos{0n}), E.RNi(p, I.Int.mul(al, I.IPos{0n}))), Y.Int.cong2(Dk.e2(p, ah, I.IPos{0n}, I.IPos{0n}, I.IPos{0n}), I.IPos{0n}, E.RNi(p, I.Int.mul(al, I.IPos{0n})), I.IPos{0n}, h2, Z1(p1, I.Int.mul(al, I.IPos{0n}), Int.mul0r(al))))
  Z1(p1, I.Int.add(Dk.e3(p, ah, al, I.IPos{0n}, I.IPos{0n}, I.IPos{0n}), E.RNi(p, I.Int.mul(al, I.IPos{0n}))), Y.Int.cong2(Dk.e3(p, ah, al, I.IPos{0n}, I.IPos{0n}, I.IPos{0n}), I.IPos{0n}, E.RNi(p, I.Int.mul(al, I.IPos{0n})), I.IPos{0n}, h3, Z1(p1, I.Int.mul(al, I.IPos{0n}), Int.mul0r(al))))

# a zero input gives pi = e = 0
def TP.zl(+p1: Nat, +s: Nat, +b: I.Int) -> {I.Int.add(TP.p(1n+p1, I.IPos{0n}, b), TP.e(1n+p1, s, I.IPos{0n}, b)) == I.Int.mul(I.IPos{0n}, b) : I.Int}:
  +p : Nat = 1n+p1
  +bh = Sp.h(p, s, b)
  +bl = Sp.l(p, s, b)
  +hp : {TP.p(p, I.IPos{0n}, b) == I.IPos{0n} : I.Int} = Z1(p1, I.Int.mul(I.IPos{0n}, b), Int.mul0l(b))
  +e1 = Equal.cong(I.Int, I.Int, z => Dk.e(p, z, Sp.l(p, s, I.IPos{0n}), bh, bl, TP.p(p, I.IPos{0n}, b)), Sp.h(p, s, I.IPos{0n}), I.IPos{0n}, Sp.z.h(p1, s))
  +e2 = Equal.cong(I.Int, I.Int, z => Dk.e(p, I.IPos{0n}, z, bh, bl, TP.p(p, I.IPos{0n}, b)), Sp.l(p, s, I.IPos{0n}), I.IPos{0n}, Sp.z.l(p1, s))
  +e3 = Equal.cong(I.Int, I.Int, z => Dk.e(p, I.IPos{0n}, I.IPos{0n}, bh, bl, z), TP.p(p, I.IPos{0n}, b), I.IPos{0n}, hp)
  +he : {TP.e(p, s, I.IPos{0n}, b) == I.IPos{0n} : I.Int} = Equal.trans(I.Int, TP.e(p, s, I.IPos{0n}, b), Dk.e(p, I.IPos{0n}, Sp.l(p, s, I.IPos{0n}), bh, bl, TP.p(p, I.IPos{0n}, b)), I.IPos{0n}, e1,
    Equal.trans(I.Int, Dk.e(p, I.IPos{0n}, Sp.l(p, s, I.IPos{0n}), bh, bl, TP.p(p, I.IPos{0n}, b)), Dk.e(p, I.IPos{0n}, I.IPos{0n}, bh, bl, TP.p(p, I.IPos{0n}, b)), I.IPos{0n}, e2,
      Equal.trans(I.Int, Dk.e(p, I.IPos{0n}, I.IPos{0n}, bh, bl, TP.p(p, I.IPos{0n}, b)), Dk.e(p, I.IPos{0n}, I.IPos{0n}, bh, bl, I.IPos{0n}), I.IPos{0n}, e3, Dk.zl(p1, bh, bl))))
  Equal.trans(I.Int, I.Int.add(TP.p(p, I.IPos{0n}, b), TP.e(p, s, I.IPos{0n}, b)), I.IPos{0n}, I.Int.mul(I.IPos{0n}, b), Y.Int.cong2(TP.p(p, I.IPos{0n}, b), I.IPos{0n}, TP.e(p, s, I.IPos{0n}, b), I.IPos{0n}, hp, he), Equal.sym(I.Int, I.Int.mul(I.IPos{0n}, b), I.IPos{0n}, Int.mul0l(b)))

def TP.zr(+p1: Nat, +s: Nat, +a: I.Int) -> {I.Int.add(TP.p(1n+p1, a, I.IPos{0n}), TP.e(1n+p1, s, a, I.IPos{0n})) == I.Int.mul(a, I.IPos{0n}) : I.Int}:
  +p : Nat = 1n+p1
  +ah = Sp.h(p, s, a)
  +al = Sp.l(p, s, a)
  +hp : {TP.p(p, a, I.IPos{0n}) == I.IPos{0n} : I.Int} = Z1(p1, I.Int.mul(a, I.IPos{0n}), Int.mul0r(a))
  +e1 = Equal.cong(I.Int, I.Int, z => Dk.e(p, ah, al, z, Sp.l(p, s, I.IPos{0n}), TP.p(p, a, I.IPos{0n})), Sp.h(p, s, I.IPos{0n}), I.IPos{0n}, Sp.z.h(p1, s))
  +e2 = Equal.cong(I.Int, I.Int, z => Dk.e(p, ah, al, I.IPos{0n}, z, TP.p(p, a, I.IPos{0n})), Sp.l(p, s, I.IPos{0n}), I.IPos{0n}, Sp.z.l(p1, s))
  +e3 = Equal.cong(I.Int, I.Int, z => Dk.e(p, ah, al, I.IPos{0n}, I.IPos{0n}, z), TP.p(p, a, I.IPos{0n}), I.IPos{0n}, hp)
  +he : {TP.e(p, s, a, I.IPos{0n}) == I.IPos{0n} : I.Int} = Equal.trans(I.Int, TP.e(p, s, a, I.IPos{0n}), Dk.e(p, ah, al, I.IPos{0n}, Sp.l(p, s, I.IPos{0n}), TP.p(p, a, I.IPos{0n})), I.IPos{0n}, e1,
    Equal.trans(I.Int, Dk.e(p, ah, al, I.IPos{0n}, Sp.l(p, s, I.IPos{0n}), TP.p(p, a, I.IPos{0n})), Dk.e(p, ah, al, I.IPos{0n}, I.IPos{0n}, TP.p(p, a, I.IPos{0n})), I.IPos{0n}, e2,
      Equal.trans(I.Int, Dk.e(p, ah, al, I.IPos{0n}, I.IPos{0n}, TP.p(p, a, I.IPos{0n})), Dk.e(p, ah, al, I.IPos{0n}, I.IPos{0n}, I.IPos{0n}), I.IPos{0n}, e3, Dk.zr(p1, ah, al))))
  Equal.trans(I.Int, I.Int.add(TP.p(p, a, I.IPos{0n}), TP.e(p, s, a, I.IPos{0n})), I.IPos{0n}, I.Int.mul(a, I.IPos{0n}), Y.Int.cong2(TP.p(p, a, I.IPos{0n}), I.IPos{0n}, TP.e(p, s, a, I.IPos{0n}), I.IPos{0n}, hp, he), Equal.sym(I.Int, I.Int.mul(a, I.IPos{0n}), I.IPos{0n}, Int.mul0r(a)))

# All representable inputs
# ------------------------

def Fx(+p: Nat, +s: Nat, +a: I.Int, +b: I.Int) -> I.Int:
  I.Int.add(TP.p(p, a, b), TP.e(p, s, a, b))

def Sh.eq(+i: Nat, +j: Nat, +n: Nat, +nn: Nat, +e: {Nat.mul(n, RD.Nat.pow2(i)) == Nat.mul(nn, RD.Nat.pow2(j)) : Nat}) -> {D.Int.sh(i, I.IPos{n}) == D.Int.sh(j, I.IPos{nn}) : I.Int}:
  Equal.trans(I.Int, D.Int.sh(i, I.IPos{n}), I.IPos{Nat.mul(n, RD.Nat.pow2(i))}, D.Int.sh(j, I.IPos{nn}), R.Sh.ipos(i, n),
    Equal.trans(I.Int, I.IPos{Nat.mul(n, RD.Nat.pow2(i))}, I.IPos{Nat.mul(nn, RD.Nat.pow2(j))}, D.Int.sh(j, I.IPos{nn}), Equal.cong(Nat, I.Int, z => I.IPos{z}, Nat.mul(n, RD.Nat.pow2(i)), Nat.mul(nn, RD.Nat.pow2(j)), e),
      Equal.sym(I.Int, D.Int.sh(j, I.IPos{nn}), I.IPos{Nat.mul(nn, RD.Nat.pow2(j))}, R.Sh.ipos(j, nn))))

# n 2^i = N 2^j and m 2^k = M 2^l with N, M normalised: scale, apply
# TwoProd.norm, scale back
def TP.asm(+s2: Nat, +n: Nat, +m: Nat, +i: Nat, +j: Nat, +nn: Nat, +e1: {Nat.mul(n, RD.Nat.pow2(i)) == Nat.mul(nn, RD.Nat.pow2(j)) : Nat}, +hnn1: {RD.Nat.lt(nn, RD.Nat.pow2(1n+Nat.add(1n+1n+s2, 1n+s2))) == True{} : Bool}, +hnn2: {RD.Nat.lt(nn, RD.Nat.pow2(Nat.add(1n+1n+s2, 1n+s2))) == False{} : Bool},
  +k: Nat, +l: Nat, +mm: Nat, +e2: {Nat.mul(m, RD.Nat.pow2(k)) == Nat.mul(mm, RD.Nat.pow2(l)) : Nat}, +hmm1: {RD.Nat.lt(mm, RD.Nat.pow2(1n+Nat.add(1n+1n+s2, 1n+s2))) == True{} : Bool}, +hmm2: {RD.Nat.lt(mm, RD.Nat.pow2(Nat.add(1n+1n+s2, 1n+s2))) == False{} : Bool})
  -> {Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, I.IPos{n}, I.IPos{m}) == I.Int.mul(I.IPos{n}, I.IPos{m}) : I.Int}:
  +a : I.Int = I.IPos{n}
  +b : I.Int = I.IPos{m}
  +a2 : I.Int = I.IPos{nn}
  +b2 : I.Int = I.IPos{mm}
  +ea = Sh.eq(i, j, n, nn, e1)
  +eb = Sh.eq(k, l, m, mm, e2)
  +ik = Nat.add(i, k)
  +jl = Nat.add(j, l)
  +x = Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a, b)
  +q1 = Y.Int.sh_add(ik, TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), a, b), TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a, b))
  +q2 = Y.Int.cong2(D.Int.sh(ik, TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), a, b)), TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), D.Int.sh(i, a), D.Int.sh(k, b)), D.Int.sh(ik, TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a, b)), TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Int.sh(i, a), D.Int.sh(k, b)),
    Equal.sym(I.Int, TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), D.Int.sh(i, a), D.Int.sh(k, b)), D.Int.sh(ik, TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), a, b)), TP.sh.p(1n+Nat.add(1n+1n+s2, 1n+s2), i, k, a, b)), Equal.sym(I.Int, TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Int.sh(i, a), D.Int.sh(k, b)), D.Int.sh(ik, TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a, b)), TP.sh.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, i, k, a, b)))
  +q3 = Equal.trans(I.Int, Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Int.sh(i, a), D.Int.sh(k, b)), Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Int.sh(j, a2), D.Int.sh(k, b)), Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Int.sh(j, a2), D.Int.sh(l, b2)), Equal.cong(I.Int, I.Int, z => Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, z, D.Int.sh(k, b)), D.Int.sh(i, a), D.Int.sh(j, a2), ea), Equal.cong(I.Int, I.Int, z => Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Int.sh(j, a2), z), D.Int.sh(k, b), D.Int.sh(l, b2), eb))
  +q4 = Y.Int.cong2(TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), D.Int.sh(j, a2), D.Int.sh(l, b2)), D.Int.sh(jl, TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), a2, b2)), TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Int.sh(j, a2), D.Int.sh(l, b2)), D.Int.sh(jl, TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a2, b2)), TP.sh.p(1n+Nat.add(1n+1n+s2, 1n+s2), j, l, a2, b2), TP.sh.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, j, l, a2, b2))
  +q5 = Equal.sym(I.Int, D.Int.sh(jl, Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a2, b2)), I.Int.add(D.Int.sh(jl, TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), a2, b2)), D.Int.sh(jl, TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a2, b2))), Y.Int.sh_add(jl, TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), a2, b2), TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a2, b2)))
  +q6 = Equal.cong(I.Int, I.Int, z => D.Int.sh(jl, z), Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a2, b2), I.Int.mul(a2, b2), TwoProd.norm(s2, nn, mm, hnn1, hnn2, hmm1, hmm2))
  +q7 = Equal.sym(I.Int, I.Int.mul(D.Int.sh(j, a2), D.Int.sh(l, b2)), D.Int.sh(jl, I.Int.mul(a2, b2)), Sh.mul2(j, l, a2, b2))
  +q8 = Equal.trans(I.Int, I.Int.mul(D.Int.sh(j, a2), D.Int.sh(l, b2)), I.Int.mul(D.Int.sh(i, a), D.Int.sh(l, b2)), I.Int.mul(D.Int.sh(i, a), D.Int.sh(k, b)), Equal.cong(I.Int, I.Int, z => I.Int.mul(z, D.Int.sh(l, b2)), D.Int.sh(j, a2), D.Int.sh(i, a), Equal.sym(I.Int, D.Int.sh(i, a), D.Int.sh(j, a2), ea)), Equal.cong(I.Int, I.Int, z => I.Int.mul(D.Int.sh(i, a), z), D.Int.sh(l, b2), D.Int.sh(k, b), Equal.sym(I.Int, D.Int.sh(k, b), D.Int.sh(l, b2), eb)))
  +q9 = Sh.mul2(i, k, a, b)
  +c1 = Equal.trans(I.Int, D.Int.sh(ik, x), I.Int.add(D.Int.sh(ik, TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), a, b)), D.Int.sh(ik, TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a, b))), Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Int.sh(i, a), D.Int.sh(k, b)), q1, q2)
  +c2 = Equal.trans(I.Int, D.Int.sh(ik, x), Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Int.sh(i, a), D.Int.sh(k, b)), Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Int.sh(j, a2), D.Int.sh(l, b2)), c1, q3)
  +c3 = Equal.trans(I.Int, D.Int.sh(ik, x), Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Int.sh(j, a2), D.Int.sh(l, b2)), I.Int.add(D.Int.sh(jl, TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), a2, b2)), D.Int.sh(jl, TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a2, b2))), c2, q4)
  +c4 = Equal.trans(I.Int, D.Int.sh(ik, x), I.Int.add(D.Int.sh(jl, TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), a2, b2)), D.Int.sh(jl, TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a2, b2))), D.Int.sh(jl, Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a2, b2)), c3, q5)
  +c5 = Equal.trans(I.Int, D.Int.sh(ik, x), D.Int.sh(jl, Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a2, b2)), D.Int.sh(jl, I.Int.mul(a2, b2)), c4, q6)
  +c6 = Equal.trans(I.Int, D.Int.sh(ik, x), D.Int.sh(jl, I.Int.mul(a2, b2)), I.Int.mul(D.Int.sh(j, a2), D.Int.sh(l, b2)), c5, q7)
  +c7 = Equal.trans(I.Int, D.Int.sh(ik, x), I.Int.mul(D.Int.sh(j, a2), D.Int.sh(l, b2)), I.Int.mul(D.Int.sh(i, a), D.Int.sh(k, b)), c6, q8)
  +c8 = Equal.trans(I.Int, D.Int.sh(ik, x), I.Int.mul(D.Int.sh(i, a), D.Int.sh(k, b)), D.Int.sh(ik, I.Int.mul(a, b)), c7, q9)
  Y.Int.sh_inj(ik, x, I.Int.mul(a, b))(c8)

def TP.pos(+s2: Nat, +n: Nat, +m: Nat, +fn: {E.Rn(1n+Nat.add(1n+1n+s2, 1n+s2), n) == n : Nat}, +fm: {E.Rn(1n+Nat.add(1n+1n+s2, 1n+s2), m) == m : Nat})
  -> {Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, I.IPos{n}, I.IPos{m}) == I.Int.mul(I.IPos{n}, I.IPos{m}) : I.Int}:
  match n:
    case 0n:
      TP.zl(Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, I.IPos{m})
    case 1n+(+n2):
      match m:
        case 0n:
          TP.zr(Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, I.IPos{1n+n2})
        case 1n+(+m2):
          Nz(Nat.add(1n+1n+s2, 1n+s2), 1n+n2, fn, {==}, {Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, I.IPos{1n+n2}, I.IPos{1n+m2}) == I.Int.mul(I.IPos{1n+n2}, I.IPos{1n+m2}) : I.Int},
            i => j => nn => e1 => h1 => h2 => Nz(Nat.add(1n+1n+s2, 1n+s2), 1n+m2, fm, {==}, {Fx(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, I.IPos{1n+n2}, I.IPos{1n+m2}) == I.Int.mul(I.IPos{1n+n2}, I.IPos{1n+m2}) : I.Int},
              k => l => mm => e2 => h3 => h4 => TP.asm(s2, 1n+n2, 1n+m2, i, j, nn, e1, h1, h2, k, l, mm, e2, h3, h4)))

def TP.ok.na(+p: Nat, +s: Nat, +a: I.Int, +b: I.Int, +h: {Fx(p, s, a, b) == I.Int.mul(a, b) : I.Int}) -> {Fx(p, s, I.Int.neg(a), b) == I.Int.mul(I.Int.neg(a), b) : I.Int}:
  +x = TP.p(p, a, b)
  +y = TP.e(p, s, a, b)
  Equal.trans(I.Int, Fx(p, s, I.Int.neg(a), b), I.Int.add(I.Int.neg(x), I.Int.neg(y)), I.Int.mul(I.Int.neg(a), b), Y.Int.cong2(TP.p(p, I.Int.neg(a), b), I.Int.neg(x), TP.e(p, s, I.Int.neg(a), b), I.Int.neg(y), RNi.nml(p, a, b), TP.na.e(p, s, a, b)), Equal.trans(I.Int, I.Int.add(I.Int.neg(x), I.Int.neg(y)), I.Int.neg(I.Int.mul(a, b)), I.Int.mul(I.Int.neg(a), b), Equal.trans(I.Int, I.Int.add(I.Int.neg(x), I.Int.neg(y)), I.Int.neg(I.Int.add(x, y)), I.Int.neg(I.Int.mul(a, b)), BP.IntN([x, y], R.Ad(R.Ng(R.V(0n)), R.Ng(R.V(1n))), R.Ng(R.Ad(R.V(0n), R.V(1n))), [], [], {==}, Unit{}), Equal.cong(I.Int, I.Int, z => I.Int.neg(z), I.Int.add(x, y), I.Int.mul(a, b), h)), BP.IntN([a, b], R.Ng(R.Ml(R.V(0n), R.V(1n))), R.Ml(R.Ng(R.V(0n)), R.V(1n)), [], [], {==}, Unit{})))

def TP.ok.nb(+p: Nat, +s: Nat, +a: I.Int, +b: I.Int, +h: {Fx(p, s, a, b) == I.Int.mul(a, b) : I.Int}) -> {Fx(p, s, a, I.Int.neg(b)) == I.Int.mul(a, I.Int.neg(b)) : I.Int}:
  +x = TP.p(p, a, b)
  +y = TP.e(p, s, a, b)
  Equal.trans(I.Int, Fx(p, s, a, I.Int.neg(b)), I.Int.add(I.Int.neg(x), I.Int.neg(y)), I.Int.mul(a, I.Int.neg(b)), Y.Int.cong2(TP.p(p, a, I.Int.neg(b)), I.Int.neg(x), TP.e(p, s, a, I.Int.neg(b)), I.Int.neg(y), RNi.nmr(p, a, b), TP.nb.e(p, s, a, b)), Equal.trans(I.Int, I.Int.add(I.Int.neg(x), I.Int.neg(y)), I.Int.neg(I.Int.mul(a, b)), I.Int.mul(a, I.Int.neg(b)), Equal.trans(I.Int, I.Int.add(I.Int.neg(x), I.Int.neg(y)), I.Int.neg(I.Int.add(x, y)), I.Int.neg(I.Int.mul(a, b)), BP.IntN([x, y], R.Ad(R.Ng(R.V(0n)), R.Ng(R.V(1n))), R.Ng(R.Ad(R.V(0n), R.V(1n))), [], [], {==}, Unit{}), Equal.cong(I.Int, I.Int, z => I.Int.neg(z), I.Int.add(x, y), I.Int.mul(a, b), h)), BP.IntN([a, b], R.Ng(R.Ml(R.V(0n), R.V(1n))), R.Ml(R.V(0n), R.Ng(R.V(1n))), [], [], {==}, Unit{})))

# Dekker's product is exact: for p = 2s with s >= 2 and every representable
# a, b, pi = RN(a b) and num/df32.bend's e give pi + e = a b
def TwoProd(+s2: Nat, +a: I.Int, +b: I.Int, +fa: {E.Rn(1n+Nat.add(1n+1n+s2, 1n+s2), RD.Int.mag(a)) == RD.Int.mag(a) : Nat}, +fb: {E.Rn(1n+Nat.add(1n+1n+s2, 1n+s2), RD.Int.mag(b)) == RD.Int.mag(b) : Nat})
  -> {I.Int.add(TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), a, b), TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, a, b)) == I.Int.mul(a, b) : I.Int}:
  match a b:
    case I.IPos{+n} I.IPos{+m}:
      TP.pos(s2, n, m, fa, fb)
    case I.INeg{+x} I.IPos{+m}:
      TP.ok.na(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, I.IPos{1n+x}, I.IPos{m}, TP.pos(s2, 1n+x, m, fa, fb))
    case I.IPos{+n} I.INeg{+y}:
      TP.ok.nb(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, I.IPos{n}, I.IPos{1n+y}, TP.pos(s2, n, 1n+y, fa, fb))
    case I.INeg{+x} I.INeg{+y}:
      TP.ok.na(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, I.IPos{1n+x}, I.INeg{y}, TP.ok.nb(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, I.IPos{1n+x}, I.IPos{1n+y}, TP.pos(s2, 1n+x, 1n+y, fa, fb)))

# In dyadic arithmetic
# --------------------
# Rounding to p bits commutes with the grid: R(N / 2^k) = R(N) / 2^k
# (Rne.of, any k), and binary32's rounding does on the grid 2^-149 (FlL,
# subnormals included). So the split and Dekker's product in Dy arithmetic
# are the integer ones above, divided by 2^k.

# R(N / 2^k) = RNi(N) / 2^k, binary rounding with no exponent bounds
def Rne.of(+p1: Nat, +k: Nat, +nn: I.Int) -> {RD.Dy.rne(1n+p1, D.Dy.of(k, nn)) == D.Dy.of(k, E.RNi(1n+p1, nn)) : D.Dy}:
  +p : Nat = 1n+p1
  +x = D.Dy.of(k, nn)
  +d = D.Dy.den(x)
  +n = D.Dy.num(x)
  +j = RD.Nat.monus(k, d)
  +r = E.Rn(p, RD.Int.mag(n))
  +ek = E.Le.wit(d, k, E.Of.den.go(k, nn, D.Int.even(nn), {==}))
  +en = E.Num.sh(k, nn)
  +er = Equal.trans(I.Int, E.RNi(p, nn), E.RNi(p, D.Int.sh(j, n)), D.Int.sh(j, RD.Int.signed(n, r)), Equal.cong(I.Int, I.Int, z => E.RNi(p, z), nn, D.Int.sh(j, n), en), E.RNi.sh(p, j, n))
  Equal.sym(D.Dy, D.Dy.of(k, E.RNi(p, nn)), D.Dy.of(d, RD.Int.signed(n, r)),
    Equal.trans(D.Dy, D.Dy.of(k, E.RNi(p, nn)), D.Dy.of(Nat.add(d, j), D.Int.sh(j, RD.Int.signed(n, r))), D.Dy.of(d, RD.Int.signed(n, r)),
      Y.Of.cong(k, Nat.add(d, j), E.RNi(p, nn), D.Int.sh(j, RD.Int.signed(n, r)), ek, er), Y.Of.shift(j, d, RD.Int.signed(n, r))))

# a / 2^k1 times b / 2^k2 is a b / 2^(k1 + k2)
def Mul.of(+k1: Nat, +a: I.Int, +k2: Nat, +b: I.Int) -> {D.Dy.mul(D.Dy.of(k1, a), D.Dy.of(k2, b)) == D.Dy.of(Nat.add(k1, k2), I.Int.mul(a, b)) : D.Dy}:
  +nx = D.Dy.num(D.Dy.of(k1, a))
  +ny = D.Dy.num(D.Dy.of(k2, b))
  +dx = D.Dy.den(D.Dy.of(k1, a))
  +dy = D.Dy.den(D.Dy.of(k2, b))
  +env : List<&2, I.Int> = [nx, ny, a, b, Y.P(k1), Y.P(k2), Y.P(dx), Y.P(dy), Y.P(Nat.add(k1, k2)), Y.P(Nat.add(dx, dy))]
  Y.Of.eqvP(Nat.add(dx, dy), Nat.add(k1, k2), I.Int.mul(nx, ny), I.Int.mul(a, b), BP.IntN(env, R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(8n)), R.Ml(R.Ml(R.V(2n), R.V(3n)), R.V(9n)), [R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(1n), R.V(5n)), R.Ml(R.V(2n), R.V(6n)), R.Ng(R.Ml(R.V(2n), R.V(3n)))], [R.Ad(R.V(8n), R.Ng(R.Ml(R.V(4n), R.V(5n)))), R.Ad(R.Ml(R.V(0n), R.V(4n)), R.Ng(R.Ml(R.V(2n), R.V(6n)))), R.Ad(R.Ml(R.V(1n), R.V(5n)), R.Ng(R.Ml(R.V(3n), R.V(7n)))), R.Ad(R.V(9n), R.Ng(R.Ml(R.V(6n), R.V(7n))))], {==}, (IntZ(env, R.V(8n), R.Ml(R.V(4n), R.V(5n)), Y.P.add(k1, k2)), (IntZ(env, R.Ml(R.V(0n), R.V(4n)), R.Ml(R.V(2n), R.V(6n)), Y.Of.valP(k1, a)), (IntZ(env, R.Ml(R.V(1n), R.V(5n)), R.Ml(R.V(3n), R.V(7n)), Y.Of.valP(k2, b)), (IntZ(env, R.V(9n), R.Ml(R.V(6n), R.V(7n)), Y.P.add(dx, dy)), Unit{}))))))

def Dsub(+k: Nat, +a: I.Int, +b: I.Int) -> {D.Dy.add(D.Dy.of(k, a), D.Dy.neg(D.Dy.of(k, b))) == D.Dy.of(k, I.Int.add(a, I.Int.neg(b))) : D.Dy}:
  Equal.trans(D.Dy, D.Dy.add(D.Dy.of(k, a), D.Dy.neg(D.Dy.of(k, b))), D.Dy.add(D.Dy.of(k, a), D.Dy.of(k, I.Int.neg(b))), D.Dy.of(k, I.Int.add(a, I.Int.neg(b))),
    Equal.cong(D.Dy, D.Dy, z => D.Dy.add(D.Dy.of(k, a), z), D.Dy.neg(D.Dy.of(k, b)), D.Dy.of(k, I.Int.neg(b)), Y.Of.neg(k, b)), Y.Add.of(k, a, I.Int.neg(b)))

def Dmul(+k1: Nat, +k2: Nat, +x: D.Dy, +a: I.Int, +y: D.Dy, +b: I.Int, +hx: {x == D.Dy.of(k1, a) : D.Dy}, +hy: {y == D.Dy.of(k2, b) : D.Dy}) -> {D.Dy.mul(x, y) == D.Dy.of(Nat.add(k1, k2), I.Int.mul(a, b)) : D.Dy}:
  Equal.trans(D.Dy, D.Dy.mul(x, y), D.Dy.mul(D.Dy.of(k1, a), D.Dy.of(k2, b)), D.Dy.of(Nat.add(k1, k2), I.Int.mul(a, b)),
    Equal.trans(D.Dy, D.Dy.mul(x, y), D.Dy.mul(D.Dy.of(k1, a), y), D.Dy.mul(D.Dy.of(k1, a), D.Dy.of(k2, b)), Equal.cong(D.Dy, D.Dy, z => D.Dy.mul(z, y), x, D.Dy.of(k1, a), hx), Equal.cong(D.Dy, D.Dy, z => D.Dy.mul(D.Dy.of(k1, a), z), y, D.Dy.of(k2, b), hy)),
    Mul.of(k1, a, k2, b))

def Dadd(+k: Nat, +x: D.Dy, +a: I.Int, +y: D.Dy, +b: I.Int, +hx: {x == D.Dy.of(k, a) : D.Dy}, +hy: {y == D.Dy.of(k, b) : D.Dy}) -> {D.Dy.add(x, y) == D.Dy.of(k, I.Int.add(a, b)) : D.Dy}:
  Equal.trans(D.Dy, D.Dy.add(x, y), D.Dy.add(D.Dy.of(k, a), D.Dy.of(k, b)), D.Dy.of(k, I.Int.add(a, b)), Y.Dy.cong2(x, D.Dy.of(k, a), y, D.Dy.of(k, b), hx, hy), Y.Add.of(k, a, b))

def Dsub2(+k: Nat, +x: D.Dy, +a: I.Int, +y: D.Dy, +b: I.Int, +hx: {x == D.Dy.of(k, a) : D.Dy}, +hy: {y == D.Dy.of(k, b) : D.Dy}) -> {D.Dy.add(x, D.Dy.neg(y)) == D.Dy.of(k, I.Int.add(a, I.Int.neg(b))) : D.Dy}:
  Equal.trans(D.Dy, D.Dy.add(x, D.Dy.neg(y)), D.Dy.add(D.Dy.of(k, a), D.Dy.neg(D.Dy.of(k, b))), D.Dy.of(k, I.Int.add(a, I.Int.neg(b))),
    Y.Dy.cong2(x, D.Dy.of(k, a), D.Dy.neg(y), D.Dy.neg(D.Dy.of(k, b)), hx, Equal.cong(D.Dy, D.Dy, z => D.Dy.neg(z), y, D.Dy.of(k, b), hy)), Dsub(k, a, b))

def Rr.e(+x: D.Dy, +y: D.Dy, +e: {x == y : D.Dy}, +p1: Nat) -> {RD.Dy.rne(1n+p1, x) == RD.Dy.rne(1n+p1, y) : D.Dy}:
  Equal.cong(D.Dy, D.Dy, z => RD.Dy.rne(1n+p1, z), x, y, e)

def Rr.add(+p1: Nat, +k: Nat, +x: D.Dy, +a: I.Int, +y: D.Dy, +b: I.Int, +hx: {x == D.Dy.of(k, a) : D.Dy}, +hy: {y == D.Dy.of(k, b) : D.Dy}) -> {RD.Dy.rne(1n+p1, D.Dy.add(x, y)) == D.Dy.of(k, E.RNi(1n+p1, I.Int.add(a, b))) : D.Dy}:
  Equal.trans(D.Dy, RD.Dy.rne(1n+p1, D.Dy.add(x, y)), RD.Dy.rne(1n+p1, D.Dy.of(k, I.Int.add(a, b))), D.Dy.of(k, E.RNi(1n+p1, I.Int.add(a, b))), Rr.e(D.Dy.add(x, y), D.Dy.of(k, I.Int.add(a, b)), Dadd(k, x, a, y, b, hx, hy), p1), Rne.of(p1, k, I.Int.add(a, b)))

def Rr.sub(+p1: Nat, +k: Nat, +x: D.Dy, +a: I.Int, +y: D.Dy, +b: I.Int, +hx: {x == D.Dy.of(k, a) : D.Dy}, +hy: {y == D.Dy.of(k, b) : D.Dy}) -> {RD.Dy.rne(1n+p1, D.Dy.add(x, D.Dy.neg(y))) == D.Dy.of(k, E.RNi(1n+p1, I.Int.add(a, I.Int.neg(b)))) : D.Dy}:
  Equal.trans(D.Dy, RD.Dy.rne(1n+p1, D.Dy.add(x, D.Dy.neg(y))), RD.Dy.rne(1n+p1, D.Dy.of(k, I.Int.add(a, I.Int.neg(b)))), D.Dy.of(k, E.RNi(1n+p1, I.Int.add(a, I.Int.neg(b)))), Rr.e(D.Dy.add(x, D.Dy.neg(y)), D.Dy.of(k, I.Int.add(a, I.Int.neg(b))), Dsub2(k, x, a, y, b, hx, hy), p1), Rne.of(p1, k, I.Int.add(a, I.Int.neg(b))))

# c x, c an integer
def Rr.mulc(+p1: Nat, +k: Nat, +c: I.Int, +x: D.Dy, +a: I.Int, +hx: {x == D.Dy.of(k, a) : D.Dy}) -> {RD.Dy.rne(1n+p1, D.Dy.mul(D.Dy.of(0n, c), x)) == D.Dy.of(k, E.RNi(1n+p1, I.Int.mul(c, a))) : D.Dy}:
  Equal.trans(D.Dy, RD.Dy.rne(1n+p1, D.Dy.mul(D.Dy.of(0n, c), x)), RD.Dy.rne(1n+p1, D.Dy.of(k, I.Int.mul(c, a))), D.Dy.of(k, E.RNi(1n+p1, I.Int.mul(c, a))), Rr.e(D.Dy.mul(D.Dy.of(0n, c), x), D.Dy.of(k, I.Int.mul(c, a)), Dmul(0n, k, D.Dy.of(0n, c), c, x, a, {==}, hx), p1), Rne.of(p1, k, I.Int.mul(c, a)))

def DRr.g(+p1: Nat, +s: Nat, +x: D.Dy) -> D.Dy:
  RD.Dy.rne(1n+p1, D.Dy.mul(D.Dy.of(0n, Sp.c(s)), x))

def DRr.d(+p1: Nat, +s: Nat, +x: D.Dy) -> D.Dy:
  RD.Dy.rne(1n+p1, D.Dy.add(x, D.Dy.neg(DRr.g(p1, s, x))))

def DRr.h(+p1: Nat, +s: Nat, +x: D.Dy) -> D.Dy:
  RD.Dy.rne(1n+p1, D.Dy.add(DRr.g(p1, s, x), DRr.d(p1, s, x)))

def DRr.l(+p1: Nat, +s: Nat, +x: D.Dy) -> D.Dy:
  RD.Dy.rne(1n+p1, D.Dy.add(x, D.Dy.neg(DRr.h(p1, s, x))))

def DRr.lg(+p1: Nat, +k: Nat, +s: Nat, +a: I.Int) -> {DRr.g(p1, s, D.Dy.of(k, a)) == D.Dy.of(k, Sp.g(1n+p1, s, a)) : D.Dy}:
  Rr.mulc(p1, k, Sp.c(s), D.Dy.of(k, a), a, {==})

def DRr.ld(+p1: Nat, +k: Nat, +s: Nat, +a: I.Int) -> {DRr.d(p1, s, D.Dy.of(k, a)) == D.Dy.of(k, Sp.d(1n+p1, s, a)) : D.Dy}:
  Rr.sub(p1, k, D.Dy.of(k, a), a, DRr.g(p1, s, D.Dy.of(k, a)), Sp.g(1n+p1, s, a), {==}, DRr.lg(p1, k, s, a))

def DRr.lh(+p1: Nat, +k: Nat, +s: Nat, +a: I.Int) -> {DRr.h(p1, s, D.Dy.of(k, a)) == D.Dy.of(k, Sp.h(1n+p1, s, a)) : D.Dy}:
  Rr.add(p1, k, DRr.g(p1, s, D.Dy.of(k, a)), Sp.g(1n+p1, s, a), DRr.d(p1, s, D.Dy.of(k, a)), Sp.d(1n+p1, s, a), DRr.lg(p1, k, s, a), DRr.ld(p1, k, s, a))

def DRr.ll(+p1: Nat, +k: Nat, +s: Nat, +a: I.Int) -> {DRr.l(p1, s, D.Dy.of(k, a)) == D.Dy.of(k, Sp.l(1n+p1, s, a)) : D.Dy}:
  Rr.sub(p1, k, D.Dy.of(k, a), a, DRr.h(p1, s, D.Dy.of(k, a)), Sp.h(1n+p1, s, a), {==}, DRr.lh(p1, k, s, a))

# Veltkamp's split is exact in this rounding: hi + lo = a
def DRr.split(+p1: Nat, +k: Nat, +s: Nat, +a: I.Int, +fa: {E.Rn(1n+p1, RD.Int.mag(a)) == RD.Int.mag(a) : Nat}) -> {D.Dy.add(DRr.h(p1, s, D.Dy.of(k, a)), DRr.l(p1, s, D.Dy.of(k, a))) == D.Dy.of(k, a) : D.Dy}:
  +h = Sp.h(1n+p1, s, a)
  Equal.trans(D.Dy, D.Dy.add(DRr.h(p1, s, D.Dy.of(k, a)), DRr.l(p1, s, D.Dy.of(k, a))), D.Dy.of(k, I.Int.add(h, Sp.l(1n+p1, s, a))), D.Dy.of(k, a),
    Dadd(k, DRr.h(p1, s, D.Dy.of(k, a)), h, DRr.l(p1, s, D.Dy.of(k, a)), Sp.l(1n+p1, s, a), DRr.lh(p1, k, s, a), DRr.ll(p1, k, s, a)),
    Y.Of.cong(k, k, I.Int.add(h, Sp.l(1n+p1, s, a)), a, {==},
      Equal.trans(I.Int, I.Int.add(h, Sp.l(1n+p1, s, a)), I.Int.add(h, I.Int.add(a, I.Int.neg(h))), a, Equal.cong(I.Int, I.Int, z => I.Int.add(h, z), Sp.l(1n+p1, s, a), I.Int.add(a, I.Int.neg(h)), Split(p1, s, a, fa)),
        BP.IntN([a, h], R.Ad(R.V(1n), R.Ad(R.V(0n), R.Ng(R.V(1n)))), R.V(0n), [], [], {==}, Unit{}))))

def Rf.e(+x: D.Dy, +y: D.Dy, +e: {x == y : D.Dy}, +p1: Nat, +emin: Nat) -> {E.Flg(p1, emin, x) == E.Flg(p1, emin, y) : D.Dy}:
  Equal.cong(D.Dy, D.Dy, z => E.Flg(p1, emin, z), x, y, e)

def Rf.add(+p1: Nat, +emin: Nat, +x: D.Dy, +a: I.Int, +y: D.Dy, +b: I.Int, +hx: {x == D.Dy.of(Nat.add(emin, p1), a) : D.Dy}, +hy: {y == D.Dy.of(Nat.add(emin, p1), b) : D.Dy}) -> {E.Flg(p1, emin, D.Dy.add(x, y)) == D.Dy.of(Nat.add(emin, p1), E.RNi(1n+p1, I.Int.add(a, b))) : D.Dy}:
  Equal.trans(D.Dy, E.Flg(p1, emin, D.Dy.add(x, y)), E.Flg(p1, emin, D.Dy.of(Nat.add(emin, p1), I.Int.add(a, b))), D.Dy.of(Nat.add(emin, p1), E.RNi(1n+p1, I.Int.add(a, b))), Rf.e(D.Dy.add(x, y), D.Dy.of(Nat.add(emin, p1), I.Int.add(a, b)), Dadd(Nat.add(emin, p1), x, a, y, b, hx, hy), p1, emin), E.FlL(p1, emin, I.Int.add(a, b)))

def Rf.sub(+p1: Nat, +emin: Nat, +x: D.Dy, +a: I.Int, +y: D.Dy, +b: I.Int, +hx: {x == D.Dy.of(Nat.add(emin, p1), a) : D.Dy}, +hy: {y == D.Dy.of(Nat.add(emin, p1), b) : D.Dy}) -> {E.Flg(p1, emin, D.Dy.add(x, D.Dy.neg(y))) == D.Dy.of(Nat.add(emin, p1), E.RNi(1n+p1, I.Int.add(a, I.Int.neg(b)))) : D.Dy}:
  Equal.trans(D.Dy, E.Flg(p1, emin, D.Dy.add(x, D.Dy.neg(y))), E.Flg(p1, emin, D.Dy.of(Nat.add(emin, p1), I.Int.add(a, I.Int.neg(b)))), D.Dy.of(Nat.add(emin, p1), E.RNi(1n+p1, I.Int.add(a, I.Int.neg(b)))), Rf.e(D.Dy.add(x, D.Dy.neg(y)), D.Dy.of(Nat.add(emin, p1), I.Int.add(a, I.Int.neg(b))), Dsub2(Nat.add(emin, p1), x, a, y, b, hx, hy), p1, emin), E.FlL(p1, emin, I.Int.add(a, I.Int.neg(b))))

# c x, c an integer
def Rf.mulc(+p1: Nat, +emin: Nat, +c: I.Int, +x: D.Dy, +a: I.Int, +hx: {x == D.Dy.of(Nat.add(emin, p1), a) : D.Dy}) -> {E.Flg(p1, emin, D.Dy.mul(D.Dy.of(0n, c), x)) == D.Dy.of(Nat.add(emin, p1), E.RNi(1n+p1, I.Int.mul(c, a))) : D.Dy}:
  Equal.trans(D.Dy, E.Flg(p1, emin, D.Dy.mul(D.Dy.of(0n, c), x)), E.Flg(p1, emin, D.Dy.of(Nat.add(emin, p1), I.Int.mul(c, a))), D.Dy.of(Nat.add(emin, p1), E.RNi(1n+p1, I.Int.mul(c, a))), Rf.e(D.Dy.mul(D.Dy.of(0n, c), x), D.Dy.of(Nat.add(emin, p1), I.Int.mul(c, a)), Dmul(0n, Nat.add(emin, p1), D.Dy.of(0n, c), c, x, a, {==}, hx), p1, emin), E.FlL(p1, emin, I.Int.mul(c, a)))

def DRf.g(+p1: Nat, +emin: Nat, +s: Nat, +x: D.Dy) -> D.Dy:
  E.Flg(p1, emin, D.Dy.mul(D.Dy.of(0n, Sp.c(s)), x))

def DRf.d(+p1: Nat, +emin: Nat, +s: Nat, +x: D.Dy) -> D.Dy:
  E.Flg(p1, emin, D.Dy.add(x, D.Dy.neg(DRf.g(p1, emin, s, x))))

def DRf.h(+p1: Nat, +emin: Nat, +s: Nat, +x: D.Dy) -> D.Dy:
  E.Flg(p1, emin, D.Dy.add(DRf.g(p1, emin, s, x), DRf.d(p1, emin, s, x)))

def DRf.l(+p1: Nat, +emin: Nat, +s: Nat, +x: D.Dy) -> D.Dy:
  E.Flg(p1, emin, D.Dy.add(x, D.Dy.neg(DRf.h(p1, emin, s, x))))

def DRf.lg(+p1: Nat, +emin: Nat, +s: Nat, +a: I.Int) -> {DRf.g(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a)) == D.Dy.of(Nat.add(emin, p1), Sp.g(1n+p1, s, a)) : D.Dy}:
  Rf.mulc(p1, emin, Sp.c(s), D.Dy.of(Nat.add(emin, p1), a), a, {==})

def DRf.ld(+p1: Nat, +emin: Nat, +s: Nat, +a: I.Int) -> {DRf.d(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a)) == D.Dy.of(Nat.add(emin, p1), Sp.d(1n+p1, s, a)) : D.Dy}:
  Rf.sub(p1, emin, D.Dy.of(Nat.add(emin, p1), a), a, DRf.g(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a)), Sp.g(1n+p1, s, a), {==}, DRf.lg(p1, emin, s, a))

def DRf.lh(+p1: Nat, +emin: Nat, +s: Nat, +a: I.Int) -> {DRf.h(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a)) == D.Dy.of(Nat.add(emin, p1), Sp.h(1n+p1, s, a)) : D.Dy}:
  Rf.add(p1, emin, DRf.g(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a)), Sp.g(1n+p1, s, a), DRf.d(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a)), Sp.d(1n+p1, s, a), DRf.lg(p1, emin, s, a), DRf.ld(p1, emin, s, a))

def DRf.ll(+p1: Nat, +emin: Nat, +s: Nat, +a: I.Int) -> {DRf.l(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a)) == D.Dy.of(Nat.add(emin, p1), Sp.l(1n+p1, s, a)) : D.Dy}:
  Rf.sub(p1, emin, D.Dy.of(Nat.add(emin, p1), a), a, DRf.h(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a)), Sp.h(1n+p1, s, a), {==}, DRf.lh(p1, emin, s, a))

# Veltkamp's split is exact in this rounding: hi + lo = a
def DRf.split(+p1: Nat, +emin: Nat, +s: Nat, +a: I.Int, +fa: {E.Rn(1n+p1, RD.Int.mag(a)) == RD.Int.mag(a) : Nat}) -> {D.Dy.add(DRf.h(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a)), DRf.l(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a))) == D.Dy.of(Nat.add(emin, p1), a) : D.Dy}:
  +h = Sp.h(1n+p1, s, a)
  Equal.trans(D.Dy, D.Dy.add(DRf.h(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a)), DRf.l(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a))), D.Dy.of(Nat.add(emin, p1), I.Int.add(h, Sp.l(1n+p1, s, a))), D.Dy.of(Nat.add(emin, p1), a),
    Dadd(Nat.add(emin, p1), DRf.h(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a)), h, DRf.l(p1, emin, s, D.Dy.of(Nat.add(emin, p1), a)), Sp.l(1n+p1, s, a), DRf.lh(p1, emin, s, a), DRf.ll(p1, emin, s, a)),
    Y.Of.cong(Nat.add(emin, p1), Nat.add(emin, p1), I.Int.add(h, Sp.l(1n+p1, s, a)), a, {==},
      Equal.trans(I.Int, I.Int.add(h, Sp.l(1n+p1, s, a)), I.Int.add(h, I.Int.add(a, I.Int.neg(h))), a, Equal.cong(I.Int, I.Int, z => I.Int.add(h, z), Sp.l(1n+p1, s, a), I.Int.add(a, I.Int.neg(h)), Split(p1, s, a, fa)),
        BP.IntN([a, h], R.Ad(R.V(1n), R.Ad(R.V(0n), R.Ng(R.V(1n)))), R.V(0n), [], [], {==}, Unit{}))))

# Dekker's product in binary rounding with no exponent bounds

def Rr.mul(+p1: Nat, +k1: Nat, +k2: Nat, +x: D.Dy, +a: I.Int, +y: D.Dy, +b: I.Int, +hx: {x == D.Dy.of(k1, a) : D.Dy}, +hy: {y == D.Dy.of(k2, b) : D.Dy})
  -> {RD.Dy.rne(1n+p1, D.Dy.mul(x, y)) == D.Dy.of(Nat.add(k1, k2), E.RNi(1n+p1, I.Int.mul(a, b))) : D.Dy}:
  Equal.trans(D.Dy, RD.Dy.rne(1n+p1, D.Dy.mul(x, y)), RD.Dy.rne(1n+p1, D.Dy.of(Nat.add(k1, k2), I.Int.mul(a, b))), D.Dy.of(Nat.add(k1, k2), E.RNi(1n+p1, I.Int.mul(a, b))),
    Rr.e(D.Dy.mul(x, y), D.Dy.of(Nat.add(k1, k2), I.Int.mul(a, b)), Dmul(k1, k2, x, a, y, b, hx, hy), p1), Rne.of(p1, Nat.add(k1, k2), I.Int.mul(a, b)))

def DDk.e1(+p1: Nat, +ah: D.Dy, +bh: D.Dy, +pi: D.Dy) -> D.Dy:
  RD.Dy.rne(1n+p1, D.Dy.add(RD.Dy.rne(1n+p1, D.Dy.mul(ah, bh)), D.Dy.neg(pi)))

def DDk.e2(+p1: Nat, +ah: D.Dy, +bh: D.Dy, +bl: D.Dy, +pi: D.Dy) -> D.Dy:
  RD.Dy.rne(1n+p1, D.Dy.add(DDk.e1(p1, ah, bh, pi), RD.Dy.rne(1n+p1, D.Dy.mul(ah, bl))))

def DDk.e3(+p1: Nat, +ah: D.Dy, +al: D.Dy, +bh: D.Dy, +bl: D.Dy, +pi: D.Dy) -> D.Dy:
  RD.Dy.rne(1n+p1, D.Dy.add(DDk.e2(p1, ah, bh, bl, pi), RD.Dy.rne(1n+p1, D.Dy.mul(al, bh))))

def DDk.e(+p1: Nat, +ah: D.Dy, +al: D.Dy, +bh: D.Dy, +bl: D.Dy, +pi: D.Dy) -> D.Dy:
  RD.Dy.rne(1n+p1, D.Dy.add(DDk.e3(p1, ah, al, bh, bl, pi), RD.Dy.rne(1n+p1, D.Dy.mul(al, bl))))

def DTP.p(+p1: Nat, +a: D.Dy, +b: D.Dy) -> D.Dy:
  RD.Dy.rne(1n+p1, D.Dy.mul(a, b))

def DTP.e(+p1: Nat, +s: Nat, +a: D.Dy, +b: D.Dy) -> D.Dy:
  DDk.e(p1, DRr.h(p1, s, a), DRr.l(p1, s, a), DRr.h(p1, s, b), DRr.l(p1, s, b), DTP.p(p1, a, b))

def DDk.l1(+p1: Nat, +k: Nat, +ah: D.Dy, +ah2: I.Int, +al: D.Dy, +al2: I.Int, +bh: D.Dy, +bh2: I.Int, +bl: D.Dy, +bl2: I.Int, +pi: D.Dy, +pi2: I.Int,
  +hah: {ah == D.Dy.of(k, ah2) : D.Dy}, +hal: {al == D.Dy.of(k, al2) : D.Dy}, +hbh: {bh == D.Dy.of(k, bh2) : D.Dy}, +hbl: {bl == D.Dy.of(k, bl2) : D.Dy}, +hpi: {pi == D.Dy.of(Nat.add(k, k), pi2) : D.Dy}) -> {DDk.e1(p1, ah, bh, pi) == D.Dy.of(Nat.add(k, k), Dk.e1(1n+p1, ah2, bh2, pi2)) : D.Dy}:
  Rr.sub(p1, Nat.add(k, k), RD.Dy.rne(1n+p1, D.Dy.mul(ah, bh)), E.RNi(1n+p1, I.Int.mul(ah2, bh2)), pi, pi2, Rr.mul(p1, k, k, ah, ah2, bh, bh2, hah, hbh), hpi)

def DDk.l2(+p1: Nat, +k: Nat, +ah: D.Dy, +ah2: I.Int, +al: D.Dy, +al2: I.Int, +bh: D.Dy, +bh2: I.Int, +bl: D.Dy, +bl2: I.Int, +pi: D.Dy, +pi2: I.Int,
  +hah: {ah == D.Dy.of(k, ah2) : D.Dy}, +hal: {al == D.Dy.of(k, al2) : D.Dy}, +hbh: {bh == D.Dy.of(k, bh2) : D.Dy}, +hbl: {bl == D.Dy.of(k, bl2) : D.Dy}, +hpi: {pi == D.Dy.of(Nat.add(k, k), pi2) : D.Dy}) -> {DDk.e2(p1, ah, bh, bl, pi) == D.Dy.of(Nat.add(k, k), Dk.e2(1n+p1, ah2, bh2, bl2, pi2)) : D.Dy}:
  Rr.add(p1, Nat.add(k, k), DDk.e1(p1, ah, bh, pi), Dk.e1(1n+p1, ah2, bh2, pi2), RD.Dy.rne(1n+p1, D.Dy.mul(ah, bl)), E.RNi(1n+p1, I.Int.mul(ah2, bl2)), DDk.l1(p1, k, ah, ah2, al, al2, bh, bh2, bl, bl2, pi, pi2, hah, hal, hbh, hbl, hpi), Rr.mul(p1, k, k, ah, ah2, bl, bl2, hah, hbl))

def DDk.l3(+p1: Nat, +k: Nat, +ah: D.Dy, +ah2: I.Int, +al: D.Dy, +al2: I.Int, +bh: D.Dy, +bh2: I.Int, +bl: D.Dy, +bl2: I.Int, +pi: D.Dy, +pi2: I.Int,
  +hah: {ah == D.Dy.of(k, ah2) : D.Dy}, +hal: {al == D.Dy.of(k, al2) : D.Dy}, +hbh: {bh == D.Dy.of(k, bh2) : D.Dy}, +hbl: {bl == D.Dy.of(k, bl2) : D.Dy}, +hpi: {pi == D.Dy.of(Nat.add(k, k), pi2) : D.Dy}) -> {DDk.e3(p1, ah, al, bh, bl, pi) == D.Dy.of(Nat.add(k, k), Dk.e3(1n+p1, ah2, al2, bh2, bl2, pi2)) : D.Dy}:
  Rr.add(p1, Nat.add(k, k), DDk.e2(p1, ah, bh, bl, pi), Dk.e2(1n+p1, ah2, bh2, bl2, pi2), RD.Dy.rne(1n+p1, D.Dy.mul(al, bh)), E.RNi(1n+p1, I.Int.mul(al2, bh2)), DDk.l2(p1, k, ah, ah2, al, al2, bh, bh2, bl, bl2, pi, pi2, hah, hal, hbh, hbl, hpi), Rr.mul(p1, k, k, al, al2, bh, bh2, hal, hbh))

def DDk.l(+p1: Nat, +k: Nat, +ah: D.Dy, +ah2: I.Int, +al: D.Dy, +al2: I.Int, +bh: D.Dy, +bh2: I.Int, +bl: D.Dy, +bl2: I.Int, +pi: D.Dy, +pi2: I.Int,
  +hah: {ah == D.Dy.of(k, ah2) : D.Dy}, +hal: {al == D.Dy.of(k, al2) : D.Dy}, +hbh: {bh == D.Dy.of(k, bh2) : D.Dy}, +hbl: {bl == D.Dy.of(k, bl2) : D.Dy}, +hpi: {pi == D.Dy.of(Nat.add(k, k), pi2) : D.Dy}) -> {DDk.e(p1, ah, al, bh, bl, pi) == D.Dy.of(Nat.add(k, k), Dk.e(1n+p1, ah2, al2, bh2, bl2, pi2)) : D.Dy}:
  Rr.add(p1, Nat.add(k, k), DDk.e3(p1, ah, al, bh, bl, pi), Dk.e3(1n+p1, ah2, al2, bh2, bl2, pi2), RD.Dy.rne(1n+p1, D.Dy.mul(al, bl)), E.RNi(1n+p1, I.Int.mul(al2, bl2)), DDk.l3(p1, k, ah, ah2, al, al2, bh, bh2, bl, bl2, pi, pi2, hah, hal, hbh, hbl, hpi), Rr.mul(p1, k, k, al, al2, bl, bl2, hal, hbl))

# Dekker's product is exact in binary rounding at p = 2s bits, s >= 2,
# with no exponent bounds (so, in a binary format, barring underflow and
# overflow): for a = A / 2^k and b = B / 2^k with A, B representable,
# pi = RN(a b) and e give pi + e = a b
def DTwoProd(+s2: Nat, +k: Nat, +aa: I.Int, +bb: I.Int, +fa: {E.Rn(1n+Nat.add(1n+1n+s2, 1n+s2), RD.Int.mag(aa)) == RD.Int.mag(aa) : Nat}, +fb: {E.Rn(1n+Nat.add(1n+1n+s2, 1n+s2), RD.Int.mag(bb)) == RD.Int.mag(bb) : Nat})
  -> {D.Dy.add(DTP.p(Nat.add(1n+1n+s2, 1n+s2), D.Dy.of(k, aa), D.Dy.of(k, bb)), DTP.e(Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Dy.of(k, aa), D.Dy.of(k, bb))) == D.Dy.mul(D.Dy.of(k, aa), D.Dy.of(k, bb)) : D.Dy}:
  +hp = Rr.mul(Nat.add(1n+1n+s2, 1n+s2), k, k, D.Dy.of(k, aa), aa, D.Dy.of(k, bb), bb, {==}, {==})
  +he = DDk.l(Nat.add(1n+1n+s2, 1n+s2), k, DRr.h(Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Dy.of(k, aa)), Sp.h(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, aa), DRr.l(Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Dy.of(k, aa)), Sp.l(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, aa), DRr.h(Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Dy.of(k, bb)), Sp.h(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, bb), DRr.l(Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Dy.of(k, bb)), Sp.l(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, bb), DTP.p(Nat.add(1n+1n+s2, 1n+s2), D.Dy.of(k, aa), D.Dy.of(k, bb)), TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), aa, bb),
    DRr.lh(Nat.add(1n+1n+s2, 1n+s2), k, 1n+1n+s2, aa), DRr.ll(Nat.add(1n+1n+s2, 1n+s2), k, 1n+1n+s2, aa), DRr.lh(Nat.add(1n+1n+s2, 1n+s2), k, 1n+1n+s2, bb), DRr.ll(Nat.add(1n+1n+s2, 1n+s2), k, 1n+1n+s2, bb), hp)
  Equal.trans(D.Dy, D.Dy.add(DTP.p(Nat.add(1n+1n+s2, 1n+s2), D.Dy.of(k, aa), D.Dy.of(k, bb)), DTP.e(Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Dy.of(k, aa), D.Dy.of(k, bb))), D.Dy.of(Nat.add(k, k), I.Int.add(TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), aa, bb), TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, aa, bb))), D.Dy.mul(D.Dy.of(k, aa), D.Dy.of(k, bb)),
    Dadd(Nat.add(k, k), DTP.p(Nat.add(1n+1n+s2, 1n+s2), D.Dy.of(k, aa), D.Dy.of(k, bb)), TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), aa, bb), DTP.e(Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, D.Dy.of(k, aa), D.Dy.of(k, bb)), TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, aa, bb), hp, he),
    Equal.trans(D.Dy, D.Dy.of(Nat.add(k, k), I.Int.add(TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), aa, bb), TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, aa, bb))), D.Dy.of(Nat.add(k, k), I.Int.mul(aa, bb)), D.Dy.mul(D.Dy.of(k, aa), D.Dy.of(k, bb)),
      Y.Of.cong(Nat.add(k, k), Nat.add(k, k), I.Int.add(TP.p(1n+Nat.add(1n+1n+s2, 1n+s2), aa, bb), TP.e(1n+Nat.add(1n+1n+s2, 1n+s2), 1n+1n+s2, aa, bb)), I.Int.mul(aa, bb), {==}, TwoProd(s2, aa, bb, fa, fb)),
      Equal.sym(D.Dy, D.Dy.mul(D.Dy.of(k, aa), D.Dy.of(k, bb)), D.Dy.of(Nat.add(k, k), I.Int.mul(aa, bb)), Mul.of(k, aa, k, bb))))
