# AccurateDWPlusDW (Joldes, Muller and Popescu, TOMS 2017, Algorithm 6 and
# Theorem 3.1), the double-word sum num/df32.bend runs:
# |zh + zl - (x + y)| (1 - 4u) <= 3u² |x + y| for p >= 6, any signs and
# exponents, in binary rounding with no exponent bounds (AccDW.gen), and
# so below 3u² + 13u³ (AccDW.simp). The proof follows the paper's cases on
# integers, at a scale where u² is an integer (ADR-012). Its one Fast2Sum
# that is not ordered by magnitude (line 4 when xh + yh cancels) is exact
# because b's binade is at most a's (F2.bin).

import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/round.bend as RD
import ../src/norm.bend as N
import ./nat.bend as NL
import ./int.bend as Z
import ./base.bend as B
import ./norm.bend as NP
import ./dyadic.bend as Y
import ./round.bend as R
import ./big.bend as BP
import ./eft.bend as E
import ./eft2.bend as E2
import ./posit3.bend as P3
import ./dw.bend as W

# Rounding facts
# --------------

# the relative error is at most u: |Rn m - m| 2^p <= m
def RelE.go(+p1: Nat, +m: Nat, u: Bool, rv: R.RV(u, m, E.Rn(1n+p1, m), R.Tr.err(RD.Tr.of(1n+p1, m))))
  -> {E.Dist(E.Rn(1n+p1, m), m) == R.Tr.err(RD.Tr.of(1n+p1, m)) : Nat}:
  match u:
    case True{}:
      Equal.trans(Nat, E.Dist(E.Rn(1n+p1, m), m), E.Dist(Nat.add(m, R.Tr.err(RD.Tr.of(1n+p1, m))), m), R.Tr.err(RD.Tr.of(1n+p1, m)),
        Equal.cong(Nat, Nat, v => E.Dist(v, m), E.Rn(1n+p1, m), Nat.add(m, R.Tr.err(RD.Tr.of(1n+p1, m))), rv), E.Dist.dn(m, R.Tr.err(RD.Tr.of(1n+p1, m))))
    case False{}:
      Equal.trans(Nat, E.Dist(E.Rn(1n+p1, m), m), E.Dist(E.Rn(1n+p1, m), Nat.add(E.Rn(1n+p1, m), R.Tr.err(RD.Tr.of(1n+p1, m)))), R.Tr.err(RD.Tr.of(1n+p1, m)),
        Equal.cong(Nat, Nat, v => E.Dist(E.Rn(1n+p1, m), v), m, Nat.add(E.Rn(1n+p1, m), R.Tr.err(RD.Tr.of(1n+p1, m))), rv), E.Dist.up(E.Rn(1n+p1, m), R.Tr.err(RD.Tr.of(1n+p1, m))))

def RelE.f(+p1: Nat, +m: Nat,
  facts: R.RV(RD.Tr.rup(RD.Tr.of(1n+p1, m)), m, RD.Tr.near(RD.Tr.of(1n+p1, m)), R.Tr.err(RD.Tr.of(1n+p1, m)))
    & {m == Nat.add(Nat.mul(R.Tr.err(RD.Tr.of(1n+p1, m)), Nat.double(RD.Nat.pow2(p1))), RD.Nat.monus(m, Nat.mul(R.Tr.err(RD.Tr.of(1n+p1, m)), Nat.double(RD.Nat.pow2(p1))))) : Nat})
  -> {RD.Nat.lt(m, Nat.mul(E.Dist(E.Rn(1n+p1, m), m), RD.Nat.pow2(1n+p1))) == False{} : Bool}:
  (rv, me) = facts
  +P = RD.Nat.pow2(1n+p1)
  +e = R.Tr.err(RD.Tr.of(1n+p1, m))
  +ed : {E.Dist(E.Rn(1n+p1, m), m) == e : Nat} = RelE.go(p1, m, RD.Tr.rup(RD.Tr.of(1n+p1, m)), rv)
  +rest = RD.Nat.monus(m, Nat.mul(e, P))
  E.Le.trans(Nat.mul(E.Dist(E.Rn(1n+p1, m), m), P), Nat.mul(e, P), m, E.Le.eq(Nat.mul(E.Dist(E.Rn(1n+p1, m), m), P), Nat.mul(e, P), Equal.cong(Nat, Nat, v => Nat.mul(v, P), E.Dist(E.Rn(1n+p1, m), m), e, ed)),
    E.Le.trans(Nat.mul(e, P), Nat.add(Nat.mul(e, P), rest), m, E.Le.add(Nat.mul(e, P), rest), E.Le.eq(Nat.add(Nat.mul(e, P), rest), m, Equal.sym(Nat, m, Nat.add(Nat.mul(e, P), rest), me))))

def RelE(+p1: Nat, +m: Nat) -> {RD.Nat.lt(m, Nat.mul(E.Dist(E.Rn(1n+p1, m), m), RD.Nat.pow2(1n+p1))) == False{} : Bool}:
  RelE.f(p1, m, R.Rne.nat(RD.Nat.pow2(p1), m, RD.Tr.of(1n+p1, m), RD.Tr.rup(RD.Tr.of(1n+p1, m)), {==}, R.Inv.of(p1, m)))

# on integers: |RN z - z| 2^p <= |z|
def RelI(+p1: Nat, +z: I.Int) -> {RD.Nat.lt(RD.Int.mag(z), Nat.mul(RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))), RD.Nat.pow2(1n+p1))) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(RD.Int.mag(z), Nat.mul(RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))), RD.Nat.pow2(1n+p1))), RD.Nat.lt(RD.Int.mag(z), Nat.mul(E.Dist(E.Rn(1n+p1, RD.Int.mag(z)), RD.Int.mag(z)), RD.Nat.pow2(1n+p1))), False{},
    Equal.cong(Nat, Bool, v => RD.Nat.lt(RD.Int.mag(z), Nat.mul(v, RD.Nat.pow2(1n+p1))), RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))), E.Dist(E.Rn(1n+p1, RD.Int.mag(z)), RD.Int.mag(z)), W.Err.i(1n+p1, z)),
    RelE(p1, RD.Int.mag(z)))

# the error is at most the rounded value
def ErrRn(+p1: Nat, +m: Nat) -> {RD.Nat.lt(E.Rn(1n+p1, m), E.Dist(E.Rn(1n+p1, m), m)) == False{} : Bool}:
  +r = E.Rn(1n+p1, m)
  +d = E.Dist(r, m)
  +P = RD.Nat.pow2(1n+p1)
  +h2 : {RD.Nat.lt(m, Nat.double(d)) == False{} : Bool} = E.Le.trans(Nat.double(d), Nat.mul(d, P), m,
    E.Le.trans(Nat.double(d), Nat.mul(d, RD.Nat.pow2(1n)), Nat.mul(d, P), E.Le.eq(Nat.double(d), Nat.mul(d, RD.Nat.pow2(1n)), Equal.sym(Nat, Nat.mul(d, RD.Nat.pow2(1n)), Nat.double(d), W.M2(d))),
      E2.Le.mull(d, RD.Nat.pow2(1n), P, E2.Pow2.mono(1n, 1n+p1, BP.Lt.z(p1)))),
    RelE(p1, m))
  +h3 : {RD.Nat.lt(Nat.add(r, d), m) == False{} : Bool} = E2.Dist.ge(r, m)
  E2.Le.canl(d, d, r, E.Le.trans(Nat.add(d, d), Nat.double(d), Nat.add(d, r), E.Le.eq(Nat.add(d, d), Nat.double(d), Equal.sym(Nat, Nat.double(d), Nat.add(d, d), Y.Nat.double_add(d))),
    E.Le.trans(Nat.double(d), m, Nat.add(d, r), h2, E.Le.trans(m, Nat.add(r, d), Nat.add(d, r), h3, E.Le.eq(Nat.add(r, d), Nat.add(d, r), NL.Nat.add_comm(r, d))))))

# Fast2Sum with b no larger in binade than a: for |a| >= 2^(p-1) 2^k and
# |b| < 2^p 2^k, s + t = a + b. When |b| > |a| both are multiples of 2^k
# below 2^p 2^k, so s - a is a multiple of 2^k of at most p bits.
def Sgn.sh(+p1: Nat, +a: I.Int, +k: Nat, +fa: {E.Rn(1n+p1, RD.Int.mag(a)) == RD.Int.mag(a) : Nat}, +ha: {RD.Nat.lt(RD.Int.mag(a), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(k))) == False{} : Bool})
  -> {a == D.Int.sh(k, RD.Int.signed(a, W.Mq(p1, RD.Int.mag(a), k))) : I.Int}:
  +m = W.Mq(p1, RD.Int.mag(a), k)
  Equal.trans(I.Int, a, RD.Int.signed(a, RD.Int.mag(a)), D.Int.sh(k, RD.Int.signed(a, m)), Equal.sym(I.Int, RD.Int.signed(a, RD.Int.mag(a)), a, E.Sgn.self(a)),
    Equal.trans(I.Int, RD.Int.signed(a, RD.Int.mag(a)), RD.Int.signed(a, Nat.mul(m, RD.Nat.pow2(k))), D.Int.sh(k, RD.Int.signed(a, m)),
      Equal.cong(Nat, I.Int, v => RD.Int.signed(a, v), RD.Int.mag(a), Nat.mul(m, RD.Nat.pow2(k)), W.Rep.mult(p1, RD.Int.mag(a), k, fa, ha)),
      Equal.sym(I.Int, D.Int.sh(k, RD.Int.signed(a, m)), RD.Int.signed(a, Nat.mul(m, RD.Nat.pow2(k))), E.Sh.signed(k, a, m))))

def F2.bin.lt(+p1: Nat, +a: I.Int, +b: I.Int, +k: Nat,
  +fa: {E.Rn(1n+p1, RD.Int.mag(a)) == RD.Int.mag(a) : Nat}, +fb: {E.Rn(1n+p1, RD.Int.mag(b)) == RD.Int.mag(b) : Nat},
  +ha: {RD.Nat.lt(RD.Int.mag(a), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(k))) == False{} : Bool}, +hb: {RD.Nat.lt(RD.Int.mag(b), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k))) == True{} : Bool},
  +hab: {RD.Nat.lt(RD.Int.mag(a), RD.Int.mag(b)) == True{} : Bool})
  -> {I.Int.add(E.F2.s(1n+p1, a, b), E.F2.t(1n+p1, a, b)) == I.Int.add(a, b) : I.Int}:
  +p : Nat = 1n+p1
  +P = RD.Nat.pow2(1n+p1)
  +K = RD.Nat.pow2(k)
  +ma = W.Mq(p1, RD.Int.mag(a), k)
  +mb = W.Mq(p1, RD.Int.mag(b), k)
  +hb1 : {RD.Nat.lt(RD.Int.mag(b), Nat.mul(RD.Nat.pow2(p1), K)) == False{} : Bool} = E.Le.trans(Nat.mul(RD.Nat.pow2(p1), K), RD.Int.mag(a), RD.Int.mag(b), ha, E2.Lt.to_le(RD.Int.mag(a), RD.Int.mag(b), hab))
  +wa = RD.Int.signed(a, ma)
  +wb = RD.Int.signed(b, mb)
  +ea : {a == D.Int.sh(k, wa) : I.Int} = Sgn.sh(p1, a, k, fa, ha)
  +eb : {b == D.Int.sh(k, wb) : I.Int} = Sgn.sh(p1, b, k, fb, hb1)
  +w = I.Int.add(wa, wb)
  # |wa|, |wb| < 2^p
  +emb : {RD.Int.mag(wb) == mb : Nat} = W.Mag.sg(b, mb)
  +ema : {RD.Int.mag(wa) == ma : Nat} = W.Mag.sg(a, ma)
  +eKb : {RD.Int.mag(b) == Nat.mul(mb, K) : Nat} = W.Rep.mult(p1, RD.Int.mag(b), k, fb, hb1)
  +eKa : {RD.Int.mag(a) == Nat.mul(ma, K) : Nat} = W.Rep.mult(p1, RD.Int.mag(a), k, fa, ha)
  +lb : {RD.Nat.lt(mb, P) == True{} : Bool} = E.Lt.cancel(mb, P, K, Equal.trans(Bool, RD.Nat.lt(Nat.mul(mb, K), Nat.mul(P, K)), RD.Nat.lt(RD.Int.mag(b), Nat.mul(P, K)), True{},
    Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.mul(P, K)), Nat.mul(mb, K), RD.Int.mag(b), Equal.sym(Nat, RD.Int.mag(b), Nat.mul(mb, K), eKb)), hb))
  +la : {RD.Nat.lt(ma, P) == True{} : Bool} = E.Lt.cancel(ma, P, K, Equal.trans(Bool, RD.Nat.lt(Nat.mul(ma, K), Nat.mul(P, K)), RD.Nat.lt(RD.Int.mag(a), Nat.mul(P, K)), True{},
    Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.mul(P, K)), Nat.mul(ma, K), RD.Int.mag(a), Equal.sym(Nat, RD.Int.mag(a), Nat.mul(ma, K), eKa)),
    E2.Lt.le_trans(RD.Int.mag(a), RD.Int.mag(b), Nat.mul(P, K), hab, E2.Lt.to_le(RD.Int.mag(b), Nat.mul(P, K), hb))))
  # |RN w - w| <= 1, since |w| < 2^p 2
  +lw : {RD.Nat.lt(Nat.mul(P, RD.Nat.pow2(1n)), RD.Int.mag(w)) == False{} : Bool} = E.Le.trans(RD.Int.mag(w), Nat.add(ma, mb), Nat.mul(P, RD.Nat.pow2(1n)),
    E.Le.trans(RD.Int.mag(w), Nat.add(RD.Int.mag(wa), RD.Int.mag(wb)), Nat.add(ma, mb), E2.Mag.tri(wa, wb),
      E.Le.eq(Nat.add(RD.Int.mag(wa), RD.Int.mag(wb)), Nat.add(ma, mb), Equal.trans(Nat, Nat.add(RD.Int.mag(wa), RD.Int.mag(wb)), Nat.add(ma, RD.Int.mag(wb)), Nat.add(ma, mb),
        Equal.cong(Nat, Nat, v => Nat.add(v, RD.Int.mag(wb)), RD.Int.mag(wa), ma, ema), Equal.cong(Nat, Nat, v => Nat.add(ma, v), RD.Int.mag(wb), mb, emb)))),
    E.Le.trans(Nat.add(ma, mb), Nat.add(P, P), Nat.mul(P, RD.Nat.pow2(1n)), E2.Le.add2(ma, P, mb, P, E2.Lt.to_le(ma, P, la), E2.Lt.to_le(mb, P, lb)),
      E.Le.eq(Nat.add(P, P), Nat.mul(P, RD.Nat.pow2(1n)), Equal.trans(Nat, Nat.add(P, P), Nat.double(P), Nat.mul(P, RD.Nat.pow2(1n)), Equal.sym(Nat, Nat.double(P), Nat.add(P, P), Y.Nat.double_add(P)), Equal.sym(Nat, Nat.mul(P, RD.Nat.pow2(1n)), Nat.double(P), W.M2(P))))))
  +ew = I.Int.add(E.RNi(p, w), I.Int.neg(w))
  +lew : {RD.Nat.lt(1n, RD.Int.mag(ew)) == False{} : Bool} = W.Le.halve(RD.Int.mag(ew), 1n, W.EB(p1, w, 1n, lw))
  # s - a = 2^k (RN w - wa), and |RN w - wa| <= |RN w - w| + |wb| <= 2^p
  +d = I.Int.add(E.RNi(p, w), I.Int.neg(wa))
  +envd : List<&2, I.Int> = [E.RNi(p, w), wa, wb]
  +ed : {d == I.Int.add(ew, wb) : I.Int} = BP.IntN(envd, R.Ad(R.V(0n), R.Ng(R.V(1n))), R.Ad(R.Ad(R.V(0n), R.Ng(R.Ad(R.V(1n), R.V(2n)))), R.V(2n)), [], [], {==}, Unit{})
  +ld : {RD.Nat.lt(P, RD.Int.mag(d)) == False{} : Bool} = E.Le.trans(RD.Int.mag(d), Nat.add(RD.Int.mag(ew), RD.Int.mag(wb)), P,
    E.Le.trans(RD.Int.mag(d), RD.Int.mag(I.Int.add(ew, wb)), Nat.add(RD.Int.mag(ew), RD.Int.mag(wb)), E.Le.eq(RD.Int.mag(d), RD.Int.mag(I.Int.add(ew, wb)), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), d, I.Int.add(ew, wb), ed)), E2.Mag.tri(ew, wb)),
    E.Le.trans(Nat.add(RD.Int.mag(ew), RD.Int.mag(wb)), Nat.add(1n, mb), P, E2.Le.add2(RD.Int.mag(ew), 1n, RD.Int.mag(wb), mb, lew, E.Le.eq(RD.Int.mag(wb), mb, emb)), E2.Le.succ(mb, P, lb)))
  +s = E.F2.s(p, a, b)
  +es : {s == D.Int.sh(k, E.RNi(p, w)) : I.Int} = Equal.trans(I.Int, s, E.RNi(p, I.Int.add(D.Int.sh(k, wa), D.Int.sh(k, wb))), D.Int.sh(k, E.RNi(p, w)),
    Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(a, b), I.Int.add(D.Int.sh(k, wa), D.Int.sh(k, wb)), Y.Int.cong2(a, D.Int.sh(k, wa), b, D.Int.sh(k, wb), ea, eb)),
    E2.RNi.shadd(p, k, wa, wb))
  +esa : {I.Int.add(s, I.Int.neg(a)) == D.Int.sh(k, d) : I.Int} = Equal.trans(I.Int, I.Int.add(s, I.Int.neg(a)), I.Int.add(D.Int.sh(k, E.RNi(p, w)), I.Int.neg(D.Int.sh(k, wa))), D.Int.sh(k, d),
    Y.Int.cong2(s, D.Int.sh(k, E.RNi(p, w)), I.Int.neg(a), I.Int.neg(D.Int.sh(k, wa)), es, Equal.cong(I.Int, I.Int, v => I.Int.neg(v), a, D.Int.sh(k, wa), ea)),
    E2.Sh.diff(k, E.RNi(p, w), wa))
  +emd : {RD.Int.mag(I.Int.add(s, I.Int.neg(a))) == Nat.mul(RD.Int.mag(d), K) : Nat} = Equal.trans(Nat, RD.Int.mag(I.Int.add(s, I.Int.neg(a))), RD.Int.mag(D.Int.sh(k, d)), Nat.mul(RD.Int.mag(d), K),
    Equal.cong(I.Int, Nat, v => RD.Int.mag(v), I.Int.add(s, I.Int.neg(a)), D.Int.sh(k, d), esa), E.Sh.mag(k, d))
  +fe : {E.Rn(p, RD.Int.mag(I.Int.add(s, I.Int.neg(a)))) == RD.Int.mag(I.Int.add(s, I.Int.neg(a))) : Nat} = W.Rn.fix(p1, RD.Int.mag(I.Int.add(s, I.Int.neg(a))), RD.Int.mag(d), k, emd, ld)
  # the sum's error is Fast2Sum(b, a)'s t, a rounded value
  +hba = E.Fast2Sum(p1, b, a, fb, fa, E2.Lt.to_le(RD.Int.mag(a), RD.Int.mag(b), hab))
  +t2 = E.F2.t(p, b, a)
  +x = I.Int.add(a, b)
  +er = I.Int.add(E.RNi(p, x), I.Int.neg(x))
  +es2 : {E.F2.s(p, b, a) == E.RNi(p, x) : I.Int} = Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(b, a), x, Z.Int.add_comm(b, a))
  +envt : List<&2, I.Int> = [E.F2.s(p, b, a), t2, a, b]
  +et : {t2 == I.Int.neg(er) : I.Int} = Equal.trans(I.Int, t2, I.Int.add(I.Int.add(b, a), I.Int.neg(E.F2.s(p, b, a))), I.Int.neg(er),
    Equal.trans(I.Int, t2, I.Int.add(I.Int.add(E.F2.s(p, b, a), t2), I.Int.neg(E.F2.s(p, b, a))), I.Int.add(I.Int.add(b, a), I.Int.neg(E.F2.s(p, b, a))),
      BP.IntN(envt, R.V(1n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(0n))), [], [], {==}, Unit{}),
      Equal.cong(I.Int, I.Int, v => I.Int.add(v, I.Int.neg(E.F2.s(p, b, a))), I.Int.add(E.F2.s(p, b, a), t2), I.Int.add(b, a), hba)),
    Equal.trans(I.Int, I.Int.add(I.Int.add(b, a), I.Int.neg(E.F2.s(p, b, a))), I.Int.add(I.Int.add(b, a), I.Int.neg(E.RNi(p, x))), I.Int.neg(er),
      Equal.cong(I.Int, I.Int, v => I.Int.add(I.Int.add(b, a), I.Int.neg(v)), E.F2.s(p, b, a), E.RNi(p, x), es2),
      BP.IntN([a, b, E.RNi(p, x)], R.Ad(R.Ad(R.V(1n), R.V(0n)), R.Ng(R.V(2n))), R.Ng(R.Ad(R.V(2n), R.Ng(R.Ad(R.V(0n), R.V(1n))))), [], [], {==}, Unit{})))
  +emr : {E.Dist(E.Rn(p, RD.Int.mag(x)), RD.Int.mag(x)) == RD.Int.mag(t2) : Nat} = Equal.trans(Nat, E.Dist(E.Rn(p, RD.Int.mag(x)), RD.Int.mag(x)), RD.Int.mag(er), RD.Int.mag(t2),
    Equal.sym(Nat, RD.Int.mag(er), E.Dist(E.Rn(p, RD.Int.mag(x)), RD.Int.mag(x)), W.Err.i(p, x)),
    Equal.trans(Nat, RD.Int.mag(er), RD.Int.mag(I.Int.neg(er)), RD.Int.mag(t2), Equal.sym(Nat, RD.Int.mag(I.Int.neg(er)), RD.Int.mag(er), E.Mag.neg(er)),
      Equal.cong(I.Int, Nat, v => RD.Int.mag(v), I.Int.neg(er), t2, Equal.sym(I.Int, t2, I.Int.neg(er), et))))
  +fr : {E.Rn(p, E.Dist(E.Rn(p, RD.Int.mag(x)), RD.Int.mag(x))) == E.Dist(E.Rn(p, RD.Int.mag(x)), RD.Int.mag(x)) : Nat} =
    E.Fn.eq(p, E.Dist(E.Rn(p, RD.Int.mag(x)), RD.Int.mag(x)), RD.Int.mag(t2), emr, W.Rf.i(p1, I.Int.add(a, I.Int.neg(E.F2.z(p, b, a)))))
  E.F2.fin(p, a, b, fe, fr)

def F2.bin.go(+p1: Nat, +a: I.Int, +b: I.Int, +k: Nat,
  +fa: {E.Rn(1n+p1, RD.Int.mag(a)) == RD.Int.mag(a) : Nat}, +fb: {E.Rn(1n+p1, RD.Int.mag(b)) == RD.Int.mag(b) : Nat},
  +ha: {RD.Nat.lt(RD.Int.mag(a), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(k))) == False{} : Bool}, +hb: {RD.Nat.lt(RD.Int.mag(b), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k))) == True{} : Bool},
  l: Bool, +el: {RD.Nat.lt(RD.Int.mag(a), RD.Int.mag(b)) == l : Bool})
  -> {I.Int.add(E.F2.s(1n+p1, a, b), E.F2.t(1n+p1, a, b)) == I.Int.add(a, b) : I.Int}:
  match l:
    case False{}:
      E.Fast2Sum(p1, a, b, fa, fb, el)
    case True{}:
      F2.bin.lt(p1, a, b, k, fa, fb, ha, hb, el)

def F2.bin(+p1: Nat, +a: I.Int, +b: I.Int, +k: Nat,
  +fa: {E.Rn(1n+p1, RD.Int.mag(a)) == RD.Int.mag(a) : Nat}, +fb: {E.Rn(1n+p1, RD.Int.mag(b)) == RD.Int.mag(b) : Nat},
  +ha: {RD.Nat.lt(RD.Int.mag(a), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(k))) == False{} : Bool}, +hb: {RD.Nat.lt(RD.Int.mag(b), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k))) == True{} : Bool})
  -> {I.Int.add(E.F2.s(1n+p1, a, b), E.F2.t(1n+p1, a, b)) == I.Int.add(a, b) : I.Int}:
  F2.bin.go(p1, a, b, k, fa, fb, ha, hb, RD.Nat.lt(RD.Int.mag(a), RD.Int.mag(b)), {==})

# Fast2Sum(0, b) for b representable
def F2.zero(+p1: Nat, +b: I.Int, +fb: {E.Rn(1n+p1, RD.Int.mag(b)) == RD.Int.mag(b) : Nat})
  -> {I.Int.add(E.F2.s(1n+p1, I.IPos{0n}, b), E.F2.t(1n+p1, I.IPos{0n}, b)) == I.Int.add(I.IPos{0n}, b) : I.Int}:
  +p : Nat = 1n+p1
  +z0 : I.Int = I.IPos{0n}
  +env : List<&2, I.Int> = [b]
  +e0 : {I.Int.add(z0, b) == b : I.Int} = BP.IntN(env, R.Ad(N.TZero{}, R.V(0n)), R.V(0n), [], [], {==}, Unit{})
  +es : {E.F2.s(p, z0, b) == b : I.Int} = Equal.trans(I.Int, E.RNi(p, I.Int.add(z0, b)), E.RNi(p, b), b, Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(z0, b), b, e0), E.RNi.exact(p, b, fb))
  +env2 : List<&2, I.Int> = [b]
  +esa : {I.Int.add(E.F2.s(p, z0, b), I.Int.neg(z0)) == b : I.Int} = Equal.trans(I.Int, I.Int.add(E.F2.s(p, z0, b), I.Int.neg(z0)), I.Int.add(b, I.Int.neg(z0)), b,
    Equal.cong(I.Int, I.Int, v => I.Int.add(v, I.Int.neg(z0)), E.F2.s(p, z0, b), b, es), BP.IntN(env2, R.Ad(R.V(0n), R.Ng(N.TZero{})), R.V(0n), [], [], {==}, Unit{}))
  +fe : {E.Rn(p, RD.Int.mag(I.Int.add(E.F2.s(p, z0, b), I.Int.neg(z0)))) == RD.Int.mag(I.Int.add(E.F2.s(p, z0, b), I.Int.neg(z0))) : Nat} =
    E.Fn.eq(p, RD.Int.mag(I.Int.add(E.F2.s(p, z0, b), I.Int.neg(z0))), RD.Int.mag(b), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), I.Int.add(E.F2.s(p, z0, b), I.Int.neg(z0)), b, esa), fb)
  +mb = RD.Int.mag(I.Int.add(z0, b))
  +ed : {E.Dist(E.Rn(p, mb), mb) == 0n : Nat} = Equal.trans(Nat, E.Dist(E.Rn(p, mb), mb), E.Dist(E.Rn(p, RD.Int.mag(b)), RD.Int.mag(b)), 0n,
    Equal.cong(Nat, Nat, v => E.Dist(E.Rn(p, v), v), mb, RD.Int.mag(b), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), I.Int.add(z0, b), b, e0)),
    Equal.trans(Nat, E.Dist(E.Rn(p, RD.Int.mag(b)), RD.Int.mag(b)), E.Dist(RD.Int.mag(b), RD.Int.mag(b)), 0n, Equal.cong(Nat, Nat, v => E.Dist(v, RD.Int.mag(b)), E.Rn(p, RD.Int.mag(b)), RD.Int.mag(b), fb), W.Dist.self(RD.Int.mag(b))))
  +fr : {E.Rn(p, E.Dist(E.Rn(p, mb), mb)) == E.Dist(E.Rn(p, mb), mb) : Nat} = E.Fn.eq(p, E.Dist(E.Rn(p, mb), mb), 0n, ed, E2.Rn.z(p1))
  E.F2.fin(p, z0, b, fe, fr)

# The algorithm on integers
# -------------------------
# (sh, sl) = TwoSum(xh, yh), (th, tl) = TwoSum(xl, yl) (exact, proofs/eft.bend),
# c = RN(sl + th), (vh, vl) = Fast2Sum(sh, c), w = RN(tl + vl),
# (zh, zl) = Fast2Sum(vh, w), as num/df32.bend computes it.

def A.sh(+p: Nat, +xh: I.Int, +yh: I.Int) -> I.Int:
  E.RNi(p, I.Int.add(xh, yh))

def A.sl(+p: Nat, +xh: I.Int, +yh: I.Int) -> I.Int:
  I.Int.add(I.Int.add(xh, yh), I.Int.neg(A.sh(p, xh, yh)))

def A.th(+p: Nat, +xl: I.Int, +yl: I.Int) -> I.Int:
  E.RNi(p, I.Int.add(xl, yl))

def A.tl(+p: Nat, +xl: I.Int, +yl: I.Int) -> I.Int:
  I.Int.add(I.Int.add(xl, yl), I.Int.neg(A.th(p, xl, yl)))

def A.c(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  E.RNi(p, I.Int.add(A.sl(p, xh, yh), A.th(p, xl, yl)))

def A.vh(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  E.F2.s(p, A.sh(p, xh, yh), A.c(p, xh, xl, yh, yl))

def A.vl(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  E.F2.t(p, A.sh(p, xh, yh), A.c(p, xh, xl, yh, yl))

def A.w(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  E.RNi(p, I.Int.add(A.tl(p, xl, yl), A.vl(p, xh, xl, yh, yl)))

def A.z(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  I.Int.add(E.F2.s(p, A.vh(p, xh, xl, yh, yl), A.w(p, xh, xl, yh, yl)), E.F2.t(p, A.vh(p, xh, xl, yh, yl), A.w(p, xh, xl, yh, yl)))

def A.eta(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  I.Int.add(A.z(p, xh, xl, yh, yl), I.Int.neg(I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl))))

# the two rounding errors that are not error-free
def A.e1(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  I.Int.add(A.c(p, xh, xl, yh, yl), I.Int.neg(I.Int.add(A.sl(p, xh, yh), A.th(p, xl, yl))))

def A.e2(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  I.Int.add(A.w(p, xh, xl, yh, yl), I.Int.neg(I.Int.add(A.tl(p, xl, yl), A.vl(p, xh, xl, yh, yl))))

# both Fast2Sums exact: eta = e1 + e2
def A.split(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int,
  +h4: {I.Int.add(A.vh(p, xh, xl, yh, yl), A.vl(p, xh, xl, yh, yl)) == I.Int.add(A.sh(p, xh, yh), A.c(p, xh, xl, yh, yl)) : I.Int},
  +h6: {A.z(p, xh, xl, yh, yl) == I.Int.add(A.vh(p, xh, xl, yh, yl), A.w(p, xh, xl, yh, yl)) : I.Int})
  -> {A.eta(p, xh, xl, yh, yl) == I.Int.add(A.e1(p, xh, xl, yh, yl), A.e2(p, xh, xl, yh, yl)) : I.Int}:
  +sh = A.sh(p, xh, yh)
  +th = A.th(p, xl, yl)
  +c = A.c(p, xh, xl, yh, yl)
  +vh = A.vh(p, xh, xl, yh, yl)
  +vl = A.vl(p, xh, xl, yh, yl)
  +w = A.w(p, xh, xl, yh, yl)
  +X = I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl))
  +env : List<&2, I.Int> = [xh, xl, yh, yl, sh, th, c, vh, vl, w]
  +ev : {vh == I.Int.add(I.Int.add(sh, c), I.Int.neg(vl)) : I.Int} = Equal.trans(I.Int, vh, I.Int.add(I.Int.add(vh, vl), I.Int.neg(vl)), I.Int.add(I.Int.add(sh, c), I.Int.neg(vl)),
    BP.IntN(env, R.V(7n), R.Ad(R.Ad(R.V(7n), R.V(8n)), R.Ng(R.V(8n))), [], [], {==}, Unit{}),
    Equal.cong(I.Int, I.Int, v => I.Int.add(v, I.Int.neg(vl)), I.Int.add(vh, vl), I.Int.add(sh, c), h4))
  Equal.trans(I.Int, A.eta(p, xh, xl, yh, yl), I.Int.add(I.Int.add(vh, w), I.Int.neg(X)), I.Int.add(A.e1(p, xh, xl, yh, yl), A.e2(p, xh, xl, yh, yl)),
    Equal.cong(I.Int, I.Int, v => I.Int.add(v, I.Int.neg(X)), A.z(p, xh, xl, yh, yl), I.Int.add(vh, w), h6),
    Equal.trans(I.Int, I.Int.add(I.Int.add(vh, w), I.Int.neg(X)), I.Int.add(I.Int.add(I.Int.add(I.Int.add(sh, c), I.Int.neg(vl)), w), I.Int.neg(X)), I.Int.add(A.e1(p, xh, xl, yh, yl), A.e2(p, xh, xl, yh, yl)),
      Equal.cong(I.Int, I.Int, v => I.Int.add(I.Int.add(v, w), I.Int.neg(X)), vh, I.Int.add(I.Int.add(sh, c), I.Int.neg(vl)), ev),
      BP.IntN(env, R.Ad(R.Ad(R.Ad(R.Ad(R.V(4n), R.V(6n)), R.Ng(R.V(8n))), R.V(9n)), R.Ng(R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(2n), R.V(3n))))),
        R.Ad(R.Ad(R.V(6n), R.Ng(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(2n)), R.Ng(R.V(4n))), R.V(5n)))), R.Ad(R.V(9n), R.Ng(R.Ad(R.Ad(R.Ad(R.V(1n), R.V(3n)), R.Ng(R.V(5n))), R.V(8n))))), [], [], {==}, Unit{})))

# Magnitude helpers
# -----------------

def Mag.flip(+a: I.Int, +b: I.Int) -> {RD.Int.mag(I.Int.add(a, I.Int.neg(b))) == RD.Int.mag(I.Int.add(b, I.Int.neg(a))) : Nat}:
  +env : List<&2, I.Int> = [a, b]
  Equal.trans(Nat, RD.Int.mag(I.Int.add(a, I.Int.neg(b))), RD.Int.mag(I.Int.neg(I.Int.add(b, I.Int.neg(a)))), RD.Int.mag(I.Int.add(b, I.Int.neg(a))),
    Equal.cong(I.Int, Nat, v => RD.Int.mag(v), I.Int.add(a, I.Int.neg(b)), I.Int.neg(I.Int.add(b, I.Int.neg(a))), BP.IntN(env, R.Ad(R.V(0n), R.Ng(R.V(1n))), R.Ng(R.Ad(R.V(1n), R.Ng(R.V(0n)))), [], [], {==}, Unit{})),
    E.Mag.neg(I.Int.add(b, I.Int.neg(a))))

# |a| <= |a + b| + |b|
def Mag.rev(+a: I.Int, +b: I.Int) -> {RD.Nat.lt(Nat.add(RD.Int.mag(I.Int.add(a, b)), RD.Int.mag(b)), RD.Int.mag(a)) == False{} : Bool}:
  +env : List<&2, I.Int> = [a, b]
  +ea : {a == I.Int.add(I.Int.add(a, b), I.Int.neg(b)) : I.Int} = BP.IntN(env, R.V(0n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(1n))), [], [], {==}, Unit{})
  E.Le.trans(RD.Int.mag(a), Nat.add(RD.Int.mag(I.Int.add(a, b)), RD.Int.mag(I.Int.neg(b))), Nat.add(RD.Int.mag(I.Int.add(a, b)), RD.Int.mag(b)),
    E.Le.trans(RD.Int.mag(a), RD.Int.mag(I.Int.add(I.Int.add(a, b), I.Int.neg(b))), Nat.add(RD.Int.mag(I.Int.add(a, b)), RD.Int.mag(I.Int.neg(b))),
      E.Le.eq(RD.Int.mag(a), RD.Int.mag(I.Int.add(I.Int.add(a, b), I.Int.neg(b))), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), a, I.Int.add(I.Int.add(a, b), I.Int.neg(b)), ea)),
      E2.Mag.tri(I.Int.add(a, b), I.Int.neg(b))),
    E.Le.eq(Nat.add(RD.Int.mag(I.Int.add(a, b)), RD.Int.mag(I.Int.neg(b))), Nat.add(RD.Int.mag(I.Int.add(a, b)), RD.Int.mag(b)), Equal.cong(Nat, Nat, v => Nat.add(RD.Int.mag(I.Int.add(a, b)), v), RD.Int.mag(I.Int.neg(b)), RD.Int.mag(b), E.Mag.neg(b))))

# |a + b| >= |a| - |b|, as: |a| <= kb + m and |b| <= kb give m <= |a + b| when |a| >= m + kb
def Mag.low(+a: I.Int, +b: I.Int, +m: Nat, +kb: Nat, +ha: {RD.Nat.lt(RD.Int.mag(a), Nat.add(m, kb)) == False{} : Bool}, +hb: {RD.Nat.lt(kb, RD.Int.mag(b)) == False{} : Bool})
  -> {RD.Nat.lt(RD.Int.mag(I.Int.add(a, b)), m) == False{} : Bool}:
  E2.Le.canl(kb, m, RD.Int.mag(I.Int.add(a, b)),
    E.Le.trans(Nat.add(kb, m), RD.Int.mag(a), Nat.add(kb, RD.Int.mag(I.Int.add(a, b))),
      E.Le.trans(Nat.add(kb, m), Nat.add(m, kb), RD.Int.mag(a), E.Le.eq(Nat.add(kb, m), Nat.add(m, kb), NL.Nat.add_comm(kb, m)), ha),
      E.Le.trans(RD.Int.mag(a), Nat.add(RD.Int.mag(I.Int.add(a, b)), RD.Int.mag(b)), Nat.add(kb, RD.Int.mag(I.Int.add(a, b))), Mag.rev(a, b),
        E.Le.trans(Nat.add(RD.Int.mag(I.Int.add(a, b)), RD.Int.mag(b)), Nat.add(RD.Int.mag(I.Int.add(a, b)), kb), Nat.add(kb, RD.Int.mag(I.Int.add(a, b))),
          E2.Le.addl(RD.Int.mag(I.Int.add(a, b)), RD.Int.mag(b), kb, hb), E.Le.eq(Nat.add(RD.Int.mag(I.Int.add(a, b)), kb), Nat.add(kb, RD.Int.mag(I.Int.add(a, b))), NL.Nat.add_comm(RD.Int.mag(I.Int.add(a, b)), kb))))))

# doubled triangle inequality
def Dbl.tri(+a: I.Int, +b: I.Int, +ka: Nat, +kb: Nat, +ha: {RD.Nat.lt(ka, Nat.double(RD.Int.mag(a))) == False{} : Bool}, +hb: {RD.Nat.lt(kb, Nat.double(RD.Int.mag(b))) == False{} : Bool})
  -> {RD.Nat.lt(Nat.add(ka, kb), Nat.double(RD.Int.mag(I.Int.add(a, b)))) == False{} : Bool}:
  E.Le.trans(Nat.double(RD.Int.mag(I.Int.add(a, b))), Nat.double(Nat.add(RD.Int.mag(a), RD.Int.mag(b))), Nat.add(ka, kb), E.Le.dd(RD.Int.mag(I.Int.add(a, b)), Nat.add(RD.Int.mag(a), RD.Int.mag(b)), E2.Mag.tri(a, b)),
    E.Le.trans(Nat.double(Nat.add(RD.Int.mag(a), RD.Int.mag(b))), Nat.add(Nat.double(RD.Int.mag(a)), Nat.double(RD.Int.mag(b))), Nat.add(ka, kb),
      E.Le.eq(Nat.double(Nat.add(RD.Int.mag(a), RD.Int.mag(b))), Nat.add(Nat.double(RD.Int.mag(a)), Nat.double(RD.Int.mag(b))), E2.Dbl.add(RD.Int.mag(a), RD.Int.mag(b))),
      E2.Le.add2(Nat.double(RD.Int.mag(a)), ka, Nat.double(RD.Int.mag(b)), kb, ha, hb)))

# the error of a rounding, by its argument's size: |z| <= 2^p X gives 2 |RN z - z| <= X
def EBx(+p1: Nat, +z: I.Int, +X: Nat, +k: Nat, +eX: {X == RD.Nat.pow2(k) : Nat}, +h: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), X), RD.Int.mag(z)) == False{} : Bool})
  -> {RD.Nat.lt(X, Nat.double(RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))))) == False{} : Bool}:
  +er = RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z)))
  Equal.trans(Bool, RD.Nat.lt(X, Nat.double(er)), RD.Nat.lt(RD.Nat.pow2(k), Nat.double(er)), False{}, Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.double(er)), X, RD.Nat.pow2(k), eX),
    W.EB(p1, z, k, Equal.trans(Bool, RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k)), RD.Int.mag(z)), RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), X), RD.Int.mag(z)), False{},
      Equal.cong(Nat, Bool, v => RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), v), RD.Int.mag(z)), RD.Nat.pow2(k), X, Equal.sym(Nat, X, RD.Nat.pow2(k), eX)), h)))

# the same for the error written the other way round
def EBy(+p1: Nat, +z: I.Int, +X: Nat, +k: Nat, +eX: {X == RD.Nat.pow2(k) : Nat}, +h: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), X), RD.Int.mag(z)) == False{} : Bool})
  -> {RD.Nat.lt(X, Nat.double(RD.Int.mag(I.Int.add(z, I.Int.neg(E.RNi(1n+p1, z)))))) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(X, Nat.double(RD.Int.mag(I.Int.add(z, I.Int.neg(E.RNi(1n+p1, z)))))), RD.Nat.lt(X, Nat.double(RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))))), False{},
    Equal.cong(Nat, Bool, v => RD.Nat.lt(X, Nat.double(v)), RD.Int.mag(I.Int.add(z, I.Int.neg(E.RNi(1n+p1, z)))), RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))), Mag.flip(z, E.RNi(1n+p1, z))),
    EBx(p1, z, X, k, eX, h))

# Case 2a of Theorem 3.1: G = 2^p Gq is u (Gq = u², sigma = 1) or 2u
# (sigma = 2), U = 2^p Q is u. For 4G <= |xh + yh| <= (2^p - 2) G,
# |xl| <= U and 2 |yl| <= G: Fast2Sum is exact twice, |e1| <= Gq and
# 2 |e2| <= Gq, so 2 |eta| <= 3 Gq.
def C2a(+p1: Nat, +q: Nat, +gq: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hs1: {RD.Nat.lt(RD.Int.mag(I.Int.add(xh, yh)), Nat.mul(4n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq)))) == False{} : Bool},
  +hs2: {RD.Nat.lt(Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq))), RD.Int.mag(I.Int.add(xh, yh))) == False{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq)), Nat.double(RD.Int.mag(yl))) == False{} : Bool},
  +hG1: {RD.Nat.lt(RD.Nat.pow2(gq), RD.Nat.pow2(q)) == False{} : Bool}, +hG2: {RD.Nat.lt(Nat.double(RD.Nat.pow2(q)), RD.Nat.pow2(gq)) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(3n, RD.Nat.pow2(gq)), Nat.double(RD.Int.mag(A.eta(1n+p1, xh, xl, yh, yl)))) == False{} : Bool}:
  +p : Nat = 1n+p1
  +P = RD.Nat.pow2(1n+p1)
  +H = RD.Nat.pow2(p1)
  +Q = RD.Nat.pow2(q)
  +Gq = RD.Nat.pow2(gq)
  +U = Nat.mul(P, Q)
  +G = Nat.mul(P, Gq)
  +G2 = Nat.double(G)
  +G4 = Nat.double(G2)
  +kG = Nat.add(1n+p1, gq)
  +eG : {G == RD.Nat.pow2(kG) : Nat} = Equal.sym(Nat, RD.Nat.pow2(kG), G, BP.Pow2.add(1n+p1, gq))
  +s = I.Int.add(xh, yh)
  +sh = E.RNi(p, s)
  +sl = A.sl(p, xh, yh)
  +L = I.Int.add(xl, yl)
  +th = E.RNi(p, L)
  +tl = A.tl(p, xl, yl)
  +k1 = I.Int.add(sl, th)
  +c = E.RNi(p, k1)
  +h4P : {RD.Nat.lt(P, 4n) == False{} : Bool} = E2.Pow2.mono(2n, 1n+p1, E.Le.trans(2n, 5n, 1n+p1, {==}, E.Le.trans(5n, p1, 1n+p1, hp, E.Le.add1(p1))))
  +env : List<&2, Nat> = [G, G2, G4]
  +e2 : {G2 == Nat.add(G, G) : Nat} = Y.Nat.double_add(G)
  +e4 : {G4 == Nat.add(G2, G2) : Nat} = Y.Nat.double_add(G2)
  +ea3 : {Nat.add(G2, G) == Nat.mul(3n, G) : Nat} = R.NatN.eq2(env, R.Ad(R.V(1n), R.V(0n)), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{}))), [], [], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n))))], {==}, Unit{}, (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, e2), Unit{}), {==}, {==})
  +ea4 : {Nat.mul(4n, G) == G4 : Nat} = R.NatN.eq2(env, R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{})))), R.V(2n), [], [], [R.Ad(R.Ad(R.V(0n), R.V(0n)), R.Ng(R.V(1n))), R.Ad(R.Ad(R.V(0n), R.V(0n)), R.Ng(R.V(1n))), R.Ad(R.Ad(R.V(1n), R.V(1n)), R.Ng(R.V(2n)))], {==}, Unit{}, (R.NatN.z(env, R.Ad(R.V(0n), R.V(0n)), R.V(1n), {==}, {==}, Equal.sym(Nat, G2, Nat.add(G, G), e2)), (R.NatN.z(env, R.Ad(R.V(0n), R.V(0n)), R.V(1n), {==}, {==}, Equal.sym(Nat, G2, Nat.add(G, G), e2)), (R.NatN.z(env, R.Ad(R.V(1n), R.V(1n)), R.V(2n), {==}, {==}, Equal.sym(Nat, G4, Nat.add(G2, G2), e4)), Unit{}))), {==}, {==})
  +fG : {E.Rn(p, G) == G : Nat} = W.Pk.fix(p1, gq)
  +f2G : {E.Rn(p, G2) == G2 : Nat} = E.Fn.dbl(p1, G, fG)
  # 2 |sl| <= G, 4G <= |sh| <= (2^p - 2) G
  +hsP : {RD.Nat.lt(Nat.mul(P, G), RD.Int.mag(s)) == False{} : Bool} = E.Le.trans(RD.Int.mag(s), Nat.mul(RD.Nat.monus(P, 2n), G), Nat.mul(P, G), hs2, E2.Le.mulr(RD.Nat.monus(P, 2n), P, G, W.Mo.le(P, 2n)))
  +hsl : {RD.Nat.lt(G, Nat.double(RD.Int.mag(sl))) == False{} : Bool} = EBy(p1, s, G, kG, eG, hsP)
  +f4 : {E.Rn(p, Nat.mul(4n, G)) == Nat.mul(4n, G) : Nat} = W.Rn.fix(p1, Nat.mul(4n, G), 4n, kG, Equal.cong(Nat, Nat, v => Nat.mul(4n, v), G, RD.Nat.pow2(kG), eG), h4P)
  +hsh : {RD.Nat.lt(RD.Int.mag(sh), Nat.mul(4n, G)) == False{} : Bool} = W.RL(p1, s, Nat.mul(4n, G), f4, hs1)
  +fPm : {E.Rn(p, Nat.mul(RD.Nat.monus(P, 2n), G)) == Nat.mul(RD.Nat.monus(P, 2n), G) : Nat} = W.Rn.fix(p1, Nat.mul(RD.Nat.monus(P, 2n), G), RD.Nat.monus(P, 2n), kG, Equal.cong(Nat, Nat, v => Nat.mul(RD.Nat.monus(P, 2n), v), G, RD.Nat.pow2(kG), eG), W.Mo.le(P, 2n))
  +hsh2 : {RD.Nat.lt(Nat.mul(RD.Nat.monus(P, 2n), G), RD.Int.mag(sh)) == False{} : Bool} = W.RB(p1, s, Nat.mul(RD.Nat.monus(P, 2n), G), fPm, hs2)
  # |L| <= 2U and 2 |L| <= 3G
  +hUG : {RD.Nat.lt(G, U) == False{} : Bool} = E2.Le.mull(P, Q, Gq, hG1)
  +hG2U : {RD.Nat.lt(Nat.double(U), G) == False{} : Bool} = E.Le.trans(G, Nat.mul(P, Nat.double(Q)), Nat.double(U), E2.Le.mull(P, Gq, Nat.double(Q), hG2), E.Le.eq(Nat.mul(P, Nat.double(Q)), Nat.double(U), R.Nat.mul_double(P, Q)))
  +hyU : {RD.Nat.lt(U, RD.Int.mag(yl)) == False{} : Bool} = W.Le.halve(RD.Int.mag(yl), U, E.Le.trans(Nat.double(RD.Int.mag(yl)), G, Nat.double(U), hy, hG2U))
  +hL : {RD.Nat.lt(Nat.double(U), RD.Int.mag(L)) == False{} : Bool} = E.Le.trans(RD.Int.mag(L), Nat.add(RD.Int.mag(xl), RD.Int.mag(yl)), Nat.double(U), E2.Mag.tri(xl, yl),
    E.Le.trans(Nat.add(RD.Int.mag(xl), RD.Int.mag(yl)), Nat.add(U, U), Nat.double(U), E2.Le.add2(RD.Int.mag(xl), U, RD.Int.mag(yl), U, hx, hyU), E.Le.eq(Nat.add(U, U), Nat.double(U), Equal.sym(Nat, Nat.double(U), Nat.add(U, U), Y.Nat.double_add(U)))))
  +hx2 : {RD.Nat.lt(G2, Nat.double(RD.Int.mag(xl))) == False{} : Bool} = E.Le.dd(RD.Int.mag(xl), G, E.Le.trans(RD.Int.mag(xl), U, G, hx, hUG))
  +hL3 : {RD.Nat.lt(Nat.mul(3n, G), Nat.double(RD.Int.mag(L))) == False{} : Bool} = E.Le.trans(Nat.double(RD.Int.mag(L)), Nat.add(G2, G), Nat.mul(3n, G), Dbl.tri(xl, yl, G2, G, hx2, hy), E.Le.eq(Nat.add(G2, G), Nat.mul(3n, G), ea3))
  # |th| <= 3G/2 = 3 2^(p-1) Gq
  +cth = Nat.mul(3n, Nat.mul(H, Gq))
  +envh : List<&2, Nat> = [H, Gq, P]
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +ecth0 : {Nat.add(cth, cth) == Nat.mul(3n, G) : Nat} = R.NatN.eq(envh, R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(0n), R.V(1n)), N.TZero{}))), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(0n), R.V(1n)), N.TZero{})))), R.Ad(R.Ml(R.V(2n), R.V(1n)), R.Ad(R.Ml(R.V(2n), R.V(1n)), R.Ad(R.Ml(R.V(2n), R.V(1n)), N.TZero{}))), [R.Ad(R.Ad(R.Ng(R.V(1n)), R.Ng(R.V(1n))), R.Ng(R.V(1n)))], [R.Ad(R.V(2n), R.Ng(R.Ad(R.V(0n), R.V(0n))))], {==}, (R.NatN.z(envh, R.V(2n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, eP), Unit{}), {==}, {==})
  +ecth : {Nat.double(cth) == Nat.mul(3n, G) : Nat} = Equal.trans(Nat, Nat.double(cth), Nat.add(cth, cth), Nat.mul(3n, G), Y.Nat.double_add(cth), ecth0)
  +hLc : {RD.Nat.lt(cth, RD.Int.mag(L)) == False{} : Bool} = W.Le.halve(RD.Int.mag(L), cth, E.Le.trans(Nat.double(RD.Int.mag(L)), Nat.mul(3n, G), Nat.double(cth), hL3, E.Le.eq(Nat.mul(3n, G), Nat.double(cth), Equal.sym(Nat, Nat.double(cth), Nat.mul(3n, G), ecth))))
  +fth : {E.Rn(p, cth) == cth : Nat} = W.Rn.fix(p1, cth, 3n, Nat.add(p1, gq), Equal.cong(Nat, Nat, v => Nat.mul(3n, v), Nat.mul(H, Gq), RD.Nat.pow2(Nat.add(p1, gq)), Equal.sym(Nat, RD.Nat.pow2(Nat.add(p1, gq)), Nat.mul(H, Gq), BP.Pow2.add(p1, gq))),
    E.Le.trans(3n, 4n, P, {==}, h4P))
  +hth : {RD.Nat.lt(cth, RD.Int.mag(th)) == False{} : Bool} = W.RB(p1, L, cth, fth, hLc)
  +hth3 : {RD.Nat.lt(Nat.mul(3n, G), Nat.double(RD.Int.mag(th))) == False{} : Bool} = E.Le.trans(Nat.double(RD.Int.mag(th)), Nat.double(cth), Nat.mul(3n, G), E.Le.dd(RD.Int.mag(th), cth, hth), E.Le.eq(Nat.double(cth), Nat.mul(3n, G), ecth))
  # |tl| <= Q
  +hLP : {RD.Nat.lt(Nat.mul(P, Nat.double(Q)), RD.Int.mag(L)) == False{} : Bool} = E.Le.trans(RD.Int.mag(L), Nat.double(U), Nat.mul(P, Nat.double(Q)), hL, E.Le.eq(Nat.double(U), Nat.mul(P, Nat.double(Q)), Equal.sym(Nat, Nat.mul(P, Nat.double(Q)), Nat.double(U), R.Nat.mul_double(P, Q))))
  +htl : {RD.Nat.lt(Nat.double(Q), Nat.double(RD.Int.mag(tl))) == False{} : Bool} = EBy(p1, L, Nat.double(Q), 1n+q, {==}, hLP)
  # |sl + th| <= 2G, so |c| <= 2G and |e1| <= Gq
  +hk4 : {RD.Nat.lt(Nat.mul(4n, G), Nat.double(RD.Int.mag(k1))) == False{} : Bool} = Dbl.tri(sl, th, G, Nat.mul(3n, G), hsl, hth3)
  +hk1 : {RD.Nat.lt(G2, RD.Int.mag(k1)) == False{} : Bool} = W.Le.halve(RD.Int.mag(k1), G2, E.Le.trans(Nat.double(RD.Int.mag(k1)), Nat.mul(4n, G), G4, hk4, E.Le.eq(Nat.mul(4n, G), G4, ea4)))
  +hc : {RD.Nat.lt(G2, RD.Int.mag(c)) == False{} : Bool} = W.RB(p1, k1, G2, f2G, hk1)
  +hk1P : {RD.Nat.lt(Nat.mul(P, Nat.double(Gq)), RD.Int.mag(k1)) == False{} : Bool} = E.Le.trans(RD.Int.mag(k1), G2, Nat.mul(P, Nat.double(Gq)), hk1, E.Le.eq(G2, Nat.mul(P, Nat.double(Gq)), Equal.sym(Nat, Nat.mul(P, Nat.double(Gq)), G2, R.Nat.mul_double(P, Gq))))
  +he1 : {RD.Nat.lt(Nat.double(Gq), Nat.double(RD.Int.mag(A.e1(1n+p1, xh, xl, yh, yl)))) == False{} : Bool} = EBx(p1, k1, Nat.double(Gq), 1n+gq, {==}, hk1P)
  # line 4: |c| <= 2G <= 4G <= |sh|
  +hG24 : {RD.Nat.lt(Nat.mul(4n, G), G2) == False{} : Bool} = E.Le.trans(G2, G4, Nat.mul(4n, G), E2.Le.dbl(G2), E.Le.eq(G4, Nat.mul(4n, G), Equal.sym(Nat, Nat.mul(4n, G), G4, ea4)))
  +hle4 : {RD.Nat.lt(RD.Int.mag(sh), RD.Int.mag(c)) == False{} : Bool} = E.Le.trans(RD.Int.mag(c), G2, RD.Int.mag(sh), hc, E.Le.trans(G2, Nat.mul(4n, G), RD.Int.mag(sh), hG24, hsh))
  +h4 : {I.Int.add(E.F2.s(p, sh, c), E.F2.t(p, sh, c)) == I.Int.add(sh, c) : I.Int} = E.Fast2Sum(p1, sh, c, W.Rf.i(p1, s), W.Rf.i(p1, k1), hle4)
  # 2 |vl| <= G: |sh + c| <= (2^p - 2) G + 2G
  +sc = I.Int.add(sh, c)
  +vh = E.F2.s(p, sh, c)
  +vl = E.F2.t(p, sh, c)
  +envv : List<&2, I.Int> = [vh, vl]
  +evl : {vl == I.Int.add(sc, I.Int.neg(E.RNi(p, sc))) : I.Int} = Equal.trans(I.Int, vl, I.Int.add(I.Int.add(vh, vl), I.Int.neg(vh)), I.Int.add(sc, I.Int.neg(E.RNi(p, sc))),
    BP.IntN(envv, R.V(1n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(0n))), [], [], {==}, Unit{}),
    Equal.cong(I.Int, I.Int, v => I.Int.add(v, I.Int.neg(vh)), I.Int.add(vh, vl), sc, h4))
  +m = RD.Nat.monus(P, 2n)
  +mG = Nat.mul(m, G)
  +eP2 : {P == Nat.add(2n, m) : Nat} = E.Le.wit(2n, P, E.Le.trans(2n, 4n, P, {==}, h4P))
  +envm : List<&2, Nat> = [mG, G, G2]
  +epm0 : {Nat.add(mG, G2) == Nat.add(G, Nat.add(G, mG)) : Nat} = R.NatN.eq2(envm, R.Ad(R.V(0n), R.V(2n)), R.Ad(R.V(1n), R.Ad(R.V(1n), R.V(0n))), [], [], [R.Ad(R.V(2n), R.Ng(R.Ad(R.V(1n), R.V(1n))))], {==}, Unit{}, (R.NatN.z(envm, R.V(2n), R.Ad(R.V(1n), R.V(1n)), {==}, {==}, e2), Unit{}), {==}, {==})
  +epm : {Nat.add(mG, G2) == Nat.mul(P, G) : Nat} = Equal.trans(Nat, Nat.add(mG, G2), Nat.add(G, Nat.add(G, mG)), Nat.mul(P, G), epm0,
    Equal.cong(Nat, Nat, v => Nat.mul(v, G), Nat.add(2n, m), P, Equal.sym(Nat, P, Nat.add(2n, m), eP2)))
  +hscP : {RD.Nat.lt(Nat.mul(P, G), RD.Int.mag(sc)) == False{} : Bool} = E.Le.trans(RD.Int.mag(sc), Nat.add(RD.Int.mag(sh), RD.Int.mag(c)), Nat.mul(P, G), E2.Mag.tri(sh, c),
    E.Le.trans(Nat.add(RD.Int.mag(sh), RD.Int.mag(c)), Nat.add(mG, G2), Nat.mul(P, G), E2.Le.add2(RD.Int.mag(sh), mG, RD.Int.mag(c), G2, hsh2, hc), E.Le.eq(Nat.add(mG, G2), Nat.mul(P, G), epm)))
  +hvl : {RD.Nat.lt(G, Nat.double(RD.Int.mag(vl))) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(G, Nat.double(RD.Int.mag(vl))), RD.Nat.lt(G, Nat.double(RD.Int.mag(I.Int.add(sc, I.Int.neg(E.RNi(p, sc)))))), False{},
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(G, Nat.double(RD.Int.mag(v))), vl, I.Int.add(sc, I.Int.neg(E.RNi(p, sc))), evl), EBy(p1, sc, G, kG, eG, hscP))
  # |tl + vl| <= G: 2 |e2| <= Gq and |w| <= G
  +tv = I.Int.add(tl, vl)
  +hQU : {RD.Nat.lt(U, Nat.double(Q)) == False{} : Bool} = E.Le.trans(Nat.double(Q), Nat.mul(RD.Nat.pow2(1n), Q), U,
    E.Le.eq(Nat.double(Q), Nat.mul(RD.Nat.pow2(1n), Q), Equal.sym(Nat, Nat.mul(RD.Nat.pow2(1n), Q), Nat.double(Q), Equal.trans(Nat, Nat.mul(Nat.double(1n), Q), Nat.double(Nat.mul(1n, Q)), Nat.double(Q), BP.Mul.dbl_l(1n, Q), Equal.cong(Nat, Nat, v => Nat.double(v), Nat.mul(1n, Q), Q, P3.Mul.one_l(Q))))),
    E2.Le.mulr(RD.Nat.pow2(1n), P, Q, E2.Pow2.mono(1n, 1n+p1, BP.Lt.z(p1))))
  +htv : {RD.Nat.lt(Nat.add(Nat.double(Q), G), Nat.double(RD.Int.mag(tv))) == False{} : Bool} = Dbl.tri(tl, vl, Nat.double(Q), G, htl, hvl)
  +htv2 : {RD.Nat.lt(G, RD.Int.mag(tv)) == False{} : Bool} = W.Le.halve(RD.Int.mag(tv), G, E.Le.trans(Nat.double(RD.Int.mag(tv)), Nat.add(Nat.double(Q), G), Nat.double(G), htv,
    E.Le.trans(Nat.add(Nat.double(Q), G), Nat.add(G, G), Nat.double(G), E2.Le.addr(Nat.double(Q), G, G, E.Le.trans(Nat.double(Q), U, G, hQU, hUG)), E.Le.eq(Nat.add(G, G), Nat.double(G), Equal.sym(Nat, Nat.double(G), Nat.add(G, G), Y.Nat.double_add(G))))))
  +he2 : {RD.Nat.lt(Gq, Nat.double(RD.Int.mag(A.e2(1n+p1, xh, xl, yh, yl)))) == False{} : Bool} = EBx(p1, tv, Gq, gq, {==}, htv2)
  +hw : {RD.Nat.lt(G, RD.Int.mag(E.RNi(p, tv))) == False{} : Bool} = W.RB(p1, tv, G, fG, htv2)
  # line 6: |vh| >= 2G >= |w|
  +hsc : {RD.Nat.lt(RD.Int.mag(sc), G2) == False{} : Bool} = Mag.low(sh, c, G2, G2, E.Le.trans(Nat.add(G2, G2), Nat.mul(4n, G), RD.Int.mag(sh), E.Le.eq(Nat.add(G2, G2), Nat.mul(4n, G), Equal.sym(Nat, Nat.mul(4n, G), Nat.add(G2, G2), Equal.trans(Nat, Nat.mul(4n, G), G4, Nat.add(G2, G2), ea4, e4))), hsh), hc)
  +hvh : {RD.Nat.lt(RD.Int.mag(vh), G2) == False{} : Bool} = W.RL(p1, sc, G2, f2G, hsc)
  +hle6 : {RD.Nat.lt(RD.Int.mag(vh), RD.Int.mag(E.RNi(p, tv))) == False{} : Bool} = E.Le.trans(RD.Int.mag(E.RNi(p, tv)), G, RD.Int.mag(vh), hw, E.Le.trans(G, G2, RD.Int.mag(vh), E2.Le.dbl(G), hvh))
  +h6 : {A.z(p, xh, xl, yh, yl) == I.Int.add(vh, E.RNi(p, tv)) : I.Int} = E.Fast2Sum(p1, vh, E.RNi(p, tv), W.Rf.i(p1, sc), W.Rf.i(p1, tv), hle6)
  # eta = e1 + e2
  +ee : {A.eta(1n+p1, xh, xl, yh, yl) == I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl)) : I.Int} = A.split(p, xh, xl, yh, yl, h4, h6)
  +envq : List<&2, Nat> = [Gq, Nat.double(Gq), Nat.mul(4n, Gq)]
  +eq2 : {Nat.double(Gq) == Nat.add(Gq, Gq) : Nat} = Y.Nat.double_add(Gq)
  +e3q : {Nat.add(Nat.double(Gq), Gq) == Nat.mul(3n, Gq) : Nat} = R.NatN.eq2(envq, R.Ad(R.V(1n), R.V(0n)), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{}))), [], [], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n))))], {==}, Unit{}, (R.NatN.z(envq, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, eq2), Unit{}), {==}, {==})
  Equal.trans(Bool, RD.Nat.lt(Nat.mul(3n, Gq), Nat.double(RD.Int.mag(A.eta(1n+p1, xh, xl, yh, yl)))), RD.Nat.lt(Nat.mul(3n, Gq), Nat.double(RD.Int.mag(I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl))))), False{},
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(Nat.mul(3n, Gq), Nat.double(RD.Int.mag(v))), A.eta(1n+p1, xh, xl, yh, yl), I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl)), ee),
    E.Le.trans(Nat.double(RD.Int.mag(I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl)))), Nat.add(Nat.double(Gq), Gq), Nat.mul(3n, Gq), Dbl.tri(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl), Nat.double(Gq), Gq, he1, he2), E.Le.eq(Nat.add(Nat.double(Gq), Gq), Nat.mul(3n, Gq), e3q)))


# 2 X and 4 X as doublings
def Mul2(+X: Nat) -> {Nat.mul(2n, X) == Nat.double(X) : Nat}:
  +env : List<&2, Nat> = [X, Nat.double(X)]
  +e2 : {Nat.double(X) == Nat.add(X, X) : Nat} = Y.Nat.double_add(X)
  R.NatN.eq2(env, R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{})), R.V(1n), [], [], [R.Ad(R.Ad(R.V(0n), R.V(0n)), R.Ng(R.V(1n)))], {==}, Unit{},
    (R.NatN.z(env, R.Ad(R.V(0n), R.V(0n)), R.V(1n), {==}, {==}, Equal.sym(Nat, Nat.double(X), Nat.add(X, X), e2)), Unit{}), {==}, {==})

def Mul4(+X: Nat) -> {Nat.mul(4n, X) == Nat.double(Nat.double(X)) : Nat}:
  +X2 = Nat.double(X)
  +X4 = Nat.double(X2)
  +env : List<&2, Nat> = [X, X2, X4]
  +e2 : {X2 == Nat.add(X, X) : Nat} = Y.Nat.double_add(X)
  +e4 : {X4 == Nat.add(X2, X2) : Nat} = Y.Nat.double_add(X2)
  R.NatN.eq2(env, R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{})))), R.V(2n), [], [],
    [R.Ad(R.Ad(R.V(0n), R.V(0n)), R.Ng(R.V(1n))), R.Ad(R.Ad(R.V(0n), R.V(0n)), R.Ng(R.V(1n))), R.Ad(R.Ad(R.V(1n), R.V(1n)), R.Ng(R.V(2n)))], {==}, Unit{},
    (R.NatN.z(env, R.Ad(R.V(0n), R.V(0n)), R.V(1n), {==}, {==}, Equal.sym(Nat, X2, Nat.add(X, X), e2)),
      (R.NatN.z(env, R.Ad(R.V(0n), R.V(0n)), R.V(1n), {==}, {==}, Equal.sym(Nat, X2, Nat.add(X, X), e2)),
        (R.NatN.z(env, R.Ad(R.V(1n), R.V(1n)), R.V(2n), {==}, {==}, Equal.sym(Nat, X4, Nat.add(X2, X2), e4)), Unit{}))), {==}, {==})

# c <= n <= c + k gives |c - n| <= k
def Dist.le(+c: Nat, +n: Nat, +k: Nat, +h1: {RD.Nat.lt(n, c) == False{} : Bool}, +h2: {RD.Nat.lt(Nat.add(c, k), n) == False{} : Bool})
  -> {RD.Nat.lt(k, E.Dist(c, n)) == False{} : Bool}:
  +d = RD.Nat.monus(n, c)
  +en : {n == Nat.add(c, d) : Nat} = E.Le.wit(c, n, h1)
  E.Le.trans(E.Dist(c, n), d, k, E.Le.eq(E.Dist(c, n), d, Equal.trans(Nat, E.Dist(c, n), E.Dist(c, Nat.add(c, d)), d, Equal.cong(Nat, Nat, v => E.Dist(c, v), n, Nat.add(c, d), en), E.Dist.up(c, d))),
    E2.Le.canl(c, d, k, E.Le.trans(Nat.add(c, d), n, Nat.add(c, k), E.Le.eq(Nat.add(c, d), n, Equal.sym(Nat, n, Nat.add(c, d), en)), h2)))

# the rounding error below 2X + Q, for X = 2^p Q: at most Q either way
def E2q.go(+p1: Nat, +q: Nat, +z: I.Int, +h: {RD.Nat.lt(Nat.add(Nat.mul(RD.Nat.pow2(1n+p1), Nat.double(RD.Nat.pow2(q))), RD.Nat.pow2(q)), RD.Int.mag(z)) == False{} : Bool},
  l: Bool, +el: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), Nat.double(RD.Nat.pow2(q))), RD.Int.mag(z)) == l : Bool})
  -> {RD.Nat.lt(Nat.double(RD.Nat.pow2(q)), Nat.double(RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))))) == False{} : Bool}:
  match l:
    case False{}:
      EBx(p1, z, Nat.double(RD.Nat.pow2(q)), 1n+q, {==}, el)
    case True{}:
      +Q = RD.Nat.pow2(q)
      +c = Nat.mul(RD.Nat.pow2(1n+p1), Nat.double(Q))
      +m = RD.Int.mag(z)
      +hd : {RD.Nat.lt(Q, E.Dist(E.Rn(1n+p1, m), m)) == False{} : Bool} = E.Le.trans(E.Dist(E.Rn(1n+p1, m), m), E.Dist(c, m), Q, E.Near(p1, m, c, W.Pk.fix(p1, 1n+q)),
        Dist.le(c, m, Q, E2.Lt.to_le(c, m, el), h))
      Equal.trans(Bool, RD.Nat.lt(Nat.double(Q), Nat.double(RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))))), RD.Nat.lt(Nat.double(Q), Nat.double(E.Dist(E.Rn(1n+p1, m), m))), False{},
        Equal.cong(Nat, Bool, v => RD.Nat.lt(Nat.double(Q), Nat.double(v)), RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))), E.Dist(E.Rn(1n+p1, m), m), W.Err.i(1n+p1, z)),
        E.Le.dd(E.Dist(E.Rn(1n+p1, m), m), Q, hd))

def E2q(+p1: Nat, +q: Nat, +z: I.Int, +h: {RD.Nat.lt(Nat.add(Nat.mul(RD.Nat.pow2(1n+p1), Nat.double(RD.Nat.pow2(q))), RD.Nat.pow2(q)), RD.Int.mag(z)) == False{} : Bool})
  -> {RD.Nat.lt(Nat.double(RD.Nat.pow2(q)), Nat.double(RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))))) == False{} : Bool}:
  E2q.go(p1, q, z, h, RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), Nat.double(RD.Nat.pow2(q))), RD.Int.mag(z)), {==})

# Case 2b of Theorem 3.1: 2 - 4u < |xh + yh| <= 4 - 4u, |xl|, |yl| <= u:
# |e1| <= 2u², |e2| <= u², so |eta| <= 3u²
def C2b(+p1: Nat, +q: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hs1: {RD.Nat.lt(RD.Int.mag(I.Int.add(xh, yh)), Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))) == False{} : Bool},
  +hs2: {RD.Nat.lt(Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 1n), Nat.double(Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))), RD.Int.mag(I.Int.add(xh, yh))) == False{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(yl)) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(3n, RD.Nat.pow2(q)), RD.Int.mag(A.eta(1n+p1, xh, xl, yh, yl))) == False{} : Bool}:
  +p : Nat = 1n+p1
  +P = RD.Nat.pow2(1n+p1)
  +H = RD.Nat.pow2(p1)
  +Q = RD.Nat.pow2(q)
  +U = Nat.mul(P, Q)
  +U2 = Nat.double(U)
  +U4 = Nat.double(U2)
  +U8 = Nat.double(U4)
  +Q2 = Nat.double(Q)
  +Q4 = Nat.double(Q2)
  +kU = Nat.add(1n+p1, q)
  +eU : {U == RD.Nat.pow2(kU) : Nat} = Equal.sym(Nat, RD.Nat.pow2(kU), U, BP.Pow2.add(1n+p1, q))
  +eU2 : {U2 == RD.Nat.pow2(1n+kU) : Nat} = Equal.cong(Nat, Nat, v => Nat.double(v), U, RD.Nat.pow2(kU), eU)
  +eU4 : {U4 == RD.Nat.pow2(2n+kU) : Nat} = Equal.cong(Nat, Nat, v => Nat.double(Nat.double(v)), U, RD.Nat.pow2(kU), eU)
  +eUq2 : {Nat.mul(P, Q2) == U2 : Nat} = R.Nat.mul_double(P, Q)
  +eUq4 : {Nat.mul(P, Q4) == U4 : Nat} = Equal.trans(Nat, Nat.mul(P, Q4), Nat.double(Nat.mul(P, Q2)), U4, R.Nat.mul_double(P, Q2), Equal.cong(Nat, Nat, v => Nat.double(v), Nat.mul(P, Q2), U2, eUq2))
  +s = I.Int.add(xh, yh)
  +sh = E.RNi(p, s)
  +sl = A.sl(p, xh, yh)
  +L = I.Int.add(xl, yl)
  +th = E.RNi(p, L)
  +tl = A.tl(p, xl, yl)
  +k1 = I.Int.add(sl, th)
  +c = E.RNi(p, k1)
  +h6P : {RD.Nat.lt(P, 6n) == False{} : Bool} = E.Le.trans(6n, 8n, P, {==}, E2.Pow2.mono(3n, 1n+p1, E.Le.trans(3n, 5n, 1n+p1, {==}, E.Le.trans(5n, p1, 1n+p1, hp, E.Le.add1(p1)))))
  +m2 = RD.Nat.monus(P, 2n)
  +eP2 : {P == Nat.add(2n, m2) : Nat} = E.Le.wit(2n, P, E.Le.trans(2n, 6n, P, {==}, h6P))
  +hm2 : {RD.Nat.lt(m2, 4n) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(m2, 4n), RD.Nat.lt(P, 6n), False{}, Equal.cong(Nat, Bool, v => RD.Nat.lt(v, 6n), Nat.add(2n, m2), P, Equal.sym(Nat, P, Nat.add(2n, m2), eP2)), h6P)
  +fU2 : {E.Rn(p, U2) == U2 : Nat} = E.Fn.eq(p, U2, Nat.mul(P, Q2), Equal.sym(Nat, Nat.mul(P, Q2), U2, eUq2), W.Pk.fix(p1, 1n+q))
  +fU4 : {E.Rn(p, U4) == U4 : Nat} = E.Fn.dbl(p1, U2, fU2)
  # 2 |sl| <= 4U
  +hsP : {RD.Nat.lt(Nat.mul(P, U4), RD.Int.mag(s)) == False{} : Bool} = E.Le.trans(RD.Int.mag(s), Nat.mul(RD.Nat.monus(P, 1n), U4), Nat.mul(P, U4), hs2, E2.Le.mulr(RD.Nat.monus(P, 1n), P, U4, W.Mo.le(P, 1n)))
  +hsl : {RD.Nat.lt(U4, Nat.double(RD.Int.mag(sl))) == False{} : Bool} = EBy(p1, s, U4, 2n+kU, eU4, hsP)
  +hsl2 : {RD.Nat.lt(U2, RD.Int.mag(sl)) == False{} : Bool} = W.Le.halve(RD.Int.mag(sl), U2, hsl)
  # |sh| >= (2^p - 2) 2U >= 8U, |sh| <= (2^p - 1) 4U
  +fs1 : {E.Rn(p, Nat.mul(m2, U2)) == Nat.mul(m2, U2) : Nat} = W.Rn.fix(p1, Nat.mul(m2, U2), m2, 1n+kU, Equal.cong(Nat, Nat, v => Nat.mul(m2, v), U2, RD.Nat.pow2(1n+kU), eU2), W.Mo.le(P, 2n))
  +hsh : {RD.Nat.lt(RD.Int.mag(sh), Nat.mul(m2, U2)) == False{} : Bool} = W.RL(p1, s, Nat.mul(m2, U2), fs1, hs1)
  +h8 : {RD.Nat.lt(Nat.mul(m2, U2), U8) == False{} : Bool} = E.Le.trans(U8, Nat.mul(4n, U2), Nat.mul(m2, U2), E.Le.eq(U8, Nat.mul(4n, U2), Equal.sym(Nat, Nat.mul(4n, U2), U8, Mul4(U2))), E2.Le.mulr(4n, m2, U2, hm2))
  +hsh8 : {RD.Nat.lt(RD.Int.mag(sh), U8) == False{} : Bool} = E.Le.trans(U8, Nat.mul(m2, U2), RD.Int.mag(sh), h8, hsh)
  +m1 = RD.Nat.monus(P, 1n)
  +fs2 : {E.Rn(p, Nat.mul(m1, U4)) == Nat.mul(m1, U4) : Nat} = W.Rn.fix(p1, Nat.mul(m1, U4), m1, 2n+kU, Equal.cong(Nat, Nat, v => Nat.mul(m1, v), U4, RD.Nat.pow2(2n+kU), eU4), W.Mo.le(P, 1n))
  +hsh2 : {RD.Nat.lt(Nat.mul(m1, U4), RD.Int.mag(sh)) == False{} : Bool} = W.RB(p1, s, Nat.mul(m1, U4), fs2, hs2)
  # |L| <= 2U: |th| <= 2U, |tl| <= Q
  +hL : {RD.Nat.lt(U2, RD.Int.mag(L)) == False{} : Bool} = E.Le.trans(RD.Int.mag(L), Nat.add(RD.Int.mag(xl), RD.Int.mag(yl)), U2, E2.Mag.tri(xl, yl),
    E.Le.trans(Nat.add(RD.Int.mag(xl), RD.Int.mag(yl)), Nat.add(U, U), U2, E2.Le.add2(RD.Int.mag(xl), U, RD.Int.mag(yl), U, hx, hy), E.Le.eq(Nat.add(U, U), U2, Equal.sym(Nat, U2, Nat.add(U, U), Y.Nat.double_add(U)))))
  +hth : {RD.Nat.lt(U2, RD.Int.mag(th)) == False{} : Bool} = W.RB(p1, L, U2, fU2, hL)
  +htl : {RD.Nat.lt(Q2, Nat.double(RD.Int.mag(tl))) == False{} : Bool} = EBy(p1, L, Q2, 1n+q, {==}, E.Le.trans(RD.Int.mag(L), U2, Nat.mul(P, Q2), hL, E.Le.eq(U2, Nat.mul(P, Q2), Equal.sym(Nat, Nat.mul(P, Q2), U2, eUq2))))
  +htl2 : {RD.Nat.lt(Q, RD.Int.mag(tl)) == False{} : Bool} = W.Le.halve(RD.Int.mag(tl), Q, htl)
  # |sl + th| <= 4U: |c| <= 4U, |e1| <= 2u²
  +hk1 : {RD.Nat.lt(U4, RD.Int.mag(k1)) == False{} : Bool} = E.Le.trans(RD.Int.mag(k1), Nat.add(U2, U2), U4, W.Tri2(sl, th, U2, U2, hsl2, hth), E.Le.eq(Nat.add(U2, U2), U4, Equal.sym(Nat, U4, Nat.add(U2, U2), Y.Nat.double_add(U2))))
  +hc : {RD.Nat.lt(U4, RD.Int.mag(c)) == False{} : Bool} = W.RB(p1, k1, U4, fU4, hk1)
  +he1 : {RD.Nat.lt(Q4, Nat.double(RD.Int.mag(A.e1(1n+p1, xh, xl, yh, yl)))) == False{} : Bool} = EBx(p1, k1, Q4, 2n+q, {==}, E.Le.trans(RD.Int.mag(k1), U4, Nat.mul(P, Q4), hk1, E.Le.eq(U4, Nat.mul(P, Q4), Equal.sym(Nat, Nat.mul(P, Q4), U4, eUq4))))
  # line 4
  +hle4 : {RD.Nat.lt(RD.Int.mag(sh), RD.Int.mag(c)) == False{} : Bool} = E.Le.trans(RD.Int.mag(c), U4, RD.Int.mag(sh), hc, E.Le.trans(U4, U8, RD.Int.mag(sh), E2.Le.dbl(U4), hsh8))
  +h4 : {I.Int.add(E.F2.s(p, sh, c), E.F2.t(p, sh, c)) == I.Int.add(sh, c) : I.Int} = E.Fast2Sum(p1, sh, c, W.Rf.i(p1, s), W.Rf.i(p1, k1), hle4)
  # |vl| <= 2U: |sh + c| <= (2^p - 1) 4U + 4U
  +sc = I.Int.add(sh, c)
  +vh = E.F2.s(p, sh, c)
  +vl = E.F2.t(p, sh, c)
  +envv : List<&2, I.Int> = [vh, vl]
  +evl : {vl == I.Int.add(sc, I.Int.neg(E.RNi(p, sc))) : I.Int} = Equal.trans(I.Int, vl, I.Int.add(I.Int.add(vh, vl), I.Int.neg(vh)), I.Int.add(sc, I.Int.neg(E.RNi(p, sc))),
    BP.IntN(envv, R.V(1n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(0n))), [], [], {==}, Unit{}),
    Equal.cong(I.Int, I.Int, v => I.Int.add(v, I.Int.neg(vh)), I.Int.add(vh, vl), sc, h4))
  +eP1 : {P == 1n+m1 : Nat} = W.Lt.pos(H, P, E2.Lt.dself(H, BP.Pow2.pos(p1)))
  +ePU : {Nat.add(Nat.mul(m1, U4), U4) == Nat.mul(P, U4) : Nat} = Equal.trans(Nat, Nat.add(Nat.mul(m1, U4), U4), Nat.add(U4, Nat.mul(m1, U4)), Nat.mul(P, U4), NL.Nat.add_comm(Nat.mul(m1, U4), U4),
    Equal.cong(Nat, Nat, v => Nat.mul(v, U4), 1n+m1, P, Equal.sym(Nat, P, 1n+m1, eP1)))
  +hscP : {RD.Nat.lt(Nat.mul(P, U4), RD.Int.mag(sc)) == False{} : Bool} = E.Le.trans(RD.Int.mag(sc), Nat.add(Nat.mul(m1, U4), U4), Nat.mul(P, U4), W.Tri2(sh, c, Nat.mul(m1, U4), U4, hsh2, hc), E.Le.eq(Nat.add(Nat.mul(m1, U4), U4), Nat.mul(P, U4), ePU))
  +hvl : {RD.Nat.lt(U4, Nat.double(RD.Int.mag(vl))) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(U4, Nat.double(RD.Int.mag(vl))), RD.Nat.lt(U4, Nat.double(RD.Int.mag(I.Int.add(sc, I.Int.neg(E.RNi(p, sc)))))), False{},
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(U4, Nat.double(RD.Int.mag(v))), vl, I.Int.add(sc, I.Int.neg(E.RNi(p, sc))), evl), EBy(p1, sc, U4, 2n+kU, eU4, hscP))
  +hvl2 : {RD.Nat.lt(U2, RD.Int.mag(vl)) == False{} : Bool} = W.Le.halve(RD.Int.mag(vl), U2, hvl)
  # |tl + vl| <= 2U + u²: |e2| <= u², |w| <= 4U
  +tv = I.Int.add(tl, vl)
  +htv : {RD.Nat.lt(Nat.add(Q, U2), RD.Int.mag(tv)) == False{} : Bool} = W.Tri2(tl, vl, Q, U2, htl2, hvl2)
  +htvP : {RD.Nat.lt(Nat.add(Nat.mul(P, Q2), Q), RD.Int.mag(tv)) == False{} : Bool} = E.Le.trans(RD.Int.mag(tv), Nat.add(Q, U2), Nat.add(Nat.mul(P, Q2), Q), htv,
    E.Le.eq(Nat.add(Q, U2), Nat.add(Nat.mul(P, Q2), Q), Equal.trans(Nat, Nat.add(Q, U2), Nat.add(U2, Q), Nat.add(Nat.mul(P, Q2), Q), NL.Nat.add_comm(Q, U2),
      Equal.cong(Nat, Nat, v => Nat.add(v, Q), U2, Nat.mul(P, Q2), Equal.sym(Nat, Nat.mul(P, Q2), U2, eUq2)))))
  +he2 : {RD.Nat.lt(Q2, Nat.double(RD.Int.mag(A.e2(1n+p1, xh, xl, yh, yl)))) == False{} : Bool} = E2q(p1, q, tv, htvP)
  +hQU : {RD.Nat.lt(U2, Q) == False{} : Bool} = E.Le.trans(Q, U, U2, E.Le.trans(Q, Nat.mul(1n, Q), U, E.Le.eq(Q, Nat.mul(1n, Q), Equal.sym(Nat, Nat.mul(1n, Q), Q, P3.Mul.one_l(Q))), E2.Le.mulr(1n, P, Q, E2.Le.one(1n+p1))), E2.Le.dbl(U))
  +htv4 : {RD.Nat.lt(U4, RD.Int.mag(tv)) == False{} : Bool} = E.Le.trans(RD.Int.mag(tv), Nat.add(Q, U2), U4, htv, E.Le.trans(Nat.add(Q, U2), Nat.add(U2, U2), U4, E2.Le.addr(Q, U2, U2, hQU), E.Le.eq(Nat.add(U2, U2), U4, Equal.sym(Nat, U4, Nat.add(U2, U2), Y.Nat.double_add(U2)))))
  +hw : {RD.Nat.lt(U4, RD.Int.mag(E.RNi(p, tv))) == False{} : Bool} = W.RB(p1, tv, U4, fU4, htv4)
  # line 6: |vh| >= 4U >= |w|
  +hsc : {RD.Nat.lt(RD.Int.mag(sc), U4) == False{} : Bool} = Mag.low(sh, c, U4, U4, E.Le.trans(Nat.add(U4, U4), U8, RD.Int.mag(sh), E.Le.eq(Nat.add(U4, U4), U8, Equal.sym(Nat, U8, Nat.add(U4, U4), Y.Nat.double_add(U4))), hsh8), hc)
  +hvh : {RD.Nat.lt(RD.Int.mag(vh), U4) == False{} : Bool} = W.RL(p1, sc, U4, fU4, hsc)
  +hle6 : {RD.Nat.lt(RD.Int.mag(vh), RD.Int.mag(E.RNi(p, tv))) == False{} : Bool} = E.Le.trans(RD.Int.mag(E.RNi(p, tv)), U4, RD.Int.mag(vh), hw, hvh)
  +h6 : {A.z(p, xh, xl, yh, yl) == I.Int.add(vh, E.RNi(p, tv)) : I.Int} = E.Fast2Sum(p1, vh, E.RNi(p, tv), W.Rf.i(p1, sc), W.Rf.i(p1, tv), hle6)
  # eta = e1 + e2: 2 |eta| <= 4u² + 2u²
  +ee : {A.eta(1n+p1, xh, xl, yh, yl) == I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl)) : I.Int} = A.split(p, xh, xl, yh, yl, h4, h6)
  +Q3 = Nat.mul(3n, Q)
  +envq : List<&2, Nat> = [Q, Q2, Q4, Q3, Nat.double(Q3)]
  +eq2 : {Q2 == Nat.add(Q, Q) : Nat} = Y.Nat.double_add(Q)
  +eq4 : {Q4 == Nat.add(Q2, Q2) : Nat} = Y.Nat.double_add(Q2)
  +eq6 : {Nat.double(Q3) == Nat.add(Q3, Q3) : Nat} = Y.Nat.double_add(Q3)
  +e6 : {Nat.add(Q4, Q2) == Nat.double(Q3) : Nat} = R.NatN.eq2(envq, R.Ad(R.V(2n), R.V(1n)), R.V(4n), [], [], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.V(1n), R.V(1n)))), R.Ad(R.Ad(R.V(3n), R.V(3n)), R.Ng(R.V(4n))), R.Ad(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{}))), R.Ng(R.V(3n))), R.Ad(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{}))), R.Ng(R.V(3n)))], {==}, Unit{}, (R.NatN.z(envq, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, eq2), (R.NatN.z(envq, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, eq2), (R.NatN.z(envq, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, eq2), (R.NatN.z(envq, R.V(2n), R.Ad(R.V(1n), R.V(1n)), {==}, {==}, eq4), (R.NatN.z(envq, R.Ad(R.V(3n), R.V(3n)), R.V(4n), {==}, {==}, Equal.sym(Nat, Nat.double(Q3), Nat.add(Q3, Q3), eq6)), (R.NatN.z(envq, R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{}))), R.V(3n), {==}, {==}, Equal.sym(Nat, Q3, Nat.mul(3n, Q), {==})), (R.NatN.z(envq, R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{}))), R.V(3n), {==}, {==}, Equal.sym(Nat, Q3, Nat.mul(3n, Q), {==})), Unit{}))))))), {==}, {==})
  W.Le.halve(RD.Int.mag(A.eta(1n+p1, xh, xl, yh, yl)), Q3, Equal.trans(Bool, RD.Nat.lt(Nat.double(Q3), Nat.double(RD.Int.mag(A.eta(1n+p1, xh, xl, yh, yl)))), RD.Nat.lt(Nat.double(Q3), Nat.double(RD.Int.mag(I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl))))), False{},
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(Nat.double(Q3), Nat.double(RD.Int.mag(v))), A.eta(1n+p1, xh, xl, yh, yl), I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl)), ee),
    E.Le.trans(Nat.double(RD.Int.mag(I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl)))), Nat.add(Q4, Q2), Nat.double(Q3), Dbl.tri(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl), Q4, Q2, he1, he2), E.Le.eq(Nat.add(Q4, Q2), Nat.double(Q3), e6))))


# The relative bound
# ------------------
# |eta| (1 - 4u) <= 3u² |x + y|, as |eta| 2^p (2^p - 4) <= 3 |x + y|

def RelA(+p1: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> Bool:
  RD.Nat.lt(Nat.mul(3n, RD.Int.mag(I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl)))), Nat.mul(RD.Int.mag(A.eta(1n+p1, xh, xl, yh, yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n))))

# 2^3p e <= (2^(p+1) + 1) M gives e 2^p (2^p - 4) <= 3M
def Fin.rel(+p1: Nat, +e: Nat, +M: Nat, +h: {RD.Nat.lt(Nat.add(Nat.add(Nat.mul(RD.Nat.pow2(1n+p1), M), Nat.mul(RD.Nat.pow2(1n+p1), M)), M), Nat.mul(Nat.mul(RD.Nat.pow2(1n+p1), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+p1))), e)) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(3n, M), Nat.mul(e, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)))) == False{} : Bool}:
  +P = RD.Nat.pow2(1n+p1)
  +m4 = RD.Nat.monus(P, 4n)
  +PP = Nat.mul(P, P)
  +PPP = Nat.mul(P, PP)
  +K = Nat.add(Nat.add(Nat.mul(P, M), Nat.mul(P, M)), M)
  +env : List<&2, Nat> = [e, P, m4, M]
  +e1 : {Nat.mul(Nat.mul(e, Nat.mul(P, m4)), PP) == Nat.mul(Nat.mul(PPP, e), m4) : Nat} = R.NatN.eq(env, R.Ml(R.Ml(R.V(0n), R.Ml(R.V(1n), R.V(2n))), R.Ml(R.V(1n), R.V(1n))), R.Ml(R.Ml(R.Ml(R.V(1n), R.Ml(R.V(1n), R.V(1n))), R.V(0n)), R.V(2n)), [], [], {==}, Unit{}, {==}, {==})
  +e2 : {Nat.mul(K, P) == Nat.add(Nat.add(Nat.mul(PP, M), Nat.mul(PP, M)), Nat.mul(P, M)) : Nat} = R.NatN.eq(env, R.Ml(R.Ad(R.Ad(R.Ml(R.V(1n), R.V(3n)), R.Ml(R.V(1n), R.V(3n))), R.V(3n)), R.V(1n)), R.Ad(R.Ad(R.Ml(R.Ml(R.V(1n), R.V(1n)), R.V(3n)), R.Ml(R.Ml(R.V(1n), R.V(1n)), R.V(3n))), R.Ml(R.V(1n), R.V(3n))), [], [], {==}, Unit{}, {==}, {==})
  +e3 : {Nat.mul(Nat.mul(3n, M), PP) == Nat.add(Nat.add(Nat.mul(PP, M), Nat.mul(PP, M)), Nat.mul(PP, M)) : Nat} = R.NatN.eq(env, R.Ml(R.Ad(R.V(3n), R.Ad(R.V(3n), R.Ad(R.V(3n), N.TZero{}))), R.Ml(R.V(1n), R.V(1n))), R.Ad(R.Ad(R.Ml(R.Ml(R.V(1n), R.V(1n)), R.V(3n)), R.Ml(R.Ml(R.V(1n), R.V(1n)), R.V(3n))), R.Ml(R.Ml(R.V(1n), R.V(1n)), R.V(3n))), [], [], {==}, Unit{}, {==}, {==})
  +hP1 : {RD.Nat.lt(P, 1n) == False{} : Bool} = E2.Le.one(1n+p1)
  +hPP : {RD.Nat.lt(PP, P) == False{} : Bool} = E.Le.trans(P, Nat.mul(P, 1n), PP, E.Le.eq(P, Nat.mul(P, 1n), Equal.sym(Nat, Nat.mul(P, 1n), P, NL.Nat.mul_one_r(P))), E2.Le.mull(P, 1n, P, hP1))
  +pos : {RD.Nat.lt(0n, PP) == True{} : Bool} = E.Lt.mono(0n, P, P, BP.Pow2.pos(1n+p1), BP.Pow2.pos(1n+p1))
  E.Le.cancel(Nat.mul(e, Nat.mul(P, m4)), Nat.mul(3n, M), PP, pos,
    E.Le.trans(Nat.mul(Nat.mul(e, Nat.mul(P, m4)), PP), Nat.mul(Nat.mul(PPP, e), m4), Nat.mul(Nat.mul(3n, M), PP), E.Le.eq(Nat.mul(Nat.mul(e, Nat.mul(P, m4)), PP), Nat.mul(Nat.mul(PPP, e), m4), e1),
      E.Le.trans(Nat.mul(Nat.mul(PPP, e), m4), Nat.mul(K, m4), Nat.mul(Nat.mul(3n, M), PP), E2.Le.mulr(Nat.mul(PPP, e), K, m4, h),
        E.Le.trans(Nat.mul(K, m4), Nat.mul(K, P), Nat.mul(Nat.mul(3n, M), PP), E2.Le.mull(K, m4, P, W.Mo.le(P, 4n)),
          E.Le.trans(Nat.mul(K, P), Nat.add(Nat.add(Nat.mul(PP, M), Nat.mul(PP, M)), Nat.mul(P, M)), Nat.mul(Nat.mul(3n, M), PP), E.Le.eq(Nat.mul(K, P), Nat.add(Nat.add(Nat.mul(PP, M), Nat.mul(PP, M)), Nat.mul(P, M)), e2),
            E.Le.trans(Nat.add(Nat.add(Nat.mul(PP, M), Nat.mul(PP, M)), Nat.mul(P, M)), Nat.add(Nat.add(Nat.mul(PP, M), Nat.mul(PP, M)), Nat.mul(PP, M)), Nat.mul(Nat.mul(3n, M), PP),
              E2.Le.addl(Nat.add(Nat.mul(PP, M), Nat.mul(PP, M)), Nat.mul(P, M), Nat.mul(PP, M), E2.Le.mulr(P, PP, M, hPP)),
              E.Le.eq(Nat.add(Nat.add(Nat.mul(PP, M), Nat.mul(PP, M)), Nat.mul(PP, M)), Nat.mul(Nat.mul(3n, M), PP), Equal.sym(Nat, Nat.mul(Nat.mul(3n, M), PP), Nat.add(Nat.add(Nat.mul(PP, M), Nat.mul(PP, M)), Nat.mul(PP, M)), e3))))))))

# eta = 0: the sum is exact
def Fin.zero(+p1: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +h: {A.eta(1n+p1, xh, xl, yh, yl) == I.IPos{0n} : I.Int})
  -> {RelA(p1, xh, xl, yh, yl) == False{} : Bool}:
  +M3 = Nat.mul(3n, RD.Int.mag(I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl))))
  Equal.trans(Bool, RelA(p1, xh, xl, yh, yl), RD.Nat.lt(M3, Nat.mul(RD.Int.mag(I.IPos{0n}), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)))), False{},
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(M3, Nat.mul(RD.Int.mag(v), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)))), A.eta(1n+p1, xh, xl, yh, yl), I.IPos{0n}, h), BP.Lt.z(M3))


# (a + b) x = a x + b x
def RDist(+a: Nat, +b: Nat, +x: Nat) -> {Nat.mul(Nat.add(a, b), x) == Nat.add(Nat.mul(a, x), Nat.mul(b, x)) : Nat}:
  +env : List<&2, Nat> = [a, b, x]
  R.NatN.eq(env, R.Ml(R.Ad(R.V(0n), R.V(1n)), R.V(2n)), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ml(R.V(1n), R.V(2n))), [], [], {==}, Unit{}, {==}, {==})

# |a + b| x <= |a| x + |b| x
def Tri.x(+a: I.Int, +b: I.Int, +x: Nat) -> {RD.Nat.lt(Nat.add(Nat.mul(RD.Int.mag(a), x), Nat.mul(RD.Int.mag(b), x)), Nat.mul(RD.Int.mag(I.Int.add(a, b)), x)) == False{} : Bool}:
  E.Le.trans(Nat.mul(RD.Int.mag(I.Int.add(a, b)), x), Nat.mul(Nat.add(RD.Int.mag(a), RD.Int.mag(b)), x), Nat.add(Nat.mul(RD.Int.mag(a), x), Nat.mul(RD.Int.mag(b), x)),
    E2.Le.mulr(RD.Int.mag(I.Int.add(a, b)), Nat.add(RD.Int.mag(a), RD.Int.mag(b)), x, E2.Mag.tri(a, b)), E.Le.eq(Nat.mul(Nat.add(RD.Int.mag(a), RD.Int.mag(b)), x), Nat.add(Nat.mul(RD.Int.mag(a), x), Nat.mul(RD.Int.mag(b), x)), RDist(RD.Int.mag(a), RD.Int.mag(b), x)))

# P |RN z - z| <= |z|, with the error written z - RN z
def RelI.y(+p1: Nat, +z: I.Int) -> {RD.Nat.lt(RD.Int.mag(z), Nat.mul(RD.Int.mag(I.Int.add(z, I.Int.neg(E.RNi(1n+p1, z)))), RD.Nat.pow2(1n+p1))) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(RD.Int.mag(z), Nat.mul(RD.Int.mag(I.Int.add(z, I.Int.neg(E.RNi(1n+p1, z)))), RD.Nat.pow2(1n+p1))), RD.Nat.lt(RD.Int.mag(z), Nat.mul(RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))), RD.Nat.pow2(1n+p1))), False{},
    Equal.cong(Nat, Bool, v => RD.Nat.lt(RD.Int.mag(z), Nat.mul(v, RD.Nat.pow2(1n+p1))), RD.Int.mag(I.Int.add(z, I.Int.neg(E.RNi(1n+p1, z)))), RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))), Mag.flip(z, E.RNi(1n+p1, z))),
    RelI(p1, z))

# Case 1 of Theorem 3.1 (-xh < yh <= -xh/2): s = xh + yh = S is exact, a
# multiple of G = ulp(yh) (u or 2u), so sl = 0, c = th and e1 = 0.
# Case 1b, |s + L| > |L| (L = xl + yl): then 4 |s + th| >= G, Fast2Sum is
# exact at line 6, and relative errors give 2^3p |eta| <= (2^(p+1) + 1) |x + y|.
def C1b(+p1: Nat, +gq: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +S: Nat, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hsp: {I.Int.add(xh, yh) == I.IPos{S} : I.Int}, +hS1: {RD.Nat.lt(S, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq))) == False{} : Bool},
  +esh: {A.sh(1n+p1, xh, yh) == I.Int.add(xh, yh) : I.Int}, +ec: {A.c(1n+p1, xh, xl, yh, yl) == E.RNi(1n+p1, I.Int.add(xl, yl)) : I.Int}, +ee1: {A.e1(1n+p1, xh, xl, yh, yl) == I.IPos{0n} : I.Int},
  +h4: {I.Int.add(A.vh(1n+p1, xh, xl, yh, yl), A.vl(1n+p1, xh, xl, yh, yl)) == I.Int.add(A.sh(1n+p1, xh, yh), A.c(1n+p1, xh, xl, yh, yl)) : I.Int},
  +htl: {RD.Nat.lt(RD.Nat.pow2(gq), RD.Int.mag(A.tl(1n+p1, xl, yl))) == False{} : Bool},
  +hb: {RD.Nat.lt(RD.Int.mag(I.Int.add(xl, yl)), RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)))) == True{} : Bool})
  -> {RelA(p1, xh, xl, yh, yl) == False{} : Bool}:
  +p : Nat = 1n+p1
  +P = RD.Nat.pow2(1n+p1)
  +Gq = RD.Nat.pow2(gq)
  +G = Nat.mul(P, Gq)
  +s = I.Int.add(xh, yh)
  +L = I.Int.add(xl, yl)
  +th = E.RNi(p, L)
  +tl = A.tl(p, xl, yl)
  +X = I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl))
  +M = RD.Int.mag(X)
  +mL = RD.Int.mag(L)
  +mtl = RD.Int.mag(tl)
  +h6P : {RD.Nat.lt(P, 6n) == False{} : Bool} = E.Le.trans(6n, 8n, P, {==}, E2.Pow2.mono(3n, 1n+p1, E.Le.trans(3n, 5n, 1n+p1, {==}, E.Le.trans(5n, p1, 1n+p1, hp, E.Le.add1(p1)))))
  +env4 : List<&2, I.Int> = [xh, xl, yh, yl]
  +eX : {X == I.Int.add(s, L) : I.Int} = BP.IntN(env4, R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(2n), R.V(3n))), R.Ad(R.Ad(R.V(0n), R.V(2n)), R.Ad(R.V(1n), R.V(3n))), [], [], {==}, Unit{})
  +eMs : {RD.Int.mag(I.Int.add(s, L)) == M : Nat} = Equal.cong(I.Int, Nat, v => RD.Int.mag(v), I.Int.add(s, L), X, Equal.sym(I.Int, X, I.Int.add(s, L), eX))
  +hM : {RD.Nat.lt(mL, M) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(mL, M), RD.Nat.lt(mL, RD.Int.mag(I.Int.add(s, L))), True{}, Equal.cong(Nat, Bool, v => RD.Nat.lt(mL, v), M, RD.Int.mag(I.Int.add(s, L)), Equal.sym(Nat, RD.Int.mag(I.Int.add(s, L)), M, eMs)), hb)
  +hLM : {RD.Nat.lt(M, mL) == False{} : Bool} = E2.Lt.to_le(mL, M, hM)
  # sh + c = s + th = X - tl
  +sc = I.Int.add(A.sh(p, xh, yh), A.c(p, xh, xl, yh, yl))
  +n = RD.Int.mag(sc)
  +est : {sc == I.Int.add(s, th) : I.Int} = Y.Int.cong2(A.sh(p, xh, yh), s, A.c(p, xh, xl, yh, yl), th, esh, ec)
  +env5 : List<&2, I.Int> = [xh, xl, yh, yl, th]
  +eXs : {X == I.Int.add(sc, tl) : I.Int} = Equal.trans(I.Int, X, I.Int.add(I.Int.add(s, th), tl), I.Int.add(sc, tl),
    BP.IntN(env5, R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(2n), R.V(3n))), R.Ad(R.Ad(R.Ad(R.V(0n), R.V(2n)), R.V(4n)), R.Ad(R.Ad(R.V(1n), R.V(3n)), R.Ng(R.V(4n)))), [], [], {==}, Unit{}),
    Equal.cong(I.Int, I.Int, v => I.Int.add(v, tl), I.Int.add(s, th), sc, Equal.sym(I.Int, sc, I.Int.add(s, th), est)))
  +envx : List<&2, I.Int> = [sc, tl]
  +esX : {sc == I.Int.add(X, I.Int.neg(tl)) : I.Int} = Equal.trans(I.Int, sc, I.Int.add(I.Int.add(sc, tl), I.Int.neg(tl)), I.Int.add(X, I.Int.neg(tl)),
    BP.IntN(envx, R.V(0n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(1n))), [], [], {==}, Unit{}),
    Equal.cong(I.Int, I.Int, v => I.Int.add(v, I.Int.neg(tl)), I.Int.add(sc, tl), X, Equal.sym(I.Int, X, I.Int.add(sc, tl), eXs)))
  +hMn : {RD.Nat.lt(Nat.add(n, mtl), M) == False{} : Bool} = E.Le.trans(M, RD.Int.mag(I.Int.add(sc, tl)), Nat.add(n, mtl), E.Le.eq(M, RD.Int.mag(I.Int.add(sc, tl)), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), X, I.Int.add(sc, tl), eXs)), E2.Mag.tri(sc, tl))
  +hnM : {RD.Nat.lt(Nat.add(M, mtl), n) == False{} : Bool} = E.Le.trans(n, RD.Int.mag(I.Int.add(X, I.Int.neg(tl))), Nat.add(M, mtl), E.Le.eq(n, RD.Int.mag(I.Int.add(X, I.Int.neg(tl))), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), sc, I.Int.add(X, I.Int.neg(tl)), esX)),
    E.Le.trans(RD.Int.mag(I.Int.add(X, I.Int.neg(tl))), Nat.add(M, RD.Int.mag(I.Int.neg(tl))), Nat.add(M, mtl), E2.Mag.tri(X, I.Int.neg(tl)), E.Le.eq(Nat.add(M, RD.Int.mag(I.Int.neg(tl))), Nat.add(M, mtl), Equal.cong(Nat, Nat, v => Nat.add(M, v), RD.Int.mag(I.Int.neg(tl)), mtl, E.Mag.neg(tl)))))
  # G <= S <= M + |L| < 2M <= 2 (n + Gq), and 4 Gq <= G: G <= 4n
  +eS : {RD.Int.mag(s) == S : Nat} = Equal.cong(I.Int, Nat, v => RD.Int.mag(v), s, I.IPos{S}, hsp)
  +hSM : {RD.Nat.lt(Nat.add(M, mL), S) == False{} : Bool} = E.Le.trans(S, RD.Int.mag(s), Nat.add(M, mL), E.Le.eq(S, RD.Int.mag(s), Equal.sym(Nat, RD.Int.mag(s), S, eS)),
    E.Le.trans(RD.Int.mag(s), Nat.add(RD.Int.mag(I.Int.add(s, L)), mL), Nat.add(M, mL), Mag.rev(s, L), E.Le.eq(Nat.add(RD.Int.mag(I.Int.add(s, L)), mL), Nat.add(M, mL), Equal.cong(Nat, Nat, v => Nat.add(v, mL), RD.Int.mag(I.Int.add(s, L)), M, eMs))))
  +hGM : {RD.Nat.lt(Nat.add(M, M), G) == False{} : Bool} = E.Le.trans(G, S, Nat.add(M, M), hS1, E.Le.trans(S, Nat.add(M, mL), Nat.add(M, M), hSM, E2.Le.addl(M, mL, M, hLM)))
  +nq = Nat.add(n, Gq)
  +hMq : {RD.Nat.lt(nq, M) == False{} : Bool} = E.Le.trans(M, Nat.add(n, mtl), nq, hMn, E2.Le.addl(n, mtl, Gq, htl))
  +hGn : {RD.Nat.lt(Nat.add(nq, nq), G) == False{} : Bool} = E.Le.trans(G, Nat.add(M, M), Nat.add(nq, nq), hGM, E2.Le.add2(M, nq, M, nq, hMq, hMq))
  +n4 = Nat.mul(4n, n)
  +envn : List<&2, Nat> = [n, Gq]
  +e44 : {Nat.add(Nat.add(nq, nq), Nat.add(nq, nq)) == Nat.add(n4, Nat.mul(4n, Gq)) : Nat} = R.NatN.eq(envn, R.Ad(R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(0n), R.V(1n))), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(0n), R.V(1n)))),
    R.Ad(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{})))), R.Ad(R.V(1n), R.Ad(R.V(1n), R.Ad(R.V(1n), R.Ad(R.V(1n), N.TZero{}))))), [], [], {==}, Unit{}, {==}, {==})
  +h4G : {RD.Nat.lt(G, Nat.mul(4n, Gq)) == False{} : Bool} = E2.Le.mulr(4n, P, Gq, E.Le.trans(4n, 6n, P, {==}, h6P))
  +hG4n : {RD.Nat.lt(n4, G) == False{} : Bool} = E2.Le.canl(G, G, n4, E.Le.trans(Nat.add(G, G), Nat.add(n4, G), Nat.add(G, n4),
    E.Le.trans(Nat.add(G, G), Nat.add(Nat.add(nq, nq), Nat.add(nq, nq)), Nat.add(n4, G), E2.Le.add2(G, Nat.add(nq, nq), G, Nat.add(nq, nq), hGn, hGn),
      E.Le.trans(Nat.add(Nat.add(nq, nq), Nat.add(nq, nq)), Nat.add(n4, Nat.mul(4n, Gq)), Nat.add(n4, G), E.Le.eq(Nat.add(Nat.add(nq, nq), Nat.add(nq, nq)), Nat.add(n4, Nat.mul(4n, Gq)), e44), E2.Le.addl(n4, Nat.mul(4n, Gq), G, h4G))),
    E.Le.eq(Nat.add(n4, G), Nat.add(G, n4), NL.Nat.add_comm(n4, G))))
  # line 6: P |tl + vl| <= G + n <= P |vh|
  +vh = A.vh(p, xh, xl, yh, yl)
  +vl = A.vl(p, xh, xl, yh, yl)
  +envv : List<&2, I.Int> = [vh, vl]
  +evl : {vl == I.Int.add(sc, I.Int.neg(E.RNi(p, sc))) : I.Int} = Equal.trans(I.Int, vl, I.Int.add(I.Int.add(vh, vl), I.Int.neg(vh)), I.Int.add(sc, I.Int.neg(E.RNi(p, sc))),
    BP.IntN(envv, R.V(1n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(0n))), [], [], {==}, Unit{}),
    Equal.cong(I.Int, I.Int, v => I.Int.add(v, I.Int.neg(vh)), I.Int.add(vh, vl), sc, h4))
  +mvl = RD.Int.mag(vl)
  +mvh = RD.Int.mag(vh)
  +hvlP : {RD.Nat.lt(n, Nat.mul(mvl, P)) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(n, Nat.mul(mvl, P)), RD.Nat.lt(n, Nat.mul(RD.Int.mag(I.Int.add(sc, I.Int.neg(E.RNi(p, sc)))), P)), False{},
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(n, Nat.mul(RD.Int.mag(v), P)), vl, I.Int.add(sc, I.Int.neg(E.RNi(p, sc))), evl), RelI.y(p1, sc))
  +hnv : {RD.Nat.lt(Nat.add(mvh, mvl), n) == False{} : Bool} = E.Le.trans(n, RD.Int.mag(I.Int.add(vh, vl)), Nat.add(mvh, mvl), E.Le.eq(n, RD.Int.mag(I.Int.add(vh, vl)), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), sc, I.Int.add(vh, vl), Equal.sym(I.Int, I.Int.add(vh, vl), sc, h4))), E2.Mag.tri(vh, vl))
  +tv = I.Int.add(tl, vl)
  +mtv = RD.Int.mag(tv)
  +htlP : {RD.Nat.lt(G, Nat.mul(mtl, P)) == False{} : Bool} = E.Le.trans(Nat.mul(mtl, P), Nat.mul(Gq, P), G, E2.Le.mulr(mtl, Gq, P, htl), E.Le.eq(Nat.mul(Gq, P), G, NL.Nat.mul_comm(Gq, P)))
  +htv : {RD.Nat.lt(Nat.add(G, n), Nat.mul(mtv, P)) == False{} : Bool} = E.Le.trans(Nat.mul(mtv, P), Nat.add(Nat.mul(mtl, P), Nat.mul(mvl, P)), Nat.add(G, n), Tri.x(tl, vl, P), E2.Le.add2(Nat.mul(mtl, P), G, Nat.mul(mvl, P), n, htlP, hvlP))
  +hnP : {RD.Nat.lt(Nat.add(Nat.mul(mvh, P), n), Nat.mul(n, P)) == False{} : Bool} = E.Le.trans(Nat.mul(n, P), Nat.add(Nat.mul(mvh, P), Nat.mul(mvl, P)), Nat.add(Nat.mul(mvh, P), n),
    E.Le.trans(Nat.mul(n, P), Nat.mul(Nat.add(mvh, mvl), P), Nat.add(Nat.mul(mvh, P), Nat.mul(mvl, P)), E2.Le.mulr(n, Nat.add(mvh, mvl), P, hnv), E.Le.eq(Nat.mul(Nat.add(mvh, mvl), P), Nat.add(Nat.mul(mvh, P), Nat.mul(mvl, P)), RDist(mvh, mvl, P))),
    E2.Le.addl(Nat.mul(mvh, P), Nat.mul(mvl, P), n, hvlP))
  +e6n : {Nat.add(Nat.add(n4, n), n) == Nat.mul(6n, n) : Nat} = R.NatN.eq(envn, R.Ad(R.Ad(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{})))), R.V(0n)), R.V(0n)),
    R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{})))))), [], [], {==}, Unit{}, {==}, {==})
  +h6n : {RD.Nat.lt(Nat.mul(n, P), Nat.add(Nat.add(G, n), n)) == False{} : Bool} = E.Le.trans(Nat.add(Nat.add(G, n), n), Nat.mul(6n, n), Nat.mul(n, P),
    E.Le.trans(Nat.add(Nat.add(G, n), n), Nat.add(Nat.add(n4, n), n), Nat.mul(6n, n), E2.Le.addr(Nat.add(G, n), Nat.add(n4, n), n, E2.Le.addr(G, n4, n, hG4n)), E.Le.eq(Nat.add(Nat.add(n4, n), n), Nat.mul(6n, n), e6n)),
    E.Le.trans(Nat.mul(6n, n), Nat.mul(P, n), Nat.mul(n, P), E2.Le.mulr(6n, P, n, h6P), E.Le.eq(Nat.mul(P, n), Nat.mul(n, P), NL.Nat.mul_comm(P, n))))
  +hGv : {RD.Nat.lt(Nat.mul(mvh, P), Nat.add(G, n)) == False{} : Bool} = E2.Le.canl(n, Nat.add(G, n), Nat.mul(mvh, P),
    E.Le.trans(Nat.add(n, Nat.add(G, n)), Nat.add(Nat.add(G, n), n), Nat.add(n, Nat.mul(mvh, P)), E.Le.eq(Nat.add(n, Nat.add(G, n)), Nat.add(Nat.add(G, n), n), NL.Nat.add_comm(n, Nat.add(G, n))),
      E.Le.trans(Nat.add(Nat.add(G, n), n), Nat.mul(n, P), Nat.add(n, Nat.mul(mvh, P)), h6n, E.Le.trans(Nat.mul(n, P), Nat.add(Nat.mul(mvh, P), n), Nat.add(n, Nat.mul(mvh, P)), hnP, E.Le.eq(Nat.add(Nat.mul(mvh, P), n), Nat.add(n, Nat.mul(mvh, P)), NL.Nat.add_comm(Nat.mul(mvh, P), n))))))
  +htvh : {RD.Nat.lt(mvh, mtv) == False{} : Bool} = E.Le.cancel(mtv, mvh, P, BP.Pow2.pos(1n+p1), E.Le.trans(Nat.mul(mtv, P), Nat.add(G, n), Nat.mul(mvh, P), htv, hGv))
  +hle6 : {RD.Nat.lt(mvh, RD.Int.mag(E.RNi(p, tv))) == False{} : Bool} = W.RB(p1, tv, mvh, W.Rf.i(p1, sc), htvh)
  +h6 : {A.z(p, xh, xl, yh, yl) == I.Int.add(vh, E.RNi(p, tv)) : I.Int} = E.Fast2Sum(p1, vh, E.RNi(p, tv), W.Rf.i(p1, sc), W.Rf.i(p1, tv), hle6)
  # eta = e2, and P^3 |e2| <= (2P + 1) M
  +e2v = A.e2(1n+p1, xh, xl, yh, yl)
  +envz : List<&2, I.Int> = [e2v]
  +eeta : {A.eta(1n+p1, xh, xl, yh, yl) == e2v : I.Int} = Equal.trans(I.Int, A.eta(1n+p1, xh, xl, yh, yl), I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), e2v), e2v, A.split(p, xh, xl, yh, yl, h4, h6),
    Equal.trans(I.Int, I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), e2v), I.Int.add(I.IPos{0n}, e2v), e2v, Equal.cong(I.Int, I.Int, v => I.Int.add(v, e2v), A.e1(1n+p1, xh, xl, yh, yl), I.IPos{0n}, ee1), BP.IntN(envz, R.Ad(N.TZero{}, R.V(0n)), R.V(0n), [], [], {==}, Unit{})))
  +me = RD.Int.mag(e2v)
  +he2 : {RD.Nat.lt(mtv, Nat.mul(me, P)) == False{} : Bool} = RelI(p1, tv)
  +htlL : {RD.Nat.lt(mL, Nat.mul(mtl, P)) == False{} : Bool} = RelI.y(p1, L)
  +c1 : {RD.Nat.lt(Nat.add(mL, n), Nat.mul(Nat.mul(me, P), P)) == False{} : Bool} = E.Le.trans(Nat.mul(Nat.mul(me, P), P), Nat.mul(mtv, P), Nat.add(mL, n), E2.Le.mulr(Nat.mul(me, P), mtv, P, he2),
    E.Le.trans(Nat.mul(mtv, P), Nat.add(Nat.mul(mtl, P), Nat.mul(mvl, P)), Nat.add(mL, n), Tri.x(tl, vl, P), E2.Le.add2(Nat.mul(mtl, P), mL, Nat.mul(mvl, P), n, htlL, hvlP)))
  +c2 : {RD.Nat.lt(Nat.add(Nat.mul(M, P), mL), Nat.mul(n, P)) == False{} : Bool} = E.Le.trans(Nat.mul(n, P), Nat.mul(Nat.add(M, mtl), P), Nat.add(Nat.mul(M, P), mL), E2.Le.mulr(n, Nat.add(M, mtl), P, hnM),
    E.Le.trans(Nat.mul(Nat.add(M, mtl), P), Nat.add(Nat.mul(M, P), Nat.mul(mtl, P)), Nat.add(Nat.mul(M, P), mL), E.Le.eq(Nat.mul(Nat.add(M, mtl), P), Nat.add(Nat.mul(M, P), Nat.mul(mtl, P)), RDist(M, mtl, P)), E2.Le.addl(Nat.mul(M, P), Nat.mul(mtl, P), mL, htlL)))
  +K = Nat.add(Nat.add(Nat.mul(P, M), Nat.mul(P, M)), M)
  +c3 : {RD.Nat.lt(K, Nat.mul(Nat.mul(Nat.mul(me, P), P), P)) == False{} : Bool} = E.Le.trans(Nat.mul(Nat.mul(Nat.mul(me, P), P), P), Nat.mul(Nat.add(mL, n), P), K, E2.Le.mulr(Nat.mul(Nat.mul(me, P), P), Nat.add(mL, n), P, c1),
    E.Le.trans(Nat.mul(Nat.add(mL, n), P), Nat.add(Nat.mul(mL, P), Nat.mul(n, P)), K, E.Le.eq(Nat.mul(Nat.add(mL, n), P), Nat.add(Nat.mul(mL, P), Nat.mul(n, P)), RDist(mL, n, P)),
      E.Le.trans(Nat.add(Nat.mul(mL, P), Nat.mul(n, P)), Nat.add(Nat.mul(M, P), Nat.add(Nat.mul(M, P), M)), K, E2.Le.add2(Nat.mul(mL, P), Nat.mul(M, P), Nat.mul(n, P), Nat.add(Nat.mul(M, P), M), E2.Le.mulr(mL, M, P, hLM),
          E.Le.trans(Nat.mul(n, P), Nat.add(Nat.mul(M, P), mL), Nat.add(Nat.mul(M, P), M), c2, E2.Le.addl(Nat.mul(M, P), mL, M, hLM))),
        E.Le.eq(Nat.add(Nat.mul(M, P), Nat.add(Nat.mul(M, P), M)), K, R.NatN.eq([M, P], R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.V(0n))), R.Ad(R.Ad(R.Ml(R.V(1n), R.V(0n)), R.Ml(R.V(1n), R.V(0n))), R.V(0n)), [], [], {==}, Unit{}, {==}, {==})))))
  +c4 : {RD.Nat.lt(K, Nat.mul(Nat.mul(P, Nat.mul(P, P)), me)) == False{} : Bool} = E.Le.trans(Nat.mul(Nat.mul(P, Nat.mul(P, P)), me), Nat.mul(Nat.mul(Nat.mul(me, P), P), P), K,
    E.Le.eq(Nat.mul(Nat.mul(P, Nat.mul(P, P)), me), Nat.mul(Nat.mul(Nat.mul(me, P), P), P), R.NatN.eq([me, P], R.Ml(R.Ml(R.V(1n), R.Ml(R.V(1n), R.V(1n))), R.V(0n)), R.Ml(R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(1n)), R.V(1n)), [], [], {==}, Unit{}, {==}, {==})), c3)
  Equal.trans(Bool, RelA(p1, xh, xl, yh, yl), RD.Nat.lt(Nat.mul(3n, M), Nat.mul(me, Nat.mul(P, RD.Nat.monus(P, 4n)))), False{},
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(Nat.mul(3n, M), Nat.mul(RD.Int.mag(v), Nat.mul(P, RD.Nat.monus(P, 4n)))), A.eta(1n+p1, xh, xl, yh, yl), e2v, eeta),
    Fin.rel(p1, me, M, c4))


# |z| = 0 gives z = 0
def Mag.z0(+z: I.Int, +h: {RD.Int.mag(z) == 0n : Nat}) -> {z == I.IPos{0n} : I.Int}:
  match z:
    case I.IPos{+n}:
      Equal.cong(Nat, I.Int, v => I.IPos{v}, n, 0n, h)
    case I.INeg{+n}:
      B.Bool.tf({I.INeg{n} == I.IPos{0n} : I.Int}, Equal.cong(Nat, Bool, v => RD.Nat.lt(0n, v), 1n+n, 0n, h))

# TwoSum's t is the exact error of RN(a + b), and representable
def TS.s.eq.go(+p: Nat, +a: I.Int, +b: I.Int, l: Bool) -> {Bool.pick(I.Int, l, E.F2.s(p, b, a), E.F2.s(p, a, b)) == E.RNi(p, I.Int.add(a, b)) : I.Int}:
  match l:
    case True{}:
      Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(b, a), I.Int.add(a, b), Z.Int.add_comm(b, a))
    case False{}:
      {==}

def TS.rep.go(+p1: Nat, +a: I.Int, +b: I.Int, l: Bool)
  -> {E.Rn(1n+p1, RD.Int.mag(Bool.pick(I.Int, l, E.F2.t(1n+p1, b, a), E.F2.t(1n+p1, a, b)))) == RD.Int.mag(Bool.pick(I.Int, l, E.F2.t(1n+p1, b, a), E.F2.t(1n+p1, a, b))) : Nat}:
  match l:
    case True{}:
      W.Rf.i(p1, I.Int.add(a, I.Int.neg(E.F2.z(1n+p1, b, a))))
    case False{}:
      W.Rf.i(p1, I.Int.add(b, I.Int.neg(E.F2.z(1n+p1, a, b))))

def TS.tl(+p1: Nat, +a: I.Int, +b: I.Int, +fa: {E.Rn(1n+p1, RD.Int.mag(a)) == RD.Int.mag(a) : Nat}, +fb: {E.Rn(1n+p1, RD.Int.mag(b)) == RD.Int.mag(b) : Nat})
  -> {A.tl(1n+p1, a, b) == E.TS.t(1n+p1, a, b) : I.Int}:
  +p : Nat = 1n+p1
  +ts = E.TS.s(p, a, b)
  +tt = E.TS.t(p, a, b)
  +env : List<&2, I.Int> = [ts, tt]
  Equal.sym(I.Int, tt, A.tl(p, a, b), Equal.trans(I.Int, tt, I.Int.add(I.Int.add(ts, tt), I.Int.neg(ts)), A.tl(p, a, b),
    BP.IntN(env, R.V(1n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(0n))), [], [], {==}, Unit{}),
    Y.Int.cong2(I.Int.add(ts, tt), I.Int.add(a, b), I.Int.neg(ts), I.Int.neg(E.RNi(p, I.Int.add(a, b))), E.TwoSum(p1, a, b, fa, fb),
      Equal.cong(I.Int, I.Int, v => I.Int.neg(v), ts, E.RNi(p, I.Int.add(a, b)), TS.s.eq.go(p, a, b, RD.Nat.lt(RD.Int.mag(a), RD.Int.mag(b)))))))

def TS.tl.rep(+p1: Nat, +a: I.Int, +b: I.Int, +fa: {E.Rn(1n+p1, RD.Int.mag(a)) == RD.Int.mag(a) : Nat}, +fb: {E.Rn(1n+p1, RD.Int.mag(b)) == RD.Int.mag(b) : Nat})
  -> {E.Rn(1n+p1, RD.Int.mag(A.tl(1n+p1, a, b))) == RD.Int.mag(A.tl(1n+p1, a, b)) : Nat}:
  +e : {RD.Int.mag(A.tl(1n+p1, a, b)) == RD.Int.mag(E.TS.t(1n+p1, a, b)) : Nat} = Equal.cong(I.Int, Nat, v => RD.Int.mag(v), A.tl(1n+p1, a, b), E.TS.t(1n+p1, a, b), TS.tl(p1, a, b, fa, fb))
  E.Fn.eq(1n+p1, RD.Int.mag(A.tl(1n+p1, a, b)), RD.Int.mag(E.TS.t(1n+p1, a, b)), e, TS.rep.go(p1, a, b, RD.Nat.lt(RD.Int.mag(a), RD.Int.mag(b))))

# Sterbenz on distances: S/2 <= T <= 2S, both representable, |S - T| is
def Ster.d.go(+p1: Nat, +S: Nat, +T: Nat, +fS: {E.Rn(1n+p1, S) == S : Nat}, +fT: {E.Rn(1n+p1, T) == T : Nat},
  +h1: {RD.Nat.lt(Nat.double(T), S) == False{} : Bool}, +h2: {RD.Nat.lt(Nat.double(S), T) == False{} : Bool}, l: Bool, +el: {RD.Nat.lt(S, T) == l : Bool})
  -> {E.Rn(1n+p1, E.Dist(S, T)) == E.Dist(S, T) : Nat}:
  match l:
    case False{}:
      +d = RD.Nat.monus(S, T)
      +eS : {S == Nat.add(T, d) : Nat} = E.Le.wit(T, S, el)
      E.Fn.eq(1n+p1, E.Dist(S, T), d, Equal.trans(Nat, E.Dist(S, T), E.Dist(Nat.add(T, d), T), d, Equal.cong(Nat, Nat, v => E.Dist(v, T), S, Nat.add(T, d), eS), E.Dist.dn(T, d)),
        E.Sterbenz(p1, S, T, d, eS, h1, fS, fT))
    case True{}:
      +d = RD.Nat.monus(T, S)
      +eT : {T == Nat.add(S, d) : Nat} = E.Le.wit(S, T, E2.Lt.to_le(S, T, el))
      E.Fn.eq(1n+p1, E.Dist(S, T), d, Equal.trans(Nat, E.Dist(S, T), E.Dist(S, Nat.add(S, d)), d, Equal.cong(Nat, Nat, v => E.Dist(S, v), T, Nat.add(S, d), eT), E.Dist.up(S, d)),
        E.Sterbenz(p1, T, S, d, eT, h2, fT, fS))

def Ster.d(+p1: Nat, +S: Nat, +T: Nat, +fS: {E.Rn(1n+p1, S) == S : Nat}, +fT: {E.Rn(1n+p1, T) == T : Nat},
  +h1: {RD.Nat.lt(Nat.double(T), S) == False{} : Bool}, +h2: {RD.Nat.lt(Nat.double(S), T) == False{} : Bool})
  -> {E.Rn(1n+p1, E.Dist(S, T)) == E.Dist(S, T) : Nat}:
  Ster.d.go(p1, S, T, fS, fT, h1, h2, RD.Nat.lt(S, T), {==})

# half of a representable 2h is representable
def Fn.half(+p1: Nat, +h: Nat, +f: {E.Rn(1n+p1, Nat.double(h)) == Nat.double(h) : Nat}) -> {E.Rn(1n+p1, h) == h : Nat}:
  +r = E.Rn(1n+p1, h)
  +e2 : {Nat.double(r) == Nat.double(h) : Nat} = Equal.trans(Nat, Nat.double(r), Nat.mul(r, RD.Nat.pow2(1n)), Nat.double(h), Equal.sym(Nat, Nat.mul(r, RD.Nat.pow2(1n)), Nat.double(r), W.M2(r)),
    Equal.trans(Nat, Nat.mul(r, RD.Nat.pow2(1n)), E.Rn(1n+p1, Nat.mul(h, RD.Nat.pow2(1n))), Nat.double(h), Equal.sym(Nat, E.Rn(1n+p1, Nat.mul(h, RD.Nat.pow2(1n))), Nat.mul(r, RD.Nat.pow2(1n)), W.Rn.sc(1n+p1, h, 1n)),
      Equal.trans(Nat, E.Rn(1n+p1, Nat.mul(h, RD.Nat.pow2(1n))), E.Rn(1n+p1, Nat.double(h)), Nat.double(h), Equal.cong(Nat, Nat, v => E.Rn(1n+p1, v), Nat.mul(h, RD.Nat.pow2(1n)), Nat.double(h), W.M2(h)), f)))
  Equal.trans(Nat, r, D.Nat.half(Nat.double(r)), h, Equal.sym(Nat, D.Nat.half(Nat.double(r)), r, Y.Nat.half_double(r)),
    Equal.trans(Nat, D.Nat.half(Nat.double(r)), D.Nat.half(Nat.double(h)), h, Equal.cong(Nat, Nat, v => D.Nat.half(v), Nat.double(r), Nat.double(h), e2), Y.Nat.half_double(h)))


def Lt1.z(+k: Nat, +h: {RD.Nat.lt(k, 1n) == True{} : Bool}) -> {k == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      B.Bool.tf({1n+j == 0n : Nat}, Equal.trans(Bool, True{}, RD.Nat.lt(1n+j, 1n), False{}, Equal.sym(Bool, RD.Nat.lt(1n+j, 1n), True{}, h), BP.Lt.z(j)))

# Fast2Sum(a, b) with |a| a multiple of g and |b| <= g: |a| >= |b|, or a = 0
def F2.grid.go(+p1: Nat, +a: I.Int, +b: I.Int, +g: Nat, +k: Nat, +fa: {E.Rn(1n+p1, RD.Int.mag(a)) == RD.Int.mag(a) : Nat}, +fb: {E.Rn(1n+p1, RD.Int.mag(b)) == RD.Int.mag(b) : Nat},
  +ma: {RD.Int.mag(a) == Nat.mul(k, g) : Nat}, +hb: {RD.Nat.lt(g, RD.Int.mag(b)) == False{} : Bool}, l: Bool, +el: {RD.Nat.lt(RD.Int.mag(a), RD.Int.mag(b)) == l : Bool})
  -> {I.Int.add(E.F2.s(1n+p1, a, b), E.F2.t(1n+p1, a, b)) == I.Int.add(a, b) : I.Int}:
  match l:
    case False{}:
      E.Fast2Sum(p1, a, b, fa, fb, el)
    case True{}:
      +p : Nat = 1n+p1
      +hk : {RD.Nat.lt(Nat.mul(k, g), Nat.mul(1n, g)) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Nat.mul(k, g), Nat.mul(1n, g)), RD.Nat.lt(RD.Int.mag(a), Nat.mul(1n, g)), True{},
        Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.mul(1n, g)), Nat.mul(k, g), RD.Int.mag(a), Equal.sym(Nat, RD.Int.mag(a), Nat.mul(k, g), ma)),
        Equal.trans(Bool, RD.Nat.lt(RD.Int.mag(a), Nat.mul(1n, g)), RD.Nat.lt(RD.Int.mag(a), g), True{}, Equal.cong(Nat, Bool, v => RD.Nat.lt(RD.Int.mag(a), v), Nat.mul(1n, g), g, P3.Mul.one_l(g)),
          E2.Lt.le_trans(RD.Int.mag(a), RD.Int.mag(b), g, el, hb)))
      +k0 : {k == 0n : Nat} = Lt1.z(k, E.Lt.cancel(k, 1n, g, hk))
      +a0 : {a == I.IPos{0n} : I.Int} = Mag.z0(a, Equal.trans(Nat, RD.Int.mag(a), Nat.mul(k, g), 0n, ma, Equal.cong(Nat, Nat, v => Nat.mul(v, g), k, 0n, k0)))
      Equal.trans(I.Int, I.Int.add(E.F2.s(p, a, b), E.F2.t(p, a, b)), I.Int.add(E.F2.s(p, I.IPos{0n}, b), E.F2.t(p, I.IPos{0n}, b)), I.Int.add(a, b),
        Equal.cong(I.Int, I.Int, v => I.Int.add(E.F2.s(p, v, b), E.F2.t(p, v, b)), a, I.IPos{0n}, a0),
        Equal.trans(I.Int, I.Int.add(E.F2.s(p, I.IPos{0n}, b), E.F2.t(p, I.IPos{0n}, b)), I.Int.add(I.IPos{0n}, b), I.Int.add(a, b), F2.zero(p1, b, fb),
          Equal.cong(I.Int, I.Int, v => I.Int.add(v, b), I.IPos{0n}, a, Equal.sym(I.Int, a, I.IPos{0n}, a0))))

def F2.grid(+p1: Nat, +a: I.Int, +b: I.Int, +g: Nat, +k: Nat, +fa: {E.Rn(1n+p1, RD.Int.mag(a)) == RD.Int.mag(a) : Nat}, +fb: {E.Rn(1n+p1, RD.Int.mag(b)) == RD.Int.mag(b) : Nat},
  +ma: {RD.Int.mag(a) == Nat.mul(k, g) : Nat}, +hb: {RD.Nat.lt(g, RD.Int.mag(b)) == False{} : Bool})
  -> {I.Int.add(E.F2.s(1n+p1, a, b), E.F2.t(1n+p1, a, b)) == I.Int.add(a, b) : I.Int}:
  F2.grid.go(p1, a, b, g, k, fa, fb, ma, hb, RD.Nat.lt(RD.Int.mag(a), RD.Int.mag(b)), {==})

# Case 1a, |s + L| <= |L|: L < 0 and S/2 <= |th| <= 2S, so s + th is exact
# (Sterbenz), vl = 0, w = tl, and the sum is exact
def C1a.neg(+p1: Nat, +gq: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +S: Nat, +ms: Nat, +ln: Nat,
  +hsp: {I.Int.add(xh, yh) == I.IPos{S} : I.Int}, +hSm: {S == Nat.mul(ms, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq))) : Nat}, +hS1: {RD.Nat.lt(S, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq))) == False{} : Bool}, +fS: {E.Rn(1n+p1, S) == S : Nat},
  +esh: {A.sh(1n+p1, xh, yh) == I.Int.add(xh, yh) : I.Int}, +ec: {A.c(1n+p1, xh, xl, yh, yl) == E.RNi(1n+p1, I.Int.add(xl, yl)) : I.Int}, +ee1: {A.e1(1n+p1, xh, xl, yh, yl) == I.IPos{0n} : I.Int},
  +h4: {I.Int.add(A.vh(1n+p1, xh, xl, yh, yl), A.vl(1n+p1, xh, xl, yh, yl)) == I.Int.add(A.sh(1n+p1, xh, yh), A.c(1n+p1, xh, xl, yh, yl)) : I.Int},
  +htl: {RD.Nat.lt(RD.Nat.pow2(gq), RD.Int.mag(A.tl(1n+p1, xl, yl))) == False{} : Bool}, +ftl: {E.Rn(1n+p1, RD.Int.mag(A.tl(1n+p1, xl, yl))) == RD.Int.mag(A.tl(1n+p1, xl, yl)) : Nat},
  +hL2: {RD.Nat.lt(Nat.double(S), RD.Int.mag(I.Int.add(xl, yl))) == False{} : Bool}, +ha: {RD.Nat.lt(RD.Int.mag(I.Int.add(xl, yl)), RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)))) == False{} : Bool},
  +el: {I.Int.add(xl, yl) == I.INeg{ln} : I.Int})
  -> {RelA(p1, xh, xl, yh, yl) == False{} : Bool}:
  +p : Nat = 1n+p1
  +P = RD.Nat.pow2(1n+p1)
  +H = RD.Nat.pow2(p1)
  +Gq = RD.Nat.pow2(gq)
  +G = Nat.mul(P, Gq)
  +s = I.Int.add(xh, yh)
  +L = I.Int.add(xl, yl)
  +T0 : Nat = 1n+ln
  +T = E.Rn(p, T0)
  +th = E.RNi(p, L)
  +tl = A.tl(p, xl, yl)
  +eT0 : {RD.Int.mag(L) == T0 : Nat} = Equal.cong(I.Int, Nat, v => RD.Int.mag(v), L, I.INeg{ln}, el)
  +eth : {th == I.Int.neg(I.IPos{T}) : I.Int} = Equal.cong(I.Int, I.Int, v => E.RNi(p, v), L, I.INeg{ln}, el)
  +eS : {RD.Int.mag(s) == S : Nat} = Equal.cong(I.Int, Nat, v => RD.Int.mag(v), s, I.IPos{S}, hsp)
  # S <= 2 T0 and T0 <= 2S
  +hST0 : {RD.Nat.lt(Nat.add(T0, T0), S) == False{} : Bool} = E.Le.trans(S, Nat.add(RD.Int.mag(I.Int.add(s, L)), RD.Int.mag(L)), Nat.add(T0, T0),
    E.Le.trans(S, RD.Int.mag(s), Nat.add(RD.Int.mag(I.Int.add(s, L)), RD.Int.mag(L)), E.Le.eq(S, RD.Int.mag(s), Equal.sym(Nat, RD.Int.mag(s), S, eS)), Mag.rev(s, L)),
    E.Le.trans(Nat.add(RD.Int.mag(I.Int.add(s, L)), RD.Int.mag(L)), Nat.add(RD.Int.mag(L), RD.Int.mag(L)), Nat.add(T0, T0), E2.Le.addr(RD.Int.mag(I.Int.add(s, L)), RD.Int.mag(L), RD.Int.mag(L), ha),
      E.Le.eq(Nat.add(RD.Int.mag(L), RD.Int.mag(L)), Nat.add(T0, T0), Equal.cong(Nat, Nat, v => Nat.add(v, v), RD.Int.mag(L), T0, eT0))))
  +hST0d : {RD.Nat.lt(Nat.double(T0), S) == False{} : Bool} = E.Le.trans(S, Nat.add(T0, T0), Nat.double(T0), hST0, E.Le.eq(Nat.add(T0, T0), Nat.double(T0), Equal.sym(Nat, Nat.double(T0), Nat.add(T0, T0), Y.Nat.double_add(T0))))
  +hT0S : {RD.Nat.lt(Nat.double(S), T0) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Nat.double(S), T0), RD.Nat.lt(Nat.double(S), RD.Int.mag(L)), False{}, Equal.cong(Nat, Bool, v => RD.Nat.lt(Nat.double(S), v), T0, RD.Int.mag(L), Equal.sym(Nat, RD.Int.mag(L), T0, eT0)), hL2)
  # S = 2 Sh: Sh <= T0 gives Sh <= T, and T <= 2S
  +HG = Nat.mul(H, Gq)
  +Sh = Nat.mul(ms, HG)
  +eG : {G == Nat.double(HG) : Nat} = BP.Mul.dbl_l(H, Gq)
  +eSh : {S == Nat.double(Sh) : Nat} = Equal.trans(Nat, S, Nat.mul(ms, Nat.double(HG)), Nat.double(Sh), Equal.trans(Nat, S, Nat.mul(ms, G), Nat.mul(ms, Nat.double(HG)), hSm, Equal.cong(Nat, Nat, v => Nat.mul(ms, v), G, Nat.double(HG), eG)), R.Nat.mul_double(ms, HG))
  +fSh : {E.Rn(p, Sh) == Sh : Nat} = Fn.half(p1, Sh, Equal.trans(Nat, E.Rn(p, Nat.double(Sh)), E.Rn(p, S), Nat.double(Sh), Equal.cong(Nat, Nat, v => E.Rn(p, v), Nat.double(Sh), S, Equal.sym(Nat, S, Nat.double(Sh), eSh)),
    Equal.trans(Nat, E.Rn(p, S), S, Nat.double(Sh), fS, eSh)))
  +hShT0 : {RD.Nat.lt(T0, Sh) == False{} : Bool} = W.Le.halve(Sh, T0, E.Le.trans(Nat.double(Sh), S, Nat.double(T0), E.Le.eq(Nat.double(Sh), S, Equal.sym(Nat, S, Nat.double(Sh), eSh)), hST0d))
  +hShT : {RD.Nat.lt(T, Sh) == False{} : Bool} = E.Mono.lo(p1, T0, Sh, fSh, hShT0)
  +hTS : {RD.Nat.lt(Nat.double(S), T) == False{} : Bool} = E.Mono.hi(p1, T0, Nat.double(S), E.Fn.dbl(p1, S, fS), hT0S)
  +hST : {RD.Nat.lt(Nat.double(T), S) == False{} : Bool} = E.Le.trans(S, Nat.double(Sh), Nat.double(T), E.Le.eq(S, Nat.double(Sh), eSh), E.Le.dd(Sh, T, hShT))
  +fT : {E.Rn(p, T) == T : Nat} = W.Rn.idem(p1, I.INeg{ln})
  # vh = s + th exactly
  +dI = I.Int.add(I.IPos{S}, I.Int.neg(I.IPos{T}))
  +sc = I.Int.add(A.sh(p, xh, yh), A.c(p, xh, xl, yh, yl))
  +esc : {sc == dI : I.Int} = Equal.trans(I.Int, sc, I.Int.add(s, th), dI, Y.Int.cong2(A.sh(p, xh, yh), s, A.c(p, xh, xl, yh, yl), th, esh, ec),
    Y.Int.cong2(s, I.IPos{S}, th, I.Int.neg(I.IPos{T}), hsp, eth))
  +emd : {RD.Int.mag(dI) == E.Dist(S, T) : Nat} = E.Mag.diff(S, T)
  +fd : {E.Rn(p, RD.Int.mag(dI)) == RD.Int.mag(dI) : Nat} = E.Fn.eq(p, RD.Int.mag(dI), E.Dist(S, T), emd, Ster.d(p1, S, T, fS, fT, hST, hTS))
  +vh = A.vh(p, xh, xl, yh, yl)
  +vl = A.vl(p, xh, xl, yh, yl)
  +evh : {vh == dI : I.Int} = Equal.trans(I.Int, vh, E.RNi(p, dI), dI, Equal.cong(I.Int, I.Int, v => E.RNi(p, v), sc, dI, esc), E.RNi.exact(p, dI, fd))
  +envv : List<&2, I.Int> = [vh, vl, dI]
  +evl : {vl == I.IPos{0n} : I.Int} = Equal.trans(I.Int, vl, I.Int.add(I.Int.add(vh, vl), I.Int.neg(vh)), I.IPos{0n},
    BP.IntN(envv, R.V(1n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(0n))), [], [], {==}, Unit{}),
    Equal.trans(I.Int, I.Int.add(I.Int.add(vh, vl), I.Int.neg(vh)), I.Int.add(dI, I.Int.neg(dI)), I.IPos{0n},
      Y.Int.cong2(I.Int.add(vh, vl), dI, I.Int.neg(vh), I.Int.neg(dI), Equal.trans(I.Int, I.Int.add(vh, vl), sc, dI, h4, esc), Equal.cong(I.Int, I.Int, v => I.Int.neg(v), vh, dI, evh)),
      BP.IntN(envv, R.Ad(R.V(2n), R.Ng(R.V(2n))), N.TZero{}, [], [], {==}, Unit{})))
  # w = tl, e2 = 0
  +envt : List<&2, I.Int> = [tl]
  +etv : {I.Int.add(tl, vl) == tl : I.Int} = Equal.trans(I.Int, I.Int.add(tl, vl), I.Int.add(tl, I.IPos{0n}), tl, Equal.cong(I.Int, I.Int, v => I.Int.add(tl, v), vl, I.IPos{0n}, evl),
    BP.IntN(envt, R.Ad(R.V(0n), N.TZero{}), R.V(0n), [], [], {==}, Unit{}))
  +ew : {A.w(p, xh, xl, yh, yl) == tl : I.Int} = Equal.trans(I.Int, A.w(p, xh, xl, yh, yl), E.RNi(p, tl), tl, Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(tl, vl), tl, etv), E.RNi.exact(p, tl, ftl))
  +ee2 : {A.e2(1n+p1, xh, xl, yh, yl) == I.IPos{0n} : I.Int} = Equal.trans(I.Int, A.e2(1n+p1, xh, xl, yh, yl), I.Int.add(tl, I.Int.neg(tl)), I.IPos{0n},
    Y.Int.cong2(A.w(p, xh, xl, yh, yl), tl, I.Int.neg(I.Int.add(tl, vl)), I.Int.neg(tl), ew, Equal.cong(I.Int, I.Int, v => I.Int.neg(v), I.Int.add(tl, vl), tl, etv)),
    BP.IntN(envt, R.Ad(R.V(0n), R.Ng(R.V(0n))), N.TZero{}, [], [], {==}, Unit{}))
  # line 6: |vh| = |S - T| is a multiple of Gq (S = 2^p ms Gq, T >= 2^(p-1) Gq), and |w| <= Gq
  +hTq : {RD.Nat.lt(T, Nat.mul(H, Gq)) == False{} : Bool} = E.Le.trans(Nat.mul(H, Gq), Sh, T,
    W.Le.halve(HG, Sh, E.Le.trans(Nat.double(HG), S, Nat.double(Sh), E.Le.trans(Nat.double(HG), G, S, E.Le.eq(Nat.double(HG), G, Equal.sym(Nat, G, Nat.double(HG), eG)), hS1), E.Le.eq(S, Nat.double(Sh), eSh))),
    hShT)
  +mt = W.Mq(p1, T, gq)
  +eTq : {T == Nat.mul(mt, Gq) : Nat} = W.Rep.mult(p1, T, gq, fT, hTq)
  +eSq : {S == Nat.mul(Nat.mul(ms, P), Gq) : Nat} = Equal.trans(Nat, S, Nat.mul(ms, G), Nat.mul(Nat.mul(ms, P), Gq), hSm, Equal.sym(Nat, Nat.mul(Nat.mul(ms, P), Gq), Nat.mul(ms, G), NL.Nat.mul_assoc(ms, P, Gq)))
  +mvh : {RD.Int.mag(vh) == Nat.mul(E.Dist(Nat.mul(ms, P), mt), Gq) : Nat} = Equal.trans(Nat, RD.Int.mag(vh), E.Dist(S, T), Nat.mul(E.Dist(Nat.mul(ms, P), mt), Gq),
    Equal.trans(Nat, RD.Int.mag(vh), RD.Int.mag(dI), E.Dist(S, T), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), vh, dI, evh), emd),
    Equal.trans(Nat, E.Dist(S, T), E.Dist(Nat.mul(Nat.mul(ms, P), Gq), Nat.mul(mt, Gq)), Nat.mul(E.Dist(Nat.mul(ms, P), mt), Gq),
      Equal.trans(Nat, E.Dist(S, T), E.Dist(Nat.mul(Nat.mul(ms, P), Gq), T), E.Dist(Nat.mul(Nat.mul(ms, P), Gq), Nat.mul(mt, Gq)),
        Equal.cong(Nat, Nat, v => E.Dist(v, T), S, Nat.mul(Nat.mul(ms, P), Gq), eSq), Equal.cong(Nat, Nat, v => E.Dist(Nat.mul(Nat.mul(ms, P), Gq), v), T, Nat.mul(mt, Gq), eTq)),
      E.Dist.mul(Nat.mul(ms, P), mt, Gq)))
  +hw : {RD.Nat.lt(Gq, RD.Int.mag(A.w(p, xh, xl, yh, yl))) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Gq, RD.Int.mag(A.w(p, xh, xl, yh, yl))), RD.Nat.lt(Gq, RD.Int.mag(tl)), False{},
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(Gq, RD.Int.mag(v)), A.w(p, xh, xl, yh, yl), tl, ew), htl)
  +h6 : {A.z(p, xh, xl, yh, yl) == I.Int.add(vh, A.w(p, xh, xl, yh, yl)) : I.Int} = F2.grid(p1, vh, A.w(p, xh, xl, yh, yl), Gq, E.Dist(Nat.mul(ms, P), mt), W.Rf.i(p1, sc), W.Rf.i(p1, I.Int.add(tl, vl)), mvh, hw)
  +envz : List<&2, I.Int> = []
  Fin.zero(p1, xh, xl, yh, yl, Equal.trans(I.Int, A.eta(1n+p1, xh, xl, yh, yl), I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl)), I.IPos{0n}, A.split(p, xh, xl, yh, yl, h4, h6),
    Equal.trans(I.Int, I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl)), I.Int.add(I.IPos{0n}, I.IPos{0n}), I.IPos{0n}, Y.Int.cong2(A.e1(1n+p1, xh, xl, yh, yl), I.IPos{0n}, A.e2(1n+p1, xh, xl, yh, yl), I.IPos{0n}, ee1, ee2), {==})))


# positive L contradicts |s + L| <= |L|
def C1a.go(+p1: Nat, +gq: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +S: Nat, +ms: Nat,
  +hsp: {I.Int.add(xh, yh) == I.IPos{S} : I.Int}, +hSm: {S == Nat.mul(ms, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq))) : Nat}, +hS1: {RD.Nat.lt(S, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq))) == False{} : Bool}, +fS: {E.Rn(1n+p1, S) == S : Nat},
  +esh: {A.sh(1n+p1, xh, yh) == I.Int.add(xh, yh) : I.Int}, +ec: {A.c(1n+p1, xh, xl, yh, yl) == E.RNi(1n+p1, I.Int.add(xl, yl)) : I.Int}, +ee1: {A.e1(1n+p1, xh, xl, yh, yl) == I.IPos{0n} : I.Int},
  +h4: {I.Int.add(A.vh(1n+p1, xh, xl, yh, yl), A.vl(1n+p1, xh, xl, yh, yl)) == I.Int.add(A.sh(1n+p1, xh, yh), A.c(1n+p1, xh, xl, yh, yl)) : I.Int},
  +htl: {RD.Nat.lt(RD.Nat.pow2(gq), RD.Int.mag(A.tl(1n+p1, xl, yl))) == False{} : Bool}, +ftl: {E.Rn(1n+p1, RD.Int.mag(A.tl(1n+p1, xl, yl))) == RD.Int.mag(A.tl(1n+p1, xl, yl)) : Nat},
  +hL2: {RD.Nat.lt(Nat.double(S), RD.Int.mag(I.Int.add(xl, yl))) == False{} : Bool}, +ha: {RD.Nat.lt(RD.Int.mag(I.Int.add(xl, yl)), RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)))) == False{} : Bool},
  l: I.Int, +el: {I.Int.add(xl, yl) == l : I.Int})
  -> {RelA(p1, xh, xl, yh, yl) == False{} : Bool}:
  match l:
    case I.INeg{+ln}:
      C1a.neg(p1, gq, xh, xl, yh, yl, S, ms, ln, hsp, hSm, hS1, fS, esh, ec, ee1, h4, htl, ftl, hL2, ha, el)
    case I.IPos{+l0}:
      +G = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq))
      +pos : {RD.Nat.lt(0n, S) == True{} : Bool} = E2.Lt.le_trans(0n, G, S, E.Lt.mono(0n, RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq), BP.Pow2.pos(1n+p1), BP.Pow2.pos(gq)), hS1)
      +es : {I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)) == I.IPos{Nat.add(S, l0)} : I.Int} = Y.Int.cong2(I.Int.add(xh, yh), I.IPos{S}, I.Int.add(xl, yl), I.IPos{l0}, hsp, el)
      +h1 : {RD.Nat.lt(l0, Nat.add(S, l0)) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(l0, Nat.add(S, l0)), RD.Nat.lt(RD.Int.mag(I.Int.add(xl, yl)), RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)))), False{},
        Equal.sym(Bool, RD.Nat.lt(RD.Int.mag(I.Int.add(xl, yl)), RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)))), RD.Nat.lt(l0, Nat.add(S, l0)),
          Equal.trans(Bool, RD.Nat.lt(RD.Int.mag(I.Int.add(xl, yl)), RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)))), RD.Nat.lt(l0, RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)))), RD.Nat.lt(l0, Nat.add(S, l0)),
            Equal.cong(I.Int, Bool, v => RD.Nat.lt(RD.Int.mag(v), RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)))), I.Int.add(xl, yl), I.IPos{l0}, el),
            Equal.cong(I.Int, Bool, v => RD.Nat.lt(l0, RD.Int.mag(v)), I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)), I.IPos{Nat.add(S, l0)}, es))), ha)
      +h2 : {RD.Nat.lt(l0, Nat.add(S, l0)) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(l0, Nat.add(S, l0)), RD.Nat.lt(Nat.add(l0, 0n), Nat.add(l0, S)), True{},
        Equal.sym(Bool, RD.Nat.lt(Nat.add(l0, 0n), Nat.add(l0, S)), RD.Nat.lt(l0, Nat.add(S, l0)),
          Equal.trans(Bool, RD.Nat.lt(Nat.add(l0, 0n), Nat.add(l0, S)), RD.Nat.lt(l0, Nat.add(l0, S)), RD.Nat.lt(l0, Nat.add(S, l0)),
            Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.add(l0, S)), Nat.add(l0, 0n), l0, NL.Nat.add_zero_r(l0)),
            Equal.cong(Nat, Bool, v => RD.Nat.lt(l0, v), Nat.add(l0, S), Nat.add(S, l0), NL.Nat.add_comm(l0, S)))),
        Equal.trans(Bool, RD.Nat.lt(Nat.add(l0, 0n), Nat.add(l0, S)), RD.Nat.lt(0n, S), True{}, BP.Lt.shift(l0, 0n, S), pos))
      B.Bool.tf({RelA(p1, xh, xl, yh, yl) == False{} : Bool}, Equal.trans(Bool, True{}, RD.Nat.lt(l0, Nat.add(S, l0)), False{}, Equal.sym(Bool, RD.Nat.lt(l0, Nat.add(S, l0)), True{}, h2), h1))

def C1.split(+p1: Nat, +gq: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +S: Nat, +ms: Nat, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hsp: {I.Int.add(xh, yh) == I.IPos{S} : I.Int}, +hSm: {S == Nat.mul(ms, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq))) : Nat}, +hS1: {RD.Nat.lt(S, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq))) == False{} : Bool}, +fS: {E.Rn(1n+p1, S) == S : Nat},
  +esh: {A.sh(1n+p1, xh, yh) == I.Int.add(xh, yh) : I.Int}, +ec: {A.c(1n+p1, xh, xl, yh, yl) == E.RNi(1n+p1, I.Int.add(xl, yl)) : I.Int}, +ee1: {A.e1(1n+p1, xh, xl, yh, yl) == I.IPos{0n} : I.Int},
  +h4: {I.Int.add(A.vh(1n+p1, xh, xl, yh, yl), A.vl(1n+p1, xh, xl, yh, yl)) == I.Int.add(A.sh(1n+p1, xh, yh), A.c(1n+p1, xh, xl, yh, yl)) : I.Int},
  +htl: {RD.Nat.lt(RD.Nat.pow2(gq), RD.Int.mag(A.tl(1n+p1, xl, yl))) == False{} : Bool}, +ftl: {E.Rn(1n+p1, RD.Int.mag(A.tl(1n+p1, xl, yl))) == RD.Int.mag(A.tl(1n+p1, xl, yl)) : Nat},
  +hL2: {RD.Nat.lt(Nat.double(S), RD.Int.mag(I.Int.add(xl, yl))) == False{} : Bool},
  b: Bool, +eb: {RD.Nat.lt(RD.Int.mag(I.Int.add(xl, yl)), RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)))) == b : Bool})
  -> {RelA(p1, xh, xl, yh, yl) == False{} : Bool}:
  match b:
    case True{}:
      C1b(p1, gq, xh, xl, yh, yl, S, hp, hsp, hS1, esh, ec, ee1, h4, htl, eb)
    case False{}:
      C1a.go(p1, gq, xh, xl, yh, yl, S, ms, hsp, hSm, hS1, fS, esh, ec, ee1, h4, htl, ftl, hL2, eb, I.Int.add(xl, yl), {==})

# Case 1: s = xh + yh = S exact, S a multiple of G = 2^p Gq (G = ulp(yh)),
# |xl| <= G, 2 |yl| <= G
def C1(+p1: Nat, +gq: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +S: Nat, +ms: Nat, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hsp: {I.Int.add(xh, yh) == I.IPos{S} : I.Int}, +hSm: {S == Nat.mul(ms, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq))) : Nat}, +hS1: {RD.Nat.lt(S, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq))) == False{} : Bool}, +fS: {E.Rn(1n+p1, S) == S : Nat},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq)), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(gq)), Nat.double(RD.Int.mag(yl))) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat})
  -> {RelA(p1, xh, xl, yh, yl) == False{} : Bool}:
  +p : Nat = 1n+p1
  +P = RD.Nat.pow2(1n+p1)
  +H = RD.Nat.pow2(p1)
  +Gq = RD.Nat.pow2(gq)
  +G = Nat.mul(P, Gq)
  +HG = Nat.mul(H, Gq)
  +s = I.Int.add(xh, yh)
  +L = I.Int.add(xl, yl)
  +th = E.RNi(p, L)
  +eS : {RD.Int.mag(s) == S : Nat} = Equal.cong(I.Int, Nat, v => RD.Int.mag(v), s, I.IPos{S}, hsp)
  +esh : {A.sh(p, xh, yh) == s : I.Int} = E.RNi.exact(p, s, E.Fn.eq(p, RD.Int.mag(s), S, eS, fS))
  +env1 : List<&2, I.Int> = [s, th]
  +esl : {A.sl(p, xh, yh) == I.IPos{0n} : I.Int} = Equal.trans(I.Int, A.sl(p, xh, yh), I.Int.add(s, I.Int.neg(s)), I.IPos{0n},
    Equal.cong(I.Int, I.Int, v => I.Int.add(s, I.Int.neg(v)), A.sh(p, xh, yh), s, esh), BP.IntN(env1, R.Ad(R.V(0n), R.Ng(R.V(0n))), N.TZero{}, [], [], {==}, Unit{}))
  +e0t : {I.Int.add(A.sl(p, xh, yh), th) == th : I.Int} = Equal.trans(I.Int, I.Int.add(A.sl(p, xh, yh), th), I.Int.add(I.IPos{0n}, th), th,
    Equal.cong(I.Int, I.Int, v => I.Int.add(v, th), A.sl(p, xh, yh), I.IPos{0n}, esl), BP.IntN(env1, R.Ad(N.TZero{}, R.V(1n)), R.V(1n), [], [], {==}, Unit{}))
  +ec : {A.c(p, xh, xl, yh, yl) == th : I.Int} = Equal.trans(I.Int, A.c(p, xh, xl, yh, yl), E.RNi(p, th), th,
    Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(A.sl(p, xh, yh), th), th, e0t), E.RNi.exact(p, th, W.Rf.i(p1, L)))
  +ee1 : {A.e1(1n+p1, xh, xl, yh, yl) == I.IPos{0n} : I.Int} = Equal.trans(I.Int, A.e1(1n+p1, xh, xl, yh, yl), I.Int.add(th, I.Int.neg(th)), I.IPos{0n},
    Y.Int.cong2(A.c(p, xh, xl, yh, yl), th, I.Int.neg(I.Int.add(A.sl(p, xh, yh), th)), I.Int.neg(th), ec, Equal.cong(I.Int, I.Int, v => I.Int.neg(v), I.Int.add(A.sl(p, xh, yh), th), th, e0t)),
    BP.IntN(env1, R.Ad(R.V(1n), R.Ng(R.V(1n))), N.TZero{}, [], [], {==}, Unit{}))
  # |L| <= 3G/2: |th| <= 3G/2 < 2G, |tl| <= Gq
  +G2 = Nat.double(G)
  +G4 = Nat.double(G2)
  +env : List<&2, Nat> = [G, G2, G4]
  +e2 : {G2 == Nat.add(G, G) : Nat} = Y.Nat.double_add(G)
  +e4 : {G4 == Nat.add(G2, G2) : Nat} = Y.Nat.double_add(G2)
  +ea3 : {Nat.add(G2, G) == Nat.mul(3n, G) : Nat} = R.NatN.eq2(env, R.Ad(R.V(1n), R.V(0n)), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{}))), [], [], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n))))], {==}, Unit{}, (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, e2), Unit{}), {==}, {==})
  +hL3 : {RD.Nat.lt(Nat.mul(3n, G), Nat.double(RD.Int.mag(L))) == False{} : Bool} = E.Le.trans(Nat.double(RD.Int.mag(L)), Nat.add(G2, G), Nat.mul(3n, G), Dbl.tri(xl, yl, G2, G, E.Le.dd(RD.Int.mag(xl), G, hx), hy), E.Le.eq(Nat.add(G2, G), Nat.mul(3n, G), ea3))
  +cth = Nat.mul(3n, HG)
  +envh : List<&2, Nat> = [H, Gq, P]
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +ecth0 : {Nat.add(cth, cth) == Nat.mul(3n, G) : Nat} = R.NatN.eq(envh, R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(0n), R.V(1n)), N.TZero{}))), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(0n), R.V(1n)), N.TZero{})))), R.Ad(R.Ml(R.V(2n), R.V(1n)), R.Ad(R.Ml(R.V(2n), R.V(1n)), R.Ad(R.Ml(R.V(2n), R.V(1n)), N.TZero{}))), [R.Ad(R.Ad(R.Ng(R.V(1n)), R.Ng(R.V(1n))), R.Ng(R.V(1n)))], [R.Ad(R.V(2n), R.Ng(R.Ad(R.V(0n), R.V(0n))))], {==}, (R.NatN.z(envh, R.V(2n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, eP), Unit{}), {==}, {==})
  +ecth : {Nat.double(cth) == Nat.mul(3n, G) : Nat} = Equal.trans(Nat, Nat.double(cth), Nat.add(cth, cth), Nat.mul(3n, G), Y.Nat.double_add(cth), ecth0)
  +hLc : {RD.Nat.lt(cth, RD.Int.mag(L)) == False{} : Bool} = W.Le.halve(RD.Int.mag(L), cth, E.Le.trans(Nat.double(RD.Int.mag(L)), Nat.mul(3n, G), Nat.double(cth), hL3, E.Le.eq(Nat.mul(3n, G), Nat.double(cth), Equal.sym(Nat, Nat.double(cth), Nat.mul(3n, G), ecth))))
  +h4P : {RD.Nat.lt(P, 4n) == False{} : Bool} = E2.Pow2.mono(2n, 1n+p1, E.Le.trans(2n, 5n, 1n+p1, {==}, E.Le.trans(5n, p1, 1n+p1, hp, E.Le.add1(p1))))
  +fth : {E.Rn(p, cth) == cth : Nat} = W.Rn.fix(p1, cth, 3n, Nat.add(p1, gq), Equal.cong(Nat, Nat, v => Nat.mul(3n, v), HG, RD.Nat.pow2(Nat.add(p1, gq)), Equal.sym(Nat, RD.Nat.pow2(Nat.add(p1, gq)), HG, BP.Pow2.add(p1, gq))),
    E.Le.trans(3n, 4n, P, {==}, h4P))
  +hth : {RD.Nat.lt(cth, RD.Int.mag(th)) == False{} : Bool} = W.RB(p1, L, cth, fth, hLc)
  +posG : {RD.Nat.lt(0n, G) == True{} : Bool} = E.Lt.mono(0n, P, Gq, BP.Pow2.pos(1n+p1), BP.Pow2.pos(gq))
  +h34 : {RD.Nat.lt(Nat.mul(3n, G), Nat.mul(4n, G)) == True{} : Bool} = E.Lt.mono(3n, 4n, G, {==}, posG)
  +hc2 : {RD.Nat.lt(cth, G2) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(cth, G2), RD.Nat.lt(Nat.double(cth), Nat.double(G2)), True{}, Equal.sym(Bool, RD.Nat.lt(Nat.double(cth), Nat.double(G2)), RD.Nat.lt(cth, G2), E.Lt.dd(cth, G2)),
    Equal.trans(Bool, RD.Nat.lt(Nat.double(cth), Nat.double(G2)), RD.Nat.lt(Nat.mul(3n, G), Nat.mul(4n, G)), True{},
      Equal.trans(Bool, RD.Nat.lt(Nat.double(cth), Nat.double(G2)), RD.Nat.lt(Nat.mul(3n, G), Nat.double(G2)), RD.Nat.lt(Nat.mul(3n, G), Nat.mul(4n, G)),
        Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.double(G2)), Nat.double(cth), Nat.mul(3n, G), ecth),
        Equal.cong(Nat, Bool, v => RD.Nat.lt(Nat.mul(3n, G), v), Nat.double(G2), Nat.mul(4n, G), Equal.sym(Nat, Nat.mul(4n, G), Nat.double(G2), Mul4(G)))), h34))
  +hLG2 : {RD.Nat.lt(G2, RD.Int.mag(L)) == False{} : Bool} = E.Le.trans(RD.Int.mag(L), cth, G2, hLc, E2.Lt.to_le(cth, G2, hc2))
  +htl2 : {RD.Nat.lt(Nat.double(Gq), Nat.double(RD.Int.mag(A.tl(p, xl, yl)))) == False{} : Bool} = EBy(p1, L, Nat.double(Gq), 1n+gq, {==},
    E.Le.trans(RD.Int.mag(L), G2, Nat.mul(P, Nat.double(Gq)), hLG2, E.Le.eq(G2, Nat.mul(P, Nat.double(Gq)), Equal.sym(Nat, Nat.mul(P, Nat.double(Gq)), G2, R.Nat.mul_double(P, Gq)))))
  +htl : {RD.Nat.lt(Gq, RD.Int.mag(A.tl(p, xl, yl))) == False{} : Bool} = W.Le.halve(RD.Int.mag(A.tl(p, xl, yl)), Gq, htl2)
  +hL2 : {RD.Nat.lt(Nat.double(S), RD.Int.mag(L)) == False{} : Bool} = E.Le.trans(RD.Int.mag(L), G2, Nat.double(S), hLG2, E.Le.dd(G, S, hS1))
  # line 4: F2.bin with 2^(p-1) 2^(1+gq) = G <= S and |c| < 2G
  +eHG : {Nat.mul(H, RD.Nat.pow2(1n+gq)) == G : Nat} = Equal.trans(Nat, Nat.mul(H, Nat.double(Gq)), Nat.double(HG), G, R.Nat.mul_double(H, Gq), Equal.sym(Nat, G, Nat.double(HG), BP.Mul.dbl_l(H, Gq)))
  +ha : {RD.Nat.lt(RD.Int.mag(A.sh(p, xh, yh)), Nat.mul(H, RD.Nat.pow2(1n+gq))) == False{} : Bool} = E.Le.trans(Nat.mul(H, RD.Nat.pow2(1n+gq)), S, RD.Int.mag(A.sh(p, xh, yh)),
    E.Le.trans(Nat.mul(H, RD.Nat.pow2(1n+gq)), G, S, E.Le.eq(Nat.mul(H, RD.Nat.pow2(1n+gq)), G, eHG), hS1),
    E.Le.eq(S, RD.Int.mag(A.sh(p, xh, yh)), Equal.trans(Nat, S, RD.Int.mag(s), RD.Int.mag(A.sh(p, xh, yh)), Equal.sym(Nat, RD.Int.mag(s), S, eS), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), s, A.sh(p, xh, yh), Equal.sym(I.Int, A.sh(p, xh, yh), s, esh)))))
  +hb : {RD.Nat.lt(RD.Int.mag(A.c(p, xh, xl, yh, yl)), Nat.mul(P, RD.Nat.pow2(1n+gq))) == True{} : Bool} = E2.Le.lt_trans(RD.Int.mag(A.c(p, xh, xl, yh, yl)), cth, Nat.mul(P, RD.Nat.pow2(1n+gq)),
    E.Le.trans(RD.Int.mag(A.c(p, xh, xl, yh, yl)), RD.Int.mag(th), cth, E.Le.eq(RD.Int.mag(A.c(p, xh, xl, yh, yl)), RD.Int.mag(th), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), A.c(p, xh, xl, yh, yl), th, ec)), hth),
    Equal.trans(Bool, RD.Nat.lt(cth, Nat.mul(P, Nat.double(Gq))), RD.Nat.lt(cth, G2), True{}, Equal.cong(Nat, Bool, v => RD.Nat.lt(cth, v), Nat.mul(P, Nat.double(Gq)), G2, R.Nat.mul_double(P, Gq)), hc2))
  +h4 = F2.bin(p1, A.sh(p, xh, yh), A.c(p, xh, xl, yh, yl), 1n+gq, W.Rf.i(p1, s), W.Rf.i(p1, I.Int.add(A.sl(p, xh, yh), th)), ha, hb)
  C1.split(p1, gq, xh, xl, yh, yl, S, ms, hp, hsp, hSm, hS1, fS, esh, ec, ee1, h4, htl, TS.tl.rep(p1, xl, yl, fx, fy), hL2,
    RD.Nat.lt(RD.Int.mag(L), RD.Int.mag(I.Int.add(s, L))), {==})


# Case 0: xh + yh = 0. sh = sl = 0, c = th, vh = th, vl = 0, w = tl, exact.
def C0(+p1: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +hs0: {I.Int.add(xh, yh) == I.IPos{0n} : I.Int},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat})
  -> {RelA(p1, xh, xl, yh, yl) == False{} : Bool}:
  +p : Nat = 1n+p1
  +s = I.Int.add(xh, yh)
  +L = I.Int.add(xl, yl)
  +th = E.RNi(p, L)
  +tl = A.tl(p, xl, yl)
  +z0 : I.Int = I.IPos{0n}
  +env : List<&2, I.Int> = [th, tl]
  +esh : {A.sh(p, xh, yh) == z0 : I.Int} = Equal.trans(I.Int, A.sh(p, xh, yh), E.RNi(p, z0), z0, Equal.cong(I.Int, I.Int, v => E.RNi(p, v), s, z0, hs0), {==})
  +esl : {A.sl(p, xh, yh) == z0 : I.Int} = Equal.trans(I.Int, A.sl(p, xh, yh), I.Int.add(z0, I.Int.neg(z0)), z0, Y.Int.cong2(s, z0, I.Int.neg(A.sh(p, xh, yh)), I.Int.neg(z0), hs0, Equal.cong(I.Int, I.Int, v => I.Int.neg(v), A.sh(p, xh, yh), z0, esh)), {==})
  +e0t : {I.Int.add(A.sl(p, xh, yh), th) == th : I.Int} = Equal.trans(I.Int, I.Int.add(A.sl(p, xh, yh), th), I.Int.add(z0, th), th,
    Equal.cong(I.Int, I.Int, v => I.Int.add(v, th), A.sl(p, xh, yh), z0, esl), BP.IntN(env, R.Ad(N.TZero{}, R.V(0n)), R.V(0n), [], [], {==}, Unit{}))
  +ec : {A.c(p, xh, xl, yh, yl) == th : I.Int} = Equal.trans(I.Int, A.c(p, xh, xl, yh, yl), E.RNi(p, th), th, Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(A.sl(p, xh, yh), th), th, e0t), E.RNi.exact(p, th, W.Rf.i(p1, L)))
  +sc = I.Int.add(A.sh(p, xh, yh), A.c(p, xh, xl, yh, yl))
  +esc : {sc == th : I.Int} = Equal.trans(I.Int, sc, I.Int.add(z0, th), th, Y.Int.cong2(A.sh(p, xh, yh), z0, A.c(p, xh, xl, yh, yl), th, esh, ec), BP.IntN(env, R.Ad(N.TZero{}, R.V(0n)), R.V(0n), [], [], {==}, Unit{}))
  +vh = A.vh(p, xh, xl, yh, yl)
  +vl = A.vl(p, xh, xl, yh, yl)
  +evh : {vh == th : I.Int} = Equal.trans(I.Int, vh, E.RNi(p, th), th, Equal.cong(I.Int, I.Int, v => E.RNi(p, v), sc, th, esc), E.RNi.exact(p, th, W.Rf.i(p1, L)))
  # line 4: Fast2Sum(0, th), so vl = 0
  +h4 : {I.Int.add(vh, vl) == sc : I.Int} = Equal.trans(I.Int, I.Int.add(vh, vl), I.Int.add(E.F2.s(p, z0, th), E.F2.t(p, z0, th)), sc,
    Y.Int.cong2(vh, E.F2.s(p, z0, th), vl, E.F2.t(p, z0, th), Equal.trans(I.Int, vh, E.F2.s(p, z0, A.c(p, xh, xl, yh, yl)), E.F2.s(p, z0, th), Equal.cong(I.Int, I.Int, v => E.F2.s(p, v, A.c(p, xh, xl, yh, yl)), A.sh(p, xh, yh), z0, esh), Equal.cong(I.Int, I.Int, v => E.F2.s(p, z0, v), A.c(p, xh, xl, yh, yl), th, ec)), Equal.trans(I.Int, vl, E.F2.t(p, z0, A.c(p, xh, xl, yh, yl)), E.F2.t(p, z0, th),
      Equal.cong(I.Int, I.Int, v => E.F2.t(p, v, A.c(p, xh, xl, yh, yl)), A.sh(p, xh, yh), z0, esh), Equal.cong(I.Int, I.Int, v => E.F2.t(p, z0, v), A.c(p, xh, xl, yh, yl), th, ec))),
    Equal.trans(I.Int, I.Int.add(E.F2.s(p, z0, th), E.F2.t(p, z0, th)), I.Int.add(z0, th), sc, F2.zero(p1, th, W.Rf.i(p1, L)), Equal.sym(I.Int, sc, I.Int.add(z0, th), Y.Int.cong2(A.sh(p, xh, yh), z0, A.c(p, xh, xl, yh, yl), th, esh, ec))))
  +envv : List<&2, I.Int> = [vh, vl, th]
  +evl : {vl == z0 : I.Int} = Equal.trans(I.Int, vl, I.Int.add(I.Int.add(vh, vl), I.Int.neg(vh)), z0, BP.IntN(envv, R.V(1n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(0n))), [], [], {==}, Unit{}),
    Equal.trans(I.Int, I.Int.add(I.Int.add(vh, vl), I.Int.neg(vh)), I.Int.add(th, I.Int.neg(th)), z0, Y.Int.cong2(I.Int.add(vh, vl), th, I.Int.neg(vh), I.Int.neg(th), Equal.trans(I.Int, I.Int.add(vh, vl), sc, th, h4, esc), Equal.cong(I.Int, I.Int, v => I.Int.neg(v), vh, th, evh)),
      BP.IntN(envv, R.Ad(R.V(2n), R.Ng(R.V(2n))), N.TZero{}, [], [], {==}, Unit{})))
  # w = tl, and |tl| <= |th|
  +etv : {I.Int.add(tl, vl) == tl : I.Int} = Equal.trans(I.Int, I.Int.add(tl, vl), I.Int.add(tl, z0), tl, Equal.cong(I.Int, I.Int, v => I.Int.add(tl, v), vl, z0, evl), BP.IntN(env, R.Ad(R.V(1n), N.TZero{}), R.V(1n), [], [], {==}, Unit{}))
  +ftl : {E.Rn(p, RD.Int.mag(tl)) == RD.Int.mag(tl) : Nat} = TS.tl.rep(p1, xl, yl, fx, fy)
  +ew : {A.w(p, xh, xl, yh, yl) == tl : I.Int} = Equal.trans(I.Int, A.w(p, xh, xl, yh, yl), E.RNi(p, tl), tl, Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(tl, vl), tl, etv), E.RNi.exact(p, tl, ftl))
  +mL = RD.Int.mag(L)
  +eth : {RD.Int.mag(th) == E.Rn(p, mL) : Nat} = W.Mag.sg(L, E.Rn(p, mL))
  +etl : {RD.Int.mag(tl) == E.Dist(E.Rn(p, mL), mL) : Nat} = Equal.trans(Nat, RD.Int.mag(tl), RD.Int.mag(I.Int.add(th, I.Int.neg(L))), E.Dist(E.Rn(p, mL), mL), Mag.flip(L, th), W.Err.i(p, L))
  +hle : {RD.Nat.lt(RD.Int.mag(vh), RD.Int.mag(A.w(p, xh, xl, yh, yl))) == False{} : Bool} = E.Le.trans(RD.Int.mag(A.w(p, xh, xl, yh, yl)), E.Dist(E.Rn(p, mL), mL), RD.Int.mag(vh),
    E.Le.eq(RD.Int.mag(A.w(p, xh, xl, yh, yl)), E.Dist(E.Rn(p, mL), mL), Equal.trans(Nat, RD.Int.mag(A.w(p, xh, xl, yh, yl)), RD.Int.mag(tl), E.Dist(E.Rn(p, mL), mL), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), A.w(p, xh, xl, yh, yl), tl, ew), etl)),
    E.Le.trans(E.Dist(E.Rn(p, mL), mL), E.Rn(p, mL), RD.Int.mag(vh), ErrRn(p1, mL), E.Le.eq(E.Rn(p, mL), RD.Int.mag(vh), Equal.trans(Nat, E.Rn(p, mL), RD.Int.mag(th), RD.Int.mag(vh), Equal.sym(Nat, RD.Int.mag(th), E.Rn(p, mL), eth), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), th, vh, Equal.sym(I.Int, vh, th, evh))))))
  +h6 : {A.z(p, xh, xl, yh, yl) == I.Int.add(vh, A.w(p, xh, xl, yh, yl)) : I.Int} = E.Fast2Sum(p1, vh, A.w(p, xh, xl, yh, yl), W.Rf.i(p1, sc), W.Rf.i(p1, I.Int.add(tl, vl)), hle)
  # e1 = e2 = 0
  +ee1 : {A.e1(1n+p1, xh, xl, yh, yl) == z0 : I.Int} = Equal.trans(I.Int, A.e1(1n+p1, xh, xl, yh, yl), I.Int.add(th, I.Int.neg(th)), z0, Y.Int.cong2(A.c(p, xh, xl, yh, yl), th, I.Int.neg(I.Int.add(A.sl(p, xh, yh), th)), I.Int.neg(th), ec, Equal.cong(I.Int, I.Int, v => I.Int.neg(v), I.Int.add(A.sl(p, xh, yh), th), th, e0t)),
    BP.IntN(env, R.Ad(R.V(0n), R.Ng(R.V(0n))), N.TZero{}, [], [], {==}, Unit{}))
  +ee2 : {A.e2(1n+p1, xh, xl, yh, yl) == z0 : I.Int} = Equal.trans(I.Int, A.e2(1n+p1, xh, xl, yh, yl), I.Int.add(tl, I.Int.neg(tl)), z0, Y.Int.cong2(A.w(p, xh, xl, yh, yl), tl, I.Int.neg(I.Int.add(tl, vl)), I.Int.neg(tl), ew, Equal.cong(I.Int, I.Int, v => I.Int.neg(v), I.Int.add(tl, vl), tl, etv)),
    BP.IntN(env, R.Ad(R.V(1n), R.Ng(R.V(1n))), N.TZero{}, [], [], {==}, Unit{}))
  Fin.zero(p1, xh, xl, yh, yl, Equal.trans(I.Int, A.eta(1n+p1, xh, xl, yh, yl), I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl)), z0, A.split(p, xh, xl, yh, yl, h4, h6), Equal.trans(I.Int, I.Int.add(A.e1(1n+p1, xh, xl, yh, yl), A.e2(1n+p1, xh, xl, yh, yl)), I.Int.add(z0, z0), z0, Y.Int.cong2(A.e1(1n+p1, xh, xl, yh, yl), z0, A.e2(1n+p1, xh, xl, yh, yl), z0, ee1, ee2), {==})))

# |eta| <= 3Q and M >= (2^p - 4) 2^p Q give the bound
def Fin.q(+p1: Nat, +e: Nat, +M: Nat, +Q: Nat, +he: {RD.Nat.lt(Nat.mul(3n, Q), e) == False{} : Bool}, +hM: {RD.Nat.lt(M, Nat.mul(Nat.mul(RD.Nat.pow2(1n+p1), Q), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n))) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(3n, M), Nat.mul(e, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)))) == False{} : Bool}:
  +P = RD.Nat.pow2(1n+p1)
  +m4 = RD.Nat.monus(P, 4n)
  +env : List<&2, Nat> = [Q, P, m4]
  +e1 : {Nat.mul(Nat.mul(3n, Q), Nat.mul(P, m4)) == Nat.mul(3n, Nat.mul(Nat.mul(P, Q), m4)) : Nat} = R.NatN.eq(env, R.Ml(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{}))), R.Ml(R.V(1n), R.V(2n))),
    R.Ad(R.Ml(R.Ml(R.V(1n), R.V(0n)), R.V(2n)), R.Ad(R.Ml(R.Ml(R.V(1n), R.V(0n)), R.V(2n)), R.Ad(R.Ml(R.Ml(R.V(1n), R.V(0n)), R.V(2n)), N.TZero{}))), [], [], {==}, Unit{}, {==}, {==})
  E.Le.trans(Nat.mul(e, Nat.mul(P, m4)), Nat.mul(Nat.mul(3n, Q), Nat.mul(P, m4)), Nat.mul(3n, M), E2.Le.mulr(e, Nat.mul(3n, Q), Nat.mul(P, m4), he),
    E.Le.trans(Nat.mul(Nat.mul(3n, Q), Nat.mul(P, m4)), Nat.mul(3n, Nat.mul(Nat.mul(P, Q), m4)), Nat.mul(3n, M), E.Le.eq(Nat.mul(Nat.mul(3n, Q), Nat.mul(P, m4)), Nat.mul(3n, Nat.mul(Nat.mul(P, Q), m4)), e1),
      E2.Le.mull(3n, Nat.mul(Nat.mul(P, Q), m4), M, hM)))

# the same from 2 |eta| <= 3Q and 2M >= (2^p - 4) 2^p Q
def Fin.q2(+p1: Nat, +e: Nat, +M: Nat, +Q: Nat, +he: {RD.Nat.lt(Nat.mul(3n, Q), Nat.double(e)) == False{} : Bool}, +hM: {RD.Nat.lt(Nat.double(M), Nat.mul(Nat.mul(RD.Nat.pow2(1n+p1), Q), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n))) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(3n, M), Nat.mul(e, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)))) == False{} : Bool}:
  +X = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n))
  +h = Fin.q(p1, Nat.double(e), Nat.double(M), Q, he, hM)
  W.Le.halve(Nat.mul(e, X), Nat.mul(3n, M), E.Le.trans(Nat.double(Nat.mul(e, X)), Nat.mul(Nat.double(e), X), Nat.double(Nat.mul(3n, M)),
    E.Le.eq(Nat.double(Nat.mul(e, X)), Nat.mul(Nat.double(e), X), Equal.sym(Nat, Nat.mul(Nat.double(e), X), Nat.double(Nat.mul(e, X)), BP.Mul.dbl_l(e, X))),
    E.Le.trans(Nat.mul(Nat.double(e), X), Nat.mul(3n, Nat.double(M)), Nat.double(Nat.mul(3n, M)), h, E.Le.eq(Nat.mul(3n, Nat.double(M)), Nat.double(Nat.mul(3n, M)), R.Nat.mul_double(3n, M)))))


# The cases with their relative bounds (U = 2^p Q is u, M = |x + y|)
def MX(+xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> Nat:
  RD.Int.mag(I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl)))

# 2a, sigma = 2: G = 2U
def F2a2(+p1: Nat, +q: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hs1: {RD.Nat.lt(RD.Int.mag(I.Int.add(xh, yh)), Nat.mul(4n, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))) == False{} : Bool}, +hs2: {RD.Nat.lt(Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), RD.Int.mag(I.Int.add(xh, yh))) == False{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(yl)) == False{} : Bool},
  +hM: {RD.Nat.lt(MX(xh, xl, yh, yl), Nat.mul(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n))) == False{} : Bool})
  -> {RelA(p1, xh, xl, yh, yl) == False{} : Bool}:
  +P = RD.Nat.pow2(1n+p1)
  +Q = RD.Nat.pow2(q)
  +U = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))
  +eG : {Nat.mul(P, Nat.double(Q)) == Nat.double(U) : Nat} = R.Nat.mul_double(P, Q)
  +r = C2a(p1, q, 1n+q, xh, xl, yh, yl, hp,
    E.Le.trans(Nat.mul(4n, Nat.mul(P, Nat.double(Q))), Nat.mul(4n, Nat.double(U)), RD.Int.mag(I.Int.add(xh, yh)), E.Le.eq(Nat.mul(4n, Nat.mul(P, Nat.double(Q))), Nat.mul(4n, Nat.double(U)), Equal.cong(Nat, Nat, v => Nat.mul(4n, v), Nat.mul(P, Nat.double(Q)), Nat.double(U), eG)), hs1),
    E.Le.trans(RD.Int.mag(I.Int.add(xh, yh)), Nat.mul(RD.Nat.monus(P, 2n), Nat.double(U)), Nat.mul(RD.Nat.monus(P, 2n), Nat.mul(P, Nat.double(Q))), hs2,
      E.Le.eq(Nat.mul(RD.Nat.monus(P, 2n), Nat.double(U)), Nat.mul(RD.Nat.monus(P, 2n), Nat.mul(P, Nat.double(Q))), Equal.cong(Nat, Nat, v => Nat.mul(RD.Nat.monus(P, 2n), v), Nat.double(U), Nat.mul(P, Nat.double(Q)), Equal.sym(Nat, Nat.mul(P, Nat.double(Q)), Nat.double(U), eG)))),
    hx, E.Le.trans(Nat.double(RD.Int.mag(yl)), Nat.double(U), Nat.mul(P, Nat.double(Q)), E.Le.dd(RD.Int.mag(yl), U, hy), E.Le.eq(Nat.double(U), Nat.mul(P, Nat.double(Q)), Equal.sym(Nat, Nat.mul(P, Nat.double(Q)), Nat.double(U), eG))),
    E2.Le.dbl(Q), E.Lt.irr(Nat.double(Q)))
  +he : {RD.Nat.lt(Nat.mul(3n, Q), RD.Int.mag(A.eta(1n+p1, xh, xl, yh, yl))) == False{} : Bool} = W.Le.halve(RD.Int.mag(A.eta(1n+p1, xh, xl, yh, yl)), Nat.mul(3n, Q),
    E.Le.trans(Nat.double(RD.Int.mag(A.eta(1n+p1, xh, xl, yh, yl))), Nat.mul(3n, Nat.double(Q)), Nat.double(Nat.mul(3n, Q)), r, E.Le.eq(Nat.mul(3n, Nat.double(Q)), Nat.double(Nat.mul(3n, Q)), R.Nat.mul_double(3n, Q))))
  Fin.q(p1, RD.Int.mag(A.eta(1n+p1, xh, xl, yh, yl)), MX(xh, xl, yh, yl), Q, he, hM)

# 2a, sigma = 1: G = U
def F2a1(+p1: Nat, +q: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hs1: {RD.Nat.lt(RD.Int.mag(I.Int.add(xh, yh)), Nat.mul(4n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))) == False{} : Bool}, +hs2: {RD.Nat.lt(Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))), RD.Int.mag(I.Int.add(xh, yh))) == False{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), Nat.double(RD.Int.mag(yl))) == False{} : Bool},
  +hM: {RD.Nat.lt(Nat.double(MX(xh, xl, yh, yl)), Nat.mul(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n))) == False{} : Bool})
  -> {RelA(p1, xh, xl, yh, yl) == False{} : Bool}:
  Fin.q2(p1, RD.Int.mag(A.eta(1n+p1, xh, xl, yh, yl)), MX(xh, xl, yh, yl), RD.Nat.pow2(q), C2a(p1, q, q, xh, xl, yh, yl, hp, hs1, hs2, hx, hy, E.Lt.irr(RD.Nat.pow2(q)), E2.Le.dbl(RD.Nat.pow2(q))), hM)

# 2b
def F2b(+p1: Nat, +q: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hs1: {RD.Nat.lt(RD.Int.mag(I.Int.add(xh, yh)), Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))) == False{} : Bool},
  +hs2: {RD.Nat.lt(Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 1n), Nat.double(Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))), RD.Int.mag(I.Int.add(xh, yh))) == False{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(yl)) == False{} : Bool},
  +hM: {RD.Nat.lt(MX(xh, xl, yh, yl), Nat.mul(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n))) == False{} : Bool})
  -> {RelA(p1, xh, xl, yh, yl) == False{} : Bool}:
  Fin.q(p1, RD.Int.mag(A.eta(1n+p1, xh, xl, yh, yl)), MX(xh, xl, yh, yl), RD.Nat.pow2(q), C2b(p1, q, xh, xl, yh, yl, hp, hs1, hs2, hx, hy), hM)

# M >= |s| - |L|: |s| >= K + k and |L| <= k give M >= K
def MX.lo(+xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +K: Nat, +k: Nat, +hs: {RD.Nat.lt(RD.Int.mag(I.Int.add(xh, yh)), Nat.add(K, k)) == False{} : Bool}, +hL: {RD.Nat.lt(k, RD.Int.mag(I.Int.add(xl, yl))) == False{} : Bool})
  -> {RD.Nat.lt(MX(xh, xl, yh, yl), K) == False{} : Bool}:
  +env : List<&2, I.Int> = [xh, xl, yh, yl]
  +eX : {I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)) == I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl)) : I.Int} = BP.IntN(env, R.Ad(R.Ad(R.V(0n), R.V(2n)), R.Ad(R.V(1n), R.V(3n))), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(2n), R.V(3n))), [], [], {==}, Unit{})
  Equal.trans(Bool, RD.Nat.lt(MX(xh, xl, yh, yl), K), RD.Nat.lt(RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl))), K), False{},
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(RD.Int.mag(v), K), I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl)), I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)), Equal.sym(I.Int, I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)), I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl)), eX)),
    Mag.low(I.Int.add(xh, yh), I.Int.add(xl, yl), K, k, hs, hL))


# 2^a < 2^b gives a < b
def Pow2.rev.go(+a: Nat, +b: Nat, +h: {RD.Nat.lt(RD.Nat.pow2(a), RD.Nat.pow2(b)) == True{} : Bool}, l: Bool, +el: {RD.Nat.lt(a, b) == l : Bool})
  -> {RD.Nat.lt(a, b) == True{} : Bool}:
  match l:
    case True{}:
      el
    case False{}:
      B.Bool.tf({RD.Nat.lt(a, b) == True{} : Bool}, Equal.trans(Bool, True{}, RD.Nat.lt(RD.Nat.pow2(a), RD.Nat.pow2(b)), False{}, Equal.sym(Bool, RD.Nat.lt(RD.Nat.pow2(a), RD.Nat.pow2(b)), True{}, h), E2.Pow2.mono(b, a, el)))

def Pow2.rev(+a: Nat, +b: Nat, +h: {RD.Nat.lt(RD.Nat.pow2(a), RD.Nat.pow2(b)) == True{} : Bool}) -> {RD.Nat.lt(a, b) == True{} : Bool}:
  Pow2.rev.go(a, b, h, RD.Nat.lt(a, b), {==})

# a positive multiple of G is at least G
def Mul.ge(+ms: Nat, +G: Nat, +d: Nat, +e: {d == Nat.mul(ms, G) : Nat}, +pos: {RD.Nat.lt(0n, d) == True{} : Bool}) -> {RD.Nat.lt(d, G) == False{} : Bool}:
  match ms:
    case 0n:
      B.Bool.tf({RD.Nat.lt(d, G) == False{} : Bool}, Equal.trans(Bool, True{}, RD.Nat.lt(0n, d), False{}, Equal.sym(Bool, RD.Nat.lt(0n, d), True{}, pos),
        Equal.trans(Bool, RD.Nat.lt(0n, d), RD.Nat.lt(0n, 0n), False{}, Equal.cong(Nat, Bool, v => RD.Nat.lt(0n, v), d, 0n, e), {==})))
    case 1n+k:
      E.Le.trans(G, Nat.add(G, Nat.mul(k, G)), d, E.Le.add(G, Nat.mul(k, G)), E.Le.eq(Nat.add(G, Nat.mul(k, G)), d, Equal.sym(Nat, d, Nat.add(G, Nat.mul(k, G)), e)))

# 2 |s| >= K + k and 2 |L| <= k give 2M >= K
def MX.lo2(+xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +K: Nat, +k: Nat, +hs: {RD.Nat.lt(Nat.double(RD.Int.mag(I.Int.add(xh, yh))), Nat.add(K, k)) == False{} : Bool}, +hL: {RD.Nat.lt(k, Nat.double(RD.Int.mag(I.Int.add(xl, yl)))) == False{} : Bool})
  -> {RD.Nat.lt(Nat.double(MX(xh, xl, yh, yl)), K) == False{} : Bool}:
  +env : List<&2, I.Int> = [xh, xl, yh, yl]
  +eX : {I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)) == I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl)) : I.Int} = BP.IntN(env, R.Ad(R.Ad(R.V(0n), R.V(2n)), R.Ad(R.V(1n), R.V(3n))), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(2n), R.V(3n))), [], [], {==}, Unit{})
  +M = MX(xh, xl, yh, yl)
  +eM : {RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl))) == M : Nat} = Equal.cong(I.Int, Nat, v => RD.Int.mag(v), I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl)), I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl)), eX)
  +hr : {RD.Nat.lt(Nat.add(M, RD.Int.mag(I.Int.add(xl, yl))), RD.Int.mag(I.Int.add(xh, yh))) == False{} : Bool} = E.Le.trans(RD.Int.mag(I.Int.add(xh, yh)), Nat.add(RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl))), RD.Int.mag(I.Int.add(xl, yl))), Nat.add(M, RD.Int.mag(I.Int.add(xl, yl))),
    Mag.rev(I.Int.add(xh, yh), I.Int.add(xl, yl)), E.Le.eq(Nat.add(RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl))), RD.Int.mag(I.Int.add(xl, yl))), Nat.add(M, RD.Int.mag(I.Int.add(xl, yl))), Equal.cong(Nat, Nat, v => Nat.add(v, RD.Int.mag(I.Int.add(xl, yl))), RD.Int.mag(I.Int.add(I.Int.add(xh, yh), I.Int.add(xl, yl))), M, eM)))
  E2.Le.canl(k, K, Nat.double(M), E.Le.trans(Nat.add(k, K), Nat.add(K, k), Nat.add(k, Nat.double(M)), E.Le.eq(Nat.add(k, K), Nat.add(K, k), NL.Nat.add_comm(k, K)),
   E.Le.trans(Nat.add(K, k), Nat.add(Nat.double(M), k), Nat.add(k, Nat.double(M)), E.Le.trans(Nat.add(K, k), Nat.double(RD.Int.mag(I.Int.add(xh, yh))), Nat.add(Nat.double(M), k), hs,
    E.Le.trans(Nat.double(RD.Int.mag(I.Int.add(xh, yh))), Nat.add(Nat.double(M), Nat.double(RD.Int.mag(I.Int.add(xl, yl)))), Nat.add(Nat.double(M), k),
      E.Le.trans(Nat.double(RD.Int.mag(I.Int.add(xh, yh))), Nat.double(Nat.add(M, RD.Int.mag(I.Int.add(xl, yl)))), Nat.add(Nat.double(M), Nat.double(RD.Int.mag(I.Int.add(xl, yl)))), E.Le.dd(RD.Int.mag(I.Int.add(xh, yh)), Nat.add(M, RD.Int.mag(I.Int.add(xl, yl))), hr),
        E.Le.eq(Nat.double(Nat.add(M, RD.Int.mag(I.Int.add(xl, yl)))), Nat.add(Nat.double(M), Nat.double(RD.Int.mag(I.Int.add(xl, yl)))), E2.Dbl.add(M, RD.Int.mag(I.Int.add(xl, yl))))),
      E2.Le.addl(Nat.double(M), Nat.double(RD.Int.mag(I.Int.add(xl, yl))), k, hL))), E.Le.eq(Nat.add(Nat.double(M), k), Nat.add(k, Nat.double(M)), NL.Nat.add_comm(Nat.double(M), k)))))


# Numeric facts for p >= 6 (2^p = 4 + m4, m4 >= 60), for any U
def NQ.e4(+p1: Nat, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool}) -> {RD.Nat.pow2(1n+p1) == Nat.add(4n, RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)) : Nat}:
  E.Le.wit(4n, RD.Nat.pow2(1n+p1), E.Le.trans(4n, 64n, RD.Nat.pow2(1n+p1), {==}, W.P64(p1, hp)))

def NQ.m60(+p1: Nat, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool}) -> {RD.Nat.lt(RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n), 60n) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n), 60n), RD.Nat.lt(Nat.add(4n, RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)), 64n), False{}, {==},
    Equal.trans(Bool, RD.Nat.lt(Nat.add(4n, RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)), 64n), RD.Nat.lt(RD.Nat.pow2(1n+p1), 64n), False{}, Equal.cong(Nat, Bool, v => RD.Nat.lt(v, 64n), Nat.add(4n, RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)), RD.Nat.pow2(1n+p1), Equal.sym(Nat, RD.Nat.pow2(1n+p1), Nat.add(4n, RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)), NQ.e4(p1, hp))), W.P64(p1, hp)))

# (m4 + 2) U = (2^p - 2) U
def NQ.one(+p1: Nat, +U: Nat, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool}) -> {Nat.add(Nat.mul(U, RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)), Nat.double(U)) == Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), U) : Nat}:
  +m4 = RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)
  +env : List<&2, Nat> = [U, m4, Nat.double(U)]
  +e2 : {Nat.double(U) == Nat.add(U, U) : Nat} = Y.Nat.double_add(U)
  Equal.trans(Nat, Nat.add(Nat.mul(U, m4), Nat.double(U)), Nat.mul(RD.Nat.monus(Nat.add(4n, m4), 2n), U), Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), U),
    R.NatN.eq2(env, R.Ad(R.Ml(R.V(0n), R.V(1n)), R.V(2n)), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ml(R.V(1n), R.V(0n)))), [], [], [R.Ad(R.V(2n), R.Ng(R.Ad(R.V(0n), R.V(0n))))], {==}, Unit{},
      (R.NatN.z(env, R.V(2n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, e2), Unit{}), {==}, {==}),
    Equal.cong(Nat, Nat, v => Nat.mul(RD.Nat.monus(v, 2n), U), Nat.add(4n, m4), RD.Nat.pow2(1n+p1), Equal.sym(Nat, RD.Nat.pow2(1n+p1), Nat.add(4n, m4), NQ.e4(p1, hp))))

# (m4 + 3) U <= 2^p U
def NQ.four(+p1: Nat, +U: Nat, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool}) -> {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), U), Nat.add(Nat.mul(U, RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)), Nat.mul(3n, U))) == False{} : Bool}:
  +m4 = RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)
  +env : List<&2, Nat> = [U, m4]
  +e : {Nat.mul(Nat.add(4n, m4), U) == Nat.add(Nat.add(Nat.mul(U, m4), Nat.mul(3n, U)), U) : Nat} = R.NatN.eq(env, R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ml(R.V(1n), R.V(0n)))))),
    R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{})))), R.V(0n)), [], [], {==}, Unit{}, {==}, {==})
  E.Le.trans(Nat.add(Nat.mul(U, m4), Nat.mul(3n, U)), Nat.add(Nat.add(Nat.mul(U, m4), Nat.mul(3n, U)), U), Nat.mul(RD.Nat.pow2(1n+p1), U), E.Le.add(Nat.add(Nat.mul(U, m4), Nat.mul(3n, U)), U),
    E.Le.eq(Nat.add(Nat.add(Nat.mul(U, m4), Nat.mul(3n, U)), U), Nat.mul(RD.Nat.pow2(1n+p1), U), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(U, m4), Nat.mul(3n, U)), U), Nat.mul(Nat.add(4n, m4), U), Nat.mul(RD.Nat.pow2(1n+p1), U),
      Equal.sym(Nat, Nat.mul(Nat.add(4n, m4), U), Nat.add(Nat.add(Nat.mul(U, m4), Nat.mul(3n, U)), U), e),
      Equal.cong(Nat, Nat, v => Nat.mul(v, U), Nat.add(4n, m4), RD.Nat.pow2(1n+p1), Equal.sym(Nat, RD.Nat.pow2(1n+p1), Nat.add(4n, m4), NQ.e4(p1, hp))))))

# 8U = 4 (2U) <= (2^p - 2) U
def NQ.three(+p1: Nat, +U: Nat, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool}) -> {RD.Nat.lt(Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), U), Nat.mul(4n, Nat.double(U))) == False{} : Bool}:
  +m4 = RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)
  +env : List<&2, Nat> = [U, Nat.double(U)]
  +e2 : {Nat.double(U) == Nat.add(U, U) : Nat} = Y.Nat.double_add(U)
  +e8 : {Nat.mul(4n, Nat.double(U)) == Nat.mul(8n, U) : Nat} = R.NatN.eq2(env, R.Ad(R.V(1n), R.Ad(R.V(1n), R.Ad(R.V(1n), R.Ad(R.V(1n), N.TZero{})))),
    R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{})))))))), [], [],
    [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n))))], {==}, Unit{},
    (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, e2), (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, e2), (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, e2), (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, e2), Unit{})))), {==}, {==})
  +h : {RD.Nat.lt(Nat.add(2n, m4), 8n) == False{} : Bool} = E.Le.trans(6n, 60n, m4, {==}, NQ.m60(p1, hp))
  E.Le.trans(Nat.mul(4n, Nat.double(U)), Nat.mul(8n, U), Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), U), E.Le.eq(Nat.mul(4n, Nat.double(U)), Nat.mul(8n, U), e8),
    E.Le.trans(Nat.mul(8n, U), Nat.mul(Nat.add(2n, m4), U), Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), U), E2.Le.mulr(8n, Nat.add(2n, m4), U, h),
      E.Le.eq(Nat.mul(Nat.add(2n, m4), U), Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), U), Equal.cong(Nat, Nat, v => Nat.mul(RD.Nat.monus(v, 2n), U), Nat.add(4n, m4), RD.Nat.pow2(1n+p1), Equal.sym(Nat, RD.Nat.pow2(1n+p1), Nat.add(4n, m4), NQ.e4(p1, hp))))))


# The cases, from the operands' form
# ----------------------------------
# xh = A 2U with 2^(p-1) <= A < 2^p (U = 2^p Q is u), yh = +-B 2^(1+Ey) with
# 2^(p-1) <= B < 2^p (2^Ey is u at yh), |yh| <= xh, Ey <= D.

# yh > 0: case 2a with sigma = 2, or 2b
def AD.pos.go(+p1: Nat, +q: Nat, +A: Nat, +B: Nat, +Ey: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hyl: {RD.Nat.lt(RD.Nat.pow2(Ey), RD.Int.mag(yl)) == False{} : Bool},
  +hEy: {RD.Nat.lt(Nat.add(1n+p1, q), Ey) == False{} : Bool}, +hyx: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey))) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat}, l: Bool, +el: {RD.Nat.lt(Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.add(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey)))) == l : Bool})
  -> {RelA(p1, I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, xl, I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}, yl) == False{} : Bool}:
  match l:
    case False{}:
  +P = RD.Nat.pow2(1n+p1)
  +H = RD.Nat.pow2(p1)
  +Q = RD.Nat.pow2(q)
  +U = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))
  +m1 = RD.Nat.monus(P, 1n)
  +m2 = RD.Nat.monus(P, 2n)
  +m4 = RD.Nat.monus(P, 4n)
  +X = Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))
  +Yv = Nat.mul(B, RD.Nat.pow2(1n+Ey))
  +Gy = RD.Nat.pow2(1n+Ey)
  +D = Nat.add(1n+p1, q)
  +eU : {RD.Nat.pow2(D) == U : Nat} = BP.Pow2.add(1n+p1, q)
  +hYU : {RD.Nat.lt(U, RD.Nat.pow2(Ey)) == False{} : Bool} = E.Le.trans(RD.Nat.pow2(Ey), RD.Nat.pow2(D), U, E2.Pow2.mono(Ey, D, hEy), E.Le.eq(RD.Nat.pow2(D), U, eU))
  +hyU : {RD.Nat.lt(U, RD.Int.mag(yl)) == False{} : Bool} = E.Le.trans(RD.Int.mag(yl), RD.Nat.pow2(Ey), U, hyl, hYU)
  +hONE : {RD.Nat.lt(X, Nat.mul(P, U)) == False{} : Bool} = E.Le.trans(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), X, E.Le.eq(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), BP.Mul.dbl_l(H, U)),
    E.Le.trans(Nat.double(Nat.mul(H, U)), Nat.double(Nat.mul(A, U)), X, E.Le.dd(Nat.mul(H, U), Nat.mul(A, U), E2.Le.mulr(H, A, U, hA1)), E.Le.eq(Nat.double(Nat.mul(A, U)), X, Equal.sym(Nat, X, Nat.double(Nat.mul(A, U)), R.Nat.mul_double(A, U)))))
  +hXm : {RD.Nat.lt(Nat.mul(m1, Nat.double(U)), X) == False{} : Bool} = E2.Le.mulr(A, m1, Nat.double(U), W.Lt.pm(A, P, hA))
  +hL2 : {RD.Nat.lt(Nat.double(U), RD.Int.mag(I.Int.add(xl, yl))) == False{} : Bool} = E.Le.trans(RD.Int.mag(I.Int.add(xl, yl)), Nat.add(U, U), Nat.double(U), W.Tri2(xl, yl, U, U, hx, hyU), E.Le.eq(Nat.add(U, U), Nat.double(U), Equal.sym(Nat, Nat.double(U), Nat.add(U, U), Y.Nat.double_add(U))))
      +hsP : {RD.Nat.lt(Nat.add(X, Yv), Nat.mul(P, U)) == False{} : Bool} = E.Le.trans(Nat.mul(P, U), X, Nat.add(X, Yv), hONE, E.Le.add(X, Yv))
      +hPm : {RD.Nat.lt(Nat.mul(P, U), Nat.mul(m2, U)) == False{} : Bool} = E2.Le.mulr(m2, P, U, W.Mo.le(P, 2n))
      F2a2(p1, q, I.IPos{X}, xl, I.IPos{Yv}, yl, hp,
        E.Le.trans(Nat.mul(4n, Nat.double(U)), Nat.mul(m2, U), Nat.add(X, Yv), NQ.three(p1, U, hp), E.Le.trans(Nat.mul(m2, U), Nat.mul(P, U), Nat.add(X, Yv), hPm, hsP)),
        el, hx, hyU,
        MX.lo(I.IPos{X}, xl, I.IPos{Yv}, yl, Nat.mul(U, m4), Nat.double(U),
          E.Le.trans(Nat.add(Nat.mul(U, m4), Nat.double(U)), Nat.mul(m2, U), Nat.add(X, Yv), E.Le.eq(Nat.add(Nat.mul(U, m4), Nat.double(U)), Nat.mul(m2, U), NQ.one(p1, U, hp)), E.Le.trans(Nat.mul(m2, U), Nat.mul(P, U), Nat.add(X, Yv), hPm, hsP)), hL2))
    case True{}:
  +P = RD.Nat.pow2(1n+p1)
  +H = RD.Nat.pow2(p1)
  +Q = RD.Nat.pow2(q)
  +U = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))
  +m1 = RD.Nat.monus(P, 1n)
  +m2 = RD.Nat.monus(P, 2n)
  +m4 = RD.Nat.monus(P, 4n)
  +X = Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))
  +Yv = Nat.mul(B, RD.Nat.pow2(1n+Ey))
  +Gy = RD.Nat.pow2(1n+Ey)
  +D = Nat.add(1n+p1, q)
  +eU : {RD.Nat.pow2(D) == U : Nat} = BP.Pow2.add(1n+p1, q)
  +hYU : {RD.Nat.lt(U, RD.Nat.pow2(Ey)) == False{} : Bool} = E.Le.trans(RD.Nat.pow2(Ey), RD.Nat.pow2(D), U, E2.Pow2.mono(Ey, D, hEy), E.Le.eq(RD.Nat.pow2(D), U, eU))
  +hyU : {RD.Nat.lt(U, RD.Int.mag(yl)) == False{} : Bool} = E.Le.trans(RD.Int.mag(yl), RD.Nat.pow2(Ey), U, hyl, hYU)
  +hONE : {RD.Nat.lt(X, Nat.mul(P, U)) == False{} : Bool} = E.Le.trans(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), X, E.Le.eq(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), BP.Mul.dbl_l(H, U)),
    E.Le.trans(Nat.double(Nat.mul(H, U)), Nat.double(Nat.mul(A, U)), X, E.Le.dd(Nat.mul(H, U), Nat.mul(A, U), E2.Le.mulr(H, A, U, hA1)), E.Le.eq(Nat.double(Nat.mul(A, U)), X, Equal.sym(Nat, X, Nat.double(Nat.mul(A, U)), R.Nat.mul_double(A, U)))))
  +hXm : {RD.Nat.lt(Nat.mul(m1, Nat.double(U)), X) == False{} : Bool} = E2.Le.mulr(A, m1, Nat.double(U), W.Lt.pm(A, P, hA))
  +hL2 : {RD.Nat.lt(Nat.double(U), RD.Int.mag(I.Int.add(xl, yl))) == False{} : Bool} = E.Le.trans(RD.Int.mag(I.Int.add(xl, yl)), Nat.add(U, U), Nat.double(U), W.Tri2(xl, yl, U, U, hx, hyU), E.Le.eq(Nat.add(U, U), Nat.double(U), Equal.sym(Nat, Nat.double(U), Nat.add(U, U), Y.Nat.double_add(U))))
      +hs : {RD.Nat.lt(Nat.add(X, Yv), Nat.mul(m2, Nat.double(U))) == False{} : Bool} = E2.Lt.to_le(Nat.mul(m2, Nat.double(U)), Nat.add(X, Yv), el)
      F2b(p1, q, I.IPos{X}, xl, I.IPos{Yv}, yl, hp, hs,
        E.Le.trans(Nat.add(X, Yv), Nat.double(X), Nat.mul(m1, Nat.double(Nat.double(U))),
          E.Le.trans(Nat.add(X, Yv), Nat.add(X, X), Nat.double(X), E2.Le.addl(X, Yv, X, hyx), E.Le.eq(Nat.add(X, X), Nat.double(X), Equal.sym(Nat, Nat.double(X), Nat.add(X, X), Y.Nat.double_add(X)))),
          E.Le.trans(Nat.double(X), Nat.double(Nat.mul(m1, Nat.double(U))), Nat.mul(m1, Nat.double(Nat.double(U))), E.Le.dd(X, Nat.mul(m1, Nat.double(U)), hXm),
            E.Le.eq(Nat.double(Nat.mul(m1, Nat.double(U))), Nat.mul(m1, Nat.double(Nat.double(U))), Equal.sym(Nat, Nat.mul(m1, Nat.double(Nat.double(U))), Nat.double(Nat.mul(m1, Nat.double(U))), R.Nat.mul_double(m1, Nat.double(U)))))),
        hx, hyU,
        MX.lo(I.IPos{X}, xl, I.IPos{Yv}, yl, Nat.mul(U, m4), Nat.double(U),
          E.Le.trans(Nat.add(Nat.mul(U, m4), Nat.double(U)), Nat.mul(m2, U), Nat.add(X, Yv), E.Le.eq(Nat.add(Nat.mul(U, m4), Nat.double(U)), Nat.mul(m2, U), NQ.one(p1, U, hp)),
            E.Le.trans(Nat.mul(m2, U), Nat.mul(m2, Nat.double(U)), Nat.add(X, Yv), E2.Le.mull(m2, U, Nat.double(U), E2.Le.dbl(U)), hs)), hL2))

def AD.pos(+p1: Nat, +q: Nat, +A: Nat, +B: Nat, +Ey: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hyl: {RD.Nat.lt(RD.Nat.pow2(Ey), RD.Int.mag(yl)) == False{} : Bool},
  +hEy: {RD.Nat.lt(Nat.add(1n+p1, q), Ey) == False{} : Bool}, +hyx: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey))) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat}) -> {RelA(p1, I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, xl, I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}, yl) == False{} : Bool}:
  AD.pos.go(p1, q, A, B, Ey, xl, yl, hp, hA1, hA, hB1, hB, hx, hyl, hEy, hyx, fx, fy, RD.Nat.lt(Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.add(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey)))), {==})


# yh < 0, 2 |yh| <= xh: case 2, sigma = 1 or 2, or 2b
def AD.big.go2(+p1: Nat, +q: Nat, +A: Nat, +B: Nat, +Ey: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hyl: {RD.Nat.lt(RD.Nat.pow2(Ey), RD.Int.mag(yl)) == False{} : Bool},
  +hEy: {RD.Nat.lt(Nat.add(1n+p1, q), Ey) == False{} : Bool}, +hyx: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey))) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat}, +d: Nat, +ems: {RD.Int.mag(I.Int.add(I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, I.Int.neg(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}))) == d : Nat}, +hdX: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), d) == False{} : Bool},
  +el1: {RD.Nat.lt(Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))), d) == True{} : Bool}, l: Bool, +el: {RD.Nat.lt(Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), d) == l : Bool})
  -> {RelA(p1, I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, xl, I.Int.neg(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}), yl) == False{} : Bool}:
  match l:
    case False{}:
  +P = RD.Nat.pow2(1n+p1)
  +H = RD.Nat.pow2(p1)
  +Q = RD.Nat.pow2(q)
  +U = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))
  +m1 = RD.Nat.monus(P, 1n)
  +m2 = RD.Nat.monus(P, 2n)
  +m4 = RD.Nat.monus(P, 4n)
  +X = Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))
  +Yv = Nat.mul(B, RD.Nat.pow2(1n+Ey))
  +Gy = RD.Nat.pow2(1n+Ey)
  +D = Nat.add(1n+p1, q)
  +eU : {RD.Nat.pow2(D) == U : Nat} = BP.Pow2.add(1n+p1, q)
  +hYU : {RD.Nat.lt(U, RD.Nat.pow2(Ey)) == False{} : Bool} = E.Le.trans(RD.Nat.pow2(Ey), RD.Nat.pow2(D), U, E2.Pow2.mono(Ey, D, hEy), E.Le.eq(RD.Nat.pow2(D), U, eU))
  +hyU : {RD.Nat.lt(U, RD.Int.mag(yl)) == False{} : Bool} = E.Le.trans(RD.Int.mag(yl), RD.Nat.pow2(Ey), U, hyl, hYU)
  +hONE : {RD.Nat.lt(X, Nat.mul(P, U)) == False{} : Bool} = E.Le.trans(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), X, E.Le.eq(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), BP.Mul.dbl_l(H, U)),
    E.Le.trans(Nat.double(Nat.mul(H, U)), Nat.double(Nat.mul(A, U)), X, E.Le.dd(Nat.mul(H, U), Nat.mul(A, U), E2.Le.mulr(H, A, U, hA1)), E.Le.eq(Nat.double(Nat.mul(A, U)), X, Equal.sym(Nat, X, Nat.double(Nat.mul(A, U)), R.Nat.mul_double(A, U)))))
  +hXm : {RD.Nat.lt(Nat.mul(m1, Nat.double(U)), X) == False{} : Bool} = E2.Le.mulr(A, m1, Nat.double(U), W.Lt.pm(A, P, hA))
  +hL2 : {RD.Nat.lt(Nat.double(U), RD.Int.mag(I.Int.add(xl, yl))) == False{} : Bool} = E.Le.trans(RD.Int.mag(I.Int.add(xl, yl)), Nat.add(U, U), Nat.double(U), W.Tri2(xl, yl, U, U, hx, hyU), E.Le.eq(Nat.add(U, U), Nat.double(U), Equal.sym(Nat, Nat.double(U), Nat.add(U, U), Y.Nat.double_add(U))))
      +s = I.Int.add(I.IPos{X}, I.Int.neg(I.IPos{Yv}))
      +hd : {RD.Nat.lt(d, Nat.mul(m2, U)) == False{} : Bool} = E2.Lt.to_le(Nat.mul(m2, U), d, el1)
      F2a2(p1, q, I.IPos{X}, xl, I.Int.neg(I.IPos{Yv}), yl, hp,
        E.Le.trans(Nat.mul(4n, Nat.double(U)), d, RD.Int.mag(s), E.Le.trans(Nat.mul(4n, Nat.double(U)), Nat.mul(m2, U), d, NQ.three(p1, U, hp), hd), E.Le.eq(d, RD.Int.mag(s), Equal.sym(Nat, RD.Int.mag(s), d, ems))),
        E.Le.trans(RD.Int.mag(s), d, Nat.mul(m2, Nat.double(U)), E.Le.eq(RD.Int.mag(s), d, ems), el), hx, hyU,
        MX.lo(I.IPos{X}, xl, I.Int.neg(I.IPos{Yv}), yl, Nat.mul(U, m4), Nat.double(U),
          E.Le.trans(Nat.add(Nat.mul(U, m4), Nat.double(U)), d, RD.Int.mag(s), E.Le.trans(Nat.add(Nat.mul(U, m4), Nat.double(U)), Nat.mul(m2, U), d, E.Le.eq(Nat.add(Nat.mul(U, m4), Nat.double(U)), Nat.mul(m2, U), NQ.one(p1, U, hp)), hd),
            E.Le.eq(d, RD.Int.mag(s), Equal.sym(Nat, RD.Int.mag(s), d, ems))), hL2))
    case True{}:
  +P = RD.Nat.pow2(1n+p1)
  +H = RD.Nat.pow2(p1)
  +Q = RD.Nat.pow2(q)
  +U = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))
  +m1 = RD.Nat.monus(P, 1n)
  +m2 = RD.Nat.monus(P, 2n)
  +m4 = RD.Nat.monus(P, 4n)
  +X = Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))
  +Yv = Nat.mul(B, RD.Nat.pow2(1n+Ey))
  +Gy = RD.Nat.pow2(1n+Ey)
  +D = Nat.add(1n+p1, q)
  +eU : {RD.Nat.pow2(D) == U : Nat} = BP.Pow2.add(1n+p1, q)
  +hYU : {RD.Nat.lt(U, RD.Nat.pow2(Ey)) == False{} : Bool} = E.Le.trans(RD.Nat.pow2(Ey), RD.Nat.pow2(D), U, E2.Pow2.mono(Ey, D, hEy), E.Le.eq(RD.Nat.pow2(D), U, eU))
  +hyU : {RD.Nat.lt(U, RD.Int.mag(yl)) == False{} : Bool} = E.Le.trans(RD.Int.mag(yl), RD.Nat.pow2(Ey), U, hyl, hYU)
  +hONE : {RD.Nat.lt(X, Nat.mul(P, U)) == False{} : Bool} = E.Le.trans(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), X, E.Le.eq(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), BP.Mul.dbl_l(H, U)),
    E.Le.trans(Nat.double(Nat.mul(H, U)), Nat.double(Nat.mul(A, U)), X, E.Le.dd(Nat.mul(H, U), Nat.mul(A, U), E2.Le.mulr(H, A, U, hA1)), E.Le.eq(Nat.double(Nat.mul(A, U)), X, Equal.sym(Nat, X, Nat.double(Nat.mul(A, U)), R.Nat.mul_double(A, U)))))
  +hXm : {RD.Nat.lt(Nat.mul(m1, Nat.double(U)), X) == False{} : Bool} = E2.Le.mulr(A, m1, Nat.double(U), W.Lt.pm(A, P, hA))
  +hL2 : {RD.Nat.lt(Nat.double(U), RD.Int.mag(I.Int.add(xl, yl))) == False{} : Bool} = E.Le.trans(RD.Int.mag(I.Int.add(xl, yl)), Nat.add(U, U), Nat.double(U), W.Tri2(xl, yl, U, U, hx, hyU), E.Le.eq(Nat.add(U, U), Nat.double(U), Equal.sym(Nat, Nat.double(U), Nat.add(U, U), Y.Nat.double_add(U))))
      +s = I.Int.add(I.IPos{X}, I.Int.neg(I.IPos{Yv}))
      +hd : {RD.Nat.lt(d, Nat.mul(m2, Nat.double(U))) == False{} : Bool} = E2.Lt.to_le(Nat.mul(m2, Nat.double(U)), d, el)
      F2b(p1, q, I.IPos{X}, xl, I.Int.neg(I.IPos{Yv}), yl, hp,
        E.Le.trans(Nat.mul(m2, Nat.double(U)), d, RD.Int.mag(s), hd, E.Le.eq(d, RD.Int.mag(s), Equal.sym(Nat, RD.Int.mag(s), d, ems))),
        E.Le.trans(RD.Int.mag(s), X, Nat.mul(m1, Nat.double(Nat.double(U))), E.Le.trans(RD.Int.mag(s), d, X, E.Le.eq(RD.Int.mag(s), d, ems), hdX),
          E.Le.trans(X, Nat.mul(m1, Nat.double(U)), Nat.mul(m1, Nat.double(Nat.double(U))), hXm, E2.Le.mull(m1, Nat.double(U), Nat.double(Nat.double(U)), E2.Le.dbl(Nat.double(U))))),
        hx, hyU,
        MX.lo(I.IPos{X}, xl, I.Int.neg(I.IPos{Yv}), yl, Nat.mul(U, m4), Nat.double(U),
          E.Le.trans(Nat.add(Nat.mul(U, m4), Nat.double(U)), d, RD.Int.mag(s), E.Le.trans(Nat.add(Nat.mul(U, m4), Nat.double(U)), Nat.mul(m2, U), d, E.Le.eq(Nat.add(Nat.mul(U, m4), Nat.double(U)), Nat.mul(m2, U), NQ.one(p1, U, hp)),
              E.Le.trans(Nat.mul(m2, U), Nat.mul(m2, Nat.double(U)), d, E2.Le.mull(m2, U, Nat.double(U), E2.Le.dbl(U)), hd)),
            E.Le.eq(d, RD.Int.mag(s), Equal.sym(Nat, RD.Int.mag(s), d, ems))), hL2))

def AD.big.go1(+p1: Nat, +q: Nat, +A: Nat, +B: Nat, +Ey: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hyl: {RD.Nat.lt(RD.Nat.pow2(Ey), RD.Int.mag(yl)) == False{} : Bool},
  +hEy: {RD.Nat.lt(Nat.add(1n+p1, q), Ey) == False{} : Bool}, +hyx: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey))) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat}, +d: Nat, +ems: {RD.Int.mag(I.Int.add(I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, I.Int.neg(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}))) == d : Nat}, +hdX: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), d) == False{} : Bool},
  +hX2: {RD.Nat.lt(Nat.double(d), Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))) == False{} : Bool}, +hGy: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Nat.pow2(1n+Ey)) == False{} : Bool},
  l: Bool, +el: {RD.Nat.lt(Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))), d) == l : Bool})
  -> {RelA(p1, I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, xl, I.Int.neg(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}), yl) == False{} : Bool}:
  match l:
    case False{}:
  +P = RD.Nat.pow2(1n+p1)
  +H = RD.Nat.pow2(p1)
  +Q = RD.Nat.pow2(q)
  +U = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))
  +m1 = RD.Nat.monus(P, 1n)
  +m2 = RD.Nat.monus(P, 2n)
  +m4 = RD.Nat.monus(P, 4n)
  +X = Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))
  +Yv = Nat.mul(B, RD.Nat.pow2(1n+Ey))
  +Gy = RD.Nat.pow2(1n+Ey)
  +D = Nat.add(1n+p1, q)
  +eU : {RD.Nat.pow2(D) == U : Nat} = BP.Pow2.add(1n+p1, q)
  +hYU : {RD.Nat.lt(U, RD.Nat.pow2(Ey)) == False{} : Bool} = E.Le.trans(RD.Nat.pow2(Ey), RD.Nat.pow2(D), U, E2.Pow2.mono(Ey, D, hEy), E.Le.eq(RD.Nat.pow2(D), U, eU))
  +hyU : {RD.Nat.lt(U, RD.Int.mag(yl)) == False{} : Bool} = E.Le.trans(RD.Int.mag(yl), RD.Nat.pow2(Ey), U, hyl, hYU)
  +hONE : {RD.Nat.lt(X, Nat.mul(P, U)) == False{} : Bool} = E.Le.trans(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), X, E.Le.eq(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), BP.Mul.dbl_l(H, U)),
    E.Le.trans(Nat.double(Nat.mul(H, U)), Nat.double(Nat.mul(A, U)), X, E.Le.dd(Nat.mul(H, U), Nat.mul(A, U), E2.Le.mulr(H, A, U, hA1)), E.Le.eq(Nat.double(Nat.mul(A, U)), X, Equal.sym(Nat, X, Nat.double(Nat.mul(A, U)), R.Nat.mul_double(A, U)))))
  +hXm : {RD.Nat.lt(Nat.mul(m1, Nat.double(U)), X) == False{} : Bool} = E2.Le.mulr(A, m1, Nat.double(U), W.Lt.pm(A, P, hA))
  +hL2 : {RD.Nat.lt(Nat.double(U), RD.Int.mag(I.Int.add(xl, yl))) == False{} : Bool} = E.Le.trans(RD.Int.mag(I.Int.add(xl, yl)), Nat.add(U, U), Nat.double(U), W.Tri2(xl, yl, U, U, hx, hyU), E.Le.eq(Nat.add(U, U), Nat.double(U), Equal.sym(Nat, Nat.double(U), Nat.add(U, U), Y.Nat.double_add(U))))
      +s = I.Int.add(I.IPos{X}, I.Int.neg(I.IPos{Yv}))
      +h2s : {RD.Nat.lt(Nat.double(RD.Int.mag(s)), Nat.mul(P, U)) == False{} : Bool} = E.Le.trans(Nat.mul(P, U), X, Nat.double(RD.Int.mag(s)), hONE,
        E.Le.trans(X, Nat.double(d), Nat.double(RD.Int.mag(s)), hX2, E.Le.eq(Nat.double(d), Nat.double(RD.Int.mag(s)), Equal.cong(Nat, Nat, v => Nat.double(v), d, RD.Int.mag(s), Equal.sym(Nat, RD.Int.mag(s), d, ems)))))
      +hPm : {RD.Nat.lt(Nat.mul(P, U), Nat.mul(m2, U)) == False{} : Bool} = E2.Le.mulr(m2, P, U, W.Mo.le(P, 2n))
      +h4U : {RD.Nat.lt(RD.Int.mag(s), Nat.mul(4n, U)) == False{} : Bool} = W.Le.halve(Nat.mul(4n, U), RD.Int.mag(s), E.Le.trans(Nat.double(Nat.mul(4n, U)), Nat.mul(P, U), Nat.double(RD.Int.mag(s)),
        E.Le.trans(Nat.double(Nat.mul(4n, U)), Nat.mul(4n, Nat.double(U)), Nat.mul(P, U), E.Le.eq(Nat.double(Nat.mul(4n, U)), Nat.mul(4n, Nat.double(U)), Equal.sym(Nat, Nat.mul(4n, Nat.double(U)), Nat.double(Nat.mul(4n, U)), R.Nat.mul_double(4n, U))),
          E.Le.trans(Nat.mul(4n, Nat.double(U)), Nat.mul(m2, U), Nat.mul(P, U), NQ.three(p1, U, hp), hPm)), h2s))
      +hy2 : {RD.Nat.lt(U, Nat.double(RD.Int.mag(yl))) == False{} : Bool} = E.Le.trans(Nat.double(RD.Int.mag(yl)), Gy, U, E.Le.dd(RD.Int.mag(yl), RD.Nat.pow2(Ey), hyl), hGy)
      +hL3 : {RD.Nat.lt(Nat.mul(3n, U), Nat.double(RD.Int.mag(I.Int.add(xl, yl)))) == False{} : Bool} = E.Le.trans(Nat.double(RD.Int.mag(I.Int.add(xl, yl))), Nat.add(Nat.double(U), U), Nat.mul(3n, U),
        Dbl.tri(xl, yl, Nat.double(U), U, E.Le.dd(RD.Int.mag(xl), U, hx), hy2),
        E.Le.eq(Nat.add(Nat.double(U), U), Nat.mul(3n, U), R.NatN.eq2([U, Nat.double(U)], R.Ad(R.V(1n), R.V(0n)), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{}))), [], [], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n))))], {==}, Unit{},
          (R.NatN.z([U, Nat.double(U)], R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, Y.Nat.double_add(U)), Unit{}), {==}, {==})))
      F2a1(p1, q, I.IPos{X}, xl, I.Int.neg(I.IPos{Yv}), yl, hp, h4U, E.Le.trans(RD.Int.mag(s), d, Nat.mul(m2, U), E.Le.eq(RD.Int.mag(s), d, ems), el), hx, hy2,
        MX.lo2(I.IPos{X}, xl, I.Int.neg(I.IPos{Yv}), yl, Nat.mul(U, m4), Nat.mul(3n, U), E.Le.trans(Nat.add(Nat.mul(U, m4), Nat.mul(3n, U)), Nat.mul(P, U), Nat.double(RD.Int.mag(s)), NQ.four(p1, U, hp), h2s), hL3))
    case True{}:
      AD.big.go2(p1, q, A, B, Ey, xl, yl, hp, hA1, hA, hB1, hB, hx, hyl, hEy, hyx, fx, fy, d, ems, hdX, el, RD.Nat.lt(Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), d), {==})

def AD.big(+p1: Nat, +q: Nat, +A: Nat, +B: Nat, +Ey: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hyl: {RD.Nat.lt(RD.Nat.pow2(Ey), RD.Int.mag(yl)) == False{} : Bool},
  +hEy: {RD.Nat.lt(Nat.add(1n+p1, q), Ey) == False{} : Bool}, +hyx: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey))) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat}, +h2Y: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.double(Nat.mul(B, RD.Nat.pow2(1n+Ey)))) == False{} : Bool})
  -> {RelA(p1, I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, xl, I.Int.neg(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}), yl) == False{} : Bool}:
  +P = RD.Nat.pow2(1n+p1)
  +H = RD.Nat.pow2(p1)
  +Q = RD.Nat.pow2(q)
  +U = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))
  +m1 = RD.Nat.monus(P, 1n)
  +m2 = RD.Nat.monus(P, 2n)
  +m4 = RD.Nat.monus(P, 4n)
  +X = Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))
  +Yv = Nat.mul(B, RD.Nat.pow2(1n+Ey))
  +Gy = RD.Nat.pow2(1n+Ey)
  +D = Nat.add(1n+p1, q)
  +eU : {RD.Nat.pow2(D) == U : Nat} = BP.Pow2.add(1n+p1, q)
  +hYU : {RD.Nat.lt(U, RD.Nat.pow2(Ey)) == False{} : Bool} = E.Le.trans(RD.Nat.pow2(Ey), RD.Nat.pow2(D), U, E2.Pow2.mono(Ey, D, hEy), E.Le.eq(RD.Nat.pow2(D), U, eU))
  +hyU : {RD.Nat.lt(U, RD.Int.mag(yl)) == False{} : Bool} = E.Le.trans(RD.Int.mag(yl), RD.Nat.pow2(Ey), U, hyl, hYU)
  +hONE : {RD.Nat.lt(X, Nat.mul(P, U)) == False{} : Bool} = E.Le.trans(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), X, E.Le.eq(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), BP.Mul.dbl_l(H, U)),
    E.Le.trans(Nat.double(Nat.mul(H, U)), Nat.double(Nat.mul(A, U)), X, E.Le.dd(Nat.mul(H, U), Nat.mul(A, U), E2.Le.mulr(H, A, U, hA1)), E.Le.eq(Nat.double(Nat.mul(A, U)), X, Equal.sym(Nat, X, Nat.double(Nat.mul(A, U)), R.Nat.mul_double(A, U)))))
  +hXm : {RD.Nat.lt(Nat.mul(m1, Nat.double(U)), X) == False{} : Bool} = E2.Le.mulr(A, m1, Nat.double(U), W.Lt.pm(A, P, hA))
  +hL2 : {RD.Nat.lt(Nat.double(U), RD.Int.mag(I.Int.add(xl, yl))) == False{} : Bool} = E.Le.trans(RD.Int.mag(I.Int.add(xl, yl)), Nat.add(U, U), Nat.double(U), W.Tri2(xl, yl, U, U, hx, hyU), E.Le.eq(Nat.add(U, U), Nat.double(U), Equal.sym(Nat, Nat.double(U), Nat.add(U, U), Y.Nat.double_add(U))))
  +d = RD.Nat.monus(X, Yv)
  +eXd : {X == Nat.add(Yv, d) : Nat} = E.Le.wit(Yv, X, hyx)
  +ems : {RD.Int.mag(I.Int.add(I.IPos{X}, I.Int.neg(I.IPos{Yv}))) == d : Nat} = Equal.trans(Nat, RD.Int.mag(I.Int.add(I.IPos{X}, I.Int.neg(I.IPos{Yv}))), E.Dist(X, Yv), d, E.Mag.diff(X, Yv),
    Equal.trans(Nat, E.Dist(X, Yv), E.Dist(Nat.add(Yv, d), Yv), d, Equal.cong(Nat, Nat, v => E.Dist(v, Yv), X, Nat.add(Yv, d), eXd), E.Dist.dn(Yv, d)))
  +hdX : {RD.Nat.lt(X, d) == False{} : Bool} = E.Le.trans(d, Nat.add(Yv, d), X, E.Le.trans(d, Nat.add(d, Yv), Nat.add(Yv, d), E.Le.add(d, Yv), E.Le.eq(Nat.add(d, Yv), Nat.add(Yv, d), NL.Nat.add_comm(d, Yv))), E.Le.eq(Nat.add(Yv, d), X, Equal.sym(Nat, X, Nat.add(Yv, d), eXd)))
  # 2Y <= X = Y + d: Y <= d, X <= 2d
  +hYd : {RD.Nat.lt(d, Yv) == False{} : Bool} = E2.Le.canl(Yv, Yv, d, E.Le.trans(Nat.add(Yv, Yv), Nat.double(Yv), Nat.add(Yv, d), E.Le.eq(Nat.add(Yv, Yv), Nat.double(Yv), Equal.sym(Nat, Nat.double(Yv), Nat.add(Yv, Yv), Y.Nat.double_add(Yv))),
    E.Le.trans(Nat.double(Yv), X, Nat.add(Yv, d), h2Y, E.Le.eq(X, Nat.add(Yv, d), eXd))))
  +hX2 : {RD.Nat.lt(Nat.double(d), X) == False{} : Bool} = E.Le.trans(X, Nat.add(d, d), Nat.double(d), E.Le.trans(X, Nat.add(Yv, d), Nat.add(d, d), E.Le.eq(X, Nat.add(Yv, d), eXd), E2.Le.addr(Yv, d, d, hYd)),
    E.Le.eq(Nat.add(d, d), Nat.double(d), Equal.sym(Nat, Nat.double(d), Nat.add(d, d), Y.Nat.double_add(d))))
  # Y < 2^p U, so 2^(1+Ey) < 2U: 2^(1+Ey) <= U
  +posU : {RD.Nat.lt(0n, Nat.double(U)) == True{} : Bool} = E2.Lt.le_trans(0n, 1n, Nat.double(U), {==}, E.Le.trans(1n, U, Nat.double(U), E.Le.trans(1n, RD.Nat.pow2(D), U, E2.Le.one(D), E.Le.eq(RD.Nat.pow2(D), U, eU)), E2.Le.dbl(U)))
  +eP1 : {P == 1n+m1 : Nat} = W.Lt.pos(H, P, E2.Lt.dself(H, BP.Pow2.pos(p1)))
  +hm1P : {RD.Nat.lt(m1, P) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(m1, P), RD.Nat.lt(m1, 1n+m1), True{}, Equal.cong(Nat, Bool, v => RD.Nat.lt(m1, v), P, 1n+m1, eP1), E2.Lt.succ(m1))
  +hm1 : {RD.Nat.lt(Nat.mul(m1, Nat.double(U)), Nat.mul(P, Nat.double(U))) == True{} : Bool} = E.Lt.mono(m1, P, Nat.double(U), hm1P, posU)
  +ePU : {Nat.mul(P, Nat.double(U)) == Nat.double(Nat.mul(P, U)) : Nat} = R.Nat.mul_double(P, U)
  +hY2 : {RD.Nat.lt(Nat.double(Yv), Nat.double(Nat.mul(P, U))) == True{} : Bool} = E2.Le.lt_trans(Nat.double(Yv), Nat.mul(m1, Nat.double(U)), Nat.double(Nat.mul(P, U)),
    E.Le.trans(Nat.double(Yv), X, Nat.mul(m1, Nat.double(U)), h2Y, hXm),
    Equal.trans(Bool, RD.Nat.lt(Nat.mul(m1, Nat.double(U)), Nat.double(Nat.mul(P, U))), RD.Nat.lt(Nat.mul(m1, Nat.double(U)), Nat.mul(P, Nat.double(U))), True{},
      Equal.cong(Nat, Bool, v => RD.Nat.lt(Nat.mul(m1, Nat.double(U)), v), Nat.double(Nat.mul(P, U)), Nat.mul(P, Nat.double(U)), Equal.sym(Nat, Nat.mul(P, Nat.double(U)), Nat.double(Nat.mul(P, U)), ePU)), hm1))
  +hY : {RD.Nat.lt(Yv, Nat.mul(P, U)) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Yv, Nat.mul(P, U)), RD.Nat.lt(Nat.double(Yv), Nat.double(Nat.mul(P, U))), True{}, Equal.sym(Bool, RD.Nat.lt(Nat.double(Yv), Nat.double(Nat.mul(P, U))), RD.Nat.lt(Yv, Nat.mul(P, U)), E.Lt.dd(Yv, Nat.mul(P, U))), hY2)
  +eHU : {Nat.mul(P, U) == Nat.mul(H, Nat.double(U)) : Nat} = Equal.trans(Nat, Nat.mul(P, U), Nat.double(Nat.mul(H, U)), Nat.mul(H, Nat.double(U)), BP.Mul.dbl_l(H, U), Equal.sym(Nat, Nat.mul(H, Nat.double(U)), Nat.double(Nat.mul(H, U)), R.Nat.mul_double(H, U)))
  +hHG : {RD.Nat.lt(Nat.mul(Gy, H), Nat.mul(Nat.double(U), H)) == True{} : Bool} = E2.Le.lt_trans(Nat.mul(Gy, H), Yv, Nat.mul(Nat.double(U), H),
    E.Le.trans(Nat.mul(Gy, H), Nat.mul(H, Gy), Yv, E.Le.eq(Nat.mul(Gy, H), Nat.mul(H, Gy), NL.Nat.mul_comm(Gy, H)), E2.Le.mulr(H, B, Gy, hB1)),
    Equal.trans(Bool, RD.Nat.lt(Yv, Nat.mul(Nat.double(U), H)), RD.Nat.lt(Yv, Nat.mul(P, U)), True{},
      Equal.cong(Nat, Bool, v => RD.Nat.lt(Yv, v), Nat.mul(Nat.double(U), H), Nat.mul(P, U), Equal.trans(Nat, Nat.mul(Nat.double(U), H), Nat.mul(H, Nat.double(U)), Nat.mul(P, U), NL.Nat.mul_comm(Nat.double(U), H), Equal.sym(Nat, Nat.mul(P, U), Nat.mul(H, Nat.double(U)), eHU))), hY))
  +hGU2 : {RD.Nat.lt(Gy, Nat.double(U)) == True{} : Bool} = E.Lt.cancel(Gy, Nat.double(U), H, hHG)
  +hEyD : {RD.Nat.lt(1n+Ey, 1n+D) == True{} : Bool} = Pow2.rev(1n+Ey, 1n+D, Equal.trans(Bool, RD.Nat.lt(Gy, Nat.double(RD.Nat.pow2(D))), RD.Nat.lt(Gy, Nat.double(U)), True{},
    Equal.cong(Nat, Bool, v => RD.Nat.lt(Gy, Nat.double(v)), RD.Nat.pow2(D), U, eU), hGU2))
  +hGy : {RD.Nat.lt(U, Gy) == False{} : Bool} = E.Le.trans(Gy, RD.Nat.pow2(D), U, E2.Pow2.mono(1n+Ey, D, E2.Le.succ(Ey, D, hEyD)), E.Le.eq(RD.Nat.pow2(D), U, eU))
  AD.big.go1(p1, q, A, B, Ey, xl, yl, hp, hA1, hA, hB1, hB, hx, hyl, hEy, hyx, fx, fy, d, ems, hdX, hX2, hGy, RD.Nat.lt(Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 2n), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))), d), {==})

# yh < 0, xh < 2 |yh| < 2 xh: case 1 (Sterbenz)
def AD.c1(+p1: Nat, +q: Nat, +A: Nat, +B: Nat, +Ey: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hyl: {RD.Nat.lt(RD.Nat.pow2(Ey), RD.Int.mag(yl)) == False{} : Bool},
  +hEy: {RD.Nat.lt(Nat.add(1n+p1, q), Ey) == False{} : Bool}, +hyx: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey))) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat}, +h2Y: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.double(Nat.mul(B, RD.Nat.pow2(1n+Ey)))) == True{} : Bool}, +hYX: {RD.Nat.lt(Nat.mul(B, RD.Nat.pow2(1n+Ey)), Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))) == True{} : Bool})
  -> {RelA(p1, I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, xl, I.Int.neg(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}), yl) == False{} : Bool}:
  +P = RD.Nat.pow2(1n+p1)
  +H = RD.Nat.pow2(p1)
  +Q = RD.Nat.pow2(q)
  +U = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))
  +m1 = RD.Nat.monus(P, 1n)
  +m2 = RD.Nat.monus(P, 2n)
  +m4 = RD.Nat.monus(P, 4n)
  +X = Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))
  +Yv = Nat.mul(B, RD.Nat.pow2(1n+Ey))
  +Gy = RD.Nat.pow2(1n+Ey)
  +D = Nat.add(1n+p1, q)
  +eU : {RD.Nat.pow2(D) == U : Nat} = BP.Pow2.add(1n+p1, q)
  +hYU : {RD.Nat.lt(U, RD.Nat.pow2(Ey)) == False{} : Bool} = E.Le.trans(RD.Nat.pow2(Ey), RD.Nat.pow2(D), U, E2.Pow2.mono(Ey, D, hEy), E.Le.eq(RD.Nat.pow2(D), U, eU))
  +hyU : {RD.Nat.lt(U, RD.Int.mag(yl)) == False{} : Bool} = E.Le.trans(RD.Int.mag(yl), RD.Nat.pow2(Ey), U, hyl, hYU)
  +hONE : {RD.Nat.lt(X, Nat.mul(P, U)) == False{} : Bool} = E.Le.trans(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), X, E.Le.eq(Nat.mul(P, U), Nat.double(Nat.mul(H, U)), BP.Mul.dbl_l(H, U)),
    E.Le.trans(Nat.double(Nat.mul(H, U)), Nat.double(Nat.mul(A, U)), X, E.Le.dd(Nat.mul(H, U), Nat.mul(A, U), E2.Le.mulr(H, A, U, hA1)), E.Le.eq(Nat.double(Nat.mul(A, U)), X, Equal.sym(Nat, X, Nat.double(Nat.mul(A, U)), R.Nat.mul_double(A, U)))))
  +hXm : {RD.Nat.lt(Nat.mul(m1, Nat.double(U)), X) == False{} : Bool} = E2.Le.mulr(A, m1, Nat.double(U), W.Lt.pm(A, P, hA))
  +hL2 : {RD.Nat.lt(Nat.double(U), RD.Int.mag(I.Int.add(xl, yl))) == False{} : Bool} = E.Le.trans(RD.Int.mag(I.Int.add(xl, yl)), Nat.add(U, U), Nat.double(U), W.Tri2(xl, yl, U, U, hx, hyU), E.Le.eq(Nat.add(U, U), Nat.double(U), Equal.sym(Nat, Nat.double(U), Nat.add(U, U), Y.Nat.double_add(U))))
  +d = RD.Nat.monus(X, Yv)
  +eXd : {X == Nat.add(Yv, d) : Nat} = E.Le.wit(Yv, X, hyx)
  +hsp : {I.Int.add(I.IPos{X}, I.Int.neg(I.IPos{Yv})) == I.IPos{d} : I.Int} = Equal.trans(I.Int, I.Int.add(I.IPos{X}, I.Int.neg(I.IPos{Yv})), I.Int.add(I.IPos{Nat.add(Yv, d)}, I.Int.neg(I.IPos{Yv})), I.IPos{d},
    Equal.cong(Nat, I.Int, v => I.Int.add(I.IPos{v}, I.Int.neg(I.IPos{Yv})), X, Nat.add(Yv, d), eXd),
    BP.IntN([I.IPos{Yv}, I.IPos{d}], R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(0n))), R.V(1n), [], [], {==}, Unit{}))
  +eXA : {X == Nat.mul(A, RD.Nat.pow2(1n+D)) : Nat} = Equal.cong(Nat, Nat, v => Nat.mul(A, Nat.double(v)), U, RD.Nat.pow2(D), Equal.sym(Nat, RD.Nat.pow2(D), U, eU))
  +fX : {E.Rn(1n+p1, X) == X : Nat} = W.Rn.fix(p1, X, A, 1n+D, eXA, E2.Lt.to_le(A, P, hA))
  +fY : {E.Rn(1n+p1, Yv) == Yv : Nat} = W.Rn.fix(p1, Yv, B, 1n+Ey, {==}, E2.Lt.to_le(B, P, hB))
  +fS : {E.Rn(1n+p1, d) == d : Nat} = E.Sterbenz(p1, X, Yv, d, eXd, E2.Lt.to_le(X, Nat.double(Yv), h2Y), fX, fY)
  +posd : {RD.Nat.lt(0n, d) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(0n, d), RD.Nat.lt(Nat.add(Yv, 0n), Nat.add(Yv, d)), True{}, Equal.sym(Bool, RD.Nat.lt(Nat.add(Yv, 0n), Nat.add(Yv, d)), RD.Nat.lt(0n, d), BP.Lt.shift(Yv, 0n, d)),
    Equal.trans(Bool, RD.Nat.lt(Nat.add(Yv, 0n), Nat.add(Yv, d)), RD.Nat.lt(Yv, X), True{},
      Equal.trans(Bool, RD.Nat.lt(Nat.add(Yv, 0n), Nat.add(Yv, d)), RD.Nat.lt(Yv, Nat.add(Yv, d)), RD.Nat.lt(Yv, X), Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.add(Yv, d)), Nat.add(Yv, 0n), Yv, NL.Nat.add_zero_r(Yv)),
        Equal.cong(Nat, Bool, v => RD.Nat.lt(Yv, v), Nat.add(Yv, d), X, Equal.sym(Nat, X, Nat.add(Yv, d), eXd))), hYX))
  # U <= G: 2^p U <= X < 2Y < 2^(p+1) G
  +posGy : {RD.Nat.lt(0n, Gy) == True{} : Bool} = BP.Pow2.pos(1n+Ey)
  +hYP : {RD.Nat.lt(Yv, Nat.mul(P, Gy)) == True{} : Bool} = E.Lt.mono(B, P, Gy, hB, posGy)
  +hXP : {RD.Nat.lt(Nat.mul(P, U), Nat.mul(P, Nat.double(Gy))) == True{} : Bool} = E2.Le.lt_trans(Nat.mul(P, U), X, Nat.mul(P, Nat.double(Gy)), hONE,
    E2.Lt.le_trans(X, Nat.double(Yv), Nat.mul(P, Nat.double(Gy)), h2Y, E.Le.trans(Nat.double(Yv), Nat.double(Nat.mul(P, Gy)), Nat.mul(P, Nat.double(Gy)), E.Le.dd(Yv, Nat.mul(P, Gy), E2.Lt.to_le(Yv, Nat.mul(P, Gy), hYP)),
      E.Le.eq(Nat.double(Nat.mul(P, Gy)), Nat.mul(P, Nat.double(Gy)), Equal.sym(Nat, Nat.mul(P, Nat.double(Gy)), Nat.double(Nat.mul(P, Gy)), R.Nat.mul_double(P, Gy))))))
  +hU2G : {RD.Nat.lt(U, Nat.double(Gy)) == True{} : Bool} = E.Lt.cancel(U, Nat.double(Gy), P, Equal.trans(Bool, RD.Nat.lt(Nat.mul(U, P), Nat.mul(Nat.double(Gy), P)), RD.Nat.lt(Nat.mul(P, U), Nat.mul(P, Nat.double(Gy))), True{},
    Equal.trans(Bool, RD.Nat.lt(Nat.mul(U, P), Nat.mul(Nat.double(Gy), P)), RD.Nat.lt(Nat.mul(P, U), Nat.mul(Nat.double(Gy), P)), RD.Nat.lt(Nat.mul(P, U), Nat.mul(P, Nat.double(Gy))),
      Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.mul(Nat.double(Gy), P)), Nat.mul(U, P), Nat.mul(P, U), NL.Nat.mul_comm(U, P)),
      Equal.cong(Nat, Bool, v => RD.Nat.lt(Nat.mul(P, U), v), Nat.mul(Nat.double(Gy), P), Nat.mul(P, Nat.double(Gy)), NL.Nat.mul_comm(Nat.double(Gy), P))), hXP))
  +hD : {RD.Nat.lt(D, 2n+Ey) == True{} : Bool} = Pow2.rev(D, 2n+Ey, Equal.trans(Bool, RD.Nat.lt(RD.Nat.pow2(D), Nat.double(Gy)), RD.Nat.lt(U, Nat.double(Gy)), True{}, Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.double(Gy)), RD.Nat.pow2(D), U, eU), hU2G))
  +hD1 : {RD.Nat.lt(1n+Ey, D) == False{} : Bool} = E2.Le.of_lt1(D, 1n+Ey, hD)
  +hUG : {RD.Nat.lt(Gy, U) == False{} : Bool} = E.Le.trans(U, RD.Nat.pow2(D), Gy, E.Le.eq(U, RD.Nat.pow2(D), Equal.sym(Nat, RD.Nat.pow2(D), U, eU)), E2.Pow2.mono(D, 1n+Ey, hD1))
  # G = 2^(1+Ey) = 2^p 2^gq, X = (A 2^j) G
  +gq = RD.Nat.monus(1n+Ey, 1n+p1)
  +eE : {1n+Ey == Nat.add(1n+p1, gq) : Nat} = E.Le.wit(1n+p1, 1n+Ey, E.Le.trans(1n+p1, D, 1n+Ey, E.Le.add(1n+p1, q), hD1))
  +G = Nat.mul(P, RD.Nat.pow2(gq))
  +eG : {Gy == G : Nat} = Equal.trans(Nat, Gy, RD.Nat.pow2(Nat.add(1n+p1, gq)), G, Equal.cong(Nat, Nat, v => RD.Nat.pow2(v), 1n+Ey, Nat.add(1n+p1, gq), eE), BP.Pow2.add(1n+p1, gq))
  +j = RD.Nat.monus(1n+D, 1n+Ey)
  +eD : {1n+D == Nat.add(1n+Ey, j) : Nat} = E.Le.wit(1n+Ey, 1n+D, hEy)
  +Aj = Nat.mul(A, RD.Nat.pow2(j))
  +eX2 : {X == Nat.mul(Aj, Gy) : Nat} = Equal.trans(Nat, X, Nat.mul(A, RD.Nat.pow2(1n+D)), Nat.mul(Aj, Gy), eXA,
    Equal.trans(Nat, Nat.mul(A, RD.Nat.pow2(1n+D)), Nat.mul(A, Nat.mul(Gy, RD.Nat.pow2(j))), Nat.mul(Aj, Gy),
      Equal.cong(Nat, Nat, v => Nat.mul(A, v), RD.Nat.pow2(1n+D), Nat.mul(Gy, RD.Nat.pow2(j)), Equal.trans(Nat, RD.Nat.pow2(1n+D), RD.Nat.pow2(Nat.add(1n+Ey, j)), Nat.mul(Gy, RD.Nat.pow2(j)),
        Equal.cong(Nat, Nat, v => RD.Nat.pow2(v), 1n+D, Nat.add(1n+Ey, j), eD), BP.Pow2.add(1n+Ey, j))),
      R.NatN.eq([A, Gy, RD.Nat.pow2(j)], R.Ml(R.V(0n), R.Ml(R.V(1n), R.V(2n))), R.Ml(R.Ml(R.V(0n), R.V(2n)), R.V(1n)), [], [], {==}, Unit{}, {==}, {==})))
  +ms = E.Dist(Aj, B)
  +hSm : {d == Nat.mul(ms, G) : Nat} = Equal.trans(Nat, d, E.Dist(X, Yv), Nat.mul(ms, G),
    Equal.sym(Nat, E.Dist(X, Yv), d, Equal.trans(Nat, E.Dist(X, Yv), E.Dist(Nat.add(Yv, d), Yv), d, Equal.cong(Nat, Nat, v => E.Dist(v, Yv), X, Nat.add(Yv, d), eXd), E.Dist.dn(Yv, d))),
    Equal.trans(Nat, E.Dist(X, Yv), E.Dist(Nat.mul(Aj, Gy), Yv), Nat.mul(ms, G), Equal.cong(Nat, Nat, v => E.Dist(v, Yv), X, Nat.mul(Aj, Gy), eX2),
      Equal.trans(Nat, E.Dist(Nat.mul(Aj, Gy), Yv), Nat.mul(ms, Gy), Nat.mul(ms, G), E.Dist.mul(Aj, B, Gy), Equal.cong(Nat, Nat, v => Nat.mul(ms, v), Gy, G, eG))))
  +hxG : {RD.Nat.lt(G, RD.Int.mag(xl)) == False{} : Bool} = E.Le.trans(RD.Int.mag(xl), U, G, hx, E.Le.trans(U, Gy, G, hUG, E.Le.eq(Gy, G, eG)))
  +hyG : {RD.Nat.lt(G, Nat.double(RD.Int.mag(yl))) == False{} : Bool} = E.Le.trans(Nat.double(RD.Int.mag(yl)), Gy, G, E.Le.dd(RD.Int.mag(yl), RD.Nat.pow2(Ey), hyl), E.Le.eq(Gy, G, eG))
  C1(p1, gq, I.IPos{X}, xl, I.Int.neg(I.IPos{Yv}), yl, d, ms, hp, hsp, hSm, Mul.ge(ms, G, d, hSm, posd), fS, hxG, hyG, fx, fy)

# yh = -xh: case 0
def AD.c0(+p1: Nat, +q: Nat, +A: Nat, +B: Nat, +Ey: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hyl: {RD.Nat.lt(RD.Nat.pow2(Ey), RD.Int.mag(yl)) == False{} : Bool},
  +hEy: {RD.Nat.lt(Nat.add(1n+p1, q), Ey) == False{} : Bool}, +hyx: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey))) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat}, +eXY: {Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))) == Nat.mul(B, RD.Nat.pow2(1n+Ey)) : Nat}) -> {RelA(p1, I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, xl, I.Int.neg(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}), yl) == False{} : Bool}:
  C0(p1, I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, xl, I.Int.neg(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}), yl, Equal.trans(I.Int, I.Int.add(I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, I.Int.neg(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))})), I.Int.add(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}, I.Int.neg(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))})), I.IPos{0n},
    Equal.cong(Nat, I.Int, v => I.Int.add(I.IPos{v}, I.Int.neg(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))})), Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey)), eXY), BP.IntN([I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}], R.Ad(R.V(0n), R.Ng(R.V(0n))), N.TZero{}, [], [], {==}, Unit{})), fx, fy)

def AD.neg.go2(+p1: Nat, +q: Nat, +A: Nat, +B: Nat, +Ey: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hyl: {RD.Nat.lt(RD.Nat.pow2(Ey), RD.Int.mag(yl)) == False{} : Bool},
  +hEy: {RD.Nat.lt(Nat.add(1n+p1, q), Ey) == False{} : Bool}, +hyx: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey))) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat}, +h2Y: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.double(Nat.mul(B, RD.Nat.pow2(1n+Ey)))) == True{} : Bool}, l: Bool, +el: {RD.Nat.lt(Nat.mul(B, RD.Nat.pow2(1n+Ey)), Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))) == l : Bool})
  -> {RelA(p1, I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, xl, I.Int.neg(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}), yl) == False{} : Bool}:
  match l:
    case True{}:
      AD.c1(p1, q, A, B, Ey, xl, yl, hp, hA1, hA, hB1, hB, hx, hyl, hEy, hyx, fx, fy, h2Y, el)
    case False{}:
      AD.c0(p1, q, A, B, Ey, xl, yl, hp, hA1, hA, hB1, hB, hx, hyl, hEy, hyx, fx, fy, E2.Le.anti(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey)), el, hyx))

def AD.neg.go1(+p1: Nat, +q: Nat, +A: Nat, +B: Nat, +Ey: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hyl: {RD.Nat.lt(RD.Nat.pow2(Ey), RD.Int.mag(yl)) == False{} : Bool},
  +hEy: {RD.Nat.lt(Nat.add(1n+p1, q), Ey) == False{} : Bool}, +hyx: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey))) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat}, l: Bool, +el: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.double(Nat.mul(B, RD.Nat.pow2(1n+Ey)))) == l : Bool})
  -> {RelA(p1, I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, xl, I.Int.neg(I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}), yl) == False{} : Bool}:
  match l:
    case False{}:
      AD.big(p1, q, A, B, Ey, xl, yl, hp, hA1, hA, hB1, hB, hx, hyl, hEy, hyx, fx, fy, el)
    case True{}:
      AD.neg.go2(p1, q, A, B, Ey, xl, yl, hp, hA1, hA, hB1, hB, hx, hyl, hEy, hyx, fx, fy, el, RD.Nat.lt(Nat.mul(B, RD.Nat.pow2(1n+Ey)), Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))), {==})

# xh = A 2u > 0, yh = +-B 2^(1+Ey), |yh| <= xh: the relative bound
def AD.core(+p1: Nat, +q: Nat, +A: Nat, +B: Nat, +Ey: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)), RD.Int.mag(xl)) == False{} : Bool}, +hyl: {RD.Nat.lt(RD.Nat.pow2(Ey), RD.Int.mag(yl)) == False{} : Bool},
  +hEy: {RD.Nat.lt(Nat.add(1n+p1, q), Ey) == False{} : Bool}, +hyx: {RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.mul(B, RD.Nat.pow2(1n+Ey))) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat}, sy: Bool) -> {RelA(p1, I.IPos{Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q))))}, xl, W.Sg(sy, I.IPos{Nat.mul(B, RD.Nat.pow2(1n+Ey))}), yl) == False{} : Bool}:
  match sy:
    case False{}:
      AD.pos(p1, q, A, B, Ey, xl, yl, hp, hA1, hA, hB1, hB, hx, hyl, hEy, hyx, fx, fy)
    case True{}:
      AD.neg.go1(p1, q, A, B, Ey, xl, yl, hp, hA1, hA, hB1, hB, hx, hyl, hEy, hyx, fx, fy, RD.Nat.lt(Nat.mul(A, Nat.double(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(q)))), Nat.double(Nat.mul(B, RD.Nat.pow2(1n+Ey)))), {==})


# Any signs, order and scale
# --------------------------
# Negating both operands negates every step, swapping them changes no step,
# and scaling both by 2^j scales every step: the relative error is that of
# xh > 0, |yh| <= xh at a scale with u² an integer.

def Neg.A(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int)
  -> {A.eta(p, I.Int.neg(xh), I.Int.neg(xl), I.Int.neg(yh), I.Int.neg(yl)) == I.Int.neg(A.eta(p, xh, xl, yh, yl)) : I.Int}:
  +nxh = I.Int.neg(xh)
  +nxl = I.Int.neg(xl)
  +nyh = I.Int.neg(yh)
  +nyl = I.Int.neg(yl)
  +sh = A.sh(p, xh, yh)
  +sl = A.sl(p, xh, yh)
  +th = A.th(p, xl, yl)
  +tl = A.tl(p, xl, yl)
  +c = A.c(p, xh, xl, yh, yl)
  +vh = A.vh(p, xh, xl, yh, yl)
  +vl = A.vl(p, xh, xl, yh, yl)
  +w = A.w(p, xh, xl, yh, yl)
  +esh : {A.sh(p, nxh, nyh) == I.Int.neg(sh) : I.Int} = E2.RNi.nadd(p, xh, yh)
  +eth : {A.th(p, nxl, nyl) == I.Int.neg(th) : I.Int} = E2.RNi.nadd(p, xl, yl)
  +env : List<&2, I.Int> = [xh, yh, sh, xl, yl, th]
  +esl : {A.sl(p, nxh, nyh) == I.Int.neg(sl) : I.Int} = Equal.trans(I.Int, A.sl(p, nxh, nyh), I.Int.add(I.Int.add(nxh, nyh), I.Int.neg(I.Int.neg(sh))), I.Int.neg(sl),
    Equal.cong(I.Int, I.Int, v => I.Int.add(I.Int.add(nxh, nyh), I.Int.neg(v)), A.sh(p, nxh, nyh), I.Int.neg(sh), esh),
    BP.IntN(env, R.Ad(R.Ad(R.Ng(R.V(0n)), R.Ng(R.V(1n))), R.Ng(R.Ng(R.V(2n)))), R.Ng(R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(2n)))), [], [], {==}, Unit{}))
  +etl : {A.tl(p, nxl, nyl) == I.Int.neg(tl) : I.Int} = Equal.trans(I.Int, A.tl(p, nxl, nyl), I.Int.add(I.Int.add(nxl, nyl), I.Int.neg(I.Int.neg(th))), I.Int.neg(tl),
    Equal.cong(I.Int, I.Int, v => I.Int.add(I.Int.add(nxl, nyl), I.Int.neg(v)), A.th(p, nxl, nyl), I.Int.neg(th), eth),
    BP.IntN(env, R.Ad(R.Ad(R.Ng(R.V(3n)), R.Ng(R.V(4n))), R.Ng(R.Ng(R.V(5n)))), R.Ng(R.Ad(R.Ad(R.V(3n), R.V(4n)), R.Ng(R.V(5n)))), [], [], {==}, Unit{}))
  +ec : {A.c(p, nxh, nxl, nyh, nyl) == I.Int.neg(c) : I.Int} = Equal.trans(I.Int, A.c(p, nxh, nxl, nyh, nyl), E.RNi(p, I.Int.add(I.Int.neg(sl), I.Int.neg(th))), I.Int.neg(c),
    Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(A.sl(p, nxh, nyh), A.th(p, nxl, nyl)), I.Int.add(I.Int.neg(sl), I.Int.neg(th)), Y.Int.cong2(A.sl(p, nxh, nyh), I.Int.neg(sl), A.th(p, nxl, nyl), I.Int.neg(th), esl, eth)),
    E2.RNi.nadd(p, sl, th))
  +evh : {A.vh(p, nxh, nxl, nyh, nyl) == I.Int.neg(vh) : I.Int} = Equal.trans(I.Int, A.vh(p, nxh, nxl, nyh, nyl), E.F2.s(p, I.Int.neg(sh), I.Int.neg(c)), I.Int.neg(vh),
    Equal.trans(I.Int, A.vh(p, nxh, nxl, nyh, nyl), E.F2.s(p, I.Int.neg(sh), A.c(p, nxh, nxl, nyh, nyl)), E.F2.s(p, I.Int.neg(sh), I.Int.neg(c)),
      Equal.cong(I.Int, I.Int, v => E.F2.s(p, v, A.c(p, nxh, nxl, nyh, nyl)), A.sh(p, nxh, nyh), I.Int.neg(sh), esh), Equal.cong(I.Int, I.Int, v => E.F2.s(p, I.Int.neg(sh), v), A.c(p, nxh, nxl, nyh, nyl), I.Int.neg(c), ec)),
    E.F2.sym.s(p, sh, c))
  +evl : {A.vl(p, nxh, nxl, nyh, nyl) == I.Int.neg(vl) : I.Int} = Equal.trans(I.Int, A.vl(p, nxh, nxl, nyh, nyl), E.F2.t(p, I.Int.neg(sh), I.Int.neg(c)), I.Int.neg(vl),
    Equal.trans(I.Int, A.vl(p, nxh, nxl, nyh, nyl), E.F2.t(p, I.Int.neg(sh), A.c(p, nxh, nxl, nyh, nyl)), E.F2.t(p, I.Int.neg(sh), I.Int.neg(c)),
      Equal.cong(I.Int, I.Int, v => E.F2.t(p, v, A.c(p, nxh, nxl, nyh, nyl)), A.sh(p, nxh, nyh), I.Int.neg(sh), esh), Equal.cong(I.Int, I.Int, v => E.F2.t(p, I.Int.neg(sh), v), A.c(p, nxh, nxl, nyh, nyl), I.Int.neg(c), ec)),
    E.F2.sym.t(p, sh, c))
  +ew : {A.w(p, nxh, nxl, nyh, nyl) == I.Int.neg(w) : I.Int} = Equal.trans(I.Int, A.w(p, nxh, nxl, nyh, nyl), E.RNi(p, I.Int.add(I.Int.neg(tl), I.Int.neg(vl))), I.Int.neg(w),
    Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(A.tl(p, nxl, nyl), A.vl(p, nxh, nxl, nyh, nyl)), I.Int.add(I.Int.neg(tl), I.Int.neg(vl)), Y.Int.cong2(A.tl(p, nxl, nyl), I.Int.neg(tl), A.vl(p, nxh, nxl, nyh, nyl), I.Int.neg(vl), etl, evl)),
    E2.RNi.nadd(p, tl, vl))
  +s2 = E.F2.s(p, vh, w)
  +t2 = E.F2.t(p, vh, w)
  +vhn = A.vh(p, nxh, nxl, nyh, nyl)
  +wn = A.w(p, nxh, nxl, nyh, nyl)
  +ez : {A.z(p, nxh, nxl, nyh, nyl) == I.Int.add(I.Int.neg(s2), I.Int.neg(t2)) : I.Int} = Y.Int.cong2(E.F2.s(p, vhn, wn), I.Int.neg(s2), E.F2.t(p, vhn, wn), I.Int.neg(t2),
    Equal.trans(I.Int, E.F2.s(p, vhn, wn), E.F2.s(p, I.Int.neg(vh), I.Int.neg(w)), I.Int.neg(s2),
      Equal.trans(I.Int, E.F2.s(p, vhn, wn), E.F2.s(p, I.Int.neg(vh), wn), E.F2.s(p, I.Int.neg(vh), I.Int.neg(w)), Equal.cong(I.Int, I.Int, v => E.F2.s(p, v, wn), vhn, I.Int.neg(vh), evh), Equal.cong(I.Int, I.Int, v => E.F2.s(p, I.Int.neg(vh), v), wn, I.Int.neg(w), ew)),
      E.F2.sym.s(p, vh, w)),
    Equal.trans(I.Int, E.F2.t(p, vhn, wn), E.F2.t(p, I.Int.neg(vh), I.Int.neg(w)), I.Int.neg(t2),
      Equal.trans(I.Int, E.F2.t(p, vhn, wn), E.F2.t(p, I.Int.neg(vh), wn), E.F2.t(p, I.Int.neg(vh), I.Int.neg(w)), Equal.cong(I.Int, I.Int, v => E.F2.t(p, v, wn), vhn, I.Int.neg(vh), evh), Equal.cong(I.Int, I.Int, v => E.F2.t(p, I.Int.neg(vh), v), wn, I.Int.neg(w), ew)),
      E.F2.sym.t(p, vh, w)))
  +enve : List<&2, I.Int> = [s2, t2, xh, xl, yh, yl]
  Equal.trans(I.Int, A.eta(p, nxh, nxl, nyh, nyl), I.Int.add(I.Int.add(I.Int.neg(s2), I.Int.neg(t2)), I.Int.neg(I.Int.add(I.Int.add(nxh, nxl), I.Int.add(nyh, nyl)))), I.Int.neg(A.eta(p, xh, xl, yh, yl)),
    Equal.cong(I.Int, I.Int, v => I.Int.add(v, I.Int.neg(I.Int.add(I.Int.add(nxh, nxl), I.Int.add(nyh, nyl)))), A.z(p, nxh, nxl, nyh, nyl), I.Int.add(I.Int.neg(s2), I.Int.neg(t2)), ez),
    BP.IntN(enve, R.Ad(R.Ad(R.Ng(R.V(0n)), R.Ng(R.V(1n))), R.Ng(R.Ad(R.Ad(R.Ng(R.V(2n)), R.Ng(R.V(3n))), R.Ad(R.Ng(R.V(4n)), R.Ng(R.V(5n)))))),
      R.Ng(R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.Ad(R.Ad(R.V(2n), R.V(3n)), R.Ad(R.V(4n), R.V(5n)))))), [], [], {==}, Unit{}))

def Neg.relA(+p1: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int)
  -> {RelA(p1, I.Int.neg(xh), I.Int.neg(xl), I.Int.neg(yh), I.Int.neg(yl)) == RelA(p1, xh, xl, yh, yl) : Bool}:
  +X = I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl))
  +Xn = I.Int.add(I.Int.add(I.Int.neg(xh), I.Int.neg(xl)), I.Int.add(I.Int.neg(yh), I.Int.neg(yl)))
  +K = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n))
  +en = A.eta(1n+p1, I.Int.neg(xh), I.Int.neg(xl), I.Int.neg(yh), I.Int.neg(yl))
  +e = A.eta(1n+p1, xh, xl, yh, yl)
  +env : List<&2, I.Int> = [xh, xl, yh, yl]
  +eX : {RD.Int.mag(Xn) == RD.Int.mag(X) : Nat} = Equal.trans(Nat, RD.Int.mag(Xn), RD.Int.mag(I.Int.neg(X)), RD.Int.mag(X),
    Equal.cong(I.Int, Nat, v => RD.Int.mag(v), Xn, I.Int.neg(X), BP.IntN(env, R.Ad(R.Ad(R.Ng(R.V(0n)), R.Ng(R.V(1n))), R.Ad(R.Ng(R.V(2n)), R.Ng(R.V(3n)))), R.Ng(R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(2n), R.V(3n)))), [], [], {==}, Unit{})),
    E.Mag.neg(X))
  +ee : {RD.Int.mag(en) == RD.Int.mag(e) : Nat} = Equal.trans(Nat, RD.Int.mag(en), RD.Int.mag(I.Int.neg(e)), RD.Int.mag(e), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), en, I.Int.neg(e), Neg.A(1n+p1, xh, xl, yh, yl)), E.Mag.neg(e))
  Equal.trans(Bool, RelA(p1, I.Int.neg(xh), I.Int.neg(xl), I.Int.neg(yh), I.Int.neg(yl)), RD.Nat.lt(Nat.mul(3n, RD.Int.mag(X)), Nat.mul(RD.Int.mag(en), K)), RelA(p1, xh, xl, yh, yl),
    Equal.cong(Nat, Bool, v => RD.Nat.lt(Nat.mul(3n, v), Nat.mul(RD.Int.mag(en), K)), RD.Int.mag(Xn), RD.Int.mag(X), eX),
    Equal.cong(Nat, Bool, v => RD.Nat.lt(Nat.mul(3n, RD.Int.mag(X)), Nat.mul(v, K)), RD.Int.mag(en), RD.Int.mag(e), ee))


def Sym.A(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> {A.eta(p, yh, yl, xh, xl) == A.eta(p, xh, xl, yh, yl) : I.Int}:
  +sh = A.sh(p, xh, yh)
  +th = A.th(p, xl, yl)
  +sl = A.sl(p, xh, yh)
  +tl = A.tl(p, xl, yl)
  +c = A.c(p, xh, xl, yh, yl)
  +vh = A.vh(p, xh, xl, yh, yl)
  +vl = A.vl(p, xh, xl, yh, yl)
  +w = A.w(p, xh, xl, yh, yl)
  +sh2 = A.sh(p, yh, xh)
  +th2 = A.th(p, yl, xl)
  +c2 = A.c(p, yh, yl, xh, xl)
  +vh2 = A.vh(p, yh, yl, xh, xl)
  +w2 = A.w(p, yh, yl, xh, xl)
  +esh : {sh2 == sh : I.Int} = Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(yh, xh), I.Int.add(xh, yh), Z.Int.add_comm(yh, xh))
  +eth : {th2 == th : I.Int} = Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(yl, xl), I.Int.add(xl, yl), Z.Int.add_comm(yl, xl))
  +esl : {A.sl(p, yh, xh) == sl : I.Int} = Y.Int.cong2(I.Int.add(yh, xh), I.Int.add(xh, yh), I.Int.neg(sh2), I.Int.neg(sh), Z.Int.add_comm(yh, xh), Equal.cong(I.Int, I.Int, v => I.Int.neg(v), sh2, sh, esh))
  +etl : {A.tl(p, yl, xl) == tl : I.Int} = Y.Int.cong2(I.Int.add(yl, xl), I.Int.add(xl, yl), I.Int.neg(th2), I.Int.neg(th), Z.Int.add_comm(yl, xl), Equal.cong(I.Int, I.Int, v => I.Int.neg(v), th2, th, eth))
  +ec : {c2 == c : I.Int} = Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(A.sl(p, yh, xh), th2), I.Int.add(sl, th), Y.Int.cong2(A.sl(p, yh, xh), sl, th2, th, esl, eth))
  +evh : {vh2 == vh : I.Int} = Equal.trans(I.Int, vh2, E.F2.s(p, sh, c2), vh, Equal.cong(I.Int, I.Int, v => E.F2.s(p, v, c2), sh2, sh, esh), Equal.cong(I.Int, I.Int, v => E.F2.s(p, sh, v), c2, c, ec))
  +evl : {A.vl(p, yh, yl, xh, xl) == vl : I.Int} = Equal.trans(I.Int, A.vl(p, yh, yl, xh, xl), E.F2.t(p, sh, c2), vl, Equal.cong(I.Int, I.Int, v => E.F2.t(p, v, c2), sh2, sh, esh), Equal.cong(I.Int, I.Int, v => E.F2.t(p, sh, v), c2, c, ec))
  +ew : {w2 == w : I.Int} = Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(A.tl(p, yl, xl), A.vl(p, yh, yl, xh, xl)), I.Int.add(tl, vl), Y.Int.cong2(A.tl(p, yl, xl), tl, A.vl(p, yh, yl, xh, xl), vl, etl, evl))
  +ez : {A.z(p, yh, yl, xh, xl) == A.z(p, xh, xl, yh, yl) : I.Int} = Y.Int.cong2(E.F2.s(p, vh2, w2), E.F2.s(p, vh, w), E.F2.t(p, vh2, w2), E.F2.t(p, vh, w),
    Equal.trans(I.Int, E.F2.s(p, vh2, w2), E.F2.s(p, vh, w2), E.F2.s(p, vh, w), Equal.cong(I.Int, I.Int, v => E.F2.s(p, v, w2), vh2, vh, evh), Equal.cong(I.Int, I.Int, v => E.F2.s(p, vh, v), w2, w, ew)),
    Equal.trans(I.Int, E.F2.t(p, vh2, w2), E.F2.t(p, vh, w2), E.F2.t(p, vh, w), Equal.cong(I.Int, I.Int, v => E.F2.t(p, v, w2), vh2, vh, evh), Equal.cong(I.Int, I.Int, v => E.F2.t(p, vh, v), w2, w, ew)))
  +env : List<&2, I.Int> = [xh, xl, yh, yl]
  Y.Int.cong2(A.z(p, yh, yl, xh, xl), A.z(p, xh, xl, yh, yl), I.Int.neg(I.Int.add(I.Int.add(yh, yl), I.Int.add(xh, xl))), I.Int.neg(I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl))), ez,
    BP.IntN(env, R.Ng(R.Ad(R.Ad(R.V(2n), R.V(3n)), R.Ad(R.V(0n), R.V(1n)))), R.Ng(R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(2n), R.V(3n)))), [], [], {==}, Unit{}))

def Sym.relA(+p1: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> {RelA(p1, yh, yl, xh, xl) == RelA(p1, xh, xl, yh, yl) : Bool}:
  +K = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n))
  +X = I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl))
  +es = A.eta(1n+p1, yh, yl, xh, xl)
  Equal.trans(Bool, RelA(p1, yh, yl, xh, xl), RD.Nat.lt(Nat.mul(3n, RD.Int.mag(X)), Nat.mul(RD.Int.mag(es), K)), RelA(p1, xh, xl, yh, yl),
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(Nat.mul(3n, RD.Int.mag(v)), Nat.mul(RD.Int.mag(es), K)), I.Int.add(I.Int.add(yh, yl), I.Int.add(xh, xl)), X, Z.Int.add_comm(I.Int.add(yh, yl), I.Int.add(xh, xl))),
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(Nat.mul(3n, RD.Int.mag(X)), Nat.mul(RD.Int.mag(v), K)), es, A.eta(1n+p1, xh, xl, yh, yl), Sym.A(1n+p1, xh, xl, yh, yl)))

# 2^j (a + b) and 2^j a + 2^j b
def Shd(+j: Nat, +a: I.Int, +b: I.Int) -> {I.Int.add(D.Int.sh(j, a), D.Int.sh(j, b)) == D.Int.sh(j, I.Int.add(a, b)) : I.Int}:
  Equal.sym(I.Int, D.Int.sh(j, I.Int.add(a, b)), I.Int.add(D.Int.sh(j, a), D.Int.sh(j, b)), Y.Int.sh_add(j, a, b))

def Sh.A(+p: Nat, +j: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int)
  -> {A.eta(p, D.Int.sh(j, xh), D.Int.sh(j, xl), D.Int.sh(j, yh), D.Int.sh(j, yl)) == D.Int.sh(j, A.eta(p, xh, xl, yh, yl)) : I.Int}:
  +a = D.Int.sh(j, xh)
  +b = D.Int.sh(j, xl)
  +cc = D.Int.sh(j, yh)
  +dd = D.Int.sh(j, yl)
  +sh = A.sh(p, xh, yh)
  +th = A.th(p, xl, yl)
  +sl = A.sl(p, xh, yh)
  +tl = A.tl(p, xl, yl)
  +c = A.c(p, xh, xl, yh, yl)
  +vh = A.vh(p, xh, xl, yh, yl)
  +vl = A.vl(p, xh, xl, yh, yl)
  +w = A.w(p, xh, xl, yh, yl)
  +sh2 = A.sh(p, a, cc)
  +th2 = A.th(p, b, dd)
  +c2 = A.c(p, a, b, cc, dd)
  +vh2 = A.vh(p, a, b, cc, dd)
  +w2 = A.w(p, a, b, cc, dd)
  +esh : {sh2 == D.Int.sh(j, sh) : I.Int} = E2.RNi.shadd(p, j, xh, yh)
  +eth : {th2 == D.Int.sh(j, th) : I.Int} = E2.RNi.shadd(p, j, xl, yl)
  +esl : {A.sl(p, a, cc) == D.Int.sh(j, sl) : I.Int} = Equal.trans(I.Int, A.sl(p, a, cc), I.Int.add(D.Int.sh(j, I.Int.add(xh, yh)), I.Int.neg(D.Int.sh(j, sh))), D.Int.sh(j, sl),
    Y.Int.cong2(I.Int.add(a, cc), D.Int.sh(j, I.Int.add(xh, yh)), I.Int.neg(sh2), I.Int.neg(D.Int.sh(j, sh)), Shd(j, xh, yh), Equal.cong(I.Int, I.Int, v => I.Int.neg(v), sh2, D.Int.sh(j, sh), esh)),
    E2.Sh.diff(j, I.Int.add(xh, yh), sh))
  +etl : {A.tl(p, b, dd) == D.Int.sh(j, tl) : I.Int} = Equal.trans(I.Int, A.tl(p, b, dd), I.Int.add(D.Int.sh(j, I.Int.add(xl, yl)), I.Int.neg(D.Int.sh(j, th))), D.Int.sh(j, tl),
    Y.Int.cong2(I.Int.add(b, dd), D.Int.sh(j, I.Int.add(xl, yl)), I.Int.neg(th2), I.Int.neg(D.Int.sh(j, th)), Shd(j, xl, yl), Equal.cong(I.Int, I.Int, v => I.Int.neg(v), th2, D.Int.sh(j, th), eth)),
    E2.Sh.diff(j, I.Int.add(xl, yl), th))
  +ec : {c2 == D.Int.sh(j, c) : I.Int} = Equal.trans(I.Int, c2, E.RNi(p, I.Int.add(D.Int.sh(j, sl), D.Int.sh(j, th))), D.Int.sh(j, c),
    Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(A.sl(p, a, cc), th2), I.Int.add(D.Int.sh(j, sl), D.Int.sh(j, th)), Y.Int.cong2(A.sl(p, a, cc), D.Int.sh(j, sl), th2, D.Int.sh(j, th), esl, eth)),
    E2.RNi.shadd(p, j, sl, th))
  +evh : {vh2 == D.Int.sh(j, vh) : I.Int} = Equal.trans(I.Int, vh2, E.F2.s(p, D.Int.sh(j, sh), D.Int.sh(j, c)), D.Int.sh(j, vh),
    Equal.trans(I.Int, vh2, E.F2.s(p, D.Int.sh(j, sh), c2), E.F2.s(p, D.Int.sh(j, sh), D.Int.sh(j, c)), Equal.cong(I.Int, I.Int, v => E.F2.s(p, v, c2), sh2, D.Int.sh(j, sh), esh), Equal.cong(I.Int, I.Int, v => E.F2.s(p, D.Int.sh(j, sh), v), c2, D.Int.sh(j, c), ec)),
    W.F2sh.s(p, j, sh, c))
  +evl : {A.vl(p, a, b, cc, dd) == D.Int.sh(j, vl) : I.Int} = Equal.trans(I.Int, A.vl(p, a, b, cc, dd), E.F2.t(p, D.Int.sh(j, sh), D.Int.sh(j, c)), D.Int.sh(j, vl),
    Equal.trans(I.Int, A.vl(p, a, b, cc, dd), E.F2.t(p, D.Int.sh(j, sh), c2), E.F2.t(p, D.Int.sh(j, sh), D.Int.sh(j, c)), Equal.cong(I.Int, I.Int, v => E.F2.t(p, v, c2), sh2, D.Int.sh(j, sh), esh), Equal.cong(I.Int, I.Int, v => E.F2.t(p, D.Int.sh(j, sh), v), c2, D.Int.sh(j, c), ec)),
    W.F2sh.t(p, j, sh, c))
  +ew : {w2 == D.Int.sh(j, w) : I.Int} = Equal.trans(I.Int, w2, E.RNi(p, I.Int.add(D.Int.sh(j, tl), D.Int.sh(j, vl))), D.Int.sh(j, w),
    Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(A.tl(p, b, dd), A.vl(p, a, b, cc, dd)), I.Int.add(D.Int.sh(j, tl), D.Int.sh(j, vl)), Y.Int.cong2(A.tl(p, b, dd), D.Int.sh(j, tl), A.vl(p, a, b, cc, dd), D.Int.sh(j, vl), etl, evl)),
    E2.RNi.shadd(p, j, tl, vl))
  +s2 = E.F2.s(p, vh, w)
  +t2 = E.F2.t(p, vh, w)
  +ez : {A.z(p, a, b, cc, dd) == D.Int.sh(j, A.z(p, xh, xl, yh, yl)) : I.Int} = Equal.trans(I.Int, A.z(p, a, b, cc, dd), I.Int.add(D.Int.sh(j, s2), D.Int.sh(j, t2)), D.Int.sh(j, A.z(p, xh, xl, yh, yl)),
    Y.Int.cong2(E.F2.s(p, vh2, w2), D.Int.sh(j, s2), E.F2.t(p, vh2, w2), D.Int.sh(j, t2),
      Equal.trans(I.Int, E.F2.s(p, vh2, w2), E.F2.s(p, D.Int.sh(j, vh), D.Int.sh(j, w)), D.Int.sh(j, s2),
        Equal.trans(I.Int, E.F2.s(p, vh2, w2), E.F2.s(p, D.Int.sh(j, vh), w2), E.F2.s(p, D.Int.sh(j, vh), D.Int.sh(j, w)), Equal.cong(I.Int, I.Int, v => E.F2.s(p, v, w2), vh2, D.Int.sh(j, vh), evh), Equal.cong(I.Int, I.Int, v => E.F2.s(p, D.Int.sh(j, vh), v), w2, D.Int.sh(j, w), ew)),
        W.F2sh.s(p, j, vh, w)),
      Equal.trans(I.Int, E.F2.t(p, vh2, w2), E.F2.t(p, D.Int.sh(j, vh), D.Int.sh(j, w)), D.Int.sh(j, t2),
        Equal.trans(I.Int, E.F2.t(p, vh2, w2), E.F2.t(p, D.Int.sh(j, vh), w2), E.F2.t(p, D.Int.sh(j, vh), D.Int.sh(j, w)), Equal.cong(I.Int, I.Int, v => E.F2.t(p, v, w2), vh2, D.Int.sh(j, vh), evh), Equal.cong(I.Int, I.Int, v => E.F2.t(p, D.Int.sh(j, vh), v), w2, D.Int.sh(j, w), ew)),
        W.F2sh.t(p, j, vh, w))),
    Shd(j, s2, t2))
  +X = I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl))
  +eX : {I.Int.add(I.Int.add(a, b), I.Int.add(cc, dd)) == D.Int.sh(j, X) : I.Int} = Equal.trans(I.Int, I.Int.add(I.Int.add(a, b), I.Int.add(cc, dd)), I.Int.add(D.Int.sh(j, I.Int.add(xh, xl)), D.Int.sh(j, I.Int.add(yh, yl))), D.Int.sh(j, X),
    Y.Int.cong2(I.Int.add(a, b), D.Int.sh(j, I.Int.add(xh, xl)), I.Int.add(cc, dd), D.Int.sh(j, I.Int.add(yh, yl)), Shd(j, xh, xl), Shd(j, yh, yl)), Shd(j, I.Int.add(xh, xl), I.Int.add(yh, yl)))
  Equal.trans(I.Int, A.eta(p, a, b, cc, dd), I.Int.add(D.Int.sh(j, A.z(p, xh, xl, yh, yl)), I.Int.neg(D.Int.sh(j, X))), D.Int.sh(j, A.eta(p, xh, xl, yh, yl)),
    Y.Int.cong2(A.z(p, a, b, cc, dd), D.Int.sh(j, A.z(p, xh, xl, yh, yl)), I.Int.neg(I.Int.add(I.Int.add(a, b), I.Int.add(cc, dd))), I.Int.neg(D.Int.sh(j, X)), ez, Equal.cong(I.Int, I.Int, v => I.Int.neg(v), I.Int.add(I.Int.add(a, b), I.Int.add(cc, dd)), D.Int.sh(j, X), eX)),
    E2.Sh.diff(j, A.z(p, xh, xl, yh, yl), X))

def Sh.relA(+p1: Nat, +j: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int)
  -> {RelA(p1, D.Int.sh(j, xh), D.Int.sh(j, xl), D.Int.sh(j, yh), D.Int.sh(j, yl)) == RelA(p1, xh, xl, yh, yl) : Bool}:
  +a = D.Int.sh(j, xh)
  +b = D.Int.sh(j, xl)
  +cc = D.Int.sh(j, yh)
  +dd = D.Int.sh(j, yl)
  +Kj = RD.Nat.pow2(j)
  +Z = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n))
  +X = I.Int.add(I.Int.add(xh, xl), I.Int.add(yh, yl))
  +M = RD.Int.mag(X)
  +e = RD.Int.mag(A.eta(1n+p1, xh, xl, yh, yl))
  +eX : {I.Int.add(I.Int.add(a, b), I.Int.add(cc, dd)) == D.Int.sh(j, X) : I.Int} = Equal.trans(I.Int, I.Int.add(I.Int.add(a, b), I.Int.add(cc, dd)), I.Int.add(D.Int.sh(j, I.Int.add(xh, xl)), D.Int.sh(j, I.Int.add(yh, yl))), D.Int.sh(j, X),
    Y.Int.cong2(I.Int.add(a, b), D.Int.sh(j, I.Int.add(xh, xl)), I.Int.add(cc, dd), D.Int.sh(j, I.Int.add(yh, yl)), Shd(j, xh, xl), Shd(j, yh, yl)), Shd(j, I.Int.add(xh, xl), I.Int.add(yh, yl)))
  +eM : {RD.Int.mag(I.Int.add(I.Int.add(a, b), I.Int.add(cc, dd))) == Nat.mul(M, Kj) : Nat} = Equal.trans(Nat, RD.Int.mag(I.Int.add(I.Int.add(a, b), I.Int.add(cc, dd))), RD.Int.mag(D.Int.sh(j, X)), Nat.mul(M, Kj),
    Equal.cong(I.Int, Nat, v => RD.Int.mag(v), I.Int.add(I.Int.add(a, b), I.Int.add(cc, dd)), D.Int.sh(j, X), eX), E.Sh.mag(j, X))
  +ee : {RD.Int.mag(A.eta(1n+p1, a, b, cc, dd)) == Nat.mul(e, Kj) : Nat} = Equal.trans(Nat, RD.Int.mag(A.eta(1n+p1, a, b, cc, dd)), RD.Int.mag(D.Int.sh(j, A.eta(1n+p1, xh, xl, yh, yl))), Nat.mul(e, Kj),
    Equal.cong(I.Int, Nat, v => RD.Int.mag(v), A.eta(1n+p1, a, b, cc, dd), D.Int.sh(j, A.eta(1n+p1, xh, xl, yh, yl)), Sh.A(1n+p1, j, xh, xl, yh, yl)), E.Sh.mag(j, A.eta(1n+p1, xh, xl, yh, yl)))
  +env : List<&2, Nat> = [M, e, Kj, Z]
  +e1 : {Nat.mul(3n, Nat.mul(M, Kj)) == Nat.mul(Nat.mul(3n, M), Kj) : Nat} = R.NatN.eq(env, R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ad(R.Ml(R.V(0n), R.V(2n)), N.TZero{}))),
    R.Ml(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{}))), R.V(2n)), [], [], {==}, Unit{}, {==}, {==})
  +e2 : {Nat.mul(Nat.mul(e, Kj), Z) == Nat.mul(Nat.mul(e, Z), Kj) : Nat} = R.NatN.eq(env, R.Ml(R.Ml(R.V(1n), R.V(2n)), R.V(3n)), R.Ml(R.Ml(R.V(1n), R.V(3n)), R.V(2n)), [], [], {==}, Unit{}, {==}, {==})
  Equal.trans(Bool, RelA(p1, a, b, cc, dd), RD.Nat.lt(Nat.mul(Nat.mul(3n, M), Kj), Nat.mul(Nat.mul(e, Z), Kj)), RelA(p1, xh, xl, yh, yl),
    Equal.trans(Bool, RelA(p1, a, b, cc, dd), RD.Nat.lt(Nat.mul(3n, Nat.mul(M, Kj)), Nat.mul(Nat.mul(e, Kj), Z)), RD.Nat.lt(Nat.mul(Nat.mul(3n, M), Kj), Nat.mul(Nat.mul(e, Z), Kj)),
      Equal.trans(Bool, RelA(p1, a, b, cc, dd), RD.Nat.lt(Nat.mul(3n, Nat.mul(M, Kj)), Nat.mul(RD.Int.mag(A.eta(1n+p1, a, b, cc, dd)), Z)), RD.Nat.lt(Nat.mul(3n, Nat.mul(M, Kj)), Nat.mul(Nat.mul(e, Kj), Z)),
        Equal.cong(Nat, Bool, v => RD.Nat.lt(Nat.mul(3n, v), Nat.mul(RD.Int.mag(A.eta(1n+p1, a, b, cc, dd)), Z)), RD.Int.mag(I.Int.add(I.Int.add(a, b), I.Int.add(cc, dd))), Nat.mul(M, Kj), eM),
        Equal.cong(Nat, Bool, v => RD.Nat.lt(Nat.mul(3n, Nat.mul(M, Kj)), Nat.mul(v, Z)), RD.Int.mag(A.eta(1n+p1, a, b, cc, dd)), Nat.mul(e, Kj), ee)),
      Equal.trans(Bool, RD.Nat.lt(Nat.mul(3n, Nat.mul(M, Kj)), Nat.mul(Nat.mul(e, Kj), Z)), RD.Nat.lt(Nat.mul(Nat.mul(3n, M), Kj), Nat.mul(Nat.mul(e, Kj), Z)), RD.Nat.lt(Nat.mul(Nat.mul(3n, M), Kj), Nat.mul(Nat.mul(e, Z), Kj)),
        Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.mul(Nat.mul(e, Kj), Z)), Nat.mul(3n, Nat.mul(M, Kj)), Nat.mul(Nat.mul(3n, M), Kj), e1),
        Equal.cong(Nat, Bool, v => RD.Nat.lt(Nat.mul(Nat.mul(3n, M), Kj), v), Nat.mul(Nat.mul(e, Kj), Z), Nat.mul(Nat.mul(e, Z), Kj), e2))),
    P3.Lt.scale(Nat.mul(3n, M), Nat.mul(e, Z), Kj, BP.Pow2.pos(j)))


def Sg.neg(b: Bool, +z: I.Int) -> {I.Int.neg(W.Sg(b, z)) == W.Sg(Bool.not(b), z) : I.Int}:
  match b:
    case True{}:
      Z.Int.neg_neg(z)
    case False{}:
      {==}

def Sg.sh(+k: Nat, b: Bool, +z: I.Int) -> {D.Int.sh(k, W.Sg(b, z)) == W.Sg(b, D.Int.sh(k, z)) : I.Int}:
  match b:
    case True{}:
      Y.Int.sh_neg(k, z)
    case False{}:
      {==}

# xh = A 2^(1+Dx) > 0, |yh| <= xh: scale both by 2^p so that u² is an integer
def AG.pos(+p1: Nat, +sy: Bool, +A: Nat, +B: Nat, +Dx: Nat, +Dy: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(Dx), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(Dy), RD.Int.mag(yl)) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat},
  +hyx: {RD.Nat.lt(Nat.mul(A, RD.Nat.pow2(1n+Dx)), Nat.mul(B, RD.Nat.pow2(1n+Dy))) == False{} : Bool})
  -> {RelA(p1, W.XH(A, Dx), xl, W.Sg(sy, W.XH(B, Dy)), yl) == False{} : Bool}:
  +P = RD.Nat.pow2(1n+p1)
  +H = RD.Nat.pow2(p1)
  +k : Nat = 1n+p1
  +K = RD.Nat.pow2(k)
  +Ey = Nat.add(Dy, k)
  +Ex = Nat.add(Dx, k)
  +Q = RD.Nat.pow2(Dx)
  +U = Nat.mul(P, Q)
  +a = D.Int.sh(k, W.XH(A, Dx))
  +b = D.Int.sh(k, xl)
  +cc = D.Int.sh(k, W.Sg(sy, W.XH(B, Dy)))
  +dd = D.Int.sh(k, yl)
  # the scaled operands in AD.core's form
  +eKU : {RD.Nat.pow2(Ex) == U : Nat} = Equal.trans(Nat, RD.Nat.pow2(Ex), Nat.mul(Q, K), U, BP.Pow2.add(Dx, k), NL.Nat.mul_comm(Q, K))
  +Xc = Nat.mul(A, Nat.double(U))
  +ea : {a == I.IPos{Xc} : I.Int} = Equal.trans(I.Int, a, W.XH(A, Ex), I.IPos{Xc}, W.XH.sh(A, Dx, k), Equal.cong(Nat, I.Int, v => I.IPos{Nat.mul(A, Nat.double(v))}, RD.Nat.pow2(Ex), U, eKU))
  +ecc : {cc == W.Sg(sy, W.XH(B, Ey)) : I.Int} = Equal.trans(I.Int, cc, W.Sg(sy, D.Int.sh(k, W.XH(B, Dy))), W.Sg(sy, W.XH(B, Ey)), Sg.sh(k, sy, W.XH(B, Dy)),
    Equal.cong(I.Int, I.Int, v => W.Sg(sy, v), D.Int.sh(k, W.XH(B, Dy)), W.XH(B, Ey), W.XH.sh(B, Dy, k)))
  # |2^k xl| <= 2^(Dx+k) = U, |2^k yl| <= 2^Ey
  +hb : {RD.Nat.lt(U, RD.Int.mag(b)) == False{} : Bool} = E.Le.trans(RD.Int.mag(b), Nat.mul(RD.Int.mag(xl), K), U, E.Le.eq(RD.Int.mag(b), Nat.mul(RD.Int.mag(xl), K), E.Sh.mag(k, xl)),
    E.Le.trans(Nat.mul(RD.Int.mag(xl), K), Nat.mul(Q, K), U, E2.Le.mulr(RD.Int.mag(xl), Q, K, hx), E.Le.eq(Nat.mul(Q, K), U, NL.Nat.mul_comm(Q, K))))
  +hd : {RD.Nat.lt(RD.Nat.pow2(Ey), RD.Int.mag(dd)) == False{} : Bool} = E.Le.trans(RD.Int.mag(dd), Nat.mul(RD.Int.mag(yl), K), RD.Nat.pow2(Ey), E.Le.eq(RD.Int.mag(dd), Nat.mul(RD.Int.mag(yl), K), E.Sh.mag(k, yl)),
    E.Le.trans(Nat.mul(RD.Int.mag(yl), K), Nat.mul(RD.Nat.pow2(Dy), K), RD.Nat.pow2(Ey), E2.Le.mulr(RD.Int.mag(yl), RD.Nat.pow2(Dy), K, hy), E.Le.eq(Nat.mul(RD.Nat.pow2(Dy), K), RD.Nat.pow2(Ey), Equal.sym(Nat, RD.Nat.pow2(Ey), Nat.mul(RD.Nat.pow2(Dy), K), BP.Pow2.add(Dy, k)))))
  +fb : {E.Rn(k, RD.Int.mag(b)) == RD.Int.mag(b) : Nat} = E.Fn.eq(k, RD.Int.mag(b), Nat.mul(RD.Int.mag(xl), K), E.Sh.mag(k, xl), E.Fn.sc(k, RD.Int.mag(xl), k, fx))
  +fd : {E.Rn(k, RD.Int.mag(dd)) == RD.Int.mag(dd) : Nat} = E.Fn.eq(k, RD.Int.mag(dd), Nat.mul(RD.Int.mag(yl), K), E.Sh.mag(k, yl), E.Fn.sc(k, RD.Int.mag(yl), k, fy))
  # Dy <= Dx: H 2^(1+Dy) <= B 2^(1+Dy) <= A 2^(1+Dx) < 2^p 2^(1+Dx) = H 2^(2+Dx)
  +hlt : {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+Dy), H), Nat.mul(RD.Nat.pow2(2n+Dx), H)) == True{} : Bool} = E2.Le.lt_trans(Nat.mul(RD.Nat.pow2(1n+Dy), H), Nat.mul(B, RD.Nat.pow2(1n+Dy)), Nat.mul(RD.Nat.pow2(2n+Dx), H),
    E.Le.trans(Nat.mul(RD.Nat.pow2(1n+Dy), H), Nat.mul(H, RD.Nat.pow2(1n+Dy)), Nat.mul(B, RD.Nat.pow2(1n+Dy)), E.Le.eq(Nat.mul(RD.Nat.pow2(1n+Dy), H), Nat.mul(H, RD.Nat.pow2(1n+Dy)), NL.Nat.mul_comm(RD.Nat.pow2(1n+Dy), H)), E2.Le.mulr(H, B, RD.Nat.pow2(1n+Dy), hB1)),
    E2.Le.lt_trans(Nat.mul(B, RD.Nat.pow2(1n+Dy)), Nat.mul(A, RD.Nat.pow2(1n+Dx)), Nat.mul(RD.Nat.pow2(2n+Dx), H), hyx,
      Equal.trans(Bool, RD.Nat.lt(Nat.mul(A, RD.Nat.pow2(1n+Dx)), Nat.mul(RD.Nat.pow2(2n+Dx), H)), RD.Nat.lt(Nat.mul(A, RD.Nat.pow2(1n+Dx)), Nat.mul(P, RD.Nat.pow2(1n+Dx))), True{},
        Equal.cong(Nat, Bool, v => RD.Nat.lt(Nat.mul(A, RD.Nat.pow2(1n+Dx)), v), Nat.mul(RD.Nat.pow2(2n+Dx), H), Nat.mul(P, RD.Nat.pow2(1n+Dx)),
          Equal.trans(Nat, Nat.mul(RD.Nat.pow2(2n+Dx), H), Nat.double(Nat.mul(RD.Nat.pow2(1n+Dx), H)), Nat.mul(P, RD.Nat.pow2(1n+Dx)), BP.Mul.dbl_l(RD.Nat.pow2(1n+Dx), H),
            Equal.trans(Nat, Nat.double(Nat.mul(RD.Nat.pow2(1n+Dx), H)), Nat.double(Nat.mul(H, RD.Nat.pow2(1n+Dx))), Nat.mul(P, RD.Nat.pow2(1n+Dx)), Equal.cong(Nat, Nat, v => Nat.double(v), Nat.mul(RD.Nat.pow2(1n+Dx), H), Nat.mul(H, RD.Nat.pow2(1n+Dx)), NL.Nat.mul_comm(RD.Nat.pow2(1n+Dx), H)),
              Equal.sym(Nat, Nat.mul(P, RD.Nat.pow2(1n+Dx)), Nat.double(Nat.mul(H, RD.Nat.pow2(1n+Dx))), BP.Mul.dbl_l(H, RD.Nat.pow2(1n+Dx)))))),
        E.Lt.mono(A, P, RD.Nat.pow2(1n+Dx), hA, BP.Pow2.pos(1n+Dx)))))
  +hDy : {RD.Nat.lt(Dx, Dy) == False{} : Bool} = E2.Le.of_lt1(1n+Dy, 1n+Dx, Pow2.rev(1n+Dy, 2n+Dx, E.Lt.cancel(RD.Nat.pow2(1n+Dy), RD.Nat.pow2(2n+Dx), H, hlt)))
  +hEy : {RD.Nat.lt(Nat.add(1n+p1, Dx), Ey) == False{} : Bool} = E.Le.trans(Ey, Nat.add(Dx, k), Nat.add(1n+p1, Dx), E2.Le.addr(Dy, Dx, k, hDy), E.Le.eq(Nat.add(Dx, k), Nat.add(1n+p1, Dx), NL.Nat.add_comm(Dx, k)))
  # |yh| <= xh, scaled
  +eXc : {Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+Dx)), K) == Xc : Nat} = Equal.trans(Nat, Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+Dx)), K), RD.Int.mag(a), Xc,
    Equal.sym(Nat, RD.Int.mag(a), Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+Dx)), K), E.Sh.mag(k, W.XH(A, Dx))), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), a, I.IPos{Xc}, ea))
  +eYc : {Nat.mul(Nat.mul(B, RD.Nat.pow2(1n+Dy)), K) == Nat.mul(B, RD.Nat.pow2(1n+Ey)) : Nat} = Equal.trans(Nat, Nat.mul(Nat.mul(B, RD.Nat.pow2(1n+Dy)), K), RD.Int.mag(D.Int.sh(k, W.XH(B, Dy))), Nat.mul(B, RD.Nat.pow2(1n+Ey)),
    Equal.sym(Nat, RD.Int.mag(D.Int.sh(k, W.XH(B, Dy))), Nat.mul(Nat.mul(B, RD.Nat.pow2(1n+Dy)), K), E.Sh.mag(k, W.XH(B, Dy))), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), D.Int.sh(k, W.XH(B, Dy)), W.XH(B, Ey), W.XH.sh(B, Dy, k)))
  +hyxc : {RD.Nat.lt(Xc, Nat.mul(B, RD.Nat.pow2(1n+Ey))) == False{} : Bool} = E.Le.trans(Nat.mul(B, RD.Nat.pow2(1n+Ey)), Nat.mul(Nat.mul(B, RD.Nat.pow2(1n+Dy)), K), Xc,
    E.Le.eq(Nat.mul(B, RD.Nat.pow2(1n+Ey)), Nat.mul(Nat.mul(B, RD.Nat.pow2(1n+Dy)), K), Equal.sym(Nat, Nat.mul(Nat.mul(B, RD.Nat.pow2(1n+Dy)), K), Nat.mul(B, RD.Nat.pow2(1n+Ey)), eYc)),
    E.Le.trans(Nat.mul(Nat.mul(B, RD.Nat.pow2(1n+Dy)), K), Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+Dx)), K), Xc, E2.Le.mulr(Nat.mul(B, RD.Nat.pow2(1n+Dy)), Nat.mul(A, RD.Nat.pow2(1n+Dx)), K, hyx), E.Le.eq(Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+Dx)), K), Xc, eXc)))
  +r : {RelA(p1, I.IPos{Xc}, b, W.Sg(sy, W.XH(B, Ey)), dd) == False{} : Bool} = AD.core(p1, Dx, A, B, Ey, b, dd, hp, hA1, hA, hB1, hB, hb, hd, hEy, hyxc, fb, fd, sy)
  Equal.trans(Bool, RelA(p1, W.XH(A, Dx), xl, W.Sg(sy, W.XH(B, Dy)), yl), RelA(p1, a, b, cc, dd), False{},
    Equal.sym(Bool, RelA(p1, a, b, cc, dd), RelA(p1, W.XH(A, Dx), xl, W.Sg(sy, W.XH(B, Dy)), yl), Sh.relA(p1, k, W.XH(A, Dx), xl, W.Sg(sy, W.XH(B, Dy)), yl)),
    Equal.trans(Bool, RelA(p1, a, b, cc, dd), RelA(p1, I.IPos{Xc}, b, W.Sg(sy, W.XH(B, Ey)), dd), False{},
      Equal.trans(Bool, RelA(p1, a, b, cc, dd), RelA(p1, I.IPos{Xc}, b, cc, dd), RelA(p1, I.IPos{Xc}, b, W.Sg(sy, W.XH(B, Ey)), dd),
        Equal.cong(I.Int, Bool, v => RelA(p1, v, b, cc, dd), a, I.IPos{Xc}, ea), Equal.cong(I.Int, Bool, v => RelA(p1, I.IPos{Xc}, b, v, dd), cc, W.Sg(sy, W.XH(B, Ey)), ecc)), r))

# x's sign moves to both operands
def AG.ord(+p1: Nat, sx: Bool, +sy: Bool, +A: Nat, +B: Nat, +Dx: Nat, +Dy: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(Dx), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(Dy), RD.Int.mag(yl)) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat},
  +hyx: {RD.Nat.lt(Nat.mul(A, RD.Nat.pow2(1n+Dx)), Nat.mul(B, RD.Nat.pow2(1n+Dy))) == False{} : Bool})
  -> {RelA(p1, W.Sg(sx, W.XH(A, Dx)), xl, W.Sg(sy, W.XH(B, Dy)), yl) == False{} : Bool}:
  match sx:
    case False{}:
      AG.pos(p1, sy, A, B, Dx, Dy, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, fx, fy, hyx)
    case True{}:
      +xh = W.XH(A, Dx)
      +yh = W.Sg(sy, W.XH(B, Dy))
      +nxl = I.Int.neg(xl)
      +nyl = I.Int.neg(yl)
      +r = AG.pos(p1, Bool.not(sy), A, B, Dx, Dy, nxl, nyl, hp, hA1, hA, hB1, hB, W.Sg.le(True{}, xl, RD.Nat.pow2(Dx), hx), W.Sg.le(True{}, yl, RD.Nat.pow2(Dy), hy),
        W.Sg.fix(1n+p1, True{}, xl, fx), W.Sg.fix(1n+p1, True{}, yl, fy), hyx)
      +e1 : {RelA(p1, I.Int.neg(xh), xl, yh, yl) == RelA(p1, I.Int.neg(xh), I.Int.neg(nxl), I.Int.neg(I.Int.neg(yh)), I.Int.neg(nyl)) : Bool} =
        Equal.trans(Bool, RelA(p1, I.Int.neg(xh), xl, yh, yl), RelA(p1, I.Int.neg(xh), I.Int.neg(nxl), yh, yl), RelA(p1, I.Int.neg(xh), I.Int.neg(nxl), I.Int.neg(I.Int.neg(yh)), I.Int.neg(nyl)),
          Equal.cong(I.Int, Bool, v => RelA(p1, I.Int.neg(xh), v, yh, yl), xl, I.Int.neg(nxl), Equal.sym(I.Int, I.Int.neg(nxl), xl, Z.Int.neg_neg(xl))),
          Equal.trans(Bool, RelA(p1, I.Int.neg(xh), I.Int.neg(nxl), yh, yl), RelA(p1, I.Int.neg(xh), I.Int.neg(nxl), I.Int.neg(I.Int.neg(yh)), yl), RelA(p1, I.Int.neg(xh), I.Int.neg(nxl), I.Int.neg(I.Int.neg(yh)), I.Int.neg(nyl)),
            Equal.cong(I.Int, Bool, v => RelA(p1, I.Int.neg(xh), I.Int.neg(nxl), v, yl), yh, I.Int.neg(I.Int.neg(yh)), Equal.sym(I.Int, I.Int.neg(I.Int.neg(yh)), yh, Z.Int.neg_neg(yh))),
            Equal.cong(I.Int, Bool, v => RelA(p1, I.Int.neg(xh), I.Int.neg(nxl), I.Int.neg(I.Int.neg(yh)), v), yl, I.Int.neg(nyl), Equal.sym(I.Int, I.Int.neg(nyl), yl, Z.Int.neg_neg(yl)))))
      Equal.trans(Bool, RelA(p1, I.Int.neg(xh), xl, yh, yl), RelA(p1, xh, nxl, I.Int.neg(yh), nyl), False{},
        Equal.trans(Bool, RelA(p1, I.Int.neg(xh), xl, yh, yl), RelA(p1, I.Int.neg(xh), I.Int.neg(nxl), I.Int.neg(I.Int.neg(yh)), I.Int.neg(nyl)), RelA(p1, xh, nxl, I.Int.neg(yh), nyl), e1, Neg.relA(p1, xh, nxl, I.Int.neg(yh), nyl)),
        Equal.trans(Bool, RelA(p1, xh, nxl, I.Int.neg(yh), nyl), RelA(p1, xh, nxl, W.Sg(Bool.not(sy), W.XH(B, Dy)), nyl), False{},
          Equal.cong(I.Int, Bool, v => RelA(p1, xh, nxl, v, nyl), I.Int.neg(yh), W.Sg(Bool.not(sy), W.XH(B, Dy)), Sg.neg(sy, W.XH(B, Dy))), r))


def AccDW.go(+p1: Nat, +sx: Bool, +sy: Bool, +A: Nat, +B: Nat, +Dx: Nat, +Dy: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(Dx), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(Dy), RD.Int.mag(yl)) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat},
  l: Bool, +el: {RD.Nat.lt(Nat.mul(A, RD.Nat.pow2(1n+Dx)), Nat.mul(B, RD.Nat.pow2(1n+Dy))) == l : Bool})
  -> {RelA(p1, W.Sg(sx, W.XH(A, Dx)), xl, W.Sg(sy, W.XH(B, Dy)), yl) == False{} : Bool}:
  match l:
    case False{}:
      AG.ord(p1, sx, sy, A, B, Dx, Dy, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, fx, fy, el)
    case True{}:
      Equal.trans(Bool, RelA(p1, W.Sg(sx, W.XH(A, Dx)), xl, W.Sg(sy, W.XH(B, Dy)), yl), RelA(p1, W.Sg(sy, W.XH(B, Dy)), yl, W.Sg(sx, W.XH(A, Dx)), xl), False{},
        Equal.sym(Bool, RelA(p1, W.Sg(sy, W.XH(B, Dy)), yl, W.Sg(sx, W.XH(A, Dx)), xl), RelA(p1, W.Sg(sx, W.XH(A, Dx)), xl, W.Sg(sy, W.XH(B, Dy)), yl), Sym.relA(p1, W.Sg(sx, W.XH(A, Dx)), xl, W.Sg(sy, W.XH(B, Dy)), yl)),
        AG.ord(p1, sy, sx, B, A, Dy, Dx, yl, xl, hp, hB1, hB, hA1, hA, hy, hx, fy, fx, E2.Lt.to_le(Nat.mul(A, RD.Nat.pow2(1n+Dx)), Nat.mul(B, RD.Nat.pow2(1n+Dy)), el)))


# AccurateDWPlusDW (Joldes, Muller and Popescu, Theorem 3.1), binary
# rounding at p >= 6 bits with no exponent bounds, any signs and exponents:
# xh = +-A 2^(Dx+1) with 2^(p-1) <= A < 2^p (so u xh is 2^Dx), |xl| <= 2^Dx
# representable, the same for y: |zh + zl - (x + y)| (1 - 4u) <= 3u² |x + y|
def AccDW.gen(+p1: Nat, +sx: Bool, +sy: Bool, +A: Nat, +B: Nat, +Dx: Nat, +Dy: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(Dx), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(Dy), RD.Int.mag(yl)) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat})
  -> {RelA(p1, W.Sg(sx, W.XH(A, Dx)), xl, W.Sg(sy, W.XH(B, Dy)), yl) == False{} : Bool}:
  AccDW.go(p1, sx, sy, A, B, Dx, Dy, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, fx, fy, RD.Nat.lt(Nat.mul(A, RD.Nat.pow2(1n+Dx)), Nat.mul(B, RD.Nat.pow2(1n+Dy))), {==})


# 3u²/(1 - 4u) < 3u² + 13u³ for p >= 6: e 2^p (2^p - 4) <= 3M gives
# e 2^3p <= (3 2^p + 13) M
def AccDW.simp(+p1: Nat, +e: Nat, +M: Nat, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +h: {RD.Nat.lt(Nat.mul(3n, M), Nat.mul(e, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.monus(RD.Nat.pow2(1n+p1), 4n)))) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(Nat.add(Nat.mul(3n, RD.Nat.pow2(1n+p1)), 13n), M), Nat.mul(e, Nat.mul(RD.Nat.pow2(1n+p1), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+p1))))) == False{} : Bool}:
  +P = RD.Nat.pow2(1n+p1)
  +m4 = RD.Nat.monus(P, 4n)
  +PP = Nat.mul(P, P)
  +K = Nat.add(Nat.mul(3n, P), 13n)
  +eP : {P == Nat.add(4n, m4) : Nat} = NQ.e4(p1, hp)
  +r = RD.Nat.monus(m4, 48n)
  +ew : {m4 == Nat.add(48n, r) : Nat} = E.Le.wit(48n, m4, E.Le.trans(48n, 60n, m4, {==}, NQ.m60(p1, hp)))
  +eor : {Nat.mul(1n, r) == r : Nat} = P3.Mul.one_l(r)
  +eom : {Nat.mul(1n, m4) == m4 : Nat} = P3.Mul.one_l(m4)
  +env : List<&2, Nat> = [1n, m4, r]
  +P4 = Nat.add(4n, m4)
  +ec0 : {Nat.mul(m4, Nat.add(Nat.mul(3n, P4), 13n)) == Nat.add(Nat.mul(3n, Nat.mul(P4, P4)), r) : Nat} = R.NatN.eq2(env, R.Ml(R.V(1n), R.Ad(R.Ad(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n))))), R.Ad(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n))))), R.Ad(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n))))), N.TZero{}))), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{}))))))))))))))), R.Ad(R.Ad(R.Ml(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n))))), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n)))))), R.Ad(R.Ml(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n))))), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n)))))), R.Ad(R.Ml(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n))))), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n)))))), N.TZero{}))), R.V(2n)), [R.V(0n)], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(2n)))))))))))))))))))))))))))))))))))))))))))))))))))], [R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n)))], {==}, (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(2n))))))))))))))))))))))))))))))))))))))))))))))))), {==}, {==}, ew), Unit{}), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eor), Unit{}), {==}, {==})
  +ec : {Nat.mul(m4, K) == Nat.add(Nat.mul(3n, PP), r) : Nat} = Equal.trans(Nat, Nat.mul(m4, K), Nat.mul(m4, Nat.add(Nat.mul(3n, P4), 13n)), Nat.add(Nat.mul(3n, PP), r),
    Equal.cong(Nat, Nat, v => Nat.mul(m4, Nat.add(Nat.mul(3n, v), 13n)), P, P4, eP),
    Equal.trans(Nat, Nat.mul(m4, Nat.add(Nat.mul(3n, P4), 13n)), Nat.add(Nat.mul(3n, Nat.mul(P4, P4)), r), Nat.add(Nat.mul(3n, PP), r), ec0,
      Equal.cong(Nat, Nat, v => Nat.add(Nat.mul(3n, Nat.mul(v, v)), r), P4, P, Equal.sym(Nat, P, P4, eP))))
  +envs : List<&2, Nat> = [e, P, m4, M, K]
  +e1 : {Nat.mul(Nat.mul(e, Nat.mul(P, PP)), m4) == Nat.mul(Nat.mul(e, Nat.mul(P, m4)), PP) : Nat} = R.NatN.eq(envs, R.Ml(R.Ml(R.V(0n), R.Ml(R.V(1n), R.Ml(R.V(1n), R.V(1n)))), R.V(2n)), R.Ml(R.Ml(R.V(0n), R.Ml(R.V(1n), R.V(2n))), R.Ml(R.V(1n), R.V(1n))), [], [], {==}, Unit{}, {==}, {==})
  +e2 : {Nat.mul(Nat.mul(3n, M), PP) == Nat.mul(Nat.mul(3n, PP), M) : Nat} = R.NatN.eq(envs, R.Ml(R.Ad(R.V(3n), R.Ad(R.V(3n), R.Ad(R.V(3n), N.TZero{}))), R.Ml(R.V(1n), R.V(1n))),
    R.Ml(R.Ad(R.Ml(R.V(1n), R.V(1n)), R.Ad(R.Ml(R.V(1n), R.V(1n)), R.Ad(R.Ml(R.V(1n), R.V(1n)), N.TZero{}))), R.V(3n)), [], [], {==}, Unit{}, {==}, {==})
  +e3 : {Nat.mul(Nat.mul(m4, K), M) == Nat.mul(Nat.mul(K, M), m4) : Nat} = R.NatN.eq(envs, R.Ml(R.Ml(R.V(2n), R.V(4n)), R.V(3n)), R.Ml(R.Ml(R.V(4n), R.V(3n)), R.V(2n)), [], [], {==}, Unit{}, {==}, {==})
  +pos : {RD.Nat.lt(0n, m4) == True{} : Bool} = E2.Lt.le_trans(0n, 60n, m4, {==}, NQ.m60(p1, hp))
  E.Le.cancel(Nat.mul(e, Nat.mul(P, PP)), Nat.mul(K, M), m4, pos,
    E.Le.trans(Nat.mul(Nat.mul(e, Nat.mul(P, PP)), m4), Nat.mul(Nat.mul(3n, PP), M), Nat.mul(Nat.mul(K, M), m4),
      E.Le.trans(Nat.mul(Nat.mul(e, Nat.mul(P, PP)), m4), Nat.mul(Nat.mul(3n, M), PP), Nat.mul(Nat.mul(3n, PP), M),
        E.Le.trans(Nat.mul(Nat.mul(e, Nat.mul(P, PP)), m4), Nat.mul(Nat.mul(e, Nat.mul(P, m4)), PP), Nat.mul(Nat.mul(3n, M), PP), E.Le.eq(Nat.mul(Nat.mul(e, Nat.mul(P, PP)), m4), Nat.mul(Nat.mul(e, Nat.mul(P, m4)), PP), e1),
          E2.Le.mulr(Nat.mul(e, Nat.mul(P, m4)), Nat.mul(3n, M), PP, h)),
        E.Le.eq(Nat.mul(Nat.mul(3n, M), PP), Nat.mul(Nat.mul(3n, PP), M), e2)),
      E.Le.trans(Nat.mul(Nat.mul(3n, PP), M), Nat.mul(Nat.add(Nat.mul(3n, PP), r), M), Nat.mul(Nat.mul(K, M), m4), E2.Le.mulr(Nat.mul(3n, PP), Nat.add(Nat.mul(3n, PP), r), M, E.Le.add(Nat.mul(3n, PP), r)),
        E.Le.eq(Nat.mul(Nat.add(Nat.mul(3n, PP), r), M), Nat.mul(Nat.mul(K, M), m4), Equal.trans(Nat, Nat.mul(Nat.add(Nat.mul(3n, PP), r), M), Nat.mul(Nat.mul(m4, K), M), Nat.mul(Nat.mul(K, M), m4),
          Equal.cong(Nat, Nat, v => Nat.mul(v, M), Nat.add(Nat.mul(3n, PP), r), Nat.mul(m4, K), Equal.sym(Nat, Nat.mul(m4, K), Nat.add(Nat.mul(3n, PP), r), ec)), e3)))))

