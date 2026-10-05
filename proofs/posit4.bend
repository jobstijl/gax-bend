# b-posit patterns, field by field (src/posit.bend): a scale class rb, an
# exponent ee < 2^es and a fraction fr < 2^fb give the pattern
#   Pat = R 2^(es + fb) + ee 2^fb + fr
# with R the regime bits, and the value
#   Val = (2^fb + fr) 2^(rb g + ee) / 2^(bias + fb).
# The decoder reads Val back from Pat (Dec.val); the next pattern is the
# next value, one unit in the last place up (Pat.succ, Val.succ); and the
# spec's rounding is the standard's rounding of the bit string (Std.round).

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
import ./posit2.bend as P2
import ./posit3.bend as P3
import ../src/posit.bend as P
import ../src/big.bend as SB

# Runs of regime bits
# -------------------

def Lt.irr(+a: Nat) -> {RD.Nat.lt(a, a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+(+a2):
      Lt.irr(a2)

# b (2^k - 1) 2^v + low: k bits b above a v-bit field
def Q(+b: Nat, +k: Nat, +v: Nat, +low: Nat) -> Nat:
  Nat.add(Nat.mul(b, Nat.mul(RD.Nat.monus(RD.Nat.pow2(k), 1n), RD.Nat.pow2(v))), low)

def Q.bits(+k: Nat, +v: Nat, +b: Nat, +low: Nat, +hb: {RD.Nat.lt(1n, b) == False{} : Bool}, +hl: {RD.Nat.lt(low, RD.Nat.pow2(v)) == True{} : Bool})
  -> {P2.Bits.ok(k, Q(b, k, v, low), Nat.add(k, v), b) == True{} : Bool}:
  P2.Same.bits(k, v, 0n, b, low, Q(b, k, v, low), hb, hl, {==})

# the top bit of a field whose top k >= 1 bits are b
def Q.top(+k1: Nat, +v: Nat, +b: Nat, +q: Nat, +h: {P2.Bits.ok(1n+k1, q, Nat.add(1n+k1, v), b) == True{} : Bool})
  -> {P2.Bitq(q, RD.Nat.monus(Nat.add(1n+k1, v), 1n)) == b : Nat}:
  Equal.trans(Nat, P2.Bitq(q, RD.Nat.monus(Nat.add(1n+k1, v), 1n)), P2.Bitq(q, Nat.add(k1, v)), b,
    Equal.cong(Nat, Nat, z => P2.Bitq(q, z), RD.Nat.monus(Nat.add(k1, v), 0n), Nat.add(k1, v), BP.Mo.z(Nat.add(k1, v))),
    P2.Eq.true(P2.Bitq(q, Nat.add(k1, v)), b, NP.Bool.and_l(Nat.is_eq(P2.Bitq(q, Nat.add(k1, v)), b), P2.Bits.ok(k1, q, Nat.add(k1, v), b), h)))

# a full run: k = rs bits b
def Run.full(+k: Nat, +v: Nat, +b: Nat, +low: Nat, +hb: {RD.Nat.lt(1n, b) == False{} : Bool}, +hl: {RD.Nat.lt(low, RD.Nat.pow2(v)) == True{} : Bool})
  -> {P.Pz.run(k, Q(b, k, v, low), Nat.add(k, v), b) == k : Nat}:
  P2.Run.ok(k, k, Nat.add(k, v), Q(b, k, v, low), b, Lt.irr(k), BP.Lt.ge(k, v), Q.bits(k, v, b, low, hb, hl),
    hk => hbt => B.Bool.tf(Empty, Equal.trans(Bool, True{}, RD.Nat.lt(k, k), False{}, Equal.sym(Bool, RD.Nat.lt(k, k), True{}, hk), Lt.irr(k))))

# bit v1 of b (2^k - 1) 2^(v1 + 1) + beta 2^v1 + lw is beta
def Q.stop(+k: Nat, +v1: Nat, +b: Nat, +beta: Nat, +lw: Nat, +hbeta: {RD.Nat.lt(1n, beta) == False{} : Bool}, +hlw: {RD.Nat.lt(lw, RD.Nat.pow2(v1)) == True{} : Bool})
  -> {P2.Bitq(Q(b, k, 1n+v1, Nat.add(Nat.mul(beta, RD.Nat.pow2(v1)), lw)), v1) == beta : Nat}:
  +M = RD.Nat.monus(RD.Nat.pow2(k), 1n)
  +P1 = RD.Nat.pow2(1n+v1)
  +Pv = RD.Nat.pow2(v1)
  +env : List<&2, Nat> = [b, M, P1, beta, Pv, lw]
  +e : {Q(b, k, 1n+v1, Nat.add(Nat.mul(beta, Pv), lw)) == Nat.add(Nat.add(Nat.mul(Nat.mul(b, M), P1), Nat.mul(beta, Pv)), lw) : Nat} =
    R.NatN.eq(env, R.Ad(R.Ml(R.V(0n), R.Ml(R.V(1n), R.V(2n))), R.Ad(R.Ml(R.V(3n), R.V(4n)), R.V(5n))), R.Ad(R.Ad(R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(2n)), R.Ml(R.V(3n), R.V(4n))), R.V(5n)), [], [], {==}, Unit{}, {==}, {==})
  Equal.trans(Nat, P2.Bitq(Q(b, k, 1n+v1, Nat.add(Nat.mul(beta, Pv), lw)), v1), P2.Bitq(Nat.add(Nat.add(Nat.mul(Nat.mul(b, M), P1), Nat.mul(beta, Pv)), lw), v1), beta,
    Equal.cong(Nat, Nat, z => P2.Bitq(z, v1), Q(b, k, 1n+v1, Nat.add(Nat.mul(beta, Pv), lw)), Nat.add(Nat.add(Nat.mul(Nat.mul(b, M), P1), Nat.mul(beta, Pv)), lw), e),
    P2.Bit.of(Nat.mul(b, M), beta, lw, v1, hbeta, hlw))

def Low.lt(+v1: Nat, +beta: Nat, +lw: Nat, +hbeta: {RD.Nat.lt(1n, beta) == False{} : Bool}, +hlw: {RD.Nat.lt(lw, RD.Nat.pow2(v1)) == True{} : Bool})
  -> {RD.Nat.lt(Nat.add(Nat.mul(beta, RD.Nat.pow2(v1)), lw), RD.Nat.pow2(1n+v1)) == True{} : Bool}:
  +Pv = RD.Nat.pow2(v1)
  +l1 : {RD.Nat.lt(Nat.add(Nat.mul(beta, Pv), lw), Nat.add(Nat.mul(beta, Pv), Pv)) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Nat.add(Nat.mul(beta, Pv), lw), Nat.add(Nat.mul(beta, Pv), Pv)), RD.Nat.lt(lw, Pv), True{}, BP.Lt.shift(Nat.mul(beta, Pv), lw, Pv), hlw)
  +l2 : {RD.Nat.lt(Nat.add(Pv, Pv), Nat.add(Nat.mul(beta, Pv), Pv)) == False{} : Bool} = E2.Le.addr(Nat.mul(beta, Pv), Pv, Pv, E.Le.trans(Nat.mul(beta, Pv), Nat.mul(1n, Pv), Pv, E2.Le.mulr(beta, 1n, Pv, hbeta), E.Le.eq(Nat.mul(1n, Pv), Pv, P3.Mul.one_l(Pv))))
  E2.Lt.le_trans(Nat.add(Nat.mul(beta, Pv), lw), Nat.add(Nat.mul(beta, Pv), Pv), RD.Nat.pow2(1n+v1), l1,
    E.Le.trans(Nat.add(Nat.mul(beta, Pv), Pv), Nat.add(Pv, Pv), RD.Nat.pow2(1n+v1), l2, E.Le.eq(Nat.add(Pv, Pv), RD.Nat.pow2(1n+v1), Equal.sym(Nat, Nat.double(Pv), Nat.add(Pv, Pv), Y.Nat.double_add(Pv)))))

# a short run: k < rs bits b, then the stop bit beta != b
def Run.short(+k: Nat, +v1: Nat, +rs: Nat, +b: Nat, +beta: Nat, +lw: Nat,
  +hb: {RD.Nat.lt(1n, b) == False{} : Bool}, +hbeta: {RD.Nat.lt(1n, beta) == False{} : Bool}, hne: {beta == b : Nat} -> Empty,
  +hkr: {RD.Nat.lt(rs, k) == False{} : Bool}, +hlw: {RD.Nat.lt(lw, RD.Nat.pow2(v1)) == True{} : Bool})
  -> {P.Pz.run(rs, Q(b, k, 1n+v1, Nat.add(Nat.mul(beta, RD.Nat.pow2(v1)), lw)), Nat.add(k, 1n+v1), b) == k : Nat}:
  +low = Nat.add(Nat.mul(beta, RD.Nat.pow2(v1)), lw)
  +q = Q(b, k, 1n+v1, low)
  +w = Nat.add(k, 1n+v1)
  +ew : {RD.Nat.monus(w, 1n+k) == v1 : Nat} = Equal.trans(Nat, RD.Nat.monus(w, 1n+k), RD.Nat.monus(1n+Nat.add(k, v1), 1n+k), v1,
    Equal.cong(Nat, Nat, z => RD.Nat.monus(z, 1n+k), w, 1n+Nat.add(k, v1), NL.Nat.add_succ_r(k, v1)), R.Nat.monus_add(k, v1))
  +est : {P2.Bitq(q, v1) == beta : Nat} = Q.stop(k, v1, b, beta, lw, hbeta, hlw)
  P2.Run.ok(k, rs, w, q, b, hkr, BP.Lt.ge(k, 1n+v1), Q.bits(k, 1n+v1, b, low, hb, Low.lt(v1, beta, lw, hbeta, hlw)),
    hk => hbt => hne(Equal.trans(Nat, beta, P2.Bitq(q, v1), b, Equal.sym(Nat, P2.Bitq(q, v1), beta, est),
      Equal.trans(Nat, P2.Bitq(q, v1), P2.Bitq(q, RD.Nat.monus(w, 1n+k)), b, Equal.cong(Nat, Nat, z => P2.Bitq(q, z), v1, RD.Nat.monus(w, 1n+k), Equal.sym(Nat, RD.Nat.monus(w, 1n+k), v1, ew)), hbt))))

# The decoder's value
# -------------------

def Pk.t(+h1: Nat, +B: Nat, +tb: Nat, +M: Nat, +el: {RD.Nat.lt(tb, B) == True{} : Bool})
  -> {SB.Bd.val(1n+h1, SB.Bd{False{}, SB.Bn.of(1n+h1, M), Nat.sub(B, tb)}) == D.Dy.of(B, I.IPos{Nat.mul(M, RD.Nat.pow2(tb))}) : D.Dy}:
  +c = RD.Nat.monus(B, tb)
  +eB : {B == Nat.add(c, tb) : Nat} = Equal.trans(Nat, B, Nat.add(tb, c), Nat.add(c, tb), E.Le.wit(tb, B, E2.Lt.to_le(tb, B, el)), NL.Nat.add_comm(tb, c))
  +ev : {SB.Bn.val(1n+h1, SB.Bn.of(1n+h1, M)) == M : Nat} = BP.Of.val(h1, M)
  +e1 : {SB.Bd.val(1n+h1, SB.Bd{False{}, SB.Bn.of(1n+h1, M), Nat.sub(B, tb)}) == D.Dy.of(c, I.IPos{M}) : D.Dy} = Y.Of.cong(Nat.sub(B, tb), c, I.IPos{SB.Bn.val(1n+h1, SB.Bn.of(1n+h1, M))}, I.IPos{M}, P2.Sub.eq(B, tb), Equal.cong(Nat, I.Int, z => I.IPos{z}, SB.Bn.val(1n+h1, SB.Bn.of(1n+h1, M)), M, ev))
  +e2 : {D.Dy.of(B, I.IPos{Nat.mul(M, RD.Nat.pow2(tb))}) == D.Dy.of(c, I.IPos{M}) : D.Dy} = Equal.trans(D.Dy, D.Dy.of(B, I.IPos{Nat.mul(M, RD.Nat.pow2(tb))}), D.Dy.of(Nat.add(c, tb), D.Int.sh(tb, I.IPos{M})), D.Dy.of(c, I.IPos{M}),
    Y.Of.cong(B, Nat.add(c, tb), I.IPos{Nat.mul(M, RD.Nat.pow2(tb))}, D.Int.sh(tb, I.IPos{M}), eB, Equal.sym(I.Int, D.Int.sh(tb, I.IPos{M}), I.IPos{Nat.mul(M, RD.Nat.pow2(tb))}, R.Sh.ipos(tb, M))),
    Y.Of.shift(tb, c, I.IPos{M}))
  Equal.trans(D.Dy, SB.Bd.val(1n+h1, SB.Bd{False{}, SB.Bn.of(1n+h1, M), Nat.sub(B, tb)}), D.Dy.of(c, I.IPos{M}), D.Dy.of(B, I.IPos{Nat.mul(M, RD.Nat.pow2(tb))}), e1,
    Equal.sym(D.Dy, D.Dy.of(B, I.IPos{Nat.mul(M, RD.Nat.pow2(tb))}), D.Dy.of(c, I.IPos{M}), e2))

def Pk.f(+h1: Nat, +B: Nat, +tb: Nat, +M: Nat, +el: {RD.Nat.lt(tb, B) == False{} : Bool})
  -> {SB.Bd.val(1n+h1, SB.Bd{False{}, SB.Bn.shl(1n+h1, Nat.sub(tb, B), SB.Bn.of(1n+h1, M)), 0n}) == D.Dy.of(B, I.IPos{Nat.mul(M, RD.Nat.pow2(tb))}) : D.Dy}:
  +c = RD.Nat.monus(tb, B)
  +etb : {tb == Nat.add(B, c) : Nat} = E.Le.wit(B, tb, el)
  +m = SB.Bn.of(1n+h1, M)
  +ev : {SB.Bn.val(1n+h1, SB.Bn.shl(1n+h1, Nat.sub(tb, B), m)) == Nat.mul(M, RD.Nat.pow2(c)) : Nat} = Equal.trans(Nat, SB.Bn.val(1n+h1, SB.Bn.shl(1n+h1, Nat.sub(tb, B), m)), Nat.mul(SB.Bn.val(1n+h1, m), RD.Nat.pow2(Nat.sub(tb, B))), Nat.mul(M, RD.Nat.pow2(c)),
    BP.Shl.val(h1, Nat.sub(tb, B), m),
    Equal.trans(Nat, Nat.mul(SB.Bn.val(1n+h1, m), RD.Nat.pow2(Nat.sub(tb, B))), Nat.mul(M, RD.Nat.pow2(Nat.sub(tb, B))), Nat.mul(M, RD.Nat.pow2(c)),
      Equal.cong(Nat, Nat, z => Nat.mul(z, RD.Nat.pow2(Nat.sub(tb, B))), SB.Bn.val(1n+h1, m), M, BP.Of.val(h1, M)),
      Equal.cong(Nat, Nat, z => Nat.mul(M, RD.Nat.pow2(z)), Nat.sub(tb, B), c, P2.Sub.eq(tb, B))))
  +Pc = RD.Nat.pow2(c)
  +PB = RD.Nat.pow2(B)
  +Pt = RD.Nat.pow2(tb)
  +ept : {Pt == Nat.mul(PB, Pc) : Nat} = Equal.trans(Nat, Pt, RD.Nat.pow2(Nat.add(B, c)), Nat.mul(PB, Pc), Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), tb, Nat.add(B, c), etb), BP.Pow2.add(B, c))
  +env : List<&2, Nat> = [M, Pc, PB, Pt]
  +em : {Nat.mul(M, Pt) == Nat.mul(Nat.mul(M, Pc), PB) : Nat} = R.NatN.eq(env, R.Ml(R.V(0n), R.V(3n)), R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(2n)), [R.V(0n)], [R.Ad(R.V(3n), R.Ng(R.Ml(R.V(2n), R.V(1n))))], {==}, (R.NatN.z(env, R.V(3n), R.Ml(R.V(2n), R.V(1n)), {==}, {==}, ept), Unit{}), {==}, {==})
  +e2 : {D.Dy.of(B, I.IPos{Nat.mul(M, Pt)}) == D.Dy.of(0n, I.IPos{Nat.mul(M, Pc)}) : D.Dy} = Equal.trans(D.Dy, D.Dy.of(B, I.IPos{Nat.mul(M, Pt)}), D.Dy.of(Nat.add(0n, B), D.Int.sh(B, I.IPos{Nat.mul(M, Pc)})), D.Dy.of(0n, I.IPos{Nat.mul(M, Pc)}),
    Y.Of.cong(B, Nat.add(0n, B), I.IPos{Nat.mul(M, Pt)}, D.Int.sh(B, I.IPos{Nat.mul(M, Pc)}), {==},
      Equal.trans(I.Int, I.IPos{Nat.mul(M, Pt)}, I.IPos{Nat.mul(Nat.mul(M, Pc), PB)}, D.Int.sh(B, I.IPos{Nat.mul(M, Pc)}), Equal.cong(Nat, I.Int, z => I.IPos{z}, Nat.mul(M, Pt), Nat.mul(Nat.mul(M, Pc), PB), em),
        Equal.sym(I.Int, D.Int.sh(B, I.IPos{Nat.mul(M, Pc)}), I.IPos{Nat.mul(Nat.mul(M, Pc), PB)}, R.Sh.ipos(B, Nat.mul(M, Pc))))),
    Y.Of.shift(B, 0n, I.IPos{Nat.mul(M, Pc)}))
  Equal.trans(D.Dy, SB.Bd.val(1n+h1, SB.Bd{False{}, SB.Bn.shl(1n+h1, Nat.sub(tb, B), m), 0n}), D.Dy.of(0n, I.IPos{Nat.mul(M, Pc)}), D.Dy.of(B, I.IPos{Nat.mul(M, Pt)}),
    Equal.cong(Nat, D.Dy, z => D.Dy.of(0n, I.IPos{z}), SB.Bn.val(1n+h1, SB.Bn.shl(1n+h1, Nat.sub(tb, B), m)), Nat.mul(M, Pc), ev),
    Equal.sym(D.Dy, D.Dy.of(B, I.IPos{Nat.mul(M, Pt)}), D.Dy.of(0n, I.IPos{Nat.mul(M, Pc)}), e2))

def Pk.go(+h1: Nat, +B: Nat, +tb: Nat, +M: Nat, l: Bool, +el: {RD.Nat.lt(tb, B) == l : Bool})
  -> {SB.Bd.val(1n+h1, Bool.pick(SB.Bd, l, SB.Bd{False{}, SB.Bn.of(1n+h1, M), Nat.sub(B, tb)}, SB.Bd{False{}, SB.Bn.shl(1n+h1, Nat.sub(tb, B), SB.Bn.of(1n+h1, M)), 0n})) == D.Dy.of(B, I.IPos{Nat.mul(M, RD.Nat.pow2(tb))}) : D.Dy}:
  match l:
    case True{}:
      Pk.t(h1, B, tb, M, el)
    case False{}:
      Pk.f(h1, B, tb, M, el)

# Dfin's value: (2^fb + fr) 2^tb / 2^(bias + fb)
def Dfin.val(+h1: Nat, +es: Nat, +rs: Nat, +b: Nat, +k: Nat, +fb: Nat, +ee: Nat, +fr: Nat)
  -> {SB.Bd.val(1n+h1, P2.Dfin(1n+h1, es, rs, False{}, b, k, fb, ee, fr)) == D.Dy.of(Nat.add(Nat.mul(rs, P.Nat.pw(es)), fb), I.IPos{Nat.mul(Nat.add(P.Nat.pw(fb), fr), RD.Nat.pow2(Nat.add(Nat.mul(Bool.pick(Nat, Nat.is_eq(b, 1n), Nat.sub(Nat.add(k, rs), 1n), Nat.sub(rs, k)), P.Nat.pw(es)), ee)))}) : D.Dy}:
  +tb = Nat.add(Nat.mul(Bool.pick(Nat, Nat.is_eq(b, 1n), Nat.sub(Nat.add(k, rs), 1n), Nat.sub(rs, k)), P.Nat.pw(es)), ee)
  +B = Nat.add(Nat.mul(rs, P.Nat.pw(es)), fb)
  +M = Nat.add(P.Nat.pw(fb), fr)
  +e0 = Equal.cong(Bool, D.Dy, z => SB.Bd.val(1n+h1, Bool.pick(SB.Bd, z, SB.Bd{False{}, SB.Bn.of(1n+h1, M), Nat.sub(B, tb)}, SB.Bd{False{}, SB.Bn.shl(1n+h1, Nat.sub(tb, B), SB.Bn.of(1n+h1, M)), 0n})), Nat.is_lt(tb, B), RD.Nat.lt(tb, B), P2.Lt.eq(tb, B))
  Equal.trans(D.Dy, SB.Bd.val(1n+h1, P2.Dfin(1n+h1, es, rs, False{}, b, k, fb, ee, fr)), SB.Bd.val(1n+h1, Bool.pick(SB.Bd, RD.Nat.lt(tb, B), SB.Bd{False{}, SB.Bn.of(1n+h1, M), Nat.sub(B, tb)}, SB.Bd{False{}, SB.Bn.shl(1n+h1, Nat.sub(tb, B), SB.Bn.of(1n+h1, M)), 0n})), D.Dy.of(B, I.IPos{Nat.mul(M, RD.Nat.pow2(tb))}),
    e0, Pk.go(h1, B, tb, M, RD.Nat.lt(tb, B), {==}))

# a field below the regime: ee 2^fb + fr < 2^(es + fb)
def Low.ok(+es: Nat, +fb: Nat, +ee: Nat, +fr: Nat, +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(fb)) == True{} : Bool})
  -> {RD.Nat.lt(Nat.add(Nat.mul(ee, RD.Nat.pow2(fb)), fr), RD.Nat.pow2(Nat.add(es, fb))) == True{} : Bool}:
  +Pf = RD.Nat.pow2(fb)
  +Pg = RD.Nat.pow2(es)
  E2.Lt.le_trans(Nat.add(Nat.mul(ee, Pf), fr), Nat.mul(1n+ee, Pf), RD.Nat.pow2(Nat.add(es, fb)), P3.Lt.next(ee, fb, fr, hfr),
    E.Le.trans(Nat.mul(1n+ee, Pf), Nat.mul(Pg, Pf), RD.Nat.pow2(Nat.add(es, fb)), E2.Le.mulr(1n+ee, Pg, Pf, E2.Le.succ(ee, Pg, hee)),
      E.Le.eq(Nat.mul(Pg, Pf), RD.Nat.pow2(Nat.add(es, fb)), Equal.sym(Nat, RD.Nat.pow2(Nat.add(es, fb)), Nat.mul(Pg, Pf), BP.Pow2.add(es, fb)))))

def VF(+rs: Nat, +fb: Nat, +ee: Nat, +fr: Nat, +gw: Nat, +pf: Nat, +tb: Nat) -> D.Dy:
  D.Dy.of(Nat.add(Nat.mul(rs, gw), fb), I.IPos{Nat.mul(Nat.add(pf, fr), RD.Nat.pow2(Nat.add(Nat.mul(tb, gw), ee)))})

# the decoder on q = R 2^(es + fb) + ee 2^fb + fr, a w-bit field whose top
# bit is b and whose regime run is k, regime length rl
def Dec.gen(+h1: Nat, +es: Nat, +rs: Nat, +w: Nat, +q: Nat, +b: Nat, +k: Nat, +rl: Nat, +fb: Nat, +ee: Nat, +fr: Nat, +rb: Nat, +Rr: Nat,
  +hw: {w == Nat.add(rl, Nat.add(es, fb)) : Nat},
  +hqlt: {RD.Nat.lt(q, RD.Nat.pow2(w)) == True{} : Bool},
  +hb: {P2.Bitq(q, RD.Nat.monus(w, 1n)) == b : Nat},
  +hk: {P.Pz.run(rs, q, w, b) == k : Nat},
  +hrl: {Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs) == rl : Nat},
  +hq: {q == Nat.add(Nat.mul(Rr, RD.Nat.pow2(Nat.add(es, fb))), Nat.add(Nat.mul(ee, RD.Nat.pow2(fb)), fr)) : Nat},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool},
  +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(fb)) == True{} : Bool},
  +htb: {Bool.pick(Nat, Nat.is_eq(b, 1n), Nat.sub(Nat.add(k, rs), 1n), Nat.sub(rs, k)) == rb : Nat})
  -> {SB.Bd.val(1n+h1, P.Pz.dec(1n+h1, 1n+w, es, rs, q)) == VF(rs, fb, ee, fr, RD.Nat.pow2(es), RD.Nat.pow2(fb), rb) : D.Dy}:
  +rem = Nat.add(es, fb)
  +low = Nat.add(Nat.mul(ee, RD.Nat.pow2(fb)), fr)
  +lowp = Nat.add(Nat.mul(ee, P.Nat.pw(fb)), fr)
  +hq1 : {Nat.is_lt(q, P.Nat.pw(w)) == True{} : Bool} = Equal.trans(Bool, Nat.is_lt(q, P.Nat.pw(w)), RD.Nat.lt(q, P.Nat.pw(w)), True{}, P2.Lt.eq(q, P.Nat.pw(w)),
    Equal.trans(Bool, RD.Nat.lt(q, P.Nat.pw(w)), RD.Nat.lt(q, RD.Nat.pow2(w)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(q, z), P.Nat.pw(w), RD.Nat.pow2(w), P2.Pw.eq(w)), hqlt))
  +hb1 : {Nat.mod(Nat.div(q, P.Nat.pw(Nat.sub(w, 1n))), 2n) == b : Nat} = Equal.trans(Nat, P2.Bitq(q, Nat.sub(w, 1n)), P2.Bitq(q, RD.Nat.monus(w, 1n)), b, Equal.cong(Nat, Nat, z => P2.Bitq(q, z), Nat.sub(w, 1n), RD.Nat.monus(w, 1n), P2.Sub.eq(w, 1n)), hb)
  +erem : {RD.Nat.monus(w, rl) == rem : Nat} = Equal.trans(Nat, RD.Nat.monus(w, rl), RD.Nat.monus(Nat.add(rl, rem), rl), rem, Equal.cong(Nat, Nat, z => RD.Nat.monus(z, rl), w, Nat.add(rl, rem), hw), R.Nat.monus_add(rl, rem))
  +hrem : {Nat.sub(w, rl) == rem : Nat} = Equal.trans(Nat, Nat.sub(w, rl), RD.Nat.monus(w, rl), rem, P2.Sub.eq(w, rl), erem)
  +hew : {Nat.is_lt(rem, es) == False{} : Bool} = Equal.trans(Bool, Nat.is_lt(rem, es), RD.Nat.lt(rem, es), False{}, P2.Lt.eq(rem, es), BP.Lt.ge(es, fb))
  +hfb : {Nat.sub(rem, es) == fb : Nat} = Equal.trans(Nat, Nat.sub(rem, es), RD.Nat.monus(rem, es), fb, P2.Sub.eq(rem, es), R.Nat.monus_add(es, fb))
  +hl : {RD.Nat.lt(low, RD.Nat.pow2(rem)) == True{} : Bool} = Low.ok(es, fb, ee, fr, hee, hfr)
  +epr : {P.Nat.pw(rem) == RD.Nat.pow2(rem) : Nat} = P2.Pw.eq(rem)
  +epf : {P.Nat.pw(fb) == RD.Nat.pow2(fb) : Nat} = P2.Pw.eq(fb)
  +hlow : {Nat.mod(q, P.Nat.pw(rem)) == lowp : Nat} = Equal.trans(Nat, Nat.mod(q, P.Nat.pw(rem)), Nat.mod(Nat.add(Nat.mul(Rr, RD.Nat.pow2(rem)), low), RD.Nat.pow2(rem)), lowp,
    Equal.trans(Nat, Nat.mod(q, P.Nat.pw(rem)), Nat.mod(q, RD.Nat.pow2(rem)), Nat.mod(Nat.add(Nat.mul(Rr, RD.Nat.pow2(rem)), low), RD.Nat.pow2(rem)),
      Equal.cong(Nat, Nat, z => Nat.mod(q, z), P.Nat.pw(rem), RD.Nat.pow2(rem), epr), Equal.cong(Nat, Nat, z => Nat.mod(z, RD.Nat.pow2(rem)), q, Nat.add(Nat.mul(Rr, RD.Nat.pow2(rem)), low), hq)),
    Equal.trans(Nat, Nat.mod(Nat.add(Nat.mul(Rr, RD.Nat.pow2(rem)), low), RD.Nat.pow2(rem)), low, lowp, P3.Dv.r(Rr, low, rem, hl),
      Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(ee, z), fr), RD.Nat.pow2(fb), P.Nat.pw(fb), Equal.sym(Nat, P.Nat.pw(fb), RD.Nat.pow2(fb), epf))))
  +s1 : {P.Pz.dec(1n+h1, 1n+w, es, rs, q) == P2.Dfin(1n+h1, es, rs, False{}, b, k, fb, ee, fr) : SB.Bd} = P2.Dec.core(1n+h1, es, rs, w, q, b, k, rl, rem, fb, ee, fr, hq1, hb1, hk, hrl, hrem, hew, hfb, hlow, hfr)
  +tbx = Bool.pick(Nat, Nat.is_eq(b, 1n), Nat.sub(Nat.add(k, rs), 1n), Nat.sub(rs, k))
  +s2 : {SB.Bd.val(1n+h1, P2.Dfin(1n+h1, es, rs, False{}, b, k, fb, ee, fr)) == VF(rs, fb, ee, fr, P.Nat.pw(es), P.Nat.pw(fb), tbx) : D.Dy} = Dfin.val(h1, es, rs, b, k, fb, ee, fr)
  +s3 = Equal.cong(Nat, D.Dy, z => VF(rs, fb, ee, fr, z, P.Nat.pw(fb), tbx), P.Nat.pw(es), RD.Nat.pow2(es), P2.Pw.eq(es))
  +s4 = Equal.cong(Nat, D.Dy, z => VF(rs, fb, ee, fr, RD.Nat.pow2(es), z, tbx), P.Nat.pw(fb), RD.Nat.pow2(fb), epf)
  +s5 = Equal.cong(Nat, D.Dy, z => VF(rs, fb, ee, fr, RD.Nat.pow2(es), RD.Nat.pow2(fb), z), tbx, rb, htb)
  Equal.trans(D.Dy, SB.Bd.val(1n+h1, P.Pz.dec(1n+h1, 1n+w, es, rs, q)), SB.Bd.val(1n+h1, P2.Dfin(1n+h1, es, rs, False{}, b, k, fb, ee, fr)), VF(rs, fb, ee, fr, RD.Nat.pow2(es), RD.Nat.pow2(fb), rb),
    Equal.cong(SB.Bd, D.Dy, z => SB.Bd.val(1n+h1, z), P.Pz.dec(1n+h1, 1n+w, es, rs, q), P2.Dfin(1n+h1, es, rs, False{}, b, k, fb, ee, fr), s1),
  Equal.trans(D.Dy, SB.Bd.val(1n+h1, P2.Dfin(1n+h1, es, rs, False{}, b, k, fb, ee, fr)), VF(rs, fb, ee, fr, P.Nat.pw(es), P.Nat.pw(fb), tbx), VF(rs, fb, ee, fr, RD.Nat.pow2(es), RD.Nat.pow2(fb), rb), s2,
  Equal.trans(D.Dy, VF(rs, fb, ee, fr, P.Nat.pw(es), P.Nat.pw(fb), tbx), VF(rs, fb, ee, fr, RD.Nat.pow2(es), P.Nat.pw(fb), tbx), VF(rs, fb, ee, fr, RD.Nat.pow2(es), RD.Nat.pow2(fb), rb), s3,
  Equal.trans(D.Dy, VF(rs, fb, ee, fr, RD.Nat.pow2(es), P.Nat.pw(fb), tbx), VF(rs, fb, ee, fr, RD.Nat.pow2(es), RD.Nat.pow2(fb), tbx), VF(rs, fb, ee, fr, RD.Nat.pow2(es), RD.Nat.pow2(fb), rb), s4, s5))))

# Fields
# ------
# A format is p0 = p01 + 1 bits of precision at least, es exponent bits
# and regime length at most rs: w = p01 + es + rs bits after the sign. In
# class rb the regime run is k, of bit b, and the regime field R is rl
# bits long; then fb = p01 + (rs - rl) fraction bits remain.

def W(+p01: Nat, +es: Nat, +rs: Nat) -> Nat:
  Nat.add(p01, Nat.add(es, rs))

def Kc(+rs: Nat, +rb: Nat) -> Nat:
  Bool.pick(Nat, RD.Nat.lt(rb, rs), RD.Nat.monus(rs, rb), 1n+RD.Nat.monus(rb, rs))

def Bc(+rs: Nat, +rb: Nat) -> Nat:
  Bool.pick(Nat, RD.Nat.lt(rb, rs), 0n, 1n)

def RgB(+z: Bool, +s: Bool, +k: Nat) -> Nat:
  Bool.pick(Nat, z, Bool.pick(Nat, s, 1n, 0n), Nat.mul(RD.Nat.monus(RD.Nat.pow2(k), 1n), Bool.pick(Nat, s, 2n, 1n)))

# the regime field: 0..01, 0..0, 1..10 or 1..1
def Rg(+rs: Nat, +rb: Nat) -> Nat:
  RgB(RD.Nat.lt(rb, rs), RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb))

def Pat(+p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat) -> Nat:
  +fb = P3.Fb(p01, rs, rb)
  Nat.add(Nat.add(Nat.mul(Rg(rs, rb), RD.Nat.pow2(Nat.add(es, fb))), Nat.mul(ee, RD.Nat.pow2(fb))), fr)

def Val(+p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat) -> D.Dy:
  VF(rs, P3.Fb(p01, rs, rb), ee, fr, RD.Nat.pow2(es), RD.Nat.pow2(P3.Fb(p01, rs, rb)), rb)

def Min.le.go(+a: Nat, +b: Nat, l: Bool, +el: {RD.Nat.lt(a, b) == l : Bool}) -> {RD.Nat.lt(b, Bool.pick(Nat, l, a, b)) == False{} : Bool}:
  match l:
    case True{}:
      BP.Lt.asym(a, b, el)
    case False{}:
      Lt.irr(b)

def Min.le(+a: Nat, +b: Nat) -> {RD.Nat.lt(b, P.Pz.min(a, b)) == False{} : Bool}:
  Min.le.go(a, b, RD.Nat.lt(a, b), {==})

def Rl.le.go(+rs: Nat, +rb: Nat, l: Bool, +el: {RD.Nat.lt(rb, rs) == l : Bool})
  -> {RD.Nat.lt(rs, Bool.pick(Nat, l, P.Pz.min(1n+RD.Nat.monus(rs, rb), rs), P.Pz.min(2n+RD.Nat.monus(rb, rs), rs))) == False{} : Bool}:
  match l:
    case True{}:
      Min.le(1n+RD.Nat.monus(rs, rb), rs)
    case False{}:
      Min.le(2n+RD.Nat.monus(rb, rs), rs)

# w = rl + es + fb

def Rl.le(+rs: Nat, +rb: Nat) -> {RD.Nat.lt(rs, P.Pz.rl(rs, rb)) == False{} : Bool}:
  Rl.le.go(rs, rb, RD.Nat.lt(rb, rs), {==})

def W.split(+p01: Nat, +es: Nat, +rs: Nat, +rb: Nat) -> {W(p01, es, rs) == Nat.add(P.Pz.rl(rs, rb), Nat.add(es, P3.Fb(p01, rs, rb))) : Nat}:
  +rl = P.Pz.rl(rs, rb)
  +c = RD.Nat.monus(rs, rl)
  +ers : {rs == Nat.add(rl, c) : Nat} = E.Le.wit(rl, rs, Rl.le(rs, rb))
  +env : List<&2, Nat> = [p01, es, rs, rl, c]
  R.NatN.eq2(env, R.Ad(R.V(0n), R.Ad(R.V(1n), R.V(2n))), R.Ad(R.V(3n), R.Ad(R.V(1n), R.Ad(R.V(0n), R.V(4n)))), [], [], [R.Ad(R.V(2n), R.Ng(R.Ad(R.V(3n), R.V(4n))))], {==}, Unit{}, (R.NatN.z(env, R.V(2n), R.Ad(R.V(3n), R.V(4n)), {==}, {==}, ers), Unit{}), {==}, {==})

# Q(b, k, v, low) < 2^(k + v)
def Q.lt(+k: Nat, +v: Nat, +b: Nat, +low: Nat, +hb: {RD.Nat.lt(1n, b) == False{} : Bool}, +hl: {RD.Nat.lt(low, RD.Nat.pow2(v)) == True{} : Bool})
  -> {RD.Nat.lt(Q(b, k, v, low), RD.Nat.pow2(Nat.add(k, v))) == True{} : Bool}:
  +M = RD.Nat.monus(RD.Nat.pow2(k), 1n)
  +Pv = RD.Nat.pow2(v)
  +Pk = RD.Nat.pow2(k)
  +X = Nat.mul(M, Pv)
  +l1 : {RD.Nat.lt(Q(b, k, v, low), Nat.add(Nat.mul(b, X), Pv)) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Nat.add(Nat.mul(b, X), low), Nat.add(Nat.mul(b, X), Pv)), RD.Nat.lt(low, Pv), True{}, BP.Lt.shift(Nat.mul(b, X), low, Pv), hl)
  +l2 : {RD.Nat.lt(Nat.add(X, Pv), Nat.add(Nat.mul(b, X), Pv)) == False{} : Bool} = E2.Le.addr(Nat.mul(b, X), X, Pv, E.Le.trans(Nat.mul(b, X), Nat.mul(1n, X), X, E2.Le.mulr(b, 1n, X, hb), E.Le.eq(Nat.mul(1n, X), X, P3.Mul.one_l(X))))
  +ek : {Pk == 1n+M : Nat} = P2.Pw.pos(k)
  +ekv : {RD.Nat.pow2(Nat.add(k, v)) == Nat.mul(Pk, Pv) : Nat} = BP.Pow2.add(k, v)
  +e3 : {Nat.add(X, Pv) == RD.Nat.pow2(Nat.add(k, v)) : Nat} = Equal.trans(Nat, Nat.add(X, Pv), Nat.mul(1n+M, Pv), RD.Nat.pow2(Nat.add(k, v)), NL.Nat.add_comm(X, Pv),
    Equal.trans(Nat, Nat.mul(1n+M, Pv), Nat.mul(Pk, Pv), RD.Nat.pow2(Nat.add(k, v)), Equal.cong(Nat, Nat, z => Nat.mul(z, Pv), 1n+M, Pk, Equal.sym(Nat, Pk, 1n+M, ek)), Equal.sym(Nat, RD.Nat.pow2(Nat.add(k, v)), Nat.mul(Pk, Pv), ekv)))
  E2.Lt.le_trans(Q(b, k, v, low), Nat.add(Nat.mul(b, X), Pv), RD.Nat.pow2(Nat.add(k, v)), l1, E.Le.trans(Nat.add(Nat.mul(b, X), Pv), Nat.add(X, Pv), RD.Nat.pow2(Nat.add(k, v)), l2, E.Le.eq(Nat.add(X, Pv), RD.Nat.pow2(Nat.add(k, v)), e3)))

def Top(+k: Nat, +v: Nat, +b: Nat, +low: Nat, +hk: {RD.Nat.lt(0n, k) == True{} : Bool}, +hb: {RD.Nat.lt(1n, b) == False{} : Bool}, +hl: {RD.Nat.lt(low, RD.Nat.pow2(v)) == True{} : Bool})
  -> {P2.Bitq(Q(b, k, v, low), RD.Nat.monus(Nat.add(k, v), 1n)) == b : Nat}:
  match k:
    case 0n:
      B.Bool.tf({P2.Bitq(Q(b, 0n, v, low), RD.Nat.monus(Nat.add(0n, v), 1n)) == b : Nat}, Equal.sym(Bool, False{}, True{}, hk))
    case 1n+(+k1):
      Q.top(k1, v, b, Q(b, 1n+k1, v, low), Q.bits(1n+k1, v, b, low, hb, hl))

# the decoder on Pat, once Pat is k bits b above a v-bit field
def Dec.q(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +b: Nat, +k: Nat, +v: Nat, +lq: Nat,
  +hb01: {RD.Nat.lt(1n, b) == False{} : Bool}, +hk1: {RD.Nat.lt(0n, k) == True{} : Bool},
  +hqQ: {Pat(p01, es, rs, rb, ee, fr) == Q(b, k, v, lq) : Nat}, +hwk: {W(p01, es, rs) == Nat.add(k, v) : Nat},
  +hlq: {RD.Nat.lt(lq, RD.Nat.pow2(v)) == True{} : Bool},
  +hrun: {P.Pz.run(rs, Q(b, k, v, lq), Nat.add(k, v), b) == k : Nat},
  +hrl: {Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs) == P.Pz.rl(rs, rb) : Nat},
  +htb: {Bool.pick(Nat, Nat.is_eq(b, 1n), Nat.sub(Nat.add(k, rs), 1n), Nat.sub(rs, k)) == rb : Nat},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool},
  +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool})
  -> {SB.Bd.val(1n+h1, P.Pz.dec(1n+h1, 1n+W(p01, es, rs), es, rs, Pat(p01, es, rs, rb, ee, fr))) == Val(p01, es, rs, rb, ee, fr) : D.Dy}:
  +w = W(p01, es, rs)
  +q = Pat(p01, es, rs, rb, ee, fr)
  +qq = Q(b, k, v, lq)
  +fb = P3.Fb(p01, rs, rb)
  +hqlt : {RD.Nat.lt(q, RD.Nat.pow2(w)) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(q, RD.Nat.pow2(w)), RD.Nat.lt(qq, RD.Nat.pow2(Nat.add(k, v))), True{},
    Equal.trans(Bool, RD.Nat.lt(q, RD.Nat.pow2(w)), RD.Nat.lt(qq, RD.Nat.pow2(w)), RD.Nat.lt(qq, RD.Nat.pow2(Nat.add(k, v))),
      Equal.cong(Nat, Bool, z => RD.Nat.lt(z, RD.Nat.pow2(w)), q, qq, hqQ), Equal.cong(Nat, Bool, z => RD.Nat.lt(qq, RD.Nat.pow2(z)), w, Nat.add(k, v), hwk)),
    Q.lt(k, v, b, lq, hb01, hlq))
  +hb : {P2.Bitq(q, RD.Nat.monus(w, 1n)) == b : Nat} = Equal.trans(Nat, P2.Bitq(q, RD.Nat.monus(w, 1n)), P2.Bitq(qq, RD.Nat.monus(Nat.add(k, v), 1n)), b,
    Equal.trans(Nat, P2.Bitq(q, RD.Nat.monus(w, 1n)), P2.Bitq(qq, RD.Nat.monus(w, 1n)), P2.Bitq(qq, RD.Nat.monus(Nat.add(k, v), 1n)),
      Equal.cong(Nat, Nat, z => P2.Bitq(z, RD.Nat.monus(w, 1n)), q, qq, hqQ), Equal.cong(Nat, Nat, z => P2.Bitq(qq, RD.Nat.monus(z, 1n)), w, Nat.add(k, v), hwk)),
    Top(k, v, b, lq, hk1, hb01, hlq))
  +hk : {P.Pz.run(rs, q, w, b) == k : Nat} = Equal.trans(Nat, P.Pz.run(rs, q, w, b), P.Pz.run(rs, qq, Nat.add(k, v), b), k,
    Equal.trans(Nat, P.Pz.run(rs, q, w, b), P.Pz.run(rs, qq, w, b), P.Pz.run(rs, qq, Nat.add(k, v), b),
      Equal.cong(Nat, Nat, z => P.Pz.run(rs, z, w, b), q, qq, hqQ), Equal.cong(Nat, Nat, z => P.Pz.run(rs, qq, z, b), w, Nat.add(k, v), hwk)),
    hrun)
  +hq : {q == Nat.add(Nat.mul(Rg(rs, rb), RD.Nat.pow2(Nat.add(es, fb))), Nat.add(Nat.mul(ee, RD.Nat.pow2(fb)), fr)) : Nat} = NL.Nat.add_assoc(Nat.mul(Rg(rs, rb), RD.Nat.pow2(Nat.add(es, fb))), Nat.mul(ee, RD.Nat.pow2(fb)), fr)
  Dec.gen(h1, es, rs, w, q, b, k, P.Pz.rl(rs, rb), fb, ee, fr, rb, Rg(rs, rb), W.split(p01, es, rs, rb), hqlt, hb, hk, hrl, hq, hee, hfr, htb)

# Small facts for the regime cases
# --------------------------------

def Ne10(e: {1n == 0n : Nat}) -> Empty:
  B.Bool.tf.empty(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n), 1n, 0n, e))

def Ne01(e: {0n == 1n : Nat}) -> Empty:
  B.Bool.tf.empty(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 0n, 1n, e))

def Lt.sa(+a: Nat) -> {RD.Nat.lt(1n+a, a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+(+a2):
      Lt.sa(a2)

def Min.succ.go(+k: Nat, +rs: Nat, +hk: {RD.Nat.lt(k, rs) == True{} : Bool}, l: Bool, +el: {RD.Nat.lt(1n+k, rs) == l : Bool}) -> {Bool.pick(Nat, l, 1n+k, rs) == 1n+k : Nat}:
  match l:
    case True{}:
      {==}
    case False{}:
      E2.Le.anti(rs, 1n+k, el, E2.Le.succ(k, rs, hk))

# min(k + 1, rs) = k + 1 for k < rs
def Min.succ(+k: Nat, +rs: Nat, +hk: {RD.Nat.lt(k, rs) == True{} : Bool}) -> {P.Pz.min(1n+k, rs) == 1n+k : Nat}:
  Min.succ.go(k, rs, hk, RD.Nat.lt(1n+k, rs), {==})

def Min.top(+rs: Nat) -> {P.Pz.min(1n+rs, rs) == rs : Nat}:
  Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 1n+rs, rs), RD.Nat.lt(1n+rs, rs), False{}, Lt.sa(rs))

# rs - (rs - rb) = rb for rb <= rs
def Mo.mo(+rs: Nat, +rb: Nat, +hle: {RD.Nat.lt(rs, rb) == False{} : Bool}) -> {RD.Nat.monus(rs, RD.Nat.monus(rs, rb)) == rb : Nat}:
  +c = RD.Nat.monus(rs, rb)
  +ers : {rs == Nat.add(rb, c) : Nat} = E.Le.wit(rb, rs, hle)
  +e1 : {RD.Nat.monus(rs, c) == RD.Nat.monus(Nat.add(c, rb), c) : Nat} = Equal.cong(Nat, Nat, z => RD.Nat.monus(z, c), rs, Nat.add(c, rb), Equal.trans(Nat, rs, Nat.add(rb, c), Nat.add(c, rb), ers, NL.Nat.add_comm(rb, c)))
  Equal.trans(Nat, RD.Nat.monus(rs, c), RD.Nat.monus(Nat.add(c, rb), c), rb, e1, R.Nat.monus_add(c, rb))

# rs - rb > 0 for rb < rs
def Mo.pos(+rb: Nat, +rs: Nat, +h: {RD.Nat.lt(rb, rs) == True{} : Bool}) -> {RD.Nat.lt(0n, RD.Nat.monus(rs, rb)) == True{} : Bool}:
  +c = RD.Nat.monus(rs, 1n+rb)
  +ers : {rs == Nat.add(rb, 1n+c) : Nat} = Equal.trans(Nat, rs, Nat.add(1n+rb, c), Nat.add(rb, 1n+c), BP.Lt.wit(rb, rs)(h), Equal.sym(Nat, Nat.add(rb, 1n+c), 1n+Nat.add(rb, c), NL.Nat.add_succ_r(rb, c)))
  +e : {RD.Nat.monus(rs, rb) == 1n+c : Nat} = Equal.trans(Nat, RD.Nat.monus(rs, rb), RD.Nat.monus(Nat.add(rb, 1n+c), rb), 1n+c, Equal.cong(Nat, Nat, z => RD.Nat.monus(z, rb), rs, Nat.add(rb, 1n+c), ers), R.Nat.monus_add(rb, 1n+c))
  Equal.cong(Nat, Bool, z => RD.Nat.lt(0n, z), RD.Nat.monus(rs, rb), 1n+c, e)

# rb + rs = rs gives rb = 0
def Add.z(+rb: Nat, +rs: Nat, +e: {Nat.add(rb, rs) == rs : Nat}) -> {rb == 0n : Nat}:
  match rb:
    case 0n:
      {==}
    case 1n+(+r):
      Empty.absurd({1n+r == 0n : Nat}, BP.Ne.self(rs, r, Equal.trans(Nat, Nat.add(rs, 1n+r), Nat.add(1n+r, rs), rs, NL.Nat.add_comm(rs, 1n+r), e)))

# The four regime cases
# ---------------------

# zeros, a short run (rb >= 1): regime 0..01, k = rs - rb
def Dec.zs(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat,
  +hz: {RD.Nat.lt(rb, rs) == True{} : Bool}, +hs: {RD.Nat.lt(RD.Nat.monus(rs, rb), rs) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool})
  -> {SB.Bd.val(1n+h1, P.Pz.dec(1n+h1, 1n+W(p01, es, rs), es, rs, Pat(p01, es, rs, rb, ee, fr))) == Val(p01, es, rs, rb, ee, fr) : D.Dy}:
  +fb = P3.Fb(p01, rs, rb)
  +rem = Nat.add(es, fb)
  +Pr = RD.Nat.pow2(rem)
  +A = Nat.mul(ee, RD.Nat.pow2(fb))
  +low = Nat.add(A, fr)
  +k = RD.Nat.monus(rs, rb)
  +eK : {Kc(rs, rb) == k : Nat} = Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, RD.Nat.monus(rs, rb), 1n+RD.Nat.monus(rb, rs)), RD.Nat.lt(rb, rs), True{}, hz)
  +eS : {RD.Nat.lt(Kc(rs, rb), rs) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Kc(rs, rb), rs), RD.Nat.lt(k, rs), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, rs), Kc(rs, rb), k, eK), hs)
  +eR : {Rg(rs, rb) == 1n : Nat} = Equal.trans(Nat, Rg(rs, rb), RgB(True{}, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), 1n,
    Equal.cong(Bool, Nat, z => RgB(z, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), RD.Nat.lt(rb, rs), True{}, hz),
    Equal.cong(Bool, Nat, z => RgB(True{}, z, Kc(rs, rb)), RD.Nat.lt(Kc(rs, rb), rs), True{}, eS))
  +erl : {P.Pz.rl(rs, rb) == 1n+k : Nat} = Equal.trans(Nat, P.Pz.rl(rs, rb), P.Pz.min(1n+k, rs), 1n+k,
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, P.Pz.min(1n+RD.Nat.monus(rs, rb), rs), P.Pz.min(2n+RD.Nat.monus(rb, rs), rs)), RD.Nat.lt(rb, rs), True{}, hz), Min.succ(k, rs, hs))
  +hqQ : {Pat(p01, es, rs, rb, ee, fr) == Q(0n, k, 1n+rem, Nat.add(Nat.mul(1n, Pr), low)) : Nat} = Equal.trans(Nat, Pat(p01, es, rs, rb, ee, fr), Nat.add(Nat.add(Nat.mul(1n, Pr), A), fr), Nat.add(Nat.mul(1n, Pr), low),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.mul(z, Pr), A), fr), Rg(rs, rb), 1n, eR), NL.Nat.add_assoc(Nat.mul(1n, Pr), A, fr))
  +hwk : {W(p01, es, rs) == Nat.add(k, 1n+rem) : Nat} = Equal.trans(Nat, W(p01, es, rs), Nat.add(P.Pz.rl(rs, rb), rem), Nat.add(k, 1n+rem), W.split(p01, es, rs, rb),
    Equal.trans(Nat, Nat.add(P.Pz.rl(rs, rb), rem), Nat.add(1n+k, rem), Nat.add(k, 1n+rem), Equal.cong(Nat, Nat, z => Nat.add(z, rem), P.Pz.rl(rs, rb), 1n+k, erl), Equal.sym(Nat, Nat.add(k, 1n+rem), 1n+Nat.add(k, rem), NL.Nat.add_succ_r(k, rem))))
  +hl : {RD.Nat.lt(low, Pr) == True{} : Bool} = Low.ok(es, fb, ee, fr, hee, hfr)
  +hrl : {Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs) == P.Pz.rl(rs, rb) : Nat} = Equal.trans(Nat, Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs), 1n+k, P.Pz.rl(rs, rb),
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 1n+k, rs), Nat.is_lt(k, rs), True{}, Equal.trans(Bool, Nat.is_lt(k, rs), RD.Nat.lt(k, rs), True{}, P2.Lt.eq(k, rs), hs)), Equal.sym(Nat, P.Pz.rl(rs, rb), 1n+k, erl))
  +htb : {Bool.pick(Nat, Nat.is_eq(0n, 1n), Nat.sub(Nat.add(k, rs), 1n), Nat.sub(rs, k)) == rb : Nat} = Equal.trans(Nat, Nat.sub(rs, k), RD.Nat.monus(rs, k), rb, P2.Sub.eq(rs, k), Mo.mo(rs, rb, BP.Lt.asym(rb, rs, hz)))
  Dec.q(h1, p01, es, rs, rb, ee, fr, 0n, k, 1n+rem, Nat.add(Nat.mul(1n, Pr), low), {==}, Mo.pos(rb, rs, hz), hqQ, hwk, Low.lt(rem, 1n, low, {==}, hl),
    Run.short(k, rem, rs, 0n, 1n, low, {==}, {==}, e => Ne10(e), BP.Lt.asym(k, rs, hs), hl), hrl, htb, hee, hfr)

# zeros, the full run (rb = 0): regime 0..0, k = rs
def Dec.zl(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool},
  +hz: {RD.Nat.lt(rb, rs) == True{} : Bool}, +hs: {RD.Nat.lt(RD.Nat.monus(rs, rb), rs) == False{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool})
  -> {SB.Bd.val(1n+h1, P.Pz.dec(1n+h1, 1n+W(p01, es, rs), es, rs, Pat(p01, es, rs, rb, ee, fr))) == Val(p01, es, rs, rb, ee, fr) : D.Dy}:
  +fb = P3.Fb(p01, rs, rb)
  +rem = Nat.add(es, fb)
  +Pr = RD.Nat.pow2(rem)
  +A = Nat.mul(ee, RD.Nat.pow2(fb))
  +low = Nat.add(A, fr)
  +c = RD.Nat.monus(rs, rb)
  +eK : {Kc(rs, rb) == c : Nat} = Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, RD.Nat.monus(rs, rb), 1n+RD.Nat.monus(rb, rs)), RD.Nat.lt(rb, rs), True{}, hz)
  +eS : {RD.Nat.lt(Kc(rs, rb), rs) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Kc(rs, rb), rs), RD.Nat.lt(c, rs), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, rs), Kc(rs, rb), c, eK), hs)
  +eR : {Rg(rs, rb) == 0n : Nat} = Equal.trans(Nat, Rg(rs, rb), RgB(True{}, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), 0n,
    Equal.cong(Bool, Nat, z => RgB(z, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), RD.Nat.lt(rb, rs), True{}, hz),
    Equal.cong(Bool, Nat, z => RgB(True{}, z, Kc(rs, rb)), RD.Nat.lt(Kc(rs, rb), rs), False{}, eS))
  +ers : {rs == Nat.add(rb, c) : Nat} = E.Le.wit(rb, rs, BP.Lt.asym(rb, rs, hz))
  +hcle : {RD.Nat.lt(rs, c) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(rs, c), RD.Nat.lt(Nat.add(c, rb), c), False{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(z, c), rs, Nat.add(c, rb), Equal.trans(Nat, rs, Nat.add(rb, c), Nat.add(c, rb), ers, NL.Nat.add_comm(rb, c))), BP.Lt.ge(c, rb))
  +ec : {c == rs : Nat} = E2.Le.anti(c, rs, hcle, hs)
  +erl : {P.Pz.rl(rs, rb) == rs : Nat} = Equal.trans(Nat, P.Pz.rl(rs, rb), P.Pz.min(1n+c, rs), rs,
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, P.Pz.min(1n+RD.Nat.monus(rs, rb), rs), P.Pz.min(2n+RD.Nat.monus(rb, rs), rs)), RD.Nat.lt(rb, rs), True{}, hz),
    Equal.trans(Nat, P.Pz.min(1n+c, rs), P.Pz.min(1n+rs, rs), rs, Equal.cong(Nat, Nat, z => P.Pz.min(1n+z, rs), c, rs, ec), Min.top(rs)))
  +erb : {rb == 0n : Nat} = Add.z(rb, rs, Equal.sym(Nat, rs, Nat.add(rb, rs), Equal.trans(Nat, rs, Nat.add(rb, c), Nat.add(rb, rs), ers, Equal.cong(Nat, Nat, z => Nat.add(rb, z), c, rs, ec))))
  +hqQ : {Pat(p01, es, rs, rb, ee, fr) == Q(0n, rs, rem, low) : Nat} = Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.mul(z, Pr), A), fr), Rg(rs, rb), 0n, eR)
  +hwk : {W(p01, es, rs) == Nat.add(rs, rem) : Nat} = Equal.trans(Nat, W(p01, es, rs), Nat.add(P.Pz.rl(rs, rb), rem), Nat.add(rs, rem), W.split(p01, es, rs, rb), Equal.cong(Nat, Nat, z => Nat.add(z, rem), P.Pz.rl(rs, rb), rs, erl))
  +hl : {RD.Nat.lt(low, Pr) == True{} : Bool} = Low.ok(es, fb, ee, fr, hee, hfr)
  +hrl : {Bool.pick(Nat, Nat.is_lt(rs, rs), 1n+rs, rs) == P.Pz.rl(rs, rb) : Nat} = Equal.trans(Nat, Bool.pick(Nat, Nat.is_lt(rs, rs), 1n+rs, rs), rs, P.Pz.rl(rs, rb),
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 1n+rs, rs), Nat.is_lt(rs, rs), False{}, Equal.trans(Bool, Nat.is_lt(rs, rs), RD.Nat.lt(rs, rs), False{}, P2.Lt.eq(rs, rs), Lt.irr(rs))), Equal.sym(Nat, P.Pz.rl(rs, rb), rs, erl))
  +htb : {Bool.pick(Nat, Nat.is_eq(0n, 1n), Nat.sub(Nat.add(rs, rs), 1n), Nat.sub(rs, rs)) == rb : Nat} = Equal.trans(Nat, Nat.sub(rs, rs), 0n, rb, P2.Sub.self(rs), Equal.sym(Nat, rb, 0n, erb))
  Dec.q(h1, p01, es, rs, rb, ee, fr, 0n, rs, rem, low, {==}, hrs, hqQ, hwk, hl, Run.full(rs, rem, 0n, low, {==}, hl), hrl, htb, hee, hfr)

# ones, a short run: regime 1..10, k = rb - rs + 1
def Dec.os(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat,
  +hz: {RD.Nat.lt(rb, rs) == False{} : Bool}, +hs: {RD.Nat.lt(1n+RD.Nat.monus(rb, rs), rs) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool})
  -> {SB.Bd.val(1n+h1, P.Pz.dec(1n+h1, 1n+W(p01, es, rs), es, rs, Pat(p01, es, rs, rb, ee, fr))) == Val(p01, es, rs, rb, ee, fr) : D.Dy}:
  +fb = P3.Fb(p01, rs, rb)
  +rem = Nat.add(es, fb)
  +Pr = RD.Nat.pow2(rem)
  +P1 = RD.Nat.pow2(1n+rem)
  +A = Nat.mul(ee, RD.Nat.pow2(fb))
  +low = Nat.add(A, fr)
  +d = RD.Nat.monus(rb, rs)
  +k : Nat = 1n+d
  +M = RD.Nat.monus(RD.Nat.pow2(k), 1n)
  +eK : {Kc(rs, rb) == k : Nat} = Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, RD.Nat.monus(rs, rb), 1n+RD.Nat.monus(rb, rs)), RD.Nat.lt(rb, rs), False{}, hz)
  +eS : {RD.Nat.lt(Kc(rs, rb), rs) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Kc(rs, rb), rs), RD.Nat.lt(k, rs), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, rs), Kc(rs, rb), k, eK), hs)
  +eR : {Rg(rs, rb) == Nat.mul(M, 2n) : Nat} = Equal.trans(Nat, Rg(rs, rb), RgB(False{}, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), Nat.mul(M, 2n),
    Equal.cong(Bool, Nat, z => RgB(z, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), RD.Nat.lt(rb, rs), False{}, hz),
    Equal.trans(Nat, RgB(False{}, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), RgB(False{}, True{}, Kc(rs, rb)), Nat.mul(M, 2n),
      Equal.cong(Bool, Nat, z => RgB(False{}, z, Kc(rs, rb)), RD.Nat.lt(Kc(rs, rb), rs), True{}, eS),
      Equal.cong(Nat, Nat, z => RgB(False{}, True{}, z), Kc(rs, rb), k, eK)))
  +erl : {P.Pz.rl(rs, rb) == 1n+k : Nat} = Equal.trans(Nat, P.Pz.rl(rs, rb), P.Pz.min(1n+k, rs), 1n+k,
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, P.Pz.min(1n+RD.Nat.monus(rs, rb), rs), P.Pz.min(2n+RD.Nat.monus(rb, rs), rs)), RD.Nat.lt(rb, rs), False{}, hz), Min.succ(k, rs, hs))
  +eM2 : {Nat.mul(M, 2n) == Nat.add(M, M) : Nat} = Equal.trans(Nat, Nat.mul(M, 2n), Nat.add(M, Nat.mul(M, 1n)), Nat.add(M, M), NL.Nat.mul_succ_r(M, 1n), Equal.cong(Nat, Nat, z => Nat.add(M, z), Nat.mul(M, 1n), M, NL.Nat.mul_one_r(M)))
  +e1 : {P1 == Nat.add(Pr, Pr) : Nat} = Y.Nat.double_add(Pr)
  +env : List<&2, Nat> = [M, Pr, P1, A, fr]
  +eN : {Nat.add(Nat.add(Nat.mul(Nat.add(M, M), Pr), A), fr) == Nat.add(Nat.mul(M, P1), low) : Nat} = R.NatN.eq(env, R.Ad(R.Ad(R.Ml(R.Ad(R.V(0n), R.V(0n)), R.V(1n)), R.V(3n)), R.V(4n)), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ad(R.V(3n), R.V(4n))), [R.Ng(R.V(0n))], [R.Ad(R.V(2n), R.Ng(R.Ad(R.V(1n), R.V(1n))))], {==}, (R.NatN.z(env, R.V(2n), R.Ad(R.V(1n), R.V(1n)), {==}, {==}, e1), Unit{}), {==}, {==})
  +hqQ : {Pat(p01, es, rs, rb, ee, fr) == Q(1n, k, 1n+rem, Nat.add(Nat.mul(0n, Pr), low)) : Nat} = Equal.trans(Nat, Pat(p01, es, rs, rb, ee, fr), Nat.add(Nat.add(Nat.mul(Nat.mul(M, 2n), Pr), A), fr), Q(1n, k, 1n+rem, Nat.add(Nat.mul(0n, Pr), low)),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.mul(z, Pr), A), fr), Rg(rs, rb), Nat.mul(M, 2n), eR),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(M, 2n), Pr), A), fr), Nat.add(Nat.add(Nat.mul(Nat.add(M, M), Pr), A), fr), Q(1n, k, 1n+rem, Nat.add(Nat.mul(0n, Pr), low)),
      Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.mul(z, Pr), A), fr), Nat.mul(M, 2n), Nat.add(M, M), eM2),
      Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.add(M, M), Pr), A), fr), Nat.add(Nat.mul(M, P1), low), Q(1n, k, 1n+rem, Nat.add(Nat.mul(0n, Pr), low)), eN,
        Equal.cong(Nat, Nat, z => Nat.add(z, low), Nat.mul(M, P1), Nat.mul(1n, Nat.mul(M, P1)), Equal.sym(Nat, Nat.mul(1n, Nat.mul(M, P1)), Nat.mul(M, P1), P3.Mul.one_l(Nat.mul(M, P1)))))))
  +hwk : {W(p01, es, rs) == Nat.add(k, 1n+rem) : Nat} = Equal.trans(Nat, W(p01, es, rs), Nat.add(P.Pz.rl(rs, rb), rem), Nat.add(k, 1n+rem), W.split(p01, es, rs, rb),
    Equal.trans(Nat, Nat.add(P.Pz.rl(rs, rb), rem), Nat.add(1n+k, rem), Nat.add(k, 1n+rem), Equal.cong(Nat, Nat, z => Nat.add(z, rem), P.Pz.rl(rs, rb), 1n+k, erl), Equal.sym(Nat, Nat.add(k, 1n+rem), 1n+Nat.add(k, rem), NL.Nat.add_succ_r(k, rem))))
  +hl : {RD.Nat.lt(low, Pr) == True{} : Bool} = Low.ok(es, fb, ee, fr, hee, hfr)
  +hrl : {Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs) == P.Pz.rl(rs, rb) : Nat} = Equal.trans(Nat, Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs), 1n+k, P.Pz.rl(rs, rb),
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 1n+k, rs), Nat.is_lt(k, rs), True{}, Equal.trans(Bool, Nat.is_lt(k, rs), RD.Nat.lt(k, rs), True{}, P2.Lt.eq(k, rs), hs)), Equal.sym(Nat, P.Pz.rl(rs, rb), 1n+k, erl))
  +erb : {rb == Nat.add(rs, d) : Nat} = E.Le.wit(rs, rb, hz)
  +htb : {Bool.pick(Nat, Nat.is_eq(1n, 1n), Nat.sub(Nat.add(k, rs), 1n), Nat.sub(rs, k)) == rb : Nat} = Equal.trans(Nat, Nat.sub(Nat.add(d, rs), 0n), Nat.add(d, rs), rb, P2.Sub.z(Nat.add(d, rs)),
    Equal.trans(Nat, Nat.add(d, rs), Nat.add(rs, d), rb, NL.Nat.add_comm(d, rs), Equal.sym(Nat, rb, Nat.add(rs, d), erb)))
  Dec.q(h1, p01, es, rs, rb, ee, fr, 1n, k, 1n+rem, Nat.add(Nat.mul(0n, Pr), low), {==}, {==}, hqQ, hwk, Low.lt(rem, 0n, low, {==}, hl),
    Run.short(k, rem, rs, 1n, 0n, low, {==}, {==}, e => Ne01(e), BP.Lt.asym(k, rs, hs), hl), hrl, htb, hee, hfr)

# ones, the full run (rb = 2 rs - 1): regime 1..1, k = rs
def Dec.ol(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool},
  +hz: {RD.Nat.lt(rb, rs) == False{} : Bool}, +hs: {RD.Nat.lt(1n+RD.Nat.monus(rb, rs), rs) == False{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool})
  -> {SB.Bd.val(1n+h1, P.Pz.dec(1n+h1, 1n+W(p01, es, rs), es, rs, Pat(p01, es, rs, rb, ee, fr))) == Val(p01, es, rs, rb, ee, fr) : D.Dy}:
  +fb = P3.Fb(p01, rs, rb)
  +rem = Nat.add(es, fb)
  +Pr = RD.Nat.pow2(rem)
  +A = Nat.mul(ee, RD.Nat.pow2(fb))
  +low = Nat.add(A, fr)
  +d = RD.Nat.monus(rb, rs)
  +M = RD.Nat.monus(RD.Nat.pow2(rs), 1n)
  +erb : {rb == Nat.add(rs, d) : Nat} = E.Le.wit(rs, rb, hz)
  +hd : {RD.Nat.lt(d, rs) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(d, rs), RD.Nat.lt(Nat.add(rs, d), Nat.add(rs, rs)), True{}, Equal.sym(Bool, RD.Nat.lt(Nat.add(rs, d), Nat.add(rs, rs)), RD.Nat.lt(d, rs), BP.Lt.shift(rs, d, rs)),
    Equal.trans(Bool, RD.Nat.lt(Nat.add(rs, d), Nat.add(rs, rs)), RD.Nat.lt(rb, Nat.double(rs)), True{},
      Equal.trans(Bool, RD.Nat.lt(Nat.add(rs, d), Nat.add(rs, rs)), RD.Nat.lt(rb, Nat.add(rs, rs)), RD.Nat.lt(rb, Nat.double(rs)), Equal.cong(Nat, Bool, z => RD.Nat.lt(z, Nat.add(rs, rs)), Nat.add(rs, d), rb, Equal.sym(Nat, rb, Nat.add(rs, d), erb)),
        Equal.cong(Nat, Bool, z => RD.Nat.lt(rb, z), Nat.add(rs, rs), Nat.double(rs), Equal.sym(Nat, Nat.double(rs), Nat.add(rs, rs), Y.Nat.double_add(rs)))), hrb))
  +ek : {1n+d == rs : Nat} = E2.Le.anti(1n+d, rs, E2.Le.succ(d, rs, hd), hs)
  +eK : {Kc(rs, rb) == rs : Nat} = Equal.trans(Nat, Kc(rs, rb), 1n+d, rs, Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, RD.Nat.monus(rs, rb), 1n+RD.Nat.monus(rb, rs)), RD.Nat.lt(rb, rs), False{}, hz), ek)
  +eS : {RD.Nat.lt(Kc(rs, rb), rs) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Kc(rs, rb), rs), RD.Nat.lt(rs, rs), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, rs), Kc(rs, rb), rs, eK), Lt.irr(rs))
  +eR : {Rg(rs, rb) == M : Nat} = Equal.trans(Nat, Rg(rs, rb), RgB(False{}, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), M,
    Equal.cong(Bool, Nat, z => RgB(z, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), RD.Nat.lt(rb, rs), False{}, hz),
    Equal.trans(Nat, RgB(False{}, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), RgB(False{}, False{}, rs), M,
      Equal.trans(Nat, RgB(False{}, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), RgB(False{}, False{}, Kc(rs, rb)), RgB(False{}, False{}, rs),
        Equal.cong(Bool, Nat, z => RgB(False{}, z, Kc(rs, rb)), RD.Nat.lt(Kc(rs, rb), rs), False{}, eS), Equal.cong(Nat, Nat, z => RgB(False{}, False{}, z), Kc(rs, rb), rs, eK)),
      NL.Nat.mul_one_r(M)))
  +erl : {P.Pz.rl(rs, rb) == rs : Nat} = Equal.trans(Nat, P.Pz.rl(rs, rb), P.Pz.min(1n+(1n+d), rs), rs,
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, P.Pz.min(1n+RD.Nat.monus(rs, rb), rs), P.Pz.min(2n+RD.Nat.monus(rb, rs), rs)), RD.Nat.lt(rb, rs), False{}, hz),
    Equal.trans(Nat, P.Pz.min(1n+(1n+d), rs), P.Pz.min(1n+rs, rs), rs, Equal.cong(Nat, Nat, z => P.Pz.min(1n+z, rs), 1n+d, rs, ek), Min.top(rs)))
  +hqQ : {Pat(p01, es, rs, rb, ee, fr) == Q(1n, rs, rem, low) : Nat} = Equal.trans(Nat, Pat(p01, es, rs, rb, ee, fr), Nat.add(Nat.add(Nat.mul(M, Pr), A), fr), Q(1n, rs, rem, low),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.mul(z, Pr), A), fr), Rg(rs, rb), M, eR),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(M, Pr), A), fr), Nat.add(Nat.mul(M, Pr), low), Q(1n, rs, rem, low), NL.Nat.add_assoc(Nat.mul(M, Pr), A, fr),
      Equal.cong(Nat, Nat, z => Nat.add(z, low), Nat.mul(M, Pr), Nat.mul(1n, Nat.mul(M, Pr)), Equal.sym(Nat, Nat.mul(1n, Nat.mul(M, Pr)), Nat.mul(M, Pr), P3.Mul.one_l(Nat.mul(M, Pr))))))
  +hwk : {W(p01, es, rs) == Nat.add(rs, rem) : Nat} = Equal.trans(Nat, W(p01, es, rs), Nat.add(P.Pz.rl(rs, rb), rem), Nat.add(rs, rem), W.split(p01, es, rs, rb), Equal.cong(Nat, Nat, z => Nat.add(z, rem), P.Pz.rl(rs, rb), rs, erl))
  +hl : {RD.Nat.lt(low, Pr) == True{} : Bool} = Low.ok(es, fb, ee, fr, hee, hfr)
  +hrl : {Bool.pick(Nat, Nat.is_lt(rs, rs), 1n+rs, rs) == P.Pz.rl(rs, rb) : Nat} = Equal.trans(Nat, Bool.pick(Nat, Nat.is_lt(rs, rs), 1n+rs, rs), rs, P.Pz.rl(rs, rb),
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 1n+rs, rs), Nat.is_lt(rs, rs), False{}, Equal.trans(Bool, Nat.is_lt(rs, rs), RD.Nat.lt(rs, rs), False{}, P2.Lt.eq(rs, rs), Lt.irr(rs))), Equal.sym(Nat, P.Pz.rl(rs, rb), rs, erl))
  +e2 : {Nat.add(rs, rs) == 1n+Nat.add(rs, d) : Nat} = Equal.trans(Nat, Nat.add(rs, rs), Nat.add(rs, 1n+d), 1n+Nat.add(rs, d), Equal.cong(Nat, Nat, z => Nat.add(rs, z), rs, 1n+d, Equal.sym(Nat, 1n+d, rs, ek)), NL.Nat.add_succ_r(rs, d))
  +htb : {Bool.pick(Nat, Nat.is_eq(1n, 1n), Nat.sub(Nat.add(rs, rs), 1n), Nat.sub(rs, rs)) == rb : Nat} = Equal.trans(Nat, Nat.sub(Nat.add(rs, rs), 1n), Nat.sub(1n+Nat.add(rs, d), 1n), rb, Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), Nat.add(rs, rs), 1n+Nat.add(rs, d), e2),
    Equal.trans(Nat, Nat.sub(Nat.add(rs, d), 0n), Nat.add(rs, d), rb, P2.Sub.z(Nat.add(rs, d)), Equal.sym(Nat, rb, Nat.add(rs, d), erb)))
  Dec.q(h1, p01, es, rs, rb, ee, fr, 1n, rs, rem, low, {==}, hrs, hqQ, hwk, hl, Run.full(rs, rem, 1n, low, {==}, hl), hrl, htb, hee, hfr)

def Dec.z(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hz: {RD.Nat.lt(rb, rs) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool}, s: Bool, +es2: {RD.Nat.lt(RD.Nat.monus(rs, rb), rs) == s : Bool})
  -> {SB.Bd.val(1n+h1, P.Pz.dec(1n+h1, 1n+W(p01, es, rs), es, rs, Pat(p01, es, rs, rb, ee, fr))) == Val(p01, es, rs, rb, ee, fr) : D.Dy}:
  match s:
    case True{}:
      Dec.zs(h1, p01, es, rs, rb, ee, fr, hz, es2, hee, hfr)
    case False{}:
      Dec.zl(h1, p01, es, rs, rb, ee, fr, hrs, hz, es2, hee, hfr)

def Dec.o(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}, +hz: {RD.Nat.lt(rb, rs) == False{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool}, s: Bool, +es2: {RD.Nat.lt(1n+RD.Nat.monus(rb, rs), rs) == s : Bool})
  -> {SB.Bd.val(1n+h1, P.Pz.dec(1n+h1, 1n+W(p01, es, rs), es, rs, Pat(p01, es, rs, rb, ee, fr))) == Val(p01, es, rs, rb, ee, fr) : D.Dy}:
  match s:
    case True{}:
      Dec.os(h1, p01, es, rs, rb, ee, fr, hz, es2, hee, hfr)
    case False{}:
      Dec.ol(h1, p01, es, rs, rb, ee, fr, hrs, hrb, hz, es2, hee, hfr)

def Dec.val.go(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool}, z: Bool, +ez: {RD.Nat.lt(rb, rs) == z : Bool})
  -> {SB.Bd.val(1n+h1, P.Pz.dec(1n+h1, 1n+W(p01, es, rs), es, rs, Pat(p01, es, rs, rb, ee, fr))) == Val(p01, es, rs, rb, ee, fr) : D.Dy}:
  match z:
    case True{}:
      Dec.z(h1, p01, es, rs, rb, ee, fr, hrs, ez, hee, hfr, RD.Nat.lt(RD.Nat.monus(rs, rb), rs), {==})
    case False{}:
      Dec.o(h1, p01, es, rs, rb, ee, fr, hrs, hrb, ez, hee, hfr, RD.Nat.lt(1n+RD.Nat.monus(rb, rs), rs), {==})

# T1. Every positive pattern decodes to its value: for every class
# rb < 2 rs, exponent ee < 2^es and fraction fr < 2^fb, the decoder reads
# Pat back as Val. (Patterns 0 and NaR aside, these are all the positive
# patterns: Pat.succ steps through them in order.)
def Dec.val(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool})
  -> {SB.Bd.val(1n+h1, P.Pz.dec(1n+h1, 1n+W(p01, es, rs), es, rs, Pat(p01, es, rs, rb, ee, fr))) == Val(p01, es, rs, rb, ee, fr) : D.Dy}:
  Dec.val.go(h1, p01, es, rs, rb, ee, fr, hrs, hrb, hee, hfr, RD.Nat.lt(rb, rs), {==})

# The next pattern
# ----------------
# Pattern q + 1 is the next value up, one unit in the last place of q.
# Within a binade that is fr + 1; at fr = 2^fb - 1 it carries into the
# exponent; at ee = 2^es - 1 too it carries into the regime, where
# (R + 1) 2^u = R' 2^u' with u = rs - rl (Rg.step).

def U(+rs: Nat, +rb: Nat) -> Nat:
  RD.Nat.monus(rs, P.Pz.rl(rs, rb))

def Rl.z(+rs: Nat, +rb: Nat, +hz: {RD.Nat.lt(rb, rs) == True{} : Bool}) -> {P.Pz.rl(rs, rb) == P.Pz.min(1n+RD.Nat.monus(rs, rb), rs) : Nat}:
  Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, P.Pz.min(1n+RD.Nat.monus(rs, rb), rs), P.Pz.min(2n+RD.Nat.monus(rb, rs), rs)), RD.Nat.lt(rb, rs), True{}, hz)

def Rl.o(+rs: Nat, +rb: Nat, +hz: {RD.Nat.lt(rb, rs) == False{} : Bool}) -> {P.Pz.rl(rs, rb) == P.Pz.min(2n+RD.Nat.monus(rb, rs), rs) : Nat}:
  Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, P.Pz.min(1n+RD.Nat.monus(rs, rb), rs), P.Pz.min(2n+RD.Nat.monus(rb, rs), rs)), RD.Nat.lt(rb, rs), False{}, hz)

def Rg.z(+rs: Nat, +rb: Nat, +hz: {RD.Nat.lt(rb, rs) == True{} : Bool}, s: Bool, +hs: {RD.Nat.lt(RD.Nat.monus(rs, rb), rs) == s : Bool}) -> {Rg(rs, rb) == Bool.pick(Nat, s, 1n, 0n) : Nat}:
  +eK : {Kc(rs, rb) == RD.Nat.monus(rs, rb) : Nat} = Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, RD.Nat.monus(rs, rb), 1n+RD.Nat.monus(rb, rs)), RD.Nat.lt(rb, rs), True{}, hz)
  +eS : {RD.Nat.lt(Kc(rs, rb), rs) == s : Bool} = Equal.trans(Bool, RD.Nat.lt(Kc(rs, rb), rs), RD.Nat.lt(RD.Nat.monus(rs, rb), rs), s, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, rs), Kc(rs, rb), RD.Nat.monus(rs, rb), eK), hs)
  Equal.trans(Nat, Rg(rs, rb), RgB(True{}, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), Bool.pick(Nat, s, 1n, 0n),
    Equal.cong(Bool, Nat, z => RgB(z, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), RD.Nat.lt(rb, rs), True{}, hz),
    Equal.cong(Bool, Nat, z => RgB(True{}, z, Kc(rs, rb)), RD.Nat.lt(Kc(rs, rb), rs), s, eS))

def Rg.o(+rs: Nat, +rb: Nat, +hz: {RD.Nat.lt(rb, rs) == False{} : Bool}, s: Bool, +hs: {RD.Nat.lt(1n+RD.Nat.monus(rb, rs), rs) == s : Bool})
  -> {Rg(rs, rb) == Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+RD.Nat.monus(rb, rs)), 1n), Bool.pick(Nat, s, 2n, 1n)) : Nat}:
  +k : Nat = 1n+RD.Nat.monus(rb, rs)
  +eK : {Kc(rs, rb) == k : Nat} = Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, RD.Nat.monus(rs, rb), 1n+RD.Nat.monus(rb, rs)), RD.Nat.lt(rb, rs), False{}, hz)
  +eS : {RD.Nat.lt(Kc(rs, rb), rs) == s : Bool} = Equal.trans(Bool, RD.Nat.lt(Kc(rs, rb), rs), RD.Nat.lt(k, rs), s, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, rs), Kc(rs, rb), k, eK), hs)
  Equal.trans(Nat, Rg(rs, rb), RgB(False{}, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), Nat.mul(RD.Nat.monus(RD.Nat.pow2(k), 1n), Bool.pick(Nat, s, 2n, 1n)),
    Equal.cong(Bool, Nat, z => RgB(z, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), RD.Nat.lt(rb, rs), False{}, hz),
    Equal.trans(Nat, RgB(False{}, RD.Nat.lt(Kc(rs, rb), rs), Kc(rs, rb)), RgB(False{}, s, Kc(rs, rb)), Nat.mul(RD.Nat.monus(RD.Nat.pow2(k), 1n), Bool.pick(Nat, s, 2n, 1n)),
      Equal.cong(Bool, Nat, z => RgB(False{}, z, Kc(rs, rb)), RD.Nat.lt(Kc(rs, rb), rs), s, eS),
      Equal.cong(Nat, Nat, z => RgB(False{}, s, z), Kc(rs, rb), k, eK)))

def StepL(+rs: Nat, +rb: Nat) -> Nat:
  Nat.add(Nat.mul(Rg(rs, rb), RD.Nat.pow2(U(rs, rb))), RD.Nat.pow2(U(rs, rb)))

def StepR(+rs: Nat, +rb: Nat) -> Nat:
  Nat.mul(Rg(rs, 1n+rb), RD.Nat.pow2(U(rs, 1n+rb)))

def Mo.self(+a: Nat) -> {RD.Nat.monus(a, a) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+a2):
      Mo.self(a2)

# from concrete values of R and u on both sides
def Step.of(+rs: Nat, +rb: Nat, +R0: Nat, +u0: Nat, +R1: Nat, +u1: Nat,
  +eR0: {Rg(rs, rb) == R0 : Nat}, +eu0: {U(rs, rb) == u0 : Nat}, +eR1: {Rg(rs, 1n+rb) == R1 : Nat}, +eu1: {U(rs, 1n+rb) == u1 : Nat},
  +core: {Nat.add(Nat.mul(R0, RD.Nat.pow2(u0)), RD.Nat.pow2(u0)) == Nat.mul(R1, RD.Nat.pow2(u1)) : Nat})
  -> {StepL(rs, rb) == StepR(rs, rb) : Nat}:
  +l1 = Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(z, RD.Nat.pow2(U(rs, rb))), RD.Nat.pow2(U(rs, rb))), Rg(rs, rb), R0, eR0)
  +l2 = Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(R0, RD.Nat.pow2(z)), RD.Nat.pow2(z)), U(rs, rb), u0, eu0)
  +r1 = Equal.cong(Nat, Nat, z => Nat.mul(z, RD.Nat.pow2(U(rs, 1n+rb))), Rg(rs, 1n+rb), R1, eR1)
  +r2 = Equal.cong(Nat, Nat, z => Nat.mul(R1, RD.Nat.pow2(z)), U(rs, 1n+rb), u1, eu1)
  Equal.trans(Nat, StepL(rs, rb), Nat.add(Nat.mul(R0, RD.Nat.pow2(U(rs, rb))), RD.Nat.pow2(U(rs, rb))), StepR(rs, rb), l1,
  Equal.trans(Nat, Nat.add(Nat.mul(R0, RD.Nat.pow2(U(rs, rb))), RD.Nat.pow2(U(rs, rb))), Nat.add(Nat.mul(R0, RD.Nat.pow2(u0)), RD.Nat.pow2(u0)), StepR(rs, rb), l2,
  Equal.trans(Nat, Nat.add(Nat.mul(R0, RD.Nat.pow2(u0)), RD.Nat.pow2(u0)), Nat.mul(R1, RD.Nat.pow2(u1)), StepR(rs, rb), core,
    Equal.sym(Nat, StepR(rs, rb), Nat.mul(R1, RD.Nat.pow2(u1)), Equal.trans(Nat, StepR(rs, rb), Nat.mul(R1, RD.Nat.pow2(U(rs, 1n+rb))), Nat.mul(R1, RD.Nat.pow2(u1)), r1, r2)))))

# class 0, the full zero run, to class 1
def Z0.R(+r1: Nat) -> {Rg(1n+r1, 0n) == 0n : Nat}:
  Rg.z(1n+r1, 0n, {==}, False{}, Lt.irr(r1))

def Z0.U(+r1: Nat) -> {U(1n+r1, 0n) == 0n : Nat}:
  +rs : Nat = 1n+r1
  +erl0 : {P.Pz.rl(rs, 0n) == rs : Nat} = Equal.trans(Nat, P.Pz.rl(rs, 0n), P.Pz.min(1n+rs, rs), rs, Rl.z(rs, 0n, {==}), Min.top(rs))
  Equal.trans(Nat, U(rs, 0n), RD.Nat.monus(rs, rs), 0n, Equal.cong(Nat, Nat, z => RD.Nat.monus(rs, z), P.Pz.rl(rs, 0n), rs, erl0), Mo.self(rs))

def Step.zero(+r1: Nat) -> {StepL(1n+r1, 0n) == StepR(1n+r1, 0n) : Nat}:
  match r1:
    case 0n:
      Step.of(1n, 0n, 0n, 0n, 1n, 0n, Z0.R(0n), Z0.U(0n), {==}, {==}, {==})
    case 1n+(+r2):
      +hz1 : {RD.Nat.lt(1n, 2n+r2) == True{} : Bool} = {==}
      +eR1 : {Rg(2n+r2, 1n) == 1n : Nat} = Rg.z(2n+r2, 1n, hz1, True{}, E2.Lt.succ(r2))
      +erl1 : {P.Pz.rl(2n+r2, 1n) == 2n+r2 : Nat} = Equal.trans(Nat, P.Pz.rl(2n+r2, 1n), P.Pz.min(2n+r2, 2n+r2), 2n+r2, Rl.z(2n+r2, 1n, hz1),
        Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 2n+r2, 2n+r2), RD.Nat.lt(2n+r2, 2n+r2), False{}, Lt.irr(2n+r2)))
      +eu1 : {U(2n+r2, 1n) == 0n : Nat} = Equal.trans(Nat, U(2n+r2, 1n), RD.Nat.monus(2n+r2, 2n+r2), 0n, Equal.cong(Nat, Nat, z => RD.Nat.monus(2n+r2, z), P.Pz.rl(2n+r2, 1n), 2n+r2, erl1), Mo.self(2n+r2))
      Step.of(2n+r2, 0n, 0n, 0n, 1n, 0n, Z0.R(1n+r2), Z0.U(1n+r2), eR1, eu1, {==})

# a short zero run means rb >= 1
def Rb.pos(+rs: Nat, +rb: Nat, +hs: {RD.Nat.lt(RD.Nat.monus(rs, rb), rs) == True{} : Bool}) -> {rb == 1n+RD.Nat.monus(rb, 1n) : Nat}:
  match rb:
    case 0n:
      B.Bool.tf({0n == 1n+RD.Nat.monus(0n, 1n) : Nat}, Equal.trans(Bool, True{}, RD.Nat.lt(rs, rs), False{}, Equal.trans(Bool, True{}, RD.Nat.lt(RD.Nat.monus(rs, 0n), rs), RD.Nat.lt(rs, rs), Equal.sym(Bool, RD.Nat.lt(RD.Nat.monus(rs, 0n), rs), True{}, hs), Equal.cong(Nat, Bool, z => RD.Nat.lt(z, rs), RD.Nat.monus(rs, 0n), rs, BP.Mo.z(rs))), Lt.irr(rs)))
    case 1n+(+r):
      Equal.cong(Nat, Nat, z => 1n+z, r, RD.Nat.monus(r, 0n), Equal.sym(Nat, RD.Nat.monus(r, 0n), r, BP.Mo.z(r)))

# a full zero run means rb = 0
def Rb.zero(+rs: Nat, +rb: Nat, +hz: {RD.Nat.lt(rb, rs) == True{} : Bool}, +hs: {RD.Nat.lt(RD.Nat.monus(rs, rb), rs) == False{} : Bool}) -> {rb == 0n : Nat}:
  +c = RD.Nat.monus(rs, rb)
  +ers : {rs == Nat.add(rb, c) : Nat} = E.Le.wit(rb, rs, BP.Lt.asym(rb, rs, hz))
  +hcle : {RD.Nat.lt(rs, c) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(rs, c), RD.Nat.lt(Nat.add(c, rb), c), False{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(z, c), rs, Nat.add(c, rb), Equal.trans(Nat, rs, Nat.add(rb, c), Nat.add(c, rb), ers, NL.Nat.add_comm(rb, c))), BP.Lt.ge(c, rb))
  +ec : {c == rs : Nat} = E2.Le.anti(c, rs, hcle, hs)
  Add.z(rb, rs, Equal.sym(Nat, rs, Nat.add(rb, rs), Equal.trans(Nat, rs, Nat.add(rb, c), Nat.add(rb, rs), ers, Equal.cong(Nat, Nat, z => Nat.add(rb, z), c, rs, ec))))

def Step.tr(+a: Nat, +b: Nat, +rb0: Nat, +rb: Nat, +ea: {a == b : Nat}, +eb: {rb0 == rb : Nat}, +h: {StepL(a, rb0) == StepR(a, rb0) : Nat}) -> {StepL(b, rb) == StepR(b, rb) : Nat}:
  +h1 : {StepL(b, rb0) == StepR(b, rb0) : Nat} = Equal.trans(Nat, StepL(b, rb0), StepL(a, rb0), StepR(b, rb0), Equal.cong(Nat, Nat, z => StepL(z, rb0), b, a, Equal.sym(Nat, a, b, ea)),
    Equal.trans(Nat, StepL(a, rb0), StepR(a, rb0), StepR(b, rb0), h, Equal.cong(Nat, Nat, z => StepR(z, rb0), a, b, ea)))
  Equal.trans(Nat, StepL(b, rb), StepL(b, rb0), StepR(b, rb), Equal.cong(Nat, Nat, z => StepL(b, z), rb, rb0, Equal.sym(Nat, rb0, rb, eb)),
    Equal.trans(Nat, StepL(b, rb0), StepR(b, rb0), StepR(b, rb), h1, Equal.cong(Nat, Nat, z => StepR(b, z), rb0, rb, eb)))

# rb = 0 to rb = 1
def Step.z0(+rs: Nat, +rb: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hz: {RD.Nat.lt(rb, rs) == True{} : Bool}, +hs: {RD.Nat.lt(RD.Nat.monus(rs, rb), rs) == False{} : Bool})
  -> {StepL(rs, rb) == StepR(rs, rb) : Nat}:
  +r1 = RD.Nat.monus(rs, 1n)
  +ers : {1n+r1 == rs : Nat} = Equal.sym(Nat, rs, 1n+r1, BP.Lt.wit(0n, rs)(hrs))
  Step.tr(1n+r1, rs, 0n, rb, ers, Equal.sym(Nat, rb, 0n, Rb.zero(rs, rb, hz, hs)), Step.zero(r1))

# zeros to zeros, rb >= 1: (1 + 1) 2^(rb - 1) = 1 2^rb
def Step.zz(+rs: Nat, +rb: Nat, +hz1: {RD.Nat.lt(1n+rb, rs) == True{} : Bool}, +hs: {RD.Nat.lt(RD.Nat.monus(rs, rb), rs) == True{} : Bool})
  -> {StepL(rs, rb) == StepR(rs, rb) : Nat}:
  +r = RD.Nat.monus(rb, 1n)
  +err : {rb == 1n+r : Nat} = Rb.pos(rs, rb, hs)
  +hz : {RD.Nat.lt(rb, rs) == True{} : Bool} = E2.Lt.le_trans(rb, 1n+rb, rs, E2.Lt.succ(rb), E2.Lt.to_le(1n+rb, rs, hz1))
  +c = RD.Nat.monus(rs, 1n+rb)
  +ers : {rs == Nat.add(1n+rb, c) : Nat} = E.Le.wit(1n+rb, rs, E2.Lt.to_le(1n+rb, rs, hz1))
  # rs = 2 + r + c in the shapes needed below
  +ers2 : {rs == Nat.add(2n+c, r) : Nat} = Equal.trans(Nat, rs, Nat.add(1n+rb, c), Nat.add(2n+c, r), ers,
    Equal.trans(Nat, Nat.add(1n+rb, c), Nat.add(2n+r, c), Nat.add(2n+c, r), Equal.cong(Nat, Nat, z => Nat.add(1n+z, c), rb, 1n+r, err), Equal.cong(Nat, Nat, z => 2n+z, Nat.add(r, c), Nat.add(c, r), NL.Nat.add_comm(r, c))))
  +ers3 : {rs == Nat.add(rb, 1n+c) : Nat} = Equal.trans(Nat, rs, Nat.add(1n+rb, c), Nat.add(rb, 1n+c), ers, Equal.sym(Nat, Nat.add(rb, 1n+c), 1n+Nat.add(rb, c), NL.Nat.add_succ_r(rb, c)))
  +e1 : {RD.Nat.monus(rs, rb) == 1n+c : Nat} = Equal.trans(Nat, RD.Nat.monus(rs, rb), RD.Nat.monus(Nat.add(rb, 1n+c), rb), 1n+c, Equal.cong(Nat, Nat, z => RD.Nat.monus(z, rb), rs, Nat.add(rb, 1n+c), ers3), R.Nat.monus_add(rb, 1n+c))
  +hc1 : {RD.Nat.lt(1n+c, rs) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(1n+c, rs), RD.Nat.lt(1n+c, Nat.add(1n+c, 1n+r)), True{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(1n+c, z), rs, Nat.add(1n+c, 1n+r), Equal.trans(Nat, rs, Nat.add(2n+c, r), Nat.add(1n+c, 1n+r), ers2, Equal.sym(Nat, Nat.add(1n+c, 1n+r), 2n+Nat.add(c, r), NL.Nat.add_succ_r(1n+c, r)))),
    BP.Lt.self(1n+c, r))
  +hc0 : {RD.Nat.lt(c, rs) == True{} : Bool} = E2.Lt.le_trans(c, 1n+c, rs, E2.Lt.succ(c), E2.Lt.to_le(1n+c, rs, hc1))
  +erl0 : {P.Pz.rl(rs, rb) == 2n+c : Nat} = Equal.trans(Nat, P.Pz.rl(rs, rb), P.Pz.min(1n+RD.Nat.monus(rs, rb), rs), 2n+c, Rl.z(rs, rb, hz),
    Equal.trans(Nat, P.Pz.min(1n+RD.Nat.monus(rs, rb), rs), P.Pz.min(2n+c, rs), 2n+c, Equal.cong(Nat, Nat, z => P.Pz.min(1n+z, rs), RD.Nat.monus(rs, rb), 1n+c, e1), Min.succ(1n+c, rs, hc1)))
  +erl1 : {P.Pz.rl(rs, 1n+rb) == 1n+c : Nat} = Equal.trans(Nat, P.Pz.rl(rs, 1n+rb), P.Pz.min(1n+c, rs), 1n+c, Rl.z(rs, 1n+rb, hz1), Min.succ(c, rs, hc0))
  +eu0 : {U(rs, rb) == r : Nat} = Equal.trans(Nat, U(rs, rb), RD.Nat.monus(Nat.add(2n+c, r), 2n+c), r,
    Equal.trans(Nat, U(rs, rb), RD.Nat.monus(rs, 2n+c), RD.Nat.monus(Nat.add(2n+c, r), 2n+c), Equal.cong(Nat, Nat, z => RD.Nat.monus(rs, z), P.Pz.rl(rs, rb), 2n+c, erl0), Equal.cong(Nat, Nat, z => RD.Nat.monus(z, 2n+c), rs, Nat.add(2n+c, r), ers2)),
    R.Nat.monus_add(2n+c, r))
  +eu1 : {U(rs, 1n+rb) == 1n+r : Nat} = Equal.trans(Nat, U(rs, 1n+rb), RD.Nat.monus(Nat.add(1n+c, 1n+r), 1n+c), 1n+r,
    Equal.trans(Nat, U(rs, 1n+rb), RD.Nat.monus(rs, 1n+c), RD.Nat.monus(Nat.add(1n+c, 1n+r), 1n+c), Equal.cong(Nat, Nat, z => RD.Nat.monus(rs, z), P.Pz.rl(rs, 1n+rb), 1n+c, erl1),
      Equal.cong(Nat, Nat, z => RD.Nat.monus(z, 1n+c), rs, Nat.add(1n+c, 1n+r), Equal.trans(Nat, rs, Nat.add(2n+c, r), Nat.add(1n+c, 1n+r), ers2, Equal.sym(Nat, Nat.add(1n+c, 1n+r), 2n+Nat.add(c, r), NL.Nat.add_succ_r(1n+c, r))))),
    R.Nat.monus_add(1n+c, 1n+r))
  +P0 = RD.Nat.pow2(r)
  +core : {Nat.add(Nat.mul(1n, P0), P0) == Nat.mul(1n, RD.Nat.pow2(1n+r)) : Nat} = Equal.trans(Nat, Nat.add(Nat.mul(1n, P0), P0), Nat.add(P0, P0), Nat.mul(1n, RD.Nat.pow2(1n+r)),
    Equal.cong(Nat, Nat, z => Nat.add(z, P0), Nat.mul(1n, P0), P0, P3.Mul.one_l(P0)),
    Equal.sym(Nat, Nat.mul(1n, RD.Nat.pow2(1n+r)), Nat.add(P0, P0), Equal.trans(Nat, Nat.mul(1n, RD.Nat.pow2(1n+r)), Nat.double(P0), Nat.add(P0, P0), P3.Mul.one_l(RD.Nat.pow2(1n+r)), Y.Nat.double_add(P0))))
  Step.of(rs, rb, 1n, r, 1n, 1n+r, Rg.z(rs, rb, hz, True{}, hs), eu0, Rg.z(rs, 1n+rb, hz1, True{}, hc0), eu1, core)

# zeros to ones, rb = rs - 1 >= 1: (1 + 1) 2^(rs - 2) = 2 2^(rs - 2)
def Step.zo(+rs: Nat, +rb: Nat, +hz: {RD.Nat.lt(rb, rs) == True{} : Bool}, +hz1: {RD.Nat.lt(1n+rb, rs) == False{} : Bool}, +hs: {RD.Nat.lt(RD.Nat.monus(rs, rb), rs) == True{} : Bool})
  -> {StepL(rs, rb) == StepR(rs, rb) : Nat}:
  +r = RD.Nat.monus(rb, 1n)
  +err : {rb == 1n+r : Nat} = Rb.pos(rs, rb, hs)
  +ers : {1n+rb == rs : Nat} = E2.Le.anti(1n+rb, rs, E2.Le.succ(rb, rs, hz), hz1)
  +ers2 : {rs == 2n+r : Nat} = Equal.trans(Nat, rs, 1n+rb, 2n+r, Equal.sym(Nat, 1n+rb, rs, ers), Equal.cong(Nat, Nat, z => 1n+z, rb, 1n+r, err))
  +ea1 : {Nat.add(rb, 1n) == 1n+rb : Nat} = Equal.trans(Nat, Nat.add(rb, 1n), 1n+Nat.add(rb, 0n), 1n+rb, NL.Nat.add_succ_r(rb, 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(rb, 0n), rb, NL.Nat.add_zero_r(rb)))
  +e1 : {RD.Nat.monus(rs, rb) == 1n : Nat} = Equal.trans(Nat, RD.Nat.monus(rs, rb), RD.Nat.monus(Nat.add(rb, 1n), rb), 1n,
    Equal.cong(Nat, Nat, z => RD.Nat.monus(z, rb), rs, Nat.add(rb, 1n), Equal.trans(Nat, rs, 1n+rb, Nat.add(rb, 1n), Equal.sym(Nat, 1n+rb, rs, ers), Equal.sym(Nat, Nat.add(rb, 1n), 1n+rb, ea1))), R.Nat.monus_add(rb, 1n))
  +h1 : {RD.Nat.lt(1n, rs) == True{} : Bool} = Equal.cong(Nat, Bool, z => RD.Nat.lt(1n, z), rs, 2n+r, ers2)
  +ed : {RD.Nat.monus(1n+rb, rs) == 0n : Nat} = Equal.trans(Nat, RD.Nat.monus(1n+rb, rs), RD.Nat.monus(rs, rs), 0n, Equal.cong(Nat, Nat, z => RD.Nat.monus(z, rs), 1n+rb, rs, ers), Mo.self(rs))
  +emr : {RD.Nat.monus(rs, 2n) == r : Nat} = Equal.trans(Nat, RD.Nat.monus(rs, 2n), RD.Nat.monus(r, 0n), r, Equal.cong(Nat, Nat, z => RD.Nat.monus(z, 2n), rs, 2n+r, ers2), BP.Mo.z(r))
  +erl0 : {P.Pz.rl(rs, rb) == 2n : Nat} = Equal.trans(Nat, P.Pz.rl(rs, rb), P.Pz.min(1n+RD.Nat.monus(rs, rb), rs), 2n, Rl.z(rs, rb, hz),
    Equal.trans(Nat, P.Pz.min(1n+RD.Nat.monus(rs, rb), rs), P.Pz.min(2n, rs), 2n, Equal.cong(Nat, Nat, z => P.Pz.min(1n+z, rs), RD.Nat.monus(rs, rb), 1n, e1), Min.succ(1n, rs, h1)))
  +erl1 : {P.Pz.rl(rs, 1n+rb) == 2n : Nat} = Equal.trans(Nat, P.Pz.rl(rs, 1n+rb), P.Pz.min(2n+RD.Nat.monus(1n+rb, rs), rs), 2n, Rl.o(rs, 1n+rb, hz1),
    Equal.trans(Nat, P.Pz.min(2n+RD.Nat.monus(1n+rb, rs), rs), P.Pz.min(2n, rs), 2n, Equal.cong(Nat, Nat, z => P.Pz.min(2n+z, rs), RD.Nat.monus(1n+rb, rs), 0n, ed), Min.succ(1n, rs, h1)))
  +eu0 : {U(rs, rb) == r : Nat} = Equal.trans(Nat, U(rs, rb), RD.Nat.monus(rs, 2n), r, Equal.cong(Nat, Nat, z => RD.Nat.monus(rs, z), P.Pz.rl(rs, rb), 2n, erl0), emr)
  +eu1 : {U(rs, 1n+rb) == r : Nat} = Equal.trans(Nat, U(rs, 1n+rb), RD.Nat.monus(rs, 2n), r, Equal.cong(Nat, Nat, z => RD.Nat.monus(rs, z), P.Pz.rl(rs, 1n+rb), 2n, erl1), emr)
  +hs1 : {RD.Nat.lt(1n+RD.Nat.monus(1n+rb, rs), rs) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(1n+RD.Nat.monus(1n+rb, rs), rs), RD.Nat.lt(1n, rs), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(1n+z, rs), RD.Nat.monus(1n+rb, rs), 0n, ed), h1)
  +eR1 : {Rg(rs, 1n+rb) == 2n : Nat} = Equal.trans(Nat, Rg(rs, 1n+rb), Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+RD.Nat.monus(1n+rb, rs)), 1n), 2n), 2n, Rg.o(rs, 1n+rb, hz1, True{}, hs1),
    Equal.cong(Nat, Nat, z => Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+z), 1n), 2n), RD.Nat.monus(1n+rb, rs), 0n, ed))
  +P0 = RD.Nat.pow2(r)
  Step.of(rs, rb, 1n, r, 2n, r, Rg.z(rs, rb, hz, True{}, hs), eu0, eR1, eu1, NL.Nat.add_comm(Nat.mul(1n, P0), P0))

# ones to ones, k + 1 < rs: (2 (2^k - 1) + 1) 2^(u' + 1) = 2 (2^(k+1) - 1) 2^u'
def Step.oo(+rs: Nat, +rb: Nat, +hz: {RD.Nat.lt(rb, rs) == False{} : Bool}, +hs1: {RD.Nat.lt(2n+RD.Nat.monus(rb, rs), rs) == True{} : Bool})
  -> {StepL(rs, rb) == StepR(rs, rb) : Nat}:
  +d = RD.Nat.monus(rb, rs)
  +erb : {rb == Nat.add(rs, d) : Nat} = E.Le.wit(rs, rb, hz)
  +hz1 : {RD.Nat.lt(1n+rb, rs) == False{} : Bool} = E.Le.trans(rs, rb, 1n+rb, hz, Lt.sa(rb))
  +ed1 : {RD.Nat.monus(1n+rb, rs) == 1n+d : Nat} = Equal.trans(Nat, RD.Nat.monus(1n+rb, rs), RD.Nat.monus(Nat.add(rs, 1n+d), rs), 1n+d,
    Equal.cong(Nat, Nat, z => RD.Nat.monus(z, rs), 1n+rb, Nat.add(rs, 1n+d), Equal.trans(Nat, 1n+rb, 1n+Nat.add(rs, d), Nat.add(rs, 1n+d), Equal.cong(Nat, Nat, z => 1n+z, rb, Nat.add(rs, d), erb), Equal.sym(Nat, Nat.add(rs, 1n+d), 1n+Nat.add(rs, d), NL.Nat.add_succ_r(rs, d)))),
    R.Nat.monus_add(rs, 1n+d))
  +hs : {RD.Nat.lt(1n+d, rs) == True{} : Bool} = E2.Lt.le_trans(1n+d, 2n+d, rs, E2.Lt.succ(1n+d), E2.Lt.to_le(2n+d, rs, hs1))
  +e = RD.Nat.monus(rs, 3n+d)
  +e3 : {rs == Nat.add(3n+d, e) : Nat} = E.Le.wit(3n+d, rs, E2.Le.succ(2n+d, rs, hs1))
  +erl0 : {P.Pz.rl(rs, rb) == 2n+d : Nat} = Equal.trans(Nat, P.Pz.rl(rs, rb), P.Pz.min(2n+d, rs), 2n+d, Rl.o(rs, rb, hz), Min.succ(1n+d, rs, hs))
  +erl1 : {P.Pz.rl(rs, 1n+rb) == 3n+d : Nat} = Equal.trans(Nat, P.Pz.rl(rs, 1n+rb), P.Pz.min(2n+RD.Nat.monus(1n+rb, rs), rs), 3n+d, Rl.o(rs, 1n+rb, hz1),
    Equal.trans(Nat, P.Pz.min(2n+RD.Nat.monus(1n+rb, rs), rs), P.Pz.min(3n+d, rs), 3n+d, Equal.cong(Nat, Nat, z => P.Pz.min(2n+z, rs), RD.Nat.monus(1n+rb, rs), 1n+d, ed1), Min.succ(2n+d, rs, hs1)))
  +eu0 : {U(rs, rb) == 1n+e : Nat} = Equal.trans(Nat, U(rs, rb), RD.Nat.monus(Nat.add(2n+d, 1n+e), 2n+d), 1n+e,
    Equal.trans(Nat, U(rs, rb), RD.Nat.monus(rs, 2n+d), RD.Nat.monus(Nat.add(2n+d, 1n+e), 2n+d), Equal.cong(Nat, Nat, z => RD.Nat.monus(rs, z), P.Pz.rl(rs, rb), 2n+d, erl0),
      Equal.cong(Nat, Nat, z => RD.Nat.monus(z, 2n+d), rs, Nat.add(2n+d, 1n+e), Equal.trans(Nat, rs, Nat.add(3n+d, e), Nat.add(2n+d, 1n+e), e3, Equal.sym(Nat, Nat.add(2n+d, 1n+e), 1n+Nat.add(2n+d, e), NL.Nat.add_succ_r(2n+d, e))))),
    R.Nat.monus_add(2n+d, 1n+e))
  +eu1 : {U(rs, 1n+rb) == e : Nat} = Equal.trans(Nat, U(rs, 1n+rb), RD.Nat.monus(Nat.add(3n+d, e), 3n+d), e,
    Equal.trans(Nat, U(rs, 1n+rb), RD.Nat.monus(rs, 3n+d), RD.Nat.monus(Nat.add(3n+d, e), 3n+d), Equal.cong(Nat, Nat, z => RD.Nat.monus(rs, z), P.Pz.rl(rs, 1n+rb), 3n+d, erl1), Equal.cong(Nat, Nat, z => RD.Nat.monus(z, 3n+d), rs, Nat.add(3n+d, e), e3)),
    R.Nat.monus_add(3n+d, e))
  +M1 = RD.Nat.monus(RD.Nat.pow2(1n+d), 1n)
  +M2 = RD.Nat.monus(RD.Nat.pow2(2n+d), 1n)
  +hs1b : {RD.Nat.lt(1n+RD.Nat.monus(1n+rb, rs), rs) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(1n+RD.Nat.monus(1n+rb, rs), rs), RD.Nat.lt(2n+d, rs), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(1n+z, rs), RD.Nat.monus(1n+rb, rs), 1n+d, ed1), hs1)
  +eR1 : {Rg(rs, 1n+rb) == Nat.mul(M2, 2n) : Nat} = Equal.trans(Nat, Rg(rs, 1n+rb), Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+RD.Nat.monus(1n+rb, rs)), 1n), 2n), Nat.mul(M2, 2n), Rg.o(rs, 1n+rb, hz1, True{}, hs1b),
    Equal.cong(Nat, Nat, z => Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+z), 1n), 2n), RD.Nat.monus(1n+rb, rs), 1n+d, ed1))
  +P1 = RD.Nat.pow2(1n+d)
  +P2 = RD.Nat.pow2(2n+d)
  +X = RD.Nat.pow2(e)
  +Y = RD.Nat.pow2(1n+e)
  +eY : {Y == Nat.add(X, X) : Nat} = Y.Nat.double_add(X)
  +eP2 : {P2 == Nat.add(P1, P1) : Nat} = Y.Nat.double_add(P1)
  +eP1 : {P1 == 1n+M1 : Nat} = P2.Pw.pos(1n+d)
  +eP2b : {P2 == 1n+M2 : Nat} = P2.Pw.pos(2n+d)
  +eoX : {Nat.mul(1n, X) == X : Nat} = P3.Mul.one_l(X)
  +env : List<&2, Nat> = [M1, M2, P1, P2, X, Y, 1n, 2n]
  +core : {Nat.add(Nat.mul(Nat.mul(M1, 2n), Y), Y) == Nat.mul(Nat.mul(M2, 2n), X) : Nat} = R.NatN.eq2(env, R.Ad(R.Ml(R.Ml(R.V(0n), R.V(7n)), R.V(5n)), R.V(5n)), R.Ml(R.Ml(R.V(1n), R.V(7n)), R.V(4n)), [R.Ml(R.V(0n), R.V(7n)), R.Ng(R.Ml(R.V(4n), R.V(7n))), R.Ad(R.Ng(R.Ml(R.V(4n), R.V(7n))), R.Ng(R.Ml(R.V(4n), R.V(7n)))), R.Ml(R.V(4n), R.V(7n)), R.Ng(R.V(7n)), R.Ng(R.V(4n))], [R.Ad(R.V(5n), R.Ng(R.Ad(R.V(4n), R.V(4n)))), R.Ad(R.V(3n), R.Ng(R.Ad(R.V(2n), R.V(2n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.V(6n), R.V(0n)))), R.Ad(R.V(3n), R.Ng(R.Ad(R.V(6n), R.V(1n)))), R.Ad(R.Ml(R.V(6n), R.V(4n)), R.Ng(R.V(4n))), R.Ad(R.V(7n), R.Ng(R.Ad(R.V(6n), R.V(6n))))], [R.Ad(R.V(5n), R.Ng(R.Ad(R.V(4n), R.V(4n)))), R.Ad(R.V(4n), R.Ng(R.Ml(R.V(6n), R.V(4n)))), R.Ad(R.V(4n), R.Ng(R.Ml(R.V(6n), R.V(4n))))], {==}, (R.NatN.z(env, R.V(5n), R.Ad(R.V(4n), R.V(4n)), {==}, {==}, eY), (R.NatN.z(env, R.V(3n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, eP2), (R.NatN.z(env, R.V(2n), R.Ad(R.V(6n), R.V(0n)), {==}, {==}, eP1), (R.NatN.z(env, R.V(3n), R.Ad(R.V(6n), R.V(1n)), {==}, {==}, eP2b), (R.NatN.z(env, R.Ml(R.V(6n), R.V(4n)), R.V(4n), {==}, {==}, eoX), (R.NatN.z(env, R.V(7n), R.Ad(R.V(6n), R.V(6n)), {==}, {==}, {==}), Unit{})))))), (R.NatN.z(env, R.V(5n), R.Ad(R.V(4n), R.V(4n)), {==}, {==}, eY), (R.NatN.z(env, R.V(4n), R.Ml(R.V(6n), R.V(4n)), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, X), X, eoX)), (R.NatN.z(env, R.V(4n), R.Ml(R.V(6n), R.V(4n)), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, X), X, eoX)), Unit{}))), {==}, {==})
  Step.of(rs, rb, Nat.mul(M1, 2n), 1n+e, Nat.mul(M2, 2n), e, Rg.o(rs, rb, hz, True{}, hs), eu0, eR1, eu1, core)

# ones to the full ones run, k + 1 = rs: 2 (2^k - 1) + 1 = 2^rs - 1
def Step.ol(+rs: Nat, +rb: Nat, +hz: {RD.Nat.lt(rb, rs) == False{} : Bool}, +hrb1: {RD.Nat.lt(1n+rb, Nat.double(rs)) == True{} : Bool}, +hs1: {RD.Nat.lt(2n+RD.Nat.monus(rb, rs), rs) == False{} : Bool})
  -> {StepL(rs, rb) == StepR(rs, rb) : Nat}:
  +d = RD.Nat.monus(rb, rs)
  +erb : {rb == Nat.add(rs, d) : Nat} = E.Le.wit(rs, rb, hz)
  +hz1 : {RD.Nat.lt(1n+rb, rs) == False{} : Bool} = E.Le.trans(rs, rb, 1n+rb, hz, Lt.sa(rb))
  +eb1 : {1n+rb == Nat.add(rs, 1n+d) : Nat} = Equal.trans(Nat, 1n+rb, 1n+Nat.add(rs, d), Nat.add(rs, 1n+d), Equal.cong(Nat, Nat, z => 1n+z, rb, Nat.add(rs, d), erb), Equal.sym(Nat, Nat.add(rs, 1n+d), 1n+Nat.add(rs, d), NL.Nat.add_succ_r(rs, d)))
  +ed1 : {RD.Nat.monus(1n+rb, rs) == 1n+d : Nat} = Equal.trans(Nat, RD.Nat.monus(1n+rb, rs), RD.Nat.monus(Nat.add(rs, 1n+d), rs), 1n+d, Equal.cong(Nat, Nat, z => RD.Nat.monus(z, rs), 1n+rb, Nat.add(rs, 1n+d), eb1), R.Nat.monus_add(rs, 1n+d))
  +hs : {RD.Nat.lt(1n+d, rs) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(1n+d, rs), RD.Nat.lt(Nat.add(rs, 1n+d), Nat.add(rs, rs)), True{}, Equal.sym(Bool, RD.Nat.lt(Nat.add(rs, 1n+d), Nat.add(rs, rs)), RD.Nat.lt(1n+d, rs), BP.Lt.shift(rs, 1n+d, rs)),
    Equal.trans(Bool, RD.Nat.lt(Nat.add(rs, 1n+d), Nat.add(rs, rs)), RD.Nat.lt(1n+rb, Nat.double(rs)), True{},
      Equal.trans(Bool, RD.Nat.lt(Nat.add(rs, 1n+d), Nat.add(rs, rs)), RD.Nat.lt(1n+rb, Nat.add(rs, rs)), RD.Nat.lt(1n+rb, Nat.double(rs)), Equal.cong(Nat, Bool, z => RD.Nat.lt(z, Nat.add(rs, rs)), Nat.add(rs, 1n+d), 1n+rb, Equal.sym(Nat, 1n+rb, Nat.add(rs, 1n+d), eb1)),
        Equal.cong(Nat, Bool, z => RD.Nat.lt(1n+rb, z), Nat.add(rs, rs), Nat.double(rs), Equal.sym(Nat, Nat.double(rs), Nat.add(rs, rs), Y.Nat.double_add(rs)))), hrb1))
  +ek : {2n+d == rs : Nat} = E2.Le.anti(2n+d, rs, E2.Le.succ(1n+d, rs, hs), hs1)
  +erl0 : {P.Pz.rl(rs, rb) == 2n+d : Nat} = Equal.trans(Nat, P.Pz.rl(rs, rb), P.Pz.min(2n+d, rs), 2n+d, Rl.o(rs, rb, hz), Min.succ(1n+d, rs, hs))
  +erl1 : {P.Pz.rl(rs, 1n+rb) == rs : Nat} = Equal.trans(Nat, P.Pz.rl(rs, 1n+rb), P.Pz.min(2n+RD.Nat.monus(1n+rb, rs), rs), rs, Rl.o(rs, 1n+rb, hz1),
    Equal.trans(Nat, P.Pz.min(2n+RD.Nat.monus(1n+rb, rs), rs), P.Pz.min(3n+d, rs), rs, Equal.cong(Nat, Nat, z => P.Pz.min(2n+z, rs), RD.Nat.monus(1n+rb, rs), 1n+d, ed1),
      Equal.trans(Nat, P.Pz.min(3n+d, rs), P.Pz.min(1n+rs, rs), rs, Equal.cong(Nat, Nat, z => P.Pz.min(1n+z, rs), 2n+d, rs, ek), Min.top(rs))))
  +eu0 : {U(rs, rb) == 0n : Nat} = Equal.trans(Nat, U(rs, rb), RD.Nat.monus(rs, rs), 0n,
    Equal.trans(Nat, U(rs, rb), RD.Nat.monus(rs, 2n+d), RD.Nat.monus(rs, rs), Equal.cong(Nat, Nat, z => RD.Nat.monus(rs, z), P.Pz.rl(rs, rb), 2n+d, erl0), Equal.cong(Nat, Nat, z => RD.Nat.monus(rs, z), 2n+d, rs, ek)), Mo.self(rs))
  +eu1 : {U(rs, 1n+rb) == 0n : Nat} = Equal.trans(Nat, U(rs, 1n+rb), RD.Nat.monus(rs, rs), 0n, Equal.cong(Nat, Nat, z => RD.Nat.monus(rs, z), P.Pz.rl(rs, 1n+rb), rs, erl1), Mo.self(rs))
  +M1 = RD.Nat.monus(RD.Nat.pow2(1n+d), 1n)
  +M2 = RD.Nat.monus(RD.Nat.pow2(2n+d), 1n)
  +hs1b : {RD.Nat.lt(1n+RD.Nat.monus(1n+rb, rs), rs) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(1n+RD.Nat.monus(1n+rb, rs), rs), RD.Nat.lt(2n+d, rs), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(1n+z, rs), RD.Nat.monus(1n+rb, rs), 1n+d, ed1), hs1)
  +eR1 : {Rg(rs, 1n+rb) == Nat.mul(M2, 1n) : Nat} = Equal.trans(Nat, Rg(rs, 1n+rb), Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+RD.Nat.monus(1n+rb, rs)), 1n), 1n), Nat.mul(M2, 1n), Rg.o(rs, 1n+rb, hz1, False{}, hs1b),
    Equal.cong(Nat, Nat, z => Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+z), 1n), 1n), RD.Nat.monus(1n+rb, rs), 1n+d, ed1))
  +P1 = RD.Nat.pow2(1n+d)
  +P2 = RD.Nat.pow2(2n+d)
  +eP2 : {P2 == Nat.add(P1, P1) : Nat} = Y.Nat.double_add(P1)
  +eP1 : {P1 == 1n+M1 : Nat} = P2.Pw.pos(1n+d)
  +eP2b : {P2 == 1n+M2 : Nat} = P2.Pw.pos(2n+d)
  +env : List<&2, Nat> = [M1, M2, P1, P2, 0n, 0n, 1n, 2n]
  +c2 : {Nat.add(Nat.add(M1, M1), 1n) == M2 : Nat} = R.NatN.eq2(env, R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(6n)), R.V(1n), [], [], [R.Ad(R.Ad(R.V(2n), R.V(2n)), R.Ng(R.V(3n))), R.Ad(R.Ad(R.V(6n), R.V(0n)), R.Ng(R.V(2n))), R.Ad(R.Ad(R.V(6n), R.V(0n)), R.Ng(R.V(2n))), R.Ad(R.V(3n), R.Ng(R.Ad(R.V(6n), R.V(1n))))], {==}, Unit{}, (R.NatN.z(env, R.Ad(R.V(2n), R.V(2n)), R.V(3n), {==}, {==}, Equal.sym(Nat, P2, Nat.add(P1, P1), eP2)), (R.NatN.z(env, R.Ad(R.V(6n), R.V(0n)), R.V(2n), {==}, {==}, Equal.sym(Nat, P1, 1n+M1, eP1)), (R.NatN.z(env, R.Ad(R.V(6n), R.V(0n)), R.V(2n), {==}, {==}, Equal.sym(Nat, P1, 1n+M1, eP1)), (R.NatN.z(env, R.V(3n), R.Ad(R.V(6n), R.V(1n)), {==}, {==}, eP2b), Unit{})))), {==}, {==})
  +eM2 : {Nat.mul(M1, 2n) == Nat.add(M1, M1) : Nat} = Equal.trans(Nat, Nat.mul(M1, 2n), Nat.add(M1, Nat.mul(M1, 1n)), Nat.add(M1, M1), NL.Nat.mul_succ_r(M1, 1n), Equal.cong(Nat, Nat, z => Nat.add(M1, z), Nat.mul(M1, 1n), M1, NL.Nat.mul_one_r(M1)))
  +core : {Nat.add(Nat.mul(Nat.mul(M1, 2n), 1n), 1n) == Nat.mul(Nat.mul(M2, 1n), 1n) : Nat} = Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(M1, 2n), 1n), 1n), Nat.add(Nat.add(M1, M1), 1n), Nat.mul(Nat.mul(M2, 1n), 1n),
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(M1, 2n), 1n), 1n), Nat.add(Nat.mul(M1, 2n), 1n), Nat.add(Nat.add(M1, M1), 1n), Equal.cong(Nat, Nat, z => Nat.add(z, 1n), Nat.mul(Nat.mul(M1, 2n), 1n), Nat.mul(M1, 2n), NL.Nat.mul_one_r(Nat.mul(M1, 2n))),
      Equal.cong(Nat, Nat, z => Nat.add(z, 1n), Nat.mul(M1, 2n), Nat.add(M1, M1), eM2)),
    Equal.trans(Nat, Nat.add(Nat.add(M1, M1), 1n), M2, Nat.mul(Nat.mul(M2, 1n), 1n), c2,
      Equal.sym(Nat, Nat.mul(Nat.mul(M2, 1n), 1n), M2, Equal.trans(Nat, Nat.mul(Nat.mul(M2, 1n), 1n), Nat.mul(M2, 1n), M2, NL.Nat.mul_one_r(Nat.mul(M2, 1n)), NL.Nat.mul_one_r(M2)))))
  Step.of(rs, rb, Nat.mul(M1, 2n), 0n, Nat.mul(M2, 1n), 0n, Rg.o(rs, rb, hz, True{}, hs), eu0, eR1, eu1, core)

def Step.g3(+rs: Nat, +rb: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hz: {RD.Nat.lt(rb, rs) == True{} : Bool}, +hz1: {RD.Nat.lt(1n+rb, rs) == True{} : Bool}, s: Bool, +es2: {RD.Nat.lt(RD.Nat.monus(rs, rb), rs) == s : Bool})
  -> {StepL(rs, rb) == StepR(rs, rb) : Nat}:
  match s:
    case True{}:
      Step.zz(rs, rb, hz1, es2)
    case False{}:
      Step.z0(rs, rb, hrs, hz, es2)

def Step.g4(+rs: Nat, +rb: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hz: {RD.Nat.lt(rb, rs) == True{} : Bool}, +hz1: {RD.Nat.lt(1n+rb, rs) == False{} : Bool}, s: Bool, +es2: {RD.Nat.lt(RD.Nat.monus(rs, rb), rs) == s : Bool})
  -> {StepL(rs, rb) == StepR(rs, rb) : Nat}:
  match s:
    case True{}:
      Step.zo(rs, rb, hz, hz1, es2)
    case False{}:
      Step.z0(rs, rb, hrs, hz, es2)

def Step.g2(+rs: Nat, +rb: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hz: {RD.Nat.lt(rb, rs) == True{} : Bool}, z1: Bool, +ez1: {RD.Nat.lt(1n+rb, rs) == z1 : Bool})
  -> {StepL(rs, rb) == StepR(rs, rb) : Nat}:
  match z1:
    case True{}:
      Step.g3(rs, rb, hrs, hz, ez1, RD.Nat.lt(RD.Nat.monus(rs, rb), rs), {==})
    case False{}:
      Step.g4(rs, rb, hrs, hz, ez1, RD.Nat.lt(RD.Nat.monus(rs, rb), rs), {==})

def Step.g5(+rs: Nat, +rb: Nat, +hrb1: {RD.Nat.lt(1n+rb, Nat.double(rs)) == True{} : Bool}, +hz: {RD.Nat.lt(rb, rs) == False{} : Bool}, s: Bool, +es2: {RD.Nat.lt(2n+RD.Nat.monus(rb, rs), rs) == s : Bool})
  -> {StepL(rs, rb) == StepR(rs, rb) : Nat}:
  match s:
    case True{}:
      Step.oo(rs, rb, hz, es2)
    case False{}:
      Step.ol(rs, rb, hz, hrb1, es2)

def Step.g1(+rs: Nat, +rb: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb1: {RD.Nat.lt(1n+rb, Nat.double(rs)) == True{} : Bool}, z: Bool, +ez: {RD.Nat.lt(rb, rs) == z : Bool})
  -> {StepL(rs, rb) == StepR(rs, rb) : Nat}:
  match z:
    case True{}:
      Step.g2(rs, rb, hrs, ez, RD.Nat.lt(1n+rb, rs), {==})
    case False{}:
      Step.g5(rs, rb, hrb1, ez, RD.Nat.lt(2n+RD.Nat.monus(rb, rs), rs), {==})

# the regime carry: (R + 1) 2^u = R' 2^u' between classes rb and rb + 1
def Rg.step(+rs: Nat, +rb: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb1: {RD.Nat.lt(1n+rb, Nat.double(rs)) == True{} : Bool})
  -> {StepL(rs, rb) == StepR(rs, rb) : Nat}:
  Step.g1(rs, rb, hrs, hrb1, RD.Nat.lt(rb, rs), {==})

# Val + one unit in the last place: (2^fb + fr + 1) 2^(rb g + ee) / 2^(bias + fb)
def Nv(+p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat) -> D.Dy:
  +fb = P3.Fb(p01, rs, rb)
  D.Dy.of(Nat.add(Nat.mul(rs, RD.Nat.pow2(es)), fb), I.IPos{Nat.mul(1n+Nat.add(RD.Nat.pow2(fb), fr), RD.Nat.pow2(Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee)))})

def DecV(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +q: Nat) -> D.Dy:
  SB.Bd.val(1n+h1, P.Pz.dec(1n+h1, 1n+W(p01, es, rs), es, rs, q))

# fr + 1 < 2^fb: the next pattern is fr + 1
def Succ.f(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hf1: {RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool})
  -> {DecV(h1, p01, es, rs, 1n+Pat(p01, es, rs, rb, ee, fr)) == Nv(p01, es, rs, rb, ee, fr) : D.Dy}:
  +fb = P3.Fb(p01, rs, rb)
  +Pf = RD.Nat.pow2(fb)
  +X = Nat.add(Nat.mul(Rg(rs, rb), RD.Nat.pow2(Nat.add(es, fb))), Nat.mul(ee, Pf))
  +ep : {Pat(p01, es, rs, rb, ee, 1n+fr) == 1n+Pat(p01, es, rs, rb, ee, fr) : Nat} = NL.Nat.add_succ_r(X, fr)
  Equal.trans(D.Dy, DecV(h1, p01, es, rs, 1n+Pat(p01, es, rs, rb, ee, fr)), DecV(h1, p01, es, rs, Pat(p01, es, rs, rb, ee, 1n+fr)), Nv(p01, es, rs, rb, ee, fr),
    Equal.cong(Nat, D.Dy, z => DecV(h1, p01, es, rs, z), 1n+Pat(p01, es, rs, rb, ee, fr), Pat(p01, es, rs, rb, ee, 1n+fr), Equal.sym(Nat, Pat(p01, es, rs, rb, ee, 1n+fr), 1n+Pat(p01, es, rs, rb, ee, fr), ep)),
    Equal.trans(D.Dy, DecV(h1, p01, es, rs, Pat(p01, es, rs, rb, ee, 1n+fr)), Val(p01, es, rs, rb, ee, 1n+fr), Nv(p01, es, rs, rb, ee, fr),
      Dec.val(h1, p01, es, rs, rb, ee, 1n+fr, hrs, hrb, hee, hf1),
      Equal.cong(Nat, D.Dy, z => D.Dy.of(Nat.add(Nat.mul(rs, RD.Nat.pow2(es)), fb), I.IPos{Nat.mul(z, RD.Nat.pow2(Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee)))}), Nat.add(Pf, 1n+fr), 1n+Nat.add(Pf, fr), NL.Nat.add_succ_r(Pf, fr))))

# fr = 2^fb - 1, ee + 1 < 2^es: the next pattern carries into the exponent
def Succ.e(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool},
  +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool}, +hf1: {RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == False{} : Bool},
  +he1: {RD.Nat.lt(1n+ee, RD.Nat.pow2(es)) == True{} : Bool})
  -> {DecV(h1, p01, es, rs, 1n+Pat(p01, es, rs, rb, ee, fr)) == Nv(p01, es, rs, rb, ee, fr) : D.Dy}:
  +fb = P3.Fb(p01, rs, rb)
  +Pf = RD.Nat.pow2(fb)
  +g = RD.Nat.pow2(es)
  +rg = Nat.mul(rb, g)
  +RP = Nat.mul(Rg(rs, rb), RD.Nat.pow2(Nat.add(es, fb)))
  +E0 = Nat.mul(ee, Pf)
  +epf : {Pf == 1n+fr : Nat} = Equal.sym(Nat, 1n+fr, Pf, E2.Le.anti(1n+fr, Pf, E2.Le.succ(fr, Pf, hfr), hf1))
  +env : List<&2, Nat> = [RP, E0, Pf, fr, 1n, RD.Nat.pow2(Nat.add(rg, ee)), RD.Nat.pow2(Nat.add(rg, 1n+ee))]
  +ep0 : {Nat.add(RP, Nat.add(Pf, E0)) == 1n+Pat(p01, es, rs, rb, ee, fr) : Nat} = R.NatN.eq2(env, R.Ad(R.V(0n), R.Ad(R.V(2n), R.V(1n))), R.Ad(R.V(4n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.V(3n))), [], [], [R.Ad(R.V(2n), R.Ng(R.Ad(R.V(4n), R.V(3n))))], {==}, Unit{}, (R.NatN.z(env, R.V(2n), R.Ad(R.V(4n), R.V(3n)), {==}, {==}, epf), Unit{}), {==}, {==})
  +ep : {Pat(p01, es, rs, rb, 1n+ee, 0n) == 1n+Pat(p01, es, rs, rb, ee, fr) : Nat} = Equal.trans(Nat, Pat(p01, es, rs, rb, 1n+ee, 0n), Nat.add(RP, Nat.add(Pf, E0)), 1n+Pat(p01, es, rs, rb, ee, fr), NL.Nat.add_zero_r(Nat.add(RP, Nat.add(Pf, E0))), ep0)
  +PT = RD.Nat.pow2(Nat.add(rg, ee))
  +PT1 = RD.Nat.pow2(Nat.add(rg, 1n+ee))
  +et1 : {PT1 == Nat.add(PT, PT) : Nat} = Equal.trans(Nat, PT1, RD.Nat.pow2(1n+Nat.add(rg, ee)), Nat.add(PT, PT), Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), Nat.add(rg, 1n+ee), 1n+Nat.add(rg, ee), NL.Nat.add_succ_r(rg, ee)), Y.Nat.double_add(PT))
  +ev0 : {Nat.mul(Pf, PT1) == Nat.mul(1n+Nat.add(Pf, fr), PT) : Nat} = R.NatN.eq(env, R.Ml(R.V(2n), R.V(6n)), R.Ml(R.Ad(R.V(4n), R.Ad(R.V(2n), R.V(3n))), R.V(5n)), [R.V(2n), R.V(5n)], [R.Ad(R.V(6n), R.Ng(R.Ad(R.V(5n), R.V(5n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.V(4n), R.V(3n))))], {==}, (R.NatN.z(env, R.V(6n), R.Ad(R.V(5n), R.V(5n)), {==}, {==}, et1), (R.NatN.z(env, R.V(2n), R.Ad(R.V(4n), R.V(3n)), {==}, {==}, epf), Unit{})), {==}, {==})
  +ev : {Nat.mul(Nat.add(Pf, 0n), PT1) == Nat.mul(1n+Nat.add(Pf, fr), PT) : Nat} = Equal.trans(Nat, Nat.mul(Nat.add(Pf, 0n), PT1), Nat.mul(Pf, PT1), Nat.mul(1n+Nat.add(Pf, fr), PT), Equal.cong(Nat, Nat, z => Nat.mul(z, PT1), Nat.add(Pf, 0n), Pf, NL.Nat.add_zero_r(Pf)), ev0)
  Equal.trans(D.Dy, DecV(h1, p01, es, rs, 1n+Pat(p01, es, rs, rb, ee, fr)), DecV(h1, p01, es, rs, Pat(p01, es, rs, rb, 1n+ee, 0n)), Nv(p01, es, rs, rb, ee, fr),
    Equal.cong(Nat, D.Dy, z => DecV(h1, p01, es, rs, z), 1n+Pat(p01, es, rs, rb, ee, fr), Pat(p01, es, rs, rb, 1n+ee, 0n), Equal.sym(Nat, Pat(p01, es, rs, rb, 1n+ee, 0n), 1n+Pat(p01, es, rs, rb, ee, fr), ep)),
    Equal.trans(D.Dy, DecV(h1, p01, es, rs, Pat(p01, es, rs, rb, 1n+ee, 0n)), Val(p01, es, rs, rb, 1n+ee, 0n), Nv(p01, es, rs, rb, ee, fr),
      Dec.val(h1, p01, es, rs, rb, 1n+ee, 0n, hrs, hrb, he1, BP.Pow2.pos(fb)),
      Equal.cong(Nat, D.Dy, z => D.Dy.of(Nat.add(Nat.mul(rs, g), fb), I.IPos{z}), Nat.mul(Nat.add(Pf, 0n), PT1), Nat.mul(1n+Nat.add(Pf, fr), PT), ev)))

# fr = 2^fb - 1, ee = 2^es - 1, rb + 1 < 2 rs: the carry reaches the regime
def Succ.r(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb1: {RD.Nat.lt(1n+rb, Nat.double(rs)) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +he1: {RD.Nat.lt(1n+ee, RD.Nat.pow2(es)) == False{} : Bool},
  +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool}, +hf1: {RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == False{} : Bool})
  -> {DecV(h1, p01, es, rs, 1n+Pat(p01, es, rs, rb, ee, fr)) == Nv(p01, es, rs, rb, ee, fr) : D.Dy}:
  +fb = P3.Fb(p01, rs, rb)
  +fb2 = P3.Fb(p01, rs, 1n+rb)
  +u = U(rs, rb)
  +u2 = U(rs, 1n+rb)
  +g = RD.Nat.pow2(es)
  +bias = Nat.mul(rs, g)
  +rg = Nat.mul(rb, g)
  +Pf = RD.Nat.pow2(fb)
  +Pf2 = RD.Nat.pow2(fb2)
  +P = RD.Nat.pow2(Nat.add(es, fb))
  +P2 = RD.Nat.pow2(Nat.add(es, fb2))
  +C = RD.Nat.pow2(Nat.add(es, p01))
  +Pu = RD.Nat.pow2(u)
  +Pu2 = RD.Nat.pow2(u2)
  +R0 = Rg(rs, rb)
  +R2 = Rg(rs, 1n+rb)
  +epf : {Pf == 1n+fr : Nat} = Equal.sym(Nat, 1n+fr, Pf, E2.Le.anti(1n+fr, Pf, E2.Le.succ(fr, Pf, hfr), hf1))
  +eg : {g == 1n+ee : Nat} = Equal.sym(Nat, 1n+ee, g, E2.Le.anti(1n+ee, g, E2.Le.succ(ee, g, hee), he1))
  +eP : {P == Nat.mul(C, Pu) : Nat} = Equal.trans(Nat, P, RD.Nat.pow2(Nat.add(Nat.add(es, p01), u)), Nat.mul(C, Pu),
    Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), Nat.add(es, Nat.add(p01, u)), Nat.add(Nat.add(es, p01), u), Equal.sym(Nat, Nat.add(Nat.add(es, p01), u), Nat.add(es, Nat.add(p01, u)), NL.Nat.add_assoc(es, p01, u))),
    BP.Pow2.add(Nat.add(es, p01), u))
  +eP2 : {P2 == Nat.mul(C, Pu2) : Nat} = Equal.trans(Nat, P2, RD.Nat.pow2(Nat.add(Nat.add(es, p01), u2)), Nat.mul(C, Pu2),
    Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), Nat.add(es, Nat.add(p01, u2)), Nat.add(Nat.add(es, p01), u2), Equal.sym(Nat, Nat.add(Nat.add(es, p01), u2), Nat.add(es, Nat.add(p01, u2)), NL.Nat.add_assoc(es, p01, u2))),
    BP.Pow2.add(Nat.add(es, p01), u2))
  +estep : {Nat.mul(R2, Pu2) == Nat.add(Nat.mul(R0, Pu), Pu) : Nat} = Equal.sym(Nat, StepL(rs, rb), StepR(rs, rb), Rg.step(rs, rb, hrs, hrb1))
  +egp : {Nat.mul(g, Pf) == P : Nat} = Equal.sym(Nat, P, Nat.mul(g, Pf), BP.Pow2.add(es, fb))
  +eo : {Nat.mul(1n, Pf) == Pf : Nat} = P3.Mul.one_l(Pf)
  +env : List<&2, Nat> = [R0, R2, Pu, Pu2, C, P, P2, 1n, ee, fr, Pf, g]
  +ep0 : {Nat.mul(R2, P2) == 1n+Pat(p01, es, rs, rb, ee, fr) : Nat} = R.NatN.eq2(env, R.Ml(R.V(1n), R.V(6n)), R.Ad(R.V(7n), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(5n)), R.Ml(R.V(8n), R.V(10n))), R.V(9n))), [R.V(1n), R.V(4n), R.Ng(R.V(0n)), R.V(10n)], [R.Ad(R.V(6n), R.Ng(R.Ml(R.V(4n), R.V(3n)))), R.Ad(R.Ml(R.V(1n), R.V(3n)), R.Ng(R.Ad(R.Ml(R.V(0n), R.V(2n)), R.V(2n)))), R.Ad(R.V(5n), R.Ng(R.Ml(R.V(4n), R.V(2n)))), R.Ad(R.V(11n), R.Ng(R.Ad(R.V(7n), R.V(8n))))], [R.Ad(R.Ml(R.V(4n), R.V(2n)), R.Ng(R.V(5n))), R.Ad(R.V(5n), R.Ng(R.Ml(R.V(11n), R.V(10n)))), R.Ad(R.Ml(R.V(7n), R.V(10n)), R.Ng(R.V(10n))), R.Ad(R.V(10n), R.Ng(R.Ad(R.V(7n), R.V(9n))))], {==}, (R.NatN.z(env, R.V(6n), R.Ml(R.V(4n), R.V(3n)), {==}, {==}, eP2), (R.NatN.z(env, R.Ml(R.V(1n), R.V(3n)), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.V(2n)), {==}, {==}, estep), (R.NatN.z(env, R.V(5n), R.Ml(R.V(4n), R.V(2n)), {==}, {==}, eP), (R.NatN.z(env, R.V(11n), R.Ad(R.V(7n), R.V(8n)), {==}, {==}, eg), Unit{})))), (R.NatN.z(env, R.Ml(R.V(4n), R.V(2n)), R.V(5n), {==}, {==}, Equal.sym(Nat, P, Nat.mul(C, Pu), eP)), (R.NatN.z(env, R.V(5n), R.Ml(R.V(11n), R.V(10n)), {==}, {==}, Equal.sym(Nat, Nat.mul(g, Pf), P, egp)), (R.NatN.z(env, R.Ml(R.V(7n), R.V(10n)), R.V(10n), {==}, {==}, eo), (R.NatN.z(env, R.V(10n), R.Ad(R.V(7n), R.V(9n)), {==}, {==}, epf), Unit{})))), {==}, {==})
  +ep : {Pat(p01, es, rs, 1n+rb, 0n, 0n) == 1n+Pat(p01, es, rs, rb, ee, fr) : Nat} = Equal.trans(Nat, Pat(p01, es, rs, 1n+rb, 0n, 0n), Nat.add(Nat.mul(R2, P2), 0n), 1n+Pat(p01, es, rs, rb, ee, fr),
    NL.Nat.add_zero_r(Nat.add(Nat.mul(R2, P2), 0n)), Equal.trans(Nat, Nat.add(Nat.mul(R2, P2), 0n), Nat.mul(R2, P2), 1n+Pat(p01, es, rs, rb, ee, fr), NL.Nat.add_zero_r(Nat.mul(R2, P2)), ep0))
  # both values are 2^((rb + 1) g) / 2^bias
  +Z = RD.Nat.pow2(Nat.add(g, rg))
  +PT = RD.Nat.pow2(Nat.add(rg, ee))
  +eL : {Nat.mul(Nat.add(Pf2, 0n), RD.Nat.pow2(Nat.add(Nat.add(g, rg), 0n))) == Nat.mul(Z, Pf2) : Nat} = Equal.trans(Nat, Nat.mul(Nat.add(Pf2, 0n), RD.Nat.pow2(Nat.add(Nat.add(g, rg), 0n))), Nat.mul(Pf2, Z), Nat.mul(Z, Pf2),
    Equal.trans(Nat, Nat.mul(Nat.add(Pf2, 0n), RD.Nat.pow2(Nat.add(Nat.add(g, rg), 0n))), Nat.mul(Pf2, RD.Nat.pow2(Nat.add(Nat.add(g, rg), 0n))), Nat.mul(Pf2, Z),
      Equal.cong(Nat, Nat, z => Nat.mul(z, RD.Nat.pow2(Nat.add(Nat.add(g, rg), 0n))), Nat.add(Pf2, 0n), Pf2, NL.Nat.add_zero_r(Pf2)),
      Equal.cong(Nat, Nat, z => Nat.mul(Pf2, RD.Nat.pow2(z)), Nat.add(Nat.add(g, rg), 0n), Nat.add(g, rg), NL.Nat.add_zero_r(Nat.add(g, rg)))),
    NL.Nat.mul_comm(Pf2, Z))
  +vL : {Val(p01, es, rs, 1n+rb, 0n, 0n) == D.Dy.of(bias, I.IPos{Z}) : D.Dy} = Equal.trans(D.Dy, Val(p01, es, rs, 1n+rb, 0n, 0n), D.Dy.of(Nat.add(bias, fb2), D.Int.sh(fb2, I.IPos{Z})), D.Dy.of(bias, I.IPos{Z}),
    Equal.cong(I.Int, D.Dy, z => D.Dy.of(Nat.add(bias, fb2), z), I.IPos{Nat.mul(Nat.add(Pf2, 0n), RD.Nat.pow2(Nat.add(Nat.add(g, rg), 0n)))}, D.Int.sh(fb2, I.IPos{Z}),
      Equal.trans(I.Int, I.IPos{Nat.mul(Nat.add(Pf2, 0n), RD.Nat.pow2(Nat.add(Nat.add(g, rg), 0n)))}, I.IPos{Nat.mul(Z, Pf2)}, D.Int.sh(fb2, I.IPos{Z}),
        Equal.cong(Nat, I.Int, z => I.IPos{z}, Nat.mul(Nat.add(Pf2, 0n), RD.Nat.pow2(Nat.add(Nat.add(g, rg), 0n))), Nat.mul(Z, Pf2), eL), Equal.sym(I.Int, D.Int.sh(fb2, I.IPos{Z}), I.IPos{Nat.mul(Z, Pf2)}, R.Sh.ipos(fb2, Z)))),
    Y.Of.shift(fb2, bias, I.IPos{Z}))
  +eZ : {Z == Nat.add(PT, PT) : Nat} = Equal.trans(Nat, Z, RD.Nat.pow2(1n+Nat.add(rg, ee)), Nat.add(PT, PT),
    Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), Nat.add(g, rg), 1n+Nat.add(rg, ee),
      Equal.trans(Nat, Nat.add(g, rg), Nat.add(rg, g), 1n+Nat.add(rg, ee), NL.Nat.add_comm(g, rg),
        Equal.trans(Nat, Nat.add(rg, g), Nat.add(rg, 1n+ee), 1n+Nat.add(rg, ee), Equal.cong(Nat, Nat, z => Nat.add(rg, z), g, 1n+ee, eg), NL.Nat.add_succ_r(rg, ee)))),
    Y.Nat.double_add(PT))
  +env3 : List<&2, Nat> = [Pf, fr, 1n, PT, Z]
  +eV : {Nat.mul(1n+Nat.add(Pf, fr), PT) == Nat.mul(Z, Pf) : Nat} = R.NatN.eq(env3, R.Ml(R.Ad(R.V(2n), R.Ad(R.V(0n), R.V(1n))), R.V(3n)), R.Ml(R.V(4n), R.V(0n)), [R.Ng(R.V(0n)), R.Ng(R.V(3n))], [R.Ad(R.V(4n), R.Ng(R.Ad(R.V(3n), R.V(3n)))), R.Ad(R.V(0n), R.Ng(R.Ad(R.V(2n), R.V(1n))))], {==}, (R.NatN.z(env3, R.V(4n), R.Ad(R.V(3n), R.V(3n)), {==}, {==}, eZ), (R.NatN.z(env3, R.V(0n), R.Ad(R.V(2n), R.V(1n)), {==}, {==}, epf), Unit{})), {==}, {==})
  +vR : {Nv(p01, es, rs, rb, ee, fr) == D.Dy.of(bias, I.IPos{Z}) : D.Dy} = Equal.trans(D.Dy, Nv(p01, es, rs, rb, ee, fr), D.Dy.of(Nat.add(bias, fb), D.Int.sh(fb, I.IPos{Z})), D.Dy.of(bias, I.IPos{Z}),
    Equal.cong(I.Int, D.Dy, z => D.Dy.of(Nat.add(bias, fb), z), I.IPos{Nat.mul(1n+Nat.add(Pf, fr), PT)}, D.Int.sh(fb, I.IPos{Z}),
      Equal.trans(I.Int, I.IPos{Nat.mul(1n+Nat.add(Pf, fr), PT)}, I.IPos{Nat.mul(Z, Pf)}, D.Int.sh(fb, I.IPos{Z}),
        Equal.cong(Nat, I.Int, z => I.IPos{z}, Nat.mul(1n+Nat.add(Pf, fr), PT), Nat.mul(Z, Pf), eV), Equal.sym(I.Int, D.Int.sh(fb, I.IPos{Z}), I.IPos{Nat.mul(Z, Pf)}, R.Sh.ipos(fb, Z)))),
    Y.Of.shift(fb, bias, I.IPos{Z}))
  Equal.trans(D.Dy, DecV(h1, p01, es, rs, 1n+Pat(p01, es, rs, rb, ee, fr)), DecV(h1, p01, es, rs, Pat(p01, es, rs, 1n+rb, 0n, 0n)), Nv(p01, es, rs, rb, ee, fr),
    Equal.cong(Nat, D.Dy, z => DecV(h1, p01, es, rs, z), 1n+Pat(p01, es, rs, rb, ee, fr), Pat(p01, es, rs, 1n+rb, 0n, 0n), Equal.sym(Nat, Pat(p01, es, rs, 1n+rb, 0n, 0n), 1n+Pat(p01, es, rs, rb, ee, fr), ep)),
    Equal.trans(D.Dy, DecV(h1, p01, es, rs, Pat(p01, es, rs, 1n+rb, 0n, 0n)), Val(p01, es, rs, 1n+rb, 0n, 0n), Nv(p01, es, rs, rb, ee, fr),
      Dec.val(h1, p01, es, rs, 1n+rb, 0n, 0n, hrs, hrb1, BP.Pow2.pos(es), BP.Pow2.pos(fb2)),
      Equal.trans(D.Dy, Val(p01, es, rs, 1n+rb, 0n, 0n), D.Dy.of(bias, I.IPos{Z}), Nv(p01, es, rs, rb, ee, fr), vL, Equal.sym(D.Dy, Nv(p01, es, rs, rb, ee, fr), D.Dy.of(bias, I.IPos{Z}), vR))))

def Succ.ge(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool}, +hf1: {RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == False{} : Bool},
  hnext: {RD.Nat.lt(1n+ee, RD.Nat.pow2(es)) == False{} : Bool} -> {RD.Nat.lt(1n+rb, Nat.double(rs)) == True{} : Bool}, e: Bool, +ee1: {RD.Nat.lt(1n+ee, RD.Nat.pow2(es)) == e : Bool})
  -> {DecV(h1, p01, es, rs, 1n+Pat(p01, es, rs, rb, ee, fr)) == Nv(p01, es, rs, rb, ee, fr) : D.Dy}:
  match e:
    case True{}:
      Succ.e(h1, p01, es, rs, rb, ee, fr, hrs, hrb, hfr, hf1, ee1)
    case False{}:
      Succ.r(h1, p01, es, rs, rb, ee, fr, hrs, hnext(ee1), hee, ee1, hfr, hf1)

def Succ.gf(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool},
  hnext: {RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == False{} : Bool} -> {RD.Nat.lt(1n+ee, RD.Nat.pow2(es)) == False{} : Bool} -> {RD.Nat.lt(1n+rb, Nat.double(rs)) == True{} : Bool},
  f: Bool, +ef: {RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == f : Bool})
  -> {DecV(h1, p01, es, rs, 1n+Pat(p01, es, rs, rb, ee, fr)) == Nv(p01, es, rs, rb, ee, fr) : D.Dy}:
  match f:
    case True{}:
      Succ.f(h1, p01, es, rs, rb, ee, fr, hrs, hrb, hee, ef)
    case False{}:
      Succ.ge(h1, p01, es, rs, rb, ee, fr, hrs, hrb, hee, hfr, ef, hnext(ef), RD.Nat.lt(1n+ee, RD.Nat.pow2(es)), {==})

# The next pattern is the next value: unless Pat is the largest pattern
# (fr, ee and rb all at their maxima), pattern Pat + 1 decodes to
# Val + 2^(rb g + ee - bias - fb), one unit in Pat's last place up.
def Succ.val(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool},
  hnext: {RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == False{} : Bool} -> {RD.Nat.lt(1n+ee, RD.Nat.pow2(es)) == False{} : Bool} -> {RD.Nat.lt(1n+rb, Nat.double(rs)) == True{} : Bool})
  -> {DecV(h1, p01, es, rs, 1n+Pat(p01, es, rs, rb, ee, fr)) == Nv(p01, es, rs, rb, ee, fr) : D.Dy}:
  Succ.gf(h1, p01, es, rs, rb, ee, fr, hrs, hrb, hee, hfr, hnext, RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))), {==})

# The standard's rounding
# -----------------------

# m 2^s / 2^D = m 2^T / 2^B when T + D = s + B
def Scale(+M: Nat, +s: Nat, +D: Nat, +T: Nat, +Bx: Nat, +hD: {Nat.add(T, D) == Nat.add(s, Bx) : Nat})
  -> {D.Dy.of(D, I.IPos{Nat.mul(M, RD.Nat.pow2(s))}) == D.Dy.of(Bx, I.IPos{Nat.mul(M, RD.Nat.pow2(T))}) : D.Dy}:
  +Ps = RD.Nat.pow2(s)
  +PB = RD.Nat.pow2(Bx)
  +PT = RD.Nat.pow2(T)
  +PD = RD.Nat.pow2(D)
  +PE = RD.Nat.pow2(Nat.add(s, Bx))
  +e1 : {PE == Nat.mul(Ps, PB) : Nat} = BP.Pow2.add(s, Bx)
  +e2 : {PE == Nat.mul(PT, PD) : Nat} = Equal.trans(Nat, PE, RD.Nat.pow2(Nat.add(T, D)), Nat.mul(PT, PD), Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), Nat.add(s, Bx), Nat.add(T, D), Equal.sym(Nat, Nat.add(T, D), Nat.add(s, Bx), hD)), BP.Pow2.add(T, D))
  +env : List<&2, Nat> = [M, Ps, PB, PT, PD, PE]
  +em : {Nat.mul(Nat.mul(M, Ps), PB) == Nat.mul(Nat.mul(M, PT), PD) : Nat} = R.NatN.eq(env, R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(2n)), R.Ml(R.Ml(R.V(0n), R.V(3n)), R.V(4n)), [R.Ng(R.V(0n)), R.V(0n)], [R.Ad(R.V(5n), R.Ng(R.Ml(R.V(1n), R.V(2n)))), R.Ad(R.V(5n), R.Ng(R.Ml(R.V(3n), R.V(4n))))], {==},
    (R.NatN.z(env, R.V(5n), R.Ml(R.V(1n), R.V(2n)), {==}, {==}, e1), (R.NatN.z(env, R.V(5n), R.Ml(R.V(3n), R.V(4n)), {==}, {==}, e2), Unit{})), {==}, {==})
  +l : {D.Dy.of(Nat.add(D, Bx), D.Int.sh(Bx, I.IPos{Nat.mul(M, Ps)})) == D.Dy.of(D, I.IPos{Nat.mul(M, Ps)}) : D.Dy} = Y.Of.shift(Bx, D, I.IPos{Nat.mul(M, Ps)})
  +r : {D.Dy.of(Nat.add(Bx, D), D.Int.sh(D, I.IPos{Nat.mul(M, PT)})) == D.Dy.of(Bx, I.IPos{Nat.mul(M, PT)}) : D.Dy} = Y.Of.shift(D, Bx, I.IPos{Nat.mul(M, PT)})
  +mid : {D.Dy.of(Nat.add(D, Bx), D.Int.sh(Bx, I.IPos{Nat.mul(M, Ps)})) == D.Dy.of(Nat.add(Bx, D), D.Int.sh(D, I.IPos{Nat.mul(M, PT)})) : D.Dy} =
    Y.Of.cong(Nat.add(D, Bx), Nat.add(Bx, D), D.Int.sh(Bx, I.IPos{Nat.mul(M, Ps)}), D.Int.sh(D, I.IPos{Nat.mul(M, PT)}), NL.Nat.add_comm(D, Bx),
      Equal.trans(I.Int, D.Int.sh(Bx, I.IPos{Nat.mul(M, Ps)}), I.IPos{Nat.mul(Nat.mul(M, Ps), PB)}, D.Int.sh(D, I.IPos{Nat.mul(M, PT)}), R.Sh.ipos(Bx, Nat.mul(M, Ps)),
        Equal.trans(I.Int, I.IPos{Nat.mul(Nat.mul(M, Ps), PB)}, I.IPos{Nat.mul(Nat.mul(M, PT), PD)}, D.Int.sh(D, I.IPos{Nat.mul(M, PT)}), Equal.cong(Nat, I.Int, z => I.IPos{z}, Nat.mul(Nat.mul(M, Ps), PB), Nat.mul(Nat.mul(M, PT), PD), em),
          Equal.sym(I.Int, D.Int.sh(D, I.IPos{Nat.mul(M, PT)}), I.IPos{Nat.mul(Nat.mul(M, PT), PD)}, R.Sh.ipos(D, Nat.mul(M, PT))))))
  Equal.trans(D.Dy, D.Dy.of(D, I.IPos{Nat.mul(M, Ps)}), D.Dy.of(Nat.add(D, Bx), D.Int.sh(Bx, I.IPos{Nat.mul(M, Ps)})), D.Dy.of(Bx, I.IPos{Nat.mul(M, PT)}), Equal.sym(D.Dy, D.Dy.of(Nat.add(D, Bx), D.Int.sh(Bx, I.IPos{Nat.mul(M, Ps)})), D.Dy.of(D, I.IPos{Nat.mul(M, Ps)}), l),
    Equal.trans(D.Dy, D.Dy.of(Nat.add(D, Bx), D.Int.sh(Bx, I.IPos{Nat.mul(M, Ps)})), D.Dy.of(Nat.add(Bx, D), D.Int.sh(D, I.IPos{Nat.mul(M, PT)})), D.Dy.of(Bx, I.IPos{Nat.mul(M, PT)}), mid, r))

# with fb >= 1 a pattern's last bit is its significand's: Pat and
# 2^fb + fr are both fr plus an even number
def Par(+p02: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat)
  -> {D.Nat.even(Pat(1n+p02, es, rs, rb, ee, fr)) == D.Nat.even(P3.Sig(1n+p02, rs, rb, fr)) : Bool}:
  +f1 = Nat.add(p02, RD.Nat.monus(rs, P.Pz.rl(rs, rb)))
  +Q0 = RD.Nat.pow2(Nat.add(es, f1))
  +F0 = RD.Nat.pow2(f1)
  +P = RD.Nat.pow2(Nat.add(es, 1n+f1))
  +R0 = Rg(rs, rb)
  +X = Nat.add(Nat.mul(R0, Q0), Nat.mul(ee, F0))
  +eP : {P == Nat.add(Q0, Q0) : Nat} = Equal.trans(Nat, P, RD.Nat.pow2(1n+Nat.add(es, f1)), Nat.add(Q0, Q0), Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), Nat.add(es, 1n+f1), 1n+Nat.add(es, f1), NL.Nat.add_succ_r(es, f1)), Y.Nat.double_add(Q0))
  +eF : {Nat.double(F0) == Nat.add(F0, F0) : Nat} = Y.Nat.double_add(F0)
  +eX : {Nat.double(X) == Nat.add(X, X) : Nat} = Y.Nat.double_add(X)
  +env : List<&2, Nat> = [R0, Q0, F0, P, ee, fr, Nat.double(F0), Nat.double(X)]
  +e1 : {Pat(1n+p02, es, rs, rb, ee, fr) == Nat.add(Nat.double(X), fr) : Nat} = R.NatN.eq2(env, R.Ad(R.Ad(R.Ml(R.V(0n), R.V(3n)), R.Ml(R.V(4n), R.V(6n))), R.V(5n)), R.Ad(R.V(7n), R.V(5n)),
    [R.V(0n), R.V(4n)], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(1n), R.V(1n)))), R.Ad(R.V(6n), R.Ng(R.Ad(R.V(2n), R.V(2n))))],
    [R.Ad(R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(4n), R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(4n), R.V(2n)))), R.Ng(R.V(7n)))], {==},
    (R.NatN.z(env, R.V(3n), R.Ad(R.V(1n), R.V(1n)), {==}, {==}, eP), (R.NatN.z(env, R.V(6n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, eF), Unit{})),
    (R.NatN.z(env, R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(4n), R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(4n), R.V(2n)))), R.V(7n), {==}, {==}, Equal.sym(Nat, Nat.double(X), Nat.add(X, X), eX)), Unit{}), {==}, {==})
  Equal.trans(Bool, D.Nat.even(Pat(1n+p02, es, rs, rb, ee, fr)), D.Nat.even(fr), D.Nat.even(P3.Sig(1n+p02, rs, rb, fr)),
    Equal.trans(Bool, D.Nat.even(Pat(1n+p02, es, rs, rb, ee, fr)), D.Nat.even(Nat.add(Nat.double(X), fr)), D.Nat.even(fr), Equal.cong(Nat, Bool, z => D.Nat.even(z), Pat(1n+p02, es, rs, rb, ee, fr), Nat.add(Nat.double(X), fr), e1), BP.Ev.dw(X, fr)),
    Equal.sym(Bool, D.Nat.even(Nat.add(Nat.double(F0), fr)), D.Nat.even(fr), BP.Ev.dw(F0, fr)))

# The bits of x past pattern q are t / 2^s in binary: the guard bit is the
# first of them (2t >= 2^s) and, given the guard bit, the sticky bit (any
# later bit set) is 2t > 2^s. The standard rounds q up when guard and
# (sticky or q odd).
def Gd(+t: Nat, +s: Nat) -> Bool:
  Bool.not(RD.Nat.lt(Nat.double(t), RD.Nat.pow2(s)))

def St(+t: Nat, +s: Nat) -> Bool:
  RD.Nat.lt(RD.Nat.pow2(s), Nat.double(t))

def BitRnd(+q: Nat, +gd: Bool, +st: Bool) -> Nat:
  Bool.pick(Nat, Bool.and(gd, Bool.or(st, Bool.not(D.Nat.even(q)))), 1n+q, q)

def Std.go(+h1: Nat, +p02: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +D: Nat, +s: Nat, +t: Nat,
  +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(1n+p02, rs, rb))) == True{} : Bool},
  +hD: {Nat.add(Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee), D) == Nat.add(s, Nat.add(P.Pz.bias(RD.Nat.pow2(es), rs), P3.Fb(1n+p02, rs, rb))) : Nat},
  hnext: {P3.Rup(P3.Sig(1n+p02, rs, rb, fr), t, s) == True{} : Bool} -> {RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(1n+p02, rs, rb))) == False{} : Bool} -> {RD.Nat.lt(1n+ee, RD.Nat.pow2(es)) == False{} : Bool} -> {RD.Nat.lt(1n+rb, Nat.double(rs)) == True{} : Bool},
  u: Bool, +eu: {P3.Rup(P3.Sig(1n+p02, rs, rb, fr), t, s) == u : Bool})
  -> {D.Dy.of(D, I.IPos{Bool.pick(Nat, u, Nat.mul(1n+P3.Sig(1n+p02, rs, rb, fr), RD.Nat.pow2(s)), Nat.mul(P3.Sig(1n+p02, rs, rb, fr), RD.Nat.pow2(s)))}) == DecV(h1, 1n+p02, es, rs, Bool.pick(Nat, u, 1n+Pat(1n+p02, es, rs, rb, ee, fr), Pat(1n+p02, es, rs, rb, ee, fr))) : D.Dy}:
  match u:
    case True{}:
      +a = P3.Sig(1n+p02, rs, rb, fr)
      +fb = P3.Fb(1n+p02, rs, rb)
      +B0 = Nat.add(Nat.mul(rs, RD.Nat.pow2(es)), fb)
      +T = Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee)
      Equal.trans(D.Dy, D.Dy.of(D, I.IPos{Nat.mul(1n+a, RD.Nat.pow2(s))}), Nv(1n+p02, es, rs, rb, ee, fr), DecV(h1, 1n+p02, es, rs, 1n+Pat(1n+p02, es, rs, rb, ee, fr)),
        Scale(1n+a, s, D, T, B0, hD),
        Equal.sym(D.Dy, DecV(h1, 1n+p02, es, rs, 1n+Pat(1n+p02, es, rs, rb, ee, fr)), Nv(1n+p02, es, rs, rb, ee, fr), Succ.val(h1, 1n+p02, es, rs, rb, ee, fr, hrs, hrb, hee, hfr, hnext(eu))))
    case False{}:
      +a = P3.Sig(1n+p02, rs, rb, fr)
      +fb = P3.Fb(1n+p02, rs, rb)
      +B0 = Nat.add(Nat.mul(rs, RD.Nat.pow2(es)), fb)
      +T = Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee)
      Equal.trans(D.Dy, D.Dy.of(D, I.IPos{Nat.mul(a, RD.Nat.pow2(s))}), Val(1n+p02, es, rs, rb, ee, fr), DecV(h1, 1n+p02, es, rs, Pat(1n+p02, es, rs, rb, ee, fr)),
        Scale(a, s, D, T, B0, hD),
        Equal.sym(D.Dy, DecV(h1, 1n+p02, es, rs, Pat(1n+p02, es, rs, rb, ee, fr)), Val(1n+p02, es, rs, rb, ee, fr), Dec.val(h1, 1n+p02, es, rs, rb, ee, fr, hrs, hrb, hee, hfr)))

# T3. b-posit rounding is the standard's rounding of the bit string. A
# value x = (a 2^s + t) / 2^D, t < 2^s, between the pattern q = Pat of
# fields (rb, ee, fr), worth a 2^s / 2^D with a = 2^fb + fr, and the next
# pattern up, rounds under Pz.fl to the value the decoder gives the
# standard's rounded pattern: q + 1 when guard and (sticky or q odd), else
# q. Every x in [minpos, maxpos] has such a spelling, any D large enough.
# Assumes p0 >= 2 (one fraction bit at least, so q's last bit is a's), and
# that rounding up does not pass the largest pattern.
def Std.round(+h1: Nat, +p02: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +D: Nat, +s: Nat, +t: Nat,
  +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(1n+p02, rs, rb))) == True{} : Bool},
  +ht: {RD.Nat.lt(t, RD.Nat.pow2(s)) == True{} : Bool},
  +hD: {Nat.add(Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee), D) == Nat.add(s, Nat.add(P.Pz.bias(RD.Nat.pow2(es), rs), P3.Fb(1n+p02, rs, rb))) : Nat},
  +hti: {P.Pz.tiny(1n+1n+p02, P.Pz.bias(RD.Nat.pow2(es), rs), D.Dy.of(D, I.IPos{P3.Xn(P3.Sig(1n+p02, rs, rb, fr), s, t)})) == False{} : Bool},
  +hov: {P.Pz.over(1n+1n+p02, P.Pz.bias(RD.Nat.pow2(es), rs), D.Dy.of(D, I.IPos{P3.Xn(P3.Sig(1n+p02, rs, rb, fr), s, t)})) == False{} : Bool},
  hnext: {P3.Rup(P3.Sig(1n+p02, rs, rb, fr), t, s) == True{} : Bool} -> {RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(1n+p02, rs, rb))) == False{} : Bool} -> {RD.Nat.lt(1n+ee, RD.Nat.pow2(es)) == False{} : Bool} -> {RD.Nat.lt(1n+rb, Nat.double(rs)) == True{} : Bool})
  -> {P.Pz.fl(1n+1n+p02, RD.Nat.pow2(es), rs, D.Dy.of(D, I.IPos{P3.Xn(P3.Sig(1n+p02, rs, rb, fr), s, t)})) == DecV(h1, 1n+p02, es, rs, BitRnd(Pat(1n+p02, es, rs, rb, ee, fr), Gd(t, s), St(t, s))) : D.Dy}:
  +p01 : Nat = 1n+p02
  +a = P3.Sig(p01, rs, rb, fr)
  +q = Pat(p01, es, rs, rb, ee, fr)
  +x = D.Dy.of(D, I.IPos{P3.Xn(a, s, t)})
  +s1 : {P.Pz.fl(1n+p01, RD.Nat.pow2(es), rs, x) == D.Dy.of(D, I.IPos{P3.RnF(a, s, t)}) : D.Dy} = P3.Fl.at(p01, es, rs, rb, ee, fr, D, s, t, hrb, hee, hfr, ht, hD, hti, hov)
  +epar : {D.Nat.even(q) == D.Nat.even(a) : Bool} = Par(p02, es, rs, rb, ee, fr)
  +eb : {BitRnd(q, Gd(t, s), St(t, s)) == Bool.pick(Nat, P3.Rup(a, t, s), 1n+q, q) : Nat} = Equal.cong(Bool, Nat, z => Bool.pick(Nat, Bool.and(Gd(t, s), Bool.or(St(t, s), Bool.not(z))), 1n+q, q), D.Nat.even(q), D.Nat.even(a), epar)
  Equal.trans(D.Dy, P.Pz.fl(1n+p01, RD.Nat.pow2(es), rs, x), D.Dy.of(D, I.IPos{P3.RnF(a, s, t)}), DecV(h1, p01, es, rs, BitRnd(q, Gd(t, s), St(t, s))), s1,
    Equal.trans(D.Dy, D.Dy.of(D, I.IPos{P3.RnF(a, s, t)}), DecV(h1, p01, es, rs, Bool.pick(Nat, P3.Rup(a, t, s), 1n+q, q)), DecV(h1, p01, es, rs, BitRnd(q, Gd(t, s), St(t, s))),
      Std.go(h1, p02, es, rs, rb, ee, fr, D, s, t, hrs, hrb, hee, hfr, hD, hnext, P3.Rup(a, t, s), {==}),
      Equal.cong(Nat, D.Dy, z => DecV(h1, p01, es, rs, z), Bool.pick(Nat, P3.Rup(a, t, s), 1n+q, q), BitRnd(q, Gd(t, s), St(t, s)), Equal.sym(Nat, BitRnd(q, Gd(t, s), St(t, s)), Bool.pick(Nat, P3.Rup(a, t, s), 1n+q, q), eb))))

# Every positive pattern
# ----------------------
# Pat steps by one through the field triples, from Pat(0, 0, 0) = 0 to the
# largest, 2^w - 1 (Pat.last). So the k-th triple has pattern k, for every
# k < 2^w (Nth.pat), and Dec.val decodes every positive pattern.

def Pat.f(+p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat) -> {Pat(p01, es, rs, rb, ee, 1n+fr) == 1n+Pat(p01, es, rs, rb, ee, fr) : Nat}:
  +fb = P3.Fb(p01, rs, rb)
  NL.Nat.add_succ_r(Nat.add(Nat.mul(Rg(rs, rb), RD.Nat.pow2(Nat.add(es, fb))), Nat.mul(ee, RD.Nat.pow2(fb))), fr)

def Pat.e(+p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +epf: {RD.Nat.pow2(P3.Fb(p01, rs, rb)) == 1n+fr : Nat})
  -> {Pat(p01, es, rs, rb, 1n+ee, 0n) == 1n+Pat(p01, es, rs, rb, ee, fr) : Nat}:
  +fb = P3.Fb(p01, rs, rb)
  +Pf = RD.Nat.pow2(fb)
  +RP = Nat.mul(Rg(rs, rb), RD.Nat.pow2(Nat.add(es, fb)))
  +E0 = Nat.mul(ee, Pf)
  +env : List<&2, Nat> = [RP, E0, Pf, fr, 1n]
  +ep0 : {Nat.add(RP, Nat.add(Pf, E0)) == 1n+Pat(p01, es, rs, rb, ee, fr) : Nat} = R.NatN.eq2(env, R.Ad(R.V(0n), R.Ad(R.V(2n), R.V(1n))), R.Ad(R.V(4n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.V(3n))), [], [], [R.Ad(R.V(2n), R.Ng(R.Ad(R.V(4n), R.V(3n))))], {==}, Unit{}, (R.NatN.z(env, R.V(2n), R.Ad(R.V(4n), R.V(3n)), {==}, {==}, epf), Unit{}), {==}, {==})
  Equal.trans(Nat, Pat(p01, es, rs, rb, 1n+ee, 0n), Nat.add(RP, Nat.add(Pf, E0)), 1n+Pat(p01, es, rs, rb, ee, fr), NL.Nat.add_zero_r(Nat.add(RP, Nat.add(Pf, E0))), ep0)

def Pat.r(+p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb1: {RD.Nat.lt(1n+rb, Nat.double(rs)) == True{} : Bool},
  +epf: {RD.Nat.pow2(P3.Fb(p01, rs, rb)) == 1n+fr : Nat}, +eg: {RD.Nat.pow2(es) == 1n+ee : Nat})
  -> {Pat(p01, es, rs, 1n+rb, 0n, 0n) == 1n+Pat(p01, es, rs, rb, ee, fr) : Nat}:
  +fb = P3.Fb(p01, rs, rb)
  +fb2 = P3.Fb(p01, rs, 1n+rb)
  +u = U(rs, rb)
  +u2 = U(rs, 1n+rb)
  +g = RD.Nat.pow2(es)
  +Pf = RD.Nat.pow2(fb)
  +P = RD.Nat.pow2(Nat.add(es, fb))
  +P2 = RD.Nat.pow2(Nat.add(es, fb2))
  +C = RD.Nat.pow2(Nat.add(es, p01))
  +Pu = RD.Nat.pow2(u)
  +Pu2 = RD.Nat.pow2(u2)
  +R0 = Rg(rs, rb)
  +R2 = Rg(rs, 1n+rb)
  +eP : {P == Nat.mul(C, Pu) : Nat} = Equal.trans(Nat, P, RD.Nat.pow2(Nat.add(Nat.add(es, p01), u)), Nat.mul(C, Pu),
    Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), Nat.add(es, Nat.add(p01, u)), Nat.add(Nat.add(es, p01), u), Equal.sym(Nat, Nat.add(Nat.add(es, p01), u), Nat.add(es, Nat.add(p01, u)), NL.Nat.add_assoc(es, p01, u))),
    BP.Pow2.add(Nat.add(es, p01), u))
  +eP2 : {P2 == Nat.mul(C, Pu2) : Nat} = Equal.trans(Nat, P2, RD.Nat.pow2(Nat.add(Nat.add(es, p01), u2)), Nat.mul(C, Pu2),
    Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), Nat.add(es, Nat.add(p01, u2)), Nat.add(Nat.add(es, p01), u2), Equal.sym(Nat, Nat.add(Nat.add(es, p01), u2), Nat.add(es, Nat.add(p01, u2)), NL.Nat.add_assoc(es, p01, u2))),
    BP.Pow2.add(Nat.add(es, p01), u2))
  +estep : {Nat.mul(R2, Pu2) == Nat.add(Nat.mul(R0, Pu), Pu) : Nat} = Equal.sym(Nat, StepL(rs, rb), StepR(rs, rb), Rg.step(rs, rb, hrs, hrb1))
  +egp : {Nat.mul(g, Pf) == P : Nat} = Equal.sym(Nat, P, Nat.mul(g, Pf), BP.Pow2.add(es, fb))
  +eo : {Nat.mul(1n, Pf) == Pf : Nat} = P3.Mul.one_l(Pf)
  +env : List<&2, Nat> = [R0, R2, Pu, Pu2, C, P, P2, 1n, ee, fr, Pf, g]
  +ep0 : {Nat.mul(R2, P2) == 1n+Pat(p01, es, rs, rb, ee, fr) : Nat} = R.NatN.eq2(env, R.Ml(R.V(1n), R.V(6n)), R.Ad(R.V(7n), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(5n)), R.Ml(R.V(8n), R.V(10n))), R.V(9n))), [R.V(1n), R.V(4n), R.Ng(R.V(0n)), R.V(10n)], [R.Ad(R.V(6n), R.Ng(R.Ml(R.V(4n), R.V(3n)))), R.Ad(R.Ml(R.V(1n), R.V(3n)), R.Ng(R.Ad(R.Ml(R.V(0n), R.V(2n)), R.V(2n)))), R.Ad(R.V(5n), R.Ng(R.Ml(R.V(4n), R.V(2n)))), R.Ad(R.V(11n), R.Ng(R.Ad(R.V(7n), R.V(8n))))], [R.Ad(R.Ml(R.V(4n), R.V(2n)), R.Ng(R.V(5n))), R.Ad(R.V(5n), R.Ng(R.Ml(R.V(11n), R.V(10n)))), R.Ad(R.Ml(R.V(7n), R.V(10n)), R.Ng(R.V(10n))), R.Ad(R.V(10n), R.Ng(R.Ad(R.V(7n), R.V(9n))))], {==}, (R.NatN.z(env, R.V(6n), R.Ml(R.V(4n), R.V(3n)), {==}, {==}, eP2), (R.NatN.z(env, R.Ml(R.V(1n), R.V(3n)), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.V(2n)), {==}, {==}, estep), (R.NatN.z(env, R.V(5n), R.Ml(R.V(4n), R.V(2n)), {==}, {==}, eP), (R.NatN.z(env, R.V(11n), R.Ad(R.V(7n), R.V(8n)), {==}, {==}, eg), Unit{})))), (R.NatN.z(env, R.Ml(R.V(4n), R.V(2n)), R.V(5n), {==}, {==}, Equal.sym(Nat, P, Nat.mul(C, Pu), eP)), (R.NatN.z(env, R.V(5n), R.Ml(R.V(11n), R.V(10n)), {==}, {==}, Equal.sym(Nat, Nat.mul(g, Pf), P, egp)), (R.NatN.z(env, R.Ml(R.V(7n), R.V(10n)), R.V(10n), {==}, {==}, eo), (R.NatN.z(env, R.V(10n), R.Ad(R.V(7n), R.V(9n)), {==}, {==}, epf), Unit{})))), {==}, {==})
  Equal.trans(Nat, Pat(p01, es, rs, 1n+rb, 0n, 0n), Nat.add(Nat.mul(R2, P2), 0n), 1n+Pat(p01, es, rs, rb, ee, fr),
    NL.Nat.add_zero_r(Nat.add(Nat.mul(R2, P2), 0n)), Equal.trans(Nat, Nat.add(Nat.mul(R2, P2), 0n), Nat.mul(R2, P2), 1n+Pat(p01, es, rs, rb, ee, fr), NL.Nat.add_zero_r(Nat.mul(R2, P2)), ep0))

# the largest triple (rb = 2 rs - 1, ee = 2^es - 1, fr = 2^fb - 1) is 2^w - 1
def Pat.last(+p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool},
  +elast: {1n+rb == Nat.double(rs) : Nat}, +eg: {RD.Nat.pow2(es) == 1n+ee : Nat}, +epf: {RD.Nat.pow2(P3.Fb(p01, rs, rb)) == 1n+fr : Nat})
  -> {1n+Pat(p01, es, rs, rb, ee, fr) == RD.Nat.pow2(W(p01, es, rs)) : Nat}:
  +r1 = RD.Nat.monus(rs, 1n)
  +ers : {rs == 1n+r1 : Nat} = BP.Lt.wit(0n, rs)(hrs)
  +erb : {rb == Nat.add(rs, r1) : Nat} = Equal.cong(Nat, Nat, z => BP.Pd(z), 1n+rb, 1n+Nat.add(rs, r1),
    Equal.trans(Nat, 1n+rb, Nat.add(rs, rs), 1n+Nat.add(rs, r1), Equal.trans(Nat, 1n+rb, Nat.double(rs), Nat.add(rs, rs), elast, Y.Nat.double_add(rs)),
      Equal.trans(Nat, Nat.add(rs, rs), Nat.add(rs, 1n+r1), 1n+Nat.add(rs, r1), Equal.cong(Nat, Nat, z => Nat.add(rs, z), rs, 1n+r1, ers), NL.Nat.add_succ_r(rs, r1))))
  +hz : {RD.Nat.lt(rb, rs) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(rb, rs), RD.Nat.lt(Nat.add(rs, r1), rs), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, rs), rb, Nat.add(rs, r1), erb), BP.Lt.ge(rs, r1))
  +ed : {RD.Nat.monus(rb, rs) == r1 : Nat} = Equal.trans(Nat, RD.Nat.monus(rb, rs), RD.Nat.monus(Nat.add(rs, r1), rs), r1, Equal.cong(Nat, Nat, z => RD.Nat.monus(z, rs), rb, Nat.add(rs, r1), erb), R.Nat.monus_add(rs, r1))
  +hs : {RD.Nat.lt(1n+RD.Nat.monus(rb, rs), rs) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(1n+RD.Nat.monus(rb, rs), rs), RD.Nat.lt(1n+r1, rs), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(1n+z, rs), RD.Nat.monus(rb, rs), r1, ed),
    Equal.trans(Bool, RD.Nat.lt(1n+r1, rs), RD.Nat.lt(1n+r1, 1n+r1), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(1n+r1, z), rs, 1n+r1, ers), Lt.irr(1n+r1)))
  +M = RD.Nat.monus(RD.Nat.pow2(rs), 1n)
  +eR : {Rg(rs, rb) == M : Nat} = Equal.trans(Nat, Rg(rs, rb), Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+RD.Nat.monus(rb, rs)), 1n), 1n), M, Rg.o(rs, rb, hz, False{}, hs),
    Equal.trans(Nat, Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+RD.Nat.monus(rb, rs)), 1n), 1n), Nat.mul(M, 1n), M,
      Equal.cong(Nat, Nat, z => Nat.mul(RD.Nat.monus(RD.Nat.pow2(z), 1n), 1n), 1n+RD.Nat.monus(rb, rs), rs, Equal.trans(Nat, 1n+RD.Nat.monus(rb, rs), 1n+r1, rs, Equal.cong(Nat, Nat, z => 1n+z, RD.Nat.monus(rb, rs), r1, ed), Equal.sym(Nat, rs, 1n+r1, ers))),
      NL.Nat.mul_one_r(M)))
  +erl : {P.Pz.rl(rs, rb) == rs : Nat} = Equal.trans(Nat, P.Pz.rl(rs, rb), P.Pz.min(2n+RD.Nat.monus(rb, rs), rs), rs, Rl.o(rs, rb, hz),
    Equal.trans(Nat, P.Pz.min(2n+RD.Nat.monus(rb, rs), rs), P.Pz.min(1n+rs, rs), rs,
      Equal.cong(Nat, Nat, z => P.Pz.min(1n+z, rs), 1n+RD.Nat.monus(rb, rs), rs, Equal.trans(Nat, 1n+RD.Nat.monus(rb, rs), 1n+r1, rs, Equal.cong(Nat, Nat, z => 1n+z, RD.Nat.monus(rb, rs), r1, ed), Equal.sym(Nat, rs, 1n+r1, ers))),
      Min.top(rs)))
  +fb = P3.Fb(p01, rs, rb)
  +g = RD.Nat.pow2(es)
  +Pf = RD.Nat.pow2(fb)
  +P = RD.Nat.pow2(Nat.add(es, fb))
  +Prs = RD.Nat.pow2(rs)
  +PW = RD.Nat.pow2(W(p01, es, rs))
  +eW : {PW == Nat.mul(Prs, P) : Nat} = Equal.trans(Nat, PW, RD.Nat.pow2(Nat.add(rs, Nat.add(es, fb))), Nat.mul(Prs, P),
    Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), W(p01, es, rs), Nat.add(rs, Nat.add(es, fb)), Equal.trans(Nat, W(p01, es, rs), Nat.add(P.Pz.rl(rs, rb), Nat.add(es, fb)), Nat.add(rs, Nat.add(es, fb)), W.split(p01, es, rs, rb), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(es, fb)), P.Pz.rl(rs, rb), rs, erl))),
    BP.Pow2.add(rs, Nat.add(es, fb)))
  +eM : {Prs == 1n+M : Nat} = P2.Pw.pos(rs)
  +egp : {Nat.mul(g, Pf) == P : Nat} = Equal.sym(Nat, P, Nat.mul(g, Pf), BP.Pow2.add(es, fb))
  +eoP : {Nat.mul(1n, P) == P : Nat} = P3.Mul.one_l(P)
  +eoF : {Nat.mul(1n, Pf) == Pf : Nat} = P3.Mul.one_l(Pf)
  +env : List<&2, Nat> = [M, Prs, P, g, Pf, ee, fr, PW, 1n]
  +eN : {1n+Nat.add(Nat.add(Nat.mul(M, P), Nat.mul(ee, Pf)), fr) == PW : Nat} = R.NatN.eq2(env, R.Ad(R.V(8n), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ml(R.V(5n), R.V(4n))), R.V(6n))), R.V(7n), [R.Ng(R.V(2n)), R.Ng(R.V(4n))], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(8n), R.V(0n)))), R.Ad(R.V(3n), R.Ng(R.Ad(R.V(8n), R.V(5n))))], [R.Ad(R.Ml(R.V(1n), R.V(2n)), R.Ng(R.V(7n))), R.Ad(R.Ad(R.V(8n), R.V(6n)), R.Ng(R.V(4n))), R.Ad(R.V(2n), R.Ng(R.Ml(R.V(8n), R.V(2n)))), R.Ad(R.Ml(R.V(3n), R.V(4n)), R.Ng(R.V(2n))), R.Ad(R.V(4n), R.Ng(R.Ml(R.V(8n), R.V(4n))))], {==}, (R.NatN.z(env, R.V(1n), R.Ad(R.V(8n), R.V(0n)), {==}, {==}, eM), (R.NatN.z(env, R.V(3n), R.Ad(R.V(8n), R.V(5n)), {==}, {==}, eg), Unit{})), (R.NatN.z(env, R.Ml(R.V(1n), R.V(2n)), R.V(7n), {==}, {==}, Equal.sym(Nat, PW, Nat.mul(Prs, P), eW)), (R.NatN.z(env, R.Ad(R.V(8n), R.V(6n)), R.V(4n), {==}, {==}, Equal.sym(Nat, Pf, 1n+fr, epf)), (R.NatN.z(env, R.V(2n), R.Ml(R.V(8n), R.V(2n)), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, P), P, eoP)), (R.NatN.z(env, R.Ml(R.V(3n), R.V(4n)), R.V(2n), {==}, {==}, egp), (R.NatN.z(env, R.V(4n), R.Ml(R.V(8n), R.V(4n)), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Pf), Pf, eoF)), Unit{}))))), {==}, {==})
  Equal.trans(Nat, 1n+Pat(p01, es, rs, rb, ee, fr), 1n+Nat.add(Nat.add(Nat.mul(M, P), Nat.mul(ee, Pf)), fr), PW,
    Equal.cong(Nat, Nat, z => 1n+Nat.add(Nat.add(Nat.mul(z, P), Nat.mul(ee, Pf)), fr), Rg(rs, rb), M, eR), eN)

type Fld is Data:
  Fld{rb: Nat, ee: Nat, fr: Nat}

def Fld.ok(+p01: Nat, +es: Nat, +rs: Nat, f: Fld) -> Bool:
  match f:
    case Fld{+rb, +ee, +fr}:
      Bool.and(RD.Nat.lt(rb, Nat.double(rs)), Bool.and(RD.Nat.lt(ee, RD.Nat.pow2(es)), RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb)))))

def Fld.pat(+p01: Nat, +es: Nat, +rs: Nat, f: Fld) -> Nat:
  match f:
    case Fld{+rb, +ee, +fr}:
      Pat(p01, es, rs, rb, ee, fr)

def Fld.val(+p01: Nat, +es: Nat, +rs: Nat, f: Fld) -> D.Dy:
  match f:
    case Fld{+rb, +ee, +fr}:
      Val(p01, es, rs, rb, ee, fr)

# the next triple: fr + 1, else carry into ee, else into rb
def Fld.next(+p01: Nat, +es: Nat, +rs: Nat, f: Fld) -> Fld:
  match f:
    case Fld{+rb, +ee, +fr}:
      Bool.pick(Fld, RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))), Fld{rb, ee, 1n+fr}, Bool.pick(Fld, RD.Nat.lt(1n+ee, RD.Nat.pow2(es)), Fld{rb, 1n+ee, 0n}, Fld{1n+rb, 0n, 0n}))

def Fld.nth(+p01: Nat, +es: Nat, +rs: Nat, k: Nat) -> Fld:
  match k:
    case 0n:
      Fld{0n, 0n, 0n}
    case 1n+j:
      Fld.next(p01, es, rs, Fld.nth(p01, es, rs, j))

def Inv(+p01: Nat, +es: Nat, +rs: Nat, +f: Fld, +k: Nat) -> Bool:
  Bool.and(Fld.ok(p01, es, rs, f), Nat.is_eq(Fld.pat(p01, es, rs, f), k))

def Inv.mk(+p01: Nat, +es: Nat, +rs: Nat, +f: Fld, +k: Nat, +hok: {Fld.ok(p01, es, rs, f) == True{} : Bool}, +hp: {Fld.pat(p01, es, rs, f) == k : Nat}) -> {Inv(p01, es, rs, f, k) == True{} : Bool}:
  Equal.trans(Bool, Inv(p01, es, rs, f, k), Bool.and(True{}, Nat.is_eq(Fld.pat(p01, es, rs, f), k)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(Fld.pat(p01, es, rs, f), k)), Fld.ok(p01, es, rs, f), True{}, hok),
    Equal.trans(Bool, Nat.is_eq(Fld.pat(p01, es, rs, f), k), Nat.is_eq(k, k), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, k), Fld.pat(p01, es, rs, f), k, hp), P2.Eq.refl(k)))

def And3(+a: Bool, +b: Bool, +c: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}, +hc: {c == True{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(a, Bool.and(b, c)), Bool.and(True{}, Bool.and(b, c)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Bool.and(b, c)), a, True{}, ha),
    Equal.trans(Bool, Bool.and(b, c), Bool.and(True{}, c), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, c), b, True{}, hb), hc))

def Nx.r(+p01: Nat, +es: Nat, +rs: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +rb: Nat, +ee: Nat, +fr: Nat, +k: Nat,
  +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}, +epat: {Pat(p01, es, rs, rb, ee, fr) == k : Nat}, +hk1: {RD.Nat.lt(1n+k, RD.Nat.pow2(W(p01, es, rs))) == True{} : Bool},
  +epf: {RD.Nat.pow2(P3.Fb(p01, rs, rb)) == 1n+fr : Nat}, +eg: {RD.Nat.pow2(es) == 1n+ee : Nat}, c: Bool, +ec: {RD.Nat.lt(1n+rb, Nat.double(rs)) == c : Bool})
  -> {Inv(p01, es, rs, Fld{1n+rb, 0n, 0n}, 1n+k) == True{} : Bool}:
  match c:
    case True{}:
      Inv.mk(p01, es, rs, Fld{1n+rb, 0n, 0n}, 1n+k, And3(RD.Nat.lt(1n+rb, Nat.double(rs)), RD.Nat.lt(0n, RD.Nat.pow2(es)), RD.Nat.lt(0n, RD.Nat.pow2(P3.Fb(p01, rs, 1n+rb))), ec, BP.Pow2.pos(es), BP.Pow2.pos(P3.Fb(p01, rs, 1n+rb))),
        Equal.trans(Nat, Pat(p01, es, rs, 1n+rb, 0n, 0n), 1n+Pat(p01, es, rs, rb, ee, fr), 1n+k, Pat.r(p01, es, rs, rb, ee, fr, hrs, ec, epf, eg), Equal.cong(Nat, Nat, z => 1n+z, Pat(p01, es, rs, rb, ee, fr), k, epat)))
    case False{}:
      +elast : {1n+rb == Nat.double(rs) : Nat} = E2.Le.anti(1n+rb, Nat.double(rs), E2.Le.succ(rb, Nat.double(rs), hrb), ec)
      +ew : {1n+k == RD.Nat.pow2(W(p01, es, rs)) : Nat} = Equal.trans(Nat, 1n+k, 1n+Pat(p01, es, rs, rb, ee, fr), RD.Nat.pow2(W(p01, es, rs)), Equal.cong(Nat, Nat, z => 1n+z, k, Pat(p01, es, rs, rb, ee, fr), Equal.sym(Nat, Pat(p01, es, rs, rb, ee, fr), k, epat)), Pat.last(p01, es, rs, rb, ee, fr, hrs, elast, eg, epf))
      B.Bool.tf({Inv(p01, es, rs, Fld{1n+rb, 0n, 0n}, 1n+k) == True{} : Bool}, Equal.trans(Bool, True{}, RD.Nat.lt(1n+k, RD.Nat.pow2(W(p01, es, rs))), False{}, Equal.sym(Bool, RD.Nat.lt(1n+k, RD.Nat.pow2(W(p01, es, rs))), True{}, hk1),
        Equal.trans(Bool, RD.Nat.lt(1n+k, RD.Nat.pow2(W(p01, es, rs))), RD.Nat.lt(RD.Nat.pow2(W(p01, es, rs)), RD.Nat.pow2(W(p01, es, rs))), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, RD.Nat.pow2(W(p01, es, rs))), 1n+k, RD.Nat.pow2(W(p01, es, rs)), ew), Lt.irr(RD.Nat.pow2(W(p01, es, rs))))))

def Nx.e(+p01: Nat, +es: Nat, +rs: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +rb: Nat, +ee: Nat, +fr: Nat, +k: Nat,
  +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}, +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +epat: {Pat(p01, es, rs, rb, ee, fr) == k : Nat}, +hk1: {RD.Nat.lt(1n+k, RD.Nat.pow2(W(p01, es, rs))) == True{} : Bool},
  +epf: {RD.Nat.pow2(P3.Fb(p01, rs, rb)) == 1n+fr : Nat}, c: Bool, +ec: {RD.Nat.lt(1n+ee, RD.Nat.pow2(es)) == c : Bool})
  -> {Inv(p01, es, rs, Bool.pick(Fld, c, Fld{rb, 1n+ee, 0n}, Fld{1n+rb, 0n, 0n}), 1n+k) == True{} : Bool}:
  match c:
    case True{}:
      Inv.mk(p01, es, rs, Fld{rb, 1n+ee, 0n}, 1n+k, And3(RD.Nat.lt(rb, Nat.double(rs)), RD.Nat.lt(1n+ee, RD.Nat.pow2(es)), RD.Nat.lt(0n, RD.Nat.pow2(P3.Fb(p01, rs, rb))), hrb, ec, BP.Pow2.pos(P3.Fb(p01, rs, rb))),
        Equal.trans(Nat, Pat(p01, es, rs, rb, 1n+ee, 0n), 1n+Pat(p01, es, rs, rb, ee, fr), 1n+k, Pat.e(p01, es, rs, rb, ee, fr, epf), Equal.cong(Nat, Nat, z => 1n+z, Pat(p01, es, rs, rb, ee, fr), k, epat)))
    case False{}:
      +eg : {RD.Nat.pow2(es) == 1n+ee : Nat} = Equal.sym(Nat, 1n+ee, RD.Nat.pow2(es), E2.Le.anti(1n+ee, RD.Nat.pow2(es), E2.Le.succ(ee, RD.Nat.pow2(es), hee), ec))
      Nx.r(p01, es, rs, hrs, rb, ee, fr, k, hrb, epat, hk1, epf, eg, RD.Nat.lt(1n+rb, Nat.double(rs)), {==})

def Nx.f(+p01: Nat, +es: Nat, +rs: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +rb: Nat, +ee: Nat, +fr: Nat, +k: Nat,
  +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}, +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool},
  +epat: {Pat(p01, es, rs, rb, ee, fr) == k : Nat}, +hk1: {RD.Nat.lt(1n+k, RD.Nat.pow2(W(p01, es, rs))) == True{} : Bool}, c: Bool, +ec: {RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == c : Bool})
  -> {Inv(p01, es, rs, Bool.pick(Fld, c, Fld{rb, ee, 1n+fr}, Bool.pick(Fld, RD.Nat.lt(1n+ee, RD.Nat.pow2(es)), Fld{rb, 1n+ee, 0n}, Fld{1n+rb, 0n, 0n})), 1n+k) == True{} : Bool}:
  match c:
    case True{}:
      Inv.mk(p01, es, rs, Fld{rb, ee, 1n+fr}, 1n+k, And3(RD.Nat.lt(rb, Nat.double(rs)), RD.Nat.lt(ee, RD.Nat.pow2(es)), RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))), hrb, hee, ec),
        Equal.trans(Nat, Pat(p01, es, rs, rb, ee, 1n+fr), 1n+Pat(p01, es, rs, rb, ee, fr), 1n+k, Pat.f(p01, es, rs, rb, ee, fr), Equal.cong(Nat, Nat, z => 1n+z, Pat(p01, es, rs, rb, ee, fr), k, epat)))
    case False{}:
      +epf : {RD.Nat.pow2(P3.Fb(p01, rs, rb)) == 1n+fr : Nat} = Equal.sym(Nat, 1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb)), E2.Le.anti(1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb)), E2.Le.succ(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb)), hfr), ec))
      Nx.e(p01, es, rs, hrs, rb, ee, fr, k, hrb, hee, epat, hk1, epf, RD.Nat.lt(1n+ee, RD.Nat.pow2(es)), {==})

def Nx(+p01: Nat, +es: Nat, +rs: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, f: Fld, +k: Nat, +hinv: {Inv(p01, es, rs, f, k) == True{} : Bool}, +hk1: {RD.Nat.lt(1n+k, RD.Nat.pow2(W(p01, es, rs))) == True{} : Bool})
  -> {Inv(p01, es, rs, Fld.next(p01, es, rs, f), 1n+k) == True{} : Bool}:
  match f:
    case Fld{+rb, +ee, +fr}:
      +ok = Fld.ok(p01, es, rs, Fld{rb, ee, fr})
      +hok : {ok == True{} : Bool} = NP.Bool.and_l(ok, Nat.is_eq(Pat(p01, es, rs, rb, ee, fr), k), hinv)
      +epat : {Pat(p01, es, rs, rb, ee, fr) == k : Nat} = P2.Eq.true(Pat(p01, es, rs, rb, ee, fr), k, NP.Bool.and_r(ok, Nat.is_eq(Pat(p01, es, rs, rb, ee, fr), k), hinv))
      +b2 = Bool.and(RD.Nat.lt(ee, RD.Nat.pow2(es)), RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))))
      +hrb : {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool} = NP.Bool.and_l(RD.Nat.lt(rb, Nat.double(rs)), b2, hok)
      +h2 : {b2 == True{} : Bool} = NP.Bool.and_r(RD.Nat.lt(rb, Nat.double(rs)), b2, hok)
      +hee : {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool} = NP.Bool.and_l(RD.Nat.lt(ee, RD.Nat.pow2(es)), RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))), h2)
      +hfr : {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool} = NP.Bool.and_r(RD.Nat.lt(ee, RD.Nat.pow2(es)), RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))), h2)
      Nx.f(p01, es, rs, hrs, rb, ee, fr, k, hrb, hee, hfr, epat, hk1, RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))), {==})

# the k-th triple is a triple and its pattern is k, for every k < 2^w
def Nth.pat(+p01: Nat, +es: Nat, +rs: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, k: Nat, +hk: {RD.Nat.lt(k, RD.Nat.pow2(W(p01, es, rs))) == True{} : Bool})
  -> {Inv(p01, es, rs, Fld.nth(p01, es, rs, k), k) == True{} : Bool}:
  match k:
    case 0n:
      +hs0 : {RD.Nat.lt(RD.Nat.monus(rs, 0n), rs) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(RD.Nat.monus(rs, 0n), rs), RD.Nat.lt(rs, rs), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, rs), RD.Nat.monus(rs, 0n), rs, BP.Mo.z(rs)), Lt.irr(rs))
      +eR : {Rg(rs, 0n) == 0n : Nat} = Rg.z(rs, 0n, hrs, False{}, hs0)
      +hd : {RD.Nat.lt(0n, Nat.double(rs)) == True{} : Bool} = E2.Lt.le_trans(0n, rs, Nat.double(rs), hrs, E2.Le.dbl(rs))
      Inv.mk(p01, es, rs, Fld{0n, 0n, 0n}, 0n, And3(RD.Nat.lt(0n, Nat.double(rs)), RD.Nat.lt(0n, RD.Nat.pow2(es)), RD.Nat.lt(0n, RD.Nat.pow2(P3.Fb(p01, rs, 0n))), hd, BP.Pow2.pos(es), BP.Pow2.pos(P3.Fb(p01, rs, 0n))),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.mul(z, RD.Nat.pow2(Nat.add(es, P3.Fb(p01, rs, 0n)))), Nat.mul(0n, RD.Nat.pow2(P3.Fb(p01, rs, 0n)))), 0n), Rg(rs, 0n), 0n, eR))
    case 1n+(+j):
      +hj : {RD.Nat.lt(j, RD.Nat.pow2(W(p01, es, rs))) == True{} : Bool} = E2.Lt.le_trans(j, 1n+j, RD.Nat.pow2(W(p01, es, rs)), E2.Lt.succ(j), E2.Lt.to_le(1n+j, RD.Nat.pow2(W(p01, es, rs)), hk))
      Nx(p01, es, rs, hrs, Fld.nth(p01, es, rs, j), j, Nth.pat(p01, es, rs, hrs, j, hj), hk)

def Dec.fld(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, f: Fld, +hok: {Fld.ok(p01, es, rs, f) == True{} : Bool})
  -> {DecV(h1, p01, es, rs, Fld.pat(p01, es, rs, f)) == Fld.val(p01, es, rs, f) : D.Dy}:
  match f:
    case Fld{+rb, +ee, +fr}:
      +b2 = Bool.and(RD.Nat.lt(ee, RD.Nat.pow2(es)), RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))))
      +h2 : {b2 == True{} : Bool} = NP.Bool.and_r(RD.Nat.lt(rb, Nat.double(rs)), b2, hok)
      Dec.val(h1, p01, es, rs, rb, ee, fr, hrs, NP.Bool.and_l(RD.Nat.lt(rb, Nat.double(rs)), b2, hok),
        NP.Bool.and_l(RD.Nat.lt(ee, RD.Nat.pow2(es)), RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))), h2), NP.Bool.and_r(RD.Nat.lt(ee, RD.Nat.pow2(es)), RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))), h2))

# T1 for every pattern: each q < 2^w (every positive b-posit) decodes to
# the value of its triple, the q-th
def Dec.all(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +q: Nat, +hq: {RD.Nat.lt(q, RD.Nat.pow2(W(p01, es, rs))) == True{} : Bool})
  -> {DecV(h1, p01, es, rs, q) == Fld.val(p01, es, rs, Fld.nth(p01, es, rs, q)) : D.Dy}:
  +f = Fld.nth(p01, es, rs, q)
  +hinv : {Inv(p01, es, rs, f, q) == True{} : Bool} = Nth.pat(p01, es, rs, hrs, q, hq)
  +hok : {Fld.ok(p01, es, rs, f) == True{} : Bool} = NP.Bool.and_l(Fld.ok(p01, es, rs, f), Nat.is_eq(Fld.pat(p01, es, rs, f), q), hinv)
  +ep : {Fld.pat(p01, es, rs, f) == q : Nat} = P2.Eq.true(Fld.pat(p01, es, rs, f), q, NP.Bool.and_r(Fld.ok(p01, es, rs, f), Nat.is_eq(Fld.pat(p01, es, rs, f), q), hinv))
  Equal.trans(D.Dy, DecV(h1, p01, es, rs, q), DecV(h1, p01, es, rs, Fld.pat(p01, es, rs, f)), Fld.val(p01, es, rs, f),
    Equal.cong(Nat, D.Dy, z => DecV(h1, p01, es, rs, z), q, Fld.pat(p01, es, rs, f), Equal.sym(Nat, Fld.pat(p01, es, rs, f), q, ep)), Dec.fld(h1, p01, es, rs, hrs, f, hok))

# x above the largest pattern
# ---------------------------
# Rounding up from the largest pattern would leave maxpos: x > maxpos
# whenever bias >= p0 (maxpos >= 1), so Pz.over holds.

def Canl(+k: Nat, +a: Nat, +b: Nat, +e: {Nat.add(k, a) == Nat.add(k, b) : Nat}) -> {a == b : Nat}:
  +l1 : {RD.Nat.lt(b, a) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(b, a), RD.Nat.lt(Nat.add(k, b), Nat.add(k, a)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.add(k, b), Nat.add(k, a)), RD.Nat.lt(b, a), BP.Lt.shift(k, b, a)),
    Equal.trans(Bool, RD.Nat.lt(Nat.add(k, b), Nat.add(k, a)), RD.Nat.lt(Nat.add(k, b), Nat.add(k, b)), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.add(k, b), z), Nat.add(k, a), Nat.add(k, b), e), Lt.irr(Nat.add(k, b))))
  +l2 : {RD.Nat.lt(a, b) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(a, b), RD.Nat.lt(Nat.add(k, a), Nat.add(k, b)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.add(k, a), Nat.add(k, b)), RD.Nat.lt(a, b), BP.Lt.shift(k, a, b)),
    Equal.trans(Bool, RD.Nat.lt(Nat.add(k, a), Nat.add(k, b)), RD.Nat.lt(Nat.add(k, a), Nat.add(k, a)), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.add(k, a), z), Nat.add(k, b), Nat.add(k, a), Equal.sym(Nat, Nat.add(k, a), Nat.add(k, b), e)), Lt.irr(Nat.add(k, a))))
  E2.Le.anti(a, b, l1, l2)

# the last class has the full ones run: regime length rs, so fb = p01
def Last.fb(+p01: Nat, +rs: Nat, +rb: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +elast: {1n+rb == Nat.double(rs) : Nat}) -> {P3.Fb(p01, rs, rb) == p01 : Nat}:
  +r1 = RD.Nat.monus(rs, 1n)
  +ers : {rs == 1n+r1 : Nat} = BP.Lt.wit(0n, rs)(hrs)
  +erb : {rb == Nat.add(rs, r1) : Nat} = Equal.cong(Nat, Nat, z => BP.Pd(z), 1n+rb, 1n+Nat.add(rs, r1),
    Equal.trans(Nat, 1n+rb, Nat.add(rs, rs), 1n+Nat.add(rs, r1), Equal.trans(Nat, 1n+rb, Nat.double(rs), Nat.add(rs, rs), elast, Y.Nat.double_add(rs)),
      Equal.trans(Nat, Nat.add(rs, rs), Nat.add(rs, 1n+r1), 1n+Nat.add(rs, r1), Equal.cong(Nat, Nat, z => Nat.add(rs, z), rs, 1n+r1, ers), NL.Nat.add_succ_r(rs, r1))))
  +hz : {RD.Nat.lt(rb, rs) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(rb, rs), RD.Nat.lt(Nat.add(rs, r1), rs), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, rs), rb, Nat.add(rs, r1), erb), BP.Lt.ge(rs, r1))
  +ed : {RD.Nat.monus(rb, rs) == r1 : Nat} = Equal.trans(Nat, RD.Nat.monus(rb, rs), RD.Nat.monus(Nat.add(rs, r1), rs), r1, Equal.cong(Nat, Nat, z => RD.Nat.monus(z, rs), rb, Nat.add(rs, r1), erb), R.Nat.monus_add(rs, r1))
  +erl : {P.Pz.rl(rs, rb) == rs : Nat} = Equal.trans(Nat, P.Pz.rl(rs, rb), P.Pz.min(2n+RD.Nat.monus(rb, rs), rs), rs, Rl.o(rs, rb, hz),
    Equal.trans(Nat, P.Pz.min(2n+RD.Nat.monus(rb, rs), rs), P.Pz.min(1n+rs, rs), rs,
      Equal.cong(Nat, Nat, z => P.Pz.min(1n+z, rs), 1n+RD.Nat.monus(rb, rs), rs, Equal.trans(Nat, 1n+RD.Nat.monus(rb, rs), 1n+r1, rs, Equal.cong(Nat, Nat, z => 1n+z, RD.Nat.monus(rb, rs), r1, ed), Equal.sym(Nat, rs, 1n+r1, ers))),
      Min.top(rs)))
  Equal.trans(Nat, P3.Fb(p01, rs, rb), Nat.add(p01, RD.Nat.monus(rs, rs)), p01, Equal.cong(Nat, Nat, z => Nat.add(p01, RD.Nat.monus(rs, z)), P.Pz.rl(rs, rb), rs, erl),
    Equal.trans(Nat, Nat.add(p01, RD.Nat.monus(rs, rs)), Nat.add(p01, 0n), p01, Equal.cong(Nat, Nat, z => Nat.add(p01, z), RD.Nat.monus(rs, rs), 0n, Mo.self(rs)), NL.Nat.add_zero_r(p01)))

# rounding up needs t > 0
def T.pos(+t: Nat, +s: Nat, +h: {RD.Nat.lt(Nat.double(t), RD.Nat.pow2(s)) == False{} : Bool}) -> {RD.Nat.lt(0n, t) == True{} : Bool}:
  match t:
    case 0n:
      B.Bool.tf({RD.Nat.lt(0n, 0n) == True{} : Bool}, Equal.trans(Bool, True{}, RD.Nat.lt(0n, RD.Nat.pow2(s)), False{}, Equal.sym(Bool, RD.Nat.lt(0n, RD.Nat.pow2(s)), True{}, BP.Pow2.pos(s)), h))
    case 1n+t2:
      {==}

def Last.over(+p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +D: Nat, +s: Nat, +t: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool},
  +elast: {1n+rb == Nat.double(rs) : Nat}, +eg: {RD.Nat.pow2(es) == 1n+ee : Nat}, +epf: {RD.Nat.pow2(P3.Fb(p01, rs, rb)) == 1n+fr : Nat},
  +hbp: {RD.Nat.lt(P.Pz.bias(RD.Nat.pow2(es), rs), 1n+p01) == False{} : Bool},
  +hD: {Nat.add(Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee), D) == Nat.add(s, Nat.add(P.Pz.bias(RD.Nat.pow2(es), rs), P3.Fb(p01, rs, rb))) : Nat},
  +hup: {P3.Rup(P3.Sig(p01, rs, rb, fr), t, s) == True{} : Bool})
  -> {P.Pz.over(1n+p01, P.Pz.bias(RD.Nat.pow2(es), rs), D.Dy.of(D, I.IPos{P3.Xn(P3.Sig(p01, rs, rb, fr), s, t)})) == True{} : Bool}:
  +g = RD.Nat.pow2(es)
  +bias = P.Pz.bias(g, rs)
  +fb = P3.Fb(p01, rs, rb)
  +Pf = RD.Nat.pow2(fb)
  +Pp = RD.Nat.pow2(p01)
  +a = P3.Sig(p01, rs, rb, fr)
  +T = Nat.add(Nat.mul(rb, g), ee)
  +n = P3.Xn(a, s, t)
  +x = D.Dy.of(D, I.IPos{n})
  +d = D.Dy.den(x)
  +m = RD.Int.mag(D.Dy.num(x))
  +j = RD.Nat.monus(D, d)
  +c = RD.Nat.monus(bias, 1n+p01)
  +efb : {fb == p01 : Nat} = Last.fb(p01, rs, rb, hrs, elast)
  # a = 2^p0 - 1
  +A1 = RD.Nat.monus(RD.Nat.pow2(1n+p01), 1n)
  +e1a : {1n+a == 1n+A1 : Nat} = Equal.trans(Nat, 1n+a, Nat.add(Pf, 1n+fr), 1n+A1, Equal.sym(Nat, Nat.add(Pf, 1n+fr), 1n+a, NL.Nat.add_succ_r(Pf, fr)),
    Equal.trans(Nat, Nat.add(Pf, 1n+fr), Nat.add(Pp, Pp), 1n+A1,
      Equal.trans(Nat, Nat.add(Pf, 1n+fr), Nat.add(Pf, Pf), Nat.add(Pp, Pp), Equal.cong(Nat, Nat, z => Nat.add(Pf, z), 1n+fr, Pf, Equal.sym(Nat, Pf, 1n+fr, epf)), Equal.cong(Nat, Nat, z => Nat.add(RD.Nat.pow2(z), RD.Nat.pow2(z)), fb, p01, efb)),
      Equal.trans(Nat, Nat.add(Pp, Pp), RD.Nat.pow2(1n+p01), 1n+A1, Equal.sym(Nat, Nat.double(Pp), Nat.add(Pp, Pp), Y.Nat.double_add(Pp)), P2.Pw.pos(1n+p01))))
  +ea : {A1 == a : Nat} = Equal.sym(Nat, a, A1, Equal.cong(Nat, Nat, z => BP.Pd(z), 1n+a, 1n+A1, e1a))
  # the scale: c + D = s
  +ebias : {bias == Nat.add(1n+p01, c) : Nat} = E.Le.wit(1n+p01, bias, hbp)
  +rg = Nat.mul(rb, g)
  +eT1 : {1n+T == Nat.add(bias, bias) : Nat} = Equal.trans(Nat, 1n+T, Nat.add(rg, g), Nat.add(bias, bias),
    Equal.trans(Nat, 1n+T, Nat.add(rg, 1n+ee), Nat.add(rg, g), Equal.sym(Nat, Nat.add(rg, 1n+ee), 1n+T, NL.Nat.add_succ_r(rg, ee)), Equal.cong(Nat, Nat, z => Nat.add(rg, z), 1n+ee, g, Equal.sym(Nat, g, 1n+ee, eg))),
    Equal.trans(Nat, Nat.add(rg, g), Nat.mul(1n+rb, g), Nat.add(bias, bias), NL.Nat.add_comm(rg, g),
      Equal.trans(Nat, Nat.mul(1n+rb, g), Nat.mul(Nat.add(rs, rs), g), Nat.add(bias, bias), Equal.cong(Nat, Nat, z => Nat.mul(z, g), 1n+rb, Nat.add(rs, rs), Equal.trans(Nat, 1n+rb, Nat.double(rs), Nat.add(rs, rs), elast, Y.Nat.double_add(rs))), NL.Nat.mul_dist_r(rs, rs, g))))
  +hD2 : {Nat.add(T, D) == Nat.add(s, Nat.add(bias, p01)) : Nat} = Equal.trans(Nat, Nat.add(T, D), Nat.add(s, Nat.add(bias, fb)), Nat.add(s, Nat.add(bias, p01)), hD, Equal.cong(Nat, Nat, z => Nat.add(s, Nat.add(bias, z)), fb, p01, efb))
  +env : List<&2, Nat> = [bias, c, D, s, T, p01, 1n]
  +ecd : {Nat.add(c, D) == s : Nat} = Canl(1n+bias, Nat.add(c, D), s, R.NatN.eq2(env, R.Ad(R.Ad(R.V(6n), R.V(0n)), R.Ad(R.V(1n), R.V(2n))), R.Ad(R.Ad(R.V(6n), R.V(0n)), R.V(3n)), [], [], [R.Ad(R.Ad(R.V(4n), R.V(2n)), R.Ng(R.Ad(R.V(3n), R.Ad(R.V(0n), R.V(5n))))), R.Ad(R.Ad(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.V(6n), R.V(4n)))), R.Ad(R.Ad(R.Ad(R.V(6n), R.V(5n)), R.V(1n)), R.Ng(R.V(0n)))], {==}, Unit{}, (R.NatN.z(env, R.Ad(R.V(4n), R.V(2n)), R.Ad(R.V(3n), R.Ad(R.V(0n), R.V(5n))), {==}, {==}, hD2), (R.NatN.z(env, R.Ad(R.V(0n), R.V(0n)), R.Ad(R.V(6n), R.V(4n)), {==}, {==}, Equal.sym(Nat, 1n+T, Nat.add(bias, bias), eT1)), (R.NatN.z(env, R.Ad(R.Ad(R.V(6n), R.V(5n)), R.V(1n)), R.V(0n), {==}, {==}, Equal.sym(Nat, bias, Nat.add(1n+p01, c), ebias)), Unit{}))), {==}, {==}))
  # maxm(d) 2^j = a 2^s < a 2^s + t = |num x| 2^j
  +eD : {D == Nat.add(d, j) : Nat} = P3.Rep.den(D, n)
  +en : {n == Nat.mul(m, RD.Nat.pow2(j)) : Nat} = P3.Rep.num(D, n)
  +MM = P.Pz.maxm(1n+p01, bias, d)
  +eM : {Nat.mul(MM, RD.Nat.pow2(j)) == Nat.mul(a, RD.Nat.pow2(s)) : Nat} = Equal.trans(Nat, Nat.mul(MM, RD.Nat.pow2(j)), Nat.mul(Nat.mul(a, RD.Nat.pow2(Nat.add(c, d))), RD.Nat.pow2(j)), Nat.mul(a, RD.Nat.pow2(s)),
    Equal.cong(Nat, Nat, z => Nat.mul(Nat.mul(z, RD.Nat.pow2(Nat.add(c, d))), RD.Nat.pow2(j)), A1, a, ea),
    Equal.trans(Nat, Nat.mul(Nat.mul(a, RD.Nat.pow2(Nat.add(c, d))), RD.Nat.pow2(j)), Nat.mul(a, RD.Nat.pow2(Nat.add(Nat.add(c, d), j))), Nat.mul(a, RD.Nat.pow2(s)),
      Equal.sym(Nat, Nat.mul(a, RD.Nat.pow2(Nat.add(Nat.add(c, d), j))), Nat.mul(Nat.mul(a, RD.Nat.pow2(Nat.add(c, d))), RD.Nat.pow2(j)), E.Sh.mul(a, j, Nat.add(c, d), Nat.add(Nat.add(c, d), j), NL.Nat.add_comm(Nat.add(c, d), j))),
      Equal.cong(Nat, Nat, z => Nat.mul(a, RD.Nat.pow2(z)), Nat.add(Nat.add(c, d), j), s,
        Equal.trans(Nat, Nat.add(Nat.add(c, d), j), Nat.add(c, D), s, Equal.trans(Nat, Nat.add(Nat.add(c, d), j), Nat.add(c, Nat.add(d, j)), Nat.add(c, D), NL.Nat.add_assoc(c, d, j), Equal.cong(Nat, Nat, z => Nat.add(c, z), Nat.add(d, j), D, Equal.sym(Nat, D, Nat.add(d, j), eD))), ecd))))
  +hg : {RD.Nat.lt(Nat.double(t), RD.Nat.pow2(s)) == False{} : Bool} = Y.Bool.not_t(RD.Nat.lt(Nat.double(t), RD.Nat.pow2(s)))(NP.Bool.and_l(Bool.not(RD.Nat.lt(Nat.double(t), RD.Nat.pow2(s))), Bool.or(RD.Nat.lt(RD.Nat.pow2(s), Nat.double(t)), Bool.not(D.Nat.even(a))), hup))
  +t1 = RD.Nat.monus(t, 1n)
  +et : {t == 1n+t1 : Nat} = BP.Lt.wit(0n, t)(T.pos(t, s, hg))
  +X = Nat.mul(a, RD.Nat.pow2(s))
  +hlt : {RD.Nat.lt(Nat.mul(MM, RD.Nat.pow2(j)), Nat.mul(m, RD.Nat.pow2(j))) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Nat.mul(MM, RD.Nat.pow2(j)), Nat.mul(m, RD.Nat.pow2(j))), RD.Nat.lt(X, Nat.add(X, 1n+t1)), True{},
    Equal.trans(Bool, RD.Nat.lt(Nat.mul(MM, RD.Nat.pow2(j)), Nat.mul(m, RD.Nat.pow2(j))), RD.Nat.lt(X, Nat.mul(m, RD.Nat.pow2(j))), RD.Nat.lt(X, Nat.add(X, 1n+t1)),
      Equal.cong(Nat, Bool, z => RD.Nat.lt(z, Nat.mul(m, RD.Nat.pow2(j))), Nat.mul(MM, RD.Nat.pow2(j)), X, eM),
      Equal.cong(Nat, Bool, z => RD.Nat.lt(X, z), Nat.mul(m, RD.Nat.pow2(j)), Nat.add(X, 1n+t1), Equal.trans(Nat, Nat.mul(m, RD.Nat.pow2(j)), n, Nat.add(X, 1n+t1), Equal.sym(Nat, n, Nat.mul(m, RD.Nat.pow2(j)), en), Equal.cong(Nat, Nat, z => Nat.add(X, z), t, 1n+t1, et)))),
    BP.Lt.self(X, t1))
  E.Lt.cancel(MM, m, RD.Nat.pow2(j), hlt)

def Nxt.go(+p02: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +D: Nat, +s: Nat, +t: Nat, +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(1n+p02, rs, rb))) == True{} : Bool},
  +hbp: {RD.Nat.lt(P.Pz.bias(RD.Nat.pow2(es), rs), 1n+1n+p02) == False{} : Bool},
  +hD: {Nat.add(Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee), D) == Nat.add(s, Nat.add(P.Pz.bias(RD.Nat.pow2(es), rs), P3.Fb(1n+p02, rs, rb))) : Nat},
  +hov: {P.Pz.over(1n+1n+p02, P.Pz.bias(RD.Nat.pow2(es), rs), D.Dy.of(D, I.IPos{P3.Xn(P3.Sig(1n+p02, rs, rb, fr), s, t)})) == False{} : Bool},
  +hup: {P3.Rup(P3.Sig(1n+p02, rs, rb, fr), t, s) == True{} : Bool}, +hf1: {RD.Nat.lt(1n+fr, RD.Nat.pow2(P3.Fb(1n+p02, rs, rb))) == False{} : Bool}, +he1: {RD.Nat.lt(1n+ee, RD.Nat.pow2(es)) == False{} : Bool},
  c: Bool, +ec: {RD.Nat.lt(1n+rb, Nat.double(rs)) == c : Bool})
  -> {RD.Nat.lt(1n+rb, Nat.double(rs)) == True{} : Bool}:
  match c:
    case True{}:
      ec
    case False{}:
      +elast : {1n+rb == Nat.double(rs) : Nat} = E2.Le.anti(1n+rb, Nat.double(rs), E2.Le.succ(rb, Nat.double(rs), hrb), ec)
      +epf : {RD.Nat.pow2(P3.Fb(1n+p02, rs, rb)) == 1n+fr : Nat} = Equal.sym(Nat, 1n+fr, RD.Nat.pow2(P3.Fb(1n+p02, rs, rb)), E2.Le.anti(1n+fr, RD.Nat.pow2(P3.Fb(1n+p02, rs, rb)), E2.Le.succ(fr, RD.Nat.pow2(P3.Fb(1n+p02, rs, rb)), hfr), hf1))
      +eg : {RD.Nat.pow2(es) == 1n+ee : Nat} = Equal.sym(Nat, 1n+ee, RD.Nat.pow2(es), E2.Le.anti(1n+ee, RD.Nat.pow2(es), E2.Le.succ(ee, RD.Nat.pow2(es), hee), he1))
      +ov = P.Pz.over(1n+1n+p02, P.Pz.bias(RD.Nat.pow2(es), rs), D.Dy.of(D, I.IPos{P3.Xn(P3.Sig(1n+p02, rs, rb, fr), s, t)}))
      B.Bool.tf({RD.Nat.lt(1n+rb, Nat.double(rs)) == True{} : Bool}, Equal.trans(Bool, True{}, ov, False{}, Equal.sym(Bool, ov, True{}, Last.over(1n+p02, es, rs, rb, ee, fr, D, s, t, hrs, elast, eg, epf, hbp, hD, hup)), hov))

# T3, in full. For a b-posit format with p0 >= 2 and bias >= p0 (maxpos >=
# 1), every x in [minpos, maxpos], spelled x = (a 2^s + t) / 2^D with a the
# significand of the pattern q = Pat(rb, ee, fr) just below x and t < 2^s,
# rounds under Pz.fl to the value of the standard's rounded pattern: q + 1
# when guard and (sticky or q odd), else q.
def Std.rnd(+h1: Nat, +p02: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +D: Nat, +s: Nat, +t: Nat,
  +hrs: {RD.Nat.lt(0n, rs) == True{} : Bool}, +hbp: {RD.Nat.lt(P.Pz.bias(RD.Nat.pow2(es), rs), 1n+1n+p02) == False{} : Bool},
  +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}, +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(1n+p02, rs, rb))) == True{} : Bool},
  +ht: {RD.Nat.lt(t, RD.Nat.pow2(s)) == True{} : Bool},
  +hD: {Nat.add(Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee), D) == Nat.add(s, Nat.add(P.Pz.bias(RD.Nat.pow2(es), rs), P3.Fb(1n+p02, rs, rb))) : Nat},
  +hti: {P.Pz.tiny(1n+1n+p02, P.Pz.bias(RD.Nat.pow2(es), rs), D.Dy.of(D, I.IPos{P3.Xn(P3.Sig(1n+p02, rs, rb, fr), s, t)})) == False{} : Bool},
  +hov: {P.Pz.over(1n+1n+p02, P.Pz.bias(RD.Nat.pow2(es), rs), D.Dy.of(D, I.IPos{P3.Xn(P3.Sig(1n+p02, rs, rb, fr), s, t)})) == False{} : Bool})
  -> {P.Pz.fl(1n+1n+p02, RD.Nat.pow2(es), rs, D.Dy.of(D, I.IPos{P3.Xn(P3.Sig(1n+p02, rs, rb, fr), s, t)})) == DecV(h1, 1n+p02, es, rs, BitRnd(Pat(1n+p02, es, rs, rb, ee, fr), Gd(t, s), St(t, s))) : D.Dy}:
  Std.round(h1, p02, es, rs, rb, ee, fr, D, s, t, hrs, hrb, hee, hfr, ht, hD, hti, hov,
    hup => hf1 => he1 => Nxt.go(p02, es, rs, rb, ee, fr, D, s, t, hrs, hrb, hee, hfr, hbp, hD, hov, hup, hf1, he1, RD.Nat.lt(1n+rb, Nat.double(rs)), {==}))
