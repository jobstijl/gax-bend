# b-posit rounding is the posit standard's bit-string rounding
# (src/posit.bend; ADR-008). Within a scale class a value x lies between
# two consecutive patterns q and q + 1, worth a u and (a + 1) u, where
# a = 2^fb + fr is q's significand and u its unit in the last place. The
# standard rounds the bit string: the bits of x past q are a guard bit and
# a sticky bit, and q rounds up when guard and (sticky or q odd). Pz.fl
# rounds the value to nearest at fb + 1 bits, ties to even. They agree.

import Base
import ../src/round.bend as RD
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/norm.bend as N
import ./int.bend as Z
import ./posit.bend as PP
import ./nat.bend as NL
import ./base.bend as B
import ./norm.bend as NP
import ./dyadic.bend as Y
import ./round.bend as R
import ./big.bend as BP
import ./eft.bend as E
import ./eft2.bend as E2
import ./posit2.bend as P2
import ../src/posit.bend as P
import ../src/big.bend as SB

# Integer rounding at a known shift
# ---------------------------------

# the bit-string rule on n = a 2^s + t, t < 2^s: guard = 2t >= 2^s,
# sticky = 2t > 2^s; round up when guard and (sticky or a odd)
def Rup(+a: Nat, +t: Nat, +s: Nat) -> Bool:
  Bool.and(Bool.not(RD.Nat.lt(Nat.double(t), RD.Nat.pow2(s))), Bool.or(RD.Nat.lt(RD.Nat.pow2(s), Nat.double(t)), Bool.not(D.Nat.even(a))))

def RnF(+a: Nat, +s: Nat, +t: Nat) -> Nat:
  Bool.pick(Nat, Rup(a, t, s), Nat.mul(1n+a, RD.Nat.pow2(s)), Nat.mul(a, RD.Nat.pow2(s)))

# (q d + b) / d = q and (q d + b) mod d = b, for b < d = 2^s
def Dv.q(+q: Nat, +b: Nat, +s: Nat, +hb: {RD.Nat.lt(b, RD.Nat.pow2(s)) == True{} : Bool})
  -> {Nat.div(Nat.add(Nat.mul(q, RD.Nat.pow2(s)), b), RD.Nat.pow2(s)) == q : Nat}:
  +pm = RD.Nat.monus(RD.Nat.pow2(s), 1n)
  +ep : {RD.Nat.pow2(s) == 1n+pm : Nat} = P2.Pw.pos(s)
  +hf : {RD.Nat.lt(pm, b) == False{} : Bool} = E2.Le.of_lt1(b, pm, Equal.trans(Bool, RD.Nat.lt(b, 1n+pm), RD.Nat.lt(b, RD.Nat.pow2(s)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(b, z), 1n+pm, RD.Nat.pow2(s), Equal.sym(Nat, RD.Nat.pow2(s), 1n+pm, ep)), hb))
  Equal.trans(Nat, Nat.div(Nat.add(Nat.mul(q, RD.Nat.pow2(s)), b), RD.Nat.pow2(s)), Nat.div(Nat.add(Nat.mul(q, 1n+pm), b), 1n+pm), q,
    Equal.cong(Nat, Nat, z => Nat.div(Nat.add(Nat.mul(q, z), b), z), RD.Nat.pow2(s), 1n+pm, ep), P2.Div.q(q, b, pm, hf))

def Dv.r(+q: Nat, +b: Nat, +s: Nat, +hb: {RD.Nat.lt(b, RD.Nat.pow2(s)) == True{} : Bool})
  -> {Nat.mod(Nat.add(Nat.mul(q, RD.Nat.pow2(s)), b), RD.Nat.pow2(s)) == b : Nat}:
  +pm = RD.Nat.monus(RD.Nat.pow2(s), 1n)
  +ep : {RD.Nat.pow2(s) == 1n+pm : Nat} = P2.Pw.pos(s)
  +hf : {RD.Nat.lt(pm, b) == False{} : Bool} = E2.Le.of_lt1(b, pm, Equal.trans(Bool, RD.Nat.lt(b, 1n+pm), RD.Nat.lt(b, RD.Nat.pow2(s)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(b, z), 1n+pm, RD.Nat.pow2(s), Equal.sym(Nat, RD.Nat.pow2(s), 1n+pm, ep)), hb))
  Equal.trans(Nat, Nat.mod(Nat.add(Nat.mul(q, RD.Nat.pow2(s)), b), RD.Nat.pow2(s)), Nat.mod(Nat.add(Nat.mul(q, 1n+pm), b), 1n+pm), b,
    Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(Nat.mul(q, z), b), z), RD.Nat.pow2(s), 1n+pm, ep), P2.Div.r(q, b, pm, hf))

# a 2^s + t < (a + 1) 2^s
def Lt.next(+a: Nat, +s: Nat, +t: Nat, +ht: {RD.Nat.lt(t, RD.Nat.pow2(s)) == True{} : Bool})
  -> {RD.Nat.lt(Nat.add(Nat.mul(a, RD.Nat.pow2(s)), t), Nat.mul(1n+a, RD.Nat.pow2(s))) == True{} : Bool}:
  +X = Nat.mul(a, RD.Nat.pow2(s))
  Equal.trans(Bool, RD.Nat.lt(Nat.add(X, t), Nat.mul(1n+a, RD.Nat.pow2(s))), RD.Nat.lt(Nat.add(X, t), Nat.add(X, RD.Nat.pow2(s))), True{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.add(X, t), z), Nat.mul(1n+a, RD.Nat.pow2(s)), Nat.add(X, RD.Nat.pow2(s)), NL.Nat.add_comm(RD.Nat.pow2(s), X)),
    Equal.trans(Bool, RD.Nat.lt(Nat.add(X, t), Nat.add(X, RD.Nat.pow2(s))), RD.Nat.lt(t, RD.Nat.pow2(s)), True{}, BP.Lt.shift(X, t, RD.Nat.pow2(s)), ht))

# rounding a 2^s + t (t < 2^s, 2^(p-1) <= a < 2^p) at p bits: the loop
# stops at shift s with quotient a and remainder t
def Rn.at(+p1: Nat, +a: Nat, +s: Nat, +t: Nat,
  +hlo: {RD.Nat.lt(a, RD.Nat.pow2(p1)) == False{} : Bool},
  +hhi: {RD.Nat.lt(a, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +ht: {RD.Nat.lt(t, RD.Nat.pow2(s)) == True{} : Bool})
  -> {E.Rn(1n+p1, Nat.add(Nat.mul(a, RD.Nat.pow2(s)), t)) == RnF(a, s, t) : Nat}:
  +p : Nat = 1n+p1
  +n = Nat.add(Nat.mul(a, RD.Nat.pow2(s)), t)
  +T = RD.Tr.of(p, n)
  +S = RD.Tr.s(T)
  +q = RD.Tr.q(T)
  +r = R.Tr.r(T)
  # the shift is s
  +h1 : {RD.Nat.lt(n, Nat.mul(RD.Nat.pow2(p), RD.Nat.pow2(s))) == True{} : Bool} = E2.Lt.le_trans(n, Nat.mul(1n+a, RD.Nat.pow2(s)), Nat.mul(RD.Nat.pow2(p), RD.Nat.pow2(s)), Lt.next(a, s, t, ht),
    E2.Le.mulr(1n+a, RD.Nat.pow2(p), RD.Nat.pow2(s), E2.Le.succ(a, RD.Nat.pow2(p), hhi)))
  +h2 : {RD.Nat.lt(n, Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(s))) == False{} : Bool} = E.Le.trans(Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(s)), Nat.mul(a, RD.Nat.pow2(s)), n,
    E2.Le.mulr(RD.Nat.pow2(p1), a, RD.Nat.pow2(s), hlo), E.Le.add(Nat.mul(a, RD.Nat.pow2(s)), t))
  +eS : {S == s : Nat} = E2.Le.anti(S, s, E2.S3(p1, n, s, h1), E2.S4(p1, n, s, h2))
  +en : {n == Nat.add(Nat.mul(q, RD.Nat.pow2(S)), r) : Nat} = Pair.fst({n == Nat.add(Nat.mul(q, RD.Nat.pow2(S)), r) : Nat}, {RD.Nat.pow2(S) == Nat.add(Nat.add(r, 1n), E.Tr.wr(T)) : Nat}, E.Sh.n(p1, n))
  +ew : {RD.Nat.pow2(S) == Nat.add(Nat.add(r, 1n), E.Tr.wr(T)) : Nat} = Pair.snd({n == Nat.add(Nat.mul(q, RD.Nat.pow2(S)), r) : Nat}, {RD.Nat.pow2(S) == Nat.add(Nat.add(r, 1n), E.Tr.wr(T)) : Nat}, E.Sh.n(p1, n))
  +ePS : {RD.Nat.pow2(S) == RD.Nat.pow2(s) : Nat} = Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), S, s, eS)
  +hr : {RD.Nat.lt(r, RD.Nat.pow2(s)) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(r, RD.Nat.pow2(s)), RD.Nat.lt(r, Nat.add(r, 1n+E.Tr.wr(T))), True{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(r, z), RD.Nat.pow2(s), Nat.add(r, 1n+E.Tr.wr(T)),
      Equal.trans(Nat, RD.Nat.pow2(s), RD.Nat.pow2(S), Nat.add(r, 1n+E.Tr.wr(T)), Equal.sym(Nat, RD.Nat.pow2(S), RD.Nat.pow2(s), ePS),
        Equal.trans(Nat, RD.Nat.pow2(S), Nat.add(Nat.add(r, 1n), E.Tr.wr(T)), Nat.add(r, 1n+E.Tr.wr(T)), ew, NL.Nat.add_assoc(r, 1n, E.Tr.wr(T))))),
    BP.Lt.self(r, E.Tr.wr(T)))
  +en2 : {n == Nat.add(Nat.mul(q, RD.Nat.pow2(s)), r) : Nat} = Equal.trans(Nat, n, Nat.add(Nat.mul(q, RD.Nat.pow2(S)), r), Nat.add(Nat.mul(q, RD.Nat.pow2(s)), r), en,
    Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(q, z), r), RD.Nat.pow2(S), RD.Nat.pow2(s), ePS))
  # quotient and remainder are a and t
  +eq : {q == a : Nat} = Equal.trans(Nat, q, Nat.div(n, RD.Nat.pow2(s)), a,
    Equal.sym(Nat, Nat.div(n, RD.Nat.pow2(s)), q, Equal.trans(Nat, Nat.div(n, RD.Nat.pow2(s)), Nat.div(Nat.add(Nat.mul(q, RD.Nat.pow2(s)), r), RD.Nat.pow2(s)), q,
      Equal.cong(Nat, Nat, z => Nat.div(z, RD.Nat.pow2(s)), n, Nat.add(Nat.mul(q, RD.Nat.pow2(s)), r), en2), Dv.q(q, r, s, hr))),
    Dv.q(a, t, s, ht))
  +er : {r == t : Nat} = Equal.trans(Nat, r, Nat.mod(n, RD.Nat.pow2(s)), t,
    Equal.sym(Nat, Nat.mod(n, RD.Nat.pow2(s)), r, Equal.trans(Nat, Nat.mod(n, RD.Nat.pow2(s)), Nat.mod(Nat.add(Nat.mul(q, RD.Nat.pow2(s)), r), RD.Nat.pow2(s)), r,
      Equal.cong(Nat, Nat, z => Nat.mod(z, RD.Nat.pow2(s)), n, Nat.add(Nat.mul(q, RD.Nat.pow2(s)), r), en2), Dv.r(q, r, s, hr))),
    Dv.r(a, t, s, ht))
  +e0 : {E.Rn(p, n) == RnF(q, S, r) : Nat} = Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, Nat.mul(1n+q, RD.Nat.pow2(S)), Nat.mul(q, RD.Nat.pow2(S))), RD.Tr.rup(T), Rup(q, r, S), BP.Rup.acc(T))
  Equal.trans(Nat, E.Rn(p, n), RnF(q, S, r), RnF(a, s, t), e0,
    Equal.trans(Nat, RnF(q, S, r), RnF(a, S, r), RnF(a, s, t), Equal.cong(Nat, Nat, z => RnF(z, S, r), q, a, eq),
      Equal.trans(Nat, RnF(a, S, r), RnF(a, s, r), RnF(a, s, t), Equal.cong(Nat, Nat, z => RnF(a, z, r), S, s, eS), Equal.cong(Nat, Nat, z => RnF(a, s, z), r, t, er))))

# Any spelling of a value
# -----------------------
# The spec reads x through its normal form (num, den). For x = n / 2^D
# spelled any way, den <= D and n = |num| 2^(D - den).

def Mul.one_l(+a: Nat) -> {Nat.mul(1n, a) == a : Nat}:
  Equal.trans(Nat, Nat.mul(1n, a), Nat.mul(a, 1n), a, NL.Nat.mul_comm(1n, a), NL.Nat.mul_one_r(a))

def Rep.den(+D: Nat, +n: Nat) -> {D == Nat.add(D.Dy.den(D.Dy.of(D, I.IPos{n})), RD.Nat.monus(D, D.Dy.den(D.Dy.of(D, I.IPos{n})))) : Nat}:
  E.Le.wit(D.Dy.den(D.Dy.of(D, I.IPos{n})), D, E.Of.den.go(D, I.IPos{n}, D.Int.even(I.IPos{n}), {==}))

def Rep.num(+D: Nat, +n: Nat) -> {n == Nat.mul(RD.Int.mag(D.Dy.num(D.Dy.of(D, I.IPos{n}))), RD.Nat.pow2(RD.Nat.monus(D, D.Dy.den(D.Dy.of(D, I.IPos{n}))))) : Nat}:
  +x = D.Dy.of(D, I.IPos{n})
  +M = D.Dy.num(x)
  +j = RD.Nat.monus(D, D.Dy.den(x))
  +e1 : {I.IPos{n} == D.Int.sh(j, M) : I.Int} = E.Num.sh(D, I.IPos{n})
  +e2 : {n == RD.Int.mag(D.Int.sh(j, M)) : Nat} = Equal.cong(I.Int, Nat, z => RD.Int.mag(z), I.IPos{n}, D.Int.sh(j, M), e1)
  +e3 : {RD.Int.mag(D.Int.sh(j, M)) == Nat.mul(RD.Int.mag(M), RD.Int.mag(Y.P(j))) : Nat} = Equal.trans(Nat, RD.Int.mag(D.Int.sh(j, M)), RD.Int.mag(I.Int.mul(M, Y.P(j))), Nat.mul(RD.Int.mag(M), RD.Int.mag(Y.P(j))),
    Equal.cong(I.Int, Nat, z => RD.Int.mag(z), D.Int.sh(j, M), I.Int.mul(M, Y.P(j)), Y.Sh.p(j, M)), E2.Mag.mul(M, Y.P(j)))
  +e4 : {RD.Int.mag(Y.P(j)) == RD.Nat.pow2(j) : Nat} = Equal.trans(Nat, RD.Int.mag(Y.P(j)), Nat.mul(1n, RD.Nat.pow2(j)), RD.Nat.pow2(j),
    Equal.cong(I.Int, Nat, z => RD.Int.mag(z), Y.P(j), I.IPos{Nat.mul(1n, RD.Nat.pow2(j))}, R.Sh.ipos(j, 1n)), Mul.one_l(RD.Nat.pow2(j)))
  Equal.trans(Nat, n, RD.Int.mag(D.Int.sh(j, M)), Nat.mul(RD.Int.mag(M), RD.Nat.pow2(j)), e2,
    Equal.trans(Nat, RD.Int.mag(D.Int.sh(j, M)), Nat.mul(RD.Int.mag(M), RD.Int.mag(Y.P(j))), Nat.mul(RD.Int.mag(M), RD.Nat.pow2(j)), e3,
      Equal.cong(Nat, Nat, z => Nat.mul(RD.Int.mag(M), z), RD.Int.mag(Y.P(j)), RD.Nat.pow2(j), e4)))

# a x < b x is a < b, for x > 0
def Lt.scale.go(+a: Nat, +b: Nat, +x: Nat, +hx: {RD.Nat.lt(0n, x) == True{} : Bool}, l: Bool, +el: {RD.Nat.lt(a, b) == l : Bool})
  -> {RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)) == RD.Nat.lt(a, b) : Bool}:
  match l:
    case True{}:
      Equal.trans(Bool, RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)), True{}, RD.Nat.lt(a, b), E.Lt.mono(a, b, x, el, hx), Equal.sym(Bool, RD.Nat.lt(a, b), True{}, el))
    case False{}:
      Equal.trans(Bool, RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)), False{}, RD.Nat.lt(a, b), E2.Le.mulr(b, a, x, el), Equal.sym(Bool, RD.Nat.lt(a, b), False{}, el))

def Lt.scale(+a: Nat, +b: Nat, +x: Nat, +hx: {RD.Nat.lt(0n, x) == True{} : Bool}) -> {RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)) == RD.Nat.lt(a, b) : Bool}:
  Lt.scale.go(a, b, x, hx, RD.Nat.lt(a, b), {==})

# m x > 0 gives m > 0
def Pos.fac(+m: Nat, +x: Nat, +h: {RD.Nat.lt(0n, Nat.mul(m, x)) == True{} : Bool}) -> {RD.Nat.lt(0n, m) == True{} : Bool}:
  match m:
    case 0n:
      h
    case 1n+m2:
      {==}

def Below.t(+bias: Nat, +i: Nat, +D: Nat, +n: Nat, +hn: {RD.Nat.lt(0n, n) == True{} : Bool}, +el: {RD.Nat.lt(Nat.add(i, D.Dy.den(D.Dy.of(D, I.IPos{n}))), bias) == True{} : Bool})
  -> {P.Pz.below(bias, i, D.Dy.of(D, I.IPos{n})) == RD.Nat.lt(Nat.mul(n, RD.Nat.pow2(bias)), RD.Nat.pow2(Nat.add(i, D))) : Bool}:
  +x = D.Dy.of(D, I.IPos{n})
  +d = D.Dy.den(x)
  +m = RD.Int.mag(D.Dy.num(x))
  +j = RD.Nat.monus(D, d)
  +Pb = RD.Nat.pow2(bias)
  +Pj = RD.Nat.pow2(j)
  +PiD = RD.Nat.pow2(Nat.add(i, D))
  +X = Nat.mul(Pj, Pb)
  +eD : {D == Nat.add(d, j) : Nat} = Rep.den(D, n)
  +en : {n == Nat.mul(m, Pj) : Nat} = Rep.num(D, n)
  +eiD0 : {Nat.add(i, D) == Nat.add(Nat.add(i, d), j) : Nat} = Equal.trans(Nat, Nat.add(i, D), Nat.add(i, Nat.add(d, j)), Nat.add(Nat.add(i, d), j), Equal.cong(Nat, Nat, z => Nat.add(i, z), D, Nat.add(d, j), eD), Equal.sym(Nat, Nat.add(Nat.add(i, d), j), Nat.add(i, Nat.add(d, j)), NL.Nat.add_assoc(i, d, j)))
  +hX : {RD.Nat.lt(0n, X) == True{} : Bool} = E.Lt.mono(0n, Pj, Pb, BP.Pow2.pos(j), BP.Pow2.pos(bias))
  +hm : {RD.Nat.lt(0n, m) == True{} : Bool} = Pos.fac(m, Pj, Equal.trans(Bool, RD.Nat.lt(0n, Nat.mul(m, Pj)), RD.Nat.lt(0n, n), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(0n, z), Nat.mul(m, Pj), n, Equal.sym(Nat, n, Nat.mul(m, Pj), en)), hn))
  +env1 : List<&2, Nat> = [m, n, Pb, 0n, Pj, PiD, 0n, 1n]
  +e1 : {Nat.mul(n, Pb) == Nat.mul(m, X) : Nat} = R.NatN.eq(env1, R.Ml(R.V(1n), R.V(2n)), R.Ml(R.V(0n), R.Ml(R.V(4n), R.V(2n))), [R.V(2n)], [R.Ad(R.V(1n), R.Ng(R.Ml(R.V(0n), R.V(4n))))], {==}, (R.NatN.z(env1, R.V(1n), R.Ml(R.V(0n), R.V(4n)), {==}, {==}, en), Unit{}), {==}, {==})
  +sel = Equal.cong(Bool, Bool, z => Bool.pick(Bool, z, False{}, RD.Nat.lt(m, RD.Nat.pow2(RD.Nat.monus(Nat.add(i, d), bias)))), RD.Nat.lt(Nat.add(i, d), bias), True{}, el)
  +h1 : {RD.Nat.lt(Nat.add(bias, j), Nat.add(Nat.add(i, d), j)) == False{} : Bool} = E2.Le.addr(Nat.add(i, d), bias, j, E2.Lt.to_le(Nat.add(i, d), bias, el))
  +h2 : {RD.Nat.lt(RD.Nat.pow2(Nat.add(bias, j)), PiD) == False{} : Bool} = E2.Pow2.mono(Nat.add(i, D), Nat.add(bias, j), E.Le.trans(Nat.add(i, D), Nat.add(Nat.add(i, d), j), Nat.add(bias, j), E.Le.eq(Nat.add(i, D), Nat.add(Nat.add(i, d), j), eiD0), h1))
  +h3 : {RD.Nat.pow2(Nat.add(bias, j)) == Nat.mul(1n, X) : Nat} = Equal.trans(Nat, RD.Nat.pow2(Nat.add(bias, j)), Nat.mul(Pb, Pj), Nat.mul(1n, X), BP.Pow2.add(bias, j),
    Equal.trans(Nat, Nat.mul(Pb, Pj), X, Nat.mul(1n, X), NL.Nat.mul_comm(Pb, Pj), Equal.sym(Nat, Nat.mul(1n, X), X, Mul.one_l(X))))
  +h4 : {RD.Nat.lt(Nat.mul(m, X), Nat.mul(1n, X)) == False{} : Bool} = E2.Le.mulr(1n, m, X, E2.Le.succ(0n, m, hm))
  +hf : {RD.Nat.lt(Nat.mul(n, Pb), PiD) == False{} : Bool} = E.Le.trans(PiD, RD.Nat.pow2(Nat.add(bias, j)), Nat.mul(n, Pb), h2,
    E.Le.trans(RD.Nat.pow2(Nat.add(bias, j)), Nat.mul(1n, X), Nat.mul(n, Pb), E.Le.eq(RD.Nat.pow2(Nat.add(bias, j)), Nat.mul(1n, X), h3),
      E.Le.trans(Nat.mul(1n, X), Nat.mul(m, X), Nat.mul(n, Pb), h4, E.Le.eq(Nat.mul(m, X), Nat.mul(n, Pb), Equal.sym(Nat, Nat.mul(n, Pb), Nat.mul(m, X), e1)))))
  Equal.trans(Bool, P.Pz.below(bias, i, x), False{}, RD.Nat.lt(Nat.mul(n, Pb), PiD), sel, Equal.sym(Bool, RD.Nat.lt(Nat.mul(n, Pb), PiD), False{}, hf))

def Below.f(+bias: Nat, +i: Nat, +D: Nat, +n: Nat, +hn: {RD.Nat.lt(0n, n) == True{} : Bool}, +el: {RD.Nat.lt(Nat.add(i, D.Dy.den(D.Dy.of(D, I.IPos{n}))), bias) == False{} : Bool})
  -> {P.Pz.below(bias, i, D.Dy.of(D, I.IPos{n})) == RD.Nat.lt(Nat.mul(n, RD.Nat.pow2(bias)), RD.Nat.pow2(Nat.add(i, D))) : Bool}:
  +x = D.Dy.of(D, I.IPos{n})
  +d = D.Dy.den(x)
  +m = RD.Int.mag(D.Dy.num(x))
  +j = RD.Nat.monus(D, d)
  +Pb = RD.Nat.pow2(bias)
  +Pj = RD.Nat.pow2(j)
  +PiD = RD.Nat.pow2(Nat.add(i, D))
  +X = Nat.mul(Pj, Pb)
  +eD : {D == Nat.add(d, j) : Nat} = Rep.den(D, n)
  +en : {n == Nat.mul(m, Pj) : Nat} = Rep.num(D, n)
  +eiD0 : {Nat.add(i, D) == Nat.add(Nat.add(i, d), j) : Nat} = Equal.trans(Nat, Nat.add(i, D), Nat.add(i, Nat.add(d, j)), Nat.add(Nat.add(i, d), j), Equal.cong(Nat, Nat, z => Nat.add(i, z), D, Nat.add(d, j), eD), Equal.sym(Nat, Nat.add(Nat.add(i, d), j), Nat.add(i, Nat.add(d, j)), NL.Nat.add_assoc(i, d, j)))
  +hX : {RD.Nat.lt(0n, X) == True{} : Bool} = E.Lt.mono(0n, Pj, Pb, BP.Pow2.pos(j), BP.Pow2.pos(bias))
  +hm : {RD.Nat.lt(0n, m) == True{} : Bool} = Pos.fac(m, Pj, Equal.trans(Bool, RD.Nat.lt(0n, Nat.mul(m, Pj)), RD.Nat.lt(0n, n), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(0n, z), Nat.mul(m, Pj), n, Equal.sym(Nat, n, Nat.mul(m, Pj), en)), hn))
  +env1 : List<&2, Nat> = [m, n, Pb, 0n, Pj, PiD, 0n, 1n]
  +e1 : {Nat.mul(n, Pb) == Nat.mul(m, X) : Nat} = R.NatN.eq(env1, R.Ml(R.V(1n), R.V(2n)), R.Ml(R.V(0n), R.Ml(R.V(4n), R.V(2n))), [R.V(2n)], [R.Ad(R.V(1n), R.Ng(R.Ml(R.V(0n), R.V(4n))))], {==}, (R.NatN.z(env1, R.V(1n), R.Ml(R.V(0n), R.V(4n)), {==}, {==}, en), Unit{}), {==}, {==})
  +sel = Equal.cong(Bool, Bool, z => Bool.pick(Bool, z, False{}, RD.Nat.lt(m, RD.Nat.pow2(RD.Nat.monus(Nat.add(i, d), bias)))), RD.Nat.lt(Nat.add(i, d), bias), False{}, el)
  +c = RD.Nat.monus(Nat.add(i, d), bias)
  +Pc = RD.Nat.pow2(c)
  +Pbc = RD.Nat.pow2(Nat.add(bias, c))
  +ec : {Nat.add(i, d) == Nat.add(bias, c) : Nat} = E.Le.wit(bias, Nat.add(i, d), el)
  +eiD : {PiD == Nat.mul(Pbc, Pj) : Nat} = Equal.trans(Nat, PiD, RD.Nat.pow2(Nat.add(Nat.add(bias, c), j)), Nat.mul(Pbc, Pj),
    Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), Nat.add(i, D), Nat.add(Nat.add(bias, c), j), Equal.trans(Nat, Nat.add(i, D), Nat.add(Nat.add(i, d), j), Nat.add(Nat.add(bias, c), j), eiD0, Equal.cong(Nat, Nat, z => Nat.add(z, j), Nat.add(i, d), Nat.add(bias, c), ec))),
    BP.Pow2.add(Nat.add(bias, c), j))
  +ebc : {Pbc == Nat.mul(Pb, Pc) : Nat} = BP.Pow2.add(bias, c)
  +env2 : List<&2, Nat> = [m, n, Pb, Pc, Pj, PiD, Pbc, 1n]
  +e2 : {PiD == Nat.mul(Pc, X) : Nat} = R.NatN.eq2(env2, R.V(5n), R.Ml(R.V(3n), R.Ml(R.V(4n), R.V(2n))), [R.V(4n)], [R.Ad(R.V(6n), R.Ng(R.Ml(R.V(2n), R.V(3n))))], [R.Ad(R.V(5n), R.Ng(R.Ml(R.V(6n), R.V(4n))))], {==}, (R.NatN.z(env2, R.V(6n), R.Ml(R.V(2n), R.V(3n)), {==}, {==}, ebc), Unit{}), (R.NatN.z(env2, R.V(5n), R.Ml(R.V(6n), R.V(4n)), {==}, {==}, eiD), Unit{}), {==}, {==})
  +er : {RD.Nat.lt(Nat.mul(n, Pb), PiD) == RD.Nat.lt(m, Pc) : Bool} = Equal.trans(Bool, RD.Nat.lt(Nat.mul(n, Pb), PiD), RD.Nat.lt(Nat.mul(m, X), Nat.mul(Pc, X)), RD.Nat.lt(m, Pc),
    Equal.trans(Bool, RD.Nat.lt(Nat.mul(n, Pb), PiD), RD.Nat.lt(Nat.mul(m, X), PiD), RD.Nat.lt(Nat.mul(m, X), Nat.mul(Pc, X)),
      Equal.cong(Nat, Bool, z => RD.Nat.lt(z, PiD), Nat.mul(n, Pb), Nat.mul(m, X), e1), Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.mul(m, X), z), PiD, Nat.mul(Pc, X), e2)),
    Lt.scale(m, Pc, X, hX))
  Equal.trans(Bool, P.Pz.below(bias, i, x), RD.Nat.lt(m, Pc), RD.Nat.lt(Nat.mul(n, Pb), PiD), sel, Equal.sym(Bool, RD.Nat.lt(Nat.mul(n, Pb), PiD), RD.Nat.lt(m, Pc), er))

# |x| < 2^(i - bias), read off any spelling n / 2^D of x > 0
def Below.go(+bias: Nat, +i: Nat, +D: Nat, +n: Nat, +hn: {RD.Nat.lt(0n, n) == True{} : Bool}, l: Bool, +el: {RD.Nat.lt(Nat.add(i, D.Dy.den(D.Dy.of(D, I.IPos{n}))), bias) == l : Bool})
  -> {P.Pz.below(bias, i, D.Dy.of(D, I.IPos{n})) == RD.Nat.lt(Nat.mul(n, RD.Nat.pow2(bias)), RD.Nat.pow2(Nat.add(i, D))) : Bool}:
  match l:
    case True{}:
      Below.t(bias, i, D, n, hn, el)
    case False{}:
      Below.f(bias, i, D, n, hn, el)

def Below.at(+bias: Nat, +i: Nat, +D: Nat, +n: Nat, +hn: {RD.Nat.lt(0n, n) == True{} : Bool})
  -> {P.Pz.below(bias, i, D.Dy.of(D, I.IPos{n})) == RD.Nat.lt(Nat.mul(n, RD.Nat.pow2(bias)), RD.Nat.pow2(Nat.add(i, D))) : Bool}:
  Below.go(bias, i, D, n, hn, RD.Nat.lt(Nat.add(i, D.Dy.den(D.Dy.of(D, I.IPos{n}))), bias), {==})

# The scale class
# ---------------
# For 2^(rb g) <= n 2^bias / 2^D < 2^((rb + 1) g), Pz.find returns rb when
# its fuel exceeds rb. Searching from rb0 with rb = rb0 + k:

def Find.go(+g: Nat, +bias: Nat, +D: Nat, +n: Nat, +hn: {RD.Nat.lt(0n, n) == True{} : Bool}, c: Nat, k: Nat, +rb0: Nat,
  +lo: {RD.Nat.lt(Nat.mul(n, RD.Nat.pow2(bias)), RD.Nat.pow2(Nat.add(Nat.mul(Nat.add(rb0, k), g), D))) == False{} : Bool},
  +hi: {RD.Nat.lt(Nat.mul(n, RD.Nat.pow2(bias)), RD.Nat.pow2(Nat.add(Nat.mul(1n+Nat.add(rb0, k), g), D))) == True{} : Bool},
  +hkc: {RD.Nat.lt(k, c) == True{} : Bool})
  -> {P.Pz.find(g, bias, c, rb0, D.Dy.of(D, I.IPos{n})) == Nat.add(rb0, k) : Nat}:
  match c:
    case 0n:
      +x = D.Dy.of(D, I.IPos{n})
      B.Bool.tf({P.Pz.find(g, bias, 0n, rb0, x) == Nat.add(rb0, k) : Nat}, Equal.trans(Bool, True{}, RD.Nat.lt(k, 0n), False{}, Equal.sym(Bool, RD.Nat.lt(k, 0n), True{}, hkc), BP.Lt.z(k)))
    case 1n+(+c2):
      match k:
        case 0n:
          +x = D.Dy.of(D, I.IPos{n})
          +nb = Nat.mul(n, RD.Nat.pow2(bias))
          +ez : {Nat.add(rb0, 0n) == rb0 : Nat} = NL.Nat.add_zero_r(rb0)
          +hi0 : {RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(1n+rb0, g), D))) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(1n+rb0, g), D))), RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(1n+Nat.add(rb0, 0n), g), D))), True{},
            Equal.cong(Nat, Bool, z => RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(1n+z, g), D))), rb0, Nat.add(rb0, 0n), Equal.sym(Nat, Nat.add(rb0, 0n), rb0, ez)), hi)
          +eb : {P.Pz.below(bias, Nat.mul(1n+rb0, g), x) == True{} : Bool} = Equal.trans(Bool, P.Pz.below(bias, Nat.mul(1n+rb0, g), x), RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(1n+rb0, g), D))), True{}, Below.at(bias, Nat.mul(1n+rb0, g), D, n, hn), hi0)
          Equal.trans(Nat, P.Pz.find(g, bias, 1n+c2, rb0, x), rb0, Nat.add(rb0, 0n),
            Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, rb0, P.Pz.find(g, bias, c2, 1n+rb0, x)), P.Pz.below(bias, Nat.mul(1n+rb0, g), x), True{}, eb), Equal.sym(Nat, Nat.add(rb0, 0n), rb0, ez))
        case 1n+(+k2):
          +x = D.Dy.of(D, I.IPos{n})
          +nb = Nat.mul(n, RD.Nat.pow2(bias))
          +es : {Nat.add(rb0, 1n+k2) == 1n+Nat.add(rb0, k2) : Nat} = NL.Nat.add_succ_r(rb0, k2)
          +lo2 : {RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(Nat.add(1n+rb0, k2), g), D))) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(1n+Nat.add(rb0, k2), g), D))), RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(Nat.add(rb0, 1n+k2), g), D))), False{},
            Equal.cong(Nat, Bool, z => RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(z, g), D))), 1n+Nat.add(rb0, k2), Nat.add(rb0, 1n+k2), Equal.sym(Nat, Nat.add(rb0, 1n+k2), 1n+Nat.add(rb0, k2), es)), lo)
          +hi2 : {RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(1n+Nat.add(1n+rb0, k2), g), D))) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(1n+1n+Nat.add(rb0, k2), g), D))), RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(1n+Nat.add(rb0, 1n+k2), g), D))), True{},
            Equal.cong(Nat, Bool, z => RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(1n+z, g), D))), 1n+Nat.add(rb0, k2), Nat.add(rb0, 1n+k2), Equal.sym(Nat, Nat.add(rb0, 1n+k2), 1n+Nat.add(rb0, k2), es)), hi)
          # (1 + rb0) g <= (rb0 + 1 + k2) g, so x is not below 2^((1 + rb0) g - bias)
          +hm : {RD.Nat.lt(Nat.mul(1n+Nat.add(rb0, k2), g), Nat.mul(1n+rb0, g)) == False{} : Bool} = E2.Le.mulr(1n+rb0, 1n+Nat.add(rb0, k2), g, E.Le.add(rb0, k2))
          +hp : {RD.Nat.lt(RD.Nat.pow2(Nat.add(Nat.mul(1n+Nat.add(rb0, k2), g), D)), RD.Nat.pow2(Nat.add(Nat.mul(1n+rb0, g), D))) == False{} : Bool} = E2.Pow2.mono(Nat.add(Nat.mul(1n+rb0, g), D), Nat.add(Nat.mul(1n+Nat.add(rb0, k2), g), D), E2.Le.addr(Nat.mul(1n+rb0, g), Nat.mul(1n+Nat.add(rb0, k2), g), D, hm))
          +nlo : {RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(1n+rb0, g), D))) == False{} : Bool} = E.Le.trans(RD.Nat.pow2(Nat.add(Nat.mul(1n+rb0, g), D)), RD.Nat.pow2(Nat.add(Nat.mul(1n+Nat.add(rb0, k2), g), D)), nb, hp, lo2)
          +eb : {P.Pz.below(bias, Nat.mul(1n+rb0, g), x) == False{} : Bool} = Equal.trans(Bool, P.Pz.below(bias, Nat.mul(1n+rb0, g), x), RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(1n+rb0, g), D))), False{}, Below.at(bias, Nat.mul(1n+rb0, g), D, n, hn), nlo)
          +ih : {P.Pz.find(g, bias, c2, 1n+rb0, x) == Nat.add(1n+rb0, k2) : Nat} = Find.go(g, bias, D, n, hn, c2, k2, 1n+rb0, lo2, hi2, hkc)
          Equal.trans(Nat, P.Pz.find(g, bias, 1n+c2, rb0, x), P.Pz.find(g, bias, c2, 1n+rb0, x), Nat.add(rb0, 1n+k2),
            Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, rb0, P.Pz.find(g, bias, c2, 1n+rb0, x)), P.Pz.below(bias, Nat.mul(1n+rb0, g), x), False{}, eb),
            Equal.trans(Nat, P.Pz.find(g, bias, c2, 1n+rb0, x), 1n+Nat.add(rb0, k2), Nat.add(rb0, 1n+k2), ih, Equal.sym(Nat, Nat.add(rb0, 1n+k2), 1n+Nat.add(rb0, k2), es)))

def Find.at(+g: Nat, +bias: Nat, +D: Nat, +n: Nat, +hn: {RD.Nat.lt(0n, n) == True{} : Bool}, +c: Nat, +rb: Nat,
  +lo: {RD.Nat.lt(Nat.mul(n, RD.Nat.pow2(bias)), RD.Nat.pow2(Nat.add(Nat.mul(rb, g), D))) == False{} : Bool},
  +hi: {RD.Nat.lt(Nat.mul(n, RD.Nat.pow2(bias)), RD.Nat.pow2(Nat.add(Nat.mul(1n+rb, g), D))) == True{} : Bool},
  +hkc: {RD.Nat.lt(rb, c) == True{} : Bool})
  -> {P.Pz.find(g, bias, c, 0n, D.Dy.of(D, I.IPos{n})) == rb : Nat}:
  Find.go(g, bias, D, n, hn, c, rb, 0n, lo, hi, hkc)

# Pz.fl in class rb
# -----------------

# fraction bits in class rb: p0 - 1 + (rs - regime length)
def Fb(+p01: Nat, +rs: Nat, +rb: Nat) -> Nat:
  Nat.add(p01, RD.Nat.monus(rs, P.Pz.rl(rs, rb)))

def Sig(+p01: Nat, +rs: Nat, +rb: Nat, +fr: Nat) -> Nat:
  Nat.add(RD.Nat.pow2(Fb(p01, rs, rb)), fr)

def Xn(+a: Nat, +s: Nat, +t: Nat) -> Nat:
  Nat.add(Nat.mul(a, RD.Nat.pow2(s)), t)

def Pos.n(+a: Nat, +s: Nat, +t: Nat, +fb: Nat, +ha: {RD.Nat.lt(a, RD.Nat.pow2(fb)) == False{} : Bool}) -> {RD.Nat.lt(0n, Xn(a, s, t)) == True{} : Bool}:
  +l1 : {RD.Nat.lt(a, 1n) == False{} : Bool} = E.Le.trans(1n, RD.Nat.pow2(fb), a, E2.Le.one(fb), ha)
  +l2 : {RD.Nat.lt(Nat.mul(a, RD.Nat.pow2(s)), Nat.mul(a, 1n)) == False{} : Bool} = E2.Le.mull(a, 1n, RD.Nat.pow2(s), E2.Le.one(s))
  +l3 : {RD.Nat.lt(Xn(a, s, t), 1n) == False{} : Bool} = E.Le.trans(1n, a, Xn(a, s, t), l1,
    E.Le.trans(a, Nat.mul(a, RD.Nat.pow2(s)), Xn(a, s, t), E.Le.trans(a, Nat.mul(a, 1n), Nat.mul(a, RD.Nat.pow2(s)), E.Le.eq(a, Nat.mul(a, 1n), Equal.sym(Nat, Nat.mul(a, 1n), a, NL.Nat.mul_one_r(a))), l2),
      E.Le.add(Nat.mul(a, RD.Nat.pow2(s)), t)))
  E2.Lt.le_trans(0n, 1n, Xn(a, s, t), {==}, l3)

# a value n / 2^D in class rb, n = a 2^s + t with t < 2^s and a = 2^fb + fr
# its significand (a 2^s / 2^D = a 2^(rb g + ee) / 2^(bias + fb)), rounds as
# the bit string: up to (a + 1) 2^s when guard and (sticky or a odd).
# Below minpos and above maxpos the format saturates, in the spec and in
# the standard alike, so those are hypotheses.
def Fl.at(+p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +D: Nat, +s: Nat, +t: Nat,
  +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool},
  +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool},
  +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(Fb(p01, rs, rb))) == True{} : Bool},
  +ht: {RD.Nat.lt(t, RD.Nat.pow2(s)) == True{} : Bool},
  +hD: {Nat.add(Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee), D) == Nat.add(s, Nat.add(P.Pz.bias(RD.Nat.pow2(es), rs), Fb(p01, rs, rb))) : Nat},
  +hti: {P.Pz.tiny(1n+p01, P.Pz.bias(RD.Nat.pow2(es), rs), D.Dy.of(D, I.IPos{Xn(Sig(p01, rs, rb, fr), s, t)})) == False{} : Bool},
  +hov: {P.Pz.over(1n+p01, P.Pz.bias(RD.Nat.pow2(es), rs), D.Dy.of(D, I.IPos{Xn(Sig(p01, rs, rb, fr), s, t)})) == False{} : Bool})
  -> {P.Pz.fl(1n+p01, RD.Nat.pow2(es), rs, D.Dy.of(D, I.IPos{Xn(Sig(p01, rs, rb, fr), s, t)})) == D.Dy.of(D, I.IPos{RnF(Sig(p01, rs, rb, fr), s, t)}) : D.Dy}:
  +g = RD.Nat.pow2(es)
  +bias = P.Pz.bias(g, rs)
  +fb = Fb(p01, rs, rb)
  +a = Sig(p01, rs, rb, fr)
  +n = Xn(a, s, t)
  +x = D.Dy.of(D, I.IPos{n})
  +Pf = RD.Nat.pow2(fb)
  +Ps = RD.Nat.pow2(s)
  +Pb = RD.Nat.pow2(bias)
  +T = Nat.add(Nat.mul(rb, g), ee)
  +E0 = Nat.add(s, Nat.add(bias, fb))
  +PE = RD.Nat.pow2(E0)
  +Pbf = RD.Nat.pow2(Nat.add(bias, fb))
  +nb = Nat.mul(n, Pb)
  +hlo : {RD.Nat.lt(a, Pf) == False{} : Bool} = E.Le.add(Pf, fr)
  +hn : {RD.Nat.lt(0n, n) == True{} : Bool} = Pos.n(a, s, t, fb, hlo)
  +eE : {PE == Nat.mul(Ps, Pbf) : Nat} = BP.Pow2.add(s, Nat.add(bias, fb))
  +ebf : {Pbf == Nat.mul(Pb, Pf) : Nat} = BP.Pow2.add(bias, fb)
  # x >= 2^(rb g - bias)
  +env1 : List<&2, Nat> = [Pf, Ps, Pb, PE, 0n, 0n, Pbf, 0n, 0n, 1n]
  +l3 : {PE == Nat.mul(Nat.mul(Pf, Ps), Pb) : Nat} = R.NatN.eq2(env1, R.V(3n), R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(2n)), [R.V(1n)], [R.Ad(R.V(6n), R.Ng(R.Ml(R.V(2n), R.V(0n))))], [R.Ad(R.V(3n), R.Ng(R.Ml(R.V(1n), R.V(6n))))], {==}, (R.NatN.z(env1, R.V(6n), R.Ml(R.V(2n), R.V(0n)), {==}, {==}, ebf), Unit{}), (R.NatN.z(env1, R.V(3n), R.Ml(R.V(1n), R.V(6n)), {==}, {==}, eE), Unit{}), {==}, {==})
  +lo1 : {RD.Nat.lt(RD.Nat.pow2(Nat.add(T, D)), RD.Nat.pow2(Nat.add(Nat.mul(rb, g), D))) == False{} : Bool} = E2.Pow2.mono(Nat.add(Nat.mul(rb, g), D), Nat.add(T, D), E2.Le.addr(Nat.mul(rb, g), T, D, E.Le.add(Nat.mul(rb, g), ee)))
  +lo2 : {RD.Nat.pow2(Nat.add(T, D)) == Nat.mul(Nat.mul(Pf, Ps), Pb) : Nat} = Equal.trans(Nat, RD.Nat.pow2(Nat.add(T, D)), PE, Nat.mul(Nat.mul(Pf, Ps), Pb), Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), Nat.add(T, D), E0, hD), l3)
  +lo4 : {RD.Nat.lt(Nat.mul(Nat.mul(a, Ps), Pb), Nat.mul(Nat.mul(Pf, Ps), Pb)) == False{} : Bool} = E2.Le.mulr(Nat.mul(Pf, Ps), Nat.mul(a, Ps), Pb, E2.Le.mulr(Pf, a, Ps, hlo))
  +lo5 : {RD.Nat.lt(nb, Nat.mul(Nat.mul(a, Ps), Pb)) == False{} : Bool} = E2.Le.mulr(Nat.mul(a, Ps), n, Pb, E.Le.add(Nat.mul(a, Ps), t))
  +lo : {RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(Nat.mul(rb, g), D))) == False{} : Bool} = E.Le.trans(RD.Nat.pow2(Nat.add(Nat.mul(rb, g), D)), RD.Nat.pow2(Nat.add(T, D)), nb, lo1,
    E.Le.trans(RD.Nat.pow2(Nat.add(T, D)), Nat.mul(Nat.mul(Pf, Ps), Pb), nb, E.Le.eq(RD.Nat.pow2(Nat.add(T, D)), Nat.mul(Nat.mul(Pf, Ps), Pb), lo2),
      E.Le.trans(Nat.mul(Nat.mul(Pf, Ps), Pb), Nat.mul(Nat.mul(a, Ps), Pb), nb, lo4, lo5)))
  # x < 2^((rb + 1) g - bias)
  +dPf = Nat.double(Pf)
  +P1E = RD.Nat.pow2(1n+E0)
  +h1 : {RD.Nat.lt(nb, Nat.mul(Nat.mul(1n+a, Ps), Pb)) == True{} : Bool} = E.Lt.mono(n, Nat.mul(1n+a, Ps), Pb, Lt.next(a, s, t, ht), BP.Pow2.pos(bias))
  +le1 : {RD.Nat.lt(Nat.add(Pf, Pf), Nat.add(Pf, 1n+fr)) == False{} : Bool} = E2.Le.addl(Pf, 1n+fr, Pf, E2.Le.succ(fr, Pf, hfr))
  +edf : {dPf == Nat.add(Pf, Pf) : Nat} = Y.Nat.double_add(Pf)
  +le2 : {RD.Nat.lt(dPf, 1n+a) == False{} : Bool} = E.Le.trans(1n+a, Nat.add(Pf, 1n+fr), dPf, E.Le.eq(1n+a, Nat.add(Pf, 1n+fr), Equal.sym(Nat, Nat.add(Pf, 1n+fr), 1n+a, NL.Nat.add_succ_r(Pf, fr))),
    E.Le.trans(Nat.add(Pf, 1n+fr), Nat.add(Pf, Pf), dPf, le1, E.Le.eq(Nat.add(Pf, Pf), dPf, Equal.sym(Nat, dPf, Nat.add(Pf, Pf), edf))))
  +h2 : {RD.Nat.lt(Nat.mul(Nat.mul(dPf, Ps), Pb), Nat.mul(Nat.mul(1n+a, Ps), Pb)) == False{} : Bool} = E2.Le.mulr(Nat.mul(1n+a, Ps), Nat.mul(dPf, Ps), Pb, E2.Le.mulr(1n+a, dPf, Ps, le2))
  +e1E : {P1E == Nat.add(PE, PE) : Nat} = Y.Nat.double_add(PE)
  +env2 : List<&2, Nat> = [Pf, Ps, Pb, PE, P1E, dPf, Pbf, 0n, 0n, 1n]
  +h3 : {Nat.mul(Nat.mul(dPf, Ps), Pb) == P1E : Nat} = R.NatN.eq2(env2, R.Ml(R.Ml(R.V(5n), R.V(1n)), R.V(2n)), R.V(4n), [R.Ml(R.V(1n), R.V(2n)), R.Ad(R.Ng(R.V(1n)), R.Ng(R.V(1n)))], [R.Ad(R.V(5n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(6n), R.Ng(R.Ml(R.V(2n), R.V(0n))))], [R.Ad(R.Ad(R.V(3n), R.V(3n)), R.Ng(R.V(4n))), R.Ad(R.Ml(R.V(1n), R.V(6n)), R.Ng(R.V(3n))), R.Ad(R.Ml(R.V(1n), R.V(6n)), R.Ng(R.V(3n)))], {==}, (R.NatN.z(env2, R.V(5n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, edf), (R.NatN.z(env2, R.V(6n), R.Ml(R.V(2n), R.V(0n)), {==}, {==}, ebf), Unit{})), (R.NatN.z(env2, R.Ad(R.V(3n), R.V(3n)), R.V(4n), {==}, {==}, Equal.sym(Nat, P1E, Nat.add(PE, PE), e1E)), (R.NatN.z(env2, R.Ml(R.V(1n), R.V(6n)), R.V(3n), {==}, {==}, Equal.sym(Nat, PE, Nat.mul(Ps, Pbf), eE)), (R.NatN.z(env2, R.Ml(R.V(1n), R.V(6n)), R.V(3n), {==}, {==}, Equal.sym(Nat, PE, Nat.mul(Ps, Pbf), eE)), Unit{}))), {==}, {==})
  +rg = Nat.mul(rb, g)
  +g1 = Nat.mul(1n+rb, g)
  +eg1 : {Nat.add(rg, g) == g1 : Nat} = Equal.trans(Nat, Nat.add(rg, g), Nat.add(g, rg), g1, NL.Nat.add_comm(rg, g),
    Equal.trans(Nat, Nat.add(g, rg), Nat.add(Nat.mul(1n, g), rg), g1, Equal.cong(Nat, Nat, z => Nat.add(z, rg), g, Nat.mul(1n, g), Equal.sym(Nat, Nat.mul(1n, g), g, Mul.one_l(g))),
      Equal.sym(Nat, g1, Nat.add(Nat.mul(1n, g), rg), NL.Nat.mul_dist_r(1n, rb, g))))
  +leT : {RD.Nat.lt(g1, 1n+T) == False{} : Bool} = E.Le.trans(1n+T, Nat.add(rg, 1n+ee), g1, E.Le.eq(1n+T, Nat.add(rg, 1n+ee), Equal.sym(Nat, Nat.add(rg, 1n+ee), 1n+T, NL.Nat.add_succ_r(rg, ee))),
    E.Le.trans(Nat.add(rg, 1n+ee), Nat.add(rg, g), g1, E2.Le.addl(rg, 1n+ee, g, E2.Le.succ(ee, g, hee)), E.Le.eq(Nat.add(rg, g), g1, eg1)))
  +h4a : {RD.Nat.lt(RD.Nat.pow2(Nat.add(g1, D)), RD.Nat.pow2(Nat.add(1n+T, D))) == False{} : Bool} = E2.Pow2.mono(Nat.add(1n+T, D), Nat.add(g1, D), E2.Le.addr(1n+T, g1, D, leT))
  +eP1 : {P1E == RD.Nat.pow2(Nat.add(1n+T, D)) : Nat} = Equal.cong(Nat, Nat, z => RD.Nat.pow2(1n+z), E0, Nat.add(T, D), Equal.sym(Nat, Nat.add(T, D), E0, hD))
  +hi : {RD.Nat.lt(nb, RD.Nat.pow2(Nat.add(g1, D))) == True{} : Bool} = E2.Lt.le_trans(nb, Nat.mul(Nat.mul(1n+a, Ps), Pb), RD.Nat.pow2(Nat.add(g1, D)), h1,
    E.Le.trans(Nat.mul(Nat.mul(1n+a, Ps), Pb), Nat.mul(Nat.mul(dPf, Ps), Pb), RD.Nat.pow2(Nat.add(g1, D)), h2,
      E.Le.trans(Nat.mul(Nat.mul(dPf, Ps), Pb), P1E, RD.Nat.pow2(Nat.add(g1, D)), E.Le.eq(Nat.mul(Nat.mul(dPf, Ps), Pb), P1E, h3),
        E.Le.trans(P1E, RD.Nat.pow2(Nat.add(1n+T, D)), RD.Nat.pow2(Nat.add(g1, D)), E.Le.eq(P1E, RD.Nat.pow2(Nat.add(1n+T, D)), eP1), h4a))))
  # so the class is rb and the precision fb + 1
  +ef : {P.Pz.find(g, bias, Nat.double(rs), 0n, x) == rb : Nat} = Find.at(g, bias, D, n, hn, Nat.double(rs), rb, lo, hi, hrb)
  +ep : {P.Pz.prec(1n+p01, g, rs, x) == 1n+fb : Nat} = Equal.cong(Nat, Nat, z => Nat.add(1n+p01, RD.Nat.monus(rs, P.Pz.rl(rs, z))), P.Pz.find(g, bias, Nat.double(rs), 0n, x), rb, ef)
  # x is not zero
  +m = RD.Int.mag(D.Dy.num(x))
  +Pj = RD.Nat.pow2(RD.Nat.monus(D, D.Dy.den(x)))
  +en : {n == Nat.mul(m, Pj) : Nat} = Rep.num(D, n)
  +hm : {RD.Nat.lt(0n, m) == True{} : Bool} = Pos.fac(m, Pj, Equal.trans(Bool, RD.Nat.lt(0n, Nat.mul(m, Pj)), RD.Nat.lt(0n, n), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(0n, z), Nat.mul(m, Pj), n, Equal.sym(Nat, n, Nat.mul(m, Pj), en)), hn))
  +ez : {P.Pz.zero(x) == False{} : Bool} = Equal.cong(Bool, Bool, z => Bool.not(z), RD.Nat.lt(0n, m), True{}, hm)
  +s1 = Equal.cong(Bool, D.Dy, z => P.Pz.fl.go(1n+p01, g, rs, z, P.Pz.tiny(1n+p01, bias, x), P.Pz.over(1n+p01, bias, x), x), P.Pz.zero(x), False{}, ez)
  +s2 = Equal.cong(Bool, D.Dy, z => P.Pz.fl.go(1n+p01, g, rs, False{}, z, P.Pz.over(1n+p01, bias, x), x), P.Pz.tiny(1n+p01, bias, x), False{}, hti)
  +s3 = Equal.cong(Bool, D.Dy, z => P.Pz.fl.go(1n+p01, g, rs, False{}, False{}, z, x), P.Pz.over(1n+p01, bias, x), False{}, hov)
  +s4 = Equal.cong(Nat, D.Dy, z => RD.Dy.rne(z, x), P.Pz.prec(1n+p01, g, rs, x), 1n+fb, ep)
  +hhi : {RD.Nat.lt(a, RD.Nat.pow2(1n+fb)) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(a, dPf), RD.Nat.lt(a, Nat.add(Pf, Pf)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(a, z), dPf, Nat.add(Pf, Pf), edf),
    Equal.trans(Bool, RD.Nat.lt(Nat.add(Pf, fr), Nat.add(Pf, Pf)), RD.Nat.lt(fr, Pf), True{}, BP.Lt.shift(Pf, fr, Pf), hfr))
  +s5 = E2.Rne.of(fb, D, I.IPos{n})
  +s6 = Equal.cong(Nat, D.Dy, z => D.Dy.of(D, I.IPos{z}), E.Rn(1n+fb, n), RnF(a, s, t), Rn.at(fb, a, s, t, hlo, hhi, ht))
  Equal.trans(D.Dy, P.Pz.fl(1n+p01, g, rs, x), P.Pz.fl.go(1n+p01, g, rs, False{}, P.Pz.tiny(1n+p01, bias, x), P.Pz.over(1n+p01, bias, x), x), D.Dy.of(D, I.IPos{RnF(a, s, t)}), s1,
  Equal.trans(D.Dy, P.Pz.fl.go(1n+p01, g, rs, False{}, P.Pz.tiny(1n+p01, bias, x), P.Pz.over(1n+p01, bias, x), x), P.Pz.fl.go(1n+p01, g, rs, False{}, False{}, P.Pz.over(1n+p01, bias, x), x), D.Dy.of(D, I.IPos{RnF(a, s, t)}), s2,
  Equal.trans(D.Dy, P.Pz.fl.go(1n+p01, g, rs, False{}, False{}, P.Pz.over(1n+p01, bias, x), x), RD.Dy.rne(P.Pz.prec(1n+p01, g, rs, x), x), D.Dy.of(D, I.IPos{RnF(a, s, t)}), s3,
  Equal.trans(D.Dy, RD.Dy.rne(P.Pz.prec(1n+p01, g, rs, x), x), RD.Dy.rne(1n+fb, x), D.Dy.of(D, I.IPos{RnF(a, s, t)}), s4,
  Equal.trans(D.Dy, RD.Dy.rne(1n+fb, x), D.Dy.of(D, E.RNi(1n+fb, I.IPos{n})), D.Dy.of(D, I.IPos{RnF(a, s, t)}), s5, s6)))))
