# Double-word bounds (num/df32.bend; Joldes, Muller and Popescu, TOMS
# 2017; Muller and Rideau, TOMS 2022). DWTimesDW (Algorithm 10, no FMA):
# |zh + zl - x y| (1 + u)² <= 5u² |x y| for p >= 6 with ties to even, any
# signs and exponents, in binary rounding with no exponent bounds (DW1.gen,
# Muller and Rideau's Theorem 2.6). The proof is theirs, on integers:
# xh = A 2^(D+1) with 2^(p-1) <= A < 2^p, so u xh is 2^D (ADR-012).

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
import ./posit4.bend as P4
import ./posit5.bend as P5

# Rounding errors by magnitude
# ----------------------------

def Dist.self(+a: Nat) -> {E.Dist(a, a) == 0n : Nat}:
  Equal.trans(Nat, E.Dist(a, a), Nat.add(0n, RD.Nat.monus(a, a)), 0n, Equal.cong(Nat, Nat, z => Nat.add(z, RD.Nat.monus(a, a)), RD.Nat.monus(a, a), 0n, P4.Mo.self(a)), P4.Mo.self(a))

# Rn n = n for n = m 2^k with m <= 2^p
def Rn.fix(+p1: Nat, +n: Nat, +m: Nat, +k: Nat, +hn: {n == Nat.mul(m, RD.Nat.pow2(k)) : Nat}, +hm: {RD.Nat.lt(RD.Nat.pow2(1n+p1), m) == False{} : Bool}) -> {E.Rn(1n+p1, n) == n : Nat}:
  Equal.cong(I.Int, Nat, z => RD.Int.mag(z), I.IPos{E.Rn(1n+p1, n)}, I.IPos{n}, E2.Px(p1, I.IPos{n}, m, k, hn, hm))

def ErrB.go(+p1: Nat, +n: Nat, +s: Nat, +h: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s)), n) == False{} : Bool}, l: Bool, +el: {RD.Nat.lt(n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s))) == l : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(s), Nat.double(E.Dist(E.Rn(1n+p1, n), n))) == False{} : Bool}:
  match l:
    case True{}:
      E.Le.trans(Nat.double(E.Dist(E.Rn(1n+p1, n), n)), RD.Nat.pow2(E2.Shf(1n+p1, n)), RD.Nat.pow2(s), E2.ErrH(p1, n), E2.Pow2.mono(E2.Shf(1n+p1, n), s, E2.S3(p1, n, s, el)))
    case False{}:
      +en : {n == Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s)) : Nat} = E2.Le.anti(n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s)), h, el)
      +ef : {E.Rn(1n+p1, n) == n : Nat} = Rn.fix(p1, n, RD.Nat.pow2(1n+p1), s, en, P4.Lt.irr(RD.Nat.pow2(1n+p1)))
      +ez : {Nat.double(E.Dist(E.Rn(1n+p1, n), n)) == 0n : Nat} = Equal.trans(Nat, Nat.double(E.Dist(E.Rn(1n+p1, n), n)), Nat.double(E.Dist(n, n)), 0n,
        Equal.cong(Nat, Nat, z => Nat.double(E.Dist(z, n)), E.Rn(1n+p1, n), n, ef), Equal.cong(Nat, Nat, z => Nat.double(z), E.Dist(n, n), 0n, Dist.self(n)))
      Equal.trans(Bool, RD.Nat.lt(RD.Nat.pow2(s), Nat.double(E.Dist(E.Rn(1n+p1, n), n))), RD.Nat.lt(RD.Nat.pow2(s), 0n), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(RD.Nat.pow2(s), z), Nat.double(E.Dist(E.Rn(1n+p1, n), n)), 0n, ez), BP.Lt.z(RD.Nat.pow2(s)))

# |Rn n - n| <= 2^s / 2 when n <= 2^p 2^s
def ErrB(+p1: Nat, +n: Nat, +s: Nat, +h: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s)), n) == False{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(s), Nat.double(E.Dist(E.Rn(1n+p1, n), n))) == False{} : Bool}:
  ErrB.go(p1, n, s, h, RD.Nat.lt(n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s))), {==})

# Signed values
# -------------

def Mag.sg(+z: I.Int, +r: Nat) -> {RD.Int.mag(RD.Int.signed(z, r)) == r : Nat}:
  match z:
    case I.IPos{n}:
      {==}
    case I.INeg{n}:
      E.Mag.neg(I.IPos{r})

def MagD.go(+a: Nat, +b: Nat, l: Bool, +el: {RD.Nat.lt(a, b) == l : Bool}) -> {RD.Int.mag(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b}))) == E.Dist(a, b) : Nat}:
  match l:
    case True{}:
      +d = RD.Nat.monus(b, a)
      +eb : {b == Nat.add(d, a) : Nat} = Equal.trans(Nat, b, Nat.add(a, d), Nat.add(d, a), E.Le.wit(a, b, E2.Lt.to_le(a, b, el)), NL.Nat.add_comm(a, d))
      Equal.trans(Nat, RD.Int.mag(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b}))), d, E.Dist(a, b),
        Equal.trans(Nat, RD.Int.mag(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b}))), RD.Int.mag(I.Int.neg(I.IPos{d})), d,
          Equal.cong(I.Int, Nat, z => RD.Int.mag(z), I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b})), I.Int.neg(I.IPos{d}),
            Equal.trans(I.Int, I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b})), I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{Nat.add(d, a)})), I.Int.neg(I.IPos{d}),
              Equal.cong(Nat, I.Int, z => I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{z})), b, Nat.add(d, a), eb), BP.Ipm(d, a))),
          E.Mag.neg(I.IPos{d})),
        Equal.sym(Nat, E.Dist(a, b), d, Equal.trans(Nat, E.Dist(a, b), E.Dist(a, Nat.add(a, d)), d, Equal.cong(Nat, Nat, z => E.Dist(a, z), b, Nat.add(a, d), E.Le.wit(a, b, E2.Lt.to_le(a, b, el))), E.Dist.up(a, d))))
    case False{}:
      +d = RD.Nat.monus(a, b)
      +ea : {a == Nat.add(b, d) : Nat} = E.Le.wit(b, a, el)
      Equal.trans(Nat, RD.Int.mag(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b}))), d, E.Dist(a, b),
        Equal.cong(I.Int, Nat, z => RD.Int.mag(z), I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b})), I.IPos{d},
          Equal.trans(I.Int, I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b})), I.Int.add(I.IPos{Nat.add(d, b)}, I.Int.neg(I.IPos{b})), I.IPos{d},
            Equal.cong(Nat, I.Int, z => I.Int.add(I.IPos{z}, I.Int.neg(I.IPos{b})), a, Nat.add(d, b), Equal.trans(Nat, a, Nat.add(b, d), Nat.add(d, b), ea, NL.Nat.add_comm(b, d))), BP.Ipm2(d, b))),
        Equal.sym(Nat, E.Dist(a, b), d, Equal.trans(Nat, E.Dist(a, b), E.Dist(Nat.add(b, d), b), d, Equal.cong(Nat, Nat, z => E.Dist(z, b), a, Nat.add(b, d), ea), E.Dist.dn(b, d))))

# |a - b| for naturals embedded as integers
def MagD(+a: Nat, +b: Nat) -> {RD.Int.mag(I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{b}))) == E.Dist(a, b) : Nat}:
  MagD.go(a, b, RD.Nat.lt(a, b), {==})

def Dist.comm(+a: Nat, +b: Nat) -> {E.Dist(a, b) == E.Dist(b, a) : Nat}:
  NL.Nat.add_comm(RD.Nat.monus(a, b), RD.Nat.monus(b, a))

# the signed rounding error has the magnitude of the unsigned one
def Err.i(+p: Nat, +z: I.Int) -> {RD.Int.mag(I.Int.add(E.RNi(p, z), I.Int.neg(z))) == E.Dist(E.Rn(p, RD.Int.mag(z)), RD.Int.mag(z)) : Nat}:
  match z:
    case I.IPos{+n}:
      MagD(E.Rn(p, n), n)
    case I.INeg{+m}:
      +r = E.Rn(p, 1n+m)
      Equal.trans(Nat, RD.Int.mag(I.Int.add(I.Int.neg(I.IPos{r}), I.IPos{1n+m})), RD.Int.mag(I.Int.add(I.IPos{1n+m}, I.Int.neg(I.IPos{r}))), E.Dist(r, 1n+m),
        Equal.cong(I.Int, Nat, w => RD.Int.mag(w), I.Int.add(I.Int.neg(I.IPos{r}), I.IPos{1n+m}), I.Int.add(I.IPos{1n+m}, I.Int.neg(I.IPos{r})), Z.Int.add_comm(I.Int.neg(I.IPos{r}), I.IPos{1n+m})),
        Equal.trans(Nat, RD.Int.mag(I.Int.add(I.IPos{1n+m}, I.Int.neg(I.IPos{r}))), E.Dist(1n+m, r), E.Dist(r, 1n+m), MagD(1n+m, r), Dist.comm(1n+m, r)))

# Rounding facts, signed: |RN z - z| <= 2^s / 2 when |z| <= 2^p 2^s; RN
# keeps |z| below (above) a representable bound
def EB(+p1: Nat, +z: I.Int, +s: Nat, +h: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s)), RD.Int.mag(z)) == False{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(s), Nat.double(RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))))) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(RD.Nat.pow2(s), Nat.double(RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))))), RD.Nat.lt(RD.Nat.pow2(s), Nat.double(E.Dist(E.Rn(1n+p1, RD.Int.mag(z)), RD.Int.mag(z)))), False{},
    Equal.cong(Nat, Bool, w => RD.Nat.lt(RD.Nat.pow2(s), Nat.double(w)), RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))), E.Dist(E.Rn(1n+p1, RD.Int.mag(z)), RD.Int.mag(z)), Err.i(1n+p1, z)),
    ErrB(p1, RD.Int.mag(z), s, h))

def RB(+p1: Nat, +z: I.Int, +c: Nat, +fc: {E.Rn(1n+p1, c) == c : Nat}, +h: {RD.Nat.lt(c, RD.Int.mag(z)) == False{} : Bool})
  -> {RD.Nat.lt(c, RD.Int.mag(E.RNi(1n+p1, z))) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(c, RD.Int.mag(E.RNi(1n+p1, z))), RD.Nat.lt(c, E.Rn(1n+p1, RD.Int.mag(z))), False{},
    Equal.cong(Nat, Bool, w => RD.Nat.lt(c, w), RD.Int.mag(E.RNi(1n+p1, z)), E.Rn(1n+p1, RD.Int.mag(z)), Mag.sg(z, E.Rn(1n+p1, RD.Int.mag(z)))),
    E.Mono.hi(p1, RD.Int.mag(z), c, fc, h))

def RL(+p1: Nat, +z: I.Int, +c: Nat, +fc: {E.Rn(1n+p1, c) == c : Nat}, +h: {RD.Nat.lt(RD.Int.mag(z), c) == False{} : Bool})
  -> {RD.Nat.lt(RD.Int.mag(E.RNi(1n+p1, z)), c) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(RD.Int.mag(E.RNi(1n+p1, z)), c), RD.Nat.lt(E.Rn(1n+p1, RD.Int.mag(z)), c), False{},
    Equal.cong(Nat, Bool, w => RD.Nat.lt(w, c), RD.Int.mag(E.RNi(1n+p1, z)), E.Rn(1n+p1, RD.Int.mag(z)), Mag.sg(z, E.Rn(1n+p1, RD.Int.mag(z)))),
    E.Mono.lo(p1, RD.Int.mag(z), c, fc, h))

# DWTimesDW1 on integers
# ----------------------
# (xh, xl) (yh, yl) -> ch + cl1 = xh yh exactly (any exact 2Prod; Dekker's
# is proven so, proofs/eft2.bend, eft3.bend), tl1 = RN(xh yl),
# tl2 = RN(xl yh), cl2 = RN(tl1 + tl2), cl3 = RN(cl1 + cl2), and
# (zh, zl) = Fast2Sum(ch, cl3), computed as num/df32.bend does.

def M.ch(+p: Nat, +xh: I.Int, +yh: I.Int) -> I.Int:
  E.RNi(p, I.Int.mul(xh, yh))

def M.cl1(+p: Nat, +xh: I.Int, +yh: I.Int) -> I.Int:
  I.Int.add(I.Int.mul(xh, yh), I.Int.neg(M.ch(p, xh, yh)))

def M.tl1(+p: Nat, +xh: I.Int, +yl: I.Int) -> I.Int:
  E.RNi(p, I.Int.mul(xh, yl))

def M.tl2(+p: Nat, +xl: I.Int, +yh: I.Int) -> I.Int:
  E.RNi(p, I.Int.mul(xl, yh))

def M.cl2(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  E.RNi(p, I.Int.add(M.tl1(p, xh, yl), M.tl2(p, xl, yh)))

def M.cl3(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  E.RNi(p, I.Int.add(M.cl1(p, xh, yh), M.cl2(p, xh, xl, yh, yl)))

# zh + zl, the value of the double-word result
def M.z(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  I.Int.add(E.F2.s(p, M.ch(p, xh, yh), M.cl3(p, xh, xl, yh, yl)), E.F2.t(p, M.ch(p, xh, yh), M.cl3(p, xh, xl, yh, yl)))

def M.eta(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  I.Int.add(M.z(p, xh, xl, yh, yl), I.Int.neg(I.Int.mul(I.Int.add(xh, xl), I.Int.add(yh, yl))))

# the four rounding errors
def M.e1(+p: Nat, +xh: I.Int, +yl: I.Int) -> I.Int:
  I.Int.add(M.tl1(p, xh, yl), I.Int.neg(I.Int.mul(xh, yl)))

def M.e2(+p: Nat, +xl: I.Int, +yh: I.Int) -> I.Int:
  I.Int.add(M.tl2(p, xl, yh), I.Int.neg(I.Int.mul(xl, yh)))

def M.e3(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  I.Int.add(M.cl2(p, xh, xl, yh, yl), I.Int.neg(I.Int.add(M.tl1(p, xh, yl), M.tl2(p, xl, yh))))

def M.e4(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> I.Int:
  I.Int.add(M.cl3(p, xh, xl, yh, yl), I.Int.neg(I.Int.add(M.cl1(p, xh, yh), M.cl2(p, xh, xl, yh, yl))))

# eta = e1 + e2 + e3 + e4 - xl yl once Fast2Sum is exact
def M.eta.split(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int,
  +hz: {M.z(p, xh, xl, yh, yl) == I.Int.add(M.ch(p, xh, yh), M.cl3(p, xh, xl, yh, yl)) : I.Int})
  -> {M.eta(p, xh, xl, yh, yl) == I.Int.add(I.Int.add(I.Int.add(M.e1(p, xh, yl), M.e2(p, xl, yh)), I.Int.add(M.e3(p, xh, xl, yh, yl), M.e4(p, xh, xl, yh, yl))), I.Int.neg(I.Int.mul(xl, yl))) : I.Int}:
  +ch = M.ch(p, xh, yh)
  +t1 = M.tl1(p, xh, yl)
  +t2 = M.tl2(p, xl, yh)
  +c2 = M.cl2(p, xh, xl, yh, yl)
  +c3 = M.cl3(p, xh, xl, yh, yl)
  +env : List<&2, I.Int> = [xh, xl, yh, yl, ch, t1, t2, c2, c3]
  +xh_ = R.V(0n)
  +xl_ = R.V(1n)
  +yh_ = R.V(2n)
  +yl_ = R.V(3n)
  +ch_ = R.V(4n)
  +t1_ = R.V(5n)
  +t2_ = R.V(6n)
  +c2_ = R.V(7n)
  +c3_ = R.V(8n)
  +cl1_ = R.Ad(R.Ml(xh_, yh_), R.Ng(ch_))
  +lhs = R.Ad(R.Ad(ch_, c3_), R.Ng(R.Ml(R.Ad(xh_, xl_), R.Ad(yh_, yl_))))
  +rhs = R.Ad(R.Ad(R.Ad(R.Ad(t1_, R.Ng(R.Ml(xh_, yl_))), R.Ad(t2_, R.Ng(R.Ml(xl_, yh_)))), R.Ad(R.Ad(c2_, R.Ng(R.Ad(t1_, t2_))), R.Ad(c3_, R.Ng(R.Ad(cl1_, c2_))))), R.Ng(R.Ml(xl_, yl_)))
  Equal.trans(I.Int, M.eta(p, xh, xl, yh, yl), I.Int.add(I.Int.add(ch, c3), I.Int.neg(I.Int.mul(I.Int.add(xh, xl), I.Int.add(yh, yl)))), I.Int.add(I.Int.add(I.Int.add(M.e1(p, xh, yl), M.e2(p, xl, yh)), I.Int.add(M.e3(p, xh, xl, yh, yl), M.e4(p, xh, xl, yh, yl))), I.Int.neg(I.Int.mul(xl, yl))),
    Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.neg(I.Int.mul(I.Int.add(xh, xl), I.Int.add(yh, yl)))), M.z(p, xh, xl, yh, yl), I.Int.add(ch, c3), hz),
    BP.IntN(env, lhs, rhs, [], [], {==}, Unit{}))

# Bounds on the partial products
# ------------------------------
# xh = A 2^(D+1), A in [2^(p-1), 2^p): xh in [1, 2 - 2u] in units of
# 2^(p+D), so u is 2^D at the inputs, 2^(2D+p) at the products, and u² is
# V = 2^(2D). |xl|, |yl| <= 2^D.

def Half.p(+m: Nat, +s: Nat, +h: {RD.Nat.lt(RD.Nat.pow2(1n+s), Nat.double(m)) == False{} : Bool}) -> {RD.Nat.lt(RD.Nat.pow2(s), m) == False{} : Bool}:
  E2.Le.half(m, RD.Nat.pow2(s), E.Le.trans(Nat.double(m), Nat.double(RD.Nat.pow2(s)), Nat.add(RD.Nat.pow2(s), RD.Nat.pow2(s)), h, E.Le.eq(Nat.double(RD.Nat.pow2(s)), Nat.add(RD.Nat.pow2(s), RD.Nat.pow2(s)), Y.Nat.double_add(RD.Nat.pow2(s)))))

def Mo.le(+a: Nat, +b: Nat) -> {RD.Nat.lt(a, RD.Nat.monus(a, b)) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+b2:
      {==}
    case 1n+a2 0n:
      P4.Lt.irr(1n+a2)
    case 1n+(+a2) 1n+(+b2):
      E.Le.trans(RD.Nat.monus(a2, b2), a2, 1n+a2, Mo.le(a2, b2), P4.Lt.sa(a2))

def Lt.pos(+m: Nat, +P: Nat, +h: {RD.Nat.lt(m, P) == True{} : Bool}) -> {P == 1n+RD.Nat.monus(P, 1n) : Nat}:
  match P:
    case 0n:
      B.Bool.tf({0n == 1n+RD.Nat.monus(0n, 1n) : Nat}, Equal.trans(Bool, True{}, RD.Nat.lt(m, 0n), False{}, Equal.sym(Bool, RD.Nat.lt(m, 0n), True{}, h), BP.Lt.z(m)))
    case 1n+(+q):
      Equal.cong(Nat, Nat, z => 1n+z, q, RD.Nat.monus(q, 0n), Equal.sym(Nat, RD.Nat.monus(q, 0n), q, BP.Mo.z(q)))

def Lt.pm(+m: Nat, +P: Nat, +h: {RD.Nat.lt(m, P) == True{} : Bool}) -> {RD.Nat.lt(RD.Nat.monus(P, 1n), m) == False{} : Bool}:
  E2.Le.of_lt1(m, RD.Nat.monus(P, 1n), Equal.trans(Bool, RD.Nat.lt(m, 1n+RD.Nat.monus(P, 1n)), RD.Nat.lt(m, P), True{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(m, z), 1n+RD.Nat.monus(P, 1n), P, Equal.sym(Nat, P, 1n+RD.Nat.monus(P, 1n), Lt.pos(m, P, h))), h))

def K1(+p1: Nat, +D: Nat) -> Nat:
  Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 1n), RD.Nat.pow2(1n+Nat.add(D, D)))

def XH(+A: Nat, +D: Nat) -> I.Int:
  I.IPos{Nat.mul(A, RD.Nat.pow2(1n+D))}

# m 2^(D+1) y <= (2^p - 1) 2^(2D+1) for m < 2^p, y <= 2^D: 2u - 2u²
def Prod.le(+p1: Nat, +D: Nat, +m: Nat, +y: Nat, +hm: {RD.Nat.lt(m, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), y) == False{} : Bool})
  -> {RD.Nat.lt(K1(p1, D), Nat.mul(Nat.mul(m, RD.Nat.pow2(1n+D)), y)) == False{} : Bool}:
  +M1 = RD.Nat.monus(RD.Nat.pow2(1n+p1), 1n)
  +e : {Nat.mul(Nat.mul(M1, RD.Nat.pow2(1n+D)), RD.Nat.pow2(D)) == K1(p1, D) : Nat} = Equal.trans(Nat, Nat.mul(Nat.mul(M1, RD.Nat.pow2(1n+D)), RD.Nat.pow2(D)), Nat.mul(M1, Nat.mul(RD.Nat.pow2(1n+D), RD.Nat.pow2(D))), K1(p1, D),
    NL.Nat.mul_assoc(M1, RD.Nat.pow2(1n+D), RD.Nat.pow2(D)),
    Equal.cong(Nat, Nat, z => Nat.mul(M1, z), Nat.mul(RD.Nat.pow2(1n+D), RD.Nat.pow2(D)), RD.Nat.pow2(1n+Nat.add(D, D)), Equal.sym(Nat, RD.Nat.pow2(Nat.add(1n+D, D)), Nat.mul(RD.Nat.pow2(1n+D), RD.Nat.pow2(D)), BP.Pow2.add(1n+D, D))))
  E.Le.trans(Nat.mul(Nat.mul(m, RD.Nat.pow2(1n+D)), y), Nat.mul(Nat.mul(M1, RD.Nat.pow2(1n+D)), RD.Nat.pow2(D)), K1(p1, D),
    E2.Le.mul2(Nat.mul(m, RD.Nat.pow2(1n+D)), Nat.mul(M1, RD.Nat.pow2(1n+D)), y, RD.Nat.pow2(D), E2.Le.mulr(m, M1, RD.Nat.pow2(1n+D), Lt.pm(m, RD.Nat.pow2(1n+p1), hm)), hy),
    E.Le.eq(Nat.mul(Nat.mul(M1, RD.Nat.pow2(1n+D)), RD.Nat.pow2(D)), K1(p1, D), e))

def K1.fix(+p1: Nat, +D: Nat) -> {E.Rn(1n+p1, K1(p1, D)) == K1(p1, D) : Nat}:
  Rn.fix(p1, K1(p1, D), RD.Nat.monus(RD.Nat.pow2(1n+p1), 1n), 1n+Nat.add(D, D), {==}, Mo.le(RD.Nat.pow2(1n+p1), 1n))

# |z| <= 2u - 2u² keeps |RN z| <= 2u - 2u² and |RN z - z| <= u²
def Rt.le(+p1: Nat, +D: Nat, +z: I.Int, +h: {RD.Nat.lt(K1(p1, D), RD.Int.mag(z)) == False{} : Bool}) -> {RD.Nat.lt(K1(p1, D), RD.Int.mag(E.RNi(1n+p1, z))) == False{} : Bool}:
  RB(p1, z, K1(p1, D), K1.fix(p1, D), h)

def Et.le(+p1: Nat, +D: Nat, +z: I.Int, +h: {RD.Nat.lt(K1(p1, D), RD.Int.mag(z)) == False{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(Nat.add(D, D)), RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z)))) == False{} : Bool}:
  +s : Nat = 1n+Nat.add(D, D)
  +hz : {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s)), RD.Int.mag(z)) == False{} : Bool} = E.Le.trans(RD.Int.mag(z), K1(p1, D), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s)), h,
    E2.Le.mulr(RD.Nat.monus(RD.Nat.pow2(1n+p1), 1n), RD.Nat.pow2(1n+p1), RD.Nat.pow2(s), Mo.le(RD.Nat.pow2(1n+p1), 1n)))
  Half.p(RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))), Nat.add(D, D), EB(p1, z, s, hz))

def TL1.mag(+A: Nat, +D: Nat, +yl: I.Int) -> {RD.Int.mag(I.Int.mul(XH(A, D), yl)) == Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+D)), RD.Int.mag(yl)) : Nat}:
  E2.Mag.mul(XH(A, D), yl)

def TL2.mag(+B: Nat, +D: Nat, +xl: I.Int) -> {RD.Int.mag(I.Int.mul(xl, XH(B, D))) == Nat.mul(Nat.mul(B, RD.Nat.pow2(1n+D)), RD.Int.mag(xl)) : Nat}:
  Equal.trans(Nat, RD.Int.mag(I.Int.mul(xl, XH(B, D))), Nat.mul(RD.Int.mag(xl), Nat.mul(B, RD.Nat.pow2(1n+D))), Nat.mul(Nat.mul(B, RD.Nat.pow2(1n+D)), RD.Int.mag(xl)),
    E2.Mag.mul(xl, XH(B, D)), NL.Nat.mul_comm(RD.Int.mag(xl), Nat.mul(B, RD.Nat.pow2(1n+D))))

def P1.le(+p1: Nat, +D: Nat, +A: Nat, +yl: I.Int, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool})
  -> {RD.Nat.lt(K1(p1, D), RD.Int.mag(I.Int.mul(XH(A, D), yl))) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(K1(p1, D), RD.Int.mag(I.Int.mul(XH(A, D), yl))), RD.Nat.lt(K1(p1, D), Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+D)), RD.Int.mag(yl))), False{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(K1(p1, D), z), RD.Int.mag(I.Int.mul(XH(A, D), yl)), Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+D)), RD.Int.mag(yl)), TL1.mag(A, D, yl)),
    Prod.le(p1, D, A, RD.Int.mag(yl), hA, hy))

def P2.le(+p1: Nat, +D: Nat, +B: Nat, +xl: I.Int, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool})
  -> {RD.Nat.lt(K1(p1, D), RD.Int.mag(I.Int.mul(xl, XH(B, D)))) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(K1(p1, D), RD.Int.mag(I.Int.mul(xl, XH(B, D)))), RD.Nat.lt(K1(p1, D), Nat.mul(Nat.mul(B, RD.Nat.pow2(1n+D)), RD.Int.mag(xl))), False{},
    Equal.cong(Nat, Bool, z => RD.Nat.lt(K1(p1, D), z), RD.Int.mag(I.Int.mul(xl, XH(B, D))), Nat.mul(Nat.mul(B, RD.Nat.pow2(1n+D)), RD.Int.mag(xl)), TL2.mag(B, D, xl)),
    Prod.le(p1, D, B, RD.Int.mag(xl), hB, hx))

# The high product
# ----------------

def S4(+D: Nat) -> Nat:
  2n+Nat.add(D, D)

def Nn(+A: Nat, +B: Nat, +D: Nat) -> Nat:
  Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+D)), Nat.mul(B, RD.Nat.pow2(1n+D)))

def Pw4.sq(+D: Nat) -> {RD.Nat.pow2(S4(D)) == Nat.mul(RD.Nat.pow2(1n+D), RD.Nat.pow2(1n+D)) : Nat}:
  Equal.trans(Nat, RD.Nat.pow2(S4(D)), RD.Nat.pow2(Nat.add(1n+D, 1n+D)), Nat.mul(RD.Nat.pow2(1n+D), RD.Nat.pow2(1n+D)),
    Equal.cong(Nat, Nat, z => RD.Nat.pow2(1n+z), 1n+Nat.add(D, D), Nat.add(D, 1n+D), Equal.sym(Nat, Nat.add(D, 1n+D), 1n+Nat.add(D, D), NL.Nat.add_succ_r(D, D))),
    BP.Pow2.add(1n+D, 1n+D))

# xh yh = A B 4u²... in product units: A B 2^(2D+2)
def Nn.eq(+A: Nat, +B: Nat, +D: Nat) -> {Nn(A, B, D) == Nat.mul(Nat.mul(A, B), RD.Nat.pow2(S4(D))) : Nat}:
  +Q = RD.Nat.pow2(1n+D)
  +env : List<&2, Nat> = [A, B, Q, RD.Nat.pow2(S4(D))]
  R.NatN.eq(env, R.Ml(R.Ml(R.V(0n), R.V(2n)), R.Ml(R.V(1n), R.V(2n))), R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(3n)), [R.Ng(R.Ml(R.V(0n), R.V(1n)))], [R.Ad(R.V(3n), R.Ng(R.Ml(R.V(2n), R.V(2n))))], {==},
    (R.NatN.z(env, R.V(3n), R.Ml(R.V(2n), R.V(2n)), {==}, {==}, Pw4.sq(D)), Unit{}), {==}, {==})

def Prod.hh(+A: Nat, +B: Nat, +D: Nat) -> {I.Int.mul(XH(A, D), XH(B, D)) == I.IPos{Nn(A, B, D)} : I.Int}:
  E2.Int.mulpp(Nat.mul(A, RD.Nat.pow2(1n+D)), Nat.mul(B, RD.Nat.pow2(1n+D)))

# rounding commutes with powers of 2
def Rn.sc(+p: Nat, +m: Nat, +k: Nat) -> {E.Rn(p, Nat.mul(m, RD.Nat.pow2(k))) == Nat.mul(E.Rn(p, m), RD.Nat.pow2(k)) : Nat}:
  +e1 : {E.RNi(p, D.Int.sh(k, I.IPos{m})) == D.Int.sh(k, E.RNi(p, I.IPos{m})) : I.Int} = E.RNi.sh(p, k, I.IPos{m})
  +e2 : {I.IPos{E.Rn(p, Nat.mul(m, RD.Nat.pow2(k)))} == I.IPos{Nat.mul(E.Rn(p, m), RD.Nat.pow2(k))} : I.Int} = Equal.trans(I.Int, E.RNi(p, I.IPos{Nat.mul(m, RD.Nat.pow2(k))}), D.Int.sh(k, E.RNi(p, I.IPos{m})), I.IPos{Nat.mul(E.Rn(p, m), RD.Nat.pow2(k))},
    Equal.trans(I.Int, E.RNi(p, I.IPos{Nat.mul(m, RD.Nat.pow2(k))}), E.RNi(p, D.Int.sh(k, I.IPos{m})), D.Int.sh(k, E.RNi(p, I.IPos{m})),
      Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.IPos{Nat.mul(m, RD.Nat.pow2(k))}, D.Int.sh(k, I.IPos{m}), Equal.sym(I.Int, D.Int.sh(k, I.IPos{m}), I.IPos{Nat.mul(m, RD.Nat.pow2(k))}, R.Sh.ipos(k, m))), e1),
    R.Sh.ipos(k, E.Rn(p, m)))
  Equal.cong(I.Int, Nat, z => RD.Int.mag(z), I.IPos{E.Rn(p, Nat.mul(m, RD.Nat.pow2(k)))}, I.IPos{Nat.mul(E.Rn(p, m), RD.Nat.pow2(k))}, e2)

def Ch.eq(+p: Nat, +A: Nat, +B: Nat, +D: Nat) -> {M.ch(p, XH(A, D), XH(B, D)) == I.IPos{E.Rn(p, Nn(A, B, D))} : I.Int}:
  Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.mul(XH(A, D), XH(B, D)), I.IPos{Nn(A, B, D)}, Prod.hh(A, B, D))

# cl1 = (A B - RN(A B)) 4u²: a multiple of 4u²
def W1(+p: Nat, +A: Nat, +B: Nat) -> I.Int:
  I.Int.add(I.IPos{Nat.mul(A, B)}, I.Int.neg(I.IPos{E.Rn(p, Nat.mul(A, B))}))

def Cl1.sh(+p: Nat, +A: Nat, +B: Nat, +D: Nat) -> {M.cl1(p, XH(A, D), XH(B, D)) == D.Int.sh(S4(D), W1(p, A, B)) : I.Int}:
  +k = S4(D)
  +AB = Nat.mul(A, B)
  +e1 : {M.cl1(p, XH(A, D), XH(B, D)) == I.Int.add(I.IPos{Nn(A, B, D)}, I.Int.neg(I.IPos{E.Rn(p, Nn(A, B, D))})) : I.Int} = Equal.trans(I.Int, M.cl1(p, XH(A, D), XH(B, D)), I.Int.add(I.IPos{Nn(A, B, D)}, I.Int.neg(M.ch(p, XH(A, D), XH(B, D)))), I.Int.add(I.IPos{Nn(A, B, D)}, I.Int.neg(I.IPos{E.Rn(p, Nn(A, B, D))})),
    Equal.cong(I.Int, I.Int, z => I.Int.add(z, I.Int.neg(M.ch(p, XH(A, D), XH(B, D)))), I.Int.mul(XH(A, D), XH(B, D)), I.IPos{Nn(A, B, D)}, Prod.hh(A, B, D)),
    Equal.cong(I.Int, I.Int, z => I.Int.add(I.IPos{Nn(A, B, D)}, I.Int.neg(z)), M.ch(p, XH(A, D), XH(B, D)), I.IPos{E.Rn(p, Nn(A, B, D))}, Ch.eq(p, A, B, D)))
  +eN : {Nn(A, B, D) == Nat.mul(AB, RD.Nat.pow2(k)) : Nat} = Nn.eq(A, B, D)
  +e2 : {I.Int.add(I.IPos{Nn(A, B, D)}, I.Int.neg(I.IPos{E.Rn(p, Nn(A, B, D))})) == I.Int.add(I.IPos{Nat.mul(AB, RD.Nat.pow2(k))}, I.Int.neg(I.IPos{Nat.mul(E.Rn(p, AB), RD.Nat.pow2(k))})) : I.Int} =
    Equal.trans(I.Int, I.Int.add(I.IPos{Nn(A, B, D)}, I.Int.neg(I.IPos{E.Rn(p, Nn(A, B, D))})), I.Int.add(I.IPos{Nat.mul(AB, RD.Nat.pow2(k))}, I.Int.neg(I.IPos{E.Rn(p, Nat.mul(AB, RD.Nat.pow2(k)))})), I.Int.add(I.IPos{Nat.mul(AB, RD.Nat.pow2(k))}, I.Int.neg(I.IPos{Nat.mul(E.Rn(p, AB), RD.Nat.pow2(k))})),
      Equal.cong(Nat, I.Int, z => I.Int.add(I.IPos{z}, I.Int.neg(I.IPos{E.Rn(p, z)})), Nn(A, B, D), Nat.mul(AB, RD.Nat.pow2(k)), eN),
      Equal.cong(Nat, I.Int, z => I.Int.add(I.IPos{Nat.mul(AB, RD.Nat.pow2(k))}, I.Int.neg(I.IPos{z})), E.Rn(p, Nat.mul(AB, RD.Nat.pow2(k))), Nat.mul(E.Rn(p, AB), RD.Nat.pow2(k)), Rn.sc(p, AB, k)))
  +e3 : {D.Int.sh(k, W1(p, A, B)) == I.Int.add(I.IPos{Nat.mul(AB, RD.Nat.pow2(k))}, I.Int.neg(I.IPos{Nat.mul(E.Rn(p, AB), RD.Nat.pow2(k))})) : I.Int} =
    Equal.trans(I.Int, D.Int.sh(k, W1(p, A, B)), I.Int.add(D.Int.sh(k, I.IPos{AB}), D.Int.sh(k, I.Int.neg(I.IPos{E.Rn(p, AB)}))), I.Int.add(I.IPos{Nat.mul(AB, RD.Nat.pow2(k))}, I.Int.neg(I.IPos{Nat.mul(E.Rn(p, AB), RD.Nat.pow2(k))})),
      Y.Int.sh_add(k, I.IPos{AB}, I.Int.neg(I.IPos{E.Rn(p, AB)})),
      Equal.trans(I.Int, I.Int.add(D.Int.sh(k, I.IPos{AB}), D.Int.sh(k, I.Int.neg(I.IPos{E.Rn(p, AB)}))), I.Int.add(I.IPos{Nat.mul(AB, RD.Nat.pow2(k))}, D.Int.sh(k, I.Int.neg(I.IPos{E.Rn(p, AB)}))), I.Int.add(I.IPos{Nat.mul(AB, RD.Nat.pow2(k))}, I.Int.neg(I.IPos{Nat.mul(E.Rn(p, AB), RD.Nat.pow2(k))})),
        Equal.cong(I.Int, I.Int, z => I.Int.add(z, D.Int.sh(k, I.Int.neg(I.IPos{E.Rn(p, AB)}))), D.Int.sh(k, I.IPos{AB}), I.IPos{Nat.mul(AB, RD.Nat.pow2(k))}, R.Sh.ipos(k, AB)),
        Equal.cong(I.Int, I.Int, z => I.Int.add(I.IPos{Nat.mul(AB, RD.Nat.pow2(k))}, z), D.Int.sh(k, I.Int.neg(I.IPos{E.Rn(p, AB)})), I.Int.neg(I.IPos{Nat.mul(E.Rn(p, AB), RD.Nat.pow2(k))}),
          Equal.trans(I.Int, D.Int.sh(k, I.Int.neg(I.IPos{E.Rn(p, AB)})), I.Int.neg(D.Int.sh(k, I.IPos{E.Rn(p, AB)})), I.Int.neg(I.IPos{Nat.mul(E.Rn(p, AB), RD.Nat.pow2(k))}),
            Y.Int.sh_neg(k, I.IPos{E.Rn(p, AB)}), Equal.cong(I.Int, I.Int, z => I.Int.neg(z), D.Int.sh(k, I.IPos{E.Rn(p, AB)}), I.IPos{Nat.mul(E.Rn(p, AB), RD.Nat.pow2(k))}, R.Sh.ipos(k, E.Rn(p, AB)))))))
  Equal.trans(I.Int, M.cl1(p, XH(A, D), XH(B, D)), I.Int.add(I.IPos{Nn(A, B, D)}, I.Int.neg(I.IPos{E.Rn(p, Nn(A, B, D))})), D.Int.sh(k, W1(p, A, B)), e1,
    Equal.trans(I.Int, I.Int.add(I.IPos{Nn(A, B, D)}, I.Int.neg(I.IPos{E.Rn(p, Nn(A, B, D))})), I.Int.add(I.IPos{Nat.mul(AB, RD.Nat.pow2(k))}, I.Int.neg(I.IPos{Nat.mul(E.Rn(p, AB), RD.Nat.pow2(k))})), D.Int.sh(k, W1(p, A, B)), e2,
      Equal.sym(I.Int, D.Int.sh(k, W1(p, A, B)), I.Int.add(I.IPos{Nat.mul(AB, RD.Nat.pow2(k))}, I.Int.neg(I.IPos{Nat.mul(E.Rn(p, AB), RD.Nat.pow2(k))})), e3)))

def Mag.shl(+k: Nat, +w: I.Int) -> {RD.Int.mag(D.Int.sh(k, w)) == Nat.mul(RD.Int.mag(w), RD.Nat.pow2(k)) : Nat}:
  Equal.trans(Nat, RD.Int.mag(D.Int.sh(k, w)), Nat.mul(RD.Int.mag(w), RD.Int.mag(Y.P(k))), Nat.mul(RD.Int.mag(w), RD.Nat.pow2(k)),
    Equal.trans(Nat, RD.Int.mag(D.Int.sh(k, w)), RD.Int.mag(I.Int.mul(w, Y.P(k))), Nat.mul(RD.Int.mag(w), RD.Int.mag(Y.P(k))),
      Equal.cong(I.Int, Nat, z => RD.Int.mag(z), D.Int.sh(k, w), I.Int.mul(w, Y.P(k)), Y.Sh.p(k, w)), E2.Mag.mul(w, Y.P(k))),
    Equal.cong(Nat, Nat, z => Nat.mul(RD.Int.mag(w), z), RD.Int.mag(Y.P(k)), RD.Nat.pow2(k),
      Equal.trans(Nat, RD.Int.mag(Y.P(k)), Nat.mul(1n, RD.Nat.pow2(k)), RD.Nat.pow2(k), Equal.cong(I.Int, Nat, z => RD.Int.mag(z), Y.P(k), I.IPos{Nat.mul(1n, RD.Nat.pow2(k))}, R.Sh.ipos(k, 1n)), P3.Mul.one_l(RD.Nat.pow2(k)))))

def Le.halve(+a: Nat, +b: Nat, +h: {RD.Nat.lt(Nat.double(b), Nat.double(a)) == False{} : Bool}) -> {RD.Nat.lt(b, a) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(b, a), RD.Nat.lt(Nat.double(b), Nat.double(a)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.double(b), Nat.double(a)), RD.Nat.lt(b, a), P5.Lt.ud(b, a)), h)

# |cl1| = |AB - RN(AB)| 4u², and 2 |AB - RN(AB)| <= 2^s for AB <= 2^p 2^s
def Cl1.mag(+p: Nat, +A: Nat, +B: Nat, +D: Nat) -> {RD.Int.mag(M.cl1(p, XH(A, D), XH(B, D))) == Nat.mul(E.Dist(E.Rn(p, Nat.mul(A, B)), Nat.mul(A, B)), RD.Nat.pow2(S4(D))) : Nat}:
  +AB = Nat.mul(A, B)
  Equal.trans(Nat, RD.Int.mag(M.cl1(p, XH(A, D), XH(B, D))), RD.Int.mag(D.Int.sh(S4(D), W1(p, A, B))), Nat.mul(E.Dist(E.Rn(p, AB), AB), RD.Nat.pow2(S4(D))),
    Equal.cong(I.Int, Nat, z => RD.Int.mag(z), M.cl1(p, XH(A, D), XH(B, D)), D.Int.sh(S4(D), W1(p, A, B)), Cl1.sh(p, A, B, D)),
    Equal.trans(Nat, RD.Int.mag(D.Int.sh(S4(D), W1(p, A, B))), Nat.mul(RD.Int.mag(W1(p, A, B)), RD.Nat.pow2(S4(D))), Nat.mul(E.Dist(E.Rn(p, AB), AB), RD.Nat.pow2(S4(D))),
      Mag.shl(S4(D), W1(p, A, B)),
      Equal.cong(Nat, Nat, z => Nat.mul(z, RD.Nat.pow2(S4(D))), RD.Int.mag(W1(p, A, B)), E.Dist(E.Rn(p, AB), AB), Equal.trans(Nat, RD.Int.mag(W1(p, A, B)), E.Dist(AB, E.Rn(p, AB)), E.Dist(E.Rn(p, AB), AB), MagD(AB, E.Rn(p, AB)), Dist.comm(AB, E.Rn(p, AB))))))

# 2 |cl1| <= 2^s 4u² for A B <= 2^p 2^s
def Cl1.le(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +s: Nat, +h: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s)), Nat.mul(A, B)) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(RD.Nat.pow2(s), RD.Nat.pow2(S4(D))), Nat.double(RD.Int.mag(M.cl1(1n+p1, XH(A, D), XH(B, D))))) == False{} : Bool}:
  +AB = Nat.mul(A, B)
  +d = E.Dist(E.Rn(1n+p1, AB), AB)
  +Q = RD.Nat.pow2(S4(D))
  +e : {Nat.double(RD.Int.mag(M.cl1(1n+p1, XH(A, D), XH(B, D)))) == Nat.mul(Nat.double(d), Q) : Nat} = Equal.trans(Nat, Nat.double(RD.Int.mag(M.cl1(1n+p1, XH(A, D), XH(B, D)))), Nat.double(Nat.mul(d, Q)), Nat.mul(Nat.double(d), Q),
    Equal.cong(Nat, Nat, z => Nat.double(z), RD.Int.mag(M.cl1(1n+p1, XH(A, D), XH(B, D))), Nat.mul(d, Q), Cl1.mag(1n+p1, A, B, D)), Equal.sym(Nat, Nat.mul(Nat.double(d), Q), Nat.double(Nat.mul(d, Q)), BP.Mul.dbl_l(d, Q)))
  E.Le.trans(Nat.double(RD.Int.mag(M.cl1(1n+p1, XH(A, D), XH(B, D)))), Nat.mul(Nat.double(d), Q), Nat.mul(RD.Nat.pow2(s), Q), E.Le.eq(Nat.double(RD.Int.mag(M.cl1(1n+p1, XH(A, D), XH(B, D)))), Nat.mul(Nat.double(d), Q), e),
    E2.Le.mulr(Nat.double(d), RD.Nat.pow2(s), Q, ErrB(p1, AB, s, h)))

# The low parts' sums
# -------------------

def K2(+p1: Nat, +D: Nat) -> Nat:
  Nat.mul(RD.Nat.monus(RD.Nat.pow2(1n+p1), 1n), RD.Nat.pow2(S4(D)))

def K2.fix(+p1: Nat, +D: Nat) -> {E.Rn(1n+p1, K2(p1, D)) == K2(p1, D) : Nat}:
  Rn.fix(p1, K2(p1, D), RD.Nat.monus(RD.Nat.pow2(1n+p1), 1n), S4(D), {==}, Mo.le(RD.Nat.pow2(1n+p1), 1n))

def K1.dbl(+p1: Nat, +D: Nat) -> {Nat.add(K1(p1, D), K1(p1, D)) == K2(p1, D) : Nat}:
  +M1 = RD.Nat.monus(RD.Nat.pow2(1n+p1), 1n)
  +Q = RD.Nat.pow2(1n+Nat.add(D, D))
  Equal.trans(Nat, Nat.add(Nat.mul(M1, Q), Nat.mul(M1, Q)), Nat.mul(M1, Nat.add(Q, Q)), K2(p1, D), Equal.sym(Nat, Nat.mul(M1, Nat.add(Q, Q)), Nat.add(Nat.mul(M1, Q), Nat.mul(M1, Q)), NL.Nat.mul_dist_l(M1, Q, Q)),
    Equal.cong(Nat, Nat, z => Nat.mul(M1, z), Nat.add(Q, Q), RD.Nat.pow2(S4(D)), Equal.sym(Nat, Nat.double(Q), Nat.add(Q, Q), Y.Nat.double_add(Q))))

# |a + b| <= ka + kb
def Tri2(+a: I.Int, +b: I.Int, +ka: Nat, +kb: Nat, +ha: {RD.Nat.lt(ka, RD.Int.mag(a)) == False{} : Bool}, +hb: {RD.Nat.lt(kb, RD.Int.mag(b)) == False{} : Bool})
  -> {RD.Nat.lt(Nat.add(ka, kb), RD.Int.mag(I.Int.add(a, b))) == False{} : Bool}:
  E.Le.trans(RD.Int.mag(I.Int.add(a, b)), Nat.add(RD.Int.mag(a), RD.Int.mag(b)), Nat.add(ka, kb), E2.Mag.tri(a, b), E2.Le.add2(RD.Int.mag(a), ka, RD.Int.mag(b), kb, ha, hb))

# |cl2| <= (2^p - 1) 4u², |e3| <= 2u², once |tl1|, |tl2| <= 2u - 2u²
def Cl2.le(+p1: Nat, +D: Nat, +t1: I.Int, +t2: I.Int, +h1: {RD.Nat.lt(K1(p1, D), RD.Int.mag(t1)) == False{} : Bool}, +h2: {RD.Nat.lt(K1(p1, D), RD.Int.mag(t2)) == False{} : Bool})
  -> {RD.Nat.lt(K2(p1, D), RD.Int.mag(I.Int.add(t1, t2))) == False{} : Bool}:
  E.Le.trans(RD.Int.mag(I.Int.add(t1, t2)), Nat.add(K1(p1, D), K1(p1, D)), K2(p1, D), Tri2(t1, t2, K1(p1, D), K1(p1, D), h1, h2), E.Le.eq(Nat.add(K1(p1, D), K1(p1, D)), K2(p1, D), K1.dbl(p1, D)))

def E3.le(+p1: Nat, +D: Nat, +c: I.Int, +h: {RD.Nat.lt(K2(p1, D), RD.Int.mag(c)) == False{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(1n+Nat.add(D, D)), RD.Int.mag(I.Int.add(E.RNi(1n+p1, c), I.Int.neg(c)))) == False{} : Bool}:
  +s = S4(D)
  +hz : {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s)), RD.Int.mag(c)) == False{} : Bool} = E.Le.trans(RD.Int.mag(c), K2(p1, D), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s)), h,
    E2.Le.mulr(RD.Nat.monus(RD.Nat.pow2(1n+p1), 1n), RD.Nat.pow2(1n+p1), RD.Nat.pow2(s), Mo.le(RD.Nat.pow2(1n+p1), 1n)))
  Half.p(RD.Int.mag(I.Int.add(E.RNi(1n+p1, c), I.Int.neg(c))), 1n+Nat.add(D, D), EB(p1, c, s, hz))

# P 2^k is representable
def Pk.fix(+p1: Nat, +k: Nat) -> {E.Rn(1n+p1, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k))) == Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k)) : Nat}:
  Rn.fix(p1, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k)), RD.Nat.pow2(1n+p1), k, {==}, P4.Lt.irr(RD.Nat.pow2(1n+p1)))

# |cl1| <= 2u and |cl2| <= 4u - 4u² give |cl1 + cl2| <= 8u: |cl3| <= 8u and |e4| <= 4u²
def C12.le(+p1: Nat, +D: Nat, +c1: I.Int, +c2: I.Int, +h1: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D))), RD.Int.mag(c1)) == False{} : Bool}, +h2: {RD.Nat.lt(K2(p1, D), RD.Int.mag(c2)) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(3n+Nat.add(D, D))), RD.Int.mag(I.Int.add(c1, c2))) == False{} : Bool}:
  +P = RD.Nat.pow2(1n+p1)
  +V2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +M1 = RD.Nat.monus(P, 1n)
  # P 2V + (P - 1) 4V <= P 2V + P 4V <= P 8V
  +l1 : {RD.Nat.lt(Nat.add(Nat.mul(P, V2), Nat.mul(P, RD.Nat.pow2(S4(D)))), Nat.add(Nat.mul(P, V2), K2(p1, D))) == False{} : Bool} = E2.Le.addl(Nat.mul(P, V2), K2(p1, D), Nat.mul(P, RD.Nat.pow2(S4(D))), E2.Le.mulr(M1, P, RD.Nat.pow2(S4(D)), Mo.le(P, 1n)))
  +env : List<&2, Nat> = [P, V2, RD.Nat.pow2(S4(D)), RD.Nat.pow2(3n+Nat.add(D, D))]
  +e4 : {RD.Nat.pow2(S4(D)) == Nat.add(V2, V2) : Nat} = Y.Nat.double_add(V2)
  +e8 : {RD.Nat.pow2(3n+Nat.add(D, D)) == Nat.add(RD.Nat.pow2(S4(D)), RD.Nat.pow2(S4(D))) : Nat} = Y.Nat.double_add(RD.Nat.pow2(S4(D)))
  +P2 = Nat.mul(P, V2)
  +P4 = Nat.mul(P, RD.Nat.pow2(S4(D)))
  +P8 = Nat.mul(P, RD.Nat.pow2(3n+Nat.add(D, D)))
  +l2 : {P8 == Nat.add(Nat.add(P2, P4), P2) : Nat} = R.NatN.eq(env,
    R.Ml(R.V(0n), R.V(3n)), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(1n))),
    [R.V(0n), R.V(0n)], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(2n), R.V(2n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.V(1n), R.V(1n))))], {==},
    (R.NatN.z(env, R.V(3n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, e8), (R.NatN.z(env, R.V(2n), R.Ad(R.V(1n), R.V(1n)), {==}, {==}, e4), Unit{})), {==}, {==})
  E.Le.trans(RD.Int.mag(I.Int.add(c1, c2)), Nat.add(P2, K2(p1, D)), P8, Tri2(c1, c2, P2, K2(p1, D), h1, h2),
    E.Le.trans(Nat.add(P2, K2(p1, D)), Nat.add(P2, P4), P8, l1,
      E.Le.trans(Nat.add(P2, P4), Nat.add(Nat.add(P2, P4), P2), P8, E.Le.add(Nat.add(P2, P4), P2), E.Le.eq(Nat.add(Nat.add(P2, P4), P2), P8, Equal.sym(Nat, P8, Nat.add(Nat.add(P2, P4), P2), l2)))))

def E4.le(+p1: Nat, +D: Nat, +c: I.Int, +h: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(3n+Nat.add(D, D))), RD.Int.mag(c)) == False{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(S4(D)), RD.Int.mag(I.Int.add(E.RNi(1n+p1, c), I.Int.neg(c)))) == False{} : Bool}:
  Half.p(RD.Int.mag(I.Int.add(E.RNi(1n+p1, c), I.Int.neg(c))), S4(D), EB(p1, c, 3n+Nat.add(D, D), h))

def Cl3.le(+p1: Nat, +D: Nat, +c: I.Int, +h: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(3n+Nat.add(D, D))), RD.Int.mag(c)) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(3n+Nat.add(D, D))), RD.Int.mag(E.RNi(1n+p1, c))) == False{} : Bool}:
  RB(p1, c, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(3n+Nat.add(D, D))), Pk.fix(p1, 3n+Nat.add(D, D)), h)

# ch >= 2^(p-1) 2^(p-1) 4u², i.e. ch >= 1 in product units
def Clo(+p1: Nat, +D: Nat) -> Nat:
  Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(p1, S4(D))))

def Ch.lo(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +hA: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool})
  -> {RD.Nat.lt(RD.Int.mag(M.ch(1n+p1, XH(A, D), XH(B, D))), Clo(p1, D)) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +Q = RD.Nat.pow2(S4(D))
  +ec : {Clo(p1, D) == Nat.mul(Nat.mul(H, H), Q) : Nat} = Equal.trans(Nat, Clo(p1, D), Nat.mul(H, Nat.mul(H, Q)), Nat.mul(Nat.mul(H, H), Q),
    Equal.cong(Nat, Nat, z => Nat.mul(H, z), RD.Nat.pow2(Nat.add(p1, S4(D))), Nat.mul(H, Q), BP.Pow2.add(p1, S4(D))), Equal.sym(Nat, Nat.mul(Nat.mul(H, H), Q), Nat.mul(H, Nat.mul(H, Q)), NL.Nat.mul_assoc(H, H, Q)))
  +fc : {E.Rn(1n+p1, Clo(p1, D)) == Clo(p1, D) : Nat} = Rn.fix(p1, Clo(p1, D), H, Nat.add(p1, S4(D)), {==}, E2.Lt.to_le(H, RD.Nat.pow2(1n+p1), E2.Lt.dself(H, BP.Pow2.pos(p1))))
  +hN : {RD.Nat.lt(Nn(A, B, D), Clo(p1, D)) == False{} : Bool} = E.Le.trans(Clo(p1, D), Nat.mul(Nat.mul(A, B), Q), Nn(A, B, D),
    E.Le.trans(Clo(p1, D), Nat.mul(Nat.mul(H, H), Q), Nat.mul(Nat.mul(A, B), Q), E.Le.eq(Clo(p1, D), Nat.mul(Nat.mul(H, H), Q), ec), E2.Le.mulr(Nat.mul(H, H), Nat.mul(A, B), Q, E2.Le.mul2(H, A, H, B, hA, hB))),
    E.Le.eq(Nat.mul(Nat.mul(A, B), Q), Nn(A, B, D), Equal.sym(Nat, Nn(A, B, D), Nat.mul(Nat.mul(A, B), Q), Nn.eq(A, B, D))))
  Equal.trans(Bool, RD.Nat.lt(RD.Int.mag(M.ch(1n+p1, XH(A, D), XH(B, D))), Clo(p1, D)), RD.Nat.lt(E.Rn(1n+p1, Nn(A, B, D)), Clo(p1, D)), False{},
    Equal.cong(I.Int, Bool, z => RD.Nat.lt(RD.Int.mag(z), Clo(p1, D)), M.ch(1n+p1, XH(A, D), XH(B, D)), I.IPos{E.Rn(1n+p1, Nn(A, B, D))}, Ch.eq(1n+p1, A, B, D)),
    E.Mono.lo(p1, Nn(A, B, D), Clo(p1, D), fc, hN))

# 8u <= 1 in product units, for p >= 3
def F2.pre(+p1: Nat, +D: Nat, +hp: {RD.Nat.lt(p1, 2n) == False{} : Bool})
  -> {RD.Nat.lt(Clo(p1, D), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(3n+Nat.add(D, D)))) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +Q4 = RD.Nat.pow2(S4(D))
  +Q8 = RD.Nat.pow2(3n+Nat.add(D, D))
  +P = RD.Nat.pow2(1n+p1)
  +X = Nat.mul(H, Q4)
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +e8 : {Q8 == Nat.add(Q4, Q4) : Nat} = Y.Nat.double_add(Q4)
  +env : List<&2, Nat> = [H, Q4, P, Q8]
  +X_ = R.Ml(R.V(0n), R.V(1n))
  +e48 : {Nat.mul(P, Q8) == Nat.mul(4n, X) : Nat} = R.NatN.eq(env, R.Ml(R.V(2n), R.V(3n)), R.Ad(X_, R.Ad(X_, R.Ad(X_, R.Ad(X_, N.TZero{})))),
    [R.V(3n), R.Ad(R.V(0n), R.V(0n))], [R.Ad(R.V(2n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(3n), R.Ng(R.Ad(R.V(1n), R.V(1n))))], {==},
    (R.NatN.z(env, R.V(2n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, eP), (R.NatN.z(env, R.V(3n), R.Ad(R.V(1n), R.V(1n)), {==}, {==}, e8), Unit{})), {==}, {==})
  +ec : {Clo(p1, D) == Nat.mul(H, X) : Nat} = Equal.cong(Nat, Nat, z => Nat.mul(H, z), RD.Nat.pow2(Nat.add(p1, S4(D))), X, BP.Pow2.add(p1, S4(D)))
  +h4 : {RD.Nat.lt(H, 4n) == False{} : Bool} = E2.Pow2.mono(2n, p1, hp)
  E.Le.trans(Nat.mul(P, Q8), Nat.mul(4n, X), Clo(p1, D), E.Le.eq(Nat.mul(P, Q8), Nat.mul(4n, X), e48),
    E.Le.trans(Nat.mul(4n, X), Nat.mul(H, X), Clo(p1, D), E2.Le.mulr(4n, H, X, h4), E.Le.eq(Nat.mul(H, X), Clo(p1, D), Equal.sym(Nat, Clo(p1, D), Nat.mul(H, X), ec))))

# The general bound
# -----------------

def Rf.i(+p1: Nat, +z: I.Int) -> {E.Rn(1n+p1, RD.Int.mag(E.RNi(1n+p1, z))) == RD.Int.mag(E.RNi(1n+p1, z)) : Nat}:
  +em : {RD.Int.mag(E.RNi(1n+p1, z)) == E.Rn(1n+p1, RD.Int.mag(z)) : Nat} = Mag.sg(z, E.Rn(1n+p1, RD.Int.mag(z)))
  Equal.trans(Nat, E.Rn(1n+p1, RD.Int.mag(E.RNi(1n+p1, z))), E.Rn(1n+p1, E.Rn(1n+p1, RD.Int.mag(z))), RD.Int.mag(E.RNi(1n+p1, z)),
    Equal.cong(Nat, Nat, w => E.Rn(1n+p1, w), RD.Int.mag(E.RNi(1n+p1, z)), E.Rn(1n+p1, RD.Int.mag(z)), em),
    Equal.trans(Nat, E.Rn(1n+p1, E.Rn(1n+p1, RD.Int.mag(z))), E.Rn(1n+p1, RD.Int.mag(z)), RD.Int.mag(E.RNi(1n+p1, z)), E.RF(p1, RD.Int.mag(z)), Equal.sym(Nat, RD.Int.mag(E.RNi(1n+p1, z)), E.Rn(1n+p1, RD.Int.mag(z)), em)))

def Le.pp(+A: Nat, +B: Nat, +P: Nat, +hA: {RD.Nat.lt(A, P) == True{} : Bool}, +hB: {RD.Nat.lt(B, P) == True{} : Bool}) -> {RD.Nat.lt(Nat.mul(P, P), Nat.mul(A, B)) == False{} : Bool}:
  E2.Le.mul2(A, P, B, P, E2.Lt.to_le(A, P, hA), E2.Lt.to_le(B, P, hB))

# |cl1| <= 2u = P 2u²
def Cl1.le2u(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool})
  -> {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D))), RD.Int.mag(M.cl1(1n+p1, XH(A, D), XH(B, D)))) == False{} : Bool}:
  +P = RD.Nat.pow2(1n+p1)
  +Y2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +c1 = RD.Int.mag(M.cl1(1n+p1, XH(A, D), XH(B, D)))
  Le.halve(c1, Nat.mul(P, Y2), E.Le.trans(Nat.double(c1), Nat.mul(P, RD.Nat.pow2(S4(D))), Nat.double(Nat.mul(P, Y2)), Cl1.le(p1, A, B, D, 1n+p1, Le.pp(A, B, P, hA, hB)),
    E.Le.eq(Nat.mul(P, RD.Nat.pow2(S4(D))), Nat.double(Nat.mul(P, Y2)), R.Nat.mul_double(P, Y2))))

def Cl2.k2(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int,
  +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool})
  -> {RD.Nat.lt(K2(p1, D), RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))))) == False{} : Bool}:
  Cl2.le(p1, D, M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)), Rt.le(p1, D, I.Int.mul(XH(A, D), yl), P1.le(p1, D, A, yl, hA, hy)), Rt.le(p1, D, I.Int.mul(xl, XH(B, D)), P2.le(p1, D, B, xl, hB, hx)))

def C12.p8(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int,
  +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(3n+Nat.add(D, D))), RD.Int.mag(I.Int.add(M.cl1(1n+p1, XH(A, D), XH(B, D)), M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  C12.le(p1, D, M.cl1(1n+p1, XH(A, D), XH(B, D)), M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl), Cl1.le2u(p1, A, B, D, hA, hB),
    RB(p1, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), K2(p1, D), K2.fix(p1, D), Cl2.k2(p1, A, B, D, xl, yl, hA, hB, hx, hy)))

# Fast2Sum(ch, cl3) is exact
def Zx.exact(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 2n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool})
  -> {M.z(1n+p1, XH(A, D), xl, XH(B, D), yl) == I.Int.add(M.ch(1n+p1, XH(A, D), XH(B, D)), M.cl3(1n+p1, XH(A, D), xl, XH(B, D), yl)) : I.Int}:
  +ch = M.ch(1n+p1, XH(A, D), XH(B, D))
  +c12 = I.Int.add(M.cl1(1n+p1, XH(A, D), XH(B, D)), M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl))
  +c3 = M.cl3(1n+p1, XH(A, D), xl, XH(B, D), yl)
  +P8 = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(3n+Nat.add(D, D)))
  +h12 = C12.p8(p1, A, B, D, xl, yl, hA, hB, hx, hy)
  +hle : {RD.Nat.lt(RD.Int.mag(ch), RD.Int.mag(c3)) == False{} : Bool} = E.Le.trans(RD.Int.mag(c3), P8, RD.Int.mag(ch), Cl3.le(p1, D, c12, h12),
    E.Le.trans(P8, Clo(p1, D), RD.Int.mag(ch), F2.pre(p1, D, hp), Ch.lo(p1, A, B, D, hA1, hB1)))
  E.Fast2Sum(p1, ch, c3, Rf.i(p1, I.Int.mul(XH(A, D), XH(B, D))), Rf.i(p1, c12), hle)

def Vsq(+D: Nat) -> {RD.Nat.pow2(Nat.add(D, D)) == Nat.mul(RD.Nat.pow2(D), RD.Nat.pow2(D)) : Nat}:
  BP.Pow2.add(D, D)

# |xl yl| <= u²
def XY.le(+D: Nat, +xl: I.Int, +yl: I.Int, +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(Nat.add(D, D)), RD.Int.mag(I.Int.neg(I.Int.mul(xl, yl)))) == False{} : Bool}:
  E.Le.trans(RD.Int.mag(I.Int.neg(I.Int.mul(xl, yl))), Nat.mul(RD.Int.mag(xl), RD.Int.mag(yl)), RD.Nat.pow2(Nat.add(D, D)), E2.Mag.negm(xl, yl),
    E.Le.trans(Nat.mul(RD.Int.mag(xl), RD.Int.mag(yl)), Nat.mul(RD.Nat.pow2(D), RD.Nat.pow2(D)), RD.Nat.pow2(Nat.add(D, D)), E2.Le.mul2(RD.Int.mag(xl), RD.Nat.pow2(D), RD.Int.mag(yl), RD.Nat.pow2(D), hx, hy),
      E.Le.eq(Nat.mul(RD.Nat.pow2(D), RD.Nat.pow2(D)), RD.Nat.pow2(Nat.add(D, D)), Equal.sym(Nat, RD.Nat.pow2(Nat.add(D, D)), Nat.mul(RD.Nat.pow2(D), RD.Nat.pow2(D)), Vsq(D)))))

# |eta| <= k1 + k2 + k3 + k4 + kx from bounds on the parts
def Eta.le(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +k1: Nat, +k2: Nat, +k3: Nat, +k4: Nat, +kx: Nat,
  +hz: {M.z(p, xh, xl, yh, yl) == I.Int.add(M.ch(p, xh, yh), M.cl3(p, xh, xl, yh, yl)) : I.Int},
  +h1: {RD.Nat.lt(k1, RD.Int.mag(M.e1(p, xh, yl))) == False{} : Bool}, +h2: {RD.Nat.lt(k2, RD.Int.mag(M.e2(p, xl, yh))) == False{} : Bool},
  +h3: {RD.Nat.lt(k3, RD.Int.mag(M.e3(p, xh, xl, yh, yl))) == False{} : Bool}, +h4: {RD.Nat.lt(k4, RD.Int.mag(M.e4(p, xh, xl, yh, yl))) == False{} : Bool},
  +hx: {RD.Nat.lt(kx, RD.Int.mag(I.Int.neg(I.Int.mul(xl, yl)))) == False{} : Bool})
  -> {RD.Nat.lt(Nat.add(Nat.add(Nat.add(k1, k2), Nat.add(k3, k4)), kx), RD.Int.mag(M.eta(p, xh, xl, yh, yl))) == False{} : Bool}:
  +e1 = M.e1(p, xh, yl)
  +e2 = M.e2(p, xl, yh)
  +e3 = M.e3(p, xh, xl, yh, yl)
  +e4 = M.e4(p, xh, xl, yh, yl)
  +sum = I.Int.add(I.Int.add(I.Int.add(e1, e2), I.Int.add(e3, e4)), I.Int.neg(I.Int.mul(xl, yl)))
  +b : {RD.Nat.lt(Nat.add(Nat.add(Nat.add(k1, k2), Nat.add(k3, k4)), kx), RD.Int.mag(sum)) == False{} : Bool} =
    Tri2(I.Int.add(I.Int.add(e1, e2), I.Int.add(e3, e4)), I.Int.neg(I.Int.mul(xl, yl)), Nat.add(Nat.add(k1, k2), Nat.add(k3, k4)), kx,
      Tri2(I.Int.add(e1, e2), I.Int.add(e3, e4), Nat.add(k1, k2), Nat.add(k3, k4), Tri2(e1, e2, k1, k2, h1, h2), Tri2(e3, e4, k3, k4, h3, h4)), hx)
  Equal.trans(Bool, RD.Nat.lt(Nat.add(Nat.add(Nat.add(k1, k2), Nat.add(k3, k4)), kx), RD.Int.mag(M.eta(p, xh, xl, yh, yl))), RD.Nat.lt(Nat.add(Nat.add(Nat.add(k1, k2), Nat.add(k3, k4)), kx), RD.Int.mag(sum)), False{},
    Equal.cong(I.Int, Bool, z => RD.Nat.lt(Nat.add(Nat.add(Nat.add(k1, k2), Nat.add(k3, k4)), kx), RD.Int.mag(z)), M.eta(p, xh, xl, yh, yl), sum, M.eta.split(p, xh, xl, yh, yl, hz)), b)

def Er1.le(+p1: Nat, +D: Nat, +A: Nat, +yl: I.Int, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(Nat.add(D, D)), RD.Int.mag(M.e1(1n+p1, XH(A, D), yl))) == False{} : Bool}:
  Et.le(p1, D, I.Int.mul(XH(A, D), yl), P1.le(p1, D, A, yl, hA, hy))

def Er2.le(+p1: Nat, +D: Nat, +B: Nat, +xl: I.Int, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(Nat.add(D, D)), RD.Int.mag(M.e2(1n+p1, xl, XH(B, D)))) == False{} : Bool}:
  Et.le(p1, D, I.Int.mul(xl, XH(B, D)), P2.le(p1, D, B, xl, hB, hx))

# Lower bounds on |x|
# -------------------

# |xh + xl| + 2^D >= xh
def X.lo(+A: Nat, +D: Nat, +xl: I.Int, +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool})
  -> {RD.Nat.lt(Nat.add(RD.Int.mag(I.Int.add(XH(A, D), xl)), RD.Nat.pow2(D)), Nat.mul(A, RD.Nat.pow2(1n+D))) == False{} : Bool}:
  +a = Nat.mul(A, RD.Nat.pow2(1n+D))
  +X = I.Int.add(XH(A, D), xl)
  +env : List<&2, I.Int> = [XH(A, D), xl]
  +e : {XH(A, D) == I.Int.add(X, I.Int.neg(xl)) : I.Int} = BP.IntN(env, R.V(0n), R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(1n))), [], [], {==}, Unit{})
  +t : {RD.Nat.lt(Nat.add(RD.Int.mag(X), RD.Int.mag(I.Int.neg(xl))), a) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Nat.add(RD.Int.mag(X), RD.Int.mag(I.Int.neg(xl))), a), RD.Nat.lt(Nat.add(RD.Int.mag(X), RD.Int.mag(I.Int.neg(xl))), RD.Int.mag(I.Int.add(X, I.Int.neg(xl)))), False{},
    Equal.cong(I.Int, Bool, z => RD.Nat.lt(Nat.add(RD.Int.mag(X), RD.Int.mag(I.Int.neg(xl))), RD.Int.mag(z)), XH(A, D), I.Int.add(X, I.Int.neg(xl)), e), E2.Mag.tri(X, I.Int.neg(xl)))
  E.Le.trans(a, Nat.add(RD.Int.mag(X), RD.Int.mag(I.Int.neg(xl))), Nat.add(RD.Int.mag(X), RD.Nat.pow2(D)), t,
    E2.Le.addl(RD.Int.mag(X), RD.Int.mag(I.Int.neg(xl)), RD.Nat.pow2(D), Equal.trans(Bool, RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(I.Int.neg(xl))), RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(RD.Nat.pow2(D), z), RD.Int.mag(I.Int.neg(xl)), RD.Int.mag(xl), E.Mag.neg(xl)), hx)))

# c 2^D <= |x| when c + 1 <= 2A
def X.lo.c(+A: Nat, +D: Nat, +xl: I.Int, +c: Nat, +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hc: {RD.Nat.lt(Nat.double(A), 1n+c) == False{} : Bool})
  -> {RD.Nat.lt(RD.Int.mag(I.Int.add(XH(A, D), xl)), Nat.mul(c, RD.Nat.pow2(D))) == False{} : Bool}:
  +W = RD.Nat.pow2(D)
  +M = RD.Int.mag(I.Int.add(XH(A, D), xl))
  +ea : {Nat.mul(Nat.double(A), W) == Nat.mul(A, RD.Nat.pow2(1n+D)) : Nat} = Equal.trans(Nat, Nat.mul(Nat.double(A), W), Nat.double(Nat.mul(A, W)), Nat.mul(A, RD.Nat.pow2(1n+D)), BP.Mul.dbl_l(A, W), Equal.sym(Nat, Nat.mul(A, Nat.double(W)), Nat.double(Nat.mul(A, W)), R.Nat.mul_double(A, W)))
  +l1 : {RD.Nat.lt(Nat.add(M, W), Nat.add(W, Nat.mul(c, W))) == False{} : Bool} = E.Le.trans(Nat.mul(1n+c, W), Nat.mul(Nat.double(A), W), Nat.add(M, W), E2.Le.mulr(1n+c, Nat.double(A), W, hc),
    E.Le.trans(Nat.mul(Nat.double(A), W), Nat.mul(A, RD.Nat.pow2(1n+D)), Nat.add(M, W), E.Le.eq(Nat.mul(Nat.double(A), W), Nat.mul(A, RD.Nat.pow2(1n+D)), ea), X.lo(A, D, xl, hx)))
  E2.Le.canl(W, Nat.mul(c, W), M, E.Le.trans(Nat.add(W, Nat.mul(c, W)), Nat.add(M, W), Nat.add(W, M), l1, E.Le.eq(Nat.add(M, W), Nat.add(W, M), NL.Nat.add_comm(M, W))))

# |xh + xl| <= xh + 2^D
def X.hi(+A: Nat, +D: Nat, +xl: I.Int, +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool})
  -> {RD.Nat.lt(Nat.add(Nat.mul(A, RD.Nat.pow2(1n+D)), RD.Nat.pow2(D)), RD.Int.mag(I.Int.add(XH(A, D), xl))) == False{} : Bool}:
  Tri2(XH(A, D), xl, Nat.mul(A, RD.Nat.pow2(1n+D)), RD.Nat.pow2(D), P4.Lt.irr(Nat.mul(A, RD.Nat.pow2(1n+D))), hx)


# xh yh >= 2: 9u² (1 + 2^p)² <= 5 |x y|
# -------------------------------------
# From |x| + u >= xh = 2A u, |x| <= xh + u (and the same for y), A B >=
# 2^p 2^(p-1) and A, B < 2^p: 5 |x y| + (10A + 10B + 15) u² >= 20 A B u²
# >= 10 P² u² >= (9 (P + 1)² + 10A + 10B + 15) u² once P >= 64.

def Big.num(+X: Nat, +Y: Nat, +W: Nat, +A: Nat, +B: Nat, +H: Nat,
  +f1: {RD.Nat.lt(Nat.add(X, W), Nat.mul(A, Nat.double(W))) == False{} : Bool}, +f2: {RD.Nat.lt(Nat.add(Y, W), Nat.mul(B, Nat.double(W))) == False{} : Bool},
  +f3: {RD.Nat.lt(Nat.add(Nat.mul(A, Nat.double(W)), W), X) == False{} : Bool}, +f4: {RD.Nat.lt(Nat.add(Nat.mul(B, Nat.double(W)), W), Y) == False{} : Bool},
  +f5: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(Nat.double(H), H)) == False{} : Bool},
  +f6: {RD.Nat.lt(Nat.double(H), 1n+A) == False{} : Bool}, +f7: {RD.Nat.lt(Nat.double(H), 1n+B) == False{} : Bool}, +f8: {RD.Nat.lt(Nat.double(H), 64n) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, Nat.mul(X, Y)), Nat.mul(Nat.mul(9n, Nat.mul(W, W)), Nat.mul(1n+Nat.double(H), 1n+Nat.double(H)))) == False{} : Bool}:
  +W2 = Nat.double(W)
  +V = Nat.mul(W, W)
  +P = Nat.double(H)
  +Q = Nat.mul(1n+P, 1n+P)
  +eV : {V == Nat.mul(W, W) : Nat} = {==}
  +eW2 : {W2 == Nat.add(W, W) : Nat} = Y.Nat.double_add(W)
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +eQ : {Q == 1n+Nat.add(P, Nat.add(P, Nat.mul(P, P))) : Nat} = Equal.cong(Nat, Nat, z => 1n+Nat.add(P, z), Nat.mul(P, 1n+P), Nat.add(P, Nat.mul(P, P)), NL.Nat.mul_succ_r(P, P))
  +eoV : {Nat.mul(1n, V) == V : Nat} = P3.Mul.one_l(V)
  +eoW : {Nat.mul(1n, Nat.mul(W, W)) == Nat.mul(W, W) : Nat} = P3.Mul.one_l(Nat.mul(W, W))
  +env : List<&2, Nat> = [X, Y, W, V, A, B, P, H, Q, W2, 1n]
  +AW = Nat.mul(A, W2)
  +BW = Nat.mul(B, W2)
  +XY = Nat.mul(X, Y)
  +T0 = Nat.add(Nat.mul(W, X), Nat.add(Nat.mul(W, Y), V))
  +T1 = Nat.add(Nat.mul(W, Nat.add(AW, W)), Nat.add(Nat.mul(W, Nat.add(BW, W)), V))
  +L1 : {RD.Nat.lt(Nat.mul(Nat.add(X, W), Nat.add(Y, W)), Nat.mul(AW, BW)) == False{} : Bool} = E2.Le.mul2(AW, Nat.add(X, W), BW, Nat.add(Y, W), f1, f2)
  +E1 : {Nat.mul(Nat.add(X, W), Nat.add(Y, W)) == Nat.add(XY, T0) : Nat} = R.NatN.eq2(env, R.Ml(R.Ad(R.V(0n), R.V(2n)), R.Ad(R.V(1n), R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(2n), R.V(0n)), R.Ad(R.Ml(R.V(2n), R.V(1n)), R.V(3n)))), [], [], [R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.V(3n)))], {==}, Unit{}, (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.V(3n), {==}, {==}, Equal.sym(Nat, V, Nat.mul(W, W), eV)), Unit{}), {==}, {==})
  +L2 : {RD.Nat.lt(T1, T0) == False{} : Bool} = E2.Le.add2(Nat.mul(W, X), Nat.mul(W, Nat.add(AW, W)), Nat.add(Nat.mul(W, Y), V), Nat.add(Nat.mul(W, Nat.add(BW, W)), V), E2.Le.mull(W, X, Nat.add(AW, W), f3), E2.Le.add2(Nat.mul(W, Y), Nat.mul(W, Nat.add(BW, W)), V, V, E2.Le.mull(W, Y, Nat.add(BW, W), f4), P4.Lt.irr(V)))
  +L3 : {RD.Nat.lt(Nat.add(XY, T1), Nat.mul(AW, BW)) == False{} : Bool} = E.Le.trans(Nat.mul(AW, BW), Nat.mul(Nat.add(X, W), Nat.add(Y, W)), Nat.add(XY, T1), L1, E.Le.trans(Nat.mul(Nat.add(X, W), Nat.add(Y, W)), Nat.add(XY, T0), Nat.add(XY, T1), E.Le.eq(Nat.mul(Nat.add(X, W), Nat.add(Y, W)), Nat.add(XY, T0), E1), E2.Le.addl(XY, T0, T1, L2)))
  +L4 : {RD.Nat.lt(Nat.mul(5n, Nat.add(XY, T1)), Nat.mul(5n, Nat.mul(AW, BW))) == False{} : Bool} = E2.Le.mull(5n, Nat.mul(AW, BW), Nat.add(XY, T1), L3)
  +Eab : {Nat.mul(AW, BW) == Nat.mul(Nat.mul(A, B), Nat.mul(W2, W2)) : Nat} = R.NatN.eq(env, R.Ml(R.Ml(R.V(4n), R.V(9n)), R.Ml(R.V(5n), R.V(9n))), R.Ml(R.Ml(R.V(4n), R.V(5n)), R.Ml(R.V(9n), R.V(9n))), [], [], {==}, Unit{}, {==}, {==})
  +L5 : {RD.Nat.lt(Nat.mul(5n, Nat.mul(AW, BW)), Nat.mul(5n, Nat.mul(Nat.mul(P, H), Nat.mul(W2, W2)))) == False{} : Bool} = E2.Le.mull(5n, Nat.mul(Nat.mul(P, H), Nat.mul(W2, W2)), Nat.mul(AW, BW), E.Le.trans(Nat.mul(Nat.mul(P, H), Nat.mul(W2, W2)), Nat.mul(Nat.mul(A, B), Nat.mul(W2, W2)), Nat.mul(AW, BW), E2.Le.mulr(Nat.mul(P, H), Nat.mul(A, B), Nat.mul(W2, W2), f5), E.Le.eq(Nat.mul(Nat.mul(A, B), Nat.mul(W2, W2)), Nat.mul(AW, BW), Equal.sym(Nat, Nat.mul(AW, BW), Nat.mul(Nat.mul(A, B), Nat.mul(W2, W2)), Eab))))
  +R10 = Nat.add(Nat.mul(10n, A), Nat.add(Nat.mul(10n, B), 15n))
  +NQ = Nat.add(Nat.mul(9n, Q), R10)
  +B9 = Nat.add(Nat.mul(9n, Nat.mul(P, P)), Nat.add(Nat.mul(18n, P), 9n))
  +RA = Nat.add(Nat.mul(10n, 1n+A), Nat.add(Nat.mul(10n, 1n+B), 15n))
  +RP = Nat.add(Nat.mul(10n, P), Nat.add(Nat.mul(10n, P), 15n))
  +C38 = Nat.add(Nat.mul(9n, Nat.mul(P, P)), Nat.add(Nat.mul(38n, P), 4n))
  +PH20 = Nat.mul(20n, Nat.mul(P, H))
  +N1 : {Nat.add(NQ, 20n) == Nat.add(B9, RA) : Nat} = R.NatN.eq2(env, R.Ad(R.Ad(R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), N.TZero{}))))))))), R.Ad(R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), N.TZero{})))))))))), R.Ad(R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), N.TZero{})))))))))), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), N.TZero{})))))))))))))))))), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), N.TZero{}))))))))))))))))))))), R.Ad(R.Ad(R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), N.TZero{}))))))))), R.Ad(R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), N.TZero{})))))))))))))))))), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), N.TZero{}))))))))))), R.Ad(R.Ad(R.Ad(R.V(10n), R.V(4n)), R.Ad(R.Ad(R.V(10n), R.V(4n)), R.Ad(R.Ad(R.V(10n), R.V(4n)), R.Ad(R.Ad(R.V(10n), R.V(4n)), R.Ad(R.Ad(R.V(10n), R.V(4n)), R.Ad(R.Ad(R.V(10n), R.V(4n)), R.Ad(R.Ad(R.V(10n), R.V(4n)), R.Ad(R.Ad(R.V(10n), R.V(4n)), R.Ad(R.Ad(R.V(10n), R.V(4n)), R.Ad(R.Ad(R.V(10n), R.V(4n)), N.TZero{})))))))))), R.Ad(R.Ad(R.Ad(R.V(10n), R.V(5n)), R.Ad(R.Ad(R.V(10n), R.V(5n)), R.Ad(R.Ad(R.V(10n), R.V(5n)), R.Ad(R.Ad(R.V(10n), R.V(5n)), R.Ad(R.Ad(R.V(10n), R.V(5n)), R.Ad(R.Ad(R.V(10n), R.V(5n)), R.Ad(R.Ad(R.V(10n), R.V(5n)), R.Ad(R.Ad(R.V(10n), R.V(5n)), R.Ad(R.Ad(R.V(10n), R.V(5n)), R.Ad(R.Ad(R.V(10n), R.V(5n)), N.TZero{})))))))))), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), N.TZero{})))))))))))))))))), [], [], [R.Ad(R.V(8n), R.Ng(R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))))), R.Ad(R.V(8n), R.Ng(R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))))), R.Ad(R.V(8n), R.Ng(R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))))), R.Ad(R.V(8n), R.Ng(R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))))), R.Ad(R.V(8n), R.Ng(R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))))), R.Ad(R.V(8n), R.Ng(R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))))), R.Ad(R.V(8n), R.Ng(R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))))), R.Ad(R.V(8n), R.Ng(R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))))), R.Ad(R.V(8n), R.Ng(R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n)))))))], {==}, Unit{}, (R.NatN.z(env, R.V(8n), R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))), {==}, {==}, eQ), (R.NatN.z(env, R.V(8n), R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))), {==}, {==}, eQ), (R.NatN.z(env, R.V(8n), R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))), {==}, {==}, eQ), (R.NatN.z(env, R.V(8n), R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))), {==}, {==}, eQ), (R.NatN.z(env, R.V(8n), R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))), {==}, {==}, eQ), (R.NatN.z(env, R.V(8n), R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))), {==}, {==}, eQ), (R.NatN.z(env, R.V(8n), R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))), {==}, {==}, eQ), (R.NatN.z(env, R.V(8n), R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))), {==}, {==}, eQ), (R.NatN.z(env, R.V(8n), R.Ad(R.V(10n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ml(R.V(6n), R.V(6n))))), {==}, {==}, eQ), Unit{}))))))))), {==}, {==})
  +L6 : {RD.Nat.lt(Nat.add(B9, RP), Nat.add(B9, RA)) == False{} : Bool} = E2.Le.addl(B9, RA, RP, E2.Le.add2(Nat.mul(10n, 1n+A), Nat.mul(10n, P), Nat.add(Nat.mul(10n, 1n+B), 15n), Nat.add(Nat.mul(10n, P), 15n), E2.Le.mull(10n, 1n+A, P, f6), E2.Le.addr(Nat.mul(10n, 1n+B), Nat.mul(10n, P), 15n, E2.Le.mull(10n, 1n+B, P, f7))))
  +N2 : {Nat.add(B9, RP) == Nat.add(C38, 20n) : Nat} = R.NatN.eq(env, R.Ad(R.Ad(R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), N.TZero{}))))))))), R.Ad(R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), N.TZero{})))))))))))))))))), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), N.TZero{}))))))))))), R.Ad(R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), N.TZero{})))))))))), R.Ad(R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), N.TZero{})))))))))), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), N.TZero{})))))))))))))))))), R.Ad(R.Ad(R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), N.TZero{}))))))))), R.Ad(R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), N.TZero{})))))))))))))))))))))))))))))))))))))), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), N.TZero{})))))), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), N.TZero{}))))))))))))))))))))), [], [], {==}, Unit{}, {==}, {==})
  +N4 : {Nat.mul(64n, P) == Nat.add(Nat.mul(38n, P), Nat.mul(26n, P)) : Nat} = R.NatN.eq(env, R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), N.TZero{})))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), R.Ad(R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), N.TZero{})))))))))))))))))))))))))))))))))))))), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), R.Ad(R.V(6n), N.TZero{}))))))))))))))))))))))))))), [], [], {==}, Unit{}, {==}, {==})
  +L7a : {RD.Nat.lt(Nat.mul(26n, P), 4n) == False{} : Bool} = E.Le.trans(4n, Nat.mul(26n, 64n), Nat.mul(26n, P), {==}, E2.Le.mull(26n, 64n, P, f8))
  +L7 : {RD.Nat.lt(Nat.mul(P, P), Nat.add(Nat.mul(38n, P), 4n)) == False{} : Bool} = E.Le.trans(Nat.add(Nat.mul(38n, P), 4n), Nat.mul(64n, P), Nat.mul(P, P), E.Le.trans(Nat.add(Nat.mul(38n, P), 4n), Nat.add(Nat.mul(38n, P), Nat.mul(26n, P)), Nat.mul(64n, P), E2.Le.addl(Nat.mul(38n, P), 4n, Nat.mul(26n, P), L7a), E.Le.eq(Nat.add(Nat.mul(38n, P), Nat.mul(26n, P)), Nat.mul(64n, P), Equal.sym(Nat, Nat.mul(64n, P), Nat.add(Nat.mul(38n, P), Nat.mul(26n, P)), N4))), E2.Le.mulr(64n, P, P, f8))
  +N3 : {Nat.add(Nat.mul(9n, Nat.mul(P, P)), Nat.mul(P, P)) == PH20 : Nat} = R.NatN.eq(env, R.Ad(R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), R.Ad(R.Ml(R.V(6n), R.V(6n)), N.TZero{}))))))))), R.Ml(R.V(6n), R.V(6n))), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), N.TZero{})))))))))))))))))))), [R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.V(6n), R.V(6n)), R.V(6n)), R.V(6n)), R.V(6n)), R.V(6n)), R.V(6n)), R.V(6n)), R.V(6n)), R.V(6n))], [R.Ad(R.V(6n), R.Ng(R.Ad(R.V(7n), R.V(7n))))], {==}, (R.NatN.z(env, R.V(6n), R.Ad(R.V(7n), R.V(7n)), {==}, {==}, eP), Unit{}), {==}, {==})
  +L8 : {RD.Nat.lt(Nat.add(PH20, 20n), Nat.add(NQ, 20n)) == False{} : Bool} = E.Le.trans(Nat.add(NQ, 20n), Nat.add(B9, RP), Nat.add(PH20, 20n), E.Le.trans(Nat.add(NQ, 20n), Nat.add(B9, RA), Nat.add(B9, RP), E.Le.eq(Nat.add(NQ, 20n), Nat.add(B9, RA), N1), L6), E.Le.trans(Nat.add(B9, RP), Nat.add(C38, 20n), Nat.add(PH20, 20n), E.Le.eq(Nat.add(B9, RP), Nat.add(C38, 20n), N2), E2.Le.addr(C38, PH20, 20n, E.Le.trans(C38, Nat.add(Nat.mul(9n, Nat.mul(P, P)), Nat.mul(P, P)), PH20, E2.Le.addl(Nat.mul(9n, Nat.mul(P, P)), Nat.add(Nat.mul(38n, P), 4n), Nat.mul(P, P), L7), E.Le.eq(Nat.add(Nat.mul(9n, Nat.mul(P, P)), Nat.mul(P, P)), PH20, N3)))))
  +L9 : {RD.Nat.lt(PH20, NQ) == False{} : Bool} = E2.Le.canl(20n, NQ, PH20, E.Le.trans(Nat.add(20n, NQ), Nat.add(NQ, 20n), Nat.add(20n, PH20), E.Le.eq(Nat.add(20n, NQ), Nat.add(NQ, 20n), NL.Nat.add_comm(20n, NQ)), E.Le.trans(Nat.add(NQ, 20n), Nat.add(PH20, 20n), Nat.add(20n, PH20), L8, E.Le.eq(Nat.add(PH20, 20n), Nat.add(20n, PH20), NL.Nat.add_comm(PH20, 20n)))))
  +Ep : {Nat.mul(5n, Nat.mul(Nat.mul(P, H), Nat.mul(W2, W2))) == Nat.mul(PH20, V) : Nat} = R.NatN.eq(env, R.Ad(R.Ml(R.Ml(R.V(6n), R.V(7n)), R.Ml(R.V(9n), R.V(9n))), R.Ad(R.Ml(R.Ml(R.V(6n), R.V(7n)), R.Ml(R.V(9n), R.V(9n))), R.Ad(R.Ml(R.Ml(R.V(6n), R.V(7n)), R.Ml(R.V(9n), R.V(9n))), R.Ad(R.Ml(R.Ml(R.V(6n), R.V(7n)), R.Ml(R.V(9n), R.V(9n))), R.Ad(R.Ml(R.Ml(R.V(6n), R.V(7n)), R.Ml(R.V(9n), R.V(9n))), N.TZero{}))))), R.Ml(R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), R.Ad(R.Ml(R.V(6n), R.V(7n)), N.TZero{})))))))))))))))))))), R.V(3n)), [R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.Ml(R.V(2n), R.V(6n)), R.V(7n)), R.Ml(R.Ml(R.V(2n), R.V(6n)), R.V(7n))), R.Ml(R.Ml(R.V(2n), R.V(6n)), R.V(7n))), R.Ml(R.Ml(R.V(2n), R.V(6n)), R.V(7n))), R.Ml(R.Ml(R.V(2n), R.V(6n)), R.V(7n))), R.Ml(R.Ml(R.V(2n), R.V(6n)), R.V(7n))), R.Ml(R.Ml(R.V(2n), R.V(6n)), R.V(7n))), R.Ml(R.Ml(R.V(2n), R.V(6n)), R.V(7n))), R.Ml(R.Ml(R.V(2n), R.V(6n)), R.V(7n))), R.Ml(R.Ml(R.V(2n), R.V(6n)), R.V(7n))), R.Ml(R.Ml(R.V(6n), R.V(7n)), R.V(9n))), R.Ml(R.Ml(R.V(6n), R.V(7n)), R.V(9n))), R.Ml(R.Ml(R.V(6n), R.V(7n)), R.V(9n))), R.Ml(R.Ml(R.V(6n), R.V(7n)), R.V(9n))), R.Ml(R.Ml(R.V(6n), R.V(7n)), R.V(9n))), R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ng(R.Ml(R.V(6n), R.V(7n))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n)))), R.Ng(R.Ml(R.V(6n), R.V(7n))))], [R.Ad(R.V(9n), R.Ng(R.Ad(R.V(2n), R.V(2n)))), R.Ad(R.V(3n), R.Ng(R.Ml(R.V(2n), R.V(2n))))], {==}, (R.NatN.z(env, R.V(9n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, eW2), (R.NatN.z(env, R.V(3n), R.Ml(R.V(2n), R.V(2n)), {==}, {==}, eV), Unit{})), {==}, {==})
  +En : {Nat.mul(NQ, V) == Nat.add(Nat.mul(Nat.mul(9n, Q), V), Nat.mul(R10, V)) : Nat} = R.NatN.eq(env, R.Ml(R.Ad(R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), N.TZero{}))))))))), R.Ad(R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), N.TZero{})))))))))), R.Ad(R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), N.TZero{})))))))))), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), N.TZero{})))))))))))))))))), R.V(3n)), R.Ad(R.Ml(R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), N.TZero{}))))))))), R.V(3n)), R.Ml(R.Ad(R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), N.TZero{})))))))))), R.Ad(R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), N.TZero{})))))))))), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), N.TZero{}))))))))))))))))), R.V(3n))), [], [], {==}, Unit{}, {==}, {==})
  +Et : {Nat.mul(5n, T1) == Nat.mul(R10, V) : Nat} = R.NatN.eq2(env, R.Ad(R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n))), R.Ad(R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n))), R.Ad(R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n))), R.Ad(R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n))), R.Ad(R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n))), N.TZero{}))))), R.Ml(R.Ad(R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), N.TZero{})))))))))), R.Ad(R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), R.Ad(R.V(5n), N.TZero{})))))))))), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), R.Ad(R.V(10n), N.TZero{}))))))))))))))))), R.V(3n)), [R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.V(2n), R.V(4n)), R.Ml(R.V(2n), R.V(4n))), R.Ml(R.V(2n), R.V(4n))), R.Ml(R.V(2n), R.V(4n))), R.Ml(R.V(2n), R.V(4n))), R.Ml(R.V(2n), R.V(5n))), R.Ml(R.V(2n), R.V(5n))), R.Ml(R.V(2n), R.V(5n))), R.Ml(R.V(2n), R.V(5n))), R.Ml(R.V(2n), R.V(5n))), R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ng(R.V(4n)), R.Ng(R.V(4n))), R.Ng(R.V(4n))), R.Ng(R.V(4n))), R.Ng(R.V(4n))), R.Ng(R.V(4n))), R.Ng(R.V(4n))), R.Ng(R.V(4n))), R.Ng(R.V(4n))), R.Ng(R.V(4n))), R.Ng(R.V(5n))), R.Ng(R.V(5n))), R.Ng(R.V(5n))), R.Ng(R.V(5n))), R.Ng(R.V(5n))), R.Ng(R.V(5n))), R.Ng(R.V(5n))), R.Ng(R.V(5n))), R.Ng(R.V(5n))), R.Ng(R.V(5n))), R.Ng(R.V(10n))), R.Ng(R.V(10n))), R.Ng(R.V(10n))), R.Ng(R.V(10n))), R.Ng(R.V(10n))), R.Ng(R.V(10n))), R.Ng(R.V(10n))), R.Ng(R.V(10n))), R.Ng(R.V(10n))), R.Ng(R.V(10n))), R.Ng(R.V(10n))), R.Ng(R.V(10n))), R.Ng(R.V(10n))), R.Ng(R.V(10n))), R.Ng(R.V(10n)))], [R.Ad(R.V(9n), R.Ng(R.Ad(R.V(2n), R.V(2n)))), R.Ad(R.V(3n), R.Ng(R.Ml(R.V(2n), R.V(2n))))], [R.Ad(R.V(3n), R.Ng(R.Ml(R.V(2n), R.V(2n)))), R.Ad(R.V(3n), R.Ng(R.Ml(R.V(2n), R.V(2n)))), R.Ad(R.V(3n), R.Ng(R.Ml(R.V(2n), R.V(2n)))), R.Ad(R.V(3n), R.Ng(R.Ml(R.V(2n), R.V(2n)))), R.Ad(R.V(3n), R.Ng(R.Ml(R.V(2n), R.V(2n)))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))))), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ng(R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n)))))], {==}, (R.NatN.z(env, R.V(9n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, eW2), (R.NatN.z(env, R.V(3n), R.Ml(R.V(2n), R.V(2n)), {==}, {==}, eV), Unit{})), (R.NatN.z(env, R.V(3n), R.Ml(R.V(2n), R.V(2n)), {==}, {==}, eV), (R.NatN.z(env, R.V(3n), R.Ml(R.V(2n), R.V(2n)), {==}, {==}, eV), (R.NatN.z(env, R.V(3n), R.Ml(R.V(2n), R.V(2n)), {==}, {==}, eV), (R.NatN.z(env, R.V(3n), R.Ml(R.V(2n), R.V(2n)), {==}, {==}, eV), (R.NatN.z(env, R.V(3n), R.Ml(R.V(2n), R.V(2n)), {==}, {==}, eV), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), (R.NatN.z(env, R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(10n), R.Ml(R.V(2n), R.V(2n))), {==}, {==}, Equal.sym(Nat, Nat.mul(1n, Nat.mul(W, W)), Nat.mul(W, W), eoW)), Unit{})))))))))))))))))))), {==}, {==})
  +E5 : {Nat.mul(5n, Nat.add(XY, T1)) == Nat.add(Nat.mul(5n, XY), Nat.mul(5n, T1)) : Nat} = R.NatN.eq(env, R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n)))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n)))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n)))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n)))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n)))), N.TZero{}))))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(0n), R.V(1n)), N.TZero{}))))), R.Ad(R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n))), R.Ad(R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n))), R.Ad(R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n))), R.Ad(R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n))), R.Ad(R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(4n), R.V(9n)), R.V(2n))), R.Ad(R.Ml(R.V(2n), R.Ad(R.Ml(R.V(5n), R.V(9n)), R.V(2n))), R.V(3n))), N.TZero{})))))), [], [], {==}, Unit{}, {==}, {==})
  +Eq9 : {Nat.mul(Nat.mul(9n, V), Q) == Nat.mul(Nat.mul(9n, Q), V) : Nat} = R.NatN.eq(env, R.Ml(R.Ad(R.V(3n), R.Ad(R.V(3n), R.Ad(R.V(3n), R.Ad(R.V(3n), R.Ad(R.V(3n), R.Ad(R.V(3n), R.Ad(R.V(3n), R.Ad(R.V(3n), R.Ad(R.V(3n), N.TZero{}))))))))), R.V(8n)), R.Ml(R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), R.Ad(R.V(8n), N.TZero{}))))))))), R.V(3n)), [], [], {==}, Unit{}, {==}, {==})
  +Q9 = Nat.mul(Nat.mul(9n, Q), V)
  +T5 = Nat.mul(5n, T1)
  +G : {RD.Nat.lt(Nat.add(T5, Nat.mul(5n, XY)), Nat.add(T5, Q9)) == False{} : Bool} = E.Le.trans(Nat.add(T5, Q9), Nat.mul(NQ, V), Nat.add(T5, Nat.mul(5n, XY)), E.Le.eq(Nat.add(T5, Q9), Nat.mul(NQ, V), Equal.trans(Nat, Nat.add(T5, Q9), Nat.add(Q9, Nat.mul(R10, V)), Nat.mul(NQ, V), Equal.trans(Nat, Nat.add(T5, Q9), Nat.add(Q9, T5), Nat.add(Q9, Nat.mul(R10, V)), NL.Nat.add_comm(T5, Q9), Equal.cong(Nat, Nat, z => Nat.add(Q9, z), T5, Nat.mul(R10, V), Et)), Equal.sym(Nat, Nat.mul(NQ, V), Nat.add(Q9, Nat.mul(R10, V)), En))), E.Le.trans(Nat.mul(NQ, V), Nat.mul(PH20, V), Nat.add(T5, Nat.mul(5n, XY)), E2.Le.mulr(NQ, PH20, V, L9), E.Le.trans(Nat.mul(PH20, V), Nat.mul(5n, Nat.mul(AW, BW)), Nat.add(T5, Nat.mul(5n, XY)), E.Le.trans(Nat.mul(PH20, V), Nat.mul(5n, Nat.mul(Nat.mul(P, H), Nat.mul(W2, W2))), Nat.mul(5n, Nat.mul(AW, BW)), E.Le.eq(Nat.mul(PH20, V), Nat.mul(5n, Nat.mul(Nat.mul(P, H), Nat.mul(W2, W2))), Equal.sym(Nat, Nat.mul(5n, Nat.mul(Nat.mul(P, H), Nat.mul(W2, W2))), Nat.mul(PH20, V), Ep)), L5), E.Le.trans(Nat.mul(5n, Nat.mul(AW, BW)), Nat.mul(5n, Nat.add(XY, T1)), Nat.add(T5, Nat.mul(5n, XY)), L4, E.Le.eq(Nat.mul(5n, Nat.add(XY, T1)), Nat.add(T5, Nat.mul(5n, XY)), Equal.trans(Nat, Nat.mul(5n, Nat.add(XY, T1)), Nat.add(Nat.mul(5n, XY), T5), Nat.add(T5, Nat.mul(5n, XY)), E5, NL.Nat.add_comm(Nat.mul(5n, XY), T5)))))))
  E.Le.trans(Nat.mul(Nat.mul(9n, V), Q), Q9, Nat.mul(5n, XY), E.Le.eq(Nat.mul(Nat.mul(9n, V), Q), Q9, Eq9), E2.Le.canl(T5, Q9, Nat.mul(5n, XY), G))

def K9.eq(+D: Nat) -> {Nat.add(Nat.add(Nat.add(RD.Nat.pow2(Nat.add(D, D)), RD.Nat.pow2(Nat.add(D, D))), Nat.add(RD.Nat.pow2(1n+Nat.add(D, D)), RD.Nat.pow2(S4(D)))), RD.Nat.pow2(Nat.add(D, D))) == Nat.mul(9n, Nat.mul(RD.Nat.pow2(D), RD.Nat.pow2(D))) : Nat}:
  +V = RD.Nat.pow2(Nat.add(D, D))
  +V2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +V4 = RD.Nat.pow2(S4(D))
  +W = RD.Nat.pow2(D)
  +env : List<&2, Nat> = [V, V2, V4, W]
  +e2 : {V2 == Nat.add(V, V) : Nat} = Y.Nat.double_add(V)
  +e4 : {V4 == Nat.add(V2, V2) : Nat} = Y.Nat.double_add(V2)
  +ev : {V == Nat.mul(W, W) : Nat} = Vsq(D)
  R.NatN.eq2(env, R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.Ad(R.V(1n), R.V(2n))), R.V(0n)), R.Ad(R.Ml(R.V(3n), R.V(3n)), R.Ad(R.Ml(R.V(3n), R.V(3n)), R.Ad(R.Ml(R.V(3n), R.V(3n)), R.Ad(R.Ml(R.V(3n), R.V(3n)), R.Ad(R.Ml(R.V(3n), R.V(3n)), R.Ad(R.Ml(R.V(3n), R.V(3n)), R.Ad(R.Ml(R.V(3n), R.V(3n)), R.Ad(R.Ml(R.V(3n), R.V(3n)), R.Ad(R.Ml(R.V(3n), R.V(3n)), N.TZero{}))))))))), [], [], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.V(1n), R.V(1n)))), R.Ad(R.V(0n), R.Ng(R.Ml(R.V(3n), R.V(3n)))), R.Ad(R.V(0n), R.Ng(R.Ml(R.V(3n), R.V(3n)))), R.Ad(R.V(0n), R.Ng(R.Ml(R.V(3n), R.V(3n)))), R.Ad(R.V(0n), R.Ng(R.Ml(R.V(3n), R.V(3n)))), R.Ad(R.V(0n), R.Ng(R.Ml(R.V(3n), R.V(3n)))), R.Ad(R.V(0n), R.Ng(R.Ml(R.V(3n), R.V(3n)))), R.Ad(R.V(0n), R.Ng(R.Ml(R.V(3n), R.V(3n)))), R.Ad(R.V(0n), R.Ng(R.Ml(R.V(3n), R.V(3n)))), R.Ad(R.V(0n), R.Ng(R.Ml(R.V(3n), R.V(3n))))], {==}, Unit{}, (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, e2), (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, e2), (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, e2), (R.NatN.z(env, R.V(2n), R.Ad(R.V(1n), R.V(1n)), {==}, {==}, e4), (R.NatN.z(env, R.V(0n), R.Ml(R.V(3n), R.V(3n)), {==}, {==}, ev), (R.NatN.z(env, R.V(0n), R.Ml(R.V(3n), R.V(3n)), {==}, {==}, ev), (R.NatN.z(env, R.V(0n), R.Ml(R.V(3n), R.V(3n)), {==}, {==}, ev), (R.NatN.z(env, R.V(0n), R.Ml(R.V(3n), R.V(3n)), {==}, {==}, ev), (R.NatN.z(env, R.V(0n), R.Ml(R.V(3n), R.V(3n)), {==}, {==}, ev), (R.NatN.z(env, R.V(0n), R.Ml(R.V(3n), R.V(3n)), {==}, {==}, ev), (R.NatN.z(env, R.V(0n), R.Ml(R.V(3n), R.V(3n)), {==}, {==}, ev), (R.NatN.z(env, R.V(0n), R.Ml(R.V(3n), R.V(3n)), {==}, {==}, ev), (R.NatN.z(env, R.V(0n), R.Ml(R.V(3n), R.V(3n)), {==}, {==}, ev), Unit{}))))))))))))), {==}, {==})

def Qp(+p1: Nat) -> Nat:
  Nat.mul(1n+RD.Nat.pow2(1n+p1), 1n+RD.Nat.pow2(1n+p1))

# the relative error, as |eta| (1 + 2^p)² <= 5 |x y|: 5u² / (1 + u)²
def Rel(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int) -> Bool:
  RD.Nat.lt(Nat.mul(5n, RD.Int.mag(I.Int.mul(I.Int.add(XH(A, D), xl), I.Int.add(XH(B, D), yl)))), Nat.mul(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)), Qp(p1)))

def Hp2(+p1: Nat, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool}) -> {RD.Nat.lt(p1, 2n) == False{} : Bool}:
  E.Le.trans(2n, 5n, p1, {==}, hp)

# |eta| <= 9u², and xh yh >= 2 makes it relative 5u² / (1 + u)²
def Case.big(+p1: Nat, +D: Nat, +A: Nat, +B: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hbig: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == False{} : Bool})
  -> {Rel(p1, A, B, D, xl, yl) == False{} : Bool}:
  +p : Nat = 1n+p1
  +xh = XH(A, D)
  +yh = XH(B, D)
  +W = RD.Nat.pow2(D)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +X = RD.Int.mag(I.Int.add(xh, xl))
  +Yv = RD.Int.mag(I.Int.add(yh, yl))
  +hz = Zx.exact(p1, A, B, D, xl, yl, Hp2(p1, hp), hA1, hA, hB1, hB, hx, hy)
  +K9 = Nat.add(Nat.add(Nat.add(V, V), Nat.add(RD.Nat.pow2(1n+Nat.add(D, D)), RD.Nat.pow2(S4(D)))), V)
  +he : {RD.Nat.lt(K9, RD.Int.mag(M.eta(p, xh, xl, yh, yl))) == False{} : Bool} = Eta.le(p, xh, xl, yh, yl, V, V, RD.Nat.pow2(1n+Nat.add(D, D)), RD.Nat.pow2(S4(D)), V, hz,
    Er1.le(p1, D, A, yl, hA, hy), Er2.le(p1, D, B, xl, hB, hx),
    E3.le(p1, D, I.Int.add(M.tl1(p, xh, yl), M.tl2(p, xl, yh)), Cl2.k2(p1, A, B, D, xl, yl, hA, hB, hx, hy)),
    E4.le(p1, D, I.Int.add(M.cl1(p, xh, yh), M.cl2(p, xh, xl, yh, yl)), C12.p8(p1, A, B, D, xl, yl, hA, hB, hx, hy)),
    XY.le(D, xl, yl, hx, hy))
  +h64 : {RD.Nat.lt(RD.Nat.pow2(1n+p1), 64n) == False{} : Bool} = E2.Pow2.mono(6n, 1n+p1, hp)
  +bn : {RD.Nat.lt(Nat.mul(5n, Nat.mul(X, Yv)), Nat.mul(Nat.mul(9n, Nat.mul(W, W)), Qp(p1))) == False{} : Bool} =
    Big.num(X, Yv, W, A, B, RD.Nat.pow2(p1), X.lo(A, D, xl, hx), X.lo(B, D, yl, hy), X.hi(A, D, xl, hx), X.hi(B, D, yl, hy), hbig,
      E2.Le.succ(A, RD.Nat.pow2(1n+p1), hA), E2.Le.succ(B, RD.Nat.pow2(1n+p1), hB), h64)
  +emag : {RD.Int.mag(I.Int.mul(I.Int.add(xh, xl), I.Int.add(yh, yl))) == Nat.mul(X, Yv) : Nat} = E2.Mag.mul(I.Int.add(xh, xl), I.Int.add(yh, yl))
  E.Le.trans(Nat.mul(RD.Int.mag(M.eta(p, xh, xl, yh, yl)), Qp(p1)), Nat.mul(K9, Qp(p1)), Nat.mul(5n, RD.Int.mag(I.Int.mul(I.Int.add(xh, xl), I.Int.add(yh, yl)))),
    E2.Le.mulr(RD.Int.mag(M.eta(p, xh, xl, yh, yl)), K9, Qp(p1), he),
    E.Le.trans(Nat.mul(K9, Qp(p1)), Nat.mul(Nat.mul(9n, Nat.mul(W, W)), Qp(p1)), Nat.mul(5n, RD.Int.mag(I.Int.mul(I.Int.add(xh, xl), I.Int.add(yh, yl)))),
      E.Le.eq(Nat.mul(K9, Qp(p1)), Nat.mul(Nat.mul(9n, Nat.mul(W, W)), Qp(p1)), Equal.cong(Nat, Nat, z => Nat.mul(z, Qp(p1)), K9, Nat.mul(9n, Nat.mul(W, W)), K9.eq(D))),
      E.Le.trans(Nat.mul(Nat.mul(9n, Nat.mul(W, W)), Qp(p1)), Nat.mul(5n, Nat.mul(X, Yv)), Nat.mul(5n, RD.Int.mag(I.Int.mul(I.Int.add(xh, xl), I.Int.add(yh, yl)))), bn,
        E.Le.eq(Nat.mul(5n, Nat.mul(X, Yv)), Nat.mul(5n, RD.Int.mag(I.Int.mul(I.Int.add(xh, xl), I.Int.add(yh, yl)))), Equal.cong(Nat, Nat, z => Nat.mul(5n, z), Nat.mul(X, Yv), RD.Int.mag(I.Int.mul(I.Int.add(xh, xl), I.Int.add(yh, yl))), Equal.sym(Nat, RD.Int.mag(I.Int.mul(I.Int.add(xh, xl), I.Int.add(yh, yl))), Nat.mul(X, Yv), emag)))))) 

# Small products: xh yh < 2
# -------------------------
# Muller and Rideau §2.6.2: the sub-cases on |cl2| and |tl1|, |tl2| need
# representable values above 2^(p-1) 2^k to be multiples of 2^k, exact
# sums of such multiples, and errors scaled finer than u².

def Pick.mul(b: Bool, +x: Nat, +y: Nat, +c: Nat) -> {Bool.pick(Nat, b, Nat.mul(x, c), Nat.mul(y, c)) == Nat.mul(Bool.pick(Nat, b, x, y), c) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the multiple of 2^k that Rn n is, once n >= 2^(p-1) 2^k
def Mq(+p1: Nat, +n: Nat, +k: Nat) -> Nat:
  +T = RD.Tr.of(1n+p1, n)
  Nat.mul(Bool.pick(Nat, RD.Tr.rup(T), 1n+RD.Tr.q(T), RD.Tr.q(T)), RD.Nat.pow2(RD.Nat.monus(RD.Tr.s(T), k)))

def Rn.mult(+p1: Nat, +n: Nat, +k: Nat, +h: {RD.Nat.lt(n, Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(k))) == False{} : Bool})
  -> {E.Rn(1n+p1, n) == Nat.mul(Mq(p1, n, k), RD.Nat.pow2(k)) : Nat}:
  +T = RD.Tr.of(1n+p1, n)
  +S = RD.Tr.s(T)
  +q = RD.Tr.q(T)
  +m = Bool.pick(Nat, RD.Tr.rup(T), 1n+q, q)
  +eS : {S == Nat.add(k, RD.Nat.monus(S, k)) : Nat} = E.Le.wit(k, S, E2.S4(p1, n, k, h))
  Equal.trans(Nat, E.Rn(1n+p1, n), Nat.mul(m, RD.Nat.pow2(S)), Nat.mul(Mq(p1, n, k), RD.Nat.pow2(k)),
    Pick.mul(RD.Tr.rup(T), 1n+q, q, RD.Nat.pow2(S)),
    E.Sh.mul(m, k, RD.Nat.monus(S, k), S, eS))

def Rep.mult(+p1: Nat, +n: Nat, +k: Nat, +fn: {E.Rn(1n+p1, n) == n : Nat}, +h: {RD.Nat.lt(n, Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(k))) == False{} : Bool})
  -> {n == Nat.mul(Mq(p1, n, k), RD.Nat.pow2(k)) : Nat}:
  Equal.trans(Nat, n, E.Rn(1n+p1, n), Nat.mul(Mq(p1, n, k), RD.Nat.pow2(k)), Equal.sym(Nat, E.Rn(1n+p1, n), n, fn), Rn.mult(p1, n, k, h))

def Rn.idem(+p1: Nat, +z: I.Int) -> {E.Rn(1n+p1, E.Rn(1n+p1, RD.Int.mag(z))) == E.Rn(1n+p1, RD.Int.mag(z)) : Nat}:
  +r = E.Rn(1n+p1, RD.Int.mag(z))
  +em : {RD.Int.mag(E.RNi(1n+p1, z)) == r : Nat} = Mag.sg(z, r)
  Equal.trans(Nat, E.Rn(1n+p1, r), E.Rn(1n+p1, RD.Int.mag(E.RNi(1n+p1, z))), r,
    Equal.cong(Nat, Nat, w => E.Rn(1n+p1, w), r, RD.Int.mag(E.RNi(1n+p1, z)), Equal.sym(Nat, RD.Int.mag(E.RNi(1n+p1, z)), r, em)),
    Equal.trans(Nat, E.Rn(1n+p1, RD.Int.mag(E.RNi(1n+p1, z))), RD.Int.mag(E.RNi(1n+p1, z)), r, Rf.i(p1, z), em))

# RN z = 2^k w once |RN z| >= 2^(p-1) 2^k
def Ri.sh(+p1: Nat, +z: I.Int, +k: Nat, +h: {RD.Nat.lt(E.Rn(1n+p1, RD.Int.mag(z)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(k))) == False{} : Bool})
  -> {E.RNi(1n+p1, z) == D.Int.sh(k, RD.Int.signed(z, Mq(p1, E.Rn(1n+p1, RD.Int.mag(z)), k))) : I.Int}:
  +r = E.Rn(1n+p1, RD.Int.mag(z))
  +m = Mq(p1, r, k)
  +er : {r == Nat.mul(m, RD.Nat.pow2(k)) : Nat} = Rep.mult(p1, r, k, Rn.idem(p1, z), h)
  Equal.trans(I.Int, RD.Int.signed(z, r), RD.Int.signed(z, Nat.mul(m, RD.Nat.pow2(k))), D.Int.sh(k, RD.Int.signed(z, m)),
    Equal.cong(Nat, I.Int, w => RD.Int.signed(z, w), r, Nat.mul(m, RD.Nat.pow2(k)), er),
    Equal.sym(I.Int, D.Int.sh(k, RD.Int.signed(z, m)), RD.Int.signed(z, Nat.mul(m, RD.Nat.pow2(k))), E.Sh.signed(k, z, m)))

# a sum of two multiples of 2^k is exact while it stays within 2^p 2^k
def Ex.sum(+p1: Nat, +k: Nat, +a: I.Int, +b: I.Int, +h: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(k)), RD.Int.mag(I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)))) == False{} : Bool})
  -> {E.RNi(1n+p1, I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b))) == I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)) : I.Int}:
  +z = I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b))
  +w = I.Int.add(a, b)
  +P = RD.Nat.pow2(1n+p1)
  +K = RD.Nat.pow2(k)
  +ez : {RD.Int.mag(z) == Nat.mul(RD.Int.mag(w), K) : Nat} = Equal.trans(Nat, RD.Int.mag(z), RD.Int.mag(D.Int.sh(k, w)), Nat.mul(RD.Int.mag(w), K),
    Equal.cong(I.Int, Nat, v => RD.Int.mag(v), z, D.Int.sh(k, w), Equal.sym(I.Int, D.Int.sh(k, w), z, Y.Int.sh_add(k, a, b))), E.Sh.mag(k, w))
  +hw : {RD.Nat.lt(P, RD.Int.mag(w)) == False{} : Bool} = E.Le.cancel(RD.Int.mag(w), P, K, BP.Pow2.pos(k),
    E.Le.trans(Nat.mul(RD.Int.mag(w), K), RD.Int.mag(z), Nat.mul(P, K), E.Le.eq(Nat.mul(RD.Int.mag(w), K), RD.Int.mag(z), Equal.sym(Nat, RD.Int.mag(z), Nat.mul(RD.Int.mag(w), K), ez)), h))
  E2.Px(p1, z, RD.Int.mag(w), k, ez, hw)

# an exact rounding has no error
def Err.z(+p: Nat, +c: I.Int, +e: {E.RNi(p, c) == c : I.Int}) -> {RD.Nat.lt(0n, RD.Int.mag(I.Int.add(E.RNi(p, c), I.Int.neg(c)))) == False{} : Bool}:
  +env : List<&2, I.Int> = [c]
  +e0 : {I.Int.add(c, I.Int.neg(c)) == I.IPos{0n} : I.Int} = BP.IntN(env, R.Ad(R.V(0n), R.Ng(R.V(0n))), N.TZero{}, [], [], {==}, Unit{})
  Equal.trans(Bool, RD.Nat.lt(0n, RD.Int.mag(I.Int.add(E.RNi(p, c), I.Int.neg(c)))), RD.Nat.lt(0n, RD.Int.mag(I.Int.add(c, I.Int.neg(c)))), False{},
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(0n, RD.Int.mag(I.Int.add(v, I.Int.neg(c)))), E.RNi(p, c), c, e),
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(0n, RD.Int.mag(v)), I.Int.add(c, I.Int.neg(c)), I.IPos{0n}, e0))

# |RN z| < c gives |z| < c, for c representable
def RL.c.go(+p1: Nat, +z: I.Int, +c: Nat, +fc: {E.Rn(1n+p1, c) == c : Nat}, +h: {RD.Nat.lt(RD.Int.mag(E.RNi(1n+p1, z)), c) == True{} : Bool}, l: Bool, +el: {RD.Nat.lt(RD.Int.mag(z), c) == l : Bool})
  -> {RD.Nat.lt(RD.Int.mag(z), c) == True{} : Bool}:
  match l:
    case True{}:
      el
    case False{}:
      B.Bool.tf({RD.Nat.lt(RD.Int.mag(z), c) == True{} : Bool}, Equal.trans(Bool, True{}, RD.Nat.lt(RD.Int.mag(E.RNi(1n+p1, z)), c), False{}, Equal.sym(Bool, RD.Nat.lt(RD.Int.mag(E.RNi(1n+p1, z)), c), True{}, h), RL(p1, z, c, fc, el)))

def RL.c(+p1: Nat, +z: I.Int, +c: Nat, +fc: {E.Rn(1n+p1, c) == c : Nat}, +h: {RD.Nat.lt(RD.Int.mag(E.RNi(1n+p1, z)), c) == True{} : Bool})
  -> {RD.Nat.lt(RD.Int.mag(z), c) == True{} : Bool}:
  RL.c.go(p1, z, c, fc, h, RD.Nat.lt(RD.Int.mag(z), c), {==})

# |Rn n - n| 2^t <= 2^s / 2 when n 2^t <= 2^p 2^s
def ErrS(+p1: Nat, +n: Nat, +s: Nat, +t: Nat, +h: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s)), Nat.mul(n, RD.Nat.pow2(t))) == False{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(s), Nat.double(Nat.mul(E.Dist(E.Rn(1n+p1, n), n), RD.Nat.pow2(t)))) == False{} : Bool}:
  +T = RD.Nat.pow2(t)
  +nt = Nat.mul(n, T)
  +ed : {E.Dist(E.Rn(1n+p1, nt), nt) == Nat.mul(E.Dist(E.Rn(1n+p1, n), n), T) : Nat} = Equal.trans(Nat, E.Dist(E.Rn(1n+p1, nt), nt), E.Dist(Nat.mul(E.Rn(1n+p1, n), T), nt), Nat.mul(E.Dist(E.Rn(1n+p1, n), n), T),
    Equal.cong(Nat, Nat, w => E.Dist(w, nt), E.Rn(1n+p1, nt), Nat.mul(E.Rn(1n+p1, n), T), Rn.sc(1n+p1, n, t)),
    E.Dist.mul(E.Rn(1n+p1, n), n, T))
  Equal.trans(Bool, RD.Nat.lt(RD.Nat.pow2(s), Nat.double(Nat.mul(E.Dist(E.Rn(1n+p1, n), n), T))), RD.Nat.lt(RD.Nat.pow2(s), Nat.double(E.Dist(E.Rn(1n+p1, nt), nt))), False{},
    Equal.cong(Nat, Bool, w => RD.Nat.lt(RD.Nat.pow2(s), Nat.double(w)), Nat.mul(E.Dist(E.Rn(1n+p1, n), n), T), E.Dist(E.Rn(1n+p1, nt), nt), Equal.sym(Nat, E.Dist(E.Rn(1n+p1, nt), nt), Nat.mul(E.Dist(E.Rn(1n+p1, n), n), T), ed)),
    ErrB(p1, nt, s, h))

def EBS(+p1: Nat, +z: I.Int, +s: Nat, +t: Nat, +h: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(s)), Nat.mul(RD.Int.mag(z), RD.Nat.pow2(t))) == False{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(s), Nat.double(Nat.mul(RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))), RD.Nat.pow2(t)))) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(RD.Nat.pow2(s), Nat.double(Nat.mul(RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))), RD.Nat.pow2(t)))), RD.Nat.lt(RD.Nat.pow2(s), Nat.double(Nat.mul(E.Dist(E.Rn(1n+p1, RD.Int.mag(z)), RD.Int.mag(z)), RD.Nat.pow2(t)))), False{},
    Equal.cong(Nat, Bool, w => RD.Nat.lt(RD.Nat.pow2(s), Nat.double(Nat.mul(w, RD.Nat.pow2(t)))), RD.Int.mag(I.Int.add(E.RNi(1n+p1, z), I.Int.neg(z))), E.Dist(E.Rn(1n+p1, RD.Int.mag(z)), RD.Int.mag(z)), Err.i(1n+p1, z)),
    ErrS(p1, RD.Int.mag(z), s, t, h))

# Lemma 2.10 of Muller and Rideau: H <= A, B and A B < 2 H² give A + Bn < 3 H
def L210.go(+A: Nat, +Bn: Nat, +H: Nat, +a: Nat, +b: Nat, +ea: {A == Nat.add(H, a) : Nat}, +eb: {Bn == Nat.add(H, b) : Nat},
  +hs: {RD.Nat.lt(Nat.mul(A, Bn), Nat.mul(Nat.double(H), H)) == True{} : Bool}, l: Bool, +el: {RD.Nat.lt(Nat.add(a, b), H) == l : Bool})
  -> {RD.Nat.lt(Nat.add(A, Bn), Nat.add(Nat.double(H), H)) == True{} : Bool}:
  match l:
    case True{}:
      +env : List<&2, Nat> = [H, a, b]
      +eH : {Nat.double(H) == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
      +e1 : {Nat.add(A, Bn) == Nat.add(Nat.add(H, a), Nat.add(H, b)) : Nat} = Equal.trans(Nat, Nat.add(A, Bn), Nat.add(Nat.add(H, a), Bn), Nat.add(Nat.add(H, a), Nat.add(H, b)),
        Equal.cong(Nat, Nat, w => Nat.add(w, Bn), A, Nat.add(H, a), ea), Equal.cong(Nat, Nat, w => Nat.add(Nat.add(H, a), w), Bn, Nat.add(H, b), eb))
      +e2 : {Nat.add(Nat.add(H, a), Nat.add(H, b)) == Nat.add(Nat.add(H, H), Nat.add(a, b)) : Nat} = R.NatN.eq(env, R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(0n), R.V(2n))), R.Ad(R.Ad(R.V(0n), R.V(0n)), R.Ad(R.V(1n), R.V(2n))), [], [], {==}, Unit{}, {==}, {==})
      +e : {Nat.add(A, Bn) == Nat.add(Nat.double(H), Nat.add(a, b)) : Nat} = Equal.trans(Nat, Nat.add(A, Bn), Nat.add(Nat.add(H, H), Nat.add(a, b)), Nat.add(Nat.double(H), Nat.add(a, b)),
        Equal.trans(Nat, Nat.add(A, Bn), Nat.add(Nat.add(H, a), Nat.add(H, b)), Nat.add(Nat.add(H, H), Nat.add(a, b)), e1, e2),
        Equal.cong(Nat, Nat, w => Nat.add(w, Nat.add(a, b)), Nat.add(H, H), Nat.double(H), Equal.sym(Nat, Nat.double(H), Nat.add(H, H), eH)))
      Equal.trans(Bool, RD.Nat.lt(Nat.add(A, Bn), Nat.add(Nat.double(H), H)), RD.Nat.lt(Nat.add(Nat.double(H), Nat.add(a, b)), Nat.add(Nat.double(H), H)), True{},
        Equal.cong(Nat, Bool, w => RD.Nat.lt(w, Nat.add(Nat.double(H), H)), Nat.add(A, Bn), Nat.add(Nat.double(H), Nat.add(a, b)), e),
        Equal.trans(Bool, RD.Nat.lt(Nat.add(Nat.double(H), Nat.add(a, b)), Nat.add(Nat.double(H), H)), RD.Nat.lt(Nat.add(a, b), H), True{}, BP.Lt.shift(Nat.double(H), Nat.add(a, b), H), el))
    case False{}:
      +env : List<&2, Nat> = [H, a, b]
      +eH : {Nat.double(H) == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
      +HH = Nat.mul(H, H)
      +e1 : {Nat.mul(A, Bn) == Nat.mul(Nat.add(H, a), Nat.add(H, b)) : Nat} = Equal.trans(Nat, Nat.mul(A, Bn), Nat.mul(Nat.add(H, a), Bn), Nat.mul(Nat.add(H, a), Nat.add(H, b)),
        Equal.cong(Nat, Nat, w => Nat.mul(w, Bn), A, Nat.add(H, a), ea), Equal.cong(Nat, Nat, w => Nat.mul(Nat.add(H, a), w), Bn, Nat.add(H, b), eb))
      +e2 : {Nat.mul(Nat.add(H, a), Nat.add(H, b)) == Nat.add(Nat.add(HH, Nat.mul(H, Nat.add(a, b))), Nat.mul(a, b)) : Nat} = R.NatN.eq(env,
        R.Ml(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(0n), R.V(2n))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ml(R.V(0n), R.Ad(R.V(1n), R.V(2n)))), R.Ml(R.V(1n), R.V(2n))), [], [], {==}, Unit{}, {==}, {==})
      +e3 : {Nat.mul(Nat.double(H), H) == Nat.add(HH, HH) : Nat} = Equal.trans(Nat, Nat.mul(Nat.double(H), H), Nat.mul(Nat.add(H, H), H), Nat.add(HH, HH),
        Equal.cong(Nat, Nat, w => Nat.mul(w, H), Nat.double(H), Nat.add(H, H), eH),
        R.NatN.eq(env, R.Ml(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ml(R.V(0n), R.V(0n))), [], [], {==}, Unit{}, {==}, {==}))
      +le : {RD.Nat.lt(Nat.mul(A, Bn), Nat.mul(Nat.double(H), H)) == False{} : Bool} = E.Le.trans(Nat.mul(Nat.double(H), H), Nat.add(HH, HH), Nat.mul(A, Bn), E.Le.eq(Nat.mul(Nat.double(H), H), Nat.add(HH, HH), e3),
        E.Le.trans(Nat.add(HH, HH), Nat.add(HH, Nat.mul(H, Nat.add(a, b))), Nat.mul(A, Bn), E2.Le.addl(HH, HH, Nat.mul(H, Nat.add(a, b)), E2.Le.mull(H, H, Nat.add(a, b), el)),
          E.Le.trans(Nat.add(HH, Nat.mul(H, Nat.add(a, b))), Nat.add(Nat.add(HH, Nat.mul(H, Nat.add(a, b))), Nat.mul(a, b)), Nat.mul(A, Bn), E.Le.add(Nat.add(HH, Nat.mul(H, Nat.add(a, b))), Nat.mul(a, b)),
            E.Le.eq(Nat.add(Nat.add(HH, Nat.mul(H, Nat.add(a, b))), Nat.mul(a, b)), Nat.mul(A, Bn), Equal.sym(Nat, Nat.mul(A, Bn), Nat.add(Nat.add(HH, Nat.mul(H, Nat.add(a, b))), Nat.mul(a, b)), Equal.trans(Nat, Nat.mul(A, Bn), Nat.mul(Nat.add(H, a), Nat.add(H, b)), Nat.add(Nat.add(HH, Nat.mul(H, Nat.add(a, b))), Nat.mul(a, b)), e1, e2))))))
      B.Bool.tf({RD.Nat.lt(Nat.add(A, Bn), Nat.add(Nat.double(H), H)) == True{} : Bool}, Equal.trans(Bool, True{}, RD.Nat.lt(Nat.mul(A, Bn), Nat.mul(Nat.double(H), H)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.mul(A, Bn), Nat.mul(Nat.double(H), H)), True{}, hs), le))

def L210(+A: Nat, +Bn: Nat, +H: Nat, +hA: {RD.Nat.lt(A, H) == False{} : Bool}, +hB: {RD.Nat.lt(Bn, H) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, Bn), Nat.mul(Nat.double(H), H)) == True{} : Bool})
  -> {RD.Nat.lt(Nat.add(A, Bn), Nat.add(Nat.double(H), H)) == True{} : Bool}:
  L210.go(A, Bn, H, RD.Nat.monus(A, H), RD.Nat.monus(Bn, H), E.Le.wit(H, A, hA), E.Le.wit(H, Bn, hB), hs, RD.Nat.lt(Nat.add(RD.Nat.monus(A, H), RD.Nat.monus(Bn, H)), H), {==})

# 4 x: errors finer than u² are bounded four times over
def Fq(+x: Nat) -> Nat:
  Nat.double(Nat.double(x))

def Fq.add(+a: Nat, +b: Nat) -> {Fq(Nat.add(a, b)) == Nat.add(Fq(a), Fq(b)) : Nat}:
  Equal.trans(Nat, Nat.double(Nat.double(Nat.add(a, b))), Nat.double(Nat.add(Nat.double(a), Nat.double(b))), Nat.add(Fq(a), Fq(b)),
    Equal.cong(Nat, Nat, w => Nat.double(w), Nat.double(Nat.add(a, b)), Nat.add(Nat.double(a), Nat.double(b)), E2.Dbl.add(a, b)),
    E2.Dbl.add(Nat.double(a), Nat.double(b)))

def Le.fq(+a: Nat, +b: Nat, h: E.Le(a, b)) -> E.Le(Fq(a), Fq(b)):
  E.Le.dd(Nat.double(a), Nat.double(b), E.Le.dd(a, b, h))

# Eta.le, four times over
def Eta4(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int, +k1: Nat, +k2: Nat, +k3: Nat, +k4: Nat, +kx: Nat,
  +hz: {M.z(p, xh, xl, yh, yl) == I.Int.add(M.ch(p, xh, yh), M.cl3(p, xh, xl, yh, yl)) : I.Int},
  +h1: {RD.Nat.lt(k1, Fq(RD.Int.mag(M.e1(p, xh, yl)))) == False{} : Bool}, +h2: {RD.Nat.lt(k2, Fq(RD.Int.mag(M.e2(p, xl, yh)))) == False{} : Bool},
  +h3: {RD.Nat.lt(k3, Fq(RD.Int.mag(M.e3(p, xh, xl, yh, yl)))) == False{} : Bool}, +h4: {RD.Nat.lt(k4, Fq(RD.Int.mag(M.e4(p, xh, xl, yh, yl)))) == False{} : Bool},
  +hx: {RD.Nat.lt(kx, Fq(RD.Int.mag(I.Int.neg(I.Int.mul(xl, yl))))) == False{} : Bool})
  -> {RD.Nat.lt(Nat.add(Nat.add(Nat.add(k1, k2), Nat.add(k3, k4)), kx), Fq(RD.Int.mag(M.eta(p, xh, xl, yh, yl)))) == False{} : Bool}:
  +m1 = RD.Int.mag(M.e1(p, xh, yl))
  +m2 = RD.Int.mag(M.e2(p, xl, yh))
  +m3 = RD.Int.mag(M.e3(p, xh, xl, yh, yl))
  +m4 = RD.Int.mag(M.e4(p, xh, xl, yh, yl))
  +mx = RD.Int.mag(I.Int.neg(I.Int.mul(xl, yl)))
  +me = RD.Int.mag(M.eta(p, xh, xl, yh, yl))
  +S = Nat.add(Nat.add(Nat.add(m1, m2), Nat.add(m3, m4)), mx)
  +F = Nat.add(Nat.add(Nat.add(Fq(m1), Fq(m2)), Nat.add(Fq(m3), Fq(m4))), Fq(mx))
  +K = Nat.add(Nat.add(Nat.add(k1, k2), Nat.add(k3, k4)), kx)
  +hs : {RD.Nat.lt(S, me) == False{} : Bool} = Eta.le(p, xh, xl, yh, yl, m1, m2, m3, m4, mx, hz, E.Lt.irr(m1), E.Lt.irr(m2), E.Lt.irr(m3), E.Lt.irr(m4), E.Lt.irr(mx))
  +eS : {Fq(S) == F : Nat} = Equal.trans(Nat, Fq(S), Nat.add(Fq(Nat.add(Nat.add(m1, m2), Nat.add(m3, m4))), Fq(mx)), F,
    Fq.add(Nat.add(Nat.add(m1, m2), Nat.add(m3, m4)), mx),
    Equal.cong(Nat, Nat, w => Nat.add(w, Fq(mx)), Fq(Nat.add(Nat.add(m1, m2), Nat.add(m3, m4))), Nat.add(Nat.add(Fq(m1), Fq(m2)), Nat.add(Fq(m3), Fq(m4))),
      Equal.trans(Nat, Fq(Nat.add(Nat.add(m1, m2), Nat.add(m3, m4))), Nat.add(Fq(Nat.add(m1, m2)), Fq(Nat.add(m3, m4))), Nat.add(Nat.add(Fq(m1), Fq(m2)), Nat.add(Fq(m3), Fq(m4))),
        Fq.add(Nat.add(m1, m2), Nat.add(m3, m4)),
        Equal.trans(Nat, Nat.add(Fq(Nat.add(m1, m2)), Fq(Nat.add(m3, m4))), Nat.add(Nat.add(Fq(m1), Fq(m2)), Fq(Nat.add(m3, m4))), Nat.add(Nat.add(Fq(m1), Fq(m2)), Nat.add(Fq(m3), Fq(m4))),
          Equal.cong(Nat, Nat, w => Nat.add(w, Fq(Nat.add(m3, m4))), Fq(Nat.add(m1, m2)), Nat.add(Fq(m1), Fq(m2)), Fq.add(m1, m2)),
          Equal.cong(Nat, Nat, w => Nat.add(Nat.add(Fq(m1), Fq(m2)), w), Fq(Nat.add(m3, m4)), Nat.add(Fq(m3), Fq(m4)), Fq.add(m3, m4))))))
  E.Le.trans(Fq(me), Fq(S), K, Le.fq(me, S, hs),
    E.Le.trans(Fq(S), F, K, E.Le.eq(Fq(S), F, eS),
      E2.Le.add2(Nat.add(Nat.add(Fq(m1), Fq(m2)), Nat.add(Fq(m3), Fq(m4))), Nat.add(Nat.add(k1, k2), Nat.add(k3, k4)), Fq(mx), kx,
        E2.Le.add2(Nat.add(Fq(m1), Fq(m2)), Nat.add(k1, k2), Nat.add(Fq(m3), Fq(m4)), Nat.add(k3, k4), E2.Le.add2(Fq(m1), k1, Fq(m2), k2, h1, h2), E2.Le.add2(Fq(m3), k3, Fq(m4), k4, h3, h4)),
        hx)))

# |cl1| <= u when xh yh < 2
def SC.cl1(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool})
  -> {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(Nat.add(D, D))), RD.Int.mag(M.cl1(1n+p1, XH(A, D), XH(B, D)))) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +V2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +V4 = RD.Nat.pow2(S4(D))
  +V8 = RD.Nat.pow2(3n+Nat.add(D, D))
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +e2 : {V2 == Nat.add(V, V) : Nat} = Y.Nat.double_add(V)
  +e4 : {V4 == Nat.add(V2, V2) : Nat} = Y.Nat.double_add(V2)
  +e8 : {V8 == Nat.add(V4, V4) : Nat} = Y.Nat.double_add(V4)
  +env : List<&2, Nat> = [H, P, V, V2, V4, V8]
  +c = RD.Int.mag(M.cl1(1n+p1, XH(A, D), XH(B, D)))
  +U = Nat.mul(P, V)
  +ec : {Nat.mul(H, V4) == Nat.add(U, U) : Nat} = R.NatN.eq(env, R.Ml(R.V(0n), R.V(4n)), R.Ad(R.Ml(R.V(1n), R.V(2n)), R.Ml(R.V(1n), R.V(2n))), [R.Ad(R.Ng(R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.V(0n), R.V(0n)), R.V(0n)], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(3n), R.Ng(R.Ad(R.V(2n), R.V(2n)))), R.Ad(R.V(4n), R.Ng(R.Ad(R.V(3n), R.V(3n))))], {==}, (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, eP), (R.NatN.z(env, R.V(3n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, e2), (R.NatN.z(env, R.V(4n), R.Ad(R.V(3n), R.V(3n)), {==}, {==}, e4), Unit{}))), {==}, {==})
  +h : {RD.Nat.lt(Nat.mul(H, V4), Nat.double(c)) == False{} : Bool} = Cl1.le(p1, A, B, D, p1, E2.Lt.to_le(Nat.mul(A, B), Nat.mul(P, H), hs))
  Le.halve(c, U, E.Le.trans(Nat.double(c), Nat.mul(H, V4), Nat.double(U), h,
    E.Le.eq(Nat.mul(H, V4), Nat.double(U), Equal.trans(Nat, Nat.mul(H, V4), Nat.add(U, U), Nat.double(U), ec, Equal.sym(Nat, Nat.double(U), Nat.add(U, U), Y.Nat.double_add(U))))))

# |xh yl| <= xh u, and so |tl1| <= xh u (xh u is representable)
def TLe(+p1: Nat, +A: Nat, +D: Nat, +z: I.Int, +l: I.Int, +ez: {RD.Int.mag(z) == Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+D)), RD.Int.mag(l)) : Nat},
  +hl: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(l)) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(A, RD.Nat.pow2(1n+Nat.add(D, D))), RD.Int.mag(z)) == False{} : Bool}:
  +W = RD.Nat.pow2(D)
  +W2 = RD.Nat.pow2(1n+D)
  +ew : {Nat.mul(Nat.mul(A, W2), W) == Nat.mul(A, RD.Nat.pow2(1n+Nat.add(D, D))) : Nat} = Equal.trans(Nat, Nat.mul(Nat.mul(A, W2), W), Nat.mul(A, Nat.mul(W2, W)), Nat.mul(A, RD.Nat.pow2(1n+Nat.add(D, D))),
    NL.Nat.mul_assoc(A, W2, W), Equal.cong(Nat, Nat, v => Nat.mul(A, v), Nat.mul(W2, W), RD.Nat.pow2(1n+Nat.add(D, D)), Equal.sym(Nat, RD.Nat.pow2(Nat.add(1n+D, D)), Nat.mul(W2, W), BP.Pow2.add(1n+D, D))))
  E.Le.trans(RD.Int.mag(z), Nat.mul(Nat.mul(A, W2), W), Nat.mul(A, RD.Nat.pow2(1n+Nat.add(D, D))),
    E.Le.trans(RD.Int.mag(z), Nat.mul(Nat.mul(A, W2), RD.Int.mag(l)), Nat.mul(Nat.mul(A, W2), W), E.Le.eq(RD.Int.mag(z), Nat.mul(Nat.mul(A, W2), RD.Int.mag(l)), ez), E2.Le.mull(Nat.mul(A, W2), RD.Int.mag(l), W, hl)),
    E.Le.eq(Nat.mul(Nat.mul(A, W2), W), Nat.mul(A, RD.Nat.pow2(1n+Nat.add(D, D))), ew))

def TLr(+p1: Nat, +A: Nat, +D: Nat, +z: I.Int, +l: I.Int, +ez: {RD.Int.mag(z) == Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+D)), RD.Int.mag(l)) : Nat},
  +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +hl: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(l)) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(A, RD.Nat.pow2(1n+Nat.add(D, D))), RD.Int.mag(E.RNi(1n+p1, z))) == False{} : Bool}:
  RB(p1, z, Nat.mul(A, RD.Nat.pow2(1n+Nat.add(D, D))), Rn.fix(p1, Nat.mul(A, RD.Nat.pow2(1n+Nat.add(D, D))), A, 1n+Nat.add(D, D), {==}, E2.Lt.to_le(A, RD.Nat.pow2(1n+p1), hA)), TLe(p1, A, D, z, l, ez, hl))

# |tl1 + tl2| <= (xh + yh) u <= 3u (Lemma 2.10)
def SC.s3(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool})
  -> {RD.Nat.lt(Nat.mul(3n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(Nat.add(D, D)))), RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))))) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +V2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +V4 = RD.Nat.pow2(S4(D))
  +V8 = RD.Nat.pow2(3n+Nat.add(D, D))
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +e2 : {V2 == Nat.add(V, V) : Nat} = Y.Nat.double_add(V)
  +e4 : {V4 == Nat.add(V2, V2) : Nat} = Y.Nat.double_add(V2)
  +e8 : {V8 == Nat.add(V4, V4) : Nat} = Y.Nat.double_add(V4)
  +env : List<&2, Nat> = [H, P, V, V2, V4, V8]
  +t1 = M.tl1(1n+p1, XH(A, D), yl)
  +t2 = M.tl2(1n+p1, xl, XH(B, D))
  +k1 = Nat.mul(A, V2)
  +k2 = Nat.mul(B, V2)
  +U3 = Nat.mul(3n, Nat.mul(P, V))
  +h12 : {RD.Nat.lt(Nat.add(k1, k2), RD.Int.mag(I.Int.add(t1, t2))) == False{} : Bool} = Tri2(t1, t2, k1, k2,
    TLr(p1, A, D, I.Int.mul(XH(A, D), yl), yl, TL1.mag(A, D, yl), hA, hy), TLr(p1, B, D, I.Int.mul(xl, XH(B, D)), xl, TL2.mag(B, D, xl), hB, hx))
  +envk : List<&2, Nat> = [A, B, V2]
  +ek : {Nat.add(k1, k2) == Nat.mul(Nat.add(A, B), V2) : Nat} = R.NatN.eq(envk, R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ml(R.V(1n), R.V(2n))), R.Ml(R.Ad(R.V(0n), R.V(1n)), R.V(2n)), [], [], {==}, Unit{}, {==}, {==})
  +hab : {RD.Nat.lt(Nat.add(P, H), Nat.add(A, B)) == False{} : Bool} = E2.Lt.to_le(Nat.add(A, B), Nat.add(P, H), L210(A, B, H, hA1, hB1, hs))
  +e3 : {Nat.mul(Nat.add(P, H), V2) == U3 : Nat} = R.NatN.eq(env, R.Ml(R.Ad(R.V(1n), R.V(0n)), R.V(3n)), R.Ad(R.Ml(R.V(1n), R.V(2n)), R.Ad(R.Ml(R.V(1n), R.V(2n)), R.Ad(R.Ml(R.V(1n), R.V(2n)), N.TZero{}))), [R.Ad(R.Ad(R.Ad(R.Ng(R.V(2n)), R.Ng(R.V(2n))), R.Ng(R.V(2n))), R.V(3n)), R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n))], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(3n), R.Ng(R.Ad(R.V(2n), R.V(2n))))], {==}, (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, eP), (R.NatN.z(env, R.V(3n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, e2), Unit{})), {==}, {==})
  E.Le.trans(RD.Int.mag(I.Int.add(t1, t2)), Nat.add(k1, k2), U3, h12,
    E.Le.trans(Nat.add(k1, k2), Nat.mul(Nat.add(A, B), V2), U3, E.Le.eq(Nat.add(k1, k2), Nat.mul(Nat.add(A, B), V2), ek),
      E.Le.trans(Nat.mul(Nat.add(A, B), V2), Nat.mul(Nat.add(P, H), V2), U3, E2.Le.mulr(Nat.add(A, B), Nat.add(P, H), V2, hab), E.Le.eq(Nat.mul(Nat.add(P, H), V2), U3, e3))))

# 3u is representable
def Fix3(+p1: Nat, +D: Nat, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool}) -> {E.Rn(1n+p1, Nat.mul(3n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(Nat.add(D, D))))) == Nat.mul(3n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(Nat.add(D, D)))) : Nat}:
  +k = Nat.add(1n+p1, Nat.add(D, D))
  +h4 : {RD.Nat.lt(RD.Nat.pow2(1n+p1), 4n) == False{} : Bool} = E2.Pow2.mono(2n, 1n+p1, E.Le.trans(2n, 5n, 1n+p1, {==}, E.Le.trans(5n, p1, 1n+p1, hp, E.Le.add1(p1))))
  Rn.fix(p1, Nat.mul(3n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(Nat.add(D, D)))), 3n, k, Equal.cong(Nat, Nat, w => Nat.mul(3n, w), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(Nat.add(D, D))), RD.Nat.pow2(k), Equal.sym(Nat, RD.Nat.pow2(k), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(Nat.add(D, D))), BP.Pow2.add(1n+p1, Nat.add(D, D)))),
    E.Le.trans(3n, 4n, RD.Nat.pow2(1n+p1), {==}, h4))

def SC.c2(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool})
  -> {RD.Nat.lt(Nat.mul(3n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(Nat.add(D, D)))), RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl))) == False{} : Bool}:
  RB(p1, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), Nat.mul(3n, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(Nat.add(D, D)))), Fix3(p1, D, hp), SC.s3(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs))

# |cl1 + cl2| <= 4u
def SC.c12(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool})
  -> {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(S4(D))), RD.Int.mag(I.Int.add(M.cl1(1n+p1, XH(A, D), XH(B, D)), M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +V2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +V4 = RD.Nat.pow2(S4(D))
  +V8 = RD.Nat.pow2(3n+Nat.add(D, D))
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +e2 : {V2 == Nat.add(V, V) : Nat} = Y.Nat.double_add(V)
  +e4 : {V4 == Nat.add(V2, V2) : Nat} = Y.Nat.double_add(V2)
  +e8 : {V8 == Nat.add(V4, V4) : Nat} = Y.Nat.double_add(V4)
  +env : List<&2, Nat> = [H, P, V, V2, V4, V8]
  +U = Nat.mul(P, V)
  +e : {Nat.add(U, Nat.mul(3n, U)) == Nat.mul(P, V4) : Nat} = R.NatN.eq(env, R.Ad(R.Ml(R.V(1n), R.V(2n)), R.Ad(R.Ml(R.V(1n), R.V(2n)), R.Ad(R.Ml(R.V(1n), R.V(2n)), R.Ad(R.Ml(R.V(1n), R.V(2n)), N.TZero{})))), R.Ml(R.V(1n), R.V(4n)), [R.Ad(R.Ng(R.V(1n)), R.Ng(R.V(1n))), R.Ng(R.V(1n))], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(2n), R.V(2n)))), R.Ad(R.V(4n), R.Ng(R.Ad(R.V(3n), R.V(3n))))], {==}, (R.NatN.z(env, R.V(3n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, e2), (R.NatN.z(env, R.V(4n), R.Ad(R.V(3n), R.V(3n)), {==}, {==}, e4), Unit{})), {==}, {==})
  E.Le.trans(RD.Int.mag(I.Int.add(M.cl1(1n+p1, XH(A, D), XH(B, D)), M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl))), Nat.add(U, Nat.mul(3n, U)), Nat.mul(P, V4), Tri2(M.cl1(1n+p1, XH(A, D), XH(B, D)), M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl), U, Nat.mul(3n, U), SC.cl1(p1, A, B, D, hs), SC.c2(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs)),
    E.Le.eq(Nat.add(U, Nat.mul(3n, U)), Nat.mul(P, V4), e))

# the error bounds of the general case, four times over
def G.e1(+p1: Nat, +A: Nat, +D: Nat, +yl: I.Int, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(S4(D)), Fq(RD.Int.mag(M.e1(1n+p1, XH(A, D), yl)))) == False{} : Bool}:
  Le.fq(RD.Int.mag(M.e1(1n+p1, XH(A, D), yl)), RD.Nat.pow2(Nat.add(D, D)), Er1.le(p1, D, A, yl, hA, hy))

def G.e2(+p1: Nat, +B: Nat, +D: Nat, +xl: I.Int, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool}, +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(S4(D)), Fq(RD.Int.mag(M.e2(1n+p1, xl, XH(B, D))))) == False{} : Bool}:
  Le.fq(RD.Int.mag(M.e2(1n+p1, xl, XH(B, D))), RD.Nat.pow2(Nat.add(D, D)), Er2.le(p1, D, B, xl, hB, hx))

def G.x(+D: Nat, +xl: I.Int, +yl: I.Int, +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(S4(D)), Fq(RD.Int.mag(I.Int.neg(I.Int.mul(xl, yl))))) == False{} : Bool}:
  Le.fq(RD.Int.mag(I.Int.neg(I.Int.mul(xl, yl))), RD.Nat.pow2(Nat.add(D, D)), XY.le(D, xl, yl, hx, hy))

def G.e3(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(3n+Nat.add(D, D)), Fq(RD.Int.mag(M.e3(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +V2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +V4 = RD.Nat.pow2(S4(D))
  +V8 = RD.Nat.pow2(3n+Nat.add(D, D))
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +e2 : {V2 == Nat.add(V, V) : Nat} = Y.Nat.double_add(V)
  +e4 : {V4 == Nat.add(V2, V2) : Nat} = Y.Nat.double_add(V2)
  +e8 : {V8 == Nat.add(V4, V4) : Nat} = Y.Nat.double_add(V4)
  +env : List<&2, Nat> = [H, P, V, V2, V4, V8]
  +U3 = Nat.mul(3n, Nat.mul(P, V))
  +e : {Nat.mul(P, V4) == Nat.add(U3, Nat.mul(P, V)) : Nat} = R.NatN.eq(env, R.Ml(R.V(1n), R.V(4n)), R.Ad(R.Ad(R.Ml(R.V(1n), R.V(2n)), R.Ad(R.Ml(R.V(1n), R.V(2n)), R.Ad(R.Ml(R.V(1n), R.V(2n)), N.TZero{}))), R.Ml(R.V(1n), R.V(2n))), [R.Ad(R.V(1n), R.V(1n)), R.V(1n)], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(2n), R.V(2n)))), R.Ad(R.V(4n), R.Ng(R.Ad(R.V(3n), R.V(3n))))], {==}, (R.NatN.z(env, R.V(3n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, e2), (R.NatN.z(env, R.V(4n), R.Ad(R.V(3n), R.V(3n)), {==}, {==}, e4), Unit{})), {==}, {==})
  +h : {RD.Nat.lt(Nat.mul(P, V4), RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))))) == False{} : Bool} = E.Le.trans(RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), U3, Nat.mul(P, V4), SC.s3(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs),
    E.Le.trans(U3, Nat.add(U3, Nat.mul(P, V)), Nat.mul(P, V4), E.Le.add(U3, Nat.mul(P, V)), E.Le.eq(Nat.add(U3, Nat.mul(P, V)), Nat.mul(P, V4), Equal.sym(Nat, Nat.mul(P, V4), Nat.add(U3, Nat.mul(P, V)), e))))
  E.Le.dd(Nat.double(RD.Int.mag(M.e3(1n+p1, XH(A, D), xl, XH(B, D), yl))), V4, EB(p1, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), S4(D), h))

def G.e4(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(3n+Nat.add(D, D)), Fq(RD.Int.mag(M.e4(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  E.Le.dd(Nat.double(RD.Int.mag(M.e4(1n+p1, XH(A, D), xl, XH(B, D), yl))), RD.Nat.pow2(S4(D)), EB(p1, I.Int.add(M.cl1(1n+p1, XH(A, D), XH(B, D)), M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), S4(D), SC.c12(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs)))

# S1: |cl2| >= 2u makes cl2, and so cl1 + cl2, a multiple of 4u²: e4 = 0
def Sm.S1(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool},
  +hc: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +V2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +V4 = RD.Nat.pow2(S4(D))
  +V8 = RD.Nat.pow2(3n+Nat.add(D, D))
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +e2 : {V2 == Nat.add(V, V) : Nat} = Y.Nat.double_add(V)
  +e4 : {V4 == Nat.add(V2, V2) : Nat} = Y.Nat.double_add(V2)
  +e8 : {V8 == Nat.add(V4, V4) : Nat} = Y.Nat.double_add(V4)
  +env : List<&2, Nat> = [H, P, V, V2, V4, V8]
  +p : Nat = 1n+p1
  +s = I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))
  +c1 = M.cl1(1n+p1, XH(A, D), XH(B, D))
  +c2 = M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)
  +k = S4(D)
  +r = E.Rn(p, RD.Int.mag(s))
  +er : {RD.Int.mag(c2) == r : Nat} = Mag.sg(s, r)
  +ehv : {Nat.mul(H, V4) == Nat.mul(P, V2) : Nat} = R.NatN.eq(env, R.Ml(R.V(0n), R.V(4n)), R.Ml(R.V(1n), R.V(3n)), [R.Ng(R.V(3n)), R.V(0n)], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(4n), R.Ng(R.Ad(R.V(3n), R.V(3n))))], {==}, (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, eP), (R.NatN.z(env, R.V(4n), R.Ad(R.V(3n), R.V(3n)), {==}, {==}, e4), Unit{})), {==}, {==})
  +hr : {RD.Nat.lt(r, Nat.mul(H, V4)) == False{} : Bool} = E.Le.trans(Nat.mul(H, V4), Nat.mul(P, V2), r, E.Le.eq(Nat.mul(H, V4), Nat.mul(P, V2), ehv),
    E.Le.trans(Nat.mul(P, V2), RD.Int.mag(c2), r, hc, E.Le.eq(RD.Int.mag(c2), r, er)))
  +a = W1(p, A, B)
  +b = RD.Int.signed(s, Mq(p1, r, k))
  +ecc : {I.Int.add(c1, c2) == I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)) : I.Int} = Equal.trans(I.Int, I.Int.add(c1, c2), I.Int.add(D.Int.sh(k, a), c2), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)),
    Equal.cong(I.Int, I.Int, w => I.Int.add(w, c2), c1, D.Int.sh(k, a), Cl1.sh(p, A, B, D)),
    Equal.cong(I.Int, I.Int, w => I.Int.add(D.Int.sh(k, a), w), c2, D.Int.sh(k, b), Ri.sh(p1, s, k, hr)))
  +h4 : {RD.Nat.lt(Nat.mul(P, V4), RD.Int.mag(I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)))) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Nat.mul(P, V4), RD.Int.mag(I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)))), RD.Nat.lt(Nat.mul(P, V4), RD.Int.mag(I.Int.add(c1, c2))), False{},
    Equal.cong(I.Int, Bool, w => RD.Nat.lt(Nat.mul(P, V4), RD.Int.mag(w)), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), I.Int.add(c1, c2), Equal.sym(I.Int, I.Int.add(c1, c2), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), ecc)),
    SC.c12(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs))
  +exc : {E.RNi(p, I.Int.add(c1, c2)) == I.Int.add(c1, c2) : I.Int} = Equal.trans(I.Int, E.RNi(p, I.Int.add(c1, c2)), E.RNi(p, I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b))), I.Int.add(c1, c2),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(c1, c2), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), ecc),
    Equal.trans(I.Int, E.RNi(p, I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b))), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), I.Int.add(c1, c2), Ex.sum(p1, k, a, b, h4), Equal.sym(I.Int, I.Int.add(c1, c2), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), ecc)))
  +hz = Zx.exact(p1, A, B, D, xl, yl, Hp2(p1, hp), hA1, hA, hB1, hB, hx, hy)
  +bd : {RD.Nat.lt(Nat.add(Nat.add(Nat.add(V4, V4), Nat.add(V8, 0n)), V4), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool} =
    Eta4(p, XH(A, D), xl, XH(B, D), yl, V4, V4, V8, 0n, V4, hz, G.e1(p1, A, D, yl, hA, hy), G.e2(p1, B, D, xl, hB, hx), G.e3(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs),
      Le.fq(RD.Int.mag(M.e4(1n+p1, XH(A, D), xl, XH(B, D), yl)), 0n, Err.z(p, I.Int.add(c1, c2), exc)), G.x(D, xl, yl, hx, hy))
  +es : {Nat.add(Nat.add(Nat.add(V4, V4), Nat.add(V8, 0n)), V4) == Nat.mul(5n, V4) : Nat} = R.NatN.eq2(env, R.Ad(R.Ad(R.Ad(R.V(4n), R.V(4n)), R.Ad(R.V(5n), N.TZero{})), R.V(4n)), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), N.TZero{}))))), [], [], [R.Ad(R.V(5n), R.Ng(R.Ad(R.V(4n), R.V(4n))))], {==}, Unit{}, (R.NatN.z(env, R.V(5n), R.Ad(R.V(4n), R.V(4n)), {==}, {==}, e8), Unit{}), {==}, {==})
  E.Le.trans(Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl))), Nat.add(Nat.add(Nat.add(V4, V4), Nat.add(V8, 0n)), V4), Nat.mul(5n, V4), bd, E.Le.eq(Nat.add(Nat.add(Nat.add(V4, V4), Nat.add(V8, 0n)), V4), Nat.mul(5n, V4), es))


# eta is symmetric in x and y
def Tl.sym(+p: Nat, +a: I.Int, +b: I.Int) -> {M.tl1(p, a, b) == M.tl2(p, b, a) : I.Int}:
  Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.mul(a, b), I.Int.mul(b, a), Z.Int.mul_comm(a, b))

def Ch.sym(+p: Nat, +xh: I.Int, +yh: I.Int) -> {M.ch(p, yh, xh) == M.ch(p, xh, yh) : I.Int}:
  Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.mul(yh, xh), I.Int.mul(xh, yh), Z.Int.mul_comm(yh, xh))

def Cl1.sym(+p: Nat, +xh: I.Int, +yh: I.Int) -> {M.cl1(p, yh, xh) == M.cl1(p, xh, yh) : I.Int}:
  Equal.trans(I.Int, M.cl1(p, yh, xh), I.Int.add(I.Int.mul(xh, yh), I.Int.neg(M.ch(p, yh, xh))), M.cl1(p, xh, yh),
    Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.neg(M.ch(p, yh, xh))), I.Int.mul(yh, xh), I.Int.mul(xh, yh), Z.Int.mul_comm(yh, xh)),
    Equal.cong(I.Int, I.Int, w => I.Int.add(I.Int.mul(xh, yh), I.Int.neg(w)), M.ch(p, yh, xh), M.ch(p, xh, yh), Ch.sym(p, xh, yh)))

def Cl2.sym(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> {M.cl2(p, yh, yl, xh, xl) == M.cl2(p, xh, xl, yh, yl) : I.Int}:
  +t1 = M.tl1(p, xh, yl)
  +t2 = M.tl2(p, xl, yh)
  +e : {I.Int.add(M.tl1(p, yh, xl), M.tl2(p, yl, xh)) == I.Int.add(t1, t2) : I.Int} = Equal.trans(I.Int, I.Int.add(M.tl1(p, yh, xl), M.tl2(p, yl, xh)), I.Int.add(t2, t1), I.Int.add(t1, t2),
    Equal.trans(I.Int, I.Int.add(M.tl1(p, yh, xl), M.tl2(p, yl, xh)), I.Int.add(t2, M.tl2(p, yl, xh)), I.Int.add(t2, t1),
      Equal.cong(I.Int, I.Int, w => I.Int.add(w, M.tl2(p, yl, xh)), M.tl1(p, yh, xl), t2, Tl.sym(p, yh, xl)),
      Equal.cong(I.Int, I.Int, w => I.Int.add(t2, w), M.tl2(p, yl, xh), t1, Equal.sym(I.Int, t1, M.tl2(p, yl, xh), Tl.sym(p, xh, yl)))),
    Z.Int.add_comm(t2, t1))
  Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(M.tl1(p, yh, xl), M.tl2(p, yl, xh)), I.Int.add(t1, t2), e)

def Cl3.sym(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> {M.cl3(p, yh, yl, xh, xl) == M.cl3(p, xh, xl, yh, yl) : I.Int}:
  +c2 = M.cl2(p, yh, yl, xh, xl)
  Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(M.cl1(p, yh, xh), c2), I.Int.add(M.cl1(p, xh, yh), M.cl2(p, xh, xl, yh, yl)),
    Equal.trans(I.Int, I.Int.add(M.cl1(p, yh, xh), c2), I.Int.add(M.cl1(p, xh, yh), c2), I.Int.add(M.cl1(p, xh, yh), M.cl2(p, xh, xl, yh, yl)),
      Equal.cong(I.Int, I.Int, w => I.Int.add(w, c2), M.cl1(p, yh, xh), M.cl1(p, xh, yh), Cl1.sym(p, xh, yh)),
      Equal.cong(I.Int, I.Int, w => I.Int.add(M.cl1(p, xh, yh), w), c2, M.cl2(p, xh, xl, yh, yl), Cl2.sym(p, xh, xl, yh, yl))))

def Eta.sym(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> {M.eta(p, yh, yl, xh, xl) == M.eta(p, xh, xl, yh, yl) : I.Int}:
  +ch = M.ch(p, xh, yh)
  +c3 = M.cl3(p, xh, xl, yh, yl)
  +c3s = M.cl3(p, yh, yl, xh, xl)
  +ez : {M.z(p, yh, yl, xh, xl) == M.z(p, xh, xl, yh, yl) : I.Int} = Equal.trans(I.Int, M.z(p, yh, yl, xh, xl), I.Int.add(E.F2.s(p, ch, c3s), E.F2.t(p, ch, c3s)), M.z(p, xh, xl, yh, yl),
    Equal.cong(I.Int, I.Int, w => I.Int.add(E.F2.s(p, w, c3s), E.F2.t(p, w, c3s)), M.ch(p, yh, xh), ch, Ch.sym(p, xh, yh)),
    Equal.cong(I.Int, I.Int, w => I.Int.add(E.F2.s(p, ch, w), E.F2.t(p, ch, w)), c3s, c3, Cl3.sym(p, xh, xl, yh, yl)))
  Equal.trans(I.Int, M.eta(p, yh, yl, xh, xl), I.Int.add(M.z(p, xh, xl, yh, yl), I.Int.neg(I.Int.mul(I.Int.add(yh, yl), I.Int.add(xh, xl)))), M.eta(p, xh, xl, yh, yl),
    Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.neg(I.Int.mul(I.Int.add(yh, yl), I.Int.add(xh, xl)))), M.z(p, yh, yl, xh, xl), M.z(p, xh, xl, yh, yl), ez),
    Equal.cong(I.Int, I.Int, w => I.Int.add(M.z(p, xh, xl, yh, yl), I.Int.neg(w)), I.Int.mul(I.Int.add(yh, yl), I.Int.add(xh, xl)), I.Int.mul(I.Int.add(xh, xl), I.Int.add(yh, yl)), Z.Int.mul_comm(I.Int.add(yh, yl), I.Int.add(xh, xl))))

def M2(+x: Nat) -> {Nat.mul(x, RD.Nat.pow2(1n)) == Nat.double(x) : Nat}:
  Equal.trans(Nat, Nat.mul(x, Nat.double(1n)), Nat.double(Nat.mul(x, 1n)), Nat.double(x), R.Nat.mul_double(x, 1n), Equal.cong(Nat, Nat, w => Nat.double(w), Nat.mul(x, 1n), x, NL.Nat.mul_one_r(x)))

# S2: |cl2| < 2u, so |tl1 + tl2| < 2u and |e3| <= u²
def S2.s(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hc2: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool})
  -> {RD.Nat.lt(RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool}:
  RL.c(p1, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D))), Pk.fix(p1, 1n+Nat.add(D, D)), hc2)

def S2.e3(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hc2: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool})
  -> {RD.Nat.lt(RD.Nat.pow2(S4(D)), Fq(RD.Int.mag(M.e3(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  E.Le.dd(Nat.double(RD.Int.mag(M.e3(1n+p1, XH(A, D), xl, XH(B, D), yl))), RD.Nat.pow2(1n+Nat.add(D, D)), EB(p1, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), 1n+Nat.add(D, D), E2.Lt.to_le(RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D))), S2.s(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2))))

# S2a: |tl1| < u/2, so |e1| <= u²/4 and |yl| < u/2
def Sm.S2a(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hc2: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool},
  +ht: {RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D)))) == True{} : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +V2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +V4 = RD.Nat.pow2(S4(D))
  +V8 = RD.Nat.pow2(3n+Nat.add(D, D))
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +e2 : {V2 == Nat.add(V, V) : Nat} = Y.Nat.double_add(V)
  +e4 : {V4 == Nat.add(V2, V2) : Nat} = Y.Nat.double_add(V2)
  +e8 : {V8 == Nat.add(V4, V4) : Nat} = Y.Nat.double_add(V4)
  +env : List<&2, Nat> = [H, P, V, V2, V4, V8]
  +p : Nat = 1n+p1
  +W = RD.Nat.pow2(D)
  +W2 = RD.Nat.pow2(1n+D)
  +t1 = I.Int.mul(XH(A, D), yl)
  +m1 = RD.Int.mag(t1)
  +y = RD.Int.mag(yl)
  +HV = Nat.mul(H, V)
  +fHV : {E.Rn(p, HV) == HV : Nat} = Rn.fix(p1, HV, H, Nat.add(D, D), {==}, E2.Lt.to_le(H, P, E2.Lt.dself(H, BP.Pow2.pos(p1))))
  +h1 : {RD.Nat.lt(m1, HV) == True{} : Bool} = RL.c(p1, t1, HV, fHV, ht)
  +l1 : {RD.Nat.lt(HV, m1) == False{} : Bool} = E2.Lt.to_le(m1, HV, h1)
  +hd : {RD.Nat.lt(Nat.mul(P, V), Nat.mul(m1, RD.Nat.pow2(1n))) == False{} : Bool} = E.Le.trans(Nat.mul(m1, RD.Nat.pow2(1n)), Nat.double(m1), Nat.mul(P, V), E.Le.eq(Nat.mul(m1, RD.Nat.pow2(1n)), Nat.double(m1), M2(m1)),
    E.Le.trans(Nat.double(m1), Nat.double(HV), Nat.mul(P, V), E.Le.dd(m1, HV, l1), E.Le.eq(Nat.double(HV), Nat.mul(P, V), Equal.sym(Nat, Nat.mul(P, V), Nat.double(HV), BP.Mul.dbl_l(H, V)))))
  +q1 = RD.Int.mag(M.e1(1n+p1, XH(A, D), yl))
  +he1 : {RD.Nat.lt(V, Fq(q1)) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(V, Fq(q1)), RD.Nat.lt(V, Nat.double(Nat.mul(q1, RD.Nat.pow2(1n)))), False{},
    Equal.cong(Nat, Bool, w => RD.Nat.lt(V, Nat.double(w)), Nat.double(q1), Nat.mul(q1, RD.Nat.pow2(1n)), Equal.sym(Nat, Nat.mul(q1, RD.Nat.pow2(1n)), Nat.double(q1), M2(q1))),
    EBS(p1, t1, Nat.add(D, D), 1n, hd))
  # 2 |yl| < 2^D
  +Y2 = Nat.double(y)
  +Vv = V
  +ew2 : {W2 == Nat.add(W, W) : Nat} = Y.Nat.double_add(W)
  +ey2 : {Y2 == Nat.add(y, y) : Nat} = Y.Nat.double_add(y)
  +ev : {Vv == Nat.mul(W, W) : Nat} = Vsq(D)
  +envy : List<&2, Nat> = [H, W, y, W2, Y2, Vv]
  +ea : {Nat.mul(Nat.mul(H, W2), y) == Nat.mul(Y2, Nat.mul(H, W)) : Nat} = R.NatN.eq(envy, R.Ml(R.Ml(R.V(0n), R.V(3n)), R.V(2n)), R.Ml(R.V(4n), R.Ml(R.V(0n), R.V(1n))), [R.Ml(R.V(0n), R.V(2n)), R.Ng(R.Ml(R.V(0n), R.V(1n)))], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(1n), R.V(1n)))), R.Ad(R.V(4n), R.Ng(R.Ad(R.V(2n), R.V(2n))))], {==}, (R.NatN.z(envy, R.V(3n), R.Ad(R.V(1n), R.V(1n)), {==}, {==}, ew2), (R.NatN.z(envy, R.V(4n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, ey2), Unit{})), {==}, {==})
  +eb : {Nat.mul(H, Vv) == Nat.mul(W, Nat.mul(H, W)) : Nat} = R.NatN.eq(envy, R.Ml(R.V(0n), R.V(5n)), R.Ml(R.V(1n), R.Ml(R.V(0n), R.V(1n))), [R.V(0n)], [R.Ad(R.V(5n), R.Ng(R.Ml(R.V(1n), R.V(1n))))], {==}, (R.NatN.z(envy, R.V(5n), R.Ml(R.V(1n), R.V(1n)), {==}, {==}, ev), Unit{}), {==}, {==})
  +lA : {RD.Nat.lt(m1, Nat.mul(Nat.mul(H, W2), y)) == False{} : Bool} = E.Le.trans(Nat.mul(Nat.mul(H, W2), y), Nat.mul(Nat.mul(A, W2), y), m1,
    E2.Le.mulr(Nat.mul(H, W2), Nat.mul(A, W2), y, E2.Le.mulr(H, A, W2, hA1)), E.Le.eq(Nat.mul(Nat.mul(A, W2), y), m1, Equal.sym(Nat, m1, Nat.mul(Nat.mul(A, W2), y), TL1.mag(A, D, yl))))
  +hy2 : {RD.Nat.lt(Y2, W) == True{} : Bool} = E.Lt.cancel(Y2, W, Nat.mul(H, W),
    E2.Le.lt_trans(Nat.mul(Y2, Nat.mul(H, W)), m1, Nat.mul(W, Nat.mul(H, W)),
      E.Le.trans(Nat.mul(Y2, Nat.mul(H, W)), Nat.mul(Nat.mul(H, W2), y), m1, E.Le.eq(Nat.mul(Y2, Nat.mul(H, W)), Nat.mul(Nat.mul(H, W2), y), Equal.sym(Nat, Nat.mul(Nat.mul(H, W2), y), Nat.mul(Y2, Nat.mul(H, W)), ea)), lA),
      Equal.trans(Bool, RD.Nat.lt(m1, Nat.mul(W, Nat.mul(H, W))), RD.Nat.lt(m1, HV), True{}, Equal.cong(Nat, Bool, w => RD.Nat.lt(m1, w), Nat.mul(W, Nat.mul(H, W)), HV, Equal.sym(Nat, HV, Nat.mul(W, Nat.mul(H, W)), eb)), h1)))
  +mx = RD.Int.mag(I.Int.neg(I.Int.mul(xl, yl)))
  +emx : {mx == Nat.mul(RD.Int.mag(xl), y) : Nat} = Equal.trans(Nat, mx, RD.Int.mag(I.Int.mul(xl, yl)), Nat.mul(RD.Int.mag(xl), y), E.Mag.neg(I.Int.mul(xl, yl)), E2.Mag.mul(xl, yl))
  +lx : {RD.Nat.lt(V, Nat.double(mx)) == False{} : Bool} = E.Le.trans(Nat.double(mx), Nat.mul(RD.Int.mag(xl), Y2), V,
    E.Le.eq(Nat.double(mx), Nat.mul(RD.Int.mag(xl), Y2), Equal.trans(Nat, Nat.double(mx), Nat.double(Nat.mul(RD.Int.mag(xl), y)), Nat.mul(RD.Int.mag(xl), Y2),
      Equal.cong(Nat, Nat, w => Nat.double(w), mx, Nat.mul(RD.Int.mag(xl), y), emx), Equal.sym(Nat, Nat.mul(RD.Int.mag(xl), Y2), Nat.double(Nat.mul(RD.Int.mag(xl), y)), R.Nat.mul_double(RD.Int.mag(xl), y)))),
    E.Le.trans(Nat.mul(RD.Int.mag(xl), Y2), Nat.mul(W, W), V, E2.Le.mul2(RD.Int.mag(xl), W, Y2, W, hx, E2.Lt.to_le(Y2, W, hy2)), E.Le.eq(Nat.mul(W, W), V, Equal.sym(Nat, V, Nat.mul(W, W), ev))))
  +hz = Zx.exact(p1, A, B, D, xl, yl, Hp2(p1, hp), hA1, hA, hB1, hB, hx, hy)
  +sm = Nat.add(Nat.add(Nat.add(V, V4), Nat.add(V4, V8)), V2)
  +bd : {RD.Nat.lt(sm, Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool} =
    Eta4(p, XH(A, D), xl, XH(B, D), yl, V, V4, V4, V8, V2, hz, he1, G.e2(p1, B, D, xl, hB, hx), S2.e3(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2), G.e4(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs), E.Le.dd(Nat.double(mx), V, lx))
  +es : {Nat.mul(5n, V4) == Nat.add(sm, V) : Nat} = R.NatN.eq2(env, R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), N.TZero{}))))), R.Ad(R.Ad(R.Ad(R.Ad(R.V(2n), R.V(4n)), R.Ad(R.V(4n), R.V(5n))), R.V(3n)), R.V(2n)), [], [], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(2n), R.V(2n)))), R.Ad(R.V(4n), R.Ng(R.Ad(R.V(3n), R.V(3n)))), R.Ad(R.Ad(R.V(4n), R.V(4n)), R.Ng(R.V(5n)))], {==}, Unit{}, (R.NatN.z(env, R.V(3n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, e2), (R.NatN.z(env, R.V(4n), R.Ad(R.V(3n), R.V(3n)), {==}, {==}, e4), (R.NatN.z(env, R.Ad(R.V(4n), R.V(4n)), R.V(5n), {==}, {==}, Equal.sym(Nat, V8, Nat.add(V4, V4), e8)), Unit{}))), {==}, {==})
  E.Le.trans(Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl))), sm, Nat.mul(5n, V4), bd,
    E.Le.trans(sm, Nat.add(sm, V), Nat.mul(5n, V4), E.Le.add(sm, V), E.Le.eq(Nat.add(sm, V), Nat.mul(5n, V4), Equal.sym(Nat, Nat.mul(5n, V4), Nat.add(sm, V), es))))

# swapping x and y: a bound on 4 |eta| for (y, x) holds for (x, y)
def Swap.hs(+p1: Nat, +A: Nat, +B: Nat, +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool})
  -> {RD.Nat.lt(Nat.mul(B, A), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(Nat.mul(B, A), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))), RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))), True{},
    Equal.cong(Nat, Bool, w => RD.Nat.lt(w, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))), Nat.mul(B, A), Nat.mul(A, B), NL.Nat.mul_comm(B, A)), hs)

def Swap.c2(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +c: Nat, +l: Bool,
  +h: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), c) == l : Bool})
  -> {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(B, D), yl, XH(A, D), xl)), c) == l : Bool}:
  Equal.trans(Bool, RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(B, D), yl, XH(A, D), xl)), c), RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), c), l,
    Equal.cong(I.Int, Bool, w => RD.Nat.lt(RD.Int.mag(w), c), M.cl2(1n+p1, XH(B, D), yl, XH(A, D), xl), M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl), Cl2.sym(1n+p1, XH(A, D), xl, XH(B, D), yl)), h)

def Swap.t2(+p1: Nat, +B: Nat, +D: Nat, +xl: I.Int, +c: Nat, +l: Bool,
  +h: {RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), c) == l : Bool})
  -> {RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(B, D), xl)), c) == l : Bool}:
  Equal.trans(Bool, RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(B, D), xl)), c), RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), c), l,
    Equal.cong(I.Int, Bool, w => RD.Nat.lt(RD.Int.mag(w), c), M.tl1(1n+p1, XH(B, D), xl), M.tl2(1n+p1, xl, XH(B, D)), Tl.sym(1n+p1, XH(B, D), xl)), h)

def Swap.t1(+p1: Nat, +A: Nat, +D: Nat, +yl: I.Int, +c: Nat, +l: Bool,
  +h: {RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), c) == l : Bool})
  -> {RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, yl, XH(A, D))), c) == l : Bool}:
  Equal.trans(Bool, RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, yl, XH(A, D))), c), RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), c), l,
    Equal.cong(I.Int, Bool, w => RD.Nat.lt(RD.Int.mag(w), c), M.tl2(1n+p1, yl, XH(A, D)), M.tl1(1n+p1, XH(A, D), yl), Equal.sym(I.Int, M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, yl, XH(A, D)), Tl.sym(1n+p1, XH(A, D), yl))), h)

def Swap.eta(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +k: Nat,
  +h: {RD.Nat.lt(k, Fq(RD.Int.mag(M.eta(1n+p1, XH(B, D), yl, XH(A, D), xl)))) == False{} : Bool})
  -> {RD.Nat.lt(k, Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(k, Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))), RD.Nat.lt(k, Fq(RD.Int.mag(M.eta(1n+p1, XH(B, D), yl, XH(A, D), xl)))), False{},
    Equal.cong(I.Int, Bool, w => RD.Nat.lt(k, Fq(RD.Int.mag(w))), M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl), M.eta(1n+p1, XH(B, D), yl, XH(A, D), xl), Equal.sym(I.Int, M.eta(1n+p1, XH(B, D), yl, XH(A, D), xl), M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl), Eta.sym(1n+p1, XH(A, D), xl, XH(B, D), yl))), h)

# S2b: |tl2| < u/2, by symmetry
def Sm.S2b(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hc2: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool},
  +ht: {RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D)))) == True{} : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  Swap.eta(p1, A, B, D, xl, yl, Nat.mul(5n, RD.Nat.pow2(S4(D))), Sm.S2a(p1, B, A, D, yl, xl, hp, hB1, hB, hA1, hA, hy, hx, Swap.hs(p1, A, B, hs),
    Swap.c2(p1, A, B, D, xl, yl, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D))), True{}, hc2), Swap.t2(p1, B, D, xl, Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D))), True{}, ht)))

# one rounding exact: the totals 18u²/4, 14u²/4 and 20u²/4
def Tot18(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +he1: {RD.Nat.lt(RD.Nat.pow2(1n+Nat.add(D, D)), Fq(RD.Int.mag(M.e1(1n+p1, XH(A, D), yl)))) == False{} : Bool}, +h3: {RD.Nat.lt(0n, RD.Int.mag(M.e3(1n+p1, XH(A, D), xl, XH(B, D), yl))) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +V2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +V4 = RD.Nat.pow2(S4(D))
  +V8 = RD.Nat.pow2(3n+Nat.add(D, D))
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +e2 : {V2 == Nat.add(V, V) : Nat} = Y.Nat.double_add(V)
  +e4 : {V4 == Nat.add(V2, V2) : Nat} = Y.Nat.double_add(V2)
  +e8 : {V8 == Nat.add(V4, V4) : Nat} = Y.Nat.double_add(V4)
  +env : List<&2, Nat> = [H, P, V, V2, V4, V8]
  +sm = Nat.add(Nat.add(Nat.add(V2, V4), Nat.add(0n, V8)), V4)
  +bd : {RD.Nat.lt(sm, Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool} =
    Eta4(1n+p1, XH(A, D), xl, XH(B, D), yl, V2, V4, 0n, V8, V4, Zx.exact(p1, A, B, D, xl, yl, Hp2(p1, hp), hA1, hA, hB1, hB, hx, hy), he1, G.e2(p1, B, D, xl, hB, hx),
      Le.fq(RD.Int.mag(M.e3(1n+p1, XH(A, D), xl, XH(B, D), yl)), 0n, h3), G.e4(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs), G.x(D, xl, yl, hx, hy))
  +es : {Nat.mul(5n, V4) == Nat.add(sm, V2) : Nat} = R.NatN.eq2(env, R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), N.TZero{}))))), R.Ad(R.Ad(R.Ad(R.Ad(R.V(3n), R.V(4n)), R.Ad(N.TZero{}, R.V(5n))), R.V(4n)), R.V(3n)), [], [], [R.Ad(R.V(4n), R.Ng(R.Ad(R.V(3n), R.V(3n)))), R.Ad(R.Ad(R.V(4n), R.V(4n)), R.Ng(R.V(5n)))], {==}, Unit{}, (R.NatN.z(env, R.V(4n), R.Ad(R.V(3n), R.V(3n)), {==}, {==}, e4), (R.NatN.z(env, R.Ad(R.V(4n), R.V(4n)), R.V(5n), {==}, {==}, Equal.sym(Nat, V8, Nat.add(V4, V4), e8)), Unit{})), {==}, {==})
  E.Le.trans(Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl))), sm, Nat.mul(5n, V4), bd,
    E.Le.trans(sm, Nat.add(sm, V2), Nat.mul(5n, V4), E.Le.add(sm, V2), E.Le.eq(Nat.add(sm, V2), Nat.mul(5n, V4), Equal.sym(Nat, Nat.mul(5n, V4), Nat.add(sm, V2), es))))

def Tot14(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hc2: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool},
  +he1: {RD.Nat.lt(RD.Nat.pow2(1n+Nat.add(D, D)), Fq(RD.Int.mag(M.e1(1n+p1, XH(A, D), yl)))) == False{} : Bool}, +h4: {RD.Nat.lt(0n, RD.Int.mag(M.e4(1n+p1, XH(A, D), xl, XH(B, D), yl))) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +V2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +V4 = RD.Nat.pow2(S4(D))
  +V8 = RD.Nat.pow2(3n+Nat.add(D, D))
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +e2 : {V2 == Nat.add(V, V) : Nat} = Y.Nat.double_add(V)
  +e4 : {V4 == Nat.add(V2, V2) : Nat} = Y.Nat.double_add(V2)
  +e8 : {V8 == Nat.add(V4, V4) : Nat} = Y.Nat.double_add(V4)
  +env : List<&2, Nat> = [H, P, V, V2, V4, V8]
  +sm = Nat.add(Nat.add(Nat.add(V2, V4), Nat.add(V4, 0n)), V4)
  +bd : {RD.Nat.lt(sm, Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool} =
    Eta4(1n+p1, XH(A, D), xl, XH(B, D), yl, V2, V4, V4, 0n, V4, Zx.exact(p1, A, B, D, xl, yl, Hp2(p1, hp), hA1, hA, hB1, hB, hx, hy), he1, G.e2(p1, B, D, xl, hB, hx),
      S2.e3(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2), Le.fq(RD.Int.mag(M.e4(1n+p1, XH(A, D), xl, XH(B, D), yl)), 0n, h4), G.x(D, xl, yl, hx, hy))
  +es : {Nat.mul(5n, V4) == Nat.add(sm, Nat.add(V4, V2)) : Nat} = R.NatN.eq2(env, R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), N.TZero{}))))), R.Ad(R.Ad(R.Ad(R.Ad(R.V(3n), R.V(4n)), R.Ad(R.V(4n), N.TZero{})), R.V(4n)), R.Ad(R.V(4n), R.V(3n))), [], [], [R.Ad(R.V(4n), R.Ng(R.Ad(R.V(3n), R.V(3n))))], {==}, Unit{}, (R.NatN.z(env, R.V(4n), R.Ad(R.V(3n), R.V(3n)), {==}, {==}, e4), Unit{}), {==}, {==})
  E.Le.trans(Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl))), sm, Nat.mul(5n, V4), bd,
    E.Le.trans(sm, Nat.add(sm, Nat.add(V4, V2)), Nat.mul(5n, V4), E.Le.add(sm, Nat.add(V4, V2)), E.Le.eq(Nat.add(sm, Nat.add(V4, V2)), Nat.mul(5n, V4), Equal.sym(Nat, Nat.mul(5n, V4), Nat.add(sm, Nat.add(V4, V2)), es))))

def Tot20(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +h3: {RD.Nat.lt(0n, RD.Int.mag(M.e3(1n+p1, XH(A, D), xl, XH(B, D), yl))) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +V2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +V4 = RD.Nat.pow2(S4(D))
  +V8 = RD.Nat.pow2(3n+Nat.add(D, D))
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +e2 : {V2 == Nat.add(V, V) : Nat} = Y.Nat.double_add(V)
  +e4 : {V4 == Nat.add(V2, V2) : Nat} = Y.Nat.double_add(V2)
  +e8 : {V8 == Nat.add(V4, V4) : Nat} = Y.Nat.double_add(V4)
  +env : List<&2, Nat> = [H, P, V, V2, V4, V8]
  +sm = Nat.add(Nat.add(Nat.add(V4, V4), Nat.add(0n, V8)), V4)
  +bd : {RD.Nat.lt(sm, Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool} =
    Eta4(1n+p1, XH(A, D), xl, XH(B, D), yl, V4, V4, 0n, V8, V4, Zx.exact(p1, A, B, D, xl, yl, Hp2(p1, hp), hA1, hA, hB1, hB, hx, hy), G.e1(p1, A, D, yl, hA, hy), G.e2(p1, B, D, xl, hB, hx),
      Le.fq(RD.Int.mag(M.e3(1n+p1, XH(A, D), xl, XH(B, D), yl)), 0n, h3), G.e4(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs), G.x(D, xl, yl, hx, hy))
  +es : {sm == Nat.mul(5n, V4) : Nat} = R.NatN.eq2(env, R.Ad(R.Ad(R.Ad(R.V(4n), R.V(4n)), R.Ad(N.TZero{}, R.V(5n))), R.V(4n)), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), N.TZero{}))))), [], [], [R.Ad(R.V(5n), R.Ng(R.Ad(R.V(4n), R.V(4n))))], {==}, Unit{}, (R.NatN.z(env, R.V(5n), R.Ad(R.V(4n), R.V(4n)), {==}, {==}, e8), Unit{}), {==}, {==})
  E.Le.trans(Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl))), sm, Nat.mul(5n, V4), bd, E.Le.eq(sm, Nat.mul(5n, V4), es))

# cl2 a multiple of 4u²: cl1 + cl2 is exact
def E4.zero(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +b: I.Int, +hc: {M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl) == D.Int.sh(S4(D), b) : I.Int})
  -> {RD.Nat.lt(0n, RD.Int.mag(M.e4(1n+p1, XH(A, D), xl, XH(B, D), yl))) == False{} : Bool}:
  +p : Nat = 1n+p1
  +k = S4(D)
  +c1 = M.cl1(1n+p1, XH(A, D), XH(B, D))
  +c2 = M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)
  +a = W1(p, A, B)
  +PV4 = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(S4(D)))
  +ecc : {I.Int.add(c1, c2) == I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)) : I.Int} = Equal.trans(I.Int, I.Int.add(c1, c2), I.Int.add(D.Int.sh(k, a), c2), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)),
    Equal.cong(I.Int, I.Int, w => I.Int.add(w, c2), c1, D.Int.sh(k, a), Cl1.sh(p, A, B, D)),
    Equal.cong(I.Int, I.Int, w => I.Int.add(D.Int.sh(k, a), w), c2, D.Int.sh(k, b), hc))
  +h4 : {RD.Nat.lt(PV4, RD.Int.mag(I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)))) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(PV4, RD.Int.mag(I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)))), RD.Nat.lt(PV4, RD.Int.mag(I.Int.add(c1, c2))), False{},
    Equal.cong(I.Int, Bool, w => RD.Nat.lt(PV4, RD.Int.mag(w)), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), I.Int.add(c1, c2), Equal.sym(I.Int, I.Int.add(c1, c2), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), ecc)),
    SC.c12(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs))
  +exc : {E.RNi(p, I.Int.add(c1, c2)) == I.Int.add(c1, c2) : I.Int} = Equal.trans(I.Int, E.RNi(p, I.Int.add(c1, c2)), E.RNi(p, I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b))), I.Int.add(c1, c2),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(c1, c2), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), ecc),
    Equal.trans(I.Int, E.RNi(p, I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b))), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), I.Int.add(c1, c2), Ex.sum(p1, k, a, b, h4), Equal.sym(I.Int, I.Int.add(c1, c2), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), ecc)))
  Err.z(p, I.Int.add(c1, c2), exc)

# S2c-ii: |tl1|, |tl2| >= u, multiples of 2u²: their sum, below 2u, is exact
def Sm.S2cii(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hc2: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool},
  +hu1: {RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == False{} : Bool}, +hu2: {RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  +p : Nat = 1n+p1
  +k : Nat = 1n+Nat.add(D, D)
  +u1 = I.Int.mul(XH(A, D), yl)
  +u2 = I.Int.mul(xl, XH(B, D))
  +r1 = E.Rn(p, RD.Int.mag(u1))
  +r2 = E.Rn(p, RD.Int.mag(u2))
  +g1 : {RD.Nat.lt(r1, Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(r1, Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))), RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))), False{},
    Equal.cong(Nat, Bool, w => RD.Nat.lt(w, Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))), r1, RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Equal.sym(Nat, RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), r1, Mag.sg(u1, r1))), hu1)
  +g2 : {RD.Nat.lt(r2, Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(r2, Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))), RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))), False{},
    Equal.cong(Nat, Bool, w => RD.Nat.lt(w, Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))), r2, RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), Equal.sym(Nat, RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), r2, Mag.sg(u2, r2))), hu2)
  +a = RD.Int.signed(u1, Mq(p1, r1, k))
  +b = RD.Int.signed(u2, Mq(p1, r2, k))
  +es : {I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))) == I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)) : I.Int} = Equal.trans(I.Int, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), I.Int.add(D.Int.sh(k, a), M.tl2(1n+p1, xl, XH(B, D))), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)),
    Equal.cong(I.Int, I.Int, w => I.Int.add(w, M.tl2(1n+p1, xl, XH(B, D))), M.tl1(1n+p1, XH(A, D), yl), D.Int.sh(k, a), Ri.sh(p1, u1, k, g1)),
    Equal.cong(I.Int, I.Int, w => I.Int.add(D.Int.sh(k, a), w), M.tl2(1n+p1, xl, XH(B, D)), D.Int.sh(k, b), Ri.sh(p1, u2, k, g2)))
  +PV2 = Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))
  +hb : {RD.Nat.lt(PV2, RD.Int.mag(I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)))) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(PV2, RD.Int.mag(I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)))), RD.Nat.lt(PV2, RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))))), False{},
    Equal.cong(I.Int, Bool, w => RD.Nat.lt(PV2, RD.Int.mag(w)), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), Equal.sym(I.Int, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), es)),
    E2.Lt.to_le(RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), PV2, S2.s(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2)))
  +ex : {E.RNi(p, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))) == I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))) : I.Int} = Equal.trans(I.Int, E.RNi(p, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), E.RNi(p, I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b))), I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), es),
    Equal.trans(I.Int, E.RNi(p, I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b))), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), Ex.sum(p1, k, a, b, hb), Equal.sym(I.Int, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)), es)))
  Tot20(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, Err.z(p, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), ex))


# Ties to even: an odd n with 2^p < n < 2^(p+1) is halfway between two
# p-bit neighbours, and rounds to the one that is a multiple of 4
def Mt(+a: Nat) -> Nat:
  Bool.pick(Nat, D.Nat.even(a), D.Nat.half(a), D.Nat.half(1n+a))

def Dbl4(+c: Nat, +h: Nat, +ec: {c == Nat.double(h) : Nat}) -> {Nat.mul(c, RD.Nat.pow2(1n)) == Nat.mul(h, RD.Nat.pow2(2n)) : Nat}:
  Equal.trans(Nat, Nat.mul(c, RD.Nat.pow2(1n)), Nat.mul(Nat.mul(h, RD.Nat.pow2(1n)), RD.Nat.pow2(1n)), Nat.mul(h, RD.Nat.pow2(2n)),
    Equal.cong(Nat, Nat, w => Nat.mul(w, RD.Nat.pow2(1n)), c, Nat.mul(h, RD.Nat.pow2(1n)), Equal.trans(Nat, c, Nat.double(h), Nat.mul(h, RD.Nat.pow2(1n)), ec, Equal.sym(Nat, Nat.mul(h, RD.Nat.pow2(1n)), Nat.double(h), M2(h)))),
    Equal.sym(Nat, Nat.mul(h, RD.Nat.pow2(2n)), Nat.mul(Nat.mul(h, RD.Nat.pow2(1n)), RD.Nat.pow2(1n)), E.Sh.mul(h, 1n, 1n, 2n, {==})))

def Tie.g(+a: Nat, b: Bool, +eb: {D.Nat.even(a) == b : Bool})
  -> {Bool.pick(Nat, Bool.not(b), Nat.mul(1n+a, RD.Nat.pow2(1n)), Nat.mul(a, RD.Nat.pow2(1n))) == Nat.mul(Mt(a), RD.Nat.pow2(2n)) : Nat}:
  match b:
    case True{}:
      +em : {Mt(a) == D.Nat.half(a) : Nat} = Equal.cong(Bool, Nat, v => Bool.pick(Nat, v, D.Nat.half(a), D.Nat.half(1n+a)), D.Nat.even(a), True{}, eb)
      Equal.trans(Nat, Nat.mul(a, RD.Nat.pow2(1n)), Nat.mul(D.Nat.half(a), RD.Nat.pow2(2n)), Nat.mul(Mt(a), RD.Nat.pow2(2n)),
        Dbl4(a, D.Nat.half(a), Y.Nat.even_split(a)(eb)),
        Equal.cong(Nat, Nat, w => Nat.mul(w, RD.Nat.pow2(2n)), D.Nat.half(a), Mt(a), Equal.sym(Nat, Mt(a), D.Nat.half(a), em)))
    case False{}:
      +em : {Mt(a) == D.Nat.half(1n+a) : Nat} = Equal.cong(Bool, Nat, v => Bool.pick(Nat, v, D.Nat.half(a), D.Nat.half(1n+a)), D.Nat.even(a), False{}, eb)
      +e1 : {D.Nat.even(1n+a) == True{} : Bool} = Equal.trans(Bool, D.Nat.even(1n+a), Bool.not(D.Nat.even(a)), True{}, Y.Nat.even_succ(a),
        Equal.cong(Bool, Bool, v => Bool.not(v), D.Nat.even(a), False{}, eb))
      Equal.trans(Nat, Nat.mul(1n+a, RD.Nat.pow2(1n)), Nat.mul(D.Nat.half(1n+a), RD.Nat.pow2(2n)), Nat.mul(Mt(a), RD.Nat.pow2(2n)),
        Dbl4(1n+a, D.Nat.half(1n+a), Y.Nat.even_split(1n+a)(e1)),
        Equal.cong(Nat, Nat, w => Nat.mul(w, RD.Nat.pow2(2n)), D.Nat.half(1n+a), Mt(a), Equal.sym(Nat, Mt(a), D.Nat.half(1n+a), em)))

def Tie(+p1: Nat, +n: Nat, +hlo: {RD.Nat.lt(RD.Nat.pow2(1n+p1), n) == True{} : Bool}, +hhi: {RD.Nat.lt(n, Nat.double(RD.Nat.pow2(1n+p1))) == True{} : Bool},
  +ho: {D.Nat.even(n) == False{} : Bool})
  -> {E.Rn(1n+p1, n) == Nat.mul(Mt(D.Nat.half(n)), RD.Nat.pow2(2n)) : Nat}:
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +a = D.Nat.half(n)
  +da = Nat.double(a)
  +en : {n == 1n+da : Nat} = Y.Nat.odd_split(n)(ho)
  +ef : {n == Nat.add(Nat.mul(a, RD.Nat.pow2(1n)), 1n) : Nat} = Equal.trans(Nat, n, 1n+da, Nat.add(Nat.mul(a, RD.Nat.pow2(1n)), 1n), en,
    Equal.trans(Nat, 1n+da, Nat.add(da, 1n), Nat.add(Nat.mul(a, RD.Nat.pow2(1n)), 1n), NL.Nat.add_comm(1n, da),
      Equal.cong(Nat, Nat, w => Nat.add(w, 1n), da, Nat.mul(a, RD.Nat.pow2(1n)), Equal.sym(Nat, Nat.mul(a, RD.Nat.pow2(1n)), da, M2(a)))))
  +l1 : {RD.Nat.lt(P, 1n+da) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(P, 1n+da), RD.Nat.lt(P, n), True{}, Equal.cong(Nat, Bool, w => RD.Nat.lt(P, w), 1n+da, n, Equal.sym(Nat, n, 1n+da, en)), hlo)
  +hl : {RD.Nat.lt(a, H) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(a, H), RD.Nat.lt(da, Nat.double(H)), False{}, Equal.sym(Bool, RD.Nat.lt(da, Nat.double(H)), RD.Nat.lt(a, H), E.Lt.dd(a, H)), E2.Le.of_lt1(P, da, l1))
  +l2 : {RD.Nat.lt(1n+da, Nat.double(P)) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(1n+da, Nat.double(P)), RD.Nat.lt(n, Nat.double(P)), True{}, Equal.cong(Nat, Bool, w => RD.Nat.lt(w, Nat.double(P)), 1n+da, n, Equal.sym(Nat, n, 1n+da, en)), hhi)
  +hh : {RD.Nat.lt(a, P) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(a, P), RD.Nat.lt(da, Nat.double(P)), True{}, Equal.sym(Bool, RD.Nat.lt(da, Nat.double(P)), RD.Nat.lt(a, P), E.Lt.dd(a, P)),
    E2.Lt.le_trans(da, 1n+da, Nat.double(P), E2.Lt.succ(da), E2.Lt.to_le(1n+da, Nat.double(P), l2)))
  Equal.trans(Nat, E.Rn(1n+p1, n), E.Rn(1n+p1, Nat.add(Nat.mul(a, RD.Nat.pow2(1n)), 1n)), Nat.mul(Mt(a), RD.Nat.pow2(2n)),
    Equal.cong(Nat, Nat, w => E.Rn(1n+p1, w), n, Nat.add(Nat.mul(a, RD.Nat.pow2(1n)), 1n), ef),
    Equal.trans(Nat, E.Rn(1n+p1, Nat.add(Nat.mul(a, RD.Nat.pow2(1n)), 1n)), P3.RnF(a, 1n, 1n), Nat.mul(Mt(a), RD.Nat.pow2(2n)),
      P3.Rn.at(p1, a, 1n, 1n, hl, hh, {==}), Tie.g(a, D.Nat.even(a), {==})))

# S2c-i: |tl1| >= u/2, |tl2| >= u/2 (multiples of u²), |tl1| < u (|e1| <= u²/2):
# tl1 + tl2 = n u² with n < 2^(p+1); exact if n is even or n <= 2^p, and
# otherwise a tie that rounds to a multiple of 4u², making e4 = 0
def S2ci.odd(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hc2: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool},
  +he1: {RD.Nat.lt(RD.Nat.pow2(1n+Nat.add(D, D)), Fq(RD.Int.mag(M.e1(1n+p1, XH(A, D), yl)))) == False{} : Bool}, +w: I.Int, +esw: {I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))) == D.Int.sh(Nat.add(D, D), w) : I.Int},
  +hn2: {RD.Nat.lt(RD.Int.mag(w), Nat.double(RD.Nat.pow2(1n+p1))) == True{} : Bool}, +ho: {D.Nat.even(RD.Int.mag(w)) == False{} : Bool},
  l: Bool, +el: {RD.Nat.lt(RD.Nat.pow2(1n+p1), RD.Int.mag(w)) == l : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  match l:
    case False{}:
      +k0 = Nat.add(D, D)
      +n = RD.Int.mag(w)
      +en : {RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))) == Nat.mul(n, RD.Nat.pow2(Nat.add(D, D))) : Nat} = Equal.trans(Nat, RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), RD.Int.mag(D.Int.sh(k0, w)), Nat.mul(n, RD.Nat.pow2(Nat.add(D, D))),
        Equal.cong(I.Int, Nat, v => RD.Int.mag(v), I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), D.Int.sh(k0, w), esw), E.Sh.mag(k0, w))
      Tot18(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, he1, Err.z(1n+p1, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), E2.Px(p1, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), n, k0, en, el)))
    case True{}:
      +p : Nat = 1n+p1
      +k0 = Nat.add(D, D)
      +n = RD.Int.mag(w)
      +s = I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))
      +m = Mt(D.Nat.half(n))
      +en : {RD.Int.mag(s) == Nat.mul(n, RD.Nat.pow2(Nat.add(D, D))) : Nat} = Equal.trans(Nat, RD.Int.mag(s), RD.Int.mag(D.Int.sh(k0, w)), Nat.mul(n, RD.Nat.pow2(Nat.add(D, D))),
        Equal.cong(I.Int, Nat, v => RD.Int.mag(v), s, D.Int.sh(k0, w), esw), E.Sh.mag(k0, w))
      +er : {E.Rn(p, RD.Int.mag(s)) == Nat.mul(m, RD.Nat.pow2(S4(D))) : Nat} = Equal.trans(Nat, E.Rn(p, RD.Int.mag(s)), E.Rn(p, Nat.mul(n, RD.Nat.pow2(Nat.add(D, D)))), Nat.mul(m, RD.Nat.pow2(S4(D))),
        Equal.cong(Nat, Nat, v => E.Rn(p, v), RD.Int.mag(s), Nat.mul(n, RD.Nat.pow2(Nat.add(D, D))), en),
        Equal.trans(Nat, E.Rn(p, Nat.mul(n, RD.Nat.pow2(Nat.add(D, D)))), Nat.mul(E.Rn(p, n), RD.Nat.pow2(Nat.add(D, D))), Nat.mul(m, RD.Nat.pow2(S4(D))), Rn.sc(p, n, k0),
          Equal.trans(Nat, Nat.mul(E.Rn(p, n), RD.Nat.pow2(Nat.add(D, D))), Nat.mul(Nat.mul(m, RD.Nat.pow2(2n)), RD.Nat.pow2(Nat.add(D, D))), Nat.mul(m, RD.Nat.pow2(S4(D))),
            Equal.cong(Nat, Nat, v => Nat.mul(v, RD.Nat.pow2(Nat.add(D, D))), E.Rn(p, n), Nat.mul(m, RD.Nat.pow2(2n)), Tie(p1, n, el, hn2, ho)),
            Equal.trans(Nat, Nat.mul(Nat.mul(m, RD.Nat.pow2(2n)), RD.Nat.pow2(Nat.add(D, D))), Nat.mul(m, Nat.mul(RD.Nat.pow2(2n), RD.Nat.pow2(Nat.add(D, D)))), Nat.mul(m, RD.Nat.pow2(S4(D))), NL.Nat.mul_assoc(m, RD.Nat.pow2(2n), RD.Nat.pow2(Nat.add(D, D))),
              Equal.cong(Nat, Nat, v => Nat.mul(m, v), Nat.mul(RD.Nat.pow2(2n), RD.Nat.pow2(Nat.add(D, D))), RD.Nat.pow2(S4(D)), Equal.sym(Nat, RD.Nat.pow2(Nat.add(2n, k0)), Nat.mul(RD.Nat.pow2(2n), RD.Nat.pow2(Nat.add(D, D))), BP.Pow2.add(2n, k0)))))))
      +hcl : {M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl) == D.Int.sh(S4(D), RD.Int.signed(s, m)) : I.Int} = Equal.trans(I.Int, M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl), RD.Int.signed(s, Nat.mul(m, RD.Nat.pow2(S4(D)))), D.Int.sh(S4(D), RD.Int.signed(s, m)),
        Equal.cong(Nat, I.Int, v => RD.Int.signed(s, v), E.Rn(p, RD.Int.mag(s)), Nat.mul(m, RD.Nat.pow2(S4(D))), er),
        Equal.sym(I.Int, D.Int.sh(S4(D), RD.Int.signed(s, m)), RD.Int.signed(s, Nat.mul(m, RD.Nat.pow2(S4(D)))), E.Sh.signed(S4(D), s, m)))
      Tot14(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2, he1, E4.zero(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, RD.Int.signed(s, m), hcl))

def S2ci.par(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hc2: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool},
  +he1: {RD.Nat.lt(RD.Nat.pow2(1n+Nat.add(D, D)), Fq(RD.Int.mag(M.e1(1n+p1, XH(A, D), yl)))) == False{} : Bool}, +w: I.Int, +esw: {I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))) == D.Int.sh(Nat.add(D, D), w) : I.Int},
  +hn2: {RD.Nat.lt(RD.Int.mag(w), Nat.double(RD.Nat.pow2(1n+p1))) == True{} : Bool}, b: Bool, +eb: {D.Nat.even(RD.Int.mag(w)) == b : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  match b:
    case True{}:
      +k0 = Nat.add(D, D)
      +n = RD.Int.mag(w)
      +h = D.Nat.half(n)
      +eh : {n == Nat.double(h) : Nat} = Y.Nat.even_split(n)(eb)
      +en : {RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))) == Nat.mul(h, RD.Nat.pow2(1n+Nat.add(D, D))) : Nat} = Equal.trans(Nat, RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), Nat.mul(n, RD.Nat.pow2(Nat.add(D, D))), Nat.mul(h, RD.Nat.pow2(1n+Nat.add(D, D))),
        Equal.trans(Nat, RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), RD.Int.mag(D.Int.sh(k0, w)), Nat.mul(n, RD.Nat.pow2(Nat.add(D, D))), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), D.Int.sh(k0, w), esw), E.Sh.mag(k0, w)),
        Equal.trans(Nat, Nat.mul(n, RD.Nat.pow2(Nat.add(D, D))), Nat.mul(Nat.double(h), RD.Nat.pow2(Nat.add(D, D))), Nat.mul(h, RD.Nat.pow2(1n+Nat.add(D, D))), Equal.cong(Nat, Nat, v => Nat.mul(v, RD.Nat.pow2(Nat.add(D, D))), n, Nat.double(h), eh),
          Equal.trans(Nat, Nat.mul(Nat.double(h), RD.Nat.pow2(Nat.add(D, D))), Nat.double(Nat.mul(h, RD.Nat.pow2(Nat.add(D, D)))), Nat.mul(h, RD.Nat.pow2(1n+Nat.add(D, D))), BP.Mul.dbl_l(h, RD.Nat.pow2(Nat.add(D, D))), Equal.sym(Nat, Nat.mul(h, RD.Nat.pow2(1n+Nat.add(D, D))), Nat.double(Nat.mul(h, RD.Nat.pow2(Nat.add(D, D)))), R.Nat.mul_double(h, RD.Nat.pow2(Nat.add(D, D)))))))
      +hh : {RD.Nat.lt(h, RD.Nat.pow2(1n+p1)) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(h, RD.Nat.pow2(1n+p1)), RD.Nat.lt(Nat.double(h), Nat.double(RD.Nat.pow2(1n+p1))), True{}, Equal.sym(Bool, RD.Nat.lt(Nat.double(h), Nat.double(RD.Nat.pow2(1n+p1))), RD.Nat.lt(h, RD.Nat.pow2(1n+p1)), E.Lt.dd(h, RD.Nat.pow2(1n+p1))),
        Equal.trans(Bool, RD.Nat.lt(Nat.double(h), Nat.double(RD.Nat.pow2(1n+p1))), RD.Nat.lt(n, Nat.double(RD.Nat.pow2(1n+p1))), True{}, Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.double(RD.Nat.pow2(1n+p1))), Nat.double(h), n, Equal.sym(Nat, n, Nat.double(h), eh)), hn2))
      Tot18(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, he1, Err.z(1n+p1, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), E2.Px(p1, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), h, 1n+k0, en, E2.Lt.to_le(h, RD.Nat.pow2(1n+p1), hh))))
    case False{}:
      S2ci.odd(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2, he1, w, esw, hn2, eb, RD.Nat.lt(RD.Nat.pow2(1n+p1), RD.Int.mag(w)), {==})

def Sm.S2ci(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hc2: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool},
  +ht1: {RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D)))) == False{} : Bool}, +ht2: {RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D)))) == False{} : Bool},
  +hu1: {RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +V2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +V4 = RD.Nat.pow2(S4(D))
  +V8 = RD.Nat.pow2(3n+Nat.add(D, D))
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +e2 : {V2 == Nat.add(V, V) : Nat} = Y.Nat.double_add(V)
  +e4 : {V4 == Nat.add(V2, V2) : Nat} = Y.Nat.double_add(V2)
  +e8 : {V8 == Nat.add(V4, V4) : Nat} = Y.Nat.double_add(V4)
  +env : List<&2, Nat> = [H, P, V, V2, V4, V8]
  +p : Nat = 1n+p1
  +k0 = Nat.add(D, D)
  +u1 = I.Int.mul(XH(A, D), yl)
  +u2 = I.Int.mul(xl, XH(B, D))
  +r1 = E.Rn(p, RD.Int.mag(u1))
  +r2 = E.Rn(p, RD.Int.mag(u2))
  # |e1| <= u²/2
  +HV2 = Nat.mul(H, V2)
  +fH2 : {E.Rn(p, HV2) == HV2 : Nat} = Rn.fix(p1, HV2, H, 1n+k0, {==}, E2.Lt.to_le(H, P, E2.Lt.dself(H, BP.Pow2.pos(p1))))
  +ehv : {HV2 == Nat.mul(P, V) : Nat} = R.NatN.eq(env, R.Ml(R.V(0n), R.V(3n)), R.Ml(R.V(1n), R.V(2n)), [R.Ng(R.V(2n)), R.V(0n)], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.V(3n), R.Ng(R.Ad(R.V(2n), R.V(2n))))], {==}, (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, eP), (R.NatN.z(env, R.V(3n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, e2), Unit{})), {==}, {==})
  +lu : {RD.Nat.lt(Nat.mul(P, V), RD.Int.mag(u1)) == False{} : Bool} = E.Le.trans(RD.Int.mag(u1), HV2, Nat.mul(P, V), E2.Lt.to_le(RD.Int.mag(u1), HV2, RL.c(p1, u1, HV2, fH2, hu1)), E.Le.eq(HV2, Nat.mul(P, V), ehv))
  +he1 : {RD.Nat.lt(V2, Fq(RD.Int.mag(M.e1(1n+p1, XH(A, D), yl)))) == False{} : Bool} = E.Le.dd(Nat.double(RD.Int.mag(M.e1(1n+p1, XH(A, D), yl))), V, EB(p1, u1, k0, lu))
  # tl1, tl2 are multiples of u²
  +g1 : {RD.Nat.lt(r1, Nat.mul(H, V)) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(r1, Nat.mul(H, V)), RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(H, V)), False{},
    Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.mul(H, V)), r1, RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Equal.sym(Nat, RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), r1, Mag.sg(u1, r1))), ht1)
  +g2 : {RD.Nat.lt(r2, Nat.mul(H, V)) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(r2, Nat.mul(H, V)), RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), Nat.mul(H, V)), False{},
    Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.mul(H, V)), r2, RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), Equal.sym(Nat, RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), r2, Mag.sg(u2, r2))), ht2)
  +a = RD.Int.signed(u1, Mq(p1, r1, k0))
  +b = RD.Int.signed(u2, Mq(p1, r2, k0))
  +w = I.Int.add(a, b)
  +esw : {I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))) == D.Int.sh(k0, w) : I.Int} = Equal.trans(I.Int, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), I.Int.add(D.Int.sh(k0, a), D.Int.sh(k0, b)), D.Int.sh(k0, w),
    Equal.trans(I.Int, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), I.Int.add(D.Int.sh(k0, a), M.tl2(1n+p1, xl, XH(B, D))), I.Int.add(D.Int.sh(k0, a), D.Int.sh(k0, b)),
      Equal.cong(I.Int, I.Int, v => I.Int.add(v, M.tl2(1n+p1, xl, XH(B, D))), M.tl1(1n+p1, XH(A, D), yl), D.Int.sh(k0, a), Ri.sh(p1, u1, k0, g1)),
      Equal.cong(I.Int, I.Int, v => I.Int.add(D.Int.sh(k0, a), v), M.tl2(1n+p1, xl, XH(B, D)), D.Int.sh(k0, b), Ri.sh(p1, u2, k0, g2))),
    Equal.sym(I.Int, D.Int.sh(k0, w), I.Int.add(D.Int.sh(k0, a), D.Int.sh(k0, b)), Y.Int.sh_add(k0, a, b)))
  # |tl1 + tl2| < 2u: n < 2^(p+1)
  +n = RD.Int.mag(w)
  +Q = Nat.double(P)
  +eq : {Q == Nat.add(P, P) : Nat} = Y.Nat.double_add(P)
  +envq : List<&2, Nat> = [P, V, V2, Q]
  +epq : {Nat.mul(P, V2) == Nat.mul(Q, V) : Nat} = R.NatN.eq(envq, R.Ml(R.V(0n), R.V(2n)), R.Ml(R.V(3n), R.V(1n)), [R.V(0n), R.Ng(R.V(1n))], [R.Ad(R.V(2n), R.Ng(R.Ad(R.V(1n), R.V(1n)))), R.Ad(R.V(3n), R.Ng(R.Ad(R.V(0n), R.V(0n))))], {==}, (R.NatN.z(envq, R.V(2n), R.Ad(R.V(1n), R.V(1n)), {==}, {==}, e2), (R.NatN.z(envq, R.V(3n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, eq), Unit{})), {==}, {==})
  +ens : {RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))) == Nat.mul(n, V) : Nat} = Equal.trans(Nat, RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), RD.Int.mag(D.Int.sh(k0, w)), Nat.mul(n, V), Equal.cong(I.Int, Nat, v => RD.Int.mag(v), I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))), D.Int.sh(k0, w), esw), E.Sh.mag(k0, w))
  +hn2 : {RD.Nat.lt(n, Q) == True{} : Bool} = E.Lt.cancel(n, Q, V,
    Equal.trans(Bool, RD.Nat.lt(Nat.mul(n, V), Nat.mul(Q, V)), RD.Nat.lt(RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), Nat.mul(P, V2)), True{},
      Equal.trans(Bool, RD.Nat.lt(Nat.mul(n, V), Nat.mul(Q, V)), RD.Nat.lt(RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), Nat.mul(Q, V)), RD.Nat.lt(RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), Nat.mul(P, V2)),
        Equal.cong(Nat, Bool, v => RD.Nat.lt(v, Nat.mul(Q, V)), Nat.mul(n, V), RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), Equal.sym(Nat, RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), Nat.mul(n, V), ens)),
        Equal.cong(Nat, Bool, v => RD.Nat.lt(RD.Int.mag(I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D)))), v), Nat.mul(Q, V), Nat.mul(P, V2), Equal.sym(Nat, Nat.mul(P, V2), Nat.mul(Q, V), epq))),
      S2.s(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2)))
  S2ci.par(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2, he1, w, esw, hn2, D.Nat.even(n), {==})

# the cases on |cl2|, |tl1| and |tl2|: 4 |eta| <= 20u² whenever xh yh < 2
def Sm.e(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hc2: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool},
  +ht1: {RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D)))) == False{} : Bool}, +ht2: {RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D)))) == False{} : Bool},
  +hu1: {RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == False{} : Bool}, l: Bool, +el: {RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == l : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  match l:
    case True{}:
      Swap.eta(p1, A, B, D, xl, yl, Nat.mul(5n, RD.Nat.pow2(S4(D))), Sm.S2ci(p1, B, A, D, yl, xl, hp, hB1, hB, hA1, hA, hy, hx, Swap.hs(p1, A, B, hs),
        Swap.c2(p1, A, B, D, xl, yl, Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D))), True{}, hc2), Swap.t2(p1, B, D, xl, Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D))), False{}, ht2), Swap.t1(p1, A, D, yl, Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D))), False{}, ht1),
        Swap.t2(p1, B, D, xl, Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D))), True{}, el)))
    case False{}:
      Sm.S2cii(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2, hu1, el)

def Sm.d(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hc2: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool},
  +ht1: {RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D)))) == False{} : Bool}, +ht2: {RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D)))) == False{} : Bool},
  l: Bool, +el: {RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == l : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  match l:
    case True{}:
      Sm.S2ci(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2, ht1, ht2, el)
    case False{}:
      Sm.e(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2, ht1, ht2, el, RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))), {==})

def Sm.c(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hc2: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool},
  +ht1: {RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D)))) == False{} : Bool}, l: Bool, +el: {RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D)))) == l : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  match l:
    case True{}:
      Sm.S2b(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2, el)
    case False{}:
      Sm.d(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2, ht1, el, RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(1n+Nat.add(D, D)))), {==})

def Sm.b(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hc2: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == True{} : Bool},
  l: Bool, +el: {RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D)))) == l : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  match l:
    case True{}:
      Sm.S2a(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2, el)
    case False{}:
      Sm.c(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hc2, el, RD.Nat.lt(RD.Int.mag(M.tl2(1n+p1, xl, XH(B, D))), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D)))), {==})

def Sm.a(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, l: Bool, +el: {RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))) == l : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  match l:
    case False{}:
      Sm.S1(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, el)
    case True{}:
      Sm.b(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, el, RD.Nat.lt(RD.Int.mag(M.tl1(1n+p1, XH(A, D), yl)), Nat.mul(RD.Nat.pow2(p1), RD.Nat.pow2(Nat.add(D, D)))), {==})

def Small.abs(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  Sm.a(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, RD.Nat.lt(RD.Int.mag(M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(1n+Nat.add(D, D)))), {==})


# Relative bounds
# ---------------
# xh = 1 (A = 2^(p-1)): cl1 = 0 and tl1 = xh yl exactly (yl representable),
# so |eta| <= 4u²; |x|, |y| >= 1 - u then give 4u² / (1 - u)² <= 5u² / (1 + u)².
# xh, yh > 1: |x|, |y| >= 1 + u and |eta| <= 5u².

def Fq.mul(k: Nat, +x: Nat) -> {Fq(Nat.mul(k, x)) == Nat.mul(k, Fq(x)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      Equal.trans(Nat, Fq(Nat.add(x, Nat.mul(j, x))), Nat.add(Fq(x), Fq(Nat.mul(j, x))), Nat.add(Fq(x), Nat.mul(j, Fq(x))),
        Fq.add(x, Nat.mul(j, x)), Equal.cong(Nat, Nat, w => Nat.add(Fq(x), w), Fq(Nat.mul(j, x)), Nat.mul(j, Fq(x)), Fq.mul(j, x)))

def Le.unfq(+a: Nat, +b: Nat, +h: {RD.Nat.lt(Fq(b), Fq(a)) == False{} : Bool}) -> {RD.Nat.lt(b, a) == False{} : Bool}:
  Le.halve(a, b, Le.halve(Nat.double(a), Nat.double(b), h))

# xh = 1: |eta| <= 4u²
def Case.one(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hAH: {A == RD.Nat.pow2(p1) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat})
  -> {RD.Nat.lt(Nat.mul(4n, RD.Nat.pow2(S4(D))), Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +V2 = RD.Nat.pow2(1n+Nat.add(D, D))
  +V4 = RD.Nat.pow2(S4(D))
  +V8 = RD.Nat.pow2(3n+Nat.add(D, D))
  +eP : {P == Nat.add(H, H) : Nat} = Y.Nat.double_add(H)
  +e2 : {V2 == Nat.add(V, V) : Nat} = Y.Nat.double_add(V)
  +e4 : {V4 == Nat.add(V2, V2) : Nat} = Y.Nat.double_add(V2)
  +e8 : {V8 == Nat.add(V4, V4) : Nat} = Y.Nat.double_add(V4)
  +env : List<&2, Nat> = [H, P, V, V2, V4, V8]
  +p : Nat = 1n+p1
  +y = RD.Int.mag(yl)
  +W2 = RD.Nat.pow2(1n+D)
  +k = Nat.add(p1, 1n+D)
  # e1 = 0: xh yl = yl 2^k
  +t1 = I.Int.mul(XH(A, D), yl)
  +et : {RD.Int.mag(t1) == Nat.mul(y, RD.Nat.pow2(k)) : Nat} = Equal.trans(Nat, RD.Int.mag(t1), Nat.mul(Nat.mul(A, W2), y), Nat.mul(y, RD.Nat.pow2(k)), TL1.mag(A, D, yl),
    Equal.trans(Nat, Nat.mul(Nat.mul(A, W2), y), Nat.mul(Nat.mul(H, W2), y), Nat.mul(y, RD.Nat.pow2(k)), Equal.cong(Nat, Nat, v => Nat.mul(Nat.mul(v, W2), y), A, H, hAH),
      Equal.trans(Nat, Nat.mul(Nat.mul(H, W2), y), Nat.mul(y, Nat.mul(H, W2)), Nat.mul(y, RD.Nat.pow2(k)), NL.Nat.mul_comm(Nat.mul(H, W2), y),
        Equal.cong(Nat, Nat, v => Nat.mul(y, v), Nat.mul(H, W2), RD.Nat.pow2(k), Equal.sym(Nat, RD.Nat.pow2(k), Nat.mul(H, W2), BP.Pow2.add(p1, 1n+D))))))
  +ft : {E.Rn(p, RD.Int.mag(t1)) == RD.Int.mag(t1) : Nat} = Equal.trans(Nat, E.Rn(p, RD.Int.mag(t1)), E.Rn(p, Nat.mul(y, RD.Nat.pow2(k))), RD.Int.mag(t1),
    Equal.cong(Nat, Nat, v => E.Rn(p, v), RD.Int.mag(t1), Nat.mul(y, RD.Nat.pow2(k)), et),
    Equal.trans(Nat, E.Rn(p, Nat.mul(y, RD.Nat.pow2(k))), Nat.mul(E.Rn(p, y), RD.Nat.pow2(k)), RD.Int.mag(t1), Rn.sc(p, y, k),
      Equal.trans(Nat, Nat.mul(E.Rn(p, y), RD.Nat.pow2(k)), Nat.mul(y, RD.Nat.pow2(k)), RD.Int.mag(t1), Equal.cong(Nat, Nat, v => Nat.mul(v, RD.Nat.pow2(k)), E.Rn(p, y), y, fy),
        Equal.sym(Nat, RD.Int.mag(t1), Nat.mul(y, RD.Nat.pow2(k)), et))))
  +h1 : {RD.Nat.lt(0n, RD.Int.mag(M.e1(1n+p1, XH(A, D), yl))) == False{} : Bool} = Err.z(p, t1, E.RNi.exact(p, t1, ft))
  # e4 = 0: xh yh = yh is exact, so cl1 = 0 and cl1 + cl2 = cl2
  +AB = Nat.mul(A, B)
  +fab : {E.Rn(p, AB) == AB : Nat} = Rn.fix(p1, AB, B, p1, Equal.trans(Nat, AB, Nat.mul(H, B), Nat.mul(B, H), Equal.cong(Nat, Nat, v => Nat.mul(v, B), A, H, hAH), NL.Nat.mul_comm(H, B)), E2.Lt.to_le(B, P, hB))
  +envw : List<&2, I.Int> = [I.IPos{AB}]
  +ew : {W1(p, A, B) == I.IPos{0n} : I.Int} = Equal.trans(I.Int, W1(p, A, B), I.Int.add(I.IPos{AB}, I.Int.neg(I.IPos{AB})), I.IPos{0n},
    Equal.cong(Nat, I.Int, v => I.Int.add(I.IPos{AB}, I.Int.neg(I.IPos{v})), E.Rn(p, AB), AB, fab),
    BP.IntN(envw, R.Ad(R.V(0n), R.Ng(R.V(0n))), N.TZero{}, [], [], {==}, Unit{}))
  +c1 = M.cl1(1n+p1, XH(A, D), XH(B, D))
  +c2 = M.cl2(1n+p1, XH(A, D), xl, XH(B, D), yl)
  +e1z : {c1 == I.IPos{0n} : I.Int} = Equal.trans(I.Int, c1, D.Int.sh(S4(D), W1(p, A, B)), I.IPos{0n}, Cl1.sh(p, A, B, D),
    Equal.trans(I.Int, D.Int.sh(S4(D), W1(p, A, B)), D.Int.sh(S4(D), I.IPos{0n}), I.IPos{0n}, Equal.cong(I.Int, I.Int, v => D.Int.sh(S4(D), v), W1(p, A, B), I.IPos{0n}, ew), Y.Int.sh_zero(S4(D))))
  +envc : List<&2, I.Int> = [c2]
  +ec : {I.Int.add(c1, c2) == c2 : I.Int} = Equal.trans(I.Int, I.Int.add(c1, c2), I.Int.add(I.IPos{0n}, c2), c2, Equal.cong(I.Int, I.Int, v => I.Int.add(v, c2), c1, I.IPos{0n}, e1z),
    BP.IntN(envc, R.Ad(N.TZero{}, R.V(0n)), R.V(0n), [], [], {==}, Unit{}))
  +exc : {E.RNi(p, I.Int.add(c1, c2)) == I.Int.add(c1, c2) : I.Int} = Equal.trans(I.Int, E.RNi(p, I.Int.add(c1, c2)), E.RNi(p, c2), I.Int.add(c1, c2),
    Equal.cong(I.Int, I.Int, v => E.RNi(p, v), I.Int.add(c1, c2), c2, ec),
    Equal.trans(I.Int, E.RNi(p, c2), c2, I.Int.add(c1, c2), E.RNi.exact(p, c2, Rf.i(p1, I.Int.add(M.tl1(1n+p1, XH(A, D), yl), M.tl2(1n+p1, xl, XH(B, D))))), Equal.sym(I.Int, I.Int.add(c1, c2), c2, ec)))
  +h4 : {RD.Nat.lt(0n, RD.Int.mag(M.e4(1n+p1, XH(A, D), xl, XH(B, D), yl))) == False{} : Bool} = Err.z(p, I.Int.add(c1, c2), exc)
  +sm = Nat.add(Nat.add(Nat.add(0n, V4), Nat.add(V8, 0n)), V4)
  +bd : {RD.Nat.lt(sm, Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl)))) == False{} : Bool} =
    Eta4(p, XH(A, D), xl, XH(B, D), yl, 0n, V4, V8, 0n, V4, Zx.exact(p1, A, B, D, xl, yl, Hp2(p1, hp), hA1, hA, hB1, hB, hx, hy),
      Le.fq(RD.Int.mag(M.e1(1n+p1, XH(A, D), yl)), 0n, h1), G.e2(p1, B, D, xl, hB, hx), G.e3(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs), Le.fq(RD.Int.mag(M.e4(1n+p1, XH(A, D), xl, XH(B, D), yl)), 0n, h4), G.x(D, xl, yl, hx, hy))
  +es : {sm == Nat.mul(4n, V4) : Nat} = R.NatN.eq2(env, R.Ad(R.Ad(R.Ad(N.TZero{}, R.V(4n)), R.Ad(R.V(5n), N.TZero{})), R.V(4n)), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), R.Ad(R.V(4n), N.TZero{})))), [], [], [R.Ad(R.V(5n), R.Ng(R.Ad(R.V(4n), R.V(4n))))], {==}, Unit{}, (R.NatN.z(env, R.V(5n), R.Ad(R.V(4n), R.V(4n)), {==}, {==}, e8), Unit{}), {==}, {==})
  E.Le.trans(Fq(RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl))), sm, Nat.mul(4n, V4), bd, E.Le.eq(sm, Nat.mul(4n, V4), es))

# 4 (m + 2)² <= 5 m² once m >= 17
def Num.one(+Pm: Nat, +h17: {RD.Nat.lt(Pm, 17n) == False{} : Bool})
  -> {RD.Nat.lt(Nat.mul(5n, Nat.mul(Pm, Pm)), Nat.mul(4n, Nat.mul(2n+Pm, 2n+Pm))) == False{} : Bool}:
  +kk = RD.Nat.monus(Pm, 17n)
  +ew : {Pm == Nat.add(17n, kk) : Nat} = E.Le.wit(17n, Pm, h17)
  +eok : {Nat.mul(1n, kk) == kk : Nat} = P3.Mul.one_l(kk)
  +eop : {Nat.mul(1n, Pm) == Pm : Nat} = P3.Mul.one_l(Pm)
  +env : List<&2, Nat> = [1n, Pm, kk]
  +L = Nat.mul(4n, Nat.mul(2n+Pm, 2n+Pm))
  +sl = Nat.add(1n, Nat.add(Nat.mul(18n, kk), Nat.mul(kk, kk)))
  +e : {Nat.mul(5n, Nat.mul(Pm, Pm)) == Nat.add(L, sl) : Nat} = R.NatN.eq2(env, R.Ad(R.Ml(R.V(1n), R.V(1n)), R.Ad(R.Ml(R.V(1n), R.V(1n)), R.Ad(R.Ml(R.V(1n), R.V(1n)), R.Ad(R.Ml(R.V(1n), R.V(1n)), R.Ad(R.Ml(R.V(1n), R.V(1n)), N.TZero{}))))), R.Ad(R.Ad(R.Ml(R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n))), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n)))), R.Ad(R.Ml(R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n))), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n)))), R.Ad(R.Ml(R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n))), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n)))), R.Ad(R.Ml(R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n))), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(1n)))), N.TZero{})))), R.Ad(R.V(0n), R.Ad(R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), R.Ad(R.V(2n), N.TZero{})))))))))))))))))), R.Ml(R.V(2n), R.V(2n))))), [R.Ad(R.Ad(R.V(0n), R.V(1n)), R.V(2n))], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(2n))))))))))))))))))))], [R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.V(0n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n))), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ng(R.V(2n)))], {==}, (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.V(2n)))))))))))))))))), {==}, {==}, ew), Unit{}), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.V(0n), {==}, {==}, {==}), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), (R.NatN.z(env, R.Ml(R.V(0n), R.V(2n)), R.V(2n), {==}, {==}, eok), Unit{}))))))))))))))))))), {==}, {==})
  E.Le.trans(L, Nat.add(L, sl), Nat.mul(5n, Nat.mul(Pm, Pm)), E.Le.add(L, sl), E.Le.eq(Nat.add(L, sl), Nat.mul(5n, Nat.mul(Pm, Pm)), Equal.sym(Nat, Nat.mul(5n, Nat.mul(Pm, Pm)), Nat.add(L, sl), e)))

def P64(+p1: Nat, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool}) -> {RD.Nat.lt(RD.Nat.pow2(1n+p1), 64n) == False{} : Bool}:
  E2.Pow2.mono(6n, 1n+p1, hp)

# xh, yh > 1, xh yh < 2
def Rel.small(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hA2: {RD.Nat.lt(RD.Nat.pow2(p1), A) == True{} : Bool}, +hB2: {RD.Nat.lt(RD.Nat.pow2(p1), B) == True{} : Bool})
  -> {Rel(p1, A, B, D, xl, yl) == False{} : Bool}:
  +p : Nat = 1n+p1
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +W = RD.Nat.pow2(D)
  +Pp : Nat = 1n+P
  +me = RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl))
  +x = I.Int.add(XH(A, D), xl)
  +y = I.Int.add(XH(B, D), yl)
  +X = RD.Int.mag(x)
  +Yv = RD.Int.mag(y)
  +h5 : {RD.Nat.lt(Nat.mul(5n, V), me) == False{} : Bool} = Le.unfq(me, Nat.mul(5n, V),
    E.Le.trans(Fq(me), Nat.mul(5n, Fq(V)), Fq(Nat.mul(5n, V)), Small.abs(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs), E.Le.eq(Nat.mul(5n, Fq(V)), Fq(Nat.mul(5n, V)), Equal.sym(Nat, Fq(Nat.mul(5n, V)), Nat.mul(5n, Fq(V)), Fq.mul(5n, V)))))
  +hX : {RD.Nat.lt(X, Nat.mul(Pp, W)) == False{} : Bool} = X.lo.c(A, D, xl, Pp, hx, E.Le.dd(1n+H, A, E2.Le.succ(H, A, hA2)))
  +hY : {RD.Nat.lt(Yv, Nat.mul(Pp, W)) == False{} : Bool} = X.lo.c(B, D, yl, Pp, hy, E.Le.dd(1n+H, B, E2.Le.succ(H, B, hB2)))
  +ev : {V == Nat.mul(W, W) : Nat} = Vsq(D)
  +env : List<&2, Nat> = [V, W, Pp]
  +e5 : {Nat.mul(Nat.mul(5n, V), Nat.mul(Pp, Pp)) == Nat.mul(5n, Nat.mul(Nat.mul(Pp, W), Nat.mul(Pp, W))) : Nat} = R.NatN.eq(env, R.Ml(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{}))))), R.Ml(R.V(2n), R.V(2n))), R.Ad(R.Ml(R.Ml(R.V(2n), R.V(1n)), R.Ml(R.V(2n), R.V(1n))), R.Ad(R.Ml(R.Ml(R.V(2n), R.V(1n)), R.Ml(R.V(2n), R.V(1n))), R.Ad(R.Ml(R.Ml(R.V(2n), R.V(1n)), R.Ml(R.V(2n), R.V(1n))), R.Ad(R.Ml(R.Ml(R.V(2n), R.V(1n)), R.Ml(R.V(2n), R.V(1n))), R.Ad(R.Ml(R.Ml(R.V(2n), R.V(1n)), R.Ml(R.V(2n), R.V(1n))), N.TZero{}))))), [R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(2n), R.V(2n))), R.Ml(R.V(2n), R.V(2n))), R.Ml(R.V(2n), R.V(2n))), R.Ml(R.V(2n), R.V(2n)))], [R.Ad(R.V(0n), R.Ng(R.Ml(R.V(1n), R.V(1n))))], {==}, (R.NatN.z(env, R.V(0n), R.Ml(R.V(1n), R.V(1n)), {==}, {==}, ev), Unit{}), {==}, {==})
  +XY = Nat.mul(5n, RD.Int.mag(I.Int.mul(x, y)))
  E.Le.trans(Nat.mul(me, Qp(p1)), Nat.mul(Nat.mul(5n, V), Nat.mul(Pp, Pp)), XY, E2.Le.mulr(me, Nat.mul(5n, V), Qp(p1), h5),
    E.Le.trans(Nat.mul(Nat.mul(5n, V), Nat.mul(Pp, Pp)), Nat.mul(5n, Nat.mul(Nat.mul(Pp, W), Nat.mul(Pp, W))), XY, E.Le.eq(Nat.mul(Nat.mul(5n, V), Nat.mul(Pp, Pp)), Nat.mul(5n, Nat.mul(Nat.mul(Pp, W), Nat.mul(Pp, W))), e5),
      E.Le.trans(Nat.mul(5n, Nat.mul(Nat.mul(Pp, W), Nat.mul(Pp, W))), Nat.mul(5n, Nat.mul(X, Yv)), XY, E2.Le.mull(5n, Nat.mul(Nat.mul(Pp, W), Nat.mul(Pp, W)), Nat.mul(X, Yv), E2.Le.mul2(Nat.mul(Pp, W), X, Nat.mul(Pp, W), Yv, hX, hY)),
        E.Le.eq(Nat.mul(5n, Nat.mul(X, Yv)), XY, Equal.cong(Nat, Nat, v => Nat.mul(5n, v), Nat.mul(X, Yv), RD.Int.mag(I.Int.mul(x, y)), Equal.sym(Nat, RD.Int.mag(I.Int.mul(x, y)), Nat.mul(X, Yv), E2.Mag.mul(x, y)))))))

# xh = 1
def Rel.one(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +hAH: {A == RD.Nat.pow2(p1) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat})
  -> {Rel(p1, A, B, D, xl, yl) == False{} : Bool}:
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(1n+p1)
  +V = RD.Nat.pow2(Nat.add(D, D))
  +W = RD.Nat.pow2(D)
  +Pm = RD.Nat.monus(P, 1n)
  +me = RD.Int.mag(M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl))
  +x = I.Int.add(XH(A, D), xl)
  +y = I.Int.add(XH(B, D), yl)
  +X = RD.Int.mag(x)
  +Yv = RD.Int.mag(y)
  +h4 : {RD.Nat.lt(Nat.mul(4n, V), me) == False{} : Bool} = Le.unfq(me, Nat.mul(4n, V),
    E.Le.trans(Fq(me), Nat.mul(4n, Fq(V)), Fq(Nat.mul(4n, V)), Case.one(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hAH, fy), E.Le.eq(Nat.mul(4n, Fq(V)), Fq(Nat.mul(4n, V)), Equal.sym(Nat, Fq(Nat.mul(4n, V)), Nat.mul(4n, Fq(V)), Fq.mul(4n, V)))))
  +eP : {P == 1n+Pm : Nat} = Lt.pos(H, P, E2.Lt.dself(H, BP.Pow2.pos(p1)))
  +lP : {RD.Nat.lt(Nat.double(H), 1n+Pm) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Nat.double(H), 1n+Pm), RD.Nat.lt(P, P), False{},
    Equal.cong(Nat, Bool, v => RD.Nat.lt(P, v), 1n+Pm, P, Equal.sym(Nat, P, 1n+Pm, eP)), E.Lt.irr(P))
  +hX : {RD.Nat.lt(X, Nat.mul(Pm, W)) == False{} : Bool} = X.lo.c(A, D, xl, Pm, hx,
    Equal.trans(Bool, RD.Nat.lt(Nat.double(A), 1n+Pm), RD.Nat.lt(Nat.double(H), 1n+Pm), False{}, Equal.cong(Nat, Bool, v => RD.Nat.lt(Nat.double(v), 1n+Pm), A, H, hAH), lP))
  +hY : {RD.Nat.lt(Yv, Nat.mul(Pm, W)) == False{} : Bool} = X.lo.c(B, D, yl, Pm, hy, E.Le.trans(1n+Pm, Nat.double(H), Nat.double(B), lP, E.Le.dd(H, B, hB1)))
  +h63 : {RD.Nat.lt(Pm, 63n) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(1n+Pm, 64n), RD.Nat.lt(P, 64n), False{}, Equal.cong(Nat, Bool, v => RD.Nat.lt(v, 64n), 1n+Pm, P, Equal.sym(Nat, P, 1n+Pm, eP)), P64(p1, hp))
  +hn : {RD.Nat.lt(Nat.mul(5n, Nat.mul(Pm, Pm)), Nat.mul(4n, Nat.mul(2n+Pm, 2n+Pm))) == False{} : Bool} = Num.one(Pm, E.Le.trans(17n, 63n, Pm, {==}, h63))
  +eQ : {Nat.mul(4n, Nat.mul(1n+P, 1n+P)) == Nat.mul(4n, Nat.mul(2n+Pm, 2n+Pm)) : Nat} = Equal.cong(Nat, Nat, v => Nat.mul(4n, Nat.mul(1n+v, 1n+v)), P, 1n+Pm, eP)
  +ev : {V == Nat.mul(W, W) : Nat} = Vsq(D)
  +Pp : Nat = 1n+P
  +env : List<&2, Nat> = [V, W, Pp]
  +ea : {Nat.mul(Nat.mul(4n, V), Nat.mul(Pp, Pp)) == Nat.mul(V, Nat.mul(4n, Nat.mul(Pp, Pp))) : Nat} = R.NatN.eq(env, R.Ml(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{})))), R.Ml(R.V(2n), R.V(2n))), R.Ml(R.V(0n), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ad(R.Ml(R.V(2n), R.V(2n)), N.TZero{}))))), [], [], {==}, Unit{}, {==}, {==})
  +envm : List<&2, Nat> = [V, W, Pm]
  +eb : {Nat.mul(V, Nat.mul(5n, Nat.mul(Pm, Pm))) == Nat.mul(5n, Nat.mul(Nat.mul(Pm, W), Nat.mul(Pm, W))) : Nat} = R.NatN.eq(envm, R.Ml(R.V(0n), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ad(R.Ml(R.V(2n), R.V(2n)), N.TZero{})))))), R.Ad(R.Ml(R.Ml(R.V(2n), R.V(1n)), R.Ml(R.V(2n), R.V(1n))), R.Ad(R.Ml(R.Ml(R.V(2n), R.V(1n)), R.Ml(R.V(2n), R.V(1n))), R.Ad(R.Ml(R.Ml(R.V(2n), R.V(1n)), R.Ml(R.V(2n), R.V(1n))), R.Ad(R.Ml(R.Ml(R.V(2n), R.V(1n)), R.Ml(R.V(2n), R.V(1n))), R.Ad(R.Ml(R.Ml(R.V(2n), R.V(1n)), R.Ml(R.V(2n), R.V(1n))), N.TZero{}))))), [R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ml(R.V(2n), R.V(2n))), R.Ml(R.V(2n), R.V(2n))), R.Ml(R.V(2n), R.V(2n))), R.Ml(R.V(2n), R.V(2n)))], [R.Ad(R.V(0n), R.Ng(R.Ml(R.V(1n), R.V(1n))))], {==}, (R.NatN.z(envm, R.V(0n), R.Ml(R.V(1n), R.V(1n)), {==}, {==}, ev), Unit{}), {==}, {==})
  +XY = Nat.mul(5n, RD.Int.mag(I.Int.mul(x, y)))
  +Q4 = Nat.mul(V, Nat.mul(4n, Nat.mul(Pp, Pp)))
  +Q5 = Nat.mul(V, Nat.mul(5n, Nat.mul(Pm, Pm)))
  E.Le.trans(Nat.mul(me, Qp(p1)), Nat.mul(Nat.mul(4n, V), Nat.mul(Pp, Pp)), XY, E2.Le.mulr(me, Nat.mul(4n, V), Qp(p1), h4),
    E.Le.trans(Nat.mul(Nat.mul(4n, V), Nat.mul(Pp, Pp)), Q4, XY, E.Le.eq(Nat.mul(Nat.mul(4n, V), Nat.mul(Pp, Pp)), Q4, ea),
      E.Le.trans(Q4, Q5, XY, E2.Le.mull(V, Nat.mul(4n, Nat.mul(Pp, Pp)), Nat.mul(5n, Nat.mul(Pm, Pm)),
          E.Le.trans(Nat.mul(4n, Nat.mul(Pp, Pp)), Nat.mul(4n, Nat.mul(2n+Pm, 2n+Pm)), Nat.mul(5n, Nat.mul(Pm, Pm)), E.Le.eq(Nat.mul(4n, Nat.mul(Pp, Pp)), Nat.mul(4n, Nat.mul(2n+Pm, 2n+Pm)), eQ), hn)),
        E.Le.trans(Q5, Nat.mul(5n, Nat.mul(Nat.mul(Pm, W), Nat.mul(Pm, W))), XY, E.Le.eq(Q5, Nat.mul(5n, Nat.mul(Nat.mul(Pm, W), Nat.mul(Pm, W))), eb),
          E.Le.trans(Nat.mul(5n, Nat.mul(Nat.mul(Pm, W), Nat.mul(Pm, W))), Nat.mul(5n, Nat.mul(X, Yv)), XY, E2.Le.mull(5n, Nat.mul(Nat.mul(Pm, W), Nat.mul(Pm, W)), Nat.mul(X, Yv), E2.Le.mul2(Nat.mul(Pm, W), X, Nat.mul(Pm, W), Yv, hX, hY)),
            E.Le.eq(Nat.mul(5n, Nat.mul(X, Yv)), XY, Equal.cong(Nat, Nat, v => Nat.mul(5n, v), Nat.mul(X, Yv), RD.Int.mag(I.Int.mul(x, y)), Equal.sym(Nat, RD.Int.mag(I.Int.mul(x, y)), Nat.mul(X, Yv), E2.Mag.mul(x, y)))))))))

def Rel.sym(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int) -> {Rel(p1, B, A, D, yl, xl) == Rel(p1, A, B, D, xl, yl) : Bool}:
  +x = I.Int.add(XH(A, D), xl)
  +y = I.Int.add(XH(B, D), yl)
  +es = M.eta(1n+p1, XH(B, D), yl, XH(A, D), xl)
  Equal.trans(Bool, Rel(p1, B, A, D, yl, xl), RD.Nat.lt(Nat.mul(5n, RD.Int.mag(I.Int.mul(x, y))), Nat.mul(RD.Int.mag(es), Qp(p1))), Rel(p1, A, B, D, xl, yl),
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(Nat.mul(5n, RD.Int.mag(v)), Nat.mul(RD.Int.mag(es), Qp(p1))), I.Int.mul(y, x), I.Int.mul(x, y), Z.Int.mul_comm(y, x)),
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(Nat.mul(5n, RD.Int.mag(I.Int.mul(x, y))), Nat.mul(RD.Int.mag(v), Qp(p1))), es, M.eta(1n+p1, XH(A, D), xl, XH(B, D), yl), Eta.sym(1n+p1, XH(A, D), xl, XH(B, D), yl)))

# DWTimesDW1 on integers (Muller and Rideau, Theorem 2.6, ties to even):
# for p >= 6, xh = A 2^(D+1), yh = B 2^(D+1) with 2^(p-1) <= A, B < 2^p,
# |xl|, |yl| <= 2^D representable: |eta| (1 + u)² <= 5u² |x y|
def DW1.b(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +hA2: {RD.Nat.lt(RD.Nat.pow2(p1), A) == True{} : Bool},
  l: Bool, +el: {RD.Nat.lt(RD.Nat.pow2(p1), B) == l : Bool})
  -> {Rel(p1, A, B, D, xl, yl) == False{} : Bool}:
  match l:
    case True{}:
      Rel.small(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, hA2, el)
    case False{}:
      Equal.trans(Bool, Rel(p1, A, B, D, xl, yl), Rel(p1, B, A, D, yl, xl), False{}, Equal.sym(Bool, Rel(p1, B, A, D, yl, xl), Rel(p1, A, B, D, xl, yl), Rel.sym(p1, A, B, D, xl, yl)),
        Rel.one(p1, B, A, D, yl, xl, hp, hB1, hB, hA1, hA, hy, hx, Swap.hs(p1, A, B, hs), E2.Le.anti(B, RD.Nat.pow2(p1), el, hB1), fx))

def DW1.a(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +hs: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == True{} : Bool}, +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat},
  l: Bool, +el: {RD.Nat.lt(RD.Nat.pow2(p1), A) == l : Bool})
  -> {Rel(p1, A, B, D, xl, yl) == False{} : Bool}:
  match l:
    case True{}:
      DW1.b(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, fx, el, RD.Nat.lt(RD.Nat.pow2(p1), B), {==})
    case False{}:
      Rel.one(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, hs, E2.Le.anti(A, RD.Nat.pow2(p1), el, hA1), fy)

def DW1.top(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat},
  l: Bool, +el: {RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))) == l : Bool})
  -> {Rel(p1, A, B, D, xl, yl) == False{} : Bool}:
  match l:
    case False{}:
      Case.big(p1, D, A, B, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, el)
    case True{}:
      DW1.a(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, el, fx, fy, RD.Nat.lt(RD.Nat.pow2(p1), A), {==})

def DW1.int(+p1: Nat, +A: Nat, +B: Nat, +D: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(D), RD.Int.mag(yl)) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat})
  -> {Rel(p1, A, B, D, xl, yl) == False{} : Bool}:
  DW1.top(p1, A, B, D, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, fx, fy, RD.Nat.lt(Nat.mul(A, B), Nat.mul(RD.Nat.pow2(1n+p1), RD.Nat.pow2(p1))), {==})


# Any signs and exponents
# -----------------------
# Negating x negates every rounded step, and scaling x by 2^j scales every
# step (no exponent bounds), so the relative error is that of positive
# inputs at a common exponent.

def RelI(+p1: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> Bool:
  RD.Nat.lt(Nat.mul(5n, RD.Int.mag(I.Int.mul(I.Int.add(xh, xl), I.Int.add(yh, yl)))), Nat.mul(RD.Int.mag(M.eta(1n+p1, xh, xl, yh, yl)), Qp(p1)))

def Neg.eta(+p: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int)
  -> {M.eta(p, I.Int.neg(xh), I.Int.neg(xl), yh, yl) == I.Int.neg(M.eta(p, xh, xl, yh, yl)) : I.Int}:
  +nxh = I.Int.neg(xh)
  +nxl = I.Int.neg(xl)
  +ch = M.ch(p, xh, yh)
  +t1 = M.tl1(p, xh, yl)
  +t2 = M.tl2(p, xl, yh)
  +c1 = M.cl1(p, xh, yh)
  +c2 = M.cl2(p, xh, xl, yh, yl)
  +c3 = M.cl3(p, xh, xl, yh, yl)
  +ech : {M.ch(p, nxh, yh) == I.Int.neg(ch) : I.Int} = E2.RNi.nml(p, xh, yh)
  +ec2 : {M.cl2(p, nxh, nxl, yh, yl) == I.Int.neg(c2) : I.Int} = Equal.trans(I.Int, M.cl2(p, nxh, nxl, yh, yl), E.RNi(p, I.Int.add(I.Int.neg(t1), I.Int.neg(t2))), I.Int.neg(c2),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(M.tl1(p, nxh, yl), M.tl2(p, nxl, yh)), I.Int.add(I.Int.neg(t1), I.Int.neg(t2)),
      Equal.trans(I.Int, I.Int.add(M.tl1(p, nxh, yl), M.tl2(p, nxl, yh)), I.Int.add(I.Int.neg(t1), M.tl2(p, nxl, yh)), I.Int.add(I.Int.neg(t1), I.Int.neg(t2)),
        Equal.cong(I.Int, I.Int, w => I.Int.add(w, M.tl2(p, nxl, yh)), M.tl1(p, nxh, yl), I.Int.neg(t1), E2.RNi.nml(p, xh, yl)),
        Equal.cong(I.Int, I.Int, w => I.Int.add(I.Int.neg(t1), w), M.tl2(p, nxl, yh), I.Int.neg(t2), E2.RNi.nml(p, xl, yh)))),
    E2.RNi.nadd(p, t1, t2))
  +envc : List<&2, I.Int> = [xh, yh, ch]
  +ec1 : {M.cl1(p, nxh, yh) == I.Int.neg(c1) : I.Int} = Equal.trans(I.Int, M.cl1(p, nxh, yh), I.Int.add(I.Int.mul(nxh, yh), I.Int.neg(I.Int.neg(ch))), I.Int.neg(c1),
    Equal.cong(I.Int, I.Int, w => I.Int.add(I.Int.mul(nxh, yh), I.Int.neg(w)), M.ch(p, nxh, yh), I.Int.neg(ch), ech),
    BP.IntN(envc, R.Ad(R.Ml(R.Ng(R.V(0n)), R.V(1n)), R.Ng(R.Ng(R.V(2n)))), R.Ng(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ng(R.V(2n)))), [], [], {==}, Unit{}))
  +ec3 : {M.cl3(p, nxh, nxl, yh, yl) == I.Int.neg(c3) : I.Int} = Equal.trans(I.Int, M.cl3(p, nxh, nxl, yh, yl), E.RNi(p, I.Int.add(I.Int.neg(c1), I.Int.neg(c2))), I.Int.neg(c3),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(M.cl1(p, nxh, yh), M.cl2(p, nxh, nxl, yh, yl)), I.Int.add(I.Int.neg(c1), I.Int.neg(c2)),
      Equal.trans(I.Int, I.Int.add(M.cl1(p, nxh, yh), M.cl2(p, nxh, nxl, yh, yl)), I.Int.add(I.Int.neg(c1), M.cl2(p, nxh, nxl, yh, yl)), I.Int.add(I.Int.neg(c1), I.Int.neg(c2)),
        Equal.cong(I.Int, I.Int, w => I.Int.add(w, M.cl2(p, nxh, nxl, yh, yl)), M.cl1(p, nxh, yh), I.Int.neg(c1), ec1),
        Equal.cong(I.Int, I.Int, w => I.Int.add(I.Int.neg(c1), w), M.cl2(p, nxh, nxl, yh, yl), I.Int.neg(c2), ec2))),
    E2.RNi.nadd(p, c1, c2))
  +s = E.F2.s(p, ch, c3)
  +t = E.F2.t(p, ch, c3)
  +c3n = M.cl3(p, nxh, nxl, yh, yl)
  +ez : {M.z(p, nxh, nxl, yh, yl) == I.Int.add(I.Int.neg(s), I.Int.neg(t)) : I.Int} = Equal.trans(I.Int, M.z(p, nxh, nxl, yh, yl), I.Int.add(E.F2.s(p, I.Int.neg(ch), I.Int.neg(c3)), E.F2.t(p, I.Int.neg(ch), I.Int.neg(c3))), I.Int.add(I.Int.neg(s), I.Int.neg(t)),
    Equal.trans(I.Int, M.z(p, nxh, nxl, yh, yl), I.Int.add(E.F2.s(p, I.Int.neg(ch), c3n), E.F2.t(p, I.Int.neg(ch), c3n)), I.Int.add(E.F2.s(p, I.Int.neg(ch), I.Int.neg(c3)), E.F2.t(p, I.Int.neg(ch), I.Int.neg(c3))),
      Equal.cong(I.Int, I.Int, w => I.Int.add(E.F2.s(p, w, c3n), E.F2.t(p, w, c3n)), M.ch(p, nxh, yh), I.Int.neg(ch), ech),
      Equal.cong(I.Int, I.Int, w => I.Int.add(E.F2.s(p, I.Int.neg(ch), w), E.F2.t(p, I.Int.neg(ch), w)), c3n, I.Int.neg(c3), ec3)),
    Equal.trans(I.Int, I.Int.add(E.F2.s(p, I.Int.neg(ch), I.Int.neg(c3)), E.F2.t(p, I.Int.neg(ch), I.Int.neg(c3))), I.Int.add(I.Int.neg(s), E.F2.t(p, I.Int.neg(ch), I.Int.neg(c3))), I.Int.add(I.Int.neg(s), I.Int.neg(t)),
      Equal.cong(I.Int, I.Int, w => I.Int.add(w, E.F2.t(p, I.Int.neg(ch), I.Int.neg(c3))), E.F2.s(p, I.Int.neg(ch), I.Int.neg(c3)), I.Int.neg(s), E.F2.sym.s(p, ch, c3)),
      Equal.cong(I.Int, I.Int, w => I.Int.add(I.Int.neg(s), w), E.F2.t(p, I.Int.neg(ch), I.Int.neg(c3)), I.Int.neg(t), E.F2.sym.t(p, ch, c3))))
  +enve : List<&2, I.Int> = [s, t, xh, xl, yh, yl]
  Equal.trans(I.Int, M.eta(p, nxh, nxl, yh, yl), I.Int.add(I.Int.add(I.Int.neg(s), I.Int.neg(t)), I.Int.neg(I.Int.mul(I.Int.add(nxh, nxl), I.Int.add(yh, yl)))), I.Int.neg(M.eta(p, xh, xl, yh, yl)),
    Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.neg(I.Int.mul(I.Int.add(nxh, nxl), I.Int.add(yh, yl)))), M.z(p, nxh, nxl, yh, yl), I.Int.add(I.Int.neg(s), I.Int.neg(t)), ez),
    BP.IntN(enve, R.Ad(R.Ad(R.Ng(R.V(0n)), R.Ng(R.V(1n))), R.Ng(R.Ml(R.Ad(R.Ng(R.V(2n)), R.Ng(R.V(3n))), R.Ad(R.V(4n), R.V(5n))))),
      R.Ng(R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.Ml(R.Ad(R.V(2n), R.V(3n)), R.Ad(R.V(4n), R.V(5n)))))), [], [], {==}, Unit{}))

def Neg.rel(+p1: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int)
  -> {RelI(p1, I.Int.neg(xh), I.Int.neg(xl), yh, yl) == RelI(p1, xh, xl, yh, yl) : Bool}:
  +X = I.Int.add(xh, xl)
  +Yy = I.Int.add(yh, yl)
  +et = M.eta(1n+p1, I.Int.neg(xh), I.Int.neg(xl), yh, yl)
  +envm : List<&2, I.Int> = [xh, xl, yh, yl]
  +em : {RD.Int.mag(I.Int.mul(I.Int.add(I.Int.neg(xh), I.Int.neg(xl)), Yy)) == RD.Int.mag(I.Int.mul(X, Yy)) : Nat} = Equal.trans(Nat, RD.Int.mag(I.Int.mul(I.Int.add(I.Int.neg(xh), I.Int.neg(xl)), Yy)), RD.Int.mag(I.Int.neg(I.Int.mul(X, Yy))), RD.Int.mag(I.Int.mul(X, Yy)),
    Equal.cong(I.Int, Nat, w => RD.Int.mag(w), I.Int.mul(I.Int.add(I.Int.neg(xh), I.Int.neg(xl)), Yy), I.Int.neg(I.Int.mul(X, Yy)),
      BP.IntN(envm, R.Ml(R.Ad(R.Ng(R.V(0n)), R.Ng(R.V(1n))), R.Ad(R.V(2n), R.V(3n))), R.Ng(R.Ml(R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(2n), R.V(3n)))), [], [], {==}, Unit{})),
    E.Mag.neg(I.Int.mul(X, Yy)))
  +ee : {RD.Int.mag(et) == RD.Int.mag(M.eta(1n+p1, xh, xl, yh, yl)) : Nat} = Equal.trans(Nat, RD.Int.mag(et), RD.Int.mag(I.Int.neg(M.eta(1n+p1, xh, xl, yh, yl))), RD.Int.mag(M.eta(1n+p1, xh, xl, yh, yl)),
    Equal.cong(I.Int, Nat, w => RD.Int.mag(w), et, I.Int.neg(M.eta(1n+p1, xh, xl, yh, yl)), Neg.eta(1n+p1, xh, xl, yh, yl)), E.Mag.neg(M.eta(1n+p1, xh, xl, yh, yl)))
  Equal.trans(Bool, RelI(p1, I.Int.neg(xh), I.Int.neg(xl), yh, yl), RD.Nat.lt(Nat.mul(5n, RD.Int.mag(I.Int.mul(X, Yy))), Nat.mul(RD.Int.mag(et), Qp(p1))), RelI(p1, xh, xl, yh, yl),
    Equal.cong(Nat, Bool, w => RD.Nat.lt(Nat.mul(5n, w), Nat.mul(RD.Int.mag(et), Qp(p1))), RD.Int.mag(I.Int.mul(I.Int.add(I.Int.neg(xh), I.Int.neg(xl)), Yy)), RD.Int.mag(I.Int.mul(X, Yy)), em),
    Equal.cong(Nat, Bool, w => RD.Nat.lt(Nat.mul(5n, RD.Int.mag(I.Int.mul(X, Yy))), Nat.mul(w, Qp(p1))), RD.Int.mag(et), RD.Int.mag(M.eta(1n+p1, xh, xl, yh, yl)), ee))

def Sym.rel(+p1: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> {RelI(p1, yh, yl, xh, xl) == RelI(p1, xh, xl, yh, yl) : Bool}:
  +x = I.Int.add(xh, xl)
  +y = I.Int.add(yh, yl)
  +es = M.eta(1n+p1, yh, yl, xh, xl)
  Equal.trans(Bool, RelI(p1, yh, yl, xh, xl), RD.Nat.lt(Nat.mul(5n, RD.Int.mag(I.Int.mul(x, y))), Nat.mul(RD.Int.mag(es), Qp(p1))), RelI(p1, xh, xl, yh, yl),
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(Nat.mul(5n, RD.Int.mag(v)), Nat.mul(RD.Int.mag(es), Qp(p1))), I.Int.mul(y, x), I.Int.mul(x, y), Z.Int.mul_comm(y, x)),
    Equal.cong(I.Int, Bool, v => RD.Nat.lt(Nat.mul(5n, RD.Int.mag(I.Int.mul(x, y))), Nat.mul(RD.Int.mag(v), Qp(p1))), es, M.eta(1n+p1, xh, xl, yh, yl), Eta.sym(1n+p1, xh, xl, yh, yl)))

# Fast2Sum commutes with 2^j
def F2sh.s(+p: Nat, +j: Nat, +a: I.Int, +b: I.Int) -> {E.F2.s(p, D.Int.sh(j, a), D.Int.sh(j, b)) == D.Int.sh(j, E.F2.s(p, a, b)) : I.Int}:
  E2.RNi.shadd(p, j, a, b)

def F2sh.z(+p: Nat, +j: Nat, +a: I.Int, +b: I.Int) -> {E.F2.z(p, D.Int.sh(j, a), D.Int.sh(j, b)) == D.Int.sh(j, E.F2.z(p, a, b)) : I.Int}:
  Equal.trans(I.Int, E.F2.z(p, D.Int.sh(j, a), D.Int.sh(j, b)), E.RNi(p, I.Int.add(D.Int.sh(j, E.F2.s(p, a, b)), I.Int.neg(D.Int.sh(j, a)))), D.Int.sh(j, E.F2.z(p, a, b)),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, I.Int.add(w, I.Int.neg(D.Int.sh(j, a)))), E.F2.s(p, D.Int.sh(j, a), D.Int.sh(j, b)), D.Int.sh(j, E.F2.s(p, a, b)), F2sh.s(p, j, a, b)),
    E2.RNi.shsub(p, j, E.F2.s(p, a, b), a))

def F2sh.t(+p: Nat, +j: Nat, +a: I.Int, +b: I.Int) -> {E.F2.t(p, D.Int.sh(j, a), D.Int.sh(j, b)) == D.Int.sh(j, E.F2.t(p, a, b)) : I.Int}:
  Equal.trans(I.Int, E.F2.t(p, D.Int.sh(j, a), D.Int.sh(j, b)), E.RNi(p, I.Int.add(D.Int.sh(j, b), I.Int.neg(D.Int.sh(j, E.F2.z(p, a, b))))), D.Int.sh(j, E.F2.t(p, a, b)),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, I.Int.add(D.Int.sh(j, b), I.Int.neg(w))), E.F2.z(p, D.Int.sh(j, a), D.Int.sh(j, b)), D.Int.sh(j, E.F2.z(p, a, b)), F2sh.z(p, j, a, b)),
    E2.RNi.shsub(p, j, b, E.F2.z(p, a, b)))

def Shm(+j: Nat, +a: I.Int, +b: I.Int) -> {I.Int.mul(D.Int.sh(j, a), b) == D.Int.sh(j, I.Int.mul(a, b)) : I.Int}:
  Equal.sym(I.Int, D.Int.sh(j, I.Int.mul(a, b)), I.Int.mul(D.Int.sh(j, a), b), Y.Int.sh_mul(j, a, b))

def Sh.eta(+p: Nat, +j: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int)
  -> {M.eta(p, D.Int.sh(j, xh), D.Int.sh(j, xl), yh, yl) == D.Int.sh(j, M.eta(p, xh, xl, yh, yl)) : I.Int}:
  +sxh = D.Int.sh(j, xh)
  +sxl = D.Int.sh(j, xl)
  +ch = M.ch(p, xh, yh)
  +t1 = M.tl1(p, xh, yl)
  +t2 = M.tl2(p, xl, yh)
  +c1 = M.cl1(p, xh, yh)
  +c2 = M.cl2(p, xh, xl, yh, yl)
  +c3 = M.cl3(p, xh, xl, yh, yl)
  +ech : {M.ch(p, sxh, yh) == D.Int.sh(j, ch) : I.Int} = Equal.trans(I.Int, M.ch(p, sxh, yh), E.RNi(p, D.Int.sh(j, I.Int.mul(xh, yh))), D.Int.sh(j, ch),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.mul(sxh, yh), D.Int.sh(j, I.Int.mul(xh, yh)), Shm(j, xh, yh)), E.RNi.sh(p, j, I.Int.mul(xh, yh)))
  +et1 : {M.tl1(p, sxh, yl) == D.Int.sh(j, t1) : I.Int} = Equal.trans(I.Int, M.tl1(p, sxh, yl), E.RNi(p, D.Int.sh(j, I.Int.mul(xh, yl))), D.Int.sh(j, t1),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.mul(sxh, yl), D.Int.sh(j, I.Int.mul(xh, yl)), Shm(j, xh, yl)), E.RNi.sh(p, j, I.Int.mul(xh, yl)))
  +et2 : {M.tl2(p, sxl, yh) == D.Int.sh(j, t2) : I.Int} = Equal.trans(I.Int, M.tl2(p, sxl, yh), E.RNi(p, D.Int.sh(j, I.Int.mul(xl, yh))), D.Int.sh(j, t2),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.mul(sxl, yh), D.Int.sh(j, I.Int.mul(xl, yh)), Shm(j, xl, yh)), E.RNi.sh(p, j, I.Int.mul(xl, yh)))
  +ec2 : {M.cl2(p, sxh, sxl, yh, yl) == D.Int.sh(j, c2) : I.Int} = Equal.trans(I.Int, M.cl2(p, sxh, sxl, yh, yl), E.RNi(p, I.Int.add(D.Int.sh(j, t1), D.Int.sh(j, t2))), D.Int.sh(j, c2),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(M.tl1(p, sxh, yl), M.tl2(p, sxl, yh)), I.Int.add(D.Int.sh(j, t1), D.Int.sh(j, t2)),
      Equal.trans(I.Int, I.Int.add(M.tl1(p, sxh, yl), M.tl2(p, sxl, yh)), I.Int.add(D.Int.sh(j, t1), M.tl2(p, sxl, yh)), I.Int.add(D.Int.sh(j, t1), D.Int.sh(j, t2)),
        Equal.cong(I.Int, I.Int, w => I.Int.add(w, M.tl2(p, sxl, yh)), M.tl1(p, sxh, yl), D.Int.sh(j, t1), et1),
        Equal.cong(I.Int, I.Int, w => I.Int.add(D.Int.sh(j, t1), w), M.tl2(p, sxl, yh), D.Int.sh(j, t2), et2))),
    E2.RNi.shadd(p, j, t1, t2))
  +ec1 : {M.cl1(p, sxh, yh) == D.Int.sh(j, c1) : I.Int} = Equal.trans(I.Int, M.cl1(p, sxh, yh), I.Int.add(D.Int.sh(j, I.Int.mul(xh, yh)), I.Int.neg(D.Int.sh(j, ch))), D.Int.sh(j, c1),
    Equal.trans(I.Int, M.cl1(p, sxh, yh), I.Int.add(D.Int.sh(j, I.Int.mul(xh, yh)), I.Int.neg(M.ch(p, sxh, yh))), I.Int.add(D.Int.sh(j, I.Int.mul(xh, yh)), I.Int.neg(D.Int.sh(j, ch))),
      Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.neg(M.ch(p, sxh, yh))), I.Int.mul(sxh, yh), D.Int.sh(j, I.Int.mul(xh, yh)), Shm(j, xh, yh)),
      Equal.cong(I.Int, I.Int, w => I.Int.add(D.Int.sh(j, I.Int.mul(xh, yh)), I.Int.neg(w)), M.ch(p, sxh, yh), D.Int.sh(j, ch), ech)),
    E2.Sh.diff(j, I.Int.mul(xh, yh), ch))
  +ec3 : {M.cl3(p, sxh, sxl, yh, yl) == D.Int.sh(j, c3) : I.Int} = Equal.trans(I.Int, M.cl3(p, sxh, sxl, yh, yl), E.RNi(p, I.Int.add(D.Int.sh(j, c1), D.Int.sh(j, c2))), D.Int.sh(j, c3),
    Equal.cong(I.Int, I.Int, w => E.RNi(p, w), I.Int.add(M.cl1(p, sxh, yh), M.cl2(p, sxh, sxl, yh, yl)), I.Int.add(D.Int.sh(j, c1), D.Int.sh(j, c2)),
      Equal.trans(I.Int, I.Int.add(M.cl1(p, sxh, yh), M.cl2(p, sxh, sxl, yh, yl)), I.Int.add(D.Int.sh(j, c1), M.cl2(p, sxh, sxl, yh, yl)), I.Int.add(D.Int.sh(j, c1), D.Int.sh(j, c2)),
        Equal.cong(I.Int, I.Int, w => I.Int.add(w, M.cl2(p, sxh, sxl, yh, yl)), M.cl1(p, sxh, yh), D.Int.sh(j, c1), ec1),
        Equal.cong(I.Int, I.Int, w => I.Int.add(D.Int.sh(j, c1), w), M.cl2(p, sxh, sxl, yh, yl), D.Int.sh(j, c2), ec2))),
    E2.RNi.shadd(p, j, c1, c2))
  +s = E.F2.s(p, ch, c3)
  +t = E.F2.t(p, ch, c3)
  +c3s = M.cl3(p, sxh, sxl, yh, yl)
  +ez : {M.z(p, sxh, sxl, yh, yl) == D.Int.sh(j, M.z(p, xh, xl, yh, yl)) : I.Int} = Equal.trans(I.Int, M.z(p, sxh, sxl, yh, yl), I.Int.add(E.F2.s(p, D.Int.sh(j, ch), D.Int.sh(j, c3)), E.F2.t(p, D.Int.sh(j, ch), D.Int.sh(j, c3))), D.Int.sh(j, M.z(p, xh, xl, yh, yl)),
    Equal.trans(I.Int, M.z(p, sxh, sxl, yh, yl), I.Int.add(E.F2.s(p, D.Int.sh(j, ch), c3s), E.F2.t(p, D.Int.sh(j, ch), c3s)), I.Int.add(E.F2.s(p, D.Int.sh(j, ch), D.Int.sh(j, c3)), E.F2.t(p, D.Int.sh(j, ch), D.Int.sh(j, c3))),
      Equal.cong(I.Int, I.Int, w => I.Int.add(E.F2.s(p, w, c3s), E.F2.t(p, w, c3s)), M.ch(p, sxh, yh), D.Int.sh(j, ch), ech),
      Equal.cong(I.Int, I.Int, w => I.Int.add(E.F2.s(p, D.Int.sh(j, ch), w), E.F2.t(p, D.Int.sh(j, ch), w)), c3s, D.Int.sh(j, c3), ec3)),
    Equal.trans(I.Int, I.Int.add(E.F2.s(p, D.Int.sh(j, ch), D.Int.sh(j, c3)), E.F2.t(p, D.Int.sh(j, ch), D.Int.sh(j, c3))), I.Int.add(D.Int.sh(j, s), D.Int.sh(j, t)), D.Int.sh(j, M.z(p, xh, xl, yh, yl)),
      Equal.trans(I.Int, I.Int.add(E.F2.s(p, D.Int.sh(j, ch), D.Int.sh(j, c3)), E.F2.t(p, D.Int.sh(j, ch), D.Int.sh(j, c3))), I.Int.add(D.Int.sh(j, s), E.F2.t(p, D.Int.sh(j, ch), D.Int.sh(j, c3))), I.Int.add(D.Int.sh(j, s), D.Int.sh(j, t)),
        Equal.cong(I.Int, I.Int, w => I.Int.add(w, E.F2.t(p, D.Int.sh(j, ch), D.Int.sh(j, c3))), E.F2.s(p, D.Int.sh(j, ch), D.Int.sh(j, c3)), D.Int.sh(j, s), F2sh.s(p, j, ch, c3)),
        Equal.cong(I.Int, I.Int, w => I.Int.add(D.Int.sh(j, s), w), E.F2.t(p, D.Int.sh(j, ch), D.Int.sh(j, c3)), D.Int.sh(j, t), F2sh.t(p, j, ch, c3))),
      Equal.sym(I.Int, D.Int.sh(j, I.Int.add(s, t)), I.Int.add(D.Int.sh(j, s), D.Int.sh(j, t)), Y.Int.sh_add(j, s, t))))
  +X = I.Int.add(xh, xl)
  +Yy = I.Int.add(yh, yl)
  +ep : {I.Int.mul(I.Int.add(sxh, sxl), Yy) == D.Int.sh(j, I.Int.mul(X, Yy)) : I.Int} = Equal.trans(I.Int, I.Int.mul(I.Int.add(sxh, sxl), Yy), I.Int.mul(D.Int.sh(j, X), Yy), D.Int.sh(j, I.Int.mul(X, Yy)),
    Equal.cong(I.Int, I.Int, w => I.Int.mul(w, Yy), I.Int.add(sxh, sxl), D.Int.sh(j, X), Equal.sym(I.Int, D.Int.sh(j, X), I.Int.add(sxh, sxl), Y.Int.sh_add(j, xh, xl))), Shm(j, X, Yy))
  Equal.trans(I.Int, M.eta(p, sxh, sxl, yh, yl), I.Int.add(D.Int.sh(j, M.z(p, xh, xl, yh, yl)), I.Int.neg(D.Int.sh(j, I.Int.mul(X, Yy)))), D.Int.sh(j, M.eta(p, xh, xl, yh, yl)),
    Equal.trans(I.Int, M.eta(p, sxh, sxl, yh, yl), I.Int.add(D.Int.sh(j, M.z(p, xh, xl, yh, yl)), I.Int.neg(I.Int.mul(I.Int.add(sxh, sxl), Yy))), I.Int.add(D.Int.sh(j, M.z(p, xh, xl, yh, yl)), I.Int.neg(D.Int.sh(j, I.Int.mul(X, Yy)))),
      Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.neg(I.Int.mul(I.Int.add(sxh, sxl), Yy))), M.z(p, sxh, sxl, yh, yl), D.Int.sh(j, M.z(p, xh, xl, yh, yl)), ez),
      Equal.cong(I.Int, I.Int, w => I.Int.add(D.Int.sh(j, M.z(p, xh, xl, yh, yl)), I.Int.neg(w)), I.Int.mul(I.Int.add(sxh, sxl), Yy), D.Int.sh(j, I.Int.mul(X, Yy)), ep)),
    E2.Sh.diff(j, M.z(p, xh, xl, yh, yl), I.Int.mul(X, Yy)))

def Sh.rel(+p1: Nat, +j: Nat, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int)
  -> {RelI(p1, D.Int.sh(j, xh), D.Int.sh(j, xl), yh, yl) == RelI(p1, xh, xl, yh, yl) : Bool}:
  +K = RD.Nat.pow2(j)
  +X = I.Int.add(xh, xl)
  +Yy = I.Int.add(yh, yl)
  +mxy = RD.Int.mag(I.Int.mul(X, Yy))
  +me = RD.Int.mag(M.eta(1n+p1, xh, xl, yh, yl))
  +Q = Qp(p1)
  +em : {RD.Int.mag(I.Int.mul(I.Int.add(D.Int.sh(j, xh), D.Int.sh(j, xl)), Yy)) == Nat.mul(mxy, K) : Nat} = Equal.trans(Nat, RD.Int.mag(I.Int.mul(I.Int.add(D.Int.sh(j, xh), D.Int.sh(j, xl)), Yy)), RD.Int.mag(D.Int.sh(j, I.Int.mul(X, Yy))), Nat.mul(mxy, K),
    Equal.cong(I.Int, Nat, w => RD.Int.mag(w), I.Int.mul(I.Int.add(D.Int.sh(j, xh), D.Int.sh(j, xl)), Yy), D.Int.sh(j, I.Int.mul(X, Yy)),
      Equal.trans(I.Int, I.Int.mul(I.Int.add(D.Int.sh(j, xh), D.Int.sh(j, xl)), Yy), I.Int.mul(D.Int.sh(j, X), Yy), D.Int.sh(j, I.Int.mul(X, Yy)),
        Equal.cong(I.Int, I.Int, w => I.Int.mul(w, Yy), I.Int.add(D.Int.sh(j, xh), D.Int.sh(j, xl)), D.Int.sh(j, X), Equal.sym(I.Int, D.Int.sh(j, X), I.Int.add(D.Int.sh(j, xh), D.Int.sh(j, xl)), Y.Int.sh_add(j, xh, xl))), Shm(j, X, Yy))),
    E.Sh.mag(j, I.Int.mul(X, Yy)))
  +ee : {RD.Int.mag(M.eta(1n+p1, D.Int.sh(j, xh), D.Int.sh(j, xl), yh, yl)) == Nat.mul(me, K) : Nat} = Equal.trans(Nat, RD.Int.mag(M.eta(1n+p1, D.Int.sh(j, xh), D.Int.sh(j, xl), yh, yl)), RD.Int.mag(D.Int.sh(j, M.eta(1n+p1, xh, xl, yh, yl))), Nat.mul(me, K),
    Equal.cong(I.Int, Nat, w => RD.Int.mag(w), M.eta(1n+p1, D.Int.sh(j, xh), D.Int.sh(j, xl), yh, yl), D.Int.sh(j, M.eta(1n+p1, xh, xl, yh, yl)), Sh.eta(1n+p1, j, xh, xl, yh, yl)),
    E.Sh.mag(j, M.eta(1n+p1, xh, xl, yh, yl)))
  +env : List<&2, Nat> = [mxy, me, K, Q]
  +e1 : {Nat.mul(5n, Nat.mul(mxy, K)) == Nat.mul(Nat.mul(5n, mxy), K) : Nat} = R.NatN.eq(env, R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ad(R.Ml(R.V(0n), R.V(2n)), N.TZero{}))))),
    R.Ml(R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), R.Ad(R.V(0n), N.TZero{}))))), R.V(2n)), [], [], {==}, Unit{}, {==}, {==})
  +e2 : {Nat.mul(Nat.mul(me, K), Q) == Nat.mul(Nat.mul(me, Q), K) : Nat} = R.NatN.eq(env, R.Ml(R.Ml(R.V(1n), R.V(2n)), R.V(3n)), R.Ml(R.Ml(R.V(1n), R.V(3n)), R.V(2n)), [], [], {==}, Unit{}, {==}, {==})
  Equal.trans(Bool, RelI(p1, D.Int.sh(j, xh), D.Int.sh(j, xl), yh, yl), RD.Nat.lt(Nat.mul(5n, Nat.mul(mxy, K)), Nat.mul(Nat.mul(me, K), Q)), RelI(p1, xh, xl, yh, yl),
    Equal.trans(Bool, RelI(p1, D.Int.sh(j, xh), D.Int.sh(j, xl), yh, yl), RD.Nat.lt(Nat.mul(5n, Nat.mul(mxy, K)), Nat.mul(RD.Int.mag(M.eta(1n+p1, D.Int.sh(j, xh), D.Int.sh(j, xl), yh, yl)), Q)), RD.Nat.lt(Nat.mul(5n, Nat.mul(mxy, K)), Nat.mul(Nat.mul(me, K), Q)),
      Equal.cong(Nat, Bool, w => RD.Nat.lt(Nat.mul(5n, w), Nat.mul(RD.Int.mag(M.eta(1n+p1, D.Int.sh(j, xh), D.Int.sh(j, xl), yh, yl)), Q)), RD.Int.mag(I.Int.mul(I.Int.add(D.Int.sh(j, xh), D.Int.sh(j, xl)), Yy)), Nat.mul(mxy, K), em),
      Equal.cong(Nat, Bool, w => RD.Nat.lt(Nat.mul(5n, Nat.mul(mxy, K)), Nat.mul(w, Q)), RD.Int.mag(M.eta(1n+p1, D.Int.sh(j, xh), D.Int.sh(j, xl), yh, yl)), Nat.mul(me, K), ee)),
    Equal.trans(Bool, RD.Nat.lt(Nat.mul(5n, Nat.mul(mxy, K)), Nat.mul(Nat.mul(me, K), Q)), RD.Nat.lt(Nat.mul(Nat.mul(5n, mxy), K), Nat.mul(Nat.mul(me, Q), K)), RelI(p1, xh, xl, yh, yl),
      Equal.trans(Bool, RD.Nat.lt(Nat.mul(5n, Nat.mul(mxy, K)), Nat.mul(Nat.mul(me, K), Q)), RD.Nat.lt(Nat.mul(Nat.mul(5n, mxy), K), Nat.mul(Nat.mul(me, K), Q)), RD.Nat.lt(Nat.mul(Nat.mul(5n, mxy), K), Nat.mul(Nat.mul(me, Q), K)),
        Equal.cong(Nat, Bool, w => RD.Nat.lt(w, Nat.mul(Nat.mul(me, K), Q)), Nat.mul(5n, Nat.mul(mxy, K)), Nat.mul(Nat.mul(5n, mxy), K), e1),
        Equal.cong(Nat, Bool, w => RD.Nat.lt(Nat.mul(Nat.mul(5n, mxy), K), w), Nat.mul(Nat.mul(me, K), Q), Nat.mul(Nat.mul(me, Q), K), e2)),
      P3.Lt.scale(Nat.mul(5n, mxy), Nat.mul(me, Q), K, BP.Pow2.pos(j))))

# a sign on xh moves to xl
def Sg(b: Bool, +z: I.Int) -> I.Int:
  match b:
    case True{}:
      I.Int.neg(z)
    case False{}:
      z

def Sg.mag(b: Bool, +z: I.Int) -> {RD.Int.mag(Sg(b, z)) == RD.Int.mag(z) : Nat}:
  match b:
    case True{}:
      E.Mag.neg(z)
    case False{}:
      {==}

def Sg.rel(+p1: Nat, b: Bool, +xh: I.Int, +xl: I.Int, +yh: I.Int, +yl: I.Int) -> {RelI(p1, Sg(b, xh), xl, yh, yl) == RelI(p1, xh, Sg(b, xl), yh, yl) : Bool}:
  match b:
    case True{}:
      Equal.trans(Bool, RelI(p1, I.Int.neg(xh), xl, yh, yl), RelI(p1, I.Int.neg(xh), I.Int.neg(I.Int.neg(xl)), yh, yl), RelI(p1, xh, I.Int.neg(xl), yh, yl),
        Equal.cong(I.Int, Bool, w => RelI(p1, I.Int.neg(xh), w, yh, yl), xl, I.Int.neg(I.Int.neg(xl)), Equal.sym(I.Int, I.Int.neg(I.Int.neg(xl)), xl, Z.Int.neg_neg(xl))),
        Neg.rel(p1, xh, I.Int.neg(xl), yh, yl))
    case False{}:
      {==}

def Sg.fix(+p: Nat, +b: Bool, +z: I.Int, +f: {E.Rn(p, RD.Int.mag(z)) == RD.Int.mag(z) : Nat}) -> {E.Rn(p, RD.Int.mag(Sg(b, z))) == RD.Int.mag(Sg(b, z)) : Nat}:
  Equal.trans(Nat, E.Rn(p, RD.Int.mag(Sg(b, z))), E.Rn(p, RD.Int.mag(z)), RD.Int.mag(Sg(b, z)),
    Equal.cong(Nat, Nat, w => E.Rn(p, w), RD.Int.mag(Sg(b, z)), RD.Int.mag(z), Sg.mag(b, z)),
    Equal.trans(Nat, E.Rn(p, RD.Int.mag(z)), RD.Int.mag(z), RD.Int.mag(Sg(b, z)), f, Equal.sym(Nat, RD.Int.mag(Sg(b, z)), RD.Int.mag(z), Sg.mag(b, z))))

def Sg.le(+b: Bool, +z: I.Int, +c: Nat, +h: {RD.Nat.lt(c, RD.Int.mag(z)) == False{} : Bool}) -> {RD.Nat.lt(c, RD.Int.mag(Sg(b, z))) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(c, RD.Int.mag(Sg(b, z))), RD.Nat.lt(c, RD.Int.mag(z)), False{}, Equal.cong(Nat, Bool, w => RD.Nat.lt(c, w), RD.Int.mag(Sg(b, z)), RD.Int.mag(z), Sg.mag(b, z)), h)

# x at a lower exponent than y: scale x up by 2^(Dy - Dx)
def XH.sh(+A: Nat, +Dx: Nat, +j: Nat) -> {D.Int.sh(j, XH(A, Dx)) == XH(A, Nat.add(Dx, j)) : I.Int}:
  E2.Sh.eq(j, 0n, Nat.mul(A, RD.Nat.pow2(1n+Dx)), Nat.mul(A, RD.Nat.pow2(1n+Nat.add(Dx, j))),
    Equal.trans(Nat, Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+Dx)), RD.Nat.pow2(j)), Nat.mul(A, Nat.mul(RD.Nat.pow2(1n+Dx), RD.Nat.pow2(j))), Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+Nat.add(Dx, j))), 1n),
      NL.Nat.mul_assoc(A, RD.Nat.pow2(1n+Dx), RD.Nat.pow2(j)),
      Equal.trans(Nat, Nat.mul(A, Nat.mul(RD.Nat.pow2(1n+Dx), RD.Nat.pow2(j))), Nat.mul(A, RD.Nat.pow2(1n+Nat.add(Dx, j))), Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+Nat.add(Dx, j))), 1n),
        Equal.cong(Nat, Nat, w => Nat.mul(A, w), Nat.mul(RD.Nat.pow2(1n+Dx), RD.Nat.pow2(j)), RD.Nat.pow2(1n+Nat.add(Dx, j)), Equal.sym(Nat, RD.Nat.pow2(Nat.add(1n+Dx, j)), Nat.mul(RD.Nat.pow2(1n+Dx), RD.Nat.pow2(j)), BP.Pow2.add(1n+Dx, j))),
        Equal.sym(Nat, Nat.mul(Nat.mul(A, RD.Nat.pow2(1n+Nat.add(Dx, j))), 1n), Nat.mul(A, RD.Nat.pow2(1n+Nat.add(Dx, j))), NL.Nat.mul_one_r(Nat.mul(A, RD.Nat.pow2(1n+Nat.add(Dx, j))))))))

def Align(+p1: Nat, +A: Nat, +B: Nat, +Dx: Nat, +Dy: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(Dx), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(Dy), RD.Int.mag(yl)) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat},
  +hD: {RD.Nat.lt(Dy, Dx) == False{} : Bool})
  -> {RelI(p1, XH(A, Dx), xl, XH(B, Dy), yl) == False{} : Bool}:
  +j = RD.Nat.monus(Dy, Dx)
  +eD : {Dy == Nat.add(Dx, j) : Nat} = E.Le.wit(Dx, Dy, hD)
  +sxl = D.Int.sh(j, xl)
  +K = RD.Nat.pow2(j)
  +em : {RD.Int.mag(sxl) == Nat.mul(RD.Int.mag(xl), K) : Nat} = E.Sh.mag(j, xl)
  +eW : {Nat.mul(RD.Nat.pow2(Dx), K) == RD.Nat.pow2(Dy) : Nat} = Equal.trans(Nat, Nat.mul(RD.Nat.pow2(Dx), K), RD.Nat.pow2(Nat.add(Dx, j)), RD.Nat.pow2(Dy),
    Equal.sym(Nat, RD.Nat.pow2(Nat.add(Dx, j)), Nat.mul(RD.Nat.pow2(Dx), K), BP.Pow2.add(Dx, j)), Equal.cong(Nat, Nat, w => RD.Nat.pow2(w), Nat.add(Dx, j), Dy, Equal.sym(Nat, Dy, Nat.add(Dx, j), eD)))
  +hx2 : {RD.Nat.lt(RD.Nat.pow2(Dy), RD.Int.mag(sxl)) == False{} : Bool} = E.Le.trans(RD.Int.mag(sxl), Nat.mul(RD.Nat.pow2(Dx), K), RD.Nat.pow2(Dy),
    E.Le.trans(RD.Int.mag(sxl), Nat.mul(RD.Int.mag(xl), K), Nat.mul(RD.Nat.pow2(Dx), K), E.Le.eq(RD.Int.mag(sxl), Nat.mul(RD.Int.mag(xl), K), em), E2.Le.mulr(RD.Int.mag(xl), RD.Nat.pow2(Dx), K, hx)),
    E.Le.eq(Nat.mul(RD.Nat.pow2(Dx), K), RD.Nat.pow2(Dy), eW))
  +fx2 : {E.Rn(1n+p1, RD.Int.mag(sxl)) == RD.Int.mag(sxl) : Nat} = Equal.trans(Nat, E.Rn(1n+p1, RD.Int.mag(sxl)), E.Rn(1n+p1, Nat.mul(RD.Int.mag(xl), K)), RD.Int.mag(sxl),
    Equal.cong(Nat, Nat, w => E.Rn(1n+p1, w), RD.Int.mag(sxl), Nat.mul(RD.Int.mag(xl), K), em),
    Equal.trans(Nat, E.Rn(1n+p1, Nat.mul(RD.Int.mag(xl), K)), Nat.mul(E.Rn(1n+p1, RD.Int.mag(xl)), K), RD.Int.mag(sxl), Rn.sc(1n+p1, RD.Int.mag(xl), j),
      Equal.trans(Nat, Nat.mul(E.Rn(1n+p1, RD.Int.mag(xl)), K), Nat.mul(RD.Int.mag(xl), K), RD.Int.mag(sxl), Equal.cong(Nat, Nat, w => Nat.mul(w, K), E.Rn(1n+p1, RD.Int.mag(xl)), RD.Int.mag(xl), fx),
        Equal.sym(Nat, RD.Int.mag(sxl), Nat.mul(RD.Int.mag(xl), K), em))))
  +r : {RelI(p1, XH(A, Dy), sxl, XH(B, Dy), yl) == False{} : Bool} = DW1.int(p1, A, B, Dy, sxl, yl, hp, hA1, hA, hB1, hB, hx2, hy, fx2, fy)
  +exh : {D.Int.sh(j, XH(A, Dx)) == XH(A, Dy) : I.Int} = Equal.trans(I.Int, D.Int.sh(j, XH(A, Dx)), XH(A, Nat.add(Dx, j)), XH(A, Dy), XH.sh(A, Dx, j),
    Equal.cong(Nat, I.Int, w => XH(A, w), Nat.add(Dx, j), Dy, Equal.sym(Nat, Dy, Nat.add(Dx, j), eD)))
  Equal.trans(Bool, RelI(p1, XH(A, Dx), xl, XH(B, Dy), yl), RelI(p1, D.Int.sh(j, XH(A, Dx)), sxl, XH(B, Dy), yl), False{},
    Equal.sym(Bool, RelI(p1, D.Int.sh(j, XH(A, Dx)), sxl, XH(B, Dy), yl), RelI(p1, XH(A, Dx), xl, XH(B, Dy), yl), Sh.rel(p1, j, XH(A, Dx), xl, XH(B, Dy), yl)),
    Equal.trans(Bool, RelI(p1, D.Int.sh(j, XH(A, Dx)), sxl, XH(B, Dy), yl), RelI(p1, XH(A, Dy), sxl, XH(B, Dy), yl), False{},
      Equal.cong(I.Int, Bool, w => RelI(p1, w, sxl, XH(B, Dy), yl), D.Int.sh(j, XH(A, Dx)), XH(A, Dy), exh), r))

def Align2(+p1: Nat, +A: Nat, +B: Nat, +Dx: Nat, +Dy: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(Dx), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(Dy), RD.Int.mag(yl)) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat},
  l: Bool, +el: {RD.Nat.lt(Dy, Dx) == l : Bool})
  -> {RelI(p1, XH(A, Dx), xl, XH(B, Dy), yl) == False{} : Bool}:
  match l:
    case False{}:
      Align(p1, A, B, Dx, Dy, xl, yl, hp, hA1, hA, hB1, hB, hx, hy, fx, fy, el)
    case True{}:
      Equal.trans(Bool, RelI(p1, XH(A, Dx), xl, XH(B, Dy), yl), RelI(p1, XH(B, Dy), yl, XH(A, Dx), xl), False{},
        Equal.sym(Bool, RelI(p1, XH(B, Dy), yl, XH(A, Dx), xl), RelI(p1, XH(A, Dx), xl, XH(B, Dy), yl), Sym.rel(p1, XH(A, Dx), xl, XH(B, Dy), yl)),
        Align(p1, B, A, Dy, Dx, yl, xl, hp, hB1, hB, hA1, hA, hy, hx, fy, fx, E2.Lt.to_le(Dy, Dx, el)))

# DWTimesDW1 (Muller and Rideau, Theorem 2.6, ties to even), any signs and
# exponents, binary rounding at p >= 6 bits with no exponent bounds:
# xh = +-A 2^(Dx+1) with 2^(p-1) <= A < 2^p (so u xh is 2^Dx), |xl| <= 2^Dx
# representable, the same for y: |zh + zl - x y| (1 + u)² <= 5u² |x y|
def DW1.gen(+p1: Nat, +sx: Bool, +sy: Bool, +A: Nat, +B: Nat, +Dx: Nat, +Dy: Nat, +xl: I.Int, +yl: I.Int, +hp: {RD.Nat.lt(p1, 5n) == False{} : Bool},
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(p1)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(p1)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(1n+p1)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(Dx), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(Dy), RD.Int.mag(yl)) == False{} : Bool},
  +fx: {E.Rn(1n+p1, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(1n+p1, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat})
  -> {RelI(p1, Sg(sx, XH(A, Dx)), xl, Sg(sy, XH(B, Dy)), yl) == False{} : Bool}:
  +xh = XH(A, Dx)
  +yh = XH(B, Dy)
  +xl2 = Sg(sx, xl)
  +yl2 = Sg(sy, yl)
  +e1 : {RelI(p1, Sg(sx, xh), xl, Sg(sy, yh), yl) == RelI(p1, xh, xl2, Sg(sy, yh), yl) : Bool} = Sg.rel(p1, sx, xh, xl, Sg(sy, yh), yl)
  +e2 : {RelI(p1, xh, xl2, Sg(sy, yh), yl) == RelI(p1, xh, xl2, yh, yl2) : Bool} = Equal.trans(Bool, RelI(p1, xh, xl2, Sg(sy, yh), yl), RelI(p1, Sg(sy, yh), yl, xh, xl2), RelI(p1, xh, xl2, yh, yl2),
    Equal.sym(Bool, RelI(p1, Sg(sy, yh), yl, xh, xl2), RelI(p1, xh, xl2, Sg(sy, yh), yl), Sym.rel(p1, xh, xl2, Sg(sy, yh), yl)),
    Equal.trans(Bool, RelI(p1, Sg(sy, yh), yl, xh, xl2), RelI(p1, yh, yl2, xh, xl2), RelI(p1, xh, xl2, yh, yl2), Sg.rel(p1, sy, yh, yl, xh, xl2), Sym.rel(p1, xh, xl2, yh, yl2)))
  Equal.trans(Bool, RelI(p1, Sg(sx, xh), xl, Sg(sy, yh), yl), RelI(p1, xh, xl2, yh, yl2), False{}, Equal.trans(Bool, RelI(p1, Sg(sx, xh), xl, Sg(sy, yh), yl), RelI(p1, xh, xl2, Sg(sy, yh), yl), RelI(p1, xh, xl2, yh, yl2), e1, e2),
    Align2(p1, A, B, Dx, Dy, xl2, yl2, hp, hA1, hA, hB1, hB, Sg.le(sx, xl, RD.Nat.pow2(Dx), hx), Sg.le(sy, yl, RD.Nat.pow2(Dy), hy), Sg.fix(1n+p1, sx, xl, fx), Sg.fix(1n+p1, sy, yl, fy), RD.Nat.lt(Dy, Dx), {==}))

