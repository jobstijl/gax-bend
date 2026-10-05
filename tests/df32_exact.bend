# The error-free transformations under double-F32 (num/df32.bend), proven
# for Fast2Sum, TwoSum, Veltkamp's split and Dekker's product (below) and
# checked exactly: big dyadics (src/big.bend) hold the exact values, so
# s + t = a + b is a test of equality, not of closeness. Fast2Sum (with
# |a| >= |b|) and TwoSum must give s + t = a + b for all finite inputs;
# Dekker's product p + e = a b barring underflow and overflow (products
# outside 2^-100 to 10^38 are skipped and counted); Veltkamp's split
# hi + lo = a with hi on 12 bits. Inputs span exponents 2^-100 to 2^60
# with random significand widths and signs, so sums cancel and cross
# exponent gaps. The control checks TwoSum's s alone against a + b, which
# must fail whenever the sum is inexact.
#
# The double-word operations against their published bounds, exactly:
# AccurateDWPlusDW within 3u^2 and DWTimesDW (Algorithm 10, no FMA) within
# 5u^2, u = 2^-24 (Joldes, Muller and Popescu 2017; 5u^2 for Algorithm 10
# is Muller and Rideau's bound, 2022). Inputs are double words from TwoSum
# with exponents in [-30, 30], away from underflow, which the bounds
# exclude. The 6u^2 and 7u^2 counts show the margin; the control counts
# inexact products, so the comparison can fail. DWTimesDW's bound is
# proven (proofs/dw.bend, F32.DWTimesDW below); AccurateDWPlusDW's is
# tested here.
import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/round.bend as RD
import ../src/big.bend as B
import ../num/df32.bend as DF
import ../proofs/eft.bend as E
import ../proofs/eft2.bend as E2
import ../proofs/dw.bend as DW

# Proven (proofs/eft.bend): binary32 values are A / 2^149 with A an integer
# that rounds to itself at 24 bits. For those, Fast2Sum (|b| <= |a|) and
# TwoSum as num/df32.bend computes it (Fast2Sum on the magnitude-sorted
# pair) are exact in Dy.f32 arithmetic. The tests below check the same on
# native F32.
def F32.Fast2Sum(aa: I.Int, +bb: I.Int, fa: E.Fi(24n, aa), +fb: {E.Rn(24n, RD.Int.mag(bb)) == RD.Int.mag(bb) : Nat}, +hle: {RD.Nat.lt(RD.Int.mag(aa), RD.Int.mag(bb)) == False{} : Bool})
  -> {D.Dy.add(RD.Dy.f32(D.Dy.add(D.Dy.of(149n, aa), D.Dy.of(149n, bb))),
        RD.Dy.f32(D.Dy.add(D.Dy.of(149n, bb), D.Dy.neg(RD.Dy.f32(D.Dy.add(RD.Dy.f32(D.Dy.add(D.Dy.of(149n, aa), D.Dy.of(149n, bb))), D.Dy.neg(D.Dy.of(149n, aa))))))))
      == D.Dy.add(D.Dy.of(149n, aa), D.Dy.of(149n, bb)) : D.Dy}:
  E.DFast2Sum(23n, 126n, aa, bb, fa, fb, hle)

def F32.TwoSum(+aa: I.Int, +bb: I.Int, +fa: {E.Rn(24n, RD.Int.mag(aa)) == RD.Int.mag(aa) : Nat}, +fb: {E.Rn(24n, RD.Int.mag(bb)) == RD.Int.mag(bb) : Nat})
  -> {D.Dy.add(E.DTS.s(23n, 126n, aa, bb), E.DTS.t(23n, 126n, aa, bb)) == D.Dy.add(D.Dy.of(149n, aa), D.Dy.of(149n, bb)) : D.Dy}:
  E.DTwoSum(23n, 126n, aa, bb, fa, fb)

# Proven (proofs/eft2.bend): Veltkamp's split as num/df32.bend computes it
# (C = 4097) is exact in Dy.f32 arithmetic for every binary32 value,
# subnormals included: hi + lo = a.
def F32.Split(+aa: I.Int, +fa: {E.Rn(24n, RD.Int.mag(aa)) == RD.Int.mag(aa) : Nat})
  -> {D.Dy.add(E2.DRf.h(23n, 126n, 12n, D.Dy.of(149n, aa)), E2.DRf.l(23n, 126n, 12n, D.Dy.of(149n, aa))) == D.Dy.of(149n, aa) : D.Dy}:
  E2.DRf.split(23n, 126n, 12n, aa, fa)

# Proven (proofs/eft2.bend): Dekker's product as num/df32.bend computes it is
# exact in 24-bit binary rounding with no exponent bounds, that is binary32
# barring underflow and overflow: for a = A / 2^k, b = B / 2^k with A, B
# 24-bit integers, p = RN(a b) and e give p + e = a b. (p = 1 + (12 + 11)
# and s = 12 are written as DTwoProd states them: the checker compares them
# without expanding 2^24.)
def F32.TwoProd(+k: Nat, +aa: I.Int, +bb: I.Int, +fa: {E.Rn(1n+Nat.add(1n+1n+10n, 1n+10n), RD.Int.mag(aa)) == RD.Int.mag(aa) : Nat}, +fb: {E.Rn(1n+Nat.add(1n+1n+10n, 1n+10n), RD.Int.mag(bb)) == RD.Int.mag(bb) : Nat})
  -> {D.Dy.add(E2.DTP.p(Nat.add(1n+1n+10n, 1n+10n), D.Dy.of(k, aa), D.Dy.of(k, bb)), E2.DTP.e(Nat.add(1n+1n+10n, 1n+10n), 1n+1n+10n, D.Dy.of(k, aa), D.Dy.of(k, bb))) == D.Dy.mul(D.Dy.of(k, aa), D.Dy.of(k, bb)) : D.Dy}:
  E2.DTwoProd(10n, k, aa, bb, fa, fb)

# DWTimesDW (Algorithm 10) at 24 bits, ties to even, barring underflow and
# overflow (proofs/dw.bend, DW1.gen): for x = xh + xl with
# xh = +-A 2^(Dx+1), 2^23 <= A < 2^24 (so u xh is 2^Dx) and |xl| <= 2^Dx a
# 24-bit integer, and y likewise, the result zh + zl has
# |zh + zl - x y| (1 + u)^2 <= 5u^2 |x y|, u = 2^-24. RelI is the negation
# of that inequality, so False is the bound. Binary32 values are A / 2^149
# (scaling by 2^-149 changes no relative error).
def F32.DWTimesDW(+sx: Bool, +sy: Bool, +A: Nat, +B: Nat, +Dx: Nat, +Dy: Nat, +xl: I.Int, +yl: I.Int,
  +hA1: {RD.Nat.lt(A, RD.Nat.pow2(23n)) == False{} : Bool}, +hA: {RD.Nat.lt(A, RD.Nat.pow2(24n)) == True{} : Bool},
  +hB1: {RD.Nat.lt(B, RD.Nat.pow2(23n)) == False{} : Bool}, +hB: {RD.Nat.lt(B, RD.Nat.pow2(24n)) == True{} : Bool},
  +hx: {RD.Nat.lt(RD.Nat.pow2(Dx), RD.Int.mag(xl)) == False{} : Bool}, +hy: {RD.Nat.lt(RD.Nat.pow2(Dy), RD.Int.mag(yl)) == False{} : Bool},
  +fx: {E.Rn(24n, RD.Int.mag(xl)) == RD.Int.mag(xl) : Nat}, +fy: {E.Rn(24n, RD.Int.mag(yl)) == RD.Int.mag(yl) : Nat})
  -> {DW.RelI(23n, DW.Sg(sx, DW.XH(A, Dx)), xl, DW.Sg(sy, DW.XH(B, Dy)), yl) == False{} : Bool}:
  DW.DW1.gen(23n, sx, sy, A, B, Dx, Dy, xl, yl, {==}, hA1, hA, hB1, hB, hx, hy, fx, fy)

def hb() -> Nat:
  8388608n

def rnd(+x: Nat) -> Nat:
  Nat.mod(Nat.mul(x, 16807n), 2147483647n)

def scale(up: Nat, dn: Nat, +f: F32) -> F32:
  match up:
    case 0n:
      match dn:
        case 0n:
          f
        case 1n+j:
          scale(0n, j, F32.mul(f, 0.5))
    case 1n+j:
      scale(j, dn, F32.mul(f, 2.0))

def dec.go(+s: Bool, +n: Nat, +ex: Nat) -> B.Bd:
  Bool.pick(B.Bd, Nat.is_lt(ex, 150n), B.Bd{s, B.Bn.of(hb(), n), Nat.sub(150n, ex)}, B.Bd{s, B.Bn.shl(hb(), Nat.sub(ex, 150n), B.Bn.of(hb(), n)), 0n})

def dec(+f: F32) -> B.Bd:
  +b = U32.to_nat(F32.bits(f))
  +s = Bool.not(Nat.is_lt(b, 2147483648n))
  +ex = Nat.mod(Nat.div(b, 8388608n), 256n)
  +fr = Nat.mod(b, 8388608n)
  Bool.pick(B.Bd, Nat.is_eq(ex, 0n), dec.go(s, fr, 1n), dec.go(s, Nat.add(8388608n, fr), ex))

def same.n(x: B.Bd, y: B.Bd) -> Bool:
  match x y:
    case B.Bd{n1, +m1, e1} B.Bd{n2, +m2, e2}:
      Bool.and(Nat.is_eq(e1, e2), Bool.and(Bool.not(Bool.or(B.Bn.lt(m1, m2), B.Bn.lt(m2, m1))), Bool.or(Bool.not(B.Bn.lt(B.BNil{}, m1)), Bool.not(Bool.xor(n1, n2)))))

def same(x: B.Bd, y: B.Bd) -> Bool:
  same.n(B.Bd.norm(hb(), x), B.Bd.norm(hb(), y))

# 1 to 24 significant bits, scaled by 2^t, t in [-100, 60]
def draw(+s: Nat) -> F32:
  +w : Nat = 1n+Nat.mod(s, 24n)
  +m : Nat = 1n+Nat.mod(rnd(s), Nat.sub(Nat.pow(2n, w), 1n))
  +t = Nat.mod(rnd(rnd(s)), 161n)
  +f = scale(Nat.sub(t, 100n), Nat.sub(100n, t), U32.to_f32(U32.from_nat(m)))
  Bool.pick(F32, Nat.is_eq(Nat.mod(rnd(rnd(rnd(s))), 2n), 0n), f, F32.neg(f))

def sumof(d: DF.DF) -> B.Bd:
  match d:
    case DF.DF{+h, +l}:
      B.Bd.add(hb(), dec(h), dec(l))

def hiof(d: DF.DF) -> B.Bd:
  match d:
    case DF.DF{+h, l}:
      dec(h)

def skip(+t: Bool) -> Nat:
  Bool.pick(Nat, t, 1n, 0n)

def miss(+ok: Bool) -> Nat:
  Bool.pick(Nat, ok, 0n, 1n)

type Cnt is Data:
  Cnt{f2s: Nat, ts: Nat, tp: Nat, sp: Nat, ctl: Nat, sk: Nat}

def tally(c: Cnt, +a: Nat, +b: Nat, +d: Nat, +e: Nat, +f: Nat, +g: Nat) -> Cnt:
  match c:
    case Cnt{x1, x2, x3, x4, x5, x6}:
      Cnt{Nat.add(x1, a), Nat.add(x2, b), Nat.add(x3, d), Nat.add(x4, e), Nat.add(x5, f), Nat.add(x6, g)}

def step(c: Cnt, +s: Nat) -> Cnt:
  +a = draw(s)
  +b = draw(rnd(rnd(rnd(rnd(s)))))
  +big = Bool.pick(F32, F32.is_lt(F32.abs(a), F32.abs(b)), b, a)
  +sml = Bool.pick(F32, F32.is_lt(F32.abs(a), F32.abs(b)), a, b)
  +x = dec(a)
  +y = dec(b)
  +ab = B.Bd.add(hb(), x, y)
  +p = F32.mul(a, b)
  # Dekker's product needs no underflow or overflow: products below 2^-100
  # or above 10^38 are skipped
  +tiny = Bool.or(F32.is_lt(F32.abs(p), 7.9e-31), Bool.not(F32.is_lt(F32.abs(p), 1.0e38)))
  tally(c, miss(same(sumof(DF.Fast2Sum(big, sml)), ab)), miss(same(sumof(DF.TwoSum(a, b)), ab)),
    miss(Bool.or(tiny, same(sumof(DF.TwoProd(a, b)), B.Bd.mul(hb(), x, y)))), miss(same(sumof(DF.Split(a)), x)),
    miss(same(hiof(DF.TwoSum(a, b)), ab)), skip(tiny))

def run(n: Nat, +s: Nat, c: Cnt) -> Cnt:
  match n:
    case 0n:
      c
    case 1n+k:
      run(k, rnd(rnd(rnd(rnd(rnd(s))))), step(c, s))

def show(c: Cnt) -> String:
  match c:
    case Cnt{x1, x2, x3, x4, x5, x6}:
      "inexact: Fast2Sum " ++ Nat.show(x1) ++ ", TwoSum " ++ Nat.show(x2) ++ ", TwoProd " ++ Nat.show(x3) ++ " (" ++ Nat.show(x6) ++ " skipped), Split " ++ Nat.show(x4) ++ "; control (s alone) " ++ Nat.show(x5)

# Double-word operations against their published bounds
# ------------------------------------------------------

# x 2^48
def up48(x: B.Bd) -> B.Bd:
  match x:
    case B.Bd{+n, +m, +e}:
      Bool.pick(B.Bd, Nat.is_lt(e, 48n), B.Bd{n, B.Bn.shl(hb(), Nat.sub(48n, e), m), 0n}, B.Bd{n, m, Nat.sub(e, 48n)})

def absb(x: B.Bd) -> B.Bd:
  match x:
    case B.Bd{n, m, e}:
      B.Bd{False{}, m, e}

# y >= 0
def nonneg.n(y: B.Bd) -> Bool:
  match y:
    case B.Bd{n, m, e}:
      Bool.or(Bool.not(n), Bool.not(B.Bn.lt(B.BNil{}, m)))

# |err| 2^48 > k |exact|, i.e. the error passes k u^2 relative
def over(+k: Nat, +err: B.Bd, +ex: B.Bd) -> Nat:
  Bool.pick(Nat, nonneg.n(B.Bd.norm(hb(), B.Bd.add(hb(), B.Bd.mul(hb(), B.Bd{False{}, B.Bn.of(hb(), k), 0n}, absb(ex)), B.Bd.neg(up48(absb(err)))))), 0n, 1n)

# 1 to 24 significant bits, scaled by 2^t, t in [-30, 30]
def draw30(+s: Nat) -> F32:
  +w : Nat = 1n+Nat.mod(s, 24n)
  +m : Nat = 1n+Nat.mod(rnd(s), Nat.sub(Nat.pow(2n, w), 1n))
  +t = Nat.mod(rnd(rnd(s)), 61n)
  +f = scale(Nat.sub(t, 30n), Nat.sub(30n, t), U32.to_f32(U32.from_nat(m)))
  Bool.pick(F32, Nat.is_eq(Nat.mod(rnd(rnd(rnd(s))), 2n), 0n), f, F32.neg(f))

# a double word: TwoSum of two such floats, the second scaled by about 2^-17

def dw(+s: Nat) -> DF.DF:
  DF.TwoSum(draw30(s), F32.mul(draw30(rnd(s)), 1.0e-5))

type W is Data:
  W{a3: Nat, m5: Nat, m6: Nat, m7: Nat, c0: Nat}

def wadd(w: W, +a: Nat, +b: Nat, +c: Nat, +d: Nat, +z: Nat) -> W:
  match w:
    case W{a3, m5, m6, m7, c0}:
      W{Nat.add(a3, a), Nat.add(m5, b), Nat.add(m6, c), Nat.add(m7, d), Nat.add(c0, z)}

def wstep(w: W, +s: Nat) -> W:
  +x = dw(s)
  +y = dw(rnd(rnd(s)))
  +ex = B.Bd.add(hb(), sumof(x), sumof(y))
  +ea = B.Bd.add(hb(), sumof(DF.DF.add(x, y)), B.Bd.neg(ex))
  +mx = B.Bd.mul(hb(), sumof(x), sumof(y))
  +em = B.Bd.add(hb(), sumof(DF.DF.mul(x, y)), B.Bd.neg(mx))
  wadd(w, over(3n, ea, ex), over(5n, em, mx), over(6n, em, mx), over(7n, em, mx), over(0n, em, mx))

def wrun(n: Nat, +s: Nat, w: W) -> W:
  match n:
    case 0n:
      w
    case 1n+k:
      wrun(k, rnd(rnd(rnd(s))), wstep(w, s))

def wshow(w: W) -> String:
  match w:
    case W{a3, m5, m6, m7, c0}:
      "AccurateDWPlusDW past 3u^2: " ++ Nat.show(a3) ++ "; DWTimesDW past 5u^2: " ++ Nat.show(m5) ++ ", 6u^2: " ++ Nat.show(m6) ++ ", 7u^2: " ++ Nat.show(m7) ++ "; control, DWTimesDW inexact: " ++ Nat.show(c0)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("20000 pairs, " ++ show(run(20000n, 3n, Cnt{0n, 0n, 0n, 0n, 0n, 0n})))
    IO.print("20000 double-word pairs, " ++ wshow(wrun(20000n, 5n, W{0n, 0n, 0n, 0n, 0n})))
#|20000 pairs, inexact: Fast2Sum 0, TwoSum 0, TwoProd 0 (2568 skipped), Split 0; control (s alone) 16742
#|20000 double-word pairs, AccurateDWPlusDW past 3u^2: 0; DWTimesDW past 5u^2: 0, 6u^2: 0, 7u^2: 0; control, DWTimesDW inexact: 19105
