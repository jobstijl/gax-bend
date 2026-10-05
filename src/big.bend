# Big naturals: limbs in base 2h, least significant first, for exact
# arithmetic past run-time Nat's 2^48 - 1 (bend-facts Q16). At run time
# h = 2^23, so a limb product with two carries stays below 2^48. Each
# operation uses Base's native Nat operations and is proven to commute
# with the value map into Nat (proofs/big.bend), so a theorem about Nat
# arithmetic holds of the limbs.

import Base
import ./int.bend as I
import ./dyadic.bend as D
import ./fast.bend as F

type Bn is Data:
  BNil{}
  BCons{d: Nat, r: Bn}

# the value, for proofs: d + 2h val(r)
def Bn.val(+h: Nat, b: Bn) -> Nat:
  match b:
    case BNil{}:
      0n
    case BCons{d, r}:
      Nat.add(d, Nat.mul(Bn.val(h, r), Nat.double(h)))

# every limb below 2h
def Bn.ok(+h: Nat, b: Bn) -> Bool:
  match b:
    case BNil{}:
      True{}
    case BCons{d, r}:
      Bool.and(F.Nat.ltf(d, Nat.double(h)), Bn.ok(h, r))

def Bn.c(acc: Bool) -> Nat:
  match acc:
    case True{}:
      1n
    case False{}:
      0n

# Comparison
# ----------

# from the low limbs up; acc compares the lower parts, as a <= b (True) or
# a < b (False); a missing limb is 0
def Bn.lt.go(a: Bn, b: Bn, acc: Bool) -> Bool:
  match a b:
    case BNil{} BNil{}:
      acc
    case BCons{x, xs} BNil{}:
      Bn.lt.go(xs, BNil{}, F.Nat.ltf(x, Nat.add(Bn.c(acc), 0n)))
    case BNil{} BCons{y, ys}:
      Bn.lt.go(BNil{}, ys, F.Nat.ltf(0n, Nat.add(Bn.c(acc), y)))
    case BCons{x, xs} BCons{y, ys}:
      Bn.lt.go(xs, ys, F.Nat.ltf(x, Nat.add(Bn.c(acc), y)))

def Bn.lt(a: Bn, b: Bn) -> Bool:
  Bn.lt.go(a, b, False{})

# Addition
# --------

def Bn.top(cy: Bool) -> Bn:
  match cy:
    case True{}:
      BCons{1n, BNil{}}
    case False{}:
      BNil{}

# a limb sum s: s - B with a carry when s >= B
def Bn.dig(+s: Nat, +bb: Nat) -> Nat:
  Bool.pick(Nat, Bool.not(F.Nat.ltf(s, bb)), F.Nat.monusf(s, bb), s)

def Bn.cy(+s: Nat, +bb: Nat) -> Bool:
  Bool.not(F.Nat.ltf(s, bb))

# a + b + [cy]
def Bn.addc(+h: Nat, a: Bn, b: Bn, cy: Bool) -> Bn:
  match a b:
    case BNil{} BNil{}:
      Bn.top(cy)
    case BCons{x, xs} BNil{}:
      +s = Nat.add(Nat.add(Bn.c(cy), x), 0n)
      BCons{Bn.dig(s, Nat.double(h)), Bn.addc(h, xs, BNil{}, Bn.cy(s, Nat.double(h)))}
    case BNil{} BCons{y, ys}:
      +s = Nat.add(Nat.add(Bn.c(cy), 0n), y)
      BCons{Bn.dig(s, Nat.double(h)), Bn.addc(h, BNil{}, ys, Bn.cy(s, Nat.double(h)))}
    case BCons{x, xs} BCons{y, ys}:
      +s = Nat.add(Nat.add(Bn.c(cy), x), y)
      BCons{Bn.dig(s, Nat.double(h)), Bn.addc(h, xs, ys, Bn.cy(s, Nat.double(h)))}

def Bn.add(+h: Nat, a: Bn, b: Bn) -> Bn:
  Bn.addc(h, a, b, False{})

# Multiplication
# --------------

# a number below B as at most one limb
def Bn.dig1(c: Nat) -> Bn:
  match c:
    case 0n:
      BNil{}
    case 1n+k:
      BCons{1n+k, BNil{}}

# a y + c, for a limb y and a carry c
def Bn.mulD(+h: Nat, a: Bn, +y: Nat, +c: Nat) -> Bn:
  match a:
    case BNil{}:
      Bn.dig1(c)
    case BCons{x, xs}:
      +s = Nat.add(Nat.mul(x, y), c)
      BCons{Nat.mod(s, Nat.double(h)), Bn.mulD(h, xs, y, Nat.div(s, Nat.double(h)))}

def Bn.mul(+h: Nat, +a: Bn, b: Bn) -> Bn:
  match b:
    case BNil{}:
      BNil{}
    case BCons{y, ys}:
      Bn.add(h, Bn.mulD(h, a, y, 0n), BCons{0n, Bn.mul(h, a, ys)})

# Halving and parity
# ------------------

# the low bit
def Bn.bit0(b: Bn) -> Nat:
  match b:
    case BNil{}:
      0n
    case BCons{d, r}:
      F.Nat.bitf(d)

def Bn.even(b: Bn) -> Bool:
  match b:
    case BNil{}:
      True{}
    case BCons{d, r}:
      F.Nat.evenf(d)

# floor(b / 2): each limb takes the low bit of the next as h
def Bn.half(+h: Nat, b: Bn) -> Bn:
  match b:
    case BNil{}:
      BNil{}
    case BCons{d, +r}:
      BCons{Nat.add(F.Nat.halff(d), Nat.mul(h, Bn.bit0(r))), Bn.half(h, r)}

# Shifts and conversion
# ---------------------

# b 2^k, by doubling
def Bn.shl(+h: Nat, k: Nat, +b: Bn) -> Bn:
  match k:
    case 0n:
      b
    case 1n+j:
      +s = Bn.shl(h, j, b)
      Bn.add(h, s, s)

def Bn.pow2(+h: Nat, k: Nat) -> Bn:
  Bn.shl(h, k, BCons{1n, BNil{}})

# a natural below B^2 (run-time Nat is below 2^48 = B^2)
def Bn.of(+h: Nat, +n: Nat) -> Bn:
  BCons{Nat.mod(n, Nat.double(h)), Bn.dig1(Nat.div(n, Nat.double(h)))}

# Subtraction
# -----------

# a - b - [br], for a >= b + [br]; a limb borrows B when x < t
def Bn.subb(+h: Nat, a: Bn, b: Bn, br: Bool) -> Bn:
  match a b:
    case BNil{} BNil{}:
      BNil{}
    case BCons{+x, xs} BNil{}:
      +t = Nat.add(Bn.c(br), 0n)
      +bw = F.Nat.ltf(x, t)
      BCons{F.Nat.monusf(Nat.add(x, Nat.mul(Bn.c(bw), Nat.double(h))), t), Bn.subb(h, xs, BNil{}, bw)}
    case BNil{} BCons{y, ys}:
      +t = Nat.add(Bn.c(br), y)
      +bw = F.Nat.ltf(0n, t)
      BCons{F.Nat.monusf(Nat.add(0n, Nat.mul(Bn.c(bw), Nat.double(h))), t), Bn.subb(h, BNil{}, ys, bw)}
    case BCons{+x, xs} BCons{y, ys}:
      +t = Nat.add(Bn.c(br), y)
      +bw = F.Nat.ltf(x, t)
      BCons{F.Nat.monusf(Nat.add(x, Nat.mul(Bn.c(bw), Nat.double(h))), t), Bn.subb(h, xs, ys, bw)}

def Bn.sub(+h: Nat, a: Bn, b: Bn) -> Bn:
  Bn.subb(h, a, b, False{})

# the number of limbs
def Bn.len(b: Bn) -> Nat:
  match b:
    case BNil{}:
      0n
    case BCons{d, r}:
      1n+Bn.len(r)

# Rounding a magnitude
# --------------------

# n = q 2^s + r, as in Tr (src/round.bend) without the proof witnesses
type TrB is Data:
  TrB{s: Nat, q: Bn, r: Bn}

def TrB.s(t: TrB) -> Nat:
  match t:
    case TrB{s, q, r}:
      s

def TrB.q(t: TrB) -> Bn:
  match t:
    case TrB{s, q, r}:
      q

def TrB.r(t: TrB) -> Bn:
  match t:
    case TrB{s, q, r}:
      r

def TrB.up(+h: Nat, t: TrB, odd: Bool) -> TrB:
  match t:
    case TrB{s, q, +r}:
      TrB{1n+s, q, Bn.addc(h, r, r, odd)}

# halve until n < 2^p (pw), at most fuel times
def TrB.go(+h: Nat, fuel: Nat, +pw: Bn, +n: Bn, lt: Bool) -> TrB:
  match fuel:
    case 0n:
      TrB{0n, n, BNil{}}
    case 1n+f:
      match lt:
        case True{}:
          TrB{0n, n, BNil{}}
        case False{}:
          +hn = Bn.half(h, n)
          TrB.up(h, TrB.go(h, f, pw, hn, Bn.lt(hn, pw)), Bool.not(Bn.even(n)))

# fuel h L suffices: n < (2h)^L <= 2^(h L) (proofs/big.bend, Val.lt)
def TrB.of(+h: Nat, +p: Nat, +n: Bn) -> TrB:
  +pw = Bn.pow2(h, p)
  TrB.go(h, Nat.mul(h, Bn.len(n)), pw, n, Bn.lt(n, pw))

def TrB.rup(+h: Nat, t: TrB) -> Bool:
  match t:
    case TrB{+s, q, +r}:
      +r2 = Bn.add(h, r, r)
      +sv = Bn.pow2(h, s)
      Bool.and(Bool.not(Bn.lt(r2, sv)), Bool.or(Bn.lt(sv, r2), Bool.not(Bn.even(q))))

def Bn.nearp(+h: Nat, u: Bool, +s: Nat, +q: Bn) -> Bn:
  match u:
    case True{}:
      Bn.shl(h, s, Bn.addc(h, q, BNil{}, True{}))
    case False{}:
      Bn.shl(h, s, q)

def TrB.near(+h: Nat, +t: TrB) -> Bn:
  Bn.nearp(h, TrB.rup(h, t), TrB.s(t), TrB.q(t))

# the grid loop: s halvings
def FxB.go(+h: Nat, s: Nat, +n: Bn) -> TrB:
  match s:
    case 0n:
      TrB{0n, n, BNil{}}
    case 1n+j:
      TrB.up(h, FxB.go(h, j, Bn.half(h, n)), Bool.not(Bn.even(n)))

# Big dyadics
# -----------

# (-1)^neg m / 2^e, m a big natural; zero may carry either sign
type Bd is Data:
  Bd{neg: Bool, m: Bn, e: Nat}

def Bd.sg(neg: Bool, n: Nat) -> I.Int:
  match neg:
    case False{}:
      I.IPos{n}
    case True{}:
      I.Int.neg(I.IPos{n})

# the value, for proofs
def Bd.val(+h: Nat, x: Bd) -> D.Dy:
  match x:
    case Bd{neg, m, e}:
      D.Dy.of(e, Bd.sg(neg, Bn.val(h, m)))

def Bd.mul(+h: Nat, x: Bd, y: Bd) -> Bd:
  match x y:
    case Bd{n1, m1, e1} Bd{n2, m2, e2}:
      Bd{Bool.xor(n1, n2), Bn.mul(h, m1, m2), Nat.add(e1, e2)}

# a - b over one exponent, by magnitudes
def Bd.sdiff(+h: Nat, +a: Bn, +b: Bn, +e: Nat, lt: Bool) -> Bd:
  match lt:
    case True{}:
      Bd{True{}, Bn.sub(h, b, a), e}
    case False{}:
      Bd{False{}, Bn.sub(h, a, b), e}

# signed magnitudes over one exponent
def Bd.sadd(+h: Nat, n1: Bool, +a: Bn, n2: Bool, +b: Bn, +e: Nat) -> Bd:
  match n1 n2:
    case False{} False{}:
      Bd{False{}, Bn.add(h, a, b), e}
    case True{} True{}:
      Bd{True{}, Bn.add(h, a, b), e}
    case False{} True{}:
      Bd.sdiff(h, a, b, e, Bn.lt(a, b))
    case True{} False{}:
      Bd.sdiff(h, b, a, e, Bn.lt(b, a))

# align to the larger exponent, then add
def Bd.addal(+h: Nat, n1: Bool, +m1: Bn, +e1: Nat, n2: Bool, +m2: Bn, +e2: Nat, lt: Bool) -> Bd:
  match lt:
    case True{}:
      Bd.sadd(h, n1, m1, n2, Bn.shl(h, F.Nat.monusf(e1, e2), m2), e1)
    case False{}:
      Bd.sadd(h, n1, Bn.shl(h, F.Nat.monusf(e2, e1), m1), n2, m2, e2)

def Bd.add(+h: Nat, x: Bd, y: Bd) -> Bd:
  match x y:
    case Bd{n1, m1, +e1} Bd{n2, m2, +e2}:
      Bd.addal(h, n1, m1, e1, n2, m2, e2, F.Nat.ltf(e2, e1))

def Bd.neg(x: Bd) -> Bd:
  match x:
    case Bd{n, m, e}:
      Bd{Bool.not(n), m, e}

# strip factors of 2 from m while e > 0 (the normal form of Dy.of)
def Bd.norm.go(+h: Nat, neg: Bool, e: Nat, +m: Bn, ev: Bool) -> Bd:
  match e:
    case 0n:
      Bd{neg, m, 0n}
    case 1n+f:
      match ev:
        case True{}:
          Bd.norm.go(h, neg, f, Bn.half(h, m), Bn.even(Bn.half(h, m)))
        case False{}:
          Bd{neg, m, 1n+f}

def Bd.norm(+h: Nat, x: Bd) -> Bd:
  match x:
    case Bd{neg, +m, e}:
      Bd.norm.go(h, neg, e, m, Bn.even(m))

# rounding a normal form: to p bits, or to the grid 2^-k
def Bd.rne.n(+h: Nat, +p: Nat, x: Bd) -> Bd:
  match x:
    case Bd{neg, +m, e}:
      Bd{neg, TrB.near(h, TrB.of(h, p, m)), e}

def Bd.rfix.p(+h: Nat, +k: Nat, neg: Bool, +m: Bn, +e: Nat, lt: Bool) -> Bd:
  match lt:
    case True{}:
      Bd{neg, TrB.near(h, FxB.go(h, F.Nat.monusf(e, k), m)), e}
    case False{}:
      Bd{neg, m, e}

def Bd.rfix.n(+h: Nat, +k: Nat, x: Bd) -> Bd:
  match x:
    case Bd{neg, +m, +e}:
      Bd.rfix.p(h, k, neg, m, e, F.Nat.ltf(k, e))

# |x| >= 2^-emin, on a normal form
def Bd.bige(+h: Nat, +emin: Nat, x: Bd) -> Bool:
  match x:
    case Bd{neg, +m, +e}:
      Bool.pick(Bool, F.Nat.ltf(emin, e), Bool.not(Bn.lt(m, Bn.pow2(h, F.Nat.monusf(e, emin)))), True{})

def Bd.fl.n(+h: Nat, +p: Nat, +k: Nat, big: Bool, +x: Bd) -> Bd:
  match big:
    case True{}:
      Bd.rne.n(h, p, x)
    case False{}:
      Bd.rfix.n(h, k, x)

# a binary format's rounding: p bits, grid 2^-k, normal from 2^-emin
def Bd.fl(+h: Nat, +p: Nat, +k: Nat, +emin: Nat, x: Bd) -> Bd:
  +nx = Bd.norm(h, x)
  Bd.fl.n(h, p, k, Bd.bige(h, emin, nx), nx)

def Bd.f32(+h: Nat, x: Bd) -> Bd:
  Bd.fl(h, 24n, 149n, 126n, x)

def Bd.f64(+h: Nat, x: Bd) -> Bd:
  Bd.fl(h, 53n, 1074n, 1022n, x)

# every limb below 2h
def Bd.ok(+h: Nat, x: Bd) -> Bool:
  match x:
    case Bd{n, m, e}:
      Bn.ok(h, m)

def Bd.n(x: Bd) -> Bool:
  match x:
    case Bd{n, m, e}:
      n

def Bd.m(x: Bd) -> Bn:
  match x:
    case Bd{n, m, e}:
      m

def Bd.e(x: Bd) -> Nat:
  match x:
    case Bd{n, m, e}:
      e

# Exact dot products
# ------------------

def Bd.zero() -> Bd:
  Bd{False{}, BNil{}, 0n}

# sum of x_i y_i, exact: a Kulisch accumulator. Rounded once (Bd.f32,
# Bd.f64), it gives the correctly rounded dot product.
def Bd.dot(+h: Nat, xs: List<&2, Bd>, ys: List<&2, Bd>) -> Bd:
  match xs:
    case Nil{}:
      Bd.zero()
    case x <> xr:
      match ys:
        case Nil{}:
          Bd.zero()
        case y <> yr:
          Bd.add(h, Bd.mul(h, x, y), Bd.dot(h, xr, yr))

# the same on dyadics, for proofs
def Dy.dotv(xs: List<&2, D.Dy>, ys: List<&2, D.Dy>) -> D.Dy:
  match xs:
    case Nil{}:
      D.Dy.zero()
    case x <> xr:
      match ys:
        case Nil{}:
          D.Dy.zero()
        case y <> yr:
          D.Dy.add(D.Dy.mul(x, y), Dy.dotv(xr, yr))

def Bd.vals(+h: Nat, xs: List<&2, Bd>) -> List<&2, D.Dy>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> xr:
      Bd.val(h, x) <> Bd.vals(h, xr)

def Bd.oks(+h: Nat, xs: List<&2, Bd>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> xr:
      Bool.and(Bd.ok(h, x), Bd.oks(h, xr))
