# Big binary32 arithmetic (src/big.bend) against native F32, bit for bit,
# over the whole finite exponent range: subnormal inputs, subnormal and
# underflowing products, sums across any exponent gap. Bd.f32 of an exact
# product or sum is proven to be Dy.f32 of it (proofs/big.bend, Mul32.lk,
# Add32.lk; imported, so the gate checks it), which meets the rounding
# model (proofs/round.bend, Fl.model). So this measures one thing: that the
# hardware rounds as IEEE says. The control adds 2^-160 to each expected
# result, so the comparison can fail.
#
# Dot products: the exact accumulator rounded once (Bd.dot, Dot32.lk) is
# the correctly rounded dot product; the line counts how often a plain F32
# loop differs from it.
import Base
import ../src/int.bend as I
import ../src/big.bend as B
import ../proofs/big.bend as BP

def hb() -> Nat:
  8388608n

# Park-Miller: x 16807 mod (2^31 - 1)
def rnd(+x: Nat) -> Nat:
  Nat.mod(Nat.mul(x, 16807n), 2147483647n)

# m 2^t, built natively (t = up - dn)
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

# the exact value of a float, from its bits
def dec.go(+s: Bool, +n: Nat, +ex: Nat) -> B.Bd:
  Bool.pick(B.Bd, Nat.is_lt(ex, 150n), B.Bd{s, B.Bn.of(hb(), n), Nat.sub(150n, ex)}, B.Bd{s, B.Bn.shl(hb(), Nat.sub(ex, 150n), B.Bn.of(hb(), n)), 0n})

def dec(+f: F32) -> B.Bd:
  +b = U32.to_nat(F32.bits(f))
  +s = Bool.not(Nat.is_lt(b, 2147483648n))
  +ex = Nat.mod(Nat.div(b, 8388608n), 256n)
  +fr = Nat.mod(b, 8388608n)
  Bool.pick(B.Bd, Nat.is_eq(ex, 0n), dec.go(s, fr, 1n), dec.go(s, Nat.add(8388608n, fr), ex))

def Bn.zero(m: B.Bn) -> Bool:
  Bool.not(B.Bn.lt(B.BNil{}, m))

# equal values: same exponent and magnitude, and sign unless zero
def same.n(x: B.Bd, y: B.Bd) -> Bool:
  match x y:
    case B.Bd{n1, +m1, e1} B.Bd{n2, +m2, e2}:
      Bool.and(Nat.is_eq(e1, e2), Bool.and(Bool.not(Bool.or(B.Bn.lt(m1, m2), B.Bn.lt(m2, m1))), Bool.or(Bn.zero(m1), Bool.not(Bool.xor(n1, n2)))))

def same(x: B.Bd, y: B.Bd) -> Bool:
  same.n(B.Bd.norm(hb(), x), B.Bd.norm(hb(), y))

# the control: 2^-160 more than the expected value
def want(ctl: Bool, +z: B.Bd) -> B.Bd:
  match ctl:
    case False{}:
      z
    case True{}:
      B.Bd.add(hb(), z, B.Bd{False{}, B.BCons{1n, B.BNil{}}, 160n})

# 1 to 24 significant bits, scaled by 2^t, t in [-170, 39], either sign
def draw(+s: Nat) -> F32:
  +w : Nat = 1n+Nat.mod(s, 24n)
  +m : Nat = 1n+Nat.mod(rnd(s), Nat.sub(Nat.pow(2n, w), 1n))
  +t = Nat.mod(rnd(rnd(s)), 210n)
  +f = scale(Nat.sub(t, 170n), Nat.sub(170n, t), U32.to_f32(U32.from_nat(m)))
  Bool.pick(F32, Nat.is_eq(Nat.mod(rnd(rnd(rnd(s))), 2n), 0n), f, F32.neg(f))

type Cnt is Data:
  Cnt{n: Nat, sub: Nat, bad: Nat}

def tally(c: Cnt, +okm: Bool, +oka: Bool, +tiny: Bool) -> Cnt:
  match c:
    case Cnt{n, sb, bd}:
      Cnt{1n+n, Nat.add(sb, Bool.pick(Nat, tiny, 1n, 0n)), Nat.add(bd, Nat.add(Bool.pick(Nat, okm, 0n, 1n), Bool.pick(Nat, oka, 0n, 1n)))}

def step(+ctl: Bool, c: Cnt, +s: Nat) -> Cnt:
  +a = draw(s)
  +b = draw(rnd(rnd(rnd(rnd(s)))))
  +x = dec(a)
  +y = dec(b)
  +p = F32.mul(a, b)
  +okm = same(dec(p), want(ctl, B.Bd.f32(hb(), B.Bd.mul(hb(), x, y))))
  +oka = same(dec(F32.add(a, b)), want(ctl, B.Bd.f32(hb(), B.Bd.add(hb(), x, y))))
  +tiny = Bool.and(F32.is_lt(F32.abs(p), 1.1754944e-38), Bool.not(F32.is_eq(p, 0.0)))
  tally(c, okm, oka, tiny)

def run(+ctl: Bool, n: Nat, +s: Nat, c: Cnt) -> Cnt:
  match n:
    case 0n:
      c
    case 1n+k:
      run(ctl, k, rnd(rnd(rnd(rnd(rnd(s))))), step(ctl, c, s))

def show(c: Cnt) -> String:
  match c:
    case Cnt{n, sb, bd}:
      Nat.show(n) ++ " products and sums (" ++ Nat.show(sb) ++ " subnormal products), mismatches: " ++ Nat.show(bd)

# Dot products of length 8
# ------------------------

def vec(k: Nat, +s: Nat) -> List<&2, F32>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      F32.mul(draw(s), 1.0e-6) <> vec(j, rnd(rnd(rnd(rnd(rnd(rnd(s)))))))

def decs(xs: List<&2, F32>) -> List<&2, B.Bd>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> xr:
      dec(x) <> decs(xr)

def ndot(xs: List<&2, F32>, ys: List<&2, F32>) -> F32:
  match xs:
    case Nil{}:
      0.0
    case x <> xr:
      match ys:
        case Nil{}:
          0.0
        case y <> yr:
          F32.add(F32.mul(x, y), ndot(xr, yr))

def dots(n: Nat, +s: Nat, +diff: Nat) -> Nat:
  match n:
    case 0n:
      diff
    case 1n+k:
      +xs = vec(8n, s)
      +ys = vec(8n, rnd(s))
      +ok = same(dec(ndot(xs, ys)), B.Bd.f32(hb(), B.Bd.dot(hb(), decs(xs), decs(ys))))
      dots(k, rnd(rnd(rnd(s))), Nat.add(diff, Bool.pick(Nat, ok, 0n, 1n)))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show(run(False{}, 20000n, 7n, Cnt{0n, 0n, 0n})))
    IO.print("control, 2^-160 off: " ++ show(run(True{}, 500n, 7n, Cnt{0n, 0n, 0n})))
    IO.print("2000 dot products of length 8: a plain F32 loop differs from the correctly rounded result in " ++ Nat.show(dots(2000n, 11n, 0n)))
#|20000 products and sums (1768 subnormal products), mismatches: 0
#|control, 2^-160 off: 500 products and sums (51 subnormal products), mismatches: 1000
#|2000 dot products of length 8: a plain F32 loop differs from the correctly rounded result in 230
