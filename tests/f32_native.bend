# Native F32 arithmetic is binary32 rounding of the exact result. Each
# sample builds two floats natively, reads their bits as dyadics, and
# compares the bits of the native product and sum against Dy.f32f of the
# exact product and sum (src/fast.bend, proven equal to Dy.f32 by
# proofs/fast.bend, imported so the gate checks it; Dy.f32 meets the
# rounding model by proofs/round.bend).
# Products reach the subnormal range and underflow to zero; sums cancel.
#
# Within run-time Nat (2^48 - 1, bend-facts Q16): significands below 2^24,
# exponents down to 2^-86, so a product's denominator stays at most 2^172
# (the range test computes 2^(d - 126)), and sums are checked only when
# the exponents differ by at most 23. The control flips the low bit of each
# expected result, so the comparison can fail.
import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/round.bend as RD
import ../src/fast.bend as F
import ../proofs/fast.bend as FL

# Park-Miller: x 16807 mod (2^31 - 1), below 2^46
def rnd(+x: Nat) -> Nat:
  Nat.mod(Nat.mul(x, 16807n), 2147483647n)

# m 2^-e, built natively: m is exact, each halving is exact while normal
def mk(+m: Nat, e: Nat) -> F32:
  match e:
    case 0n:
      U32.to_f32(U32.from_nat(m))
    case 1n+j:
      F32.mul(mk(m, j), 0.5)

# the exact value of a float, from its bits
def dec.go(+n: Nat, +ex: Nat) -> D.Dy:
  Bool.pick(D.Dy, Nat.is_lt(ex, 150n), F.Dy.off(Nat.sub(150n, ex), I.IPos{n}), D.DInt{I.IPos{Nat.mul(n, RD.Nat.pow2(Nat.sub(ex, 150n)))}})

def dec(+f: F32) -> D.Dy:
  +b = U32.to_nat(F32.bits(f))
  +ex = Nat.mod(Nat.div(b, 8388608n), 256n)
  +fr = Nat.mod(b, 8388608n)
  +v = Bool.pick(D.Dy, Nat.is_eq(ex, 0n), dec.go(fr, 1n), dec.go(Nat.add(8388608n, fr), ex))
  Bool.pick(D.Dy, Nat.is_lt(b, 2147483648n), v, D.Dy.neg(v))

def same(+x: D.Dy, +y: D.Dy) -> Bool:
  +a = D.Dy.num(x)
  +b = D.Dy.num(y)
  Bool.and(Nat.is_eq(D.Dy.den(x), D.Dy.den(y)),
    Bool.and(Nat.is_eq(RD.Int.mag(a), RD.Int.mag(b)), Bool.or(Nat.is_eq(RD.Int.mag(a), 0n), Bool.not(Bool.xor(I.Int.pos(a), I.Int.pos(b))))))

# the expected value, or with its low numerator bit flipped (control)
def want(ctl: Bool, +z: D.Dy) -> D.Dy:
  match ctl:
    case False{}:
      z
    case True{}:
      F.Dy.off(1n+D.Dy.den(z), F.Int.addf(D.Int.dbl(D.Dy.num(z)), I.IPos{1n}))

# a random float: 1 to 24 significant bits, exponent 2^-86 to 1, either sign
def draw(+s: Nat) -> F32:
  +w : Nat = 1n+Nat.mod(s, 24n)
  +m : Nat = 1n+Nat.mod(rnd(s), Nat.sub(RD.Nat.pow2(w), 1n))
  +f = mk(m, Nat.mod(rnd(rnd(s)), 87n))
  Bool.pick(F32, Nat.is_eq(Nat.mod(rnd(rnd(rnd(s))), 2n), 0n), f, F32.neg(f))

type Cnt is Data:
  Cnt{mul: Nat, add: Nat, sub: Nat, skip: Nat, bad: Nat}

def tally(+c: Cnt, +ok: Bool, +sub: Bool, +skip: Bool, +okadd: Bool) -> Cnt:
  match c:
    case Cnt{m, a, s, k, b}:
      Cnt{1n+m, Bool.pick(Nat, skip, a, 1n+a), Bool.pick(Nat, sub, 1n+s, s), Bool.pick(Nat, skip, 1n+k, k),
        Nat.add(b, Nat.add(Bool.pick(Nat, ok, 0n, 1n), Bool.pick(Nat, Bool.or(skip, okadd), 0n, 1n)))}

# the rounded sum, when the exponents are near (a match: Bool.pick would
# compute it regardless)
def sum(far: Bool, +x: D.Dy, +y: D.Dy) -> D.Dy:
  match far:
    case True{}:
      D.Dy.zero()
    case False{}:
      F.Dy.f32f(F.Dy.addaf(x, y))

def step(+ctl: Bool, +c: Cnt, +s: Nat) -> Cnt:
  +a = draw(s)
  +b = draw(rnd(rnd(rnd(rnd(s)))))
  +x = dec(a)
  +y = dec(b)
  +p = F.Dy.f32f(F.Dy.mulf(x, y))
  +far = Nat.is_lt(23n, Bool.pick(Nat, Nat.is_lt(D.Dy.den(x), D.Dy.den(y)), Nat.sub(D.Dy.den(y), D.Dy.den(x)), Nat.sub(D.Dy.den(x), D.Dy.den(y))))
  +q = sum(far, x, y)
  tally(c, same(dec(F32.mul(a, b)), want(ctl, p)), Bool.and(RD.Nat.lt(0n, RD.Int.mag(D.Dy.num(p))), Bool.not(F.Dy.bigf(p))), far, same(dec(F32.add(a, b)), want(ctl, q)))

def run(+ctl: Bool, n: Nat, +s: Nat, +c: Cnt) -> Cnt:
  match n:
    case 0n:
      c
    case 1n+k:
      run(ctl, k, rnd(rnd(rnd(rnd(rnd(s))))), step(ctl, c, s))

def show(c: Cnt) -> String:
  match c:
    case Cnt{m, a, s, k, b}:
      Nat.show(m) ++ " products (" ++ Nat.show(s) ++ " subnormal), " ++ Nat.show(a) ++ " sums, mismatches: " ++ Nat.show(b)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show(run(False{}, 100000n, 7n, Cnt{0n, 0n, 0n, 0n, 0n})))
    IO.print("control, low bit flipped: " ++ show(run(True{}, 2000n, 7n, Cnt{0n, 0n, 0n, 0n, 0n})))
#|100000 products (4253 subnormal), 46829 sums, mismatches: 0
#|control, low bit flipped: 2000 products (87 subnormal), 915 sums, mismatches: 2915
