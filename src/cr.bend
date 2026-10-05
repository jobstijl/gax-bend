# Correctly rounded kernels at run time (docs/numerics.md §3). Any kernel
# run with the big-dyadic operations below computes its outputs exactly;
# CR.f32 then rounds each output once, so the result is the binary32 value
# nearest the exact one, ties to even (proofs/cr.bend, CR.fields;
# algebras/*/cr.bend kernel by kernel). CR.of reads a float exactly and
# CR.to_f32 writes a rounded value back, exactly.

import Base
import ./dyadic.bend as D
import ./big.bend as B

# limbs in base 2h = 2^12; h = 1 + h1 so that proofs see 1n+h1 unfold. Every
# proof holds for any h; a small one keeps the checker's evaluation of
# closed terms (a kernel's zero outputs, rounded) small, and 2^12 is the
# least for which Bn.of reads a 24-bit significand into two limbs.
def CR.h1() -> Nat:
  2047n

def CR.h() -> Nat:
  1n+CR.h1()

def CR.add(x: B.Bd, y: B.Bd) -> B.Bd:
  B.Bd.add(CR.h(), x, y)

def CR.mul(x: B.Bd, y: B.Bd) -> B.Bd:
  B.Bd.mul(CR.h(), x, y)

def CR.f32(x: B.Bd) -> B.Bd:
  B.Bd.f32(CR.h(), x)

def CR.val(x: B.Bd) -> D.Dy:
  B.Bd.val(CR.h(), x)

# the exact value of a float, from its bits
def CR.of.go(+s: Bool, +n: Nat, +ex: Nat) -> B.Bd:
  Bool.pick(B.Bd, Nat.is_lt(ex, 150n), B.Bd{s, B.Bn.of(CR.h(), n), Nat.sub(150n, ex)}, B.Bd{s, B.Bn.shl(CR.h(), Nat.sub(ex, 150n), B.Bn.of(CR.h(), n)), 0n})

def CR.of(+f: F32) -> B.Bd:
  +b = U32.to_nat(F32.bits(f))
  +s = Bool.not(Nat.is_lt(b, 2147483648n))
  +ex = Nat.mod(Nat.div(b, 8388608n), 256n)
  +fr = Nat.mod(b, 8388608n)
  Bool.pick(B.Bd, Nat.is_eq(ex, 0n), CR.of.go(s, fr, 1n), CR.of.go(s, Nat.add(8388608n, fr), ex))

# a big natural as a float, top limb first: exact for at most 24
# significant bits below 2^128
def CR.bn(m: B.Bn) -> F32:
  match m:
    case B.BNil{}:
      0.0
    case B.BCons{d, r}:
      F32.add(F32.mul(CR.bn(r), F32.from_nat(Nat.double(CR.h()))), F32.from_nat(d))

def CR.half(e: Nat, +f: F32) -> F32:
  match e:
    case 0n:
      f
    case 1n+k:
      CR.half(k, F32.mul(f, 0.5))

def CR.sign(n: Bool, +f: F32) -> F32:
  match n:
    case True{}:
      F32.neg(f)
    case False{}:
      f

def CR.out(x: B.Bd) -> F32:
  match x:
    case B.Bd{n, m, +e}:
      CR.sign(n, CR.half(e, CR.bn(m)))

# a rounded value back as a float: normalised first, so the magnitude has
# at most 24 bits unless the value is a whole number
def CR.to_f32(x: B.Bd) -> F32:
  CR.out(B.Bd.norm(CR.h(), x))
