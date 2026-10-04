# Q9: a software IEEE binary32 add and mul on U32 (round to nearest even,
# subnormals, infinities, NaNs), branch-free in the shape of Berkeley
# SoftFloat's roundPackToF32. main checks it bit for bit against native F32
# on random pairs and times both.
import Base

def sel(c: Bool, a: U32, b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

def shr(a: U32, n: U32) -> U32:
  U32.shrn(a, U32.to_nat(n))

def shl(a: U32, n: U32) -> U32:
  U32.shln(a, U32.to_nat(n))

# 1 when a is not zero
def nz(a: U32) -> U32:
  sel(U32.is_zero(a), 0, 1)

# shift right by n (any n), OR-ing every lost bit into bit 0
def shr_jam(+a: U32, +n: U32) -> U32:
  +kept = shr(a, n)
  (kept .|. nz((a - shl(kept, n) : U32)) : U32)

def clz(+x: U32) -> U32:
  +c1 = U32.is_lt(x, 65536)
  +x1 = sel(c1, (x << 16n : U32), x)
  +c2 = U32.is_lt(x1, 16777216)
  +x2 = sel(c2, (x1 << 8n : U32), x1)
  +c3 = U32.is_lt(x2, 268435456)
  +x3 = sel(c3, (x2 << 4n : U32), x2)
  +c4 = U32.is_lt(x3, 1073741824)
  +x4 = sel(c4, (x3 << 2n : U32), x3)
  +c5 = U32.is_lt(x4, 2147483648)
  +n = (sel(c1, 16, 0) + sel(c2, 8, 0) + sel(c3, 4, 0) + sel(c4, 2, 0) + sel(c5, 1, 0) : U32)
  sel(U32.is_zero(x), 32, n)

# the high word of a*b, jammed with the low word (32x32 -> 64 from 16-bit halves)
def mul_hi_jam(+a: U32, +b: U32) -> U32:
  +al = (a .&. 65535 : U32)
  +ah = (a >> 16n : U32)
  +bl = (b .&. 65535 : U32)
  +bh = (b >> 16n : U32)
  +ll = (al * bl : U32)
  +lh = (al * bh : U32)
  +mid = (lh + (ah * bl) : U32)
  +lo = (ll + (mid << 16n) : U32)
  +hi = ((ah * bh) + (mid >> 16n) + sel(U32.is_lt(mid, lh), 65536, 0) + sel(U32.is_lt(lo, ll), 1, 0) : U32)
  (hi .|. nz(lo) : U32)

# sig has its leading 1 at bit 30 and 7 round bits; e is the biased exponent
# minus one, as a two's-complement U32 (negative: the result is subnormal)
def round_pack(+s: U32, +e: U32, +sig: U32) -> U32:
  +neg = U32.is_ge(e, 2147483648)
  +sig1 = sel(neg, shr_jam(sig, (0 - e : U32)), sig)
  +e1 = sel(neg, 0, e)
  +rb = (sig1 .&. 127 : U32)
  +big = Bool.or(U32.is_gt(e1, 253), Bool.and(U32.is_eq(e1, 253), U32.is_ge((sig1 + 64 : U32), 2147483648)))
  +ovf = Bool.and(Bool.not(neg), big)
  +sig2 = ((sig1 + 64 : U32) >> 7n : U32)
  +sig3 = sel(U32.is_eq(rb, 64), (sig2 .&. 4294967294 : U32), sig2)
  +e2 = sel(U32.is_zero(sig3), 0, e1)
  sel(ovf, ((s << 31n) + 2139095040 : U32), ((s << 31n) + (e2 << 23n) + sig3 : U32))

def is_nan(+a: U32) -> Bool:
  U32.is_gt((a .&. 2147483647 : U32), 2139095040)

def is_inf(+a: U32) -> Bool:
  U32.is_eq((a .&. 2147483647 : U32), 2139095040)

def is_zero(+a: U32) -> Bool:
  U32.is_zero((a .&. 2147483647 : U32))

# NaN results: a NaN operand comes back quiet (a's first); an invalid
# operation gives x86's default NaN 0xFFC00000
def nan_pick(+a: U32, +b: U32, r: U32) -> U32:
  sel(is_nan(a), (a .|. 4194304 : U32), sel(is_nan(b), (b .|. 4194304 : U32), r))

def SoftF32.mul(+a: U32, +b: U32) -> U32:
  +s = ((a .^. b : U32) >> 31n : U32)
  +ea = ((a >> 23n : U32) .&. 255 : U32)
  +eb = ((b >> 23n : U32) .&. 255 : U32)
  +ma = (a .&. 8388607 : U32)
  +mb = (b .&. 8388607 : U32)
  +sa = U32.is_zero(ea)
  +sb = U32.is_zero(eb)
  +ka = (clz(ma) - 8 : U32)
  +kb = (clz(mb) - 8 : U32)
  +na = sel(sa, shl(ma, ka), (ma .|. 8388608 : U32))
  +nb = sel(sb, shl(mb, kb), (mb .|. 8388608 : U32))
  +xa = sel(sa, (1 - ka : U32), ea)
  +xb = sel(sb, (1 - kb : U32), eb)
  +z = mul_hi_jam((na << 7n : U32), (nb << 8n : U32))
  +small = U32.is_lt(z, 1073741824)
  +ez = (xa + xb - 127 : U32)
  +r = round_pack(s, sel(small, (ez - 1 : U32), ez), sel(small, (z << 1n : U32), z))
  +inf = Bool.or(is_inf(a), is_inf(b))
  +zero = Bool.or(is_zero(a), is_zero(b))
  +inv = Bool.and(inf, zero)
  +r1 = sel(inf, ((s << 31n) + 2139095040 : U32), sel(zero, (s << 31n : U32), r))
  nan_pick(a, b, sel(inv, 4290772992, r1))

def SoftF32.add(+a: U32, +b: U32) -> U32:
  +swap = U32.is_lt((a .&. 2147483647 : U32), (b .&. 2147483647 : U32))
  +x = sel(swap, b, a)
  +y = sel(swap, a, b)
  +sx = (x >> 31n : U32)
  +ex = ((x >> 23n : U32) .&. 255 : U32)
  +ey = ((y >> 23n : U32) .&. 255 : U32)
  +mx = (x .&. 8388607 : U32)
  +my = (y .&. 8388607 : U32)
  +nx = sel(U32.is_zero(ex), mx, (mx .|. 8388608 : U32))
  +ny = sel(U32.is_zero(ey), my, (my .|. 8388608 : U32))
  +xe = sel(U32.is_zero(ex), 1, ex)
  +ye = sel(U32.is_zero(ey), 1, ey)
  +gx = (nx << 6n : U32)
  +gy = shr_jam((ny << 6n : U32), (xe - ye : U32))
  +same = U32.is_eq(sx, (y >> 31n : U32))
  +sum = sel(same, (gx + gy : U32), (gx - gy : U32))
  +k = (clz(sum) - 1 : U32)
  +r = round_pack(sx, (xe - k : U32), shl(sum, k))
  +r2 = sel(U32.is_zero(sum), sel(same, (sx << 31n : U32), 0), r)
  +inv = Bool.and(Bool.and(is_inf(x), is_inf(y)), Bool.not(same))
  nan_pick(a, b, sel(inv, 4290772992, sel(is_inf(x), x, r2)))

def F32.of_bits(u: U32) -> F32:
  match u:
    case U32{w}:
      F32{w}

def Nat.add_ok(+x: U32, +y: U32) -> Bool:
  Bool.or(U32.is_eq(x, y), Bool.and(is_nan(x), is_nan(y)))

def next(+x: U32) -> U32:
  +x1 = (x .^. (x << 13n) : U32)
  +x2 = (x1 .^. (x1 >> 17n) : U32)
  (x2 .^. (x2 << 5n) : U32)

def check.one(+a: U32, +b: U32) -> U32:
  +na = F32.bits(F32.add(F32.of_bits(a), F32.of_bits(b)))
  +nm = F32.bits(F32.mul(F32.of_bits(a), F32.of_bits(b)))
  (sel(Nat.add_ok(SoftF32.add(a, b), na), 0, 1) + sel(Nat.add_ok(SoftF32.mul(a, b), nm), 0, 65536) : U32)

# random pairs, and near-cancelling pairs (b = -a nudged in its low bits)
def check(n: Nat, +x: U32, bad: U32) -> U32:
  match n:
    case 0n:
      bad
    case 1n+k:
      +y = next(x)
      +z = next(y)
      +near = ((x .^. 2147483648 : U32) + (z .&. 255 : U32) : U32)
      check(k, z, (bad + check.one(x, y) + check.one(x, near) : U32))

def soft.loop(n: Nat, +x: U32, acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+k:
      +y = next(x)
      soft.loop(k, y, SoftF32.add(acc, SoftF32.mul((x .&. 1065353215 : U32), (y .&. 1065353215 : U32))))

def native.loop(n: Nat, +x: U32, acc: F32) -> F32:
  match n:
    case 0n:
      acc
    case 1n+k:
      +y = next(x)
      native.loop(k, y, F32.add(acc, F32.mul(F32.of_bits((x .&. 1065353215 : U32)), F32.of_bits((y .&. 1065353215 : U32)))))

def main() -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +bad : U32 = check(8388608n, 2463534242, 0)
    +t1 : Nat <- IO.now()
    IO.print("2^24 pairs checked: add mismatches " ++ U32.show((bad .&. 65535 : U32)) ++ ", mul mismatches " ++ U32.show((bad >> 16n : U32)) ++ " (" ++ Nat.show(Nat.sub(t1, t0)) ++ " ms)")
    +s : U32 = soft.loop(16777216n, 88172645, 0)
    +t2 : Nat <- IO.now()
    +f : F32 = native.loop(16777216n, 88172645, 0.0)
    +t3 : Nat <- IO.now()
    IO.print("2^24 mul+add: soft " ++ Nat.show(Nat.sub(t2, t1)) ++ " ms, native " ++ Nat.show(Nat.sub(t3, t2)) ++ " ms; same bits: " ++ Bool.show(U32.is_eq(s, F32.bits(f))))
