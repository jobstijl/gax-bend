# Bounded posits (b-posits): posits whose regime field stops at rs bits
# (Jonnalagadda, Thotli and Gustafson, 2026; arXiv 2603.01615). A run of k
# equal regime bits, ended by the opposite bit or by reaching rs bits,
# gives r = -k (zeros) or k - 1 (ones); the scale is T = r 2^es + e. With
# es exponent bits always present, every value in range keeps at least
# p0 = n - es - rs significant bits, so a b-posit rounds like a binary
# float whose precision depends on the scale: round to nearest, ties to
# even, at p0 + (rs - regime length) bits. Outside the range it saturates:
# never to zero below minpos, never to infinity above maxpos. The pattern 1
# is minpos = 2^-bias (1 + 2^-(p0 - 1)): 2^-bias itself would be the
# all-zero pattern, which is zero. proofs/posit.bend proves the model
#   |fl(x) - x| <= 2^-p0 |x| + minpos   whenever |x| <= maxpos,
# and the run-time version on big dyadics equal to this spec. The quire is
# Bd.dot (src/big.bend) rounded once.
#
# A format is (p0, g, rs) with g = 2^es and bias = rs g; the scale classes
# rb = r + rs run over [0, 2 rs). b-posit32 is (21, 32, 6): range 2^-192 to
# 2^192, 21 to 25 bits. b-posit16 is (7, 8, 6): range 2^-48 to 2^48.

import Base
import ./int.bend as I
import ./dyadic.bend as D
import ./round.bend as RD
import ./fast.bend as F
import ./big.bend as B

# The spec, on dyadics in normal form
# -----------------------------------

def Pz.bias(+g: Nat, +rs: Nat) -> Nat:
  Nat.mul(rs, g)

def Pz.min(+a: Nat, +b: Nat) -> Nat:
  Bool.pick(Nat, RD.Nat.lt(a, b), a, b)

# |x| < 2^(i - bias)
def Pz.below(+bias: Nat, +i: Nat, +x: D.Dy) -> Bool:
  Bool.pick(Bool, RD.Nat.lt(Nat.add(i, D.Dy.den(x)), bias), False{}, RD.Nat.lt(RD.Int.mag(D.Dy.num(x)), RD.Nat.pow2(RD.Nat.monus(Nat.add(i, D.Dy.den(x)), bias))))

# the scale class: the least rb with |x| < 2^((rb + 1) g - bias), from rb up
def Pz.find(+g: Nat, +bias: Nat, c: Nat, +rb: Nat, +x: D.Dy) -> Nat:
  match c:
    case 0n:
      rb
    case 1n+k:
      Bool.pick(Nat, Pz.below(bias, Nat.mul(1n+rb, g), x), rb, Pz.find(g, bias, k, 1n+rb, x))

# the regime field's length in class rb
def Pz.rl(+rs: Nat, +rb: Nat) -> Nat:
  Bool.pick(Nat, RD.Nat.lt(rb, rs), Pz.min(1n+RD.Nat.monus(rs, rb), rs), Pz.min(2n+RD.Nat.monus(rb, rs), rs))

# significant bits in class rb: p0 + (rs - rl)
def Pz.prec(+p0: Nat, +g: Nat, +rs: Nat, +x: D.Dy) -> Nat:
  Nat.add(p0, RD.Nat.monus(rs, Pz.rl(rs, Pz.find(g, Pz.bias(g, rs), Nat.double(rs), 0n, x))))

# maxpos = (2^p0 - 1) 2^(bias - p0), over 2^d
def Pz.maxm(+p0: Nat, +bias: Nat, +d: Nat) -> Nat:
  Nat.mul(RD.Nat.monus(RD.Nat.pow2(p0), 1n), RD.Nat.pow2(Nat.add(RD.Nat.monus(bias, p0), d)))

# minpos = (2^(p0-1) + 1) / 2^(bias + p0 - 1)
def Pz.minm(+p0: Nat) -> Nat:
  1n+RD.Nat.pow2(RD.Nat.monus(p0, 1n))

def Pz.mine(+p0: Nat, +bias: Nat) -> Nat:
  Nat.add(bias, RD.Nat.monus(p0, 1n))

# 0 < |x| < minpos, for x not zero: |m| 2^c < minm 2^d
def Pz.tiny(+p0: Nat, +bias: Nat, +x: D.Dy) -> Bool:
  RD.Nat.lt(Nat.mul(RD.Int.mag(D.Dy.num(x)), RD.Nat.pow2(Pz.mine(p0, bias))), Nat.mul(Pz.minm(p0), RD.Nat.pow2(D.Dy.den(x))))

def Pz.zero(+x: D.Dy) -> Bool:
  Bool.not(RD.Nat.lt(0n, RD.Int.mag(D.Dy.num(x))))

def Pz.over(+p0: Nat, +bias: Nat, +x: D.Dy) -> Bool:
  RD.Nat.lt(Pz.maxm(p0, bias, D.Dy.den(x)), RD.Int.mag(D.Dy.num(x)))

def Pz.fl.go(+p0: Nat, +g: Nat, +rs: Nat, z: Bool, t: Bool, o: Bool, +x: D.Dy) -> D.Dy:
  match z:
    case True{}:
      x
    case False{}:
      match t:
        case True{}:
          D.Dy.of(Pz.mine(p0, Pz.bias(g, rs)), RD.Int.signed(D.Dy.num(x), Pz.minm(p0)))
        case False{}:
          match o:
            case True{}:
              D.Dy.of(D.Dy.den(x), RD.Int.signed(D.Dy.num(x), Pz.maxm(p0, Pz.bias(g, rs), D.Dy.den(x))))
            case False{}:
              RD.Dy.rne(Pz.prec(p0, g, rs, x), x)

# b-posit rounding: zero stays, below minpos to minpos, above maxpos to
# maxpos, else to nearest at the class's precision
def Pz.fl(+p0: Nat, +g: Nat, +rs: Nat, +x: D.Dy) -> D.Dy:
  Pz.fl.go(p0, g, rs, Pz.zero(x), Pz.tiny(p0, Pz.bias(g, rs), x), Pz.over(p0, Pz.bias(g, rs), x), x)

# Run time, on big dyadics in normal form
# ---------------------------------------

def Pz.bbelow(+h: Nat, +bias: Nat, +i: Nat, x: B.Bd) -> Bool:
  match x:
    case B.Bd{n, +m, +e}:
      Bool.pick(Bool, F.Nat.ltf(Nat.add(i, e), bias), False{}, B.Bn.lt(m, B.Bn.pow2(h, F.Nat.monusf(Nat.add(i, e), bias))))

def Pz.bfind(+h: Nat, +g: Nat, +bias: Nat, c: Nat, +rb: Nat, +x: B.Bd) -> Nat:
  match c:
    case 0n:
      rb
    case 1n+k:
      Bool.pick(Nat, Pz.bbelow(h, bias, Nat.mul(1n+rb, g), x), rb, Pz.bfind(h, g, bias, k, 1n+rb, x))

def Pz.bprec(+h: Nat, +p0: Nat, +g: Nat, +rs: Nat, +x: B.Bd) -> Nat:
  Nat.add(p0, RD.Nat.monus(rs, Pz.rl(rs, Pz.bfind(h, g, Pz.bias(g, rs), Nat.double(rs), 0n, x))))

def Pz.bmaxm(+h: Nat, +p0: Nat, +bias: Nat, +d: Nat) -> B.Bn:
  B.Bn.shl(h, Nat.add(F.Nat.monusf(bias, p0), d), B.Bn.sub(h, B.Bn.pow2(h, p0), B.BCons{1n, B.BNil{}}))

# minm = 2^(p0 - 1) + 1 as limbs
def Pz.bminm(+h: Nat, +p0: Nat) -> B.Bn:
  B.Bn.addc(h, B.Bn.pow2(h, F.Nat.monusf(p0, 1n)), B.BNil{}, True{})

def Pz.btiny(+h: Nat, +p0: Nat, +bias: Nat, x: B.Bd) -> Bool:
  match x:
    case B.Bd{n, +m, +e}:
      B.Bn.lt(B.Bn.shl(h, Pz.mine(p0, bias), m), B.Bn.shl(h, e, Pz.bminm(h, p0)))

def Pz.bzero(x: B.Bd) -> Bool:
  match x:
    case B.Bd{n, m, e}:
      Bool.not(B.Bn.lt(B.BNil{}, m))

def Pz.bover(+h: Nat, +p0: Nat, +bias: Nat, x: B.Bd) -> Bool:
  match x:
    case B.Bd{n, +m, +e}:
      B.Bn.lt(Pz.bmaxm(h, p0, bias, e), m)

def Pz.bfl.go(+h: Nat, +p0: Nat, +g: Nat, +rs: Nat, z: Bool, t: Bool, o: Bool, +x: B.Bd) -> B.Bd:
  match z:
    case True{}:
      x
    case False{}:
      match t:
        case True{}:
          B.Bd{B.Bd.n(x), Pz.bminm(h, p0), Pz.mine(p0, Pz.bias(g, rs))}
        case False{}:
          match o:
            case True{}:
              B.Bd{B.Bd.n(x), Pz.bmaxm(h, p0, Pz.bias(g, rs), B.Bd.e(x)), B.Bd.e(x)}
            case False{}:
              B.Bd.rne.n(h, Pz.bprec(h, p0, g, rs, x), x)

def Pz.bfl.n(+h: Nat, +p0: Nat, +g: Nat, +rs: Nat, +x: B.Bd) -> B.Bd:
  Pz.bfl.go(h, p0, g, rs, Pz.bzero(x), Pz.btiny(h, p0, Pz.bias(g, rs), x), Pz.bover(h, p0, Pz.bias(g, rs), x), x)

def Pz.bfl(+h: Nat, +p0: Nat, +g: Nat, +rs: Nat, x: B.Bd) -> B.Bd:
  Pz.bfl.n(h, p0, g, rs, B.Bd.norm(h, x))

# Bit patterns (run time; tests/bposit.bend checks them against an
# independent bit-string rounding)
# ---------------------------------------------------------------

# the bit length of a big natural, by halving (a match on nz, so the
# recursion stops at zero: Bool.pick would run out the fuel)
def Bn.blen(+h: Nat, fuel: Nat, +b: B.Bn, nz: Bool) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      match nz:
        case True{}:
          1n+Bn.blen(h, f, B.Bn.half(h, b), B.Bn.lt(B.BNil{}, B.Bn.half(h, b)))
        case False{}:
          0n

def Nat.pw(k: Nat) -> Nat:
  Nat.pow(2n, k)

# b / 2^k, by halving
def Bn.shr(+h: Nat, k: Nat, b: B.Bn) -> B.Bn:
  match k:
    case 0n:
      b
    case 1n+j:
      Bn.shr(h, j, B.Bn.half(h, b))

# the n-bit pattern of a b-posit value (rounded, normal form, l = bit length
# of m), es = log2 g
def Pz.enc.go(+h: Nat, +n: Nat, +es: Nat, +rs: Nat, +neg: Bool, +m: B.Bn, +l: Nat, +e: Nat) -> Nat:
  +g = Nat.pw(es)
  +tb = Nat.sub(Nat.add(Nat.sub(l, 1n), Nat.mul(rs, g)), e)
  +rb = Nat.div(tb, g)
  +ee = Nat.mod(tb, g)
  +k = Bool.pick(Nat, Nat.is_lt(rb, rs), Nat.sub(rs, rb), Nat.add(Nat.sub(rb, rs), 1n))
  +rl = Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs)
  +reg = Bool.pick(Nat, Nat.is_lt(rb, rs), Bool.pick(Nat, Nat.is_lt(k, rs), 1n, 0n), Nat.mul(Nat.sub(Nat.pw(k), 1n), Bool.pick(Nat, Nat.is_lt(k, rs), 2n, 1n)))
  +fb = Nat.sub(Nat.sub(Nat.sub(n, 1n), rl), es)
  # the significand as fb + 1 bits
  +mm = Bool.pick(B.Bn, Nat.is_lt(fb, Nat.sub(l, 1n)), Bn.shr(h, Nat.sub(Nat.sub(l, 1n), fb), m), B.Bn.shl(h, Nat.sub(fb, Nat.sub(l, 1n)), m))
  +fr = Nat.sub(B.Bn.val(h, mm), Nat.pw(fb))
  +q = Nat.add(Nat.add(Nat.mul(reg, Nat.pw(Nat.sub(Nat.sub(n, 1n), rl))), Nat.mul(ee, Nat.pw(fb))), fr)
  Bool.pick(Nat, neg, Nat.sub(Nat.pw(n), q), q)

def Pz.enc.n(+h: Nat, +n: Nat, +es: Nat, +rs: Nat, x: B.Bd) -> Nat:
  match x:
    case B.Bd{neg, +m, e}:
      +l = Bn.blen(h, Nat.mul(h, B.Bn.len(m)), m, B.Bn.lt(B.BNil{}, m))
      Bool.pick(Nat, Nat.is_eq(l, 0n), 0n, Pz.enc.go(h, n, es, rs, neg, m, l, e))

def Pz.enc(+h: Nat, +n: Nat, +es: Nat, +rs: Nat, x: B.Bd) -> Nat:
  Pz.enc.n(h, n, es, rs, B.Bd.norm(h, x))

# the run length of bit b from the top of a w-bit field q, up to lim
def Pz.run(c: Nat, +q: Nat, +w: Nat, +b: Nat) -> Nat:
  match c:
    case 0n:
      0n
    case 1n+k:
      Bool.pick(Nat, Bool.and(Nat.is_lt(0n, w), Nat.is_eq(Nat.mod(Nat.div(q, Nat.pw(Nat.sub(w, 1n))), 2n), b)), 1n+Pz.run(k, q, Nat.sub(w, 1n), b), 0n)

# the exact value of an n-bit pattern (not 0 or NaR)
def Pz.dec(+h: Nat, +n: Nat, +es: Nat, +rs: Nat, +pt: Nat) -> B.Bd:
  +neg = Bool.not(Nat.is_lt(pt, Nat.pw(Nat.sub(n, 1n))))
  +q = Bool.pick(Nat, neg, Nat.sub(Nat.pw(n), pt), pt)
  +w = Nat.sub(n, 1n)
  +b = Nat.mod(Nat.div(q, Nat.pw(Nat.sub(w, 1n))), 2n)
  +k = Pz.run(rs, q, w, b)
  +rl = Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs)
  +rem = Nat.sub(w, rl)
  +ew = Bool.pick(Nat, Nat.is_lt(rem, es), rem, es)
  +fb = Nat.sub(rem, ew)
  +low = Nat.mod(q, Nat.pw(rem))
  +ee = Nat.mul(Nat.div(low, Nat.pw(fb)), Nat.pw(Nat.sub(es, ew)))
  +fr = Nat.mod(low, Nat.pw(fb))
  +g = Nat.pw(es)
  # scale + bias = (r + rs) g + e, with r = k - 1 (ones) or -k (zeros)
  +tb = Nat.add(Nat.mul(Bool.pick(Nat, Nat.is_eq(b, 1n), Nat.sub(Nat.add(k, rs), 1n), Nat.sub(rs, k)), g), ee)
  +m = B.Bn.of(h, Nat.add(Nat.pw(fb), fr))
  # value (2^fb + fr) 2^(tb - bias - fb)
  +bias = Nat.mul(rs, g)
  Bool.pick(B.Bd, Nat.is_lt(tb, Nat.add(bias, fb)), B.Bd{neg, m, Nat.sub(Nat.add(bias, fb), tb)}, B.Bd{neg, B.Bn.shl(h, Nat.sub(tb, Nat.add(bias, fb)), m), 0n})

# b-posit32: n = 32, es = 5, rs = 6
def P32.fl(+h: Nat, x: B.Bd) -> B.Bd:
  Pz.bfl(h, 21n, 32n, 6n, x)

def P32.enc(+h: Nat, x: B.Bd) -> Nat:
  Pz.enc(h, 32n, 5n, 6n, x)

def P32.dec(+h: Nat, +pt: Nat) -> B.Bd:
  Pz.dec(h, 32n, 5n, 6n, pt)
