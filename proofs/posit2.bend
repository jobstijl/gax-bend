# b-posit patterns (src/posit.bend), the bit-level part: Base's Nat
# division by powers of two ((q d + b) / d = q and (q d + b) mod d = b for
# b < d), reading a bit (Bit.of), the regime run (Run.ok, Same.bits), and
# the decoder unfolded one step at a time (Dec.core: a positive pattern
# whose fields are known decodes to Dfin of them). proofs/posit4.bend
# builds the decoder's correctness on these.

import Base
import ../src/round.bend as RD
import ./nat.bend as NL
import ./base.bend as B
import ./norm.bend as NP
import ./dyadic.bend as Y
import ./round.bend as R
import ./big.bend as BP
import ./eft.bend as E
import ./eft2.bend as E2
import ../src/posit.bend as P
import ../src/big.bend as SB

# go(n, m, d, r) counts n down; m is the steps left before the quotient d
# grows, r the steps taken since. A run of s <= m steps only adds to r.
def Dm.short(+s: Nat, +m: Nat, +d: Nat, +r: Nat, +h: {RD.Nat.lt(m, s) == False{} : Bool})
  -> {Nat.divmod.go(s, m, d, r) == (d, Nat.add(r, s)) : Nat & Nat}:
  match s:
    case 0n:
      Equal.cong(Nat, Nat & Nat, z => (d, z), r, Nat.add(r, 0n), Equal.sym(Nat, Nat.add(r, 0n), r, NL.Nat.add_zero_r(r)))
    case 1n+(+s2):
      match m:
        case 0n:
          Empty.absurd({Nat.divmod.go(1n+s2, 0n, d, r) == (d, Nat.add(r, 1n+s2)) : Nat & Nat}, B.Bool.tf.empty(h))
        case 1n+(+m2):
          Equal.trans(Nat & Nat, Nat.divmod.go(s2, m2, d, 1n+r), (d, Nat.add(1n+r, s2)), (d, Nat.add(r, 1n+s2)), Dm.short(s2, m2, d, 1n+r, h),
            Equal.cong(Nat, Nat & Nat, z => (d, z), 1n+Nat.add(r, s2), Nat.add(r, 1n+s2), Equal.sym(Nat, Nat.add(r, 1n+s2), 1n+Nat.add(r, s2), NL.Nat.add_succ_r(r, s2))))

# k + 1 + n steps from k left: the block ends, d grows, r restarts
def Dm.skip(+k: Nat, +n: Nat, +d: Nat, +r: Nat)
  -> {Nat.divmod.go(Nat.add(k, 1n+n), k, d, r) == Nat.divmod.go(n, Nat.add(r, k), 1n+d, 0n) : Nat & Nat}:
  match k:
    case 0n:
      Equal.cong(Nat, Nat & Nat, z => Nat.divmod.go(n, z, 1n+d, 0n), r, Nat.add(r, 0n), Equal.sym(Nat, Nat.add(r, 0n), r, NL.Nat.add_zero_r(r)))
    case 1n+(+k2):
      Equal.trans(Nat & Nat, Nat.divmod.go(Nat.add(k2, 1n+n), k2, d, 1n+r), Nat.divmod.go(n, Nat.add(1n+r, k2), 1n+d, 0n), Nat.divmod.go(n, Nat.add(r, 1n+k2), 1n+d, 0n),
        Dm.skip(k2, n, d, 1n+r),
        Equal.cong(Nat, Nat & Nat, z => Nat.divmod.go(n, z, 1n+d, 0n), 1n+Nat.add(r, k2), Nat.add(r, 1n+k2), Equal.sym(Nat, Nat.add(r, 1n+k2), 1n+Nat.add(r, k2), NL.Nat.add_succ_r(r, k2))))

# q whole blocks and then b < 1 + bp steps: quotient d + q, remainder b
def Dm.full(+q: Nat, +b: Nat, +bp: Nat, +d: Nat, +hb: {RD.Nat.lt(bp, b) == False{} : Bool})
  -> {Nat.divmod.go(Nat.add(Nat.mul(q, 1n+bp), b), bp, d, 0n) == (Nat.add(d, q), b) : Nat & Nat}:
  match q:
    case 0n:
      Equal.trans(Nat & Nat, Nat.divmod.go(b, bp, d, 0n), (d, b), (Nat.add(d, 0n), b), Dm.short(b, bp, d, 0n, hb),
        Equal.cong(Nat, Nat & Nat, z => (z, b), d, Nat.add(d, 0n), Equal.sym(Nat, Nat.add(d, 0n), d, NL.Nat.add_zero_r(d))))
    case 1n+(+q2):
      +x = Nat.mul(q2, 1n+bp)
      # (1 + bp + x) + b = bp + (1 + (x + b))
      +e : {Nat.add(Nat.add(1n+bp, x), b) == Nat.add(bp, 1n+Nat.add(x, b)) : Nat} = Equal.trans(Nat, Nat.add(Nat.add(1n+bp, x), b), 1n+Nat.add(bp, Nat.add(x, b)), Nat.add(bp, 1n+Nat.add(x, b)),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(bp, x), b), Nat.add(bp, Nat.add(x, b)), NL.Nat.add_assoc(bp, x, b)),
        Equal.sym(Nat, Nat.add(bp, 1n+Nat.add(x, b)), 1n+Nat.add(bp, Nat.add(x, b)), NL.Nat.add_succ_r(bp, Nat.add(x, b))))
      Equal.trans(Nat & Nat, Nat.divmod.go(Nat.add(Nat.add(1n+bp, x), b), bp, d, 0n), Nat.divmod.go(Nat.add(x, b), bp, 1n+d, 0n), (Nat.add(d, 1n+q2), b),
        Equal.trans(Nat & Nat, Nat.divmod.go(Nat.add(Nat.add(1n+bp, x), b), bp, d, 0n), Nat.divmod.go(Nat.add(bp, 1n+Nat.add(x, b)), bp, d, 0n), Nat.divmod.go(Nat.add(x, b), bp, 1n+d, 0n),
          Equal.cong(Nat, Nat & Nat, z => Nat.divmod.go(z, bp, d, 0n), Nat.add(Nat.add(1n+bp, x), b), Nat.add(bp, 1n+Nat.add(x, b)), e),
          Dm.skip(bp, Nat.add(x, b), d, 0n)),
        Equal.trans(Nat & Nat, Nat.divmod.go(Nat.add(x, b), bp, 1n+d, 0n), (Nat.add(1n+d, q2), b), (Nat.add(d, 1n+q2), b), Dm.full(q2, b, bp, 1n+d, hb),
          Equal.cong(Nat, Nat & Nat, z => (z, b), 1n+Nat.add(d, q2), Nat.add(d, 1n+q2), Equal.sym(Nat, Nat.add(d, 1n+q2), 1n+Nat.add(d, q2), NL.Nat.add_succ_r(d, q2)))))

# (q d + b) / d = q and (q d + b) mod d = b, for b < d
def Div.of(+q: Nat, +b: Nat, +bp: Nat, +hb: {RD.Nat.lt(bp, b) == False{} : Bool})
  -> {Nat.divmod(Nat.add(Nat.mul(q, 1n+bp), b), 1n+bp) == (q, b) : Nat & Nat}:
  Dm.full(q, b, bp, 0n, hb)

def Div.q(+q: Nat, +b: Nat, +bp: Nat, +hb: {RD.Nat.lt(bp, b) == False{} : Bool}) -> {Nat.div(Nat.add(Nat.mul(q, 1n+bp), b), 1n+bp) == q : Nat}:
  Equal.cong(Nat & Nat, Nat, z => Pair.fst(Nat, Nat, z), Nat.divmod(Nat.add(Nat.mul(q, 1n+bp), b), 1n+bp), (q, b), Div.of(q, b, bp, hb))

def Div.r(+q: Nat, +b: Nat, +bp: Nat, +hb: {RD.Nat.lt(bp, b) == False{} : Bool}) -> {Nat.mod(Nat.add(Nat.mul(q, 1n+bp), b), 1n+bp) == b : Nat}:
  Equal.cong(Nat & Nat, Nat, z => Pair.snd(Nat, Nat, z), Nat.divmod(Nat.add(Nat.mul(q, 1n+bp), b), 1n+bp), (q, b), Div.of(q, b, bp, hb))

# Base's operations and the project's
# -----------------------------------

def Pw.eq(+k: Nat) -> {Nat.pow(2n, k) == RD.Nat.pow2(k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +x = Nat.pow(2n, j)
      Equal.trans(Nat, Nat.add(x, Nat.add(x, 0n)), Nat.double(x), Nat.double(RD.Nat.pow2(j)),
        Equal.trans(Nat, Nat.add(x, Nat.add(x, 0n)), Nat.add(x, x), Nat.double(x), Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(x, 0n), x, NL.Nat.add_zero_r(x)), Equal.sym(Nat, Nat.double(x), Nat.add(x, x), Y.Nat.double_add(x))),
        Equal.cong(Nat, Nat, z => Nat.double(z), x, RD.Nat.pow2(j), Pw.eq(j)))

def Sub.eq(+a: Nat, +b: Nat) -> {Nat.sub(a, b) == RD.Nat.monus(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+b2:
      {==}
    case 1n+a2 0n:
      {==}
    case 1n+(+a2) 1n+(+b2):
      Sub.eq(a2, b2)

def Lt.eq(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == RD.Nat.lt(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+b2:
      {==}
    case 1n+a2 0n:
      {==}
    case 1n+(+a2) 1n+(+b2):
      Lt.eq(a2, b2)

def Eq.eq(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == Bool.and(Bool.not(RD.Nat.lt(a, b)), Bool.not(RD.Nat.lt(b, a))) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+b2:
      {==}
    case 1n+a2 0n:
      {==}
    case 1n+(+a2) 1n+(+b2):
      Eq.eq(a2, b2)

# Bits
# ----

def Pw.pos(+i: Nat) -> {RD.Nat.pow2(i) == 1n+RD.Nat.monus(RD.Nat.pow2(i), 1n) : Nat}:
  BP.Lt.wit(0n, RD.Nat.pow2(i))(BP.Pow2.pos(i))

# bit i of A 2^(i+1) + beta 2^i + gamma, gamma < 2^i, beta < 2, is beta
def Bit.of(+A: Nat, +beta: Nat, +gam: Nat, +i: Nat, +hb: {RD.Nat.lt(1n, beta) == False{} : Bool}, +hg: {RD.Nat.lt(gam, RD.Nat.pow2(i)) == True{} : Bool})
  -> {Nat.mod(Nat.div(Nat.add(Nat.add(Nat.mul(A, RD.Nat.pow2(1n+i)), Nat.mul(beta, RD.Nat.pow2(i))), gam), Nat.pow(2n, i)), 2n) == beta : Nat}:
  +P = RD.Nat.pow2(i)
  +pm = RD.Nat.monus(P, 1n)
  +ep : {P == 1n+pm : Nat} = Pw.pos(i)
  +t = Nat.add(Nat.add(Nat.mul(A, RD.Nat.pow2(1n+i)), Nat.mul(beta, P)), gam)
  +qq = Nat.add(Nat.mul(A, 2n), beta)
  # t = (2A + beta) 2^i + gam
  +env : List<&2, Nat> = [A, beta, gam, P, RD.Nat.pow2(1n+i), 1n]
  +et : {t == Nat.add(Nat.mul(qq, P), gam) : Nat} = R.NatN.eq2(env, R.Ad(R.Ad(R.Ml(R.V(0n), R.V(4n)), R.Ml(R.V(1n), R.V(3n))), R.V(2n)), R.Ad(R.Ml(R.Ad(R.Ml(R.V(0n), R.Ad(R.V(5n), R.V(5n))), R.V(1n)), R.V(3n)), R.V(2n)), [R.V(0n)], [R.Ad(R.V(4n), R.Ng(R.Ad(R.V(3n), R.V(3n))))], [R.Ad(R.Ml(R.V(0n), R.V(3n)), R.Ng(R.Ml(R.Ml(R.V(0n), R.V(3n)), R.V(5n)))), R.Ad(R.Ml(R.V(0n), R.V(3n)), R.Ng(R.Ml(R.Ml(R.V(0n), R.V(3n)), R.V(5n))))], {==}, (R.NatN.z(env, R.V(4n), R.Ad(R.V(3n), R.V(3n)), {==}, {==}, Y.Nat.double_add(P)), Unit{}), (R.NatN.z(env, R.Ml(R.V(0n), R.V(3n)), R.Ml(R.Ml(R.V(0n), R.V(3n)), R.V(5n)), {==}, {==}, Equal.sym(Nat, Nat.mul(Nat.mul(A, P), 1n), Nat.mul(A, P), NL.Nat.mul_one_r(Nat.mul(A, P)))), (R.NatN.z(env, R.Ml(R.V(0n), R.V(3n)), R.Ml(R.Ml(R.V(0n), R.V(3n)), R.V(5n)), {==}, {==}, Equal.sym(Nat, Nat.mul(Nat.mul(A, P), 1n), Nat.mul(A, P), NL.Nat.mul_one_r(Nat.mul(A, P)))), Unit{})), {==}, {==})
  +hg2 : {RD.Nat.lt(pm, gam) == False{} : Bool} = E2.Le.of_lt1(gam, pm, Equal.trans(Bool, RD.Nat.lt(gam, 1n+pm), RD.Nat.lt(gam, P), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(gam, z), 1n+pm, P, Equal.sym(Nat, P, 1n+pm, ep)), hg))
  # t / 2^i = 2A + beta, and that mod 2 is beta
  +ed : {Nat.div(t, Nat.pow(2n, i)) == qq : Nat} = Equal.trans(Nat, Nat.div(t, Nat.pow(2n, i)), Nat.div(Nat.add(Nat.mul(qq, 1n+pm), gam), 1n+pm), qq,
    Equal.trans(Nat, Nat.div(t, Nat.pow(2n, i)), Nat.div(t, 1n+pm), Nat.div(Nat.add(Nat.mul(qq, 1n+pm), gam), 1n+pm),
      Equal.cong(Nat, Nat, z => Nat.div(t, z), Nat.pow(2n, i), 1n+pm, Equal.trans(Nat, Nat.pow(2n, i), P, 1n+pm, Pw.eq(i), ep)),
      Equal.cong(Nat, Nat, z => Nat.div(z, 1n+pm), t, Nat.add(Nat.mul(qq, 1n+pm), gam), Equal.trans(Nat, t, Nat.add(Nat.mul(qq, P), gam), Nat.add(Nat.mul(qq, 1n+pm), gam), et, Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(qq, z), gam), P, 1n+pm, ep)))),
    Div.q(qq, gam, pm, hg2))
  Equal.trans(Nat, Nat.mod(Nat.div(t, Nat.pow(2n, i)), 2n), Nat.mod(qq, 2n), beta, Equal.cong(Nat, Nat, z => Nat.mod(z, 2n), Nat.div(t, Nat.pow(2n, i)), qq, ed),
    Equal.trans(Nat, Nat.mod(qq, 2n), Nat.mod(Nat.add(Nat.mul(A, 1n+1n), beta), 1n+1n), beta, {==}, Div.r(A, beta, 1n, hb)))

# Regime runs
# -----------

def Bitq(+q: Nat, +i: Nat) -> Nat:
  Nat.mod(Nat.div(q, P.Nat.pw(i)), 2n)

def Sub.z(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+a2:
      {==}

def Eq.refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+(+a2):
      Eq.refl(a2)

def Eq.true(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+b2:
      B.Bool.tf({0n == 1n+b2 : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+a2 0n:
      B.Bool.tf({1n+a2 == 0n : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+(+a2) 1n+(+b2):
      Equal.cong(Nat, Nat, z => 1n+z, a2, b2, Eq.true(a2, b2, h))

def Run.stop.go(+c2: Nat, +q: Nat, +w2: Nat, +b: Nat, hst: {Bitq(q, RD.Nat.monus(1n+w2, 1n)) == b : Nat} -> Empty, e: Bool, +ee: {Nat.is_eq(Bitq(q, w2), b) == e : Bool})
  -> {P.Pz.run(1n+c2, q, 1n+w2, b) == 0n : Nat}:
  match e:
    case False{}:
      Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 1n+P.Pz.run(c2, q, Nat.sub(1n+w2, 1n), b), 0n), Nat.is_eq(Bitq(q, Nat.sub(w2, 0n)), b), False{},
        Equal.trans(Bool, Nat.is_eq(Bitq(q, Nat.sub(w2, 0n)), b), Nat.is_eq(Bitq(q, w2), b), False{}, Equal.cong(Nat, Bool, z => Nat.is_eq(Bitq(q, z), b), Nat.sub(w2, 0n), w2, Sub.z(w2)), ee))
    case True{}:
      Empty.absurd({P.Pz.run(1n+c2, q, 1n+w2, b) == 0n : Nat}, hst(Equal.trans(Nat, Bitq(q, RD.Nat.monus(1n+w2, 1n)), Bitq(q, w2), b, Equal.cong(Nat, Nat, z => Bitq(q, z), RD.Nat.monus(w2, 0n), w2, BP.Mo.z(w2)), Eq.true(Bitq(q, w2), b, ee))))

# the run stops at once when the top bit differs from b
def Run.stop(+c2: Nat, +q: Nat, +w: Nat, +b: Nat, hst: {Bitq(q, RD.Nat.monus(w, 1n)) == b : Nat} -> Empty) -> {P.Pz.run(1n+c2, q, w, b) == 0n : Nat}:
  match w:
    case 0n:
      {==}
    case 1n+(+w2):
      Run.stop.go(c2, q, w2, b, hst, Nat.is_eq(Bitq(q, w2), b), {==})

# the top k bits of a w-bit field q are all b
def Bits.ok(+k: Nat, +q: Nat, +w: Nat, +b: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+k2:
      match w:
        case 0n:
          False{}
        case 1n+(+w2):
          Bool.and(Nat.is_eq(Bitq(q, w2), b), Bits.ok(k2, q, w2, b))

# the run of b from the top of a w-bit field: if the first k bits are b
# and (when the fuel c allows more) the next is not, the run is k
def Run.ok(+k: Nat, +c: Nat, +w: Nat, +q: Nat, +b: Nat, +hkc: {RD.Nat.lt(c, k) == False{} : Bool}, +hkw: {RD.Nat.lt(w, k) == False{} : Bool},
  +hb: {Bits.ok(k, q, w, b) == True{} : Bool},
  hs: {RD.Nat.lt(k, c) == True{} : Bool} -> {Bitq(q, RD.Nat.monus(w, 1n+k)) == b : Nat} -> Empty)
  -> {P.Pz.run(c, q, w, b) == k : Nat}:
  match k:
    case 0n:
      match c:
        case 0n:
          {==}
        case 1n+(+c2):
          Run.stop(c2, q, w, b, h => hs({==}, h))
    case 1n+(+k2):
      match c:
        case 0n:
          B.Bool.tf({P.Pz.run(0n, q, w, b) == 1n+k2 : Nat}, hkc)
        case 1n+(+c2):
          match w:
            case 0n:
              B.Bool.tf({P.Pz.run(1n+c2, q, 0n, b) == 1n+k2 : Nat}, hkw)
            case 1n+(+w2):
              +bit0 : {Bitq(q, w2) == b : Nat} = Eq.true(Bitq(q, w2), b, NP.Bool.and_l(Nat.is_eq(Bitq(q, w2), b), Bits.ok(k2, q, w2, b), hb))
              +ih : {P.Pz.run(c2, q, w2, b) == k2 : Nat} = Run.ok(k2, c2, w2, q, b, hkc, hkw, NP.Bool.and_r(Nat.is_eq(Bitq(q, w2), b), Bits.ok(k2, q, w2, b), hb), hk => hbt => hs(hk, hbt))
              +e1 = Equal.cong(Nat, Nat, z => Bool.pick(Nat, Nat.is_eq(Bitq(q, z), b), 1n+P.Pz.run(c2, q, z, b), 0n), Nat.sub(w2, 0n), w2, Sub.z(w2))
              +e2 = Equal.cong(Nat, Nat, z => Bool.pick(Nat, Nat.is_eq(z, b), 1n+P.Pz.run(c2, q, w2, b), 0n), Bitq(q, w2), b, bit0)
              +e3 = Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 1n+P.Pz.run(c2, q, w2, b), 0n), Nat.is_eq(b, b), True{}, Eq.refl(b))
              Equal.trans(Nat, P.Pz.run(1n+c2, q, 1n+w2, b), Bool.pick(Nat, Nat.is_eq(Bitq(q, w2), b), 1n+P.Pz.run(c2, q, w2, b), 0n), 1n+k2, e1,
                Equal.trans(Nat, Bool.pick(Nat, Nat.is_eq(Bitq(q, w2), b), 1n+P.Pz.run(c2, q, w2, b), 0n), Bool.pick(Nat, Nat.is_eq(b, b), 1n+P.Pz.run(c2, q, w2, b), 0n), 1n+k2, e2,
                  Equal.trans(Nat, Bool.pick(Nat, Nat.is_eq(b, b), 1n+P.Pz.run(c2, q, w2, b), 0n), 1n+P.Pz.run(c2, q, w2, b), 1n+k2, e3, Equal.cong(Nat, Nat, z => 1n+z, P.Pz.run(c2, q, w2, b), k2, ih))))

# the top k bits of A 2^(k+v) + b (2^k - 1) 2^v + low, low < 2^v, are b
def Same.bits(+k: Nat, +v: Nat, +A: Nat, +b: Nat, +low: Nat, +q: Nat, +hb: {RD.Nat.lt(1n, b) == False{} : Bool}, +hl: {RD.Nat.lt(low, RD.Nat.pow2(v)) == True{} : Bool},
  +hq: {q == Nat.add(Nat.add(Nat.mul(A, RD.Nat.pow2(Nat.add(k, v))), Nat.mul(b, Nat.mul(RD.Nat.monus(RD.Nat.pow2(k), 1n), RD.Nat.pow2(v)))), low) : Nat})
  -> {Bits.ok(k, q, Nat.add(k, v), b) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+k2):
      +w2 = Nat.add(k2, v)
      +Pk = RD.Nat.pow2(k2)
      +Pv = RD.Nat.pow2(v)
      +M1 = RD.Nat.monus(RD.Nat.pow2(1n+k2), 1n)
      +Mk = RD.Nat.monus(Pk, 1n)
      +PW = RD.Nat.pow2(w2)
      +PW1 = RD.Nat.pow2(1n+w2)
      +P1k = RD.Nat.pow2(1n+k2)
      +env : List<&2, Nat> = [A, b, Pk, Pv, M1, Mk, low, PW, PW1, P1k, 1n]
      +X = Nat.mul(Mk, Pv)
      +gam = Nat.add(Nat.mul(b, X), low)
      +eq : {q == Nat.add(Nat.add(Nat.mul(A, PW1), Nat.mul(b, PW)), gam) : Nat} = Equal.trans(Nat, q, Nat.add(Nat.add(Nat.mul(A, PW1), Nat.mul(b, Nat.mul(M1, Pv))), low), Nat.add(Nat.add(Nat.mul(A, PW1), Nat.mul(b, PW)), gam), hq,
        R.NatN.eq(env, R.Ad(R.Ad(R.Ml(R.V(0n), R.V(8n)), R.Ml(R.V(1n), R.Ml(R.V(4n), R.V(3n)))), R.V(6n)), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(8n)), R.Ml(R.V(1n), R.V(7n))), R.Ad(R.Ml(R.V(1n), R.Ml(R.V(5n), R.V(3n))), R.V(6n))), [R.Ng(R.V(1n)), R.Ml(R.V(1n), R.V(3n)), R.Ng(R.Ml(R.V(1n), R.V(3n))), R.Ml(R.V(1n), R.V(3n))], [R.Ad(R.V(7n), R.Ng(R.Ml(R.V(2n), R.V(3n)))), R.Ad(R.V(9n), R.Ng(R.Ad(R.V(2n), R.V(2n)))), R.Ad(R.V(9n), R.Ng(R.Ad(R.V(10n), R.V(4n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.V(10n), R.V(5n))))], {==}, (R.NatN.z(env, R.V(7n), R.Ml(R.V(2n), R.V(3n)), {==}, {==}, BP.Pow2.add(k2, v)), (R.NatN.z(env, R.V(9n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, Y.Nat.double_add(Pk)), (R.NatN.z(env, R.V(9n), R.Ad(R.V(10n), R.V(4n)), {==}, {==}, Pw.pos(1n+k2)), (R.NatN.z(env, R.V(2n), R.Ad(R.V(10n), R.V(5n)), {==}, {==}, Pw.pos(k2)), Unit{})))), {==}, {==}))
      # gam < 2^w2: b X + low <= X + low < X + 2^v = 2^k2 2^v
      +hx : {RD.Nat.lt(X, Nat.mul(b, X)) == False{} : Bool} = E.Le.trans(Nat.mul(b, X), Nat.mul(1n, X), X, E2.Le.mulr(b, 1n, X, hb), E.Le.eq(Nat.mul(1n, X), X, NL.Nat.add_zero_r(X)))
      +ePW : {Nat.add(X, Pv) == PW : Nat} = Equal.trans(Nat, Nat.add(X, Pv), Nat.mul(1n+Mk, Pv), PW, NL.Nat.add_comm(X, Pv),
        Equal.trans(Nat, Nat.mul(1n+Mk, Pv), Nat.mul(Pk, Pv), PW, Equal.cong(Nat, Nat, z => Nat.mul(z, Pv), 1n+Mk, Pk, Equal.sym(Nat, Pk, 1n+Mk, Pw.pos(k2))), Equal.sym(Nat, PW, Nat.mul(Pk, Pv), BP.Pow2.add(k2, v))))
      +hg : {RD.Nat.lt(gam, PW) == True{} : Bool} = E2.Le.lt_trans(gam, Nat.add(X, low), PW, E2.Le.addr(Nat.mul(b, X), X, low, hx),
        Equal.trans(Bool, RD.Nat.lt(Nat.add(X, low), PW), RD.Nat.lt(Nat.add(X, low), Nat.add(X, Pv)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.add(X, low), z), PW, Nat.add(X, Pv), Equal.sym(Nat, Nat.add(X, Pv), PW, ePW)),
          Equal.trans(Bool, RD.Nat.lt(Nat.add(X, low), Nat.add(X, Pv)), RD.Nat.lt(low, Pv), True{}, BP.Lt.shift(X, low, Pv), hl)))
      +bit : {Bitq(q, w2) == b : Nat} = Equal.trans(Nat, Bitq(q, w2), Bitq(Nat.add(Nat.add(Nat.mul(A, PW1), Nat.mul(b, PW)), gam), w2), b,
        Equal.cong(Nat, Nat, z => Bitq(z, w2), q, Nat.add(Nat.add(Nat.mul(A, PW1), Nat.mul(b, PW)), gam), eq), Bit.of(A, b, gam, w2, hb, hg))
      +A2 = Nat.add(Nat.mul(A, 2n), b)
      +hq2 : {q == Nat.add(Nat.add(Nat.mul(A2, PW), Nat.mul(b, X)), low) : Nat} = Equal.trans(Nat, q, Nat.add(Nat.add(Nat.mul(A, PW1), Nat.mul(b, PW)), gam), Nat.add(Nat.add(Nat.mul(A2, PW), Nat.mul(b, X)), low), eq,
        R.NatN.eq2(env, R.Ad(R.Ad(R.Ml(R.V(0n), R.V(8n)), R.Ml(R.V(1n), R.V(7n))), R.Ad(R.Ml(R.V(1n), R.Ml(R.V(5n), R.V(3n))), R.V(6n))), R.Ad(R.Ad(R.Ml(R.Ad(R.Ml(R.V(0n), R.Ad(R.V(10n), R.V(10n))), R.V(1n)), R.V(7n)), R.Ml(R.V(1n), R.Ml(R.V(5n), R.V(3n)))), R.V(6n)), [R.V(0n)], [R.Ad(R.V(8n), R.Ng(R.Ad(R.V(7n), R.V(7n))))], [R.Ad(R.Ml(R.V(7n), R.V(0n)), R.Ng(R.Ml(R.Ml(R.V(7n), R.V(0n)), R.V(10n)))), R.Ad(R.Ml(R.V(7n), R.V(0n)), R.Ng(R.Ml(R.Ml(R.V(7n), R.V(0n)), R.V(10n))))], {==}, (R.NatN.z(env, R.V(8n), R.Ad(R.V(7n), R.V(7n)), {==}, {==}, Y.Nat.double_add(PW)), Unit{}), (R.NatN.z(env, R.Ml(R.V(7n), R.V(0n)), R.Ml(R.Ml(R.V(7n), R.V(0n)), R.V(10n)), {==}, {==}, Equal.sym(Nat, Nat.mul(Nat.mul(PW, A), 1n), Nat.mul(PW, A), NL.Nat.mul_one_r(Nat.mul(PW, A)))), (R.NatN.z(env, R.Ml(R.V(7n), R.V(0n)), R.Ml(R.Ml(R.V(7n), R.V(0n)), R.V(10n)), {==}, {==}, Equal.sym(Nat, Nat.mul(Nat.mul(PW, A), 1n), Nat.mul(PW, A), NL.Nat.mul_one_r(Nat.mul(PW, A)))), Unit{})), {==}, {==}))
      +ih = Same.bits(k2, v, A2, b, low, q, hb, hl, hq2)
      Equal.trans(Bool, Bool.and(Nat.is_eq(Bitq(q, w2), b), Bits.ok(k2, q, w2, b)), Bool.and(Nat.is_eq(b, b), Bits.ok(k2, q, w2, b)), True{},
        Equal.cong(Nat, Bool, z => Bool.and(Nat.is_eq(z, b), Bits.ok(k2, q, w2, b)), Bitq(q, w2), b, bit),
        Equal.trans(Bool, Bool.and(Nat.is_eq(b, b), Bits.ok(k2, q, w2, b)), Bool.and(True{}, Bits.ok(k2, q, w2, b)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Bits.ok(k2, q, w2, b)), Nat.is_eq(b, b), True{}, Eq.refl(b)), ih))

# The decoder, step by step
# -------------------------
# Pz.dec unfolds to Dtop; each D* takes the values computed so far as
# parameters, so a proof rewrites them one at a time.

def Dfin(+h: Nat, +es: Nat, +rs: Nat, +neg: Bool, +b: Nat, +k: Nat, +fb: Nat, +ee: Nat, +fr: Nat) -> SB.Bd:
  +g = P.Nat.pw(es)
  +tb = Nat.add(Nat.mul(Bool.pick(Nat, Nat.is_eq(b, 1n), Nat.sub(Nat.add(k, rs), 1n), Nat.sub(rs, k)), g), ee)
  +m = SB.Bn.of(h, Nat.add(P.Nat.pw(fb), fr))
  +bias = Nat.mul(rs, g)
  Bool.pick(SB.Bd, Nat.is_lt(tb, Nat.add(bias, fb)), SB.Bd{neg, m, Nat.sub(Nat.add(bias, fb), tb)}, SB.Bd{neg, SB.Bn.shl(h, Nat.sub(tb, Nat.add(bias, fb)), m), 0n})

def Dlow(+h: Nat, +es: Nat, +rs: Nat, +neg: Bool, +b: Nat, +k: Nat, +ew: Nat, +fb: Nat, +low: Nat) -> SB.Bd:
  Dfin(h, es, rs, neg, b, k, fb, Nat.mul(Nat.div(low, P.Nat.pw(fb)), P.Nat.pw(Nat.sub(es, ew))), Nat.mod(low, P.Nat.pw(fb)))

def Dew(+h: Nat, +es: Nat, +rs: Nat, +neg: Bool, +q: Nat, +b: Nat, +k: Nat, +rem: Nat, +ew: Nat) -> SB.Bd:
  Dlow(h, es, rs, neg, b, k, ew, Nat.sub(rem, ew), Nat.mod(q, P.Nat.pw(rem)))

def Drem(+h: Nat, +es: Nat, +rs: Nat, +neg: Bool, +q: Nat, +b: Nat, +k: Nat, +rem: Nat) -> SB.Bd:
  Dew(h, es, rs, neg, q, b, k, rem, Bool.pick(Nat, Nat.is_lt(rem, es), rem, es))

def Drl(+h: Nat, +es: Nat, +rs: Nat, +neg: Bool, +q: Nat, +w: Nat, +b: Nat, +k: Nat, +rl: Nat) -> SB.Bd:
  Drem(h, es, rs, neg, q, b, k, Nat.sub(w, rl))

def Dk(+h: Nat, +es: Nat, +rs: Nat, +neg: Bool, +q: Nat, +w: Nat, +b: Nat, +k: Nat) -> SB.Bd:
  Drl(h, es, rs, neg, q, w, b, k, Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs))

def Dtop(+h: Nat, +n: Nat, +es: Nat, +rs: Nat, +neg: Bool, +q: Nat) -> SB.Bd:
  Dk(h, es, rs, neg, q, Nat.sub(n, 1n), Nat.mod(Nat.div(q, P.Nat.pw(Nat.sub(Nat.sub(n, 1n), 1n))), 2n),
    P.Pz.run(rs, q, Nat.sub(n, 1n), Nat.mod(Nat.div(q, P.Nat.pw(Nat.sub(Nat.sub(n, 1n), 1n))), 2n)))

def Dec.top(+h: Nat, +n: Nat, +es: Nat, +rs: Nat, +pt: Nat)
  -> {P.Pz.dec(h, n, es, rs, pt) == Dtop(h, n, es, rs, Bool.not(Nat.is_lt(pt, P.Nat.pw(Nat.sub(n, 1n)))), Bool.pick(Nat, Bool.not(Nat.is_lt(pt, P.Nat.pw(Nat.sub(n, 1n)))), Nat.sub(P.Nat.pw(n), pt), pt)) : SB.Bd}:
  {==}

def Sub.self(+a: Nat) -> {Nat.sub(a, a) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+a2):
      Sub.self(a2)

# x = ee 2^fb + fr, fr < 2^fb: x / 2^fb = ee, x mod 2^fb = fr
def Split.q(+ee: Nat, +fr: Nat, +fb: Nat, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(fb)) == True{} : Bool})
  -> {Nat.div(Nat.add(Nat.mul(ee, P.Nat.pw(fb)), fr), P.Nat.pw(fb)) == ee : Nat} & {Nat.mod(Nat.add(Nat.mul(ee, P.Nat.pw(fb)), fr), P.Nat.pw(fb)) == fr : Nat}:
  +pm = RD.Nat.monus(RD.Nat.pow2(fb), 1n)
  +ep : {P.Nat.pw(fb) == 1n+pm : Nat} = Equal.trans(Nat, P.Nat.pw(fb), RD.Nat.pow2(fb), 1n+pm, Pw.eq(fb), Pw.pos(fb))
  +hf : {RD.Nat.lt(pm, fr) == False{} : Bool} = E2.Le.of_lt1(fr, pm, Equal.trans(Bool, RD.Nat.lt(fr, 1n+pm), RD.Nat.lt(fr, RD.Nat.pow2(fb)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(fr, z), 1n+pm, RD.Nat.pow2(fb), Equal.sym(Nat, RD.Nat.pow2(fb), 1n+pm, Pw.pos(fb))), hfr))
  (Equal.trans(Nat, Nat.div(Nat.add(Nat.mul(ee, P.Nat.pw(fb)), fr), P.Nat.pw(fb)), Nat.div(Nat.add(Nat.mul(ee, 1n+pm), fr), 1n+pm), ee,
     Equal.cong(Nat, Nat, z => Nat.div(Nat.add(Nat.mul(ee, z), fr), z), P.Nat.pw(fb), 1n+pm, ep), Div.q(ee, fr, pm, hf)),
   Equal.trans(Nat, Nat.mod(Nat.add(Nat.mul(ee, P.Nat.pw(fb)), fr), P.Nat.pw(fb)), Nat.mod(Nat.add(Nat.mul(ee, 1n+pm), fr), 1n+pm), fr,
     Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(Nat.mul(ee, z), fr), z), P.Nat.pw(fb), 1n+pm, ep), Div.r(ee, fr, pm, hf)))

# a positive pattern whose fields are known decodes to Dfin of them
def Dec.core(+h: Nat, +es: Nat, +rs: Nat, +w: Nat, +q: Nat, +b: Nat, +k: Nat, +rl: Nat, +rem: Nat, +fb: Nat, +ee: Nat, +fr: Nat,
  +hq: {Nat.is_lt(q, P.Nat.pw(w)) == True{} : Bool},
  +hb: {Nat.mod(Nat.div(q, P.Nat.pw(Nat.sub(w, 1n))), 2n) == b : Nat},
  +hk: {P.Pz.run(rs, q, w, b) == k : Nat},
  +hrl: {Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs) == rl : Nat},
  +hrem: {Nat.sub(w, rl) == rem : Nat},
  +hew: {Nat.is_lt(rem, es) == False{} : Bool},
  +hfb: {Nat.sub(rem, es) == fb : Nat},
  +hlow: {Nat.mod(q, P.Nat.pw(rem)) == Nat.add(Nat.mul(ee, P.Nat.pw(fb)), fr) : Nat},
  +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(fb)) == True{} : Bool})
  -> {P.Pz.dec(h, 1n+w, es, rs, q) == Dfin(h, es, rs, False{}, b, k, fb, ee, fr) : SB.Bd}:
  +n : Nat = 1n+w
  +neg = Bool.not(Nat.is_lt(q, P.Nat.pw(Nat.sub(n, 1n))))
  +eneg : {neg == False{} : Bool} = Equal.trans(Bool, neg, Bool.not(Nat.is_lt(q, P.Nat.pw(w))), False{},
    Equal.cong(Nat, Bool, z => Bool.not(Nat.is_lt(q, P.Nat.pw(z))), Nat.sub(w, 0n), w, Sub.z(w)),
    Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_lt(q, P.Nat.pw(w)), True{}, hq))
  +s0 = Dec.top(h, n, es, rs, q)
  +low = Nat.add(Nat.mul(ee, P.Nat.pw(fb)), fr)
  +ediv : {Nat.div(low, P.Nat.pw(fb)) == ee : Nat} = Pair.fst({Nat.div(low, P.Nat.pw(fb)) == ee : Nat}, {Nat.mod(low, P.Nat.pw(fb)) == fr : Nat}, Split.q(ee, fr, fb, hfr))
  +emod : {Nat.mod(low, P.Nat.pw(fb)) == fr : Nat} = Pair.snd({Nat.div(low, P.Nat.pw(fb)) == ee : Nat}, {Nat.mod(low, P.Nat.pw(fb)) == fr : Nat}, Split.q(ee, fr, fb, hfr))
  +eee : {Nat.mul(Nat.div(low, P.Nat.pw(fb)), P.Nat.pw(Nat.sub(es, es))) == ee : Nat} = Equal.trans(Nat, Nat.mul(Nat.div(low, P.Nat.pw(fb)), P.Nat.pw(Nat.sub(es, es))), Nat.mul(ee, P.Nat.pw(0n)), ee,
    Equal.trans(Nat, Nat.mul(Nat.div(low, P.Nat.pw(fb)), P.Nat.pw(Nat.sub(es, es))), Nat.mul(ee, P.Nat.pw(Nat.sub(es, es))), Nat.mul(ee, P.Nat.pw(0n)),
      Equal.cong(Nat, Nat, z => Nat.mul(z, P.Nat.pw(Nat.sub(es, es))), Nat.div(low, P.Nat.pw(fb)), ee, ediv),
      Equal.cong(Nat, Nat, z => Nat.mul(ee, P.Nat.pw(z)), Nat.sub(es, es), 0n, Sub.self(es))),
    NL.Nat.mul_one_r(ee))
  # Dtop(neg, q) -> Dk(False, q, w, b, k) -> ... -> Dfin
  +s1 = Equal.cong(Bool, SB.Bd, z => Dtop(h, n, es, rs, z, Bool.pick(Nat, z, Nat.sub(P.Nat.pw(n), q), q)), neg, False{}, eneg)
  +bx = Nat.mod(Nat.div(q, P.Nat.pw(Nat.sub(Nat.sub(n, 1n), 1n))), 2n)
  +s2 = Equal.cong(Nat, SB.Bd, z => Dk(h, es, rs, False{}, q, z, Nat.mod(Nat.div(q, P.Nat.pw(Nat.sub(z, 1n))), 2n), P.Pz.run(rs, q, z, Nat.mod(Nat.div(q, P.Nat.pw(Nat.sub(z, 1n))), 2n))), Nat.sub(w, 0n), w, Sub.z(w))
  +s3 = Equal.cong(Nat, SB.Bd, z => Dk(h, es, rs, False{}, q, w, z, P.Pz.run(rs, q, w, z)), Nat.mod(Nat.div(q, P.Nat.pw(Nat.sub(w, 1n))), 2n), b, hb)
  +s4 = Equal.cong(Nat, SB.Bd, z => Dk(h, es, rs, False{}, q, w, b, z), P.Pz.run(rs, q, w, b), k, hk)
  +s5 = Equal.cong(Nat, SB.Bd, z => Drl(h, es, rs, False{}, q, w, b, k, z), Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs), rl, hrl)
  +s6 = Equal.cong(Nat, SB.Bd, z => Drem(h, es, rs, False{}, q, b, k, z), Nat.sub(w, rl), rem, hrem)
  +s7 = Equal.cong(Bool, SB.Bd, z => Dew(h, es, rs, False{}, q, b, k, rem, Bool.pick(Nat, z, rem, es)), Nat.is_lt(rem, es), False{}, hew)
  +s8 = Equal.cong(Nat, SB.Bd, z => Dlow(h, es, rs, False{}, b, k, es, z, Nat.mod(q, P.Nat.pw(rem))), Nat.sub(rem, es), fb, hfb)
  +s9 = Equal.cong(Nat, SB.Bd, z => Dlow(h, es, rs, False{}, b, k, es, fb, z), Nat.mod(q, P.Nat.pw(rem)), low, hlow)
  +s10 = Equal.cong(Nat, SB.Bd, z => Dfin(h, es, rs, False{}, b, k, fb, z, Nat.mod(low, P.Nat.pw(fb))), Nat.mul(Nat.div(low, P.Nat.pw(fb)), P.Nat.pw(Nat.sub(es, es))), ee, eee)
  +s11 = Equal.cong(Nat, SB.Bd, z => Dfin(h, es, rs, False{}, b, k, fb, ee, z), Nat.mod(low, P.Nat.pw(fb)), fr, emod)
  Equal.trans(SB.Bd, P.Pz.dec(h, n, es, rs, q), Dtop(h, n, es, rs, neg, Bool.pick(Nat, neg, Nat.sub(P.Nat.pw(n), q), q)), Dfin(h, es, rs, False{}, b, k, fb, ee, fr), s0,
  Equal.trans(SB.Bd, Dtop(h, n, es, rs, neg, Bool.pick(Nat, neg, Nat.sub(P.Nat.pw(n), q), q)), Dtop(h, n, es, rs, False{}, q), Dfin(h, es, rs, False{}, b, k, fb, ee, fr), s1,
  Equal.trans(SB.Bd, Dtop(h, n, es, rs, False{}, q), Dk(h, es, rs, False{}, q, w, Nat.mod(Nat.div(q, P.Nat.pw(Nat.sub(w, 1n))), 2n), P.Pz.run(rs, q, w, Nat.mod(Nat.div(q, P.Nat.pw(Nat.sub(w, 1n))), 2n))), Dfin(h, es, rs, False{}, b, k, fb, ee, fr), s2,
  Equal.trans(SB.Bd, Dk(h, es, rs, False{}, q, w, Nat.mod(Nat.div(q, P.Nat.pw(Nat.sub(w, 1n))), 2n), P.Pz.run(rs, q, w, Nat.mod(Nat.div(q, P.Nat.pw(Nat.sub(w, 1n))), 2n))), Dk(h, es, rs, False{}, q, w, b, P.Pz.run(rs, q, w, b)), Dfin(h, es, rs, False{}, b, k, fb, ee, fr), s3,
  Equal.trans(SB.Bd, Dk(h, es, rs, False{}, q, w, b, P.Pz.run(rs, q, w, b)), Dk(h, es, rs, False{}, q, w, b, k), Dfin(h, es, rs, False{}, b, k, fb, ee, fr), s4,
  Equal.trans(SB.Bd, Dk(h, es, rs, False{}, q, w, b, k), Drl(h, es, rs, False{}, q, w, b, k, rl), Dfin(h, es, rs, False{}, b, k, fb, ee, fr), s5,
  Equal.trans(SB.Bd, Drl(h, es, rs, False{}, q, w, b, k, rl), Drem(h, es, rs, False{}, q, b, k, rem), Dfin(h, es, rs, False{}, b, k, fb, ee, fr), s6,
  Equal.trans(SB.Bd, Drem(h, es, rs, False{}, q, b, k, rem), Dew(h, es, rs, False{}, q, b, k, rem, es), Dfin(h, es, rs, False{}, b, k, fb, ee, fr), s7,
  Equal.trans(SB.Bd, Dew(h, es, rs, False{}, q, b, k, rem, es), Dlow(h, es, rs, False{}, b, k, es, fb, Nat.mod(q, P.Nat.pw(rem))), Dfin(h, es, rs, False{}, b, k, fb, ee, fr), s8,
  Equal.trans(SB.Bd, Dlow(h, es, rs, False{}, b, k, es, fb, Nat.mod(q, P.Nat.pw(rem))), Dlow(h, es, rs, False{}, b, k, es, fb, low), Dfin(h, es, rs, False{}, b, k, fb, ee, fr), s9,
  Equal.trans(SB.Bd, Dlow(h, es, rs, False{}, b, k, es, fb, low), Dfin(h, es, rs, False{}, b, k, fb, ee, Nat.mod(low, P.Nat.pw(fb))), Dfin(h, es, rs, False{}, b, k, fb, ee, fr), s10, s11)))))))))))
