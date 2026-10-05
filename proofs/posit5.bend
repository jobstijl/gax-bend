# The b-posit encoder writes a value's pattern (src/posit.bend, Pz.enc):
# for every field triple, Pz.enc of any big dyadic worth Val is Pat
# (Enc.pat). With proofs/posit4.bend (Dec.val, Std.round) the bit
# patterns are proven both ways: decode(Pat) = Val, encode(Val) = Pat,
# and the spec's rounding is the standard's rounding of the bit string.

import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/round.bend as RD
import ./nat.bend as NL
import ./base.bend as B
import ./norm.bend as NP
import ./dyadic.bend as Y
import ./round.bend as R
import ./big.bend as BP
import ./eft.bend as E
import ./eft2.bend as E2
import ./posit2.bend as P2
import ./posit3.bend as P3
import ./posit4.bend as P4
import ../src/posit.bend as P
import ../src/big.bend as SB

# Bit length
# ----------

def Lt.ud(+a: Nat, +b: Nat) -> {RD.Nat.lt(Nat.double(a), Nat.double(b)) == RD.Nat.lt(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+b2:
      {==}
    case 1n+a2 0n:
      {==}
    case 1n+(+a2) 1n+(+b2):
      Lt.ud(a2, b2)

def Le.dbl(+a: Nat, +b: Nat, +h: {RD.Nat.lt(b, a) == False{} : Bool}) -> {RD.Nat.lt(Nat.double(b), Nat.double(a)) == False{} : Bool}:
  Equal.trans(Bool, RD.Nat.lt(Nat.double(b), Nat.double(a)), RD.Nat.lt(b, a), False{}, Lt.ud(b, a), h)

def Bit.le(+n: Nat) -> {RD.Nat.lt(1n, RD.Nat.bit(n)) == False{} : Bool}:
  E.Ge.of(1n, RD.Nat.bit(n), RD.Nat.monus(1n, RD.Nat.bit(n)), Equal.sym(Nat, Nat.add(RD.Nat.bit(n), RD.Nat.monus(1n, RD.Nat.bit(n))), 1n, R.Nat.bit01(n)))

def Blen.z(+h: Nat, f: Nat, +b: SB.Bn) -> {P.Bn.blen(h, f, b, False{}) == 0n : Nat}:
  match f:
    case 0n:
      {==}
    case 1n+f2:
      {==}

# half of v in [2^(l+1), 2^(l+2)) is in [2^l, 2^(l+1))
def Half.lo.go(+l: Nat, +v: Nat, +hlo: {RD.Nat.lt(v, RD.Nat.pow2(1n+l)) == False{} : Bool}, c: Bool, +ec: {RD.Nat.lt(D.Nat.half(v), RD.Nat.pow2(l)) == c : Bool})
  -> {RD.Nat.lt(D.Nat.half(v), RD.Nat.pow2(l)) == False{} : Bool}:
  match c:
    case False{}:
      ec
    case True{}:
      +H = D.Nat.half(v)
      +ev : {v == Nat.add(Nat.double(H), RD.Nat.bit(v)) : Nat} = R.Nat.split2(v)
      +l1 : {RD.Nat.lt(Nat.double(RD.Nat.pow2(l)), 2n+Nat.double(H)) == False{} : Bool} = Le.dbl(1n+H, RD.Nat.pow2(l), E2.Le.succ(H, RD.Nat.pow2(l), ec))
      +l2 : {RD.Nat.lt(1n+Nat.double(H), v) == False{} : Bool} = E.Le.trans(v, Nat.add(Nat.double(H), 1n), 1n+Nat.double(H),
        E.Le.trans(v, Nat.add(Nat.double(H), RD.Nat.bit(v)), Nat.add(Nat.double(H), 1n), E.Le.eq(v, Nat.add(Nat.double(H), RD.Nat.bit(v)), ev), E2.Le.addl(Nat.double(H), RD.Nat.bit(v), 1n, Bit.le(v))),
        E.Le.eq(Nat.add(Nat.double(H), 1n), 1n+Nat.double(H), Equal.trans(Nat, Nat.add(Nat.double(H), 1n), Nat.add(1n, Nat.double(H)), 1n+Nat.double(H), NL.Nat.add_comm(Nat.double(H), 1n), {==})))
      +bad : {RD.Nat.lt(1n+Nat.double(H), 2n+Nat.double(H)) == False{} : Bool} = E.Le.trans(2n+Nat.double(H), Nat.double(RD.Nat.pow2(l)), 1n+Nat.double(H), l1, E.Le.trans(Nat.double(RD.Nat.pow2(l)), v, 1n+Nat.double(H), hlo, l2))
      B.Bool.tf({RD.Nat.lt(D.Nat.half(v), RD.Nat.pow2(l)) == False{} : Bool}, Equal.trans(Bool, True{}, RD.Nat.lt(1n+Nat.double(H), 2n+Nat.double(H)), False{}, Equal.sym(Bool, RD.Nat.lt(1n+Nat.double(H), 2n+Nat.double(H)), True{}, E2.Lt.succ(1n+Nat.double(H))), bad))

def Half.hi(+l: Nat, +v: Nat, +hhi: {RD.Nat.lt(v, RD.Nat.pow2(2n+l)) == True{} : Bool}) -> {RD.Nat.lt(D.Nat.half(v), RD.Nat.pow2(1n+l)) == True{} : Bool}:
  +H = D.Nat.half(v)
  +ev : {v == Nat.add(Nat.double(H), RD.Nat.bit(v)) : Nat} = R.Nat.split2(v)
  +l1 : {RD.Nat.lt(Nat.double(H), RD.Nat.pow2(2n+l)) == True{} : Bool} = E2.Le.lt_trans(Nat.double(H), v, RD.Nat.pow2(2n+l),
    E.Le.trans(Nat.double(H), Nat.add(Nat.double(H), RD.Nat.bit(v)), v, E.Le.add(Nat.double(H), RD.Nat.bit(v)), E.Le.eq(Nat.add(Nat.double(H), RD.Nat.bit(v)), v, Equal.sym(Nat, v, Nat.add(Nat.double(H), RD.Nat.bit(v)), ev))), hhi)
  Equal.trans(Bool, RD.Nat.lt(H, RD.Nat.pow2(1n+l)), RD.Nat.lt(Nat.double(H), Nat.double(RD.Nat.pow2(1n+l))), True{}, Equal.sym(Bool, RD.Nat.lt(Nat.double(H), Nat.double(RD.Nat.pow2(1n+l))), RD.Nat.lt(H, RD.Nat.pow2(1n+l)), Lt.ud(H, RD.Nat.pow2(1n+l))), l1)

# blen counts the bits: on 2^l <= val b < 2^(l + 1), with fuel enough, l + 1
def Blen(+h1: Nat, l: Nat, +f: Nat, +b: SB.Bn, +ob: {SB.Bn.ok(1n+h1, b) == True{} : Bool},
  +hlo: {RD.Nat.lt(SB.Bn.val(1n+h1, b), RD.Nat.pow2(l)) == False{} : Bool}, +hhi: {RD.Nat.lt(SB.Bn.val(1n+h1, b), RD.Nat.pow2(1n+l)) == True{} : Bool})
  -> {P.Bn.blen(1n+h1, Nat.add(1n+l, f), b, SB.Bn.lt(SB.BNil{}, b)) == 1n+l : Nat}:
  match l:
    case 0n:
      +h : Nat = 1n+h1
      +v = SB.Bn.val(h, b)
      +hb = SB.Bn.half(h, b)
      +enz : {SB.Bn.lt(SB.BNil{}, b) == True{} : Bool} = Equal.trans(Bool, SB.Bn.lt(SB.BNil{}, b), RD.Nat.lt(0n, v), True{}, BP.Cmp.lt(h, SB.BNil{}, b, {==}, ob), E2.Lt.le_trans(0n, 1n, v, {==}, hlo))
      +ev1 : {v == 1n : Nat} = E2.Le.anti(v, 1n, E2.Le.of_lt1(v, 1n, hhi), hlo)
      +eh : {SB.Bn.val(h, hb) == 0n : Nat} = Equal.trans(Nat, SB.Bn.val(h, hb), D.Nat.half(v), 0n, BP.Half.val(h, b), Equal.cong(Nat, Nat, z => D.Nat.half(z), v, 1n, ev1))
      +enz2 : {SB.Bn.lt(SB.BNil{}, hb) == False{} : Bool} = Equal.trans(Bool, SB.Bn.lt(SB.BNil{}, hb), RD.Nat.lt(0n, SB.Bn.val(h, hb)), False{}, BP.Cmp.lt(h, SB.BNil{}, hb, {==}, BP.Half.ok(h, b, ob)), Equal.cong(Nat, Bool, z => RD.Nat.lt(0n, z), SB.Bn.val(h, hb), 0n, eh))
      Equal.trans(Nat, P.Bn.blen(h, 1n+f, b, SB.Bn.lt(SB.BNil{}, b)), 1n+P.Bn.blen(h, f, hb, SB.Bn.lt(SB.BNil{}, hb)), 1n,
        Equal.cong(Bool, Nat, z => P.Bn.blen(h, 1n+f, b, z), SB.Bn.lt(SB.BNil{}, b), True{}, enz),
        Equal.cong(Nat, Nat, z => 1n+z, P.Bn.blen(h, f, hb, SB.Bn.lt(SB.BNil{}, hb)), 0n,
          Equal.trans(Nat, P.Bn.blen(h, f, hb, SB.Bn.lt(SB.BNil{}, hb)), P.Bn.blen(h, f, hb, False{}), 0n, Equal.cong(Bool, Nat, z => P.Bn.blen(h, f, hb, z), SB.Bn.lt(SB.BNil{}, hb), False{}, enz2), Blen.z(h, f, hb))))
    case 1n+(+l2):
      +h : Nat = 1n+h1
      +v = SB.Bn.val(h, b)
      +hb = SB.Bn.half(h, b)
      +enz : {SB.Bn.lt(SB.BNil{}, b) == True{} : Bool} = Equal.trans(Bool, SB.Bn.lt(SB.BNil{}, b), RD.Nat.lt(0n, v), True{}, BP.Cmp.lt(h, SB.BNil{}, b, {==}, ob),
        E2.Lt.le_trans(0n, 1n, v, {==}, E.Le.trans(1n, RD.Nat.pow2(1n+l2), v, E2.Le.one(1n+l2), hlo)))
      +ehv : {SB.Bn.val(h, hb) == D.Nat.half(v) : Nat} = BP.Half.val(h, b)
      +hlo2 : {RD.Nat.lt(SB.Bn.val(h, hb), RD.Nat.pow2(l2)) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(SB.Bn.val(h, hb), RD.Nat.pow2(l2)), RD.Nat.lt(D.Nat.half(v), RD.Nat.pow2(l2)), False{},
        Equal.cong(Nat, Bool, z => RD.Nat.lt(z, RD.Nat.pow2(l2)), SB.Bn.val(h, hb), D.Nat.half(v), ehv), Half.lo.go(l2, v, hlo, RD.Nat.lt(D.Nat.half(v), RD.Nat.pow2(l2)), {==}))
      +hhi2 : {RD.Nat.lt(SB.Bn.val(h, hb), RD.Nat.pow2(1n+l2)) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(SB.Bn.val(h, hb), RD.Nat.pow2(1n+l2)), RD.Nat.lt(D.Nat.half(v), RD.Nat.pow2(1n+l2)), True{},
        Equal.cong(Nat, Bool, z => RD.Nat.lt(z, RD.Nat.pow2(1n+l2)), SB.Bn.val(h, hb), D.Nat.half(v), ehv), Half.hi(l2, v, hhi))
      +ih : {P.Bn.blen(h, Nat.add(1n+l2, f), hb, SB.Bn.lt(SB.BNil{}, hb)) == 1n+l2 : Nat} = Blen(h1, l2, f, hb, BP.Half.ok(h, b, ob), hlo2, hhi2)
      Equal.trans(Nat, P.Bn.blen(h, 1n+Nat.add(1n+l2, f), b, SB.Bn.lt(SB.BNil{}, b)), 1n+P.Bn.blen(h, Nat.add(1n+l2, f), hb, SB.Bn.lt(SB.BNil{}, hb)), 1n+1n+l2,
        Equal.cong(Bool, Nat, z => P.Bn.blen(h, 1n+Nat.add(1n+l2, f), b, z), SB.Bn.lt(SB.BNil{}, b), True{}, enz),
        Equal.cong(Nat, Nat, z => 1n+z, P.Bn.blen(h, Nat.add(1n+l2, f), hb, SB.Bn.lt(SB.BNil{}, hb)), 1n+l2, ih))

# a right shift that drops only zeros: val m = X 2^k gives X
def Shr.val(+h1: Nat, k: Nat, +m: SB.Bn, +X: Nat, +hv: {SB.Bn.val(1n+h1, m) == Nat.mul(X, RD.Nat.pow2(k)) : Nat}) -> {SB.Bn.val(1n+h1, P.Bn.shr(1n+h1, k, m)) == X : Nat}:
  match k:
    case 0n:
      Equal.trans(Nat, SB.Bn.val(1n+h1, m), Nat.mul(X, 1n), X, hv, NL.Nat.mul_one_r(X))
    case 1n+(+j):
      +hm = SB.Bn.half(1n+h1, m)
      +ev : {SB.Bn.val(1n+h1, hm) == Nat.mul(X, RD.Nat.pow2(j)) : Nat} = Equal.trans(Nat, SB.Bn.val(1n+h1, hm), D.Nat.half(SB.Bn.val(1n+h1, m)), Nat.mul(X, RD.Nat.pow2(j)), BP.Half.val(1n+h1, m),
        Equal.trans(Nat, D.Nat.half(SB.Bn.val(1n+h1, m)), D.Nat.half(Nat.double(Nat.mul(X, RD.Nat.pow2(j)))), Nat.mul(X, RD.Nat.pow2(j)),
          Equal.cong(Nat, Nat, z => D.Nat.half(z), SB.Bn.val(1n+h1, m), Nat.double(Nat.mul(X, RD.Nat.pow2(j))), Equal.trans(Nat, SB.Bn.val(1n+h1, m), Nat.mul(X, Nat.double(RD.Nat.pow2(j))), Nat.double(Nat.mul(X, RD.Nat.pow2(j))), hv, R.Nat.mul_double(X, RD.Nat.pow2(j)))),
          Y.Nat.half_double(Nat.mul(X, RD.Nat.pow2(j)))))
      Shr.val(h1, j, hm, X, ev)

# The encoder, step by step
# -------------------------
# Pz.enc.go unfolds to E1; each E* takes the values computed so far as
# parameters, so a proof rewrites them one at a time. lm1 is l - 1.

def Efin(+n: Nat, +neg: Bool, +rl: Nat, +reg: Nat, +ee: Nat, +fb: Nat, +fr: Nat) -> Nat:
  +q = Nat.add(Nat.add(Nat.mul(reg, P.Nat.pw(Nat.sub(Nat.sub(n, 1n), rl))), Nat.mul(ee, P.Nat.pw(fb))), fr)
  Bool.pick(Nat, neg, Nat.sub(P.Nat.pw(n), q), q)

def E7(+h: Nat, +n: Nat, +neg: Bool, +rl: Nat, +reg: Nat, +ee: Nat, +fb: Nat, +mm: SB.Bn) -> Nat:
  Efin(n, neg, rl, reg, ee, fb, Nat.sub(SB.Bn.val(h, mm), P.Nat.pw(fb)))

def E6(+h: Nat, +n: Nat, +neg: Bool, +m: SB.Bn, +lm1: Nat, +rl: Nat, +reg: Nat, +ee: Nat, +fb: Nat) -> Nat:
  E7(h, n, neg, rl, reg, ee, fb, Bool.pick(SB.Bn, Nat.is_lt(fb, lm1), P.Bn.shr(h, Nat.sub(lm1, fb), m), SB.Bn.shl(h, Nat.sub(fb, lm1), m)))

def E5(+h: Nat, +n: Nat, +es: Nat, +neg: Bool, +m: SB.Bn, +lm1: Nat, +rl: Nat, +reg: Nat, +ee: Nat) -> Nat:
  E6(h, n, neg, m, lm1, rl, reg, ee, Nat.sub(Nat.sub(Nat.sub(n, 1n), rl), es))

def E4(+h: Nat, +n: Nat, +es: Nat, +rs: Nat, +neg: Bool, +m: SB.Bn, +lm1: Nat, +rb: Nat, +ee: Nat, +k: Nat) -> Nat:
  E5(h, n, es, neg, m, lm1, Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs), Bool.pick(Nat, Nat.is_lt(rb, rs), Bool.pick(Nat, Nat.is_lt(k, rs), 1n, 0n), Nat.mul(Nat.sub(P.Nat.pw(k), 1n), Bool.pick(Nat, Nat.is_lt(k, rs), 2n, 1n))), ee)

def E3(+h: Nat, +n: Nat, +es: Nat, +rs: Nat, +neg: Bool, +m: SB.Bn, +lm1: Nat, +rb: Nat, +ee: Nat) -> Nat:
  E4(h, n, es, rs, neg, m, lm1, rb, ee, Bool.pick(Nat, Nat.is_lt(rb, rs), Nat.sub(rs, rb), Nat.add(Nat.sub(rb, rs), 1n)))

def E2(+h: Nat, +n: Nat, +es: Nat, +rs: Nat, +neg: Bool, +m: SB.Bn, +lm1: Nat, +tb: Nat) -> Nat:
  E3(h, n, es, rs, neg, m, lm1, Nat.div(tb, P.Nat.pw(es)), Nat.mod(tb, P.Nat.pw(es)))

def E1(+h: Nat, +n: Nat, +es: Nat, +rs: Nat, +neg: Bool, +m: SB.Bn, +lm1: Nat, +e: Nat) -> Nat:
  E2(h, n, es, rs, neg, m, lm1, Nat.sub(Nat.add(lm1, Nat.mul(rs, P.Nat.pw(es))), e))

def Enc.top(+h: Nat, +n: Nat, +es: Nat, +rs: Nat, +neg: Bool, +m: SB.Bn, +l: Nat, +e: Nat)
  -> {P.Pz.enc.go(h, n, es, rs, neg, m, l, e) == E1(h, n, es, rs, neg, m, Nat.sub(l, 1n), e) : Nat}:
  {==}

# Facts for the encoder's steps
# -----------------------------

def Add.canl(+k: Nat, +a: Nat, +b: Nat, +e: {Nat.add(k, a) == Nat.add(k, b) : Nat}) -> {a == b : Nat}:
  +l1 : {RD.Nat.lt(b, a) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(b, a), RD.Nat.lt(Nat.add(k, b), Nat.add(k, a)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.add(k, b), Nat.add(k, a)), RD.Nat.lt(b, a), BP.Lt.shift(k, b, a)),
    Equal.trans(Bool, RD.Nat.lt(Nat.add(k, b), Nat.add(k, a)), RD.Nat.lt(Nat.add(k, b), Nat.add(k, b)), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.add(k, b), z), Nat.add(k, a), Nat.add(k, b), e), P4.Lt.irr(Nat.add(k, b))))
  +l2 : {RD.Nat.lt(a, b) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(a, b), RD.Nat.lt(Nat.add(k, a), Nat.add(k, b)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.add(k, a), Nat.add(k, b)), RD.Nat.lt(a, b), BP.Lt.shift(k, a, b)),
    Equal.trans(Bool, RD.Nat.lt(Nat.add(k, a), Nat.add(k, b)), RD.Nat.lt(Nat.add(k, a), Nat.add(k, a)), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.add(k, a), z), Nat.add(k, b), Nat.add(k, a), Equal.sym(Nat, Nat.add(k, a), Nat.add(k, b), e)), P4.Lt.irr(Nat.add(k, a))))
  E2.Le.anti(a, b, l1, l2)

def Mul.canr(+a: Nat, +b: Nat, +x: Nat, +hx: {RD.Nat.lt(0n, x) == True{} : Bool}, +e: {Nat.mul(a, x) == Nat.mul(b, x) : Nat}) -> {a == b : Nat}:
  +l1 : {RD.Nat.lt(b, a) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(b, a), RD.Nat.lt(Nat.mul(b, x), Nat.mul(a, x)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.mul(b, x), Nat.mul(a, x)), RD.Nat.lt(b, a), P3.Lt.scale(b, a, x, hx)),
    Equal.trans(Bool, RD.Nat.lt(Nat.mul(b, x), Nat.mul(a, x)), RD.Nat.lt(Nat.mul(b, x), Nat.mul(b, x)), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.mul(b, x), z), Nat.mul(a, x), Nat.mul(b, x), e), P4.Lt.irr(Nat.mul(b, x))))
  +l2 : {RD.Nat.lt(a, b) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(a, b), RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)), RD.Nat.lt(a, b), P3.Lt.scale(a, b, x, hx)),
    Equal.trans(Bool, RD.Nat.lt(Nat.mul(a, x), Nat.mul(b, x)), RD.Nat.lt(Nat.mul(a, x), Nat.mul(a, x)), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.mul(a, x), z), Nat.mul(b, x), Nat.mul(a, x), Equal.sym(Nat, Nat.mul(a, x), Nat.mul(b, x), e)), P4.Lt.irr(Nat.mul(a, x))))
  E2.Le.anti(a, b, l1, l2)

def Kc.le.go(+rs: Nat, +rb: Nat, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}, z: Bool, +ez: {RD.Nat.lt(rb, rs) == z : Bool})
  -> {RD.Nat.lt(rs, Bool.pick(Nat, z, RD.Nat.monus(rs, rb), 1n+RD.Nat.monus(rb, rs))) == False{} : Bool}:
  match z:
    case True{}:
      +c = RD.Nat.monus(rs, rb)
      +ers : {rs == Nat.add(rb, c) : Nat} = E.Le.wit(rb, rs, BP.Lt.asym(rb, rs, ez))
      Equal.trans(Bool, RD.Nat.lt(rs, c), RD.Nat.lt(Nat.add(c, rb), c), False{},
        Equal.cong(Nat, Bool, w => RD.Nat.lt(w, c), rs, Nat.add(c, rb), Equal.trans(Nat, rs, Nat.add(rb, c), Nat.add(c, rb), ers, NL.Nat.add_comm(rb, c))), BP.Lt.ge(c, rb))
    case False{}:
      +d = RD.Nat.monus(rb, rs)
      +erb : {rb == Nat.add(rs, d) : Nat} = E.Le.wit(rs, rb, ez)
      +hd : {RD.Nat.lt(d, rs) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(d, rs), RD.Nat.lt(Nat.add(rs, d), Nat.add(rs, rs)), True{}, Equal.sym(Bool, RD.Nat.lt(Nat.add(rs, d), Nat.add(rs, rs)), RD.Nat.lt(d, rs), BP.Lt.shift(rs, d, rs)),
        Equal.trans(Bool, RD.Nat.lt(Nat.add(rs, d), Nat.add(rs, rs)), RD.Nat.lt(rb, Nat.double(rs)), True{},
          Equal.trans(Bool, RD.Nat.lt(Nat.add(rs, d), Nat.add(rs, rs)), RD.Nat.lt(rb, Nat.add(rs, rs)), RD.Nat.lt(rb, Nat.double(rs)), Equal.cong(Nat, Bool, w => RD.Nat.lt(w, Nat.add(rs, rs)), Nat.add(rs, d), rb, Equal.sym(Nat, rb, Nat.add(rs, d), erb)),
            Equal.cong(Nat, Bool, w => RD.Nat.lt(rb, w), Nat.add(rs, rs), Nat.double(rs), Equal.sym(Nat, Nat.double(rs), Nat.add(rs, rs), Y.Nat.double_add(rs)))), hrb))
      E2.Le.succ(d, rs, hd)

# the regime run k is at most rs
def Kc.le(+rs: Nat, +rb: Nat, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}) -> {RD.Nat.lt(rs, P4.Kc(rs, rb)) == False{} : Bool}:
  Kc.le.go(rs, rb, hrb, RD.Nat.lt(rb, rs), {==})

def Rl.min.go(+rs: Nat, +rb: Nat, z: Bool, +ez: {RD.Nat.lt(rb, rs) == z : Bool})
  -> {Bool.pick(Nat, z, P.Pz.min(1n+RD.Nat.monus(rs, rb), rs), P.Pz.min(2n+RD.Nat.monus(rb, rs), rs)) == P.Pz.min(1n+Bool.pick(Nat, z, RD.Nat.monus(rs, rb), 1n+RD.Nat.monus(rb, rs)), rs) : Nat}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

# the regime length is min(k + 1, rs)
def Rl.min(+rs: Nat, +rb: Nat) -> {P.Pz.rl(rs, rb) == P.Pz.min(1n+P4.Kc(rs, rb), rs) : Nat}:
  Rl.min.go(rs, rb, RD.Nat.lt(rb, rs), {==})

def Rl.kc.go(+k: Nat, +rs: Nat, +hk: {RD.Nat.lt(rs, k) == False{} : Bool}, l: Bool, +el: {RD.Nat.lt(k, rs) == l : Bool}) -> {Bool.pick(Nat, l, 1n+k, rs) == P.Pz.min(1n+k, rs) : Nat}:
  match l:
    case True{}:
      Equal.sym(Nat, P.Pz.min(1n+k, rs), 1n+k, P4.Min.succ(k, rs, el))
    case False{}:
      +ek : {k == rs : Nat} = E2.Le.anti(k, rs, hk, el)
      Equal.sym(Nat, P.Pz.min(1n+k, rs), rs, Equal.trans(Nat, P.Pz.min(1n+k, rs), P.Pz.min(1n+rs, rs), rs, Equal.cong(Nat, Nat, w => P.Pz.min(1n+w, rs), k, rs, ek), P4.Min.top(rs)))

# the encoder's regime length is the spec's
def Rl.kc(+rs: Nat, +rb: Nat, +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}) -> {Bool.pick(Nat, Nat.is_lt(P4.Kc(rs, rb), rs), 1n+P4.Kc(rs, rb), rs) == P.Pz.rl(rs, rb) : Nat}:
  +k = P4.Kc(rs, rb)
  Equal.trans(Nat, Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs), Bool.pick(Nat, RD.Nat.lt(k, rs), 1n+k, rs), P.Pz.rl(rs, rb),
    Equal.cong(Bool, Nat, w => Bool.pick(Nat, w, 1n+k, rs), Nat.is_lt(k, rs), RD.Nat.lt(k, rs), P2.Lt.eq(k, rs)),
    Equal.trans(Nat, Bool.pick(Nat, RD.Nat.lt(k, rs), 1n+k, rs), P.Pz.min(1n+k, rs), P.Pz.rl(rs, rb), Rl.kc.go(k, rs, Kc.le(rs, rb, hrb), RD.Nat.lt(k, rs), {==}),
      Equal.sym(Nat, P.Pz.rl(rs, rb), P.Pz.min(1n+k, rs), Rl.min(rs, rb))))

# the significand at fb + 1 bits: val m 2^j = a 2^T and fb + T = L + j,
# shifted by L - fb either way, is a
def Mm.go(+h1: Nat, +m: SB.Bn, +L: Nat, +j: Nat, +fb: Nat, +T: Nat, +a: Nat,
  +hV: {Nat.mul(SB.Bn.val(1n+h1, m), RD.Nat.pow2(j)) == Nat.mul(a, RD.Nat.pow2(T)) : Nat}, +hL: {Nat.add(fb, T) == Nat.add(L, j) : Nat}, l: Bool, +el: {RD.Nat.lt(fb, L) == l : Bool})
  -> {SB.Bn.val(1n+h1, Bool.pick(SB.Bn, l, P.Bn.shr(1n+h1, Nat.sub(L, fb), m), SB.Bn.shl(1n+h1, Nat.sub(fb, L), m))) == a : Nat}:
  match l:
    case True{}:
      +V = SB.Bn.val(1n+h1, m)
      +c = RD.Nat.monus(L, fb)
      +eL : {L == Nat.add(fb, c) : Nat} = E.Le.wit(fb, L, E2.Lt.to_le(fb, L, el))
      +eT : {T == Nat.add(c, j) : Nat} = Add.canl(fb, T, Nat.add(c, j), Equal.trans(Nat, Nat.add(fb, T), Nat.add(L, j), Nat.add(fb, Nat.add(c, j)), hL,
        Equal.trans(Nat, Nat.add(L, j), Nat.add(Nat.add(fb, c), j), Nat.add(fb, Nat.add(c, j)), Equal.cong(Nat, Nat, z => Nat.add(z, j), L, Nat.add(fb, c), eL), NL.Nat.add_assoc(fb, c, j))))
      +e2 : {Nat.mul(V, RD.Nat.pow2(j)) == Nat.mul(Nat.mul(a, RD.Nat.pow2(c)), RD.Nat.pow2(j)) : Nat} = Equal.trans(Nat, Nat.mul(V, RD.Nat.pow2(j)), Nat.mul(a, RD.Nat.pow2(T)), Nat.mul(Nat.mul(a, RD.Nat.pow2(c)), RD.Nat.pow2(j)), hV,
        Equal.trans(Nat, Nat.mul(a, RD.Nat.pow2(T)), Nat.mul(a, RD.Nat.pow2(Nat.add(c, j))), Nat.mul(Nat.mul(a, RD.Nat.pow2(c)), RD.Nat.pow2(j)), Equal.cong(Nat, Nat, z => Nat.mul(a, RD.Nat.pow2(z)), T, Nat.add(c, j), eT),
          E.Sh.mul(a, j, c, Nat.add(c, j), NL.Nat.add_comm(c, j))))
      +ev : {V == Nat.mul(a, RD.Nat.pow2(c)) : Nat} = Mul.canr(V, Nat.mul(a, RD.Nat.pow2(c)), RD.Nat.pow2(j), BP.Pow2.pos(j), e2)
      Shr.val(h1, Nat.sub(L, fb), m, a, Equal.trans(Nat, V, Nat.mul(a, RD.Nat.pow2(c)), Nat.mul(a, RD.Nat.pow2(Nat.sub(L, fb))), ev, Equal.cong(Nat, Nat, z => Nat.mul(a, RD.Nat.pow2(z)), c, Nat.sub(L, fb), Equal.sym(Nat, Nat.sub(L, fb), c, P2.Sub.eq(L, fb)))))
    case False{}:
      +V = SB.Bn.val(1n+h1, m)
      +c = RD.Nat.monus(fb, L)
      +efb : {fb == Nat.add(L, c) : Nat} = E.Le.wit(L, fb, el)
      +ej : {Nat.add(c, T) == j : Nat} = Add.canl(L, Nat.add(c, T), j, Equal.trans(Nat, Nat.add(L, Nat.add(c, T)), Nat.add(fb, T), Nat.add(L, j),
        Equal.trans(Nat, Nat.add(L, Nat.add(c, T)), Nat.add(Nat.add(L, c), T), Nat.add(fb, T), Equal.sym(Nat, Nat.add(Nat.add(L, c), T), Nat.add(L, Nat.add(c, T)), NL.Nat.add_assoc(L, c, T)), Equal.cong(Nat, Nat, z => Nat.add(z, T), Nat.add(L, c), fb, Equal.sym(Nat, fb, Nat.add(L, c), efb))), hL))
      +e2 : {Nat.mul(Nat.mul(V, RD.Nat.pow2(c)), RD.Nat.pow2(T)) == Nat.mul(a, RD.Nat.pow2(T)) : Nat} = Equal.trans(Nat, Nat.mul(Nat.mul(V, RD.Nat.pow2(c)), RD.Nat.pow2(T)), Nat.mul(V, RD.Nat.pow2(j)), Nat.mul(a, RD.Nat.pow2(T)),
        Equal.trans(Nat, Nat.mul(Nat.mul(V, RD.Nat.pow2(c)), RD.Nat.pow2(T)), Nat.mul(V, RD.Nat.pow2(Nat.add(c, T))), Nat.mul(V, RD.Nat.pow2(j)),
          Equal.sym(Nat, Nat.mul(V, RD.Nat.pow2(Nat.add(c, T))), Nat.mul(Nat.mul(V, RD.Nat.pow2(c)), RD.Nat.pow2(T)), E.Sh.mul(V, T, c, Nat.add(c, T), NL.Nat.add_comm(c, T))),
          Equal.cong(Nat, Nat, z => Nat.mul(V, RD.Nat.pow2(z)), Nat.add(c, T), j, ej)), hV)
      +ev : {Nat.mul(V, RD.Nat.pow2(c)) == a : Nat} = Mul.canr(Nat.mul(V, RD.Nat.pow2(c)), a, RD.Nat.pow2(T), BP.Pow2.pos(T), e2)
      Equal.trans(Nat, SB.Bn.val(1n+h1, SB.Bn.shl(1n+h1, Nat.sub(fb, L), m)), Nat.mul(V, RD.Nat.pow2(Nat.sub(fb, L))), a, BP.Shl.val(h1, Nat.sub(fb, L), m),
        Equal.trans(Nat, Nat.mul(V, RD.Nat.pow2(Nat.sub(fb, L))), Nat.mul(V, RD.Nat.pow2(c)), a, Equal.cong(Nat, Nat, z => Nat.mul(V, RD.Nat.pow2(z)), Nat.sub(fb, L), c, P2.Sub.eq(fb, L)), ev))

# the encoder on a positive m / 2^e with val m 2^j = a 2^T, e + j = bias +
# fb and fb + T = L + j (L + 1 is m's bit length) writes Pat
def Enc.core(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +m: SB.Bn, +L: Nat, +e: Nat, +j: Nat,
  +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}, +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool},
  +hV: {Nat.mul(SB.Bn.val(1n+h1, m), RD.Nat.pow2(j)) == Nat.mul(P3.Sig(p01, rs, rb, fr), RD.Nat.pow2(Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee))) : Nat},
  +hB: {Nat.add(e, j) == Nat.add(Nat.mul(rs, RD.Nat.pow2(es)), P3.Fb(p01, rs, rb)) : Nat},
  +hL: {Nat.add(P3.Fb(p01, rs, rb), Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee)) == Nat.add(L, j) : Nat})
  -> {E1(1n+h1, 1n+P4.W(p01, es, rs), es, rs, False{}, m, L, e) == P4.Pat(p01, es, rs, rb, ee, fr) : Nat}:
  +h : Nat = 1n+h1
  +W = P4.W(p01, es, rs)
  +n : Nat = 1n+W
  +G = RD.Nat.pow2(es)
  +g = P.Nat.pw(es)
  +bias = Nat.mul(rs, G)
  +fb = P3.Fb(p01, rs, rb)
  +Pf = RD.Nat.pow2(fb)
  +a = P3.Sig(p01, rs, rb, fr)
  +T = Nat.add(Nat.mul(rb, G), ee)
  +k = P4.Kc(rs, rb)
  +rl = P.Pz.rl(rs, rb)
  +R0 = P4.Rg(rs, rb)
  +eg : {g == G : Nat} = P2.Pw.eq(es)
  # the scale
  +env : List<&2, Nat> = [L, bias, T, e, j, fb]
  +e1 : {Nat.add(L, bias) == Nat.add(e, T) : Nat} = R.NatN.eq2(env, R.Ad(R.V(0n), R.V(1n)), R.Ad(R.V(3n), R.V(2n)), [], [], [R.Ad(R.Ad(R.V(1n), R.V(5n)), R.Ng(R.Ad(R.V(3n), R.V(4n)))), R.Ad(R.Ad(R.V(0n), R.V(4n)), R.Ng(R.Ad(R.V(5n), R.V(2n))))], {==}, Unit{},
    (R.NatN.z(env, R.Ad(R.V(1n), R.V(5n)), R.Ad(R.V(3n), R.V(4n)), {==}, {==}, Equal.sym(Nat, Nat.add(e, j), Nat.add(bias, fb), hB)), (R.NatN.z(env, R.Ad(R.V(0n), R.V(4n)), R.Ad(R.V(5n), R.V(2n)), {==}, {==}, Equal.sym(Nat, Nat.add(fb, T), Nat.add(L, j), hL)), Unit{})), {==}, {==})
  +etb : {Nat.sub(Nat.add(L, Nat.mul(rs, g)), e) == T : Nat} = Equal.trans(Nat, Nat.sub(Nat.add(L, Nat.mul(rs, g)), e), Nat.sub(Nat.add(e, T), e), T,
    Equal.cong(Nat, Nat, z => Nat.sub(z, e), Nat.add(L, Nat.mul(rs, g)), Nat.add(e, T), Equal.trans(Nat, Nat.add(L, Nat.mul(rs, g)), Nat.add(L, bias), Nat.add(e, T), Equal.cong(Nat, Nat, z => Nat.add(L, Nat.mul(rs, z)), g, G, eg), e1)),
    Equal.trans(Nat, Nat.sub(Nat.add(e, T), e), RD.Nat.monus(Nat.add(e, T), e), T, P2.Sub.eq(Nat.add(e, T), e), R.Nat.monus_add(e, T)))
  +s1 = Equal.cong(Nat, Nat, z => E2(h, n, es, rs, False{}, m, L, z), Nat.sub(Nat.add(L, Nat.mul(rs, g)), e), T, etb)
  # class and exponent
  +ediv : {Nat.div(T, g) == rb : Nat} = Equal.trans(Nat, Nat.div(T, g), Nat.div(T, G), rb, Equal.cong(Nat, Nat, z => Nat.div(T, z), g, G, eg), P3.Dv.q(rb, ee, es, hee))
  +emod : {Nat.mod(T, g) == ee : Nat} = Equal.trans(Nat, Nat.mod(T, g), Nat.mod(T, G), ee, Equal.cong(Nat, Nat, z => Nat.mod(T, z), g, G, eg), P3.Dv.r(rb, ee, es, hee))
  +s2a = Equal.cong(Nat, Nat, z => E3(h, n, es, rs, False{}, m, L, z, Nat.mod(T, g)), Nat.div(T, g), rb, ediv)
  +s2b = Equal.cong(Nat, Nat, z => E3(h, n, es, rs, False{}, m, L, rb, z), Nat.mod(T, g), ee, emod)
  # the regime run
  +ea1 : {Nat.add(RD.Nat.monus(rb, rs), 1n) == 1n+RD.Nat.monus(rb, rs) : Nat} = Equal.trans(Nat, Nat.add(RD.Nat.monus(rb, rs), 1n), 1n+Nat.add(RD.Nat.monus(rb, rs), 0n), 1n+RD.Nat.monus(rb, rs), NL.Nat.add_succ_r(RD.Nat.monus(rb, rs), 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(RD.Nat.monus(rb, rs), 0n), RD.Nat.monus(rb, rs), NL.Nat.add_zero_r(RD.Nat.monus(rb, rs))))
  +kx = Bool.pick(Nat, Nat.is_lt(rb, rs), Nat.sub(rs, rb), Nat.add(Nat.sub(rb, rs), 1n))
  +ek : {kx == k : Nat} = Equal.trans(Nat, kx, Bool.pick(Nat, RD.Nat.lt(rb, rs), Nat.sub(rs, rb), Nat.add(Nat.sub(rb, rs), 1n)), k,
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, Nat.sub(rs, rb), Nat.add(Nat.sub(rb, rs), 1n)), Nat.is_lt(rb, rs), RD.Nat.lt(rb, rs), P2.Lt.eq(rb, rs)),
    Equal.trans(Nat, Bool.pick(Nat, RD.Nat.lt(rb, rs), Nat.sub(rs, rb), Nat.add(Nat.sub(rb, rs), 1n)), Bool.pick(Nat, RD.Nat.lt(rb, rs), RD.Nat.monus(rs, rb), Nat.add(Nat.sub(rb, rs), 1n)), k,
      Equal.cong(Nat, Nat, z => Bool.pick(Nat, RD.Nat.lt(rb, rs), z, Nat.add(Nat.sub(rb, rs), 1n)), Nat.sub(rs, rb), RD.Nat.monus(rs, rb), P2.Sub.eq(rs, rb)),
      Equal.cong(Nat, Nat, z => Bool.pick(Nat, RD.Nat.lt(rb, rs), RD.Nat.monus(rs, rb), z), Nat.add(Nat.sub(rb, rs), 1n), 1n+RD.Nat.monus(rb, rs),
        Equal.trans(Nat, Nat.add(Nat.sub(rb, rs), 1n), Nat.add(RD.Nat.monus(rb, rs), 1n), 1n+RD.Nat.monus(rb, rs), Equal.cong(Nat, Nat, z => Nat.add(z, 1n), Nat.sub(rb, rs), RD.Nat.monus(rb, rs), P2.Sub.eq(rb, rs)), ea1))))
  +s3 = Equal.cong(Nat, Nat, z => E4(h, n, es, rs, False{}, m, L, rb, ee, z), kx, k, ek)
  # regime length and field
  +regx = Bool.pick(Nat, Nat.is_lt(rb, rs), Bool.pick(Nat, Nat.is_lt(k, rs), 1n, 0n), Nat.mul(Nat.sub(P.Nat.pw(k), 1n), Bool.pick(Nat, Nat.is_lt(k, rs), 2n, 1n)))
  +ereg : {regx == R0 : Nat} = Equal.trans(Nat, regx, P4.RgB(Nat.is_lt(rb, rs), Nat.is_lt(k, rs), k), R0,
    Equal.cong(Nat, Nat, z => Bool.pick(Nat, Nat.is_lt(rb, rs), Bool.pick(Nat, Nat.is_lt(k, rs), 1n, 0n), Nat.mul(z, Bool.pick(Nat, Nat.is_lt(k, rs), 2n, 1n))), Nat.sub(P.Nat.pw(k), 1n), RD.Nat.monus(RD.Nat.pow2(k), 1n),
      Equal.trans(Nat, Nat.sub(P.Nat.pw(k), 1n), RD.Nat.monus(P.Nat.pw(k), 1n), RD.Nat.monus(RD.Nat.pow2(k), 1n), P2.Sub.eq(P.Nat.pw(k), 1n), Equal.cong(Nat, Nat, z => RD.Nat.monus(z, 1n), P.Nat.pw(k), RD.Nat.pow2(k), P2.Pw.eq(k)))),
    Equal.trans(Nat, P4.RgB(Nat.is_lt(rb, rs), Nat.is_lt(k, rs), k), P4.RgB(RD.Nat.lt(rb, rs), Nat.is_lt(k, rs), k), R0,
      Equal.cong(Bool, Nat, z => P4.RgB(z, Nat.is_lt(k, rs), k), Nat.is_lt(rb, rs), RD.Nat.lt(rb, rs), P2.Lt.eq(rb, rs)),
      Equal.cong(Bool, Nat, z => P4.RgB(RD.Nat.lt(rb, rs), z, k), Nat.is_lt(k, rs), RD.Nat.lt(k, rs), P2.Lt.eq(k, rs))))
  +rlx = Bool.pick(Nat, Nat.is_lt(k, rs), 1n+k, rs)
  +erl : {rlx == rl : Nat} = Rl.kc(rs, rb, hrb)
  +s4a = Equal.cong(Nat, Nat, z => E5(h, n, es, False{}, m, L, z, regx, ee), rlx, rl, erl)
  +s4b = Equal.cong(Nat, Nat, z => E5(h, n, es, False{}, m, L, rl, z, ee), regx, R0, ereg)
  # fraction bits
  +ew : {W == Nat.add(rl, Nat.add(es, fb)) : Nat} = P4.W.split(p01, es, rs, rb)
  +ewr : {Nat.sub(Nat.sub(n, 1n), rl) == Nat.add(es, fb) : Nat} = Equal.trans(Nat, Nat.sub(Nat.sub(W, 0n), rl), Nat.sub(W, rl), Nat.add(es, fb), Equal.cong(Nat, Nat, z => Nat.sub(z, rl), Nat.sub(W, 0n), W, P2.Sub.z(W)),
    Equal.trans(Nat, Nat.sub(W, rl), RD.Nat.monus(W, rl), Nat.add(es, fb), P2.Sub.eq(W, rl), Equal.trans(Nat, RD.Nat.monus(W, rl), RD.Nat.monus(Nat.add(rl, Nat.add(es, fb)), rl), Nat.add(es, fb), Equal.cong(Nat, Nat, z => RD.Nat.monus(z, rl), W, Nat.add(rl, Nat.add(es, fb)), ew), R.Nat.monus_add(rl, Nat.add(es, fb)))))
  +efb : {Nat.sub(Nat.sub(Nat.sub(n, 1n), rl), es) == fb : Nat} = Equal.trans(Nat, Nat.sub(Nat.sub(Nat.sub(n, 1n), rl), es), Nat.sub(Nat.add(es, fb), es), fb, Equal.cong(Nat, Nat, z => Nat.sub(z, es), Nat.sub(Nat.sub(n, 1n), rl), Nat.add(es, fb), ewr),
    Equal.trans(Nat, Nat.sub(Nat.add(es, fb), es), RD.Nat.monus(Nat.add(es, fb), es), fb, P2.Sub.eq(Nat.add(es, fb), es), R.Nat.monus_add(es, fb)))
  +s5 = Equal.cong(Nat, Nat, z => E6(h, n, False{}, m, L, rl, R0, ee, z), Nat.sub(Nat.sub(Nat.sub(n, 1n), rl), es), fb, efb)
  # significand and fraction
  +mmx = Bool.pick(SB.Bn, Nat.is_lt(fb, L), P.Bn.shr(h, Nat.sub(L, fb), m), SB.Bn.shl(h, Nat.sub(fb, L), m))
  +emm : {SB.Bn.val(h, mmx) == a : Nat} = Equal.trans(Nat, SB.Bn.val(h, mmx), SB.Bn.val(h, Bool.pick(SB.Bn, RD.Nat.lt(fb, L), P.Bn.shr(h, Nat.sub(L, fb), m), SB.Bn.shl(h, Nat.sub(fb, L), m))), a,
    Equal.cong(Bool, Nat, z => SB.Bn.val(h, Bool.pick(SB.Bn, z, P.Bn.shr(h, Nat.sub(L, fb), m), SB.Bn.shl(h, Nat.sub(fb, L), m))), Nat.is_lt(fb, L), RD.Nat.lt(fb, L), P2.Lt.eq(fb, L)),
    Mm.go(h1, m, L, j, fb, T, a, hV, hL, RD.Nat.lt(fb, L), {==}))
  +efr : {Nat.sub(a, P.Nat.pw(fb)) == fr : Nat} = Equal.trans(Nat, Nat.sub(a, P.Nat.pw(fb)), RD.Nat.monus(a, P.Nat.pw(fb)), fr, P2.Sub.eq(a, P.Nat.pw(fb)),
    Equal.trans(Nat, RD.Nat.monus(a, P.Nat.pw(fb)), RD.Nat.monus(a, Pf), fr, Equal.cong(Nat, Nat, z => RD.Nat.monus(a, z), P.Nat.pw(fb), Pf, P2.Pw.eq(fb)), R.Nat.monus_add(Pf, fr)))
  +s6a = Equal.cong(Nat, Nat, z => Efin(n, False{}, rl, R0, ee, fb, Nat.sub(z, P.Nat.pw(fb))), SB.Bn.val(h, mmx), a, emm)
  +s6b = Equal.cong(Nat, Nat, z => Efin(n, False{}, rl, R0, ee, fb, z), Nat.sub(a, P.Nat.pw(fb)), fr, efr)
  # the pattern
  +s7a = Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.mul(R0, P.Nat.pw(z)), Nat.mul(ee, P.Nat.pw(fb))), fr), Nat.sub(Nat.sub(n, 1n), rl), Nat.add(es, fb), ewr)
  +s7b = Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.mul(R0, z), Nat.mul(ee, P.Nat.pw(fb))), fr), P.Nat.pw(Nat.add(es, fb)), RD.Nat.pow2(Nat.add(es, fb)), P2.Pw.eq(Nat.add(es, fb)))
  +s7c = Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.mul(R0, RD.Nat.pow2(Nat.add(es, fb))), Nat.mul(ee, z)), fr), P.Nat.pw(fb), Pf, P2.Pw.eq(fb))
  Equal.trans(Nat, E1(h, n, es, rs, False{}, m, L, e), E2(h, n, es, rs, False{}, m, L, T), P4.Pat(p01, es, rs, rb, ee, fr), s1,
  Equal.trans(Nat, E2(h, n, es, rs, False{}, m, L, T), E3(h, n, es, rs, False{}, m, L, rb, Nat.mod(T, g)), P4.Pat(p01, es, rs, rb, ee, fr), s2a,
  Equal.trans(Nat, E3(h, n, es, rs, False{}, m, L, rb, Nat.mod(T, g)), E3(h, n, es, rs, False{}, m, L, rb, ee), P4.Pat(p01, es, rs, rb, ee, fr), s2b,
  Equal.trans(Nat, E3(h, n, es, rs, False{}, m, L, rb, ee), E4(h, n, es, rs, False{}, m, L, rb, ee, k), P4.Pat(p01, es, rs, rb, ee, fr), s3,
  Equal.trans(Nat, E4(h, n, es, rs, False{}, m, L, rb, ee, k), E5(h, n, es, False{}, m, L, rl, regx, ee), P4.Pat(p01, es, rs, rb, ee, fr), s4a,
  Equal.trans(Nat, E5(h, n, es, False{}, m, L, rl, regx, ee), E5(h, n, es, False{}, m, L, rl, R0, ee), P4.Pat(p01, es, rs, rb, ee, fr), s4b,
  Equal.trans(Nat, E5(h, n, es, False{}, m, L, rl, R0, ee), E6(h, n, False{}, m, L, rl, R0, ee, fb), P4.Pat(p01, es, rs, rb, ee, fr), s5,
  Equal.trans(Nat, E6(h, n, False{}, m, L, rl, R0, ee, fb), Efin(n, False{}, rl, R0, ee, fb, Nat.sub(a, P.Nat.pw(fb))), P4.Pat(p01, es, rs, rb, ee, fr), s6a,
  Equal.trans(Nat, Efin(n, False{}, rl, R0, ee, fb, Nat.sub(a, P.Nat.pw(fb))), Efin(n, False{}, rl, R0, ee, fb, fr), P4.Pat(p01, es, rs, rb, ee, fr), s6b,
  Equal.trans(Nat, Efin(n, False{}, rl, R0, ee, fb, fr), Nat.add(Nat.add(Nat.mul(R0, P.Nat.pw(Nat.add(es, fb))), Nat.mul(ee, P.Nat.pw(fb))), fr), P4.Pat(p01, es, rs, rb, ee, fr), s7a,
  Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(R0, P.Nat.pw(Nat.add(es, fb))), Nat.mul(ee, P.Nat.pw(fb))), fr), Nat.add(Nat.add(Nat.mul(R0, RD.Nat.pow2(Nat.add(es, fb))), Nat.mul(ee, P.Nat.pw(fb))), fr), P4.Pat(p01, es, rs, rb, ee, fr), s7b, s7c)))))))))))

# From the value
# --------------

def Sig.pos(+p01: Nat, +rs: Nat, +rb: Nat, +fr: Nat) -> {RD.Nat.lt(0n, P3.Sig(p01, rs, rb, fr)) == True{} : Bool}:
  +fb = P3.Fb(p01, rs, rb)
  E2.Lt.le_trans(0n, 1n, P3.Sig(p01, rs, rb, fr), {==}, E.Le.trans(1n, RD.Nat.pow2(fb), P3.Sig(p01, rs, rb, fr), E2.Le.one(fb), E.Le.add(RD.Nat.pow2(fb), fr)))

# a negative normal form cannot be worth a positive value
def Neg.c(+V: Nat, +aT: Nat, +jj: Nat, +Mx: I.Int, +e1: {I.IPos{aT} == D.Int.sh(jj, Mx) : I.Int}, +e2: {Mx == I.Int.neg(I.IPos{V}) : I.Int}, +haT: {RD.Nat.lt(0n, aT) == True{} : Bool}) -> Empty:
  match V:
    case 0n:
      +ez : {aT == 0n : Nat} = Equal.cong(I.Int, Nat, z => RD.Int.mag(z), I.IPos{aT}, I.IPos{0n},
        Equal.trans(I.Int, I.IPos{aT}, D.Int.sh(jj, Mx), I.IPos{0n}, e1, Equal.trans(I.Int, D.Int.sh(jj, Mx), D.Int.sh(jj, I.IPos{0n}), I.IPos{0n}, Equal.cong(I.Int, I.Int, z => D.Int.sh(jj, z), Mx, I.IPos{0n}, e2), Y.Int.sh_zero(jj))))
      B.Bool.tf.empty(Equal.trans(Bool, True{}, RD.Nat.lt(0n, aT), False{}, Equal.sym(Bool, RD.Nat.lt(0n, aT), True{}, haT), Equal.cong(Nat, Bool, z => RD.Nat.lt(0n, z), aT, 0n, ez)))
    case 1n+(+v):
      B.Bool.tf.empty(Equal.trans(Bool, True{}, I.Int.pos(D.Int.sh(jj, Mx)), False{}, Equal.cong(I.Int, Bool, z => I.Int.pos(z), I.IPos{aT}, D.Int.sh(jj, Mx), e1),
        Equal.trans(Bool, I.Int.pos(D.Int.sh(jj, Mx)), I.Int.pos(Mx), False{}, Y.Int.pos_sh(jj, Mx), Equal.cong(I.Int, Bool, z => I.Int.pos(z), Mx, I.INeg{v}, e2))))

# 2^L <= V < 2^F gives L < F
def Fuel.ok(+L: Nat, +F: Nat, +V: Nat, +hlo: {RD.Nat.lt(V, RD.Nat.pow2(L)) == False{} : Bool}, +hv: {RD.Nat.lt(V, RD.Nat.pow2(F)) == True{} : Bool}, c: Bool, +ec: {RD.Nat.lt(L, F) == c : Bool})
  -> {RD.Nat.lt(L, F) == True{} : Bool}:
  match c:
    case True{}:
      ec
    case False{}:
      +bad : {RD.Nat.lt(V, RD.Nat.pow2(F)) == False{} : Bool} = E.Le.trans(RD.Nat.pow2(F), RD.Nat.pow2(L), V, E2.Pow2.mono(F, L, ec), hlo)
      B.Bool.tf({RD.Nat.lt(L, F) == True{} : Bool}, Equal.trans(Bool, True{}, RD.Nat.lt(V, RD.Nat.pow2(F)), False{}, Equal.sym(Bool, RD.Nat.lt(V, RD.Nat.pow2(F)), True{}, hv), bad))

# the bit length is L + 1, L = fb + T - j, and the fuel suffices
def Enc.pos2(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +m: SB.Bn, +e: Nat, +j: Nat,
  +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}, +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool},
  +om: {SB.Bn.ok(1n+h1, m) == True{} : Bool},
  +hV: {Nat.mul(SB.Bn.val(1n+h1, m), RD.Nat.pow2(j)) == Nat.mul(P3.Sig(p01, rs, rb, fr), RD.Nat.pow2(Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee))) : Nat},
  +hB: {Nat.add(e, j) == Nat.add(Nat.mul(rs, RD.Nat.pow2(es)), P3.Fb(p01, rs, rb)) : Nat},
  +hVp: {RD.Nat.lt(0n, SB.Bn.val(1n+h1, m)) == True{} : Bool},
  +up: {RD.Nat.lt(Nat.mul(SB.Bn.val(1n+h1, m), RD.Nat.pow2(j)), RD.Nat.pow2(1n+Nat.add(P3.Fb(p01, rs, rb), Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee)))) == True{} : Bool},
  +lo: {RD.Nat.lt(Nat.mul(SB.Bn.val(1n+h1, m), RD.Nat.pow2(j)), RD.Nat.pow2(Nat.add(P3.Fb(p01, rs, rb), Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee)))) == False{} : Bool},
  c: Bool, +ec: {RD.Nat.lt(Nat.add(P3.Fb(p01, rs, rb), Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee)), j) == c : Bool})
  -> {P.Pz.enc.n(1n+h1, 1n+P4.W(p01, es, rs), es, rs, SB.Bd{False{}, m, e}) == P4.Pat(p01, es, rs, rb, ee, fr) : Nat}:
  match c:
    case True{}:
      +V = SB.Bn.val(1n+h1, m)
      +S = Nat.add(P3.Fb(p01, rs, rb), Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee))
      +Pj = RD.Nat.pow2(j)
      +l1 : {RD.Nat.lt(Pj, RD.Nat.pow2(1n+S)) == False{} : Bool} = E2.Pow2.mono(1n+S, j, E2.Le.succ(S, j, ec))
      +l2 : {RD.Nat.lt(Nat.mul(V, Pj), Pj) == False{} : Bool} = E.Le.trans(Pj, Nat.mul(1n, Pj), Nat.mul(V, Pj), E.Le.eq(Pj, Nat.mul(1n, Pj), Equal.sym(Nat, Nat.mul(1n, Pj), Pj, P3.Mul.one_l(Pj))), E2.Le.mulr(1n, V, Pj, E2.Le.succ(0n, V, hVp)))
      +bad : {RD.Nat.lt(Nat.mul(V, Pj), RD.Nat.pow2(1n+S)) == False{} : Bool} = E.Le.trans(RD.Nat.pow2(1n+S), Pj, Nat.mul(V, Pj), l1, l2)
      B.Bool.tf({P.Pz.enc.n(1n+h1, 1n+P4.W(p01, es, rs), es, rs, SB.Bd{False{}, m, e}) == P4.Pat(p01, es, rs, rb, ee, fr) : Nat}, Equal.trans(Bool, True{}, RD.Nat.lt(Nat.mul(V, Pj), RD.Nat.pow2(1n+S)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.mul(V, Pj), RD.Nat.pow2(1n+S)), True{}, up), bad))
    case False{}:
      +h : Nat = 1n+h1
      +n : Nat = 1n+P4.W(p01, es, rs)
      +V = SB.Bn.val(h, m)
      +fb = P3.Fb(p01, rs, rb)
      +T = Nat.add(Nat.mul(rb, RD.Nat.pow2(es)), ee)
      +S = Nat.add(fb, T)
      +Pj = RD.Nat.pow2(j)
      +L = RD.Nat.monus(S, j)
      +eS : {S == Nat.add(j, L) : Nat} = E.Le.wit(j, S, ec)
      +eLj : {Nat.add(L, j) == S : Nat} = Equal.trans(Nat, Nat.add(L, j), Nat.add(j, L), S, NL.Nat.add_comm(L, j), Equal.sym(Nat, S, Nat.add(j, L), eS))
      +hL : {Nat.add(fb, T) == Nat.add(L, j) : Nat} = Equal.sym(Nat, Nat.add(L, j), S, eLj)
      +hlo : {RD.Nat.lt(V, RD.Nat.pow2(L)) == False{} : Bool} = E.Le.cancel(RD.Nat.pow2(L), V, Pj, BP.Pow2.pos(j),
        E.Le.trans(Nat.mul(RD.Nat.pow2(L), Pj), RD.Nat.pow2(S), Nat.mul(V, Pj), E.Le.eq(Nat.mul(RD.Nat.pow2(L), Pj), RD.Nat.pow2(S),
          Equal.trans(Nat, Nat.mul(RD.Nat.pow2(L), Pj), RD.Nat.pow2(Nat.add(L, j)), RD.Nat.pow2(S), Equal.sym(Nat, RD.Nat.pow2(Nat.add(L, j)), Nat.mul(RD.Nat.pow2(L), Pj), BP.Pow2.add(L, j)), Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), Nat.add(L, j), S, eLj))), lo))
      +hhi : {RD.Nat.lt(V, RD.Nat.pow2(1n+L)) == True{} : Bool} = E.Lt.cancel(V, RD.Nat.pow2(1n+L), Pj,
        Equal.trans(Bool, RD.Nat.lt(Nat.mul(V, Pj), Nat.mul(RD.Nat.pow2(1n+L), Pj)), RD.Nat.lt(Nat.mul(V, Pj), RD.Nat.pow2(1n+S)), True{},
          Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.mul(V, Pj), z), Nat.mul(RD.Nat.pow2(1n+L), Pj), RD.Nat.pow2(1n+S),
            Equal.trans(Nat, Nat.mul(RD.Nat.pow2(1n+L), Pj), RD.Nat.pow2(Nat.add(1n+L, j)), RD.Nat.pow2(1n+S), Equal.sym(Nat, RD.Nat.pow2(Nat.add(1n+L, j)), Nat.mul(RD.Nat.pow2(1n+L), Pj), BP.Pow2.add(1n+L, j)), Equal.cong(Nat, Nat, z => RD.Nat.pow2(1n+z), Nat.add(L, j), S, eLj))), up))
      +F = Nat.mul(h, SB.Bn.len(m))
      +hF : {RD.Nat.lt(L, F) == True{} : Bool} = Fuel.ok(L, F, V, hlo, BP.Val.lt(h1, m, om), RD.Nat.lt(L, F), {==})
      +eF : {F == Nat.add(1n+L, RD.Nat.monus(F, 1n+L)) : Nat} = E.Le.wit(1n+L, F, E2.Le.succ(L, F, hF))
      +eb : {P.Bn.blen(h, F, m, SB.Bn.lt(SB.BNil{}, m)) == 1n+L : Nat} = Equal.trans(Nat, P.Bn.blen(h, F, m, SB.Bn.lt(SB.BNil{}, m)), P.Bn.blen(h, Nat.add(1n+L, RD.Nat.monus(F, 1n+L)), m, SB.Bn.lt(SB.BNil{}, m)), 1n+L,
        Equal.cong(Nat, Nat, z => P.Bn.blen(h, z, m, SB.Bn.lt(SB.BNil{}, m)), F, Nat.add(1n+L, RD.Nat.monus(F, 1n+L)), eF), Blen(h1, L, RD.Nat.monus(F, 1n+L), m, om, hlo, hhi))
      +s1 = Equal.cong(Nat, Nat, z => Bool.pick(Nat, Nat.is_eq(z, 0n), 0n, P.Pz.enc.go(h, n, es, rs, False{}, m, z, e)), P.Bn.blen(h, F, m, SB.Bn.lt(SB.BNil{}, m)), 1n+L, eb)
      +s2 = Equal.cong(Nat, Nat, z => E1(h, n, es, rs, False{}, m, z, e), Nat.sub(L, 0n), L, P2.Sub.z(L))
      Equal.trans(Nat, P.Pz.enc.n(h, n, es, rs, SB.Bd{False{}, m, e}), P.Pz.enc.go(h, n, es, rs, False{}, m, 1n+L, e), P4.Pat(p01, es, rs, rb, ee, fr), s1,
        Equal.trans(Nat, P.Pz.enc.go(h, n, es, rs, False{}, m, 1n+L, e), E1(h, n, es, rs, False{}, m, L, e), P4.Pat(p01, es, rs, rb, ee, fr), s2,
          Enc.core(h1, p01, es, rs, rb, ee, fr, m, L, e, j, hrb, hee, hV, hB, hL)))

def Enc.pos(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +m: SB.Bn, +e: Nat,
  +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}, +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool},
  +om: {SB.Bn.ok(1n+h1, m) == True{} : Bool},
  +hd: {D.Dy.den(P4.Val(p01, es, rs, rb, ee, fr)) == e : Nat}, +hn: {D.Dy.num(P4.Val(p01, es, rs, rb, ee, fr)) == I.IPos{SB.Bn.val(1n+h1, m)} : I.Int})
  -> {P.Pz.enc.n(1n+h1, 1n+P4.W(p01, es, rs), es, rs, SB.Bd{False{}, m, e}) == P4.Pat(p01, es, rs, rb, ee, fr) : Nat}:
  +h : Nat = 1n+h1
  +n : Nat = 1n+P4.W(p01, es, rs)
  +G = RD.Nat.pow2(es)
  +fb = P3.Fb(p01, rs, rb)
  +Pf = RD.Nat.pow2(fb)
  +a = P3.Sig(p01, rs, rb, fr)
  +T = Nat.add(Nat.mul(rb, G), ee)
  +PT = RD.Nat.pow2(T)
  +aT = Nat.mul(a, PT)
  +B0 = Nat.add(Nat.mul(rs, G), fb)
  +X = P4.Val(p01, es, rs, rb, ee, fr)
  +V = SB.Bn.val(h, m)
  +j = RD.Nat.monus(B0, e)
  +eB : {B0 == Nat.add(e, j) : Nat} = Equal.trans(Nat, B0, Nat.add(D.Dy.den(X), RD.Nat.monus(B0, D.Dy.den(X))), Nat.add(e, j), P3.Rep.den(B0, aT), Equal.cong(Nat, Nat, z => Nat.add(z, RD.Nat.monus(B0, z)), D.Dy.den(X), e, hd))
  +hV : {Nat.mul(V, RD.Nat.pow2(j)) == aT : Nat} = Equal.sym(Nat, aT, Nat.mul(V, RD.Nat.pow2(j)), Equal.trans(Nat, aT, Nat.mul(RD.Int.mag(D.Dy.num(X)), RD.Nat.pow2(RD.Nat.monus(B0, D.Dy.den(X)))), Nat.mul(V, RD.Nat.pow2(j)), P3.Rep.num(B0, aT),
    Equal.trans(Nat, Nat.mul(RD.Int.mag(D.Dy.num(X)), RD.Nat.pow2(RD.Nat.monus(B0, D.Dy.den(X)))), Nat.mul(V, RD.Nat.pow2(RD.Nat.monus(B0, D.Dy.den(X)))), Nat.mul(V, RD.Nat.pow2(j)),
      Equal.cong(I.Int, Nat, z => Nat.mul(RD.Int.mag(z), RD.Nat.pow2(RD.Nat.monus(B0, D.Dy.den(X)))), D.Dy.num(X), I.IPos{V}, hn),
      Equal.cong(Nat, Nat, z => Nat.mul(V, RD.Nat.pow2(RD.Nat.monus(B0, z))), D.Dy.den(X), e, hd))))
  +haT : {RD.Nat.lt(0n, aT) == True{} : Bool} = E.Lt.mono(0n, a, PT, Sig.pos(p01, rs, rb, fr), BP.Pow2.pos(T))
  +hVp : {RD.Nat.lt(0n, V) == True{} : Bool} = P3.Pos.fac(V, RD.Nat.pow2(j), Equal.trans(Bool, RD.Nat.lt(0n, Nat.mul(V, RD.Nat.pow2(j))), RD.Nat.lt(0n, aT), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(0n, z), Nat.mul(V, RD.Nat.pow2(j)), aT, hV), haT))
  # 2^(fb + T) <= V 2^j < 2^(fb + T + 1)
  +S = Nat.add(fb, T)
  +ha : {RD.Nat.lt(a, RD.Nat.pow2(1n+fb)) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(a, Nat.double(Pf)), RD.Nat.lt(a, Nat.add(Pf, Pf)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(a, z), Nat.double(Pf), Nat.add(Pf, Pf), Y.Nat.double_add(Pf)),
    Equal.trans(Bool, RD.Nat.lt(Nat.add(Pf, fr), Nat.add(Pf, Pf)), RD.Nat.lt(fr, Pf), True{}, BP.Lt.shift(Pf, fr, Pf), hfr))
  +up : {RD.Nat.lt(Nat.mul(V, RD.Nat.pow2(j)), RD.Nat.pow2(1n+S)) == True{} : Bool} = Equal.trans(Bool, RD.Nat.lt(Nat.mul(V, RD.Nat.pow2(j)), RD.Nat.pow2(1n+S)), RD.Nat.lt(aT, Nat.mul(RD.Nat.pow2(1n+fb), PT)), True{},
    Equal.trans(Bool, RD.Nat.lt(Nat.mul(V, RD.Nat.pow2(j)), RD.Nat.pow2(1n+S)), RD.Nat.lt(aT, RD.Nat.pow2(1n+S)), RD.Nat.lt(aT, Nat.mul(RD.Nat.pow2(1n+fb), PT)),
      Equal.cong(Nat, Bool, z => RD.Nat.lt(z, RD.Nat.pow2(1n+S)), Nat.mul(V, RD.Nat.pow2(j)), aT, hV), Equal.cong(Nat, Bool, z => RD.Nat.lt(aT, z), RD.Nat.pow2(1n+S), Nat.mul(RD.Nat.pow2(1n+fb), PT), BP.Pow2.add(1n+fb, T))),
    E.Lt.mono(a, RD.Nat.pow2(1n+fb), PT, ha, BP.Pow2.pos(T)))
  +lo : {RD.Nat.lt(Nat.mul(V, RD.Nat.pow2(j)), RD.Nat.pow2(S)) == False{} : Bool} = E.Le.trans(RD.Nat.pow2(S), Nat.mul(Pf, PT), Nat.mul(V, RD.Nat.pow2(j)), E.Le.eq(RD.Nat.pow2(S), Nat.mul(Pf, PT), BP.Pow2.add(fb, T)),
    E.Le.trans(Nat.mul(Pf, PT), aT, Nat.mul(V, RD.Nat.pow2(j)), E2.Le.mulr(Pf, a, PT, E.Le.add(Pf, fr)), E.Le.eq(aT, Nat.mul(V, RD.Nat.pow2(j)), Equal.sym(Nat, Nat.mul(V, RD.Nat.pow2(j)), aT, hV))))
  Enc.pos2(h1, p01, es, rs, rb, ee, fr, m, e, j, hrb, hee, om, hV, Equal.sym(Nat, B0, Nat.add(e, j), eB), hVp, up, lo, RD.Nat.lt(S, j), {==})

def Enc.sg(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, +n: Bool, +m: SB.Bn, +e: Nat,
  +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}, +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool},
  +om: {SB.Bn.ok(1n+h1, m) == True{} : Bool},
  +hd: {D.Dy.den(P4.Val(p01, es, rs, rb, ee, fr)) == e : Nat}, +hn: {D.Dy.num(P4.Val(p01, es, rs, rb, ee, fr)) == SB.Bd.sg(n, SB.Bn.val(1n+h1, m)) : I.Int})
  -> {P.Pz.enc.n(1n+h1, 1n+P4.W(p01, es, rs), es, rs, SB.Bd{n, m, e}) == P4.Pat(p01, es, rs, rb, ee, fr) : Nat}:
  match n:
    case False{}:
      Enc.pos(h1, p01, es, rs, rb, ee, fr, m, e, hrb, hee, hfr, om, hd, hn)
    case True{}:
      +G = RD.Nat.pow2(es)
      +a = P3.Sig(p01, rs, rb, fr)
      +T = Nat.add(Nat.mul(rb, G), ee)
      +aT = Nat.mul(a, RD.Nat.pow2(T))
      +B0 = Nat.add(Nat.mul(rs, G), P3.Fb(p01, rs, rb))
      +X = P4.Val(p01, es, rs, rb, ee, fr)
      Empty.absurd({P.Pz.enc.n(1n+h1, 1n+P4.W(p01, es, rs), es, rs, SB.Bd{True{}, m, e}) == P4.Pat(p01, es, rs, rb, ee, fr) : Nat},
        Neg.c(SB.Bn.val(1n+h1, m), aT, RD.Nat.monus(B0, D.Dy.den(X)), D.Dy.num(X), E.Num.sh(B0, I.IPos{aT}), hn, E.Lt.mono(0n, a, RD.Nat.pow2(T), Sig.pos(p01, rs, rb, fr), BP.Pow2.pos(T))))

def Enc.n(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, r: SB.Bd, nf: BP.NF(1n+h1, r), +om: {SB.Bn.ok(1n+h1, SB.Bd.m(r)) == True{} : Bool},
  +hv: {SB.Bd.val(1n+h1, r) == P4.Val(p01, es, rs, rb, ee, fr) : D.Dy},
  +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}, +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool})
  -> {P.Pz.enc.n(1n+h1, 1n+P4.W(p01, es, rs), es, rs, r) == P4.Pat(p01, es, rs, rb, ee, fr) : Nat}:
  match r:
    case SB.Bd{+n, +m, +e}:
      match nf:
        case (ed0, en0):
          +X = P4.Val(p01, es, rs, rb, ee, fr)
          +r2 : SB.Bd = SB.Bd{n, m, e}
          +ed : {D.Dy.den(SB.Bd.val(1n+h1, r2)) == e : Nat} = ed0
          +en : {D.Dy.num(SB.Bd.val(1n+h1, r2)) == SB.Bd.sg(n, SB.Bn.val(1n+h1, m)) : I.Int} = en0
          +hd : {D.Dy.den(X) == e : Nat} = Equal.trans(Nat, D.Dy.den(X), D.Dy.den(SB.Bd.val(1n+h1, r2)), e, Equal.cong(D.Dy, Nat, z => D.Dy.den(z), X, SB.Bd.val(1n+h1, r2), Equal.sym(D.Dy, SB.Bd.val(1n+h1, r2), X, hv)), ed)
          +hn : {D.Dy.num(X) == SB.Bd.sg(n, SB.Bn.val(1n+h1, m)) : I.Int} = Equal.trans(I.Int, D.Dy.num(X), D.Dy.num(SB.Bd.val(1n+h1, r2)), SB.Bd.sg(n, SB.Bn.val(1n+h1, m)), Equal.cong(D.Dy, I.Int, z => D.Dy.num(z), X, SB.Bd.val(1n+h1, r2), Equal.sym(D.Dy, SB.Bd.val(1n+h1, r2), X, hv)), en)
          Enc.sg(h1, p01, es, rs, rb, ee, fr, n, m, e, hrb, hee, hfr, om, hd, hn)

# T2. The encoder writes every value's pattern: for every field triple and
# any big dyadic x worth Val (limbs below 2h, any spelling), Pz.enc x = Pat.
def Enc.pat(+h1: Nat, +p01: Nat, +es: Nat, +rs: Nat, +rb: Nat, +ee: Nat, +fr: Nat, x: SB.Bd, +ox: {SB.Bd.ok(1n+h1, x) == True{} : Bool},
  +hx: {SB.Bd.val(1n+h1, x) == P4.Val(p01, es, rs, rb, ee, fr) : D.Dy},
  +hrb: {RD.Nat.lt(rb, Nat.double(rs)) == True{} : Bool}, +hee: {RD.Nat.lt(ee, RD.Nat.pow2(es)) == True{} : Bool}, +hfr: {RD.Nat.lt(fr, RD.Nat.pow2(P3.Fb(p01, rs, rb))) == True{} : Bool})
  -> {P.Pz.enc(1n+h1, 1n+P4.W(p01, es, rs), es, rs, x) == P4.Pat(p01, es, rs, rb, ee, fr) : Nat}:
  match x:
    case SB.Bd{+neg, +m, +e}:
      +h : Nat = 1n+h1
      +ev = SB.Bn.even(m)
      +r = SB.Bd.norm.go(h, neg, e, m, ev)
      +hv : {SB.Bd.val(h, r) == P4.Val(p01, es, rs, rb, ee, fr) : D.Dy} = Equal.trans(D.Dy, SB.Bd.val(h, r), D.Dy.of(e, SB.Bd.sg(neg, SB.Bn.val(h, m))), P4.Val(p01, es, rs, rb, ee, fr), BP.Norm.val(h, neg, e, m, ev, {==}), hx)
      Enc.n(h1, p01, es, rs, rb, ee, fr, r, BP.Norm.nf(h, neg, e, m, ev, {==}), BP.Norm.ok(h, neg, e, m, ev, ox), hv, hrb, hee, hfr)
