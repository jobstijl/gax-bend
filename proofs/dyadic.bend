# Dyadics are an ordered commutative ring (src/dyadic.bend).
#
# Method: a pair (m, e) stands for m / 2^e, and (m1, e1) ~ (m2, e2) when
# m1 2^e2 = m2 2^e1, with 2^k written as k doublings (Int.sh). Dy.of
# normalises a pair: its result is equivalent to the pair (Of.val), equivalent
# pairs normalise alike (Of.eq), and a dyadic's own pair normalises back to it
# (Of.self). The ring laws then hold on pairs up to ~ and carry over. Int's
# laws come from proofs/int.bend.

import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ./nat.bend as NL
import ./int.bend as Z
import ./norm.bend as NP
import ./equiv.bend as EQ
import ../src/norm.bend as N

# Naturals: doubling and halving
# ------------------------------

def Nat.isz(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

# 0 is no successor
def Nat.zs(-k: Nat, e: {0n == 1n+k : Nat}) -> Empty:
  %e : Nat.isz(_)
  Unit{}

def Nat.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def Nat.pred2(-a: Nat, -b: Nat, e: {2n+a == 2n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, x => Nat.pred(Nat.pred(x)), 2n+a, 2n+b, e)

def Nat.double_add(+n: Nat) -> {Nat.double(n) == Nat.add(n, n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, 2n+Nat.double(p), 2n+Nat.add(p, p), 1n+Nat.add(p, 1n+p),
        Equal.cong(Nat, Nat, x => 2n+x, Nat.double(p), Nat.add(p, p), Nat.double_add(p)),
        Equal.cong(Nat, Nat, x => 1n+x, 1n+Nat.add(p, p), Nat.add(p, 1n+p), Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), NL.Nat.add_succ_r(p, p))))

def Nat.even_double(+n: Nat) -> {D.Nat.even(Nat.double(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Nat.even_double(p)

def Nat.odd_double(+n: Nat) -> {D.Nat.even(1n+Nat.double(n)) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Nat.odd_double(p)

def Nat.half_double(+n: Nat) -> {D.Nat.half(Nat.double(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, D.Nat.half(Nat.double(p)), p, Nat.half_double(p))

def Nat.half_odd(+n: Nat) -> {D.Nat.half(1n+Nat.double(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, D.Nat.half(1n+Nat.double(p)), p, Nat.half_odd(p))

# an even n is twice its half, an odd one one more
def Nat.even_split(+n: Nat) -> {D.Nat.even(n) == True{} : Bool} -> {n == Nat.double(D.Nat.half(n)) : Nat}:
  match n:
    case 0n:
      e => {==}
    case 1n+p:
      match p:
        case 0n:
          e => Empty.absurd({1n == 0n : Nat}, Z.Bool.ft(e))
        case 1n+q:
          e => Equal.cong(Nat, Nat, x => 2n+x, q, Nat.double(D.Nat.half(q)), Nat.even_split(q)(e))

def Nat.odd_split(+n: Nat) -> {D.Nat.even(n) == False{} : Bool} -> {n == 1n+Nat.double(D.Nat.half(n)) : Nat}:
  match n:
    case 0n:
      e => Empty.absurd({0n == 1n : Nat}, Z.Bool.ft(Equal.sym(Bool, True{}, False{}, e)))
    case 1n+p:
      match p:
        case 0n:
          e => {==}
        case 1n+q:
          e => Equal.cong(Nat, Nat, x => 2n+x, q, 1n+Nat.double(D.Nat.half(q)), Nat.odd_split(q)(e))

def Nat.double_inj(+a: Nat, +b: Nat) -> {Nat.double(a) == Nat.double(b) : Nat} -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      e => {==}
    case 0n 1n+q:
      e => Empty.absurd({0n == 1n+q : Nat}, Nat.zs(1n+Nat.double(q), e))
    case 1n+p 0n:
      e => Empty.absurd({1n+p == 0n : Nat}, Nat.zs(1n+Nat.double(p), Equal.sym(Nat, 2n+Nat.double(p), 0n, e)))
    case 1n+p 1n+q:
      e => Equal.cong(Nat, Nat, x => 1n+x, p, q, Nat.double_inj(p, q)(Nat.pred2(Nat.double(p), Nat.double(q), e)))

# Booleans
# --------

def Bool.not_t(+x: Bool) -> {Bool.not(x) == True{} : Bool} -> {x == False{} : Bool}:
  match x:
    case True{}:
      e => Empty.absurd({True{} == False{} : Bool}, Z.Bool.ft(e))
    case False{}:
      e => {==}

def Bool.not_not(+x: Bool) -> {Bool.not(Bool.not(x)) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def Nat.even_succ(+p: Nat) -> {D.Nat.even(1n+p) == Bool.not(D.Nat.even(p)) : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      Equal.trans(Bool, D.Nat.even(q), Bool.not(Bool.not(D.Nat.even(q))), Bool.not(D.Nat.even(1n+q)),
        Equal.sym(Bool, Bool.not(Bool.not(D.Nat.even(q))), D.Nat.even(q), Bool.not_not(D.Nat.even(q))),
        Equal.cong(Bool, Bool, x => Bool.not(x), Bool.not(D.Nat.even(q)), D.Nat.even(1n+q), Equal.sym(Bool, D.Nat.even(1n+q), Bool.not(D.Nat.even(q)), Nat.even_succ(q))))

# Integers: doubling
# ------------------

def Int.mag(a: I.Int) -> Nat:
  match a:
    case I.IPos{n}:
      n
    case I.INeg{n}:
      n

def Int.isneg(a: I.Int) -> Type:
  match a:
    case I.IPos{n}:
      Unit
    case I.INeg{n}:
      Empty

def Int.pn(-n: Nat, -m: Nat, e: {I.IPos{n} == I.INeg{m} : I.Int}) -> Empty:
  %e : Int.isneg(_)
  Unit{}

# (a + b) + (c + d) = (a + c) + (b + d)
def Int.add4(+a: I.Int, +b: I.Int, +c: I.Int, +d: I.Int) -> {I.Int.add(I.Int.add(a, b), I.Int.add(c, d)) == I.Int.add(I.Int.add(a, c), I.Int.add(b, d)) : I.Int}:
  +s1 = I.Int.add(a, I.Int.add(b, I.Int.add(c, d)))
  +s2 = I.Int.add(a, I.Int.add(I.Int.add(b, c), d))
  +s3 = I.Int.add(a, I.Int.add(I.Int.add(c, b), d))
  +s4 = I.Int.add(a, I.Int.add(c, I.Int.add(b, d)))
  Equal.trans(I.Int, I.Int.add(I.Int.add(a, b), I.Int.add(c, d)), s1, I.Int.add(I.Int.add(a, c), I.Int.add(b, d)), Z.Int.add_assoc(a, b, I.Int.add(c, d)),
    Equal.trans(I.Int, s1, s2, I.Int.add(I.Int.add(a, c), I.Int.add(b, d)),
      Equal.cong(I.Int, I.Int, w => I.Int.add(a, w), I.Int.add(b, I.Int.add(c, d)), I.Int.add(I.Int.add(b, c), d), Equal.sym(I.Int, I.Int.add(I.Int.add(b, c), d), I.Int.add(b, I.Int.add(c, d)), Z.Int.add_assoc(b, c, d))),
      Equal.trans(I.Int, s2, s3, I.Int.add(I.Int.add(a, c), I.Int.add(b, d)),
        Equal.cong(I.Int, I.Int, w => I.Int.add(a, I.Int.add(w, d)), I.Int.add(b, c), I.Int.add(c, b), Z.Int.add_comm(b, c)),
        Equal.trans(I.Int, s3, s4, I.Int.add(I.Int.add(a, c), I.Int.add(b, d)),
          Equal.cong(I.Int, I.Int, w => I.Int.add(a, w), I.Int.add(I.Int.add(c, b), d), I.Int.add(c, I.Int.add(b, d)), Z.Int.add_assoc(c, b, d)),
          Equal.sym(I.Int, I.Int.add(I.Int.add(a, c), I.Int.add(b, d)), s4, Z.Int.add_assoc(a, c, I.Int.add(b, d)))))))

# (a + b) c = a c + b c
def Int.dist_r(+a: I.Int, +b: I.Int, +c: I.Int) -> {I.Int.mul(I.Int.add(a, b), c) == I.Int.add(I.Int.mul(a, c), I.Int.mul(b, c)) : I.Int}:
  Equal.trans(I.Int, I.Int.mul(I.Int.add(a, b), c), I.Int.mul(c, I.Int.add(a, b)), I.Int.add(I.Int.mul(a, c), I.Int.mul(b, c)), Z.Int.mul_comm(I.Int.add(a, b), c),
    Equal.trans(I.Int, I.Int.mul(c, I.Int.add(a, b)), I.Int.add(I.Int.mul(c, a), I.Int.mul(c, b)), I.Int.add(I.Int.mul(a, c), I.Int.mul(b, c)), Z.Int.dist_l(c, a, b),
      Equal.trans(I.Int, I.Int.add(I.Int.mul(c, a), I.Int.mul(c, b)), I.Int.add(I.Int.mul(a, c), I.Int.mul(c, b)), I.Int.add(I.Int.mul(a, c), I.Int.mul(b, c)),
        Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.mul(c, b)), I.Int.mul(c, a), I.Int.mul(a, c), Z.Int.mul_comm(c, a)),
        Equal.cong(I.Int, I.Int, w => I.Int.add(I.Int.mul(a, c), w), I.Int.mul(c, b), I.Int.mul(b, c), Z.Int.mul_comm(c, b)))))

def Int.dbl_add(+a: I.Int) -> {D.Int.dbl(a) == I.Int.add(a, a) : I.Int}:
  match a:
    case I.IPos{+n}:
      Equal.cong(Nat, I.Int, w => I.IPos{w}, Nat.double(n), Nat.add(n, n), Nat.double_add(n))
    case I.INeg{+n}:
      Equal.cong(Nat, I.Int, w => I.INeg{1n+w}, Nat.double(n), Nat.add(n, n), Nat.double_add(n))

def Int.dbl_hom(+a: I.Int, +b: I.Int) -> {D.Int.dbl(I.Int.add(a, b)) == I.Int.add(D.Int.dbl(a), D.Int.dbl(b)) : I.Int}:
  +ab = I.Int.add(a, b)
  Equal.trans(I.Int, D.Int.dbl(ab), I.Int.add(ab, ab), I.Int.add(D.Int.dbl(a), D.Int.dbl(b)), Int.dbl_add(ab),
    Equal.trans(I.Int, I.Int.add(ab, ab), I.Int.add(I.Int.add(a, a), I.Int.add(b, b)), I.Int.add(D.Int.dbl(a), D.Int.dbl(b)), Int.add4(a, b, a, b),
      Equal.sym(I.Int, I.Int.add(D.Int.dbl(a), D.Int.dbl(b)), I.Int.add(I.Int.add(a, a), I.Int.add(b, b)),
        Equal.trans(I.Int, I.Int.add(D.Int.dbl(a), D.Int.dbl(b)), I.Int.add(I.Int.add(a, a), D.Int.dbl(b)), I.Int.add(I.Int.add(a, a), I.Int.add(b, b)),
          Equal.cong(I.Int, I.Int, w => I.Int.add(w, D.Int.dbl(b)), D.Int.dbl(a), I.Int.add(a, a), Int.dbl_add(a)),
          Equal.cong(I.Int, I.Int, w => I.Int.add(I.Int.add(a, a), w), D.Int.dbl(b), I.Int.add(b, b), Int.dbl_add(b))))))

def Int.dbl_mul(+a: I.Int, +b: I.Int) -> {D.Int.dbl(I.Int.mul(a, b)) == I.Int.mul(D.Int.dbl(a), b) : I.Int}:
  +ab = I.Int.mul(a, b)
  Equal.trans(I.Int, D.Int.dbl(ab), I.Int.add(ab, ab), I.Int.mul(D.Int.dbl(a), b), Int.dbl_add(ab),
    Equal.trans(I.Int, I.Int.add(ab, ab), I.Int.mul(I.Int.add(a, a), b), I.Int.mul(D.Int.dbl(a), b), Equal.sym(I.Int, I.Int.mul(I.Int.add(a, a), b), I.Int.add(ab, ab), Int.dist_r(a, a, b)),
      Equal.cong(I.Int, I.Int, w => I.Int.mul(w, b), I.Int.add(a, a), D.Int.dbl(a), Equal.sym(I.Int, D.Int.dbl(a), I.Int.add(a, a), Int.dbl_add(a)))))

def Int.dbl_neg(+a: I.Int) -> {D.Int.dbl(I.Int.neg(a)) == I.Int.neg(D.Int.dbl(a)) : I.Int}:
  Equal.trans(I.Int, D.Int.dbl(I.Int.neg(a)), I.Int.add(I.Int.neg(a), I.Int.neg(a)), I.Int.neg(D.Int.dbl(a)), Int.dbl_add(I.Int.neg(a)),
    Equal.trans(I.Int, I.Int.add(I.Int.neg(a), I.Int.neg(a)), I.Int.neg(I.Int.add(a, a)), I.Int.neg(D.Int.dbl(a)), Equal.sym(I.Int, I.Int.neg(I.Int.add(a, a)), I.Int.add(I.Int.neg(a), I.Int.neg(a)), Z.Int.neg_add(a, a)),
      Equal.cong(I.Int, I.Int, w => I.Int.neg(w), I.Int.add(a, a), D.Int.dbl(a), Equal.sym(I.Int, D.Int.dbl(a), I.Int.add(a, a), Int.dbl_add(a)))))

def Int.dbl_inj(+a: I.Int, +b: I.Int) -> {D.Int.dbl(a) == D.Int.dbl(b) : I.Int} -> {a == b : I.Int}:
  match a b:
    case I.IPos{+n} I.IPos{+m}:
      e => Equal.cong(Nat, I.Int, w => I.IPos{w}, n, m, Nat.double_inj(n, m)(Equal.cong(I.Int, Nat, w => Int.mag(w), I.IPos{Nat.double(n)}, I.IPos{Nat.double(m)}, e)))
    case I.INeg{+n} I.INeg{+m}:
      e => Equal.cong(Nat, I.Int, w => I.INeg{w}, n, m, Nat.double_inj(n, m)(Equal.cong(Nat, Nat, w => Nat.pred(w), 1n+Nat.double(n), 1n+Nat.double(m), Equal.cong(I.Int, Nat, w => Int.mag(w), I.INeg{1n+Nat.double(n)}, I.INeg{1n+Nat.double(m)}, e))))
    case I.IPos{+n} I.INeg{+m}:
      e => Empty.absurd({I.IPos{n} == I.INeg{m} : I.Int}, Int.pn(Nat.double(n), 1n+Nat.double(m), e))
    case I.INeg{+n} I.IPos{+m}:
      e => Empty.absurd({I.INeg{n} == I.IPos{m} : I.Int}, Int.pn(Nat.double(m), 1n+Nat.double(n), Equal.sym(I.Int, I.INeg{1n+Nat.double(n)}, I.IPos{Nat.double(m)}, e)))

def Int.even_dbl(+a: I.Int) -> {D.Int.even(D.Int.dbl(a)) == True{} : Bool}:
  match a:
    case I.IPos{+n}:
      Nat.even_double(n)
    case I.INeg{+n}:
      %Equal.sym(Bool, D.Nat.even(1n+Nat.double(n)), False{}, Nat.odd_double(n)) : {Bool.not(_) == True{} : Bool}
      {==}

def Int.half_dbl(+a: I.Int) -> {D.Int.half(D.Int.dbl(a)) == a : I.Int}:
  match a:
    case I.IPos{+n}:
      Equal.cong(Nat, I.Int, w => I.IPos{w}, D.Nat.half(Nat.double(n)), n, Nat.half_double(n))
    case I.INeg{+n}:
      Equal.cong(Nat, I.Int, w => I.INeg{w}, D.Nat.half(1n+Nat.double(n)), n, Nat.half_odd(n))

# an even integer is twice its half
def Int.even_split(+a: I.Int) -> {D.Int.even(a) == True{} : Bool} -> {a == D.Int.dbl(D.Int.half(a)) : I.Int}:
  match a:
    case I.IPos{+n}:
      e => Equal.cong(Nat, I.Int, w => I.IPos{w}, n, Nat.double(D.Nat.half(n)), Nat.even_split(n)(e))
    case I.INeg{+n}:
      e => Equal.cong(Nat, I.Int, w => I.INeg{w}, n, 1n+Nat.double(D.Nat.half(n)), Nat.odd_split(n)(Bool.not_t(D.Nat.even(n))(e)))

def Int.pos_dbl(+a: I.Int) -> {I.Int.pos(D.Int.dbl(a)) == I.Int.pos(a) : Bool}:
  match a:
    case I.IPos{n}:
      {==}
    case I.INeg{n}:
      {==}

def Int.pos_half(+a: I.Int) -> {I.Int.pos(D.Int.half(a)) == I.Int.pos(a) : Bool}:
  match a:
    case I.IPos{n}:
      {==}
    case I.INeg{n}:
      {==}

def Int.abs_dbl(+a: I.Int) -> {I.Int.abs(D.Int.dbl(a)) == D.Int.dbl(I.Int.abs(a)) : I.Int}:
  match a:
    case I.IPos{n}:
      {==}
    case I.INeg{n}:
      {==}

# Integers: shifting
# ------------------

def Int.sh_add(+k: Nat, +a: I.Int, +b: I.Int) -> {D.Int.sh(k, I.Int.add(a, b)) == I.Int.add(D.Int.sh(k, a), D.Int.sh(k, b)) : I.Int}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(I.Int, D.Int.dbl(D.Int.sh(j, I.Int.add(a, b))), D.Int.dbl(I.Int.add(D.Int.sh(j, a), D.Int.sh(j, b))), I.Int.add(D.Int.dbl(D.Int.sh(j, a)), D.Int.dbl(D.Int.sh(j, b))),
        Equal.cong(I.Int, I.Int, w => D.Int.dbl(w), D.Int.sh(j, I.Int.add(a, b)), I.Int.add(D.Int.sh(j, a), D.Int.sh(j, b)), Int.sh_add(j, a, b)),
        Int.dbl_hom(D.Int.sh(j, a), D.Int.sh(j, b)))

def Int.sh_mul(+k: Nat, +a: I.Int, +b: I.Int) -> {D.Int.sh(k, I.Int.mul(a, b)) == I.Int.mul(D.Int.sh(k, a), b) : I.Int}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(I.Int, D.Int.dbl(D.Int.sh(j, I.Int.mul(a, b))), D.Int.dbl(I.Int.mul(D.Int.sh(j, a), b)), I.Int.mul(D.Int.dbl(D.Int.sh(j, a)), b),
        Equal.cong(I.Int, I.Int, w => D.Int.dbl(w), D.Int.sh(j, I.Int.mul(a, b)), I.Int.mul(D.Int.sh(j, a), b), Int.sh_mul(j, a, b)),
        Int.dbl_mul(D.Int.sh(j, a), b))

def Int.sh_sh(+j: Nat, +k: Nat, +a: I.Int) -> {D.Int.sh(j, D.Int.sh(k, a)) == D.Int.sh(Nat.add(j, k), a) : I.Int}:
  match j:
    case 0n:
      {==}
    case 1n+i:
      Equal.cong(I.Int, I.Int, w => D.Int.dbl(w), D.Int.sh(i, D.Int.sh(k, a)), D.Int.sh(Nat.add(i, k), a), Int.sh_sh(i, k, a))

def Int.sh_neg(+k: Nat, +a: I.Int) -> {D.Int.sh(k, I.Int.neg(a)) == I.Int.neg(D.Int.sh(k, a)) : I.Int}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(I.Int, D.Int.dbl(D.Int.sh(j, I.Int.neg(a))), D.Int.dbl(I.Int.neg(D.Int.sh(j, a))), I.Int.neg(D.Int.dbl(D.Int.sh(j, a))),
        Equal.cong(I.Int, I.Int, w => D.Int.dbl(w), D.Int.sh(j, I.Int.neg(a)), I.Int.neg(D.Int.sh(j, a)), Int.sh_neg(j, a)),
        Int.dbl_neg(D.Int.sh(j, a)))

def Int.sh_zero(+k: Nat) -> {D.Int.sh(k, I.IPos{0n}) == I.IPos{0n} : I.Int}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.cong(I.Int, I.Int, w => D.Int.dbl(w), D.Int.sh(j, I.IPos{0n}), I.IPos{0n}, Int.sh_zero(j))

def Int.sh_inj(+k: Nat, +a: I.Int, +b: I.Int) -> {D.Int.sh(k, a) == D.Int.sh(k, b) : I.Int} -> {a == b : I.Int}:
  match k:
    case 0n:
      e => e
    case 1n+j:
      e => Int.sh_inj(j, a, b)(Int.dbl_inj(D.Int.sh(j, a), D.Int.sh(j, b))(e))

def Int.pos_sh(+k: Nat, +a: I.Int) -> {I.Int.pos(D.Int.sh(k, a)) == I.Int.pos(a) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(Bool, I.Int.pos(D.Int.dbl(D.Int.sh(j, a))), I.Int.pos(D.Int.sh(j, a)), I.Int.pos(a), Int.pos_dbl(D.Int.sh(j, a)), Int.pos_sh(j, a))

def Int.abs_sh(+k: Nat, +a: I.Int) -> {I.Int.abs(D.Int.sh(k, a)) == D.Int.sh(k, I.Int.abs(a)) : I.Int}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(I.Int, I.Int.abs(D.Int.dbl(D.Int.sh(j, a))), D.Int.dbl(I.Int.abs(D.Int.sh(j, a))), D.Int.dbl(D.Int.sh(j, I.Int.abs(a))),
        Int.abs_dbl(D.Int.sh(j, a)),
        Equal.cong(I.Int, I.Int, w => D.Int.dbl(w), I.Int.abs(D.Int.sh(j, a)), D.Int.sh(j, I.Int.abs(a)), Int.abs_sh(j, a)))

# sh(k, dbl a) = dbl(sh(k, a))
def Int.sh_dbl(+k: Nat, +a: I.Int) -> {D.Int.sh(k, D.Int.dbl(a)) == D.Int.dbl(D.Int.sh(k, a)) : I.Int}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.cong(I.Int, I.Int, w => D.Int.dbl(w), D.Int.sh(j, D.Int.dbl(a)), D.Int.dbl(D.Int.sh(j, a)), Int.sh_dbl(j, a))

# The normal form
# ---------------

# (m1, e1) ~ (m2, e2): m1 2^e2 = m2 2^e1
def Sim(m1: I.Int, e1: Nat, m2: I.Int, e2: Nat) -> Type:
  {D.Int.sh(e2, m1) == D.Int.sh(e1, m2) : I.Int}

def Bool.not_f(+x: Bool) -> {Bool.not(x) == False{} : Bool} -> {x == True{} : Bool}:
  match x:
    case True{}:
      e => {==}
    case False{}:
      e => Empty.absurd({False{} == True{} : Bool}, Z.Bool.ft(Equal.sym(Bool, True{}, False{}, e)))

def Of.even(+f: Nat, +m: I.Int, ev: {D.Int.even(m) == True{} : Bool}) -> {D.Dy.of(1n+f, m) == D.Dy.of(f, D.Int.half(m)) : D.Dy}:
  %Equal.sym(Bool, D.Int.even(m), True{}, ev) : {Bool.pick(D.Dy, _, D.Dy.of(f, D.Int.half(m)), D.Dy.odd(m, f)) == D.Dy.of(f, D.Int.half(m)) : D.Dy}
  {==}

def Of.odd(+f: Nat, +m: I.Int, od: {D.Int.even(m) == False{} : Bool}) -> {D.Dy.of(1n+f, m) == D.Dy.odd(m, f) : D.Dy}:
  %Equal.sym(Bool, D.Int.even(m), False{}, od) : {Bool.pick(D.Dy, _, D.Dy.of(f, D.Int.half(m)), D.Dy.odd(m, f)) == D.Dy.odd(m, f) : D.Dy}
  {==}

def Odd.num(+m: I.Int, +f: Nat) -> {D.Int.even(m) == False{} : Bool} -> {D.Dy.num(D.Dy.odd(m, f)) == m : I.Int}:
  match m:
    case I.IPos{+n}:
      od => Equal.cong(Nat, I.Int, w => I.IPos{w}, 1n+Nat.double(D.Nat.half(n)), n, Equal.sym(Nat, n, 1n+Nat.double(D.Nat.half(n)), Nat.odd_split(n)(od)))
    case I.INeg{+n}:
      od => Equal.cong(Nat, I.Int, w => I.INeg{w}, Nat.double(D.Nat.half(n)), n, Equal.sym(Nat, n, Nat.double(D.Nat.half(n)), Nat.even_split(n)(Bool.not_f(D.Nat.even(n))(od))))

def Odd.den(+m: I.Int, +f: Nat) -> {D.Dy.den(D.Dy.odd(m, f)) == 1n+f : Nat}:
  match m:
    case I.IPos{n}:
      {==}
    case I.INeg{n}:
      {==}

def Dy.bump(x: D.Dy) -> D.Dy:
  match x:
    case D.DInt{m}:
      D.DInt{m}
    case D.DFrac{s, k, e}:
      D.DFrac{s, k, 1n+e}

def Odd.bump(+m: I.Int, +f: Nat) -> {Dy.bump(D.Dy.odd(m, f)) == D.Dy.odd(m, 1n+f) : D.Dy}:
  match m:
    case I.IPos{n}:
      {==}
    case I.INeg{n}:
      {==}

# of(e + k, m 2^k) = of(e, m)
def Of.shift(+k: Nat, +e: Nat, +m: I.Int) -> {D.Dy.of(Nat.add(e, k), D.Int.sh(k, m)) == D.Dy.of(e, m) : D.Dy}:
  match k:
    case 0n:
      Equal.cong(Nat, D.Dy, w => D.Dy.of(w, m), Nat.add(e, 0n), e, NL.Nat.add_zero_r(e))
    case 1n+j:
      +x = D.Int.dbl(D.Int.sh(j, m))
      +ej = Nat.add(e, j)
      Equal.trans(D.Dy, D.Dy.of(Nat.add(e, 1n+j), x), D.Dy.of(1n+ej, x), D.Dy.of(e, m),
        Equal.cong(Nat, D.Dy, w => D.Dy.of(w, x), Nat.add(e, 1n+j), 1n+ej, NL.Nat.add_succ_r(e, j)),
        Equal.trans(D.Dy, D.Dy.of(1n+ej, x), D.Dy.of(ej, D.Int.half(x)), D.Dy.of(e, m), Of.even(ej, x, Int.even_dbl(D.Int.sh(j, m))),
          Equal.trans(D.Dy, D.Dy.of(ej, D.Int.half(x)), D.Dy.of(ej, D.Int.sh(j, m)), D.Dy.of(e, m),
            Equal.cong(I.Int, D.Dy, w => D.Dy.of(ej, w), D.Int.half(x), D.Int.sh(j, m), Int.half_dbl(D.Int.sh(j, m))),
            Of.shift(j, e, m))))

# the normal form has the pair's value
def Of.val.p(+e: Nat, +m: I.Int, p: Bool, +ep: {D.Int.even(m) == p : Bool}) -> Sim(D.Dy.num(D.Dy.of(e, m)), D.Dy.den(D.Dy.of(e, m)), m, e):
  match e:
   case 0n:
    {==}
   case 1n+f:
    match p:
     case True{}:
      +y = D.Dy.of(f, D.Int.half(m))
      ih = Of.val.p(f, D.Int.half(m), D.Int.even(D.Int.half(m)), {==})
      %Equal.sym(D.Dy, D.Dy.of(1n+f, m), y, Of.even(f, m, ep)) : {D.Int.sh(1n+f, D.Dy.num(_)) == D.Int.sh(D.Dy.den(_), m) : I.Int}
      Equal.trans(I.Int, D.Int.dbl(D.Int.sh(f, D.Dy.num(y))), D.Int.dbl(D.Int.sh(D.Dy.den(y), D.Int.half(m))), D.Int.sh(D.Dy.den(y), m),
        Equal.cong(I.Int, I.Int, w => D.Int.dbl(w), D.Int.sh(f, D.Dy.num(y)), D.Int.sh(D.Dy.den(y), D.Int.half(m)), ih),
        Equal.trans(I.Int, D.Int.dbl(D.Int.sh(D.Dy.den(y), D.Int.half(m))), D.Int.sh(D.Dy.den(y), D.Int.dbl(D.Int.half(m))), D.Int.sh(D.Dy.den(y), m),
          Equal.sym(I.Int, D.Int.sh(D.Dy.den(y), D.Int.dbl(D.Int.half(m))), D.Int.dbl(D.Int.sh(D.Dy.den(y), D.Int.half(m))), Int.sh_dbl(D.Dy.den(y), D.Int.half(m))),
          Equal.cong(I.Int, I.Int, w => D.Int.sh(D.Dy.den(y), w), D.Int.dbl(D.Int.half(m)), m, Equal.sym(I.Int, m, D.Int.dbl(D.Int.half(m)), Int.even_split(m)(ep)))))
     case False{}:
      +y = D.Dy.odd(m, f)
      %Equal.sym(D.Dy, D.Dy.of(1n+f, m), y, Of.odd(f, m, ep)) : {D.Int.sh(1n+f, D.Dy.num(_)) == D.Int.sh(D.Dy.den(_), m) : I.Int}
      %Equal.sym(Nat, D.Dy.den(D.Dy.odd(m, f)), 1n+f, Odd.den(m, f)) : {D.Int.sh(1n+f, D.Dy.num(y)) == D.Int.sh(_, m) : I.Int}
      Equal.cong(I.Int, I.Int, w => D.Int.sh(1n+f, w), D.Dy.num(y), m, Odd.num(m, f)(ep))

def Of.val(+e: Nat, +m: I.Int) -> Sim(D.Dy.num(D.Dy.of(e, m)), D.Dy.den(D.Dy.of(e, m)), m, e):
  Of.val.p(e, m, D.Int.even(m), {==})

# a dyadic's own pair normalises back to it
def Of.self(+x: D.Dy) -> {D.Dy.of(D.Dy.den(x), D.Dy.num(x)) == x : D.Dy}:
  match x:
    case D.DInt{m}:
      {==}
    case D.DFrac{s, +k, +e}:
      match s:
        case False{}:
          Equal.trans(D.Dy, D.Dy.of(1n+e, I.IPos{1n+Nat.double(k)}), D.Dy.odd(I.IPos{1n+Nat.double(k)}, e), D.DFrac{False{}, k, e},
            Of.odd(e, I.IPos{1n+Nat.double(k)}, Nat.odd_double(k)),
            Equal.cong(Nat, D.Dy, w => D.DFrac{False{}, w, e}, D.Nat.half(1n+Nat.double(k)), k, Nat.half_odd(k)))
        case True{}:
          Equal.trans(D.Dy, D.Dy.of(1n+e, I.INeg{Nat.double(k)}), D.Dy.odd(I.INeg{Nat.double(k)}, e), D.DFrac{True{}, k, e},
            Of.odd(e, I.INeg{Nat.double(k)}, Equal.cong(Bool, Bool, w => Bool.not(w), D.Nat.even(Nat.double(k)), True{}, Nat.even_double(k))),
            Equal.cong(Nat, D.Dy, w => D.DFrac{True{}, w, e}, D.Nat.half(Nat.double(k)), k, Nat.half_double(k)))

# twice something is not odd
def Odd.dbl(+z: I.Int, -m: I.Int, h: {D.Int.dbl(z) == m : I.Int}, od: {D.Int.even(m) == False{} : Bool}) -> Empty:
  Z.Bool.ft(Equal.trans(Bool, False{}, D.Int.even(m), True{}, Equal.sym(Bool, D.Int.even(m), False{}, od),
    Equal.trans(Bool, D.Int.even(m), D.Int.even(D.Int.dbl(z)), True{},
      Equal.cong(I.Int, Bool, w => D.Int.even(w), m, D.Int.dbl(z), Equal.sym(I.Int, D.Int.dbl(z), m, h)),
      Int.even_dbl(z))))

# odd m1 2^b = odd m2 2^a forces a = b and m1 = m2
def Odd.uniq(+a: Nat, +b: Nat, +m1: I.Int, +m2: I.Int, +od1: {D.Int.even(m1) == False{} : Bool}, +od2: {D.Int.even(m2) == False{} : Bool},
  h: {D.Int.sh(b, m1) == D.Int.sh(a, m2) : I.Int}) -> {D.Dy.odd(m1, a) == D.Dy.odd(m2, b) : D.Dy}:
  match a b:
    case 0n 0n:
      Equal.cong(I.Int, D.Dy, w => D.Dy.odd(w, 0n), m1, m2, h)
    case 0n 1n+bp:
      Empty.absurd({D.Dy.odd(m1, 0n) == D.Dy.odd(m2, 1n+bp) : D.Dy}, Odd.dbl(D.Int.sh(bp, m1), m2, h, od2))
    case 1n+ap 0n:
      Empty.absurd({D.Dy.odd(m1, 1n+ap) == D.Dy.odd(m2, 0n) : D.Dy}, Odd.dbl(D.Int.sh(ap, m2), m1, Equal.sym(I.Int, m1, D.Int.dbl(D.Int.sh(ap, m2)), h), od1))
    case 1n+ap 1n+bp:
      +ih = Odd.uniq(ap, bp, m1, m2, od1, od2, Int.dbl_inj(D.Int.sh(bp, m1), D.Int.sh(ap, m2))(h))
      Equal.trans(D.Dy, D.Dy.odd(m1, 1n+ap), Dy.bump(D.Dy.odd(m1, ap)), D.Dy.odd(m2, 1n+bp),
        Equal.sym(D.Dy, Dy.bump(D.Dy.odd(m1, ap)), D.Dy.odd(m1, 1n+ap), Odd.bump(m1, ap)),
        Equal.trans(D.Dy, Dy.bump(D.Dy.odd(m1, ap)), Dy.bump(D.Dy.odd(m2, bp)), D.Dy.odd(m2, 1n+bp),
          Equal.cong(D.Dy, D.Dy, w => Dy.bump(w), D.Dy.odd(m1, ap), D.Dy.odd(m2, bp), ih),
          Odd.bump(m2, bp)))

# equivalent pairs have the same normal form; by induction on (e1, e2),
# lexicographically, with the parities of m1 and m2 at hand
def Of.eq(+e1: Nat, +e2: Nat, +m1: I.Int, +m2: I.Int, p1: Bool, +ep1: {D.Int.even(m1) == p1 : Bool}, p2: Bool, +ep2: {D.Int.even(m2) == p2 : Bool},
  h: Sim(m1, e1, m2, e2)) -> {D.Dy.of(e1, m1) == D.Dy.of(e2, m2) : D.Dy}:
  match e1 e2:
    case 0n e2b:
      Equal.trans(D.Dy, D.Dy.of(0n, m1), D.Dy.of(e2b, D.Int.sh(e2b, m1)), D.Dy.of(e2b, m2),
        Equal.sym(D.Dy, D.Dy.of(e2b, D.Int.sh(e2b, m1)), D.Dy.of(0n, m1), Of.shift(e2b, 0n, m1)),
        Equal.cong(I.Int, D.Dy, w => D.Dy.of(e2b, w), D.Int.sh(e2b, m1), m2, h))
    case 1n+a 0n:
      Equal.trans(D.Dy, D.Dy.of(1n+a, m1), D.Dy.of(1n+a, D.Int.sh(1n+a, m2)), D.Dy.of(0n, m2),
        Equal.cong(I.Int, D.Dy, w => D.Dy.of(1n+a, w), m1, D.Int.sh(1n+a, m2), h),
        Of.shift(1n+a, 0n, m2))
    case 1n+a 1n+b:
      match p1 p2:
        case True{} True{}:
          +h0 = Int.dbl_inj(D.Int.sh(b, m1), D.Int.sh(a, m2))(h)
          +h1 = D.Int.half(m1)
          +h2 = D.Int.half(m2)
          +s1 = Int.even_split(m1)(ep1)
          +s2 = Int.even_split(m2)(ep2)
          +sim = Int.dbl_inj(D.Int.sh(b, h1), D.Int.sh(a, h2))(
            Equal.trans(I.Int, D.Int.dbl(D.Int.sh(b, h1)), D.Int.sh(b, m1), D.Int.dbl(D.Int.sh(a, h2)),
              Equal.trans(I.Int, D.Int.dbl(D.Int.sh(b, h1)), D.Int.sh(b, D.Int.dbl(h1)), D.Int.sh(b, m1),
                Equal.sym(I.Int, D.Int.sh(b, D.Int.dbl(h1)), D.Int.dbl(D.Int.sh(b, h1)), Int.sh_dbl(b, h1)),
                Equal.cong(I.Int, I.Int, w => D.Int.sh(b, w), D.Int.dbl(h1), m1, Equal.sym(I.Int, m1, D.Int.dbl(h1), s1))),
              Equal.trans(I.Int, D.Int.sh(b, m1), D.Int.sh(a, m2), D.Int.dbl(D.Int.sh(a, h2)), h0,
                Equal.trans(I.Int, D.Int.sh(a, m2), D.Int.sh(a, D.Int.dbl(h2)), D.Int.dbl(D.Int.sh(a, h2)),
                  Equal.cong(I.Int, I.Int, w => D.Int.sh(a, w), m2, D.Int.dbl(h2), s2),
                  Int.sh_dbl(a, h2)))))
          Equal.trans(D.Dy, D.Dy.of(1n+a, m1), D.Dy.of(a, h1), D.Dy.of(1n+b, m2), Of.even(a, m1, ep1),
            Equal.trans(D.Dy, D.Dy.of(a, h1), D.Dy.of(b, h2), D.Dy.of(1n+b, m2),
              Of.eq(a, b, h1, h2, D.Int.even(h1), {==}, D.Int.even(h2), {==}, sim),
              Equal.sym(D.Dy, D.Dy.of(1n+b, m2), D.Dy.of(b, h2), Of.even(b, m2, ep2))))
        case True{} False{}:
          +h0 = Int.dbl_inj(D.Int.sh(b, m1), D.Int.sh(a, m2))(h)
          +h1 = D.Int.half(m1)
          +s1 = Int.even_split(m1)(ep1)
          +sim = Equal.trans(I.Int, D.Int.dbl(D.Int.sh(b, h1)), D.Int.sh(b, m1), D.Int.sh(a, m2),
            Equal.trans(I.Int, D.Int.dbl(D.Int.sh(b, h1)), D.Int.sh(b, D.Int.dbl(h1)), D.Int.sh(b, m1),
              Equal.sym(I.Int, D.Int.sh(b, D.Int.dbl(h1)), D.Int.dbl(D.Int.sh(b, h1)), Int.sh_dbl(b, h1)),
              Equal.cong(I.Int, I.Int, w => D.Int.sh(b, w), D.Int.dbl(h1), m1, Equal.sym(I.Int, m1, D.Int.dbl(h1), s1))),
            h0)
          Equal.trans(D.Dy, D.Dy.of(1n+a, m1), D.Dy.of(a, h1), D.Dy.of(1n+b, m2), Of.even(a, m1, ep1),
            Of.eq(a, 1n+b, h1, m2, D.Int.even(h1), {==}, False{}, ep2, sim))
        case False{} True{}:
          +h0 = Int.dbl_inj(D.Int.sh(b, m1), D.Int.sh(a, m2))(h)
          +h2 = D.Int.half(m2)
          +s2 = Int.even_split(m2)(ep2)
          +sim = Equal.trans(I.Int, D.Int.sh(b, m1), D.Int.sh(a, m2), D.Int.dbl(D.Int.sh(a, h2)), h0,
            Equal.trans(I.Int, D.Int.sh(a, m2), D.Int.sh(a, D.Int.dbl(h2)), D.Int.dbl(D.Int.sh(a, h2)),
              Equal.cong(I.Int, I.Int, w => D.Int.sh(a, w), m2, D.Int.dbl(h2), s2),
              Int.sh_dbl(a, h2)))
          Equal.trans(D.Dy, D.Dy.of(1n+a, m1), D.Dy.of(b, h2), D.Dy.of(1n+b, m2),
            Of.eq(1n+a, b, m1, h2, False{}, ep1, D.Int.even(h2), {==}, sim),
            Equal.sym(D.Dy, D.Dy.of(1n+b, m2), D.Dy.of(b, h2), Of.even(b, m2, ep2)))
        case False{} False{}:
          +h0 = Int.dbl_inj(D.Int.sh(b, m1), D.Int.sh(a, m2))(h)
          Equal.trans(D.Dy, D.Dy.of(1n+a, m1), D.Dy.odd(m1, a), D.Dy.of(1n+b, m2), Of.odd(a, m1, ep1),
            Equal.trans(D.Dy, D.Dy.odd(m1, a), D.Dy.odd(m2, b), D.Dy.of(1n+b, m2),
              Odd.uniq(a, b, m1, m2, ep1, ep2, h0),
              Equal.sym(D.Dy, D.Dy.of(1n+b, m2), D.Dy.odd(m2, b), Of.odd(b, m2, ep2))))

def Of.eqv(+e1: Nat, +e2: Nat, +m1: I.Int, +m2: I.Int, h: Sim(m1, e1, m2, e2)) -> {D.Dy.of(e1, m1) == D.Dy.of(e2, m2) : D.Dy}:
  Of.eq(e1, e2, m1, m2, D.Int.even(m1), {==}, D.Int.even(m2), {==}, h)

# Powers of two as products
# -------------------------
# The ring laws are Int identities in the numerators and the powers 2^e,
# proven by the normaliser at T = Int (proofs/equiv.bend), so shifts are
# rewritten as products by P(k) = 2^k.

def P(k: Nat) -> I.Int:
  D.Int.sh(k, I.IPos{1n})

def Int.one_l(+m: I.Int) -> {I.Int.mul(I.IPos{1n}, m) == m : I.Int}:
  Equal.trans(I.Int, I.Int.mul(I.IPos{1n}, m), I.Int.mul(m, I.IPos{1n}), m, Z.Int.mul_comm(I.IPos{1n}, m), Z.Int.unit_r(m))

def Sh.p(+k: Nat, +m: I.Int) -> {D.Int.sh(k, m) == I.Int.mul(m, P(k)) : I.Int}:
  Equal.trans(I.Int, D.Int.sh(k, m), D.Int.sh(k, I.Int.mul(I.IPos{1n}, m)), I.Int.mul(m, P(k)),
    Equal.cong(I.Int, I.Int, w => D.Int.sh(k, w), m, I.Int.mul(I.IPos{1n}, m), Equal.sym(I.Int, I.Int.mul(I.IPos{1n}, m), m, Int.one_l(m))),
    Equal.trans(I.Int, D.Int.sh(k, I.Int.mul(I.IPos{1n}, m)), I.Int.mul(P(k), m), I.Int.mul(m, P(k)), Int.sh_mul(k, I.IPos{1n}, m), Z.Int.mul_comm(P(k), m)))

def P.add(+a: Nat, +b: Nat) -> {P(Nat.add(a, b)) == I.Int.mul(P(a), P(b)) : I.Int}:
  Equal.trans(I.Int, P(Nat.add(a, b)), D.Int.sh(a, P(b)), I.Int.mul(P(a), P(b)),
    Equal.sym(I.Int, D.Int.sh(a, P(b)), P(Nat.add(a, b)), Int.sh_sh(a, b, I.IPos{1n})),
    Equal.trans(I.Int, D.Int.sh(a, P(b)), I.Int.mul(P(b), P(a)), I.Int.mul(P(a), P(b)), Sh.p(a, P(b)), Z.Int.mul_comm(P(b), P(a))))

# x 2^k = y 2^k gives x = y
def Pc(+k: Nat, +x: I.Int, +y: I.Int, h: {I.Int.mul(x, P(k)) == I.Int.mul(y, P(k)) : I.Int}) -> {x == y : I.Int}:
  Int.sh_inj(k, x, y)(Equal.trans(I.Int, D.Int.sh(k, x), I.Int.mul(x, P(k)), D.Int.sh(k, y), Sh.p(k, x),
    Equal.trans(I.Int, I.Int.mul(x, P(k)), I.Int.mul(y, P(k)), D.Int.sh(k, y), h, Equal.sym(I.Int, D.Int.sh(k, y), I.Int.mul(y, P(k)), Sh.p(k, y)))))

# the normal form's value, and equal values, with products
def Of.valP(+e: Nat, +m: I.Int) -> {I.Int.mul(D.Dy.num(D.Dy.of(e, m)), P(e)) == I.Int.mul(m, P(D.Dy.den(D.Dy.of(e, m)))) : I.Int}:
  +n = D.Dy.num(D.Dy.of(e, m))
  +d = D.Dy.den(D.Dy.of(e, m))
  Equal.trans(I.Int, I.Int.mul(n, P(e)), D.Int.sh(e, n), I.Int.mul(m, P(d)), Equal.sym(I.Int, D.Int.sh(e, n), I.Int.mul(n, P(e)), Sh.p(e, n)),
    Equal.trans(I.Int, D.Int.sh(e, n), D.Int.sh(d, m), I.Int.mul(m, P(d)), Of.val(e, m), Sh.p(d, m)))

def Of.eqvP(+e1: Nat, +e2: Nat, +m1: I.Int, +m2: I.Int, h: {I.Int.mul(m1, P(e2)) == I.Int.mul(m2, P(e1)) : I.Int}) -> {D.Dy.of(e1, m1) == D.Dy.of(e2, m2) : D.Dy}:
  Of.eqv(e1, e2, m1, m2, Equal.trans(I.Int, D.Int.sh(e2, m1), I.Int.mul(m1, P(e2)), D.Int.sh(e1, m2), Sh.p(e2, m1),
    Equal.trans(I.Int, I.Int.mul(m1, P(e2)), I.Int.mul(m2, P(e1)), D.Int.sh(e1, m2), h, Equal.sym(I.Int, D.Int.sh(e1, m2), I.Int.mul(m2, P(e1)), Sh.p(e1, m2)))))

def Of.cong(-e1: Nat, -e2: Nat, -m1: I.Int, -m2: I.Int, ee: {e1 == e2 : Nat}, em: {m1 == m2 : I.Int}) -> {D.Dy.of(e1, m1) == D.Dy.of(e2, m2) : D.Dy}:
  %ee : {D.Dy.of(e1, m1) == D.Dy.of(_, m2) : D.Dy}
  %em : {D.Dy.of(e1, m1) == D.Dy.of(e1, _) : D.Dy}
  {==}

def Int.cong2(-a1: I.Int, -a2: I.Int, -b1: I.Int, -b2: I.Int, e1: {a1 == a2 : I.Int}, e2: {b1 == b2 : I.Int}) -> {I.Int.add(a1, b1) == I.Int.add(a2, b2) : I.Int}:
  %e1 : {I.Int.add(a1, b1) == I.Int.add(_, b2) : I.Int}
  %e2 : {I.Int.add(a1, b1) == I.Int.add(a1, _) : I.Int}
  {==}

def Int.mcong2(-a1: I.Int, -a2: I.Int, -b1: I.Int, -b2: I.Int, e1: {a1 == a2 : I.Int}, e2: {b1 == b2 : I.Int}) -> {I.Int.mul(a1, b1) == I.Int.mul(a2, b2) : I.Int}:
  %e1 : {I.Int.mul(a1, b1) == I.Int.mul(_, b2) : I.Int}
  %e2 : {I.Int.mul(a1, b1) == I.Int.mul(a1, _) : I.Int}
  {==}

# a raw sum's numerator with products
def Cv.sum(+ma: I.Int, +ea: Nat, +mb: I.Int, +eb: Nat) -> {I.Int.add(D.Int.sh(ea, ma), D.Int.sh(eb, mb)) == I.Int.add(I.Int.mul(ma, P(ea)), I.Int.mul(mb, P(eb))) : I.Int}:
  Int.cong2(D.Int.sh(ea, ma), I.Int.mul(ma, P(ea)), D.Int.sh(eb, mb), I.Int.mul(mb, P(eb)), Sh.p(ea, ma), Sh.p(eb, mb))

# Parts of a dyadic
# -----------------

def Num.neg(+x: D.Dy) -> {D.Dy.num(D.Dy.neg(x)) == I.Int.neg(D.Dy.num(x)) : I.Int}:
  match x:
    case D.DInt{m}:
      {==}
    case D.DFrac{s, k, e}:
      match s:
        case True{}:
          {==}
        case False{}:
          {==}

def Den.neg(+x: D.Dy) -> {D.Dy.den(D.Dy.neg(x)) == D.Dy.den(x) : Nat}:
  match x:
    case D.DInt{m}:
      {==}
    case D.DFrac{s, k, e}:
      {==}

def Int.mul_zero_l(+a: I.Int) -> {I.Int.mul(I.IPos{0n}, a) == I.IPos{0n} : I.Int}:
  Equal.trans(I.Int, I.Int.mul(I.IPos{0n}, a), I.Int.mul(a, I.IPos{0n}), I.IPos{0n}, Z.Int.mul_comm(I.IPos{0n}, a),
    NP.Alg.mul_zero_r(~I.Int, ~I.IPos{0n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.dist_l, a))

def Of.zero(+e: Nat) -> {D.Dy.of(e, I.IPos{0n}) == D.Dy.zero() : D.Dy}:
  Of.eqvP(e, 0n, I.IPos{0n}, I.IPos{0n}, Equal.trans(I.Int, I.Int.mul(I.IPos{0n}, P(0n)), I.IPos{0n}, I.Int.mul(I.IPos{0n}, P(e)), Int.mul_zero_l(P(0n)), Equal.sym(I.Int, I.Int.mul(I.IPos{0n}, P(e)), I.IPos{0n}, Int.mul_zero_l(P(e)))))

# negation passes through the normal form
def Of.neg(+e: Nat, +m: I.Int) -> {D.Dy.neg(D.Dy.of(e, m)) == D.Dy.of(e, I.Int.neg(m)) : D.Dy}:
  +o = D.Dy.of(e, m)
  +no = D.Dy.neg(o)
  +h = Equal.trans(I.Int, I.Int.mul(I.Int.neg(D.Dy.num(o)), P(e)), I.Int.neg(I.Int.mul(D.Dy.num(o), P(e))), I.Int.mul(I.Int.neg(m), P(D.Dy.den(o))),
    Z.Int.neg_mul_l(D.Dy.num(o), P(e)),
    Equal.trans(I.Int, I.Int.neg(I.Int.mul(D.Dy.num(o), P(e))), I.Int.neg(I.Int.mul(m, P(D.Dy.den(o)))), I.Int.mul(I.Int.neg(m), P(D.Dy.den(o))),
      Equal.cong(I.Int, I.Int, w => I.Int.neg(w), I.Int.mul(D.Dy.num(o), P(e)), I.Int.mul(m, P(D.Dy.den(o))), Of.valP(e, m)),
      Equal.sym(I.Int, I.Int.mul(I.Int.neg(m), P(D.Dy.den(o))), I.Int.neg(I.Int.mul(m, P(D.Dy.den(o)))), Z.Int.neg_mul_l(m, P(D.Dy.den(o))))))
  Equal.trans(D.Dy, no, D.Dy.of(D.Dy.den(no), D.Dy.num(no)), D.Dy.of(e, I.Int.neg(m)), Equal.sym(D.Dy, D.Dy.of(D.Dy.den(no), D.Dy.num(no)), no, Of.self(no)),
    Equal.trans(D.Dy, D.Dy.of(D.Dy.den(no), D.Dy.num(no)), D.Dy.of(D.Dy.den(o), I.Int.neg(D.Dy.num(o))), D.Dy.of(e, I.Int.neg(m)),
      Of.cong(D.Dy.den(no), D.Dy.den(o), D.Dy.num(no), I.Int.neg(D.Dy.num(o)), Den.neg(o), Num.neg(o)),
      Of.eqvP(D.Dy.den(o), e, I.Int.neg(D.Dy.num(o)), I.Int.neg(m), h)))

# The ring laws without nesting
# -----------------------------

def Dy.add_comm(+x: D.Dy, +y: D.Dy) -> {D.Dy.add(x, y) == D.Dy.add(y, x) : D.Dy}:
  Of.cong(Nat.add(D.Dy.den(x), D.Dy.den(y)), Nat.add(D.Dy.den(y), D.Dy.den(x)),
    I.Int.add(D.Int.sh(D.Dy.den(y), D.Dy.num(x)), D.Int.sh(D.Dy.den(x), D.Dy.num(y))), I.Int.add(D.Int.sh(D.Dy.den(x), D.Dy.num(y)), D.Int.sh(D.Dy.den(y), D.Dy.num(x))),
    NL.Nat.add_comm(D.Dy.den(x), D.Dy.den(y)), Z.Int.add_comm(D.Int.sh(D.Dy.den(y), D.Dy.num(x)), D.Int.sh(D.Dy.den(x), D.Dy.num(y))))

def Dy.mul_comm(+x: D.Dy, +y: D.Dy) -> {D.Dy.mul(x, y) == D.Dy.mul(y, x) : D.Dy}:
  Of.cong(Nat.add(D.Dy.den(x), D.Dy.den(y)), Nat.add(D.Dy.den(y), D.Dy.den(x)), I.Int.mul(D.Dy.num(x), D.Dy.num(y)), I.Int.mul(D.Dy.num(y), D.Dy.num(x)),
    NL.Nat.add_comm(D.Dy.den(x), D.Dy.den(y)), Z.Int.mul_comm(D.Dy.num(x), D.Dy.num(y)))

def Dy.zero_l(+x: D.Dy) -> {D.Dy.add(D.Dy.zero(), x) == x : D.Dy}:
  +dx = D.Dy.den(x)
  +nx = D.Dy.num(x)
  Equal.trans(D.Dy, D.Dy.of(dx, I.Int.add(D.Int.sh(dx, I.IPos{0n}), nx)), D.Dy.of(dx, nx), x,
    Of.cong(dx, dx, I.Int.add(D.Int.sh(dx, I.IPos{0n}), nx), nx, {==},
      Equal.trans(I.Int, I.Int.add(D.Int.sh(dx, I.IPos{0n}), nx), I.Int.add(I.IPos{0n}, nx), nx,
        Equal.cong(I.Int, I.Int, w => I.Int.add(w, nx), D.Int.sh(dx, I.IPos{0n}), I.IPos{0n}, Int.sh_zero(dx)),
        Z.Int.zero_l(nx))),
    Of.self(x))

def Dy.unit_r(+x: D.Dy) -> {D.Dy.mul(x, D.Dy.one()) == x : D.Dy}:
  +dx = D.Dy.den(x)
  +nx = D.Dy.num(x)
  Equal.trans(D.Dy, D.Dy.of(Nat.add(dx, 0n), I.Int.mul(nx, I.IPos{1n})), D.Dy.of(dx, nx), x,
    Of.cong(Nat.add(dx, 0n), dx, I.Int.mul(nx, I.IPos{1n}), nx, NL.Nat.add_zero_r(dx), Z.Int.unit_r(nx)),
    Of.self(x))

def Dy.neg_neg(+x: D.Dy) -> {D.Dy.neg(D.Dy.neg(x)) == x : D.Dy}:
  match x:
    case D.DInt{+m}:
      Equal.cong(I.Int, D.Dy, w => D.DInt{w}, I.Int.neg(I.Int.neg(m)), m, Z.Int.neg_neg(m))
    case D.DFrac{+s, k, e}:
      Equal.cong(Bool, D.Dy, w => D.DFrac{w, k, e}, Bool.not(Bool.not(s)), s, Bool.not_not(s))

def Dy.add_inv(+x: D.Dy) -> {D.Dy.add(x, D.Dy.neg(x)) == D.Dy.zero() : D.Dy}:
  +dx = D.Dy.den(x)
  +nx = D.Dy.num(x)
  +nnx = D.Dy.neg(x)
  Equal.trans(D.Dy, D.Dy.add(x, nnx), D.Dy.of(Nat.add(dx, dx), I.IPos{0n}), D.Dy.zero(),
    Of.cong(Nat.add(dx, D.Dy.den(nnx)), Nat.add(dx, dx), I.Int.add(D.Int.sh(D.Dy.den(nnx), nx), D.Int.sh(dx, D.Dy.num(nnx))), I.IPos{0n},
      Equal.cong(Nat, Nat, w => Nat.add(dx, w), D.Dy.den(nnx), dx, Den.neg(x)),
      Equal.trans(I.Int, I.Int.add(D.Int.sh(D.Dy.den(nnx), nx), D.Int.sh(dx, D.Dy.num(nnx))), I.Int.add(D.Int.sh(dx, nx), D.Int.sh(dx, I.Int.neg(nx))), I.IPos{0n},
        Int.cong2(D.Int.sh(D.Dy.den(nnx), nx), D.Int.sh(dx, nx), D.Int.sh(dx, D.Dy.num(nnx)), D.Int.sh(dx, I.Int.neg(nx)),
          Equal.cong(Nat, I.Int, w => D.Int.sh(w, nx), D.Dy.den(nnx), dx, Den.neg(x)),
          Equal.cong(I.Int, I.Int, w => D.Int.sh(dx, w), D.Dy.num(nnx), I.Int.neg(nx), Num.neg(x))),
        Equal.trans(I.Int, I.Int.add(D.Int.sh(dx, nx), D.Int.sh(dx, I.Int.neg(nx))), D.Int.sh(dx, I.Int.add(nx, I.Int.neg(nx))), I.IPos{0n},
          Equal.sym(I.Int, D.Int.sh(dx, I.Int.add(nx, I.Int.neg(nx))), I.Int.add(D.Int.sh(dx, nx), D.Int.sh(dx, I.Int.neg(nx))), Int.sh_add(dx, nx, I.Int.neg(nx))),
          Equal.trans(I.Int, D.Int.sh(dx, I.Int.add(nx, I.Int.neg(nx))), D.Int.sh(dx, I.IPos{0n}), I.IPos{0n},
            Equal.cong(I.Int, I.Int, w => D.Int.sh(dx, w), I.Int.add(nx, I.Int.neg(nx)), I.IPos{0n}, Z.Int.add_inv(nx)),
            Int.sh_zero(dx))))),
    Of.zero(Nat.add(dx, dx)))

def Dy.neg_add(+x: D.Dy, +y: D.Dy) -> {D.Dy.neg(D.Dy.add(x, y)) == D.Dy.add(D.Dy.neg(x), D.Dy.neg(y)) : D.Dy}:
  +dx = D.Dy.den(x)
  +dy = D.Dy.den(y)
  +nx = D.Dy.num(x)
  +ny = D.Dy.num(y)
  +s = I.Int.add(D.Int.sh(dy, nx), D.Int.sh(dx, ny))
  +rx = D.Dy.neg(x)
  +ry = D.Dy.neg(y)
  Equal.trans(D.Dy, D.Dy.neg(D.Dy.of(Nat.add(dx, dy), s)), D.Dy.of(Nat.add(dx, dy), I.Int.neg(s)), D.Dy.add(rx, ry),
    Of.neg(Nat.add(dx, dy), s),
    Of.cong(Nat.add(dx, dy), Nat.add(D.Dy.den(rx), D.Dy.den(ry)), I.Int.neg(s), I.Int.add(D.Int.sh(D.Dy.den(ry), D.Dy.num(rx)), D.Int.sh(D.Dy.den(rx), D.Dy.num(ry))),
      Equal.sym(Nat, Nat.add(D.Dy.den(rx), D.Dy.den(ry)), Nat.add(dx, dy), Z.Nat.cong2(D.Dy.den(rx), dx, D.Dy.den(ry), dy, Den.neg(x), Den.neg(y))),
      Equal.trans(I.Int, I.Int.neg(s), I.Int.add(I.Int.neg(D.Int.sh(dy, nx)), I.Int.neg(D.Int.sh(dx, ny))), I.Int.add(D.Int.sh(D.Dy.den(ry), D.Dy.num(rx)), D.Int.sh(D.Dy.den(rx), D.Dy.num(ry))),
        Z.Int.neg_add(D.Int.sh(dy, nx), D.Int.sh(dx, ny)),
        Int.cong2(I.Int.neg(D.Int.sh(dy, nx)), D.Int.sh(D.Dy.den(ry), D.Dy.num(rx)), I.Int.neg(D.Int.sh(dx, ny)), D.Int.sh(D.Dy.den(rx), D.Dy.num(ry)),
          Equal.trans(I.Int, I.Int.neg(D.Int.sh(dy, nx)), D.Int.sh(dy, I.Int.neg(nx)), D.Int.sh(D.Dy.den(ry), D.Dy.num(rx)),
            Equal.sym(I.Int, D.Int.sh(dy, I.Int.neg(nx)), I.Int.neg(D.Int.sh(dy, nx)), Int.sh_neg(dy, nx)),
            Equal.sym(I.Int, D.Int.sh(D.Dy.den(ry), D.Dy.num(rx)), D.Int.sh(dy, I.Int.neg(nx)),
              Equal.trans(I.Int, D.Int.sh(D.Dy.den(ry), D.Dy.num(rx)), D.Int.sh(dy, D.Dy.num(rx)), D.Int.sh(dy, I.Int.neg(nx)),
                Equal.cong(Nat, I.Int, w => D.Int.sh(w, D.Dy.num(rx)), D.Dy.den(ry), dy, Den.neg(y)),
                Equal.cong(I.Int, I.Int, w => D.Int.sh(dy, w), D.Dy.num(rx), I.Int.neg(nx), Num.neg(x))))),
          Equal.trans(I.Int, I.Int.neg(D.Int.sh(dx, ny)), D.Int.sh(dx, I.Int.neg(ny)), D.Int.sh(D.Dy.den(rx), D.Dy.num(ry)),
            Equal.sym(I.Int, D.Int.sh(dx, I.Int.neg(ny)), I.Int.neg(D.Int.sh(dx, ny)), Int.sh_neg(dx, ny)),
            Equal.sym(I.Int, D.Int.sh(D.Dy.den(rx), D.Dy.num(ry)), D.Int.sh(dx, I.Int.neg(ny)),
              Equal.trans(I.Int, D.Int.sh(D.Dy.den(rx), D.Dy.num(ry)), D.Int.sh(dx, D.Dy.num(ry)), D.Int.sh(dx, I.Int.neg(ny)),
                Equal.cong(Nat, I.Int, w => D.Int.sh(w, D.Dy.num(ry)), D.Dy.den(rx), dx, Den.neg(x)),
                Equal.cong(I.Int, I.Int, w => D.Int.sh(dx, w), D.Dy.num(ry), I.Int.neg(ny), Num.neg(y)))))))))

def Dy.neg_mul_l(+x: D.Dy, +y: D.Dy) -> {D.Dy.mul(D.Dy.neg(x), y) == D.Dy.neg(D.Dy.mul(x, y)) : D.Dy}:
  +dx = D.Dy.den(x)
  +dy = D.Dy.den(y)
  +nx = D.Dy.num(x)
  +ny = D.Dy.num(y)
  +rx = D.Dy.neg(x)
  Equal.trans(D.Dy, D.Dy.mul(rx, y), D.Dy.of(Nat.add(dx, dy), I.Int.neg(I.Int.mul(nx, ny))), D.Dy.neg(D.Dy.mul(x, y)),
    Of.cong(Nat.add(D.Dy.den(rx), dy), Nat.add(dx, dy), I.Int.mul(D.Dy.num(rx), ny), I.Int.neg(I.Int.mul(nx, ny)),
      Equal.cong(Nat, Nat, w => Nat.add(w, dy), D.Dy.den(rx), dx, Den.neg(x)),
      Equal.trans(I.Int, I.Int.mul(D.Dy.num(rx), ny), I.Int.mul(I.Int.neg(nx), ny), I.Int.neg(I.Int.mul(nx, ny)),
        Equal.cong(I.Int, I.Int, w => I.Int.mul(w, ny), D.Dy.num(rx), I.Int.neg(nx), Num.neg(x)),
        Z.Int.neg_mul_l(nx, ny))),
    Equal.sym(D.Dy, D.Dy.neg(D.Dy.mul(x, y)), D.Dy.of(Nat.add(dx, dy), I.Int.neg(I.Int.mul(nx, ny))), Of.neg(Nat.add(dx, dy), I.Int.mul(nx, ny))))

# The nested ring laws
# --------------------
# Each is an Int identity modulo the values of the inner normal forms
# (Of.valP): multiplied by a power of two, lhs - rhs = sum of l_i r_i,
# checked by the normaliser (EQ.Rel.many), then the power cancels (Pc).

def V(i: Nat) -> N.Tm:
  N.TVar{i}

def Ml(a: N.Tm, b: N.Tm) -> N.Tm:
  N.TMul{a, b}

def Ad(a: N.Tm, b: N.Tm) -> N.Tm:
  N.TAdd{a, b}

def Ng(a: N.Tm) -> N.Tm:
  N.TNeg{a}

# a = b gives a - b = 0
def Rel.z(+a: I.Int, +b: I.Int, e: {a == b : I.Int}) -> {I.Int.add(a, I.Int.neg(b)) == I.IPos{0n} : I.Int}:
  Equal.trans(I.Int, I.Int.add(a, I.Int.neg(b)), I.Int.add(b, I.Int.neg(b)), I.IPos{0n}, Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.neg(b)), a, b, e), Z.Int.add_inv(b))

# Of.valP for a raw sum, with products: n (Pa Pb) = (ma Pb + mb Pa) Pn
def Val.sum(+ma: I.Int, +ea: Nat, +mb: I.Int, +eb: Nat)
  -> {I.Int.mul(D.Dy.num(D.Dy.of(Nat.add(ea, eb), I.Int.add(D.Int.sh(eb, ma), D.Int.sh(ea, mb)))), I.Int.mul(P(ea), P(eb)))
      == I.Int.mul(I.Int.add(I.Int.mul(ma, P(eb)), I.Int.mul(mb, P(ea))), P(D.Dy.den(D.Dy.of(Nat.add(ea, eb), I.Int.add(D.Int.sh(eb, ma), D.Int.sh(ea, mb)))))) : I.Int}:
  +s = I.Int.add(D.Int.sh(eb, ma), D.Int.sh(ea, mb))
  +o = D.Dy.of(Nat.add(ea, eb), s)
  Equal.trans(I.Int, I.Int.mul(D.Dy.num(o), I.Int.mul(P(ea), P(eb))), I.Int.mul(D.Dy.num(o), P(Nat.add(ea, eb))), I.Int.mul(I.Int.add(I.Int.mul(ma, P(eb)), I.Int.mul(mb, P(ea))), P(D.Dy.den(o))),
    Equal.cong(I.Int, I.Int, w => I.Int.mul(D.Dy.num(o), w), I.Int.mul(P(ea), P(eb)), P(Nat.add(ea, eb)), Equal.sym(I.Int, P(Nat.add(ea, eb)), I.Int.mul(P(ea), P(eb)), P.add(ea, eb))),
    Equal.trans(I.Int, I.Int.mul(D.Dy.num(o), P(Nat.add(ea, eb))), I.Int.mul(s, P(D.Dy.den(o))), I.Int.mul(I.Int.add(I.Int.mul(ma, P(eb)), I.Int.mul(mb, P(ea))), P(D.Dy.den(o))),
      Of.valP(Nat.add(ea, eb), s),
      Equal.cong(I.Int, I.Int, w => I.Int.mul(w, P(D.Dy.den(o))), s, I.Int.add(I.Int.mul(ma, P(eb)), I.Int.mul(mb, P(ea))), Cv.sum(ma, eb, mb, ea))))

# Of.valP for a raw product: n (Pa Pb) = (ma mb) Pn
def Val.prod(+ma: I.Int, +ea: Nat, +mb: I.Int, +eb: Nat)
  -> {I.Int.mul(D.Dy.num(D.Dy.of(Nat.add(ea, eb), I.Int.mul(ma, mb))), I.Int.mul(P(ea), P(eb)))
      == I.Int.mul(I.Int.mul(ma, mb), P(D.Dy.den(D.Dy.of(Nat.add(ea, eb), I.Int.mul(ma, mb))))) : I.Int}:
  +o = D.Dy.of(Nat.add(ea, eb), I.Int.mul(ma, mb))
  Equal.trans(I.Int, I.Int.mul(D.Dy.num(o), I.Int.mul(P(ea), P(eb))), I.Int.mul(D.Dy.num(o), P(Nat.add(ea, eb))), I.Int.mul(I.Int.mul(ma, mb), P(D.Dy.den(o))),
    Equal.cong(I.Int, I.Int, w => I.Int.mul(D.Dy.num(o), w), I.Int.mul(P(ea), P(eb)), P(Nat.add(ea, eb)), Equal.sym(I.Int, P(Nat.add(ea, eb)), I.Int.mul(P(ea), P(eb)), P.add(ea, eb))),
    Of.valP(Nat.add(ea, eb), I.Int.mul(ma, mb)))

def Dy.add_assoc(+x: D.Dy, +y: D.Dy, +z: D.Dy) -> {D.Dy.add(D.Dy.add(x, y), z) == D.Dy.add(x, D.Dy.add(y, z)) : D.Dy}:
  +dx = D.Dy.den(x)
  +dy = D.Dy.den(y)
  +dz = D.Dy.den(z)
  +nx = D.Dy.num(x)
  +ny = D.Dy.num(y)
  +nz = D.Dy.num(z)
  +u = D.Dy.add(x, y)
  +w = D.Dy.add(y, z)
  +nu = D.Dy.num(u)
  +du = D.Dy.den(u)
  +nw = D.Dy.num(w)
  +dw = D.Dy.den(w)
  +al = I.Int.add(D.Int.sh(dz, nu), D.Int.sh(du, nz))
  +ar = I.Int.add(D.Int.sh(dw, nx), D.Int.sh(dx, nw))
  +alp = I.Int.add(I.Int.mul(nu, P(dz)), I.Int.mul(nz, P(du)))
  +arp = I.Int.add(I.Int.mul(nx, P(dw)), I.Int.mul(nw, P(dx)))
  +env : List<&2, I.Int> = [nx, ny, nz, nu, nw, P(dx), P(dy), P(dz), P(du), P(dw)]
  +t = Ml(Ml(Ad(Ml(V(3n), V(7n)), Ml(V(2n), V(8n))), Ml(V(5n), V(9n))), V(6n))
  +v = Ml(Ml(Ad(Ml(V(0n), V(9n)), Ml(V(4n), V(5n))), Ml(V(8n), V(7n))), V(6n))
  +r1 = Ad(Ml(V(3n), Ml(V(5n), V(6n))), Ng(Ml(Ad(Ml(V(0n), V(6n)), Ml(V(1n), V(5n))), V(8n))))
  +r2 = Ad(Ml(V(4n), Ml(V(6n), V(7n))), Ng(Ml(Ad(Ml(V(1n), V(7n)), Ml(V(2n), V(6n))), V(9n))))
  +z1 = Rel.z(I.Int.mul(nu, I.Int.mul(P(dx), P(dy))), I.Int.mul(I.Int.add(I.Int.mul(nx, P(dy)), I.Int.mul(ny, P(dx))), P(du)), Val.sum(nx, dx, ny, dy))
  +z2 = Rel.z(I.Int.mul(nw, I.Int.mul(P(dy), P(dz))), I.Int.mul(I.Int.add(I.Int.mul(ny, P(dz)), I.Int.mul(nz, P(dy))), P(dw)), Val.sum(ny, dy, nz, dz))
  +e = EQ.Rel.many(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg,
    env, t, v, [Ml(V(7n), V(9n)), Ng(Ml(V(5n), V(8n)))], [r1, r2], {==}, (z1, (z2, Unit{})))
  +c = Pc(dy, I.Int.mul(alp, I.Int.mul(P(dx), P(dw))), I.Int.mul(arp, I.Int.mul(P(du), P(dz))), e)
  Of.eqvP(Nat.add(du, dz), Nat.add(dx, dw), al, ar,
    Equal.trans(I.Int, I.Int.mul(al, P(Nat.add(dx, dw))), I.Int.mul(alp, I.Int.mul(P(dx), P(dw))), I.Int.mul(ar, P(Nat.add(du, dz))),
      Int.mcong2(al, alp, P(Nat.add(dx, dw)), I.Int.mul(P(dx), P(dw)), Cv.sum(nu, dz, nz, du), P.add(dx, dw)),
      Equal.trans(I.Int, I.Int.mul(alp, I.Int.mul(P(dx), P(dw))), I.Int.mul(arp, I.Int.mul(P(du), P(dz))), I.Int.mul(ar, P(Nat.add(du, dz))), c,
        Equal.sym(I.Int, I.Int.mul(ar, P(Nat.add(du, dz))), I.Int.mul(arp, I.Int.mul(P(du), P(dz))),
          Int.mcong2(ar, arp, P(Nat.add(du, dz)), I.Int.mul(P(du), P(dz)), Cv.sum(nx, dw, nw, dx), P.add(du, dz))))))

def Dy.mul_assoc(+x: D.Dy, +y: D.Dy, +z: D.Dy) -> {D.Dy.mul(D.Dy.mul(x, y), z) == D.Dy.mul(x, D.Dy.mul(y, z)) : D.Dy}:
  +dx = D.Dy.den(x)
  +dy = D.Dy.den(y)
  +dz = D.Dy.den(z)
  +nx = D.Dy.num(x)
  +ny = D.Dy.num(y)
  +nz = D.Dy.num(z)
  +u = D.Dy.mul(x, y)
  +w = D.Dy.mul(y, z)
  +nu = D.Dy.num(u)
  +du = D.Dy.den(u)
  +nw = D.Dy.num(w)
  +dw = D.Dy.den(w)
  +al = I.Int.mul(nu, nz)
  +ar = I.Int.mul(nx, nw)
  +env : List<&2, I.Int> = [nx, ny, nz, nu, nw, P(dx), P(dy), P(dz), P(du), P(dw)]
  +t = Ml(Ml(Ml(V(3n), V(2n)), Ml(V(5n), V(9n))), V(6n))
  +v = Ml(Ml(Ml(V(0n), V(4n)), Ml(V(8n), V(7n))), V(6n))
  +r1 = Ad(Ml(V(3n), Ml(V(5n), V(6n))), Ng(Ml(Ml(V(0n), V(1n)), V(8n))))
  +r2 = Ad(Ml(V(4n), Ml(V(6n), V(7n))), Ng(Ml(Ml(V(1n), V(2n)), V(9n))))
  +z1 = Rel.z(I.Int.mul(nu, I.Int.mul(P(dx), P(dy))), I.Int.mul(I.Int.mul(nx, ny), P(du)), Val.prod(nx, dx, ny, dy))
  +z2 = Rel.z(I.Int.mul(nw, I.Int.mul(P(dy), P(dz))), I.Int.mul(I.Int.mul(ny, nz), P(dw)), Val.prod(ny, dy, nz, dz))
  +e = EQ.Rel.many(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg,
    env, t, v, [Ml(V(2n), V(9n)), Ng(Ml(V(0n), V(8n)))], [r1, r2], {==}, (z1, (z2, Unit{})))
  +c = Pc(dy, I.Int.mul(al, I.Int.mul(P(dx), P(dw))), I.Int.mul(ar, I.Int.mul(P(du), P(dz))), e)
  Of.eqvP(Nat.add(du, dz), Nat.add(dx, dw), al, ar,
    Equal.trans(I.Int, I.Int.mul(al, P(Nat.add(dx, dw))), I.Int.mul(al, I.Int.mul(P(dx), P(dw))), I.Int.mul(ar, P(Nat.add(du, dz))),
      Equal.cong(I.Int, I.Int, w2 => I.Int.mul(al, w2), P(Nat.add(dx, dw)), I.Int.mul(P(dx), P(dw)), P.add(dx, dw)),
      Equal.trans(I.Int, I.Int.mul(al, I.Int.mul(P(dx), P(dw))), I.Int.mul(ar, I.Int.mul(P(du), P(dz))), I.Int.mul(ar, P(Nat.add(du, dz))), c,
        Equal.cong(I.Int, I.Int, w2 => I.Int.mul(ar, w2), I.Int.mul(P(du), P(dz)), P(Nat.add(du, dz)), Equal.sym(I.Int, P(Nat.add(du, dz)), I.Int.mul(P(du), P(dz)), P.add(du, dz))))))

def Dy.dist_l(+x: D.Dy, +y: D.Dy, +z: D.Dy) -> {D.Dy.mul(x, D.Dy.add(y, z)) == D.Dy.add(D.Dy.mul(x, y), D.Dy.mul(x, z)) : D.Dy}:
  +dx = D.Dy.den(x)
  +dy = D.Dy.den(y)
  +dz = D.Dy.den(z)
  +nx = D.Dy.num(x)
  +ny = D.Dy.num(y)
  +nz = D.Dy.num(z)
  +w = D.Dy.add(y, z)
  +a = D.Dy.mul(x, y)
  +b = D.Dy.mul(x, z)
  +nw = D.Dy.num(w)
  +dw = D.Dy.den(w)
  +na = D.Dy.num(a)
  +da = D.Dy.den(a)
  +nb = D.Dy.num(b)
  +db = D.Dy.den(b)
  +al = I.Int.mul(nx, nw)
  +ar = I.Int.add(D.Int.sh(db, na), D.Int.sh(da, nb))
  +arp = I.Int.add(I.Int.mul(na, P(db)), I.Int.mul(nb, P(da)))
  +k = Nat.add(Nat.add(dx, dy), dz)
  +pk = I.Int.mul(I.Int.mul(P(dx), P(dy)), P(dz))
  +env : List<&2, I.Int> = [nx, ny, nz, nw, na, nb, P(dx), P(dy), P(dz), P(dw), P(da), P(db)]
  +t = Ml(Ml(Ml(V(0n), V(3n)), Ml(V(10n), V(11n))), Ml(Ml(V(6n), V(7n)), V(8n)))
  +v = Ml(Ml(Ad(Ml(V(4n), V(11n)), Ml(V(5n), V(10n))), Ml(V(6n), V(9n))), Ml(Ml(V(6n), V(7n)), V(8n)))
  +rw = Ad(Ml(V(3n), Ml(V(7n), V(8n))), Ng(Ml(Ad(Ml(V(1n), V(8n)), Ml(V(2n), V(7n))), V(9n))))
  +ra = Ad(Ml(V(4n), Ml(V(6n), V(7n))), Ng(Ml(Ml(V(0n), V(1n)), V(10n))))
  +rb = Ad(Ml(V(5n), Ml(V(6n), V(8n))), Ng(Ml(Ml(V(0n), V(2n)), V(11n))))
  +zw = Rel.z(I.Int.mul(nw, I.Int.mul(P(dy), P(dz))), I.Int.mul(I.Int.add(I.Int.mul(ny, P(dz)), I.Int.mul(nz, P(dy))), P(dw)), Val.sum(ny, dy, nz, dz))
  +za = Rel.z(I.Int.mul(na, I.Int.mul(P(dx), P(dy))), I.Int.mul(I.Int.mul(nx, ny), P(da)), Val.prod(nx, dx, ny, dy))
  +zb = Rel.z(I.Int.mul(nb, I.Int.mul(P(dx), P(dz))), I.Int.mul(I.Int.mul(nx, nz), P(db)), Val.prod(nx, dx, nz, dz))
  +e = EQ.Rel.many(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg,
    env, t, v, [Ml(Ml(Ml(V(0n), V(10n)), V(11n)), V(6n)), Ng(Ml(Ml(Ml(V(11n), V(6n)), V(9n)), V(8n))), Ng(Ml(Ml(Ml(V(10n), V(6n)), V(9n)), V(7n)))], [rw, ra, rb], {==}, (zw, (za, (zb, Unit{}))))
  +pke = Equal.trans(I.Int, pk, I.Int.mul(P(Nat.add(dx, dy)), P(dz)), P(k),
    Equal.cong(I.Int, I.Int, w2 => I.Int.mul(w2, P(dz)), I.Int.mul(P(dx), P(dy)), P(Nat.add(dx, dy)), Equal.sym(I.Int, P(Nat.add(dx, dy)), I.Int.mul(P(dx), P(dy)), P.add(dx, dy))),
    Equal.sym(I.Int, P(k), I.Int.mul(P(Nat.add(dx, dy)), P(dz)), P.add(Nat.add(dx, dy), dz)))
  +lx = I.Int.mul(al, I.Int.mul(P(da), P(db)))
  +rx = I.Int.mul(arp, I.Int.mul(P(dx), P(dw)))
  +e2 = Equal.trans(I.Int, I.Int.mul(lx, P(k)), I.Int.mul(lx, pk), I.Int.mul(rx, P(k)),
    Equal.cong(I.Int, I.Int, w2 => I.Int.mul(lx, w2), P(k), pk, Equal.sym(I.Int, pk, P(k), pke)),
    Equal.trans(I.Int, I.Int.mul(lx, pk), I.Int.mul(rx, pk), I.Int.mul(rx, P(k)), e,
      Equal.cong(I.Int, I.Int, w2 => I.Int.mul(rx, w2), pk, P(k), pke)))
  +c = Pc(k, lx, rx, e2)
  Of.eqvP(Nat.add(dx, dw), Nat.add(da, db), al, ar,
    Equal.trans(I.Int, I.Int.mul(al, P(Nat.add(da, db))), lx, I.Int.mul(ar, P(Nat.add(dx, dw))),
      Equal.cong(I.Int, I.Int, w2 => I.Int.mul(al, w2), P(Nat.add(da, db)), I.Int.mul(P(da), P(db)), P.add(da, db)),
      Equal.trans(I.Int, lx, rx, I.Int.mul(ar, P(Nat.add(dx, dw))), c,
        Equal.sym(I.Int, I.Int.mul(ar, P(Nat.add(dx, dw))), rx,
          Int.mcong2(ar, arp, P(Nat.add(dx, dw)), I.Int.mul(P(dx), P(dw)), Cv.sum(na, db, nb, da), P.add(dx, dw))))))

# The order
# ---------

def Num.abs(+x: D.Dy) -> {D.Dy.num(D.Dy.abs(x)) == I.Int.abs(D.Dy.num(x)) : I.Int}:
  match x:
    case D.DInt{m}:
      {==}
    case D.DFrac{s, k, e}:
      match s:
        case True{}:
          {==}
        case False{}:
          {==}

def Den.abs(+x: D.Dy) -> {D.Dy.den(D.Dy.abs(x)) == D.Dy.den(x) : Nat}:
  match x:
    case D.DInt{m}:
      {==}
    case D.DFrac{s, k, e}:
      {==}

def Pos.num(+x: D.Dy) -> {D.Dy.pos(x) == I.Int.pos(D.Dy.num(x)) : Bool}:
  match x:
    case D.DInt{m}:
      {==}
    case D.DFrac{s, k, e}:
      match s:
        case True{}:
          {==}
        case False{}:
          {==}

def Pos.p(+a: I.Int, +k: Nat) -> {I.Int.pos(I.Int.mul(a, P(k))) == I.Int.pos(a) : Bool}:
  Equal.trans(Bool, I.Int.pos(I.Int.mul(a, P(k))), I.Int.pos(D.Int.sh(k, a)), I.Int.pos(a),
    Equal.cong(I.Int, Bool, w => I.Int.pos(w), I.Int.mul(a, P(k)), D.Int.sh(k, a), Equal.sym(I.Int, D.Int.sh(k, a), I.Int.mul(a, P(k)), Sh.p(k, a))),
    Int.pos_sh(k, a))

# the sign of a normal form is its numerator's
def Pos.of(+e: Nat, +m: I.Int) -> {D.Dy.pos(D.Dy.of(e, m)) == I.Int.pos(m) : Bool}:
  +o = D.Dy.of(e, m)
  Equal.trans(Bool, D.Dy.pos(o), I.Int.pos(D.Dy.num(o)), I.Int.pos(m), Pos.num(o),
    Equal.trans(Bool, I.Int.pos(D.Dy.num(o)), I.Int.pos(I.Int.mul(D.Dy.num(o), P(e))), I.Int.pos(m),
      Equal.sym(Bool, I.Int.pos(I.Int.mul(D.Dy.num(o), P(e))), I.Int.pos(D.Dy.num(o)), Pos.p(D.Dy.num(o), e)),
      Equal.trans(Bool, I.Int.pos(I.Int.mul(D.Dy.num(o), P(e))), I.Int.pos(I.Int.mul(m, P(D.Dy.den(o)))), I.Int.pos(m),
        Equal.cong(I.Int, Bool, w => I.Int.pos(w), I.Int.mul(D.Dy.num(o), P(e)), I.Int.mul(m, P(D.Dy.den(o))), Of.valP(e, m)),
        Pos.p(m, D.Dy.den(o)))))

def Pos.rw(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {b == True{} : Bool}) -> {a == True{} : Bool}:
  Equal.trans(Bool, a, b, True{}, e, h)

def Dy.pos_add.go(+x: D.Dy, +y: D.Dy, px: {D.Dy.pos(x) == True{} : Bool}, py: {D.Dy.pos(y) == True{} : Bool}) -> {D.Dy.pos(D.Dy.add(x, y)) == True{} : Bool}:
  +a = D.Int.sh(D.Dy.den(y), D.Dy.num(x))
  +b = D.Int.sh(D.Dy.den(x), D.Dy.num(y))
  ha = Pos.rw(I.Int.pos(a), D.Dy.pos(x), Equal.trans(Bool, I.Int.pos(a), I.Int.pos(D.Dy.num(x)), D.Dy.pos(x), Int.pos_sh(D.Dy.den(y), D.Dy.num(x)), Equal.sym(Bool, D.Dy.pos(x), I.Int.pos(D.Dy.num(x)), Pos.num(x))), px)
  hb = Pos.rw(I.Int.pos(b), D.Dy.pos(y), Equal.trans(Bool, I.Int.pos(b), I.Int.pos(D.Dy.num(y)), D.Dy.pos(y), Int.pos_sh(D.Dy.den(x), D.Dy.num(y)), Equal.sym(Bool, D.Dy.pos(y), I.Int.pos(D.Dy.num(y)), Pos.num(y))), py)
  Pos.rw(D.Dy.pos(D.Dy.add(x, y)), I.Int.pos(I.Int.add(a, b)), Pos.of(Nat.add(D.Dy.den(x), D.Dy.den(y)), I.Int.add(a, b)), Z.Int.pos_add(a, b)(ha)(hb))

def Dy.pos_add(x: D.Dy, y: D.Dy) -> {D.Dy.pos(x) == True{} : Bool} -> {D.Dy.pos(y) == True{} : Bool} -> {D.Dy.pos(D.Dy.add(x, y)) == True{} : Bool}:
  px => py => Dy.pos_add.go(x, y, px, py)

def Dy.pos_mul.go(+x: D.Dy, +y: D.Dy, px: {D.Dy.pos(x) == True{} : Bool}, py: {D.Dy.pos(y) == True{} : Bool}) -> {D.Dy.pos(D.Dy.mul(x, y)) == True{} : Bool}:
  ha = Pos.rw(I.Int.pos(D.Dy.num(x)), D.Dy.pos(x), Equal.sym(Bool, D.Dy.pos(x), I.Int.pos(D.Dy.num(x)), Pos.num(x)), px)
  hb = Pos.rw(I.Int.pos(D.Dy.num(y)), D.Dy.pos(y), Equal.sym(Bool, D.Dy.pos(y), I.Int.pos(D.Dy.num(y)), Pos.num(y)), py)
  Pos.rw(D.Dy.pos(D.Dy.mul(x, y)), I.Int.pos(I.Int.mul(D.Dy.num(x), D.Dy.num(y))), Pos.of(Nat.add(D.Dy.den(x), D.Dy.den(y)), I.Int.mul(D.Dy.num(x), D.Dy.num(y))), Z.Int.pos_mul(D.Dy.num(x), D.Dy.num(y))(ha)(hb))

def Dy.pos_mul(x: D.Dy, y: D.Dy) -> {D.Dy.pos(x) == True{} : Bool} -> {D.Dy.pos(y) == True{} : Bool} -> {D.Dy.pos(D.Dy.mul(x, y)) == True{} : Bool}:
  px => py => Dy.pos_mul.go(x, y, px, py)

def Dy.pos_abs(x: D.Dy) -> {D.Dy.pos(D.Dy.abs(x)) == True{} : Bool}:
  match x:
    case D.DInt{m}:
      Z.Int.pos_abs(m)
    case D.DFrac{s, k, e}:
      {==}

def Dy.abs_neg(x: D.Dy) -> {D.Dy.abs(D.Dy.neg(x)) == D.Dy.abs(x) : D.Dy}:
  match x:
    case D.DInt{+m}:
      Equal.cong(I.Int, D.Dy, w => D.DInt{w}, I.Int.abs(I.Int.neg(m)), I.Int.abs(m), Z.Int.abs_neg(m))
    case D.DFrac{s, k, e}:
      {==}

def Abs.P(+k: Nat) -> {I.Int.abs(P(k)) == P(k) : I.Int}:
  Int.abs_sh(k, I.IPos{1n})

# |.| passes through the normal form
def Abs.of(+e: Nat, +m: I.Int) -> {D.Dy.abs(D.Dy.of(e, m)) == D.Dy.of(e, I.Int.abs(m)) : D.Dy}:
  +o = D.Dy.of(e, m)
  +ao = D.Dy.abs(o)
  +n = D.Dy.num(o)
  +d = D.Dy.den(o)
  +h = Equal.trans(I.Int, I.Int.mul(I.Int.abs(n), P(e)), I.Int.abs(I.Int.mul(n, P(e))), I.Int.mul(I.Int.abs(m), P(d)),
    Equal.trans(I.Int, I.Int.mul(I.Int.abs(n), P(e)), I.Int.mul(I.Int.abs(n), I.Int.abs(P(e))), I.Int.abs(I.Int.mul(n, P(e))),
      Equal.cong(I.Int, I.Int, w => I.Int.mul(I.Int.abs(n), w), P(e), I.Int.abs(P(e)), Equal.sym(I.Int, I.Int.abs(P(e)), P(e), Abs.P(e))),
      Equal.sym(I.Int, I.Int.abs(I.Int.mul(n, P(e))), I.Int.mul(I.Int.abs(n), I.Int.abs(P(e))), Z.Int.abs_mul(n, P(e)))),
    Equal.trans(I.Int, I.Int.abs(I.Int.mul(n, P(e))), I.Int.abs(I.Int.mul(m, P(d))), I.Int.mul(I.Int.abs(m), P(d)),
      Equal.cong(I.Int, I.Int, w => I.Int.abs(w), I.Int.mul(n, P(e)), I.Int.mul(m, P(d)), Of.valP(e, m)),
      Equal.trans(I.Int, I.Int.abs(I.Int.mul(m, P(d))), I.Int.mul(I.Int.abs(m), I.Int.abs(P(d))), I.Int.mul(I.Int.abs(m), P(d)),
        Z.Int.abs_mul(m, P(d)),
        Equal.cong(I.Int, I.Int, w => I.Int.mul(I.Int.abs(m), w), I.Int.abs(P(d)), P(d), Abs.P(d)))))
  Equal.trans(D.Dy, ao, D.Dy.of(D.Dy.den(ao), D.Dy.num(ao)), D.Dy.of(e, I.Int.abs(m)), Equal.sym(D.Dy, D.Dy.of(D.Dy.den(ao), D.Dy.num(ao)), ao, Of.self(ao)),
    Equal.trans(D.Dy, D.Dy.of(D.Dy.den(ao), D.Dy.num(ao)), D.Dy.of(d, I.Int.abs(n)), D.Dy.of(e, I.Int.abs(m)),
      Of.cong(D.Dy.den(ao), d, D.Dy.num(ao), I.Int.abs(n), Den.abs(o), Num.abs(o)),
      Of.eqvP(d, e, I.Int.abs(n), I.Int.abs(m), h)))

def Dy.abs_mul.go(+x: D.Dy, +y: D.Dy) -> {D.Dy.abs(D.Dy.mul(x, y)) == D.Dy.mul(D.Dy.abs(x), D.Dy.abs(y)) : D.Dy}:
  +e = Nat.add(D.Dy.den(x), D.Dy.den(y))
  +nx = D.Dy.num(x)
  +ny = D.Dy.num(y)
  Equal.trans(D.Dy, D.Dy.abs(D.Dy.of(e, I.Int.mul(nx, ny))), D.Dy.of(e, I.Int.abs(I.Int.mul(nx, ny))), D.Dy.mul(D.Dy.abs(x), D.Dy.abs(y)),
    Abs.of(e, I.Int.mul(nx, ny)),
    Of.cong(e, Nat.add(D.Dy.den(D.Dy.abs(x)), D.Dy.den(D.Dy.abs(y))), I.Int.abs(I.Int.mul(nx, ny)), I.Int.mul(D.Dy.num(D.Dy.abs(x)), D.Dy.num(D.Dy.abs(y))),
      Equal.sym(Nat, Nat.add(D.Dy.den(D.Dy.abs(x)), D.Dy.den(D.Dy.abs(y))), e, Z.Nat.cong2(D.Dy.den(D.Dy.abs(x)), D.Dy.den(x), D.Dy.den(D.Dy.abs(y)), D.Dy.den(y), Den.abs(x), Den.abs(y))),
      Equal.trans(I.Int, I.Int.abs(I.Int.mul(nx, ny)), I.Int.mul(I.Int.abs(nx), I.Int.abs(ny)), I.Int.mul(D.Dy.num(D.Dy.abs(x)), D.Dy.num(D.Dy.abs(y))),
        Z.Int.abs_mul(nx, ny),
        Equal.sym(I.Int, I.Int.mul(D.Dy.num(D.Dy.abs(x)), D.Dy.num(D.Dy.abs(y))), I.Int.mul(I.Int.abs(nx), I.Int.abs(ny)), Int.mcong2(D.Dy.num(D.Dy.abs(x)), I.Int.abs(nx), D.Dy.num(D.Dy.abs(y)), I.Int.abs(ny), Num.abs(x), Num.abs(y))))))

def Dy.abs_mul(x: D.Dy, y: D.Dy) -> {D.Dy.abs(D.Dy.mul(x, y)) == D.Dy.mul(D.Dy.abs(x), D.Dy.abs(y)) : D.Dy}:
  Dy.abs_mul.go(x, y)

# A / 2^e + B / 2^e = (A + B) / 2^e
def Add.of(+e: Nat, +a: I.Int, +b: I.Int) -> {D.Dy.add(D.Dy.of(e, a), D.Dy.of(e, b)) == D.Dy.of(e, I.Int.add(a, b)) : D.Dy}:
  +u = D.Dy.of(e, a)
  +v = D.Dy.of(e, b)
  +nu = D.Dy.num(u)
  +du = D.Dy.den(u)
  +nv = D.Dy.num(v)
  +dv = D.Dy.den(v)
  +x = I.Int.add(D.Int.sh(dv, nu), D.Int.sh(du, nv))
  +xp = I.Int.add(I.Int.mul(nu, P(dv)), I.Int.mul(nv, P(du)))
  +env : List<&2, I.Int> = [a, b, nu, nv, P(e), P(du), P(dv)]
  +t = Ml(Ad(Ml(V(2n), V(6n)), Ml(V(3n), V(5n))), V(4n))
  +w = Ml(Ad(V(0n), V(1n)), Ml(V(5n), V(6n)))
  +r1 = Ad(Ml(V(2n), V(4n)), Ng(Ml(V(0n), V(5n))))
  +r2 = Ad(Ml(V(3n), V(4n)), Ng(Ml(V(1n), V(6n))))
  +z1 = Rel.z(I.Int.mul(nu, P(e)), I.Int.mul(a, P(du)), Of.valP(e, a))
  +z2 = Rel.z(I.Int.mul(nv, P(e)), I.Int.mul(b, P(dv)), Of.valP(e, b))
  +h = EQ.Rel.many(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg,
    env, t, w, [V(6n), V(5n)], [r1, r2], {==}, (z1, (z2, Unit{})))
  Of.eqvP(Nat.add(du, dv), e, x, I.Int.add(a, b),
    Equal.trans(I.Int, I.Int.mul(x, P(e)), I.Int.mul(xp, P(e)), I.Int.mul(I.Int.add(a, b), P(Nat.add(du, dv))),
      Equal.cong(I.Int, I.Int, w2 => I.Int.mul(w2, P(e)), x, xp, Cv.sum(nu, dv, nv, du)),
      Equal.trans(I.Int, I.Int.mul(xp, P(e)), I.Int.mul(I.Int.add(a, b), I.Int.mul(P(du), P(dv))), I.Int.mul(I.Int.add(a, b), P(Nat.add(du, dv))), h,
        Equal.cong(I.Int, I.Int, w2 => I.Int.mul(I.Int.add(a, b), w2), I.Int.mul(P(du), P(dv)), P(Nat.add(du, dv)), Equal.sym(I.Int, P(Nat.add(du, dv)), I.Int.mul(P(du), P(dv)), P.add(du, dv))))))

def Dy.cong2(-u1: D.Dy, -u2: D.Dy, -v1: D.Dy, -v2: D.Dy, e1: {u1 == u2 : D.Dy}, e2: {v1 == v2 : D.Dy}) -> {D.Dy.add(u1, v1) == D.Dy.add(u2, v2) : D.Dy}:
  %e1 : {D.Dy.add(u1, v1) == D.Dy.add(_, v2) : D.Dy}
  %e2 : {D.Dy.add(u1, v1) == D.Dy.add(u1, _) : D.Dy}
  {==}

# |x| = |num x| 2^k / 2^(den x + k)
def Abs.at(+x: D.Dy, +k: Nat) -> {D.Dy.abs(x) == D.Dy.of(Nat.add(D.Dy.den(x), k), D.Int.sh(k, I.Int.abs(D.Dy.num(x)))) : D.Dy}:
  +ax = D.Dy.abs(x)
  Equal.trans(D.Dy, ax, D.Dy.of(D.Dy.den(x), I.Int.abs(D.Dy.num(x))), D.Dy.of(Nat.add(D.Dy.den(x), k), D.Int.sh(k, I.Int.abs(D.Dy.num(x)))),
    Equal.trans(D.Dy, ax, D.Dy.of(D.Dy.den(ax), D.Dy.num(ax)), D.Dy.of(D.Dy.den(x), I.Int.abs(D.Dy.num(x))),
      Equal.sym(D.Dy, D.Dy.of(D.Dy.den(ax), D.Dy.num(ax)), ax, Of.self(ax)),
      Of.cong(D.Dy.den(ax), D.Dy.den(x), D.Dy.num(ax), I.Int.abs(D.Dy.num(x)), Den.abs(x), Num.abs(x))),
    Equal.sym(D.Dy, D.Dy.of(Nat.add(D.Dy.den(x), k), D.Int.sh(k, I.Int.abs(D.Dy.num(x)))), D.Dy.of(D.Dy.den(x), I.Int.abs(D.Dy.num(x))), Of.shift(k, D.Dy.den(x), I.Int.abs(D.Dy.num(x)))))

# |x + y| <= |x| + |y|
def Dy.tri.go(+x: D.Dy, +y: D.Dy) -> {D.Dy.pos(D.Dy.add(D.Dy.add(D.Dy.abs(x), D.Dy.abs(y)), D.Dy.neg(D.Dy.abs(D.Dy.add(x, y))))) == True{} : Bool}:
  +dx = D.Dy.den(x)
  +dy = D.Dy.den(y)
  +e = Nat.add(dx, dy)
  +a = D.Int.sh(dy, D.Dy.num(x))
  +b = D.Int.sh(dx, D.Dy.num(y))
  +ap = D.Int.sh(dy, I.Int.abs(D.Dy.num(x)))
  +bp = D.Int.sh(dx, I.Int.abs(D.Dy.num(y)))
  +s = I.Int.add(a, b)
  +zz = I.Int.add(I.Int.add(ap, bp), I.Int.neg(I.Int.abs(s)))
  # |x| + |y| = (ap + bp) / 2^e
  +eay = Equal.trans(D.Dy, D.Dy.abs(y), D.Dy.of(Nat.add(dy, dx), bp), D.Dy.of(e, bp), Abs.at(y, dx),
    Equal.cong(Nat, D.Dy, w => D.Dy.of(w, bp), Nat.add(dy, dx), e, NL.Nat.add_comm(dy, dx)))
  +esum = Equal.trans(D.Dy, D.Dy.add(D.Dy.abs(x), D.Dy.abs(y)), D.Dy.add(D.Dy.of(e, ap), D.Dy.of(e, bp)), D.Dy.of(e, I.Int.add(ap, bp)),
    Dy.cong2(D.Dy.abs(x), D.Dy.of(e, ap), D.Dy.abs(y), D.Dy.of(e, bp), Abs.at(x, dy), eay),
    Add.of(e, ap, bp))
  # -|x + y| = -|s| / 2^e
  +eneg = Equal.trans(D.Dy, D.Dy.neg(D.Dy.abs(D.Dy.of(e, s))), D.Dy.neg(D.Dy.of(e, I.Int.abs(s))), D.Dy.of(e, I.Int.neg(I.Int.abs(s))),
    Equal.cong(D.Dy, D.Dy, w => D.Dy.neg(w), D.Dy.abs(D.Dy.of(e, s)), D.Dy.of(e, I.Int.abs(s)), Abs.of(e, s)),
    Of.neg(e, I.Int.abs(s)))
  +eall = Equal.trans(D.Dy, D.Dy.add(D.Dy.add(D.Dy.abs(x), D.Dy.abs(y)), D.Dy.neg(D.Dy.abs(D.Dy.add(x, y)))), D.Dy.add(D.Dy.of(e, I.Int.add(ap, bp)), D.Dy.of(e, I.Int.neg(I.Int.abs(s)))), D.Dy.of(e, zz),
    Dy.cong2(D.Dy.add(D.Dy.abs(x), D.Dy.abs(y)), D.Dy.of(e, I.Int.add(ap, bp)), D.Dy.neg(D.Dy.abs(D.Dy.add(x, y))), D.Dy.of(e, I.Int.neg(I.Int.abs(s))), esum, eneg),
    Add.of(e, I.Int.add(ap, bp), I.Int.neg(I.Int.abs(s))))
  # ap = |a|, bp = |b|
  +ez = Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.neg(I.Int.abs(s))), I.Int.add(ap, bp), I.Int.add(I.Int.abs(a), I.Int.abs(b)),
    Int.cong2(ap, I.Int.abs(a), bp, I.Int.abs(b), Equal.sym(I.Int, I.Int.abs(a), ap, Int.abs_sh(dy, D.Dy.num(x))), Equal.sym(I.Int, I.Int.abs(b), bp, Int.abs_sh(dx, D.Dy.num(y)))))
  Pos.rw(D.Dy.pos(D.Dy.add(D.Dy.add(D.Dy.abs(x), D.Dy.abs(y)), D.Dy.neg(D.Dy.abs(D.Dy.add(x, y))))), I.Int.pos(zz),
    Equal.trans(Bool, D.Dy.pos(D.Dy.add(D.Dy.add(D.Dy.abs(x), D.Dy.abs(y)), D.Dy.neg(D.Dy.abs(D.Dy.add(x, y))))), D.Dy.pos(D.Dy.of(e, zz)), I.Int.pos(zz),
      Equal.cong(D.Dy, Bool, w => D.Dy.pos(w), D.Dy.add(D.Dy.add(D.Dy.abs(x), D.Dy.abs(y)), D.Dy.neg(D.Dy.abs(D.Dy.add(x, y)))), D.Dy.of(e, zz), eall),
      Pos.of(e, zz)),
    Pos.rw(I.Int.pos(zz), I.Int.pos(I.Int.add(I.Int.add(I.Int.abs(a), I.Int.abs(b)), I.Int.neg(I.Int.abs(s)))),
      Equal.cong(I.Int, Bool, w => I.Int.pos(w), zz, I.Int.add(I.Int.add(I.Int.abs(a), I.Int.abs(b)), I.Int.neg(I.Int.abs(s))), ez),
      Z.Int.tri(a, b)))

def Dy.tri(x: D.Dy, y: D.Dy) -> {D.Dy.pos(D.Dy.add(D.Dy.add(D.Dy.abs(x), D.Dy.abs(y)), D.Dy.neg(D.Dy.abs(D.Dy.add(x, y))))) == True{} : Bool}:
  Dy.tri.go(x, y)

# The instance: plain parameters, the types src/ring.bend and src/err.bend name
# ------------

def Dy.r.add_assoc(a: D.Dy, b: D.Dy, c: D.Dy) -> {D.Dy.add(D.Dy.add(a, b), c) == D.Dy.add(a, D.Dy.add(b, c)) : D.Dy}:
  Dy.add_assoc(a, b, c)

def Dy.r.add_comm(a: D.Dy, b: D.Dy) -> {D.Dy.add(a, b) == D.Dy.add(b, a) : D.Dy}:
  Dy.add_comm(a, b)

def Dy.r.zero_l(a: D.Dy) -> {D.Dy.add(D.Dy.zero(), a) == a : D.Dy}:
  Dy.zero_l(a)

def Dy.r.add_inv(a: D.Dy) -> {D.Dy.add(a, D.Dy.neg(a)) == D.Dy.zero() : D.Dy}:
  Dy.add_inv(a)

def Dy.r.mul_assoc(a: D.Dy, b: D.Dy, c: D.Dy) -> {D.Dy.mul(D.Dy.mul(a, b), c) == D.Dy.mul(a, D.Dy.mul(b, c)) : D.Dy}:
  Dy.mul_assoc(a, b, c)

def Dy.r.mul_comm(a: D.Dy, b: D.Dy) -> {D.Dy.mul(a, b) == D.Dy.mul(b, a) : D.Dy}:
  Dy.mul_comm(a, b)

def Dy.r.unit_r(a: D.Dy) -> {D.Dy.mul(a, D.Dy.one()) == a : D.Dy}:
  Dy.unit_r(a)

def Dy.r.dist_l(a: D.Dy, b: D.Dy, c: D.Dy) -> {D.Dy.mul(a, D.Dy.add(b, c)) == D.Dy.add(D.Dy.mul(a, b), D.Dy.mul(a, c)) : D.Dy}:
  Dy.dist_l(a, b, c)

def Dy.r.neg_add(a: D.Dy, b: D.Dy) -> {D.Dy.neg(D.Dy.add(a, b)) == D.Dy.add(D.Dy.neg(a), D.Dy.neg(b)) : D.Dy}:
  Dy.neg_add(a, b)

def Dy.r.neg_mul_l(a: D.Dy, b: D.Dy) -> {D.Dy.mul(D.Dy.neg(a), b) == D.Dy.neg(D.Dy.mul(a, b)) : D.Dy}:
  Dy.neg_mul_l(a, b)

def Dy.r.neg_neg(a: D.Dy) -> {D.Dy.neg(D.Dy.neg(a)) == a : D.Dy}:
  Dy.neg_neg(a)
