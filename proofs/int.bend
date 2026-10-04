# Int is an ordered commutative ring: the ring laws src/ring.bend names,
# and the order laws src/err.bend assumes, for src/int.bend.
#
# Method: every integer is a difference of naturals. P(a) - Q(a) = a, with
# (P, Q) = (n, 0) for IPos{n} and (0, n + 1) for INeg{n}, and sub_nat(p, q)
# turns any pair back into the integer. sub_nat ignores a common summand
# (SN.shift), and every pair is its normal form plus a common summand
# (SN.e1, SN.e2), so addition and multiplication are the pair operations
# (Add.pair, Mul.pair, Add.gen, Mul.gen). Each Int law is then a Nat
# identity (proofs/nat.bend).

import Base
import ../src/int.bend as I
import ./nat.bend as NL

# Pairs
# -----

def P(a: I.Int) -> Nat:
  match a:
    case I.IPos{n}:
      n
    case I.INeg{n}:
      0n

def Q(a: I.Int) -> Nat:
  match a:
    case I.IPos{n}:
      0n
    case I.INeg{n}:
      1n+n

# the common summand sub_nat strips: min(p, q)
def cm(p: Nat, q: Nat) -> Nat:
  match p q:
    case 0n _:
      0n
    case 1n+mp 0n:
      0n
    case 1n+mp 1n+kp:
      1n+cm(mp, kp)

def SN.cong(-p1: Nat, -p2: Nat, -q1: Nat, -q2: Nat, e1: {p1 == p2 : Nat}, e2: {q1 == q2 : Nat})
  -> {I.Int.sub_nat(p1, q1) == I.Int.sub_nat(p2, q2) : I.Int}:
  %e1 : {I.Int.sub_nat(p1, q1) == I.Int.sub_nat(_, q2) : I.Int}
  %e2 : {I.Int.sub_nat(p1, q1) == I.Int.sub_nat(p1, _) : I.Int}
  {==}

def Nat.cong2(-a1: Nat, -a2: Nat, -b1: Nat, -b2: Nat, e1: {a1 == a2 : Nat}, e2: {b1 == b2 : Nat})
  -> {Nat.add(a1, b1) == Nat.add(a2, b2) : Nat}:
  %e1 : {Nat.add(a1, b1) == Nat.add(_, b2) : Nat}
  %e2 : {Nat.add(a1, b1) == Nat.add(a1, _) : Nat}
  {==}

def SN.zero_r(+n: Nat) -> {I.Int.sub_nat(n, 0n) == I.IPos{n} : I.Int}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def SN.self(+n: Nat) -> {I.Int.sub_nat(n, n) == I.IPos{0n} : I.Int}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      SN.self(m)

def SN.shift(k: Nat, +p: Nat, +q: Nat) -> {I.Int.sub_nat(Nat.add(k, p), Nat.add(k, q)) == I.Int.sub_nat(p, q) : I.Int}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      SN.shift(j, p, q)

def SN.rep(+a: I.Int) -> {I.Int.sub_nat(P(a), Q(a)) == a : I.Int}:
  match a:
    case I.IPos{n}:
      SN.zero_r(n)
    case I.INeg{n}:
      {==}

# p = min(p, q) + P(sub_nat(p, q)), and likewise q
def SN.e1(+p: Nat, +q: Nat) -> {p == Nat.add(cm(p, q), P(I.Int.sub_nat(p, q))) : Nat}:
  match p q:
    case 0n 0n:
      {==}
    case 0n 1n+kp:
      {==}
    case 1n+mp 0n:
      {==}
    case 1n+mp 1n+kp:
      Equal.cong(Nat, Nat, x => 1n+x, mp, Nat.add(cm(mp, kp), P(I.Int.sub_nat(mp, kp))), SN.e1(mp, kp))

def SN.e2(+p: Nat, +q: Nat) -> {q == Nat.add(cm(p, q), Q(I.Int.sub_nat(p, q))) : Nat}:
  match p q:
    case 0n 0n:
      {==}
    case 0n 1n+kp:
      {==}
    case 1n+mp 0n:
      {==}
    case 1n+mp 1n+kp:
      Equal.cong(Nat, Nat, x => 1n+x, kp, Nat.add(cm(mp, kp), Q(I.Int.sub_nat(mp, kp))), SN.e2(mp, kp))

# Addition
# --------

def Add.pair(+a: I.Int, +b: I.Int) -> {I.Int.add(a, b) == I.Int.sub_nat(Nat.add(P(a), P(b)), Nat.add(Q(a), Q(b))) : I.Int}:
  match a b:
    case I.IPos{+m} I.IPos{+n}:
      Equal.sym(I.Int, I.Int.sub_nat(Nat.add(m, n), 0n), I.IPos{Nat.add(m, n)}, SN.zero_r(Nat.add(m, n)))
    case I.INeg{+m} I.INeg{+n}:
      Equal.cong(Nat, I.Int, x => I.INeg{x}, 1n+Nat.add(m, n), Nat.add(m, 1n+n), Equal.sym(Nat, Nat.add(m, 1n+n), 1n+Nat.add(m, n), NL.Nat.add_succ_r(m, n)))
    case I.IPos{+m} I.INeg{+n}:
      Equal.cong(Nat, I.Int, x => I.Int.sub_nat(x, 1n+n), m, Nat.add(m, 0n), Equal.sym(Nat, Nat.add(m, 0n), m, NL.Nat.add_zero_r(m)))
    case I.INeg{+m} I.IPos{+n}:
      Equal.cong(Nat, I.Int, x => I.Int.sub_nat(n, 1n+x), m, Nat.add(m, 0n), Equal.sym(Nat, Nat.add(m, 0n), m, NL.Nat.add_zero_r(m)))

def Int.add_comm(+a: I.Int, +b: I.Int) -> {I.Int.add(a, b) == I.Int.add(b, a) : I.Int}:
  +l = I.Int.sub_nat(Nat.add(P(a), P(b)), Nat.add(Q(a), Q(b)))
  +r = I.Int.sub_nat(Nat.add(P(b), P(a)), Nat.add(Q(b), Q(a)))
  Equal.trans(I.Int, I.Int.add(a, b), l, I.Int.add(b, a), Add.pair(a, b),
    Equal.trans(I.Int, l, r, I.Int.add(b, a),
      SN.cong(Nat.add(P(a), P(b)), Nat.add(P(b), P(a)), Nat.add(Q(a), Q(b)), Nat.add(Q(b), Q(a)), NL.Nat.add_comm(P(a), P(b)), NL.Nat.add_comm(Q(a), Q(b))),
      Equal.sym(I.Int, I.Int.add(b, a), r, Add.pair(b, a))))

# sub_nat(p, q) + c is the pair sum
def Add.gen(+p: Nat, +q: Nat, +c: I.Int) -> {I.Int.add(I.Int.sub_nat(p, q), c) == I.Int.sub_nat(Nat.add(p, P(c)), Nat.add(q, Q(c))) : I.Int}:
  +s = I.Int.sub_nat(p, q)
  +x = P(s)
  +y = Q(s)
  +k = cm(p, q)
  +r1 = I.Int.sub_nat(Nat.add(x, P(c)), Nat.add(y, Q(c)))
  +r2 = I.Int.sub_nat(Nat.add(k, Nat.add(x, P(c))), Nat.add(k, Nat.add(y, Q(c))))
  +r3 = I.Int.sub_nat(Nat.add(Nat.add(k, x), P(c)), Nat.add(Nat.add(k, y), Q(c)))
  +r4 = I.Int.sub_nat(Nat.add(p, P(c)), Nat.add(q, Q(c)))
  Equal.trans(I.Int, I.Int.add(s, c), r1, r4, Add.pair(s, c),
    Equal.trans(I.Int, r1, r2, r4, Equal.sym(I.Int, r2, r1, SN.shift(k, Nat.add(x, P(c)), Nat.add(y, Q(c)))),
      Equal.trans(I.Int, r2, r3, r4,
        SN.cong(Nat.add(k, Nat.add(x, P(c))), Nat.add(Nat.add(k, x), P(c)), Nat.add(k, Nat.add(y, Q(c))), Nat.add(Nat.add(k, y), Q(c)),
          Equal.sym(Nat, Nat.add(Nat.add(k, x), P(c)), Nat.add(k, Nat.add(x, P(c))), NL.Nat.add_assoc(k, x, P(c))),
          Equal.sym(Nat, Nat.add(Nat.add(k, y), Q(c)), Nat.add(k, Nat.add(y, Q(c))), NL.Nat.add_assoc(k, y, Q(c)))),
        SN.cong(Nat.add(Nat.add(k, x), P(c)), Nat.add(p, P(c)), Nat.add(Nat.add(k, y), Q(c)), Nat.add(q, Q(c)),
          Equal.cong(Nat, Nat, w => Nat.add(w, P(c)), Nat.add(k, x), p, Equal.sym(Nat, p, Nat.add(k, x), SN.e1(p, q))),
          Equal.cong(Nat, Nat, w => Nat.add(w, Q(c)), Nat.add(k, y), q, Equal.sym(Nat, q, Nat.add(k, y), SN.e2(p, q)))))))

# the sum of two pairs
def Add.gen2(+p: Nat, +q: Nat, +r: Nat, +s: Nat) -> {I.Int.add(I.Int.sub_nat(p, q), I.Int.sub_nat(r, s)) == I.Int.sub_nat(Nat.add(p, r), Nat.add(q, s)) : I.Int}:
  +t = I.Int.sub_nat(r, s)
  +x = P(t)
  +y = Q(t)
  +k = cm(r, s)
  +r1 = I.Int.sub_nat(Nat.add(p, x), Nat.add(q, y))
  +r2 = I.Int.sub_nat(Nat.add(k, Nat.add(p, x)), Nat.add(k, Nat.add(q, y)))
  +r3 = I.Int.sub_nat(Nat.add(p, Nat.add(k, x)), Nat.add(q, Nat.add(k, y)))
  +r4 = I.Int.sub_nat(Nat.add(p, r), Nat.add(q, s))
  Equal.trans(I.Int, I.Int.add(I.Int.sub_nat(p, q), t), r1, r4, Add.gen(p, q, t),
    Equal.trans(I.Int, r1, r2, r4, Equal.sym(I.Int, r2, r1, SN.shift(k, Nat.add(p, x), Nat.add(q, y))),
      Equal.trans(I.Int, r2, r3, r4,
        SN.cong(Nat.add(k, Nat.add(p, x)), Nat.add(p, Nat.add(k, x)), Nat.add(k, Nat.add(q, y)), Nat.add(q, Nat.add(k, y)), NL.Nat.add_swap(k, p, x), NL.Nat.add_swap(k, q, y)),
        SN.cong(Nat.add(p, Nat.add(k, x)), Nat.add(p, r), Nat.add(q, Nat.add(k, y)), Nat.add(q, s),
          Equal.cong(Nat, Nat, w => Nat.add(p, w), Nat.add(k, x), r, Equal.sym(Nat, r, Nat.add(k, x), SN.e1(r, s))),
          Equal.cong(Nat, Nat, w => Nat.add(q, w), Nat.add(k, y), s, Equal.sym(Nat, s, Nat.add(k, y), SN.e2(r, s)))))))

def Int.add_assoc(+a: I.Int, +b: I.Int, +c: I.Int) -> {I.Int.add(I.Int.add(a, b), c) == I.Int.add(a, I.Int.add(b, c)) : I.Int}:
  +pab = Nat.add(P(a), P(b))
  +qab = Nat.add(Q(a), Q(b))
  +pbc = Nat.add(P(b), P(c))
  +qbc = Nat.add(Q(b), Q(c))
  +m = I.Int.sub_nat(Nat.add(P(a), pbc), Nat.add(Q(a), qbc))
  +l1 = I.Int.add(I.Int.sub_nat(pab, qab), c)
  +l2 = I.Int.sub_nat(Nat.add(pab, P(c)), Nat.add(qab, Q(c)))
  +left = Equal.trans(I.Int, I.Int.add(I.Int.add(a, b), c), l1, m,
    Equal.cong(I.Int, I.Int, w => I.Int.add(w, c), I.Int.add(a, b), I.Int.sub_nat(pab, qab), Add.pair(a, b)),
    Equal.trans(I.Int, l1, l2, m, Add.gen(pab, qab, c),
      SN.cong(Nat.add(pab, P(c)), Nat.add(P(a), pbc), Nat.add(qab, Q(c)), Nat.add(Q(a), qbc), NL.Nat.add_assoc(P(a), P(b), P(c)), NL.Nat.add_assoc(Q(a), Q(b), Q(c)))))
  +r1 = I.Int.add(a, I.Int.sub_nat(pbc, qbc))
  +r2 = I.Int.add(I.Int.sub_nat(pbc, qbc), a)
  +r3 = I.Int.sub_nat(Nat.add(pbc, P(a)), Nat.add(qbc, Q(a)))
  +right = Equal.trans(I.Int, I.Int.add(a, I.Int.add(b, c)), r1, m,
    Equal.cong(I.Int, I.Int, w => I.Int.add(a, w), I.Int.add(b, c), I.Int.sub_nat(pbc, qbc), Add.pair(b, c)),
    Equal.trans(I.Int, r1, r2, m, Int.add_comm(a, I.Int.sub_nat(pbc, qbc)),
      Equal.trans(I.Int, r2, r3, m, Add.gen(pbc, qbc, a),
        SN.cong(Nat.add(pbc, P(a)), Nat.add(P(a), pbc), Nat.add(qbc, Q(a)), Nat.add(Q(a), qbc), NL.Nat.add_comm(pbc, P(a)), NL.Nat.add_comm(qbc, Q(a))))))
  Equal.trans(I.Int, I.Int.add(I.Int.add(a, b), c), m, I.Int.add(a, I.Int.add(b, c)), left, Equal.sym(I.Int, I.Int.add(a, I.Int.add(b, c)), m, right))

def Int.zero_l(+a: I.Int) -> {I.Int.add(I.IPos{0n}, a) == a : I.Int}:
  match a:
    case I.IPos{n}:
      {==}
    case I.INeg{n}:
      {==}

def Int.add_inv(+a: I.Int) -> {I.Int.add(a, I.Int.neg(a)) == I.IPos{0n} : I.Int}:
  match a:
    case I.IPos{0n}:
      {==}
    case I.IPos{1n+m}:
      SN.self(m)
    case I.INeg{m}:
      SN.self(m)

def Int.neg_neg(+a: I.Int) -> {I.Int.neg(I.Int.neg(a)) == a : I.Int}:
  match a:
    case I.IPos{0n}:
      {==}
    case I.IPos{1n+m}:
      {==}
    case I.INeg{m}:
      {==}

# Negation
# --------

def Neg.sn(+p: Nat, +q: Nat) -> {I.Int.neg(I.Int.sub_nat(p, q)) == I.Int.sub_nat(q, p) : I.Int}:
  match p q:
    case 0n 0n:
      {==}
    case 0n 1n+kp:
      {==}
    case 1n+mp 0n:
      {==}
    case 1n+mp 1n+kp:
      Neg.sn(mp, kp)

def Neg.P(+a: I.Int) -> {P(I.Int.neg(a)) == Q(a) : Nat}:
  match a:
    case I.IPos{0n}:
      {==}
    case I.IPos{1n+m}:
      {==}
    case I.INeg{m}:
      {==}

def Neg.Q(+a: I.Int) -> {Q(I.Int.neg(a)) == P(a) : Nat}:
  match a:
    case I.IPos{0n}:
      {==}
    case I.IPos{1n+m}:
      {==}
    case I.INeg{m}:
      {==}

def Int.neg_add(+a: I.Int, +b: I.Int) -> {I.Int.neg(I.Int.add(a, b)) == I.Int.add(I.Int.neg(a), I.Int.neg(b)) : I.Int}:
  +na = I.Int.neg(a)
  +nb = I.Int.neg(b)
  +m = I.Int.sub_nat(Nat.add(Q(a), Q(b)), Nat.add(P(a), P(b)))
  +l1 = I.Int.neg(I.Int.sub_nat(Nat.add(P(a), P(b)), Nat.add(Q(a), Q(b))))
  +left = Equal.trans(I.Int, I.Int.neg(I.Int.add(a, b)), l1, m,
    Equal.cong(I.Int, I.Int, w => I.Int.neg(w), I.Int.add(a, b), I.Int.sub_nat(Nat.add(P(a), P(b)), Nat.add(Q(a), Q(b))), Add.pair(a, b)),
    Neg.sn(Nat.add(P(a), P(b)), Nat.add(Q(a), Q(b))))
  +r1 = I.Int.sub_nat(Nat.add(P(na), P(nb)), Nat.add(Q(na), Q(nb)))
  +right = Equal.trans(I.Int, I.Int.add(na, nb), r1, m, Add.pair(na, nb),
    SN.cong(Nat.add(P(na), P(nb)), Nat.add(Q(a), Q(b)), Nat.add(Q(na), Q(nb)), Nat.add(P(a), P(b)),
      Nat.cong2(P(na), Q(a), P(nb), Q(b), Neg.P(a), Neg.P(b)),
      Nat.cong2(Q(na), P(a), Q(nb), P(b), Neg.Q(a), Neg.Q(b))))
  Equal.trans(I.Int, I.Int.neg(I.Int.add(a, b)), m, I.Int.add(na, nb), left, Equal.sym(I.Int, I.Int.add(na, nb), m, right))

# Multiplication
# --------------

# n (1 + m) + m = n + m (1 + n)
def Nat.cross(+m: Nat, +n: Nat) -> {Nat.add(Nat.mul(n, 1n+m), m) == Nat.add(n, Nat.mul(m, 1n+n)) : Nat}:
  +a1 = Nat.add(Nat.add(n, Nat.mul(n, m)), m)
  +a2 = Nat.add(n, Nat.add(Nat.mul(n, m), m))
  +a3 = Nat.add(n, Nat.add(m, Nat.mul(n, m)))
  +a4 = Nat.add(n, Nat.add(m, Nat.mul(m, n)))
  Equal.trans(Nat, Nat.add(Nat.mul(n, 1n+m), m), a1, Nat.add(n, Nat.mul(m, 1n+n)),
    Equal.cong(Nat, Nat, w => Nat.add(w, m), Nat.mul(n, 1n+m), Nat.add(n, Nat.mul(n, m)), NL.Nat.mul_succ_r(n, m)),
    Equal.trans(Nat, a1, a2, Nat.add(n, Nat.mul(m, 1n+n)), NL.Nat.add_assoc(n, Nat.mul(n, m), m),
      Equal.trans(Nat, a2, a3, Nat.add(n, Nat.mul(m, 1n+n)),
        Equal.cong(Nat, Nat, w => Nat.add(n, w), Nat.add(Nat.mul(n, m), m), Nat.add(m, Nat.mul(n, m)), NL.Nat.add_comm(Nat.mul(n, m), m)),
        Equal.trans(Nat, a3, a4, Nat.add(n, Nat.mul(m, 1n+n)),
          Equal.cong(Nat, Nat, w => Nat.add(n, Nat.add(m, w)), Nat.mul(n, m), Nat.mul(m, n), NL.Nat.mul_comm(n, m)),
          Equal.cong(Nat, Nat, w => Nat.add(n, w), Nat.add(m, Nat.mul(m, n)), Nat.mul(m, 1n+n), Equal.sym(Nat, Nat.mul(m, 1n+n), Nat.add(m, Nat.mul(m, n)), NL.Nat.mul_succ_r(m, n)))))))

# m 0 + 0 = 0
def Nat.mz(+m: Nat) -> {Nat.add(Nat.mul(m, 0n), 0n) == 0n : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(m, 0n), 0n), Nat.mul(m, 0n), 0n, NL.Nat.add_zero_r(Nat.mul(m, 0n)), NL.Nat.mul_zero_r(m))

def Mul.pair(+a: I.Int, +b: I.Int)
  -> {I.Int.mul(a, b) == I.Int.sub_nat(Nat.add(Nat.mul(P(a), P(b)), Nat.mul(Q(a), Q(b))), Nat.add(Nat.mul(P(a), Q(b)), Nat.mul(Q(a), P(b)))) : I.Int}:
  match a b:
    case I.IPos{+m} I.IPos{+n}:
      +x = Nat.mul(m, n)
      Equal.trans(I.Int, I.IPos{x}, I.Int.sub_nat(x, 0n), I.Int.sub_nat(Nat.add(x, 0n), Nat.add(Nat.mul(m, 0n), 0n)),
        Equal.sym(I.Int, I.Int.sub_nat(x, 0n), I.IPos{x}, SN.zero_r(x)),
        SN.cong(x, Nat.add(x, 0n), 0n, Nat.add(Nat.mul(m, 0n), 0n), Equal.sym(Nat, Nat.add(x, 0n), x, NL.Nat.add_zero_r(x)), Equal.sym(Nat, Nat.add(Nat.mul(m, 0n), 0n), 0n, Nat.mz(m))))
    case I.INeg{+m} I.INeg{+n}:
      +x = Nat.mul(1n+m, 1n+n)
      Equal.sym(I.Int, I.Int.sub_nat(x, Nat.mul(m, 0n)), I.IPos{x},
        Equal.trans(I.Int, I.Int.sub_nat(x, Nat.mul(m, 0n)), I.Int.sub_nat(x, 0n), I.IPos{x},
          Equal.cong(Nat, I.Int, w => I.Int.sub_nat(x, w), Nat.mul(m, 0n), 0n, NL.Nat.mul_zero_r(m)),
          SN.zero_r(x)))
    case I.IPos{0n} I.INeg{n}:
      {==}
    case I.IPos{1n+(+m)} I.INeg{+n}:
      +y = Nat.add(n, Nat.mul(m, 1n+n))
      Equal.trans(I.Int, I.INeg{Nat.add(Nat.mul(m, 1n+n), n)}, I.INeg{y}, I.Int.sub_nat(Nat.add(Nat.mul(m, 0n), 0n), 1n+Nat.add(y, 0n)),
        Equal.cong(Nat, I.Int, w => I.INeg{w}, Nat.add(Nat.mul(m, 1n+n), n), y, NL.Nat.add_comm(Nat.mul(m, 1n+n), n)),
        SN.cong(0n, Nat.add(Nat.mul(m, 0n), 0n), 1n+y, 1n+Nat.add(y, 0n),
          Equal.sym(Nat, Nat.add(Nat.mul(m, 0n), 0n), 0n, Nat.mz(m)),
          Equal.cong(Nat, Nat, w => 1n+w, y, Nat.add(y, 0n), Equal.sym(Nat, Nat.add(y, 0n), y, NL.Nat.add_zero_r(y)))))
    case I.INeg{+m} I.IPos{0n}:
      Equal.sym(I.Int, I.Int.sub_nat(Nat.mul(m, 0n), Nat.mul(m, 0n)), I.IPos{0n}, SN.self(Nat.mul(m, 0n)))
    case I.INeg{+m} I.IPos{1n+(+n)}:
      +y = Nat.add(n, Nat.mul(m, 1n+n))
      Equal.trans(I.Int, I.INeg{Nat.add(Nat.mul(n, 1n+m), m)}, I.INeg{y}, I.Int.sub_nat(Nat.mul(m, 0n), 1n+y),
        Equal.cong(Nat, I.Int, w => I.INeg{w}, Nat.add(Nat.mul(n, 1n+m), m), y, Nat.cross(m, n)),
        Equal.cong(Nat, I.Int, w => I.Int.sub_nat(w, 1n+y), 0n, Nat.mul(m, 0n), Equal.sym(Nat, Nat.mul(m, 0n), 0n, NL.Nat.mul_zero_r(m))))

# (k + x) e + (k + y) f = (k e + k f) + (x e + y f)
def Nat.dist2(+k: Nat, +x: Nat, +y: Nat, +e: Nat, +f: Nat)
  -> {Nat.add(Nat.mul(Nat.add(k, x), e), Nat.mul(Nat.add(k, y), f)) == Nat.add(Nat.add(Nat.mul(k, e), Nat.mul(k, f)), Nat.add(Nat.mul(x, e), Nat.mul(y, f))) : Nat}:
  +m = Nat.add(Nat.add(Nat.mul(k, e), Nat.mul(x, e)), Nat.add(Nat.mul(k, f), Nat.mul(y, f)))
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(k, x), e), Nat.mul(Nat.add(k, y), f)), m, Nat.add(Nat.add(Nat.mul(k, e), Nat.mul(k, f)), Nat.add(Nat.mul(x, e), Nat.mul(y, f))),
    Nat.cong2(Nat.mul(Nat.add(k, x), e), Nat.add(Nat.mul(k, e), Nat.mul(x, e)), Nat.mul(Nat.add(k, y), f), Nat.add(Nat.mul(k, f), Nat.mul(y, f)), NL.Nat.mul_dist_r(k, x, e), NL.Nat.mul_dist_r(k, y, f)),
    NL.Nat.add_4(Nat.mul(k, e), Nat.mul(x, e), Nat.mul(k, f), Nat.mul(y, f)))

# sub_nat(p, q) c is the pair product
def Mul.gen(+p: Nat, +q: Nat, +c: I.Int)
  -> {I.Int.mul(I.Int.sub_nat(p, q), c) == I.Int.sub_nat(Nat.add(Nat.mul(p, P(c)), Nat.mul(q, Q(c))), Nat.add(Nat.mul(p, Q(c)), Nat.mul(q, P(c)))) : I.Int}:
  +s = I.Int.sub_nat(p, q)
  +x = P(s)
  +y = Q(s)
  +k = cm(p, q)
  +e = P(c)
  +f = Q(c)
  +ka = Nat.add(Nat.mul(k, e), Nat.mul(k, f))
  +xa = Nat.add(Nat.mul(x, e), Nat.mul(y, f))
  +xb = Nat.add(Nat.mul(x, f), Nat.mul(y, e))
  +r1 = I.Int.sub_nat(xa, xb)
  +r2 = I.Int.sub_nat(Nat.add(ka, xa), Nat.add(ka, xb))
  +r3 = I.Int.sub_nat(Nat.add(Nat.mul(Nat.add(k, x), e), Nat.mul(Nat.add(k, y), f)), Nat.add(Nat.mul(Nat.add(k, x), f), Nat.mul(Nat.add(k, y), e)))
  +r4 = I.Int.sub_nat(Nat.add(Nat.mul(p, e), Nat.mul(q, f)), Nat.add(Nat.mul(p, f), Nat.mul(q, e)))
  +kb2 = Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(k, x), f), Nat.mul(Nat.add(k, y), e)), Nat.add(Nat.add(Nat.mul(k, f), Nat.mul(k, e)), xb), Nat.add(ka, xb),
    Nat.dist2(k, x, y, f, e),
    Equal.cong(Nat, Nat, w => Nat.add(w, xb), Nat.add(Nat.mul(k, f), Nat.mul(k, e)), ka, NL.Nat.add_comm(Nat.mul(k, f), Nat.mul(k, e))))
  +pe = SN.e1(p, q)
  +qe = SN.e2(p, q)
  Equal.trans(I.Int, I.Int.mul(s, c), r1, r4, Mul.pair(s, c),
    Equal.trans(I.Int, r1, r2, r4, Equal.sym(I.Int, r2, r1, SN.shift(ka, xa, xb)),
      Equal.trans(I.Int, r2, r3, r4,
        Equal.sym(I.Int, r3, r2, SN.cong(Nat.add(Nat.mul(Nat.add(k, x), e), Nat.mul(Nat.add(k, y), f)), Nat.add(ka, xa), Nat.add(Nat.mul(Nat.add(k, x), f), Nat.mul(Nat.add(k, y), e)), Nat.add(ka, xb), Nat.dist2(k, x, y, e, f), kb2)),
        Equal.sym(I.Int, r4, r3,
          Equal.trans(I.Int, r4, I.Int.sub_nat(Nat.add(Nat.mul(Nat.add(k, x), e), Nat.mul(q, f)), Nat.add(Nat.mul(Nat.add(k, x), f), Nat.mul(q, e))), r3,
            Equal.cong(Nat, I.Int, w => I.Int.sub_nat(Nat.add(Nat.mul(w, e), Nat.mul(q, f)), Nat.add(Nat.mul(w, f), Nat.mul(q, e))), p, Nat.add(k, x), pe),
            Equal.cong(Nat, I.Int, w => I.Int.sub_nat(Nat.add(Nat.mul(Nat.add(k, x), e), Nat.mul(w, f)), Nat.add(Nat.mul(Nat.add(k, x), f), Nat.mul(w, e))), q, Nat.add(k, y), qe))))))

def Int.mul_comm(+a: I.Int, +b: I.Int) -> {I.Int.mul(a, b) == I.Int.mul(b, a) : I.Int}:
  +l = I.Int.sub_nat(Nat.add(Nat.mul(P(a), P(b)), Nat.mul(Q(a), Q(b))), Nat.add(Nat.mul(P(a), Q(b)), Nat.mul(Q(a), P(b))))
  +r = I.Int.sub_nat(Nat.add(Nat.mul(P(b), P(a)), Nat.mul(Q(b), Q(a))), Nat.add(Nat.mul(P(b), Q(a)), Nat.mul(Q(b), P(a))))
  Equal.trans(I.Int, I.Int.mul(a, b), l, I.Int.mul(b, a), Mul.pair(a, b),
    Equal.trans(I.Int, l, r, I.Int.mul(b, a),
      SN.cong(Nat.add(Nat.mul(P(a), P(b)), Nat.mul(Q(a), Q(b))), Nat.add(Nat.mul(P(b), P(a)), Nat.mul(Q(b), Q(a))),
        Nat.add(Nat.mul(P(a), Q(b)), Nat.mul(Q(a), P(b))), Nat.add(Nat.mul(P(b), Q(a)), Nat.mul(Q(b), P(a))),
        Nat.cong2(Nat.mul(P(a), P(b)), Nat.mul(P(b), P(a)), Nat.mul(Q(a), Q(b)), Nat.mul(Q(b), Q(a)), NL.Nat.mul_comm(P(a), P(b)), NL.Nat.mul_comm(Q(a), Q(b))),
        Equal.trans(Nat, Nat.add(Nat.mul(P(a), Q(b)), Nat.mul(Q(a), P(b))), Nat.add(Nat.mul(Q(b), P(a)), Nat.mul(P(b), Q(a))), Nat.add(Nat.mul(P(b), Q(a)), Nat.mul(Q(b), P(a))),
          Nat.cong2(Nat.mul(P(a), Q(b)), Nat.mul(Q(b), P(a)), Nat.mul(Q(a), P(b)), Nat.mul(P(b), Q(a)), NL.Nat.mul_comm(P(a), Q(b)), NL.Nat.mul_comm(Q(a), P(b))),
          NL.Nat.add_comm(Nat.mul(Q(b), P(a)), Nat.mul(P(b), Q(a))))),
      Equal.sym(I.Int, I.Int.mul(b, a), r, Mul.pair(b, a))))

# (x y) z = (y z) x
def Nat.m3(+x: Nat, +y: Nat, +z: Nat) -> {Nat.mul(Nat.mul(x, y), z) == Nat.mul(Nat.mul(y, z), x) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.mul(x, y), z), Nat.mul(x, Nat.mul(y, z)), Nat.mul(Nat.mul(y, z), x), NL.Nat.mul_assoc(x, y, z), NL.Nat.mul_comm(x, Nat.mul(y, z)))

# (a b + c d) e + (a d + c b) f = (b e + d f) a + (b f + d e) c
def Nat.assoc_p(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat)
  -> {Nat.add(Nat.mul(Nat.add(Nat.mul(a, b), Nat.mul(c, d)), e), Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(c, b)), f))
      == Nat.add(Nat.mul(Nat.add(Nat.mul(b, e), Nat.mul(d, f)), a), Nat.mul(Nat.add(Nat.mul(b, f), Nat.mul(d, e)), c)) : Nat}:
  +a1 = Nat.mul(Nat.mul(a, b), e)
  +a2 = Nat.mul(Nat.mul(c, d), e)
  +a3 = Nat.mul(Nat.mul(a, d), f)
  +a4 = Nat.mul(Nat.mul(c, b), f)
  +b1 = Nat.mul(Nat.mul(b, e), a)
  +b2 = Nat.mul(Nat.mul(d, e), c)
  +b3 = Nat.mul(Nat.mul(d, f), a)
  +b4 = Nat.mul(Nat.mul(b, f), c)
  +l = Nat.add(Nat.mul(Nat.add(Nat.mul(a, b), Nat.mul(c, d)), e), Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(c, b)), f))
  +r = Nat.add(Nat.mul(Nat.add(Nat.mul(b, e), Nat.mul(d, f)), a), Nat.mul(Nat.add(Nat.mul(b, f), Nat.mul(d, e)), c))
  +l1 = Nat.add(Nat.add(a1, a2), Nat.add(a3, a4))
  +r1 = Nat.add(Nat.add(b1, b3), Nat.add(b4, b2))
  +el = Nat.cong2(Nat.mul(Nat.add(Nat.mul(a, b), Nat.mul(c, d)), e), Nat.add(a1, a2), Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(c, b)), f), Nat.add(a3, a4),
    NL.Nat.mul_dist_r(Nat.mul(a, b), Nat.mul(c, d), e), NL.Nat.mul_dist_r(Nat.mul(a, d), Nat.mul(c, b), f))
  +er = Nat.cong2(Nat.mul(Nat.add(Nat.mul(b, e), Nat.mul(d, f)), a), Nat.add(b1, b3), Nat.mul(Nat.add(Nat.mul(b, f), Nat.mul(d, e)), c), Nat.add(b4, b2),
    NL.Nat.mul_dist_r(Nat.mul(b, e), Nat.mul(d, f), a), NL.Nat.mul_dist_r(Nat.mul(b, f), Nat.mul(d, e), c))
  +mid = Equal.trans(Nat, l1, Nat.add(Nat.add(a1, a3), Nat.add(a2, a4)), r1, NL.Nat.add_4(a1, a2, a3, a4),
    Equal.trans(Nat, Nat.add(Nat.add(a1, a3), Nat.add(a2, a4)), Nat.add(Nat.add(a1, a3), Nat.add(a4, a2)), r1,
      Equal.cong(Nat, Nat, w => Nat.add(Nat.add(a1, a3), w), Nat.add(a2, a4), Nat.add(a4, a2), NL.Nat.add_comm(a2, a4)),
      Nat.cong2(Nat.add(a1, a3), Nat.add(b1, b3), Nat.add(a4, a2), Nat.add(b4, b2),
        Nat.cong2(a1, b1, a3, b3, Nat.m3(a, b, e), Nat.m3(a, d, f)),
        Nat.cong2(a4, b4, a2, b2, Nat.m3(c, b, f), Nat.m3(c, d, e)))))
  Equal.trans(Nat, l, l1, r, el, Equal.trans(Nat, l1, r1, r, mid, Equal.sym(Nat, r, r1, er)))

# (a b + c d) f + (a d + c b) e = (b e + d f) c + (b f + d e) a
def Nat.assoc_q(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat)
  -> {Nat.add(Nat.mul(Nat.add(Nat.mul(a, b), Nat.mul(c, d)), f), Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(c, b)), e))
      == Nat.add(Nat.mul(Nat.add(Nat.mul(b, e), Nat.mul(d, f)), c), Nat.mul(Nat.add(Nat.mul(b, f), Nat.mul(d, e)), a)) : Nat}:
  +c1 = Nat.mul(Nat.mul(a, b), f)
  +c2 = Nat.mul(Nat.mul(c, d), f)
  +c3 = Nat.mul(Nat.mul(a, d), e)
  +c4 = Nat.mul(Nat.mul(c, b), e)
  +d1 = Nat.mul(Nat.mul(b, e), c)
  +d2 = Nat.mul(Nat.mul(d, f), c)
  +d3 = Nat.mul(Nat.mul(b, f), a)
  +d4 = Nat.mul(Nat.mul(d, e), a)
  +l = Nat.add(Nat.mul(Nat.add(Nat.mul(a, b), Nat.mul(c, d)), f), Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(c, b)), e))
  +r = Nat.add(Nat.mul(Nat.add(Nat.mul(b, e), Nat.mul(d, f)), c), Nat.mul(Nat.add(Nat.mul(b, f), Nat.mul(d, e)), a))
  +l1 = Nat.add(Nat.add(c1, c2), Nat.add(c3, c4))
  +r1 = Nat.add(Nat.add(d1, d2), Nat.add(d3, d4))
  +el = Nat.cong2(Nat.mul(Nat.add(Nat.mul(a, b), Nat.mul(c, d)), f), Nat.add(c1, c2), Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(c, b)), e), Nat.add(c3, c4),
    NL.Nat.mul_dist_r(Nat.mul(a, b), Nat.mul(c, d), f), NL.Nat.mul_dist_r(Nat.mul(a, d), Nat.mul(c, b), e))
  +er = Nat.cong2(Nat.mul(Nat.add(Nat.mul(b, e), Nat.mul(d, f)), c), Nat.add(d1, d2), Nat.mul(Nat.add(Nat.mul(b, f), Nat.mul(d, e)), a), Nat.add(d3, d4),
    NL.Nat.mul_dist_r(Nat.mul(b, e), Nat.mul(d, f), c), NL.Nat.mul_dist_r(Nat.mul(b, f), Nat.mul(d, e), a))
  # (c1 + c2) + (c3 + c4) -> (c4 + c2) + (c1 + c3), then c4 = d1, c2 = d2, c1 = d3, c3 = d4
  +s1 = Nat.add(Nat.add(c1, c3), Nat.add(c2, c4))
  +s2 = Nat.add(Nat.add(c2, c4), Nat.add(c1, c3))
  +s3 = Nat.add(Nat.add(c4, c2), Nat.add(c1, c3))
  +mid = Equal.trans(Nat, l1, s1, r1, NL.Nat.add_4(c1, c2, c3, c4),
    Equal.trans(Nat, s1, s2, r1, NL.Nat.add_comm(Nat.add(c1, c3), Nat.add(c2, c4)),
      Equal.trans(Nat, s2, s3, r1,
        Equal.cong(Nat, Nat, w => Nat.add(w, Nat.add(c1, c3)), Nat.add(c2, c4), Nat.add(c4, c2), NL.Nat.add_comm(c2, c4)),
        Nat.cong2(Nat.add(c4, c2), Nat.add(d1, d2), Nat.add(c1, c3), Nat.add(d3, d4),
          Nat.cong2(c4, d1, c2, d2, Nat.m3(c, b, e), Nat.m3(c, d, f)),
          Nat.cong2(c1, d3, c3, d4, Nat.m3(a, b, f), Nat.m3(a, d, e))))))
  Equal.trans(Nat, l, l1, r, el, Equal.trans(Nat, l1, r1, r, mid, Equal.sym(Nat, r, r1, er)))

def Int.mul_assoc(+a: I.Int, +b: I.Int, +c: I.Int) -> {I.Int.mul(I.Int.mul(a, b), c) == I.Int.mul(a, I.Int.mul(b, c)) : I.Int}:
  +x1 = Nat.add(Nat.mul(P(a), P(b)), Nat.mul(Q(a), Q(b)))
  +y1 = Nat.add(Nat.mul(P(a), Q(b)), Nat.mul(Q(a), P(b)))
  +x2 = Nat.add(Nat.mul(P(b), P(c)), Nat.mul(Q(b), Q(c)))
  +y2 = Nat.add(Nat.mul(P(b), Q(c)), Nat.mul(Q(b), P(c)))
  +lp = Nat.add(Nat.mul(x1, P(c)), Nat.mul(y1, Q(c)))
  +lq = Nat.add(Nat.mul(x1, Q(c)), Nat.mul(y1, P(c)))
  +rp = Nat.add(Nat.mul(x2, P(a)), Nat.mul(y2, Q(a)))
  +rq = Nat.add(Nat.mul(x2, Q(a)), Nat.mul(y2, P(a)))
  +l1 = I.Int.mul(I.Int.sub_nat(x1, y1), c)
  +r1 = I.Int.mul(a, I.Int.sub_nat(x2, y2))
  +r2 = I.Int.mul(I.Int.sub_nat(x2, y2), a)
  +left = Equal.trans(I.Int, I.Int.mul(I.Int.mul(a, b), c), l1, I.Int.sub_nat(lp, lq),
    Equal.cong(I.Int, I.Int, w => I.Int.mul(w, c), I.Int.mul(a, b), I.Int.sub_nat(x1, y1), Mul.pair(a, b)),
    Mul.gen(x1, y1, c))
  +right = Equal.trans(I.Int, I.Int.mul(a, I.Int.mul(b, c)), r1, I.Int.sub_nat(rp, rq),
    Equal.cong(I.Int, I.Int, w => I.Int.mul(a, w), I.Int.mul(b, c), I.Int.sub_nat(x2, y2), Mul.pair(b, c)),
    Equal.trans(I.Int, r1, r2, I.Int.sub_nat(rp, rq), Int.mul_comm(a, I.Int.sub_nat(x2, y2)), Mul.gen(x2, y2, a)))
  +mid = SN.cong(lp, rp, lq, rq,
    Nat.assoc_p(P(a), P(b), Q(a), Q(b), P(c), Q(c)),
    Nat.assoc_q(P(a), P(b), Q(a), Q(b), P(c), Q(c)))
  Equal.trans(I.Int, I.Int.mul(I.Int.mul(a, b), c), I.Int.sub_nat(lp, lq), I.Int.mul(a, I.Int.mul(b, c)), left,
    Equal.trans(I.Int, I.Int.sub_nat(lp, lq), I.Int.sub_nat(rp, rq), I.Int.mul(a, I.Int.mul(b, c)), mid,
      Equal.sym(I.Int, I.Int.mul(a, I.Int.mul(b, c)), I.Int.sub_nat(rp, rq), right)))

# (b + c) a = a b + a c
def Nat.dr(+b: Nat, +c: Nat, +a: Nat) -> {Nat.mul(Nat.add(b, c), a) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.add(b, c), a), Nat.add(Nat.mul(b, a), Nat.mul(c, a)), Nat.add(Nat.mul(a, b), Nat.mul(a, c)),
    NL.Nat.mul_dist_r(b, c, a),
    Nat.cong2(Nat.mul(b, a), Nat.mul(a, b), Nat.mul(c, a), Nat.mul(a, c), NL.Nat.mul_comm(b, a), NL.Nat.mul_comm(c, a)))

def Int.dist_l(+a: I.Int, +b: I.Int, +c: I.Int) -> {I.Int.mul(a, I.Int.add(b, c)) == I.Int.add(I.Int.mul(a, b), I.Int.mul(a, c)) : I.Int}:
  +pa = P(a)
  +qa = Q(a)
  +pbc = Nat.add(P(b), P(c))
  +qbc = Nat.add(Q(b), Q(c))
  +xab = Nat.add(Nat.mul(pa, P(b)), Nat.mul(qa, Q(b)))
  +yab = Nat.add(Nat.mul(pa, Q(b)), Nat.mul(qa, P(b)))
  +xac = Nat.add(Nat.mul(pa, P(c)), Nat.mul(qa, Q(c)))
  +yac = Nat.add(Nat.mul(pa, Q(c)), Nat.mul(qa, P(c)))
  +lp = Nat.add(Nat.mul(pbc, pa), Nat.mul(qbc, qa))
  +lq = Nat.add(Nat.mul(pbc, qa), Nat.mul(qbc, pa))
  +l1 = I.Int.mul(a, I.Int.sub_nat(pbc, qbc))
  +l2 = I.Int.mul(I.Int.sub_nat(pbc, qbc), a)
  +left = Equal.trans(I.Int, I.Int.mul(a, I.Int.add(b, c)), l1, I.Int.sub_nat(lp, lq),
    Equal.cong(I.Int, I.Int, w => I.Int.mul(a, w), I.Int.add(b, c), I.Int.sub_nat(pbc, qbc), Add.pair(b, c)),
    Equal.trans(I.Int, l1, l2, I.Int.sub_nat(lp, lq), Int.mul_comm(a, I.Int.sub_nat(pbc, qbc)), Mul.gen(pbc, qbc, a)))
  +r1 = I.Int.add(I.Int.sub_nat(xab, yab), I.Int.mul(a, c))
  +r2 = I.Int.add(I.Int.sub_nat(xab, yab), I.Int.sub_nat(xac, yac))
  +right = Equal.trans(I.Int, I.Int.add(I.Int.mul(a, b), I.Int.mul(a, c)), r1, I.Int.sub_nat(Nat.add(xab, xac), Nat.add(yab, yac)),
    Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.mul(a, c)), I.Int.mul(a, b), I.Int.sub_nat(xab, yab), Mul.pair(a, b)),
    Equal.trans(I.Int, r1, r2, I.Int.sub_nat(Nat.add(xab, xac), Nat.add(yab, yac)),
      Equal.cong(I.Int, I.Int, w => I.Int.add(I.Int.sub_nat(xab, yab), w), I.Int.mul(a, c), I.Int.sub_nat(xac, yac), Mul.pair(a, c)),
      Add.gen2(xab, yab, xac, yac)))
  # P parts: (pa P(b) + pa P(c)) + (qa Q(b) + qa Q(c)) -> xab + xac
  +ep = Equal.trans(Nat, lp, Nat.add(Nat.add(Nat.mul(pa, P(b)), Nat.mul(pa, P(c))), Nat.add(Nat.mul(qa, Q(b)), Nat.mul(qa, Q(c)))), Nat.add(xab, xac),
    Nat.cong2(Nat.mul(pbc, pa), Nat.add(Nat.mul(pa, P(b)), Nat.mul(pa, P(c))), Nat.mul(qbc, qa), Nat.add(Nat.mul(qa, Q(b)), Nat.mul(qa, Q(c))), Nat.dr(P(b), P(c), pa), Nat.dr(Q(b), Q(c), qa)),
    NL.Nat.add_4(Nat.mul(pa, P(b)), Nat.mul(pa, P(c)), Nat.mul(qa, Q(b)), Nat.mul(qa, Q(c))))
  # Q parts: (qa P(b) + qa P(c)) + (pa Q(b) + pa Q(c)) -> (qa P(b) + pa Q(b)) + (qa P(c) + pa Q(c)) -> yab + yac
  +s1 = Nat.add(Nat.add(Nat.mul(qa, P(b)), Nat.mul(qa, P(c))), Nat.add(Nat.mul(pa, Q(b)), Nat.mul(pa, Q(c))))
  +s2 = Nat.add(Nat.add(Nat.mul(qa, P(b)), Nat.mul(pa, Q(b))), Nat.add(Nat.mul(qa, P(c)), Nat.mul(pa, Q(c))))
  +eq = Equal.trans(Nat, lq, s1, Nat.add(yab, yac),
    Nat.cong2(Nat.mul(pbc, qa), Nat.add(Nat.mul(qa, P(b)), Nat.mul(qa, P(c))), Nat.mul(qbc, pa), Nat.add(Nat.mul(pa, Q(b)), Nat.mul(pa, Q(c))), Nat.dr(P(b), P(c), qa), Nat.dr(Q(b), Q(c), pa)),
    Equal.trans(Nat, s1, s2, Nat.add(yab, yac), NL.Nat.add_4(Nat.mul(qa, P(b)), Nat.mul(qa, P(c)), Nat.mul(pa, Q(b)), Nat.mul(pa, Q(c))),
      Nat.cong2(Nat.add(Nat.mul(qa, P(b)), Nat.mul(pa, Q(b))), yab, Nat.add(Nat.mul(qa, P(c)), Nat.mul(pa, Q(c))), yac,
        NL.Nat.add_comm(Nat.mul(qa, P(b)), Nat.mul(pa, Q(b))), NL.Nat.add_comm(Nat.mul(qa, P(c)), Nat.mul(pa, Q(c))))))
  Equal.trans(I.Int, I.Int.mul(a, I.Int.add(b, c)), I.Int.sub_nat(lp, lq), I.Int.add(I.Int.mul(a, b), I.Int.mul(a, c)), left,
    Equal.trans(I.Int, I.Int.sub_nat(lp, lq), I.Int.sub_nat(Nat.add(xab, xac), Nat.add(yab, yac)), I.Int.add(I.Int.mul(a, b), I.Int.mul(a, c)),
      SN.cong(lp, Nat.add(xab, xac), lq, Nat.add(yab, yac), ep, eq),
      Equal.sym(I.Int, I.Int.add(I.Int.mul(a, b), I.Int.mul(a, c)), I.Int.sub_nat(Nat.add(xab, xac), Nat.add(yab, yac)), right)))

def Int.unit_r(+a: I.Int) -> {I.Int.mul(a, I.IPos{1n}) == a : I.Int}:
  match a:
    case I.IPos{0n}:
      {==}
    case I.IPos{1n+(+m)}:
      Equal.cong(Nat, I.Int, w => I.IPos{w}, Nat.mul(1n+m, 1n), 1n+m, NL.Nat.mul_one_r(1n+m))
    case I.INeg{m}:
      {==}

def Int.neg_mul_l(+a: I.Int, +b: I.Int) -> {I.Int.mul(I.Int.neg(a), b) == I.Int.neg(I.Int.mul(a, b)) : I.Int}:
  +na = I.Int.neg(a)
  +pa = P(a)
  +qa = Q(a)
  +pb = P(b)
  +qb = Q(b)
  +m = I.Int.sub_nat(Nat.add(Nat.mul(pa, qb), Nat.mul(qa, pb)), Nat.add(Nat.mul(pa, pb), Nat.mul(qa, qb)))
  +l1 = I.Int.sub_nat(Nat.add(Nat.mul(P(na), pb), Nat.mul(Q(na), qb)), Nat.add(Nat.mul(P(na), qb), Nat.mul(Q(na), pb)))
  +l2 = I.Int.sub_nat(Nat.add(Nat.mul(qa, pb), Nat.mul(Q(na), qb)), Nat.add(Nat.mul(qa, qb), Nat.mul(Q(na), pb)))
  +l3 = I.Int.sub_nat(Nat.add(Nat.mul(qa, pb), Nat.mul(pa, qb)), Nat.add(Nat.mul(qa, qb), Nat.mul(pa, pb)))
  +left = Equal.trans(I.Int, I.Int.mul(na, b), l1, m, Mul.pair(na, b),
    Equal.trans(I.Int, l1, l2, m,
      Equal.cong(Nat, I.Int, w => I.Int.sub_nat(Nat.add(Nat.mul(w, pb), Nat.mul(Q(na), qb)), Nat.add(Nat.mul(w, qb), Nat.mul(Q(na), pb))), P(na), qa, Neg.P(a)),
      Equal.trans(I.Int, l2, l3, m,
        Equal.cong(Nat, I.Int, w => I.Int.sub_nat(Nat.add(Nat.mul(qa, pb), Nat.mul(w, qb)), Nat.add(Nat.mul(qa, qb), Nat.mul(w, pb))), Q(na), pa, Neg.Q(a)),
        SN.cong(Nat.add(Nat.mul(qa, pb), Nat.mul(pa, qb)), Nat.add(Nat.mul(pa, qb), Nat.mul(qa, pb)), Nat.add(Nat.mul(qa, qb), Nat.mul(pa, pb)), Nat.add(Nat.mul(pa, pb), Nat.mul(qa, qb)),
          NL.Nat.add_comm(Nat.mul(qa, pb), Nat.mul(pa, qb)), NL.Nat.add_comm(Nat.mul(qa, qb), Nat.mul(pa, pb))))))
  +x = Nat.add(Nat.mul(pa, pb), Nat.mul(qa, qb))
  +y = Nat.add(Nat.mul(pa, qb), Nat.mul(qa, pb))
  +right = Equal.trans(I.Int, I.Int.neg(I.Int.mul(a, b)), I.Int.neg(I.Int.sub_nat(x, y)), m,
    Equal.cong(I.Int, I.Int, w => I.Int.neg(w), I.Int.mul(a, b), I.Int.sub_nat(x, y), Mul.pair(a, b)),
    Neg.sn(x, y))
  Equal.trans(I.Int, I.Int.mul(na, b), m, I.Int.neg(I.Int.mul(a, b)), left, Equal.sym(I.Int, I.Int.neg(I.Int.mul(a, b)), m, right))

# Order
# -----

def Bool.disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def Bool.ft(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.disc(_)
  Unit{}

def Int.pos_add(a: I.Int, b: I.Int) -> {I.Int.pos(a) == True{} : Bool} -> {I.Int.pos(b) == True{} : Bool} -> {I.Int.pos(I.Int.add(a, b)) == True{} : Bool}:
  match a b:
    case I.IPos{m} I.IPos{n}:
      pa => pb => {==}
    case I.IPos{m} I.INeg{n}:
      pa => pb => Empty.absurd({I.Int.pos(I.Int.sub_nat(m, 1n+n)) == True{} : Bool}, Bool.ft(pb))
    case I.INeg{m} b2:
      pa => pb => Empty.absurd({I.Int.pos(I.Int.add(I.INeg{m}, b2)) == True{} : Bool}, Bool.ft(pa))

def Int.pos_mul(a: I.Int, b: I.Int) -> {I.Int.pos(a) == True{} : Bool} -> {I.Int.pos(b) == True{} : Bool} -> {I.Int.pos(I.Int.mul(a, b)) == True{} : Bool}:
  match a b:
    case I.IPos{0n} I.IPos{n}:
      pa => pb => {==}
    case I.IPos{1n+m} I.IPos{n}:
      pa => pb => {==}
    case I.IPos{m} I.INeg{n}:
      pa => pb => Empty.absurd({I.Int.pos(I.Int.mul(I.IPos{m}, I.INeg{n})) == True{} : Bool}, Bool.ft(pb))
    case I.INeg{m} b2:
      pa => pb => Empty.absurd({I.Int.pos(I.Int.mul(I.INeg{m}, b2)) == True{} : Bool}, Bool.ft(pa))

def Int.pos_abs(a: I.Int) -> {I.Int.pos(I.Int.abs(a)) == True{} : Bool}:
  match a:
    case I.IPos{n}:
      {==}
    case I.INeg{n}:
      {==}

def Int.abs_neg(a: I.Int) -> {I.Int.abs(I.Int.neg(a)) == I.Int.abs(a) : I.Int}:
  match a:
    case I.IPos{0n}:
      {==}
    case I.IPos{1n+m}:
      {==}
    case I.INeg{m}:
      {==}

def Int.abs_mul.go(+a: I.Int, +b: I.Int) -> {I.Int.abs(I.Int.mul(a, b)) == I.Int.mul(I.Int.abs(a), I.Int.abs(b)) : I.Int}:
  match a b:
    case I.IPos{m} I.IPos{n}:
      {==}
    case I.INeg{m} I.INeg{n}:
      {==}
    case I.IPos{0n} I.INeg{n}:
      {==}
    case I.IPos{1n+(+m)} I.INeg{+n}:
      Equal.cong(Nat, I.Int, w => I.IPos{1n+w}, Nat.add(Nat.mul(m, 1n+n), n), Nat.add(n, Nat.mul(m, 1n+n)), NL.Nat.add_comm(Nat.mul(m, 1n+n), n))
    case I.INeg{+m} I.IPos{0n}:
      Equal.cong(Nat, I.Int, w => I.IPos{w}, 0n, Nat.mul(m, 0n), Equal.sym(Nat, Nat.mul(m, 0n), 0n, NL.Nat.mul_zero_r(m)))
    case I.INeg{+m} I.IPos{1n+(+n)}:
      Equal.cong(Nat, I.Int, w => I.IPos{1n+w}, Nat.add(Nat.mul(n, 1n+m), m), Nat.add(n, Nat.mul(m, 1n+n)), Nat.cross(m, n))

def Int.abs_mul(a: I.Int, b: I.Int) -> {I.Int.abs(I.Int.mul(a, b)) == I.Int.mul(I.Int.abs(a), I.Int.abs(b)) : I.Int}:
  Int.abs_mul.go(a, b)

# |a| = P(a) + Q(a)
def Abs.pair(+a: I.Int) -> {I.Int.abs(a) == I.IPos{Nat.add(P(a), Q(a))} : I.Int}:
  match a:
    case I.IPos{+n}:
      Equal.cong(Nat, I.Int, w => I.IPos{w}, n, Nat.add(n, 0n), Equal.sym(Nat, Nat.add(n, 0n), n, NL.Nat.add_zero_r(n)))
    case I.INeg{n}:
      {==}

# (d + m) - m is nonnegative
def Pos.diff(+d: Nat, +m: Nat) -> {I.Int.pos(I.Int.add(I.IPos{Nat.add(d, m)}, I.Int.neg(I.IPos{m}))) == True{} : Bool}:
  +nm = I.Int.neg(I.IPos{m})
  +x = I.Int.add(I.IPos{Nat.add(d, m)}, nm)
  +s1 = I.Int.sub_nat(Nat.add(Nat.add(d, m), P(nm)), Nat.add(0n, Q(nm)))
  +s2 = I.Int.sub_nat(Nat.add(Nat.add(d, m), 0n), m)
  +s3 = I.Int.sub_nat(Nat.add(m, d), Nat.add(m, 0n))
  +e = Equal.trans(I.Int, x, s1, I.IPos{d}, Add.pair(I.IPos{Nat.add(d, m)}, nm),
    Equal.trans(I.Int, s1, s2, I.IPos{d},
      SN.cong(Nat.add(Nat.add(d, m), P(nm)), Nat.add(Nat.add(d, m), 0n), Q(nm), m,
        Equal.cong(Nat, Nat, w => Nat.add(Nat.add(d, m), w), P(nm), 0n, Neg.P(I.IPos{m})), Neg.Q(I.IPos{m})),
      Equal.trans(I.Int, s2, s3, I.IPos{d},
        SN.cong(Nat.add(Nat.add(d, m), 0n), Nat.add(m, d), m, Nat.add(m, 0n),
          Equal.trans(Nat, Nat.add(Nat.add(d, m), 0n), Nat.add(d, m), Nat.add(m, d), NL.Nat.add_zero_r(Nat.add(d, m)), NL.Nat.add_comm(d, m)),
          Equal.sym(Nat, Nat.add(m, 0n), m, NL.Nat.add_zero_r(m))),
        Equal.trans(I.Int, s3, I.Int.sub_nat(d, 0n), I.IPos{d}, SN.shift(m, d, 0n), SN.zero_r(d)))))
  %Equal.sym(I.Int, x, I.IPos{d}, e) : {I.Int.pos(_) == True{} : Bool}
  {==}

# |a + b| <= |a| + |b|
def Int.tri.go(+a: I.Int, +b: I.Int) -> {I.Int.pos(I.Int.add(I.Int.add(I.Int.abs(a), I.Int.abs(b)), I.Int.neg(I.Int.abs(I.Int.add(a, b))))) == True{} : Bool}:
  +pab = Nat.add(P(a), P(b))
  +qab = Nat.add(Q(a), Q(b))
  +s = I.Int.sub_nat(pab, qab)
  +x = P(s)
  +y = Q(s)
  +k = cm(pab, qab)
  +mm = Nat.add(x, y)
  +d = Nat.add(k, k)
  # |a| + |b| = d + mm
  +n1 = Nat.add(Nat.add(P(a), Q(a)), Nat.add(P(b), Q(b)))
  +n2 = Nat.add(pab, qab)
  +n3 = Nat.add(Nat.add(k, x), Nat.add(k, y))
  +en = Equal.trans(Nat, n1, n2, Nat.add(d, mm), NL.Nat.add_4(P(a), Q(a), P(b), Q(b)),
    Equal.trans(Nat, n2, n3, Nat.add(d, mm), Nat.cong2(pab, Nat.add(k, x), qab, Nat.add(k, y), SN.e1(pab, qab), SN.e2(pab, qab)),
      NL.Nat.add_4(k, x, k, y)))
  +ea = Equal.trans(I.Int, I.Int.add(I.Int.abs(a), I.Int.abs(b)), I.Int.add(I.IPos{Nat.add(P(a), Q(a))}, I.IPos{Nat.add(P(b), Q(b))}), I.IPos{Nat.add(d, mm)},
    Equal.trans(I.Int, I.Int.add(I.Int.abs(a), I.Int.abs(b)), I.Int.add(I.IPos{Nat.add(P(a), Q(a))}, I.Int.abs(b)), I.Int.add(I.IPos{Nat.add(P(a), Q(a))}, I.IPos{Nat.add(P(b), Q(b))}),
      Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.abs(b)), I.Int.abs(a), I.IPos{Nat.add(P(a), Q(a))}, Abs.pair(a)),
      Equal.cong(I.Int, I.Int, w => I.Int.add(I.IPos{Nat.add(P(a), Q(a))}, w), I.Int.abs(b), I.IPos{Nat.add(P(b), Q(b))}, Abs.pair(b))),
    Equal.cong(Nat, I.Int, w => I.IPos{w}, n1, Nat.add(d, mm), en))
  +eb = Equal.trans(I.Int, I.Int.abs(I.Int.add(a, b)), I.Int.abs(s), I.IPos{mm},
    Equal.cong(I.Int, I.Int, w => I.Int.abs(w), I.Int.add(a, b), s, Add.pair(a, b)),
    Abs.pair(s))
  +lhs = I.Int.add(I.Int.add(I.Int.abs(a), I.Int.abs(b)), I.Int.neg(I.Int.abs(I.Int.add(a, b))))
  +rhs = I.Int.add(I.IPos{Nat.add(d, mm)}, I.Int.neg(I.IPos{mm}))
  +e = Equal.trans(I.Int, lhs, I.Int.add(I.IPos{Nat.add(d, mm)}, I.Int.neg(I.Int.abs(I.Int.add(a, b)))), rhs,
    Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.neg(I.Int.abs(I.Int.add(a, b)))), I.Int.add(I.Int.abs(a), I.Int.abs(b)), I.IPos{Nat.add(d, mm)}, ea),
    Equal.cong(I.Int, I.Int, w => I.Int.add(I.IPos{Nat.add(d, mm)}, I.Int.neg(w)), I.Int.abs(I.Int.add(a, b)), I.IPos{mm}, eb))
  %Equal.sym(I.Int, lhs, rhs, e) : {I.Int.pos(_) == True{} : Bool}
  Pos.diff(d, mm)

def Int.tri(a: I.Int, b: I.Int) -> {I.Int.pos(I.Int.add(I.Int.add(I.Int.abs(a), I.Int.abs(b)), I.Int.neg(I.Int.abs(I.Int.add(a, b))))) == True{} : Bool}:
  Int.tri.go(a, b)

# The instance
# ------------
# The laws above with plain parameters, so that each has exactly the type
# src/ring.bend and src/err.bend name (a + parameter changes a function's
# type). Pass these as the ring and order hypotheses at T = Int.

def Int.r.add_assoc(a: I.Int, b: I.Int, c: I.Int) -> {I.Int.add(I.Int.add(a, b), c) == I.Int.add(a, I.Int.add(b, c)) : I.Int}:
  Int.add_assoc(a, b, c)

def Int.r.add_comm(a: I.Int, b: I.Int) -> {I.Int.add(a, b) == I.Int.add(b, a) : I.Int}:
  Int.add_comm(a, b)

def Int.r.zero_l(a: I.Int) -> {I.Int.add(I.IPos{0n}, a) == a : I.Int}:
  Int.zero_l(a)

def Int.r.add_inv(a: I.Int) -> {I.Int.add(a, I.Int.neg(a)) == I.IPos{0n} : I.Int}:
  Int.add_inv(a)

def Int.r.mul_assoc(a: I.Int, b: I.Int, c: I.Int) -> {I.Int.mul(I.Int.mul(a, b), c) == I.Int.mul(a, I.Int.mul(b, c)) : I.Int}:
  Int.mul_assoc(a, b, c)

def Int.r.mul_comm(a: I.Int, b: I.Int) -> {I.Int.mul(a, b) == I.Int.mul(b, a) : I.Int}:
  Int.mul_comm(a, b)

def Int.r.unit_r(a: I.Int) -> {I.Int.mul(a, I.IPos{1n}) == a : I.Int}:
  Int.unit_r(a)

def Int.r.dist_l(a: I.Int, b: I.Int, c: I.Int) -> {I.Int.mul(a, I.Int.add(b, c)) == I.Int.add(I.Int.mul(a, b), I.Int.mul(a, c)) : I.Int}:
  Int.dist_l(a, b, c)

def Int.r.neg_add(a: I.Int, b: I.Int) -> {I.Int.neg(I.Int.add(a, b)) == I.Int.add(I.Int.neg(a), I.Int.neg(b)) : I.Int}:
  Int.neg_add(a, b)

def Int.r.neg_mul_l(a: I.Int, b: I.Int) -> {I.Int.mul(I.Int.neg(a), b) == I.Int.neg(I.Int.mul(a, b)) : I.Int}:
  Int.neg_mul_l(a, b)

def Int.r.neg_neg(a: I.Int) -> {I.Int.neg(I.Int.neg(a)) == a : I.Int}:
  Int.neg_neg(a)
