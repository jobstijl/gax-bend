# Nat is a commutative semiring: the laws of Base's Nat.add and Nat.mul,
# by induction. Nat.add and Nat.mul recurse on their first argument, so
# laws about the first argument hold by computation and the rest follow
# from these. The foundation of proofs/int.bend.

import Base

# Addition
# --------

def Nat.add_zero_r(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, Nat.add_zero_r(p))

def Nat.add_succ_r(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), Nat.add_succ_r(p, b))

def Nat.add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, Nat.add_zero_r(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, b), Nat.add(b, p), Nat.add_comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), Nat.add_succ_r(b, p)))

def Nat.add_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), Nat.add_assoc(p, b, c))

# a + (b + c) = b + (a + c)
def Nat.add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Nat.add_assoc(a, b, c)),
    Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c), Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, x => Nat.add(x, c), Nat.add(a, b), Nat.add(b, a), Nat.add_comm(a, b)),
      Nat.add_assoc(b, a, c)))

# (a + b) + (c + d) = (a + c) + (b + d)
def Nat.add_4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)),
    Nat.add_assoc(a, b, Nat.add(c, d)),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(a, Nat.add(c, Nat.add(b, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)),
      Equal.cong(Nat, Nat, x => Nat.add(a, x), Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), Nat.add_swap(b, c, d)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), Nat.add_assoc(a, c, Nat.add(b, d)))))

# Multiplication
# --------------

def Nat.mul_zero_r(+a: Nat) -> {Nat.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.mul_zero_r(p)

def Nat.mul_one_r(+a: Nat) -> {Nat.mul(a, 1n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.mul(p, 1n), p, Nat.mul_one_r(p))

# a (1 + b) = a + a b
def Nat.mul_succ_r(+a: Nat, +b: Nat) -> {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(b, Nat.mul(p, 1n+b)), Nat.add(p, Nat.add(b, Nat.mul(p, b))),
        Equal.trans(Nat, Nat.add(b, Nat.mul(p, 1n+b)), Nat.add(b, Nat.add(p, Nat.mul(p, b))), Nat.add(p, Nat.add(b, Nat.mul(p, b))),
          Equal.cong(Nat, Nat, x => Nat.add(b, x), Nat.mul(p, 1n+b), Nat.add(p, Nat.mul(p, b)), Nat.mul_succ_r(p, b)),
          Nat.add_swap(b, p, Nat.mul(p, b))))

def Nat.mul_comm(+a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, Nat.mul_zero_r(b))
    case 1n+p:
      Equal.trans(Nat, Nat.add(b, Nat.mul(p, b)), Nat.add(b, Nat.mul(b, p)), Nat.mul(b, 1n+p),
        Equal.cong(Nat, Nat, x => Nat.add(b, x), Nat.mul(p, b), Nat.mul(b, p), Nat.mul_comm(p, b)),
        Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), Nat.mul_succ_r(b, p)))

# (a + b) c = a c + b c
def Nat.mul_dist_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.add(c, Nat.mul(Nat.add(p, b), c)), Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))), Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)),
        Equal.cong(Nat, Nat, x => Nat.add(c, x), Nat.mul(Nat.add(p, b), c), Nat.add(Nat.mul(p, c), Nat.mul(b, c)), Nat.mul_dist_r(p, b, c)),
        Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)), Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))), Nat.add_assoc(c, Nat.mul(p, c), Nat.mul(b, c))))

# a (b + c) = a b + a c
def Nat.mul_dist_l(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}:
  Equal.trans(Nat, Nat.mul(a, Nat.add(b, c)), Nat.mul(Nat.add(b, c), a), Nat.add(Nat.mul(a, b), Nat.mul(a, c)),
    Nat.mul_comm(a, Nat.add(b, c)),
    Equal.trans(Nat, Nat.mul(Nat.add(b, c), a), Nat.add(Nat.mul(b, a), Nat.mul(c, a)), Nat.add(Nat.mul(a, b), Nat.mul(a, c)),
      Nat.mul_dist_r(b, c, a),
      Equal.trans(Nat, Nat.add(Nat.mul(b, a), Nat.mul(c, a)), Nat.add(Nat.mul(a, b), Nat.mul(c, a)), Nat.add(Nat.mul(a, b), Nat.mul(a, c)),
        Equal.cong(Nat, Nat, x => Nat.add(x, Nat.mul(c, a)), Nat.mul(b, a), Nat.mul(a, b), Nat.mul_comm(b, a)),
        Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(a, b), x), Nat.mul(c, a), Nat.mul(a, c), Nat.mul_comm(c, a)))))

def Nat.mul_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.mul(Nat.add(b, Nat.mul(p, b)), c), Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)), Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))),
        Nat.mul_dist_r(b, Nat.mul(p, b), c),
        Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(b, c), x), Nat.mul(Nat.mul(p, b), c), Nat.mul(p, Nat.mul(b, c)), Nat.mul_assoc(p, b, c)))
