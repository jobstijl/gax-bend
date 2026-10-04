# The ring laws a theorem may assume, as named types. A law over "any ring"
# takes the operations as ~ parameters and exactly the hypotheses its proof
# uses, also as ~ parameters (a ~ proof may be used any number of times;
# issue #848). Fewer hypotheses make a stronger theorem: gp associativity,
# for instance, needs no commutativity.

import Base

def Ring.Assoc(T: Data, op: T -> T -> T) -> Type:
  @a: T -> @b: T -> @c: T -> {op(op(a, b), c) == op(a, op(b, c)) : T}

def Ring.Comm(T: Data, op: T -> T -> T) -> Type:
  @a: T -> @b: T -> {op(a, b) == op(b, a) : T}

# a * (b + c) = a * b + a * c
def Ring.DistL(T: Data, add: T -> T -> T, mul: T -> T -> T) -> Type:
  @a: T -> @b: T -> @c: T -> {mul(a, add(b, c)) == add(mul(a, b), mul(a, c)) : T}

# (a + b) * c = a * c + b * c
def Ring.DistR(T: Data, add: T -> T -> T, mul: T -> T -> T) -> Type:
  @a: T -> @b: T -> @c: T -> {mul(add(a, b), c) == add(mul(a, c), mul(b, c)) : T}

# -(a + b) = -a + -b
def Ring.NegAdd(T: Data, add: T -> T -> T, neg: T -> T) -> Type:
  @a: T -> @b: T -> {neg(add(a, b)) == add(neg(a), neg(b)) : T}

# (-a) * b = -(a * b)
def Ring.NegMulL(T: Data, mul: T -> T -> T, neg: T -> T) -> Type:
  @a: T -> @b: T -> {mul(neg(a), b) == neg(mul(a, b)) : T}

# a * (-b) = -(a * b)
def Ring.NegMulR(T: Data, mul: T -> T -> T, neg: T -> T) -> Type:
  @a: T -> @b: T -> {mul(a, neg(b)) == neg(mul(a, b)) : T}

# -(-a) = a
def Ring.NegNeg(T: Data, neg: T -> T) -> Type:
  @a: T -> {neg(neg(a)) == a : T}

# 1 * a = a
def Ring.UnitL(T: Data, mul: T -> T -> T, one: T) -> Type:
  @a: T -> {mul(one, a) == a : T}

# a * 1 = a
def Ring.UnitR(T: Data, mul: T -> T -> T, one: T) -> Type:
  @a: T -> {mul(a, one) == a : T}
