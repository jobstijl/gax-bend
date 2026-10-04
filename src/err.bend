# Rounding error of a term (ADR-005, docs/numerics.md). Exact values live
# in an ordered commutative ring T; a rounded operation is rnd(a op b) for
# a rounding function rnd with |rnd(x) - x| <= eps |x| (the standard model,
# no underflow). For a term t (a reified kernel field, src/norm.bend):
#   Tm.fl     the rounded evaluation, rnd after every add and mul;
#   Tm.absev  t with |x| at the leaves and + for -: its absolute size;
#   Tm.k      the roundings along the worst path;
#   Err.H     h(k) = (1 + eps)^k - 1.
# proofs/err.bend proves |fl(t) - eval(t)| <= h(k(t)) absev(t).
# Order is positivity: a <= b means pos(b - a).

import Base
import ./norm.bend as N

def Tm.fl(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~rnd: T -> T, +env: List<&2, T>, t: N.Tm) -> T:
  match t:
    case N.TVar{i}:
      N.Env.at(~T, ~zero, env, i)
    case N.TZero{}:
      zero
    case N.TAdd{a, b}:
      rnd(add(Tm.fl(~T, ~zero, ~add, ~mul, ~neg, ~rnd, env, a), Tm.fl(~T, ~zero, ~add, ~mul, ~neg, ~rnd, env, b)))
    case N.TMul{a, b}:
      rnd(mul(Tm.fl(~T, ~zero, ~add, ~mul, ~neg, ~rnd, env, a), Tm.fl(~T, ~zero, ~add, ~mul, ~neg, ~rnd, env, b)))
    case N.TNeg{a}:
      neg(Tm.fl(~T, ~zero, ~add, ~mul, ~neg, ~rnd, env, a))

def Tm.absev(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~abs: T -> T, +env: List<&2, T>, t: N.Tm) -> T:
  match t:
    case N.TVar{i}:
      abs(N.Env.at(~T, ~zero, env, i))
    case N.TZero{}:
      zero
    case N.TAdd{a, b}:
      add(Tm.absev(~T, ~zero, ~add, ~mul, ~abs, env, a), Tm.absev(~T, ~zero, ~add, ~mul, ~abs, env, b))
    case N.TMul{a, b}:
      mul(Tm.absev(~T, ~zero, ~add, ~mul, ~abs, env, a), Tm.absev(~T, ~zero, ~add, ~mul, ~abs, env, b))
    case N.TNeg{a}:
      Tm.absev(~T, ~zero, ~add, ~mul, ~abs, env, a)

def Tm.k(t: N.Tm) -> Nat:
  match t:
    case N.TVar{i}:
      0n
    case N.TZero{}:
      0n
    case N.TAdd{a, b}:
      1n+Nat.max(Tm.k(a), Tm.k(b))
    case N.TMul{a, b}:
      1n+Nat.add(Tm.k(a), Tm.k(b))
    case N.TNeg{a}:
      Tm.k(a)

# h(k) = (1 + eps)^k - 1, as h(k + 1) = (1 + eps) h(k) + eps
def Err.H(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~eps: T, k: Nat) -> T:
  match k:
    case 0n:
      zero
    case 1n+j:
      add(mul(add(one, eps), Err.H(~T, ~zero, ~one, ~add, ~mul, ~eps, j)), eps)

# a <= b
def Err.Le(~T: Data, ~pos: T -> Bool, ~add: T -> T -> T, ~neg: T -> T, a: T, b: T) -> Type:
  {pos(add(b, neg(a))) == True{} : Bool}

# The order laws a bound assumes, beside the ring laws (src/ring.bend)

# nonnegatives are closed under + and *
def Ord.PosAdd(T: Data, add: T -> T -> T, pos: T -> Bool) -> Type:
  @a: T -> @b: T -> {pos(a) == True{} : Bool} -> {pos(b) == True{} : Bool} -> {pos(add(a, b)) == True{} : Bool}

def Ord.PosMul(T: Data, mul: T -> T -> T, pos: T -> Bool) -> Type:
  @a: T -> @b: T -> {pos(a) == True{} : Bool} -> {pos(b) == True{} : Bool} -> {pos(mul(a, b)) == True{} : Bool}

def Ord.PosAbs(T: Data, abs: T -> T, pos: T -> Bool) -> Type:
  @a: T -> {pos(abs(a)) == True{} : Bool}

# |a + b| <= |a| + |b|
def Ord.Tri(T: Data, add: T -> T -> T, neg: T -> T, abs: T -> T, pos: T -> Bool) -> Type:
  @a: T -> @b: T -> {pos(add(add(abs(a), abs(b)), neg(abs(add(a, b))))) == True{} : Bool}

def Ord.AbsMul(T: Data, mul: T -> T -> T, abs: T -> T) -> Type:
  @a: T -> @b: T -> {abs(mul(a, b)) == mul(abs(a), abs(b)) : T}

def Ord.AbsNeg(T: Data, neg: T -> T, abs: T -> T) -> Type:
  @a: T -> {abs(neg(a)) == abs(a) : T}

# the standard model: |rnd(x) - x| <= eps |x|
def Ord.Rnd(T: Data, add: T -> T -> T, mul: T -> T -> T, neg: T -> T, abs: T -> T, pos: T -> Bool, eps: T, rnd: T -> T) -> Type:
  @x: T -> {pos(add(mul(eps, abs(x)), neg(abs(add(rnd(x), neg(x)))))) == True{} : Bool}

# With underflow (docs/numerics.md §1): additions and multiplications round
# by separate functions, each within eps |x| + eta. IEEE binary32 with
# gradual underflow has eta = 0 for sums (Hauser 1996) and 2^-150 for
# products; flushing subnormals to zero makes both 2^-126.
def Ord.RndU(T: Data, add: T -> T -> T, mul: T -> T -> T, neg: T -> T, abs: T -> T, pos: T -> Bool, eps: T, eta: T, rnd: T -> T) -> Type:
  @x: T -> {pos(add(add(mul(eps, abs(x)), eta), neg(abs(add(rnd(x), neg(x)))))) == True{} : Bool}

# the evaluation with rnda after each addition, rndm after each product
def Tm.flu(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~rnda: T -> T, ~rndm: T -> T, +env: List<&2, T>, t: N.Tm) -> T:
  match t:
    case N.TVar{i}:
      N.Env.at(~T, ~zero, env, i)
    case N.TZero{}:
      zero
    case N.TAdd{a, b}:
      rnda(add(Tm.flu(~T, ~zero, ~add, ~mul, ~neg, ~rnda, ~rndm, env, a), Tm.flu(~T, ~zero, ~add, ~mul, ~neg, ~rnda, ~rndm, env, b)))
    case N.TMul{a, b}:
      rndm(mul(Tm.flu(~T, ~zero, ~add, ~mul, ~neg, ~rnda, ~rndm, env, a), Tm.flu(~T, ~zero, ~add, ~mul, ~neg, ~rnda, ~rndm, env, b)))
    case N.TNeg{a}:
      neg(Tm.flu(~T, ~zero, ~add, ~mul, ~neg, ~rnda, ~rndm, env, a))

# The absolute part of the bound: zero when eta_a = eta_m = 0.
#   D(a + b) = eta_a + (1 + eps)(D(a) + D(b))
#   D(a b)   = eta_m + (1 + eps)(F(a) D(b) + D(a) F(b) + D(a) D(b)),
# with F(x) = (1 + h(k(x))) absev(x) the bound on |fl(x)| without eta.
def Err.D(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~abs: T -> T, ~eps: T, ~eta_a: T, ~eta_m: T, +env: List<&2, T>, t: N.Tm) -> T:
  match t:
    case N.TVar{i}:
      zero
    case N.TZero{}:
      zero
    case N.TAdd{a, b}:
      +s = add(Err.D(~T, ~zero, ~one, ~add, ~mul, ~abs, ~eps, ~eta_a, ~eta_m, env, a), Err.D(~T, ~zero, ~one, ~add, ~mul, ~abs, ~eps, ~eta_a, ~eta_m, env, b))
      add(eta_a, add(s, mul(eps, s)))
    case N.TMul{+a, +b}:
      +da = Err.D(~T, ~zero, ~one, ~add, ~mul, ~abs, ~eps, ~eta_a, ~eta_m, env, a)
      +db = Err.D(~T, ~zero, ~one, ~add, ~mul, ~abs, ~eps, ~eta_a, ~eta_m, env, b)
      +fa = add(mul(Err.H(~T, ~zero, ~one, ~add, ~mul, ~eps, Tm.k(a)), Tm.absev(~T, ~zero, ~add, ~mul, ~abs, env, a)), Tm.absev(~T, ~zero, ~add, ~mul, ~abs, env, a))
      +fb = add(mul(Err.H(~T, ~zero, ~one, ~add, ~mul, ~eps, Tm.k(b)), Tm.absev(~T, ~zero, ~add, ~mul, ~abs, env, b)), Tm.absev(~T, ~zero, ~add, ~mul, ~abs, env, b))
      +x = add(add(mul(fa, db), mul(da, fb)), mul(da, db))
      add(eta_m, add(x, mul(eps, x)))
    case N.TNeg{a}:
      Err.D(~T, ~zero, ~one, ~add, ~mul, ~abs, ~eps, ~eta_a, ~eta_m, env, a)
