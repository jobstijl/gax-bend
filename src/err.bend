# Rounding error of a term (ADR-005, docs/numerics.md). Exact values live
# in an ordered commutative ring T. The computed operations are fadd and
# fmul, each within eps of the exact one: |fadd(x, y) - (x + y)| <=
# eps |x + y| (the standard model; rnd(x + y) is one instance), plus an
# absolute eta when underflow is counted. For a term t (a reified kernel
# field, src/norm.bend):
#   N.Tm.eval at (fadd, fmul)  the computed value; at (add, mul) the exact;
#   Tm.absev  t with |x| at the leaves and + for -: its absolute size;
#   Tm.k      the roundings along the worst path;
#   Err.H     h(k) = (1 + eps)^k - 1.
# proofs/err.bend proves |computed - exact| <= h(k(t)) absev(t).
# Order is positivity: a <= b means pos(b - a).

import Base
import ./norm.bend as N

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

# the standard model for a computed operation: |fop(x, y) - op(x, y)| <=
# eps |op(x, y)|
def Ord.Rel(T: Data, add: T -> T -> T, mul: T -> T -> T, neg: T -> T, abs: T -> T, pos: T -> Bool, eps: T, op: T -> T -> T, fop: T -> T -> T) -> Type:
  @x: T -> @y: T -> {pos(add(mul(eps, abs(op(x, y))), neg(abs(add(fop(x, y), neg(op(x, y))))))) == True{} : Bool}

# With underflow (docs/numerics.md §1): |fop(x, y) - op(x, y)| <=
# eps |op(x, y)| + eta. IEEE binary32 with gradual underflow has eta = 0
# for sums (Hauser 1996) and 2^-150 for products; flushing subnormals to
# zero makes both 2^-126.
def Ord.Approx(T: Data, add: T -> T -> T, mul: T -> T -> T, neg: T -> T, abs: T -> T, pos: T -> Bool, eps: T, eta: T, op: T -> T -> T, fop: T -> T -> T) -> Type:
  @x: T -> @y: T -> {pos(add(add(mul(eps, abs(op(x, y))), eta), neg(abs(add(fop(x, y), neg(op(x, y))))))) == True{} : Bool}

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

# Kernels: every output field of a kernel is a term, so a kernel's bound
# is a list of term bounds. Over the terms ts with environment env:
def Tm.evals(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, +env: List<&2, T>, ts: List<&2, N.Tm>) -> List<&2, T>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, t) <> Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, r)

def Tm.absevs(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~abs: T -> T, +env: List<&2, T>, ts: List<&2, N.Tm>) -> List<&2, T>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      Tm.absev(~T, ~zero, ~add, ~mul, ~abs, env, t) <> Tm.absevs(~T, ~zero, ~add, ~mul, ~abs, env, r)

def Tm.ks(ts: List<&2, N.Tm>) -> List<&2, Nat>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      Tm.k(t) <> Tm.ks(r)

# field by field: |f - e| <= h(k) a, for computed fs, exact es, absolute
# sizes as and depths ks
def Err.Fields(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~pos: T -> Bool, ~abs: T -> T, ~eps: T,
  fs: List<&2, T>, es: List<&2, T>, as: List<&2, T>, ks: List<&2, Nat>) -> Type:
  match fs:
    case Nil{}:
      Unit
    case f <> ft:
      match es:
        case Nil{}:
          Unit
        case e <> et:
          match as:
            case Nil{}:
              Unit
            case a <> at:
              match ks:
                case Nil{}:
                  Unit
                case k <> kt:
                  {pos(add(mul(Err.H(~T, ~zero, ~one, ~add, ~mul, ~eps, k), a), neg(abs(add(f, neg(e)))))) == True{} : Bool} & Err.Fields(~T, ~zero, ~one, ~add, ~mul, ~neg, ~pos, ~abs, ~eps, ft, et, at, kt)

# the absolute parts D(t) of a kernel's fields
def Tm.Ds(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~abs: T -> T, ~eps: T, ~eta_a: T, ~eta_m: T, +env: List<&2, T>, ts: List<&2, N.Tm>) -> List<&2, T>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      Err.D(~T, ~zero, ~one, ~add, ~mul, ~abs, ~eps, ~eta_a, ~eta_m, env, t) <> Tm.Ds(~T, ~zero, ~one, ~add, ~mul, ~abs, ~eps, ~eta_a, ~eta_m, env, r)

# field by field, with underflow: |f - e| <= h(k) a + d
def Err.Fields_u(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~pos: T -> Bool, ~abs: T -> T, ~eps: T,
  fs: List<&2, T>, es: List<&2, T>, as: List<&2, T>, ds: List<&2, T>, ks: List<&2, Nat>) -> Type:
  match fs:
    case Nil{}:
      Unit
    case f <> ft:
      match es:
        case Nil{}:
          Unit
        case e <> et:
          match as:
            case Nil{}:
              Unit
            case a <> at:
              match ds:
                case Nil{}:
                  Unit
                case d <> dt:
                  match ks:
                    case Nil{}:
                      Unit
                    case k <> kt:
                      {pos(add(add(mul(Err.H(~T, ~zero, ~one, ~add, ~mul, ~eps, k), a), d), neg(abs(add(f, neg(e)))))) == True{} : Bool} & Err.Fields_u(~T, ~zero, ~one, ~add, ~mul, ~neg, ~pos, ~abs, ~eps, ft, et, at, dt, kt)

# the depth semiring: a generic kernel run on Nat with these operations
# and zero inputs computes k for each output field
def Err.dadd(a: Nat, b: Nat) -> Nat:
  1n+Nat.max(a, b)

def Err.dmul(a: Nat, b: Nat) -> Nat:
  1n+Nat.add(a, b)

# Tracking (docs/numerics.md §3): the bound from computed quantities only.
# The absolute size A = absev(t) is not computed exactly at run time; what
# is computed is A^ = the term evaluated with fadd and fmul on |leaves|,
# negation dropped. proofs/err.bend (Err.track) shows
#   |computed(t) - eval(t)| (1 - h) <= h A^,   h = h(k(t)) < 1.

def Ord.AbsAbs(T: Data, abs: T -> T) -> Type:
  @a: T -> {abs(abs(a)) == abs(a) : T}

# a <= |a|
def Ord.LeAbs(T: Data, add: T -> T -> T, neg: T -> T, abs: T -> T, pos: T -> Bool) -> Type:
  @a: T -> {pos(add(abs(a), neg(a))) == True{} : Bool}

# t with its negations dropped
def Tm.strip(t: N.Tm) -> N.Tm:
  match t:
    case N.TVar{i}:
      N.TVar{i}
    case N.TZero{}:
      N.TZero{}
    case N.TAdd{a, b}:
      N.TAdd{Tm.strip(a), Tm.strip(b)}
    case N.TMul{a, b}:
      N.TMul{Tm.strip(a), Tm.strip(b)}
    case N.TNeg{a}:
      Tm.strip(a)

# every field stripped
def Tm.strips(ts: List<&2, N.Tm>) -> List<&2, N.Tm>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      Tm.strip(t) <> Tm.strips(r)

# field by field, tracked: given h(k) <= 1, |f - e| (1 - h(k)) <= h(k) ah,
# for computed fs, exact es, computed sizes ahs and depths ks
def Err.Fields_t(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~pos: T -> Bool, ~abs: T -> T, ~eps: T,
  fs: List<&2, T>, es: List<&2, T>, ahs: List<&2, T>, ks: List<&2, Nat>) -> Type:
  match fs:
    case Nil{}:
      Unit
    case f <> ft:
      match es:
        case Nil{}:
          Unit
        case e <> et:
          match ahs:
            case Nil{}:
              Unit
            case ah <> at:
              match ks:
                case Nil{}:
                  Unit
                case k <> kt:
                  ({pos(add(one, neg(Err.H(~T, ~zero, ~one, ~add, ~mul, ~eps, k)))) == True{} : Bool} -> {pos(add(mul(Err.H(~T, ~zero, ~one, ~add, ~mul, ~eps, k), ah), neg(mul(abs(add(f, neg(e))), add(one, neg(Err.H(~T, ~zero, ~one, ~add, ~mul, ~eps, k))))))) == True{} : Bool}) & Err.Fields_t(~T, ~zero, ~one, ~add, ~mul, ~neg, ~pos, ~abs, ~eps, ft, et, at, kt)

# |x| for every variable
def Env.abs(~T: Data, ~abs: T -> T, env: List<&2, T>) -> List<&2, T>:
  match env:
    case Nil{}:
      Nil{}
    case x <> t:
      abs(x) <> Env.abs(~T, ~abs, t)
