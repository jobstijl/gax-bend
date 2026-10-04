# Ring identities by cancellation. A term over add, mul, neg and zero is
# reified as a Tm whose variables index an environment. Flattening it gives
# a list of signed monomials (every coefficient is +1 or -1; a coefficient
# 2 is a monomial listed twice), each with its variables sorted. Norm.zero
# cancels opposite monomials in pairs; when nothing is left, the term is
# zero in every commutative ring (proofs/norm.bend proves it). Equalities
# a == b are checked as a + (-b) == 0.
#
# Every function is structural and computes both arms of a choice
# (Bool.pick), so it needs no fuel and the checker can run it on closed
# terms.

import Base

# Terms
# -----

type Tm is Data:
  TVar{i: Nat}
  TZero{}
  TAdd{a: Tm, b: Tm}
  TMul{a: Tm, b: Tm}
  TNeg{a: Tm}

# the ring operations on terms: running a generic operation at T = Tm on
# variable leaves reifies it, so a proof can name the term without
# printing it
def Tm.add(a: Tm, b: Tm) -> Tm:
  TAdd{a, b}

def Tm.mul(a: Tm, b: Tm) -> Tm:
  TMul{a, b}

def Tm.neg(a: Tm) -> Tm:
  TNeg{a}

# variable i of the environment (zero past its end)
def Env.at(~T: Data, ~zero: T, env: List<&2, T>, i: Nat) -> T:
  match env:
    case Nil{}:
      zero
    case x <> t:
      match i:
        case 0n:
          x
        case 1n+j:
          Env.at(~T, ~zero, t, j)

def Tm.eval(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, +env: List<&2, T>, t: Tm) -> T:
  match t:
    case TVar{i}:
      Env.at(~T, ~zero, env, i)
    case TZero{}:
      zero
    case TAdd{a, b}:
      add(Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b))
    case TMul{a, b}:
      mul(Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b))
    case TNeg{a}:
      neg(Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a))

# Monomials
# ---------

# s: negated; vs: the variables multiplied, sorted
type Mono is Data:
  Mono{s: Bool, vs: List<&2, Nat>}

def Sgn.ap(~T: Data, ~neg: T -> T, s: Bool, x: T) -> T:
  match s:
    case False{}:
      x
    case True{}:
      neg(x)

def Vs.prod(~T: Data, ~zero: T, ~mul: T -> T -> T, ~one: T, +env: List<&2, T>, vs: List<&2, Nat>) -> T:
  match vs:
    case Nil{}:
      one
    case v <> t:
      mul(Env.at(~T, ~zero, env, v), Vs.prod(~T, ~zero, ~mul, ~one, env, t))

def Mono.eval(~T: Data, ~zero: T, ~mul: T -> T -> T, ~neg: T -> T, ~one: T, +env: List<&2, T>, m: Mono) -> T:
  match m:
    case Mono{s, vs}:
      Sgn.ap(~T, ~neg, s, Vs.prod(~T, ~zero, ~mul, ~one, env, vs))

def Ms.sum(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~one: T, +env: List<&2, T>, ms: List<&2, Mono>) -> T:
  match ms:
    case Nil{}:
      zero
    case m <> t:
      add(Mono.eval(~T, ~zero, ~mul, ~neg, ~one, env, m), Ms.sum(~T, ~zero, ~add, ~mul, ~neg, ~one, env, t))

# Sorted variable lists
# ---------------------

# x into the sorted list ys
def Vs.ins(+x: Nat, ys: List<&2, Nat>) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      [x]
    case +y <> +t:
      Bool.pick(List<&2, Nat>, Nat.is_le(x, y), x <> y <> t, y <> Vs.ins(x, t))

def Vs.merge(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case x <> t:
      Vs.ins(x, Vs.merge(t, ys))

def Vs.eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> yt:
      False{}
    case x <> xt Nil{}:
      False{}
    case x <> xt y <> yt:
      Bool.and(Nat.is_eq(x, y), Vs.eq(xt, yt))

# Lists of monomials
# ------------------

def Mono.mul(a: Mono, b: Mono) -> Mono:
  match a b:
    case Mono{s, vs} Mono{t, ws}:
      Mono{Bool.xor(s, t), Vs.merge(vs, ws)}

def Mono.flip(a: Mono) -> Mono:
  match a:
    case Mono{s, vs}:
      Mono{Bool.not(s), vs}

def Ms.app(xs: List<&2, Mono>, ys: List<&2, Mono>) -> List<&2, Mono>:
  match xs:
    case Nil{}:
      ys
    case x <> t:
      x <> Ms.app(t, ys)

def Ms.flip(xs: List<&2, Mono>) -> List<&2, Mono>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      Mono.flip(x) <> Ms.flip(t)

# x times each of ys
def Ms.scale(+x: Mono, ys: List<&2, Mono>) -> List<&2, Mono>:
  match ys:
    case Nil{}:
      Nil{}
    case y <> t:
      Mono.mul(x, y) <> Ms.scale(x, t)

def Ms.mul(xs: List<&2, Mono>, +ys: List<&2, Mono>) -> List<&2, Mono>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      Ms.app(Ms.scale(x, ys), Ms.mul(t, ys))

def Tm.flat(t: Tm) -> List<&2, Mono>:
  match t:
    case TVar{i}:
      [Mono{False{}, [i]}]
    case TZero{}:
      Nil{}
    case TAdd{a, b}:
      Ms.app(Tm.flat(a), Tm.flat(b))
    case TMul{a, b}:
      Ms.mul(Tm.flat(a), Tm.flat(b))
    case TNeg{a}:
      Ms.flip(Tm.flat(a))

# Cancellation
# ------------

# a and b are opposite: the same variables, opposite signs
def Mono.opp(a: Mono, b: Mono) -> Bool:
  match a b:
    case Mono{s, vs} Mono{t, ws}:
      Bool.and(Bool.xor(s, t), Vs.eq(vs, ws))

# ps with the first monomial opposite to m removed, or with m appended
def Ms.ins(+m: Mono, ps: List<&2, Mono>) -> List<&2, Mono>:
  match ps:
    case Nil{}:
      [m]
    case +p <> +t:
      Bool.pick(List<&2, Mono>, Mono.opp(m, p), t, p <> Ms.ins(m, t))

# the monomials of l and ps left after cancelling opposite pairs
def Ms.cancel(l: List<&2, Mono>, ps: List<&2, Mono>) -> List<&2, Mono>:
  match l:
    case Nil{}:
      ps
    case m <> t:
      Ms.cancel(t, Ms.ins(m, ps))

# what is left of t after cancellation: Nil{} means t is zero
def Norm.left(t: Tm) -> List<&2, Mono>:
  Ms.cancel(Tm.flat(t), Nil{})

# a == b as a term that is zero
def Tm.diff(a: Tm, b: Tm) -> Tm:
  TAdd{a, TNeg{b}}

# Identities over rings with a half
# ---------------------------------
# A change of basis such as CGA's null basis (eo = ½(e- - e+)) brings in
# ½. With h one of the variables and h + h = 1 in the ring, every monomial
# m h^k equals m h^(k+1) + m h^(k+1). NormH.left lifts every monomial to the
# same power of h, so that opposite ones cancel, and then cancels. This
# decides every identity that holds in all commutative rings with h = ½.

def Vs.count(+v: Nat, vs: List<&2, Nat>) -> Nat:
  match vs:
    case Nil{}:
      0n
    case w <> t:
      +c = Vs.count(v, t)
      Bool.pick(Nat, Nat.is_eq(v, w), 1n+c, c)

def Ms.maxh(+v: Nat, ms: List<&2, Mono>) -> Nat:
  match ms:
    case Nil{}:
      0n
    case Mono{s, vs} <> t:
      Nat.max(Vs.count(v, vs), Ms.maxh(v, t))

# 2^k copies of m with k more factors h
def Mono.lift(+v: Nat, k: Nat, m: Mono) -> List<&2, Mono>:
  match k:
    case 0n:
      [m]
    case 1n+j:
      match m:
        case Mono{+s, vs}:
          +l = Mono.lift(v, j, Mono{s, Vs.ins(v, vs)})
          Ms.app(l, l)

# every monomial lifted to the power n of h
def Ms.lift(+v: Nat, +n: Nat, ms: List<&2, Mono>) -> List<&2, Mono>:
  match ms:
    case Nil{}:
      Nil{}
    case Mono{+s, +vs} <> t:
      Ms.app(Mono.lift(v, Nat.sub(n, Vs.count(v, vs)), Mono{s, vs}), Ms.lift(v, n, t))

# what is left of t after lifting and cancellation, with h variable v
def NormH.left(+v: Nat, t: Tm) -> List<&2, Mono>:
  +ms = Tm.flat(t)
  Ms.cancel(Ms.lift(v, Ms.maxh(v, ms), ms), Nil{})
