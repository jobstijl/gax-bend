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

# xs negated when s
def Ms.sflip(s: Bool, xs: List<&2, Mono>) -> List<&2, Mono>:
  match s:
    case False{}:
      xs
    case True{}:
      Ms.flip(xs)

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

# Sorting before cancelling
# -------------------------
# Ms.cancel is quadratic. For large terms (CGA's sandwiches run to
# thousands of monomials) NormS flattens with an accumulator, sorts the
# monomials by their variables with a bottom-up merge sort, and cancels
# adjacent opposites with a stack in one pass: O(n log n). No recursive
# call sits inside a choice (Bool.pick computes both arms at run time):
# the merge takes its next step as a parameter.

# the monomials of t, negated when s, in front of acc
def Tm.flatx(t: Tm, +s: Bool, acc: List<&2, Mono>) -> List<&2, Mono>:
  match t:
    case TVar{i}:
      Mono{s, [i]} <> acc
    case TZero{}:
      acc
    case TAdd{a, b}:
      Tm.flatx(a, s, Tm.flatx(b, s, acc))
    case TMul{a, b}:
      Ms.app(Ms.sflip(s, Ms.mul(Tm.flatx(a, False{}, Nil{}), Tm.flatx(b, False{}, Nil{}))), acc)
    case TNeg{a}:
      Tm.flatx(a, Bool.not(s), acc)

# lexicographic order on sorted variable lists
def Vs.le(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} ys2:
      True{}
    case x <> xt Nil{}:
      False{}
    case +x <> xt +y <> yt:
      Bool.or(Nat.is_lt(x, y), Bool.and(Nat.is_eq(x, y), Vs.le(xt, yt)))

def Mono.le(a: Mono, b: Mono) -> Bool:
  match a b:
    case Mono{s, vs} Mono{t, ws}:
      Vs.le(vs, ws)

# whether the next element of a merge comes from xs
def Ms.lehd(xs: List<&2, Mono>, ys: List<&2, Mono>) -> Bool:
  match xs ys:
    case Nil{} ys2:
      False{}
    case x <> xt Nil{}:
      True{}
    case x <> xt y <> yt:
      Mono.le(x, y)

def Ms.merge(+xs: List<&2, Mono>, +ys: List<&2, Mono>, c: Bool) -> List<&2, Mono>:
  match xs ys:
    case Nil{} ys2:
      ys2
    case x <> xt Nil{}:
      x <> xt
    case x <> +xt y <> +yt:
      match c:
        case True{}:
          x <> Ms.merge(xt, ys, Ms.lehd(xt, ys))
        case False{}:
          y <> Ms.merge(xs, yt, Ms.lehd(xs, yt))

# sorted runs: one pass merges neighbours
def Runs.pass(rs: List<&2, List<&2, Mono>>) -> List<&2, List<&2, Mono>>:
  match rs:
    case Nil{}:
      Nil{}
    case +a <> t:
      match t:
        case Nil{}:
          [a]
        case +b <> u:
          Ms.merge(a, b, Ms.lehd(a, b)) <> Runs.pass(u)

def Runs.sort(n: Nat, rs: List<&2, List<&2, Mono>>) -> List<&2, List<&2, Mono>>:
  match n:
    case 0n:
      rs
    case 1n+k:
      Runs.sort(k, Runs.pass(rs))

def Runs.cat(rs: List<&2, List<&2, Mono>>) -> List<&2, Mono>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      Ms.app(r, Runs.cat(t))

def Runs.single(xs: List<&2, Mono>) -> List<&2, List<&2, Mono>>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      [x] <> Runs.single(t)

# sorted by variables (32 passes: lists below 2^32)
def Ms.sort(xs: List<&2, Mono>) -> List<&2, Mono>:
  Runs.cat(Runs.sort(32n, Runs.single(xs)))

# cancel adjacent opposites with a stack
def Cs.step(+m: Mono, st: List<&2, Mono>) -> List<&2, Mono>:
  match st:
    case Nil{}:
      [m]
    case +p <> +t:
      Bool.pick(List<&2, Mono>, Mono.opp(m, p), t, m <> p <> t)

def Cs.go(l: List<&2, Mono>, st: List<&2, Mono>) -> List<&2, Mono>:
  match l:
    case Nil{}:
      st
    case m <> t:
      Cs.go(t, Cs.step(m, st))

# what is left of t after sorting and cancelling: Nil{} means t is zero
def NormS.left(t: Tm) -> List<&2, Mono>:
  Cs.go(Ms.sort(Tm.flatx(t, False{}, Nil{})), Nil{})

# the same over rings with a half, h being variable v
def NormSH.left(+v: Nat, t: Tm) -> List<&2, Mono>:
  +ms = Tm.flatx(t, False{}, Nil{})
  Cs.go(Ms.sort(Ms.lift(v, Ms.maxh(v, ms), ms)), Nil{})

# Lists of identities
# -------------------
# A kernel's law compares all coefficients at once: the evaluations of two
# lists of terms are equal when each pair's difference cancels.

def Tm.evals(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, +env: List<&2, T>, ts: List<&2, Tm>) -> List<&2, T>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, t) <> Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, rest)

def NormSH.alls(+v: Nat, as: List<&2, Tm>, bs: List<&2, Tm>) -> Bool:
  match as bs:
    case Nil{} Nil{}:
      True{}
    case Nil{} b <> bt:
      False{}
    case a <> at Nil{}:
      False{}
    case a <> at b <> bt:
      Bool.and(List.is_empty(&2, Mono, NormSH.left(v, Tm.diff(a, b))), NormSH.alls(v, at, bt))
