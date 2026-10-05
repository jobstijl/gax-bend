# Approximate inputs (docs/numerics.md §3, "A type for it"). An Approx is a
# value v with a bound b on its distance from an exact value x it stands
# for: |v - x| <= b. A kernel run on Approx inputs, with computed
# operations, returns Approx outputs whose bounds come from two sources:
# the rounding of this run, h(k) A' (A' the absolute size at the computed
# inputs, proofs/err.bend), and the inputs' own error carried through the
# kernel, D. D is the kernel run in the size-deviation semiring Ad below,
# on (|x|, b) per input: proofs/approx.bend shows
#   |eval(env', t) - eval(env, t)| <= dev(env, del, t)
# whenever every |env'_i - env_i| <= del_i.

import Base
import ./norm.bend as N
import ./err.bend as E

type Approx<T: Data> is Data:
  Approx{v: T, b: T}

# the deviation of term t's value when each input i moves by at most del_i,
# around the exact inputs env: a product's error is da (|b| + db) + |a| db
def Tm.dev(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~abs: T -> T, +env: List<&2, T>, +del: List<&2, T>, t: N.Tm) -> T:
  match t:
    case N.TVar{i}:
      N.Env.at(~T, ~zero, del, i)
    case N.TZero{}:
      zero
    case N.TAdd{a, b}:
      add(Tm.dev(~T, ~zero, ~add, ~mul, ~abs, env, del, a), Tm.dev(~T, ~zero, ~add, ~mul, ~abs, env, del, b))
    case N.TMul{+a, +b}:
      add(mul(Tm.dev(~T, ~zero, ~add, ~mul, ~abs, env, del, a), add(E.Tm.absev(~T, ~zero, ~add, ~mul, ~abs, env, b), Tm.dev(~T, ~zero, ~add, ~mul, ~abs, env, del, b))),
        mul(E.Tm.absev(~T, ~zero, ~add, ~mul, ~abs, env, a), Tm.dev(~T, ~zero, ~add, ~mul, ~abs, env, del, b)))
    case N.TNeg{a}:
      Tm.dev(~T, ~zero, ~add, ~mul, ~abs, env, del, a)

def Tm.devs(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~abs: T -> T, +env: List<&2, T>, +del: List<&2, T>, ts: List<&2, N.Tm>) -> List<&2, T>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      Tm.dev(~T, ~zero, ~add, ~mul, ~abs, env, del, t) <> Tm.devs(~T, ~zero, ~add, ~mul, ~abs, env, del, r)

# every input within its bound: |env2_i - env_i| <= del_i, lists of one length
def Close(~T: Data, ~add: T -> T -> T, ~neg: T -> T, ~abs: T -> T, ~pos: T -> Bool, env2: List<&2, T>, env: List<&2, T>, del: List<&2, T>) -> Bool:
  match env2:
    case Nil{}:
      match env:
        case Nil{}:
          match del:
            case Nil{}:
              True{}
            case d <> dt:
              False{}
        case x <> xt:
          False{}
    case x2 <> t2:
      match env:
        case Nil{}:
          False{}
        case x <> xt:
          match del:
            case Nil{}:
              False{}
            case d <> dt:
              Bool.and(pos(add(d, neg(abs(add(x2, neg(x)))))), Close(~T, ~add, ~neg, ~abs, ~pos, t2, xt, dt))

# field by field: |f - e| <= h(k) a2 + d, for computed fs at the moved
# inputs, exact es at the exact inputs, sizes a2s at the moved inputs,
# deviations ds and depths ks
def Err.Fields_a(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~pos: T -> Bool, ~abs: T -> T, ~eps: T,
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
                      {pos(add(add(mul(E.Err.H(~T, ~zero, ~one, ~add, ~mul, ~eps, k), a), d), neg(abs(add(f, neg(e)))))) == True{} : Bool} & Err.Fields_a(~T, ~zero, ~one, ~add, ~mul, ~neg, ~pos, ~abs, ~eps, ft, et, at, dt, kt)

# The size-deviation semiring: a kernel run on Ad{|x_i|, del_i} computes, in
# d, the deviation Tm.dev of each output (and in a, its absolute size)
type Ad<T: Data> is Data:
  Ad{a: T, d: T}

def Ad.zero(~T: Data, ~zero: T) -> Ad<T>:
  Ad{zero, zero}

def Ad.add(~T: Data, ~add: T -> T -> T, x: Ad<T>, y: Ad<T>) -> Ad<T>:
  match x y:
    case Ad{xa, xd} Ad{ya, yd}:
      Ad{add(xa, ya), add(xd, yd)}

def Ad.mul(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, x: Ad<T>, y: Ad<T>) -> Ad<T>:
  match x y:
    case Ad{+xa, +xd} Ad{+ya, +yd}:
      Ad{mul(xa, ya), add(mul(xd, add(ya, yd)), mul(xa, yd))}

def Ad.d(-T: Data, x: Ad<T>) -> T:
  match x:
    case Ad{a, d}:
      d
