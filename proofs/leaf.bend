# Leaf lemmas: how the sign flag (-1)^n of Ring.negf moves through the ring
# operations, each from the one ring law it needs.

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S

def Negf.negf(~T: Data, ~neg: T -> T, ~neg_neg: R.Ring.NegNeg(T, neg), n: Bool, m: Bool, a: T)
  -> {S.Ring.negf(~T, ~neg, n, S.Ring.negf(~T, ~neg, m, a)) == S.Ring.negf(~T, ~neg, Bool.xor(n, m), a) : T}:
  match n m:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      neg_neg(a)

def Negf.add(~T: Data, ~add: T -> T -> T, ~neg: T -> T, ~neg_add: R.Ring.NegAdd(T, add, neg), n: Bool, a: T, b: T)
  -> {S.Ring.negf(~T, ~neg, n, add(a, b)) == add(S.Ring.negf(~T, ~neg, n, a), S.Ring.negf(~T, ~neg, n, b)) : T}:
  match n:
    case False{}:
      {==}
    case True{}:
      neg_add(a, b)

def Negf.mul_l(~T: Data, ~mul: T -> T -> T, ~neg: T -> T, ~neg_mul_l: R.Ring.NegMulL(T, mul, neg), n: Bool, a: T, b: T)
  -> {mul(S.Ring.negf(~T, ~neg, n, a), b) == S.Ring.negf(~T, ~neg, n, mul(a, b)) : T}:
  match n:
    case False{}:
      {==}
    case True{}:
      neg_mul_l(a, b)

def Negf.mul_r(~T: Data, ~mul: T -> T -> T, ~neg: T -> T, ~neg_mul_r: R.Ring.NegMulR(T, mul, neg), n: Bool, a: T, b: T)
  -> {mul(a, S.Ring.negf(~T, ~neg, n, b)) == S.Ring.negf(~T, ~neg, n, mul(a, b)) : T}:
  match n:
    case False{}:
      {==}
    case True{}:
      neg_mul_r(a, b)

# equal flags give equal signs
def Negf.flag(~T: Data, ~neg: T -> T, -n: Bool, -m: Bool, -a: T, e: {n == m : Bool})
  -> {S.Ring.negf(~T, ~neg, n, a) == S.Ring.negf(~T, ~neg, m, a) : T}:
  %e : {S.Ring.negf(~T, ~neg, n, a) == S.Ring.negf(~T, ~neg, _, a) : T}
  {==}
