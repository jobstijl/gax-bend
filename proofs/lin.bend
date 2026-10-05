# Linearity (gax law family B): every kernel is linear in each operand it
# is linear in. The generated laws (algebras/*/lin.bend) state, per
# kernel K and per such operand,
#   K(a + a', b) = K(a, b) + K(a', b)   and   K(c a, b) = c K(a, b),
# field by field, and prove each by the ring normaliser through Lin.eqs:
# both sides are evaluated at symbolic coefficients and must normalise to
# the same polynomial.

import Base
import ../src/ring.bend as R
import ../src/norm.bend as N
import ./base.bend as B
import ./norm.bend as NP

# every pair of terms normalises to the same polynomial
def Lin.alls(as: List<&2, N.Tm>, bs: List<&2, N.Tm>) -> Bool:
  match as bs:
    case Nil{} Nil{}:
      True{}
    case Nil{} b <> bt:
      False{}
    case a <> at Nil{}:
      False{}
    case a <> at b <> bt:
      Bool.and(List.is_empty(&2, N.Mono, N.NormS.left(N.Tm.diff(a, b))), Lin.alls(at, bt))

# then their evaluations agree, in every commutative ring
def Lin.eqs(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, as: List<&2, N.Tm>, bs: List<&2, N.Tm>,
  +ok: {Lin.alls(as, bs) == True{} : Bool})
  -> {N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, as) == N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, bs) : List<&2, T>}:
  match as bs:
    case Nil{} Nil{}:
      {==}
    case Nil{} b <> bt:
      B.Bool.tf({Nil{} == N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, b <> bt) : List<&2, T>}, Equal.sym(Bool, False{}, True{}, ok))
    case a <> at Nil{}:
      B.Bool.tf({N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, a <> at) == Nil{} : List<&2, T>}, Equal.sym(Bool, False{}, True{}, ok))
    case +a <> +at +b <> +bt:
      B.Eq.cong2(T, List<&2, T>, List<&2, T>, x => y => x <> y, N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, a), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, b),
        N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, at), N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, bt),
        NP.NormS.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, a, b,
          NP.List.empty_nil(N.Mono, N.NormS.left(N.Tm.diff(a, b)),
            NP.Bool.and_l(List.is_empty(&2, N.Mono, N.NormS.left(N.Tm.diff(a, b))), Lin.alls(at, bt), ok))),
        Lin.eqs(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, at, bt,
          NP.Bool.and_r(List.is_empty(&2, N.Mono, N.NormS.left(N.Tm.diff(a, b))), Lin.alls(at, bt), ok)))
