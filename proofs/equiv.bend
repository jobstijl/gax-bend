# Identities modulo one relation: when t = u + l r is a ring identity (the
# normaliser proves it) and r evaluates to zero, t and u are equal. This
# carries the equivariance laws (algebras/*/equiv.bend) whose versor must
# satisfy a condition, such as a PGA3D motor's m ~m having no e0123 part.

import Base
import ../src/ring.bend as R
import ../src/norm.bend as N
import ./base.bend as B
import ./norm.bend as NP

# every t_i - (u_i + l_i r) cancels
# lists of unequal length fail
def Rel.alls(ts: List<&2, N.Tm>, us: List<&2, N.Tm>, ls: List<&2, N.Tm>, +r: N.Tm) -> Bool:
  match ts:
    case Nil{}:
      match us:
        case Nil{}:
          List.is_empty(&2, N.Tm, ls)
        case u <> ut:
          False{}
    case t <> tt:
      match us:
        case Nil{}:
          False{}
        case u <> ut:
          match ls:
            case Nil{}:
              False{}
            case l <> lt:
              Bool.and(List.is_empty(&2, N.Mono, N.NormS.left(N.Tm.diff(t, N.TAdd{u, N.TMul{l, r}}))), Rel.alls(tt, ut, lt, r))

def Rel.eq(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, +t: N.Tm, +v: N.Tm, +l: N.Tm, +r: N.Tm,
  ok: {N.NormS.left(N.Tm.diff(t, N.TAdd{v, N.TMul{l, r}})) == Nil{} : List<&2, N.Mono>},
  +hr: {N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, r) == zero : T})
  -> {N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, t) == N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, v) : T}:
  +et = N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, t)
  +ev = N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, v)
  +el = N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, l)
  +er = N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, r)
  Equal.trans(T, et, add(ev, mul(el, er)), ev,
    NP.NormS.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, t, N.TAdd{v, N.TMul{l, r}}, ok),
    Equal.trans(T, add(ev, mul(el, er)), add(ev, mul(el, zero)), ev,
      Equal.cong(T, T, w => add(ev, mul(el, w)), er, zero, hr),
      Equal.trans(T, add(ev, mul(el, zero)), add(ev, zero), ev,
        Equal.cong(T, T, w => add(ev, w), mul(el, zero), zero, NP.Alg.mul_zero_r(~T, ~zero, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~dl, el)),
        NP.Alg.zero_r(~T, ~zero, ~add, ~ac, ~z, ev))))

# the evaluations of ts and us agree, given r = 0
def Rel.eqs(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, ts: List<&2, N.Tm>, us: List<&2, N.Tm>, ls: List<&2, N.Tm>, +r: N.Tm,
  +ok: {Rel.alls(ts, us, ls, r) == True{} : Bool}, +hr: {N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, r) == zero : T})
  -> {N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, ts) == N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, us) : List<&2, T>}:
  match ts:
    case Nil{}:
      match us:
        case Nil{}:
          {==}
        case v2 <> vt2:
          B.Bool.tf({Nil{} == N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, v2 <> vt2) : List<&2, T>}, Equal.sym(Bool, False{}, True{}, ok))
    case +t <> +tt:
      match us:
        case Nil{}:
          B.Bool.tf({N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, t <> tt) == Nil{} : List<&2, T>}, Equal.sym(Bool, False{}, True{}, ok))
        case +v <> +vt:
          match ls:
            case Nil{}:
              B.Bool.tf({N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, t <> tt) == N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, v <> vt) : List<&2, T>}, Equal.sym(Bool, False{}, True{}, ok))
            case +l <> +lt:
              B.Eq.cong2(T, List<&2, T>, List<&2, T>, x => y => x <> y, N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, t), N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, v),
                N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, tt), N.Tm.evals(~T, ~zero, ~add, ~mul, ~neg, env, vt),
                Rel.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, t, v, l, r,
                  NP.List.empty_nil(N.Mono, N.NormS.left(N.Tm.diff(t, N.TAdd{v, N.TMul{l, r}})),
                    NP.Bool.and_l(List.is_empty(&2, N.Mono, N.NormS.left(N.Tm.diff(t, N.TAdd{v, N.TMul{l, r}}))), Rel.alls(tt, vt, lt, r), ok)), hr),
                Rel.eqs(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, tt, vt, lt, r,
                  NP.Bool.and_r(List.is_empty(&2, N.Mono, N.NormS.left(N.Tm.diff(t, N.TAdd{v, N.TMul{l, r}}))), Rel.alls(tt, vt, lt, r), ok), hr))

# Several relations
# -----------------

# l1 r1 + l2 r2 + ...
def Tm.lin(ls: List<&2, N.Tm>, rs: List<&2, N.Tm>) -> N.Tm:
  match ls:
    case Nil{}:
      N.TZero{}
    case l <> lt:
      match rs:
        case Nil{}:
          N.TZero{}
        case r <> rt:
          N.TAdd{N.TMul{l, r}, Tm.lin(lt, rt)}

# every r in rs evaluates to zero
def Zs(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, env: List<&2, T>, rs: List<&2, N.Tm>) -> Type:
  match rs:
    case Nil{}:
      Unit
    case r <> rt:
      {N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, r) == zero : T} & Zs(~T, ~zero, ~add, ~mul, ~neg, env, rt)

def Lin.zero(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~dl: R.Ring.DistL(T, add, mul), +env: List<&2, T>, ls: List<&2, N.Tm>, rs: List<&2, N.Tm>, hz: Zs(~T, ~zero, ~add, ~mul, ~neg, env, rs))
  -> {N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, Tm.lin(ls, rs)) == zero : T}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +lt:
      match rs:
        case Nil{}:
          {==}
        case +r <> +rt:
          (h, ht) = hz
          +el = N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, l)
          +er = N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, r)
          +rest = N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, Tm.lin(lt, rt))
          Equal.trans(T, add(mul(el, er), rest), add(mul(el, zero), rest), zero,
            Equal.cong(T, T, w => add(mul(el, w), rest), er, zero, h),
            Equal.trans(T, add(mul(el, zero), rest), add(zero, rest), zero,
              Equal.cong(T, T, w => add(w, rest), mul(el, zero), zero, NP.Alg.mul_zero_r(~T, ~zero, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~dl, el)),
              Equal.trans(T, add(zero, rest), rest, zero, z(rest),
                Lin.zero(~T, ~zero, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~dl, env, lt, rt, ht))))

# t = v + l1 r1 + l2 r2 + ... as a ring identity, and every r_i = 0: t = v
def Rel.many(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), +env: List<&2, T>, +t: N.Tm, +v: N.Tm, +ls: List<&2, N.Tm>, +rs: List<&2, N.Tm>,
  ok: {N.NormS.left(N.Tm.diff(t, N.TAdd{v, Tm.lin(ls, rs)})) == Nil{} : List<&2, N.Mono>},
  hz: Zs(~T, ~zero, ~add, ~mul, ~neg, env, rs))
  -> {N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, t) == N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, v) : T}:
  +ev = N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, v)
  +el = N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, Tm.lin(ls, rs))
  Equal.trans(T, N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, t), add(ev, el), ev,
    NP.NormS.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, env, t, N.TAdd{v, Tm.lin(ls, rs)}, ok),
    Equal.trans(T, add(ev, el), add(ev, zero), ev,
      Equal.cong(T, T, w => add(ev, w), el, zero, Lin.zero(~T, ~zero, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~dl, env, ls, rs, hz)),
      NP.Alg.zero_r(~T, ~zero, ~add, ~ac, ~z, ev)))
