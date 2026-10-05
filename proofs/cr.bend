# Correctly rounded kernels: a kernel run on big dyadics (src/big.bend)
# computes each output exactly, so rounding it once (Bd.f32) gives the
# correctly rounded value, Dy.f32 of the exact output. Here for any term
# over big-dyadic inputs (Ev.lk), and for a list of terms, a kernel's
# outputs (CR.fields); algebras/*/cr.bend states it kernel by kernel.

import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/round.bend as RD
import ../src/norm.bend as N
import ../src/big.bend as B
import ./int.bend as Z
import ./dyadic.bend as Y
import ./big.bend as BP
import ./norm.bend as NP

# a term on big dyadics with limb base 2h
def Bd.ev(+h: Nat, +env: List<&2, B.Bd>, t: N.Tm) -> B.Bd:
  match t:
    case N.TVar{i}:
      N.Env.at(~B.Bd, ~B.Bd.zero(), env, i)
    case N.TZero{}:
      B.Bd.zero()
    case N.TAdd{a, b}:
      B.Bd.add(h, Bd.ev(h, env, a), Bd.ev(h, env, b))
    case N.TMul{a, b}:
      B.Bd.mul(h, Bd.ev(h, env, a), Bd.ev(h, env, b))
    case N.TNeg{a}:
      B.Bd.neg(Bd.ev(h, env, a))

def Dy.ev(+env: List<&2, D.Dy>, t: N.Tm) -> D.Dy:
  N.Tm.eval(~D.Dy, ~D.Dy.zero(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg, env, t)

def Bd.neg.lk(+h: Nat, x: B.Bd) -> {B.Bd.val(h, B.Bd.neg(x)) == D.Dy.neg(B.Bd.val(h, x)) : D.Dy}:
  match x:
    case B.Bd{n, +m, +e}:
      match n:
        case False{}:
          Equal.sym(D.Dy, D.Dy.neg(D.Dy.of(e, I.IPos{B.Bn.val(h, m)})), D.Dy.of(e, I.Int.neg(I.IPos{B.Bn.val(h, m)})), Y.Of.neg(e, I.IPos{B.Bn.val(h, m)}))
        case True{}:
          Equal.trans(D.Dy, D.Dy.of(e, I.IPos{B.Bn.val(h, m)}), D.Dy.of(e, I.Int.neg(I.Int.neg(I.IPos{B.Bn.val(h, m)}))), D.Dy.neg(D.Dy.of(e, I.Int.neg(I.IPos{B.Bn.val(h, m)}))),
            Equal.cong(I.Int, D.Dy, z => D.Dy.of(e, z), I.IPos{B.Bn.val(h, m)}, I.Int.neg(I.Int.neg(I.IPos{B.Bn.val(h, m)})), Equal.sym(I.Int, I.Int.neg(I.Int.neg(I.IPos{B.Bn.val(h, m)})), I.IPos{B.Bn.val(h, m)}, Z.Int.neg_neg(I.IPos{B.Bn.val(h, m)}))),
            Equal.sym(D.Dy, D.Dy.neg(D.Dy.of(e, I.Int.neg(I.IPos{B.Bn.val(h, m)}))), D.Dy.of(e, I.Int.neg(I.Int.neg(I.IPos{B.Bn.val(h, m)}))), Y.Of.neg(e, I.Int.neg(I.IPos{B.Bn.val(h, m)}))))

def Bd.neg.ok(+h: Nat, x: B.Bd, +ox: {B.Bd.ok(h, x) == True{} : Bool}) -> {B.Bd.ok(h, B.Bd.neg(x)) == True{} : Bool}:
  match x:
    case B.Bd{n, m, e}:
      ox

# an input of a well-formed environment is well formed, and its value is
# the value environment's input
def At.ok(+h: Nat, +env: List<&2, B.Bd>, +i: Nat, +ok: {B.Bd.oks(h, env) == True{} : Bool}) -> {B.Bd.ok(h, N.Env.at(~B.Bd, ~B.Bd.zero(), env, i)) == True{} : Bool}:
  match env:
    case Nil{}:
      {==}
    case +x <> +r:
      match i:
        case 0n:
          NP.Bool.and_l(B.Bd.ok(h, x), B.Bd.oks(h, r), ok)
        case 1n+(+j):
          At.ok(h, r, j, NP.Bool.and_r(B.Bd.ok(h, x), B.Bd.oks(h, r), ok))

def At.val(+h: Nat, +env: List<&2, B.Bd>, +i: Nat) -> {B.Bd.val(h, N.Env.at(~B.Bd, ~B.Bd.zero(), env, i)) == N.Env.at(~D.Dy, ~D.Dy.zero(), B.Bd.vals(h, env), i) : D.Dy}:
  match env:
    case Nil{}:
      {==}
    case +x <> +r:
      match i:
        case 0n:
          {==}
        case 1n+(+j):
          At.val(h, r, j)

# a term evaluated on big dyadics is well formed
def Ev.ok(+h1: Nat, +env: List<&2, B.Bd>, +ok: {B.Bd.oks(1n+h1, env) == True{} : Bool}, t: N.Tm) -> {B.Bd.ok(1n+h1, Bd.ev(1n+h1, env, t)) == True{} : Bool}:
  match t:
    case N.TVar{+i}:
      At.ok(1n+h1, env, i, ok)
    case N.TZero{}:
      {==}
    case N.TAdd{+a, +b}:
      BP.Bd.add.ok(h1, Bd.ev(1n+h1, env, a), Bd.ev(1n+h1, env, b), Ev.ok(h1, env, ok, a), Ev.ok(h1, env, ok, b))
    case N.TMul{+a, +b}:
      BP.Bd.mul.ok(h1, Bd.ev(1n+h1, env, a), Bd.ev(1n+h1, env, b), Ev.ok(h1, env, ok, a), Ev.ok(h1, env, ok, b))
    case N.TNeg{+a}:
      Bd.neg.ok(1n+h1, Bd.ev(1n+h1, env, a), Ev.ok(h1, env, ok, a))

# and its value is the exact value
def Ev.lk(+h1: Nat, +env: List<&2, B.Bd>, +ok: {B.Bd.oks(1n+h1, env) == True{} : Bool}, t: N.Tm) -> {B.Bd.val(1n+h1, Bd.ev(1n+h1, env, t)) == Dy.ev(B.Bd.vals(1n+h1, env), t) : D.Dy}:
  match t:
    case N.TVar{+i}:
      At.val(1n+h1, env, i)
    case N.TZero{}:
      {==}
    case N.TAdd{+a, +b}:
      +x = Bd.ev(1n+h1, env, a)
      +y = Bd.ev(1n+h1, env, b)
      Equal.trans(D.Dy, B.Bd.val(1n+h1, B.Bd.add(1n+h1, x, y)), D.Dy.add(B.Bd.val(1n+h1, x), B.Bd.val(1n+h1, y)), D.Dy.add(Dy.ev(B.Bd.vals(1n+h1, env), a), Dy.ev(B.Bd.vals(1n+h1, env), b)),
        BP.Bd.add.lk(h1, x, y, Ev.ok(h1, env, ok, a), Ev.ok(h1, env, ok, b)),
        Y.Dy.cong2(B.Bd.val(1n+h1, x), Dy.ev(B.Bd.vals(1n+h1, env), a), B.Bd.val(1n+h1, y), Dy.ev(B.Bd.vals(1n+h1, env), b), Ev.lk(h1, env, ok, a), Ev.lk(h1, env, ok, b)))
    case N.TMul{+a, +b}:
      +x = Bd.ev(1n+h1, env, a)
      +y = Bd.ev(1n+h1, env, b)
      Equal.trans(D.Dy, B.Bd.val(1n+h1, B.Bd.mul(1n+h1, x, y)), D.Dy.mul(B.Bd.val(1n+h1, x), B.Bd.val(1n+h1, y)), D.Dy.mul(Dy.ev(B.Bd.vals(1n+h1, env), a), Dy.ev(B.Bd.vals(1n+h1, env), b)),
        BP.Bd.mul.lk(h1, x, y),
        Equal.trans(D.Dy, D.Dy.mul(B.Bd.val(1n+h1, x), B.Bd.val(1n+h1, y)), D.Dy.mul(Dy.ev(B.Bd.vals(1n+h1, env), a), B.Bd.val(1n+h1, y)), D.Dy.mul(Dy.ev(B.Bd.vals(1n+h1, env), a), Dy.ev(B.Bd.vals(1n+h1, env), b)),
          Equal.cong(D.Dy, D.Dy, z => D.Dy.mul(z, B.Bd.val(1n+h1, y)), B.Bd.val(1n+h1, x), Dy.ev(B.Bd.vals(1n+h1, env), a), Ev.lk(h1, env, ok, a)),
          Equal.cong(D.Dy, D.Dy, z => D.Dy.mul(Dy.ev(B.Bd.vals(1n+h1, env), a), z), B.Bd.val(1n+h1, y), Dy.ev(B.Bd.vals(1n+h1, env), b), Ev.lk(h1, env, ok, b))))
    case N.TNeg{+a}:
      +x = Bd.ev(1n+h1, env, a)
      Equal.trans(D.Dy, B.Bd.val(1n+h1, B.Bd.neg(x)), D.Dy.neg(B.Bd.val(1n+h1, x)), D.Dy.neg(Dy.ev(B.Bd.vals(1n+h1, env), a)),
        Bd.neg.lk(1n+h1, x), Equal.cong(D.Dy, D.Dy, z => D.Dy.neg(z), B.Bd.val(1n+h1, x), Dy.ev(B.Bd.vals(1n+h1, env), a), Ev.lk(h1, env, ok, a)))

def Bd.evs(+h: Nat, +env: List<&2, B.Bd>, ts: List<&2, N.Tm>) -> List<&2, B.Bd>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      B.Bd.f32(h, Bd.ev(h, env, t)) <> Bd.evs(h, env, r)

def Dy.evs(+env: List<&2, D.Dy>, ts: List<&2, N.Tm>) -> List<&2, D.Dy>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      RD.Dy.f32(Dy.ev(env, t)) <> Dy.evs(env, r)

# every output, run exactly and rounded once, is the correctly rounded
# exact output
def CR.fields(+h1: Nat, +env: List<&2, B.Bd>, +ok: {B.Bd.oks(1n+h1, env) == True{} : Bool}, ts: List<&2, N.Tm>)
  -> {B.Bd.vals(1n+h1, Bd.evs(1n+h1, env, ts)) == Dy.evs(B.Bd.vals(1n+h1, env), ts) : List<&2, D.Dy>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +r:
      +x = Bd.ev(1n+h1, env, t)
      Equal.trans(List<&2, D.Dy>, B.Bd.val(1n+h1, B.Bd.f32(1n+h1, x)) <> B.Bd.vals(1n+h1, Bd.evs(1n+h1, env, r)), RD.Dy.f32(Dy.ev(B.Bd.vals(1n+h1, env), t)) <> B.Bd.vals(1n+h1, Bd.evs(1n+h1, env, r)), Dy.evs(B.Bd.vals(1n+h1, env), t <> r),
        Equal.cong(D.Dy, List<&2, D.Dy>, z => z <> B.Bd.vals(1n+h1, Bd.evs(1n+h1, env, r)), B.Bd.val(1n+h1, B.Bd.f32(1n+h1, x)), RD.Dy.f32(Dy.ev(B.Bd.vals(1n+h1, env), t)),
          Equal.trans(D.Dy, B.Bd.val(1n+h1, B.Bd.f32(1n+h1, x)), RD.Dy.f32(B.Bd.val(1n+h1, x)), RD.Dy.f32(Dy.ev(B.Bd.vals(1n+h1, env), t)), BP.F32.lk(h1, x, Ev.ok(h1, env, ok, t)),
            Equal.cong(D.Dy, D.Dy, z => RD.Dy.f32(z), B.Bd.val(1n+h1, x), Dy.ev(B.Bd.vals(1n+h1, env), t), Ev.lk(h1, env, ok, t)))),
        Equal.cong(List<&2, D.Dy>, List<&2, D.Dy>, z => RD.Dy.f32(Dy.ev(B.Bd.vals(1n+h1, env), t)) <> z, B.Bd.vals(1n+h1, Bd.evs(1n+h1, env, r)), Dy.evs(B.Bd.vals(1n+h1, env), r), CR.fields(h1, env, ok, r)))
