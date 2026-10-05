# b-posit rounding (src/posit.bend) meets the rounding model
#   |fl(x) - x| <= 2^-p0 |x| + minpos   whenever |x| <= maxpos:
# in range it rounds to nearest at p0 + (rs - rl) >= p0 bits (Rne.rel and
# Ulp.mono); below minpos the error is minpos - |x|. So every error theorem
# (proofs/err.bend, Err.bound_u) holds for b-posit arithmetic with
# u = 2^-p0 and eta = minpos, as long as no result passes maxpos, where
# the format saturates, as IEEE overflows. And the run-time version on big
# dyadics computes the spec.

import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/round.bend as RD
import ../src/norm.bend as N
import ../src/fast.bend as F
import ../src/big.bend as B
import ../src/posit.bend as P
import ./nat.bend as NL
import ./int.bend as Z
import ./dyadic.bend as Y
import ./round.bend as R
import ./norm.bend as NP
import ./fast.bend as FL
import ./big.bend as BP

# Precision only helps
# --------------------

def Ulp.step(+k: Nat) -> {D.Dy.pos(D.Dy.add(D.Dy.ulp(k), D.Dy.neg(D.Dy.ulp(1n+k)))) == True{} : Bool}:
  +e1 = Equal.trans(D.Dy, D.Dy.of(k, I.IPos{1n}), D.Dy.of(Nat.add(k, 1n), D.Int.sh(1n, I.IPos{1n})), D.Dy.of(1n+k, I.IPos{2n}),
    Equal.sym(D.Dy, D.Dy.of(Nat.add(k, 1n), D.Int.sh(1n, I.IPos{1n})), D.Dy.of(k, I.IPos{1n}), Y.Of.shift(1n, k, I.IPos{1n})),
    Equal.cong(Nat, D.Dy, z => D.Dy.of(z, I.IPos{2n}), Nat.add(k, 1n), 1n+k, Equal.trans(Nat, Nat.add(k, 1n), 1n+Nat.add(k, 0n), 1n+k, NL.Nat.add_succ_r(k, 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(k, 0n), k, NL.Nat.add_zero_r(k)))))
  +e2 = Equal.trans(D.Dy, D.Dy.add(D.Dy.of(1n+k, I.IPos{2n}), D.Dy.neg(D.Dy.of(1n+k, I.IPos{1n}))), D.Dy.add(D.Dy.of(1n+k, I.IPos{2n}), D.Dy.of(1n+k, I.Int.neg(I.IPos{1n}))), D.Dy.of(1n+k, I.IPos{1n}),
    Equal.cong(D.Dy, D.Dy, z => D.Dy.add(D.Dy.of(1n+k, I.IPos{2n}), z), D.Dy.neg(D.Dy.of(1n+k, I.IPos{1n})), D.Dy.of(1n+k, I.Int.neg(I.IPos{1n})), Y.Of.neg(1n+k, I.IPos{1n})),
    Y.Add.of(1n+k, I.IPos{2n}, I.Int.neg(I.IPos{1n})))
  +e = Equal.trans(D.Dy, D.Dy.add(D.Dy.ulp(k), D.Dy.neg(D.Dy.ulp(1n+k))), D.Dy.add(D.Dy.of(1n+k, I.IPos{2n}), D.Dy.neg(D.Dy.of(1n+k, I.IPos{1n}))), D.Dy.of(1n+k, I.IPos{1n}),
    Equal.cong(D.Dy, D.Dy, z => D.Dy.add(z, D.Dy.neg(D.Dy.of(1n+k, I.IPos{1n}))), D.Dy.ulp(k), D.Dy.of(1n+k, I.IPos{2n}), e1), e2)
  Equal.trans(Bool, D.Dy.pos(D.Dy.add(D.Dy.ulp(k), D.Dy.neg(D.Dy.ulp(1n+k)))), D.Dy.pos(D.Dy.of(1n+k, I.IPos{1n})), True{},
    Equal.cong(D.Dy, Bool, z => D.Dy.pos(z), D.Dy.add(D.Dy.ulp(k), D.Dy.neg(D.Dy.ulp(1n+k))), D.Dy.of(1n+k, I.IPos{1n}), e), Y.Pos.of(1n+k, I.IPos{1n}))

# a - c >= 0 from a - b >= 0 and b - c >= 0
def Dy.le_trans(+a: D.Dy, +b: D.Dy, +c: D.Dy, hab: {D.Dy.pos(D.Dy.add(a, D.Dy.neg(b))) == True{} : Bool}, hbc: {D.Dy.pos(D.Dy.add(b, D.Dy.neg(c))) == True{} : Bool})
  -> {D.Dy.pos(D.Dy.add(a, D.Dy.neg(c))) == True{} : Bool}:
  R.Dy.pr(D.Dy.add(a, D.Dy.neg(c)), D.Dy.add(D.Dy.add(a, D.Dy.neg(b)), D.Dy.add(b, D.Dy.neg(c))),
    NP.Norm.eq(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg,
      ~Y.Dy.r.add_assoc, ~Y.Dy.r.add_comm, ~Y.Dy.r.zero_l, ~Y.Dy.r.add_inv, ~Y.Dy.r.mul_assoc, ~Y.Dy.r.mul_comm, ~Y.Dy.r.unit_r, ~Y.Dy.r.dist_l, ~Y.Dy.r.neg_add, ~Y.Dy.r.neg_mul_l, ~Y.Dy.r.neg_neg,
      [a, b, c], R.Ad(R.V(0n), R.Ng(R.V(2n))), R.Ad(R.Ad(R.V(0n), R.Ng(R.V(1n))), R.Ad(R.V(1n), R.Ng(R.V(2n)))), {==}),
    Y.Dy.pos_add(D.Dy.add(a, D.Dy.neg(b)), D.Dy.add(b, D.Dy.neg(c)))(hab)(hbc))

# 2^-a >= 2^-(a + w)
def Ulp.mono(+a: Nat, +w: Nat) -> {D.Dy.pos(D.Dy.add(D.Dy.ulp(a), D.Dy.neg(D.Dy.ulp(Nat.add(a, w))))) == True{} : Bool}:
  match w:
    case 0n:
      +e = Equal.trans(D.Dy, D.Dy.add(D.Dy.ulp(a), D.Dy.neg(D.Dy.ulp(Nat.add(a, 0n)))), D.Dy.add(D.Dy.ulp(a), D.Dy.neg(D.Dy.ulp(a))), D.Dy.zero(),
        Equal.cong(Nat, D.Dy, z => D.Dy.add(D.Dy.ulp(a), D.Dy.neg(D.Dy.ulp(z))), Nat.add(a, 0n), a, NL.Nat.add_zero_r(a)), Y.Dy.add_inv(D.Dy.ulp(a)))
      Equal.cong(D.Dy, Bool, z => D.Dy.pos(z), D.Dy.add(D.Dy.ulp(a), D.Dy.neg(D.Dy.ulp(Nat.add(a, 0n)))), D.Dy.zero(), e)
    case 1n+(+v):
      +k = Nat.add(a, v)
      Equal.trans(Bool, D.Dy.pos(D.Dy.add(D.Dy.ulp(a), D.Dy.neg(D.Dy.ulp(Nat.add(a, 1n+v))))), D.Dy.pos(D.Dy.add(D.Dy.ulp(a), D.Dy.neg(D.Dy.ulp(1n+k)))), True{},
        Equal.cong(Nat, Bool, z => D.Dy.pos(D.Dy.add(D.Dy.ulp(a), D.Dy.neg(D.Dy.ulp(z)))), Nat.add(a, 1n+v), 1n+k, NL.Nat.add_succ_r(a, v)),
        Dy.le_trans(D.Dy.ulp(a), D.Dy.ulp(k), D.Dy.ulp(1n+k), Ulp.mono(a, v), Ulp.step(k)))

# Below minpos
# ------------

def Sh.signed(+k: Nat, +n: I.Int, +m: Nat) -> {D.Int.sh(k, RD.Int.signed(n, m)) == RD.Int.signed(n, Nat.mul(m, RD.Nat.pow2(k))) : I.Int}:
  match n:
    case I.IPos{a}:
      R.Sh.ipos(k, m)
    case I.INeg{a}:
      Equal.trans(I.Int, D.Int.sh(k, I.Int.neg(I.IPos{m})), I.Int.neg(D.Int.sh(k, I.IPos{m})), I.Int.neg(I.IPos{Nat.mul(m, RD.Nat.pow2(k))}), Y.Int.sh_neg(k, I.IPos{m}),
        Equal.cong(I.Int, I.Int, z => I.Int.neg(z), D.Int.sh(k, I.IPos{m}), I.IPos{Nat.mul(m, RD.Nat.pow2(k))}, R.Sh.ipos(k, m)))

def Sgn.self(+n: I.Int) -> {RD.Int.signed(n, RD.Int.mag(n)) == n : I.Int}:
  match n:
    case I.IPos{a}:
      {==}
    case I.INeg{a}:
      {==}

def Sdiff2(+n: I.Int, +b: Nat, +w: Nat) -> {I.Int.add(RD.Int.signed(n, Nat.add(b, w)), I.Int.neg(RD.Int.signed(n, b))) == RD.Int.signed(n, w) : I.Int}:
  match n:
    case I.IPos{a}:
      +env : List<&2, I.Int> = [I.IPos{b}, I.IPos{w}]
      BP.IntN(env, R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(0n))), R.V(1n), [], [], {==}, Unit{})
    case I.INeg{a}:
      +env : List<&2, I.Int> = [I.IPos{b}, I.IPos{w}]
      BP.IntN(env, R.Ad(R.Ng(R.Ad(R.V(0n), R.V(1n))), R.Ng(R.Ng(R.V(0n)))), R.Ng(R.V(1n)), [], [], {==}, Unit{})

# x below minpos rounds to minpos (with x's sign), within minpos
def Tiny.err(+p0: Nat, +bias: Nat, +x: D.Dy, +ht: {P.Pz.tiny(p0, bias, x) == True{} : Bool})
  -> {D.Dy.pos(D.Dy.add(D.Dy.of(P.Pz.mine(p0, bias), I.IPos{P.Pz.minm(p0)}), D.Dy.neg(D.Dy.abs(D.Dy.add(D.Dy.of(P.Pz.mine(p0, bias), RD.Int.signed(D.Dy.num(x), P.Pz.minm(p0))), D.Dy.neg(x)))))) == True{} : Bool}:
  +n = D.Dy.num(x)
  +d = D.Dy.den(x)
  +m = RD.Int.mag(n)
  +c = P.Pz.mine(p0, bias)
  +mm = P.Pz.minm(p0)
  +dd = Nat.add(d, c)
  +a = Nat.mul(mm, RD.Nat.pow2(d))
  +bv = Nat.mul(m, RD.Nat.pow2(c))
  +w : Nat = 1n+RD.Nat.monus(a, 1n+bv)
  +ha = Equal.trans(Nat, a, 1n+Nat.add(bv, RD.Nat.monus(a, 1n+bv)), Nat.add(bv, w), BP.Lt.wit(bv, a)(ht), Equal.sym(Nat, Nat.add(bv, w), 1n+Nat.add(bv, RD.Nat.monus(a, 1n+bv)), NL.Nat.add_succ_r(bv, RD.Nat.monus(a, 1n+bv))))
  +ecd = NL.Nat.add_comm(c, d)
  # x and the result over 2^(d + c)
  +ex = Equal.trans(D.Dy, x, D.Dy.of(dd, D.Int.sh(c, n)), D.Dy.of(dd, RD.Int.signed(n, bv)),
    Equal.trans(D.Dy, x, D.Dy.of(d, n), D.Dy.of(dd, D.Int.sh(c, n)), Equal.sym(D.Dy, D.Dy.of(d, n), x, Y.Of.self(x)), Equal.sym(D.Dy, D.Dy.of(dd, D.Int.sh(c, n)), D.Dy.of(d, n), Y.Of.shift(c, d, n))),
    Equal.cong(I.Int, D.Dy, z => D.Dy.of(dd, z), D.Int.sh(c, n), RD.Int.signed(n, bv),
      Equal.trans(I.Int, D.Int.sh(c, n), D.Int.sh(c, RD.Int.signed(n, m)), RD.Int.signed(n, bv), Equal.cong(I.Int, I.Int, z => D.Int.sh(c, z), n, RD.Int.signed(n, m), Equal.sym(I.Int, RD.Int.signed(n, m), n, Sgn.self(n))), Sh.signed(c, n, m))))
  +ey = Equal.trans(D.Dy, D.Dy.of(c, RD.Int.signed(n, mm)), D.Dy.of(Nat.add(c, d), D.Int.sh(d, RD.Int.signed(n, mm))), D.Dy.of(dd, RD.Int.signed(n, a)),
    Equal.sym(D.Dy, D.Dy.of(Nat.add(c, d), D.Int.sh(d, RD.Int.signed(n, mm))), D.Dy.of(c, RD.Int.signed(n, mm)), Y.Of.shift(d, c, RD.Int.signed(n, mm))),
    Y.Of.cong(Nat.add(c, d), dd, D.Int.sh(d, RD.Int.signed(n, mm)), RD.Int.signed(n, a), ecd, Sh.signed(d, n, mm)))
  +em = Equal.trans(D.Dy, D.Dy.of(c, I.IPos{mm}), D.Dy.of(Nat.add(c, d), D.Int.sh(d, I.IPos{mm})), D.Dy.of(dd, I.IPos{a}),
    Equal.sym(D.Dy, D.Dy.of(Nat.add(c, d), D.Int.sh(d, I.IPos{mm})), D.Dy.of(c, I.IPos{mm}), Y.Of.shift(d, c, I.IPos{mm})),
    Y.Of.cong(Nat.add(c, d), dd, D.Int.sh(d, I.IPos{mm}), I.IPos{a}, NL.Nat.add_comm(c, d), R.Sh.ipos(d, mm)))
  # the difference is W / 2^(d + c), with a = bv + W
  +ediff = Equal.trans(D.Dy, D.Dy.add(D.Dy.of(c, RD.Int.signed(n, mm)), D.Dy.neg(x)), D.Dy.add(D.Dy.of(dd, RD.Int.signed(n, a)), D.Dy.neg(D.Dy.of(dd, RD.Int.signed(n, bv)))), D.Dy.of(dd, RD.Int.signed(n, w)),
    Y.Dy.cong2(D.Dy.of(c, RD.Int.signed(n, mm)), D.Dy.of(dd, RD.Int.signed(n, a)), D.Dy.neg(x), D.Dy.neg(D.Dy.of(dd, RD.Int.signed(n, bv))), ey, Equal.cong(D.Dy, D.Dy, z => D.Dy.neg(z), x, D.Dy.of(dd, RD.Int.signed(n, bv)), ex)),
    Equal.trans(D.Dy, D.Dy.add(D.Dy.of(dd, RD.Int.signed(n, a)), D.Dy.neg(D.Dy.of(dd, RD.Int.signed(n, bv)))), D.Dy.of(dd, I.Int.add(RD.Int.signed(n, a), I.Int.neg(RD.Int.signed(n, bv)))), D.Dy.of(dd, RD.Int.signed(n, w)),
      Equal.trans(D.Dy, D.Dy.add(D.Dy.of(dd, RD.Int.signed(n, a)), D.Dy.neg(D.Dy.of(dd, RD.Int.signed(n, bv)))), D.Dy.add(D.Dy.of(dd, RD.Int.signed(n, a)), D.Dy.of(dd, I.Int.neg(RD.Int.signed(n, bv)))), D.Dy.of(dd, I.Int.add(RD.Int.signed(n, a), I.Int.neg(RD.Int.signed(n, bv)))),
        Equal.cong(D.Dy, D.Dy, z => D.Dy.add(D.Dy.of(dd, RD.Int.signed(n, a)), z), D.Dy.neg(D.Dy.of(dd, RD.Int.signed(n, bv))), D.Dy.of(dd, I.Int.neg(RD.Int.signed(n, bv))), Y.Of.neg(dd, RD.Int.signed(n, bv))),
        Y.Add.of(dd, RD.Int.signed(n, a), I.Int.neg(RD.Int.signed(n, bv)))),
      Equal.cong(I.Int, D.Dy, z => D.Dy.of(dd, z), I.Int.add(RD.Int.signed(n, a), I.Int.neg(RD.Int.signed(n, bv))), RD.Int.signed(n, w),
        Equal.trans(I.Int, I.Int.add(RD.Int.signed(n, a), I.Int.neg(RD.Int.signed(n, bv))), I.Int.add(RD.Int.signed(n, Nat.add(bv, w)), I.Int.neg(RD.Int.signed(n, bv))), RD.Int.signed(n, w),
          Equal.cong(Nat, I.Int, z => I.Int.add(RD.Int.signed(n, z), I.Int.neg(RD.Int.signed(n, bv))), a, Nat.add(bv, w), ha),
          Sdiff2(n, bv, w)))))
  +eabs = Equal.trans(D.Dy, D.Dy.abs(D.Dy.add(D.Dy.of(c, RD.Int.signed(n, mm)), D.Dy.neg(x))), D.Dy.abs(D.Dy.of(dd, RD.Int.signed(n, w))), D.Dy.of(dd, I.IPos{w}),
    Equal.cong(D.Dy, D.Dy, z => D.Dy.abs(z), D.Dy.add(D.Dy.of(c, RD.Int.signed(n, mm)), D.Dy.neg(x)), D.Dy.of(dd, RD.Int.signed(n, w)), ediff),
    Equal.trans(D.Dy, D.Dy.abs(D.Dy.of(dd, RD.Int.signed(n, w))), D.Dy.of(dd, I.Int.abs(RD.Int.signed(n, w))), D.Dy.of(dd, I.IPos{w}), Y.Abs.of(dd, RD.Int.signed(n, w)),
      Y.Of.cong(dd, dd, I.Int.abs(RD.Int.signed(n, w)), I.IPos{w}, {==}, R.Sg.abs(n, w))))
  # minpos - error = bv / 2^(d + c) >= 0
  +eres = Equal.trans(D.Dy, D.Dy.add(D.Dy.of(c, I.IPos{mm}), D.Dy.neg(D.Dy.abs(D.Dy.add(D.Dy.of(c, RD.Int.signed(n, mm)), D.Dy.neg(x))))), D.Dy.add(D.Dy.of(dd, I.IPos{a}), D.Dy.neg(D.Dy.of(dd, I.IPos{w}))), D.Dy.of(dd, I.IPos{bv}),
    Y.Dy.cong2(D.Dy.of(c, I.IPos{mm}), D.Dy.of(dd, I.IPos{a}), D.Dy.neg(D.Dy.abs(D.Dy.add(D.Dy.of(c, RD.Int.signed(n, mm)), D.Dy.neg(x)))), D.Dy.neg(D.Dy.of(dd, I.IPos{w})), em,
      Equal.cong(D.Dy, D.Dy, z => D.Dy.neg(z), D.Dy.abs(D.Dy.add(D.Dy.of(c, RD.Int.signed(n, mm)), D.Dy.neg(x))), D.Dy.of(dd, I.IPos{w}), eabs)),
    Equal.trans(D.Dy, D.Dy.add(D.Dy.of(dd, I.IPos{a}), D.Dy.neg(D.Dy.of(dd, I.IPos{w}))), D.Dy.of(dd, I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{w}))), D.Dy.of(dd, I.IPos{bv}),
      Equal.trans(D.Dy, D.Dy.add(D.Dy.of(dd, I.IPos{a}), D.Dy.neg(D.Dy.of(dd, I.IPos{w}))), D.Dy.add(D.Dy.of(dd, I.IPos{a}), D.Dy.of(dd, I.Int.neg(I.IPos{w}))), D.Dy.of(dd, I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{w}))),
        Equal.cong(D.Dy, D.Dy, z => D.Dy.add(D.Dy.of(dd, I.IPos{a}), z), D.Dy.neg(D.Dy.of(dd, I.IPos{w})), D.Dy.of(dd, I.Int.neg(I.IPos{w})), Y.Of.neg(dd, I.IPos{w})),
        Y.Add.of(dd, I.IPos{a}, I.Int.neg(I.IPos{w}))),
      Equal.cong(I.Int, D.Dy, z => D.Dy.of(dd, z), I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{w})), I.IPos{bv},
        Equal.trans(I.Int, I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{w})), I.Int.add(I.IPos{Nat.add(bv, w)}, I.Int.neg(I.IPos{w})), I.IPos{bv},
          Equal.cong(Nat, I.Int, z => I.Int.add(I.IPos{z}, I.Int.neg(I.IPos{w})), a, Nat.add(bv, w), ha), BP.Ipm2(bv, w)))))
  Equal.trans(Bool, D.Dy.pos(D.Dy.add(D.Dy.of(c, I.IPos{mm}), D.Dy.neg(D.Dy.abs(D.Dy.add(D.Dy.of(c, RD.Int.signed(n, mm)), D.Dy.neg(x)))))), D.Dy.pos(D.Dy.of(dd, I.IPos{bv})), True{},
    Equal.cong(D.Dy, Bool, z => D.Dy.pos(z), D.Dy.add(D.Dy.of(c, I.IPos{mm}), D.Dy.neg(D.Dy.abs(D.Dy.add(D.Dy.of(c, RD.Int.signed(n, mm)), D.Dy.neg(x))))), D.Dy.of(dd, I.IPos{bv}), eres),
    Y.Pos.of(dd, I.IPos{bv}))

# The model
# ---------

def Mdl.mp(+p0: Nat, +bias: Nat) -> D.Dy:
  D.Dy.of(P.Pz.mine(p0, bias), I.IPos{P.Pz.minm(p0)})

def Mdl.go(+p01: Nat, +g: Nat, +rs: Nat, +x: D.Dy, z: Bool, t: Bool, o: Bool,
  +et: {P.Pz.tiny(1n+p01, P.Pz.bias(g, rs), x) == t : Bool}, +eo: {P.Pz.over(1n+p01, P.Pz.bias(g, rs), x) == o : Bool}, +ho: {P.Pz.over(1n+p01, P.Pz.bias(g, rs), x) == False{} : Bool})
  -> {D.Dy.pos(D.Dy.add(D.Dy.add(D.Dy.mul(D.Dy.ulp(1n+p01), D.Dy.abs(x)), Mdl.mp(1n+p01, P.Pz.bias(g, rs))), D.Dy.neg(D.Dy.abs(D.Dy.add(P.Pz.fl.go(1n+p01, g, rs, z, t, o, x), D.Dy.neg(x)))))) == True{} : Bool}:
  match z:
    case True{}:
      +a = D.Dy.mul(D.Dy.ulp(1n+p01), D.Dy.abs(x))
      +mp = Mdl.mp(1n+p01, P.Pz.bias(g, rs))
      +ee = D.Dy.abs(D.Dy.add(x, D.Dy.neg(x)))
      +e0 = Equal.cong(D.Dy, D.Dy, w => D.Dy.abs(w), D.Dy.add(x, D.Dy.neg(x)), D.Dy.zero(), Y.Dy.add_inv(x))
      R.Dy.pr(D.Dy.add(D.Dy.add(a, mp), D.Dy.neg(ee)), D.Dy.add(D.Dy.add(a, mp), D.Dy.neg(D.Dy.zero())),
        Equal.cong(D.Dy, D.Dy, w => D.Dy.add(D.Dy.add(a, mp), D.Dy.neg(w)), ee, D.Dy.zero(), e0),
        R.Dy.pr(D.Dy.add(D.Dy.add(a, mp), D.Dy.neg(D.Dy.zero())), D.Dy.add(a, mp),
          NP.Norm.eq(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg,
            ~Y.Dy.r.add_assoc, ~Y.Dy.r.add_comm, ~Y.Dy.r.zero_l, ~Y.Dy.r.add_inv, ~Y.Dy.r.mul_assoc, ~Y.Dy.r.mul_comm, ~Y.Dy.r.unit_r, ~Y.Dy.r.dist_l, ~Y.Dy.r.neg_add, ~Y.Dy.r.neg_mul_l, ~Y.Dy.r.neg_neg,
            [a, mp], R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(N.TZero{})), R.Ad(R.V(0n), R.V(1n)), {==}),
          Y.Dy.pos_add(a, mp)(Y.Dy.pos_mul(D.Dy.ulp(1n+p01), D.Dy.abs(x))(R.Round.eps_pos(1n+p01))(Y.Dy.pos_abs(x)))(Y.Pos.of(P.Pz.mine(1n+p01, P.Pz.bias(g, rs)), I.IPos{P.Pz.minm(1n+p01)}))))
    case False{}:
      match t:
        case True{}:
          +bias = P.Pz.bias(g, rs)
          +a = D.Dy.mul(D.Dy.ulp(1n+p01), D.Dy.abs(x))
          +mp = Mdl.mp(1n+p01, bias)
          +ee = D.Dy.abs(D.Dy.add(D.Dy.of(P.Pz.mine(1n+p01, bias), RD.Int.signed(D.Dy.num(x), P.Pz.minm(1n+p01))), D.Dy.neg(x)))
          R.Dy.pr(D.Dy.add(D.Dy.add(a, mp), D.Dy.neg(ee)), D.Dy.add(D.Dy.add(mp, D.Dy.neg(ee)), a),
            NP.Norm.eq(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg,
              ~Y.Dy.r.add_assoc, ~Y.Dy.r.add_comm, ~Y.Dy.r.zero_l, ~Y.Dy.r.add_inv, ~Y.Dy.r.mul_assoc, ~Y.Dy.r.mul_comm, ~Y.Dy.r.unit_r, ~Y.Dy.r.dist_l, ~Y.Dy.r.neg_add, ~Y.Dy.r.neg_mul_l, ~Y.Dy.r.neg_neg,
              [a, mp, ee], R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(2n))), R.Ad(R.Ad(R.V(1n), R.Ng(R.V(2n))), R.V(0n)), {==}),
            Y.Dy.pos_add(D.Dy.add(mp, D.Dy.neg(ee)), a)(Tiny.err(1n+p01, bias, x, et))(Y.Dy.pos_mul(D.Dy.ulp(1n+p01), D.Dy.abs(x))(R.Round.eps_pos(1n+p01))(Y.Dy.pos_abs(x))))
        case False{}:
          match o:
            case True{}:
              Empty.absurd({D.Dy.pos(D.Dy.add(D.Dy.add(D.Dy.mul(D.Dy.ulp(1n+p01), D.Dy.abs(x)), Mdl.mp(1n+p01, P.Pz.bias(g, rs))), D.Dy.neg(D.Dy.abs(D.Dy.add(P.Pz.fl.go(1n+p01, g, rs, False{}, False{}, True{}, x), D.Dy.neg(x)))))) == True{} : Bool},
                Z.Bool.ft(Equal.trans(Bool, False{}, P.Pz.over(1n+p01, P.Pz.bias(g, rs), x), True{}, Equal.sym(Bool, P.Pz.over(1n+p01, P.Pz.bias(g, rs), x), False{}, ho), eo)))
            case False{}:
              +bias = P.Pz.bias(g, rs)
              +wv = RD.Nat.monus(rs, P.Pz.rl(rs, P.Pz.find(g, bias, Nat.double(rs), 0n, x)))
              +pp = Nat.add(p01, wv)
              +u0 = D.Dy.ulp(1n+p01)
              +up = D.Dy.ulp(1n+pp)
              +xa = D.Dy.abs(x)
              +mp = Mdl.mp(1n+p01, bias)
              +ee = D.Dy.abs(D.Dy.add(RD.Dy.rne(1n+pp, x), D.Dy.neg(x)))
              R.Dy.pr(D.Dy.add(D.Dy.add(D.Dy.mul(u0, xa), mp), D.Dy.neg(ee)), D.Dy.add(D.Dy.add(D.Dy.add(D.Dy.mul(up, xa), D.Dy.neg(ee)), D.Dy.mul(D.Dy.add(u0, D.Dy.neg(up)), xa)), mp),
                NP.Norm.eq(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg,
                  ~Y.Dy.r.add_assoc, ~Y.Dy.r.add_comm, ~Y.Dy.r.zero_l, ~Y.Dy.r.add_inv, ~Y.Dy.r.mul_assoc, ~Y.Dy.r.mul_comm, ~Y.Dy.r.unit_r, ~Y.Dy.r.dist_l, ~Y.Dy.r.neg_add, ~Y.Dy.r.neg_mul_l, ~Y.Dy.r.neg_neg,
                  [u0, up, xa, mp, ee], R.Ad(R.Ad(R.Ml(R.V(0n), R.V(2n)), R.V(3n)), R.Ng(R.V(4n))),
                  R.Ad(R.Ad(R.Ad(R.Ml(R.V(1n), R.V(2n)), R.Ng(R.V(4n))), R.Ml(R.Ad(R.V(0n), R.Ng(R.V(1n))), R.V(2n))), R.V(3n)), {==}),
                Y.Dy.pos_add(D.Dy.add(D.Dy.add(D.Dy.mul(up, xa), D.Dy.neg(ee)), D.Dy.mul(D.Dy.add(u0, D.Dy.neg(up)), xa)), mp)(Y.Dy.pos_add(D.Dy.add(D.Dy.mul(up, xa), D.Dy.neg(ee)), D.Dy.mul(D.Dy.add(u0, D.Dy.neg(up)), xa))(R.Rne.rel(pp, x))(Y.Dy.pos_mul(D.Dy.add(u0, D.Dy.neg(up)), xa)(Ulp.mono(1n+p01, wv))(Y.Dy.pos_abs(x))))(Y.Pos.of(P.Pz.mine(1n+p01, bias), I.IPos{P.Pz.minm(1n+p01)})))

# b-posit rounding meets the model with u = 2^-p0 and eta = minpos, for
# every x up to maxpos
def Pz.model(+p01: Nat, +g: Nat, +rs: Nat, +x: D.Dy, +ho: {P.Pz.over(1n+p01, P.Pz.bias(g, rs), x) == False{} : Bool})
  -> {D.Dy.pos(D.Dy.add(D.Dy.add(D.Dy.mul(D.Dy.ulp(1n+p01), D.Dy.abs(x)), Mdl.mp(1n+p01, P.Pz.bias(g, rs))), D.Dy.neg(D.Dy.abs(D.Dy.add(P.Pz.fl(1n+p01, g, rs, x), D.Dy.neg(x)))))) == True{} : Bool}:
  +bias = P.Pz.bias(g, rs)
  Mdl.go(p01, g, rs, x, P.Pz.zero(x), P.Pz.tiny(1n+p01, bias, x), P.Pz.over(1n+p01, bias, x), {==}, {==}, ho)

# The run-time version computes the spec
# --------------------------------------

# on a normal form Bd{n, m, e} with value X: den X = e, num X = sg(n, V)
def Xv(+h: Nat, +n: Bool, +m: B.Bn, +e: Nat) -> D.Dy:
  D.Dy.of(e, B.Bd.sg(n, B.Bn.val(h, m)))

def Lk.mag(+h: Nat, +n: Bool, +m: B.Bn, +e: Nat, +en: {D.Dy.num(Xv(h, n, m, e)) == B.Bd.sg(n, B.Bn.val(h, m)) : I.Int})
  -> {RD.Int.mag(D.Dy.num(Xv(h, n, m, e))) == B.Bn.val(h, m) : Nat}:
  Equal.trans(Nat, RD.Int.mag(D.Dy.num(Xv(h, n, m, e))), RD.Int.mag(B.Bd.sg(n, B.Bn.val(h, m))), B.Bn.val(h, m),
    Equal.cong(I.Int, Nat, z => RD.Int.mag(z), D.Dy.num(Xv(h, n, m, e)), B.Bd.sg(n, B.Bn.val(h, m)), en), BP.Sg.mag(n, B.Bn.val(h, m)))

def Lk.zero(+h1: Nat, +n: Bool, +m: B.Bn, +e: Nat, +en: {D.Dy.num(Xv(1n+h1, n, m, e)) == B.Bd.sg(n, B.Bn.val(1n+h1, m)) : I.Int}, +om: {B.Bn.ok(1n+h1, m) == True{} : Bool})
  -> {P.Pz.bzero(B.Bd{n, m, e}) == P.Pz.zero(Xv(1n+h1, n, m, e)) : Bool}:
  +h : Nat = 1n+h1
  +v = B.Bn.val(h, m)
  Equal.cong(Bool, Bool, z => Bool.not(z), B.Bn.lt(B.BNil{}, m), RD.Nat.lt(0n, RD.Int.mag(D.Dy.num(Xv(h, n, m, e)))),
    Equal.trans(Bool, B.Bn.lt(B.BNil{}, m), RD.Nat.lt(0n, v), RD.Nat.lt(0n, RD.Int.mag(D.Dy.num(Xv(h, n, m, e)))), BP.Cmp.lt(h, B.BNil{}, m, {==}, om),
      Equal.cong(Nat, Bool, z => RD.Nat.lt(0n, z), v, RD.Int.mag(D.Dy.num(Xv(h, n, m, e))), Equal.sym(Nat, RD.Int.mag(D.Dy.num(Xv(h, n, m, e))), v, Lk.mag(h, n, m, e, en)))))

def Vminm(+h1: Nat, +p0: Nat) -> {B.Bn.val(1n+h1, P.Pz.bminm(1n+h1, p0)) == P.Pz.minm(p0) : Nat}:
  +h : Nat = 1n+h1
  +pw = B.Bn.pow2(h, F.Nat.monusf(p0, 1n))
  Equal.trans(Nat, B.Bn.val(h, B.Bn.addc(h, pw, B.BNil{}, True{})), 1n+Nat.add(B.Bn.val(h, pw), 0n), P.Pz.minm(p0), BP.Add.val(h, pw, B.BNil{}, True{}),
    Equal.cong(Nat, Nat, z => 1n+z, Nat.add(B.Bn.val(h, pw), 0n), RD.Nat.pow2(RD.Nat.monus(p0, 1n)),
      Equal.trans(Nat, Nat.add(B.Bn.val(h, pw), 0n), B.Bn.val(h, pw), RD.Nat.pow2(RD.Nat.monus(p0, 1n)), NL.Nat.add_zero_r(B.Bn.val(h, pw)),
        BP.Vpw(h1, F.Nat.monusf(p0, 1n), RD.Nat.monus(p0, 1n), Equal.sym(Nat, RD.Nat.monus(p0, 1n), F.Nat.monusf(p0, 1n), FL.L.monus(p0, 1n))))))

def Ominm(+h1: Nat, +p0: Nat) -> {B.Bn.ok(1n+h1, P.Pz.bminm(1n+h1, p0)) == True{} : Bool}:
  BP.Add.ok(h1, B.Bn.pow2(1n+h1, F.Nat.monusf(p0, 1n)), B.BNil{}, True{}, BP.Pow2.ok(h1, F.Nat.monusf(p0, 1n)), {==})

# 2^p0 - 1 as limbs
def Vsub(+h1: Nat, +p0: Nat) -> {B.Bn.val(1n+h1, B.Bn.sub(1n+h1, B.Bn.pow2(1n+h1, p0), B.BCons{1n, B.BNil{}})) == RD.Nat.monus(RD.Nat.pow2(p0), 1n) : Nat}:
  +h : Nat = 1n+h1
  +pw = B.Bn.pow2(h, p0)
  +vs = B.Bn.val(h, B.Bn.sub(h, pw, B.BCons{1n, B.BNil{}}))
  +w = RD.Nat.monus(RD.Nat.pow2(p0), 1n)
  +hp = Equal.trans(Nat, B.Bn.val(h, pw), RD.Nat.pow2(p0), 1n+w, BP.Pow2.val(h1, p0), BP.Lt.wit(0n, RD.Nat.pow2(p0))(BP.Pow2.pos(p0)))
  +hyp = Equal.trans(Bool, RD.Nat.lt(B.Bn.val(h, pw), 1n), RD.Nat.lt(1n+w, 1n), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, 1n), B.Bn.val(h, pw), 1n+w, hp), BP.Lt.z(w))
  +hs = BP.Sub.val(h, pw, B.BCons{1n, B.BNil{}}, False{}, BP.Pow2.ok(h1, p0), {==}, hyp)
  # vs + 1 = 2^p0
  +e1 = Equal.trans(Nat, Nat.add(1n, vs), Nat.add(vs, 1n), RD.Nat.pow2(p0), NL.Nat.add_comm(1n, vs), Equal.trans(Nat, Nat.add(vs, 1n), B.Bn.val(h, pw), RD.Nat.pow2(p0), hs, BP.Pow2.val(h1, p0)))
  Equal.sym(Nat, RD.Nat.monus(RD.Nat.pow2(p0), 1n), vs,
    Equal.trans(Nat, RD.Nat.monus(RD.Nat.pow2(p0), 1n), RD.Nat.monus(Nat.add(1n, vs), 1n), vs,
      Equal.cong(Nat, Nat, z => RD.Nat.monus(z, 1n), RD.Nat.pow2(p0), Nat.add(1n, vs), Equal.sym(Nat, Nat.add(1n, vs), RD.Nat.pow2(p0), e1)),
      R.Nat.monus_add(1n, vs)))

def Osub(+h1: Nat, +p0: Nat) -> {B.Bn.ok(1n+h1, B.Bn.sub(1n+h1, B.Bn.pow2(1n+h1, p0), B.BCons{1n, B.BNil{}})) == True{} : Bool}:
  BP.Sub.ok(1n+h1, B.Bn.pow2(1n+h1, p0), B.BCons{1n, B.BNil{}}, False{}, BP.Pow2.ok(h1, p0), {==})

def Vmaxm(+h1: Nat, +p0: Nat, +bias: Nat, +e: Nat) -> {B.Bn.val(1n+h1, P.Pz.bmaxm(1n+h1, p0, bias, e)) == P.Pz.maxm(p0, bias, e) : Nat}:
  +h : Nat = 1n+h1
  +sb = B.Bn.sub(h, B.Bn.pow2(h, p0), B.BCons{1n, B.BNil{}})
  +kf = Nat.add(F.Nat.monusf(bias, p0), e)
  +k = Nat.add(RD.Nat.monus(bias, p0), e)
  Equal.trans(Nat, B.Bn.val(h, B.Bn.shl(h, kf, sb)), Nat.mul(B.Bn.val(h, sb), RD.Nat.pow2(kf)), P.Pz.maxm(p0, bias, e), BP.Shl.val(h1, kf, sb),
    Equal.trans(Nat, Nat.mul(B.Bn.val(h, sb), RD.Nat.pow2(kf)), Nat.mul(RD.Nat.monus(RD.Nat.pow2(p0), 1n), RD.Nat.pow2(kf)), P.Pz.maxm(p0, bias, e),
      Equal.cong(Nat, Nat, z => Nat.mul(z, RD.Nat.pow2(kf)), B.Bn.val(h, sb), RD.Nat.monus(RD.Nat.pow2(p0), 1n), Vsub(h1, p0)),
      Equal.cong(Nat, Nat, z => Nat.mul(RD.Nat.monus(RD.Nat.pow2(p0), 1n), RD.Nat.pow2(Nat.add(z, e))), F.Nat.monusf(bias, p0), RD.Nat.monus(bias, p0), Equal.sym(Nat, RD.Nat.monus(bias, p0), F.Nat.monusf(bias, p0), FL.L.monus(bias, p0)))))

def Lk.tiny(+h1: Nat, +p0: Nat, +bias: Nat, +n: Bool, +m: B.Bn, +e: Nat, +ed: {D.Dy.den(Xv(1n+h1, n, m, e)) == e : Nat}, +en: {D.Dy.num(Xv(1n+h1, n, m, e)) == B.Bd.sg(n, B.Bn.val(1n+h1, m)) : I.Int}, +om: {B.Bn.ok(1n+h1, m) == True{} : Bool})
  -> {P.Pz.btiny(1n+h1, p0, bias, B.Bd{n, m, e}) == P.Pz.tiny(p0, bias, Xv(1n+h1, n, m, e)) : Bool}:
  +h : Nat = 1n+h1
  +x = Xv(h, n, m, e)
  +c = P.Pz.mine(p0, bias)
  +v = B.Bn.val(h, m)
  +bm = P.Pz.bminm(h, p0)
  +lhs = RD.Nat.lt(Nat.mul(v, RD.Nat.pow2(c)), Nat.mul(P.Pz.minm(p0), RD.Nat.pow2(e)))
  Equal.trans(Bool, B.Bn.lt(B.Bn.shl(h, c, m), B.Bn.shl(h, e, bm)), lhs, P.Pz.tiny(p0, bias, x),
    Equal.trans(Bool, B.Bn.lt(B.Bn.shl(h, c, m), B.Bn.shl(h, e, bm)), RD.Nat.lt(B.Bn.val(h, B.Bn.shl(h, c, m)), B.Bn.val(h, B.Bn.shl(h, e, bm))), lhs,
      BP.Cmp.lt(h, B.Bn.shl(h, c, m), B.Bn.shl(h, e, bm), BP.Shl.ok(h1, c, m, om), BP.Shl.ok(h1, e, bm, Ominm(h1, p0))),
      Equal.trans(Bool, RD.Nat.lt(B.Bn.val(h, B.Bn.shl(h, c, m)), B.Bn.val(h, B.Bn.shl(h, e, bm))), RD.Nat.lt(Nat.mul(v, RD.Nat.pow2(c)), B.Bn.val(h, B.Bn.shl(h, e, bm))), lhs,
        Equal.cong(Nat, Bool, z => RD.Nat.lt(z, B.Bn.val(h, B.Bn.shl(h, e, bm))), B.Bn.val(h, B.Bn.shl(h, c, m)), Nat.mul(v, RD.Nat.pow2(c)), BP.Shl.val(h1, c, m)),
        Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.mul(v, RD.Nat.pow2(c)), z), B.Bn.val(h, B.Bn.shl(h, e, bm)), Nat.mul(P.Pz.minm(p0), RD.Nat.pow2(e)),
          Equal.trans(Nat, B.Bn.val(h, B.Bn.shl(h, e, bm)), Nat.mul(B.Bn.val(h, bm), RD.Nat.pow2(e)), Nat.mul(P.Pz.minm(p0), RD.Nat.pow2(e)), BP.Shl.val(h1, e, bm),
            Equal.cong(Nat, Nat, z => Nat.mul(z, RD.Nat.pow2(e)), B.Bn.val(h, bm), P.Pz.minm(p0), Vminm(h1, p0)))))),
    Equal.sym(Bool, P.Pz.tiny(p0, bias, x), lhs,
      Equal.trans(Bool, P.Pz.tiny(p0, bias, x), RD.Nat.lt(Nat.mul(v, RD.Nat.pow2(c)), Nat.mul(P.Pz.minm(p0), RD.Nat.pow2(D.Dy.den(x)))), lhs,
        Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.mul(z, RD.Nat.pow2(c)), Nat.mul(P.Pz.minm(p0), RD.Nat.pow2(D.Dy.den(x)))), RD.Int.mag(D.Dy.num(x)), v, Lk.mag(h, n, m, e, en)),
        Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.mul(v, RD.Nat.pow2(c)), Nat.mul(P.Pz.minm(p0), RD.Nat.pow2(z))), D.Dy.den(x), e, ed))))

def Lk.over(+h1: Nat, +p0: Nat, +bias: Nat, +n: Bool, +m: B.Bn, +e: Nat, +ed: {D.Dy.den(Xv(1n+h1, n, m, e)) == e : Nat}, +en: {D.Dy.num(Xv(1n+h1, n, m, e)) == B.Bd.sg(n, B.Bn.val(1n+h1, m)) : I.Int}, +om: {B.Bn.ok(1n+h1, m) == True{} : Bool})
  -> {P.Pz.bover(1n+h1, p0, bias, B.Bd{n, m, e}) == P.Pz.over(p0, bias, Xv(1n+h1, n, m, e)) : Bool}:
  +h : Nat = 1n+h1
  +x = Xv(h, n, m, e)
  +v = B.Bn.val(h, m)
  +bm = P.Pz.bmaxm(h, p0, bias, e)
  +lhs = RD.Nat.lt(P.Pz.maxm(p0, bias, e), v)
  Equal.trans(Bool, B.Bn.lt(bm, m), lhs, P.Pz.over(p0, bias, x),
    Equal.trans(Bool, B.Bn.lt(bm, m), RD.Nat.lt(B.Bn.val(h, bm), v), lhs, BP.Cmp.lt(h, bm, m, BP.Shl.ok(h1, Nat.add(F.Nat.monusf(bias, p0), e), B.Bn.sub(h, B.Bn.pow2(h, p0), B.BCons{1n, B.BNil{}}), Osub(h1, p0)), om),
      Equal.cong(Nat, Bool, z => RD.Nat.lt(z, v), B.Bn.val(h, bm), P.Pz.maxm(p0, bias, e), Vmaxm(h1, p0, bias, e))),
    Equal.sym(Bool, P.Pz.over(p0, bias, x), lhs,
      Equal.trans(Bool, P.Pz.over(p0, bias, x), RD.Nat.lt(P.Pz.maxm(p0, bias, e), RD.Int.mag(D.Dy.num(x))), lhs,
        Equal.cong(Nat, Bool, z => RD.Nat.lt(P.Pz.maxm(p0, bias, z), RD.Int.mag(D.Dy.num(x))), D.Dy.den(x), e, ed),
        Equal.cong(Nat, Bool, z => RD.Nat.lt(P.Pz.maxm(p0, bias, e), z), RD.Int.mag(D.Dy.num(x)), v, Lk.mag(h, n, m, e, en)))))

def Lk.below(+h1: Nat, +bias: Nat, +i: Nat, +n: Bool, +m: B.Bn, +e: Nat, +ed: {D.Dy.den(Xv(1n+h1, n, m, e)) == e : Nat}, +en: {D.Dy.num(Xv(1n+h1, n, m, e)) == B.Bd.sg(n, B.Bn.val(1n+h1, m)) : I.Int}, +om: {B.Bn.ok(1n+h1, m) == True{} : Bool})
  -> {P.Pz.bbelow(1n+h1, bias, i, B.Bd{n, m, e}) == P.Pz.below(bias, i, Xv(1n+h1, n, m, e)) : Bool}:
  +h : Nat = 1n+h1
  +x = Xv(h, n, m, e)
  +v = B.Bn.val(h, m)
  +j = RD.Nat.monus(Nat.add(i, e), bias)
  +jf = F.Nat.monusf(Nat.add(i, e), bias)
  +mid = Bool.pick(Bool, RD.Nat.lt(Nat.add(i, e), bias), False{}, RD.Nat.lt(v, RD.Nat.pow2(j)))
  Equal.trans(Bool, P.Pz.bbelow(h, bias, i, B.Bd{n, m, e}), mid, P.Pz.below(bias, i, x),
    Equal.trans(Bool, Bool.pick(Bool, F.Nat.ltf(Nat.add(i, e), bias), False{}, B.Bn.lt(m, B.Bn.pow2(h, jf))), Bool.pick(Bool, RD.Nat.lt(Nat.add(i, e), bias), False{}, B.Bn.lt(m, B.Bn.pow2(h, jf))), mid,
      Equal.cong(Bool, Bool, z => Bool.pick(Bool, z, False{}, B.Bn.lt(m, B.Bn.pow2(h, jf))), F.Nat.ltf(Nat.add(i, e), bias), RD.Nat.lt(Nat.add(i, e), bias), Equal.sym(Bool, RD.Nat.lt(Nat.add(i, e), bias), F.Nat.ltf(Nat.add(i, e), bias), FL.L.lt(Nat.add(i, e), bias))),
      Equal.cong(Bool, Bool, z => Bool.pick(Bool, RD.Nat.lt(Nat.add(i, e), bias), False{}, z), B.Bn.lt(m, B.Bn.pow2(h, jf)), RD.Nat.lt(v, RD.Nat.pow2(j)),
        Equal.trans(Bool, B.Bn.lt(m, B.Bn.pow2(h, jf)), RD.Nat.lt(v, B.Bn.val(h, B.Bn.pow2(h, jf))), RD.Nat.lt(v, RD.Nat.pow2(j)), BP.Cmp.lt(h, m, B.Bn.pow2(h, jf), om, BP.Pow2.ok(h1, jf)),
          Equal.cong(Nat, Bool, z => RD.Nat.lt(v, z), B.Bn.val(h, B.Bn.pow2(h, jf)), RD.Nat.pow2(j), BP.Vpw(h1, jf, j, Equal.sym(Nat, j, jf, FL.L.monus(Nat.add(i, e), bias))))))),
    Equal.sym(Bool, P.Pz.below(bias, i, x), mid,
      Equal.trans(Bool, P.Pz.below(bias, i, x), Bool.pick(Bool, RD.Nat.lt(Nat.add(i, e), bias), False{}, RD.Nat.lt(RD.Int.mag(D.Dy.num(x)), RD.Nat.pow2(j))), mid,
        Equal.cong(Nat, Bool, z => Bool.pick(Bool, RD.Nat.lt(Nat.add(i, z), bias), False{}, RD.Nat.lt(RD.Int.mag(D.Dy.num(x)), RD.Nat.pow2(RD.Nat.monus(Nat.add(i, z), bias)))), D.Dy.den(x), e, ed),
        Equal.cong(Nat, Bool, z => Bool.pick(Bool, RD.Nat.lt(Nat.add(i, e), bias), False{}, RD.Nat.lt(z, RD.Nat.pow2(j))), RD.Int.mag(D.Dy.num(x)), v, Lk.mag(h, n, m, e, en)))))

def Lk.find(+h1: Nat, +g: Nat, +bias: Nat, c: Nat, +rb: Nat, +n: Bool, +m: B.Bn, +e: Nat, +ed: {D.Dy.den(Xv(1n+h1, n, m, e)) == e : Nat}, +en: {D.Dy.num(Xv(1n+h1, n, m, e)) == B.Bd.sg(n, B.Bn.val(1n+h1, m)) : I.Int}, +om: {B.Bn.ok(1n+h1, m) == True{} : Bool})
  -> {P.Pz.bfind(1n+h1, g, bias, c, rb, B.Bd{n, m, e}) == P.Pz.find(g, bias, c, rb, Xv(1n+h1, n, m, e)) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+(+k):
      +h : Nat = 1n+h1
      +x = Xv(h, n, m, e)
      +i = Nat.mul(1n+rb, g)
      Equal.trans(Nat, Bool.pick(Nat, P.Pz.bbelow(h, bias, i, B.Bd{n, m, e}), rb, P.Pz.bfind(h, g, bias, k, 1n+rb, B.Bd{n, m, e})), Bool.pick(Nat, P.Pz.below(bias, i, x), rb, P.Pz.bfind(h, g, bias, k, 1n+rb, B.Bd{n, m, e})), Bool.pick(Nat, P.Pz.below(bias, i, x), rb, P.Pz.find(g, bias, k, 1n+rb, x)),
        Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, rb, P.Pz.bfind(h, g, bias, k, 1n+rb, B.Bd{n, m, e})), P.Pz.bbelow(h, bias, i, B.Bd{n, m, e}), P.Pz.below(bias, i, x), Lk.below(h1, bias, i, n, m, e, ed, en, om)),
        Equal.cong(Nat, Nat, z => Bool.pick(Nat, P.Pz.below(bias, i, x), rb, z), P.Pz.bfind(h, g, bias, k, 1n+rb, B.Bd{n, m, e}), P.Pz.find(g, bias, k, 1n+rb, x), Lk.find(h1, g, bias, k, 1n+rb, n, m, e, ed, en, om)))

def Sgn.nz1(+n: Bool, +w: Nat, +r: Nat) -> {RD.Int.signed(B.Bd.sg(n, 1n+w), r) == B.Bd.sg(n, r) : I.Int}:
  match n:
    case False{}:
      {==}
    case True{}:
      {==}

# a nonzero magnitude keeps its sign through Int.signed
def Sgn.nz(+n: Bool, +v: Nat, +r: Nat, +hv: {RD.Nat.lt(0n, v) == True{} : Bool}) -> {RD.Int.signed(B.Bd.sg(n, v), r) == B.Bd.sg(n, r) : I.Int}:
  +w = RD.Nat.monus(v, 1n)
  +ev = BP.Lt.wit(0n, v)(hv)
  Equal.trans(I.Int, RD.Int.signed(B.Bd.sg(n, v), r), RD.Int.signed(B.Bd.sg(n, 1n+w), r), B.Bd.sg(n, r),
    Equal.cong(Nat, I.Int, z => RD.Int.signed(B.Bd.sg(n, z), r), v, 1n+w, ev), Sgn.nz1(n, w, r))

# the results, once x is known nonzero
def Bflgo.lk2(+h1: Nat, +p0: Nat, +g: Nat, +rs: Nat, +n: Bool, +m: B.Bn, +e: Nat, +ed: {D.Dy.den(Xv(1n+h1, n, m, e)) == e : Nat}, +en: {D.Dy.num(Xv(1n+h1, n, m, e)) == B.Bd.sg(n, B.Bn.val(1n+h1, m)) : I.Int}, +om: {B.Bn.ok(1n+h1, m) == True{} : Bool},
  +hv: {RD.Nat.lt(0n, B.Bn.val(1n+h1, m)) == True{} : Bool}, t: Bool, o: Bool)
  -> {B.Bd.val(1n+h1, P.Pz.bfl.go(1n+h1, p0, g, rs, False{}, t, o, B.Bd{n, m, e})) == P.Pz.fl.go(p0, g, rs, False{}, t, o, Xv(1n+h1, n, m, e)) : D.Dy}:
  match t:
    case True{}:
      +h : Nat = 1n+h1
      +x = Xv(h, n, m, e)
      +v = B.Bn.val(h, m)
      +c = P.Pz.mine(p0, P.Pz.bias(g, rs))
      +mm = P.Pz.minm(p0)
      Equal.cong(I.Int, D.Dy, w => D.Dy.of(c, w), B.Bd.sg(n, B.Bn.val(h, P.Pz.bminm(h, p0))), RD.Int.signed(D.Dy.num(x), mm),
        Equal.trans(I.Int, B.Bd.sg(n, B.Bn.val(h, P.Pz.bminm(h, p0))), B.Bd.sg(n, mm), RD.Int.signed(D.Dy.num(x), mm),
          Equal.cong(Nat, I.Int, w => B.Bd.sg(n, w), B.Bn.val(h, P.Pz.bminm(h, p0)), mm, Vminm(h1, p0)),
          Equal.sym(I.Int, RD.Int.signed(D.Dy.num(x), mm), B.Bd.sg(n, mm),
            Equal.trans(I.Int, RD.Int.signed(D.Dy.num(x), mm), RD.Int.signed(B.Bd.sg(n, v), mm), B.Bd.sg(n, mm),
              Equal.cong(I.Int, I.Int, w => RD.Int.signed(w, mm), D.Dy.num(x), B.Bd.sg(n, v), en), Sgn.nz(n, v, mm, hv)))))
    case False{}:
      match o:
        case True{}:
          +h : Nat = 1n+h1
          +x = Xv(h, n, m, e)
          +v = B.Bn.val(h, m)
          +bias = P.Pz.bias(g, rs)
          +mx = P.Pz.maxm(p0, bias, e)
          Equal.trans(D.Dy, D.Dy.of(e, B.Bd.sg(n, B.Bn.val(h, P.Pz.bmaxm(h, p0, bias, e)))), D.Dy.of(e, B.Bd.sg(n, mx)), D.Dy.of(D.Dy.den(x), RD.Int.signed(D.Dy.num(x), P.Pz.maxm(p0, bias, D.Dy.den(x)))),
            Equal.cong(Nat, D.Dy, w => D.Dy.of(e, B.Bd.sg(n, w)), B.Bn.val(h, P.Pz.bmaxm(h, p0, bias, e)), mx, Vmaxm(h1, p0, bias, e)),
            Equal.sym(D.Dy, D.Dy.of(D.Dy.den(x), RD.Int.signed(D.Dy.num(x), P.Pz.maxm(p0, bias, D.Dy.den(x)))), D.Dy.of(e, B.Bd.sg(n, mx)),
              Equal.trans(D.Dy, D.Dy.of(D.Dy.den(x), RD.Int.signed(D.Dy.num(x), P.Pz.maxm(p0, bias, D.Dy.den(x)))), D.Dy.of(e, RD.Int.signed(D.Dy.num(x), mx)), D.Dy.of(e, B.Bd.sg(n, mx)),
                Equal.cong(Nat, D.Dy, w => D.Dy.of(w, RD.Int.signed(D.Dy.num(x), P.Pz.maxm(p0, bias, w))), D.Dy.den(x), e, ed),
                Equal.cong(I.Int, D.Dy, w => D.Dy.of(e, w), RD.Int.signed(D.Dy.num(x), mx), B.Bd.sg(n, mx),
                  Equal.trans(I.Int, RD.Int.signed(D.Dy.num(x), mx), RD.Int.signed(B.Bd.sg(n, v), mx), B.Bd.sg(n, mx),
                    Equal.cong(I.Int, I.Int, w => RD.Int.signed(w, mx), D.Dy.num(x), B.Bd.sg(n, v), en), Sgn.nz(n, v, mx, hv))))))
        case False{}:
          +h : Nat = 1n+h1
          +x = Xv(h, n, m, e)
          +r2 : B.Bd = B.Bd{n, m, e}
          Equal.trans(D.Dy, B.Bd.val(h, B.Bd.rne.n(h, P.Pz.bprec(h, p0, g, rs, r2), r2)), RD.Dy.rne(P.Pz.bprec(h, p0, g, rs, r2), x), RD.Dy.rne(P.Pz.prec(p0, g, rs, x), x),
            BP.Rne.n.lk(h1, P.Pz.bprec(h, p0, g, rs, r2), r2, (ed, en), om),
            Equal.cong(Nat, D.Dy, w => RD.Dy.rne(w, x), P.Pz.bprec(h, p0, g, rs, r2), P.Pz.prec(p0, g, rs, x),
              Equal.cong(Nat, Nat, w => Nat.add(p0, RD.Nat.monus(rs, P.Pz.rl(rs, w))), P.Pz.bfind(h, g, P.Pz.bias(g, rs), Nat.double(rs), 0n, r2), P.Pz.find(g, P.Pz.bias(g, rs), Nat.double(rs), 0n, x),
                Lk.find(h1, g, P.Pz.bias(g, rs), Nat.double(rs), 0n, n, m, e, ed, en, om))))

def Bflgo.lk(+h1: Nat, +p0: Nat, +g: Nat, +rs: Nat, +n: Bool, +m: B.Bn, +e: Nat, +ed: {D.Dy.den(Xv(1n+h1, n, m, e)) == e : Nat}, +en: {D.Dy.num(Xv(1n+h1, n, m, e)) == B.Bd.sg(n, B.Bn.val(1n+h1, m)) : I.Int}, +om: {B.Bn.ok(1n+h1, m) == True{} : Bool},
  z: Bool, +ez: {P.Pz.zero(Xv(1n+h1, n, m, e)) == z : Bool}, t: Bool, o: Bool)
  -> {B.Bd.val(1n+h1, P.Pz.bfl.go(1n+h1, p0, g, rs, z, t, o, B.Bd{n, m, e})) == P.Pz.fl.go(p0, g, rs, z, t, o, Xv(1n+h1, n, m, e)) : D.Dy}:
  match z:
    case True{}:
      {==}
    case False{}:
      +h : Nat = 1n+h1
      +x = Xv(h, n, m, e)
      +v = B.Bn.val(h, m)
      +bias = P.Pz.bias(g, rs)
      +hv = Equal.trans(Bool, RD.Nat.lt(0n, v), RD.Nat.lt(0n, RD.Int.mag(D.Dy.num(x))), True{},
        Equal.cong(Nat, Bool, w => RD.Nat.lt(0n, w), v, RD.Int.mag(D.Dy.num(x)), Equal.sym(Nat, RD.Int.mag(D.Dy.num(x)), v, Lk.mag(h, n, m, e, en))),
        Y.Bool.not_f(RD.Nat.lt(0n, RD.Int.mag(D.Dy.num(x))))(ez))
      Bflgo.lk2(h1, p0, g, rs, n, m, e, ed, en, om, hv, t, o)

def Pz.lk.n(+h1: Nat, +p0: Nat, +g: Nat, +rs: Nat, r: B.Bd, nf: BP.NF(1n+h1, r), +om: {B.Bn.ok(1n+h1, B.Bd.m(r)) == True{} : Bool})
  -> {B.Bd.val(1n+h1, P.Pz.bfl.n(1n+h1, p0, g, rs, r)) == P.Pz.fl(p0, g, rs, B.Bd.val(1n+h1, r)) : D.Dy}:
  match r:
    case B.Bd{+n, +m, +e}:
      match nf:
        case (ed0, en0):
          +h : Nat = 1n+h1
          +ed : {D.Dy.den(Xv(h, n, m, e)) == e : Nat} = ed0
          +en : {D.Dy.num(Xv(h, n, m, e)) == B.Bd.sg(n, B.Bn.val(h, m)) : I.Int} = en0
          +x = Xv(h, n, m, e)
          +bias = P.Pz.bias(g, rs)
          +r2 : B.Bd = B.Bd{n, m, e}
          +bz = P.Pz.bzero(r2)
          +bt = P.Pz.btiny(h, p0, bias, r2)
          +bo = P.Pz.bover(h, p0, bias, r2)
          +sz = P.Pz.zero(x)
          +st = P.Pz.tiny(p0, bias, x)
          +so = P.Pz.over(p0, bias, x)
          Equal.trans(D.Dy, B.Bd.val(h, P.Pz.bfl.go(h, p0, g, rs, bz, bt, bo, r2)), B.Bd.val(h, P.Pz.bfl.go(h, p0, g, rs, sz, st, so, r2)), P.Pz.fl.go(p0, g, rs, sz, st, so, x),
            Equal.trans(D.Dy, B.Bd.val(h, P.Pz.bfl.go(h, p0, g, rs, bz, bt, bo, r2)), B.Bd.val(h, P.Pz.bfl.go(h, p0, g, rs, sz, bt, bo, r2)), B.Bd.val(h, P.Pz.bfl.go(h, p0, g, rs, sz, st, so, r2)),
              Equal.cong(Bool, D.Dy, w => B.Bd.val(h, P.Pz.bfl.go(h, p0, g, rs, w, bt, bo, r2)), bz, sz, Lk.zero(h1, n, m, e, en, om)),
              Equal.trans(D.Dy, B.Bd.val(h, P.Pz.bfl.go(h, p0, g, rs, sz, bt, bo, r2)), B.Bd.val(h, P.Pz.bfl.go(h, p0, g, rs, sz, st, bo, r2)), B.Bd.val(h, P.Pz.bfl.go(h, p0, g, rs, sz, st, so, r2)),
                Equal.cong(Bool, D.Dy, w => B.Bd.val(h, P.Pz.bfl.go(h, p0, g, rs, sz, w, bo, r2)), bt, st, Lk.tiny(h1, p0, bias, n, m, e, ed, en, om)),
                Equal.cong(Bool, D.Dy, w => B.Bd.val(h, P.Pz.bfl.go(h, p0, g, rs, sz, st, w, r2)), bo, so, Lk.over(h1, p0, bias, n, m, e, ed, en, om)))),
            Bflgo.lk(h1, p0, g, rs, n, m, e, ed, en, om, sz, {==}, st, so))

# the run-time b-posit rounding is the spec's
def Pz.lk(+h1: Nat, +p0: Nat, +g: Nat, +rs: Nat, x: B.Bd, +ox: {B.Bd.ok(1n+h1, x) == True{} : Bool})
  -> {B.Bd.val(1n+h1, P.Pz.bfl(1n+h1, p0, g, rs, x)) == P.Pz.fl(p0, g, rs, B.Bd.val(1n+h1, x)) : D.Dy}:
  match x:
    case B.Bd{+neg, +m, +e}:
      +h : Nat = 1n+h1
      +nx = B.Bd.norm.go(h, neg, e, m, B.Bn.even(m))
      Equal.trans(D.Dy, B.Bd.val(h, P.Pz.bfl.n(h, p0, g, rs, nx)), P.Pz.fl(p0, g, rs, B.Bd.val(h, nx)), P.Pz.fl(p0, g, rs, D.Dy.of(e, B.Bd.sg(neg, B.Bn.val(h, m)))),
        Pz.lk.n(h1, p0, g, rs, nx, BP.Norm.nf(h, neg, e, m, B.Bn.even(m), {==}), BP.Norm.ok(h, neg, e, m, B.Bn.even(m), ox)),
        Equal.cong(D.Dy, D.Dy, w => P.Pz.fl(p0, g, rs, w), B.Bd.val(h, nx), D.Dy.of(e, B.Bd.sg(neg, B.Bn.val(h, m))), BP.Norm.val(h, neg, e, m, B.Bn.even(m), {==})))

# Operations and the quire
# ------------------------

def Pmul.lk(+h1: Nat, +p0: Nat, +g: Nat, +rs: Nat, +x: B.Bd, +y: B.Bd, +ox: {B.Bd.ok(1n+h1, x) == True{} : Bool}, +oy: {B.Bd.ok(1n+h1, y) == True{} : Bool})
  -> {B.Bd.val(1n+h1, P.Pz.bfl(1n+h1, p0, g, rs, B.Bd.mul(1n+h1, x, y))) == P.Pz.fl(p0, g, rs, D.Dy.mul(B.Bd.val(1n+h1, x), B.Bd.val(1n+h1, y))) : D.Dy}:
  +h : Nat = 1n+h1
  Equal.trans(D.Dy, B.Bd.val(h, P.Pz.bfl(h, p0, g, rs, B.Bd.mul(h, x, y))), P.Pz.fl(p0, g, rs, B.Bd.val(h, B.Bd.mul(h, x, y))), P.Pz.fl(p0, g, rs, D.Dy.mul(B.Bd.val(h, x), B.Bd.val(h, y))),
    Pz.lk(h1, p0, g, rs, B.Bd.mul(h, x, y), BP.Bd.mul.ok(h1, x, y, ox, oy)),
    Equal.cong(D.Dy, D.Dy, w => P.Pz.fl(p0, g, rs, w), B.Bd.val(h, B.Bd.mul(h, x, y)), D.Dy.mul(B.Bd.val(h, x), B.Bd.val(h, y)), BP.Bd.mul.lk(h1, x, y)))

def Padd.lk(+h1: Nat, +p0: Nat, +g: Nat, +rs: Nat, +x: B.Bd, +y: B.Bd, +ox: {B.Bd.ok(1n+h1, x) == True{} : Bool}, +oy: {B.Bd.ok(1n+h1, y) == True{} : Bool})
  -> {B.Bd.val(1n+h1, P.Pz.bfl(1n+h1, p0, g, rs, B.Bd.add(1n+h1, x, y))) == P.Pz.fl(p0, g, rs, D.Dy.add(B.Bd.val(1n+h1, x), B.Bd.val(1n+h1, y))) : D.Dy}:
  +h : Nat = 1n+h1
  Equal.trans(D.Dy, B.Bd.val(h, P.Pz.bfl(h, p0, g, rs, B.Bd.add(h, x, y))), P.Pz.fl(p0, g, rs, B.Bd.val(h, B.Bd.add(h, x, y))), P.Pz.fl(p0, g, rs, D.Dy.add(B.Bd.val(h, x), B.Bd.val(h, y))),
    Pz.lk(h1, p0, g, rs, B.Bd.add(h, x, y), BP.Bd.add.ok(h1, x, y, ox, oy)),
    Equal.cong(D.Dy, D.Dy, w => P.Pz.fl(p0, g, rs, w), B.Bd.val(h, B.Bd.add(h, x, y)), D.Dy.add(B.Bd.val(h, x), B.Bd.val(h, y)), BP.Bd.add.lk(h1, x, y, ox, oy)))

# the quire: the exact dot product, rounded once to the b-posit format;
# with Pz.model, its error is at most 2^-p0 |x . y| + minpos
def Quire.lk(+h1: Nat, +p0: Nat, +g: Nat, +rs: Nat, +xs: List<&2, B.Bd>, +ys: List<&2, B.Bd>, +ox: {B.Bd.oks(1n+h1, xs) == True{} : Bool}, +oy: {B.Bd.oks(1n+h1, ys) == True{} : Bool})
  -> {B.Bd.val(1n+h1, P.Pz.bfl(1n+h1, p0, g, rs, B.Bd.dot(1n+h1, xs, ys))) == P.Pz.fl(p0, g, rs, B.Dy.dotv(B.Bd.vals(1n+h1, xs), B.Bd.vals(1n+h1, ys))) : D.Dy}:
  +h : Nat = 1n+h1
  Equal.trans(D.Dy, B.Bd.val(h, P.Pz.bfl(h, p0, g, rs, B.Bd.dot(h, xs, ys))), P.Pz.fl(p0, g, rs, B.Bd.val(h, B.Bd.dot(h, xs, ys))), P.Pz.fl(p0, g, rs, B.Dy.dotv(B.Bd.vals(h, xs), B.Bd.vals(h, ys))),
    Pz.lk(h1, p0, g, rs, B.Bd.dot(h, xs, ys), BP.Dot.ok(h1, xs, ys, ox, oy)),
    Equal.cong(D.Dy, D.Dy, w => P.Pz.fl(p0, g, rs, w), B.Bd.val(h, B.Bd.dot(h, xs, ys)), B.Dy.dotv(B.Bd.vals(h, xs), B.Bd.vals(h, ys)), BP.Dot.lk(h1, xs, ys, ox, oy)))
