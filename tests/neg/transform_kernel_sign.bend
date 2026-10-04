# NEGATIVE CONTROL: the generated PGA3D Motor.transform.Point kernel (the
# quadratic form) with one sign flipped in the weight entry m3_3 must not
# prove equal to the spec. Same shape as the generated .ok law.
import Base
import ../../src/spec.bend as S
import ../../src/ring.bend as R
import ../../src/norm.bend as N
import ../../proofs/norm.bend as NP
import ../../algebras/pga3d/kinds.bend as K

def wrong(~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, a: K.Motor<T>, b: K.Point<T>) -> K.Point<T>:
  match a b:
    case K.Motor{+a_s, +a_e23, +a_e31, +a_e12, +a_e01, +a_e02, +a_e03, +a_e0123} K.Point{+b_e032, +b_e013, +b_e021, +b_e123}:
      +q2_2 = mul(a_e31, a_e31)
      +q3_3 = mul(a_e12, a_e12)
      +q0_0 = mul(a_s, a_s)
      +q1_1 = mul(a_e23, a_e23)
      +q1_2 = mul(a_e23, a_e31)
      +q0_3 = mul(a_s, a_e12)
      +q0_2 = mul(a_s, a_e31)
      +q1_3 = mul(a_e23, a_e12)
      +q2_6 = mul(a_e31, a_e03)
      +q3_5 = mul(a_e12, a_e02)
      +q0_4 = mul(a_s, a_e01)
      +q1_7 = mul(a_e23, a_e0123)
      +q0_1 = mul(a_s, a_e23)
      +q2_3 = mul(a_e31, a_e12)
      +q1_6 = mul(a_e23, a_e03)
      +q0_5 = mul(a_s, a_e02)
      +q3_4 = mul(a_e12, a_e01)
      +q2_7 = mul(a_e31, a_e0123)
      +q0_6 = mul(a_s, a_e03)
      +q1_5 = mul(a_e23, a_e02)
      +q2_4 = mul(a_e31, a_e01)
      +q3_7 = mul(a_e12, a_e0123)
      +m0_0 = add(add(add(neg(q2_2), neg(q3_3)), q0_0), q1_1)
      +m0_1 = add(add(add(q1_2, q0_3), q0_3), q1_2)
      +m0_2 = add(add(add(neg(q0_2), q1_3), neg(q0_2)), q1_3)
      +m0_3 = add(add(add(add(add(add(add(q2_6, neg(q3_5)), neg(q0_4)), neg(q1_7)), neg(q0_4)), neg(q1_7)), q2_6), neg(q3_5))
      +m1_0 = add(add(add(q1_2, neg(q0_3)), neg(q0_3)), q1_2)
      +m1_1 = add(add(add(neg(q1_1), q0_0), neg(q3_3)), q2_2)
      +m1_2 = add(add(add(q0_1, q0_1), q2_3), q2_3)
      +m1_3 = add(add(add(add(add(add(add(neg(q1_6), neg(q0_5)), q3_4), neg(q2_7)), neg(q0_5)), neg(q1_6)), neg(q2_7)), q3_4)
      +m2_0 = add(add(add(q0_2, q1_3), q0_2), q1_3)
      +m2_1 = add(add(add(neg(q0_1), neg(q0_1)), q2_3), q2_3)
      +m2_2 = add(add(add(q0_0, neg(q1_1)), neg(q2_2)), q3_3)
      +m2_3 = add(add(add(add(add(add(add(neg(q0_6), q1_5), neg(q2_4)), neg(q3_7)), neg(q0_6)), q1_5), neg(q2_4)), neg(q3_7))
      +m3_3 = add(add(add(q0_0, q1_1), q2_2), neg(q3_3))
      K.Point{
        add(mul(b_e032, m0_0), add(mul(b_e013, m0_1), add(mul(b_e021, m0_2), mul(b_e123, m0_3)))),
        add(mul(b_e032, m1_0), add(mul(b_e013, m1_1), add(mul(b_e021, m1_2), mul(b_e123, m1_3)))),
        add(mul(b_e032, m2_0), add(mul(b_e013, m2_1), add(mul(b_e021, m2_2), mul(b_e123, m2_3)))),
        mul(b_e123, m3_3)}

def wrong.ok(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), a: K.Motor<T>, b: K.Point<T>)
  -> {K.Point.of_tree(~T, ~zero, ~neg, S.MV.gp(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), S.MV.gp(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Motor.tree(~T, ~neg, a), K.Point.tree(~T, ~neg, b)), S.MV.reverse(~T, ~neg, 4n, K.Motor.tree(~T, ~neg, a)))) == wrong(~T, ~zero, ~add, ~mul, ~neg, a, b) : K.Point<T>}:
  match a b:
    case K.Motor{+a_s, +a_e23, +a_e31, +a_e12, +a_e01, +a_e02, +a_e03, +a_e0123} K.Point{+b_e032, +b_e013, +b_e021, +b_e123}:
      K.Point.cong(T,
        S.MV.at(~T, ~zero, ~neg, 4n, [True{}, False{}, True{}, True{}], True{}, S.MV.gp(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), S.MV.gp(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Motor.tree(~T, ~neg, K.Motor{a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123}), K.Point.tree(~T, ~neg, K.Point{b_e032, b_e013, b_e021, b_e123})), S.MV.reverse(~T, ~neg, 4n, K.Motor.tree(~T, ~neg, K.Motor{a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123})))),
        S.MV.at(~T, ~zero, ~neg, 4n, [True{}, True{}, False{}, True{}], False{}, S.MV.gp(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), S.MV.gp(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Motor.tree(~T, ~neg, K.Motor{a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123}), K.Point.tree(~T, ~neg, K.Point{b_e032, b_e013, b_e021, b_e123})), S.MV.reverse(~T, ~neg, 4n, K.Motor.tree(~T, ~neg, K.Motor{a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123})))),
        S.MV.at(~T, ~zero, ~neg, 4n, [True{}, True{}, True{}, False{}], True{}, S.MV.gp(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), S.MV.gp(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Motor.tree(~T, ~neg, K.Motor{a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123}), K.Point.tree(~T, ~neg, K.Point{b_e032, b_e013, b_e021, b_e123})), S.MV.reverse(~T, ~neg, 4n, K.Motor.tree(~T, ~neg, K.Motor{a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123})))),
        S.MV.at(~T, ~zero, ~neg, 4n, [False{}, True{}, True{}, True{}], False{}, S.MV.gp(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), S.MV.gp(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Motor.tree(~T, ~neg, K.Motor{a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123}), K.Point.tree(~T, ~neg, K.Point{b_e032, b_e013, b_e021, b_e123})), S.MV.reverse(~T, ~neg, 4n, K.Motor.tree(~T, ~neg, K.Motor{a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123})))),
        K.Point.e032(T, wrong(~T, ~zero, ~add, ~mul, ~neg, K.Motor{a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123}, K.Point{b_e032, b_e013, b_e021, b_e123})),
        K.Point.e013(T, wrong(~T, ~zero, ~add, ~mul, ~neg, K.Motor{a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123}, K.Point{b_e032, b_e013, b_e021, b_e123})),
        K.Point.e021(T, wrong(~T, ~zero, ~add, ~mul, ~neg, K.Motor{a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123}, K.Point{b_e032, b_e013, b_e021, b_e123})),
        K.Point.e123(T, wrong(~T, ~zero, ~add, ~mul, ~neg, K.Motor{a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123}, K.Point{b_e032, b_e013, b_e021, b_e123})),
        NP.Norm.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123, b_e032, b_e013, b_e021, b_e123],
          S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, 4n, [True{}, False{}, True{}, True{}], True{}, S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), K.Motor.tree(~N.Tm, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}}), K.Point.tree(~N.Tm, ~N.Tm.neg, K.Point{N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})), S.MV.reverse(~N.Tm, ~N.Tm.neg, 4n, K.Motor.tree(~N.Tm, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}})))),
          K.Point.e032(N.Tm, wrong(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}}, K.Point{N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})),
          {==}),
        NP.Norm.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123, b_e032, b_e013, b_e021, b_e123],
          S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, 4n, [True{}, True{}, False{}, True{}], False{}, S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), K.Motor.tree(~N.Tm, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}}), K.Point.tree(~N.Tm, ~N.Tm.neg, K.Point{N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})), S.MV.reverse(~N.Tm, ~N.Tm.neg, 4n, K.Motor.tree(~N.Tm, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}})))),
          K.Point.e013(N.Tm, wrong(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}}, K.Point{N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})),
          {==}),
        NP.Norm.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123, b_e032, b_e013, b_e021, b_e123],
          S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, 4n, [True{}, True{}, True{}, False{}], True{}, S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), K.Motor.tree(~N.Tm, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}}), K.Point.tree(~N.Tm, ~N.Tm.neg, K.Point{N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})), S.MV.reverse(~N.Tm, ~N.Tm.neg, 4n, K.Motor.tree(~N.Tm, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}})))),
          K.Point.e021(N.Tm, wrong(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}}, K.Point{N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})),
          {==}),
        NP.Norm.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a_s, a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, a_e0123, b_e032, b_e013, b_e021, b_e123],
          S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, 4n, [False{}, True{}, True{}, True{}], False{}, S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), K.Motor.tree(~N.Tm, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}}), K.Point.tree(~N.Tm, ~N.Tm.neg, K.Point{N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})), S.MV.reverse(~N.Tm, ~N.Tm.neg, 4n, K.Motor.tree(~N.Tm, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}})))),
          K.Point.e123(N.Tm, wrong(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}}, K.Point{N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})),
          {==}))
