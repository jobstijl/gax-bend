# NEGATIVE CONTROL: the commutator kernel is half of xy - yx. Claiming it
# equals the doubled spec itself, without adding it to itself, must fail
# (PGA3D Line.commutator.Line, the generated .ok with the doubling removed).
import Base
import ../../src/spec.bend as S
import ../../src/ring.bend as R
import ../../src/norm.bend as N
import ../../proofs/norm.bend as NP
import ../../algebras/pga3d/kinds.bend as K
import ../../algebras/pga3d/ops.bend as O

def not_halved(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg), a: K.Line<T>, b: K.Line<T>)
  -> {K.Line.of_tree(~T, ~zero, ~neg, S.MV.commutator2(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Line.tree(~T, ~neg, a), K.Line.tree(~T, ~neg, b))) == O.Line.commutator.Line(~T, ~zero, ~add, ~mul, ~neg, a, b) : K.Line<T>}:
  match a b:
    case K.Line{+a_e23, +a_e31, +a_e12, +a_e01, +a_e02, +a_e03} K.Line{+b_e23, +b_e31, +b_e12, +b_e01, +b_e02, +b_e03}:
      K.Line.cong(T,
        S.MV.at(~T, ~zero, ~neg, 4n, [False{}, False{}, True{}, True{}], False{}, S.MV.commutator2(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Line.tree(~T, ~neg, K.Line{a_e23, a_e31, a_e12, a_e01, a_e02, a_e03}), K.Line.tree(~T, ~neg, K.Line{b_e23, b_e31, b_e12, b_e01, b_e02, b_e03}))),
        S.MV.at(~T, ~zero, ~neg, 4n, [False{}, True{}, False{}, True{}], True{}, S.MV.commutator2(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Line.tree(~T, ~neg, K.Line{a_e23, a_e31, a_e12, a_e01, a_e02, a_e03}), K.Line.tree(~T, ~neg, K.Line{b_e23, b_e31, b_e12, b_e01, b_e02, b_e03}))),
        S.MV.at(~T, ~zero, ~neg, 4n, [False{}, True{}, True{}, False{}], False{}, S.MV.commutator2(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Line.tree(~T, ~neg, K.Line{a_e23, a_e31, a_e12, a_e01, a_e02, a_e03}), K.Line.tree(~T, ~neg, K.Line{b_e23, b_e31, b_e12, b_e01, b_e02, b_e03}))),
        S.MV.at(~T, ~zero, ~neg, 4n, [True{}, True{}, False{}, False{}], False{}, S.MV.commutator2(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Line.tree(~T, ~neg, K.Line{a_e23, a_e31, a_e12, a_e01, a_e02, a_e03}), K.Line.tree(~T, ~neg, K.Line{b_e23, b_e31, b_e12, b_e01, b_e02, b_e03}))),
        S.MV.at(~T, ~zero, ~neg, 4n, [True{}, False{}, True{}, False{}], False{}, S.MV.commutator2(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Line.tree(~T, ~neg, K.Line{a_e23, a_e31, a_e12, a_e01, a_e02, a_e03}), K.Line.tree(~T, ~neg, K.Line{b_e23, b_e31, b_e12, b_e01, b_e02, b_e03}))),
        S.MV.at(~T, ~zero, ~neg, 4n, [True{}, False{}, False{}, True{}], False{}, S.MV.commutator2(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Line.tree(~T, ~neg, K.Line{a_e23, a_e31, a_e12, a_e01, a_e02, a_e03}), K.Line.tree(~T, ~neg, K.Line{b_e23, b_e31, b_e12, b_e01, b_e02, b_e03}))),
        K.Line.e23(T, O.Line.commutator.Line(~T, ~zero, ~add, ~mul, ~neg, K.Line{a_e23, a_e31, a_e12, a_e01, a_e02, a_e03}, K.Line{b_e23, b_e31, b_e12, b_e01, b_e02, b_e03})),
        K.Line.e31(T, O.Line.commutator.Line(~T, ~zero, ~add, ~mul, ~neg, K.Line{a_e23, a_e31, a_e12, a_e01, a_e02, a_e03}, K.Line{b_e23, b_e31, b_e12, b_e01, b_e02, b_e03})),
        K.Line.e12(T, O.Line.commutator.Line(~T, ~zero, ~add, ~mul, ~neg, K.Line{a_e23, a_e31, a_e12, a_e01, a_e02, a_e03}, K.Line{b_e23, b_e31, b_e12, b_e01, b_e02, b_e03})),
        K.Line.e01(T, O.Line.commutator.Line(~T, ~zero, ~add, ~mul, ~neg, K.Line{a_e23, a_e31, a_e12, a_e01, a_e02, a_e03}, K.Line{b_e23, b_e31, b_e12, b_e01, b_e02, b_e03})),
        K.Line.e02(T, O.Line.commutator.Line(~T, ~zero, ~add, ~mul, ~neg, K.Line{a_e23, a_e31, a_e12, a_e01, a_e02, a_e03}, K.Line{b_e23, b_e31, b_e12, b_e01, b_e02, b_e03})),
        K.Line.e03(T, O.Line.commutator.Line(~T, ~zero, ~add, ~mul, ~neg, K.Line{a_e23, a_e31, a_e12, a_e01, a_e02, a_e03}, K.Line{b_e23, b_e31, b_e12, b_e01, b_e02, b_e03})),
        NP.Norm.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, b_e23, b_e31, b_e12, b_e01, b_e02, b_e03],
          S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, 4n, [False{}, False{}, True{}, True{}], False{}, S.MV.commutator2(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), K.Line.tree(~N.Tm, ~N.Tm.neg, K.Line{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}), K.Line.tree(~N.Tm, ~N.Tm.neg, K.Line{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}}))),
          K.Line.e23(N.Tm, O.Line.commutator.Line(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Line{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}, K.Line{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})),
          {==}),
        NP.Norm.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, b_e23, b_e31, b_e12, b_e01, b_e02, b_e03],
          S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, 4n, [False{}, True{}, False{}, True{}], True{}, S.MV.commutator2(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), K.Line.tree(~N.Tm, ~N.Tm.neg, K.Line{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}), K.Line.tree(~N.Tm, ~N.Tm.neg, K.Line{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}}))),
          K.Line.e31(N.Tm, O.Line.commutator.Line(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Line{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}, K.Line{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})),
          {==}),
        NP.Norm.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, b_e23, b_e31, b_e12, b_e01, b_e02, b_e03],
          S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, 4n, [False{}, True{}, True{}, False{}], False{}, S.MV.commutator2(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), K.Line.tree(~N.Tm, ~N.Tm.neg, K.Line{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}), K.Line.tree(~N.Tm, ~N.Tm.neg, K.Line{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}}))),
          K.Line.e12(N.Tm, O.Line.commutator.Line(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Line{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}, K.Line{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})),
          {==}),
        NP.Norm.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, b_e23, b_e31, b_e12, b_e01, b_e02, b_e03],
          S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, 4n, [True{}, True{}, False{}, False{}], False{}, S.MV.commutator2(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), K.Line.tree(~N.Tm, ~N.Tm.neg, K.Line{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}), K.Line.tree(~N.Tm, ~N.Tm.neg, K.Line{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}}))),
          K.Line.e01(N.Tm, O.Line.commutator.Line(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Line{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}, K.Line{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})),
          {==}),
        NP.Norm.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, b_e23, b_e31, b_e12, b_e01, b_e02, b_e03],
          S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, 4n, [True{}, False{}, True{}, False{}], False{}, S.MV.commutator2(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), K.Line.tree(~N.Tm, ~N.Tm.neg, K.Line{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}), K.Line.tree(~N.Tm, ~N.Tm.neg, K.Line{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}}))),
          K.Line.e02(N.Tm, O.Line.commutator.Line(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Line{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}, K.Line{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})),
          {==}),
        NP.Norm.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a_e23, a_e31, a_e12, a_e01, a_e02, a_e03, b_e23, b_e31, b_e12, b_e01, b_e02, b_e03],
          S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, 4n, [True{}, False{}, False{}, True{}], False{}, S.MV.commutator2(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(), K.Line.tree(~N.Tm, ~N.Tm.neg, K.Line{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}), K.Line.tree(~N.Tm, ~N.Tm.neg, K.Line{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}}))),
          K.Line.e03(N.Tm, O.Line.commutator.Line(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Line{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}, K.Line{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})),
          {==}))
