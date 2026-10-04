# Negative control for the sandwich support laws: the e023 coefficient of
# m p ~m (a PGA3D motor on a point) is the moved point's x, not zero, so
# the normaliser must leave monomials and the claim must fail.
import Base
import ../../src/spec.bend as S
import ../../src/ring.bend as R
import ../../src/norm.bend as N
import ../../proofs/norm.bend as NP
import ../../algebras/pga3d/kinds.bend as K

def Motor.transform.Point.zero_e023(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg),
  +a: K.Motor<T>, b: K.Point<T>)
  -> {S.MV.at(~T, ~zero, ~neg, 4n, [True{}, False{}, True{}, True{}], False{},
        S.MV.gp(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), S.MV.gp(~T, ~add, ~mul, ~neg, 4n, K.PGA3.sig(), K.Motor.tree(~T, ~neg, a), K.Point.tree(~T, ~neg, b)),
          S.MV.reverse(~T, ~neg, 4n, K.Motor.tree(~T, ~neg, a)))) == zero : T}:
  match a b:
    case K.Motor{a0, a1, a2, a3, a4, a5, a6, a7} K.Point{b0, b1, b2, b3}:
      NP.Norm.zero(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn,
        [a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3],
        S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, 4n, [True{}, False{}, True{}, True{}], False{},
          S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(),
            S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, 4n, K.PGA3.sig(),
              K.Motor.tree(~N.Tm, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}}),
              K.Point.tree(~N.Tm, ~N.Tm.neg, K.Point{N.TVar{8n}, N.TVar{9n}, N.TVar{10n}, N.TVar{11n}})),
            S.MV.reverse(~N.Tm, ~N.Tm.neg, 4n,
              K.Motor.tree(~N.Tm, ~N.Tm.neg, K.Motor{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}, N.TVar{5n}, N.TVar{6n}, N.TVar{7n}})))),
        {==})
