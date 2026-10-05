# A negative control: a sandwich is quadratic in its versor, so scaling the
# rotor by c does not scale the result by c, and the law must fail.

import Base
import ../../src/ring.bend as R
import ../../src/norm.bend as N
import ../../proofs/lin.bend as LN
import ../../algebras/vga3d/kinds.bend as K
import ../../algebras/vga3d/ops.bend as O
import ../../algebras/vga3d/lin.bend as L

def Rotor.transform.Vector.sc_a(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg),
  c: T, a: K.Rotor<T>, b: K.Vector<T>)
  -> {K.Vector.fields(T, O.Rotor.transform.Vector(~T, ~zero, ~add, ~mul, ~neg, K.Rotor.map(~T, ~T, ~(x => mul(c, x)), a), b))
    == K.Vector.fields(T, K.Vector.map(~T, ~T, ~(x => mul(c, x)), O.Rotor.transform.Vector(~T, ~zero, ~add, ~mul, ~neg, a, b))) : List<&2, T>}:
  match a b:
    case K.Rotor{a_s, a_e23, a_e31, a_e12} K.Vector{b_e1, b_e2, b_e3}:
      LN.Lin.eqs(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [c, a_s, a_e23, a_e31, a_e12, b_e1, b_e2, b_e3],
        K.Vector.fields(N.Tm, O.Rotor.transform.Vector(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Rotor.map(~N.Tm, ~N.Tm, ~(x => N.TMul{N.TVar{0n}, x}), K.Rotor{N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}}), K.Vector{N.TVar{5n}, N.TVar{6n}, N.TVar{7n}})),
        K.Vector.fields(N.Tm, K.Vector.map(~N.Tm, ~N.Tm, ~(x => N.TMul{N.TVar{0n}, x}), O.Rotor.transform.Vector(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Rotor{N.TVar{1n}, N.TVar{2n}, N.TVar{3n}, N.TVar{4n}}, K.Vector{N.TVar{5n}, N.TVar{6n}, N.TVar{7n}}))),
        {==})
