# A negative control: addition is linear in both operands at once, not in
# one alone, so (a + a') + b = (a + b) + (a' + b) must fail.

import Base
import ../../src/ring.bend as R
import ../../src/norm.bend as N
import ../../proofs/lin.bend as LN
import ../../algebras/vga3d/kinds.bend as K
import ../../algebras/vga3d/ops.bend as O
import ../../algebras/vga3d/lin.bend as L

def Vector.add.Vector.lin_a(~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),
  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),
  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg),
  a: K.Vector<T>, a2: K.Vector<T>, b: K.Vector<T>)
  -> {K.Vector.fields(T, O.Vector.add.Vector(~T, ~zero, ~add, ~mul, ~neg, L.Vector.plus(~T, ~add, a, a2), b))
    == K.Vector.fields(T, L.Vector.plus(~T, ~add, O.Vector.add.Vector(~T, ~zero, ~add, ~mul, ~neg, a, b), O.Vector.add.Vector(~T, ~zero, ~add, ~mul, ~neg, a2, b))) : List<&2, T>}:
  match a a2 b:
    case K.Vector{a_e1, a_e2, a_e3} K.Vector{c_e1, c_e2, c_e3} K.Vector{b_e1, b_e2, b_e3}:
      LN.Lin.eqs(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, [a_e1, a_e2, a_e3, c_e1, c_e2, c_e3, b_e1, b_e2, b_e3],
        K.Vector.fields(N.Tm, O.Vector.add.Vector(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, L.Vector.plus(~N.Tm, ~N.Tm.add, K.Vector{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}}, K.Vector{N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}), K.Vector{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}})),
        K.Vector.fields(N.Tm, L.Vector.plus(~N.Tm, ~N.Tm.add, O.Vector.add.Vector(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Vector{N.TVar{0n}, N.TVar{1n}, N.TVar{2n}}, K.Vector{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}}), O.Vector.add.Vector(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, K.Vector{N.TVar{3n}, N.TVar{4n}, N.TVar{5n}}, K.Vector{N.TVar{6n}, N.TVar{7n}, N.TVar{8n}}))),
        {==})
