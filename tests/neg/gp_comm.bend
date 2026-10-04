# NEGATIVE CONTROL: the geometric product is NOT commutative; this claim
# must fail to check (it does for the plane: e1 e2 = -e2 e1).
import Base
import ../../src/ring.bend as R
import ../../src/spec.bend as S

law gp_comm:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for ~add_comm: R.Ring.Comm(T, add)
  for ~mul_comm: R.Ring.Comm(T, mul)
  for +d: Nat
  for +sig: S.Sig(d)
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  {S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y) == S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, x) : S.MV(T, d)}

def gp_comm(T, add, mul, neg, add_comm, mul_comm, d, sig, x, y):
  {==}
