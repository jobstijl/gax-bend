# NEGATIVE CONTROL: associativity with the inner sign flag dropped on the
# right must fail: (-1)^n2 matters. Instantiated at a closed 2D example
# over Int so the failure is a computed mismatch, not a missing proof.
import Base
import ../../src/spec.bend as S
import ../../src/int.bend as I

def Sg() -> S.Sig(2n):
  S.Gen{S.QP{}, S.Gen{S.QP{}, S.SigEnd{}}}

def e(i: Nat) -> S.MV(I.Int, 2n):
  S.MV.gen(I.Int, 2n, i, I.Int.one())

law wrong:
  {S.MV.gpf(~I.Int, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, 2n, False{}, False{},
     S.MV.gpf(~I.Int, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, 2n, False{}, True{}, e(0n), e(1n), Sg()), e(1n), Sg())
   == S.MV.gpf(~I.Int, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, 2n, False{}, False{}, e(0n),
     S.MV.gpf(~I.Int, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, 2n, False{}, False{}, e(1n), e(1n), Sg()), Sg()) : S.MV(I.Int, 2n)}

def wrong():
  {==}
