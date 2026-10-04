# Shared closed examples for the negative controls: VGA2D over exact integers.
import Base
import ../../src/spec.bend as S
import ../../src/int.bend as I

def Sg() -> S.Sig(2n):
  S.Gen{S.QP{}, S.Gen{S.QP{}, S.SigEnd{}}}

def e(i: Nat) -> S.MV(I.Int, 2n):
  S.MV.gen(I.Int, 2n, i, I.Int.one())

def gp(x: S.MV(I.Int, 2n), y: S.MV(I.Int, 2n)) -> S.MV(I.Int, 2n):
  S.MV.gp(~I.Int, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, 2n, Sg(), x, y)
