# NEGATIVE CONTROL: in a signature where e1 squares to -1, claiming
# e1 e1 == +1 must fail.
import Base
import ../../src/spec.bend as S
import ../../src/int.bend as I

def Sg() -> S.Sig(2n):
  S.Gen{S.QN{}, S.Gen{S.QP{}, S.SigEnd{}}}

law wrong:
  {S.MV.gp(~I.Int, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, 2n, Sg(), S.MV.gen(I.Int, 2n, 0n, I.Int.one()), S.MV.gen(I.Int, 2n, 0n, I.Int.one()))
    == S.MV.scalar(I.Int, 2n, I.Int.one()) : S.MV(I.Int, 2n)}

def wrong():
  {==}
