# NEGATIVE CONTROL: J_R is not its own inverse in the plane: J_R(J_R(e1))
# is -e1, so claiming it is e1 must fail (J_L undoes J_R, not J_R).
import Base
import ../../src/spec.bend as S
import ../../src/int.bend as I
import ./common.bend as C

law wrong:
  {S.MV.rcomp(~I.Int, ~I.Int.neg, 2n, S.MV.rcomp(~I.Int, ~I.Int.neg, 2n, C.e(0n))) == C.e(0n) : S.MV(I.Int, 2n)}

def wrong():
  {==}
