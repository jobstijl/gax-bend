# NEGATIVE CONTROL: the involution must act on both factors; claiming
# inv(e1 e2) == inv(e1) e2 must fail (e12 against -e12).
import Base
import ../../src/spec.bend as S
import ../../src/int.bend as I
import ./common.bend as C

law wrong:
  {S.MV.involute(~I.Int, ~I.Int.neg, 2n, C.gp(C.e(0n), C.e(1n)))
    == C.gp(S.MV.involute(~I.Int, ~I.Int.neg, 2n, C.e(0n)), C.e(1n)) : S.MV(I.Int, 2n)}

def wrong():
  {==}
