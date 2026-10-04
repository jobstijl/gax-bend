# NEGATIVE CONTROL: the reverse is an ANTI-automorphism; claiming
# rev(e1 e2) == rev(e1) rev(e2) must fail (it is -e12 against +e12).
import Base
import ../../src/spec.bend as S
import ../../src/int.bend as I
import ./common.bend as C

law wrong:
  {S.MV.reverse(~I.Int, ~I.Int.neg, 2n, C.gp(C.e(0n), C.e(1n)))
    == C.gp(S.MV.reverse(~I.Int, ~I.Int.neg, 2n, C.e(0n)), S.MV.reverse(~I.Int, ~I.Int.neg, 2n, C.e(1n))) : S.MV(I.Int, 2n)}

def wrong():
  {==}
