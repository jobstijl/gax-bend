# NEGATIVE CONTROL: e1 ^ e2 is a 2-vector; claiming it is a 3-vector (its
# grade-3 part is all of it) must fail.
import Base
import ../../src/spec.bend as S
import ../../src/int.bend as I
import ./common.bend as C

law wrong:
  S.MV.Homog(I.Int, 2n, 3n, S.MV.wedge(~I.Int, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, 2n, C.e(0n), C.e(1n)))

def wrong():
  {==}
