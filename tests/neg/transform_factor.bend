# NEGATIVE CONTROL: the versor law needs its factor ~m m. Without it,
# (m x ~m)(m y ~m) = m (x y) ~m is false: for m = 2 and x = y = e1 in the
# plane the left side is 16 and the right side 4.
import Base
import ../../src/spec.bend as S
import ../../src/int.bend as I
import ./common.bend as C

def two() -> S.MV(I.Int, 2n):
  S.MV.scalar(I.Int, 2n, I.IPos{2n})

def tr(x: S.MV(I.Int, 2n)) -> S.MV(I.Int, 2n):
  S.MV.transform(~I.Int, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, 2n, C.Sg(), two(), x)

def no_factor() -> {C.gp(tr(C.e(0n)), tr(C.e(0n))) == tr(C.gp(C.e(0n), C.e(0n))) : S.MV(I.Int, 2n)}:
  {==}
