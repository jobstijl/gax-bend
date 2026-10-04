# Q9b: a law over native F32 that takes "the hardware add is IEEE" as a ~
# hypothesis (stated against SoftF32.add), and the same as a +h point equation.
import Base
import ./q09_softf32.bend as S

law native_add_bits:
  for ~ieee: @a: F32 -> @b: F32 -> {F32.bits(F32.add(a, b)) == S.SoftF32.add(F32.bits(a), F32.bits(b)) : U32}
  for a: F32
  for b: F32
  {F32.bits(F32.add(a, b)) == S.SoftF32.add(F32.bits(a), F32.bits(b)) : U32}

def native_add_bits(ieee, a, b):
  ieee(a, b)
