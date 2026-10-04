# Q9c: the same hypothesis as an ordinary +h point equation (no ~).
import Base
import ./q09_softf32.bend as S

law native_add_bits_h:
  for a: F32
  for b: F32
  for +h: {F32.bits(F32.add(a, b)) == S.SoftF32.add(F32.bits(a), F32.bits(b)) : U32}
  {S.SoftF32.add(F32.bits(a), F32.bits(b)) == F32.bits(F32.add(a, b)) : U32}

def native_add_bits_h(a, b, h):
  Equal.sym(U32, F32.bits(F32.add(a, b)), S.SoftF32.add(F32.bits(a), F32.bits(b)), h)
