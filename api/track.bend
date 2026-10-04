# Tracking rounding error at run time (docs/numerics.md §3). For an output
# of a kernel with depth k, computed at F32 as c^, with A^ the same kernel
# computed at F32 on |inputs| with neg the identity (its absolute size),
#   |c^ - c| <= Track.factor(k) A^,
# which follows from Err.track (proofs/err.bend) under the hypothesis that
# F32 rounds by the standard model (u = 2^-24), for k u < 1/2.
#
# The factor: with g = k u, h(k) <= g / (1 - g), so h / (1 - h) <=
# g / (1 - 2g); the result is inflated by 1 + 2^-20 against the roundings
# of this formula itself.

import Base

def Track.factor(k: Nat) -> F32:
  +g = (U32.to_f32(U32.from_nat(k)) * 5.9604645e-8 : F32)
  (g / (1.0 - 2.0 * g) * 1.000001 : F32)
