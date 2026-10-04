# Functions of a bivector's square, for exp and log (gax ADR-019, numerics.md).
#
# In dimension 4 and below a bivector B squares to a Study number
# z = σ + π I (a scalar plus a multiple of the pseudoscalar). The power
# series of exp split into even and odd parts:
#   exp(B) = C(z) + S(z) B,  C(z) = Σ z^k/(2k)!,  S(z) = Σ z^k/(2k+1)!,
# entire functions of z, so no branch is involved. Where I² = 0 (PGA) a
# function of z is f(σ) + π f'(σ) I, so C, S and their derivatives at the
# real σ are all that is needed: C' = S/2, and S' = D below.
#
# Each function switches to its series for |σ| < 1/4, where the closed form
# cancels or divides by zero; the series there are exact to F32.

import Base

# below this |σ| the series are used
def Study.small() -> F32:
  0.25

# C(σ) = cos √-σ for σ < 0, cosh √σ for σ > 0
def Study.C.series(+s: F32) -> F32:
  (1.0 + s / 2.0 * (1.0 + s / 12.0 * (1.0 + s / 30.0 * (1.0 + s / 56.0 * (1.0 + s / 90.0)))) : F32)

def Study.C.closed(+s: F32) -> F32:
  Bool.pick(F32, F32.is_lt(s, 0.0), F32.cos(F32.sqrt(F32.neg(s))), F32.cosh(F32.sqrt(s)))

def Study.C(+s: F32) -> F32:
  Bool.pick(F32, F32.is_lt(F32.abs(s), Study.small()), Study.C.series(s), Study.C.closed(s))

# S(σ) = sin θ / θ with θ = √-σ, sinh r / r with r = √σ
def Study.S.series(+s: F32) -> F32:
  (1.0 + s / 6.0 * (1.0 + s / 20.0 * (1.0 + s / 42.0 * (1.0 + s / 72.0 * (1.0 + s / 110.0)))) : F32)

def Study.S.neg(+t: F32) -> F32:
  (F32.sin(t) / t : F32)

def Study.S.pos(+r: F32) -> F32:
  (F32.sinh(r) / r : F32)

def Study.S.closed(+s: F32) -> F32:
  Bool.pick(F32, F32.is_lt(s, 0.0), Study.S.neg(F32.sqrt(F32.neg(s))), Study.S.pos(F32.sqrt(s)))

def Study.S(+s: F32) -> F32:
  Bool.pick(F32, F32.is_lt(F32.abs(s), Study.small()), Study.S.series(s), Study.S.closed(s))

# D(σ) = S'(σ) = Σ (k+1) σ^k/(2k+3)! = (C - S) / (2σ)
def Study.D.series(+s: F32) -> F32:
  (0.16666667 + s * (0.016666668 + s * (5.952381e-4 + s * (1.1022928e-5 + s * (1.2526054e-7 + s * 9.6359945e-10)))) : F32)

def Study.D.closed(+s: F32) -> F32:
  ((Study.C.closed(s) - Study.S.closed(s)) / (2.0 * s) : F32)

def Study.D(+s: F32) -> F32:
  Bool.pick(F32, F32.is_lt(F32.abs(s), Study.small()), Study.D.series(s), Study.D.closed(s))

# θ / sin θ from (s, c) = (sin θ, cos θ) scaled alike: atan2(s, c) / s,
# which for c > 0 and small s / c is (1/c)(1 - t²/3 + t⁴/5 - ...) with
# t = s / c; past a quarter turn (c <= 0) atan2 itself is used
def Study.angle_over_sin.series(+s: F32, +c: F32) -> F32:
  +t2 = (s / c * (s / c) : F32)
  (1.0 / c * (1.0 - t2 * (0.33333334 - t2 * (0.2 - t2 * (0.14285715 - t2 * 0.11111111)))) : F32)

def Study.angle_over_sin(+s: F32, +c: F32) -> F32:
  Bool.pick(F32, F32.is_lt(F32.abs(s), (c * 0.1 : F32)), Study.angle_over_sin.series(s, c), (F32.atan2(s, c) / s : F32))
