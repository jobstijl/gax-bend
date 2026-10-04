# Complex numbers at F32: the Study numbers of an algebra whose
# pseudoscalar squares to -1 (STA). A bivector there squares to a scalar
# plus a multiple of I, and functions of that square are complex functions.

import Base

type Cx is Data:
  Cx{re: F32, im: F32}

def Cx.re(z: Cx) -> F32:
  match z:
    case Cx{re, im}:
      re

def Cx.im(z: Cx) -> F32:
  match z:
    case Cx{re, im}:
      im

def Cx.add(a: Cx, b: Cx) -> Cx:
  match a b:
    case Cx{ar, ai} Cx{br, bi}:
      Cx{(ar + br : F32), (ai + bi : F32)}

def Cx.mul(a: Cx, b: Cx) -> Cx:
  match a b:
    case Cx{+ar, +ai} Cx{+br, +bi}:
      Cx{(ar * br - ai * bi : F32), (ar * bi + ai * br : F32)}

def Cx.scale(+k: F32, z: Cx) -> Cx:
  match z:
    case Cx{re, im}:
      Cx{(k * re : F32), (k * im : F32)}

def Cx.abs2(z: Cx) -> F32:
  match z:
    case Cx{+re, +im}:
      (re * re + im * im : F32)

def Cx.inv(+z: Cx) -> Cx:
  match z:
    case Cx{re, im}:
      +n = Cx.abs2(Cx{re, im})
      Cx{(re / n : F32), (F32.neg(im) / n : F32)}

def Cx.div(a: Cx, +b: Cx) -> Cx:
  Cx.mul(a, Cx.inv(b))

# the principal square root: sqrt((|z| + re)/2) + i sign(im) sqrt((|z| - re)/2),
# with the larger part computed directly and the other as im / (2 larger)
def Cx.sqrt.go(+re: F32, +im: F32, +r: F32) -> Cx:
  +big = F32.sqrt(((r + F32.abs(re)) * 0.5 : F32))
  +small = Bool.pick(F32, F32.is_eq(big, 0.0), 0.0, (F32.abs(im) / (2.0 * big) : F32))
  +sg = Bool.pick(F32, F32.is_lt(im, 0.0), F32.neg(1.0), 1.0)
  Bool.pick(Cx, F32.is_lt(re, 0.0), Cx{small, (sg * big : F32)}, Cx{big, (sg * small : F32)})

def Cx.sqrt(z: Cx) -> Cx:
  match z:
    case Cx{+re, +im}:
      Cx.sqrt.go(re, im, F32.sqrt(Cx.abs2(Cx{re, im})))

# the principal logarithm: log |z| + i arg z
def Cx.log(+z: Cx) -> Cx:
  match z:
    case Cx{+re, +im}:
      Cx{(0.5 * F32.log(Cx.abs2(Cx{re, im})) : F32), F32.atan2(im, re)}

# cosh and sinh of a + i b
def Cx.cosh(z: Cx) -> Cx:
  match z:
    case Cx{+a, +b}:
      Cx{(F32.cosh(a) * F32.cos(b) : F32), (F32.sinh(a) * F32.sin(b) : F32)}

def Cx.sinh(z: Cx) -> Cx:
  match z:
    case Cx{+a, +b}:
      Cx{(F32.sinh(a) * F32.cos(b) : F32), (F32.cosh(a) * F32.sin(b) : F32)}

# below this |z| the series are used
def Cx.small() -> F32:
  0.0625

# Horner steps 1 + z/k (1 + ...) in complex arithmetic
def Cx.step(+z: Cx, +k: F32, rest: Cx) -> Cx:
  Cx.add(Cx{1.0, 0.0}, Cx.mul(Cx.scale((1.0 / k : F32), z), rest))

# C(z) = cosh √z and S(z) = sinh √z / √z: entire, so the branch of √z does
# not matter. exp(B) = C(B²) + S(B²) B.
def Cx.C(+z: Cx) -> Cx:
  Bool.pick(Cx, F32.is_lt(Cx.abs2(z), (Cx.small() * Cx.small() : F32)),
    Cx.step(z, 2.0, Cx.step(z, 12.0, Cx.step(z, 30.0, Cx.step(z, 56.0, Cx.step(z, 90.0, Cx{1.0, 0.0}))))),
    Cx.cosh(Cx.sqrt(z)))

def Cx.S.closed(+w: Cx) -> Cx:
  Cx.div(Cx.sinh(w), w)

def Cx.S(+z: Cx) -> Cx:
  Bool.pick(Cx, F32.is_lt(Cx.abs2(z), (Cx.small() * Cx.small() : F32)),
    Cx.step(z, 6.0, Cx.step(z, 20.0, Cx.step(z, 42.0, Cx.step(z, 72.0, Cx.step(z, 110.0, Cx{1.0, 0.0}))))),
    Cx.S.closed(Cx.sqrt(z)))

# 1/√z, principal
def Cx.rsqrt(+z: Cx) -> Cx:
  Cx.inv(Cx.sqrt(z))

# h(c, u) = acosh(c) / √u for c² - u = 1, the factor with log(c + P) = h P
# when P² = u: with q = √u, acosh c = log(c + q), and the ratio does not
# depend on the branch of q. Near c = 1, asinh(q)/q = 1 - u/6 + 3u²/40 -
# 5u³/112 + 35u⁴/1152 needs no root (for Re c > 0; near c = -1 the closed
# form is used).
def Cx.H.series(+u: Cx) -> Cx:
  Cx.add(Cx{1.0, 0.0}, Cx.mul(u, Cx.add(Cx{F32.neg(0.16666667), 0.0}, Cx.mul(u, Cx.add(Cx{0.075, 0.0}, Cx.mul(u, Cx.add(Cx{F32.neg(0.044642858), 0.0}, Cx.scale(0.030381944, u))))))))

def Cx.H.closed(+c: Cx, +q: Cx) -> Cx:
  Cx.div(Cx.log(Cx.add(c, q)), q)

def Cx.H(+c: Cx, +u: Cx) -> Cx:
  +near1 = Bool.and(F32.is_lt(Cx.abs2(u), (Cx.small() * Cx.small() : F32)), F32.is_lt(0.0, Cx.re(c)))
  Bool.pick(Cx, near1, Cx.H.series(u), Cx.H.closed(c, Cx.sqrt(u)))
