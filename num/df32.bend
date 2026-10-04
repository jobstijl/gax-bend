# Double-F32 ("float-float"): a value hi + lo held as two F32, about 48
# bits of precision at native speed on every lane. Built from error-free
# transformations in plain F32 (Bend has no FMA, and contraction is off):
# TwoSum, Veltkamp's split and Dekker's product. The operations are
# Joldes, Muller and Popescu's (ACM TOMS 44(2), 2017): AccurateDWPlusDW
# (relative error below 3u², u = 2^-24) and DWTimesDW (below 5u²), whose
# bounds Muller and Rideau formalised (TOMS 2022). Here they serve as the
# reference that F32 kernels are measured against; their own proofs over
# a software float come later (docs/numerics.md).

import Base

type DF is Data:
  DF{hi: F32, lo: F32}

def DF.of(x: F32) -> DF:
  DF{x, 0.0}

def DF.hi(x: DF) -> F32:
  match x:
    case DF{h, l}:
      h

def DF.zero() -> DF:
  DF{0.0, 0.0}

# s + t = a + b exactly, given |a| >= |b|
def Fast2Sum(+a: F32, +b: F32) -> DF:
  +s = (a + b : F32)
  DF{s, (b - (s - a : F32) : F32)}

# s + t = a + b exactly
def TwoSum(+a: F32, +b: F32) -> DF:
  +s = (a + b : F32)
  +a2 = (s - b : F32)
  +b2 = (s - a2 : F32)
  DF{s, ((a - a2 : F32) + (b - b2 : F32) : F32)}

# a = hi + lo with hi on 12 bits: Veltkamp's split, C = 2^12 + 1
def Split(+a: F32) -> DF:
  +g = (4097.0 * a : F32)
  +h = (g + (a - g : F32) : F32)
  DF{h, (a - h : F32)}

def TwoProd.go(+a: F32, +b: F32, +p: F32, sa: DF, sb: DF) -> DF:
  match sa sb:
    case DF{+ah, +al} DF{+bh, +bl}:
      +e1 = ((ah * bh : F32) - p : F32)
      +e2 = (e1 + (ah * bl : F32) : F32)
      +e3 = (e2 + (al * bh : F32) : F32)
      DF{p, (e3 + (al * bl : F32) : F32)}

# p + e = a b exactly (Dekker), barring overflow and underflow
def TwoProd(+a: F32, +b: F32) -> DF:
  TwoProd.go(a, b, (a * b : F32), Split(a), Split(b))

def DF.add.fin(v: DF, +tl: F32) -> DF:
  match v:
    case DF{+vh, +vl}:
      Fast2Sum(vh, (tl + vl : F32))

def DF.add.go(s: DF, t: DF) -> DF:
  match s t:
    case DF{+sh, +sl} DF{+th, +tl}:
      DF.add.fin(Fast2Sum(sh, (sl + th : F32)), tl)

# AccurateDWPlusDW
def DF.add(x: DF, y: DF) -> DF:
  match x y:
    case DF{+xh, +xl} DF{+yh, +yl}:
      DF.add.go(TwoSum(xh, yh), TwoSum(xl, yl))

def DF.mul.go(c: DF, +cl2: F32) -> DF:
  match c:
    case DF{+ch, +cl1}:
      Fast2Sum(ch, (cl1 + cl2 : F32))

# DWTimesDW
def DF.mul(x: DF, y: DF) -> DF:
  match x y:
    case DF{+xh, +xl} DF{+yh, +yl}:
      DF.mul.go(TwoProd(xh, yh), ((xh * yl : F32) + (xl * yh : F32) : F32))

def DF.neg(x: DF) -> DF:
  match x:
    case DF{h, l}:
      DF{F32.neg(h), F32.neg(l)}

def DF.id(x: DF) -> DF:
  x

def DF.abs(x: DF) -> DF:
  match x:
    case DF{+h, +l}:
      Bool.pick(DF, F32.is_lt(h, 0.0), DF{F32.neg(h), F32.neg(l)}, DF{h, l})

# x - y as an F32 pair difference, then to the nearest F32
def DF.sub(x: DF, y: DF) -> DF:
  DF.add(x, DF.neg(y))

def DF.to_f32(x: DF) -> F32:
  match x:
    case DF{h, l}:
      (h + l : F32)
