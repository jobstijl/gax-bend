# Dyadic rationals: m / 2^e, the exact values of binary floating point.
# Every dyadic has exactly one spelling: an integer DInt{m}, or a proper
# fraction DFrac{neg, k, e} = ±(2k + 1) / 2^(e + 1) with an odd numerator.
# So equal dyadics are the same term, and the ring laws are equalities
# (proofs/dyadic.bend).
#
# Operations work on pairs (m, e) meaning m / 2^e and normalise the result
# (Dy.of): a sum over the common denominator 2^(e1 + e2), a product over
# 2^(e1 + e2). Runtime Nat is capped at 2^48 - 1 (bend-facts Q16), so this
# type is for proofs and small values, not an F32 oracle.

import Base
import ./int.bend as I

type Dy is Data:
  DInt{m: I.Int}
  DFrac{neg: Bool, k: Nat, e: Nat}

# Halving and doubling
# --------------------

def Nat.even(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match p:
        case 0n:
          False{}
        case 1n+q:
          Nat.even(q)

def Nat.half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+Nat.half(q)

def Int.dbl(a: I.Int) -> I.Int:
  match a:
    case I.IPos{n}:
      I.IPos{Nat.double(n)}
    case I.INeg{n}:
      I.INeg{1n+Nat.double(n)}

# a 2^k
def Int.sh(k: Nat, a: I.Int) -> I.Int:
  match k:
    case 0n:
      a
    case 1n+j:
      Int.dbl(Int.sh(j, a))

def Int.even(a: I.Int) -> Bool:
  match a:
    case I.IPos{n}:
      Nat.even(n)
    case I.INeg{n}:
      Bool.not(Nat.even(n))

def Int.half(a: I.Int) -> I.Int:
  match a:
    case I.IPos{n}:
      I.IPos{Nat.half(n)}
    case I.INeg{n}:
      I.INeg{Nat.half(n)}

# Normal form
# -----------

# an odd m over 2^(f + 1)
def Dy.odd(m: I.Int, f: Nat) -> Dy:
  match m:
    case I.IPos{n}:
      DFrac{False{}, Nat.half(n), f}
    case I.INeg{n}:
      DFrac{True{}, Nat.half(n), f}

# m / 2^e in normal form: strip common factors of 2
def Dy.of(+e: Nat, +m: I.Int) -> Dy:
  match e:
    case 0n:
      DInt{m}
    case 1n+f:
      Bool.pick(Dy, Int.even(m), Dy.of(f, Int.half(m)), Dy.odd(m, f))

# the numerator and the exponent of the denominator
def Dy.num(x: Dy) -> I.Int:
  match x:
    case DInt{m}:
      m
    case DFrac{s, +k, e}:
      Bool.pick(I.Int, s, I.INeg{Nat.double(k)}, I.IPos{1n+Nat.double(k)})

def Dy.den(x: Dy) -> Nat:
  match x:
    case DInt{m}:
      0n
    case DFrac{s, k, e}:
      1n+e

# The ring
# --------

def Dy.zero() -> Dy:
  DInt{I.IPos{0n}}

def Dy.one() -> Dy:
  DInt{I.IPos{1n}}

def Dy.add.go(+x: Dy, +y: Dy) -> Dy:
  Dy.of(Nat.add(Dy.den(x), Dy.den(y)), I.Int.add(Int.sh(Dy.den(y), Dy.num(x)), Int.sh(Dy.den(x), Dy.num(y))))

def Dy.mul.go(+x: Dy, +y: Dy) -> Dy:
  Dy.of(Nat.add(Dy.den(x), Dy.den(y)), I.Int.mul(Dy.num(x), Dy.num(y)))

# plain parameters, so the operations can be passed as T -> T -> T
def Dy.add(x: Dy, y: Dy) -> Dy:
  Dy.add.go(x, y)

def Dy.mul(x: Dy, y: Dy) -> Dy:
  Dy.mul.go(x, y)

def Dy.neg(x: Dy) -> Dy:
  match x:
    case DInt{m}:
      DInt{I.Int.neg(m)}
    case DFrac{s, k, e}:
      DFrac{Bool.not(s), k, e}

# The order
# ---------

def Dy.pos(x: Dy) -> Bool:
  match x:
    case DInt{m}:
      I.Int.pos(m)
    case DFrac{s, k, e}:
      Bool.not(s)

def Dy.abs(x: Dy) -> Dy:
  match x:
    case DInt{m}:
      DInt{I.Int.abs(m)}
    case DFrac{s, k, e}:
      DFrac{False{}, k, e}

# 2^-e
def Dy.ulp(e: Nat) -> Dy:
  Dy.of(e, I.IPos{1n})

def Dy.show(+x: Dy) -> String:
  I.Int.show(Dy.num(x)) ++ "/2^" ++ Nat.show(Dy.den(x))
