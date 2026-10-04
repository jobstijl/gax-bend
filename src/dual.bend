# Dual numbers over a ring T: a + b ε with ε² = 0. A commutative ring
# whenever T is one (proofs/dual.bend), so every generic kernel and every
# law runs on them. Running a kernel with ε on one input coefficient gives,
# in the ε parts of the outputs, the derivative along that coefficient: for
# a kernel linear in that operand, a column of its matrix (api/map.bend).
# That is how values and linear maps share one implementation here, and it
# is forward-mode differentiation besides.

import Base

type Dual<-T: Data> is Data:
  Dual{v: T, d: T}

def Dual.zero(~T: Data, ~zero: T) -> Dual<T>:
  Dual{zero, zero}

def Dual.one(~T: Data, ~zero: T, ~one: T) -> Dual<T>:
  Dual{one, zero}

def Dual.add(~T: Data, ~add: T -> T -> T, x: Dual<T>, y: Dual<T>) -> Dual<T>:
  match x y:
    case Dual{a, b} Dual{c, d}:
      Dual{add(a, c), add(b, d)}

# (a + b ε)(c + d ε) = a c + (a d + b c) ε
def Dual.mul(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, x: Dual<T>, y: Dual<T>) -> Dual<T>:
  match x y:
    case Dual{+a, b} Dual{+c, d}:
      Dual{mul(a, c), add(mul(a, d), mul(b, c))}

def Dual.neg(~T: Data, ~neg: T -> T, x: Dual<T>) -> Dual<T>:
  match x:
    case Dual{a, b}:
      Dual{neg(a), neg(b)}

def Dual.const(~T: Data, ~zero: T, a: T) -> Dual<T>:
  Dual{a, zero}

def Dual.v(-T: Data, x: Dual<T>) -> T:
  match x:
    case Dual{a, b}:
      a

def Dual.d(-T: Data, x: Dual<T>) -> T:
  match x:
    case Dual{a, b}:
      b
