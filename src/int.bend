# Exact integers: IPos{n} is n, INeg{n} is -(n+1), so every integer has one
# spelling and equal integers are the same term. The ring for exact checks,
# symbolic coefficients and, later, dyadic floats.

import Base

type Int is Data:
  IPos{n: Nat}
  INeg{n: Nat}

def Int.zero() -> Int:
  IPos{0n}

def Int.one() -> Int:
  IPos{1n}

def Int.from_nat(n: Nat) -> Int:
  IPos{n}

# m - k for naturals
def Int.sub_nat(m: Nat, k: Nat) -> Int:
  match m k:
    case 0n 0n:
      IPos{0n}
    case 0n 1n+kp:
      INeg{kp}
    case 1n+mp 0n:
      IPos{1n+mp}
    case 1n+mp 1n+kp:
      Int.sub_nat(mp, kp)

def Int.add(a: Int, b: Int) -> Int:
  match a b:
    case IPos{m} IPos{n}:
      IPos{Nat.add(m, n)}
    case INeg{m} INeg{n}:
      INeg{1n+Nat.add(m, n)}
    case IPos{m} INeg{n}:
      Int.sub_nat(m, 1n+n)
    case INeg{m} IPos{n}:
      Int.sub_nat(n, 1n+m)

def Int.neg(a: Int) -> Int:
  match a:
    case IPos{0n}:
      IPos{0n}
    case IPos{1n+m}:
      INeg{m}
    case INeg{m}:
      IPos{1n+m}

def Int.sub(a: Int, b: Int) -> Int:
  Int.add(a, Int.neg(b))

def Int.mul(a: Int, b: Int) -> Int:
  match a b:
    case IPos{m} IPos{n}:
      IPos{Nat.mul(m, n)}
    case INeg{m} INeg{n}:
      IPos{Nat.mul(1n+m, 1n+n)}
    case IPos{0n} INeg{n}:
      IPos{0n}
    case IPos{1n+m} INeg{+n}:
      INeg{Nat.add(Nat.mul(m, 1n+n), n)}
    case INeg{m} IPos{0n}:
      IPos{0n}
    case INeg{+m} IPos{1n+n}:
      INeg{Nat.add(Nat.mul(n, 1n+m), m)}

def Int.is_zero(a: Int) -> Bool:
  match a:
    case IPos{0n}:
      True{}
    case IPos{1n+m}:
      False{}
    case INeg{m}:
      False{}

# the order: nonnegativity, and the absolute value
def Int.pos(a: Int) -> Bool:
  match a:
    case IPos{n}:
      True{}
    case INeg{n}:
      False{}

def Int.abs(a: Int) -> Int:
  match a:
    case IPos{n}:
      IPos{n}
    case INeg{n}:
      IPos{1n+n}

def Int.show(a: Int) -> String:
  match a:
    case IPos{n}:
      Nat.show(n)
    case INeg{n}:
      "-" ++ Nat.show(1n+n)
