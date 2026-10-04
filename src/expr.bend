# A symbolic ring: terms built from variables by add, mul and neg, nothing
# simplified. Running a Layer-S operation at T = Expr records exactly the
# term the spec computes, which the generator prints as a mirror kernel.

import Base

type Expr is Data:
  EVar{name: String}
  EZero{}
  EAdd{a: Expr, b: Expr}
  EMul{a: Expr, b: Expr}
  ENeg{a: Expr}

def Expr.add(a: Expr, b: Expr) -> Expr:
  EAdd{a, b}

def Expr.mul(a: Expr, b: Expr) -> Expr:
  EMul{a, b}

def Expr.neg(a: Expr) -> Expr:
  ENeg{a}

# the term as Bend source over the template operations add, mul, neg, zero
def Expr.show(e: Expr) -> String:
  match e:
    case EVar{n}:
      n
    case EZero{}:
      "zero"
    case EAdd{a, b}:
      "add(" ++ Expr.show(a) ++ ", " ++ Expr.show(b) ++ ")"
    case EMul{a, b}:
      "mul(" ++ Expr.show(a) ++ ", " ++ Expr.show(b) ++ ")"
    case ENeg{a}:
      "neg(" ++ Expr.show(a) ++ ")"

# how many multiplications the term performs
def Expr.muls(e: Expr) -> Nat:
  match e:
    case EVar{n}:
      0n
    case EZero{}:
      0n
    case EAdd{a, b}:
      Nat.add(Expr.muls(a), Expr.muls(b))
    case EMul{a, b}:
      1n+Nat.add(Expr.muls(a), Expr.muls(b))
    case ENeg{a}:
      Expr.muls(a)
