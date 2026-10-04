# Q3: a type-level MV(T, sig) as parameter and result of recursive live defs.
# Fuchs-Thery tree: a level for generator e holds N{x1, x2} = e*x1 + x2, Z{} = 0.
# gp(sig, f, n, x, y) = (-1)^n * inv^f(x) * y, the grade involution passed down
# as the flag f, the sign as the flag n, so no negated subtree is ever built.
import Base

type Q is Data:
  QP{}
  QN{}
  QZ{}

type S<-T: Data> is Data:
  S0{}
  S1{x: T}

type Lv<-A: Data> is Data:
  Z{}
  N{e: A, r: A}

def MV(T: Data, sig: List<&2, Q>) -> Data:
  match sig:
    case Nil{}:
      S<T>
    case Con{q, +rest}:
      Lv<MV(T, rest)>

def MV.add(~T: Data, ~add: T -> T -> T, sig: List<&2, Q>, a: MV(T, sig), b: MV(T, sig)) -> MV(T, sig):
  match sig:
    case Nil{}:
      match a:
        case S0{}:
          b
        case S1{x}:
          match b:
            case S0{}:
              S1{x}
            case S1{y}:
              S1{add(x, y)}
    case Con{q, +rest}:
      match a:
        case Z{}:
          b
        case N{a1, a2}:
          match b:
            case Z{}:
              N{a1, a2}
            case N{b1, b2}:
              N{MV.add(~T, ~add, rest, a1, b1), MV.add(~T, ~add, rest, a2, b2)}

def Leaf.mul(~T: Data, ~mul: T -> T -> T, ~neg: T -> T, n: Bool, a: T, b: T) -> T:
  match n:
    case False{}:
      mul(a, b)
    case True{}:
      neg(mul(a, b))

def MV.gp(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  sig: List<&2, Q>, +f: Bool, +n: Bool, x: MV(T, sig), y: MV(T, sig)) -> MV(T, sig):
  match sig:
    case Nil{}:
      match x:
        case S0{}:
          S0{}
        case S1{a}:
          match y:
            case S0{}:
              S0{}
            case S1{b}:
              S1{Leaf.mul(~T, ~mul, ~neg, n, a, b)}
    case Con{q, +rest}:
      match q:
        case QZ{}:
          match x:
            case Z{}:
              Z{}
            case N{x1, +x2}:
              match y:
                case Z{}:
                  Z{}
                case N{y1, +y2}:
                  +nf = Bool.xor(n, f)
                  e = MV.add(~T, ~add, rest, MV.gp(~T, ~add, ~mul, ~neg, rest, f, nf, x1, y2), MV.gp(~T, ~add, ~mul, ~neg, rest, Bool.not(f), n, x2, y1))
                  r2 = MV.gp(~T, ~add, ~mul, ~neg, rest, f, n, x2, y2)
                  N{e, r2}
        case QP{}:
          match x:
            case Z{}:
              Z{}
            case N{+x1, +x2}:
              match y:
                case Z{}:
                  Z{}
                case N{+y1, +y2}:
                  +nf = Bool.xor(n, f)
                  e = MV.add(~T, ~add, rest, MV.gp(~T, ~add, ~mul, ~neg, rest, f, nf, x1, y2), MV.gp(~T, ~add, ~mul, ~neg, rest, Bool.not(f), n, x2, y1))
                  r2 = MV.gp(~T, ~add, ~mul, ~neg, rest, f, n, x2, y2)
                  N{e, MV.add(~T, ~add, rest, MV.gp(~T, ~add, ~mul, ~neg, rest, Bool.not(f), nf, x1, y1), r2)}
        case QN{}:
          match x:
            case Z{}:
              Z{}
            case N{+x1, +x2}:
              match y:
                case Z{}:
                  Z{}
                case N{+y1, +y2}:
                  +nf = Bool.xor(n, f)
                  e = MV.add(~T, ~add, rest, MV.gp(~T, ~add, ~mul, ~neg, rest, f, nf, x1, y2), MV.gp(~T, ~add, ~mul, ~neg, rest, Bool.not(f), n, x2, y1))
                  r2 = MV.gp(~T, ~add, ~mul, ~neg, rest, f, n, x2, y2)
                  N{e, MV.add(~T, ~add, rest, MV.gp(~T, ~add, ~mul, ~neg, rest, Bool.not(f), Bool.not(nf), x1, y1), r2)}

def U32.neg(a: U32) -> U32:
  (0 - a : U32)

def gp2(sig: List<&2, Q>, x: MV(U32, sig), y: MV(U32, sig)) -> MV(U32, sig):
  MV.gp(~U32, ~U32.add, ~U32.mul, ~U32.neg, sig, False{}, False{}, x, y)

def E2() -> List<&2, Q>:
  [QP{}, QP{}]

def e1() -> MV(U32, E2()):
  N{N{S0{}, S1{1}}, Z{}}

def e2() -> MV(U32, E2()):
  N{Z{}, N{S1{1}, S0{}}}

def main() -> MV(U32, E2()) & MV(U32, E2()) & MV(U32, E2()) & MV(U32, [QZ{}, QP{}]):
  (gp2(E2(), e1(), e1()), gp2(E2(), e1(), e2()), gp2(E2(), e2(), e1()),
    gp2([QZ{}, QP{}], N{N{S0{}, S1{1}}, Z{}}, N{N{S0{}, S1{1}}, Z{}}))
