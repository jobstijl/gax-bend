# Q10: a Layer-S law for EVERY signature, by induction on sig: MV.add is
# commutative over any ~add with a ~comm hypothesis. Layer S copied from q03:
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

law MV.add_comm:
  for ~T: Data
  for ~add: T -> T -> T
  for ~comm: @x: T -> @y: T -> {add(x, y) == add(y, x) : T}
  for sig: List<&2, Q>
  for a: MV(T, sig)
  for b: MV(T, sig)
  {MV.add(~T, ~add, sig, a, b) == MV.add(~T, ~add, sig, b, a) : MV(T, sig)}

def MV.add_comm(T, add, comm, sig, a, b):
  match sig:
    case Nil{}:
      match a b:
        case S0{} S0{}:
          {==}
        case S0{} S1{y}:
          {==}
        case S1{x} S0{}:
          {==}
        case S1{x} S1{y}:
          %comm(x, y) : {S1{add(x, y)} == S1{_} : S<T>}
          {==}
    case Con{q, +rest}:
      match a b:
        case Z{} Z{}:
          {==}
        case Z{} N{b1, b2}:
          {==}
        case N{a1, a2} Z{}:
          {==}
        case N{+a1, +a2} N{+b1, +b2}:
          %MV.add_comm(~T, ~add, ~comm, rest, a1, b1) : {N{MV.add(~T, ~add, rest, a1, b1), MV.add(~T, ~add, rest, a2, b2)} == N{_, MV.add(~T, ~add, rest, b2, a2)} : Lv<MV(T, rest)>}
          %MV.add_comm(~T, ~add, ~comm, rest, a2, b2) : {N{MV.add(~T, ~add, rest, a1, b1), MV.add(~T, ~add, rest, a2, b2)} == N{MV.add(~T, ~add, rest, a1, b1), _} : Lv<MV(T, rest)>}
          {==}
