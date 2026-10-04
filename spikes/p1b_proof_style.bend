# P1b: proof style: congruence through a two-field lemma, subterms named by
# erased lets.
import Base
import ../src/ring.bend as R
import ../src/spec.bend as S

def Node.cong2(-A: Data, -a1: A, -b1: A, -a2: A, -b2: A, e1: {a1 == b1 : A}, e2: {a2 == b2 : A}) -> {S.N{a1, a2} == S.N{b1, b2} : S.Node<A>}:
  %e1 : {S.N{a1, a2} == S.N{_, b2} : S.Node<A>}
  %e2 : {S.N{a1, a2} == S.N{a1, _} : S.Node<A>}
  {==}

def Leaf.cong(-T: Data, -a: T, -b: T, e: {a == b : T}) -> {S.L{a} == S.L{b} : S.Leaf<T>}:
  %e : {S.L{a} == S.L{_} : S.Leaf<T>}
  {==}

law add_assoc:
  for ~T: Data
  for ~add: T -> T -> T
  for ~assoc: R.Ring.Assoc(T, add)
  for +d: Nat
  for x: S.MV(T, d)
  for y: S.MV(T, d)
  for z: S.MV(T, d)
  {S.MV.add(~T, ~add, d, S.MV.add(~T, ~add, d, x, y), z) == S.MV.add(~T, ~add, d, x, S.MV.add(~T, ~add, d, y, z)) : S.MV(T, d)}

def add_assoc(T, add, assoc, d, x, y, z):
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          {==}
        case S.L{a}:
          match y:
            case S.LZ{}:
              {==}
            case S.L{b}:
              match z:
                case S.LZ{}:
                  {==}
                case S.L{c}:
                  Leaf.cong(T, add(add(a, b), c), add(a, add(b, c)), assoc(a, b, c))
    case 1n+p:
      match x:
        case S.NZ{}:
          {==}
        case S.N{a1, a2}:
          match y:
            case S.NZ{}:
              {==}
            case S.N{b1, b2}:
              match z:
                case S.NZ{}:
                  {==}
                case S.N{c1, c2}:
                  -l1 = S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, a1, b1), c1)
                  -r1 = S.MV.add(~T, ~add, p, a1, S.MV.add(~T, ~add, p, b1, c1))
                  -l2 = S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, a2, b2), c2)
                  -r2 = S.MV.add(~T, ~add, p, a2, S.MV.add(~T, ~add, p, b2, c2))
                  Node.cong2(S.MV(T, p), l1, r1, l2, r2,
                    add_assoc(~T, ~add, ~assoc, p, a1, b1, c1), add_assoc(~T, ~add, ~assoc, p, a2, b2, c2))
