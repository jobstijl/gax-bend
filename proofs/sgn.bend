# Grade signs: MV.sgn(n, f, r) is a group action of Z2^3 (flags compose by
# xor), it is additive, keeps zero, and passes through MV.mk.

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S
import ./base.bend as B
import ./leaf.bend as L

# equal flags give equal grade signs
def Sgn.flag(~T: Data, ~neg: T -> T, -d: Nat, -n: Bool, -n2: Bool, -f: Bool, -f2: Bool, -r: Bool, -x: S.MV(T, d),
  en: {n == n2 : Bool}, ef: {f == f2 : Bool})
  -> {S.MV.sgn(~T, ~neg, d, n, f, r, x) == S.MV.sgn(~T, ~neg, d, n2, f2, r, x) : S.MV(T, d)}:
  %en : {S.MV.sgn(~T, ~neg, d, n, f, r, x) == S.MV.sgn(~T, ~neg, d, _, f2, r, x) : S.MV(T, d)}
  %ef : {S.MV.sgn(~T, ~neg, d, n, f, r, x) == S.MV.sgn(~T, ~neg, d, n, _, r, x) : S.MV(T, d)}
  {==}

# equal arguments give equal grade signs
def Sgn.cong(~T: Data, ~neg: T -> T, -d: Nat, -n: Bool, -f: Bool, -r: Bool, -x: S.MV(T, d), -y: S.MV(T, d),
  e: {x == y : S.MV(T, d)})
  -> {S.MV.sgn(~T, ~neg, d, n, f, r, x) == S.MV.sgn(~T, ~neg, d, n, f, r, y) : S.MV(T, d)}:
  %e : {S.MV.sgn(~T, ~neg, d, n, f, r, x) == S.MV.sgn(~T, ~neg, d, n, f, r, _) : S.MV(T, d)}
  {==}

# no flag set is the identity
def Sgn.id(~T: Data, ~neg: T -> T, +d: Nat, x: S.MV(T, d))
  -> {S.MV.sgn(~T, ~neg, d, False{}, False{}, False{}, x) == x : S.MV(T, d)}:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          {==}
        case S.L{a}:
          {==}
    case 1n+p:
      match x:
        case S.NZ{}:
          {==}
        case S.N{x1, x2}:
          B.Node.cong2(S.MV(T, p),
            S.MV.sgn(~T, ~neg, p, False{}, False{}, False{}, x1), x1,
            S.MV.sgn(~T, ~neg, p, False{}, False{}, False{}, x2), x2,
            Sgn.id(~T, ~neg, p, x1), Sgn.id(~T, ~neg, p, x2))

def Sgn.zero(~T: Data, ~neg: T -> T, d: Nat, n: Bool, f: Bool, r: Bool)
  -> {S.MV.sgn(~T, ~neg, d, n, f, r, S.MV.zero(T, d)) == S.MV.zero(T, d) : S.MV(T, d)}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Sgn.compose(~T: Data, ~neg: T -> T, ~neg_neg: R.Ring.NegNeg(T, neg), +d: Nat,
  +n1: Bool, +f1: Bool, +r1: Bool, +n2: Bool, +f2: Bool, +r2: Bool, x: S.MV(T, d))
  -> {S.MV.sgn(~T, ~neg, d, n1, f1, r1, S.MV.sgn(~T, ~neg, d, n2, f2, r2, x))
      == S.MV.sgn(~T, ~neg, d, Bool.xor(n1, n2), Bool.xor(f1, f2), Bool.xor(r1, r2), x) : S.MV(T, d)}:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          {==}
        case S.L{a}:
          B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n1, S.Ring.negf(~T, ~neg, n2, a)), S.Ring.negf(~T, ~neg, Bool.xor(n1, n2), a),
            L.Negf.negf(~T, ~neg, ~neg_neg, n1, n2, a))
    case 1n+p:
      match x:
        case S.NZ{}:
          {==}
        case S.N{x1, x2}:
          # the e-part: compose, then reorder the xors of the flags
          -nx = Bool.xor(Bool.xor(n1, f1), Bool.xor(n2, f2))
          -fx = Bool.xor(Bool.xor(f1, r1), Bool.xor(f2, r2))
          -ny = Bool.xor(Bool.xor(n1, n2), Bool.xor(f1, f2))
          -fy = Bool.xor(Bool.xor(f1, f2), Bool.xor(r1, r2))
          e1 = Equal.trans(S.MV(T, p),
            S.MV.sgn(~T, ~neg, p, Bool.xor(n1, f1), Bool.xor(f1, r1), r1,
              S.MV.sgn(~T, ~neg, p, Bool.xor(n2, f2), Bool.xor(f2, r2), r2, x1)),
            S.MV.sgn(~T, ~neg, p, nx, fx, Bool.xor(r1, r2), x1),
            S.MV.sgn(~T, ~neg, p, ny, fy, Bool.xor(r1, r2), x1),
            Sgn.compose(~T, ~neg, ~neg_neg, p, Bool.xor(n1, f1), Bool.xor(f1, r1), r1, Bool.xor(n2, f2), Bool.xor(f2, r2), r2, x1),
            Sgn.flag(~T, ~neg, p, nx, ny, fx, fy, Bool.xor(r1, r2), x1,
              B.Bool.xor_swap4(n1, f1, n2, f2), B.Bool.xor_swap4(f1, r1, f2, r2)))
          B.Node.cong2(S.MV(T, p),
            S.MV.sgn(~T, ~neg, p, Bool.xor(n1, f1), Bool.xor(f1, r1), r1,
              S.MV.sgn(~T, ~neg, p, Bool.xor(n2, f2), Bool.xor(f2, r2), r2, x1)),
            S.MV.sgn(~T, ~neg, p, ny, fy, Bool.xor(r1, r2), x1),
            S.MV.sgn(~T, ~neg, p, n1, f1, r1, S.MV.sgn(~T, ~neg, p, n2, f2, r2, x2)),
            S.MV.sgn(~T, ~neg, p, Bool.xor(n1, n2), Bool.xor(f1, f2), Bool.xor(r1, r2), x2),
            e1, Sgn.compose(~T, ~neg, ~neg_neg, p, n1, f1, r1, n2, f2, r2, x2))

def Sgn.add(~T: Data, ~add: T -> T -> T, ~neg: T -> T, ~neg_add: R.Ring.NegAdd(T, add, neg), +d: Nat,
  +n: Bool, +f: Bool, +r: Bool, a: S.MV(T, d), b: S.MV(T, d))
  -> {S.MV.sgn(~T, ~neg, d, n, f, r, S.MV.add(~T, ~add, d, a, b))
      == S.MV.add(~T, ~add, d, S.MV.sgn(~T, ~neg, d, n, f, r, a), S.MV.sgn(~T, ~neg, d, n, f, r, b)) : S.MV(T, d)}:
  match d:
    case 0n:
      match a b:
        case S.LZ{} S.LZ{}:
          {==}
        case S.LZ{} S.L{y}:
          {==}
        case S.L{x} S.LZ{}:
          {==}
        case S.L{x} S.L{y}:
          B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, add(x, y)), add(S.Ring.negf(~T, ~neg, n, x), S.Ring.negf(~T, ~neg, n, y)),
            L.Negf.add(~T, ~add, ~neg, ~neg_add, n, x, y))
    case 1n+p:
      match a b:
        case S.NZ{} S.NZ{}:
          {==}
        case S.NZ{} S.N{b1, b2}:
          {==}
        case S.N{a1, a2} S.NZ{}:
          {==}
        case S.N{a1, a2} S.N{b1, b2}:
          B.Node.cong2(S.MV(T, p),
            S.MV.sgn(~T, ~neg, p, Bool.xor(n, f), Bool.xor(f, r), r, S.MV.add(~T, ~add, p, a1, b1)),
            S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(n, f), Bool.xor(f, r), r, a1), S.MV.sgn(~T, ~neg, p, Bool.xor(n, f), Bool.xor(f, r), r, b1)),
            S.MV.sgn(~T, ~neg, p, n, f, r, S.MV.add(~T, ~add, p, a2, b2)),
            S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, n, f, r, a2), S.MV.sgn(~T, ~neg, p, n, f, r, b2)),
            Sgn.add(~T, ~add, ~neg, ~neg_add, p, Bool.xor(n, f), Bool.xor(f, r), r, a1, b1),
            Sgn.add(~T, ~add, ~neg, ~neg_add, p, n, f, r, a2, b2))

# a grade sign passes through the collapsing constructor
def Sgn.mk(~T: Data, ~neg: T -> T, d: Nat, n: Bool, f: Bool, r: Bool, a: S.MV(T, d), b: S.MV(T, d))
  -> {S.MV.sgn(~T, ~neg, 1n+d, n, f, r, S.MV.mk(T, d, a, b))
      == S.MV.mk(T, d, S.MV.sgn(~T, ~neg, d, Bool.xor(n, f), Bool.xor(f, r), r, a), S.MV.sgn(~T, ~neg, d, n, f, r, b)) : S.MV(T, 1n+d)}:
  match d:
    case 0n:
      match a:
        case S.LZ{}:
          match b:
            case S.LZ{}:
              {==}
            case S.L{y}:
              {==}
        case S.L{x}:
          {==}
    case 1n+p:
      match a:
        case S.NZ{}:
          match b:
            case S.NZ{}:
              {==}
            case S.N{b1, b2}:
              {==}
        case S.N{a1, a2}:
          {==}
