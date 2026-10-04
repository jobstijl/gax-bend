# Grades: the outer product of a j-vector and a k-vector is a (j+k)-vector.

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S
import ./base.bend as B
import ./add.bend as A
import ./gp.bend as P

# Constructors
# ------------

def Node.e_or(-A: Data, z: A, x: S.Node<A>) -> A:
  match x:
    case S.NZ{}:
      z
    case S.N{e, r}:
      e

def Node.r_or(-A: Data, z: A, x: S.Node<A>) -> A:
  match x:
    case S.NZ{}:
      z
    case S.N{e, r}:
      r

def Node.inj1(-A: Data, -a: A, -b: A, -c: A, -d: A, e: {S.N{a, b} == S.N{c, d} : S.Node<A>}) -> {a == c : A}:
  Equal.cong(S.Node<A>, A, w => Node.e_or(A, a, w), S.N{a, b}, S.N{c, d}, e)

def Node.inj2(-A: Data, -a: A, -b: A, -c: A, -d: A, e: {S.N{a, b} == S.N{c, d} : S.Node<A>}) -> {b == d : A}:
  Equal.cong(S.Node<A>, A, w => Node.r_or(A, b, w), S.N{a, b}, S.N{c, d}, e)

def Node.disc(-A: Data, x: S.Node<A>) -> Type:
  match x:
    case S.NZ{}:
      Unit
    case S.N{e, r}:
      Empty

def Node.nz.empty(-A: Data, -c: A, -d: A, e: {S.NZ{} == S.N{c, d} : S.Node<A>}) -> Empty:
  %e : Node.disc(A, _)
  Unit{}

# zero is not a level
def Node.nz(-A: Data, -B: Type, -c: A, -d: A, e: {S.NZ{} == S.N{c, d} : S.Node<A>}) -> B:
  Empty.absurd(B, Node.nz.empty(A, c, d, e))

# from mk(a, b) == N{c, d}: a == c
def Mk.inv1(-T: Data, d: Nat, a: S.MV(T, d), b: S.MV(T, d), -c: S.MV(T, d), -e: S.MV(T, d),
  h: {S.MV.mk(T, d, a, b) == S.N{c, e} : S.MV(T, 1n+d)}) -> {a == c : S.MV(T, d)}:
  match d:
    case 0n:
      match a:
        case S.LZ{}:
          match b:
            case S.LZ{}:
              Node.nz(S.Leaf<T>, {S.LZ{} == c : S.Leaf<T>}, c, e, h)
            case S.L{y}:
              Node.inj1(S.Leaf<T>, S.LZ{}, S.L{y}, c, e, h)
        case S.L{x}:
          Node.inj1(S.Leaf<T>, S.L{x}, b, c, e, h)
    case 1n+p:
      match a:
        case S.NZ{}:
          match b:
            case S.NZ{}:
              Node.nz(S.MV(T, 1n+p), {S.NZ{} == c : S.MV(T, 1n+p)}, c, e, h)
            case S.N{b1, b2}:
              Node.inj1(S.MV(T, 1n+p), S.NZ{}, S.N{b1, b2}, c, e, h)
        case S.N{a1, a2}:
          Node.inj1(S.MV(T, 1n+p), S.N{a1, a2}, b, c, e, h)

# from mk(a, b) == N{c, d}: b == d
def Mk.inv2(-T: Data, d: Nat, a: S.MV(T, d), b: S.MV(T, d), -c: S.MV(T, d), -e: S.MV(T, d),
  h: {S.MV.mk(T, d, a, b) == S.N{c, e} : S.MV(T, 1n+d)}) -> {b == e : S.MV(T, d)}:
  match d:
    case 0n:
      match a:
        case S.LZ{}:
          match b:
            case S.LZ{}:
              Node.nz(S.Leaf<T>, {S.LZ{} == e : S.Leaf<T>}, c, e, h)
            case S.L{y}:
              Node.inj2(S.Leaf<T>, S.LZ{}, S.L{y}, c, e, h)
        case S.L{x}:
          Node.inj2(S.Leaf<T>, S.L{x}, b, c, e, h)
    case 1n+p:
      match a:
        case S.NZ{}:
          match b:
            case S.NZ{}:
              Node.nz(S.MV(T, 1n+p), {S.NZ{} == e : S.MV(T, 1n+p)}, c, e, h)
            case S.N{b1, b2}:
              Node.inj2(S.MV(T, 1n+p), S.NZ{}, S.N{b1, b2}, c, e, h)
        case S.N{a1, a2}:
          Node.inj2(S.MV(T, 1n+p), S.N{a1, a2}, b, c, e, h)

def Leaf.disc(-T: Data, x: S.Leaf<T>) -> Type:
  match x:
    case S.LZ{}:
      Unit
    case S.L{a}:
      Empty

def Leaf.lz.empty(-T: Data, -a: T, e: {S.LZ{} == S.L{a} : S.Leaf<T>}) -> Empty:
  %e : Leaf.disc(T, _)
  Unit{}

# a leaf zero is not a coefficient
def Leaf.lz(-T: Data, -B: Type, -a: T, e: {S.LZ{} == S.L{a} : S.Leaf<T>}) -> B:
  Empty.absurd(B, Leaf.lz.empty(T, a, e))

def Nat.add_succ_r(j: Nat, +k: Nat) -> {Nat.add(j, 1n+k) == 1n+Nat.add(j, k) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+i:
      Equal.cong(Nat, Nat, w => 1n+w, Nat.add(i, 1n+k), 1n+Nat.add(i, k), Nat.add_succ_r(i, k))

# Grade projection
# ----------------

def Grade.zero(-T: Data, d: Nat, k: Nat) -> {S.MV.grade(T, d, k, S.MV.zero(T, d)) == S.MV.zero(T, d) : S.MV(T, d)}:
  match d:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case 1n+p:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}

def Grade.idx(-T: Data, -d: Nat, -k: Nat, -k2: Nat, -x: S.MV(T, d), e: {k == k2 : Nat})
  -> {S.MV.grade(T, d, k, x) == S.MV.grade(T, d, k2, x) : S.MV(T, d)}:
  %e : {S.MV.grade(T, d, k, x) == S.MV.grade(T, d, _, x) : S.MV(T, d)}
  {==}

# a grade projection keeps the zero level of MV.mk
def Grade.mk_s(-T: Data, +d: Nat, +j: Nat, a: S.MV(T, d), b: S.MV(T, d))
  -> {S.MV.grade(T, 1n+d, 1n+j, S.MV.mk(T, d, a, b)) == S.MV.mk(T, d, S.MV.grade(T, d, j, a), S.MV.grade(T, d, 1n+j, b)) : S.MV(T, 1n+d)}:
  match d:
    case 0n:
      match a:
        case S.LZ{}:
          match b:
            case S.LZ{}:
              Equal.sym(S.MV(T, 1n), S.MV.mk(T, 0n, S.MV.grade(T, 0n, j, S.LZ{}), S.MV.grade(T, 0n, 1n+j, S.LZ{})), S.NZ{},
                P.Mk.cong(T, 0n, S.MV.grade(T, 0n, j, S.LZ{}), S.LZ{}, S.MV.grade(T, 0n, 1n+j, S.LZ{}), S.LZ{},
                  Grade.zero(T, 0n, j), {==}))
            case S.L{y}:
              {==}
        case S.L{x}:
          {==}
    case 1n+p:
      match a:
        case S.NZ{}:
          match b:
            case S.NZ{}:
              Equal.sym(S.MV(T, 2n+p), S.MV.mk(T, 1n+p, S.MV.grade(T, 1n+p, j, S.NZ{}), S.MV.grade(T, 1n+p, 1n+j, S.NZ{})), S.NZ{},
                P.Mk.cong(T, 1n+p, S.MV.grade(T, 1n+p, j, S.NZ{}), S.NZ{}, S.MV.grade(T, 1n+p, 1n+j, S.NZ{}), S.NZ{},
                  Grade.zero(T, 1n+p, j), Grade.zero(T, 1n+p, 1n+j)))
            case S.N{b1, b2}:
              {==}
        case S.N{a1, a2}:
          {==}

def Grade.mk_0(-T: Data, +d: Nat, a: S.MV(T, d), b: S.MV(T, d))
  -> {S.MV.grade(T, 1n+d, 0n, S.MV.mk(T, d, a, b)) == S.MV.mk(T, d, S.MV.zero(T, d), S.MV.grade(T, d, 0n, b)) : S.MV(T, 1n+d)}:
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
              Equal.sym(S.MV(T, 2n+p), S.MV.mk(T, 1n+p, S.MV.zero(T, 1n+p), S.MV.grade(T, 1n+p, 0n, S.NZ{})), S.NZ{},
                P.Mk.cong(T, 1n+p, S.MV.zero(T, 1n+p), S.NZ{}, S.MV.grade(T, 1n+p, 0n, S.NZ{}), S.NZ{},
                  {==}, Grade.zero(T, 1n+p, 0n)))
            case S.N{b1, b2}:
              {==}
        case S.N{a1, a2}:
          {==}

# grade projection is additive
def Grade.add(~T: Data, ~add: T -> T -> T, +d: Nat, +k: Nat, a: S.MV(T, d), b: S.MV(T, d))
  -> {S.MV.grade(T, d, k, S.MV.add(~T, ~add, d, a, b)) == S.MV.add(~T, ~add, d, S.MV.grade(T, d, k, a), S.MV.grade(T, d, k, b)) : S.MV(T, d)}:
  match d:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case 1n+p:
      match k:
        case 0n:
          match a:
            case S.NZ{}:
              {==}
            case S.N{+a1, +a2}:
              match b:
                case S.NZ{}:
                  Equal.sym(S.MV(T, 1n+p), S.MV.add(~T, ~add, 1n+p, S.MV.grade(T, 1n+p, 0n, S.N{a1, a2}), S.NZ{}), S.MV.grade(T, 1n+p, 0n, S.N{a1, a2}),
                    A.Add.zero_r(~T, ~add, 1n+p, S.MV.grade(T, 1n+p, 0n, S.N{a1, a2})))
                case S.N{+b1, +b2}:
                  B.Eq.join(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, S.MV.add(~T, ~add, p, a2, b2))), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, a2)), S.MV.mk(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, b2))), S.MV.mk(T, p, S.MV.zero(T, p), S.MV.add(~T, ~add, p, S.MV.grade(T, p, 0n, a2), S.MV.grade(T, p, 0n, b2))),
                      P.Mk.cong(T, p, S.MV.zero(T, p), S.MV.zero(T, p), S.MV.grade(T, p, 0n, S.MV.add(~T, ~add, p, a2, b2)), S.MV.add(~T, ~add, p, S.MV.grade(T, p, 0n, a2), S.MV.grade(T, p, 0n, b2)),
                        {==},
                        Grade.add(~T, ~add, p, 0n, a2, b2)),
                      Equal.trans(S.MV(T, 1n+p), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, a2)), S.MV.mk(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, b2))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.zero(T, p), S.MV.zero(T, p)), S.MV.add(~T, ~add, p, S.MV.grade(T, p, 0n, a2), S.MV.grade(T, p, 0n, b2))), S.MV.mk(T, p, S.MV.zero(T, p), S.MV.add(~T, ~add, p, S.MV.grade(T, p, 0n, a2), S.MV.grade(T, p, 0n, b2))),
                        A.Add.mk(~T, ~add, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, a2), S.MV.zero(T, p), S.MV.grade(T, p, 0n, b2)),
                        P.Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.zero(T, p), S.MV.zero(T, p)), S.MV.zero(T, p), S.MV.add(~T, ~add, p, S.MV.grade(T, p, 0n, a2), S.MV.grade(T, p, 0n, b2)), S.MV.add(~T, ~add, p, S.MV.grade(T, p, 0n, a2), S.MV.grade(T, p, 0n, b2)),
                          A.Add.zero_l(~T, ~add, p, S.MV.zero(T, p)),
                          {==})))
        case 1n+j:
          match a:
            case S.NZ{}:
              {==}
            case S.N{+a1, +a2}:
              match b:
                case S.NZ{}:
                  Equal.sym(S.MV(T, 1n+p), S.MV.add(~T, ~add, 1n+p, S.MV.grade(T, 1n+p, 1n+j, S.N{a1, a2}), S.NZ{}), S.MV.grade(T, 1n+p, 1n+j, S.N{a1, a2}),
                    A.Add.zero_r(~T, ~add, 1n+p, S.MV.grade(T, 1n+p, 1n+j, S.N{a1, a2})))
                case S.N{+b1, +b2}:
                  B.Eq.join(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.grade(T, p, j, S.MV.add(~T, ~add, p, a1, b1)), S.MV.grade(T, p, 1n+j, S.MV.add(~T, ~add, p, a2, b2))), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.grade(T, p, j, a1), S.MV.grade(T, p, 1n+j, a2)), S.MV.mk(T, p, S.MV.grade(T, p, j, b1), S.MV.grade(T, p, 1n+j, b2))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.grade(T, p, j, a1), S.MV.grade(T, p, j, b1)), S.MV.add(~T, ~add, p, S.MV.grade(T, p, 1n+j, a2), S.MV.grade(T, p, 1n+j, b2))),
                      P.Mk.cong(T, p, S.MV.grade(T, p, j, S.MV.add(~T, ~add, p, a1, b1)), S.MV.add(~T, ~add, p, S.MV.grade(T, p, j, a1), S.MV.grade(T, p, j, b1)), S.MV.grade(T, p, 1n+j, S.MV.add(~T, ~add, p, a2, b2)), S.MV.add(~T, ~add, p, S.MV.grade(T, p, 1n+j, a2), S.MV.grade(T, p, 1n+j, b2)),
                        Grade.add(~T, ~add, p, j, a1, b1),
                        Grade.add(~T, ~add, p, 1n+j, a2, b2)),
                      A.Add.mk(~T, ~add, p, S.MV.grade(T, p, j, a1), S.MV.grade(T, p, 1n+j, a2), S.MV.grade(T, p, j, b1), S.MV.grade(T, p, 1n+j, b2)))

def Wedge.zero_l(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, d: Nat, f: Bool, n: Bool, y: S.MV(T, d)) -> {S.MV.wedgef(~T, ~add, ~mul, ~neg, d, f, n, S.MV.zero(T, d), y) == S.MV.zero(T, d) : S.MV(T, d)}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Wedge.zero_r(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, d: Nat, f: Bool, n: Bool, x: S.MV(T, d)) -> {S.MV.wedgef(~T, ~add, ~mul, ~neg, d, f, n, x, S.MV.zero(T, d)) == S.MV.zero(T, d) : S.MV(T, d)}:
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
        case S.N{a, b}:
          {==}

# a wedge with a zero left operand is zero in every grade
def Wedge.grade.zl(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, +p: Nat, +f: Bool, +n: Bool, +k: Nat, -x1: S.MV(T, p), +y2: S.MV(T, p), h: {S.MV.zero(T, p) == x1 : S.MV(T, p)})
  -> {S.MV.grade(T, p, k, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x1, y2)) == S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x1, y2) : S.MV(T, p)}:
    %h : {S.MV.grade(T, p, k, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, _, y2)) == S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, _, y2) : S.MV(T, p)}
  Equal.trans(S.MV(T, p), S.MV.grade(T, p, k, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, S.MV.zero(T, p), y2)), S.MV.zero(T, p), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, S.MV.zero(T, p), y2),
      Equal.trans(S.MV(T, p), S.MV.grade(T, p, k, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, S.MV.zero(T, p), y2)), S.MV.grade(T, p, k, S.MV.zero(T, p)), S.MV.zero(T, p),
        Equal.cong(S.MV(T, p), S.MV(T, p), w => S.MV.grade(T, p, k, w), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, S.MV.zero(T, p), y2), S.MV.zero(T, p), Wedge.zero_l(~T, ~add, ~mul, ~neg, p, f, n, y2)),
        Grade.zero(T, p, k)),
      Equal.sym(S.MV(T, p), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, S.MV.zero(T, p), y2), S.MV.zero(T, p),
        Wedge.zero_l(~T, ~add, ~mul, ~neg, p, f, n, y2)))

# a wedge with a zero right operand is zero in every grade
def Wedge.grade.zr(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, +p: Nat, +f: Bool, +n: Bool, +k: Nat, +x2: S.MV(T, p), -y1: S.MV(T, p), h: {S.MV.zero(T, p) == y1 : S.MV(T, p)})
  -> {S.MV.grade(T, p, k, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y1)) == S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y1) : S.MV(T, p)}:
    %h : {S.MV.grade(T, p, k, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, _)) == S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, _) : S.MV(T, p)}
  Equal.trans(S.MV(T, p), S.MV.grade(T, p, k, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.zero(T, p))), S.MV.zero(T, p), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.zero(T, p)),
      Equal.trans(S.MV(T, p), S.MV.grade(T, p, k, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.zero(T, p))), S.MV.grade(T, p, k, S.MV.zero(T, p)), S.MV.zero(T, p),
        Equal.cong(S.MV(T, p), S.MV(T, p), w => S.MV.grade(T, p, k, w), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.zero(T, p)), S.MV.zero(T, p), Wedge.zero_r(~T, ~add, ~mul, ~neg, p, f, n, x2)),
        Grade.zero(T, p, k)),
      Equal.sym(S.MV(T, p), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.zero(T, p)), S.MV.zero(T, p),
        Wedge.zero_r(~T, ~add, ~mul, ~neg, p, f, n, x2)))

# a wedge with a zero operand is zero
def Wedge.grade.zx(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, +p: Nat, +f: Bool, +n: Bool, -x1: S.MV(T, p), +y2: S.MV(T, p), h: {S.MV.zero(T, p) == x1 : S.MV(T, p)})
  -> {S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x1, y2) == S.MV.zero(T, p) : S.MV(T, p)}:
  %h : {S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, _, y2) == S.MV.zero(T, p) : S.MV(T, p)}
  Wedge.zero_l(~T, ~add, ~mul, ~neg, p, f, n, y2)

def Wedge.grade.zy(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, +p: Nat, +f: Bool, +n: Bool, +x2: S.MV(T, p), -y1: S.MV(T, p), h: {S.MV.zero(T, p) == y1 : S.MV(T, p)})
  -> {S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y1) == S.MV.zero(T, p) : S.MV(T, p)}:
  %h : {S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, _) == S.MV.zero(T, p) : S.MV(T, p)}
  Wedge.zero_r(~T, ~add, ~mul, ~neg, p, f, n, x2)

# the outer product of a j-vector and a k-vector is a (j+k)-vector
def Wedge.grade(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, +d: Nat, +f: Bool, +n: Bool, +j: Nat, +k: Nat, x: S.MV(T, d), y: S.MV(T, d),
  +hx: {S.MV.grade(T, d, j, x) == x : S.MV(T, d)}, +hy: {S.MV.grade(T, d, k, y) == y : S.MV(T, d)})
  -> {S.MV.grade(T, d, Nat.add(j, k), S.MV.wedgef(~T, ~add, ~mul, ~neg, d, f, n, x, y)) == S.MV.wedgef(~T, ~add, ~mul, ~neg, d, f, n, x, y) : S.MV(T, d)}:
  match d:
    case 0n:
      match j:
        case 0n:
          match k:
            case 0n:
              {==}
            case 1n+k2:
              match x:
                case S.LZ{}:
                  match y:
                    case S.LZ{}:
                      {==}
                    case S.L{b}:
                      Leaf.lz(T, {S.MV.grade(T, 0n, 1n+k2, S.MV.wedgef(~T, ~add, ~mul, ~neg, 0n, f, n, S.LZ{}, S.L{b})) == S.MV.wedgef(~T, ~add, ~mul, ~neg, 0n, f, n, S.LZ{}, S.L{b}) : S.MV(T, 0n)}, b, hy)
                case S.L{a}:
                  match y:
                    case S.LZ{}:
                      {==}
                    case S.L{b}:
                      Leaf.lz(T, {S.MV.grade(T, 0n, 1n+k2, S.MV.wedgef(~T, ~add, ~mul, ~neg, 0n, f, n, S.L{a}, S.L{b})) == S.MV.wedgef(~T, ~add, ~mul, ~neg, 0n, f, n, S.L{a}, S.L{b}) : S.MV(T, 0n)}, b, hy)
        case 1n+j2:
          match x:
            case S.LZ{}:
              {==}
            case S.L{a}:
              Leaf.lz(T, {S.MV.grade(T, 0n, Nat.add(1n+j2, k), S.MV.wedgef(~T, ~add, ~mul, ~neg, 0n, f, n, S.L{a}, y)) == S.MV.wedgef(~T, ~add, ~mul, ~neg, 0n, f, n, S.L{a}, y) : S.MV(T, 0n)}, a, hx)
    case 1n+p:
      match j:
        case 0n:
          match k:
            case 0n:
              match x:
                case S.NZ{}:
                  Grade.zero(T, 1n+p, Nat.add(0n, 0n))
                case S.N{+x1, +x2}:
                  match y:
                    case S.NZ{}:
                      Grade.zero(T, 1n+p, Nat.add(0n, 0n))
                    case S.N{+y1, +y2}:
                      +hx1 = Mk.inv1(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, x2), x1, x2, hx)
                      +hx2 = Mk.inv2(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, x2), x1, x2, hx)
                      +hy1 = Mk.inv1(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, y2), y1, y2, hy)
                      +hy2 = Mk.inv2(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, y2), y1, y2, hy)
                      +ex1 = Wedge.grade.zx(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2, hx1)
                      +ey1 = Wedge.grade.zy(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1, hy1)
                      Equal.trans(S.MV(T, 1n+p), S.MV.grade(T, 1n+p, 0n, S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2))), S.MV.mk(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2)),
                          Grade.mk_0(T, p, S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2)),
                          P.Mk.cong(T, p, S.MV.zero(T, p), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.grade(T, p, 0n, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2),
                            Equal.sym(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.zero(T, p),
                              Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.add(~T, ~add, p, S.MV.zero(T, p), S.MV.zero(T, p)), S.MV.zero(T, p),
                                A.Add.cong(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.zero(T, p), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1), S.MV.zero(T, p),
                                  ex1,
                                  ey1),
                                A.Add.zero_l(~T, ~add, p, S.MV.zero(T, p)))),
                            Wedge.grade(~T, ~add, ~mul, ~neg, p, f, n, 0n, 0n, x2, y2, hx2, hy2)))
            case 1n+k2:
              match x:
                case S.NZ{}:
                  Grade.zero(T, 1n+p, Nat.add(0n, 1n+k2))
                case S.N{+x1, +x2}:
                  match y:
                    case S.NZ{}:
                      Grade.zero(T, 1n+p, Nat.add(0n, 1n+k2))
                    case S.N{+y1, +y2}:
                      +hx1 = Mk.inv1(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, x2), x1, x2, hx)
                      +hx2 = Mk.inv2(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, x2), x1, x2, hx)
                      +hy1 = Mk.inv1(T, p, S.MV.grade(T, p, k2, y1), S.MV.grade(T, p, 1n+k2, y2), y1, y2, hy)
                      +hy2 = Mk.inv2(T, p, S.MV.grade(T, p, k2, y1), S.MV.grade(T, p, 1n+k2, y2), y1, y2, hy)
                      +zx1 = Wedge.grade.zl(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), k2, x1, y2, hx1)
                      Equal.trans(S.MV(T, 1n+p), S.MV.grade(T, 1n+p, 1n+k2, S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2))), S.MV.mk(T, p, S.MV.grade(T, p, k2, S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1))), S.MV.grade(T, p, 1n+k2, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2)),
                          Grade.mk_s(T, p, k2, S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2)),
                          P.Mk.cong(T, p, S.MV.grade(T, p, k2, S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1))), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.grade(T, p, 1n+k2, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2),
                            Equal.trans(S.MV(T, p), S.MV.grade(T, p, k2, S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1))), S.MV.add(~T, ~add, p, S.MV.grade(T, p, k2, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2)), S.MV.grade(T, p, k2, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1))), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)),
                              Grade.add(~T, ~add, p, k2, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)),
                              A.Add.cong(~T, ~add, p, S.MV.grade(T, p, k2, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.grade(T, p, k2, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1),
                                zx1,
                                Wedge.grade(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, 0n, k2, x2, y1, hx2, hy1))),
                            Wedge.grade(~T, ~add, ~mul, ~neg, p, f, n, 0n, 1n+k2, x2, y2, hx2, hy2)))
        case 1n+j2:
          match k:
            case 0n:
              match x:
                case S.NZ{}:
                  Grade.zero(T, 1n+p, Nat.add(1n+j2, 0n))
                case S.N{+x1, +x2}:
                  match y:
                    case S.NZ{}:
                      Grade.zero(T, 1n+p, Nat.add(1n+j2, 0n))
                    case S.N{+y1, +y2}:
                      +hx1 = Mk.inv1(T, p, S.MV.grade(T, p, j2, x1), S.MV.grade(T, p, 1n+j2, x2), x1, x2, hx)
                      +hx2 = Mk.inv2(T, p, S.MV.grade(T, p, j2, x1), S.MV.grade(T, p, 1n+j2, x2), x1, x2, hx)
                      +hy1 = Mk.inv1(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, y2), y1, y2, hy)
                      +hy2 = Mk.inv2(T, p, S.MV.zero(T, p), S.MV.grade(T, p, 0n, y2), y1, y2, hy)
                      +zy1 = Wedge.grade.zr(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, Nat.add(j2, 0n), x2, y1, hy1)
                      Equal.trans(S.MV(T, 1n+p), S.MV.grade(T, 1n+p, 1n+Nat.add(j2, 0n), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2))), S.MV.mk(T, p, S.MV.grade(T, p, Nat.add(j2, 0n), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1))), S.MV.grade(T, p, 1n+Nat.add(j2, 0n), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2)),
                          Grade.mk_s(T, p, Nat.add(j2, 0n), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2)),
                          P.Mk.cong(T, p, S.MV.grade(T, p, Nat.add(j2, 0n), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1))), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.grade(T, p, 1n+Nat.add(j2, 0n), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2),
                            Equal.trans(S.MV(T, p), S.MV.grade(T, p, Nat.add(j2, 0n), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1))), S.MV.add(~T, ~add, p, S.MV.grade(T, p, Nat.add(j2, 0n), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2)), S.MV.grade(T, p, Nat.add(j2, 0n), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1))), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)),
                              Grade.add(~T, ~add, p, Nat.add(j2, 0n), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)),
                              A.Add.cong(~T, ~add, p, S.MV.grade(T, p, Nat.add(j2, 0n), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.grade(T, p, Nat.add(j2, 0n), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1),
                                Wedge.grade(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), j2, 0n, x1, y2, hx1, hy2),
                                zy1)),
                            Wedge.grade(~T, ~add, ~mul, ~neg, p, f, n, 1n+j2, 0n, x2, y2, hx2, hy2)))
            case 1n+k2:
              match x:
                case S.NZ{}:
                  Grade.zero(T, 1n+p, Nat.add(1n+j2, 1n+k2))
                case S.N{+x1, +x2}:
                  match y:
                    case S.NZ{}:
                      Grade.zero(T, 1n+p, Nat.add(1n+j2, 1n+k2))
                    case S.N{+y1, +y2}:
                      +hx1 = Mk.inv1(T, p, S.MV.grade(T, p, j2, x1), S.MV.grade(T, p, 1n+j2, x2), x1, x2, hx)
                      +hx2 = Mk.inv2(T, p, S.MV.grade(T, p, j2, x1), S.MV.grade(T, p, 1n+j2, x2), x1, x2, hx)
                      +hy1 = Mk.inv1(T, p, S.MV.grade(T, p, k2, y1), S.MV.grade(T, p, 1n+k2, y2), y1, y2, hy)
                      +hy2 = Mk.inv2(T, p, S.MV.grade(T, p, k2, y1), S.MV.grade(T, p, 1n+k2, y2), y1, y2, hy)
                      Equal.trans(S.MV(T, 1n+p), S.MV.grade(T, 1n+p, 1n+Nat.add(j2, 1n+k2), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2))), S.MV.mk(T, p, S.MV.grade(T, p, Nat.add(j2, 1n+k2), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1))), S.MV.grade(T, p, 1n+Nat.add(j2, 1n+k2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2)),
                          Grade.mk_s(T, p, Nat.add(j2, 1n+k2), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2)),
                          P.Mk.cong(T, p, S.MV.grade(T, p, Nat.add(j2, 1n+k2), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1))), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.grade(T, p, 1n+Nat.add(j2, 1n+k2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2),
                            Equal.trans(S.MV(T, p), S.MV.grade(T, p, Nat.add(j2, 1n+k2), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1))), S.MV.add(~T, ~add, p, S.MV.grade(T, p, Nat.add(j2, 1n+k2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2)), S.MV.grade(T, p, Nat.add(j2, 1n+k2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1))), S.MV.add(~T, ~add, p, S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)),
                              Grade.add(~T, ~add, p, Nat.add(j2, 1n+k2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)),
                              A.Add.cong(~T, ~add, p, S.MV.grade(T, p, Nat.add(j2, 1n+k2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2), S.MV.grade(T, p, Nat.add(j2, 1n+k2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1),
                                Wedge.grade(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), j2, 1n+k2, x1, y2, hx1, hy2),
                                Equal.trans(S.MV(T, p), S.MV.grade(T, p, Nat.add(j2, 1n+k2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.grade(T, p, 1n+Nat.add(j2, k2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1),
                                  Grade.idx(T, p, Nat.add(j2, 1n+k2), 1n+Nat.add(j2, k2), S.MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1), Nat.add_succ_r(j2, k2)),
                                  Wedge.grade(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, 1n+j2, k2, x2, y1, hx2, hy1)))),
                            Wedge.grade(~T, ~add, ~mul, ~neg, p, f, n, 1n+j2, 1n+k2, x2, y2, hx2, hy2)))
