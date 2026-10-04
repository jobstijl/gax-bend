# Q4b: an exact symbolic ring for the checker: polynomials over a user Int.
# A Poly is a list of terms sorted by monomial, equal monomials merged, no
# zero coefficient, so two equal polynomials are the same term and {==}
# decides equality. Every operation renormalises: sort, then merge.
import Base

# Int: IPos{n} = n, INeg{n} = -(n+1); one spelling per integer.
type Int is Data:
  IPos{n: Nat}
  INeg{n: Nat}

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

# a monomial is a sorted list of variable indices (with multiplicity)
def Cmp.then(a: Cmp, b: Cmp) -> Cmp:
  match a:
    case LT{}:
      LT{}
    case EQ{}:
      b
    case GT{}:
      GT{}

def Mono.cmp(a: List<&2, Nat>, b: List<&2, Nat>) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} y <> yt:
      LT{}
    case x <> xt Nil{}:
      GT{}
    case x <> xt y <> yt:
      Cmp.then(Nat.cmp(x, y), Mono.cmp(xt, yt))

def Mono.mul(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  List.sort(~Nat, ~Nat.is_le, List.append(&2, Nat, a, b))

type Tm is Data:
  Tm{c: Int, m: List<&2, Nat>}

def Tm.le(a: Tm, b: Tm) -> Bool:
  match a b:
    case Tm{ac, am} Tm{bc, bm}:
      Cmp.is_le(Mono.cmp(am, bm))

def Poly() -> Data:
  List<&2, Tm>

# merge loop state: the open term (coefficient, monomial) and the output so far
type St is Data:
  St{c: Int, m: List<&2, Nat>, acc: List<&2, Tm>}

def Poly.flush(c: Int, m: List<&2, Nat>, acc: Poly(), z: Bool) -> Poly():
  match z:
    case True{}:
      acc
    case False{}:
      Tm{c, m} <> acc

def Poly.step.if(c: Int, +m: List<&2, Nat>, acc: Poly(), tc: Int, tm: List<&2, Nat>, same: Bool) -> St:
  match same:
    case True{}:
      St{Int.add(c, tc), m, acc}
    case False{}:
      +c2 = c
      St{tc, tm, Poly.flush(c2, m, acc, Int.is_zero(c2))}

def Poly.step(st: St, t: Tm) -> St:
  match st t:
    case St{c, +m, acc} Tm{tc, +tm}:
      Poly.step.if(c, m, acc, tc, tm, Cmp.is_eq(Mono.cmp(m, tm)))

def Poly.merge(ts: Poly(), st: St) -> Poly():
  match ts:
    case Nil{}:
      match st:
        case St{+c, m, acc}:
          List.reverse(&2, Tm, Poly.flush(c, m, acc, Int.is_zero(c)))
    case t <> rest:
      Poly.merge(rest, Poly.step(st, t))

def Poly.norm.go(ts: Poly()) -> Poly():
  match ts:
    case Nil{}:
      Nil{}
    case Tm{c, m} <> rest:
      Poly.merge(rest, St{c, m, Nil{}})

def Poly.norm(ts: Poly()) -> Poly():
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      Poly.norm.go(List.sort(~Tm, ~Tm.le, t <> rest))

def Poly.var(i: Nat) -> Poly():
  [Tm{IPos{1n}, [i]}]

def Poly.add(p: Poly(), q: Poly()) -> Poly():
  Poly.norm(List.append(&2, Tm, p, q))

def Poly.neg(p: Poly()) -> Poly():
  match p:
    case Nil{}:
      Nil{}
    case Tm{c, m} <> rest:
      Tm{Int.neg(c), m} <> Poly.neg(rest)

def Poly.scale(+c: Int, +m: List<&2, Nat>, q: Poly()) -> Poly():
  match q:
    case Nil{}:
      Nil{}
    case Tm{qc, qm} <> rest:
      Tm{Int.mul(c, qc), Mono.mul(m, qm)} <> Poly.scale(c, m, rest)

def Poly.cross(p: Poly(), +q: Poly()) -> Poly():
  match p:
    case Nil{}:
      Nil{}
    case Tm{c, m} <> rest:
      List.append(&2, Tm, Poly.scale(c, m, q), Poly.cross(rest, q))

def Poly.mul(p: Poly(), q: Poly()) -> Poly():
  Poly.norm(Poly.cross(p, q))

