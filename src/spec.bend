# Layer S: the multivector spec.
#
# A multivector over d generators is a Fuchs-Thery tree. The outermost level
# belongs to the first generator e: N{x1, x2} means e*x1 + x2, where x1 and x2
# hold no e. NZ{} is zero at a level, LZ{} at a leaf, so sparsity is structure
# and a product with zero vanishes by computation, not by a ring law.
#
# Every operation is generic over the scalar ring, passed as separate ~
# operations (ADR-001 item 2), and recursive on the dimension d, so every
# law below holds for every signature at once.
#
# Signs never build negated subtrees. They travel down as flags and land on
# the leaves: MV.sgn(n, f, r) multiplies grade k by (-1)^(n + f*k + r*k(k-1)/2),
# and MV.gpf(f, n, x, y) is (-1)^n * inv^f(x) * y.
#
# Products drop terms where a generator squares to zero, so they build each
# level through MV.mk, which writes N{zero, zero} as zero: every product
# returns the canonical tree (ADR-001 A3).

import Base

# The metric
# ----------

# what one generator squares to: +1, -1 or 0
type Q is Data:
  QP{}
  QN{}
  QZ{}

type Sig.End is Data:
  SigEnd{}

type Sig.Gen<-p: Nat> is Data:
  Gen{q: Q, rest: Sig(p)}

# the metric of d generators, the outermost first
def Sig(d: Nat) -> Data:
  match d:
    case 0n:
      Sig.End
    case 1n+p:
      Sig.Gen<p>

# the same number of generators, each squaring to zero
def Sig.zero(d: Nat) -> Sig(d):
  match d:
    case 0n:
      SigEnd{}
    case 1n+p:
      Gen{QZ{}, Sig.zero(p)}

# the metric of generator i (0 is the outermost); QZ past the last one
def Sig.at(d: Nat, sig: Sig(d), i: Nat) -> Q:
  match d:
    case 0n:
      QZ{}
    case 1n+p:
      match sig:
        case Gen{q, rest}:
          match i:
            case 0n:
              q
            case 1n+j:
              Sig.at(p, rest, j)

# Multivectors
# ------------

type Leaf<-T: Data> is Data:
  LZ{}
  L{x: T}

type Node<-A: Data> is Data:
  NZ{}
  N{e: A, r: A}

def MV(T: Data, d: Nat) -> Data:
  match d:
    case 0n:
      Leaf<T>
    case 1n+p:
      Node<MV(T, p)>

def MV.zero(-T: Data, d: Nat) -> MV(T, d):
  match d:
    case 0n:
      LZ{}
    case 1n+p:
      NZ{}

# the level N{e, r}, with N{zero, zero} written as zero
def MV.mk(-T: Data, d: Nat, e: MV(T, d), r: MV(T, d)) -> MV(T, 1n+d):
  match d:
    case 0n:
      match e:
        case LZ{}:
          match r:
            case LZ{}:
              NZ{}
            case L{b}:
              N{LZ{}, L{b}}
        case L{a}:
          N{L{a}, r}
    case 1n+p:
      match e:
        case NZ{}:
          match r:
            case NZ{}:
              NZ{}
            case N{r1, r2}:
              N{NZ{}, N{r1, r2}}
        case N{e1, e2}:
          N{N{e1, e2}, r}

# the scalar a
def MV.scalar(-T: Data, +d: Nat, a: T) -> MV(T, d):
  match d:
    case 0n:
      L{a}
    case 1n+p:
      N{MV.zero(T, p), MV.scalar(T, p, a)}

# a times generator i (0 is the outermost); zero past the last one
def MV.gen(-T: Data, +d: Nat, i: Nat, a: T) -> MV(T, d):
  match d:
    case 0n:
      LZ{}
    case 1n+p:
      match i:
        case 0n:
          N{MV.scalar(T, p, a), MV.zero(T, p)}
        case 1n+j:
          MV.mk(T, p, MV.zero(T, p), MV.gen(T, p, j, a))

# Ring helpers
# ------------

# (-1)^n * a
def Ring.negf(~T: Data, ~neg: T -> T, n: Bool, a: T) -> T:
  match n:
    case False{}:
      a
    case True{}:
      neg(a)

# Linear structure
# ----------------

def MV.add(~T: Data, ~add: T -> T -> T, +d: Nat, a: MV(T, d), b: MV(T, d)) -> MV(T, d):
  match d:
    case 0n:
      match a:
        case LZ{}:
          b
        case L{x}:
          match b:
            case LZ{}:
              L{x}
            case L{y}:
              L{add(x, y)}
    case 1n+p:
      match a:
        case NZ{}:
          b
        case N{a1, a2}:
          match b:
            case NZ{}:
              N{a1, a2}
            case N{b1, b2}:
              N{MV.add(~T, ~add, p, a1, b1), MV.add(~T, ~add, p, a2, b2)}

# c * x, the scalar on the left of every coefficient
def MV.scale(~T: Data, ~mul: T -> T -> T, +d: Nat, +c: T, x: MV(T, d)) -> MV(T, d):
  match d:
    case 0n:
      match x:
        case LZ{}:
          LZ{}
        case L{a}:
          L{mul(c, a)}
    case 1n+p:
      match x:
        case NZ{}:
          NZ{}
        case N{x1, x2}:
          N{MV.scale(~T, ~mul, p, c, x1), MV.scale(~T, ~mul, p, c, x2)}

# Grade signs
# -----------

# grade k times (-1)^(n + f*k + r*k(k-1)/2): (F,F,F) is the identity, n
# negates, f is the grade involution, r the reverse, f and r together the
# Clifford conjugate. The flags compose by xor: a group Z2^3.
def MV.sgn(~T: Data, ~neg: T -> T, +d: Nat, +n: Bool, +f: Bool, +r: Bool, x: MV(T, d)) -> MV(T, d):
  match d:
    case 0n:
      match x:
        case LZ{}:
          LZ{}
        case L{a}:
          L{Ring.negf(~T, ~neg, n, a)}
    case 1n+p:
      match x:
        case NZ{}:
          NZ{}
        case N{x1, x2}:
          N{MV.sgn(~T, ~neg, p, Bool.xor(n, f), Bool.xor(f, r), r, x1), MV.sgn(~T, ~neg, p, n, f, r, x2)}

def MV.neg(~T: Data, ~neg: T -> T, d: Nat, x: MV(T, d)) -> MV(T, d):
  MV.sgn(~T, ~neg, d, True{}, False{}, False{}, x)

def MV.involute(~T: Data, ~neg: T -> T, d: Nat, x: MV(T, d)) -> MV(T, d):
  MV.sgn(~T, ~neg, d, False{}, True{}, False{}, x)

def MV.reverse(~T: Data, ~neg: T -> T, d: Nat, x: MV(T, d)) -> MV(T, d):
  MV.sgn(~T, ~neg, d, False{}, False{}, True{}, x)

def MV.conjugate(~T: Data, ~neg: T -> T, d: Nat, x: MV(T, d)) -> MV(T, d):
  MV.sgn(~T, ~neg, d, False{}, True{}, True{}, x)

# Products
# --------

# (-1)^n * inv^f(x) * y. For x = e*x1 + x2 and y = e*y1 + y2, moving e
# across the involuted part and squaring it to q gives
#   e*((-1)^(n+f) inv^f(x1) y2 + (-1)^n inv^(not f)(x2) y1)
#     + ((-1)^(n+f) q inv^(not f)(x1) y1 + (-1)^n inv^f(x2) y2)
# The metric comes last, so a zero operand gives zero before it is read.
def MV.gpf(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +d: Nat, +f: Bool, +n: Bool, x: MV(T, d), y: MV(T, d), sig: Sig(d)) -> MV(T, d):
  match d:
    case 0n:
      match x:
        case LZ{}:
          LZ{}
        case L{a}:
          match y:
            case LZ{}:
              LZ{}
            case L{b}:
              L{Ring.negf(~T, ~neg, n, mul(a, b))}
    case 1n+p:
      match x:
        case NZ{}:
          NZ{}
        case N{+x1, +x2}:
          match y:
            case NZ{}:
              NZ{}
            case N{+y1, +y2}:
              match sig:
                case Gen{q, +rest}:
                  match q:
                    case QZ{}:
                      MV.mk(T, p,
                        MV.add(~T, ~add, p,
                          MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2, rest),
                          MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1, rest)),
                        MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, y2, rest))
                    case QP{}:
                      MV.mk(T, p,
                        MV.add(~T, ~add, p,
                          MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2, rest),
                          MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1, rest)),
                        MV.add(~T, ~add, p,
                          MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), x1, y1, rest),
                          MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, y2, rest)))
                    case QN{}:
                      MV.mk(T, p,
                        MV.add(~T, ~add, p,
                          MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2, rest),
                          MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1, rest)),
                        MV.add(~T, ~add, p,
                          MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, y1, rest),
                          MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, y2, rest)))

def MV.gp(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  d: Nat, sig: Sig(d), x: MV(T, d), y: MV(T, d)) -> MV(T, d):
  MV.gpf(~T, ~add, ~mul, ~neg, d, False{}, False{}, x, y, sig)

# the sandwich m x ~m: x moved by the versor m (gax's transform)
def MV.transform(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +d: Nat, +sig: Sig(d), +m: MV(T, d), x: MV(T, d)) -> MV(T, d):
  MV.gp(~T, ~add, ~mul, ~neg, d, sig, MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), MV.reverse(~T, ~neg, d, m))

# the outer product, (-1)^n * inv^f(x) ^ y: the QZ case of MV.gpf, written
# without a metric (the law wedge_is_gp_zero ties the two)
def MV.wedgef(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +d: Nat, +f: Bool, +n: Bool, x: MV(T, d), y: MV(T, d)) -> MV(T, d):
  match d:
    case 0n:
      match x:
        case LZ{}:
          LZ{}
        case L{a}:
          match y:
            case LZ{}:
              LZ{}
            case L{b}:
              L{Ring.negf(~T, ~neg, n, mul(a, b))}
    case 1n+p:
      match x:
        case NZ{}:
          NZ{}
        case N{x1, +x2}:
          match y:
            case NZ{}:
              NZ{}
            case N{y1, +y2}:
              MV.mk(T, p,
                MV.add(~T, ~add, p,
                  MV.wedgef(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2),
                  MV.wedgef(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1)),
                MV.wedgef(~T, ~add, ~mul, ~neg, p, f, n, x2, y2))

def MV.wedge(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  d: Nat, x: MV(T, d), y: MV(T, d)) -> MV(T, d):
  MV.wedgef(~T, ~add, ~mul, ~neg, d, False{}, False{}, x, y)

# Complements
# -----------

# (-1)^n * J_R(inv^f(x)), where J_R is the right complement, metric-free:
# a ^ J_R(a) is the pseudoscalar for every basis blade a, so
# J_R(e*x1 + x2) = e*J_R(inv(x2)) + J_R(x1)
def MV.rcf(~T: Data, ~neg: T -> T, +d: Nat, +n: Bool, +f: Bool, x: MV(T, d)) -> MV(T, d):
  match d:
    case 0n:
      match x:
        case LZ{}:
          LZ{}
        case L{a}:
          L{Ring.negf(~T, ~neg, n, a)}
    case 1n+p:
      match x:
        case NZ{}:
          NZ{}
        case N{x1, x2}:
          N{MV.rcf(~T, ~neg, p, n, Bool.not(f), x2), MV.rcf(~T, ~neg, p, Bool.xor(n, f), f, x1)}

# (-1)^n * inv^f(J_L(x)), where J_L is the left complement: J_L(a) ^ a is the
# pseudoscalar for every basis blade a, so J_L(e*x1 + x2) = e*J_L(x2) + inv(J_L(x1))
def MV.lcf(~T: Data, ~neg: T -> T, +d: Nat, +n: Bool, +f: Bool, x: MV(T, d)) -> MV(T, d):
  match d:
    case 0n:
      match x:
        case LZ{}:
          LZ{}
        case L{a}:
          L{Ring.negf(~T, ~neg, n, a)}
    case 1n+p:
      match x:
        case NZ{}:
          NZ{}
        case N{x1, x2}:
          N{MV.lcf(~T, ~neg, p, Bool.xor(n, f), f, x2), MV.lcf(~T, ~neg, p, n, Bool.not(f), x1)}

def MV.rcomp(~T: Data, ~neg: T -> T, d: Nat, x: MV(T, d)) -> MV(T, d):
  MV.rcf(~T, ~neg, d, False{}, False{}, x)

def MV.lcomp(~T: Data, ~neg: T -> T, d: Nat, x: MV(T, d)) -> MV(T, d):
  MV.lcf(~T, ~neg, d, False{}, False{}, x)

# the regressive product, metric-free: J_L(J_R(x) ^ J_R(y))
def MV.vee(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +d: Nat, x: MV(T, d), y: MV(T, d)) -> MV(T, d):
  MV.lcomp(~T, ~neg, d, MV.wedge(~T, ~add, ~mul, ~neg, d, MV.rcomp(~T, ~neg, d, x), MV.rcomp(~T, ~neg, d, y)))

# Grades
# ------

# the grade-k part
def MV.grade(-T: Data, +d: Nat, +k: Nat, x: MV(T, d)) -> MV(T, d):
  match d:
    case 0n:
      match k:
        case 0n:
          x
        case 1n+j:
          LZ{}
    case 1n+p:
      match k:
        case 0n:
          match x:
            case NZ{}:
              NZ{}
            case N{x1, x2}:
              MV.mk(T, p, MV.zero(T, p), MV.grade(T, p, 0n, x2))
        case 1n+j:
          match x:
            case NZ{}:
              NZ{}
            case N{x1, x2}:
              MV.mk(T, p, MV.grade(T, p, j, x1), MV.grade(T, p, 1n+j, x2))

# x is a k-vector: its grade-k part is all of it
def MV.Homog(-T: Data, d: Nat, k: Nat, x: MV(T, d)) -> Data:
  {MV.grade(T, d, k, x) == x : MV(T, d)}

# Inner products
# --------------
# On a pair of blades of grades r and s, gax's inner products each keep one
# grade of the geometric product: the left contraction grade s - r when
# r <= s, the right contraction grade r - s when s <= r, the symmetric
# ("fat") dot grade |r - s|, and the scalar product grade 0. By bilinearity
# each is a sum over pairs of grade parts, which is how they are written
# here. The mirror kernels print only the terms that survive.

# grade j of (grade a of x) (grade b of y)
def MV.gpg(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +d: Nat, +sig: Sig(d), a: Nat, b: Nat, j: Nat, +x: MV(T, d), +y: MV(T, d)) -> MV(T, d):
  MV.grade(T, d, j, MV.gp(~T, ~add, ~mul, ~neg, d, sig, MV.grade(T, d, a, x), MV.grade(T, d, b, y)))

# the pair (r, r + j) when left, else (r + j, r), kept at grade j
def MV.gpg.side(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +d: Nat, +sig: Sig(d), left: Bool, +r: Nat, +j: Nat, +x: MV(T, d), +y: MV(T, d)) -> MV(T, d):
  match left:
    case True{}:
      MV.gpg(~T, ~add, ~mul, ~neg, d, sig, r, Nat.add(r, j), j, x, y)
    case False{}:
      MV.gpg(~T, ~add, ~mul, ~neg, d, sig, Nat.add(r, j), r, j, x, y)

# the sum over j = 1 .. n of the side terms
def MV.inner.row(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +d: Nat, +sig: Sig(d), +left: Bool, +r: Nat, +n: Nat, +x: MV(T, d), +y: MV(T, d)) -> MV(T, d):
  match n:
    case 0n:
      MV.zero(T, d)
    case 1n+m:
      MV.add(~T, ~add, d, MV.gpg.side(~T, ~add, ~mul, ~neg, d, sig, left, r, 1n+m, x, y),
        MV.inner.row(~T, ~add, ~mul, ~neg, d, sig, left, r, m, x, y))

type Inner is Data:
  ILc{}
  IRc{}
  IDot{}

# the off-diagonal terms of grade r on the left (r, r + j) or right side
def MV.inner.off(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  op: Inner, +d: Nat, +sig: Sig(d), +r: Nat, +x: MV(T, d), +y: MV(T, d)) -> MV(T, d):
  match op:
    case ILc{}:
      MV.inner.row(~T, ~add, ~mul, ~neg, d, sig, True{}, r, Nat.sub(d, r), x, y)
    case IRc{}:
      MV.inner.row(~T, ~add, ~mul, ~neg, d, sig, False{}, r, Nat.sub(d, r), x, y)
    case IDot{}:
      MV.add(~T, ~add, d, MV.inner.row(~T, ~add, ~mul, ~neg, d, sig, True{}, r, Nat.sub(d, r), x, y),
        MV.inner.row(~T, ~add, ~mul, ~neg, d, sig, False{}, r, Nat.sub(d, r), x, y))

# the sum over r = 0 .. n of the diagonal term (r, r) at grade 0 and the
# off-diagonal terms
def MV.inner.go(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +op: Inner, +d: Nat, +sig: Sig(d), +n: Nat, +x: MV(T, d), +y: MV(T, d)) -> MV(T, d):
  match n:
    case 0n:
      MV.add(~T, ~add, d, MV.gpg(~T, ~add, ~mul, ~neg, d, sig, 0n, 0n, 0n, x, y),
        MV.inner.off(~T, ~add, ~mul, ~neg, op, d, sig, 0n, x, y))
    case 1n+m:
      MV.add(~T, ~add, d,
        MV.add(~T, ~add, d, MV.gpg(~T, ~add, ~mul, ~neg, d, sig, 1n+m, 1n+m, 0n, x, y),
          MV.inner.off(~T, ~add, ~mul, ~neg, op, d, sig, 1n+m, x, y)),
        MV.inner.go(~T, ~add, ~mul, ~neg, op, d, sig, m, x, y))

def MV.inner(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +op: Inner, +d: Nat, +sig: Sig(d), +x: MV(T, d), +y: MV(T, d)) -> MV(T, d):
  MV.inner.go(~T, ~add, ~mul, ~neg, op, d, sig, d, x, y)

# the left contraction x ⌋ y
def MV.lc(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +d: Nat, +sig: Sig(d), +x: MV(T, d), +y: MV(T, d)) -> MV(T, d):
  MV.inner(~T, ~add, ~mul, ~neg, ILc{}, d, sig, x, y)

# the right contraction x ⌊ y
def MV.rc(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +d: Nat, +sig: Sig(d), +x: MV(T, d), +y: MV(T, d)) -> MV(T, d):
  MV.inner(~T, ~add, ~mul, ~neg, IRc{}, d, sig, x, y)

# the symmetric inner product x | y
def MV.dot(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +d: Nat, +sig: Sig(d), +x: MV(T, d), +y: MV(T, d)) -> MV(T, d):
  MV.inner(~T, ~add, ~mul, ~neg, IDot{}, d, sig, x, y)

# twice the commutator, xy - yx, and twice the anticommutator, xy + yx.
# gax's commutator and anticommutator are the halves; their kernels have
# integer coefficients and are proven equal to these by doubling, so no
# ring here needs 1/2.
def MV.commutator2(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +d: Nat, +sig: Sig(d), +x: MV(T, d), +y: MV(T, d)) -> MV(T, d):
  MV.add(~T, ~add, d, MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y), MV.neg(~T, ~neg, d, MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, x)))

def MV.anticommutator2(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +d: Nat, +sig: Sig(d), +x: MV(T, d), +y: MV(T, d)) -> MV(T, d):
  MV.add(~T, ~add, d, MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y), MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, x))

# the scalar product <x y>_0
def MV.scalar_product(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,
  +d: Nat, +sig: Sig(d), x: MV(T, d), y: MV(T, d)) -> MV(T, d):
  MV.grade(T, d, 0n, MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y))

# The metric as multivectors
# --------------------------

# the scalar q, with q one of +1, -1, 0 given a ring's one
def MV.of_q(~T: Data, ~neg: T -> T, d: Nat, q: Q, one: T) -> MV(T, d):
  match q:
    case QP{}:
      MV.scalar(T, d, one)
    case QN{}:
      MV.scalar(T, d, neg(one))
    case QZ{}:
      MV.zero(T, d)

# what generator i squares to, as a multivector
def MV.metric(~T: Data, ~neg: T -> T, +d: Nat, sig: Sig(d), i: Nat, one: T) -> MV(T, d):
  MV.of_q(~T, ~neg, d, Sig.at(d, sig, i), one)

# Blades by path
# --------------
# A basis blade is a path: one Bool per generator, outermost first, True
# where the blade holds the generator (the e-part of that level).

# x times the blade at path (a missing step is False)
def MV.blade(-T: Data, +d: Nat, path: List<&2, Bool>, x: T) -> MV(T, d):
  match d:
    case 0n:
      L{x}
    case 1n+p:
      match path:
        case Nil{}:
          N{MV.zero(T, p), MV.blade(T, p, Nil{}, x)}
        case Con{b, rest}:
          match b:
            case True{}:
              N{MV.blade(T, p, rest, x), MV.zero(T, p)}
            case False{}:
              N{MV.zero(T, p), MV.blade(T, p, rest, x)}

# (-1)^s times the coefficient at path, zero where the tree has none
def MV.at(~T: Data, ~zero: T, ~neg: T -> T, +d: Nat, path: List<&2, Bool>, s: Bool, x: MV(T, d)) -> T:
  match d:
    case 0n:
      match x:
        case LZ{}:
          zero
        case L{a}:
          Ring.negf(~T, ~neg, s, a)
    case 1n+p:
      match path:
        case Nil{}:
          match x:
            case NZ{}:
              zero
            case N{e, r}:
              MV.at(~T, ~zero, ~neg, p, Nil{}, s, r)
        case Con{b, rest}:
          match b:
            case True{}:
              match x:
                case NZ{}:
                  zero
                case N{e, r}:
                  MV.at(~T, ~zero, ~neg, p, rest, s, e)
            case False{}:
              match x:
                case NZ{}:
                  zero
                case N{e, r}:
                  MV.at(~T, ~zero, ~neg, p, rest, s, r)

# x with the coefficient at path removed
def MV.clear(-T: Data, +d: Nat, path: List<&2, Bool>, x: MV(T, d)) -> MV(T, d):
  match d:
    case 0n:
      LZ{}
    case 1n+p:
      match path:
        case Nil{}:
          match x:
            case NZ{}:
              NZ{}
            case N{e, r}:
              MV.mk(T, p, e, MV.clear(T, p, Nil{}, r))
        case Con{b, rest}:
          match b:
            case True{}:
              match x:
                case NZ{}:
                  NZ{}
                case N{e, r}:
                  MV.mk(T, p, MV.clear(T, p, rest, e), r)
            case False{}:
              match x:
                case NZ{}:
                  NZ{}
                case N{e, r}:
                  MV.mk(T, p, e, MV.clear(T, p, rest, r))
