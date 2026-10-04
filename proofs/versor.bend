# Versors act as homomorphisms. For m with ~m m the scalar n,
#   (m x ~m)(m y ~m) = n (m (x y) ~m),
# in every dimension and signature: m x (~m m) y ~m by associativity, then
# n times a product, since a product is a canonical tree (ADR-001 A3).
# Sandwiches also compose: m1 (m2 x ~m2) ~m1 = (m1 m2) x ~(m1 m2).

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S
import ./base.bend as B
import ./add.bend as A
import ./gp.bend as P
import ./gp_assoc.bend as PA
import ./scale.bend as SC
import ./rev.bend as RV

# Canonical trees
# ---------------
# A tree is canonical when no level is N{zero, zero}. MV.mk builds levels
# so that products are canonical (A3), and with a canonical operand the
# scalar n acts by scaling.

def MV.is_zero(-T: Data, d: Nat, x: S.MV(T, d)) -> Bool:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          True{}
        case S.L{a}:
          False{}
    case 1n+p:
      match x:
        case S.NZ{}:
          True{}
        case S.N{a, b}:
          False{}

def MV.Canon(-T: Data, d: Nat, x: S.MV(T, d)) -> Type:
  match d:
    case 0n:
      Unit
    case 1n+p:
      match x:
        case S.NZ{}:
          Unit
        case S.N{a, b}:
          MV.Canon(T, p, a) & MV.Canon(T, p, b) & {Bool.and(MV.is_zero(T, p, a), MV.is_zero(T, p, b)) == False{} : Bool}

def Bool.and_f(q: Bool) -> {Bool.and(q, False{}) == False{} : Bool}:
  match q:
    case False{}:
      {==}
    case True{}:
      {==}

def Bool.and4(p: Bool, q: Bool, r: Bool, -s: Bool, h: {Bool.and(p, r) == False{} : Bool})
  -> {Bool.and(Bool.and(p, q), Bool.and(r, s)) == False{} : Bool}:
  match p r:
    case False{} r2:
      {==}
    case True{} False{}:
      Bool.and_f(q)
    case True{} True{}:
      B.Bool.tf({Bool.and(q, s) == False{} : Bool}, h)

def Add.is_zero(~T: Data, ~add: T -> T -> T, +d: Nat, a: S.MV(T, d), b: S.MV(T, d))
  -> {MV.is_zero(T, d, S.MV.add(~T, ~add, d, a, b)) == Bool.and(MV.is_zero(T, d, a), MV.is_zero(T, d, b)) : Bool}:
  match d:
    case 0n:
      match a b:
        case S.LZ{} b2:
          {==}
        case S.L{x} S.LZ{}:
          {==}
        case S.L{x} S.L{y}:
          {==}
    case 1n+p:
      match a b:
        case S.NZ{} b2:
          {==}
        case S.N{a1, a2} S.NZ{}:
          {==}
        case S.N{a1, a2} S.N{b1, b2}:
          {==}

# the sum of canonical trees is canonical: leaves never cancel structurally
def Add.canon(~T: Data, ~add: T -> T -> T, +d: Nat, a: S.MV(T, d), b: S.MV(T, d), ca: MV.Canon(T, d, a), cb: MV.Canon(T, d, b))
  -> MV.Canon(T, d, S.MV.add(~T, ~add, d, a, b)):
  match d:
    case 0n:
      Unit{}
    case 1n+p:
      match a b:
        case S.NZ{} b2:
          cb
        case S.N{a1, a2} S.NZ{}:
          ca
        case S.N{+a1, +a2} S.N{+b1, +b2}:
          match ca:
            case (ca1, ra):
              match ra:
                case (ca2, za):
                  match cb:
                    case (cb1, rb):
                      match rb:
                        case (cb2, zb):
                          (Add.canon(                ~T, ~add, p, a1, b1, ca1, cb1), (Add.canon(~T, ~add, p, a2, b2, ca2, cb2),
                                    Equal.trans(Bool, Bool.and(MV.is_zero(T, p, S.MV.add(~T, ~add, p, a1, b1)), MV.is_zero(T, p, S.MV.add(~T, ~add, p, a2, b2))),
                                  Bool.and(Bool.and(MV.is_zero(T, p, a1), MV.is_zero(T, p, b1)), Bool.and(MV.is_zero(T, p, a2), MV.is_zero(T, p, b2))), False{},
                                  B.Eq.cong2(Bool, Bool, Bool, x => y => Bool.and(x, y), MV.is_zero(T, p, S.MV.add(~T, ~add, p, a1, b1)), Bool.and(MV.is_zero(T, p, a1), MV.is_zero(T, p, b1)),
                                    MV.is_zero(T, p, S.MV.add(~T, ~add, p, a2, b2)), Bool.and(MV.is_zero(T, p, a2), MV.is_zero(T, p, b2)), Add.is_zero(~T, ~add, p, a1, b1), Add.is_zero(~T, ~add, p, a2, b2)),
                                  Bool.and4(MV.is_zero(T, p, a1), MV.is_zero(T, p, b1), MV.is_zero(T, p, a2), MV.is_zero(T, p, b2), za))))

# MV.mk of canonical trees is canonical
def Mk.canon(-T: Data, +d: Nat, e: S.MV(T, d), r: S.MV(T, d), ce: MV.Canon(T, d, e), cr: MV.Canon(T, d, r)) -> MV.Canon(T, 1n+d, S.MV.mk(T, d, e, r)):
  match d:
    case 0n:
      match e:
        case S.LZ{}:
          match r:
            case S.LZ{}:
              Unit{}
            case S.L{b}:
              (Unit{}, (Unit{}, {==}))
        case S.L{a}:
          (Unit{}, (cr, {==}))
    case 1n+p:
      match e:
        case S.NZ{}:
          match r:
            case S.NZ{}:
              Unit{}
            case S.N{r1, r2}:
              (Unit{}, (cr, {==}))
        case S.N{e1, e2}:
          (ce, (cr, {==}))


# every geometric product is canonical, whatever its operands
def Gpf.canon(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, +d: Nat, +f: Bool, +n: Bool, x: S.MV(T, d), y: S.MV(T, d), sig: S.Sig(d)) -> MV.Canon(T, d, S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, y, sig)):
  match d:
    case 0n:
      Unit{}
    case 1n+p:
      match x:
        case S.NZ{}:
          Unit{}
        case S.N{+x1, +x2}:
          match y:
            case S.NZ{}:
              Unit{}
            case S.N{+y1, +y2}:
              match sig:
                case S.Gen{q, +rest}:
                  match q:
                    case S.QZ{}:
                      Mk.canon(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, y2, rest),
                        Add.canon(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1, rest), Gpf.canon(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2, rest), Gpf.canon(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1, rest)),
                        Gpf.canon(~T, ~add, ~mul, ~neg, p, f, n, x2, y2, rest))
                    case S.QP{}:
                      Mk.canon(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), x1, y1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, y2, rest)),
                        Add.canon(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1, rest), Gpf.canon(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2, rest), Gpf.canon(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1, rest)),
                        Add.canon(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), x1, y1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, y2, rest), Gpf.canon(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), x1, y1, rest), Gpf.canon(~T, ~add, ~mul, ~neg, p, f, n, x2, y2, rest)))
                    case S.QN{}:
                      Mk.canon(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, y1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, y2, rest)),
                        Add.canon(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1, rest), Gpf.canon(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, y2, rest), Gpf.canon(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, y1, rest)),
                        Add.canon(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, y1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, y2, rest), Gpf.canon(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, y1, rest), Gpf.canon(~T, ~add, ~mul, ~neg, p, f, n, x2, y2, rest)))

def Scale.is_zero(~T: Data, ~mul: T -> T -> T, +d: Nat, +c: T, w: S.MV(T, d)) -> {MV.is_zero(T, d, S.MV.scale(~T, ~mul, d, c, w)) == MV.is_zero(T, d, w) : Bool}:
  match d:
    case 0n:
      match w:
        case S.LZ{}:
          {==}
        case S.L{b}:
          {==}
    case 1n+p:
      match w:
        case S.NZ{}:
          {==}
        case S.N{w1, w2}:
          {==}

# MV.mk is N when its parts are not both zero
def Mk.open(-T: Data, +d: Nat, a: S.MV(T, d), b: S.MV(T, d), h: {Bool.and(MV.is_zero(T, d, a), MV.is_zero(T, d, b)) == False{} : Bool})
  -> {S.MV.mk(T, d, a, b) == S.N{a, b} : S.MV(T, 1n+d)}:
  match d:
    case 0n:
      match a:
        case S.LZ{}:
          match b:
            case S.LZ{}:
              B.Bool.tf({S.NZ{} == S.N{S.LZ{}, S.LZ{}} : S.MV(T, 1n)}, h)
            case S.L{y}:
              {==}
        case S.L{x}:
          {==}
    case 1n+p:
      match a:
        case S.NZ{}:
          match b:
            case S.NZ{}:
              B.Bool.tf({S.NZ{} == S.N{S.NZ{}, S.NZ{}} : S.MV(T, 2n+p)}, h)
            case S.N{b1, b2}:
              {==}
        case S.N{a1, a2}:
          {==}

def Gp.negf_mul(~T: Data, ~mul: T -> T -> T, ~neg: T -> T, ~neg_mul_l: R.Ring.NegMulL(T, mul, neg), n: Bool, +c: T, +b: T)
  -> {S.Ring.negf(~T, ~neg, n, mul(c, b)) == mul(S.Ring.negf(~T, ~neg, n, c), b) : T}:
  match n:
    case False{}:
      {==}
    case True{}:
      Equal.sym(T, mul(neg(c), b), neg(mul(c, b)), neg_mul_l(c, b))

# the scalar c acts on a canonical tree by scaling: (-1)^n c w = scale
def Gp.scalar(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~neg_mul_l: R.Ring.NegMulL(T, mul, neg), +d: Nat, +f: Bool, +n: Bool, +c: T, w: S.MV(T, d), cw: MV.Canon(T, d, w), sig: S.Sig(d))
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, S.MV.scalar(T, d, c), w, sig) == S.MV.scale(~T, ~mul, d, S.Ring.negf(~T, ~neg, n, c), w) : S.MV(T, d)}:
  match d:
    case 0n:
      match w:
        case S.LZ{}:
          {==}
        case S.L{+b}:
          B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, mul(c, b)), mul(S.Ring.negf(~T, ~neg, n, c), b), Gp.negf_mul(~T, ~mul, ~neg, ~neg_mul_l, n, c, b))
    case 1n+p:
      match w:
        case S.NZ{}:
          {==}
        case S.N{+w1, +w2}:
          match cw:
            case (c1, rc):
              match rc:
                case (c2, nz):
                  match sig:
                    case S.Gen{q, +rest}:
                      match q:
                        case S.QZ{}:
                          Equal.trans(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.zero(T, p), w2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.MV.mk(T, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.N{S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)},
                            B.Eq.cong2(S.MV(T, p), S.MV(T, p), S.MV(T, 1n+p), u => v => S.MV.mk(T, p, u, v), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.zero(T, p), w2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest),
                              Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.zero(T, p), w2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.add(~T, ~add, p, S.MV.zero(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest),
                                Equal.cong(S.MV(T, p), S.MV(T, p), u => S.MV.add(~T, ~add, p, u, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.zero(T, p), w2, rest), S.MV.zero(T, p), P.Gp.zero_l(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), w2, rest)),
                                A.Add.zero_l(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest))),
                              {==}),
                            Equal.trans(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.MV.mk(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)), S.N{S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)},
                              B.Eq.cong2(S.MV(T, p), S.MV(T, p), S.MV(T, 1n+p), u => v => S.MV.mk(T, p, u, v), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2), Gp.scalar(~T, ~add, ~mul, ~neg, ~neg_mul_l, p, Bool.not(f), n, c, w1, c1, rest), Gp.scalar(~T, ~add, ~mul, ~neg, ~neg_mul_l, p, f, n, c, w2, c2, rest)),
                              Mk.open(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2),
                                Equal.trans(Bool, Bool.and(MV.is_zero(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1)), MV.is_zero(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2))), Bool.and(MV.is_zero(T, p, w1), MV.is_zero(T, p, w2)), False{},
                                  B.Eq.cong2(Bool, Bool, Bool, u => v => Bool.and(u, v), MV.is_zero(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1)), MV.is_zero(T, p, w1), MV.is_zero(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)), MV.is_zero(T, p, w2),
                                    Scale.is_zero(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), Scale.is_zero(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)),
                                  nz))))
                        case S.QP{}:
                          Equal.trans(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.zero(T, p), w2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), S.MV.zero(T, p), w1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest))), S.MV.mk(T, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.N{S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)},
                            B.Eq.cong2(S.MV(T, p), S.MV(T, p), S.MV(T, 1n+p), u => v => S.MV.mk(T, p, u, v), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.zero(T, p), w2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), S.MV.zero(T, p), w1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest),
                              Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.zero(T, p), w2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.add(~T, ~add, p, S.MV.zero(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest),
                                Equal.cong(S.MV(T, p), S.MV(T, p), u => S.MV.add(~T, ~add, p, u, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.zero(T, p), w2, rest), S.MV.zero(T, p), P.Gp.zero_l(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), w2, rest)),
                                A.Add.zero_l(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest))),
                              Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), S.MV.zero(T, p), w1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.MV.add(~T, ~add, p, S.MV.zero(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest),
                                Equal.cong(S.MV(T, p), S.MV(T, p), u => S.MV.add(~T, ~add, p, u, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), S.MV.zero(T, p), w1, rest), S.MV.zero(T, p), P.Gp.zero_l(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), w1, rest)),
                                A.Add.zero_l(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)))),
                            Equal.trans(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.MV.mk(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)), S.N{S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)},
                              B.Eq.cong2(S.MV(T, p), S.MV(T, p), S.MV(T, 1n+p), u => v => S.MV.mk(T, p, u, v), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2), Gp.scalar(~T, ~add, ~mul, ~neg, ~neg_mul_l, p, Bool.not(f), n, c, w1, c1, rest), Gp.scalar(~T, ~add, ~mul, ~neg, ~neg_mul_l, p, f, n, c, w2, c2, rest)),
                              Mk.open(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2),
                                Equal.trans(Bool, Bool.and(MV.is_zero(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1)), MV.is_zero(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2))), Bool.and(MV.is_zero(T, p, w1), MV.is_zero(T, p, w2)), False{},
                                  B.Eq.cong2(Bool, Bool, Bool, u => v => Bool.and(u, v), MV.is_zero(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1)), MV.is_zero(T, p, w1), MV.is_zero(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)), MV.is_zero(T, p, w2),
                                    Scale.is_zero(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), Scale.is_zero(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)),
                                  nz))))
                        case S.QN{}:
                          Equal.trans(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.zero(T, p), w2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), S.MV.zero(T, p), w1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest))), S.MV.mk(T, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.N{S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)},
                            B.Eq.cong2(S.MV(T, p), S.MV(T, p), S.MV(T, 1n+p), u => v => S.MV.mk(T, p, u, v), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.zero(T, p), w2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), S.MV.zero(T, p), w1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest),
                              Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.zero(T, p), w2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.add(~T, ~add, p, S.MV.zero(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest),
                                Equal.cong(S.MV(T, p), S.MV(T, p), u => S.MV.add(~T, ~add, p, u, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.zero(T, p), w2, rest), S.MV.zero(T, p), P.Gp.zero_l(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), w2, rest)),
                                A.Add.zero_l(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest))),
                              Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), S.MV.zero(T, p), w1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.MV.add(~T, ~add, p, S.MV.zero(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest),
                                Equal.cong(S.MV(T, p), S.MV(T, p), u => S.MV.add(~T, ~add, p, u, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), S.MV.zero(T, p), w1, rest), S.MV.zero(T, p), P.Gp.zero_l(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), w1, rest)),
                                A.Add.zero_l(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)))),
                            Equal.trans(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest)), S.MV.mk(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)), S.N{S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)},
                              B.Eq.cong2(S.MV(T, p), S.MV(T, p), S.MV(T, 1n+p), u => v => S.MV.mk(T, p, u, v), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.scalar(T, p, c), w1, rest), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.scalar(T, p, c), w2, rest), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2), Gp.scalar(~T, ~add, ~mul, ~neg, ~neg_mul_l, p, Bool.not(f), n, c, w1, c1, rest), Gp.scalar(~T, ~add, ~mul, ~neg, ~neg_mul_l, p, f, n, c, w2, c2, rest)),
                              Mk.open(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2),
                                Equal.trans(Bool, Bool.and(MV.is_zero(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1)), MV.is_zero(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2))), Bool.and(MV.is_zero(T, p, w1), MV.is_zero(T, p, w2)), False{},
                                  B.Eq.cong2(Bool, Bool, Bool, u => v => Bool.and(u, v), MV.is_zero(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1)), MV.is_zero(T, p, w1), MV.is_zero(T, p, S.MV.scale(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)), MV.is_zero(T, p, w2),
                                    Scale.is_zero(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w1), Scale.is_zero(~T, ~mul, p, S.Ring.negf(~T, ~neg, n, c), w2)),
                                  nz))))


# Versor laws
# -----------

# for ~m m = nn: (m x ~m)(m y ~m) = nn (m (x y) ~m)
def Versor.gp(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~add_assoc: R.Ring.Assoc(T, add), ~add_comm: R.Ring.Comm(T, add), ~mul_assoc: R.Ring.Assoc(T, mul), ~mul_comm: R.Ring.Comm(T, mul),
  ~dist_l: R.Ring.DistL(T, add, mul), ~dist_r: R.Ring.DistR(T, add, mul), ~neg_add: R.Ring.NegAdd(T, add, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  ~neg_mul_l: R.Ring.NegMulL(T, mul, neg), ~neg_mul_r: R.Ring.NegMulR(T, mul, neg),
  +d: Nat, +sig: S.Sig(d), +m: S.MV(T, d), +x: S.MV(T, d), +y: S.MV(T, d), +nn: T, h: {S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), m) == S.MV.scalar(T, d, nn) : S.MV(T, d)})
  -> {S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, m, x), S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, m, y)) == S.MV.scale(~T, ~mul, d, nn, S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, m, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y))) : S.MV(T, d)}:
  Equal.trans(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, m, x), S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, m, y)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, y), S.MV.reverse(~T, ~neg, d, m)))), S.MV.scale(~T, ~mul, d, nn, S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, m, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y))),
    PA.Gp.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, False{}, False{}, False{}, False{}, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), S.MV.reverse(~T, ~neg, d, m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, y), S.MV.reverse(~T, ~neg, d, m)), sig),
    Equal.trans(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, y), S.MV.reverse(~T, ~neg, d, m)))), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), S.MV.scale(~T, ~mul, d, nn, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m)))), S.MV.scale(~T, ~mul, d, nn, S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, m, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y))),
    Equal.cong(S.MV(T, d), S.MV(T, d), u => S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), u), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, y), S.MV.reverse(~T, ~neg, d, m))), S.MV.scale(~T, ~mul, d, nn, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m))), Equal.trans(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, y), S.MV.reverse(~T, ~neg, d, m))), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, y)), S.MV.reverse(~T, ~neg, d, m)), S.MV.scale(~T, ~mul, d, nn, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m))),
    Equal.sym(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, y)), S.MV.reverse(~T, ~neg, d, m)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, y), S.MV.reverse(~T, ~neg, d, m))), PA.Gp.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, False{}, False{}, False{}, False{}, S.MV.reverse(~T, ~neg, d, m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, y), S.MV.reverse(~T, ~neg, d, m), sig)),
    Equal.trans(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, y)), S.MV.reverse(~T, ~neg, d, m)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), m), y), S.MV.reverse(~T, ~neg, d, m)), S.MV.scale(~T, ~mul, d, nn, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m))),
    Equal.cong(S.MV(T, d), S.MV(T, d), u => S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, u, S.MV.reverse(~T, ~neg, d, m)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, y)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), m), y), Equal.sym(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), m), y), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, y)), PA.Gp.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, False{}, False{}, False{}, False{}, S.MV.reverse(~T, ~neg, d, m), m, y, sig))),
    Equal.trans(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), m), y), S.MV.reverse(~T, ~neg, d, m)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m))), S.MV.scale(~T, ~mul, d, nn, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m))),
    PA.Gp.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, False{}, False{}, False{}, False{}, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), m), y, S.MV.reverse(~T, ~neg, d, m), sig),
    Equal.trans(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), m), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m))), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.scalar(T, d, nn), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m))), S.MV.scale(~T, ~mul, d, nn, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m))),
    Equal.cong(S.MV(T, d), S.MV(T, d), u => S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, u, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m))), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, m), m), S.MV.scalar(T, d, nn), h),
    Gp.scalar(~T, ~add, ~mul, ~neg, ~neg_mul_l, d, False{}, False{}, nn, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m)), Gpf.canon(~T, ~add, ~mul, ~neg, d, False{}, False{}, y, S.MV.reverse(~T, ~neg, d, m), sig), sig)))))),
    Equal.trans(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), S.MV.scale(~T, ~mul, d, nn, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m)))), S.MV.scale(~T, ~mul, d, nn, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m)))), S.MV.scale(~T, ~mul, d, nn, S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, m, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y))),
    SC.Scale.gp_r(~T, ~add, ~mul, ~neg, ~mul_assoc, ~mul_comm, ~dist_l, ~neg_mul_r, d, False{}, False{}, nn, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m)), sig),
    Equal.cong(S.MV(T, d), S.MV(T, d), u => S.MV.scale(~T, ~mul, d, nn, u), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m))), S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, m, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y)),
    Equal.trans(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m))), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), y), S.MV.reverse(~T, ~neg, d, m)), S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, m, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y)),
    Equal.sym(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), y), S.MV.reverse(~T, ~neg, d, m)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, S.MV.reverse(~T, ~neg, d, m))), PA.Gp.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, False{}, False{}, False{}, False{}, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), y, S.MV.reverse(~T, ~neg, d, m), sig)),
    Equal.cong(S.MV(T, d), S.MV(T, d), u => S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, u, S.MV.reverse(~T, ~neg, d, m)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, x), y), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, m, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y)), PA.Gp.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, False{}, False{}, False{}, False{}, m, x, y, sig)))))))

# sandwiches compose: a (b x ~b) ~a = (a b) x ~(a b)
def Versor.compose(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~add_assoc: R.Ring.Assoc(T, add), ~add_comm: R.Ring.Comm(T, add), ~mul_assoc: R.Ring.Assoc(T, mul), ~mul_comm: R.Ring.Comm(T, mul),
  ~dist_l: R.Ring.DistL(T, add, mul), ~dist_r: R.Ring.DistR(T, add, mul), ~neg_add: R.Ring.NegAdd(T, add, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  ~neg_mul_l: R.Ring.NegMulL(T, mul, neg), ~neg_mul_r: R.Ring.NegMulR(T, mul, neg),
  +d: Nat, +sig: S.Sig(d), +a: S.MV(T, d), +b: S.MV(T, d), +x: S.MV(T, d))
  -> {S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, a, S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, b, x)) == S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), x) : S.MV(T, d)}:
  Equal.trans(S.MV(T, d), S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, a, S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, b, x)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, b, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b)))), S.MV.reverse(~T, ~neg, d, a)), S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), x),
    Equal.cong(S.MV(T, d), S.MV(T, d), u => S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, u), S.MV.reverse(~T, ~neg, d, a)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, b, x), S.MV.reverse(~T, ~neg, d, b)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, b, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b))), PA.Gp.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, False{}, False{}, False{}, False{}, b, x, S.MV.reverse(~T, ~neg, d, b), sig)),
    Equal.trans(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, b, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b)))), S.MV.reverse(~T, ~neg, d, a)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b))), S.MV.reverse(~T, ~neg, d, a)), S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), x),
    Equal.cong(S.MV(T, d), S.MV(T, d), u => S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, u, S.MV.reverse(~T, ~neg, d, a)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, b, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b)))), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b))), Equal.sym(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b))), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, b, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b)))), PA.Gp.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, False{}, False{}, False{}, False{}, a, b, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b)), sig))),
    Equal.trans(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b))), S.MV.reverse(~T, ~neg, d, a)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b)), S.MV.reverse(~T, ~neg, d, a))), S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), x),
    PA.Gp.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, False{}, False{}, False{}, False{}, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b)), S.MV.reverse(~T, ~neg, d, a), sig),
    Equal.trans(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b)), S.MV.reverse(~T, ~neg, d, a))), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, b), S.MV.reverse(~T, ~neg, d, a)))), S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), x),
    Equal.cong(S.MV(T, d), S.MV(T, d), u => S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), u), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, b)), S.MV.reverse(~T, ~neg, d, a)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, b), S.MV.reverse(~T, ~neg, d, a))), PA.Gp.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, False{}, False{}, False{}, False{}, x, S.MV.reverse(~T, ~neg, d, b), S.MV.reverse(~T, ~neg, d, a), sig)),
    Equal.trans(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, b), S.MV.reverse(~T, ~neg, d, a)))), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b)))), S.MV.transform(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), x),
    Equal.cong(S.MV(T, d), S.MV(T, d), u => S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, u)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, b), S.MV.reverse(~T, ~neg, d, a)), S.MV.reverse(~T, ~neg, d, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b)), Equal.sym(S.MV(T, d), S.MV.reverse(~T, ~neg, d, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b)), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, b), S.MV.reverse(~T, ~neg, d, a)), RV.Rev.gp(~T, ~add, ~mul, ~neg, ~add_comm, ~mul_comm, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, False{}, False{}, False{}, False{}, a, b, sig))),
    Equal.sym(S.MV(T, d), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), x), S.MV.reverse(~T, ~neg, d, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b))), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.reverse(~T, ~neg, d, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b)))), PA.Gp.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, False{}, False{}, False{}, False{}, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b), x, S.MV.reverse(~T, ~neg, d, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, a, b)), sig)))))))
