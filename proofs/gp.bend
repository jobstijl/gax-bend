# The geometric product, part 1: congruence, zero, the collapsing
# constructor, and distributivity over addition on both sides.

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S
import ./base.bend as B
import ./leaf.bend as L
import ./add.bend as A
import ./flags.bend as F
import ./sgn.bend as G

# Congruence
# ----------

def Mk.cong(-T: Data, -d: Nat, -e: S.MV(T, d), -e2: S.MV(T, d), -r: S.MV(T, d), -r2: S.MV(T, d),
  ee: {e == e2 : S.MV(T, d)}, er: {r == r2 : S.MV(T, d)})
  -> {S.MV.mk(T, d, e, r) == S.MV.mk(T, d, e2, r2) : S.MV(T, 1n+d)}:
  %ee : {S.MV.mk(T, d, e, r) == S.MV.mk(T, d, _, r2) : S.MV(T, 1n+d)}
  %er : {S.MV.mk(T, d, e, r) == S.MV.mk(T, d, e, _) : S.MV(T, 1n+d)}
  {==}

def Gp.flag(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, -d: Nat, -f: Bool, -f2: Bool, -n: Bool, -n2: Bool,
  -x: S.MV(T, d), -y: S.MV(T, d), -sig: S.Sig(d), ef: {f == f2 : Bool}, en: {n == n2 : Bool})
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, y, sig) == S.MV.gpf(~T, ~add, ~mul, ~neg, d, f2, n2, x, y, sig) : S.MV(T, d)}:
  %ef : {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, y, sig) == S.MV.gpf(~T, ~add, ~mul, ~neg, d, _, n2, x, y, sig) : S.MV(T, d)}
  %en : {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, y, sig) == S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, _, x, y, sig) : S.MV(T, d)}
  {==}

def Gp.cong(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, -d: Nat, -f: Bool, -n: Bool, -x: S.MV(T, d), -x2: S.MV(T, d),
  -y: S.MV(T, d), -y2: S.MV(T, d), -sig: S.Sig(d), ex: {x == x2 : S.MV(T, d)}, ey: {y == y2 : S.MV(T, d)})
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, y, sig) == S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x2, y2, sig) : S.MV(T, d)}:
  %ex : {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, y, sig) == S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, _, y2, sig) : S.MV(T, d)}
  %ey : {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, y, sig) == S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, _, sig) : S.MV(T, d)}
  {==}

# Zero
# ----

def Gp.zero_r(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, d: Nat, f: Bool, n: Bool, x: S.MV(T, d), sig: S.Sig(d))
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, S.MV.zero(T, d), sig) == S.MV.zero(T, d) : S.MV(T, d)}:
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
          {==}

def Gp.zero_l(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, d: Nat, f: Bool, n: Bool, y: S.MV(T, d), sig: S.Sig(d))
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, S.MV.zero(T, d), y, sig) == S.MV.zero(T, d) : S.MV(T, d)}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

# The collapsing constructor
# --------------------------

# a product does not see whether its left operand came through MV.mk
def Gp.mk_l(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, +p: Nat, +f: Bool, +n: Bool, a: S.MV(T, p), b: S.MV(T, p), y: S.MV(T, 1n+p), sig: S.Sig(1n+p))
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+p, f, n, S.MV.mk(T, p, a, b), y, sig) == S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+p, f, n, S.N{a, b}, y, sig) : S.MV(T, 1n+p)}:
  match p:
    case 0n:
      match a:
        case S.LZ{}:
          match b:
            case S.LZ{}:
              match y:
                case S.NZ{}:
                  {==}
                case S.N{y1, y2}:
                  match sig:
                    case S.Gen{q, +rest}:
                      match q:
                        case S.QZ{}:
                          {==}
                        case S.QP{}:
                          {==}
                        case S.QN{}:
                          {==}
            case S.L{w}:
              {==}
        case S.L{v}:
          {==}
    case 1n+o:
      match a:
        case S.NZ{}:
          match b:
            case S.NZ{}:
              match y:
                case S.NZ{}:
                  {==}
                case S.N{y1, y2}:
                  match sig:
                    case S.Gen{q, +rest}:
                      match q:
                        case S.QZ{}:
                          {==}
                        case S.QP{}:
                          {==}
                        case S.QN{}:
                          {==}
            case S.N{b1, b2}:
              {==}
        case S.N{a1, a2}:
          {==}

# a product with a right operand N{zero, zero} is zero
def Gp.zero_lvl(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, +p: Nat, +f: Bool, +n: Bool, +x1: S.MV(T, p), +x2: S.MV(T, p), sig: S.Sig(1n+p))
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+p, f, n, S.N{x1, x2}, S.N{S.MV.zero(T, p), S.MV.zero(T, p)}, sig) == S.NZ{} : S.MV(T, 1n+p)}:
  match p:
    case 0n:
      match sig:
        case S.Gen{q, +rest}:
          match q:
            case S.QZ{}:
              Mk.cong(T, 0n, S.MV.add(~T, ~add, 0n, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, f, Bool.xor(n, f), x1, S.LZ{}, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), n, x2, S.LZ{}, rest)), S.MV.add(~T, ~add, 0n, S.LZ{}, S.LZ{}), S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, f, n, x2, S.LZ{}, rest), S.LZ{},
                A.Add.cong(~T, ~add, 0n, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, f, Bool.xor(n, f), x1, S.LZ{}, rest), S.LZ{}, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), n, x2, S.LZ{}, rest), S.LZ{}, Gp.zero_r(~T, ~add, ~mul, ~neg, 0n, f, Bool.xor(n, f), x1, rest), Gp.zero_r(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), n, x2, rest)),
                Gp.zero_r(~T, ~add, ~mul, ~neg, 0n, f, n, x2, rest))
            case S.QP{}:
              Mk.cong(T, 0n, S.MV.add(~T, ~add, 0n, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, f, Bool.xor(n, f), x1, S.LZ{}, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), n, x2, S.LZ{}, rest)), S.MV.add(~T, ~add, 0n, S.LZ{}, S.LZ{}), S.MV.add(~T, ~add, 0n, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), Bool.xor(n, f), x1, S.LZ{}, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, f, n, x2, S.LZ{}, rest)), S.MV.add(~T, ~add, 0n, S.LZ{}, S.LZ{}),
                A.Add.cong(~T, ~add, 0n, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, f, Bool.xor(n, f), x1, S.LZ{}, rest), S.LZ{}, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), n, x2, S.LZ{}, rest), S.LZ{}, Gp.zero_r(~T, ~add, ~mul, ~neg, 0n, f, Bool.xor(n, f), x1, rest), Gp.zero_r(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), n, x2, rest)),
                A.Add.cong(~T, ~add, 0n, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), Bool.xor(n, f), x1, S.LZ{}, rest), S.LZ{}, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, f, n, x2, S.LZ{}, rest), S.LZ{}, Gp.zero_r(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), Bool.xor(n, f), x1, rest), Gp.zero_r(~T, ~add, ~mul, ~neg, 0n, f, n, x2, rest)))
            case S.QN{}:
              Mk.cong(T, 0n, S.MV.add(~T, ~add, 0n, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, f, Bool.xor(n, f), x1, S.LZ{}, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), n, x2, S.LZ{}, rest)), S.MV.add(~T, ~add, 0n, S.LZ{}, S.LZ{}), S.MV.add(~T, ~add, 0n, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, S.LZ{}, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, f, n, x2, S.LZ{}, rest)), S.MV.add(~T, ~add, 0n, S.LZ{}, S.LZ{}),
                A.Add.cong(~T, ~add, 0n, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, f, Bool.xor(n, f), x1, S.LZ{}, rest), S.LZ{}, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), n, x2, S.LZ{}, rest), S.LZ{}, Gp.zero_r(~T, ~add, ~mul, ~neg, 0n, f, Bool.xor(n, f), x1, rest), Gp.zero_r(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), n, x2, rest)),
                A.Add.cong(~T, ~add, 0n, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, S.LZ{}, rest), S.LZ{}, S.MV.gpf(~T, ~add, ~mul, ~neg, 0n, f, n, x2, S.LZ{}, rest), S.LZ{}, Gp.zero_r(~T, ~add, ~mul, ~neg, 0n, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, rest), Gp.zero_r(~T, ~add, ~mul, ~neg, 0n, f, n, x2, rest)))
    case 1n+o:
      match sig:
        case S.Gen{q, +rest}:
          match q:
            case S.QZ{}:
              Mk.cong(T, 1n+o, S.MV.add(~T, ~add, 1n+o, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, f, Bool.xor(n, f), x1, S.NZ{}, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), n, x2, S.NZ{}, rest)), S.MV.add(~T, ~add, 1n+o, S.NZ{}, S.NZ{}), S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, f, n, x2, S.NZ{}, rest), S.NZ{},
                A.Add.cong(~T, ~add, 1n+o, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, f, Bool.xor(n, f), x1, S.NZ{}, rest), S.NZ{}, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), n, x2, S.NZ{}, rest), S.NZ{}, Gp.zero_r(~T, ~add, ~mul, ~neg, 1n+o, f, Bool.xor(n, f), x1, rest), Gp.zero_r(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), n, x2, rest)),
                Gp.zero_r(~T, ~add, ~mul, ~neg, 1n+o, f, n, x2, rest))
            case S.QP{}:
              Mk.cong(T, 1n+o, S.MV.add(~T, ~add, 1n+o, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, f, Bool.xor(n, f), x1, S.NZ{}, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), n, x2, S.NZ{}, rest)), S.MV.add(~T, ~add, 1n+o, S.NZ{}, S.NZ{}), S.MV.add(~T, ~add, 1n+o, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), Bool.xor(n, f), x1, S.NZ{}, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, f, n, x2, S.NZ{}, rest)), S.MV.add(~T, ~add, 1n+o, S.NZ{}, S.NZ{}),
                A.Add.cong(~T, ~add, 1n+o, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, f, Bool.xor(n, f), x1, S.NZ{}, rest), S.NZ{}, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), n, x2, S.NZ{}, rest), S.NZ{}, Gp.zero_r(~T, ~add, ~mul, ~neg, 1n+o, f, Bool.xor(n, f), x1, rest), Gp.zero_r(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), n, x2, rest)),
                A.Add.cong(~T, ~add, 1n+o, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), Bool.xor(n, f), x1, S.NZ{}, rest), S.NZ{}, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, f, n, x2, S.NZ{}, rest), S.NZ{}, Gp.zero_r(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), Bool.xor(n, f), x1, rest), Gp.zero_r(~T, ~add, ~mul, ~neg, 1n+o, f, n, x2, rest)))
            case S.QN{}:
              Mk.cong(T, 1n+o, S.MV.add(~T, ~add, 1n+o, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, f, Bool.xor(n, f), x1, S.NZ{}, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), n, x2, S.NZ{}, rest)), S.MV.add(~T, ~add, 1n+o, S.NZ{}, S.NZ{}), S.MV.add(~T, ~add, 1n+o, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, S.NZ{}, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, f, n, x2, S.NZ{}, rest)), S.MV.add(~T, ~add, 1n+o, S.NZ{}, S.NZ{}),
                A.Add.cong(~T, ~add, 1n+o, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, f, Bool.xor(n, f), x1, S.NZ{}, rest), S.NZ{}, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), n, x2, S.NZ{}, rest), S.NZ{}, Gp.zero_r(~T, ~add, ~mul, ~neg, 1n+o, f, Bool.xor(n, f), x1, rest), Gp.zero_r(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), n, x2, rest)),
                A.Add.cong(~T, ~add, 1n+o, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, S.NZ{}, rest), S.NZ{}, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+o, f, n, x2, S.NZ{}, rest), S.NZ{}, Gp.zero_r(~T, ~add, ~mul, ~neg, 1n+o, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, rest), Gp.zero_r(~T, ~add, ~mul, ~neg, 1n+o, f, n, x2, rest)))

# a product does not see whether its right operand came through MV.mk
def Gp.mk_r(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, +p: Nat, +f: Bool, +n: Bool, x: S.MV(T, 1n+p), a: S.MV(T, p), b: S.MV(T, p), +sig: S.Sig(1n+p))
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+p, f, n, x, S.MV.mk(T, p, a, b), sig) == S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+p, f, n, x, S.N{a, b}, sig) : S.MV(T, 1n+p)}:
  match p:
    case 0n:
      match x:
        case S.NZ{}:
          {==}
        case S.N{x1, x2}:
          match a:
            case S.LZ{}:
              match b:
                case S.LZ{}:
                  Equal.sym(S.MV(T, 1n), S.MV.gpf(~T, ~add, ~mul, ~neg, 1n, f, n, S.N{x1, x2}, S.N{S.LZ{}, S.LZ{}}, sig), S.NZ{},
                    Gp.zero_lvl(~T, ~add, ~mul, ~neg, 0n, f, n, x1, x2, sig))
                case S.L{w}:
                  {==}
            case S.L{v}:
              {==}
    case 1n+o:
      match x:
        case S.NZ{}:
          {==}
        case S.N{x1, x2}:
          match a:
            case S.NZ{}:
              match b:
                case S.NZ{}:
                  Equal.sym(S.MV(T, 2n+o), S.MV.gpf(~T, ~add, ~mul, ~neg, 2n+o, f, n, S.N{x1, x2}, S.N{S.NZ{}, S.NZ{}}, sig), S.NZ{},
                    Gp.zero_lvl(~T, ~add, ~mul, ~neg, 1n+o, f, n, x1, x2, sig))
                case S.N{b1, b2}:
                  {==}
            case S.N{a1, a2}:
              {==}
# Distributivity
# --------------

# (-1)^n * inv^f(a + b) * z = (-1)^n * inv^f(a) * z + (-1)^n * inv^f(b) * z
def Gp.add_l(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~add_assoc: R.Ring.Assoc(T, add), ~add_comm: R.Ring.Comm(T, add),
  ~dist_r: R.Ring.DistR(T, add, mul), ~neg_add: R.Ring.NegAdd(T, add, neg),
  +d: Nat, +f: Bool, +n: Bool, a: S.MV(T, d), b: S.MV(T, d), z: S.MV(T, d), +sig: S.Sig(d))
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, S.MV.add(~T, ~add, d, a, b), z, sig) == S.MV.add(~T, ~add, d, S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, a, z, sig), S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, b, z, sig)) : S.MV(T, d)}:
  match d:
    case 0n:
      match a:
        case S.LZ{}:
          {==}
        case S.L{+x}:
          match b:
            case S.LZ{}:
              match z:
                case S.LZ{}:
                  {==}
                case S.L{c}:
                  {==}
            case S.L{+y}:
              match z:
                case S.LZ{}:
                  {==}
                case S.L{+c}:
                  B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, mul(add(x, y), c)),
                    add(S.Ring.negf(~T, ~neg, n, mul(x, c)), S.Ring.negf(~T, ~neg, n, mul(y, c))),
                    Equal.trans(T, S.Ring.negf(~T, ~neg, n, mul(add(x, y), c)),
                      S.Ring.negf(~T, ~neg, n, add(mul(x, c), mul(y, c))),
                      add(S.Ring.negf(~T, ~neg, n, mul(x, c)), S.Ring.negf(~T, ~neg, n, mul(y, c))),
                      Equal.cong(T, T, w => S.Ring.negf(~T, ~neg, n, w), mul(add(x, y), c), add(mul(x, c), mul(y, c)), dist_r(x, y, c)),
                      L.Negf.add(~T, ~add, ~neg, ~neg_add, n, mul(x, c), mul(y, c))))
    case 1n+p:
      match a:
        case S.NZ{}:
          {==}
        case S.N{+a1, +a2}:
          match b:
            case S.NZ{}:
              Equal.sym(S.MV(T, 1n+p), S.MV.add(~T, ~add, 1n+p, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+p, f, n, S.N{a1, a2}, z, sig), S.NZ{}), S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+p, f, n, S.N{a1, a2}, z, sig),
                A.Add.zero_r(~T, ~add, 1n+p, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+p, f, n, S.N{a1, a2}, z, sig)))
            case S.N{+b1, +b2}:
              match z:
                case S.NZ{}:
                  {==}
                case S.N{+z1, +z2}:
                  match sig:
                    case S.Gen{q, +rest}:
                      match q:
                        case S.QZ{}:
                          +pa1 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), a1, z2, rest)
                          +pb1 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), b1, z2, rest)
                          +pa2 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, a2, z1, rest)
                          +pb2 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, b2, z1, rest)
                          +pa3 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), a1, z1, rest)
                          +pb3 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), b1, z1, rest)
                          +pa4 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, a2, z2, rest)
                          +pb4 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, b2, z2, rest)
                          Equal.trans(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.add(~T, ~add, p, a2, b2), z1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.add(~T, ~add, p, a2, b2), z2, rest)), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, pa4, pb4)), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.add(~T, ~add, p, pa1, pa2), pa4), S.MV.mk(T, p, S.MV.add(~T, ~add, p, pb1, pb2), pb4)),
                              Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.add(~T, ~add, p, a2, b2), z1, rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.add(~T, ~add, p, a2, b2), z2, rest), S.MV.add(~T, ~add, p, pa4, pb4),
                                Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.add(~T, ~add, p, a2, b2), z1, rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pb1), S.MV.add(~T, ~add, p, pa2, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)),
                                A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z2, rest), S.MV.add(~T, ~add, p, pa1, pb1), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.add(~T, ~add, p, a2, b2), z1, rest), S.MV.add(~T, ~add, p, pa2, pb2), Gp.add_l(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_r, ~neg_add, p, f, Bool.xor(n, f), a1, b1, z2, rest), Gp.add_l(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_r, ~neg_add, p, Bool.not(f), n, a2, b2, z1, rest)),
                                A.Add.swap4(~T, ~add, ~add_assoc, ~add_comm, p, pa1, pb1, pa2, pb2)),
                                Gp.add_l(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_r, ~neg_add, p, f, n, a2, b2, z2, rest)),
                              Equal.sym(S.MV(T, 1n+p), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.add(~T, ~add, p, pa1, pa2), pa4), S.MV.mk(T, p, S.MV.add(~T, ~add, p, pb1, pb2), pb4)), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, pa4, pb4)),
                              A.Add.mk(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), pa4, S.MV.add(~T, ~add, p, pb1, pb2), pb4)))
                        case S.QP{}:
                          +pa1 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), a1, z2, rest)
                          +pb1 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), b1, z2, rest)
                          +pa2 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, a2, z1, rest)
                          +pb2 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, b2, z1, rest)
                          +pa3 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), a1, z1, rest)
                          +pb3 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), b1, z1, rest)
                          +pa4 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, a2, z2, rest)
                          +pb4 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, b2, z2, rest)
                          Equal.trans(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.add(~T, ~add, p, a2, b2), z1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.add(~T, ~add, p, a2, b2), z2, rest))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4))), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pa3, pa4)), S.MV.mk(T, p, S.MV.add(~T, ~add, p, pb1, pb2), S.MV.add(~T, ~add, p, pb3, pb4))),
                              Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.add(~T, ~add, p, a2, b2), z1, rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.add(~T, ~add, p, a2, b2), z2, rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4)),
                                Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.add(~T, ~add, p, a2, b2), z1, rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pb1), S.MV.add(~T, ~add, p, pa2, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)),
                                A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z2, rest), S.MV.add(~T, ~add, p, pa1, pb1), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.add(~T, ~add, p, a2, b2), z1, rest), S.MV.add(~T, ~add, p, pa2, pb2), Gp.add_l(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_r, ~neg_add, p, f, Bool.xor(n, f), a1, b1, z2, rest), Gp.add_l(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_r, ~neg_add, p, Bool.not(f), n, a2, b2, z1, rest)),
                                A.Add.swap4(~T, ~add, ~add_assoc, ~add_comm, p, pa1, pb1, pa2, pb2)),
                                Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.add(~T, ~add, p, a2, b2), z2, rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pb3), S.MV.add(~T, ~add, p, pa4, pb4)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4)),
                                A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z1, rest), S.MV.add(~T, ~add, p, pa3, pb3), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.add(~T, ~add, p, a2, b2), z2, rest), S.MV.add(~T, ~add, p, pa4, pb4), Gp.add_l(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_r, ~neg_add, p, Bool.not(f), Bool.xor(n, f), a1, b1, z1, rest), Gp.add_l(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_r, ~neg_add, p, f, n, a2, b2, z2, rest)),
                                A.Add.swap4(~T, ~add, ~add_assoc, ~add_comm, p, pa3, pb3, pa4, pb4))),
                              Equal.sym(S.MV(T, 1n+p), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pa3, pa4)), S.MV.mk(T, p, S.MV.add(~T, ~add, p, pb1, pb2), S.MV.add(~T, ~add, p, pb3, pb4))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4))),
                              A.Add.mk(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb1, pb2), S.MV.add(~T, ~add, p, pb3, pb4))))
                        case S.QN{}:
                          +pa1 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), a1, z2, rest)
                          +pb1 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), b1, z2, rest)
                          +pa2 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, a2, z1, rest)
                          +pb2 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, b2, z1, rest)
                          +pa3 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), a1, z1, rest)
                          +pb3 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), b1, z1, rest)
                          +pa4 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, a2, z2, rest)
                          +pb4 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, b2, z2, rest)
                          Equal.trans(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.add(~T, ~add, p, a2, b2), z1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), S.MV.add(~T, ~add, p, a1, b1), z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.add(~T, ~add, p, a2, b2), z2, rest))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4))), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pa3, pa4)), S.MV.mk(T, p, S.MV.add(~T, ~add, p, pb1, pb2), S.MV.add(~T, ~add, p, pb3, pb4))),
                              Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.add(~T, ~add, p, a2, b2), z1, rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), S.MV.add(~T, ~add, p, a1, b1), z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.add(~T, ~add, p, a2, b2), z2, rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4)),
                                Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.add(~T, ~add, p, a2, b2), z1, rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pb1), S.MV.add(~T, ~add, p, pa2, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)),
                                A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.add(~T, ~add, p, a1, b1), z2, rest), S.MV.add(~T, ~add, p, pa1, pb1), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.add(~T, ~add, p, a2, b2), z1, rest), S.MV.add(~T, ~add, p, pa2, pb2), Gp.add_l(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_r, ~neg_add, p, f, Bool.xor(n, f), a1, b1, z2, rest), Gp.add_l(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_r, ~neg_add, p, Bool.not(f), n, a2, b2, z1, rest)),
                                A.Add.swap4(~T, ~add, ~add_assoc, ~add_comm, p, pa1, pb1, pa2, pb2)),
                                Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), S.MV.add(~T, ~add, p, a1, b1), z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.add(~T, ~add, p, a2, b2), z2, rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pb3), S.MV.add(~T, ~add, p, pa4, pb4)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4)),
                                A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), S.MV.add(~T, ~add, p, a1, b1), z1, rest), S.MV.add(~T, ~add, p, pa3, pb3), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.add(~T, ~add, p, a2, b2), z2, rest), S.MV.add(~T, ~add, p, pa4, pb4), Gp.add_l(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_r, ~neg_add, p, Bool.not(f), Bool.not(Bool.xor(n, f)), a1, b1, z1, rest), Gp.add_l(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_r, ~neg_add, p, f, n, a2, b2, z2, rest)),
                                A.Add.swap4(~T, ~add, ~add_assoc, ~add_comm, p, pa3, pb3, pa4, pb4))),
                              Equal.sym(S.MV(T, 1n+p), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pa3, pa4)), S.MV.mk(T, p, S.MV.add(~T, ~add, p, pb1, pb2), S.MV.add(~T, ~add, p, pb3, pb4))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4))),
                              A.Add.mk(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb1, pb2), S.MV.add(~T, ~add, p, pb3, pb4))))

# (-1)^n * inv^f(x) * (a + b) = (-1)^n * inv^f(x) * a + (-1)^n * inv^f(x) * b
def Gp.add_r(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~add_assoc: R.Ring.Assoc(T, add), ~add_comm: R.Ring.Comm(T, add),
  ~dist_l: R.Ring.DistL(T, add, mul), ~neg_add: R.Ring.NegAdd(T, add, neg),
  +d: Nat, +f: Bool, +n: Bool, x: S.MV(T, d), a: S.MV(T, d), b: S.MV(T, d), +sig: S.Sig(d))
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, S.MV.add(~T, ~add, d, a, b), sig) == S.MV.add(~T, ~add, d, S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, a, sig), S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, b, sig)) : S.MV(T, d)}:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          {==}
        case S.L{+c}:
          match a:
            case S.LZ{}:
              {==}
            case S.L{+y}:
              match b:
                case S.LZ{}:
                  {==}
                case S.L{+w}:
                  B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, mul(c, add(y, w))),
                    add(S.Ring.negf(~T, ~neg, n, mul(c, y)), S.Ring.negf(~T, ~neg, n, mul(c, w))),
                    Equal.trans(T, S.Ring.negf(~T, ~neg, n, mul(c, add(y, w))),
                      S.Ring.negf(~T, ~neg, n, add(mul(c, y), mul(c, w))),
                      add(S.Ring.negf(~T, ~neg, n, mul(c, y)), S.Ring.negf(~T, ~neg, n, mul(c, w))),
                      Equal.cong(T, T, v => S.Ring.negf(~T, ~neg, n, v), mul(c, add(y, w)), add(mul(c, y), mul(c, w)), dist_l(c, y, w)),
                      L.Negf.add(~T, ~add, ~neg, ~neg_add, n, mul(c, y), mul(c, w))))
    case 1n+p:
      match x:
        case S.NZ{}:
          {==}
        case S.N{+x1, +x2}:
          match a:
            case S.NZ{}:
              {==}
            case S.N{+a1, +a2}:
              match b:
                case S.NZ{}:
                  Equal.sym(S.MV(T, 1n+p), S.MV.add(~T, ~add, 1n+p, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+p, f, n, S.N{x1, x2}, S.N{a1, a2}, sig), S.NZ{}), S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+p, f, n, S.N{x1, x2}, S.N{a1, a2}, sig),
                    A.Add.zero_r(~T, ~add, 1n+p, S.MV.gpf(~T, ~add, ~mul, ~neg, 1n+p, f, n, S.N{x1, x2}, S.N{a1, a2}, sig)))
                case S.N{+b1, +b2}:
                  match sig:
                    case S.Gen{q, +rest}:
                      match q:
                        case S.QZ{}:
                          +pa1 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, a2, rest)
                          +pb1 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, b2, rest)
                          +pa2 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, a1, rest)
                          +pb2 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, b1, rest)
                          +pa3 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), x1, a1, rest)
                          +pb3 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), x1, b1, rest)
                          +pa4 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, a2, rest)
                          +pb4 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, b2, rest)
                          Equal.trans(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, S.MV.add(~T, ~add, p, a1, b1), rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.add(~T, ~add, p, a2, b2), rest)), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, pa4, pb4)), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.add(~T, ~add, p, pa1, pa2), pa4), S.MV.mk(T, p, S.MV.add(~T, ~add, p, pb1, pb2), pb4)),
                              Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, S.MV.add(~T, ~add, p, a1, b1), rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.add(~T, ~add, p, pa4, pb4),
                                Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, S.MV.add(~T, ~add, p, a1, b1), rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pb1), S.MV.add(~T, ~add, p, pa2, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)),
                                A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.add(~T, ~add, p, pa1, pb1), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, S.MV.add(~T, ~add, p, a1, b1), rest), S.MV.add(~T, ~add, p, pa2, pb2), Gp.add_r(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_l, ~neg_add, p, f, Bool.xor(n, f), x1, a2, b2, rest), Gp.add_r(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_l, ~neg_add, p, Bool.not(f), n, x2, a1, b1, rest)),
                                A.Add.swap4(~T, ~add, ~add_assoc, ~add_comm, p, pa1, pb1, pa2, pb2)),
                                Gp.add_r(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_l, ~neg_add, p, f, n, x2, a2, b2, rest)),
                              Equal.sym(S.MV(T, 1n+p), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.add(~T, ~add, p, pa1, pa2), pa4), S.MV.mk(T, p, S.MV.add(~T, ~add, p, pb1, pb2), pb4)), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, pa4, pb4)),
                              A.Add.mk(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), pa4, S.MV.add(~T, ~add, p, pb1, pb2), pb4)))
                        case S.QP{}:
                          +pa1 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, a2, rest)
                          +pb1 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, b2, rest)
                          +pa2 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, a1, rest)
                          +pb2 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, b1, rest)
                          +pa3 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), x1, a1, rest)
                          +pb3 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), x1, b1, rest)
                          +pa4 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, a2, rest)
                          +pb4 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, b2, rest)
                          Equal.trans(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, S.MV.add(~T, ~add, p, a1, b1), rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a1, b1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.add(~T, ~add, p, a2, b2), rest))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4))), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pa3, pa4)), S.MV.mk(T, p, S.MV.add(~T, ~add, p, pb1, pb2), S.MV.add(~T, ~add, p, pb3, pb4))),
                              Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, S.MV.add(~T, ~add, p, a1, b1), rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a1, b1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.add(~T, ~add, p, a2, b2), rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4)),
                                Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, S.MV.add(~T, ~add, p, a1, b1), rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pb1), S.MV.add(~T, ~add, p, pa2, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)),
                                A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.add(~T, ~add, p, pa1, pb1), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, S.MV.add(~T, ~add, p, a1, b1), rest), S.MV.add(~T, ~add, p, pa2, pb2), Gp.add_r(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_l, ~neg_add, p, f, Bool.xor(n, f), x1, a2, b2, rest), Gp.add_r(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_l, ~neg_add, p, Bool.not(f), n, x2, a1, b1, rest)),
                                A.Add.swap4(~T, ~add, ~add_assoc, ~add_comm, p, pa1, pb1, pa2, pb2)),
                                Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a1, b1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.add(~T, ~add, p, a2, b2), rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pb3), S.MV.add(~T, ~add, p, pa4, pb4)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4)),
                                A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a1, b1), rest), S.MV.add(~T, ~add, p, pa3, pb3), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.add(~T, ~add, p, pa4, pb4), Gp.add_r(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_l, ~neg_add, p, Bool.not(f), Bool.xor(n, f), x1, a1, b1, rest), Gp.add_r(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_l, ~neg_add, p, f, n, x2, a2, b2, rest)),
                                A.Add.swap4(~T, ~add, ~add_assoc, ~add_comm, p, pa3, pb3, pa4, pb4))),
                              Equal.sym(S.MV(T, 1n+p), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pa3, pa4)), S.MV.mk(T, p, S.MV.add(~T, ~add, p, pb1, pb2), S.MV.add(~T, ~add, p, pb3, pb4))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4))),
                              A.Add.mk(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb1, pb2), S.MV.add(~T, ~add, p, pb3, pb4))))
                        case S.QN{}:
                          +pa1 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, a2, rest)
                          +pb1 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, b2, rest)
                          +pa2 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, a1, rest)
                          +pb2 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, b1, rest)
                          +pa3 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, a1, rest)
                          +pb3 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, b1, rest)
                          +pa4 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, a2, rest)
                          +pb4 = S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, b2, rest)
                          Equal.trans(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, S.MV.add(~T, ~add, p, a1, b1), rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, S.MV.add(~T, ~add, p, a1, b1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.add(~T, ~add, p, a2, b2), rest))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4))), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pa3, pa4)), S.MV.mk(T, p, S.MV.add(~T, ~add, p, pb1, pb2), S.MV.add(~T, ~add, p, pb3, pb4))),
                              Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, S.MV.add(~T, ~add, p, a1, b1), rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, S.MV.add(~T, ~add, p, a1, b1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.add(~T, ~add, p, a2, b2), rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4)),
                                Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, S.MV.add(~T, ~add, p, a1, b1), rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pb1), S.MV.add(~T, ~add, p, pa2, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)),
                                A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), x1, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.add(~T, ~add, p, pa1, pb1), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, x2, S.MV.add(~T, ~add, p, a1, b1), rest), S.MV.add(~T, ~add, p, pa2, pb2), Gp.add_r(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_l, ~neg_add, p, f, Bool.xor(n, f), x1, a2, b2, rest), Gp.add_r(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_l, ~neg_add, p, Bool.not(f), n, x2, a1, b1, rest)),
                                A.Add.swap4(~T, ~add, ~add_assoc, ~add_comm, p, pa1, pb1, pa2, pb2)),
                                Equal.trans(S.MV(T, p), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, S.MV.add(~T, ~add, p, a1, b1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.add(~T, ~add, p, a2, b2), rest)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pb3), S.MV.add(~T, ~add, p, pa4, pb4)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4)),
                                A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, S.MV.add(~T, ~add, p, a1, b1), rest), S.MV.add(~T, ~add, p, pa3, pb3), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, x2, S.MV.add(~T, ~add, p, a2, b2), rest), S.MV.add(~T, ~add, p, pa4, pb4), Gp.add_r(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_l, ~neg_add, p, Bool.not(f), Bool.not(Bool.xor(n, f)), x1, a1, b1, rest), Gp.add_r(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_l, ~neg_add, p, f, n, x2, a2, b2, rest)),
                                A.Add.swap4(~T, ~add, ~add_assoc, ~add_comm, p, pa3, pb3, pa4, pb4))),
                              Equal.sym(S.MV(T, 1n+p), S.MV.add(~T, ~add, 1n+p, S.MV.mk(T, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pa3, pa4)), S.MV.mk(T, p, S.MV.add(~T, ~add, p, pb1, pb2), S.MV.add(~T, ~add, p, pb3, pb4))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pb1, pb2)), S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb3, pb4))),
                              A.Add.mk(~T, ~add, p, S.MV.add(~T, ~add, p, pa1, pa2), S.MV.add(~T, ~add, p, pa3, pa4), S.MV.add(~T, ~add, p, pb1, pb2), S.MV.add(~T, ~add, p, pb3, pb4))))
# Signs
# -----

# a sign on the right operand comes out: x * ((-1)^m v) = (-1)^m (x * v)
def Gp.sgn_r(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~neg_mul_r: R.Ring.NegMulR(T, mul, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  +d: Nat, +f: Bool, +n: Bool, u: S.MV(T, d), +m: Bool, v: S.MV(T, d), +sig: S.Sig(d))
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, u, S.MV.sgn(~T, ~neg, d, m, False{}, False{}, v), sig) == S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, Bool.xor(n, m), u, v, sig) : S.MV(T, d)}:
  match d:
    case 0n:
      match u:
        case S.LZ{}:
          {==}
        case S.L{+a}:
          match v:
            case S.LZ{}:
              {==}
            case S.L{+b}:
              B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, mul(a, S.Ring.negf(~T, ~neg, m, b))), S.Ring.negf(~T, ~neg, Bool.xor(n, m), mul(a, b)),
                Equal.trans(T, S.Ring.negf(~T, ~neg, n, mul(a, S.Ring.negf(~T, ~neg, m, b))),
                  S.Ring.negf(~T, ~neg, n, S.Ring.negf(~T, ~neg, m, mul(a, b))),
                  S.Ring.negf(~T, ~neg, Bool.xor(n, m), mul(a, b)),
                  Equal.cong(T, T, w => S.Ring.negf(~T, ~neg, n, w), mul(a, S.Ring.negf(~T, ~neg, m, b)), S.Ring.negf(~T, ~neg, m, mul(a, b)),
                    L.Negf.mul_r(~T, ~mul, ~neg, ~neg_mul_r, m, a, b)),
                  L.Negf.negf(~T, ~neg, ~neg_neg, n, m, mul(a, b))))
    case 1n+p:
      match u:
        case S.NZ{}:
          {==}
        case S.N{+u1, +u2}:
          match v:
            case S.NZ{}:
              {==}
            case S.N{+v1, +v2}:
              match sig:
                case S.Gen{q, +rest}:
                  match q:
                    case S.QZ{}:
                      Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), u1, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, u2, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(Bool.xor(n, m), f), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, m), u2, v1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, u2, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, m), u2, v2, rest),
                          A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), u1, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(Bool.xor(n, m), f), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, u2, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, m), u2, v1, rest),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), u1, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(Bool.xor(n, f), m), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(Bool.xor(n, m), f), u1, v2, rest),
                              Gp.sgn_r(~T, ~add, ~mul, ~neg, ~neg_mul_r, ~neg_neg, p, f, Bool.xor(n, f), u1, m, v2, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, f, f, Bool.xor(Bool.xor(n, f), m), Bool.xor(Bool.xor(n, m), f), u1, v2, rest,
                              {==},
                              F.Flag.sr_a(n, f, m))),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, u2, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, Bool.xor(m, False{})), u2, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, m), u2, v1, rest),
                              Gp.sgn_r(~T, ~add, ~mul, ~neg, ~neg_mul_r, ~neg_neg, p, Bool.not(f), n, u2, Bool.xor(m, False{}), v1, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(f), Bool.xor(n, Bool.xor(m, False{})), Bool.xor(n, m), u2, v1, rest,
                              {==},
                              F.Flag.sr_b(n, m)))),
                          Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, u2, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, m), u2, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, m), u2, v2, rest),
                            Gp.sgn_r(~T, ~add, ~mul, ~neg, ~neg_mul_r, ~neg_neg, p, f, n, u2, m, v2, rest),
                            Gp.flag(~T, ~add, ~mul, ~neg, p, f, f, Bool.xor(n, m), Bool.xor(n, m), u2, v2, rest,
                            {==},
                            {==})))
                    case S.QP{}:
                      Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), u1, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, u2, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(Bool.xor(n, m), f), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, m), u2, v1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), u1, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, u2, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(Bool.xor(n, m), f), u1, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, m), u2, v2, rest)),
                          A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), u1, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(Bool.xor(n, m), f), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, u2, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, m), u2, v1, rest),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), u1, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(Bool.xor(n, f), m), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(Bool.xor(n, m), f), u1, v2, rest),
                              Gp.sgn_r(~T, ~add, ~mul, ~neg, ~neg_mul_r, ~neg_neg, p, f, Bool.xor(n, f), u1, m, v2, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, f, f, Bool.xor(Bool.xor(n, f), m), Bool.xor(Bool.xor(n, m), f), u1, v2, rest,
                              {==},
                              F.Flag.sr_a(n, f, m))),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, u2, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, Bool.xor(m, False{})), u2, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, m), u2, v1, rest),
                              Gp.sgn_r(~T, ~add, ~mul, ~neg, ~neg_mul_r, ~neg_neg, p, Bool.not(f), n, u2, Bool.xor(m, False{}), v1, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(f), Bool.xor(n, Bool.xor(m, False{})), Bool.xor(n, m), u2, v1, rest,
                              {==},
                              F.Flag.sr_b(n, m)))),
                          A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), u1, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(Bool.xor(n, m), f), u1, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, u2, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, m), u2, v2, rest),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), u1, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(Bool.xor(n, f), Bool.xor(m, False{})), u1, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(Bool.xor(n, m), f), u1, v1, rest),
                              Gp.sgn_r(~T, ~add, ~mul, ~neg, ~neg_mul_r, ~neg_neg, p, Bool.not(f), Bool.xor(n, f), u1, Bool.xor(m, False{}), v1, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(f), Bool.xor(Bool.xor(n, f), Bool.xor(m, False{})), Bool.xor(Bool.xor(n, m), f), u1, v1, rest,
                              {==},
                              F.Flag.sr_cp(n, f, m))),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, u2, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, m), u2, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, m), u2, v2, rest),
                              Gp.sgn_r(~T, ~add, ~mul, ~neg, ~neg_mul_r, ~neg_neg, p, f, n, u2, m, v2, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, f, f, Bool.xor(n, m), Bool.xor(n, m), u2, v2, rest,
                              {==},
                              {==}))))
                    case S.QN{}:
                      Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), u1, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, u2, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(Bool.xor(n, m), f), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, m), u2, v1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), u1, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, u2, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(Bool.xor(n, m), f)), u1, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, m), u2, v2, rest)),
                          A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), u1, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(Bool.xor(n, m), f), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, u2, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, m), u2, v1, rest),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), u1, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(Bool.xor(n, f), m), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(Bool.xor(n, m), f), u1, v2, rest),
                              Gp.sgn_r(~T, ~add, ~mul, ~neg, ~neg_mul_r, ~neg_neg, p, f, Bool.xor(n, f), u1, m, v2, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, f, f, Bool.xor(Bool.xor(n, f), m), Bool.xor(Bool.xor(n, m), f), u1, v2, rest,
                              {==},
                              F.Flag.sr_a(n, f, m))),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, u2, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, Bool.xor(m, False{})), u2, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, m), u2, v1, rest),
                              Gp.sgn_r(~T, ~add, ~mul, ~neg, ~neg_mul_r, ~neg_neg, p, Bool.not(f), n, u2, Bool.xor(m, False{}), v1, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(f), Bool.xor(n, Bool.xor(m, False{})), Bool.xor(n, m), u2, v1, rest,
                              {==},
                              F.Flag.sr_b(n, m)))),
                          A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), u1, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(Bool.xor(n, m), f)), u1, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, u2, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, m), u2, v2, rest),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), u1, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, v1), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(Bool.not(Bool.xor(n, f)), Bool.xor(m, False{})), u1, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(Bool.xor(n, m), f)), u1, v1, rest),
                              Gp.sgn_r(~T, ~add, ~mul, ~neg, ~neg_mul_r, ~neg_neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), u1, Bool.xor(m, False{}), v1, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(f), Bool.xor(Bool.not(Bool.xor(n, f)), Bool.xor(m, False{})), Bool.not(Bool.xor(Bool.xor(n, m), f)), u1, v1, rest,
                              {==},
                              F.Flag.sr_cn(n, f, m))),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, u2, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, v2), rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, m), u2, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, m), u2, v2, rest),
                              Gp.sgn_r(~T, ~add, ~mul, ~neg, ~neg_mul_r, ~neg_neg, p, f, n, u2, m, v2, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, f, f, Bool.xor(n, m), Bool.xor(n, m), u2, v2, rest,
                              {==},
                              {==}))))

# a grade sign on the left operand joins the flags:
# inv^f((-1)^m inv^g(u)) * v = (-1)^m inv^(f xor g)(u) * v
def Gp.sgn_l(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~neg_mul_l: R.Ring.NegMulL(T, mul, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  +d: Nat, +f: Bool, +n: Bool, +m: Bool, +g: Bool, u: S.MV(T, d), v: S.MV(T, d), +sig: S.Sig(d))
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, S.MV.sgn(~T, ~neg, d, m, g, False{}, u), v, sig) == S.MV.gpf(~T, ~add, ~mul, ~neg, d, Bool.xor(f, g), Bool.xor(n, m), u, v, sig) : S.MV(T, d)}:
  match d:
    case 0n:
      match u:
        case S.LZ{}:
          {==}
        case S.L{+a}:
          match v:
            case S.LZ{}:
              {==}
            case S.L{+b}:
              B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, mul(S.Ring.negf(~T, ~neg, m, a), b)), S.Ring.negf(~T, ~neg, Bool.xor(n, m), mul(a, b)),
                Equal.trans(T, S.Ring.negf(~T, ~neg, n, mul(S.Ring.negf(~T, ~neg, m, a), b)),
                  S.Ring.negf(~T, ~neg, n, S.Ring.negf(~T, ~neg, m, mul(a, b))),
                  S.Ring.negf(~T, ~neg, Bool.xor(n, m), mul(a, b)),
                  Equal.cong(T, T, w => S.Ring.negf(~T, ~neg, n, w), mul(S.Ring.negf(~T, ~neg, m, a), b), S.Ring.negf(~T, ~neg, m, mul(a, b)),
                    L.Negf.mul_l(~T, ~mul, ~neg, ~neg_mul_l, m, a, b)),
                  L.Negf.negf(~T, ~neg, ~neg_neg, n, m, mul(a, b))))
    case 1n+p:
      match u:
        case S.NZ{}:
          {==}
        case S.N{+u1, +u2}:
          match v:
            case S.NZ{}:
              {==}
            case S.N{+v1, +v2}:
              match sig:
                case S.Gen{q, +rest}:
                  match q:
                    case S.QZ{}:
                      Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.xor(n, m), u2, v1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(n, m), u2, v2, rest),
                          A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.xor(n, m), u2, v1, rest),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, Bool.xor(g, False{})), Bool.xor(Bool.xor(n, f), Bool.xor(m, g)), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v2, rest),
                              Gp.sgn_l(~T, ~add, ~mul, ~neg, ~neg_mul_l, ~neg_neg, p, f, Bool.xor(n, f), Bool.xor(m, g), Bool.xor(g, False{}), u1, v2, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.xor(f, Bool.xor(g, False{})), Bool.xor(f, g), Bool.xor(Bool.xor(n, f), Bool.xor(m, g)), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v2, rest,
                              F.Flag.sl_a(f, g),
                              F.Flag.sl_b(n, f, m, g))),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(Bool.not(f), g), Bool.xor(n, m), u2, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.xor(n, m), u2, v1, rest),
                              Gp.sgn_l(~T, ~add, ~mul, ~neg, ~neg_mul_l, ~neg_neg, p, Bool.not(f), n, m, g, u2, v1, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.xor(Bool.not(f), g), Bool.not(Bool.xor(f, g)), Bool.xor(n, m), Bool.xor(n, m), u2, v1, rest,
                              F.Flag.sl_c(f, g),
                              {==}))),
                          Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(n, m), u2, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(n, m), u2, v2, rest),
                            Gp.sgn_l(~T, ~add, ~mul, ~neg, ~neg_mul_l, ~neg_neg, p, f, n, m, g, u2, v2, rest),
                            Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(f, g), Bool.xor(n, m), Bool.xor(n, m), u2, v2, rest,
                            {==},
                            {==})))
                    case S.QP{}:
                      Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.xor(n, m), u2, v1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v2, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(n, m), u2, v2, rest)),
                          A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.xor(n, m), u2, v1, rest),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, Bool.xor(g, False{})), Bool.xor(Bool.xor(n, f), Bool.xor(m, g)), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v2, rest),
                              Gp.sgn_l(~T, ~add, ~mul, ~neg, ~neg_mul_l, ~neg_neg, p, f, Bool.xor(n, f), Bool.xor(m, g), Bool.xor(g, False{}), u1, v2, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.xor(f, Bool.xor(g, False{})), Bool.xor(f, g), Bool.xor(Bool.xor(n, f), Bool.xor(m, g)), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v2, rest,
                              F.Flag.sl_a(f, g),
                              F.Flag.sl_b(n, f, m, g))),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(Bool.not(f), g), Bool.xor(n, m), u2, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.xor(n, m), u2, v1, rest),
                              Gp.sgn_l(~T, ~add, ~mul, ~neg, ~neg_mul_l, ~neg_neg, p, Bool.not(f), n, m, g, u2, v1, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.xor(Bool.not(f), g), Bool.not(Bool.xor(f, g)), Bool.xor(n, m), Bool.xor(n, m), u2, v1, rest,
                              F.Flag.sl_c(f, g),
                              {==}))),
                          A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(n, m), u2, v2, rest),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.xor(n, f), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(Bool.not(f), Bool.xor(g, False{})), Bool.xor(Bool.xor(n, f), Bool.xor(m, g)), u1, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v1, rest),
                              Gp.sgn_l(~T, ~add, ~mul, ~neg, ~neg_mul_l, ~neg_neg, p, Bool.not(f), Bool.xor(n, f), Bool.xor(m, g), Bool.xor(g, False{}), u1, v1, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.xor(Bool.not(f), Bool.xor(g, False{})), Bool.not(Bool.xor(f, g)), Bool.xor(Bool.xor(n, f), Bool.xor(m, g)), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v1, rest,
                              F.Flag.sl_d(f, g),
                              F.Flag.sl_b(n, f, m, g))),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(n, m), u2, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(n, m), u2, v2, rest),
                              Gp.sgn_l(~T, ~add, ~mul, ~neg, ~neg_mul_l, ~neg_neg, p, f, n, m, g, u2, v2, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(f, g), Bool.xor(n, m), Bool.xor(n, m), u2, v2, rest,
                              {==},
                              {==}))))
                    case S.QN{}:
                      Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.xor(n, m), u2, v1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v2, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.not(Bool.xor(Bool.xor(n, m), Bool.xor(f, g))), u1, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(n, m), u2, v2, rest)),
                          A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.xor(n, m), u2, v1, rest),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, Bool.xor(n, f), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, Bool.xor(g, False{})), Bool.xor(Bool.xor(n, f), Bool.xor(m, g)), u1, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v2, rest),
                              Gp.sgn_l(~T, ~add, ~mul, ~neg, ~neg_mul_l, ~neg_neg, p, f, Bool.xor(n, f), Bool.xor(m, g), Bool.xor(g, False{}), u1, v2, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.xor(f, Bool.xor(g, False{})), Bool.xor(f, g), Bool.xor(Bool.xor(n, f), Bool.xor(m, g)), Bool.xor(Bool.xor(n, m), Bool.xor(f, g)), u1, v2, rest,
                              F.Flag.sl_a(f, g),
                              F.Flag.sl_b(n, f, m, g))),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(Bool.not(f), g), Bool.xor(n, m), u2, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.xor(n, m), u2, v1, rest),
                              Gp.sgn_l(~T, ~add, ~mul, ~neg, ~neg_mul_l, ~neg_neg, p, Bool.not(f), n, m, g, u2, v1, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.xor(Bool.not(f), g), Bool.not(Bool.xor(f, g)), Bool.xor(n, m), Bool.xor(n, m), u2, v1, rest,
                              F.Flag.sl_c(f, g),
                              {==}))),
                          A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.not(Bool.xor(Bool.xor(n, m), Bool.xor(f, g))), u1, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(n, m), u2, v2, rest),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), Bool.xor(g, False{}), False{}, u1), v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(Bool.not(f), Bool.xor(g, False{})), Bool.xor(Bool.not(Bool.xor(n, f)), Bool.xor(m, g)), u1, v1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(Bool.xor(f, g)), Bool.not(Bool.xor(Bool.xor(n, m), Bool.xor(f, g))), u1, v1, rest),
                              Gp.sgn_l(~T, ~add, ~mul, ~neg, ~neg_mul_l, ~neg_neg, p, Bool.not(f), Bool.not(Bool.xor(n, f)), Bool.xor(m, g), Bool.xor(g, False{}), u1, v1, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.xor(Bool.not(f), Bool.xor(g, False{})), Bool.not(Bool.xor(f, g)), Bool.xor(Bool.not(Bool.xor(n, f)), Bool.xor(m, g)), Bool.not(Bool.xor(Bool.xor(n, m), Bool.xor(f, g))), u1, v1, rest,
                              F.Flag.sl_d(f, g),
                              F.Flag.sl_e(n, f, m, g))),
                            Equal.trans(S.MV(T, p), S.MV.gpf(~T, ~add, ~mul, ~neg, p, f, n, S.MV.sgn(~T, ~neg, p, m, g, False{}, u2), v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(n, m), u2, v2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(n, m), u2, v2, rest),
                              Gp.sgn_l(~T, ~add, ~mul, ~neg, ~neg_mul_l, ~neg_neg, p, f, n, m, g, u2, v2, rest),
                              Gp.flag(~T, ~add, ~mul, ~neg, p, Bool.xor(f, g), Bool.xor(f, g), Bool.xor(n, m), Bool.xor(n, m), u2, v2, rest,
                              {==},
                              {==}))))
# the sign flag of a product is a grade sign of the product:
# (-1)^m inv^g(y) z = (-1)^m (inv^g(y) z)
def Gp.sign(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~neg_add: R.Ring.NegAdd(T, add, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  +d: Nat, +g: Bool, +m: Bool, y: S.MV(T, d), z: S.MV(T, d), +sig: S.Sig(d))
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, d, g, m, y, z, sig) == S.MV.sgn(~T, ~neg, d, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, d, g, False{}, y, z, sig)) : S.MV(T, d)}:
  match d:
    case 0n:
      match y:
        case S.LZ{}:
          {==}
        case S.L{a}:
          match z:
            case S.LZ{}:
              {==}
            case S.L{b}:
              {==}
    case 1n+p:
      match y:
        case S.NZ{}:
          {==}
        case S.N{+y1, +y2}:
          match z:
            case S.NZ{}:
              {==}
            case S.N{+z1, +z2}:
              match sig:
                case S.Gen{q, +rest}:
                  match q:
                    case S.QZ{}:
                      B.Eq.join(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, Bool.xor(m, g), y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), m, y2, z1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, m, y2, z2, rest)), S.MV.sgn(~T, ~neg, 1n+p, m, False{}, False{}, S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))),
                          Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, Bool.xor(m, g), y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), m, y2, z1, rest)), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, m, y2, z2, rest), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)),
                            A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, Bool.xor(m, g), y1, z2, rest), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), m, y2, z1, rest), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, g, Bool.xor(m, g), y1, z2, rest), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, Bool.not(g), m, y2, z1, rest)),
                            Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, g, m, y2, z2, rest)),
                          Equal.trans(S.MV(T, 1n+p), S.MV.sgn(~T, ~neg, 1n+p, m, False{}, False{}, S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))), S.MV.mk(T, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))),
                            G.Sgn.mk(~T, ~neg, p, m, False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)),
                            Mk.cong(T, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)),
                              Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))),
                                G.Sgn.add(~T, ~add, ~neg, ~neg_add, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)),
                                A.Add.cong(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)),
                                  Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(Bool.xor(m, False{}), g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)),
                                    Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.sgn(~T, ~neg, p, g, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest))), S.MV.sgn(~T, ~neg, p, Bool.xor(Bool.xor(m, False{}), g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)),
                                      G.Sgn.cong(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.sgn(~T, ~neg, p, g, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, g, g, y1, z2, rest)),
                                      G.Sgn.compose(~T, ~neg, ~neg_neg, p, Bool.xor(m, False{}), False{}, False{}, g, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest))),
                                    G.Sgn.flag(~T, ~neg, p, Bool.xor(Bool.xor(m, False{}), g), Bool.xor(m, g), False{}, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest), F.Flag.sg_a(m, g), {==})),
                                  G.Sgn.flag(~T, ~neg, p, Bool.xor(m, False{}), m, False{}, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest), F.Flag.xf(m), {==}))),
                              {==})))
                    case S.QP{}:
                      B.Eq.join(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, Bool.xor(m, g), y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), m, y2, z1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.xor(m, g), y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, m, y2, z2, rest))), S.MV.sgn(~T, ~neg, 1n+p, m, False{}, False{}, S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), g, y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)))),
                          Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, Bool.xor(m, g), y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), m, y2, z1, rest)), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.xor(m, g), y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, m, y2, z2, rest)), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))),
                            A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, Bool.xor(m, g), y1, z2, rest), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), m, y2, z1, rest), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, g, Bool.xor(m, g), y1, z2, rest), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, Bool.not(g), m, y2, z1, rest)),
                            A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.xor(m, g), y1, z1, rest), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, m, y2, z2, rest), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, Bool.not(g), Bool.xor(m, g), y1, z1, rest), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, g, m, y2, z2, rest))),
                          Equal.trans(S.MV(T, 1n+p), S.MV.sgn(~T, ~neg, 1n+p, m, False{}, False{}, S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), g, y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)))), S.MV.mk(T, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), g, y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)))),
                            G.Sgn.mk(~T, ~neg, p, m, False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), g, y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))),
                            Mk.cong(T, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), g, y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))),
                              Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))),
                                G.Sgn.add(~T, ~add, ~neg, ~neg_add, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)),
                                A.Add.cong(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)),
                                  Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(Bool.xor(m, False{}), g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)),
                                    Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.sgn(~T, ~neg, p, g, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest))), S.MV.sgn(~T, ~neg, p, Bool.xor(Bool.xor(m, False{}), g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)),
                                      G.Sgn.cong(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.sgn(~T, ~neg, p, g, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, g, g, y1, z2, rest)),
                                      G.Sgn.compose(~T, ~neg, ~neg_neg, p, Bool.xor(m, False{}), False{}, False{}, g, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest))),
                                    G.Sgn.flag(~T, ~neg, p, Bool.xor(Bool.xor(m, False{}), g), Bool.xor(m, g), False{}, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest), F.Flag.sg_a(m, g), {==})),
                                  G.Sgn.flag(~T, ~neg, p, Bool.xor(m, False{}), m, False{}, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest), F.Flag.xf(m), {==}))),
                              Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), g, y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), g, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))),
                                G.Sgn.add(~T, ~add, ~neg, ~neg_add, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), g, y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)),
                                A.Add.cong(~T, ~add, p, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), g, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)),
                                  Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), g, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)),
                                    Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), g, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.sgn(~T, ~neg, p, g, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest))), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)),
                                      G.Sgn.cong(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), g, y1, z1, rest), S.MV.sgn(~T, ~neg, p, g, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, Bool.not(g), g, y1, z1, rest)),
                                      G.Sgn.compose(~T, ~neg, ~neg_neg, p, m, False{}, False{}, g, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest))),
                                    G.Sgn.flag(~T, ~neg, p, Bool.xor(m, g), Bool.xor(m, g), False{}, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest), {==}, {==})),
                                  {==})))))
                    case S.QN{}:
                      B.Eq.join(S.MV(T, 1n+p), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, Bool.xor(m, g), y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), m, y2, z1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(Bool.xor(m, g)), y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, m, y2, z2, rest))), S.MV.sgn(~T, ~neg, 1n+p, m, False{}, False{}, S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(g), y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.not(Bool.xor(m, g)), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)))),
                          Mk.cong(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, Bool.xor(m, g), y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), m, y2, z1, rest)), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(Bool.xor(m, g)), y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, m, y2, z2, rest)), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.not(Bool.xor(m, g)), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))),
                            A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, Bool.xor(m, g), y1, z2, rest), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), m, y2, z1, rest), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, g, Bool.xor(m, g), y1, z2, rest), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, Bool.not(g), m, y2, z1, rest)),
                            A.Add.cong(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(Bool.xor(m, g)), y1, z1, rest), S.MV.sgn(~T, ~neg, p, Bool.not(Bool.xor(m, g)), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, m, y2, z2, rest), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, Bool.not(g), Bool.not(Bool.xor(m, g)), y1, z1, rest), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, g, m, y2, z2, rest))),
                          Equal.trans(S.MV(T, 1n+p), S.MV.sgn(~T, ~neg, 1n+p, m, False{}, False{}, S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(g), y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)))), S.MV.mk(T, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(g), y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)))), S.MV.mk(T, p, S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.not(Bool.xor(m, g)), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)))),
                            G.Sgn.mk(~T, ~neg, p, m, False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(g), y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))),
                            Mk.cong(T, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(g), y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.not(Bool.xor(m, g)), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))),
                              Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest))),
                                G.Sgn.add(~T, ~add, ~neg, ~neg_add, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)),
                                A.Add.cong(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest)),
                                  Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(Bool.xor(m, False{}), g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)),
                                    Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.sgn(~T, ~neg, p, g, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest))), S.MV.sgn(~T, ~neg, p, Bool.xor(Bool.xor(m, False{}), g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)),
                                      G.Sgn.cong(~T, ~neg, p, Bool.xor(m, False{}), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, g, y1, z2, rest), S.MV.sgn(~T, ~neg, p, g, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest)), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, g, g, y1, z2, rest)),
                                      G.Sgn.compose(~T, ~neg, ~neg_neg, p, Bool.xor(m, False{}), False{}, False{}, g, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest))),
                                    G.Sgn.flag(~T, ~neg, p, Bool.xor(Bool.xor(m, False{}), g), Bool.xor(m, g), False{}, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y1, z2, rest), F.Flag.sg_a(m, g), {==})),
                                  G.Sgn.flag(~T, ~neg, p, Bool.xor(m, False{}), m, False{}, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y2, z1, rest), F.Flag.xf(m), {==}))),
                              Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.add(~T, ~add, p, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(g), y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(g), y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))), S.MV.add(~T, ~add, p, S.MV.sgn(~T, ~neg, p, Bool.not(Bool.xor(m, g)), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest))),
                                G.Sgn.add(~T, ~add, ~neg, ~neg_add, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(g), y1, z1, rest), S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)),
                                A.Add.cong(~T, ~add, p, S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(g), y1, z1, rest)), S.MV.sgn(~T, ~neg, p, Bool.not(Bool.xor(m, g)), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, g, False{}, y2, z2, rest)),
                                  Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(g), y1, z1, rest)), S.MV.sgn(~T, ~neg, p, Bool.xor(m, Bool.not(g)), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), S.MV.sgn(~T, ~neg, p, Bool.not(Bool.xor(m, g)), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)),
                                    Equal.trans(S.MV(T, p), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(g), y1, z1, rest)), S.MV.sgn(~T, ~neg, p, m, False{}, False{}, S.MV.sgn(~T, ~neg, p, Bool.not(g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest))), S.MV.sgn(~T, ~neg, p, Bool.xor(m, Bool.not(g)), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)),
                                      G.Sgn.cong(~T, ~neg, p, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), Bool.not(g), y1, z1, rest), S.MV.sgn(~T, ~neg, p, Bool.not(g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest)), Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, p, Bool.not(g), Bool.not(g), y1, z1, rest)),
                                      G.Sgn.compose(~T, ~neg, ~neg_neg, p, m, False{}, False{}, Bool.not(g), False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest))),
                                    G.Sgn.flag(~T, ~neg, p, Bool.xor(m, Bool.not(g)), Bool.not(Bool.xor(m, g)), False{}, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, p, Bool.not(g), False{}, y1, z1, rest), F.Flag.sg_b(m, g), {==})),
                                  {==})))))

# a sign inside the right operand comes out to the product's flag
def Gp.pull(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T, ~neg_add: R.Ring.NegAdd(T, add, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  ~neg_mul_r: R.Ring.NegMulR(T, mul, neg),
  +d: Nat, +f: Bool, +n: Bool, +x: S.MV(T, d), +g: Bool, +m: Bool, +y: S.MV(T, d), +z: S.MV(T, d), +sig: S.Sig(d))
  -> {S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, S.MV.gpf(~T, ~add, ~mul, ~neg, d, g, m, y, z, sig), sig) == S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, Bool.xor(n, m), x, S.MV.gpf(~T, ~add, ~mul, ~neg, d, g, False{}, y, z, sig), sig) : S.MV(T, d)}:
  Equal.trans(S.MV(T, d), S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, S.MV.gpf(~T, ~add, ~mul, ~neg, d, g, m, y, z, sig), sig), S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, n, x, S.MV.sgn(~T, ~neg, d, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, d, g, False{}, y, z, sig)), sig), S.MV.gpf(~T, ~add, ~mul, ~neg, d, f, Bool.xor(n, m), x, S.MV.gpf(~T, ~add, ~mul, ~neg, d, g, False{}, y, z, sig), sig),
    Gp.cong(~T, ~add, ~mul, ~neg, d, f, n, x, x, S.MV.gpf(~T, ~add, ~mul, ~neg, d, g, m, y, z, sig), S.MV.sgn(~T, ~neg, d, m, False{}, False{}, S.MV.gpf(~T, ~add, ~mul, ~neg, d, g, False{}, y, z, sig)), sig, {==}, Gp.sign(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, d, g, m, y, z, sig)),
    Gp.sgn_r(~T, ~add, ~mul, ~neg, ~neg_mul_r, ~neg_neg, d, f, n, x, m, S.MV.gpf(~T, ~add, ~mul, ~neg, d, g, False{}, y, z, sig), sig))
