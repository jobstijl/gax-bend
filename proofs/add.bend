# Addition of multivectors: zero laws, commutativity, associativity, the
# rearrangements the product proofs need, and how addition passes through
# the collapsing constructor MV.mk.

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S
import ./base.bend as B

def Add.zero_l(~T: Data, ~add: T -> T -> T, d: Nat, y: S.MV(T, d))
  -> {S.MV.add(~T, ~add, d, S.MV.zero(T, d), y) == y : S.MV(T, d)}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Add.zero_r(~T: Data, ~add: T -> T -> T, d: Nat, x: S.MV(T, d))
  -> {S.MV.add(~T, ~add, d, x, S.MV.zero(T, d)) == x : S.MV(T, d)}:
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

def Add.comm(~T: Data, ~add: T -> T -> T, ~add_comm: R.Ring.Comm(T, add), +d: Nat, x: S.MV(T, d), y: S.MV(T, d))
  -> {S.MV.add(~T, ~add, d, x, y) == S.MV.add(~T, ~add, d, y, x) : S.MV(T, d)}:
  match d:
    case 0n:
      match x y:
        case S.LZ{} S.LZ{}:
          {==}
        case S.LZ{} S.L{b}:
          {==}
        case S.L{a} S.LZ{}:
          {==}
        case S.L{a} S.L{b}:
          B.Leaf.cong(T, add(a, b), add(b, a), add_comm(a, b))
    case 1n+p:
      match x y:
        case S.NZ{} S.NZ{}:
          {==}
        case S.NZ{} S.N{b1, b2}:
          {==}
        case S.N{a1, a2} S.NZ{}:
          {==}
        case S.N{a1, a2} S.N{b1, b2}:
          B.Node.cong2(S.MV(T, p),
            S.MV.add(~T, ~add, p, a1, b1), S.MV.add(~T, ~add, p, b1, a1),
            S.MV.add(~T, ~add, p, a2, b2), S.MV.add(~T, ~add, p, b2, a2),
            Add.comm(~T, ~add, ~add_comm, p, a1, b1), Add.comm(~T, ~add, ~add_comm, p, a2, b2))

def Add.assoc(~T: Data, ~add: T -> T -> T, ~add_assoc: R.Ring.Assoc(T, add), +d: Nat,
  x: S.MV(T, d), y: S.MV(T, d), z: S.MV(T, d))
  -> {S.MV.add(~T, ~add, d, S.MV.add(~T, ~add, d, x, y), z) == S.MV.add(~T, ~add, d, x, S.MV.add(~T, ~add, d, y, z)) : S.MV(T, d)}:
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
                  B.Leaf.cong(T, add(add(a, b), c), add(a, add(b, c)), add_assoc(a, b, c))
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
                  B.Node.cong2(S.MV(T, p),
                    S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, a1, b1), c1), S.MV.add(~T, ~add, p, a1, S.MV.add(~T, ~add, p, b1, c1)),
                    S.MV.add(~T, ~add, p, S.MV.add(~T, ~add, p, a2, b2), c2), S.MV.add(~T, ~add, p, a2, S.MV.add(~T, ~add, p, b2, c2)),
                    Add.assoc(~T, ~add, ~add_assoc, p, a1, b1, c1), Add.assoc(~T, ~add, ~add_assoc, p, a2, b2, c2))

# congruence in both arguments
def Add.cong(~T: Data, ~add: T -> T -> T, -d: Nat, -a: S.MV(T, d), -a2: S.MV(T, d), -b: S.MV(T, d), -b2: S.MV(T, d),
  ea: {a == a2 : S.MV(T, d)}, eb: {b == b2 : S.MV(T, d)})
  -> {S.MV.add(~T, ~add, d, a, b) == S.MV.add(~T, ~add, d, a2, b2) : S.MV(T, d)}:
  %ea : {S.MV.add(~T, ~add, d, a, b) == S.MV.add(~T, ~add, d, _, b2) : S.MV(T, d)}
  %eb : {S.MV.add(~T, ~add, d, a, b) == S.MV.add(~T, ~add, d, a, _) : S.MV(T, d)}
  {==}

# (a + b) + (c + e) = (a + c) + (b + e)
def Add.swap4(~T: Data, ~add: T -> T -> T, ~add_assoc: R.Ring.Assoc(T, add), ~add_comm: R.Ring.Comm(T, add), +d: Nat,
  +a: S.MV(T, d), +b: S.MV(T, d), +c: S.MV(T, d), +e: S.MV(T, d))
  -> {S.MV.add(~T, ~add, d, S.MV.add(~T, ~add, d, a, b), S.MV.add(~T, ~add, d, c, e))
      == S.MV.add(~T, ~add, d, S.MV.add(~T, ~add, d, a, c), S.MV.add(~T, ~add, d, b, e)) : S.MV(T, d)}:
  +bc = S.MV.add(~T, ~add, d, b, c)
  +cb = S.MV.add(~T, ~add, d, c, b)
  +ce = S.MV.add(~T, ~add, d, c, e)
  +be = S.MV.add(~T, ~add, d, b, e)
  # (a + b) + (c + e) = a + (b + (c + e))
  s1 = Add.assoc(~T, ~add, ~add_assoc, d, a, b, ce)
  # b + (c + e) = (b + c) + e = (c + b) + e = c + (b + e)
  i1 = Equal.sym(S.MV(T, d), S.MV.add(~T, ~add, d, bc, e), S.MV.add(~T, ~add, d, b, ce), Add.assoc(~T, ~add, ~add_assoc, d, b, c, e))
  i2 = Add.cong(~T, ~add, d, bc, cb, e, e, Add.comm(~T, ~add, ~add_comm, d, b, c), {==})
  i3 = Add.assoc(~T, ~add, ~add_assoc, d, c, b, e)
  inner = Equal.trans(S.MV(T, d), S.MV.add(~T, ~add, d, b, ce), S.MV.add(~T, ~add, d, cb, e), S.MV.add(~T, ~add, d, c, be),
    Equal.trans(S.MV(T, d), S.MV.add(~T, ~add, d, b, ce), S.MV.add(~T, ~add, d, bc, e), S.MV.add(~T, ~add, d, cb, e), i1, i2), i3)
  s2 = Add.cong(~T, ~add, d, a, a, S.MV.add(~T, ~add, d, b, ce), S.MV.add(~T, ~add, d, c, be), {==}, inner)
  # a + (c + (b + e)) = (a + c) + (b + e)
  s3 = Equal.sym(S.MV(T, d), S.MV.add(~T, ~add, d, S.MV.add(~T, ~add, d, a, c), be), S.MV.add(~T, ~add, d, a, S.MV.add(~T, ~add, d, c, be)),
    Add.assoc(~T, ~add, ~add_assoc, d, a, c, be))
  Equal.trans(S.MV(T, d),
    S.MV.add(~T, ~add, d, S.MV.add(~T, ~add, d, a, b), ce),
    S.MV.add(~T, ~add, d, a, S.MV.add(~T, ~add, d, c, be)),
    S.MV.add(~T, ~add, d, S.MV.add(~T, ~add, d, a, c), be),
    Equal.trans(S.MV(T, d),
      S.MV.add(~T, ~add, d, S.MV.add(~T, ~add, d, a, b), ce),
      S.MV.add(~T, ~add, d, a, S.MV.add(~T, ~add, d, b, ce)),
      S.MV.add(~T, ~add, d, a, S.MV.add(~T, ~add, d, c, be)), s1, s2),
    s3)

# (a + b) + (c + e) = (c + a) + (b + e)
def Add.rot4(~T: Data, ~add: T -> T -> T, ~add_assoc: R.Ring.Assoc(T, add), ~add_comm: R.Ring.Comm(T, add), +d: Nat,
  +a: S.MV(T, d), +b: S.MV(T, d), +c: S.MV(T, d), +e: S.MV(T, d))
  -> {S.MV.add(~T, ~add, d, S.MV.add(~T, ~add, d, a, b), S.MV.add(~T, ~add, d, c, e))
      == S.MV.add(~T, ~add, d, S.MV.add(~T, ~add, d, c, a), S.MV.add(~T, ~add, d, b, e)) : S.MV(T, d)}:
  +ac = S.MV.add(~T, ~add, d, a, c)
  +ca = S.MV.add(~T, ~add, d, c, a)
  +be = S.MV.add(~T, ~add, d, b, e)
  Equal.trans(S.MV(T, d),
    S.MV.add(~T, ~add, d, S.MV.add(~T, ~add, d, a, b), S.MV.add(~T, ~add, d, c, e)),
    S.MV.add(~T, ~add, d, ac, be),
    S.MV.add(~T, ~add, d, ca, be),
    Add.swap4(~T, ~add, ~add_assoc, ~add_comm, d, a, b, c, e),
    Add.cong(~T, ~add, d, ac, ca, be, be, Add.comm(~T, ~add, ~add_comm, d, a, c), {==}))

# addition passes through the collapsing constructor
def Add.mk(~T: Data, ~add: T -> T -> T, +d: Nat, a: S.MV(T, d), b: S.MV(T, d), c: S.MV(T, d), e: S.MV(T, d))
  -> {S.MV.add(~T, ~add, 1n+d, S.MV.mk(T, d, a, b), S.MV.mk(T, d, c, e))
      == S.MV.mk(T, d, S.MV.add(~T, ~add, d, a, c), S.MV.add(~T, ~add, d, b, e)) : S.MV(T, 1n+d)}:
  match d:
    case 0n:
      match a:
        case S.LZ{}:
          match b:
            case S.LZ{}:
              {==}
            case S.L{y}:
              match c:
                case S.LZ{}:
                  match e:
                    case S.LZ{}:
                      {==}
                    case S.L{w}:
                      {==}
                case S.L{v}:
                  {==}
        case S.L{x}:
          match c:
            case S.LZ{}:
              match e:
                case S.LZ{}:
                  %Equal.sym(S.MV(T, 0n), S.MV.add(~T, ~add, 0n, b, S.LZ{}), b, Add.zero_r(~T, ~add, 0n, b))
                    : {S.N{S.L{x}, b} == S.N{S.L{x}, _} : S.MV(T, 1n)}
                  {==}
                case S.L{w}:
                  {==}
            case S.L{v}:
              {==}
    case 1n+p:
      match a:
        case S.NZ{}:
          match b:
            case S.NZ{}:
              {==}
            case S.N{b1, b2}:
              match c:
                case S.NZ{}:
                  match e:
                    case S.NZ{}:
                      {==}
                    case S.N{e1, e2}:
                      {==}
                case S.N{c1, c2}:
                  {==}
        case S.N{a1, a2}:
          match c:
            case S.NZ{}:
              match e:
                case S.NZ{}:
                  %Equal.sym(S.MV(T, 1n+p), S.MV.add(~T, ~add, 1n+p, b, S.NZ{}), b, Add.zero_r(~T, ~add, 1n+p, b))
                    : {S.N{S.N{a1, a2}, b} == S.N{S.N{a1, a2}, _} : S.MV(T, 2n+p)}
                  {==}
                case S.N{e1, e2}:
                  {==}
            case S.N{c1, c2}:
              {==}
