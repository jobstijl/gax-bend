# Truncation to p significant bits satisfies the standard model with
# eps = 2^(1-p) (src/round.bend):
#   |trunc(x) - x| <= 2^(1-p) |x|.
#
# On a magnitude n the loop keeps n = q 2^s + r, 2^s = r + 1 + wr and, once
# it has shifted, q = 2^(p-1) + wq (Inv). From these, n = r 2^(p-1) + c for
# an explicit c (Tr.c), an identity the normaliser checks at T = Int on
# naturals embedded as nonnegative integers. So r 2^(p-1) <= n, which is
# the bound.

import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/round.bend as RD
import ../src/norm.bend as N
import ./nat.bend as NL
import ./int.bend as Z
import ./dyadic.bend as Y
import ./equiv.bend as EQ
import ./norm.bend as NP

# Naturals
# --------

def Nat.lt_f(+a: Nat, +b: Nat) -> {RD.Nat.lt(a, b) == False{} : Bool} -> {a == Nat.add(b, RD.Nat.monus(a, b)) : Nat}:
  match a b:
    case a2 0n:
      e => {==}
    case 0n 1n+bp:
      e => Empty.absurd({0n == Nat.add(1n+bp, 0n) : Nat}, Z.Bool.ft(Equal.sym(Bool, True{}, False{}, e)))
    case 1n+ap 1n+bp:
      e => Equal.cong(Nat, Nat, x => 1n+x, ap, Nat.add(bp, RD.Nat.monus(ap, bp)), Nat.lt_f(ap, bp)(e))

def Nat.double_hom(+a: Nat, +b: Nat) -> {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 2n+x, Nat.double(Nat.add(p, b)), Nat.add(Nat.double(p), Nat.double(b)), Nat.double_hom(p, b))

# n = double(half n) + bit n
def Nat.split2(+n: Nat) -> {n == Nat.add(Nat.double(D.Nat.half(n)), RD.Nat.bit(n)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          Equal.cong(Nat, Nat, x => 2n+x, q, Nat.add(Nat.double(D.Nat.half(q)), RD.Nat.bit(q)), Nat.split2(q))

# half(double a + w) = a + half w
def Nat.half_dw(+a: Nat, +w: Nat) -> {D.Nat.half(Nat.add(Nat.double(a), w)) == Nat.add(a, D.Nat.half(w)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, D.Nat.half(Nat.add(Nat.double(p), w)), Nat.add(p, D.Nat.half(w)), Nat.half_dw(p, w))

def Nat.bit01(+n: Nat) -> {Nat.add(RD.Nat.bit(n), RD.Nat.monus(1n, RD.Nat.bit(n))) == 1n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          Nat.bit01(q)

# Naturals as integers
# --------------------

def Ip.mul(+a: Nat, +b: Nat) -> {I.Int.mul(I.IPos{a}, I.IPos{b}) == I.IPos{Nat.mul(a, b)} : I.Int}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Ip.inj(-a: Nat, -b: Nat, e: {I.IPos{a} == I.IPos{b} : I.Int}) -> {a == b : Nat}:
  Equal.cong(I.Int, Nat, x => Y.Int.mag(x), I.IPos{a}, I.IPos{b}, e)

def Ip.eq(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {I.IPos{a} == I.IPos{b} : I.Int}:
  Equal.cong(Nat, I.Int, x => I.IPos{x}, a, b, e)

# The loop's invariant
# --------------------

def Inv(pp: Nat, n: Nat, t: RD.Tr) -> Type:
  match t:
    case RD.Tr{s, q, r, wr, wq}:
      match s:
        case 0n:
          {n == q : Nat} & ({r == 0n : Nat} & {wr == 0n : Nat})
        case 1n+s1:
          {n == Nat.add(Nat.mul(q, RD.Nat.pow2(1n+s1)), r) : Nat} & ({RD.Nat.pow2(1n+s1) == Nat.add(Nat.add(r, 1n), wr) : Nat} & {q == Nat.add(pp, wq) : Nat})

def Nat.mul2(+q: Nat) -> {Nat.mul(q, 2n) == Nat.double(q) : Nat}:
  Equal.trans(Nat, Nat.mul(q, 2n), Nat.add(q, Nat.mul(q, 1n)), Nat.double(q), NL.Nat.mul_succ_r(q, 1n),
    Equal.trans(Nat, Nat.add(q, Nat.mul(q, 1n)), Nat.add(q, q), Nat.double(q),
      Equal.cong(Nat, Nat, x => Nat.add(q, x), Nat.mul(q, 1n), q, NL.Nat.mul_one_r(q)),
      Equal.sym(Nat, Nat.double(q), Nat.add(q, q), Y.Nat.double_add(q))))

def Nat.mul_double(+q: Nat, +s: Nat) -> {Nat.mul(q, Nat.double(s)) == Nat.double(Nat.mul(q, s)) : Nat}:
  Equal.trans(Nat, Nat.mul(q, Nat.double(s)), Nat.mul(q, Nat.add(s, s)), Nat.double(Nat.mul(q, s)),
    Equal.cong(Nat, Nat, x => Nat.mul(q, x), Nat.double(s), Nat.add(s, s), Y.Nat.double_add(s)),
    Equal.trans(Nat, Nat.mul(q, Nat.add(s, s)), Nat.add(Nat.mul(q, s), Nat.mul(q, s)), Nat.double(Nat.mul(q, s)),
      NL.Nat.mul_dist_l(q, s, s),
      Equal.sym(Nat, Nat.double(Nat.mul(q, s)), Nat.add(Nat.mul(q, s), Nat.mul(q, s)), Y.Nat.double_add(Nat.mul(q, s)))))

# (x + y) + 1 + z with x + z' = 1 reorders: (a + b) + 1 + (c + m) = a + c + 2 when b + m = 1
def Nat.reord(+a: Nat, +b: Nat, +c: Nat, +m: Nat, h: {Nat.add(b, m) == 1n : Nat})
  -> {Nat.add(Nat.add(Nat.add(a, b), 1n), Nat.add(c, m)) == Nat.add(Nat.add(a, 2n), c) : Nat}:
  +l1 = Nat.add(Nat.add(Nat.add(a, b), 1n), Nat.add(c, m))
  +l2 = Nat.add(Nat.add(a, Nat.add(b, 1n)), Nat.add(c, m))
  +l3 = Nat.add(a, Nat.add(Nat.add(b, 1n), Nat.add(c, m)))
  +l4 = Nat.add(a, Nat.add(Nat.add(b, m), Nat.add(1n, c)))
  +l5 = Nat.add(a, Nat.add(1n, Nat.add(1n, c)))
  Equal.trans(Nat, l1, l2, Nat.add(Nat.add(a, 2n), c),
    Equal.cong(Nat, Nat, x => Nat.add(x, Nat.add(c, m)), Nat.add(Nat.add(a, b), 1n), Nat.add(a, Nat.add(b, 1n)), NL.Nat.add_assoc(a, b, 1n)),
    Equal.trans(Nat, l2, l3, Nat.add(Nat.add(a, 2n), c), NL.Nat.add_assoc(a, Nat.add(b, 1n), Nat.add(c, m)),
      Equal.trans(Nat, l3, l4, Nat.add(Nat.add(a, 2n), c),
        Equal.cong(Nat, Nat, x => Nat.add(a, x), Nat.add(Nat.add(b, 1n), Nat.add(c, m)), Nat.add(Nat.add(b, m), Nat.add(1n, c)),
          Equal.trans(Nat, Nat.add(Nat.add(b, 1n), Nat.add(c, m)), Nat.add(Nat.add(b, 1n), Nat.add(m, c)), Nat.add(Nat.add(b, m), Nat.add(1n, c)),
            Equal.cong(Nat, Nat, x => Nat.add(Nat.add(b, 1n), x), Nat.add(c, m), Nat.add(m, c), NL.Nat.add_comm(c, m)),
            NL.Nat.add_4(b, 1n, m, c))),
        Equal.trans(Nat, l4, l5, Nat.add(Nat.add(a, 2n), c),
          Equal.cong(Nat, Nat, x => Nat.add(a, Nat.add(x, Nat.add(1n, c))), Nat.add(b, m), 1n, h),
          Equal.sym(Nat, Nat.add(Nat.add(a, 2n), c), l5, NL.Nat.add_assoc(a, 2n, c))))))

# one halving keeps the invariant
def Up.inv(+pp: Nat, +n: Nat, +b: Nat, +w: Nat, t: RD.Tr, ih: Inv(pp, D.Nat.half(n), t),
  hn: {n == Nat.add(Nat.double(D.Nat.half(n)), b) : Nat}, hw: {D.Nat.half(n) == Nat.add(pp, D.Nat.half(w)) : Nat}, hb: {Nat.add(b, RD.Nat.monus(1n, b)) == 1n : Nat})
  -> Inv(pp, n, RD.Tr.up(t, b, w)):
  match t:
    case RD.Tr{+s, +q, +r, +wr, +wq}:
      match s:
        case 0n:
          (e1x, (e2x, e3)) = ih
          +e1 = e1x
          +e2 = e2x
          +m = RD.Nat.monus(1n, b)
          +ea = Equal.trans(Nat, n, Nat.add(Nat.double(q), b), Nat.add(Nat.mul(q, 2n), Nat.add(Nat.double(r), b)),
            Equal.trans(Nat, n, Nat.add(Nat.double(D.Nat.half(n)), b), Nat.add(Nat.double(q), b), hn,
              Equal.cong(Nat, Nat, x => Nat.add(Nat.double(x), b), D.Nat.half(n), q, e1)),
            Z.Nat.cong2(Nat.double(q), Nat.mul(q, 2n), b, Nat.add(Nat.double(r), b), Equal.sym(Nat, Nat.mul(q, 2n), Nat.double(q), Nat.mul2(q)),
              Equal.cong(Nat, Nat, x => Nat.add(Nat.double(x), b), 0n, r, Equal.sym(Nat, r, 0n, e2))))
          +eb = Equal.sym(Nat, Nat.add(Nat.add(Nat.add(Nat.double(r), b), 1n), Nat.add(Nat.double(wr), m)), 2n,
            Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.double(r), b), 1n), Nat.add(Nat.double(wr), m)), Nat.add(Nat.add(Nat.double(r), 2n), Nat.double(wr)), 2n,
              Nat.reord(Nat.double(r), b, Nat.double(wr), m, hb),
              Equal.trans(Nat, Nat.add(Nat.add(Nat.double(r), 2n), Nat.double(wr)), Nat.add(Nat.add(0n, 2n), 0n), 2n,
                Z.Nat.cong2(Nat.add(Nat.double(r), 2n), Nat.add(0n, 2n), Nat.double(wr), 0n,
                  Equal.cong(Nat, Nat, x => Nat.add(Nat.double(x), 2n), r, 0n, e2),
                  Equal.cong(Nat, Nat, x => Nat.double(x), wr, 0n, e3)),
                {==})))
          +ec = Equal.trans(Nat, q, D.Nat.half(n), Nat.add(pp, D.Nat.half(w)), Equal.sym(Nat, D.Nat.half(n), q, e1), hw)
          (ea, (eb, ec))
        case 1n+s1:
          (e1, (e2, e3)) = ih
          +m = RD.Nat.monus(1n, b)
          +sv = RD.Nat.pow2(1n+s1)
          +ea = Equal.trans(Nat, n, Nat.add(Nat.double(Nat.add(Nat.mul(q, sv), r)), b), Nat.add(Nat.mul(q, Nat.double(sv)), Nat.add(Nat.double(r), b)),
            Equal.trans(Nat, n, Nat.add(Nat.double(D.Nat.half(n)), b), Nat.add(Nat.double(Nat.add(Nat.mul(q, sv), r)), b), hn,
              Equal.cong(Nat, Nat, x => Nat.add(Nat.double(x), b), D.Nat.half(n), Nat.add(Nat.mul(q, sv), r), e1)),
            Equal.trans(Nat, Nat.add(Nat.double(Nat.add(Nat.mul(q, sv), r)), b), Nat.add(Nat.add(Nat.double(Nat.mul(q, sv)), Nat.double(r)), b), Nat.add(Nat.mul(q, Nat.double(sv)), Nat.add(Nat.double(r), b)),
              Equal.cong(Nat, Nat, x => Nat.add(x, b), Nat.double(Nat.add(Nat.mul(q, sv), r)), Nat.add(Nat.double(Nat.mul(q, sv)), Nat.double(r)), Nat.double_hom(Nat.mul(q, sv), r)),
              Equal.trans(Nat, Nat.add(Nat.add(Nat.double(Nat.mul(q, sv)), Nat.double(r)), b), Nat.add(Nat.double(Nat.mul(q, sv)), Nat.add(Nat.double(r), b)), Nat.add(Nat.mul(q, Nat.double(sv)), Nat.add(Nat.double(r), b)),
                NL.Nat.add_assoc(Nat.double(Nat.mul(q, sv)), Nat.double(r), b),
                Equal.cong(Nat, Nat, x => Nat.add(x, Nat.add(Nat.double(r), b)), Nat.double(Nat.mul(q, sv)), Nat.mul(q, Nat.double(sv)), Equal.sym(Nat, Nat.mul(q, Nat.double(sv)), Nat.double(Nat.mul(q, sv)), Nat.mul_double(q, sv))))))
          +eb = Equal.trans(Nat, Nat.double(sv), Nat.double(Nat.add(Nat.add(r, 1n), wr)), Nat.add(Nat.add(Nat.add(Nat.double(r), b), 1n), Nat.add(Nat.double(wr), m)),
            Equal.cong(Nat, Nat, x => Nat.double(x), sv, Nat.add(Nat.add(r, 1n), wr), e2),
            Equal.trans(Nat, Nat.double(Nat.add(Nat.add(r, 1n), wr)), Nat.add(Nat.add(Nat.double(r), 2n), Nat.double(wr)), Nat.add(Nat.add(Nat.add(Nat.double(r), b), 1n), Nat.add(Nat.double(wr), m)),
              Equal.trans(Nat, Nat.double(Nat.add(Nat.add(r, 1n), wr)), Nat.add(Nat.double(Nat.add(r, 1n)), Nat.double(wr)), Nat.add(Nat.add(Nat.double(r), 2n), Nat.double(wr)),
                Nat.double_hom(Nat.add(r, 1n), wr),
                Equal.cong(Nat, Nat, x => Nat.add(x, Nat.double(wr)), Nat.double(Nat.add(r, 1n)), Nat.add(Nat.double(r), 2n), Nat.double_hom(r, 1n))),
              Equal.sym(Nat, Nat.add(Nat.add(Nat.add(Nat.double(r), b), 1n), Nat.add(Nat.double(wr), m)), Nat.add(Nat.add(Nat.double(r), 2n), Nat.double(wr)), Nat.reord(Nat.double(r), b, Nat.double(wr), m, hb))))
          (ea, (eb, e3))

# the loop keeps the invariant, whatever its fuel
def Inv.go(+fuel: Nat, +p1: Nat, +n: Nat, lt: Bool, +el: {RD.Nat.lt(n, RD.Nat.pow2(1n+p1)) == lt : Bool}) -> Inv(RD.Nat.pow2(p1), n, RD.Tr.go(fuel, 1n+p1, n)):
  match fuel:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+f:
      match lt:
        case True{}:
          +pp = RD.Nat.pow2(p1)
          +y = RD.Tr.up(RD.Tr.go(f, 1n+p1, D.Nat.half(n)), RD.Nat.bit(n), RD.Nat.monus(n, RD.Nat.pow2(1n+p1)))
          %Equal.sym(Bool, RD.Nat.lt(n, RD.Nat.pow2(1n+p1)), True{}, el) : Inv(pp, n, Bool.pick(RD.Tr, _, RD.Tr{0n, n, 0n, 0n, 0n}, y))
          ({==}, ({==}, {==}))
        case False{}:
          +pp = RD.Nat.pow2(p1)
          +y = RD.Tr.up(RD.Tr.go(f, 1n+p1, D.Nat.half(n)), RD.Nat.bit(n), RD.Nat.monus(n, RD.Nat.pow2(1n+p1)))
          +w = RD.Nat.monus(n, RD.Nat.pow2(1n+p1))
          +hw = Equal.trans(Nat, D.Nat.half(n), D.Nat.half(Nat.add(Nat.double(pp), w)), Nat.add(pp, D.Nat.half(w)),
            Equal.cong(Nat, Nat, x => D.Nat.half(x), n, Nat.add(Nat.double(pp), w), Nat.lt_f(n, RD.Nat.pow2(1n+p1))(el)),
            Nat.half_dw(pp, w))
          %Equal.sym(Bool, RD.Nat.lt(n, RD.Nat.pow2(1n+p1)), False{}, el) : Inv(pp, n, Bool.pick(RD.Tr, _, RD.Tr{0n, n, 0n, 0n, 0n}, y))
          Up.inv(pp, n, RD.Nat.bit(n), w, RD.Tr.go(f, 1n+p1, D.Nat.half(n)),
            Inv.go(f, p1, D.Nat.half(n), RD.Nat.lt(D.Nat.half(n), RD.Nat.pow2(1n+p1)), {==}),
            Nat.split2(n), hw, Nat.bit01(n))

def Inv.of(+p1: Nat, +n: Nat) -> Inv(RD.Nat.pow2(p1), n, RD.Tr.of(1n+p1, n)):
  Inv.go(n, p1, n, RD.Nat.lt(n, RD.Nat.pow2(1n+p1)), {==})

def Tr.r(t: RD.Tr) -> Nat:
  match t:
    case RD.Tr{s, q, r, wr, wq}:
      r

# the slack: n = r 2^(p-1) + c
def Tr.c(+pp: Nat, +n: Nat, t: RD.Tr) -> Nat:
  match t:
    case RD.Tr{s, q, +r, wr, wq}:
      match s:
        case 0n:
          n
        case 1n+s1:
          Nat.add(Nat.add(Nat.mul(pp, Nat.add(1n, wr)), Nat.mul(wq, RD.Nat.pow2(1n+s1))), r)

def V(i: Nat) -> N.Tm:
  N.TVar{i}

def Ml(a: N.Tm, b: N.Tm) -> N.Tm:
  N.TMul{a, b}

def Ad(a: N.Tm, b: N.Tm) -> N.Tm:
  N.TAdd{a, b}

def Ng(a: N.Tm) -> N.Tm:
  N.TNeg{a}

def Int.rz(+a: I.Int, +b: I.Int, e: {a == b : I.Int}) -> {I.Int.add(a, I.Int.neg(b)) == I.IPos{0n} : I.Int}:
  Equal.trans(I.Int, I.Int.add(a, I.Int.neg(b)), I.Int.add(b, I.Int.neg(b)), I.IPos{0n}, Equal.cong(I.Int, I.Int, w => I.Int.add(w, I.Int.neg(b)), a, b, e), Z.Int.add_inv(b))

# n = val + r, and n = r 2^(p-1) + c
def Err.nat(+pp: Nat, +n: Nat, +t: RD.Tr, inv: Inv(pp, n, t))
  -> {n == Nat.add(RD.Tr.val(t), Tr.r(t)) : Nat} & {n == Nat.add(Nat.mul(Tr.r(t), pp), Tr.c(pp, n, t)) : Nat}:
  match t:
    case RD.Tr{+s, +q, +r, +wr, +wq}:
      match s:
        case 0n:
          (e1x, (e2x, e3)) = inv
          +e1 = e1x
          +e2 = e2x
          (Equal.trans(Nat, n, q, Nat.add(Nat.mul(q, 1n), r), e1,
             Equal.sym(Nat, Nat.add(Nat.mul(q, 1n), r), q,
               Equal.trans(Nat, Nat.add(Nat.mul(q, 1n), r), Nat.add(q, 0n), q,
                 Z.Nat.cong2(Nat.mul(q, 1n), q, r, 0n, NL.Nat.mul_one_r(q), e2), NL.Nat.add_zero_r(q)))),
           Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(x, pp), n), 0n, r, Equal.sym(Nat, r, 0n, e2)))
        case 1n+s1:
          (e1x, (e2x, e3x)) = inv
          +e1 = e1x
          +sv = RD.Nat.pow2(1n+s1)
          +qs = Nat.add(Nat.mul(q, sv), r)
          +c = Nat.add(Nat.add(Nat.mul(pp, Nat.add(1n, wr)), Nat.mul(wq, sv)), r)
          +env : List<&2, I.Int> = [I.IPos{n}, I.IPos{q}, I.IPos{r}, I.IPos{wr}, I.IPos{wq}, I.IPos{pp}, I.IPos{sv}, I.IPos{1n}]
          +r2 = Ad(V(6n), Ng(Ad(Ad(V(2n), V(7n)), V(3n))))
          +r3 = Ad(V(1n), Ng(Ad(V(5n), V(4n))))
          +z2 = Int.rz(I.IPos{sv}, I.Int.add(I.Int.add(I.IPos{r}, I.IPos{1n}), I.IPos{wr}), Ip.eq(sv, Nat.add(Nat.add(r, 1n), wr), e2x))
          +z3 = Int.rz(I.IPos{q}, I.Int.add(I.IPos{pp}, I.IPos{wq}), Ip.eq(q, Nat.add(pp, wq), e3x))
          +ei = EQ.Rel.many(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg,
            env, Ad(Ml(V(1n), V(6n)), V(2n)), Ad(Ml(V(2n), V(5n)), Ad(Ad(Ml(V(5n), Ad(V(7n), V(3n))), Ml(V(4n), V(6n))), V(2n))), [V(6n), V(5n)], [r3, r2], {==}, (z3, (z2, Unit{})))
          # read the Int identity back as naturals
          +lhs = Equal.trans(I.Int, I.IPos{qs}, I.Int.add(I.Int.mul(I.IPos{q}, I.IPos{sv}), I.IPos{r}), I.IPos{Nat.add(Nat.mul(r, pp), c)},
            Equal.cong(I.Int, I.Int, x => I.Int.add(x, I.IPos{r}), I.IPos{Nat.mul(q, sv)}, I.Int.mul(I.IPos{q}, I.IPos{sv}), Equal.sym(I.Int, I.Int.mul(I.IPos{q}, I.IPos{sv}), I.IPos{Nat.mul(q, sv)}, Ip.mul(q, sv))),
            Equal.trans(I.Int, I.Int.add(I.Int.mul(I.IPos{q}, I.IPos{sv}), I.IPos{r}), I.Int.add(I.Int.mul(I.IPos{r}, I.IPos{pp}), I.Int.add(I.Int.add(I.Int.mul(I.IPos{pp}, I.Int.add(I.IPos{1n}, I.IPos{wr})), I.Int.mul(I.IPos{wq}, I.IPos{sv})), I.IPos{r})), I.IPos{Nat.add(Nat.mul(r, pp), c)},
              ei,
              Equal.cong(I.Int, I.Int, x => x, I.Int.add(I.Int.mul(I.IPos{r}, I.IPos{pp}), I.Int.add(I.Int.add(I.Int.mul(I.IPos{pp}, I.Int.add(I.IPos{1n}, I.IPos{wr})), I.Int.mul(I.IPos{wq}, I.IPos{sv})), I.IPos{r})), I.IPos{Nat.add(Nat.mul(r, pp), c)},
                Equal.trans(I.Int, I.Int.add(I.Int.mul(I.IPos{r}, I.IPos{pp}), I.Int.add(I.Int.add(I.Int.mul(I.IPos{pp}, I.Int.add(I.IPos{1n}, I.IPos{wr})), I.Int.mul(I.IPos{wq}, I.IPos{sv})), I.IPos{r})),
                  I.Int.add(I.IPos{Nat.mul(r, pp)}, I.Int.add(I.Int.add(I.IPos{Nat.mul(pp, Nat.add(1n, wr))}, I.IPos{Nat.mul(wq, sv)}), I.IPos{r})), I.IPos{Nat.add(Nat.mul(r, pp), c)},
                  Y.Int.cong2(I.Int.mul(I.IPos{r}, I.IPos{pp}), I.IPos{Nat.mul(r, pp)}, I.Int.add(I.Int.add(I.Int.mul(I.IPos{pp}, I.Int.add(I.IPos{1n}, I.IPos{wr})), I.Int.mul(I.IPos{wq}, I.IPos{sv})), I.IPos{r}), I.Int.add(I.Int.add(I.IPos{Nat.mul(pp, Nat.add(1n, wr))}, I.IPos{Nat.mul(wq, sv)}), I.IPos{r}),
                    Ip.mul(r, pp),
                    Equal.cong(I.Int, I.Int, x => I.Int.add(x, I.IPos{r}), I.Int.add(I.Int.mul(I.IPos{pp}, I.Int.add(I.IPos{1n}, I.IPos{wr})), I.Int.mul(I.IPos{wq}, I.IPos{sv})), I.Int.add(I.IPos{Nat.mul(pp, Nat.add(1n, wr))}, I.IPos{Nat.mul(wq, sv)}),
                      Y.Int.cong2(I.Int.mul(I.IPos{pp}, I.Int.add(I.IPos{1n}, I.IPos{wr})), I.IPos{Nat.mul(pp, Nat.add(1n, wr))}, I.Int.mul(I.IPos{wq}, I.IPos{sv}), I.IPos{Nat.mul(wq, sv)}, Ip.mul(pp, Nat.add(1n, wr)), Ip.mul(wq, sv)))),
                  {==}))))
          (e1, Equal.trans(Nat, n, qs, Nat.add(Nat.mul(r, pp), c), e1, Ip.inj(qs, Nat.add(Nat.mul(r, pp), c), lhs)))

# The dyadic statement
# --------------------

# (a / 2^e1)(b / 2^e2) = a b / 2^(e1 + e2)
def Mul.of(+e1: Nat, +e2: Nat, +a: I.Int, +b: I.Int) -> {D.Dy.mul(D.Dy.of(e1, a), D.Dy.of(e2, b)) == D.Dy.of(Nat.add(e1, e2), I.Int.mul(a, b)) : D.Dy}:
  +u = D.Dy.of(e1, a)
  +w = D.Dy.of(e2, b)
  +nu = D.Dy.num(u)
  +du = D.Dy.den(u)
  +nw = D.Dy.num(w)
  +dw = D.Dy.den(w)
  +env : List<&2, I.Int> = [a, b, nu, nw, Y.P(e1), Y.P(e2), Y.P(du), Y.P(dw)]
  +r1 = Ad(Ml(V(2n), V(4n)), Ng(Ml(V(0n), V(6n))))
  +r2 = Ad(Ml(V(3n), V(5n)), Ng(Ml(V(1n), V(7n))))
  +z1 = Int.rz(I.Int.mul(nu, Y.P(e1)), I.Int.mul(a, Y.P(du)), Y.Of.valP(e1, a))
  +z2 = Int.rz(I.Int.mul(nw, Y.P(e2)), I.Int.mul(b, Y.P(dw)), Y.Of.valP(e2, b))
  +h = EQ.Rel.many(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg,
    env, Ml(Ml(V(2n), V(3n)), Ml(V(4n), V(5n))), Ml(Ml(V(0n), V(1n)), Ml(V(6n), V(7n))), [Ml(V(3n), V(5n)), Ml(V(0n), V(6n))], [r1, r2], {==}, (z1, (z2, Unit{})))
  Y.Of.eqvP(Nat.add(du, dw), Nat.add(e1, e2), I.Int.mul(nu, nw), I.Int.mul(a, b),
    Equal.trans(I.Int, I.Int.mul(I.Int.mul(nu, nw), Y.P(Nat.add(e1, e2))), I.Int.mul(I.Int.mul(nu, nw), I.Int.mul(Y.P(e1), Y.P(e2))), I.Int.mul(I.Int.mul(a, b), Y.P(Nat.add(du, dw))),
      Equal.cong(I.Int, I.Int, x => I.Int.mul(I.Int.mul(nu, nw), x), Y.P(Nat.add(e1, e2)), I.Int.mul(Y.P(e1), Y.P(e2)), Y.P.add(e1, e2)),
      Equal.trans(I.Int, I.Int.mul(I.Int.mul(nu, nw), I.Int.mul(Y.P(e1), Y.P(e2))), I.Int.mul(I.Int.mul(a, b), I.Int.mul(Y.P(du), Y.P(dw))), I.Int.mul(I.Int.mul(a, b), Y.P(Nat.add(du, dw))), h,
        Equal.cong(I.Int, I.Int, x => I.Int.mul(I.Int.mul(a, b), x), I.Int.mul(Y.P(du), Y.P(dw)), Y.P(Nat.add(du, dw)), Equal.sym(I.Int, Y.P(Nat.add(du, dw)), I.Int.mul(Y.P(du), Y.P(dw)), Y.P.add(du, dw))))))

def Int.abs_mag(+n: I.Int) -> {I.Int.abs(n) == I.IPos{RD.Int.mag(n)} : I.Int}:
  match n:
    case I.IPos{k}:
      {==}
    case I.INeg{k}:
      {==}

def Sg.abs(+n: I.Int, +r: Nat) -> {I.Int.abs(RD.Int.signed(n, r)) == I.IPos{r} : I.Int}:
  match n:
    case I.IPos{k}:
      {==}
    case I.INeg{k}:
      Z.Int.abs_neg(I.IPos{r})

# signed(n, v) - n = -signed(n, r) when |n| = v + r
def Sg.diff(+n: I.Int, +v: Nat, +r: Nat, h: {RD.Int.mag(n) == Nat.add(v, r) : Nat}) -> {I.Int.add(RD.Int.signed(n, v), I.Int.neg(n)) == I.Int.neg(RD.Int.signed(n, r)) : I.Int}:
  match n:
    case I.IPos{k}:
      %Equal.sym(Nat, k, Nat.add(v, r), h) : {I.Int.add(I.IPos{v}, I.Int.neg(I.IPos{_})) == I.Int.neg(I.IPos{r}) : I.Int}
      NP.Norm.eq(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg,
        [I.IPos{v}, I.IPos{r}], Ad(V(0n), Ng(Ad(V(0n), V(1n)))), Ng(V(1n)), {==})
    case I.INeg{k}:
      Equal.trans(I.Int, I.Int.add(I.Int.neg(I.IPos{v}), I.IPos{1n+k}), I.Int.add(I.Int.neg(I.IPos{v}), I.IPos{Nat.add(v, r)}), I.Int.neg(I.Int.neg(I.IPos{r})),
        Equal.cong(Nat, I.Int, x => I.Int.add(I.Int.neg(I.IPos{v}), I.IPos{x}), 1n+k, Nat.add(v, r), h),
        NP.Norm.eq(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg,
          [I.IPos{v}, I.IPos{r}], Ad(Ng(V(0n)), Ad(V(0n), V(1n))), Ng(Ng(V(1n))), {==}))

def Sh.ipos(+k: Nat, +r: Nat) -> {D.Int.sh(k, I.IPos{r}) == I.IPos{Nat.mul(r, RD.Nat.pow2(k))} : I.Int}:
  match k:
    case 0n:
      Equal.cong(Nat, I.Int, x => I.IPos{x}, r, Nat.mul(r, 1n), Equal.sym(Nat, Nat.mul(r, 1n), r, NL.Nat.mul_one_r(r)))
    case 1n+j:
      Equal.trans(I.Int, D.Int.dbl(D.Int.sh(j, I.IPos{r})), D.Int.dbl(I.IPos{Nat.mul(r, RD.Nat.pow2(j))}), I.IPos{Nat.mul(r, Nat.double(RD.Nat.pow2(j)))},
        Equal.cong(I.Int, I.Int, x => D.Int.dbl(x), D.Int.sh(j, I.IPos{r}), I.IPos{Nat.mul(r, RD.Nat.pow2(j))}, Sh.ipos(j, r)),
        Equal.cong(Nat, I.Int, x => I.IPos{x}, Nat.double(Nat.mul(r, RD.Nat.pow2(j))), Nat.mul(r, Nat.double(RD.Nat.pow2(j))), Equal.sym(Nat, Nat.mul(r, Nat.double(RD.Nat.pow2(j))), Nat.double(Nat.mul(r, RD.Nat.pow2(j))), Nat.mul_double(r, RD.Nat.pow2(j)))))

# |trunc(z) - z| <= 2^(1-p) |z|, with p = 1 + p1
def Round.rel.go(+p1: Nat, +z: D.Dy,
  en: {RD.Int.mag(D.Dy.num(z)) == Nat.add(RD.Tr.val(RD.Tr.of(1n+p1, RD.Int.mag(D.Dy.num(z)))), Tr.r(RD.Tr.of(1n+p1, RD.Int.mag(D.Dy.num(z))))) : Nat}
    & {RD.Int.mag(D.Dy.num(z)) == Nat.add(Nat.mul(Tr.r(RD.Tr.of(1n+p1, RD.Int.mag(D.Dy.num(z)))), RD.Nat.pow2(p1)), Tr.c(RD.Nat.pow2(p1), RD.Int.mag(D.Dy.num(z)), RD.Tr.of(1n+p1, RD.Int.mag(D.Dy.num(z))))) : Nat})
  -> {D.Dy.pos(D.Dy.add(D.Dy.mul(D.Dy.ulp(p1), D.Dy.abs(z)), D.Dy.neg(D.Dy.abs(D.Dy.add(RD.Dy.trunc(1n+p1, z), D.Dy.neg(z)))))) == True{} : Bool}:
  (en1x, en2x) = en
  +n = D.Dy.num(z)
  +d = D.Dy.den(z)
  +m = RD.Int.mag(n)
  +t = RD.Tr.of(1n+p1, m)
  +v = RD.Tr.val(t)
  +r = Tr.r(t)
  +pp = RD.Nat.pow2(p1)
  +c = Tr.c(pp, m, t)
  +e = Nat.add(p1, d)
  +en1 = en1x
  +tz = RD.Dy.trunc(1n+p1, z)
  +sv = RD.Int.signed(n, v)
  +sr = RD.Int.signed(n, r)
  +nz = Equal.trans(D.Dy, D.Dy.neg(z), D.Dy.neg(D.Dy.of(d, n)), D.Dy.of(d, I.Int.neg(n)),
    Equal.cong(D.Dy, D.Dy, w => D.Dy.neg(w), z, D.Dy.of(d, n), Equal.sym(D.Dy, D.Dy.of(d, n), z, Y.Of.self(z))),
    Y.Of.neg(d, n))
  # |trunc z - z| = r / 2^d
  +sa = Equal.trans(D.Dy, D.Dy.add(tz, D.Dy.neg(z)), D.Dy.add(D.Dy.of(d, sv), D.Dy.of(d, I.Int.neg(n))), D.Dy.of(d, I.Int.neg(sr)),
    Y.Dy.cong2(tz, D.Dy.of(d, sv), D.Dy.neg(z), D.Dy.of(d, I.Int.neg(n)), {==}, nz),
    Equal.trans(D.Dy, D.Dy.add(D.Dy.of(d, sv), D.Dy.of(d, I.Int.neg(n))), D.Dy.of(d, I.Int.add(sv, I.Int.neg(n))), D.Dy.of(d, I.Int.neg(sr)),
      Y.Add.of(d, sv, I.Int.neg(n)),
      Y.Of.cong(d, d, I.Int.add(sv, I.Int.neg(n)), I.Int.neg(sr), {==}, Sg.diff(n, v, r, en1))))
  +stepa = Equal.trans(D.Dy, D.Dy.abs(D.Dy.add(tz, D.Dy.neg(z))), D.Dy.abs(D.Dy.of(d, I.Int.neg(sr))), D.Dy.of(d, I.IPos{r}),
    Equal.cong(D.Dy, D.Dy, w => D.Dy.abs(w), D.Dy.add(tz, D.Dy.neg(z)), D.Dy.of(d, I.Int.neg(sr)), sa),
    Equal.trans(D.Dy, D.Dy.abs(D.Dy.of(d, I.Int.neg(sr))), D.Dy.of(d, I.Int.abs(I.Int.neg(sr))), D.Dy.of(d, I.IPos{r}),
      Y.Abs.of(d, I.Int.neg(sr)),
      Y.Of.cong(d, d, I.Int.abs(I.Int.neg(sr)), I.IPos{r}, {==}, Equal.trans(I.Int, I.Int.abs(I.Int.neg(sr)), I.Int.abs(sr), I.IPos{r}, Z.Int.abs_neg(sr), Sg.abs(n, r)))))
  # 2^(1-p) |z| = m / 2^(p1 + d)
  +az = Equal.trans(D.Dy, D.Dy.abs(z), D.Dy.abs(D.Dy.of(d, n)), D.Dy.of(d, I.IPos{m}),
    Equal.cong(D.Dy, D.Dy, w => D.Dy.abs(w), z, D.Dy.of(d, n), Equal.sym(D.Dy, D.Dy.of(d, n), z, Y.Of.self(z))),
    Equal.trans(D.Dy, D.Dy.abs(D.Dy.of(d, n)), D.Dy.of(d, I.Int.abs(n)), D.Dy.of(d, I.IPos{m}), Y.Abs.of(d, n), Y.Of.cong(d, d, I.Int.abs(n), I.IPos{m}, {==}, Int.abs_mag(n))))
  +stepb = Equal.trans(D.Dy, D.Dy.mul(D.Dy.ulp(p1), D.Dy.abs(z)), D.Dy.mul(D.Dy.of(p1, I.IPos{1n}), D.Dy.of(d, I.IPos{m})), D.Dy.of(e, I.IPos{m}),
    Equal.cong(D.Dy, D.Dy, w => D.Dy.mul(D.Dy.of(p1, I.IPos{1n}), w), D.Dy.abs(z), D.Dy.of(d, I.IPos{m}), az),
    Equal.trans(D.Dy, D.Dy.mul(D.Dy.of(p1, I.IPos{1n}), D.Dy.of(d, I.IPos{m})), D.Dy.of(e, I.Int.mul(I.IPos{1n}, I.IPos{m})), D.Dy.of(e, I.IPos{m}),
      Mul.of(p1, d, I.IPos{1n}, I.IPos{m}),
      Y.Of.cong(e, e, I.Int.mul(I.IPos{1n}, I.IPos{m}), I.IPos{m}, {==}, Y.Int.one_l(I.IPos{m}))))
  # -(r / 2^d) = -(r 2^p1) / 2^(p1 + d)
  +nr = I.Int.neg(I.IPos{r})
  +stepc = Equal.trans(D.Dy, D.Dy.neg(D.Dy.of(d, I.IPos{r})), D.Dy.of(d, nr), D.Dy.of(e, D.Int.sh(p1, nr)),
    Y.Of.neg(d, I.IPos{r}),
    Equal.trans(D.Dy, D.Dy.of(d, nr), D.Dy.of(Nat.add(d, p1), D.Int.sh(p1, nr)), D.Dy.of(e, D.Int.sh(p1, nr)),
      Equal.sym(D.Dy, D.Dy.of(Nat.add(d, p1), D.Int.sh(p1, nr)), D.Dy.of(d, nr), Y.Of.shift(p1, d, nr)),
      Y.Of.cong(Nat.add(d, p1), e, D.Int.sh(p1, nr), D.Int.sh(p1, nr), NL.Nat.add_comm(d, p1), {==})))
  +mm = I.Int.add(I.IPos{m}, D.Int.sh(p1, nr))
  +stepd = Equal.trans(D.Dy, D.Dy.add(D.Dy.mul(D.Dy.ulp(p1), D.Dy.abs(z)), D.Dy.neg(D.Dy.abs(D.Dy.add(tz, D.Dy.neg(z))))), D.Dy.add(D.Dy.of(e, I.IPos{m}), D.Dy.of(e, D.Int.sh(p1, nr))), D.Dy.of(e, mm),
    Y.Dy.cong2(D.Dy.mul(D.Dy.ulp(p1), D.Dy.abs(z)), D.Dy.of(e, I.IPos{m}), D.Dy.neg(D.Dy.abs(D.Dy.add(tz, D.Dy.neg(z)))), D.Dy.of(e, D.Int.sh(p1, nr)), stepb,
      Equal.trans(D.Dy, D.Dy.neg(D.Dy.abs(D.Dy.add(tz, D.Dy.neg(z)))), D.Dy.neg(D.Dy.of(d, I.IPos{r})), D.Dy.of(e, D.Int.sh(p1, nr)),
        Equal.cong(D.Dy, D.Dy, w => D.Dy.neg(w), D.Dy.abs(D.Dy.add(tz, D.Dy.neg(z))), D.Dy.of(d, I.IPos{r}), stepa), stepc)),
    Y.Add.of(e, I.IPos{m}, D.Int.sh(p1, nr)))
  # the numerator is (c + r 2^p1) - r 2^p1
  +rp = Nat.mul(r, pp)
  +em = Equal.trans(I.Int, mm, I.Int.add(I.IPos{Nat.add(c, rp)}, I.Int.neg(I.IPos{rp})), I.Int.add(I.IPos{Nat.add(c, rp)}, I.Int.neg(I.IPos{rp})),
    Y.Int.cong2(I.IPos{m}, I.IPos{Nat.add(c, rp)}, D.Int.sh(p1, nr), I.Int.neg(I.IPos{rp}),
      Ip.eq(m, Nat.add(c, rp), Equal.trans(Nat, m, Nat.add(rp, c), Nat.add(c, rp), en2x, NL.Nat.add_comm(rp, c))),
      Equal.trans(I.Int, D.Int.sh(p1, nr), I.Int.neg(D.Int.sh(p1, I.IPos{r})), I.Int.neg(I.IPos{rp}), Y.Int.sh_neg(p1, I.IPos{r}),
        Equal.cong(I.Int, I.Int, w => I.Int.neg(w), D.Int.sh(p1, I.IPos{r}), I.IPos{rp}, Sh.ipos(p1, r)))),
    {==})
  Equal.trans(Bool, D.Dy.pos(D.Dy.add(D.Dy.mul(D.Dy.ulp(p1), D.Dy.abs(z)), D.Dy.neg(D.Dy.abs(D.Dy.add(tz, D.Dy.neg(z)))))), D.Dy.pos(D.Dy.of(e, mm)), True{},
    Equal.cong(D.Dy, Bool, w => D.Dy.pos(w), D.Dy.add(D.Dy.mul(D.Dy.ulp(p1), D.Dy.abs(z)), D.Dy.neg(D.Dy.abs(D.Dy.add(tz, D.Dy.neg(z))))), D.Dy.of(e, mm), stepd),
    Equal.trans(Bool, D.Dy.pos(D.Dy.of(e, mm)), I.Int.pos(mm), True{}, Y.Pos.of(e, mm),
      Equal.trans(Bool, I.Int.pos(mm), I.Int.pos(I.Int.add(I.IPos{Nat.add(c, rp)}, I.Int.neg(I.IPos{rp}))), True{},
        Equal.cong(I.Int, Bool, w => I.Int.pos(w), mm, I.Int.add(I.IPos{Nat.add(c, rp)}, I.Int.neg(I.IPos{rp})), em),
        Z.Pos.diff(c, rp))))

def Round.rel(+p1: Nat, +z: D.Dy) -> {D.Dy.pos(D.Dy.add(D.Dy.mul(D.Dy.ulp(p1), D.Dy.abs(z)), D.Dy.neg(D.Dy.abs(D.Dy.add(RD.Dy.trunc(1n+p1, z), D.Dy.neg(z)))))) == True{} : Bool}:
  Round.rel.go(p1, z, Err.nat(RD.Nat.pow2(p1), RD.Int.mag(D.Dy.num(z)), RD.Tr.of(1n+p1, RD.Int.mag(D.Dy.num(z))), Inv.of(p1, RD.Int.mag(D.Dy.num(z)))))

# The instance: p-bit truncating arithmetic satisfies the standard model
def Round.add_ok(p1: Nat, x: D.Dy, y: D.Dy) -> {D.Dy.pos(D.Dy.add(D.Dy.mul(D.Dy.ulp(p1), D.Dy.abs(D.Dy.add(x, y))), D.Dy.neg(D.Dy.abs(D.Dy.add(RD.Dy.radd(1n+p1, x, y), D.Dy.neg(D.Dy.add(x, y))))))) == True{} : Bool}:
  Round.rel(p1, D.Dy.add(x, y))

def Round.mul_ok(p1: Nat, x: D.Dy, y: D.Dy) -> {D.Dy.pos(D.Dy.add(D.Dy.mul(D.Dy.ulp(p1), D.Dy.abs(D.Dy.mul(x, y))), D.Dy.neg(D.Dy.abs(D.Dy.add(RD.Dy.rmul(1n+p1, x, y), D.Dy.neg(D.Dy.mul(x, y))))))) == True{} : Bool}:
  Round.rel(p1, D.Dy.mul(x, y))

def Round.eps_pos(+p1: Nat) -> {D.Dy.pos(D.Dy.ulp(p1)) == True{} : Bool}:
  Y.Pos.of(p1, I.IPos{1n})
