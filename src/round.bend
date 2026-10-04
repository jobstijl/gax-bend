# Rounding a dyadic to p significant bits, toward zero: the simplest
# floating-point rounding, with unbounded exponents (no overflow, no
# underflow). proofs/round.bend proves |trunc(x) - x| <= 2^(1-p) |x| for
# p >= 1, the standard model with eps = 2^(1-p) (faithful rounding).
#
# On a magnitude n, Tr.go halves until n < 2^p, keeping n = q 2^s + r and
# witnesses for the invariants the proof needs: 2^s = r + 1 + wr, and, once
# s > 0, q = 2^(p-1) + wq. The result is q 2^s.

import Base
import ./int.bend as I
import ./dyadic.bend as D

def Nat.pow2(k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+j:
      Nat.double(Nat.pow2(j))

def Nat.lt(a: Nat, b: Nat) -> Bool:
  match a b:
    case _ 0n:
      False{}
    case 0n 1n+bp:
      True{}
    case 1n+ap 1n+bp:
      Nat.lt(ap, bp)

# a - b for a >= b
def Nat.monus(a: Nat, b: Nat) -> Nat:
  match a b:
    case a2 0n:
      a2
    case 0n 1n+bp:
      0n
    case 1n+ap 1n+bp:
      Nat.monus(ap, bp)

def Nat.bit(n: Nat) -> Nat:
  Bool.pick(Nat, D.Nat.even(n), 0n, 1n)

type Tr is Data:
  Tr{s: Nat, q: Nat, r: Nat, wr: Nat, wq: Nat}

def Tr.s(t: Tr) -> Nat:
  match t:
    case Tr{s, q, r, wr, wq}:
      s

def Tr.q(t: Tr) -> Nat:
  match t:
    case Tr{s, q, r, wr, wq}:
      q

# one more halving below: n = 2 (q 2^s + r) + b, with n = 2^p + w
def Tr.up(t: Tr, +b: Nat, +w: Nat) -> Tr:
  match t:
    case Tr{+s, q, +r, +wr, wq}:
      Tr{1n+s, q, Nat.add(Nat.double(r), b), Nat.add(Nat.double(wr), Nat.monus(1n, b)), Bool.pick(Nat, Nat.is_eq(s, 0n), D.Nat.half(w), wq)}

def Tr.go(fuel: Nat, +p: Nat, +n: Nat) -> Tr:
  match fuel:
    case 0n:
      Tr{0n, n, 0n, 0n, 0n}
    case 1n+f:
      Bool.pick(Tr, Nat.lt(n, Nat.pow2(p)), Tr{0n, n, 0n, 0n, 0n},
        Tr.up(Tr.go(f, p, D.Nat.half(n)), Nat.bit(n), Nat.monus(n, Nat.pow2(p))))

def Tr.of(+p: Nat, +n: Nat) -> Tr:
  Tr.go(n, p, n)

# q 2^s
def Tr.val(t: Tr) -> Nat:
  match t:
    case Tr{s, q, r, wr, wq}:
      Nat.mul(q, Nat.pow2(s))

def Int.mag(a: I.Int) -> Nat:
  match a:
    case I.IPos{n}:
      n
    case I.INeg{n}:
      1n+n

# the same sign as a, magnitude m
def Int.signed(a: I.Int, m: Nat) -> I.Int:
  match a:
    case I.IPos{n}:
      I.IPos{m}
    case I.INeg{n}:
      I.Int.neg(I.IPos{m})

# x to p significant bits, toward zero
def Dy.trunc(+p: Nat, +x: D.Dy) -> D.Dy:
  D.Dy.of(D.Dy.den(x), Int.signed(D.Dy.num(x), Tr.val(Tr.of(p, Int.mag(D.Dy.num(x))))))

# the operations of p-bit truncating arithmetic
def Dy.radd(p: Nat, x: D.Dy, y: D.Dy) -> D.Dy:
  Dy.trunc(p, D.Dy.add(x, y))

def Dy.rmul(p: Nat, x: D.Dy, y: D.Dy) -> D.Dy:
  Dy.trunc(p, D.Dy.mul(x, y))

# Round to nearest, ties to even: from the truncation n = q 2^s + r, round
# up when 2r > 2^s, or 2r = 2^s and q is odd. proofs/round.bend proves
# |rne(x) - x| <= 2^-p |x| (the standard model with eps = 2^-p, IEEE's u).
def Tr.rup(t: Tr) -> Bool:
  match t:
    case Tr{+s, q, +r, wr, wq}:
      Bool.and(Bool.not(Nat.lt(Nat.double(r), Nat.pow2(s))), Bool.or(Nat.lt(Nat.pow2(s), Nat.double(r)), Bool.not(D.Nat.even(q))))

# the rounded magnitude: q 2^s, or (q + 1) 2^s
def Tr.near(+t: Tr) -> Nat:
  Bool.pick(Nat, Tr.rup(t), Nat.mul(1n+Tr.q(t), Nat.pow2(Tr.s(t))), Nat.mul(Tr.q(t), Nat.pow2(Tr.s(t))))

def Dy.rne(+p: Nat, +x: D.Dy) -> D.Dy:
  D.Dy.of(D.Dy.den(x), Int.signed(D.Dy.num(x), Tr.near(Tr.of(p, Int.mag(D.Dy.num(x))))))

def Dy.nadd(p: Nat, x: D.Dy, y: D.Dy) -> D.Dy:
  Dy.rne(p, D.Dy.add(x, y))

def Dy.nmul(p: Nat, x: D.Dy, y: D.Dy) -> D.Dy:
  Dy.rne(p, D.Dy.mul(x, y))
