# The executable binary32 spec. src/dyadic.bend and src/round.bend define
# halving, parity, comparison and subtraction by recursion, which the
# proofs need, but which take n steps at run time. Here the same functions
# use Base's native Nat operations, and proofs/fast.bend proves each equal
# to its recursive original. So Dy.f32f computes Dy.f32 and is fast.
#
# Run-time Nat is capped at 2^48 - 1 (bend-facts Q16): products of two
# binary32 significands fit; sums fit when the exponents differ by at most
# 23 (Dy.addaf aligns to the larger denominator only); the range test
# computes 2^(d - 126), so denominators stay at most 2^173.

import Base
import ./int.bend as I
import ./dyadic.bend as D
import ./round.bend as RD

# Primitives
# ----------

def Nat.halff(n: Nat) -> Nat:
  Nat.div(n, 2n)

def Nat.evenf(n: Nat) -> Bool:
  Nat.is_eq(Nat.mod(n, 2n), 0n)

def Nat.ltf(a: Nat, b: Nat) -> Bool:
  Nat.is_lt(a, b)

def Nat.monusf(a: Nat, b: Nat) -> Nat:
  Nat.sub(a, b)

def Nat.bitf(n: Nat) -> Nat:
  Bool.pick(Nat, Nat.evenf(n), 0n, 1n)

def Int.evenf(a: I.Int) -> Bool:
  match a:
    case I.IPos{n}:
      Nat.evenf(n)
    case I.INeg{n}:
      Bool.not(Nat.evenf(n))

def Int.halff(a: I.Int) -> I.Int:
  match a:
    case I.IPos{n}:
      I.IPos{Nat.halff(n)}
    case I.INeg{n}:
      I.INeg{Nat.halff(n)}

# m - k for naturals
def Int.sub_natf(+m: Nat, +k: Nat) -> I.Int:
  Bool.pick(I.Int, Nat.ltf(m, k), I.INeg{Nat.monusf(Nat.monusf(k, m), 1n)}, I.IPos{Nat.monusf(m, k)})

def Int.addf(a: I.Int, b: I.Int) -> I.Int:
  match a b:
    case I.IPos{m} I.IPos{n}:
      I.IPos{Nat.add(m, n)}
    case I.INeg{m} I.INeg{n}:
      I.INeg{1n+Nat.add(m, n)}
    case I.IPos{m} I.INeg{n}:
      Int.sub_natf(m, 1n+n)
    case I.INeg{m} I.IPos{n}:
      Int.sub_natf(n, 1n+m)

# Dyadics
# -------

def Dy.oddf(m: I.Int, f: Nat) -> D.Dy:
  match m:
    case I.IPos{n}:
      D.DFrac{False{}, Nat.halff(n), f}
    case I.INeg{n}:
      D.DFrac{True{}, Nat.halff(n), f}

# Dy.of, as a match on the parity (not a pick: its recursion runs once)
def Dy.off.go(e: Nat, +m: I.Int, ev: Bool) -> D.Dy:
  match e:
    case 0n:
      D.DInt{m}
    case 1n+f:
      match ev:
        case True{}:
          Dy.off.go(f, Int.halff(m), Int.evenf(Int.halff(m)))
        case False{}:
          Dy.oddf(m, f)

def Dy.off(+e: Nat, +m: I.Int) -> D.Dy:
  Dy.off.go(e, m, Int.evenf(m))

def Dy.mulf(+x: D.Dy, +y: D.Dy) -> D.Dy:
  Dy.off(Nat.add(D.Dy.den(x), D.Dy.den(y)), I.Int.mul(D.Dy.num(x), D.Dy.num(y)))

# a sum over the larger denominator: m1 / 2^e1 + m2 / 2^e2 with e1 <= e2 is
# (m1 2^(e2 - e1) + m2) / 2^e2
def Dy.addaf(+x: D.Dy, +y: D.Dy) -> D.Dy:
  Bool.pick(D.Dy, Nat.ltf(D.Dy.den(y), D.Dy.den(x)),
    Dy.off(D.Dy.den(x), Int.addf(D.Dy.num(x), D.Int.sh(Nat.monusf(D.Dy.den(x), D.Dy.den(y)), D.Dy.num(y)))),
    Dy.off(D.Dy.den(y), Int.addf(D.Int.sh(Nat.monusf(D.Dy.den(y), D.Dy.den(x)), D.Dy.num(x)), D.Dy.num(y))))

# Rounding
# --------

def Tr.upf(t: RD.Tr, +b: Nat, +w: Nat) -> RD.Tr:
  match t:
    case RD.Tr{+s, q, +r, +wr, wq}:
      RD.Tr{1n+s, q, Nat.add(Nat.double(r), b), Nat.add(Nat.double(wr), Nat.monusf(1n, b)), Bool.pick(Nat, Nat.is_eq(s, 0n), Nat.halff(w), wq)}

def Tr.gof(fuel: Nat, +p: Nat, +n: Nat, lt: Bool) -> RD.Tr:
  match fuel:
    case 0n:
      RD.Tr{0n, n, 0n, 0n, 0n}
    case 1n+f:
      match lt:
        case True{}:
          RD.Tr{0n, n, 0n, 0n, 0n}
        case False{}:
          Tr.upf(Tr.gof(f, p, Nat.halff(n), Nat.ltf(Nat.halff(n), RD.Nat.pow2(p))), Nat.bitf(n), Nat.monusf(n, RD.Nat.pow2(p)))

def Tr.off(+p: Nat, +n: Nat) -> RD.Tr:
  Tr.gof(n, p, n, Nat.ltf(n, RD.Nat.pow2(p)))

def Tr.rupf(t: RD.Tr) -> Bool:
  match t:
    case RD.Tr{+s, q, +r, wr, wq}:
      Bool.and(Bool.not(Nat.ltf(Nat.double(r), RD.Nat.pow2(s))), Bool.or(Nat.ltf(RD.Nat.pow2(s), Nat.double(r)), Bool.not(Nat.evenf(q))))

def Tr.nearf(+t: RD.Tr) -> Nat:
  Bool.pick(Nat, Tr.rupf(t), Nat.mul(1n+RD.Tr.q(t), RD.Nat.pow2(RD.Tr.s(t))), Nat.mul(RD.Tr.q(t), RD.Nat.pow2(RD.Tr.s(t))))

def Fx.gof(s: Nat, +n: Nat) -> RD.Tr:
  match s:
    case 0n:
      RD.Tr{0n, n, 0n, 0n, 0n}
    case 1n+j:
      Tr.upf(Fx.gof(j, Nat.halff(n)), Nat.bitf(n), 0n)

def Dy.rnef(+p: Nat, +x: D.Dy) -> D.Dy:
  Dy.off(D.Dy.den(x), RD.Int.signed(D.Dy.num(x), Tr.nearf(Tr.off(p, RD.Int.mag(D.Dy.num(x))))))

def Dy.rfixf(+k: Nat, +x: D.Dy) -> D.Dy:
  Bool.pick(D.Dy, Nat.ltf(k, D.Dy.den(x)),
    Dy.off(D.Dy.den(x), RD.Int.signed(D.Dy.num(x), Tr.nearf(Fx.gof(Nat.monusf(D.Dy.den(x), k), RD.Int.mag(D.Dy.num(x)))))),
    x)

def Dy.bigf(+x: D.Dy) -> Bool:
  Bool.pick(Bool, Nat.ltf(126n, D.Dy.den(x)), Bool.not(Nat.ltf(RD.Int.mag(D.Dy.num(x)), RD.Nat.pow2(Nat.monusf(D.Dy.den(x), 126n)))), True{})

def Dy.flf(+p: Nat, +k: Nat, big: Bool, +x: D.Dy) -> D.Dy:
  match big:
    case True{}:
      Dy.rnef(p, x)
    case False{}:
      Dy.rfixf(k, x)

def Dy.f32f(+x: D.Dy) -> D.Dy:
  Dy.flf(24n, 149n, Dy.bigf(x), x)
