# The executable binary32 spec computes the proven one (src/fast.bend):
# each fast function equals its recursive original, from the four links
# between Base's native Nat operations and the recursive halving, parity,
# comparison and subtraction the proofs use.

import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/round.bend as RD
import ../src/fast.bend as F
import ./nat.bend as NL
import ./int.bend as Z
import ./dyadic.bend as Y
import ./round.bend as R

# Primitives
# ----------

def L.lt(+a: Nat, +b: Nat) -> {RD.Nat.lt(a, b) == F.Nat.ltf(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+ap 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      L.lt(ap, bp)

def L.monus(+a: Nat, +b: Nat) -> {RD.Nat.monus(a, b) == F.Nat.monusf(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+ap 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      L.monus(ap, bp)

# Base's division by 2 runs Nat.divmod.go between two states; in both, the
# quotient grows as half and the remainder follows the parity
def Dm(+n: Nat, +d: Nat) -> ({Pair.fst(Nat, Nat, Nat.divmod.go(n, 1n, d, 0n)) == Nat.add(d, D.Nat.half(n)) : Nat} & {Pair.fst(Nat, Nat, Nat.divmod.go(n, 0n, d, 1n)) == Nat.add(d, D.Nat.half(1n+n)) : Nat}) & ({Pair.snd(Nat, Nat, Nat.divmod.go(n, 1n, d, 0n)) == RD.Nat.bit(n) : Nat} & {Pair.snd(Nat, Nat, Nat.divmod.go(n, 0n, d, 1n)) == RD.Nat.bit(1n+n) : Nat}):
  match n:
    case 0n:
      ((Equal.sym(Nat, Nat.add(d, 0n), d, NL.Nat.add_zero_r(d)), Equal.sym(Nat, Nat.add(d, 0n), d, NL.Nat.add_zero_r(d))), ({==}, {==}))
    case 1n+np:
      ((Pair.snd({Pair.fst(Nat, Nat, Nat.divmod.go(np, 1n, d, 0n)) == Nat.add(d, D.Nat.half(np)) : Nat}, {Pair.fst(Nat, Nat, Nat.divmod.go(np, 0n, d, 1n)) == Nat.add(d, D.Nat.half(1n+np)) : Nat}, Pair.fst({Pair.fst(Nat, Nat, Nat.divmod.go(np, 1n, d, 0n)) == Nat.add(d, D.Nat.half(np)) : Nat} & {Pair.fst(Nat, Nat, Nat.divmod.go(np, 0n, d, 1n)) == Nat.add(d, D.Nat.half(1n+np)) : Nat}, {Pair.snd(Nat, Nat, Nat.divmod.go(np, 1n, d, 0n)) == RD.Nat.bit(np) : Nat} & {Pair.snd(Nat, Nat, Nat.divmod.go(np, 0n, d, 1n)) == RD.Nat.bit(1n+np) : Nat}, Dm(np, d))),
        Equal.trans(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(np, 1n, 1n+d, 0n)), Nat.add(1n+d, D.Nat.half(np)), Nat.add(d, D.Nat.half(2n+np)),
          Pair.fst({Pair.fst(Nat, Nat, Nat.divmod.go(np, 1n, 1n+d, 0n)) == Nat.add(1n+d, D.Nat.half(np)) : Nat}, {Pair.fst(Nat, Nat, Nat.divmod.go(np, 0n, 1n+d, 1n)) == Nat.add(1n+d, D.Nat.half(1n+np)) : Nat}, Pair.fst({Pair.fst(Nat, Nat, Nat.divmod.go(np, 1n, 1n+d, 0n)) == Nat.add(1n+d, D.Nat.half(np)) : Nat} & {Pair.fst(Nat, Nat, Nat.divmod.go(np, 0n, 1n+d, 1n)) == Nat.add(1n+d, D.Nat.half(1n+np)) : Nat}, {Pair.snd(Nat, Nat, Nat.divmod.go(np, 1n, 1n+d, 0n)) == RD.Nat.bit(np) : Nat} & {Pair.snd(Nat, Nat, Nat.divmod.go(np, 0n, 1n+d, 1n)) == RD.Nat.bit(1n+np) : Nat}, Dm(np, 1n+d))),
          Equal.sym(Nat, Nat.add(d, 1n+D.Nat.half(np)), 1n+Nat.add(d, D.Nat.half(np)), NL.Nat.add_succ_r(d, D.Nat.half(np))))),
       (Pair.snd({Pair.snd(Nat, Nat, Nat.divmod.go(np, 1n, d, 0n)) == RD.Nat.bit(np) : Nat}, {Pair.snd(Nat, Nat, Nat.divmod.go(np, 0n, d, 1n)) == RD.Nat.bit(1n+np) : Nat}, Pair.snd({Pair.fst(Nat, Nat, Nat.divmod.go(np, 1n, d, 0n)) == Nat.add(d, D.Nat.half(np)) : Nat} & {Pair.fst(Nat, Nat, Nat.divmod.go(np, 0n, d, 1n)) == Nat.add(d, D.Nat.half(1n+np)) : Nat}, {Pair.snd(Nat, Nat, Nat.divmod.go(np, 1n, d, 0n)) == RD.Nat.bit(np) : Nat} & {Pair.snd(Nat, Nat, Nat.divmod.go(np, 0n, d, 1n)) == RD.Nat.bit(1n+np) : Nat}, Dm(np, d))),
        Pair.fst({Pair.snd(Nat, Nat, Nat.divmod.go(np, 1n, 1n+d, 0n)) == RD.Nat.bit(np) : Nat}, {Pair.snd(Nat, Nat, Nat.divmod.go(np, 0n, 1n+d, 1n)) == RD.Nat.bit(1n+np) : Nat}, Pair.snd({Pair.fst(Nat, Nat, Nat.divmod.go(np, 1n, 1n+d, 0n)) == Nat.add(1n+d, D.Nat.half(np)) : Nat} & {Pair.fst(Nat, Nat, Nat.divmod.go(np, 0n, 1n+d, 1n)) == Nat.add(1n+d, D.Nat.half(1n+np)) : Nat}, {Pair.snd(Nat, Nat, Nat.divmod.go(np, 1n, 1n+d, 0n)) == RD.Nat.bit(np) : Nat} & {Pair.snd(Nat, Nat, Nat.divmod.go(np, 0n, 1n+d, 1n)) == RD.Nat.bit(1n+np) : Nat}, Dm(np, 1n+d)))))

def L.half(+n: Nat) -> {D.Nat.half(n) == F.Nat.halff(n) : Nat}:
  Equal.sym(Nat, F.Nat.halff(n), D.Nat.half(n), Pair.fst({Pair.fst(Nat, Nat, Nat.divmod.go(n, 1n, 0n, 0n)) == Nat.add(0n, D.Nat.half(n)) : Nat}, {Pair.fst(Nat, Nat, Nat.divmod.go(n, 0n, 0n, 1n)) == Nat.add(0n, D.Nat.half(1n+n)) : Nat}, Pair.fst({Pair.fst(Nat, Nat, Nat.divmod.go(n, 1n, 0n, 0n)) == Nat.add(0n, D.Nat.half(n)) : Nat} & {Pair.fst(Nat, Nat, Nat.divmod.go(n, 0n, 0n, 1n)) == Nat.add(0n, D.Nat.half(1n+n)) : Nat}, {Pair.snd(Nat, Nat, Nat.divmod.go(n, 1n, 0n, 0n)) == RD.Nat.bit(n) : Nat} & {Pair.snd(Nat, Nat, Nat.divmod.go(n, 0n, 0n, 1n)) == RD.Nat.bit(1n+n) : Nat}, Dm(n, 0n))))

def L.bit_eq(+n: Nat, b: Bool, +eb: {D.Nat.even(n) == b : Bool}) -> {D.Nat.even(n) == Nat.is_eq(RD.Nat.bit(n), 0n) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, D.Nat.even(n), True{}, eb) : {_ == Nat.is_eq(Bool.pick(Nat, _, 0n, 1n), 0n) : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, D.Nat.even(n), False{}, eb) : {_ == Nat.is_eq(Bool.pick(Nat, _, 0n, 1n), 0n) : Bool}
      {==}

def L.even(+n: Nat) -> {D.Nat.even(n) == F.Nat.evenf(n) : Bool}:
  Equal.trans(Bool, D.Nat.even(n), Nat.is_eq(RD.Nat.bit(n), 0n), F.Nat.evenf(n), L.bit_eq(n, D.Nat.even(n), {==}),
    Equal.cong(Nat, Bool, w => Nat.is_eq(w, 0n), RD.Nat.bit(n), Pair.snd(Nat, Nat, Nat.divmod.go(n, 1n, 0n, 0n)),
      Equal.sym(Nat, Pair.snd(Nat, Nat, Nat.divmod.go(n, 1n, 0n, 0n)), RD.Nat.bit(n), Pair.fst({Pair.snd(Nat, Nat, Nat.divmod.go(n, 1n, 0n, 0n)) == RD.Nat.bit(n) : Nat}, {Pair.snd(Nat, Nat, Nat.divmod.go(n, 0n, 0n, 1n)) == RD.Nat.bit(1n+n) : Nat}, Pair.snd({Pair.fst(Nat, Nat, Nat.divmod.go(n, 1n, 0n, 0n)) == Nat.add(0n, D.Nat.half(n)) : Nat} & {Pair.fst(Nat, Nat, Nat.divmod.go(n, 0n, 0n, 1n)) == Nat.add(0n, D.Nat.half(1n+n)) : Nat}, {Pair.snd(Nat, Nat, Nat.divmod.go(n, 1n, 0n, 0n)) == RD.Nat.bit(n) : Nat} & {Pair.snd(Nat, Nat, Nat.divmod.go(n, 0n, 0n, 1n)) == RD.Nat.bit(1n+n) : Nat}, Dm(n, 0n))))))

# Integers and dyadics
# --------------------

def L.ieven(+a: I.Int) -> {D.Int.even(a) == F.Int.evenf(a) : Bool}:
  match a:
    case I.IPos{+n}:
      L.even(n)
    case I.INeg{+n}:
      Equal.cong(Bool, Bool, w => Bool.not(w), D.Nat.even(n), F.Nat.evenf(n), L.even(n))

def L.ihalf(+a: I.Int) -> {D.Int.half(a) == F.Int.halff(a) : I.Int}:
  match a:
    case I.IPos{+n}:
      Equal.cong(Nat, I.Int, w => I.IPos{w}, D.Nat.half(n), F.Nat.halff(n), L.half(n))
    case I.INeg{+n}:
      Equal.cong(Nat, I.Int, w => I.INeg{w}, D.Nat.half(n), F.Nat.halff(n), L.half(n))

def L.odd(+m: I.Int, +f: Nat) -> {D.Dy.odd(m, f) == F.Dy.oddf(m, f) : D.Dy}:
  match m:
    case I.IPos{+n}:
      Equal.cong(Nat, D.Dy, w => D.DFrac{False{}, w, f}, D.Nat.half(n), F.Nat.halff(n), L.half(n))
    case I.INeg{+n}:
      Equal.cong(Nat, D.Dy, w => D.DFrac{True{}, w, f}, D.Nat.half(n), F.Nat.halff(n), L.half(n))

def L.of.go(+e: Nat, +m: I.Int, ev: Bool, +eev: {F.Int.evenf(m) == ev : Bool}) -> {F.Dy.off.go(e, m, ev) == D.Dy.of(e, m) : D.Dy}:
  match e:
    case 0n:
      {==}
    case 1n+f:
      match ev:
        case True{}:
          +hm = F.Int.halff(m)
          Equal.trans(D.Dy, F.Dy.off.go(f, hm, F.Int.evenf(hm)), D.Dy.of(f, hm), D.Dy.of(1n+f, m),
            L.of.go(f, hm, F.Int.evenf(hm), {==}),
            Equal.trans(D.Dy, D.Dy.of(f, hm), D.Dy.of(f, D.Int.half(m)), D.Dy.of(1n+f, m),
              Equal.cong(I.Int, D.Dy, w => D.Dy.of(f, w), hm, D.Int.half(m), Equal.sym(I.Int, D.Int.half(m), hm, L.ihalf(m))),
              Equal.sym(D.Dy, D.Dy.of(1n+f, m), D.Dy.of(f, D.Int.half(m)), Y.Of.even(f, m, Equal.trans(Bool, D.Int.even(m), F.Int.evenf(m), True{}, L.ieven(m), eev)))))
        case False{}:
          Equal.trans(D.Dy, F.Dy.oddf(m, f), D.Dy.odd(m, f), D.Dy.of(1n+f, m),
            Equal.sym(D.Dy, D.Dy.odd(m, f), F.Dy.oddf(m, f), L.odd(m, f)),
            Equal.sym(D.Dy, D.Dy.of(1n+f, m), D.Dy.odd(m, f), Y.Of.odd(f, m, Equal.trans(Bool, D.Int.even(m), F.Int.evenf(m), False{}, L.ieven(m), eev))))

def L.of(+e: Nat, +m: I.Int) -> {F.Dy.off(e, m) == D.Dy.of(e, m) : D.Dy}:
  L.of.go(e, m, F.Int.evenf(m), {==})

def L.mul(+x: D.Dy, +y: D.Dy) -> {F.Dy.mulf(x, y) == D.Dy.mul(x, y) : D.Dy}:
  L.of(Nat.add(D.Dy.den(x), D.Dy.den(y)), I.Int.mul(D.Dy.num(x), D.Dy.num(y)))

def Nat.sub0(+n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def L.subnat(+m: Nat, +k: Nat) -> {I.Int.sub_nat(m, k) == F.Int.sub_natf(m, k) : I.Int}:
  match m k:
    case 0n 0n:
      {==}
    case 0n 1n+kp:
      Equal.cong(Nat, I.Int, w => I.INeg{w}, kp, Nat.sub(kp, 0n), Equal.sym(Nat, Nat.sub(kp, 0n), kp, Nat.sub0(kp)))
    case 1n+mp 0n:
      {==}
    case 1n+mp 1n+kp:
      L.subnat(mp, kp)

def L.iadd(+a: I.Int, +b: I.Int) -> {I.Int.add(a, b) == F.Int.addf(a, b) : I.Int}:
  match a b:
    case I.IPos{m} I.IPos{n}:
      {==}
    case I.INeg{m} I.INeg{n}:
      {==}
    case I.IPos{+m} I.INeg{+n}:
      L.subnat(m, 1n+n)
    case I.INeg{+m} I.IPos{+n}:
      L.subnat(n, 1n+m)

# the aligned sum has the same normal form as the cross-multiplied one
def L.adda.go(+x: D.Dy, +y: D.Dy, b: Bool, +eb: {F.Nat.ltf(D.Dy.den(y), D.Dy.den(x)) == b : Bool}) -> {F.Dy.addaf(x, y) == D.Dy.add(x, y) : D.Dy}:
  match b:
    case True{}:
      +dx = D.Dy.den(x)
      +dy = D.Dy.den(y)
      +nx = D.Dy.num(x)
      +ny = D.Dy.num(y)
      +k = RD.Nat.monus(dx, dy)
      +a = I.Int.add(nx, D.Int.sh(k, ny))
      +bb = I.Int.add(D.Int.sh(dy, nx), D.Int.sh(dx, ny))
      +hd = R.Nat.lt_t(dy, dx)(Equal.trans(Bool, RD.Nat.lt(dy, dx), F.Nat.ltf(dy, dx), True{}, L.lt(dy, dx), eb))
      %Equal.sym(Bool, F.Nat.ltf(dy, dx), True{}, eb) : {Bool.pick(D.Dy, _, F.Dy.off(dx, F.Int.addf(nx, D.Int.sh(F.Nat.monusf(dx, dy), ny))), F.Dy.off(dy, F.Int.addf(D.Int.sh(F.Nat.monusf(dy, dx), nx), ny))) == D.Dy.add(x, y) : D.Dy}
      +sim = Equal.trans(I.Int, D.Int.sh(Nat.add(dx, dy), a), I.Int.add(D.Int.sh(Nat.add(dx, dy), nx), D.Int.sh(Nat.add(Nat.add(dx, dy), k), ny)), D.Int.sh(dx, bb),
        Equal.trans(I.Int, D.Int.sh(Nat.add(dx, dy), a), I.Int.add(D.Int.sh(Nat.add(dx, dy), nx), D.Int.sh(Nat.add(dx, dy), D.Int.sh(k, ny))), I.Int.add(D.Int.sh(Nat.add(dx, dy), nx), D.Int.sh(Nat.add(Nat.add(dx, dy), k), ny)),
          Y.Int.sh_add(Nat.add(dx, dy), nx, D.Int.sh(k, ny)),
          Equal.cong(I.Int, I.Int, w => I.Int.add(D.Int.sh(Nat.add(dx, dy), nx), w), D.Int.sh(Nat.add(dx, dy), D.Int.sh(k, ny)), D.Int.sh(Nat.add(Nat.add(dx, dy), k), ny), Y.Int.sh_sh(Nat.add(dx, dy), k, ny))),
        Equal.sym(I.Int, D.Int.sh(dx, bb), I.Int.add(D.Int.sh(Nat.add(dx, dy), nx), D.Int.sh(Nat.add(Nat.add(dx, dy), k), ny)),
          Equal.trans(I.Int, D.Int.sh(dx, bb), I.Int.add(D.Int.sh(dx, D.Int.sh(dy, nx)), D.Int.sh(dx, D.Int.sh(dx, ny))), I.Int.add(D.Int.sh(Nat.add(dx, dy), nx), D.Int.sh(Nat.add(Nat.add(dx, dy), k), ny)),
            Y.Int.sh_add(dx, D.Int.sh(dy, nx), D.Int.sh(dx, ny)),
            Y.Int.cong2(D.Int.sh(dx, D.Int.sh(dy, nx)), D.Int.sh(Nat.add(dx, dy), nx), D.Int.sh(dx, D.Int.sh(dx, ny)), D.Int.sh(Nat.add(Nat.add(dx, dy), k), ny),
              Y.Int.sh_sh(dx, dy, nx),
              Equal.trans(I.Int, D.Int.sh(dx, D.Int.sh(dx, ny)), D.Int.sh(Nat.add(dx, dx), ny), D.Int.sh(Nat.add(Nat.add(dx, dy), k), ny), Y.Int.sh_sh(dx, dx, ny),
                Equal.cong(Nat, I.Int, w => D.Int.sh(w, ny), Nat.add(dx, dx), Nat.add(Nat.add(dx, dy), k),
                  Equal.trans(Nat, Nat.add(dx, dx), Nat.add(dx, Nat.add(dy, k)), Nat.add(Nat.add(dx, dy), k),
                    Equal.cong(Nat, Nat, w => Nat.add(dx, w), dx, Nat.add(dy, k), hd),
                    Equal.sym(Nat, Nat.add(Nat.add(dx, dy), k), Nat.add(dx, Nat.add(dy, k)), NL.Nat.add_assoc(dx, dy, k)))))))))
      Equal.trans(D.Dy, F.Dy.off(dx, F.Int.addf(nx, D.Int.sh(F.Nat.monusf(dx, dy), ny))), D.Dy.of(dx, a), D.Dy.add(x, y),
        Equal.trans(D.Dy, F.Dy.off(dx, F.Int.addf(nx, D.Int.sh(F.Nat.monusf(dx, dy), ny))), D.Dy.of(dx, F.Int.addf(nx, D.Int.sh(F.Nat.monusf(dx, dy), ny))), D.Dy.of(dx, a),
          L.of(dx, F.Int.addf(nx, D.Int.sh(F.Nat.monusf(dx, dy), ny))),
          Equal.cong(I.Int, D.Dy, w => D.Dy.of(dx, w), F.Int.addf(nx, D.Int.sh(F.Nat.monusf(dx, dy), ny)), a,
            Equal.trans(I.Int, F.Int.addf(nx, D.Int.sh(F.Nat.monusf(dx, dy), ny)), I.Int.add(nx, D.Int.sh(F.Nat.monusf(dx, dy), ny)), a,
              Equal.sym(I.Int, I.Int.add(nx, D.Int.sh(F.Nat.monusf(dx, dy), ny)), F.Int.addf(nx, D.Int.sh(F.Nat.monusf(dx, dy), ny)), L.iadd(nx, D.Int.sh(F.Nat.monusf(dx, dy), ny))),
              Equal.cong(Nat, I.Int, w => I.Int.add(nx, D.Int.sh(w, ny)), F.Nat.monusf(dx, dy), k, Equal.sym(Nat, k, F.Nat.monusf(dx, dy), L.monus(dx, dy)))))),
        Y.Of.eqv(dx, Nat.add(dx, dy), a, bb, sim))
    case False{}:
      +dx = D.Dy.den(x)
      +dy = D.Dy.den(y)
      +nx = D.Dy.num(x)
      +ny = D.Dy.num(y)
      +k = RD.Nat.monus(dy, dx)
      +a = I.Int.add(D.Int.sh(k, nx), ny)
      +bb = I.Int.add(D.Int.sh(dy, nx), D.Int.sh(dx, ny))
      +hd = R.Nat.lt_f(dy, dx)(Equal.trans(Bool, RD.Nat.lt(dy, dx), F.Nat.ltf(dy, dx), False{}, L.lt(dy, dx), eb))
      %Equal.sym(Bool, F.Nat.ltf(dy, dx), False{}, eb) : {Bool.pick(D.Dy, _, F.Dy.off(dx, F.Int.addf(nx, D.Int.sh(F.Nat.monusf(dx, dy), ny))), F.Dy.off(dy, F.Int.addf(D.Int.sh(F.Nat.monusf(dy, dx), nx), ny))) == D.Dy.add(x, y) : D.Dy}
      # sh(dx + dy, sh(k, nx) + ny) = sh(dy, sh(dy, nx) + sh(dx, ny)), with dy = dx + k
      +e1 = Equal.trans(Nat, Nat.add(Nat.add(dx, dy), k), Nat.add(dy, Nat.add(dx, k)), Nat.add(dy, dy),
        Equal.trans(Nat, Nat.add(Nat.add(dx, dy), k), Nat.add(Nat.add(dy, dx), k), Nat.add(dy, Nat.add(dx, k)),
          Equal.cong(Nat, Nat, w => Nat.add(w, k), Nat.add(dx, dy), Nat.add(dy, dx), NL.Nat.add_comm(dx, dy)),
          NL.Nat.add_assoc(dy, dx, k)),
        Equal.cong(Nat, Nat, w => Nat.add(dy, w), Nat.add(dx, k), dy, Equal.sym(Nat, dy, Nat.add(dx, k), hd)))
      +sim = Equal.trans(I.Int, D.Int.sh(Nat.add(dx, dy), a), I.Int.add(D.Int.sh(Nat.add(dy, dy), nx), D.Int.sh(Nat.add(dy, dx), ny)), D.Int.sh(dy, bb),
        Equal.trans(I.Int, D.Int.sh(Nat.add(dx, dy), a), I.Int.add(D.Int.sh(Nat.add(dx, dy), D.Int.sh(k, nx)), D.Int.sh(Nat.add(dx, dy), ny)), I.Int.add(D.Int.sh(Nat.add(dy, dy), nx), D.Int.sh(Nat.add(dy, dx), ny)),
          Y.Int.sh_add(Nat.add(dx, dy), D.Int.sh(k, nx), ny),
          Y.Int.cong2(D.Int.sh(Nat.add(dx, dy), D.Int.sh(k, nx)), D.Int.sh(Nat.add(dy, dy), nx), D.Int.sh(Nat.add(dx, dy), ny), D.Int.sh(Nat.add(dy, dx), ny),
            Equal.trans(I.Int, D.Int.sh(Nat.add(dx, dy), D.Int.sh(k, nx)), D.Int.sh(Nat.add(Nat.add(dx, dy), k), nx), D.Int.sh(Nat.add(dy, dy), nx), Y.Int.sh_sh(Nat.add(dx, dy), k, nx),
              Equal.cong(Nat, I.Int, w => D.Int.sh(w, nx), Nat.add(Nat.add(dx, dy), k), Nat.add(dy, dy), e1)),
            Equal.cong(Nat, I.Int, w => D.Int.sh(w, ny), Nat.add(dx, dy), Nat.add(dy, dx), NL.Nat.add_comm(dx, dy)))),
        Equal.sym(I.Int, D.Int.sh(dy, bb), I.Int.add(D.Int.sh(Nat.add(dy, dy), nx), D.Int.sh(Nat.add(dy, dx), ny)),
          Equal.trans(I.Int, D.Int.sh(dy, bb), I.Int.add(D.Int.sh(dy, D.Int.sh(dy, nx)), D.Int.sh(dy, D.Int.sh(dx, ny))), I.Int.add(D.Int.sh(Nat.add(dy, dy), nx), D.Int.sh(Nat.add(dy, dx), ny)),
            Y.Int.sh_add(dy, D.Int.sh(dy, nx), D.Int.sh(dx, ny)),
            Y.Int.cong2(D.Int.sh(dy, D.Int.sh(dy, nx)), D.Int.sh(Nat.add(dy, dy), nx), D.Int.sh(dy, D.Int.sh(dx, ny)), D.Int.sh(Nat.add(dy, dx), ny), Y.Int.sh_sh(dy, dy, nx), Y.Int.sh_sh(dy, dx, ny)))))
      Equal.trans(D.Dy, F.Dy.off(dy, F.Int.addf(D.Int.sh(F.Nat.monusf(dy, dx), nx), ny)), D.Dy.of(dy, a), D.Dy.add(x, y),
        Equal.trans(D.Dy, F.Dy.off(dy, F.Int.addf(D.Int.sh(F.Nat.monusf(dy, dx), nx), ny)), D.Dy.of(dy, F.Int.addf(D.Int.sh(F.Nat.monusf(dy, dx), nx), ny)), D.Dy.of(dy, a),
          L.of(dy, F.Int.addf(D.Int.sh(F.Nat.monusf(dy, dx), nx), ny)),
          Equal.cong(I.Int, D.Dy, w => D.Dy.of(dy, w), F.Int.addf(D.Int.sh(F.Nat.monusf(dy, dx), nx), ny), a,
            Equal.trans(I.Int, F.Int.addf(D.Int.sh(F.Nat.monusf(dy, dx), nx), ny), I.Int.add(D.Int.sh(F.Nat.monusf(dy, dx), nx), ny), a,
              Equal.sym(I.Int, I.Int.add(D.Int.sh(F.Nat.monusf(dy, dx), nx), ny), F.Int.addf(D.Int.sh(F.Nat.monusf(dy, dx), nx), ny), L.iadd(D.Int.sh(F.Nat.monusf(dy, dx), nx), ny)),
              Equal.cong(Nat, I.Int, w => I.Int.add(D.Int.sh(w, nx), ny), F.Nat.monusf(dy, dx), k, Equal.sym(Nat, k, F.Nat.monusf(dy, dx), L.monus(dy, dx)))))),
        Y.Of.eqv(dy, Nat.add(dx, dy), a, bb, sim))

def L.adda(+x: D.Dy, +y: D.Dy) -> {F.Dy.addaf(x, y) == D.Dy.add(x, y) : D.Dy}:
  L.adda.go(x, y, F.Nat.ltf(D.Dy.den(y), D.Dy.den(x)), {==})

# Rounding
# --------

def L.bit(+n: Nat) -> {RD.Nat.bit(n) == F.Nat.bitf(n) : Nat}:
  Equal.cong(Bool, Nat, w => Bool.pick(Nat, w, 0n, 1n), D.Nat.even(n), F.Nat.evenf(n), L.even(n))

def L.up(t: RD.Tr, +b: Nat, +w: Nat) -> {RD.Tr.up(t, b, w) == F.Tr.upf(t, b, w) : RD.Tr}:
  match t:
    case RD.Tr{+s, +q, +r, +wr, +wq}:
      +m1 = Equal.sym(Nat, RD.Nat.monus(1n, b), F.Nat.monusf(1n, b), L.monus(1n, b))
      +h1 = Equal.sym(Nat, D.Nat.half(w), F.Nat.halff(w), L.half(w))
      %m1 : {RD.Tr{1n+s, q, Nat.add(Nat.double(r), b), Nat.add(Nat.double(wr), _), Bool.pick(Nat, Nat.is_eq(s, 0n), D.Nat.half(w), wq)} == RD.Tr{1n+s, q, Nat.add(Nat.double(r), b), Nat.add(Nat.double(wr), F.Nat.monusf(1n, b)), Bool.pick(Nat, Nat.is_eq(s, 0n), F.Nat.halff(w), wq)} : RD.Tr}
      %h1 : {RD.Tr{1n+s, q, Nat.add(Nat.double(r), b), Nat.add(Nat.double(wr), F.Nat.monusf(1n, b)), Bool.pick(Nat, Nat.is_eq(s, 0n), _, wq)} == RD.Tr{1n+s, q, Nat.add(Nat.double(r), b), Nat.add(Nat.double(wr), F.Nat.monusf(1n, b)), Bool.pick(Nat, Nat.is_eq(s, 0n), F.Nat.halff(w), wq)} : RD.Tr}
      {==}

def L.go(+fuel: Nat, +p: Nat, +n: Nat, lt: Bool) -> {RD.Tr.go(fuel, p, n, lt) == F.Tr.gof(fuel, p, n, lt) : RD.Tr}:
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      match lt:
        case True{}:
          {==}
        case False{}:
          +pw = RD.Nat.pow2(p)
          +g1 = RD.Tr.go(f, p, D.Nat.half(n), RD.Nat.lt(D.Nat.half(n), pw))
          +g2 = F.Tr.gof(f, p, D.Nat.half(n), RD.Nat.lt(D.Nat.half(n), pw))
          +g3 = F.Tr.gof(f, p, F.Nat.halff(n), RD.Nat.lt(F.Nat.halff(n), pw))
          +g4 = F.Tr.gof(f, p, F.Nat.halff(n), F.Nat.ltf(F.Nat.halff(n), pw))
          +eg = Equal.trans(RD.Tr, g1, g2, g4, L.go(f, p, D.Nat.half(n), RD.Nat.lt(D.Nat.half(n), pw)),
            Equal.trans(RD.Tr, g2, g3, g4,
              Equal.cong(Nat, RD.Tr, w => F.Tr.gof(f, p, w, RD.Nat.lt(w, pw)), D.Nat.half(n), F.Nat.halff(n), L.half(n)),
              Equal.cong(Bool, RD.Tr, w => F.Tr.gof(f, p, F.Nat.halff(n), w), RD.Nat.lt(F.Nat.halff(n), pw), F.Nat.ltf(F.Nat.halff(n), pw), L.lt(F.Nat.halff(n), pw))))
          Equal.trans(RD.Tr, RD.Tr.up(g1, RD.Nat.bit(n), RD.Nat.monus(n, pw)), RD.Tr.up(g4, F.Nat.bitf(n), F.Nat.monusf(n, pw)), F.Tr.upf(g4, F.Nat.bitf(n), F.Nat.monusf(n, pw)),
            Equal.trans(RD.Tr, RD.Tr.up(g1, RD.Nat.bit(n), RD.Nat.monus(n, pw)), RD.Tr.up(g4, RD.Nat.bit(n), RD.Nat.monus(n, pw)), RD.Tr.up(g4, F.Nat.bitf(n), F.Nat.monusf(n, pw)),
              Equal.cong(RD.Tr, RD.Tr, w => RD.Tr.up(w, RD.Nat.bit(n), RD.Nat.monus(n, pw)), g1, g4, eg),
              Equal.trans(RD.Tr, RD.Tr.up(g4, RD.Nat.bit(n), RD.Nat.monus(n, pw)), RD.Tr.up(g4, F.Nat.bitf(n), RD.Nat.monus(n, pw)), RD.Tr.up(g4, F.Nat.bitf(n), F.Nat.monusf(n, pw)),
                Equal.cong(Nat, RD.Tr, w => RD.Tr.up(g4, w, RD.Nat.monus(n, pw)), RD.Nat.bit(n), F.Nat.bitf(n), L.bit(n)),
                Equal.cong(Nat, RD.Tr, w => RD.Tr.up(g4, F.Nat.bitf(n), w), RD.Nat.monus(n, pw), F.Nat.monusf(n, pw), L.monus(n, pw)))),
            L.up(g4, F.Nat.bitf(n), F.Nat.monusf(n, pw)))

def L.trof(+p: Nat, +n: Nat) -> {RD.Tr.of(p, n) == F.Tr.off(p, n) : RD.Tr}:
  Equal.trans(RD.Tr, RD.Tr.go(n, p, n, RD.Nat.lt(n, RD.Nat.pow2(p))), F.Tr.gof(n, p, n, RD.Nat.lt(n, RD.Nat.pow2(p))), F.Tr.gof(n, p, n, F.Nat.ltf(n, RD.Nat.pow2(p))),
    L.go(n, p, n, RD.Nat.lt(n, RD.Nat.pow2(p))),
    Equal.cong(Bool, RD.Tr, w => F.Tr.gof(n, p, n, w), RD.Nat.lt(n, RD.Nat.pow2(p)), F.Nat.ltf(n, RD.Nat.pow2(p)), L.lt(n, RD.Nat.pow2(p))))

def L.rup(t: RD.Tr) -> {RD.Tr.rup(t) == F.Tr.rupf(t) : Bool}:
  match t:
    case RD.Tr{+s, +q, +r, wr, wq}:
      +sv = RD.Nat.pow2(s)
      +e1 = Equal.sym(Bool, RD.Nat.lt(Nat.double(r), sv), F.Nat.ltf(Nat.double(r), sv), L.lt(Nat.double(r), sv))
      +e2 = Equal.sym(Bool, RD.Nat.lt(sv, Nat.double(r)), F.Nat.ltf(sv, Nat.double(r)), L.lt(sv, Nat.double(r)))
      +e3 = Equal.sym(Bool, D.Nat.even(q), F.Nat.evenf(q), L.even(q))
      %e1 : {Bool.and(Bool.not(_), Bool.or(RD.Nat.lt(sv, Nat.double(r)), Bool.not(D.Nat.even(q)))) == Bool.and(Bool.not(F.Nat.ltf(Nat.double(r), sv)), Bool.or(F.Nat.ltf(sv, Nat.double(r)), Bool.not(F.Nat.evenf(q)))) : Bool}
      %e2 : {Bool.and(Bool.not(F.Nat.ltf(Nat.double(r), sv)), Bool.or(_, Bool.not(D.Nat.even(q)))) == Bool.and(Bool.not(F.Nat.ltf(Nat.double(r), sv)), Bool.or(F.Nat.ltf(sv, Nat.double(r)), Bool.not(F.Nat.evenf(q)))) : Bool}
      %e3 : {Bool.and(Bool.not(F.Nat.ltf(Nat.double(r), sv)), Bool.or(F.Nat.ltf(sv, Nat.double(r)), Bool.not(_))) == Bool.and(Bool.not(F.Nat.ltf(Nat.double(r), sv)), Bool.or(F.Nat.ltf(sv, Nat.double(r)), Bool.not(F.Nat.evenf(q)))) : Bool}
      {==}

def L.near(+t: RD.Tr) -> {RD.Tr.near(t) == F.Tr.nearf(t) : Nat}:
  Equal.cong(Bool, Nat, w => Bool.pick(Nat, w, Nat.mul(1n+RD.Tr.q(t), RD.Nat.pow2(RD.Tr.s(t))), Nat.mul(RD.Tr.q(t), RD.Nat.pow2(RD.Tr.s(t)))), RD.Tr.rup(t), F.Tr.rupf(t), L.rup(t))

def L.fx(+s: Nat, +n: Nat) -> {RD.Fx.go(s, n) == F.Fx.gof(s, n) : RD.Tr}:
  match s:
    case 0n:
      {==}
    case 1n+j:
      +g1 = RD.Fx.go(j, D.Nat.half(n))
      +g4 = F.Fx.gof(j, F.Nat.halff(n))
      +eg = Equal.trans(RD.Tr, g1, F.Fx.gof(j, D.Nat.half(n)), g4, L.fx(j, D.Nat.half(n)),
        Equal.cong(Nat, RD.Tr, w => F.Fx.gof(j, w), D.Nat.half(n), F.Nat.halff(n), L.half(n)))
      Equal.trans(RD.Tr, RD.Tr.up(g1, RD.Nat.bit(n), 0n), RD.Tr.up(g4, F.Nat.bitf(n), 0n), F.Tr.upf(g4, F.Nat.bitf(n), 0n),
        Equal.trans(RD.Tr, RD.Tr.up(g1, RD.Nat.bit(n), 0n), RD.Tr.up(g4, RD.Nat.bit(n), 0n), RD.Tr.up(g4, F.Nat.bitf(n), 0n),
          Equal.cong(RD.Tr, RD.Tr, w => RD.Tr.up(w, RD.Nat.bit(n), 0n), g1, g4, eg),
          Equal.cong(Nat, RD.Tr, w => RD.Tr.up(g4, w, 0n), RD.Nat.bit(n), F.Nat.bitf(n), L.bit(n))),
        L.up(g4, F.Nat.bitf(n), 0n))

# the rounded magnitude, through both loops
def L.nmag(+p: Nat, +n: Nat) -> {RD.Tr.near(RD.Tr.of(p, n)) == F.Tr.nearf(F.Tr.off(p, n)) : Nat}:
  Equal.trans(Nat, RD.Tr.near(RD.Tr.of(p, n)), RD.Tr.near(F.Tr.off(p, n)), F.Tr.nearf(F.Tr.off(p, n)),
    Equal.cong(RD.Tr, Nat, t => RD.Tr.near(t), RD.Tr.of(p, n), F.Tr.off(p, n), L.trof(p, n)),
    L.near(F.Tr.off(p, n)))

def L.rne(+p: Nat, +x: D.Dy) -> {RD.Dy.rne(p, x) == F.Dy.rnef(p, x) : D.Dy}:
  +d = D.Dy.den(x)
  +m = D.Dy.num(x)
  +a = RD.Tr.near(RD.Tr.of(p, RD.Int.mag(m)))
  +b = F.Tr.nearf(F.Tr.off(p, RD.Int.mag(m)))
  Equal.trans(D.Dy, D.Dy.of(d, RD.Int.signed(m, a)), D.Dy.of(d, RD.Int.signed(m, b)), F.Dy.off(d, RD.Int.signed(m, b)),
    Equal.cong(Nat, D.Dy, w => D.Dy.of(d, RD.Int.signed(m, w)), a, b, L.nmag(p, RD.Int.mag(m))),
    Equal.sym(D.Dy, F.Dy.off(d, RD.Int.signed(m, b)), D.Dy.of(d, RD.Int.signed(m, b)), L.of(d, RD.Int.signed(m, b))))

def L.rfix(+k: Nat, +x: D.Dy) -> {RD.Dy.rfix(k, x) == F.Dy.rfixf(k, x) : D.Dy}:
  +d = D.Dy.den(x)
  +m = D.Dy.num(x)
  +n = RD.Int.mag(m)
  +a = RD.Tr.near(RD.Fx.go(RD.Nat.monus(d, k), n))
  +b = F.Tr.nearf(F.Fx.gof(F.Nat.monusf(d, k), n))
  +ea = Equal.trans(Nat, a, RD.Tr.near(RD.Fx.go(F.Nat.monusf(d, k), n)), b,
    Equal.cong(Nat, Nat, s => RD.Tr.near(RD.Fx.go(s, n)), RD.Nat.monus(d, k), F.Nat.monusf(d, k), L.monus(d, k)),
    Equal.trans(Nat, RD.Tr.near(RD.Fx.go(F.Nat.monusf(d, k), n)), RD.Tr.near(F.Fx.gof(F.Nat.monusf(d, k), n)), b,
      Equal.cong(RD.Tr, Nat, t => RD.Tr.near(t), RD.Fx.go(F.Nat.monusf(d, k), n), F.Fx.gof(F.Nat.monusf(d, k), n), L.fx(F.Nat.monusf(d, k), n)),
      L.near(F.Fx.gof(F.Nat.monusf(d, k), n))))
  +ey = Equal.trans(D.Dy, D.Dy.of(d, RD.Int.signed(m, a)), D.Dy.of(d, RD.Int.signed(m, b)), F.Dy.off(d, RD.Int.signed(m, b)),
    Equal.cong(Nat, D.Dy, w => D.Dy.of(d, RD.Int.signed(m, w)), a, b, ea),
    Equal.sym(D.Dy, F.Dy.off(d, RD.Int.signed(m, b)), D.Dy.of(d, RD.Int.signed(m, b)), L.of(d, RD.Int.signed(m, b))))
  +el = Equal.sym(Bool, RD.Nat.lt(k, d), F.Nat.ltf(k, d), L.lt(k, d))
  %el : {Bool.pick(D.Dy, _, D.Dy.of(d, RD.Int.signed(m, a)), x) == Bool.pick(D.Dy, F.Nat.ltf(k, d), F.Dy.off(d, RD.Int.signed(m, b)), x) : D.Dy}
  Equal.cong(D.Dy, D.Dy, y => Bool.pick(D.Dy, F.Nat.ltf(k, d), y, x), D.Dy.of(d, RD.Int.signed(m, a)), F.Dy.off(d, RD.Int.signed(m, b)), ey)

def L.big(+x: D.Dy) -> {RD.Dy.big(x) == F.Dy.bigf(x) : Bool}:
  +d = D.Dy.den(x)
  +n = RD.Int.mag(D.Dy.num(x))
  +e1 = Equal.sym(Bool, RD.Nat.lt(126n, d), F.Nat.ltf(126n, d), L.lt(126n, d))
  +e2 = Equal.sym(Nat, RD.Nat.monus(d, 126n), F.Nat.monusf(d, 126n), L.monus(d, 126n))
  +e3 = Equal.sym(Bool, RD.Nat.lt(n, RD.Nat.pow2(F.Nat.monusf(d, 126n))), F.Nat.ltf(n, RD.Nat.pow2(F.Nat.monusf(d, 126n))), L.lt(n, RD.Nat.pow2(F.Nat.monusf(d, 126n))))
  %e1 : {Bool.pick(Bool, _, Bool.not(RD.Nat.lt(n, RD.Nat.pow2(RD.Nat.monus(d, 126n)))), True{}) == F.Dy.bigf(x) : Bool}
  %e2 : {Bool.pick(Bool, F.Nat.ltf(126n, d), Bool.not(RD.Nat.lt(n, RD.Nat.pow2(_))), True{}) == F.Dy.bigf(x) : Bool}
  %e3 : {Bool.pick(Bool, F.Nat.ltf(126n, d), Bool.not(_), True{}) == F.Dy.bigf(x) : Bool}
  {==}

def L.fl(+p: Nat, +k: Nat, big: Bool, +x: D.Dy) -> {RD.Dy.fl(p, k, big, x) == F.Dy.flf(p, k, big, x) : D.Dy}:
  match big:
    case True{}:
      L.rne(p, x)
    case False{}:
      L.rfix(k, x)

# the fast binary32 rounding is binary32 rounding
def L.f32(+x: D.Dy) -> {RD.Dy.f32(x) == F.Dy.f32f(x) : D.Dy}:
  Equal.trans(D.Dy, RD.Dy.fl(24n, 149n, RD.Dy.big(x), x), RD.Dy.fl(24n, 149n, F.Dy.bigf(x), x), F.Dy.flf(24n, 149n, F.Dy.bigf(x), x),
    Equal.cong(Bool, D.Dy, w => RD.Dy.fl(24n, 149n, w, x), RD.Dy.big(x), F.Dy.bigf(x), L.big(x)),
    L.fl(24n, 149n, F.Dy.bigf(x), x))

# so the fast binary32 operations are the modelled ones (Fl.model applies)
def L.mul32(+x: D.Dy, +y: D.Dy) -> {F.Dy.f32f(F.Dy.mulf(x, y)) == RD.Dy.f32(D.Dy.mul(x, y)) : D.Dy}:
  Equal.trans(D.Dy, F.Dy.f32f(F.Dy.mulf(x, y)), F.Dy.f32f(D.Dy.mul(x, y)), RD.Dy.f32(D.Dy.mul(x, y)),
    Equal.cong(D.Dy, D.Dy, z => F.Dy.f32f(z), F.Dy.mulf(x, y), D.Dy.mul(x, y), L.mul(x, y)),
    Equal.sym(D.Dy, RD.Dy.f32(D.Dy.mul(x, y)), F.Dy.f32f(D.Dy.mul(x, y)), L.f32(D.Dy.mul(x, y))))

def L.add32(+x: D.Dy, +y: D.Dy) -> {F.Dy.f32f(F.Dy.addaf(x, y)) == RD.Dy.f32(D.Dy.add(x, y)) : D.Dy}:
  Equal.trans(D.Dy, F.Dy.f32f(F.Dy.addaf(x, y)), F.Dy.f32f(D.Dy.add(x, y)), RD.Dy.f32(D.Dy.add(x, y)),
    Equal.cong(D.Dy, D.Dy, z => F.Dy.f32f(z), F.Dy.addaf(x, y), D.Dy.add(x, y), L.adda(x, y)),
    Equal.sym(D.Dy, RD.Dy.f32(D.Dy.add(x, y)), F.Dy.f32f(D.Dy.add(x, y)), L.f32(D.Dy.add(x, y))))
