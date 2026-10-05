# Big naturals compute Nat arithmetic (src/big.bend): each operation
# commutes with the value map, for limbs below the base (Bn.ok).

import Base
import ../src/round.bend as RD
import ../src/dyadic.bend as D
import ../src/int.bend as I
import ../src/fast.bend as F
import ../src/big.bend as B
import ../src/norm.bend as N
import ./nat.bend as NL
import ./int.bend as Z
import ./round.bend as R
import ./dyadic.bend as Y
import ./equiv.bend as EQ
import ./fast.bend as FL

# Order on Nat
# ------------

def Lt.z(+a: Nat) -> {RD.Nat.lt(a, 0n) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Lt.shift(+k: Nat, +a: Nat, +b: Nat) -> {RD.Nat.lt(Nat.add(k, a), Nat.add(k, b)) == RD.Nat.lt(a, b) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Lt.shift(j, a, b)

def Lt.self(+w: Nat, +k: Nat) -> {RD.Nat.lt(w, Nat.add(w, 1n+k)) == True{} : Bool}:
  match w:
    case 0n:
      {==}
    case 1n+j:
      Lt.self(j, k)

def Lt.ge(+a: Nat, +k: Nat) -> {RD.Nat.lt(Nat.add(a, k), a) == False{} : Bool}:
  match a:
    case 0n:
      Lt.z(k)
    case 1n+j:
      Lt.ge(j, k)

def Mo.z(+n: Nat) -> {RD.Nat.monus(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a < b gives b = (1 + a) + (b - (1 + a))
def Lt.wit(+a: Nat, +b: Nat) -> {RD.Nat.lt(a, b) == True{} : Bool} -> {b == Nat.add(1n+a, RD.Nat.monus(b, 1n+a)) : Nat}:
  match a b:
    case a2 0n:
      e => Empty.absurd({0n == Nat.add(1n+a2, RD.Nat.monus(0n, 1n+a2)) : Nat}, Z.Bool.ft(e))
    case 0n 1n+bp:
      e => Equal.cong(Nat, Nat, x => 1n+x, bp, RD.Nat.monus(bp, 0n), Equal.sym(Nat, RD.Nat.monus(bp, 0n), bp, Mo.z(bp)))
    case 1n+ap 1n+bp:
      e => Equal.cong(Nat, Nat, x => 1n+x, bp, Nat.add(1n+ap, RD.Nat.monus(bp, 1n+ap)), Lt.wit(ap, bp)(e))

# with w < B: w + A B < V B exactly when A < V
def Lt.lo(+bb: Nat, +w: Nat, +u: Nat, +hb: {bb == Nat.add(w, 1n+u) : Nat}, +a: Nat, +v: Nat)
  -> {RD.Nat.lt(Nat.add(w, Nat.mul(a, bb)), Nat.mul(v, bb)) == RD.Nat.lt(a, v) : Bool}:
  match a v:
    case 0n 0n:
      Lt.z(Nat.add(w, 0n))
    case 0n 1n+vp:
      +z = Nat.mul(vp, bb)
      +e1 = Equal.sym(Nat, Nat.add(w, 0n), w, NL.Nat.add_zero_r(w))
      +e2 = Equal.trans(Nat, Nat.add(bb, z), Nat.add(Nat.add(w, 1n+u), z), Nat.add(w, Nat.add(1n+u, z)),
        Equal.cong(Nat, Nat, x => Nat.add(x, z), bb, Nat.add(w, 1n+u), hb), NL.Nat.add_assoc(w, 1n+u, z))
      +e2s = Equal.sym(Nat, Nat.add(bb, z), Nat.add(w, Nat.add(1n+u, z)), e2)
      %e1 : {RD.Nat.lt(_, Nat.add(bb, z)) == True{} : Bool}
      %e2s : {RD.Nat.lt(w, _) == True{} : Bool}
      Lt.self(w, Nat.add(u, z))
    case 1n+ap 0n:
      Lt.z(Nat.add(w, Nat.add(bb, Nat.mul(ap, bb))))
    case 1n+ap 1n+vp:
      +e = Equal.sym(Nat, Nat.add(w, Nat.add(bb, Nat.mul(ap, bb))), Nat.add(bb, Nat.add(w, Nat.mul(ap, bb))), NL.Nat.add_swap(w, bb, Nat.mul(ap, bb)))
      %e : {RD.Nat.lt(_, Nat.add(bb, Nat.mul(vp, bb))) == RD.Nat.lt(ap, vp) : Bool}
      Equal.trans(Bool, RD.Nat.lt(Nat.add(bb, Nat.add(w, Nat.mul(ap, bb))), Nat.add(bb, Nat.mul(vp, bb))), RD.Nat.lt(Nat.add(w, Nat.mul(ap, bb)), Nat.mul(vp, bb)), RD.Nat.lt(ap, vp),
        Lt.shift(bb, Nat.add(w, Nat.mul(ap, bb)), Nat.mul(vp, bb)), Lt.lo(bb, w, u, hb, ap, vp))

# with 1 + w <= B: A B < (1 + w) + V B exactly when A < 1 + V
def Lt.hi(+bb: Nat, +w: Nat, +u: Nat, +hb: {bb == Nat.add(1n+w, u) : Nat}, +a: Nat, +v: Nat)
  -> {RD.Nat.lt(Nat.mul(a, bb), Nat.add(1n+w, Nat.mul(v, bb))) == RD.Nat.lt(a, 1n+v) : Bool}:
  match a v:
    case 0n v2:
      {==}
    case 1n+ap 0n:
      +k = Nat.add(u, Nat.mul(ap, bb))
      +e1 = Equal.trans(Nat, Nat.add(bb, Nat.mul(ap, bb)), Nat.add(Nat.add(1n+w, u), Nat.mul(ap, bb)), Nat.add(1n+w, k),
        Equal.cong(Nat, Nat, x => Nat.add(x, Nat.mul(ap, bb)), bb, Nat.add(1n+w, u), hb), NL.Nat.add_assoc(1n+w, u, Nat.mul(ap, bb)))
      +e1s = Equal.sym(Nat, Nat.add(bb, Nat.mul(ap, bb)), Nat.add(1n+w, k), e1)
      +e2 = Equal.sym(Nat, 1n+Nat.add(w, 0n), 1n+w, Equal.cong(Nat, Nat, x => 1n+x, Nat.add(w, 0n), w, NL.Nat.add_zero_r(w)))
      %e1s : {RD.Nat.lt(_, 1n+Nat.add(w, 0n)) == RD.Nat.lt(ap, 0n) : Bool}
      %e2 : {RD.Nat.lt(Nat.add(1n+w, k), _) == RD.Nat.lt(ap, 0n) : Bool}
      Equal.trans(Bool, RD.Nat.lt(Nat.add(1n+w, k), 1n+w), False{}, RD.Nat.lt(ap, 0n), Lt.ge(1n+w, k), Equal.sym(Bool, RD.Nat.lt(ap, 0n), False{}, Lt.z(ap)))
    case 1n+ap 1n+vp:
      +e = Equal.sym(Nat, Nat.add(1n+w, Nat.add(bb, Nat.mul(vp, bb))), Nat.add(bb, Nat.add(1n+w, Nat.mul(vp, bb))), NL.Nat.add_swap(1n+w, bb, Nat.mul(vp, bb)))
      %e : {RD.Nat.lt(Nat.add(bb, Nat.mul(ap, bb)), _) == RD.Nat.lt(ap, 1n+vp) : Bool}
      Equal.trans(Bool, RD.Nat.lt(Nat.add(bb, Nat.mul(ap, bb)), Nat.add(bb, Nat.add(1n+w, Nat.mul(vp, bb)))), RD.Nat.lt(Nat.mul(ap, bb), Nat.add(1n+w, Nat.mul(vp, bb))), RD.Nat.lt(ap, 1n+vp),
        Lt.shift(bb, Nat.mul(ap, bb), Nat.add(1n+w, Nat.mul(vp, bb))), Lt.hi(bb, w, u, hb, ap, vp))

def And.r(+x: Bool, +y: Bool) -> {Bool.and(x, y) == True{} : Bool} -> {y == True{} : Bool}:
  match x:
    case True{}:
      e => e
    case False{}:
      e => Empty.absurd({y == True{} : Bool}, Z.Bool.ft(e))

# Limbs
# -----

def Ok.hd(+h: Nat, +x: Nat, +xs: B.Bn, oa: {B.Bn.ok(h, B.BCons{x, xs}) == True{} : Bool})
  -> {Nat.double(h) == Nat.add(1n+x, RD.Nat.monus(Nat.double(h), 1n+x)) : Nat}:
  Lt.wit(x, Nat.double(h))(Equal.trans(Bool, RD.Nat.lt(x, Nat.double(h)), F.Nat.ltf(x, Nat.double(h)), True{}, FL.L.lt(x, Nat.double(h)),
    R.Bool.and_t1(F.Nat.ltf(x, Nat.double(h)), B.Bn.ok(h, xs))(oa)))

def Ok.tl(+h: Nat, +x: Nat, +xs: B.Bn, oa: {B.Bn.ok(h, B.BCons{x, xs}) == True{} : Bool}) -> {B.Bn.ok(h, xs) == True{} : Bool}:
  And.r(F.Nat.ltf(x, Nat.double(h)), B.Bn.ok(h, xs))(oa)

# Comparison
# ----------

# one limb: with x < B and k <= B, comparing x + A B with k + V B is
# comparing A with V, or with V + 1 when x < k
def Cmp.k(+bb: Nat, +x: Nat, +k: Nat, +a: Nat, +v: Nat, +ux: Nat, +hx: {bb == Nat.add(1n+x, ux) : Nat}, +uk: Nat, +hk: {bb == Nat.add(k, uk) : Nat}, b: Bool, +eb: {RD.Nat.lt(x, k) == b : Bool})
  -> {RD.Nat.lt(Nat.add(x, Nat.mul(a, bb)), Nat.add(k, Nat.mul(v, bb))) == RD.Nat.lt(a, Nat.add(B.Bn.c(b), v)) : Bool}:
  match b:
    case True{}:
      +ab = Nat.mul(a, bb)
      +vb = Nat.mul(v, bb)
      +w = RD.Nat.monus(k, 1n+x)
      +hkx = Lt.wit(x, k)(eb)
      +ek = Equal.trans(Nat, Nat.add(k, vb), Nat.add(Nat.add(1n+x, w), vb), Nat.add(x, Nat.add(1n+w, vb)),
        Equal.cong(Nat, Nat, z => Nat.add(z, vb), k, Nat.add(1n+x, w), hkx),
        Equal.trans(Nat, 1n+Nat.add(Nat.add(x, w), vb), 1n+Nat.add(x, Nat.add(w, vb)), Nat.add(x, 1n+Nat.add(w, vb)),
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(x, w), vb), Nat.add(x, Nat.add(w, vb)), NL.Nat.add_assoc(x, w, vb)),
          Equal.sym(Nat, Nat.add(x, 1n+Nat.add(w, vb)), 1n+Nat.add(x, Nat.add(w, vb)), NL.Nat.add_succ_r(x, Nat.add(w, vb)))))
      +hb = Equal.trans(Nat, bb, Nat.add(k, uk), Nat.add(1n+w, Nat.add(x, uk)), hk,
        Equal.trans(Nat, Nat.add(k, uk), Nat.add(Nat.add(1n+x, w), uk), Nat.add(1n+w, Nat.add(x, uk)),
          Equal.cong(Nat, Nat, z => Nat.add(z, uk), k, Nat.add(1n+x, w), hkx),
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(x, w), uk), Nat.add(w, Nat.add(x, uk)),
            Equal.trans(Nat, Nat.add(Nat.add(x, w), uk), Nat.add(x, Nat.add(w, uk)), Nat.add(w, Nat.add(x, uk)), NL.Nat.add_assoc(x, w, uk), NL.Nat.add_swap(x, w, uk)))))
      +eks = Equal.sym(Nat, Nat.add(k, vb), Nat.add(x, Nat.add(1n+w, vb)), ek)
      %eks : {RD.Nat.lt(Nat.add(x, ab), _) == RD.Nat.lt(a, 1n+v) : Bool}
      Equal.trans(Bool, RD.Nat.lt(Nat.add(x, ab), Nat.add(x, Nat.add(1n+w, vb))), RD.Nat.lt(ab, Nat.add(1n+w, vb)), RD.Nat.lt(a, 1n+v),
        Lt.shift(x, ab, Nat.add(1n+w, vb)), Lt.hi(bb, w, Nat.add(x, uk), hb, a, v))
    case False{}:
      +ab = Nat.mul(a, bb)
      +vb = Nat.mul(v, bb)
      +w = RD.Nat.monus(x, k)
      +hxk = R.Nat.lt_f(x, k)(eb)
      +ex = Equal.trans(Nat, Nat.add(x, ab), Nat.add(Nat.add(k, w), ab), Nat.add(k, Nat.add(w, ab)),
        Equal.cong(Nat, Nat, z => Nat.add(z, ab), x, Nat.add(k, w), hxk), NL.Nat.add_assoc(k, w, ab))
      +hb = Equal.trans(Nat, bb, 1n+Nat.add(x, ux), Nat.add(w, 1n+Nat.add(k, ux)), hx,
        Equal.trans(Nat, 1n+Nat.add(x, ux), 1n+Nat.add(w, Nat.add(k, ux)), Nat.add(w, 1n+Nat.add(k, ux)),
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(x, ux), Nat.add(w, Nat.add(k, ux)),
            Equal.trans(Nat, Nat.add(x, ux), Nat.add(Nat.add(k, w), ux), Nat.add(w, Nat.add(k, ux)),
              Equal.cong(Nat, Nat, z => Nat.add(z, ux), x, Nat.add(k, w), hxk),
              Equal.trans(Nat, Nat.add(Nat.add(k, w), ux), Nat.add(k, Nat.add(w, ux)), Nat.add(w, Nat.add(k, ux)), NL.Nat.add_assoc(k, w, ux), NL.Nat.add_swap(k, w, ux)))),
          Equal.sym(Nat, Nat.add(w, 1n+Nat.add(k, ux)), 1n+Nat.add(w, Nat.add(k, ux)), NL.Nat.add_succ_r(w, Nat.add(k, ux)))))
      +fx = Equal.sym(Nat, Nat.add(x, ab), Nat.add(k, Nat.add(w, ab)), ex)
      %fx : {RD.Nat.lt(_, Nat.add(k, vb)) == RD.Nat.lt(a, v) : Bool}
      Equal.trans(Bool, RD.Nat.lt(Nat.add(k, Nat.add(w, ab)), Nat.add(k, vb)), RD.Nat.lt(Nat.add(w, ab), vb), RD.Nat.lt(a, v),
        Lt.shift(k, Nat.add(w, ab), vb), Lt.lo(bb, w, Nat.add(k, ux), hb, a, v))

# the same, with the lower parts' verdict acc as a carry into y
def Cmp.step(+bb: Nat, +x: Nat, +y: Nat, +a: Nat, +v: Nat, +ux: Nat, +hx: {bb == Nat.add(1n+x, ux) : Nat}, +uy: Nat, +hy: {bb == Nat.add(1n+y, uy) : Nat},
  acc: Bool, b: Bool, +eb: {RD.Nat.lt(x, Nat.add(B.Bn.c(acc), y)) == b : Bool})
  -> {RD.Nat.lt(Nat.add(x, Nat.mul(a, bb)), Nat.add(B.Bn.c(acc), Nat.add(y, Nat.mul(v, bb)))) == RD.Nat.lt(a, Nat.add(B.Bn.c(b), v)) : Bool}:
  match acc:
    case True{}:
      Cmp.k(bb, x, 1n+y, a, v, ux, hx, uy, hy, b, eb)
    case False{}:
      Cmp.k(bb, x, y, a, v, ux, hx, 1n+uy, Equal.trans(Nat, bb, 1n+Nat.add(y, uy), Nat.add(y, 1n+uy), hy, Equal.sym(Nat, Nat.add(y, 1n+uy), 1n+Nat.add(y, uy), NL.Nat.add_succ_r(y, uy))), b, eb)

# Bn.lt.go compares values: a < b + [acc]
def Cmp.go(+h: Nat, a: B.Bn, b: B.Bn, +acc: Bool, +oa: {B.Bn.ok(h, a) == True{} : Bool}, +ob: {B.Bn.ok(h, b) == True{} : Bool})
  -> {B.Bn.lt.go(a, b, acc) == RD.Nat.lt(B.Bn.val(h, a), Nat.add(B.Bn.c(acc), B.Bn.val(h, b))) : Bool}:
  match a b:
    case B.BNil{} B.BNil{}:
      match acc:
        case True{}:
          {==}
        case False{}:
          {==}
    case B.BCons{+x, +xs} B.BNil{}:
      +bb = Nat.double(h)
      +vx = B.Bn.val(h, xs)
      +ux = RD.Nat.monus(bb, 1n+x)
      +hx = Ok.hd(h, x, xs, oa)
      +b2 = F.Nat.ltf(x, Nat.add(B.Bn.c(acc), 0n))
      Equal.trans(Bool, B.Bn.lt.go(xs, B.BNil{}, b2), RD.Nat.lt(vx, Nat.add(B.Bn.c(b2), 0n)), RD.Nat.lt(Nat.add(x, Nat.mul(vx, bb)), Nat.add(B.Bn.c(acc), 0n)),
        Cmp.go(h, xs, B.BNil{}, b2, Ok.tl(h, x, xs, oa), ob),
        Equal.sym(Bool, RD.Nat.lt(Nat.add(x, Nat.mul(vx, bb)), Nat.add(B.Bn.c(acc), 0n)), RD.Nat.lt(vx, Nat.add(B.Bn.c(b2), 0n)),
          Cmp.step(bb, x, 0n, vx, 0n, ux, hx, Nat.add(x, ux), hx, acc, b2, FL.L.lt(x, Nat.add(B.Bn.c(acc), 0n)))))
    case B.BNil{} B.BCons{+y, +ys}:
      +bb = Nat.double(h)
      +vy = B.Bn.val(h, ys)
      +uy = RD.Nat.monus(bb, 1n+y)
      +hy = Ok.hd(h, y, ys, ob)
      +b2 = F.Nat.ltf(0n, Nat.add(B.Bn.c(acc), y))
      Equal.trans(Bool, B.Bn.lt.go(B.BNil{}, ys, b2), RD.Nat.lt(0n, Nat.add(B.Bn.c(b2), vy)), RD.Nat.lt(0n, Nat.add(B.Bn.c(acc), Nat.add(y, Nat.mul(vy, bb)))),
        Cmp.go(h, B.BNil{}, ys, b2, oa, Ok.tl(h, y, ys, ob)),
        Equal.sym(Bool, RD.Nat.lt(0n, Nat.add(B.Bn.c(acc), Nat.add(y, Nat.mul(vy, bb)))), RD.Nat.lt(0n, Nat.add(B.Bn.c(b2), vy)),
          Cmp.step(bb, 0n, y, 0n, vy, Nat.add(y, uy), hy, uy, hy, acc, b2, FL.L.lt(0n, Nat.add(B.Bn.c(acc), y)))))
    case B.BCons{+x, +xs} B.BCons{+y, +ys}:
      +bb = Nat.double(h)
      +vx = B.Bn.val(h, xs)
      +vy = B.Bn.val(h, ys)
      +b2 = F.Nat.ltf(x, Nat.add(B.Bn.c(acc), y))
      Equal.trans(Bool, B.Bn.lt.go(xs, ys, b2), RD.Nat.lt(vx, Nat.add(B.Bn.c(b2), vy)), RD.Nat.lt(Nat.add(x, Nat.mul(vx, bb)), Nat.add(B.Bn.c(acc), Nat.add(y, Nat.mul(vy, bb)))),
        Cmp.go(h, xs, ys, b2, Ok.tl(h, x, xs, oa), Ok.tl(h, y, ys, ob)),
        Equal.sym(Bool, RD.Nat.lt(Nat.add(x, Nat.mul(vx, bb)), Nat.add(B.Bn.c(acc), Nat.add(y, Nat.mul(vy, bb)))), RD.Nat.lt(vx, Nat.add(B.Bn.c(b2), vy)),
          Cmp.step(bb, x, y, vx, vy, RD.Nat.monus(bb, 1n+x), Ok.hd(h, x, xs, oa), RD.Nat.monus(bb, 1n+y), Ok.hd(h, y, ys, ob), acc, b2, FL.L.lt(x, Nat.add(B.Bn.c(acc), y)))))

def Cmp.lt(+h: Nat, +a: B.Bn, +b: B.Bn, +oa: {B.Bn.ok(h, a) == True{} : Bool}, +ob: {B.Bn.ok(h, b) == True{} : Bool})
  -> {B.Bn.lt(a, b) == RD.Nat.lt(B.Bn.val(h, a), B.Bn.val(h, b)) : Bool}:
  Cmp.go(h, a, b, False{}, oa, ob)

# Division
# --------

# Base's divmod.go counts m down to the next quotient step and r up: with
# B = 1 + m + r, it keeps q B + r + n and r < B
def Re1(+bb: Nat, +dd: Nat, +r: Nat, +np: Nat, +hb: {bb == 1n+r : Nat}) -> {Nat.add(Nat.add(Nat.add(bb, dd), 0n), np) == Nat.add(Nat.add(dd, r), 1n+np) : Nat}:
  +e1 = Equal.sym(Nat, bb, 1n+r, hb)
  %e1 : {Nat.add(Nat.add(Nat.add(_, dd), 0n), np) == Nat.add(Nat.add(dd, r), 1n+np) : Nat}
  +e2 = Equal.sym(Nat, Nat.add(Nat.add(dd, r), 1n+np), 1n+Nat.add(Nat.add(dd, r), np), NL.Nat.add_succ_r(Nat.add(dd, r), np))
  %e2 : {1n+Nat.add(Nat.add(Nat.add(r, dd), 0n), np) == _ : Nat}
  +e3 = Equal.sym(Nat, Nat.add(Nat.add(r, dd), 0n), Nat.add(r, dd), NL.Nat.add_zero_r(Nat.add(r, dd)))
  %e3 : {1n+Nat.add(_, np) == 1n+Nat.add(Nat.add(dd, r), np) : Nat}
  +e4 = Equal.sym(Nat, Nat.add(r, dd), Nat.add(dd, r), NL.Nat.add_comm(r, dd))
  %e4 : {1n+Nat.add(_, np) == 1n+Nat.add(Nat.add(dd, r), np) : Nat}
  {==}

def Re2(+dd: Nat, +r: Nat, +np: Nat) -> {Nat.add(Nat.add(dd, 1n+r), np) == Nat.add(Nat.add(dd, r), 1n+np) : Nat}:
  +e1 = Equal.sym(Nat, Nat.add(dd, 1n+r), 1n+Nat.add(dd, r), NL.Nat.add_succ_r(dd, r))
  %e1 : {Nat.add(_, np) == Nat.add(Nat.add(dd, r), 1n+np) : Nat}
  +e2 = Equal.sym(Nat, Nat.add(Nat.add(dd, r), 1n+np), 1n+Nat.add(Nat.add(dd, r), np), NL.Nat.add_succ_r(Nat.add(dd, r), np))
  %e2 : {1n+Nat.add(Nat.add(dd, r), np) == _ : Nat}
  {==}

def DM.go(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bb: Nat, +hb: {bb == 1n+Nat.add(m, r) : Nat})
  -> {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), bb), Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r))) == Nat.add(Nat.add(Nat.mul(d, bb), r), n) : Nat}
   & {RD.Nat.lt(Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)), bb) == True{} : Bool}:
  match n:
    case 0n:
      +hb2 = Equal.trans(Nat, bb, 1n+Nat.add(m, r), Nat.add(r, 1n+m), hb,
        Equal.trans(Nat, 1n+Nat.add(m, r), 1n+Nat.add(r, m), Nat.add(r, 1n+m), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(m, r), Nat.add(r, m), NL.Nat.add_comm(m, r)),
          Equal.sym(Nat, Nat.add(r, 1n+m), 1n+Nat.add(r, m), NL.Nat.add_succ_r(r, m))))
      +hb3 = Equal.sym(Nat, bb, Nat.add(r, 1n+m), hb2)
      (Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(d, bb), r), 0n), Nat.add(Nat.mul(d, bb), r), NL.Nat.add_zero_r(Nat.add(Nat.mul(d, bb), r))),
       Equal.trans(Bool, RD.Nat.lt(r, bb), RD.Nat.lt(r, Nat.add(r, 1n+m)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(r, z), bb, Nat.add(r, 1n+m), hb2), Lt.self(r, m)))
    case 1n+np:
      match m:
        case 0n:
          +hb1 = Equal.trans(Nat, bb, 1n+r, 1n+Nat.add(r, 0n), hb, Equal.cong(Nat, Nat, z => 1n+z, r, Nat.add(r, 0n), Equal.sym(Nat, Nat.add(r, 0n), r, NL.Nat.add_zero_r(r))))
          +q = Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))
          +rr = Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))
          (Equal.trans(Nat, Nat.add(Nat.mul(q, bb), rr), Nat.add(Nat.add(Nat.add(bb, Nat.mul(d, bb)), 0n), np), Nat.add(Nat.add(Nat.mul(d, bb), r), 1n+np),
             Pair.fst({Nat.add(Nat.mul(q, bb), rr) == Nat.add(Nat.add(Nat.mul(1n+d, bb), 0n), np) : Nat}, {RD.Nat.lt(rr, bb) == True{} : Bool}, DM.go(np, r, 1n+d, 0n, bb, hb1)),
             Re1(bb, Nat.mul(d, bb), r, np, hb)),
           Pair.snd({Nat.add(Nat.mul(q, bb), rr) == Nat.add(Nat.add(Nat.mul(1n+d, bb), 0n), np) : Nat}, {RD.Nat.lt(rr, bb) == True{} : Bool}, DM.go(np, r, 1n+d, 0n, bb, hb1)))
        case 1n+mp:
          +hb1 = Equal.trans(Nat, bb, 2n+Nat.add(mp, r), 1n+Nat.add(mp, 1n+r), hb, Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(mp, r), Nat.add(mp, 1n+r), Equal.sym(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), NL.Nat.add_succ_r(mp, r))))
          +q = Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r))
          +rr = Pair.snd(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r))
          (Equal.trans(Nat, Nat.add(Nat.mul(q, bb), rr), Nat.add(Nat.add(Nat.mul(d, bb), 1n+r), np), Nat.add(Nat.add(Nat.mul(d, bb), r), 1n+np),
             Pair.fst({Nat.add(Nat.mul(q, bb), rr) == Nat.add(Nat.add(Nat.mul(d, bb), 1n+r), np) : Nat}, {RD.Nat.lt(rr, bb) == True{} : Bool}, DM.go(np, mp, d, 1n+r, bb, hb1)),
             Re2(Nat.mul(d, bb), r, np)),
           Pair.snd({Nat.add(Nat.mul(q, bb), rr) == Nat.add(Nat.add(Nat.mul(d, bb), 1n+r), np) : Nat}, {RD.Nat.lt(rr, bb) == True{} : Bool}, DM.go(np, mp, d, 1n+r, bb, hb1)))

# a = div(a, B) B + mod(a, B), mod(a, B) < B, for B = 1 + bp
def DM(+a: Nat, +bp: Nat) -> {Nat.add(Nat.mul(Nat.div(a, 1n+bp), 1n+bp), Nat.mod(a, 1n+bp)) == a : Nat} & {RD.Nat.lt(Nat.mod(a, 1n+bp), 1n+bp) == True{} : Bool}:
  DM.go(a, bp, 0n, 0n, 1n+bp, Equal.cong(Nat, Nat, z => 1n+z, bp, Nat.add(bp, 0n), Equal.sym(Nat, Nat.add(bp, 0n), bp, NL.Nat.add_zero_r(bp))))

# Addition
# --------

def Dig.val.go(+bb: Nat, +s: Nat, b: Bool, +eb: {RD.Nat.lt(s, bb) == b : Bool})
  -> {Nat.add(Bool.pick(Nat, Bool.not(b), F.Nat.monusf(s, bb), s), Nat.mul(B.Bn.c(Bool.not(b)), bb)) == s : Nat}:
  match b:
    case True{}:
      NL.Nat.add_zero_r(s)
    case False{}:
      +m = RD.Nat.monus(s, bb)
      +hs = R.Nat.lt_f(s, bb)(eb)
      +em = FL.L.monus(s, bb)
      %em : {Nat.add(_, Nat.add(bb, 0n)) == s : Nat}
      Equal.trans(Nat, Nat.add(m, Nat.add(bb, 0n)), Nat.add(bb, m), s,
        Equal.trans(Nat, Nat.add(m, Nat.add(bb, 0n)), Nat.add(m, bb), Nat.add(bb, m), Equal.cong(Nat, Nat, z => Nat.add(m, z), Nat.add(bb, 0n), bb, NL.Nat.add_zero_r(bb)), NL.Nat.add_comm(m, bb)),
        Equal.sym(Nat, s, Nat.add(bb, m), hs))

def Dig.val(+bb: Nat, +s: Nat) -> {Nat.add(B.Bn.dig(s, bb), Nat.mul(B.Bn.c(B.Bn.cy(s, bb)), bb)) == s : Nat}:
  Dig.val.go(bb, s, F.Nat.ltf(s, bb), FL.L.lt(s, bb))

# d + cb B = c + x + y gives the limb identity of a sum
def Add.id(+bb: Nat, +x: Nat, +y: Nat, +vx: Nat, +vy: Nat, +cc: Nat, +d: Nat, +cb: Nat, hd: {Nat.add(d, Nat.mul(cb, bb)) == Nat.add(Nat.add(cc, x), y) : Nat})
  -> {Nat.add(d, Nat.mul(Nat.add(cb, Nat.add(vx, vy)), bb)) == Nat.add(cc, Nat.add(Nat.add(x, Nat.mul(vx, bb)), Nat.add(y, Nat.mul(vy, bb)))) : Nat}:
  +env : List<&2, Nat> = [0n, bb, x, y, vx, vy, cc, d, cb]
  R.NatN.eq2(env, R.Ad(R.V(7n), R.Ml(R.Ad(R.V(8n), R.Ad(R.V(4n), R.V(5n))), R.V(1n))), R.Ad(R.V(6n), R.Ad(R.Ad(R.V(2n), R.Ml(R.V(4n), R.V(1n))), R.Ad(R.V(3n), R.Ml(R.V(5n), R.V(1n))))),
    [], [], [R.Ad(R.Ad(R.V(7n), R.Ml(R.V(8n), R.V(1n))), R.Ng(R.Ad(R.Ad(R.V(6n), R.V(2n)), R.V(3n))))],
    {==}, Unit{}, (R.NatN.z(env, R.Ad(R.V(7n), R.Ml(R.V(8n), R.V(1n))), R.Ad(R.Ad(R.V(6n), R.V(2n)), R.V(3n)), {==}, {==}, hd), Unit{}), {==}, {==})

def Add.val(+h: Nat, a: B.Bn, b: B.Bn, +cy: Bool)
  -> {B.Bn.val(h, B.Bn.addc(h, a, b, cy)) == Nat.add(B.Bn.c(cy), Nat.add(B.Bn.val(h, a), B.Bn.val(h, b))) : Nat}:
  match a b:
    case B.BNil{} B.BNil{}:
      match cy:
        case True{}:
          {==}
        case False{}:
          {==}
    case B.BCons{+x, +xs} B.BNil{}:
      +bb = Nat.double(h)
      +s = Nat.add(Nat.add(B.Bn.c(cy), x), 0n)
      +c2 = B.Bn.cy(s, bb)
      +vx = B.Bn.val(h, xs)
      Equal.trans(Nat, Nat.add(B.Bn.dig(s, bb), Nat.mul(B.Bn.val(h, B.Bn.addc(h, xs, B.BNil{}, c2)), bb)), Nat.add(B.Bn.dig(s, bb), Nat.mul(Nat.add(B.Bn.c(c2), Nat.add(vx, 0n)), bb)), Nat.add(B.Bn.c(cy), Nat.add(Nat.add(x, Nat.mul(vx, bb)), 0n)),
        Equal.cong(Nat, Nat, z => Nat.add(B.Bn.dig(s, bb), Nat.mul(z, bb)), B.Bn.val(h, B.Bn.addc(h, xs, B.BNil{}, c2)), Nat.add(B.Bn.c(c2), Nat.add(vx, 0n)), Add.val(h, xs, B.BNil{}, c2)),
        Add.id(bb, x, 0n, vx, 0n, B.Bn.c(cy), B.Bn.dig(s, bb), B.Bn.c(c2), Dig.val(bb, s)))
    case B.BNil{} B.BCons{+y, +ys}:
      +bb = Nat.double(h)
      +s = Nat.add(Nat.add(B.Bn.c(cy), 0n), y)
      +c2 = B.Bn.cy(s, bb)
      +vy = B.Bn.val(h, ys)
      Equal.trans(Nat, Nat.add(B.Bn.dig(s, bb), Nat.mul(B.Bn.val(h, B.Bn.addc(h, B.BNil{}, ys, c2)), bb)), Nat.add(B.Bn.dig(s, bb), Nat.mul(Nat.add(B.Bn.c(c2), Nat.add(0n, vy)), bb)), Nat.add(B.Bn.c(cy), Nat.add(0n, Nat.add(y, Nat.mul(vy, bb)))),
        Equal.cong(Nat, Nat, z => Nat.add(B.Bn.dig(s, bb), Nat.mul(z, bb)), B.Bn.val(h, B.Bn.addc(h, B.BNil{}, ys, c2)), Nat.add(B.Bn.c(c2), Nat.add(0n, vy)), Add.val(h, B.BNil{}, ys, c2)),
        Add.id(bb, 0n, y, 0n, vy, B.Bn.c(cy), B.Bn.dig(s, bb), B.Bn.c(c2), Dig.val(bb, s)))
    case B.BCons{+x, +xs} B.BCons{+y, +ys}:
      +bb = Nat.double(h)
      +s = Nat.add(Nat.add(B.Bn.c(cy), x), y)
      +c2 = B.Bn.cy(s, bb)
      +vx = B.Bn.val(h, xs)
      +vy = B.Bn.val(h, ys)
      Equal.trans(Nat, Nat.add(B.Bn.dig(s, bb), Nat.mul(B.Bn.val(h, B.Bn.addc(h, xs, ys, c2)), bb)), Nat.add(B.Bn.dig(s, bb), Nat.mul(Nat.add(B.Bn.c(c2), Nat.add(vx, vy)), bb)), Nat.add(B.Bn.c(cy), Nat.add(Nat.add(x, Nat.mul(vx, bb)), Nat.add(y, Nat.mul(vy, bb)))),
        Equal.cong(Nat, Nat, z => Nat.add(B.Bn.dig(s, bb), Nat.mul(z, bb)), B.Bn.val(h, B.Bn.addc(h, xs, ys, c2)), Nat.add(B.Bn.c(c2), Nat.add(vx, vy)), Add.val(h, xs, ys, c2)),
        Add.id(bb, x, y, vx, vy, B.Bn.c(cy), B.Bn.dig(s, bb), B.Bn.c(c2), Dig.val(bb, s)))

def And.tt(+x: Bool, +y: Bool, ex: {x == True{} : Bool}, ey: {y == True{} : Bool}) -> {Bool.and(x, y) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(x, y), Bool.and(True{}, y), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, y), x, True{}, ex), ey)

def Cc(+cy: Bool) -> {Nat.add(B.Bn.c(cy), B.Bn.c(Bool.not(cy))) == 1n : Nat}:
  match cy:
    case True{}:
      {==}
    case False{}:
      {==}

# a limb sum of two limbs below B and a carry stays below 2B, so its digit is below B
def Dig.ok.go(+bb: Nat, +s: Nat, +x: Nat, +y: Nat, +ux: Nat, +uy: Nat, +cc: Nat, +cc2: Nat,
  hs: {s == Nat.add(Nat.add(cc, x), y) : Nat}, hc: {Nat.add(cc, cc2) == 1n : Nat}, hx: {bb == Nat.add(1n+x, ux) : Nat}, hy: {bb == Nat.add(1n+y, uy) : Nat},
  b: Bool, +eb: {RD.Nat.lt(s, bb) == b : Bool})
  -> {F.Nat.ltf(Bool.pick(Nat, Bool.not(b), F.Nat.monusf(s, bb), s), bb) == True{} : Bool}:
  match b:
    case True{}:
      Equal.trans(Bool, F.Nat.ltf(s, bb), RD.Nat.lt(s, bb), True{}, Equal.sym(Bool, RD.Nat.lt(s, bb), F.Nat.ltf(s, bb), FL.L.lt(s, bb)), eb)
    case False{}:
      +m = RD.Nat.monus(s, bb)
      +w = Nat.add(Nat.add(ux, uy), cc2)
      +hm = R.Nat.lt_f(s, bb)(eb)
      +env : List<&2, Nat> = [0n, 1n, bb, s, x, y, ux, uy, cc, cc2, m]
      +r1 = R.NatN.z(env, R.V(3n), R.Ad(R.V(2n), R.V(10n)), {==}, {==}, hm)
      +r2 = R.NatN.z(env, R.V(2n), R.Ad(R.Ad(R.V(1n), R.V(4n)), R.V(6n)), {==}, {==}, hx)
      +r3 = R.NatN.z(env, R.V(2n), R.Ad(R.Ad(R.V(1n), R.V(5n)), R.V(7n)), {==}, {==}, hy)
      +r4 = R.NatN.z(env, R.Ad(R.Ad(R.V(8n), R.V(4n)), R.V(5n)), R.V(3n), {==}, {==}, Equal.sym(Nat, s, Nat.add(Nat.add(cc, x), y), hs))
      +r5 = R.NatN.z(env, R.V(1n), R.Ad(R.V(8n), R.V(9n)), {==}, {==}, Equal.sym(Nat, Nat.add(cc, cc2), 1n, hc))
      +hb = R.NatN.eq2(env, R.V(2n), R.Ad(R.V(10n), R.Ad(R.V(1n), R.Ad(R.Ad(R.V(6n), R.V(7n)), R.V(9n)))),
        [], [], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(2n), R.V(10n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.Ad(R.V(1n), R.V(4n)), R.V(6n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.Ad(R.V(1n), R.V(5n)), R.V(7n)))), R.Ad(R.Ad(R.Ad(R.V(8n), R.V(4n)), R.V(5n)), R.Ng(R.V(3n))), R.Ad(R.V(1n), R.Ng(R.Ad(R.V(8n), R.V(9n))))],
        {==}, Unit{}, (r1, (r2, (r3, (r4, (r5, Unit{}))))), {==}, {==})
      +em = FL.L.monus(s, bb)
      %em : {F.Nat.ltf(_, bb) == True{} : Bool}
      +el = FL.L.lt(m, bb)
      %el : {_ == True{} : Bool}
      Equal.trans(Bool, RD.Nat.lt(m, bb), RD.Nat.lt(m, Nat.add(m, 1n+w)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(m, z), bb, Nat.add(m, 1n+w), hb), Lt.self(m, w))

def Dig.ok(+bb: Nat, +x: Nat, +y: Nat, +ux: Nat, +uy: Nat, hx: {bb == Nat.add(1n+x, ux) : Nat}, hy: {bb == Nat.add(1n+y, uy) : Nat}, +cy: Bool)
  -> {F.Nat.ltf(B.Bn.dig(Nat.add(Nat.add(B.Bn.c(cy), x), y), bb), bb) == True{} : Bool}:
  +s = Nat.add(Nat.add(B.Bn.c(cy), x), y)
  Dig.ok.go(bb, s, x, y, ux, uy, B.Bn.c(cy), B.Bn.c(Bool.not(cy)), {==}, Cc(cy), hx, hy, F.Nat.ltf(s, bb), FL.L.lt(s, bb))

# sums keep limbs below the base (h >= 1, so the top carry 1 is a limb)
def Add.ok(+h1: Nat, a: B.Bn, b: B.Bn, +cy: Bool, +oa: {B.Bn.ok(1n+h1, a) == True{} : Bool}, +ob: {B.Bn.ok(1n+h1, b) == True{} : Bool})
  -> {B.Bn.ok(1n+h1, B.Bn.addc(1n+h1, a, b, cy)) == True{} : Bool}:
  match a b:
    case B.BNil{} B.BNil{}:
      match cy:
        case True{}:
          {==}
        case False{}:
          {==}
    case B.BCons{+x, +xs} B.BNil{}:
      +bb = Nat.double(1n+h1)
      +s = Nat.add(Nat.add(B.Bn.c(cy), x), 0n)
      +ux = RD.Nat.monus(bb, 1n+x)
      +hx = Ok.hd(1n+h1, x, xs, oa)
      And.tt(F.Nat.ltf(B.Bn.dig(s, bb), bb), B.Bn.ok(1n+h1, B.Bn.addc(1n+h1, xs, B.BNil{}, B.Bn.cy(s, bb))),
        Dig.ok(bb, x, 0n, ux, Nat.add(x, ux), hx, hx, cy),
        Add.ok(h1, xs, B.BNil{}, B.Bn.cy(s, bb), Ok.tl(1n+h1, x, xs, oa), ob))
    case B.BNil{} B.BCons{+y, +ys}:
      +bb = Nat.double(1n+h1)
      +s = Nat.add(Nat.add(B.Bn.c(cy), 0n), y)
      +uy = RD.Nat.monus(bb, 1n+y)
      +hy = Ok.hd(1n+h1, y, ys, ob)
      And.tt(F.Nat.ltf(B.Bn.dig(s, bb), bb), B.Bn.ok(1n+h1, B.Bn.addc(1n+h1, B.BNil{}, ys, B.Bn.cy(s, bb))),
        Dig.ok(bb, 0n, y, Nat.add(y, uy), uy, hy, hy, cy),
        Add.ok(h1, B.BNil{}, ys, B.Bn.cy(s, bb), oa, Ok.tl(1n+h1, y, ys, ob)))
    case B.BCons{+x, +xs} B.BCons{+y, +ys}:
      +bb = Nat.double(1n+h1)
      +s = Nat.add(Nat.add(B.Bn.c(cy), x), y)
      And.tt(F.Nat.ltf(B.Bn.dig(s, bb), bb), B.Bn.ok(1n+h1, B.Bn.addc(1n+h1, xs, ys, B.Bn.cy(s, bb))),
        Dig.ok(bb, x, y, RD.Nat.monus(bb, 1n+x), RD.Nat.monus(bb, 1n+y), Ok.hd(1n+h1, x, xs, oa), Ok.hd(1n+h1, y, ys, ob), cy),
        Add.ok(h1, xs, ys, B.Bn.cy(s, bb), Ok.tl(1n+h1, x, xs, oa), Ok.tl(1n+h1, y, ys, ob)))

# Multiplication
# --------------

def Pd(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# a + (1 + k) is never a
def Ne.self(+a: Nat, +k: Nat, e: {Nat.add(a, 1n+k) == a : Nat}) -> Empty:
  match a:
    case 0n:
      Z.Bool.ft(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 1n+k, 0n, e))
    case 1n+j:
      Ne.self(j, k, Equal.cong(Nat, Nat, z => Pd(z), 1n+Nat.add(j, 1n+k), 1n+j, e))

def Dig1.val(+h: Nat, +c: Nat) -> {B.Bn.val(h, B.Bn.dig1(c)) == c : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+k:
      NL.Nat.add_zero_r(1n+k)

def MulD.id(+bb: Nat, +x: Nat, +y: Nat, +c: Nat, +vx: Nat, +md: Nat, +dv: Nat, hd: {Nat.add(Nat.mul(dv, bb), md) == Nat.add(Nat.mul(x, y), c) : Nat})
  -> {Nat.add(md, Nat.mul(Nat.add(Nat.mul(vx, y), dv), bb)) == Nat.add(Nat.mul(Nat.add(x, Nat.mul(vx, bb)), y), c) : Nat}:
  +env : List<&2, Nat> = [0n, bb, x, y, c, vx, md, dv]
  R.NatN.eq2(env, R.Ad(R.V(6n), R.Ml(R.Ad(R.Ml(R.V(5n), R.V(3n)), R.V(7n)), R.V(1n))), R.Ad(R.Ml(R.Ad(R.V(2n), R.Ml(R.V(5n), R.V(1n))), R.V(3n)), R.V(4n)),
    [], [], [R.Ad(R.Ad(R.Ml(R.V(7n), R.V(1n)), R.V(6n)), R.Ng(R.Ad(R.Ml(R.V(2n), R.V(3n)), R.V(4n))))],
    {==}, Unit{}, (R.NatN.z(env, R.Ad(R.Ml(R.V(7n), R.V(1n)), R.V(6n)), R.Ad(R.Ml(R.V(2n), R.V(3n)), R.V(4n)), {==}, {==}, hd), Unit{}), {==}, {==})

def MulD.val(+h1: Nat, a: B.Bn, +y: Nat, +c: Nat)
  -> {B.Bn.val(1n+h1, B.Bn.mulD(1n+h1, a, y, c)) == Nat.add(Nat.mul(B.Bn.val(1n+h1, a), y), c) : Nat}:
  match a:
    case B.BNil{}:
      Dig1.val(1n+h1, c)
    case B.BCons{+x, +xs}:
      +bb = Nat.double(1n+h1)
      +bp : Nat = 1n+Nat.double(h1)
      +s = Nat.add(Nat.mul(x, y), c)
      +vx = B.Bn.val(1n+h1, xs)
      +md = Nat.mod(s, bb)
      +dv = Nat.div(s, bb)
      Equal.trans(Nat, Nat.add(md, Nat.mul(B.Bn.val(1n+h1, B.Bn.mulD(1n+h1, xs, y, dv)), bb)), Nat.add(md, Nat.mul(Nat.add(Nat.mul(vx, y), dv), bb)), Nat.add(Nat.mul(Nat.add(x, Nat.mul(vx, bb)), y), c),
        Equal.cong(Nat, Nat, z => Nat.add(md, Nat.mul(z, bb)), B.Bn.val(1n+h1, B.Bn.mulD(1n+h1, xs, y, dv)), Nat.add(Nat.mul(vx, y), dv), MulD.val(h1, xs, y, dv)),
        MulD.id(bb, x, y, c, vx, md, dv, Pair.fst({Nat.add(Nat.mul(Nat.div(s, 1n+bp), 1n+bp), Nat.mod(s, 1n+bp)) == s : Nat}, {RD.Nat.lt(Nat.mod(s, 1n+bp), 1n+bp) == True{} : Bool}, DM(s, bp))))

def Lt.of(+c: Nat, +bb: Nat, +uc: Nat, hc: {bb == Nat.add(1n+c, uc) : Nat}) -> {F.Nat.ltf(c, bb) == True{} : Bool}:
  +e = Equal.trans(Nat, bb, 1n+Nat.add(c, uc), Nat.add(c, 1n+uc), hc, Equal.sym(Nat, Nat.add(c, 1n+uc), 1n+Nat.add(c, uc), NL.Nat.add_succ_r(c, uc)))
  Equal.trans(Bool, F.Nat.ltf(c, bb), RD.Nat.lt(c, bb), True{}, Equal.sym(Bool, RD.Nat.lt(c, bb), F.Nat.ltf(c, bb), FL.L.lt(c, bb)),
    Equal.trans(Bool, RD.Nat.lt(c, bb), RD.Nat.lt(c, Nat.add(c, 1n+uc)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(c, z), bb, Nat.add(c, 1n+uc), e), Lt.self(c, uc)))

# the carry of x y + c, all below B, is below B: else x y + c >= B B
def Cy.bound.go(+bp: Nat, +x: Nat, +y: Nat, +c: Nat, +ux: Nat, +uy: Nat, +uc: Nat,
  +hx: {1n+bp == Nat.add(1n+x, ux) : Nat}, hy: {1n+bp == Nat.add(1n+y, uy) : Nat}, hc: {1n+bp == Nat.add(1n+c, uc) : Nat},
  b: Bool, +eb: {RD.Nat.lt(Nat.div(Nat.add(Nat.mul(x, y), c), 1n+bp), 1n+bp) == b : Bool})
  -> {RD.Nat.lt(Nat.div(Nat.add(Nat.mul(x, y), c), 1n+bp), 1n+bp) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +bb : Nat = 1n+bp
      +s = Nat.add(Nat.mul(x, y), c)
      +q = Nat.div(s, bb)
      +md = Nat.mod(s, bb)
      +w = RD.Nat.monus(q, bb)
      +env : List<&2, Nat> = [0n, 1n, bb, x, y, c, ux, uy, uc, q, md, w]
      +o : N.Tm = R.V(1n)
      +ra = R.NatN.z(env, R.Ad(R.Ml(R.V(9n), R.V(2n)), R.V(10n)), R.Ad(R.Ml(R.V(3n), R.V(4n)), R.V(5n)), {==}, {==},
        Pair.fst({Nat.add(Nat.mul(q, bb), md) == s : Nat}, {RD.Nat.lt(md, bb) == True{} : Bool}, DM(s, bp)))
      +rq = R.NatN.z(env, R.V(9n), R.Ad(R.V(2n), R.V(11n)), {==}, {==}, R.Nat.lt_f(q, bb)(eb))
      +rx1 = R.NatN.z(env, R.V(2n), R.Ad(R.Ad(o, R.V(3n)), R.V(6n)), {==}, {==}, hx)
      +rx2 = R.NatN.z(env, R.V(2n), R.Ad(R.Ad(o, R.V(3n)), R.V(6n)), {==}, {==}, hx)
      +ry = R.NatN.z(env, R.V(2n), R.Ad(R.Ad(o, R.V(4n)), R.V(7n)), {==}, {==}, hy)
      +rc = R.NatN.z(env, R.Ad(R.Ad(o, R.V(5n)), R.V(8n)), R.V(2n), {==}, {==}, Equal.sym(Nat, bb, Nat.add(1n+c, uc), hc))
      +o1 = R.NatN.z(env, o, R.Ml(o, o), {==}, {==}, {==})
      +o2 = R.NatN.z(env, R.V(4n), R.Ml(o, R.V(4n)), {==}, {==}, Equal.sym(Nat, Nat.add(y, 0n), y, NL.Nat.add_zero_r(y)))
      +o3 = R.NatN.z(env, R.V(7n), R.Ml(o, R.V(7n)), {==}, {==}, Equal.sym(Nat, Nat.add(uy, 0n), uy, NL.Nat.add_zero_r(uy)))
      +o4 = R.NatN.z(env, R.V(3n), R.Ml(o, R.V(3n)), {==}, {==}, Equal.sym(Nat, Nat.add(x, 0n), x, NL.Nat.add_zero_r(x)))
      +o5 = R.NatN.z(env, R.V(6n), R.Ml(o, R.V(6n)), {==}, {==}, Equal.sym(Nat, Nat.add(ux, 0n), ux, NL.Nat.add_zero_r(ux)))
      +kw = R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.V(4n), R.V(7n)), R.V(8n)), R.Ml(R.V(3n), R.V(7n))), R.Ml(R.V(6n), R.V(4n))), R.Ml(R.V(6n), R.V(7n)))
      +kk = R.Ad(R.Ad(R.Ml(R.V(11n), R.V(2n)), R.V(10n)), kw)
      +e = R.NatN.eq2(env, R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ad(o, kk)), R.Ml(R.V(2n), R.V(2n)),
        [R.Ng(R.V(2n)), R.Ng(R.V(2n)), R.Ng(R.Ad(R.Ad(o, R.V(3n)), R.V(6n)))],
        [R.Ad(R.V(9n), R.Ng(R.Ad(R.V(2n), R.V(11n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.Ad(o, R.V(3n)), R.V(6n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.Ad(o, R.V(4n)), R.V(7n))))],
        [R.Ad(R.Ad(R.Ml(R.V(9n), R.V(2n)), R.V(10n)), R.Ng(R.Ad(R.Ml(R.V(3n), R.V(4n)), R.V(5n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.Ad(o, R.V(3n)), R.V(6n)))), R.Ad(R.Ad(R.Ad(o, R.V(5n)), R.V(8n)), R.Ng(R.V(2n))),
         R.Ad(o, R.Ng(R.Ml(o, o))), R.Ad(R.V(4n), R.Ng(R.Ml(o, R.V(4n)))), R.Ad(R.V(7n), R.Ng(R.Ml(o, R.V(7n)))), R.Ad(R.V(3n), R.Ng(R.Ml(o, R.V(3n)))), R.Ad(R.V(6n), R.Ng(R.Ml(o, R.V(6n))))],
        {==}, (rq, (rx1, (ry, Unit{}))), (ra, (rx2, (rc, (o1, (o2, (o3, (o4, (o5, Unit{})))))))), {==}, {==})
      Empty.absurd({RD.Nat.lt(q, bb) == True{} : Bool}, Ne.self(Nat.mul(bb, bb), R.NatN.eval(env, kk), e))

def Cy.bound(+bp: Nat, +x: Nat, +y: Nat, +c: Nat, +ux: Nat, +uy: Nat, +uc: Nat,
  hx: {1n+bp == Nat.add(1n+x, ux) : Nat}, hy: {1n+bp == Nat.add(1n+y, uy) : Nat}, hc: {1n+bp == Nat.add(1n+c, uc) : Nat})
  -> {RD.Nat.lt(Nat.div(Nat.add(Nat.mul(x, y), c), 1n+bp), 1n+bp) == True{} : Bool}:
  Cy.bound.go(bp, x, y, c, ux, uy, uc, hx, hy, hc, RD.Nat.lt(Nat.div(Nat.add(Nat.mul(x, y), c), 1n+bp), 1n+bp), {==})

def MulD.ok(+h1: Nat, a: B.Bn, +y: Nat, +c: Nat, +oa: {B.Bn.ok(1n+h1, a) == True{} : Bool},
  +uy: Nat, +hy: {Nat.double(1n+h1) == Nat.add(1n+y, uy) : Nat}, +uc: Nat, +hc: {Nat.double(1n+h1) == Nat.add(1n+c, uc) : Nat})
  -> {B.Bn.ok(1n+h1, B.Bn.mulD(1n+h1, a, y, c)) == True{} : Bool}:
  match a:
    case B.BNil{}:
      match c:
        case 0n:
          {==}
        case 1n+k:
          And.tt(F.Nat.ltf(1n+k, Nat.double(1n+h1)), True{}, Lt.of(1n+k, Nat.double(1n+h1), uc, hc), {==})
    case B.BCons{+x, +xs}:
      +bb = Nat.double(1n+h1)
      +bp : Nat = 1n+Nat.double(h1)
      +s = Nat.add(Nat.mul(x, y), c)
      +dv = Nat.div(s, bb)
      +md = Nat.mod(s, bb)
      +hdv = Lt.wit(dv, bb)(Cy.bound(bp, x, y, c, RD.Nat.monus(bb, 1n+x), uy, uc, Ok.hd(1n+h1, x, xs, oa), hy, hc))
      +hmd = Equal.trans(Bool, F.Nat.ltf(md, bb), RD.Nat.lt(md, bb), True{}, Equal.sym(Bool, RD.Nat.lt(md, bb), F.Nat.ltf(md, bb), FL.L.lt(md, bb)),
        Pair.snd({Nat.add(Nat.mul(dv, bb), md) == s : Nat}, {RD.Nat.lt(md, bb) == True{} : Bool}, DM(s, bp)))
      And.tt(F.Nat.ltf(md, bb), B.Bn.ok(1n+h1, B.Bn.mulD(1n+h1, xs, y, dv)), hmd,
        MulD.ok(h1, xs, y, dv, Ok.tl(1n+h1, x, xs, oa), uy, hy, RD.Nat.monus(bb, 1n+dv), hdv))

def Mul.id(+va: Nat, +y: Nat, +vr: Nat, +bb: Nat)
  -> {Nat.add(Nat.add(Nat.mul(va, y), 0n), Nat.mul(Nat.mul(va, vr), bb)) == Nat.mul(va, Nat.add(y, Nat.mul(vr, bb))) : Nat}:
  +env : List<&2, Nat> = [0n, va, y, vr, bb]
  R.NatN.eq(env, R.Ad(R.Ad(R.Ml(R.V(1n), R.V(2n)), N.TZero{}), R.Ml(R.Ml(R.V(1n), R.V(3n)), R.V(4n))), R.Ml(R.V(1n), R.Ad(R.V(2n), R.Ml(R.V(3n), R.V(4n)))), [], [], {==}, Unit{}, {==}, {==})

def Mul.val(+h1: Nat, +a: B.Bn, b: B.Bn) -> {B.Bn.val(1n+h1, B.Bn.mul(1n+h1, a, b)) == Nat.mul(B.Bn.val(1n+h1, a), B.Bn.val(1n+h1, b)) : Nat}:
  match b:
    case B.BNil{}:
      Equal.sym(Nat, Nat.mul(B.Bn.val(1n+h1, a), 0n), 0n, NL.Nat.mul_zero_r(B.Bn.val(1n+h1, a)))
    case B.BCons{+y, +ys}:
      +h : Nat = 1n+h1
      +bb = Nat.double(1n+h1)
      +va = B.Bn.val(h, a)
      +md = B.Bn.mulD(h, a, y, 0n)
      +rest = B.Bn.mul(h, a, ys)
      Equal.trans(Nat, B.Bn.val(h, B.Bn.add(h, md, B.BCons{0n, rest})), Nat.add(B.Bn.val(h, md), Nat.mul(B.Bn.val(h, rest), bb)), Nat.mul(va, Nat.add(y, Nat.mul(B.Bn.val(h, ys), bb))),
        Add.val(h, md, B.BCons{0n, rest}, False{}),
        Equal.trans(Nat, Nat.add(B.Bn.val(h, md), Nat.mul(B.Bn.val(h, rest), bb)), Nat.add(Nat.add(Nat.mul(va, y), 0n), Nat.mul(Nat.mul(va, B.Bn.val(h, ys)), bb)), Nat.mul(va, Nat.add(y, Nat.mul(B.Bn.val(h, ys), bb))),
          Equal.trans(Nat, Nat.add(B.Bn.val(h, md), Nat.mul(B.Bn.val(h, rest), bb)), Nat.add(Nat.add(Nat.mul(va, y), 0n), Nat.mul(B.Bn.val(h, rest), bb)), Nat.add(Nat.add(Nat.mul(va, y), 0n), Nat.mul(Nat.mul(va, B.Bn.val(h, ys)), bb)),
            Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(B.Bn.val(h, rest), bb)), B.Bn.val(h, md), Nat.add(Nat.mul(va, y), 0n), MulD.val(h1, a, y, 0n)),
            Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.mul(va, y), 0n), Nat.mul(z, bb)), B.Bn.val(h, rest), Nat.mul(va, B.Bn.val(h, ys)), Mul.val(h1, a, ys))),
          Mul.id(va, y, B.Bn.val(h, ys), bb)))

def Mul.ok(+h1: Nat, +a: B.Bn, b: B.Bn, +oa: {B.Bn.ok(1n+h1, a) == True{} : Bool}, +ob: {B.Bn.ok(1n+h1, b) == True{} : Bool})
  -> {B.Bn.ok(1n+h1, B.Bn.mul(1n+h1, a, b)) == True{} : Bool}:
  match b:
    case B.BNil{}:
      {==}
    case B.BCons{+y, +ys}:
      +h : Nat = 1n+h1
      +bb = Nat.double(1n+h1)
      +uy = RD.Nat.monus(bb, 1n+y)
      +hy = Ok.hd(h, y, ys, ob)
      Add.ok(h1, B.Bn.mulD(h, a, y, 0n), B.BCons{0n, B.Bn.mul(h, a, ys)}, False{},
        MulD.ok(h1, a, y, 0n, oa, uy, hy, Nat.add(y, uy), hy),
        And.tt(F.Nat.ltf(0n, bb), B.Bn.ok(h, B.Bn.mul(h, a, ys)), {==}, Mul.ok(h1, a, ys, oa, Ok.tl(h, y, ys, ob))))

# Halving and parity
# ------------------

def Ev.dw(+a: Nat, +w: Nat) -> {D.Nat.even(Nat.add(Nat.double(a), w)) == D.Nat.even(w) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+j:
      Ev.dw(j, w)

# the parity of d + V 2h is d's
def Ev.limb(+d: Nat, +v: Nat, +h: Nat) -> {D.Nat.even(Nat.add(d, Nat.mul(v, Nat.double(h)))) == D.Nat.even(d) : Bool}:
  +e1 = R.Nat.mul_double(v, h)
  +e2 = NL.Nat.add_comm(d, Nat.double(Nat.mul(v, h)))
  Equal.trans(Bool, D.Nat.even(Nat.add(d, Nat.mul(v, Nat.double(h)))), D.Nat.even(Nat.add(Nat.double(Nat.mul(v, h)), d)), D.Nat.even(d),
    Equal.cong(Nat, Bool, z => D.Nat.even(z), Nat.add(d, Nat.mul(v, Nat.double(h))), Nat.add(Nat.double(Nat.mul(v, h)), d),
      Equal.trans(Nat, Nat.add(d, Nat.mul(v, Nat.double(h))), Nat.add(d, Nat.double(Nat.mul(v, h))), Nat.add(Nat.double(Nat.mul(v, h)), d), Equal.cong(Nat, Nat, z => Nat.add(d, z), Nat.mul(v, Nat.double(h)), Nat.double(Nat.mul(v, h)), e1), e2)),
    Ev.dw(Nat.mul(v, h), d))

def Even.val(+h: Nat, b: B.Bn) -> {B.Bn.even(b) == D.Nat.even(B.Bn.val(h, b)) : Bool}:
  match b:
    case B.BNil{}:
      {==}
    case B.BCons{+d, +r}:
      Equal.trans(Bool, F.Nat.evenf(d), D.Nat.even(d), D.Nat.even(Nat.add(d, Nat.mul(B.Bn.val(h, r), Nat.double(h)))),
        Equal.sym(Bool, D.Nat.even(d), F.Nat.evenf(d), FL.L.even(d)),
        Equal.sym(Bool, D.Nat.even(Nat.add(d, Nat.mul(B.Bn.val(h, r), Nat.double(h)))), D.Nat.even(d), Ev.limb(d, B.Bn.val(h, r), h)))

def Bit0.val(+h: Nat, b: B.Bn) -> {B.Bn.bit0(b) == RD.Nat.bit(B.Bn.val(h, b)) : Nat}:
  match b:
    case B.BNil{}:
      {==}
    case B.BCons{+d, +r}:
      Equal.trans(Nat, F.Nat.bitf(d), RD.Nat.bit(d), RD.Nat.bit(Nat.add(d, Nat.mul(B.Bn.val(h, r), Nat.double(h)))),
        Equal.sym(Nat, RD.Nat.bit(d), F.Nat.bitf(d), FL.L.bit(d)),
        Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 0n, 1n), D.Nat.even(d), D.Nat.even(Nat.add(d, Nat.mul(B.Bn.val(h, r), Nat.double(h)))),
          Equal.sym(Bool, D.Nat.even(Nat.add(d, Nat.mul(B.Bn.val(h, r), Nat.double(h)))), D.Nat.even(d), Ev.limb(d, B.Bn.val(h, r), h))))

# half(d + V 2h) = half(d) + V h
def Half.limb(+d: Nat, +v: Nat, +h: Nat) -> {D.Nat.half(Nat.add(d, Nat.mul(v, Nat.double(h)))) == Nat.add(D.Nat.half(d), Nat.mul(v, h)) : Nat}:
  +x = Nat.mul(v, h)
  Equal.trans(Nat, D.Nat.half(Nat.add(d, Nat.mul(v, Nat.double(h)))), D.Nat.half(Nat.add(Nat.double(x), d)), Nat.add(D.Nat.half(d), x),
    Equal.cong(Nat, Nat, z => D.Nat.half(z), Nat.add(d, Nat.mul(v, Nat.double(h))), Nat.add(Nat.double(x), d),
      Equal.trans(Nat, Nat.add(d, Nat.mul(v, Nat.double(h))), Nat.add(d, Nat.double(x)), Nat.add(Nat.double(x), d),
        Equal.cong(Nat, Nat, z => Nat.add(d, z), Nat.mul(v, Nat.double(h)), Nat.double(x), R.Nat.mul_double(v, h)), NL.Nat.add_comm(d, Nat.double(x)))),
    Equal.trans(Nat, D.Nat.half(Nat.add(Nat.double(x), d)), Nat.add(x, D.Nat.half(d)), Nat.add(D.Nat.half(d), x), R.Nat.half_dw(x, d), NL.Nat.add_comm(x, D.Nat.half(d))))

def Half.id(+h: Nat, +v: Nat, +hd: Nat, +hv: Nat, +bv: Nat, hs: {v == Nat.add(Nat.double(hv), bv) : Nat})
  -> {Nat.add(Nat.add(hd, Nat.mul(h, bv)), Nat.mul(hv, Nat.double(h))) == Nat.add(hd, Nat.mul(v, h)) : Nat}:
  +env : List<&2, Nat> = [0n, h, v, hd, hv, bv, Nat.double(h), Nat.double(hv)]
  +rdh = R.NatN.z(env, R.V(6n), R.Ad(R.V(1n), R.V(1n)), {==}, {==}, Y.Nat.double_add(h))
  +rdv = R.NatN.z(env, R.V(7n), R.Ad(R.V(4n), R.V(4n)), {==}, {==}, Y.Nat.double_add(hv))
  +rv = R.NatN.z(env, R.V(2n), R.Ad(R.V(7n), R.V(5n)), {==}, {==}, hs)
  R.NatN.eq(env, R.Ad(R.Ad(R.V(3n), R.Ml(R.V(1n), R.V(5n))), R.Ml(R.V(4n), R.V(6n))), R.Ad(R.V(3n), R.Ml(R.V(2n), R.V(1n))),
    [R.V(4n), R.Ng(R.V(1n)), R.Ng(R.V(1n))], [R.Ad(R.V(6n), R.Ng(R.Ad(R.V(1n), R.V(1n)))), R.Ad(R.V(7n), R.Ng(R.Ad(R.V(4n), R.V(4n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.V(7n), R.V(5n))))],
    {==}, (rdh, (rdv, (rv, Unit{}))), {==}, {==})

def Half.val(+h: Nat, b: B.Bn) -> {B.Bn.val(h, B.Bn.half(h, b)) == D.Nat.half(B.Bn.val(h, b)) : Nat}:
  match b:
    case B.BNil{}:
      {==}
    case B.BCons{+d, +r}:
      +v = B.Bn.val(h, r)
      +hd = D.Nat.half(d)
      +hv = D.Nat.half(v)
      +bv = RD.Nat.bit(v)
      +lhs = Nat.add(Nat.add(F.Nat.halff(d), Nat.mul(h, B.Bn.bit0(r))), Nat.mul(B.Bn.val(h, B.Bn.half(h, r)), Nat.double(h)))
      +e1 = Equal.trans(Nat, lhs, Nat.add(Nat.add(hd, Nat.mul(h, B.Bn.bit0(r))), Nat.mul(B.Bn.val(h, B.Bn.half(h, r)), Nat.double(h))), Nat.add(Nat.add(hd, Nat.mul(h, bv)), Nat.mul(B.Bn.val(h, B.Bn.half(h, r)), Nat.double(h))),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.add(z, Nat.mul(h, B.Bn.bit0(r))), Nat.mul(B.Bn.val(h, B.Bn.half(h, r)), Nat.double(h))), F.Nat.halff(d), hd, Equal.sym(Nat, hd, F.Nat.halff(d), FL.L.half(d))),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.add(hd, Nat.mul(h, z)), Nat.mul(B.Bn.val(h, B.Bn.half(h, r)), Nat.double(h))), B.Bn.bit0(r), bv, Bit0.val(h, r)))
      +e2 = Equal.cong(Nat, Nat, z => Nat.add(Nat.add(hd, Nat.mul(h, bv)), Nat.mul(z, Nat.double(h))), B.Bn.val(h, B.Bn.half(h, r)), hv, Half.val(h, r))
      Equal.trans(Nat, lhs, Nat.add(Nat.add(hd, Nat.mul(h, bv)), Nat.mul(hv, Nat.double(h))), D.Nat.half(Nat.add(d, Nat.mul(v, Nat.double(h)))),
        Equal.trans(Nat, lhs, Nat.add(Nat.add(hd, Nat.mul(h, bv)), Nat.mul(B.Bn.val(h, B.Bn.half(h, r)), Nat.double(h))), Nat.add(Nat.add(hd, Nat.mul(h, bv)), Nat.mul(hv, Nat.double(h))), e1, e2),
        Equal.trans(Nat, Nat.add(Nat.add(hd, Nat.mul(h, bv)), Nat.mul(hv, Nat.double(h))), Nat.add(hd, Nat.mul(v, h)), D.Nat.half(Nat.add(d, Nat.mul(v, Nat.double(h)))),
          Half.id(h, v, hd, hv, bv, R.Nat.split2(v)),
          Equal.sym(Nat, D.Nat.half(Nat.add(d, Nat.mul(v, Nat.double(h)))), Nat.add(hd, Nat.mul(v, h)), Half.limb(d, v, h))))

# half(d) < h when d < 2h
def Half.lt.go(+h: Nat, +d: Nat, +ud: Nat, +hd: {Nat.double(h) == Nat.add(1n+d, ud) : Nat}, b: Bool, +eb: {RD.Nat.lt(D.Nat.half(d), h) == b : Bool})
  -> {RD.Nat.lt(D.Nat.half(d), h) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +hf = D.Nat.half(d)
      +w = RD.Nat.monus(hf, h)
      +env : List<&2, Nat> = [0n, 1n, h, d, ud, hf, w, Nat.double(h), Nat.double(hf), RD.Nat.bit(d)]
      +r1 = R.NatN.z(env, R.Ad(R.Ad(R.V(1n), R.V(3n)), R.V(4n)), R.V(7n), {==}, {==}, Equal.sym(Nat, Nat.double(h), Nat.add(1n+d, ud), hd))
      +r2 = R.NatN.z(env, R.V(7n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, Y.Nat.double_add(h))
      +r3 = R.NatN.z(env, R.Ad(R.V(8n), R.V(9n)), R.V(3n), {==}, {==}, Equal.sym(Nat, d, Nat.add(Nat.double(hf), RD.Nat.bit(d)), R.Nat.split2(d)))
      +r4 = R.NatN.z(env, R.Ad(R.V(5n), R.V(5n)), R.V(8n), {==}, {==}, Equal.sym(Nat, Nat.double(hf), Nat.add(hf, hf), Y.Nat.double_add(hf)))
      +r5 = R.NatN.z(env, R.Ad(R.V(2n), R.V(6n)), R.V(5n), {==}, {==}, Equal.sym(Nat, hf, Nat.add(h, w), R.Nat.lt_f(hf, h)(eb)))
      +r6 = R.NatN.z(env, R.Ad(R.V(2n), R.V(6n)), R.V(5n), {==}, {==}, Equal.sym(Nat, hf, Nat.add(h, w), R.Nat.lt_f(hf, h)(eb)))
      # 2h + (1 + 2w + bit + ud) = 2h
      +kk = R.Ad(R.Ad(R.Ad(R.V(6n), R.V(6n)), R.V(9n)), R.V(4n))
      +e = R.NatN.eq2(env, R.Ad(R.V(7n), R.Ad(R.V(1n), kk)), R.V(7n), [], [],
        [R.Ad(R.Ad(R.V(8n), R.V(9n)), R.Ng(R.V(3n))), R.Ad(R.Ad(R.Ad(R.V(1n), R.V(3n)), R.V(4n)), R.Ng(R.V(7n))), R.Ad(R.V(7n), R.Ng(R.Ad(R.V(2n), R.V(2n)))),
         R.Ad(R.Ad(R.V(5n), R.V(5n)), R.Ng(R.V(8n))), R.Ad(R.Ad(R.V(2n), R.V(6n)), R.Ng(R.V(5n))), R.Ad(R.Ad(R.V(2n), R.V(6n)), R.Ng(R.V(5n)))],
        {==}, Unit{}, (r3, (r1, (r2, (r4, (r5, (r6, Unit{})))))), {==}, {==})
      Empty.absurd({RD.Nat.lt(hf, h) == True{} : Bool}, Ne.self(Nat.double(h), R.NatN.eval(env, kk), e))

def Half.lt(+h: Nat, +d: Nat, +ud: Nat, +hd: {Nat.double(h) == Nat.add(1n+d, ud) : Nat}) -> {RD.Nat.lt(D.Nat.half(d), h) == True{} : Bool}:
  Half.lt.go(h, d, ud, hd, RD.Nat.lt(D.Nat.half(d), h), {==})

# the halved limb half(d) + h bit stays below 2h
def Half.dig(+h: Nat, +d: Nat, +ud: Nat, +hd: {Nat.double(h) == Nat.add(1n+d, ud) : Nat}, +v: Nat)
  -> {RD.Nat.lt(Nat.add(D.Nat.half(d), Nat.mul(h, RD.Nat.bit(v))), Nat.double(h)) == True{} : Bool}:
  +hf = D.Nat.half(d)
  +b0 = RD.Nat.bit(v)
  +b1 = RD.Nat.monus(1n, b0)
  +wh = RD.Nat.monus(h, 1n+hf)
  +dg = Nat.add(hf, Nat.mul(h, b0))
  +w = Nat.add(wh, Nat.mul(h, b1))
  +env : List<&2, Nat> = [0n, 1n, h, hf, wh, b0, b1, Nat.double(h)]
  +rd = R.NatN.z(env, R.V(7n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, Y.Nat.double_add(h))
  +rh = R.NatN.z(env, R.V(2n), R.Ad(R.Ad(R.V(1n), R.V(3n)), R.V(4n)), {==}, {==}, Lt.wit(hf, h)(Half.lt(h, d, ud, hd)))
  +ro = R.NatN.z(env, R.V(2n), R.Ml(R.V(1n), R.V(2n)), {==}, {==}, Equal.sym(Nat, Nat.add(h, 0n), h, NL.Nat.add_zero_r(h)))
  +rb = R.NatN.z(env, R.Ad(R.V(5n), R.V(6n)), R.V(1n), {==}, {==}, R.Nat.bit01(v))
  +e = R.NatN.eq2(env, R.V(7n), R.Ad(R.Ad(R.V(3n), R.Ml(R.V(2n), R.V(5n))), R.Ad(R.V(1n), R.Ad(R.V(4n), R.Ml(R.V(2n), R.V(6n))))),
    [R.Ng(R.V(2n))], [R.Ad(R.Ad(R.V(5n), R.V(6n)), R.Ng(R.V(1n)))],
    [R.Ad(R.V(7n), R.Ng(R.Ad(R.V(2n), R.V(2n)))), R.Ad(R.V(2n), R.Ng(R.Ad(R.Ad(R.V(1n), R.V(3n)), R.V(4n)))), R.Ad(R.V(2n), R.Ng(R.Ml(R.V(1n), R.V(2n))))],
    {==}, (rb, Unit{}), (rd, (rh, (ro, Unit{}))), {==}, {==})
  Equal.trans(Bool, RD.Nat.lt(dg, Nat.double(h)), RD.Nat.lt(dg, Nat.add(dg, 1n+w)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(dg, z), Nat.double(h), Nat.add(dg, 1n+w), e), Lt.self(dg, w))

def Half.ok(+h: Nat, b: B.Bn, +ob: {B.Bn.ok(h, b) == True{} : Bool}) -> {B.Bn.ok(h, B.Bn.half(h, b)) == True{} : Bool}:
  match b:
    case B.BNil{}:
      {==}
    case B.BCons{+d, +r}:
      +dh = Nat.double(h)
      +v = B.Bn.val(h, r)
      +dg = Nat.add(F.Nat.halff(d), Nat.mul(h, B.Bn.bit0(r)))
      +dg2 = Nat.add(D.Nat.half(d), Nat.mul(h, RD.Nat.bit(v)))
      +edg = Equal.trans(Nat, dg, Nat.add(D.Nat.half(d), Nat.mul(h, B.Bn.bit0(r))), dg2,
        Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(h, B.Bn.bit0(r))), F.Nat.halff(d), D.Nat.half(d), Equal.sym(Nat, D.Nat.half(d), F.Nat.halff(d), FL.L.half(d))),
        Equal.cong(Nat, Nat, z => Nat.add(D.Nat.half(d), Nat.mul(h, z)), B.Bn.bit0(r), RD.Nat.bit(v), Bit0.val(h, r)))
      +hl = Equal.trans(Bool, F.Nat.ltf(dg, dh), RD.Nat.lt(dg, dh), True{}, Equal.sym(Bool, RD.Nat.lt(dg, dh), F.Nat.ltf(dg, dh), FL.L.lt(dg, dh)),
        Equal.trans(Bool, RD.Nat.lt(dg, dh), RD.Nat.lt(dg2, dh), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, dh), dg, dg2, edg),
          Half.dig(h, d, RD.Nat.monus(dh, 1n+d), Ok.hd(h, d, r, ob), v)))
      And.tt(F.Nat.ltf(dg, dh), B.Bn.ok(h, B.Bn.half(h, r)), hl, Half.ok(h, r, Ok.tl(h, d, r, ob)))

# Shifts and conversion
# ---------------------

def Shl.val(+h1: Nat, +k: Nat, +b: B.Bn) -> {B.Bn.val(1n+h1, B.Bn.shl(1n+h1, k, b)) == Nat.mul(B.Bn.val(1n+h1, b), RD.Nat.pow2(k)) : Nat}:
  match k:
    case 0n:
      Equal.sym(Nat, Nat.mul(B.Bn.val(1n+h1, b), 1n), B.Bn.val(1n+h1, b), NL.Nat.mul_one_r(B.Bn.val(1n+h1, b)))
    case 1n+j:
      +h : Nat = 1n+h1
      +s = B.Bn.shl(h, j, b)
      +m = Nat.mul(B.Bn.val(h, b), RD.Nat.pow2(j))
      Equal.trans(Nat, B.Bn.val(h, B.Bn.add(h, s, s)), Nat.add(B.Bn.val(h, s), B.Bn.val(h, s)), Nat.mul(B.Bn.val(h, b), Nat.double(RD.Nat.pow2(j))),
        Add.val(h, s, s, False{}),
        Equal.trans(Nat, Nat.add(B.Bn.val(h, s), B.Bn.val(h, s)), Nat.add(m, m), Nat.mul(B.Bn.val(h, b), Nat.double(RD.Nat.pow2(j))),
          Equal.trans(Nat, Nat.add(B.Bn.val(h, s), B.Bn.val(h, s)), Nat.add(m, B.Bn.val(h, s)), Nat.add(m, m),
            Equal.cong(Nat, Nat, z => Nat.add(z, B.Bn.val(h, s)), B.Bn.val(h, s), m, Shl.val(h1, j, b)),
            Equal.cong(Nat, Nat, z => Nat.add(m, z), B.Bn.val(h, s), m, Shl.val(h1, j, b))),
          Equal.trans(Nat, Nat.add(m, m), Nat.double(m), Nat.mul(B.Bn.val(h, b), Nat.double(RD.Nat.pow2(j))),
            Equal.sym(Nat, Nat.double(m), Nat.add(m, m), Y.Nat.double_add(m)),
            Equal.sym(Nat, Nat.mul(B.Bn.val(h, b), Nat.double(RD.Nat.pow2(j))), Nat.double(m), R.Nat.mul_double(B.Bn.val(h, b), RD.Nat.pow2(j))))))

def Shl.ok(+h1: Nat, +k: Nat, +b: B.Bn, +ob: {B.Bn.ok(1n+h1, b) == True{} : Bool}) -> {B.Bn.ok(1n+h1, B.Bn.shl(1n+h1, k, b)) == True{} : Bool}:
  match k:
    case 0n:
      ob
    case 1n+j:
      Add.ok(h1, B.Bn.shl(1n+h1, j, b), B.Bn.shl(1n+h1, j, b), False{}, Shl.ok(h1, j, b, ob), Shl.ok(h1, j, b, ob))

def Pow2.val(+h1: Nat, +k: Nat) -> {B.Bn.val(1n+h1, B.Bn.pow2(1n+h1, k)) == RD.Nat.pow2(k) : Nat}:
  Equal.trans(Nat, B.Bn.val(1n+h1, B.Bn.pow2(1n+h1, k)), Nat.mul(1n, RD.Nat.pow2(k)), RD.Nat.pow2(k), Shl.val(h1, k, B.BCons{1n, B.BNil{}}), NL.Nat.add_zero_r(RD.Nat.pow2(k)))

def Pow2.ok(+h1: Nat, +k: Nat) -> {B.Bn.ok(1n+h1, B.Bn.pow2(1n+h1, k)) == True{} : Bool}:
  Shl.ok(h1, k, B.BCons{1n, B.BNil{}}, {==})

def Of.val(+h1: Nat, +n: Nat) -> {B.Bn.val(1n+h1, B.Bn.of(1n+h1, n)) == n : Nat}:
  +bb = Nat.double(1n+h1)
  +bp : Nat = 1n+Nat.double(h1)
  +q = Nat.div(n, bb)
  +md = Nat.mod(n, bb)
  Equal.trans(Nat, Nat.add(md, Nat.mul(B.Bn.val(1n+h1, B.Bn.dig1(q)), bb)), Nat.add(md, Nat.mul(q, bb)), n,
    Equal.cong(Nat, Nat, z => Nat.add(md, Nat.mul(z, bb)), B.Bn.val(1n+h1, B.Bn.dig1(q)), q, Dig1.val(1n+h1, q)),
    Equal.trans(Nat, Nat.add(md, Nat.mul(q, bb)), Nat.add(Nat.mul(q, bb), md), n, NL.Nat.add_comm(md, Nat.mul(q, bb)),
      Pair.fst({Nat.add(Nat.mul(q, bb), md) == n : Nat}, {RD.Nat.lt(md, bb) == True{} : Bool}, DM(n, bp))))

# n < B B gives div(n, B) < B
def Div.bound.go(+bp: Nat, +n: Nat, +un: Nat, +hn: {Nat.mul(1n+bp, 1n+bp) == Nat.add(1n+n, un) : Nat}, b: Bool, +eb: {RD.Nat.lt(Nat.div(n, 1n+bp), 1n+bp) == b : Bool})
  -> {RD.Nat.lt(Nat.div(n, 1n+bp), 1n+bp) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +bb : Nat = 1n+bp
      +q = Nat.div(n, bb)
      +md = Nat.mod(n, bb)
      +w = RD.Nat.monus(q, bb)
      +env : List<&2, Nat> = [0n, 1n, bb, n, un, q, md, w]
      +ra = R.NatN.z(env, R.Ad(R.Ml(R.V(5n), R.V(2n)), R.V(6n)), R.V(3n), {==}, {==}, Pair.fst({Nat.add(Nat.mul(q, bb), md) == n : Nat}, {RD.Nat.lt(md, bb) == True{} : Bool}, DM(n, bp)))
      +rn = R.NatN.z(env, R.Ad(R.Ad(R.V(1n), R.V(3n)), R.V(4n)), R.Ml(R.V(2n), R.V(2n)), {==}, {==}, Equal.sym(Nat, Nat.mul(bb, bb), Nat.add(1n+n, un), hn))
      +rq = R.NatN.z(env, R.V(5n), R.Ad(R.V(2n), R.V(7n)), {==}, {==}, R.Nat.lt_f(q, bb)(eb))
      +kk = R.Ad(R.Ad(R.Ml(R.V(7n), R.V(2n)), R.V(6n)), R.V(4n))
      +e = R.NatN.eq2(env, R.Ad(R.Ml(R.V(2n), R.V(2n)), R.Ad(R.V(1n), kk)), R.Ml(R.V(2n), R.V(2n)), [R.Ng(R.V(2n))], [R.Ad(R.V(5n), R.Ng(R.Ad(R.V(2n), R.V(7n))))],
        [R.Ad(R.Ad(R.Ml(R.V(5n), R.V(2n)), R.V(6n)), R.Ng(R.V(3n))), R.Ad(R.Ad(R.Ad(R.V(1n), R.V(3n)), R.V(4n)), R.Ng(R.Ml(R.V(2n), R.V(2n))))],
        {==}, (rq, Unit{}), (ra, (rn, Unit{})), {==}, {==})
      Empty.absurd({RD.Nat.lt(q, bb) == True{} : Bool}, Ne.self(Nat.mul(bb, bb), R.NatN.eval(env, kk), e))

def Of.ok(+h1: Nat, +n: Nat, +un: Nat, +hn: {Nat.mul(Nat.double(1n+h1), Nat.double(1n+h1)) == Nat.add(1n+n, un) : Nat}) -> {B.Bn.ok(1n+h1, B.Bn.of(1n+h1, n)) == True{} : Bool}:
  +bb = Nat.double(1n+h1)
  +bp : Nat = 1n+Nat.double(h1)
  +q = Nat.div(n, bb)
  +md = Nat.mod(n, bb)
  +hq = Lt.wit(q, bb)(Div.bound.go(bp, n, un, hn, RD.Nat.lt(q, bb), {==}))
  +hm = Equal.trans(Bool, F.Nat.ltf(md, bb), RD.Nat.lt(md, bb), True{}, Equal.sym(Bool, RD.Nat.lt(md, bb), F.Nat.ltf(md, bb), FL.L.lt(md, bb)),
    Pair.snd({Nat.add(Nat.mul(q, bb), md) == n : Nat}, {RD.Nat.lt(md, bb) == True{} : Bool}, DM(n, bp)))
  And.tt(F.Nat.ltf(md, bb), B.Bn.ok(1n+h1, B.Bn.dig1(q)), hm,
    MulD.ok(h1, B.BNil{}, 0n, q, {==}, 1n+Nat.double(h1), {==}, RD.Nat.monus(bb, 1n+q), hq))

# Subtraction
# -----------

# a borrowing limb: (x + [bw] B) - t, t <= B, then adding t back
def Sdig(+x: Nat, +t: Nat, +bb: Nat, +ub: Nat, +hb: {bb == Nat.add(t, ub) : Nat}, bw: Bool, +eb: {RD.Nat.lt(x, t) == bw : Bool})
  -> {Nat.add(RD.Nat.monus(Nat.add(x, Nat.mul(B.Bn.c(bw), bb)), t), t) == Nat.add(x, Nat.mul(B.Bn.c(bw), bb)) : Nat}:
  match bw:
    case True{}:
      +m = Nat.add(x, Nat.add(bb, 0n))
      +env : List<&2, Nat> = [0n, x, t, bb, ub]
      +hm = R.NatN.eq2(env, R.Ad(R.V(1n), R.Ad(R.V(3n), N.TZero{})), R.Ad(R.V(2n), R.Ad(R.V(1n), R.V(4n))), [], [], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(2n), R.V(4n))))],
        {==}, Unit{}, (R.NatN.z(env, R.V(3n), R.Ad(R.V(2n), R.V(4n)), {==}, {==}, hb), Unit{}), {==}, {==})
      Equal.trans(Nat, Nat.add(RD.Nat.monus(m, t), t), Nat.add(t, RD.Nat.monus(m, t)), m, NL.Nat.add_comm(RD.Nat.monus(m, t), t),
        Equal.sym(Nat, m, Nat.add(t, RD.Nat.monus(m, t)), R.Nat.monus_back(m, t, Nat.add(x, ub), hm)))
    case False{}:
      +m = Nat.add(x, 0n)
      +w = RD.Nat.monus(x, t)
      +hm = Equal.trans(Nat, m, x, Nat.add(t, w), NL.Nat.add_zero_r(x), R.Nat.lt_f(x, t)(eb))
      Equal.trans(Nat, Nat.add(RD.Nat.monus(m, t), t), Nat.add(t, RD.Nat.monus(m, t)), m, NL.Nat.add_comm(RD.Nat.monus(m, t), t),
        Equal.sym(Nat, m, Nat.add(t, RD.Nat.monus(m, t)), R.Nat.monus_back(m, t, w, hm)))

def Sub.dig.ok(+x: Nat, +t: Nat, +bb: Nat, +ux: Nat, +hx: {bb == Nat.add(1n+x, ux) : Nat}, bw: Bool, +eb: {RD.Nat.lt(x, t) == bw : Bool},
  +hs: {Nat.add(RD.Nat.monus(Nat.add(x, Nat.mul(B.Bn.c(bw), bb)), t), t) == Nat.add(x, Nat.mul(B.Bn.c(bw), bb)) : Nat})
  -> {RD.Nat.lt(RD.Nat.monus(Nat.add(x, Nat.mul(B.Bn.c(bw), bb)), t), bb) == True{} : Bool}:
  match bw:
    case True{}:
      +dg = RD.Nat.monus(Nat.add(x, Nat.add(bb, 0n)), t)
      +w = RD.Nat.monus(t, 1n+x)
      +env : List<&2, Nat> = [0n, 1n, x, t, bb, dg, w]
      +rt = R.NatN.z(env, R.V(3n), R.Ad(R.Ad(R.V(1n), R.V(2n)), R.V(6n)), {==}, {==}, Lt.wit(x, t)(eb))
      +rs = R.NatN.z(env, R.Ad(R.V(2n), R.Ad(R.V(4n), N.TZero{})), R.Ad(R.V(5n), R.V(3n)), {==}, {==}, Equal.sym(Nat, Nat.add(dg, t), Nat.add(x, Nat.add(bb, 0n)), hs))
      +e = R.NatN.eq2(env, R.V(4n), R.Ad(R.V(5n), R.Ad(R.V(1n), R.V(6n))), [], [],
        [R.Ad(R.V(3n), R.Ng(R.Ad(R.Ad(R.V(1n), R.V(2n)), R.V(6n)))), R.Ad(R.Ad(R.V(2n), R.Ad(R.V(4n), N.TZero{})), R.Ng(R.Ad(R.V(5n), R.V(3n))))],
        {==}, Unit{}, (rt, (rs, Unit{})), {==}, {==})
      Equal.trans(Bool, RD.Nat.lt(dg, bb), RD.Nat.lt(dg, Nat.add(dg, 1n+w)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(dg, z), bb, Nat.add(dg, 1n+w), e), Lt.self(dg, w))
    case False{}:
      +dg = RD.Nat.monus(Nat.add(x, 0n), t)
      +w = Nat.add(t, ux)
      +env : List<&2, Nat> = [0n, 1n, x, t, bb, dg, ux]
      +rx = R.NatN.z(env, R.V(4n), R.Ad(R.Ad(R.V(1n), R.V(2n)), R.V(6n)), {==}, {==}, hx)
      +rs = R.NatN.z(env, R.Ad(R.V(2n), N.TZero{}), R.Ad(R.V(5n), R.V(3n)), {==}, {==}, Equal.sym(Nat, Nat.add(dg, t), Nat.add(x, 0n), hs))
      +e = R.NatN.eq2(env, R.V(4n), R.Ad(R.V(5n), R.Ad(R.V(1n), R.Ad(R.V(3n), R.V(6n)))), [], [],
        [R.Ad(R.V(4n), R.Ng(R.Ad(R.Ad(R.V(1n), R.V(2n)), R.V(6n)))), R.Ad(R.Ad(R.V(2n), N.TZero{}), R.Ng(R.Ad(R.V(5n), R.V(3n))))],
        {==}, Unit{}, (rx, (rs, Unit{})), {==}, {==})
      Equal.trans(Bool, RD.Nat.lt(dg, bb), RD.Nat.lt(dg, Nat.add(dg, 1n+w)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(dg, z), bb, Nat.add(dg, 1n+w), e), Lt.self(dg, w))

# t = [br] + y <= B when y < B
def Sub.tb(+bb: Nat, +y: Nat, +uy: Nat, +hy: {bb == Nat.add(1n+y, uy) : Nat}, +br: Bool)
  -> {bb == Nat.add(Nat.add(B.Bn.c(br), y), Nat.add(B.Bn.c(Bool.not(br)), uy)) : Nat}:
  +c = B.Bn.c(br)
  +c2 = B.Bn.c(Bool.not(br))
  +env : List<&2, Nat> = [0n, 1n, bb, y, uy, c, c2]
  R.NatN.eq2(env, R.V(2n), R.Ad(R.Ad(R.V(5n), R.V(3n)), R.Ad(R.V(6n), R.V(4n))), [], [],
    [R.Ad(R.V(2n), R.Ng(R.Ad(R.Ad(R.V(1n), R.V(3n)), R.V(4n)))), R.Ad(R.V(1n), R.Ng(R.Ad(R.V(5n), R.V(6n))))],
    {==}, Unit{}, (R.NatN.z(env, R.V(2n), R.Ad(R.Ad(R.V(1n), R.V(3n)), R.V(4n)), {==}, {==}, hy), (R.NatN.z(env, R.V(1n), R.Ad(R.V(5n), R.V(6n)), {==}, {==}, Equal.sym(Nat, Nat.add(c, c2), 1n, Cc(br))), Unit{})), {==}, {==})

def Sub.id(+bb: Nat, +x: Nat, +y: Nat, +vx: Nat, +vy: Nat, +cbr: Nat, +cbw: Nat, +dg: Nat, +rr: Nat,
  hs: {Nat.add(dg, Nat.add(cbr, y)) == Nat.add(x, Nat.mul(cbw, bb)) : Nat}, hi: {Nat.add(rr, Nat.add(cbw, vy)) == vx : Nat})
  -> {Nat.add(Nat.add(dg, Nat.mul(rr, bb)), Nat.add(cbr, Nat.add(y, Nat.mul(vy, bb)))) == Nat.add(x, Nat.mul(vx, bb)) : Nat}:
  +env : List<&2, Nat> = [0n, bb, x, y, vx, vy, cbr, cbw, dg, rr]
  R.NatN.eq2(env, R.Ad(R.Ad(R.V(8n), R.Ml(R.V(9n), R.V(1n))), R.Ad(R.V(6n), R.Ad(R.V(3n), R.Ml(R.V(5n), R.V(1n))))), R.Ad(R.V(2n), R.Ml(R.V(4n), R.V(1n))),
    [R.V(1n)], [R.Ad(R.Ad(R.V(9n), R.Ad(R.V(7n), R.V(5n))), R.Ng(R.V(4n)))],
    [R.Ad(R.Ad(R.V(8n), R.Ad(R.V(6n), R.V(3n))), R.Ng(R.Ad(R.V(2n), R.Ml(R.V(7n), R.V(1n)))))],
    {==}, (R.NatN.z(env, R.Ad(R.V(9n), R.Ad(R.V(7n), R.V(5n))), R.V(4n), {==}, {==}, hi), Unit{}),
    (R.NatN.z(env, R.Ad(R.V(8n), R.Ad(R.V(6n), R.V(3n))), R.Ad(R.V(2n), R.Ml(R.V(7n), R.V(1n))), {==}, {==}, hs), Unit{}), {==}, {==})

# a limb of a difference: its identity and its bound
def Sub.limb(+bb: Nat, +x: Nat, +y: Nat, +ux: Nat, +hx: {bb == Nat.add(1n+x, ux) : Nat}, +uy: Nat, +hy: {bb == Nat.add(1n+y, uy) : Nat}, +br: Bool)
  -> {Nat.add(F.Nat.monusf(Nat.add(x, Nat.mul(B.Bn.c(F.Nat.ltf(x, Nat.add(B.Bn.c(br), y))), bb)), Nat.add(B.Bn.c(br), y)), Nat.add(B.Bn.c(br), y)) == Nat.add(x, Nat.mul(B.Bn.c(F.Nat.ltf(x, Nat.add(B.Bn.c(br), y))), bb)) : Nat}
   & {F.Nat.ltf(F.Nat.monusf(Nat.add(x, Nat.mul(B.Bn.c(F.Nat.ltf(x, Nat.add(B.Bn.c(br), y))), bb)), Nat.add(B.Bn.c(br), y)), bb) == True{} : Bool}:
  +t = Nat.add(B.Bn.c(br), y)
  +bw = F.Nat.ltf(x, t)
  +m = Nat.add(x, Nat.mul(B.Bn.c(bw), bb))
  +em = FL.L.monus(m, t)
  +hs = Sdig(x, t, bb, Nat.add(B.Bn.c(Bool.not(br)), uy), Sub.tb(bb, y, uy, hy, br), bw, FL.L.lt(x, t))
  +hs2 = Sdig(x, t, bb, Nat.add(B.Bn.c(Bool.not(br)), uy), Sub.tb(bb, y, uy, hy, br), bw, FL.L.lt(x, t))
  (Equal.trans(Nat, Nat.add(F.Nat.monusf(m, t), t), Nat.add(RD.Nat.monus(m, t), t), m, Equal.cong(Nat, Nat, z => Nat.add(z, t), F.Nat.monusf(m, t), RD.Nat.monus(m, t), Equal.sym(Nat, RD.Nat.monus(m, t), F.Nat.monusf(m, t), em)), hs),
   Equal.trans(Bool, F.Nat.ltf(F.Nat.monusf(m, t), bb), RD.Nat.lt(F.Nat.monusf(m, t), bb), True{}, Equal.sym(Bool, RD.Nat.lt(F.Nat.monusf(m, t), bb), F.Nat.ltf(F.Nat.monusf(m, t), bb), FL.L.lt(F.Nat.monusf(m, t), bb)),
     Equal.trans(Bool, RD.Nat.lt(F.Nat.monusf(m, t), bb), RD.Nat.lt(RD.Nat.monus(m, t), bb), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, bb), F.Nat.monusf(m, t), RD.Nat.monus(m, t), Equal.sym(Nat, RD.Nat.monus(m, t), F.Nat.monusf(m, t), FL.L.monus(m, t))),
       Sub.dig.ok(x, t, bb, ux, hx, bw, FL.L.lt(x, t), hs2))))

def Sub.val(+h: Nat, a: B.Bn, b: B.Bn, +br: Bool, +oa: {B.Bn.ok(h, a) == True{} : Bool}, +ob: {B.Bn.ok(h, b) == True{} : Bool},
  +hyp: {RD.Nat.lt(B.Bn.val(h, a), Nat.add(B.Bn.c(br), B.Bn.val(h, b))) == False{} : Bool})
  -> {Nat.add(B.Bn.val(h, B.Bn.subb(h, a, b, br)), Nat.add(B.Bn.c(br), B.Bn.val(h, b))) == B.Bn.val(h, a) : Nat}:
  match a b:
    case B.BNil{} B.BNil{}:
      match br:
        case True{}:
          Empty.absurd({Nat.add(0n, 1n) == 0n : Nat}, Z.Bool.ft(Equal.sym(Bool, True{}, False{}, hyp)))
        case False{}:
          {==}
    case B.BCons{+x, +xs} B.BNil{}:
      +bb = Nat.double(h)
      +ux = RD.Nat.monus(bb, 1n+x)
      +hx = Ok.hd(h, x, xs, oa)
      +t = Nat.add(B.Bn.c(br), 0n)
      +bw = F.Nat.ltf(x, t)
      +vx = B.Bn.val(h, xs)
      +step = Cmp.step(bb, x, 0n, vx, 0n, ux, hx, Nat.add(x, ux), hx, br, bw, FL.L.lt(x, t))
      +ih = Sub.val(h, xs, B.BNil{}, bw, Ok.tl(h, x, xs, oa), ob, Equal.trans(Bool, RD.Nat.lt(vx, Nat.add(B.Bn.c(bw), 0n)), RD.Nat.lt(Nat.add(x, Nat.mul(vx, bb)), Nat.add(B.Bn.c(br), 0n)), False{},
        Equal.sym(Bool, RD.Nat.lt(Nat.add(x, Nat.mul(vx, bb)), Nat.add(B.Bn.c(br), 0n)), RD.Nat.lt(vx, Nat.add(B.Bn.c(bw), 0n)), step), hyp))
      Sub.id(bb, x, 0n, vx, 0n, B.Bn.c(br), B.Bn.c(bw), F.Nat.monusf(Nat.add(x, Nat.mul(B.Bn.c(bw), bb)), t), B.Bn.val(h, B.Bn.subb(h, xs, B.BNil{}, bw)),
        Pair.fst({Nat.add(F.Nat.monusf(Nat.add(x, Nat.mul(B.Bn.c(bw), bb)), t), t) == Nat.add(x, Nat.mul(B.Bn.c(bw), bb)) : Nat}, {F.Nat.ltf(F.Nat.monusf(Nat.add(x, Nat.mul(B.Bn.c(bw), bb)), t), bb) == True{} : Bool},
          Sub.limb(bb, x, 0n, ux, hx, Nat.add(x, ux), hx, br)), ih)
    case B.BNil{} B.BCons{+y, +ys}:
      +bb = Nat.double(h)
      +uy = RD.Nat.monus(bb, 1n+y)
      +hy = Ok.hd(h, y, ys, ob)
      +t = Nat.add(B.Bn.c(br), y)
      +bw = F.Nat.ltf(0n, t)
      +vy = B.Bn.val(h, ys)
      +step = Cmp.step(bb, 0n, y, 0n, vy, Nat.add(y, uy), hy, uy, hy, br, bw, FL.L.lt(0n, t))
      +ih = Sub.val(h, B.BNil{}, ys, bw, oa, Ok.tl(h, y, ys, ob), Equal.trans(Bool, RD.Nat.lt(0n, Nat.add(B.Bn.c(bw), vy)), RD.Nat.lt(0n, Nat.add(B.Bn.c(br), Nat.add(y, Nat.mul(vy, bb)))), False{},
        Equal.sym(Bool, RD.Nat.lt(0n, Nat.add(B.Bn.c(br), Nat.add(y, Nat.mul(vy, bb)))), RD.Nat.lt(0n, Nat.add(B.Bn.c(bw), vy)), step), hyp))
      Sub.id(bb, 0n, y, 0n, vy, B.Bn.c(br), B.Bn.c(bw), F.Nat.monusf(Nat.add(0n, Nat.mul(B.Bn.c(bw), bb)), t), B.Bn.val(h, B.Bn.subb(h, B.BNil{}, ys, bw)),
        Pair.fst({Nat.add(F.Nat.monusf(Nat.add(0n, Nat.mul(B.Bn.c(bw), bb)), t), t) == Nat.add(0n, Nat.mul(B.Bn.c(bw), bb)) : Nat}, {F.Nat.ltf(F.Nat.monusf(Nat.add(0n, Nat.mul(B.Bn.c(bw), bb)), t), bb) == True{} : Bool},
          Sub.limb(bb, 0n, y, Nat.add(y, uy), hy, uy, hy, br)), ih)
    case B.BCons{+x, +xs} B.BCons{+y, +ys}:
      +bb = Nat.double(h)
      +ux = RD.Nat.monus(bb, 1n+x)
      +hx = Ok.hd(h, x, xs, oa)
      +uy = RD.Nat.monus(bb, 1n+y)
      +hy = Ok.hd(h, y, ys, ob)
      +t = Nat.add(B.Bn.c(br), y)
      +bw = F.Nat.ltf(x, t)
      +vx = B.Bn.val(h, xs)
      +vy = B.Bn.val(h, ys)
      +step = Cmp.step(bb, x, y, vx, vy, ux, hx, uy, hy, br, bw, FL.L.lt(x, t))
      +ih = Sub.val(h, xs, ys, bw, Ok.tl(h, x, xs, oa), Ok.tl(h, y, ys, ob), Equal.trans(Bool, RD.Nat.lt(vx, Nat.add(B.Bn.c(bw), vy)), RD.Nat.lt(Nat.add(x, Nat.mul(vx, bb)), Nat.add(B.Bn.c(br), Nat.add(y, Nat.mul(vy, bb)))), False{},
        Equal.sym(Bool, RD.Nat.lt(Nat.add(x, Nat.mul(vx, bb)), Nat.add(B.Bn.c(br), Nat.add(y, Nat.mul(vy, bb)))), RD.Nat.lt(vx, Nat.add(B.Bn.c(bw), vy)), step), hyp))
      Sub.id(bb, x, y, vx, vy, B.Bn.c(br), B.Bn.c(bw), F.Nat.monusf(Nat.add(x, Nat.mul(B.Bn.c(bw), bb)), t), B.Bn.val(h, B.Bn.subb(h, xs, ys, bw)),
        Pair.fst({Nat.add(F.Nat.monusf(Nat.add(x, Nat.mul(B.Bn.c(bw), bb)), t), t) == Nat.add(x, Nat.mul(B.Bn.c(bw), bb)) : Nat}, {F.Nat.ltf(F.Nat.monusf(Nat.add(x, Nat.mul(B.Bn.c(bw), bb)), t), bb) == True{} : Bool},
          Sub.limb(bb, x, y, ux, hx, uy, hy, br)), ih)

def Sub.ok(+h: Nat, a: B.Bn, b: B.Bn, +br: Bool, +oa: {B.Bn.ok(h, a) == True{} : Bool}, +ob: {B.Bn.ok(h, b) == True{} : Bool})
  -> {B.Bn.ok(h, B.Bn.subb(h, a, b, br)) == True{} : Bool}:
  match a b:
    case B.BNil{} B.BNil{}:
      {==}
    case B.BCons{+x, +xs} B.BNil{}:
      +bb = Nat.double(h)
      +ux = RD.Nat.monus(bb, 1n+x)
      +hx = Ok.hd(h, x, xs, oa)
      +t = Nat.add(B.Bn.c(br), 0n)
      +bw = F.Nat.ltf(x, t)
      +dg = F.Nat.monusf(Nat.add(x, Nat.mul(B.Bn.c(bw), bb)), t)
      And.tt(F.Nat.ltf(dg, bb), B.Bn.ok(h, B.Bn.subb(h, xs, B.BNil{}, bw)),
        Pair.snd({Nat.add(dg, t) == Nat.add(x, Nat.mul(B.Bn.c(bw), bb)) : Nat}, {F.Nat.ltf(dg, bb) == True{} : Bool}, Sub.limb(bb, x, 0n, ux, hx, Nat.add(x, ux), hx, br)),
        Sub.ok(h, xs, B.BNil{}, bw, Ok.tl(h, x, xs, oa), ob))
    case B.BNil{} B.BCons{+y, +ys}:
      +bb = Nat.double(h)
      +uy = RD.Nat.monus(bb, 1n+y)
      +hy = Ok.hd(h, y, ys, ob)
      +t = Nat.add(B.Bn.c(br), y)
      +bw = F.Nat.ltf(0n, t)
      +dg = F.Nat.monusf(Nat.add(0n, Nat.mul(B.Bn.c(bw), bb)), t)
      And.tt(F.Nat.ltf(dg, bb), B.Bn.ok(h, B.Bn.subb(h, B.BNil{}, ys, bw)),
        Pair.snd({Nat.add(dg, t) == Nat.add(0n, Nat.mul(B.Bn.c(bw), bb)) : Nat}, {F.Nat.ltf(dg, bb) == True{} : Bool}, Sub.limb(bb, 0n, y, Nat.add(y, uy), hy, uy, hy, br)),
        Sub.ok(h, B.BNil{}, ys, bw, oa, Ok.tl(h, y, ys, ob)))
    case B.BCons{+x, +xs} B.BCons{+y, +ys}:
      +bb = Nat.double(h)
      +t = Nat.add(B.Bn.c(br), y)
      +bw = F.Nat.ltf(x, t)
      +dg = F.Nat.monusf(Nat.add(x, Nat.mul(B.Bn.c(bw), bb)), t)
      And.tt(F.Nat.ltf(dg, bb), B.Bn.ok(h, B.Bn.subb(h, xs, ys, bw)),
        Pair.snd({Nat.add(dg, t) == Nat.add(x, Nat.mul(B.Bn.c(bw), bb)) : Nat}, {F.Nat.ltf(dg, bb) == True{} : Bool},
          Sub.limb(bb, x, y, RD.Nat.monus(bb, 1n+x), Ok.hd(h, x, xs, oa), RD.Nat.monus(bb, 1n+y), Ok.hd(h, y, ys, ob), br)),
        Sub.ok(h, xs, ys, bw, Ok.tl(h, x, xs, oa), Ok.tl(h, y, ys, ob)))

# Fuel
# ----

# the loop's result does not depend on its fuel, once n < 2^(p + fuel)
def Go.base(+f: Nat, +p: Nat, +n: Nat) -> {RD.Tr.go(f, p, n, True{}) == RD.Tr{0n, n, 0n, 0n, 0n} : RD.Tr}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

def Fuel.go(+f: Nat, +g: Nat, +p: Nat, +n: Nat, lt: Bool, +el: {RD.Nat.lt(n, RD.Nat.pow2(p)) == lt : Bool},
  +hf: {RD.Nat.lt(n, RD.Nat.pow2(Nat.add(p, f))) == True{} : Bool}, +hg: {RD.Nat.lt(n, RD.Nat.pow2(Nat.add(p, g))) == True{} : Bool})
  -> {RD.Tr.go(f, p, n, lt) == RD.Tr.go(g, p, n, lt) : RD.Tr}:
  match f g:
    case 0n g2:
      match lt:
        case True{}:
          Equal.sym(RD.Tr, RD.Tr.go(g2, p, n, True{}), RD.Tr{0n, n, 0n, 0n, 0n}, Go.base(g2, p, n))
        case False{}:
          +e = Equal.trans(Bool, RD.Nat.lt(n, RD.Nat.pow2(p)), RD.Nat.lt(n, RD.Nat.pow2(Nat.add(p, 0n))), True{},
            Equal.cong(Nat, Bool, z => RD.Nat.lt(n, RD.Nat.pow2(z)), p, Nat.add(p, 0n), Equal.sym(Nat, Nat.add(p, 0n), p, NL.Nat.add_zero_r(p))), hf)
          Empty.absurd({RD.Tr.go(0n, p, n, False{}) == RD.Tr.go(g2, p, n, False{}) : RD.Tr}, Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(n, RD.Nat.pow2(p)), True{}, Equal.sym(Bool, RD.Nat.lt(n, RD.Nat.pow2(p)), False{}, el), e)))
    case 1n+f2 0n:
      match lt:
        case True{}:
          {==}
        case False{}:
          +e = Equal.trans(Bool, RD.Nat.lt(n, RD.Nat.pow2(p)), RD.Nat.lt(n, RD.Nat.pow2(Nat.add(p, 0n))), True{},
            Equal.cong(Nat, Bool, z => RD.Nat.lt(n, RD.Nat.pow2(z)), p, Nat.add(p, 0n), Equal.sym(Nat, Nat.add(p, 0n), p, NL.Nat.add_zero_r(p))), hg)
          Empty.absurd({RD.Tr.go(1n+f2, p, n, False{}) == RD.Tr.go(0n, p, n, False{}) : RD.Tr}, Z.Bool.ft(Equal.trans(Bool, False{}, RD.Nat.lt(n, RD.Nat.pow2(p)), True{}, Equal.sym(Bool, RD.Nat.lt(n, RD.Nat.pow2(p)), False{}, el), e)))
    case 1n+f2 1n+g2:
      match lt:
        case True{}:
          {==}
        case False{}:
          +pw = RD.Nat.pow2(p)
          +hn = D.Nat.half(n)
          +lt2 = RD.Nat.lt(hn, pw)
          # n < 2^(p + 1 + f) = 2 2^(p + f) gives half(n) < 2^(p + f)
          +qf = RD.Nat.pow2(Nat.add(p, f2))
          +qg = RD.Nat.pow2(Nat.add(p, g2))
          +ef = Equal.trans(Bool, RD.Nat.lt(n, Nat.double(qf)), RD.Nat.lt(n, RD.Nat.pow2(Nat.add(p, 1n+f2))), True{},
            Equal.cong(Nat, Bool, z => RD.Nat.lt(n, RD.Nat.pow2(z)), 1n+Nat.add(p, f2), Nat.add(p, 1n+f2), Equal.sym(Nat, Nat.add(p, 1n+f2), 1n+Nat.add(p, f2), NL.Nat.add_succ_r(p, f2))), hf)
          +eg = Equal.trans(Bool, RD.Nat.lt(n, Nat.double(qg)), RD.Nat.lt(n, RD.Nat.pow2(Nat.add(p, 1n+g2))), True{},
            Equal.cong(Nat, Bool, z => RD.Nat.lt(n, RD.Nat.pow2(z)), 1n+Nat.add(p, g2), Nat.add(p, 1n+g2), Equal.sym(Nat, Nat.add(p, 1n+g2), 1n+Nat.add(p, g2), NL.Nat.add_succ_r(p, g2))), hg)
          +ih = Fuel.go(f2, g2, p, hn, lt2, {==},
            Half.lt(qf, n, RD.Nat.monus(Nat.double(qf), 1n+n), Lt.wit(n, Nat.double(qf))(ef)),
            Half.lt(qg, n, RD.Nat.monus(Nat.double(qg), 1n+n), Lt.wit(n, Nat.double(qg))(eg)))
          Equal.cong(RD.Tr, RD.Tr, t => RD.Tr.up(t, RD.Nat.bit(n), RD.Nat.monus(n, pw)), RD.Tr.go(f2, p, hn, lt2), RD.Tr.go(g2, p, hn, lt2), ih)

def Lt.dbl(+n: Nat, +x: Nat, +h: {RD.Nat.lt(n, x) == True{} : Bool}) -> {RD.Nat.lt(n, Nat.double(x)) == True{} : Bool}:
  +w = RD.Nat.monus(x, 1n+n)
  +k = Nat.add(w, x)
  +env : List<&2, Nat> = [0n, 1n, n, w, x, Nat.double(x)]
  +e = R.NatN.eq2(env, R.V(5n), R.Ad(R.V(2n), R.Ad(R.V(1n), R.Ad(R.V(3n), R.V(4n)))), [], [],
    [R.Ad(R.V(5n), R.Ng(R.Ad(R.V(4n), R.V(4n)))), R.Ad(R.V(4n), R.Ng(R.Ad(R.Ad(R.V(1n), R.V(2n)), R.V(3n))))],
    {==}, Unit{}, (R.NatN.z(env, R.V(5n), R.Ad(R.V(4n), R.V(4n)), {==}, {==}, Y.Nat.double_add(x)), (R.NatN.z(env, R.V(4n), R.Ad(R.Ad(R.V(1n), R.V(2n)), R.V(3n)), {==}, {==}, Lt.wit(n, x)(h)), Unit{})), {==}, {==})
  Equal.trans(Bool, RD.Nat.lt(n, Nat.double(x)), RD.Nat.lt(n, Nat.add(n, 1n+k)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(n, z), Nat.double(x), Nat.add(n, 1n+k), e), Lt.self(n, k))

def Lt.pw(+n: Nat, +p: Nat, +f: Nat, +h: {RD.Nat.lt(n, RD.Nat.pow2(f)) == True{} : Bool}) -> {RD.Nat.lt(n, RD.Nat.pow2(Nat.add(p, f))) == True{} : Bool}:
  match p:
    case 0n:
      h
    case 1n+q:
      Lt.dbl(n, RD.Nat.pow2(Nat.add(q, f)), Lt.pw(n, q, f, h))

# n < 2^n
def Lt.npow(+n: Nat) -> {RD.Nat.lt(n, RD.Nat.pow2(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +x = RD.Nat.pow2(m)
      +w = RD.Nat.monus(x, 1n+m)
      +k = Nat.add(m, Nat.add(w, w))
      +env : List<&2, Nat> = [0n, 1n, m, w, x, Nat.double(x)]
      +rx = R.Ad(R.V(4n), R.Ng(R.Ad(R.Ad(R.V(1n), R.V(2n)), R.V(3n))))
      +e = R.NatN.eq2(env, R.V(5n), R.Ad(R.Ad(R.V(1n), R.V(2n)), R.Ad(R.V(1n), R.Ad(R.V(2n), R.Ad(R.V(3n), R.V(3n))))), [], [],
        [R.Ad(R.V(5n), R.Ng(R.Ad(R.V(4n), R.V(4n)))), rx, rx],
        {==}, Unit{}, (R.NatN.z(env, R.V(5n), R.Ad(R.V(4n), R.V(4n)), {==}, {==}, Y.Nat.double_add(x)),
          (R.NatN.z(env, R.V(4n), R.Ad(R.Ad(R.V(1n), R.V(2n)), R.V(3n)), {==}, {==}, Lt.wit(m, x)(Lt.npow(m))),
          (R.NatN.z(env, R.V(4n), R.Ad(R.Ad(R.V(1n), R.V(2n)), R.V(3n)), {==}, {==}, Lt.wit(m, x)(Lt.npow(m))), Unit{}))), {==}, {==})
      Equal.trans(Bool, RD.Nat.lt(1n+m, Nat.double(x)), RD.Nat.lt(1n+m, Nat.add(1n+m, 1n+k)), True{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(1n+m, z), Nat.double(x), Nat.add(1n+m, 1n+k), e), Lt.self(1n+m, k))

def Mul.dbl_l(+x: Nat, +y: Nat) -> {Nat.mul(Nat.double(x), y) == Nat.double(Nat.mul(x, y)) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.double(x), y), Nat.mul(Nat.add(x, x), y), Nat.double(Nat.mul(x, y)),
    Equal.cong(Nat, Nat, z => Nat.mul(z, y), Nat.double(x), Nat.add(x, x), Y.Nat.double_add(x)),
    Equal.trans(Nat, Nat.mul(Nat.add(x, x), y), Nat.add(Nat.mul(x, y), Nat.mul(x, y)), Nat.double(Nat.mul(x, y)),
      NL.Nat.mul_dist_r(x, x, y), Equal.sym(Nat, Nat.double(Nat.mul(x, y)), Nat.add(Nat.mul(x, y), Nat.mul(x, y)), Y.Nat.double_add(Nat.mul(x, y)))))

def Pow2.add(+a: Nat, +b: Nat) -> {RD.Nat.pow2(Nat.add(a, b)) == Nat.mul(RD.Nat.pow2(a), RD.Nat.pow2(b)) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(RD.Nat.pow2(b), 0n), RD.Nat.pow2(b), NL.Nat.add_zero_r(RD.Nat.pow2(b)))
    case 1n+c:
      Equal.trans(Nat, Nat.double(RD.Nat.pow2(Nat.add(c, b))), Nat.double(Nat.mul(RD.Nat.pow2(c), RD.Nat.pow2(b))), Nat.mul(Nat.double(RD.Nat.pow2(c)), RD.Nat.pow2(b)),
        Equal.cong(Nat, Nat, z => Nat.double(z), RD.Nat.pow2(Nat.add(c, b)), Nat.mul(RD.Nat.pow2(c), RD.Nat.pow2(b)), Pow2.add(c, b)),
        Equal.sym(Nat, Nat.mul(Nat.double(RD.Nat.pow2(c)), RD.Nat.pow2(b)), Nat.double(Nat.mul(RD.Nat.pow2(c), RD.Nat.pow2(b))), Mul.dbl_l(RD.Nat.pow2(c), RD.Nat.pow2(b))))

# 2h <= 2^h for h >= 1, with the gap
def Wf(k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+(+j):
      Nat.add(Nat.double(j), Nat.double(Wf(j)))

def Le2h(+k: Nat) -> {RD.Nat.pow2(1n+k) == Nat.add(Nat.double(1n+k), Wf(k)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      +a = Nat.double(1n+j)
      +w = Wf(j)
      +dj = Nat.double(j)
      +e1 = Equal.cong(Nat, Nat, z => Nat.double(z), RD.Nat.pow2(1n+j), Nat.add(a, w), Le2h(j))
      +e2 = R.Nat.double_hom(a, w)
      +e3 = Equal.cong(Nat, Nat, z => 4n+z, Nat.add(Nat.double(dj), Nat.double(w)), Nat.add(dj, Nat.add(dj, Nat.double(w))),
        Equal.trans(Nat, Nat.add(Nat.double(dj), Nat.double(w)), Nat.add(Nat.add(dj, dj), Nat.double(w)), Nat.add(dj, Nat.add(dj, Nat.double(w))),
          Equal.cong(Nat, Nat, z => Nat.add(z, Nat.double(w)), Nat.double(dj), Nat.add(dj, dj), Y.Nat.double_add(dj)), NL.Nat.add_assoc(dj, dj, Nat.double(w))))
      Equal.trans(Nat, Nat.double(RD.Nat.pow2(1n+j)), Nat.double(Nat.add(a, w)), Nat.add(Nat.double(2n+j), Nat.add(dj, Nat.double(w))), e1,
        Equal.trans(Nat, Nat.double(Nat.add(a, w)), Nat.add(Nat.double(a), Nat.double(w)), Nat.add(Nat.double(2n+j), Nat.add(dj, Nat.double(w))), e2, e3))

# a number of L limbs below 2h is below 2^(h L)
def Val.lt(+h1: Nat, b: B.Bn, +ob: {B.Bn.ok(1n+h1, b) == True{} : Bool}) -> {RD.Nat.lt(B.Bn.val(1n+h1, b), RD.Nat.pow2(Nat.mul(1n+h1, B.Bn.len(b)))) == True{} : Bool}:
  match b:
    case B.BNil{}:
      Equal.cong(Nat, Bool, z => RD.Nat.lt(0n, RD.Nat.pow2(z)), Nat.mul(1n+h1, 0n), 0n, NL.Nat.mul_zero_r(1n+h1))
    case B.BCons{+d, +r}:
      +h : Nat = 1n+h1
      +dh = Nat.double(h)
      +l = B.Bn.len(r)
      +v = B.Bn.val(h, r)
      +pp = RD.Nat.pow2(Nat.mul(h, l))
      +tt = RD.Nat.pow2(h)
      +ud = RD.Nat.monus(dh, 1n+d)
      +wv = RD.Nat.monus(pp, 1n+v)
      +w2 = Wf(h1)
      +k = Nat.add(Nat.add(ud, Nat.mul(dh, wv)), Nat.mul(w2, pp))
      +env : List<&2, Nat> = [0n, 1n, d, ud, v, wv, pp, tt, w2, dh]
      +rt = R.NatN.z(env, R.V(7n), R.Ad(R.V(9n), R.V(8n)), {==}, {==}, Le2h(h1))
      +rp = R.NatN.z(env, R.V(6n), R.Ad(R.Ad(R.V(1n), R.V(4n)), R.V(5n)), {==}, {==}, Lt.wit(v, pp)(Val.lt(h1, r, Ok.tl(h, d, r, ob))))
      +rd = R.NatN.z(env, R.V(9n), R.Ad(R.Ad(R.V(1n), R.V(2n)), R.V(3n)), {==}, {==}, Ok.hd(h, d, r, ob))
      +ro = R.NatN.z(env, R.Ml(R.V(1n), R.V(9n)), R.V(9n), {==}, {==}, NL.Nat.add_zero_r(dh))
      +e = R.NatN.eq2(env, R.Ml(R.V(7n), R.V(6n)), R.Ad(R.Ad(R.V(2n), R.Ml(R.V(4n), R.V(9n))), R.Ad(R.V(1n), R.Ad(R.Ad(R.V(3n), R.Ml(R.V(9n), R.V(5n))), R.Ml(R.V(8n), R.V(6n))))),
        [R.V(6n), R.V(9n)], [R.Ad(R.V(7n), R.Ng(R.Ad(R.V(9n), R.V(8n)))), R.Ad(R.V(6n), R.Ng(R.Ad(R.Ad(R.V(1n), R.V(4n)), R.V(5n))))],
        [R.Ad(R.V(9n), R.Ng(R.Ad(R.Ad(R.V(1n), R.V(2n)), R.V(3n)))), R.Ad(R.Ml(R.V(1n), R.V(9n)), R.Ng(R.V(9n)))],
        {==}, (rt, (rp, Unit{})), (rd, (ro, Unit{})), {==}, {==})
      +val = Nat.add(d, Nat.mul(v, dh))
      +ep = Equal.trans(Nat, RD.Nat.pow2(Nat.mul(h, 1n+l)), RD.Nat.pow2(Nat.add(h, Nat.mul(h, l))), Nat.mul(tt, pp),
        Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), Nat.mul(h, 1n+l), Nat.add(h, Nat.mul(h, l)), NL.Nat.mul_succ_r(h, l)), Pow2.add(h, Nat.mul(h, l)))
      Equal.trans(Bool, RD.Nat.lt(val, RD.Nat.pow2(Nat.mul(h, 1n+l))), RD.Nat.lt(val, Nat.add(val, 1n+k)), True{},
        Equal.cong(Nat, Bool, z => RD.Nat.lt(val, z), RD.Nat.pow2(Nat.mul(h, 1n+l)), Nat.add(val, 1n+k), Equal.trans(Nat, RD.Nat.pow2(Nat.mul(h, 1n+l)), Nat.mul(tt, pp), Nat.add(val, 1n+k), ep, e)),
        Lt.self(val, k))

# Rounding a magnitude
# --------------------

# a TrB tracks a Tr: the same shift, quotient and remainder
def Lk(h: Nat, tb: B.TrB, t: RD.Tr) -> Type:
  {B.TrB.s(tb) == RD.Tr.s(t) : Nat} & ({B.Bn.val(h, B.TrB.q(tb)) == RD.Tr.q(t) : Nat} & {B.Bn.val(h, B.TrB.r(tb)) == R.Tr.r(t) : Nat})

def OkT(h: Nat, tb: B.TrB) -> Type:
  {B.Bn.ok(h, B.TrB.q(tb)) == True{} : Bool} & {B.Bn.ok(h, B.TrB.r(tb)) == True{} : Bool}

def Lk.tr(+h: Nat, +tb: B.TrB, +t1: RD.Tr, +t2: RD.Tr, +e: {t1 == t2 : RD.Tr}, l: Lk(h, tb, t1)) -> Lk(h, tb, t2):
  match l:
    case (ls, lqr):
      match lqr:
        case (lq, lr):
          (Equal.trans(Nat, B.TrB.s(tb), RD.Tr.s(t1), RD.Tr.s(t2), ls, Equal.cong(RD.Tr, Nat, z => RD.Tr.s(z), t1, t2, e)),
           (Equal.trans(Nat, B.Bn.val(h, B.TrB.q(tb)), RD.Tr.q(t1), RD.Tr.q(t2), lq, Equal.cong(RD.Tr, Nat, z => RD.Tr.q(z), t1, t2, e)),
            Equal.trans(Nat, B.Bn.val(h, B.TrB.r(tb)), R.Tr.r(t1), R.Tr.r(t2), lr, Equal.cong(RD.Tr, Nat, z => R.Tr.r(z), t1, t2, e))))

def Cb(+e: Bool) -> {B.Bn.c(Bool.not(e)) == Bool.pick(Nat, e, 0n, 1n) : Nat}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def Up.lk(+h: Nat, tb: B.TrB, t: RD.Tr, +odd: Bool, +b: Nat, +eo: {B.Bn.c(odd) == b : Nat}, +w: Nat, l: Lk(h, tb, t))
  -> Lk(h, B.TrB.up(h, tb, odd), RD.Tr.up(t, b, w)):
  match tb t:
    case B.TrB{s, q, +r} RD.Tr{s2, q2, +r2, wr, wq}:
      match l:
        case (ls, lqr):
          match lqr:
            case (lq, lr):
              (Equal.cong(Nat, Nat, z => 1n+z, s, s2, ls),
               (lq,
                Equal.trans(Nat, B.Bn.val(h, B.Bn.addc(h, r, r, odd)), Nat.add(B.Bn.c(odd), Nat.add(B.Bn.val(h, r), B.Bn.val(h, r))), Nat.add(Nat.double(r2), b), Add.val(h, r, r, odd),
                Equal.trans(Nat, Nat.add(B.Bn.c(odd), Nat.add(B.Bn.val(h, r), B.Bn.val(h, r))), Nat.add(b, Nat.add(r2, r2)), Nat.add(Nat.double(r2), b),
                  Equal.trans(Nat, Nat.add(B.Bn.c(odd), Nat.add(B.Bn.val(h, r), B.Bn.val(h, r))), Nat.add(b, Nat.add(B.Bn.val(h, r), B.Bn.val(h, r))), Nat.add(b, Nat.add(r2, r2)),
                    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(B.Bn.val(h, r), B.Bn.val(h, r))), B.Bn.c(odd), b, eo),
                    Equal.cong(Nat, Nat, z => Nat.add(b, Nat.add(z, z)), B.Bn.val(h, r), r2, lr)),
                  Equal.trans(Nat, Nat.add(b, Nat.add(r2, r2)), Nat.add(Nat.add(r2, r2), b), Nat.add(Nat.double(r2), b), NL.Nat.add_comm(b, Nat.add(r2, r2)),
                    Equal.cong(Nat, Nat, z => Nat.add(z, b), Nat.add(r2, r2), Nat.double(r2), Equal.sym(Nat, Nat.double(r2), Nat.add(r2, r2), Y.Nat.double_add(r2))))))))

def Up.ok(+h1: Nat, tb: B.TrB, +odd: Bool, ok: OkT(1n+h1, tb)) -> OkT(1n+h1, B.TrB.up(1n+h1, tb, odd)):
  match tb:
    case B.TrB{s, q, +r}:
      match ok:
        case (oq, +orr):
          (oq, Add.ok(h1, r, r, odd, orr, orr))

def Go.ok(+h1: Nat, fuel: Nat, +pw: B.Bn, +n: B.Bn, lt: Bool, +on: {B.Bn.ok(1n+h1, n) == True{} : Bool}) -> OkT(1n+h1, B.TrB.go(1n+h1, fuel, pw, n, lt)):
  match fuel:
    case 0n:
      (on, {==})
    case 1n+(+f):
      match lt:
        case True{}:
          (on, {==})
        case False{}:
          +hn = B.Bn.half(1n+h1, n)
          Up.ok(h1, B.TrB.go(1n+h1, f, pw, hn, B.Bn.lt(hn, pw)), Bool.not(B.Bn.even(n)), Go.ok(h1, f, pw, hn, B.Bn.lt(hn, pw), Half.ok(1n+h1, n, on)))

def Odd.bit(+h: Nat, +n: B.Bn, +v: Nat, +hv: {B.Bn.val(h, n) == v : Nat}) -> {B.Bn.c(Bool.not(B.Bn.even(n))) == RD.Nat.bit(v) : Nat}:
  +e = Equal.trans(Bool, B.Bn.even(n), D.Nat.even(B.Bn.val(h, n)), D.Nat.even(v), Even.val(h, n), Equal.cong(Nat, Bool, z => D.Nat.even(z), B.Bn.val(h, n), v, hv))
  Equal.trans(Nat, B.Bn.c(Bool.not(B.Bn.even(n))), B.Bn.c(Bool.not(D.Nat.even(v))), RD.Nat.bit(v),
    Equal.cong(Bool, Nat, z => B.Bn.c(Bool.not(z)), B.Bn.even(n), D.Nat.even(v), e), Cb(D.Nat.even(v)))

def Go.hv2(+h: Nat, +n: B.Bn, +v: Nat, +hv: {B.Bn.val(h, n) == v : Nat}) -> {B.Bn.val(h, B.Bn.half(h, n)) == D.Nat.half(v) : Nat}:
  Equal.trans(Nat, B.Bn.val(h, B.Bn.half(h, n)), D.Nat.half(B.Bn.val(h, n)), D.Nat.half(v), Half.val(h, n), Equal.cong(Nat, Nat, z => D.Nat.half(z), B.Bn.val(h, n), v, hv))

def Go.el2(+h: Nat, +pw: B.Bn, +p: Nat, +n: B.Bn, +v: Nat, +hv: {B.Bn.val(h, n) == v : Nat},
  +hpw: {B.Bn.val(h, pw) == RD.Nat.pow2(p) : Nat}, +opw: {B.Bn.ok(h, pw) == True{} : Bool}, +on: {B.Bn.ok(h, n) == True{} : Bool})
  -> {RD.Nat.lt(D.Nat.half(v), RD.Nat.pow2(p)) == B.Bn.lt(B.Bn.half(h, n), pw) : Bool}:
  +pp = RD.Nat.pow2(p)
  +hn = B.Bn.half(h, n)
  +lt2 = B.Bn.lt(hn, pw)
  Equal.sym(Bool, lt2, RD.Nat.lt(D.Nat.half(v), pp),
    Equal.trans(Bool, lt2, RD.Nat.lt(B.Bn.val(h, hn), B.Bn.val(h, pw)), RD.Nat.lt(D.Nat.half(v), pp), Cmp.lt(h, hn, pw, Half.ok(h, n, on), opw),
      Equal.trans(Bool, RD.Nat.lt(B.Bn.val(h, hn), B.Bn.val(h, pw)), RD.Nat.lt(D.Nat.half(v), B.Bn.val(h, pw)), RD.Nat.lt(D.Nat.half(v), pp),
        Equal.cong(Nat, Bool, z => RD.Nat.lt(z, B.Bn.val(h, pw)), B.Bn.val(h, hn), D.Nat.half(v), Go.hv2(h, n, v, hv)),
        Equal.cong(Nat, Bool, z => RD.Nat.lt(D.Nat.half(v), z), B.Bn.val(h, pw), pp, hpw))))

def Go.lk(+h1: Nat, fuel: Nat, +pw: B.Bn, +p: Nat, +n: B.Bn, +v: Nat, +hv: {B.Bn.val(1n+h1, n) == v : Nat},
  +hpw: {B.Bn.val(1n+h1, pw) == RD.Nat.pow2(p) : Nat}, +opw: {B.Bn.ok(1n+h1, pw) == True{} : Bool}, +on: {B.Bn.ok(1n+h1, n) == True{} : Bool},
  lt: Bool, +el: {RD.Nat.lt(v, RD.Nat.pow2(p)) == lt : Bool})
  -> Lk(1n+h1, B.TrB.go(1n+h1, fuel, pw, n, lt), RD.Tr.go(fuel, p, v, lt)):
  match fuel:
    case 0n:
      ({==}, (hv, {==}))
    case 1n+(+f):
      match lt:
        case True{}:
          ({==}, (hv, {==}))
        case False{}:
          +h : Nat = 1n+h1
          +pp = RD.Nat.pow2(p)
          +hn = B.Bn.half(h, n)
          +lt2 = B.Bn.lt(hn, pw)
          ih = Go.lk(h1, f, pw, p, hn, D.Nat.half(v), Go.hv2(h, n, v, hv), hpw, opw, Half.ok(h, n, on), lt2, Go.el2(h, pw, p, n, v, hv, hpw, opw, on))
          ih2 = Lk.tr(h, B.TrB.go(h, f, pw, hn, lt2), RD.Tr.go(f, p, D.Nat.half(v), lt2), RD.Tr.go(f, p, D.Nat.half(v), RD.Nat.lt(D.Nat.half(v), pp)),
            Equal.cong(Bool, RD.Tr, z => RD.Tr.go(f, p, D.Nat.half(v), z), lt2, RD.Nat.lt(D.Nat.half(v), pp), Equal.sym(Bool, RD.Nat.lt(D.Nat.half(v), pp), lt2, Go.el2(h, pw, p, n, v, hv, hpw, opw, on))), ih)
          Up.lk(h, B.TrB.go(h, f, pw, hn, lt2), RD.Tr.go(f, p, D.Nat.half(v), RD.Nat.lt(D.Nat.half(v), pp)), Bool.not(B.Bn.even(n)), RD.Nat.bit(v), Odd.bit(h, n, v, hv), RD.Nat.monus(v, pp), ih2)

# the run-time loop with fuel h L is the spec's loop with fuel n
def Of.el(+h1: Nat, +p: Nat, +n: B.Bn, +on: {B.Bn.ok(1n+h1, n) == True{} : Bool}) -> {RD.Nat.lt(B.Bn.val(1n+h1, n), RD.Nat.pow2(p)) == B.Bn.lt(n, B.Bn.pow2(1n+h1, p)) : Bool}:
  +h : Nat = 1n+h1
  +pw = B.Bn.pow2(h, p)
  +pp = RD.Nat.pow2(p)
  +v = B.Bn.val(h, n)
  +lt = B.Bn.lt(n, pw)
  Equal.sym(Bool, lt, RD.Nat.lt(v, pp),
    Equal.trans(Bool, lt, RD.Nat.lt(v, B.Bn.val(h, pw)), RD.Nat.lt(v, pp), Cmp.lt(h, n, pw, on, Pow2.ok(h1, p)),
      Equal.cong(Nat, Bool, z => RD.Nat.lt(v, z), B.Bn.val(h, pw), pp, Pow2.val(h1, p))))

def Of.lk(+h1: Nat, +p: Nat, +n: B.Bn, +on: {B.Bn.ok(1n+h1, n) == True{} : Bool}) -> Lk(1n+h1, B.TrB.of(1n+h1, p, n), RD.Tr.of(p, B.Bn.val(1n+h1, n))):
  +h : Nat = 1n+h1
  +pw = B.Bn.pow2(h, p)
  +pp = RD.Nat.pow2(p)
  +v = B.Bn.val(h, n)
  +fu = Nat.mul(h, B.Bn.len(n))
  +lt = B.Bn.lt(n, pw)
  ef = Equal.trans(RD.Tr, RD.Tr.go(fu, p, v, lt), RD.Tr.go(fu, p, v, RD.Nat.lt(v, pp)), RD.Tr.go(v, p, v, RD.Nat.lt(v, pp)),
    Equal.cong(Bool, RD.Tr, z => RD.Tr.go(fu, p, v, z), lt, RD.Nat.lt(v, pp), Equal.sym(Bool, RD.Nat.lt(v, pp), lt, Of.el(h1, p, n, on))),
    Fuel.go(fu, v, p, v, RD.Nat.lt(v, pp), {==}, Lt.pw(v, p, fu, Val.lt(h1, n, on)), Lt.pw(v, p, v, Lt.npow(v))))
  Lk.tr(h, B.TrB.of(h, p, n), RD.Tr.go(fu, p, v, lt), RD.Tr.of(p, v), ef,
    Go.lk(h1, fu, pw, p, n, v, {==}, Pow2.val(h1, p), Pow2.ok(h1, p), on, lt, Of.el(h1, p, n, on)))

def Vdbl(+h1: Nat, +r: B.Bn, +r2: Nat, +lr: {B.Bn.val(1n+h1, r) == r2 : Nat}) -> {B.Bn.val(1n+h1, B.Bn.add(1n+h1, r, r)) == Nat.double(r2) : Nat}:
  Equal.trans(Nat, B.Bn.val(1n+h1, B.Bn.add(1n+h1, r, r)), Nat.add(B.Bn.val(1n+h1, r), B.Bn.val(1n+h1, r)), Nat.double(r2), Add.val(1n+h1, r, r, False{}),
    Equal.trans(Nat, Nat.add(B.Bn.val(1n+h1, r), B.Bn.val(1n+h1, r)), Nat.add(r2, r2), Nat.double(r2), Equal.cong(Nat, Nat, z => Nat.add(z, z), B.Bn.val(1n+h1, r), r2, lr),
      Equal.sym(Nat, Nat.double(r2), Nat.add(r2, r2), Y.Nat.double_add(r2))))

def Vpw(+h1: Nat, +s: Nat, +s2: Nat, +ls: {s == s2 : Nat}) -> {B.Bn.val(1n+h1, B.Bn.pow2(1n+h1, s)) == RD.Nat.pow2(s2) : Nat}:
  Equal.trans(Nat, B.Bn.val(1n+h1, B.Bn.pow2(1n+h1, s)), RD.Nat.pow2(s), RD.Nat.pow2(s2), Pow2.val(h1, s), Equal.cong(Nat, Nat, z => RD.Nat.pow2(z), s, s2, ls))

def Rup.cong(+a1: Bool, +a2: Bool, +b1: Bool, +b2: Bool, +c1: Bool, +c2: Bool, ea: {a1 == a2 : Bool}, eb: {b1 == b2 : Bool}, ec: {c1 == c2 : Bool})
  -> {Bool.and(Bool.not(a1), Bool.or(b1, Bool.not(c1))) == Bool.and(Bool.not(a2), Bool.or(b2, Bool.not(c2))) : Bool}:
  Equal.trans(Bool, Bool.and(Bool.not(a1), Bool.or(b1, Bool.not(c1))), Bool.and(Bool.not(a2), Bool.or(b1, Bool.not(c1))), Bool.and(Bool.not(a2), Bool.or(b2, Bool.not(c2))),
    Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), Bool.or(b1, Bool.not(c1))), a1, a2, ea),
    Equal.trans(Bool, Bool.and(Bool.not(a2), Bool.or(b1, Bool.not(c1))), Bool.and(Bool.not(a2), Bool.or(b2, Bool.not(c1))), Bool.and(Bool.not(a2), Bool.or(b2, Bool.not(c2))),
      Equal.cong(Bool, Bool, z => Bool.and(Bool.not(a2), Bool.or(z, Bool.not(c1))), b1, b2, eb),
      Equal.cong(Bool, Bool, z => Bool.and(Bool.not(a2), Bool.or(b2, Bool.not(z))), c1, c2, ec)))

def Rup.lk(+h1: Nat, tb: B.TrB, t: RD.Tr, l: Lk(1n+h1, tb, t), okt: OkT(1n+h1, tb)) -> {B.TrB.rup(1n+h1, tb) == RD.Tr.rup(t) : Bool}:
  match tb t:
    case B.TrB{+s, +q, +r} RD.Tr{+s2, +q2, +r2, wr, wq}:
      match l:
        case (ls0, lqr):
          match lqr:
            case (lq, lr0):
              match okt:
                case (oq, orr0):
                  +ls : {s == s2 : Nat} = ls0
                  +lr : {B.Bn.val(1n+h1, r) == r2 : Nat} = lr0
                  +orr : {B.Bn.ok(1n+h1, r) == True{} : Bool} = orr0
                  +h : Nat = 1n+h1
                  +r2b = B.Bn.add(h, r, r)
                  +sv = B.Bn.pow2(h, s)
                  +or2 = Add.ok(h1, r, r, False{}, orr, orr)
                  Rup.cong(B.Bn.lt(r2b, sv), RD.Nat.lt(Nat.double(r2), RD.Nat.pow2(s2)), B.Bn.lt(sv, r2b), RD.Nat.lt(RD.Nat.pow2(s2), Nat.double(r2)), B.Bn.even(q), D.Nat.even(q2),
                    Equal.trans(Bool, B.Bn.lt(r2b, sv), RD.Nat.lt(B.Bn.val(h, r2b), B.Bn.val(h, sv)), RD.Nat.lt(Nat.double(r2), RD.Nat.pow2(s2)), Cmp.lt(h, r2b, sv, or2, Pow2.ok(h1, s)),
                      Equal.trans(Bool, RD.Nat.lt(B.Bn.val(h, r2b), B.Bn.val(h, sv)), RD.Nat.lt(Nat.double(r2), B.Bn.val(h, sv)), RD.Nat.lt(Nat.double(r2), RD.Nat.pow2(s2)),
                        Equal.cong(Nat, Bool, z => RD.Nat.lt(z, B.Bn.val(h, sv)), B.Bn.val(h, r2b), Nat.double(r2), Vdbl(h1, r, r2, lr)),
                        Equal.cong(Nat, Bool, z => RD.Nat.lt(Nat.double(r2), z), B.Bn.val(h, sv), RD.Nat.pow2(s2), Vpw(h1, s, s2, ls)))),
                    Equal.trans(Bool, B.Bn.lt(sv, r2b), RD.Nat.lt(B.Bn.val(h, sv), B.Bn.val(h, r2b)), RD.Nat.lt(RD.Nat.pow2(s2), Nat.double(r2)), Cmp.lt(h, sv, r2b, Pow2.ok(h1, s), Add.ok(h1, r, r, False{}, orr, orr)),
                      Equal.trans(Bool, RD.Nat.lt(B.Bn.val(h, sv), B.Bn.val(h, r2b)), RD.Nat.lt(RD.Nat.pow2(s2), B.Bn.val(h, r2b)), RD.Nat.lt(RD.Nat.pow2(s2), Nat.double(r2)),
                        Equal.cong(Nat, Bool, z => RD.Nat.lt(z, B.Bn.val(h, r2b)), B.Bn.val(h, sv), RD.Nat.pow2(s2), Vpw(h1, s, s2, ls)),
                        Equal.cong(Nat, Bool, z => RD.Nat.lt(RD.Nat.pow2(s2), z), B.Bn.val(h, r2b), Nat.double(r2), Vdbl(h1, r, r2, lr)))),
                    Equal.trans(Bool, B.Bn.even(q), D.Nat.even(B.Bn.val(h, q)), D.Nat.even(q2), Even.val(h, q), Equal.cong(Nat, Bool, z => D.Nat.even(z), B.Bn.val(h, q), q2, lq)))

def Np(+h1: Nat, u: Bool, +s: Nat, +q: B.Bn, +s2: Nat, +q2: Nat, +ls: {s == s2 : Nat}, +lq: {B.Bn.val(1n+h1, q) == q2 : Nat})
  -> {B.Bn.val(1n+h1, B.Bn.nearp(1n+h1, u, s, q)) == Bool.pick(Nat, u, Nat.mul(1n+q2, RD.Nat.pow2(s2)), Nat.mul(q2, RD.Nat.pow2(s2))) : Nat}:
  match u:
    case True{}:
      +h : Nat = 1n+h1
      +q1 = B.Bn.addc(h, q, B.BNil{}, True{})
      +e1 = Equal.trans(Nat, B.Bn.val(h, q1), 1n+Nat.add(B.Bn.val(h, q), 0n), 1n+q2, Add.val(h, q, B.BNil{}, True{}),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(B.Bn.val(h, q), 0n), q2, Equal.trans(Nat, Nat.add(B.Bn.val(h, q), 0n), B.Bn.val(h, q), q2, NL.Nat.add_zero_r(B.Bn.val(h, q)), lq)))
      Equal.trans(Nat, B.Bn.val(h, B.Bn.shl(h, s, q1)), Nat.mul(B.Bn.val(h, q1), RD.Nat.pow2(s)), Nat.mul(1n+q2, RD.Nat.pow2(s2)), Shl.val(h1, s, q1),
        Equal.trans(Nat, Nat.mul(B.Bn.val(h, q1), RD.Nat.pow2(s)), Nat.mul(1n+q2, RD.Nat.pow2(s)), Nat.mul(1n+q2, RD.Nat.pow2(s2)),
          Equal.cong(Nat, Nat, z => Nat.mul(z, RD.Nat.pow2(s)), B.Bn.val(h, q1), 1n+q2, e1),
          Equal.cong(Nat, Nat, z => Nat.mul(1n+q2, RD.Nat.pow2(z)), s, s2, ls)))
    case False{}:
      +h : Nat = 1n+h1
      Equal.trans(Nat, B.Bn.val(h, B.Bn.shl(h, s, q)), Nat.mul(B.Bn.val(h, q), RD.Nat.pow2(s)), Nat.mul(q2, RD.Nat.pow2(s2)), Shl.val(h1, s, q),
        Equal.trans(Nat, Nat.mul(B.Bn.val(h, q), RD.Nat.pow2(s)), Nat.mul(q2, RD.Nat.pow2(s)), Nat.mul(q2, RD.Nat.pow2(s2)),
          Equal.cong(Nat, Nat, z => Nat.mul(z, RD.Nat.pow2(s)), B.Bn.val(h, q), q2, lq),
          Equal.cong(Nat, Nat, z => Nat.mul(q2, RD.Nat.pow2(z)), s, s2, ls)))

# the rounded magnitude, given two copies of the link (each lemma consumes one)
def Near.lk(+h1: Nat, +tb: B.TrB, +t: RD.Tr, l1: Lk(1n+h1, tb, t), l2: Lk(1n+h1, tb, t), okt: OkT(1n+h1, tb))
  -> {B.Bn.val(1n+h1, B.TrB.near(1n+h1, tb)) == RD.Tr.near(t) : Nat}:
  match l2:
    case (ls, lqr):
      match lqr:
        case (lq, lr):
          +h : Nat = 1n+h1
          Equal.trans(Nat, B.Bn.val(h, B.Bn.nearp(h, B.TrB.rup(h, tb), B.TrB.s(tb), B.TrB.q(tb))), B.Bn.val(h, B.Bn.nearp(h, RD.Tr.rup(t), B.TrB.s(tb), B.TrB.q(tb))), RD.Tr.near(t),
            Equal.cong(Bool, Nat, z => B.Bn.val(h, B.Bn.nearp(h, z, B.TrB.s(tb), B.TrB.q(tb))), B.TrB.rup(h, tb), RD.Tr.rup(t), Rup.lk(h1, tb, t, l1, okt)),
            Np(h1, RD.Tr.rup(t), B.TrB.s(tb), B.TrB.q(tb), RD.Tr.s(t), RD.Tr.q(t), ls, lq))

def Fx.lk(+h1: Nat, s: Nat, +n: B.Bn, +v: Nat, +hv: {B.Bn.val(1n+h1, n) == v : Nat}) -> Lk(1n+h1, B.FxB.go(1n+h1, s, n), RD.Fx.go(s, v)):
  match s:
    case 0n:
      ({==}, (hv, {==}))
    case 1n+(+j):
      +h : Nat = 1n+h1
      Up.lk(h, B.FxB.go(h, j, B.Bn.half(h, n)), RD.Fx.go(j, D.Nat.half(v)), Bool.not(B.Bn.even(n)), RD.Nat.bit(v), Odd.bit(h, n, v, hv), 0n,
        Fx.lk(h1, j, B.Bn.half(h, n), D.Nat.half(v), Go.hv2(h, n, v, hv)))

def Fx.ok(+h1: Nat, s: Nat, +n: B.Bn, +on: {B.Bn.ok(1n+h1, n) == True{} : Bool}) -> OkT(1n+h1, B.FxB.go(1n+h1, s, n)):
  match s:
    case 0n:
      (on, {==})
    case 1n+(+j):
      Up.ok(h1, B.FxB.go(1n+h1, j, B.Bn.half(1n+h1, n)), Bool.not(B.Bn.even(n)), Fx.ok(h1, j, B.Bn.half(1n+h1, n), Half.ok(1n+h1, n, on)))

# Big dyadics
# -----------

# an identity of integers modulo relations r_i = 0 with multipliers l_i
def IntN(+env: List<&2, I.Int>, +t: N.Tm, +u: N.Tm, +ls: List<&2, N.Tm>, +rs: List<&2, N.Tm>,
  ok: {N.NormS.left(N.Tm.diff(t, N.TAdd{u, EQ.Tm.lin(ls, rs)})) == Nil{} : List<&2, N.Mono>},
  hz: EQ.Zs(~I.Int, ~I.IPos{0n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, env, rs))
  -> {N.Tm.eval(~I.Int, ~I.IPos{0n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, env, t) == N.Tm.eval(~I.Int, ~I.IPos{0n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, env, u) : I.Int}:
  EQ.Rel.many(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg,
    env, t, u, ls, rs, ok, hz)

# the sum of two dyadics over one exponent, unnormalised
def AddE(+e: Nat, +a: I.Int, +b: I.Int) -> {D.Dy.add(D.Dy.of(e, a), D.Dy.of(e, b)) == D.Dy.of(e, I.Int.add(a, b)) : D.Dy}:
  +x = D.Dy.of(e, a)
  +y = D.Dy.of(e, b)
  +nx = D.Dy.num(x)
  +ny = D.Dy.num(y)
  +dx = D.Dy.den(x)
  +dy = D.Dy.den(y)
  +s = I.Int.add(D.Int.sh(dy, nx), D.Int.sh(dx, ny))
  +sp = I.Int.add(I.Int.mul(nx, Y.P(dy)), I.Int.mul(ny, Y.P(dx)))
  +env : List<&2, I.Int> = [nx, ny, a, b, Y.P(e), Y.P(dx), Y.P(dy)]
  +ei = IntN(env, R.Ml(R.Ad(R.Ml(R.V(0n), R.V(6n)), R.Ml(R.V(1n), R.V(5n))), R.V(4n)), R.Ml(R.Ad(R.V(2n), R.V(3n)), R.Ml(R.V(5n), R.V(6n))),
    [R.V(6n), R.V(5n)], [R.Ad(R.Ml(R.V(0n), R.V(4n)), R.Ng(R.Ml(R.V(2n), R.V(5n)))), R.Ad(R.Ml(R.V(1n), R.V(4n)), R.Ng(R.Ml(R.V(3n), R.V(6n))))],
    {==}, (Y.Rel.z(I.Int.mul(nx, Y.P(e)), I.Int.mul(a, Y.P(dx)), Y.Of.valP(e, a)), (Y.Rel.z(I.Int.mul(ny, Y.P(e)), I.Int.mul(b, Y.P(dy)), Y.Of.valP(e, b)), Unit{})))
  Y.Of.eqvP(Nat.add(dx, dy), e, s, I.Int.add(a, b),
    Equal.trans(I.Int, I.Int.mul(s, Y.P(e)), I.Int.mul(sp, Y.P(e)), I.Int.mul(I.Int.add(a, b), Y.P(Nat.add(dx, dy))),
      Equal.cong(I.Int, I.Int, z => I.Int.mul(z, Y.P(e)), s, sp, Y.Cv.sum(nx, dy, ny, dx)),
      Equal.trans(I.Int, I.Int.mul(sp, Y.P(e)), I.Int.mul(I.Int.add(a, b), I.Int.mul(Y.P(dx), Y.P(dy))), I.Int.mul(I.Int.add(a, b), Y.P(Nat.add(dx, dy))), ei,
        Equal.cong(I.Int, I.Int, z => I.Int.mul(I.Int.add(a, b), z), I.Int.mul(Y.P(dx), Y.P(dy)), Y.P(Nat.add(dx, dy)), Equal.sym(I.Int, Y.P(Nat.add(dx, dy)), I.Int.mul(Y.P(dx), Y.P(dy)), Y.P.add(dx, dy))))))

def Sg.mul(+n1: Bool, +n2: Bool, +u: Nat, +v: Nat) -> {I.Int.mul(B.Bd.sg(n1, u), B.Bd.sg(n2, v)) == B.Bd.sg(Bool.xor(n1, n2), Nat.mul(u, v)) : I.Int}:
  match n1 n2:
    case False{} False{}:
      R.Ip.mul(u, v)
    case True{} False{}:
      +pu : I.Int = I.IPos{u}
      +pv : I.Int = I.IPos{v}
      Equal.trans(I.Int, I.Int.mul(I.Int.neg(pu), pv), I.Int.neg(I.Int.mul(pu, pv)), I.Int.neg(I.IPos{Nat.mul(u, v)}), Z.Int.neg_mul_l(pu, pv),
        Equal.cong(I.Int, I.Int, z => I.Int.neg(z), I.Int.mul(pu, pv), I.IPos{Nat.mul(u, v)}, R.Ip.mul(u, v)))
    case False{} True{}:
      +pu : I.Int = I.IPos{u}
      +pv : I.Int = I.IPos{v}
      Equal.trans(I.Int, I.Int.mul(pu, I.Int.neg(pv)), I.Int.mul(I.Int.neg(pv), pu), I.Int.neg(I.IPos{Nat.mul(u, v)}), Z.Int.r.mul_comm(pu, I.Int.neg(pv)),
        Equal.trans(I.Int, I.Int.mul(I.Int.neg(pv), pu), I.Int.neg(I.Int.mul(pv, pu)), I.Int.neg(I.IPos{Nat.mul(u, v)}), Z.Int.neg_mul_l(pv, pu),
          Equal.cong(I.Int, I.Int, z => I.Int.neg(z), I.Int.mul(pv, pu), I.IPos{Nat.mul(u, v)},
            Equal.trans(I.Int, I.Int.mul(pv, pu), I.Int.mul(pu, pv), I.IPos{Nat.mul(u, v)}, Z.Int.r.mul_comm(pv, pu), R.Ip.mul(u, v)))))
    case True{} True{}:
      +pu : I.Int = I.IPos{u}
      +pv : I.Int = I.IPos{v}
      Equal.trans(I.Int, I.Int.mul(I.Int.neg(pu), I.Int.neg(pv)), I.Int.neg(I.Int.mul(pu, I.Int.neg(pv))), I.IPos{Nat.mul(u, v)}, Z.Int.neg_mul_l(pu, I.Int.neg(pv)),
        Equal.trans(I.Int, I.Int.neg(I.Int.mul(pu, I.Int.neg(pv))), I.Int.neg(I.Int.neg(I.IPos{Nat.mul(u, v)})), I.IPos{Nat.mul(u, v)},
          Equal.cong(I.Int, I.Int, z => I.Int.neg(z), I.Int.mul(pu, I.Int.neg(pv)), I.Int.neg(I.IPos{Nat.mul(u, v)}),
            Equal.trans(I.Int, I.Int.mul(pu, I.Int.neg(pv)), I.Int.mul(I.Int.neg(pv), pu), I.Int.neg(I.IPos{Nat.mul(u, v)}), Z.Int.r.mul_comm(pu, I.Int.neg(pv)),
              Equal.trans(I.Int, I.Int.mul(I.Int.neg(pv), pu), I.Int.neg(I.Int.mul(pv, pu)), I.Int.neg(I.IPos{Nat.mul(u, v)}), Z.Int.neg_mul_l(pv, pu),
                Equal.cong(I.Int, I.Int, z => I.Int.neg(z), I.Int.mul(pv, pu), I.IPos{Nat.mul(u, v)},
                  Equal.trans(I.Int, I.Int.mul(pv, pu), I.Int.mul(pu, pv), I.IPos{Nat.mul(u, v)}, Z.Int.r.mul_comm(pv, pu), R.Ip.mul(u, v)))))),
          Z.Int.neg_neg(I.IPos{Nat.mul(u, v)})))

def Sg.sh(+n: Bool, +k: Nat, +v: Nat) -> {D.Int.sh(k, B.Bd.sg(n, v)) == B.Bd.sg(n, Nat.mul(v, RD.Nat.pow2(k))) : I.Int}:
  match n:
    case False{}:
      R.Sh.ipos(k, v)
    case True{}:
      Equal.trans(I.Int, D.Int.sh(k, I.Int.neg(I.IPos{v})), I.Int.neg(D.Int.sh(k, I.IPos{v})), I.Int.neg(I.IPos{Nat.mul(v, RD.Nat.pow2(k))}), Y.Int.sh_neg(k, I.IPos{v}),
        Equal.cong(I.Int, I.Int, z => I.Int.neg(z), D.Int.sh(k, I.IPos{v}), I.IPos{Nat.mul(v, RD.Nat.pow2(k))}, R.Sh.ipos(k, v)))

def Bd.mul.lk(+h1: Nat, x: B.Bd, y: B.Bd) -> {B.Bd.val(1n+h1, B.Bd.mul(1n+h1, x, y)) == D.Dy.mul(B.Bd.val(1n+h1, x), B.Bd.val(1n+h1, y)) : D.Dy}:
  match x y:
    case B.Bd{+n1, +m1, +e1} B.Bd{+n2, +m2, +e2}:
      +h : Nat = 1n+h1
      +v1 = B.Bn.val(h, m1)
      +v2 = B.Bn.val(h, m2)
      Equal.trans(D.Dy, D.Dy.of(Nat.add(e1, e2), B.Bd.sg(Bool.xor(n1, n2), B.Bn.val(h, B.Bn.mul(h, m1, m2)))), D.Dy.of(Nat.add(e1, e2), I.Int.mul(B.Bd.sg(n1, v1), B.Bd.sg(n2, v2))), D.Dy.mul(D.Dy.of(e1, B.Bd.sg(n1, v1)), D.Dy.of(e2, B.Bd.sg(n2, v2))),
        Equal.cong(I.Int, D.Dy, z => D.Dy.of(Nat.add(e1, e2), z), B.Bd.sg(Bool.xor(n1, n2), B.Bn.val(h, B.Bn.mul(h, m1, m2))), I.Int.mul(B.Bd.sg(n1, v1), B.Bd.sg(n2, v2)),
          Equal.trans(I.Int, B.Bd.sg(Bool.xor(n1, n2), B.Bn.val(h, B.Bn.mul(h, m1, m2))), B.Bd.sg(Bool.xor(n1, n2), Nat.mul(v1, v2)), I.Int.mul(B.Bd.sg(n1, v1), B.Bd.sg(n2, v2)),
            Equal.cong(Nat, I.Int, z => B.Bd.sg(Bool.xor(n1, n2), z), B.Bn.val(h, B.Bn.mul(h, m1, m2)), Nat.mul(v1, v2), Mul.val(h1, m1, m2)),
            Equal.sym(I.Int, I.Int.mul(B.Bd.sg(n1, v1), B.Bd.sg(n2, v2)), B.Bd.sg(Bool.xor(n1, n2), Nat.mul(v1, v2)), Sg.mul(n1, n2, v1, v2)))),
        Equal.sym(D.Dy, D.Dy.mul(D.Dy.of(e1, B.Bd.sg(n1, v1)), D.Dy.of(e2, B.Bd.sg(n2, v2))), D.Dy.of(Nat.add(e1, e2), I.Int.mul(B.Bd.sg(n1, v1), B.Bd.sg(n2, v2))), R.Mul.of(e1, e2, B.Bd.sg(n1, v1), B.Bd.sg(n2, v2))))

def Bd.mul.ok(+h1: Nat, x: B.Bd, y: B.Bd, ox: {B.Bd.ok(1n+h1, x) == True{} : Bool}, oy: {B.Bd.ok(1n+h1, y) == True{} : Bool}) -> {B.Bd.ok(1n+h1, B.Bd.mul(1n+h1, x, y)) == True{} : Bool}:
  match x y:
    case B.Bd{n1, +m1, e1} B.Bd{n2, m2, e2}:
      Mul.ok(h1, m1, m2, ox, oy)

def Ipm2(+d: Nat, +b: Nat) -> {I.Int.add(I.IPos{Nat.add(d, b)}, I.Int.neg(I.IPos{b})) == I.IPos{d} : I.Int}:
  +env : List<&2, I.Int> = [I.IPos{d}, I.IPos{b}]
  IntN(env, R.Ad(R.Ad(R.V(0n), R.V(1n)), R.Ng(R.V(1n))), R.V(0n), [], [], {==}, Unit{})

def Ipm(+d: Nat, +a: Nat) -> {I.Int.add(I.IPos{a}, I.Int.neg(I.IPos{Nat.add(d, a)})) == I.Int.neg(I.IPos{d}) : I.Int}:
  +env : List<&2, I.Int> = [I.IPos{d}, I.IPos{a}]
  IntN(env, R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(1n)))), R.Ng(R.V(0n)), [], [], {==}, Unit{})

def Ineg(+u: Nat, +w: Nat) -> {I.Int.add(I.Int.neg(I.IPos{u}), I.Int.neg(I.IPos{w})) == I.Int.neg(I.IPos{Nat.add(u, w)}) : I.Int}:
  +env : List<&2, I.Int> = [I.IPos{u}, I.IPos{w}]
  IntN(env, R.Ad(R.Ng(R.V(0n)), R.Ng(R.V(1n))), R.Ng(R.Ad(R.V(0n), R.V(1n))), [], [], {==}, Unit{})

def Lt.asym(+a: Nat, +b: Nat, +h: {RD.Nat.lt(a, b) == True{} : Bool}) -> {RD.Nat.lt(b, a) == False{} : Bool}:
  +w = RD.Nat.monus(b, 1n+a)
  +e = Equal.trans(Nat, b, 1n+Nat.add(a, w), Nat.add(a, 1n+w), Lt.wit(a, b)(h), Equal.sym(Nat, Nat.add(a, 1n+w), 1n+Nat.add(a, w), NL.Nat.add_succ_r(a, w)))
  Equal.trans(Bool, RD.Nat.lt(b, a), RD.Nat.lt(Nat.add(a, 1n+w), a), False{}, Equal.cong(Nat, Bool, z => RD.Nat.lt(z, a), b, Nat.add(a, 1n+w), e), Lt.ge(a, 1n+w))

# a - b by magnitudes
def Sdiff.lk(+h1: Nat, +a: B.Bn, +b: B.Bn, +e: Nat, lt: Bool, +elt: {B.Bn.lt(a, b) == lt : Bool}, +oa: {B.Bn.ok(1n+h1, a) == True{} : Bool}, +ob: {B.Bn.ok(1n+h1, b) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.sdiff(1n+h1, a, b, e, lt)) == D.Dy.of(e, I.Int.add(I.IPos{B.Bn.val(1n+h1, a)}, I.Int.neg(I.IPos{B.Bn.val(1n+h1, b)}))) : D.Dy}:
  match lt:
    case True{}:
      +h : Nat = 1n+h1
      +va = B.Bn.val(h, a)
      +vb = B.Bn.val(h, b)
      +vd = B.Bn.val(h, B.Bn.sub(h, b, a))
      +hab = Equal.trans(Bool, RD.Nat.lt(va, vb), B.Bn.lt(a, b), True{}, Equal.sym(Bool, B.Bn.lt(a, b), RD.Nat.lt(va, vb), Cmp.lt(h, a, b, oa, ob)), elt)
      +hd = Sub.val(h, b, a, False{}, ob, oa, Lt.asym(va, vb, hab))
      Equal.cong(I.Int, D.Dy, z => D.Dy.of(e, z), I.Int.neg(I.IPos{vd}), I.Int.add(I.IPos{va}, I.Int.neg(I.IPos{vb})),
        Equal.sym(I.Int, I.Int.add(I.IPos{va}, I.Int.neg(I.IPos{vb})), I.Int.neg(I.IPos{vd}),
          Equal.trans(I.Int, I.Int.add(I.IPos{va}, I.Int.neg(I.IPos{vb})), I.Int.add(I.IPos{va}, I.Int.neg(I.IPos{Nat.add(vd, va)})), I.Int.neg(I.IPos{vd}),
            Equal.cong(Nat, I.Int, z => I.Int.add(I.IPos{va}, I.Int.neg(I.IPos{z})), vb, Nat.add(vd, va), Equal.sym(Nat, Nat.add(vd, va), vb, hd)),
            Ipm(vd, va))))
    case False{}:
      +h : Nat = 1n+h1
      +va = B.Bn.val(h, a)
      +vb = B.Bn.val(h, b)
      +vd = B.Bn.val(h, B.Bn.sub(h, a, b))
      +hab = Equal.trans(Bool, RD.Nat.lt(va, vb), B.Bn.lt(a, b), False{}, Equal.sym(Bool, B.Bn.lt(a, b), RD.Nat.lt(va, vb), Cmp.lt(h, a, b, oa, ob)), elt)
      +hd = Sub.val(h, a, b, False{}, oa, ob, hab)
      Equal.cong(I.Int, D.Dy, z => D.Dy.of(e, z), I.IPos{vd}, I.Int.add(I.IPos{va}, I.Int.neg(I.IPos{vb})),
        Equal.sym(I.Int, I.Int.add(I.IPos{va}, I.Int.neg(I.IPos{vb})), I.IPos{vd},
          Equal.trans(I.Int, I.Int.add(I.IPos{va}, I.Int.neg(I.IPos{vb})), I.Int.add(I.IPos{Nat.add(vd, vb)}, I.Int.neg(I.IPos{vb})), I.IPos{vd},
            Equal.cong(Nat, I.Int, z => I.Int.add(I.IPos{z}, I.Int.neg(I.IPos{vb})), va, Nat.add(vd, vb), Equal.sym(Nat, Nat.add(vd, vb), va, hd)),
            Ipm2(vd, vb))))

def SAdd.lk(+h1: Nat, n1: Bool, +a: B.Bn, n2: Bool, +b: B.Bn, +e: Nat, +oa: {B.Bn.ok(1n+h1, a) == True{} : Bool}, +ob: {B.Bn.ok(1n+h1, b) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.sadd(1n+h1, n1, a, n2, b, e)) == D.Dy.of(e, I.Int.add(B.Bd.sg(n1, B.Bn.val(1n+h1, a)), B.Bd.sg(n2, B.Bn.val(1n+h1, b)))) : D.Dy}:
  match n1 n2:
    case False{} False{}:
      Equal.cong(Nat, D.Dy, z => D.Dy.of(e, I.IPos{z}), B.Bn.val(1n+h1, B.Bn.add(1n+h1, a, b)), Nat.add(B.Bn.val(1n+h1, a), B.Bn.val(1n+h1, b)), Add.val(1n+h1, a, b, False{}))
    case True{} True{}:
      +va = B.Bn.val(1n+h1, a)
      +vb = B.Bn.val(1n+h1, b)
      Equal.cong(I.Int, D.Dy, z => D.Dy.of(e, z), I.Int.neg(I.IPos{B.Bn.val(1n+h1, B.Bn.add(1n+h1, a, b))}), I.Int.add(I.Int.neg(I.IPos{va}), I.Int.neg(I.IPos{vb})),
        Equal.trans(I.Int, I.Int.neg(I.IPos{B.Bn.val(1n+h1, B.Bn.add(1n+h1, a, b))}), I.Int.neg(I.IPos{Nat.add(va, vb)}), I.Int.add(I.Int.neg(I.IPos{va}), I.Int.neg(I.IPos{vb})),
          Equal.cong(Nat, I.Int, z => I.Int.neg(I.IPos{z}), B.Bn.val(1n+h1, B.Bn.add(1n+h1, a, b)), Nat.add(va, vb), Add.val(1n+h1, a, b, False{})),
          Equal.sym(I.Int, I.Int.add(I.Int.neg(I.IPos{va}), I.Int.neg(I.IPos{vb})), I.Int.neg(I.IPos{Nat.add(va, vb)}), Ineg(va, vb))))
    case False{} True{}:
      Sdiff.lk(h1, a, b, e, B.Bn.lt(a, b), {==}, oa, ob)
    case True{} False{}:
      +va = B.Bn.val(1n+h1, a)
      +vb = B.Bn.val(1n+h1, b)
      Equal.trans(D.Dy, B.Bd.val(1n+h1, B.Bd.sdiff(1n+h1, b, a, e, B.Bn.lt(b, a))), D.Dy.of(e, I.Int.add(I.IPos{vb}, I.Int.neg(I.IPos{va}))), D.Dy.of(e, I.Int.add(I.Int.neg(I.IPos{va}), I.IPos{vb})),
        Sdiff.lk(h1, b, a, e, B.Bn.lt(b, a), {==}, ob, oa),
        Equal.cong(I.Int, D.Dy, z => D.Dy.of(e, z), I.Int.add(I.IPos{vb}, I.Int.neg(I.IPos{va})), I.Int.add(I.Int.neg(I.IPos{va}), I.IPos{vb}), Z.Int.add_comm(I.IPos{vb}, I.Int.neg(I.IPos{va}))))

# shifting a magnitude by k = e - e0 puts it over 2^e
def Shift.lk(+h1: Nat, +n: Bool, +m: B.Bn, +e0: Nat, +e: Nat, +k: Nat, +hk: {e == Nat.add(e0, k) : Nat})
  -> {D.Dy.of(e, B.Bd.sg(n, B.Bn.val(1n+h1, B.Bn.shl(1n+h1, k, m)))) == D.Dy.of(e0, B.Bd.sg(n, B.Bn.val(1n+h1, m))) : D.Dy}:
  +v = B.Bn.val(1n+h1, m)
  +s = B.Bd.sg(n, v)
  Equal.trans(D.Dy, D.Dy.of(e, B.Bd.sg(n, B.Bn.val(1n+h1, B.Bn.shl(1n+h1, k, m)))), D.Dy.of(e, D.Int.sh(k, s)), D.Dy.of(e0, s),
    Equal.cong(I.Int, D.Dy, z => D.Dy.of(e, z), B.Bd.sg(n, B.Bn.val(1n+h1, B.Bn.shl(1n+h1, k, m))), D.Int.sh(k, s),
      Equal.trans(I.Int, B.Bd.sg(n, B.Bn.val(1n+h1, B.Bn.shl(1n+h1, k, m))), B.Bd.sg(n, Nat.mul(v, RD.Nat.pow2(k))), D.Int.sh(k, s),
        Equal.cong(Nat, I.Int, z => B.Bd.sg(n, z), B.Bn.val(1n+h1, B.Bn.shl(1n+h1, k, m)), Nat.mul(v, RD.Nat.pow2(k)), Shl.val(h1, k, m)),
        Equal.sym(I.Int, D.Int.sh(k, s), B.Bd.sg(n, Nat.mul(v, RD.Nat.pow2(k))), Sg.sh(n, k, v)))),
    Equal.trans(D.Dy, D.Dy.of(e, D.Int.sh(k, s)), D.Dy.of(Nat.add(e0, k), D.Int.sh(k, s)), D.Dy.of(e0, s),
      Equal.cong(Nat, D.Dy, z => D.Dy.of(z, D.Int.sh(k, s)), e, Nat.add(e0, k), hk), Y.Of.shift(k, e0, s)))

def Addal.lk(+h1: Nat, +n1: Bool, +m1: B.Bn, +e1: Nat, +n2: Bool, +m2: B.Bn, +e2: Nat, lt: Bool, +elt: {F.Nat.ltf(e2, e1) == lt : Bool},
  +o1: {B.Bn.ok(1n+h1, m1) == True{} : Bool}, +o2: {B.Bn.ok(1n+h1, m2) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.addal(1n+h1, n1, m1, e1, n2, m2, e2, lt)) == D.Dy.add(D.Dy.of(e1, B.Bd.sg(n1, B.Bn.val(1n+h1, m1))), D.Dy.of(e2, B.Bd.sg(n2, B.Bn.val(1n+h1, m2)))) : D.Dy}:
  match lt:
    case True{}:
      +h : Nat = 1n+h1
      +k = F.Nat.monusf(e1, e2)
      +s1 = B.Bd.sg(n1, B.Bn.val(h, m1))
      +s2 = B.Bd.sg(n2, B.Bn.val(h, m2))
      +m2s = B.Bn.shl(h, k, m2)
      +s2s = B.Bd.sg(n2, B.Bn.val(h, m2s))
      +hk = Equal.trans(Nat, e1, Nat.add(e2, RD.Nat.monus(e1, e2)), Nat.add(e2, k), R.Nat.lt_t(e2, e1)(Equal.trans(Bool, RD.Nat.lt(e2, e1), F.Nat.ltf(e2, e1), True{}, FL.L.lt(e2, e1), elt)),
        Equal.cong(Nat, Nat, z => Nat.add(e2, z), RD.Nat.monus(e1, e2), k, FL.L.monus(e1, e2)))
      Equal.trans(D.Dy, B.Bd.val(h, B.Bd.sadd(h, n1, m1, n2, m2s, e1)), D.Dy.of(e1, I.Int.add(s1, s2s)), D.Dy.add(D.Dy.of(e1, s1), D.Dy.of(e2, s2)),
        SAdd.lk(h1, n1, m1, n2, m2s, e1, o1, Shl.ok(h1, k, m2, o2)),
        Equal.trans(D.Dy, D.Dy.of(e1, I.Int.add(s1, s2s)), D.Dy.add(D.Dy.of(e1, s1), D.Dy.of(e1, s2s)), D.Dy.add(D.Dy.of(e1, s1), D.Dy.of(e2, s2)),
          Equal.sym(D.Dy, D.Dy.add(D.Dy.of(e1, s1), D.Dy.of(e1, s2s)), D.Dy.of(e1, I.Int.add(s1, s2s)), AddE(e1, s1, s2s)),
          Equal.cong(D.Dy, D.Dy, z => D.Dy.add(D.Dy.of(e1, s1), z), D.Dy.of(e1, s2s), D.Dy.of(e2, s2), Shift.lk(h1, n2, m2, e2, e1, k, hk))))
    case False{}:
      +h : Nat = 1n+h1
      +k = F.Nat.monusf(e2, e1)
      +s1 = B.Bd.sg(n1, B.Bn.val(h, m1))
      +s2 = B.Bd.sg(n2, B.Bn.val(h, m2))
      +m1s = B.Bn.shl(h, k, m1)
      +s1s = B.Bd.sg(n1, B.Bn.val(h, m1s))
      +hk = Equal.trans(Nat, e2, Nat.add(e1, RD.Nat.monus(e2, e1)), Nat.add(e1, k), R.Nat.lt_f(e2, e1)(Equal.trans(Bool, RD.Nat.lt(e2, e1), F.Nat.ltf(e2, e1), False{}, FL.L.lt(e2, e1), elt)),
        Equal.cong(Nat, Nat, z => Nat.add(e1, z), RD.Nat.monus(e2, e1), k, FL.L.monus(e2, e1)))
      Equal.trans(D.Dy, B.Bd.val(h, B.Bd.sadd(h, n1, m1s, n2, m2, e2)), D.Dy.of(e2, I.Int.add(s1s, s2)), D.Dy.add(D.Dy.of(e1, s1), D.Dy.of(e2, s2)),
        SAdd.lk(h1, n1, m1s, n2, m2, e2, Shl.ok(h1, k, m1, o1), o2),
        Equal.trans(D.Dy, D.Dy.of(e2, I.Int.add(s1s, s2)), D.Dy.add(D.Dy.of(e2, s1s), D.Dy.of(e2, s2)), D.Dy.add(D.Dy.of(e1, s1), D.Dy.of(e2, s2)),
          Equal.sym(D.Dy, D.Dy.add(D.Dy.of(e2, s1s), D.Dy.of(e2, s2)), D.Dy.of(e2, I.Int.add(s1s, s2)), AddE(e2, s1s, s2)),
          Equal.cong(D.Dy, D.Dy, z => D.Dy.add(z, D.Dy.of(e2, s2)), D.Dy.of(e2, s1s), D.Dy.of(e1, s1), Shift.lk(h1, n1, m1, e1, e2, k, hk))))

def Bd.add.lk(+h1: Nat, x: B.Bd, y: B.Bd, +ox: {B.Bd.ok(1n+h1, x) == True{} : Bool}, +oy: {B.Bd.ok(1n+h1, y) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.add(1n+h1, x, y)) == D.Dy.add(B.Bd.val(1n+h1, x), B.Bd.val(1n+h1, y)) : D.Dy}:
  match x y:
    case B.Bd{+n1, +m1, +e1} B.Bd{+n2, +m2, +e2}:
      Addal.lk(h1, n1, m1, e1, n2, m2, e2, F.Nat.ltf(e2, e1), {==}, ox, oy)

def Sdiff.ok(+h: Nat, +a: B.Bn, +b: B.Bn, +e: Nat, lt: Bool, +oa: {B.Bn.ok(h, a) == True{} : Bool}, +ob: {B.Bn.ok(h, b) == True{} : Bool})
  -> {B.Bd.ok(h, B.Bd.sdiff(h, a, b, e, lt)) == True{} : Bool}:
  match lt:
    case True{}:
      Sub.ok(h, b, a, False{}, ob, oa)
    case False{}:
      Sub.ok(h, a, b, False{}, oa, ob)

def SAdd.ok(+h1: Nat, n1: Bool, +a: B.Bn, n2: Bool, +b: B.Bn, +e: Nat, +oa: {B.Bn.ok(1n+h1, a) == True{} : Bool}, +ob: {B.Bn.ok(1n+h1, b) == True{} : Bool})
  -> {B.Bd.ok(1n+h1, B.Bd.sadd(1n+h1, n1, a, n2, b, e)) == True{} : Bool}:
  match n1 n2:
    case False{} False{}:
      Add.ok(h1, a, b, False{}, oa, ob)
    case True{} True{}:
      Add.ok(h1, a, b, False{}, oa, ob)
    case False{} True{}:
      Sdiff.ok(1n+h1, a, b, e, B.Bn.lt(a, b), oa, ob)
    case True{} False{}:
      Sdiff.ok(1n+h1, b, a, e, B.Bn.lt(b, a), ob, oa)

def Addal.ok(+h1: Nat, +n1: Bool, +m1: B.Bn, +e1: Nat, +n2: Bool, +m2: B.Bn, +e2: Nat, lt: Bool, +o1: {B.Bn.ok(1n+h1, m1) == True{} : Bool}, +o2: {B.Bn.ok(1n+h1, m2) == True{} : Bool})
  -> {B.Bd.ok(1n+h1, B.Bd.addal(1n+h1, n1, m1, e1, n2, m2, e2, lt)) == True{} : Bool}:
  match lt:
    case True{}:
      SAdd.ok(h1, n1, m1, n2, B.Bn.shl(1n+h1, F.Nat.monusf(e1, e2), m2), e1, o1, Shl.ok(h1, F.Nat.monusf(e1, e2), m2, o2))
    case False{}:
      SAdd.ok(h1, n1, B.Bn.shl(1n+h1, F.Nat.monusf(e2, e1), m1), n2, m2, e2, Shl.ok(h1, F.Nat.monusf(e2, e1), m1, o1), o2)

def Bd.add.ok(+h1: Nat, x: B.Bd, y: B.Bd, +ox: {B.Bd.ok(1n+h1, x) == True{} : Bool}, +oy: {B.Bd.ok(1n+h1, y) == True{} : Bool})
  -> {B.Bd.ok(1n+h1, B.Bd.add(1n+h1, x, y)) == True{} : Bool}:
  match x y:
    case B.Bd{+n1, +m1, +e1} B.Bd{+n2, +m2, +e2}:
      Addal.ok(h1, n1, m1, e1, n2, m2, e2, F.Nat.ltf(e2, e1), ox, oy)

# Normal forms
# ------------

def Sg.even(+n: Bool, +v: Nat) -> {D.Int.even(B.Bd.sg(n, v)) == D.Nat.even(v) : Bool}:
  match n:
    case False{}:
      {==}
    case True{}:
      match v:
        case 0n:
          {==}
        case 1n+k:
          Equal.sym(Bool, D.Nat.even(1n+k), Bool.not(D.Nat.even(k)), Y.Nat.even_succ(k))

def Sg.half(+n: Bool, +v: Nat, +ev: {D.Nat.even(v) == True{} : Bool}) -> {D.Int.half(B.Bd.sg(n, v)) == B.Bd.sg(n, D.Nat.half(v)) : I.Int}:
  match n:
    case False{}:
      {==}
    case True{}:
      match v:
        case 0n:
          {==}
        case 1n+k:
          # k is odd: k = 1 + 2j, half(1 + k) = 1 + j
          +j = D.Nat.half(k)
          +ek = Y.Nat.odd_split(k)(Equal.trans(Bool, D.Nat.even(k), Bool.not(Bool.not(D.Nat.even(k))), False{}, Equal.sym(Bool, Bool.not(Bool.not(D.Nat.even(k))), D.Nat.even(k), Y.Bool.not_not(D.Nat.even(k))),
            Equal.cong(Bool, Bool, z => Bool.not(z), Bool.not(D.Nat.even(k)), True{}, Equal.trans(Bool, Bool.not(D.Nat.even(k)), D.Nat.even(1n+k), True{}, Equal.sym(Bool, D.Nat.even(1n+k), Bool.not(D.Nat.even(k)), Y.Nat.even_succ(k)), ev))))
          +eh = Equal.trans(Nat, D.Nat.half(1n+k), D.Nat.half(2n+Nat.double(j)), 1n+j, Equal.cong(Nat, Nat, z => D.Nat.half(1n+z), k, 1n+Nat.double(j), ek),
            Equal.cong(Nat, Nat, z => 1n+z, D.Nat.half(Nat.double(j)), j, Y.Nat.half_double(j)))
          Equal.sym(I.Int, I.Int.neg(I.IPos{D.Nat.half(1n+k)}), I.INeg{j}, Equal.cong(Nat, I.Int, z => I.Int.neg(I.IPos{z}), D.Nat.half(1n+k), 1n+j, eh))

def Sg.mag(+n: Bool, +v: Nat) -> {RD.Int.mag(B.Bd.sg(n, v)) == v : Nat}:
  match n:
    case False{}:
      {==}
    case True{}:
      match v:
        case 0n:
          {==}
        case 1n+k:
          {==}

# a normal form: the value's denominator and numerator are the fields
def NF(h: Nat, r: B.Bd) -> Type:
  {D.Dy.den(B.Bd.val(h, r)) == B.Bd.e(r) : Nat} & {D.Dy.num(B.Bd.val(h, r)) == B.Bd.sg(B.Bd.n(r), B.Bn.val(h, B.Bd.m(r))) : I.Int}

def Norm.val(+h: Nat, +neg: Bool, e: Nat, +m: B.Bn, ev: Bool, +eev: {B.Bn.even(m) == ev : Bool})
  -> {B.Bd.val(h, B.Bd.norm.go(h, neg, e, m, ev)) == D.Dy.of(e, B.Bd.sg(neg, B.Bn.val(h, m))) : D.Dy}:
  match e:
    case 0n:
      {==}
    case 1n+(+f):
      match ev:
        case True{}:
          +v = B.Bn.val(h, m)
          +hm = B.Bn.half(h, m)
          +evv = Equal.trans(Bool, D.Nat.even(v), B.Bn.even(m), True{}, Equal.sym(Bool, B.Bn.even(m), D.Nat.even(v), Even.val(h, m)), eev)
          Equal.trans(D.Dy, B.Bd.val(h, B.Bd.norm.go(h, neg, f, hm, B.Bn.even(hm))), D.Dy.of(f, B.Bd.sg(neg, B.Bn.val(h, hm))), D.Dy.of(1n+f, B.Bd.sg(neg, v)),
            Norm.val(h, neg, f, hm, B.Bn.even(hm), {==}),
            Equal.trans(D.Dy, D.Dy.of(f, B.Bd.sg(neg, B.Bn.val(h, hm))), D.Dy.of(f, D.Int.half(B.Bd.sg(neg, v))), D.Dy.of(1n+f, B.Bd.sg(neg, v)),
              Equal.cong(I.Int, D.Dy, z => D.Dy.of(f, z), B.Bd.sg(neg, B.Bn.val(h, hm)), D.Int.half(B.Bd.sg(neg, v)),
                Equal.trans(I.Int, B.Bd.sg(neg, B.Bn.val(h, hm)), B.Bd.sg(neg, D.Nat.half(v)), D.Int.half(B.Bd.sg(neg, v)),
                  Equal.cong(Nat, I.Int, z => B.Bd.sg(neg, z), B.Bn.val(h, hm), D.Nat.half(v), Half.val(h, m)),
                  Equal.sym(I.Int, D.Int.half(B.Bd.sg(neg, v)), B.Bd.sg(neg, D.Nat.half(v)), Sg.half(neg, v, evv)))),
              Equal.sym(D.Dy, D.Dy.of(1n+f, B.Bd.sg(neg, v)), D.Dy.of(f, D.Int.half(B.Bd.sg(neg, v))),
                Y.Of.even(f, B.Bd.sg(neg, v), Equal.trans(Bool, D.Int.even(B.Bd.sg(neg, v)), D.Nat.even(v), True{}, Sg.even(neg, v), evv)))))
        case False{}:
          {==}

def Norm.nf(+h: Nat, +neg: Bool, e: Nat, +m: B.Bn, ev: Bool, +eev: {B.Bn.even(m) == ev : Bool}) -> NF(h, B.Bd.norm.go(h, neg, e, m, ev)):
  match e:
    case 0n:
      ({==}, {==})
    case 1n+(+f):
      match ev:
        case True{}:
          Norm.nf(h, neg, f, B.Bn.half(h, m), B.Bn.even(B.Bn.half(h, m)), {==})
        case False{}:
          +v = B.Bn.val(h, m)
          +s = B.Bd.sg(neg, v)
          +od = Equal.trans(Bool, D.Int.even(s), D.Nat.even(v), False{}, Sg.even(neg, v), Equal.trans(Bool, D.Nat.even(v), B.Bn.even(m), False{}, Equal.sym(Bool, B.Bn.even(m), D.Nat.even(v), Even.val(h, m)), eev))
          +eo = Y.Of.odd(f, s, od)
          (Equal.trans(Nat, D.Dy.den(D.Dy.of(1n+f, s)), D.Dy.den(D.Dy.odd(s, f)), 1n+f, Equal.cong(D.Dy, Nat, z => D.Dy.den(z), D.Dy.of(1n+f, s), D.Dy.odd(s, f), eo), Y.Odd.den(s, f)),
           Equal.trans(I.Int, D.Dy.num(D.Dy.of(1n+f, s)), D.Dy.num(D.Dy.odd(s, f)), s, Equal.cong(D.Dy, I.Int, z => D.Dy.num(z), D.Dy.of(1n+f, s), D.Dy.odd(s, f), Y.Of.odd(f, s, od)), Y.Odd.num(s, f)(od)))

def Norm.ok(+h: Nat, +neg: Bool, e: Nat, +m: B.Bn, ev: Bool, +om: {B.Bn.ok(h, m) == True{} : Bool}) -> {B.Bn.ok(h, B.Bd.m(B.Bd.norm.go(h, neg, e, m, ev))) == True{} : Bool}:
  match e:
    case 0n:
      om
    case 1n+(+f):
      match ev:
        case True{}:
          Norm.ok(h, neg, f, B.Bn.half(h, m), B.Bn.even(B.Bn.half(h, m)), Half.ok(h, m, om))
        case False{}:
          om

# Rounding big dyadics
# --------------------

def Rne.mag(+h1: Nat, +p: Nat, +m: B.Bn, +om: {B.Bn.ok(1n+h1, m) == True{} : Bool})
  -> {B.Bn.val(1n+h1, B.TrB.near(1n+h1, B.TrB.of(1n+h1, p, m))) == RD.Tr.near(RD.Tr.of(p, B.Bn.val(1n+h1, m))) : Nat}:
  +h : Nat = 1n+h1
  +pw = B.Bn.pow2(h, p)
  Near.lk(h1, B.TrB.of(h, p, m), RD.Tr.of(p, B.Bn.val(h, m)), Of.lk(h1, p, m, om), Of.lk(h1, p, m, om),
    Go.ok(h1, Nat.mul(h, B.Bn.len(m)), pw, m, B.Bn.lt(m, pw), om))

def Rfix.mag(+h1: Nat, +s: Nat, +m: B.Bn, +om: {B.Bn.ok(1n+h1, m) == True{} : Bool})
  -> {B.Bn.val(1n+h1, B.TrB.near(1n+h1, B.FxB.go(1n+h1, s, m))) == RD.Tr.near(RD.Fx.go(s, B.Bn.val(1n+h1, m))) : Nat}:
  +h : Nat = 1n+h1
  Near.lk(h1, B.FxB.go(h, s, m), RD.Fx.go(s, B.Bn.val(h, m)), Fx.lk(h1, s, m, B.Bn.val(h, m), {==}), Fx.lk(h1, s, m, B.Bn.val(h, m), {==}), Fx.ok(h1, s, m, om))

def Pow2.pos(+s: Nat) -> {RD.Nat.lt(0n, RD.Nat.pow2(s)) == True{} : Bool}:
  +w = RD.Nat.monus(RD.Nat.pow2(s), 1n+s)
  Equal.cong(Nat, Bool, z => RD.Nat.lt(0n, z), RD.Nat.pow2(s), Nat.add(1n+s, w), Lt.wit(s, RD.Nat.pow2(s))(Lt.npow(s)))

def Up.q(t: RD.Tr, +b: Nat, +w: Nat) -> {RD.Tr.q(RD.Tr.up(t, b, w)) == RD.Tr.q(t) : Nat}:
  match t:
    case RD.Tr{s, q, r, wr, wq}:
      {==}

def Up.r(t: RD.Tr, +b: Nat, +w: Nat) -> {R.Tr.r(RD.Tr.up(t, b, w)) == Nat.add(Nat.double(R.Tr.r(t)), b) : Nat}:
  match t:
    case RD.Tr{s, q, r, wr, wq}:
      {==}

def Rup.acc(t: RD.Tr) -> {RD.Tr.rup(t) == Bool.and(Bool.not(RD.Nat.lt(Nat.double(R.Tr.r(t)), RD.Nat.pow2(RD.Tr.s(t)))), Bool.or(RD.Nat.lt(RD.Nat.pow2(RD.Tr.s(t)), Nat.double(R.Tr.r(t))), Bool.not(D.Nat.even(RD.Tr.q(t))))) : Bool}:
  match t:
    case RD.Tr{s, q, r, wr, wq}:
      {==}

# rounding 0 to the grid gives 0
def Fx0.qr(s: Nat) -> {RD.Tr.q(RD.Fx.go(s, 0n)) == 0n : Nat} & {R.Tr.r(RD.Fx.go(s, 0n)) == 0n : Nat}:
  match s:
    case 0n:
      ({==}, {==})
    case 1n+(+j):
      +qa = RD.Tr.q(RD.Fx.go(j, 0n))
      +ra = R.Tr.r(RD.Fx.go(j, 0n))
      (Equal.trans(Nat, RD.Tr.q(RD.Tr.up(RD.Fx.go(j, 0n), 0n, 0n)), qa, 0n, Up.q(RD.Fx.go(j, 0n), 0n, 0n), Pair.fst({qa == 0n : Nat}, {ra == 0n : Nat}, Fx0.qr(j))),
       Equal.trans(Nat, R.Tr.r(RD.Tr.up(RD.Fx.go(j, 0n), 0n, 0n)), Nat.add(Nat.double(ra), 0n), 0n, Up.r(RD.Fx.go(j, 0n), 0n, 0n),
         Equal.cong(Nat, Nat, z => Nat.add(Nat.double(z), 0n), ra, 0n, Pair.snd({qa == 0n : Nat}, {ra == 0n : Nat}, Fx0.qr(j)))))

def Fx0(+s: Nat) -> {RD.Tr.near(RD.Fx.go(s, 0n)) == 0n : Nat}:
  +t = RD.Fx.go(s, 0n)
  +er2 : {R.Tr.r(RD.Fx.go(s, 0n)) == 0n : Nat} = Pair.snd({RD.Tr.q(t) == 0n : Nat}, {R.Tr.r(t) == 0n : Nat}, Fx0.qr(s))
  +eq : {RD.Tr.q(RD.Fx.go(s, 0n)) == 0n : Nat} = Pair.fst({RD.Tr.q(t) == 0n : Nat}, {R.Tr.r(t) == 0n : Nat}, Fx0.qr(s))
  +eu = Equal.trans(Bool, RD.Tr.rup(t), Bool.and(Bool.not(RD.Nat.lt(Nat.double(R.Tr.r(t)), RD.Nat.pow2(RD.Tr.s(t)))), Bool.or(RD.Nat.lt(RD.Nat.pow2(RD.Tr.s(t)), Nat.double(R.Tr.r(t))), Bool.not(D.Nat.even(RD.Tr.q(t))))), False{},
    Rup.acc(t),
    Equal.trans(Bool, Bool.and(Bool.not(RD.Nat.lt(Nat.double(R.Tr.r(t)), RD.Nat.pow2(RD.Tr.s(t)))), Bool.or(RD.Nat.lt(RD.Nat.pow2(RD.Tr.s(t)), Nat.double(R.Tr.r(t))), Bool.not(D.Nat.even(RD.Tr.q(t))))),
      Bool.and(Bool.not(RD.Nat.lt(0n, RD.Nat.pow2(RD.Tr.s(t)))), Bool.or(RD.Nat.lt(RD.Nat.pow2(RD.Tr.s(t)), 0n), Bool.not(D.Nat.even(RD.Tr.q(t))))), False{},
      Equal.cong(Nat, Bool, z => Bool.and(Bool.not(RD.Nat.lt(Nat.double(z), RD.Nat.pow2(RD.Tr.s(t)))), Bool.or(RD.Nat.lt(RD.Nat.pow2(RD.Tr.s(t)), Nat.double(z)), Bool.not(D.Nat.even(RD.Tr.q(t))))), R.Tr.r(t), 0n, er2),
      Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), Bool.or(RD.Nat.lt(RD.Nat.pow2(RD.Tr.s(t)), 0n), Bool.not(D.Nat.even(RD.Tr.q(t))))), RD.Nat.lt(0n, RD.Nat.pow2(RD.Tr.s(t))), True{}, Pow2.pos(RD.Tr.s(t)))))
  Equal.trans(Nat, RD.Tr.near(t), Nat.mul(RD.Tr.q(t), RD.Nat.pow2(RD.Tr.s(t))), 0n, R.Near.dn(t, eu),
    Equal.cong(Nat, Nat, z => Nat.mul(z, RD.Nat.pow2(RD.Tr.s(t))), RD.Tr.q(t), 0n, eq))

def Sgn.near(+n: Bool, +v: Nat, +p: Nat) -> {RD.Int.signed(B.Bd.sg(n, v), RD.Tr.near(RD.Tr.of(p, v))) == B.Bd.sg(n, RD.Tr.near(RD.Tr.of(p, v))) : I.Int}:
  match n:
    case False{}:
      {==}
    case True{}:
      match v:
        case 0n:
          {==}
        case 1n+k:
          {==}

def Sgn.fix(+n: Bool, +v: Nat, +s: Nat) -> {RD.Int.signed(B.Bd.sg(n, v), RD.Tr.near(RD.Fx.go(s, v))) == B.Bd.sg(n, RD.Tr.near(RD.Fx.go(s, v))) : I.Int}:
  match n:
    case False{}:
      {==}
    case True{}:
      match v:
        case 0n:
          +e = Fx0(s)
          +e2 = Fx0(s)
          Equal.trans(I.Int, I.IPos{RD.Tr.near(RD.Fx.go(s, 0n))}, I.IPos{0n}, I.Int.neg(I.IPos{RD.Tr.near(RD.Fx.go(s, 0n))}),
            Equal.cong(Nat, I.Int, z => I.IPos{z}, RD.Tr.near(RD.Fx.go(s, 0n)), 0n, e),
            Equal.cong(Nat, I.Int, z => I.Int.neg(I.IPos{z}), 0n, RD.Tr.near(RD.Fx.go(s, 0n)), Equal.sym(Nat, RD.Tr.near(RD.Fx.go(s, 0n)), 0n, e2)))
        case 1n+k:
          {==}

def Rne.n.lk(+h1: Nat, +p: Nat, r: B.Bd, nf: NF(1n+h1, r), +om: {B.Bn.ok(1n+h1, B.Bd.m(r)) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.rne.n(1n+h1, p, r)) == RD.Dy.rne(p, B.Bd.val(1n+h1, r)) : D.Dy}:
  match r:
    case B.Bd{+neg, +m, +e}:
      match nf:
        case (ed, en):
          +h : Nat = 1n+h1
          +v = B.Bn.val(h, m)
          +x = D.Dy.of(e, B.Bd.sg(neg, v))
          +sg = B.Bd.sg(neg, v)
          +rr = RD.Tr.near(RD.Tr.of(p, v))
          +en2 : {D.Dy.num(x) == sg : I.Int} = en
          Equal.trans(D.Dy, D.Dy.of(e, B.Bd.sg(neg, B.Bn.val(h, B.TrB.near(h, B.TrB.of(h, p, m))))), D.Dy.of(e, B.Bd.sg(neg, rr)), RD.Dy.rne(p, x),
            Equal.cong(Nat, D.Dy, z => D.Dy.of(e, B.Bd.sg(neg, z)), B.Bn.val(h, B.TrB.near(h, B.TrB.of(h, p, m))), rr, Rne.mag(h1, p, m, om)),
            Equal.sym(D.Dy, RD.Dy.rne(p, x), D.Dy.of(e, B.Bd.sg(neg, rr)),
              Equal.trans(D.Dy, D.Dy.of(D.Dy.den(x), RD.Int.signed(D.Dy.num(x), RD.Tr.near(RD.Tr.of(p, RD.Int.mag(D.Dy.num(x)))))), D.Dy.of(e, RD.Int.signed(sg, RD.Tr.near(RD.Tr.of(p, RD.Int.mag(sg))))), D.Dy.of(e, B.Bd.sg(neg, rr)),
                Equal.trans(D.Dy, D.Dy.of(D.Dy.den(x), RD.Int.signed(D.Dy.num(x), RD.Tr.near(RD.Tr.of(p, RD.Int.mag(D.Dy.num(x)))))), D.Dy.of(e, RD.Int.signed(D.Dy.num(x), RD.Tr.near(RD.Tr.of(p, RD.Int.mag(D.Dy.num(x)))))), D.Dy.of(e, RD.Int.signed(sg, RD.Tr.near(RD.Tr.of(p, RD.Int.mag(sg))))),
                  Equal.cong(Nat, D.Dy, z => D.Dy.of(z, RD.Int.signed(D.Dy.num(x), RD.Tr.near(RD.Tr.of(p, RD.Int.mag(D.Dy.num(x)))))), D.Dy.den(x), e, ed),
                  Equal.cong(I.Int, D.Dy, z => D.Dy.of(e, RD.Int.signed(z, RD.Tr.near(RD.Tr.of(p, RD.Int.mag(z))))), D.Dy.num(x), sg, en2)),
                Equal.cong(I.Int, D.Dy, z => D.Dy.of(e, z), RD.Int.signed(sg, RD.Tr.near(RD.Tr.of(p, RD.Int.mag(sg)))), B.Bd.sg(neg, rr),
                  Equal.trans(I.Int, RD.Int.signed(sg, RD.Tr.near(RD.Tr.of(p, RD.Int.mag(sg)))), RD.Int.signed(sg, rr), B.Bd.sg(neg, rr),
                    Equal.cong(Nat, I.Int, z => RD.Int.signed(sg, RD.Tr.near(RD.Tr.of(p, z))), RD.Int.mag(sg), v, Sg.mag(neg, v)),
                    Sgn.near(neg, v, p))))))

def Rfixp.go(+h1: Nat, +k: Nat, +neg: Bool, +m: B.Bn, +e: Nat, lt: Bool, +om: {B.Bn.ok(1n+h1, m) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.rfix.p(1n+h1, k, neg, m, e, lt))
      == Bool.pick(D.Dy, lt, D.Dy.of(e, RD.Int.signed(B.Bd.sg(neg, B.Bn.val(1n+h1, m)), RD.Tr.near(RD.Fx.go(RD.Nat.monus(e, k), RD.Int.mag(B.Bd.sg(neg, B.Bn.val(1n+h1, m))))))), D.Dy.of(e, B.Bd.sg(neg, B.Bn.val(1n+h1, m)))) : D.Dy}:
  match lt:
    case True{}:
      +h : Nat = 1n+h1
      +v = B.Bn.val(h, m)
      +sg = B.Bd.sg(neg, v)
      +kf = F.Nat.monusf(e, k)
      +kk = RD.Nat.monus(e, k)
      +rr = RD.Tr.near(RD.Fx.go(kk, v))
      Equal.cong(I.Int, D.Dy, z => D.Dy.of(e, z), B.Bd.sg(neg, B.Bn.val(h, B.TrB.near(h, B.FxB.go(h, kf, m)))), RD.Int.signed(sg, RD.Tr.near(RD.Fx.go(kk, RD.Int.mag(sg)))),
        Equal.trans(I.Int, B.Bd.sg(neg, B.Bn.val(h, B.TrB.near(h, B.FxB.go(h, kf, m)))), B.Bd.sg(neg, rr), RD.Int.signed(sg, RD.Tr.near(RD.Fx.go(kk, RD.Int.mag(sg)))),
          Equal.cong(Nat, I.Int, z => B.Bd.sg(neg, z), B.Bn.val(h, B.TrB.near(h, B.FxB.go(h, kf, m))), rr,
            Equal.trans(Nat, B.Bn.val(h, B.TrB.near(h, B.FxB.go(h, kf, m))), RD.Tr.near(RD.Fx.go(kf, v)), rr, Rfix.mag(h1, kf, m, om),
              Equal.cong(Nat, Nat, z => RD.Tr.near(RD.Fx.go(z, v)), kf, kk, Equal.sym(Nat, kk, kf, FL.L.monus(e, k))))),
          Equal.sym(I.Int, RD.Int.signed(sg, RD.Tr.near(RD.Fx.go(kk, RD.Int.mag(sg)))), B.Bd.sg(neg, rr),
            Equal.trans(I.Int, RD.Int.signed(sg, RD.Tr.near(RD.Fx.go(kk, RD.Int.mag(sg)))), RD.Int.signed(sg, rr), B.Bd.sg(neg, rr),
              Equal.cong(Nat, I.Int, z => RD.Int.signed(sg, RD.Tr.near(RD.Fx.go(kk, z))), RD.Int.mag(sg), v, Sg.mag(neg, v)),
              Sgn.fix(neg, v, kk)))))
    case False{}:
      {==}

def Rfixp.lk(+h1: Nat, +k: Nat, +neg: Bool, +m: B.Bn, +e: Nat, lt: Bool, +elt: {F.Nat.ltf(k, e) == lt : Bool}, +om: {B.Bn.ok(1n+h1, m) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.rfix.p(1n+h1, k, neg, m, e, lt))
      == Bool.pick(D.Dy, RD.Nat.lt(k, e), D.Dy.of(e, RD.Int.signed(B.Bd.sg(neg, B.Bn.val(1n+h1, m)), RD.Tr.near(RD.Fx.go(RD.Nat.monus(e, k), RD.Int.mag(B.Bd.sg(neg, B.Bn.val(1n+h1, m))))))), D.Dy.of(e, B.Bd.sg(neg, B.Bn.val(1n+h1, m)))) : D.Dy}:
  +el = Equal.sym(Bool, RD.Nat.lt(k, e), lt, Equal.trans(Bool, RD.Nat.lt(k, e), F.Nat.ltf(k, e), lt, FL.L.lt(k, e), elt))
  %el : {B.Bd.val(1n+h1, B.Bd.rfix.p(1n+h1, k, neg, m, e, lt)) == Bool.pick(D.Dy, _, D.Dy.of(e, RD.Int.signed(B.Bd.sg(neg, B.Bn.val(1n+h1, m)), RD.Tr.near(RD.Fx.go(RD.Nat.monus(e, k), RD.Int.mag(B.Bd.sg(neg, B.Bn.val(1n+h1, m))))))), D.Dy.of(e, B.Bd.sg(neg, B.Bn.val(1n+h1, m)))) : D.Dy}
  Rfixp.go(h1, k, neg, m, e, lt, om)

def Rfix.n.lk(+h1: Nat, +k: Nat, r: B.Bd, nf: NF(1n+h1, r), +om: {B.Bn.ok(1n+h1, B.Bd.m(r)) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.rfix.n(1n+h1, k, r)) == RD.Dy.rfix(k, B.Bd.val(1n+h1, r)) : D.Dy}:
  match r:
    case B.Bd{+neg, +m, +e}:
      match nf:
        case (ed, en):
          +h : Nat = 1n+h1
          +v = B.Bn.val(h, m)
          +sg = B.Bd.sg(neg, v)
          +x = D.Dy.of(e, sg)
          +en2 : {D.Dy.num(x) == sg : I.Int} = en
          Equal.trans(D.Dy, B.Bd.val(h, B.Bd.rfix.p(h, k, neg, m, e, F.Nat.ltf(k, e))),
            Bool.pick(D.Dy, RD.Nat.lt(k, e), D.Dy.of(e, RD.Int.signed(sg, RD.Tr.near(RD.Fx.go(RD.Nat.monus(e, k), RD.Int.mag(sg))))), x), RD.Dy.rfix(k, x),
            Rfixp.lk(h1, k, neg, m, e, F.Nat.ltf(k, e), {==}, om),
            Equal.sym(D.Dy, RD.Dy.rfix(k, x), Bool.pick(D.Dy, RD.Nat.lt(k, e), D.Dy.of(e, RD.Int.signed(sg, RD.Tr.near(RD.Fx.go(RD.Nat.monus(e, k), RD.Int.mag(sg))))), x),
              Equal.trans(D.Dy, RD.Dy.rfix(k, x), Bool.pick(D.Dy, RD.Nat.lt(k, e), D.Dy.of(e, RD.Int.signed(D.Dy.num(x), RD.Tr.near(RD.Fx.go(RD.Nat.monus(e, k), RD.Int.mag(D.Dy.num(x)))))), x),
                Bool.pick(D.Dy, RD.Nat.lt(k, e), D.Dy.of(e, RD.Int.signed(sg, RD.Tr.near(RD.Fx.go(RD.Nat.monus(e, k), RD.Int.mag(sg))))), x),
                Equal.cong(Nat, D.Dy, d => Bool.pick(D.Dy, RD.Nat.lt(k, d), D.Dy.of(d, RD.Int.signed(D.Dy.num(x), RD.Tr.near(RD.Fx.go(RD.Nat.monus(d, k), RD.Int.mag(D.Dy.num(x)))))), x), D.Dy.den(x), e, ed),
                Equal.cong(I.Int, D.Dy, z => Bool.pick(D.Dy, RD.Nat.lt(k, e), D.Dy.of(e, RD.Int.signed(z, RD.Tr.near(RD.Fx.go(RD.Nat.monus(e, k), RD.Int.mag(z))))), x), D.Dy.num(x), sg, en2))))

def Bige.lk(+h1: Nat, +emin: Nat, r: B.Bd, nf: NF(1n+h1, r), +om: {B.Bn.ok(1n+h1, B.Bd.m(r)) == True{} : Bool})
  -> {B.Bd.bige(1n+h1, emin, r) == RD.Dy.bige(emin, B.Bd.val(1n+h1, r)) : Bool}:
  match r:
    case B.Bd{+neg, +m, +e}:
      match nf:
        case (ed, en):
          +h : Nat = 1n+h1
          +v = B.Bn.val(h, m)
          +sg = B.Bd.sg(neg, v)
          +x = D.Dy.of(e, sg)
          +j = RD.Nat.monus(e, emin)
          +jf = F.Nat.monusf(e, emin)
          +en2 : {D.Dy.num(x) == sg : I.Int} = en
          +rhs = Bool.pick(Bool, RD.Nat.lt(emin, e), Bool.not(RD.Nat.lt(v, RD.Nat.pow2(j))), True{})
          +el = Equal.trans(Bool, Bool.pick(Bool, F.Nat.ltf(emin, e), Bool.not(B.Bn.lt(m, B.Bn.pow2(h, jf))), True{}), Bool.pick(Bool, RD.Nat.lt(emin, e), Bool.not(B.Bn.lt(m, B.Bn.pow2(h, jf))), True{}), rhs,
            Equal.cong(Bool, Bool, z => Bool.pick(Bool, z, Bool.not(B.Bn.lt(m, B.Bn.pow2(h, jf))), True{}), F.Nat.ltf(emin, e), RD.Nat.lt(emin, e), Equal.sym(Bool, RD.Nat.lt(emin, e), F.Nat.ltf(emin, e), FL.L.lt(emin, e))),
            Equal.cong(Bool, Bool, z => Bool.pick(Bool, RD.Nat.lt(emin, e), Bool.not(z), True{}), B.Bn.lt(m, B.Bn.pow2(h, jf)), RD.Nat.lt(v, RD.Nat.pow2(j)),
              Equal.trans(Bool, B.Bn.lt(m, B.Bn.pow2(h, jf)), RD.Nat.lt(v, B.Bn.val(h, B.Bn.pow2(h, jf))), RD.Nat.lt(v, RD.Nat.pow2(j)), Cmp.lt(h, m, B.Bn.pow2(h, jf), om, Pow2.ok(h1, jf)),
                Equal.cong(Nat, Bool, z => RD.Nat.lt(v, z), B.Bn.val(h, B.Bn.pow2(h, jf)), RD.Nat.pow2(j), Vpw(h1, jf, j, Equal.sym(Nat, j, jf, FL.L.monus(e, emin)))))))
          +er = Equal.trans(Bool, RD.Dy.bige(emin, x), Bool.pick(Bool, RD.Nat.lt(emin, e), Bool.not(RD.Nat.lt(RD.Int.mag(D.Dy.num(x)), RD.Nat.pow2(RD.Nat.monus(e, emin)))), True{}), rhs,
            Equal.cong(Nat, Bool, d => Bool.pick(Bool, RD.Nat.lt(emin, d), Bool.not(RD.Nat.lt(RD.Int.mag(D.Dy.num(x)), RD.Nat.pow2(RD.Nat.monus(d, emin)))), True{}), D.Dy.den(x), e, ed),
            Equal.cong(Nat, Bool, z => Bool.pick(Bool, RD.Nat.lt(emin, e), Bool.not(RD.Nat.lt(z, RD.Nat.pow2(j))), True{}), RD.Int.mag(D.Dy.num(x)), v,
              Equal.trans(Nat, RD.Int.mag(D.Dy.num(x)), RD.Int.mag(sg), v, Equal.cong(I.Int, Nat, z => RD.Int.mag(z), D.Dy.num(x), sg, en2), Sg.mag(neg, v))))
          Equal.trans(Bool, B.Bd.bige(h, emin, B.Bd{neg, m, e}), rhs, RD.Dy.bige(emin, x), el, Equal.sym(Bool, RD.Dy.bige(emin, x), rhs, er))

def Fln.lk(+h1: Nat, +p: Nat, +k: Nat, b: Bool, +r: B.Bd, nf: NF(1n+h1, r), +om: {B.Bn.ok(1n+h1, B.Bd.m(r)) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.fl.n(1n+h1, p, k, b, r)) == RD.Dy.fl(p, k, b, B.Bd.val(1n+h1, r)) : D.Dy}:
  match b:
    case True{}:
      Rne.n.lk(h1, p, r, nf, om)
    case False{}:
      Rfix.n.lk(h1, k, r, nf, om)

# big binary formats round exactly as the spec
def Fl.lk(+h1: Nat, +p: Nat, +k: Nat, +emin: Nat, x: B.Bd, +ox: {B.Bd.ok(1n+h1, x) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.fl(1n+h1, p, k, emin, x)) == RD.Dy.fl(p, k, RD.Dy.bige(emin, B.Bd.val(1n+h1, x)), B.Bd.val(1n+h1, x)) : D.Dy}:
  match x:
    case B.Bd{+neg, +m, +e}:
      +h : Nat = 1n+h1
      +nx = B.Bd.norm.go(h, neg, e, m, B.Bn.even(m))
      +vx = D.Dy.of(e, B.Bd.sg(neg, B.Bn.val(h, m)))
      +ev = Norm.val(h, neg, e, m, B.Bn.even(m), {==})
      Equal.trans(D.Dy, B.Bd.val(h, B.Bd.fl.n(h, p, k, B.Bd.bige(h, emin, nx), nx)), B.Bd.val(h, B.Bd.fl.n(h, p, k, RD.Dy.bige(emin, B.Bd.val(h, nx)), nx)), RD.Dy.fl(p, k, RD.Dy.bige(emin, vx), vx),
        Equal.cong(Bool, D.Dy, z => B.Bd.val(h, B.Bd.fl.n(h, p, k, z, nx)), B.Bd.bige(h, emin, nx), RD.Dy.bige(emin, B.Bd.val(h, nx)),
          Bige.lk(h1, emin, nx, Norm.nf(h, neg, e, m, B.Bn.even(m), {==}), Norm.ok(h, neg, e, m, B.Bn.even(m), ox))),
        Equal.trans(D.Dy, B.Bd.val(h, B.Bd.fl.n(h, p, k, RD.Dy.bige(emin, B.Bd.val(h, nx)), nx)), RD.Dy.fl(p, k, RD.Dy.bige(emin, B.Bd.val(h, nx)), B.Bd.val(h, nx)), RD.Dy.fl(p, k, RD.Dy.bige(emin, vx), vx),
          Fln.lk(h1, p, k, RD.Dy.bige(emin, B.Bd.val(h, nx)), nx, Norm.nf(h, neg, e, m, B.Bn.even(m), {==}), Norm.ok(h, neg, e, m, B.Bn.even(m), ox)),
          Equal.cong(D.Dy, D.Dy, z => RD.Dy.fl(p, k, RD.Dy.bige(emin, z), z), B.Bd.val(h, nx), vx, ev)))

def F32.lk(+h1: Nat, +x: B.Bd, +ox: {B.Bd.ok(1n+h1, x) == True{} : Bool}) -> {B.Bd.val(1n+h1, B.Bd.f32(1n+h1, x)) == RD.Dy.f32(B.Bd.val(1n+h1, x)) : D.Dy}:
  Fl.lk(h1, 24n, 149n, 126n, x, ox)

def F64.lk(+h1: Nat, +x: B.Bd, +ox: {B.Bd.ok(1n+h1, x) == True{} : Bool}) -> {B.Bd.val(1n+h1, B.Bd.f64(1n+h1, x)) == RD.Dy.f64(B.Bd.val(1n+h1, x)) : D.Dy}:
  Fl.lk(h1, 53n, 1074n, 1022n, x, ox)

# Operations
# ----------

# big binary32 and binary64 products and sums are the modelled ones
# (proofs/round.bend, Fl.model), with no bound on the operands' size
def Mul32.lk(+h1: Nat, +x: B.Bd, +y: B.Bd, +ox: {B.Bd.ok(1n+h1, x) == True{} : Bool}, +oy: {B.Bd.ok(1n+h1, y) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.f32(1n+h1, B.Bd.mul(1n+h1, x, y))) == RD.Dy.f32(D.Dy.mul(B.Bd.val(1n+h1, x), B.Bd.val(1n+h1, y))) : D.Dy}:
  +h : Nat = 1n+h1
  Equal.trans(D.Dy, B.Bd.val(h, B.Bd.f32(h, B.Bd.mul(h, x, y))), RD.Dy.f32(B.Bd.val(h, B.Bd.mul(h, x, y))), RD.Dy.f32(D.Dy.mul(B.Bd.val(h, x), B.Bd.val(h, y))),
    F32.lk(h1, B.Bd.mul(h, x, y), Bd.mul.ok(h1, x, y, ox, oy)),
    Equal.cong(D.Dy, D.Dy, z => RD.Dy.f32(z), B.Bd.val(h, B.Bd.mul(h, x, y)), D.Dy.mul(B.Bd.val(h, x), B.Bd.val(h, y)), Bd.mul.lk(h1, x, y)))

def Add32.lk(+h1: Nat, +x: B.Bd, +y: B.Bd, +ox: {B.Bd.ok(1n+h1, x) == True{} : Bool}, +oy: {B.Bd.ok(1n+h1, y) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.f32(1n+h1, B.Bd.add(1n+h1, x, y))) == RD.Dy.f32(D.Dy.add(B.Bd.val(1n+h1, x), B.Bd.val(1n+h1, y))) : D.Dy}:
  +h : Nat = 1n+h1
  Equal.trans(D.Dy, B.Bd.val(h, B.Bd.f32(h, B.Bd.add(h, x, y))), RD.Dy.f32(B.Bd.val(h, B.Bd.add(h, x, y))), RD.Dy.f32(D.Dy.add(B.Bd.val(h, x), B.Bd.val(h, y))),
    F32.lk(h1, B.Bd.add(h, x, y), Bd.add.ok(h1, x, y, ox, oy)),
    Equal.cong(D.Dy, D.Dy, z => RD.Dy.f32(z), B.Bd.val(h, B.Bd.add(h, x, y)), D.Dy.add(B.Bd.val(h, x), B.Bd.val(h, y)), Bd.add.lk(h1, x, y, ox, oy)))

def Mul64.lk(+h1: Nat, +x: B.Bd, +y: B.Bd, +ox: {B.Bd.ok(1n+h1, x) == True{} : Bool}, +oy: {B.Bd.ok(1n+h1, y) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.f64(1n+h1, B.Bd.mul(1n+h1, x, y))) == RD.Dy.f64(D.Dy.mul(B.Bd.val(1n+h1, x), B.Bd.val(1n+h1, y))) : D.Dy}:
  +h : Nat = 1n+h1
  Equal.trans(D.Dy, B.Bd.val(h, B.Bd.f64(h, B.Bd.mul(h, x, y))), RD.Dy.f64(B.Bd.val(h, B.Bd.mul(h, x, y))), RD.Dy.f64(D.Dy.mul(B.Bd.val(h, x), B.Bd.val(h, y))),
    F64.lk(h1, B.Bd.mul(h, x, y), Bd.mul.ok(h1, x, y, ox, oy)),
    Equal.cong(D.Dy, D.Dy, z => RD.Dy.f64(z), B.Bd.val(h, B.Bd.mul(h, x, y)), D.Dy.mul(B.Bd.val(h, x), B.Bd.val(h, y)), Bd.mul.lk(h1, x, y)))

def Add64.lk(+h1: Nat, +x: B.Bd, +y: B.Bd, +ox: {B.Bd.ok(1n+h1, x) == True{} : Bool}, +oy: {B.Bd.ok(1n+h1, y) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.f64(1n+h1, B.Bd.add(1n+h1, x, y))) == RD.Dy.f64(D.Dy.add(B.Bd.val(1n+h1, x), B.Bd.val(1n+h1, y))) : D.Dy}:
  +h : Nat = 1n+h1
  Equal.trans(D.Dy, B.Bd.val(h, B.Bd.f64(h, B.Bd.add(h, x, y))), RD.Dy.f64(B.Bd.val(h, B.Bd.add(h, x, y))), RD.Dy.f64(D.Dy.add(B.Bd.val(h, x), B.Bd.val(h, y))),
    F64.lk(h1, B.Bd.add(h, x, y), Bd.add.ok(h1, x, y, ox, oy)),
    Equal.cong(D.Dy, D.Dy, z => RD.Dy.f64(z), B.Bd.val(h, B.Bd.add(h, x, y)), D.Dy.add(B.Bd.val(h, x), B.Bd.val(h, y)), Bd.add.lk(h1, x, y, ox, oy)))

# Exact dot products
# ------------------

def Bd.zero.val(+h: Nat) -> {B.Bd.val(h, B.Bd.zero()) == D.Dy.zero() : D.Dy}:
  {==}

def Dot.ok(+h1: Nat, xs: List<&2, B.Bd>, ys: List<&2, B.Bd>, +ox: {B.Bd.oks(1n+h1, xs) == True{} : Bool}, +oy: {B.Bd.oks(1n+h1, ys) == True{} : Bool})
  -> {B.Bd.ok(1n+h1, B.Bd.dot(1n+h1, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +xr:
      match ys:
        case Nil{}:
          {==}
        case +y <> +yr:
          +h : Nat = 1n+h1
          Bd.add.ok(h1, B.Bd.mul(h, x, y), B.Bd.dot(h, xr, yr),
            Bd.mul.ok(h1, x, y, R.Bool.and_t1(B.Bd.ok(h, x), B.Bd.oks(h, xr))(ox), R.Bool.and_t1(B.Bd.ok(h, y), B.Bd.oks(h, yr))(oy)),
            Dot.ok(h1, xr, yr, And.r(B.Bd.ok(h, x), B.Bd.oks(h, xr))(ox), And.r(B.Bd.ok(h, y), B.Bd.oks(h, yr))(oy)))

# the accumulator holds the exact dot product
def Dot.lk(+h1: Nat, xs: List<&2, B.Bd>, ys: List<&2, B.Bd>, +ox: {B.Bd.oks(1n+h1, xs) == True{} : Bool}, +oy: {B.Bd.oks(1n+h1, ys) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.dot(1n+h1, xs, ys)) == B.Dy.dotv(B.Bd.vals(1n+h1, xs), B.Bd.vals(1n+h1, ys)) : D.Dy}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +xr:
      match ys:
        case Nil{}:
          {==}
        case +y <> +yr:
          +h : Nat = 1n+h1
          +ox1 = R.Bool.and_t1(B.Bd.ok(h, x), B.Bd.oks(h, xr))(ox)
          +oy1 = R.Bool.and_t1(B.Bd.ok(h, y), B.Bd.oks(h, yr))(oy)
          +ox2 = And.r(B.Bd.ok(h, x), B.Bd.oks(h, xr))(ox)
          +oy2 = And.r(B.Bd.ok(h, y), B.Bd.oks(h, yr))(oy)
          +p = B.Bd.mul(h, x, y)
          +s = B.Bd.dot(h, xr, yr)
          Equal.trans(D.Dy, B.Bd.val(h, B.Bd.add(h, p, s)), D.Dy.add(B.Bd.val(h, p), B.Bd.val(h, s)), D.Dy.add(D.Dy.mul(B.Bd.val(h, x), B.Bd.val(h, y)), B.Dy.dotv(B.Bd.vals(h, xr), B.Bd.vals(h, yr))),
            Bd.add.lk(h1, p, s, Bd.mul.ok(h1, x, y, ox1, oy1), Dot.ok(h1, xr, yr, ox2, oy2)),
            Equal.trans(D.Dy, D.Dy.add(B.Bd.val(h, p), B.Bd.val(h, s)), D.Dy.add(D.Dy.mul(B.Bd.val(h, x), B.Bd.val(h, y)), B.Bd.val(h, s)), D.Dy.add(D.Dy.mul(B.Bd.val(h, x), B.Bd.val(h, y)), B.Dy.dotv(B.Bd.vals(h, xr), B.Bd.vals(h, yr))),
              Equal.cong(D.Dy, D.Dy, z => D.Dy.add(z, B.Bd.val(h, s)), B.Bd.val(h, p), D.Dy.mul(B.Bd.val(h, x), B.Bd.val(h, y)), Bd.mul.lk(h1, x, y)),
              Equal.cong(D.Dy, D.Dy, z => D.Dy.add(D.Dy.mul(B.Bd.val(h, x), B.Bd.val(h, y)), z), B.Bd.val(h, s), B.Dy.dotv(B.Bd.vals(h, xr), B.Bd.vals(h, yr)), Dot.lk(h1, xr, yr, ox2, oy2))))

# rounded once: the correctly rounded dot product, in binary32 and binary64
def Dot32.lk(+h1: Nat, +xs: List<&2, B.Bd>, +ys: List<&2, B.Bd>, +ox: {B.Bd.oks(1n+h1, xs) == True{} : Bool}, +oy: {B.Bd.oks(1n+h1, ys) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.f32(1n+h1, B.Bd.dot(1n+h1, xs, ys))) == RD.Dy.f32(B.Dy.dotv(B.Bd.vals(1n+h1, xs), B.Bd.vals(1n+h1, ys))) : D.Dy}:
  +h : Nat = 1n+h1
  Equal.trans(D.Dy, B.Bd.val(h, B.Bd.f32(h, B.Bd.dot(h, xs, ys))), RD.Dy.f32(B.Bd.val(h, B.Bd.dot(h, xs, ys))), RD.Dy.f32(B.Dy.dotv(B.Bd.vals(h, xs), B.Bd.vals(h, ys))),
    F32.lk(h1, B.Bd.dot(h, xs, ys), Dot.ok(h1, xs, ys, ox, oy)),
    Equal.cong(D.Dy, D.Dy, z => RD.Dy.f32(z), B.Bd.val(h, B.Bd.dot(h, xs, ys)), B.Dy.dotv(B.Bd.vals(h, xs), B.Bd.vals(h, ys)), Dot.lk(h1, xs, ys, ox, oy)))

def Dot64.lk(+h1: Nat, +xs: List<&2, B.Bd>, +ys: List<&2, B.Bd>, +ox: {B.Bd.oks(1n+h1, xs) == True{} : Bool}, +oy: {B.Bd.oks(1n+h1, ys) == True{} : Bool})
  -> {B.Bd.val(1n+h1, B.Bd.f64(1n+h1, B.Bd.dot(1n+h1, xs, ys))) == RD.Dy.f64(B.Dy.dotv(B.Bd.vals(1n+h1, xs), B.Bd.vals(1n+h1, ys))) : D.Dy}:
  +h : Nat = 1n+h1
  Equal.trans(D.Dy, B.Bd.val(h, B.Bd.f64(h, B.Bd.dot(h, xs, ys))), RD.Dy.f64(B.Bd.val(h, B.Bd.dot(h, xs, ys))), RD.Dy.f64(B.Dy.dotv(B.Bd.vals(h, xs), B.Bd.vals(h, ys))),
    F64.lk(h1, B.Bd.dot(h, xs, ys), Dot.ok(h1, xs, ys, ox, oy)),
    Equal.cong(D.Dy, D.Dy, z => RD.Dy.f64(z), B.Bd.val(h, B.Bd.dot(h, xs, ys)), B.Dy.dotv(B.Bd.vals(h, xs), B.Bd.vals(h, ys)), Dot.lk(h1, xs, ys, ox, oy)))
