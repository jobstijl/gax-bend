# Correctly rounded kernels (src/cr.bend, proofs/cr.bend): PGA3D's motor
# product on 500 random pairs, run three ways: in F32, exactly on big
# dyadics, and exactly then rounded once (CR). Checks:
# - converting the rounded value to F32 and back is exact (mismatches: 0);
# - the CR result is never farther from the exact one than the F32 result
#   (worse: 0), as correct rounding requires;
# - the control: how many fields F32 gets wrong, which must be nonzero.
# The fourth run is the kernel in double-F32 (num/df32.bend), rounded to
# F32 at the end: a compensated kernel. It differs from the correctly
# rounded result in 6 of 4000 fields, and in 2 of those it is farther from
# exact than plain F32: the last step rounds twice (to double-F32, then to
# F32). Correct rounding needs the exact accumulator.
import Base
import ../src/big.bend as B
import ../src/cr.bend as C
import ../num/df32.bend as DF
import ../algebras/pga3d/kinds.bend as K
import ../algebras/pga3d/ops.bend as O

def rnd(+x: Nat) -> Nat:
  Nat.mod(Nat.mul(x, 16807n), 2147483647n)

def scale(up: Nat, dn: Nat, +f: F32) -> F32:
  match up:
    case 0n:
      match dn:
        case 0n:
          f
        case 1n+j:
          scale(0n, j, F32.mul(f, 0.5))
    case 1n+j:
      scale(j, dn, F32.mul(f, 2.0))

# 1 to 24 significant bits, scaled by 2^t, t in [-30, 30]
def draw(+s: Nat) -> F32:
  +w : Nat = 1n+Nat.mod(s, 24n)
  +m : Nat = 1n+Nat.mod(rnd(s), Nat.sub(Nat.pow(2n, w), 1n))
  +t = Nat.mod(rnd(rnd(s)), 61n)
  +f = scale(Nat.sub(t, 30n), Nat.sub(30n, t), U32.to_f32(U32.from_nat(m)))
  Bool.pick(F32, Nat.is_eq(Nat.mod(rnd(rnd(rnd(s))), 2n), 0n), f, F32.neg(f))

def motor(+s: Nat) -> K.Motor<F32>:
  +s1 = rnd(s)
  +s2 = rnd(s1)
  +s3 = rnd(s2)
  +s4 = rnd(s3)
  +s5 = rnd(s4)
  +s6 = rnd(s5)
  +s7 = rnd(s6)
  K.Motor{draw(s), draw(s1), draw(s2), draw(s3), draw(s4), draw(s5), draw(s6), draw(s7)}

# exact comparisons on big dyadics
def zero(m: B.Bn) -> Bool:
  Bool.not(B.Bn.lt(B.BNil{}, m))

def same.n(x: B.Bd, y: B.Bd) -> Bool:
  match x y:
    case B.Bd{n1, +m1, e1} B.Bd{n2, +m2, e2}:
      Bool.and(Nat.is_eq(e1, e2), Bool.and(Bool.not(Bool.or(B.Bn.lt(m1, m2), B.Bn.lt(m2, m1))), Bool.or(zero(m1), Bool.not(Bool.xor(n1, n2)))))

def same(x: B.Bd, y: B.Bd) -> Bool:
  same.n(B.Bd.norm(C.CR.h(), x), B.Bd.norm(C.CR.h(), y))

def babs(x: B.Bd) -> B.Bd:
  match x:
    case B.Bd{n, m, e}:
      B.Bd{False{}, m, e}

# x < 0, strictly
def bneg.go(x: B.Bd) -> Bool:
  match x:
    case B.Bd{n, +m, e}:
      Bool.and(n, Bool.not(zero(m)))

def bneg(x: B.Bd) -> Bool:
  bneg.go(B.Bd.norm(C.CR.h(), x))

# |u - x| > |v - x|: u is strictly farther from x than v
def farther(+u: B.Bd, +v: B.Bd, +x: B.Bd) -> Bool:
  bneg(C.CR.add(babs(C.CR.add(v, B.Bd.neg(x))), B.Bd.neg(babs(C.CR.add(u, B.Bd.neg(x))))))

type Cnt is Data:
  Cnt{mis: Nat, worse: Nat, diff: Nat, n: Nat, dworse: Nat, ddiff: Nat}

def neq(+f: F32, +g: F32) -> Nat:
  Bool.pick(Nat, Nat.is_eq(U32.to_nat(F32.bits(f)), U32.to_nat(F32.bits(g))), 0n, 1n)

def field(+f: F32, +g: F32, +x: B.Bd, c: Cnt) -> Cnt:
  match c:
    case Cnt{a, w, d, n, dw, dd}:
      +r = C.CR.f32(x)
      +cr = C.CR.to_f32(r)
      Cnt{Nat.add(a, Bool.pick(Nat, same(C.CR.of(cr), r), 0n, 1n)),
          Nat.add(w, Bool.pick(Nat, farther(C.CR.of(cr), C.CR.of(f), x), 1n, 0n)),
          Nat.add(d, neq(f, cr)),
          1n+n,
          Nat.add(dw, Bool.pick(Nat, farther(C.CR.of(g), C.CR.of(f), x), 1n, 0n)),
          Nat.add(dd, neq(g, cr))}

def fields(fs: List<&2, F32>, gs: List<&2, F32>, xs: List<&2, B.Bd>, c: Cnt) -> Cnt:
  match fs gs xs:
    case f <> ft g <> gt x <> xt:
      fields(ft, gt, xt, field(f, g, x, c))
    case _ _ _:
      c

def step(+s: Nat, c: Cnt) -> Cnt:
  +a = motor(s)
  +b = motor(rnd(rnd(rnd(rnd(rnd(rnd(rnd(rnd(s)))))))))
  +naive = O.Motor.gp.Motor(~F32, ~0.0, ~F32.add, ~F32.mul, ~F32.neg, a, b)
  +exact = O.Motor.gp.Motor(~B.Bd, ~B.Bd.zero(), ~C.CR.add, ~C.CR.mul, ~B.Bd.neg, K.Motor.map(~F32, ~B.Bd, ~(x => C.CR.of(x)), a), K.Motor.map(~F32, ~B.Bd, ~(x => C.CR.of(x)), b))
  +dw = O.Motor.gp.Motor(~DF.DF, ~DF.DF.zero(), ~DF.DF.add, ~DF.DF.mul, ~DF.DF.neg, K.Motor.map(~F32, ~DF.DF, ~DF.DF.of, a), K.Motor.map(~F32, ~DF.DF, ~DF.DF.of, b))
  fields(K.Motor.fields(F32, naive), K.Motor.fields(F32, K.Motor.map(~DF.DF, ~F32, ~DF.DF.to_f32, dw)), K.Motor.fields(B.Bd, exact), c)

def run(n: Nat, +s: Nat, c: Cnt) -> Cnt:
  match n:
    case 0n:
      c
    case 1n+k:
      run(k, rnd(rnd(rnd(s))), step(s, c))

def show(c: Cnt) -> String:
  match c:
    case Cnt{a, w, d, n, dw, dd}:
      Nat.show(n) ++ " fields: round-trip mismatches " ++ Nat.show(a) ++ ", CR farther than F32 " ++ Nat.show(w) ++ "; control, F32 differs from CR " ++ Nat.show(d) ++ "; double-F32 farther than F32 " ++ Nat.show(dw) ++ ", differs from CR " ++ Nat.show(dd)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("500 motor products, " ++ show(run(500n, 7n, Cnt{0n, 0n, 0n, 0n, 0n, 0n})))
#|500 motor products, 4000 fields: round-trip mismatches 0, CR farther than F32 0; control, F32 differs from CR 699; double-F32 farther than F32 2, differs from CR 6
