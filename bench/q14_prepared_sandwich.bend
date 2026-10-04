# Q14: the prepared sandwich: the motor's matrix computed once
# (O.Motor.prepare.Point), then O.Motor.Point.apply per point (13
# multiplies), on the Q5 workload (2^26 points).
import Base
import ../algebras/pga3d/kinds.bend as K
import ../algebras/pga3d/ops.bend as O

def sandwich(+m: O.MotorPointMap<F32>, p: K.Point<F32>) -> K.Point<F32>:
  O.Motor.Point.apply(~F32, ~0.0, ~F32.add, ~F32.mul, ~F32.neg, m, p)

def gen(+i: U32) -> K.Point<F32>:
  K.Point{U32.to_f32((i .&. 1023 : U32)), U32.to_f32((U32.shrn(i, 10n) .&. 1023 : U32)), U32.to_f32(U32.shrn(i, 20n)), 1.0}

def Point.sum(f: K.Point<F32>) -> F32:
  match f:
    case K.Point{e032, e013, e021, e123}:
      (e032 + e013 + e021 + e123 : F32)

def leaf(n: Nat, +i: U32, acc: F32, +m: O.MotorPointMap<F32>) -> F32:
  match n:
    case 0n:
      acc
    case 1n+k:
      leaf(k, (i + 1 : U32), (acc + Point.sum(sandwich(m, gen(i))) : F32), m)

def tree(+d: Nat, +i: U32, +m: O.MotorPointMap<F32>) -> F32:
  match d:
    case 0n:
      leaf(4096n, U32.shln(i, 12n), 0.0, m)
    case 1n+k:
      a b = tree(k, (i * 2 : U32), m) tree(k, (i * 2 + 1 : U32), m)
      (a + b : F32)

def show(s: F32, +t0: Nat, t1: Nat) -> String:
  +b = s
  "sum " ++ F32.show(b) ++ "  " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms"

def run(+d: Nat, +k: F32) -> F32:
  tree(d, 0, O.Motor.prepare.Point(~F32, ~0.0, ~F32.add, ~F32.mul, ~F32.neg, K.Motor{0.8, 0.36, 0.48, (k * 0.0 : F32), 0.1, 0.2, 0.3, 0.05}))

def runb(+d: Nat, +k: F32) -> F32:
  tree!(d, 0, O.Motor.prepare.Point(~F32, ~0.0, ~F32.add, ~F32.mul, ~F32.neg, K.Motor{0.8, 0.36, 0.48, (k * 0.0 : F32), 0.1, 0.2, 0.3, 0.05}))

def main() -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +k : F32 = U32.to_f32(U32.and(U32.from_nat(t0), 1))
    s : F32 = run(14n, k)
    +t1 : Nat <- IO.now()
    IO.print("cpu   " ++ show(s, t0, t1))
    +t2 : Nat <- IO.now()
    sb : F32 = runb(14n, k)
    t3 : Nat <- IO.now()
    IO.print("bang  " ++ show(sb, t2, t3))
