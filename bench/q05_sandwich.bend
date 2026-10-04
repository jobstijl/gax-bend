# Q5: gax unit_motor_sandwich_point (33 multiplies) as a flat F32 record
# kernel, over a balanced fork tree of 2^D leaves, each a flat loop of 2^12
# points. Same arithmetic and sum order as q05_sandwich.c.
import Base

type Motor is Data:
  Motor{c0x: F32, c0y: F32, c0z: F32, c0w: F32, c1x: F32, c1y: F32, c1z: F32, c1w: F32}

type Point is Data:
  Point{x: F32, y: F32, z: F32, w: F32}

def sandwich(v: Motor, p: Point) -> Point:
  match v p:
    case Motor{+c0x, +c0y, +c0z, +c0w, +c1x, +c1y, +c1z, +c1w} Point{+px, +py, +pz, +pw}:
      +t2 = (c1z * pw : F32)
      +t3 = (c0y * py + t2 : F32)
      +t4 = (F32.neg(c0z) * px + t3 : F32)
      +t5 = (c0y * pz : F32)
      +t8 = (F32.neg(c0w) * px + t5 : F32)
      +t9 = (F32.neg(c1y) * pw + t8 : F32)
      +t12 = (c1x * pw : F32)
      +t13 = (c0z * pz + t12 : F32)
      +t14 = (F32.neg(c0w) * py + t13 : F32)
      +t15 = (c1w * pw : F32)
      +t17 = (c0y * t15 : F32)
      +t19 = (c0w * t9 : F32)
      +t22 = (c0z * t15 : F32)
      +t23 = (c0w * t14 : F32)
      +t25 = (c0y * t9 : F32)
      +t27 = (c0w * t15 : F32)
      +t28 = (c0z * t4 + t19 : F32)
      +t29 = (c0x * t14 + t17 : F32)
      +t30 = (t28 - t29 : F32)
      +t33 = (c0y * c0y : F32)
      +t35 = (c0w * c0w : F32)
      +t36 = (c0x * c0x + t33 : F32)
      +t37 = (c0z * c0z + t35 : F32)
      +t38 = (t36 + t37 : F32)
      +t39 = (px * t38 : F32)
      +t40 = (t30 * 2.0 + t39 : F32)
      +t41 = (c0x * t9 + t23 : F32)
      +t42 = (c0y * t4 + t22 : F32)
      +t43 = (t41 - t42 : F32)
      +t45 = (py * t38 : F32)
      +t46 = (t43 * 2.0 + t45 : F32)
      +t47 = (c0x * t4 + t25 : F32)
      +t48 = (c0z * t14 + t27 : F32)
      +t49 = (t47 + t48 : F32)
      +t51 = (pz * t38 : F32)
      +t52 = (F32.neg(t49) * 2.0 + t51 : F32)
      +t53 = (pw * t38 : F32)
      Point{t40, t46, t52, t53}

def gen(+i: U32) -> Point:
  Point{U32.to_f32((i .&. 1023 : U32)), U32.to_f32((U32.shrn(i, 10n) .&. 1023 : U32)), U32.to_f32(U32.shrn(i, 20n)), 1.0}

def Point.sum(p: Point) -> F32:
  match p:
    case Point{x, y, z, w}:
      (x + y + z + w : F32)

def leaf(n: Nat, +i: U32, acc: F32, +m: Motor) -> F32:
  match n:
    case 0n:
      acc
    case 1n+k:
      leaf(k, (i + 1 : U32), (acc + Point.sum(sandwich(m, gen(i))) : F32), m)

def tree(+d: Nat, +i: U32, +m: Motor) -> F32:
  match d:
    case 0n:
      leaf(4096n, U32.shln(i, 12n), 0.0, m)
    case 1n+k:
      a b = tree(k, (i * 2 : U32), m) tree(k, (i * 2 + 1 : U32), m)
      (a + b : F32)

def show(s: F32, +t0: Nat, t1: Nat) -> String:
  +b = s
  "sum " ++ F32.show(b) ++ " bits " ++ U32.show(F32.bits(b)) ++ "  " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms"

def run(+d: Nat, +k: F32, +t0: Nat) -> F32:
  tree(d, 0, Motor{0.8, 0.36, 0.48, (k * 0.0 : F32), 0.1, 0.2, 0.3, 0.05})

def runb(+d: Nat, +k: F32, +t0: Nat) -> F32:
  tree!(d, 0, Motor{0.8, 0.36, 0.48, (k * 0.0 : F32), 0.1, 0.2, 0.3, 0.05})

def main() -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +k : F32 = U32.to_f32(U32.and(U32.from_nat(t0), 1))
    s : F32 = run(14n, k, t0)
    t1 : Nat <- IO.now()
    IO.print("cpu   " ++ show(s, t0, t1))
    +t2 : Nat <- IO.now()
    sb : F32 = runb(14n, k, t2)
    t3 : Nat <- IO.now()
    IO.print("bang  " ++ show(sb, t2, t3))
