# Q2: one ~ ring record vs separate ~ ops; inputs from IO.now() so nothing folds.
import Base

type Ring<-T: Data> is Type:
  Ring{zero: T, one: T, add: T -> T -> T, mul: T -> T -> T, neg: T -> T}

def Ring.add(-T: Data, r: Ring<T>, a: T, b: T) -> T:
  match r:
    case Ring{z, o, add, mul, neg}:
      add(a, b)

def Ring.mul(-T: Data, r: Ring<T>, a: T, b: T) -> T:
  match r:
    case Ring{z, o, add, mul, neg}:
      mul(a, b)

def dotR(~T: Data, ~R: Ring<T>, +a0: T, +a1: T, +b0: T, +b1: T) -> T:
  Ring.add(T, R, Ring.mul(T, R, a0, b0), Ring.mul(T, R, a1, b1))

def dotS(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, +a0: T, +a1: T, +b0: T, +b1: T) -> T:
  add(mul(a0, b0), mul(a1, b1))

def F32R() -> Ring<F32>:
  Ring{0.0, 1.0, F32.add, F32.mul, F32.neg}

def F32L() -> Ring<F32>:
  Ring{0.0, 1.0, a => b => F32.add(a, b), a => b => F32.mul(a, b), a => F32.neg(a)}

def dotH(+a0: F32, +a1: F32, +b0: F32, +b1: F32) -> F32:
  F32.add(F32.mul(a0, b0), F32.mul(a1, b1))

def go(+t: F32) -> String:
  r1 = dotR(~F32, ~F32R(), t, 2.0, 3.0, t)
  r2 = dotR(~F32, ~F32L(), t, 2.0, 3.0, t)
  s1 = dotS(~F32, ~F32.add, ~F32.mul, t, 2.0, 3.0, t)
  s2 = dotS(~F32, ~(a => b => F32.add(a, b)), ~(a => b => F32.mul(a, b)), t, 2.0, 3.0, t)
  h = dotH(t, 2.0, 3.0, t)
  F32.show(r1) ++ " " ++ F32.show(r2) ++ " " ++ F32.show(s1) ++ " " ++ F32.show(s2) ++ " " ++ F32.show(h)

def main() -> IO(Unit):
  do IO<Unit>:
    n : Nat <- IO.now()
    IO.print(go(U32.to_f32(U32.and(U32.from_nat(n), 7))))
