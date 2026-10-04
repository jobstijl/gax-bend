# Q2c: EXPECTED TO FAIL. A ~R record cannot be destructured in a template body,
# even annotated ("a match cannot scrutinize a computed value").
import Base

type Ring<-T: Data> is Type:
  Ring{zero: T, one: T, add: T -> T -> T, mul: T -> T -> T, neg: T -> T}

def Ring.add(~T: Data, ~r: Ring<T>, a: T, b: T) -> T:
  Ring{z, o, add, mul, neg} = {r : Ring<T>}
  add(a, b)

def Ring.mul(~T: Data, ~r: Ring<T>, a: T, b: T) -> T:
  Ring{z, o, add, mul, neg} = {r : Ring<T>}
  mul(a, b)

def dotR(~T: Data, ~R: Ring<T>, +a0: T, +a1: T, +b0: T, +b1: T) -> T:
  Ring.add(~T, ~R, Ring.mul(~T, ~R, a0, b0), Ring.mul(~T, ~R, a1, b1))

def F32R() -> Ring<F32>:
  Ring{0.0, 1.0, F32.add, F32.mul, F32.neg}

def go(+t: F32) -> String:
  r1 = dotR(~F32, ~F32R(), t, 2.0, 3.0, t)
  r2 = dotR(~F32, ~Ring{0.0, 1.0, F32.add, F32.mul, F32.neg}, t, 2.0, 3.0, t)
  F32.show(r1) ++ " " ++ F32.show(r2)

def main() -> IO(Unit):
  do IO<Unit>:
    n : Nat <- IO.now()
    IO.print(go(U32.to_f32(U32.and(U32.from_nat(n), 7))))
