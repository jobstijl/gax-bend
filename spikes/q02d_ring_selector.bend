# Q2d: the ring as ONE template: a top-level def dispatching on an op tag.
import Base

type Op is Data:
  Add{}
  Sub{}
  Mul{}
  Neg{}

def F32.ring(op: Op, a: F32, b: F32) -> F32:
  match op:
    case Add{}:
      F32.add(a, b)
    case Sub{}:
      F32.sub(a, b)
    case Mul{}:
      F32.mul(a, b)
    case Neg{}:
      F32.neg(a)

def dotS(~T: Data, ~R: Op -> T -> T -> T, +a0: T, +a1: T, +b0: T, +b1: T) -> T:
  R(Add{}, R(Mul{}, a0, b0), R(Mul{}, a1, b1))

def go(+t: F32) -> String:
  F32.show(dotS(~F32, ~F32.ring, t, 2.0, 3.0, t))

def main() -> IO(Unit):
  do IO<Unit>:
    n : Nat <- IO.now()
    IO.print(go(U32.to_f32(U32.and(U32.from_nat(n), 7))))
