# Q6: operator sugar on a user type: .^. calls T.xor, .&. calls T.and, * calls T.mul.
import Base

type Vec2 is Data:
  Vec2{x: U32, y: U32}

type Biv2 is Data:
  Biv2{e12: U32}

# the wedge, reached as (a .^. b : Vec2); the result type is free
def Vec2.xor(a: Vec2, b: Vec2) -> Biv2:
  match a b:
    case Vec2{+ax, +ay} Vec2{+bx, +by}:
      Biv2{(ax * by - ay * bx : U32)}

def Vec2.and(a: Vec2, b: Vec2) -> U32:
  match a b:
    case Vec2{ax, ay} Vec2{bx, by}:
      (ax * bx + ay * by : U32)

def main() -> Biv2 & U32:
  ((Vec2{1, 2} .^. Vec2{3, 4} : Vec2), (Vec2{1, 2} .&. Vec2{3, 4} : Vec2))
