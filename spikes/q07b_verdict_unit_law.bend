# Q7b: --verdict on a law whose ~ hypotheses include a unit law op(x, e) == x.
import Base

law unit2:
  for ~T: Data
  for ~e: T
  for ~op: T -> T -> T
  for ~unit: @x: T -> {op(x, e) == x : T}
  for +a: T
  {op(op(a, e), e) == a : T}

def unit2(T, e, op, unit, a):
  Equal.trans(T, op(op(a, e), e), op(a, e), a, unit(op(a, e)), unit(a))
