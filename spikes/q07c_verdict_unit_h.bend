# Q7c: the unit law with point equations as ordinary +h arguments (equations are Data;
# a function-typed hypothesis is a Type, so it is affine and cannot be +).
import Base

law unit2h:
  for ~T: Data
  for ~e: T
  for ~op: T -> T -> T
  for +a: T
  for +h1: {op(op(a, e), e) == op(a, e) : T}
  for +h2: {op(a, e) == a : T}
  {op(op(a, e), e) == a : T}

def unit2h(T, e, op, a, h1, h2):
  Equal.trans(T, op(op(a, e), e), op(a, e), a, h1, h2)
