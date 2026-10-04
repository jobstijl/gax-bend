# Q7a: --verdict on a law over ~ ops with ~ hypotheses (comm only: a model exists).
import Base

law comm3:
  for ~T: Data
  for ~op: T -> T -> T
  for ~comm: @x: T -> @y: T -> {op(x, y) == op(y, x) : T}
  for +a: T
  for +b: T
  for +c: T
  {op(op(a, b), c) == op(c, op(b, a)) : T}

def comm3(T, op, comm, a, b, c):
  %comm(b, a) : {op(_, c) == op(c, op(b, a)) : T}
  %comm(c, op(b, a)) : {_ == op(c, op(b, a)) : T}
  {==}
