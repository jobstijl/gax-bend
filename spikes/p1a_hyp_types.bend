# P1a: ring hypotheses as named type-level defs, used through ~ parameters.
import Base

def Assoc(T: Data, op: T -> T -> T) -> Type:
  @a: T -> @b: T -> @c: T -> {op(op(a, b), c) == op(a, op(b, c)) : T}

def Comm(T: Data, op: T -> T -> T) -> Type:
  @a: T -> @b: T -> {op(a, b) == op(b, a) : T}

law reassoc:
  for ~T: Data
  for ~op: T -> T -> T
  for ~assoc: Assoc(T, op)
  for ~comm: Comm(T, op)
  for +a: T
  for +b: T
  for +c: T
  {op(op(a, b), c) == op(c, op(b, a)) : T}

def reassoc(T, op, assoc, comm, a, b, c):
  Equal.trans(T, op(op(a, b), c), op(c, op(a, b)), op(c, op(b, a)), comm(op(a, b), c),
    Equal.cong(T, T, w => op(c, w), op(a, b), op(b, a), comm(a, b)))

law use:
  {U32.add(U32.add(1, 2), 3) == U32.add(3, U32.add(2, 1)) : U32}

def use():
  reassoc(~U32, ~U32.add, ~u32_assoc, ~U32.add_comm, 1, 2, 3)

def u32_assoc(a: U32, b: U32, c: U32) -> {U32.add(U32.add(a, b), c) == U32.add(a, U32.add(b, c)) : U32}:
  ?TODO
