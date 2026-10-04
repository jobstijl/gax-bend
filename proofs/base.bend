# Proof toolkit: congruence through constructors and two-argument
# functions, and the Bool algebra of sign flags. Every lemma is closed: it
# assumes nothing.

import Base
import ../src/spec.bend as S

# Congruence
# ----------

def Eq.cong2(-A: Type, -B: Type, -C: Type, -f: A -> B -> C, -a: A, -a2: A, -b: B, -b2: B,
  ea: {a == a2 : A}, eb: {b == b2 : B}) -> {f(a, b) == f(a2, b2) : C}:
  %ea : {f(a, b) == f(_, b2) : C}
  %eb : {f(a, b) == f(a, _) : C}
  {==}

def Eq.cong3(-A: Type, -B: Type, -C: Type, -D: Type, -f: A -> B -> C -> D, -a: A, -a2: A, -b: B, -b2: B,
  -c: C, -c2: C, ea: {a == a2 : A}, eb: {b == b2 : B}, ec: {c == c2 : C}) -> {f(a, b, c) == f(a2, b2, c2) : D}:
  %ea : {f(a, b, c) == f(_, b2, c2) : D}
  %eb : {f(a, b, c) == f(a, _, c2) : D}
  %ec : {f(a, b, c) == f(a, b, _) : D}
  {==}

def Node.cong2(-A: Data, -a1: A, -b1: A, -a2: A, -b2: A, e1: {a1 == b1 : A}, e2: {a2 == b2 : A})
  -> {S.N{a1, a2} == S.N{b1, b2} : S.Node<A>}:
  %e1 : {S.N{a1, a2} == S.N{_, b2} : S.Node<A>}
  %e2 : {S.N{a1, a2} == S.N{a1, _} : S.Node<A>}
  {==}

def Leaf.cong(-T: Data, -a: T, -b: T, e: {a == b : T}) -> {S.L{a} == S.L{b} : S.Leaf<T>}:
  %e : {S.L{a} == S.L{_} : S.Leaf<T>}
  {==}

# a == c and b == c give a == b
def Eq.join(-A: Type, -a: A, -b: A, -c: A, ac: {a == c : A}, bc: {b == c : A}) -> {a == b : A}:
  Equal.trans(A, a, c, b, ac, Equal.sym(A, b, c, bc))

# Bool flags
# ----------

def Bool.not_not(b: Bool) -> {Bool.not(Bool.not(b)) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Bool.xor_f(b: Bool) -> {Bool.xor(b, False{}) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Bool.xor_t(b: Bool) -> {Bool.xor(b, True{}) == Bool.not(b) : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Bool.xor_self(b: Bool) -> {Bool.xor(b, b) == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Bool.xor_comm(a: Bool, b: Bool) -> {Bool.xor(a, b) == Bool.xor(b, a) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Bool.xor_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.xor(Bool.xor(a, b), c) == Bool.xor(a, Bool.xor(b, c)) : Bool}:
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def Bool.xor_not_l(a: Bool, b: Bool) -> {Bool.xor(Bool.not(a), b) == Bool.not(Bool.xor(a, b)) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Bool.xor_not_r(a: Bool, b: Bool) -> {Bool.xor(a, Bool.not(b)) == Bool.not(Bool.xor(a, b)) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# the middle two of four swap: (a + b) + (c + d) = (a + c) + (b + d)
def Bool.xor_swap4(a: Bool, b: Bool, c: Bool, d: Bool)
  -> {Bool.xor(Bool.xor(a, b), Bool.xor(c, d)) == Bool.xor(Bool.xor(a, c), Bool.xor(b, d)) : Bool}:
  match a b c d:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

# Refutation
# ----------

def Bool.disc(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

def Bool.tf.empty(e: {True{} == False{} : Bool}) -> Empty:
  %e : Bool.disc(_)
  Unit{}

# True is not False: anything follows
def Bool.tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  Empty.absurd(A, Bool.tf.empty(e))
