# Cancellation in CGA3D at F32, measured (docs/numerics.md §2).
# p . q = -|x - y|^2 / 2 for embedded points: when x and y lie near each
# other far from the origin, the kernel subtracts terms of size |x|^2 to get
# one of size |x - y|^2. The proven bound (proofs/err.bend) is absolute,
# k u absev, so it must still hold, while the relative error grows like the
# condition number kappa = absev / |exact| (de Haan et al. 2024).
# Inputs are the F32 vectors themselves, so this is the kernel's own error;
# the embedding's rounding is not counted.
import Base
import ../num/df32.bend as D
import ../algebras/cga3d/kinds.bend as K
import ../algebras/cga3d/ops.bend as O

def mix(+x: U32) -> U32:
  +a = ((x .^. U32.shrn(x, 16n)) * 2246822507 : U32)
  +b = ((a .^. U32.shrn(a, 13n)) * 3266489909 : U32)
  (b .^. U32.shrn(b, 16n) : U32)

def rnd(+seed: U32, +i: U32) -> F32:
  (U32.to_f32(U32.shrn(mix((seed * 64 + i : U32)), 8n)) * 1.1920929e-7 - 1.0 : F32)

def up(+x: F32, +y: F32, +z: F32) -> K.Vector<F32>:
  K.Vector{x, y, z, 1.0, (0.5 * (x * x + y * y + z * z) : F32)}

def Vector.map(~A: Data, ~B: Data, ~f: A -> B, v: K.Vector<A>) -> K.Vector<B>:
  match v:
    case K.Vector{a, b, c, d, e}:
      K.Vector{f(a), f(b), f(c), f(d), f(e)}

def Scalar.s(-T: Data, x: K.Scalar<T>) -> T:
  match x:
    case K.Scalar{s}:
      s

def dfa(x: F32) -> D.DF:
  D.DF.abs(D.DF.of(x))

def Dep.add(a: Nat, b: Nat) -> Nat:
  1n+Nat.max(a, b)

def Dep.mul(a: Nat, b: Nat) -> Nat:
  1n+Nat.add(a, b)

def Dep.id(a: Nat) -> Nat:
  a

def k() -> Nat:
  Scalar.s(Nat, O.Vector.dot.Vector(~Nat, ~0n, ~Dep.add, ~Dep.mul, ~Dep.id, K.Vector{0n, 0n, 0n, 0n, 0n}, K.Vector{0n, 0n, 0n, 0n, 0n}))

type Acc is Data:
  Acc{bound: F32, rel: F32, kappa: F32}

def Acc.one(+b: F32, +r: F32, +c: F32, a: Acc) -> Acc:
  match a:
    case Acc{bound, rel, kappa}:
      Acc{F32.max(bound, b), F32.max(rel, r), F32.max(kappa, c)}

# x near the point (R, R/2, -R/3), y = x + an offset in [-1, 1)^3
def one(+r: F32, +s: U32, +kk: Nat, +a: Acc) -> Acc:
  +x1 = (r + rnd(s, 0) : F32)
  +x2 = (0.5 * r + rnd(s, 1) : F32)
  +x3 = (F32.neg(0.33333334) * r + rnd(s, 2) : F32)
  +p = up(x1, x2, x3)
  +q = up((x1 + rnd(s, 3) : F32), (x2 + rnd(s, 4) : F32), (x3 + rnd(s, 5) : F32))
  +f = Scalar.s(F32, O.Vector.dot.Vector(~F32, ~0.0, ~F32.add, ~F32.mul, ~F32.neg, p, q))
  +e = Scalar.s(D.DF, O.Vector.dot.Vector(~D.DF, ~D.DF.zero(), ~D.DF.add, ~D.DF.mul, ~D.DF.neg, Vector.map(~F32, ~D.DF, ~D.DF.of, p), Vector.map(~F32, ~D.DF, ~D.DF.of, q)))
  +ab = D.DF.to_f32(Scalar.s(D.DF, O.Vector.dot.Vector(~D.DF, ~D.DF.zero(), ~D.DF.add, ~D.DF.mul, ~D.DF.id, Vector.map(~F32, ~D.DF, ~dfa, p), Vector.map(~F32, ~D.DF, ~dfa, q))))
  +err = D.DF.to_f32(D.DF.abs(D.DF.sub(D.DF.of(f), e)))
  +ex = F32.abs(D.DF.to_f32(e))
  +bound = (U32.to_f32(U32.from_nat(kk)) * 5.9604645e-8 * ab : F32)
  Bool.pick(Acc, F32.is_lt(0.0, ex), Acc.one((err / bound : F32), (err / ex : F32), (ab / ex : F32), a), a)

def run(n: Nat, +r: F32, +s: U32, +kk: Nat, a: Acc) -> Acc:
  match n:
    case 0n:
      a
    case 1n+j:
      run(j, r, (s + 1 : U32), kk, one(r, s, kk, a))

def Acc.show(+r: F32, a: Acc) -> String:
  match a:
    case Acc{bound, rel, kappa}:
      "R = " ++ F32.show(r) ++ ": max err/bound " ++ F32.show(bound) ++ ", max relative error " ++ F32.show(rel) ++ ", max kappa " ++ F32.show(kappa)

def show(+r: F32, +kk: Nat) -> String:
  Acc.show(r, run(100000n, r, 1, kk, Acc{0.0, 0.0, 0.0}))

def main() -> IO(Unit):
  do IO<Unit>:
    +kk : Nat = k()
    IO.print("Vector.dot.Vector, k = " ++ Nat.show(kk))
    IO.print(show(1.0, kk))
    IO.print(show(100.0, kk))
    IO.print(show(10000.0, kk))
