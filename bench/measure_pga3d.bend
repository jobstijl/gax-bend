# Rounding error of PGA3D kernels at F32, measured (docs/numerics.md §2).
# Each kernel runs four times, as the same generic code:
#   at F32                          the result under test;
#   at double-F32 (num/df32.bend)   the reference, ~2^-48 relative;
#   at double-F32 on |inputs| with neg the identity: absev, the bound's size;
#   at the depth semiring on Nat    k, the roundings on the worst path.
# The theorem (proofs/err.bend) says err <= h(k) absev ~ k u absev, given
# that F32 rounds by the standard model (u = 2^-24). The report gives the
# worst and mean err / bound (the hypothesis predicts <= 1) and the worst
# err / (u absev), the growth seen against the worst case k.
import Base
import ../num/df32.bend as D
import ../algebras/pga3d/kinds.bend as K
import ../algebras/pga3d/ops.bend as O

# Random inputs in [-1, 1)
def mix(+x: U32) -> U32:
  +a = ((x .^. U32.shrn(x, 16n)) * 2246822507 : U32)
  +b = ((a .^. U32.shrn(a, 13n)) * 3266489909 : U32)
  (b .^. U32.shrn(b, 16n) : U32)

def rnd(+seed: U32, +i: U32) -> F32:
  (U32.to_f32(U32.shrn(mix((seed * 64 + i : U32)), 8n)) * 1.1920929e-7 - 1.0 : F32)

def motor(+s: U32, +o: U32) -> K.Motor<F32>:
  K.Motor{rnd(s, o), rnd(s, (o + 1 : U32)), rnd(s, (o + 2 : U32)), rnd(s, (o + 3 : U32)), rnd(s, (o + 4 : U32)), rnd(s, (o + 5 : U32)), rnd(s, (o + 6 : U32)), rnd(s, (o + 7 : U32))}

def point(+s: U32, +o: U32) -> K.Point<F32>:
  K.Point{rnd(s, o), rnd(s, (o + 1 : U32)), rnd(s, (o + 2 : U32)), rnd(s, (o + 3 : U32))}

def line(+s: U32, +o: U32) -> K.Line<F32>:
  K.Line{rnd(s, o), rnd(s, (o + 1 : U32)), rnd(s, (o + 2 : U32)), rnd(s, (o + 3 : U32)), rnd(s, (o + 4 : U32)), rnd(s, (o + 5 : U32))}

# Instantiations
def dfa(x: F32) -> D.DF:
  D.DF.abs(D.DF.of(x))

def Dep.add(a: Nat, b: Nat) -> Nat:
  1n+Nat.max(a, b)

def Dep.mul(a: Nat, b: Nat) -> Nat:
  1n+Nat.add(a, b)

def Dep.id(a: Nat) -> Nat:
  a

def Motor.map(~A: Data, ~B: Data, ~f: A -> B, m: K.Motor<A>) -> K.Motor<B>:
  match m:
    case K.Motor{a, b, c, d, e, g, h, i}:
      K.Motor{f(a), f(b), f(c), f(d), f(e), f(g), f(h), f(i)}

def Point.map(~A: Data, ~B: Data, ~f: A -> B, p: K.Point<A>) -> K.Point<B>:
  match p:
    case K.Point{a, b, c, d}:
      K.Point{f(a), f(b), f(c), f(d)}

def Line.map(~A: Data, ~B: Data, ~f: A -> B, p: K.Line<A>) -> K.Line<B>:
  match p:
    case K.Line{a, b, c, d, e, g}:
      K.Line{f(a), f(b), f(c), f(d), f(e), f(g)}

def Motor.l(-T: Data, m: K.Motor<T>) -> List<&2, T>:
  match m:
    case K.Motor{a, b, c, d, e, g, h, i}:
      [a, b, c, d, e, g, h, i]

def Point.l(-T: Data, p: K.Point<T>) -> List<&2, T>:
  match p:
    case K.Point{a, b, c, d}:
      [a, b, c, d]

def Line.l(-T: Data, p: K.Line<T>) -> List<&2, T>:
  match p:
    case K.Line{a, b, c, d, e, g}:
      [a, b, c, d, e, g]

# Accumulating the report
type Acc is Data:
  Acc{mx: F32, sum: F32, n: F32, grow: F32}

def Acc.one(+r: F32, +g: F32, a: Acc) -> Acc:
  match a:
    case Acc{mx, sum, n, grow}:
      Acc{F32.max(mx, r), (sum + r : F32), (n + 1.0 : F32), F32.max(grow, g)}

# one field: err = |f - e|, unit = u absev, bound = k unit
def Acc.field(+f: F32, e: D.DF, ab: D.DF, +k: Nat, +a: Acc) -> Acc:
  +err = D.DF.to_f32(D.DF.abs(D.DF.sub(D.DF.of(f), e)))
  +unit = (5.9604645e-8 * D.DF.to_f32(ab) : F32)
  +bound = (U32.to_f32(U32.from_nat(k)) * unit : F32)
  Bool.pick(Acc, F32.is_lt(0.0, bound), Acc.one((err / bound : F32), (err / unit : F32), a), a)

def Acc.fields(fs: List<&2, F32>, es: List<&2, D.DF>, as: List<&2, D.DF>, ks: List<&2, Nat>, a: Acc) -> Acc:
  match fs es as ks:
    case f <> ft e <> et b <> bt k <> kt:
      Acc.fields(ft, et, bt, kt, Acc.field(f, e, b, k, a))
    case _ _ _ _:
      a

def Acc.show(+name: String, a: Acc, kmax: Nat) -> String:
  match a:
    case Acc{mx, sum, +n, grow}:
      name ++ ": max err/bound " ++ F32.show(mx) ++ ", mean " ++ F32.show((sum / n : F32)) ++ ", max err/(u absev) " ++ F32.show(grow) ++ " (k up to " ++ Nat.show(kmax) ++ ")"

def Nat.maxl(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Nat.max(x, Nat.maxl(t))

# Kernels
def mtp.k() -> List<&2, Nat>:
  Point.l(Nat, O.Motor.transform.Point(~Nat, ~0n, ~Dep.add, ~Dep.mul, ~Dep.id, K.Motor{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}, K.Point{0n, 0n, 0n, 0n}))

def mtp.one(+s: U32, +ks: List<&2, Nat>, a: Acc) -> Acc:
  +m = motor(s, 0)
  +p = point(s, 8)
  Acc.fields(Point.l(F32, O.Motor.transform.Point(~F32, ~0.0, ~F32.add, ~F32.mul, ~F32.neg, m, p)),
    Point.l(D.DF, O.Motor.transform.Point(~D.DF, ~D.DF.zero(), ~D.DF.add, ~D.DF.mul, ~D.DF.neg, Motor.map(~F32, ~D.DF, ~D.DF.of, m), Point.map(~F32, ~D.DF, ~D.DF.of, p))),
    Point.l(D.DF, O.Motor.transform.Point(~D.DF, ~D.DF.zero(), ~D.DF.add, ~D.DF.mul, ~D.DF.id, Motor.map(~F32, ~D.DF, ~dfa, m), Point.map(~F32, ~D.DF, ~dfa, p))),
    ks, a)

def mm.k() -> List<&2, Nat>:
  Motor.l(Nat, O.Motor.gp.Motor(~Nat, ~0n, ~Dep.add, ~Dep.mul, ~Dep.id, K.Motor{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}, K.Motor{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}))

def mm.one(+s: U32, +ks: List<&2, Nat>, a: Acc) -> Acc:
  +x = motor(s, 0)
  +y = motor(s, 8)
  Acc.fields(Motor.l(F32, O.Motor.gp.Motor(~F32, ~0.0, ~F32.add, ~F32.mul, ~F32.neg, x, y)),
    Motor.l(D.DF, O.Motor.gp.Motor(~D.DF, ~D.DF.zero(), ~D.DF.add, ~D.DF.mul, ~D.DF.neg, Motor.map(~F32, ~D.DF, ~D.DF.of, x), Motor.map(~F32, ~D.DF, ~D.DF.of, y))),
    Motor.l(D.DF, O.Motor.gp.Motor(~D.DF, ~D.DF.zero(), ~D.DF.add, ~D.DF.mul, ~D.DF.id, Motor.map(~F32, ~D.DF, ~dfa, x), Motor.map(~F32, ~D.DF, ~dfa, y))),
    ks, a)

def pvp.k() -> List<&2, Nat>:
  Line.l(Nat, O.Point.vee.Point(~Nat, ~0n, ~Dep.add, ~Dep.mul, ~Dep.id, K.Point{0n, 0n, 0n, 0n}, K.Point{0n, 0n, 0n, 0n}))

def pvp.one(+s: U32, +ks: List<&2, Nat>, a: Acc) -> Acc:
  +x = point(s, 0)
  +y = point(s, 8)
  Acc.fields(Line.l(F32, O.Point.vee.Point(~F32, ~0.0, ~F32.add, ~F32.mul, ~F32.neg, x, y)),
    Line.l(D.DF, O.Point.vee.Point(~D.DF, ~D.DF.zero(), ~D.DF.add, ~D.DF.mul, ~D.DF.neg, Point.map(~F32, ~D.DF, ~D.DF.of, x), Point.map(~F32, ~D.DF, ~D.DF.of, y))),
    Line.l(D.DF, O.Point.vee.Point(~D.DF, ~D.DF.zero(), ~D.DF.add, ~D.DF.mul, ~D.DF.id, Point.map(~F32, ~D.DF, ~dfa, x), Point.map(~F32, ~D.DF, ~dfa, y))),
    ks, a)

def run.mtp(n: Nat, +s: U32, +ks: List<&2, Nat>, a: Acc) -> Acc:
  match n:
    case 0n:
      a
    case 1n+j:
      run.mtp(j, (s + 1 : U32), ks, mtp.one(s, ks, a))

def run.mm(n: Nat, +s: U32, +ks: List<&2, Nat>, a: Acc) -> Acc:
  match n:
    case 0n:
      a
    case 1n+j:
      run.mm(j, (s + 1 : U32), ks, mm.one(s, ks, a))

def run.pvp(n: Nat, +s: U32, +ks: List<&2, Nat>, a: Acc) -> Acc:
  match n:
    case 0n:
      a
    case 1n+j:
      run.pvp(j, (s + 1 : U32), ks, pvp.one(s, ks, a))

def acc0() -> Acc:
  Acc{0.0, 0.0, 0.0, 0.0}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Acc.show("Motor.transform.Point", run.mtp(100000n, 1, mtp.k(), acc0()), Nat.maxl(mtp.k())))
    IO.print(Acc.show("Motor.gp.Motor", run.mm(100000n, 1, mm.k(), acc0()), Nat.maxl(mm.k())))
    IO.print(Acc.show("Point.vee.Point", run.pvp(100000n, 1, pvp.k(), acc0()), Nat.maxl(pvp.k())))
