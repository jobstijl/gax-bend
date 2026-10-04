# The PGA3D API at F32 (f32-prop): motions and their numerics.
# Checks, each printed as coordinates rounded to 1e-4 or as a tolerance test:
# - a quarter turn about the x axis (the join of the origin and (1, 0, 0))
#   moves (0, 1, 0) to (0, 0, 1): right-handed;
# - the translation by (1, 2, 3) moves the origin to (1, 2, 3);
# - the motion between two points carries the first to the second;
# - the motion between two lines carries the first to the second;
# - log(exp(B)) = B within 1e-5 for a screw B (rotation with translation);
# - a scaled motor normalizes to m ~m = 1 within 1e-6;
# - sqrt(m) sqrt(m) = m within 1e-5;
# - exp(B) = exp(B/2)² within 1e-6 on both sides of the series boundary
#   |B²| = 1/4 (half-angles 0.4999 and 0.5001) and at a half-angle of 1e-4;
# - log(exp(B)) = B within 1e-7 at a half-angle of 1e-4;
# - log of a pure translation is exact.
import Base
import ../api/pga3d.bend as P
import ../api/normed.bend as U
import ../algebras/pga3d/kinds.bend as K
import ../algebras/pga3d/f32.bend as G

def r4(x: F32) -> String:
  F32.show((F32.round((x * 10000.0 : F32)) / 10000.0 : F32))

def Point.show(p: K.Point<F32>) -> String:
  match p:
    case K.Point{x, y, z, +w}:
      "(" ++ r4((x / w : F32)) ++ ", " ++ r4((y / w : F32)) ++ ", " ++ r4((z / w : F32)) ++ ")"

def M(u: U.Normed<K.Motor<F32>>) -> K.Motor<F32>:
  U.Normed.get(K.Motor<F32>, u)

def Line.err(a: K.Line<F32>, b: K.Line<F32>) -> F32:
  match a b:
    case K.Line{a1, a2, a3, a4, a5, a6} K.Line{b1, b2, b3, b4, b5, b6}:
      F32.max(F32.max(F32.max(F32.abs((a1 - b1 : F32)), F32.abs((a2 - b2 : F32))), F32.max(F32.abs((a3 - b3 : F32)), F32.abs((a4 - b4 : F32)))),
        F32.max(F32.abs((a5 - b5 : F32)), F32.abs((a6 - b6 : F32))))

def Motor.err(a: K.Motor<F32>, b: K.Motor<F32>) -> F32:
  match a b:
    case K.Motor{a0, a1, a2, a3, a4, a5, a6, a7} K.Motor{b0, b1, b2, b3, b4, b5, b6, b7}:
      F32.max(F32.max(F32.max(F32.abs((a0 - b0 : F32)), F32.abs((a1 - b1 : F32))), F32.max(F32.abs((a2 - b2 : F32)), F32.abs((a3 - b3 : F32)))),
        F32.max(F32.max(F32.abs((a4 - b4 : F32)), F32.abs((a5 - b5 : F32))), F32.max(F32.abs((a6 - b6 : F32)), F32.abs((a7 - b7 : F32)))))

def Study.err(sp: F32 & F32) -> F32:
  match sp:
    case (s, p):
      F32.max(F32.abs((s - 1.0 : F32)), F32.abs(p))

def screw() -> K.Line<F32>:
  K.Line{0.3, F32.neg(0.4), 0.5, 0.7, 0.2, F32.neg(0.9)}

def x_axis() -> K.Line<F32>:
  G.Point.vee.Point(P.Point.xyz(0.0, 0.0, 0.0), P.Point.xyz(1.0, 0.0, 0.0))

# the screw direction scaled to half-angle t (|u| = t), with a moment
def screw.at(+t: F32) -> K.Line<F32>:
  G.Scalar.gp.Line(K.Scalar{(t / 0.70710677 : F32)}, K.Line{0.3, F32.neg(0.4), 0.5, 0.7, 0.2, F32.neg(0.9)})

def halving.err(+b: K.Line<F32>) -> F32:
  +h = M(P.Line.exp(G.Scalar.gp.Line(K.Scalar{0.5}, b)))
  Motor.err(G.Motor.gp.Motor(h, h), M(P.Line.exp(b)))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Point.show(G.Motor.transform.Point(M(P.Motor.rotation(x_axis(), (F32.pi() * 0.5 : F32))), P.Point.xyz(0.0, 1.0, 0.0))))
    IO.print(Point.show(G.Motor.transform.Point(M(P.Motor.translation(1.0, 2.0, 3.0)), P.Point.xyz(0.0, 0.0, 0.0))))
    IO.print(Point.show(G.Motor.transform.Point(M(P.Motor.between.points(P.Point.xyz(1.0, 2.0, 3.0), P.Point.xyz(F32.neg(4.0), 5.0, 0.5))), P.Point.xyz(1.0, 2.0, 3.0))))
    +l1 : K.Line<F32> = G.Point.vee.Point(P.Point.xyz(1.0, 0.0, 0.0), P.Point.xyz(1.0, 1.0, 0.0))
    +l2 : K.Line<F32> = G.Point.vee.Point(P.Point.xyz(0.0, 0.0, 2.0), P.Point.xyz(1.0, 0.0, 2.0))
    IO.print(F32.show(Line.err(P.Line.normalized(G.Motor.transform.Line(M(P.Motor.between.lines(l1, l2)), l1)), P.Line.normalized(l2))))
    IO.print(Bool.show(F32.is_lt(Line.err(P.Motor.log(P.Line.exp(screw())), screw()), 1.0e-5)))
    IO.print(Bool.show(F32.is_lt(Study.err(P.Motor.study(M(P.Motor.normalized(K.Motor{2.0, 0.6, F32.neg(0.8), 1.0, 0.3, 0.1, 0.7, 0.25})))), 1.0e-6)))
    +m : K.Motor<F32> = M(P.Line.exp(screw()))
    +h : K.Motor<F32> = M(P.Motor.sqrt(U.Normed{m}))
    IO.print(Bool.show(F32.is_lt(Motor.err(G.Motor.gp.Motor(h, h), m), 1.0e-5)))
    IO.print(Bool.show(F32.is_lt(halving.err(screw.at(0.4999)), 1.0e-6)))
    IO.print(Bool.show(F32.is_lt(halving.err(screw.at(0.5001)), 1.0e-6)))
    IO.print(Bool.show(F32.is_lt(halving.err(screw.at(1.0e-4)), 1.0e-6)))
    IO.print(Bool.show(F32.is_lt(Line.err(P.Motor.log(P.Line.exp(screw.at(1.0e-4))), screw.at(1.0e-4)), 1.0e-7)))
    IO.print(F32.show(Line.err(P.Motor.log(P.Motor.translation(3.0, F32.neg(2.0), 7.5)), K.Line{0.0, 0.0, 0.0, F32.neg(1.5), 1.0, F32.neg(3.75)})))
#|(0, 0, 1)
#|(1, 2, 3)
#|(-4, 5, 0.5)
#|0
#|True
#|True
#|True
#|True
#|True
#|True
#|True
#|0
