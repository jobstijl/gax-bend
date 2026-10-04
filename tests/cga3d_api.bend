# The CGA3D API at F32 (f32-prop), printed rounded to 1e-4:
# - a quarter turn about z moves (1, 0, 0) to (0, 1, 0) (right-handed);
# - the translation by (1, 2, 3) moves the origin to (1, 2, 3);
# - the squared distance of (1, 2, 3) and (4, 6, 3) is 25;
# - the point (3, 4, 0) lies on the sphere of radius 5 at the origin: P . S = 0;
# - after a turn and a translation, the moved point still lies on the moved
#   sphere (P . S within 1e-4).
import Base
import ../api/cga3d.bend as C
import ../api/normed.bend as U
import ../algebras/cga3d/kinds.bend as K
import ../algebras/cga3d/f32.bend as G

def r4(x: F32) -> String:
  F32.show((F32.round((x * 10000.0 : F32)) / 10000.0 : F32))

def Point.show.go(p: K.Vector<F32>) -> String:
  match p:
    case K.Vector{x, y, z, o, i}:
      "(" ++ r4(x) ++ ", " ++ r4(y) ++ ", " ++ r4(z) ++ ")"

def Point.show(p: K.Vector<F32>) -> String:
  Point.show.go(C.Point.unitized(p))

def dot(a: K.Vector<F32>, b: K.Vector<F32>) -> F32:
  C.Scalar.s(G.Vector.dot.Vector(a, b))

def m() -> U.Normed<K.Motor<F32>>:
  C.Motor.then(C.Motor.rotation(1.0, 1.0, 0.0, 0.7), C.Motor.translation(0.5, F32.neg(2.0), 1.5))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Point.show(C.Motor.apply(C.Motor.rotation(0.0, 0.0, 1.0, (F32.pi() * 0.5 : F32)), C.Point.xyz(1.0, 0.0, 0.0))))
    IO.print(Point.show(C.Motor.apply(C.Motor.translation(1.0, 2.0, 3.0), C.Point.xyz(0.0, 0.0, 0.0))))
    IO.print(r4(C.Point.distance2(C.Point.xyz(1.0, 2.0, 3.0), C.Point.xyz(4.0, 6.0, 3.0))))
    IO.print(r4(dot(C.Point.xyz(3.0, 4.0, 0.0), C.Sphere.at(0.0, 0.0, 0.0, 5.0))))
    IO.print(Bool.show(F32.is_lt(F32.abs(dot(C.Motor.apply(m(), C.Point.xyz(3.0, 4.0, 0.0)), C.Motor.apply(m(), C.Sphere.at(0.0, 0.0, 0.0, 5.0)))), 1.0e-4)))
#|(0, 1, 0)
#|(1, 2, 3)
#|25
#|0
#|True
