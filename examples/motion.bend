# A quarter turn about the x axis, then a translation by 2 along z, applied
# to the point (0, 1, 0): it lands on (0, 0, 3).
import Base
import ../api/pga3d.bend as P
import ../api/normed.bend as U
import ../algebras/pga3d/kinds.bend as K
import ../algebras/pga3d/f32.bend as G

def x_axis() -> K.Line<F32>:
  G.Point.vee.Point(P.Point.xyz(0.0, 0.0, 0.0), P.Point.xyz(1.0, 0.0, 0.0))

def moved(p: K.Point<F32>) -> K.Point<F32>:
  +m = P.Motor.then(P.Motor.rotation(x_axis(), (F32.pi() * 0.5 : F32)), P.Motor.translation(0.0, 0.0, 2.0))
  G.Motor.transform.Point(U.Normed.get(K.Motor<F32>, m), p)

def r4(x: F32) -> String:
  F32.show((F32.round((x * 10000.0 : F32)) / 10000.0 : F32))

def Point.show(p: K.Point<F32>) -> String:
  match p:
    case K.Point{x, y, z, +w}:
      "(" ++ r4((x / w : F32)) ++ ", " ++ r4((y / w : F32)) ++ ", " ++ r4((z / w : F32)) ++ ")"

def main() -> IO(Unit):
  IO.print(Point.show(moved(P.Point.xyz(0.0, 1.0, 0.0))))
#|(0, 0, 3)
