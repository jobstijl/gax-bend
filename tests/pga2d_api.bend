# The PGA2D API at F32 (f32-prop), printed rounded to 1e-4:
# - the translation by (3, 4) moves the origin to (3, 4);
# - a quarter turn about the origin moves (1, 0) to (0, 1) (counterclockwise);
# - a quarter turn about (1, 1) moves (2, 1) to (1, 2);
# - the motion between (1, 2) and (-3, 0.5) carries the first to the second;
# - log(exp(B)) = B within 1e-6 for a rotation and for a translation.
import Base
import ../api/pga2d.bend as P
import ../api/normed.bend as U
import ../algebras/pga2d/kinds.bend as K

def r4(x: F32) -> String:
  F32.show((F32.round((x * 10000.0 : F32)) / 10000.0 : F32))

def Point.show(p: K.Point<F32>) -> String:
  match p:
    case K.Point{x, y, +w}:
      "(" ++ r4((x / w : F32)) ++ ", " ++ r4((y / w : F32)) ++ ")"

def Pt.err(a: K.Point<F32>, b: K.Point<F32>) -> F32:
  match a b:
    case K.Point{a1, a2, a3} K.Point{b1, b2, b3}:
      F32.max(F32.abs((a1 - b1 : F32)), F32.max(F32.abs((a2 - b2 : F32)), F32.abs((a3 - b3 : F32))))

def quarter() -> F32:
  (F32.pi() * 0.5 : F32)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Point.show(P.Motor.apply(P.Motor.translation(3.0, 4.0), P.Point.xy(0.0, 0.0))))
    IO.print(Point.show(P.Motor.apply(P.Motor.rotation(P.Point.xy(0.0, 0.0), quarter()), P.Point.xy(1.0, 0.0))))
    IO.print(Point.show(P.Motor.apply(P.Motor.rotation(P.Point.xy(1.0, 1.0), quarter()), P.Point.xy(2.0, 1.0))))
    IO.print(Point.show(P.Motor.apply(P.Motor.between.points(P.Point.xy(1.0, 2.0), P.Point.xy(F32.neg(3.0), 0.5)), P.Point.xy(1.0, 2.0))))
    IO.print(Bool.show(F32.is_lt(Pt.err(P.Motor.log(P.Point.exp(K.Point{0.2, F32.neg(0.7), 0.6})), K.Point{0.2, F32.neg(0.7), 0.6}), 1.0e-6)))
    IO.print(Bool.show(F32.is_lt(Pt.err(P.Motor.log(P.Point.exp(K.Point{1.5, F32.neg(2.5), 0.0})), K.Point{1.5, F32.neg(2.5), 0.0}), 1.0e-6)))
#|(3, 4)
#|(0, 1)
#|(1, 2)
#|(-3, 0.5)
#|True
#|True
