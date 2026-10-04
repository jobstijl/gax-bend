# Drift is a uniform scale (ADR-003, "unit kernels: measured, not
# adopted"): the generated sandwich is homogeneous of degree 2 in the
# motor, so a drifted motor (1 + d) M moves points by (1 + d)² times the
# same homogeneous point. After unitizing, the moved points agree, and so
# do distances. Here d = 10^-3.
import Base
import ../api/pga3d.bend as P
import ../api/normed.bend as U
import ../algebras/pga3d/kinds.bend as K
import ../algebras/pga3d/f32.bend as G

def scale(+k: F32, m: K.Motor<F32>) -> K.Motor<F32>:
  match m:
    case K.Motor{a, b, c, d, e, f, g, h}:
      K.Motor{(k * a : F32), (k * b : F32), (k * c : F32), (k * d : F32), (k * e : F32), (k * f : F32), (k * g : F32), (k * h : F32)}

type V3 is Data:
  V3{x: F32, y: F32, z: F32}

# (x, y, z) of a homogeneous point
def xyz(p: K.Point<F32>) -> V3:
  match p:
    case K.Point{x, y, z, +w}:
      V3{(x / w : F32), (y / w : F32), (z / w : F32)}

def dist(a: V3, b: V3) -> F32:
  match a b:
    case V3{ax, ay, az} V3{bx, by, bz}:
      +dx = (ax - bx : F32)
      +dy = (ay - by : F32)
      +dz = (az - bz : F32)
      F32.sqrt((dx * dx + dy * dy + dz * dz : F32))

def close(+a: F32, +b: F32) -> Bool:
  F32.is_lt(F32.abs((a - b : F32)), 1.0e-5)

def same(a: V3, b: V3) -> Bool:
  match a b:
    case V3{ax, ay, az} V3{bx, by, bz}:
      Bool.and(close(ax, bx), Bool.and(close(ay, by), close(az, bz)))

def main() -> IO(Unit):
  +m = P.Motor.of(K.Motor<F32>, P.Motor.then(P.Motor.rotation(K.Line{0.3, 0.5, 0.8, 0.1, F32.neg(0.2), 0.05}, 1.1), P.Motor.translation(1.0, F32.neg(2.0), 0.5)))
  +md = scale(1.001, m)
  +p = P.Point.xyz(1.0, 2.0, 3.0)
  +q = P.Point.xyz(F32.neg(0.5), 0.25, 4.0)
  +p1 = xyz(G.Motor.transform.Point(m, p))
  +q1 = xyz(G.Motor.transform.Point(m, q))
  +p2 = xyz(G.Motor.transform.Point(md, p))
  +q2 = xyz(G.Motor.transform.Point(md, q))
  do IO<Unit>:
    IO.print("moved points agree: " ++ Bool.show(Bool.and(same(p1, p2), same(q1, q2))))
    IO.print("distance kept: " ++ Bool.show(close(dist(p2, q2), dist(xyz(p), xyz(q)))))
#|moved points agree: True
#|distance kept: True
