# PGA2D, the API (Layer A): points, lines and rigid motions of the plane,
# at F32. Products and sandwiches are the generated kernels in
# algebras/pga2d/f32.bend (G), kinds in algebras/pga2d/kinds.bend (K).
#
# Conventions are gax's: a point is x e20 + y e01 + w e12, a line
# a e1 + b e2 + c e0 (ax + by + c = 0), a translator 1 + (dy e20 - dx e01)/2.
# A motor's bivector squares to the scalar -e12², so exp and log are the
# Study functions at I = 0 (api/study.bend).

import Base
import ./study.bend as St
import ./normed.bend as U
import ../algebras/pga2d/kinds.bend as K
import ../algebras/pga2d/f32.bend as G

def Point.xy(x: F32, y: F32) -> K.Point<F32>:
  K.Point{x, y, 1.0}

def Line.abc(a: F32, b: F32, c: F32) -> K.Line<F32>:
  K.Line{a, b, c}

def Motor.identity() -> U.Normed<K.Motor<F32>>:
  U.Normed{K.Motor{1.0, 0.0, 0.0, 0.0}}

# the translation by (dx, dy)
def Motor.translation(+dx: F32, +dy: F32) -> U.Normed<K.Motor<F32>>:
  U.Normed{K.Motor{1.0, 0.0, (dy * 0.5 : F32), (F32.neg(dx) * 0.5 : F32)}}

def Motor.scalar(m: K.Motor<F32>) -> F32:
  match m:
    case K.Motor{s, a, b, c}:
      s

def Motor.normalized(+m: K.Motor<F32>) -> U.Normed<K.Motor<F32>>:
  U.Normed{G.Scalar.gp.Motor(K.Scalar{(1.0 / F32.sqrt(Motor.scalar(G.Motor.gp.Motor(m, G.Motor.reverse(m)))) : F32)}, m)}

def Motor.renormalize_fast(u: U.Normed<K.Motor<F32>>) -> U.Normed<K.Motor<F32>>:
  match u:
    case U.Normed{+m}:
      U.Normed{G.Scalar.gp.Motor(K.Scalar{((3.0 - Motor.scalar(G.Motor.gp.Motor(m, G.Motor.reverse(m)))) * 0.5 : F32)}, m)}

def Point.exp.fin(c: F32, +sv: F32, b: K.Point<F32>) -> U.Normed<K.Motor<F32>>:
  match b:
    case K.Point{x, y, w}:
      U.Normed{K.Motor{c, (sv * w : F32), (sv * x : F32), (sv * y : F32)}}

# exp(B) for a bivector B (a point's components): C(σ) + S(σ) B, σ = -e12²
def Point.exp(+b: K.Point<F32>) -> U.Normed<K.Motor<F32>>:
  match b:
    case K.Point{x, y, +w}:
      +s = F32.neg((w * w : F32))
      Point.exp.fin(St.Study.C(s), St.Study.S(s), K.Point{x, y, w})

def Motor.log.go(+c: F32, +w: F32, x: F32, y: F32) -> K.Point<F32>:
  +f = St.Study.angle_over_sin(F32.abs(w), c)
  K.Point{(f * x : F32), (f * y : F32), (f * w : F32)}

# the bivector B with exp(B) = m
def Motor.log(u: U.Normed<K.Motor<F32>>) -> K.Point<F32>:
  match u:
    case U.Normed{m}:
      match m:
        case K.Motor{c, w, x, y}:
          Motor.log.go(c, w, x, y)

# the rotation by angle about the point p, counterclockwise
def Motor.rotation(p: K.Point<F32>, +angle: F32) -> U.Normed<K.Motor<F32>>:
  match p:
    case K.Point{x, y, +w}:
      +k = (F32.neg(0.5) * angle / w : F32)
      Point.exp(K.Point{(k * x : F32), (k * y : F32), (k * w : F32)})

def Motor.sqrt(u: U.Normed<K.Motor<F32>>) -> U.Normed<K.Motor<F32>>:
  match u:
    case U.Normed{m}:
      Motor.normalized(G.Motor.add.Motor(K.Motor{1.0, 0.0, 0.0, 0.0}, m))

def Translator.widen(t: K.Translator<F32>) -> K.Motor<F32>:
  match t:
    case K.Translator{s, a, b}:
      K.Motor{s, 0.0, a, b}

# the motion carrying the point a to b, and the line a to b
def Motor.between.points(+a: K.Point<F32>, b: K.Point<F32>) -> U.Normed<K.Motor<F32>>:
  Motor.sqrt(Motor.normalized(Translator.widen(G.Point.gp.Point(b, G.Point.reverse(a)))))

def Motor.between.lines(+a: K.Line<F32>, b: K.Line<F32>) -> U.Normed<K.Motor<F32>>:
  Motor.sqrt(Motor.normalized(G.Line.gp.Line(b, G.Line.reverse(a))))

def Motor.then(u: U.Normed<K.Motor<F32>>, w: U.Normed<K.Motor<F32>>) -> U.Normed<K.Motor<F32>>:
  match u w:
    case U.Normed{a} U.Normed{b}:
      U.Normed{G.Motor.gp.Motor(b, a)}

def Motor.apply(u: U.Normed<K.Motor<F32>>, p: K.Point<F32>) -> K.Point<F32>:
  match u:
    case U.Normed{m}:
      G.Motor.transform.Point(m, p)
