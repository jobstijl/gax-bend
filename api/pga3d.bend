# PGA3D, the API (Layer A): constructors, norms, exp and log, square roots
# and the motor between two elements, at F32. Products and sandwiches are
# the generated kernels in algebras/pga3d/f32.bend (G), the kinds and their
# fields in algebras/pga3d/kinds.bend (K).
#
# Conventions are gax's (docs/guide.md §17): a point is
# x e032 + y e013 + z e021 + w e123, a plane a e1 + b e2 + c e3 + d e0
# (ax + by + cz + d = 0), a translator 1 - (d e0i) / 2, and a positive
# rotation about a line is right-handed about its direction.

import Base
import ./study.bend as St
import ./normed.bend as U
import ../algebras/pga3d/kinds.bend as K
import ../algebras/pga3d/f32.bend as G

# Constructors
# ------------

# the point (x, y, z)
def Point.xyz(x: F32, y: F32, z: F32) -> K.Point<F32>:
  K.Point{x, y, z, 1.0}

# the direction (x, y, z): a point at infinity
def Point.direction(x: F32, y: F32, z: F32) -> K.Point<F32>:
  K.Point{x, y, z, 0.0}

# the plane ax + by + cz + d = 0
def Plane.abcd(a: F32, b: F32, c: F32, d: F32) -> K.Plane<F32>:
  K.Plane{a, b, c, d}

def Motor.identity() -> U.Normed<K.Motor<F32>>:
  U.Normed{K.Motor{1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0}}

# the translation by (dx, dy, dz)
def Motor.translation(+dx: F32, +dy: F32, +dz: F32) -> U.Normed<K.Motor<F32>>:
  U.Normed{K.Motor{1.0, 0.0, 0.0, 0.0, (dx * F32.neg(0.5) : F32), (dy * F32.neg(0.5) : F32), (dz * F32.neg(0.5) : F32), 0.0}}

def Motor.of(-A: Data, u: U.Normed<K.Motor<F32>>) -> K.Motor<F32>:
  U.Normed.get(K.Motor<F32>, u)

# Study numbers
# -------------
# x ~x of a motor or a line is a Study number s + p I (I = e0123, I² = 0);
# multiplying by one is a + b I, done as a x + b (I x).

def Motor.study.go(n: K.Motor<F32>) -> F32 & F32:
  match n:
    case K.Motor{s, a1, a2, a3, a4, a5, a6, p}:
      (s, p)

# (s, p) with m ~m = s + p I
def Motor.study(+m: K.Motor<F32>) -> F32 & F32:
  Motor.study.go(G.Motor.gp.Motor(m, G.Motor.reverse(m)))

def Motor.scale_study(+a: F32, +b: F32, +m: K.Motor<F32>) -> K.Motor<F32>:
  G.Motor.add.Motor(G.Scalar.gp.Motor(K.Scalar{a}, m), G.Scalar.gp.Motor(K.Scalar{b}, G.Pseudoscalar.gp.Motor(K.Pseudoscalar{1.0}, m)))

def Line.scale_study(+a: F32, +b: F32, +l: K.Line<F32>) -> K.Line<F32>:
  G.Line.add.Line(G.Scalar.gp.Line(K.Scalar{a}, l), G.Scalar.gp.Line(K.Scalar{b}, G.Pseudoscalar.gp.Line(K.Pseudoscalar{1.0}, l)))

# (s + p I)^(-1/2) = s^(-1/2) - (p/2) s^(-3/2) I, exact for I² = 0
def Study.rsqrt(sp: F32 & F32) -> F32 & F32:
  match sp:
    case (+s, +p):
      +a = (1.0 / F32.sqrt(s) : F32)
      (a, (F32.neg(p) * 0.5 * a / s : F32))

# Norms
# -----

def Motor.normalized.go(+m: K.Motor<F32>, ab: F32 & F32) -> U.Normed<K.Motor<F32>>:
  match ab:
    case (a, b):
      U.Normed{Motor.scale_study(a, b, m)}

# m (m ~m)^(-1/2): scale-invariant, and exact in form for the e0123 part
def Motor.normalized(+m: K.Motor<F32>) -> U.Normed<K.Motor<F32>>:
  Motor.normalized.go(m, Study.rsqrt(Motor.study(m)))

def Line.study(+l: K.Line<F32>) -> F32 & F32:
  Motor.study.go(G.Line.gp.Line(l, G.Line.reverse(l)))

def Line.normalized.go(+l: K.Line<F32>, ab: F32 & F32) -> K.Line<F32>:
  match ab:
    case (a, b):
      Line.scale_study(a, b, l)

# the line scaled so that l ~l = 1
def Line.normalized(+l: K.Line<F32>) -> K.Line<F32>:
  Line.normalized.go(l, Study.rsqrt(Line.study(l)))

# one Newton step back towards m ~m = 1, with no square root (gax's
# renormalize_fast): (3 - n) m / 2 with n = m ~m = s + p I, so an error e
# in n becomes (3/4) e². Use it after products that drift.
def Motor.renormalize_fast.go(+m: K.Motor<F32>, sp: F32 & F32) -> U.Normed<K.Motor<F32>>:
  match sp:
    case (s, p):
      U.Normed{Motor.scale_study(((3.0 - s) * 0.5 : F32), (F32.neg(p) * 0.5 : F32), m)}

def Motor.renormalize_fast(u: U.Normed<K.Motor<F32>>) -> U.Normed<K.Motor<F32>>:
  match u:
    case U.Normed{+m}:
      Motor.renormalize_fast.go(m, Motor.study(m))

# Exponential and logarithm
# -------------------------

def Line.exp.fin(c: F32, q: F32, l: K.Line<F32>) -> U.Normed<K.Motor<F32>>:
  match l:
    case K.Line{a, b, d, e, f, g}:
      U.Normed{K.Motor{c, a, b, d, e, f, g, q}}

def Line.exp.go(+b: K.Line<F32>, sq: K.Motor<F32>) -> U.Normed<K.Motor<F32>>:
  match sq:
    case K.Motor{+s, a1, a2, a3, a4, a5, a6, +p}:
      +sv = St.Study.S(s)
      Line.exp.fin(St.Study.C(s), (p * sv * 0.5 : F32), Line.scale_study(sv, (p * St.Study.D(s) : F32), b))

# exp(B) = C(z) + S(z) B for B² = z = σ + π I, with each function of z
# taken as f(σ) + π f'(σ) I (St.Study, C' = S/2, S' = D)
def Line.exp(+b: K.Line<F32>) -> U.Normed<K.Motor<F32>>:
  Line.exp.go(b, G.Line.gp.Line(b, b))

def Motor.log.fin(+f: F32, +g: F32, +l: K.Line<F32>) -> K.Line<F32>:
  Line.scale_study(f, F32.neg(g), l)

def Motor.log.go(+c: F32, +l: K.Line<F32>, +p: F32) -> K.Line<F32>:
  match l:
    case K.Line{+u1, +u2, +u3, m1, m2, m3}:
      +s = F32.sqrt((u1 * u1 + u2 * u2 + u3 * u3 : F32))
      +f = St.Study.angle_over_sin(s, c)
      +th = (f * s : F32)
      Motor.log.fin(f, (2.0 * p * f * f * f * St.Study.D(F32.neg((th * th : F32))) : F32), l)

# the line B with exp(B) = m, for a unit motor m = c + B' + p I: B is
# f B' - g (I B'), with θ = atan2(|B'|, c) in [0, π], f = θ / sin θ and
# g = 2 p f³ S'(-θ²). A motor with c < 0 turns the long way; negate it for
# the short way (m and -m are the same motion).
def Motor.log(u: U.Normed<K.Motor<F32>>) -> K.Line<F32>:
  match u:
    case U.Normed{m}:
      match m:
        case K.Motor{c, a, b, d, e, f, g, p}:
          Motor.log.go(c, K.Line{a, b, d, e, f, g}, p)

# Square roots and motions between elements
# -----------------------------------------

# the square root of a unit motor: normalized(1 + m), the motion halfway
def Motor.sqrt(u: U.Normed<K.Motor<F32>>) -> U.Normed<K.Motor<F32>>:
  match u:
    case U.Normed{m}:
      Motor.normalized(G.Motor.add.Motor(K.Motor{1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0}, m))

def Translator.widen(t: K.Translator<F32>) -> K.Motor<F32>:
  match t:
    case K.Translator{s, a, b, c}:
      K.Motor{s, 0.0, 0.0, 0.0, a, b, c, 0.0}

# the motion that carries the point a to b: sqrt(normalized(b ~a))
def Motor.between.points(+a: K.Point<F32>, b: K.Point<F32>) -> U.Normed<K.Motor<F32>>:
  Motor.sqrt(Motor.normalized(Translator.widen(G.Point.gp.Point(b, G.Point.reverse(a)))))

# the motion that carries the line a to b
def Motor.between.lines(+a: K.Line<F32>, b: K.Line<F32>) -> U.Normed<K.Motor<F32>>:
  Motor.sqrt(Motor.normalized(G.Line.gp.Line(b, G.Line.reverse(a))))

# the motion that carries the plane a to b
def Motor.between.planes(+a: K.Plane<F32>, b: K.Plane<F32>) -> U.Normed<K.Motor<F32>>:
  Motor.sqrt(Motor.normalized(G.Plane.gp.Plane(b, G.Plane.reverse(a))))

# the rotation by angle about a line, right-handed about its direction
def Motor.rotation(axis: K.Line<F32>, +angle: F32) -> U.Normed<K.Motor<F32>>:
  Line.exp(G.Scalar.gp.Line(K.Scalar{(angle * F32.neg(0.5) : F32)}, Line.normalized(axis)))

# composition: first a, then b (b a); units compose
def Motor.then(u: U.Normed<K.Motor<F32>>, w: U.Normed<K.Motor<F32>>) -> U.Normed<K.Motor<F32>>:
  match u w:
    case U.Normed{a} U.Normed{b}:
      U.Normed{G.Motor.gp.Motor(b, a)}

def Motor.inverse(u: U.Normed<K.Motor<F32>>) -> U.Normed<K.Motor<F32>>:
  match u:
    case U.Normed{m}:
      U.Normed{G.Motor.reverse(m)}
