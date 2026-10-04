# CGA3D, the API (Layer A): conformal points, spheres and planes, motions,
# at F32. Products and sandwiches are the generated kernels in
# algebras/cga3d/f32.bend (G), kinds in algebras/cga3d/kinds.bend (K).
#
# Conventions are gax's: the null basis e1, e2, e3, eo (origin), ei
# (infinity) with eo . ei = -1; a point is x + (x²/2) ei + eo; a sphere
# with centre c and radius r is c - (r²/2) ei (dual form); a plane with
# unit normal n at distance d from the origin is n + d ei; a translator is
# 1 - (t ei)/2.

import Base
import ./normed.bend as U
import ../algebras/cga3d/kinds.bend as K
import ../algebras/cga3d/f32.bend as G

# the point (x, y, z)
def Point.xyz(+x: F32, +y: F32, +z: F32) -> K.Vector<F32>:
  K.Vector{x, y, z, 1.0, (0.5 * (x * x + y * y + z * z) : F32)}

# the sphere with centre (x, y, z) and radius r
def Sphere.at(+x: F32, +y: F32, +z: F32, +r: F32) -> K.Vector<F32>:
  K.Vector{x, y, z, 1.0, (0.5 * (x * x + y * y + z * z - r * r) : F32)}

# the plane n . x = d for a unit normal n
def Plane.normal(nx: F32, ny: F32, nz: F32, d: F32) -> K.Vector<F32>:
  K.Vector{nx, ny, nz, 0.0, d}

# a point scaled to weight 1 (eo coefficient 1)
def Point.unitized(x: K.Vector<F32>) -> K.Vector<F32>:
  match x:
    case K.Vector{a, b, c, +o, i}:
      K.Vector{(a / o : F32), (b / o : F32), (c / o : F32), 1.0, (i / o : F32)}

def Motor.identity() -> U.Normed<K.Motor<F32>>:
  U.Normed{K.Motor{1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0}}

# the translation by (dx, dy, dz)
def Motor.translation(+dx: F32, +dy: F32, +dz: F32) -> U.Normed<K.Motor<F32>>:
  U.Normed{K.Motor{1.0, 0.0, 0.0, 0.0, (dx * F32.neg(0.5) : F32), (dy * F32.neg(0.5) : F32), (dz * F32.neg(0.5) : F32), 0.0}}

# the rotation by angle about the axis through the origin along (x, y, z),
# right-handed: exp(-angle/2 * the axis' dual bivector)
def Motor.rotation(+x: F32, +y: F32, +z: F32, +angle: F32) -> U.Normed<K.Motor<F32>>:
  +n = F32.sqrt((x * x + y * y + z * z : F32))
  +s = (F32.sin((angle * 0.5 : F32)) / n : F32)
  U.Normed{K.Motor{F32.cos((angle * 0.5 : F32)), F32.neg((s * x : F32)), F32.neg((s * y : F32)), F32.neg((s * z : F32)), 0.0, 0.0, 0.0, 0.0}}

# first a, then b
def Motor.then(u: U.Normed<K.Motor<F32>>, w: U.Normed<K.Motor<F32>>) -> U.Normed<K.Motor<F32>>:
  match u w:
    case U.Normed{a} U.Normed{b}:
      U.Normed{G.Motor.gp.Motor(b, a)}

# the vector part of an odd element: what a motor makes of a point, sphere
# or plane (the rest is zero for a unit motor)
def Odd.vector(x: K.Odd<F32>) -> K.Vector<F32>:
  match x:
    case K.Odd{e1, e2, e3, eo, ei, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, ps}:
      K.Vector{e1, e2, e3, eo, ei}

# a point, sphere or plane moved by a unit motor
def Motor.apply(u: U.Normed<K.Motor<F32>>, x: K.Vector<F32>) -> K.Vector<F32>:
  match u:
    case U.Normed{m}:
      Odd.vector(G.Motor.transform.Vector(m, x))

# the squared distance between two points: -2 P . Q for unit points
def Scalar.s(x: K.Scalar<F32>) -> F32:
  match x:
    case K.Scalar{s}:
      s

def Point.distance2(p: K.Vector<F32>, q: K.Vector<F32>) -> F32:
  (F32.neg(2.0) * Scalar.s(G.Vector.dot.Vector(Point.unitized(p), Point.unitized(q))) : F32)

# Lines, point pairs and flat points
# ----------------------------------

def eo() -> K.Vector<F32>:
  K.Vector{0.0, 0.0, 0.0, 1.0, 0.0}

def ei() -> K.Vector<F32>:
  K.Vector{0.0, 0.0, 0.0, 0.0, 1.0}

# the line through two points: p ^ q ^ ei (direct form)
def Line.through(p: K.Vector<F32>, q: K.Vector<F32>) -> K.Trivector<F32>:
  G.Bivector.wedge.Vector(G.Vector.wedge.Vector(p, q), ei())

# where a line meets a sphere or a plane (both in dual form): s ⌋ l, a
# point pair for a sphere, a flat point (p ^ ei) for a plane
def Line.meet(s: K.Vector<F32>, l: K.Trivector<F32>) -> K.Bivector<F32>:
  G.Vector.lc.Trivector(s, l)

# b² of a point pair: positive when its two points are real
def PointPair.square(+b: K.Bivector<F32>) -> F32:
  Scalar.s(G.Bivector.scalar_product.Bivector(b, b))

def PointPair.real(+b: K.Bivector<F32>) -> Bool:
  F32.is_lt(0.0, PointPair.square(b))

def Odd.vector.of(x: K.Odd<F32>) -> K.Vector<F32>:
  Odd.vector(x)

# the two points of a real point pair b = p ^ q, unitized:
# p = (b - √(b²))(ei ⌋ b) and q = (b + √(b²))(ei ⌋ b), up to scale
def PointPair.points(+b: K.Bivector<F32>) -> K.Vector<F32> & K.Vector<F32>:
  +v = G.Vector.lc.Bivector(ei(), b)
  +bv = Odd.vector(G.Bivector.gp.Vector(b, v))
  +rv = G.Scalar.gp.Vector(K.Scalar{F32.sqrt(PointPair.square(b))}, v)
  (Point.unitized(G.Vector.sub.Vector(bv, rv)), Point.unitized(G.Vector.add.Vector(bv, rv)))

def Point.of_flat(v: K.Vector<F32>) -> K.Vector<F32>:
  match v:
    case K.Vector{a, b, c, +o, i}:
      Point.xyz((a / o : F32), (b / o : F32), (c / o : F32))

# the point of a flat point f = p ^ ei: eo ⌋ f is p's position plus eo
def FlatPoint.point(f: K.Bivector<F32>) -> K.Vector<F32>:
  Point.of_flat(G.Vector.lc.Bivector(eo(), f))

# the centre of a sphere (dual form)
def Sphere.center(s: K.Vector<F32>) -> K.Vector<F32>:
  Point.of_flat(s)

# Directions
# ----------
# A direction is a vector with no eo and no ei part: a point at infinity's
# Euclidean part.

def Direction.xyz(x: F32, y: F32, z: F32) -> K.Vector<F32>:
  K.Vector{x, y, z, 0.0, 0.0}

def Direction.dot(a: K.Vector<F32>, b: K.Vector<F32>) -> F32:
  Scalar.s(G.Vector.dot.Vector(a, b))

def Direction.unit(v: K.Vector<F32>) -> K.Vector<F32>:
  match v:
    case K.Vector{+a, +b, +c, o, i}:
      +n = F32.sqrt((a * a + b * b + c * c : F32))
      K.Vector{(a / n : F32), (b / n : F32), (c / n : F32), 0.0, 0.0}

# the unit direction from point p to point q
def Direction.of(v: K.Vector<F32>) -> K.Vector<F32>:
  match v:
    case K.Vector{a, b, c, o, i}:
      Direction.unit(K.Vector{a, b, c, 0.0, 0.0})

def Direction.between(p: K.Vector<F32>, q: K.Vector<F32>) -> K.Vector<F32>:
  Direction.of(G.Vector.sub.Vector(Point.unitized(q), Point.unitized(p)))

# a direction scaled by k (a colour dimmed, a step lengthened)
def Direction.scaled(k: F32, d: K.Vector<F32>) -> K.Vector<F32>:
  G.Scalar.gp.Vector(K.Scalar{k}, d)

# the translation along a direction (by its length)
def Motor.along(d: K.Vector<F32>) -> U.Normed<K.Motor<F32>>:
  match d:
    case K.Vector{a, b, c, o, i}:
      Motor.translation(a, b, c)

# p moved by the direction d
def Point.moved(p: K.Vector<F32>, d: K.Vector<F32>) -> K.Vector<F32>:
  Motor.apply(Motor.along(d), p)
