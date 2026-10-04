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
