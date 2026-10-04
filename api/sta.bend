# STA, the API (Layer A): the Lorentz group at F32. Rotors are even
# versors (Normed<Even>), bivectors generate them, events are vectors.
# Products and sandwiches are the generated kernels (G, algebras/sta).
#
# Conventions: signature (+, -, -, -) with e0 the time direction, so an
# event is t e0 + x e1 + y e2 + z e3, and I = e0123 squares to -1. A
# bivector B squares to a complex number z = λ + μ I, so exp and log are
# complex functions of z (api/cx.bend): exp(B) = C(z) + S(z) B. A boost
# with rapidity φ along a unit direction n is exp(φ/2 n_k e_k0), taking e0
# to cosh φ e0 + sinh φ n; a rotation by θ about n is exp(θ/2 (n1 e23 +
# n2 e31 + n3 e12)), right-handed.

import Base
import ./cx.bend as C
import ./normed.bend as U
import ../algebras/sta/kinds.bend as K
import ../algebras/sta/f32.bend as G

# Parts
# -----

def Phasor.of(z: C.Cx) -> K.Phasor<F32>:
  match z:
    case C.Cx{re, im}:
      K.Phasor{re, im}

# the scalar and pseudoscalar parts of an even element, as a complex number
def Even.phasor(r: K.Even<F32>) -> C.Cx:
  match r:
    case K.Even{s, e10, e20, e30, e23, e31, e12, e0123}:
      C.Cx{s, e0123}

def Even.bivector(r: K.Even<F32>) -> K.Bivector<F32>:
  match r:
    case K.Even{s, e10, e20, e30, e23, e31, e12, e0123}:
      K.Bivector{e10, e20, e30, e23, e31, e12}

# B², a complex number (the bivector part of B B vanishes in 4D)
def Bivector.square(+b: K.Bivector<F32>) -> C.Cx:
  Even.phasor(G.Bivector.gp.Bivector(b, b))

def Rotor.of(-A: Data, u: U.Normed<K.Even<F32>>) -> K.Even<F32>:
  U.Normed.get(K.Even<F32>, u)

# Constructors
# ------------

# the event (t, x, y, z)
def Event.txyz(t: F32, x: F32, y: F32, z: F32) -> K.Vector<F32>:
  K.Vector{t, x, y, z}

def Rotor.identity() -> U.Normed<K.Even<F32>>:
  U.Normed{K.Even{1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0}}

# exp(B) = C(B²) + S(B²) B, a unit rotor
def Bivector.exp.go(+b: K.Bivector<F32>, +z: C.Cx) -> U.Normed<K.Even<F32>>:
  U.Normed{G.Phasor.add.Bivector(Phasor.of(C.Cx.C(z)), G.Phasor.gp.Bivector(Phasor.of(C.Cx.S(z)), b))}

def Bivector.exp(+b: K.Bivector<F32>) -> U.Normed<K.Even<F32>>:
  Bivector.exp.go(b, Bivector.square(b))

# log R = h P for R = c + P (c its phasor part, P its bivector part), with
# h = acosh(c) / √(P²) (api/cx.bend, Cx.H)
def Even.log.go(+c: C.Cx, +p: K.Bivector<F32>) -> K.Bivector<F32>:
  G.Phasor.gp.Bivector(Phasor.of(C.Cx.H(c, Bivector.square(p))), p)

def Rotor.log(u: U.Normed<K.Even<F32>>) -> K.Bivector<F32>:
  +r = Rotor.of(K.Even<F32>, u)
  Even.log.go(Even.phasor(r), Even.bivector(r))

# R (R ~R)^(-1/2): R ~R is a phasor, which commutes with R
def Rotor.normalized(+r: K.Even<F32>) -> U.Normed<K.Even<F32>>:
  U.Normed{G.Phasor.gp.Even(Phasor.of(C.Cx.rsqrt(Even.phasor(G.Even.gp.Even(r, G.Even.reverse(r))))), r)}

# the boost with rapidity phi along (nx, ny, nz)
def Rotor.boost(+nx: F32, +ny: F32, +nz: F32, +phi: F32) -> U.Normed<K.Even<F32>>:
  +k = (0.5 * phi / F32.sqrt((nx * nx + ny * ny + nz * nz : F32)) : F32)
  Bivector.exp(K.Bivector{(k * nx : F32), (k * ny : F32), (k * nz : F32), 0.0, 0.0, 0.0})

# the rotation by angle about (nx, ny, nz), right-handed
def Rotor.rotation(+nx: F32, +ny: F32, +nz: F32, +angle: F32) -> U.Normed<K.Even<F32>>:
  +k = (0.5 * angle / F32.sqrt((nx * nx + ny * ny + nz * nz : F32)) : F32)
  Bivector.exp(K.Bivector{0.0, 0.0, 0.0, (k * nx : F32), (k * ny : F32), (k * nz : F32)})

# Using rotors
# ------------

# u, then w
def Rotor.then(u: U.Normed<K.Even<F32>>, w: U.Normed<K.Even<F32>>) -> U.Normed<K.Even<F32>>:
  U.Normed{G.Even.gp.Even(Rotor.of(K.Even<F32>, w), Rotor.of(K.Even<F32>, u))}

def Rotor.inverse(u: U.Normed<K.Even<F32>>) -> U.Normed<K.Even<F32>>:
  U.Normed{G.Even.reverse(Rotor.of(K.Even<F32>, u))}

# R v ~R
def Rotor.apply(u: U.Normed<K.Even<F32>>, v: K.Vector<F32>) -> K.Vector<F32>:
  G.Even.transform.Vector(Rotor.of(K.Even<F32>, u), v)

# the Minkowski square t² - x² - y² - z²
def Vector.square(+v: K.Vector<F32>) -> F32:
  K.Scalar.s(F32, G.Vector.scalar_product.Vector(v, v))
