# VGA3D, the API (Layer A): rotations of Euclidean space by rotors, at
# F32. Products and sandwiches are the generated kernels in
# algebras/vga3d/f32.bend (G), kinds in algebras/vga3d/kinds.bend (K).
# A rotor's bivector squares to a scalar, so exp and log are the Study
# functions at I = 0 (api/study.bend) with no pseudoscalar part.

import Base
import ./study.bend as St
import ./normed.bend as U
import ../algebras/vga3d/kinds.bend as K
import ../algebras/vga3d/f32.bend as G

def Vector.xyz(x: F32, y: F32, z: F32) -> K.Vector<F32>:
  K.Vector{x, y, z}

def Rotor.identity() -> U.Normed<K.Rotor<F32>>:
  U.Normed{K.Rotor{1.0, 0.0, 0.0, 0.0}}

def Rotor.scalar(r: K.Rotor<F32>) -> F32:
  match r:
    case K.Rotor{s, a, b, c}:
      s

# r / sqrt(r ~r)
def Rotor.normalized(+r: K.Rotor<F32>) -> U.Normed<K.Rotor<F32>>:
  U.Normed{G.Scalar.gp.Rotor(K.Scalar{(1.0 / F32.sqrt(Rotor.scalar(G.Rotor.gp.Rotor(r, G.Rotor.reverse(r)))) : F32)}, r)}

# one Newton step back towards r ~r = 1: (3 - r ~r) r / 2
def Rotor.renormalize_fast(u: U.Normed<K.Rotor<F32>>) -> U.Normed<K.Rotor<F32>>:
  match u:
    case U.Normed{+r}:
      U.Normed{G.Scalar.gp.Rotor(K.Scalar{((3.0 - Rotor.scalar(G.Rotor.gp.Rotor(r, G.Rotor.reverse(r)))) * 0.5 : F32)}, r)}

def Bivector.exp.fin(c: F32, +sv: F32, b: K.Bivector<F32>) -> U.Normed<K.Rotor<F32>>:
  match b:
    case K.Bivector{+x, +y, +z}:
      U.Normed{K.Rotor{c, (sv * x : F32), (sv * y : F32), (sv * z : F32)}}

# exp(B) = C(σ) + S(σ) B with σ = B²
def Bivector.exp(+b: K.Bivector<F32>) -> U.Normed<K.Rotor<F32>>:
  +s = Rotor.scalar(G.Bivector.gp.Bivector(b, b))
  Bivector.exp.fin(St.Study.C(s), St.Study.S(s), b)

def Rotor.log.go(+c: F32, +x: F32, +y: F32, +z: F32) -> K.Bivector<F32>:
  +f = St.Study.angle_over_sin(F32.sqrt((x * x + y * y + z * z : F32)), c)
  K.Bivector{(f * x : F32), (f * y : F32), (f * z : F32)}

# the bivector B with exp(B) = r, the angle in [0, π]
def Rotor.log(u: U.Normed<K.Rotor<F32>>) -> K.Bivector<F32>:
  match u:
    case U.Normed{r}:
      match r:
        case K.Rotor{c, x, y, z}:
          Rotor.log.go(c, x, y, z)

# the rotation by angle about the axis (x, y, z), right-handed
def Rotor.rotation(+x: F32, +y: F32, +z: F32, +angle: F32) -> U.Normed<K.Rotor<F32>>:
  +k = (F32.neg(0.5) * angle / F32.sqrt((x * x + y * y + z * z : F32)) : F32)
  Bivector.exp(K.Bivector{(k * x : F32), (k * y : F32), (k * z : F32)})

def Rotor.sqrt(u: U.Normed<K.Rotor<F32>>) -> U.Normed<K.Rotor<F32>>:
  match u:
    case U.Normed{r}:
      Rotor.normalized(G.Rotor.add.Rotor(K.Rotor{1.0, 0.0, 0.0, 0.0}, r))

# the rotation that turns the direction of a into the direction of b
def Rotor.between(+a: K.Vector<F32>, b: K.Vector<F32>) -> U.Normed<K.Rotor<F32>>:
  Rotor.sqrt(Rotor.normalized(G.Vector.gp.Vector(b, a)))

# first a, then b
def Rotor.then(u: U.Normed<K.Rotor<F32>>, w: U.Normed<K.Rotor<F32>>) -> U.Normed<K.Rotor<F32>>:
  match u w:
    case U.Normed{a} U.Normed{b}:
      U.Normed{G.Rotor.gp.Rotor(b, a)}

def Rotor.apply(u: U.Normed<K.Rotor<F32>>, v: K.Vector<F32>) -> K.Vector<F32>:
  match u:
    case U.Normed{r}:
      G.Rotor.transform.Vector(r, v)
