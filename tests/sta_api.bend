# STA's API (api/sta.bend) at F32: a boost and a rotation act as stated,
# exp and log invert each other on bivectors whose square is complex (a
# boost and a rotation together), exp gives unit rotors, normalized
# recovers a scaled rotor, and a Lorentz rotor keeps the Minkowski square.
import Base
import ../api/sta.bend as A
import ../api/cx.bend as C
import ../api/normed.bend as U
import ../algebras/sta/kinds.bend as K

def near(+a: F32, +b: F32) -> Bool:
  F32.is_lt(F32.abs((a - b : F32)), 2.0e-5)

def Vector.near(a: K.Vector<F32>, b: K.Vector<F32>) -> Bool:
  match a b:
    case K.Vector{a0, a1, a2, a3} K.Vector{b0, b1, b2, b3}:
      Bool.and(Bool.and(near(a0, b0), near(a1, b1)), Bool.and(near(a2, b2), near(a3, b3)))

def Bivector.near(a: K.Bivector<F32>, b: K.Bivector<F32>) -> Bool:
  match a b:
    case K.Bivector{a0, a1, a2, a3, a4, a5} K.Bivector{b0, b1, b2, b3, b4, b5}:
      Bool.and(Bool.and(Bool.and(near(a0, b0), near(a1, b1)), Bool.and(near(a2, b2), near(a3, b3))), Bool.and(near(a4, b4), near(a5, b5)))

def Even.near(a: K.Even<F32>, b: K.Even<F32>) -> Bool:
  match a b:
    case K.Even{a0, a1, a2, a3, a4, a5, a6, a7} K.Even{b0, b1, b2, b3, b4, b5, b6, b7}:
      Bool.and(Bool.and(Bool.and(near(a0, b0), near(a1, b1)), Bool.and(near(a2, b2), near(a3, b3))),
        Bool.and(Bool.and(near(a4, b4), near(a5, b5)), Bool.and(near(a6, b6), near(a7, b7))))

def roundtrip(+b: K.Bivector<F32>) -> Bool:
  Bivector.near(A.Rotor.log(A.Bivector.exp(b)), b)

# R ~R = 1
def unit(+b: K.Bivector<F32>) -> Bool:
  +r = A.Rotor.of(K.Even<F32>, A.Bivector.exp(b))
  +n = A.Rotor.of(K.Even<F32>, A.Rotor.then(A.Rotor.inverse(U.Normed{r}), U.Normed{r}))
  Even.near(n, K.Even{1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0})

def scaled(+r: K.Even<F32>) -> K.Even<F32>:
  match r:
    case K.Even{a0, a1, a2, a3, a4, a5, a6, a7}:
      K.Even{(3.0 * a0 : F32), (3.0 * a1 : F32), (3.0 * a2 : F32), (3.0 * a3 : F32), (3.0 * a4 : F32), (3.0 * a5 : F32), (3.0 * a6 : F32), (3.0 * a7 : F32)}

def renorm(+b: K.Bivector<F32>) -> Bool:
  +r = A.Rotor.of(K.Even<F32>, A.Bivector.exp(b))
  Even.near(A.Rotor.of(K.Even<F32>, A.Rotor.normalized(scaled(r))), r)

def mixed() -> K.Bivector<F32>:
  K.Bivector{0.3, 0.0, 0.0, 0.5, 0.0, 0.0}

def generic() -> K.Bivector<F32>:
  K.Bivector{0.2, F32.neg(0.1), 0.3, 0.4, 0.1, F32.neg(0.2)}

def tiny() -> K.Bivector<F32>:
  K.Bivector{0.001, 0.0, F32.neg(0.002), 0.0, 0.0015, 0.0}

def big() -> K.Bivector<F32>:
  K.Bivector{0.0, 1.5, 0.0, 0.9, 0.0, 2.5}

def main() -> IO(Unit):
  +boosted = A.Rotor.apply(A.Rotor.boost(1.0, 0.0, 0.0, 0.5), A.Event.txyz(1.0, 0.0, 0.0, 0.0))
  +turned = A.Rotor.apply(A.Rotor.rotation(0.0, 0.0, 1.0, 1.5707964), A.Event.txyz(0.0, 1.0, 0.0, 0.0))
  +ev = A.Event.txyz(2.0, 0.3, F32.neg(0.4), 1.1)
  +moved = A.Rotor.apply(A.Bivector.exp(generic()), ev)
  do IO<Unit>:
    IO.print("boost e0: " ++ Bool.show(Vector.near(boosted, A.Event.txyz(F32.cosh(0.5), F32.sinh(0.5), 0.0, 0.0))))
    IO.print("rotate e1 about e3: " ++ Bool.show(Vector.near(turned, A.Event.txyz(0.0, 0.0, 1.0, 0.0))))
    IO.print("B squares to " ++ F32.show(C.Cx.re(A.Bivector.square(mixed()))) ++ " + " ++ F32.show(C.Cx.im(A.Bivector.square(mixed()))) ++ " I")
    IO.print("log exp: " ++ Bool.show(Bool.and(Bool.and(roundtrip(mixed()), roundtrip(generic())), Bool.and(roundtrip(tiny()), roundtrip(big())))))
    IO.print("unit: " ++ Bool.show(Bool.and(unit(generic()), unit(big()))))
    IO.print("normalized: " ++ Bool.show(Bool.and(renorm(generic()), renorm(mixed()))))
    IO.print("Minkowski square kept: " ++ Bool.show(near(A.Vector.square(moved), A.Vector.square(ev))))
#|boost e0: True
#|rotate e1 about e3: True
#|B squares to -0.16 + -0.3 I
#|log exp: True
#|unit: True
#|normalized: True
#|Minkowski square kept: True
