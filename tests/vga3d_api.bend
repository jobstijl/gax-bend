# The VGA3D API at F32 (f32-prop), printed rounded to 1e-4:
# - a quarter turn about z moves (1, 0, 0) to (0, 1, 0) (right-handed);
# - the rotor between (1, 0, 0) and (0, 3, 4) turns the first into (0, 0.6, 0.8);
# - log(exp(B)) = B within 1e-6, and sqrt(r)² = r within 1e-6;
# - renormalize_fast takes r ~r = 1.002001 back within 1e-5.
import Base
import ../api/vga3d.bend as V
import ../api/normed.bend as U
import ../algebras/vga3d/kinds.bend as K
import ../algebras/vga3d/f32.bend as G

def r4(x: F32) -> String:
  F32.show((F32.round((x * 10000.0 : F32)) / 10000.0 : F32))

def Vector.show(v: K.Vector<F32>) -> String:
  match v:
    case K.Vector{x, y, z}:
      "(" ++ r4(x) ++ ", " ++ r4(y) ++ ", " ++ r4(z) ++ ")"

def R(u: U.Normed<K.Rotor<F32>>) -> K.Rotor<F32>:
  U.Normed.get(K.Rotor<F32>, u)

def B.err(a: K.Bivector<F32>, b: K.Bivector<F32>) -> F32:
  match a b:
    case K.Bivector{a1, a2, a3} K.Bivector{b1, b2, b3}:
      F32.max(F32.abs((a1 - b1 : F32)), F32.max(F32.abs((a2 - b2 : F32)), F32.abs((a3 - b3 : F32))))

def R.err(a: K.Rotor<F32>, b: K.Rotor<F32>) -> F32:
  match a b:
    case K.Rotor{a0, a1, a2, a3} K.Rotor{b0, b1, b2, b3}:
      F32.max(F32.max(F32.abs((a0 - b0 : F32)), F32.abs((a1 - b1 : F32))), F32.max(F32.abs((a2 - b2 : F32)), F32.abs((a3 - b3 : F32))))

def bv() -> K.Bivector<F32>:
  K.Bivector{0.3, F32.neg(0.9), 0.4}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Vector.show(V.Rotor.apply(V.Rotor.rotation(0.0, 0.0, 1.0, (F32.pi() * 0.5 : F32)), V.Vector.xyz(1.0, 0.0, 0.0))))
    IO.print(Vector.show(V.Rotor.apply(V.Rotor.between(V.Vector.xyz(1.0, 0.0, 0.0), V.Vector.xyz(0.0, 3.0, 4.0)), V.Vector.xyz(1.0, 0.0, 0.0))))
    IO.print(Bool.show(F32.is_lt(B.err(V.Rotor.log(V.Bivector.exp(bv())), bv()), 1.0e-6)))
    +r : K.Rotor<F32> = R(V.Bivector.exp(bv()))
    +h : K.Rotor<F32> = R(V.Rotor.sqrt(U.Normed{r}))
    IO.print(Bool.show(F32.is_lt(R.err(G.Rotor.gp.Rotor(h, h), r), 1.0e-6)))
    +d : K.Rotor<F32> = R(V.Rotor.renormalize_fast(U.Normed{G.Scalar.gp.Rotor(K.Scalar{1.001}, r)}))
    IO.print(Bool.show(F32.is_lt(F32.abs((V.Rotor.scalar(G.Rotor.gp.Rotor(d, G.Rotor.reverse(d))) - 1.0 : F32)), 1.0e-5)))
#|(0, 1, 0)
#|(0, 0.6, 0.8)
#|True
#|True
#|True
