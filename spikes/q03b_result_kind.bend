# Q3b: a result-kind function in signatures (VGA2D), a dispatcher over kind
# tags, and a missing product as a named empty type.
import Base

type K is Data:
  KS{}
  KV{}
  KB{}
  KR{}

type Scalar<-T: Data> is Data:
  Scalar{s: T}

type Vector<-T: Data> is Data:
  Vector{e1: T, e2: T}

type Bivector<-T: Data> is Data:
  Bivector{e12: T}

type Rotor<-T: Data> is Data:
  Rotor{s: T, e12: T}

def KT(k: K, T: Data) -> Data:
  match k:
    case KS{}:
      Scalar<T>
    case KV{}:
      Vector<T>
    case KB{}:
      Bivector<T>
    case KR{}:
      Rotor<T>

# the wedge's result kind; vector ^ bivector has empty support in 2D
type NoWedge.Vector.Bivector.grade3.exceeds.dim2 is Data:

def WedgeOk(a: K, b: K) -> Data:
  match a b:
    case KV{} KB{}:
      NoWedge.Vector.Bivector.grade3.exceeds.dim2
    case _ _:
      Unit

def WedgeK(a: K, b: K) -> K:
  match a b:
    case KV{} KV{}:
      KB{}
    case KS{} k:
      k
    case _ _:
      KS{}

def wedge.vv(~T: Data, ~sub: T -> T -> T, ~mul: T -> T -> T, a: KT(KV{}, T), b: KT(KV{}, T)) -> KT(WedgeK(KV{}, KV{}), T):
  match a b:
    case Vector{+a1, +a2} Vector{+b1, +b2}:
      Bivector{sub(mul(a1, b2), mul(a2, b1))}

def wedge.sv(~T: Data, ~mul: T -> T -> T, a: KT(KS{}, T), b: KT(KV{}, T)) -> KT(WedgeK(KS{}, KV{}), T):
  match a b:
    case Scalar{+s} Vector{b1, b2}:
      Vector{mul(s, b1), mul(s, b2)}

def wedge(~T: Data, ~zero: T, ~sub: T -> T -> T, ~mul: T -> T -> T, ka: K, kb: K, ok: WedgeOk(ka, kb),
  x: KT(ka, T), y: KT(kb, T)) -> KT(WedgeK(ka, kb), T):
  match ka kb:
    case KS{} KS{}:
      y
    case KS{} KV{}:
      wedge.sv(~T, ~mul, x, y)
    case KS{} KB{}:
      y
    case KS{} KR{}:
      y
    case KV{} KS{}:
      Scalar{zero}
    case KV{} KV{}:
      wedge.vv(~T, ~sub, ~mul, x, y)
    case KV{} KB{}:
      match ok:
    case KV{} KR{}:
      Scalar{zero}
    case KB{} KS{}:
      Scalar{zero}
    case KB{} KV{}:
      Scalar{zero}
    case KB{} KB{}:
      Scalar{zero}
    case KB{} KR{}:
      Scalar{zero}
    case KR{} KS{}:
      Scalar{zero}
    case KR{} KV{}:
      Scalar{zero}
    case KR{} KB{}:
      Scalar{zero}
    case KR{} KR{}:
      Scalar{zero}

def show.biv(w: Bivector<F32>) -> String:
  Bivector{c} = w
  F32.show(c)

def go(+t: F32) -> String:
  show.biv(wedge(~F32, ~0.0, ~F32.sub, ~F32.mul, KV{}, KV{}, Unit{}, Vector{t, 2.0}, Vector{3.0, t}))

def main() -> IO(Unit):
  do IO<Unit>:
    n : Nat <- IO.now()
    IO.print(go(U32.to_f32(U32.and(U32.from_nat(n), 7))))
