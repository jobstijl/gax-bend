# Q9 GPU column: SoftF32 vs native F32 mul+add, 2^14 balanced leaves, each a
# dependent chain of 2^12 steps; the leaf sums are added in tree order.
import Base
import ../spikes/q09_softf32.bend as S

def soft.tree(+d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      S.soft.loop(4096n, (i * 2654435761 + 1 : U32), 0)
    case 1n+k:
      a b = soft.tree(k, (i * 2 : U32)) soft.tree(k, (i * 2 + 1 : U32))
      S.SoftF32.add(a, b)

def native.tree(+d: Nat, +i: U32) -> F32:
  match d:
    case 0n:
      S.native.loop(4096n, (i * 2654435761 + 1 : U32), 0.0)
    case 1n+k:
      a b = native.tree(k, (i * 2 : U32)) native.tree(k, (i * 2 + 1 : U32))
      F32.add(a, b)

def run.soft(+d: Nat, +k: U32) -> U32:
  soft.tree!(d, k)

def run.native(+d: Nat, +k: U32) -> F32:
  native.tree!(d, k)

def main() -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +k : U32 = U32.and(U32.from_nat(t0), 1)
    +s : U32 = run.soft(14n, k)
    +t1 : Nat <- IO.now()
    +f : F32 = run.native(14n, k)
    +t2 : Nat <- IO.now()
    IO.print("2^26 mul+add, bang: soft " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms, native " ++ Nat.show(Nat.sub(t2, t1)) ++ " ms; same bits: " ++ Bool.show(U32.is_eq(s, F32.bits(f))))
