# Q8: is a generator written in Bend practical? Blade products from U32
# bitmasks (reordering sign + diagonal metric), the full 16x16 PGA3D product
# printed as Bend source text, R times, written to a file. Timed per phase.
import Base

# popcount by a Nat fuel of 32 steps
def pop.go(n: Nat, x: U32, acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+k:
      +y = x
      pop.go(k, U32.shr(y), (acc + (y .&. 1 : U32) : U32))

def pop(x: U32) -> U32:
  pop.go(32n, x, 0)

# swaps to sort the factors of blade a * blade b: sum over shifts of popcount
def swaps.go(n: Nat, a: U32, +b: U32, acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+k:
      +a1 = U32.shr(a)
      swaps.go(k, a1, b, (acc + pop((a1 .&. b : U32)) : U32))

def word.pick(c: Bool, a: U32, b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

# PGA3D metric: bit 0 is e0 (squares to 0), bits 1..3 square to +1
def blade.coef(+a: U32, +b: U32) -> U32:
  +zero = U32.is_zero((a .&. b .&. 1 : U32))
  +odd = U32.is_even(swaps.go(4n, a, b, 0))
  word.pick(zero, word.pick(odd, 1, 2), 0)

def sign.str(pos: Bool) -> String:
  match pos:
    case True{}:
      "+"
    case False{}:
      "-"

def term.str(+a: U32, +b: U32, c: U32) -> String:
  sign.str(U32.is_eq(c, 1)) ++ " a" ++ U32.show(a) ++ "*b" ++ U32.show(b)

def term.put.if(+a: U32, +b: U32, k: U32, acc: String, z: Bool) -> String:
  match z:
    case True{}:
      acc
    case False{}:
      "c" ++ U32.show((a .^. b : U32)) ++ " " ++ term.str(a, b, k) ++ "\n" ++ acc

def term.put(+a: U32, +b: U32, +c: U32, acc: String) -> String:
  term.put.if(a, b, c, acc, U32.is_zero(c))

def row.go(n: Nat, +a: U32, b: U32, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+k:
      +bb = b
      row.go(k, a, (bb + 1 : U32), term.put(a, bb, blade.coef(a, bb), acc))

def table.go(n: Nat, a: U32, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+k:
      +aa = a
      table.go(k, (aa + 1 : U32), row.go(16n, aa, 0, acc))

def table() -> String:
  table.go(16n, 0, "")

def reps(n: Nat, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+k:
      reps(k, String.append(table(), acc))

def main() -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +s : String = reps(100n, "")
    +n : Nat = String.length(s)
    +t1 : Nat <- IO.now()
    IO.print("built " ++ Nat.show(n) ++ " chars in " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")
    f : File <- IO.try(File, File.open("build/q08_out.txt", "w"))
    r : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, s)
    +t2 : Nat <- IO.now()
    IO.print("wrote in " ++ Nat.show(Nat.sub(t2, t1)) ++ " ms")
    IO.print(String.take(table(), 120n))
