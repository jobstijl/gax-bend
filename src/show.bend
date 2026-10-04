# Printing multivectors as sums of basis blades, for tests and debugging.
# Generator i of the tree is printed as e<base+i>, so PGA (e0 first) passes
# base 0 and VGA (e1 first) passes base 1.

import Base
import ./spec.bend as S

# digits of the generators, ids listing them last first
def Show.digits(ids: List<&2, Nat>, acc: String) -> String:
  match ids:
    case Nil{}:
      acc
    case i <> rest:
      Show.digits(rest, Nat.show(i) ++ acc)

def Show.blade(ids: List<&2, Nat>) -> String:
  match ids:
    case Nil{}:
      "1"
    case i <> rest:
      "e" ++ Show.digits(i <> rest, "")

# the nonzero coefficients of x as "coef*blade" strings, in tree order;
# ids lists the e-parts taken so far, the last one first
def Show.terms(~T: Data, ~show: T -> String, +d: Nat, +g: Nat, +ids: List<&2, Nat>, x: S.MV(T, d)) -> List<&2, String>:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          Nil{}
        case S.L{a}:
          [show(a) ++ "*" ++ Show.blade(ids)]
    case 1n+p:
      match x:
        case S.NZ{}:
          Nil{}
        case S.N{x1, x2}:
          List.append(&2, String, Show.terms(~T, ~show, p, 1n+g, g <> ids, x1), Show.terms(~T, ~show, p, 1n+g, ids, x2))

def Show.mv.join(ts: List<&2, String>) -> String:
  match ts:
    case Nil{}:
      "0"
    case t <> rest:
      String.join(t <> rest, " + ")

def Show.mv(~T: Data, ~show: T -> String, d: Nat, base: Nat, x: S.MV(T, d)) -> String:
  Show.mv.join(Show.terms(~T, ~show, d, base, Nil{}, x))
