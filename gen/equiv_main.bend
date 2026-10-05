# The equivariance laws for every kind pair: `gen/equiv_main <out-dir>`
# writes <out-dir>/<algebra>/equiv_all.bend (gen/equiv.bend,
# Eq.module.all). tools/regen.sh builds it natively and runs it with an
# unlimited stack: its polynomials nest deeper than the interpreter's
# stack allows. CSTA has no equiv_all.bend: its vector laws ran 2.5 hours
# without finishing (ADR-013).

import Base
import ./gen.bend as G
import ./specs.bend as Sp
import ./equiv.bend as EQ

def Gen.put.fin(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, res) = r
  File.close(f)

def Gen.put(path: String, text: String) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "w"))
    r : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, text)
    Gen.put.fin(r)

# proofs_2.bend, proofs_3.bend, ...
def Gen.more(+dir: String, ms: List<&2, String>, +i: Nat) -> IO(Unit):
  match ms:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case m <> t:
      do IO<Unit>:
        Gen.put(dir ++ "/proofs_" ++ Nat.show(i) ++ ".bend", m)
        Gen.more(dir, t, 1n+i)

def Gen.emit(+dir: String, o: G.Out) -> IO(Unit):
  match o:
    case G.Out{k, p, f, ms, a, e, l, t, x, c, s}:
      do IO<Unit>:
        r : U32 & (String & String) <- IO.try(U32 & (String & String), Process.run("mkdir", ["-p", dir], "", 4096, 10000))
        Gen.put(dir ++ "/kinds.bend", k)
        Gen.put(dir ++ "/ops.bend", p)
        Gen.put(dir ++ "/proofs.bend", f)
        Gen.more(dir, ms, 2n)
        Gen.put(dir ++ "/f32.bend", a)
        Gen.put(dir ++ "/err.bend", e)
        Gen.put(dir ++ "/lin.bend", l)
        Gen.put(dir ++ "/track.bend", t)
        Gen.put(dir ++ "/approx.bend", x)
        Gen.put(dir ++ "/cr.bend", c)
        IO.print(s)

def Gen.ops() -> List<&2, G.Op>:
  [G.OGp{}, G.OWedge{}, G.OVee{}, G.OLc{}, G.ORc{}, G.ODot{}, G.OScalar{}, G.OAdd{}, G.OSub{}]

def Gen.unary() -> List<&2, G.Op1>:
  [G.ONeg{}, G.ORev{}, G.OInv{}, G.OConj{}, G.ODual{}, G.OUndual{}]

def Gen.outdir.go(args: List<String>) -> String:
  match args:
    case Nil{}:
      "algebras"
    case d <> rest:
      d

def Gen.outdir(args: List<String>) -> String:
  match args:
    case Nil{}:
      "algebras"
    case p <> rest:
      Gen.outdir.go(rest)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +out : String = Gen.outdir(args)
    Gen.put(out ++ "/vga2d/equiv_all.bend", EQ.Eq.module.all(Sp.VGA2D(), ["Rotor", "Vector"]))
    Gen.put(out ++ "/vga3d/equiv_all.bend", EQ.Eq.module.all(Sp.VGA3D(), ["Rotor", "Odd"]))
    Gen.put(out ++ "/pga2d/equiv_all.bend", EQ.Eq.module.all(Sp.PGA2D(), ["Motor", "Flector"]))
    Gen.put(out ++ "/pga3d/equiv_all.bend", EQ.Eq.module.all(Sp.PGA3D(), ["Motor", "Flector"]))
    Gen.put(out ++ "/sta/equiv_all.bend", EQ.Eq.module.all(Sp.STA(), ["Even", "Odd"]))
    Gen.put(out ++ "/stap/equiv_all.bend", EQ.Eq.module.all(Sp.STAP(), ["Vector"]))
    Gen.put(out ++ "/cga3d/equiv_all.bend", EQ.Eq.module.all(Sp.CGA3D(), ["Vector"]))
