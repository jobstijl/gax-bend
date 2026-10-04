# The generator's entry point: `bend gen/main.bend <out-dir>` writes
# <out-dir>/<algebra>/{kinds,ops,proofs}.bend for every algebra in
# gen/specs.bend. tools/regen.sh runs it.

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
    case G.Out{k, p, f, ms, a, e, s}:
      do IO<Unit>:
        r : U32 & (String & String) <- IO.try(U32 & (String & String), Process.run("mkdir", ["-p", dir], "", 4096, 10000))
        Gen.put(dir ++ "/kinds.bend", k)
        Gen.put(dir ++ "/ops.bend", p)
        Gen.put(dir ++ "/proofs.bend", f)
        Gen.more(dir, ms, 2n)
        Gen.put(dir ++ "/f32.bend", a)
        Gen.put(dir ++ "/err.bend", e)
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
    Gen.emit(out ++ "/vga2d", G.Gen.out(Sp.VGA2D(), Gen.ops(), Gen.unary()))
    Gen.emit(out ++ "/vga3d", G.Gen.out(Sp.VGA3D(), Gen.ops(), Gen.unary()))
    Gen.emit(out ++ "/pga2d", G.Gen.out(Sp.PGA2D(), Gen.ops(), Gen.unary()))
    Gen.emit(out ++ "/pga3d", G.Gen.out(Sp.PGA3D(), Gen.ops(), Gen.unary()))
    Gen.emit(out ++ "/sta", G.Gen.out(Sp.STA(), Gen.ops(), Gen.unary()))
    Gen.emit(out ++ "/cga3d", G.Gen.out(Sp.CGA3D(), Gen.ops(), Gen.unary()))
    Gen.emit(out ++ "/stap", G.Gen.out(Sp.STAP(), Gen.ops(), Gen.unary()))
    Gen.emit(out ++ "/csta", G.Gen.out(Sp.CSTA(), Gen.ops(), Gen.unary()))
    Gen.put(out ++ "/pga3d/equiv.bend", EQ.Eq.module(Sp.PGA3D(), EQ.laws.pga3d()))
    Gen.put(out ++ "/vga3d/equiv.bend", EQ.Eq.module(Sp.VGA3D(), EQ.laws.vga3d()))
    Gen.put(out ++ "/pga2d/equiv.bend", EQ.Eq.module(Sp.PGA2D(), EQ.laws.pga2d()))
    Gen.put(out ++ "/sta/equiv.bend", EQ.Eq.module(Sp.STA(), EQ.laws.sta()))
