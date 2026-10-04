# The generator's entry point: `bend gen/main.bend <out-dir>` writes
# <out-dir>/<algebra>/{kinds,ops,proofs}.bend for every algebra in
# gen/specs.bend. tools/regen.sh runs it.

import Base
import ./gen.bend as G
import ./specs.bend as Sp

def Gen.put.fin(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, res) = r
  File.close(f)

def Gen.put(path: String, text: String) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "w"))
    r : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, text)
    Gen.put.fin(r)

def Gen.emit(+dir: String, o: G.Out) -> IO(Unit):
  match o:
    case G.Out{k, p, f, s}:
      do IO<Unit>:
        r : U32 & (String & String) <- IO.try(U32 & (String & String), Process.run("mkdir", ["-p", dir], "", 4096, 10000))
        Gen.put(dir ++ "/kinds.bend", k)
        Gen.put(dir ++ "/ops.bend", p)
        Gen.put(dir ++ "/proofs.bend", f)
        IO.print(s)

def Gen.ops() -> List<&2, G.Op>:
  [G.OGp{}, G.OWedge{}, G.OVee{}]

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
    Gen.emit(out ++ "/pga3d", G.Gen.out(Sp.PGA3D(), Gen.ops()))
