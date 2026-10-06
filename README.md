# gax-bend

A geometric algebra library for [Bend 2](https://github.com/bendlang/bend):
fast on Bend's CPU and GPU backends, with its algebra proven in Bend's own
type theory instead of tested. gax ([github.com/jobstijl/gax](https://github.com/jobstijl/gax))
is the semantic reference.

New here? [docs/guide.md](docs/guide.md) covers using the library, what is
proven and trusted, the gate, and extending it with algebras, laws and
proofs.

## Status

| layer | what | state |
|---|---|---|
| S, the spec | a multivector tree over any dimension, any diagonal signature, any scalar ring | **24 laws proven** ([docs/laws.md](docs/laws.md)); `LAWS.bend` approved |
| K, kernels | flat per-kind records with straight-line kernels, each proven equal to the spec | **generated** for VGA2D, VGA3D, PGA2D, PGA3D, STA, STAP, CGA3D and CSTA (the last two in gax's null basis, through a proven change of basis): 7547 kernels, all proven (CSTA's in 1.6 h with `--csta`; `algebras/`), each proven linear in every operand it is linear in (gax family B: 22 806 laws, `algebras/*/lin.bend`), and equivariant under versors in all eight algebras (gax family D: 552 laws for every kind pair, `algebras/*/equiv_all.bend`, and 16 curated ones, `algebras/*/equiv.bend`) |
| A, the API | PGA2D/3D, VGA3D, CGA3D, STA with geometric nouns and batch APIs | PGA3D (`api/pga3d.bend`): constructors, exp/log, normalize, sqrt, motions between elements; CGA3D (`api/cga3d.bend`): points, spheres, planes, motions; VGA3D rotors and PGA2D motions (`api/vga3d.bend`, `api/pga2d.bend`); STA (`api/sta.bend`): the Lorentz group, with boosts, rotations, and exp/log through complex Study numbers (`api/cx.bend`) |
| rounding error | one theorem for every term, with and without underflow, and per kernel a law that each output is within h(k)·(kernel on \|inputs\|) of exact | **proven** (`proofs/err.bend`, `algebras/*/err.bend`: 7189 kernel laws and 7189 with underflow, all checked); F32 measured within the bound ([docs/numerics.md](docs/numerics.md)); a proven run-time bound from computed quantities (`Err.track`, `api/track.bend`), per kernel too (7189 tracked laws, `algebras/*/track.bend`); bounds that compose through chains of kernels on approximate inputs (7189 laws, `algebras/*/approx.bend`); every kernel correctly rounded when run on big dyadics (7189 laws, `algebras/*/cr.bend`, `src/cr.bend`) |
| numbers | exact `Int` and dyadic rationals, both proven ordered commutative rings (`proofs/int.bend`, `proofs/dyadic.bend`); double-F32 (`num/df32.bend`), Fast2Sum, TwoSum and Veltkamp's split proven exact in every binary format, Dekker's product at every precision from 4 bits, binary32 and binary64 included, barring underflow (`proofs/eft.bend`, `proofs/eft2.bend`, `proofs/eft3.bend`: with nearest-ness, Sterbenz and the representable rounding error), the double-word bounds proven for p ≥ 6: DWTimesDW's 5u² with ties to even (`proofs/dw.bend`) and AccurateDWPlusDW's 3u²/(1 − 4u) (`proofs/dwadd.bend`), and checked exactly on 20 000 pairs (`tests/df32_exact.bend`); rounding to p bits, truncating or to nearest (ties to even, ε = 2^−p), proven to meet the rounding model, so the error theorems hold outright for p-bit arithmetic (`proofs/round.bend`); binary32 rounding with gradual underflow, proven to meet the model with η = 2⁻¹⁵⁰, run by a fast spec proven equal to it (`proofs/fast.bend`) and matched bit for bit by native F32 on 146 829 sampled operations (`tests/f32_native.bend`); big naturals and dyadics on 24-bit limbs, every operation proven to compute its value (`proofs/big.bend`), giving binary32 and binary64 (SoftF64) at any operand size, proven equal to the rounding spec and matched bit for bit against native F32 and Python doubles, and an exact dot-product accumulator that rounds once (`tests/big_f32.bend`, `tests/big_f64.bend`); b-posits with their quire, proven to meet the rounding model with u = 2^−p0 and η = minpos, the run-time version proven equal to the spec, the bit patterns proven (every pattern decodes to its value and encodes back) and the rounding proven to be the standard's bit-string rounding (`proofs/posit.bend` to `proofs/posit5.bend`), and matched against an independent reference (`tests/bposit.bend`) | Phase 3 |

The Phase 0 measurements behind the design (checker cost, kernel speed
against C, GPU) are in [docs/bend-facts.md](docs/bend-facts.md), and the
decisions in [docs/design.md](docs/design.md).

## Running it

```sh
. tools/env.sh          # bend 2.0.35 and the project's clang on PATH
tools/gate.sh           # proofs, generated kernels and their error laws, example tests, negative controls (CGA3D's proofs skipped; about 10 min)
tools/gate.sh --full    # also CGA3D's kernel proofs and every equivariance file (about 1.5 hours)
tools/gate.sh --csta    # also CSTA's (1.6 hours)
tools/regen.sh          # regenerate algebras/ from gen/specs.bend (--check: compare)
bend tests/spec_pga3d.bend
```

`tools/gate.sh` passes only when:
- `bend PROOF.bend` prints ALL PROOFS CHECK;
- `algebras/` and the generated `proofs/` modules are what the generators
  write (`tools/regen.sh --check`);
- every `algebras/*/proofs.bend` and `algebras/*/f32.bend` checks;
- every `tests/*.bend` and `examples/*.bend` prints the `#|` lines it ends with;
- every negative control in `tests/neg/` fails.

## Using it

`examples/motion.bend` (checked by the gate), PGA3D at F32:

```bend
# A quarter turn about the x axis, then a translation by 2 along z, applied
# to the point (0, 1, 0): it lands on (0, 0, 3).
import Base
import ../api/pga3d.bend as P
import ../api/normed.bend as U
import ../algebras/pga3d/kinds.bend as K
import ../algebras/pga3d/f32.bend as G

def x_axis() -> K.Line<F32>:
  G.Point.vee.Point(P.Point.xyz(0.0, 0.0, 0.0), P.Point.xyz(1.0, 0.0, 0.0))

def moved(p: K.Point<F32>) -> K.Point<F32>:
  +m = P.Motor.then(P.Motor.rotation(x_axis(), (F32.pi() * 0.5 : F32)), P.Motor.translation(0.0, 0.0, 2.0))
  G.Motor.transform.Point(U.Normed.get(K.Motor<F32>, m), p)

def r4(x: F32) -> String:
  F32.show((F32.round((x * 10000.0 : F32)) / 10000.0 : F32))

def Point.show(p: K.Point<F32>) -> String:
  match p:
    case K.Point{x, y, z, +w}:
      "(" ++ r4((x / w : F32)) ++ ", " ++ r4((y / w : F32)) ++ ", " ++ r4((z / w : F32)) ++ ")"

def main() -> IO(Unit):
  IO.print(Point.show(moved(P.Point.xyz(0.0, 1.0, 0.0))))
```

The kinds module (`K`) holds the geometric nouns (`Point`, `Line`,
`Plane`, `Motor`, ...). Every product is a generated kernel named by its
operands (`G.Point.vee.Point`, `G.Motor.transform.Point`,
`G.Line.lc.Plane`), so a product that does not exist is a missing name. The
API (`P`) adds the constructors and numerics.

## Demo

`demos/raytrace.bend` ray-traces three balls on a floor in CGA3D: each ray
is the line through the eye and a pixel's point, meets a sphere in a point
pair and the floor in a flat point, and is shaded by a dot product of
directions, with shadow rays. It renders into Bend's quadtree `Image`, one
fork per quadrant, and writes a PPM:

```sh
bend demos/raytrace.bend -o build/rt && build/rt build/raytrace.ppm   # 256x256, ~30 ms
```

![raytrace](demos/raytrace.png)

What the library gained so that the demo needs no raw square roots or
coordinate arithmetic is in [docs/friction.md](docs/friction.md).
`tests/raytrace_pixels.bend` checks four of its pixels.

GPU runs use the upstream `hip` branch: `. tools/env-hip.sh`, then `bend-hip`.
See bend-facts, "Pins".

## Layout

```
LAWS.bend         the laws (owned by the human once approved)
PROOF.bend        fills every law; the gate
src/spec.bend     Layer S: MV(T, d), Sig(d), products, signs, complements, grades
src/ring.bend     the ring laws a theorem may assume
src/int.bend      exact integers
src/dyadic.bend   dyadic rationals, one spelling per value
src/round.bend    rounding a dyadic to p significant bits
src/fast.bend     the same rounding on native Nat operations (proofs/fast.bend: equal)
src/big.bend      big naturals and dyadics on limbs: binary32, binary64, exact dot products
src/posit.bend    b-posits: rounding, bit patterns, the quire
src/dual.bend     dual numbers: linear maps and derivatives from any kernel (ADR-006)
src/show.bend     printing multivectors as blade sums
src/expr.bend     the symbolic ring the generator runs Layer S on
src/err.bend      the rounding-error model: computed operations, absev, k, h
num/              number types (double-F32)
gen/              the kernel generator (Bend): specs, symbolic evaluation, printers
gen/proofs/       the proof writer (Bend): emits the large Layer-S proof modules
algebras/         generated: kinds, kernels, proofs, error laws, F32 module per algebra
api/              Layer A: per-algebra API at F32 (pga3d, pga2d, vga3d, cga3d, sta), Study functions, complex numbers, Normed
proofs/           the lemmas behind PROOF.bend (base, leaf, add, sgn by hand;
                  the rest generated by gen/proofs), and the Nat and Int laws
tests/            example tests (`#|` expected output) and negative controls
bench/            benchmarks (Bend against C) and rounding-error measurements
examples/         small programs using the API, checked by the gate
demos/            the CGA3D ray tracer (Phase 4 demo)
spikes/           Phase 0 experiments, kept as evidence for bend-facts
tools/            env, the 16 GB cap, the gate
docs/             the guide, facts, design (ADRs), laws, numerics, upstream notes
```

## Conventions

Basis, orientation and signs follow gax (ADR-009 there):
- PGA puts e0 first;
- the join sign is e123 ∨ e032 = +e23;
- `J_R` is the right complement, with a ∧ J_R(a) = I;
- the regressive product is J_L(J_R a ∧ J_R b).
