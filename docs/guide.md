# The gax-bend guide

This guide is for two readers: people writing programs with gax-bend, and
people extending it with new algebras, laws or proofs. It explains how the
pieces fit together and points to the file where each claim is checked. The
other documents go deeper:
- [laws.md](laws.md) lists every law and its evidence;
- [design.md](design.md) holds the decisions (ADRs);
- [numerics.md](numerics.md) covers rounding error;
- [bend-facts.md](bend-facts.md) has the measurements and the Bend idioms.

Contents:
1. [What gax-bend is](#1-what-gax-bend-is)
2. [Setting up](#2-setting-up)
3. [A first program](#3-a-first-program)
4. [Algebras, kinds and kernels](#4-algebras-kinds-and-kernels)
5. [The API, algebra by algebra](#5-the-api-algebra-by-algebra)
6. [Number types](#6-number-types)
7. [Rounding error](#7-rounding-error)
8. [What is proven, and what is trusted](#8-what-is-proven-and-what-is-trusted)
9. [Checking: the gate and the generators](#9-checking-the-gate-and-the-generators)
10. [Extending gax-bend](#10-extending-gax-bend)
11. [Writing proofs](#11-writing-proofs)
12. [Known limits, and how the equivariance generator decides](#12-known-limits-and-how-the-equivariance-generator-decides)
13. [Troubleshooting](#13-troubleshooting)

## 1. What gax-bend is

gax-bend is a geometric algebra library for Bend 2. Its semantics follow
[gax](https://github.com/jobstijl/gax), and its algebra is proven in Bend's
type theory rather than tested. It has three layers (ADR-001):

| layer | where | what it is |
|---|---|---|
| S, the spec | `src/spec.bend` | One multivector tree `MV(T, d)` over any dimension, any diagonal signature and any scalar ring, with every product defined once. The laws are proven here. |
| K, kernels | `algebras/<name>/` | Flat records per kind (`Point`, `Motor`, ...) and straight-line kernels per product and kind pair. A generator writes them, and each one is proven equal to the spec. |
| A, the API | `api/` | Geometric nouns and numerics at F32: constructors, exp and log, normalization, motions between elements. |

Correctness flows downward. A law is proven once on the spec. Each kernel
is proven equal to the spec, so the law holds for the kernels as well. The
API is built from kernels.

## 2. Setting up

```sh
. tools/env.sh           # bend 2.0.35 and the project's clang on PATH, telemetry off
bend examples/motion.bend          # run a file (interpreted, after checking)
bend file.bend --check-only        # check proofs only; prints ALL PROOFS CHECK or SOME PROOFS FAIL
bend file.bend -o build/x && build/x   # native build
```

- **Versions are pinned** in [bend-facts.md, "Pins and machine"](bend-facts.md#pins-and-machine).
- **GPU** runs use the upstream `hip` branch: `. tools/env-hip.sh`, then
  `bend-hip`. That branch is Bend 2.0.24, so not every file builds there.
- **Heavy jobs run under a memory cap**: `tools/cap.sh <command>` runs the
  command with 16 GB and no swap. The gate uses it for every file. Some
  checks (CGA3D's and CSTA's kernel proofs, STA's equivariance laws) take
  several GB and minutes to hours, so run them one at a time.
- **Deep recursion**: a native build whose recursion is deep needs
  `ulimit -s unlimited`. The equivariance generator does
  (`tools/regen.sh`).

## 3. A first program

[`examples/motion.bend`](../examples/motion.bend), checked by the gate:

```bend
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
```

Four imports do the work:

| alias | module | gives |
|---|---|---|
| `K` | `algebras/pga3d/kinds.bend` | the kinds: `K.Point<T>`, `K.Line<T>`, `K.Motor<T>`, ... |
| `G` | `algebras/pga3d/f32.bend` | every kernel at F32 |
| `P` | `api/pga3d.bend` | constructors and numerics |
| `U` | `api/normed.bend` | `Normed<A>`, a versor certified to have v ṽ = 1 |

The join of two points is a line: `G.Point.vee.Point`. The program builds
two motors and composes them with `Motor.then`, which applies its first
argument first. The point is moved by the sandwich kernel
`G.Motor.transform.Point`.

## 4. Algebras, kinds and kernels

### The algebras

| algebra | signature | kinds | API |
|---|---|---|---|
| VGA2D | R(2,0) | Scalar, Vector, Pseudoscalar, Rotor, Multivector | none |
| VGA3D | R(3,0) | Scalar, Vector, Bivector, Pseudoscalar, Paravector, Rotor, Odd, Multivector | `api/vga3d.bend` |
| PGA2D | R(2,0,1), e0 first | Scalar, Line, Point, Direction, Pseudoscalar, Rotor, Translator, Motor, Flector, Multivector | `api/pga2d.bend` |
| PGA3D | R(3,0,1), e0 first | Scalar, Plane, Line, Point, Direction, Pseudoscalar, Rotor, Translator, Motor, Flector, Multivector | `api/pga3d.bend` |
| STA | R(1,3), e0² = 1 | Scalar, Vector, Bivector, Trivector, Pseudoscalar, Phasor, Even, Odd, Multivector | `api/sta.bend` |
| STAP | R(3,1,1), e0 degenerate, e4 time | Scalar, Vector, Bivector, Trivector, Quadvector, Pseudoscalar, Motor, Odd, Multivector | none |
| CGA3D | R(4,1) in the null basis e1 e2 e3 eo ei | Scalar, Vector, Twist, Bivector, Trivector, Quadvector, Pseudoscalar, Motor, Even, Odd, Multivector | `api/cga3d.bend` |
| CSTA | R(4,2) in the null basis e1 e2 e3 e4 eo ei | Scalar to Pseudoscalar by grade (Twist, Quintvector included), Motor, Even, Odd, Multivector | none |

The source of each algebra is a `GSpec` in
[`gen/specs.bend`](../gen/specs.bend). It is the content of gax's `.gax`
file for that algebra.

Conventions follow gax:
- PGA puts e0 first, and the join sign is e123 ∨ e032 = +e23;
- `J_R` is the right complement, with a ∧ J_R(a) = I, and the regressive
  product is J_L(J_R a ∧ J_R b);
- in the null-basis algebras eo · ei = −1, and a point is
  x + (x²/2) ei + eo.

`tests/spec_pga3d.bend` checks the PGA conventions, and
`tests/cga3d_dual.bend` checks CGA3D against gax's generated code.

### Kinds

A kind is a record with one field per blade, generic in its scalar type:

```bend
type Point<-T: Data> is Data:
  Point{e032: T, e013: T, e021: T, e123: T}
```

Fields are named after their blades in the orientation gax writes them, so
`e032` is stored with that sign. Every kind comes with a set of helpers:

| helper | what it does |
|---|---|
| `X.tree` and `X.of_tree` | convert to and from the spec's tree |
| `X.fields` | the coefficients as a list |
| `X.map` | apply a function to every coefficient |
| `X.<field>` | a getter for each field, such as `K.Even.s` |

### Kernels

Every product of two kinds is a kernel named `A.op.B`. A product that does
not exist is a missing name, so it fails at compile time rather than at
run time.

**Binary operations:**

| name | product |
|---|---|
| `gp` | geometric product |
| `wedge` | outer product (∧) |
| `vee` | regressive product (∨) |
| `lc` and `rc` | left and right contraction |
| `dot` | dot product |
| `scalar_product` | scalar product |
| `commutator` and `anticommutator` | gax's halved forms (xy − yx)/2 and (xy + yx)/2; Layer S defines the doubled forms, so no ring needs ½ |
| `add` and `sub` | sum and difference |

**Sandwiches:**
- `V.transform.X(v, x)` computes v x ṽ, the versor applied to x.
- For applying one versor to many elements, `V.prepare.X(v)` builds the
  map as a matrix once, and `V.X.apply(map, x)` applies it.

**Unary operations:** `neg`, `reverse`, `involute`, `conjugate`, `dual`
(J_R) and `undual` (J_L).

**Result kinds.** The generator chooses each result kind by gax's rule:
the smallest kind that holds the product's support. Usually that is the
kind you would expect. Sometimes it is wider: `Scalar.gp.Direction` returns
a `Point`, and `Plane.gp.Line` returns a `Flector`. The signature in
`f32.bend` states each result kind.

**Two modules per algebra hold the kernels:**
- **`ops.bend`** has every kernel generic over a ring:
  `O.Motor.gp.Motor(~T, ~zero, ~add, ~mul, ~neg, a, b)`.
- **`f32.bend`** instantiates each one at F32:
  `G.Motor.gp.Motor(a, b)`.

To run a kernel on another number type, call the `ops.bend` version with
that type's operations. Section 6 shows which types are available.

## 5. The API, algebra by algebra

All API functions work at F32. **Normed versors:**
- Versors that the API builds are `U.Normed<K.Motor<F32>>` (or `Rotor`,
  `Even`), certified to satisfy v ṽ = 1 (`api/normed.bend`).
- `U.Normed.get(K.Motor<F32>, m)` unwraps one for use with the kernels.
- `then(u, w)` means first u, then w.
- Rounding makes a long product of unit versors drift away from 1. Call
  `normalized`, or the cheaper `renormalize_fast`, now and then.

**PGA3D** (`api/pga3d.bend`):

| area | functions |
|---|---|
| constructors | `Point.xyz`, `Point.direction`, `Plane.abcd` |
| simple motors | `Motor.identity`, `Motor.translation(dx, dy, dz)`, `Motor.rotation(axis: Line, angle)` |
| combining motors | `Motor.then`, `Motor.inverse`, `Motor.sqrt` |
| exp and log | `Line.exp(bivector)` gives a motor; `Motor.log(motor)` gives a line |
| motions between elements | `Motor.between.points`, `Motor.between.lines`, `Motor.between.planes` |
| normalization | `Motor.normalized`, `Line.normalized`, `Motor.renormalize_fast` |

Normalization works on the Study number (a + b I) of m m̃. The laws of this
API are in [laws.md, "The PGA3D API"](laws.md).

**PGA2D** (`api/pga2d.bend`):

| area | functions |
|---|---|
| constructors | `Point.xy`, `Line.abc` |
| motors | `Motor.translation`, `Motor.rotation(centre: Point, angle)` |
| exp and log | `Point.exp`, `Motor.log` |
| other | `Motor.sqrt`, `Motor.between.points`, `Motor.between.lines`, `Motor.then`, `Motor.apply` |

**VGA3D** (`api/vga3d.bend`):

| area | functions |
|---|---|
| constructors | `Vector.xyz` |
| rotors | `Rotor.rotation(x, y, z, angle)`, `Rotor.between(a, b)`, `Rotor.sqrt` |
| exp and log | `Bivector.exp`, `Rotor.log` |
| other | `Rotor.then`, `Rotor.apply` |

**CGA3D** (`api/cga3d.bend`):

| area | functions |
|---|---|
| objects | `Point.xyz`, `Sphere.at(x, y, z, r)`, `Plane.normal(n, d)`, `eo`, `ei` |
| lines and intersections | `Line.through(p, q)`, `Line.meet(sphere, line)` (a point pair) |
| point pairs and centres | `PointPair.real`, `PointPair.points`, `FlatPoint.point`, `Sphere.center` |
| directions | `Direction.xyz`, `Direction.dot`, `Direction.unit`, `Direction.between`, `Direction.scaled`, `Motor.along`, `Point.moved` |
| motors | `Motor.translation`, `Motor.rotation`, `Motor.then`, `Motor.apply` |
| other | `Point.distance2` |

The ray tracer in `demos/raytrace.bend` uses all of these.
[friction.md](friction.md) records what the API gained so that the ray
tracer needs no raw coordinate arithmetic.

**STA** (`api/sta.bend`), the Lorentz group:

| area | functions |
|---|---|
| events | `Event.txyz` |
| rotors | `Rotor.boost(n, φ)`, `Rotor.rotation(n, angle)`, `Rotor.then`, `Rotor.inverse`, `Rotor.apply` |
| exp and log | `Bivector.exp`, `Rotor.log` |
| other | `Rotor.normalized`, `Vector.square` |

A bivector in STA squares to a complex number (scalar + I·scalar). Its exp
and log therefore go through the complex Study functions in
`api/cx.bend`.

**The Study functions** in `api/study.bend` are shared by exp, log and sqrt
in every algebra. They are C(s) = cosh√s, S(s) = sinh√s/√s, and their
relatives. Near zero they switch to series.

## 6. Number types

The kernels in `ops.bend` take any ring, so the same kernel runs on any of
the following types:

| type | module | use it for | proven |
|---|---|---|---|
| `F32` | native | speed | F32 is axiomatic in Bend; its error is bounded through the rounding model (section 7) |
| `I.Int` | `src/int.bend` | exact tests | ordered commutative ring (`proofs/int.bend`) |
| `D.Dy` (dyadic rationals) | `src/dyadic.bend` | exact values of binary floats | ordered commutative ring (`proofs/dyadic.bend`) |
| `B.Bd` (big dyadics on 24-bit limbs) | `src/big.bend` | binary32, binary64 (SoftF64) and exact dot products at any size | every operation computes its value (`proofs/big.bend`); bit for bit against native F32 (`tests/big_f32.bend`) and Python doubles (`tests/big_f64.bend`) |
| b-posits and their quire | `src/posit.bend` | posit arithmetic | rounding model, bit patterns, the standard's rounding (`proofs/posit*.bend`, `tests/bposit.bend`) |
| `DF` (double-F32) | `num/df32.bend` | about 48 bits of precision on F32 hardware | see below |
| `DU.Dual<T>` | `src/dual.bend` | derivatives and linear maps of any kernel | commutative ring (`proofs/dual.bend`) |

**Double-F32** has Fast2Sum, TwoSum, Veltkamp's split and Dekker's
product, all proven exact. Its double-word operations have proven bounds
for p ≥ 6:

| operation | proven bound | proof |
|---|---|---|
| `DF.mul` (DWTimesDW) | 5u² with ties to even | `proofs/dw.bend` |
| `DF.add` (AccurateDWPlusDW) | 3u²/(1 − 4u) | `proofs/dwadd.bend` |

Both bounds hold barring underflow and overflow (ADR-009 to ADR-012).
`tests/df32_exact.bend` checks them exactly on 20 000 pairs.

**Dual numbers:** set ε on one input coordinate, and one run of a kernel
gives one column of its linear map (ADR-006). `tests/dual_map.bend`
recovers a motor's 4×4 matrix this way.

## 7. Rounding error

For the error bounds, see [numerics.md](numerics.md). In practice:

- **Every kernel has a proven bound.** Each output is within h(k) times the
  kernel run on |inputs|, where k is the kernel's depth and
  h(k) = k u/(1 − k u) (`proofs/err.bend`). Every kernel has the bound as
  its own law, both with and without underflow (`algebras/*/err.bend`).
- **The bound can be tracked at run time** from computed quantities only:
  - run the kernel a second time, on |inputs| with `neg` as the identity,
    to get Â;
  - then B = `Track.factor(k)` · Â bounds the error (`api/track.bend`,
    `algebras/*/track.bend`);
  - `tests/err_measure.bend` checks err/B ≤ 1 on sampled inputs.
- **Bounds compose through chains of kernels.** `Approx`
  (`src/approx.bend`, `algebras/*/approx.bend`) carries a value together
  with a bound on its distance from the exact value.
- **Correctly rounded results are available.** Run the kernel on big
  dyadics with `src/cr.bend` and round once per output. The result is
  proven to be the binary32 value nearest the exact one
  (`algebras/*/cr.bend`). `tests/cr_kernels.bend` shows how to call it.
- **Compensated kernels:** running a kernel in double-F32 gets close to
  correct rounding (6 of 4000 fields differ in `tests/cr_kernels.bend`),
  but it is not correctly rounded.

## 8. What is proven, and what is trusted

**Proven.** "Proven" means that Bend 2's checker accepts the file. The gate
requires every proof file to print `ALL PROOFS CHECK`. What is proven:
- **The algebraic laws:** 24 Layer-S laws in `LAWS.bend`, filled by
  `PROOF.bend`.
- **Every kernel's equality to the spec** (`algebras/*/proofs*.bend`).
- **Linearity:** each kernel is linear in every operand it is linear in
  (`lin.bend`).
- **Equivariance under versors** (`equiv.bend`, `equiv_all.bend`).
- **The rounding-error theorems** (section 7).
- **The number types' laws** (section 6).

**Trusted, and documented as trusted:**
- **Native F32 arithmetic** is axiomatic in Bend. A `∀` hypothesis about
  it has no model (upstream-notes item 2). The error theorems are
  therefore proven for any arithmetic that meets the rounding model.
  Bit-exact F32 rounding is proven for the spec (`proofs/fast.bend`), and
  native F32 is *tested* against it on 146 829 operations
  (`tests/f32_native.bend`).
- **`Normed` over F32** is a certificate that only the API's constructors
  issue (`api/normed.bend`), not a proof.

**Not trusted, because their output is checked:**
- the generators (`gen/`);
- the proof writer (`gen/proofs/`).

Their output is plain Bend that the gate checks, and the gate fails if the
committed files differ from what the generators write.

[laws.md](laws.md) lists every law with its proof and its check. The
negative controls in `tests/neg/` are deliberately wrong laws that must
fail to check. They show that the checker rejects, for example:
- a wrong sign;
- a wrong factor;
- a missing condition.

## 9. Checking: the gate and the generators

```sh
tools/gate.sh            # about 10 minutes
tools/gate.sh --full     # also CGA3D's kernel proofs and every equiv_all.bend (about 1.5 hours)
tools/gate.sh --csta     # also CSTA's kernel proofs (1.6 hours)
tools/gate.sh -q         # one line per failure
```

The gate passes only when all of the following hold:
1. `PROOF.bend` checks.
2. The generated files are what the generators write (`tools/regen.sh --check`).
3. Every generated proof file checks.
4. Every `tests/*.bend` and `examples/*.bend` prints exactly the `#|`
   lines at its end.
5. Every negative control fails.

Files the current tier skips are counted and reported as skipped.

**Regenerating.** Never edit generated files by hand: their headers say
"Do not edit".

```sh
tools/regen.sh                  # algebras/ and the generated proofs/, about 2 minutes
tools/regen.sh --check          # compare instead of writing
```

**Writing a test.** End the file with the expected output, one `#|` line
per printed line:

```bend
def main() -> IO(Unit):
  IO.print("hello")
#|hello
```

## 10. Extending gax-bend

### A new algebra

1. **Add a `GSpec` to [`gen/specs.bend`](../gen/specs.bend):**

   | field | content |
   |---|---|
   | name | the algebra's name |
   | prefix | the module prefix |
   | `d` | the dimension of the tree |
   | generator names | one per generator |
   | signature | one `S.Gen{S.QP{}}`, `S.Gen{S.QN{}}` or `S.Gen{S.QZ{}}` per generator, squaring to +1, −1 or 0 |
   | kinds | a list of `G.GKind{name, res, blades}` |
   | versors | the names of the versor kinds |
   | null basis | `G.NoNul{}`, or `G.Nul{p, m}` naming the e+ and e− generators |

   For each kind:
   - `blades` lists the blades in written order as lists of generator
     indices (e032 is `[0n, 3n, 2n]`);
   - `res` is `False` for kinds that must not be chosen as a result, like
     gax's `part` (PGA's `Direction`).

   A null-basis algebra runs its tree on e± and writes eo and ei as
   indices d and d + 1, as CGA3D and CSTA do.
2. **Add a `Gen.emit` line** for it to [`gen/main.bend`](../gen/main.bend).
   For equivariance laws for every kind pair, also add a line to
   [`gen/equiv_main.bend`](../gen/equiv_main.bend) naming its versor
   kinds.
3. **Run `tools/regen.sh`, then check the new files** one at a time with
   `tools/cap.sh bend algebras/<name>/proofs.bend`. Check the other
   generated files the same way. A 6-dimensional algebra's kernel proofs
   take hours (CSTA: 1.6 h), so add its directory to the slow tiers in
   `tools/gate.sh`.
4. **Add an exact test** over `I.Int` in `tests/`, in the style of
   `tests/cga3d.bend`. If gax has generated code for the algebra, compare
   against it, as `tests/cga3d_dual.bend` does.
5. **Write an API module in `api/`**, if the algebra needs geometric
   nouns.

### A new law

1. **State it.**
   - A law of the whole algebra is stated on Layer S. It goes into
     `LAWS.bend` (owned by the maintainer once approved) and is filled in
     `PROOF.bend`.
   - A family of per-kernel laws, such as linearity or equivariance, is
     generated: add an emitter to the generator, as `gen/equiv.bend` does.
2. **Add a negative control** to `tests/neg/`: a slightly wrong version
   that must fail.
3. **Add a row to [laws.md](laws.md)** naming the proof and the file that
   checks it.
4. **Record the decision.** A decision with costs gets an ADR in
   [design.md](design.md), with a status, a "What it costs" section and a
   "Measured, not adopted" section.

## 11. Writing proofs

**Ring identities by cancellation** (ADR-003). Most per-kernel laws are
polynomial identities in the coefficients. `Norm.eq` (`proofs/norm.bend`)
proves them for any commutative ring, given the ring laws as `~`
arguments:

```bend
NP.Norm.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn,
  [x, y], lhs_term, rhs_term, {==})
```

The two terms are `N.Tm` trees over the variable list. The checker
normalizes both sides and compares them. For laws with a condition, such
as m m̃ having no e0123 part, `Rel.eqs` (`proofs/equiv.bend`) takes the
remainder l with lhs = rhs + l·r together with the hypothesis r = 0.
`tests/int_ring.bend` is a small worked example.

**Integer models** of floating point. The error-free transformations and
the double-word bounds work on integers:
- binary values become A·2^e with integer A;
- rounding becomes the integer loop of `src/round.bend`;
- inequalities are stated as `E.Le`, and their polynomial steps are
  discharged by the normaliser over Nat and Int (`NatN.eq`, `NatN.z`).

`proofs/dw.bend` and `proofs/dwadd.bend` are the largest examples, and
[bend-facts.md, Q17 and Q18](bend-facts.md) collects the idioms.

**Bend 2 pitfalls** met in this project (more in bend-facts, "Language
facts"):

| situation | rule |
|---|---|
| `match` | Match only parameters and pattern variables, before any `let`, in binder order. To read a computed record, write a helper def that takes it as a parameter. |
| definition order | Define before use. There is no mutual recursion. |
| reuse | Reusing a value needs `+` on Data parameters, pattern fields (`case +x <> +t`, `case 1n+(+j)`) and lets. Annotate lets: `+k : Nat = 1n + n`. |
| function-typed hypotheses | They must be used linearly. Pass them on rather than calling them twice. |
| names | Import aliases share the namespace with parameters (a parameter `B` clashes with an alias `B.`). Name segments cannot be numbers (`NQ.1`) or contain primes. |
| rewriting | `%e : P` with `e : {a == b}` needs the goal to be `P[_ := b]`, and turns it into `P[_ := a]`. |
| `@unsafe` | Never use it to get past a failing proof. If Bend blocks, write a minimal reproduction and record it in [upstream-notes.md](upstream-notes.md). |
| weakening | Never weaken a law to make its proof pass. |

## 12. Known limits, and how the equivariance generator decides

**Known limits:**
- **Slow checks.** CGA3D's kernel proofs take about an hour and CSTA's 1.6
  hours, so the default gate skips both.
- **Kinds without equivariance laws** (ADR-013), because the sandwich
  takes them to another kind:
  - PGA's Direction becomes a Point;
  - PGA3D's scalar becomes a Motor;
  - STA's pseudoscalar under Even and Odd;
  - CGA3D's and CSTA's Twist under Vector.
- **Single-vector versors in STAP, CGA3D and CSTA.** Their equivariance
  laws take a single vector as the versor. `Equiv.compose` extends the
  laws to any product of vectors applied in turn. General Motor, Even and
  Odd elements are not covered: their m m̃ has several non-scalar parts,
  and the generator's reduction handles at most one condition.

### Deciding the sign by evaluation

Before writing an equivariance law, the generator (`gen/equiv.bend`)
decides its factor's sign, +‖m‖² or −‖m‖². In a null-basis algebra it
used to normalize both sides symbolically on the whole spec tree, with
h = ½ as a variable. At d = 6 (CSTA) that meant 64 blades of degree-6
polynomials in up to 46 variables. CGA3D took 26 minutes, and CSTA ran 2.5
hours without finishing.

The generator now evaluates both sides modulo the prime
Q = 16 777 213 (`Zq`), at two pseudo-random points, and takes the sign on
which both points agree. Nothing is lost by this:
- **An identity vanishes at every point**, so no law that the symbolic
  method would find is dropped.
- **A polynomial that is not identically zero** vanishes at a random point
  with probability at most degree/Q, about 5·10⁻⁷ for one point
  (Schwartz–Zippel).
- **The generator is not trusted.** A wrong sign gives a law that fails to
  check, never a false proof.

The result:
- CGA3D's file came out byte-identical to the symbolic one.
- Generation went from 26 minutes to under a second.
- CSTA's 119 laws generate in 2 s and check in 752 s.
- `tools/regen.sh` now always includes `equiv_all.bend`.

**Open paths:**
- The diagonal algebras still normalize symbolically. A law with a
  condition must print its quotient l, and the evaluation gives no l.
- **More versor kinds.** Taking general Motor, Even and Odd elements as
  versors in CGA3D and CSTA needs a reduction by several conditions.
- **Cheaper checks via bilinearity.** Each law is linear in a and in b,
  and the kernels are proven linear, so the law could be proven on pairs
  of basis blades only. That needs a generic lemma lifting it to all
  operands, which is not written yet. No check needs it so far.

## 13. Troubleshooting

| symptom | cause and fix |
|---|---|
| `SOME PROOFS FAIL` | Run `bend file.bend --check-only` and read the first error. For a generated file, regenerate before suspecting the proof. |
| stack overflow in a generator | Build natively and run with `ulimit -s unlimited` (`tools/regen.sh` does this for `gen/equiv_main.bend`). |
| a check is killed | It hit the 16 GB cap of `tools/cap.sh`. Check one heavy file at a time. |
| `a match cannot scrutinize a local binder` | Move the match into a helper def that takes the value as a parameter. |
| `a filled definition ...` on a call | The callee is defined below the caller. Move it up. |
| a benchmark runs in zero time | Its inputs were literals and got folded at compile time. Take a seed from `IO.now()`. |
| the gate says generated sources are stale | Run `tools/regen.sh` and commit the result together with the generator change. |
