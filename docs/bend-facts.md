# Bend facts for gax-blend

Phase 0, measured on 2026-10-04. Each answer names the spike in `spikes/` (or
`bench/`) that shows it and quotes what it printed. Re-run any of them with
`. tools/env.sh && bend spikes/<file>.bend`. Heavy runs go through
`tools/cap.sh` (16 GB, no swap).

Bend changes almost daily. Every fact below holds for the pinned version only.
Re-check it before relying on it after an upgrade.

## Pins and machine

| what | value |
|---|---|
| Bend | `bend 2.0.35` (installer sha256 `63039d1a…722f`, linux-x64); repo commit `2bfc83fd` (2026-10-03), shallow clone in `.vendor/bend` |
| clang | 22.1.8. Arch `clang-22.1.8-1` unpacked in `.vendor/clang` (sha256 checked against pacman's sync db); the system `llvm-libs` 22.1.8 supplies libLLVM; wrapper `.vendor/bin/clang` |
| Lean (for `--verdict`) | **Removed 2026-10-04 at your request (no Lean on this PC).** `--verdict` needs Lean 4.34.0 to build its kernel; 4.33.0 cannot build `bendtt.lean`. The Q7 results were measured with 4.34.0 installed. Since then `--verdict` cannot run here, and the gate is bend2 alone |
| GPU lane | upstream `hip` branch (`bfcc9bd`, **Bend 2.0.24**, 147 commits behind main) in `.vendor/bend-hip`, run with Bun 1.4.2 (`.vendor/bun`, sha256 checked). ROCm 7.2.4 is unpacked from the Arch packages (sha256 checked against the pacman db) in `.vendor/rocm`, 7.1 GB. `. tools/env-hip.sh` provides `bend-hip` |
| JS lane | node is not installed. `-o x.js` output runs under `deno run -A x.cjs` |
| CPU | Ryzen 7 5800X, 8 cores / 16 threads, 62 GB, no swap |
| GPU | AMD RX 6900 XT (`gfx1030`, 80 CUs, as `rocminfo` reports it). Mainline Bend has no lane for it: Metal and CUDA only (WONTFIX #811). **The `hip` branch drives it** (row above). `!` numbers marked "CPU pool" came from mainline builds; those marked "HIP" came from `bend-hip` builds |
| disk | 105 GB free after removing the Rust `target/` build directories (keeping gax's `target/criterion`) and Lean 4.34; `.vendor` ≈ 7.6 GB |

`tools/env.sh` puts `bend` and the clang wrapper on PATH, sets `CC`, and turns telemetry off.

## Q1. Version

`spikes/q01_version.bend` checks, runs and builds natively (`bend ok: 42`).
`bend` picks the compiler from `$CC`, then `clang`, then any `clang-NN`. A CPU
build needs clang ≥ 14; a `!` build needs clang ≥ 19 plus CUDA at
`/usr/local/cuda` (main.ts `cc_find`, `cli_build`). Without CUDA, a `!`
program builds as a CPU program.

## Q2. One `~R: Ring` template, or separate operations?

**Use separate `~` operations.** A ring record is accepted, but it cannot be opened at compile time, and it costs closures at run time.

- **Record of closures** (`q02_ring.bend`, `dotR`): it typechecks and runs (`30`).
  - A `~R` cannot be matched or destructured in a template body:
    - `match r:` gives `expected : an annotated term (cannot infer)`;
    - `Ring{..} = {r : Ring<T>}` gives `a parameter or field scrutinee (a match cannot scrutinize a computed value: give it its own def)` (`q02c_ring_tproj.bend`).
  - Projections must therefore be runtime defs. The emitted C then builds closures (`term_clo(FID_F32R_C11…)`), calls `Ring.mul` as a segment and applies closures through `FID_CLO_APPLY` (`build/q02.c`).
- **Separate operations** `~add: T -> T -> T, ~mul: …` (`dotS`): zero overhead, whether the argument is a def name (`~F32.mul`) or a lambda.
  - Both compile to the same flat spin as the hand-written `dotH`: `f32_rewrap(f32_unbox(f32_rewrap(f32_unbox(a0) * f32_unbox(b0))) + …)`.
  - `f32_unbox` and `f32_rewrap` are union bit-casts.
- **One op-selector template** `~R: Op -> T -> T -> T`, filled with a def that matches an `Op` tag (`q02d_ring_selector.bend`): nearly free.
  - Bend's inliner folds the match for constant tags: both `R(Mul{}, …)` calls became direct multiplies.
  - What is left is an `INLINE` spin with a constant tag, which clang folds.
  - It is unwieldy for operations of different arity (`neg`, constants).
- Every closure is affine (callable once) and only `~` arguments may be used freely, so a bundle of laws can only travel as separate `~` proof arguments (see Q7).

## Q3. Type-level `MV(T, sig)` and result kinds

**Yes to both.**

- `q03_mv_tree.bend` defines `def MV(T: Data, sig: List<&2, Q>) -> Data` as a Fuchs–Théry tree:
  - `S<T>` at the leaves (`S0{}` or `S1{x}`);
  - `Lv<A>` at each level (`Z{}` or `N{e, r}`, meaning `e·x₁ + x₂`).
- It works as the parameter and result type of recursive live defs `MV.add` and `MV.gp`, with the involution as a flag and the sign as a flag.
- Matching on `sig` refines the types of `a` and `b`.
- The products come out right:
  ```
  (N{Z{}, N{S0{}, S1{1}}}, N{N{S1{1}, S0{}}, Z{}}, N{N{S1{4294967295}, S0{}}, Z{}}, N{Z{}, Z{}})
  ```
  That is e1e1 = 1, e1e2 = e12, e2e1 = −e12 and, in PGA, e0e0 = 0.
- **Normal forms are not canonical.** e0e0 is `N{Z{}, Z{}}`, not `Z{}`, and equality is intensional. Phase 1 must state laws through a canonicalising function or build trees with a collapsing smart constructor.
- **Result-kind functions** (`q03b_result_kind.bend`):
  - In `def wedge.vv(… a: KT(KV{}, T), b: KT(KV{}, T)) -> KT(WedgeK(KV{}, KV{}), T)`, the result type reduces to `Bivector<T>` both in the body and at call sites.
  - The dispatcher `wedge(…, ka: K, kb: K, ok: WedgeOk(ka, kb), x: KT(ka, T), y: KT(kb, T)) -> KT(WedgeK(ka, kb), T)` checks with a 16-arm match.
  - Called with literal tags, it **folds away completely**: the C calls the `vv` kernel's spin directly. No tag test or tag word survives, and the one-field record is unboxed.
- **Missing products are a type error with a reason** (`q03c_missing_product.bend`). The witness type is a named empty type:
  ```
  - expected : NoWedge.Vector.Bivector.grade3.exceeds.dim2
  - observed : Unit
  ```
  An empty `match ok:` closes that arm. A match takes only live arguments, so `ok` is a real parameter, but it folds to nothing.

## Q4. Checker cost

All times are wall times for the whole file under `tools/cap.sh`. "bend2" is the ordinary checker; "verdict" is `--verdict`, i.e. bend2 followed by the Lean-proven kernel. Neither overflowed the stack in any run.

**Mirror kernels.** `spikes/gen_q04.py` symbolically runs Layer S's `MV.gp` and emits the flat kernel term for term. The law
`Flat.tree(gp(x,y)) == MV.gp(tree x, tree y)` holds over an opaque `~add ~mul ~neg`, and the proof is `match x y` followed by `{==}`.

| signature | coefficients | multiplies | bend2 | verdict |
|---|---|---|---|---|
| `PP` (VGA2D) | 4 | 16 | 0.32 s ✓ | 0.27 s ✓ |
| `PPP` (VGA3D) | 8 | 64 | 0.28 s ✓ | 0.30 s ✓ |
| `ZPPP` (PGA3D, e0 first) | 16 | 192 | 0.32 s ✓ | 0.33 s ✓ |
| `PPPP` | 16 | 256 | 0.33 s ✓ | — |
| `PPPPN` | 32 | 1024 | 0.42 s ✓ | — |

**Reflective normaliser.** `spikes/q04b_poly.bend` is about 170 lines: `Int` as sign-magnitude over `Nat`, polynomials as sorted, merged term lists, every operation renormalising.
- It sorts and merges with a structural loop and non-recursive step helpers, so it needs no fuel and no mutual recursion.
- Check: `(x+y)(x−y)` gives `[x², −y²]`.
- `spikes/gen_q04c.py` runs the production `MV.gp` at `T = Poly` on three symbolic multivectors and decides `(ab)c == a(bc)` by `{==}`.

| signature | bend2 | verdict |
|---|---|---|
| `PP` | 0.42 s ✓ | 0.65 s ✓ |
| `PPP` | 1.06 s ✓ | 3.1 s ✓ |
| `ZPPP` | 5.6 s ✓ | **fails: `out of fuel`** (kernel limit 400 M steps, 5.7 s) |
| `PPPP` | 9.9 s ✓ | — |

This measures only the computation. The soundness theorem `eval(norm p) = eval(p)` is not written yet.

**Negative controls fail as they should:**
- `q04n_assoc_wrong_PPP.bend` claims `(ba)c == a(bc)`. It fails, printing the expected polynomial.
- `q04n_gp_mirror_flip_ZPPP.bend` drops one `neg(` from the kernel. It fails.

**Generic induction** (Q10 below) costs 0.25 s for bend2 plus verdict.

## Q5. Kernel speed: flat F32 records against C

`bench/q05_sandwich.{bend,c}` uses gax's drift-tolerant unit-motor→point sandwich (`pga3d.wgsl:7271`, 33 multiplies), with FMA expanded to mul+add. Motor and Point are flat F32 records. The work is 2²⁶ sandwiches: a balanced fork tree of 2¹⁴ leaves, each a flat loop over 2¹² points. C uses `-O3 -ffp-contract=off`, the same recursion and the same summation order.

| run | C | Bend |
|---|---|---|
| 1 thread | 0.414–0.447 s | 0.364–0.432 s |
| 16 threads | 65–80 ms (16 pthreads) | 59–71 ms (`--threads 16`) |
| `!`, CPU pool (mainline) | — | 67–70 ms |
| `!`, **HIP** (`bend-hip`) | — | **7 ms** |

At 2²⁸ sandwiches (`build/q05_d16.bend`):
- HIP `!` takes **7–8 ms**;
- the same binary on 16 CPU threads takes 202–238 ms; with `--gpu off` its `!` takes 211–227 ms;
- C on 16 threads takes 257 ms.

Every run gives the same bits (`0x528bb8ba`). The device is about 30× the 16-thread CPU here, and bit-identical to it. The timer has 1 ms resolution, so the device figure carries roughly ±1 ms.

- About 6.4 ns per sandwich on one thread. The 16-thread speedup is about 6× in both, since the machine has 8 physical cores.
- **The checksum is bit-identical:** C `0x518aaa64`, Bend `1368042084` (the same bits).
- The emitted C:
  - `leaf` is one flat spin;
  - the Motor travels unboxed as 8 `u32` registers;
  - user segments contain no `term_keep`, `ctr_take` or `rfc_seal`.

1M points (the size in the brief) runs in about 6 ms per thread, too short to time reliably, hence 2²⁶.

## Q6. Operator sugar on user types

**Yes** (`q06_ops.bend` prints `(Biv2{4294967294}, 11)`). The head of `T` in `(… : T)` is the namespace:
- `(a .^. b : Vec2)` calls `Vec2.xor(a, b)`;
- `.&.` calls `Vec2.and`;
- `.|.` calls `.or`;
- `>>` / `<<` call `.shrn` / `.shln`;
- `* / % + -` call `.mul .div .mod .add .sub`.

The result type is free; only the two arguments are passed. Consequences:
- The spellings would have to be the defs `Line.xor` (wedge), `Line.and` (vee) and `Motor.shrn` (the sandwich `>>`).
- `|` and `&` themselves are type formers, not available as operators.
- An operator reaches only a two-argument def, so it cannot reach a kind-indexed generic product that also needs `ka, kb`. It can reach a def on a sum type, or one inside a single kind.

## Q7. What `--verdict` accepts

**Accepted** (each printed ALL PROOFS CHECK under `--verdict`):
- templates with `~` operations and type-level defs (`q03_mv_tree`);
- the mirror laws (Q4);
- small normaliser instances (Q4);
- a law with a `~comm` hypothesis (`q07a`);
- point equations passed as `+h` (`q07c`, `q09c`);
- **a Layer-S law for every signature by induction**: `MV.add` commutative, given `~comm` (`q10_induction_all_sigs.bend`).

**Rejected, though bend2 accepts:**
- **A `~` hypothesis with a bare variable on one side.** `q07b`: `for ~unit: @x -> {op(x, e) == x : T}`. `-o x.bendtt` says `no model for unit2~unit`.
  - The kernel checks a template once, with each `~` constant replaced by a model chosen greedily: T ↦ Unit, operations ↦ `λx y. Unit{}`.
  - Under that model every equation between operation applications holds. `op(x, e) == x` does not, because the kernel has no eta.
  - Upstream: #1182; PR #1263 (open) adds backtracking. Even with backtracking, unit laws plus commutativity have no model in an eta-free kernel; see `upstream/verdict_ring_hypotheses.bend`.
- **A `∀` hypothesis that native `F32.add` is IEEE** (`q09b`): `no model for native_add_bits~ieee`.
- **Large closed computations:** `out of fuel` at 400 M kernel steps (Q4, PGA3D associativity through the normaliser).

**General points:**
- Any def that is out of scope fails the whole run, with the generic "mismatch between the TypeScript implementation, and the formalized BendTT kernel" message. `bend f.bend -o f.bendtt` prints the real reason.
- A hypothesis used more than once must be a `~` argument (issue #848). A function-typed `+h` is rejected: `+unit can be used many times, so its type must be Data`.

## Q8. Strings and file IO for a generator written in Bend

**Fast enough; the cost is ergonomic.** `q08_gen_io.bend` computes PGA3D blade products from `U32` bitmasks (reordering sign and diagonal metric) and prints the full 16×16 product table as text, 100 times:
- 233 KB built in **4 ms** compiled, written in 1 ms;
- 16 ms on the JS lane (deno);
- spot check: `c1 - a15*b14`, i.e. e0123·e123 = −e0, is right.

The ergonomic cost:
- There is no `if`.
- A match or destructure takes only parameters and pattern variables.
- Defs are ordered: a def may call only defs above it.

So every branch on a computed value becomes a helper def, and strings are cons lists. Per Q4, emitted kernels are proven against Layer S inside Bend, so a generator written in another language adds nothing to the trusted base (ADR-001).

## Q9. What a software float costs

`q09_softf32.bend` implements `SoftF32.add` and `SoftF32.mul` on `U32`, about 150 lines:
- branch-free selects, round-to-nearest-even, subnormals, infinities, NaNs;
- Berkeley's `roundPackToF32` structure;
- clz and a 32×32→64 multiply built from 16-bit halves. Base has neither natively. Variable shifts are native (`U32.shrn(a, U32.to_nat(n))`).

Results:
- **Bit-exact against native F32:** `2^24 pairs checked: add mismatches 0, mul mismatches 0`. That covers random pairs plus near-cancelling pairs; NaNs are compared as a class, since NaN payloads may differ.
- **The emitted C is plain integer code** (`U32_BIN(…)` in flat spins, no float operations).
- **Cost:** a dependent chain of 2²⁴ mul+add takes 509 ms in software against 30 ms native, about 17× (~30 ns against 1.8 ns). That is latency-bound; independent lanes would close part of the gap.
- **Parallel, and on the GPU** (`bench/q09_soft_par.bend`): 2²⁶ mul+add over 2¹⁴ balanced leaves, the seed taken from `IO.now()`.

  | run | soft | native |
  |---|---|---|
  | 1 thread (mainline) | 1568 ms | 122 ms |
  | 16 threads (mainline) | 217–224 ms | 14 ms |
  | 16 threads (`bend-hip`, `--gpu off`) | 247–268 ms | 22–23 ms |
  | **HIP `!`** | **7–8 ms** | **1 ms** |

  Soft and native give the same bits everywhere. Soft costs about 13–16× native on the CPU and about 7× on the device (whole process 0.08 s).
- **Native F32 under a hypothesis:**
  - A law taking `~ieee: @a @b -> {F32.bits(F32.add(a,b)) == SoftF32.add(bits a, bits b)}` passes bend2 but **fails `--verdict`** (no model, `q09b`).
  - A law taking the instance it needs as a `+h` point equation passes both (`q09c`).
- **Upstream plans:** Base's F32 operations are bodiless laws. WONTFIX lists "F32 that computes in the checker (#1017)" and F64/U64 (#1120, #1027) as SOON. When #1017 lands, native F32 becomes provable directly and the conditional route is no longer needed.

## Q10. Generic induction over all signatures (extra)

`q10_induction_all_sigs.bend` proves `MV.add(sig, a, b) == MV.add(sig, b, a)` for every `sig`, every `T` and every `~add` with `~comm`. The proof:
- induction on `sig`, matching Z/N and S0/S1;
- the induction hypothesis rewrites each field (`%MV.add_comm(~T, ~add, ~comm, rest, a1, b1) : {N{…} == N{_, …}}`).

It passes bend2 and `--verdict` in 0.25 s. This is Layer S's proof architecture in miniature.

## Language facts that shape the code

These were learned while writing the spikes; the error text is quoted.

1. **Match and destructure only parameters and pattern variables.** `w = f(x); K{a} = w` fails with `a match cannot scrutinize a local binder: give it its own def`. Reading a computed record needs a helper def that takes it as a parameter.
2. **Scrutinee order:** `'q' can't be matched in this position (it is matched after a local statement or after a match on a later binder…)`. Match each parameter before any `let`, in binder order.
3. **Defs are ordered and there is no mutual recursion:** `a filled definition (an unfilled law is a dead claim…)` appears when a def calls one written below it. Loops whose step needs a computed comparison follow the pattern of a structural loop plus a non-recursive step helper (`Poly.merge`/`Poly.step`); Base instead uses fuel (`List.merge.go`).
4. **`A & B` is `Sigma<&1, &1, …>`, which is `Type`.** Its fields cannot be made `+`. For multi-value results, declare `Data` records.
5. **A `~` argument is an opaque constant in the body.** It cannot be matched, and a type-level def applied to it stays stuck. Generic bodies must therefore take shape-carrying data such as `sig` as ordinary arguments and match on them.
6. **Template laws:** one `for` line per parameter. `for ~T: Data, ~add: …` gives `expected : a term, observed : ','`. Proof defs name `~` parameters without the `~` (`def comm3(T, op, comm, a, b, c)`) and pass them with `~` in recursive calls.
7. **Reuse needs `+`** on Data parameters, pattern fields, lets and IO binders: `+t0 : Nat <- IO.now()`. A function value is never Data.
8. **The rewrite `%e : P`, with `e : {a == b}`:** the goal must be `P[_ := b]`, and it becomes `P[_ := a]`. I got this backwards twice; `Equal.trans` and `Equal.sym` are often simpler.
9. **Constant folding is aggressive.** A pure `main` over literals compiles to a constant. Benchmarks must take inputs from `IO.now()` or arguments.
10. **The `+` sugar** in `(… : T)` resolves to `T.add` on the head name of `T`, so `(x + y : U32)` inside a `~` lambda needs its own annotation.

## Upstream items

Nothing is filed; per your decision the notes live in [upstream-notes.md](upstream-notes.md).

## Measurement pitfalls met so far

- zsh does not word-split an unquoted `$o`, so `./x $o` with `o="--gpu off"` passes one argument, which the runtime ignores. Write the flag out in full.
- A computation whose inputs are all literals may be folded at compile time. Take a seed from `IO.now()`.
