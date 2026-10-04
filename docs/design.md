# gax-blend design decisions

Each ADR has a status, the decision, the numbers behind it, a "what it costs"
line, and the ideas that were measured and not adopted. Amendments are dated
notes added in place. The facts and measurements cited live in
[bend-facts.md](bend-facts.md), referenced as Qn.

---

## ADR-001: Three layers (spec, kernels, API), with the proof burden on Bend

**Status:** accepted with amendments, 2026-10-04. Proposed in Phase 0; your review answered the open decisions. The amendments (A1–A4) follow the Decision section and override the items they name. 2026-10-04: Layer S is built and all 22 of its draft laws are proven ([laws.md](laws.md)); item 1 holds as written, and A3 (MV.mk) cost the predicted one transparency lemma per operation.

### Context

The brief proposes three layers:
- **S**, a generic tree spec with laws proved for all signatures;
- **K**, generated flat kernels, each proven against S;
- **A**, a geometric API.

Phase 0 tested each assumption on Bend 2.0.35 (Q1–Q10). The architecture
stands. Six amendments follow from the measurements.

### Decision

**1. Layer S is the Fuchs–Théry tree, as prototyped** (`spikes/q03_mv_tree.bend`).
- `MV(T, sig)` is a type-level def. Each level is `Lv<A> = Z{} | N{e, r}`, meaning `e·x₁ + x₂`; the leaves are `S<T> = S0{} | S1{x}`. The metric list `sig` holds `QP`, `QN` and `QZ`, with the degenerate generator first.
- Products are structural recursion on `sig`:
  - the geometric product makes 4 sub-calls (3 at a `QZ` level);
  - the grade involution and the sign travel down as Boolean flags, so no negated subtree is ever built;
  - zero is structural at every level.
- `sig` is an ordinary (runtime) argument, not a `~` one. A `~` argument cannot be matched, and a type-level def applied to it stays stuck (Q3, Q2c).
- Laws are proved for every signature by induction on `sig`. The pattern passes bend2 and `--verdict` (Q10: `MV.add` commutativity in 0.25 s).
- The tree's metric is diagonal. CGA's null basis comes in through a proven change of basis, as in the brief.
- **Open for Phase 1: canonical zero.** e0·e0 evaluates to `N{Z{}, Z{}}`, not `Z{}`, and equality is intensional (Q3). Two options:
  - (a) state every law up to a canonicalising `MV.canon`;
  - (b) build every tree through a collapsing smart constructor.

  I lean to (a): the products stay exactly Fuchs–Théry, and the canonicalising function is proven idempotent once.

**2. The scalar ring is a set of separate `~` operations, not one record.**
- Generic code takes `~T: Data, ~add, ~mul, ~neg`. Subtraction is `add(a, neg(b))`, which in IEEE gives the same bits as `a − b`. Zero and one are passed only where a law needs them.
- These compile to exactly the hand-written native code (Q2).
- A `~R: Ring<T>` record cannot be opened at compile time. Through runtime projections it leaves closures and `clo_apply` in the C (Q2).
- Users never see the operation arguments: Layer A has per-scalar concrete entry points, generated for `F32`, `Int`, `Poly` and the rest.

**3. Ring hypotheses are `~` proofs with an operation on both sides.**
- The hypotheses are commutativity, associativity, distributivity and sign laws such as `neg(mul(x, y)) == mul(neg(x), y)`, all stated with an operation application on both sides.
- Reason: `--verdict` checks a template against a greedy model (T ↦ Unit, operations constant). Every such equation holds there. One with a bare variable on one side, like `add(x, zero) == x` or `neg(neg(x)) == x`, has no model, so the law falls out of the kernel's scope (Q7, `upstream/verdict_ring_hypotheses.bend`, issue #1182).
- The tree makes this affordable. Structural zero removes every need for an additive identity, and sign flags avoid `neg ∘ neg` on bare variables.
- A hypothesis passed as `+h` must be a point equation: function-typed hypotheses are affine (Q7, issue #848).
- If a Phase-1 proof needs a law outside this form, I report it rather than weaken anything. This is a restriction on the hypotheses, not on the laws in `LAWS.bend`: fewer hypotheses make a stronger theorem.

**4. Layer K: flat `Data` records per kind, mirror kernels proven by `{==}`.**
- **Mirror kernels.** A kernel that reproduces the spec's unfolding term for term is proven by `match x y` followed by `{==}`.
  - This is cheap at every size measured: PGA3D (192 multiplies) takes 0.32 s in bend2 and 0.33 s under `--verdict`; a 32-coefficient algebra (1024 multiplies) takes 0.42 s in bend2 (Q4).
  - In the speed test (Q5), the gax unit-motor sandwich written as a flat F32-record kernel matches clang (0.36–0.43 s against 0.41–0.45 s for 2²⁶ sandwiches on one thread; 59–71 ms against 65–80 ms on 16 threads), with the same bits.
- **Optimised kernels** (CSE, drift repair). They need the polynomial normaliser.
  - In bend2 the cost is fine: PGA3D associativity takes 5.6 s, 4D 9.9 s.
  - Under `--verdict` the kernel runs out of fuel at PGA3D (400 M steps), while 2D and 3D pass.
  - So these laws get a separate evidence tag (item 8) unless the Phase 2 test of splitting per output coefficient fits within the fuel.
  - The soundness theorem of the normaliser, `eval(norm p) = eval p`, is still to be written. Its cost is paid once.

**5. The generator is untrusted, so it goes where it is cheapest: a Bend printer in gax-gen.**
- Every emitted kernel is proven against Layer S inside Bend (item 4). A wrong sign, blade or orientation fails the check (negative controls: Q4).
- Every result-kind table entry is a type-level function whose reduction the kernel's signature must match.
- So the language the generator is written in adds nothing to the trusted base. That makes it cheapest to reuse gax-gen (Rust): its spec parser, Chevalley tables, kind rule (ADR-021 there), SLP/CSE optimiser, Study kernels and error bounds.
- It gets a `Target::Bend` printer that emits mirror kernels plus their proof defs. `regen --check` keeps the committed output byte-identical.
- **What the proofs do not cover:**
  - that the chosen result kind is the *smallest* (a wrong choice that is too large still passes);
  - that a product reported missing really has empty support.

  Both can be closed with generated per-pair laws: the spec product of the embedded kinds is canonical zero, or has the declared support. Phase 2 adds them.
- **Where the code lives is your call:** a branch of the gax repository, or a vendored copy.

**6. Result kinds are computed at the type level** (this overturns gax ADR-036).
- Kinds are `Data` tags.
- `KT(k, T)` maps a kind to its record type, and `GpK(ka, kb)`-style tables give the result kind.
- A dispatcher over tags folds to the direct kernel call when the tags are literals (Q3).
- A missing product is an erased-in-effect witness of a named empty type. The user then reads `expected : NoWedge.Vector.Bivector.grade3.exceeds.dim2` (Q3c).
- **Operator sugar** only reaches two-argument defs on the head type: `(a .^. b : Line)` calls `Line.xor` (Q6). How products are spelled in Layer A (named per-pair defs, dispatcher, or operators within a kind) is a Phase 2 API decision, to be shown to you with examples.

**7. Numbers (brief §3b) are kept, with one amendment.**
- The conditional route for native F32, a `~ieee` `∀`-hypothesis, passes bend2 but fails `--verdict`: there is no model (Q9b). Laws over native F32 therefore either:
  - take the per-operation instances they use as `+h` point equations, which pass `--verdict` (Q9c) but are verbose; or
  - carry the bend2-only tag.
- Upstream lists bit-level F32 in the checker as "SOON" (#1017). When it lands, native F32 becomes provable directly and SoftF32's link proof transfers.
- Accordingly, the exact spec (dyadics) and the SoftF32 link come before tuning the fast path.
- Measured: SoftF32 add+mul are bit-exact on 2²⁴ checked pairs (2²³ random, 2²³ near-cancelling) and about 17× slower than native on a dependent chain (Q9).

**8. Evidence tags** (used in `docs/laws.md`).

| tag | meaning |
|---|---|
| **proof** | bend2 *and* `--verdict` accept it |
| **proof-bend2** | bend2 accepts it; the kernel rejects it with a recorded reason (out of fuel, or no model) |
| **proof-modulo** | proven given `~` or `+h` hypotheses, which are named |
| **exact-sample** | exact identity tests at random points (ℤ/p, Schwartz–Zippel) |
| **f32-prop** | F32 property or differential test, with its tolerance |
| **doc** | stated, not checked |

Negative controls are required per law family.

**9. GPU.** Mainline Bend has no lane for this machine's AMD GPU (Metal and CUDA only, WONTFIX #811). See A4.

### Amendments (2026-10-04, after review)

**A1. The generator is written in Bend, in this repository** (replaces item 5).
- Your decision: no Rust, no gax dependency.
- The trust argument of item 5 still holds. Every emitted kernel and kind table is proven against Layer S, so the generator stays outside the trusted base, and in Bend its blade and sign logic can carry laws of its own as well.
- Speed is no obstacle: 100 PGA3D product tables (233 KB) are built in 4 ms (Q8).
- **What it costs:**
  - re-implementing in Bend what gax-gen already has: the spec parser, Chevalley tables, the kind rule, and later the CSE / SLP optimiser and error bounds;
  - Bend's ergonomics: no `if`, a helper per branch, cons-list strings.
- **Shape:** a Bend program reads `specs/*.gax`, the same format as gax, and writes the generated `.bend` modules plus their proof modules. `regen --check` compares the committed output byte for byte.

**A2. The gate is bend2; there is no `--verdict` on this machine** (amends items 3, 4, 7 and 8).
- Your decision: no Lean on this PC. Lean 4.34 and the compiled kernel are removed.
- "Proven" now means the gate `bend PROOF.bend` prints ALL PROOFS CHECK.
- Item 3's restriction (ring hypotheses with an operation on both sides) existed only to satisfy `--verdict`'s model search, so it is **lifted**. `~` hypotheses may be any ring laws; bend2 accepts them (`q07b`). Proofs still avoid needless bare-variable hypotheses, since that costs nothing and keeps them kernel-friendly.
- Item 4: normaliser proofs of optimised kernels are ordinary proofs, since bend2 checks PGA3D associativity in 5.6 s.
- Item 7: laws over native F32 are conditional bend2 theorems with a `~ieee` hypothesis per operation (accepted by bend2, `q09b`), tagged proof-modulo. The hypothesis is backed by the agreement tests (Q9: 0 mismatches).
- **Revised evidence tags:**

  | tag | meaning |
  |---|---|
  | **proof** | the bend2 gate accepts it |
  | **proof-modulo** | proven given named hypotheses (for example `~ieee`) |
  | **exact-sample** | exact identity tests at random points |
  | **f32-prop** | F32 property or differential test, with its tolerance |
  | **doc** | stated, not checked |

- **What it costs:** bend2 (TypeScript) is the only checker; there is no second, Lean-proven check. Upstream limits on the kernel are logged in [upstream-notes.md](upstream-notes.md) and not filed.

**A3. Canonical zero: products build levels through a collapsing constructor** (closes the open point in item 1). Revised on 2026-10-04 before any proof was written. The first version stated every law up to an `MV.canon` function.

- **Decision:** `MV.mk(d, e, r)` writes `N{zero, zero}` as zero.
  - The operations that can drop terms build each level through it: the geometric and outer products (where a generator squares to 0) and grade projection.
  - The sign operations (negation, involutions, complements) only permute and negate, so they keep the input's shape and need no collapse. Addition of canonical trees is canonical as it stands.
  - So every product returns the canonical tree, and laws are plain equalities: `gp(gp(x,y),z) == gp(x,gp(y,z))`.
- **What the proofs pay:** one transparency lemma per operation, for example `gpf(mk(a,b), y) == gpf(N{a,b}, y)` and `add(mk(a,b), mk(c,e)) == mk(add(a,c), add(b,e))` (`proofs/gp.bend`, `proofs/add.bend`).
- **The cost of `canon` instead:** a `canon` on both sides of every law, plus a respect lemma per operation. That is the same work, with uglier statements.
- **Mirror kernels:** they are unaffected. `mk` reduces as soon as its arguments are constructors, which they are on symbolic inputs.
- **Hypotheses:** a law whose statement has a bare variable on one side, such as a unit law `gp(1, x) == x`, needs its input to be canonical. Such laws take a canonicity hypothesis. None of the current laws needs one.
- **Ring zeros stay leaves:** a leaf `L{x}` whose `x` happens to be a ring zero is not collapsed, because rings need not have decidable equality.

**A4. GPU numbers come from the upstream `hip` branch with ROCm** (replaces item 9).
- **Setup:** your decision, no CUDA or Metal hardware here. The branch is Bend 2.0.24, 147 commits behind main, and is run with Bun 1.4.2. ROCm 7.2.4 is unpacked in `.vendor/rocm` (7.1 GB, no system install). `. tools/env-hip.sh` provides `bend-hip`.
- **The device works and is bit-identical to the CPU:**
  - 2²⁸ PGA3D unit-motor sandwiches take 7–8 ms on the RX 6900 XT, against 202–238 ms for the same Bend binary on 16 CPU threads and 257 ms for C on 16 threads;
  - SoftF32 mul+add costs 7–8 ms against 1 ms native for 2²⁶ (Q5, Q9).
- **Rules:**
  - Library code targets main (2.0.35).
  - Every benchmark that runs on the device must also check on 2.0.24.
  - Results record which compiler produced them.
  - When upstream merges or drops the lane, this amendment is revisited.
- **What it costs:**
  - two compilers in play;
  - a branch that may be abandoned;
  - 7.1 GB of ROCm in `.vendor`;
  - a 1 ms timer, which caps resolution on short device runs, so benchmarks size their work to at least 100 ms.

### What it costs

- **Verbose generated code:** four `~` operations on every generic def, and a helper def wherever a computed value is inspected (bend-facts "Language facts" 1–3).
- **Restricted hypotheses:** ring laws must have an operation on both sides.
- **Optimised-kernel proofs** at 16 coefficients and above are, for now, bend2-only.
- **Generator in Bend** (A1): more code to write.
- **bend2 is the only checker** (A2).
- **GPU through an unmerged branch** (A4).
- **Disk:** about 7.6 GB in `.vendor` (ROCm 7.1 GB, clang 0.4 GB, Bun 0.1 GB, Bend sources).

### Measured, not adopted

| idea | measurement | why not |
|---|---|---|
| One `~R: Ring<T>` record | closures, `Ring.mul` segment and `clo_apply` in the C (Q2); cannot be matched in a template | runtime cost; it cannot be opened at compile time |
| Op-selector `~R: Op -> T -> T -> T` | folds to native code (Q2d) | awkward for operations of other arity; laws read badly |
| Generator as a Bend printer in gax-gen (Rust) | reuses gax-gen's parser, kind tables and optimiser | your decision: everything in Bend, in this repository (A1) |
| Normaliser proofs as the main kernel evidence | `--verdict` out of fuel at PGA3D (Q4) | kept for bend2; mirror kernels are the kernel-checked route |
| `~ieee` hypothesis for native F32 under `--verdict` | no model (Q9b) | moot after A2: bend2 accepts it; tagged proof-modulo |
