# gax-bend design decisions

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

---

## ADR-002: Layer K: generated kind records and mirror kernels, proven by `{==}`

**Status:** accepted, 2026-10-04. Built for VGA2D, VGA3D, PGA2D, PGA3D and STA: 2083 kernels (gp, wedge, vee, add, sub, neg, reverse, involute, conjugate, dual, undual), each with a mirror law and a support law, plus field getters and an F32 module per algebra. The gate checks them all in about 10 s. Mirror kernels run as fast as gax's optimised sandwich in the Q5 harness (bend-facts Q11).

*Amended 2026-10-04:* the inner products (lc, rc, dot, scalar_product), the halved commutator and anticommutator, and the sandwiches (ADR-003) bring it to 4064 kernels.

### Context

Layer S is proven, but it is a tree walk: no use as runtime code. Speed
needs flat records per kind and straight-line kernels (Q5: a flat F32
record kernel matches clang). ADR-001 A1 puts the generator in Bend.

### Decision

1. **An algebra is Bend data.** An algebra is a `Spec` value: a name, a
   signature `Sig(d)` and kinds. A kind is a name plus oriented blades, each
   written as a list of generator indices (so e032 is `[0, 3, 2]`, stored as
   −e023). This is the content of gax's `.gax` files, typed. A text parser
   for `.gax` can come later.
2. **The generator runs the spec itself.** `gen/` instantiates Layer S at a
   symbolic ring `Expr` (variables, `add`, `mul`, `neg` as data) and
   evaluates `MV.gpf` (and the other products) on the embedded symbolic
   operands. The output tree is printed as the kernel. So a mirror kernel is
   the spec's own unfolding, and its equality with the spec holds by
   construction. The checker confirms it per kernel by `{==}` (Q4: 0.3 s
   for a full PGA3D product).
3. **Every algebra is generated as three modules:**
   - kinds: records `Motor<T>` and so on, the embedding `K.tree` (fields to
     leaves, with orientation signs) and the projection `K.of_tree`;
   - kernels: one def per (operation, kind, kind), generic over
     `~T, ~zero, ~add, ~mul, ~neg`, returning the result kind's record;
   - proofs: per kernel the law `K.of_tree(spec(A.tree x, B.tree y)) ==
     kernel(x, y)`, plus the support law (the spec's result is zero outside
     the result kind). Both are proven by matching the records and `{==}`.

   The generator also writes `regen --check`, which compares the committed
   output byte for byte.
4. **Result kind** follows gax's rule (ADR-021 there):
   1. among the declared kinds that contain the support, prefer one that
      adds no grade;
   2. then the smallest;
   3. then the first declared.

   An empty support means no kernel, plus a named empty witness type for
   the API (Q3c). The support law makes a wrong choice a failed proof.
   Minimality is not proven (ADR-001 item 5).
5. **Fields of the result kind outside the support** are `zero` in the
   kernel: a constant, never a multiplication.
6. **No CSE or reassociation in mirror kernels.** Optimised kernels
   (sandwiches, unit kernels) are Phase 3, proven through the polynomial
   normaliser.

### What it costs

- A Bend program of a few hundred lines (Expr, blade masks, printing, file
  IO).
- Generated code grows with kinds² × operations.
- Mirror kernels carry the tree's sum order and its sign noise. In F32 a
  negation is a sign flip, which clang folds into an fsub.

### Measured, not adopted

- **Printing kernels from blade tables (gax-gen's way):** it would need a
  separate proof that the tables equal the spec. Running the spec makes
  that proof `{==}`.

---

## ADR-003: Ring identities by cancellation; sandwiches proven by reflection

**Status:** accepted, 2026-10-04. Built: `src/norm.bend` with
`proofs/norm.bend` (soundness), and the sandwich kernels of every algebra
(198 kernels, 245 zero laws).

### Context

A sandwich v x ~v keeps the grade of x, but only because terms such as
a·b − b·a cancel. So its support law is not `{==}`, and the right result
kind cannot be read off the symbolic tree. ADR-001 item 4 planned a
polynomial normaliser for this, and the brief planned it for versor laws
modulo u~u = 1 and for optimised kernels.

### Decision

1. **Signed monomials, no integer coefficients.** A term (`Tm`) flattens to
   a list of monomials, each with a sign and a sorted list of variables. A
   coefficient c is c copies of a monomial. `Norm.left` cancels opposite
   pairs with a structural pass: each monomial either removes its opposite
   from the pending list or joins it. The soundness proof then needs only
   sums of lists, with no integer-to-ring map and no lemma about
   coefficient arithmetic.
2. **Completeness:** every identity of commutative rings is found, because
   the net count of each monomial is what decides it.
3. **Reflection without printing.** A proof names its term by running the
   spec at `T = Tm` on variable leaves. The checker computes the term, and
   `Norm.zero`'s `ok` is `{==}`. The generated proofs stay small: one
   `Norm.zero` call per blade.
4. **Hypotheses:** the eleven commutative-ring laws listed in `laws.md`,
   among them laws with a bare variable on one side (`zero_l`, `unit_r`,
   `neg_neg`). A2 allows these.
5. **Kernels are quadratic forms** (amended the same day; first they bound
   v x as lets and kept the mirror law). Field c is Σ_j x_j Q_cj(v), with
   the Q_cj read off the spec's coefficients after cancellation. Each field
   is proven equal to the spec's by `Norm.eq`, and a generated congruence
   lemma per kind joins the fields. The matrix Q is what a batch reuses
   for many operands.

### Numbers

- `proofs/norm.bend` checks in 0.5 s.
- One PGA3D zero law (motor on point, e1) checks in under 0.5 s with
  everything it loads (`spikes/q12_transform_support.bend`). Each algebra's
  whole proofs file, sandwiches included, takes 0.6–2.7 s.
- PGA3D `Motor.transform.Point` costs 35 multiplications: 22 products of
  motor coefficients and 13 matrix entries (the let-bound mirror form took
  52; gax's plain kernel takes 38 and its unit kernel 33).
- With every sandwich field proven by `Norm.eq`, the PGA3D proofs file
  checks in 9.6 s and STA's in 9.3 s; the whole gate takes 44 s.
- Speed (bend-facts Q13, 2²⁶ points, one motor): 162–176 ms on one thread
  and 30–34 ms on 16, against 288–295 ms and 46–53 ms for gax's unit
  kernel in Bend and 0.30 s for it in C. Clang hoists the motor-only half
  out of the loop.

### What it costs

- Zero laws assume a commutative ring, so sandwich support is claimed
  only there. The other kernel certificates need no ring law.
- Cancellation is quadratic in the number of monomials. That is fine for
  degree-3 sandwich terms; degree-4 or larger identities may need sorting
  first.
- The quadratic form is not further simplified: an entry such as
  2(ab + cd) is computed with repeated additions, and unit versors get no
  cheaper kernel yet (gax's unit kernels use u ~u = 1).

### Measured, not adopted

- **Printing the reified term into the proof:** about 30 KB per
  coefficient. Running the spec at `T = Tm` in the checker costs nothing
  extra.
- **Integer coefficients with merge-sorted polynomials** (`spikes/q04b`):
  faster on large terms, but the soundness proof needs an integer-to-ring
  map and lemmas about its arithmetic.
- **Unit kernels, simplified modulo u ~u = 1 and made homogeneous again**
  (the brief's drift-tolerant kernels; gax ADR-020). In the quadratic
  slice, the only homogeneous representatives of a unit sandwich are the
  plain kernel plus multiples of the Study condition (gax's
  performance.md). So the saving is small: gax's unit `Motor >> Point`
  costs 33 multiplications, its plain one 38. Our plain quadratic-form
  sandwich costs 35 and is already homogeneous of degree 2, so drift is
  already a uniform scale. `tests/drift_pga3d.bend` checks that: a motor
  drifted by 10⁻³ moves points to the same places after unitizing, within
  10⁻⁵, where a non-homogeneous kernel distorts by about 2.6·10⁻³. The
  remaining gain (about 6%) would need a relation-reducing simplifier in
  the generator, and laws proven modulo the unit relations with explicit
  multipliers. Revisit if a profile shows sandwiches dominate.
  `renormalize_fast` (one Newton step) is in `api/pga3d.bend`.

---

## ADR-004: CGA3D in gax's null basis, through a proven change of basis

**Status:** accepted, 2026-10-04. Built: `algebras/cga3d` (11 kinds, 1219
kernels), every kernel and every kind's change of basis proven.

### Context

gax writes CGA3D in the null basis e1, e2, e3, eo, e∞ with eo·e∞ = −1,
eo² = e∞² = 0 (`cga3d.gax`). Its kinds are sparse there: a motor has 8
fields, a twist 6. Layer S's metric is diagonal (ADR-001 item 1), and the
brief asks for the null basis "via change of basis, proven". In the
diagonal basis e₊, e₋ the same subspaces need more fields (e1∧e∞ is
e1∧e₋ + e1∧e₊), and the coefficients of eo carry ½.

### Decision

1. **The tree runs on e₊, e₋; kinds stay in the null basis.** The spec
   names e₊ and e₋ as generators 3 and 4 (squares +1, −1) and writes blades
   with eo and e∞ as indices 5 and 6. A kind's `tree` embeds each field
   through eo = h(e₋ − e₊), e∞ = e₋ + e₊, with h = ½ a template constant
   (`~half`). Its `of_tree` reads each field back through the inverse,
   e₊ = h e∞ − eo, e₋ = h e∞ + eo. The generator derives both maps by
   expanding blades multilinearly (`Nb.emb`, `Nb.fun`).
2. **Kernels have integer coefficients.** For each result field the
   generator runs the spec at `T = Tm` through the change of basis,
   normalises with `NormSH` (every monomial lifted to one power hᴺ), keeps
   one in 2ᴺ copies, and drops h. The null-basis structure constants are
   integers, so this is exact. No kernel contains ½.
3. **One law per kernel.** `K.Multivector.fields(of_tree(spec(tree a,
   tree b))) == K.Multivector.fields(to_mv(kernel(a, b)))`. Every null-basis
   coefficient of the spec equals the kernel's, and the ones outside the
   result kind are zero. It is proven by one call to `NormSH.eqs`, given
   `h + h = 1`. It covers what `.ok` and the support laws cover elsewhere.
4. **The change of basis is a law per kind:** `of_tree(tree x) = x`
   (`K.<kind>.basis`).
5. **vee carries a sign.** The regressive product depends only on the
   pseudoscalar. e123oi = −e123₊₋, so the spec of CGA's vee is
   `neg(vee)`. Checked against gax's `Vector.vee.Quadvector` term by term.
6. **Dual and undual are the null basis's own complements.** A complement
   depends on the basis, not only on the pseudoscalar (J_diag(eo) =
   ½ e123∞, but J_null(eo) = −e123∞), so the diagonal complements do not
   carry over. gax's dual is the metric-free right complement on the null
   blades. So each null kind also gets `.raw`/`.of_raw`/`.out`, its
   coefficients on the null blades with no change of basis, and dual and
   undual are proven against `S.MV.rcomp`/`lcomp` on that layout, by
   `{==}` (amended 2026-10-05; `tests/cga3d_dual.bend` checks values
   against gax's generated code).

### Numbers

- Result kinds equal gax's generated types for all 954 pairs: gp 121,
  wedge 100, vee 92, lc 98, rc 98, dot 121, scalar product 57, commutator
  81, anticommutator 121, sandwiches 44.
- `tests/cga3d.bend`, over exact integers: eo e∞ = −1 + eo∧e∞; a conformal
  point squares to 0; a translator moves (1, 1, 0) to (3, 1, 0); P·Q is
  −½|p − q|².
- Generation of all six algebras: 13 s. The CGA3D proofs are 3.2 MB (per-field laws in
  the earlier form were 47.6 MB), split into `proofs.bend` (the
  change-of-basis laws) and 21 files of 60 kernels (`proofs_2.bend` and
  on), so a failure points at a part.
- **Checking takes 4136 s** as one file (3.7 GB peak), and `tools/gate.sh
  --full` takes 4905 s in all, 55 min of it for `proofs_22.bend`: the
  last 19 kernels, sandwiches by Even and Odd on the largest kinds. A
  32×32 Multivector product alone takes 17 s. So `tools/gate.sh` skips
  CGA3D's proofs and says so; `tools/gate.sh --full` checks them.

### What it costs

- An hour of checking for CGA3D, outside the default gate. The cost is in
  normalising both sides of each law in the checker. A homomorphism lemma
  ("eval commutes with the spec"), proven once per operation, would remove
  one side.
- Laws need ring with ½ (`~half`, `h + h = 1`); kernels do not.

### Measured, not adopted

- **Kinds in the diagonal basis e₊, e₋:** every operation would be a plain
  mirror kernel, but a motor needs 12 fields instead of 8 and the kinds no
  longer match gax's.
- **One law per field** (as for the diagonal sandwiches): 47.6 MB of proofs.

---

## ADR-005: Rounding error is proven once for every kernel, measured against an exact oracle, tracked optionally

**Status:** accepted, 2026-10-04; work in progress. The plan, the survey and the
sources are in [numerics.md](numerics.md).

### Decision

1. **Prove** one theorem by induction on the reified term (`Tm`):
   |fl(e) − ⟦e⟧| ≤ h(k(e))·|e|abs, with h(k) = (1+u)ᵏ − 1. It holds over
   any ordered ring and any rounding function satisfying the standard
   model |rnd(x) − x| ≤ u|x| (+ η for underflow). Each kernel's bound
   follows from its depth and its sign-stripped twin.
2. **Measure** against the same kernel run at T = dyadic (exact), reporting
   ulps, error over bound, and the condition ratio.
3. **Track** (optional): running bounds (the ⊛ kernel, about 2×), and an
   `Approx(b)` type in the absolute metric.
4. **Native F32** gets the theorem under the hypothesis that it rounds by
   the model (proof-modulo). The software float discharges that hypothesis
   by proof, faithful rounding first.

### What it costs

- An ordered-ring hypothesis set beside the ring one.
- The bound is the worst case: about k·u where measurements show about
  √k·u.
- The software float's rounding proof is the largest single piece of work
  in the plan.
- The theorem is stated over computed operations fadd, fmul within ε of
  exact, not over a rounding function. rnd∘add is one instance, and
  F32.add is one directly. This is what lets a kernel law be a `{==}`
  instantiation.
- Per-kernel laws: 40 MB of generated source (`algebras/*/err.bend`, 7189 laws and
  as many underflow laws, mostly the repeated hypothesis list) and about
  4 minutes of gate time.

### Measured, not adopted

- **NumFuzz's relative-precision metric:** not defined across sign
  changes, and GA sums cancel.
- **Probabilistic bounds as theorems:** false under round-to-nearest
  (deterministic rounding), and they would need probability theory in the
  checker.
- **Per-kernel tools (FPTaylor, Gappa) as the evidence:** one run per
  kernel, outside Bend. Kept as cross-checks.

---

## ADR-006: Linear maps come from the dual-number coefficient ring, not from typed slot lists

**Status:** accepted, 2026-10-05. Partial answer to the brief's extensor
layer (gax law families A–C); the multicategory structure is not typed.

### Decision

gax makes values, linear maps and multilinear forms one type family:
`Point<(Point,)>` is a point-valued map of a point, and products of
`A<S1>` and `B<S2>` are `C<S1 ++ S2>`. That needs every kernel templated
over a bilinear coefficient pairing, A × B → C, and in Bend also a Layer S
over pairings, so that the mirror proofs still apply.

Here kernels keep one coefficient ring, and maps come from a ring instead:
dual numbers T[ε]/(ε²) (`src/dual.bend`), proven a commutative ring over
any commutative ring T (`proofs/dual.bend`). Running a kernel with ε on
input coefficient j puts column j of the kernel's matrix (for a kernel
linear in that operand) in the outputs' ε parts. In general it puts the
derivative along that coefficient there: forward-mode differentiation.
Every kernel, mirror law, error law and API function runs on duals
unchanged, because they are generic in T.

### What it costs

- A matrix takes n kernel runs, one per input coefficient, where gax gets
  it in one pass. The prepared sandwich maps (`V.prepare.X`) stay the fast
  path for versors.
- Slot lists are not types: there is no `B<(A,)>` kind, no typed
  composition, and the multicategory laws (gax family A) are not stated.
  Linearity (family B) is checked on values (`tests/dual_map.bend`: matrix
  times point equals the kernel), not yet proven per kernel.
- Lifting (family C) holds by construction: the dual-number instance of a
  kernel is the same code.

### Measured, not adopted

- **Typed slot lists with pairing-templated kernels:** every kernel's
  signature, the generator and Layer S would change, with the mirror
  proofs redone over pairings. Revisit if typed maps prove necessary for
  the API.

## ADR-007: Exact and binary64 arithmetic runs on limbs proven by a value map

**Status:** accepted, 2026-10-05. Answers the brief's SoftF64 and exact
oracle items, and the accumulator half of "posits with quires".

### Decision

Run-time Nat stops at 2⁴⁸ − 1 (bend-facts Q16). A binary64 product needs
106 bits, a binary32 sum across the exponent range about 280, and an
exact accumulator more. So `src/big.bend` has big naturals as limbs in base
2h, least significant first, and big dyadics as sign, limbs and exponent.
Each operation uses Base's native Nat operations on limbs. A value map
`Bn.val` into Nat (unbounded in the checker) states correctness:
comparison, addition, multiplication, subtraction, halving, parity and
shifts each commute with it, for limbs below the base, and keep them there
(`proofs/big.bend`). The base stays symbolic in every proof: the checker
never sees 2²³.

Rounding on limbs runs the spec's loop (`Tr.go`, `Fx.go`) with limb
operations. The spec uses fuel n, which no run-time number can hold, so
the limb loop uses fuel h·(number of limbs), and two lemmas join them:
the loop's result does not depend on its fuel once n < 2^(p+fuel)
(`Fuel.go`), and a number of L limbs is below 2^(h·L) (`Val.lt`, from
2h ≤ 2^h). From there, normal forms, the range test and the two formats
link to `Dy.f32` and `Dy.f64` (`F32.lk`, `F64.lk`), so `Fl.model`, and
with it every error theorem, holds for big binary32 and binary64.

### What it costs

- About 2 000 lines of proof for 450 lines of code, and the proofs check
  in about a second.
- Speed: a binary64 product takes about 40 limb operations plus a
  rounding loop of up to 53 halvings over 5 limbs; the 600-operation
  binary64 test runs in 1.4 s including startup. A reference, not a
  kernel format: kernels stay native F32.
- Shifts double one bit at a time (`Bn.shl`), so a sum across a wide
  exponent gap costs one addition per bit of the gap.
- Results can carry leading zero limbs; values and comparisons are
  unaffected.

### Measured, not adopted

- **Binary limbs (base 2):** halving is free and the proofs shorter, but a
  53-bit product takes 2 809 bit steps instead of about 9 limb products.
- **The spec's fuel n at run time:** impossible past 2⁴⁸, hence `Fuel.go`.
- **Proving rounding invariant under scaling** instead of normalising
  before rounding: it needs the loop's behaviour on 2n, a longer proof
  than mirroring `Dy.of`.

## ADR-008: Posits are bounded posits (b-posits), rounded as tapered binary floats

**Status:** accepted, 2026-10-05. Answers the brief's "posits/b-posits with
quires".

### Decision

A posit's regime can fill the word. Then exponent bits are cut off, and
rounding on the bit string is no longer rounding to nearest in value: the
relative error reaches a factor of 2 at the extremes. No uniform model
holds there. A b-posit caps the regime at rs bits (Jonnalagadda, Thotli
and Gustafson 2026), so the exponent field is always whole and at least
p0 = n − es − rs fraction-plus-hidden bits remain. Then rounding the bit
string to nearest, ties to even, is rounding the value to nearest at
p0 + (rs − regime length) bits. `src/posit.bend` defines it that way, on
dyadics, with saturation at minpos and maxpos. The model follows from
`Rne.rel` and `Ulp.mono`, plus a direct argument below minpos
(`Tiny.err`). The run-time version reuses the big dyadics of ADR-007 and
is proven equal (`Pz.lk`). The quire is `Bd.dot` rounded once.

### What it costs

- 250 lines of code and 470 of proof; the proofs check in about a second.
- The equivalence with the standard's bit-string rounding is tested,
  not proven: 1 640 checks against an independent Python reference.
- Encoding to bits and decoding run on Nat patterns; they are tested, not
  proven.
- Above maxpos, saturation is outside the model; theorems hold for
  executions with no result beyond maxpos.

### Measured, not adopted

- **Standard posits (rs = n − 1):** in range and with whole exponents they
  are the same spec, but the extreme regimes need the bit-string rounding
  and admit no uniform model. Left out.
- **Takums** (Hunhold 2024), another bounded tapered format: same shape of
  model, different encoding. Not needed for the brief.

## ADR-009: TwoSum is Fast2Sum on the magnitude-sorted pair

**Status:** accepted, 2026-10-05.

### Decision

Knuth's TwoSum is branch-free and takes 6 additions. `num/df32.bend`
instead orders the operands by magnitude with two selects and runs
Fast2Sum, which takes 3. The two return the same pair, since both are
exact. Fast2Sum's exactness is proven (`proofs/eft.bend`), from
nearest-ness, monotonicity and Sterbenz's lemma, so TwoSum's is a
two-case corollary.

### What it costs

- One magnitude comparison per TwoSum, as a select; no branch on GPU.
- Knuth's version would need its own, longer proof.

### Measured, not adopted

- **Knuth's 6-operation TwoSum:** same results (`tests/df32_exact.bend`
  shows both exact before the switch); its proof has more cases than
  Fast2Sum's and buys nothing on this target.

## ADR-010: Dekker's product is proven for even precision, without underflow

**Status:** accepted, 2026-10-05.

### Decision

`proofs/eft2.bend` proves the two halves of `num/df32.bend`'s TwoProd on
the integers rounded to p bits, as `proofs/eft.bend` does for Fast2Sum.

- **Veltkamp's split** is exact for every representable input, at every
  precision and for every s. The hi step is Fast2Sum's opposite-sign case
  (`F2S.opp`). lo is a rounding error, representable by `LA.d`.
- **Dekker's product** is exact for p = 2s with s >= 2, for every
  representable input:
  - Each input is scaled by a power of two into [2^(p-1), 2^p). Every
    step commutes with that scaling (`TP.sh.e`), and with negation.
  - There the split gives hi = Ah 2^s with Ah <= 2^s and 2 |lo| <= 2^s.
  - The partial sums lie on a grid: e1 = ah bh - pi on 2^(p-1), e2 on
    2^s. They are also small: |e1| <= 2^p 2^(p-1), |e2| <= 2^p 2^s,
    |e3| <= 2^p. So each one is representable (`Rep`).
  - The magnitude bounds are polynomial certificates under 2^s >= 4,
    checked by the ring normaliser (`Poly1`, `Poly2`).
- **Binary32.** p = 24 = 2 · 12 is an instance:
  - `F32.Split` holds in Dy.f32 arithmetic for every binary32 value,
    since on the 2^-149 grid the format's rounding is the integer
    rounding (FlL).
  - `F32.TwoProd` holds in 24-bit rounding with no exponent bounds.

### What it costs

- **Even p only.** Binary64 (p = 53) is not covered. Dekker's product
  is exact there too in radix 2 (Boldo, 2006), but that is a separate
  argument.
- **The product's theorem excludes underflow.** With gradual underflow,
  the error of a b can fall below the subnormal grid, and then e is not
  exact. The native test skips those products (2 568 of 20 000 in
  `tests/df32_exact.bend`). The split has no such restriction.
- **Size.** 1 872 lines, which check in about 2 s.

### Measured, not adopted

- **Analysing σ, the shift of g - a, for every input.** The brute force
  (p <= 10) confirms σ <= s and hi on p - s bits for any a. For
  normalised a and p = 2s, σ = s exactly (p <= 14), so scaling to
  normalised inputs removes that case analysis.
- **Machine-chosen multipliers.** sympy's division by the relations
  (lex order) found valid certificates, but with up to about 60 relation
  copies for S·S >= 4S. Hand-chosen multipliers, checked by sympy before
  Bend sees them, need 4.
