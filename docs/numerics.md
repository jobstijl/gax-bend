# Numerics: measuring, proving and tracking rounding error

Status: plan (ADR-005), 2026-10-04. The survey behind it is summarised at
the end, with sources.

## Where we start

Every generated kernel is a straight-line sum of products. Each output
coefficient is a polynomial in the input coefficients, evaluated in a fixed
tree of `add`, `mul` and `neg`. The proofs already reify each kernel as a
term (`Tm`, `src/norm.bend`): its shape, its depth and its exact value are
data the checker can compute with. Native F32 is axiomatic in Bend, but a
software float on `U32` is open to the checker.

That shape is the most favourable case in numerical analysis. Rounding
error in a sum-of-products tree has a classical worst-case bound (Higham,
*Accuracy and Stability*, §3–4) that depends only on the tree. One theorem,
proven once by induction on `Tm`, covers every kernel. No mechanised
library we found states it for arbitrary trees: LAProof covers list folds,
FPTaylor and Gappa certify one expression at a time.

## 1. Prove: one error theorem for every kernel

**Model.** Exact values live in an ordered commutative ring R (dyadic
rationals in practice: every binary32 value is one). A float operation is
`rnd(a op b)`, with `rnd : R → R` any function satisfying the standard
model
  |rnd(x) − x| ≤ u·|x| + η,
with η = 0 for additions (Hauser: an underflowing sum is exact). For
binary32, u = 2⁻²⁴ (round to nearest) or 2⁻²³ (faithful), and η = 2⁻¹⁵⁰.
`neg` and multiplication by a power of two are exact.

**Theorem** (no underflow first, then with η):
  |fl(e) − ⟦e⟧| ≤ h(k(e)) · |e|abs
where:
- ⟦e⟧ is the exact value;
- fl(e) is the rounded evaluation;
- |e|abs is e evaluated with |x| at the leaves and `+` for `−`;
- k counts roundings along the worst path: k(e₁ + e₂) = 1 + max(k₁, k₂),
  k(e₁ · e₂) = 1 + k₁ + k₂;
- h(k) = (1 + u)ᵏ − 1, a polynomial, so the identities it needs are ring
  identities (LAProof's choice over γₖ = ku/(1 − ku)).

The proof is induction on the term. It uses:
- (1 + h(a))(1 + h(b)) = 1 + h(a + b);
- (1 + u) h(m) + u = h(m + 1);
- the monotonicity of h;
- the triangle inequality;
- |xy| = |x||y|.

The ordered-ring laws enter as `~` hypotheses, like the ring laws.
Inequalities reduce to positivity: b − a is a sum of products of known
nonnegatives, which the normaliser checks.

**What it says about a kernel.** The kernel's exact value is the spec's
(the mirror and `.ok` laws). For output k of a product:
  |ĉₖ − (a·b)ₖ| ≤ h(dₖ + 1) · (|a| ⊛ |b|)ₖ,
where ⊛ is the sign-stripped product and dₖ the depth of the output's
addition tree. A sandwich adds one multiplication level. The generator
emits dₖ and the ⊛ kernel, and a law per kernel instantiates the theorem.

**For the hardware.** The theorem holds for every `rnd` satisfying the
model. It applies to native F32 under the hypothesis that the hardware
rounds that way (proof-modulo, ADR-001 A2, backed by agreement tests). It
applies outright once the software float's rounding is proven to satisfy
the model. Faithful rounding (u = 2⁻²³) is the easier first target.

**Later tightenings, not first:** k·u instead of h(k) (Jeannerod–Rump
2013); tree depth instead of operation count.

## 2. Measure

- **An exact oracle.** Run the same kernel at T = dyadic, on the exact
  values of the F32 inputs. The kernels are generic in T, so this is the
  same code. The error is then exact, not estimated. A Kulisch accumulator
  on U32 limbs (about 20 limbs for binary32 products) is the fast version.
- **What to report per kernel and output:** error in ulps; error over the
  theorem's bound; the condition ratio κ = (|a| ⊛ |b|)ₖ / |cₖ|; growth
  against the worst case h(k) ≈ ku and against the √k·u that the
  probabilistic model predicts (Higham & Mary 2019). The probabilistic
  figure only interprets measurements: under round-to-nearest its
  independence assumption is false, so it is not a theorem.
- **Inputs:**
  - random and log-uniform magnitudes;
  - near cancellation: near-identity rotors, CGA points far from the
    origin (null-basis cancellation is why CGA needs fp32, de Haan et al.
    2024);
  - long chains of motor products, with and without `renormalize_fast`,
    tracking ‖m m̃ − 1‖.
- **CPU against GPU, bit for bit**, kernel by kernel (Q5 showed equality
  for one).

## 3. Track (optional, after 1 and 2)

- **A running bound:** the ⊛ kernel next to each kernel, times h(dₖ + 1),
  rounded upward. It costs about 2× and is sound by the same theorem plus
  a lemma bounding the computed absolute sum.
- **A type for it:** `Approx(b)`, a value with an erased proof that its
  error is at most b. Kernel signatures then compose bounds the way
  NumFuzz composes its grades, but in the absolute / |e|abs metric:
  NumFuzz's relative-precision metric does not survive signed cancellation,
  and GA coefficients are signed.
- **More accuracy where it matters:**
  - compensated kernels: TwoSum, plus the Veltkamp/Dekker product, since
    Bend has no FMA (Ogita–Rump–Oishi's Dot2: as if in twice the
    precision);
  - correctly rounded kernels through the exact accumulator;
  - double-F32 (Joldes–Muller–Popescu, formalised by Muller–Rideau).
  All of them belong to the numbers package.
- **Not planned:** stochastic arithmetic (CADNA, Verificarlo) as a
  product, since it estimates and does not bound, and proving
  probabilistic bounds.

## Order of work

1. `Tm.fl`, `Tm.abs`, k and h, and the theorem over an ordered ring with
   an abstract `rnd` (no underflow), then the η term.
2. Per-kernel corollaries from the generator (dₖ, the ⊛ kernel).
3. Dyadic numbers and the exact oracle; a measurement report per algebra.
4. The software float: faithful rounding proven against the model, then
   correct rounding. The largest piece; recent Lean work (TorchLean's
   IEEE32Exec, FloatLib, Tunnell's FP) is the closest reference.
5. Running bounds and `Approx`; compensated and exact-accumulator kernels.

## Survey (2015–2026), what each contributes here

| work | idea | use for us |
|---|---|---|
| Higham, *Accuracy and Stability* (2002); SISC 14 (1993) | tree summation bound Σ γ_{dᵢ}\|xᵢ\| | the theorem's shape |
| LAProof (Kellison, Appel et al., ARITH 2023) | Coq dot-product/GEMM bounds with h(n) = (1+u)ⁿ − 1, an underflow term, finiteness hypotheses | h(k), underflow term, finiteness as a hypothesis |
| VCFloat2 (Appel & Kellison, CPP 2024) | reflective round-off analysis of expression trees, fl(x) = x(1+δ) + ε | architecture: a computable bound proven sound once |
| FloVer (Becker et al. 2017) | verified checker of analyzer certificates for straight-line code | generator emits bounds, a proven checker validates them |
| NumFuzz (Kellison & Hsu, PLDI 2024); Bean (PLDI 2025); eggshel (PLDI 2026) | graded types for forward and backward error | `Approx` typing; not the relative-precision metric |
| Satire (SC 2020), FPTaylor (TOPLAS 2018), Daisy, PRECiSA 4 (FM 2024), Gappa | per-expression symbolic or interval bounds | external cross-checks |
| Higham & Mary (SISC 2019); Sao et al. (2026) | probabilistic √n·u bounds; reduction-tree second moments | interpreting measurements |
| Jeannerod & Rump (SIMAX 2013) | γₙ → n·u | later tightening |
| Boldo–Graillat–Muller (TOMS 2017); Joldes–Muller–Popescu (TOMS 2017); Muller–Rideau (TOMS 2022) | proven TwoSum, double-word bounds | compensated and double-F32 kernels |
| Kulisch accumulator, ExBLAS; posit quire; b-posits (2026) | exact sums of products, one rounding | exact oracle; correctly rounded mode |
| TorchLean IEEE32Exec, FloatLib, Tunnell FP (Lean, 2026) | checker-visible software binary32 and its bounds | reference for the software float |
| De Keninck & Roelfs (MMAS 2024) | closed-form normalisation, exp and log below 6D | renormalisation (`api/`) |
| de Haan et al. (AISTATS 2024) | CGA needs fp32: null-basis cancellation | measurement inputs |

Links: arXiv 2405.04612 (NumFuzz), 2501.14550 (Bean), 2604.15633 (eggshel),
2004.11960 (Satire), 1707.02115 (FloVer), github.com/VeriNum/LAProof,
doi:10.1145/3636501.3636953 (VCFloat2), doi:10.1137/120894488
(Jeannerod–Rump), doi:10.1145/3484514 (Muller–Rideau), 2206.07496 (De
Keninck–Roelfs), 2603.01615 (b-posits), 2602.22631 (TorchLean),
2609.19352 (FloatLib), zenodo.org/records/22775704 (Tunnell FP),
doi:10.1017/S0962492922000101 (Boldo et al., *Acta Numerica* 2023, the
survey to start from).
