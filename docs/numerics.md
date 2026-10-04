# Numerics: measuring, proving and tracking rounding error

Status: ADR-005, 2026-10-04. Step 1 is proven, without and with
underflow (`Err.bound`, `Err.bound_u` in `proofs/err.bend`, written by
`gen/proofs/err.bend`). A first measurement against it, with a
double-F32 reference, is in "Measured so far" and checked by
`tests/err_measure.bend`. The survey behind it is summarised at the end,
with sources.

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

**What it says about a kernel** (proven: `algebras/*/err.bend`, one law
per kernel). The kernel's exact value is the spec's (the mirror and `.ok`
laws). For output i:
  |ĉᵢ − cᵢ| ≤ h(kᵢ) · (|a| ⊛ |b|)ᵢ,
where ⊛ is the kernel itself run on |inputs| with neg the identity, and
kᵢ is the kernel run in the depth semiring (add = 1 + max, mul = 1 + a +
b) on zero inputs. No second implementation is involved. Each law matches
the operands and calls the generic `Err.fields` on the kernel's own terms
(the kernel run at T = Tm); conversion does the rest.

**For the hardware.** The theorem holds for every `rnd` satisfying the
model. It applies to native F32 under the hypothesis that the hardware
rounds that way (proof-modulo, ADR-001 A2, backed by agreement tests). It
applies outright once the software float's rounding is proven to satisfy
the model. Faithful rounding (u = 2⁻²³) is the easier first target.

**With underflow, as proven** (`Err.bound_u`): additions round by
rnda within ε|x| + η_a and products by rndm within ε|x| + η_m. Separate
functions let one theorem cover both gradual underflow (η_a = 0, Hauser)
and flush-to-zero GPUs (η_a = η_m = 2⁻¹²⁶). The bound becomes
  |fl(e) − ⟦e⟧| ≤ h(k(e)) · |e|abs + D(e),
  D(a + b) = η_a + (1 + u)(D(a) + D(b)),
  D(a · b) = η_m + (1 + u)(F(a) D(b) + D(a) F(b) + D(a) D(b)),
with F(x) = (1 + h(k(x))) |x|abs, the bound on |fl(x)| without η. D is
computed from the term, like k, and is 0 when η_a = η_m = 0. Its
D(a)D(b) term is second order in η, negligible in practice but kept
because it makes the statement exact.

**Overflow** is outside the model. `rnd` satisfies it only for results
within the format's range, so the theorems describe overflow-free
executions, as LAProof's finiteness hypotheses do.

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

### Measured so far

`bench/measure_pga3d.bend` and `bench/measure_cga3d.bend`, 100 000 random
inputs per kernel (seeded, in [−1, 1)). Each kernel runs as the same
generic code at four instantiations:
- F32, the result under test;
- double-F32 (`num/df32.bend`: TwoSum, Veltkamp–Dekker TwoProd,
  Joldes–Muller–Popescu's AccurateDWPlusDW and DWTimesDW), the reference;
- double-F32 on |inputs| with `neg` the identity, giving |e|abs;
- a depth semiring on Nat (add = 1 + max, mul = 1 + a + b), giving k.

The bound used is k·u·|e|abs with u = 2⁻²⁴, which is h(k) to first order.

| kernel | k | max err / bound | mean | max err / (u·\|e\|abs) |
|---|---|---|---|---|
| PGA3D Motor.transform.Point | 12 | 0.63 | 0.057 | 4.5 |
| PGA3D Motor.gp.Motor | 4 | 0.79 | 0.10 | 2.4 |
| PGA3D Point.vee.Point | 2 | 0.96 | 0.20 | 1.9 |

What this shows:
- No sample breaks the bound. So nothing contradicts the hypothesis that
  F32 rounds by the standard model.
- For short kernels the bound is nearly attained: 0.96 for the two-term
  sums of `vee`.
- For the long sandwich the observed growth (4.5 u) is well below the worst
  case (12 u), between √k and k. This fits the probabilistic picture.

CGA3D `Vector.dot.Vector` on embedded points: x near (R, R/2, −R/3) and y
within 1 of x, k = 5.

| R | max err / bound | max relative error | max κ |
|---|---|---|---|
| 1 | 0.48 | 8·10⁻⁴ | 4.6·10⁴ |
| 100 | 0.25 | 1.4 | 1.0·10⁸ |
| 10⁴ | 0.26 | 7.9·10⁴ | 2.9·10¹³ |

The absolute bound holds at every scale. The relative error tracks κ: at
R = 100 the worst sample's distance has no correct digits. This is the null-basis
cancellation of de Haan et al. 2024, now with a proven bound. A caller
that needs distances far from the origin should translate the points
towards the origin first, or use double-F32.

Caveat: the reference has its own error, about k·2⁻⁴⁸·|e|abs. That is
2⁻²⁴ of the bound, so err / bound is exact to about 10⁻⁷. The relative
error, though, is only reliable while κ ≪ 2⁴⁸/k. The R = 10⁴ row exceeds
that, so its relative error is an order of magnitude only. The exact
dyadic oracle (step 3) removes this caveat.

The gate runs `tests/err_measure.bend`, 20 000 samples per kernel. It also
runs a control: the same check against a quarter of the bound must fail,
and it does.

## 3. Track (optional, after 1 and 2)

- **A running bound (proven, `Err.track`):** the absolute-size kernel is
  computed at F32 too, Â (the kernel on |inputs| with neg the identity).
  Then
    |ĉ − c| · (1 − h(k)) ≤ h(k) · Â.
  The proof applies the theorem to the absolute-size term itself, which
  gives A·(1 − h) ≤ Â, and chains it with the main bound. It needs two
  more order facts, ||x|| = |x| and x ≤ |x|, both easy for Int and Dy.
  `api/track.bend` turns this into a factor, `Track.factor(k)` ≥ h/(1 − h),
  so B = factor · Â, at about twice the kernel's cost. Measured in
  `bench/measure_pga3d.bend`: err/B is at most 0.96 over 300 000 samples,
  as tight as the exact-size bound. `tests/err_measure.bend` checks
  err/B ≤ 1 in the gate.
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
   an abstract `rnd` (no underflow), then the η term. **Done.**
2. Per-kernel corollaries from the generator (dₖ, the ⊛ kernel).
   **Done**, without underflow; the underflow form (`Err.bound_u`) has
   no per-kernel law yet.
3. Dyadic numbers and the exact oracle; a measurement report per algebra.
   **Dyadics done and proven an ordered ring** (`proofs/dyadic.bend`).
   The oracle is not: run-time Nat is capped at 2⁴⁸ (bend-facts Q16), so
   exact F32 sums need limbs. The double-F32 reference stays meanwhile.
4. The software float: faithful rounding proven against the model, then
   correct rounding. **Started:** truncation to p bits on dyadics is
   proven to meet the model with ε = 2^(1−p) (`proofs/round.bend`). So the
   theorems hold outright for p-bit truncating arithmetic. Round to
   nearest, ties to even, is proven with ε = 2^−p, IEEE's unit roundoff
   (`Rne.rel`; `tests/round_err.bend`). Gradual underflow is proven
   too: the format model |fl(x) − x| ≤ 2^−p|x| + 2^−(k+1) (`Fl.model`),
   with binary32 at p = 24, k = 149. Still to do: a fast executable
   version of the spec proven equal to it, and native F32 checked against
   it bit for bit. The largest piece; recent Lean work (TorchLean's
   IEEE32Exec, FloatLib, Tunnell's FP) is the closest reference.
5. Running bounds (**done**: `Err.track`, `api/track.bend`) and `Approx`;
   compensated and exact-accumulator kernels.

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
