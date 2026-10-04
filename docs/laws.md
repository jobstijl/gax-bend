# Laws and their evidence

Every law in [`LAWS.bend`](../LAWS.bend) is listed here with its evidence
tag (ADR-001, amendment A2), the ring hypotheses it assumes, and the file
that proves it. `tools/gate.sh` re-checks all of it: `bend PROOF.bend` must
print ALL PROOFS CHECK, and every negative control in `tests/neg/` must fail.

**Status (2026-10-04):** 22 of 22 Layer-S laws proven. `LAWS.bend` is
approved (the owner delegated the review to Claude).

## Scope of the Layer-S laws

Each law below holds:
- for **every dimension d and every diagonal signature** (each generator
  squares to +1, −1 or 0), because it is proven by induction on d;
- for **any scalar type `T`** with operations `add`, `mul`, `neg`, assuming
  only the listed ring laws.

The hypothesis names come from `src/ring.bend`:

| name | meaning |
|---|---|
| `add_assoc`, `add_comm` | addition is associative, commutative |
| `mul_assoc`, `mul_comm` | multiplication is associative, commutative |
| `dist_l`, `dist_r` | a(b + c) = ab + ac, (a + b)c = ac + bc |
| `neg_add` | −(a + b) = −a + −b |
| `neg_neg` | −(−a) = a |
| `neg_mul_l`, `neg_mul_r` | (−a)b = −(ab), a(−b) = −(ab) |
| `one_one` | 1·1 = 1 |
| `zero_l`, `add_inv` | 0 + a = a, a + (−a) = 0 (the normaliser only) |
| `unit_r` | a·1 = a (the normaliser only) |

Commutativity of multiplication is assumed only where a law needs it:
`reverse_gp` and `gp_scale_right`. So `gp_assoc`, distributivity,
`involute_gp` and the generator laws hold over noncommutative rings too.

## Layer S

| law | statement | assumes | tag | proof |
|---|---|---|---|---|
| `add_comm` | x + y = y + x | add_comm | proof | `proofs/add.bend` `Add.comm` |
| `add_assoc` | (x + y) + z = x + (y + z) | add_assoc | proof | `proofs/add.bend` `Add.assoc` |
| `sgn_compose` | grade signs compose by xor of (n, f, r) | neg_neg | proof | `proofs/sgn.bend` `Sgn.compose` |
| `involute_involute` | inv(inv x) = x | neg_neg | proof | `PROOF.bend`, from `Sgn.compose`, `Sgn.id` |
| `reverse_reverse` | rev(rev x) = x | neg_neg | proof | as above |
| `reverse_involute` | rev∘inv = inv∘rev = conjugate | neg_neg | proof | `Sgn.compose` |
| `gp_add_left` | (x + y)z = xz + yz | add_assoc, add_comm, dist_r, neg_add | proof | `proofs/gp.bend` `Gp.add_l` |
| `gp_add_right` | x(y + z) = xy + xz | add_assoc, add_comm, dist_l, neg_add | proof | `proofs/gp.bend` `Gp.add_r` |
| `gp_scale_left` | (c x) y = c (x y) | mul_assoc, dist_l, neg_mul_r | proof | `proofs/scale.bend` `Scale.gp_l` |
| `gp_scale_right` | x (c y) = c (x y) | mul_assoc, mul_comm, dist_l, neg_mul_r | proof | `proofs/scale.bend` `Scale.gp_r` |
| `gen_square` | e_i e_i = q_i (0 past the last generator) | one_one | proof | `proofs/gen.bend` `Gen.sq` |
| `gen_anticomm` | i ≠ j ⇒ e_i e_j = −(e_j e_i) | neg_neg | proof | `proofs/gen.bend` `Gen.ac` |
| `involute_gp` | inv(xy) = inv(x) inv(y) | neg_add, neg_neg, neg_mul_l, neg_mul_r | proof | `proofs/inv.bend` `Inv.gp` |
| `reverse_gp` | rev(xy) = rev(y) rev(x) | add_comm, mul_comm, neg_add, neg_neg, neg_mul_l, neg_mul_r | proof | `proofs/rev.bend` `Rev.gp` |
| `gp_assoc` | (xy)z = x(yz) | add_assoc, add_comm, mul_assoc, dist_l, dist_r, neg_add, neg_neg, neg_mul_l, neg_mul_r | proof | `proofs/gp_assoc.bend` `Gp.assoc` |
| `wedge_is_gp_zero` | x ∧ y = the geometric product of the zero metric | none | proof | `proofs/wedge.bend` `Wedge.gp0` |
| `wedge_assoc` | (x ∧ y) ∧ z = x ∧ (y ∧ z) | as gp_assoc | proof | `proofs/wedge.bend` `Wedge.assoc` |
| `vee_assoc` | (x ∨ y) ∨ z = x ∨ (y ∨ z) | as gp_assoc | proof | `proofs/wedge.bend` `Vee.assoc` |
| `lcomp_rcomp` | J_L(J_R x) = x | neg_neg | proof | `proofs/wedge.bend` `Comp.lr` |
| `rcomp_lcomp` | J_R(J_L x) = x | neg_neg | proof | `proofs/wedge.bend` `Comp.rl` |
| `rcomp_vee` | J_R(x ∨ y) = J_R x ∧ J_R y | neg_neg | proof | `proofs/wedge.bend` `Comp.rcomp_vee` |
| `wedge_grade` | a j-vector ∧ a k-vector is a (j+k)-vector | none | proof | `proofs/grade.bend` `Wedge.grade` |

## The general lemmas

These lemmas carry the sign flags of the spec. Each law above is one of them
with every flag false.

- **`Gp.assoc`:** (−1)^{n1} inv^{f1}((−1)^{n2} inv^{f2}(x) y) z equals
  (−1)^{n1+n2} inv^{f1⊕f2}(x) · (inv^{f1}(y) z).
- **`Inv.gp`:** (−1)^m inv(inv^f(x) y) equals inv^f(inv x) · ((−1)^m inv y).
- **`Rev.gp`:** (−1)^m inv^a rev((−1)^n inv^f(x) y) equals
  (−1)^{m+n} inv^a(rev y) · inv^{a⊕f}(rev x).
- **`Comp.rl`:** J_R and J_L with flags between them compose to a grade
  sign that depends on the parity of d.

## Ring identities by cancellation (`src/norm.bend`)

A term over `add`, `mul`, `neg` and `zero` is reified as a `Tm` whose
variables index an environment list. `Tm.flat` expands it into signed
monomials with sorted variables, and `Norm.left` cancels opposite monomials
in pairs. All of it is structural and runs in the checker on closed terms.

| law | statement | assumes | tag | proof |
|---|---|---|---|---|
| `Norm.zero` | `Norm.left(t) == []` ⇒ eval(t) = 0 | add_assoc, add_comm, zero_l, add_inv, mul_assoc, mul_comm, unit_r, dist_l, neg_add, neg_mul_l, neg_neg | proof | `proofs/norm.bend` |
| `Norm.eq` | `Norm.left(a − b) == []` ⇒ eval(a) = eval(b) | as `Norm.zero` | proof | `proofs/norm.bend` |
| `NormS.zero`, `NormS.eq` | as `Norm.zero`/`Norm.eq`, but flattening with an accumulator, merge-sorting the monomials and cancelling neighbours with a stack: O(n log n) | as `Norm.zero` | proof | `proofs/norm.bend` |
| `NormSH.zero`, `NormSH.eq` | the sorting form of `NormH` | as `NormH` | proof | `proofs/norm.bend` |
| `NormH.zero`, `NormH.eq` | the same over rings with a half: given h + h = 1 for a variable h, `NormH.left` lifts every monomial to the highest power of h, using m hᵏ = m hᵏ⁺¹ + m hᵏ⁺¹, then cancels | as `Norm.zero`, plus h + h = 1 | proof | `proofs/norm.bend` |

The method is complete for identities whose expanded monomials cancel
with coefficients ±1, which covers every polynomial identity: a
coefficient c is c copies of a monomial. `NormH` is complete for
identities over ℤ[½]: after lifting to a common power hᴺ, a term is zero
at h = ½ exactly when its monomials cancel. It is what CGA's null basis
needs (eo = ½(e₋ − e₊)). `Norm.left` is quadratic in the number of monomials; the generated
kernel proofs use `NormS`. Measured in the checker (bend-facts Q14):
4050 monomials take 18.7 s with `Norm` and 3.7 s with `NormS`. Uses: `tests/norm_identities.bend` (positive);
`tests/neg/norm_wrong.bend` claims (x + y)² = x² + y², and the checker
reports the two xy monomials left over.

## Generated kernels (Layer K)

Every kernel in `algebras/<name>/ops.bend` comes with two generated
certificates in `algebras/<name>/proofs.bend`, both tagged **proof**:

- **Mirror law** `K.ok`: `C.of_tree(spec(A.tree a, B.tree b)) == kernel(a, b)`.
  The kernel is the Layer-S operation, field by field, including the
  orientation signs of the kind layouts.
- **Support law** `K.supp`: the spec's result is zero outside the result
  kind, so no coefficient is dropped by the choice of result kind.

Both are proven by matching the operand records and `{==}`, over any `T`
and any operations: no ring law is used. Combined with the Layer-S laws
above, every algebraic law transfers to the kernels.

| algebra | kinds | kernels | of which sandwiches | zero laws | multiplications |
|---|---|---|---|---|---|
| VGA2D | 5 | 280 | 10 | 4 | 606 |
| VGA3D | 8 | 681 | 24 | 24 | 3941 |
| PGA2D | 10 | 1023 | 60 | 32 | 3848 |
| PGA3D | 11 | 1231 | 77 | 101 | 12277 |
| STA | 9 | 849 | 27 | 84 | 11190 |
| CGA3D (null basis) | 11 | 1219 | 44 | (in `.ok`) | 47041 |

The operations are gp, wedge, vee, lc, rc, dot, scalar_product,
commutator, anticommutator, add, sub (any two kinds) and neg, reverse,
involute, conjugate, dual (J_R) and undual (J_L). The inner products
follow gax's blade-pair definitions (`src/spec.bend`, "Inner products"):
per pair of grades r and s, lc keeps grade s − r (r ≤ s), rc grade r − s,
dot grade |r − s|, the scalar product grade 0. For PGA3D every result kind
of gp, wedge, vee, lc, rc, dot, scalar_product, commutator and
anticommutator equals gax's generated type (117, 102, 97, 88, 88, 115, 45,
85 and 109 pairs). `tests/inner_pga3d.bend` checks values on blades.

**Commutator and anticommutator.** gax's are halved: (xy − yx)/2 and
(xy + yx)/2. Layer S defines the doubled forms (`MV.commutator2`,
`MV.anticommutator2`), so no ring needs ½. Every coefficient of a doubled
form is even, so the generator halves it exactly (one of each pair of equal
monomials), and the kernel has integer coefficients. Its law `.ok` states
kernel + kernel = the doubled spec, field by field by `Norm.eq`, plus zero
laws as for sandwiches. Over a ring without 2-torsion that fixes the
kernel. The negative control `commutator_not_halved.bend` drops the
doubling.

**CGA3D, in gax's null basis** (ADR-004). Kinds are written over e1, e2,
e3, eo, e∞ (eo·e∞ = −1); the tree runs on e₊, e₋, with eo = ½(e₋ − e₊)
and e∞ = e₋ + e₊. Kernels have integer coefficients. Two kinds of law,
both tag **proof** given the normaliser's ring laws and h + h = 1:
- **`.ok`, one per kernel:** every null-basis coefficient of the spec
  (through the change of basis) equals the kernel's widened to the full
  basis (`to_mv`), so it is the mirror law and the support law in one. It is
  proven by one `NormSH.eqs`.
- **`.basis`, one per kind:** `of_tree(tree x) = x`, the change of basis
  itself.

Result kinds equal gax's for all 954 pairs (gp, wedge, vee, lc, rc, dot,
scalar product, commutator, anticommutator, sandwiches).
`tests/cga3d.bend` checks values over exact integers. The vee is the
negated diagonal one: e123oi = −e123₊₋. Dual and undual are not generated
for CGA3D (ADR-004).

**Sandwiches.** `V.transform.X(v, x)` is v x ~v (gax's `transform`), for
every versor kind V and every kind X:
- **The kernel is the quadratic form:** field c of v x ~v is
  Σ_j x_j Q_cj(v), each Q_cj a sum of ±v_a v_b. The generator reads the
  Q_cj off the spec's coefficients after cancellation, computes each
  product v_a v_b once, and then the entries and the fields. The cost is
  (#products + #entries) multiplications: 35 for a PGA3D motor on a
  point, where gax's plain kernel has 38 and its unit kernel 33.
- **Equality law** `.ok`: each field equals the spec's coefficient, by
  `Norm.eq`, and the generated `K.<kind>.cong` joins the fields into the
  record equality. Tag: **proof**, assuming the normaliser's ring laws.
- **Zero laws** `.zero_<blade>`, one per blade where the spec's tree has a
  coefficient outside the result kind, such as the grade-1 part of a
  motor acting on a point. Each states that the coefficient is zero in every
  commutative ring, proven by `Norm.zero` on the spec run at `T = Tm`.
  Tag: **proof**, assuming the normaliser's ring laws.
- **Result kind:** gax's rule applied to the support that survives
  cancellation. For PGA3D all 77 pairs agree with gax's generated types.
- **Prepared form:** `V.prepare.X(v)` is the matrix Q (one record per
  pair, `MotorPointMap`), and `V.X.apply(Q, x)` applies it: 13
  multiplications per point for a PGA3D motor. The law `.prepared` states
  `apply(prepare(v), x) = transform(v, x)`, by `{==}`, for every sandwich
  of every algebra (263 laws).
- **Example:** `tests/transform_pga3d.bend`, over exact integers, checks
  a translation, a half turn, a reflection and a moved plane.
- **Negative control:** `tests/neg/transform_support.bend` claims that the
  x coefficient of a moved point is zero.

What the certificates do not cover, per ADR-001 item 5:
- that the chosen result kind is the smallest one;
- that a missing kernel's product really is identically zero.

The generator decides both from the same symbolic run, but no proof backs
them yet.

## The PGA3D API (Layer A, `api/pga3d.bend`)

Over F32 nothing is provable (ADR-001 item 7), so these are property tests,
tag **f32-prop**, in `tests/pga3d_api.bend`:

| function | property | tolerance |
|---|---|---|
| `Motor.rotation(axis, θ)` | a quarter turn about the x axis moves (0, 1, 0) to (0, 0, 1) (right-handed) | 1e-4 |
| `Motor.translation` | moves the origin to (dx, dy, dz) | 1e-4 |
| `Motor.between.points` | carries the first point to the second | 1e-4 |
| `Motor.between.lines` | carries the first line to the second (both normalized) | exact here |
| `Line.exp`, `Motor.log` | log(exp B) = B for a screw; also at a half-angle of 1e-4 | 1e-5; 1e-7 |
| `Line.exp` | exp(B) = exp(B/2)² on both sides of the series boundary, and at 1e-4 | 1e-6 |
| `Motor.log` | exact on a pure translation | exact |
| `Motor.normalized` | m ~m = 1, the e0123 part included | 1e-6 |
| `Motor.sqrt` | sqrt(m)² = m | 1e-5 |
| `Motor.renormalize_fast` | one Newton step (3 − m~m)m/2: a unit motor scaled by 1.001 returns to m~m = 1 | 1e-5 |

The CGA3D API (`api/cga3d.bend`) is tested the same way in
`tests/cga3d_api.bend` (f32-prop, rounded to 1e-4):
- a right-handed quarter turn about z;
- a translation;
- the squared distance −2 P·Q of two points;
- a point on a sphere has P·S = 0;
- incidence survives a motion: P·S stays below 1e-4 after a turn and a
  translation.

`Normed<A>` (gax's `Unit<M>`; Base already has a `Unit`) is the
certificate. Over F32 it is a trust boundary: only the API's constructors
make one.

## Negative controls (`tests/neg/`)

Each one must fail to check. The gate fails if any passes.

| file | false claim | family |
|---|---|---|
| `gp_comm.bend` | the geometric product is commutative (over any commutative ring) | product |
| `assoc_wrong_flag.bend` | associativity with the inner sign dropped (closed 2D example) | associativity |
| `reverse_not_auto.bend` | rev(e1 e2) = rev(e1) rev(e2) | reverse |
| `involute_one_side.bend` | inv(e1 e2) = inv(e1) e2 | involution |
| `rcomp_not_involution.bend` | J_R(J_R e1) = e1 in the plane | complements |
| `metric_sign.bend` | e1 e1 = +1 when e1 squares to −1 | metric |
| `wedge_grade_off.bend` | e1 ∧ e2 is a 3-vector | grades |
| `kernel_sign.bend` | a PGA3D kernel with one sign flipped equals the spec | kernels |
| `norm_wrong.bend` | (x + y)² = x² + y² over any commutative ring | normaliser |
| `normh_wrong.bend` | h a + h h a = a given h + h = 1 | normaliser with ½ |
| `transform_support.bend` | a motor moves a point to one with x = 0 | sandwiches |
| `transform_kernel_sign.bend` | the PGA3D motor-on-point kernel with one sign flipped in its weight entry equals the spec | sandwich kernels |
| `commutator_not_halved.bend` | the line-line commutator kernel equals xy − yx (not its half) | halved products |

## Examples (`tests/`)

`tests/spec_pga3d.bend` checks gax's conventions on PGA3D over exact
integers, among them:
- the join sign e123 ∨ e032 = +e23;
- J_R(e123) = −e0;
- the signs of reverse, involute and conjugate;
- grade projection;
- canonical zeros.

## How the proofs were written

`proofs/base.bend`, `leaf.bend`, `add.bend` and `sgn.bend` are written by
hand. The large modules are written by the proof writer in `gen/proofs/`, a
Bend program that assembles them from a term-level vocabulary
(`gen/proofs/dsl.bend`):
- `gp.bend` and `gp_assoc.bend`: the geometric product and its associativity;
- `wedge.bend`, `scale.bend`, `inv.bend`, `rev.bend`, `gen.bend` and
  `grade.bend`;
- `flags.bend`: every Bool flag identity the others use, each proven by
  checking all cases.

The proof writer is not trusted: what it writes is plain Bend that the gate
checks like any other proof. `tools/regen.sh` rewrites the modules, and the
gate fails when the committed ones differ from what it writes
(`tools/regen.sh --check`). The port from the throwaway Python scripts that
first expanded these proofs was checked by byte-identical output for all
nine modules.
