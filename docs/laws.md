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

| algebra | kinds | kernels | multiplications |
|---|---|---|---|
| VGA2D | 5 | 149 | 218 |
| VGA3D | 8 | 347 | 1445 |
| PGA2D | 10 | 528 | 1519 |
| PGA3D | 11 | 624 | 4787 |
| STA | 9 | 435 | 4168 |

The operations are gp, wedge, vee, add, sub (any two kinds) and neg,
reverse, involute, conjugate, dual (J_R) and undual (J_L).

What the certificates do not cover, per ADR-001 item 5:
- that the chosen result kind is the smallest one;
- that a missing kernel's product really is identically zero.

The generator decides both from the same symbolic run, but no proof backs
them yet.

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
