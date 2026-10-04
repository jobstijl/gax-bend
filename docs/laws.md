# Laws and their evidence

Every law in [`LAWS.bend`](../LAWS.bend) is listed here with its evidence
tag (ADR-001, amendment A2), the ring hypotheses it assumes, and the file
that proves it. `tools/gate.sh` re-checks all of it: `bend PROOF.bend` must
print ALL PROOFS CHECK, and every negative control in `tests/neg/` must fail.

**Status (2026-10-04):** 22 of 22 Layer-S laws proven. `LAWS.bend` is still
a DRAFT awaiting your review.

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

## Examples (`tests/`)

`tests/spec_pga3d.bend` checks gax's conventions on PGA3D over exact
integers, among them:
- the join sign e123 ∨ e032 = +e23;
- J_R(e123) = −e0;
- the signs of reverse, involute and conjugate;
- grade projection;
- canonical zeros.

## How the proofs were written

The large proof modules were expanded by a throwaway Python script from a
term-level shorthand: `gp_assoc.bend`, `inv.bend`, `rev.bend`, `gen.bend`
and `grade.bend`, and the case-checked flag identities in `flags.bend`.
That script is not part of this repository: it is not trusted, and nothing
depends on it. Every proof is plain Bend checked by the gate. The Phase 2
generator, written in Bend, will take over emitting the kernel proofs.
