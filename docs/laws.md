# Laws and their evidence

Every law in [`LAWS.bend`](../LAWS.bend) is listed here with its evidence
tag (ADR-001, amendment A2), the ring hypotheses it assumes, and the file
that proves it. `tools/gate.sh` re-checks all of it: `bend PROOF.bend` must
print ALL PROOFS CHECK, and every negative control in `tests/neg/` must fail.

**Status (2026-10-04):** 24 of 24 Layer-S laws proven. `LAWS.bend` is
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
| `transform_gp` | ~m m = n ⇒ (m x ~m)(m y ~m) = n (m (x y) ~m): a versor acts as a homomorphism, up to its norm | as gp_assoc, plus mul_comm | proof | `proofs/versor.bend` `Versor.gp` |
| `transform_compose` | a (b x ~b) ~a = (a b) x ~(a b) | as gp_assoc, plus add_comm, mul_comm | proof | `proofs/versor.bend` `Versor.compose` |

**About `transform_gp`.** The chain is m x (~m m) y ~m by associativity,
then n times y ~m. That last step holds because y ~m is a product, and
every product is a canonical tree (no level N{zero, zero}; A3):
`Gpf.canon`, with `Add.canon` and `Mk.canon` behind it. On a canonical
tree a scalar acts by scaling (`Gp.scalar`). gax derives the same factor
per algebra, modulo the versor conditions (its `law-factors.md`); here it
is one theorem for every dimension and signature. The other products' laws
(∧, ∨, contractions) are not stated yet.

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

## Equivariance (`algebras/<name>/equiv.bend`, gax family D)

A versor's sandwich commutes with the products, up to a factor:
  (m >> a) op (m >> b) = ‖m‖² · (m >> (a op b)),
where ‖m‖² is the scalar part of m ~m. Each law is a generated per-kernel
**proof**. Where m ~m can have another part (PGA3D motor: e0123; STA even:
the pseudoscalar), the law takes that part being zero as its hypothesis:
the condition that makes m a versor (gax's sym/ideal tag). The generator
(`gen/equiv.bend`) divides the difference of the two sides by that part r.
That gives l with lhs = rhs + l·r, a ring identity the normaliser checks
(`proofs/equiv.bend`, `Rel.eqs`), and r = 0 closes it.

| algebra | versor | laws (op: a, b → c) | condition | checked in |
|---|---|---|---|---|
| PGA3D | Motor | ∨: Point,Point→Line; ∨: Point,Line→Plane; ∧: Plane,Plane→Line; ∧: Plane,Line→Point; ⌋: Plane,Point→Line; ·: Line,Plane→Plane | e0123 of m ~m = 0 | 9 s |
| PGA2D | Motor | ∨: Point,Point→Line; ∧: Line,Line→Point; ⌋: Line,Point→Line | none | 1 s |
| VGA3D | Rotor | ∧: Vector,Vector→Bivector; ∨: Bivector,Bivector→Vector; ⌋: Vector,Bivector→Vector; ·: Bivector,Vector→Vector | none | 1 s |
| STA | Even | ∧: Vector,Vector→Bivector; ⌋: Vector,Bivector→Vector; ∨: Trivector,Trivector→Bivector | e0123 of m ~m = 0 | 29 s |

The set is curated: the joins, meets and contractions of the geometric
kinds. Under even versors the factor is +‖m‖² throughout, matching gax's
law-factors table. Negative controls: `tests/neg/equiv_factor.bend` (the
PGA3D join without ‖m‖²) and `tests/neg/equiv_condition.bend` (the same
law without its condition) both fail. gp equivariance holds in general at
Layer S (`transform_gp`).

**Every kind pair** (`algebras/<name>/equiv_all.bend`, ADR-013). For each
listed versor kind, every ∧, ∨, ⌋, ⌊ and · of two single-grade kinds
whose product is not identically zero. Operands and result must be kinds
the versor's generated sandwich maps to themselves (`Eq.closed`). Kinds it
does not are left out: under a general Motor a PGA Direction comes out
typed as a Point, and a PGA3D scalar as a Motor (m ~m has an e0123 part);
so are STA's pseudoscalar under Even and Odd and CGA3D's and CSTA's
Twist under Vector. The factor is +‖m‖², except −‖m‖² on ∨ for odd versors in even
dimensions.

| algebra | versors | laws | with −‖m‖² | condition | checked in |
|---|---|---|---|---|---|
| VGA2D | Rotor, Vector | 30 | 4 (Vector ∨) | none | 1 s |
| VGA3D | Rotor, Odd | 64 | 0 | none | 8 s |
| PGA2D | Motor, Flector | 58 | 0 | none | 2 s |
| PGA3D | Motor, Flector | 80 | 10 (Flector ∨) | e0123 of m ~m = 0 | 46 s |
| STA | Even, Odd | 36 | 3 (Odd ∨) | e0123 of m ~m = 0 | 355 s |
| STAP | Vector | 81 | 0 | none | 51 s |
| CGA3D | Vector | 84 | 0 | none | 98 s |
| CSTA | Vector | 119 | 26 (Vector ∨) | none | 752 s |

In the null-basis algebras (CGA3D, CSTA) the generator decides each
law's sign by evaluation modulo a prime (ADR-013); the checker proves
the law. In STAP, CGA3D and CSTA the versor is a single vector, for which
m ~m = m² is a scalar. A general even or odd element there has several more parts in
m ~m, so its laws need several conditions, and the generator reduces by
one. Every versor is a product of vectors, and `Equiv.compose`
(`proofs/equiv.bend`) proves that equivariance composes: if the sandwiches
by a and by b carry op up to ca and cb, their composite carries it up to
ca cb. With `Versor.compose` the vector laws extend to any product of
vectors, applied as successive sandwiches.

## Exact integers (`src/int.bend`)

| law | statement | assumes | tag | proof |
|---|---|---|---|---|
| Nat semiring | + and × associative and commutative, × distributes, 0 and 1 units | nothing | proof | `proofs/nat.bend` |
| Int ring | every law `src/ring.bend` names that the normaliser takes (`Int.r.*`): + associative, commutative, 0, inverses; × associative, commutative, 1; distributivity; −(a + b), (−a)b, −(−a) | nothing | proof | `proofs/int.bend` |
| Int order | `Int.pos` closed under + and ×; \|a\| ≥ 0; \|a + b\| ≤ \|a\| + \|b\|; \|ab\| = \|a\|\|b\|; \|−a\| = \|a\|; \|0\| = 0 | nothing | proof | `proofs/int.bend` |

The proofs write every integer as a difference of naturals. `sub_nat`
ignores a common summand, and every pair is its normal form plus one, so
each Int law becomes a Nat identity. `tests/int_ring.bend` instantiates the
generic normaliser at T = Int with these laws and proves (x + y)(x − y) =
x² − y² for all integers. Int is thus a concrete ordered commutative ring
for every theorem stated over one. That includes the rounding-error
theorem, once a rounding with ε > 0 exists, which needs the dyadic numbers
built on Int.

## Dyadic numbers (`src/dyadic.bend`)

| law | statement | assumes | tag | proof |
|---|---|---|---|---|
| Dy ring | every law the normaliser takes (`Dy.r.*`) | nothing | proof | `proofs/dyadic.bend` |
| Dy order | `Dy.pos` closed under + and ×; \|x\| ≥ 0; \|x + y\| ≤ \|x\| + \|y\|; \|xy\| = \|x\|\|y\|; \|−x\| = \|x\| | nothing | proof | `proofs/dyadic.bend` |

A dyadic is an integer or ±(2k + 1)/2^(e + 1): one spelling per value, so
the laws are equalities. The proofs use pairs (m, e) for m/2^e, equivalent
when m₁2^e₂ = m₂2^e₁:
- the normaliser `Dy.of` keeps the value (`Of.val`);
- equivalent pairs normalise alike (`Of.eq`, by lexicographic induction on
  the exponents, with parities);
- a dyadic's own pair normalises back to it (`Of.self`).

The nested laws (associativity, distributivity) are Int identities modulo
the values of the inner normal forms. They are proven with the generic
normaliser at T = Int (`Rel.many`, proofs/equiv.bend), with multipliers
worked out by hand; a wrong multiplier fails. `tests/dyadic_ring.bend`
instantiates the normaliser at T = Dy, and a generated kernel error law at
T = Dy for any ε ≥ 0. So binary floating point's exact values form a
concrete ordered ring for every theorem stated over one.

## Rounding (`src/round.bend`)

| law | statement | assumes | tag | proof |
|---|---|---|---|---|
| `Round.rel` | for every dyadic z and p ≥ 1: \|trunc_p(z) − z\| ≤ 2^(1−p) \|z\| (truncation to p significant bits, toward zero) | nothing | proof | `proofs/round.bend` |
| `Rne.rel` | for every dyadic z and p ≥ 1: \|rne_p(z) − z\| ≤ 2^(−p) \|z\| (round to nearest, ties to even: IEEE's significand rounding, unit roundoff u = 2^−p) | nothing | proof | `proofs/round.bend` |
| `Rfix.rel` | rounding to the grid 2^−k (nearest, ties to even): \|rfix_k(z) − z\| ≤ 2^−(k+1) | nothing | proof | `proofs/round.bend` |
| `Fl.model` | a format rounding to p bits in its normal range and to the grid 2^−k below: \|fl(x) − x\| ≤ 2^−p \|x\| + 2^−(k+1), whatever the range test decides. Binary32 is p = 24, k = 149: u = 2⁻²⁴, η = 2⁻¹⁵⁰ | nothing | proof | `proofs/round.bend` |
| `L.f32`, `L.mul32`, `L.add32` | the fast binary32 rounding (`src/fast.bend`, Base's native Nat operations) equals `Dy.f32`; the fast product and sum, rounded, equal `Dy.f32` of the exact product and sum. So `Fl.model` holds for the executable spec | nothing | proof | `proofs/fast.bend` |

Truncation halves the magnitude n until it is below 2^p, keeping n = q 2^s
+ r, 2^s = r + 1 + w_r and, once shifted, q = 2^(p−1) + w_q (`Inv`, true
for any fuel). From these, n = r 2^(p−1) + c for an explicit c, an
identity the normaliser checks at T = Int. So the rounding error r is at
most 2^(1−p) of n.

Round to nearest reuses the truncation. When 2r > 2^s, or on a tie with
q odd, it rounds up to (q + 1)2^s, so the error e is at most 2^(s−1). The
comparison yields a witness w with 2^s = 2e + w either way (`Cmp.dn`,
`Cmp.up`), so n = e 2^p + c again. A small normaliser for naturals
(`NatN`, naturals embedded in Int) checks these identities.

So p-bit arithmetic on dyadics, truncating or rounding to nearest, meets
the standard model, and every theorem above holds for it with no
hypothesis left. `tests/round_err.bend` instantiates VGA2D's
vector-product error law in both, for every p. It also checks that
neither ε can be halved:
- at p = 2, z = 11 truncates to 8, an error of 3/11 of |z|, more than 2⁻²;
- z = 5 rounds to nearest to 4 (a tie, to even), an error of 1/5, more
  than 2⁻³.

`Fl.model` adds gradual underflow. Below the normal range the format
rounds to a fixed grid, an absolute error of at most half its spacing, so
the format meets the model of `Err.bound_u` with η = 2^−(k+1).
`tests/f32_model.bend` instantiates `Err.bound_u` in such arithmetic for
every format. That is the rounding-error theorem for binary32's rounding
(p = 24, k = 149), with no hypothesis left. Overflow stays outside the
model, so the theorem covers executions whose results are finite.

The spec's halving, parity and comparison recurse, so it takes n steps at
run time. `src/fast.bend` computes the same functions with Base's native
Nat operations, and `proofs/fast.bend` proves each equal to its original,
from four primitive links (`L.half`, `L.even`, `L.lt`, `L.monus`). The
hardware link is measured, not proven: `tests/f32_native.bend` compares
native `F32.mul` and `F32.add` with the executable spec, bit for bit. Over
100 000 products, 4 253 of them subnormal, and 46 829 sums with
cancellation, it finds no difference; a control with the low bit flipped
mismatches on every operation. The samples stay within run-time Nat
(2⁴⁸): exponents down to 2⁻⁸⁶, and sums of exponents at most 23 apart.

## Big numbers (`src/big.bend`, ADR-007)

Big naturals are limbs in base 2h, least significant first. Every law
holds for any h ≥ 1; at run time h = 2²³, so limb products with carries
stay below 2⁴⁸. Each operation commutes with the value map into Nat, for
limbs below the base (`Bn.ok`), and keeps them there.

| law | statement | assumes | tag | proof |
|---|---|---|---|---|
| `Cmp.lt` | `Bn.lt(a, b)` is `val a < val b` | limbs below 2h | proof | `proofs/big.bend` |
| `Add.val`, `Add.ok` | `val(addc(a, b, c)) = [c] + val a + val b`; limbs stay below 2h | `Add.ok`: limbs below 2h | proof | `proofs/big.bend` |
| `Mul.val`, `Mul.ok` | `val(mul(a, b)) = val a · val b`; limbs stay below 2h (the carry bound `Cy.bound`) | `Mul.ok`: limbs below 2h | proof | `proofs/big.bend` |
| `Sub.val`, `Sub.ok` | `val(subb(a, b, br)) + [br] + val b = val a` | `val a ≥ val b + [br]`, limbs below 2h | proof | `proofs/big.bend` |
| `Half.val`, `Even.val`, `Shl.val`, `Pow2.val`, `Of.val` | halving, parity, b·2ᵏ, 2ᵏ and conversion from Nat commute with the value map | conversion: n < B² | proof | `proofs/big.bend` |
| `Fuel.go` | the spec's rounding loop gives one result for every fuel f with n < 2^(p+f) | nothing | proof | `proofs/big.bend` |
| `Of.lk`, `Rne.mag`, `Rfix.mag` | the limb rounding loop (fuel h·limbs, `Val.lt`: val < 2^(h·limbs)) tracks `Tr.of`; its rounded magnitude is `Tr.near(Tr.of(p, val n))`, and on the grid `Tr.near(Fx.go(s, val n))` | limbs below 2h | proof | `proofs/big.bend` |
| `Bd.mul.lk`, `Bd.add.lk` | big dyadics (sign, limbs, exponent) multiply and add as their values do; sums align to the larger exponent | sums: limbs below 2h | proof | `proofs/big.bend` |
| `Norm.val`, `Norm.nf` | normalising keeps the value and yields its normal form's denominator and numerator | nothing | proof | `proofs/big.bend` |
| `F32.lk`, `F64.lk` | `Bd.f32(x)` is `Dy.f32(val x)`; `Bd.f64(x)` is `Dy.f64(val x)` (53 bits from 2⁻¹⁰²², the grid 2⁻¹⁰⁷⁴) | limbs below 2h | proof | `proofs/big.bend` |
| `Mul32.lk`, `Add32.lk`, `Mul64.lk`, `Add64.lk` | the big binary32/binary64 product and sum are the format's rounding of the exact one, at any operand size, so `Fl.model` holds (binary64: u = 2⁻⁵³, η = 2⁻¹⁰⁷⁵) | limbs below 2h | proof | `proofs/big.bend` |
| `Dot.lk`, `Dot32.lk`, `Dot64.lk` | `Bd.dot` holds the exact dot product (a Kulisch accumulator); rounded once, it is the correctly rounded dot product, with error at most u·\|x·y\| + η | limbs below 2h | proof | `proofs/big.bend` |

The proofs check in about a second. Two tests run them. `tests/big_f32.bend`
compares native F32 with big binary32 bit for bit over the whole finite
range. It finds no difference in 20 000 products, 1 768 of them
subnormal, and 20 000 sums across any exponent gap. In 2 000 dot products
of length 8, a plain F32 loop differs from the correctly rounded result
230 times. `tests/big_f64.bend` matches 300 Python-computed binary64
products and sums: 42 subnormal products, 21 underflows to zero, 100
cancelling sums. Each test has a control that fails on every operation.

## Posits (`src/posit.bend`, ADR-008)

Bounded posits (b-posits, Jonnalagadda, Thotli and Gustafson 2026): the
regime field stops at rs bits, so every value keeps at least
p0 = n − es − rs significant bits. A format is (p0, 2^es, rs); b-posit32
is (21, 32, 6), range 2^±192, 21 to 25 bits.

| law | statement | assumes | tag | proof |
|---|---|---|---|---|
| `Pz.model` | \|fl(x) − x\| ≤ 2^−p0 \|x\| + minpos for every x with \|x\| ≤ maxpos, minpos = 2^−bias (1 + 2^−(p0−1)); for every format | nothing beyond \|x\| ≤ maxpos | proof | `proofs/posit.bend` |
| `Ulp.mono` | 2^−a ≥ 2^−(a+w): more precision never loosens the bound | nothing | proof | `proofs/posit.bend` |
| `Pz.lk` | the run-time rounding on big dyadics (`Pz.bfl`) is the spec `Pz.fl` | limbs below 2h | proof | `proofs/posit.bend` |
| `Pmul.lk`, `Padd.lk`, `Quire.lk` | b-posit products and sums, and the quire (the exact dot product `Bd.dot`, rounded once), are the format's rounding of the exact result | limbs below 2h | proof | `proofs/posit.bend` |
| `Dec.all` | every positive pattern q < 2^(n−1) decodes (`Pz.dec`) to the value of its field triple, the q-th: (2^fb + fr) 2^(rb g + ee) / 2^(bias + fb) | rs ≥ 1 | proof | `proofs/posit4.bend` |
| `Enc.pat` | the encoder (`Pz.enc`) writes back the pattern of any big dyadic worth a triple's value, in any spelling | limbs below 2h | proof | `proofs/posit5.bend` |
| `Succ.val` | the pattern after q decodes to q's value plus one unit in q's last place, through carries into the exponent and the regime | q is not the largest pattern | proof | `proofs/posit4.bend` |
| `Std.rnd` | b-posit rounding is the standard's rounding of the bit string: for x in [minpos, maxpos] between pattern q and q + 1, `Pz.fl` x is the value of q + 1 when guard and (sticky or q odd), else of q | p0 ≥ 2, bias ≥ p0 (b-posit32: 21, 192) | proof | `proofs/posit3.bend`, `proofs/posit4.bend` |

The spec rounds to nearest, ties to even, at the scale's precision
p0 + (rs − regime length), and saturates at minpos and maxpos. The
posit standard defines rounding on the bit string instead; `Std.rnd`
proves the two the same for every format with p0 ≥ 2 and bias ≥ p0.
The proof runs through the patterns: the field triples, stepped through
by carries (`Fld.next`), have patterns 0, 1, …, 2^(n−1) − 1
(`Nth.pat`, with `Pat.last` at the top); the decoder reads each back
(`Dec.val`, by the four regime cases and the regime run `Run.ok`); and
within a class `Pz.fl` rounds n = a 2^s + t at a's precision exactly as
the guard and sticky bits say (`Fl.at`, from `Rn.at`: the rounding
loop stops at shift s with quotient a and remainder t).
`tests/bposit.bend` also checks the agreement at b-posit32, against an
independent Python reference (`tools/bposit_cases.py`): 400 products and
sums, 49 of them saturating, 800 decode–encode round trips and 40 quire dot products
of length 8. All match; the control fails on all 1 640 checks. The
reference first showed that minpos is pattern 1, 2^−192 (1 + 2^−20), not
2^−192, which is the all-zero pattern, zero. The spec was wrong there for
five saturating products, and was fixed. Above maxpos the format
saturates, outside the model, as IEEE overflow is.

## Error-free transformations (`proofs/eft.bend`, `proofs/eft2.bend`, `proofs/eft3.bend`, ADR-009, ADR-010)

On integers rounded to p significant bits by the loop of `src/round.bend`
(any p; a binary format's values are integers over 2^k):

| law | statement | assumes | tag | proof |
|---|---|---|---|---|
| `Sc.near`, `Sc.pow` | R(n 2^g) = R(n) 2^g | nothing | proof | `proofs/eft.bend` |
| `G.le`, `RF` | m 2^j with m <= 2^p is representable (R fixes it); so is every rounded value | nothing | proof | `proofs/eft.bend` |
| `Near` | no representable c is closer to n than R(n) | c representable | proof | `proofs/eft.bend` |
| `Mono.lo`, `Mono.hi` | rounding never crosses a representable value | c representable | proof | `proofs/eft.bend` |
| `Sterbenz` | b <= a <= 2b, both representable: a - b is representable | nothing else | proof | `proofs/eft.bend` |
| `LA`, `LA.d` | the error of a rounded sum or difference of representable values is representable | nothing else | proof | `proofs/eft.bend` |
| `Fast2Sum`, `TwoSum` | s = RN(a + b), z = RN(s - a), t = RN(b - z) give s + t = a + b when \|b\| <= \|a\|; TwoSum is Fast2Sum on the magnitude-sorted pair, exact for all a, b | a, b representable | proof | `proofs/eft.bend` |
| `FlL`, `DFast2Sum`, `DTwoSum` | a binary format (p = 1 + p1, normal from 2^-emin, grid 2^-(emin + p1)) rounds N / 2^k to RN(N) / 2^k, so Fast2Sum and TwoSum are exact in the format; `F32.Fast2Sum`, `F32.TwoSum` instantiate binary32 | A, B representable | proof | `proofs/eft.bend`, `tests/df32_exact.bend` |

| `Split` | Veltkamp: g = RN(C a), d = RN(a - g), hi = RN(g + d), lo = RN(a - hi) with C = 2^s + 1 give lo = a - hi exactly, so hi + lo = a, at any precision and any s | a representable | proof | `proofs/eft2.bend` |
| `V.hi.grid`, `V.ah.le`, `V.lo.le` | for a in [2^(p-1), 2^p) and 2^p = 2^r 2^s: hi = Ah 2^s with Ah <= 2^r, and 2 \|lo\| <= 2^s | a normalised | proof | `proofs/eft2.bend` |
| `TwoProd` | Dekker: pi = RN(a b), e1 = RN(RN(ah bh) - pi), e2 = RN(e1 + RN(ah bl)), e3 = RN(e2 + RN(al bh)), e = RN(e3 + RN(al bl)) give pi + e = a b, for p = 2s, s >= 2 | a, b representable | proof | `proofs/eft2.bend` |
| `TwoProd.odd` | the same at p = 2s − 1, s ≥ 3 (binary64: s = 27) | a, b representable | proof | `proofs/eft3.bend` |
| `DRf.split`, `DTwoProd` | the same in dyadic arithmetic: the split in a binary format with gradual underflow; Dekker's product in binary rounding with no exponent bounds. `F32.Split` instantiates binary32 for every value, subnormals included; `F32.TwoProd` instantiates p = 24, s = 12, so binary32 barring underflow and overflow | A, B representable | proof | `proofs/eft2.bend`, `tests/df32_exact.bend` |
| `DTwoProd.odd`; `F64.Split`, `F64.TwoProd` | the binary64 instances: the split with C = 2^27 + 1 for every binary64 value, subnormals included; Dekker's product at 53 bits, barring underflow and overflow | A, B representable | proof | `proofs/eft3.bend`, `tests/big_f64.bend` |
| `DW1.int`, `DW1.gen` | DWTimesDW (Algorithm 10): for xh = ±A 2^(Dx+1) with 2^(p−1) ≤ A < 2^p and \|xl\| ≤ 2^Dx, y likewise, \|zh + zl − xy\| (1 + u)² ≤ 5u² \|xy\| (Muller–Rideau, Theorem 2.6). The cases: xh yh ≥ 2 from \|η\| ≤ 9u² (`Case.big`); xh yh < 2 by the sub-cases on \|cl2\|, \|tl1\|, \|tl2\|, 4\|η\| ≤ 20u² (`Small.abs`); xh = 1 or yh = 1, \|η\| ≤ 4u² (`Case.one`) | p ≥ 6, ties to even, xl, yl representable, no exponent bounds | proof | `proofs/dw.bend` |
| `Tie` | an odd n with 2^p < n < 2^(p+1) rounds to a multiple of 4 (ties to even) | n odd | proof | `proofs/dw.bend` |
| `F32.DWTimesDW` | the binary32 instance, p = 24 | barring underflow and overflow | proof | `tests/df32_exact.bend` |
| `F2.bin` | Fast2Sum is exact when \|a\| >= 2^(p−1) 2^k and \|b\| < 2^p 2^k (b in a's binade or below), not only for \|b\| <= \|a\| | a, b representable | proof | `proofs/dwadd.bend` |
| `AccDW.gen` | AccurateDWPlusDW (Algorithm 6): for x, y as in `DW1.gen`, \|zh + zl − (x + y)\| (1 − 4u) <= 3u² \|x + y\| (Joldes–Muller–Popescu, Theorem 3.1). Cases: xh + yh = 0 (`C0`), Sterbenz (`C1`), xh + yh <= 2 − 4u (`C2a`) or above (`C2b`) | p ≥ 6, xl, yl representable, no exponent bounds | proof | `proofs/dwadd.bend` |
| `AccDW.simp` | 3u²/(1 − 4u) < 3u² + 13u³ | p ≥ 6 | proof | `proofs/dwadd.bend` |
| `F32.AccDW` | the binary32 instance, p = 24 | barring underflow and overflow | proof | `tests/df32_exact.bend` |

Both double-word bounds are also checked exactly on 20 000 sampled pairs
(`tests/df32_exact.bend`).

## Dual numbers (`src/dual.bend`, ADR-006)

| law | statement | assumes | tag | proof |
|---|---|---|---|---|
| Dual ring | every law `src/ring.bend` names that the normaliser takes, for T[ε]/(ε²) (`Dual.r.*`) | T a commutative ring (the same laws) | proof | `proofs/dual.bend` |

Each law is two identities over T, one per part, proven by the
normaliser. `tests/dual_map.bend` runs the normaliser at T = Dual⟨Int⟩. It
also extracts the 4×4 matrix of a PGA3D motor's action on points by
running the kernel with ε on each coordinate, and checks that the matrix
times a point equals the kernel on it.

## Rounding error (`src/err.bend`, ADR-005)

| law | statement | assumes | tag | proof |
|---|---|---|---|---|
| `Err.bound` | for every term t: \|fl(t) − eval(t)\| ≤ h(k(t)) · absev(t), with h(k) = (1+ε)ᵏ − 1, k the roundings on the worst path (an add counts 1 + max, a product 1 + sum), absev the sign-stripped evaluation | the ring laws of `Norm.zero`; an order given by a positivity predicate closed under + and ×, with \|·\| nonnegative, the triangle inequality, \|ab\| = \|a\|\|b\|, \|−a\| = \|a\|, \|0\| = 0; a rounding function with \|rnd(x) − x\| ≤ ε\|x\| | proof | `proofs/err.bend` |
| `Err.bound_u` | with underflow: \|fl(t) − eval(t)\| ≤ h(k(t)) · absev(t) + D(t), where additions round by rnda and products by rndm, and D (`Err.D`) adds η_a or η_m at each rounding and carries the children's D through (1+ε) | as `Err.bound`, but \|rnda(x) − x\| ≤ ε\|x\| + η_a and \|rndm(x) − x\| ≤ ε\|x\| + η_m, with η_a, η_m ≥ 0 | proof | `proofs/err.bend` |
| `D.pos` | D(t) ≥ 0 | as above | proof | `proofs/err.bend` |
| `Err.track` | \|fl(t) − eval(t)\| (1 − h) ≤ h · Â, with Â the negation-free term computed with fadd, fmul at \|leaves\|: a bound from computed quantities | as `Err.bound`, plus \|\|x\|\| = \|x\|, x ≤ \|x\|, and 1 − h(k) ≥ 0 | proof | `proofs/err.bend` |
| `Ev.le` | \|eval(t)\| ≤ absev(t) | as above | proof | `proofs/err.bend` |
| `H.add` | h(a + b) = h(a) + h(b) + h(a)h(b) | ring laws | proof | `proofs/err.bend` |

Every generated kernel field is a term, so the theorem bounds the rounded
evaluation of every kernel at once. It holds for any rounding functions
satisfying the model. For binary32, η_a = 0 with gradual underflow and
2⁻¹²⁶ with subnormals flushed; η_m is 2⁻¹⁵⁰ or 2⁻¹²⁶ respectively. With
η_a = η_m = 0, D(t) is 0. The model holds only for results within the
format's range, so both theorems describe executions without overflow.
Native F32 meets the model by hypothesis, which `tests/err_measure.bend`
samples. The software float is to meet it by proof (numerics.md, order of
work). The proof writer is `gen/proofs/err.bend`. Breaking `Err.D` (η_a
in place of η_m in the product case) makes the check fail. A negative
control in the gate needs a concrete rounding: the dyadics now give the
ring (proofs/dyadic.bend), and a proven rounding on them is the next step.

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

A third certificate, in `algebras/<name>/err.bend`, bounds the kernel's
rounding error (**proof**):

- **Error law** `K.err`: for every output field i,
  |K(fadd, fmul)(a, b)ᵢ − K(a, b)ᵢ| ≤ h(kᵢ) · K(add, mul, id)(|a|, |b|)ᵢ.
  Here kᵢ is field i of the kernel run in the depth semiring on Nat
  (`E.Err.dadd`, `E.Err.dmul`), the absolute size is the kernel run on
  |inputs| with neg the identity, and fadd, fmul are any operations within
  ε of exact (`E.Ord.Rel`). All three sides are the generated kernel
  itself at other instantiations, so the bound is computable at run time
  by the same code.

The proof matches the operand records and calls `Err.fields` on the
kernel run over `N.Tm` (the kernel's own terms). The checker's
conversion then identifies each instantiation with the term's
evaluation. Unary kernels that only negate are exact and have no law;
that leaves 7189 laws. Each kernel also has the underflow law
(`name.erru`, from `Err.fields_u`): every field within h(k)·(its size)
plus D, the absolute term of `Err.bound_u`, for any η_a and η_m, so for
binary32 with η = 2⁻¹⁵⁰ and b-posits with η = minpos. That is 7189 more.
Both check in about four minutes (CSTA: 145 s, was 94 s without the
underflow laws). Giving the law the wrong terms (operands swapped) fails.

A fourth certificate, in `algebras/<name>/track.bend`, is the kernel's
tracked bound (**proof**, `K.track`, from `Err.fields_t` and `Err.track`):
for every output field i with h(kᵢ) ≤ 1,
|K(fadd, fmul)(a, b)ᵢ − K(a, b)ᵢ| · (1 − h(kᵢ)) ≤ h(kᵢ) · Âᵢ, with
Â = K(fadd, fmul, id)(|a|, |b|), the kernel itself at computed
operations on |inputs|. It is the bound `api/track.bend` computes at run
time, stated per kernel. 7189 laws, checked in 2 s (VGA2D) to 124 s
(CSTA), in every gate tier.

A fifth, in `algebras/<name>/lin.bend`, is linearity (gax family B,
**proof**): K(a + a′, b) = K(a, b) + K(a′, b) and K(c·a, b) = c·K(a, b)
(`lin_a`, `sc_a`), and the same in b (`lin_b`, `sc_b`), field by field,
by the normaliser (`proofs/lin.bend`, `Lin.eqs`). Sums are field-wise
(`A.plus`), since the add kernel can return a wider kind. Which operands
get laws:
- the products are linear in both operands;
- add and sub are linear only in both at once, so they have none;
- a sandwich is linear in what it moves (`lin_b`, `sc_b`), not in its
  versor;
- unary kernels are linear in their operand.

22 806 laws. They check in 4 s (VGA2D) to 204 s (STAP); CGA3D's (about
6 minutes) and CSTA's (about 30) run in the slow tiers. Negative
controls: `tests/neg/lin_add_one_side.bend` (add linear in one operand)
and `tests/neg/lin_transform_versor.bend` (a sandwich homogeneous in its
versor) both fail.

A sixth, in `algebras/<name>/approx.bend`, is the kernel on approximate
inputs (**proof**, `K.approx`, from `Err.fields_a`, ADR-011): if the
computed inputs a′, b′ are within da, db of exact a, b (field by field,
`AP.Close`), then for every output field i,
|K(fadd, fmul)(a′, b′)ᵢ − K(a, b)ᵢ| ≤ h(kᵢ) · A′ᵢ + Dᵢ, with A′ the
absolute size at a′, b′ and D the kernel itself run in the size-deviation
semiring (`AP.Ad`) on (|a|, da), (|b|, db). Outputs of one kernel are
inputs of the next, so bounds compose through a chain of kernels. The
term-level theorem is `Prop.bound` (|eval(env′, t) − eval(env, t)| ≤
dev(t)) with `Err.approx` (`proofs/approx.bend`). 7189 laws.

A seventh, in `algebras/<name>/cr.bend`, is correct rounding (**proof**,
`K.cr`, from `CR.fields`, ADR-011): the kernel run on big dyadics with
`src/cr.bend`'s operations and rounded once per output (`CR.f32`) is
`Dy.f32` of the exact output, the kernel's terms evaluated over dyadics.
`tests/cr_kernels.bend` runs it on 500 PGA3D motor products. Converting
back to F32 (`CR.to_f32`) is exact on all 4000 outputs, and the result
is never farther from the exact value than plain F32, which differs from
it in 699. 7189 laws.

| algebra | kinds | kernels | of which sandwiches | zero laws | multiplications |
|---|---|---|---|---|---|
| VGA2D | 5 | 280 | 10 | 4 | 606 |
| VGA3D | 8 | 681 | 24 | 24 | 3941 |
| PGA2D | 10 | 1023 | 60 | 32 | 3848 |
| PGA3D | 11 | 1231 | 77 | 101 | 12277 |
| STA | 9 | 849 | 27 | 84 | 11190 |
| CGA3D (null basis) | 11 | 1241 | 44 | (in `.ok`) | 47041 |
| STAP | 9 | 814 | 27 | — | 27312 |
| CSTA (null basis) | 12 | 1428 | 24 | (in `.ok`) | 150235 |

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

**STAP and CSTA** (added 2026-10-04). STAP, projective spacetime
R(3,1,1), goes through the diagonal path; its proofs check in 43 s and are
in the default gate. CSTA, conformal spacetime R(4,2), goes through the
null-basis path as CGA3D does. Its proofs **check in full**: all 25 files,
1.6 hours in sequence (2026-10-05; the slowest file 20 minutes), almost
all of it in the normaliser (ADR-004, "What it costs"). Probes had
predicted 10 hours. `tools/gate.sh --csta` runs it; the default gate
skips it, and tests/csta.bend also checks values over exact integers. For
STAP and CSTA, every result kind equals gax's (STAP 598 pairs, CSTA 1068).
`tests/stap.bend` and `tests/csta.bend` check values. The five other
algebras were compared again, all equal: VGA2D 200, VGA3D 505, PGA2D 763,
PGA3D 754, STA 633, CGA3D 954.

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
negated diagonal one: e123oi = −e123₊₋. Dual and undual are the metric-free
complements on the null blades themselves (gax's), proven against
`S.MV.rcomp`/`lcomp` on each kind's `.raw` layout (ADR-004, point 6);
`tests/cga3d_dual.bend` checks them against gax's generated code.

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

The VGA3D API (`api/vga3d.bend`, rotors) and the PGA2D API
(`api/pga2d.bend`, points, lines, motors) are tested the same way:
- `tests/vga3d_api.bend`: a right-handed quarter turn; the rotor between
  two directions; log∘exp; sqrt²; renormalize_fast.
- `tests/pga2d_api.bend`: a translation; quarter turns about the origin
  and about a point (counterclockwise); the motion between two points;
  log∘exp for a rotation and a translation.

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
| `transform_factor.bend` | (m x ~m)(m y ~m) = m (x y) ~m without the factor ~m m (m = 2 in the plane: 16 against 4) | versor laws |
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
