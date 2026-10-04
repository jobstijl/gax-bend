# gax-blend: the laws. The human owns this file; PROOF.bend proves it.
#
# STATUS: DRAFT for review (Phase 1, 2026-10-04). Until it is approved,
# Claude may still edit it; afterwards a law changes only by the owner.
#
# Layer S: the multivector spec (src/spec.bend). Every law holds for every
# dimension d and every signature sig at once, over any ring: the scalar
# type T and its operations are ~ parameters, and each law assumes only the
# ring laws (src/ring.bend) its proof uses.

import Base
import ./src/ring.bend as R
import ./src/spec.bend as S

# Addition
# --------

# LAW: addition of multivectors is commutative
law add_comm:
  for ~T: Data
  for ~add: T -> T -> T
  for ~add_comm: R.Ring.Comm(T, add)
  for +d: Nat
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  {S.MV.add(~T, ~add, d, x, y) == S.MV.add(~T, ~add, d, y, x) : S.MV(T, d)}

# LAW: addition of multivectors is associative
law add_assoc:
  for ~T: Data
  for ~add: T -> T -> T
  for ~add_assoc: R.Ring.Assoc(T, add)
  for +d: Nat
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  for +z: S.MV(T, d)
  {S.MV.add(~T, ~add, d, S.MV.add(~T, ~add, d, x, y), z) == S.MV.add(~T, ~add, d, x, S.MV.add(~T, ~add, d, y, z)) : S.MV(T, d)}

# Grade signs: the involutions are involutive and commute
# --------------------------------------------------------

# LAW: grade signs compose by xor of their flags: (n, f, r) is a group Z2^3,
# so every involution is involutive and any two commute
law sgn_compose:
  for ~T: Data
  for ~neg: T -> T
  for ~neg_neg: R.Ring.NegNeg(T, neg)
  for +d: Nat
  for +n1: Bool
  for +f1: Bool
  for +r1: Bool
  for +n2: Bool
  for +f2: Bool
  for +r2: Bool
  for +x: S.MV(T, d)
  {S.MV.sgn(~T, ~neg, d, n1, f1, r1, S.MV.sgn(~T, ~neg, d, n2, f2, r2, x))
    == S.MV.sgn(~T, ~neg, d, Bool.xor(n1, n2), Bool.xor(f1, f2), Bool.xor(r1, r2), x) : S.MV(T, d)}

# LAW: the grade involution is an involution
law involute_involute:
  for ~T: Data
  for ~neg: T -> T
  for ~neg_neg: R.Ring.NegNeg(T, neg)
  for +d: Nat
  for +x: S.MV(T, d)
  {S.MV.involute(~T, ~neg, d, S.MV.involute(~T, ~neg, d, x)) == x : S.MV(T, d)}

# LAW: the reverse is an involution
law reverse_reverse:
  for ~T: Data
  for ~neg: T -> T
  for ~neg_neg: R.Ring.NegNeg(T, neg)
  for +d: Nat
  for +x: S.MV(T, d)
  {S.MV.reverse(~T, ~neg, d, S.MV.reverse(~T, ~neg, d, x)) == x : S.MV(T, d)}

# LAW: the reverse and the grade involution commute, and together they are
# the Clifford conjugate
law reverse_involute:
  for ~T: Data
  for ~neg: T -> T
  for ~neg_neg: R.Ring.NegNeg(T, neg)
  for +d: Nat
  for +x: S.MV(T, d)
  {S.MV.reverse(~T, ~neg, d, S.MV.involute(~T, ~neg, d, x)) == S.MV.conjugate(~T, ~neg, d, x) : S.MV(T, d)}
  & {S.MV.involute(~T, ~neg, d, S.MV.reverse(~T, ~neg, d, x)) == S.MV.conjugate(~T, ~neg, d, x) : S.MV(T, d)}

# The geometric product
# ---------------------

# LAW: the geometric product distributes over addition on the left
law gp_add_left:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for ~add_assoc: R.Ring.Assoc(T, add)
  for ~add_comm: R.Ring.Comm(T, add)
  for ~dist_r: R.Ring.DistR(T, add, mul)
  for ~neg_add: R.Ring.NegAdd(T, add, neg)
  for +d: Nat
  for +sig: S.Sig(d)
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  for +z: S.MV(T, d)
  {S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.add(~T, ~add, d, x, y), z)
    == S.MV.add(~T, ~add, d, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, z), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, z)) : S.MV(T, d)}

# LAW: the geometric product distributes over addition on the right
law gp_add_right:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for ~add_assoc: R.Ring.Assoc(T, add)
  for ~add_comm: R.Ring.Comm(T, add)
  for ~dist_l: R.Ring.DistL(T, add, mul)
  for ~neg_add: R.Ring.NegAdd(T, add, neg)
  for +d: Nat
  for +sig: S.Sig(d)
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  for +z: S.MV(T, d)
  {S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.add(~T, ~add, d, y, z))
    == S.MV.add(~T, ~add, d, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y), S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, z)) : S.MV(T, d)}

# LAW: a scalar factor on the left operand comes out in front
law gp_scale_left:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for ~mul_assoc: R.Ring.Assoc(T, mul)
  for ~dist_l: R.Ring.DistL(T, add, mul)
  for ~neg_mul_r: R.Ring.NegMulR(T, mul, neg)
  for +d: Nat
  for +sig: S.Sig(d)
  for +c: T
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  {S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.scale(~T, ~mul, d, c, x), y)
    == S.MV.scale(~T, ~mul, d, c, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y)) : S.MV(T, d)}

# LAW: a scalar factor on the right operand comes out in front (the ring
# is commutative here)
law gp_scale_right:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for ~mul_assoc: R.Ring.Assoc(T, mul)
  for ~mul_comm: R.Ring.Comm(T, mul)
  for ~dist_l: R.Ring.DistL(T, add, mul)
  for ~neg_mul_r: R.Ring.NegMulR(T, mul, neg)
  for +d: Nat
  for +sig: S.Sig(d)
  for +c: T
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  {S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.scale(~T, ~mul, d, c, y))
    == S.MV.scale(~T, ~mul, d, c, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y)) : S.MV(T, d)}

# LAW: a generator squares to its metric: e_i e_i = q_i (zero past the last
# generator)
law gen_square:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for ~one: T
  for ~one_one: {mul(one, one) == one : T}
  for +d: Nat
  for +sig: S.Sig(d)
  for +i: Nat
  {S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gen(T, d, i, one), S.MV.gen(T, d, i, one))
    == S.MV.metric(~T, ~neg, d, sig, i, one) : S.MV(T, d)}

# LAW: distinct generators anticommute: e_i e_j = -(e_j e_i)
law gen_anticomm:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for ~neg_neg: R.Ring.NegNeg(T, neg)
  for ~one: T
  for +d: Nat
  for +sig: S.Sig(d)
  for +i: Nat
  for +j: Nat
  for +ne: {Nat.is_eq(i, j) == False{} : Bool}
  {S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gen(T, d, i, one), S.MV.gen(T, d, j, one))
    == S.MV.neg(~T, ~neg, d, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gen(T, d, j, one), S.MV.gen(T, d, i, one))) : S.MV(T, d)}

# LAW: the grade involution is an automorphism of the geometric product
law involute_gp:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for ~neg_add: R.Ring.NegAdd(T, add, neg)
  for ~neg_neg: R.Ring.NegNeg(T, neg)
  for ~neg_mul_l: R.Ring.NegMulL(T, mul, neg)
  for ~neg_mul_r: R.Ring.NegMulR(T, mul, neg)
  for +d: Nat
  for +sig: S.Sig(d)
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  {S.MV.involute(~T, ~neg, d, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y))
    == S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.involute(~T, ~neg, d, x), S.MV.involute(~T, ~neg, d, y)) : S.MV(T, d)}

# LAW: the reverse is an anti-automorphism of the geometric product
law reverse_gp:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for ~add_comm: R.Ring.Comm(T, add)
  for ~mul_comm: R.Ring.Comm(T, mul)
  for ~neg_add: R.Ring.NegAdd(T, add, neg)
  for ~neg_neg: R.Ring.NegNeg(T, neg)
  for ~neg_mul_l: R.Ring.NegMulL(T, mul, neg)
  for ~neg_mul_r: R.Ring.NegMulR(T, mul, neg)
  for +d: Nat
  for +sig: S.Sig(d)
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  {S.MV.reverse(~T, ~neg, d, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y))
    == S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.reverse(~T, ~neg, d, y), S.MV.reverse(~T, ~neg, d, x)) : S.MV(T, d)}

# LAW: the geometric product is associative (no commutativity needed)
law gp_assoc:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for ~add_assoc: R.Ring.Assoc(T, add)
  for ~add_comm: R.Ring.Comm(T, add)
  for ~mul_assoc: R.Ring.Assoc(T, mul)
  for ~dist_l: R.Ring.DistL(T, add, mul)
  for ~dist_r: R.Ring.DistR(T, add, mul)
  for ~neg_add: R.Ring.NegAdd(T, add, neg)
  for ~neg_neg: R.Ring.NegNeg(T, neg)
  for ~neg_mul_l: R.Ring.NegMulL(T, mul, neg)
  for ~neg_mul_r: R.Ring.NegMulR(T, mul, neg)
  for +d: Nat
  for +sig: S.Sig(d)
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  for +z: S.MV(T, d)
  {S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, y), z)
    == S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, x, S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, y, z)) : S.MV(T, d)}

# Outer and regressive products
# -----------------------------

# LAW: the outer product is the geometric product of the zero metric
law wedge_is_gp_zero:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for +d: Nat
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  {S.MV.wedge(~T, ~add, ~mul, ~neg, d, x, y) == S.MV.gp(~T, ~add, ~mul, ~neg, d, S.Sig.zero(d), x, y) : S.MV(T, d)}

# LAW: the outer product is associative
law wedge_assoc:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for ~add_assoc: R.Ring.Assoc(T, add)
  for ~add_comm: R.Ring.Comm(T, add)
  for ~mul_assoc: R.Ring.Assoc(T, mul)
  for ~dist_l: R.Ring.DistL(T, add, mul)
  for ~dist_r: R.Ring.DistR(T, add, mul)
  for ~neg_add: R.Ring.NegAdd(T, add, neg)
  for ~neg_neg: R.Ring.NegNeg(T, neg)
  for ~neg_mul_l: R.Ring.NegMulL(T, mul, neg)
  for ~neg_mul_r: R.Ring.NegMulR(T, mul, neg)
  for +d: Nat
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  for +z: S.MV(T, d)
  {S.MV.wedge(~T, ~add, ~mul, ~neg, d, S.MV.wedge(~T, ~add, ~mul, ~neg, d, x, y), z)
    == S.MV.wedge(~T, ~add, ~mul, ~neg, d, x, S.MV.wedge(~T, ~add, ~mul, ~neg, d, y, z)) : S.MV(T, d)}

# LAW: the regressive product is associative
law vee_assoc:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for ~add_assoc: R.Ring.Assoc(T, add)
  for ~add_comm: R.Ring.Comm(T, add)
  for ~mul_assoc: R.Ring.Assoc(T, mul)
  for ~dist_l: R.Ring.DistL(T, add, mul)
  for ~dist_r: R.Ring.DistR(T, add, mul)
  for ~neg_add: R.Ring.NegAdd(T, add, neg)
  for ~neg_neg: R.Ring.NegNeg(T, neg)
  for ~neg_mul_l: R.Ring.NegMulL(T, mul, neg)
  for ~neg_mul_r: R.Ring.NegMulR(T, mul, neg)
  for +d: Nat
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  for +z: S.MV(T, d)
  {S.MV.vee(~T, ~add, ~mul, ~neg, d, S.MV.vee(~T, ~add, ~mul, ~neg, d, x, y), z)
    == S.MV.vee(~T, ~add, ~mul, ~neg, d, x, S.MV.vee(~T, ~add, ~mul, ~neg, d, y, z)) : S.MV(T, d)}

# Complements
# -----------

# LAW: the left complement undoes the right complement
law lcomp_rcomp:
  for ~T: Data
  for ~neg: T -> T
  for ~neg_neg: R.Ring.NegNeg(T, neg)
  for +d: Nat
  for +x: S.MV(T, d)
  {S.MV.lcomp(~T, ~neg, d, S.MV.rcomp(~T, ~neg, d, x)) == x : S.MV(T, d)}

# LAW: the right complement undoes the left complement
law rcomp_lcomp:
  for ~T: Data
  for ~neg: T -> T
  for ~neg_neg: R.Ring.NegNeg(T, neg)
  for +d: Nat
  for +x: S.MV(T, d)
  {S.MV.rcomp(~T, ~neg, d, S.MV.lcomp(~T, ~neg, d, x)) == x : S.MV(T, d)}

# LAW: the right complement turns the regressive product into the outer
# product of the complements
law rcomp_vee:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for ~neg_neg: R.Ring.NegNeg(T, neg)
  for +d: Nat
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  {S.MV.rcomp(~T, ~neg, d, S.MV.vee(~T, ~add, ~mul, ~neg, d, x, y))
    == S.MV.wedge(~T, ~add, ~mul, ~neg, d, S.MV.rcomp(~T, ~neg, d, x), S.MV.rcomp(~T, ~neg, d, y)) : S.MV(T, d)}

# Grades
# ------

# LAW: the outer product of a j-vector and a k-vector is a (j+k)-vector
law wedge_grade:
  for ~T: Data
  for ~add: T -> T -> T
  for ~mul: T -> T -> T
  for ~neg: T -> T
  for +d: Nat
  for +j: Nat
  for +k: Nat
  for +x: S.MV(T, d)
  for +y: S.MV(T, d)
  for +hx: S.MV.Homog(T, d, j, x)
  for +hy: S.MV.Homog(T, d, k, y)
  S.MV.Homog(T, d, Nat.add(j, k), S.MV.wedge(~T, ~add, ~mul, ~neg, d, x, y))
