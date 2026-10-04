# gax-blend: the proofs of LAWS.bend. `bend PROOF.bend` is the gate: it
# prints ALL PROOFS CHECK only when every law holds. The lemmas live in
# proofs/; each def below fills the law of the same name.

import Base
import ./src/ring.bend as R
import ./src/spec.bend as S
import ./LAWS.bend as Laws
import ./proofs/base.bend as B
import ./proofs/add.bend as A
import ./proofs/sgn.bend as G
import ./proofs/gp.bend as P
import ./proofs/gp_assoc.bend as PA
import ./proofs/wedge.bend as WV
import ./proofs/scale.bend as SC
import ./proofs/inv.bend as IV
import ./proofs/rev.bend as RV
import ./proofs/gen.bend as GN
import ./proofs/grade.bend as GR

# Addition
# --------

def Laws.add_comm(T, add, add_comm, d, x, y):
  A.Add.comm(~T, ~add, ~add_comm, d, x, y)

def Laws.add_assoc(T, add, add_assoc, d, x, y, z):
  A.Add.assoc(~T, ~add, ~add_assoc, d, x, y, z)

# Grade signs
# -----------

def Laws.sgn_compose(T, neg, neg_neg, d, n1, f1, r1, n2, f2, r2, x):
  G.Sgn.compose(~T, ~neg, ~neg_neg, d, n1, f1, r1, n2, f2, r2, x)

def Laws.involute_involute(T, neg, neg_neg, d, x):
  Equal.trans(S.MV(T, d),
    S.MV.involute(~T, ~neg, d, S.MV.involute(~T, ~neg, d, x)),
    S.MV.sgn(~T, ~neg, d, False{}, False{}, False{}, x), x,
    G.Sgn.compose(~T, ~neg, ~neg_neg, d, False{}, True{}, False{}, False{}, True{}, False{}, x),
    G.Sgn.id(~T, ~neg, d, x))

def Laws.reverse_reverse(T, neg, neg_neg, d, x):
  Equal.trans(S.MV(T, d),
    S.MV.reverse(~T, ~neg, d, S.MV.reverse(~T, ~neg, d, x)),
    S.MV.sgn(~T, ~neg, d, False{}, False{}, False{}, x), x,
    G.Sgn.compose(~T, ~neg, ~neg_neg, d, False{}, False{}, True{}, False{}, False{}, True{}, x),
    G.Sgn.id(~T, ~neg, d, x))

def Laws.reverse_involute(T, neg, neg_neg, d, x):
  (G.Sgn.compose(~T, ~neg, ~neg_neg, d, False{}, False{}, True{}, False{}, True{}, False{}, x),
   G.Sgn.compose(~T, ~neg, ~neg_neg, d, False{}, True{}, False{}, False{}, False{}, True{}, x))

# The geometric product
# ---------------------

def Laws.gp_add_left(T, add, mul, neg, add_assoc, add_comm, dist_r, neg_add, d, sig, x, y, z):
  P.Gp.add_l(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_r, ~neg_add, d, False{}, False{}, x, y, z, sig)

def Laws.gp_add_right(T, add, mul, neg, add_assoc, add_comm, dist_l, neg_add, d, sig, x, y, z):
  P.Gp.add_r(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_l, ~neg_add, d, False{}, False{}, x, y, z, sig)

def Laws.gp_assoc(T, add, mul, neg, add_assoc, add_comm, mul_assoc, dist_l, dist_r, neg_add, neg_neg, neg_mul_l, neg_mul_r, d, sig, x, y, z):
  PA.Gp.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r,
    d, False{}, False{}, False{}, False{}, x, y, z, sig)

def Laws.gp_scale_left(T, add, mul, neg, mul_assoc, dist_l, neg_mul_r, d, sig, c, x, y):
  SC.Scale.gp_l(~T, ~add, ~mul, ~neg, ~mul_assoc, ~dist_l, ~neg_mul_r, d, False{}, False{}, c, x, y, sig)

def Laws.gp_scale_right(T, add, mul, neg, mul_assoc, mul_comm, dist_l, neg_mul_r, d, sig, c, x, y):
  SC.Scale.gp_r(~T, ~add, ~mul, ~neg, ~mul_assoc, ~mul_comm, ~dist_l, ~neg_mul_r, d, False{}, False{}, c, x, y, sig)

def Laws.involute_gp(T, add, mul, neg, neg_add, neg_neg, neg_mul_l, neg_mul_r, d, sig, x, y):
  IV.Inv.gp(~T, ~add, ~mul, ~neg, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, False{}, False{}, False{}, x, y, sig)

def Laws.reverse_gp(T, add, mul, neg, add_comm, mul_comm, neg_add, neg_neg, neg_mul_l, neg_mul_r, d, sig, x, y):
  RV.Rev.gp(~T, ~add, ~mul, ~neg, ~add_comm, ~mul_comm, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r,
    d, False{}, False{}, False{}, False{}, x, y, sig)

def Laws.gen_square(T, add, mul, neg, one, one_one, d, sig, i):
  Equal.trans(S.MV(T, d),
    S.MV.gp(~T, ~add, ~mul, ~neg, d, sig, S.MV.gen(T, d, i, one), S.MV.gen(T, d, i, one)),
    S.MV.of_q(~T, ~neg, d, S.Sig.at(d, sig, i), mul(one, one)),
    S.MV.of_q(~T, ~neg, d, S.Sig.at(d, sig, i), one),
    GN.Gen.sq(~T, ~add, ~mul, ~neg, d, i, one, one, sig),
    Equal.cong(T, S.MV(T, d), w => S.MV.of_q(~T, ~neg, d, S.Sig.at(d, sig, i), w), mul(one, one), one, one_one))

def Laws.gen_anticomm(T, add, mul, neg, neg_neg, one, d, sig, i, j, ne):
  GN.Gen.ac(~T, ~add, ~mul, ~neg, ~neg_neg, d, i, j, one, sig, ne)

# Outer and regressive products
# -----------------------------

def Laws.wedge_is_gp_zero(T, add, mul, neg, d, x, y):
  WV.Wedge.gp0(~T, ~add, ~mul, ~neg, d, False{}, False{}, x, y)

def Laws.wedge_assoc(T, add, mul, neg, add_assoc, add_comm, mul_assoc, dist_l, dist_r, neg_add, neg_neg, neg_mul_l, neg_mul_r, d, x, y, z):
  WV.Wedge.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, x, y, z)

def Laws.vee_assoc(T, add, mul, neg, add_assoc, add_comm, mul_assoc, dist_l, dist_r, neg_add, neg_neg, neg_mul_l, neg_mul_r, d, x, y, z):
  WV.Vee.assoc(~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r, d, x, y, z)

# Complements
# -----------

def Laws.lcomp_rcomp(T, neg, neg_neg, d, x):
  WV.Comp.lcomp_rcomp(~T, ~neg, ~neg_neg, d, x)

def Laws.rcomp_lcomp(T, neg, neg_neg, d, x):
  WV.Comp.rcomp_lcomp(~T, ~neg, ~neg_neg, d, x)

def Laws.rcomp_vee(T, add, mul, neg, neg_neg, d, x, y):
  WV.Comp.rcomp_vee(~T, ~add, ~mul, ~neg, ~neg_neg, d, x, y)

# Grades
# ------

def Laws.wedge_grade(T, add, mul, neg, d, j, k, x, y, hx, hy):
  GR.Wedge.grade(~T, ~add, ~mul, ~neg, d, False{}, False{}, j, k, x, y, hx, hy)
