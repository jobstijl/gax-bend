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
