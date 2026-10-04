# Upstream repro (not filed): a theorem over ANY commutative monoid fails
# --verdict, because the ~ constants need a model and none exists.
#
#   bend upstream/verdict_ring_hypotheses.bend            -> ALL PROOFS CHECK
#   bend upstream/verdict_ring_hypotheses.bend --verdict  -> SOME PROOFS FAIL (mismatch)
#   bend upstream/verdict_ring_hypotheses.bend -o x.bendtt
#     -> BendTT: out of scope ... sum3: no model for sum3~unit
#
# Same root cause as #1182 (greedy per-constant models; PR #1263 adds
# backtracking). This case goes further: with T := Unit and no eta in the
# kernel, add_comm forces add := \x y. Unit{} and add_unit then needs
# Unit{} == x for a variable x, so even a backtracking search finds no
# model. Every unital algebraic structure (monoid, ring, field, the scalar
# ring of a geometric algebra) is affected. Bend 2.0.35, commit 2bfc83fd.
import Base

law sum3:
  for ~T: Data
  for ~zero: T
  for ~add: T -> T -> T
  for ~comm: @x: T -> @y: T -> {add(x, y) == add(y, x) : T}
  for ~unit: @x: T -> {add(x, zero) == x : T}
  for +a: T
  {add(zero, a) == a : T}

def sum3(T, zero, add, comm, unit, a):
  Equal.trans(T, add(zero, a), add(a, zero), a, comm(zero, a), unit(a))
