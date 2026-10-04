# IEEE binary32 rounding, as exact arithmetic on dyadics (src/round.bend:
# round to nearest even at 24 bits in the normal range, to the grid 2^-149
# below, finite range), meets the rounding model with underflow:
# |f32(x) - x| <= 2^-24 |x| + 2^-150 (proofs/round.bend, Fl.model). So the
# rounding-error theorem with underflow (Err.bound_u) holds outright for
# every term computed in such arithmetic. It is proven for every format (p
# bits, grid 2^-k, any range test); binary32 is p1 = 23, k = 149,
# big = Dy.normal. Bend cannot specialise the template at those constants
# in the checker: ~ arguments are compile time, and 2^24 is expanded
# (bend-facts Q16). Run: 5 / 2^151 rounds to the grid point 2^-149.
import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/round.bend as RD
import ../src/norm.bend as N
import ../src/err.bend as E
import ../proofs/err.bend as ER
import ../proofs/dyadic.bend as Y
import ../proofs/round.bend as R

# for any format: p = 1 + p1 bits, grid 2^-k, range test big
def fl(~p1: Nat, ~k: Nat, ~big: D.Dy -> Bool, +env: List<&2, D.Dy>, t: N.Tm)
  -> {D.Dy.pos(D.Dy.add(D.Dy.add(D.Dy.mul(E.Err.H(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.ulp(1n+p1), E.Tm.k(t)), E.Tm.absev(~D.Dy, ~D.Dy.zero(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.abs, env, t)),
        E.Err.D(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.abs, ~D.Dy.ulp(1n+p1), ~D.Dy.ulp(1n+k), ~D.Dy.ulp(1n+k), env, t)),
      D.Dy.neg(D.Dy.abs(D.Dy.add(N.Tm.eval(~D.Dy, ~D.Dy.zero(), ~RD.Dy.fladd(~1n+p1, ~k, ~big), ~RD.Dy.flmul(~1n+p1, ~k, ~big), ~D.Dy.neg, env, t), D.Dy.neg(N.Tm.eval(~D.Dy, ~D.Dy.zero(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg, env, t))))))) == True{} : Bool}:
  ER.Err.bound_u(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg,
    ~Y.Dy.r.add_assoc, ~Y.Dy.r.add_comm, ~Y.Dy.r.zero_l, ~Y.Dy.r.add_inv, ~Y.Dy.r.mul_assoc, ~Y.Dy.r.mul_comm, ~Y.Dy.r.unit_r, ~Y.Dy.r.dist_l,
    ~Y.Dy.r.neg_add, ~Y.Dy.r.neg_mul_l, ~Y.Dy.r.neg_neg,
    ~D.Dy.pos, ~D.Dy.abs, ~Y.Dy.pos_add, ~Y.Dy.pos_mul, ~Y.Dy.pos_abs, ~Y.Dy.tri, ~Y.Dy.abs_mul, ~Y.Dy.abs_neg, ~{==}, ~D.Dy.ulp(1n+p1), ~R.Round.eps_pos(1n+p1),
    ~D.Dy.ulp(1n+k), ~D.Dy.ulp(1n+k), ~R.Round.eps_pos(1n+k), ~R.Round.eps_pos(1n+k),
    ~RD.Dy.fladd(~1n+p1, ~k, ~big), ~RD.Dy.flmul(~1n+p1, ~k, ~big), ~R.Fl.add_ok(~p1, ~k, ~big), ~R.Fl.mul_ok(~p1, ~k, ~big),
    env, t)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(D.Dy.show(RD.Dy.rfix(149n, D.Dy.of(151n, I.IPos{5n}))))
#|1/2^149
