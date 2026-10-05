# Dekker's product at odd precision (ADR-010): p = 2s - 1, so binary64
# (p = 53, s = 27). The split is proofs/eft2.bend's (its sizes hold for any
# 2^p = 2^r 2^s, here r = s - 1); the partial sums are exact by the same
# grid argument, with bounds for P = R S, R = 2^(s-1), S = 2^s.

import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/round.bend as RD
import ../src/norm.bend as N
import ./nat.bend as NL
import ./int.bend as Z
import ./dyadic.bend as Y
import ./round.bend as R
import ./big.bend as BP
import ./equiv.bend as EQ
import ./eft.bend as E
import ./eft2.bend as E2

# Bounds
# ------
# With S = 2R and R R >= 4 R; each is a polynomial identity plus a
# remainder with nonnegative coefficients.

# R S + R S S + S R S + S R <= 2 R S R R
def PolyO1(+R: Nat, h4: E.Le(Nat.add(Nat.add(Nat.add(R, R), R), R), Nat.mul(R, R))) -> E.Le(Nat.add(Nat.mul(R, Nat.double(R)), Nat.add(Nat.mul(Nat.mul(R, Nat.double(R)), Nat.double(R)), Nat.add(Nat.mul(Nat.double(R), Nat.mul(R, Nat.double(R))), Nat.mul(Nat.double(R), R)))), Nat.add(Nat.mul(Nat.mul(R, Nat.double(R)), Nat.mul(R, R)), Nat.mul(Nat.mul(R, Nat.double(R)), Nat.mul(R, R)))):
  +w = RD.Nat.monus(Nat.mul(R, R), Nat.add(Nat.add(Nat.add(R, R), R), R))
  +hw = E.Le.wit(Nat.add(Nat.add(Nat.add(R, R), R), R), Nat.mul(R, R), h4)
  +env : List<&2, Nat> = [R, Nat.double(R), w]
  E.Ge.of(Nat.add(Nat.mul(Nat.mul(R, Nat.double(R)), Nat.mul(R, R)), Nat.mul(Nat.mul(R, Nat.double(R)), Nat.mul(R, R))), Nat.add(Nat.mul(R, Nat.double(R)), Nat.add(Nat.mul(Nat.mul(R, Nat.double(R)), Nat.double(R)), Nat.add(Nat.mul(Nat.double(R), Nat.mul(R, Nat.double(R))), Nat.mul(Nat.double(R), R)))), R.NatN.eval(env, R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.Ml(R.V(2n), R.V(2n))), R.Ml(R.V(2n), R.V(2n))), R.Ml(R.V(2n), R.V(2n))), R.Ml(R.V(2n), R.V(2n))), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n))),
    R.NatN.eq2(env, R.Ad(R.Ml(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(0n), R.V(0n)))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(1n)), R.Ad(R.Ml(R.V(1n), R.Ml(R.V(0n), R.V(1n))), R.Ml(R.V(1n), R.V(0n))))), R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.Ml(R.V(2n), R.V(2n))), R.Ml(R.V(2n), R.V(2n))), R.Ml(R.V(2n), R.V(2n))), R.Ml(R.V(2n), R.V(2n))), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n))), [R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.Ml(R.V(0n), R.V(0n)), R.V(0n)), R.Ml(R.Ml(R.V(0n), R.V(0n)), R.V(0n))), R.Ng(R.Ml(R.V(0n), R.V(0n)))), R.Ng(R.Ml(R.V(0n), R.V(0n)))), R.Ng(R.Ml(R.V(0n), R.V(0n)))), R.Ng(R.Ml(R.V(0n), R.V(0n)))), R.Ng(R.Ml(R.V(0n), R.V(1n)))), R.Ng(R.Ml(R.V(0n), R.V(1n)))), R.Ng(R.V(0n))), R.Ng(R.V(0n))), R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(0n))), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n))], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n))))], [R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n))))], {==}, (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, Y.Nat.double_add(R)), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), Unit{})), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), Unit{})))))))))))))))))))))))))))), {==}, {==}))

# R S + S R S + S R <= 2 R S S
def PolyO2(+R: Nat, h4: E.Le(Nat.add(Nat.add(Nat.add(R, R), R), R), Nat.mul(R, R))) -> E.Le(Nat.add(Nat.mul(R, Nat.double(R)), Nat.add(Nat.mul(Nat.double(R), Nat.mul(R, Nat.double(R))), Nat.mul(Nat.double(R), R))), Nat.add(Nat.mul(Nat.mul(R, Nat.double(R)), Nat.double(R)), Nat.mul(Nat.mul(R, Nat.double(R)), Nat.double(R)))):
  +w = RD.Nat.monus(Nat.mul(R, R), Nat.add(Nat.add(Nat.add(R, R), R), R))
  +hw = E.Le.wit(Nat.add(Nat.add(Nat.add(R, R), R), R), Nat.mul(R, R), h4)
  +env : List<&2, Nat> = [R, Nat.double(R), w]
  E.Ge.of(Nat.add(Nat.mul(Nat.mul(R, Nat.double(R)), Nat.double(R)), Nat.mul(Nat.mul(R, Nat.double(R)), Nat.double(R))), Nat.add(Nat.mul(R, Nat.double(R)), Nat.add(Nat.mul(Nat.double(R), Nat.mul(R, Nat.double(R))), Nat.mul(Nat.double(R), R))), R.NatN.eval(env, R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n))),
    R.NatN.eq2(env, R.Ad(R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(1n)), R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(1n))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ad(R.Ml(R.V(1n), R.Ml(R.V(0n), R.V(1n))), R.Ml(R.V(1n), R.V(0n)))), R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.V(0n), R.V(2n)), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.Ml(R.V(0n), R.V(2n))), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n)), R.V(2n))), [R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ml(R.V(0n), R.V(0n))), R.Ml(R.V(0n), R.V(1n))), R.Ng(R.V(0n))), R.Ng(R.V(0n))), R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n))], [R.Ad(R.V(1n), R.Ng(R.Ad(R.V(0n), R.V(0n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n))))], [R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)))), R.Ad(R.Ml(R.V(0n), R.V(0n)), R.Ng(R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n))))], {==}, (R.NatN.z(env, R.V(1n), R.Ad(R.V(0n), R.V(0n)), {==}, {==}, Y.Nat.double_add(R)), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), Unit{})), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), (R.NatN.z(env, R.Ml(R.V(0n), R.V(0n)), R.Ad(R.Ad(R.Ad(R.Ad(R.V(0n), R.V(0n)), R.V(0n)), R.V(0n)), R.V(2n)), {==}, {==}, hw), Unit{})))))))))))), {==}, {==}))

# 2 |e1| <= 2 P H, from 2|err| <= P, |ah|, |bh| <= P, 2|al|, 2|bl| <= S
def B1o(+R: Nat, +ee: Nat, +ma: Nat, +mb: Nat, +la: Nat, +lb: Nat, he: E.Le(Nat.double(ee), Nat.mul(R, Nat.double(R))), hma: E.Le(ma, Nat.mul(R, Nat.double(R))), hmb: E.Le(mb, Nat.mul(R, Nat.double(R))),
  +hla: {RD.Nat.lt(Nat.double(R), Nat.double(la)) == False{} : Bool}, +hlb: {RD.Nat.lt(Nat.double(R), Nat.double(lb)) == False{} : Bool}, h4: E.Le(Nat.add(Nat.add(Nat.add(R, R), R), R), Nat.mul(R, R)))
  -> E.Le(Nat.double(Nat.add(ee, Nat.add(Nat.mul(ma, lb), Nat.add(Nat.mul(la, mb), Nat.mul(la, lb))))), Nat.add(Nat.mul(Nat.mul(R, Nat.double(R)), Nat.mul(R, R)), Nat.mul(Nat.mul(R, Nat.double(R)), Nat.mul(R, R)))):
  +S = Nat.double(R)
  +rs = Nat.mul(R, Nat.double(R))
  +t2 = Nat.mul(ma, lb)
  +t3 = Nat.mul(la, mb)
  +t4 = Nat.mul(la, lb)
  +lbr : {RD.Nat.lt(R, lb) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(R, lb), RD.Nat.lt(Nat.double(R), Nat.double(lb)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.double(R), Nat.double(lb)), RD.Nat.lt(R, lb), E.Lt.dd(R, lb)), hlb)
  +ed = Equal.trans(Nat, Nat.double(Nat.add(ee, Nat.add(t2, Nat.add(t3, t4)))), Nat.add(Nat.double(ee), Nat.double(Nat.add(t2, Nat.add(t3, t4)))), Nat.add(Nat.double(ee), Nat.add(Nat.double(t2), Nat.add(Nat.double(t3), Nat.double(t4)))),
    E2.Dbl.add(ee, Nat.add(t2, Nat.add(t3, t4))),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.double(ee), z), Nat.double(Nat.add(t2, Nat.add(t3, t4))), Nat.add(Nat.double(t2), Nat.add(Nat.double(t3), Nat.double(t4))),
      Equal.trans(Nat, Nat.double(Nat.add(t2, Nat.add(t3, t4))), Nat.add(Nat.double(t2), Nat.double(Nat.add(t3, t4))), Nat.add(Nat.double(t2), Nat.add(Nat.double(t3), Nat.double(t4))), E2.Dbl.add(t2, Nat.add(t3, t4)),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.double(t2), z), Nat.double(Nat.add(t3, t4)), Nat.add(Nat.double(t3), Nat.double(t4)), E2.Dbl.add(t3, t4)))))
  hs = E2.Le.add2(Nat.double(ee), rs, Nat.add(Nat.double(t2), Nat.add(Nat.double(t3), Nat.double(t4))), Nat.add(Nat.mul(rs, S), Nat.add(Nat.mul(S, rs), Nat.mul(S, R))), he,
    E2.Le.add2(Nat.double(t2), Nat.mul(rs, S), Nat.add(Nat.double(t3), Nat.double(t4)), Nat.add(Nat.mul(S, rs), Nat.mul(S, R)), E2.Dbl.mr(ma, lb, rs, S, hma, hlb),
      E2.Le.add2(Nat.double(t3), Nat.mul(S, rs), Nat.double(t4), Nat.mul(S, R), E2.Dbl.ml(la, mb, S, rs, hla, hmb), E2.Dbl.ml(la, lb, S, R, hla, lbr))))
  E.Le.trans(Nat.double(Nat.add(ee, Nat.add(t2, Nat.add(t3, t4)))), Nat.add(Nat.mul(R, Nat.double(R)), Nat.add(Nat.mul(Nat.mul(R, Nat.double(R)), Nat.double(R)), Nat.add(Nat.mul(Nat.double(R), Nat.mul(R, Nat.double(R))), Nat.mul(Nat.double(R), R)))), Nat.add(Nat.mul(Nat.mul(R, Nat.double(R)), Nat.mul(R, R)), Nat.mul(Nat.mul(R, Nat.double(R)), Nat.mul(R, R))),
    E.Le.trans(Nat.double(Nat.add(ee, Nat.add(t2, Nat.add(t3, t4)))), Nat.add(Nat.double(ee), Nat.add(Nat.double(t2), Nat.add(Nat.double(t3), Nat.double(t4)))), Nat.add(Nat.mul(R, Nat.double(R)), Nat.add(Nat.mul(Nat.mul(R, Nat.double(R)), Nat.double(R)), Nat.add(Nat.mul(Nat.double(R), Nat.mul(R, Nat.double(R))), Nat.mul(Nat.double(R), R)))),
      E.Le.eq(Nat.double(Nat.add(ee, Nat.add(t2, Nat.add(t3, t4)))), Nat.add(Nat.double(ee), Nat.add(Nat.double(t2), Nat.add(Nat.double(t3), Nat.double(t4)))), ed), hs),
    PolyO1(R, h4))

# 2 |e2| <= 2 P S
def B2o(+R: Nat, +ee: Nat, +ma: Nat, +mb: Nat, +la: Nat, +lb: Nat, he: E.Le(Nat.double(ee), Nat.mul(R, Nat.double(R))), hma: E.Le(ma, Nat.mul(R, Nat.double(R))), hmb: E.Le(mb, Nat.mul(R, Nat.double(R))),
  +hla: {RD.Nat.lt(Nat.double(R), Nat.double(la)) == False{} : Bool}, +hlb: {RD.Nat.lt(Nat.double(R), Nat.double(lb)) == False{} : Bool}, h4: E.Le(Nat.add(Nat.add(Nat.add(R, R), R), R), Nat.mul(R, R)))
  -> E.Le(Nat.double(Nat.add(ee, Nat.add(Nat.mul(la, mb), Nat.mul(la, lb)))), Nat.add(Nat.mul(Nat.mul(R, Nat.double(R)), Nat.double(R)), Nat.mul(Nat.mul(R, Nat.double(R)), Nat.double(R)))):
  +S = Nat.double(R)
  +rs = Nat.mul(R, Nat.double(R))
  +t3 = Nat.mul(la, mb)
  +t4 = Nat.mul(la, lb)
  +lbr : {RD.Nat.lt(R, lb) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(R, lb), RD.Nat.lt(Nat.double(R), Nat.double(lb)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.double(R), Nat.double(lb)), RD.Nat.lt(R, lb), E.Lt.dd(R, lb)), hlb)
  +ed = Equal.trans(Nat, Nat.double(Nat.add(ee, Nat.add(t3, t4))), Nat.add(Nat.double(ee), Nat.double(Nat.add(t3, t4))), Nat.add(Nat.double(ee), Nat.add(Nat.double(t3), Nat.double(t4))),
    E2.Dbl.add(ee, Nat.add(t3, t4)), Equal.cong(Nat, Nat, z => Nat.add(Nat.double(ee), z), Nat.double(Nat.add(t3, t4)), Nat.add(Nat.double(t3), Nat.double(t4)), E2.Dbl.add(t3, t4)))
  hs = E2.Le.add2(Nat.double(ee), rs, Nat.add(Nat.double(t3), Nat.double(t4)), Nat.add(Nat.mul(S, rs), Nat.mul(S, R)), he,
    E2.Le.add2(Nat.double(t3), Nat.mul(S, rs), Nat.double(t4), Nat.mul(S, R), E2.Dbl.ml(la, mb, S, rs, hla, hmb), E2.Dbl.ml(la, lb, S, R, hla, lbr)))
  E.Le.trans(Nat.double(Nat.add(ee, Nat.add(t3, t4))), Nat.add(Nat.mul(R, Nat.double(R)), Nat.add(Nat.mul(Nat.double(R), Nat.mul(R, Nat.double(R))), Nat.mul(Nat.double(R), R))), Nat.add(Nat.mul(Nat.mul(R, Nat.double(R)), Nat.double(R)), Nat.mul(Nat.mul(R, Nat.double(R)), Nat.double(R))),
    E.Le.trans(Nat.double(Nat.add(ee, Nat.add(t3, t4))), Nat.add(Nat.double(ee), Nat.add(Nat.double(t3), Nat.double(t4))), Nat.add(Nat.mul(R, Nat.double(R)), Nat.add(Nat.mul(Nat.double(R), Nat.mul(R, Nat.double(R))), Nat.mul(Nat.double(R), R))),
      E.Le.eq(Nat.double(Nat.add(ee, Nat.add(t3, t4))), Nat.add(Nat.double(ee), Nat.add(Nat.double(t3), Nat.double(t4))), ed), hs),
    PolyO2(R, h4))

# 2 |e3| <= 2 P
def B3o(+R: Nat, +ee: Nat, +la: Nat, +lb: Nat, he: E.Le(Nat.double(ee), Nat.mul(R, Nat.double(R))), +hla: {RD.Nat.lt(Nat.double(R), Nat.double(la)) == False{} : Bool}, +hlb: {RD.Nat.lt(Nat.double(R), Nat.double(lb)) == False{} : Bool})
  -> E.Le(Nat.double(Nat.add(ee, Nat.mul(la, lb))), Nat.add(Nat.mul(R, Nat.double(R)), Nat.mul(R, Nat.double(R)))):
  +S = Nat.double(R)
  +rs = Nat.mul(R, Nat.double(R))
  +t4 = Nat.mul(la, lb)
  +lbr : {RD.Nat.lt(R, lb) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(R, lb), RD.Nat.lt(Nat.double(R), Nat.double(lb)), False{}, Equal.sym(Bool, RD.Nat.lt(Nat.double(R), Nat.double(lb)), RD.Nat.lt(R, lb), E.Lt.dd(R, lb)), hlb)
  E.Le.trans(Nat.double(Nat.add(ee, t4)), Nat.add(Nat.double(ee), Nat.double(t4)), Nat.add(rs, rs), E.Le.eq(Nat.double(Nat.add(ee, t4)), Nat.add(Nat.double(ee), Nat.double(t4)), E2.Dbl.add(ee, t4)),
    E2.Le.add2(Nat.double(ee), rs, Nat.double(t4), rs, he,
      E.Le.trans(Nat.double(t4), Nat.mul(S, R), rs, E2.Dbl.ml(la, lb, S, R, hla, lbr), E.Le.eq(Nat.mul(S, R), rs, NL.Nat.mul_comm(S, R)))))

# Dekker's core at p = 2s - 1
# ---------------------------

# the products are exact; e1 = ah bh - pi exactly, on the grid 2^(p-1)
def Dko.c1(+t: Nat, +a: I.Int, +b: I.Int, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int, +A: Nat, +B: Nat, +Q: Nat,
  +hal: {al == I.Int.add(a, I.Int.neg(ah)) : I.Int}, +hbl: {bl == I.Int.add(b, I.Int.neg(bh)) : I.Int},
  +hma: {RD.Int.mag(ah) == Nat.mul(A, RD.Nat.pow2(1n+1n+t)) : Nat}, +hmb: {RD.Int.mag(bh) == Nat.mul(B, RD.Nat.pow2(1n+1n+t)) : Nat},
  +hA: {RD.Nat.lt(RD.Nat.pow2(1n+t), A) == False{} : Bool}, +hB: {RD.Nat.lt(RD.Nat.pow2(1n+t), B) == False{} : Bool},
  +hla: {RD.Nat.lt(RD.Nat.pow2(1n+1n+t), Nat.double(RD.Int.mag(al))) == False{} : Bool}, +hlb: {RD.Nat.lt(RD.Nat.pow2(1n+1n+t), Nat.double(RD.Int.mag(bl))) == False{} : Bool},
  +hpi: {RD.Int.mag(pi) == Nat.mul(Q, RD.Nat.pow2(Nat.add(1n+t, 1n+t))) : Nat}, +herr: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+t), RD.Nat.pow2(1n+1n+t)), Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))))) == False{} : Bool},
  +h4: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+t), RD.Nat.pow2(1n+t)), Nat.add(Nat.add(Nat.add(RD.Nat.pow2(1n+t), RD.Nat.pow2(1n+t)), RD.Nat.pow2(1n+t)), RD.Nat.pow2(1n+t))) == False{} : Bool})
  -> {E2.Dk.e1(1n+Nat.add(1n+t, 1n+t), ah, bh, pi) == I.Int.add(I.Int.mul(ah, bh), I.Int.neg(pi)) : I.Int} & {I.Int.add(I.Int.mul(ah, bh), I.Int.neg(pi)) == D.Int.sh(Nat.add(1n+t, 1n+t), I.Int.add(RD.Int.signed(I.Int.mul(ah, bh), Nat.double(Nat.double(Nat.mul(A, B)))), I.Int.neg(RD.Int.signed(pi, Q)))) : I.Int}:
  +s1 : Nat = 1n+t
  +s : Nat = 1n+s1
  +p1 = Nat.add(s1, s1)
  +p : Nat = 1n+p1
  +R = RD.Nat.pow2(s1)
  +S = RD.Nat.pow2(s)
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(p)
  +rs = Nat.mul(R, S)
  +rr = Nat.mul(R, R)
  +hH : {H == rr : Nat} = BP.Pow2.add(s1, s1)
  +hP : {P == rs : Nat} = Equal.trans(Nat, P, Nat.double(rr), rs, Equal.cong(Nat, Nat, z => Nat.double(z), H, rr, hH), Equal.sym(Nat, rs, Nat.double(rr), R.Nat.mul_double(R, R)))
  +ma = RD.Int.mag(ah)
  +mb = RD.Int.mag(bh)
  +la = RD.Int.mag(al)
  +lb = RD.Int.mag(bl)
  +err = I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))
  +ee = RD.Int.mag(err)
  +P1 = I.Int.mul(ah, bh)
  +P2 = I.Int.mul(ah, bl)
  +P3 = I.Int.mul(al, bh)
  +P4 = I.Int.mul(al, bl)
  +env : List<&2, I.Int> = [a, b, ah, al, bh, bl, pi]
  +hma2 : {RD.Nat.lt(rs, ma) == False{} : Bool} = E.Le.trans(ma, Nat.mul(A, S), rs, E.Le.eq(ma, Nat.mul(A, S), hma), E2.Le.mulr(A, R, S, hA))
  +hmb2 : {RD.Nat.lt(rs, mb) == False{} : Bool} = E.Le.trans(mb, Nat.mul(B, S), rs, E.Le.eq(mb, Nat.mul(B, S), hmb), E2.Le.mulr(B, R, S, hB))
  +hla1 : {RD.Nat.lt(R, la) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(R, la), RD.Nat.lt(S, Nat.double(la)), False{}, Equal.sym(Bool, RD.Nat.lt(S, Nat.double(la)), RD.Nat.lt(R, la), E.Lt.dd(R, la)), hla)
  +hlb1 : {RD.Nat.lt(R, lb) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(R, lb), RD.Nat.lt(S, Nat.double(lb)), False{}, Equal.sym(Bool, RD.Nat.lt(S, Nat.double(lb)), RD.Nat.lt(R, lb), E.Lt.dd(R, lb)), hlb)
  +hrp : {RD.Nat.lt(P, rs) == False{} : Bool} = E.Le.eq(rs, P, Equal.sym(Nat, P, rs, hP))
  +hrr : {RD.Nat.lt(P, rr) == False{} : Bool} = E.Le.trans(rr, rs, P, E2.Le.mull(R, R, S, E2.Le.dbl(R)), hrp)
  +ab = Nat.mul(A, B)
  +d1 = Nat.double(ab)
  +dd = Nat.double(d1)
  +ess : {RD.Int.mag(P1) == Nat.mul(Nat.mul(A, S), Nat.mul(B, S)) : Nat} = Equal.trans(Nat, RD.Int.mag(P1), Nat.mul(ma, mb), Nat.mul(Nat.mul(A, S), Nat.mul(B, S)), E2.Mag.mul(ah, bh),
    Equal.trans(Nat, Nat.mul(ma, mb), Nat.mul(Nat.mul(A, S), mb), Nat.mul(Nat.mul(A, S), Nat.mul(B, S)), Equal.cong(Nat, Nat, z => Nat.mul(z, mb), ma, Nat.mul(A, S), hma), Equal.cong(Nat, Nat, z => Nat.mul(Nat.mul(A, S), z), mb, Nat.mul(B, S), hmb)))
  +em1 : {RD.Int.mag(P1) == Nat.mul(ab, RD.Nat.pow2(Nat.add(s, s))) : Nat} = Equal.trans(Nat, RD.Int.mag(P1), Nat.mul(Nat.mul(A, S), Nat.mul(B, S)), Nat.mul(ab, RD.Nat.pow2(Nat.add(s, s))), ess,
    Equal.trans(Nat, Nat.mul(Nat.mul(A, S), Nat.mul(B, S)), Nat.mul(ab, Nat.mul(S, S)), Nat.mul(ab, RD.Nat.pow2(Nat.add(s, s))),
      R.NatN.eq([A, B, S], R.Ml(R.Ml(R.V(0n), R.V(2n)), R.Ml(R.V(1n), R.V(2n))), R.Ml(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(2n), R.V(2n))), [], [], {==}, Unit{}, {==}, {==}),
      Equal.cong(Nat, Nat, z => Nat.mul(ab, z), Nat.mul(S, S), RD.Nat.pow2(Nat.add(s, s)), Equal.sym(Nat, RD.Nat.pow2(Nat.add(s, s)), Nat.mul(S, S), BP.Pow2.add(s, s)))))
  +x1 = E2.Px(p1, P1, ab, Nat.add(s, s), em1, E.Le.trans(ab, rr, P, E2.Le.mul2(A, R, B, R, hA, hB), hrr))
  +env4 : List<&2, Nat> = [A, B, R, S, d1, dd]
  +emh : {RD.Int.mag(P1) == Nat.mul(dd, H) : Nat} = Equal.trans(Nat, RD.Int.mag(P1), Nat.mul(Nat.mul(A, S), Nat.mul(B, S)), Nat.mul(dd, H), ess,
    Equal.trans(Nat, Nat.mul(Nat.mul(A, S), Nat.mul(B, S)), Nat.mul(dd, rr), Nat.mul(dd, H),
      R.NatN.eq(env4, R.Ml(R.Ml(R.V(0n), R.V(3n)), R.Ml(R.V(1n), R.V(3n))), R.Ml(R.V(5n), R.Ml(R.V(2n), R.V(2n))), [R.Ad(R.Ad(R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(2n)), R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(2n))), R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(3n))), R.Ng(R.Ml(R.V(2n), R.V(2n))), R.Ad(R.Ng(R.Ml(R.V(2n), R.V(2n))), R.Ng(R.Ml(R.V(2n), R.V(2n))))], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(2n), R.V(2n)))), R.Ad(R.V(5n), R.Ng(R.Ad(R.V(4n), R.V(4n)))), R.Ad(R.V(4n), R.Ng(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(0n), R.V(1n)))))], {==}, (R.NatN.z(env4, R.V(3n), R.Ad(R.V(2n), R.V(2n)), {==}, {==}, Y.Nat.double_add(R)), (R.NatN.z(env4, R.V(5n), R.Ad(R.V(4n), R.V(4n)), {==}, {==}, Y.Nat.double_add(d1)), (R.NatN.z(env4, R.V(4n), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ml(R.V(0n), R.V(1n))), {==}, {==}, Y.Nat.double_add(Nat.mul(A, B))), Unit{}))), {==}, {==}),
      Equal.cong(Nat, Nat, z => Nat.mul(dd, z), rr, H, Equal.sym(Nat, H, rr, hH))))
  +x1g = RD.Int.signed(P1, dd)
  +xq = RD.Int.signed(pi, Q)
  +z1 = I.Int.add(P1, I.Int.neg(pi))
  +gz = Equal.trans(I.Int, z1, I.Int.add(D.Int.sh(p1, x1g), I.Int.neg(D.Int.sh(p1, xq))), D.Int.sh(p1, I.Int.add(x1g, I.Int.neg(xq))),
    Y.Int.cong2(P1, D.Int.sh(p1, x1g), I.Int.neg(pi), I.Int.neg(D.Int.sh(p1, xq)), E2.Grid.i(P1, dd, p1, emh), Equal.cong(I.Int, I.Int, z => I.Int.neg(z), pi, D.Int.sh(p1, xq), E2.Grid.i(pi, Q, p1, hpi))),
    E2.Sh.diff(p1, x1g, xq))
  +r1 = I.Int.add(err, I.Int.add(I.Int.neg(P2), I.Int.add(I.Int.neg(P3), I.Int.neg(P4))))
  +i1 : {z1 == r1 : I.Int} = BP.IntN(env, R.Ad(R.Ml(R.V(2n), R.V(4n)), R.Ng(R.V(6n))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ng(R.V(6n))), R.Ad(R.Ng(R.Ml(R.V(2n), R.V(5n))), R.Ad(R.Ng(R.Ml(R.V(3n), R.V(4n))), R.Ng(R.Ml(R.V(3n), R.V(5n)))))), [R.Ad(R.V(4n), R.V(5n)), R.V(0n)], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(0n), R.Ng(R.V(2n))))), R.Ad(R.V(5n), R.Ng(R.Ad(R.V(1n), R.Ng(R.V(4n)))))], {==}, (E2.IntZ(env, R.V(3n), R.Ad(R.V(0n), R.Ng(R.V(2n))), hal), (E2.IntZ(env, R.V(5n), R.Ad(R.V(1n), R.Ng(R.V(4n))), hbl), Unit{})))
  +bd = Nat.add(ee, Nat.add(Nat.mul(ma, lb), Nat.add(Nat.mul(la, mb), Nat.mul(la, lb))))
  hm = E.Le.trans(RD.Int.mag(z1), RD.Int.mag(r1), bd, E.Le.eq(RD.Int.mag(z1), RD.Int.mag(r1), Equal.cong(I.Int, Nat, z => RD.Int.mag(z), z1, r1, i1)),
    E2.Tri.e(err, I.Int.add(I.Int.neg(P2), I.Int.add(I.Int.neg(P3), I.Int.neg(P4))), Nat.add(Nat.mul(ma, lb), Nat.add(Nat.mul(la, mb), Nat.mul(la, lb))),
      E2.Tri.nm(ah, bl, I.Int.add(I.Int.neg(P3), I.Int.neg(P4)), Nat.add(Nat.mul(la, mb), Nat.mul(la, lb)), E2.Tri.nm(al, bh, I.Int.neg(P4), Nat.mul(la, lb), E2.Mag.negm(al, bl)))))
  +ph = Nat.mul(P, H)
  +eqt : {Nat.add(Nat.mul(rs, rr), Nat.mul(rs, rr)) == Nat.add(ph, ph) : Nat} = Equal.cong(Nat, Nat, z => Nat.add(z, z), Nat.mul(rs, rr), ph,
    Equal.trans(Nat, Nat.mul(rs, rr), Nat.mul(P, rr), ph, Equal.cong(Nat, Nat, z => Nat.mul(z, rr), rs, P, Equal.sym(Nat, P, rs, hP)), Equal.cong(Nat, Nat, z => Nat.mul(P, z), rr, H, Equal.sym(Nat, H, rr, hH))))
  hzb = E2.Le.half(RD.Int.mag(z1), ph, E.Le.trans(Nat.double(RD.Int.mag(z1)), Nat.add(Nat.mul(rs, rr), Nat.mul(rs, rr)), Nat.add(ph, ph),
    E.Le.trans(Nat.double(RD.Int.mag(z1)), Nat.double(bd), Nat.add(Nat.mul(rs, rr), Nat.mul(rs, rr)), E.Le.dd(RD.Int.mag(z1), bd, hm), B1o(R, ee, ma, mb, la, lb, herr, hma2, hmb2, hla, hlb, h4)),
    E.Le.eq(Nat.add(Nat.mul(rs, rr), Nat.mul(rs, rr)), Nat.add(ph, ph), eqt)))
  +ez = E.RNi.exact(p, z1, E2.Rep(p1, z1, I.Int.add(x1g, I.Int.neg(xq)), p1, gz, hzb))
  +ee1 = Equal.trans(I.Int, E2.Dk.e1(p, ah, bh, pi), E.RNi(p, z1), z1, Equal.cong(I.Int, I.Int, z => E.RNi(p, I.Int.add(z, I.Int.neg(pi))), E.RNi(p, P1), P1, x1), ez)
  (ee1, gz)

# e2 = e1 + ah bl exactly, on the grid 2^s
def Dko.c2(+t: Nat, +a: I.Int, +b: I.Int, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int, +A: Nat, +B: Nat, +Q: Nat,
  +hal: {al == I.Int.add(a, I.Int.neg(ah)) : I.Int}, +hbl: {bl == I.Int.add(b, I.Int.neg(bh)) : I.Int},
  +hma: {RD.Int.mag(ah) == Nat.mul(A, RD.Nat.pow2(1n+1n+t)) : Nat}, +hmb: {RD.Int.mag(bh) == Nat.mul(B, RD.Nat.pow2(1n+1n+t)) : Nat},
  +hA: {RD.Nat.lt(RD.Nat.pow2(1n+t), A) == False{} : Bool}, +hB: {RD.Nat.lt(RD.Nat.pow2(1n+t), B) == False{} : Bool},
  +hla: {RD.Nat.lt(RD.Nat.pow2(1n+1n+t), Nat.double(RD.Int.mag(al))) == False{} : Bool}, +hlb: {RD.Nat.lt(RD.Nat.pow2(1n+1n+t), Nat.double(RD.Int.mag(bl))) == False{} : Bool},
  +hpi: {RD.Int.mag(pi) == Nat.mul(Q, RD.Nat.pow2(Nat.add(1n+t, 1n+t))) : Nat}, +herr: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+t), RD.Nat.pow2(1n+1n+t)), Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))))) == False{} : Bool},
  +h4: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+t), RD.Nat.pow2(1n+t)), Nat.add(Nat.add(Nat.add(RD.Nat.pow2(1n+t), RD.Nat.pow2(1n+t)), RD.Nat.pow2(1n+t)), RD.Nat.pow2(1n+t))) == False{} : Bool})
  -> {E2.Dk.e2(1n+Nat.add(1n+t, 1n+t), ah, bh, bl, pi) == I.Int.add(I.Int.add(I.Int.mul(ah, bh), I.Int.neg(pi)), I.Int.mul(ah, bl)) : I.Int}:
  +s1 : Nat = 1n+t
  +s : Nat = 1n+s1
  +p1 = Nat.add(s1, s1)
  +p : Nat = 1n+p1
  +R = RD.Nat.pow2(s1)
  +S = RD.Nat.pow2(s)
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(p)
  +rs = Nat.mul(R, S)
  +rr = Nat.mul(R, R)
  +hH : {H == rr : Nat} = BP.Pow2.add(s1, s1)
  +hP : {P == rs : Nat} = Equal.trans(Nat, P, Nat.double(rr), rs, Equal.cong(Nat, Nat, z => Nat.double(z), H, rr, hH), Equal.sym(Nat, rs, Nat.double(rr), R.Nat.mul_double(R, R)))
  +ma = RD.Int.mag(ah)
  +mb = RD.Int.mag(bh)
  +la = RD.Int.mag(al)
  +lb = RD.Int.mag(bl)
  +err = I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))
  +ee = RD.Int.mag(err)
  +P1 = I.Int.mul(ah, bh)
  +P2 = I.Int.mul(ah, bl)
  +P3 = I.Int.mul(al, bh)
  +P4 = I.Int.mul(al, bl)
  +env : List<&2, I.Int> = [a, b, ah, al, bh, bl, pi]
  +hma2 : {RD.Nat.lt(rs, ma) == False{} : Bool} = E.Le.trans(ma, Nat.mul(A, S), rs, E.Le.eq(ma, Nat.mul(A, S), hma), E2.Le.mulr(A, R, S, hA))
  +hmb2 : {RD.Nat.lt(rs, mb) == False{} : Bool} = E.Le.trans(mb, Nat.mul(B, S), rs, E.Le.eq(mb, Nat.mul(B, S), hmb), E2.Le.mulr(B, R, S, hB))
  +hla1 : {RD.Nat.lt(R, la) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(R, la), RD.Nat.lt(S, Nat.double(la)), False{}, Equal.sym(Bool, RD.Nat.lt(S, Nat.double(la)), RD.Nat.lt(R, la), E.Lt.dd(R, la)), hla)
  +hlb1 : {RD.Nat.lt(R, lb) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(R, lb), RD.Nat.lt(S, Nat.double(lb)), False{}, Equal.sym(Bool, RD.Nat.lt(S, Nat.double(lb)), RD.Nat.lt(R, lb), E.Lt.dd(R, lb)), hlb)
  +hrp : {RD.Nat.lt(P, rs) == False{} : Bool} = E.Le.eq(rs, P, Equal.sym(Nat, P, rs, hP))
  +hrr : {RD.Nat.lt(P, rr) == False{} : Bool} = E.Le.trans(rr, rs, P, E2.Le.mull(R, R, S, E2.Le.dbl(R)), hrp)
  +z1 = I.Int.add(P1, I.Int.neg(pi))
  +w1 = I.Int.add(RD.Int.signed(I.Int.mul(ah, bh), Nat.double(Nat.double(Nat.mul(A, B)))), I.Int.neg(RD.Int.signed(pi, Q)))
  +ec1 : {E2.Dk.e1(p, ah, bh, pi) == z1 : I.Int} = Pair.fst({E2.Dk.e1(p, ah, bh, pi) == z1 : I.Int}, {z1 == D.Int.sh(p1, w1) : I.Int}, Dko.c1(t, a, b, ah, al, bh, bl, pi, A, B, Q, hal, hbl, hma, hmb, hA, hB, hla, hlb, hpi, herr, h4))
  +gz1 : {z1 == D.Int.sh(p1, w1) : I.Int} = Pair.snd({E2.Dk.e1(p, ah, bh, pi) == z1 : I.Int}, {z1 == D.Int.sh(p1, w1) : I.Int}, Dko.c1(t, a, b, ah, al, bh, bl, pi, A, B, Q, hal, hbl, hma, hmb, hA, hB, hla, hlb, hpi, herr, h4))
  +ep : {p1 == Nat.add(s, t) : Nat} = Equal.cong(Nat, Nat, z => 1n+z, Nat.add(t, 1n+t), 1n+Nat.add(t, t), NL.Nat.add_succ_r(t, t))
  +al2 = Nat.mul(A, lb)
  +em2 : {RD.Int.mag(P2) == Nat.mul(al2, S) : Nat} = Equal.trans(Nat, RD.Int.mag(P2), Nat.mul(ma, lb), Nat.mul(al2, S), E2.Mag.mul(ah, bl),
    Equal.trans(Nat, Nat.mul(ma, lb), Nat.mul(Nat.mul(A, S), lb), Nat.mul(al2, S), Equal.cong(Nat, Nat, z => Nat.mul(z, lb), ma, Nat.mul(A, S), hma),
      R.NatN.eq([A, S, lb], R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(2n)), R.Ml(R.Ml(R.V(0n), R.V(2n)), R.V(1n)), [], [], {==}, Unit{}, {==}, {==})))
  +x2 = E2.Px(p1, P2, al2, s, em2, E.Le.trans(al2, rr, P, E2.Le.mul2(A, R, lb, R, hA, hlb1), hrr))
  +x2g = RD.Int.signed(P2, al2)
  +z2 = I.Int.add(z1, P2)
  +gs : {z1 == D.Int.sh(s, D.Int.sh(t, w1)) : I.Int} = Equal.trans(I.Int, z1, D.Int.sh(p1, w1), D.Int.sh(s, D.Int.sh(t, w1)), gz1,
    Equal.trans(I.Int, D.Int.sh(p1, w1), D.Int.sh(Nat.add(s, t), w1), D.Int.sh(s, D.Int.sh(t, w1)), Equal.cong(Nat, I.Int, z => D.Int.sh(z, w1), p1, Nat.add(s, t), ep),
      Equal.sym(I.Int, D.Int.sh(s, D.Int.sh(t, w1)), D.Int.sh(Nat.add(s, t), w1), Y.Int.sh_sh(s, t, w1))))
  +gz = Equal.trans(I.Int, z2, I.Int.add(D.Int.sh(s, D.Int.sh(t, w1)), D.Int.sh(s, x2g)), D.Int.sh(s, I.Int.add(D.Int.sh(t, w1), x2g)),
    Y.Int.cong2(z1, D.Int.sh(s, D.Int.sh(t, w1)), P2, D.Int.sh(s, x2g), gs, E2.Grid.i(P2, al2, s, em2)),
    Equal.sym(I.Int, D.Int.sh(s, I.Int.add(D.Int.sh(t, w1), x2g)), I.Int.add(D.Int.sh(s, D.Int.sh(t, w1)), D.Int.sh(s, x2g)), Y.Int.sh_add(s, D.Int.sh(t, w1), x2g)))
  +r2 = I.Int.add(err, I.Int.add(I.Int.neg(P3), I.Int.neg(P4)))
  +i2 : {z2 == r2 : I.Int} = BP.IntN(env, R.Ad(R.Ad(R.Ml(R.V(2n), R.V(4n)), R.Ng(R.V(6n))), R.Ml(R.V(2n), R.V(5n))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ng(R.V(6n))), R.Ad(R.Ng(R.Ml(R.V(3n), R.V(4n))), R.Ng(R.Ml(R.V(3n), R.V(5n))))), [R.Ad(R.V(4n), R.V(5n)), R.V(0n)], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(0n), R.Ng(R.V(2n))))), R.Ad(R.V(5n), R.Ng(R.Ad(R.V(1n), R.Ng(R.V(4n)))))], {==}, (E2.IntZ(env, R.V(3n), R.Ad(R.V(0n), R.Ng(R.V(2n))), hal), (E2.IntZ(env, R.V(5n), R.Ad(R.V(1n), R.Ng(R.V(4n))), hbl), Unit{})))
  +bd = Nat.add(ee, Nat.add(Nat.mul(la, mb), Nat.mul(la, lb)))
  hm = E.Le.trans(RD.Int.mag(z2), RD.Int.mag(r2), bd, E.Le.eq(RD.Int.mag(z2), RD.Int.mag(r2), Equal.cong(I.Int, Nat, z => RD.Int.mag(z), z2, r2, i2)),
    E2.Tri.e(err, I.Int.add(I.Int.neg(P3), I.Int.neg(P4)), Nat.add(Nat.mul(la, mb), Nat.mul(la, lb)), E2.Tri.nm(al, bh, I.Int.neg(P4), Nat.mul(la, lb), E2.Mag.negm(al, bl))))
  hzb = E.Le.trans(RD.Int.mag(z2), Nat.mul(rs, S), Nat.mul(P, S),
    E2.Le.half(RD.Int.mag(z2), Nat.mul(rs, S), E.Le.trans(Nat.double(RD.Int.mag(z2)), Nat.double(bd), Nat.add(Nat.mul(rs, S), Nat.mul(rs, S)), E.Le.dd(RD.Int.mag(z2), bd, hm), B2o(R, ee, ma, mb, la, lb, herr, hma2, hmb2, hla, hlb, h4))),
    E.Le.eq(Nat.mul(rs, S), Nat.mul(P, S), Equal.cong(Nat, Nat, z => Nat.mul(z, S), rs, P, Equal.sym(Nat, P, rs, hP))))
  +ez = E.RNi.exact(p, z2, E2.Rep(p1, z2, I.Int.add(D.Int.sh(t, w1), x2g), s, gz, hzb))
  Equal.trans(I.Int, E2.Dk.e2(p, ah, bh, bl, pi), E.RNi(p, z2), z2,
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(E2.Dk.e1(p, ah, bh, pi), E.RNi(p, P2)), z2, Y.Int.cong2(E2.Dk.e1(p, ah, bh, pi), z1, E.RNi(p, P2), P2, ec1, x2)), ez)

# e3 = e2 + al bh exactly: |e3| <= 2^p
def Dko.c3(+t: Nat, +a: I.Int, +b: I.Int, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int, +A: Nat, +B: Nat, +Q: Nat,
  +hal: {al == I.Int.add(a, I.Int.neg(ah)) : I.Int}, +hbl: {bl == I.Int.add(b, I.Int.neg(bh)) : I.Int},
  +hma: {RD.Int.mag(ah) == Nat.mul(A, RD.Nat.pow2(1n+1n+t)) : Nat}, +hmb: {RD.Int.mag(bh) == Nat.mul(B, RD.Nat.pow2(1n+1n+t)) : Nat},
  +hA: {RD.Nat.lt(RD.Nat.pow2(1n+t), A) == False{} : Bool}, +hB: {RD.Nat.lt(RD.Nat.pow2(1n+t), B) == False{} : Bool},
  +hla: {RD.Nat.lt(RD.Nat.pow2(1n+1n+t), Nat.double(RD.Int.mag(al))) == False{} : Bool}, +hlb: {RD.Nat.lt(RD.Nat.pow2(1n+1n+t), Nat.double(RD.Int.mag(bl))) == False{} : Bool},
  +hpi: {RD.Int.mag(pi) == Nat.mul(Q, RD.Nat.pow2(Nat.add(1n+t, 1n+t))) : Nat}, +herr: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+t), RD.Nat.pow2(1n+1n+t)), Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))))) == False{} : Bool},
  +h4: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+t), RD.Nat.pow2(1n+t)), Nat.add(Nat.add(Nat.add(RD.Nat.pow2(1n+t), RD.Nat.pow2(1n+t)), RD.Nat.pow2(1n+t)), RD.Nat.pow2(1n+t))) == False{} : Bool})
  -> {E2.Dk.e3(1n+Nat.add(1n+t, 1n+t), ah, al, bh, bl, pi) == I.Int.add(I.Int.add(I.Int.add(I.Int.mul(ah, bh), I.Int.neg(pi)), I.Int.mul(ah, bl)), I.Int.mul(al, bh)) : I.Int}:
  +s1 : Nat = 1n+t
  +s : Nat = 1n+s1
  +p1 = Nat.add(s1, s1)
  +p : Nat = 1n+p1
  +R = RD.Nat.pow2(s1)
  +S = RD.Nat.pow2(s)
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(p)
  +rs = Nat.mul(R, S)
  +rr = Nat.mul(R, R)
  +hH : {H == rr : Nat} = BP.Pow2.add(s1, s1)
  +hP : {P == rs : Nat} = Equal.trans(Nat, P, Nat.double(rr), rs, Equal.cong(Nat, Nat, z => Nat.double(z), H, rr, hH), Equal.sym(Nat, rs, Nat.double(rr), R.Nat.mul_double(R, R)))
  +ma = RD.Int.mag(ah)
  +mb = RD.Int.mag(bh)
  +la = RD.Int.mag(al)
  +lb = RD.Int.mag(bl)
  +err = I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))
  +ee = RD.Int.mag(err)
  +P1 = I.Int.mul(ah, bh)
  +P2 = I.Int.mul(ah, bl)
  +P3 = I.Int.mul(al, bh)
  +P4 = I.Int.mul(al, bl)
  +env : List<&2, I.Int> = [a, b, ah, al, bh, bl, pi]
  +hma2 : {RD.Nat.lt(rs, ma) == False{} : Bool} = E.Le.trans(ma, Nat.mul(A, S), rs, E.Le.eq(ma, Nat.mul(A, S), hma), E2.Le.mulr(A, R, S, hA))
  +hmb2 : {RD.Nat.lt(rs, mb) == False{} : Bool} = E.Le.trans(mb, Nat.mul(B, S), rs, E.Le.eq(mb, Nat.mul(B, S), hmb), E2.Le.mulr(B, R, S, hB))
  +hla1 : {RD.Nat.lt(R, la) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(R, la), RD.Nat.lt(S, Nat.double(la)), False{}, Equal.sym(Bool, RD.Nat.lt(S, Nat.double(la)), RD.Nat.lt(R, la), E.Lt.dd(R, la)), hla)
  +hlb1 : {RD.Nat.lt(R, lb) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(R, lb), RD.Nat.lt(S, Nat.double(lb)), False{}, Equal.sym(Bool, RD.Nat.lt(S, Nat.double(lb)), RD.Nat.lt(R, lb), E.Lt.dd(R, lb)), hlb)
  +hrp : {RD.Nat.lt(P, rs) == False{} : Bool} = E.Le.eq(rs, P, Equal.sym(Nat, P, rs, hP))
  +hrr : {RD.Nat.lt(P, rr) == False{} : Bool} = E.Le.trans(rr, rs, P, E2.Le.mull(R, R, S, E2.Le.dbl(R)), hrp)
  +z2 = I.Int.add(I.Int.add(I.Int.mul(ah, bh), I.Int.neg(pi)), I.Int.mul(ah, bl))
  +la2 = Nat.mul(la, B)
  +em3 : {RD.Int.mag(P3) == Nat.mul(la2, S) : Nat} = Equal.trans(Nat, RD.Int.mag(P3), Nat.mul(la, mb), Nat.mul(la2, S), E2.Mag.mul(al, bh),
    Equal.trans(Nat, Nat.mul(la, mb), Nat.mul(la, Nat.mul(B, S)), Nat.mul(la2, S), Equal.cong(Nat, Nat, z => Nat.mul(la, z), mb, Nat.mul(B, S), hmb),
      R.NatN.eq([la, B, S], R.Ml(R.V(0n), R.Ml(R.V(1n), R.V(2n))), R.Ml(R.Ml(R.V(0n), R.V(1n)), R.V(2n)), [], [], {==}, Unit{}, {==}, {==})))
  +x3 = E2.Px(p1, P3, la2, s, em3, E.Le.trans(la2, rr, P, E2.Le.mul2(la, R, B, R, hla1, hB), hrr))
  +z3 = I.Int.add(z2, P3)
  +r3 = I.Int.add(err, I.Int.neg(P4))
  +i3 : {z3 == r3 : I.Int} = BP.IntN(env, R.Ad(R.Ad(R.Ad(R.Ml(R.V(2n), R.V(4n)), R.Ng(R.V(6n))), R.Ml(R.V(2n), R.V(5n))), R.Ml(R.V(3n), R.V(4n))), R.Ad(R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ng(R.V(6n))), R.Ng(R.Ml(R.V(3n), R.V(5n)))), [R.Ad(R.V(4n), R.V(5n)), R.V(0n)], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(0n), R.Ng(R.V(2n))))), R.Ad(R.V(5n), R.Ng(R.Ad(R.V(1n), R.Ng(R.V(4n)))))], {==}, (E2.IntZ(env, R.V(3n), R.Ad(R.V(0n), R.Ng(R.V(2n))), hal), (E2.IntZ(env, R.V(5n), R.Ad(R.V(1n), R.Ng(R.V(4n))), hbl), Unit{})))
  +bd = Nat.add(ee, Nat.mul(la, lb))
  hm = E.Le.trans(RD.Int.mag(z3), RD.Int.mag(r3), bd, E.Le.eq(RD.Int.mag(z3), RD.Int.mag(r3), Equal.cong(I.Int, Nat, z => RD.Int.mag(z), z3, r3, i3)),
    E2.Tri.e(err, I.Int.neg(P4), Nat.mul(la, lb), E2.Mag.negm(al, bl)))
  hzb = E.Le.trans(RD.Int.mag(z3), rs, P,
    E2.Le.half(RD.Int.mag(z3), rs, E.Le.trans(Nat.double(RD.Int.mag(z3)), Nat.double(bd), Nat.add(rs, rs), E.Le.dd(RD.Int.mag(z3), bd, hm), B3o(R, ee, la, lb, herr, hla, hlb))), hrp)
  Equal.trans(I.Int, E2.Dk.e3(p, ah, al, bh, bl, pi), E.RNi(p, z3), z3,
    Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(E2.Dk.e2(p, ah, bh, bl, pi), E.RNi(p, P3)), z3, Y.Int.cong2(E2.Dk.e2(p, ah, bh, bl, pi), z2, E.RNi(p, P3), P3, Dko.c2(t, a, b, ah, al, bh, bl, pi, A, B, Q, hal, hbl, hma, hmb, hA, hB, hla, hlb, hpi, herr, h4), x3)),
    E2.Pxs(p1, z3, hzb))

# e = e3 + al bl = err exactly, so pi + e = a b
def Dko.core(+t: Nat, +a: I.Int, +b: I.Int, +ah: I.Int, +al: I.Int, +bh: I.Int, +bl: I.Int, +pi: I.Int, +A: Nat, +B: Nat, +Q: Nat,
  +hal: {al == I.Int.add(a, I.Int.neg(ah)) : I.Int}, +hbl: {bl == I.Int.add(b, I.Int.neg(bh)) : I.Int},
  +hma: {RD.Int.mag(ah) == Nat.mul(A, RD.Nat.pow2(1n+1n+t)) : Nat}, +hmb: {RD.Int.mag(bh) == Nat.mul(B, RD.Nat.pow2(1n+1n+t)) : Nat},
  +hA: {RD.Nat.lt(RD.Nat.pow2(1n+t), A) == False{} : Bool}, +hB: {RD.Nat.lt(RD.Nat.pow2(1n+t), B) == False{} : Bool},
  +hla: {RD.Nat.lt(RD.Nat.pow2(1n+1n+t), Nat.double(RD.Int.mag(al))) == False{} : Bool}, +hlb: {RD.Nat.lt(RD.Nat.pow2(1n+1n+t), Nat.double(RD.Int.mag(bl))) == False{} : Bool},
  +hpi: {RD.Int.mag(pi) == Nat.mul(Q, RD.Nat.pow2(Nat.add(1n+t, 1n+t))) : Nat}, +herr: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+t), RD.Nat.pow2(1n+1n+t)), Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))))) == False{} : Bool},
  +h4: {RD.Nat.lt(Nat.mul(RD.Nat.pow2(1n+t), RD.Nat.pow2(1n+t)), Nat.add(Nat.add(Nat.add(RD.Nat.pow2(1n+t), RD.Nat.pow2(1n+t)), RD.Nat.pow2(1n+t)), RD.Nat.pow2(1n+t))) == False{} : Bool})
  -> {I.Int.add(pi, E2.Dk.e(1n+Nat.add(1n+t, 1n+t), ah, al, bh, bl, pi)) == I.Int.mul(a, b) : I.Int}:
  +s1 : Nat = 1n+t
  +s : Nat = 1n+s1
  +p1 = Nat.add(s1, s1)
  +p : Nat = 1n+p1
  +R = RD.Nat.pow2(s1)
  +S = RD.Nat.pow2(s)
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(p)
  +rs = Nat.mul(R, S)
  +rr = Nat.mul(R, R)
  +hH : {H == rr : Nat} = BP.Pow2.add(s1, s1)
  +hP : {P == rs : Nat} = Equal.trans(Nat, P, Nat.double(rr), rs, Equal.cong(Nat, Nat, z => Nat.double(z), H, rr, hH), Equal.sym(Nat, rs, Nat.double(rr), R.Nat.mul_double(R, R)))
  +ma = RD.Int.mag(ah)
  +mb = RD.Int.mag(bh)
  +la = RD.Int.mag(al)
  +lb = RD.Int.mag(bl)
  +err = I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))
  +ee = RD.Int.mag(err)
  +P1 = I.Int.mul(ah, bh)
  +P2 = I.Int.mul(ah, bl)
  +P3 = I.Int.mul(al, bh)
  +P4 = I.Int.mul(al, bl)
  +env : List<&2, I.Int> = [a, b, ah, al, bh, bl, pi]
  +hma2 : {RD.Nat.lt(rs, ma) == False{} : Bool} = E.Le.trans(ma, Nat.mul(A, S), rs, E.Le.eq(ma, Nat.mul(A, S), hma), E2.Le.mulr(A, R, S, hA))
  +hmb2 : {RD.Nat.lt(rs, mb) == False{} : Bool} = E.Le.trans(mb, Nat.mul(B, S), rs, E.Le.eq(mb, Nat.mul(B, S), hmb), E2.Le.mulr(B, R, S, hB))
  +hla1 : {RD.Nat.lt(R, la) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(R, la), RD.Nat.lt(S, Nat.double(la)), False{}, Equal.sym(Bool, RD.Nat.lt(S, Nat.double(la)), RD.Nat.lt(R, la), E.Lt.dd(R, la)), hla)
  +hlb1 : {RD.Nat.lt(R, lb) == False{} : Bool} = Equal.trans(Bool, RD.Nat.lt(R, lb), RD.Nat.lt(S, Nat.double(lb)), False{}, Equal.sym(Bool, RD.Nat.lt(S, Nat.double(lb)), RD.Nat.lt(R, lb), E.Lt.dd(R, lb)), hlb)
  +hrp : {RD.Nat.lt(P, rs) == False{} : Bool} = E.Le.eq(rs, P, Equal.sym(Nat, P, rs, hP))
  +hrr : {RD.Nat.lt(P, rr) == False{} : Bool} = E.Le.trans(rr, rs, P, E2.Le.mull(R, R, S, E2.Le.dbl(R)), hrp)
  +z3 = I.Int.add(I.Int.add(I.Int.add(I.Int.mul(ah, bh), I.Int.neg(pi)), I.Int.mul(ah, bl)), I.Int.mul(al, bh))
  +x4 = E2.Pxs(p1, P4, E.Le.trans(RD.Int.mag(P4), rr, P, E.Le.trans(RD.Int.mag(P4), Nat.mul(la, lb), rr, E.Le.eq(RD.Int.mag(P4), Nat.mul(la, lb), E2.Mag.mul(al, bl)), E2.Le.mul2(la, R, lb, R, hla1, hlb1)), hrr))
  +z4 = I.Int.add(z3, P4)
  +i4 : {z4 == err : I.Int} = BP.IntN(env, R.Ad(R.Ad(R.Ad(R.Ad(R.Ml(R.V(2n), R.V(4n)), R.Ng(R.V(6n))), R.Ml(R.V(2n), R.V(5n))), R.Ml(R.V(3n), R.V(4n))), R.Ml(R.V(3n), R.V(5n))), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ng(R.V(6n))), [R.Ad(R.V(4n), R.V(5n)), R.V(0n)], [R.Ad(R.V(3n), R.Ng(R.Ad(R.V(0n), R.Ng(R.V(2n))))), R.Ad(R.V(5n), R.Ng(R.Ad(R.V(1n), R.Ng(R.V(4n)))))], {==}, (E2.IntZ(env, R.V(3n), R.Ad(R.V(0n), R.Ng(R.V(2n))), hal), (E2.IntZ(env, R.V(5n), R.Ad(R.V(1n), R.Ng(R.V(4n))), hbl), Unit{})))
  hzb = E.Le.trans(RD.Int.mag(z4), ee, P, E.Le.eq(RD.Int.mag(z4), ee, Equal.cong(I.Int, Nat, z => RD.Int.mag(z), z4, err, i4)), E.Le.trans(ee, rs, P, E2.Le.of_dbl(ee, rs, herr), hrp))
  +ez : {E2.Dk.e(p, ah, al, bh, bl, pi) == err : I.Int} = Equal.trans(I.Int, E2.Dk.e(p, ah, al, bh, bl, pi), z4, err,
    Equal.trans(I.Int, E2.Dk.e(p, ah, al, bh, bl, pi), E.RNi(p, z4), z4,
      Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.add(E2.Dk.e3(p, ah, al, bh, bl, pi), E.RNi(p, P4)), z4, Y.Int.cong2(E2.Dk.e3(p, ah, al, bh, bl, pi), z3, E.RNi(p, P4), P4, Dko.c3(t, a, b, ah, al, bh, bl, pi, A, B, Q, hal, hbl, hma, hmb, hA, hB, hla, hlb, hpi, herr, h4), x4)),
      E2.Pxs(p1, z4, hzb)), i4)
  Equal.trans(I.Int, I.Int.add(pi, E2.Dk.e(p, ah, al, bh, bl, pi)), I.Int.add(pi, err), I.Int.mul(a, b), Equal.cong(I.Int, I.Int, z => I.Int.add(pi, z), E2.Dk.e(p, ah, al, bh, bl, pi), err, ez),
    BP.IntN([a, b, pi], R.Ad(R.V(2n), R.Ad(R.Ml(R.V(0n), R.V(1n)), R.Ng(R.V(2n)))), R.Ml(R.V(0n), R.V(1n)), [], [], {==}, Unit{}))

# Normalised inputs
# ------------------

# the split of a normalised n, as Dko.core needs it (p = 2s - 1)
def Spo.facts.h(+t: Nat, +n: Nat, +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+Nat.add(1n+t, 1n+t))) == True{} : Bool}, +hh: {RD.Nat.lt(n, RD.Nat.pow2(Nat.add(1n+t, 1n+t))) == False{} : Bool},
  +hc: {RD.Nat.lt(RD.Nat.pow2(1n+Nat.add(1n+t, 1n+t)), 1n+RD.Nat.pow2(1n+1n+t)) == False{} : Bool})
  -> {RD.Int.mag(E2.Sp.h(1n+Nat.add(1n+t, 1n+t), 1n+1n+t, I.IPos{n})) == Nat.mul(E2.V.ah(1n+Nat.add(1n+t, 1n+t), 1n+1n+t, n), RD.Nat.pow2(1n+1n+t)) : Nat}:
  +p1 = Nat.add(1n+t, 1n+t)
  +p : Nat = 1n+p1
  +s : Nat = 1n+1n+t
  +fn = E.Small(p1, n, E2.Lt.to_le(n, RD.Nat.pow2(p), hn))
  +hi = E2.V.hi(p, s, n)
  +eh = Pair.fst({E2.Sp.h(p, s, I.IPos{n}) == I.IPos{hi} : I.Int}, {E2.Sp.l(p, s, I.IPos{n}) == I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{hi})) : I.Int}, E2.Sp.pos(p1, s, n, fn))
  Equal.trans(Nat, RD.Int.mag(E2.Sp.h(p, s, I.IPos{n})), hi, Nat.mul(E2.V.ah(p, s, n), RD.Nat.pow2(s)), Equal.cong(I.Int, Nat, z => RD.Int.mag(z), E2.Sp.h(p, s, I.IPos{n}), I.IPos{hi}, eh), E2.V.hi.grid(p1, s, n, hn, hh, hc))

def Spo.facts.l(+t: Nat, +n: Nat, +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+Nat.add(1n+t, 1n+t))) == True{} : Bool})
  -> E.Le(Nat.double(RD.Int.mag(E2.Sp.l(1n+Nat.add(1n+t, 1n+t), 1n+1n+t, I.IPos{n}))), RD.Nat.pow2(1n+1n+t)):
  +p1 = Nat.add(1n+t, 1n+t)
  +p : Nat = 1n+p1
  +s : Nat = 1n+1n+t
  +fn = E.Small(p1, n, E2.Lt.to_le(n, RD.Nat.pow2(p), hn))
  +hi = E2.V.hi(p, s, n)
  +el = Pair.snd({E2.Sp.h(p, s, I.IPos{n}) == I.IPos{hi} : I.Int}, {E2.Sp.l(p, s, I.IPos{n}) == I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{hi})) : I.Int}, E2.Sp.pos(p1, s, n, fn))
  +em = Equal.trans(Nat, RD.Int.mag(E2.Sp.l(p, s, I.IPos{n})), RD.Int.mag(I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{hi}))), E.Dist(E2.V.d(p, s, n), E2.V.x(p, s, n)),
    Equal.cong(I.Int, Nat, z => RD.Int.mag(z), E2.Sp.l(p, s, I.IPos{n}), I.Int.add(I.IPos{n}, I.Int.neg(I.IPos{hi})), el), E2.V.lo.mag(p1, s, n, fn))
  E.Le.trans(Nat.double(RD.Int.mag(E2.Sp.l(p, s, I.IPos{n}))), Nat.double(E.Dist(E2.V.d(p, s, n), E2.V.x(p, s, n))), RD.Nat.pow2(s),
    E.Le.eq(Nat.double(RD.Int.mag(E2.Sp.l(p, s, I.IPos{n}))), Nat.double(E.Dist(E2.V.d(p, s, n), E2.V.x(p, s, n))), Equal.cong(Nat, Nat, z => Nat.double(z), RD.Int.mag(E2.Sp.l(p, s, I.IPos{n})), E.Dist(E2.V.d(p, s, n), E2.V.x(p, s, n)), em)),
    E2.V.lo.le(p1, s, n, hn))


# Dekker's product is exact on normalised positive inputs at p = 2s - 1,
# s >= 3: for n, m in [2^(p-1), 2^p), pi + e = n m
def TwoProd.norm.odd(+t2: Nat, +n: Nat, +m: Nat,
  +hn: {RD.Nat.lt(n, RD.Nat.pow2(1n+Nat.add(1n+1n+t2, 1n+1n+t2))) == True{} : Bool}, +hhn: {RD.Nat.lt(n, RD.Nat.pow2(Nat.add(1n+1n+t2, 1n+1n+t2))) == False{} : Bool},
  +hm: {RD.Nat.lt(m, RD.Nat.pow2(1n+Nat.add(1n+1n+t2, 1n+1n+t2))) == True{} : Bool}, +hhm: {RD.Nat.lt(m, RD.Nat.pow2(Nat.add(1n+1n+t2, 1n+1n+t2))) == False{} : Bool})
  -> {I.Int.add(E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), I.IPos{n}, I.IPos{m}), E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, I.IPos{n}, I.IPos{m})) == I.Int.mul(I.IPos{n}, I.IPos{m}) : I.Int}:
  +t : Nat = 1n+t2
  +s1 : Nat = 1n+t
  +s : Nat = 1n+s1
  +p1 = Nat.add(s1, s1)
  +p : Nat = 1n+p1
  +R = RD.Nat.pow2(s1)
  +S = RD.Nat.pow2(s)
  +H = RD.Nat.pow2(p1)
  +P = RD.Nat.pow2(p)
  +rs = Nat.mul(R, S)
  +rr = Nat.mul(R, R)
  +hH : {H == rr : Nat} = BP.Pow2.add(s1, s1)
  +hP : {P == rs : Nat} = Equal.trans(Nat, P, Nat.double(rr), rs, Equal.cong(Nat, Nat, z => Nat.double(z), H, rr, hH), Equal.sym(Nat, rs, Nat.double(rr), R.Nat.mul_double(R, R)))
  +h4 : {RD.Nat.lt(rr, Nat.add(Nat.add(Nat.add(R, R), R), R)) == False{} : Bool} = E2.Sq4(t2)
  # s <= p - 1, so 1 + 2^s <= 2^(p-1) + 2^(p-1) = 2^p
  +es : {p1 == Nat.add(s, t) : Nat} = Equal.cong(Nat, Nat, z => 1n+z, Nat.add(t, 1n+t), 1n+Nat.add(t, t), NL.Nat.add_succ_r(t, t))
  +hsh : {RD.Nat.lt(H, S) == False{} : Bool} = E2.Pow2.mono(s, p1, E.Ge.of(p1, s, t, es))
  +hc : {RD.Nat.lt(P, 1n+S) == False{} : Bool} = E.Le.trans(1n+S, Nat.add(H, H), P, E2.Le.add2(1n, H, S, H, E2.Le.one(p1), hsh),
    E.Le.eq(Nat.add(H, H), P, Equal.sym(Nat, Nat.double(H), Nat.add(H, H), Y.Nat.double_add(H))))
  +a : I.Int = I.IPos{n}
  +b : I.Int = I.IPos{m}
  +nm = Nat.mul(n, m)
  +fn = E.Small(p1, n, E2.Lt.to_le(n, P, hn))
  +fm = E.Small(p1, m, E2.Lt.to_le(m, P, hm))
  +ep : {I.Int.mul(a, b) == I.IPos{nm} : I.Int} = E2.Int.mulpp(n, m)
  +pi = E2.TP.p(p, a, b)
  +epi : {pi == I.IPos{E.Rn(p, nm)} : I.Int} = Equal.cong(I.Int, I.Int, z => E.RNi(p, z), I.Int.mul(a, b), I.IPos{nm}, ep)
  +hpi : {RD.Int.mag(pi) == Nat.mul(E2.Gq(p, nm, p1), H) : Nat} = Equal.trans(Nat, RD.Int.mag(pi), E.Rn(p, nm), Nat.mul(E2.Gq(p, nm, p1), H), Equal.cong(I.Int, Nat, z => RD.Int.mag(z), pi, I.IPos{E.Rn(p, nm)}, epi),
    E2.Grid(p1, nm, p1, E2.Le.mul2(H, n, H, m, hhn, hhm)))
  +hlt = E2.Lt.le_trans(nm, Nat.mul(P, m), Nat.mul(P, P), E.Lt.mono(n, P, m, hn, E2.Lt.le_trans(0n, H, m, BP.Pow2.pos(p1), hhm)), E2.Le.mull(P, m, P, E2.Lt.to_le(m, P, hm)))
  +eer : {RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))) == E.Dist(E.Rn(p, nm), nm) : Nat} = Equal.trans(Nat, RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))), RD.Int.mag(I.Int.add(I.IPos{nm}, I.Int.neg(I.IPos{E.Rn(p, nm)}))), E.Dist(E.Rn(p, nm), nm),
    Equal.cong(I.Int, Nat, z => RD.Int.mag(z), I.Int.add(I.Int.mul(a, b), I.Int.neg(pi)), I.Int.add(I.IPos{nm}, I.Int.neg(I.IPos{E.Rn(p, nm)})), Y.Int.cong2(I.Int.mul(a, b), I.IPos{nm}, I.Int.neg(pi), I.Int.neg(I.IPos{E.Rn(p, nm)}), ep, Equal.cong(I.Int, I.Int, z => I.Int.neg(z), pi, I.IPos{E.Rn(p, nm)}, epi))),
    Equal.trans(Nat, RD.Int.mag(I.Int.add(I.IPos{nm}, I.Int.neg(I.IPos{E.Rn(p, nm)}))), E.Dist(nm, E.Rn(p, nm)), E.Dist(E.Rn(p, nm), nm), E.Mag.diff(nm, E.Rn(p, nm)), E.Dist.comm(nm, E.Rn(p, nm))))
  +herr : {RD.Nat.lt(rs, Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))))) == False{} : Bool} = E.Le.trans(Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi)))), P, rs,
    E.Le.trans(Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi)))), Nat.double(E.Dist(E.Rn(p, nm), nm)), P, E.Le.eq(Nat.double(RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi)))), Nat.double(E.Dist(E.Rn(p, nm), nm)), Equal.cong(Nat, Nat, z => Nat.double(z), RD.Int.mag(I.Int.add(I.Int.mul(a, b), I.Int.neg(pi))), E.Dist(E.Rn(p, nm), nm), eer)),
      E.Le.trans(Nat.double(E.Dist(E.Rn(p, nm), nm)), RD.Nat.pow2(E2.Shf(p, nm)), P, E2.ErrH(p1, nm), E2.Pow2.mono(E2.Shf(p, nm), p, E2.S3(p1, nm, p, hlt)))),
    E.Le.eq(P, rs, hP))
  Dko.core(t, a, b, E2.Sp.h(p, s, a), E2.Sp.l(p, s, a), E2.Sp.h(p, s, b), E2.Sp.l(p, s, b), pi, E2.V.ah(p, s, n), E2.V.ah(p, s, m), E2.Gq(p, nm, p1),
    E2.Split(p1, s, a, fn), E2.Split(p1, s, b, fm), Spo.facts.h(t, n, hn, hhn, hc), Spo.facts.h(t, m, hm, hhm, hc),
    E2.V.ah.le(p1, s, s1, n, hn, hhn, hc, hP), E2.V.ah.le(p1, s, s1, m, hm, hhm, hc, hP), Spo.facts.l(t, n, hn), Spo.facts.l(t, m, hm), hpi, herr, h4)

# All representable inputs
# ------------------------

# n 2^i = N 2^j and m 2^k = M 2^l with N, M normalised: scale, apply
# TwoProd.norm, scale back
def TPo.asm(+t2: Nat, +n: Nat, +m: Nat, +i: Nat, +j: Nat, +nn: Nat, +e1: {Nat.mul(n, RD.Nat.pow2(i)) == Nat.mul(nn, RD.Nat.pow2(j)) : Nat}, +hnn1: {RD.Nat.lt(nn, RD.Nat.pow2(1n+Nat.add(1n+1n+t2, 1n+1n+t2))) == True{} : Bool}, +hnn2: {RD.Nat.lt(nn, RD.Nat.pow2(Nat.add(1n+1n+t2, 1n+1n+t2))) == False{} : Bool},
  +k: Nat, +l: Nat, +mm: Nat, +e2: {Nat.mul(m, RD.Nat.pow2(k)) == Nat.mul(mm, RD.Nat.pow2(l)) : Nat}, +hmm1: {RD.Nat.lt(mm, RD.Nat.pow2(1n+Nat.add(1n+1n+t2, 1n+1n+t2))) == True{} : Bool}, +hmm2: {RD.Nat.lt(mm, RD.Nat.pow2(Nat.add(1n+1n+t2, 1n+1n+t2))) == False{} : Bool})
  -> {E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, I.IPos{n}, I.IPos{m}) == I.Int.mul(I.IPos{n}, I.IPos{m}) : I.Int}:
  +a : I.Int = I.IPos{n}
  +b : I.Int = I.IPos{m}
  +a2 : I.Int = I.IPos{nn}
  +b2 : I.Int = I.IPos{mm}
  +ea = E2.Sh.eq(i, j, n, nn, e1)
  +eb = E2.Sh.eq(k, l, m, mm, e2)
  +ik = Nat.add(i, k)
  +jl = Nat.add(j, l)
  +x = E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a, b)
  +q1 = Y.Int.sh_add(ik, E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), a, b), E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a, b))
  +q2 = Y.Int.cong2(D.Int.sh(ik, E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), a, b)), E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), D.Int.sh(i, a), D.Int.sh(k, b)), D.Int.sh(ik, E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a, b)), E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Int.sh(i, a), D.Int.sh(k, b)),
    Equal.sym(I.Int, E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), D.Int.sh(i, a), D.Int.sh(k, b)), D.Int.sh(ik, E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), a, b)), E2.TP.sh.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), i, k, a, b)), Equal.sym(I.Int, E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Int.sh(i, a), D.Int.sh(k, b)), D.Int.sh(ik, E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a, b)), E2.TP.sh.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, i, k, a, b)))
  +q3 = Equal.trans(I.Int, E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Int.sh(i, a), D.Int.sh(k, b)), E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Int.sh(j, a2), D.Int.sh(k, b)), E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Int.sh(j, a2), D.Int.sh(l, b2)), Equal.cong(I.Int, I.Int, z => E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, z, D.Int.sh(k, b)), D.Int.sh(i, a), D.Int.sh(j, a2), ea), Equal.cong(I.Int, I.Int, z => E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Int.sh(j, a2), z), D.Int.sh(k, b), D.Int.sh(l, b2), eb))
  +q4 = Y.Int.cong2(E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), D.Int.sh(j, a2), D.Int.sh(l, b2)), D.Int.sh(jl, E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), a2, b2)), E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Int.sh(j, a2), D.Int.sh(l, b2)), D.Int.sh(jl, E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a2, b2)), E2.TP.sh.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), j, l, a2, b2), E2.TP.sh.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, j, l, a2, b2))
  +q5 = Equal.sym(I.Int, D.Int.sh(jl, E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a2, b2)), I.Int.add(D.Int.sh(jl, E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), a2, b2)), D.Int.sh(jl, E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a2, b2))), Y.Int.sh_add(jl, E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), a2, b2), E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a2, b2)))
  +q6 = Equal.cong(I.Int, I.Int, z => D.Int.sh(jl, z), E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a2, b2), I.Int.mul(a2, b2), TwoProd.norm.odd(t2, nn, mm, hnn1, hnn2, hmm1, hmm2))
  +q7 = Equal.sym(I.Int, I.Int.mul(D.Int.sh(j, a2), D.Int.sh(l, b2)), D.Int.sh(jl, I.Int.mul(a2, b2)), E2.Sh.mul2(j, l, a2, b2))
  +q8 = Equal.trans(I.Int, I.Int.mul(D.Int.sh(j, a2), D.Int.sh(l, b2)), I.Int.mul(D.Int.sh(i, a), D.Int.sh(l, b2)), I.Int.mul(D.Int.sh(i, a), D.Int.sh(k, b)), Equal.cong(I.Int, I.Int, z => I.Int.mul(z, D.Int.sh(l, b2)), D.Int.sh(j, a2), D.Int.sh(i, a), Equal.sym(I.Int, D.Int.sh(i, a), D.Int.sh(j, a2), ea)), Equal.cong(I.Int, I.Int, z => I.Int.mul(D.Int.sh(i, a), z), D.Int.sh(l, b2), D.Int.sh(k, b), Equal.sym(I.Int, D.Int.sh(k, b), D.Int.sh(l, b2), eb)))
  +q9 = E2.Sh.mul2(i, k, a, b)
  +c1 = Equal.trans(I.Int, D.Int.sh(ik, x), I.Int.add(D.Int.sh(ik, E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), a, b)), D.Int.sh(ik, E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a, b))), E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Int.sh(i, a), D.Int.sh(k, b)), q1, q2)
  +c2 = Equal.trans(I.Int, D.Int.sh(ik, x), E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Int.sh(i, a), D.Int.sh(k, b)), E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Int.sh(j, a2), D.Int.sh(l, b2)), c1, q3)
  +c3 = Equal.trans(I.Int, D.Int.sh(ik, x), E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Int.sh(j, a2), D.Int.sh(l, b2)), I.Int.add(D.Int.sh(jl, E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), a2, b2)), D.Int.sh(jl, E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a2, b2))), c2, q4)
  +c4 = Equal.trans(I.Int, D.Int.sh(ik, x), I.Int.add(D.Int.sh(jl, E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), a2, b2)), D.Int.sh(jl, E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a2, b2))), D.Int.sh(jl, E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a2, b2)), c3, q5)
  +c5 = Equal.trans(I.Int, D.Int.sh(ik, x), D.Int.sh(jl, E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a2, b2)), D.Int.sh(jl, I.Int.mul(a2, b2)), c4, q6)
  +c6 = Equal.trans(I.Int, D.Int.sh(ik, x), D.Int.sh(jl, I.Int.mul(a2, b2)), I.Int.mul(D.Int.sh(j, a2), D.Int.sh(l, b2)), c5, q7)
  +c7 = Equal.trans(I.Int, D.Int.sh(ik, x), I.Int.mul(D.Int.sh(j, a2), D.Int.sh(l, b2)), I.Int.mul(D.Int.sh(i, a), D.Int.sh(k, b)), c6, q8)
  +c8 = Equal.trans(I.Int, D.Int.sh(ik, x), I.Int.mul(D.Int.sh(i, a), D.Int.sh(k, b)), D.Int.sh(ik, I.Int.mul(a, b)), c7, q9)
  Y.Int.sh_inj(ik, x, I.Int.mul(a, b))(c8)

def TPo.pos(+t2: Nat, +n: Nat, +m: Nat, +fn: {E.Rn(1n+Nat.add(1n+1n+t2, 1n+1n+t2), n) == n : Nat}, +fm: {E.Rn(1n+Nat.add(1n+1n+t2, 1n+1n+t2), m) == m : Nat})
  -> {E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, I.IPos{n}, I.IPos{m}) == I.Int.mul(I.IPos{n}, I.IPos{m}) : I.Int}:
  match n:
    case 0n:
      E2.TP.zl(Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, I.IPos{m})
    case 1n+(+n2):
      match m:
        case 0n:
          E2.TP.zr(Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, I.IPos{1n+n2})
        case 1n+(+m2):
          E2.Nz(Nat.add(1n+1n+t2, 1n+1n+t2), 1n+n2, fn, {==}, {E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, I.IPos{1n+n2}, I.IPos{1n+m2}) == I.Int.mul(I.IPos{1n+n2}, I.IPos{1n+m2}) : I.Int},
            i => j => nn => e1 => h1 => h2 => E2.Nz(Nat.add(1n+1n+t2, 1n+1n+t2), 1n+m2, fm, {==}, {E2.Fx(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, I.IPos{1n+n2}, I.IPos{1n+m2}) == I.Int.mul(I.IPos{1n+n2}, I.IPos{1n+m2}) : I.Int},
              k => l => mm => e2 => h3 => h4 => TPo.asm(t2, 1n+n2, 1n+m2, i, j, nn, e1, h1, h2, k, l, mm, e2, h3, h4)))

# Dekker's product is exact at p = 2s - 1 with s >= 3 (binary64: s = 27) for
# every representable a, b: pi = RN(a b) and e give pi + e = a b
def TwoProd.odd(+t2: Nat, +a: I.Int, +b: I.Int, +fa: {E.Rn(1n+Nat.add(1n+1n+t2, 1n+1n+t2), RD.Int.mag(a)) == RD.Int.mag(a) : Nat}, +fb: {E.Rn(1n+Nat.add(1n+1n+t2, 1n+1n+t2), RD.Int.mag(b)) == RD.Int.mag(b) : Nat})
  -> {I.Int.add(E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), a, b), E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, a, b)) == I.Int.mul(a, b) : I.Int}:
  match a b:
    case I.IPos{+n} I.IPos{+m}:
      TPo.pos(t2, n, m, fa, fb)
    case I.INeg{+x} I.IPos{+m}:
      E2.TP.ok.na(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, I.IPos{1n+x}, I.IPos{m}, TPo.pos(t2, 1n+x, m, fa, fb))
    case I.IPos{+n} I.INeg{+y}:
      E2.TP.ok.nb(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, I.IPos{n}, I.IPos{1n+y}, TPo.pos(t2, n, 1n+y, fa, fb))
    case I.INeg{+x} I.INeg{+y}:
      E2.TP.ok.na(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, I.IPos{1n+x}, I.INeg{y}, E2.TP.ok.nb(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, I.IPos{1n+x}, I.IPos{1n+y}, TPo.pos(t2, 1n+x, 1n+y, fa, fb)))


# In dyadic arithmetic
# --------------------

# Dekker's product is exact in binary rounding at p = 2s - 1 bits, s >= 3,
# with no exponent bounds (so, in a binary format, barring underflow and
# overflow): for a = A / 2^k and b = B / 2^k with A, B representable,
# pi = RN(a b) and e give pi + e = a b
def DTwoProd.odd(+t2: Nat, +k: Nat, +aa: I.Int, +bb: I.Int, +fa: {E.Rn(1n+Nat.add(1n+1n+t2, 1n+1n+t2), RD.Int.mag(aa)) == RD.Int.mag(aa) : Nat}, +fb: {E.Rn(1n+Nat.add(1n+1n+t2, 1n+1n+t2), RD.Int.mag(bb)) == RD.Int.mag(bb) : Nat})
  -> {D.Dy.add(E2.DTP.p(Nat.add(1n+1n+t2, 1n+1n+t2), D.Dy.of(k, aa), D.Dy.of(k, bb)), E2.DTP.e(Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Dy.of(k, aa), D.Dy.of(k, bb))) == D.Dy.mul(D.Dy.of(k, aa), D.Dy.of(k, bb)) : D.Dy}:
  +hp = E2.Rr.mul(Nat.add(1n+1n+t2, 1n+1n+t2), k, k, D.Dy.of(k, aa), aa, D.Dy.of(k, bb), bb, {==}, {==})
  +he = E2.DDk.l(Nat.add(1n+1n+t2, 1n+1n+t2), k, E2.DRr.h(Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Dy.of(k, aa)), E2.Sp.h(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, aa), E2.DRr.l(Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Dy.of(k, aa)), E2.Sp.l(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, aa), E2.DRr.h(Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Dy.of(k, bb)), E2.Sp.h(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, bb), E2.DRr.l(Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Dy.of(k, bb)), E2.Sp.l(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, bb), E2.DTP.p(Nat.add(1n+1n+t2, 1n+1n+t2), D.Dy.of(k, aa), D.Dy.of(k, bb)), E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), aa, bb),
    E2.DRr.lh(Nat.add(1n+1n+t2, 1n+1n+t2), k, 1n+1n+1n+t2, aa), E2.DRr.ll(Nat.add(1n+1n+t2, 1n+1n+t2), k, 1n+1n+1n+t2, aa), E2.DRr.lh(Nat.add(1n+1n+t2, 1n+1n+t2), k, 1n+1n+1n+t2, bb), E2.DRr.ll(Nat.add(1n+1n+t2, 1n+1n+t2), k, 1n+1n+1n+t2, bb), hp)
  Equal.trans(D.Dy, D.Dy.add(E2.DTP.p(Nat.add(1n+1n+t2, 1n+1n+t2), D.Dy.of(k, aa), D.Dy.of(k, bb)), E2.DTP.e(Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Dy.of(k, aa), D.Dy.of(k, bb))), D.Dy.of(Nat.add(k, k), I.Int.add(E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), aa, bb), E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, aa, bb))), D.Dy.mul(D.Dy.of(k, aa), D.Dy.of(k, bb)),
    E2.Dadd(Nat.add(k, k), E2.DTP.p(Nat.add(1n+1n+t2, 1n+1n+t2), D.Dy.of(k, aa), D.Dy.of(k, bb)), E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), aa, bb), E2.DTP.e(Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, D.Dy.of(k, aa), D.Dy.of(k, bb)), E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, aa, bb), hp, he),
    Equal.trans(D.Dy, D.Dy.of(Nat.add(k, k), I.Int.add(E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), aa, bb), E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, aa, bb))), D.Dy.of(Nat.add(k, k), I.Int.mul(aa, bb)), D.Dy.mul(D.Dy.of(k, aa), D.Dy.of(k, bb)),
      Y.Of.cong(Nat.add(k, k), Nat.add(k, k), I.Int.add(E2.TP.p(1n+Nat.add(1n+1n+t2, 1n+1n+t2), aa, bb), E2.TP.e(1n+Nat.add(1n+1n+t2, 1n+1n+t2), 1n+1n+1n+t2, aa, bb)), I.Int.mul(aa, bb), {==}, TwoProd.odd(t2, aa, bb, fa, fb)),
      Equal.sym(D.Dy, D.Dy.mul(D.Dy.of(k, aa), D.Dy.of(k, bb)), D.Dy.of(Nat.add(k, k), I.Int.mul(aa, bb)), E2.Mul.of(k, aa, k, bb))))
