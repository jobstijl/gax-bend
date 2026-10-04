# Int is a commutative ring (proofs/int.bend): the generic normaliser,
# instantiated at T = Int with the proven laws, proves an identity over
# Int variables, and the laws compute on literals.
import Base
import ../src/int.bend as I
import ../src/norm.bend as N
import ../proofs/norm.bend as NP
import ../proofs/int.bend as Z

# (x + y)(x - y) = x x - y y, for all integers x and y
def diff_sq(x: I.Int, y: I.Int) -> {I.Int.mul(I.Int.add(x, y), I.Int.add(x, I.Int.neg(y))) == I.Int.add(I.Int.mul(x, x), I.Int.neg(I.Int.mul(y, y))) : I.Int}:
  NP.Norm.eq(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg,
    ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l,
    ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg,
    [x, y], N.TMul{N.TAdd{N.TVar{0n}, N.TVar{1n}}, N.TAdd{N.TVar{0n}, N.TNeg{N.TVar{1n}}}},
    N.TAdd{N.TMul{N.TVar{0n}, N.TVar{0n}}, N.TNeg{N.TMul{N.TVar{1n}, N.TVar{1n}}}}, {==})

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(I.Int.show(I.Int.mul(I.Int.add(I.IPos{7n}, I.INeg{2n}), I.Int.add(I.IPos{7n}, I.Int.neg(I.INeg{2n})))))
    IO.print(I.Int.show(I.Int.add(I.Int.mul(I.IPos{7n}, I.IPos{7n}), I.Int.neg(I.Int.mul(I.INeg{2n}, I.INeg{2n})))))
#|40
#|40
