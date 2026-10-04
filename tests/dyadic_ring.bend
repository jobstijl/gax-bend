# Dyadics are an ordered commutative ring (proofs/dyadic.bend). Two uses
# that need every law: the generic normaliser at T = Dy proves an identity
# over dyadic variables, and a generated kernel's rounding-error law
# (algebras/vga2d/err.bend) is instantiated at T = Dy, every ordered-ring
# hypothesis supplied by a proof. The operations here
# are exact, so the bound holds trivially; a proven rounding takes their
# place next. Values on literals check the arithmetic.
import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/norm.bend as N
import ../src/err.bend as E
import ../proofs/norm.bend as NP
import ../proofs/dyadic.bend as Y
import ../algebras/vga2d/kinds.bend as K
import ../algebras/vga2d/ops.bend as O
import ../algebras/vga2d/err.bend as V

# (x + y)(x - y) = x x - y y, for all dyadics
def diff_sq(x: D.Dy, y: D.Dy) -> {D.Dy.mul(D.Dy.add(x, y), D.Dy.add(x, D.Dy.neg(y))) == D.Dy.add(D.Dy.mul(x, x), D.Dy.neg(D.Dy.mul(y, y))) : D.Dy}:
  NP.Norm.eq(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg,
    ~Y.Dy.r.add_assoc, ~Y.Dy.r.add_comm, ~Y.Dy.r.zero_l, ~Y.Dy.r.add_inv, ~Y.Dy.r.mul_assoc, ~Y.Dy.r.mul_comm, ~Y.Dy.r.unit_r, ~Y.Dy.r.dist_l,
    ~Y.Dy.r.neg_add, ~Y.Dy.r.neg_mul_l, ~Y.Dy.r.neg_neg,
    [x, y], N.TMul{N.TAdd{N.TVar{0n}, N.TVar{1n}}, N.TAdd{N.TVar{0n}, N.TNeg{N.TVar{1n}}}},
    N.TAdd{N.TMul{N.TVar{0n}, N.TVar{0n}}, N.TNeg{N.TMul{N.TVar{1n}, N.TVar{1n}}}}, {==})

# exact operations are within any eps >= 0: |op - op| = 0 <= eps |op|
def exact.go(+eps: D.Dy, +pe: {D.Dy.pos(eps) == True{} : Bool}, +op: D.Dy) -> {D.Dy.pos(D.Dy.add(D.Dy.mul(eps, D.Dy.abs(op)), D.Dy.neg(D.Dy.abs(D.Dy.add(op, D.Dy.neg(op)))))) == True{} : Bool}:
  +q = D.Dy.mul(eps, D.Dy.abs(op))
  %Equal.sym(D.Dy, D.Dy.add(op, D.Dy.neg(op)), D.Dy.zero(), Y.Dy.add_inv(op)) : {D.Dy.pos(D.Dy.add(q, D.Dy.neg(D.Dy.abs(_)))) == True{} : Bool}
  %Equal.sym(D.Dy, D.Dy.add(q, D.Dy.zero()), q, Equal.trans(D.Dy, D.Dy.add(q, D.Dy.zero()), D.Dy.add(D.Dy.zero(), q), q, Y.Dy.add_comm(q, D.Dy.zero()), Y.Dy.zero_l(q))) : {D.Dy.pos(_) == True{} : Bool}
  Y.Dy.pos_mul(eps, D.Dy.abs(op))(pe)(Y.Dy.pos_abs(op))

def exact.add(~eps: D.Dy, ~pe: {D.Dy.pos(eps) == True{} : Bool}, x: D.Dy, y: D.Dy) -> {D.Dy.pos(D.Dy.add(D.Dy.mul(eps, D.Dy.abs(D.Dy.add(x, y))), D.Dy.neg(D.Dy.abs(D.Dy.add(D.Dy.add(x, y), D.Dy.neg(D.Dy.add(x, y))))))) == True{} : Bool}:
  exact.go(eps, pe, D.Dy.add(x, y))

def exact.mul(~eps: D.Dy, ~pe: {D.Dy.pos(eps) == True{} : Bool}, x: D.Dy, y: D.Dy) -> {D.Dy.pos(D.Dy.add(D.Dy.mul(eps, D.Dy.abs(D.Dy.mul(x, y))), D.Dy.neg(D.Dy.abs(D.Dy.add(D.Dy.mul(x, y), D.Dy.neg(D.Dy.mul(x, y))))))) == True{} : Bool}:
  exact.go(eps, pe, D.Dy.mul(x, y))

# the error law of VGA2D's vector product, at T = Dy, for any eps >= 0
# (a concrete eps = 2^-24 would make the checker compute (1 + eps)^k
# exactly, with naturals it does not compute with efficiently)
def vgp(~eps: D.Dy, ~pe: {D.Dy.pos(eps) == True{} : Bool}, a: K.Vector<D.Dy>, b: K.Vector<D.Dy>)
  -> E.Err.Fields(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg, ~D.Dy.pos, ~D.Dy.abs, ~eps,
    K.Rotor.fields(D.Dy, O.Vector.gp.Vector(~D.Dy, ~D.Dy.zero(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg, a, b)),
    K.Rotor.fields(D.Dy, O.Vector.gp.Vector(~D.Dy, ~D.Dy.zero(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg, a, b)),
    K.Rotor.fields(D.Dy, O.Vector.gp.Vector(~D.Dy, ~D.Dy.zero(), ~D.Dy.add, ~D.Dy.mul, ~(x => x), K.Vector.map(~D.Dy, ~D.Dy, ~D.Dy.abs, a), K.Vector.map(~D.Dy, ~D.Dy, ~D.Dy.abs, b))),
    K.Rotor.fields(Nat, O.Vector.gp.Vector(~Nat, ~0n, ~E.Err.dadd, ~E.Err.dmul, ~(x => x), K.Vector{0n, 0n}, K.Vector{0n, 0n}))):
  V.Vector.gp.Vector.err(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg,
    ~Y.Dy.r.add_assoc, ~Y.Dy.r.add_comm, ~Y.Dy.r.zero_l, ~Y.Dy.r.add_inv, ~Y.Dy.r.mul_assoc, ~Y.Dy.r.mul_comm, ~Y.Dy.r.unit_r, ~Y.Dy.r.dist_l,
    ~Y.Dy.r.neg_add, ~Y.Dy.r.neg_mul_l, ~Y.Dy.r.neg_neg,
    ~D.Dy.pos, ~D.Dy.abs, ~Y.Dy.pos_add, ~Y.Dy.pos_mul, ~Y.Dy.pos_abs, ~Y.Dy.tri, ~Y.Dy.abs_mul, ~Y.Dy.abs_neg, ~{==}, ~eps, ~pe,
    ~D.Dy.add, ~D.Dy.mul, ~exact.add(~eps, ~pe), ~exact.mul(~eps, ~pe), a, b)

def main() -> IO(Unit):
  +a = D.Dy.of(3n, I.IPos{3n})
  +b = D.Dy.of(2n, I.INeg{4n})
  do IO<Unit>:
    IO.print(D.Dy.show(D.Dy.add(a, b)) ++ ", " ++ D.Dy.show(D.Dy.mul(a, b)) ++ ", " ++ D.Dy.show(D.Dy.add(a, D.Dy.neg(a))))
#|-7/2^3, -15/2^5, 0/2^0
