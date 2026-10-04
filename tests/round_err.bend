# Concrete floating-point arithmetics with proven error bounds and no
# hypotheses left. On dyadics (src/round.bend), p-bit truncation meets the
# standard model with eps = 2^(1-p) (Round.rel), and round to nearest, ties
# to even, with eps = 2^-p (Rne.rel), IEEE's unit roundoff. So a generated
# kernel's error law holds outright in either arithmetic, for every p.
# Run: p = 2 on z = 11 truncates to 8, an error of 3/11 of |z|: within
# 2^-1, beyond 2^-2. Rounding z = 5 to nearest gives 4 (a tie, to even),
# an error of 1/5: within 2^-2, beyond 2^-3. Neither eps can be halved.
import Base
import ../src/int.bend as I
import ../src/dyadic.bend as D
import ../src/round.bend as RD
import ../src/err.bend as E
import ../proofs/dyadic.bend as Y
import ../proofs/round.bend as R
import ../algebras/vga2d/kinds.bend as K
import ../algebras/vga2d/ops.bend as O
import ../algebras/vga2d/err.bend as V

# VGA2D's vector product in (1 + p1)-bit truncating arithmetic
def vgp(~p1: Nat, a: K.Vector<D.Dy>, b: K.Vector<D.Dy>)
  -> E.Err.Fields(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg, ~D.Dy.pos, ~D.Dy.abs, ~D.Dy.ulp(p1),
    K.Rotor.fields(D.Dy, O.Vector.gp.Vector(~D.Dy, ~D.Dy.zero(), ~RD.Dy.radd(1n+p1), ~RD.Dy.rmul(1n+p1), ~D.Dy.neg, a, b)),
    K.Rotor.fields(D.Dy, O.Vector.gp.Vector(~D.Dy, ~D.Dy.zero(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg, a, b)),
    K.Rotor.fields(D.Dy, O.Vector.gp.Vector(~D.Dy, ~D.Dy.zero(), ~D.Dy.add, ~D.Dy.mul, ~(x => x), K.Vector.map(~D.Dy, ~D.Dy, ~D.Dy.abs, a), K.Vector.map(~D.Dy, ~D.Dy, ~D.Dy.abs, b))),
    K.Rotor.fields(Nat, O.Vector.gp.Vector(~Nat, ~0n, ~E.Err.dadd, ~E.Err.dmul, ~(x => x), K.Vector{0n, 0n}, K.Vector{0n, 0n}))):
  V.Vector.gp.Vector.err(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg,
    ~Y.Dy.r.add_assoc, ~Y.Dy.r.add_comm, ~Y.Dy.r.zero_l, ~Y.Dy.r.add_inv, ~Y.Dy.r.mul_assoc, ~Y.Dy.r.mul_comm, ~Y.Dy.r.unit_r, ~Y.Dy.r.dist_l,
    ~Y.Dy.r.neg_add, ~Y.Dy.r.neg_mul_l, ~Y.Dy.r.neg_neg,
    ~D.Dy.pos, ~D.Dy.abs, ~Y.Dy.pos_add, ~Y.Dy.pos_mul, ~Y.Dy.pos_abs, ~Y.Dy.tri, ~Y.Dy.abs_mul, ~Y.Dy.abs_neg, ~{==}, ~D.Dy.ulp(p1), ~R.Round.eps_pos(p1),
    ~RD.Dy.radd(1n+p1), ~RD.Dy.rmul(1n+p1), ~R.Round.add_ok(p1), ~R.Round.mul_ok(p1), a, b)

# the same law in (1 + p1)-bit round-to-nearest arithmetic, eps = 2^-(1+p1)
def vgp_rne(~p1: Nat, a: K.Vector<D.Dy>, b: K.Vector<D.Dy>)
  -> E.Err.Fields(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg, ~D.Dy.pos, ~D.Dy.abs, ~D.Dy.ulp(1n+p1),
    K.Rotor.fields(D.Dy, O.Vector.gp.Vector(~D.Dy, ~D.Dy.zero(), ~RD.Dy.nadd(1n+p1), ~RD.Dy.nmul(1n+p1), ~D.Dy.neg, a, b)),
    K.Rotor.fields(D.Dy, O.Vector.gp.Vector(~D.Dy, ~D.Dy.zero(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg, a, b)),
    K.Rotor.fields(D.Dy, O.Vector.gp.Vector(~D.Dy, ~D.Dy.zero(), ~D.Dy.add, ~D.Dy.mul, ~(x => x), K.Vector.map(~D.Dy, ~D.Dy, ~D.Dy.abs, a), K.Vector.map(~D.Dy, ~D.Dy, ~D.Dy.abs, b))),
    K.Rotor.fields(Nat, O.Vector.gp.Vector(~Nat, ~0n, ~E.Err.dadd, ~E.Err.dmul, ~(x => x), K.Vector{0n, 0n}, K.Vector{0n, 0n}))):
  V.Vector.gp.Vector.err(~D.Dy, ~D.Dy.zero(), ~D.Dy.one(), ~D.Dy.add, ~D.Dy.mul, ~D.Dy.neg,
    ~Y.Dy.r.add_assoc, ~Y.Dy.r.add_comm, ~Y.Dy.r.zero_l, ~Y.Dy.r.add_inv, ~Y.Dy.r.mul_assoc, ~Y.Dy.r.mul_comm, ~Y.Dy.r.unit_r, ~Y.Dy.r.dist_l,
    ~Y.Dy.r.neg_add, ~Y.Dy.r.neg_mul_l, ~Y.Dy.r.neg_neg,
    ~D.Dy.pos, ~D.Dy.abs, ~Y.Dy.pos_add, ~Y.Dy.pos_mul, ~Y.Dy.pos_abs, ~Y.Dy.tri, ~Y.Dy.abs_mul, ~Y.Dy.abs_neg, ~{==}, ~D.Dy.ulp(1n+p1), ~R.Round.eps_pos(1n+p1),
    ~RD.Dy.nadd(1n+p1), ~RD.Dy.nmul(1n+p1), ~R.Rne.add_ok(p1), ~R.Rne.mul_ok(p1), a, b)

# eps |z| - |rne z - z| >= 0, eps = 2^-k
def near_within(+p1: Nat, +k: Nat, +z: D.Dy) -> Bool:
  D.Dy.pos(D.Dy.add(D.Dy.mul(D.Dy.ulp(k), D.Dy.abs(z)), D.Dy.neg(D.Dy.abs(D.Dy.add(RD.Dy.rne(1n+p1, z), D.Dy.neg(z))))))

# eps |z| - |trunc z - z| >= 0
def within(+p1: Nat, +z: D.Dy) -> Bool:
  D.Dy.pos(D.Dy.add(D.Dy.mul(D.Dy.ulp(p1), D.Dy.abs(z)), D.Dy.neg(D.Dy.abs(D.Dy.add(RD.Dy.trunc(1n+p1, z), D.Dy.neg(z))))))

# the same with eps halved
def within_half(+p1: Nat, +z: D.Dy) -> Bool:
  D.Dy.pos(D.Dy.add(D.Dy.mul(D.Dy.ulp(1n+p1), D.Dy.abs(z)), D.Dy.neg(D.Dy.abs(D.Dy.add(RD.Dy.trunc(1n+p1, z), D.Dy.neg(z))))))

def main() -> IO(Unit):
  +z = D.Dy.of(0n, I.IPos{11n})
  do IO<Unit>:
    IO.print("trunc to 2 bits: " ++ D.Dy.show(RD.Dy.trunc(2n, z)))
    IO.print("within 2^-1 |z|: " ++ Bool.show(within(1n, z)))
    IO.print("within 2^-2 |z|: " ++ Bool.show(within_half(1n, z)))
    IO.print("5 to nearest at 2 bits: " ++ D.Dy.show(RD.Dy.rne(2n, D.Dy.of(0n, I.IPos{5n}))))
    IO.print("within 2^-2 |z|: " ++ Bool.show(near_within(1n, 2n, D.Dy.of(0n, I.IPos{5n}))))
    IO.print("within 2^-3 |z|: " ++ Bool.show(near_within(1n, 3n, D.Dy.of(0n, I.IPos{5n}))))
#|trunc to 2 bits: 8/2^0
#|within 2^-1 |z|: True
#|within 2^-2 |z|: False
#|5 to nearest at 2 bits: 4/2^0
#|within 2^-2 |z|: True
#|within 2^-3 |z|: False
