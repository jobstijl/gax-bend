# Dual numbers are a commutative ring (proofs/dual.bend), so the generic
# normaliser runs at T = Dual<Int>, and every kernel runs on them. Running
# PGA3D's Motor.transform.Point with eps on one point coordinate gives one
# column of the motor's 4x4 action matrix; the matrix applied to a point
# equals the kernel on it.
import Base
import ../src/int.bend as I
import ../src/dual.bend as DU
import ../src/norm.bend as N
import ../proofs/norm.bend as NP
import ../proofs/int.bend as Z
import ../proofs/dual.bend as Q
import ../api/pga3d.bend as P
import ../algebras/pga3d/kinds.bend as K
import ../algebras/pga3d/ops.bend as O
import ../algebras/pga3d/f32.bend as G

# (x + y)(x - y) = x x - y y for all dual integers
def diff_sq(x: DU.Dual<I.Int>, y: DU.Dual<I.Int>)
  -> {DU.Dual.mul(~I.Int, ~I.Int.add, ~I.Int.mul, DU.Dual.add(~I.Int, ~I.Int.add, x, y), DU.Dual.add(~I.Int, ~I.Int.add, x, DU.Dual.neg(~I.Int, ~I.Int.neg, y)))
      == DU.Dual.add(~I.Int, ~I.Int.add, DU.Dual.mul(~I.Int, ~I.Int.add, ~I.Int.mul, x, x), DU.Dual.neg(~I.Int, ~I.Int.neg, DU.Dual.mul(~I.Int, ~I.Int.add, ~I.Int.mul, y, y))) : DU.Dual<I.Int>}:
  NP.Norm.eq(~DU.Dual<I.Int>, ~DU.Dual.zero(~I.Int, ~I.IPos{0n}), ~DU.Dual.one(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}), ~DU.Dual.add(~I.Int, ~I.Int.add), ~DU.Dual.mul(~I.Int, ~I.Int.add, ~I.Int.mul), ~DU.Dual.neg(~I.Int, ~I.Int.neg),
    ~Q.Dual.r.add_assoc(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg),
    ~Q.Dual.r.add_comm(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg),
    ~Q.Dual.r.zero_l(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg),
    ~Q.Dual.r.add_inv(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg),
    ~Q.Dual.r.mul_assoc(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg),
    ~Q.Dual.r.mul_comm(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg),
    ~Q.Dual.r.unit_r(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg),
    ~Q.Dual.r.dist_l(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg),
    ~Q.Dual.r.neg_add(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg),
    ~Q.Dual.r.neg_mul_l(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg),
    ~Q.Dual.r.neg_neg(~I.Int, ~I.IPos{0n}, ~I.IPos{1n}, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, ~Z.Int.r.add_assoc, ~Z.Int.r.add_comm, ~Z.Int.r.zero_l, ~Z.Int.r.add_inv, ~Z.Int.r.mul_assoc, ~Z.Int.r.mul_comm, ~Z.Int.r.unit_r, ~Z.Int.r.dist_l, ~Z.Int.r.neg_add, ~Z.Int.r.neg_mul_l, ~Z.Int.r.neg_neg),
    [x, y], N.TMul{N.TAdd{N.TVar{0n}, N.TVar{1n}}, N.TAdd{N.TVar{0n}, N.TNeg{N.TVar{1n}}}},
    N.TAdd{N.TMul{N.TVar{0n}, N.TVar{0n}}, N.TNeg{N.TMul{N.TVar{1n}, N.TVar{1n}}}}, {==})

# the motor's action at dual F32: column j has eps on coordinate j
def c(x: F32) -> DU.Dual<F32>:
  DU.Dual{x, 0.0}

def e(x: F32) -> DU.Dual<F32>:
  DU.Dual{x, 1.0}

def act(+m: K.Motor<F32>, p: K.Point<DU.Dual<F32>>) -> K.Point<F32>:
  K.Point.map(~DU.Dual<F32>, ~F32, ~(w => DU.Dual.d(F32, w)),
    O.Motor.transform.Point(~DU.Dual<F32>, ~DU.Dual{0.0, 0.0}, ~DU.Dual.add(~F32, ~F32.add), ~DU.Dual.mul(~F32, ~F32.add, ~F32.mul), ~DU.Dual.neg(~F32, ~F32.neg),
      K.Motor.map(~F32, ~DU.Dual<F32>, ~c, m), p))

def axpy(+a: F32, x: K.Point<F32>, y: K.Point<F32>) -> K.Point<F32>:
  match x y:
    case K.Point{x0, x1, x2, x3} K.Point{y0, y1, y2, y3}:
      K.Point{(a * x0 + y0 : F32), (a * x1 + y1 : F32), (a * x2 + y2 : F32), (a * x3 + y3 : F32)}

def close(a: K.Point<F32>, b: K.Point<F32>) -> Bool:
  match a b:
    case K.Point{a0, a1, a2, a3} K.Point{b0, b1, b2, b3}:
      Bool.and(Bool.and(F32.is_lt(F32.abs((a0 - b0 : F32)), 1.0e-4), F32.is_lt(F32.abs((a1 - b1 : F32)), 1.0e-4)),
        Bool.and(F32.is_lt(F32.abs((a2 - b2 : F32)), 1.0e-4), F32.is_lt(F32.abs((a3 - b3 : F32)), 1.0e-4)))

def main() -> IO(Unit):
  +m = P.Motor.of(K.Motor<F32>, P.Motor.then(P.Motor.rotation(K.Line{0.3, 0.5, 0.8, 0.1, F32.neg(0.2), 0.05}, 1.1), P.Motor.translation(1.0, F32.neg(2.0), 0.5)))
  +c0 = act(m, K.Point{e(0.0), c(0.0), c(0.0), c(0.0)})
  +c1 = act(m, K.Point{c(0.0), e(0.0), c(0.0), c(0.0)})
  +c2 = act(m, K.Point{c(0.0), c(0.0), e(0.0), c(0.0)})
  +c3 = act(m, K.Point{c(0.0), c(0.0), c(0.0), e(0.0)})
  +p = P.Point.xyz(1.0, 2.0, 3.0)
  +mp = axpy(1.0, c0, axpy(2.0, c1, axpy(3.0, c2, axpy(1.0, c3, K.Point{0.0, 0.0, 0.0, 0.0}))))
  do IO<Unit>:
    IO.print("matrix times point = kernel on point: " ++ Bool.show(close(mp, G.Motor.transform.Point(m, p))))
#|matrix times point = kernel on point: True
