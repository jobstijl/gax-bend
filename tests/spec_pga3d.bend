# Layer S on PGA3D (e0 squares to 0, e1 e2 e3 to +1) over exact integers:
# basis products, signs, the gax join convention e123 v e032 = +e23 and the
# complements J_R(e123) = -e0, J_R(e032) = -e1 (gax ADR-009).
import Base
import ../src/spec.bend as S
import ../src/int.bend as I
import ../src/show.bend as Sh

def Sg() -> S.Sig(4n):
  S.Gen{S.QZ{}, S.Gen{S.QP{}, S.Gen{S.QP{}, S.Gen{S.QP{}, S.SigEnd{}}}}}

def e(i: Nat) -> S.MV(I.Int, 4n):
  S.MV.gen(I.Int, 4n, i, I.Int.one())

def gp(x: S.MV(I.Int, 4n), y: S.MV(I.Int, 4n)) -> S.MV(I.Int, 4n):
  S.MV.gp(~I.Int, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, 4n, Sg(), x, y)

def wedge(x: S.MV(I.Int, 4n), y: S.MV(I.Int, 4n)) -> S.MV(I.Int, 4n):
  S.MV.wedge(~I.Int, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, 4n, x, y)

def vee(x: S.MV(I.Int, 4n), y: S.MV(I.Int, 4n)) -> S.MV(I.Int, 4n):
  S.MV.vee(~I.Int, ~I.Int.add, ~I.Int.mul, ~I.Int.neg, 4n, x, y)

def add(x: S.MV(I.Int, 4n), y: S.MV(I.Int, 4n)) -> S.MV(I.Int, 4n):
  S.MV.add(~I.Int, ~I.Int.add, 4n, x, y)

def show(x: S.MV(I.Int, 4n)) -> String:
  Sh.Show.mv(~I.Int, ~I.Int.show, 4n, 0n, x)

def e123() -> S.MV(I.Int, 4n):
  gp(gp(e(1n), e(2n)), e(3n))

def e032() -> S.MV(I.Int, 4n):
  gp(gp(e(0n), e(3n)), e(2n))

def main() -> List<&2, String>:
  [ show(gp(e(1n), e(1n))),
    show(gp(e(0n), e(0n))),
    show(gp(e(1n), e(2n))),
    show(gp(e(2n), e(1n))),
    show(e032()),
    show(vee(e123(), e032())),
    show(S.MV.rcomp(~I.Int, ~I.Int.neg, 4n, e123())),
    show(S.MV.rcomp(~I.Int, ~I.Int.neg, 4n, e032())),
    show(S.MV.lcomp(~I.Int, ~I.Int.neg, 4n, S.MV.rcomp(~I.Int, ~I.Int.neg, 4n, e032()))),
    show(S.MV.reverse(~I.Int, ~I.Int.neg, 4n, e123())),
    show(S.MV.involute(~I.Int, ~I.Int.neg, 4n, e123())),
    show(S.MV.conjugate(~I.Int, ~I.Int.neg, 4n, gp(e(1n), e(2n)))),
    show(wedge(e(1n), e(2n))),
    show(wedge(e(1n), e(1n))),
    show(S.MV.grade(I.Int, 4n, 2n, add(e(1n), gp(e(0n), e(1n))))),
    show(gp(add(e(0n), e(1n)), add(e(0n), e(1n)))) ]
#|["1*1", "0", "1*e12", "-1*e12", "-1*e023", "1*e23", "-1*e0", "-1*e1", "-1*e023", "-1*e123", "-1*e123", "-1*e12", "1*e12", "0", "1*e01", "0*e01 + 1*1"]
