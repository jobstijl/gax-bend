# Writes proofs/inv.bend: the grade involution is an automorphism of the
# geometric product, through a lemma that carries the sign flags.

import Base
import ./dsl.bend as D

def I.flags() -> List<&2, D.Fl>:
  [ D.Fl{"iv_t", ["k"], D.xor("k", D.Tr()), D.bnot("k")},
    D.Fl{"iv_tt", ["k"], D.xor(D.xor("k", D.Tr()), D.Tr()), "k"},
    D.Fl{"iv_f", ["f"], D.xor("f", D.F()), "f"},
    D.Fl{"iv_c", ["m", "n"], D.xor("m", "n"), D.xor("n", "m")} ]

def I.gcong(+d: String, +f: String, +n: String, +x: String, +x2: String, +y: String, +y2: String, +s: String, +ex: String, +ey: String) -> String:
  D.cat(["P.Gp.cong(", D.OPS(), ", ", d, ", ", f, ", ", n, ", ", x, ", ", x2, ", ", y, ", ", y2, ", ", s, ",\n  ", D.ind(ex, 2n), ",\n  ", D.ind(ey, 2n), ")"])

def I.swap() -> String:
  +mv = D.mv("d")
  +u = D.sgn("d", D.F(), D.Tr(), D.F(), "u")
  +kv = D.sgn("d", "k", D.Tr(), D.F(), "v")
  +nf = D.gpf("d", "f", D.xor("n", D.Tr()), u, kv, "sig")
  +ly = D.sgn("d", D.xor("k", D.Tr()), D.Tr(), D.F(), "v")
  +ly2 = D.sgn("d", D.Tr(), D.F(), D.F(), kv)
  +ey_l = D.trans(mv, ly, D.sgn("d", D.bnot("k"), D.Tr(), D.F(), "v"), ly2,
    D.cat(["G.Sgn.flag(~T, ~neg, d, ", D.xor("k", D.Tr()), ", ", D.bnot("k"), ", ", D.Tr(), ", ", D.Tr(), ", ", D.F(), ", v, ", D.flag.call("iv_t", ["k"]), ", {==})"]),
    D.sym(mv, ly2, D.sgn("d", D.bnot("k"), D.Tr(), D.F(), "v"), D.cat(["G.Sgn.compose(~T, ~neg, ~neg_neg, d, ", D.Tr(), ", ", D.F(), ", ", D.F(), ", k, ", D.Tr(), ", ", D.F(), ", v)"])))
  +lhs = D.gpf("d", "f", "n", u, ly, "sig")
  +lhs_nf = D.trans(mv, lhs, D.gpf("d", "f", "n", u, ly2, "sig"), nf,
    I.gcong("d", "f", "n", u, u, ly, ly2, "sig", "{==}", ey_l),
    D.cat(["P.Gp.sgn_r(", D.OPS(), ", ~neg_mul_r, ~neg_neg, d, f, n, ", u, ", ", D.Tr(), ", ", kv, ", sig)"]))
  +rx = D.sgn("d", D.Tr(), D.Tr(), D.F(), "u")
  +rx2 = D.sgn("d", D.Tr(), D.F(), D.F(), u)
  +rhs = D.gpf("d", "f", "n", rx, kv, "sig")
  +rhs_nf = D.trans(mv, rhs, D.gpf("d", "f", "n", rx2, kv, "sig"), nf,
    I.gcong("d", "f", "n", rx, rx2, kv, kv, "sig",
      D.sym(mv, rx2, rx, D.cat(["G.Sgn.compose(~T, ~neg, ~neg_neg, d, ", D.Tr(), ", ", D.F(), ", ", D.F(), ", ", D.F(), ", ", D.Tr(), ", ", D.F(), ", u)"])), "{==}"),
    D.trans(mv, D.gpf("d", "f", "n", rx2, kv, "sig"), D.gpf("d", D.xor("f", D.F()), D.xor("n", D.Tr()), u, kv, "sig"), nf,
      D.cat(["P.Gp.sgn_l(", D.OPS(), ", ~neg_mul_l, ~neg_neg, d, f, n, ", D.Tr(), ", ", D.F(), ", ", u, ", ", kv, ", sig)"]),
      D.gflag("P.", "d", D.xor("f", D.F()), "f", D.xor("n", D.Tr()), D.xor("n", D.Tr()), u, kv, "sig", D.flag.call("iv_f", ["f"]), "{==}")))
  D.cat(["# The grade involution is an automorphism
# ---------------------------------------

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S
import ./base.bend as B
import ./leaf.bend as L
import ./add.bend as A
import ./flags.bend as F
import ./sgn.bend as G
import ./gp.bend as P

# a negation may move between an involuted left operand and a signed,
# involuted right operand
def Inv.swap(", D.OPSD(), ", ~neg_mul_l: R.Ring.NegMulL(T, mul, neg), ~neg_mul_r: R.Ring.NegMulR(T, mul, neg),
  ~neg_neg: R.Ring.NegNeg(T, neg), +d: Nat, +f: Bool, +n: Bool, +u: ", mv, ", +k: Bool, +v: ", mv, ", +sig: S.Sig(d))
  -> {", lhs, " == ", rhs, " : ", mv, "}:
  B.Eq.join(", mv, ", ", lhs, ", ", rhs, ", ", nf, ",
    ", D.ind(lhs_nf, 4n), ",
    ", D.ind(rhs_nf, 4n), ")
"])

def I.h() -> String:
  D.OPS() ++ ", ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r"

def I.hsw() -> String:
  D.OPS() ++ ", ~neg_mul_l, ~neg_mul_r, ~neg_neg"

type It is Data:
  It{f: String, n: String, x: String, y: String}

def I.g(t: It) -> String:
  match t:
    case It{f, n, x, y}:
      D.gpf("p", f, n, x, y, "rest")

def I.ih(+k: String, t: It) -> String:
  match t:
    case It{f, n, x, y}:
      D.cat(["Inv.gp(", I.h(), ", p, ", k, ", ", f, ", ", n, ", ", x, ", ", y, ", rest)"])

def I.ihform(+k: String, t: It) -> String:
  match t:
    case It{f, n, x, y}:
      D.gpf("p", f, n, D.sgn("p", D.F(), D.Tr(), D.F(), x), D.sgn("p", k, D.Tr(), D.F(), y), "rest")

def I.level(+q: D.Qc) -> String:
  +isz = D.isz(q)
  +mv = D.mv("p")
  +nf = D.xor("n", "f")
  +nf3 = D.byq(q, nf, nf, D.bnot(nf))
  +mt = D.xor("m", D.Tr())
  +t1 = {It{"f", nf, "x1", "y2"} : It}
  +t2 = {It{D.bnot("f"), "n", "x2", "y1"} : It}
  +t3 = {It{D.bnot("f"), nf3, "x1", "y1"} : It}
  +t4 = {It{"f", "n", "x2", "y2"} : It}
  +e0 = D.add("p", I.g(t1), I.g(t2))
  +r0 = D.pick(isz, I.g(t4), D.add("p", I.g(t3), I.g(t4)))
  +le1 = I.ihform(mt, t1)
  +le2 = I.ihform(mt, t2)
  +le3 = I.ihform("m", t3)
  +le4 = I.ihform("m", t4)
  +ee = D.trans(mv, D.sgn("p", mt, D.Tr(), D.F(), e0), D.add("p", D.sgn("p", mt, D.Tr(), D.F(), I.g(t1)), D.sgn("p", mt, D.Tr(), D.F(), I.g(t2))), D.add("p", le1, le2),
    D.cat(["G.Sgn.add(~T, ~add, ~neg, ~neg_add, p, ", mt, ", ", D.Tr(), ", ", D.F(), ", ", I.g(t1), ", ", I.g(t2), ")"]),
    D.cat(["A.Add.cong(~T, ~add, p, ", D.sgn("p", mt, D.Tr(), D.F(), I.g(t1)), ", ", le1, ", ", D.sgn("p", mt, D.Tr(), D.F(), I.g(t2)), ", ", le2, ", ", I.ih(mt, t1), ", ", I.ih(mt, t2), ")"]))
  +rl = D.pick(isz, le4, D.add("p", le3, le4))
  +er = D.pick(isz, I.ih("m", t4),
    D.trans(mv, D.sgn("p", "m", D.Tr(), D.F(), r0), D.add("p", D.sgn("p", "m", D.Tr(), D.F(), I.g(t3)), D.sgn("p", "m", D.Tr(), D.F(), I.g(t4))), rl,
      D.cat(["G.Sgn.add(~T, ~add, ~neg, ~neg_add, p, m, ", D.Tr(), ", ", D.F(), ", ", I.g(t3), ", ", I.g(t4), ")"]),
      D.cat(["A.Add.cong(~T, ~add, p, ", D.sgn("p", "m", D.Tr(), D.F(), I.g(t3)), ", ", le3, ", ", D.sgn("p", "m", D.Tr(), D.F(), I.g(t4)), ", ", le4, ", ", I.ih("m", t3), ", ", I.ih("m", t4), ")"])))
  +lhs = D.sgn("1n+p", "m", D.Tr(), D.F(), D.mk("p", e0, r0))
  +m1 = D.mk("p", D.sgn("p", mt, D.Tr(), D.F(), e0), D.sgn("p", "m", D.Tr(), D.F(), r0))
  +m2 = D.mk("p", D.add("p", le1, le2), rl)
  +re1 = D.gpf("p", "f", nf, D.sgn("p", D.Tr(), D.Tr(), D.F(), "x1"), D.sgn("p", "m", D.Tr(), D.F(), "y2"), "rest")
  +e_r = D.add("p", re1, le2)
  +ee2 = D.cat(["A.Add.cong(~T, ~add, p, ", le1, ", ", re1, ", ", le2, ", ", le2, ", ", D.cat(["Inv.swap(", I.hsw(), ", p, f, ", nf, ", x1, m, y2, rest)"]), ", {==})"])
  +re3 = D.gpf("p", D.bnot("f"), nf3, D.sgn("p", D.Tr(), D.Tr(), D.F(), "x1"), D.sgn("p", mt, D.Tr(), D.F(), "y1"), "rest")
  +ix1 = D.sgn("p", D.F(), D.Tr(), D.F(), "x1")
  +mid3 = D.gpf("p", D.bnot("f"), nf3, ix1, D.sgn("p", D.xor(mt, D.Tr()), D.Tr(), D.F(), "y1"), "rest")
  +e3 = D.trans(mv, le3, mid3, re3,
    I.gcong("p", D.bnot("f"), nf3, ix1, ix1, D.sgn("p", "m", D.Tr(), D.F(), "y1"), D.sgn("p", D.xor(mt, D.Tr()), D.Tr(), D.F(), "y1"), "rest", "{==}",
      D.cat(["G.Sgn.flag(~T, ~neg, p, m, ", D.xor(mt, D.Tr()), ", ", D.Tr(), ", ", D.Tr(), ", ", D.F(), ", y1, ", D.sym("Bool", D.xor(mt, D.Tr()), "m", D.flag.call("iv_tt", ["m"])), ", {==})"])),
    D.cat(["Inv.swap(", I.hsw(), ", p, ", D.bnot("f"), ", ", nf3, ", x1, ", mt, ", y1, rest)"]))
  +r_r = D.pick(isz, le4, D.add("p", re3, le4))
  +er2 = D.pick(isz, "{==}", D.cat(["A.Add.cong(~T, ~add, p, ", le3, ", ", re3, ", ", le4, ", ", le4, ", ", e3, ", {==})"]))
  +m3 = D.mk("p", e_r, r_r)
  +s1 = D.cat(["G.Sgn.mk(~T, ~neg, p, m, ", D.Tr(), ", ", D.F(), ", ", e0, ", ", r0, ")"])
  +s2 = D.cat(["P.Mk.cong(T, p, ", D.sgn("p", mt, D.Tr(), D.F(), e0), ", ", D.add("p", le1, le2), ", ", D.sgn("p", "m", D.Tr(), D.F(), r0), ", ", rl, ",\n  ", D.ind(ee, 2n), ",\n  ", D.ind(er, 2n), ")"])
  +s3 = D.cat(["P.Mk.cong(T, p, ", D.add("p", le1, le2), ", ", e_r, ", ", rl, ", ", r_r, ",\n  ", D.ind(ee2, 2n), ",\n  ", D.ind(er2, 2n), ")"])
  D.trans(D.mv("1n+p"), lhs, m2, m3, D.trans(D.mv("1n+p"), lhs, m1, m2, s1, s2), s3)

def I.gp() -> String:
  +mvd = D.mv("d")
  D.cat(["# a grade sign with the involution set, applied to a product, moves onto the
# operands: (-1)^m inv(inv^f(x) y) = inv^f(inv x) ((-1)^m inv y)
def Inv.gp(", D.OPSD(), ", ~neg_add: R.Ring.NegAdd(T, add, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  ~neg_mul_l: R.Ring.NegMulL(T, mul, neg), ~neg_mul_r: R.Ring.NegMulR(T, mul, neg),
  +d: Nat, +m: Bool, +f: Bool, +n: Bool, x: ", mvd, ", y: ", mvd, ", +sig: S.Sig(d))
  -> {", D.sgn("d", "m", D.Tr(), D.F(), D.gpf("d", "f", "n", "x", "y", "sig")), " == ", D.gpf("d", "f", "n", D.sgn("d", D.F(), D.Tr(), D.F(), "x"), D.sgn("d", "m", D.Tr(), D.F(), "y"), "sig"), " : ", mvd, "}:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          {==}
        case S.L{+a}:
          match y:
            case S.LZ{}:
              {==}
            case S.L{+b}:
              B.Leaf.cong(T, S.Ring.negf(~T, ~neg, m, S.Ring.negf(~T, ~neg, n, mul(a, b))), S.Ring.negf(~T, ~neg, n, mul(a, S.Ring.negf(~T, ~neg, m, b))),
                B.Eq.join(T, S.Ring.negf(~T, ~neg, m, S.Ring.negf(~T, ~neg, n, mul(a, b))), S.Ring.negf(~T, ~neg, n, mul(a, S.Ring.negf(~T, ~neg, m, b))),
                  S.Ring.negf(~T, ~neg, ", D.xor("n", "m"), ", mul(a, b)),
                  Equal.trans(T, S.Ring.negf(~T, ~neg, m, S.Ring.negf(~T, ~neg, n, mul(a, b))), S.Ring.negf(~T, ~neg, ", D.xor("m", "n"), ", mul(a, b)),
                    S.Ring.negf(~T, ~neg, ", D.xor("n", "m"), ", mul(a, b)),
                    L.Negf.negf(~T, ~neg, ~neg_neg, m, n, mul(a, b)),
                    L.Negf.flag(~T, ~neg, ", D.xor("m", "n"), ", ", D.xor("n", "m"), ", mul(a, b), ", D.flag.call("iv_c", ["m", "n"]), ")),
                  Equal.trans(T, S.Ring.negf(~T, ~neg, n, mul(a, S.Ring.negf(~T, ~neg, m, b))), S.Ring.negf(~T, ~neg, n, S.Ring.negf(~T, ~neg, m, mul(a, b))),
                    S.Ring.negf(~T, ~neg, ", D.xor("n", "m"), ", mul(a, b)),
                    Equal.cong(T, T, w => S.Ring.negf(~T, ~neg, n, w), mul(a, S.Ring.negf(~T, ~neg, m, b)), S.Ring.negf(~T, ~neg, m, mul(a, b)),
                      L.Negf.mul_r(~T, ~mul, ~neg, ~neg_mul_r, m, a, b)),
                    L.Negf.negf(~T, ~neg, ~neg_neg, n, m, mul(a, b)))))
    case 1n+p:
      match x:
        case S.NZ{}:
          {==}
        case S.N{+x1, +x2}:
          match y:
            case S.NZ{}:
              {==}
            case S.N{+y1, +y2}:
", D.qcases(I.level(D.CZ{}), I.level(D.CP{}), I.level(D.CN{}), 14n), "
"])

def I.text() -> String:
  D.sep([I.swap(), I.gp()], "\n")
