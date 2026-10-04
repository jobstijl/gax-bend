# Writes proofs/gp_assoc.bend: associativity of the geometric product, by
# induction on the dimension over every flag. At a level both sides expand
# (through MV.mk transparency, distributivity and the sign pull) into the
# same terms up to xor identities of the flags and a rotation of four sums.

import Base
import ./dsl.bend as D

def A.h() -> String:
  D.OPS() ++ ", ~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r"

def A.g(+f: String, +n: String, +x: String, +y: String) -> String:
  D.gpf("p", f, n, x, y, "rest")

def A.ih(+fa: String, +na: String, +fb: String, +nb: String, +x: String, +y: String, +z: String) -> String:
  D.cat(["Gp.assoc(", A.h(), ", p, ", fa, ", ", na, ", ", fb, ", ", nb, ", ", x, ", ", y, ", ", z, ", rest)"])

def A.addl(+f: String, +n: String, +a: String, +b: String, +z: String) -> String:
  D.cat(["P.Gp.add_l(", D.OPS(), ", ~add_assoc, ~add_comm, ~dist_r, ~neg_add, p, ", f, ", ", n, ", ", a, ", ", b, ", ", z, ", rest)"])

def A.addr(+f: String, +n: String, +x: String, +a: String, +b: String) -> String:
  D.cat(["P.Gp.add_r(", D.OPS(), ", ~add_assoc, ~add_comm, ~dist_l, ~neg_add, p, ", f, ", ", n, ", ", x, ", ", a, ", ", b, ", rest)"])

def A.pull(+f: String, +n: String, +x: String, +gg: String, +mm: String, +y: String, +z: String) -> String:
  D.cat(["P.Gp.pull(", D.OPS(), ", ~neg_add, ~neg_neg, ~neg_mul_r, p, ", f, ", ", n, ", ", x, ", ", gg, ", ", mm, ", ", y, ", ", z, ", rest)"])

def A.acong(+a: String, +a2: String, +b: String, +b2: String, +ea: String, +eb: String) -> String:
  D.cat(["A.Add.cong(~T, ~add, p, ", a, ", ", a2, ", ", b, ", ", b2, ",\n  ", D.ind(ea, 2n), ",\n  ", D.ind(eb, 2n), ")"])

def A.mcong(+e: String, +e2: String, +r: String, +r2: String, +ee: String, +er: String) -> String:
  D.cat(["P.Mk.cong(T, p, ", e, ", ", e2, ", ", r, ", ", r2, ",\n  ", D.ind(ee, 2n), ",\n  ", D.ind(er, 2n), ")"])

def A.fl(+fa: String, +fb: String, +na: String, +nb: String, +x: String, +inner: String, +ef: String, +en: String) -> String:
  D.gflag("P.", "p", fa, fb, na, nb, x, inner, "rest", ef, en)

def A.flags() -> List<&2, D.Fl>:
  [ D.Fl{"as_t1n", ["a", "b", "c", "d"], D.xor(D.xor("a", "b"), D.xor("c", "d")), D.xor(D.xor("a", "c"), D.xor("b", "d"))},
    D.Fl{"as_fxn", ["a", "b"], D.xor("a", D.bnot("b")), D.bnot(D.xor("a", "b"))},
    D.Fl{"as_fnx", ["a", "b"], D.xor(D.bnot("a"), "b"), D.bnot(D.xor("a", "b"))},
    D.Fl{"as_fnn", ["a", "b"], D.xor(D.bnot("a"), D.bnot("b")), D.xor("a", "b")},
    D.Fl{"as_t2n", ["n1", "f1", "n2"], D.xor(D.xor("n1", "f1"), "n2"), D.xor(D.xor("n1", "n2"), "f1")},
    D.Fl{"as_t3p", ["n1", "n2", "f1", "f2"], D.xor("n1", D.xor("n2", "f2")), D.xor(D.xor(D.xor("n1", "n2"), D.xor("f1", "f2")), "f1")},
    D.Fl{"as_t3n", ["n1", "n2", "f1", "f2"], D.xor("n1", D.bnot(D.xor("n2", "f2"))), D.xor(D.xor(D.xor("n1", "n2"), D.xor("f1", "f2")), D.bnot("f1"))},
    D.Fl{"as_u1n", ["n1", "f1", "n2", "f2"], D.xor(D.bnot(D.xor("n1", "f1")), D.xor("n2", "f2")), D.bnot(D.xor(D.xor("n1", "n2"), D.xor("f1", "f2")))},
    D.Fl{"as_u2n", ["n1", "f1", "n2"], D.xor(D.bnot(D.xor("n1", "f1")), "n2"), D.xor(D.xor("n1", "n2"), D.bnot("f1"))},
    D.Fl{"as_u3n", ["n1", "n2", "f1", "f2"], D.xor("n1", D.bnot(D.xor("n2", "f2"))), D.xor(D.bnot(D.xor(D.xor("n1", "n2"), D.xor("f1", "f2"))), "f1")} ]

def A.call(+n: String, +args: List<&2, String>) -> String:
  D.flag.call(n, args)

# the terms of a level, left and right of the equation
type Tms is Data:
  Tms{t1: String, t2: String, t3: String, t4: String, u1: String, u2: String, u3: String, u4: String,
    t1r: String, t2r: String, t3r: String, t4r: String, u1r: String, u2r: String, u3r: String, u4r: String}

def A.level.go(+q: D.Qc, +isz: Bool, +mv: String, +mv1: String, +g: String, +m: String, +n1f1: String, +n2f2: String,
  +n2f2b: String, +n1f1b: String, +c1n: String, +mg: String, +mgb: String, +a1: String, +a2: String, +b1: String, +b2: String,
  +w1: String, +w2: String, +c1: String, +c2: String, +d1: String, +d2: String, +v1: String, +v2: String,
  +i22: String, +i12: String, +i11: String, +i21: String, tm: Tms) -> String:
  match tm:
    case Tms{+t1, +t2, +t3, +t4, +u1, +u2, +u3, +u4, +t1r, +t2r, +t3r, +t4r, +u1r, +u2r, +u3r, +u4r}:
      +nf1 = D.bnot("f1")
      +ng = D.bnot(g)
      +et1 = A.fl(D.xor("f1", "f2"), g, D.xor(n1f1, n2f2), mg, "x1", i22, "{==}", A.call("as_t1n", ["n1", "f1", "n2", "f2"]))
      +et2 = A.fl(D.xor("f1", D.bnot("f2")), ng, D.xor(n1f1, "n2"), D.xor(m, "f1"), "x2", i12, A.call("as_fxn", ["f1", "f2"]), A.call("as_t2n", ["n1", "f1", "n2"]))
      +et3 = A.fl(D.xor(nf1, D.bnot("f2")), g, D.xor("n1", n2f2b), D.xor(mg, c1n), "x1", i11, A.call("as_fnn", ["f1", "f2"]),
        D.byq(q, A.call("as_t3p", ["n1", "n2", "f1", "f2"]), A.call("as_t3p", ["n1", "n2", "f1", "f2"]), A.call("as_t3n", ["n1", "n2", "f1", "f2"])))
      +et4 = A.fl(D.xor(nf1, "f2"), ng, m, m, "x2", i21, A.call("as_fnx", ["f1", "f2"]), "{==}")
      +eu1 = A.fl(D.xor(nf1, "f2"), ng, D.xor(n1f1b, n2f2), mgb, "x1", i21, A.call("as_fnx", ["f1", "f2"]),
        D.byq(q, A.call("as_t1n", ["n1", "f1", "n2", "f2"]), A.call("as_t1n", ["n1", "f1", "n2", "f2"]), A.call("as_u1n", ["n1", "f1", "n2", "f2"])))
      +eu2 = A.fl(D.xor(nf1, D.bnot("f2")), g, D.xor(n1f1b, "n2"), D.xor(m, c1n), "x2", i11, A.call("as_fnn", ["f1", "f2"]),
        D.byq(q, A.call("as_t2n", ["n1", "f1", "n2"]), A.call("as_t2n", ["n1", "f1", "n2"]), A.call("as_u2n", ["n1", "f1", "n2"])))
      +eu3 = A.fl(D.xor("f1", D.bnot("f2")), ng, D.xor("n1", n2f2b), D.xor(mgb, "f1"), "x1", i12, A.call("as_fxn", ["f1", "f2"]),
        D.byq(q, A.call("as_t3p", ["n1", "n2", "f1", "f2"]), A.call("as_t3p", ["n1", "n2", "f1", "f2"]), A.call("as_u3n", ["n1", "n2", "f1", "f2"])))
      +el = D.add("p", A.g("f1", n1f1, w1, "z2"), A.g(nf1, "n1", w2, "z1"))
      +rl = D.pick(isz, A.g("f1", "n1", w2, "z2"), D.add("p", A.g(nf1, n1f1b, w1, "z1"), A.g("f1", "n1", w2, "z2")))
      +e_first = D.trans(mv, A.g("f1", n1f1, w1, "z2"), D.add("p", A.g("f1", n1f1, a1, "z2"), A.g("f1", n1f1, a2, "z2")), D.add("p", t1, t2),
        A.addl("f1", n1f1, a1, a2, "z2"),
        A.acong(A.g("f1", n1f1, a1, "z2"), t1, A.g("f1", n1f1, a2, "z2"), t2,
          A.ih("f1", n1f1, "f2", n2f2, "x1", "y2", "z2"), A.ih("f1", n1f1, D.bnot("f2"), "n2", "x2", "y1", "z2")))
      +e_second = D.pick(isz, A.ih(nf1, "n1", "f2", "n2", "x2", "y2", "z1"),
        D.trans(mv, A.g(nf1, "n1", w2, "z1"), D.add("p", A.g(nf1, "n1", b1, "z1"), A.g(nf1, "n1", b2, "z1")), D.add("p", t3, t4),
          A.addl(nf1, "n1", b1, b2, "z1"),
          A.acong(A.g(nf1, "n1", b1, "z1"), t3, A.g(nf1, "n1", b2, "z1"), t4,
            A.ih(nf1, "n1", D.bnot("f2"), n2f2b, "x1", "y1", "z1"), A.ih(nf1, "n1", "f2", "n2", "x2", "y2", "z1"))))
      +t34 = D.pick(isz, t4, D.add("p", t3, t4))
      +el4 = D.add("p", D.add("p", t1, t2), t34)
      +eel = A.acong(A.g("f1", n1f1, w1, "z2"), D.add("p", t1, t2), A.g(nf1, "n1", w2, "z1"), t34, e_first, e_second)
      +r_first = D.trans(mv, A.g(nf1, n1f1b, w1, "z1"), D.add("p", A.g(nf1, n1f1b, a1, "z1"), A.g(nf1, n1f1b, a2, "z1")), D.add("p", u1, u2),
        A.addl(nf1, n1f1b, a1, a2, "z1"),
        A.acong(A.g(nf1, n1f1b, a1, "z1"), u1, A.g(nf1, n1f1b, a2, "z1"), u2,
          A.ih(nf1, n1f1b, "f2", n2f2, "x1", "y2", "z1"), A.ih(nf1, n1f1b, D.bnot("f2"), "n2", "x2", "y1", "z1")))
      +r_second = D.trans(mv, A.g("f1", "n1", w2, "z2"), D.add("p", A.g("f1", "n1", b1, "z2"), A.g("f1", "n1", b2, "z2")), D.add("p", u3, u4),
        A.addl("f1", "n1", b1, b2, "z2"),
        A.acong(A.g("f1", "n1", b1, "z2"), u3, A.g("f1", "n1", b2, "z2"), u4,
          A.ih("f1", "n1", D.bnot("f2"), n2f2b, "x1", "y1", "z2"), A.ih("f1", "n1", "f2", "n2", "x2", "y2", "z2")))
      +rl4 = D.pick(isz, u4, D.add("p", D.add("p", u1, u2), D.add("p", u3, u4)))
      +erl = D.pick(isz, A.ih("f1", "n1", "f2", "n2", "x2", "y2", "z2"),
        A.acong(A.g(nf1, n1f1b, w1, "z1"), D.add("p", u1, u2), A.g("f1", "n1", w2, "z2"), D.add("p", u3, u4), r_first, r_second))
      +erot = D.pick(isz, D.add("p", t1, D.add("p", t2, t4)), D.add("p", D.add("p", t3, t1), D.add("p", t2, t4)))
      +eerot = D.pick(isz, D.cat(["A.Add.assoc(~T, ~add, ~add_assoc, p, ", t1, ", ", t2, ", ", t4, ")"]),
        D.cat(["A.Add.rot4(~T, ~add, ~add_assoc, ~add_comm, p, ", t1, ", ", t2, ", ", t3, ", ", t4, ")"]))
      +rrot = D.pick(isz, u4, D.add("p", D.add("p", u3, u1), D.add("p", u2, u4)))
      +errot = D.pick(isz, "{==}", D.cat(["A.Add.rot4(~T, ~add, ~add_assoc, ~add_comm, p, ", u1, ", ", u2, ", ", u3, ", ", u4, ")"]))
      +efin = D.pick(isz, D.add("p", t1r, D.add("p", t2r, t4r)), D.add("p", D.add("p", t3r, t1r), D.add("p", t2r, t4r)))
      +eefin = D.pick(isz, A.acong(t1, t1r, D.add("p", t2, t4), D.add("p", t2r, t4r), et1, A.acong(t2, t2r, t4, t4r, et2, et4)),
        A.acong(D.add("p", t3, t1), D.add("p", t3r, t1r), D.add("p", t2, t4), D.add("p", t2r, t4r),
          A.acong(t3, t3r, t1, t1r, et3, et1), A.acong(t2, t2r, t4, t4r, et2, et4)))
      +rfin = D.pick(isz, u4r, D.add("p", D.add("p", u3r, u1r), D.add("p", u2r, u4r)))
      +erfin = D.pick(isz, "{==}", A.acong(D.add("p", u3, u1), D.add("p", u3r, u1r), D.add("p", u2, u4), D.add("p", u2r, u4r),
        A.acong(u3, u3r, u1, u1r, eu3, eu1), A.acong(u2, u2r, u4, u4r, eu2, "{==}")))
      +sig = D.byq(q, "S.Gen{S.QZ{}, rest}", "S.Gen{S.QP{}, rest}", "S.Gen{S.QN{}, rest}")
      +lhs = D.gpf("1n+p", "f1", "n1", D.mk("p", w1, w2), "S.N{z1, z2}", sig)
      +l_n = D.gpf("1n+p", "f1", "n1", D.cat(["S.N{", w1, ", ", w2, "}"]), "S.N{z1, z2}", sig)
      +l0 = D.cat(["P.Gp.mk_l(", D.OPS(), ", p, f1, n1, ", w1, ", ", w2, ", S.N{z1, z2}, ", sig, ")"])
      +l1 = A.mcong(el, el4, rl, rl4, eel, erl)
      +l2 = A.mcong(el4, erot, rl4, rrot, eerot, errot)
      +l3 = A.mcong(erot, efin, rrot, rfin, eefin, erfin)
      +mfin = D.mk("p", efin, rfin)
      +lhs_chain = D.trans(mv1, lhs, l_n, mfin, l0,
        D.trans(mv1, D.mk("p", el, rl), D.mk("p", el4, rl4), mfin, l1,
          D.trans(mv1, D.mk("p", el4, rl4), D.mk("p", erot, rrot), mfin, l2, l3)))
      +rhs = D.gpf("1n+p", g, m, "S.N{x1, x2}", D.mk("p", v1, v2), sig)
      +r_n = D.gpf("1n+p", g, m, "S.N{x1, x2}", D.cat(["S.N{", v1, ", ", v2, "}"]), sig)
      +r0 = D.cat(["P.Gp.mk_r(", D.OPS(), ", p, ", g, ", ", m, ", S.N{x1, x2}, ", v1, ", ", v2, ", ", sig, ")"])
      +er = D.add("p", A.g(g, mg, "x1", v2), A.g(ng, m, "x2", v1))
      +rr = D.pick(isz, A.g(g, m, "x2", v2), D.add("p", A.g(ng, mgb, "x1", v1), A.g(g, m, "x2", v2)))
      +e_r2 = D.trans(mv, A.g(ng, m, "x2", v1), D.add("p", A.g(ng, m, "x2", d1), A.g(ng, m, "x2", d2)), D.add("p", t2r, t4r),
        A.addr(ng, m, "x2", d1, d2),
        A.acong(A.g(ng, m, "x2", d1), t2r, A.g(ng, m, "x2", d2), t4r, A.pull(ng, m, "x2", "f1", "f1", "y1", "z2"), "{==}"))
      +e_r1 = D.trans(mv, A.g(g, mg, "x1", v2), D.add("p", A.g(g, mg, "x1", c1), A.g(g, mg, "x1", c2)), D.add("p", t3r, t1r),
        A.addr(g, mg, "x1", c1, c2),
        A.acong(A.g(g, mg, "x1", c1), t3r, A.g(g, mg, "x1", c2), t1r, A.pull(g, mg, "x1", nf1, c1n, "y1", "z1"), "{==}"))
      +eer = D.pick(isz, A.acong(A.g(g, mg, "x1", v2), t1r, A.g(ng, m, "x2", v1), D.add("p", t2r, t4r), "{==}", e_r2),
        A.acong(A.g(g, mg, "x1", v2), D.add("p", t3r, t1r), A.g(ng, m, "x2", v1), D.add("p", t2r, t4r), e_r1, e_r2))
      +rr1 = D.trans(mv, A.g(ng, mgb, "x1", v1), D.add("p", A.g(ng, mgb, "x1", d1), A.g(ng, mgb, "x1", d2)), D.add("p", u3r, u1r),
        A.addr(ng, mgb, "x1", d1, d2),
        A.acong(A.g(ng, mgb, "x1", d1), u3r, A.g(ng, mgb, "x1", d2), u1r, A.pull(ng, mgb, "x1", "f1", "f1", "y1", "z2"), "{==}"))
      +rr2 = D.trans(mv, A.g(g, m, "x2", v2), D.add("p", A.g(g, m, "x2", c1), A.g(g, m, "x2", c2)), D.add("p", u2r, u4r),
        A.addr(g, m, "x2", c1, c2),
        A.acong(A.g(g, m, "x2", c1), u2r, A.g(g, m, "x2", c2), u4r, A.pull(g, m, "x2", nf1, c1n, "y1", "z1"), "{==}"))
      +err = D.pick(isz, "{==}", A.acong(A.g(ng, mgb, "x1", v1), D.add("p", u3r, u1r), A.g(g, m, "x2", v2), D.add("p", u2r, u4r), rr1, rr2))
      +rhs_chain = D.trans(mv1, rhs, r_n, mfin, r0, A.mcong(er, efin, rr, rfin, eer, err))
      D.cat(["B.Eq.join(", mv1, ", ", lhs, ", ", rhs, ", ", mfin, ",\n  ", D.ind(lhs_chain, 2n), ",\n  ", D.ind(rhs_chain, 2n), ")"])

def A.level(+q: D.Qc) -> String:
  +isz = D.isz(q)
  +mv = D.mv("p")
  +mv1 = D.mv("1n+p")
  +g = D.xor("f1", "f2")
  +m = D.xor("n1", "n2")
  +n1f1 = D.xor("n1", "f1")
  +n2f2 = D.xor("n2", "f2")
  +n2f2b = D.byq(q, n2f2, n2f2, D.bnot(n2f2))
  +n1f1b = D.byq(q, n1f1, n1f1, D.bnot(n1f1))
  +c1n = D.byq(q, "f1", "f1", D.bnot("f1"))
  +mg = D.xor(m, g)
  +mgb = D.byq(q, mg, mg, D.bnot(mg))
  +a1 = A.g("f2", n2f2, "x1", "y2")
  +a2 = A.g(D.bnot("f2"), "n2", "x2", "y1")
  +b1 = A.g(D.bnot("f2"), n2f2b, "x1", "y1")
  +b2 = A.g("f2", "n2", "x2", "y2")
  +w1 = D.add("p", a1, a2)
  +w2 = D.pick(isz, b2, D.add("p", b1, b2))
  +c1 = A.g(D.bnot("f1"), c1n, "y1", "z1")
  +c2 = A.g("f1", D.F(), "y2", "z2")
  +d1 = A.g("f1", "f1", "y1", "z2")
  +d2 = A.g(D.bnot("f1"), D.F(), "y2", "z1")
  +v1 = D.add("p", d1, d2)
  +v2 = D.pick(isz, c2, D.add("p", c1, c2))
  +i22 = A.g("f1", D.F(), "y2", "z2")
  +i12 = A.g("f1", D.F(), "y1", "z2")
  +i11 = A.g(D.bnot("f1"), D.F(), "y1", "z1")
  +i21 = A.g(D.bnot("f1"), D.F(), "y2", "z1")
  +tm = {Tms{
    A.g(D.xor("f1", "f2"), D.xor(n1f1, n2f2), "x1", i22),
    A.g(D.xor("f1", D.bnot("f2")), D.xor(n1f1, "n2"), "x2", i12),
    A.g(D.xor(D.bnot("f1"), D.bnot("f2")), D.xor("n1", n2f2b), "x1", i11),
    A.g(D.xor(D.bnot("f1"), "f2"), D.xor("n1", "n2"), "x2", i21),
    A.g(D.xor(D.bnot("f1"), "f2"), D.xor(n1f1b, n2f2), "x1", i21),
    A.g(D.xor(D.bnot("f1"), D.bnot("f2")), D.xor(n1f1b, "n2"), "x2", i11),
    A.g(D.xor("f1", D.bnot("f2")), D.xor("n1", n2f2b), "x1", i12),
    A.g(D.xor("f1", "f2"), D.xor("n1", "n2"), "x2", i22),
    A.g(g, mg, "x1", i22),
    A.g(D.bnot(g), D.xor(m, "f1"), "x2", i12),
    A.g(g, D.xor(mg, c1n), "x1", i11),
    A.g(D.bnot(g), m, "x2", i21),
    A.g(D.bnot(g), mgb, "x1", i21),
    A.g(g, D.xor(m, c1n), "x2", i11),
    A.g(D.bnot(g), D.xor(mgb, "f1"), "x1", i12),
    A.g(g, m, "x2", i22)} : Tms}
  A.level.go(q, isz, mv, mv1, g, m, n1f1, n2f2, n2f2b, n1f1b, c1n, mg, mgb, a1, a2, b1, b2, w1, w2, c1, c2, d1, d2, v1, v2, i22, i12, i11, i21, tm)

def A.text() -> String:
  +mvd = D.mv("d")
  +g = D.xor("f1", "f2")
  +m = D.xor("n1", "n2")
  D.cat(["# The geometric product, part 2: associativity, by induction on the
# dimension over every flag, from the lemmas of gp.bend.

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S
import ./base.bend as B
import ./leaf.bend as L
import ./add.bend as A
import ./flags.bend as F
import ./gp.bend as P
# Associativity
# -------------

# (inv^f1 ((-1)^n2 inv^f2(x) y)) z, signed by n1, is the product of x and
# inv^f1(y) z with the flags combined: the induction carries every flag.
def Gp.assoc(", D.OPSD(), ", ~add_assoc: R.Ring.Assoc(T, add), ~add_comm: R.Ring.Comm(T, add),
  ~mul_assoc: R.Ring.Assoc(T, mul), ~dist_l: R.Ring.DistL(T, add, mul), ~dist_r: R.Ring.DistR(T, add, mul),
  ~neg_add: R.Ring.NegAdd(T, add, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  ~neg_mul_l: R.Ring.NegMulL(T, mul, neg), ~neg_mul_r: R.Ring.NegMulR(T, mul, neg),
  +d: Nat, +f1: Bool, +n1: Bool, +f2: Bool, +n2: Bool, x: ", mvd, ", y: ", mvd, ", z: ", mvd, ", +sig: S.Sig(d))
  -> {", D.gpf("d", "f1", "n1", D.gpf("d", "f2", "n2", "x", "y", "sig"), "z", "sig"), " == ", D.gpf("d", g, m, "x", D.gpf("d", "f1", D.F(), "y", "z", "sig"), "sig"), " : ", mvd, "}:
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
              match z:
                case S.LZ{}:
                  {==}
                case S.L{+c}:
                  B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n1, mul(S.Ring.negf(~T, ~neg, n2, mul(a, b)), c)),
                    S.Ring.negf(~T, ~neg, ", m, ", mul(a, mul(b, c))),
                    Equal.trans(T, S.Ring.negf(~T, ~neg, n1, mul(S.Ring.negf(~T, ~neg, n2, mul(a, b)), c)),
                      S.Ring.negf(~T, ~neg, ", m, ", mul(mul(a, b), c)),
                      S.Ring.negf(~T, ~neg, ", m, ", mul(a, mul(b, c))),
                      Equal.trans(T, S.Ring.negf(~T, ~neg, n1, mul(S.Ring.negf(~T, ~neg, n2, mul(a, b)), c)),
                        S.Ring.negf(~T, ~neg, n1, S.Ring.negf(~T, ~neg, n2, mul(mul(a, b), c))),
                        S.Ring.negf(~T, ~neg, ", m, ", mul(mul(a, b), c)),
                        Equal.cong(T, T, w => S.Ring.negf(~T, ~neg, n1, w), mul(S.Ring.negf(~T, ~neg, n2, mul(a, b)), c),
                          S.Ring.negf(~T, ~neg, n2, mul(mul(a, b), c)), L.Negf.mul_l(~T, ~mul, ~neg, ~neg_mul_l, n2, mul(a, b), c)),
                        L.Negf.negf(~T, ~neg, ~neg_neg, n1, n2, mul(mul(a, b), c))),
                      Equal.cong(T, T, w => S.Ring.negf(~T, ~neg, ", m, ", w), mul(mul(a, b), c), mul(a, mul(b, c)), mul_assoc(a, b, c))))
    case 1n+p:
      match x:
        case S.NZ{}:
          {==}
        case S.N{+x1, +x2}:
          match y:
            case S.NZ{}:
              {==}
            case S.N{+y1, +y2}:
              match z:
                case S.NZ{}:
                  P.Gp.zero_r(", D.OPS(), ", 1n+p, f1, n1, ", D.gpf("1n+p", "f2", "n2", "S.N{x1, x2}", "S.N{y1, y2}", "sig"), ", sig)
                case S.N{+z1, +z2}:
", D.qcases(A.level(D.CZ{}), A.level(D.CP{}), A.level(D.CN{}), 18n), "
"])
