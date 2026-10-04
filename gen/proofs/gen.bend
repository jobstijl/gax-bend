# Writes proofs/gen.bend: basis vectors square to their metric and distinct
# ones anticommute, with the scalar and vector products behind both.

import Base
import ./dsl.bend as D

def N.sc(+d: String, +c: String) -> String:
  D.cat(["S.MV.scalar(T, ", d, ", ", c, ")"])

def N.ge(+d: String, +i: String, +c: String) -> String:
  D.cat(["S.MV.gen(T, ", d, ", ", i, ", ", c, ")"])

def N.z(+d: String) -> String:
  D.cat(["S.MV.zero(T, ", d, ")"])

def N.ofq(+d: String, +q: String, +c: String) -> String:
  D.cat(["S.MV.of_q(~T, ~neg, ", d, ", ", q, ", ", c, ")"])

def N.negf(+n: String, +a: String) -> String:
  D.cat(["S.Ring.negf(~T, ~neg, ", n, ", ", a, ")"])

def N.zl(+d: String, +f: String, +n: String, +y: String) -> String:
  D.cat(["P.Gp.zero_l(", D.OPS(), ", ", d, ", ", f, ", ", n, ", ", y, ", rest)"])

def N.zr(+d: String, +f: String, +n: String, +x: String) -> String:
  D.cat(["P.Gp.zero_r(", D.OPS(), ", ", d, ", ", f, ", ", n, ", ", x, ", rest)"])

def N.acong(+d: String, +a: String, +a2: String, +b: String, +b2: String, +ea: String, +eb: String) -> String:
  D.cat(["A.Add.cong(~T, ~add, ", d, ", ", a, ", ", a2, ", ", b, ", ", b2, ",\n  ", D.ind(ea, 2n), ",\n  ", D.ind(eb, 2n), ")"])

def N.zl_add(+d: String) -> String:
  D.cat(["A.Add.zero_l(~T, ~add, ", d, ", ", N.z(d), ")"])

def N.mcong(+p: String, +e: String, +e2: String, +r: String, +r2: String, +ee: String, +er: String) -> String:
  D.cat(["P.Mk.cong(T, ", p, ", ", e, ", ", e2, ", ", r, ", ", r2, ",\n  ", D.ind(ee, 2n), ",\n  ", D.ind(er, 2n), ")"])

# add(t1, t2) == zero given t1 == zero and t2 == zero
def N.zz(+p: String, +t1: String, +t2: String, +e1: String, +e2: String) -> String:
  D.trans(D.mv(p), D.add(p, t1, t2), D.add(p, N.z(p), N.z(p)), N.z(p), N.acong(p, t1, N.z(p), t2, N.z(p), e1, e2), N.zl_add(p))

def N.head() -> String:
  D.cat(["# Generators: basis vectors square to their metric and distinct ones
# anticommute.

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S
import ./base.bend as B
import ./leaf.bend as L
import ./add.bend as A
import ./sgn.bend as G
import ./gp.bend as P

def Gen.mk_zs(-T: Data, d: Nat, w: T) -> {", D.mk("d", N.z("d"), N.sc("d", "w")), " == ", N.sc("1n+d", "w"), " : ", D.mv("1n+d"), "}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Gen.mk_sz(-T: Data, d: Nat, w: T) -> {", D.mk("d", N.sc("d", "w"), N.z("d")), " == S.N{", N.sc("d", "w"), ", ", N.z("d"), "} : ", D.mv("1n+d"), "}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Gen.mk_zz(-T: Data, d: Nat) -> {", D.mk("d", N.z("d"), N.z("d")), " == ", N.z("1n+d"), " : ", D.mv("1n+d"), "}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Gen.ofq_mk(~T: Data, ~neg: T -> T, +d: Nat, q: S.Q, c: T) -> {", N.ofq("1n+d", "q", "c"), " == ", D.mk("d", N.z("d"), N.ofq("d", "q", "c")), " : ", D.mv("1n+d"), "}:
  match q:
    case S.QP{}:
      Equal.sym(", D.mv("1n+d"), ", ", D.mk("d", N.z("d"), N.sc("d", "c")), ", ", N.sc("1n+d", "c"), ", Gen.mk_zs(T, d, c))
    case S.QN{}:
      Equal.sym(", D.mv("1n+d"), ", ", D.mk("d", N.z("d"), N.sc("d", "neg(c)")), ", ", N.sc("1n+d", "neg(c)"), ", Gen.mk_zs(T, d, neg(c)))
    case S.QZ{}:
      Equal.sym(", D.mv("1n+d"), ", ", D.mk("d", N.z("d"), N.z("d")), ", ", N.z("1n+d"), ", Gen.mk_zz(T, d))

def Gen.coef(-T: Data, -d: Nat, -j: Nat, -c: T, -c2: T, e: {c == c2 : T}) -> {", N.ge("d", "j", "c"), " == ", N.ge("d", "j", "c2"), " : ", D.mv("d"), "}:
  %e : {", N.ge("d", "j", "c"), " == ", N.ge("d", "j", "_"), " : ", D.mv("d"), "}
  {==}
"])

# one metric case of Gen.ss: a scalar times a scalar
def N.ss.body(+q: D.Qc) -> String:
  +isz = D.isz(q)
  +nf = D.xor("n", "f")
  +nf3 = D.byq(q, nf, nf, D.bnot(nf))
  +w = N.negf("n", "mul(a, b)")
  +g0 = D.gpf("p", "f", nf, N.z("p"), N.sc("p", "b"), "rest")
  +g1 = D.gpf("p", D.bnot("f"), "n", N.sc("p", "a"), N.z("p"), "rest")
  +ee = N.zz("p", g0, g1, N.zl("p", "f", nf, N.sc("p", "b")), N.zr("p", D.bnot("f"), "n", N.sc("p", "a")))
  +s4 = D.gpf("p", "f", "n", N.sc("p", "a"), N.sc("p", "b"), "rest")
  +ih = D.cat(["Gen.ss(", D.OPS(), ", p, f, n, a, b, rest)"])
  +g3 = D.gpf("p", D.bnot("f"), nf3, N.z("p"), N.z("p"), "rest")
  +r0 = D.pick(isz, s4, D.add("p", g3, s4))
  +er = D.pick(isz, ih, D.trans(D.mv("p"), D.add("p", g3, s4), D.add("p", N.z("p"), N.sc("p", w)), N.sc("p", w),
    N.acong("p", g3, N.z("p"), s4, N.sc("p", w), N.zl("p", D.bnot("f"), nf3, N.z("p")), ih),
    D.cat(["A.Add.zero_l(~T, ~add, p, ", N.sc("p", w), ")"])))
  +e0 = D.add("p", g0, g1)
  D.trans(D.mv("1n+p"), D.mk("p", e0, r0), D.mk("p", N.z("p"), N.sc("p", w)), N.sc("1n+p", w),
    N.mcong("p", e0, N.z("p"), r0, N.sc("p", w), ee, er), D.cat(["Gen.mk_zs(T, p, ", w, ")"]))

def N.ss() -> String:
  D.cat(["# a scalar times a scalar
def Gen.ss(", D.OPSD(), ", +d: Nat, +f: Bool, +n: Bool, +a: T, +b: T, +sig: S.Sig(d))
  -> {", D.gpf("d", "f", "n", N.sc("d", "a"), N.sc("d", "b"), "sig"), " == ", N.sc("d", N.negf("n", "mul(a, b)")), " : ", D.mv("d"), "}:
  match d:
    case 0n:
      {==}
    case 1n+p:
", D.qcases(N.ss.body(D.CZ{}), N.ss.body(D.CP{}), N.ss.body(D.CN{}), 6n), "
"])

# Gen.sq at index 0, one metric case
def N.sq0(+q: D.Qc) -> String:
  +isz = D.isz(q)
  +g0 = D.gpf("p", D.F(), D.F(), N.sc("p", "a"), N.z("p"), "rest")
  +g1 = D.gpf("p", D.Tr(), D.F(), N.z("p"), N.sc("p", "b"), "rest")
  +e0 = D.add("p", g0, g1)
  +ee = N.zz("p", g0, g1, N.zr("p", D.F(), D.F(), N.sc("p", "a")), N.zl("p", D.Tr(), D.F(), N.sc("p", "b")))
  +g4 = D.gpf("p", D.F(), D.F(), N.z("p"), N.z("p"), "rest")
  +n3 = D.byq(q, D.F(), D.F(), D.Tr())
  +w = D.byq(q, "mul(a, b)", "mul(a, b)", "neg(mul(a, b))")
  +g3 = D.gpf("p", D.Tr(), n3, N.sc("p", "a"), N.sc("p", "b"), "rest")
  +r0 = D.add("p", g3, g4)
  +er = D.trans(D.mv("p"), r0, D.add("p", N.sc("p", w), N.z("p")), N.sc("p", w),
    N.acong("p", g3, N.sc("p", w), g4, N.z("p"), D.cat(["Gen.ss(", D.OPS(), ", p, ", D.Tr(), ", ", n3, ", a, b, rest)"]), N.zl("p", D.F(), D.F(), N.z("p"))),
    D.cat(["A.Add.zero_r(~T, ~add, p, ", N.sc("p", w), ")"]))
  D.pick(isz,
    D.trans(D.mv("1n+p"), D.mk("p", e0, g4), D.mk("p", N.z("p"), N.z("p")), N.z("1n+p"),
      N.mcong("p", e0, N.z("p"), g4, N.z("p"), ee, N.zl("p", D.F(), D.F(), N.z("p"))), "Gen.mk_zz(T, p)"),
    D.trans(D.mv("1n+p"), D.mk("p", e0, r0), D.mk("p", N.z("p"), N.sc("p", w)), N.sc("1n+p", w),
      N.mcong("p", e0, N.z("p"), r0, N.sc("p", w), ee, er), D.cat(["Gen.mk_zs(T, p, ", w, ")"])))

# Gen.sq at index 1+j, one metric case
def N.sqj(+q: D.Qc) -> String:
  +isz = D.isz(q)
  +c = {"mul(a, b)" : String}
  +ga = N.ge("p", "j", "a")
  +gb = N.ge("p", "j", "b")
  +sigq = D.byq(q, "S.Gen{S.QZ{}, rest}", "S.Gen{S.QP{}, rest}", "S.Gen{S.QN{}, rest}")
  +l0 = D.gpf("1n+p", D.F(), D.F(), D.mk("p", N.z("p"), ga), D.mk("p", N.z("p"), gb), sigq)
  +l1 = D.gpf("1n+p", D.F(), D.F(), D.cat(["S.N{", N.z("p"), ", ", ga, "}"]), D.mk("p", N.z("p"), gb), sigq)
  +l2 = D.gpf("1n+p", D.F(), D.F(), D.cat(["S.N{", N.z("p"), ", ", ga, "}"]), D.cat(["S.N{", N.z("p"), ", ", gb, "}"]), sigq)
  +s1 = D.cat(["P.Gp.mk_l(", D.OPS(), ", p, ", D.F(), ", ", D.F(), ", ", N.z("p"), ", ", ga, ", ", D.mk("p", N.z("p"), gb), ", ", sigq, ")"])
  +s2 = D.cat(["P.Gp.mk_r(", D.OPS(), ", p, ", D.F(), ", ", D.F(), ", S.N{", N.z("p"), ", ", ga, "}, ", N.z("p"), ", ", gb, ", ", sigq, ")"])
  +g0 = D.gpf("p", D.F(), D.F(), N.z("p"), gb, "rest")
  +g1 = D.gpf("p", D.Tr(), D.F(), ga, N.z("p"), "rest")
  +e0 = D.add("p", g0, g1)
  +ee = N.zz("p", g0, g1, N.zl("p", D.F(), D.F(), gb), N.zr("p", D.Tr(), D.F(), ga))
  +g4 = D.gpf("p", D.F(), D.F(), ga, gb, "rest")
  +target = N.ofq("p", "S.Sig.at(p, rest, j)", c)
  +ih = D.cat(["Gen.sq(", D.OPS(), ", p, j, a, b, rest)"])
  +n3 = D.byq(q, D.F(), D.F(), D.Tr())
  +g3 = D.gpf("p", D.Tr(), n3, N.z("p"), N.z("p"), "rest")
  +r0 = D.pick(isz, g4, D.add("p", g3, g4))
  +er = D.pick(isz, ih, D.trans(D.mv("p"), D.add("p", g3, g4), D.add("p", N.z("p"), target), target,
    N.acong("p", g3, N.z("p"), g4, target, N.zl("p", D.Tr(), n3, N.z("p")), ih), D.cat(["A.Add.zero_l(~T, ~add, p, ", target, ")"])))
  +s3 = N.mcong("p", e0, N.z("p"), r0, target, ee, er)
  +ofq1 = N.ofq("1n+p", "S.Sig.at(p, rest, j)", c)
  +s4 = D.sym(D.mv("1n+p"), ofq1, D.mk("p", N.z("p"), target), D.cat(["Gen.ofq_mk(~T, ~neg, p, S.Sig.at(p, rest, j), ", c, ")"]))
  D.trans(D.mv("1n+p"), l0, l2, ofq1,
    D.trans(D.mv("1n+p"), l0, l1, l2, s1, s2),
    D.trans(D.mv("1n+p"), D.mk("p", e0, r0), D.mk("p", N.z("p"), target), ofq1, s3, s4))

def N.sq() -> String:
  D.cat(["# a generator squares to its metric: e_i a e_i b = q_i ab
def Gen.sq(", D.OPSD(), ", +d: Nat, +i: Nat, +a: T, +b: T, +sig: S.Sig(d))
  -> {", D.gpf("d", D.F(), D.F(), N.ge("d", "i", "a"), N.ge("d", "i", "b"), "sig"), " == ", N.ofq("d", "S.Sig.at(d, sig, i)", "mul(a, b)"), " : ", D.mv("d"), "}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      match i:
        case 0n:
          match sig:
            case S.Gen{q, +rest}:
              match q:
                case S.QZ{}:
", D.ind(N.sq0(D.CZ{}), 18n), "
                case S.QP{}:
", D.ind(N.sq0(D.CP{}), 18n), "
                case S.QN{}:
", D.ind(N.sq0(D.CN{}), 18n), "
        case 1n+j:
          match sig:
            case S.Gen{q, +rest}:
              match q:
                case S.QZ{}:
", D.ind(N.sqj(D.CZ{}), 18n), "
                case S.QP{}:
", D.ind(N.sqj(D.CP{}), 18n), "
                case S.QN{}:
", D.ind(N.sqj(D.CN{}), 18n), "
"])

def N.part1() -> String:
  D.sep([N.head(), N.ss(), N.sq()], "\n")

# Part 2: grade signs of scalars and vectors, scalar times vector
# ---------------------------------------------------------------

def N.signs() -> String:
  D.cat(["# a grade sign on a scalar is its n flag
def Gen.sgns(~T: Data, ~neg: T -> T, +d: Nat, +m: Bool, +g: Bool, +c: T)
  -> {", D.sgn("d", "m", "g", D.F(), N.sc("d", "c")), " == ", N.sc("d", N.negf("m", "c")), " : ", D.mv("d"), "}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      B.Node.cong2(", D.mv("p"), ", ", D.sgn("p", D.xor("m", "g"), D.xor("g", D.F()), D.F(), N.z("p")), ", ", N.z("p"), ", ", D.sgn("p", "m", "g", D.F(), N.sc("p", "c")), ", ", N.sc("p", N.negf("m", "c")), ",
        G.Sgn.zero(~T, ~neg, p, ", D.xor("m", "g"), ", ", D.xor("g", D.F()), ", ", D.F(), "), Gen.sgns(~T, ~neg, p, m, g, c))

# a grade sign on a vector: (-1)^(n + f)
def Gen.sgnv(~T: Data, ~neg: T -> T, +d: Nat, +n: Bool, +f: Bool, +j: Nat, +c: T)
  -> {", D.sgn("d", "n", "f", D.F(), N.ge("d", "j", "c")), " == ", N.ge("d", "j", N.negf(D.xor("n", "f"), "c")), " : ", D.mv("d"), "}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      match j:
        case 0n:
          B.Node.cong2(", D.mv("p"), ", ", D.sgn("p", D.xor("n", "f"), D.xor("f", D.F()), D.F(), N.sc("p", "c")), ", ", N.sc("p", N.negf(D.xor("n", "f"), "c")), ",
            ", D.sgn("p", "n", "f", D.F(), N.z("p")), ", ", N.z("p"), ",
            Gen.sgns(~T, ~neg, p, ", D.xor("n", "f"), ", ", D.xor("f", D.F()), ", c), G.Sgn.zero(~T, ~neg, p, n, f, ", D.F(), "))
        case 1n+k:
          Equal.trans(", D.mv("1n+p"), ", ", D.sgn("1n+p", "n", "f", D.F(), D.mk("p", N.z("p"), N.ge("p", "k", "c"))), ",
            ", D.mk("p", D.sgn("p", D.xor("n", "f"), D.xor("f", D.F()), D.F(), N.z("p")), D.sgn("p", "n", "f", D.F(), N.ge("p", "k", "c"))), ",
            ", D.mk("p", N.z("p"), N.ge("p", "k", N.negf(D.xor("n", "f"), "c"))), ",
            G.Sgn.mk(~T, ~neg, p, n, f, ", D.F(), ", ", N.z("p"), ", ", N.ge("p", "k", "c"), "),
            P.Mk.cong(T, p, ", D.sgn("p", D.xor("n", "f"), D.xor("f", D.F()), D.F(), N.z("p")), ", ", N.z("p"), ", ", D.sgn("p", "n", "f", D.F(), N.ge("p", "k", "c")), ", ", N.ge("p", "k", N.negf(D.xor("n", "f"), "c")), ",
              G.Sgn.zero(~T, ~neg, p, ", D.xor("n", "f"), ", ", D.xor("f", D.F()), ", ", D.F(), "), Gen.sgnv(~T, ~neg, p, n, f, k, c)))
"])

# scalar times vector at index 0
def N.sv0(+q: D.Qc) -> String:
  +isz = D.isz(q)
  +nf = D.xor("n", "f")
  +nf3 = D.byq(q, nf, nf, D.bnot(nf))
  +w = N.negf("n", "mul(a, b)")
  +g0 = D.gpf("p", "f", nf, N.z("p"), N.z("p"), "rest")
  +g1 = D.gpf("p", D.bnot("f"), "n", N.sc("p", "a"), N.sc("p", "b"), "rest")
  +ee = D.trans(D.mv("p"), D.add("p", g0, g1), D.add("p", N.z("p"), N.sc("p", w)), N.sc("p", w),
    N.acong("p", g0, N.z("p"), g1, N.sc("p", w), N.zl("p", "f", nf, N.z("p")), D.cat(["Gen.ss(", D.OPS(), ", p, ", D.bnot("f"), ", n, a, b, rest)"])),
    D.cat(["A.Add.zero_l(~T, ~add, p, ", N.sc("p", w), ")"]))
  +g4 = D.gpf("p", "f", "n", N.sc("p", "a"), N.z("p"), "rest")
  +g3 = D.gpf("p", D.bnot("f"), nf3, N.z("p"), N.sc("p", "b"), "rest")
  +r0 = D.pick(isz, g4, D.add("p", g3, g4))
  +er = D.pick(isz, N.zr("p", "f", "n", N.sc("p", "a")), N.zz("p", g3, g4, N.zl("p", D.bnot("f"), nf3, N.sc("p", "b")), N.zr("p", "f", "n", N.sc("p", "a"))))
  +e0 = D.add("p", g0, g1)
  D.trans(D.mv("1n+p"), D.mk("p", e0, r0), D.mk("p", N.sc("p", w), N.z("p")), D.cat(["S.N{", N.sc("p", w), ", ", N.z("p"), "}"]),
    N.mcong("p", e0, N.sc("p", w), r0, N.z("p"), ee, er), D.cat(["Gen.mk_sz(T, p, ", w, ")"]))

# scalar times vector at index 1+k, after MV.mk is opened
def N.svk(+q: D.Qc) -> String:
  +isz = D.isz(q)
  +nf = D.xor("n", "f")
  +nf3 = D.byq(q, nf, nf, D.bnot(nf))
  +gb = N.ge("p", "k", "b")
  +w = N.negf("n", "mul(a, b)")
  +tgt = N.ge("p", "k", w)
  +g0 = D.gpf("p", "f", nf, N.z("p"), gb, "rest")
  +g1 = D.gpf("p", D.bnot("f"), "n", N.sc("p", "a"), N.z("p"), "rest")
  +ee = N.zz("p", g0, g1, N.zl("p", "f", nf, gb), N.zr("p", D.bnot("f"), "n", N.sc("p", "a")))
  +g4 = D.gpf("p", "f", "n", N.sc("p", "a"), gb, "rest")
  +ih = D.cat(["Gen.sv(", D.OPS(), ", p, f, n, a, k, b, rest)"])
  +g3 = D.gpf("p", D.bnot("f"), nf3, N.z("p"), N.z("p"), "rest")
  +r0 = D.pick(isz, g4, D.add("p", g3, g4))
  +er = D.pick(isz, ih, D.trans(D.mv("p"), D.add("p", g3, g4), D.add("p", N.z("p"), tgt), tgt, N.acong("p", g3, N.z("p"), g4, tgt, N.zl("p", D.bnot("f"), nf3, N.z("p")), ih),
    D.cat(["A.Add.zero_l(~T, ~add, p, ", tgt, ")"])))
  N.mcong("p", D.add("p", g0, g1), N.z("p"), r0, tgt, ee, er)

# vector times scalar at index 0
def N.vs0(+q: D.Qc) -> String:
  +isz = D.isz(q)
  +nf = D.xor("n", "f")
  +nf3 = D.byq(q, nf, nf, D.bnot(nf))
  +w = N.negf(nf, "mul(a, b)")
  +g0 = D.gpf("p", "f", nf, N.sc("p", "a"), N.sc("p", "b"), "rest")
  +g1 = D.gpf("p", D.bnot("f"), "n", N.z("p"), N.z("p"), "rest")
  +ee = D.trans(D.mv("p"), D.add("p", g0, g1), D.add("p", N.sc("p", w), N.z("p")), N.sc("p", w),
    N.acong("p", g0, N.sc("p", w), g1, N.z("p"), D.cat(["Gen.ss(", D.OPS(), ", p, f, ", nf, ", a, b, rest)"]), N.zl("p", D.bnot("f"), "n", N.z("p"))),
    D.cat(["A.Add.zero_r(~T, ~add, p, ", N.sc("p", w), ")"]))
  +g4 = D.gpf("p", "f", "n", N.z("p"), N.sc("p", "b"), "rest")
  +g3 = D.gpf("p", D.bnot("f"), nf3, N.sc("p", "a"), N.z("p"), "rest")
  +r0 = D.pick(isz, g4, D.add("p", g3, g4))
  +er = D.pick(isz, N.zl("p", "f", "n", N.sc("p", "b")), N.zz("p", g3, g4, N.zr("p", D.bnot("f"), nf3, N.sc("p", "a")), N.zl("p", "f", "n", N.sc("p", "b"))))
  +e0 = D.add("p", g0, g1)
  D.trans(D.mv("1n+p"), D.mk("p", e0, r0), D.mk("p", N.sc("p", w), N.z("p")), D.cat(["S.N{", N.sc("p", w), ", ", N.z("p"), "}"]),
    N.mcong("p", e0, N.sc("p", w), r0, N.z("p"), ee, er), D.cat(["Gen.mk_sz(T, p, ", w, ")"]))

# vector times scalar at index 1+k, after MV.mk is opened
def N.vsk(+q: D.Qc) -> String:
  +isz = D.isz(q)
  +nf = D.xor("n", "f")
  +nf3 = D.byq(q, nf, nf, D.bnot(nf))
  +ga = N.ge("p", "k", "a")
  +w = N.negf(nf, "mul(a, b)")
  +tgt = N.ge("p", "k", w)
  +g0 = D.gpf("p", "f", nf, N.z("p"), N.sc("p", "b"), "rest")
  +g1 = D.gpf("p", D.bnot("f"), "n", ga, N.z("p"), "rest")
  +ee = N.zz("p", g0, g1, N.zl("p", "f", nf, N.sc("p", "b")), N.zr("p", D.bnot("f"), "n", ga))
  +g4 = D.gpf("p", "f", "n", ga, N.sc("p", "b"), "rest")
  +ih = D.cat(["Gen.vs(", D.OPS(), ", p, f, n, k, a, b, rest)"])
  +g3 = D.gpf("p", D.bnot("f"), nf3, N.z("p"), N.z("p"), "rest")
  +r0 = D.pick(isz, g4, D.add("p", g3, g4))
  +er = D.pick(isz, ih, D.trans(D.mv("p"), D.add("p", g3, g4), D.add("p", N.z("p"), tgt), tgt, N.acong("p", g3, N.z("p"), g4, tgt, N.zl("p", D.bnot("f"), nf3, N.z("p")), ih),
    D.cat(["A.Add.zero_l(~T, ~add, p, ", tgt, ")"])))
  N.mcong("p", D.add("p", g0, g1), N.z("p"), r0, tgt, ee, er)

def N.sigq(q: D.Qc) -> String:
  D.byq(q, "S.Gen{S.QZ{}, rest}", "S.Gen{S.QP{}, rest}", "S.Gen{S.QN{}, rest}")

def N.svk.wrap(+q: D.Qc) -> String:
  +sigq = N.sigq(q)
  +x = D.cat(["S.N{", N.z("p"), ", ", N.sc("p", "a"), "}"])
  +g = N.ge("p", "k", "b")
  D.trans(D.mv("1n+p"), D.gpf("1n+p", "f", "n", x, D.mk("p", N.z("p"), g), sigq), D.gpf("1n+p", "f", "n", x, D.cat(["S.N{", N.z("p"), ", ", g, "}"]), sigq),
    D.mk("p", N.z("p"), N.ge("p", "k", N.negf("n", "mul(a, b)"))),
    D.cat(["P.Gp.mk_r(", D.OPS(), ", p, f, n, ", x, ", ", N.z("p"), ", ", g, ", ", sigq, ")"]), N.svk(q))

def N.vsk.wrap(+q: D.Qc) -> String:
  +sigq = N.sigq(q)
  +y = D.cat(["S.N{", N.z("p"), ", ", N.sc("p", "b"), "}"])
  +g = N.ge("p", "k", "a")
  D.trans(D.mv("1n+p"), D.gpf("1n+p", "f", "n", D.mk("p", N.z("p"), g), y, sigq), D.gpf("1n+p", "f", "n", D.cat(["S.N{", N.z("p"), ", ", g, "}"]), y, sigq),
    D.mk("p", N.z("p"), N.ge("p", "k", N.negf(D.xor("n", "f"), "mul(a, b)"))),
    D.cat(["P.Gp.mk_l(", D.OPS(), ", p, f, n, ", N.z("p"), ", ", g, ", ", y, ", ", sigq, ")"]), N.vsk(q))

def N.svvs() -> String:
  D.cat(["# a scalar times a vector
def Gen.sv(", D.OPSD(), ", +d: Nat, +f: Bool, +n: Bool, +a: T, +j: Nat, +b: T, +sig: S.Sig(d))
  -> {", D.gpf("d", "f", "n", N.sc("d", "a"), N.ge("d", "j", "b"), "sig"), " == ", N.ge("d", "j", N.negf("n", "mul(a, b)")), " : ", D.mv("d"), "}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      match j:
        case 0n:
", D.qcases(N.sv0(D.CZ{}), N.sv0(D.CP{}), N.sv0(D.CN{}), 10n), "
        case 1n+k:
", D.qcases(N.svk.wrap(D.CZ{}), N.svk.wrap(D.CP{}), N.svk.wrap(D.CN{}), 10n), "

# a vector times a scalar: the vector's involution shows as the f flag
def Gen.vs(", D.OPSD(), ", +d: Nat, +f: Bool, +n: Bool, +j: Nat, +a: T, +b: T, +sig: S.Sig(d))
  -> {", D.gpf("d", "f", "n", N.ge("d", "j", "a"), N.sc("d", "b"), "sig"), " == ", N.ge("d", "j", N.negf(D.xor("n", "f"), "mul(a, b)")), " : ", D.mv("d"), "}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      match j:
        case 0n:
", D.qcases(N.vs0(D.CZ{}), N.vs0(D.CP{}), N.vs0(D.CN{}), 10n), "
        case 1n+k:
", D.qcases(N.vsk.wrap(D.CZ{}), N.vsk.wrap(D.CP{}), N.vsk.wrap(D.CN{}), 10n), "
"])

def N.part2() -> String:
  D.sep([N.signs(), N.svvs()], "\n")

# Part 3: distinct generators anticommute
# ---------------------------------------

def N.n3(q: D.Qc) -> String:
  D.byq(q, D.F(), D.F(), D.Tr())

def N.G(+f: String, +n: String, +x: String, +y: String) -> String:
  D.gpf("p", f, n, x, y, "rest")

# the e and r halves of a level of the product N{X1, X2} N{Y1, Y2}
def N.lvl.e(+x1: String, +x2: String, +y1: String, +y2: String) -> String:
  D.add("p", N.G(D.F(), D.F(), x1, y2), N.G(D.Tr(), D.F(), x2, y1))

def N.lvl.r(+q: D.Qc, +x1: String, +x2: String, +y1: String, +y2: String) -> String:
  D.pick(D.isz(q), N.G(D.F(), D.F(), x2, y2), D.add("p", N.G(D.Tr(), N.n3(q), x1, y1), N.G(D.F(), D.F(), x2, y2)))

def N.join(+l0: String, +rhs: String, +m: String, +lhs: String, +rpf: String) -> String:
  D.cat(["B.Eq.join(", D.mv("1n+p"), ", ", l0, ", ", rhs, ", ", m, ",\n  ", D.ind(lhs, 2n), ",\n  ", D.ind(rpf, 2n), ")"])

# the sign side: sgn(T, F, F, I0) == M through Is = mk(tI, zero), with s3
# proving sgn(tI) == tE
def N.rside(+i0: String, +ims: String, +inner: String, +ti: String, +te: String, +m: String, +s3: String) -> String:
  +z = N.z("p")
  +tt = D.Tr()
  +ff = D.F()
  +s1 = D.sgn("p", tt, ff, ff, ti)
  +r1 = D.cat(["G.Sgn.cong(~T, ~neg, 1n+p, ", tt, ", ", ff, ", ", ff, ", ", i0, ", ", ims, ", ", inner, ")"])
  +r2 = D.cat(["G.Sgn.mk(~T, ~neg, p, ", tt, ", ", ff, ", ", ff, ", ", ti, ", ", z, ")"])
  +r3 = N.mcong("p", s1, te, D.sgn("p", tt, ff, ff, z), z, s3, D.cat(["G.Sgn.zero(~T, ~neg, p, ", tt, ", ", ff, ", ", ff, ")"]))
  +si = D.sgn("1n+p", tt, ff, ff, ims)
  D.trans(D.mv("1n+p"), D.sgn("1n+p", tt, ff, ff, i0), si, m, r1,
    D.trans(D.mv("1n+p"), si, D.mk("p", s1, D.sgn("p", tt, ff, ff, z)), m, r2, r3))

# e_0 a times e_(1+k) a
def N.ac0k(+q: D.Qc) -> String:
  +sigq = N.sigq(q)
  +isz = D.isz(q)
  +n3 = N.n3(q)
  +tt = D.Tr()
  +ff = D.F()
  +z = N.z("p")
  +sa = N.sc("p", "a")
  +gk = N.ge("p", "k", "a")
  +nsa = D.cat(["S.N{", sa, ", ", z, "}"])
  +l0 = D.gpf("1n+p", ff, ff, nsa, D.mk("p", z, gk), sigq)
  +sl = D.cat(["P.Gp.mk_r(", D.OPS(), ", p, ", ff, ", ", ff, ", ", nsa, ", ", z, ", ", gk, ", ", sigq, ")"])
  +e0 = N.lvl.e(sa, z, z, gk)
  +r0 = N.lvl.r(q, sa, z, z, gk)
  +te = N.ge("p", "k", "mul(a, a)")
  +ee = D.trans(D.mv("p"), e0, D.add("p", te, z), te,
    N.acong("p", N.G(ff, ff, sa, gk), te, N.G(tt, ff, z, z), z, D.cat(["Gen.sv(", D.OPS(), ", p, ", ff, ", ", ff, ", a, k, a, rest)"]), N.zl("p", tt, ff, z)),
    D.cat(["A.Add.zero_r(~T, ~add, p, ", te, ")"]))
  +er = D.pick(isz, N.zl("p", ff, ff, gk), N.zz("p", N.G(tt, n3, sa, z), N.G(ff, ff, z, gk), N.zr("p", tt, n3, sa), N.zl("p", ff, ff, gk)))
  +m = D.mk("p", te, z)
  +lhs = D.trans(D.mv("1n+p"), l0, D.mk("p", e0, r0), m, sl, N.mcong("p", e0, te, r0, z, ee, er))
  +i0 = D.gpf("1n+p", ff, ff, D.mk("p", z, gk), nsa, sigq)
  +si = D.cat(["P.Gp.mk_l(", D.OPS(), ", p, ", ff, ", ", ff, ", ", z, ", ", gk, ", ", nsa, ", ", sigq, ")"])
  +e1 = N.lvl.e(z, gk, sa, z)
  +r1 = N.lvl.r(q, z, gk, sa, z)
  +ti = N.ge("p", "k", "neg(mul(a, a))")
  +ee1 = D.trans(D.mv("p"), e1, D.add("p", z, ti), ti,
    N.acong("p", N.G(ff, ff, z, z), z, N.G(tt, ff, gk, sa), ti, N.zl("p", ff, ff, z), D.cat(["Gen.vs(", D.OPS(), ", p, ", tt, ", ", ff, ", k, a, a, rest)"])),
    D.cat(["A.Add.zero_l(~T, ~add, p, ", ti, ")"]))
  +er1 = D.pick(isz, N.zr("p", ff, ff, gk), N.zz("p", N.G(tt, n3, z, sa), N.G(ff, ff, gk, z), N.zl("p", tt, n3, sa), N.zr("p", ff, ff, gk)))
  +ims = D.mk("p", ti, z)
  +inner = D.trans(D.mv("1n+p"), i0, D.mk("p", e1, r1), ims, si, N.mcong("p", e1, ti, r1, z, ee1, er1))
  +s3 = D.trans(D.mv("p"), D.sgn("p", tt, ff, ff, ti), N.ge("p", "k", "neg(neg(mul(a, a)))"), te,
    "Gen.sgnv(~T, ~neg, p, True{}, False{}, k, neg(mul(a, a)))",
    "Gen.coef(T, p, k, neg(neg(mul(a, a))), mul(a, a), neg_neg(mul(a, a)))")
  N.join(l0, D.sgn("1n+p", tt, ff, ff, i0), m, lhs, N.rside(i0, ims, inner, ti, te, m, s3))

# e_(1+h) a times e_0 a
def N.ach0(+q: D.Qc) -> String:
  +sigq = N.sigq(q)
  +isz = D.isz(q)
  +n3 = N.n3(q)
  +tt = D.Tr()
  +ff = D.F()
  +z = N.z("p")
  +sa = N.sc("p", "a")
  +gh = N.ge("p", "h", "a")
  +nsa = D.cat(["S.N{", sa, ", ", z, "}"])
  +l0 = D.gpf("1n+p", ff, ff, D.mk("p", z, gh), nsa, sigq)
  +sl = D.cat(["P.Gp.mk_l(", D.OPS(), ", p, ", ff, ", ", ff, ", ", z, ", ", gh, ", ", nsa, ", ", sigq, ")"])
  +e0 = N.lvl.e(z, gh, sa, z)
  +r0 = N.lvl.r(q, z, gh, sa, z)
  +te = N.ge("p", "h", "neg(mul(a, a))")
  +ee = D.trans(D.mv("p"), e0, D.add("p", z, te), te,
    N.acong("p", N.G(ff, ff, z, z), z, N.G(tt, ff, gh, sa), te, N.zl("p", ff, ff, z), D.cat(["Gen.vs(", D.OPS(), ", p, ", tt, ", ", ff, ", h, a, a, rest)"])),
    D.cat(["A.Add.zero_l(~T, ~add, p, ", te, ")"]))
  +er = D.pick(isz, N.zr("p", ff, ff, gh), N.zz("p", N.G(tt, n3, z, sa), N.G(ff, ff, gh, z), N.zl("p", tt, n3, sa), N.zr("p", ff, ff, gh)))
  +m = D.mk("p", te, z)
  +lhs = D.trans(D.mv("1n+p"), l0, D.mk("p", e0, r0), m, sl, N.mcong("p", e0, te, r0, z, ee, er))
  +i0 = D.gpf("1n+p", ff, ff, nsa, D.mk("p", z, gh), sigq)
  +si = D.cat(["P.Gp.mk_r(", D.OPS(), ", p, ", ff, ", ", ff, ", ", nsa, ", ", z, ", ", gh, ", ", sigq, ")"])
  +e1 = N.lvl.e(sa, z, z, gh)
  +r1 = N.lvl.r(q, sa, z, z, gh)
  +ti = N.ge("p", "h", "mul(a, a)")
  +ee1 = D.trans(D.mv("p"), e1, D.add("p", ti, z), ti,
    N.acong("p", N.G(ff, ff, sa, gh), ti, N.G(tt, ff, z, z), z, D.cat(["Gen.sv(", D.OPS(), ", p, ", ff, ", ", ff, ", a, h, a, rest)"]), N.zl("p", tt, ff, z)),
    D.cat(["A.Add.zero_r(~T, ~add, p, ", ti, ")"]))
  +er1 = D.pick(isz, N.zl("p", ff, ff, gh), N.zz("p", N.G(tt, n3, sa, z), N.G(ff, ff, z, gh), N.zr("p", tt, n3, sa), N.zl("p", ff, ff, gh)))
  +ims = D.mk("p", ti, z)
  +inner = D.trans(D.mv("1n+p"), i0, D.mk("p", e1, r1), ims, si, N.mcong("p", e1, ti, r1, z, ee1, er1))
  N.join(l0, D.sgn("1n+p", tt, ff, ff, i0), m, lhs, N.rside(i0, ims, inner, ti, te, m, "Gen.sgnv(~T, ~neg, p, True{}, False{}, h, mul(a, a))"))

# one side of e_(1+h) a times e_(1+k) a: gpf(mk(0, gx), mk(0, gy)) == mk(0, core)
def N.side.l0(+q: D.Qc, +gx: String, +gy: String) -> String:
  +z = N.z("p")
  D.gpf("1n+p", D.F(), D.F(), D.mk("p", z, gx), D.mk("p", z, gy), N.sigq(q))

def N.side.pf(+q: D.Qc, +gx: String, +gy: String) -> String:
  +sigq = N.sigq(q)
  +n3 = N.n3(q)
  +tt = D.Tr()
  +ff = D.F()
  +z = N.z("p")
  +nx = D.cat(["S.N{", z, ", ", gx, "}"])
  +l0 = N.side.l0(q, gx, gy)
  +l1 = D.gpf("1n+p", ff, ff, nx, D.mk("p", z, gy), sigq)
  +l2 = D.gpf("1n+p", ff, ff, nx, D.cat(["S.N{", z, ", ", gy, "}"]), sigq)
  +s1 = D.cat(["P.Gp.mk_l(", D.OPS(), ", p, ", ff, ", ", ff, ", ", z, ", ", gx, ", ", D.mk("p", z, gy), ", ", sigq, ")"])
  +s2 = D.cat(["P.Gp.mk_r(", D.OPS(), ", p, ", ff, ", ", ff, ", ", nx, ", ", z, ", ", gy, ", ", sigq, ")"])
  +e0 = N.lvl.e(z, gx, z, gy)
  +r0 = N.lvl.r(q, z, gx, z, gy)
  +ee = N.zz("p", N.G(ff, ff, z, gy), N.G(tt, ff, gx, z), N.zl("p", ff, ff, gy), N.zr("p", tt, ff, gx))
  +core = N.G(ff, ff, gx, gy)
  +er = D.pick(D.isz(q), "{==}", D.trans(D.mv("p"), r0, D.add("p", z, core), core,
    N.acong("p", N.G(tt, n3, z, z), z, core, core, N.zl("p", tt, n3, z), "{==}"),
    D.cat(["A.Add.zero_l(~T, ~add, p, ", core, ")"])))
  D.trans(D.mv("1n+p"), l0, l2, D.mk("p", z, core), D.trans(D.mv("1n+p"), l0, l1, l2, s1, s2), N.mcong("p", e0, z, r0, core, ee, er))

def N.achk(+q: D.Qc) -> String:
  +tt = D.Tr()
  +ff = D.F()
  +z = N.z("p")
  +gh = N.ge("p", "h", "a")
  +gk = N.ge("p", "k", "a")
  +l0 = N.side.l0(q, gh, gk)
  +i0 = N.side.l0(q, gk, gh)
  +cl = N.G(ff, ff, gh, gk)
  +cr = N.G(ff, ff, gk, gh)
  +ml = D.mk("p", z, cl)
  +mi = D.mk("p", z, cr)
  +scr = D.sgn("p", tt, ff, ff, cr)
  +mfin = D.mk("p", z, scr)
  +ih = D.cat(["Gen.ac(", D.OPS(), ", ~neg_neg, p, h, k, a, rest, ne)"])
  +lhs = D.trans(D.mv("1n+p"), l0, ml, mfin, N.side.pf(q, gh, gk), N.mcong("p", z, z, cl, scr, "{==}", ih))
  +r1 = D.cat(["G.Sgn.cong(~T, ~neg, 1n+p, ", tt, ", ", ff, ", ", ff, ", ", i0, ", ", mi, ", ", N.side.pf(q, gk, gh), ")"])
  +r2 = D.cat(["G.Sgn.mk(~T, ~neg, p, ", tt, ", ", ff, ", ", ff, ", ", z, ", ", cr, ")"])
  +s0 = D.sgn("p", tt, ff, ff, z)
  +r3 = N.mcong("p", s0, z, scr, scr, D.cat(["G.Sgn.zero(~T, ~neg, p, ", tt, ", ", ff, ", ", ff, ")"]), "{==}")
  +smi = D.sgn("1n+p", tt, ff, ff, mi)
  +rhs = D.trans(D.mv("1n+p"), D.sgn("1n+p", tt, ff, ff, i0), smi, mfin, r1,
    D.trans(D.mv("1n+p"), smi, D.mk("p", s0, scr), mfin, r2, r3))
  N.join(l0, D.sgn("1n+p", tt, ff, ff, i0), mfin, lhs, rhs)

def N.ac.goal(+d: String, +i: String, +j: String) -> String:
  +tt = D.Tr()
  +ff = D.F()
  D.cat(["{", D.gpf(d, ff, ff, N.ge(d, i, "a"), N.ge(d, j, "a"), "sig"), " == ", D.sgn(d, tt, ff, ff, D.gpf(d, ff, ff, N.ge(d, j, "a"), N.ge(d, i, "a"), "sig")), " : ", D.mv(d), "}"])

def N.part3() -> String:
  D.cat(["# distinct generators anticommute: e_i a e_j a = -(e_j a e_i a)
def Gen.ac(", D.OPSD(), ", ~neg_neg: R.Ring.NegNeg(T, neg), +d: Nat, +i: Nat, +j: Nat, +a: T, +sig: S.Sig(d),
  ne: {Nat.is_eq(i, j) == False{} : Bool})
  -> ", N.ac.goal("d", "i", "j"), ":
  match d:
    case 0n:
      {==}
    case 1n+p:
      match i:
        case 0n:
          match j:
            case 0n:
              B.Bool.tf(", N.ac.goal("1n+p", "0n", "0n"), ", ne)
            case 1n+k:
", D.qcases(N.ac0k(D.CZ{}), N.ac0k(D.CP{}), N.ac0k(D.CN{}), 14n), "
        case 1n+h:
          match j:
            case 0n:
", D.qcases(N.ach0(D.CZ{}), N.ach0(D.CP{}), N.ach0(D.CN{}), 14n), "
            case 1n+k:
", D.qcases(N.achk(D.CZ{}), N.achk(D.CP{}), N.achk(D.CN{}), 14n), "
"])

def N.text() -> String:
  D.cat([N.part1(), N.part2(), N.part3()])
