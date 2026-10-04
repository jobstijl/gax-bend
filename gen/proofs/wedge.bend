# Writes proofs/wedge.bend: the outer product as the geometric product of
# the zero metric, wedge and vee associativity, and the complements.

import Base
import ./dsl.bend as D

def W.wf(+d: String, +f: String, +n: String, +x: String, +y: String) -> String:
  D.cat(["S.MV.wedgef(", D.OPS(), ", ", d, ", ", f, ", ", n, ", ", x, ", ", y, ")"])

def W.wd(+d: String, +x: String, +y: String) -> String:
  D.cat(["S.MV.wedge(", D.OPS(), ", ", d, ", ", x, ", ", y, ")"])

def W.gp(+d: String, +s: String, +x: String, +y: String) -> String:
  D.cat(["S.MV.gp(", D.OPS(), ", ", d, ", ", s, ", ", x, ", ", y, ")"])

def W.rcf(+d: String, +n: String, +f: String, +x: String) -> String:
  D.cat(["S.MV.rcf(~T, ~neg, ", d, ", ", n, ", ", f, ", ", x, ")"])

def W.lcf(+d: String, +n: String, +f: String, +x: String) -> String:
  D.cat(["S.MV.lcf(~T, ~neg, ", d, ", ", n, ", ", f, ", ", x, ")"])

def W.rc(+d: String, +x: String) -> String:
  D.cat(["S.MV.rcomp(~T, ~neg, ", d, ", ", x, ")"])

def W.lc(+d: String, +x: String) -> String:
  D.cat(["S.MV.lcomp(~T, ~neg, ", d, ", ", x, ")"])

def W.vee(+d: String, +x: String, +y: String) -> String:
  D.cat(["S.MV.vee(", D.OPS(), ", ", d, ", ", x, ", ", y, ")"])

def W.h() -> String:
  "~add_assoc, ~add_comm, ~mul_assoc, ~dist_l, ~dist_r, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r"

def W.hd() -> String:
  "~add_assoc: R.Ring.Assoc(T, add), ~add_comm: R.Ring.Comm(T, add),
  ~mul_assoc: R.Ring.Assoc(T, mul), ~dist_l: R.Ring.DistL(T, add, mul), ~dist_r: R.Ring.DistR(T, add, mul),
  ~neg_add: R.Ring.NegAdd(T, add, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  ~neg_mul_l: R.Ring.NegMulL(T, mul, neg), ~neg_mul_r: R.Ring.NegMulR(T, mul, neg)"

def W.par(+d: String) -> String:
  "Comp.par(" ++ d ++ ")"

def W.band(+a: String, +b: String) -> String:
  D.cat(["Bool.and(", a, ", ", b, ")"])

# the parity sign of J_R after J_L
def W.hh(+d: String, +n: String, +f: String, +m: String, +g: String) -> String:
  D.xor(D.xor(n, m), W.band(W.par(d), D.xor(f, g)))

def W.flags() -> List<&2, D.Fl>:
  [ D.Fl{"lr_n", ["n", "f", "m", "g"], D.xor(D.xor("n", "f"), D.xor("m", "g")), D.xor(D.xor("n", "m"), D.xor("f", "g"))},
    D.Fl{"lr_f", ["f", "g"], D.xor(D.bnot("f"), D.bnot("g")), D.xor(D.xor("f", "g"), D.F())},
    D.Fl{"lr_xf", ["a", "b"], D.xor(D.xor("a", "b"), D.F()), D.xor("a", "b")},
    D.Fl{"rl_1", ["n", "f", "m", "g", "P"], D.xor(D.xor("n", "m"), W.band("P", D.xor(D.bnot("f"), D.bnot("g")))),
      D.xor(D.xor(D.xor("n", "m"), W.band(D.bnot("P"), D.xor("f", "g"))), D.xor("f", "g"))},
    D.Fl{"rl_2", ["n", "f", "m", "g", "P"], D.xor(D.xor(D.xor("n", "f"), D.xor("m", "g")), W.band("P", D.xor("f", "g"))),
      D.xor(D.xor("n", "m"), W.band(D.bnot("P"), D.xor("f", "g")))},
    D.Fl{"rl_0", ["n", "m", "b"], D.xor(D.xor("n", "m"), W.band(D.F(), "b")), D.xor("n", "m")},
    D.Fl{"and_f", ["b"], W.band("b", D.F()), D.F()} ]

def W.gp0() -> String:
  +nf = D.xor("n", "f")
  +z = {"S.Sig.zero(p)" : String}
  D.cat(["# Outer and regressive products, and the complements.

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S
import ./base.bend as B
import ./leaf.bend as L
import ./add.bend as A
import ./flags.bend as F
import ./sgn.bend as G
import ./gp.bend as P
import ./gp_assoc.bend as PA

# The outer product
# -----------------

# the outer product is the geometric product of the zero metric, flags and all
def Wedge.gp0(", D.OPSD(), ", +d: Nat, +f: Bool, +n: Bool, x: ", D.mv("d"), ", y: ", D.mv("d"), ")
  -> {", W.wf("d", "f", "n", "x", "y"), " == ", D.gpf("d", "f", "n", "x", "y", "S.Sig.zero(d)"), " : ", D.mv("d"), "}:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          {==}
        case S.L{a}:
          match y:
            case S.LZ{}:
              {==}
            case S.L{b}:
              {==}
    case 1n+p:
      match x:
        case S.NZ{}:
          {==}
        case S.N{+x1, +x2}:
          match y:
            case S.NZ{}:
              {==}
            case S.N{+y1, +y2}:
              P.Mk.cong(T, p,
                ", D.add("p", W.wf("p", "f", nf, "x1", "y2"), W.wf("p", D.bnot("f"), "n", "x2", "y1")), ",
                ", D.add("p", D.gpf("p", "f", nf, "x1", "y2", z), D.gpf("p", D.bnot("f"), "n", "x2", "y1", z)), ",
                ", W.wf("p", "f", "n", "x2", "y2"), ", ", D.gpf("p", "f", "n", "x2", "y2", z), ",
                A.Add.cong(~T, ~add, p, ", W.wf("p", "f", nf, "x1", "y2"), ", ", D.gpf("p", "f", nf, "x1", "y2", z), ",
                  ", W.wf("p", D.bnot("f"), "n", "x2", "y1"), ", ", D.gpf("p", D.bnot("f"), "n", "x2", "y1", z), ",
                  Wedge.gp0(", D.OPS(), ", p, f, ", nf, ", x1, y2), Wedge.gp0(", D.OPS(), ", p, ", D.bnot("f"), ", n, x2, y1)),
                Wedge.gp0(", D.OPS(), ", p, f, n, x2, y2))
"])

def W.w0(+x: String, +y: String) -> String:
  D.cat(["Wedge.gp0(", D.OPS(), ", d, False{}, False{}, ", x, ", ", y, ")"])

def W.gcong(+x: String, +x2: String, +y: String, +y2: String, +ex: String, +ey: String) -> String:
  D.cat(["P.Gp.cong(", D.OPS(), ", d, False{}, False{}, ", x, ", ", x2, ", ", y, ", ", y2, ", S.Sig.zero(d), ", ex, ", ", ey, ")"])

def W.assoc() -> String:
  +mv = D.mv("d")
  +z0 = {"S.Sig.zero(d)" : String}
  +wxy = W.wd("d", "x", "y")
  +wyz = W.wd("d", "y", "z")
  +a1 = W.wd("d", wxy, "z")
  +a2 = W.gp("d", z0, wxy, "z")
  +a3 = W.gp("d", z0, W.gp("d", z0, "x", "y"), "z")
  +a4 = W.gp("d", z0, "x", W.gp("d", z0, "y", "z"))
  +a5 = W.gp("d", z0, "x", wyz)
  +a6 = W.wd("d", "x", wyz)
  +s1 = W.w0(wxy, "z")
  +s2 = W.gcong(wxy, W.gp("d", z0, "x", "y"), "z", "z", W.w0("x", "y"), "{==}")
  +s3 = D.cat(["PA.Gp.assoc(", D.OPS(), ", ", W.h(), ", d, False{}, False{}, False{}, False{}, x, y, z, ", z0, ")"])
  +s4 = W.gcong("x", "x", W.gp("d", z0, "y", "z"), wyz, "{==}", D.sym(mv, wyz, W.gp("d", z0, "y", "z"), W.w0("y", "z")))
  +s5 = D.sym(mv, a6, a5, W.w0("x", wyz))
  +chain = D.trans(mv, a1, a5, a6, D.trans(mv, a1, a4, a5, D.trans(mv, a1, a3, a4, D.trans(mv, a1, a2, a3, s1, s2), s3), s4), s5)
  D.cat(["# the outer product is associative: it is the geometric product of the
# zero metric, which is associative
def Wedge.assoc(", D.OPSD(), ", ", W.hd(), ",
  +d: Nat, +x: ", mv, ", +y: ", mv, ", +z: ", mv, ")
  -> {", a1, " == ", a6, " : ", mv, "}:
  ", D.ind(chain, 2n), "
"])

def W.lr.node() -> String:
  +fg = D.xor("f", "g")
  +nm = D.xor("n", "m")
  +a1 = W.lcf("p", D.xor("n", "f"), "f", W.rcf("p", D.xor("m", "g"), "g", "x1"))
  +a2 = W.lcf("p", "n", D.bnot("f"), W.rcf("p", "m", D.bnot("g"), "x2"))
  +i1 = D.sgn("p", D.xor(D.xor("n", "f"), D.xor("m", "g")), fg, D.F(), "x1")
  +i2 = D.sgn("p", nm, D.xor(D.bnot("f"), D.bnot("g")), D.F(), "x2")
  +r1 = D.sgn("p", D.xor(nm, fg), D.xor(fg, D.F()), D.F(), "x1")
  +r2 = D.sgn("p", nm, fg, D.F(), "x2")
  +e1 = D.trans(D.mv("p"), a1, i1, r1, D.cat(["Comp.lr(~T, ~neg, ~neg_neg, p, ", D.xor("n", "f"), ", f, ", D.xor("m", "g"), ", g, x1)"]),
    D.cat(["G.Sgn.flag(~T, ~neg, p, ", D.xor(D.xor("n", "f"), D.xor("m", "g")), ", ", D.xor(nm, fg), ", ", fg, ", ", D.xor(fg, D.F()), ", ", D.F(), ", x1, ",
      D.flag.call("lr_n", ["n", "f", "m", "g"]), ", ", D.sym("Bool", D.xor(fg, D.F()), fg, D.flag.call("lr_xf", ["f", "g"])), ")"]))
  +e2 = D.trans(D.mv("p"), a2, i2, r2, D.cat(["Comp.lr(~T, ~neg, ~neg_neg, p, n, ", D.bnot("f"), ", m, ", D.bnot("g"), ", x2)"]),
    D.cat(["G.Sgn.flag(~T, ~neg, p, ", nm, ", ", nm, ", ", D.xor(D.bnot("f"), D.bnot("g")), ", ", fg, ", ", D.F(), ", x2, {==}, Equal.trans(Bool, ",
      D.xor(D.bnot("f"), D.bnot("g")), ", ", D.xor(fg, D.F()), ", ", fg, ", ", D.flag.call("lr_f", ["f", "g"]), ", ", D.flag.call("lr_xf", ["f", "g"]), "))"]))
  D.cat(["B.Node.cong2(", D.mv("p"), ", ", a1, ", ", r1, ", ", a2, ", ", r2, ",\n  ", D.ind(e1, 2n), ",\n  ", D.ind(e2, 2n), ")"])

def W.rl.node() -> String:
  +fg = D.xor("f", "g")
  +a1 = W.rcf("p", "n", D.bnot("f"), W.lcf("p", "m", D.bnot("g"), "x1"))
  +a2 = W.rcf("p", D.xor("n", "f"), "f", W.lcf("p", D.xor("m", "g"), "g", "x2"))
  +h1 = W.hh("p", "n", D.bnot("f"), "m", D.bnot("g"))
  +h2 = W.hh("p", D.xor("n", "f"), "f", D.xor("m", "g"), "g")
  +i1 = D.sgn("p", h1, D.xor(D.bnot("f"), D.bnot("g")), D.F(), "x1")
  +i2 = D.sgn("p", h2, fg, D.F(), "x2")
  +hd = W.hh("1n+p", "n", "f", "m", "g")
  +r1 = D.sgn("p", D.xor(hd, fg), D.xor(fg, D.F()), D.F(), "x1")
  +r2 = D.sgn("p", hd, fg, D.F(), "x2")
  +e1 = D.trans(D.mv("p"), a1, i1, r1, D.cat(["Comp.rl(~T, ~neg, ~neg_neg, p, n, ", D.bnot("f"), ", m, ", D.bnot("g"), ", x1)"]),
    D.cat(["G.Sgn.flag(~T, ~neg, p, ", h1, ", ", D.xor(hd, fg), ", ", D.xor(D.bnot("f"), D.bnot("g")), ", ", D.xor(fg, D.F()), ", ", D.F(), ", x1, ",
      D.flag.call("rl_1", ["n", "f", "m", "g", W.par("p")]), ", ", D.flag.call("lr_f", ["f", "g"]), ")"]))
  +e2 = D.trans(D.mv("p"), a2, i2, r2, D.cat(["Comp.rl(~T, ~neg, ~neg_neg, p, ", D.xor("n", "f"), ", f, ", D.xor("m", "g"), ", g, x2)"]),
    D.cat(["G.Sgn.flag(~T, ~neg, p, ", h2, ", ", hd, ", ", fg, ", ", fg, ", ", D.F(), ", x2, ", D.flag.call("rl_2", ["n", "f", "m", "g", W.par("p")]), ", {==})"]))
  D.cat(["B.Node.cong2(", D.mv("p"), ", ", a1, ", ", r1, ", ", a2, ", ", r2, ",\n  ", D.ind(e1, 2n), ",\n  ", D.ind(e2, 2n), ")"])

def W.comp() -> String:
  +mvd = D.mv("d")
  +h0 = W.hh("0n", "n", "f", "m", "g")
  D.sep([D.cat(["# The complements
# ---------------

# J_L after J_R, with their flags: lcf(n, f, rcf(m, g, x)) is the grade sign
# (n xor m, f xor g)
def Comp.lr(~T: Data, ~neg: T -> T, ~neg_neg: R.Ring.NegNeg(T, neg), +d: Nat, +n: Bool, +f: Bool, +m: Bool, +g: Bool, x: ", mvd, ")
  -> {", W.lcf("d", "n", "f", W.rcf("d", "m", "g", "x")), " == ", D.sgn("d", D.xor("n", "m"), D.xor("f", "g"), D.F(), "x"), " : ", mvd, "}:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          {==}
        case S.L{a}:
          B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, S.Ring.negf(~T, ~neg, m, a)), S.Ring.negf(~T, ~neg, ", D.xor("n", "m"), ", a),
            L.Negf.negf(~T, ~neg, ~neg_neg, n, m, a))
    case 1n+p:
      match x:
        case S.NZ{}:
          {==}
        case S.N{x1, x2}:
", D.ind(W.lr.node(), 10n), "
"]), D.cat(["# the parity of d
def Comp.par(d: Nat) -> Bool:
  match d:
    case 0n:
      False{}
    case 1n+p:
      Bool.not(Comp.par(p))

# J_R after J_L, with their flags: the involution between them does not
# cancel, so the sign picks up the parity of d when f xor g
def Comp.rl(~T: Data, ~neg: T -> T, ~neg_neg: R.Ring.NegNeg(T, neg), +d: Nat, +n: Bool, +f: Bool, +m: Bool, +g: Bool, x: ", mvd, ")
  -> {", W.rcf("d", "n", "f", W.lcf("d", "m", "g", "x")), " == ", D.sgn("d", W.hh("d", "n", "f", "m", "g"), D.xor("f", "g"), D.F(), "x"), " : ", mvd, "}:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          {==}
        case S.L{+a}:
          B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, S.Ring.negf(~T, ~neg, m, a)), S.Ring.negf(~T, ~neg, ", h0, ", a),
            Equal.trans(T, S.Ring.negf(~T, ~neg, n, S.Ring.negf(~T, ~neg, m, a)), S.Ring.negf(~T, ~neg, ", D.xor("n", "m"), ", a),
              S.Ring.negf(~T, ~neg, ", h0, ", a),
              L.Negf.negf(~T, ~neg, ~neg_neg, n, m, a),
              L.Negf.flag(~T, ~neg, ", D.xor("n", "m"), ", ", h0, ", a,
                ", D.sym("Bool", h0, D.xor("n", "m"), D.flag.call("rl_0", ["n", "m", D.xor("f", "g")])), ")))
    case 1n+p:
      match x:
        case S.NZ{}:
          {==}
        case S.N{x1, x2}:
", D.ind(W.rl.node(), 10n), "
"])], "\n")

def W.cor() -> String:
  +mvd = D.mv("d")
  +b0 = W.band(W.par("d"), D.F())
  D.cat(["def Comp.lcomp_rcomp(~T: Data, ~neg: T -> T, ~neg_neg: R.Ring.NegNeg(T, neg), +d: Nat, +x: ", mvd, ")
  -> {", W.lc("d", W.rc("d", "x")), " == x : ", mvd, "}:
  Equal.trans(", mvd, ", ", W.lc("d", W.rc("d", "x")), ", ", D.sgn("d", D.F(), D.F(), D.F(), "x"), ", x,
    Comp.lr(~T, ~neg, ~neg_neg, d, ", D.F(), ", ", D.F(), ", ", D.F(), ", ", D.F(), ", x), G.Sgn.id(~T, ~neg, d, x))

def Comp.rcomp_lcomp(~T: Data, ~neg: T -> T, ~neg_neg: R.Ring.NegNeg(T, neg), +d: Nat, +x: ", mvd, ")
  -> {", W.rc("d", W.lc("d", "x")), " == x : ", mvd, "}:
  Equal.trans(", mvd, ", ", W.rc("d", W.lc("d", "x")), ", ", D.sgn("d", b0, D.F(), D.F(), "x"), ", x,
    Comp.rl(~T, ~neg, ~neg_neg, d, ", D.F(), ", ", D.F(), ", ", D.F(), ", ", D.F(), ", x),
    Equal.trans(", mvd, ", ", D.sgn("d", b0, D.F(), D.F(), "x"), ", ", D.sgn("d", D.F(), D.F(), D.F(), "x"), ", x,
      G.Sgn.flag(~T, ~neg, d, ", b0, ", ", D.F(), ", ", D.F(), ", ", D.F(), ", ", D.F(), ", x, ", D.flag.call("and_f", [W.par("d")]), ", {==}),
      G.Sgn.id(~T, ~neg, d, x)))

# the right complement of a regressive product is the outer product of the
# right complements
def Comp.rcomp_vee(", D.OPSD(), ", ~neg_neg: R.Ring.NegNeg(T, neg), +d: Nat, +x: ", mvd, ", +y: ", mvd, ")
  -> {", W.rc("d", W.vee("d", "x", "y")), " == ", W.wd("d", W.rc("d", "x"), W.rc("d", "y")), " : ", mvd, "}:
  Comp.rcomp_lcomp(~T, ~neg, ~neg_neg, d, ", W.wd("d", W.rc("d", "x"), W.rc("d", "y")), ")
"])

def W.rv(+x: String, +y: String) -> String:
  D.cat(["Comp.rcomp_vee(", D.OPS(), ", ~neg_neg, d, ", x, ", ", y, ")"])

def W.lcong(+a: String, +b: String, +e: String) -> String:
  D.cat(["Equal.cong(", D.mv("d"), ", ", D.mv("d"), ", w => ", W.lc("d", "w"), ", ", a, ", ", b, ", ", e, ")"])

def W.wcong(+x: String, +x2: String, +y: String, +y2: String, +ex: String, +ey: String) -> String:
  D.cat(["B.Eq.cong2(", D.mv("d"), ", ", D.mv("d"), ", ", D.mv("d"), ", u => v => ", W.wd("d", "u", "v"), ", ", x, ", ", x2, ", ", y, ", ", y2, ", ", ex, ", ", ey, ")"])

def W.vee.assoc() -> String:
  +rx = W.rc("d", "x")
  +ry = W.rc("d", "y")
  +rz = W.rc("d", "z")
  +vxy = W.vee("d", "x", "y")
  +vyz = W.vee("d", "y", "z")
  +b1 = W.lc("d", W.wd("d", W.rc("d", vxy), rz))
  +b2 = W.lc("d", W.wd("d", W.wd("d", rx, ry), rz))
  +b3 = W.lc("d", W.wd("d", rx, W.wd("d", ry, rz)))
  +b4 = W.lc("d", W.wd("d", rx, W.rc("d", vyz)))
  +t1 = W.lcong(W.wd("d", W.rc("d", vxy), rz), W.wd("d", W.wd("d", rx, ry), rz), W.wcong(W.rc("d", vxy), W.wd("d", rx, ry), rz, rz, W.rv("x", "y"), "{==}"))
  +t2 = W.lcong(W.wd("d", W.wd("d", rx, ry), rz), W.wd("d", rx, W.wd("d", ry, rz)), D.cat(["Wedge.assoc(", D.OPS(), ", ", W.h(), ", d, ", rx, ", ", ry, ", ", rz, ")"]))
  +t3 = W.lcong(W.wd("d", rx, W.wd("d", ry, rz)), W.wd("d", rx, W.rc("d", vyz)),
    W.wcong(rx, rx, W.wd("d", ry, rz), W.rc("d", vyz), "{==}", D.sym(D.mv("d"), W.rc("d", vyz), W.wd("d", ry, rz), W.rv("y", "z"))))
  +chain = D.trans(D.mv("d"), b1, b3, b4, D.trans(D.mv("d"), b1, b2, b3, t1, t2), t3)
  D.cat(["# the regressive product is associative
def Vee.assoc(", D.OPSD(), ", ", W.hd(), ",
  +d: Nat, +x: ", D.mv("d"), ", +y: ", D.mv("d"), ", +z: ", D.mv("d"), ")
  -> {", W.vee("d", vxy, "z"), " == ", W.vee("d", "x", vyz), " : ", D.mv("d"), "}:
  ", D.ind(chain, 2n), "
"])

def W.text() -> String:
  D.sep([W.gp0(), W.assoc(), W.comp(), W.cor(), W.vee.assoc()], "\n")
