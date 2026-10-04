# Writes proofs/gp.bend: congruence, zero, the collapsing constructor,
# distributivity, and the sign lemmas of the geometric product.

import Base
import ./dsl.bend as D

# Part 1: congruence, zero, MV.mk
# -------------------------------

def G1.header() -> String:
  "# The geometric product, part 1: congruence, zero, the collapsing
# constructor, and distributivity over addition on both sides.

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S
import ./base.bend as B
import ./leaf.bend as L
import ./add.bend as A
import ./flags.bend as F
import ./sgn.bend as G
"

def G1.cong() -> String:
  +mvd = D.mv("d")
  +mv1 = D.mv("1n+d")
  +g0 = D.gpf("d", "f", "n", "x", "y", "sig")
  D.cat(["# Congruence
# ----------

def Mk.cong(-T: Data, -d: Nat, -e: ", mvd, ", -e2: ", mvd, ", -r: ", mvd, ", -r2: ", mvd, ",
  ee: {e == e2 : ", mvd, "}, er: {r == r2 : ", mvd, "})
  -> {", D.mk("d", "e", "r"), " == ", D.mk("d", "e2", "r2"), " : ", mv1, "}:
  %ee : {", D.mk("d", "e", "r"), " == ", D.mk("d", "_", "r2"), " : ", mv1, "}
  %er : {", D.mk("d", "e", "r"), " == ", D.mk("d", "e", "_"), " : ", mv1, "}
  {==}

def Gp.flag(", D.OPSD(), ", -d: Nat, -f: Bool, -f2: Bool, -n: Bool, -n2: Bool,
  -x: ", mvd, ", -y: ", mvd, ", -sig: S.Sig(d), ef: {f == f2 : Bool}, en: {n == n2 : Bool})
  -> {", g0, " == ", D.gpf("d", "f2", "n2", "x", "y", "sig"), " : ", mvd, "}:
  %ef : {", g0, " == ", D.gpf("d", "_", "n2", "x", "y", "sig"), " : ", mvd, "}
  %en : {", g0, " == ", D.gpf("d", "f", "_", "x", "y", "sig"), " : ", mvd, "}
  {==}

def Gp.cong(", D.OPSD(), ", -d: Nat, -f: Bool, -n: Bool, -x: ", mvd, ", -x2: ", mvd, ",
  -y: ", mvd, ", -y2: ", mvd, ", -sig: S.Sig(d), ex: {x == x2 : ", mvd, "}, ey: {y == y2 : ", mvd, "})
  -> {", g0, " == ", D.gpf("d", "f", "n", "x2", "y2", "sig"), " : ", mvd, "}:
  %ex : {", g0, " == ", D.gpf("d", "f", "n", "_", "y2", "sig"), " : ", mvd, "}
  %ey : {", g0, " == ", D.gpf("d", "f", "n", "x", "_", "sig"), " : ", mvd, "}
  {==}
"])

def G1.zero() -> String:
  +mvd = D.mv("d")
  D.cat(["# Zero
# ----

def Gp.zero_r(", D.OPSD(), ", d: Nat, f: Bool, n: Bool, x: ", mvd, ", sig: S.Sig(d))
  -> {", D.gpf("d", "f", "n", "x", "S.MV.zero(T, d)", "sig"), " == S.MV.zero(T, d) : ", mvd, "}:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          {==}
        case S.L{a}:
          {==}
    case 1n+p:
      match x:
        case S.NZ{}:
          {==}
        case S.N{x1, x2}:
          {==}

def Gp.zero_l(", D.OPSD(), ", d: Nat, f: Bool, n: Bool, y: ", mvd, ", sig: S.Sig(d))
  -> {", D.gpf("d", "f", "n", "S.MV.zero(T, d)", "y", "sig"), " == S.MV.zero(T, d) : ", mvd, "}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}
"])

def G1.mk_l() -> String:
  +mvp = D.mv("p")
  +mv1 = D.mv("1n+p")
  +refl = D.qcases("{==}", "{==}", "{==}", 18n)
  D.cat(["# The collapsing constructor
# --------------------------

# a product does not see whether its left operand came through MV.mk
def Gp.mk_l(", D.OPSD(), ", +p: Nat, +f: Bool, +n: Bool, a: ", mvp, ", b: ", mvp, ", y: ", mv1, ", sig: S.Sig(1n+p))
  -> {", D.gpf("1n+p", "f", "n", D.mk("p", "a", "b"), "y", "sig"), " == ", D.gpf("1n+p", "f", "n", "S.N{a, b}", "y", "sig"), " : ", mv1, "}:
  match p:
    case 0n:
      match a:
        case S.LZ{}:
          match b:
            case S.LZ{}:
              match y:
                case S.NZ{}:
                  {==}
                case S.N{y1, y2}:
", refl, "
            case S.L{w}:
              {==}
        case S.L{v}:
          {==}
    case 1n+o:
      match a:
        case S.NZ{}:
          match b:
            case S.NZ{}:
              match y:
                case S.NZ{}:
                  {==}
                case S.N{y1, y2}:
", refl, "
            case S.N{b1, b2}:
              {==}
        case S.N{a1, a2}:
          {==}
"])

# one metric case of Gp.zero_lvl: every product with a zero operand is zero
def G1.zlvl(+p: String, +z: String, +q: D.Qc) -> String:
  +nf = D.xor("n", "f")
  +g1 = D.gpf(p, "f", nf, "x1", z, "rest")
  +g2 = D.gpf(p, D.bnot("f"), "n", "x2", z, "rest")
  +g4 = D.gpf(p, "f", "n", "x2", z, "rest")
  +z4 = D.cat(["Gp.zero_r(", D.OPS(), ", ", p, ", f, n, x2, rest)"])
  +e = D.add(p, g1, g2)
  +ee = D.cat(["A.Add.cong(~T, ~add, ", p, ", ", g1, ", ", z, ", ", g2, ", ", z, ", ",
    D.cat(["Gp.zero_r(", D.OPS(), ", ", p, ", f, ", nf, ", x1, rest)"]), ", ",
    D.cat(["Gp.zero_r(", D.OPS(), ", ", p, ", ", D.bnot("f"), ", n, x2, rest)"]), ")"])
  +nf3 = D.byq(q, nf, nf, D.bnot(nf))
  +g3 = D.gpf(p, D.bnot("f"), nf3, "x1", z, "rest")
  +z3 = D.cat(["Gp.zero_r(", D.OPS(), ", ", p, ", ", D.bnot("f"), ", ", nf3, ", x1, rest)"])
  +isz = D.isz(q)
  D.cat(["Mk.cong(T, ", p, ", ", e, ", ", D.add(p, z, z), ", ",
    D.pick(isz, g4, D.add(p, g3, g4)), ", ", D.pick(isz, z, D.add(p, z, z)), ",\n  ", ee, ",\n  ",
    D.pick(isz, z4, D.cat(["A.Add.cong(~T, ~add, ", p, ", ", g3, ", ", z, ", ", g4, ", ", z, ", ", z3, ", ", z4, ")"])), ")"])

def G1.zero_lvl() -> String:
  +mvp = D.mv("p")
  +mv1 = D.mv("1n+p")
  D.cat(["# a product with a right operand N{zero, zero} is zero
def Gp.zero_lvl(", D.OPSD(), ", +p: Nat, +f: Bool, +n: Bool, +x1: ", mvp, ", +x2: ", mvp, ", sig: S.Sig(1n+p))
  -> {", D.gpf("1n+p", "f", "n", "S.N{x1, x2}", "S.N{S.MV.zero(T, p), S.MV.zero(T, p)}", "sig"), " == S.NZ{} : ", mv1, "}:
  match p:
    case 0n:
", D.qcases(G1.zlvl("0n", "S.LZ{}", D.CZ{}), G1.zlvl("0n", "S.LZ{}", D.CP{}), G1.zlvl("0n", "S.LZ{}", D.CN{}), 6n), "
    case 1n+o:
", D.qcases(G1.zlvl("1n+o", "S.NZ{}", D.CZ{}), G1.zlvl("1n+o", "S.NZ{}", D.CP{}), G1.zlvl("1n+o", "S.NZ{}", D.CN{}), 6n), "
"])

def G1.mk_r() -> String:
  +mvp = D.mv("p")
  +mv1 = D.mv("1n+p")
  D.cat(["# a product does not see whether its right operand came through MV.mk
def Gp.mk_r(", D.OPSD(), ", +p: Nat, +f: Bool, +n: Bool, x: ", mv1, ", a: ", mvp, ", b: ", mvp, ", +sig: S.Sig(1n+p))
  -> {", D.gpf("1n+p", "f", "n", "x", D.mk("p", "a", "b"), "sig"), " == ", D.gpf("1n+p", "f", "n", "x", "S.N{a, b}", "sig"), " : ", mv1, "}:
  match p:
    case 0n:
      match x:
        case S.NZ{}:
          {==}
        case S.N{x1, x2}:
          match a:
            case S.LZ{}:
              match b:
                case S.LZ{}:
                  Equal.sym(", D.mv("1n"), ", ", D.gpf("1n", "f", "n", "S.N{x1, x2}", "S.N{S.LZ{}, S.LZ{}}", "sig"), ", S.NZ{},
                    Gp.zero_lvl(", D.OPS(), ", 0n, f, n, x1, x2, sig))
                case S.L{w}:
                  {==}
            case S.L{v}:
              {==}
    case 1n+o:
      match x:
        case S.NZ{}:
          {==}
        case S.N{x1, x2}:
          match a:
            case S.NZ{}:
              match b:
                case S.NZ{}:
                  Equal.sym(", D.mv("2n+o"), ", ", D.gpf("2n+o", "f", "n", "S.N{x1, x2}", "S.N{S.NZ{}, S.NZ{}}", "sig"), ", S.NZ{},
                    Gp.zero_lvl(", D.OPS(), ", 1n+o, f, n, x1, x2, sig))
                case S.N{b1, b2}:
                  {==}
            case S.N{a1, a2}:
              {==}
"])

def G1.text() -> String:
  D.sep([G1.header(), G1.cong(), G1.zero(), G1.mk_l(), G1.zero_lvl(), G1.mk_r()], "\n")

# Part 2: distributivity
# ----------------------

# a term (f flag, n flag, left, right) of a level: on the left side the
# summed operand is the left one (indices 1/2 on a and b), on the right
# side the right one
type T4 is Data:
  T4{f: String, n: String, u: String, v: String}

def G2.term(+left: Bool, +t: T4, +w: String) -> String:
  match t:
    case T4{+f, +n, +u, +v}:
      D.pick(left, D.gpf("p", f, n, w ++ u, v, "rest"), D.gpf("p", f, n, u, w ++ v, "rest"))

def G2.sum(+left: Bool, +t: T4) -> String:
  match t:
    case T4{+f, +n, +u, +v}:
      D.pick(left, D.gpf("p", f, n, D.add("p", "a" ++ u, "b" ++ u), v, "rest"),
        D.gpf("p", f, n, u, D.add("p", "a" ++ v, "b" ++ v), "rest"))

def G2.ih(+left: Bool, +h: String, +rec: String, +t: T4) -> String:
  match t:
    case T4{+f, +n, +u, +v}:
      D.pick(left, D.cat([rec, "(", h, ", p, ", f, ", ", n, ", a", u, ", b", u, ", ", v, ", rest)"]),
        D.cat([rec, "(", h, ", p, ", f, ", ", n, ", ", u, ", a", v, ", b", v, ", rest)"]))

def G2.level(+left: Bool, +h: String, +rec: String, +q: D.Qc) -> String:
  +nf = D.xor("n", "f")
  +nf3 = D.byq(q, nf, nf, D.bnot(nf))
  +t1 = D.pick(left, "1", "x1")
  +t2 = D.pick(left, "2", "x2")
  +r1 = D.pick(left, "z2", "2")
  +r2 = D.pick(left, "z1", "1")
  +a1 = {T4{"f", nf, t1, r1} : T4}
  +a2 = {T4{D.bnot("f"), "n", t2, r2} : T4}
  +a3 = {T4{D.bnot("f"), nf3, t1, r2} : T4}
  +a4 = {T4{"f", "n", t2, r1} : T4}
  +mv = D.mv("p")
  +lets = D.sep([
    "+pa1 = " ++ G2.term(left, a1, "a"), "+pb1 = " ++ G2.term(left, a1, "b"),
    "+pa2 = " ++ G2.term(left, a2, "a"), "+pb2 = " ++ G2.term(left, a2, "b"),
    "+pa3 = " ++ G2.term(left, a3, "a"), "+pb3 = " ++ G2.term(left, a3, "b"),
    "+pa4 = " ++ G2.term(left, a4, "a"), "+pb4 = " ++ G2.term(left, a4, "b")], "\n") ++ "\n"
  +s1 = G2.sum(left, a1)
  +s2 = G2.sum(left, a2)
  +s3 = G2.sum(left, a3)
  +s4 = G2.sum(left, a4)
  +el = D.add("p", s1, s2)
  +ea = D.add("p", "pa1", "pa2")
  +eb = D.add("p", "pb1", "pb2")
  +efin = D.add("p", ea, eb)
  +ee = D.trans0(mv, el, D.add("p", D.add("p", "pa1", "pb1"), D.add("p", "pa2", "pb2")), efin,
    D.cat(["A.Add.cong(~T, ~add, p, ", s1, ", ", D.add("p", "pa1", "pb1"), ", ", s2, ", ", D.add("p", "pa2", "pb2"), ", ",
      G2.ih(left, h, rec, a1), ", ", G2.ih(left, h, rec, a2), ")"]),
    "A.Add.swap4(~T, ~add, ~add_assoc, ~add_comm, p, pa1, pb1, pa2, pb2)")
  +isz = D.isz(q)
  +ra = D.pick(isz, "pa4", D.add("p", "pa3", "pa4"))
  +rb = D.pick(isz, "pb4", D.add("p", "pb3", "pb4"))
  +rl = D.pick(isz, s4, D.add("p", s3, s4))
  +rfin = D.add("p", ra, rb)
  +er = D.pick(isz, G2.ih(left, h, rec, a4),
    D.trans0(mv, rl, D.add("p", D.add("p", "pa3", "pb3"), D.add("p", "pa4", "pb4")), rfin,
      D.cat(["A.Add.cong(~T, ~add, p, ", s3, ", ", D.add("p", "pa3", "pb3"), ", ", s4, ", ", D.add("p", "pa4", "pb4"), ", ",
        G2.ih(left, h, rec, a3), ", ", G2.ih(left, h, rec, a4), ")"]),
      "A.Add.swap4(~T, ~add, ~add_assoc, ~add_comm, p, pa3, pb3, pa4, pb4)"))
  +mv1 = D.mv("1n+p")
  +mid = D.mk("p", efin, rfin)
  +right = D.add("1n+p", D.mk("p", ea, ra), D.mk("p", eb, rb))
  +step1 = D.cat(["Mk.cong(T, p, ", el, ", ", efin, ", ", rl, ", ", rfin, ",\n  ", D.ind(ee, 2n), ",\n  ", D.ind(er, 2n), ")"])
  +step2 = D.sym0(mv1, right, mid, D.cat(["A.Add.mk(~T, ~add, p, ", ea, ", ", ra, ", ", eb, ", ", rb, ")"]))
  D.app(lets, D.trans0(mv1, D.mk("p", el, rl), mid, right, D.ind(step1, 2n), D.ind(step2, 2n)))

def G2.levels(+left: Bool, +h: String, +rec: String) -> String:
  D.qcases(G2.level(left, h, rec, D.CZ{}), G2.level(left, h, rec, D.CP{}), G2.level(left, h, rec, D.CN{}), 18n)

def G2.text() -> String:
  +mvd = D.mv("d")
  +mv1 = D.mv("1n+p")
  +hl = {"~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_r, ~neg_add" : String}
  +hr = {"~T, ~add, ~mul, ~neg, ~add_assoc, ~add_comm, ~dist_l, ~neg_add" : String}
  +gl = D.gpf("1n+p", "f", "n", "S.N{a1, a2}", "z", "sig")
  +gr = D.gpf("1n+p", "f", "n", "S.N{x1, x2}", "S.N{a1, a2}", "sig")
  D.sep([D.cat(["# Distributivity
# --------------

# (-1)^n * inv^f(a + b) * z = (-1)^n * inv^f(a) * z + (-1)^n * inv^f(b) * z
def Gp.add_l(", D.OPSD(), ", ~add_assoc: R.Ring.Assoc(T, add), ~add_comm: R.Ring.Comm(T, add),
  ~dist_r: R.Ring.DistR(T, add, mul), ~neg_add: R.Ring.NegAdd(T, add, neg),
  +d: Nat, +f: Bool, +n: Bool, a: ", mvd, ", b: ", mvd, ", z: ", mvd, ", +sig: S.Sig(d))
  -> {", D.gpf("d", "f", "n", D.add("d", "a", "b"), "z", "sig"), " == ", D.add("d", D.gpf("d", "f", "n", "a", "z", "sig"), D.gpf("d", "f", "n", "b", "z", "sig")), " : ", mvd, "}:
  match d:
    case 0n:
      match a:
        case S.LZ{}:
          {==}
        case S.L{+x}:
          match b:
            case S.LZ{}:
              match z:
                case S.LZ{}:
                  {==}
                case S.L{c}:
                  {==}
            case S.L{+y}:
              match z:
                case S.LZ{}:
                  {==}
                case S.L{+c}:
                  B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, mul(add(x, y), c)),
                    add(S.Ring.negf(~T, ~neg, n, mul(x, c)), S.Ring.negf(~T, ~neg, n, mul(y, c))),
                    Equal.trans(T, S.Ring.negf(~T, ~neg, n, mul(add(x, y), c)),
                      S.Ring.negf(~T, ~neg, n, add(mul(x, c), mul(y, c))),
                      add(S.Ring.negf(~T, ~neg, n, mul(x, c)), S.Ring.negf(~T, ~neg, n, mul(y, c))),
                      Equal.cong(T, T, w => S.Ring.negf(~T, ~neg, n, w), mul(add(x, y), c), add(mul(x, c), mul(y, c)), dist_r(x, y, c)),
                      L.Negf.add(~T, ~add, ~neg, ~neg_add, n, mul(x, c), mul(y, c))))
    case 1n+p:
      match a:
        case S.NZ{}:
          {==}
        case S.N{+a1, +a2}:
          match b:
            case S.NZ{}:
              Equal.sym(", mv1, ", ", D.add("1n+p", gl, "S.NZ{}"), ", ", gl, ",
                A.Add.zero_r(~T, ~add, 1n+p, ", gl, "))
            case S.N{+b1, +b2}:
              match z:
                case S.NZ{}:
                  {==}
                case S.N{+z1, +z2}:
", G2.levels(True{}, hl, "Gp.add_l"), "
"]), D.cat(["# (-1)^n * inv^f(x) * (a + b) = (-1)^n * inv^f(x) * a + (-1)^n * inv^f(x) * b
def Gp.add_r(", D.OPSD(), ", ~add_assoc: R.Ring.Assoc(T, add), ~add_comm: R.Ring.Comm(T, add),
  ~dist_l: R.Ring.DistL(T, add, mul), ~neg_add: R.Ring.NegAdd(T, add, neg),
  +d: Nat, +f: Bool, +n: Bool, x: ", mvd, ", a: ", mvd, ", b: ", mvd, ", +sig: S.Sig(d))
  -> {", D.gpf("d", "f", "n", "x", D.add("d", "a", "b"), "sig"), " == ", D.add("d", D.gpf("d", "f", "n", "x", "a", "sig"), D.gpf("d", "f", "n", "x", "b", "sig")), " : ", mvd, "}:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          {==}
        case S.L{+c}:
          match a:
            case S.LZ{}:
              {==}
            case S.L{+y}:
              match b:
                case S.LZ{}:
                  {==}
                case S.L{+w}:
                  B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, mul(c, add(y, w))),
                    add(S.Ring.negf(~T, ~neg, n, mul(c, y)), S.Ring.negf(~T, ~neg, n, mul(c, w))),
                    Equal.trans(T, S.Ring.negf(~T, ~neg, n, mul(c, add(y, w))),
                      S.Ring.negf(~T, ~neg, n, add(mul(c, y), mul(c, w))),
                      add(S.Ring.negf(~T, ~neg, n, mul(c, y)), S.Ring.negf(~T, ~neg, n, mul(c, w))),
                      Equal.cong(T, T, v => S.Ring.negf(~T, ~neg, n, v), mul(c, add(y, w)), add(mul(c, y), mul(c, w)), dist_l(c, y, w)),
                      L.Negf.add(~T, ~add, ~neg, ~neg_add, n, mul(c, y), mul(c, w))))
    case 1n+p:
      match x:
        case S.NZ{}:
          {==}
        case S.N{+x1, +x2}:
          match a:
            case S.NZ{}:
              {==}
            case S.N{+a1, +a2}:
              match b:
                case S.NZ{}:
                  Equal.sym(", mv1, ", ", D.add("1n+p", gr, "S.NZ{}"), ", ", gr, ",
                    A.Add.zero_r(~T, ~add, 1n+p, ", gr, "))
                case S.N{+b1, +b2}:
", G2.levels(False{}, hr, "Gp.add_r"), "
"])], "\n")

# Part 3: signs
# -------------

# a component of a level: a term, its target, and the proof between them
type Cp is Data:
  Cp{l: String, r: String, pf: String}

def comb(+p: String, +c3: Cp, +c4: Cp) -> Cp:
  match c3 c4:
    case Cp{+l3, +r3, t3} Cp{+l4, +r4, t4}:
      Cp{D.add(p, l3, l4), D.add(p, r3, r4),
        D.cat(["A.Add.cong(~T, ~add, ", p, ", ", l3, ", ", r3, ", ", l4, ", ", r4, ",\n  ", D.ind(t3, 2n), ",\n  ", D.ind(t4, 2n), ")"])}

def pickc(+c: Bool, +a: Cp, +b: Cp) -> Cp:
  match c:
    case True{}:
      a
    case False{}:
      b

# a level from its components: Mk.cong over the e-part and the r-part
def level(+p: String, +c1: Cp, +c2: Cp, +rr: Cp) -> String:
  match c1 c2 rr:
    case Cp{+l1, +r1, t1} Cp{+l2, +r2, t2} Cp{rl, rr2, er}:
      +ee = D.cat(["A.Add.cong(~T, ~add, ", p, ", ", l1, ", ", r1, ", ", l2, ", ", r2, ",\n  ", D.ind(t1, 2n), ",\n  ", D.ind(t2, 2n), ")"])
      D.cat(["Mk.cong(T, ", p, ", ", D.add(p, l1, l2), ", ", D.add(p, r1, r2), ", ", rl, ", ", rr2, ",\n  ",
        D.ind(ee, 2n), ",\n  ", D.ind(er, 2n), ")"])

def G3.flags() -> List<&2, D.Fl>:
  [ D.Fl{"sr_a", ["n", "f", "m"], D.xor(D.xor("n", "f"), "m"), D.xor(D.xor("n", "m"), "f")},
    D.Fl{"sr_b", ["n", "m"], D.xor("n", D.xor("m", D.F())), D.xor("n", "m")},
    D.Fl{"sr_cp", ["n", "f", "m"], D.xor(D.xor("n", "f"), D.xor("m", D.F())), D.xor(D.xor("n", "m"), "f")},
    D.Fl{"sr_cn", ["n", "f", "m"], D.xor(D.bnot(D.xor("n", "f")), D.xor("m", D.F())), D.bnot(D.xor(D.xor("n", "m"), "f"))},
    D.Fl{"sl_a", ["f", "g"], D.xor("f", D.xor("g", D.F())), D.xor("f", "g")},
    D.Fl{"sl_b", ["n", "f", "m", "g"], D.xor(D.xor("n", "f"), D.xor("m", "g")), D.xor(D.xor("n", "m"), D.xor("f", "g"))},
    D.Fl{"sl_c", ["f", "g"], D.xor(D.bnot("f"), "g"), D.bnot(D.xor("f", "g"))},
    D.Fl{"sl_d", ["f", "g"], D.xor(D.bnot("f"), D.xor("g", D.F())), D.bnot(D.xor("f", "g"))},
    D.Fl{"sl_e", ["n", "f", "m", "g"], D.xor(D.bnot(D.xor("n", "f")), D.xor("m", "g")), D.bnot(D.xor(D.xor("n", "m"), D.xor("f", "g")))} ]

def G3.sr.term(+f: String, +n: String, +u: String, +mf: String, +v: String, +nr: String, +fl: String) -> Cp:
  +l = D.gpf("p", f, n, u, D.sgn("p", mf, D.F(), D.F(), v), "rest")
  +r = D.gpf("p", f, nr, u, v, "rest")
  Cp{l, r, D.trans(D.mv("p"), l, D.gpf("p", f, D.xor(n, mf), u, v, "rest"), r,
    D.cat(["Gp.sgn_r(", D.OPS(), ", ~neg_mul_r, ~neg_neg, p, ", f, ", ", n, ", ", u, ", ", mf, ", ", v, ", rest)"]),
    D.gflag("", "p", f, f, D.xor(n, mf), nr, u, v, "rest", "{==}", fl))}

def G3.sr(+q: D.Qc) -> String:
  +nf = D.xor("n", "f")
  +nm = D.xor("n", "m")
  +xm = D.xor("m", D.F())
  +c3 = G3.sr.term(D.bnot("f"), D.byq(q, nf, nf, D.bnot(nf)), "u1", xm, "v1",
    D.byq(q, D.xor(nm, "f"), D.xor(nm, "f"), D.bnot(D.xor(nm, "f"))),
    D.byq(q, "", D.flag.call("sr_cp", ["n", "f", "m"]), D.flag.call("sr_cn", ["n", "f", "m"])))
  +c4 = G3.sr.term("f", "n", "u2", "m", "v2", nm, "{==}")
  level("p", G3.sr.term("f", nf, "u1", "m", "v2", D.xor(nm, "f"), D.flag.call("sr_a", ["n", "f", "m"])),
    G3.sr.term(D.bnot("f"), "n", "u2", xm, "v1", nm, D.flag.call("sr_b", ["n", "m"])),
    pickc(D.isz(q), c4, comb("p", c3, c4)))

def G3.sl.term(+f: String, +n: String, +one: Bool, +v: String, +fr: String, +nr: String, +ef: String, +en: String) -> Cp:
  +sm = D.pick(one, D.xor("m", "g"), "m")
  +sg = D.pick(one, D.xor("g", D.F()), "g")
  +u = D.pick(one, "u1", "u2")
  +l = D.gpf("p", f, n, D.sgn("p", sm, sg, D.F(), u), v, "rest")
  +r = D.gpf("p", fr, nr, u, v, "rest")
  Cp{l, r, D.trans(D.mv("p"), l, D.gpf("p", D.xor(f, sg), D.xor(n, sm), u, v, "rest"), r,
    D.cat(["Gp.sgn_l(", D.OPS(), ", ~neg_mul_l, ~neg_neg, p, ", f, ", ", n, ", ", sm, ", ", sg, ", ", u, ", ", v, ", rest)"]),
    D.gflag("", "p", D.xor(f, sg), fr, D.xor(n, sm), nr, u, v, "rest", ef, en))}

def G3.sl(+q: D.Qc) -> String:
  +nf = D.xor("n", "f")
  +nm = D.xor("n", "m")
  +fg = D.xor("f", "g")
  +c3 = G3.sl.term(D.bnot("f"), D.byq(q, nf, nf, D.bnot(nf)), True{}, "v1", D.bnot(fg),
    D.byq(q, D.xor(nm, fg), D.xor(nm, fg), D.bnot(D.xor(nm, fg))), D.flag.call("sl_d", ["f", "g"]),
    D.byq(q, "", D.flag.call("sl_b", ["n", "f", "m", "g"]), D.flag.call("sl_e", ["n", "f", "m", "g"])))
  +c4 = G3.sl.term("f", "n", False{}, "v2", fg, nm, "{==}", "{==}")
  level("p", G3.sl.term("f", nf, True{}, "v2", fg, D.xor(nm, fg), D.flag.call("sl_a", ["f", "g"]), D.flag.call("sl_b", ["n", "f", "m", "g"])),
    G3.sl.term(D.bnot("f"), "n", False{}, "v1", D.bnot(fg), nm, D.flag.call("sl_c", ["f", "g"]), "{==}"),
    pickc(D.isz(q), c4, comb("p", c3, c4)))

def G3.text() -> String:
  +mvd = D.mv("d")
  D.sep([D.cat(["# Signs
# -----

# a sign on the right operand comes out: x * ((-1)^m v) = (-1)^m (x * v)
def Gp.sgn_r(", D.OPSD(), ", ~neg_mul_r: R.Ring.NegMulR(T, mul, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  +d: Nat, +f: Bool, +n: Bool, u: ", mvd, ", +m: Bool, v: ", mvd, ", +sig: S.Sig(d))
  -> {", D.gpf("d", "f", "n", "u", D.sgn("d", "m", D.F(), D.F(), "v"), "sig"), " == ", D.gpf("d", "f", D.xor("n", "m"), "u", "v", "sig"), " : ", mvd, "}:
  match d:
    case 0n:
      match u:
        case S.LZ{}:
          {==}
        case S.L{+a}:
          match v:
            case S.LZ{}:
              {==}
            case S.L{+b}:
              B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, mul(a, S.Ring.negf(~T, ~neg, m, b))), S.Ring.negf(~T, ~neg, ", D.xor("n", "m"), ", mul(a, b)),
                Equal.trans(T, S.Ring.negf(~T, ~neg, n, mul(a, S.Ring.negf(~T, ~neg, m, b))),
                  S.Ring.negf(~T, ~neg, n, S.Ring.negf(~T, ~neg, m, mul(a, b))),
                  S.Ring.negf(~T, ~neg, ", D.xor("n", "m"), ", mul(a, b)),
                  Equal.cong(T, T, w => S.Ring.negf(~T, ~neg, n, w), mul(a, S.Ring.negf(~T, ~neg, m, b)), S.Ring.negf(~T, ~neg, m, mul(a, b)),
                    L.Negf.mul_r(~T, ~mul, ~neg, ~neg_mul_r, m, a, b)),
                  L.Negf.negf(~T, ~neg, ~neg_neg, n, m, mul(a, b))))
    case 1n+p:
      match u:
        case S.NZ{}:
          {==}
        case S.N{+u1, +u2}:
          match v:
            case S.NZ{}:
              {==}
            case S.N{+v1, +v2}:
", D.qcases(G3.sr(D.CZ{}), G3.sr(D.CP{}), G3.sr(D.CN{}), 14n), "
"]), D.cat(["# a grade sign on the left operand joins the flags:
# inv^f((-1)^m inv^g(u)) * v = (-1)^m inv^(f xor g)(u) * v
def Gp.sgn_l(", D.OPSD(), ", ~neg_mul_l: R.Ring.NegMulL(T, mul, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  +d: Nat, +f: Bool, +n: Bool, +m: Bool, +g: Bool, u: ", mvd, ", v: ", mvd, ", +sig: S.Sig(d))
  -> {", D.gpf("d", "f", "n", D.sgn("d", "m", "g", D.F(), "u"), "v", "sig"), " == ", D.gpf("d", D.xor("f", "g"), D.xor("n", "m"), "u", "v", "sig"), " : ", mvd, "}:
  match d:
    case 0n:
      match u:
        case S.LZ{}:
          {==}
        case S.L{+a}:
          match v:
            case S.LZ{}:
              {==}
            case S.L{+b}:
              B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, mul(S.Ring.negf(~T, ~neg, m, a), b)), S.Ring.negf(~T, ~neg, ", D.xor("n", "m"), ", mul(a, b)),
                Equal.trans(T, S.Ring.negf(~T, ~neg, n, mul(S.Ring.negf(~T, ~neg, m, a), b)),
                  S.Ring.negf(~T, ~neg, n, S.Ring.negf(~T, ~neg, m, mul(a, b))),
                  S.Ring.negf(~T, ~neg, ", D.xor("n", "m"), ", mul(a, b)),
                  Equal.cong(T, T, w => S.Ring.negf(~T, ~neg, n, w), mul(S.Ring.negf(~T, ~neg, m, a), b), S.Ring.negf(~T, ~neg, m, mul(a, b)),
                    L.Negf.mul_l(~T, ~mul, ~neg, ~neg_mul_l, m, a, b)),
                  L.Negf.negf(~T, ~neg, ~neg_neg, n, m, mul(a, b))))
    case 1n+p:
      match u:
        case S.NZ{}:
          {==}
        case S.N{+u1, +u2}:
          match v:
            case S.NZ{}:
              {==}
            case S.N{+v1, +v2}:
", D.qcases(G3.sl(D.CZ{}), G3.sl(D.CP{}), G3.sl(D.CN{}), 14n), "
"])], "\n")

# Part 4: the sign of a product
# -----------------------------

def G4.flags() -> List<&2, D.Fl>:
  [ D.Fl{"xf", ["m"], D.xor("m", D.F()), "m"},
    D.Fl{"sg_a", ["m", "g"], D.xor(D.xor("m", D.F()), "g"), D.xor("m", "g")},
    D.Fl{"sg_b", ["m", "g"], D.xor("m", D.bnot("g")), D.bnot(D.xor("m", "g"))} ]

def G4.hs() -> String:
  D.OPS() ++ ", ~neg_add, ~neg_neg"

# the normal form sgn(k, F, F, gpf(g, F, y, z))
def G4.nf(+g: String, +k: String, +y: String, +z: String) -> String:
  D.sgn("p", k, D.F(), D.F(), D.gpf("p", g, D.F(), y, z, "rest"))

def G4.ih(+g: String, +k: String, +y: String, +z: String) -> String:
  D.cat(["Gp.sign(", G4.hs(), ", p, ", g, ", ", k, ", ", y, ", ", z, ", rest)"])

# a raw right-hand term and its proof to normal form
type Rt is Data:
  Rt{raw: String, pf: String}

def G4.compose(+sf: String, +g: String, +inner: String, +y: String, +z: String, +nff: String, +fl: String) -> Rt:
  +mv = D.mv("p")
  +raw = D.sgn("p", sf, D.F(), D.F(), D.gpf("p", g, inner, y, z, "rest"))
  +a = D.sgn("p", sf, D.F(), D.F(), G4.nf(g, inner, y, z))
  +b = G4.nf(g, D.xor(sf, inner), y, z)
  +c = G4.nf(g, nff, y, z)
  +s1 = D.cat(["G.Sgn.cong(~T, ~neg, p, ", sf, ", ", D.F(), ", ", D.F(), ", ", D.gpf("p", g, inner, y, z, "rest"), ", ", G4.nf(g, inner, y, z), ", ", G4.ih(g, inner, y, z), ")"])
  +s2 = D.cat(["G.Sgn.compose(~T, ~neg, ~neg_neg, p, ", sf, ", ", D.F(), ", ", D.F(), ", ", inner, ", ", D.F(), ", ", D.F(), ", ", D.gpf("p", g, D.F(), y, z, "rest"), ")"])
  +s3 = D.cat(["G.Sgn.flag(~T, ~neg, p, ", D.xor(sf, inner), ", ", nff, ", ", D.F(), ", ", D.F(), ", ", D.F(), ", ", D.gpf("p", g, D.F(), y, z, "rest"), ", ", fl, ", {==})"])
  Rt{raw, D.trans(mv, raw, b, c, D.trans(mv, raw, a, b, s1, s2), s3)}

def G4.plain(+sf: String, +g: String, +y: String, +z: String, +nff: String, +fl: String) -> Rt:
  Rt{D.sgn("p", sf, D.F(), D.F(), D.gpf("p", g, D.F(), y, z, "rest")),
    D.cat(["G.Sgn.flag(~T, ~neg, p, ", sf, ", ", nff, ", ", D.F(), ", ", D.F(), ", ", D.F(), ", ", D.gpf("p", g, D.F(), y, z, "rest"), ", ", fl, ", {==})"])}

def G4.body.fin(+isz: Bool, +mv: String, +xm: String, +e0: String, +r0: String, +rhs: String, +rmid: String, +el: String, +en: String,
  +rl: String, +rn: String, +lhs_nf: String, +n1: String, +n2: String, +n3: String, +n4: String, +a3: String,
  r1: Rt, r2: Rt, r3: Rt, r4: Rt) -> String:
  match r1 r2 r3 r4:
    case Rt{+w1, +p1} Rt{+w2, +p2} Rt{+w3, +p3} Rt{+w4, +p4}:
      +se = D.cat(["G.Sgn.add(~T, ~add, ~neg, ~neg_add, p, ", xm, ", ", D.F(), ", ", D.F(), ", ", D.gpf("p", "g", "g", "y1", "z2", "rest"), ", ", D.gpf("p", D.bnot("g"), D.F(), "y2", "z1", "rest"), ")"])
      +ee = D.trans(mv, D.sgn("p", xm, D.F(), D.F(), e0), D.add("p", w1, w2), en, se,
        D.cat(["A.Add.cong(~T, ~add, p, ", w1, ", ", n1, ", ", w2, ", ", n2, ",\n  ", D.ind(p1, 2n), ",\n  ", D.ind(p2, 2n), ")"]))
      +sr = D.cat(["G.Sgn.add(~T, ~add, ~neg, ~neg_add, p, m, ", D.F(), ", ", D.F(), ", ", a3, ", ", D.gpf("p", "g", D.F(), "y2", "z2", "rest"), ")"])
      +er = D.pick(isz, "{==}", D.trans(mv, D.sgn("p", "m", D.F(), D.F(), r0), D.add("p", w3, w4), rn, sr,
        D.cat(["A.Add.cong(~T, ~add, p, ", w3, ", ", n3, ", ", w4, ", ", n4, ",\n  ", D.ind(p3, 2n), ",\n  ", D.ind(p4, 2n), ")"])))
      +rhs_nf = D.trans(D.mv("1n+p"), rhs, rmid, D.mk("p", en, rn),
        D.cat(["G.Sgn.mk(~T, ~neg, p, m, ", D.F(), ", ", D.F(), ", ", e0, ", ", r0, ")"]),
        D.cat(["Mk.cong(T, p, ", D.sgn("p", xm, D.F(), D.F(), e0), ", ", en, ", ", D.sgn("p", "m", D.F(), D.F(), r0), ", ", rn, ",\n  ", D.ind(ee, 2n), ",\n  ", D.ind(er, 2n), ")"]))
      D.cat(["B.Eq.join(", D.mv("1n+p"), ", ", D.mk("p", el, rl), ", ", rhs, ", ", D.mk("p", en, rn), ",\n  ", D.ind(lhs_nf, 2n), ",\n  ", D.ind(rhs_nf, 2n), ")"])

def G4.body(+q: D.Qc) -> String:
  +isz = D.isz(q)
  +mv = D.mv("p")
  +xm = D.xor("m", D.F())
  +mg = D.xor("m", "g")
  +ng = D.bnot("g")
  +k3 = D.byq(q, mg, mg, D.bnot(mg))
  # left terms in normal form
  +l1 = D.gpf("p", "g", mg, "y1", "z2", "rest")
  +l2 = D.gpf("p", ng, "m", "y2", "z1", "rest")
  +l3 = D.gpf("p", ng, k3, "y1", "z1", "rest")
  +l4 = D.gpf("p", "g", "m", "y2", "z2", "rest")
  +n1 = G4.nf("g", mg, "y1", "z2")
  +n2 = G4.nf(ng, "m", "y2", "z1")
  +n3 = G4.nf(ng, k3, "y1", "z1")
  +n4 = G4.nf("g", "m", "y2", "z2")
  +i1 = G4.ih("g", mg, "y1", "z2")
  +i2 = G4.ih(ng, "m", "y2", "z1")
  +i3 = G4.ih(ng, k3, "y1", "z1")
  +i4 = G4.ih("g", "m", "y2", "z2")
  +el = D.add("p", l1, l2)
  +en = D.add("p", n1, n2)
  +eel = D.cat(["A.Add.cong(~T, ~add, p, ", l1, ", ", n1, ", ", l2, ", ", n2, ", ", i1, ", ", i2, ")"])
  +rl = D.pick(isz, l4, D.add("p", l3, l4))
  +rn = D.pick(isz, n4, D.add("p", n3, n4))
  +erl = D.pick(isz, i4, D.cat(["A.Add.cong(~T, ~add, p, ", l3, ", ", n3, ", ", l4, ", ", n4, ", ", i3, ", ", i4, ")"]))
  +lhs_nf = D.cat(["Mk.cong(T, p, ", el, ", ", en, ", ", rl, ", ", rn, ",\n  ", D.ind(eel, 2n), ",\n  ", D.ind(erl, 2n), ")"])
  # right side
  +e0 = D.add("p", D.gpf("p", "g", "g", "y1", "z2", "rest"), D.gpf("p", ng, D.F(), "y2", "z1", "rest"))
  +a3 = D.gpf("p", ng, D.byq(q, "g", "g", ng), "y1", "z1", "rest")
  +r0 = D.pick(isz, D.gpf("p", "g", D.F(), "y2", "z2", "rest"), D.add("p", a3, D.gpf("p", "g", D.F(), "y2", "z2", "rest")))
  +rhs = D.sgn("1n+p", "m", D.F(), D.F(), D.mk("p", e0, r0))
  +rmid = D.mk("p", D.sgn("p", xm, D.F(), D.F(), e0), D.sgn("p", "m", D.F(), D.F(), r0))
  +r1 = G4.compose(xm, "g", "g", "y1", "z2", mg, D.flag.call("sg_a", ["m", "g"]))
  +r2 = G4.plain(xm, ng, "y2", "z1", "m", D.flag.call("xf", ["m"]))
  +r3 = G4.compose("m", ng, D.byq(q, "g", "g", ng), "y1", "z1", k3, D.byq(q, "{==}", "{==}", D.flag.call("sg_b", ["m", "g"])))
  +r4 = {Rt{n4, "{==}"} : Rt}
  G4.body.fin(isz, mv, xm, e0, r0, rhs, rmid, el, en, rl, rn, lhs_nf, n1, n2, n3, n4, a3, r1, r2, r3, r4)

def G4.text() -> String:
  +mvd = D.mv("d")
  +g1 = D.gpf("d", "f", "n", "x", D.gpf("d", "g", "m", "y", "z", "sig"), "sig")
  +g2 = D.gpf("d", "f", "n", "x", D.sgn("d", "m", D.F(), D.F(), D.gpf("d", "g", D.F(), "y", "z", "sig")), "sig")
  +g3 = D.gpf("d", "f", D.xor("n", "m"), "x", D.gpf("d", "g", D.F(), "y", "z", "sig"), "sig")
  D.cat(["# the sign flag of a product is a grade sign of the product:
# (-1)^m inv^g(y) z = (-1)^m (inv^g(y) z)
def Gp.sign(", D.OPSD(), ", ~neg_add: R.Ring.NegAdd(T, add, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  +d: Nat, +g: Bool, +m: Bool, y: ", mvd, ", z: ", mvd, ", +sig: S.Sig(d))
  -> {", D.gpf("d", "g", "m", "y", "z", "sig"), " == ", D.sgn("d", "m", D.F(), D.F(), D.gpf("d", "g", D.F(), "y", "z", "sig")), " : ", mvd, "}:
  match d:
    case 0n:
      match y:
        case S.LZ{}:
          {==}
        case S.L{a}:
          match z:
            case S.LZ{}:
              {==}
            case S.L{b}:
              {==}
    case 1n+p:
      match y:
        case S.NZ{}:
          {==}
        case S.N{+y1, +y2}:
          match z:
            case S.NZ{}:
              {==}
            case S.N{+z1, +z2}:
", D.qcases(G4.body(D.CZ{}), G4.body(D.CP{}), G4.body(D.CN{}), 14n), "

# a sign inside the right operand comes out to the product's flag
def Gp.pull(", D.OPSD(), ", ~neg_add: R.Ring.NegAdd(T, add, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  ~neg_mul_r: R.Ring.NegMulR(T, mul, neg),
  +d: Nat, +f: Bool, +n: Bool, +x: ", mvd, ", +g: Bool, +m: Bool, +y: ", mvd, ", +z: ", mvd, ", +sig: S.Sig(d))
  -> {", g1, " == ", g3, " : ", mvd, "}:
  ", D.trans(mvd, g1, g2, g3,
    D.cat(["Gp.cong(", D.OPS(), ", d, f, n, x, x, ", D.gpf("d", "g", "m", "y", "z", "sig"), ", ", D.sgn("d", "m", D.F(), D.F(), D.gpf("d", "g", D.F(), "y", "z", "sig")), ", sig, {==}, Gp.sign(", G4.hs(), ", d, g, m, y, z, sig))"]),
    D.cat(["Gp.sgn_r(", D.OPS(), ", ~neg_mul_r, ~neg_neg, d, f, n, x, m, ", D.gpf("d", "g", D.F(), "y", "z", "sig"), ", sig)"])), "
"])

# proofs/gp.bend, and the flag identities it uses (in registration order)
def GP.text() -> String:
  D.cat([G1.text(), G2.text(), G3.text(), G4.text()])

def GP.flags() -> List<&2, D.Fl>:
  List.append(&2, D.Fl, G3.flags(), G4.flags())
