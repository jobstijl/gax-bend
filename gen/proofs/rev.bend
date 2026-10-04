# Writes proofs/rev.bend: the reverse is an anti-automorphism of the
# geometric product, through a lemma that carries the involution and sign
# flags. Each pair of terms is compared after pulling every sign out of the
# reversed operands (Rev.nf); the flag identities that remain are emitted
# where the two flag terms differ.

import Base
import ./dsl.bend as D

def V.hsl() -> String:
  D.OPS() ++ ", ~neg_mul_l, ~neg_neg"

def V.hsr() -> String:
  D.OPS() ++ ", ~neg_mul_r, ~neg_neg"

def V.hnf() -> String:
  D.OPS() ++ ", ~neg_neg, ~neg_mul_l, ~neg_mul_r"

def V.h() -> String:
  D.OPS() ++ ", ~add_comm, ~mul_comm, ~neg_add, ~neg_neg, ~neg_mul_l, ~neg_mul_r"

def V.gcong(+d: String, +f: String, +n: String, +x: String, +x2: String, +y: String, +y2: String, +s: String, +ex: String, +ey: String) -> String:
  D.cat(["P.Gp.cong(", D.OPS(), ", ", d, ", ", f, ", ", n, ", ", x, ", ", x2, ", ", y, ", ", y2, ", ", s, ",\n  ", D.ind(ex, 2n), ",\n  ", D.ind(ey, 2n), ")"])

def V.head() -> String:
  +mv = D.mv("d")
  +y0 = D.sgn("d", D.F(), D.F(), D.Tr(), "y")
  +x0 = D.sgn("d", D.F(), "b", D.Tr(), "x")
  +ly = D.sgn("d", "j", "c", D.Tr(), "y")
  +lx = D.sgn("d", "k2", "b", D.Tr(), "x")
  +my = D.sgn("d", "j", "c", D.F(), y0)
  +mx = D.sgn("d", "k2", D.F(), D.F(), x0)
  +xf = {"xf" : String}
  +e_y = D.trans(mv, ly, D.sgn("d", D.xor("j", D.F()), D.xor("c", D.F()), D.Tr(), "y"), my,
    D.cat(["G.Sgn.flag(~T, ~neg, d, j, ", D.xor("j", D.F()), ", c, ", D.xor("c", D.F()), ", ", D.Tr(), ", y, ",
      D.sym("Bool", D.xor("j", D.F()), "j", D.flag.call(xf, ["j"])), ", ", D.sym("Bool", D.xor("c", D.F()), "c", D.flag.call(xf, ["c"])), ")"]),
    D.sym(mv, my, D.sgn("d", D.xor("j", D.F()), D.xor("c", D.F()), D.Tr(), "y"), D.cat(["G.Sgn.compose(~T, ~neg, ~neg_neg, d, j, c, ", D.F(), ", ", D.F(), ", ", D.F(), ", ", D.Tr(), ", y)"])))
  +e_x = D.trans(mv, lx, D.sgn("d", D.xor("k2", D.F()), "b", D.Tr(), "x"), mx,
    D.cat(["G.Sgn.flag(~T, ~neg, d, k2, ", D.xor("k2", D.F()), ", b, b, ", D.Tr(), ", x, ", D.sym("Bool", D.xor("k2", D.F()), "k2", D.flag.call(xf, ["k2"])), ", {==})"]),
    D.sym(mv, mx, D.sgn("d", D.xor("k2", D.F()), "b", D.Tr(), "x"), D.cat(["G.Sgn.compose(~T, ~neg, ~neg_neg, d, k2, ", D.F(), ", ", D.F(), ", ", D.F(), ", b, ", D.Tr(), ", x)"])))
  +g0 = D.gpf("d", "g", "k", ly, lx, "sig")
  +g1 = D.gpf("d", "g", "k", my, mx, "sig")
  +g2 = D.gpf("d", "g", D.xor("k", "k2"), my, x0, "sig")
  +g3 = D.gpf("d", D.xor("g", "c"), D.xor(D.xor("k", "k2"), "j"), y0, x0, "sig")
  +nf_proof = D.trans(mv, g0, g1, g3,
    V.gcong("d", "g", "k", ly, my, lx, mx, "sig", e_y, e_x),
    D.trans(mv, g1, g2, g3,
      D.cat(["P.Gp.sgn_r(", V.hsr(), ", d, g, k, ", my, ", k2, ", x0, ", sig)"]),
      D.cat(["P.Gp.sgn_l(", V.hsl(), ", d, g, ", D.xor("k", "k2"), ", j, c, ", y0, ", ", x0, ", sig)"])))
  +lhs_m = D.gpf("d", "g", "k", D.sgn("d", D.F(), D.F(), D.Tr(), "y"), D.sgn("d", D.F(), "b", D.Tr(), "x"), "sig")
  D.cat(["# The reverse is an anti-automorphism
# -----------------------------------

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S
import ./base.bend as B
import ./leaf.bend as L
import ./add.bend as A
import ./flags.bend as F
import ./sgn.bend as G
import ./gp.bend as P

# the signs of reversed operands come out: inv^c(y) and the signs (-1)^j,
# (-1)^k2 move into the product's flags, leaving rev(y) and inv^b(rev(x))
def Rev.nf(", D.OPSD(), ", ~neg_neg: R.Ring.NegNeg(T, neg), ~neg_mul_l: R.Ring.NegMulL(T, mul, neg), ~neg_mul_r: R.Ring.NegMulR(T, mul, neg),
  +d: Nat, +g: Bool, +k: Bool, +j: Bool, +c: Bool, +y: ", mv, ", +k2: Bool, +b: Bool, +x: ", mv, ", +sig: S.Sig(d))
  -> {", g0, " == ", g3, " : ", mv, "}:
  ", D.ind(nf_proof, 2n), "

# equal flags give equal normal forms
def Rev.match(", D.OPSD(), ", -d: Nat, -g: Bool, -g2: Bool, -k: Bool, -k2: Bool, -y: ", mv, ", -b: Bool, -b2: Bool, -x: ", mv, ", -sig: S.Sig(d),
  eg: {g == g2 : Bool}, ek: {k == k2 : Bool}, eb: {b == b2 : Bool})
  -> {", lhs_m, " == ", D.gpf("d", "g2", "k2", D.sgn("d", D.F(), D.F(), D.Tr(), "y"), D.sgn("d", D.F(), "b2", D.Tr(), "x"), "sig"), " : ", mv, "}:
  %eg : {", lhs_m, " == ", D.gpf("d", "_", "k2", D.sgn("d", D.F(), D.F(), D.Tr(), "y"), D.sgn("d", D.F(), "b2", D.Tr(), "x"), "sig"), " : ", mv, "}
  %ek : {", lhs_m, " == ", D.gpf("d", "g", "_", D.sgn("d", D.F(), D.F(), D.Tr(), "y"), D.sgn("d", D.F(), "b2", D.Tr(), "x"), "sig"), " : ", mv, "}
  %eb : {", lhs_m, " == ", D.gpf("d", "g", "k", D.sgn("d", D.F(), D.F(), D.Tr(), "y"), D.sgn("d", D.F(), "_", D.Tr(), "x"), "sig"), " : ", mv, "}
  {==}
"])

# a term of a level: gpf(g, k, sgn(j, c, T, y), sgn(k2, b, T, x))
type Rv is Data:
  Rv{g: String, k: String, j: String, c: String, k2: String, b: String}

def V.term(t: Rv, +y: String, +x: String) -> String:
  match t:
    case Rv{g, k, j, c, k2, b}:
      D.gpf("p", g, k, D.sgn("p", j, c, D.Tr(), y), D.sgn("p", k2, b, D.Tr(), x), "rest")

# the normal-form flags (g xor c, (k xor k2) xor j, b)
def V.nfg(t: Rv) -> String:
  match t:
    case Rv{g, k, j, c, k2, b}:
      D.xor(g, c)

def V.nfk(t: Rv) -> String:
  match t:
    case Rv{g, k, j, c, k2, b}:
      D.xor(D.xor(k, k2), j)

def V.nfb(t: Rv) -> String:
  match t:
    case Rv{g, k, j, c, k2, b}:
      b

def V.nft(+gg: String, +kk: String, +bb: String, +y: String, +x: String) -> String:
  D.gpf("p", gg, kk, D.sgn("p", D.F(), D.F(), D.Tr(), y), D.sgn("p", D.F(), bb, D.Tr(), x), "rest")

def V.nfpf(t: Rv, +y: String, +x: String) -> String:
  match t:
    case Rv{g, k, j, c, k2, b}:
      D.cat(["Rev.nf(", V.hnf(), ", p, ", g, ", ", k, ", ", j, ", ", c, ", ", y, ", ", k2, ", ", b, ", ", x, ", rest)"])

# the flag identity named rv_<tag><i>, or {==} when the two sides agree
def V.ident(+name: String, +l: String, +r: String) -> String:
  D.pick(String.eq(l, r), "{==}", D.flag.call(name, ["m", "a", "n", "f"]))

def V.ident.fl.if(name: String, l: String, r: String, same: Bool) -> List<&2, D.Fl>:
  match same:
    case True{}:
      Nil{}
    case False{}:
      [D.Fl{name, ["m", "a", "n", "f"], l, r}]

def V.ident.fl(+name: String, +l: String, +r: String) -> List<&2, D.Fl>:
  V.ident.fl.if(name, l, r, String.eq(l, r))

# the identities a pair needs, in order
def V.pair.fl(+tag: String, +l: Rv, +r: Rv) -> List<&2, D.Fl>:
  List.append(&2, D.Fl, V.ident.fl("rv_" ++ tag ++ "0", V.nfg(l), V.nfg(r)),
    List.append(&2, D.Fl, V.ident.fl("rv_" ++ tag ++ "1", V.nfk(l), V.nfk(r)), V.ident.fl("rv_" ++ tag ++ "2", V.nfb(l), V.nfb(r))))

# a proof that the two terms of a pair are equal
def V.pair(+tag: String, +l: Rv, +r: Rv, +y: String, +x: String) -> String:
  +mv = D.mv("p")
  +lt = V.term(l, y, x)
  +rt = V.term(r, y, x)
  +lnf = V.nft(V.nfg(l), V.nfk(l), V.nfb(l), y, x)
  +rnf = V.nft(V.nfg(r), V.nfk(r), V.nfb(r), y, x)
  +m = D.cat(["Rev.match(", D.OPS(), ", p, ", V.nfg(l), ", ", V.nfg(r), ", ", V.nfk(l), ", ", V.nfk(r), ", ", y, ", ", V.nfb(l), ", ", V.nfb(r), ", ", x, ", rest,\n  ",
    V.ident("rv_" ++ tag ++ "0", V.nfg(l), V.nfg(r)), ",\n  ",
    V.ident("rv_" ++ tag ++ "1", V.nfk(l), V.nfk(r)), ",\n  ",
    V.ident("rv_" ++ tag ++ "2", V.nfb(l), V.nfb(r)), ")"])
  D.trans(mv, lt, rnf, rt, D.trans(mv, lt, lnf, rnf, V.nfpf(l, y, x), m), D.sym(mv, rt, rnf, V.nfpf(r, y, x)))

type Gt is Data:
  Gt{f: String, n: String, x: String, y: String}

def V.g(t: Gt) -> String:
  match t:
    case Gt{f, n, x, y}:
      D.gpf("p", f, n, x, y, "rest")

def V.ih(+mm: String, +aa: String, t: Gt) -> String:
  match t:
    case Gt{f, n, x, y}:
      D.cat(["Rev.gp(", V.h(), ", p, ", mm, ", ", aa, ", ", f, ", ", n, ", ", x, ", ", y, ", rest)"])

# the six left and right forms of a level
type Lv6 is Data:
  Lv6{le1: Rv, le2: Rv, le3: Rv, le4: Rv, re1: Rv, re2: Rv, rr3: Rv, rr4: Rv}

def V.forms(+q: D.Qc) -> Lv6:
  +nf = D.xor("n", "f")
  +nf3 = D.byq(q, nf, nf, D.bnot(nf))
  +ma = D.xor("m", "a")
  +at = D.xor("a", D.Tr())
  +mn = D.xor("m", "n")
  +af = D.xor("a", "f")
  +rk = D.byq(q, D.xor(mn, D.F()), D.xor(mn, D.F()), D.bnot(D.xor(mn, D.F())))
  Lv6{
    Rv{D.F(), D.xor(ma, nf), D.F(), at, D.F(), D.xor(at, "f")},
    Rv{D.F(), D.xor(ma, "n"), D.F(), at, D.F(), D.xor(at, D.bnot("f"))},
    Rv{D.F(), D.xor("m", nf3), D.F(), "a", D.F(), D.xor("a", D.bnot("f"))},
    Rv{D.F(), D.xor("m", "n"), D.F(), "a", D.F(), af},
    Rv{D.F(), D.xor(mn, D.F()), "a", at, D.F(), af},
    Rv{D.Tr(), mn, D.F(), "a", af, D.xor(af, D.Tr())},
    Rv{D.Tr(), rk, "a", at, af, D.xor(af, D.Tr())},
    Rv{D.F(), mn, D.F(), "a", D.F(), af}}

def V.ctag(q: D.Qc) -> String:
  D.byq(q, "CQZ", "CQP", "CQN")

def V.level.fl.c(z: Bool, +tag: String, +l: Rv, +r: Rv) -> List<&2, D.Fl>:
  match z:
    case True{}:
      Nil{}
    case False{}:
      V.pair.fl(tag, l, r)

def V.level.fl.go(+q: D.Qc, f: Lv6) -> List<&2, D.Fl>:
  match f:
    case Lv6{+le1, +le2, +le3, le4, +re1, +re2, +rr3, rr4}:
      List.append(&2, D.Fl, V.pair.fl("A", le1, re2),
        List.append(&2, D.Fl, V.pair.fl("B", le2, re1), V.level.fl.c(D.isz(q), V.ctag(q), le3, rr3)))

# the identities of a level, in the order flags.bend lists them
def V.level.fl(+q: D.Qc) -> List<&2, D.Fl>:
  V.level.fl.go(q, V.forms(q))

def V.flags() -> List<&2, D.Fl>:
  List.append(&2, D.Fl, [D.Fl{"xf", ["m"], D.xor("m", D.F()), "m"}],
    List.append(&2, D.Fl, V.level.fl(D.CZ{}), List.append(&2, D.Fl, V.level.fl(D.CP{}), V.level.fl(D.CN{}))))

def V.level.go(+q: D.Qc, f: Lv6) -> String:
  match f:
    case Lv6{+le1, +le2, +le3, +le4, +re1, +re2, +rr3, +rr4}:
      +isz = D.isz(q)
      +mv = D.mv("p")
      +mv1 = D.mv("1n+p")
      +nf = D.xor("n", "f")
      +nf3 = D.byq(q, nf, nf, D.bnot(nf))
      +ma = D.xor("m", "a")
      +at = D.xor("a", D.Tr())
      +g1 = {Gt{"f", nf, "x1", "y2"} : Gt}
      +g2 = {Gt{D.bnot("f"), "n", "x2", "y1"} : Gt}
      +g3 = {Gt{D.bnot("f"), nf3, "x1", "y1"} : Gt}
      +g4 = {Gt{"f", "n", "x2", "y2"} : Gt}
      +e0 = D.add("p", V.g(g1), V.g(g2))
      +r0 = D.pick(isz, V.g(g4), D.add("p", V.g(g3), V.g(g4)))
      +l1 = V.term(le1, "y2", "x1")
      +l2 = V.term(le2, "y1", "x2")
      +l3 = V.term(le3, "y1", "x1")
      +l4 = V.term(le4, "y2", "x2")
      +ee = D.trans(mv, D.sgn("p", ma, at, D.Tr(), e0), D.add("p", D.sgn("p", ma, at, D.Tr(), V.g(g1)), D.sgn("p", ma, at, D.Tr(), V.g(g2))), D.add("p", l1, l2),
        D.cat(["G.Sgn.add(~T, ~add, ~neg, ~neg_add, p, ", ma, ", ", at, ", ", D.Tr(), ", ", V.g(g1), ", ", V.g(g2), ")"]),
        D.cat(["A.Add.cong(~T, ~add, p, ", D.sgn("p", ma, at, D.Tr(), V.g(g1)), ", ", l1, ", ", D.sgn("p", ma, at, D.Tr(), V.g(g2)), ", ", l2, ", ", V.ih(ma, at, g1), ", ", V.ih(ma, at, g2), ")"]))
      +rl = D.pick(isz, l4, D.add("p", l3, l4))
      +er = D.pick(isz, V.ih("m", "a", g4),
        D.trans(mv, D.sgn("p", "m", "a", D.Tr(), r0), D.add("p", D.sgn("p", "m", "a", D.Tr(), V.g(g3)), D.sgn("p", "m", "a", D.Tr(), V.g(g4))), rl,
          D.cat(["G.Sgn.add(~T, ~add, ~neg, ~neg_add, p, m, a, ", D.Tr(), ", ", V.g(g3), ", ", V.g(g4), ")"]),
          D.cat(["A.Add.cong(~T, ~add, p, ", D.sgn("p", "m", "a", D.Tr(), V.g(g3)), ", ", l3, ", ", D.sgn("p", "m", "a", D.Tr(), V.g(g4)), ", ", l4, ", ", V.ih("m", "a", g3), ", ", V.ih("m", "a", g4), ")"])))
      +lhs = D.sgn("1n+p", "m", "a", D.Tr(), D.mk("p", e0, r0))
      +m1 = D.mk("p", D.sgn("p", ma, at, D.Tr(), e0), D.sgn("p", "m", "a", D.Tr(), r0))
      +m2 = D.mk("p", D.add("p", l1, l2), rl)
      +pa = V.pair("A", le1, re2, "y2", "x1")
      +rta = V.term(re2, "y2", "x1")
      +pb = V.pair("B", le2, re1, "y1", "x2")
      +rtb = V.term(re1, "y1", "x2")
      +e_r = D.add("p", rtb, rta)
      +ee2 = D.trans(mv, D.add("p", l1, l2), D.add("p", l2, l1), e_r,
        D.cat(["A.Add.comm(~T, ~add, ~add_comm, p, ", l1, ", ", l2, ")"]),
        D.cat(["A.Add.cong(~T, ~add, p, ", l2, ", ", rtb, ", ", l1, ", ", rta, ",\n  ", D.ind(pb, 2n), ",\n  ", D.ind(pa, 2n), ")"]))
      +rr4t = V.term(rr4, "y2", "x2")
      +pc = V.pair(V.ctag(q), le3, rr3, "y1", "x1")
      +rtc = V.term(rr3, "y1", "x1")
      +r_r = D.pick(isz, rr4t, D.add("p", rtc, rr4t))
      +er2 = D.pick(isz, "{==}", D.cat(["A.Add.cong(~T, ~add, p, ", l3, ", ", rtc, ", ", l4, ", ", rr4t, ",\n  ", D.ind(pc, 2n), ",\n  {==})"]))
      +m3 = D.mk("p", e_r, r_r)
      +s1 = D.cat(["G.Sgn.mk(~T, ~neg, p, m, a, ", D.Tr(), ", ", e0, ", ", r0, ")"])
      +s2 = D.cat(["P.Mk.cong(T, p, ", D.sgn("p", ma, at, D.Tr(), e0), ", ", D.add("p", l1, l2), ", ", D.sgn("p", "m", "a", D.Tr(), r0), ", ", rl, ",\n  ", D.ind(ee, 2n), ",\n  ", D.ind(er, 2n), ")"])
      +s3 = D.cat(["P.Mk.cong(T, p, ", D.add("p", l1, l2), ", ", e_r, ", ", rl, ", ", r_r, ",\n  ", D.ind(ee2, 2n), ",\n  ", D.ind(er2, 2n), ")"])
      D.trans(mv1, lhs, m2, m3, D.trans(mv1, lhs, m1, m2, s1, s2), s3)

def V.level(+q: D.Qc) -> String:
  V.level.go(q, V.forms(q))

def V.gp() -> String:
  +mvd = D.mv("d")
  D.cat(["# (-1)^m inv^a(rev(inv^f(x) y)), signed by n, is rev(y) times rev(x) with
# the involutions and signs carried: the reverse turns products around
def Rev.gp(", D.OPSD(), ", ~add_comm: R.Ring.Comm(T, add), ~mul_comm: R.Ring.Comm(T, mul),
  ~neg_add: R.Ring.NegAdd(T, add, neg), ~neg_neg: R.Ring.NegNeg(T, neg),
  ~neg_mul_l: R.Ring.NegMulL(T, mul, neg), ~neg_mul_r: R.Ring.NegMulR(T, mul, neg),
  +d: Nat, +m: Bool, +a: Bool, +f: Bool, +n: Bool, x: ", mvd, ", y: ", mvd, ", +sig: S.Sig(d))
  -> {", D.sgn("d", "m", "a", D.Tr(), D.gpf("d", "f", "n", "x", "y", "sig")), " == ", D.gpf("d", D.F(), D.xor("m", "n"), D.sgn("d", D.F(), "a", D.Tr(), "y"), D.sgn("d", D.F(), D.xor("a", "f"), D.Tr(), "x"), "sig"), " : ", mvd, "}:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          match y:
            case S.LZ{}:
              {==}
            case S.L{v}:
              {==}
        case S.L{+u}:
          match y:
            case S.LZ{}:
              {==}
            case S.L{+v}:
              B.Leaf.cong(T, S.Ring.negf(~T, ~neg, m, S.Ring.negf(~T, ~neg, n, mul(u, v))), S.Ring.negf(~T, ~neg, ", D.xor("m", "n"), ", mul(v, u)),
                Equal.trans(T, S.Ring.negf(~T, ~neg, m, S.Ring.negf(~T, ~neg, n, mul(u, v))), S.Ring.negf(~T, ~neg, ", D.xor("m", "n"), ", mul(u, v)),
                  S.Ring.negf(~T, ~neg, ", D.xor("m", "n"), ", mul(v, u)),
                  L.Negf.negf(~T, ~neg, ~neg_neg, m, n, mul(u, v)),
                  Equal.cong(T, T, w => S.Ring.negf(~T, ~neg, ", D.xor("m", "n"), ", w), mul(u, v), mul(v, u), mul_comm(u, v))))
    case 1n+p:
      match x:
        case S.NZ{}:
          match y:
            case S.NZ{}:
              {==}
            case S.N{y1, y2}:
              {==}
        case S.N{+x1, +x2}:
          match y:
            case S.NZ{}:
              {==}
            case S.N{+y1, +y2}:
", D.qcases(V.level(D.CZ{}), V.level(D.CP{}), V.level(D.CN{}), 14n), "
"])

def V.text() -> String:
  D.sep([V.head(), V.gp()], "\n")
