# Writes proofs/err.bend: the rounding error of every term, without and
# with underflow (ADR-005, docs/numerics.md §1). Each inequality step is a
# ring identity, proven by the normaliser, over pieces known nonnegative.

import Base
import ./dsl.bend as D

# Ring identities, as data: atoms are indices into a list of Bend terms
type Ex is Data:
  X{i: Nat}
  Z{}
  Pl{a: Ex, b: Ex}
  Mu{a: Ex, b: Ex}
  Ng{a: Ex}

# Bend text for T's operations
def Er.add(+a: String, +b: String) -> String:
  D.cat(["add(", a, ", ", b, ")"])

def Er.mul(+a: String, +b: String) -> String:
  D.cat(["mul(", a, ", ", b, ")"])

def Er.neg(+a: String) -> String:
  D.cat(["neg(", a, ")"])

def Er.ab(+a: String) -> String:
  D.cat(["abs(", a, ")"])

def Er.LE(+a: String, +b: String) -> String:
  D.cat(["{pos(", Er.add(b, Er.neg(a)), ") == True{} : Bool}"])

def Er.POS(+a: String) -> String:
  D.cat(["{pos(", a, ") == True{} : Bool}"])

def Er.EQ(+a: String, +b: String) -> String:
  D.cat(["{", a, " == ", b, " : T}"])

def Er.at(xs: List<&2, String>, i: Nat) -> String:
  match xs:
    case Nil{}:
      "?"
    case x <> t:
      match i:
        case 0n:
          x
        case 1n+j:
          Er.at(t, j)

def Er.tT(e: Ex, +atoms: List<&2, String>) -> String:
  match e:
    case X{i}:
      Er.at(atoms, i)
    case Z{}:
      "zero"
    case Pl{a, b}:
      Er.add(Er.tT(a, atoms), Er.tT(b, atoms))
    case Mu{a, b}:
      Er.mul(Er.tT(a, atoms), Er.tT(b, atoms))
    case Ng{a}:
      Er.neg(Er.tT(a, atoms))

def Er.tM(e: Ex) -> String:
  match e:
    case X{i}:
      D.cat(["N.TVar{", Nat.show(i), "n}"])
    case Z{}:
      "N.TZero{}"
    case Pl{a, b}:
      D.cat(["N.TAdd{", Er.tM(a), ", ", Er.tM(b), "}"])
    case Mu{a, b}:
      D.cat(["N.TMul{", Er.tM(a), ", ", Er.tM(b), "}"])
    case Ng{a}:
      D.cat(["N.TNeg{", Er.tM(a), "}"])

def v(i: Nat) -> Ex:
  X{i}

def p(a: Ex, b: Ex) -> Ex:
  Pl{a, b}

def m(a: Ex, b: Ex) -> Ex:
  Mu{a, b}

def n(a: Ex) -> Ex:
  Ng{a}

def z() -> Ex:
  Z{}

# Hypotheses
# ----------

def Er.OPSD() -> String:
  "~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T"

def Er.RH() -> String:
  "~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),\n  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),\n  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg)"

def Er.OH() -> String:
  "~pos: T -> Bool, ~abs: T -> T, ~pos_add: E.Ord.PosAdd(T, add, pos), ~pos_mul: E.Ord.PosMul(T, mul, pos), ~pos_abs: E.Ord.PosAbs(T, abs, pos),\n  ~tri: E.Ord.Tri(T, add, neg, abs, pos), ~abs_mul: E.Ord.AbsMul(T, mul, abs), ~abs_neg: E.Ord.AbsNeg(T, neg, abs), ~abs_zero: {abs(zero) == zero : T},\n  ~eps: T, ~pos_eps: {pos(eps) == True{} : Bool}"

def Er.RNDH() -> String:
  "~rnd: T -> T, ~rnd_ok: E.Ord.Rnd(T, add, mul, neg, abs, pos, eps, rnd)"

def Er.ETAH() -> String:
  "~eta_a: T, ~eta_m: T, ~pos_eta_a: {pos(eta_a) == True{} : Bool}, ~pos_eta_m: {pos(eta_m) == True{} : Bool}"

def Er.RNDUH() -> String:
  "~rnda: T -> T, ~rndm: T -> T, ~rnda_ok: E.Ord.RndU(T, add, mul, neg, abs, pos, eps, eta_a, rnda), ~rndm_ok: E.Ord.RndU(T, add, mul, neg, abs, pos, eps, eta_m, rndm)"

def Er.ALL() -> String:
  D.cat([Er.OPSD(), ",\n  ", Er.RH(), ",\n  ", Er.OH()])

def Er.OPS() -> String:
  "~T, ~zero, ~one, ~add, ~mul, ~neg"

def Er.RHA() -> String:
  "~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn"

def Er.A() -> String:
  D.cat([Er.OPS(), ", ", Er.RHA(), ", ~pos, ~abs, ~pos_add, ~pos_mul, ~pos_abs, ~tri, ~abs_mul, ~abs_neg, ~abs_zero, ~eps, ~pos_eps"])

# Proof steps
# -----------

def Er.NORM(atoms: List<&2, String>, l: Ex, r: Ex) -> String:
  D.cat(["NP.Norm.eq(", Er.OPS(), ", ", Er.RHA(), ", [", D.sep(atoms, ", "), "], ", Er.tM(l), ", ", Er.tM(r), ", {==})"])

# an identity whose atoms are the given terms, with both sides as text
def Er.call(+name: String, args: List<&2, String>) -> String:
  D.cat([name, "(", Er.A(), ", ", D.sep(args, ", "), ")"])

def Er.call0(+name: String) -> String:
  D.cat([name, "(", Er.A(), ")"])

def Er.trans(+a: String, +b: String, +c: String, +x: String, +y: String) -> String:
  Er.call("Le.trans", [a, b, c, x, y])

def Er.congabs(+x: String, +y: String, +e: String) -> String:
  D.cat(["Equal.cong(T, T, w => abs(w), ", x, ", ", y, ", ", e, ")"])

def Er.etrans(+a: String, +b: String, +c: String, +x: String, +y: String) -> String:
  D.cat(["Equal.trans(T, ", a, ", ", b, ", ", c, ", ", x, ", ", y, ")"])

def Er.esym(+a: String, +b: String, +x: String) -> String:
  D.cat(["Equal.sym(T, ", a, ", ", b, ", ", x, ")"])

def Er.PR(+s: String, +t: String, +e: String, +x: String) -> String:
  D.cat(["Pos.rw(~T, ~pos, ", s, ", ", t, ", ", e, ", ", x, ")"])

def Er.pos_add(+x: String, +y: String, +px: String, +py: String) -> String:
  D.cat(["pos_add(", x, ", ", y, ", ", px, ", ", py, ")"])

def Er.pos_mul(+x: String, +y: String, +px: String, +py: String) -> String:
  D.cat(["pos_mul(", x, ", ", y, ", ", px, ", ", py, ")"])

# Order
# -----

def Er.order() -> String:
  +all = Er.ALL()
  +ama = Er.add("a", Er.neg("a"))
  +wy = Er.add("w3", Er.neg("y"))
  +yx = Er.add("y", Er.neg("x"))
  +y1x1 = Er.add("y1", Er.neg("x1"))
  +y2x2 = Er.add("y2", Er.neg("x2"))
  +yx_ = Er.add("y", Er.neg("x"))
  +xy = Er.add("x", Er.neg("y"))
  +xyy = Er.add(xy, "y")
  D.cat(["# The rounding error of every term (ADR-005, docs/numerics.md): for an
# ordered commutative ring T and a rounding function rnd satisfying the
# standard model |rnd(x) - x| <= eps |x|,
#   |fl(t) - eval(t)| <= h(k(t)) absev(t),
# with h(k) = (1 + eps)^k - 1 (src/err.bend). With underflow, additions
# and products round within eps |x| + eta_a and eps |x| + eta_m, and the
# bound gains the absolute term D(t). Order is positivity: a <= b means
# pos(b - a), and each step is a ring identity (the normaliser) over
# nonnegative pieces.

import Base
import ../src/ring.bend as R
import ../src/norm.bend as N
import ../src/err.bend as E
import ./norm.bend as NP

# Order
# -----

def Pos.rw(~T: Data, ~pos: T -> Bool, -s: T, -t: T, e: {s == t : T}, +p: {pos(s) == True{} : Bool}) -> {pos(t) == True{} : Bool}:
  %e : {pos(_) == True{} : Bool}
  p

def Pos.zero(", all, ") -> ", Er.POS("zero"), ":
  ", Er.PR("abs(zero)", "zero", "abs_zero", "pos_abs(zero)"), "

def Le.refl(", all, ", +a: T) -> ", Er.LE("a", "a"), ":
  ", Er.PR("zero", ama, Er.esym(ama, "zero", "inv(a)"), Er.call0("Pos.zero")), "

def Le.eq(", all, ", +a: T, -b: T, e: ", Er.EQ("a", "b"), ") -> ", Er.LE("a", "b"), ":
  %e : {pos(add(_, neg(a))) == True{} : Bool}
  ", Er.call("Le.refl", ["a"]), "

def Le.trans(", all, ", +x: T, +y: T, +w3: T, +p: ", Er.LE("x", "y"), ", +q: ", Er.LE("y", "w3"), ") -> ", Er.LE("x", "w3"), ":
  ", Er.PR(Er.add(wy, yx), Er.add("w3", Er.neg("x")), Er.NORM(["x", "y", "w3"], p(p(v(2n), n(v(1n))), p(v(1n), n(v(0n)))), p(v(2n), n(v(0n)))), D.cat(["pos_add(", wy, ", ", yx, ", q, p)"])), "

def Le.add(", all, ", +x1: T, +y1: T, +x2: T, +y2: T, +p1: ", Er.LE("x1", "y1"), ", +p2: ", Er.LE("x2", "y2"), ") -> ", Er.LE(Er.add("x1", "x2"), Er.add("y1", "y2")), ":
  ", Er.PR(Er.add(y1x1, y2x2), Er.add(Er.add("y1", "y2"), Er.neg(Er.add("x1", "x2"))), Er.NORM(["x1", "y1", "x2", "y2"], p(p(v(1n), n(v(0n))), p(v(3n), n(v(2n)))), p(p(v(1n), v(3n)), n(p(v(0n), v(2n))))), D.cat(["pos_add(", y1x1, ", ", y2x2, ", p1, p2)"])), "

def Le.scale(", all, ", +c: T, +x: T, +y: T, +pc: ", Er.POS("c"), ", +p: ", Er.LE("x", "y"), ") -> ", Er.LE(Er.mul("c", "x"), Er.mul("c", "y")), ":
  ", Er.PR(Er.mul("c", yx_), Er.add(Er.mul("c", "y"), Er.neg(Er.mul("c", "x"))), Er.NORM(["c", "x", "y"], m(v(0n), p(v(2n), n(v(1n)))), p(m(v(0n), v(2n)), n(m(v(0n), v(1n))))), D.cat(["pos_mul(c, ", yx_, ", pc, p)"])), "

def Le.scale_r(", all, ", +c: T, +x: T, +y: T, +pc: ", Er.POS("c"), ", +p: ", Er.LE("x", "y"), ") -> ", Er.LE(Er.mul("x", "c"), Er.mul("y", "c")), ":
  ", Er.PR(Er.mul(yx_, "c"), Er.add(Er.mul("y", "c"), Er.neg(Er.mul("x", "c"))), Er.NORM(["c", "x", "y"], m(p(v(2n), n(v(1n))), v(0n)), p(m(v(2n), v(0n)), n(m(v(1n), v(0n))))), D.cat(["pos_mul(", yx_, ", c, p, pc)"])), "

def Le.zero(", all, ", +x: T, +p: ", Er.POS("x"), ") -> ", Er.LE("zero", "x"), ":
  ", Er.PR("x", Er.add("x", Er.neg("zero")), Er.NORM(["x"], v(0n), p(v(0n), n(z()))), "p"), "

def Le.mul2(", all, ", +x1: T, +y1: T, +x2: T, +y2: T, +p1: ", Er.LE("x1", "y1"), ", +p2: ", Er.LE("x2", "y2"), ", +px2: ", Er.POS("x2"), ", +py1: ", Er.POS("y1"), ")
  -> ", Er.LE(Er.mul("x1", "x2"), Er.mul("y1", "y2")), ":
  ", Er.trans(Er.mul("x1", "x2"), Er.mul("y1", "x2"), Er.mul("y1", "y2"), Er.call("Le.scale_r", ["x2", "x1", "y1", "px2", "p1"]), Er.call("Le.scale", ["y1", "x2", "y2", "py1", "p2"])), "

# |x| <= |x - y| + |y|
def Le.split(", all, ", +x: T, +y: T) -> ", Er.LE(Er.ab("x"), Er.add(Er.ab(xy), Er.ab("y"))), ":
  ", Er.trans(Er.ab("x"), Er.ab(xyy), Er.add(Er.ab(xy), Er.ab("y")),
     Er.call("Le.eq", [Er.ab("x"), Er.ab(xyy), Er.congabs("x", xyy, Er.esym(xyy, "x", Er.NORM(["x", "y"], p(p(v(0n), n(v(1n))), v(1n)), v(0n))))]),
     D.cat(["tri(", xy, ", y)"])), "
"])

# h
# -

def Er.H(+k: String) -> String:
  D.cat(["E.Err.H(~T, ~zero, ~one, ~add, ~mul, ~eps, ", k, ")"])

# h(m + 1) = h(m) + eps h(m) + eps
def Er.U(+x: String) -> String:
  Er.add(Er.add(x, Er.mul("eps", x)), "eps")

def Er.HADD(+a: String, +b: String) -> String:
  Er.add(Er.add(Er.H(a), Er.H(b)), Er.mul(Er.H(a), Er.H(b)))

def Er.hs() -> String:
  +all = Er.ALL()
  +hj = Er.H("j")
  +hk = Er.H("k")
  +hi = Er.H("i")
  +eh = Er.mul("eps", hj)
  +ap = Er.H("ap")
  +hb = Er.H("b")
  +nab = Er.H("Nat.add(ap, b)")
  +hab = Er.HADD("ap", "b")
  +h1ab = Er.HADD("1n+ap", "b")
  D.cat(["
# h
# -

# h(j + 1) = h(j) + eps h(j) + eps
def H.unfold(", all, ", +j: Nat) -> ", Er.EQ(Er.H("1n+j"), Er.U(hj)), ":
  Equal.cong(T, T, w => add(w, eps), mul(add(one, eps), ", hj, "), add(", hj, ", mul(eps, ", hj, ")),
    ", Er.etrans(Er.mul("add(one, eps)", hj), Er.add(Er.mul("one", hj), eh), Er.add(hj, eh),
       D.cat(["NP.Alg.dist_r(~T, ~add, ~mul, ~mc, ~dl, one, eps, ", hj, ")"]),
       D.cat(["Equal.cong(T, T, w => add(w, mul(eps, ", hj, ")), mul(one, ", hj, "), ", hj, ", NP.Alg.unit_l(~T, ~mul, ~one, ~mc, ~u, ", hj, "))"])), ")

def H.pos(", all, ", +j: Nat) -> ", Er.POS(hj), ":
  match j:
    case 0n:
      ", Er.call0("Pos.zero"), "
    case 1n+k:
      +ih = ", Er.call("H.pos", ["k"]), "
      ", Er.PR(Er.U(hk), Er.H("1n+k"), Er.esym(Er.H("1n+k"), Er.U(hk), Er.call("H.unfold", ["k"])),
         D.cat(["pos_add(", Er.add(hk, Er.mul("eps", hk)), ", eps, pos_add(", hk, ", ", Er.mul("eps", hk), ", ih, pos_mul(eps, ", hk, ", pos_eps, ih)), pos_eps)"])), "

def H.succ(", all, ", +i: Nat, +j: Nat, +p: ", Er.LE(hi, hj), ") -> ", Er.LE(Er.H("1n+i"), Er.H("1n+j")), ":
  ", Er.trans(Er.H("1n+i"), Er.U(hi), Er.H("1n+j"), Er.call("Le.eq", [Er.H("1n+i"), Er.U(hi), Er.call("H.unfold", ["i"])]),
     Er.trans(Er.U(hi), Er.U(hj), Er.H("1n+j"),
       Er.call("Le.add", [Er.add(hi, Er.mul("eps", hi)), Er.add(hj, eh), "eps", "eps",
         Er.call("Le.add", [hi, hj, Er.mul("eps", hi), eh, "p", Er.call("Le.scale", ["eps", hi, hj, "pos_eps", "p"])]),
         Er.call("Le.refl", ["eps"])]),
       Er.call("Le.eq", [Er.U(hj), Er.H("1n+j"), Er.esym(Er.H("1n+j"), Er.U(hj), Er.call("H.unfold", ["j"]))]))), "

def H.max_l(", all, ", +a: Nat, +b: Nat) -> ", Er.LE(Er.H("a"), Er.H("Nat.max(a, b)")), ":
  match a b:
    case 0n b2:
      ", Er.call("Le.zero", [Er.H("b2"), Er.call("H.pos", ["b2"])]), "
    case 1n+ap 0n:
      ", Er.call("Le.refl", [Er.H("1n+ap")]), "
    case 1n+ap 1n+bp:
      ", Er.call("H.succ", ["ap", "Nat.max(ap, bp)", Er.call("H.max_l", ["ap", "bp"])]), "

def H.max_r(", all, ", +a: Nat, +b: Nat) -> ", Er.LE(hb, Er.H("Nat.max(a, b)")), ":
  match a b:
    case 0n b2:
      ", Er.call("Le.refl", [Er.H("b2")]), "
    case 1n+ap 0n:
      ", Er.call("Le.zero", [Er.H("1n+ap"), Er.call("H.pos", ["1n+ap"])]), "
    case 1n+ap 1n+bp:
      ", Er.call("H.succ", ["bp", "Nat.max(ap, bp)", Er.call("H.max_r", ["ap", "bp"])]), "

# h(a + b) = h(a) + h(b) + h(a) h(b): (1 + eps)^(a+b) splits
def H.add(", all, ", +a: Nat, +b: Nat) -> ", Er.EQ(Er.H("Nat.add(a, b)"), Er.HADD("a", "b")), ":
  match a:
    case 0n:
      ", Er.NORM([hb], v(0n), p(p(z(), v(0n)), m(z(), v(0n)))), "
    case 1n+ap:
      ", Er.etrans(Er.H("1n+Nat.add(ap, b)"), Er.U(nab), h1ab,
         Er.call("H.unfold", ["Nat.add(ap, b)"]),
         Er.etrans(Er.U(nab), Er.U(hab), h1ab,
           D.cat(["Equal.cong(T, T, w => ", Er.U("w"), ", ", nab, ", ", hab, ", ", Er.call("H.add", ["ap", "b"]), ")"]),
           Er.etrans(Er.U(hab), Er.add(Er.add(Er.U(ap), hb), Er.mul(Er.U(ap), hb)), h1ab,
             Er.NORM([ap, hb, "eps"], p(p(p(p(v(0n), v(1n)), m(v(0n), v(1n))), m(v(2n), p(p(v(0n), v(1n)), m(v(0n), v(1n))))), v(2n)), p(p(p(p(v(0n), m(v(2n), v(0n))), v(2n)), v(1n)), m(p(p(v(0n), m(v(2n), v(0n))), v(2n)), v(1n)))),
             D.cat(["Equal.cong(T, T, w => add(add(w, ", hb, "), mul(w, ", hb, ")), ", Er.U(ap), ", ", Er.H("1n+ap"), ", ", Er.esym(Er.H("1n+ap"), Er.U(ap), Er.call("H.unfold", ["ap"])), ")"])))), "
"])

# Terms
# -----

def Er.EV(+t: String) -> String:
  D.cat(["N.Tm.eval(~T, ~zero, ~add, ~mul, ~neg, env, ", t, ")"])

def Er.FL(+t: String) -> String:
  D.cat(["E.Tm.fl(~T, ~zero, ~add, ~mul, ~neg, ~rnd, env, ", t, ")"])

def Er.FLU(+t: String) -> String:
  D.cat(["E.Tm.flu(~T, ~zero, ~add, ~mul, ~neg, ~rnda, ~rndm, env, ", t, ")"])

def Er.AB(+t: String) -> String:
  D.cat(["E.Tm.absev(~T, ~zero, ~add, ~mul, ~abs, env, ", t, ")"])

def Er.DD(+t: String) -> String:
  D.cat(["E.Err.D(~T, ~zero, ~one, ~add, ~mul, ~abs, ~eps, ~eta_a, ~eta_m, env, ", t, ")"])

def Er.K(+t: String) -> String:
  D.cat(["E.Tm.k(", t, ")"])

def Er.Xv() -> String:
  "N.Env.at(~T, ~zero, env, i)"

def Er.ENV() -> String:
  "+env: List<&2, T>"

def Er.callE(+name: String, args: List<&2, String>) -> String:
  D.cat([name, "(", Er.A(), ", env, ", D.sep(args, ", "), ")"])

def Er.terms() -> String:
  +all = Er.ALL()
  +env = Er.ENV()
  +x = Er.Xv()
  +a = Er.AB("a")
  +b = Er.AB("b")
  +ea = Er.EV("a")
  +eb = Er.EV("b")
  +pa = Er.callE("Absev.pos", ["a"])
  +pb = Er.callE("Absev.pos", ["b"])
  +va = Er.callE("Ev.le", ["a"])
  +vb = Er.callE("Ev.le", ["b"])
  D.cat(["
# Terms
# -----

def Absev.pos(", all, ", ", env, ", t: N.Tm) -> ", Er.POS(Er.AB("t")), ":
  match t:
    case N.TVar{+i}:
      pos_abs(", x, ")
    case N.TZero{}:
      ", Er.call0("Pos.zero"), "
    case N.TAdd{+a, +b}:
      pos_add(", a, ", ", b, ", ", pa, ", ", pb, ")
    case N.TMul{+a, +b}:
      pos_mul(", a, ", ", b, ", ", pa, ", ", pb, ")
    case N.TNeg{+a}:
      ", pa, "

# the exact value is at most the absolute size: |eval(t)| <= absev(t)
def Ev.le(", all, ", ", env, ", t: N.Tm) -> ", Er.LE(Er.ab(Er.EV("t")), Er.AB("t")), ":
  match t:
    case N.TVar{+i}:
      ", Er.call("Le.refl", [Er.ab(x)]), "
    case N.TZero{}:
      ", Er.call("Le.eq", [Er.ab("zero"), "zero", "abs_zero"]), "
    case N.TAdd{+a, +b}:
      ", Er.trans(Er.ab(Er.add(ea, eb)), Er.add(Er.ab(ea), Er.ab(eb)), Er.add(a, b), D.cat(["tri(", ea, ", ", eb, ")"]),
         Er.call("Le.add", [Er.ab(ea), a, Er.ab(eb), b, va, vb])), "
    case N.TMul{+a, +b}:
      ", Er.trans(Er.ab(Er.mul(ea, eb)), Er.mul(Er.ab(ea), Er.ab(eb)), Er.mul(a, b), Er.call("Le.eq", [Er.ab(Er.mul(ea, eb)), Er.mul(Er.ab(ea), Er.ab(eb)), D.cat(["abs_mul(", ea, ", ", eb, ")"])]),
         Er.call("Le.mul2", [Er.ab(ea), a, Er.ab(eb), b, va, vb, D.cat(["pos_abs(", eb, ")"]), pa])), "
    case N.TNeg{+a}:
      ", Er.trans(Er.ab(Er.neg(ea)), Er.ab(ea), a, Er.call("Le.eq", [Er.ab(Er.neg(ea)), Er.ab(ea), D.cat(["abs_neg(", ea, ")"])]), va), "
"])

# The theorem
# -----------

def Er.callR(+name: String, args: List<&2, String>) -> String:
  D.cat([name, "(", Er.A(), ", ~rnd, ~rnd_ok, env, ", D.sep(args, ", "), ")"])

def Er.ETAA() -> String:
  "~eta_a, ~eta_m, ~pos_eta_a, ~pos_eta_m"

def Er.callD(+name: String, args: List<&2, String>) -> String:
  D.cat([name, "(", Er.A(), ", ", Er.ETAA(), ", env, ", D.sep(args, ", "), ")"])

def Er.callU(+name: String, args: List<&2, String>) -> String:
  D.cat([name, "(", Er.A(), ", ", Er.ETAA(), ", ~rnda, ~rndm, ~rnda_ok, ~rndm_ok, env, ", D.sep(args, ", "), ")"])

def Er.Mx() -> String:
  D.cat(["Nat.max(", Er.K("a"), ", ", Er.K("b"), ")"])

def Er.Ks() -> String:
  D.cat(["Nat.add(", Er.K("a"), ", ", Er.K("b"), ")"])

# |r - (ea + eb)| = |R + (Ea + Eb)| with R = r - (fa + fb), Ex = fx - ex
def Er.split_add(+rs: String, +fa: String, +fb: String, +ea: String, +eb: String) -> String:
  +l = Er.ab(Er.add(rs, Er.neg(Er.add(ea, eb))))
  +r = Er.add(Er.add(rs, Er.neg(Er.add(fa, fb))), Er.add(Er.add(fa, Er.neg(ea)), Er.add(fb, Er.neg(eb))))
  Er.call("Le.eq", [l, Er.ab(r), Er.congabs(Er.add(rs, Er.neg(Er.add(ea, eb))), r,
    Er.NORM([rs, fa, fb, ea, eb], p(v(0n), n(p(v(3n), v(4n)))), p(p(v(0n), n(p(v(1n), v(2n)))), p(p(v(1n), n(v(3n))), p(v(2n), n(v(4n)))))))])

# |r - ea eb| = |R + (Ea fb + ea Eb)| with R = r - fa fb
def Er.split_mul(+rs: String, +fa: String, +fb: String, +ea: String, +eb: String) -> String:
  +l = Er.ab(Er.add(rs, Er.neg(Er.mul(ea, eb))))
  +r = Er.add(Er.add(rs, Er.neg(Er.mul(fa, fb))), Er.add(Er.mul(Er.add(fa, Er.neg(ea)), fb), Er.mul(ea, Er.add(fb, Er.neg(eb)))))
  Er.call("Le.eq", [l, Er.ab(r), Er.congabs(Er.add(rs, Er.neg(Er.mul(ea, eb))), r,
    Er.NORM([rs, fa, fb, ea, eb], p(v(0n), n(m(v(3n), v(4n)))), p(p(v(0n), n(m(v(1n), v(2n)))), p(m(p(v(1n), n(v(3n))), v(2n)), m(v(3n), p(v(2n), n(v(4n))))))))])

# |-fa - -ea| = |Ea|
def Er.negstep(+fa: String, +ea: String) -> String:
  +ea_ = Er.add(fa, Er.neg(ea))
  +l = Er.ab(Er.add(Er.neg(fa), Er.neg(Er.neg(ea))))
  Er.call("Le.eq", [l, Er.ab(ea_), Er.etrans(l, Er.ab(Er.neg(ea_)), Er.ab(ea_),
     Er.congabs(Er.add(Er.neg(fa), Er.neg(Er.neg(ea))), Er.neg(ea_), Er.NORM([fa, ea], p(n(v(0n)), n(n(v(1n)))), n(p(v(0n), n(v(1n)))))), D.cat(["abs_neg(", ea_, ")"]))])

# |x - x| = 0
def Er.selfstep(+x: String) -> String:
  Er.call("Le.eq", [Er.ab(Er.add(x, Er.neg(x))), "zero", Er.etrans(Er.ab(Er.add(x, Er.neg(x))), Er.ab("zero"), "zero", Er.congabs(Er.add(x, Er.neg(x)), "zero", D.cat(["inv(", x, ")"])), "abs_zero")])

# |f| <= Hm X + X, from |f - e| <= Hx X
def Er.fbound(+f: String, +e: String, +ax: String, +hx: String, +hm: String, +bx: String, +vx: String, +hle: String, +pax: String) -> String:
  +fe = Er.ab(Er.add(f, Er.neg(e)))
  Er.trans(Er.ab(f), Er.add(fe, Er.ab(e)), Er.add(Er.mul(hm, ax), ax), Er.call("Le.split", [f, e]),
    Er.trans(Er.add(fe, Er.ab(e)), Er.add(Er.mul(hx, ax), ax), Er.add(Er.mul(hm, ax), ax), Er.call("Le.add", [fe, Er.mul(hx, ax), Er.ab(e), ax, bx, vx]),
      Er.call("Le.add", [Er.mul(hx, ax), Er.mul(hm, ax), ax, ax, Er.call("Le.scale_r", [ax, hx, hm, pax, hle]), Er.call("Le.refl", [ax])])))

def Er.b.add() -> String:
  +fa = Er.FL("a")
  +fb = Er.FL("b")
  +ea = Er.EV("a")
  +eb = Er.EV("b")
  +a = Er.AB("a")
  +b = Er.AB("b")
  +ha = Er.H(Er.K("a"))
  +hb = Er.H(Er.K("b"))
  +mx = Er.Mx()
  +hm = Er.H(mx)
  +xa = Er.add(fa, Er.neg(ea))
  +xb = Er.add(fb, Er.neg(eb))
  +ba = Er.callR("Err.bound", ["a"])
  +bb = Er.callR("Err.bound", ["b"])
  +va = Er.callE("Ev.le", ["a"])
  +vb = Er.callE("Ev.le", ["b"])
  +pa = Er.callE("Absev.pos", ["a"])
  +pb = Er.callE("Absev.pos", ["b"])
  +hla = Er.call("H.max_l", [Er.K("a"), Er.K("b")])
  +hrb = Er.call("H.max_r", [Er.K("a"), Er.K("b")])
  +s = Er.add(fa, fb)
  +rs = D.cat(["rnd(", s, ")"])
  +r = Er.add(rs, Er.neg(s))
  +e2 = D.cat(["tri(", r, ", ", Er.add(xa, xb), ")"])
  +e3 = Er.call("Le.add", [Er.ab(r), Er.mul("eps", Er.ab(s)), Er.ab(Er.add(xa, xb)), Er.add(Er.ab(xa), Er.ab(xb)), D.cat(["rnd_ok(", s, ")"]), D.cat(["tri(", xa, ", ", xb, ")"])])
  +sbt = Er.add(Er.add(Er.mul(hm, a), a), Er.add(Er.mul(hm, b), b))
  +sb = Er.trans(Er.ab(s), Er.add(Er.ab(fa), Er.ab(fb)), sbt, D.cat(["tri(", fa, ", ", fb, ")"]), Er.call("Le.add", [Er.ab(fa), Er.add(Er.mul(hm, a), a), Er.ab(fb), Er.add(Er.mul(hm, b), b), Er.fbound(fa, ea, a, ha, hm, ba, va, hla, pa), Er.fbound(fb, eb, b, hb, hm, bb, vb, hrb, pb)]))
  +es = Er.call("Le.scale", ["eps", Er.ab(s), sbt, "pos_eps", sb])
  +ee = Er.call("Le.add", [Er.ab(xa), Er.mul(hm, a), Er.ab(xb), Er.mul(hm, b),
    Er.trans(Er.ab(xa), Er.mul(ha, a), Er.mul(hm, a), ba, Er.call("Le.scale_r", [a, ha, hm, pa, hla])),
    Er.trans(Er.ab(xb), Er.mul(hb, b), Er.mul(hm, b), bb, Er.call("Le.scale_r", [b, hb, hm, pb, hrb]))])
  +e4 = Er.call("Le.add", [Er.mul("eps", Er.ab(s)), Er.mul("eps", sbt), Er.add(Er.ab(xa), Er.ab(xb)), Er.add(Er.mul(hm, a), Er.mul(hm, b)), es, ee])
  +l4 = Er.add(Er.mul("eps", sbt), Er.add(Er.mul(hm, a), Er.mul(hm, b)))
  +h1 = Er.H(D.cat(["1n+", mx]))
  +ga = Er.mul(h1, Er.add(a, b))
  +fin = Er.call("Le.eq", [l4, ga, Er.etrans(l4, Er.mul(Er.U(hm), Er.add(a, b)), ga,
    Er.NORM(["eps", hm, a, b], p(m(v(0n), p(p(m(v(1n), v(2n)), v(2n)), p(m(v(1n), v(3n)), v(3n)))), p(m(v(1n), v(2n)), m(v(1n), v(3n)))), m(p(p(v(1n), m(v(0n), v(1n))), v(0n)), p(v(2n), v(3n)))),
    D.cat(["Equal.cong(T, T, w => mul(w, ", Er.add(a, b), "), ", Er.U(hm), ", ", h1, ", ", Er.esym(h1, Er.U(hm), Er.call("H.unfold", [mx])), ")"]))])
  +g1 = Er.ab(Er.add(r, Er.add(xa, xb)))
  +g2 = Er.add(Er.ab(r), Er.ab(Er.add(xa, xb)))
  +g3 = Er.add(Er.mul("eps", Er.ab(s)), Er.add(Er.ab(xa), Er.ab(xb)))
  Er.trans(Er.ab(Er.add(rs, Er.neg(Er.add(ea, eb)))), g1, ga, Er.split_add(rs, fa, fb, ea, eb),
    Er.trans(g1, g2, ga, e2, Er.trans(g2, g3, ga, e3, Er.trans(g3, l4, ga, e4, fin))))

def Er.b.mul() -> String:
  +fa = Er.FL("a")
  +fb = Er.FL("b")
  +ea = Er.EV("a")
  +eb = Er.EV("b")
  +a = Er.AB("a")
  +b = Er.AB("b")
  +ha = Er.H(Er.K("a"))
  +hb = Er.H(Er.K("b"))
  +xa = Er.add(fa, Er.neg(ea))
  +xb = Er.add(fb, Er.neg(eb))
  +ba = Er.callR("Err.bound", ["a"])
  +bb = Er.callR("Err.bound", ["b"])
  +va = Er.callE("Ev.le", ["a"])
  +vb = Er.callE("Ev.le", ["b"])
  +pa = Er.callE("Absev.pos", ["a"])
  +s = Er.mul(fa, fb)
  +rs = D.cat(["rnd(", s, ")"])
  +r = Er.add(rs, Er.neg(s))
  +t1 = Er.mul(xa, fb)
  +t2 = Er.mul(ea, xb)
  +m2 = D.cat(["tri(", r, ", ", Er.add(t1, t2), ")"])
  +m3 = Er.call("Le.add", [Er.ab(r), Er.mul("eps", Er.ab(s)), Er.ab(Er.add(t1, t2)), Er.add(Er.ab(t1), Er.ab(t2)), D.cat(["rnd_ok(", s, ")"]), D.cat(["tri(", t1, ", ", t2, ")"])])
  +fbt = Er.add(Er.mul(hb, b), b)
  +fat = Er.add(Er.mul(ha, a), a)
  +fbb = Er.trans(Er.ab(fb), Er.add(Er.ab(xb), Er.ab(eb)), fbt, Er.call("Le.split", [fb, eb]), Er.call("Le.add", [Er.ab(xb), Er.mul(hb, b), Er.ab(eb), b, bb, vb]))
  +fab = Er.trans(Er.ab(fa), Er.add(Er.ab(xa), Er.ab(ea)), fat, Er.call("Le.split", [fa, ea]), Er.call("Le.add", [Er.ab(xa), Er.mul(ha, a), Er.ab(ea), a, ba, va]))
  +phaa = Er.pos_mul(ha, a, Er.call("H.pos", [Er.K("a")]), pa)
  +s1 = Er.trans(Er.ab(t1), Er.mul(Er.ab(xa), Er.ab(fb)), Er.mul(Er.mul(ha, a), fbt), Er.call("Le.eq", [Er.ab(t1), Er.mul(Er.ab(xa), Er.ab(fb)), D.cat(["abs_mul(", xa, ", ", fb, ")"])]),
    Er.call("Le.mul2", [Er.ab(xa), Er.mul(ha, a), Er.ab(fb), fbt, ba, fbb, D.cat(["pos_abs(", fb, ")"]), phaa]))
  +s2 = Er.trans(Er.ab(t2), Er.mul(Er.ab(ea), Er.ab(xb)), Er.mul(a, Er.mul(hb, b)), Er.call("Le.eq", [Er.ab(t2), Er.mul(Er.ab(ea), Er.ab(xb)), D.cat(["abs_mul(", ea, ", ", xb, ")"])]),
    Er.call("Le.mul2", [Er.ab(ea), a, Er.ab(xb), Er.mul(hb, b), va, bb, D.cat(["pos_abs(", xb, ")"]), pa]))
  +ss = Er.mul(fat, fbt)
  +sbm = Er.trans(Er.ab(s), Er.mul(Er.ab(fa), Er.ab(fb)), ss, Er.call("Le.eq", [Er.ab(s), Er.mul(Er.ab(fa), Er.ab(fb)), D.cat(["abs_mul(", fa, ", ", fb, ")"])]),
    Er.call("Le.mul2", [Er.ab(fa), fat, Er.ab(fb), fbt, fab, fbb, D.cat(["pos_abs(", fb, ")"]), Er.pos_add(Er.mul(ha, a), a, phaa, pa)]))
  +esm = Er.call("Le.scale", ["eps", Er.ab(s), ss, "pos_eps", sbm])
  +rest = Er.add(Er.mul(Er.mul(ha, a), fbt), Er.mul(a, Er.mul(hb, b)))
  +m4 = Er.call("Le.add", [Er.mul("eps", Er.ab(s)), Er.mul("eps", ss), Er.add(Er.ab(t1), Er.ab(t2)), rest, esm,
    Er.call("Le.add", [Er.ab(t1), Er.mul(Er.mul(ha, a), fbt), Er.ab(t2), Er.mul(a, Er.mul(hb, b)), s1, s2])])
  +l4 = Er.add(Er.mul("eps", ss), rest)
  +ks = Er.Ks()
  +hks = Er.H(ks)
  +h1 = Er.H(D.cat(["1n+", ks]))
  +ab_ = Er.mul(a, b)
  +gm = Er.mul(h1, ab_)
  +hab = Er.add(Er.add(ha, hb), Er.mul(ha, hb))
  +fin = Er.call("Le.eq", [l4, gm, Er.etrans(l4, Er.mul(Er.U(hab), ab_), gm,
    Er.NORM(["eps", ha, hb, a, b], p(m(v(0n), m(p(m(v(1n), v(3n)), v(3n)), p(m(v(2n), v(4n)), v(4n)))), p(m(m(v(1n), v(3n)), p(m(v(2n), v(4n)), v(4n))), m(v(3n), m(v(2n), v(4n))))), m(p(p(p(p(v(1n), v(2n)), m(v(1n), v(2n))), m(v(0n), p(p(v(1n), v(2n)), m(v(1n), v(2n))))), v(0n)), m(v(3n), v(4n)))),
    Er.etrans(Er.mul(Er.U(hab), ab_), Er.mul(Er.U(hks), ab_), gm,
      D.cat(["Equal.cong(T, T, w => mul(", Er.U("w"), ", ", ab_, "), ", hab, ", ", hks, ", ", Er.esym(hks, hab, Er.call("H.add", [Er.K("a"), Er.K("b")])), ")"]),
      D.cat(["Equal.cong(T, T, w => mul(w, ", ab_, "), ", Er.U(hks), ", ", h1, ", ", Er.esym(h1, Er.U(hks), Er.call("H.unfold", [ks])), ")"])))])
  +g1 = Er.ab(Er.add(r, Er.add(t1, t2)))
  +g2 = Er.add(Er.ab(r), Er.ab(Er.add(t1, t2)))
  +g3 = Er.add(Er.mul("eps", Er.ab(s)), Er.add(Er.ab(t1), Er.ab(t2)))
  Er.trans(Er.ab(Er.add(rs, Er.neg(Er.mul(ea, eb)))), g1, gm, Er.split_mul(rs, fa, fb, ea, eb),
    Er.trans(g1, g2, gm, m2, Er.trans(g2, g3, gm, m3, Er.trans(g3, l4, gm, m4, fin))))

def Er.bound() -> String:
  +x = Er.Xv()
  +fa = Er.FL("a")
  +ea = Er.EV("a")
  +xa = Er.add(fa, Er.neg(ea))
  +ha_a = Er.mul(Er.H(Er.K("a")), Er.AB("a"))
  D.cat(["
# The theorem
# -----------

# |fl(t) - eval(t)| <= h(k(t)) absev(t)
def Err.bound(", Er.ALL(), ", ", Er.RNDH(), ", ", Er.ENV(), ", t: N.Tm) -> ", Er.LE(Er.ab(Er.add(Er.FL("t"), Er.neg(Er.EV("t")))), Er.mul(Er.H(Er.K("t")), Er.AB("t"))), ":
  match t:
    case N.TVar{+i}:
      ", Er.trans(Er.ab(Er.add(x, Er.neg(x))), "zero", Er.mul("zero", Er.ab(x)), Er.selfstep(x), Er.call("Le.eq", ["zero", Er.mul("zero", Er.ab(x)), Er.NORM([Er.ab(x)], z(), m(z(), v(0n)))])), "
    case N.TZero{}:
      ", Er.trans(Er.ab(Er.add("zero", Er.neg("zero"))), "zero", Er.mul("zero", "zero"), Er.selfstep("zero"), Er.call("Le.eq", ["zero", Er.mul("zero", "zero"), Er.NORM([], z(), m(z(), z()))])), "
    case N.TAdd{+a, +b}:
      ", Er.b.add(), "
    case N.TMul{+a, +b}:
      ", Er.b.mul(), "
    case N.TNeg{+a}:
      ", Er.trans(Er.ab(Er.add(Er.neg(fa), Er.neg(Er.neg(ea)))), Er.ab(xa), ha_a, Er.negstep(fa, ea), Er.callR("Err.bound", ["a"])), "
"])

# With underflow
# --------------

def Er.Ha() -> String:
  Er.H(Er.K("a"))

def Er.Hb() -> String:
  Er.H(Er.K("b"))

# F(x) = h(k(x)) absev(x) + absev(x), and its positivity
def Er.F(+h: String, +a: String) -> String:
  Er.add(Er.mul(h, a), a)

def Er.pF(+h: String, +a: String, +ph: String, +pa: String) -> String:
  Er.pos_add(Er.mul(h, a), a, Er.pos_mul(h, a, ph, pa), pa)

# X = F(a) D(b) + D(a) F(b) + D(a) D(b), as in E.Err.D
def Er.Xm() -> String:
  +fa = Er.F(Er.Ha(), Er.AB("a"))
  +fb = Er.F(Er.Hb(), Er.AB("b"))
  +da = Er.DD("a")
  +db = Er.DD("b")
  Er.add(Er.add(Er.mul(fa, db), Er.mul(da, fb)), Er.mul(da, db))

def Er.pXm() -> String:
  +a = Er.AB("a")
  +b = Er.AB("b")
  +fa = Er.F(Er.Ha(), a)
  +fb = Er.F(Er.Hb(), b)
  +da = Er.DD("a")
  +db = Er.DD("b")
  +pda = Er.callD("D.pos", ["a"])
  +pdb = Er.callD("D.pos", ["b"])
  +pfa = Er.pF(Er.Ha(), a, Er.call("H.pos", [Er.K("a")]), Er.callE("Absev.pos", ["a"]))
  +pfb = Er.pF(Er.Hb(), b, Er.call("H.pos", [Er.K("b")]), Er.callE("Absev.pos", ["b"]))
  Er.pos_add(Er.add(Er.mul(fa, db), Er.mul(da, fb)), Er.mul(da, db),
    Er.pos_add(Er.mul(fa, db), Er.mul(da, fb), Er.pos_mul(fa, db, pfa, pdb), Er.pos_mul(da, fb, pda, pfb)), Er.pos_mul(da, db, pda, pdb))

def Er.dpos() -> String:
  +sa = Er.add(Er.DD("a"), Er.DD("b"))
  +ps = Er.pos_add(Er.DD("a"), Er.DD("b"), Er.callD("D.pos", ["a"]), Er.callD("D.pos", ["b"]))
  +x = Er.Xm()
  +px = Er.pXm()
  D.cat(["
# With underflow
# --------------

def D.pos(", Er.ALL(), ", ", Er.ETAH(), ", ", Er.ENV(), ", t: N.Tm) -> ", Er.POS(Er.DD("t")), ":
  match t:
    case N.TVar{+i}:
      ", Er.call0("Pos.zero"), "
    case N.TZero{}:
      ", Er.call0("Pos.zero"), "
    case N.TAdd{+a, +b}:
      ", Er.pos_add("eta_a", Er.add(sa, Er.mul("eps", sa)), "pos_eta_a", Er.pos_add(sa, Er.mul("eps", sa), ps, Er.pos_mul("eps", sa, "pos_eps", ps))), "
    case N.TMul{+a, +b}:
      ", Er.pos_add("eta_m", Er.add(x, Er.mul("eps", x)), "pos_eta_m", Er.pos_add(x, Er.mul("eps", x), px, Er.pos_mul("eps", x, "pos_eps", px))), "
    case N.TNeg{+a}:
      ", Er.callD("D.pos", ["a"]), "
"])

# |f| <= (Hx X + Dx) + X, from |f - e| <= Hx X + Dx
def Er.fbnd(+f: String, +e: String, +ax: String, +hx: String, +dx: String, +bx: String, +vx: String) -> String:
  +fe = Er.ab(Er.add(f, Er.neg(e)))
  Er.trans(Er.ab(f), Er.add(fe, Er.ab(e)), Er.add(Er.add(Er.mul(hx, ax), dx), ax), Er.call("Le.split", [f, e]),
    Er.call("Le.add", [fe, Er.add(Er.mul(hx, ax), dx), Er.ab(e), ax, bx, vx]))

# Hx X + Dx <= Hm X + Dx, and with + X on both sides
def Er.raise1(+ax: String, +hx: String, +hm: String, +dx: String, +hle: String, +pax: String) -> String:
  Er.call("Le.add", [Er.mul(hx, ax), Er.mul(hm, ax), dx, dx, Er.call("Le.scale_r", [ax, hx, hm, pax, hle]), Er.call("Le.refl", [dx])])

def Er.raise2(+ax: String, +hx: String, +hm: String, +dx: String, +hle: String, +pax: String) -> String:
  Er.call("Le.add", [Er.add(Er.mul(hx, ax), dx), Er.add(Er.mul(hm, ax), dx), ax, ax, Er.raise1(ax, hx, hm, dx, hle, pax), Er.call("Le.refl", [ax])])

def Er.u.add() -> String:
  +fa = Er.FLU("a")
  +fb = Er.FLU("b")
  +ea = Er.EV("a")
  +eb = Er.EV("b")
  +a = Er.AB("a")
  +b = Er.AB("b")
  +ha = Er.Ha()
  +hb = Er.Hb()
  +da = Er.DD("a")
  +db = Er.DD("b")
  +mx = Er.Mx()
  +hm = Er.H(mx)
  +xa = Er.add(fa, Er.neg(ea))
  +xb = Er.add(fb, Er.neg(eb))
  +ba = Er.callU("Err.bound_u", ["a"])
  +bb = Er.callU("Err.bound_u", ["b"])
  +va = Er.callE("Ev.le", ["a"])
  +vb = Er.callE("Ev.le", ["b"])
  +pa = Er.callE("Absev.pos", ["a"])
  +pb = Er.callE("Absev.pos", ["b"])
  +hla = Er.call("H.max_l", [Er.K("a"), Er.K("b")])
  +hrb = Er.call("H.max_r", [Er.K("a"), Er.K("b")])
  +s = Er.add(fa, fb)
  +rs = D.cat(["rnda(", s, ")"])
  +r = Er.add(rs, Er.neg(s))
  +at : List<&2, String> = ["eps", hm, a, b, da, db, "eta_a"]
  +famd = p(p(m(v(1n), v(2n)), v(4n)), v(2n))
  +fbmd = p(p(m(v(1n), v(3n)), v(5n)), v(3n))
  +l4d = p(p(m(v(0n), p(famd, fbmd)), v(6n)), p(p(m(v(1n), v(2n)), v(4n)), p(m(v(1n), v(3n)), v(5n))))
  +ud = p(p(v(1n), m(v(0n), v(1n))), v(0n))
  +sad = p(v(4n), v(5n))
  +rhd = p(m(ud, p(v(2n), v(3n))), p(v(6n), p(sad, m(v(0n), sad))))
  +fam = Er.tT(famd, at)
  +fbm = Er.tT(fbmd, at)
  +sbt = Er.add(fam, fbm)
  +l4 = Er.tT(l4d, at)
  +rh = Er.tT(rhd, at)
  +sa = Er.add(da, db)
  +dadd = Er.add("eta_a", Er.add(sa, Er.mul("eps", sa)))
  +h1 = Er.H(D.cat(["1n+", mx]))
  +ga = Er.add(Er.mul(h1, Er.add(a, b)), dadd)
  +e2 = D.cat(["tri(", r, ", ", Er.add(xa, xb), ")"])
  +es = Er.add(Er.mul("eps", Er.ab(s)), "eta_a")
  +e3 = Er.call("Le.add", [Er.ab(r), es, Er.ab(Er.add(xa, xb)), Er.add(Er.ab(xa), Er.ab(xb)), D.cat(["rnda_ok(", s, ")"]), D.cat(["tri(", xa, ", ", xb, ")"])])
  +sb = Er.trans(Er.ab(s), Er.add(Er.ab(fa), Er.ab(fb)), sbt, D.cat(["tri(", fa, ", ", fb, ")"]),
    Er.call("Le.add", [Er.ab(fa), fam, Er.ab(fb), fbm,
      Er.trans(Er.ab(fa), Er.add(Er.add(Er.mul(ha, a), da), a), fam, Er.fbnd(fa, ea, a, ha, da, ba, va), Er.raise2(a, ha, hm, da, hla, pa)),
      Er.trans(Er.ab(fb), Er.add(Er.add(Er.mul(hb, b), db), b), fbm, Er.fbnd(fb, eb, b, hb, db, bb, vb), Er.raise2(b, hb, hm, db, hrb, pb))]))
  +e4 = Er.call("Le.add", [es, Er.add(Er.mul("eps", sbt), "eta_a"), Er.add(Er.ab(xa), Er.ab(xb)), Er.add(Er.add(Er.mul(hm, a), da), Er.add(Er.mul(hm, b), db)),
    Er.call("Le.add", [Er.mul("eps", Er.ab(s)), Er.mul("eps", sbt), "eta_a", "eta_a", Er.call("Le.scale", ["eps", Er.ab(s), sbt, "pos_eps", sb]), Er.call("Le.refl", ["eta_a"])]),
    Er.call("Le.add", [Er.ab(xa), Er.add(Er.mul(hm, a), da), Er.ab(xb), Er.add(Er.mul(hm, b), db),
      Er.trans(Er.ab(xa), Er.add(Er.mul(ha, a), da), Er.add(Er.mul(hm, a), da), ba, Er.raise1(a, ha, hm, da, hla, pa)),
      Er.trans(Er.ab(xb), Er.add(Er.mul(hb, b), db), Er.add(Er.mul(hm, b), db), bb, Er.raise1(b, hb, hm, db, hrb, pb))])])
  +fin = Er.call("Le.eq", [l4, ga, Er.etrans(l4, rh, ga, Er.NORM(at, l4d, rhd),
    D.cat(["Equal.cong(T, T, w => add(mul(w, ", Er.add(a, b), "), ", dadd, "), ", Er.U(hm), ", ", h1, ", ", Er.esym(h1, Er.U(hm), Er.call("H.unfold", [mx])), ")"]))])
  +g1 = Er.ab(Er.add(r, Er.add(xa, xb)))
  +g2 = Er.add(Er.ab(r), Er.ab(Er.add(xa, xb)))
  +g3 = Er.add(es, Er.add(Er.ab(xa), Er.ab(xb)))
  Er.trans(Er.ab(Er.add(rs, Er.neg(Er.add(ea, eb)))), g1, ga, Er.split_add(rs, fa, fb, ea, eb),
    Er.trans(g1, g2, ga, e2, Er.trans(g2, g3, ga, e3, Er.trans(g3, l4, ga, e4, fin))))

def Er.u.mul() -> String:
  +fa = Er.FLU("a")
  +fb = Er.FLU("b")
  +ea = Er.EV("a")
  +eb = Er.EV("b")
  +a = Er.AB("a")
  +b = Er.AB("b")
  +ha = Er.Ha()
  +hb = Er.Hb()
  +da = Er.DD("a")
  +db = Er.DD("b")
  +xa = Er.add(fa, Er.neg(ea))
  +xb = Er.add(fb, Er.neg(eb))
  +ba = Er.callU("Err.bound_u", ["a"])
  +bb = Er.callU("Err.bound_u", ["b"])
  +va = Er.callE("Ev.le", ["a"])
  +vb = Er.callE("Ev.le", ["b"])
  +pa = Er.callE("Absev.pos", ["a"])
  +pda = Er.callD("D.pos", ["a"])
  +s = Er.mul(fa, fb)
  +rs = D.cat(["rndm(", s, ")"])
  +r = Er.add(rs, Er.neg(s))
  +t1 = Er.mul(xa, fb)
  +t2 = Er.mul(ea, xb)
  +at : List<&2, String> = ["eps", ha, hb, a, b, da, db, "eta_m"]
  +fapd = p(p(m(v(1n), v(3n)), v(5n)), v(3n))
  +fbpd = p(p(m(v(2n), v(4n)), v(6n)), v(4n))
  +l4md = p(p(m(v(0n), m(fapd, fbpd)), v(7n)), p(m(p(m(v(1n), v(3n)), v(5n)), fbpd), m(v(3n), p(m(v(2n), v(4n)), v(6n)))))
  +habd = p(p(v(1n), v(2n)), m(v(1n), v(2n)))
  +uhd = p(p(habd, m(v(0n), habd)), v(0n))
  +fad = p(m(v(1n), v(3n)), v(3n))
  +fbd = p(m(v(2n), v(4n)), v(4n))
  +xd = p(p(m(fad, v(6n)), m(v(5n), fbd)), m(v(5n), v(6n)))
  +rhmd = p(m(uhd, m(v(3n), v(4n))), p(v(7n), p(xd, m(v(0n), xd))))
  +fap = Er.tT(fapd, at)
  +fbp = Er.tT(fbpd, at)
  +l4 = Er.tT(l4md, at)
  +rh = Er.tT(rhmd, at)
  +x = Er.Xm()
  +dmul = Er.add("eta_m", Er.add(x, Er.mul("eps", x)))
  +ks = Er.Ks()
  +hks = Er.H(ks)
  +h1 = Er.H(D.cat(["1n+", ks]))
  +ab_ = Er.mul(a, b)
  +gm = Er.add(Er.mul(h1, ab_), dmul)
  +hab = Er.add(Er.add(ha, hb), Er.mul(ha, hb))
  +hda = Er.add(Er.mul(ha, a), da)
  +hdb = Er.add(Er.mul(hb, b), db)
  +m2 = D.cat(["tri(", r, ", ", Er.add(t1, t2), ")"])
  +es = Er.add(Er.mul("eps", Er.ab(s)), "eta_m")
  +m3 = Er.call("Le.add", [Er.ab(r), es, Er.ab(Er.add(t1, t2)), Er.add(Er.ab(t1), Er.ab(t2)), D.cat(["rndm_ok(", s, ")"]), D.cat(["tri(", t1, ", ", t2, ")"])])
  +fab = Er.fbnd(fa, ea, a, ha, da, ba, va)
  +fbb = Er.fbnd(fb, eb, b, hb, db, bb, vb)
  +phda = Er.pos_add(Er.mul(ha, a), da, Er.pos_mul(ha, a, Er.call("H.pos", [Er.K("a")]), pa), pda)
  +pfap = Er.pos_add(hda, a, phda, pa)
  +s1 = Er.trans(Er.ab(t1), Er.mul(Er.ab(xa), Er.ab(fb)), Er.mul(hda, fbp), Er.call("Le.eq", [Er.ab(t1), Er.mul(Er.ab(xa), Er.ab(fb)), D.cat(["abs_mul(", xa, ", ", fb, ")"])]),
    Er.call("Le.mul2", [Er.ab(xa), hda, Er.ab(fb), fbp, ba, fbb, D.cat(["pos_abs(", fb, ")"]), phda]))
  +s2 = Er.trans(Er.ab(t2), Er.mul(Er.ab(ea), Er.ab(xb)), Er.mul(a, hdb), Er.call("Le.eq", [Er.ab(t2), Er.mul(Er.ab(ea), Er.ab(xb)), D.cat(["abs_mul(", ea, ", ", xb, ")"])]),
    Er.call("Le.mul2", [Er.ab(ea), a, Er.ab(xb), hdb, va, bb, D.cat(["pos_abs(", xb, ")"]), pa]))
  +ss = Er.mul(fap, fbp)
  +sbm = Er.trans(Er.ab(s), Er.mul(Er.ab(fa), Er.ab(fb)), ss, Er.call("Le.eq", [Er.ab(s), Er.mul(Er.ab(fa), Er.ab(fb)), D.cat(["abs_mul(", fa, ", ", fb, ")"])]),
    Er.call("Le.mul2", [Er.ab(fa), fap, Er.ab(fb), fbp, fab, fbb, D.cat(["pos_abs(", fb, ")"]), pfap]))
  +rest = Er.add(Er.mul(hda, fbp), Er.mul(a, hdb))
  +m4 = Er.call("Le.add", [es, Er.add(Er.mul("eps", ss), "eta_m"), Er.add(Er.ab(t1), Er.ab(t2)), rest,
    Er.call("Le.add", [Er.mul("eps", Er.ab(s)), Er.mul("eps", ss), "eta_m", "eta_m", Er.call("Le.scale", ["eps", Er.ab(s), ss, "pos_eps", sbm]), Er.call("Le.refl", ["eta_m"])]),
    Er.call("Le.add", [Er.ab(t1), Er.mul(hda, fbp), Er.ab(t2), Er.mul(a, hdb), s1, s2])])
  +fin = Er.call("Le.eq", [l4, gm, Er.etrans(l4, rh, gm, Er.NORM(at, l4md, rhmd),
    Er.etrans(rh, Er.add(Er.mul(Er.U(hks), ab_), dmul), gm,
      D.cat(["Equal.cong(T, T, w => add(mul(", Er.U("w"), ", ", ab_, "), ", dmul, "), ", hab, ", ", hks, ", ", Er.esym(hks, hab, Er.call("H.add", [Er.K("a"), Er.K("b")])), ")"]),
      D.cat(["Equal.cong(T, T, w => add(mul(w, ", ab_, "), ", dmul, "), ", Er.U(hks), ", ", h1, ", ", Er.esym(h1, Er.U(hks), Er.call("H.unfold", [ks])), ")"])))])
  +g1 = Er.ab(Er.add(r, Er.add(t1, t2)))
  +g2 = Er.add(Er.ab(r), Er.ab(Er.add(t1, t2)))
  +g3 = Er.add(es, Er.add(Er.ab(t1), Er.ab(t2)))
  Er.trans(Er.ab(Er.add(rs, Er.neg(Er.mul(ea, eb)))), g1, gm, Er.split_mul(rs, fa, fb, ea, eb),
    Er.trans(g1, g2, gm, m2, Er.trans(g2, g3, gm, m3, Er.trans(g3, l4, gm, m4, fin))))

def Er.bound_u() -> String:
  +x = Er.Xv()
  +fa = Er.FLU("a")
  +ea = Er.EV("a")
  +xa = Er.add(fa, Er.neg(ea))
  +hda = Er.add(Er.mul(Er.Ha(), Er.AB("a")), Er.DD("a"))
  D.cat(["
# |fl(t) - eval(t)| <= h(k(t)) absev(t) + D(t), additions rounded by rnda
# and products by rndm, each within eps |x| + its eta
def Err.bound_u(", Er.ALL(), ", ", Er.ETAH(), ", ", Er.RNDUH(), ", ", Er.ENV(), ", t: N.Tm) -> ", Er.LE(Er.ab(Er.add(Er.FLU("t"), Er.neg(Er.EV("t")))), Er.add(Er.mul(Er.H(Er.K("t")), Er.AB("t")), Er.DD("t"))), ":
  match t:
    case N.TVar{+i}:
      ", Er.trans(Er.ab(Er.add(x, Er.neg(x))), "zero", Er.add(Er.mul("zero", Er.ab(x)), "zero"), Er.selfstep(x), Er.call("Le.eq", ["zero", Er.add(Er.mul("zero", Er.ab(x)), "zero"), Er.NORM([Er.ab(x)], z(), p(m(z(), v(0n)), z()))])), "
    case N.TZero{}:
      ", Er.trans(Er.ab(Er.add("zero", Er.neg("zero"))), "zero", Er.add(Er.mul("zero", "zero"), "zero"), Er.selfstep("zero"), Er.call("Le.eq", ["zero", Er.add(Er.mul("zero", "zero"), "zero"), Er.NORM([], z(), p(m(z(), z()), z()))])), "
    case N.TAdd{+a, +b}:
      ", Er.u.add(), "
    case N.TMul{+a, +b}:
      ", Er.u.mul(), "
    case N.TNeg{+a}:
      ", Er.trans(Er.ab(Er.add(Er.neg(fa), Er.neg(Er.neg(ea)))), Er.ab(xa), hda, Er.negstep(fa, ea), Er.callU("Err.bound_u", ["a"])), "
"])

def Er.text() -> String:
  D.cat([Er.order(), Er.hs(), Er.terms(), Er.bound(), Er.dpos(), Er.bound_u()])
