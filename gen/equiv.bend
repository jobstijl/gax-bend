# Equivariance laws (gax law family D): a versor's sandwich commutes with
# the products, up to a factor,
#   (m >> a) op (m >> b) == |m|² (m >> (a op b)),
# with |m|² the scalar part of m ~m. Where m ~m can have other parts (a
# PGA3D motor's e0123, STA's I), the law assumes that part is zero, the
# condition that makes m a versor. The generator divides the difference of
# the two sides by that relation, giving l with lhs = rhs + l r, and the
# law is proven by proofs/equiv.bend (Rel.eqs): the normaliser checks the
# identity, the hypothesis r = 0 closes it. A curated set of laws per
# algebra: joins, meets and contractions of the geometric kinds.

import Base
import ../src/spec.bend as S
import ../src/norm.bend as N
import ../src/expr.bend as E
import ./gen.bend as G

# a law: the versor kind v, the operation, the operand kinds a and b, the
# result kind c, and p, the kind of v ~v
type Law is Data:
  Law{v: String, o: G.Op, a: String, b: String, c: String, p: String}

def Eq.run(+d: Nat, +sig: S.Sig(d), o: G.Op, x: S.MV(N.Tm, d), y: S.MV(N.Tm, d)) -> S.MV(N.Tm, d):
  match o:
    case G.OGp{}:
      S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, d, sig, x, y)
    case G.OWedge{}:
      S.MV.wedge(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, d, x, y)
    case G.OVee{}:
      S.MV.vee(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, d, x, y)
    case G.OLc{}:
      S.MV.lc(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, d, sig, x, y)
    case G.ORc{}:
      S.MV.rc(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, d, sig, x, y)
    case G.ODot{}:
      S.MV.dot(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, d, sig, x, y)
    case G.OScalar{}:
      S.MV.scalar_product(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, d, sig, x, y)
    case G.OAdd{}:
      S.MV.add(~N.Tm, ~N.Tm.add, d, x, y)
    case G.OSub{}:
      S.MV.add(~N.Tm, ~N.Tm.add, d, x, S.MV.neg(~N.Tm, ~N.Tm.neg, d, y))

# a kind's fields of a tree, in the kind's orientation
def Eq.coefs(+d: Nat, bls: List<&2, G.Bl>, +x: S.MV(N.Tm, d)) -> List<&2, N.Tm>:
  match bls:
    case Nil{}:
      Nil{}
    case G.Bl{n, q, s, g} <> t:
      S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, d, q, s, x) <> Eq.coefs(d, t, x)

# Polynomials: sorted, cancelled lists of monomials
# ------------------------------------------------

def Eq.norm(ms: List<&2, N.Mono>) -> List<&2, N.Mono>:
  N.Cs.go(N.Ms.sort(ms), Nil{})

def Vs.minus.cons(+x: Nat, r: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match r:
    case None{}:
      None{}
    case Some{l}:
      Some{x <> l}

# xs without the multiset ys (both sorted), if ys is inside xs
def Vs.minus(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          Some{Nil{}}
        case y <> yt:
          None{}
    case +x <> +xt:
      match ys:
        case Nil{}:
          Some{x <> xt}
        case +y <> +yt:
          Bool.pick(Maybe<&2, List<&2, Nat>>, Nat.is_eq(x, y), Vs.minus(xt, yt),
            Bool.pick(Maybe<&2, List<&2, Nat>>, Nat.is_lt(x, y), Vs.minus.cons(x, Vs.minus(xt, y <> yt)), None{}))

def Eq.quot(+s: Bool, +ls: Bool, r: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, N.Mono>:
  match r:
    case None{}:
      None{}
    case Some{vs}:
      Some{N.Mono{Bool.xor(s, ls), vs}}

# m / lead, if lead divides m
def Eq.div1(m: N.Mono, lead: N.Mono) -> Maybe<&2, N.Mono>:
  match m lead:
    case N.Mono{s, vs} N.Mono{+ls, lvs}:
      Eq.quot(s, ls, Vs.minus(vs, lvs))

def Eq.first(a: Maybe<&2, N.Mono>, b: Maybe<&2, N.Mono>) -> Maybe<&2, N.Mono>:
  match a:
    case None{}:
      b
    case Some{q}:
      Some{q}

# the first monomial divisible by lead, divided by it
def Eq.find.go(ms: List<&2, N.Mono>, +lead: N.Mono) -> Maybe<&2, N.Mono>:
  match ms:
    case Nil{}:
      None{}
    case m <> t:
      Eq.first(Eq.div1(m, lead), Eq.find.go(t, lead))

def Eq.find(ms: List<&2, N.Mono>, +lead: N.Mono) -> Maybe<&2, N.Mono>:
  Eq.find.go(ms, lead)

# - q r
def Eq.negmul(+q: N.Mono, r: List<&2, N.Mono>) -> List<&2, N.Mono>:
  match r:
    case Nil{}:
      Nil{}
    case m <> t:
      N.Mono.flip(N.Mono.mul(q, m)) <> Eq.negmul(q, t)

type Dv is Data:
  Dv{rem: List<&2, N.Mono>, quot: List<&2, N.Mono>}

# d = rem + quot r, rem with no monomial divisible by lead; found is
# lead's quotient in d's first divisible monomial (fuel-bounded)
def Eq.div(fuel: Nat, +d: List<&2, N.Mono>, +r: List<&2, N.Mono>, +lead: N.Mono, +lam: List<&2, N.Mono>, found: Maybe<&2, N.Mono>) -> Dv:
  match fuel:
    case 0n:
      Dv{d, lam}
    case 1n+f:
      match found:
        case None{}:
          Dv{d, lam}
        case Some{+q}:
          +d2 = Eq.norm(List.append(&2, N.Mono, d, Eq.negmul(q, r)))
          Eq.div(f, d2, r, lead, q <> lam, Eq.find(d2, lead))

def Eq.divide(+d: List<&2, N.Mono>, +r: List<&2, N.Mono>, +lead: N.Mono) -> Dv:
  Eq.div(4096n, d, r, lead, Nil{}, Eq.find(d, lead))

def Ms.last(ms: List<&2, N.Mono>, +dflt: N.Mono) -> N.Mono:
  match ms:
    case Nil{}:
      dflt
    case m <> t:
      Ms.last(t, m)

# Printing terms
# --------------

def Eq.show.vs(vs: List<&2, Nat>) -> String:
  match vs:
    case Nil{}:
      "N.TOne?"
    case +v <> +t:
      Bool.pick(String, List.is_empty(&2, Nat, t), "N.TVar{" ++ Nat.show(v) ++ "n}", "N.TMul{N.TVar{" ++ Nat.show(v) ++ "n}, " ++ Eq.show.vs(t) ++ "}")

def Eq.show.mono(m: N.Mono) -> String:
  match m:
    case N.Mono{s, +vs}:
      Bool.pick(String, s, "N.TNeg{" ++ Eq.show.vs(vs) ++ "}", Eq.show.vs(vs))

def Eq.show.poly(ms: List<&2, N.Mono>) -> String:
  match ms:
    case Nil{}:
      "N.TZero{}"
    case +m <> +t:
      Bool.pick(String, List.is_empty(&2, N.Mono, t), Eq.show.mono(m), "N.TAdd{" ++ Eq.show.mono(m) ++ ", " ++ Eq.show.poly(t) ++ "}")

# The laws
# --------

def Bl.name(b: G.Bl) -> String:
  match b:
    case G.Bl{n, q, s, g}:
      n

def Bl.grade(b: G.Bl) -> Nat:
  match b:
    case G.Bl{n, q, s, g}:
      g

# the scalar field of a kind
def Eq.scalar(bls: List<&2, G.Bl>) -> G.Bl:
  match bls:
    case Nil{}:
      G.Bl{"?", Nil{}, False{}, 0n}
    case +b <> t:
      Bool.pick(G.Bl, Nat.is_eq(Bl.grade(b), 0n), b, Eq.scalar(t))

type Rl is Data:
  Rl{name: String, poly: List<&2, N.Mono>}

def Eq.rels.put(+name: String, +ms: List<&2, N.Mono>, +acc: List<&2, Rl>) -> List<&2, Rl>:
  Bool.pick(List<&2, Rl>, List.is_empty(&2, N.Mono, ms), acc, Rl{name, ms} <> acc)

# the non-scalar parts of m ~m that do not vanish identically
def Eq.rels(+d: Nat, bls: List<&2, G.Bl>, +x: S.MV(N.Tm, d)) -> List<&2, Rl>:
  match bls:
    case Nil{}:
      Nil{}
    case G.Bl{+n, q, s, +g} <> +t:
      Bool.pick(List<&2, Rl>, Nat.is_eq(g, 0n), Eq.rels(d, t, x),
        Eq.rels.put(n, N.NormS.left(S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, d, q, s, x)), Eq.rels(d, t, x)))

def Rl.first(rs: List<&2, Rl>) -> Rl:
  match rs:
    case Nil{}:
      Rl{"?", Nil{}}
    case r <> t:
      r

def Rl.name(r: Rl) -> String:
  match r:
    case Rl{n, p}:
      n

def Rl.poly(r: Rl) -> List<&2, N.Mono>:
  match r:
    case Rl{n, p}:
      p

# l for each field, and whether every remainder vanished
type Ls is Data:
  Ls{texts: List<&2, String>, ok: Bool}

def Eq.ls.cons(dv: Dv, l: Ls) -> Ls:
  match dv l:
    case Dv{rem, quot} Ls{ts, ok}:
      Ls{Eq.show.poly(quot) <> ts, Bool.and(List.is_empty(&2, N.Mono, rem), ok)}

def Eq.ls(lhs: List<&2, N.Tm>, rhs: List<&2, N.Tm>, +nrm: N.Tm, +r: List<&2, N.Mono>, +lead: N.Mono) -> Ls:
  match lhs rhs:
    case l <> lt x <> xt:
      Eq.ls.cons(Eq.divide(N.NormS.left(N.Tm.diff(l, N.TMul{nrm, x})), r, lead), Eq.ls(lt, xt, nrm, r, lead))
    case _ _:
      Ls{Nil{}, True{}}

def Eq.ring() -> String:
  "~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,\n  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),\n  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),\n  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg)"

def Eq.ringa() -> String:
  "~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn"

def Ls.texts(l: Ls) -> List<&2, String>:
  match l:
    case Ls{ts, ok}:
      ts

def Ls.ok(l: Ls) -> Bool:
  match l:
    case Ls{ts, ok}:
      ok

# the law's text: factor -|m|² when minus, the hypothesis r = 0 when rel
# names a relation, l for each field
def Eq.emit(+v: String, +o: G.Op, +a: String, +b: String, +c: String, +p: String, +vb: List<&2, G.Bl>, +ab: List<&2, G.Bl>, +bb: List<&2, G.Bl>,
  +sbn: String, +minus: Bool, +hasr: Bool, +rn: String, +ls: List<&2, String>, +rvo: String) -> String:
  +nm = List.length(&2, G.Bl, vb)
  +na = List.length(&2, G.Bl, ab)
  +name = v ++ "." ++ G.Op.name(o) ++ "." ++ a ++ "." ++ b
  +ops = {"~T, ~zero, ~add, ~mul, ~neg" : String}
  +opst = {"~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg" : String}
  +rvt = Bool.pick(String, String.eq(rvo, "~T, ~zero, ~neg"), "~N.Tm, ~N.TZero{}, ~N.Tm.neg", opst)
  +kop = "O." ++ a ++ "." ++ G.Op.name(o) ++ "." ++ b
  +tm = "K." ++ v ++ "{" ++ String.join(G.Kd.tvars(vb, 0n), ", ") ++ "}"
  +ta = "K." ++ a ++ "{" ++ String.join(G.Kd.tvars(ab, nm), ", ") ++ "}"
  +tb = "K." ++ b ++ "{" ++ String.join(G.Kd.tvars(bb, Nat.add(nm, na)), ", ") ++ "}"
  +vv = "O." ++ v ++ ".gp." ++ v
  +vr = "O." ++ v ++ ".reverse"
  +pp = "K." ++ p ++ "."
  +nrm = pp ++ sbn ++ "(T, " ++ vv ++ "(" ++ ops ++ ", m, " ++ vr ++ "(" ++ rvo ++ ", m)))"
  +nrmT = pp ++ sbn ++ "(N.Tm, " ++ vv ++ "(" ++ opst ++ ", " ++ tm ++ ", " ++ vr ++ "(" ++ rvt ++ ", " ++ tm ++ ")))"
  +fac = Bool.pick(String, minus, "neg(mul(" ++ nrm ++ ", x))", "mul(" ++ nrm ++ ", x)")
  +facT = Bool.pick(String, minus, "N.TNeg{N.TMul{" ++ nrmT ++ ", x}}", "N.TMul{" ++ nrmT ++ ", x}")
  +hyp = "{" ++ pp ++ rn ++ "(T, " ++ vv ++ "(" ++ ops ++ ", m, " ++ vr ++ "(" ++ rvo ++ ", m))) == zero : T}"
  +rt = Bool.pick(String, hasr, pp ++ rn ++ "(N.Tm, " ++ vv ++ "(" ++ opst ++ ", " ++ tm ++ ", " ++ vr ++ "(" ++ rvt ++ ", " ++ tm ++ ")))", "N.TZero{}")
  +env = "[" ++ String.join(List.append(&2, String, G.Kd.fields(vb, "m_", ""), List.append(&2, String, G.Kd.fields(ab, "a_", ""), G.Kd.fields(bb, "b_", ""))), ", ") ++ "]"
  +pat = "K." ++ v ++ "{" ++ String.join(G.Kd.fields(vb, "m_", ""), ", ") ++ "} K." ++ a ++ "{" ++ String.join(G.Kd.fields(ab, "a_", ""), ", ") ++ "} K." ++ b ++ "{" ++ String.join(G.Kd.fields(bb, "b_", ""), ", ") ++ "}"
  String.concat([
    "def ", name, ".equiv(", Eq.ring(), ",\n  m: K.", v, "<T>, a: K.", a, "<T>, b: K.", b, "<T>)\n  -> ",
    Bool.pick(String, hasr, hyp ++ " -> ", ""),
    "{K.", c, ".fields(T, ", kop, "(", ops, ", O.", v, ".transform.", a, "(", ops, ", m, a), O.", v, ".transform.", b, "(", ops, ", m, b)))\n",
    "    == K.", c, ".fields(T, K.", c, ".map(~T, ~T, ~(x => ", fac, "), O.", v, ".transform.", c, "(", ops, ", m, ", kop, "(", ops, ", a, b)))) : List<&2, T>}:\n",
    "  match m a b:\n    case ", pat, ":\n      ",
    Bool.pick(String, hasr, "hr => ", ""),
    "EQ.Rel.eqs(", Eq.ringa(), ", ", env, ",\n",
    "        K.", c, ".fields(N.Tm, ", kop, "(", opst, ", O.", v, ".transform.", a, "(", opst, ", ", tm, ", ", ta, "), O.", v, ".transform.", b, "(", opst, ", ", tm, ", ", tb, "))),\n",
    "        K.", c, ".fields(N.Tm, K.", c, ".map(~N.Tm, ~N.Tm, ~(x => ", facT, "), O.", v, ".transform.", c, "(", opst, ", ", tm, ", ", kop, "(", opst, ", ", ta, ", ", tb, ")))),\n",
    "        [", String.join(ls, ",\n         "), "],\n",
    "        ", rt, ", {==}, ", Bool.pick(String, hasr, "hr", "{==}"), ")\n"])

def Eq.negs(xs: List<&2, N.Tm>) -> List<&2, N.Tm>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      N.TNeg{x} <> Eq.negs(t)

# the factor's sign (minus) and l for each field
type Sg is Data:
  Sg{minus: Bool, ls: List<&2, String>}

# the factor's sign: +|m|² if the remainders vanish, else -|m|², else none.
# Each step is a match, so a native (strict) build computes the -|m|²
# remainders only when +|m|² fails, and nothing with two conditions.
def Eq.sign.mk(lm: Ls) -> Maybe<&2, Sg>:
  match lm:
    case Ls{tm, +okm}:
      Bool.pick(Maybe<&2, Sg>, okm, Some{Sg{True{}, tm}}, None{})

def Eq.sign.m(+lhs: List<&2, N.Tm>, +rhs: List<&2, N.Tm>, +nrmt: N.Tm, +rpoly: List<&2, N.Mono>, +lead: N.Mono) -> Maybe<&2, Sg>:
  Eq.sign.mk(Eq.ls(lhs, Eq.negs(rhs), nrmt, rpoly, lead))

def Eq.sign.p(lp: Ls, +lhs: List<&2, N.Tm>, +rhs: List<&2, N.Tm>, +nrmt: N.Tm, +rpoly: List<&2, N.Mono>, +lead: N.Mono) -> Maybe<&2, Sg>:
  match lp:
    case Ls{tp, okp}:
      match okp:
        case True{}:
          Some{Sg{False{}, tp}}
        case False{}:
          Eq.sign.m(lhs, rhs, nrmt, rpoly, lead)

def Eq.sign.nr(one: Bool, +lhs: List<&2, N.Tm>, +rhs: List<&2, N.Tm>, +nrmt: N.Tm, +rpoly: List<&2, N.Mono>, +lead: N.Mono) -> Maybe<&2, Sg>:
  match one:
    case False{}:
      None{}
    case True{}:
      Eq.sign.p(Eq.ls(lhs, rhs, nrmt, rpoly, lead), lhs, rhs, nrmt, rpoly, lead)

def Eq.law.fin(+v: String, +o: G.Op, +a: String, +b: String, +c: String, +p: String, +vb: List<&2, G.Bl>, +ab: List<&2, G.Bl>, +bb: List<&2, G.Bl>,
  +sbn: String, +hasr: Bool, +rn: String, +rvo: String, r: Maybe<&2, Sg>) -> Maybe<&2, String>:
  match r:
    case None{}:
      None{}
    case Some{sl}:
      match sl:
        case Sg{+minus, +ls}:
          Some{Eq.emit(v, o, a, b, c, p, vb, ab, bb, sbn, minus, hasr, rn, ls, rvo)}

# a law in a diagonal basis, if it reduces (at most one condition)
def Eq.law(+d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, lw: Law) -> Maybe<&2, String>:
  match lw:
    case Law{+v, +o, +a, +b, +c, +p}:
      +vb = G.Kd.bls(G.Kd.find(ks, v))
      +ab = G.Kd.bls(G.Kd.find(ks, a))
      +bb = G.Kd.bls(G.Kd.find(ks, b))
      +cb = G.Kd.bls(G.Kd.find(ks, c))
      +pb = G.Kd.bls(G.Kd.find(ks, p))
      +nm = List.length(&2, G.Bl, vb)
      +na = List.length(&2, G.Bl, ab)
      +mt = G.SymT.tree(d, vb, 0n)
      +at = G.SymT.tree(d, ab, nm)
      +bt = G.SymT.tree(d, bb, Nat.add(nm, na))
      +lhs = Eq.coefs(d, cb, Eq.run(d, sig, o, G.Sw.tm(d, sig, mt, at), G.Sw.tm(d, sig, mt, bt)))
      +rhs = Eq.coefs(d, cb, G.Sw.tm(d, sig, mt, Eq.run(d, sig, o, at, bt)))
      +pt = S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, d, sig, mt, S.MV.reverse(~N.Tm, ~N.Tm.neg, d, mt))
      +sb = Eq.scalar(pb)
      +nrmt = S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, d, Nil{}, False{}, pt)
      +rels = Eq.rels(d, pb, pt)
      +nr = List.length(&2, Rl, rels)
      +rel = Rl.first(rels)
      +rpoly = Rl.poly(rel)
      +lead = Ms.last(rpoly, N.Mono{False{}, [0n]})
      Eq.law.fin(v, o, a, b, c, p, vb, ab, bb, Bl.name(sb), Bool.not(Nat.is_eq(nr, 0n)), Rl.name(rel), "~T, ~zero, ~neg",
        Eq.sign.nr(Nat.is_lt(nr, 2n), lhs, rhs, nrmt, rpoly, lead))

# Null-basis algebras
# --------------------

def Eq.zeros(bls: List<&2, G.Bl>) -> List<&2, String>:
  match bls:
    case Nil{}:
      Nil{}
    case h <> t:
      "N.TZero{}" <> Eq.zeros(t)

# The sign by evaluation
# ----------------------
# A null-basis law has no quotients to print (l is zero on every field),
# so the generator only needs the sign. Normalizing the two sides
# symbolically costs hours at d = 6 (CSTA); evaluating them modulo a prime
# at two pseudo-random points costs milliseconds. A polynomial that is not
# zero vanishes at a random point with probability at most its degree over
# Q (Schwartz–Zippel), and the checker proves every written law, so a wrong
# sign gives a law that fails to check, never a false one; an identity
# vanishes at every point, so no law is lost.

# Q = 16777213, the largest prime below 2^24: products of two residues
# stay below Bend's native Nat limit 2^48
def Zq.q() -> Nat:
  16777213n

def Zq.add(a: Nat, b: Nat) -> Nat:
  Nat.mod(Nat.add(a, b), Zq.q())

def Zq.mul(a: Nat, b: Nat) -> Nat:
  Nat.mod(Nat.mul(a, b), Zq.q())

def Zq.neg(a: Nat) -> Nat:
  Nat.mod(Nat.sub(Zq.q(), a), Zq.q())

# h = 1/2 modulo Q
def Zq.h() -> Nat:
  8388607n

def Zq.pow(k: Nat, +h: Nat, x: Nat) -> Nat:
  match k:
    case 0n:
      x
    case 1n+j:
      Zq.mul(h, Zq.pow(j, h, x))

# n values of the MINSTD generator (modulus 2^31 - 1) from seed s, reduced
# modulo Q
def Zq.draw(n: Nat, +s: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      +t = Nat.mod(Nat.mul(s, 48271n), 2147483647n)
      Nat.mod(t, Zq.q()) <> Zq.draw(k, t)

def Zq.embV(+d: Nat, cs: List<&2, G.Cb>, +x: Nat, +h: Nat) -> S.MV(Nat, d):
  match cs:
    case Nil{}:
      S.MV.zero(Nat, d)
    case G.Cb{path, s, k} <> t:
      S.MV.add(~Nat, ~Zq.add, d, S.MV.blade(Nat, d, path, S.Ring.negf(~Nat, ~Zq.neg, s, Zq.pow(k, h, x))), Zq.embV(d, t, x, h))

# a null kind's element at the values xs, as Nl.symT builds it over Tm
def Zq.symV(+nb: G.Nb, +ng: List<&2, Nat>, +d: Nat, bls: List<&2, G.Bl>, xs: List<&2, Nat>) -> S.MV(Nat, d):
  match bls:
    case Nil{}:
      S.MV.zero(Nat, d)
    case G.Bl{name, key, pi, g} <> t:
      match xs:
        case Nil{}:
          S.MV.zero(Nat, d)
        case +x <> xt:
          S.MV.add(~Nat, ~Zq.add, d, Zq.embV(d, G.Nb.emb(nb, ng, key, pi), x, Zq.h()), Zq.symV(nb, ng, d, t, xt))

def Zq.zero(+d: Nat, x: S.MV(Nat, d)) -> Bool:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          True{}
        case S.L{a}:
          Nat.is_eq(a, 0n)
    case 1n+(+q):
      match x:
        case S.NZ{}:
          True{}
        case S.N{e, r}:
          Bool.and(Zq.zero(q, e), Zq.zero(q, r))

def Zq.run(+d: Nat, +sig: S.Sig(d), o: G.Op, x: S.MV(Nat, d), y: S.MV(Nat, d)) -> S.MV(Nat, d):
  match o:
    case G.OGp{}:
      S.MV.gp(~Nat, ~Zq.add, ~Zq.mul, ~Zq.neg, d, sig, x, y)
    case G.OWedge{}:
      S.MV.wedge(~Nat, ~Zq.add, ~Zq.mul, ~Zq.neg, d, x, y)
    case G.OVee{}:
      S.MV.vee(~Nat, ~Zq.add, ~Zq.mul, ~Zq.neg, d, x, y)
    case G.OLc{}:
      S.MV.lc(~Nat, ~Zq.add, ~Zq.mul, ~Zq.neg, d, sig, x, y)
    case G.ORc{}:
      S.MV.rc(~Nat, ~Zq.add, ~Zq.mul, ~Zq.neg, d, sig, x, y)
    case G.ODot{}:
      S.MV.dot(~Nat, ~Zq.add, ~Zq.mul, ~Zq.neg, d, sig, x, y)
    case G.OScalar{}:
      S.MV.scalar_product(~Nat, ~Zq.add, ~Zq.mul, ~Zq.neg, d, sig, x, y)
    case G.OAdd{}:
      S.MV.add(~Nat, ~Zq.add, d, x, y)
    case G.OSub{}:
      S.MV.add(~Nat, ~Zq.add, d, x, S.MV.neg(~Nat, ~Zq.neg, d, y))

def Zq.sw(+d: Nat, +sig: S.Sig(d), +v: S.MV(Nat, d), x: S.MV(Nat, d)) -> S.MV(Nat, d):
  S.MV.gp(~Nat, ~Zq.add, ~Zq.mul, ~Zq.neg, d, sig,
    S.MV.gp(~Nat, ~Zq.add, ~Zq.mul, ~Zq.neg, d, sig, v, x),
    S.MV.reverse(~Nat, ~Zq.neg, d, v))

# x + k y
def Zq.axpy(+d: Nat, +sig: S.Sig(d), +k: Nat, x: S.MV(Nat, d), y: S.MV(Nat, d)) -> S.MV(Nat, d):
  S.MV.add(~Nat, ~Zq.add, d, x, S.MV.gp(~Nat, ~Zq.add, ~Zq.mul, ~Zq.neg, d, sig, S.MV.blade(Nat, d, Nil{}, k), y))

# the sign at one point: 0 for +|m|², 1 for -|m|², 2 for neither or when
# m ~m is not a scalar there
def Zq.sign.go(scal: Bool, plus: Bool, minus: Bool) -> Nat:
  match scal:
    case False{}:
      2n
    case True{}:
      Bool.pick(Nat, plus, 0n, Bool.pick(Nat, minus, 1n, 2n))

def Zq.sign(+d: Nat, +sig: S.Sig(d), +o: G.Op, +mt: S.MV(Nat, d), +at: S.MV(Nat, d), +bt: S.MV(Nat, d)) -> Nat:
  +pt = S.MV.gp(~Nat, ~Zq.add, ~Zq.mul, ~Zq.neg, d, sig, mt, S.MV.reverse(~Nat, ~Zq.neg, d, mt))
  +nrm = S.MV.at(~Nat, ~0n, ~Zq.neg, d, Nil{}, False{}, pt)
  +lt = Zq.run(d, sig, o, Zq.sw(d, sig, mt, at), Zq.sw(d, sig, mt, bt))
  +rt = Zq.sw(d, sig, mt, Zq.run(d, sig, o, at, bt))
  Zq.sign.go(Zq.zero(d, Zq.axpy(d, sig, Zq.neg(nrm), pt, S.MV.blade(Nat, d, Nil{}, 1n))),
    Zq.zero(d, Zq.axpy(d, sig, Zq.neg(nrm), lt, rt)), Zq.zero(d, Zq.axpy(d, sig, nrm, lt, rt)))

# the sign at the point drawn from seed s
def Zq.at(+nb: G.Nb, +ng: List<&2, Nat>, +d: Nat, +sig: S.Sig(d), +o: G.Op, +vb: List<&2, G.Bl>, +ab: List<&2, G.Bl>, +bb: List<&2, G.Bl>, +s: Nat) -> Nat:
  +nm = List.length(&2, G.Bl, vb)
  +na = List.length(&2, G.Bl, ab)
  +xs = Zq.draw(Nat.add(Nat.add(nm, na), List.length(&2, G.Bl, bb)), s)
  Zq.sign(d, sig, o, Zq.symV(nb, ng, d, vb, xs), Zq.symV(nb, ng, d, ab, List.drop(&2, Nat, xs, nm)), Zq.symV(nb, ng, d, bb, List.drop(&2, Nat, xs, Nat.add(nm, na))))

def Zq.sg(+s1: Nat, s2: Nat, +zs: List<&2, String>) -> Maybe<&2, Sg>:
  Bool.pick(Maybe<&2, Sg>, Bool.and(Nat.is_eq(s1, s2), Nat.is_lt(s1, 2n)), Some{Sg{Nat.is_eq(s1, 1n), zs}}, None{})

# a law in a null basis: m ~m must be a scalar (no condition), and the two
# sides equal up to +|m|² or -|m|² on every blade, both at two points
def Eq.lawn(+nb: G.Nb, +ng: List<&2, Nat>, +d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, lw: Law) -> Maybe<&2, String>:
  match lw:
    case Law{+v, +o, +a, +b, +c, +p}:
      +vb = G.Kd.bls(G.Kd.find(ks, v))
      +ab = G.Kd.bls(G.Kd.find(ks, a))
      +bb = G.Kd.bls(G.Kd.find(ks, b))
      +cb = G.Kd.bls(G.Kd.find(ks, c))
      +pb = G.Kd.bls(G.Kd.find(ks, p))
      Eq.law.fin(v, o, a, b, c, p, vb, ab, bb, Bl.name(Eq.scalar(pb)), False{}, "?", "~T, ~zero, ~add, ~mul, ~neg",
        Zq.sg(Zq.at(nb, ng, d, sig, o, vb, ab, bb, 20261006n), Zq.at(nb, ng, d, sig, o, vb, ab, bb, 9137n), Eq.zeros(cb)))

def Eq.laws.put(r: Maybe<&2, String>, +name: String, rest: List<&2, String>) -> List<&2, String>:
  match r:
    case None{}:
      ("# NOT REDUCED: " ++ name ++ "\n") <> rest
    case Some{x}:
      x <> rest

def Law.name(lw: Law) -> String:
  match lw:
    case Law{v, o, a, b, c, p}:
      v ++ "." ++ G.Op.name(o) ++ "." ++ a ++ "." ++ b

def Eq.laws(+d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, ls: List<&2, Law>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> t:
      Eq.laws.put(Eq.law(d, sig, ks, l), Law.name(l), Eq.laws(d, sig, ks, t))

def Eq.module(s: G.GSpec, ls: List<&2, Law>) -> String:
  match s:
    case G.GSpec{+name, pre, +d, +gens, +sig, kinds, vs, nul}:
      +ks = G.Gen.kinds(d, gens, kinds)
      String.concat([G.Gen.header(name),
        "import ../../src/ring.bend as R\nimport ../../src/norm.bend as N\nimport ../../proofs/equiv.bend as EQ\nimport ./kinds.bend as K\nimport ./ops.bend as O\n\n",
        "# Equivariance (gen/equiv.bend): the versor's sandwich commutes with the\n# product, up to |m|², the scalar part of m ~m. A hypothesis, where present,\n# is the condition that makes m a versor.\n\n",
        String.join(Eq.laws(d, sig, ks, ls), "\n")])

# The curated laws
# ----------------

def laws.pga3d() -> List<&2, Law>:
  [ Law{"Motor", G.OVee{}, "Point", "Point", "Line", "Motor"},
    Law{"Motor", G.OVee{}, "Point", "Line", "Plane", "Motor"},
    Law{"Motor", G.OWedge{}, "Plane", "Plane", "Line", "Motor"},
    Law{"Motor", G.OWedge{}, "Plane", "Line", "Point", "Motor"},
    Law{"Motor", G.OLc{}, "Plane", "Point", "Line", "Motor"},
    Law{"Motor", G.ODot{}, "Line", "Plane", "Plane", "Motor"} ]

def laws.vga3d() -> List<&2, Law>:
  [ Law{"Rotor", G.OWedge{}, "Vector", "Vector", "Bivector", "Rotor"},
    Law{"Rotor", G.OVee{}, "Bivector", "Bivector", "Vector", "Rotor"},
    Law{"Rotor", G.OLc{}, "Vector", "Bivector", "Vector", "Rotor"},
    Law{"Rotor", G.ODot{}, "Bivector", "Vector", "Vector", "Rotor"} ]

def laws.pga2d() -> List<&2, Law>:
  [ Law{"Motor", G.OVee{}, "Point", "Point", "Line", "Motor"},
    Law{"Motor", G.OWedge{}, "Line", "Line", "Point", "Motor"},
    Law{"Motor", G.OLc{}, "Line", "Point", "Line", "Motor"} ]

def laws.sta() -> List<&2, Law>:
  [ Law{"Even", G.OWedge{}, "Vector", "Vector", "Bivector", "Even"},
    Law{"Even", G.OLc{}, "Vector", "Bivector", "Vector", "Even"},
    Law{"Even", G.OVee{}, "Trivector", "Trivector", "Bivector", "Even"} ]

# Every kind pair
# ---------------
# For the given versors, every product (wedge, vee, left and right
# contraction, dot) of two single-grade kinds that is not identically zero,
# its result kind chosen as the kernel generator chooses it. A law that
# does not reduce (two or more conditions, or neither sign) is listed, not
# written.

type Md is Data:
  MDiag{}
  MNul{nb: G.Nb, ng: List<&2, Nat>, mbs: List<&2, G.Bl>}

def Eq.rk(b: G.Best) -> Maybe<&2, String>:
  match b:
    case G.BNone{}:
      None{}
    case G.BSome{k, a, n}:
      Some{G.Kd.name(k)}

def Eq.rk.go(+ks: List<&2, G.Kd>, supp: List<&2, List<&2, Bool>>) -> Maybe<&2, String>:
  match supp:
    case Nil{}:
      None{}
    case +h <> +t:
      Eq.rk(G.Best.scan(ks, h <> t, G.BNone{}))

def Eq.rkd(+d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, o: G.Op, ka: G.Kd, kb: G.Kd) -> Maybe<&2, String>:
  match ka kb:
    case G.Kd{an, ar, +abs} G.Kd{bn, br, +bbs}:
      Eq.rk.go(ks, G.MV.leaves(E.Expr, d, Nil{}, G.Op.run(d, sig, o, G.Sym.tree(d, "a_", abs), G.Sym.tree(d, "b_", bbs))))

def Eq.rkn(+nb: G.Nb, +ng: List<&2, Nat>, +d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, +mbs: List<&2, G.Bl>, o: G.Op, ka: G.Kd, kb: G.Kd) -> Maybe<&2, String>:
  match ka kb:
    case G.Kd{an, ar, +abs} G.Kd{bn, br, +bbs}:
      +na = List.length(&2, G.Bl, abs)
      +hv = Nat.add(na, List.length(&2, G.Bl, bbs))
      +h = {N.TVar{hv} : N.Tm}
      Eq.rk.go(ks, G.Nl.supp(nb, ng, d, mbs, G.NK.tm(d, sig, G.NKB{o}, G.Nl.symT(nb, ng, d, abs, 0n, h), G.Nl.symT(nb, ng, d, bbs, na, h)), h, hv))

def Eq.rkm(md: Md, +d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, o: G.Op, ka: G.Kd, kb: G.Kd) -> Maybe<&2, String>:
  match md:
    case MDiag{}:
      Eq.rkd(d, sig, ks, o, ka, kb)
    case MNul{+nb, +ng, +mbs}:
      Eq.rkn(nb, ng, d, sig, ks, mbs, o, ka, kb)

def Eq.lawm(md: Md, +d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, lw: Law) -> Maybe<&2, String>:
  match md:
    case MDiag{}:
      Eq.law(d, sig, ks, lw)
    case MNul{+nb, +ng, mbs}:
      Eq.lawn(nb, ng, d, sig, ks, lw)

def Eq.allg(bls: List<&2, G.Bl>, +g: Nat) -> Bool:
  match bls:
    case Nil{}:
      True{}
    case G.Bl{n, q, s, +h} <> t:
      Bool.and(Nat.is_eq(h, g), Eq.allg(t, g))

# a single grade, not the scalars
def Eq.single(bls: List<&2, G.Bl>) -> Bool:
  match bls:
    case Nil{}:
      False{}
    case G.Bl{n, q, s, +g} <> t:
      Bool.and(Bool.not(Nat.is_eq(g, 0n)), Eq.allg(t, g))

def Eq.mem(+c: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(String.eq(x, c), Eq.mem(c, t))

# a single grade, the scalars included
def Eq.single0(bls: List<&2, G.Bl>) -> Bool:
  match bls:
    case Nil{}:
      False{}
    case G.Bl{n, q, s, +g} <> t:
      Eq.allg(t, g)

def Eq.gks(ks: List<&2, G.Kd>) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case G.Kd{+n, r, +bls} <> +t:
      Bool.pick(List<&2, String>, Eq.single0(bls), n <> Eq.gks(t), Eq.gks(t))

def Eq.inter(xs: List<&2, String>, +ys: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      Bool.pick(List<&2, String>, Eq.mem(x, ys), x <> Eq.inter(t, ys), Eq.inter(t, ys))

def Eq.opks(ks: List<&2, G.Kd>) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case G.Kd{+n, r, +bls} <> +t:
      Bool.pick(List<&2, String>, Eq.single(bls), n <> Eq.opks(t), Eq.opks(t))

def Eq.ops() -> List<&2, G.Op>:
  [G.OWedge{}, G.OVee{}, G.OLc{}, G.ORc{}, G.ODot{}]

# a law needs its result kind mapped to itself too (cl, the closed kinds)
def Eq.push(+v: String, +p: String, +o: G.Op, +a: String, +b: String, +cl: List<&2, String>, r: Maybe<&2, String>, +acc: List<&2, Law>) -> List<&2, Law>:
  match r:
    case None{}:
      acc
    case Some{+c}:
      Bool.pick(List<&2, Law>, Eq.mem(c, cl), Law{v, o, a, b, c, p} <> acc, acc)

def Eq.auto.b(+md: Md, +d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, +v: String, +p: String, +o: G.Op, +a: String, +cl: List<&2, String>, bs: List<&2, String>, acc: List<&2, Law>) -> List<&2, Law>:
  match bs:
    case Nil{}:
      acc
    case +b <> t:
      Eq.auto.b(md, d, sig, ks, v, p, o, a, cl, t, Eq.push(v, p, o, a, b, cl, Eq.rkm(md, d, sig, ks, o, G.Kd.find(ks, a), G.Kd.find(ks, b)), acc))

def Eq.auto.a(+md: Md, +d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, +v: String, +p: String, +o: G.Op, +cl: List<&2, String>, as: List<&2, String>, +bs: List<&2, String>, acc: List<&2, Law>) -> List<&2, Law>:
  match as:
    case Nil{}:
      acc
    case +a <> t:
      Eq.auto.a(md, d, sig, ks, v, p, o, cl, t, bs, Eq.auto.b(md, d, sig, ks, v, p, o, a, cl, bs, acc))

def Eq.auto.o(+md: Md, +d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, +v: String, +p: String, os: List<&2, G.Op>, +as: List<&2, String>, +cl: List<&2, String>, acc: List<&2, Law>) -> List<&2, Law>:
  match os:
    case Nil{}:
      acc
    case +o <> t:
      Eq.auto.o(md, d, sig, ks, v, p, t, as, cl, Eq.auto.a(md, d, sig, ks, v, p, o, cl, as, as, acc))

def Eq.pv(r: Maybe<&2, String>) -> String:
  match r:
    case None{}:
      "?"
    case Some{p}:
      p

# the kind of v x ~v, as the kernel generator picks it (gen/gen.bend,
# Sw.make, NKS): a kind need not map to itself, as a PGA2D motor takes a
# Direction to the Point kind
def Eq.swd(+d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, kv: G.Kd, kb: G.Kd) -> Maybe<&2, String>:
  match kv kb:
    case G.Kd{vn, vr, +vbs} G.Kd{bn, br, +bbs}:
      +rt = G.Sw.tm(d, sig, G.SymT.tree(d, vbs, 0n), G.SymT.tree(d, bbs, List.length(&2, G.Bl, vbs)))
      Eq.rk.go(ks, G.Supp.live(d, G.MV.leaves(N.Tm, d, Nil{}, rt), rt))

def Eq.swn(+nb: G.Nb, +ng: List<&2, Nat>, +d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, +mbs: List<&2, G.Bl>, kv: G.Kd, kb: G.Kd) -> Maybe<&2, String>:
  match kv kb:
    case G.Kd{an, ar, +abs} G.Kd{bn, br, +bbs}:
      +na = List.length(&2, G.Bl, abs)
      +hv = Nat.add(na, List.length(&2, G.Bl, bbs))
      +h = {N.TVar{hv} : N.Tm}
      Eq.rk.go(ks, G.Nl.supp(nb, ng, d, mbs, G.NK.tm(d, sig, G.NKS{}, G.Nl.symT(nb, ng, d, abs, 0n, h), G.Nl.symT(nb, ng, d, bbs, na, h)), h, hv))

def Eq.swm(md: Md, +d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, kv: G.Kd, kb: G.Kd) -> Maybe<&2, String>:
  match md:
    case MDiag{}:
      Eq.swd(d, sig, ks, kv, kb)
    case MNul{+nb, +ng, +mbs}:
      Eq.swn(nb, ng, d, sig, ks, mbs, kv, kb)

def Eq.keep(r: Maybe<&2, String>, +n: String, +rest: List<&2, String>) -> List<&2, String>:
  match r:
    case None{}:
      rest
    case Some{m}:
      Bool.pick(List<&2, String>, String.eq(m, n), n <> rest, rest)

# the kinds the versor kind kv maps to themselves
def Eq.closed(+md: Md, +d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, +kv: G.Kd, ns: List<&2, String>) -> List<&2, String>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> t:
      Eq.keep(Eq.swm(md, d, sig, ks, kv, G.Kd.find(ks, n)), n, Eq.closed(md, d, sig, ks, kv, t))

def Eq.auto.v(+md: Md, +d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, vs: List<&2, String>, +os: List<&2, G.Op>, +as: List<&2, String>, acc: List<&2, Law>) -> List<&2, Law>:
  match vs:
    case Nil{}:
      acc
    case +v <> t:
      +p = Eq.pv(Eq.rkm(md, d, sig, ks, G.OGp{}, G.Kd.find(ks, v), G.Kd.find(ks, v)))
      +cl = Eq.closed(md, d, sig, ks, G.Kd.find(ks, v), Eq.gks(ks))
      Eq.auto.v(md, d, sig, ks, t, os, as, Eq.auto.o(md, d, sig, ks, v, p, os, Eq.inter(as, cl), cl, acc))

type Res is Data:
  Res{texts: List<&2, String>, miss: List<&2, String>}

def Eq.collect.add(r: Maybe<&2, String>, +nm: String, rs: Res) -> Res:
  match r rs:
    case None{} Res{ts, ms}:
      Res{ts, nm <> ms}
    case Some{x} Res{ts, ms}:
      Res{x <> ts, ms}

def Eq.collect(+md: Md, +d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, ls: List<&2, Law>) -> Res:
  match ls:
    case Nil{}:
      Res{Nil{}, Nil{}}
    case +l <> t:
      Eq.collect.add(Eq.lawm(md, d, sig, ks, l), Law.name(l), Eq.collect(md, d, sig, ks, t))

def Eq.module.txt(+name: String, vs: List<&2, String>, r: Res) -> String:
  match r:
    case Res{+ts, +ms}:
      String.concat([G.Gen.header(name),
        "import ../../src/ring.bend as R\nimport ../../src/norm.bend as N\nimport ../../proofs/equiv.bend as EQ\nimport ./kinds.bend as K\nimport ./ops.bend as O\n\n",
        "# Equivariance for every kind pair (gen/equiv.bend, Eq.module.all): for the\n# versors ", String.join(vs, ", "), ", every wedge, vee, left and right\n",
        "# contraction and dot of two single-grade kinds the versor maps to\n# themselves, that is not identically zero:\n# (m >> a) op (m >> b) == +-|m|² (m >> (a op b)). ",
        Nat.show(List.length(&2, String, ts)), " laws.\n",
        Bool.pick(String, List.is_empty(&2, String, ms), "", "# Not reduced, so not written: " ++ String.join(ms, ", ") ++ "\n"),
        "\n", String.join(ts, "\n")])

def Eq.module.fin(+name: String, +md: Md, +d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, +vs: List<&2, String>) -> String:
  Eq.module.txt(name, vs, Eq.collect(md, d, sig, ks, List.reverse(&2, Law, Eq.auto.v(md, d, sig, ks, vs, Eq.ops(), Eq.opks(ks), Nil{}))))

def Eq.module.all(s: G.GSpec, vs: List<&2, String>) -> String:
  match s:
    case G.GSpec{+name, pre, +d, +gens, +sig, kinds, vers, nul}:
      match nul:
        case G.NoNul{}:
          Eq.module.fin(name, MDiag{}, d, sig, G.Gen.kinds(d, gens, kinds), vs)
        case G.Nul{+pn, +mn}:
          +nb : G.Nb = G.Nb{d, pn, mn}
          +ng = G.Nb.ng(nb)
          +ks = G.Nl.kinds(d, gens, ng, kinds)
          Eq.module.fin(name, MNul{nb, ng, G.Kd.bls(G.Kd.find(ks, "Multivector"))}, d, sig, ks, vs)
