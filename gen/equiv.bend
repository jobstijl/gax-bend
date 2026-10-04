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

def Eq.law(+d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, lw: Law) -> String:
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
      +ls = Eq.ls(lhs, rhs, nrmt, rpoly, lead)
      +name = v ++ "." ++ G.Op.name(o) ++ "." ++ a ++ "." ++ b
      +ops = {"~T, ~zero, ~add, ~mul, ~neg" : String}
      +opst = {"~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg" : String}
      +kop = "O." ++ a ++ "." ++ G.Op.name(o) ++ "." ++ b
      +tm = "K." ++ v ++ "{" ++ String.join(G.Kd.tvars(vb, 0n), ", ") ++ "}"
      +ta = "K." ++ a ++ "{" ++ String.join(G.Kd.tvars(ab, nm), ", ") ++ "}"
      +tb = "K." ++ b ++ "{" ++ String.join(G.Kd.tvars(bb, Nat.add(nm, na)), ", ") ++ "}"
      +vv = "O." ++ v ++ ".gp." ++ v
      +vr = "O." ++ v ++ ".reverse"
      +pp = "K." ++ p ++ "."
      +nrm = pp ++ Bl.name(sb) ++ "(T, " ++ vv ++ "(" ++ ops ++ ", m, " ++ vr ++ "(~T, ~zero, ~neg, m)))"
      +nrmT = pp ++ Bl.name(sb) ++ "(N.Tm, " ++ vv ++ "(" ++ opst ++ ", " ++ tm ++ ", " ++ vr ++ "(~N.Tm, ~N.TZero{}, ~N.Tm.neg, " ++ tm ++ ")))"
      +hyp = "{" ++ pp ++ Rl.name(rel) ++ "(T, " ++ vv ++ "(" ++ ops ++ ", m, " ++ vr ++ "(~T, ~zero, ~neg, m))) == zero : T}"
      +rt = Bool.pick(String, Nat.is_eq(nr, 0n), "N.TZero{}", pp ++ Rl.name(rel) ++ "(N.Tm, " ++ vv ++ "(" ++ opst ++ ", " ++ tm ++ ", " ++ vr ++ "(~N.Tm, ~N.TZero{}, ~N.Tm.neg, " ++ tm ++ ")))")
      +env = "[" ++ String.join(List.append(&2, String, G.Kd.fields(vb, "m_", ""), List.append(&2, String, G.Kd.fields(ab, "a_", ""), G.Kd.fields(bb, "b_", ""))), ", ") ++ "]"
      +pat = "K." ++ v ++ "{" ++ String.join(G.Kd.fields(vb, "m_", ""), ", ") ++ "} K." ++ a ++ "{" ++ String.join(G.Kd.fields(ab, "a_", ""), ", ") ++ "} K." ++ b ++ "{" ++ String.join(G.Kd.fields(bb, "b_", ""), ", ") ++ "}"
      +note = Bool.pick(String, Bool.and(Ls.ok(ls), Nat.is_lt(nr, 2n)), "", "# NOT REDUCED: the generator could not divide by the condition\n")
      String.concat([note,
        "def ", name, ".equiv(", Eq.ring(), ",\n  m: K.", v, "<T>, a: K.", a, "<T>, b: K.", b, "<T>)\n  -> ",
        Bool.pick(String, Nat.is_eq(nr, 0n), "", hyp ++ " -> "),
        "{K.", c, ".fields(T, ", kop, "(", ops, ", O.", v, ".transform.", a, "(", ops, ", m, a), O.", v, ".transform.", b, "(", ops, ", m, b)))\n",
        "    == K.", c, ".fields(T, K.", c, ".map(~T, ~T, ~(x => mul(", nrm, ", x)), O.", v, ".transform.", c, "(", ops, ", m, ", kop, "(", ops, ", a, b)))) : List<&2, T>}:\n",
        "  match m a b:\n    case ", pat, ":\n      ",
        Bool.pick(String, Nat.is_eq(nr, 0n), "", "hr => "),
        "EQ.Rel.eqs(", Eq.ringa(), ", ", env, ",\n",
        "        K.", c, ".fields(N.Tm, ", kop, "(", opst, ", O.", v, ".transform.", a, "(", opst, ", ", tm, ", ", ta, "), O.", v, ".transform.", b, "(", opst, ", ", tm, ", ", tb, "))),\n",
        "        K.", c, ".fields(N.Tm, K.", c, ".map(~N.Tm, ~N.Tm, ~(x => N.TMul{", nrmT, ", x}), O.", v, ".transform.", c, "(", opst, ", ", tm, ", ", kop, "(", opst, ", ", ta, ", ", tb, ")))),\n",
        "        [", String.join(Ls.texts(ls), ",\n         "), "],\n",
        "        ", rt, ", {==}, ", Bool.pick(String, Nat.is_eq(nr, 0n), "{==}", "hr"), ")\n"])

def Eq.laws(+d: Nat, +sig: S.Sig(d), +ks: List<&2, G.Kd>, ls: List<&2, Law>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> t:
      Eq.law(d, sig, ks, l) <> Eq.laws(d, sig, ks, t)

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
