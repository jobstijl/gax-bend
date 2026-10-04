# The kernel generator (ADR-002). An algebra is a GSpec: a signature and
# kinds of oriented blades. For each operation and pair of kinds the
# generator runs the Layer-S operation at T = Expr on symbolic operands,
# reads off the support, picks the result kind by gax's rule, and prints
# the kernel, the kind records, and a {==} proof that the kernel is the spec.
#
# Nothing here is trusted: every printed kernel is checked against Layer S
# by the gate (tools/gate.sh imports the generated proofs).

import Base
import ../src/spec.bend as S
import ../src/expr.bend as E
import ../src/norm.bend as N

# Specs
# -----

# a kind: its name, whether it may be a result (gax's `part` may not), and
# its blades as written, each a list of generator indices (e032 is [0,3,2])
type GKind is Data:
  GKind{name: String, res: Bool, blades: List<&2, List<&2, Nat>>}

# an algebra: name, module prefix, generator names, signature, kinds, and
# the names of the kinds that are versors (gax's `versor`)
type GSpec is Data:
  GSpec{name: String, pre: String, d: Nat, gens: List<&2, String>, sig: S.Sig(d), kinds: List<&2, GKind>, versors: List<&2, String>}

# a blade after processing: field name, path, orientation sign, grade
type Bl is Data:
  Bl{name: String, path: List<&2, Bool>, sign: Bool, grade: Nat}

# a processed kind
type Kd is Data:
  Kd{name: String, res: Bool, bls: List<&2, Bl>}

# Blades
# ------

def Nat.lt(a: Nat, b: Nat) -> Bool:
  Nat.is_lt(a, b)

# the parity of the elements of xs below x
def Gen.below(+x: Nat, xs: List<&2, Nat>, acc: Bool) -> Bool:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Gen.below(x, t, Bool.xor(acc, Nat.lt(h, x)))

# the parity of the inversions of a list: the sign of sorting it
def Gen.parity(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +h <> +t:
      Bool.xor(Gen.below(h, t, False{}), Gen.parity(t))

def Gen.has(+x: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(Nat.is_eq(h, x), Gen.has(x, t))

# the path of a blade: generator l is in it for l = i, i+1, .., d-1
def Gen.path(n: Nat, +i: Nat, +gs: List<&2, Nat>) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Gen.has(i, gs) <> Gen.path(k, 1n+i, gs)

def Gen.nth(xs: List<&2, String>, n: Nat) -> String:
  match xs:
    case Nil{}:
      "?"
    case h <> t:
      match n:
        case 0n:
          h
        case 1n+k:
          Gen.nth(t, k)

def Gen.digits(gs: List<&2, Nat>, +names: List<&2, String>) -> String:
  match gs:
    case Nil{}:
      ""
    case g <> t:
      Gen.nth(names, g) ++ Gen.digits(t, names)

def Gen.bname(gs: List<&2, Nat>, names: List<&2, String>) -> String:
  match gs:
    case Nil{}:
      "s"
    case g <> t:
      "e" ++ Gen.digits(g <> t, names)

def Gen.blade(+d: Nat, +names: List<&2, String>, +gs: List<&2, Nat>) -> Bl:
  Bl{Gen.bname(gs, names), Gen.path(d, 0n, gs), Gen.parity(gs), List.length(&2, Nat, gs)}

def Gen.blades(+d: Nat, +names: List<&2, String>, bs: List<&2, List<&2, Nat>>) -> List<&2, Bl>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> t:
      Gen.blade(d, names, b) <> Gen.blades(d, names, t)

def Gen.kinds(+d: Nat, +names: List<&2, String>, ks: List<&2, GKind>) -> List<&2, Kd>:
  match ks:
    case Nil{}:
      Nil{}
    case GKind{n, r, bs} <> t:
      Kd{n, r, Gen.blades(d, names, bs)} <> Gen.kinds(d, names, t)

# Paths
# -----

def Path.eq(a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> ys:
      False{}
    case x <> xs Nil{}:
      False{}
    case x <> xs y <> ys:
      Bool.and(Bool.not(Bool.xor(x, y)), Path.eq(xs, ys))

def Bool.to_nat(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

def Path.grade(p: List<&2, Bool>) -> Nat:
  match p:
    case Nil{}:
      0n
    case b <> t:
      Nat.add(Bool.to_nat(b), Path.grade(t))

def Bool.show.ctor(b: Bool) -> String:
  match b:
    case False{}:
      "False{}"
    case True{}:
      "True{}"

def Path.show.go(p: List<&2, Bool>) -> List<&2, String>:
  match p:
    case Nil{}:
      Nil{}
    case b <> t:
      Bool.show.ctor(b) <> Path.show.go(t)

def Path.show(p: List<&2, Bool>) -> String:
  "[" ++ String.join(Path.show.go(p), ", ") ++ "]"

# Symbolic evaluation
# -------------------

# the paths of the nonzero coefficients of x; pre is the path so far, last step first
def MV.leaves(-T: Data, +d: Nat, +pre: List<&2, Bool>, x: S.MV(T, d)) -> List<&2, List<&2, Bool>>:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          Nil{}
        case S.L{a}:
          [List.reverse(&2, Bool, pre)]
    case 1n+p:
      match x:
        case S.NZ{}:
          Nil{}
        case S.N{e, r}:
          List.append(&2, List<&2, Bool>, MV.leaves(T, p, True{} <> pre, e), MV.leaves(T, p, False{} <> pre, r))

# a kind's general element with variables named prefix ++ field
def Sym.tree(+d: Nat, +pre: String, bls: List<&2, Bl>) -> S.MV(E.Expr, d):
  match bls:
    case Nil{}:
      S.MV.zero(E.Expr, d)
    case Bl{name, path, sign, g} <> t:
      S.MV.add(~E.Expr, ~E.Expr.add, d,
        S.MV.blade(E.Expr, d, path, S.Ring.negf(~E.Expr, ~E.Expr.neg, sign, E.EVar{pre ++ name})),
        Sym.tree(d, pre, t))

type Op is Data:
  OGp{}
  OWedge{}
  OVee{}
  OAdd{}
  OSub{}
  OLc{}
  ORc{}
  ODot{}
  OScalar{}

def Op.name(o: Op) -> String:
  match o:
    case OGp{}:
      "gp"
    case OWedge{}:
      "wedge"
    case OVee{}:
      "vee"
    case OAdd{}:
      "add"
    case OSub{}:
      "sub"
    case OLc{}:
      "lc"
    case ORc{}:
      "rc"
    case ODot{}:
      "dot"
    case OScalar{}:
      "scalar_product"

def Op.run(+d: Nat, sig: S.Sig(d), o: Op, x: S.MV(E.Expr, d), y: S.MV(E.Expr, d)) -> S.MV(E.Expr, d):
  match o:
    case OGp{}:
      S.MV.gp(~E.Expr, ~E.Expr.add, ~E.Expr.mul, ~E.Expr.neg, d, sig, x, y)
    case OWedge{}:
      S.MV.wedge(~E.Expr, ~E.Expr.add, ~E.Expr.mul, ~E.Expr.neg, d, x, y)
    case OVee{}:
      S.MV.vee(~E.Expr, ~E.Expr.add, ~E.Expr.mul, ~E.Expr.neg, d, x, y)
    case OAdd{}:
      S.MV.add(~E.Expr, ~E.Expr.add, d, x, y)
    case OSub{}:
      S.MV.add(~E.Expr, ~E.Expr.add, d, x, S.MV.neg(~E.Expr, ~E.Expr.neg, d, y))
    case OLc{}:
      S.MV.lc(~E.Expr, ~E.Expr.add, ~E.Expr.mul, ~E.Expr.neg, d, sig, x, y)
    case ORc{}:
      S.MV.rc(~E.Expr, ~E.Expr.add, ~E.Expr.mul, ~E.Expr.neg, d, sig, x, y)
    case ODot{}:
      S.MV.dot(~E.Expr, ~E.Expr.add, ~E.Expr.mul, ~E.Expr.neg, d, sig, x, y)
    case OScalar{}:
      S.MV.scalar_product(~E.Expr, ~E.Expr.add, ~E.Expr.mul, ~E.Expr.neg, d, sig, x, y)

# the spec term the proofs evaluate, as Bend source, around the operands
def Op.spec(o: Op, +dn: String, +pre: String, x: String, y: String) -> String:
  match o:
    case OGp{}:
      "S.MV.gp(~T, ~add, ~mul, ~neg, " ++ dn ++ ", K." ++ pre ++ ".sig(), " ++ x ++ ", " ++ y ++ ")"
    case OWedge{}:
      "S.MV.wedge(~T, ~add, ~mul, ~neg, " ++ dn ++ ", " ++ x ++ ", " ++ y ++ ")"
    case OVee{}:
      "S.MV.vee(~T, ~add, ~mul, ~neg, " ++ dn ++ ", " ++ x ++ ", " ++ y ++ ")"
    case OAdd{}:
      "S.MV.add(~T, ~add, " ++ dn ++ ", " ++ x ++ ", " ++ y ++ ")"
    case OSub{}:
      "S.MV.add(~T, ~add, " ++ dn ++ ", " ++ x ++ ", S.MV.neg(~T, ~neg, " ++ dn ++ ", " ++ y ++ "))"
    case OLc{}:
      "S.MV.lc(~T, ~add, ~mul, ~neg, " ++ dn ++ ", K." ++ pre ++ ".sig(), " ++ x ++ ", " ++ y ++ ")"
    case ORc{}:
      "S.MV.rc(~T, ~add, ~mul, ~neg, " ++ dn ++ ", K." ++ pre ++ ".sig(), " ++ x ++ ", " ++ y ++ ")"
    case ODot{}:
      "S.MV.dot(~T, ~add, ~mul, ~neg, " ++ dn ++ ", K." ++ pre ++ ".sig(), " ++ x ++ ", " ++ y ++ ")"
    case OScalar{}:
      "S.MV.scalar_product(~T, ~add, ~mul, ~neg, " ++ dn ++ ", K." ++ pre ++ ".sig(), " ++ x ++ ", " ++ y ++ ")"

# Result kinds
# ------------

def Path.in(+p: List<&2, Bool>, bls: List<&2, Bl>) -> Bool:
  match bls:
    case Nil{}:
      False{}
    case Bl{n, q, s, g} <> t:
      Bool.or(Path.eq(p, q), Path.in(p, t))

def Supp.subset(ps: List<&2, List<&2, Bool>>, +bls: List<&2, Bl>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> t:
      Bool.and(Path.in(p, bls), Supp.subset(t, bls))

def Supp.has_grade(ps: List<&2, List<&2, Bool>>, +g: Nat) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> t:
      Bool.or(Nat.is_eq(Path.grade(p), g), Supp.has_grade(t, g))

# a kind adds a grade when one of its blades has a grade the support lacks
def Kd.adds(bls: List<&2, Bl>, +ps: List<&2, List<&2, Bool>>) -> Bool:
  match bls:
    case Nil{}:
      False{}
    case Bl{n, q, s, g} <> t:
      Bool.or(Bool.not(Supp.has_grade(ps, g)), Kd.adds(t, ps))

# the better of two candidate keys (adds a grade, size): strictly less wins
def Key.lt(a1: Bool, s1: Nat, a2: Bool, s2: Nat) -> Bool:
  match a1 a2:
    case False{} True{}:
      True{}
    case True{} False{}:
      False{}
    case False{} False{}:
      Nat.is_lt(s1, s2)
    case True{} True{}:
      Nat.is_lt(s1, s2)

type Best is Data:
  BNone{}
  BSome{k: Kd, adds: Bool, size: Nat}

def Best.take.lt(k0: Kd, a0: Bool, s0: Nat, k: Kd, a: Bool, s: Nat, lt: Bool) -> Best:
  match lt:
    case True{}:
      BSome{k, a, s}
    case False{}:
      BSome{k0, a0, s0}

def Best.take.cmp(b: Best, k: Kd, +adds: Bool, +size: Nat) -> Best:
  match b:
    case BNone{}:
      BSome{k, adds, size}
    case BSome{k0, +a0, +s0}:
      Best.take.lt(k0, a0, s0, k, adds, size, Key.lt(adds, size, a0, s0))

def Best.take(b: Best, k: Kd, adds: Bool, size: Nat, ok: Bool) -> Best:
  match ok:
    case False{}:
      b
    case True{}:
      Best.take.cmp(b, k, adds, size)

def Best.scan(ks: List<&2, Kd>, +ps: List<&2, List<&2, Bool>>, b: Best) -> Best:
  match ks:
    case Nil{}:
      b
    case Kd{n, +r, +bls} <> t:
      Best.scan(t, ps, Best.take(b, Kd{n, r, bls}, Kd.adds(bls, ps), List.length(&2, Bl, bls), Bool.and(r, Supp.subset(ps, bls))))

# Printing
# --------

def Q.show(q: S.Q) -> String:
  match q:
    case S.QP{}:
      "S.QP{}"
    case S.QN{}:
      "S.QN{}"
    case S.QZ{}:
      "S.QZ{}"

def Sig.show(+d: Nat, sig: S.Sig(d)) -> String:
  match d:
    case 0n:
      "S.SigEnd{}"
    case 1n+p:
      match sig:
        case S.Gen{q, rest}:
          "S.Gen{" ++ Q.show(q) ++ ", " ++ Sig.show(p, rest) ++ "}"

def MV.print(+d: Nat, x: S.MV(E.Expr, d)) -> String:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          "S.LZ{}"
        case S.L{e}:
          "S.L{" ++ E.Expr.show(e) ++ "}"
    case 1n+p:
      match x:
        case S.NZ{}:
          "S.NZ{}"
        case S.N{e, r}:
          "S.N{" ++ MV.print(p, e) ++ ", " ++ MV.print(p, r) ++ "}"

def Kd.fields(bls: List<&2, Bl>, +pre: String, +post: String) -> List<&2, String>:
  match bls:
    case Nil{}:
      Nil{}
    case Bl{n, q, s, g} <> t:
      (pre ++ n ++ post) <> Kd.fields(t, pre, post)

def Kd.at(bls: List<&2, Bl>, +dn: String) -> List<&2, String>:
  match bls:
    case Nil{}:
      Nil{}
    case Bl{n, q, s, g} <> t:
      ("S.MV.at(~T, ~zero, ~neg, " ++ dn ++ ", " ++ Path.show(q) ++ ", " ++ Bool.show.ctor(s) ++ ", t)") <> Kd.at(t, dn)

def Kd.getters(+n: String, +fs: List<&2, String>, bls: List<&2, Bl>) -> List<&2, String>:
  match bls:
    case Nil{}:
      Nil{}
    case Bl{f, q, s, g} <> t:
      +f2 = f
      String.concat(["def ", n, ".", f2, "(-T: Data, x: ", n, "<T>) -> T:\n  match x:\n    case ", n, "{",
        String.join(fs, ", "), "}:\n      ", f2, "\n"]) <> Kd.getters(n, fs, t)

def Kd.clears(bls: List<&2, Bl>, +dn: String) -> String:
  match bls:
    case Nil{}:
      "t"
    case Bl{n, q, s, g} <> t:
      "S.MV.clear(T, " ++ dn ++ ", " ++ Path.show(q) ++ ", " ++ Kd.clears(t, dn) ++ ")"

def Cong.slot(+k: Nat, +i: Nat) -> String:
  Bool.pick(String, Nat.is_lt(k, i), "a" ++ Nat.show(k), Bool.pick(String, Nat.is_eq(k, i), "_", "b" ++ Nat.show(k)))

def Cong.slots(+i: Nat, ks: List<&2, Nat>) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> t:
      Cong.slot(k, i) <> Cong.slots(i, t)

def Cong.names(+pre: String, +post: String, ks: List<&2, Nat>) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case +k <> t:
      (pre ++ Nat.show(k) ++ post) <> Cong.names(pre, post, t)

def Cong.eqs(ks: List<&2, Nat>) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case +k <> t:
      ("e" ++ Nat.show(k) ++ ": {a" ++ Nat.show(k) ++ " == b" ++ Nat.show(k) ++ " : T}") <> Cong.eqs(t)

def Cong.rewrites(+n: String, +lhs: String, +ks: List<&2, Nat>, ix: List<&2, Nat>) -> String:
  match ix:
    case Nil{}:
      ""
    case +i <> t:
      "  %e" ++ Nat.show(i) ++ " : {" ++ lhs ++ " == " ++ n ++ "{" ++ String.join(Cong.slots(i, ks), ", ") ++ "} : " ++ n ++ "<T>}\n" ++ Cong.rewrites(n, lhs, ks, t)

# congruence: records with equal fields are equal
def Kd.cong(+n: String, +k: Nat) -> String:
  +ks = List.range(k)
  +lhs = n ++ "{" ++ String.join(Cong.names("a", "", ks), ", ") ++ "}"
  String.concat([
    "def ", n, ".cong(-T: Data, ", String.join(Cong.names("-a", ": T", ks), ", "), ", ", String.join(Cong.names("-b", ": T", ks), ", "), ",\n  ",
    String.join(Cong.eqs(ks), ", "), ")\n  -> {", lhs, " == ", n, "{", String.join(Cong.names("b", "", ks), ", "), "} : ", n, "<T>}:\n",
    Cong.rewrites(n, lhs, ks, ks), "  {==}\n"])

# a kind's record, embedding, projection and support-clearing function
def Kd.module(+d: Nat, +dn: String, k: Kd) -> String:
  match k:
    case Kd{+n, r, +bls}:
      String.concat([
        "type ", n, "<-T: Data> is Data:\n  ", n, "{", String.join(Kd.fields(bls, "", ": T"), ", "), "}\n\n",
        "def ", n, ".tree(~T: Data, ~neg: T -> T, x: ", n, "<T>) -> S.MV(T, ", dn, "):\n",
        "  match x:\n    case ", n, "{", String.join(Kd.fields(bls, "", ""), ", "), "}:\n      ",
        MV.print(d, Sym.tree(d, "", bls)), "\n\n",
        "def ", n, ".of_tree(~T: Data, ~zero: T, ~neg: T -> T, +t: S.MV(T, ", dn, ")) -> ", n, "<T>:\n",
        "  ", n, "{\n    ", String.join(Kd.at(bls, dn), ",\n    "), "}\n\n",
        "def ", n, ".out(-T: Data, t: S.MV(T, ", dn, ")) -> S.MV(T, ", dn, "):\n  ", Kd.clears(bls, dn), "\n\n",
        String.join(Kd.getters(n, Kd.fields(bls, "", ""), bls), "\n"), "\n", Kd.cong(n, List.length(&2, Bl, bls))])

def Kd.modules(+d: Nat, +dn: String, ks: List<&2, Kd>) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> t:
      Kd.module(d, dn, k) <> Kd.modules(d, dn, t)

# Kernels
# -------

# one generated kernel: its source, its proofs, and its multiplication count
type Ker is Data:
  Ker{src: String, prf: String, api: String, muls: Nat}

def Ker.fields(+d: Nat, bls: List<&2, Bl>, +r: S.MV(E.Expr, d)) -> List<&2, E.Expr>:
  match bls:
    case Nil{}:
      Nil{}
    case Bl{n, q, s, g} <> t:
      S.MV.at(~E.Expr, ~E.EZero{}, ~E.Expr.neg, d, q, s, r) <> Ker.fields(d, t, r)

def Ker.show(es: List<&2, E.Expr>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      E.Expr.show(e) <> Ker.show(t)

def Ker.muls(es: List<&2, E.Expr>) -> Nat:
  match es:
    case Nil{}:
      0n
    case e <> t:
      Nat.add(E.Expr.muls(e), Ker.muls(t))

def Ker.text(+dn: String, +pre: String, +o: Op, ka: Kd, kb: Kd, kc: Kd, es: List<&2, E.Expr>) -> Ker:
  match ka kb kc:
    case Kd{+an, ar, +abs} Kd{+bn, br, +bbs} Kd{+cn, cr, cbs}:
      +name = an ++ "." ++ Op.name(o) ++ "." ++ bn
      +ops = {"~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T" : String}
      +args = "a: K." ++ an ++ "<T>, b: K." ++ bn ++ "<T>"
      +pat = "K." ++ an ++ "{" ++ String.join(Kd.fields(abs, "a_", ""), ", ") ++ "} K." ++ bn ++ "{" ++ String.join(Kd.fields(bbs, "b_", ""), ", ") ++ "}"
      +spec = Op.spec(o, dn, pre, "K." ++ an ++ ".tree(~T, ~neg, a)", "K." ++ bn ++ ".tree(~T, ~neg, b)")
      +es2 = es
      Ker{
        String.concat([
          "def ", name, "(", ops, ", ", args, ") -> K.", cn, "<T>:\n",
          "  match a b:\n    case K.", an, "{", String.join(Kd.fields(abs, "+a_", ""), ", "), "} K.", bn, "{",
          String.join(Kd.fields(bbs, "+b_", ""), ", "), "}:\n",
          "      K.", cn, "{\n        ", String.join(Ker.show(es2), ",\n        "), "}\n"]),
        String.concat([
          "def ", name, ".ok(", ops, ", ", args, ")\n",
          "  -> {K.", cn, ".of_tree(~T, ~zero, ~neg, ", spec, ") == O.", name, "(~T, ~zero, ~add, ~mul, ~neg, a, b) : K.", cn, "<T>}:\n",
          "  match a b:\n    case ", pat, ":\n      {==}\n\n",
          "def ", name, ".supp(", ops, ", ", args, ")\n",
          "  -> {K.", cn, ".out(T, ", spec, ") == S.MV.zero(T, ", dn, ") : S.MV(T, ", dn, ")}:\n",
          "  match a b:\n    case ", pat, ":\n      {==}\n"]),
        String.concat([
          "def ", name, "(a: K.", an, "<F32>, b: K.", bn, "<F32>) -> K.", cn, "<F32>:\n",
          "  O.", name, "(~F32, ~0.0, ~F32.add, ~F32.mul, ~F32.neg, a, b)\n"]),
        Ker.muls(es2)}

def Ker.pick.go(+d: Nat, +dn: String, +pre: String, o: Op, ka: Kd, kb: Kd, kc: Kd, +r: S.MV(E.Expr, d)) -> Maybe<&2, Ker>:
  match kc:
    case Kd{cn, cr, +cbs}:
      Some{Ker.text(dn, pre, o, ka, kb, Kd{cn, cr, cbs}, Ker.fields(d, cbs, r))}

def Ker.pick(+d: Nat, +dn: String, +pre: String, o: Op, ka: Kd, kb: Kd, b: Best, +r: S.MV(E.Expr, d)) -> Maybe<&2, Ker>:
  match b:
    case BNone{}:
      None{}
    case BSome{kc, a, s}:
      Ker.pick.go(d, dn, pre, o, ka, kb, kc, r)

# no kernel when the support is empty: the product is identically zero
def Ker.make.go(+d: Nat, +dn: String, +pre: String, o: Op, ka: Kd, kb: Kd, supp: List<&2, List<&2, Bool>>, b: Best, +r: S.MV(E.Expr, d)) -> Maybe<&2, Ker>:
  match supp:
    case Nil{}:
      None{}
    case h <> t:
      Ker.pick(d, dn, pre, o, ka, kb, b, r)

# the kernel of o on kinds ka, kb, if the product is not identically zero
def Ker.make(+d: Nat, +dn: String, +pre: String, +sig: S.Sig(d), +ks: List<&2, Kd>, +o: Op, ka: Kd, kb: Kd) -> Maybe<&2, Ker>:
  match ka kb:
    case Kd{an, ar, +abs} Kd{bn, br, +bbs}:
      +r = Op.run(d, sig, o, Sym.tree(d, "a_", abs), Sym.tree(d, "b_", bbs))
      +supp = MV.leaves(E.Expr, d, Nil{}, r)
      Ker.make.go(d, dn, pre, o, Kd{an, ar, abs}, Kd{bn, br, bbs}, supp, Best.scan(ks, supp, BNone{}), r)

# Unary kernels
# -------------

type Op1 is Data:
  ONeg{}
  ORev{}
  OInv{}
  OConj{}
  ODual{}
  OUndual{}

def Op1.name(o: Op1) -> String:
  match o:
    case ONeg{}:
      "neg"
    case ORev{}:
      "reverse"
    case OInv{}:
      "involute"
    case OConj{}:
      "conjugate"
    case ODual{}:
      "dual"
    case OUndual{}:
      "undual"

def Op1.run(+d: Nat, o: Op1, x: S.MV(E.Expr, d)) -> S.MV(E.Expr, d):
  match o:
    case ONeg{}:
      S.MV.neg(~E.Expr, ~E.Expr.neg, d, x)
    case ORev{}:
      S.MV.reverse(~E.Expr, ~E.Expr.neg, d, x)
    case OInv{}:
      S.MV.involute(~E.Expr, ~E.Expr.neg, d, x)
    case OConj{}:
      S.MV.conjugate(~E.Expr, ~E.Expr.neg, d, x)
    case ODual{}:
      S.MV.rcomp(~E.Expr, ~E.Expr.neg, d, x)
    case OUndual{}:
      S.MV.lcomp(~E.Expr, ~E.Expr.neg, d, x)

def Op1.spec(o: Op1, +dn: String) -> String:
  match o:
    case ONeg{}:
      "S.MV.neg(~T, ~neg, " ++ dn ++ ", "
    case ORev{}:
      "S.MV.reverse(~T, ~neg, " ++ dn ++ ", "
    case OInv{}:
      "S.MV.involute(~T, ~neg, " ++ dn ++ ", "
    case OConj{}:
      "S.MV.conjugate(~T, ~neg, " ++ dn ++ ", "
    case ODual{}:
      "S.MV.rcomp(~T, ~neg, " ++ dn ++ ", "
    case OUndual{}:
      "S.MV.lcomp(~T, ~neg, " ++ dn ++ ", "

def Ker1.text(+dn: String, +o: Op1, ka: Kd, kc: Kd, es: List<&2, E.Expr>) -> Ker:
  match ka kc:
    case Kd{+an, ar, +abs} Kd{+cn, cr, cbs}:
      +name = an ++ "." ++ Op1.name(o)
      +ops = {"~T: Data, ~zero: T, ~neg: T -> T" : String}
      +spec = Op1.spec(o, dn) ++ "K." ++ an ++ ".tree(~T, ~neg, a))"
      +pat = "K." ++ an ++ "{" ++ String.join(Kd.fields(abs, "a_", ""), ", ") ++ "}"
      +es2 = es
      Ker{
        String.concat([
          "def ", name, "(", ops, ", a: K.", an, "<T>) -> K.", cn, "<T>:\n",
          "  match a:\n    case K.", an, "{", String.join(Kd.fields(abs, "+a_", ""), ", "), "}:\n",
          "      K.", cn, "{\n        ", String.join(Ker.show(es2), ",\n        "), "}\n"]),
        String.concat([
          "def ", name, ".ok(", ops, ", a: K.", an, "<T>)\n",
          "  -> {K.", cn, ".of_tree(~T, ~zero, ~neg, ", spec, ") == O.", name, "(~T, ~zero, ~neg, a) : K.", cn, "<T>}:\n",
          "  match a:\n    case ", pat, ":\n      {==}\n\n",
          "def ", name, ".supp(~T: Data, ~neg: T -> T, a: K.", an, "<T>)\n",
          "  -> {K.", cn, ".out(T, ", spec, ") == S.MV.zero(T, ", dn, ") : S.MV(T, ", dn, ")}:\n",
          "  match a:\n    case ", pat, ":\n      {==}\n"]),
        String.concat([
          "def ", name, "(a: K.", an, "<F32>) -> K.", cn, "<F32>:\n",
          "  O.", name, "(~F32, ~0.0, ~F32.neg, a)\n"]),
        Ker.muls(es2)}

def Ker1.pick.go(+d: Nat, +dn: String, o: Op1, ka: Kd, kc: Kd, +r: S.MV(E.Expr, d)) -> Maybe<&2, Ker>:
  match kc:
    case Kd{cn, cr, +cbs}:
      Some{Ker1.text(dn, o, ka, Kd{cn, cr, cbs}, Ker.fields(d, cbs, r))}

def Ker1.pick(+d: Nat, +dn: String, o: Op1, ka: Kd, b: Best, +r: S.MV(E.Expr, d)) -> Maybe<&2, Ker>:
  match b:
    case BNone{}:
      None{}
    case BSome{kc, a, s}:
      Ker1.pick.go(d, dn, o, ka, kc, r)

def Ker1.make.go(+d: Nat, +dn: String, o: Op1, ka: Kd, supp: List<&2, List<&2, Bool>>, b: Best, +r: S.MV(E.Expr, d)) -> Maybe<&2, Ker>:
  match supp:
    case Nil{}:
      None{}
    case h <> t:
      Ker1.pick(d, dn, o, ka, b, r)

def Ker1.make(+d: Nat, +dn: String, +ks: List<&2, Kd>, +o: Op1, ka: Kd) -> Maybe<&2, Ker>:
  match ka:
    case Kd{an, ar, +abs}:
      +r = Op1.run(d, o, Sym.tree(d, "a_", abs))
      +supp = MV.leaves(E.Expr, d, Nil{}, r)
      Ker1.make.go(d, dn, o, Kd{an, ar, abs}, supp, Best.scan(ks, supp, BNone{}), r)

def Ker.push(m: Maybe<&2, Ker>, acc: List<&2, Ker>) -> List<&2, Ker>:
  match m:
    case None{}:
      acc
    case Some{k}:
      k <> acc

# Sandwiches
# ----------
# V.transform.X(v, x) = v x ~v (gax's transform), for each versor kind V
# and every kind X. The result kind follows the rule above, applied to the
# support that survives cancellation (src/norm.bend): a motor moves a
# point to a point although the spec's term has grade-1 parts, which
# cancel. The kernel computes v x once, binds its coefficients, and
# multiplies by ~v. After substitution that is the spec's own term, so the
# mirror law is {==}. Every blade where the spec's term is nonzero as a
# tree but outside the result kind gets a law that its coefficient is
# zero, proven by Norm.zero on the spec run at T = Tm.

# a kind's general element over Tm, its variables numbered from i
def SymT.tree(+d: Nat, bls: List<&2, Bl>, +i: Nat) -> S.MV(N.Tm, d):
  match bls:
    case Nil{}:
      S.MV.zero(N.Tm, d)
    case Bl{name, path, sign, g} <> t:
      S.MV.add(~N.Tm, ~N.Tm.add, d,
        S.MV.blade(N.Tm, d, path, S.Ring.negf(~N.Tm, ~N.Tm.neg, sign, N.TVar{i})),
        SymT.tree(d, t, 1n+i))

def Sw.tm(+d: Nat, +sig: S.Sig(d), +v: S.MV(N.Tm, d), x: S.MV(N.Tm, d)) -> S.MV(N.Tm, d):
  S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, d, sig,
    S.MV.gp(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, d, sig, v, x),
    S.MV.reverse(~N.Tm, ~N.Tm.neg, d, v))

def Supp.keep(+p: List<&2, Bool>, left: List<&2, N.Mono>, acc: List<&2, List<&2, Bool>>) -> List<&2, List<&2, Bool>>:
  match left:
    case Nil{}:
      acc
    case m <> t:
      p <> acc

# the paths among ps whose coefficient in r does not cancel
def Supp.live(+d: Nat, ps: List<&2, List<&2, Bool>>, +r: S.MV(N.Tm, d)) -> List<&2, List<&2, Bool>>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      Supp.keep(p, N.NormS.left(S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, d, p, False{}, r)), Supp.live(d, t, r))

def Supp.out.keep(+p: List<&2, Bool>, inside: Bool, acc: List<&2, List<&2, Bool>>) -> List<&2, List<&2, Bool>>:
  match inside:
    case True{}:
      acc
    case False{}:
      p <> acc

# the paths among ps outside the blades bls
def Supp.outside(ps: List<&2, List<&2, Bool>>, +bls: List<&2, Bl>) -> List<&2, List<&2, Bool>>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      Supp.out.keep(p, Path.in(p, bls), Supp.outside(t, bls))

def Path.digit(b: Bool, +n: String) -> String:
  match b:
    case True{}:
      n
    case False{}:
      ""

def Path.digits(p: List<&2, Bool>, names: List<&2, String>) -> String:
  match p:
    case Nil{}:
      ""
    case b <> t:
      match names:
        case Nil{}:
          ""
        case n <> nt:
          Path.digit(b, n) ++ Path.digits(t, nt)

# a blade's name from its path: s for the scalar, else e and the generators
def Path.bname.go(g: Nat, ds: String) -> String:
  match g:
    case 0n:
      "s"
    case 1n+h:
      "e" ++ ds

def Path.bname(+p: List<&2, Bool>, names: List<&2, String>) -> String:
  Path.bname.go(Path.grade(p), Path.digits(p, names))

# a let binding of a kernel, and the multiplications it costs
type Let is Data:
  Let{src: String, muls: Nat}

def Let.srcs(ls: List<&2, Let>) -> String:
  match ls:
    case Nil{}:
      ""
    case Let{s, m} <> t:
      s ++ Let.srcs(t)

def Let.muls(ls: List<&2, Let>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Let{s, m} <> t:
      Nat.add(m, Let.muls(t))

# a kind's general element over Tm as Bend source: K.<n>{N.TVar{i}, ...}
def Kd.tvars(bls: List<&2, Bl>, +i: Nat) -> List<&2, String>:
  match bls:
    case Nil{}:
      Nil{}
    case b <> t:
      ("N.TVar{" ++ Nat.show(i) ++ "n}") <> Kd.tvars(t, 1n+i)

def Sw.spec(+dn: String, +pre: String, +ring: String, +treeops: String, +v: String, x: String) -> String:
  String.concat(["S.MV.gp(", ring, ", ", dn, ", K.", pre, ".sig(), S.MV.gp(", ring, ", ", dn, ", K.", pre, ".sig(), ", v, ", ", x,
    "), S.MV.reverse(", treeops, ", ", dn, ", ", v, "))"])

# the zero law of one blade outside the result kind
def Sw.zero(+dn: String, +name: String, +names: List<&2, String>, +hd: String, +pat: String, +env: String, +spec: String, +spect: String, +p: List<&2, Bool>) -> String:
  +ps = Path.show(p)
  String.concat([
    "def ", name, ".zero_", Path.bname(p, names), "(", hd, ")\n",
    "  -> {S.MV.at(~T, ~zero, ~neg, ", dn, ", ", ps, ", False{}, ", spec, ") == zero : T}:\n",
    "  match a b:\n    case ", pat, ":\n",
    "      NP.NormS.zero(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, ", env, ",\n",
    "        S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, ", dn, ", ", ps, ", False{}, ", spect, "),\n",
    "        {==})\n"])

def Sw.zeros(+dn: String, +name: String, +names: List<&2, String>, +hd: String, +pat: String, +env: String, +spec: String, +spect: String, ps: List<&2, List<&2, Bool>>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      Sw.zero(dn, name, names, hd, pat, env, spec, spect, p) <> Sw.zeros(dn, name, names, hd, pat, env, spec, spect, t)

# The quadratic form of a sandwich: field c of v x ~v is Σ_j x_j Q_cj(v),
# with each Q_cj a sum of ±v_a v_b. The kernel computes each product
# v_a v_b once, each Q_cj as a sum of them, and each field as Σ_j x_j Q_cj:
# (#products + #entries) multiplications, and Q is the motor's matrix. The
# terms come from the spec's own coefficients after cancellation
# (src/norm.bend), so a coefficient that cancels costs nothing, and each
# field is proven equal to the spec's by Norm.eq.

# ±v_a v_b
type Term is Data:
  Term{s: Bool, a: Nat, b: Nat}

def Qf.term3(s: Bool, a: Nat, b: Nat, x: Nat, +xj: Nat, +acc: List<&2, Term>) -> List<&2, Term>:
  Bool.pick(List<&2, Term>, Nat.is_eq(x, xj), Term{s, a, b} <> acc, acc)

# a monomial v_a v_b x_j (variables sorted, so x last) as a term, if j = xj
def Qf.term(s: Bool, vs: List<&2, Nat>, +xj: Nat, +acc: List<&2, Term>) -> List<&2, Term>:
  match vs:
    case Nil{}:
      acc
    case a <> t1:
      match t1:
        case Nil{}:
          acc
        case b <> t2:
          match t2:
            case Nil{}:
              acc
            case x <> t3:
              Qf.term3(s, a, b, x, xj, acc)

def Qf.terms(ms: List<&2, N.Mono>, +xj: Nat) -> List<&2, Term>:
  match ms:
    case Nil{}:
      Nil{}
    case N.Mono{s, vs} <> t:
      Qf.term(s, vs, xj, Qf.terms(t, xj))

# the entries Q_cj of one field, j = 0 .. nx-1
def Qf.row(+ms: List<&2, N.Mono>, +nv: Nat, js: List<&2, Nat>) -> List<&2, List<&2, Term>>:
  match js:
    case Nil{}:
      Nil{}
    case j <> t:
      Qf.terms(ms, Nat.add(nv, j)) <> Qf.row(ms, nv, t)

def Qf.rows(+d: Nat, bls: List<&2, Bl>, +rt: S.MV(N.Tm, d), +nv: Nat, +js: List<&2, Nat>) -> List<&2, List<&2, List<&2, Term>>>:
  match bls:
    case Nil{}:
      Nil{}
    case Bl{n, q, s, g} <> t:
      Qf.row(N.NormS.left(S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, d, q, s, rt)), nv, js) <> Qf.rows(d, t, rt, nv, js)

# the distinct products v_a v_b
type Pr is Data:
  Pr{a: Nat, b: Nat}

def Pr.has(+a: Nat, +b: Nat, ps: List<&2, Pr>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Pr{pa, pb} <> t:
      Bool.or(Bool.and(Nat.is_eq(a, pa), Nat.is_eq(b, pb)), Pr.has(a, b, t))

def Pr.put(+a: Nat, +b: Nat, +ps: List<&2, Pr>) -> List<&2, Pr>:
  Bool.pick(List<&2, Pr>, Pr.has(a, b, ps), ps, List.append(&2, Pr, ps, [Pr{a, b}]))

def Pr.terms(ts: List<&2, Term>, ps: List<&2, Pr>) -> List<&2, Pr>:
  match ts:
    case Nil{}:
      ps
    case Term{s, a, b} <> t:
      Pr.terms(t, Pr.put(a, b, ps))

def Pr.row(r: List<&2, List<&2, Term>>, ps: List<&2, Pr>) -> List<&2, Pr>:
  match r:
    case Nil{}:
      ps
    case ts <> t:
      Pr.row(t, Pr.terms(ts, ps))

def Pr.rows(rs: List<&2, List<&2, List<&2, Term>>>, ps: List<&2, Pr>) -> List<&2, Pr>:
  match rs:
    case Nil{}:
      ps
    case r <> t:
      Pr.rows(t, Pr.row(r, ps))

def Qf.qname(a: Nat, b: Nat) -> String:
  "q" ++ Nat.show(a) ++ "_" ++ Nat.show(b)

def Qf.mname(c: Nat, j: Nat) -> String:
  "m" ++ Nat.show(c) ++ "_" ++ Nat.show(j)

def Qf.signed(s: Bool, e: E.Expr) -> E.Expr:
  match s:
    case False{}:
      e
    case True{}:
      E.ENeg{e}

def Qf.texpr(t: Term) -> E.Expr:
  match t:
    case Term{s, a, b}:
      Qf.signed(s, E.EVar{Qf.qname(a, b)})

def Qf.sum.go(ts: List<&2, Term>, acc: E.Expr) -> E.Expr:
  match ts:
    case Nil{}:
      acc
    case t <> r:
      Qf.sum.go(r, E.EAdd{acc, Qf.texpr(t)})

def Qf.sum(ts: List<&2, Term>) -> E.Expr:
  match ts:
    case Nil{}:
      E.EZero{}
    case t <> r:
      Qf.sum.go(r, Qf.texpr(t))

# the lets of the products
def Qf.plets(ps: List<&2, Pr>, +vs: List<&2, String>) -> List<&2, Let>:
  match ps:
    case Nil{}:
      Nil{}
    case Pr{+a, +b} <> t:
      Let{"      +" ++ Qf.qname(a, b) ++ " = mul(" ++ Gen.nth(vs, a) ++ ", " ++ Gen.nth(vs, b) ++ ")\n", 1n} <> Qf.plets(t, vs)

# the lets of the nonzero entries of field c, and the field: Σ_j x_j Q_cj
type Fld is Data:
  Fld{lets: List<&2, Let>, e: E.Expr, muls: Nat}

def Fld.add(+c: Nat, +j: Nat, +x: String, ts: List<&2, Term>, f: Fld) -> Fld:
  match ts:
    case Nil{}:
      f
    case +h <> +t:
      match f:
        case Fld{ls, e, m}:
          Fld{Let{"      +" ++ Qf.mname(c, j) ++ " = " ++ E.Expr.show(Qf.sum(h <> t)) ++ "\n", 0n} <> ls,
            E.EAdd{E.EMul{E.EVar{x}, E.EVar{Qf.mname(c, j)}}, e}, 1n+m}

def Qf.field(+c: Nat, r: List<&2, List<&2, Term>>, +j: Nat, xs: List<&2, String>) -> Fld:
  match r xs:
    case Nil{} Nil{}:
      Fld{Nil{}, E.EZero{}, 0n}
    case Nil{} x <> xt:
      Fld{Nil{}, E.EZero{}, 0n}
    case ts <> rt Nil{}:
      Fld{Nil{}, E.EZero{}, 0n}
    case ts <> rt x <> xt:
      Fld.add(c, j, x, ts, Qf.field(c, rt, 1n+j, xt))

def Qf.trim.add(b: E.Expr, a: E.Expr) -> E.Expr:
  match b:
    case E.EZero{}:
      a
    case E.EAdd{p, q}:
      E.EAdd{a, Qf.trim.add(q, p)}
    case E.EVar{n}:
      E.EAdd{a, E.EVar{n}}
    case E.EMul{p, q}:
      E.EAdd{a, E.EMul{p, q}}
    case E.ENeg{p}:
      E.EAdd{a, E.ENeg{p}}

# a sum with the zero of the last entry dropped: x + 0 is printed as x
def Qf.trim(e: E.Expr) -> E.Expr:
  match e:
    case E.EAdd{a, b}:
      Qf.trim.add(b, a)
    case E.EVar{n}:
      E.EVar{n}
    case E.EZero{}:
      E.EZero{}
    case E.EMul{a, b}:
      E.EMul{a, b}
    case E.ENeg{a}:
      E.ENeg{a}

type Fs is Data:
  Fs{lets: List<&2, Let>, es: List<&2, E.Expr>, muls: Nat}

def Qf.fields.cons(f: Fld, fs: Fs) -> Fs:
  match f fs:
    case Fld{ls, e, m} Fs{ls2, es, m2}:
      Fs{List.append(&2, Let, ls, ls2), Qf.trim(e) <> es, Nat.add(m, m2)}

def Qf.fields(rs: List<&2, List<&2, List<&2, Term>>>, +c: Nat, +xs: List<&2, String>) -> Fs:
  match rs:
    case Nil{}:
      Fs{Nil{}, Nil{}, 0n}
    case r <> t:
      Qf.fields.cons(Qf.field(c, r, 0n, xs), Qf.fields(t, 1n+c, xs))

# Assembly
# --------

# one field's equation: spec side, kernel side, and its Norm.eq proof
type Cf is Data:
  Cf{l: String, r: String, p: String}

def Sw.cf(+dn: String, +name: String, +cn: String, +env: String, +specr: String, +spect: String, +recs: String, +recst: String, b: Bl) -> Cf:
  match b:
    case Bl{f, q, s, g}:
      +at = ", " ++ dn ++ ", " ++ Path.show(q) ++ ", " ++ Bool.show.ctor(s) ++ ", "
      +get = "K." ++ cn ++ "." ++ f
      Cf{
        "S.MV.at(~T, ~zero, ~neg" ++ at ++ specr ++ ")",
        get ++ "(T, O." ++ name ++ "(~T, ~zero, ~add, ~mul, ~neg, " ++ recs ++ "))",
        String.concat(["NP.NormS.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, ", env, ",\n          ",
          "S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg", at, spect, "),\n          ",
          get, "(N.Tm, O.", name, "(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, ", recst, ")),\n          {==})"])}

def Sw.cfs(+dn: String, +name: String, +cn: String, +env: String, +specr: String, +spect: String, +recs: String, +recst: String, bls: List<&2, Bl>) -> List<&2, Cf>:
  match bls:
    case Nil{}:
      Nil{}
    case b <> t:
      Sw.cf(dn, name, cn, env, specr, spect, recs, recst, b) <> Sw.cfs(dn, name, cn, env, specr, spect, recs, recst, t)

def Cf.ls(cs: List<&2, Cf>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Cf{l, r, p} <> t:
      l <> Cf.ls(t)

def Cf.rs(cs: List<&2, Cf>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Cf{l, r, p} <> t:
      r <> Cf.rs(t)

def Cf.ps(cs: List<&2, Cf>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Cf{l, r, p} <> t:
      p <> Cf.ps(t)

def Sw.text(+dn: String, +pre: String, +names: List<&2, String>, ka: Kd, kb: Kd, kc: Kd, fs: Fs, outs: List<&2, List<&2, Bool>>) -> Ker:
  match ka kb kc fs:
    case Kd{+an, ar, +abs} Kd{+bn, br, +bbs} Kd{+cn, cr, +cbs} Fs{ls, es, muls}:
      +name = an ++ ".transform." ++ bn
      +ops = {"~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T" : String}
      +hyps = {"~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,\n  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),\n  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),\n  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg)" : String}
      +args = "a: K." ++ an ++ "<T>, b: K." ++ bn ++ "<T>"
      +ra = "K." ++ an ++ "{" ++ String.join(Kd.fields(abs, "a_", ""), ", ") ++ "}"
      +rb = "K." ++ bn ++ "{" ++ String.join(Kd.fields(bbs, "b_", ""), ", ") ++ "}"
      +pat = ra ++ " " ++ rb
      +ppat = "K." ++ an ++ "{" ++ String.join(Kd.fields(abs, "+a_", ""), ", ") ++ "} K." ++ bn ++ "{" ++ String.join(Kd.fields(bbs, "+b_", ""), ", ") ++ "}"
      +env = "[" ++ String.join(List.append(&2, String, Kd.fields(abs, "a_", ""), Kd.fields(bbs, "b_", "")), ", ") ++ "]"
      +spec = Sw.spec(dn, pre, "~T, ~add, ~mul, ~neg", "~T, ~neg", "K." ++ an ++ ".tree(~T, ~neg, a)", "K." ++ bn ++ ".tree(~T, ~neg, b)")
      +specr = Sw.spec(dn, pre, "~T, ~add, ~mul, ~neg", "~T, ~neg", "K." ++ an ++ ".tree(~T, ~neg, " ++ ra ++ ")", "K." ++ bn ++ ".tree(~T, ~neg, " ++ rb ++ ")")
      +na = List.length(&2, Bl, abs)
      +ta = "K." ++ an ++ "{" ++ String.join(Kd.tvars(abs, 0n), ", ") ++ "}"
      +tb = "K." ++ bn ++ "{" ++ String.join(Kd.tvars(bbs, na), ", ") ++ "}"
      +spect = Sw.spec(dn, pre, "~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg", "~N.Tm, ~N.Tm.neg",
        "K." ++ an ++ ".tree(~N.Tm, ~N.Tm.neg, " ++ ta ++ ")", "K." ++ bn ++ ".tree(~N.Tm, ~N.Tm.neg, " ++ tb ++ ")")
      +cfs = Sw.cfs(dn, name, cn, env, specr, spect, ra ++ ", " ++ rb, ta ++ ", " ++ tb, cbs)
      +es2 = es
      Ker{
        String.concat([
          "def ", name, "(", ops, ", ", args, ") -> K.", cn, "<T>:\n",
          "  match a b:\n    case ", ppat, ":\n",
          Let.srcs(ls),
          "      K.", cn, "{\n        ", String.join(Ker.show(es2), ",\n        "), "}\n"]),
        String.concat([
          "def ", name, ".ok(", hyps, ", ", args, ")\n",
          "  -> {K.", cn, ".of_tree(~T, ~zero, ~neg, ", spec, ") == O.", name, "(~T, ~zero, ~add, ~mul, ~neg, a, b) : K.", cn, "<T>}:\n",
          "  match a b:\n    case ", ppat, ":\n",
          "      K.", cn, ".cong(T,\n        ", String.join(Cf.ls(cfs), ",\n        "), ",\n        ",
          String.join(Cf.rs(cfs), ",\n        "), ",\n        ", String.join(Cf.ps(cfs), ",\n        "), ")\n",
          String.concat(Sw.zeros(dn, name, names, hyps ++ ", " ++ args, pat, env, spec, spect, outs))]),
        String.concat([
          "def ", name, "(a: K.", an, "<F32>, b: K.", bn, "<F32>) -> K.", cn, "<F32>:\n",
          "  O.", name, "(~F32, ~0.0, ~F32.add, ~F32.mul, ~F32.neg, a, b)\n"]),
        muls}

# the product lets in front, their multiplications counted
def Sw.fs(pl: List<&2, Let>, np: Nat, fs: Fs) -> Fs:
  match fs:
    case Fs{ls, es, m}:
      Fs{List.append(&2, Let, pl, ls), es, Nat.add(np, m)}

def Sw.pick.go(+d: Nat, +dn: String, +pre: String, +names: List<&2, String>, ka: Kd, kb: Kd, kc: Kd, +rt: S.MV(N.Tm, d), +all: List<&2, List<&2, Bool>>) -> Maybe<&2, Ker>:
  match ka kb kc:
    case Kd{an, ar, +abs} Kd{bn, br, +bbs} Kd{cn, cr, +cbs}:
      +rows = Qf.rows(d, cbs, rt, List.length(&2, Bl, abs), List.range(List.length(&2, Bl, bbs)))
      +ps = Pr.rows(rows, Nil{})
      +fs = Qf.fields(rows, 0n, Kd.fields(bbs, "b_", ""))
      Some{Sw.text(dn, pre, names, Kd{an, ar, abs}, Kd{bn, br, bbs}, Kd{cn, cr, cbs},
        Sw.fs(Qf.plets(ps, Kd.fields(abs, "a_", "")), List.length(&2, Pr, ps), fs), Supp.outside(all, cbs))}

def Sw.pick(+d: Nat, +dn: String, +pre: String, +names: List<&2, String>, ka: Kd, kb: Kd, b: Best, +rt: S.MV(N.Tm, d), +all: List<&2, List<&2, Bool>>) -> Maybe<&2, Ker>:
  match b:
    case BNone{}:
      None{}
    case BSome{kc, a, s}:
      Sw.pick.go(d, dn, pre, names, ka, kb, kc, rt, all)

def Sw.make.go(+d: Nat, +dn: String, +pre: String, +names: List<&2, String>, +ks: List<&2, Kd>, ka: Kd, kb: Kd, live: List<&2, List<&2, Bool>>,
  +rt: S.MV(N.Tm, d), +all: List<&2, List<&2, Bool>>) -> Maybe<&2, Ker>:
  match live:
    case Nil{}:
      None{}
    case +h <> +t:
      Sw.pick(d, dn, pre, names, ka, kb, Best.scan(ks, h <> t, BNone{}), rt, all)

# the sandwich of kind kb by the versor kind ka
def Sw.make(+d: Nat, +dn: String, +pre: String, +names: List<&2, String>, +sig: S.Sig(d), +ks: List<&2, Kd>, ka: Kd, kb: Kd) -> Maybe<&2, Ker>:
  match ka kb:
    case Kd{an, ar, +abs} Kd{bn, br, +bbs}:
      +rt = Sw.tm(d, sig, SymT.tree(d, abs, 0n), SymT.tree(d, bbs, List.length(&2, Bl, abs)))
      +all = MV.leaves(N.Tm, d, Nil{}, rt)
      Sw.make.go(d, dn, pre, names, ks, Kd{an, ar, abs}, Kd{bn, br, bbs}, Supp.live(d, all, rt), rt, all)

def Kd.named(+n: String, ns: List<&2, String>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case m <> t:
      Bool.or(String.eq(m, n), Kd.named(n, t))

def Sw.row(+d: Nat, +dn: String, +pre: String, +names: List<&2, String>, +sig: S.Sig(d), +ks: List<&2, Kd>, +ka: Kd, kbs: List<&2, Kd>, acc: List<&2, Ker>) -> List<&2, Ker>:
  match kbs:
    case Nil{}:
      acc
    case kb <> t:
      Sw.row(d, dn, pre, names, sig, ks, ka, t, Ker.push(Sw.make(d, dn, pre, names, sig, ks, ka, kb), acc))

def Sw.row.if(+d: Nat, +dn: String, +pre: String, +names: List<&2, String>, +sig: S.Sig(d), +ks: List<&2, Kd>, ka: Kd, versor: Bool, acc: List<&2, Ker>) -> List<&2, Ker>:
  match versor:
    case False{}:
      acc
    case True{}:
      Sw.row(d, dn, pre, names, sig, ks, ka, ks, acc)

def Sw.table(+d: Nat, +dn: String, +pre: String, +names: List<&2, String>, +sig: S.Sig(d), +ks: List<&2, Kd>, +vs: List<&2, String>, kas: List<&2, Kd>, acc: List<&2, Ker>) -> List<&2, Ker>:
  match kas:
    case Nil{}:
      acc
    case Kd{+n, r, bls} <> t:
      Sw.table(d, dn, pre, names, sig, ks, vs, t, Sw.row.if(d, dn, pre, names, sig, ks, Kd{n, r, bls}, Kd.named(n, vs), acc))

# Halved products
# ---------------
# x.commutator.y = (xy - yx)/2 and x.anticommutator.y = (xy + yx)/2 (gax's
# definitions). Layer S has the doubled forms; every coefficient of those
# is even, so the generator halves it by dropping one of each pair of equal
# monomials, and the kernel has integer coefficients. The law .ok states
# kernel + kernel = the doubled spec, field by field by Norm.eq.

type HOp is Data:
  HComm{}
  HAnti{}

def HOp.name(o: HOp) -> String:
  match o:
    case HComm{}:
      "commutator"
    case HAnti{}:
      "anticommutator"

def HOp.fn(o: HOp) -> String:
  match o:
    case HComm{}:
      "S.MV.commutator2"
    case HAnti{}:
      "S.MV.anticommutator2"

def HOp.tm(+d: Nat, +sig: S.Sig(d), o: HOp, +x: S.MV(N.Tm, d), +y: S.MV(N.Tm, d)) -> S.MV(N.Tm, d):
  match o:
    case HComm{}:
      S.MV.commutator2(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, d, sig, x, y)
    case HAnti{}:
      S.MV.anticommutator2(~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, d, sig, x, y)

def Mono.same(a: N.Mono, b: N.Mono) -> Bool:
  match a b:
    case N.Mono{s, vs} N.Mono{t, ws}:
      Bool.and(Bool.not(Bool.xor(s, t)), N.Vs.eq(vs, ws))

type Taken is Data:
  TNone{}
  TSome{rest: List<&2, N.Mono>}

def Taken.cons(p: N.Mono, tk: Taken) -> Taken:
  match tk:
    case TNone{}:
      TNone{}
    case TSome{r}:
      TSome{p <> r}

# ps without the first monomial equal to m, if there is one
def Ms.take(+m: N.Mono, ps: List<&2, N.Mono>) -> Taken:
  match ps:
    case Nil{}:
      TNone{}
    case +p <> +t:
      Bool.pick(Taken, Mono.same(m, p), TSome{t}, Taken.cons(p, Ms.take(m, t)))

# the pending monomials, and one of each pair found so far
type Hs is Data:
  Hs{ps: List<&2, N.Mono>, out: List<&2, N.Mono>}

def Ms.half.step(+m: N.Mono, ps: List<&2, N.Mono>, out: List<&2, N.Mono>, tk: Taken) -> Hs:
  match tk:
    case TNone{}:
      Hs{m <> ps, out}
    case TSome{r}:
      Hs{r, m <> out}

def Ms.half.next(+m: N.Mono, st: Hs) -> Hs:
  match st:
    case Hs{+ps, out}:
      Ms.half.step(m, ps, out, Ms.take(m, ps))

def Ms.half.go(l: List<&2, N.Mono>, st: Hs) -> Hs:
  match l:
    case Nil{}:
      st
    case m <> t:
      Ms.half.go(t, Ms.half.next(m, st))

# half of a list whose monomials come in equal pairs
def Hs.out(st: Hs) -> List<&2, N.Mono>:
  match st:
    case Hs{ps, out}:
      List.reverse(&2, N.Mono, out)

def Ms.half(l: List<&2, N.Mono>) -> List<&2, N.Mono>:
  Hs.out(Ms.half.go(l, Hs{Nil{}, Nil{}}))

# a bilinear monomial x_a y_b as a term of the kernel
def Hf.term(s: Bool, vs: List<&2, Nat>, +xs: List<&2, String>, +ys: List<&2, String>, +na: Nat) -> E.Expr:
  match vs:
    case Nil{}:
      E.EZero{}
    case a <> t1:
      match t1:
        case Nil{}:
          E.EZero{}
        case b <> t2:
          Qf.signed(s, E.EMul{E.EVar{Gen.nth(xs, a)}, E.EVar{Gen.nth(ys, Nat.sub(b, na))}})

def Hf.sum(ms: List<&2, N.Mono>, +xs: List<&2, String>, +ys: List<&2, String>, +na: Nat, acc: E.Expr) -> E.Expr:
  match ms:
    case Nil{}:
      acc
    case N.Mono{s, vs} <> t:
      Hf.sum(t, xs, ys, na, E.EAdd{acc, Hf.term(s, vs, xs, ys, na)})

def Hf.field(ms: List<&2, N.Mono>, +xs: List<&2, String>, +ys: List<&2, String>, +na: Nat) -> E.Expr:
  match ms:
    case Nil{}:
      E.EZero{}
    case N.Mono{s, vs} <> t:
      Hf.sum(t, xs, ys, na, Hf.term(s, vs, xs, ys, na))

def Hf.fields(+d: Nat, bls: List<&2, Bl>, +rt: S.MV(N.Tm, d), +xs: List<&2, String>, +ys: List<&2, String>, +na: Nat) -> List<&2, E.Expr>:
  match bls:
    case Nil{}:
      Nil{}
    case Bl{n, q, s, g} <> t:
      Hf.field(Ms.half(N.NormS.left(S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg, d, q, s, rt))), xs, ys, na) <> Hf.fields(d, t, rt, xs, ys, na)

def Hf.spec(+dn: String, +pre: String, +fn: String, +ring: String, x: String, y: String) -> String:
  String.concat([fn, "(", ring, ", ", dn, ", K.", pre, ".sig(), ", x, ", ", y, ")"])

# one field's equation: the doubled spec against kernel + kernel
def Hf.cf(+dn: String, +name: String, +cn: String, +env: String, +specr: String, +spect: String, +recs: String, +recst: String, b: Bl) -> Cf:
  match b:
    case Bl{f, q, s, g}:
      +at = ", " ++ dn ++ ", " ++ Path.show(q) ++ ", " ++ Bool.show.ctor(s) ++ ", "
      +get = "K." ++ cn ++ "." ++ f
      +kt = "O." ++ name ++ "(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, " ++ recst ++ ")"
      Cf{
        "S.MV.at(~T, ~zero, ~neg" ++ at ++ specr ++ ")",
        get ++ "(T, O." ++ cn ++ ".add." ++ cn ++ "(~T, ~zero, ~add, ~mul, ~neg, O." ++ name ++ "(~T, ~zero, ~add, ~mul, ~neg, " ++ recs ++ "), O." ++ name ++ "(~T, ~zero, ~add, ~mul, ~neg, " ++ recs ++ ")))",
        String.concat(["NP.NormS.eq(~T, ~zero, ~one, ~add, ~mul, ~neg, ~aa, ~ac, ~z, ~inv, ~ma, ~mc, ~u, ~dl, ~na, ~nm, ~nn, ", env, ",\n          ",
          "S.MV.at(~N.Tm, ~N.TZero{}, ~N.Tm.neg", at, spect, "),\n          ",
          get, "(N.Tm, O.", cn, ".add.", cn, "(~N.Tm, ~N.TZero{}, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg, ", kt, ", ", kt, ")),\n          {==})"])}

def Hf.cfs(+dn: String, +name: String, +cn: String, +env: String, +specr: String, +spect: String, +recs: String, +recst: String, bls: List<&2, Bl>) -> List<&2, Cf>:
  match bls:
    case Nil{}:
      Nil{}
    case b <> t:
      Hf.cf(dn, name, cn, env, specr, spect, recs, recst, b) <> Hf.cfs(dn, name, cn, env, specr, spect, recs, recst, t)

def Hf.text(+dn: String, +pre: String, +names: List<&2, String>, +o: HOp, ka: Kd, kb: Kd, kc: Kd, es: List<&2, E.Expr>, outs: List<&2, List<&2, Bool>>) -> Ker:
  match ka kb kc:
    case Kd{+an, ar, +abs} Kd{+bn, br, +bbs} Kd{+cn, cr, +cbs}:
      +name = an ++ "." ++ HOp.name(o) ++ "." ++ bn
      +ops = {"~T: Data, ~zero: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T" : String}
      +hyps = {"~T: Data, ~zero: T, ~one: T, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T,\n  ~aa: R.Ring.Assoc(T, add), ~ac: R.Ring.Comm(T, add), ~z: R.Ring.ZeroL(T, add, zero), ~inv: R.Ring.AddInv(T, add, neg, zero),\n  ~ma: R.Ring.Assoc(T, mul), ~mc: R.Ring.Comm(T, mul), ~u: R.Ring.UnitR(T, mul, one), ~dl: R.Ring.DistL(T, add, mul),\n  ~na: R.Ring.NegAdd(T, add, neg), ~nm: R.Ring.NegMulL(T, mul, neg), ~nn: R.Ring.NegNeg(T, neg)" : String}
      +args = "a: K." ++ an ++ "<T>, b: K." ++ bn ++ "<T>"
      +ra = "K." ++ an ++ "{" ++ String.join(Kd.fields(abs, "a_", ""), ", ") ++ "}"
      +rb = "K." ++ bn ++ "{" ++ String.join(Kd.fields(bbs, "b_", ""), ", ") ++ "}"
      +pat = ra ++ " " ++ rb
      +ppat = "K." ++ an ++ "{" ++ String.join(Kd.fields(abs, "+a_", ""), ", ") ++ "} K." ++ bn ++ "{" ++ String.join(Kd.fields(bbs, "+b_", ""), ", ") ++ "}"
      +env = "[" ++ String.join(List.append(&2, String, Kd.fields(abs, "a_", ""), Kd.fields(bbs, "b_", "")), ", ") ++ "]"
      +ring = {"~T, ~add, ~mul, ~neg" : String}
      +spec = Hf.spec(dn, pre, HOp.fn(o), ring, "K." ++ an ++ ".tree(~T, ~neg, a)", "K." ++ bn ++ ".tree(~T, ~neg, b)")
      +specr = Hf.spec(dn, pre, HOp.fn(o), ring, "K." ++ an ++ ".tree(~T, ~neg, " ++ ra ++ ")", "K." ++ bn ++ ".tree(~T, ~neg, " ++ rb ++ ")")
      +na = List.length(&2, Bl, abs)
      +ta = "K." ++ an ++ "{" ++ String.join(Kd.tvars(abs, 0n), ", ") ++ "}"
      +tb = "K." ++ bn ++ "{" ++ String.join(Kd.tvars(bbs, na), ", ") ++ "}"
      +spect = Hf.spec(dn, pre, HOp.fn(o), "~N.Tm, ~N.Tm.add, ~N.Tm.mul, ~N.Tm.neg",
        "K." ++ an ++ ".tree(~N.Tm, ~N.Tm.neg, " ++ ta ++ ")", "K." ++ bn ++ ".tree(~N.Tm, ~N.Tm.neg, " ++ tb ++ ")")
      +cfs = Hf.cfs(dn, name, cn, env, specr, spect, ra ++ ", " ++ rb, ta ++ ", " ++ tb, cbs)
      +es2 = es
      Ker{
        String.concat([
          "def ", name, "(", ops, ", ", args, ") -> K.", cn, "<T>:\n",
          "  match a b:\n    case ", ppat, ":\n",
          "      K.", cn, "{\n        ", String.join(Ker.show(es2), ",\n        "), "}\n"]),
        String.concat([
          "def ", name, ".ok(", hyps, ", ", args, ")\n",
          "  -> {K.", cn, ".of_tree(~T, ~zero, ~neg, ", spec, ") == O.", cn, ".add.", cn, "(~T, ~zero, ~add, ~mul, ~neg, O.", name,
          "(~T, ~zero, ~add, ~mul, ~neg, a, b), O.", name, "(~T, ~zero, ~add, ~mul, ~neg, a, b)) : K.", cn, "<T>}:\n",
          "  match a b:\n    case ", ppat, ":\n",
          "      K.", cn, ".cong(T,\n        ", String.join(Cf.ls(cfs), ",\n        "), ",\n        ",
          String.join(Cf.rs(cfs), ",\n        "), ",\n        ", String.join(Cf.ps(cfs), ",\n        "), ")\n",
          String.concat(Sw.zeros(dn, name, names, hyps ++ ", " ++ args, pat, env, spec, spect, outs))]),
        String.concat([
          "def ", name, "(a: K.", an, "<F32>, b: K.", bn, "<F32>) -> K.", cn, "<F32>:\n",
          "  O.", name, "(~F32, ~0.0, ~F32.add, ~F32.mul, ~F32.neg, a, b)\n"]),
        Ker.muls(es2)}

def Hf.pick.go(+d: Nat, +dn: String, +pre: String, +names: List<&2, String>, +o: HOp, ka: Kd, kb: Kd, kc: Kd, +rt: S.MV(N.Tm, d), +all: List<&2, List<&2, Bool>>) -> Maybe<&2, Ker>:
  match ka kb kc:
    case Kd{an, ar, +abs} Kd{bn, br, +bbs} Kd{cn, cr, +cbs}:
      Some{Hf.text(dn, pre, names, o, Kd{an, ar, abs}, Kd{bn, br, bbs}, Kd{cn, cr, cbs},
        Hf.fields(d, cbs, rt, Kd.fields(abs, "a_", ""), Kd.fields(bbs, "b_", ""), List.length(&2, Bl, abs)), Supp.outside(all, cbs))}

def Hf.pick(+d: Nat, +dn: String, +pre: String, +names: List<&2, String>, +o: HOp, ka: Kd, kb: Kd, b: Best, +rt: S.MV(N.Tm, d), +all: List<&2, List<&2, Bool>>) -> Maybe<&2, Ker>:
  match b:
    case BNone{}:
      None{}
    case BSome{kc, a, s}:
      Hf.pick.go(d, dn, pre, names, o, ka, kb, kc, rt, all)

def Hf.make.go(+d: Nat, +dn: String, +pre: String, +names: List<&2, String>, +ks: List<&2, Kd>, +o: HOp, ka: Kd, kb: Kd, live: List<&2, List<&2, Bool>>,
  +rt: S.MV(N.Tm, d), +all: List<&2, List<&2, Bool>>) -> Maybe<&2, Ker>:
  match live:
    case Nil{}:
      None{}
    case +h <> +t:
      Hf.pick(d, dn, pre, names, o, ka, kb, Best.scan(ks, h <> t, BNone{}), rt, all)

def Hf.make(+d: Nat, +dn: String, +pre: String, +names: List<&2, String>, +sig: S.Sig(d), +ks: List<&2, Kd>, +o: HOp, ka: Kd, kb: Kd) -> Maybe<&2, Ker>:
  match ka kb:
    case Kd{an, ar, +abs} Kd{bn, br, +bbs}:
      +rt = HOp.tm(d, sig, o, SymT.tree(d, abs, 0n), SymT.tree(d, bbs, List.length(&2, Bl, abs)))
      +all = MV.leaves(N.Tm, d, Nil{}, rt)
      Hf.make.go(d, dn, pre, names, ks, o, Kd{an, ar, abs}, Kd{bn, br, bbs}, Supp.live(d, all, rt), rt, all)

def Hf.row(+d: Nat, +dn: String, +pre: String, +names: List<&2, String>, +sig: S.Sig(d), +ks: List<&2, Kd>, +o: HOp, +ka: Kd, kbs: List<&2, Kd>, acc: List<&2, Ker>) -> List<&2, Ker>:
  match kbs:
    case Nil{}:
      acc
    case kb <> t:
      Hf.row(d, dn, pre, names, sig, ks, o, ka, t, Ker.push(Hf.make(d, dn, pre, names, sig, ks, o, ka, kb), acc))

def Hf.table(+d: Nat, +dn: String, +pre: String, +names: List<&2, String>, +sig: S.Sig(d), +ks: List<&2, Kd>, +o: HOp, kas: List<&2, Kd>, acc: List<&2, Ker>) -> List<&2, Ker>:
  match kas:
    case Nil{}:
      acc
    case ka <> t:
      Hf.table(d, dn, pre, names, sig, ks, o, t, Hf.row(d, dn, pre, names, sig, ks, o, ka, ks, acc))

# Tables and files
# ----------------

def Ker.row(+d: Nat, +dn: String, +pre: String, +sig: S.Sig(d), +ks: List<&2, Kd>, +o: Op, +ka: Kd, kbs: List<&2, Kd>, acc: List<&2, Ker>) -> List<&2, Ker>:
  match kbs:
    case Nil{}:
      acc
    case kb <> t:
      Ker.row(d, dn, pre, sig, ks, o, ka, t, Ker.push(Ker.make(d, dn, pre, sig, ks, o, ka, kb), acc))

def Ker.table(+d: Nat, +dn: String, +pre: String, +sig: S.Sig(d), +ks: List<&2, Kd>, +o: Op, kas: List<&2, Kd>, acc: List<&2, Ker>) -> List<&2, Ker>:
  match kas:
    case Nil{}:
      acc
    case ka <> t:
      Ker.table(d, dn, pre, sig, ks, o, t, Ker.row(d, dn, pre, sig, ks, o, ka, ks, acc))

def Ker.ops(+d: Nat, +dn: String, +pre: String, +sig: S.Sig(d), +ks: List<&2, Kd>, os: List<&2, Op>, acc: List<&2, Ker>) -> List<&2, Ker>:
  match os:
    case Nil{}:
      acc
    case o <> t:
      Ker.ops(d, dn, pre, sig, ks, t, Ker.table(d, dn, pre, sig, ks, o, ks, acc))

def Ker1.row(+d: Nat, +dn: String, +ks: List<&2, Kd>, +o: Op1, kas: List<&2, Kd>, acc: List<&2, Ker>) -> List<&2, Ker>:
  match kas:
    case Nil{}:
      acc
    case ka <> t:
      Ker1.row(d, dn, ks, o, t, Ker.push(Ker1.make(d, dn, ks, o, ka), acc))

def Ker1.ops(+d: Nat, +dn: String, +ks: List<&2, Kd>, os: List<&2, Op1>, acc: List<&2, Ker>) -> List<&2, Ker>:
  match os:
    case Nil{}:
      acc
    case o <> t:
      Ker1.ops(d, dn, ks, t, Ker1.row(d, dn, ks, o, ks, acc))

def Ker.srcs(ks: List<&2, Ker>) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case Ker{s, p, a, m} <> t:
      s <> Ker.srcs(t)

def Ker.prfs(ks: List<&2, Ker>) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case Ker{s, p, a, m} <> t:
      p <> Ker.prfs(t)

def Ker.apis(ks: List<&2, Ker>) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case Ker{s, p, a, m} <> t:
      a <> Ker.apis(t)

def Ker.total(ks: List<&2, Ker>) -> Nat:
  match ks:
    case Nil{}:
      0n
    case Ker{s, p, a, m} <> t:
      Nat.add(m, Ker.total(t))

# the generated modules of one algebra, and a summary line
type Out is Data:
  Out{kinds: String, ops: String, proofs: String, f32: String, summary: String}

def Gen.header(name: String) -> String:
  "# Generated by gen/main.bend from the " ++ name ++ " spec (gen/specs.bend).\n# Do not edit: run tools/regen.sh.\n\nimport Base\nimport ../../src/spec.bend as S\n"

def Gen.out.go(+name: String, +pre: String, +d: Nat, +sig: S.Sig(d), +ks: List<&2, Kd>, +kers: List<&2, Ker>) -> Out:
  +dn = Nat.show(d) ++ "n"
  Out{
    String.concat([Gen.header(name), "\ndef ", pre, ".sig() -> S.Sig(", dn, "):\n  ", Sig.show(d, sig), "\n\n",
      String.join(Kd.modules(d, dn, ks), "\n")]),
    String.concat([Gen.header(name), "import ./kinds.bend as K\n\n", String.join(Ker.srcs(kers), "\n")]),
    String.concat([Gen.header(name), "import ../../src/ring.bend as R\nimport ../../src/norm.bend as N\nimport ../../proofs/norm.bend as NP\nimport ./kinds.bend as K\nimport ./ops.bend as O\n\n", String.join(Ker.prfs(kers), "\n")]),
    String.concat([Gen.header(name), "import ./kinds.bend as K\nimport ./ops.bend as O\n\n",
      "# Every kernel at F32: the runtime instantiation (ADR-002).\n\n", String.join(Ker.apis(kers), "\n")]),
    String.concat([name, ": ", Nat.show(List.length(&2, Kd, ks)), " kinds, ", Nat.show(List.length(&2, Ker, kers)),
      " kernels, ", Nat.show(Ker.total(kers)), " multiplications"])}

def Gen.out(s: GSpec, os: List<&2, Op>, us: List<&2, Op1>) -> Out:
  match s:
    case GSpec{+name, +pre, +d, +gens, +sig, kinds, vs}:
      +ks = Gen.kinds(d, gens, kinds)
      +dn = Nat.show(d) ++ "n"
      Gen.out.go(name, pre, d, sig, ks,
        List.reverse(&2, Ker, Hf.table(d, dn, pre, gens, sig, ks, HAnti{}, ks, Hf.table(d, dn, pre, gens, sig, ks, HComm{}, ks,
          Sw.table(d, dn, pre, gens, sig, ks, vs, ks,
            Ker1.ops(d, dn, ks, us, Ker.ops(d, dn, pre, sig, ks, os, Nil{})))))))
