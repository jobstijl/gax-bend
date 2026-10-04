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

# Specs
# -----

# a kind: its name, whether it may be a result (gax's `part` may not), and
# its blades as written, each a list of generator indices (e032 is [0,3,2])
type GKind is Data:
  GKind{name: String, res: Bool, blades: List<&2, List<&2, Nat>>}

# an algebra: name, module prefix, generator names, signature, kinds
type GSpec is Data:
  GSpec{name: String, pre: String, d: Nat, gens: List<&2, String>, sig: S.Sig(d), kinds: List<&2, GKind>}

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
        String.join(Kd.getters(n, Kd.fields(bls, "", ""), bls), "\n")])

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

# Tables and files
# ----------------

def Ker.push(m: Maybe<&2, Ker>, acc: List<&2, Ker>) -> List<&2, Ker>:
  match m:
    case None{}:
      acc
    case Some{k}:
      k <> acc

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
    String.concat([Gen.header(name), "import ./kinds.bend as K\nimport ./ops.bend as O\n\n", String.join(Ker.prfs(kers), "\n")]),
    String.concat([Gen.header(name), "import ./kinds.bend as K\nimport ./ops.bend as O\n\n",
      "# Every kernel at F32: the runtime instantiation (ADR-002).\n\n", String.join(Ker.apis(kers), "\n")]),
    String.concat([name, ": ", Nat.show(List.length(&2, Kd, ks)), " kinds, ", Nat.show(List.length(&2, Ker, kers)),
      " kernels, ", Nat.show(Ker.total(kers)), " multiplications"])}

def Gen.out(s: GSpec, os: List<&2, Op>, us: List<&2, Op1>) -> Out:
  match s:
    case GSpec{+name, +pre, +d, +gens, +sig, kinds}:
      +ks = Gen.kinds(d, gens, kinds)
      +dn = Nat.show(d) ++ "n"
      Gen.out.go(name, pre, d, sig, ks,
        List.reverse(&2, Ker, Ker1.ops(d, dn, ks, us, Ker.ops(d, dn, pre, sig, ks, os, Nil{}))))
