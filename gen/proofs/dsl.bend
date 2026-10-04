# The proof writer's vocabulary: Bend source for the terms and proof steps
# the Layer-S proofs are made of. Every function returns source text; the
# proof modules (gen/proofs/*.bend) assemble it into proofs/*.bend.

import Base

# Text
# ----
# Proof text runs to hundreds of kilobytes, and strings are lists of
# characters, so every operation here is tail-recursive: a non-tail walk
# over a long string overflows the runtime's stack.

# the characters of s, reversed, in front of acc
def rev(s: String, acc: String) -> String:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      rev(t, SCon{h, acc})

# a ++ b, in time |a| and constant stack
def app(a: String, b: String) -> String:
  rev(rev(a, SNil{}), b)

def cat.go(xs: List<&2, String>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      cat.go(t, app(x, acc))

def cat(xs: List<&2, String>) -> String:
  cat.go(List.reverse(&2, String, xs), "")

def sep.go(xs: List<&2, String>, +s: String, acc: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      sep.go(t, s, x <> (s <> acc))

def sep(xs: List<&2, String>, +s: String) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> t:
      cat(List.reverse(&2, String, sep.go(t, s, [x])))

# pad every non-empty line of s by k spaces
def ind.emit(+c: Char, +pad: String, nl: Bool, start: Bool, acc: String) -> String:
  match nl:
    case True{}:
      SCon{c, acc}
    case False{}:
      match start:
        case True{}:
          SCon{c, rev(pad, acc)}
        case False{}:
          SCon{c, acc}

def ind.go(s: String, +pad: String, start: Bool, acc: String) -> String:
  match s:
    case SNil{}:
      rev(acc, SNil{})
    case SCon{+c, t}:
      +nl = Char.is_eq(c, '\n')
      ind.go(t, pad, nl, ind.emit(c, pad, nl, start, acc))

def ind(s: String, k: Nat) -> String:
  ind.go(s, String.repeat(" ", k), True{}, SNil{})

# s without trailing newlines
def rstrip.go.if(c: Char, t: String, nl: Bool) -> String:
  match nl:
    case True{}:
      t
    case False{}:
      SCon{c, t}

def rstrip.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      rstrip.go.if(c, t, Char.is_eq(c, '\n'))

# drop the leading newlines of s (s is the reversed text)
def rstrip.drop(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+k:
      rstrip.drop(k, rstrip.go(s))

def rstrip(s: String) -> String:
  rev(rstrip.drop(8n, rev(s, SNil{})), SNil{})

# Terms
# -----

def OPS() -> String:
  "~T, ~add, ~mul, ~neg"

def OPSD() -> String:
  "~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~neg: T -> T"

def F() -> String:
  "False{}"

def Tr() -> String:
  "True{}"

def gpf(d: String, f: String, n: String, x: String, y: String, s: String) -> String:
  cat(["S.MV.gpf(", OPS(), ", ", d, ", ", f, ", ", n, ", ", x, ", ", y, ", ", s, ")"])

def add(d: String, a: String, b: String) -> String:
  cat(["S.MV.add(~T, ~add, ", d, ", ", a, ", ", b, ")"])

def mk(d: String, e: String, r: String) -> String:
  cat(["S.MV.mk(T, ", d, ", ", e, ", ", r, ")"])

def sgn(d: String, n: String, f: String, r: String, x: String) -> String:
  cat(["S.MV.sgn(~T, ~neg, ", d, ", ", n, ", ", f, ", ", r, ", ", x, ")"])

def mv(d: String) -> String:
  cat(["S.MV(T, ", d, ")"])

def xor(a: String, b: String) -> String:
  "Bool.xor(" ++ a ++ ", " ++ b ++ ")"

def bnot(a: String) -> String:
  "Bool.not(" ++ a ++ ")"

# Proof steps
# -----------

# Equal.trans with its two proofs indented (the form most modules use)
def trans(A: String, a: String, b: String, c: String, p1: String, p2: String) -> String:
  cat(["Equal.trans(", A, ", ", a, ", ", b, ", ", c, ",\n  ", ind(p1, 2n), ",\n  ", ind(p2, 2n), ")"])

def sym(A: String, a: String, b: String, p: String) -> String:
  cat(["Equal.sym(", A, ", ", a, ", ", b, ",\n  ", ind(p, 2n), ")"])

# the unindented forms (the distributivity proofs use these)
def trans0(A: String, a: String, b: String, c: String, p1: String, p2: String) -> String:
  cat(["Equal.trans(", A, ", ", a, ", ", b, ", ", c, ",\n  ", p1, ",\n  ", p2, ")"])

def sym0(A: String, a: String, b: String, p: String) -> String:
  cat(["Equal.sym(", A, ", ", a, ", ", b, ",\n  ", p, ")"])

# Gp.flag under a module prefix ("" inside gp.bend, "P." elsewhere)
def gflag(pre: String, d: String, f: String, f2: String, n: String, n2: String, x: String, y: String, s: String, ef: String, en: String) -> String:
  cat([pre, "Gp.flag(", OPS(), ", ", d, ", ", f, ", ", f2, ", ", n, ", ", n2, ", ", x, ", ", y, ", ", s, ",\n  ", ef, ",\n  ", en, ")"])

# the three metric cases of a level, each body under its case, indented by k
def qcases(bz: String, bp: String, bn: String, k: Nat) -> String:
  ind(rstrip(cat(["match sig:\n  case S.Gen{q, +rest}:\n    match q:\n",
    "      case S.QZ{}:\n", ind(bz, 8n), "\n",
    "      case S.QP{}:\n", ind(bp, 8n), "\n",
    "      case S.QN{}:\n", ind(bn, 8n), "\n"])), k)

# Flag identities
# ---------------

# an equation between xor/not terms of the named Bool variables
type Fl is Data:
  Fl{name: String, vars: List<&2, String>, lhs: String, rhs: String}

def flag.call(name: String, args: List<&2, String>) -> String:
  "F.Flag." ++ name ++ "(" ++ String.join(args, ", ") ++ ")"

def flag.has(+name: String, fs: List<&2, Fl>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Fl{n, v, l, r} <> t:
      Bool.or(String.eq(n, name), flag.has(name, t))

# the first occurrence of each name, in order
def flag.dedup.put(f: Fl, acc: List<&2, Fl>, seen: Bool) -> List<&2, Fl>:
  match seen:
    case True{}:
      acc
    case False{}:
      f <> acc

def flag.dedup.go(fs: List<&2, Fl>, acc: List<&2, Fl>) -> List<&2, Fl>:
  match fs:
    case Nil{}:
      List.reverse(&2, Fl, acc)
    case Fl{+n, v, l, r} <> t:
      +acc2 = acc
      flag.dedup.go(t, flag.dedup.put(Fl{n, v, l, r}, acc2, flag.has(n, acc2)))

def flag.dedup(fs: List<&2, Fl>) -> List<&2, Fl>:
  flag.dedup.go(fs, Nil{})

def flag.prefix(+h: String, xs: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      (h <> x) <> flag.prefix(h, t)

# every assignment of False{}/True{} to n variables, the last fastest
def flag.combos(n: Nat) -> List<&2, List<&2, String>>:
  match n:
    case 0n:
      [Nil{}]
    case 1n+k:
      +rest = flag.combos(k)
      List.append(&2, List<&2, String>, flag.prefix("False{}", rest), flag.prefix("True{}", rest))

def flag.cases(cs: List<&2, List<&2, String>>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      ("    case " ++ String.join(c, " ") ++ ":") <> ("      {==}" <> flag.cases(t))

def flag.sig(vs: List<&2, String>) -> List<&2, String>:
  match vs:
    case Nil{}:
      Nil{}
    case v <> t:
      (v ++ ": Bool") <> flag.sig(t)

def flag.lemma(f: Fl) -> List<&2, String>:
  match f:
    case Fl{n, +vs, l, r}:
      List.append(&2, String,
        [cat(["def Flag.", n, "(", String.join(flag.sig(vs), ", "), ") -> {", l, " == ", r, " : Bool}:"]),
         "  match " ++ String.join(vs, " ") ++ ":"],
        List.append(&2, String, flag.cases(flag.combos(List.length(&2, String, vs))), [""]))

def flag.lemmas(fs: List<&2, Fl>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> t:
      List.append(&2, String, flag.lemma(f), flag.lemmas(t))

# proofs/flags.bend
def flag.module(fs: List<&2, Fl>) -> String:
  sep("# Flag identities: each is an equation between xor/not terms of Bool\n# flags, proven by checking every case. Generated alongside the proofs that\n# use them.\n\nimport Base\n" <> flag.lemmas(flag.dedup(fs)), "\n")

# Metric cases
# ------------

# the three cases of a level's metric, as the proofs branch on them
type Qc is Data:
  CZ{}
  CP{}
  CN{}

# a when c, else b
def pick(c: Bool, a: String, b: String) -> String:
  match c:
    case True{}:
      a
    case False{}:
      b

# a for QZ, b for QP, c for QN
def byq(q: Qc, a: String, b: String, c: String) -> String:
  match q:
    case CZ{}:
      a
    case CP{}:
      b
    case CN{}:
      c

def isz(q: Qc) -> Bool:
  match q:
    case CZ{}:
      True{}
    case CP{}:
      False{}
    case CN{}:
      False{}
