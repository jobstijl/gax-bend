# Writes proofs/grade.bend: grade projection is additive, and the outer
# product of a j-vector and a k-vector is a (j+k)-vector.

import Base
import ./dsl.bend as D
import ./gen.bend as GE

def Q.gr(+d: String, +k: String, +x: String) -> String:
  D.cat(["S.MV.grade(T, ", d, ", ", k, ", ", x, ")"])

def Q.wf(+d: String, +f: String, +n: String, +x: String, +y: String) -> String:
  D.cat(["S.MV.wedgef(", D.OPS(), ", ", d, ", ", f, ", ", n, ", ", x, ", ", y, ")"])

# x is homogeneous of grade k
def Q.homog(+d: String, +k: String, +x: String) -> String:
  D.cat(["{", Q.gr(d, k, x), " == ", x, " : ", D.mv(d), "}"])

def Q.z(+d: String) -> String:
  GE.N.z(d)

# Constructors and grade projection
# ---------------------------------

def Q.inv(+i: String, +said: String, +which: String) -> String:
  D.cat(["# from mk(a, b) == N{c, d}: ", said, "
def Mk.inv", i, "(-T: Data, d: Nat, a: ", D.mv("d"), ", b: ", D.mv("d"), ", -c: ", D.mv("d"), ", -e: ", D.mv("d"), ",
  h: {", D.mk("d", "a", "b"), " == S.N{c, e} : ", D.mv("1n+d"), "}) -> {", which, " : ", D.mv("d"), "}:
  match d:
    case 0n:
      match a:
        case S.LZ{}:
          match b:
            case S.LZ{}:
              Node.nz(S.Leaf<T>, {S.LZ{} == ", D.pick(String.eq(i, "1"), "c", "e"), " : S.Leaf<T>}, c, e, h)
            case S.L{y}:
              Node.inj", i, "(S.Leaf<T>, S.LZ{}, S.L{y}, c, e, h)
        case S.L{x}:
          Node.inj", i, "(S.Leaf<T>, S.L{x}, b, c, e, h)
    case 1n+p:
      match a:
        case S.NZ{}:
          match b:
            case S.NZ{}:
              Node.nz(", D.mv("1n+p"), ", {S.NZ{} == ", D.pick(String.eq(i, "1"), "c", "e"), " : ", D.mv("1n+p"), "}, c, e, h)
            case S.N{b1, b2}:
              Node.inj", i, "(", D.mv("1n+p"), ", S.NZ{}, S.N{b1, b2}, c, e, h)
        case S.N{a1, a2}:
          Node.inj", i, "(", D.mv("1n+p"), ", S.N{a1, a2}, b, c, e, h)
"])

def Q.head() -> String:
  D.cat(["# Grades: the outer product of a j-vector and a k-vector is a (j+k)-vector.

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S
import ./base.bend as B
import ./add.bend as A
import ./gp.bend as P

# Constructors
# ------------

def Node.e_or(-A: Data, z: A, x: S.Node<A>) -> A:
  match x:
    case S.NZ{}:
      z
    case S.N{e, r}:
      e

def Node.r_or(-A: Data, z: A, x: S.Node<A>) -> A:
  match x:
    case S.NZ{}:
      z
    case S.N{e, r}:
      r

def Node.inj1(-A: Data, -a: A, -b: A, -c: A, -d: A, e: {S.N{a, b} == S.N{c, d} : S.Node<A>}) -> {a == c : A}:
  Equal.cong(S.Node<A>, A, w => Node.e_or(A, a, w), S.N{a, b}, S.N{c, d}, e)

def Node.inj2(-A: Data, -a: A, -b: A, -c: A, -d: A, e: {S.N{a, b} == S.N{c, d} : S.Node<A>}) -> {b == d : A}:
  Equal.cong(S.Node<A>, A, w => Node.r_or(A, b, w), S.N{a, b}, S.N{c, d}, e)

def Node.disc(-A: Data, x: S.Node<A>) -> Type:
  match x:
    case S.NZ{}:
      Unit
    case S.N{e, r}:
      Empty

def Node.nz.empty(-A: Data, -c: A, -d: A, e: {S.NZ{} == S.N{c, d} : S.Node<A>}) -> Empty:
  %e : Node.disc(A, _)
  Unit{}

# zero is not a level
def Node.nz(-A: Data, -B: Type, -c: A, -d: A, e: {S.NZ{} == S.N{c, d} : S.Node<A>}) -> B:
  Empty.absurd(B, Node.nz.empty(A, c, d, e))

", Q.inv("1", "a == c", "a == c"), "
", Q.inv("2", "b == d", "b == e"), "
def Leaf.disc(-T: Data, x: S.Leaf<T>) -> Type:
  match x:
    case S.LZ{}:
      Unit
    case S.L{a}:
      Empty

def Leaf.lz.empty(-T: Data, -a: T, e: {S.LZ{} == S.L{a} : S.Leaf<T>}) -> Empty:
  %e : Leaf.disc(T, _)
  Unit{}

# a leaf zero is not a coefficient
def Leaf.lz(-T: Data, -B: Type, -a: T, e: {S.LZ{} == S.L{a} : S.Leaf<T>}) -> B:
  Empty.absurd(B, Leaf.lz.empty(T, a, e))

def Nat.add_succ_r(j: Nat, +k: Nat) -> {Nat.add(j, 1n+k) == 1n+Nat.add(j, k) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+i:
      Equal.cong(Nat, Nat, w => 1n+w, Nat.add(i, 1n+k), 1n+Nat.add(i, k), Nat.add_succ_r(i, k))

"])

def Q.proj() -> String:
  D.cat(["# Grade projection
# ----------------

def Grade.zero(-T: Data, d: Nat, k: Nat) -> {", Q.gr("d", "k", Q.z("d")), " == ", Q.z("d"), " : ", D.mv("d"), "}:
  match d:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case 1n+p:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}

def Grade.idx(-T: Data, -d: Nat, -k: Nat, -k2: Nat, -x: ", D.mv("d"), ", e: {k == k2 : Nat})
  -> {", Q.gr("d", "k", "x"), " == ", Q.gr("d", "k2", "x"), " : ", D.mv("d"), "}:
  %e : {", Q.gr("d", "k", "x"), " == ", Q.gr("d", "_", "x"), " : ", D.mv("d"), "}
  {==}

# a grade projection keeps the zero level of MV.mk
def Grade.mk_s(-T: Data, +d: Nat, +j: Nat, a: ", D.mv("d"), ", b: ", D.mv("d"), ")
  -> {", Q.gr("1n+d", "1n+j", D.mk("d", "a", "b")), " == ", D.mk("d", Q.gr("d", "j", "a"), Q.gr("d", "1n+j", "b")), " : ", D.mv("1n+d"), "}:
  match d:
    case 0n:
      match a:
        case S.LZ{}:
          match b:
            case S.LZ{}:
              Equal.sym(", D.mv("1n"), ", ", D.mk("0n", Q.gr("0n", "j", "S.LZ{}"), Q.gr("0n", "1n+j", "S.LZ{}")), ", S.NZ{},
                P.Mk.cong(T, 0n, ", Q.gr("0n", "j", "S.LZ{}"), ", S.LZ{}, ", Q.gr("0n", "1n+j", "S.LZ{}"), ", S.LZ{},
                  Grade.zero(T, 0n, j), {==}))
            case S.L{y}:
              {==}
        case S.L{x}:
          {==}
    case 1n+p:
      match a:
        case S.NZ{}:
          match b:
            case S.NZ{}:
              Equal.sym(", D.mv("2n+p"), ", ", D.mk("1n+p", Q.gr("1n+p", "j", "S.NZ{}"), Q.gr("1n+p", "1n+j", "S.NZ{}")), ", S.NZ{},
                P.Mk.cong(T, 1n+p, ", Q.gr("1n+p", "j", "S.NZ{}"), ", S.NZ{}, ", Q.gr("1n+p", "1n+j", "S.NZ{}"), ", S.NZ{},
                  Grade.zero(T, 1n+p, j), Grade.zero(T, 1n+p, 1n+j)))
            case S.N{b1, b2}:
              {==}
        case S.N{a1, a2}:
          {==}

def Grade.mk_0(-T: Data, +d: Nat, a: ", D.mv("d"), ", b: ", D.mv("d"), ")
  -> {", Q.gr("1n+d", "0n", D.mk("d", "a", "b")), " == ", D.mk("d", Q.z("d"), Q.gr("d", "0n", "b")), " : ", D.mv("1n+d"), "}:
  match d:
    case 0n:
      match a:
        case S.LZ{}:
          match b:
            case S.LZ{}:
              {==}
            case S.L{y}:
              {==}
        case S.L{x}:
          {==}
    case 1n+p:
      match a:
        case S.NZ{}:
          match b:
            case S.NZ{}:
              Equal.sym(", D.mv("2n+p"), ", ", D.mk("1n+p", Q.z("1n+p"), Q.gr("1n+p", "0n", "S.NZ{}")), ", S.NZ{},
                P.Mk.cong(T, 1n+p, ", Q.z("1n+p"), ", S.NZ{}, ", Q.gr("1n+p", "0n", "S.NZ{}"), ", S.NZ{},
                  {==}, Grade.zero(T, 1n+p, 0n)))
            case S.N{b1, b2}:
              {==}
        case S.N{a1, a2}:
          {==}
"])

# Grade.add
# ---------

def Q.ga.join(+left: String, +right: String, +mid: String, +s1: String, +s2: String) -> String:
  D.cat(["B.Eq.join(", D.mv("1n+p"), ", ", left, ", ", right, ", ", mid, ",\n  ", D.ind(s1, 2n), ",\n  ", D.ind(s2, 2n), ")"])

# the node case at grade 0: only the r level survives
def Q.ga.node0() -> String:
  +z = Q.z("p")
  +g2 = Q.gr("p", "0n", D.add("p", "a2", "b2"))
  +g2s = D.add("p", Q.gr("p", "0n", "a2"), Q.gr("p", "0n", "b2"))
  +mid = D.mk("p", z, g2s)
  +right = D.add("1n+p", D.mk("p", z, Q.gr("p", "0n", "a2")), D.mk("p", z, Q.gr("p", "0n", "b2")))
  +mid2 = D.mk("p", D.add("p", z, z), g2s)
  +s1 = GE.N.mcong("p", z, z, g2, g2s, "{==}", "Grade.add(~T, ~add, p, 0n, a2, b2)")
  +s2 = D.cat(["A.Add.mk(~T, ~add, p, ", z, ", ", Q.gr("p", "0n", "a2"), ", ", z, ", ", Q.gr("p", "0n", "b2"), ")"])
  +s3 = GE.N.mcong("p", D.add("p", z, z), z, g2s, g2s, GE.N.zl_add("p"), "{==}")
  Q.ga.join(D.mk("p", z, g2), right, mid, s1, D.trans(D.mv("1n+p"), right, mid2, mid, s2, s3))

# the node case at grade 1+j: both levels project
def Q.ga.nodej() -> String:
  +g1 = Q.gr("p", "j", D.add("p", "a1", "b1"))
  +g1s = D.add("p", Q.gr("p", "j", "a1"), Q.gr("p", "j", "b1"))
  +g2 = Q.gr("p", "1n+j", D.add("p", "a2", "b2"))
  +g2s = D.add("p", Q.gr("p", "1n+j", "a2"), Q.gr("p", "1n+j", "b2"))
  +right = D.add("1n+p", D.mk("p", Q.gr("p", "j", "a1"), Q.gr("p", "1n+j", "a2")), D.mk("p", Q.gr("p", "j", "b1"), Q.gr("p", "1n+j", "b2")))
  +s1 = GE.N.mcong("p", g1, g1s, g2, g2s, "Grade.add(~T, ~add, p, j, a1, b1)", "Grade.add(~T, ~add, p, 1n+j, a2, b2)")
  +s2 = D.cat(["A.Add.mk(~T, ~add, p, ", Q.gr("p", "j", "a1"), ", ", Q.gr("p", "1n+j", "a2"), ", ", Q.gr("p", "j", "b1"), ", ", Q.gr("p", "1n+j", "b2"), ")"])
  Q.ga.join(D.mk("p", g1, g2), right, D.mk("p", g1s, g2s), s1, s2)

def Q.ga.k(+kk: String, +node: String) -> String:
  +g = Q.gr("1n+p", kk, "S.N{a1, a2}")
  D.cat(["match a:
  case S.NZ{}:
    {==}
  case S.N{+a1, +a2}:
    match b:
      case S.NZ{}:
        Equal.sym(", D.mv("1n+p"), ", ", D.add("1n+p", g, "S.NZ{}"), ", ", g, ",
          A.Add.zero_r(~T, ~add, 1n+p, ", g, "))
      case S.N{+b1, +b2}:
", D.ind(node, 8n)])

def Q.add() -> String:
  D.cat(["# grade projection is additive
def Grade.add(~T: Data, ~add: T -> T -> T, +d: Nat, +k: Nat, a: ", D.mv("d"), ", b: ", D.mv("d"), ")
  -> {", Q.gr("d", "k", D.add("d", "a", "b")), " == ", D.add("d", Q.gr("d", "k", "a"), Q.gr("d", "k", "b")), " : ", D.mv("d"), "}:
  match d:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case 1n+p:
      match k:
        case 0n:
", D.ind(Q.ga.k("0n", Q.ga.node0()), 10n), "
        case 1n+j:
", D.ind(Q.ga.k("1n+j", Q.ga.nodej()), 10n), "

def Wedge.zero_l(", D.OPSD(), ", d: Nat, f: Bool, n: Bool, y: ", D.mv("d"), ") -> {", Q.wf("d", "f", "n", Q.z("d"), "y"), " == ", Q.z("d"), " : ", D.mv("d"), "}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Wedge.zero_r(", D.OPSD(), ", d: Nat, f: Bool, n: Bool, x: ", D.mv("d"), ") -> {", Q.wf("d", "f", "n", "x", Q.z("d")), " == ", Q.z("d"), " : ", D.mv("d"), "}:
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
        case S.N{a, b}:
          {==}
"])

# The outer product of homogeneous operands
# -----------------------------------------
# At level 1+p, x = N{x1, x2} and y = N{y1, y2}; the e level of the wedge
# is w1 + w2 and the r level is rw.

def Q.nf() -> String:
  D.xor("n", "f")

def Q.w1() -> String:
  Q.wf("p", "f", Q.nf(), "x1", "y2")

def Q.w2() -> String:
  Q.wf("p", D.bnot("f"), "n", "x2", "y1")

def Q.rw() -> String:
  Q.wf("p", "f", "n", "x2", "y2")

def Q.E() -> String:
  D.add("p", Q.w1(), Q.w2())

def Q.ih(+f: String, +n: String, +j: String, +k: String, +x: String, +y: String, +hx: String, +hy: String) -> String:
  D.cat(["Wedge.grade(", D.OPS(), ", p, ", f, ", ", n, ", ", j, ", ", k, ", ", x, ", ", y, ", ", hx, ", ", hy, ")"])

def Q.mkinv(+i: String, +a: String, +b: String, +c: String, +e: String, +h: String) -> String:
  D.cat(["Mk.inv", i, "(T, p, ", a, ", ", b, ", ", c, ", ", e, ", ", h, ")"])

# the four split hypotheses, given what x and y project to
def Q.hyps(+xa: String, +xb: String, +ya: String, +yb: String) -> String:
  D.cat(["+hx1 = ", Q.mkinv("1", xa, xb, "x1", "x2", "hx"), "\n+hx2 = ", Q.mkinv("2", xa, xb, "x1", "x2", "hx"),
    "\n+hy1 = ", Q.mkinv("1", ya, yb, "y1", "y2", "hy"), "\n+hy2 = ", Q.mkinv("2", ya, yb, "y1", "y2", "hy"), "\n"])

# grade s of the e level and grade 1+s of the r level give back the wedge
def Q.body(+s: String, +i1: String, +i2: String, +i3: String) -> String:
  +e = Q.E()
  +rw = Q.rw()
  +w1 = Q.w1()
  +w2 = Q.w2()
  +s1 = D.cat(["1n+", s])
  +ee = D.trans(D.mv("p"), Q.gr("p", s, e), D.add("p", Q.gr("p", s, w1), Q.gr("p", s, w2)), e,
    D.cat(["Grade.add(~T, ~add, p, ", s, ", ", w1, ", ", w2, ")"]), GE.N.acong("p", Q.gr("p", s, w1), w1, Q.gr("p", s, w2), w2, i1, i2))
  D.trans(D.mv("1n+p"), Q.gr("1n+p", s1, D.mk("p", e, rw)), D.mk("p", Q.gr("p", s, e), Q.gr("p", s1, rw)), D.mk("p", e, rw),
    D.cat(["Grade.mk_s(T, p, ", s, ", ", e, ", ", rw, ")"]), GE.N.mcong("p", Q.gr("p", s, e), e, Q.gr("p", s1, rw), rw, ee, i3))

def Q.css() -> String:
  +s = {"Nat.add(j2, 1n+k2)" : String}
  +w2 = Q.w2()
  +i1 = Q.ih("f", Q.nf(), "j2", "1n+k2", "x1", "y2", "hx1", "hy2")
  +i2 = D.trans(D.mv("p"), Q.gr("p", s, w2), Q.gr("p", "1n+Nat.add(j2, k2)", w2), w2,
    D.cat(["Grade.idx(T, p, ", s, ", 1n+Nat.add(j2, k2), ", w2, ", Nat.add_succ_r(j2, k2))"]),
    Q.ih(D.bnot("f"), "n", "1n+j2", "k2", "x2", "y1", "hx2", "hy1"))
  +i3 = Q.ih("f", "n", "1n+j2", "1n+k2", "x2", "y2", "hx2", "hy2")
  D.cat([Q.hyps(Q.gr("p", "j2", "x1"), Q.gr("p", "1n+j2", "x2"), Q.gr("p", "k2", "y1"), Q.gr("p", "1n+k2", "y2")), Q.body(s, i1, i2, i3)])

def Q.c0s() -> String:
  +i2 = Q.ih(D.bnot("f"), "n", "0n", "k2", "x2", "y1", "hx2", "hy1")
  +i3 = Q.ih("f", "n", "0n", "1n+k2", "x2", "y2", "hx2", "hy2")
  D.cat([Q.hyps(Q.z("p"), Q.gr("p", "0n", "x2"), Q.gr("p", "k2", "y1"), Q.gr("p", "1n+k2", "y2")),
    "+zx1 = Wedge.grade.zl(", D.OPS(), ", p, f, ", Q.nf(), ", k2, x1, y2, hx1)\n", Q.body("k2", "zx1", i2, i3)])

def Q.cs0() -> String:
  +t = {"Nat.add(j2, 0n)" : String}
  +i1 = Q.ih("f", Q.nf(), "j2", "0n", "x1", "y2", "hx1", "hy2")
  +i3 = Q.ih("f", "n", "1n+j2", "0n", "x2", "y2", "hx2", "hy2")
  D.cat([Q.hyps(Q.gr("p", "j2", "x1"), Q.gr("p", "1n+j2", "x2"), Q.z("p"), Q.gr("p", "0n", "y2")),
    "+zy1 = Wedge.grade.zr(", D.OPS(), ", p, ", D.bnot("f"), ", n, ", t, ", x2, y1, hy1)\n", Q.body(t, i1, "zy1", i3)])

def Q.c00() -> String:
  +z = Q.z("p")
  +e = Q.E()
  +rw = Q.rw()
  +i3 = Q.ih("f", "n", "0n", "0n", "x2", "y2", "hx2", "hy2")
  +eez = D.trans(D.mv("p"), e, D.add("p", z, z), z, GE.N.acong("p", Q.w1(), z, Q.w2(), z, "ex1", "ey1"), GE.N.zl_add("p"))
  +body = D.trans(D.mv("1n+p"), Q.gr("1n+p", "0n", D.mk("p", e, rw)), D.mk("p", z, Q.gr("p", "0n", rw)), D.mk("p", e, rw),
    D.cat(["Grade.mk_0(T, p, ", e, ", ", rw, ")"]),
    GE.N.mcong("p", z, e, Q.gr("p", "0n", rw), rw, D.sym(D.mv("p"), e, z, eez), i3))
  D.cat([Q.hyps(z, Q.gr("p", "0n", "x2"), z, Q.gr("p", "0n", "y2")),
    "+ex1 = Wedge.grade.zx(", D.OPS(), ", p, f, ", Q.nf(), ", x1, y2, hx1)\n",
    "+ey1 = Wedge.grade.zy(", D.OPS(), ", p, ", D.bnot("f"), ", n, x2, y1, hy1)\n", body])

def Q.jk(+jc: String, +kc: String, +body: String) -> String:
  +s = D.cat(["Nat.add(", jc, ", ", kc, ")"])
  D.cat(["match x:
  case S.NZ{}:
    Grade.zero(T, 1n+p, ", s, ")
  case S.N{+x1, +x2}:
    match y:
      case S.NZ{}:
        Grade.zero(T, 1n+p, ", s, ")
      case S.N{+y1, +y2}:
", D.ind(body, 8n)])

# grade k of a wedge whose zero operand is the left (l) or right (r) one;
# h says zero == that operand
def Q.zero_by(+side: Bool, +other: String) -> String:
  +z = Q.z("p")
  +tz = D.pick(side, Q.wf("p", "f", "n", z, other), Q.wf("p", "f", "n", other, z))
  +wz = D.pick(side, D.cat(["Wedge.zero_l(", D.OPS(), ", p, f, n, ", other, ")"]), D.cat(["Wedge.zero_r(", D.OPS(), ", p, f, n, ", other, ")"]))
  +hole = D.pick(side, Q.wf("p", "f", "n", "_", other), Q.wf("p", "f", "n", other, "_"))
  +motive = D.cat(["{", Q.gr("p", "k", hole), " == ", hole, " : ", D.mv("p"), "}"])
  +inner = D.trans(D.mv("p"), Q.gr("p", "k", tz), z, tz,
    D.trans(D.mv("p"), Q.gr("p", "k", tz), Q.gr("p", "k", z), z,
      D.cat(["Equal.cong(", D.mv("p"), ", ", D.mv("p"), ", w => ", Q.gr("p", "k", "w"), ", ", tz, ", ", z, ", ", wz, ")"]), "Grade.zero(T, p, k)"),
    D.sym(D.mv("p"), tz, z, wz))
  D.cat(["%h : ", motive, "\n", inner])

def Q.wedge() -> String:
  +z = Q.z("p")
  D.cat(["# a wedge with a zero left operand is zero in every grade
def Wedge.grade.zl(", D.OPSD(), ", +p: Nat, +f: Bool, +n: Bool, +k: Nat, -x1: ", D.mv("p"), ", +y2: ", D.mv("p"), ", h: {", z, " == x1 : ", D.mv("p"), "})
  -> {", Q.gr("p", "k", Q.wf("p", "f", "n", "x1", "y2")), " == ", Q.wf("p", "f", "n", "x1", "y2"), " : ", D.mv("p"), "}:
  ", D.ind(Q.zero_by(True{}, "y2"), 2n), "

# a wedge with a zero right operand is zero in every grade
def Wedge.grade.zr(", D.OPSD(), ", +p: Nat, +f: Bool, +n: Bool, +k: Nat, +x2: ", D.mv("p"), ", -y1: ", D.mv("p"), ", h: {", z, " == y1 : ", D.mv("p"), "})
  -> {", Q.gr("p", "k", Q.wf("p", "f", "n", "x2", "y1")), " == ", Q.wf("p", "f", "n", "x2", "y1"), " : ", D.mv("p"), "}:
  ", D.ind(Q.zero_by(False{}, "x2"), 2n), "

# a wedge with a zero operand is zero
def Wedge.grade.zx(", D.OPSD(), ", +p: Nat, +f: Bool, +n: Bool, -x1: ", D.mv("p"), ", +y2: ", D.mv("p"), ", h: {", z, " == x1 : ", D.mv("p"), "})
  -> {", Q.wf("p", "f", "n", "x1", "y2"), " == ", z, " : ", D.mv("p"), "}:
  %h : {", Q.wf("p", "f", "n", "_", "y2"), " == ", z, " : ", D.mv("p"), "}
  Wedge.zero_l(", D.OPS(), ", p, f, n, y2)

def Wedge.grade.zy(", D.OPSD(), ", +p: Nat, +f: Bool, +n: Bool, +x2: ", D.mv("p"), ", -y1: ", D.mv("p"), ", h: {", z, " == y1 : ", D.mv("p"), "})
  -> {", Q.wf("p", "f", "n", "x2", "y1"), " == ", z, " : ", D.mv("p"), "}:
  %h : {", Q.wf("p", "f", "n", "x2", "_"), " == ", z, " : ", D.mv("p"), "}
  Wedge.zero_r(", D.OPS(), ", p, f, n, x2)

# the outer product of a j-vector and a k-vector is a (j+k)-vector
def Wedge.grade(", D.OPSD(), ", +d: Nat, +f: Bool, +n: Bool, +j: Nat, +k: Nat, x: ", D.mv("d"), ", y: ", D.mv("d"), ",
  +hx: ", Q.homog("d", "j", "x"), ", +hy: ", Q.homog("d", "k", "y"), ")
  -> ", Q.homog("d", "Nat.add(j, k)", Q.wf("d", "f", "n", "x", "y")), ":
  match d:
    case 0n:
      match j:
        case 0n:
          match k:
            case 0n:
              {==}
            case 1n+k2:
              match x:
                case S.LZ{}:
                  match y:
                    case S.LZ{}:
                      {==}
                    case S.L{b}:
                      Leaf.lz(T, ", Q.homog("0n", "1n+k2", Q.wf("0n", "f", "n", "S.LZ{}", "S.L{b}")), ", b, hy)
                case S.L{a}:
                  match y:
                    case S.LZ{}:
                      {==}
                    case S.L{b}:
                      Leaf.lz(T, ", Q.homog("0n", "1n+k2", Q.wf("0n", "f", "n", "S.L{a}", "S.L{b}")), ", b, hy)
        case 1n+j2:
          match x:
            case S.LZ{}:
              {==}
            case S.L{a}:
              Leaf.lz(T, ", Q.homog("0n", "Nat.add(1n+j2, k)", Q.wf("0n", "f", "n", "S.L{a}", "y")), ", a, hx)
    case 1n+p:
      match j:
        case 0n:
          match k:
            case 0n:
", D.ind(Q.jk("0n", "0n", Q.c00()), 14n), "
            case 1n+k2:
", D.ind(Q.jk("0n", "1n+k2", Q.c0s()), 14n), "
        case 1n+j2:
          match k:
            case 0n:
", D.ind(Q.jk("1n+j2", "0n", Q.cs0()), 14n), "
            case 1n+k2:
", D.ind(Q.jk("1n+j2", "1n+k2", Q.css()), 14n), "
"])

def Q.text() -> String:
  D.sep([D.cat([Q.head(), Q.proj()]), Q.add(), Q.wedge()], "\n")
