# Writes proofs/scale.bend: scalar factors distribute over addition, pass
# through MV.mk, and come out of either operand of the geometric product.

import Base
import ./dsl.bend as D

def C.sc(+d: String, +c: String, +x: String) -> String:
  D.cat(["S.MV.scale(~T, ~mul, ", d, ", ", c, ", ", x, ")"])

def C.head() -> String:
  D.cat(["# Scalar factors: scale distributes over addition, passes through MV.mk, and
# comes out of either operand of the geometric product.

import Base
import ../src/ring.bend as R
import ../src/spec.bend as S
import ./base.bend as B
import ./leaf.bend as L
import ./add.bend as A
import ./gp.bend as P

def Scale.add(~T: Data, ~add: T -> T -> T, ~mul: T -> T -> T, ~dist_l: R.Ring.DistL(T, add, mul),
  +d: Nat, +c: T, a: ", D.mv("d"), ", b: ", D.mv("d"), ")
  -> {", C.sc("d", "c", D.add("d", "a", "b")), " == ", D.add("d", C.sc("d", "c", "a"), C.sc("d", "c", "b")), " : ", D.mv("d"), "}:
  match d:
    case 0n:
      match a b:
        case S.LZ{} S.LZ{}:
          {==}
        case S.LZ{} S.L{y}:
          {==}
        case S.L{x} S.LZ{}:
          {==}
        case S.L{x} S.L{y}:
          B.Leaf.cong(T, mul(c, add(x, y)), add(mul(c, x), mul(c, y)), dist_l(c, x, y))
    case 1n+p:
      match a b:
        case S.NZ{} S.NZ{}:
          {==}
        case S.NZ{} S.N{b1, b2}:
          {==}
        case S.N{a1, a2} S.NZ{}:
          {==}
        case S.N{a1, a2} S.N{b1, b2}:
          B.Node.cong2(", D.mv("p"), ", ", C.sc("p", "c", D.add("p", "a1", "b1")), ", ", D.add("p", C.sc("p", "c", "a1"), C.sc("p", "c", "b1")), ",
            ", C.sc("p", "c", D.add("p", "a2", "b2")), ", ", D.add("p", C.sc("p", "c", "a2"), C.sc("p", "c", "b2")), ",
            Scale.add(~T, ~add, ~mul, ~dist_l, p, c, a1, b1), Scale.add(~T, ~add, ~mul, ~dist_l, p, c, a2, b2))

def Scale.mk(~T: Data, ~mul: T -> T -> T, d: Nat, c: T, a: ", D.mv("d"), ", b: ", D.mv("d"), ")
  -> {", C.sc("1n+d", "c", D.mk("d", "a", "b")), " == ", D.mk("d", C.sc("d", "c", "a"), C.sc("d", "c", "b")), " : ", D.mv("1n+d"), "}:
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
              {==}
            case S.N{b1, b2}:
              {==}
        case S.N{a1, a2}:
          {==}
"])

# a term (f, n, x, y) of a level; on the left side the scale sits on x
type Ct is Data:
  Ct{f: String, n: String, x: String, y: String}

def C.lt(+left: Bool, t: Ct) -> String:
  match t:
    case Ct{+f, +n, +x, +y}:
      D.pick(left, D.gpf("p", f, n, C.sc("p", "c", x), y, "rest"), D.gpf("p", f, n, x, C.sc("p", "c", y), "rest"))

def C.g(t: Ct) -> String:
  match t:
    case Ct{f, n, x, y}:
      D.gpf("p", f, n, x, y, "rest")

def C.ih(+h: String, +rec: String, t: Ct) -> String:
  match t:
    case Ct{f, n, x, y}:
      D.cat([rec, "(", h, ", p, ", f, ", ", n, ", c, ", x, ", ", y, ", rest)"])

def C.level(+left: Bool, +h: String, +rec: String, +q: D.Qc) -> String:
  +isz = D.isz(q)
  +nf = D.xor("n", "f")
  +t1 = {Ct{"f", nf, "x1", "y2"} : Ct}
  +t2 = {Ct{D.bnot("f"), "n", "x2", "y1"} : Ct}
  +t3 = {Ct{D.bnot("f"), D.byq(q, nf, nf, D.bnot(nf)), "x1", "y1"} : Ct}
  +t4 = {Ct{"f", "n", "x2", "y2"} : Ct}
  +el = D.add("p", C.lt(left, t1), C.lt(left, t2))
  +en = D.add("p", C.sc("p", "c", C.g(t1)), C.sc("p", "c", C.g(t2)))
  +eel = D.cat(["A.Add.cong(~T, ~add, p, ", C.lt(left, t1), ", ", C.sc("p", "c", C.g(t1)), ", ", C.lt(left, t2), ", ", C.sc("p", "c", C.g(t2)), ", ", C.ih(h, rec, t1), ", ", C.ih(h, rec, t2), ")"])
  +rl = D.pick(isz, C.lt(left, t4), D.add("p", C.lt(left, t3), C.lt(left, t4)))
  +rn = D.pick(isz, C.sc("p", "c", C.g(t4)), D.add("p", C.sc("p", "c", C.g(t3)), C.sc("p", "c", C.g(t4))))
  +erl = D.pick(isz, C.ih(h, rec, t4),
    D.cat(["A.Add.cong(~T, ~add, p, ", C.lt(left, t3), ", ", C.sc("p", "c", C.g(t3)), ", ", C.lt(left, t4), ", ", C.sc("p", "c", C.g(t4)), ", ", C.ih(h, rec, t3), ", ", C.ih(h, rec, t4), ")"]))
  +r0 = D.pick(isz, C.g(t4), D.add("p", C.g(t3), C.g(t4)))
  +er0 = D.pick(isz, "{==}", D.cat(["Scale.add(~T, ~add, ~mul, ~dist_l, p, c, ", C.g(t3), ", ", C.g(t4), ")"]))
  +e0 = D.add("p", C.g(t1), C.g(t2))
  +nfm = D.mk("p", en, rn)
  +rhs = C.sc("1n+p", "c", D.mk("p", e0, r0))
  +lhs_nf = D.cat(["P.Mk.cong(T, p, ", el, ", ", en, ", ", rl, ", ", rn, ",\n  ", eel, ",\n  ", erl, ")"])
  +rhs_nf = D.trans(D.mv("1n+p"), rhs, D.mk("p", C.sc("p", "c", e0), C.sc("p", "c", r0)), nfm,
    D.cat(["Scale.mk(~T, ~mul, p, c, ", e0, ", ", r0, ")"]),
    D.cat(["P.Mk.cong(T, p, ", C.sc("p", "c", e0), ", ", en, ", ", C.sc("p", "c", r0), ", ", rn, ",\n  Scale.add(~T, ~add, ~mul, ~dist_l, p, c, ", C.g(t1), ", ", C.g(t2), "),\n  ", er0, ")"]))
  D.cat(["B.Eq.join(", D.mv("1n+p"), ", ", D.mk("p", el, rl), ", ", rhs, ", ", nfm, ",\n  ", D.ind(lhs_nf, 2n), ",\n  ", D.ind(rhs_nf, 2n), ")"])

def C.levels(+left: Bool, +h: String, +rec: String) -> String:
  D.qcases(C.level(left, h, rec, D.CZ{}), C.level(left, h, rec, D.CP{}), C.level(left, h, rec, D.CN{}), 14n)

def C.gp_l() -> String:
  D.cat(["# a scalar on the left operand comes out in front
def Scale.gp_l(", D.OPSD(), ", ~mul_assoc: R.Ring.Assoc(T, mul), ~dist_l: R.Ring.DistL(T, add, mul),
  ~neg_mul_r: R.Ring.NegMulR(T, mul, neg),
  +d: Nat, +f: Bool, +n: Bool, +c: T, x: ", D.mv("d"), ", y: ", D.mv("d"), ", +sig: S.Sig(d))
  -> {", D.gpf("d", "f", "n", C.sc("d", "c", "x"), "y", "sig"), " == ", C.sc("d", "c", D.gpf("d", "f", "n", "x", "y", "sig")), " : ", D.mv("d"), "}:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          {==}
        case S.L{+a}:
          match y:
            case S.LZ{}:
              {==}
            case S.L{+b}:
              B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, mul(mul(c, a), b)), mul(c, S.Ring.negf(~T, ~neg, n, mul(a, b))),
                Equal.trans(T, S.Ring.negf(~T, ~neg, n, mul(mul(c, a), b)), S.Ring.negf(~T, ~neg, n, mul(c, mul(a, b))),
                  mul(c, S.Ring.negf(~T, ~neg, n, mul(a, b))),
                  Equal.cong(T, T, w => S.Ring.negf(~T, ~neg, n, w), mul(mul(c, a), b), mul(c, mul(a, b)), mul_assoc(c, a, b)),
                  Equal.sym(T, mul(c, S.Ring.negf(~T, ~neg, n, mul(a, b))), S.Ring.negf(~T, ~neg, n, mul(c, mul(a, b))),
                    L.Negf.mul_r(~T, ~mul, ~neg, ~neg_mul_r, n, c, mul(a, b)))))
    case 1n+p:
      match x:
        case S.NZ{}:
          {==}
        case S.N{+x1, +x2}:
          match y:
            case S.NZ{}:
              {==}
            case S.N{+y1, +y2}:
", C.levels(True{}, D.OPS() ++ ", ~mul_assoc, ~dist_l, ~neg_mul_r", "Scale.gp_l"), "
"])

def C.gp_r() -> String:
  D.cat(["# a scalar on the right operand comes out in front (commutative ring)
def Scale.gp_r(", D.OPSD(), ", ~mul_assoc: R.Ring.Assoc(T, mul), ~mul_comm: R.Ring.Comm(T, mul),
  ~dist_l: R.Ring.DistL(T, add, mul), ~neg_mul_r: R.Ring.NegMulR(T, mul, neg),
  +d: Nat, +f: Bool, +n: Bool, +c: T, x: ", D.mv("d"), ", y: ", D.mv("d"), ", +sig: S.Sig(d))
  -> {", D.gpf("d", "f", "n", "x", C.sc("d", "c", "y"), "sig"), " == ", C.sc("d", "c", D.gpf("d", "f", "n", "x", "y", "sig")), " : ", D.mv("d"), "}:
  match d:
    case 0n:
      match x:
        case S.LZ{}:
          {==}
        case S.L{+a}:
          match y:
            case S.LZ{}:
              {==}
            case S.L{+b}:
              B.Leaf.cong(T, S.Ring.negf(~T, ~neg, n, mul(a, mul(c, b))), mul(c, S.Ring.negf(~T, ~neg, n, mul(a, b))),
                Equal.trans(T, S.Ring.negf(~T, ~neg, n, mul(a, mul(c, b))), S.Ring.negf(~T, ~neg, n, mul(c, mul(a, b))),
                  mul(c, S.Ring.negf(~T, ~neg, n, mul(a, b))),
                  Equal.cong(T, T, w => S.Ring.negf(~T, ~neg, n, w), mul(a, mul(c, b)), mul(c, mul(a, b)),
                    Equal.trans(T, mul(a, mul(c, b)), mul(mul(c, a), b), mul(c, mul(a, b)),
                      Equal.trans(T, mul(a, mul(c, b)), mul(mul(a, c), b), mul(mul(c, a), b),
                        Equal.sym(T, mul(mul(a, c), b), mul(a, mul(c, b)), mul_assoc(a, c, b)),
                        Equal.cong(T, T, w => mul(w, b), mul(a, c), mul(c, a), mul_comm(a, c))),
                      mul_assoc(c, a, b))),
                  Equal.sym(T, mul(c, S.Ring.negf(~T, ~neg, n, mul(a, b))), S.Ring.negf(~T, ~neg, n, mul(c, mul(a, b))),
                    L.Negf.mul_r(~T, ~mul, ~neg, ~neg_mul_r, n, c, mul(a, b)))))
    case 1n+p:
      match x:
        case S.NZ{}:
          {==}
        case S.N{+x1, +x2}:
          match y:
            case S.NZ{}:
              {==}
            case S.N{+y1, +y2}:
", C.levels(False{}, D.OPS() ++ ", ~mul_assoc, ~mul_comm, ~dist_l, ~neg_mul_r", "Scale.gp_r"), "
"])

def C.text() -> String:
  D.sep([C.head(), C.gp_l(), C.gp_r()], "\n")
