# Flag identities: each is an equation between xor/not terms of Bool
# flags, proven by checking every case. Generated alongside the proofs that
# use them.

import Base

def Flag.sr_a(n: Bool, f: Bool, m: Bool) -> {Bool.xor(Bool.xor(n, f), m) == Bool.xor(Bool.xor(n, m), f) : Bool}:
  match n f m:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def Flag.sr_b(n: Bool, m: Bool) -> {Bool.xor(n, Bool.xor(m, False{})) == Bool.xor(n, m) : Bool}:
  match n m:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Flag.sr_cp(n: Bool, f: Bool, m: Bool) -> {Bool.xor(Bool.xor(n, f), Bool.xor(m, False{})) == Bool.xor(Bool.xor(n, m), f) : Bool}:
  match n f m:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def Flag.sr_cn(n: Bool, f: Bool, m: Bool) -> {Bool.xor(Bool.not(Bool.xor(n, f)), Bool.xor(m, False{})) == Bool.not(Bool.xor(Bool.xor(n, m), f)) : Bool}:
  match n f m:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def Flag.sl_a(f: Bool, g: Bool) -> {Bool.xor(f, Bool.xor(g, False{})) == Bool.xor(f, g) : Bool}:
  match f g:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Flag.sl_b(n: Bool, f: Bool, m: Bool, g: Bool) -> {Bool.xor(Bool.xor(n, f), Bool.xor(m, g)) == Bool.xor(Bool.xor(n, m), Bool.xor(f, g)) : Bool}:
  match n f m g:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.sl_c(f: Bool, g: Bool) -> {Bool.xor(Bool.not(f), g) == Bool.not(Bool.xor(f, g)) : Bool}:
  match f g:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Flag.sl_d(f: Bool, g: Bool) -> {Bool.xor(Bool.not(f), Bool.xor(g, False{})) == Bool.not(Bool.xor(f, g)) : Bool}:
  match f g:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Flag.sl_e(n: Bool, f: Bool, m: Bool, g: Bool) -> {Bool.xor(Bool.not(Bool.xor(n, f)), Bool.xor(m, g)) == Bool.not(Bool.xor(Bool.xor(n, m), Bool.xor(f, g))) : Bool}:
  match n f m g:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.xf(m: Bool) -> {Bool.xor(m, False{}) == m : Bool}:
  match m:
    case False{}:
      {==}
    case True{}:
      {==}

def Flag.sg_a(m: Bool, g: Bool) -> {Bool.xor(Bool.xor(m, False{}), g) == Bool.xor(m, g) : Bool}:
  match m g:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Flag.sg_b(m: Bool, g: Bool) -> {Bool.xor(m, Bool.not(g)) == Bool.not(Bool.xor(m, g)) : Bool}:
  match m g:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Flag.as_t1n(a: Bool, b: Bool, c: Bool, d: Bool) -> {Bool.xor(Bool.xor(a, b), Bool.xor(c, d)) == Bool.xor(Bool.xor(a, c), Bool.xor(b, d)) : Bool}:
  match a b c d:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.as_fxn(a: Bool, b: Bool) -> {Bool.xor(a, Bool.not(b)) == Bool.not(Bool.xor(a, b)) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Flag.as_fnx(a: Bool, b: Bool) -> {Bool.xor(Bool.not(a), b) == Bool.not(Bool.xor(a, b)) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Flag.as_fnn(a: Bool, b: Bool) -> {Bool.xor(Bool.not(a), Bool.not(b)) == Bool.xor(a, b) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Flag.as_t2n(n1: Bool, f1: Bool, n2: Bool) -> {Bool.xor(Bool.xor(n1, f1), n2) == Bool.xor(Bool.xor(n1, n2), f1) : Bool}:
  match n1 f1 n2:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def Flag.as_t3p(n1: Bool, n2: Bool, f1: Bool, f2: Bool) -> {Bool.xor(n1, Bool.xor(n2, f2)) == Bool.xor(Bool.xor(Bool.xor(n1, n2), Bool.xor(f1, f2)), f1) : Bool}:
  match n1 n2 f1 f2:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.as_t3n(n1: Bool, n2: Bool, f1: Bool, f2: Bool) -> {Bool.xor(n1, Bool.not(Bool.xor(n2, f2))) == Bool.xor(Bool.xor(Bool.xor(n1, n2), Bool.xor(f1, f2)), Bool.not(f1)) : Bool}:
  match n1 n2 f1 f2:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.as_u1n(n1: Bool, f1: Bool, n2: Bool, f2: Bool) -> {Bool.xor(Bool.not(Bool.xor(n1, f1)), Bool.xor(n2, f2)) == Bool.not(Bool.xor(Bool.xor(n1, n2), Bool.xor(f1, f2))) : Bool}:
  match n1 f1 n2 f2:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.as_u2n(n1: Bool, f1: Bool, n2: Bool) -> {Bool.xor(Bool.not(Bool.xor(n1, f1)), n2) == Bool.xor(Bool.xor(n1, n2), Bool.not(f1)) : Bool}:
  match n1 f1 n2:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def Flag.as_u3n(n1: Bool, n2: Bool, f1: Bool, f2: Bool) -> {Bool.xor(n1, Bool.not(Bool.xor(n2, f2))) == Bool.xor(Bool.not(Bool.xor(Bool.xor(n1, n2), Bool.xor(f1, f2))), f1) : Bool}:
  match n1 n2 f1 f2:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.lr_n(n: Bool, f: Bool, m: Bool, g: Bool) -> {Bool.xor(Bool.xor(n, f), Bool.xor(m, g)) == Bool.xor(Bool.xor(n, m), Bool.xor(f, g)) : Bool}:
  match n f m g:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.lr_f(f: Bool, g: Bool) -> {Bool.xor(Bool.not(f), Bool.not(g)) == Bool.xor(Bool.xor(f, g), False{}) : Bool}:
  match f g:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Flag.lr_xf(a: Bool, b: Bool) -> {Bool.xor(Bool.xor(a, b), False{}) == Bool.xor(a, b) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Flag.rl_1(n: Bool, f: Bool, m: Bool, g: Bool, P: Bool) -> {Bool.xor(Bool.xor(n, m), Bool.and(P, Bool.xor(Bool.not(f), Bool.not(g)))) == Bool.xor(Bool.xor(Bool.xor(n, m), Bool.and(Bool.not(P), Bool.xor(f, g))), Bool.xor(f, g)) : Bool}:
  match n f m g P:
    case False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

def Flag.rl_2(n: Bool, f: Bool, m: Bool, g: Bool, P: Bool) -> {Bool.xor(Bool.xor(Bool.xor(n, f), Bool.xor(m, g)), Bool.and(P, Bool.xor(f, g))) == Bool.xor(Bool.xor(n, m), Bool.and(Bool.not(P), Bool.xor(f, g))) : Bool}:
  match n f m g P:
    case False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

def Flag.rl_0(n: Bool, m: Bool, b: Bool) -> {Bool.xor(Bool.xor(n, m), Bool.and(False{}, b)) == Bool.xor(n, m) : Bool}:
  match n m b:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def Flag.and_f(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Flag.iv_t(k: Bool) -> {Bool.xor(k, True{}) == Bool.not(k) : Bool}:
  match k:
    case False{}:
      {==}
    case True{}:
      {==}

def Flag.iv_tt(k: Bool) -> {Bool.xor(Bool.xor(k, True{}), True{}) == k : Bool}:
  match k:
    case False{}:
      {==}
    case True{}:
      {==}

def Flag.iv_f(f: Bool) -> {Bool.xor(f, False{}) == f : Bool}:
  match f:
    case False{}:
      {==}
    case True{}:
      {==}

def Flag.iv_c(m: Bool, n: Bool) -> {Bool.xor(m, n) == Bool.xor(n, m) : Bool}:
  match m n:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Flag.rv_A0(m: Bool, a: Bool, n: Bool, f: Bool) -> {Bool.xor(False{}, Bool.xor(a, True{})) == Bool.xor(True{}, a) : Bool}:
  match m a n f:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.rv_A1(m: Bool, a: Bool, n: Bool, f: Bool) -> {Bool.xor(Bool.xor(Bool.xor(Bool.xor(m, a), Bool.xor(n, f)), False{}), False{}) == Bool.xor(Bool.xor(Bool.xor(m, n), Bool.xor(a, f)), False{}) : Bool}:
  match m a n f:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.rv_A2(m: Bool, a: Bool, n: Bool, f: Bool) -> {Bool.xor(Bool.xor(a, True{}), f) == Bool.xor(Bool.xor(a, f), True{}) : Bool}:
  match m a n f:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.rv_B1(m: Bool, a: Bool, n: Bool, f: Bool) -> {Bool.xor(Bool.xor(Bool.xor(Bool.xor(m, a), n), False{}), False{}) == Bool.xor(Bool.xor(Bool.xor(Bool.xor(m, n), False{}), False{}), a) : Bool}:
  match m a n f:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.rv_B2(m: Bool, a: Bool, n: Bool, f: Bool) -> {Bool.xor(Bool.xor(a, True{}), Bool.not(f)) == Bool.xor(a, f) : Bool}:
  match m a n f:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.rv_CQP0(m: Bool, a: Bool, n: Bool, f: Bool) -> {Bool.xor(False{}, a) == Bool.xor(True{}, Bool.xor(a, True{})) : Bool}:
  match m a n f:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.rv_CQP1(m: Bool, a: Bool, n: Bool, f: Bool) -> {Bool.xor(Bool.xor(Bool.xor(m, Bool.xor(n, f)), False{}), False{}) == Bool.xor(Bool.xor(Bool.xor(Bool.xor(m, n), False{}), Bool.xor(a, f)), a) : Bool}:
  match m a n f:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.rv_CQP2(m: Bool, a: Bool, n: Bool, f: Bool) -> {Bool.xor(a, Bool.not(f)) == Bool.xor(Bool.xor(a, f), True{}) : Bool}:
  match m a n f:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.rv_CQN0(m: Bool, a: Bool, n: Bool, f: Bool) -> {Bool.xor(False{}, a) == Bool.xor(True{}, Bool.xor(a, True{})) : Bool}:
  match m a n f:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.rv_CQN1(m: Bool, a: Bool, n: Bool, f: Bool) -> {Bool.xor(Bool.xor(Bool.xor(m, Bool.not(Bool.xor(n, f))), False{}), False{}) == Bool.xor(Bool.xor(Bool.not(Bool.xor(Bool.xor(m, n), False{})), Bool.xor(a, f)), a) : Bool}:
  match m a n f:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def Flag.rv_CQN2(m: Bool, a: Bool, n: Bool, f: Bool) -> {Bool.xor(a, Bool.not(f)) == Bool.xor(Bool.xor(a, f), True{}) : Bool}:
  match m a n f:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}
