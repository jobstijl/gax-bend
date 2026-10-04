# Normed<A>: a versor certified to satisfy v ~v = 1 (gax's Unit<M>; Base
# already names its unit type Unit). Its inverse is its reverse, and normed
# versors compose.
#
# Over F32 the certificate is a documented trust boundary, not a proof:
# F32 arithmetic is axiomatic in Bend (ADR-001 item 7), and only this
# library's constructors (normalized, exp, translation, ...) make them.
# Rounding makes a product of units drift from 1; renormalize now and then.

import Base

type Normed<-A: Data> is Data:
  Normed{v: A}

def Normed.get(-A: Data, u: Normed<A>) -> A:
  match u:
    case Normed{v}:
      v
