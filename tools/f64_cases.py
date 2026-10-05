#!/usr/bin/env python3
"""Expected IEEE binary64 results for tests/big_f64.bend.

CPython floats are hardware doubles, so a*b and a+b are correctly rounded
binary64. Prints the cases() definition the test lists: a third random
pairs, a third with tiny products (subnormal or zero), a third that cancel.
"""
import math
import random
import struct
from fractions import Fraction

random.seed(5)


def bits(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def mk(m, e, neg):
    x = float(Fraction(m) * Fraction(2) ** e)
    return -x if neg else x


def rnd_double(lo=-560, hi=500):
    w = random.randint(1, 53)
    return mk(random.randrange(1, 2 ** w), random.randint(lo, hi), random.random() < 0.5)


cases = []
while len(cases) < 300:
    k = len(cases) % 3
    a = rnd_double()
    if k == 0:
        b = rnd_double()
    elif k == 1:
        a = rnd_double(-600, -480)
        b = rnd_double(-600, -480)
    else:
        b = -a * (1 + random.uniform(-1e-9, 1e-9))
    p, s = a * b, a + b
    if math.isinf(p) or math.isinf(s) or math.isnan(p) or a == 0 or b == 0:
        continue
    cases.append((bits(a), bits(b), bits(p), bits(s)))

rows = ["C{" + ", ".join(f"{v >> 32}n, {v & 0xffffffff}n" for v in c) + "}" for c in cases]
print("def cases() -> List<&2, C>:")
print("  (" + " <>\n   ".join(rows) + " <>\n   Nil{})")
