#!/usr/bin/env python3
"""Expected b-posit32 results for tests/bposit.bend, by an independent route.

The reference rounds the way the posit standard defines it: write the exact
value's bit string (regime, exponent, fraction) and round that string to
n - 1 bits, to nearest, ties to the even pattern; saturate at maxpos and
minpos. src/posit.bend instead rounds to nearest at the scale's precision.
The test checks that the two agree. Format (Jonnalagadda et al. 2026): n =
32, es = 5, regime at most rs = 6 bits.
"""
import random
from fractions import Fraction

N, ES, RS = 32, 5, 6
G = 1 << ES
BIAS = RS * G
MAXP = (1 << (N - 1)) - 1


def decode(p):
    if p == 0:
        return Fraction(0)
    neg = p >> (N - 1)
    q = (1 << N) - p if neg else p
    w = N - 1
    bits = [(q >> (w - 1 - i)) & 1 for i in range(w)]
    b, k = bits[0], 0
    while k < RS and bits[k] == b:
        k += 1
    rl = k + 1 if k < RS else RS
    r = k - 1 if b == 1 else -k
    rest = bits[rl:]
    eb = rest[:ES] + [0] * (ES - len(rest[:ES]))
    e = int(''.join(map(str, eb)), 2)
    fb = rest[ES:]
    f = Fraction(int(''.join(map(str, fb)) or '0', 2), 1 << len(fb))
    v = Fraction(2) ** (r * G + e) * (1 + f)
    return -v if neg else v


def encode(x):
    if x == 0:
        return 0
    neg, a = x < 0, abs(x)
    t = a.numerator.bit_length() - a.denominator.bit_length()
    if Fraction(2) ** t > a:
        t -= 1
    if t >= BIAS:
        q = MAXP
    elif t < -BIAS:
        q = 1
    else:
        r = t // G
        e = t - r * G
        reg = '1' * (r + 1) + ('0' if r + 1 < RS else '') if r >= 0 else '0' * (-r) + ('1' if -r < RS else '')
        s = reg + format(e, '0%db' % ES)
        frac = a / Fraction(2) ** t - 1
        while len(s) < N + 2:
            frac *= 2
            bit = int(frac >= 1)
            s += str(bit)
            frac -= bit
        q0 = int(s[:N - 1], 2)
        guard = s[N - 1] == '1'
        sticky = frac != 0 or '1' in s[N:]
        q = q0 + (1 if guard and (sticky or q0 & 1) else 0)
        q = min(q, MAXP)
        q = max(q, 1)
    return (1 << N) - q if neg else q


def rnd_pattern(near=False, edge=False):
    while True:
        if edge:
            # the longest regimes, 000000 or 111111: |x| near 2^-192 or 2^192
            p = (random.choice([0, 0b111111]) << 25) | random.getrandbits(25)
            if random.random() < 0.5:
                p = (1 << N) - p
        elif near:
            # regime of 2 bits: |x| in [2^-32, 2^32)
            p = (random.choice([0b01, 0b10]) << 29) | random.getrandbits(29)
            if random.random() < 0.5:
                p = (1 << N) - p
        else:
            p = random.getrandbits(N)
        if p not in (0, 1 << (N - 1)):
            return p


random.seed(7)
for _ in range(1000):
    p = rnd_pattern()
    assert encode(decode(p)) == p
pairs = ([(rnd_pattern(), rnd_pattern()) for _ in range(150)] + [(rnd_pattern(True), rnd_pattern(True)) for _ in range(150)]
         + [(rnd_pattern(edge=True), rnd_pattern(edge=True)) for _ in range(50)] + [(rnd_pattern(edge=True), rnd_pattern(True)) for _ in range(50)])
rows = []
for a, b in pairs:
    x, y = decode(a), decode(b)
    rows.append((a, b, encode(x * y), encode(x + y)))
dots = []
for _ in range(40):
    xs = [rnd_pattern(True) for _ in range(8)]
    ys = [rnd_pattern(True) for _ in range(8)]
    dots.append((xs, ys, encode(sum(decode(u) * decode(v) for u, v in zip(xs, ys)))))
nmax = sum(1 for r in rows if r[2] in (MAXP, (1 << N) - MAXP))
nmin = sum(1 for r in rows if r[2] in (1, (1 << N) - 1))
print("# products saturating at maxpos: %d, at minpos: %d" % (nmax, nmin))
print("def cases() -> List<&2, C>:")
print("  (" + " <>\n   ".join("C{%dn, %dn, %dn, %dn}" % r for r in rows) + " <>\n   Nil{})")
print()
print("def dots() -> List<&2, Q>:")
print("  (" + " <>\n   ".join("Q{%s, %s, %dn}" % ("(" + " <> ".join("%dn" % u for u in xs) + " <> Nil{})", "(" + " <> ".join("%dn" % v for v in ys) + " <> Nil{})", e) for xs, ys, e in dots) + " <>\n   Nil{})")
