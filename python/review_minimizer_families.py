"""Referee check: are the 7/24-optimal patterns isolated (22 formulas) or do they form families?

Run with PYTHONPATH set to numpy + python-flint:  python review_minimizer_families.py <winners.pkl>
(<winners.pkl> = the list of 22 winner patterns written by cheaper_fast.py).
For each group of winners, the generic member of their span is tested exactly.
"""
import pickle, sys, itertools
from fractions import Fraction
from math import gcd
from flint import fmpq_mat, fmpq
from mpmath import mp, mpf, pi

N = 120
U = [c for c in range(1, N) if gcd(c, N) == 1]


def cost(p):
    t = 0
    for c in U:
        s = 1
        while p[s * c % N] == 0:
            s += 1
        t += Fraction(1, s)
    return t / len(U)


def val(p):
    mp.dps = 50
    tot, k = mpf(0), 1
    while k // 2 <= mp.prec + 40:
        r = p[k % N]
        if r:
            tot += mpf(r.numerator) / r.denominator / (mpf(k) * mpf(2) ** (k // 2))
        k += 1
    return tot / pi


def rank(rows):
    return fmpq_mat([[fmpq(x.numerator, x.denominator) for x in r] for r in rows]).rank()


W = pickle.load(open(sys.argv[1], "rb"))
Z = [frozenset(k for k in range(N) if p[k] == 0) for p in W]
groups = []
for i in range(len(W)):
    for g in groups:
        if cost([0 if k in (Z[i] & Z[g[0]]) else 1 for k in range(N)]) == Fraction(7, 24):
            g.append(i)
            break
    else:
        groups.append([i])
print("groups of winners whose pairwise generic combinations keep cost 7/24:", groups)
for g in groups:
    pats = [W[i] for i in g]
    common = frozenset.intersection(*[Z[i] for i in g])
    print("group of %d: span dimension %d; common zero set %d entries; cost of the common zero set %s"
          % (len(g), rank(pats), len(common), cost([0 if k in common else 1 for k in range(N)])))
    # an explicit non-vertex optimal formula: v_a + 2 v_b + 5 v_c (value pi/4 * 8), rescaled
    a, b, c = pats[0], pats[1], pats[2]
    mix = [x + 2 * y + 5 * z for x, y, z in zip(a, b, c)]
    mix = [x / 8 for x in mix]
    print("   example (v1 + 2 v2 + 5 v3)/8: value/pi = %s, mean(1/s) = %s, non-zero entries %d, zero set size %d"
          % (mp.nstr(val(mix), 20), cost(mix), sum(1 for x in mix if x), sum(1 for x in mix if x == 0)))
