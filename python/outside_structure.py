"""Structure of the families F_n: the multiplicative relations among 1 - r*x.

Run:  python outside_structure.py [n ...]     (default: 2 3 4 5 6 8 12; needs python-flint)

x = 2^(-1/n).  For the candidate roots of unity r (see outside_family_findings.md) this
finds, by lattice reduction on the complex logarithms, every relation with small
exponents

    prod (1 - r x)^(e_r) = root of unity,

re-checks each at higher precision, and reports
  * how many independent relations there are,
  * how many are constant on the cosets r * mu_n1 (n1 = n/2 for even n, n for odd n):
    those are exactly the relations of F_2 (resp. F_1) written in the variable x^n1,
  * how many are new, and whether the new ones carry an angle (a multiple of pi).

n = 2 is the control: it must return the 13 relations of full_class_theorem.py.
"""
import sys
import time
from fractions import Fraction
from math import gcd

from flint import fmpz_mat
from mpmath import mp, mpf, pi, log, exp

R0_F2 = [0, 60, 30, 90, 20, 100, 15, 45, 75, 105, 12, 36, 84, 108, 10, 50, 18, 42, 66, 114, 5, 25, 65, 85]


def lcm(a, b):
    return a * b // gcd(a, b)


def candidate_roots(n):
    """Angles f (r = exp(2 pi i f)) of the roots that can occur in a relation."""
    out = set()
    if n % 2:
        for g in (Fraction(0), Fraction(1, 2), Fraction(1, 6), Fraction(5, 6)):      # r^n in {1, -1, zeta_6^+-1}
            for m in range(n):
                out.add(((g + m) / n) % 1)
    else:
        n1 = n // 2
        for j in R0_F2:                                                              # zeta_8 * r^n1 in R0(F_2)
            for m in range(n1):
                out.add(((Fraction(j, 120) - Fraction(1, 8) + m) / n1) % 1)
    return sorted(out)


def rank_of(vectors):
    rows = [[Fraction(x) for x in v] for v in vectors]
    r = 0
    ncols = len(rows[0]) if rows else 0
    for c in range(ncols):
        p = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        for i in range(r + 1, len(rows)):
            if rows[i][c] != 0:
                f = rows[i][c] / rows[r][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


def analyse(n, bits_per=30):
    roots = candidate_roots(n)
    P = lcm(8, n)
    for f in roots:
        P = lcm(P, f.denominator)
    N = len(roots)
    Wc = bits_per * (N + 2) + 256
    W = Wc + 256
    mp.prec = W + 64
    x = mpf(2) ** (-mpf(1) / n)
    logs = [log(1 - exp(2j * pi * mpf(f.numerator) / f.denominator) * x) for f in roots]
    unit = pi / (2 * P)
    def fx(v, bits):
        return int(mp.floor(v * mpf(2) ** bits + mpf(1) / 2))
    re = [fx(l.real, W) for l in logs] + [0]
    im = [fx(l.imag, W) for l in logs] + [fx(unit, W)]
    rows = []
    for i in range(N + 1):
        row = [0] * (N + 3)
        row[i] = 1
        row[N + 1] = re[i] >> (W - Wc)
        row[N + 2] = im[i] >> (W - Wc)
        rows.append(row)
    t0 = time.time()
    red = fmpz_mat(rows).lll()
    rels = []
    norms = []
    for i in range(N + 1):
        row = [int(red[i, j]) for j in range(N + 3)]
        coef = row[:N + 1]
        norms.append(sum(c * c for c in row))
        size = (sum(abs(c) for c in coef) + 1) << 80
        if abs(sum(c * v for c, v in zip(coef, re))) < size and abs(sum(c * v for c, v in zip(coef, im))) < size:
            rels.append(coef)
    norms.sort()
    nxt = norms[len(rels)].bit_length() - 1 if len(rels) < len(norms) else 0
    n1 = n // 2 if n % 2 == 0 else n
    index = {f: i for i, f in enumerate(roots)}
    avg = []
    for e in rels:
        v = [Fraction(0)] * N
        for f, i in index.items():
            for m in range(n1):
                v[i] += Fraction(e[index[(f + Fraction(m, n1)) % 1]], n1)
        avg.append(v)
    inv = rank_of(avg) if avg else 0
    total = rank_of([e[:N] for e in rels]) if rels else 0
    carrying = sum(1 for e in rels if e[N] != 0)
    print("n = %2d: %3d candidate roots, period %d; %d-bit logarithms; LLL %.0f s"
          % (n, N, P, Wc, time.time() - t0))
    print("   independent relations: %d   (largest squared length %d; smallest non-relation about 2^%d)"
          % (total, norms[len(rels) - 1] if rels else 0, nxt))
    print("   constant on cosets r*mu_%d (= the relations of F_%d): %d;   new: %d;   basis relations with an angle: %d"
          % (n1, 2 if n % 2 == 0 else 1, inv, total - inv, carrying))
    return roots, rels


if __name__ == "__main__":
    for arg in (sys.argv[1:] or ["2", "3", "4", "5", "6", "8", "12"]):
        roots, rels = analyse(int(arg))
        if int(arg) in (3, 5) and rels:
            for e in rels:
                print("      " + " ".join("%+d[%s]" % (c, f) for c, f in zip(e, roots) if c)
                      + "   angle %s*pi" % Fraction(-e[-1], 1))
