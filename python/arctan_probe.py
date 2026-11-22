"""Does arctan(2/7) have a binary BBP-type formula?  A theory-free numerical search.

    python arctan_probe.py [P ...]        (needs python-flint and mpmath; default P = 104)

Bailey's compendium of BBP-type formulas says it is not known whether arctan(2/7) possesses
a binary BBP formula; Borwein, Borwein and Galway (2004) name it as the first arctangent for
which they found none.

In our class F, a formula is a rational pattern rho of period P with
    sum over k >= 1 of rho(k) 2^(-floor(k/2)) / k  =  the constant.
With S_j = sum over k = j (mod P) of 2^(-floor(k/2))/k, that is a rational relation between
the constant and S_1, ..., S_P.  This script finds, by lattice reduction (LLL), every
integer relation with small coefficients among

    pi, arctan(1/2), arctan(2/7), arctan(6/11),  S_1, ..., S_P

and reports which rational combinations of the four constants are values of period-P
series.  Nothing about roots of unity, Baker's theorem or prime ideals is used.

Expected from the theory: 7 + 2i has norm 53, and the only place 53 occurs is
Phi_13(1 + i) = -64 + 65 i = i (7 + 2i)(11 + 6i), together with the prime 11 + 6i of norm
157.  So for P divisible by 104: pi and arctan(1/2) are values, arctan(2/7) + arctan(6/11)
is a value up to a multiple of pi, and arctan(2/7) alone is not.
A negative result here is evidence only: it excludes formulas of this period with small
coefficients, nothing more.  The proof is in lean/Pilean/PiFormula/Arctan.lean.
"""
import sys
import time
from fractions import Fraction

from flint import fmpz_mat
from mpmath import mp, mpf, atan, floor, pi

NAMES = ["pi", "arctan(1/2)", "arctan(2/7)", "arctan(6/11)"]


def constants():
    return [+pi, atan(mpf(1) / 2), atan(mpf(2) / 7), atan(mpf(6) / 11)]


def class_sums(P, W):
    """S_j * 2^W as integers, j = 1..P (index j-1; j = P is the class k = 0 mod P)."""
    acc = [0] * P
    k = 1
    while k // 2 <= W + 8:
        acc[(k - 1) % P] += (1 << (W - k // 2 + 64)) // k
        k += 1
    return [a >> 64 for a in acc]


def rank_and_span(rows):
    """Reduced row echelon form of a list of rational vectors."""
    rows = [[Fraction(x) for x in r] for r in rows]
    piv, r = [], 0
    ncols = len(rows[0]) if rows else 0
    for col in range(ncols):
        p = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        inv = 1 / rows[r][col]
        rows[r] = [x * inv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        piv.append(col)
        r += 1
    return rows[:r], piv


def probe(P, bits_per=28):
    m = len(NAMES)
    Wc = bits_per * (P + m) + 256                # precision used in the lattice
    W = Wc + 256                                 # precision used for the re-check
    mp.prec = W + 64
    S = class_sums(P, W)
    T = [int(floor(c * mpf(2) ** W)) for c in constants()]
    vals = T + S
    n = len(vals)
    t0 = time.time()
    rows = []
    for i, v in enumerate(vals):
        row = [0] * (n + 1)
        row[i] = 1
        row[n] = v >> (W - Wc)
        rows.append(row)
    red = fmpz_mat(rows).lll()
    rels, norms = [], []
    for i in range(n):
        row = [int(red[i, j]) for j in range(n + 1)]
        norms.append(sum(c * c for c in row))
        coef = row[:n]
        resid = abs(sum(c * v for c, v in zip(coef, vals)))
        if resid < (sum(abs(c) for c in coef) + 1) << 80:      # a true relation: only noise left
            rels.append(coef)
    norms.sort()
    small = len(rels)
    gap_hi = norms[small] if small < len(norms) else None
    print("P = %d: %d numbers, %d bits; LLL %.0f s" % (P, n, Wc, time.time() - t0))
    print("  relations found: %d (largest squared length %s; smallest non-relation %s)"
          % (small, norms[small - 1] if small else 0,
             "about 2^%d" % (gap_hi.bit_length() - 1) if gap_hi else "-"))
    proj = [r[:m] for r in rels if any(r[:m])]
    basis, piv = rank_and_span(proj) if proj else ([], [])
    print("  zero relations among the S_j alone: %d" % (small - len(basis)))
    print("  combinations of the constants that are values of a period-%d series "
          "(dimension %d of %d):" % (P, len(basis), m))
    for b in basis:
        print("     " + " ".join("%+s %s" % (c, nm) for c, nm in zip(b, NAMES) if c != 0))
    target = [Fraction(int(i == 2)) for i in range(m)]
    for b, pc in zip(basis, piv):
        if target[pc] != 0:
            f = target[pc]
            target = [a - f * x for a, x in zip(target, b)]
    print("  arctan(2/7) alone is %sa value of a period-%d series with small coefficients"
          % ("" if not any(target) else "NOT ", P))
    return basis


if __name__ == "__main__":
    for P in [int(a) for a in sys.argv[1:]] or [104]:
        probe(P)
