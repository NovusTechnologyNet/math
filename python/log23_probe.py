"""Does log 23 have a binary BBP-type formula?  A theory-free numerical search.

    python log23_probe.py [P ...]        (needs python-flint and mpmath; default P = 88)

Bailey's compendium of BBP-type formulas lists the primes p for which log p has a known
binary BBP formula and says it is unknown whether all primes have one; 23 is the first
prime missing, and Chamberland (J. Integer Seq. 6, 2003) says the case of log 23 is open.

In our class F, a formula is a rational pattern rho of period P with
    sum over k >= 1 of rho(k) 2^(-floor(k/2)) / k  =  the constant.
With S_j = sum over k = j (mod P) of 2^(-floor(k/2))/k, that is a rational relation between
the constant and S_1, ..., S_P.  This script finds, by lattice reduction (LLL), every
integer relation with small coefficients among

    log 2, log 3, log 5, log 23, log 89, log 683,  S_1, ..., S_P

and reports which rational combinations of the six logarithms are values of period-P
series.  Nothing about roots of unity, Baker's theorem or prime ideals is used.

Expected from the theory (2^11 - 1 = 23 * 89, 2^11 + 1 = 3 * 683): log 2, log 3, log 5,
log 683 and log 23 + log 89 are values (for P divisible by 88), but log 23 alone is not.
A negative result here is evidence only: it excludes formulas of this period with small
coefficients, nothing more.
"""
import sys
import time
from fractions import Fraction

from flint import fmpz_mat
from mpmath import mp, mpf, log, floor

NAMES = ["log 2", "log 3", "log 5", "log 23", "log 89", "log 683"]
ARGS = [2, 3, 5, 23, 89, 683]


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
    m = len(ARGS)
    Wc = bits_per * (P + m) + 256                # precision used in the lattice
    W = Wc + 256                                 # precision used for the re-check
    mp.prec = W + 64
    S = class_sums(P, W)
    T = [int(floor(log(mpf(a)) * mpf(2) ** W)) for a in ARGS]
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
    # which combinations of the logarithms are values of period-P series
    proj = [r[:m] for r in rels if any(r[:m])]
    basis, piv = rank_and_span(proj) if proj else ([], [])
    print("  zero relations among the S_j alone: %d" % (small - len(basis)))
    print("  combinations of the logarithms that are values of a period-%d series "
          "(dimension %d of %d):" % (P, len(basis), m))
    for b in basis:
        print("     " + " ".join("%+s %s" % (c, nm) for c, nm in zip(b, NAMES) if c != 0))
    e23 = [Fraction(int(i == 3)) for i in range(m)]
    red23 = list(e23)
    for b, pc in zip(basis, piv):
        if red23[pc] != 0:
            f = red23[pc]
            red23 = [a - f * x for a, x in zip(red23, b)]
    print("  log 23 alone is %sa value of a period-%d series with small coefficients"
          % ("" if not any(red23) else "NOT ", P))
    return basis


if __name__ == "__main__":
    for P in [int(a) for a in sys.argv[1:]] or [88]:
        probe(P)
