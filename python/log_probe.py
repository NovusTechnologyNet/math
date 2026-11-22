"""Which products of given primes have a logarithm that is a value of a period-P series?

    python log_probe.py P p1 p2 ...        (needs python-flint and mpmath)

A theory-free numerical search, as in log23_probe.py, for any primes.  With
S_j = sum over k = j (mod P) of 2^(-floor(k/2))/k, lattice reduction (LLL) finds every integer
relation with small coefficients among log p1, log p2, ..., S_1, ..., S_P, and the script
reports which rational combinations of the logarithms are values of period-P series.
A negative result is evidence only: it excludes formulas of this period with small
coefficients.
"""
import sys
import time
from fractions import Fraction

from flint import fmpz_mat
from mpmath import mp, mpf, log, floor

from log23_probe import class_sums, rank_and_span


def probe(P, primes, bits_per=28):
    names = ["log %d" % p for p in primes]
    m = len(primes)
    Wc = bits_per * (P + m) + 256
    W = Wc + 256
    mp.prec = W + 64
    S = class_sums(P, W)
    T = [int(floor(log(mpf(a)) * mpf(2) ** W)) for a in primes]
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
        if resid < (sum(abs(c) for c in coef) + 1) << 80:
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
    print("  combinations of the logarithms that are values of a period-%d series "
          "(dimension %d of %d):" % (P, len(basis), m))
    for b in basis:
        print("     " + "  ".join("%s %s" % (c, nm) for c, nm in zip(b, names) if c != 0))
    for i, p in enumerate(primes):
        target = [Fraction(int(j == i)) for j in range(m)]
        for b, pc in zip(basis, piv):
            if target[pc] != 0:
                f = target[pc]
                target = [a - f * x for a, x in zip(target, b)]
        print("  log %d alone: %s" % (p, "a value" if not any(target) else "NOT a value"))
    return basis


if __name__ == "__main__":
    probe(int(sys.argv[1]), [int(a) for a in sys.argv[2:]])
