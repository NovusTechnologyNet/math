"""Base 3: which constants are values of a series  sum rho(k) 3^(-floor(k/2)) / k ?

    python base3_probe.py P [BASE]            (needs python-flint and mpmath; BASE defaults to 3)

A theory-free numerical search, the base-b version of log_probe.py.  With
S_j = sum over k = j (mod P) of b^(-floor(k/2))/k, lattice reduction (LLL) finds every integer
relation with small coefficients among a list of target constants and S_1, ..., S_P.  The
script reports

  * the number of relations among the S_j alone (the "zero relations" of period P),
  * which rational combinations of the targets are values of a period-P series,
  * for each target alone, whether it is a value.

A negative result is evidence only: it excludes formulas of this period with small
coefficients.  Nothing here is a proof.
"""
import sys
import time
from fractions import Fraction

from flint import fmpz_mat
from mpmath import mp, mpf, log, floor, pi, sqrt, atan

from log23_probe import rank_and_span


def class_sums(P, W, b):
    """S_j * 2^W as integers, j = 1..P (index j-1; j = P is the class k = 0 mod P)."""
    acc = [0] * P
    k = 1
    top = 1 << (W + 72)
    bp = 1                       # b^(k // 2)
    while bp <= top:
        acc[(k - 1) % P] += (1 << (W + 64)) // (bp * k)
        k += 1
        if k % 2 == 0:
            bp *= b
    return [a >> 64 for a in acc]


LOG_PRIMES = None                # set to a list of primes to probe only their logarithms


def targets(b):
    """(name, value) pairs, evaluated at the current mp.prec."""
    if LOG_PRIMES is not None:
        return [("log %d" % p, log(mpf(p))) for p in LOG_PRIMES]
    r = sqrt(mpf(b))
    out = [("pi", pi), ("pi*sqrt(%d)" % b, pi * r)]
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43):
        out.append(("log %d" % p, log(mpf(p))))
    if b == 3:
        out.append(("sqrt(3)*log(2+sqrt(3))", r * log(2 + r)))
        out.append(("sqrt(3)*atan(sqrt(3)/5)", r * atan(r / 5)))
        out.append(("sqrt(3)*atan(sqrt(3)/2)", r * atan(r / 2)))
        out.append(("atan(1/2)", atan(mpf(1) / 2)))
    return out


def probe(P, b=3, bits_per=28, names_only=None):
    mp.prec = 64
    tl = targets(b)
    if names_only is not None:
        tl = [x for x in tl if x[0] in names_only]
    m = len(tl)
    Wc = bits_per * (P + m) + 256
    W = Wc + 256
    mp.prec = W + 64
    tl = [x for x in targets(b) if names_only is None or x[0] in names_only]
    names = [x[0] for x in tl]
    S = class_sums(P, W, b)
    T = [int(floor(x[1] * mpf(2) ** W)) for x in tl]
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
    print("base %d, P = %d: %d numbers, %d bits; LLL %.0f s" % (b, P, n, Wc, time.time() - t0))
    print("  relations found: %d (largest squared length %s; smallest non-relation %s)"
          % (small, norms[small - 1] if small else 0,
             "about 2^%d" % (gap_hi.bit_length() - 1) if gap_hi else "-"))
    proj = [r[:m] for r in rels if any(r[:m])]
    basis, piv = rank_and_span(proj) if proj else ([], [])
    zero = small - len(basis)
    print("  zero relations among the S_j: %d of %d, so the values span dimension %d"
          % (zero, P, P - zero))
    print("  combinations of the targets that are values (dimension %d of %d):"
          % (len(basis), m))
    for bvec in basis:
        print("     " + "  ".join("%s*[%s]" % (c, nm) for c, nm in zip(bvec, names) if c != 0))
    alone = {}
    for i, nm in enumerate(names):
        target = [Fraction(int(j == i)) for j in range(m)]
        for bvec, pc in zip(basis, piv):
            if target[pc] != 0:
                f = target[pc]
                target = [a - f * x for a, x in zip(target, bvec)]
        alone[nm] = not any(target)
    print("  values:     " + ", ".join(nm for nm in names if alone[nm]))
    print("  not values: " + ", ".join(nm for nm in names if not alone[nm]))
    return rels, names, zero


if __name__ == "__main__":
    # python base3_probe.py P            the standard targets, base 3
    # python base3_probe.py P logs p1 p2 ...   only the logarithms of the given primes
    P = int(sys.argv[1])
    if len(sys.argv) > 2 and sys.argv[2] == "logs":
        LOG_PRIMES = [int(a) for a in sys.argv[3:]]
        probe(P, 3)
    else:
        probe(P, int(sys.argv[2]) if len(sys.argv) > 2 else 3)
