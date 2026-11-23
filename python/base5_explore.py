"""Base 5: exploration of the series  S(rho) = sum_{k>=1} rho(k) 5^(-floor(k/2)) / k.

    python base5_explore.py primes [NMAX]      good primes for sqrt(5) - r   (mpmath, sympy)
    python base5_explore.py relations N [B]    relations among the Log(1 - r/sqrt(B)), r^N = 1
                                               (python-flint, mpmath; B defaults to 5)
    python base5_explore.py logs P p1 p2 ...   which combinations of log 5, log p1, ... are
                                               values of a series of period P (python-flint)

Nothing here is a proof. The three commands test, by computer, what the method of the note
(Parts III and V) predicts for base 5, with t = sqrt(5):

  primes     For a root of unity r of order n, the norm of t - r down to Q is computed, and
             the program looks for an odd prime p, not 5 and not dividing n, that divides it
             (a "good prime": a prime ideal above p then contains t - r and no t - r' for
             another root r' of the same or a smaller order). Prediction: every r other than
             1 and -1 has one.
  relations  Lattice reduction looks for integer vectors (z_r; z_0) with
             sum z_r Log(1 - r/t) + z_0 * 2 pi i = 0. Prediction for base 5: none. (For base
             3 the same command must find a lattice of rank 3: a test of the program.)
  logs       The theory-free probe of base3_probe.py, in base 5, on logarithms of primes
             together with log 5.
"""
import sys
import time
from math import gcd

from mpmath import mp, mpf, mpc, pi, sqrt, log, floor, exp


# ---------------------------------------------------------------------------------------
# 1. Good primes
# ---------------------------------------------------------------------------------------

def legendre5(c):
    c %= 5
    return 0 if c == 0 else (1 if c in (1, 4) else -1)


def norms_for_order(n):
    """The absolute norms of sqrt(5) - r for r of order n: a list of (label, integer).

    If 5 does not divide n there is one class; if 5 divides n there are two (the two
    Aurifeuillian-type halves), according to the quadratic character of the exponent."""
    units = [c for c in range(1, n + 1) if gcd(c, n) == 1]
    mp.dps = int(len(units) * 0.36 * 2) + 60
    t = sqrt(mpf(5))
    zeta = [exp(2j * pi * c / n) for c in units]
    out = []
    if n % 5:
        prod = mpc(1)
        for z in zeta:
            prod *= (t - z) * (-t - z)
        out.append(("all", prod))
    else:
        for eps in (1, -1):
            prod = mpc(1)
            for c, z in zip(units, zeta):
                prod *= (eps * legendre5(c) * t - z)
            out.append(("+" if eps == 1 else "-", prod))
    res = []
    for label, prod in out:
        val = int(mp.nint(prod.real))
        assert abs(prod.imag) < mpf(10) ** (-20) and abs(prod.real - val) < mpf(10) ** (-20), n
        res.append((label, abs(val)))
    return res


def strip(N, n):
    """Remove from N the prime 2 and the prime factors of n; return the cofactor."""
    from sympy import primefactors
    for p in set(primefactors(n)) | {2}:
        while N % p == 0:
            N //= p
    return N


def cmd_primes(nmax):
    from sympy import factorint
    bad = []
    print("order n : class : norm of sqrt(5) - r (factored when small) : good prime?")
    for n in range(1, nmax + 1):
        for label, N in norms_for_order(n):
            cof = strip(N, n)
            ok = cof > 1
            if not ok:
                bad.append((n, label, N))
            if n <= 30 or not ok:
                fac = factorint(N) if N < 10 ** 40 else None
                shown = (" * ".join("%d^%d" % (p, e) if e > 1 else str(p)
                                    for p, e in sorted(fac.items())) if fac else str(N)[:30] + "...")
                print("  n = %3d  %-3s  %s   %s" % (n, label, shown if N > 1 else "1",
                                                    "yes" if ok else "NO"))
    print()
    print("orders up to %d with a class that has no good prime: %s"
          % (nmax, ", ".join("%d(%s)" % (n, lab) for n, lab, _ in bad) or "none"))


# ---------------------------------------------------------------------------------------
# 2. Relations among the logarithms
# ---------------------------------------------------------------------------------------

def cmd_relations(N, base):
    from flint import fmpz_mat
    bits_per = 30
    Wc = bits_per * (N + 1) + 300
    extra = 400                 # the values are known to Wc + extra bits; the lattice sees Wc
    mp.prec = Wc + extra + 64
    t = sqrt(mpf(base))
    vals = []
    for a in range(N):
        w = log(1 - exp(2j * pi * a / N) / t)
        vals.append((w.real, w.imag))
    vals.append((mpf(0), 2 * pi))
    scale = mpf(2) ** Wc
    n = len(vals)
    rows = []
    for i, (re, im) in enumerate(vals):
        row = [0] * (n + 2)
        row[i] = 1
        row[n] = int(floor(re * scale))
        row[n + 1] = int(floor(im * scale))
        rows.append(row)
    t0 = time.time()
    red = fmpz_mat(rows).lll()
    rels = []
    norms = []
    for i in range(n):
        row = [int(red[i, j]) for j in range(n + 2)]
        norms.append(sum(c * c for c in row))
        coef = row[:n]
        re = sum(c * v[0] for c, v in zip(coef, vals))
        im = sum(c * v[1] for c, v in zip(coef, vals))
        # a true relation vanishes to the full precision; a vector that is merely short for
        # the lattice has a residue of about 2^(-Wc) times its coefficients
        tol = (sum(abs(c) for c in coef) + 1) * mpf(2) ** (-(Wc + extra - 100))
        if abs(re) < tol and abs(im) < tol:
            rels.append(coef)
    norms.sort()
    print("base %d, N = %d: %d logarithms and 2 pi i, %d bits; LLL %.0f s"
          % (base, N, N, Wc, time.time() - t0))
    print("  relations found: %d   (smallest squared length of a non-relation: about 2^%d)"
          % (len(rels), norms[len(rels)].bit_length() - 1 if len(rels) < n else 0))
    for r in rels:
        supp = ["%+d*L(%d)" % (c, a) for a, c in enumerate(r[:N]) if c]
        print("     " + " ".join(supp) + ("  %+d*(2 pi i)" % r[N] if r[N] else ""))
    return rels


# ---------------------------------------------------------------------------------------
# 3. Logarithms
# ---------------------------------------------------------------------------------------

def cmd_logs(P, primes):
    import base3_probe
    base3_probe.LOG_PRIMES = [5] + [p for p in primes if p != 5]
    base3_probe.probe(P, 5)


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "primes":
        cmd_primes(int(sys.argv[2]) if len(sys.argv) > 2 else 120)
    elif cmd == "relations":
        cmd_relations(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 5)
    elif cmd == "logs":
        cmd_logs(int(sys.argv[2]), [int(a) for a in sys.argv[3:]])
    else:
        print(__doc__)
