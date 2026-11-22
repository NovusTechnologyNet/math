"""Search the FULL class for a formula for pi that is cheaper than Euler's.

Run with the system Python:  python cheaper_formula.py

A series  S = sum_{k>=1} rho(k) * 2^(-floor(k/2)) / k  (rho rational, period 120) puts a
prime p into a denominator first at k = s*p, where s is the least multiplier with
rho(s*p) != 0. Then p is needed up to 2m/s for a window at bit m, so the per-prime
state of the window algorithm is  1.44 * 2 * mean(1/s)  bits per bit of position,
the mean taken over the 32 classes of primes modulo 120.

    BBP 1995:  s = 1 or 2  -> mean 3/4   -> 2.16
    Euler:     s = 3       -> mean 1/3   -> 0.96

Step D builds, exactly, the space of ALL rational patterns whose series is a rational
multiple of pi (using the relations found by full_class_theorem.py), and step E
searches it for the pattern with the smallest mean(1/s).
"""
import sys
import time
from fractions import Fraction
from math import gcd

from mpmath import mp, mpf, mpc, pi, log, exp, matrix

import full_class_theorem as fc

N = fc.N
UNITS = [c for c in range(1, N) if gcd(c, N) == 1]


# ------------------------------------------------------------------ small exact helpers
def frac(x, tol):
    """Rational number with a small denominator equal to the mp number x."""
    a0 = x
    h0, h1, k0, k1 = 0, 1, 1, 0
    for _ in range(60):
        a = int(mp.floor(a0))
        h0, h1 = h1, a * h1 + h0
        k0, k1 = k1, a * k1 + k0
        if abs(x - mpf(h1) / k1) < tol:
            return Fraction(h1, k1)
        a0 = 1 / (a0 - a)
    raise ValueError("not a small rational: %s" % mp.nstr(x, 30))


def rref(rows, ncols):
    """Exact reduced row echelon form over Q. Returns (rows, pivot columns)."""
    rows = [list(r) for r in rows]
    piv, r = [], 0
    for c in range(ncols):
        p = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        inv = 1 / Fraction(rows[r][c])
        rows[r] = [v * inv for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [v - f * u for v, u in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    return rows[:r], piv


def null_basis(rows, ncols):
    red, piv = rref(rows, ncols)
    free = [c for c in range(ncols) if c not in piv]
    out = []
    for f in free:
        v = [Fraction(0)] * ncols
        v[f] = Fraction(1)
        for row, p in zip(red, piv):
            v[p] = -row[f]
        out.append(v)
    return out


# ------------------------------------------------------------------ pattern <-> weights on roots
def u_phase(k):
    """2^(-floor(k/2)) * t^k = t^(k mod 2) * i^(k div 2), as (exponent of zeta, has factor t)."""
    return 30 * ((k // 2) % 4), k % 2


def d_exact(rho, j):
    """d_j = (1/120) sum_k D(k) zeta^(-jk),  D(k) = -2i rho(k) u(k); exact element of Q(zeta_120)."""
    acc = [Fraction(0)] * N
    for k in range(1, N + 1):
        r = rho[k % N]
        if r == 0:
            continue
        e, has_t = u_phase(k)
        base = (30 + e - j * k) % N
        acc[base] += -2 * r
        if has_t:
            acc[(base + 30) % N] += -2 * r
    return [v / N for v in fc.reduce(acc)]


def d_numeric_row(j):
    """Coefficients of rho(1..120) in d_j, as complex mp numbers."""
    row = []
    for k in range(1, N + 1):
        e, has_t = u_phase(k)
        val = -2 * exp(2j * pi * mpf((30 + e - j * k) % N) / N)
        if has_t:
            val *= mpc(1, 1)
        row.append(val / N)
    return row


def series_value(rho):
    total, k = mpf(0), 1
    while k // 2 <= mp.prec + 40:
        r = rho[k % N]
        if r:
            total += mpf(r.numerator) / r.denominator / (mpf(k) * mpf(2) ** (k // 2))
        k += 1
    return total


# ------------------------------------------------------------------ step D
def numeric_rref_nullspace(rows, ncols, eps):
    rows = [list(r) for r in rows]
    piv, r = [], 0
    for c in range(ncols):
        p = max(range(r, len(rows)), key=lambda i: abs(rows[i][c]), default=None)
        if p is None or abs(rows[p][c]) < eps:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        inv = 1 / rows[r][c]
        rows[r] = [v * inv for v in rows[r]]
        for i in range(len(rows)):
            if i != r and abs(rows[i][c]) > eps:
                f = rows[i][c]
                rows[i] = [v - f * u for v, u in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
        if r == len(rows):
            break
    return rows[:r], piv


def step_d(order, rels, lw):
    s = len(rels)
    # place matrix on the 24 roots
    units1 = [a for a in UNITS if a % 4 == 1]
    place = [[mpf(v) for v in row] for row in fc.valuation_rows(order)]
    for a in units1:
        place.append([log(abs(fc.w(j * a % N))) for j in order])
    drow = {j: d_numeric_row(j) for j in range(N)}
    cons = []
    for j in range(N):
        if j not in order:
            cons.append([v.real for v in drow[j]])
            cons.append([v.imag for v in drow[j]])
    for prow in place:
        comb = [sum(prow[i] * drow[j][k] for i, j in enumerate(order)) for k in range(N)]
        cons.append([v.real for v in comb])
        cons.append([v.imag for v in comb])
    eps = mpf(10) ** (-mp.dps // 2)
    red, piv = numeric_rref_nullspace(cons, N, eps)
    free = [c for c in range(N) if c not in piv]
    tol = mpf(10) ** (-mp.dps // 2)
    basis = []
    for f in free:
        v = [Fraction(0)] * N                      # index k mod 120; column c is k = c + 1
        v[(f + 1) % N] = Fraction(1)
        for row, p in zip(red, piv):
            v[(p + 1) % N] = -frac(row[f], tol) if abs(row[f]) > tol else Fraction(0)
        basis.append(v)
    print("D. rational patterns whose series is an algebraic multiple of pi: dimension %d (expected %d)"
          % (len(basis), s))

    # exact check of every basis pattern, and its exact value / pi
    emat = [[Fraction(e.get(j, 0)) for e, _ in rels] for j in order]          # 24 x s
    contents = [c for _, c in rels]
    # left inverse of emat: solve by normal equations, exactly
    ete = [[sum(emat[r][a] * emat[r][b] for r in range(len(order))) for b in range(s)] for a in range(s)]
    aug = [ete[a] + [Fraction(int(a == b)) for b in range(s)] for a in range(s)]
    red2, piv2 = rref(aug, s)
    assert piv2 == list(range(s))
    inv = [row[s:] for row in red2]
    pinv = [[sum(inv[a][b] * emat[r][b] for b in range(s)) for r in range(len(order))] for a in range(s)]
    values = []
    for v in basis:
        dvec = {j: d_exact(v, j) for j in range(N)}
        assert all(not any(dvec[j]) for j in range(N) if j not in order), "weight outside the 24 roots"
        x = [[sum(pinv[a][r] * dvec[j][m] for r, j in enumerate(order)) for m in range(fc.DEG)] for a in range(s)]
        for r, j in enumerate(order):                       # d = E x exactly
            back = [sum(emat[r][a] * x[a][m] for a in range(s)) for m in range(fc.DEG)]
            assert back == dvec[j], "weights are not a combination of the relations"
        q = [sum(contents[a] * x[a][m] for a in range(s)) / 2 for m in range(fc.DEG)]   # value / pi
        num = series_value(v) / pi
        qnum = sum(mpf(c.numerator) / c.denominator * exp(2j * pi * mpf(m) / N) for m, c in enumerate(q))
        assert abs(qnum - num) < mpf(10) ** (-mp.dps + 30), "value/pi does not match the series"
        values.append(q)
    print("   every basis pattern verified exactly; value/pi matches the summed series to %d digits" % (mp.dps - 30))

    # rational multiples of pi: the non-constant coordinates of value/pi must vanish
    rows = [[values[b][m] for b in range(len(basis))] for m in range(1, fc.DEG)]
    comb = null_basis(rows, len(basis))
    pats = [[sum(c[b] * basis[b][k] for b in range(len(basis))) for k in range(N)] for c in comb]
    qs = [sum(c[b] * values[b][0] for b in range(len(basis))) for c in comb]
    print("   of these, patterns giving a RATIONAL multiple of pi (or zero): dimension %d" % len(pats))
    return pats, qs


# ------------------------------------------------------------------ step E
def levels(pat):
    out = {}
    for c in UNITS:
        s = 1
        while pat[s * c % N] == 0:
            s += 1
            if s > N:
                return None
        out[c] = s
    return out


def cost(pat):
    lv = levels(pat)
    return None if lv is None else sum(Fraction(1, s) for s in lv.values()) / len(UNITS)


def describe(pat, q, label):
    lv = levels(pat)
    cst = cost(pat)
    hist = {}
    for s in lv.values():
        hist[s] = hist.get(s, 0) + 1
    print("   %s: value = %s * pi;  mean(1/s) = %s = %.4f;  state %.3f bits per bit;  classes by s: %s"
          % (label, q, cst, float(cst), 2.88 * float(cst), dict(sorted(hist.items()))))


def main():
    mp.dps = fc.DPS
    t0 = time.time()
    roots = fc.step_a(36)
    order = sorted(roots, key=lambda j: (N // gcd(j, N), j))
    indep, rels, lw = fc.step_b(order)
    print("   (%d roots, %d relations)" % (len(order), len(rels)))
    pats, qs = step_d(order, rels, lw)
    import pickle
    with open(sys.argv[1] if len(sys.argv) > 1 else "pi_patterns.pkl", "wb") as fh:
        pickle.dump((pats, qs), fh)
    print("   saved; %.0f s" % (time.time() - t0))
    # ranks of the coordinate families
    for name, idx in (("s=1 (k = p)", sorted({c % N for c in UNITS})),
                      ("s=2 (k = 2p)", sorted({2 * c % N for c in UNITS})),
                      ("s=3 (k = 3p)", sorted({3 * c % N for c in UNITS})),
                      ("s=4 (k = 4p)", sorted({4 * c % N for c in UNITS}))):
        red, piv = rref([[p[k] for k in idx] for p in pats], len(idx))
        print("   coordinates %-13s: %2d residues, rank %d" % (name, len(idx), len(red)))


if __name__ == "__main__":
    main()
