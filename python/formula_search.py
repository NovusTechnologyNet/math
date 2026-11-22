"""Search for binary arctan formulas for pi whose series all converge fast.

In the prime form, the size of the fraction data depends only on the LARGEST
denominator any series reaches, i.e. on the slowest series in the formula.
arctan(1/N) with N = 2^a or 2^a +- 1 has a power-of-two (BBP-type) series gaining
`rate` bits per term: rate = a for N = 2^a, and a - 1/2 for N = 2^a +- 1.

A formula  m*pi/4 = sum c_j * arctan(1/N_j)  exists exactly when the Gaussian
integers (N_j + i)^c_j multiply to a unit times a power of (1+i) times a rational,
which is a linear condition on signed prime exponents. This script finds all such
relations among the candidates and reports those with m != 0, by slowest rate.
"""
from fractions import Fraction
from math import atan, pi


def factor(m):
    f, p = {}, 2
    while p * p <= m:
        while m % p == 0:
            f[p] = f.get(p, 0) + 1
            m //= p
        p += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f


def sqrt_minus_one(p):
    for g in range(2, p):
        r = pow(g, (p - 1) // 4, p)
        if r * r % p == p - 1:
            return min(r, p - r)


def nullspace(rows, ncols):
    """Rational nullspace basis of an integer matrix (list of rows)."""
    m = [[Fraction(x) for x in r] for r in rows]
    pivots, r = [], 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        m[r] = [x / m[r][c] for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                m[i] = [x - m[i][c] * y for x, y in zip(m[i], m[r])]
        pivots.append(c)
        r += 1
    basis = []
    for free in (c for c in range(ncols) if c not in pivots):
        v = [Fraction(0)] * ncols
        v[free] = Fraction(1)
        for i, c in enumerate(pivots):
            v[c] = -m[i][free]
        den = 1
        for x in v:
            den = den * x.denominator // __import__("math").gcd(den, x.denominator)
        basis.append([int(x * den) for x in v])
    return basis


def search(min_rate, max_a=40):
    cands = []
    for a in range(1, max_a + 1):
        for N, rate in ((2 ** a - 1, a - 0.5), (2 ** a, float(a)), (2 ** a + 1, a - 0.5)):
            if N >= 2 and rate >= min_rate and N < 2 ** 26:
                cands.append((N, rate))
    vec = {}
    for N, rate in cands:
        v = {}
        for p, e in factor(N * N + 1).items():
            if p != 2:
                v[p] = e if N % p == sqrt_minus_one(p) else -e
        vec[N] = v
    alive = dict(cands)
    while True:                      # drop candidates owning a prime nobody shares
        count = {}
        for N in alive:
            for p in vec[N]:
                count[p] = count.get(p, 0) + 1
        dead = [N for N in alive if any(count[p] == 1 for p in vec[N])]
        if not dead:
            break
        for N in dead:
            del alive[N]
    names = sorted(alive)
    primes = sorted({p for N in names for p in vec[N]})
    rows = [[vec[N].get(p, 0) for N in names] for p in primes]
    out = []
    for rel in nullspace(rows, len(names)):
        m = sum(c * atan(1.0 / N) for c, N in zip(rel, names)) / (pi / 4)
        out.append((round(m), rel))
    return names, alive, out


if __name__ == "__main__":
    for min_rate in (1.0, 1.5, 2.0, 2.5, 3.0, 3.5):
        names, rates, rels = search(min_rate)
        good = [(m, r) for m, r in rels if m != 0]
        print("slowest rate >= %.1f bits/term: %d usable arctans, %d relations, %d give pi"
              % (min_rate, len(names), len(rels), len(good)))
        for m, rel in good[:2]:
            terms = " ".join("%+d*atan(1/%d)" % (c, N) for c, N in zip(rel, names) if c)
            print("    %d*pi/4 = %s" % (m, terms))
            used = min(rates[N] for c, N in zip(rel, names) if c)
            print("    slowest series in it: %.1f bits/term" % used)
