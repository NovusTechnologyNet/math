"""Computer checks for the theorem on binary arctangent formulas for pi.

Run with the system Python (needs sympy and mpmath):  python machin_theorem.py

Part 1  The Bang/Schinzel ingredient. For odd n let
            L_n = 2^n - 2^((n+1)/2) + 1,   M_n = 2^n + 2^((n+1)/2) + 1,
        so L_n * M_n = 4^n + 1. A prime factor is "primitive" if it divides no
        4^d + 1 with d a proper divisor of n. The proof needs: for every odd
        n >= 7, both L_n and M_n have a primitive prime factor. (Schinzel 1962.)

Part 2  The finite core. The proof reduces every formula to one among
        arctan(1/N), N in {1, 2, 3, 5, 7, 8, 9, 32}. List all relations there.

Part 3  A wider family. Every binary arctangent-type series is a rational
        combination of  S = Im log( Phi_d(y) / y^deg ),  y = eps * (1+i)^n,
        Phi_d the d-th cyclotomic polynomial (d odd), eps a unit; its speed is
        n/2 bits per term. Search for relations that give pi using only
        series with n/2 >= a threshold.
"""
import sys
from fractions import Fraction
from math import gcd

from mpmath import mp, mpc, mpf, log, pi
from sympy import cyclotomic_poly, factorint, symbols

mp.dps = 60
X = symbols("x")


# ------------------------------------------------------------------ Part 1
def primitive_part(x, n):
    for d in range(1, n):
        if n % d == 0:
            g = gcd(x, 4 ** d + 1)
            while g > 1:
                x //= g
                g = gcd(x, g)
    return x


def size_bound(limit):
    """Why n beyond the computed range needs no checking.

    With t = 1+i, {L_n, M_n} = {|t^n - 1|^2, |t^n + 1|^2}, and the part that can hold
    primitive primes is a_n = |Phi_n(+-t)|^2. Since |Phi_n(z)| is the product of
    |z^d - 1|^mu(n/d) over d | n, and |z| = sqrt(2),
        a_n >= 2^phi(n) * (A/B)^2,   A = prod (1 - 2^(-d/2)),  B = prod (1 + 2^(-d/2)),
    products over odd d. At most one non-primitive prime (a divisor of n, to the
    first power) divides Phi_4n(2), so a_n > n forces a primitive prime factor.
    With phi(n) >= sqrt(n) this holds once 2^sqrt(n) * (A/B)^2 > n."""
    a = b = mpf(1)
    for d in range(1, 400, 2):
        a *= 1 - mpf(2) ** (-mpf(d) / 2)
        b *= 1 + mpf(2) ** (-mpf(d) / 2)
    c = (a / b) ** 2
    n = 9
    while mpf(2) ** mp.sqrt(n) * c <= n:
        n += 2
    print("Part 0: A = %s, B = %s, (A/B)^2 = %s" % (mp.nstr(a, 6), mp.nstr(b, 6), mp.nstr(c, 6)))
    print("        the size bound alone settles every odd n >= %d; the computed range goes to %d"
          % (n, limit))
    return n


def part1(limit):
    bad = []
    for n in range(1, limit + 1, 2):
        half = 2 ** ((n + 1) // 2)
        lo, hi = 2 ** n - half + 1, 2 ** n + half + 1
        pl, pm = primitive_part(lo, n), primitive_part(hi, n)
        if pl == 1 or pm == 1:
            bad.append((n, lo, pl, hi, pm))
    print("Part 1: odd n up to %d; cases where L_n or M_n has NO primitive prime factor:" % limit)
    for n, lo, pl, hi, pm in bad:
        print("   n=%d  L=%d (primitive part %d)   M=%d (primitive part %d)" % (n, lo, pl, hi, pm))
    return [b[0] for b in bad]


# ------------------------------------------------------------------ Gaussian integers
def gmul(u, v):
    return (u[0] * v[0] - u[1] * v[1], u[0] * v[1] + u[1] * v[0])


def gpow(u, n):
    r = (1, 0)
    while n:
        if n & 1:
            r = gmul(r, u)
        u = gmul(u, u)
        n >>= 1
    return r


def sqrt_minus_one(p):
    for g in range(2, p):
        r = pow(g, (p - 1) // 4, p)
        if r * r % p == p - 1:
            return min(r, p - r)


def arg_vector(w, cache):
    """Signed exponents of the Gaussian primes above odd rational primes."""
    a, b = w
    g = gcd(a, b)
    a, b = a // g, b // g
    vec = {}
    for p, e in factorint(a * a + b * b).items():
        if p == 2:
            continue
        if p not in cache:
            cache[p] = sqrt_minus_one(p)
        vec[p] = e if (a + b * cache[p]) % p == 0 else -e
    return vec


def nullspace(rows, ncols):
    m = [[Fraction(x) for x in r] for r in rows]
    pivots, r = [], 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        inv = m[r][c]
        m[r] = [x / inv for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [x - f * y for x, y in zip(m[i], m[r])]
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
            den = den * x.denominator // gcd(den, x.denominator)
        basis.append([int(x * den) for x in v])
    return basis


def relations(gens):
    """gens: list of (name, value S, vector). Returns (alive names, basis relations
    as (pi content in units of pi/4, coefficient list))."""
    alive = list(range(len(gens)))
    while True:                      # a generator owning a prime nobody shares is out
        count = {}
        for j in alive:
            for p in gens[j][2]:
                count[p] = count.get(p, 0) + 1
        keep = [j for j in alive if all(count[p] > 1 for p in gens[j][2])]
        if len(keep) == len(alive):
            break
        alive = keep
    primes = sorted({p for j in alive for p in gens[j][2]})
    rows = [[gens[j][2].get(p, 0) for j in alive] for p in primes]
    out = []
    for rel in nullspace(rows, len(alive)):
        total = sum(c * gens[j][1] for c, j in zip(rel, alive))
        m = total / (pi / 4)
        mi = int(mp.nint(m))
        assert abs(m - mi) < mpf(10) ** -30, "pi content is not an integer: %s" % m
        out.append((mi, rel))
    return alive, out


# ------------------------------------------------------------------ Part 2
def part2():
    cache = {}
    gens = []
    for N in (1, 2, 3, 5, 7, 8, 9, 32):
        gens.append(("atan(1/%d)" % N, mp.atan(mpf(1) / N), arg_vector((N, 1), cache)))
    alive, rels = relations(gens)
    print("Part 2: relations among atan(1/N), N in {1,2,3,5,7,8,9,32}: %d independent" % len(rels))
    for m, rel in rels:
        terms = " ".join("%+d*%s" % (c, gens[j][0]) for c, j in zip(rel, alive) if c)
        print("   %+d*pi/4 = %s" % (m, terms))
    fast = [g for g in gens if g[0] in ("atan(1/7)", "atan(1/8)", "atan(1/9)", "atan(1/32)")]
    alive, rels = relations(fast)
    print("   restricted to the fast ones {7, 8, 9, 32}: %d relation(s), pi content %s"
          % (len(rels), [m for m, _ in rels]))


# ------------------------------------------------------------------ Part 3
UNITS = {"1": (1, 0), "i": (0, 1), "-1": (-1, 0), "-i": (0, -1)}


def part3(min_n, max_bits):
    cache, gens, seen = {}, [], set()
    for d in (1, 3, 5, 7, 9, 11, 13, 15, 21):
        coeffs = [int(c) for c in cyclotomic_poly(d, X, polys=True).all_coeffs()]
        deg = len(coeffs) - 1
        n = min_n
        while n * deg <= max_bits:
            tn = gpow((1, 1), n)
            for ename, eps in UNITS.items():
                y = gmul(eps, tn)
                w = (0, 0)
                for c in coeffs:                      # Horner: w = Phi_d(y)
                    w = gmul(w, y)
                    w = (w[0] + c, w[1])
                key = (w[0], abs(w[1]))               # a conjugate is the same series, negated
                if w[1] == 0 or key in seen:
                    continue
                seen.add(key)
                yd = gpow(y, deg)
                s = log(mpc(w[0], w[1]) / mpc(yd[0], yd[1])).imag
                gens.append(("Phi%d(%s*t^%d)" % (d, ename, n), s, arg_vector(w, cache), n))
            n += 1
    alive, rels = relations(gens)
    good = [(m, rel) for m, rel in rels if m != 0]
    print("Part 3: speed >= %.1f bits/term: %d series, %d survive pruning, %d relations, %d give pi"
          % (min_n / 2, len(gens), len(alive), len(rels), len(good)))
    for m, rel in good[:3]:
        used = [(c, gens[j][0], gens[j][3]) for c, j in zip(rel, alive) if c]
        print("   %+d*pi/4 = %s" % (m, " ".join("%+d*%s" % (c, name) for c, name, _ in used)))
        print("      slowest series in it: %.1f bits/term" % (min(n for _, _, n in used) / 2))
    return len(good)


if __name__ == "__main__":
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 601
    size_bound(limit)
    part1(limit)
    part2()
    if "--core-only" in sys.argv:
        sys.exit(0)
    bits = int(sys.argv[2]) if len(sys.argv) > 2 else 64
    for min_n in (1, 2, 3, 4, 5, 6):
        part3(min_n, bits)
