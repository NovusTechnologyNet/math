"""The full class: EVERY rational periodic pattern, not only the symmetric ones.

Run with the system Python (needs sympy and mpmath):  python full_class_theorem.py

The series studied are   S = sum over k >= 1 of rho(k) * 2^(-floor(k/2)) / k   with rho
any periodic rational pattern. Write t = 1 + i and w_r = 1 - r/t for a root of unity r.
Every such series is  (1/2i) * sum over r of d_r * Log(w_r)  with algebraic d_r, and its
k-th term is a multiple of  D(k) = sum over r of d_r * r^k.

Steps (see pi_formula_theorem.md, Part III):
  A. find the roots of unity that can occur in a multiplicative relation among the w_r
     (the "exceptional" roots and the ones that share a prime with them);
  B. find every multiplicative relation among those w_r, verify each one exactly in
     Z[zeta_120], and certify that there are no more;
  C. linear algebra: can a combination of those relations have D(k) = 0 on all slow k
     and still carry pi?
"""
import sys
from fractions import Fraction
from math import gcd

from mpmath import mp, mpf, mpc, pi, log, exp, pslq, matrix, svd_r, svd_c, e as EULER_E
from sympy import factorint, totient, cyclotomic_poly, Poly, Symbol

from wider_theorem import orbits_of_order, atom

N = 120
DPS = 200

# ---------------------------------------------------------------- exact arithmetic in Z[zeta_120]
_x = Symbol("x")
PHI = [int(c) for c in reversed(Poly(cyclotomic_poly(N, _x), _x).all_coeffs())]
DEG = len(PHI) - 1


def reduce(a):
    a = list(a) + [0] * max(0, DEG - len(a))
    for k in range(len(a) - 1, DEG - 1, -1):
        c = a[k]
        if c:
            a[k] = 0
            for m in range(DEG):
                if PHI[m]:
                    a[k - DEG + m] -= c * PHI[m]
    return a[:DEG]


def cmul(a, b):
    res = [0] * (2 * DEG - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    res[i + j] += ai * bj
    return reduce(res)


def zeta(j):
    a = [0] * (j % N + 1)
    a[j % N] = 1
    return reduce(a)


ONE = zeta(0)
T = [u + v for u, v in zip(ONE, zeta(N // 4))]                 # t = 1 + i


def cpow(a, n):
    out = ONE
    for _ in range(n):
        out = cmul(out, a)
    return out


def t_minus(j):
    return [u - v for u, v in zip(T, zeta(j))]


def exact_root_of_unity(rel):
    """rel: {j: e}. Is prod (1 - zeta^j/t)^e a root of unity? Returns its exponent m
    (the product equals zeta^m), or None."""
    total = sum(rel.values())
    lhs, rhs = ONE, ONE
    for j, e in rel.items():
        if e > 0:
            lhs = cmul(lhs, cpow(t_minus(j), e))
        elif e < 0:
            rhs = cmul(rhs, cpow(t_minus(j), -e))
    if total > 0:
        rhs = cmul(rhs, cpow(T, total))
    elif total < 0:
        lhs = cmul(lhs, cpow(T, -total))
    for m in range(N):
        if lhs == cmul(zeta(m), rhs):
            return m
    return None


# ---------------------------------------------------------------- step A
def step_a(max_size):
    """Exceptional orbits: every prime of the atom divides the order of the roots."""
    exceptional, nonunit = [], []
    d = 1
    while d <= 16 * max_size:
        size = totient(d) // (2 if d % 4 == 0 else 1)
        if size <= max_size:
            for o in orbits_of_order(d):
                a, b = atom(o)
                primes = factorint(a * a + b * b)
                if all(d % p == 0 for p in primes):
                    exceptional.append((d, o, (a, b)))
        d += 1
    print("A. exceptional orbits (no primitive prime), orbit sizes up to %d, orders up to %d:"
          % (max_size, 16 * max_size))
    roots = {}
    for d, o, z in exceptional:
        assert N % d == 0, "an exceptional orbit of order %d does not divide %d" % (d, N)
        js = sorted(int(f * N) for f in o)
        print("     order %2d  roots zeta^%s  atom %s" % (d, js, complex(*z)))
        for j in js:
            roots[j] = "exceptional"
        primes = factorint(z[0] ** 2 + z[1] ** 2)
        for p in primes:
            pa = 1
            while (d // pa) % p == 0:
                pa *= p
            dprime = d // pa
            # prime-to-p part of each root: exponent u = 1 mod dprime, 0 mod pa
            u = next(u for u in range(0, d, pa) if u % dprime == 1 % dprime)
            for f in o:
                nonunit.append((int(f * N) * u % N, p))
    for j, p in sorted(set(nonunit)):
        if j not in roots:
            roots[j] = "shares the prime %d" % p
            print("     also  zeta^%d  (%s with an exceptional root)" % (j, roots[j]))
    return roots


# ---------------------------------------------------------------- step B
def w(j):
    return 1 - exp(2j * pi * mpf(j) / N) / mpc(1, 1)


def step_b(order):
    rho = +EULER_E                       # a generic real number mixes modulus and angle
    x0 = rho * pi / 60
    lw = {j: log(w(j)) for j in order}
    x = {j: lw[j].real + rho * lw[j].imag for j in order}
    indep, rels = [], []
    for j in order:
        vec = [x0] + [x[i] for i in indep] + [x[j]]
        rel = pslq(vec, maxcoeff=10 ** 5, maxsteps=10 ** 6)
        if rel is None:
            indep.append(j)
            continue
        assert rel[-1] != 0, "the 'independent' set is not independent"
        if rel[-1] < 0:
            rel = [-c for c in rel]
        e = {i: c for i, c in zip(indep + [j], rel[1:]) if c}
        total = sum(c * lw[i] for i, c in e.items())
        assert abs(total.real) < mpf(10) ** (-DPS + 30)
        m = exact_root_of_unity(e)
        assert m is not None, "relation fails the exact check: %s" % e
        content = Fraction(int(mp.nint(total.imag / pi * 60)), 60)      # sum e*Log w = content * i*pi
        assert abs(total.imag / pi - mpf(content.numerator) / content.denominator) < mpf(10) ** (-DPS + 30)
        assert (content * 60 - m) % 120 == 0, "angle does not match the exact root of unity"
        rels.append((e, content))
    return indep, rels, lw


def valuation_rows(order):
    """Valuations of t - zeta^j at the primes above 2, 3, 5 (see the note, Part III)."""
    rows = [[1] * len(order)]
    table = [{45: 2, 5: 1, 85: 1}, {105: 2, 25: 1, 65: 1},
             {60: 4, 12: 1, 36: 1, 84: 1, 108: 1}, {90: 4, 18: 1, 42: 1, 66: 1, 114: 1}]
    for tab in table:
        rows.append([tab.get(j, 0) for j in order])
    return rows


def certify_rank(order, indep, lw):
    """The matrix of all valuations and all absolute values, on the independent columns."""
    units = [a for a in range(1, N) if gcd(a, N) == 1 and a % 4 == 1]
    cols = [order.index(j) for j in indep]
    rows = [[mpf(r[c]) for c in cols] for r in valuation_rows(order)]
    for a in units:
        rows.append([log(abs(w(j * a % N))) for j in indep])
    sv = svd_r(matrix(rows), compute_uv=False)
    return min(sv), max(sv)


# ---------------------------------------------------------------- step C
def find_prime(n):
    p = n + 1
    while True:
        if all(p % q for q in range(2, int(p ** 0.5) + 1)):
            for g in range(2, p):
                wv = pow(g, (p - 1) // n, p)
                if all(pow(wv, n // q, p) != 1 for q in factorint(n)):
                    return p, wv
        p += n


def rank_mod(rows, p):
    rows = [list(r) for r in rows]
    rank, ncols = 0, len(rows[0]) if rows else 0
    for c in range(ncols):
        piv = next((i for i in range(rank, len(rows)) if rows[i][c] % p), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][c], p - 2, p)
        rows[rank] = [v * inv % p for v in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(v - f * u) % p for v, u in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def step_c(rels):
    s = len(rels)
    contents = [c for _, c in rels]
    scale = 60
    p1, w1 = find_prime(N)
    print("C. speed. A term k is present exactly when D(k) is non-zero; the speed is half the")
    print("   smallest gcd(k, 120) that is present. Unknowns: one coefficient per relation (%d)." % s)
    print("   exact ranks are computed modulo the prime %d (a lower bound) and by 200-digit SVD." % p1)
    print("   threshold  slow terms  rank   solutions  can a solution carry pi?")
    results = {}
    for g in (2, 3, 4, 5, 6, 8, 10, 12, 15):
        slow = [k for k in range(1, N + 1) if gcd(k, N) < g]
        num = [[sum(c * exp(2j * pi * mpf(j * k % N) / N) for j, c in e.items()) for e, _ in rels] for k in slow]
        sv = svd_c(matrix(num), compute_uv=False)
        rank_num = sum(1 for v in sv if v > mpf(10) ** (-DPS // 2))
        small = [v for v in sv if v <= mpf(10) ** (-DPS // 2)]
        assert all(v < mpf(10) ** (-DPS + 40) for v in small), "ambiguous singular value"
        mod = [[sum(c * pow(w1, j * k % N, p1) for j, c in e.items()) % p1 for e, _ in rels] for k in slow]
        rank_p = rank_mod(mod, p1)
        num2 = num + [[mpf(int(c * scale)) for c in contents]]
        sv2 = svd_c(matrix(num2), compute_uv=False)
        rank2 = sum(1 for v in sv2 if v > mpf(10) ** (-DPS // 2))
        mod2 = mod + [[int(c * scale) % p1 for c in contents]]
        rank2_p = rank_mod(mod2, p1)
        carries = rank2 > rank_num
        results[g] = (s - rank_num, carries)
        print("   gcd >= %-2d   %3d        %2d (mod p: %2d)   %2d        %s   (with pi row: %d, mod p: %d)"
              % (g, len(slow), rank_num, rank_p, s - rank_num, "YES" if carries else "no", rank2, rank2_p))
    return results


def main():
    mp.dps = DPS
    roots = step_a(36)
    order = sorted(roots, key=lambda j: (N // gcd(j, N), j))
    print("   %d roots of unity can occur: zeta_120^j for j in %s" % (len(order), order))
    indep, rels, lw = step_b(order)
    print("B. multiplicative relations among the w_r = 1 - r/t  (each verified exactly in Z[zeta_120]):")
    for e, content in rels:
        print("     %s   ->   sum e*Log(w) = %s * i*pi"
              % (" ".join("%+d[%d]" % (c, j) for j, c in sorted(e.items())), content))
    lo, hi = certify_rank(order, indep, lw)
    print("   independent: %d of %d;  relations: %d." % (len(indep), len(order), len(rels)))
    print("   certificate that there are no more: the %d independent columns of the place matrix have"
          % len(indep))
    print("   smallest singular value %s (largest %s), so they are independent." % (mp.nstr(lo, 5), mp.nstr(hi, 5)))
    step_c(rels)


if __name__ == "__main__":
    main()
