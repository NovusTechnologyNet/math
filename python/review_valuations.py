"""Referee check: valuations of t - zeta_120^j at every prime of Q(zeta_120) above 3 and 5,
computed independently of full_class_theorem.valuation_rows().

Run with PYTHONPATH unset (needs sympy only):  python review_valuations.py

Method (no hand analysis): for p in {3, 5} write N = 120 = p * M with p not dividing M.
Phi_M is squarefree mod p; factor it mod p and Hensel-lift every factor h_i to Z/p^L.
Then G_i(x) = h_i(x^p) / h_i(x) is the p-adic irreducible factor of Phi_120 that belongs to
the i-th prime P_i above p (degree e*f with e = p - 1). For alpha in Z[zeta_120]:

    v_{P_i}(alpha) = v_p( Res(G_i, alpha) ) / f,      f = deg h_i,

normalised so that v_{P_i}(p) = e. The resultant is the determinant of multiplication by
alpha on Z_p[x]/(G_i), computed exactly on integer representatives (correct mod p^L).
Also: the absolute norm of t - zeta^j for the 24 roots, to list every prime involved.
"""
from math import gcd

from sympy import Poly, Symbol, cyclotomic_poly, factorint, GF
from sympy.polys.factortools import dup_zz_hensel_lift
from sympy.polys.domains import ZZ

N = 120
X = Symbol("x")
R0 = [0, 60, 30, 90, 20, 100, 15, 45, 75, 105, 12, 36, 84, 108, 10, 50, 18, 42, 66, 114, 5, 25, 65, 85]
TABLE = [{45: 2, 5: 1, 85: 1}, {105: 2, 25: 1, 65: 1},
         {60: 4, 12: 1, 36: 1, 84: 1, 108: 1}, {90: 4, 18: 1, 42: 1, 66: 1, 114: 1}]
L = 60          # p-adic precision


def poly_divmod(a, b, mod):
    """a, b: coefficient lists, highest degree first; b monic."""
    a = [c % mod for c in a]
    out = []
    while len(a) >= len(b):
        c = a[0]
        out.append(c)
        a = [(x - c * y) % mod for x, y in zip(a, b + [0] * (len(a) - len(b)))][1:]
    return out, a


def det_int(m):
    """Exact determinant (Bareiss)."""
    m = [row[:] for row in m]
    n = len(m)
    sign, prev = 1, 1
    for k in range(n - 1):
        if m[k][k] == 0:
            sw = next((i for i in range(k + 1, n) if m[i][k] != 0), None)
            if sw is None:
                return 0
            m[k], m[sw] = m[sw], m[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                m[i][j] = (m[i][j] * m[k][k] - m[i][k] * m[k][j]) // prev
        prev = m[k][k]
    return sign * m[n - 1][n - 1]


def vp(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def local_factors(p):
    M = N // p
    phiM = Poly(cyclotomic_poly(M, X), X)
    fac = Poly(phiM.as_expr(), X, modulus=p).factor_list()[1]
    hs = []
    for g, mult in fac:
        assert mult == 1
        c = [int(x) % p for x in g.all_coeffs()]
        inv = pow(c[0], -1, p)
        hs.append([x * inv % p for x in c])
    f = [int(x) for x in phiM.all_coeffs()]
    lifted = dup_zz_hensel_lift(ZZ(p), [ZZ(x) for x in f], [[ZZ(x) for x in h] for h in hs], L, ZZ)
    mod = p ** L
    out = []
    for h in lifted:
        h = [int(x) % mod for x in h]
        deg = len(h) - 1
        hp = [0] * (p * deg + 1)                       # h(x^p), highest degree first
        for i, c in enumerate(h):
            hp[i * p] = c
        G, rem = poly_divmod(hp, h, mod)
        assert all(r == 0 for r in rem), "h(x^p) is not divisible by h(x)"
        out.append((deg, G))
    # sanity: product of the G_i is Phi_120 mod p^L
    prod = [1]
    for _, G in out:
        new = [0] * (len(prod) + len(G) - 1)
        for i, a in enumerate(prod):
            for j, b in enumerate(G):
                new[i + j] = (new[i + j] + a * b) % mod
        prod = new
    phiN = [int(x) % mod for x in Poly(cyclotomic_poly(N, X), X).all_coeffs()]
    assert prod == phiN, "local factors do not multiply to Phi_120"
    return out


def mult_matrix(alpha_low, G, mod):
    """Matrix of multiplication by alpha (low-degree-first list) on Z[x]/(G), G high-first monic."""
    d = len(G) - 1
    rows = []
    for k in range(d):
        # x^k * alpha reduced mod G
        a = [0] * k + alpha_low
        high = list(reversed(a))
        _, r = poly_divmod(high, G, mod)
        r = list(reversed(r)) + [0] * d
        rows.append([c for c in r[:d]])
    return rows


def alpha_t_minus(j):
    a = [0] * N
    a[0] += 1
    a[30] += 1            # t = 1 + i, i = zeta^30
    a[j % N] -= 1
    return a


def main():
    mod_all = {}
    for p in (3, 5):
        facs = local_factors(p)
        mod = p ** L
        rows = []
        for f, G in facs:
            row = {}
            for j in range(N):
                m = mult_matrix(alpha_t_minus(j), G, mod)
                dt = det_int(m) % mod
                v = vp(dt, p)
                assert v is not None and v < L - 5, "precision too low"
                assert v % f == 0
                if v:
                    row[j] = v // f
            rows.append(row)
            # check normalisation: v(p) = e = p - 1
            m = mult_matrix([p] + [0] * (N - 1), G, mod)
            assert vp(det_int(m) % mod, p) // f == p - 1
        print("p = %d: %d primes above p (f = %d, e = %d)" % (p, len(facs), facs[0][0], p - 1))
        for r in rows:
            print("   all j in 0..119 with v > 0:", dict(sorted(r.items())))
        mod_all[p] = rows

    print()
    print("restricted to the 24 roots of Part III:")
    distinct = []
    for p in (3, 5):
        for r in mod_all[p]:
            rr = {j: v for j, v in r.items() if j in R0}
            if rr not in distinct:
                distinct.append(rr)
            print("   p = %d: %s" % (p, dict(sorted(rr.items()))))
    print("distinct rows on the 24 roots: %d" % len(distinct))
    for tab in TABLE:
        print("   table row %s  found among the computed rows: %s" % (tab, tab in distinct))
    print("   every computed row is a table row: %s" % all(r in TABLE for r in distinct))

    print()
    print("absolute norms N_{Q(zeta_120)/Q}(t - zeta^j), j in the 24 roots:")
    phiN = Poly(cyclotomic_poly(N, X), X)
    for j in R0:
        a = Poly(1 + X ** 30 - X ** j, X)
        res = phiN.resultant(a)
        print("   j = %3d  order %3d  norm %s  = %s" % (j, N // gcd(j, N), res, factorint(abs(res))))


if __name__ == "__main__":
    main()
