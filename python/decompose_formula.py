"""Write the new formula as a combination of named series.

Run:  python decompose_formula.py

With t = 1 + i and a set O of roots of unity:
    ARG(O) = sum over r in O of  Im Log(1 - r/t)      (arctangent type)
    LOG(O) = sum over r in O of  log|1 - r/t|         (logarithm type)
Both are series  sum_k rho(k) 2^(-floor(k/2)) / k  with rational rho.
"""
import json
from fractions import Fraction

from mpmath import mp, mpf, mpc, pi, exp, sqrt, log, atan

from cheaper_search import N, reduce_rows

mp.dps = 50
T = mpc(1, 1)


def z(j, n):
    return exp(2j * pi * mpf(j) / n)


def gauss(x):
    a, b = int(mp.nint(x.real)), int(mp.nint(x.imag))
    assert abs(x - mpc(a, b)) < mpf(10) ** -30, x
    return a, b


def tinv(k):
    """t^(-k) * 2^floor(k/2) as an exact Gaussian rational (re, im)."""
    re, im = Fraction(1), Fraction(0)
    for _ in range(k):
        re, im = (re + im) / 2, (im - re) / 2
    s = Fraction(2) ** (k // 2)
    return re * s, im * s


def pattern(power_sum, kind):
    """rho(k) for  -Im( t^-k * P(k) ) / k   (kind 'arg')  or  -Re(...) / k  (kind 'log')."""
    out = []
    for k in range(N):
        kk = k if k else N
        a, b = gauss(power_sum(kk))
        re, im = tinv(kk)
        out.append(-(re * b + im * a) if kind == "arg" else -(re * a - im * b))
    return out


def orbit(roots):
    return lambda k: sum(r ** k for r in roots)


O1 = [z(0, 1)]
O2 = [z(1, 2)]
O6 = [z(1, 6), z(5, 6)]
O10 = [z(a, 10) for a in (1, 3, 7, 9)]
O8a = [z(1, 8), z(5, 8)]
O8b = [z(3, 8), z(7, 8)]
O24 = [z(a, 24) for a in (1, 5, 13, 17)]


def combo(parts, kind):
    pats = [(c, pattern(orbit(o), kind)) for c, o in parts]
    return [sum(c * p[k] for c, p in pats) for k in range(N)]


def twisted():
    """sqrt3 * [g(z24) - g(z24^5) + g(z24^13) - g(z24^17)]  +  sqrt3 * [g(z6) - g(z6^5)]: value 0."""
    def ps(k):
        return sqrt(3) * (z(1, 24) ** k - z(5, 24) ** k + z(13, 24) ** k - z(17, 24) ** k
                          + z(1, 6) ** k - z(5, 6) ** k)
    return pattern(ps, "arg")


NAMED = [
    ("ARG(O1)                         [= pi/4, the arctan(1) series]", combo([(1, O1)], "arg"), Fraction(1, 4)),
    ("ARG(O6)                         [= 0]", combo([(1, O6)], "arg"), Fraction(0)),
    ("ARG(O10) - ARG(O2)              [= pi/4]", combo([(1, O10), (-1, O2)], "arg"), Fraction(1, 4)),
    ("LOG(O6) - 2 LOG(O1)             [= 0]", combo([(1, O6), (-2, O1)], "log"), Fraction(0)),
    ("LOG(O8a) - 2 LOG(O1)            [= 0]", combo([(1, O8a), (-2, O1)], "log"), Fraction(0)),
    ("LOG(O10) - LOG(O2) - 3 LOG(O1)  [= 0]", combo([(1, O10), (-1, O2), (-3, O1)], "log"), Fraction(0)),
    ("LOG(O24) - LOG(O8b) - 2 LOG(O1) [= 0]", combo([(1, O24), (-1, O8b), (-2, O1)], "log"), Fraction(0)),
    ("TW  (sqrt 3 - twisted, order 24 and 6) [= 0]", twisted(), Fraction(0)),
]


def value(pat):
    total, k = mpf(0), 1
    while k // 2 <= mp.prec + 40:
        r = pat[k % N]
        if r:
            total += mpf(r.numerator) / r.denominator / (mpf(k) * mpf(2) ** (k // 2))
        k += 1
    return total


def solve(target):
    """Exact rational coefficients c with sum c_i * NAMED_i = target."""
    n = len(NAMED)
    rows = [[NAMED[i][1][k] for i in range(n)] + [target[k]] for k in range(N)]
    piv, r = [], 0
    for c in range(n):
        p = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        inv = 1 / rows[r][c]
        rows[r] = [v * inv for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [v - f * u for v, u in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    assert all(not any(row) for row in rows[r:]), "target is not a combination of the named series"
    return piv, [rows[i][n] for i in range(r)]


def main():
    for name, pat, val in NAMED:
        v = value(pat) / pi
        assert abs(v - mpf(val.numerator) / val.denominator) < mpf(10) ** -40, (name, v)
    red = reduce_rows([list(p) + [0] for _, p, _ in NAMED])
    print("named series: %d, independent: %d (all values checked to 40 digits)" % (len(NAMED), len(red)))
    data = json.load(open("pi_formula_120.json"))
    target = [Fraction(a, data["denominator"]) for a in data["numerators"]]
    piv, coef = solve(target)
    print("new formula  =")
    total = Fraction(0)
    for i, c in zip(piv, coef):
        if c:
            print("    %+6s * %s" % (c, NAMED[i][0]))
            total += c * NAMED[i][2]
    print("value: %s * pi" % total)


if __name__ == "__main__":
    main()
