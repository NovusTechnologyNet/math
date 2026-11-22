"""Referee check of the formula table in Part III ("Two cost measures") and of the two
Huvent-rate formulas of Theorem E, using the space V built by review_space.py.

Run with PYTHONPATH set to the numpy + python-flint folders:
    python review_formulas.py <pickle written by review_space.py>

Each formula is converted to a period-120 pattern rho of F by my own code
(k = N j + i, 2^(-Bj) = 2^(-floor(k/2)) 2^(floor(i/2)) when N = 2B), summed to 200 digits,
tested for exact membership in V, and scored in both measures.
Also: V is compared with the basis stored in pi_space_basis_120.json.
"""
import json
import pickle
import sys
from fractions import Fraction
from math import gcd

from flint import fmpq_mat, fmpq
from mpmath import mp, mpf, pi as MPI

N = 120
UNITS = [c for c in range(1, N) if gcd(c, N) == 1]


def from_bbp(B, Nlen, coeffs, scale, alternating=False):
    """value = scale * sum_j (+-1)^j 2^(-Bj) sum_i coeffs[i] / (Nlen j + i), with Nlen = 2B.
    Returns rho (index k mod 120) for the series equal to that value."""
    assert Nlen == 2 * B
    per = Nlen * (2 if alternating else 1)
    rho = [Fraction(0)] * per
    for i, c in coeffs.items():
        for par in range(2 if alternating else 1):
            k = Nlen * par + i
            rho[k % per] += scale * c * (-1) ** par * Fraction(2) ** (i // 2)
    assert N % per == 0
    return [rho[k % per] for k in range(N)]


def bellard():
    """pi = 2^-6 sum (-1)^n 2^(-10n) (-2^5/(4n+1) - 1/(4n+3) + 2^8/(10n+1) - 2^6/(10n+3)
    - 2^2/(10n+5) - 2^2/(10n+7) + 1/(10n+9)); written with k = 20n + r."""
    terms = [(4, 1, -32), (4, 3, -1), (10, 1, 256), (10, 3, -64), (10, 5, -4), (10, 7, -4), (10, 9, 1)]
    coeffs = {}
    for a, b, c in terms:
        r = 20 * b // a
        assert 20 * b % a == 0
        coeffs[r] = coeffs.get(r, 0) + Fraction(c * 20, a)
    return from_bbp(10, 20, coeffs, Fraction(1, 64), alternating=True)


def ramanujan(n, k):
    return sum(mobius(n // d) * d for d in range(1, n + 1) if n % d == 0 and k % d == 0)


def mobius(n):
    out, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            out = -out
        p += 1
    return -out if n > 1 else out


def tinv_scaled(k):
    """t^(-k) * 2^floor(k/2) as exact (re, im)."""
    re, im = Fraction(1), Fraction(0)
    for _ in range(k):
        re, im = (re + im) / 2, (im - re) / 2
    s = Fraction(2) ** (k // 2)
    return re * s, im * s


def euler():
    """gamma(O10) - gamma(O2) - 2 gamma(O6) = 2 arctan(1/3) + arctan(1/7), as -Im(P(k) t^-k)/k."""
    out = []
    for k in range(N):
        kk = k if k else N
        P = ramanujan(10, kk) - (-1) ** kk - 2 * ramanujan(6, kk)
        re, im = tinv_scaled(kk)
        out.append(-P * im)
    return out


def value_over_pi(rho, dps=200):
    mp.dps = dps
    tot, k = mpf(0), 1
    while k // 2 <= mp.prec + 40:
        r = rho[k % N]
        if r:
            tot += mpf(r.numerator) / r.denominator / (mpf(k) * mpf(2) ** (k // 2))
        k += 1
    return tot / MPI


def measures(rho):
    lv = []
    for c in UNITS:
        s = 1
        while rho[s * c % N] == 0:
            s += 1
        lv.append(s)
    return sum(Fraction(1, s) for s in lv) / len(UNITS), Fraction(sum(1 for x in rho if x), 60)


def rank(rows):
    M = fmpq_mat([[fmpq(x.numerator, x.denominator) for x in r] for r in rows])
    return M.rank()


def main():
    data = pickle.load(open(sys.argv[1], "rb"))
    V = data["V"]                                       # lists over k = 1..120
    Vk = [[v[(k - 1) % N] for k in range(N)] for v in V]   # re-index by k mod 120
    Vk = [[v[(k - 1) % N] if k else v[N - 1] for k in range(N)] for v in V]
    base = rank(Vk)
    assert base == 8

    js = json.load(open("pi_space_basis_120.json"))
    J = [[Fraction(x) for x in p] for p in js["patterns"]]
    print("pi_space_basis_120.json: %d patterns; rank %d; rank together with my V: %d (8 means same span)"
          % (len(J), rank(J), rank(Vk + J)))
    worst = 0
    for p, q in zip(J, js["pi_content"]):
        worst = max(worst, abs(value_over_pi(p, 80) - Fraction(q).numerator / mpf(Fraction(q).denominator)))
    print("   stored pi_content against direct summation: max error %s" % mp.nstr(worst, 3))

    huv1 = from_bbp(12, 24, {3: 768, 4: 512, 6: 128, 12: -16, 14: -16, 15: -12, 20: 2, 22: -1},
                    Fraction(1, 512))
    huv2 = from_bbp(12, 24, {2: 2048, 4: -1024, 9: 192, 10: 128, 12: 32, 18: -4, 20: -4, 21: -3},
                    Fraction(1, 1024))
    bbp = from_bbp(4, 8, {1: 4, 4: -2, 5: -1, 6: -1}, Fraction(1, 4))
    jsn = json.load(open("pi_formula_120.json"))
    thmE = [Fraction(a, jsn["denominator"]) for a in jsn["numerators"]]
    formulas = [("BBP 1995 (pi/4)", bbp), ("Bellard 1997 (pi)", bellard()), ("Euler/Hutton (pi/4)", euler()),
                ("Theorem E 'Huvent rate' #1 (pi/4)", huv1), ("Theorem E 'Huvent rate' #2 (pi/4)", huv2),
                ("pi_formula_120.json (pi/4)", thmE)]
    print("formula                               value/pi           in V   mean(1/s)  terms per bit")
    for name, rho in formulas:
        v = value_over_pi(rho)
        inV = rank(Vk + [rho]) == 8
        c, t = measures(rho)
        print("  %-36s %.15f  %-5s  %-9s  %s" % (name, float(v), inV, c, t))
        tgt = mpf(1) / 4 if "pi/4" in name else mpf(1)
        assert abs(v - tgt) < mpf(10) ** -190, (name, v)
    print("  (all values agree with the stated multiple of pi to 190 digits)")


if __name__ == "__main__":
    main()
