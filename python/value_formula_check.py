# The value formula and the sharpness of Theorem D (exact rational arithmetic).
#
#   python value_formula_check.py
#
# V is the 8-dimensional space of rational patterns rho of period 120 whose series
#     S(rho) = sum_{k>=1} rho(k) 2^(-floor(k/2)) / k
# is a rational multiple of pi (Theorem C). It is spanned by the eight named patterns
# A1, A6, A10, L6, L8, L10, L24, TW of lean/Pilean/PiFormula/VSeries.lean, with values
# pi/4, 0, pi/4, 0, 0, 0, 0, 0.
#
# Checked here:
#   1. The value formula. On V,
#        S(rho) = (7 rho(1)/12 + rho(2)/8 + rho(3)/6 - 7 rho(7)/12 + rho(9)/6 - rho(14)/8) pi/4.
#      (In Lean: PiFormula.value_formula, from Baker's theorem.)
#   2. The formula on BBP's formula, Bellard's formula and the new formula of
#      pi_formula_120.json, and each of these series numerically.
#   3. Sharp Theorem D: the patterns of V with no term at gcd(k, 120) < 4 form a line,
#      spanned by -2 L8 + 2 L10 + L24, of value 0.
#   4. Theorem D is best possible: for each two of the classes gcd(k, 120) = 1, 2, 3 there is
#      a formula for pi in V with no term in those two classes.
# Items 3 and 4 are also in Lean: PiFormula.theoremD_sharp and PiFormula.finrank_fast (from
# Baker's theorem), PiFormula.theoremD_best_possible (unconditional).
import cmath
import json
import math
from fractions import Fraction as Fr

import mpmath as mp
import sympy as sp

mp.mp.dps = 40


def gi_pow(n): return [1, 1j, -1, -1j][n % 4]
def ngi_pow(n): return [1, -1j, -1, 1j][n % 4]
def c2(k): return (2 if k % 2 == 0 else 0) - 1
def c6(k): return (6 if k % 6 == 0 else 0) - (3 if k % 3 == 0 else 0) - (2 if k % 2 == 0 else 0) + 1
def c10(k): return (10 if k % 10 == 0 else 0) - (5 if k % 5 == 0 else 0) - (2 if k % 2 == 0 else 0) + 1
def p8a(k): return 2 * gi_pow(k // 2) if k % 2 == 0 else 0
def p8b(k): return 2 * ngi_pow(k // 2) if k % 2 == 0 else 0
def p24(k): return (6 * gi_pow(k // 6) if k % 6 == 0 else 0) - p8b(k)


z24 = cmath.exp(2j * cmath.pi / 24)


def ptw(k):
    s3 = z24 ** 2 - z24 ** 10
    v = s3 * (z24 ** k - z24 ** (5 * k) + z24 ** (13 * k) - z24 ** (17 * k)
              + z24 ** (4 * k) - z24 ** (20 * k))
    return complex(round(v.real), round(v.imag))


def U(k): return ngi_pow(k // 2) * (2 if k % 2 == 0 else (1 - 1j))
def A(P, k): return -(P(k) * U(k)).imag
def L(P, k): return -(P(k) * U(k)).real


one = lambda k: 1
named2 = [
    lambda k: A(one, k), lambda k: A(c6, k), lambda k: A(c10, k) - A(c2, k),
    lambda k: L(c6, k) - 2 * L(one, k), lambda k: L(p8a, k) - 2 * L(one, k),
    lambda k: L(c10, k) - L(c2, k) - 3 * L(one, k),
    lambda k: L(p24, k) - L(p8b, k) - 2 * L(one, k), lambda k: A(ptw, k)]
NAMES = ["A1", "A6", "A10", "L6", "L8", "L10", "L24", "TW"]
VALUE = [1, 0, 1, 0, 0, 0, 0, 0]          # in units of pi/4


def row(k):
    """The values at k of the eight named patterns."""
    return [sp.Rational(int(round(named2[i](k))), 2) for i in range(8)]


SIX = [(1, sp.Rational(7, 12)), (2, sp.Rational(1, 8)), (3, sp.Rational(1, 6)),
       (7, sp.Rational(-7, 12)), (9, sp.Rational(1, 6)), (14, sp.Rational(-1, 8))]

# 1. The value formula on V: sum of c_k * row(k) is the value vector.
lhs = [sum(c * row(k)[i] for k, c in SIX) for i in range(8)]
assert lhs == VALUE, lhs
print("1. value formula holds on the eight named patterns: OK")


# 2. Three known formulas.
def functional(rho):
    return sum(Fr(c.p, c.q) * rho(k) for k, c in SIX)


def series(rho, K=400):
    return mp.fsum(mp.mpf(rho(k).numerator) / rho(k).denominator / mp.mpf(2) ** (k // 2) / k
                   for k in range(1, K))


def bbp(k):
    # pi = sum 16^-j (4/(8j+1) - 2/(8j+4) - 1/(8j+5) - 1/(8j+6))
    a = {1: 4, 4: -2, 5: -1, 6: -1}
    i = (k - 1) % 8 + 1
    return Fr(a.get(i, 0) * 2 ** (i // 2))


def bellard(k):
    # pi = 2^-6 sum (-1)^n 2^-10n (-2^5/(4n+1) - 1/(4n+3) + 2^8/(10n+1) - 2^6/(10n+3)
    #                              - 2^2/(10n+5) - 2^2/(10n+7) + 1/(10n+9))
    tot = Fr(0)
    for (c, m, b) in [(-32, 4, 1), (-1, 4, 3), (256, 10, 1), (-64, 10, 3), (-4, 10, 5),
                      (-4, 10, 7), (1, 10, 9)]:
        mult = 20 // m
        if (k - mult * b) % 20 == 0 and k >= mult * b:
            n = (k - mult * b) // 20
            tot += Fr((-1) ** n * c * mult, 64) * Fr(2) ** (k // 2 - 10 * n)
    return tot


d = json.load(open("pi_formula_120.json"))


def new(k):
    return Fr(d["numerators"][k % 120], d["denominator"])


print("2. the six-term value, in units of pi/4, against the series:")
for name, rho in [("BBP", bbp), ("Bellard", bellard), ("new formula", new)]:
    f = functional(rho)
    s = series(rho) / (mp.pi / 4)
    assert abs(s - f) < mp.mpf(10) ** -30
    six = ", ".join("rho(%d) = %s" % (k, rho(k)) for k, _ in SIX if rho(k) != 0)
    print("   %-12s %s   (%s)" % (name, f, six))

# 3. Sharp Theorem D.
ks = [k for k in range(1, 121) if math.gcd(k, 120) < 4]
ns = sp.Matrix([row(k) for k in ks]).nullspace()
assert len(ns) == 1
v = list(ns[0])
assert v == [0, 0, 0, 0, -2, 2, 1, 0], v
pat = [sum(v[i] * row(k)[i] for i in range(8)) for k in range(1, 121)]
gcds = sorted({math.gcd(k, 120) for k, x in zip(range(1, 121), pat) if x != 0})
print("3. patterns of V with no term at gcd(k,120) < 4: the line spanned by",
      " ".join("%+d %s" % (c, n) for c, n in zip(v, NAMES) if c != 0))
print("   value %s; its terms sit at gcd(k,120) in %s" % (v[0] + v[2], gcds))

# 4. Theorem D is best possible.
print("4. avoiding two of the three slow classes:")
for S in [{1, 2}, {1, 3}, {2, 3}, {1, 2, 3}]:
    kk = [k for k in range(1, 121) if math.gcd(k, 120) in S]
    ns = sp.Matrix([row(k) for k in kk]).nullspace()
    vals = [x[0] + x[2] for x in ns]
    print("   no term at gcd in %s: dimension %d, formulas for pi: %s"
          % (sorted(S), len(ns), "yes" if any(x != 0 for x in vals) else "no"))
    assert any(x != 0 for x in vals) == (len(S) == 2)

# The three explicit formulas used in Lean (coordinates in the named basis).
for S, vec in [({1, 2}, [0, -2, 1, 0, 0, 0, 0, 0]), ({1, 3}, [2, 0, -1, 0, 0, 0, 0, 0]),
               ({2, 3}, [6, 4, 1, 0, 0, 0, 0, 0])]:
    for k in range(1, 121):
        if math.gcd(k, 120) in S:
            assert sum(vec[i] * row(k)[i] for i in range(8)) == 0
    print("   %s: value %s pi/4, no term at gcd in %s"
          % (" ".join("%+d %s" % (c, n) for c, n in zip(vec, NAMES) if c != 0),
             vec[0] + vec[2], sorted(S)))
