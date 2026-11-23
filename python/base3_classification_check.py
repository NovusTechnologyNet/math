"""Numerical check of the classification of base-3 formulas (Theorem C3 in full).

    python base3_classification_check.py        (needs mpmath)

The Lean file lean/Pilean/Base3/Dimension.lean proves: a rational periodic pattern rho has
S(rho) = sum_{k>=1} rho(k) 3^(-floor(k/2)) / k equal to an algebraic multiple of pi if and only
if rho = a G + b Z1 + c Z2, and then S(rho) = a pi sqrt(3), where (for k = 1, ..., 12)

    G  = (6, 0, -6, 0, 6, 0, -6, 0, 6, 0, -6, 0)        the Gregory series,
    Z1 = (0, 1, -2, 0, 1, 4, 0, 3, 2, 4, -1, 0)         a zero relation,
    Z2 = (1, -3, -4, -3, 1, 0, -1, 3, 4, 3, -1, 0)      a zero relation.

This script checks the three values to 60 digits, and that the auxiliary patterns of the proof
(H with S = pi sqrt(3)/3 and F with S = 0) are H = G/3 - Z2 and F = Z2 - 2 Z1. It is a check
of the statement, independent of the Lean proof.
"""
from fractions import Fraction

from mpmath import mp, mpf, pi, sqrt

mp.dps = 70

G = [6, 0, -6, 0, 6, 0, -6, 0, 6, 0, -6, 0]
Z1 = [0, 1, -2, 0, 1, 4, 0, 3, 2, 4, -1, 0]
Z2 = [1, -3, -4, -3, 1, 0, -1, 3, 4, 3, -1, 0]
H = [1, 3, 2, 3, 1, 0, -1, -3, -2, -3, -1, 0]
F = [1, -5, 0, -3, -1, -8, -1, -3, 0, -5, 1, 0]


def series(pattern, terms=400):
    total = mpf(0)
    n = len(pattern)
    for k in range(1, terms + 1):
        r = pattern[(k - 1) % n]
        if r:
            total += mpf(r) / (mpf(3) ** (k // 2) * k)
    return total


if __name__ == "__main__":
    tol = mpf(10) ** (-60)
    assert abs(series(G) - pi * sqrt(3)) < tol
    assert abs(series(Z1)) < tol
    assert abs(series(Z2)) < tol
    assert abs(series(H) - pi * sqrt(3) / 3) < tol
    assert abs(series(F)) < tol
    assert all(Fraction(H[i]) == Fraction(G[i], 3) - Z2[i] for i in range(12))
    assert all(F[i] == Z2[i] - 2 * Z1[i] for i in range(12))
    # the two zero relations found earlier by lattice reduction lie in the span of Z1, Z2
    old1 = [1, 0, -10, -3, 4, 12, -1, 12, 10, 15, -4, 0]
    assert all(old1[i] == 3 * Z1[i] + Z2[i] for i in range(12))
    print("S(G)  - pi sqrt(3)   = %s" % mp.nstr(series(G) - pi * sqrt(3), 5))
    print("S(Z1)                = %s" % mp.nstr(series(Z1), 5))
    print("S(Z2)                = %s" % mp.nstr(series(Z2), 5))
    print("S(H)  - pi sqrt(3)/3 = %s" % mp.nstr(series(H) - pi * sqrt(3) / 3, 5))
    print("S(F)                 = %s" % mp.nstr(series(F), 5))
    print("checked: H = G/3 - Z2, F = Z2 - 2 Z1, and (1, 0, -10, ...) = 3 Z1 + Z2")
