# The five series with irrational values, and the 13-dimensional space of Theorem C.
#
#   python five_series_check.py
#
# Theorem C: the rational patterns rho of period 120 whose series
#     S(rho) = sum_{k>=1} rho(k) 2^(-floor(k/2)) / k
# is an algebraic multiple of pi form a space of dimension 13. Eight of the thirteen are the
# named patterns (rational multiples of pi). This script checks the other five:
#
#     S3   -pi/sqrt(3)                 sqrt(3)-twist, roots of order 6
#     S2   -sqrt(2) pi                 sqrt(2)-twist, roots of order 8 and 24
#     S5   -sqrt(5) pi                 sqrt(5)-twist, roots of order 10 and 20
#     T1   (th1 - 3 th3) pi/5          th1 = 2cos(pi/10), th3 = 2cos(3pi/10)
#     T2   (3 th1 + th3) pi/5
#
# Each is sum_j e_j arg(1 - zeta^j / t), zeta = exp(2 pi i/120), t = 1 + i, with real e_j.
# Checked here: the power sums are Gaussian integers (exactly, modulo the cyclotomic
# polynomial); each series to 40 digits; the thirteen patterns are independent (exactly);
# and in the 13-dimensional space the patterns with no term at gcd(k, 120) < 4 still form
# one line (Theorem D for algebraic multiples).
# In Lean: PiFormula.hasSum_extraS3 ... hasSum_extraT2, PiFormula.fam13_linearIndependent,
# PiFormula.finrank_algSpace, PiFormula.theoremD_alg_sharp.
import math
import os

import mpmath as mp
import sympy as sp

mp.mp.dps = 50

# The definitions (series, tables, the thirteen patterns) are those of the generator.
HERE = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(HERE, "..", "lean", "scripts", "fivegen.py")
src = open(GEN, encoding="utf-8").read().split("out = io.StringIO()")[0]
G = {}
exec(compile(src, "fivegen_defs", "exec"), G)
SERIES, gauss_table, row13, NAMES = G["SERIES"], G["gauss_table"], G["row13"], G["NAMES"]

zeta = mp.e ** (2j * mp.pi / 120)
t = mp.mpc(1, 1)


def garg(j):
    return mp.im(mp.log(1 - zeta ** j / t))


REAL = {"Real.sqrt 3": mp.sqrt(3), "Real.sqrt 2": mp.sqrt(2), "Real.sqrt 5": mp.sqrt(5),
        "th1": 2 * mp.cos(mp.pi / 10), "th3": 2 * mp.cos(3 * mp.pi / 10)}
th1, th3 = REAL["th1"], REAL["th3"]
PRED = {"S3": -mp.sqrt(3) / 3, "S2": -mp.sqrt(2), "S5": -mp.sqrt(5),
        "T1": (th1 - 3 * th3) / 5, "T2": (3 * th1 + th3) / 5}

# The two theta values are -tan(pi/10) and tan(3pi/10).
assert abs(PRED["T1"] + mp.tan(mp.pi / 10)) < mp.mpf(10) ** -40
assert abs(PRED["T2"] - mp.tan(3 * mp.pi / 10)) < mp.mpf(10) ** -40

tables = [gauss_table(n, groups) for _, n, _, groups in SERIES]
print("1. the five series (value / pi):")
for idx, ((name, n, var, groups), tab) in enumerate(zip(SERIES, tables)):
    # sum of e_j arg w_j
    val = mp.mpf(0)
    for real, _, _, terms in groups:
        for sg, a in terms:
            val += sg * REAL[real] * garg(a * (120 // n))
    # the series of the pattern, from the exact table
    pat = [row13(k, tables)[8 + idx] for k in range(0, 120)]
    ser = mp.fsum(mp.mpf(pat[k % 120].p) / pat[k % 120].q / mp.mpf(2) ** (k // 2) / k
                  for k in range(1, 500))
    assert abs(val / mp.pi - PRED[name]) < mp.mpf(10) ** -40
    assert abs(ser / mp.pi - PRED[name]) < mp.mpf(10) ** -40
    per = min(p for p in (1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120)
              if all(pat[k] == pat[(k + p) % 120] for k in range(120)))
    print("   %s  %s   pattern of period %d" % (name, mp.nstr(PRED[name], 20), per))

rows = [row13(k, tables) for k in range(1, 121)]
assert sp.Matrix(rows).rank() == 13
print("2. the thirteen patterns are linearly independent: OK")

ks = [k for k in range(1, 121) if math.gcd(k, 120) < 4]
ns = sp.Matrix([row13(k, tables) for k in ks]).nullspace()
assert len(ns) == 1
v = ns[0] * sp.ilcm(*[x.q for x in ns[0]])
print("3. no term at gcd(k,120) < 4, in the 13-dimensional space: the line spanned by",
      " ".join("%+d %s" % (c, nm) for c, nm in zip(v, NAMES) if c != 0))
