import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "python"))
os.makedirs(os.path.join(HERE, "generated"), exist_ok=True)
from fractions import Fraction
import cmath
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
    v = s3 * (z24 ** k - z24 ** (5 * k) + z24 ** (13 * k) - z24 ** (17 * k) + z24 ** (4 * k) - z24 ** (20 * k))
    return complex(round(v.real), round(v.imag))
def U(k): return ngi_pow(k // 2) * (2 if k % 2 == 0 else (1 - 1j))
def A(P, k): return -(P(k) * U(k)).imag      # = 2 rho for ARG
def L(P, k): return -(P(k) * U(k)).real      # = 2 rho for LOG
one = lambda k: 1
named = [
  lambda k: A(one, k),
  lambda k: A(c6, k),
  lambda k: A(c10, k) - A(c2, k),
  lambda k: L(c6, k) - 2 * L(one, k),
  lambda k: L(p8a, k) - 2 * L(one, k),
  lambda k: L(c10, k) - L(c2, k) - 3 * L(one, k),
  lambda k: L(p24, k) - L(p8b, k) - 2 * L(one, k),
  lambda k: A(ptw, k),
]
# compare with decompose_formula NAMED (rho = N/2)
import decompose_formula as dfm
ok = True
for i, (name, pat, val) in enumerate(dfm.NAMED):
    for k in range(120):
        kk = k if k else 120
        if Fraction(named[i](kk)).limit_denominator(1000) / 2 != pat[k]:
            ok = False; print("mismatch", i, k, named[i](kk) / 2, pat[k]); break
print("all named match:", ok)
# exact ptw table for k mod 24
print("ptw table:", [ptw(k) for k in range(24)])
# choose 8 independent coordinates greedily
import sympy
rows = []
chosen = []
M = sympy.Matrix(0, 8, [])
for k in range(1, 121):
    row = [int(round(named[i](k))) for i in range(8)]
    M2 = M.col_join(sympy.Matrix([row]))
    if M2.rank() > M.rank():
        M = M2; chosen.append(k)
    if len(chosen) == 8: break
print("coords", chosen)
print("matrix", M.tolist())
print("det", M.det())
print("inverse", M.inv().tolist())

names = ["namedA1", "namedA6", "namedA10", "namedL6", "namedL8", "namedL10", "namedL24", "namedTW"]
from fractions import Fraction as Fr
vals = [[Fr(int(round(named[j](k))), 2) for j in range(8)] for k in range(1, 9)]
Mr = sympy.Matrix([[sympy.Rational(v.numerator, v.denominator) for v in row] for row in vals])
B = Mr.inv()
def q(x):
    x = sympy.Rational(x)
    return ("(%d : ℚ)" % x.p) if x.q == 1 else ("(%d / %d : ℚ)" % (x.p, x.q))
out = []
for k in range(1, 9):
    for j in range(8):
        out.append("theorem %s_at_%d : %s %d = %s := by decide" % (names[j], k, names[j], k, q(vals[k-1][j])))
out.append("")
for i in range(8):
    terms = " + ".join("%s * e%d" % (q(B[i, k]), k + 1) for k in range(8) if B[i, k] != 0)
    out.append("  · linear_combination %s" % terms)
open(os.path.join(HERE, "generated", "indep.lean"), "w", encoding="utf-8").write("\n".join(out))
print("indep written")
