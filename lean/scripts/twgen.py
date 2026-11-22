from sympy import Symbol, Poly, cyclotomic_poly, expand, div
import os
HERE = os.path.dirname(os.path.abspath(__file__))
os.makedirs(os.path.join(HERE, "generated"), exist_ok=True)
z = Symbol('z')
phi = Poly(cyclotomic_poly(24, z), z)
table = [(0,0),(0,3),(6,3),(0,0),(0,3),(0,-3),(0,0),(0,3),(0,9),(0,0),(-6,-3),(0,-3),(0,0),(0,3),(-6,3),(0,0),(0,-9),(0,-3),(0,0),(0,3),(0,-3),(0,0),(6,-3),(0,-3)]
def lean_poly(q, var):
    terms = [(int(c), d) for (d,), c in sorted(q.terms(), reverse=True) if int(c) != 0]
    if not terms: return "0"
    s = ""
    for i, (c, d) in enumerate(terms):
        mon = "1" if d == 0 else (var if d == 1 else "%s ^ %d" % (var, d))
        a = abs(c)
        body = mon if (a == 1 and d != 0) else ("%d" % a if d == 0 else "%d * %s" % (a, mon))
        s += (("-" if c < 0 else "") + body) if i == 0 else (" %s %s" % ("-" if c < 0 else "+", body))
    return s
lines = []
for r in range(24):
    ex = [r % 24, 5 * r % 24, 13 * r % 24, 17 * r % 24, 4 * r % 24, 20 * r % 24]
    expr = (z**2 - z**10) * (z**ex[0] - z**ex[1] + z**ex[2] - z**ex[3] + z**ex[4] - z**ex[5])
    a, b = table[r]
    rhs = a + b * z**6
    q, rem = div(Poly(expand(expr - rhs), z), phi)
    assert rem.is_zero, r
    lines.append("  · linear_combination (%s) * cyc24" % lean_poly(q, "z24"))
open(os.path.join(HERE, "generated", "tw_cases.lean"), "w", encoding="utf-8").write("\n".join(lines))
print("ok", len(lines))
