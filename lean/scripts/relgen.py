# Generate Lean certificates for the 13 relations of full_class_theorem.py.
import os
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
os.makedirs(os.path.join(HERE, "generated"), exist_ok=True)
from sympy import Symbol, Poly, cyclotomic_poly, expand, div
RELS = [
 ({0:-1,30:1}, Fraction(-1,2)),
 ({0:-2,20:1,100:1}, Fraction(-1,2)),
 ({0:-2,15:1,75:1}, Fraction(-1,2)),
 ({0:-3,12:1,36:1,60:-1,84:1,108:1}, Fraction(-1,2)),
 ({10:1,20:-1}, Fraction(1,3)),
 ({0:-2,20:1,50:1}, Fraction(-5,6)),
 ({12:-4,18:4,60:1,90:-1}, Fraction(-11,10)),
 ({0:-12,12:4,36:4,42:4,60:-3,84:4,90:-1}, Fraction(-39,10)),
 ({60:1,66:4,84:-4,90:-1}, Fraction(-7,10)),
 ({36:-4,60:1,90:-1,114:4}, Fraction(17,10)),
 ({5:-2,25:2,45:1,105:-1}, Fraction(-4,3)),
 ({0:-2,5:2,45:-1,65:2,105:-1}, Fraction(-1,6)),
 ({0:-1,5:1,45:-1,85:1}, Fraction(1,4)),
]
z = Symbol('z')
out = []
out_content = [str(c) for _, c in RELS]
for idx, (e, content) in enumerate(RELS, 1):
    m = int(content * 60) % 120
    g = 6 if all(j % 6 == 0 for j in e) and m % 6 == 0 else 5
    assert all(j % g == 0 for j in e) and m % g == 0 and 30 % g == 0
    n = 120 // g
    phi = Poly(cyclotomic_poly(n, z), z)
    t = 1 + z ** (30 // g)
    total = sum(e.values())
    lhs, rhs = 1, z ** (m // g)
    for j, ej in sorted(e.items()):
        f = (t - z ** (j // g))
        if ej > 0: lhs = lhs * f ** ej
        else: rhs = rhs * f ** (-ej)
    if total > 0: rhs = rhs * t ** total
    elif total < 0: lhs = lhs * t ** (-total)
    q, r = div(Poly(expand(lhs - rhs), z), phi)
    assert r.is_zero, (idx, r)
    out.append((idx, e, m, g, n, q, total))
    print(idx, "g", g, "n", n, "m", m, "deg lhs", Poly(expand(lhs), z).degree(), "deg q", q.degree(),
          "max coeff", max(abs(c) for c in q.all_coeffs()))

def lean_poly(q, var):
    terms = []
    for (d,), c in sorted(q.terms(), reverse=True):
        c = int(c)
        if c == 0: continue
        mon = "1" if d == 0 else (var if d == 1 else "%s ^ %d" % (var, d))
        terms.append((c, mon))
    s = ""
    for i, (c, mon) in enumerate(terms):
        sign = "-" if c < 0 else "+"
        a = abs(c)
        body = mon if a == 1 and mon != "1" else ("%d" % a if mon == "1" else "%d * %s" % (a, mon))
        if i == 0:
            s = ("-" if c < 0 else "") + body
        else:
            s += " %s %s" % (sign, body)
    return s if s else "0"

def factor(j):
    return "(tC - 1)" if j == 0 else "(tC - ζ120 ^ %d)" % j

def prod_str(items):
    parts = []
    for j, ex in items:
        f = factor(j)
        parts.append(f if ex == 1 else "%s ^ %d" % (f, ex))
    return " * ".join(parts) if parts else "1"

lines = []
for idx, e, m, g, n, q, total in out:
    var = "z20" if g == 6 else "z24"
    cyc = "cyc20" if g == 6 else "cyc24"
    pos = [(j, ej) for j, ej in sorted(e.items()) if ej > 0]
    neg = [(j, -ej) for j, ej in sorted(e.items()) if ej < 0]
    L = prod_str(pos)
    R = prod_str(neg)
    if total < 0: L = L + " * tC ^ %d" % (-total) if L != "1" else "tC ^ %d" % (-total)
    if total > 0: R = R + " * tC ^ %d" % total if R != "1" else "tC ^ %d" % total
    root = "ζ120 ^ %d" % m
    desc = " ".join(("%+d[%d]" % (ej, j)) for j, ej in sorted(e.items()))
    lines.append("/-- Relation %d: `%s`, `∑ e Log w = %s · iπ`. -/" % (idx, desc, out_content[idx-1]))
    lines.append("theorem relation_%d :" % idx)
    lines.append("    %s =" % L)
    lines.append("      %s * %s := by" % (root, R))
    js = sorted(set([j for j in e if j != 0] + [m]))
    rws = []
    for j in js:
        k = j // g
        tgt = var if k == 1 else ("%s ^ %d" % (var, k) if k != 0 else "1")
        rws.append("show ζ120 ^ %d = %s by rw [%s, ← pow_mul]" % (j, tgt, var) if k not in (0,) else "show ζ120 ^ %d = 1 by rw [pow_zero]" % j)
    tq = "show tC = 1 + %s ^ %d by rw [tC, %s]" % (var, 30 // g, "I_" + var)
    lines.append("  rw [" + ",\n    ".join(rws + [tq]) + "]")
    lines.append("  linear_combination (%s) * %s" % (lean_poly(q, var), cyc))
    lines.append("")
open(os.path.join(HERE, "generated", "relations_body.lean"), "w", encoding="utf-8").write("\n".join(lines))
print("written", len(lines))
