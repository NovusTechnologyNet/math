# Generates the certificate part of lean/Pilean/PiFormula/TheoremD.lean (milestone M8):
#   * namedComb_at_m : the value of a combination of the eight named patterns at k = m;
#   * coords_p8, coords_p12, coords_p24, coords_p40, coords_p60 : what period g forces on the
#     coordinates of a zero relation;
#   * coords_even : what "zero relation supported on even k" forces;
#   * coords_D : what "no term at gcd(k, 120) < 4" forces (Theorem D);
#   * coords_Dall : the same hypothesis, all seven consequences (the sharp form).
#
#   python lean/scripts/baileygen.py > fragment.lean
#
# Every certificate is a linear combination of a few equations; Lean checks it with
# `linear_combination`, and checks the values of the patterns with `decide +kernel`.
import sys, io, math, cmath
import sympy as sp


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
NAMES = ["namedA1", "namedA6", "namedA10", "namedL6", "namedL8", "namedL10", "namedL24",
         "namedTW"]


def row(k):
    return [sp.Rational(int(round(named2[i](k))), 2) for i in range(8)]


VAL = [1, 0, 1, 0, 0, 0, 0, 0]


def E(i):
    v = [0] * 8
    v[i] = 1
    return v


S46 = [0, 0, 0, 0, 1, 0, 1, 0]
CASES = [
    ("p8", 8, [E(0), E(1), E(2), E(3), E(5), E(6), E(7)]),
    ("p12", 12, [E(0), E(1), E(2), E(3), E(5), E(7), S46]),
    ("p24", 24, [E(0), E(2), E(5)]),
    ("p40", 40, [E(1), E(3), E(6), E(7)]),
    ("p60", 60, [E(0), E(1), E(2), E(3), E(5), E(7), S46]),
    ("even", None, [E(0), E(1), E(2), E(3), E(5), E(7), S46]),
    ("D", None, [VAL]),
    ("Dall", None, [E(0), E(1), E(2), E(3), E(7), [0, 0, 0, 0, 1, 1, 0, 0],
                    [0, 0, 0, 0, 1, 0, 2, 0]]),
]
NOVAL = ("D", "Dall")


def q(x):
    x = sp.Rational(x)
    if x.q == 1:
        return "%d" % x.p if x.p >= 0 else "(%d)" % x.p
    return "(%d / %d)" % (x.p, x.q)


def linform(v):
    ts = ["%s * q %d" % (q(c), i) for i, c in enumerate(v) if c != 0]
    if not ts:
        return "0"
    if len(ts) > 4:
        return " + ".join(ts[:4]) + "\n      + " + " + ".join(ts[4:])
    return " + ".join(ts)


def target(t):
    ts = [("q %d" % i if c == 1 else "%s * q %d" % (q(c), i)) for i, c in enumerate(t)
          if c != 0]
    return " + ".join(ts) + " = 0"


plans = []
allm = set()
for name, g, targets in CASES:
    if name == "even":
        cand = [("at", k) for k in range(1, 120, 2)]
    elif name in NOVAL:
        cand = [("at", k) for k in range(1, 121) if math.gcd(k, 120) < 4]
    else:
        cand = [("per", k) for k in range(1, 121)]

    def vec(e):
        kind, k = e
        if kind == "at":
            return row(k)
        return [a - b for a, b in zip(row(k + g), row(k))]

    rows = [] if name in NOVAL else [VAL]
    chosen = [] if name in NOVAL else [("val", 0)]

    def ok(rs):
        return bool(rs) and sp.Matrix(rs + targets).rank() == sp.Matrix(rs).rank()

    for e in cand:
        if ok(rows):
            break
        v = vec(e)
        if sp.Matrix(rows + [v]).rank() > (sp.Matrix(rows).rank() if rows else 0):
            rows.append(v)
            chosen.append(e)
    assert ok(rows)
    M = sp.Matrix(rows)
    sols = []
    for t in targets:
        y = sp.symbols("y0:%d" % len(rows))
        eqs = [sum(y[i] * M[i, j] for i in range(len(rows))) - t[j] for j in range(8)]
        s = sp.solve(eqs, y, dict=True)[0]
        sols.append([s.get(v, 0) for v in y])
    for kind, k in chosen:
        if kind == "at":
            allm.add(k)
        elif kind == "per":
            allm.add(k)
            allm.add(k + g)
    plans.append((name, g, targets, chosen, sols))

out = io.StringIO()
w = out.write
w("/-! ## 2. Values of a combination at particular `k` (generated) -/\n\n")
for m in sorted(allm):
    r = row(m)
    w("theorem namedComb_at_%d (q : Fin 8 → ℚ) :\n    namedComb q %d = %s := by\n"
      % (m, m, linform(r)))
    conj = " ∧ ".join("%s %d = %s" % (NAMES[i], m, q(r[i])) for i in range(8))
    # wrap the conjunction
    parts = conj.split(" ∧ ")
    lines = []
    cur = "  have h :"
    for i, p in enumerate(parts):
        piece = " " + p + (" ∧" if i < len(parts) - 1 else " := by")
        if len(cur) + len(piece) > 98:
            lines.append(cur)
            cur = "     " + piece
        else:
            cur += piece
    lines.append(cur)
    w("\n".join(lines) + "\n    decide +kernel\n")
    w("  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h\n")
    w("  simp only [namedComb, h0, h1, h2, h3, h4, h5, h6, h7]\n  ring\n\n")

w("/-! ## 3. What each condition forces on the coordinates (generated) -/\n\n")
for name, g, targets, chosen, sols in plans:
    concl = " ∧ ".join(target(t) for t in targets)
    if name == "D":
        w("/-- No term at `gcd(k, 120) < 4` forces `q 0 + q 2 = 0`, that is, the value 0. -/\n")
        w("theorem coords_D (q : Fin 8 → ℚ)\n"
          "    (h : ∀ k, Nat.gcd k 120 < 4 → namedComb q k = 0) : %s := by\n" % concl)
    elif name == "Dall":
        w("/-- No term at `gcd(k, 120) < 4` leaves one direction: `-2 L8 + 2 L10 + L24`. -/\n")
        w("theorem coords_Dall (q : Fin 8 → ℚ)\n"
          "    (h : ∀ k, Nat.gcd k 120 < 4 → namedComb q k = 0) :\n    %s := by\n" % concl)
    elif name == "even":
        w("/-- A zero relation supported on even `k` is a multiple of `namedL24 - namedL8`. -/\n")
        w("theorem coords_even (q : Fin 8 → ℚ) (hv : q 0 + q 2 = 0)\n"
          "    (h : ∀ k, k %% 2 = 1 → namedComb q k = 0) :\n    %s := by\n" % concl)
    else:
        w("/-- The coordinates of a zero relation of period %d. -/\n" % g)
        hvname = "hv" if any(s[0] != 0 for s in sols) else "_hv"
        w("theorem coords_%s (q : Fin 8 → ℚ) (%s : q 0 + q 2 = 0)\n"
          "    (h : ∀ k, namedComb q (k + %d) = namedComb q k) :\n    %s := by\n"
          % (name, hvname, g, concl))
    hyps = []
    for kind, k in chosen:
        if kind == "val":
            hyps.append("hv")
        elif kind == "at":
            hn = "e%d" % k
            w("  have %s := h %d (by decide)\n" % (hn, k))
            w("  rw [namedComb_at_%d] at %s\n" % (k, hn))
            hyps.append(hn)
        else:
            hn = "e%d" % k
            w("  have %s : namedComb q %d = namedComb q %d := h %d\n" % (hn, k + g, k, k))
            w("  rw [namedComb_at_%d, namedComb_at_%d] at %s\n" % (k + g, k, hn))
            hyps.append(hn)
    if len(targets) > 1:
        w("  refine ⟨" + ", ".join(["?_"] * len(targets)) + "⟩\n")
    for t, s in zip(targets, sols):
        terms = ["%s * %s" % (q(c), hn) for c, hn in zip(s, hyps) if c != 0]
        lc = " + ".join(terms)
        line = ("  · " if len(targets) > 1 else "  ") + "linear_combination " + lc
        if len(line) > 100:
            half = len(terms) // 2
            line = (("  · " if len(targets) > 1 else "  ") + "linear_combination "
                    + " + ".join(terms[:half]) + "\n      + " + " + ".join(terms[half:]))
        w(line + "\n")
    w("\n")
sys.stdout.buffer.write(out.getvalue().encode("utf-8"))
