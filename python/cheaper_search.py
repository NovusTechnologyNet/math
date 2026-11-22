"""Step E: exhaustive search of the space of all pi patterns for the cheapest one.

Run:  python cheaper_search.py <patterns file written by cheaper_formula.py>

The space V of rational patterns (period 120) whose series is a rational multiple of
pi has dimension 8. The cost of a pattern depends only on which of its 120 entries are
zero, so the cheapest pattern is found by walking through every subspace of V that is
cut out by setting entries to zero ("flats"), and scoring a generic member of each.
"""
import pickle
import sys
import time
from fractions import Fraction
from math import gcd

from mpmath import mp, mpf, pi, atan

N = 120
UNITS = [c for c in range(1, N) if gcd(c, N) == 1]


def reduce_rows(rows):
    """Row echelon basis of the span of rows (exact). Each row has 121 entries: pattern + q."""
    rows = [list(r) for r in rows]
    out = []
    for c in range(N + 1):
        p = next((i for i, r in enumerate(rows) if r[c] != 0), None)
        if p is None:
            continue
        piv = rows.pop(p)
        inv = 1 / piv[c]
        piv = [v * inv for v in piv]
        rows = [[v - r[c] * u for v, u in zip(r, piv)] if r[c] != 0 else r for r in rows]
        out = [[v - r[c] * u for v, u in zip(r, piv)] if r[c] != 0 else r for r in out]
        out.append(piv)
    return out


def cut(rows, k):
    """Subspace of span(rows) with entry k equal to zero."""
    p = next(i for i, r in enumerate(rows) if r[k] != 0)
    piv = rows[p]
    out = []
    for i, r in enumerate(rows):
        if i == p:
            continue
        if r[k] != 0:
            f = r[k] / piv[k]
            r = [v - f * u for v, u in zip(r, piv)]
        out.append(r)
    return out


def zero_set(rows):
    return frozenset(k for k in range(N) if all(r[k] == 0 for r in rows))


def level_table(zeros):
    out = {}
    for c in UNITS:
        s = 1
        while s * c % N in zeros:
            s += 1
        out[c] = s
    return out


def cost_of(zeros):
    return sum(Fraction(1, s) for s in level_table(zeros).values()) / len(UNITS)


def generic(rows):
    """A member of the subspace with no accidental zero and q != 0 if possible."""
    zeros = zero_set(rows)
    mult = 1
    while True:
        v = [sum((mult ** i) * r[k] for i, r in enumerate(rows)) for k in range(N + 1)]
        if all(v[k] != 0 for k in range(N) if k not in zeros) and (v[N] != 0 or all(r[N] == 0 for r in rows)):
            return v
        mult += 1


def pattern_from_terms(fn):
    """Pattern rho(k mod 120) from a function giving the k-th coefficient of 2^(-floor(k/2))/k."""
    return [Fraction(fn(k if k else N)) for k in range(N)]


def in_span(rows, v):
    red = reduce_rows(rows)
    v = list(v)
    for r in red:
        c = next(i for i, x in enumerate(r) if x != 0)
        if v[c] != 0:
            f = v[c] / r[c]
            v = [a - f * b for a, b in zip(v, r)]
    return not any(v[:N])


def ramanujan(n, k):
    """Ramanujan sum c_n(k) = sum over d | gcd(n, k) of mu(n/d) * d."""
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


def im_re(k):
    """(Im, Re) of t^(-k) * 2^floor(k/2), exact rationals."""
    re, im = Fraction(1), Fraction(0)
    for _ in range(k):                       # multiply by t^-1 = (1 - i)/2
        re, im = (re + im) / 2, (im - re) / 2
    scale = Fraction(2) ** (k // 2)
    return im * scale, re * scale


def euler_pattern(c):
    """Euler's series plus c times the reviewer's logarithm-type zero series."""
    def term(k):
        e = -2 * ramanujan(6, k) + ramanujan(10, k) - (-1) ** k
        b = ramanujan(10, k) - (-1) ** k - ramanujan(6, k) - 1
        im, re = im_re(k)
        return -(e * im + c * b * re)
    return pattern_from_terms(term)


def series_value(rho):
    total, k = mpf(0), 1
    while k // 2 <= mp.prec + 40:
        r = rho[k % N]
        if r:
            total += mpf(r.numerator) / r.denominator / (mpf(k) * mpf(2) ** (k // 2))
        k += 1
    return total


def show(pat, label):
    zeros = frozenset(k for k in range(N) if pat[k] == 0)
    lv = level_table(zeros)
    cst = cost_of(zeros)
    hist = {}
    for s in lv.values():
        hist[s] = hist.get(s, 0) + 1
    val = series_value(pat) / pi
    print("   %-34s value/pi = %-22s mean(1/s) = %-7s = %.4f  state %.3f bits/bit  terms %3d/120  levels %s"
          % (label, mp.nstr(val, 15), cst, float(cst), 2.88539 * float(cst), N - len(zeros), dict(sorted(hist.items()))))
    return cst


def main():
    mp.dps = 60
    pats, qs = pickle.load(open(sys.argv[1], "rb"))
    rows = [list(p) + [q] for p, q in zip(pats, qs)]
    rows = reduce_rows(rows)
    print("E. the space V of all rational patterns for (rational) * pi: dimension %d" % len(rows))
    classes = {}
    for k in range(N):
        col = tuple(r[k] for r in rows)
        if any(col):
            lead = next(x for x in col if x != 0)
            classes.setdefault(tuple(x / lead for x in col), []).append(k)
    print("   entries that are zero for every pattern: %d;  distinct conditions 'entry = 0': %d"
          % (len(zero_set(rows)), len(classes)))

    print("   known formulas, as members of V:")
    for label, pat in (("Euler 2atan(1/3)+atan(1/7)", euler_pattern(0)),
                       ("reviewer's variant (c = -2)", euler_pattern(-2))):
        assert in_span(rows, pat), label + " is not in V"
        show(pat, label)

    # ---- all flats
    t0 = time.time()
    start = zero_set(rows)
    seen = {start: rows}
    frontier = [start]
    best = None
    count_pi = 0
    while frontier:
        nxt = []
        for z in frontier:
            sub = seen[z]
            if any(r[N] != 0 for r in sub):
                count_pi += 1
                c = cost_of(z)
                if best is None or c < best[0]:
                    best = (c, [z])
                elif c == best[0]:
                    best[1].append(z)
            if len(sub) == 1:
                continue
            tried = set()
            for k in range(N):
                if k in z or k in tried:
                    continue
                child = cut(sub, k)
                cz = zero_set(child)
                tried |= cz
                if cz not in seen:
                    seen[cz] = child
                    nxt.append(cz)
        frontier = nxt
        print("   ... %d flats so far, %d carry pi, best mean(1/s) %.4f  [%.0fs]"
              % (len(seen), count_pi, float(best[0]), time.time() - t0), flush=True)
    print("   all %d flats examined; %d of them carry pi." % (len(seen), count_pi))
    print("   BEST: mean(1/s) = %s = %.4f  (Euler: 1/3 = 0.3333);  attained by %d flat(s)"
          % (best[0], float(best[0]), len(best[1])))
    out = []
    for z in best[1]:
        sub = seen[z]
        v = generic(sub)
        scale = Fraction(1, 4) / v[N] if v[N] != 0 else 1
        pat = [x * scale for x in v[:N]]
        show(pat, "best (dimension %d)" % len(sub))
        out.append((len(sub), pat, [r[:] for r in sub]))
    with open(sys.argv[2] if len(sys.argv) > 2 else "best_patterns.pkl", "wb") as fh:
        pickle.dump(out, fh)


if __name__ == "__main__":
    main()
