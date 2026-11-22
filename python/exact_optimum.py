"""Exact (certified) search for the best binary BBP-type formulas for pi, in two measures.

Run:  python exact_optimum.py          (needs numpy and mpmath; no sympy)

V is the 8-dimensional space of rational patterns rho (period 120) with
sum_k rho(k) 2^(-floor(k/2))/k in Q*pi (Theorem C; basis in pi_space_basis_120.json).
Two costs of a pattern with non-zero pi:
  * prime measure  mean(1/s): a prime p first appears at k = s*p (s depends on p mod 120);
    per-prime state of the window algorithm = 2.885 * mean(1/s) bits per bit.
  * standard measure  terms per bit: non-zero entries per period / bits per period
    (BBP 1, Bellard 0.7 by the published count).
Both depend only on which entries are zero, and both are minimised at a "vertex": a
pattern fixed up to scale by its zero entries (if a pattern with pi has a zero set Z
and its flat has dimension >= 2, one more entry can be made zero while keeping pi).
V has 35 distinct conditions "entry = 0", so every vertex is the solution of 7 of them.

This program tries all C(35, 7) = 6,724,520 choices EXACTLY. For a choice C, let m be
the vector of signed 7x7 minors of the 7x8 integer matrix of C. Then the flat is the
line through m (if m != 0), and condition c vanishes on it iff the integer
D_c = det[C; c] = c . m is 0; the pi content is q . m. All these are integers bounded
by the Hadamard bound H, so they are computed modulo several primes whose product
exceeds H: an integer below the product that is 0 modulo every prime is 0. Modulo one
prime, m is obtained by row reduction (it is a non-zero multiple of the kernel vector
when the rank is 7 modulo that prime, and m = 0 modulo it otherwise). No floating
point is used anywhere in the decisions.
"""
import itertools
import json
import os
import sys
import time
from fractions import Fraction
from math import gcd, lcm, isqrt

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
N = 120
UNITS = [c for c in range(1, N) if gcd(c, N) == 1]
SMAX = 40
LSCORE = lcm(*range(1, SMAX + 1))          # cost * 32 * LSCORE is an integer


def load():
    d = json.load(open(os.path.join(HERE, "pi_space_basis_120.json")))
    pats = [[Fraction(x) for x in p] for p in d["patterns"]]
    qs = [Fraction(x) for x in d["pi_content"]]
    return pats, qs


def primitive(vec):
    L = lcm(*[x.denominator for x in vec])
    iv = [int(x * L) for x in vec]
    g = 0
    for x in iv:
        g = gcd(g, x)
    iv = [x // g for x in iv]
    if next(x for x in iv if x) < 0:
        iv = [-x for x in iv]
    return iv


def is_prime(n):
    if n < 2:
        return False
    for d in range(2, isqrt(n) + 1):
        if n % d == 0:
            return False
    return True


def primes_below(top, count):
    out, n = [], top
    while len(out) < count:
        n -= 1
        if is_prime(n):
            out.append(n)
    return out


def inv_mod(x, p):
    r = np.ones_like(x)
    b = x % p
    e = p - 2
    while e:
        if e & 1:
            r = (r * b) % p
        b = (b * b) % p
        e >>= 1
    return r


def kernel_mod_p(A, p):
    """A: (B, 7, 8) residues mod p. Returns (rank7 mask, v) with v a kernel vector of
    each rank-7 matrix (v = 0 for the others)."""
    A = A.copy()
    Bn, R, C = A.shape
    rptr = np.zeros(Bn, dtype=np.int64)
    pivcol = np.full((Bn, R), -1, dtype=np.int64)
    ar = np.arange(Bn)
    rows = np.arange(R)
    for col in range(C):
        mask = (A[:, :, col] != 0) & (rows[None, :] >= rptr[:, None])
        has = mask.any(axis=1) & (rptr < R)
        if not has.any():
            continue
        piv = np.argmax(mask, axis=1)
        idx, pr, rr = ar[has], piv[has], rptr[has]
        top = A[idx, rr, :].copy()
        A[idx, rr, :] = A[idx, pr, :]
        A[idx, pr, :] = top
        iv = inv_mod(A[idx, rr, col], p)
        A[idx, rr, :] = (A[idx, rr, :] * iv[:, None]) % p
        prow = A[idx, rr, :]
        f = A[idx, :, col].copy()
        f[np.arange(len(idx)), rr] = 0
        A[idx] = (A[idx] - f[:, :, None] * prow[:, None, :]) % p
        pivcol[idx, rr] = col
        rptr[idx] += 1
    rank7 = rptr == R
    v = np.zeros((Bn, C), dtype=np.int64)
    good = ar[rank7]
    if len(good):
        pc = pivcol[good]
        free = (C * (C - 1) // 2) - pc.sum(axis=1)
        v[good, free] = 1
        af = A[good[:, None], np.arange(R)[None, :], free[:, None]]
        v[good[:, None], pc] = (-af) % p
    return rank7, v


def dot_mod(v, M, p):
    """(B, 8) x (8, K) modulo p without overflow."""
    out = np.zeros((v.shape[0], M.shape[1]), dtype=np.int64)
    for i in range(v.shape[1]):
        out = (out + (v[:, i:i + 1] * M[i:i + 1, :]) % p) % p
    return out


def exact_vertex(pats, qs, cls_entries, zero_classes):
    """The pattern of V vanishing on the given classes, scaled to value pi/4 (exact)."""
    d = len(pats)
    rows = [[pats[i][k] for i in range(d)] for c in zero_classes for k in cls_entries[c][:1]]
    # nullspace of rows (exact)
    rows = [list(r) for r in rows]
    piv, r = [], 0
    for col in range(d):
        p = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        inv = 1 / rows[r][col]
        rows[r] = [x * inv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                fct = rows[i][col]
                rows[i] = [a - fct * b for a, b in zip(rows[i], rows[r])]
        piv.append(col)
        r += 1
    free = [c for c in range(d) if c not in piv]
    assert len(free) == 1, "not a vertex"
    c = [Fraction(0)] * d
    c[free[0]] = Fraction(1)
    for row, pc in zip(rows, piv):
        c[pc] = -row[free[0]]
    q = sum(ci * qi for ci, qi in zip(c, qs))
    assert q != 0
    scale = Fraction(1, 4) / q
    return [sum(c[i] * pats[i][k] for i in range(d)) * scale for k in range(N)]


def measures(pat):
    zero = [pat[k] == 0 for k in range(N)]
    lv = {}
    for c in UNITS:
        s = 1
        while zero[s * c % N]:
            s += 1
        lv[c] = s
    cost = sum(Fraction(1, s) for s in lv.values()) / len(UNITS)
    terms = sum(1 for k in range(N) if not zero[k])
    return cost, Fraction(terms, 60), lv


def series_over_pi(pat, digits=60):
    from mpmath import mp, mpf, pi
    mp.dps = digits + 10
    total, k = mpf(0), 1
    while k // 2 <= mp.prec + 40:
        r = pat[k % N]
        if r:
            total += mpf(r.numerator) / r.denominator / (mpf(k) * mpf(2) ** (k // 2))
        k += 1
    return total / pi


def min_period(pat):
    for p in sorted(d for d in range(1, N + 1) if N % d == 0):
        if all(pat[k] == pat[(k + p) % N] for k in range(N)):
            return p


def bbp_form(pat):
    """Write the pattern as P(1, 2^B, n, A): pi/4 = sum_j 2^(-Bj) sum_i A_i/(nj+i), n = period."""
    n = min_period(pat)
    if n % 2:
        n *= 2
    B = n // 2
    A = [pat[i % N] / Fraction(2) ** (i // 2) for i in range(1, n + 1)]
    den = lcm(*[a.denominator for a in A])
    return B, n, den, [int(a * den) for a in A]


def known_formulas():
    """BBP 1995, Bellard 1997, Euler/Hutton (binary series), the Theorem E formula; all as
    patterns of period 120 with value pi/4."""
    out = {}
    bbp = [Fraction(0)] * 8                     # pi = sum 16^-j (4/(8j+1) - 2/(8j+4) - 1/(8j+5) - 1/(8j+6))
    for i, a in ((1, 4), (4, -2), (5, -1), (6, -1)):
        bbp[i % 8] = Fraction(a) * 2 ** (i // 2) / 4
    out["BBP 1995"] = [bbp[k % 8] for k in range(N)]
    bel = [Fraction(0)] * 40                    # Bellard, written with k = 20n + K0
    terms = [(4, 1, -2 ** 5), (4, 3, -1), (10, 1, 2 ** 8), (10, 3, -2 ** 6), (10, 5, -2 ** 2),
             (10, 7, -2 ** 2), (10, 9, 1)]
    for parity in (0, 1):
        for c, d, a in terms:
            k0 = 20 * d // c
            kk = 20 * parity + k0
            bel[kk % 40] += Fraction(a) * (-1) ** parity * Fraction(20, c) * 2 ** (k0 // 2) / 64 / 4
    out["Bellard 1997"] = [bel[k % 40] for k in range(N)]
    from cheaper_search import euler_pattern
    out["Euler/Hutton"] = euler_pattern(0)
    data = json.load(open(os.path.join(HERE, "pi_formula_120.json")))
    out["Theorem E formula"] = [Fraction(a, data["denominator"]) for a in data["numerators"]]
    return out


def in_span(pats, vec):
    d = len(pats)
    rows = [[pats[i][k] for i in range(d)] + [vec[k]] for k in range(N)]
    r = 0
    for col in range(d):
        p = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col] / rows[r][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        r += 1
    return all(row[d] == 0 for row in rows[r:])


def main():
    pats, qs = load()
    d = len(pats)
    # ---- the conditions "entry k = 0"
    classes, cls_entries = {}, {}
    ent_cls = [-1] * N
    for k in range(N):
        col = [pats[i][k] for i in range(d)]
        if not any(col):
            continue
        key = tuple(primitive(col))
        if key not in classes:
            classes[key] = len(classes)
            cls_entries[classes[key]] = []
        ent_cls[k] = classes[key]
        cls_entries[classes[key]].append(k)
    ncls = len(classes)
    conds = [list(k) for k, _ in sorted(classes.items(), key=lambda t: t[1])]
    qrow = primitive(qs)
    norms = [sum(x * x for x in c) for c in conds]
    m_bound = 1
    for nm in sorted(norms)[-7:]:
        m_bound *= nm
    m_bound = isqrt(m_bound) + 1                           # bound for every 7x7 minor
    d_bound = m_bound * (isqrt(max(max(norms), sum(x * x for x in qrow))) + 1)
    primes, prod = [], 1
    for p in primes_below(2 ** 31, 12):
        primes.append(p)
        prod *= p
        if prod > 2 * d_bound:
            break
    print("V: dimension %d; %d entries always zero; %d distinct conditions 'entry = 0'"
          % (d, ent_cls.count(-1), ncls))
    print("Hadamard bound for every determinant: 2^%d; primes used: %d (product 2^%d)"
          % (d_bound.bit_length(), len(primes), prod.bit_length()))

    sizes = np.array([len(cls_entries[c]) for c in range(ncls)], dtype=np.int64)
    seq = np.array([[ent_cls[s * c % N] for s in range(1, SMAX + 1)] for c in UNITS], dtype=np.int64)
    combos = itertools.combinations(range(ncls), d - 1)
    t0 = time.time()
    total = rank_ok = with_pi = fallback = 0
    seen = {}                                          # zero-set bitmask -> (score, terms)
    bitw = (1 << np.arange(ncls, dtype=np.uint64)).astype(np.uint64)
    conds_np = [np.array(conds, dtype=object) % p for p in primes]
    while True:
        chunk = np.fromiter(itertools.chain.from_iterable(itertools.islice(combos, 200000)), dtype=np.int64)
        if chunk.size == 0:
            break
        chunk = chunk.reshape(-1, d - 1)
        total += len(chunk)
        zero_all = np.ones((len(chunk), ncls), dtype=bool)
        qz_all = np.ones(len(chunk), dtype=bool)
        rank_any = np.zeros(len(chunk), dtype=bool)
        for p, cm in zip(primes, conds_np):
            Cm = cm.astype(np.int64)
            qm = (np.array(qrow, dtype=object) % p).astype(np.int64)
            A = Cm[chunk]                                    # (B, 7, 8)
            r7, v = kernel_mod_p(A, p)
            D = dot_mod(v, Cm.T.copy(), p)                   # (B, ncls)
            Dq = dot_mod(v, qm.reshape(-1, 1), p)[:, 0]
            zero_all &= (D == 0) | (~r7)[:, None]
            qz_all &= (Dq == 0) | ~r7
            rank_any |= r7
        rank_ok += int(rank_any.sum())
        keep = rank_any & ~qz_all
        with_pi += int(keep.sum())
        Z = zero_all[keep]
        if len(Z) == 0:
            continue
        Zx = np.concatenate([Z, np.ones((len(Z), 1), dtype=bool)], axis=1)   # column -1: always zero
        level = np.zeros((len(Z), len(UNITS)), dtype=np.int64)
        alive = np.ones((len(Z), len(UNITS)), dtype=bool)
        for s in range(1, SMAX + 1):
            z = Zx[:, seq[:, s - 1]]
            hit = alive & ~z
            level[hit] = s
            alive &= z
        if alive.any():
            fallback += int(alive.any(axis=1).sum())
            level[alive] = SMAX + 1                          # handled below, exactly
        score = (LSCORE // np.maximum(level, 1)).sum(axis=1)
        terms = (~Z).astype(np.int64) @ sizes
        keys = (Z.astype(np.uint64) * bitw).sum(axis=1)
        for kk, sc, tm, bad in zip(keys.tolist(), score.tolist(), terms.tolist(), alive.any(axis=1).tolist()):
            if kk not in seen:
                seen[kk] = (sc, tm, bad)
    print("tried %d choices in %.0f s: %d have rank 7, %d of those carry pi; %d distinct vertices with pi"
          % (total, time.time() - t0, rank_ok, with_pi, len(seen)))
    if fallback:
        print("  %d vertices needed s > %d for some class; their scores are recomputed exactly" % (fallback, SMAX))

    def zero_classes(key):
        return [c for c in range(ncls) if key >> c & 1]

    exact = {}
    for key, (sc, tm, bad) in seen.items():
        if bad:
            pat = exact_vertex(pats, qs, cls_entries, zero_classes(key))
            cost, tpb, _ = measures(pat)
            exact[key] = (cost, Fraction(tm, 60))
        else:
            exact[key] = (Fraction(sc, LSCORE * len(UNITS)), Fraction(tm, 60))

    best_cost = min(v[0] for v in exact.values())
    best_terms = min(v[1] for v in exact.values())
    print()
    print("PRIME MEASURE: minimum mean(1/s) = %s = %.6f  (state %.4f bits per bit), attained by %d vertices"
          % (best_cost, float(best_cost), 2.88539 * float(best_cost), sum(1 for v in exact.values() if v[0] == best_cost)))
    print("STANDARD MEASURE: minimum terms per bit = %s = %.6f, attained by %d vertices"
          % (best_terms, float(best_terms), sum(1 for v in exact.values() if v[1] == best_terms)))
    # Pareto front
    front = []
    for cost, tpb in sorted(set(exact.values()), key=lambda t: (t[0], t[1])):
        if not front or tpb < front[-1][1]:
            front.append((cost, tpb))
    print("trade-off (no formula is better in both measures than one of these):")
    for cost, tpb in front:
        print("   mean(1/s) = %-6s (%.4f)   terms per bit = %-6s (%.4f)" % (cost, float(cost), tpb, float(tpb)))

    print()
    print("the optimal formulas, recomputed exactly and summed to 60 digits:")
    shown = 0
    for label, target in (("prime measure", lambda v: v[0] == best_cost),
                          ("standard measure", lambda v: v[1] == best_terms)):
        keys = [k for k, v in exact.items() if target(v)]
        pats_opt = [exact_vertex(pats, qs, cls_entries, zero_classes(k)) for k in keys]
        # the best of the winners in the other measure first
        pats_opt.sort(key=lambda pt: measures(pt)[1] if label == "prime measure" else measures(pt)[0])
        for pt in pats_opt[:3]:
            cost, tpb, lv = measures(pt)
            val = series_over_pi(pt)
            B, n, den, A = bbp_form(pt)
            print("  [%s] mean(1/s) = %s, terms per bit = %s, |series/pi - 1/4| = %.1e, period %d"
                  % (label, cost, tpb, float(abs(val - 0.25)), min_period(pt)))
            print("      pi/4 = (1/%d) sum_j 2^(-%dj) sum_i A_i/(%dj+i),  A = %s" % (den, B, n, A))
        shown += 1

    print()
    print("known formulas, scored exactly (each checked to lie in V and summed to 60 digits):")
    for name, pt in known_formulas().items():
        ok = in_span(pats, pt)
        cost, tpb, lv = measures(pt)
        val = series_over_pi(pt)
        print("  %-18s in V: %-5s  series/pi = %.12f   mean(1/s) = %-6s (%.4f, state %.3f)   terms per bit = %s (%.4f)"
              % (name, ok, float(val), cost, float(cost), 2.88539 * float(cost), tpb, float(tpb)))


if __name__ == "__main__":
    main()
