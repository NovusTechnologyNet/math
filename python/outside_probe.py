"""Theory-free probe of the families F_n outside F = F_2.

    F_n :  S(rho) = sum over k >= 1 of  rho(k) * 2^(-floor(k/n)) / k,   rho rational, period P.

Run:  python outside_probe.py <n> <P> [bits per entry, default 28]
(needs python-flint and numpy on PYTHONPATH; no sympy)

For the residue-class sums  S_j = sum over k = j (mod P) of 2^(-floor(k/n))/k  this
finds, by lattice reduction (LLL), EVERY integer relation with small coefficients among
pi, S_1, ..., S_P.  A relation  c*pi + sum rho_j S_j = 0  is exactly a rational pattern
rho whose series equals (-c)*pi, so the relations found are a basis of the space
V_n(P) of all period-P patterns with value in Q*pi.  Nothing about roots of unity,
Baker's theorem or prime ideals is used.

Then:
  * each relation is re-checked at higher precision;
  * the "sub-series lemma" is tested: the part of the pattern on k = 0 (mod n1), with
    n1 = n/2 (n even) or n (n odd), must carry the whole value, the rest must sum to 0;
  * the cheapest pattern with non-zero pi is found by vertex enumeration.
    cost = n * mean(1/s) over classes of primes; F_2's best is 0.5833, Euler's 0.6667.
"""
import itertools
import sys
import time
from fractions import Fraction
from math import gcd

import numpy as np
from flint import fmpz_mat
from mpmath import mp, mpf, pi as MP_PI


def class_sums(n, P, W):
    """S_j * 2^W as integers, j = 1..P (index j-1; j = P is the class k = 0 mod P)."""
    acc = [0] * P
    k = 1
    while k // n <= W + 8:
        acc[(k - 1) % P] += (1 << (W - k // n + 64)) // k
        k += 1
    return [a >> 64 for a in acc]


def relations(n, P, bits_per):
    Wc = bits_per * (P + 1) + 256                 # precision used in the lattice
    W = Wc + 256                                  # precision used for the re-check
    mp.prec = W + 64
    S = class_sums(n, P, W)
    PI = int(mp.floor(MP_PI * mpf(2) ** W))
    vals = [PI] + S
    t0 = time.time()
    rows = []
    for i, v in enumerate(vals):
        row = [0] * (P + 2)
        row[i] = 1
        row[P + 1] = v >> (W - Wc)
        rows.append(row)
    red = fmpz_mat(rows).lll()
    out, norms = [], []
    for i in range(P + 1):
        row = [int(red[i, j]) for j in range(P + 2)]
        norm2 = sum(c * c for c in row)
        norms.append(norm2)
        coef = row[:P + 1]
        resid = abs(sum(c * v for c, v in zip(coef, vals)))
        # a true relation leaves only rounding noise at the higher precision
        if resid < (sum(abs(c) for c in coef) + 1) << 80:
            out.append(coef)
    norms.sort()
    small = len(out)
    gap_lo = norms[small - 1] if small else 0
    gap_hi = norms[small] if small < len(norms) else None
    print("n = %d, P = %d: %d entries, %d bits each; LLL %.0f s" % (n, P, P + 1, Wc, time.time() - t0))
    print("  relations found: %d   (largest squared length among them %s; smallest non-relation %s)"
          % (small, gap_lo, "about 2^%d" % (gap_hi.bit_length() - 1) if gap_hi else "-"))
    return out, vals, W


def rref(rows, ncols):
    rows = [[Fraction(x) for x in r] for r in rows]
    piv, r = [], 0
    for c in range(ncols):
        p = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        inv = 1 / rows[r][c]
        rows[r] = [v * inv for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [v - f * u for v, u in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    return rows[:r], piv


def levels(pat, n, P):
    """First multiplier s with a non-zero entry, for each class of primes mod P."""
    out = {}
    for c in range(1, P):
        if gcd(c, P) != 1:
            continue
        s = 1
        while pat[(s * c - 1) % P] == 0:
            s += 1
            if s > 4 * P:
                return None
        out[c] = s
    return out


def cost(pat, n, P):
    lv = levels(pat, n, P)
    if lv is None:
        return None
    return n * sum(Fraction(1, s) for s in lv.values()) / len(lv)


def best_vertex(rels, n, P, cap=3_000_000):
    """Cheapest pattern with non-zero pi in the span of the relations (vertex enumeration)."""
    # rows: pattern (P entries) then q = -coefficient of pi
    rows = [[Fraction(c) for c in r[1:]] + [Fraction(-r[0])] for r in rels]
    rows, _ = rref(rows, P + 1)
    dim = len(rows)
    if not any(r[P] != 0 for r in rows):
        return None, dim, 0
    classes = {}
    for k in range(P):
        col = tuple(r[k] for r in rows)
        if any(col):
            lead = next(x for x in col if x != 0)
            classes.setdefault(tuple(x / lead for x in col), []).append(k)
    reps = [ks[0] for ks in classes.values()]
    ncls = len(reps)
    if dim == 1:
        v = rows[0]
        return (cost(v[:P], n, P), [v]), dim, ncls
    total = 1
    for i in range(dim - 1):
        total = total * (ncls - i) // (i + 1)
    if total > cap:
        print("  vertex enumeration skipped: C(%d, %d) = %d candidates" % (ncls, dim - 1, total))
        return "skipped", dim, ncls
    cls_of = {k: i for i, ks in enumerate(classes.values()) for k in ks}
    cols = np.array([[float(r[k]) for r in rows] for k in reps])
    cols /= np.linalg.norm(cols, axis=1, keepdims=True)
    qvec = np.array([float(r[P]) for r in rows])
    qvec /= np.linalg.norm(qvec)
    units = [c for c in range(1, P) if gcd(c, P) == 1]
    smax = 4 * P
    seq = np.full((len(units), smax), -1, dtype=np.int64)
    for i, c in enumerate(units):
        for s in range(1, smax + 1):
            seq[i, s - 1] = cls_of.get((s * c - 1) % P, -1)
    best, best_sets = 1e9, []
    combos = itertools.combinations(range(ncls), dim - 1)
    while True:
        chunk = np.fromiter(itertools.chain.from_iterable(itertools.islice(combos, 100000)), dtype=np.int64)
        if chunk.size == 0:
            break
        chunk = chunk.reshape(-1, dim - 1)
        m = cols[chunk]
        a = np.empty((len(chunk), dim))
        for i in range(dim):
            a[:, i] = (-1) ** i * np.linalg.det(np.delete(m, i, axis=2))
        norm = np.linalg.norm(a, axis=1)
        ok = norm > 1e-9
        a = a[ok] / norm[ok, None]
        a = a[np.abs(a @ qvec) > 1e-7]
        if len(a) == 0:
            continue
        zero = np.abs(a @ cols.T) < 1e-7
        zero = np.concatenate([zero, np.ones((len(a), 1), dtype=bool)], axis=1)
        level = np.zeros((len(a), len(units)))
        alive = np.ones((len(a), len(units)), dtype=bool)
        for s in range(1, smax + 1):
            z = zero[:, seq[:, s - 1]]
            hit = alive & ~z
            level[hit] = s
            alive &= z
            if not alive.any():
                break
        level[alive] = np.inf
        cst = n * (1.0 / level).mean(axis=1)
        lo = cst.min()
        if lo < best - 1e-12:
            best, best_sets = lo, []
        if abs(lo - best) < 1e-12:
            for i in np.nonzero(np.abs(cst - lo) < 1e-12)[0][:4]:
                best_sets.append(tuple(np.nonzero(zero[i, :ncls])[0]))
    # exact recomputation of one winner
    winners = []
    for zs in sorted(set(best_sets))[:3]:
        sub = rows
        for idx in zs:
            k = reps[idx]
            if any(r[k] != 0 for r in sub):
                p = next(i for i, r in enumerate(sub) if r[k] != 0)
                piv = sub[p]
                sub = [[v - (r[k] / piv[k]) * u for v, u in zip(r, piv)] for i, r in enumerate(sub) if i != p]
        if len(sub) == 1 and sub[0][P] != 0:
            winners.append(sub[0])
    exact = min((cost(w[:P], n, P) for w in winners), default=None)
    return (exact if exact is not None else best, winners), dim, ncls


def main():
    n, P = int(sys.argv[1]), int(sys.argv[2])
    bits_per = int(sys.argv[3]) if len(sys.argv) > 3 else 28
    assert P % n == 0
    rels, vals, W = relations(n, P, bits_per)
    n1 = n // 2 if n % 2 == 0 else n
    with_pi = [r for r in rels if r[0] != 0]
    print("  relations that involve pi: %d of %d" % (len(with_pi), len(rels)))
    odd_support = 0
    worst_inv = worst_tw = 0
    for r in rels:
        inv = r[0] * vals[0] + sum(c * vals[j] for j, c in enumerate(r[1:], start=1) if j % n1 == 0)
        tw = sum(c * vals[j] for j, c in enumerate(r[1:], start=1) if j % n1 != 0)
        if any(c for j, c in enumerate(r[1:], start=1) if j % n1 != 0):
            odd_support += 1
        worst_inv = max(worst_inv, abs(inv))
        worst_tw = max(worst_tw, abs(tw))
    print("  basis relations with entries off the classes k = 0 (mod %d): %d" % (n1, odd_support))
    print("  sub-series lemma: largest |value on k = 0 (mod %d) minus whole value| = 2^%d, "
          "largest |rest| = 2^%d   (relative to 2^0; noise level is about 2^%d)"
          % (n1, worst_inv.bit_length() - W, worst_tw.bit_length() - W, 90 - W))
    # split every relation into its part on k = 0 (mod n1) (with the pi term) and the rest
    noise = 1 << 100
    inv_part, tw_part = [], []
    split_ok = True
    for r in rels:
        a = [r[0]] + [c if j % n1 == 0 else 0 for j, c in enumerate(r[1:], start=1)]
        b = [0] + [c if j % n1 != 0 else 0 for j, c in enumerate(r[1:], start=1)]
        if abs(sum(c * v for c, v in zip(a, vals))) > noise * (sum(map(abs, a)) + 1):
            split_ok = False
        inv_part.append(a)
        tw_part.append(b)
    d_inv = len(rref(inv_part, P + 1)[0]) if inv_part else 0
    d_tw = len(rref(tw_part, P + 1)[0]) if tw_part else 0
    print("  splitting: every relation = (relation on k = 0 mod %d) + (relation on the other classes, no pi): %s"
          % (n1, split_ok))
    print("  dimensions: on k = 0 (mod %d): %d   [an F_%d space of period %d];   on the other classes: %d   (new, value 0)"
          % (n1, d_inv, 2 if n % 2 == 0 else 1, P // n1 * (1 if n % 2 == 0 else 1), d_tw))
    if d_tw:
        tw_rows, _ = rref(tw_part, P + 1)
        ex = min(tw_rows, key=lambda v: sum(1 for c in v if c))
        nz = [(k, ex[k]) for k in range(1, P + 1) if ex[k]]
        print("    a new zero series (%d non-zero entries; k: coefficient): %s%s"
              % (len(nz), ", ".join("%d: %s" % kv for kv in nz[:14]), " ..." if len(nz) > 14 else ""))
    res, dim, ncls = best_vertex(rels, n, P, cap=8_000_000)
    print("  space V_%d(%d): dimension %d, distinct conditions 'entry = 0': %d" % (n, P, dim, ncls))
    if res == "skipped" and split_ok:
        # entries off k = 0 (mod n1) can only add terms, so the optimum is attained on the first part
        res, dim2, ncls2 = best_vertex(inv_part, n, P, cap=8_000_000)
        print("  optimum taken over the part on k = 0 (mod %d) (dimension %d, %d conditions); "
              "the other part cannot lower any cost" % (n1, dim2, ncls2))
    if res is None:
        print("  NO pattern of this period gives a non-zero rational multiple of pi.")
    elif res == "skipped":
        pass
    else:
        c, winners = res
        print("  cheapest pattern with non-zero pi: cost = %s = %.4f   (F_2 best 0.5833, Euler 0.6667)"
              % (c, float(c)))
        for w in winners[:1]:
            nz = [(k + 1, str(w[k])) for k in range(P) if w[k] != 0]
            print("    value %s * pi; %d non-zero entries; residues used mod %d: %s"
                  % (w[P], len(nz), n1, sorted({k % n1 for k, _ in nz})))


if __name__ == "__main__":
    main()
