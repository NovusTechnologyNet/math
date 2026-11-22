"""Fast exhaustive search for the cheapest pi pattern (floating point, then exact check).

Run:  python cheaper_fast.py <patterns file written by cheaper_formula.py> [output file]

The cheapest pattern can be taken to be a "vertex": a pattern fixed, up to scale, by
which of its entries vanish. V has dimension 8 and only 35 distinct conditions
"entry = 0", so every vertex is the solution of 7 of those 35 conditions:
C(35, 7) = 6,724,520 candidates. All are tried in floating point; the winners are then
recomputed exactly with rational arithmetic and summed to 60 digits.
"""
import itertools
import pickle
import sys
import time
from fractions import Fraction
from math import gcd

import numpy as np
from mpmath import mp, mpf, pi

from cheaper_search import N, UNITS, reduce_rows, level_table, cost_of, series_value, show

TOL = 1e-7


def main():
    mp.dps = 60
    pats, qs = pickle.load(open(sys.argv[1], "rb"))
    rows = reduce_rows([list(p) + [q] for p, q in zip(pats, qs)])
    dim = len(rows)
    classes = {}
    for k in range(N):
        col = tuple(r[k] for r in rows)
        if any(col):
            lead = next(x for x in col if x != 0)
            classes.setdefault(tuple(x / lead for x in col), []).append(k)
    reps = [ks[0] for ks in classes.values()]
    cls_of = {}
    for idx, ks in enumerate(classes.values()):
        for k in ks:
            cls_of[k] = idx
    ncls = len(reps)
    cols = np.array([[float(r[k]) for r in rows] for k in reps])          # ncls x dim
    cols /= np.linalg.norm(cols, axis=1, keepdims=True)
    qvec = np.array([float(r[N]) for r in rows])
    qvec /= np.linalg.norm(qvec)

    # for each class of primes c, the condition met at multiplier s = 1, 2, 3, ...
    smax = 24
    seq = np.full((len(UNITS), smax), -1, dtype=np.int64)                 # -1: entry is always zero
    for i, c in enumerate(UNITS):
        for s in range(1, smax + 1):
            seq[i, s - 1] = cls_of.get(s * c % N, -1)

    t0 = time.time()
    gap = {"dependent, largest": 0.0, "independent, smallest": 1e9, "zero, largest": 0.0, "non-zero, smallest": 1e9}
    best_cost, best_sets = 10.0, []
    combos = itertools.combinations(range(ncls), dim - 1)
    total = 0
    while True:
        chunk = np.fromiter(itertools.chain.from_iterable(itertools.islice(combos, 150000)), dtype=np.int64)
        if chunk.size == 0:
            break
        chunk = chunk.reshape(-1, dim - 1)
        total += len(chunk)
        m = cols[chunk]                                                    # B x 7 x 8
        a = np.empty((len(chunk), dim))
        for i in range(dim):
            a[:, i] = (-1) ** i * np.linalg.det(np.delete(m, i, axis=2))
        norm = np.linalg.norm(a, axis=1)
        ok = norm > 1e-9
        if (~ok).any():
            gap["dependent, largest"] = max(gap["dependent, largest"], norm[~ok].max())
        gap["independent, smallest"] = min(gap["independent, smallest"], norm[ok].min())
        a = a[ok] / norm[ok, None]
        sub = chunk[ok]
        qv = np.abs(a @ qvec)
        vals = np.abs(a @ cols.T)
        both = np.concatenate([vals.ravel(), qv])
        gap["zero, largest"] = max(gap["zero, largest"], both[both < TOL].max())
        gap["non-zero, smallest"] = min(gap["non-zero, smallest"], both[both >= TOL].min())
        carries = qv > TOL
        a, sub = a[carries], sub[carries]
        if len(a) == 0:
            continue
        zero = np.abs(a @ cols.T) < TOL                                    # B x ncls
        zero = np.concatenate([zero, np.ones((len(a), 1), dtype=bool)], axis=1)   # index -1: always zero
        level = np.zeros((len(a), len(UNITS)))
        alive = np.ones((len(a), len(UNITS)), dtype=bool)
        for s in range(1, smax + 1):
            z = zero[:, seq[:, s - 1]]                                     # B x 32
            hit = alive & ~z
            level[hit] = s
            alive &= z
        assert not alive.any()
        cost = (1.0 / level).mean(axis=1)
        lo = cost.min()
        if lo < best_cost - 1e-12:
            best_cost, best_sets = lo, []
        if abs(lo - best_cost) < 1e-12:
            for i in np.nonzero(np.abs(cost - lo) < 1e-12)[0]:
                best_sets.append(tuple(np.nonzero(zero[i, :ncls])[0]))
    best_sets = sorted(set(best_sets))
    print("F. %d candidate vertices tried in %.0f s; best mean(1/s) = %.6f; distinct winners: %d"
          % (total, time.time() - t0, best_cost, len(best_sets)))
    print("   floating-point margins (a wide gap means no value was near a threshold):")
    for name in ("dependent, largest", "independent, smallest", "zero, largest", "non-zero, smallest"):
        print("      %-22s %.3e" % (name, gap[name]))

    # ---- exact recomputation of the winners
    print("   the conditions, by the entries k (mod 120) they cover:")
    for idx, ks in enumerate(classes.values()):
        print("      %2d: gcd(k,120) = %-3d k = %s" % (idx, gcd(ks[0], N), ks))
    out = []
    for zs in best_sets:
        sub = rows
        for idx in zs:
            k = reps[idx]
            if any(r[k] != 0 for r in sub):
                p = next(i for i, r in enumerate(sub) if r[k] != 0)
                piv = sub[p]
                sub = [[v - (r[k] / piv[k]) * u for v, u in zip(r, piv)] for i, r in enumerate(sub) if i != p]
        assert len(sub) == 1, "winner is not a vertex"
        v = sub[0]
        assert v[N] != 0
        pat = [x * Fraction(1, 4) / v[N] for x in v[:N]]
        cst = show(pat, "winner")
        assert abs(series_value(pat) / pi - mpf(1) / 4) < mpf(10) ** -50
        out.append(pat)
    if len(sys.argv) > 2:
        with open(sys.argv[2], "wb") as fh:
            pickle.dump(out, fh)
    return out


if __name__ == "__main__":
    main()
