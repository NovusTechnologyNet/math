"""Referee check of Theorem E (uniqueness count): EXACT enumeration of all 2-dimensional flats
(generic member of each) -- derived from review_vertex_exact.py.

Original description of the vertex enumerator follows.

EXACT enumeration of all vertices of the arrangement of the
35 conditions "entry = 0" on V, with exact integer arithmetic throughout.

Run with PYTHONPATH set to the numpy + python-flint folders:
    python review_vertex_exact.py <pickle written by review_space.py>

V comes from review_space.py (built independently of cheaper_formula.py). An integer
(LLL-reduced) basis of V is used; each condition is a primitive integer vector in Z^8.
A depth-first search over subsets of conditions maintains an exact integer basis of the
common kernel. At depth 6 (kernel of dimension 2, basis u, w) every 7th condition m gives
the vertex v = (c_m.w) u - (c_m.u) w, and c_j.v = (c_m.w)(c_j.u) - (c_m.u)(c_j.w) exactly.
Each distinct vertex (identified by its exact zero set) is scored once.
"""
import pickle
import sys
import time
from fractions import Fraction
from math import gcd

import numpy as np
from flint import fmpz_mat

N = 120
UNITS = [c for c in range(1, N) if gcd(c, N) == 1]


def prim(v):
    g = 0
    for x in v:
        g = gcd(g, x)
    if g == 0:
        return v
    v = [x // g for x in v]
    lead = next(x for x in v if x)
    return [-x for x in v] if lead < 0 else v


def main():
    data = pickle.load(open(sys.argv[1], "rb"))
    V, qV = data["V"], data["qV"]
    dim = len(V)
    # rows: pattern entries k = 1..120 then q; make integer, then LLL
    den = 1
    for r, q in zip(V, qV):
        for x in list(r) + [q]:
            den = den * x.denominator // gcd(den, x.denominator)
    rows = [[int(x * den) for x in r] + [int(q * den)] for r, q in zip(V, qV)]
    rows = [prim(r) for r in rows]                      # primitive rows before LLL
    # saturate: the lattice V cap Z^121 (HNF of the rational row space, cleared)
    from flint import fmpq_mat
    R, rk = fmpq_mat(rows).rref()
    rows = []
    for i in range(rk):
        rr = [Fraction(int(R[i, j].p), int(R[i, j].q)) for j in range(N + 1)]
        L = 1
        for x in rr:
            L = L * x.denominator // gcd(L, x.denominator)
        rows.append(prim([int(x * L) for x in rr]))
    B = fmpz_mat(rows).lll()
    rows = [[int(B[i, j]) for j in range(N + 1)] for i in range(dim)]
    # columns: entry k (k = 1..120 -> index k-1), and q
    col = {}
    for k in range(1, N + 1):
        c = [rows[i][k - 1] for i in range(dim)]
        if any(c):
            col[k % N] = c
    qcol = [rows[i][N] for i in range(dim)]
    classes, cls_of = [], {}
    for k, c in sorted(col.items()):
        p = prim(c)
        if p not in classes:
            classes.append(p)
        cls_of[k] = classes.index(p)
    ncls = len(classes)
    csize = [sum(1 for k in cls_of if cls_of[k] == j) for j in range(ncls)]
    print("V: dimension %d; non-trivial entries %d; distinct conditions %d; max |entry| of basis %d"
          % (dim, len(col), ncls, max(abs(x) for r in rows for x in r)))
    C = np.array(classes, dtype=object)
    smax = N
    seq = np.full((len(UNITS), smax), ncls, dtype=np.int64)          # index ncls: always zero
    for i, c in enumerate(UNITS):
        for s in range(1, smax + 1):
            k = s * c % N
            if k in cls_of:
                seq[i, s - 1] = cls_of[k]

    cache = {}
    stats = {"6-subsets of rank 6": 0, "distinct 2-dim flats": 0, "2-dim flats carrying pi": 0}

    def score(mask_bits):
        zero = np.zeros(ncls + 1, dtype=bool)
        zero[ncls] = True
        for j in range(ncls):
            if mask_bits >> j & 1:
                zero[j] = True
        lv = np.zeros(len(UNITS), dtype=np.int64)
        alive = np.ones(len(UNITS), dtype=bool)
        for s in range(1, smax + 1):
            z = zero[seq[:, s - 1]]
            hit = alive & ~z
            lv[hit] = s
            alive &= z
            if not alive.any():
                break
        assert not alive.any()
        terms = sum(csize[j] for j in range(ncls) if not (mask_bits >> j & 1))
        return (sum(Fraction(1, int(x)) for x in lv) / len(UNITS), Fraction(terms, 60))

    t0 = time.time()

    def dfs(start, depth, basis):
        # basis: list of integer vectors spanning the common kernel of the chosen conditions
        if depth == dim - 2:
            u, w = basis
            P0 = [sum(a * b for a, b in zip(c, u)) for c in classes]
            P1 = [sum(a * b for a, b in zip(c, w)) for c in classes]
            Q0 = sum(a * b for a, b in zip(qcol, u))
            Q1 = sum(a * b for a, b in zip(qcol, w))
            stats["6-subsets of rank 6"] += 1
            mask = 0
            for j in range(ncls):
                if P0[j] == 0 and P1[j] == 0:
                    mask |= 1 << j
            if mask in cache:
                return
            stats["distinct 2-dim flats"] += 1
            if Q0 == 0 and Q1 == 0:
                cache[mask] = None
                return
            stats["2-dim flats carrying pi"] += 1
            cache[mask] = score(mask)
            return
        for m in range(start, ncls):
            c = classes[m]
            vals = [sum(a * b for a, b in zip(c, v)) for v in basis]
            piv = next((i for i, x in enumerate(vals) if x != 0), None)
            if piv is None:
                continue                                       # dependent: prune
            new = []
            for i, v in enumerate(basis):
                if i == piv:
                    continue
                nv = [vals[piv] * x - vals[i] * y for x, y in zip(v, basis[piv])]
                new.append(prim(nv) if any(nv) else nv)
            dfs(m + 1, depth + 1, new)

    ident = [[int(i == j) for j in range(dim)] for i in range(dim)]
    dfs(0, 0, ident)
    print("exact enumeration done in %.0f s: %s" % (time.time() - t0, stats))
    sc = [c for c in cache.values() if c is not None]
    for name, idx in (("mean(1/s)", 0), ("terms per bit", 1)):
        vals = sorted({c[idx] for c in sc})
        print("%s: minimum %s attained by %d distinct vertices; next values %s"
              % (name, vals[0], sum(1 for c in sc if c[idx] == vals[0]), [str(v) for v in vals[1:4]]))
    front = []
    for a, b in sorted(set(sc)):
        if not front or b < front[-1][1]:
            front.append((a, b))
    print("Pareto front (mean(1/s), terms per bit): %s" % [(str(a), str(b)) for a, b in front])
    mn = min(x[0] for x in sc)
    best = [k for k, c in cache.items() if c is not None and c[0] == mn]
    with open(sys.argv[1] + ".flats2", "wb") as fh:
        pickle.dump({"classes": classes, "cache": cache, "best": best, "csize": csize}, fh)


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
