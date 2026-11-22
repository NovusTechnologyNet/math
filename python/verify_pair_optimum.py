# Computing pi AND checking it: how few terms can two formulas share?
#
#   python verify_pair_optimum.py
#
# Takahashi (Ramanujan J. 51 (2020), 177-186) computes and verifies hexadecimal digits of
# pi with two different BBP-type formulas instead of running one formula twice, and reports
# 20% fewer terms than Huvent's formula run twice.  This script asks what the best possible
# pair is, inside the class F, using the classification of Theorem C.
#
# Model.  Let S_j be the sum of 2^(-floor(k/2))/k over k = j (mod 120).  A formula for pi is
# a rational pattern rho with sum rho(j) S_j = c pi, c != 0.  If two such formulas, scaled
# to the same value, differ at every position where either is non-zero, then their
# difference z is a zero relation (sum z(j) S_j = 0) whose support is the union of the two
# supports, and a wrong value of any single S_j changes the two results differently.  So:
#
#     cost of a checked computation  =  the least |supp z| over zero relations z of F
#                                       whose support contains the support of a pi formula.
#
# General cost (Takahashi's own accounting).  He also allows the two formulas to agree at
# a shared position, and then computes that series twice (his S(10,5) and S(30,15) are the
# same series).  With z = rho1 - rho2 that costs
#
#     |supp z|  +  2 |supp rho1 minus supp z|,
#
# and the first model is the case where the second term is 0.  Both are minimised below.
# Takahashi's pair (his formulas (23) and (26), base -2^30) is rebuilt in our coordinates
# as a test: it must lie in the 8-dimensional space, have value pi, and cost 60 (he counts
# 64, taking two pairs of equal series as different).
#
# The search is a branch-and-bound on the conditions "z(k) = 0", in exact rational
# arithmetic, on the 8-dimensional space of Theorem C or on its part of a given period.
#
# Proved in Lean since (lean/Pilean/PiFormula/CheckedPair.lean, Theorem J): the general cost
# is at least 60, and Takahashi's pair costs exactly 60.  Still only computed here: that his
# pair is the only one at 60, and the least cost 63 when no series is computed twice.
import os
import sys
from fractions import Fraction as Fr
from math import gcd

sys.setrecursionlimit(10000)
HERE = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(HERE, "..", "lean", "scripts", "baileygen.py")
src = open(GEN, encoding="utf-8").read().split(
    "VAL = [1, 0, 1, 0, 0, 0, 0, 0]")[0]
G = {}
exec(compile(src, "baileygen_defs", "exec"), G)
row = G["row"]                       # values at k of the eight named patterns
N = 120
QV = [Fr(1), Fr(0), Fr(1), Fr(0), Fr(0), Fr(0), Fr(0), Fr(0)]     # the value, in units of pi/4
ROWS = {k: [Fr(int(x.p), int(x.q)) for x in row(k)] for k in range(1, N + 1)}


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def norm(v):
    piv = next((x for x in v if x != 0), None)
    return None if piv is None else tuple(x / piv for x in v)


def reduce_vec(basis, v):
    v = list(v)
    for piv, r in basis:
        if v[piv] != 0:
            f = v[piv]
            v = [a - f * b for a, b in zip(v, r)]
    return v


def add_vec(basis, v):
    w = reduce_vec(basis, v)
    piv = next((i for i, x in enumerate(w) if x != 0), None)
    if piv is None:
        return basis
    w = [x / w[piv] for x in w]
    nb = []
    for p, r in basis:
        if r[piv] != 0:
            f = r[piv]
            r = tuple(a - f * b for a, b in zip(r, w))
        nb.append((p, r))
    nb.append((piv, tuple(w)))
    return tuple(nb)


def in_span(basis, v):
    return all(x == 0 for x in reduce_vec(basis, v))


def nullspace(basis, m):
    """A basis of {q : r.q = 0 for every r in basis} (basis in reduced echelon form)."""
    pivs = {p: r for p, r in basis}
    out = []
    for f in (j for j in range(m) if j not in pivs):
        q = [Fr(0)] * m
        q[f] = Fr(1)
        for p, r in pivs.items():
            q[p] = -r[f]
        out.append(q)
    return out


def clear(q):
    den = 1
    for x in q:
        den = den * x.denominator // gcd(den, x.denominator)
    v = [int(x * den) for x in q]
    g = 0
    for x in v:
        g = gcd(g, abs(x))
    return [x // g for x in v] if g else v


def analyze(B, label, show=3, general=0):
    """B: a basis (in the coordinates of the eight named patterns) of the space searched."""
    m = len(B)
    forms = {k: [dot(ROWS[k], b) for b in B] for k in range(1, N + 1)}
    Q = [dot(QV, b) for b in B]
    if all(x == 0 for x in Q):
        print("%s: dimension %d, no formula for pi" % (label, m))
        return None
    cls_of, vecs, keys = {}, [], {}
    for k in range(1, N + 1):
        n = norm(forms[k])
        if n is None:
            cls_of[k] = -1
        else:
            if n not in keys:
                keys[n] = len(vecs)
                vecs.append(list(n))
            cls_of[k] = keys[n]
    NC = len(vecs)
    sizes = [sum(1 for k in range(1, N + 1) if cls_of[k] == i) for i in range(NC)]
    total = sum(sizes)

    def span_of(Z, withQ):
        basis = add_vec((), Q) if withQ else ()
        for i in sorted(Z):
            basis = add_vec(basis, vecs[i])
        return basis

    cache1, cache2 = {}, {}

    def info1(Z):          # one formula: closure of Z, and "a pi formula vanishes on Z"
        key = frozenset(Z)
        if key not in cache1:
            basis = span_of(key, False)
            cl = frozenset(i for i in range(NC) if in_span(basis, vecs[i]))
            cache1[key] = cache1[cl] = (cl, not in_span(basis, Q))
        return cache1[key]

    def info2(Z):          # checked pair: zero set of the generic zero relation, feasibility
        key = frozenset(Z)
        if key not in cache2:
            basis = span_of(key, True)
            cl = frozenset(i for i in range(NC) if in_span(basis, vecs[i]))
            feas = len(basis) <= m - 1 and info1(cl)[1]
            cache2[key] = cache2[cl] = (cl, feas)
        return cache2[key]

    def search(info):
        best = [-1, []]
        nodes = [0]

        def tree(Z, D):
            nodes[0] += 1
            cl, _ = info(Z)
            while True:
                F = set()
                for i in range(NC):
                    if i not in cl and i not in D:
                        cl2, feas2 = info(set(cl) | {i})
                        if (not feas2) or (cl2 & D):
                            F.add(i)
                if not F:
                    break
                D = D | F
            free = [i for i in range(NC) if i not in cl and i not in D]
            have = sum(sizes[i] for i in cl)
            if have + sum(sizes[i] for i in free) < best[0]:
                return
            if not free:
                if have > best[0]:
                    best[0], best[1] = have, [cl]
                elif cl not in best[1]:
                    best[1].append(cl)
                return
            i = min(free, key=lambda i: (-sizes[i], i))
            tree(info(set(cl) | {i})[0], D)
            tree(cl, D | {i})

        root, feas = info(frozenset())
        if feas:
            tree(root, frozenset())
        return best, nodes[0]

    (w1, sols1), n1 = search(info1)
    (w2, sols2), n2 = search(info2)
    c1 = total - w1
    print("%s: dimension %d, %d positions with a term" % (label, m, total))
    print("   one formula:          %3d terms per 120 positions (%s per bit); %d supports; "
          "%d nodes" % (c1, Fr(c1, 60), len(sols1), n1))
    if w2 < 0:
        print("   checked pair:         none (no zero relation contains a pi formula)")
        return (c1, None)
    c2 = total - w2
    print("   checked pair:         %3d terms per 120 positions (%s per bit); %d supports; "
          "%d nodes" % (c2, Fr(c2, 60), len(sols2), n2))
    print("   one formula twice:    %3d;  the pair saves %.1f%%" % (2 * c1, 100 - 50.0 * c2 / c1))
    for cl in sols2[:show]:
        supp = sorted(k for k in range(1, N + 1) if cls_of[k] >= 0 and cls_of[k] not in cl)
        per = next(p for p in (4, 8, 12, 20, 24, 40, 60, 120)
                   if all((((k + p - 1) % N + 1) in supp) == (k in supp) for k in range(1, N + 1)))
        zs = nullspace(span_of(cl, True), m)
        ps = nullspace(span_of(cl, False), m)
        print("   support of period %d: %s" % (per, [k for k in supp if k <= per]))
        print("      zero relations with this support: dimension %d; patterns: dimension %d"
              % (len(zs), len(ps)))
        zq = [sum(c * b[j] for c, b in zip(zs[0], B)) for j in range(8)]
        print("      a zero relation (coordinates in the eight named patterns):", clear(zq))
        rho = next(p for p in ps if dot(p, Q) != 0)
        rq = [sum(c * b[j] for c, b in zip(rho, B)) for j in range(8)]
        scale = 1 / dot(rq, QV)
        vals = [dot(ROWS[k], rq) * scale for k in range(1, per + 1)]
        print("      a pi formula inside it (value pi/4), entries 1..%d:" % per,
              " ".join(str(v) for v in vals))
    if general:
        cache3 = {}

        def info3(Z):      # zero relations only: zero set of the generic one, z != 0 exists
            key = frozenset(Z)
            if key not in cache3:
                basis = span_of(key, True)
                cl = frozenset(i for i in range(NC) if in_span(basis, vecs[i]))
                cache3[key] = cache3[cl] = (cl, len(basis) <= m - 1)
            return cache3[key]

        def inner(Zf):     # most positions of Zf on which some pi formula vanishes
            bestw = [-1]

            def tree(Z, D):
                cl, _ = info1(Z)
                while True:
                    F = set()
                    for i in Zf:
                        if i not in cl and i not in D:
                            cl2, feas2 = info1(set(cl) | {i})
                            if (not feas2) or (cl2 & D):
                                F.add(i)
                    if not F:
                        break
                    D = D | F
                free = [i for i in Zf if i not in cl and i not in D]
                have = sum(sizes[i] for i in cl if i in Zf)
                if have + sum(sizes[i] for i in free) <= bestw[0]:
                    return
                if not free:
                    bestw[0] = have
                    return
                i = min(free, key=lambda i: (-sizes[i], i))
                tree(info1(set(cl) | {i})[0], D)
                tree(cl, D | {i})

            tree(info1(frozenset())[0], frozenset())
            return bestw[0]

        gbest = [min(c2, general), []]    # start from a known pair
        gn = [0, 0]

        def gtree(Z, D):
            gn[0] += 1
            cl, _ = info3(Z)
            while True:
                F = set()
                for i in range(NC):
                    if i not in cl and i not in D:
                        cl2, feas2 = info3(set(cl) | {i})
                        if (not feas2) or (cl2 & D):
                            F.add(i)
                if not F:
                    break
                D = D | F
            free = [i for i in range(NC) if i not in cl and i not in D]
            have = sum(sizes[i] for i in cl)
            if total - (have + sum(sizes[i] for i in free)) > gbest[0]:
                return
            if not free:
                gn[1] += 1
                e = have - inner(cl)
                cost = total - have + 2 * e
                if cost < gbest[0]:
                    gbest[0], gbest[1] = cost, [(cl, e)]
                elif cost == gbest[0]:
                    gbest[1].append((cl, e))
                return
            i = min(free, key=lambda i: (-sizes[i], i))
            gtree(info3(set(cl) | {i})[0], D)
            gtree(cl, D | {i})

        root, feas = info3(frozenset())
        if feas:
            gtree(root, frozenset())
        print("   general cost |supp z| + 2 |supp rho minus supp z|: least value %d; %d optima "
              "(%d with no series computed twice); %d nodes, %d zero-relation supports tried"
              % (gbest[0], len(gbest[1]), sum(1 for _, e in gbest[1] if e == 0), gn[0], gn[1]))
    return (c1, c2)


def takahashi():
    """His formulas (23) and (26) as patterns of period 120 (values at 1..120)."""
    def pat(terms):
        v = [Fr(0)] * (N + 1)
        for m, j, sign, e in terms:            # sign * 2^e * S(m, j)
            s = 60 // m
            pos = s * j
            c = sign * Fr(2) ** e * s * Fr(2) ** (pos // 2)
            v[pos] += c                        # k even
            v[pos + 60] -= c                   # k odd
        return v[1:]
    f23 = [(12, 1, -1, -1), (12, 3, -1, -6), (12, 5, 1, -11), (12, 7, 1, -16), (12, 9, -1, -21),
           (12, 11, -1, -26), (30, 1, 1, 2), (30, 3, -1, 0), (30, 5, -1, -4), (30, 7, -1, -4),
           (30, 9, 1, -6), (30, 11, -1, -8), (30, 13, 1, -10), (30, 15, 1, -14),
           (30, 17, 1, -14), (30, 19, -1, -16), (30, 21, 1, -18), (30, 23, -1, -20),
           (30, 25, -1, -24), (30, 27, -1, -24), (30, 29, 1, -26)]
    f26 = [(10, 5, 1, -14), (20, 1, 1, 0), (20, 3, 1, -3), (20, 5, -1, -6), (20, 7, -1, -9),
           (20, 9, 1, -12), (20, 11, 1, -15), (20, 13, -1, -18), (20, 15, -1, -21),
           (20, 17, 1, -24), (20, 19, 1, -27), (30, 1, 1, 1), (30, 3, 1, -2), (30, 5, 1, -3),
           (30, 7, -1, -5), (30, 9, -1, -8), (30, 11, -1, -9), (30, 13, 1, -11),
           (30, 15, -1, -13), (30, 17, 1, -15), (30, 19, -1, -17), (30, 21, -1, -20),
           (30, 23, -1, -21), (30, 25, 1, -23), (30, 27, 1, -26), (30, 29, 1, -27)]
    return pat(f23), pat(f26)


def coords(v):
    """Coordinates of a pattern in the eight named patterns, or None."""
    M = [list(ROWS[k]) + [v[k - 1]] for k in range(1, N + 1)]
    r = 0
    for c in range(8):
        p = next((i for i in range(r, N) if M[i][c] != 0), None)
        if p is None:
            return None
        M[r], M[p] = M[p], M[r]
        M[r] = [x / M[r][c] for x in M[r]]
        for i in range(N):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    if any(M[i][8] != 0 for i in range(8, N)):
        return None
    return [M[i][8] for i in range(8)]


def period_space(p):
    """The patterns of the 8-dimensional space that have period p."""
    basis = ()
    for k in range(1, N + 1):
        k2 = (k + p - 1) % N + 1
        basis = add_vec(basis, [a - b for a, b in zip(ROWS[k], ROWS[k2])])
    return nullspace(basis, 8)


if __name__ == "__main__":
    r23, r26 = takahashi()
    q23, q26 = coords(r23), coords(r26)
    assert q23 is not None and q26 is not None, "Takahashi's formulas are not in the space"
    v23, v26 = dot(q23, QV), dot(q26, QV)
    s23, s26 = [x / v23 for x in r23], [x / v26 for x in r26]
    n1 = sum(1 for x in s23 if x != 0)
    n2 = sum(1 for x in s26 if x != 0)
    diff = sum(1 for a, b in zip(s23, s26) if a != 0 and b != 0 and a != b)
    same = sum(1 for a, b in zip(s23, s26) if a != 0 and a == b)
    print("Takahashi's pair in our coordinates: values %s pi and %s pi" % (v23 / 4, v26 / 4))
    print("   terms per 120 positions: %d and %d; shared and different: %d; shared and equal: %d"
          % (n1, n2, diff, same))
    print("   cost = %d + %d - %d = %d   (his count: 64 per 60 bits)"
          % (n1, n2, diff, n1 + n2 - diff))
    print()
    E = [[Fr(int(i == j)) for j in range(8)] for i in range(8)]
    analyze(E, "all of F (period 120)", general=n1 + n2 - diff)
    print()
    for p in (8, 12, 20, 24, 40, 60):
        B = period_space(p)
        if B:
            analyze(B, "period %d, that is P(1, 2^%d, %d, .)" % (p, p // 2, p), show=1)
        else:
            print("period %d: no pattern" % p)
