# How small can a proof of Theorem E be?  (experiment of 21 November 2026)
#
#   python theorem_e_experiment.py
#
# Theorem E: over the 8-dimensional space V of rational patterns whose series is a rational
# multiple of pi, with non-zero value,
#   * the least mean(1/s) over the 32 classes of primes modulo 120 is 7/24,
#   * the least number of non-zero entries per period 120 is 40 (terms per bit 2/3).
# exact_optimum.py proves this by trying all C(35, 7) = 6,724,520 choices of 7 zero
# conditions. That is too much for Lean's kernel. This script looks for a much smaller
# proof: a branch-and-bound tree on the 35 conditions "entry = 0".
#
# A node is a set Z of conditions assumed zero (closed under linear dependence, and not
# forcing pi = 0) and a set D of conditions assumed non-zero. A leaf is a node where a
# bound already decides the question. Everything is exact rational arithmetic.
#
# Result: 13 nodes for the bound 7/24 (20 with the equality cases: exactly two flats),
# and about 1,100 nodes for the bound 40 (about 1,800 with the equality cases: exactly two
# vertices). The third claim of Theorem E (the non-dominated pairs) is not tested here.
import math
import os
import sys
from fractions import Fraction as Fr

sys.setrecursionlimit(10000)
HERE = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(HERE, "..", "lean", "scripts", "baileygen.py")
src = open(GEN, encoding="utf-8").read().split(
    "VAL = [1, 0, 1, 0, 0, 0, 0, 0]")[0]
G = {}
exec(compile(src, "baileygen_defs", "exec"), G)
row = G["row"]                       # values at k of the eight named patterns
N = 120
Q = [Fr(1), Fr(0), Fr(1), Fr(0), Fr(0), Fr(0), Fr(0), Fr(0)]      # the value, in units of pi/4


def norm(v):
    piv = next((x for x in v if x != 0), None)
    return None if piv is None else tuple(x / piv for x in v)


# The conditions "rho(k) = 0": positions with proportional functionals form one class.
cls_of, vecs, keys = {}, [], {}
for k in range(1, N + 1):
    n = norm([Fr(int(x.p), int(x.q)) for x in row(k)])
    if n is None:
        cls_of[k] = -1
    else:
        if n not in keys:
            keys[n] = len(vecs)
            vecs.append(list(n))
        cls_of[k] = keys[n]
NC = len(vecs)
sizes = [sum(1 for k in range(1, N + 1) if cls_of[k] == i) for i in range(NC)]
rep = [min(k for k in range(1, N + 1) if cls_of[k] == i) for i in range(NC)]


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


cache = {}


def closure(Z):
    """(closure of Z, a basis of its span, does it leave pi non-zero?)"""
    key = frozenset(Z)
    if key not in cache:
        basis = ()
        for i in sorted(key):
            basis = add_vec(basis, vecs[i])
        cl = frozenset(i for i in range(NC) if in_span(basis, vecs[i]))
        cache[key] = cache[cl] = (cl, basis, not in_span(basis, Q))
    return cache[key]


def show(S):
    return "{" + ",".join(str(rep[i]) for i in sorted(S)) + "}"


# ------------------------------------------------------------------ prime measure
UNITS = [c for c in range(1, N) if math.gcd(c, N) == 1]
types = {}
for c in UNITS:
    ch = tuple(cls_of[N if s * c % N == 0 else s * c % N] for s in range(1, N + 1))
    types.setdefault(ch, []).append(c)
TYPES = [(ch, len(cs), cs[0]) for ch, cs in types.items()]


def max_s(ch, cl, basis, D):
    """The chain c, 2c, 3c, ... cannot stay zero beyond this s."""
    b, cur = basis, set(cl)
    for s, j in enumerate(ch, start=1):
        if j == -1 or j in cur:
            continue
        if j in D:
            return s
        nb = add_vec(b, vecs[j])
        if in_span(nb, Q):
            return s
        b = nb
        cur = set(i for i in range(NC) if in_span(b, vecs[i]))
        if cur & D:
            return s
    return 10 ** 9


def prime_tree(Z, D, depth, strict, out):
    cl, basis, _ = closure(Z)
    lb, und, info = Fr(0), [], []
    for ch, mult, c0 in TYPES:
        s, j = next((s, j) for s, j in enumerate(ch, start=1) if j != -1 and j not in cl)
        if j in D:
            lb += Fr(mult, s)
            info.append("s_%d=%d" % (c0, s))
        else:
            m = max_s(ch, cl, basis, D)
            lb += Fr(mult, m)
            und.append((Fr(mult, s) - Fr(mult, m), j))
            info.append("s_%d<=%d" % (c0, m))
    leaf = lb > Fr(28, 3) if strict else lb >= Fr(28, 3)
    out.append("%szero %s nonzero %s: %s, mean >= %s%s"
               % ("  " * depth, show(cl), show(D), " ".join(info), lb / 32, "  (leaf)" if leaf else ""))
    if leaf:
        return 1
    if not und:
        out.append("%s  attains %s" % ("  " * depth, lb / 32))
        return 1
    j = max(und)[1]
    n = 1
    cl2, _, feas2 = closure(set(cl) | {j})
    if feas2 and not (cl2 & D):
        n += prime_tree(cl2, D, depth + 1, strict, out)
    return n + prime_tree(cl, D | {j}, depth + 1, strict, out)


# ------------------------------------------------------------------ fewest terms
def terms_tree(Z, D, strict, found):
    cl, basis, _ = closure(Z)
    while True:                       # conditions that can no longer be zero
        F = set()
        for i in range(NC):
            if i not in cl and i not in D:
                cl2, _, feas2 = closure(set(cl) | {i})
                if (not feas2) or (cl2 & D):
                    F.add(i)
        if not F:
            break
        D = D | F
    free = [i for i in range(NC) if i not in cl and i not in D]
    have = sum(sizes[i] for i in cl)
    ub = have + sum(sizes[i] for i in free)
    if len(basis) == 6 and free:      # one more independent condition at most
        ub = max(sum(sizes[j] for j in closure(set(cl) | {i})[0]) for i in free)
    if (ub < 79) if strict else (ub <= 79):
        return 1
    if not free:
        found.append(sorted(rep[i] for i in cl))
        return 1
    i = min(free, key=lambda i: (-sizes[i], i))
    return 1 + terms_tree(closure(set(cl) | {i})[0], D, strict, found) + terms_tree(cl, D | {i}, strict, found)


if __name__ == "__main__":
    print("conditions: %d classes; chain types among the 32 units: %d" % (NC, len(TYPES)))
    for ch, mult, c0 in TYPES:
        print("  units = %d (mod 12): %d classes of primes, chain of positions %s"
              % (c0 % 12, mult, [rep[j] for j in ch[:8]]))
    out = []
    n = prime_tree(frozenset(), frozenset(), 0, False, out)
    print("\nPrime measure, proof that mean(1/s) >= 7/24: %d nodes" % n)
    print("\n".join(out))
    out = []
    n = prime_tree(frozenset(), frozenset(), 0, True, out)
    print("\nPrime measure with the equality cases: %d nodes, attained by %d flats"
          % (n, sum(1 for l in out if "attains" in l)))
    found = []
    n = terms_tree(frozenset(), frozenset(), False, found)
    print("\nFewest terms, proof that at least 40 of 120 entries are non-zero: %d nodes" % n)
    found = []
    n = terms_tree(frozenset(), frozenset(), True, found)
    print("Fewest terms with the equality cases: %d nodes, attained by %d vertices" % (n, len(found)))
    for f in found:
        print("  zero conditions (representatives):", f)
    print("\nexact_optimum.py tries 6,724,520 cases for the same two statements.")
