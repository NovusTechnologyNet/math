#!/usr/bin/env python3
"""
erdos_pm1_check.py -- independent check of a 2-adic ("parity") theorem on Erdos's conjecture.

Conjecture (Erdos, via Livingston 1965).  q >= 2, f: Z -> {-1,0,1} periodic mod q, f(n) = +-1 for q not
dividing n, f(n) = 0 for q | n.  Then sum_{n>=1} f(n)/n != 0 (when it converges, i.e. sum_{r<=q} f(r) = 0).

Criterion (Okada 1982; here derived from Baker's theorem, see research/2026-11-23-erdos-pm1/00_summary.md).
For q odd and f: Z/q -> Q with sum f = 0 put  M(q) = {integers >= 1 composed of primes dividing q}.
  L(1,f) = -(1/q) * [ sum_{a in (Z/q)^*} g(a) psi(a/q)  +  sum_{p | q} c_p log p ],
  g(a)  = sum_{m in M(q)} f(a m)/m,
  c_p   = sum_{r=1..q} f(r) lam(r,p),  lam(r,p) = v_p(r) if v_p(r) < v_p(q), else v_p(q) + 1/(p-1),
and L(1,f) = 0  iff  (a) g(a) = 0 for every unit a  and  (b) c_p = 0 for every prime p | q.
Equivalent description of the solution space (with f(0) = 0):  f = prod_{p|q} (1 - T_p/p) h,  (T_p h)(n) = h(pn),
h supported on the non-units, h(0) = 0, and for each p: sum of h(n) over {n : gcd(n,q) = p^i, 1 <= i <= v_p(q)} = 0.

Theorem checked here.  If f(0) = 0, every f(r), r != 0, is a rational number with odd numerator and odd
denominator, and L(1,f) = 0, then q is a perfect square.  (So Erdos's conjecture holds for every non-square q.)
Key lemma (Theorem A): under (a) alone, for every prime p | q with k = v_p(q):
      sum_{r != 0, p^k | r} f(r)  =  (p-1) k   modulo 2^(v_2(p-1)+1),
while (b) forces this sum to be 0 modulo 2^(v_2(p-1)+1).

What the program does (all exact unless stated):
  criterion  : numerical test of the criterion (60+ digits) on random rational solutions and non-solutions,
               the formula for L(1,f), and (with python-flint) an LLL test that there are no further relations.
  direct     : method A.  2-adic test on the full solution space: is there a vanishing f with all f(r), r != 0,
               2-adic units?  (Linear system modulo 2^64 with Smith-type elimination; rigorous.)
  reduced    : method B.  The same question after reduction to 2-groups (system (M) + (b) of the summary).
  brute      : method C.  Exhaustive exact search for +-1 solutions for small q (no parity argument).
  theoremA   : builds explicit rational f with odd values satisfying (a) and checks the key congruence.
  mainequation: exact check of the group-ring identity (M) (Lemma 2) and of Lemma 1 on explicit functions.
  abstract   : tests Lemma D, Lemma KL and Theorem A on random "abstract" data (no arithmetic input).
  squares    : explicit odd-valued vanishing functions for odd squares (the parity method cannot work there).
  known      : which q = 1 mod 4 are covered by no known result as listed in the two research reports.
  selftest   : a quick run of everything on small cases (about a minute).

Usage:  env -u PYTHONPATH python erdos_pm1_check.py selftest
        env -u PYTHONPATH python erdos_pm1_check.py direct 9 600
        env -u PYTHONPATH python erdos_pm1_check.py reduced 9 5000
        (see the bottom of the file for the other commands).   Output is ASCII only.
"""
import sys
import time
import random
from fractions import Fraction as Fr
from itertools import product, combinations
from math import gcd, isqrt

import numpy as np
from sympy import (factorint, totient, divisors, isprime, n_order, primitive_root,
                   discrete_log, jacobi_symbol)

MOD = 1 << 64


# --------------------------------------------------------------------------------------------------
# 0. small helpers
# --------------------------------------------------------------------------------------------------
def v2(x):
    """2-adic valuation of a non-zero integer."""
    x = int(x)
    return (x & -x).bit_length() - 1


def v2q(x):
    """2-adic valuation of a non-zero rational."""
    x = Fr(x)
    return v2(x.numerator) - v2(x.denominator)


def squarefree_divisors(primes):
    """[(D, mu(D))] for the squarefree D composed of the given primes."""
    res = [(1, 1)]
    for p in primes:
        res += [(d * p, -m) for (d, m) in res]
    return res


def is_square(q):
    return isqrt(q) ** 2 == q


# --------------------------------------------------------------------------------------------------
# 1. the criterion
# --------------------------------------------------------------------------------------------------
def M_weights(q, primes, n):
    """dict r -> w(r) with  sum_{m in M(q)} f(n m)/m = sum_r w(r) f(r)   (exact, geometric series)."""
    cur = {n % q: Fr(1)}
    for p in primes:
        new = {}
        for x0, w in cur.items():
            seen = {}
            seq = []
            x = x0
            while x not in seen:            # orbit of multiplication by p: pre-period, then a cycle
                seen[x] = len(seq)
                seq.append(x)
                x = (x * p) % q
            pre = seen[x]
            per = len(seq) - pre
            for j, y in enumerate(seq):
                c = Fr(1, p ** j)
                if j >= pre:
                    c = c / (1 - Fr(1, p ** per))
                new[y] = new.get(y, 0) + w * c
        cur = new
    return cur


def cond_a(f, q):
    """[g(a) for units a],  g(a) = sum_{m in M(q)} f(am)/m."""
    primes = sorted(factorint(q))
    out = []
    for a in range(1, q):
        if gcd(a, q) == 1:
            out.append(sum(w * f[r] for r, w in M_weights(q, primes, a).items()))
    return out


def lam(r, p, k):
    v = 0
    while v < k and r % p == 0:
        r //= p
        v += 1
    return Fr(v) if v < k else Fr(k) + Fr(1, p - 1)


def cond_b(f, q):
    """[c_p for p | q],  c_p = sum_{r=1..q} f(r) lam(r,p)   (r = q is the residue 0)."""
    fac = factorint(q)
    return [sum(f[r % q] * lam(r, p, fac[p]) for r in range(1, q + 1)) for p in sorted(fac)]


def f_from_h(h, q, primes):
    """f = prod_p (1 - T_p/p) h."""
    divs = squarefree_divisors(primes)
    return [sum(Fr(mu, d) * h[(d * n) % q] for d, mu in divs) for n in range(q)]


def Y_set(q, primes, p):
    """{n != 0 : gcd(n,q) is a non-trivial power of p}."""
    return [n for n in range(1, q) if gcd(n, q) > 1 and all(gcd(n, q) % r for r in primes if r != p)]


def random_vanishing(q, rng, den=5, enforce_b=True):
    """random rational f in the solution space of the criterion (or only of (a) if enforce_b is False)."""
    primes = sorted(factorint(q))
    h = [Fr(0)] * q
    for n in range(1, q):
        if gcd(n, q) > 1:
            h[n] = Fr(rng.randint(-9, 9), rng.randint(1, den))
    if enforce_b:
        for p in primes:
            Y = Y_set(q, primes, p)
            h[Y[0]] -= sum(h[n] for n in Y)
    return f_from_h(h, q, primes)


def L1(f, q, dps=70):
    """sum_{n>=1} f(n)/n = -(1/q) sum_{a=1..q-1} f(a) psi(a/q)   (needs sum f = 0 and f(0) = 0)."""
    import mpmath as mp
    mp.mp.dps = dps
    assert sum(f) == 0 and f[0] == 0
    s = mp.mpf(0)
    for a in range(1, q):
        fa = Fr(f[a])
        if fa != 0:
            s += mp.mpf(fa.numerator) / fa.denominator * mp.digamma(mp.mpf(a) / q)
    return -s / q


def test_criterion(qs, seed=1, verbose=True):
    """(1) solutions of the linear system have L(1,f) = 0 to 60 digits; (2) the general formula for L(1,f);
    (3) functions outside the solution space have L(1,f) != 0."""
    import mpmath as mp
    rng = random.Random(seed)
    ok = True
    for q in qs:
        fac = factorint(q)
        primes = sorted(fac)
        f = random_vanishing(q, rng)
        ga, cb = cond_a(f, q), cond_b(f, q)
        val = L1(f, q)
        t1 = all(x == 0 for x in ga) and all(x == 0 for x in cb) and abs(val) < mp.mpf(10) ** -60
        # (2) general formula on a random integer function with sum 0 (not a solution)
        f2 = [0] + [rng.randint(-3, 3) for _ in range(q - 1)]
        f2[1] -= sum(f2)
        f2 = [Fr(x) for x in f2]
        ga2, cb2 = cond_a(f2, q), cond_b(f2, q)
        units = [a for a in range(1, q) if gcd(a, q) == 1]
        rhs = mp.mpf(0)
        for a, g in zip(units, ga2):
            rhs += mp.mpf(g.numerator) / g.denominator * mp.digamma(mp.mpf(a) / q)
        for p, c in zip(primes, cb2):
            rhs += mp.mpf(c.numerator) / c.denominator * mp.log(p)
        rhs = -rhs / q
        val2 = L1(f2, q)
        t2 = abs(val2 - rhs) < mp.mpf(10) ** -60
        # (3) a function satisfying (a) but not (b): L(1,f) = -(1/q) sum c_p log p, non-zero
        f3 = random_vanishing(q, rng, enforce_b=False)
        cb3 = cond_b(f3, q)
        val3 = L1(f3, q)
        t3 = all(x == 0 for x in cond_a(f3, q)) and (any(c != 0 for c in cb3) == (abs(val3) > mp.mpf(10) ** -30))
        ok = ok and t1 and t2 and t3
        if verbose:
            print("q=%4d  solution: |L(1,f)| = %s  (a),(b) exact: %s | formula for L(1,f) on a random f: %s (L = %s) |"
                  " (a) only: L = %s, some c_p != 0: %s" % (q, mp.nstr(abs(val), 3), t1, t2, mp.nstr(val2, 10),
                                                         mp.nstr(val3, 10), any(c != 0 for c in cb3)), flush=True)
    return ok


def lll_completeness(qs, verbose=True):
    """Integer relations sum f(r) psi(r/q) = 0, sum f = 0 of small height: their number should be exactly
    q - 1 - phi(q) - t.  Needs python-flint.  (300-digit arithmetic; numerical evidence, not a proof.)"""
    import flint
    import mpmath as mp
    mp.mp.dps = 330
    C = 10 ** 300
    ok = True
    for q in qs:
        n = q - 1
        rows = []
        for i in range(n):
            row = [0] * n + [C, int(mp.nint(mp.digamma(mp.mpf(i + 1) / q) * C))]
            row[i] = 1
            rows.append(row)
        M = flint.fmpz_mat(rows).lll()
        norms = sorted(sum(int(M[i, j]) ** 2 for j in range(n + 2)) for i in range(n))
        small = [x for x in norms if x < 10 ** 8]
        pred = q - 1 - int(totient(q)) - len(factorint(q))
        ok = ok and len(small) == pred
        if verbose:
            rest = norms[len(small)] if len(small) < n else 0
            print("q=%3d  relations of small height: %d  predicted dimension: %d  largest squared norm: %d  "
                  "next vector: about 10^%d" % (q, len(small), pred, max(small) if small else 0,
                                                len(str(rest)) - 1), flush=True)
    return ok


def square_example(q):
    """For an odd square q: f(r) = (-1)^Omega(N) * rad(N)/N * theta(r), N = q/gcd(r,q), theta(r) = Legendre
    symbol of r/gcd(r,q) mod p if N is a power of one prime p, else 1.  Odd-valued, f(0) = 0, L(1,f) = 0."""
    assert all(k % 2 == 0 for k in factorint(q).values())
    f = [Fr(0)] * q
    for r in range(1, q):
        d = gcd(r, q)
        fN = factorint(q // d)
        rad = 1
        for p in fN:
            rad *= p
        val = Fr(rad, q // d) * (-1) ** sum(fN.values())
        if len(fN) == 1:
            p = list(fN)[0]
            val *= int(jacobi_symbol((r // d) % p, p))
        f[r] = val
    return f


# --------------------------------------------------------------------------------------------------
# 2. linear systems modulo 2^64 (Smith-type elimination, pivot of least 2-adic valuation)
# --------------------------------------------------------------------------------------------------
def val64(arr):
    """2-adic valuations of the entries of a uint64 array (64 for 0)."""
    a = arr.astype(np.uint64)
    low = a & (~a + np.uint64(1))
    out = np.full(a.shape, 64, dtype=np.int64)
    nz = low != 0
    out[nz] = np.round(np.log2(low[nz].astype(np.float64))).astype(np.int64)
    return out


def to_u64(rows):
    return np.array([[int(x) % MOD for x in r] for r in rows], dtype=np.uint64)


def eliminate(M, b=None, want_solution=False):
    """M: (m,n) uint64, b: (m,) uint64 or None.  Row elimination with full pivoting on the valuation.
    Returns (solvable, pivot_valuations, x).  'solvable' refers to M x = b modulo 2^64 and is exact:
    at step i the pivot has the least valuation v_i of the remaining block, so row i reads
    2^v_i * (unit * x_i + ...) = b_i, solvable iff 2^v_i | b_i (back-substitution); rows that become 0 need b = 0.
    If the number of pivots equals m and all v_i < 64, the same answer holds over the 2-adic integers."""
    M = M.copy()
    m, n = M.shape
    b = np.zeros(m, dtype=np.uint64) if b is None else b.copy()
    perm = list(range(n))
    piv = []
    i = 0
    while i < m and i < n:
        sub = M[i:, i:]
        v = val64(sub)
        idx = int(np.argmin(v))
        r, c = divmod(idx, sub.shape[1])
        vmin = int(v[r, c])
        if vmin >= 64:
            break
        r += i
        c += i
        if r != i:
            M[[i, r]] = M[[r, i]]
            b[[i, r]] = b[[r, i]]
        if c != i:
            M[:, [i, c]] = M[:, [c, i]]
            perm[i], perm[c] = perm[c], perm[i]
        inv = pow(int(M[i, i]) >> vmin, -1, MOD)
        col = M[i + 1:, i].copy()
        nz = np.nonzero(col)[0]
        if len(nz):
            mult = (col[nz] >> np.uint64(vmin)) * np.uint64(inv)
            M[i + 1 + nz, i:] -= mult[:, None] * M[i, i:][None, :]
            b[i + 1 + nz] -= mult * b[i]
        piv.append(vmin)
        i += 1
    ok = not np.any(b[i:] != 0)
    for k in range(i):
        if piv[k] and (int(b[k]) & ((1 << piv[k]) - 1)):
            ok = False
    x = None
    if ok and want_solution:
        xs = [0] * n
        for k in range(i - 1, -1, -1):
            rhs = (int(b[k]) - sum(int(M[k, c]) * xs[c] for c in range(k + 1, n) if xs[c])) % MOD
            xs[k] = ((rhs >> piv[k]) * pow(int(M[k, k]) >> piv[k], -1, MOD)) % MOD
        x = [0] * n
        for k in range(n):
            x[perm[k]] = xs[k]
    return ok, piv, x


# --------------------------------------------------------------------------------------------------
# 3. method A: the 2-adic test on the full solution space
# --------------------------------------------------------------------------------------------------
def denominator_bound(q, fac):
    """D0 with 2^D0 * prod_p (1 - T_p/p)^(-1) 2-adically integral: sum_p v_2(p^n_p - 1), n_p = order of p
    modulo q/p^k (the period of T_p)."""
    D = 0
    for p, k in fac.items():
        m = q // p ** k
        D += v2(p ** (1 if m == 1 else n_order(p, m)) - 1)
    return D


def direct_system(q, use_b=True):
    """Unknowns h' = 2^63 h on the non-units (one unknown per prime removed by sum_{Y_p} h = 0 if use_b).
    Rows n = 1..q-1:  rad(q) * f(n) = sum_D mu(D) (rad(q)/D) h(Dn).   f(n) = 1 mod 2 for all n  <=>
    rows * h' = 2^63 (mod 2^64).  Valid because 2^D0 h is integral for every solution and D0 <= 63."""
    fac = factorint(q)
    primes = sorted(fac)
    assert q % 2 == 1 and denominator_bound(q, fac) <= 63, "q even or denominators too large for 64 bits"
    Q = 1
    for p in primes:
        Q *= p
    Lset = [n for n in range(1, q) if gcd(n, q) > 1]
    pos = {n: i for i, n in enumerate(Lset)}
    rows = [[0] * len(Lset) for _ in range(q - 1)]
    for n in range(1, q):
        for d, mu in squarefree_divisors(primes):
            x = (d * n) % q
            if x in pos:
                rows[n - 1][pos[x]] += mu * (Q // d)
    B = to_u64(rows)
    keep = list(range(len(Lset)))
    subst = []
    if use_b:
        drop = set()
        for p in primes:
            Y = Y_set(q, primes, p)
            for n in Y[1:]:
                B[:, pos[n]] -= B[:, pos[Y[0]]]
            drop.add(pos[Y[0]])
            subst.append((Y[0], Y[1:]))
        keep = [i for i in keep if i not in drop]
    return B[:, keep], [Lset[i] for i in keep], subst, primes


def parity_direct(q, use_b=True):
    """True iff some f in the solution space (of (a),(b); or of (a) only) has all f(r), r != 0, 2-adic units,
    i.e. iff the parity argument does NOT exclude q."""
    B, _, _, _ = direct_system(q, use_b)
    rhs = np.full(q - 1, np.uint64(1 << 63), dtype=np.uint64)
    return eliminate(B, rhs)[0]


def unit_solution(q, use_b=False):
    """An explicit f: Z/q -> Q, f(0) = 0, all other values odd/odd, in the solution space of (a)
    (and (b) if use_b); None if there is none."""
    B, cols, subst, primes = direct_system(q, use_b)
    rhs = np.full(q - 1, np.uint64(1 << 63), dtype=np.uint64)
    ok, _, x = eliminate(B, rhs, want_solution=True)
    if not ok:
        return None
    h = [Fr(0)] * q
    for n, hv in zip(cols, x):
        h[n] = Fr(hv - MOD if hv >= MOD // 2 else hv, 1 << 63)
    for n0, rest in subst:
        h[n0] = -sum(h[n] for n in rest)
    return f_from_h(h, q, primes)


# --------------------------------------------------------------------------------------------------
# 4. method B: the reduced system on 2-groups
# --------------------------------------------------------------------------------------------------
def data_from_q(q):
    """P (primes), K (exponents), S (s_p = v_2(p-1)), TH[i][j] = class of p_j in C_i = Z/2^s_i
    (discrete logarithm of p_j modulo p_i, reduced modulo 2^s_i)."""
    fac = factorint(q)
    P = sorted(fac)
    K = [fac[p] for p in P]
    S = [v2(p - 1) for p in P]
    t = len(P)
    TH = [[0] * t for _ in range(t)]
    for i, p in enumerate(P):
        g = primitive_root(p)
        for j, r in enumerate(P):
            if i != j:
                TH[i][j] = int(discrete_log(p, r % p, g)) % (1 << S[i])
    return P, K, S, TH


def reduced_system(P, K, S, TH, use_b=True):
    """Unknowns e_n(x), n a non-empty subset of the primes, x in S_n = prod_{i in n} Z/2^s_i  (g_n = nu(n) + 2 e_n).
    (M): for every y in S_P:  sum_n [prod_{i in n} (p_i - T_i) (e_n o pi_n)](y) = -(Pi_P - 1)/2,
         (T_i phi)(y) = phi(y + theta_i), theta_i = (class of p_i in C_j)_{j != i}, 0 at i,
         Pi_A = prod_{i in A} (1 + (p_i - 1) k_i).
    (b): for every i:  sum_{n not containing i} o(n) sum_x e_n(x) = -(Pi_{P - i} - 1)/2,
         exactly if k_i = 1, modulo 2^s_i if k_i >= 2 (slack variable);  o(n) = prod (p-1)/2^s_p."""
    t = len(P)
    sizes = [1 << s for s in S]
    pts = list(product(*[range(m) for m in sizes]))
    pidx = {y: i for i, y in enumerate(pts)}
    nQ = len(pts)
    subsets = [n for r in range(1, t + 1) for n in combinations(range(t), r)]
    cols = [(n, x) for n in subsets for x in product(*[range(sizes[i]) for i in n])]
    nslack = sum(1 for k in K if k >= 2) if use_b else 0
    M = [[0] * (len(cols) + nslack) for _ in range(nQ + (t if use_b else 0))]

    def o(n):
        r = 1
        for i in n:
            r *= (P[i] - 1) >> S[i]
        return r

    def Pi(n):
        r = 1
        for i in n:
            r *= 1 + (P[i] - 1) * K[i]
        return r

    for c, (n, x) in enumerate(cols):
        phi = {y: 1 for y in pts if all(y[i] == x[a] for a, i in enumerate(n))}
        for i in n:
            new = {}
            for y, val in phi.items():
                new[y] = new.get(y, 0) + P[i] * val
                y2 = tuple((y[j] - (TH[j][i] if j != i else 0)) % sizes[j] for j in range(t))
                new[y2] = new.get(y2, 0) - val
            phi = new
        for y, val in phi.items():
            M[pidx[y]][c] += val
        if use_b:
            for i in range(t):
                if i not in n:
                    M[nQ + i][c] += o(n)
    b = [-(Pi(range(t)) - 1) // 2] * nQ
    if use_b:
        sl = 0
        for i in range(t):
            b.append(-(Pi([j for j in range(t) if j != i]) - 1) // 2)
            if K[i] >= 2:
                M[nQ + i][len(cols) + sl] = 1 << S[i]
                sl += 1
    return M, b, cols


def reduced_solvable(P, K, S, TH, use_b=True):
    if len(P) == 1:                       # prime power: (p-1) e = -(p-1) k/2
        return K[0] % 2 == 0
    M, b, _ = reduced_system(P, K, S, TH, use_b)
    ok, piv, _ = eliminate(to_u64(M), np.array([x % MOD for x in b], dtype=np.uint64))
    assert len(piv) == len(M) and max(piv) < 64, "rank or precision problem"
    return ok


def parity_reduced(q, use_b=True):
    P, K, S, TH = data_from_q(q)
    return reduced_solvable(P, K, S, TH, use_b)


def predicted_a_only(q):
    """Observed (not proved in general): (a) alone has a 2-adic-unit solution iff the number of primes p | q
    with v_2(p-1) minimal and v_p(q) odd is even."""
    fac = factorint(q)
    smin = min(v2(p - 1) for p in fac)
    return sum(1 for p, k in fac.items() if v2(p - 1) == smin and k % 2 == 1) % 2 == 0


# --------------------------------------------------------------------------------------------------
# 5. method C: exhaustive exact search for +-1 solutions
# --------------------------------------------------------------------------------------------------
def brute_force_pm1(q, max_free=24):
    """Number of f with values +-1 off 0, f(0) = 0, in the solution space, found by enumerating all sign
    patterns on the non-units (the values on the units are then forced: f(a) = sum_{D>1} mu(D) h(Da)/D with
    h = M f).  Exact integer arithmetic.  Returns (count, number of sign patterns examined)."""
    fac = factorint(q)
    primes = sorted(fac)
    Lset = [n for n in range(1, q) if gcd(n, q) > 1]
    nL = len(Lset)
    if nL > max_free:
        return None
    pos = {n: i for i, n in enumerate(Lset)}
    hrow = {n: M_weights(q, primes, n) for n in Lset}
    rows = []
    for a in range(1, q):
        if gcd(a, q) == 1:
            row = [Fr(0)] * nL
            for d, mu in squarefree_divisors(primes):
                x = (d * a) % q
                if d > 1 and x != 0:
                    for r, w in hrow[x].items():
                        if r != 0:
                            row[pos[r]] += Fr(mu, d) * w
            rows.append((row, True))
    for p in primes:
        rows.append(([lam(r, p, fac[p]) for r in Lset], False))
    int_rows = []
    for row, is_unit in rows:
        den = 1
        for x in row:
            den = den * x.denominator // gcd(den, x.denominator)
        ints = [int(x * den) for x in row]
        assert sum(abs(v) for v in ints) < 2 ** 62
        int_rows.append((np.array(ints, dtype=np.int64), den if is_unit else 0))
    int_rows.sort(key=lambda r: r[1])      # the (b) equations (target 0) first
    count = 0
    total = 1 << (nL - 1)                   # f and -f: fix the first sign
    chunk = 1 << 18
    shifts = np.arange(nL - 1, dtype=np.int64)
    for start in range(0, total, chunk):
        idx = np.arange(start, min(start + chunk, total), dtype=np.int64)
        X = np.ones((len(idx), nL), dtype=np.int64)
        X[:, 1:] = 1 - 2 * ((idx[:, None] >> shifts[None, :]) & 1)
        for vec, target in int_rows:
            X = X[np.abs(X @ vec) == target]
            if len(X) == 0:
                break
        count += 2 * len(X)
    return count, 2 * total


# --------------------------------------------------------------------------------------------------
# 6. Theorem A on explicit functions
# --------------------------------------------------------------------------------------------------
def check_theorem_A(q, verify_a=None):
    """Take an explicit odd-valued f satisfying (a) (if any) and check, for each p | q,
    sum_{r != 0, p^k | r} f(r) = (p-1) k  mod 2^(s+1).  Returns None if (a) has no such f, else (ok, details)."""
    f = unit_solution(q, use_b=False)
    if f is None:
        return None
    fac = factorint(q)
    assert f[0] == 0 and all(v2q(f[r]) == 0 for r in range(1, q))
    if verify_a if verify_a is not None else q <= 120:
        assert all(x == 0 for x in cond_a(f, q)), "(a) fails"
    ok = True
    det = []
    for p in sorted(fac):
        k, s = fac[p], v2(p - 1)
        ell = sum(f[r] for r in range(1, q) if r % p ** k == 0)
        d = ell - (p - 1) * k
        good = d == 0 or v2q(d) >= s + 1
        ok = ok and good
        det.append((p, k, s, "inf" if d == 0 else v2q(d)))
    return ok, det, len(set(f[1:]))


def check_theorem_B(qs, rng, trials=5):
    """For random odd-valued f (f(0) = 0; no other condition): (p-1) c_p = ((p-1)k+1) * ell mod 2^(s+1),
    ell = sum_{r != 0, p^k | r} f(r).  (So c_p = 0 forces ell = 0 mod 2^(s+1).)  Returns (cases, failures)."""
    n = bad = 0
    for q in qs:
        fac = factorint(q)
        for _ in range(trials):
            f = [Fr(0)] + [Fr(rng.randrange(-99, 100, 2), rng.randrange(1, 60, 2)) for _ in range(q - 1)]
            for p, c in zip(sorted(fac), cond_b(f, q)):
                k, s = fac[p], v2(p - 1)
                ell = sum(f[r] for r in range(1, q) if r % p ** k == 0)
                d = (p - 1) * c - ((p - 1) * k + 1) * ell
                n += 1
                bad += 1 if d != 0 and v2q(d) < s + 1 else 0
    return n, bad


def main_equation_residual(f, q):
    """Exact check of Lemma 2.  Computes the elements g_n of the summary from f (definition 5.1) and returns
    (the function x -> sum_n [prod_{p in n} (p - T_p) (g_n o pi_n)](x) on S_P, the g_n, the data)."""
    P, K, S, TH = data_from_q(q)
    t = len(P)
    sizes = [1 << s for s in S]
    gens = [primitive_root(p) for p in P]
    g = {}
    for r in range(1, q):
        d = gcd(r, q)
        n = tuple(i for i in range(t) if (q // d) % P[i] == 0)
        x = tuple(int(discrete_log(P[i], (r // d) % P[i], gens[i])) % sizes[i] for i in n)
        on = 1
        for i in n:
            on *= (P[i] - 1) >> S[i]
        g.setdefault(n, {})
        g[n][x] = g[n].get(x, 0) + Fr(f[r]) / on
    pts = list(product(*[range(k) for k in sizes]))
    res = {y: Fr(0) for y in pts}
    for n, gn in g.items():
        phi = {y: gn.get(tuple(y[i] for i in n), Fr(0)) for y in pts}
        for i in n:                         # (T_i phi)(y) = phi(y + theta_i)
            phi = {y: P[i] * phi[y] - phi[tuple((y[j] + (TH[j][i] if j != i else 0)) % sizes[j] for j in range(t))]
                   for y in pts}
        for y in pts:
            res[y] += phi[y]
    return res, g, (P, K, S, TH)


def check_main_equation(q, rng):
    """(M) holds exactly for a random rational solution of (a), fails for a random f, and Lemma 1 holds for an
    odd-valued solution of (a) (third entry None if (a) has no odd-valued solution)."""
    f = random_vanishing(q, rng, enforce_b=False)
    holds = all(v == 0 for v in main_equation_residual(f, q)[0].values())
    f2 = [Fr(0)] + [Fr(rng.randint(-3, 3)) for _ in range(q - 1)]
    fails = any(v != 0 for v in main_equation_residual(f2, q)[0].values())
    fu = unit_solution(q, use_b=False)
    lem1 = None
    if fu is not None:
        res, g, (P, K, S, TH) = main_equation_residual(fu, q)
        lem1 = all(v == 0 for v in res.values())
        for n, gn in g.items():
            nu, size = 1, 1
            for i in n:
                nu *= K[i]
                size <<= S[i]
            lem1 = lem1 and len(gn) == size and all(v == nu or v2q(v - nu) >= 1 for v in gn.values())
    return holds, fails, lem1


# --------------------------------------------------------------------------------------------------
# 7. abstract tests of the lemmas (random data: odd numbers p_i = 1 mod 2^s_i, arbitrary group elements)
# --------------------------------------------------------------------------------------------------
def random_abstract(rng, t, smax):
    S = [rng.randint(1, smax) for _ in range(t)]
    P = [1 + (1 << s) * rng.randrange(1, 64, 2) for s in S]
    K = [rng.randint(1, 4) for _ in range(t)]
    TH = [[0 if i == j else rng.randrange(1 << S[i]) for j in range(t)] for i in range(t)]
    return P, K, S, TH


def abstract_theorem_A(P, K, S, TH):
    """For abstract data: the set of residues c mod 2^(s_i+1) for which (M) together with
    'sum_{n without i} o(n) eps(g_n) = c' is solvable must be exactly {(p_i - 1) k_i}.  None if (M) unsolvable."""
    t = len(P)
    M, b, cols = reduced_system(P, K, S, TH, use_b=False)
    if not eliminate(to_u64(M), np.array([x % MOD for x in b], dtype=np.uint64))[0]:
        return None

    def o(n):
        r = 1
        for i in n:
            r *= (P[i] - 1) >> S[i]
        return r
    good = True
    for i in range(t):
        rest = [j for j in range(t) if j != i]
        Pi = 1
        for j in rest:
            Pi *= 1 + (P[j] - 1) * K[j]
        row = [o(n) if i not in n else 0 for (n, x) in cols]
        sols = []
        for c in range(0, 1 << (S[i] + 1), 2):
            M2 = [r + [0] for r in M] + [row + [1 << S[i]]]
            b2 = b + [(c - (Pi - 1)) // 2]
            ok, piv, _ = eliminate(to_u64(M2), np.array([x % MOD for x in b2], dtype=np.uint64))
            assert len(piv) == len(M2)
            if ok:
                sols.append(c)
        good = good and sols == [((P[i] - 1) * K[i]) % (1 << (S[i] + 1))]
    return good


def _group_ring(sizes):
    t = len(sizes)
    pts = list(product(*[range(k) for k in sizes]))
    idx = {y: i for i, y in enumerate(pts)}

    def mul(a, b):
        out = {}
        for x, va in a.items():
            for y, vb in b.items():
                z = tuple((x[j] + y[j]) % sizes[j] for j in range(t))
                out[z] = out.get(z, 0) + va * vb
        return {k: v for k, v in out.items() if v}

    def rows_of(g):
        res = []
        for y in pts:
            row = [0] * len(pts)
            for k, v in mul(g, {y: 1}).items():
                row[idx[k]] = v
            res.append(row)
        return res
    return pts, idx, mul, rows_of


def abstract_lemma_D(P, S, U):
    """Lemma D with coefficient ring Z_(2): I = prod_p (N_p, p - u_p) equals I# = {x : x Delta_n in a_n Lambda}.
    Since I <= I# always and I# is the dual of J = sum_n gamma_n Lambda, it is enough to compare indices:
    v_2[Lambda : I] == v_2[J : Lambda].  U[i] = exponent vector of u_i (0 at position i)."""
    t = len(P)
    sizes = [1 << s for s in S]
    pts, idx, mul, rows_of = _group_ring(sizes)
    G = len(pts)
    zero = tuple([0] * t)
    one = {zero: 1}
    Np = [{tuple(k if j == i else 0 for j in range(t)): 1 for k in range(sizes[i])} for i in range(t)]
    subsets = [n for r in range(t + 1) for n in combinations(range(t), r)]
    rowsI, dataJ = [], []
    for n in subsets:
        g = one
        for i in range(t):
            if i in n:
                a = {zero: P[i]}
                a[tuple(U[i])] = a.get(tuple(U[i]), 0) - 1
                g = mul(g, a)
            else:
                g = mul(g, Np[i])
        rowsI += rows_of(g)
        g, den = one, 1
        for i in n:                        # (p - u^-1)^-1 = Theta / (p^N - 1),  times (1 - c_i^-1)
            u = tuple((-v) % sizes[j] for j, v in enumerate(U[i]))
            th, z, N = {}, zero, 0
            while True:
                N += 1
                z2 = tuple((z[j] + u[j]) % sizes[j] for j in range(t))
                if z2 == zero:
                    break
                z = z2
            z = zero
            for j in range(N):
                th[z] = th.get(z, 0) + P[i] ** (N - 1 - j)
                z = tuple((z[k] + u[k]) % sizes[k] for k in range(t))
            g = mul(g, th)
            den *= P[i] ** N - 1
            g = mul(g, {zero: 1, tuple((-1) % sizes[j] if j == i else 0 for j in range(t)): -1})
        dataJ.append((g, den))
    Kmax = max(v2(den) for g, den in dataJ)
    rowsJ = []
    for g, den in dataJ:
        sc = 1 << (Kmax - v2(den))
        rowsJ += [[v * sc for v in row] for row in rows_of(g)]
    pI = eliminate(to_u64(rowsI))[1]
    pJ = eliminate(to_u64(rowsJ))[1]
    assert len(pI) == G and len(pJ) == G
    return sum(pI) == Kmax * G - sum(pJ)


def abstract_lemma_KL(P, S, TH):
    """Lemma KL: index 0 is the distinguished group C_0, 1..t-1 the primes of m.  Every C_0-invariant element
    N_0 w of I = prod_{p in m} (N_p, p - u_p) has eps(w) = 0 mod |S_m|.  Returns the least v_2(eps(w))
    and s_m (they must be equal: N_0 N_m itself lies in I)."""
    t = len(P)
    sizes = [1 << s for s in S]
    pts = list(product(*[range(k) for k in sizes]))
    pidx = {y: i for i, y in enumerate(pts)}
    m = list(range(1, t))
    colsM = []
    for n in [n for r in range(t) for n in combinations(m, r)]:
        for x in product(range(sizes[0]), *[range(sizes[i]) for i in n]):
            phi = {y: 1 for y in pts if y[0] == x[0] and all(y[i] == x[a + 1] for a, i in enumerate(n))}
            for i in n:
                new = {}
                for y, val in phi.items():
                    new[y] = new.get(y, 0) + P[i] * val
                    y2 = tuple((y[j] - (TH[j][i] if j != i else 0)) % sizes[j] for j in range(t))
                    new[y2] = new.get(y2, 0) - val
                phi = new
            col = [0] * len(pts)
            for y, val in phi.items():
                col[pidx[y]] = val
            colsM.append(col)
    ny = len(colsM)
    wpts = list(product(*[range(sizes[i]) for i in m]))
    for wv in wpts:
        colsM.append([-1 if y[1:] == wv else 0 for y in pts])
    A = [list(r) for r in zip(*colsM)]
    sm = sum(S[1:])
    for j in range(sm + 2):
        A2 = [r + [0] for r in A] + [[0] * ny + [1] * len(wpts) + [1 << (sm + 1)]]
        b2 = [0] * len(A) + [1 << j]
        ok, piv, _ = eliminate(to_u64(A2), np.array(b2, dtype=np.uint64))
        assert len(piv) == len(A2) and max(piv) < 60
        if ok:
            return j, sm
    return sm + 2, sm


def abstract_tests(seed=0, scale=1, verbose=True):
    rng = random.Random(seed)
    res = {"theoremA": [0, 0], "lemmaD": [0, 0], "lemmaKL": [0, 0], "nonsquare survivors": [0, 0]}
    for t, smax, trials in [(2, 3, 30), (3, 2, 30), (3, 3, 6), (4, 1, 15)]:
        for _ in range(trials * scale):
            P, K, S, TH = random_abstract(rng, t, smax)
            r = abstract_theorem_A(P, K, S, TH)
            if r is not None:
                res["theoremA"][0] += 1
                res["theoremA"][1] += 0 if r else 1
            if any(k % 2 for k in K):
                res["nonsquare survivors"][0] += 1
                res["nonsquare survivors"][1] += 1 if reduced_solvable(P, K, S, TH) else 0
            U = [[0 if j == i else rng.randrange(1 << S[j]) for j in range(t)] for i in range(t)]
            res["lemmaD"][0] += 1
            res["lemmaD"][1] += 0 if abstract_lemma_D(P, S, U) else 1
            j, sm = abstract_lemma_KL(P, S, TH)
            res["lemmaKL"][0] += 1
            res["lemmaKL"][1] += 0 if j == sm else 1
    if verbose:
        for k, (n, bad) in res.items():
            print("abstract test %-20s instances: %4d  failures: %d" % (k, n, bad), flush=True)
    return all(bad == 0 for n, bad in res.values())


# --------------------------------------------------------------------------------------------------
# 8. known results (as stated in the two research reports; the papers were not read)
# --------------------------------------------------------------------------------------------------
def known_cover(q):
    fac = factorint(q)
    lab = []
    if isprime(q):
        lab.append("prime (BBW 1973)")
    if 2 * int(totient(q)) + 1 > q:
        lab.append("Okada: 2 phi(q)+1 > q")
    if q % 4 == 3:
        lab.append("q = 3 mod 4 (Murty-Saradha 2010)")
    if sum(Fr(1, int(totient(d))) for d in divisors(q) if d >= 3) < 1:
        lab.append("Chatterjee-Murty Prop 3.1")
    if min(fac) >= len(divisors(q)):
        lab.append("Chatterjee-Murty Cor 3.3")
    for p in fac:                           # Bharadwaj Cor 1: q = p N, N = 3 mod 4 squarefree, p large
        if fac[p] == 1:
            fN = factorint(q // p)
            if (q // p) % 4 == 3 and all(e == 1 for e in fN.values()):
                bound = 2 ** len(fN)
                for l in fN:
                    bound *= (l + 1) ** 2 + 1
                if p > bound:
                    lab.append("Bharadwaj Cor 1")
    return lab


def known_report(limit):
    new, open_sq, total, cov = [], [], 0, 0
    for q in range(9, limit + 1, 4):
        if isprime(q):
            continue
        total += 1
        lab = known_cover(q)
        cov += 1 if lab else 0
        if not lab:
            (open_sq if is_square(q) else new).append(q)
    print("composite q = 1 mod 4 up to %d: %d;  covered by a listed known result: %d" % (limit, total, cov))
    print("covered by no listed known result but NOT a square (settled by the parity theorem): %d" % len(new))
    print("first twenty:", ", ".join("%d = %s" % (q, "*".join("%d^%d" % (p, k) if k > 1 else str(p)
                                                               for p, k in sorted(factorint(q).items())))
                                     for q in new[:20]))
    print("squares covered by no listed known result (open):", open_sq)
    return new, open_sq


# --------------------------------------------------------------------------------------------------
# 9. scans and self-test
# --------------------------------------------------------------------------------------------------
def scan(lo, hi, method, max_unknowns=1500):
    """For odd composite q in [lo, hi]: parity test; reports every q whose answer differs from 'survives iff
    q is a square'.  method = 'direct' (A) or 'reduced' (B; also tests the (a)-only prediction)."""
    t0 = time.time()
    n, bad, skipped = 0, [], []
    for q in range(lo | 1, hi + 1, 2):
        fac = factorint(q)
        if isprime(q):
            continue
        if method == "direct":
            res = parity_direct(q)
        else:
            unk = 1
            for p in fac:
                unk *= 1 + (1 << v2(p - 1))
            if unk > max_unknowns:
                skipped.append(q)
                continue
            res = parity_reduced(q)
            if len(fac) > 1 and parity_reduced(q, use_b=False) != predicted_a_only(q):
                bad.append((q, "(a)-only prediction"))
        n += 1
        if res != is_square(q):
            bad.append((q, "survives" if res else "killed"))
    print("%s scan %d..%d: %d odd composite q tested, unexpected: %s, skipped (system too large): %s, %.0f s"
          % (method, lo, hi, n, bad, skipped, time.time() - t0), flush=True)
    return bad


def selftest():
    t0 = time.time()
    ok = True
    print("[1] criterion, 60 digits")
    ok &= test_criterion([9, 15, 21, 25, 27, 35, 45, 63, 75, 105], verbose=True)
    try:
        import flint  # noqa: F401
        print("[1b] LLL completeness")
        ok &= lll_completeness([9, 15, 21, 25, 27, 33, 35], verbose=True)
    except ImportError:
        print("[1b] python-flint not available: LLL test skipped")
    print("[2] methods A and B agree, survivors are exactly the squares, q <= 400")
    for q in range(9, 401, 2):
        if isprime(q):
            continue
        a, b = parity_direct(q), parity_reduced(q)
        if not (a == b == is_square(q)):
            ok = False
            print("   MISMATCH at", q, a, b)
    print("[3] brute force (+-1 values, no parity argument)")
    for q in [9, 15, 21, 25, 27, 33, 35, 39, 45, 49, 51, 55]:
        cnt, tot = brute_force_pm1(q)
        print("   q=%2d: %d of %d sign patterns on the non-units give a +-1 solution; parity test: %s"
              % (q, cnt, tot, "survives" if parity_direct(q) else "killed"), flush=True)
        ok &= cnt == 0
    print("[4] Theorem A on explicit odd-valued solutions of (a)")
    for q in [21, 45, 65, 105, 117, 153, 165, 189, 225, 273]:
        r = check_theorem_A(q)
        print("   q=%3d: %s" % (q, "no odd-valued solution of (a)" if r is None else
                                "%d distinct values; (p, k, s, v_2(sum - (p-1)k)) = %s  %s"
                                % (r[2], r[1], "OK" if r[0] else "VIOLATION")), flush=True)
        ok &= r is None or r[0]
    print("[4b] the main equation (M) and Lemma 1, exact, on explicit functions")
    rng = random.Random(5)
    for q in [15, 21, 45, 63, 105, 117, 225]:
        holds, fails, lem1 = check_main_equation(q, rng)
        print("   q=%3d: (M) for a random solution of (a): %s; fails for a random f: %s; odd-valued solution, "
              "(M) and Lemma 1: %s" % (q, holds, fails, lem1), flush=True)
        ok &= holds and fails and lem1 is not False
    n, bad = check_theorem_B([9, 15, 27, 45, 63, 75, 105, 135, 225, 243, 315, 441, 675, 1125], random.Random(3))
    print("[4c] Theorem B congruence on random odd-valued f: %d cases, %d failures" % (n, bad))
    ok &= bad == 0
    print("[5] abstract tests of Lemma D, Lemma KL, Theorem A")
    ok &= abstract_tests(seed=1, verbose=True)
    print("[6] squares: explicit odd-valued vanishing functions")
    import mpmath as mp
    for q in [9, 25, 225, 441, 1225]:
        f = square_example(q)
        val = L1(f, q)
        good = sum(f) == 0 and all(v2q(x) == 0 for x in f[1:]) and abs(val) < mp.mpf(10) ** -60
        print("   q=%5d: |L(1,f)| = %s, all values odd: %s" % (q, mp.nstr(abs(val), 3), good), flush=True)
        ok &= good
    print("SELFTEST", "PASSED" if ok else "FAILED", "(%.0f s)" % (time.time() - t0))
    return ok


def main(argv):
    cmd = argv[1] if len(argv) > 1 else "selftest"
    if cmd == "selftest":
        sys.exit(0 if selftest() else 1)
    elif cmd == "criterion":
        qs = [int(x) for x in argv[2:]] or [9, 15, 21, 25, 27, 33, 35, 45, 49, 63, 75, 81, 99, 105, 135, 147, 165, 225]
        print("ALL OK" if test_criterion(qs) else "FAILURE")
    elif cmd == "lll":
        qs = [int(x) for x in argv[2:]] or [9, 15, 21, 25, 27, 33, 35, 39, 45, 49, 51, 55, 63]
        print("ALL OK" if lll_completeness(qs) else "FAILURE")
    elif cmd in ("direct", "reduced"):
        scan(int(argv[2]), int(argv[3]), cmd, int(argv[4]) if len(argv) > 4 else 1500)
    elif cmd == "brute":
        for q in [int(x) for x in argv[2:]] or [9, 15, 21, 25, 27, 33, 35, 39, 45, 49, 51, 55, 57, 65, 77, 85, 91]:
            r = brute_force_pm1(q)
            print("q=%3d:" % q, "too many non-units" if r is None else
                  "%d +-1 solutions among %d sign patterns; parity test: %s"
                  % (r[0], r[1], "survives" if parity_direct(q) else "killed"), flush=True)
    elif cmd == "theoremA":
        for q in [int(x) for x in argv[2:]] or [21, 33, 45, 57, 65, 69, 77, 105, 117, 145, 153, 165, 189, 225, 273,
                                                 285, 297, 345, 357, 385, 425, 465, 585, 765]:
            r = check_theorem_A(q)
            print("q=%4d:" % q, "no odd-valued solution of (a)" if r is None else
                  "%d distinct values; (p, k, s, v_2(sum - (p-1)k)) = %s  %s" % (r[2], r[1], "OK" if r[0] else "VIOLATION"),
                  flush=True)
    elif cmd == "mainequation":
        rng = random.Random(5)
        for q in [int(x) for x in argv[2:]] or [15, 21, 45, 63, 75, 105, 117, 135, 165, 225, 273, 315, 495, 525]:
            print("q=%4d: (M) for a random solution of (a): %s; fails for a random f: %s; odd-valued solution, "
                  "(M) and Lemma 1: %s" % ((q,) + check_main_equation(q, rng)), flush=True)
    elif cmd == "abstract":
        print("ALL OK" if abstract_tests(seed=int(argv[2]) if len(argv) > 2 else 0,
                                         scale=int(argv[3]) if len(argv) > 3 else 3) else "FAILURE")
    elif cmd == "squares":
        import mpmath as mp
        for q in [int(x) for x in argv[2:]] or [9, 25, 49, 81, 225, 441, 1225, 2025, 11025]:
            f = square_example(q)
            print("q=%5d: values %s ...; sum of f(n)/n = %s" % (q, [str(v) for v in sorted(set(f[1:]))][:8],
                                                             mp.nstr(L1(f, q), 5)), flush=True)
    elif cmd == "known":
        known_report(int(argv[2]) if len(argv) > 2 else 10000)
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv)
