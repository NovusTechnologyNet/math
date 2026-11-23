#!/usr/bin/env python
"""Referee checks for research/2026-11-23-erdos-pm1/00_summary.md.

Written from the definitions in that document; it does not import or read python/erdos_pm1_check.py.

Setting: q odd, P = primes of q, k_p = v_p(q), M(q) = integers >= 1 all of whose prime factors are in P.
For f: Z/q -> Q:
    g(a) = sum_{m in M(q)} f(a m)/m                      (a a unit mod q)
    c_p  = sum_{r=1..q} f(r) lam(r,p),  lam(r,p) = v_p(r) if v_p(r) < k_p, else k_p + 1/(p-1).
(a): g(a) = 0 for all units a.   (b): c_p = 0 for all p in P.

Commands (all output is ASCII):
    selftest                 quick run of every check (well under a minute)
    part1                    Part I: exact identities and 60-digit numerics for the formula and the criterion
    refute LO HI             exact 2-adic decision "is there an odd-valued f with (a),(b)?", every odd composite
                             q in [LO,HI], by the FULL system (unknowns f(r), r = 1..q-1)
    orbit LO HI [MAXORB]     the same decision by the orbit-reduced system (f constant on the orbits of the
                             odd-order part of (Z/q)^*; justified by averaging, see class Orb)
    special                  special q (many primes, primes with large v_2(p-1), ...)
    squares                  odd squares: explicit odd-valued solutions (mine, and formula 6.3), exact + numeric
    part2                    Lemma 1, Lemma 2 (M), Theorems A and B on explicit odd-valued solutions of (a)
    abstract [N]             Lemma D, Lemma KL, abstract Theorem A on random data
    aonly LO HI              the "(a) alone" classification claimed in section 6.1
    lll                      integer relations among psi(r/q) by LLL (needs python-flint)
"""
import sys
import random
import itertools
import time
from fractions import Fraction as Fr
from math import gcd

import numpy as np

M64 = 1 << 64
MAXU = np.uint64(0xFFFFFFFFFFFFFFFF)
ONE = np.uint64(1)


# ----------------------------------------------------------------------------------------------
# elementary number theory
# ----------------------------------------------------------------------------------------------
def factor(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def divisors(n):
    ds = [1]
    for p, k in factor(n).items():
        ds = [d * p ** j for d in ds for j in range(k + 1)]
    return sorted(ds)


def v2(n):
    assert n != 0
    return (n & -n).bit_length() - 1


def v2_fr(x):
    """2-adic valuation of a non-zero Fraction."""
    return v2(x.numerator) - v2(x.denominator)


def is_odd_fr(x):
    return x != 0 and x.numerator % 2 == 1 and x.denominator % 2 == 1


def mult_order(a, N):
    if N == 1:
        return 1
    a %= N
    assert gcd(a, N) == 1
    x, e = a, 1
    while x != 1:
        x = x * a % N
        e += 1
    return e


def is_square(n):
    r = int(round(n ** 0.5))
    while r * r > n:
        r -= 1
    while (r + 1) * (r + 1) <= n:
        r += 1
    return r * r == n


def prim_root(p):
    fs = list(factor(p - 1))
    for g in range(2, p):
        if all(pow(g, (p - 1) // l, p) != 1 for l in fs):
            return g
    raise ValueError(p)


def dlog_table(p):
    g = prim_root(p)
    tab = [None] * p
    x = 1
    for e in range(p - 1):
        tab[x] = e
        x = x * g % p
    return tab


def lam(fac, r, p):
    """lam(r,p) of the document, r in 1..q."""
    k = fac[p]
    v = 0
    while v < k and r % p == 0:
        r //= p
        v += 1
    return Fr(v) if v < k else Fr(k) + Fr(1, p - 1)


def c_lam(q, fac, f, p):
    return sum(f[r % q] * lam(fac, r, p) for r in range(1, q + 1))


# ----------------------------------------------------------------------------------------------
# ground truth: g(a) and sum_a sum_m f(am) v_p(m)/m computed from the definition as sums over M(q)
# (the exponent of each prime is split into finitely many classes on which p^e mod q is constant)
# ----------------------------------------------------------------------------------------------
def exp_classes(q, p, k):
    """classes of exponents e >= 0: p^e mod q is constant on each class.
    returns (representative e, S0 = sum over the class of p^-e, S1 = sum over the class of e p^-e)."""
    L = mult_order(p, q // p ** k)
    out = [(i, Fr(1, p ** i), Fr(i, p ** i)) for i in range(k)]
    x = Fr(1, p ** L)
    for j in range(L):
        e = k + j
        out.append((e, Fr(1, p ** e) / (1 - x), Fr(1, p ** e) * (Fr(e) / (1 - x) + L * x / (1 - x) ** 2)))
    return out


def g_def(q, fac, f, a):
    ps = sorted(fac)
    cls = [exp_classes(q, p, fac[p]) for p in ps]
    tot = Fr(0)
    for combo in itertools.product(*cls):
        m, w = 1, Fr(1)
        for p, (e, S0, S1) in zip(ps, combo):
            m = m * pow(p, e, q) % q
            w *= S0
        tot += f[a * m % q] * w
    return tot


def c_def(q, fac, f, p0):
    """sum over units a and m in M(q) of f(am) v_p0(m)/m, exactly."""
    ps = sorted(fac)
    cls = [exp_classes(q, p, fac[p]) for p in ps]
    i0 = ps.index(p0)
    # weight of each residue m mod q
    wt = {}
    for combo in itertools.product(*cls):
        m, w = 1, Fr(1)
        for i, (p, (e, S0, S1)) in enumerate(zip(ps, combo)):
            m = m * pow(p, e, q) % q
            w *= S1 if i == i0 else S0
        wt[m] = wt.get(m, 0) + w
    tot = Fr(0)
    for a in range(1, q):
        if gcd(a, q) == 1:
            for m, w in wt.items():
                tot += f[a * m % q] * w
    return tot


def smooth_numbers(ps, bound):
    out = [1]
    for p in ps:
        new = []
        for m in out:
            x = m
            while x <= bound:
                new.append(x)
                x *= p
        out = new
    return out


# ----------------------------------------------------------------------------------------------
# coefficient of f(r) in g(a):  w(a,r) = sum_{m in M(q), am = r mod q} 1/m
# For gcd(r,q) = d, N = q/d: m = d * prod_{p not dividing N} p^(j_p), j_p >= 0, and the condition is
# a * prod p^(j_p) = r/d (mod N).
# ----------------------------------------------------------------------------------------------
def tb_tables(q, fac):
    ps = sorted(fac)
    tabs = {}
    for N in divisors(q):
        if N == 1:
            continue
        others = [(p, mult_order(p, N)) for p in ps if N % p != 0]
        tab = {}
        for js in itertools.product(*[range(L) for (p, L) in others]):
            u, w = 1, Fr(1)
            for (p, L), j in zip(others, js):
                u = u * pow(p, j, N) % N
                w *= Fr(1, p ** j) / (1 - Fr(1, p ** L))
            tab[u] = tab.get(u, 0) + w
        tabs[N] = tab
    return tabs


class Full:
    """the full system for q: coordinates r = 1..q-1."""

    def __init__(self, q):
        self.q = q
        self.fac = factor(q)
        self.ps = sorted(self.fac)
        self.units = [a for a in range(1, q) if gcd(a, q) == 1]
        self.nonunits = [r for r in range(1, q) if gcd(r, q) > 1]
        self.tabs = tb_tables(q, self.fac)
        self.ainv = {a: pow(a, -1, q) for a in self.units}

    def w(self, a, r):
        q = self.q
        d = gcd(r, q)
        N = q // d
        u = self.ainv[a] * (r // d) % N
        x = self.tabs[N].get(u, 0)
        return x / d if x else Fr(0)

    def g(self, f, a):
        """g(a) through the coefficients w(a,r)."""
        return f[a] + sum(self.w(a, r) * f[r] for r in self.nonunits if f[r] != 0)

    def cp(self, f, p):
        return c_lam(self.q, self.fac, f, p)

    def b_pivots(self):
        """for each p a non-unit r_p != 0 with lam(r_p,p) != 0 and lam(r_p,p') = 0 for p' != p."""
        if len(self.ps) >= 2:
            return {p: p ** self.fac[p] for p in self.ps}
        p = self.ps[0]
        assert self.fac[p] >= 2
        return {p: p}

    def complete(self, vals, with_b=True):
        """vals: dict non-unit r -> value on the FREE non-units (all non-units if not with_b).
        Returns the unique f (list of length q, f[0] = 0) with these values and (a) [and (b)]."""
        q = self.q
        f = [Fr(0)] * q
        for r, x in vals.items():
            f[r] = Fr(x)
        if with_b:
            piv = self.b_pivots()
            for p, rp in piv.items():
                assert rp not in vals
                rest = sum(f[r] * lam(self.fac, r, p) for r in self.nonunits if r != rp)
                f[rp] = -rest / lam(self.fac, rp, p)
        for a in self.units:
            f[a] = -sum(self.w(a, r) * f[r] for r in self.nonunits if f[r] != 0)
        return f

    def basis(self, with_b=True):
        """exact basis of the solution space of (a) [and (b)]: one vector for each free non-unit r0
        (value 1 at r0, 0 at the other free non-units). Returns (free list, rows); rows are lists over
        r = 1..q-1."""
        piv = self.b_pivots() if with_b else {}
        pivset = set(piv.values())
        free = [r for r in self.nonunits if r not in pivset]
        # column of w for each non-unit
        wcol = {r: [self.w(a, r) for a in self.units] for r in self.nonunits}
        rows = []
        for r0 in free:
            row = [Fr(0)] * (self.q - 1)
            row[r0 - 1] = Fr(1)
            ucol = [-x for x in wcol[r0]]
            for p, rp in piv.items():
                l0 = lam(self.fac, r0, p)
                if l0 != 0:
                    rho = l0 / lam(self.fac, rp, p)
                    row[rp - 1] = -rho
                    ucol = [x + rho * y for x, y in zip(ucol, wcol[rp])]
            for a, x in zip(self.units, ucol):
                row[a - 1] = x
            rows.append(row)
        return free, rows


# ----------------------------------------------------------------------------------------------
# exact 2-adic linear algebra modulo 2^64 (numpy uint64 wraps modulo 2^64)
# ----------------------------------------------------------------------------------------------
def fr_to_u64(x, shift):
    """x * 2^shift modulo 2^64 for a Fraction x with v_2(x) >= -shift."""
    if x == 0:
        return 0
    den = x.denominator
    e = v2(den)
    assert shift >= e
    return (x.numerator << (shift - e)) * pow(den >> e, -1, M64) % M64


def rows_to_u64(rows):
    """each row is multiplied by the least power of 2 making it 2-adically integral.
    returns (uint64 matrix, list of shifts)."""
    A = np.zeros((len(rows), len(rows[0]) if rows else 0), dtype=np.uint64)
    shifts = []
    for i, row in enumerate(rows):
        sh = 0
        for x in row:
            if x != 0:
                e = v2(x.denominator)
                if e > sh:
                    sh = e
        shifts.append(sh)
        A[i, :] = np.array([fr_to_u64(x, sh) for x in row], dtype=np.uint64)
    return A, shifts


def z2_echelon(A, npiv=None):
    """Elimination with full pivoting: at each step the pivot is an entry of least 2-adic valuation of the
    remaining rows (searched in the first npiv columns). All multipliers are 2-adic integers and every
    operation is exact modulo 2^64 on the first npiv columns. Returns (A', piv): row i of A' has its pivot
    in column piv[i][0] with valuation piv[i][1]; the first npiv entries of row i are divisible by
    2^piv[i][1]; rows below have 0 in the pivot column; the valuations are non-decreasing.
    Rows beyond len(piv) are 0 modulo 2^64 on the first npiv columns."""
    A = A.copy()
    r, n = A.shape
    if npiv is None:
        npiv = n
    piv = []
    for i in range(r):
        sub = A[i:, :npiv]
        lb = sub & (~sub + ONE)
        lb[lb == 0] = MAXU
        j = int(np.argmin(lb))
        mn = int(lb.reshape(-1)[j])
        if mn == int(MAXU):
            break
        v = mn.bit_length() - 1
        ri, c = i + j // npiv, j % npiv
        if ri != i:
            A[[i, ri]] = A[[ri, i]]
        inv = np.uint64(pow(int(A[i, c]) >> v, -1, M64))
        if i + 1 < r:
            mult = (A[i + 1:, c] >> np.uint64(v)) * inv
            nz = np.nonzero(mult)[0]
            if len(nz):
                A[i + 1 + nz, :] -= np.outer(mult[nz], A[i, :])
        piv.append((c, v))
    return A, piv


def ones_in_span(R, piv):
    """R, piv from z2_echelon of a matrix with independent rows (len(piv) = number of rows).
    The rows R[i] / 2^v_i form a basis of the 2-saturation of the row lattice; decide whether a vector with
    all coordinates odd lies in it. Returns (bool, coefficient list in F_2)."""
    n = R.shape[1]
    res = np.ones(n, dtype=np.uint8)
    coefs = []
    for i, (c, v) in enumerate(piv):
        if res[c]:
            res ^= ((R[i, :] >> np.uint64(v)) & ONE).astype(np.uint8)
            coefs.append(1)
        else:
            coefs.append(0)
    return (not res.any()), coefs


def odd_point(rows, free_idx, want_solution=False, rng=None, nvariants=0):
    """rows: exact basis (Fractions) of a subspace V of Q^n such that row j has 1 at coordinate free_idx[j]
    and 0 at the other free coordinates. Decide whether V contains a vector all of whose coordinates are
    units of Z_(2). Returns (exists, maxval, sols): maxval = largest pivot valuation; sols = list of exact
    solutions (lists of Fractions) if want_solution."""
    if not rows:
        return False, 0, []
    A, shifts = rows_to_u64(rows)
    R, piv = z2_echelon(A)
    if len(piv) < len(rows):
        raise ArithmeticError("pivot valuation >= 64: precision of 64 bits is not enough")
    maxval = max(v for c, v in piv)
    ok, coefs = ones_in_span(R, piv)
    sols = []
    if ok and want_solution:
        D = max(shifts)
        prec = 64 - maxval
        if prec < D + 2:
            raise ArithmeticError("not enough precision to extract a solution")
        mod = 1 << (D + 1)

        def exact_from(zs):
            # 2-adic vector  sum_i (coefs_i + 2 z_i) R_i / 2^v_i  on the free coordinates, modulo 2^(D+1)
            vals = []
            for j in free_idx:
                tot = 0
                for i, (c, v) in enumerate(piv):
                    cf = coefs[i] + 2 * zs[i]
                    if cf:
                        tot += cf * (int(R[i, j]) >> v)
                vals.append(tot % mod)
            return vals

        zlist = [[0] * len(piv)]
        for _ in range(nvariants):
            zlist.append([rng.randint(0, 3) for _ in piv])
        for zs in zlist:
            vals = exact_from(zs)
            if rng is not None and zs is not zlist[0]:
                vals = [x + mod * rng.randint(-2, 2) for x in vals]
            n = len(rows[0])
            f = [Fr(0)] * n
            for x, row in zip(vals, rows):
                if x:
                    for jj, y in enumerate(row):
                        if y != 0:
                            f[jj] += x * y
            assert all(is_odd_fr(x) for x in f), "extracted vector is not odd-valued"
            sols.append(f)
    return ok, maxval, sols


def decide_full(q, with_b=True, want_solution=False, rng=None, nvariants=0):
    """is there f: Z/q -> Q, f(0) = 0, f(r) odd for r != 0, with (a) [and (b)]?  (full system)"""
    F = Full(q)
    if not F.nonunits:
        return False, 0, []
    if with_b and len(F.ps) == 1 and F.fac[F.ps[0]] == 1:
        return False, 0, []
    free, rows = F.basis(with_b)
    if not rows:
        return False, 0, []
    ok, mv, sols = odd_point(rows, [r - 1 for r in free], want_solution, rng, nvariants)
    return ok, mv, [[Fr(0)] + s for s in sols]


# ----------------------------------------------------------------------------------------------
# orbit-reduced system. H = subgroup of odd order of (Z/q)^* ... more precisely the kernel of
# (Z/q)^* -> S_P = prod_p (Z/p)^*/(odd part). H has odd order and acts on Z/q by multiplication.
# If f is an odd-valued solution of (a),(b) then so is its average over H (g(ha) = g_h(a), c_p is
# invariant, an average of an odd number of odd values is odd). So it is enough to look for solutions
# constant on H-orbits. The orbits of non-zero r are the pairs (N, sigma): N = q/gcd(r,q) > 1,
# sigma = class of r/gcd(r,q) in S_n, n = primes of N; the orbit has phi(N)/2^(s_n) elements.
# ----------------------------------------------------------------------------------------------
class Orb:
    def __init__(self, q):
        self.q = q
        self.fac = factor(q)
        self.ps = sorted(self.fac)
        self.t = len(self.ps)
        self.s = {p: v2(p - 1) for p in self.ps}
        self.ordr = {p: 1 << self.s[p] for p in self.ps}
        self.dl = {p: dlog_table(p) for p in self.ps}
        self.divs = [N for N in divisors(q) if N > 1]
        self.nset = {N: tuple(p for p in self.ps if N % p == 0) for N in self.divs}
        self.orbits = []
        for N in self.divs:
            for sig in itertools.product(*[range(self.ordr[p]) for p in self.nset[N]]):
                self.orbits.append((N, sig))
        self.index = {o: i for i, o in enumerate(self.orbits)}
        self.tbk = {N: self._tbk(N) for N in self.divs}

    def norbits(self):
        return len(self.orbits)

    def cls(self, u, n):
        return tuple(self.dl[p][u % p] % self.ordr[p] for p in n)

    def orbit_of(self, r):
        q = self.q
        d = gcd(r, q)
        N = q // d
        return (N, self.cls(r // d, self.nset[N]))

    def size(self, N):
        # phi(N) / 2^(s_n)
        ph = N
        for p in self.nset[N]:
            ph = ph // p * (p - 1)
        for p in self.nset[N]:
            ph //= self.ordr[p]
        return ph

    def _tbk(self, N):
        """tau in S_n -> sum over tuples j >= 0 (primes not dividing N) with prod [p]^j_p = tau of prod p^-j_p."""
        n = self.nset[N]
        others = [p for p in self.ps if N % p != 0]
        gens = [self.cls(p, n) for p in others]
        ords = []
        for gcl in gens:
            L = 1
            for comp, p in zip(gcl, n):
                o = self.ordr[p] // gcd(comp, self.ordr[p])
                L = max(L, o)
            ords.append(L)
        tab = {}
        for js in itertools.product(*[range(L) for L in ords]):
            tau = [0] * len(n)
            w = Fr(1)
            for p, gcl, L, j in zip(others, gens, ords, js):
                for i in range(len(n)):
                    tau[i] += j * gcl[i]
                w *= Fr(1, p ** j) / (1 - Fr(1, p ** L))
            tau = tuple(x % self.ordr[p] for x, p in zip(tau, n))
            tab[tau] = tab.get(tau, 0) + w
        return tab

    def W(self, x, N, sig):
        """coefficient of f(N,sig) in g(a) for a unit a of class x (x a tuple over all primes)."""
        n = self.nset[N]
        xn = tuple(x[self.ps.index(p)] for p in n)
        tau = tuple((s_ - x_) % self.ordr[p] for s_, x_, p in zip(sig, xn, n))
        val = self.tbk[N].get(tau, 0)
        return val / (self.q // N) if val else Fr(0)

    def lamN(self, N, p):
        k = self.fac[p]
        if N % p == 0:
            e = 0
            M = N
            while M % p == 0:
                M //= p
                e += 1
            return Fr(k - e)
        return Fr(k) + Fr(1, p - 1)

    def b_pivots(self):
        if self.t >= 2:
            return {p: (self.q // p ** self.fac[p], tuple(0 for _ in self.ps if _ != p)) for p in self.ps}
        p = self.ps[0]
        assert self.fac[p] >= 2
        return {p: (self.q // p, (0,))}

    def basis(self, with_b=True):
        q = self.q
        piv = self.b_pivots() if with_b else {}
        pivset = set(piv.values())
        unit_orbs = [o for o in self.orbits if o[0] == q]
        non = [o for o in self.orbits if o[0] != q]
        free = [o for o in non if o not in pivset]
        wcol = {o: [self.W(x[1], o[0], o[1]) for x in unit_orbs] for o in non}
        rows = []
        for o0 in free:
            row = [Fr(0)] * len(self.orbits)
            row[self.index[o0]] = Fr(1)
            ucol = [-x for x in wcol[o0]]
            for p, op in piv.items():
                l0 = self.lamN(o0[0], p) * self.size(o0[0])
                if l0 != 0:
                    rho = l0 / (self.lamN(op[0], p) * self.size(op[0]))
                    row[self.index[op]] = -rho
                    ucol = [x + rho * y for x, y in zip(ucol, wcol[op])]
            for x, val in zip(unit_orbs, ucol):
                row[self.index[x]] = val
            rows.append(row)
        return free, rows

    def expand(self, F):
        """orbit vector -> f on Z/q."""
        q = self.q
        f = [Fr(0)] * q
        for r in range(1, q):
            f[r] = F[self.index[self.orbit_of(r)]]
        return f


def decide_orbit(q, with_b=True, want_solution=False, rng=None, nvariants=0, maxorb=None):
    O = Orb(q)
    if maxorb is not None and O.norbits() > maxorb:
        return None, 0, []
    if all(o[0] == q for o in O.orbits):
        return False, 0, []
    if with_b and O.t == 1 and O.fac[O.ps[0]] == 1:
        return False, 0, []
    free, rows = O.basis(with_b)
    if not rows:
        return False, 0, []
    ok, mv, sols = odd_point(rows, [O.index[o] for o in free], want_solution, rng, nvariants)
    return ok, mv, [O.expand(s) for s in sols]


# ----------------------------------------------------------------------------------------------
# Part I
# ----------------------------------------------------------------------------------------------
def rand_fr(rng):
    return Fr(rng.choice([-1, 1]) * rng.randint(1, 9), rng.choice([1, 1, 2, 3, 4, 5, 7]))


def random_f(q, rng, zero_sum=True):
    f = [Fr(0)] + [rand_fr(rng) for _ in range(q - 1)]
    if zero_sum:
        f[q - 1] -= sum(f)
    return f


def mpf_of(x):
    import mpmath as mp
    return mp.mpf(x.numerator) / x.denominator


def series_psi(q, f):
    """sum_{n>=1} f(n)/n = -(1/q) sum_r f(r) psi(r/q) (valid when sum_r f(r) = 0)."""
    import mpmath as mp
    assert sum(f) == 0 and f[0] == 0
    return -sum(mpf_of(f[r]) * mp.digamma(mp.mpf(r) / q) for r in range(1, q) if f[r] != 0) / q


def series_direct(q, f):
    """the same sum by extrapolation of the partial sums over whole periods (no digamma)."""
    import mpmath as mp
    ff = [mpf_of(x) for x in f]

    def block(j):
        return sum(ff[r] / (j * q + r) for r in range(1, q))

    # partial sums over M = 32 * 2^k whole periods have an expansion in powers of 1/M: Richardson by hand
    # (mpmath's nsum with its default method is NOT reliable here: it returned 5 correct digits)
    vals = []
    acc = mp.mpf(0)
    j = 0
    for k in range(9):
        M = 32 * 2 ** k
        while j < M:
            acc += block(j)
            j += 1
        vals.append(acc)
    for lev in range(1, 9):
        vals = [(2 ** lev * vals[i + 1] - vals[i]) / (2 ** lev - 1) for i in range(len(vals) - 1)]
    return vals[0]


def formula_doc(F, f):
    """-(1/q) [ sum_a g(a) psi(a/q) + sum_p c_p log p ] with g, c_p exact."""
    import mpmath as mp
    q = F.q
    tot = mp.mpf(0)
    for a in F.units:
        ga = F.g(f, a)
        if ga != 0:
            tot += mpf_of(ga) * mp.digamma(mp.mpf(a) / q)
    for p in F.ps:
        tot += mpf_of(F.cp(f, p)) * mp.log(p)
    return -tot / q


def part1(qs_exact=(9, 15, 21, 27, 45, 63, 75, 99, 105, 135, 225),
          qs_num=(9, 15, 21, 25, 27, 33, 35, 45, 49, 63, 75, 81, 99, 105, 135, 147, 165, 225),
          seed=1, verbose=True):
    import mpmath as mp
    rng = random.Random(seed)
    out = print if verbose else (lambda *a, **k: None)
    # (1) truncated sums over M(q) against the closed forms (floating point)
    for q in (9, 15, 45, 75):
        fac = factor(q)
        ps = sorted(fac)
        f = random_f(q, rng, zero_sum=False)
        ms = smooth_numbers(ps, 10 ** 14)
        ff = [float(x) for x in f]
        a = rng.choice([a for a in range(1, q) if gcd(a, q) == 1])
        approx = sum(ff[a * m % q] / m for m in ms)
        exact = g_def(q, fac, f, a)
        assert abs(approx - float(exact)) < 1e-9, (q, approx, float(exact))
        for p in ps:
            def vpm(m):
                v = 0
                while m % p == 0:
                    m //= p
                    v += 1
                return v
            approx = sum(ff[b * m % q] * vpm(m) / m for m in ms for b in range(1, q) if gcd(b, q) == 1)
            exact = c_def(q, fac, f, p)
            assert abs(approx - float(exact)) < 1e-7, (q, p, approx, float(exact))
    out("part1 (1) closed forms for the sums over M(q) agree with truncated sums: q = 9, 15, 45, 75")
    # (2) exact: g via w(a,r) = g from the definition; c_p identity; sum_a g(a) = sum_r f(r)
    for q in qs_exact:
        F = Full(q)
        f = random_f(q, rng, zero_sum=False)
        gs = {a: F.g(f, a) for a in F.units}
        for a in (F.units if q <= 105 else rng.sample(F.units, 12)):
            assert gs[a] == g_def(q, F.fac, f, a), (q, a)
        assert sum(gs.values()) == sum(f), q
        for p in F.ps:
            assert c_def(q, F.fac, f, p) == c_lam(q, F.fac, f, p), (q, p)
        # the description of c_p through h = Mop f:  c_p = sum over {n: gcd(n,q) = p^i, 1 <= i <= k_p} h(n)
        h = {}
        for n in range(0, q):
            h[n] = g_def(q, F.fac, [f[(n * r) % q] for r in range(q)], 1)
        for p in F.ps:
            k = F.fac[p]
            tot = sum(h[n] for n in range(0, q) if gcd(n if n else q, q) in [p ** i for i in range(1, k + 1)])
            assert tot == c_lam(q, F.fac, f, p), (q, p, "Mop description of c_p")
        out("part1 (2) q = %d: g(a) [w-table] = g(a) [definition]; sum_a g(a) = sum_r f(r); "
            "c_p identity exact for p = %s; Mop description of c_p" % (q, F.ps))
    # (3) numerics
    mp.mp.dps = 75
    tol = mp.mpf(10) ** (-60)
    worst = mp.mpf(0)
    for q in qs_num:
        F = Full(q)
        # (3a) the formula for random rational f with sum 0
        f = random_f(q, rng)
        s1 = series_psi(q, f)
        s2 = formula_doc(F, f)
        assert abs(s1 - s2) < tol, (q, s1, s2)
        worst = max(worst, abs(s1 - s2))
        if q <= 35:
            mp.mp.dps = 30
            sd = series_direct(q, f)
            assert abs(sd - series_psi(q, f)) < mp.mpf(10) ** (-20), (q, sd)
            mp.mp.dps = 75
        # (3b) "if": random rational f with (a) and (b)
        free, rows = F.basis(True)
        if free:
            vals = {r: rand_fr(rng) for r in free}
            fs = F.complete(vals, True)
            assert all(F.g(fs, a) == 0 for a in F.units) and all(F.cp(fs, p) == 0 for p in F.ps)
            if q <= 49:
                assert all(g_def(q, F.fac, fs, a) == 0 for a in F.units)
            sv = series_psi(q, fs)
            assert abs(sv) < tol, (q, sv)
            worst = max(worst, abs(sv))
        # (3c) (a) but not (b): the sum is -(1/q) sum c_p log p, non-zero
        while True:
            vals = {r: rand_fr(rng) for r in F.nonunits}
            fa = F.complete(vals, False)
            cps = {p: F.cp(fa, p) for p in F.ps}
            if any(c != 0 for c in cps.values()):
                break
        assert all(F.g(fa, a) == 0 for a in F.units)
        sv = series_psi(q, fa)
        pred = -sum(mpf_of(c) * mp.log(p) for p, c in cps.items()) / q
        assert abs(sv - pred) < tol and abs(sv) > mp.mpf(10) ** (-6), (q, sv, pred)
        # (3d) (b) but not (a): non-zero
        f = random_f(q, rng)
        piv = F.b_pivots() if (len(F.ps) > 1 or F.fac[F.ps[0]] > 1) else {}
        if piv:
            for p, rp in piv.items():
                rest = sum(f[r] * lam(F.fac, r, p) for r in F.nonunits if r != rp)
                f[rp] = -rest / lam(F.fac, rp, p)
            f[1] -= sum(f)
            assert all(F.cp(f, p) == 0 for p in F.ps)
            sv = series_psi(q, f)
            assert abs(sv) > mp.mpf(10) ** (-6), (q, sv)
            assert abs(sv - formula_doc(F, f)) < tol
        out("part1 (3) q = %d: formula ok; f with (a),(b): |sum| < 1e-60; (a) only: sum = -(1/q) sum c_p log p"
            " = %s; (b) only: sum != 0" % (q, mp.nstr(pred, 12)))
    # (4) Gauss's formula, and the eigenvalues sum_a chi(a) psi(a/q) of the map g -> T
    for q in (9, 15, 21, 25, 45):
        for a in range(1, q):
            lhs = mp.digamma(mp.mpf(a) / q)
            rhs = (-mp.euler - mp.log(2 * q) - mp.pi / 2 * mp.cot(mp.pi * a / q)
                   + 2 * sum(mp.cos(2 * mp.pi * a * j / q) * mp.log(mp.sin(mp.pi * j / q))
                             for j in range(1, (q - 1) // 2 + 1)))
            assert abs(lhs - rhs) < tol, (q, a)
        us = [a for a in range(1, q) if gcd(a, q) == 1]
        idx = {a: i for i, a in enumerate(us)}
        mp.mp.dps = 30
        T = mp.matrix(len(us), len(us))
        for h in us:
            for b in us:
                # T(h) = sum_b g(b) psi(<h b>/q)   (the document's T(h^-1), same family)
                T[idx[h], idx[b]] = mp.digamma(mp.mpf(h * b % q) / q)
        sv = mp.svd_r(T, compute_uv=False)
        smin = min(sv)
        assert smin > mp.mpf(10) ** (-3), (q, smin)
        mp.mp.dps = 75
        out("part1 (4) q = %d: Gauss's formula ok to 60 digits; the matrix [psi(<hb>/q)] over the units is "
            "non-singular (least singular value %s)" % (q, mp.nstr(smin, 6)))
    out("part1: worst deviation %s" % mp.nstr(worst, 3))
    return True


def lll_test(qs=(9, 15, 21, 25, 27, 33, 35, 39, 45), digits=220):
    import mpmath as mp
    import flint
    mp.mp.dps = digits + 40
    for q in qs:
        F = Full(q)
        n = q - 1
        C = mp.mpf(10) ** digits
        rows = []
        for r in range(1, q):
            row = [0] * (n + 2)
            row[r - 1] = 1
            row[n] = int(mp.nint(C * mp.digamma(mp.mpf(r) / q)))
            row[n + 1] = 10 ** digits
            rows.append(row)
        L = flint.fmpz_mat(rows).lll()
        short = []
        norms = []
        for i in range(n):
            vec = [int(L[i, j]) for j in range(n + 2)]
            nrm = sum(x * x for x in vec)
            norms.append(nrm)
            if nrm < 10 ** 12:
                short.append(vec)
        expect = q - 1 - len(F.units) - len(F.ps)
        nxt = min([x for x in norms if x >= 10 ** 12] or [0])
        ok = True
        for vec in short:
            f = [Fr(0)] + [Fr(x) for x in vec[:n]]
            if not (all(F.g(f, a) == 0 for a in F.units) and all(F.cp(f, p) == 0 for p in F.ps)):
                ok = False
        print("lll q = %d: %d short relations (expected dimension %d), all in the space of (a),(b): %s; "
              "next squared norm about 10^%d" % (q, len(short), expect, ok, len(str(nxt)) - 1))
        assert len(short) == expect and ok


# ----------------------------------------------------------------------------------------------
# refutation searches
# ----------------------------------------------------------------------------------------------
def brute_small(q):
    """no linear algebra: every choice of odd values modulo 2^(D+1) on the free non-units, the other values
    being forced by (a),(b); 2^D = largest power of 2 in a denominator of the basis. Returns the number of
    choices for which the forced values are all odd (the oddness of f depends only on these residues)."""
    F = Full(q)
    free, rows = F.basis(True)
    D = 0
    for row in rows:
        for x in row:
            if x != 0:
                D = max(D, v2(x.denominator))
    mod = 1 << (D + 1)
    assert (mod // 2) ** len(free) <= 300000
    found = 0
    for cs in itertools.product(range(1, mod, 2), repeat=len(free)):
        ok = True
        for j in range(q - 1):
            x = sum(c * row[j] for c, row in zip(cs, rows) if row[j] != 0)
            if not is_odd_fr(Fr(x)):
                ok = False
                break
        found += ok
    return found


def refute(lo, hi, verbose=True, compare_orbit=True):
    surv, killed, bad = [], 0, []
    maxv = 0
    t0 = time.time()
    for q in range(lo | 1, hi + 1, 2):
        fac = factor(q)
        if len(fac) == 1 and list(fac.values())[0] == 1:
            continue
        ok, mv, _ = decide_full(q, True)
        maxv = max(maxv, mv)
        if compare_orbit:
            ok2, mv2, _ = decide_orbit(q, True)
            assert ok2 == ok, ("full and orbit systems disagree", q)
        if ok:
            surv.append(q)
        else:
            killed += 1
        if ok != is_square(q):
            bad.append(q)
    if verbose:
        print("refute [%d,%d] (full system): %d odd composite q; killed %d; survivors %s" %
              (lo, hi, killed + len(surv), killed, surv))
        print("   survivors are exactly the squares: %s; exceptions: %s; largest pivot valuation %d; %.1f s"
              % (not bad, bad, maxv, time.time() - t0))
    return surv, bad


def orbit_sweep(lo, hi, maxorb=4000, verbose=True):
    surv, bad, skipped = [], [], []
    count = 0
    maxv = 0
    t0 = time.time()
    for q in range(lo | 1, hi + 1, 2):
        fac = factor(q)
        if len(fac) == 1 and list(fac.values())[0] == 1:
            continue
        ok, mv, _ = decide_orbit(q, True, maxorb=maxorb)
        if ok is None:
            skipped.append(q)
            continue
        count += 1
        maxv = max(maxv, mv)
        if ok:
            surv.append(q)
        if ok != is_square(q):
            bad.append(q)
    if verbose:
        print("orbit [%d,%d]: decided %d odd composite q (skipped %d with more than %d orbits)" %
              (lo, hi, count, len(skipped), maxorb))
        print("   survivors: %s" % surv)
        print("   survivors are exactly the squares: %s; exceptions: %s; largest pivot valuation %d; %.1f s"
              % (not bad, bad, maxv, time.time() - t0))
        if skipped:
            print("   skipped: %s" % skipped)
    return surv, bad, skipped


def special(verbose=True):
    res = []
    lst_full = [255, 771, 1155, 1285, 1649, 873, 1737, 2313, 2601, 3315]
    lst_orb = [1155, 3003, 5005, 15015, 19635, 51, 85, 153, 291, 485, 579, 965, 771, 1285, 1649, 4369, 18721,
               24929, 49601, 1105, 5525, 32045, 17 * 17 * 3, 17 * 17 * 97, 17 ** 3, 97 ** 3,
               3 ** 5 * 17, 3 ** 3 * 5 ** 3, 3 ** 3 * 5 ** 2, 3 ** 2 * 5 ** 2 * 7, 11025, 27225, 99225,
               289 * 9, 289 * 25, 97 * 97, 193 * 193, 257 * 9, 17 * 113, 17 * 113 * 3, 41 * 73,
               3 * 5 * 7 * 11 * 13 * 19, 3 * 7 * 11 * 19 * 23 * 31,
               # the q <= 12000 that "orbit 3001 12000 3000" skips (more than 3000 orbits; about 90 s each)
               3855, 8995, 9843, 10023, 11535, 11565]
    for q in lst_full:
        t0 = time.time()
        ok, mv, _ = decide_full(q, True)
        res.append((q, "full", ok))
        if verbose:
            print("special q = %d = %s (full system, %d unknowns): odd-valued solution of (a),(b): %s "
                  "[square: %s] (%.1f s)" % (q, factor(q), q - 1, ok, is_square(q), time.time() - t0))
        assert ok == is_square(q)
    for q in lst_orb:
        t0 = time.time()
        O = Orb(q)
        ok, mv, _ = decide_orbit(q, True)
        res.append((q, "orbit", ok))
        if verbose:
            print("special q = %d = %s (orbit system, %d orbits): odd-valued solution of (a),(b): %s "
                  "[square: %s] (%.1f s)" % (q, factor(q), O.norbits(), ok, is_square(q), time.time() - t0))
        assert ok == is_square(q)
    return res


def aonly(lo, hi, verbose=True):
    """section 6.1: (a) alone has no odd-valued solution iff the number of p | q with v_2(p-1) minimal and
    k_p odd is odd."""
    bad = []
    cnt = 0
    for q in range(lo | 1, hi + 1, 2):
        fac = factor(q)
        if len(fac) == 1 and list(fac.values())[0] == 1:
            continue
        ok, mv, _ = decide_full(q, False)
        smin = min(v2(p - 1) for p in fac)
        num = sum(1 for p in fac if v2(p - 1) == smin and fac[p] % 2 == 1)
        cnt += 1
        if ok != (num % 2 == 0):
            bad.append(q)
    if verbose:
        print("aonly [%d,%d]: %d odd composite q; rule of section 6.1 holds: %s; exceptions %s" %
              (lo, hi, cnt, not bad, bad))
    return bad


# ----------------------------------------------------------------------------------------------
# squares
# ----------------------------------------------------------------------------------------------
def f_63(q):
    """the function of section 6.3 for an odd square q."""
    fac = factor(q)
    f = [Fr(0)] * q
    for r in range(1, q):
        d = gcd(r, q)
        N = q // d
        fN = factor(N)
        Om = sum(fN.values())
        rad = 1
        for p in fN:
            rad *= p
        th = 1
        if len(fN) == 1:
            p = list(fN)[0]
            u = (r // d) % p
            th = 1 if pow(u, (p - 1) // 2, p) == 1 else -1
        f[r] = Fr((-1) ** Om * rad * th, N)
    return f


def squares(qs=(9, 25, 49, 81, 225, 441), verbose=True, seed=5):
    import mpmath as mp
    mp.mp.dps = 75
    rng = random.Random(seed)
    for q in qs:
        F = Full(q)
        # the document's formula
        f = f_63(q)
        assert all(is_odd_fr(x) for x in f[1:])
        assert all(F.g(f, a) == 0 for a in F.units) and all(F.cp(f, p) == 0 for p in F.ps)
        if q <= 81:
            assert all(g_def(q, F.fac, f, a) == 0 for a in F.units)
        s1 = series_psi(q, f)
        assert abs(s1) < mp.mpf(10) ** (-60)
        # my own construction from the full system
        ok, mv, sols = decide_full(q, True, want_solution=True, rng=rng, nvariants=2)
        assert ok and sols
        worst = abs(s1)
        for fs in sols:
            assert fs[0] == 0 and all(is_odd_fr(x) for x in fs[1:])
            assert all(F.g(fs, a) == 0 for a in F.units) and all(F.cp(fs, p) == 0 for p in F.ps)
            if q <= 81:
                assert all(g_def(q, F.fac, fs, a) == 0 for a in F.units)
            sv = series_psi(q, fs)
            assert abs(sv) < mp.mpf(10) ** (-60)
            worst = max(worst, abs(sv))
        if verbose:
            vals = sorted(set(sols[0][1:]))
            print("squares q = %d: formula 6.3 is odd-valued, satisfies (a),(b) exactly; %d odd-valued "
                  "solutions built by 2-adic elimination, (a),(b) exact; |sum f(n)/n| <= %s; "
                  "first solution has %d distinct values, e.g. %s" %
                  (q, len(sols), mp.nstr(worst, 3), len(vals), ", ".join(str(x) for x in vals[:6])))
    return True


# ----------------------------------------------------------------------------------------------
# group rings (elements: dict tuple -> number), for S_P and for abstract products of cyclic groups
# ----------------------------------------------------------------------------------------------
def gr_mul(x, y, orders):
    res = {}
    for g, a in x.items():
        for h, b in y.items():
            k = tuple((gi + hi) % o for gi, hi, o in zip(g, h, orders))
            res[k] = res.get(k, 0) + a * b
    return {k: v for k, v in res.items() if v != 0}


def gr_add(x, y, c=1):
    res = dict(x)
    for k, v in y.items():
        res[k] = res.get(k, 0) + c * v
    return {k: v for k, v in res.items() if v != 0}


def gr_norm(orders, idxs):
    """sum of the elements of the subgroup prod_{i in idxs} C_i."""
    rngs = [range(o) if i in idxs else range(1) for i, o in enumerate(orders)]
    return {g: 1 for g in itertools.product(*rngs)}


def gr_eps(x):
    return sum(x.values())


def gr_one(orders):
    return {tuple(0 for _ in orders): 1}


class SP:
    """the objects of section 5.1 for an odd q."""

    def __init__(self, q):
        self.q = q
        self.fac = factor(q)
        self.ps = sorted(self.fac)
        self.t = len(self.ps)
        self.s = [v2(p - 1) for p in self.ps]
        self.orders = tuple(1 << s for s in self.s)
        self.dl = [dlog_table(p) for p in self.ps]
        self.k = [self.fac[p] for p in self.ps]
        # u_p: component at p' != p is [p]_{p'}^(-1)
        self.u = []
        for i, p in enumerate(self.ps):
            self.u.append(tuple(0 if j == i else (-self.dl[j][p % pp]) % self.orders[j]
                                for j, pp in enumerate(self.ps)))

    def nset(self, r):
        N = self.q // gcd(r, self.q)
        return frozenset(i for i, p in enumerate(self.ps) if N % p == 0)

    def cl(self, r):
        d = gcd(r, self.q)
        u = r // d
        n = self.nset(r)
        return tuple(self.dl[i][u % p] % self.orders[i] if i in n else 0 for i, p in enumerate(self.ps))

    def o(self, n):
        x = 1
        for i in n:
            x *= (self.ps[i] - 1) >> self.s[i]
        return x

    def nu(self, n):
        x = 1
        for i in n:
            x *= self.k[i]
        return x

    def a(self, n, drop=None):
        """a_n = prod_{p in n} (p - u_p); if drop is an index, the image under C_drop -> 1."""
        res = gr_one(self.orders)
        for i in n:
            u = self.u[i]
            if drop is not None:
                u = tuple(0 if j == drop else x for j, x in enumerate(u))
            res = gr_mul(res, gr_add({tuple(0 for _ in self.orders): self.ps[i]}, {u: 1}, -1), self.orders)
        return res

    def gn(self, f):
        """dict n -> g_n."""
        res = {}
        for r in range(1, self.q):
            n = self.nset(r)
            c = self.cl(r)
            d = res.setdefault(n, {})
            d[c] = d.get(c, 0) + f[r]
        return {n: {k: v / self.o(n) for k, v in d.items() if v != 0} for n, d in res.items()}

    def subsets(self, base=None):
        base = list(range(self.t)) if base is None else list(base)
        for m in range(len(base) + 1):
            for c in itertools.combinations(base, m):
                yield frozenset(c)

    def main_equation(self, f):
        """the left side of (M)."""
        g = self.gn(f)
        allp = frozenset(range(self.t))
        tot = {}
        for n in self.subsets():
            if not n or n not in g:
                continue
            term = gr_mul(gr_mul(self.a(n), gr_norm(self.orders, allp - n), self.orders), g[n], self.orders)
            tot = gr_add(tot, term)
        return tot

    def lemma1(self, f):
        g = self.gn(f)
        for n in self.subsets():
            if not n:
                continue
            e = gr_add(g.get(n, {}), gr_norm(self.orders, n), -self.nu(n))
            for k, v in e.items():
                if v2_fr(Fr(v)) < 1:
                    return False
        return True

    def ell(self, f, i0):
        p = self.ps[i0]
        pk = p ** self.k[i0]
        return sum(f[r] for r in range(pk, self.q, pk))

    def theoremA(self, f, i0):
        l = self.ell(f, i0)
        x = l - (self.ps[i0] - 1) * self.k[i0]
        return x == 0 or v2_fr(x) >= self.s[i0] + 1

    def proofA(self, f, i0):
        """the intermediate objects of section 5.5; returns True if every stated relation holds."""
        g = self.gn(f)
        allp = frozenset(range(self.t))
        m = allp - {i0}
        Z = {}
        for n in self.subsets(m):
            if n:
                Z = gr_add(Z, gr_mul(gr_mul(self.a(n, drop=i0), gr_norm(self.orders, m - n), self.orders),
                                     g.get(n, {}), self.orders))
        B = {}
        for n in self.subsets(m):
            B = gr_add(B, gr_mul(gr_mul(self.a(n), gr_norm(self.orders, m - n), self.orders),
                                 g.get(n | {i0}, {}), self.orders))
        # B is C_0-invariant
        for k, v in B.items():
            for j in range(self.orders[i0]):
                kk = tuple(j if i == i0 else x for i, x in enumerate(k))
                if B.get(kk, 0) != v:
                    return False
        w = {k: v for k, v in B.items() if k[i0] == 0}
        # Z = -(p_0 - u_0) w
        a0 = self.a([i0])
        if gr_add(Z, gr_mul(a0, w, self.orders)):
            return False
        sm = sum(self.s[i] for i in m)
        ew = Fr(gr_eps(w))
        x = ew - self.k[i0] * (1 << sm)
        if not (x == 0 or v2_fr(x) >= sm + 1):
            return False
        # 2^(s_m) ell = eps(Z) = -(p_0 - 1) eps(w)
        l = self.ell(f, i0)
        return (1 << sm) * l == gr_eps(Z) == -(self.ps[i0] - 1) * ew


def theoremB_congruence(q, fac, f, p):
    k = fac[p]
    s = v2(p - 1)
    l = sum(f[r] for r in range(1, q) if r % p ** k == 0)
    x = (p - 1) * c_lam(q, fac, f, p) - ((p - 1) * k + 1) * l
    return x == 0 or v2_fr(x) >= s + 1


def rand_odd(rng):
    return Fr(rng.choice([-1, 1]) * rng.choice([1, 3, 5, 7, 9, 11]), rng.choice([1, 1, 3, 5, 7]))


def part2(qs_full=(9, 21, 25, 27, 45, 49, 63, 81, 105, 117, 147, 153, 165, 189, 225, 273, 357),
          qs_orbit=(65, 221, 765, 833, 1105, 1225, 1365, 1921, 2465, 2993, 3 * 17 * 113, 5 * 13 * 9,
                    41 * 73 * 9, 17 * 113 * 9, 17 ** 2 * 3 * 7, 193 * 449, 97 * 353, 17 * 113 * 241,
                    5 ** 2 * 13, 5 ** 3 * 13, 3 * 5 ** 2 * 7, 3 ** 4 * 5 ** 2, 289, 625, 17 ** 4),
          seed=7, verbose=True, nvariants=3):
    rng = random.Random(seed)
    out = print if verbose else (lambda *a, **k: None)
    nA = 0
    # ---- Lemma 1 and Theorem B need no equation
    for q in (9, 15, 21, 27, 45, 63, 75, 85, 105, 153, 221, 225, 255, 325, 357, 425, 459, 663):
        S = SP(q)
        for _ in range(4):
            f = [Fr(0)] + [rand_odd(rng) for _ in range(q - 1)]
            assert S.lemma1(f), ("Lemma 1", q)
            for p in S.ps:
                assert theoremB_congruence(q, S.fac, f, p), ("Theorem B congruence", q, p)
            # an odd-valued f with c_p = 0 exactly (possible when q is not a prime power)
            if S.t >= 2:
                for i0, p in enumerate(S.ps):
                    rstar = p ** S.k[i0]
                    f2 = list(f)
                    rest = sum(f2[r] * lam(S.fac, r, p) for r in range(1, q) if r != rstar)
                    f2[rstar] = -rest / lam(S.fac, rstar, p)
                    assert is_odd_fr(f2[rstar]), ("Theorem B: solved value not odd", q, p)
                    assert c_lam(q, S.fac, f2, p) == 0
                    l = S.ell(f2, i0)
                    assert l == 0 or v2_fr(l) >= S.s[i0] + 1, ("Theorem B", q, p)
        # Lemma 1 must fail for non-odd data (the test has teeth)
        f = [Fr(0)] + [rand_odd(rng) for _ in range(q - 1)]
        f[1] += 1
        assert not S.lemma1(f)
    out("part2: Lemma 1 and Theorem B hold on random odd-valued f (18 values of q, 4 functions each; "
        "Theorem B also on odd-valued f with c_p = 0 exactly)")
    # ---- Lemma 2 on random rational solutions of (a) (not odd-valued), and failure for random f
    for q in (15, 21, 45, 63, 75, 105, 117, 135, 165, 225, 273, 315):
        F = Full(q)
        S = SP(q)
        fa = F.complete({r: rand_fr(rng) for r in F.nonunits}, False)
        assert not S.main_equation(fa), ("(M) fails on a solution of (a)", q)
        fr_ = random_f(q, rng, zero_sum=False)
        assert S.main_equation(fr_), ("(M) holds for a random f", q)
    out("part2: (M) holds exactly for random rational solutions of (a) and fails for random f "
        "(q = 15, 21, 45, 63, 75, 105, 117, 135, 165, 225, 273, 315)")
    # ---- explicit odd-valued solutions of (a)
    def run(q, sols, how):
        nonlocal nA
        F = Full(q)
        S = SP(q)
        fac = S.fac
        us = F.units
        if q <= 400:
            check_units = us
        else:
            # the functions from the orbit system are constant on the orbits of H (checked below), so g is
            # constant on each class of units: one unit per class is enough
            reps = {}
            for a in us:
                reps.setdefault(S.cl(a), a)
            assert len(reps) == 1 << sum(S.s)
            check_units = list(reps.values())
        combos = 1
        for p in fac:
            combos *= fac[p] + mult_order(p, q // p ** fac[p])
        for f in sols:
            assert f[0] == 0 and all(is_odd_fr(x) for x in f[1:])
            if q > 400:
                seen = {}
                for r in range(1, q):
                    key = (gcd(r, q), S.cl(r))
                    assert seen.setdefault(key, f[r]) == f[r], ("f is not constant on an orbit", q)
            assert all(F.g(f, a) == 0 for a in check_units), ("(a) fails", q)
            if combos <= 200000:
                for a in (us if q <= 60 else rng.sample(us, 6 if combos < 20000 else 2)):
                    assert g_def(q, fac, f, a) == 0, ("(a) fails [definition]", q, a)
            assert S.lemma1(f), ("Lemma 1", q)
            assert not S.main_equation(f), ("(M)", q)
            for i0, p in enumerate(S.ps):
                assert S.theoremA(f, i0), ("Theorem A FAILS", q, p)
                assert S.proofA(f, i0), ("a relation in the proof of Theorem A fails", q, p)
                assert theoremB_congruence(q, fac, f, p), ("Theorem B congruence", q, p)
                if S.k[i0] % 2 == 1:
                    # corollary: for k_p odd the coefficient c_p of log p is a 2-adic unit, so (b) fails
                    cp = c_lam(q, fac, f, p)
                    assert cp != 0 and v2_fr(cp) == 0, ("c_p is not a unit although k_p is odd", q, p)
                nA += 1
        info = []
        f = sols[0]
        for i0, p in enumerate(S.ps):
            l = S.ell(f, i0)
            info.append("p=%d: v2(ell)=%s, v2((p-1)k)=%d" % (p, "inf" if l == 0 else v2_fr(l),
                                                             S.s[i0] + v2(S.k[i0])))
        out("part2 q = %d = %s (%s, %d solutions, %d distinct values): Lemma 1, (M), Theorem A and its proof "
            "relations hold; %s" % (q, dict(fac), how, len(sols), len(set(f)), "; ".join(info)))

    none_full, none_orb = [], []
    for q in qs_full:
        ok, mv, sols = decide_full(q, False, want_solution=True, rng=rng, nvariants=nvariants)
        if not ok:
            none_full.append(q)
            continue
        run(q, sols, "full system")
    for q in qs_orbit:
        ok, mv, sols = decide_orbit(q, False, want_solution=True, rng=rng, nvariants=nvariants)
        if not ok:
            none_orb.append(q)
            continue
        run(q, sols, "orbit system")
    out("part2: no odd-valued solution of (a) exists for q in %s (full) and %s (orbit): Theorem A is vacuous "
        "there" % (none_full, none_orb))
    out("part2: Theorem A checked on %d (function, prime) pairs" % nA)
    return nA


# ----------------------------------------------------------------------------------------------
# abstract data: Lemma D, Lemma KL, Theorem A from (M) and Lemma 1 alone
# ----------------------------------------------------------------------------------------------
class AG:
    """finite abelian group prod Z/o_i with a fixed enumeration."""

    def __init__(self, orders):
        self.orders = tuple(orders)
        self.elems = list(itertools.product(*[range(o) for o in self.orders]))
        self.idx = {g: i for i, g in enumerate(self.elems)}
        self.size = len(self.elems)

    def vec(self, x):
        v = [0] * self.size
        for g, c in x.items():
            v[self.idx[g]] = c
        return v

    def shift(self, x, g):
        return {tuple((a + b) % o for a, b, o in zip(k, g, self.orders)): c for k, c in x.items()}

    def mulmat(self, z):
        """rows: g * z for g in the group (so  vec(x) @ mulmat(z) = vec(x z))."""
        return [self.vec(self.shift(z, g)) for g in self.elems]

    def mul(self, x, y):
        return gr_mul(x, y, self.orders)

    def one(self):
        return {tuple(0 for _ in self.orders): 1}

    def gen(self, i, e=1):
        return tuple(e % o if j == i else 0 for j, o in enumerate(self.orders))


def to_u64(M):
    return np.array([[int(x) % M64 for x in row] for row in M], dtype=np.uint64)


def z2_left_kernel(T):
    """Z_(2)-basis (approximate modulo a high power of 2) of {x : x T = 0}; T an integer matrix (lists)."""
    T = to_u64(T)
    r, n = T.shape
    A = np.zeros((r, n + r), dtype=np.uint64)
    A[:, :n] = T
    for i in range(r):
        A[i, n + i] = 1
    R, piv = z2_echelon(A, npiv=n)
    maxv = max([v for c, v in piv] or [0])
    assert maxv <= 30, "valuations too large for the 64-bit kernel"
    return [[int(x) for x in R[i, n:]] for i in range(len(piv), r)], maxv


def z2_member(Gens, vecs, bits=30):
    """is each vector (integers modulo 2^bits at least) in the Z_(2)-span of the rows of Gens (full rank)?"""
    G = to_u64(Gens)
    R, piv = z2_echelon(G)
    assert len(piv) == G.shape[1], "generators do not have full rank"
    assert max(v for c, v in piv) < bits
    res = []
    mod = 1 << bits
    for x in vecs:
        x = [int(c) % mod for c in x]
        ok = True
        for i, (c, v) in enumerate(piv):
            xc = x[c]
            if xc == 0:
                continue
            if xc % (1 << v):
                ok = False
                break
            coef = (xc >> v) * pow(int(R[i, c]) >> v, -1, mod) % mod
            row = R[i, :]
            x = [(a - coef * int(b)) % mod for a, b in zip(x, row)]
        res.append(ok)
    return res


def subsets_of(lst):
    for m in range(len(lst) + 1):
        for c in itertools.combinations(lst, m):
            yield frozenset(c)


def lemmaD_instance(rng, sizes=(2, 2, 4, 3, 4, 6, 8), maxN=32, wrong=False):
    while True:
        t = rng.choice([1, 2, 2, 3])
        orders = [rng.choice(sizes) for _ in range(t)]
        N = 1
        for o in orders:
            N *= o
        if N <= maxN and (t < 3 or N <= 16):
            break
    G = AG(orders)
    pis = [rng.choice([-9, -7, -5, -4, -3, -2, 2, 3, 4, 5, 6, 7, 9, 13]) for _ in range(t)]
    us, sg = [], []
    for i in range(t):
        g = tuple(0 if j == i else rng.randrange(o) for j, o in enumerate(orders))
        us.append(g)
        sg.append(rng.choice([1, -1]))        # Gamma = {+1, -1}
    def a_of(n):
        x = G.one()
        for i in n:
            x = G.mul(x, gr_add({G.gen(i, 0): pis[i]}, {us[i]: sg[i]}, -1))
        return x
    def delta(n):
        x = G.one()
        for i in n:
            x = G.mul(x, gr_add(G.one(), {G.gen(i): 1}, -1))
        return x
    allm = frozenset(range(t))
    subs = list(subsets_of(list(range(t))))
    # generators of I
    gensI = []
    for n in subs:
        if wrong and n == allm - {0}:
            continue
        el = G.mul(a_of(n), gr_norm(G.orders, allm - n))
        gensI += G.mulmat(el)
    # I^# as the projection of the left kernel of T: variables (x, z_n for n non-empty), x Delta_n = z_n a_n
    ne = [n for n in subs if n]
    Nn = G.size
    T = [[0] * (Nn * len(ne)) for _ in range(Nn * (1 + len(ne)))]
    for bi, n in enumerate(ne):
        Md = G.mulmat(delta(n))
        Ma = G.mulmat(a_of(n))
        for i in range(Nn):
            for j in range(Nn):
                T[i][bi * Nn + j] = Md[i][j]
                T[Nn * (1 + bi) + i][bi * Nn + j] = -Ma[i][j]
    ker, maxv = z2_left_kernel(T)
    assert len(ker) == Nn
    xs = [k[:Nn] for k in ker]
    # the x-parts must span a full lattice; check membership in I
    mem = z2_member(gensI, xs)
    # and I inside I^#: every generator of I is in the span of the xs
    mem2 = z2_member(xs, [[c % M64 for c in row] for row in gensI])
    # is I^# a proper sublattice of Lambda (so that the test says something)?
    proper = not all(z2_member(xs, [[1 if j == i else 0 for j in range(Nn)] for i in range(Nn)]))
    return all(mem), all(mem2), proper, (orders, pis, us, sg)


def lemmaKL_instance(rng, violate=False):
    # C_0: any finite abelian group; S_m: cyclic C_p with |C_p| dividing p - 1
    while True:
        c0 = rng.choice([[1], [2], [4], [2, 2], [3], [6], [8]])
        t = rng.choice([1, 2, 2, 3])
        pcs = []
        for _ in range(t):
            p = rng.choice([3, 5, 7, 9, 13, 17, 25, -3, -7, 4, 10])
            dv = [d for d in range(1, abs(p - 1) + 1) if (p - 1) % d == 0 and d <= 8]
            e = rng.choice(dv)
            if violate:
                e = rng.choice([2, 4, 8])
            pcs.append((p, e))
        size = 1
        for o in c0:
            size *= o
        for p, e in pcs:
            size *= e
        if size <= 64:
            break
    n0 = len(c0)
    orders = list(c0) + [e for p, e in pcs]
    G = AG(orders)
    mi = list(range(n0, n0 + t))
    us = []
    for i in mi:
        us.append(tuple(0 if j == i else rng.randrange(o) for j, o in enumerate(orders)))
    def a_of(n):
        x = G.one()
        for i in n:
            x = G.mul(x, gr_add({G.gen(0, 0): pcs[i - n0][0]}, {us[i - n0]: 1}, -1))
        return x
    allm = frozenset(mi)
    gensI = []
    for n in subsets_of(mi):
        gensI += G.mulmat(G.mul(a_of(n), gr_norm(G.orders, allm - n)))
    N0 = gr_norm(G.orders, frozenset(range(n0)))
    sm_elems = [g for g in G.elems if all(g[j] == 0 for j in range(n0))]
    rowsW = [[-c for c in G.vec(G.shift(N0, g))] for g in sm_elems]
    ker, maxv = z2_left_kernel(gensI + rowsW)
    Sm = len(sm_elems)
    # eps(w) for the w-parts of the kernel vectors
    need = v2(Sm) if Sm else 0
    worst = None
    for kv in ker:
        w = kv[len(gensI):]
        e = sum(w) % (1 << 30)
        val = 30 if e == 0 else v2(e)
        worst = val if worst is None else min(worst, val)
    return worst >= need, worst, need, (c0, pcs, us)


def abstractA_instance(rng):
    """(M) with g_n = nu(n) N_n + 2 e_n, e_n unknown in Z_(2)[S_n], arbitrary u_p in S_{P-p}, arbitrary odd
    integers p with v_2(p-1) = s_p. Claim: every solution has ell_0 = (p_0-1) k_0 mod 2^(s_0+1)."""
    while True:
        t = rng.choice([1, 2, 2, 3, 3])
        ss = [rng.choice([1, 1, 2, 3]) for _ in range(t)]
        if sum(ss) <= 5:
            break
    ps = []
    for s in ss:
        cands = [p for p in (3, 5, 7, 9, 11, 13, 15, 17, 21, 25, 27, 29, 41, 49, 73) if v2(p - 1) == s]
        ps.append(rng.choice(cands))
    ks = [rng.choice([1, 1, 2, 3, 4]) for _ in range(t)]
    orders = [1 << s for s in ss]
    G = AG(orders)
    us = [tuple(0 if j == i else rng.randrange(o) for j, o in enumerate(orders)) for i in range(t)]
    allp = frozenset(range(t))
    def a_of(n):
        x = G.one()
        for i in n:
            x = G.mul(x, gr_add({G.gen(0, 0): ps[i]}, {us[i]: 1}, -1))
        return x
    def nu(n):
        x = 1
        for i in n:
            x *= ks[i]
        return x
    def o(n):
        x = 1
        for i in n:
            x *= (ps[i] - 1) >> ss[i]
        return x
    ne = [n for n in subsets_of(list(range(t))) if n]
    # rows: first the variable T (homogenizing), then for each n and each sigma in S_n the variable e_n(sigma)
    rows = []
    const = {}
    for n in ne:
        const = gr_add(const, G.mul(G.mul(a_of(n), gr_norm(G.orders, allp - n)), gr_norm(G.orders, n)), nu(n))
    rows.append(G.vec(const))
    varinfo = []
    for n in ne:
        base = G.mul(a_of(n), gr_norm(G.orders, allp - n))
        for sig in itertools.product(*[range(orders[i]) if i in n else range(1) for i in range(t)]):
            rows.append([2 * c for c in G.vec(G.shift(base, sig))])
            varinfo.append(n)
    ker, maxv = z2_left_kernel(rows)
    has_odd = any(kv[0] % 2 for kv in ker)
    if not has_odd:
        return None, (ps, ks, us)
    okall = True
    for i0 in range(t):
        m = allp - {i0}
        for kv in ker:
            T = kv[0]
            L = -T * (ps[i0] - 1) * ks[i0]
            for n in ne:
                if n <= m:
                    L += o(n) * T * nu(n) * (1 << sum(ss[i] for i in n))
            for val, n in zip(kv[1:], varinfo):
                if n <= m:
                    L += o(n) * 2 * val
            if L % (1 << (ss[i0] + 1)):
                okall = False
    square_pattern = all(k % 2 == 0 for k in ks)
    return okall, (ps, ks, us, square_pattern)


def abstract(n=60, seed=11, verbose=True):
    rng = random.Random(seed)
    out = print if verbose else (lambda *a, **k: None)
    cD = cprop = 0
    for _ in range(n):
        m1, m2, proper, data = lemmaD_instance(rng)
        assert m1, ("Lemma D fails: I^# not inside I", data)
        assert m2, ("I not inside I^#", data)
        cD += 1
        cprop += proper
    teeth = 0
    for _ in range(max(10, n // 3)):
        m1, m2, proper, data = lemmaD_instance(rng, wrong=True)
        teeth += (not m1)
    out("abstract: Lemma D (I = I^#) holds on %d random instances (cyclic groups of orders 2,3,4,6,8; "
        "Gamma = {+-1}; integers pi in -9..13), I^# proper in %d; with one generator of I removed the "
        "equality fails in %d of %d instances" % (cD, cprop, teeth, max(10, n // 3)))
    cK = sharp = 0
    for _ in range(n):
        ok, worst, need, data = lemmaKL_instance(rng)
        assert ok, ("Lemma KL fails", data, worst, need)
        cK += 1
        sharp += (worst == need)
    viol = 0
    for _ in range(n):
        ok, worst, need, data = lemmaKL_instance(rng, violate=True)
        viol += (not ok)
    out("abstract: Lemma KL holds on %d random instances (bound attained in %d); when |C_p| is not required "
        "to divide p-1 the conclusion fails in %d of %d instances" % (cK, sharp, viol, n))
    cA = vac = 0
    for _ in range(n):
        ok, data = abstractA_instance(rng)
        if ok is None:
            vac += 1
            continue
        assert ok, ("abstract Theorem A fails", data)
        cA += 1
    out("abstract: Theorem A from (M) and Lemma 1 alone, arbitrary u_p: holds on %d instances with solutions "
        "(%d instances had no solution of the required shape)" % (cA, vac))
    return cD, cK, cA


# ----------------------------------------------------------------------------------------------
# self-test
# ----------------------------------------------------------------------------------------------
def selftest():
    t0 = time.time()
    rng = random.Random(3)
    # basis rows satisfy (a),(b) by the definition-based functions; full = orbit
    for q in (9, 15, 21, 27, 45, 63, 75):
        F = Full(q)
        free, rows = F.basis(True)
        assert len(rows) == q - 1 - len(F.units) - len(F.ps)
        for row in rows:
            f = [Fr(0)] + row
            assert all(g_def(q, F.fac, f, a) == 0 for a in F.units)
            assert all(c_lam(q, F.fac, f, p) == 0 for p in F.ps)
        O = Orb(q)
        fr2, rows2 = O.basis(True)
        for row in rows2[:6]:
            f = O.expand(row)
            assert all(F.g(f, a) == 0 for a in F.units) and all(F.cp(f, p) == 0 for p in F.ps)
    print("selftest: the basis vectors of the full and of the orbit system satisfy (a),(b) exactly "
          "(q = 9, 15, 21, 27, 45, 63, 75)")
    # the elimination: compare with a brute-force search over Z/8 for tiny lattices
    for _ in range(200):
        r = rng.randint(1, 3)
        n = r + rng.randint(1, 3)
        rows =[[Fr(rng.randint(-6, 6), rng.choice([1, 1, 2, 4, 3])) for _ in range(n)] for _ in range(r)]
        for i, row in enumerate(rows):
            for j in range(r):
                row[j] = Fr(1 if i == j else 0)
        ok, mv, _ = odd_point(rows, list(range(r)))
        # brute force: the coefficients are the free coordinates, odd, and only matter modulo 8
        # (the denominators of the rows are at most 4)
        found = False
        for cs in itertools.product([1, 3, 5, 7], repeat=r):
            vec = [sum(c * row[j] for c, row in zip(cs, rows)) for j in range(n)]
            if all(is_odd_fr(x) for x in vec):
                found = True
                break
        assert ok == found, (rows, ok, found)
    print("selftest: 2-adic elimination agrees with brute force on 200 random small lattices")
    for q in (9, 15, 21, 25, 27):
        assert (brute_small(q) > 0) == decide_full(q)[0] == is_square(q)
    print("selftest: enumeration of all residue patterns (no linear algebra) for q = 9, 15, 21, 25, 27: "
          "odd-valued solutions of (a),(b) exist exactly for 9 and 25")
    part1(qs_exact=(9, 15, 27, 45, 75), qs_num=(9, 15, 21, 25, 27, 33, 35, 45, 49, 63, 75, 105), verbose=False)
    print("selftest: part1 ok (formula and criterion, 12 values of q, 60 digits)")
    surv, bad = refute(9, 200, verbose=False)
    assert not bad and surv == [9, 25, 49, 81, 121, 169]
    print("selftest: refute 9..200 (full system, compared with the orbit system): survivors %s" % surv)
    s2, bad2, sk = orbit_sweep(201, 1200, verbose=False)
    assert not bad2 and not sk
    print("selftest: orbit 201..1200: survivors %s" % s2)
    squares(qs=(9, 25, 49, 225), verbose=False)
    print("selftest: squares 9, 25, 49, 225: explicit odd-valued solutions, exact and numeric")
    nA = part2(qs_full=(9, 21, 45, 63, 105, 153, 165), qs_orbit=(65, 221, 765, 1105, 1921, 625),
               verbose=False, nvariants=2)
    print("selftest: part2 ok (Lemma 1, (M), Theorem A on %d (function, prime) pairs, Theorem B)" % nA)
    cD, cK, cA = abstract(n=25, verbose=False)
    print("selftest: abstract ok (Lemma D %d, Lemma KL %d, abstract Theorem A %d instances)" % (cD, cK, cA))
    print("selftest passed in %.0f s" % (time.time() - t0))


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return
    cmd = argv[1]
    if cmd == "selftest":
        selftest()
    elif cmd == "part1":
        part1()
    elif cmd == "refute":
        refute(int(argv[2]), int(argv[3]))
    elif cmd == "orbit":
        orbit_sweep(int(argv[2]), int(argv[3]), int(argv[4]) if len(argv) > 4 else 4000)
    elif cmd == "special":
        special()
    elif cmd == "squares":
        squares()
    elif cmd == "part2":
        part2()
    elif cmd == "abstract":
        abstract(int(argv[2]) if len(argv) > 2 else 60)
    elif cmd == "aonly":
        aonly(int(argv[2]), int(argv[3]))
    elif cmd == "lll":
        lll_test()
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv)
