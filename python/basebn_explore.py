"""Base b, step n: numerical probes of the classes

    F_(b,n) :  S(rho) = sum over k >= 1 of rho(k) * b^(-floor(k/n)) / k,    rho rational, periodic.

    python basebn_explore.py selftest               checks of the program on known relations
    python basebn_explore.py sums B N P [T ...]     probe A: relations among pi (or the targets T)
                                                    and the P class sums of F_(B,N)
    python basebn_explore.py logs B N NN            probe B: relations among 2 pi i and the numbers
                                                    Log(1 - r / B^(1/N)), r^NN = 1
    python basebn_explore.py reduce                 "Bailey formula -> step n" and "base a^j -> base a",
                                                    checked by direct summation on examples
    python basebn_explore.py kummer [NMAX MMAX]     the degree of b^(1/n) over Q(zeta_M), certified
    python basebn_explore.py table OUT [PROCS MAXP] the standard set of probes (periods up to MAXP,
                                                    default 144), in parallel; one JSON line per run is
                                                    appended to the file OUT; runs already there are skipped
    python basebn_explore.py jobs OUT PROCS K:B:N:P ...   extra runs (K is sums or logs), appended to OUT
    python basebn_explore.py report OUT [OUT2 ...]  the table of results, from the files

Needs mpmath and python-flint (python-flint on PYTHONPATH, as for baseb_explore.py and
base5_explore.py); `kummer` and `selftest` also need sympy. Prints ASCII only.
Summary of the runs: research/2026-11-22-general-step/00_summary.md.

NOTHING HERE IS A PROOF. A lattice search finds every integer relation whose sum of
|coefficients| is below a bound (printed with each run; at least 2^21 in the runs of the
summary) at ONE period; it says nothing about larger coefficients or other periods.

Setting (Parts IV to VI of notes/pi_formula_theorem.md). A BBP-type formula of degree 1,
sum_j b^(-B j) sum_{i=1..N} a_i / (N j + i), is the series of F_(b,n) with n = N / gcd(B, N),
supported on the multiples of B / gcd(B, N) (command `reduce`). With c = b^(1/n) and x = 1/c,

    b^(-floor(k/n)) = c^(k mod n) x^k,      S(rho) = - sum over r^P = 1 of d_r Log(1 - r x).

Probe A (theory-free). S_j = sum over k = j (mod P) of b^(-floor(k/n)) / k. An integer relation
z_0 pi + sum_j z_j S_j = 0 is a rational pattern (z_j) of period P with value (-z_0) pi, so the
relations found are a basis of the space of period-P patterns with value in Q pi (or in the
Q-span of the targets). A target is a product of tokens: pi, sqrtM, cS (c^S, c = b^(1/n)); for
example pi*sqrt3*c1.

Probe B (uses Baker's theorem to read the result). Integer vectors z with
sum_r z_r Log(1 - r x) + z_0 2 pi i = 0, r over the NN-th roots of unity. By Baker's theorem
and Galois descent, the rank of this lattice is the dimension of the space of rational
patterns of period NN whose value is an ALGEBRAIC multiple of pi (zero included). Rank 0 means:
no zero relation and no algebraic multiple of pi at this period, up to the coefficient bound.

The sub-series lemma, as tested. Write b = a^j with a not a perfect power, n1 = n/2 (n even) or
n (n odd), and n1' = n1 / gcd(n1, j). The conjugates of c over the field of all roots of unity
are the eta*c with eta^(n1') = 1 (command `kummer` certifies the degree n1' over Q(zeta_M)).
Prediction: every relation splits into its parts on the classes k = u (mod n1'), each part
being a relation by itself, and a target with twist c^S belongs to the part u = S (mod n1').
For a base that is not a perfect power n1' = n1; for a perfect power the split with n1 itself
is false in general (it fails for b = 9, n = 4 and for b = 8, n = 3: see `selftest`).

How a relation is accepted. The lattice is built from the values rounded to Wc bits; a row
of the reduced basis is accepted only if the same combination, evaluated with 300 (probe A)
or 400 (probe B) more bits, is below 2^-(Wc + 200) or 2^-(Wc + 300) times its sum of
|coefficients|. Short vectors that are not relations fail this by hundreds of bits. The bound printed with each run is a certificate: with the accepted rows
first, every other lattice vector is at least as long as the smallest Gram-Schmidt length of
the remaining rows, so an integer relation with sum |z_i| below the bound lies in the span
of the relations found.
"""
import json
import random
import sys
import time
from fractions import Fraction
from math import gcd

from mpmath import mp, mpf, pi, sqrt, log, floor


# ---------------------------------------------------------------------------------------
# 0. Arithmetic of the base and the step
# ---------------------------------------------------------------------------------------

def perfect_power(b):
    """b = a^j with a not a perfect power; returns (a, j)."""
    for j in range(b.bit_length(), 1, -1):
        a = round(b ** (1.0 / j))
        for cand in (a - 1, a, a + 1):
            if cand >= 2 and cand ** j == b:
                return cand, j
    return b, 1


def n1_of(n):
    return n // 2 if n % 2 == 0 else n


def n1_corrected(b, n):
    """n1' = n1 / gcd(n1, j): the degree of b^(1/n) over the field of all roots of unity."""
    a, j = perfect_power(b)
    return n1_of(n) // gcd(n1_of(n), j)


def sqfree_split(b):
    """b = s^2 d with d squarefree; returns (s, d)."""
    s, d, p = 1, b, 2
    while p * p <= d:
        while d % (p * p) == 0:
            d //= p * p
            s *= p
        p += 1
    return s, d


def conductor(d):
    return 1 if d == 1 else (d if d % 4 == 1 else 4 * d)


def lcm(a, b):
    return a * b // gcd(a, b)


# ---------------------------------------------------------------------------------------
# 1. Lattice reduction with the high-precision guard and the certificate
# ---------------------------------------------------------------------------------------

def is_relation(coef, vals, Wc, extra):
    """True if sum coef_i * vals_i vanishes (in every coordinate) to Wc + extra - 100 bits."""
    tol = (sum(abs(c) for c in coef) + 1) * mpf(2) ** (-(Wc + extra - 100))
    for t in range(len(vals[0])):
        if abs(mp.fdot(coef, [v[t] for v in vals])) >= tol:
            return False
    return True


def gs_bound(rel_rows, other_rows, q):
    """floor(min Gram-Schmidt length of the rows that are not relations / sqrt(q + 1))."""
    if not other_rows:
        return None
    old = mp.prec
    mp.prec = 200
    gs, best = [], None
    for idx, row in enumerate(rel_rows + other_rows):
        v = [mpf(c) for c in row]
        for g, gg in gs:
            c = mp.fdot(v, g) / gg
            v = [x - c * y for x, y in zip(v, g)]
        vv = mp.fdot(v, v)
        gs.append((v, vv))
        if idx >= len(rel_rows) and (best is None or vv < best):
            best = vv
    out = int(floor(sqrt(best / (q + 1))))
    mp.prec = old
    return out


def integer_relations(vals, Wc, extra):
    """vals: list of tuples of q real numbers (mpf), known to Wc + extra + 64 bits.

    Returns (relations, bound, seconds): the integer vectors z with sum z_i vals_i = 0 found by
    LLL at Wc bits and confirmed at Wc + extra bits; and the certificate bound (see the module
    docstring): any integer relation with sum |z_i| < bound is in the span of those returned."""
    from flint import fmpz_mat
    m, q = len(vals), len(vals[0])
    mp.prec = Wc + extra + 64
    scale = mpf(2) ** Wc
    rows = []
    for i, v in enumerate(vals):
        row = [0] * (m + q)
        row[i] = 1
        for t in range(q):
            row[m + t] = int(floor(v[t] * scale))
        rows.append(row)
    t0 = time.time()
    red = fmpz_mat(rows).lll()
    t_lll = time.time() - t0
    rel_rows, other_rows = [], []
    for i in range(m):
        row = [int(red[i, j]) for j in range(m + q)]
        (rel_rows if is_relation(row[:m], vals, Wc, extra) else other_rows).append(row)
    bound = gs_bound(rel_rows, other_rows, q)
    mp.prec = Wc + extra + 64
    return [r[:m] for r in rel_rows], bound, t_lll


def rank_Q(rows):
    from flint import fmpz_mat
    rows = [r for r in rows if any(r)]
    if not rows:
        return 0
    return fmpz_mat(rows).rank()


def in_span(rels, vec):
    """True if the rational vector vec (a list of Fractions or integers) is in the span of rels."""
    den = 1
    for x in vec:
        den = lcm(den, Fraction(x).denominator)
    v = [int(Fraction(x) * den) for x in vec]
    return rank_Q(rels + [v]) == rank_Q(rels)


def bits(x):
    return "-" if x is None else "2^%d" % (int(x).bit_length() - 1)


# ---------------------------------------------------------------------------------------
# 2. Probe A: pi (or other targets) and the class sums
# ---------------------------------------------------------------------------------------

def class_sums(b, n, P, W):
    """floor-accurate S_j * 2^W, j = 1..P (index j - 1; j = P is the class k = 0 mod P)."""
    acc = [0] * P
    one = 1 << (W + 64)
    top = 1 << (W + 72)
    k, bp = 1, (b if n == 1 else 1)   # bp = b^(k // n)
    while bp <= top:
        acc[(k - 1) % P] += one // (bp * k)
        k += 1
        if k % n == 0:
            bp *= b
    return [a >> 64 for a in acc]


def target_value(name, b, n):
    """(value, twist) of a target such as 'pi', 'pi*sqrt3', 'pi*sqrt3*c1' (c = b^(1/n))."""
    val, twist = mpf(1), 0
    for tok in name.split("*"):
        if tok == "pi":
            val *= pi
        elif tok.startswith("sqrt"):
            val *= sqrt(mpf(int(tok[4:])))
        elif tok.startswith("c"):
            s = int(tok[1:])
            val *= mpf(b) ** (mpf(s) / n)
            twist += s
        else:
            raise ValueError("unknown target token: " + tok)
    return val, twist


def probe_sums(b, n, P, targets=("pi",), bits_per=None, quiet=False, keep=False):
    """Probe A. Returns a dict; with keep=True it also holds the relations and the values."""
    assert P % n == 0, "the period must be a multiple of the step"
    targets = tuple(targets)
    nt = len(targets)
    m = nt + P
    if bits_per is None:
        bits_per = 40 if m <= 64 else 28
    Wc = bits_per * m + 256
    extra = 300
    W = Wc + extra
    mp.prec = W + 64
    tv = [target_value(t, b, n) for t in targets]
    S = class_sums(b, n, P, W)
    vals = [(v,) for v, _ in tv] + [(mp.ldexp(mpf(s), -W),) for s in S]
    rels, bound, t_lll = integer_relations(vals, Wc, extra)
    a, j = perfect_power(b)
    n1 = n1_of(n)
    n1c = n1 // gcd(n1, j)

    def component(r, mod, u):
        """The part of the relation r on the classes k = u (mod mod), with the targets of twist u."""
        return [c if ((i < nt and tv[i][1] % mod == u) or (i >= nt and (i - nt + 1) % mod == u))
                else 0 for i, c in enumerate(r)]

    def split_ok(mod):
        for r in rels:
            for u in range(mod):
                part = component(r, mod, u)
                if any(part) and not is_relation(part, vals, Wc, extra):
                    return False
        return True

    rank = len(rels)
    tcols = [[r[i] for r in rels] for i in range(nt)]
    with_target = [any(col) for col in tcols]
    lemma_ok = split_ok(n1c)
    naive_ok = lemma_ok if n1 == n1c else split_ok(n1)
    dim0 = rank_Q([component(r, n1c, 0) for r in rels]) if rels else 0
    res = {"probe": "sums", "b": b, "n": n, "P": P, "targets": list(targets), "bits": Wc,
           "rank": rank, "with_target": with_target, "n1": n1, "n1c": n1c,
           "lemma_ok": lemma_ok, "naive_ok": naive_ok, "dim_sub": dim0, "dim_rest": rank - dim0,
           "bound_bits": None if bound is None else bound.bit_length() - 1, "t_lll": round(t_lll, 1)}
    if keep:
        res["rels"], res["vals"], res["Wc"], res["extra"] = rels, vals, Wc, extra
    if not quiet:
        print("F_(%d,%d), period %d: %s and %d class sums, %d bits; LLL %.0f s"
              % (b, n, P, ", ".join(targets), P, Wc, t_lll))
        print("  relations found: %d;  no other relation with sum of |coefficients| below %s"
              % (rank, bits(bound)))
        for t, w in zip(targets, with_target):
            print("  a relation involves %s: %s" % (t, "YES" if w else "no"))
        if rels:
            print("  sub-series lemma (split modulo n1' = %d): %s;  on k = 0 (mod %d): dimension %d,"
                  " on the other classes: %d" % (n1c, "holds" if lemma_ok else "FAILS", n1c, dim0,
                                                  rank - dim0))
            if n1 != n1c:
                print("  the split modulo n1 = %d (not valid for the perfect power %d = %d^%d): %s"
                      % (n1, b, a, j, "holds" if naive_ok else "fails, as expected"))
            for r in rels[:6]:
                nz = ["%s: %d" % (targets[i] if i < nt else "k=%d" % (i - nt + 1), c)
                      for i, c in enumerate(r) if c]
                print("    " + ", ".join(nz[:16]) + (" ..." if len(nz) > 16 else ""))
    return res


# ---------------------------------------------------------------------------------------
# 3. Probe B: 2 pi i and the logarithms Log(1 - r / b^(1/n))
# ---------------------------------------------------------------------------------------

def probe_logs(b, n, N, bits_per=30, quiet=False, keep=False):
    """Probe B. The rank is the dimension of the rational patterns of period N in F_(b,n) with
    value in (algebraic numbers) * pi. 'lifted' counts the relations constant on the cosets
    r * mu_(n1'): these are relations of step 2 (or 1), the part that the lemma leaves."""
    Wc = bits_per * (N + 1) + 300
    extra = 400
    mp.prec = Wc + extra + 64
    x = mpf(b) ** (-mpf(1) / n)
    vals = []
    for e in range(N):
        w = log(1 - mp.expjpi(mpf(2 * e) / N) * x)
        vals.append((w.real, w.imag))
    vals.append((mpf(0), 2 * pi))
    rels, bound, t_lll = integer_relations(vals, Wc, extra)
    rank = len(rels)
    n1c = n1_corrected(b, n)
    lifted = None
    if N % n1c == 0:
        step = N // n1c
        inv = []
        for e in range(step):
            row = [0] * (N + 1)
            for i in range(n1c):
                row[e + i * step] = 1
            inv.append(row)
        inv.append([0] * N + [1])
        lifted = (rank + len(inv) - rank_Q(rels + inv)) if rels else 0
    orders = sorted({N // gcd(e, N) for r in rels for e in range(N) if r[e]})
    res = {"probe": "logs", "b": b, "n": n, "P": N, "bits": Wc, "rank": rank,
           "with_pi": any(r[N] for r in rels), "n1c": n1c, "lifted": lifted, "orders": orders,
           "bound_bits": None if bound is None else bound.bit_length() - 1, "t_lll": round(t_lll, 1)}
    if keep:
        res["rels"] = rels
    if not quiet:
        print("base %d, step %d (c = %d^(1/%d)), N = %d: %d logarithms and 2 pi i, %d bits; LLL %.0f s"
              % (b, n, b, n, N, N, Wc, t_lll))
        print("  relations found: %d;  no other relation with sum of |exponents| below %s"
              % (rank, bits(bound)))
        if rels:
            print("  a relation involves 2 pi i: %s;  constant on the cosets of the %d-th roots of 1"
                  " (lifted from step 2 or 1): %s;  orders of the roots that occur: %s"
                  % ("YES" if res["with_pi"] else "no", n1c, lifted, orders))
            for r in rels[:8]:
                terms = ["%+d L(%s)" % (c, Fraction(e, N)) for e, c in enumerate(r[:N]) if c]
                print("    " + " ".join(terms[:14]) + (" ..." if len(terms) > 14 else "")
                      + ("  %+d (2 pi i)" % r[N] if r[N] else ""))
    return res


# ---------------------------------------------------------------------------------------
# 4. Direct summation; the reductions "Bailey formula -> step n" and "base a^j -> base a"
# ---------------------------------------------------------------------------------------

def series(b, n, rho, digits=50):
    """S(rho) in F_(b,n) by direct summation; rho is one period, for k = 1, 2, ..."""
    mp.dps = digits + 15
    P = len(rho)
    total, k = mpf(0), 1
    w = mpf(1) / b if n == 1 else mpf(1)     # w = b^(-floor(k/n))
    eps = mpf(10) ** (-(digits + 10))
    while w > eps:
        if rho[(k - 1) % P]:
            total += rho[(k - 1) % P] * w / k
        k += 1
        if k % n == 0:
            w /= b
    return total


def bailey_series(b, B, N, a, digits=50):
    """sum over j >= 0 of b^(-B j) * sum_{i=1..N} a_i / (N j + i), by direct summation."""
    mp.dps = digits + 15
    total, j, w = mpf(0), 0, mpf(1)
    eps = mpf(10) ** (-(digits + 10))
    q = mpf(b) ** (-B)
    while w > eps:
        total += w * sum(mpf(Fraction(a[i - 1]).numerator) / Fraction(a[i - 1]).denominator
                         / (N * j + i) for i in range(1, N + 1) if a[i - 1])
        j += 1
        w *= q
    return total


def bailey_to_step(b, B, N, a):
    """The pattern of F_(b,n) equal to the Bailey formula (b^B, N, a).

    n = N / g and the support is on the multiples of m = B / g, g = gcd(B, N):
    rho(m (N j + i)) = m * b^(floor(B i / N)) * a_i, of period m N. Returns (n, rho)."""
    g = gcd(B, N)
    n, m = N // g, B // g
    rho = [Fraction(0)] * (m * N)
    for i in range(1, N + 1):
        rho[m * i - 1] = Fraction(a[i - 1]) * m * b ** (B * i // N)
    return n, rho


def power_to_root(b, n, rho):
    """For b = a^j: the pattern of F_(a, n0) equal to the pattern rho of F_(b, n).

    g = gcd(j, n), n0 = n / g, j0 = j / g; the support is on the multiples of j0:
    rho'(j0 k) = j0 * a^(floor(j (k mod n) / n)) * rho(k). Returns (a, n0, rho')."""
    a, j = perfect_power(b)
    g = gcd(j, n)
    n0, j0 = n // g, j // g
    P = lcm(len(rho), n)
    out = [Fraction(0)] * (j0 * P)
    for k in range(1, P + 1):
        out[j0 * k - 1] = Fraction(rho[(k - 1) % len(rho)]) * j0 * a ** (j * (k % n) // n)
    return a, n0, out


def cmd_reduce():
    rnd = random.Random(20261122)
    print("1. Bailey formula sum_j b^(-B j) sum_i a_i/(N j + i)  ->  series of F_(b,n), n = N/gcd(B,N)")
    cases = [(2, 4, 8, [4, 0, 0, -2, -1, -1, 0, 0], "the BBP formula (value pi)"),
             (2, 2, 6, [9, 0, 0, -9, 0, 0], "the example of Part IV (value pi sqrt(3) 2^(1/3))")]
    for b, B, N in [(10, 3, 4), (10, 2, 6), (10, 1, 8), (7, 6, 4), (12, 5, 5), (3, 4, 6),
                    (5, 12, 8), (6, 3, 9)]:
        cases.append((b, B, N, [Fraction(rnd.randint(-9, 9), rnd.randint(1, 5)) for _ in range(N)],
                      "random coefficients"))
    worst = mpf(0)
    for b, B, N, a, what in cases:
        n, rho = bailey_to_step(b, B, N, a)
        v1 = bailey_series(b, B, N, a)
        v2 = series(b, n, rho)
        mp.dps = 20
        worst = max(worst, abs(v1 - v2))
        print("   base %d^%d, N = %d (%s): step n = %d, support on multiples of %d, period %d;"
              "  difference of the two sums: %s" % (b, B, N, what, n, B // gcd(B, N), len(rho),
                                                    mp.nstr(abs(v1 - v2), 3)))
    print("   largest difference: %s (sums to 50 digits)" % mp.nstr(worst, 3))
    print("2. Base b = a^j, step n  ->  base a, step n0 = n/gcd(j,n), support on multiples of j/gcd(j,n)")
    worst = mpf(0)
    for b, n in [(9, 4), (9, 2), (9, 3), (8, 3), (8, 2), (8, 6), (4, 2), (4, 4), (4, 6), (4, 3),
                 (16, 8), (16, 6), (27, 2), (25, 4), (36, 4), (100, 6)]:
        rho = [Fraction(rnd.randint(-9, 9), rnd.randint(1, 4)) for _ in range(2 * n)]
        a, n0, rho2 = power_to_root(b, n, rho)
        v1 = series(b, n, rho)
        v2 = series(a, n0, rho2)
        mp.dps = 20
        worst = max(worst, abs(v1 - v2))
        j = perfect_power(b)[1]
        print("   F_(%d,%d) = part of F_(%d,%d) on the multiples of %d;  n1' = %d;  difference: %s"
              % (b, n, a, n0, j // gcd(j, n), n1_corrected(b, n), mp.nstr(abs(v1 - v2), 3)))
    print("   largest difference: %s" % mp.nstr(worst, 3))


# ---------------------------------------------------------------------------------------
# 5. The degree of b^(1/n) over Q(zeta_M): prediction and certificate
# ---------------------------------------------------------------------------------------

def kummer_degree(b, n, M, max_primes=4000):
    """(predicted, certified lower bound) for [Q(zeta_M, b^(1/n)) : Q(zeta_M)], n | M.

    Prediction, with b = a^j, a not a perfect power, f the conductor of Q(sqrt(a)):
    n / gcd(n, 2j) if f | M, and n / gcd(n, j) otherwise. It is an upper bound for the degree
    (that power of b^(1/n) is rational, or a rational multiple of sqrt(a), which lies in
    Q(zeta_M) when f | M). Certificate for the lower bound: for a prime p = 1 (mod M) not
    dividing b, the polynomial X^n - b modulo p has all its irreducible factors of degree
    ord(b^((p-1)/n) mod p), and this degree divides the degree sought (the Frobenius at a
    prime above p, which is unramified and has residue field F_p in Q(zeta_M))."""
    from sympy import isprime
    assert M % n == 0
    a, j = perfect_power(b)
    f = conductor(sqfree_split(a)[1])
    pred = n // gcd(n, 2 * j) if M % f == 0 else n // gcd(n, j)
    low, p, seen = 1, 1, 0
    while low < pred and seen < max_primes:
        p += M
        if gcd(p, b) != 1 or not isprime(p):
            continue
        seen += 1
        beta = pow(b, (p - 1) // n, p)
        o = next(d for d in range(1, n + 1) if n % d == 0 and pow(beta, d, p) == 1)
        low = lcm(low, o)
    return pred, low


def cmd_kummer(nmax, mmax):
    bases = [2, 3, 5, 6, 7, 10, 12, 18, 72, 4, 8, 9, 16, 25, 27, 36, 64, 100, 144]
    bad, count, shown = [], 0, []
    for b in bases:
        a, j = perfect_power(b)
        for n in range(1, nmax + 1):
            for M in range(n, mmax + 1, n):
                pred, low = kummer_degree(b, n, M)
                count += 1
                if pred != low:
                    bad.append((b, n, M, pred, low))
            f = conductor(sqfree_split(a)[1])
            M = lcm(lcm(n, f), 8)
            shown.append((b, a, j, n, n1_of(n), n1_corrected(b, n), M, kummer_degree(b, n, M)))
    print("degree of b^(1/n) over Q(zeta_M): %d triples (b, n, M), n <= %d, n | M, M <= %d" % (count, nmax, mmax))
    print("prediction not certified for: %s" % (bad or "none"))
    print("examples, with M a multiple of n, 8 and the conductor of Q(sqrt(a)):")
    print("  b = a^j     n   n1  n1'   M    degree (predicted, certified lower bound)")
    for b, a, j, n, n1, n1c, M, (pred, low) in shown:
        if n in (3, 4, 6, 8, 12) and n <= nmax:
            print("  %3d = %d^%d  %2d  %2d  %2d  %4d   %d, %d%s"
                  % (b, a, j, n, n1, n1c, M, pred, low, "" if n1 == n1c else "    (n1' < n1)"))


# ---------------------------------------------------------------------------------------
# 6. Self-test
# ---------------------------------------------------------------------------------------

def cmd_selftest():
    ok = True

    def check(cond, text):
        nonlocal ok
        ok = ok and bool(cond)
        print("  %s: %s" % ("ok  " if cond else "FAIL", text))

    print("direct summation")
    mp.dps = 50
    bbp = [4, 0, 0, -8, -4, -8, 0, 0]                 # the BBP formula as a pattern of F_(2,2)
    check(abs(series(2, 2, bbp) - pi) < mpf(10) ** (-48), "BBP formula in F_(2,2), period 8, is pi")
    n, rho = bailey_to_step(2, 4, 8, [4, 0, 0, -2, -1, -1, 0, 0])
    check(n == 2 and rho == bbp, "Bailey (16, 8, (4,0,0,-2,-1,-1,0,0)) -> step 2, pattern (4,0,0,-8,-4,-8,0,0)")
    ex = [9, 0, 0, -18, 0, 0]                         # 9 sum 4^(-j) (1/(6j+1) - 1/(6j+4)) in F_(2,3)
    mp.dps = 50
    check(abs(series(2, 3, ex) - pi * sqrt(3) * mpf(2) ** (mpf(1) / 3)) < mpf(10) ** (-48),
          "9 sum 4^(-j) (1/(6j+1) - 1/(6j+4)) = pi sqrt(3) 2^(1/3), a series of F_(2,3)")
    G = [6, 0, -6, 0, 6, 0, -6, 0, 6, 0, -6, 0]
    Z1 = [0, 1, -2, 0, 1, 4, 0, 3, 2, 4, -1, 0]
    Z2 = [1, -3, -4, -3, 1, 0, -1, 3, 4, 3, -1, 0]
    mp.dps = 50
    check(abs(series(3, 2, G) - pi * sqrt(3)) < mpf(10) ** (-48)
          and abs(series(3, 2, Z1)) < mpf(10) ** (-48) and abs(series(3, 2, Z2)) < mpf(10) ** (-48),
          "base 3: S(G) = pi sqrt(3), S(Z1) = S(Z2) = 0")

    # every power of 2 has a formula for pi: the BBP formula with its terms grouped j at a time
    good = True
    for j in (2, 3, 5):
        a = []
        for s in range(j):
            a += [Fraction(x, 16 ** s) for x in (4, 0, 0, -2, -1, -1, 0, 0)]
        v = bailey_series(2 ** j, 4, 8 * j, a)
        mp.dps = 50
        good = good and abs(v - pi) < mpf(10) ** (-48)
    check(good, "bases 4, 8, 32: sum_i (2^j)^(-4i) sum_{l=1..8j} a_l/(8j i + l) = pi (BBP, grouped)")
    # found by this program (probe A with the targets pi*c1, pi*c2*sqrt3, pi*c1*sqrt2): base 3 has
    # series of step 6 and 4 for pi times an irrational algebraic number that is not cyclotomic
    c6, c4 = mpf(3) ** (mpf(1) / 6), mpf(3) ** (mpf(1) / 4)
    check(abs(series(3, 6, [9, 0, 0, -3, 0, 0, -9, 0, 0, -9, 0, 0]) - 2 * pi * c6) < mpf(10) ** (-48),
          "base 3, step 6: sum 9^(-j) (9/(12j+1) - 3/(12j+4) - 3/(12j+7) - 3/(12j+10)) = 2 pi 3^(1/6)")
    check(abs(series(3, 6, [0, 27, 0, 0, 9, 0, 0, 9, 0, 0, -9, 0]) - 2 * pi * c6 ** 5) < mpf(10) ** (-48),
          "base 3, step 6: the pattern (0,27,0,0,9,0,0,9,0,0,-9,0) of period 12 has the sum 2 pi 3^(5/6)")
    check(abs(series(3, 4, [6, 0, 0, 0, -6, 0, 2, 0, 12, 0, 2, 0, -6, 0, 0, 0, 6, 0, -2, 0, -12, 0, -2, 0])
              - pi * c4 * sqrt(2)) < mpf(10) ** (-48),
          "base 3, step 4: a pattern of period 24 on odd k has the sum pi sqrt(2) 3^(1/4)")

    print("probe A, base 2")
    r = probe_sums(2, 2, 8, quiet=True, keep=True)
    check(r["rank"] == 2 and r["with_target"][0] and in_span(r["rels"], [-1] + bbp),
          "F_(2,2), P = 8: rank 2, and the BBP formula is in the span")
    r = probe_sums(2, 8, 32, quiet=True, keep=True)
    dil = [0] * 32
    for k in range(1, 9):
        dil[4 * k - 1] = 4 * bbp[k - 1]
    check(r["rank"] == 2 and r["lemma_ok"] and r["dim_rest"] == 0 and in_span(r["rels"], [-1] + dil),
          "F_(2,8), P = 32: rank 2, all on k = 0 (mod 4), contains the BBP formula (k -> 4k)")
    r = probe_sums(2, 3, 18, targets=("pi", "pi*sqrt3*c1", "pi*sqrt3*c2"), quiet=True, keep=True)
    check(r["lemma_ok"] and not r["with_target"][0] and r["with_target"][1] and r["with_target"][2]
          and in_span(r["rels"], [0, -1, 0] + ex * 3),
          "F_(2,3), P = 18: no pi; pi sqrt(3) 2^(1/3) on k = 1 (mod 3) (the example) and"
          " pi sqrt(3) 2^(2/3) on k = 2 (mod 3); rank %d" % r["rank"])
    r = probe_sums(2, 4, 48, quiet=True)
    check(r["rank"] == 6 and r["lemma_ok"] and r["dim_sub"] == 6,
          "F_(2,4), P = 48: rank 6, all on even k (as in outside_family_findings.md)")

    print("probes A and B, base 3")
    r = probe_sums(3, 2, 12, targets=("pi", "pi*sqrt3"), quiet=True, keep=True)
    check(r["rank"] == 3 and not r["with_target"][0] and r["with_target"][1]
          and in_span(r["rels"], [0, -1] + G) and in_span(r["rels"], [0, 0] + Z1)
          and in_span(r["rels"], [0, 0] + Z2),
          "F_(3,2), P = 12: rank 3 = span of G (pi sqrt(3)), Z1, Z2; no pi")
    r = probe_logs(3, 2, 12, quiet=True)
    check(r["rank"] == 3 and r["with_pi"], "logarithms, base 3, step 2, N = 12: rank 3, with 2 pi i")
    r = probe_logs(2, 2, 24, quiet=True)
    check(r["rank"] == 8 and r["with_pi"],
          "logarithms, base 2, step 2, N = 24: rank 8, with 2 pi i (as baseb_explore.py relations 2 24)")

    print("the guard: bases with no relation")
    r = probe_sums(5, 2, 20, quiet=True)
    check(r["rank"] == 0, "F_(5,2), P = 20: rank 0 (certificate: none with sum of |coefficients| below 2^%s)"
          % r["bound_bits"])
    r = probe_logs(10, 2, 40, quiet=True)
    check(r["rank"] == 0, "logarithms, base 10, step 2, N = 40: rank 0 (none with sum of |exponents| below 2^%s)" % r["bound_bits"])

    print("perfect powers: the lemma needs n1' = n1 / gcd(n1, j)")
    r = probe_sums(9, 4, 12, targets=("pi", "pi*sqrt3"), quiet=True)
    check(r["rank"] == 3 and r["lemma_ok"] and not r["naive_ok"] and r["n1c"] == 1,
          "F_(9,4) = F_(3,2), P = 12: rank 3; the split modulo n1 = 2 fails (Z1 on even k is not 0)")
    r = probe_sums(8, 3, 6, quiet=True)
    check(r["rank"] == 1 and r["lemma_ok"] and not r["naive_ok"] and r["n1c"] == 1,
          "F_(8,3) = F_(2,1), P = 6: rank 1 (log(3/4) = log(3/2) + log(1/2)); the split modulo 3 fails")
    r = probe_sums(4, 4, 8, quiet=True)
    check(r["rank"] == 2 and r["with_target"][0] and not r["naive_ok"],
          "F_(4,4) = F_(2,2), P = 8: the BBP formula; its terms with even k alone are not pi")
    mp.dps = 30
    check(abs(series(3, 2, [0, 1, 0, 0, 0, 4, 0, 3, 0, 4, 0, 0])) > 0.1,
          "direct: the part of Z1 on even k has a non-zero sum")

    print("degree of b^(1/n) over Q(zeta_M)")
    for b, n, M in [(2, 8, 48), (3, 6, 72), (10, 4, 40), (10, 6, 120), (12, 4, 24), (9, 4, 24),
                    (8, 3, 24), (4, 6, 24), (10, 4, 12)]:
        pred, low = kummer_degree(b, n, M)
        check(pred == low, "b = %d, n = %d, M = %d: degree %d (n1 = %d, n1' = %d)"
              % (b, n, M, pred, n1_of(n), n1_corrected(b, n)))
    print("selftest: %s" % ("all ok" if ok else "FAILED"))
    return ok


# ---------------------------------------------------------------------------------------
# 7. The standard set of runs, and the table
# ---------------------------------------------------------------------------------------

BASES_MAIN = (3, 5, 6, 7, 10, 12)
BASES_POWER = (9, 4, 8)
STEPS = (1, 2, 3, 4, 6)


def periods(b, n, maxP):
    """The periods of the standard set: every multiple of n up to 60 (up to 100 for base 10),
    then the multiples of 12 and of the conductor of Q(sqrt(b)) in the list below."""
    if b in BASES_POWER:
        ps = {12, 24, 48, 72}
    else:
        ps = {12, 24, 36, 48, 60, 72, 84, 96, 120, 144}
        ps |= set(range(n, (100 if b == 10 else 60) + 1, n))
        if b in (5, 10):
            ps |= {20, 40, 80, 100}
        if b == 7:
            ps |= {28, 56}
    return sorted(P for P in ps if P % n == 0 and P <= maxP)


def sum_targets(b):
    a = perfect_power(b)[0]
    return ("pi", "pi*sqrt3") if a == 3 else ("pi",)


def run_job(job):
    kind, b, n, P = job
    try:
        if kind == "sums":
            res = probe_sums(b, n, P, targets=sum_targets(b), quiet=True)
        else:
            res = probe_logs(b, n, P, quiet=True)
    except Exception as exc:                      # keep the pool alive; the error is recorded
        res = {"probe": kind, "b": b, "n": n, "P": P, "error": repr(exc)}
    return res


def cmd_table(out, procs, maxP):
    jobs = []
    for b in BASES_MAIN + BASES_POWER:
        for n in STEPS:
            for P in periods(b, n, maxP):
                jobs.append(("sums", b, n, P))
                jobs.append(("logs", b, n, P))
    done = set()
    try:
        with open(out) as fh:
            for line in fh:
                d = json.loads(line)
                if "error" not in d:
                    done.add((d["probe"], d["b"], d["n"], d["P"]))
    except FileNotFoundError:
        pass
    jobs = [j for j in jobs if j not in done]
    print("%d runs already in %s" % (len(done), out))
    run_pool(jobs, out, procs)


def run_pool(jobs, out, procs):
    from concurrent.futures import ProcessPoolExecutor, as_completed
    jobs = sorted(jobs, key=lambda j: -j[3])
    print("%d runs to do, %d processes" % (len(jobs), procs))
    sys.stdout.flush()
    t0 = time.time()
    with ProcessPoolExecutor(max_workers=procs) as pool:
        futs = [pool.submit(run_job, j) for j in jobs]
        for i, fut in enumerate(as_completed(futs)):
            res = fut.result()
            with open(out, "a") as fh:
                fh.write(json.dumps(res) + "\n")
            print("  [%d/%d, %.0f s] %s b=%d n=%d P=%d: %s"
                  % (i + 1, len(jobs), time.time() - t0, res["probe"], res["b"], res["n"], res["P"],
                     res.get("error") or "rank %d" % res["rank"]))
            sys.stdout.flush()


def cmd_report(files):
    """One line per (b, n), from the JSON lines of one or several files."""
    rows = {}
    for out in files:
        with open(out) as fh:
            for line in fh:
                d = json.loads(line)
                if "error" in d:
                    print("ERROR in run: %s" % d)
                    continue
                rows[(d["b"], d["n"], d["P"], d["probe"])] = d
    order = (2,) + BASES_MAIN + BASES_POWER
    keys = sorted({k[:2] for k in rows}, key=lambda k: (order.index(k[0]) if k[0] in order else 99, k[1]))

    def fmt(pairs):
        """pairs (P, value): the value if constant, otherwise the periods of each value."""
        vals = sorted({v for _, v in pairs}, key=str)
        if len(vals) == 1:
            return str(vals[0])
        parts = []
        for v in vals:
            Ps = [P for P, x in pairs if x == v]
            if v == 0:
                parts.append("0 at %d periods" % len(Ps))
            else:
                parts.append("%s at P = %s" % (v, ",".join(map(str, Ps[:6])) + (",..." if len(Ps) > 6 else "")))
        return "; ".join(parts)

    print("A = probe A (class sums; targets pi, and pi*sqrt3 for the bases 3 and 9); B = probe B (logarithms).")
    print("| b | n | periods: number (largest; of A, of B) | A: rank | A: a relation with pi | A: split of the lemma |"
          " B: rank | B: with 2 pi i | B: rank not lifted from step 2 or 1 | smallest bound (A, B) |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for b, n in keys:
        A = [rows[k] for k in sorted(rows) if k[:2] == (b, n) and k[3] == "sums"]
        B = [rows[k] for k in sorted(rows) if k[:2] == (b, n) and k[3] == "logs"]
        nper = len({d["P"] for d in A + B})
        a_pi = "YES" if any(d["with_target"][0] for d in A) else "no"
        if any(len(d["targets"]) > 1 and d["with_target"][1] for d in A):
            a_pi += " (pi*sqrt3: yes)"
        lem = "-"
        if any(d["rank"] for d in A):
            lem = "holds" if all(d["lemma_ok"] for d in A) else "FAILS"
            if not all(d["naive_ok"] for d in A):
                lem += " mod n1' = %d (not mod n1 = %d)" % (A[0]["n1c"], A[0]["n1"])
        b_pi = "YES" if any(d["with_pi"] for d in B) else "no"
        new = fmt([(d["P"], d["rank"] - d["lifted"]) for d in B if d["lifted"] is not None])
        bounds = "2^%s, 2^%s" % (min((d["bound_bits"] for d in A if d["bound_bits"] is not None), default="-"),
                                 min((d["bound_bits"] for d in B if d["bound_bits"] is not None), default="-"))
        print("| %d | %d | %d (%s, %s) | %s | %s | %s | %s | %s | %s | %s |"
              % (b, n, nper, max((d["P"] for d in A), default="-"), max((d["P"] for d in B), default="-"),
                 fmt([(d["P"], d["rank"]) for d in A]), a_pi, lem,
                 fmt([(d["P"], d["rank"]) for d in B]), b_pi, new, bounds))
    print()
    for b in sorted({k[0] for k in rows}):
        sub = [d for k, d in rows.items() if k[0] == b]
        if not any(d["rank"] for d in sub):
            print("base %d: no relation in any of the %d runs (steps %s; %d periods, the largest %d)"
                  % (b, len(sub), ",".join(map(str, sorted({d["n"] for d in sub}))),
                     len({(d["n"], d["P"]) for d in sub}), max(d["P"] for d in sub)))
    total = sum(d["t_lll"] for d in rows.values())
    print("%d runs; total LLL time %.0f s; largest lattice dimension %d"
          % (len(rows), total, max(k[2] for k in rows) + 2))


if __name__ == "__main__":
    args = sys.argv[1:]
    cmd = args[0] if args else ""
    if cmd == "selftest":
        sys.exit(0 if cmd_selftest() else 1)
    elif cmd == "sums":
        b, n, P = int(args[1]), int(args[2]), int(args[3])
        probe_sums(b, n, P, targets=tuple(args[4:]) or ("pi",))
    elif cmd == "logs":
        probe_logs(int(args[1]), int(args[2]), int(args[3]))
    elif cmd == "reduce":
        cmd_reduce()
    elif cmd == "kummer":
        ints = [int(x) for x in args[1:]]
        cmd_kummer(*(ints + [12, 240][len(ints):])[:2])
    elif cmd == "table":
        cmd_table(args[1], int(args[2]) if len(args) > 2 else 8, int(args[3]) if len(args) > 3 else 144)
    elif cmd == "jobs":
        # jobs OUT PROCS kind:b:n:P ...   (kind is sums or logs): extra runs, appended to OUT
        todo = [(k, int(x), int(y), int(z)) for k, x, y, z in (a.split(":") for a in args[3:])]
        run_pool(todo, args[1], int(args[2]))
    elif cmd == "report":
        cmd_report(args[1:])
    else:
        print(__doc__)
