"""Rational bases p/q > 1: exploration of the series

    S(rho) = sum over k >= 1 of rho(k) (q/p)^floor(k/2) / k,    rho rational and periodic,

for coprime integers p > q >= 1 (q = 1 is the integer base p of baseb_explore.py).

    python ratbase_explore.py selftest                checks of the program on known cases
    python ratbase_explore.py relations P Q N         the lattice of relations among 2 pi i and the
                                                      Log(1 - r sqrt(Q/P)), r^N = 1, with all checks
    python ratbase_explore.py table [PMAX PROCS]      one line per base p/q, p <= PMAX (default 16), N = 24,
                                                      48, 60, 72, 84, 96, 120 (and lcm(f, 4) <= 168), in parallel
    python ratbase_explore.py extra PROCS P:Q:N ...   more lattice runs, one line each
    python ratbase_explore.py scan [PMAX NMAX]        exceptional classes (exact norms) and the set R0
    python ratbase_explore.py size [PMAX]             the size condition: where it fails, and a direct
                                                      look at every triple (p, q, m) where it fails
    python ratbase_explore.py aurif P Q JMAX          the two-class case: norms, the character-sum bound
    python ratbase_explore.py describe P Q            every formula of the base (3/2 and 4/3): patterns,
                                                      values, zero relations, fewest terms, periods
    python ratbase_explore.py formulas                the two formulas (a), (b) of P03, by direct summation
    python ratbase_explore.py sums P Q PERIOD [T ...] theory-free probe: pi (or targets T) and class sums
    python ratbase_explore.py step P Q n N            2 pi i and Log(1 - r (Q/P)^(1/n)), r^N = 1
    python ratbase_explore.py steps PROCS P:Q:n:N ... several such runs, one line each

Needs mpmath, sympy and python-flint (python-flint on PYTHONPATH, as for baseb_explore.py).
Prints ASCII only. Findings: research/2026-11-22-rational-bases/00_summary.md.

NOTHING HERE IS A PROOF. A lattice search finds every integer relation whose sum of
|coefficients| is below the bound printed with it, at ONE period. The norms are exact integers
(a product evaluated to 25 digits beyond the size of the result, then compared with an exact
product formula).

Setting. t = sqrt(p/q), u = sqrt(pq), pq = s^2 d with d squarefree, f the conductor of Q(sqrt d).

    S(rho) = - sum over roots of unity r of D_r Log(1 - r/t),    1 - r/t = x_r / sqrt(p),
    x_r = sqrt(p) - r sqrt(q),      x_r x_(-r) = p - r^2 q,
    product over the primitive m-th roots s of (p - s q) = Phi_m(p, q)   (homogeneous).

x_r is an algebraic integer prime to pq. In an integer relation prod (1 - r/t)^(z_r) = root of
unity the sum of the z_r is 0 (look at a prime above p), so it is a relation among the x_r.

Vocabulary (as in baseb_explore.py, with d the squarefree part of pq).

  class       Roots r of the same order n whose numbers r/t are conjugate over Q. Two classes
              ("+", "-") when d > 1, f divides n and not (4 | n and f | n/2): the Aurifeuillian
              case (then m = ord(r^2) has m/(eta d) odd, eta = 1 for d = 1 mod 4, else 2).
              Otherwise one class ("all").
  norm        One class: Phi_m(p, q), m = ord(r^2) (for pq a square, p = a^2, q = b^2:
              Phi_n(a, b), n = ord(r)). Two classes: N+, N- with N+ N- = Phi_m(p, q)^e,
              e = 2 if 4 | n, else 1; N+ is the product of the conjugates of x_r.
  good prime  A prime l dividing the norm and not dividing 2 p q n. Some prime ideal above l
              contains x_r, and it contains x_r' only if r'/r has order a power of l.
  exceptional A class with no good prime.
  R0          The exceptional roots, closed under: r' in R0, l an odd prime dividing ord(r') and
              the norm of the class of r'  =>  the l'-part of r' is in R0. Every integer relation
              is supported on R0.
  size cond.  SC(p, q, m): Phi_m(p, q) > g (sqrt p + sqrt q)^phi(m), g = q0 (the largest prime
              factor of m) if q0 divides Phi_m(p, q), else 1. It implies a good prime for every
              root r with ord(r^2) = m (summary, section 3). SC2(p, q, m) is the same with
              U_m(p, q) = prod over the primitive m-th roots s of (p + q + sqrt(2pq(1 + Re s)))^(1/2)
              in place of (sqrt p + sqrt q)^phi(m); it is weaker than SC and gives the same.
"""
import sys
import time
from fractions import Fraction
from functools import lru_cache
from math import gcd, isqrt, log as flog, sqrt as fsqrt

from mpmath import mp, mpf, mpc, pi, sqrt, log, floor


# ---------------------------------------------------------------------------------------
# 0. Arithmetic of the base
# ---------------------------------------------------------------------------------------

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


def fund_disc(delta):
    """The discriminant of Q(sqrt(delta)), delta squarefree (positive or negative), not 1."""
    return delta if delta % 4 == 1 else 4 * delta


def kron(D, c):
    """Kronecker symbol (D / c) for a discriminant D (D = 0 or 1 mod 4, any sign) and c >= 1."""
    from sympy import jacobi_symbol
    if gcd(D, c) > 1:
        return 0
    res = 1
    while c % 2 == 0:
        c //= 2
        res *= 1 if D % 8 in (1, 7) else -1
    return res * (int(jacobi_symbol(D % c, c)) if c > 1 else 1)


@lru_cache(maxsize=None)
def base_data(p, q):
    """(s, d, f): pq = s^2 d, f the conductor of Q(sqrt(d)) (f = 1 when pq is a square)."""
    assert p > q >= 1 and gcd(p, q) == 1
    s, d = sqfree_split(p * q)
    return s, d, conductor(d)


def is_split(p, q, n):
    """True when the roots of order n fall into two classes."""
    s, d, f = base_data(p, q)
    if d == 1 or n % f:
        return False
    return not (n % 4 == 0 and (n // 2) % f == 0)


@lru_cache(maxsize=None)
def cyclo_hom(m, p, q):
    """Phi_m(p, q) = q^phi(m) Phi_m(p/q) = prod over d | m of (p^d - q^d)^mu(m/d), exactly."""
    from sympy import divisors, mobius
    num, den = 1, 1
    for dd in divisors(m):
        mu = mobius(m // dd)
        if mu == 1:
            num *= p ** dd - q ** dd
        elif mu == -1:
            den *= p ** dd - q ** dd
    assert num % den == 0
    return num // den


def strip(N, m):
    """Remove from N every prime factor of m; return the cofactor."""
    from sympy import primefactors
    for l in primefactors(m):
        while N % l == 0:
            N //= l
    return N


def show_int(N):
    from sympy import factorint
    if N == 1:
        return "1"
    if N > 10 ** 40:
        return "%d digits" % len(str(N))
    return "*".join("%d^%d" % (l, e) if e > 1 else str(l) for l, e in sorted(factorint(N).items()))


def coprime_pairs(pmax, pmin=2):
    return [(p, q) for p in range(pmin, pmax + 1) for q in range(1, p) if gcd(p, q) == 1]


def is_perfect_power_rat(p, q):
    """(a, b, j): p/q = (a/b)^j with a/b not a perfect power in Q (j = gcd of the exponents)."""
    from sympy import factorint
    exps = list(factorint(p).values()) + list(factorint(q).values())
    j = 0
    for e in exps:
        j = gcd(j, e)
    j = max(j, 1)
    a = round(p ** (1.0 / j))
    b = round(q ** (1.0 / j))
    assert a ** j == p and b ** j == q
    return a, b, j


# ---------------------------------------------------------------------------------------
# 1. Classes, norms, exceptional roots, the set R0
# ---------------------------------------------------------------------------------------

@lru_cache(maxsize=None)
def classes(p, q, n):
    """The classes of roots of order n: a tuple of (label, norm, exponents).

    exponents: the a (1 <= a <= n, prime to n) with zeta_n^a in the class."""
    s, d, f = base_data(p, q)
    units = tuple(a for a in range(1, n + 1) if gcd(a, n) == 1)
    if d == 1:
        return (("all", abs(cyclo_hom(n, isqrt(p), isqrt(q))), units),)
    m = n // gcd(n, 2)                       # the order of r^2
    if not is_split(p, q, n):
        return (("all", abs(cyclo_hom(m, p, q)), units),)
    chi = {a: kron(f, a) for a in units}
    old = mp.dps
    mp.dps = int(len(units) * flog(fsqrt(p) + fsqrt(q), 10)) + 60
    sp, sq = sqrt(mpf(p)), sqrt(mpf(q))
    zeta = {a: mp.expjpi(mpf(2 * a) / n) for a in units}
    out = []
    for eps in (1, -1):
        prod = mpc(1)
        for a in units:
            prod *= eps * chi[a] * sp - zeta[a] * sq
        val = int(mp.nint(prod.real))
        assert abs(prod.imag) < mpf(10) ** (-25) and abs(prod.real - val) < mpf(10) ** (-25), (p, q, n)
        out.append(("+" if eps == 1 else "-", abs(val),
                    tuple(a for a in units if chi[a] == eps)))
    mp.dps = old
    e = 2 if n % 4 == 0 else 1
    assert out[0][1] * out[1][1] == abs(cyclo_hom(m, p, q)) ** e, (p, q, n)      # N+ N- = Phi^e
    return tuple(out)


def class_of(p, q, r):
    """(label, norm) of the class of the root exp(2 pi i r), r a Fraction."""
    n, a = r.denominator, r.numerator % r.denominator
    if n == 1:
        a = 1
    for label, N, exps in classes(p, q, n):
        if a in exps:
            return label, N
    raise ValueError((p, q, r))


def exceptional_classes(p, q, nmax):
    """[(n, label, norm, exponents)] for the classes of order <= nmax with no good prime."""
    out = []
    for n in range(1, nmax + 1):
        for label, N, exps in classes(p, q, n):
            if strip(N, 2 * p * q * n) == 1:
                out.append((n, label, N, exps))
    return out


def l_prime_part(r, l):
    """The l'-part of the root of unity exp(2 pi i r)."""
    n = r.denominator
    qq = 1
    while (n // qq) % l == 0:
        qq *= l
    n1 = n // qq
    u = (qq * pow(qq, -1, n1)) % n if n1 > 1 else 0      # u = 1 mod n1, u = 0 mod qq
    return Fraction(r.numerator * u, n) % 1


def closure_R0(p, q, exc):
    """The set R0 as a set of Fractions (a/n stands for exp(2 pi i a/n))."""
    from sympy import primefactors
    R0, queue = set(), []
    for n, label, N, exps in exc:
        for a in exps:
            r = Fraction(a, n) % 1
            R0.add(r)
            queue.append(r)
    while queue:
        r = queue.pop()
        label, N = class_of(p, q, r)
        for l in primefactors(r.denominator):
            if l % 2 and N % l == 0:
                r1 = l_prime_part(r, l)
                if r1 not in R0:
                    R0.add(r1)
                    queue.append(r1)
    return R0


def describe_exc(exc):
    if not exc:
        return "none"
    return ", ".join("%d%s: %s" % (n, "" if label == "all" else label, show_int(N))
                     for n, label, N, _ in exc)


def describe_R0(R0):
    if not R0:
        return "empty"
    by = {}
    for r in R0:
        by.setdefault(r.denominator, []).append(r.numerator)
    return "; ".join("order %d: exponents %s" % (n, sorted(v)) for n, v in sorted(by.items()))


def predicted_exceptional(p, q):
    """The exceptional classes (order, label) that section 3 of the summary predicts.

    Orders 1, 2, 4 (the fourth roots) by the two numbers p - q and p + q; beyond them only the
    five bases 2, 3, 4, 3/2, 4/3."""
    def pow2(x):
        return x >= 1 and x & (x - 1) == 0
    special = {(2, 1): [(1, "all"), (2, "all"), (8, "+"), (12, "all"), (24, "+"), (40, "+")],
               (3, 1): [(1, "all"), (2, "all"), (4, "all"), (12, "+")],
               (4, 1): [(1, "all"), (6, "all")],
               (3, 2): [(1, "all"), (2, "all"), (24, "+")],
               (4, 3): [(1, "all"), (2, "all"), (12, "+")]}
    if (p, q) in special:
        return special[(p, q)]
    s, d, f = base_data(p, q)
    out = []
    if d == 1:
        a, b = isqrt(p), isqrt(q)
        if pow2(a - b):
            out.append((1, "all"))
        if pow2(a + b):
            out.append((2, "all"))
    else:
        if pow2(p - q):
            out += [(1, "all"), (2, "all")]
        if pow2(p + q):
            out.append((4, "all"))
    return out


def cmd_scan(pmax, nmax):
    bad, withbig = [], []
    for p, q in coprime_pairs(pmax):
        s, d, f = base_data(p, q)
        exc = exceptional_classes(p, q, nmax)
        R0 = closure_R0(p, q, exc)
        got = [(n, label) for n, label, N, _ in exc]
        pred = [x for x in predicted_exceptional(p, q) if x[0] <= nmax]
        if got != pred:
            bad.append((p, q, got, pred))
        big = [(n, label) for n, label in got if n not in (1, 2, 4)]
        if big:
            withbig.append((p, q))
        print("%d/%d (d = %d, f = %d): exceptional (order, class: norm): %s | R0: %s"
              % (p, q, d, f, describe_exc(exc), describe_R0(R0)))
        sys.stdout.flush()
    print()
    print("orders up to %d; bases with an exceptional class outside the fourth roots: %s"
          % (nmax, ", ".join("%d/%d" % x for x in withbig) or "none"))
    print("disagreements with the prediction: %s" % (bad or "none"))


# ---------------------------------------------------------------------------------------
# 2. The lattice of relations
# ---------------------------------------------------------------------------------------

def log_values(p, q, N, prec, n=2):
    """[(Re, Im)] of Log(1 - zeta_N^a (q/p)^(1/n)), a = 0..N-1, then (0, 2 pi)."""
    mp.prec = prec
    x = (mpf(q) / p) ** (mpf(1) / n)
    vals = []
    for a in range(N):
        w = log(1 - mp.expjpi(mpf(2 * a) / N) * x)
        vals.append((w.real, w.imag))
    vals.append((mpf(0), 2 * pi))
    return vals


def lattice(vals, Wc, extra):
    """Integer relations among the rows of vals (tuples of reals known to Wc + extra + 64 bits).

    A row of the reduced basis is accepted only if the combination vanishes to Wc + extra - 100
    bits (the lattice saw Wc bits). Certificate: with the accepted rows first, the smallest
    Gram-Schmidt length mu of the other rows; an integer relation z outside the span of those
    found gives a lattice vector of length at most sqrt(q + 1) sum|z_i| and at least mu.
    Returns (relations, bound, seconds)."""
    from flint import fmpz_mat
    m, qd = len(vals), len(vals[0])
    mp.prec = Wc + extra + 64
    scale = mpf(2) ** Wc
    rows = []
    for i, v in enumerate(vals):
        row = [0] * (m + qd)
        row[i] = 1
        for j in range(qd):
            row[m + j] = int(floor(v[j] * scale))
        rows.append(row)
    t0 = time.time()
    red = fmpz_mat(rows).lll()
    t_lll = time.time() - t0
    rel_rows, other_rows = [], []
    for i in range(m):
        row = [int(red[i, j]) for j in range(m + qd)]
        coef = row[:m]
        tol = (sum(abs(c) for c in coef) + 1) * mpf(2) ** (-(Wc + extra - 100))
        ok = all(abs(mp.fdot(coef, [v[j] for v in vals])) < tol for j in range(qd))
        (rel_rows if ok else other_rows).append(row)
    bound = None
    if other_rows:
        mp.prec = 300
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
        bound = int(floor(sqrt(best / (qd + 1))))
    mp.prec = Wc + extra + 64
    return [r[:m] for r in rel_rows], bound, t_lll


def bits(x):
    return "-" if x is None else "2^%d" % (int(x).bit_length() - 1)


def rank_Q(rows):
    from flint import fmpz_mat
    rows = [r for r in rows if any(r)]
    if not rows:
        return 0
    return fmpz_mat(rows).rank()


def find_relations(p, q, N, bits_per=30, n=2):
    Wc = bits_per * (N + 1) + 300
    extra = 400
    vals = log_values(p, q, N, Wc + extra + 64, n)
    rels, bound, t_lll = lattice(vals, Wc, extra)
    return {"p": p, "q": q, "N": N, "bits": Wc, "rels": rels, "rank": len(rels), "bound": bound,
            "vals": vals, "t_lll": t_lll}


def galois_group(p, q, N):
    """The automorphisms of Q(zeta_N, t) as pairs (a, eps): zeta -> zeta^a, t -> eps t."""
    s, d, f = base_data(p, q)
    out = []
    for a in range(1, N + 1):
        if gcd(a, N) > 1:
            continue
        if d == 1:
            out.append((a, 1))
        elif N % f == 0:
            out.append((a, kron(f, a)))
        else:
            out.append((a, 1))
            out.append((a, -1))
    return out


def lambda_matrix(res):
    """Rows indexed by the automorphisms g, columns by the relations z_j: the coefficient of
    2 pi i in the relation g.z_j, where (g.z) at eps r^a is z at r. Needs N even."""
    p, q, N, rels, vals = res["p"], res["q"], res["N"], res["rels"], res["vals"]
    assert N % 2 == 0
    mp.prec = res["bits"] + 400
    two_pi = 2 * pi
    G = galois_group(p, q, N)
    A = []
    for a, eps in G:
        row = []
        for z in rels:
            w = [0] * N
            for k in range(N):
                if z[k]:
                    w[(a * k + (N // 2 if eps == -1 else 0)) % N] = z[k]
            re = sum(c * vals[k][0] for k, c in enumerate(w) if c)
            im = sum(c * vals[k][1] for k, c in enumerate(w) if c)
            lam = -im / two_pi
            m = int(mp.nint(lam))
            assert abs(re) < mpf(2) ** (-res["bits"]) and abs(lam - m) < mpf(2) ** (-res["bits"]), \
                "the lattice is not stable under the Galois group"
            row.append(m)
        A.append(row)
    return G, A


def value_fields(p, q, N, G, A):
    """The squarefree delta >= 1 for which pi sqrt(delta) is a value: the quadratic characters
    psi of the group with sum over g of psi(g) lambda(g.z) != 0 for some relation z. psi belongs
    to the imaginary quadratic field Q(sqrt(-delta)) inside Q(zeta_N, sqrt d)."""
    from sympy import primefactors
    s, d, f = base_data(p, q)
    primes = primefactors(2 * N * d)
    found = []
    for mask in range(1 << len(primes)):
        delta = 1
        for i, l in enumerate(primes):
            if mask >> i & 1:
                delta *= l
        D0 = fund_disc(-delta)
        if N % abs(D0) == 0:
            psi = [kron(D0, a) for a, eps in G]
        elif d > 1 and N % f:
            s1, d1 = sqfree_split(delta * d)
            D1 = fund_disc(-d1)                  # sqrt(-delta) = sqrt(d) sqrt(-d1) / rational
            if N % abs(D1):
                continue
            psi = [eps * kron(D1, a) for a, eps in G]
        else:
            continue
        if any(sum(psi[i] * A[i][j] for i in range(len(G))) for j in range(len(A[0]))):
            found.append(delta)
    return sorted(found)


def verify_exact(p, q, N, z):
    """Exact check of prod (1 - r/t)^(z_r) = 1 in Z[zeta_M], M = lcm(N, f, 2).

    With U = 2u = 2 sqrt(pq), an element of Z[zeta_M] (a Gauss sum), 1 - r/t = (U - 2qr)/U and
    the identity reads prod (U - 2qr)^(z_r) = U^(sum z_r)."""
    from flint import fmpz_poly
    s, d, f = base_data(p, q)
    M = N * f // gcd(N, f)
    if M % 2:
        M *= 2
    phi = fmpz_poly.cyclotomic(M)

    def mono(k):
        return fmpz_poly([0] * (k % M) + [1])

    if d == 1:
        U = fmpz_poly([2 * s])
    else:
        g = fmpz_poly([0])
        for c in range(1, f):
            ch = kron(f, c)
            if ch:
                g = g + ch * mono(c * (M // f))
        U = ((2 * s if f == d else s) * g) % phi
    assert (U * U) % phi == fmpz_poly([4 * p * q]), "Gauss sum"
    lhs, rhs, Z = fmpz_poly([1]), fmpz_poly([1]), 0
    for k in range(N):
        e = z[k]
        if not e:
            continue
        Z += e
        fac = (U - 2 * q * mono(k * (M // N))) % phi
        for _ in range(abs(e)):
            if e > 0:
                lhs = (lhs * fac) % phi
            else:
                rhs = (rhs * fac) % phi
    for _ in range(abs(Z)):
        if Z > 0:
            rhs = (rhs * U) % phi
        else:
            lhs = (lhs * U) % phi
    return lhs == rhs


def format_relation(z, N):
    terms = []
    for a, c in enumerate(z[:N]):
        if c:
            r = Fraction(a, N)
            terms.append("%+d L(%d/%d)" % (c, r.numerator, r.denominator))
    s = " ".join(terms)
    if z[N]:
        s += "  %+d (2 pi i)" % z[N]
    return s


def analyse(p, q, N, R0=None, nmax=None, quiet=True, show=False, bits_per=30):
    """Relations of base p/q on the N-th roots of unity (N even), with all the checks."""
    res = find_relations(p, q, N, bits_per=bits_per)
    rels = res["rels"]
    if R0 is None:
        R0 = closure_R0(p, q, exceptional_classes(p, q, nmax or max(N, 120)))
    support = set()
    for z in rels:
        support |= {Fraction(a, N) % 1 for a in range(N) if z[a]}
    res["support"] = support
    res["support_ok"] = support <= R0
    res["sum_zero"] = all(sum(z[:N]) == 0 for z in rels)
    res["exact_ok"] = all(verify_exact(p, q, N, z) for z in rels)
    period = 1
    for r in support:
        period = period * r.denominator // gcd(period, r.denominator)
    res["period"] = period if rels else 0
    if rels:
        G, A = lambda_matrix(res)
        res["value_dim"] = rank_Q(A)
        res["fields"] = value_fields(p, q, N, G, A)
    else:
        res["value_dim"], res["fields"] = 0, []
    res["zero_dim"] = res["rank"] - res["value_dim"]
    if not quiet:
        print("base %d/%d, N = %d: %d logarithms and 2 pi i, %d bits; LLL %.0f s"
              % (p, q, N, N, res["bits"], res["t_lll"]))
        print("  relations found: %d; every integer relation with sum of |coefficients| below %s"
              " lies in their span" % (res["rank"], bits(res["bound"])))
        if rels:
            print("  each relation: exact in Z[zeta]: %s; sum of exponents 0: %s; support inside R0: %s"
                  " (support %d roots, lcm of orders %d; R0 has %d)"
                  % (res["exact_ok"], res["sum_zero"], res["support_ok"], len(support),
                     res["period"], len(R0)))
            print("  rational patterns with value in (algebraic numbers) pi: dimension %d;"
                  " values/pi: dimension %d over Q; zero relations: dimension %d"
                  % (res["rank"], res["value_dim"], res["zero_dim"]))
            print("  quadratic values: %s%s"
                  % (", ".join("pi" if dl == 1 else "pi sqrt(%d)" % dl for dl in res["fields"]) or "none",
                     "" if len(res["fields"]) == res["value_dim"] else
                     "  (and %d dimensions of non-quadratic multiples)"
                     % (res["value_dim"] - len(res["fields"]))))
            if show:
                print("  a basis (L(a/n) = Log(1 - exp(2 pi i a/n) sqrt(%d/%d))):" % (q, p))
                for z in rels:
                    print("     " + format_relation(z, N))
    return res


def fields_text(res):
    if not res["rank"]:
        return "-"
    txt = ", ".join("pi" if dl == 1 else "pi sqrt%d" % dl for dl in res["fields"]) or "none"
    extra = res["value_dim"] - len(res["fields"])
    return txt + (" + %d non-quadratic" % extra if extra else "")


def run_one(job):
    """One lattice run for the tables: job = (p, q, N). Returns a small picklable summary."""
    p, q, N = job
    R0 = closure_R0(p, q, exceptional_classes(p, q, max(N, 120)))
    res = analyse(p, q, N, R0=R0)
    return {"p": p, "q": q, "N": N, "rank": res["rank"], "bound": res["bound"],
            "ok": res["support_ok"] and res["exact_ok"] and res["sum_zero"],
            "value_dim": res["value_dim"], "zero_dim": res["zero_dim"], "fields": fields_text(res),
            "period": res["period"], "pi": 1 in res["fields"], "t": res["t_lll"]}


def table_orders(p, q):
    """The periods N used for base p/q in the table."""
    s, d, f = base_data(p, q)
    Ns = {24, 48, 60, 72, 84, 96, 120}
    if d > 1 and 120 % f:
        base = f * 4 // gcd(f, 4)
        if base <= 168:
            Ns.add(base)
    return sorted(Ns)


def cmd_table(pmax, procs, jobs=None, nmax=240):
    from multiprocessing import Pool
    pairs = coprime_pairs(pmax) if jobs is None else sorted({(p, q) for p, q, N in jobs})
    if jobs is None:
        jobs = [(p, q, N) for p, q in pairs for N in table_orders(p, q)]
    jobs.sort(key=lambda j: -j[2])
    t0 = time.time()
    results = {}
    with Pool(procs) as pool:
        for r in pool.imap_unordered(run_one, jobs):
            results[(r["p"], r["q"], r["N"])] = r
            sys.stderr.write("  %d/%d N=%d rank=%d LLL %.0fs (elapsed %.0fs)\n"
                             % (r["p"], r["q"], r["N"], r["rank"], r["t"], time.time() - t0))
    print("| p/q | d | f | exceptional classes, order <= %d (order, class: norm) | N tested | rank |"
          " values | zero rel. | period | bound |" % nmax)
    print("|---|---|---|---|---|---|---|---|---|---|")
    withrel, bad, minbound = [], [], None
    for p, q in pairs:
        s, d, f = base_data(p, q)
        exc = exceptional_classes(p, q, nmax)
        rs = [results[j] for j in sorted(results) if j[:2] == (p, q)]
        ranks = [r["rank"] for r in rs]
        top = max(rs, key=lambda r: (r["rank"], r["N"]))
        bnd = min(r["bound"] for r in rs if r["bound"] is not None)
        minbound = bnd if minbound is None else min(minbound, bnd)
        if not all(r["ok"] for r in rs):
            bad.append((p, q))
        if max(ranks):
            withrel.append((p, q))
        rank_txt = str(ranks[0]) if len(set(ranks)) == 1 else "/".join(map(str, ranks))
        print("| %d/%d | %d | %d | %s | %s | %s | %s | %s | %s | %s |"
              % (p, q, d, f, describe_exc(exc), ", ".join(str(r["N"]) for r in rs), rank_txt,
                 top["fields"], top["zero_dim"] if top["rank"] else "-",
                 top["period"] if top["rank"] else "-", bits(bnd)))
    print()
    print("bases with a relation: %s" % (", ".join("%d/%d" % x for x in withrel) or "none"))
    print("smallest certificate bound: %s; cross-checks (support in R0, exact identity,"
          " sum of exponents 0) failed for: %s" % (bits(minbound), bad or "none"))
    print("%d runs, %.0f s" % (len(jobs), time.time() - t0))


# ---------------------------------------------------------------------------------------
# 3. The size condition
# ---------------------------------------------------------------------------------------

def euler_fn(rho):
    """A lower bound for prod over d >= 1 of (1 - rho^d), 0 < rho < 1 (float, rounded down)."""
    prod, d = 1.0, 1
    while rho ** d > 1e-18:
        prod *= 1 - rho ** d
        d += 1
    return prod * (1 - 1e-9)


def phi_bound(p, q):
    """A number F such that SC(p, q, m) holds for every m >= 3 with phi(m) > F; None if there is
    none (p <= sqrt p + sqrt q). Two lower bounds for Phi_m(p, q):
      (M) Phi_m(p, q) >= (p^2 - pq + q^2)^(phi(m)/2)        (superadditivity of geometric means)
      (E) Phi_m(p, q) >= p^phi(m) * prod_{d >= 1} (1 - (q/p)^d)
    and q0 <= phi(m) + 1. Returns the smaller of the two thresholds."""
    A = fsqrt(p) + fsqrt(q)
    best = None
    for c, E in ((fsqrt(p * p - p * q + q * q) / A, 0.0), (p / A, -flog(euler_fn(q / p)))):
        if c <= 1.0000001:
            continue
        # x log c - log(x + 1) - E is convex and <= 0 at x = 0: its non-positive set is an
        # interval [0, x*]; F = the largest integer in it (at least 1)
        F = 1
        while (F + 1) * flog(c) <= flog(F + 2) + E + 1e-9:
            F += 1
        best = F if best is None else min(best, F)
    return best


def sc_holds(p, q, m, crude=False):
    """SC(p, q, m), decided with 60 guard digits. crude: g = q0 always."""
    from sympy import totient, primefactors
    ph = int(totient(m))
    Phi = cyclo_hom(m, p, q)
    q0 = max(primefactors(m))
    g = q0 if (crude or Phi % q0 == 0) else 1
    old = mp.dps
    mp.dps = int(ph * flog(fsqrt(p) + fsqrt(q), 10)) + 80
    rhs = g * (sqrt(mpf(p)) + sqrt(mpf(q))) ** ph
    diff = (mpf(Phi) - rhs) / rhs
    mp.dps = old
    assert abs(diff) > mpf(10) ** (-40), (p, q, m)
    return diff > 0


def sc_failures(p, q, crude=False):
    """All m >= 3 where SC(p, q, m) fails, or None when it fails for infinitely many m."""
    from sympy import totient
    F = phi_bound(p, q)
    if F is None:
        return None
    if F < 2:
        return []
    mmax = max(6, 2 * F * F)                 # phi(m) >= sqrt(m/2)
    return [m for m in range(3, mmax + 1) if totient(m) <= F and not sc_holds(p, q, m, crude)]


def u_log(p, q, m):
    """log U_m(p, q), U_m = prod over the primitive m-th roots s of (p + q + sqrt(2pq(1 + Re s)))^(1/2).

    U_m^k bounds the cofactor: for each primitive n-th root r' at most one of sqrt(p) -+ r' sqrt(q)
    is left to the cofactor, and max |sqrt(p) -+ r' sqrt(q)|^2 = p + q + 2 sqrt(pq) |Re r'|,
    |Re r'|^2 = (1 + Re r'^2)/2. So SC2(p, q, m): Phi_m(p, q) > g U_m(p, q) gives a good prime
    as SC does, and SC implies SC2 because U_m <= (sqrt p + sqrt q)^phi(m)."""
    tot = mpf(0)
    for j in range(1, m + 1):
        if gcd(j, m) == 1:
            tot += log(p + q + sqrt(2 * p * q * (1 + mp.cospi(mpf(2 * j) / m)))) / 2
    return tot


def sc2_holds(p, q, m):
    """SC2(p, q, m): Phi_m(p, q) > g U_m(p, q), decided with 25 guard digits. A difference
    below 10^-15 counts as a failure (equality occurs: Phi_6(3, 1) = U_6(3, 1) = 7)."""
    from sympy import primefactors
    Phi = cyclo_hom(m, p, q)
    q0 = max(primefactors(m))
    g = q0 if Phi % q0 == 0 else 1
    old = mp.dps
    mp.dps = 40
    diff = log(mpf(Phi)) - log(g) - u_log(p, q, m)
    mp.dps = old
    return diff > mpf(10) ** (-15)


def phi_bound2(p, q):
    """A number F such that SC2(p, q, m) holds for every m >= 3 with phi(m) >= F; None if there
    is none (only for 2/1). Uses U_m <= W^(phi/2), W = p + q + sqrt(2pq(1 + 1/phi)) (the arithmetic
    mean bounds the geometric mean, and the primitive m-th roots have sum mu(m)), g <= phi + 1,
    and the lower bounds (M), (E) of phi_bound for Phi_m(p, q). With a(x) = log(c) - log(W(x))/2
    increasing in x, the function y a(x) - log(y + 1) - E of y >= x is convex, so it stays
    positive once it is positive at y = x with slope a(x) - 1/(x + 1) >= 0."""
    best = None
    for logc, E in ((flog(p * p - p * q + q * q) / 2, 0.0), (flog(p), -flog(euler_fn(q / p)))):
        if logc <= flog(p + q + fsqrt(2 * p * q)) / 2 + 1e-9:
            continue
        F = 2
        while True:
            a = logc - flog(p + q + fsqrt(2 * p * q * (1 + 1.0 / F))) / 2
            if F * a > flog(F + 1) + E + 1e-9 and a > 1.0 / (F + 1) + 1e-12:
                break
            F += 1
        best = F if best is None else min(best, F)
    return best


def sc2_failures(p, q):
    """All m >= 3 where SC2(p, q, m) fails, or None when it fails for infinitely many m."""
    from sympy import totient
    F = phi_bound2(p, q)
    if F is None:
        return None
    mmax = max(6, 2 * F * F)                 # phi(m) >= sqrt(m/2)
    return [m for m in range(3, mmax + 1) if totient(m) < F and not sc2_holds(p, q, m)]


def cofactor_test(p, q, m, max_pairs=12):
    """The exact cofactor test at (p, q, m): no Galois theory, a finite check.

    With n = m (m odd) or 2m, the cofactor of the proof is C' = prod of |+-sqrt(p) - r' sqrt(q)|
    over a set that contains at most one of the two signs for each primitive n-th root r' and is
    closed under complex conjugation; |sqrt(p) -+ r' sqrt(q)|^2 = p + q -+ 2 sqrt(pq) Re r'. If
    the root r has no good prime then C' = Phi_m(p, q)^k / C with C^2 = q0^j, 0 <= j <= 2k
    (j = 0 if q0 does not divide Phi_m). Returns (number of selections whose product is such a
    value, smallest |log difference| among the others), or None if there are too many
    selections. 0 matches: every root r with ord(r^2) = m has a good prime."""
    from sympy import primefactors, totient
    n = m if m % 2 else 2 * m
    reps = [a for a in range(1, n // 2 + 1) if gcd(a, n) == 1]          # r' and its conjugate
    if len(reps) > max_pairs:
        return None
    k = int(totient(n)) // int(totient(m))
    Phi = cyclo_hom(m, p, q)
    q0 = max(primefactors(m))
    old = mp.dps
    mp.dps = 40
    A, B = mpf(p + q), 2 * sqrt(mpf(p * q))
    opts = []
    for a in reps:
        c = mp.cospi(mpf(2 * a) / n)
        opts.append((mpf(0), 2 * log(A - B * c), 2 * log(A + B * c)))   # log of the factor of C'^2
    targets = [2 * k * log(mpf(Phi)) - j * log(q0) for j in range(2 * k + 1 if Phi % q0 == 0 else 1)]
    sums = [mpf(0)]
    for o in opts:
        sums = [s + x for s in sums for x in o]
    matches, gap = 0, None
    for s in sums:
        dmin = min(abs(s - t) for t in targets)
        if dmin < mpf(10) ** (-25):
            matches += 1
        elif gap is None or dmin < gap:
            gap = dmin
    mp.dps = old
    return matches, float(gap)


def direct_look(p, q, m):
    """The classes of the roots r with ord(r^2) = m: [(n, label, norm, has a good prime)]."""
    s, d, f = base_data(p, q)
    orders = [2 * m] if m % 2 == 0 else [m, 2 * m]
    out, seen = [], set()
    for n in orders:
        for label, N, exps in classes(p, q, n):
            key = (N, label) if d > 1 else (n, label)
            if d > 1 and label == "all" and key in seen:
                continue                      # one class: orders m and 2m have the same norm
            seen.add(key)
            out.append((n, label, N, strip(N, 2 * p * q * n) > 1))
    return out


def cmd_size(pmax):
    from sympy import totient
    print("Size condition SC(p, q, m): Phi_m(p, q) > g (sqrt p + sqrt q)^phi(m), m >= 3.")
    print("Proved for every m when p >= 16 (summary, section 3). Below: every coprime p > q, p <= %d."
          % pmax)
    inf, total, genuine = [], 0, []
    allm = 0
    for p, q in coprime_pairs(pmax):
        fails = sc_failures(p, q)
        if fails is None:
            inf.append((p, q))
            few = [m for m in range(3, 61) if not sc_holds(p, q, m)]
            print("%d/%d: p <= sqrt p + sqrt q: fails for all large m; holds only for m in %s (m <= 60)"
                  % (p, q, [m for m in range(3, 61) if m not in few]))
            continue
        F = phi_bound(p, q)
        allm += 1 if not fails else 0
        if not fails:
            continue
        crude = sc_failures(p, q, crude=True)
        total += len(fails)
        print("%d/%d: holds for phi(m) > %d; fails at m = %s%s"
              % (p, q, F, fails,
                 "" if crude == fails else "; with g = q0 always, also at %s"
                 % [m for m in crude if m not in fails]))
        for m in fails:
            for n, label, N, good in direct_look(p, q, m):
                if not good:
                    genuine.append((p, q, m, n, label, N))
                print("      m = %d, order %d%s: norm %s%s"
                      % (m, n, "" if label == "all" else label, show_int(N),
                         "" if good else "   NO GOOD PRIME"))
    print()
    print("pairs with p <= %d where SC holds for every m >= 3: %d of %d"
          % (pmax, allm, len(coprime_pairs(pmax))))
    print("pairs where it fails for infinitely many m: %s" % ", ".join("%d/%d" % x for x in inf))
    print("other failures: %d triples; of these, classes with no good prime:" % total)
    for p, q, m, n, label, N in genuine:
        print("   %d/%d, m = %d: order %d%s, norm %s" % (p, q, m, n, "" if label == "all" else label,
                                                        show_int(N)))
    # the bound used in the proof for p >= 16
    worst = min(fsqrt(p * p - p * q + q * q) / (fsqrt(p) + fsqrt(q))
                for p in range(16, 400) for q in range(1, p))
    print("check of the proof for p >= 16: min of sqrt(p^2-pq+q^2)/(sqrt p + sqrt q) over"
          " 16 <= p < 400 is %.4f > sqrt 3 = %.4f" % (worst, fsqrt(3)))
    print()
    print("Sharper condition SC2(p, q, m): Phi_m(p, q) > g U_m(p, q) (see u_log). SC implies SC2.")
    genuine2, n2 = [], 0
    for p, q in coprime_pairs(pmax):
        fails = sc2_failures(p, q)
        if fails is None:
            print("%d/%d: p^2 <= p + q + sqrt(2pq): fails for all large m" % (p, q))
            continue
        if not fails:
            continue
        n2 += len(fails)
        print("%d/%d: holds for phi(m) >= %d; fails at m = %s" % (p, q, phi_bound2(p, q), fails))
        tests = [(m, cofactor_test(p, q, m)) for m in fails]
        print("      exact cofactor test (m: matching selections, smallest other gap): %s"
              % ", ".join("%d: %s" % (m, "not run" if t is None else "%d, %.2g" % t) for m, t in tests))
        for m in fails:
            for n, label, N, good in direct_look(p, q, m):
                if not good:
                    genuine2.append("%d/%d m=%d (order %d%s)" % (p, q, m, n, "" if label == "all" else label))
                if sc_failures(p, q) is None:
                    print("      m = %d, order %d%s: norm %s%s"
                          % (m, n, "" if label == "all" else label, show_int(N),
                             "" if good else "   NO GOOD PRIME"))
    print("SC2 fails at %d triples in all (2/1 apart); classes with no good prime among them: %s"
          % (n2, ", ".join(genuine2)))


# ---------------------------------------------------------------------------------------
# 4. The two-class case: norms and the character-sum bound
# ---------------------------------------------------------------------------------------

def gauss_sum(f, n, j):
    """G(j) = sum over a mod n, prime to n, of chi(a) cos(2 pi a j / n), chi of conductor f | n."""
    from math import cos, pi as fpi
    return sum(kron(f, a) * cos(2 * fpi * a * j / n) for a in range(1, n + 1) if gcd(a, n) == 1)


def cmd_aurif(p, q, jmax):
    """For the two-class orders n of base p/q: the two norms, their good primes, and the bound
    |log(N-/N+)| <= 2 sqrt(f) t/(t^2 - 1) (from |G(j)| <= sqrt(f) gcd(j, n/f))."""
    from sympy import totient
    s, d, f = base_data(p, q)
    assert d > 1
    t = fsqrt(p / q)
    bound = 2 * fsqrt(f) * t / (t * t - 1)
    print("base %d/%d: d = %d, f = %d; bound for |log(N-/N+)|: %.3f" % (p, q, d, f, bound))
    n0 = f if f % 2 else f                    # two-class orders: f * j (and 2 f j for odd f), j odd
    worst = 0.0
    for j in range(1, jmax + 1, 2):
        for n in ([f * j, 2 * f * j] if f % 2 else [f * j]):
            if not is_split(p, q, n):
                continue
            cl = classes(p, q, n)
            Np, Nm = cl[0][1], cl[1][1]
            ratio = abs(flog(Nm) - flog(Np))
            worst = max(worst, ratio)
            good = [strip(N, 2 * p * q * n) > 1 for N in (Np, Nm)]
            print("  n = %d (m = %d, phi(n) = %d): N+ = %s%s; N- = %s%s; |log(N-/N+)| = %.3f"
                  % (n, n // gcd(n, 2), totient(n), show_int(Np), "" if good[0] else " NO GOOD PRIME",
                     show_int(Nm), "" if good[1] else " NO GOOD PRIME", ratio))
            sys.stdout.flush()
    print("largest |log(N-/N+)| seen: %.3f (bound %.3f)" % (worst, bound))
    okg = True
    for n in [f * j for j in (1, 3, 5, 7, 9, 15)]:
        if n > 600:
            continue
        for j in range(1, 80, 2):
            G = gauss_sum(f, n, j)
            if abs(G) > fsqrt(f) * gcd(j, n // f) + 1e-6:
                okg = False
    print("|G(j)| <= sqrt(f) gcd(j, n/f) for n = f, 3f, 5f, 7f, 9f, 15f (n <= 600), odd j < 80: %s" % okg)


# ---------------------------------------------------------------------------------------
# 5. Series, the theory-free probe, the description of a base
# ---------------------------------------------------------------------------------------

def series(p, q, rho, digits=60):
    """S(rho) by direct summation; rho is one period, for k = 1, 2, ..."""
    mp.dps = digits + 15
    P = len(rho)
    total, k, w = mpf(0), 1, mpf(1)
    eps = mpf(10) ** (-(digits + 10))
    ratio = mpf(q) / p
    while True:
        term = w / k
        c = rho[(k - 1) % P]
        if c:
            total += (mpf(c.numerator) / c.denominator if isinstance(c, Fraction) else c) * term
        if term < eps:
            break
        k += 1
        if k % 2 == 0:
            w *= ratio
    return total


def bailey(beta, B, N, a, digits=60):
    """sum_j beta^(-B j) sum_{i=1..N} a_i/(N j + i), beta and the a_i Fractions."""
    mp.dps = digits + 15
    x = (mpf(beta.denominator) / beta.numerator) ** B
    total, j, w = mpf(0), 0, mpf(1)
    eps = mpf(10) ** (-(digits + 10))
    av = [mpf(c.numerator) / c.denominator for c in a]
    while w > eps:
        total += w * sum(av[i - 1] / (N * j + i) for i in range(1, N + 1) if av[i - 1])
        w *= x
        j += 1
    return total


FORMULA_A = [Fraction(*x) for x in [(1, 2), (1, 3), (0, 1), (0, 1), (2, 9), (8, 27), (4, 27), (0, 1), (0, 1),
                                    (16, 243), (16, 243), (0, 1), (-32, 729), (-64, 2187), (0, 1), (0, 1),
                                    (-128, 6561), (-512, 19683), (-256, 19683), (0, 1), (0, 1),
                                    (-1024, 177147), (-1024, 177147), (0, 1)]]
FORMULA_B = [Fraction(*x) for x in [(1, 4), (3, 8), (3, 8), (9, 32), (9, 64), (0, 1), (-27, 256), (-81, 512),
                                    (-81, 512), (-243, 2048), (-243, 4096), (0, 1)]]

# The classes of base 3/2 and base 4/3 (summary, section 2); rho(k) for k = 1, 2, ...
P32 = [1, 1, 0, 0, 1, 2, 1, 0, 0, 1, 1, 0, -1, -1, 0, 0, -1, -2, -1, 0, 0, -1, -1, 0]       # pi/2
Y32 = [1, 0, -2, -3, -1, 0, -1, -3, -2, 0, 1, 0, -1, 0, 2, 3, 1, 0, 1, 3, 2, 0, -1, 0]      # 0
Z32 = [-1, 2, 0, 1, -1, 2, 1, 3, 0, 2, 1, 4, 1, 2, 0, 3, 1, 2, -1, 1, 0, 2, -1, 0]          # 0
G43 = [1, 2, 2, 2, 1, 0, -1, -2, -2, -2, -1, 0]                                           # 4 pi sqrt(3)/9
Z43 = [-3, 2, 0, 6, 3, 8, 3, 6, 0, 2, -3, 0]                                              # 0


def to_pattern(beta, B, N, a):
    """The pattern rho of period N with sum_j beta^(-Bj) sum_i a_i/(Nj+i) = S(rho); needs N = 2B."""
    assert N == 2 * B
    return [a[i - 1] * beta ** (i // 2) for i in range(1, N + 1)]


def cmd_formulas():
    mp.dps = 75
    va = bailey(Fraction(3, 2), 12, 24, FORMULA_A)
    vb = 9 * bailey(Fraction(4, 3), 6, 12, FORMULA_B)
    print("(a) sum_k (2/3)^(12k) sum_j a_j/(24k+j) - pi/4       = %s" % mp.nstr(va - pi / 4, 5))
    print("(b) 9 sum_k (3/4)^(6k) sum_j c_j/(12k+j) - sqrt(3) pi = %s" % mp.nstr(vb - sqrt(mpf(3)) * pi, 5))
    ra = to_pattern(Fraction(3, 2), 12, 24, FORMULA_A)
    rb = to_pattern(Fraction(4, 3), 6, 12, FORMULA_B)
    print("as patterns: (a) is S(rho) with rho = (1/2) %s" % [int(2 * x) for x in ra])
    print("             (b) is 9 S(rho) with rho = (1/4) %s" % [int(4 * x) for x in rb])
    ok = (abs(va - pi / 4) < mpf(10) ** (-58) and abs(vb - sqrt(mpf(3)) * pi) < mpf(10) ** (-58)
          and [2 * x for x in ra] == P32 and [4 * x for x in rb] == G43)
    return ok


def class_sums(p, q, P, W):
    """floor-accurate 2^W * S_j, S_j = sum over k = j (mod P) of (q/p)^floor(k/2)/k, j = 1..P."""
    acc = [0] * P
    one = 1 << (W + 64)
    k, num, den = 1, 1, 1                     # num/den = (q/p)^floor(k/2)
    while den <= num << (W + 72):
        acc[(k - 1) % P] += (one * num) // (den * k)
        k += 1
        if k % 2 == 0:
            num *= q
            den *= p
    return [a >> 64 for a in acc]


def probe_sums(p, q, P, targets=("pi",), quiet=True):
    """Theory-free probe: integer relations among the targets (pi, pi*sqrt2, ...) and the P class
    sums. A relation is a rational pattern of period P with value in the Q-span of the targets."""
    nt = len(targets)
    m = nt + P
    Wc = (40 if m <= 64 else 28) * m + 256
    extra = 300
    W = Wc + extra
    mp.prec = W + 64
    tv = []
    for name in targets:
        v = mpf(1)
        for tok in name.split("*"):
            v *= pi if tok == "pi" else sqrt(mpf(int(tok[4:])))
        tv.append(v)
    S = class_sums(p, q, P, W)
    vals = [(v,) for v in tv] + [(mp.ldexp(mpf(x), -W),) for x in S]
    rels, bound, t_lll = lattice(vals, Wc, extra)
    res = {"rels": rels, "rank": len(rels), "bound": bound, "nt": nt,
           "with_target": [any(r[i] for r in rels) for i in range(nt)]}
    if not quiet:
        print("base %d/%d, period %d: %s and %d class sums, %d bits; LLL %.0f s"
              % (p, q, P, ", ".join(targets), P, Wc, t_lll))
        print("  relations found: %d; no other relation with sum of |coefficients| below %s"
              % (res["rank"], bits(bound)))
        for tname, w in zip(targets, res["with_target"]):
            print("  a relation involves %s: %s" % (tname, "YES" if w else "no"))
        for r in rels[:8]:
            print("    targets %s; rho = %s" % (r[:nt], r[nt:]))
    return res


def in_span(rows, vec):
    den = 1
    for x in vec:
        den = den * Fraction(x).denominator // gcd(den, Fraction(x).denominator)
    v = [int(Fraction(x) * den) for x in vec]
    return rank_Q(rows + [v]) == rank_Q(rows)


def fewest_terms(value_pat, zero_pats):
    """The least number of non-zero entries of value_pat + sum c_i zero_pats[i] (c_i rational),
    and the patterns attaining it. Exhaustive: the minimizers are vertices of the arrangement
    of the hyperplanes (entry k = 0), so it is enough to try every choice of len(zero_pats)
    entries to cancel."""
    from itertools import combinations
    from sympy import Matrix, Rational
    P, kz = len(value_pat), len(zero_pats)
    assert kz in (1, 2)
    points = [tuple([Fraction(0)] * kz)]
    for idx in combinations(range(P), kz):
        A = Matrix([[Rational(z[i]) for z in zero_pats] for i in idx])
        if A.det() == 0:
            continue
        c = A.solve(Matrix([-Rational(value_pat[i]) for i in idx]))
        points.append(tuple(Fraction(int(c[j].p), int(c[j].q)) for j in range(kz)))
    if kz == 2:                               # a generic point on each line (entry i = 0)
        for i in range(P):
            u, v = Fraction(zero_pats[0][i]), Fraction(zero_pats[1][i])
            if u or v:
                lam = -Fraction(value_pat[i]) / (u * u + v * v)
                tau = Fraction(1000003, 7)
                points.append((lam * u - tau * v, lam * v + tau * u))
    best, argbest = P + 1, set()
    for c in set(points):
        pat = tuple(Fraction(value_pat[i]) + sum(c[j] * zero_pats[j][i] for j in range(kz))
                    for i in range(P))
        cnt = sum(1 for x in pat if x)
        if cnt < best:
            best, argbest = cnt, {pat}
        elif cnt == best:
            argbest.add(pat)
    return best, sorted(argbest)


def min_period(pat):
    P = len(pat)
    for dd in range(1, P + 1):
        if P % dd == 0 and all(pat[i] == pat[i % dd] for i in range(P)):
            return dd
    return P


def cmd_describe(p, q):
    """Every formula of base 3/2 or 4/3: the stored patterns, their values, the lattices at
    several periods (both probes), the fewest terms."""
    from sympy import Matrix, Rational
    if (p, q) == (3, 2):
        pats = [("P", P32, lambda: pi / 2, "pi/2"), ("Y", Y32, lambda: 0, "0"), ("Z", Z32, lambda: 0, "0")]
        targets = ("pi", "pi*sqrt2", "pi*sqrt3", "pi*sqrt6")
        periods = (24, 48, 72, 120)
    elif (p, q) == (4, 3):
        pats = [("G", G43, lambda: 4 * sqrt(mpf(3)) * pi / 9, "4 pi sqrt(3)/9"), ("Z", Z43, lambda: 0, "0")]
        targets = ("pi", "pi*sqrt3")
        periods = (12, 24, 36, 60, 120)
    else:
        raise SystemExit("describe: only 3 2 and 4 3")
    ok = True
    print("base %d/%d: the patterns (rho(k), k = 1, 2, ...) and S(rho) - value, 60 digits" % (p, q))
    for name, pat, val, txt in pats:
        err = series(p, q, pat) - val()
        ok = ok and abs(err) < mpf(10) ** (-58)
        print("  %s = %s:  S - %s = %s" % (name, pat, txt, mp.nstr(err, 5)))
    exc = exceptional_classes(p, q, 400)
    R0 = closure_R0(p, q, exc)
    print("exceptional classes, order <= 400: %s" % describe_exc(exc))
    print("R0: %s" % describe_R0(R0))
    for N in periods:
        res = analyse(p, q, N, R0=R0, quiet=False, show=(N == periods[0]))
        ok = ok and res["rank"] == len(pats) * (1 if N % periods[0] == 0 else 0) and res["exact_ok"]
        A = probe_sums(p, q, N, targets)
        stored = [[0] * len(targets) + [pt[i % len(pt)] for i in range(N)] for _, pt, _, _ in pats[1:]]
        name, pt, _, _ = pats[0]
        print("  theory-free probe, period %d, targets %s: rank %d, with target: %s; bound %s"
              % (N, ", ".join(targets), A["rank"], A["with_target"], bits(A["bound"])))
        if N % periods[0] == 0:
            zin = all(in_span(A["rels"], v) for v in stored)
            # the value pattern, with its target coefficient: P -> pi/2, G -> (4/9) pi sqrt 3
            if (p, q) == (3, 2):
                vrow = [-1, 0, 0, 0] + [2 * pt[i % 24] for i in range(N)]
            else:
                vrow = [0, -4] + [9 * pt[i % 12] for i in range(N)]
            vin = in_span(A["rels"], vrow)
            ok = ok and zin and vin and A["rank"] == len(pats)
            print("    the stored patterns lie in the span of the relations found: %s" % (zin and vin))
    best, arg = fewest_terms(pats[0][1], [pt for _, pt, _, _ in pats[1:]])
    print("fewest non-zero entries per period among value pattern + zero relations: %d of %d;"
          " attained by %d pattern(s):" % (best, len(pats[0][1]), len(arg)))
    for pat in arg:
        den = 1
        for x in pat:
            den = den * x.denominator // gcd(den, x.denominator)
        print("    (1/%d) %s   S - value = %s" % (den, [int(x * den) for x in pat],
                                                 mp.nstr(series(p, q, list(pat)) - pats[0][2](), 5)))
    # the periods dd | Pn for which some combination with non-zero value has period dd, and
    # those for which some non-zero combination is supported on the even indices (step 1)
    Pn = len(pats[0][1])
    with_value = []
    for dd in range(1, Pn + 1):
        if Pn % dd:
            continue
        M = Matrix([[Rational(pt[i] - pt[i % dd]) for _, pt, _, _ in pats] for i in range(Pn)])
        if any(v[0] != 0 for v in M.nullspace()):
            with_value.append(dd)
    M = Matrix([[Rational(pt[i]) for _, pt, _, _ in pats] for i in range(0, Pn, 2)])
    print("periods of the patterns with non-zero value: the multiples of %d" % min(with_value))
    print("combinations supported on even k (series of step 1): dimension %d, with non-zero value: %s"
          % (len(M.nullspace()), any(v[0] != 0 for v in M.nullspace())))
    print("all checks: %s" % ("ok" if ok else "FAILED"))
    return ok


# ---------------------------------------------------------------------------------------
# 6. Other steps
# ---------------------------------------------------------------------------------------

def cmd_step(p, q, n, N, quiet=False):
    """2 pi i and the Log(1 - r (q/p)^(1/n)), r^N = 1: the rank is the dimension of the rational
    patterns of period N of the class with step n, sum rho(k) (q/p)^floor(k/n)/k, whose value is
    an algebraic multiple of pi. 'lifted': the relations constant on the cosets of the n1'-th
    roots of unity (n1 = n/2 or n, n1' = n1/gcd(n1, j) for p/q = (a/b)^j): they come from step 2
    or 1 of the base (p/q)^(1/n1')."""
    res = find_relations(p, q, N, n=n)
    rels = res["rels"]
    a, b, j = is_perfect_power_rat(p, q)
    n1 = n // 2 if n % 2 == 0 else n
    n1c = n1 // gcd(n1, j)
    lifted = None
    if N % n1c == 0 and rels:
        stepn = N // n1c
        inv = []
        for e in range(stepn):
            row = [0] * (N + 1)
            for i in range(n1c):
                row[e + i * stepn] = 1
            inv.append(row)
        inv.append([0] * N + [1])
        lifted = len(rels) + len(inv) - rank_Q(rels + inv)
    if not quiet:
        print("base %d/%d, step %d, N = %d: rank %d (lifted from step <= 2: %s; with 2 pi i: %s);"
              " bound %s; LLL %.0f s"
              % (p, q, n, N, res["rank"], "-" if lifted is None else lifted,
                 "yes" if any(z[N] for z in rels) else "no", bits(res["bound"]), res["t_lll"]))
    res["lifted"] = lifted
    return res


def step_one(job):
    p, q, n, N = job
    res = cmd_step(p, q, n, N, quiet=True)
    return (p, q, n, N, res["rank"], res["lifted"], any(z[N] for z in res["rels"]), res["bound"])


# ---------------------------------------------------------------------------------------
# 7. Self-test
# ---------------------------------------------------------------------------------------

def cmd_selftest():
    ok = True

    def check(name, cond):
        nonlocal ok
        ok = ok and bool(cond)
        print("%-74s %s" % (name, "ok" if cond else "FAILED"))

    # 1. arithmetic
    check("Phi_12(3,2) = 61, Phi_6(4,3) = 13, Phi_6(5,1) = 21, Phi_3(4,1) = 21",
          (cyclo_hom(12, 3, 2), cyclo_hom(6, 4, 3), cyclo_hom(6, 5, 1), cyclo_hom(3, 4, 1)) == (61, 13, 21, 21))
    check("classes: 3/2 at order 24 has norms 1, 61^2; 4/3 at order 12 has norms 1, 13^2",
          [c[1] for c in classes(3, 2, 24)] == [1, 3721] and [c[1] for c in classes(4, 3, 12)] == [1, 169])
    check("classes: base 5 at orders 5, 15 (11, 71; 181, 1741), as in baseb_explore",
          [c[1] for c in classes(5, 1, 5)] == [11, 71] and sorted(c[1] for c in classes(5, 1, 15)) == [181, 1741])
    for (p, q) in ((2, 1), (3, 1), (4, 1), (3, 2), (4, 3), (5, 1), (5, 2), (7, 3), (9, 4), (9, 2)):
        got = [(n, lab) for n, lab, _, _ in exceptional_classes(p, q, 200)]
        check("exceptional classes of %d/%d, order <= 200: %s" % (p, q, got or "none"),
              got == predicted_exceptional(p, q))
    check("R0: 24 roots for base 2, 6 for base 3, 6 for base 3/2, 4 for base 4/3, 4 for base 4",
          [len(closure_R0(p, q, exceptional_classes(p, q, 200)))
           for p, q in ((2, 1), (3, 1), (3, 2), (4, 3), (4, 1))] == [24, 6, 6, 4, 4])
    # 2. the formulas (a), (b) by direct summation, and the stored patterns
    check("formulas (a) and (b) of P03 to 58 digits; their patterns are P32/2 and G43/4", cmd_formulas())
    mp.dps = 75
    check("S(P32) = pi/2, S(Y32) = S(Z32) = 0 (base 3/2); S(G43) = 4 pi sqrt(3)/9, S(Z43) = 0 (base 4/3)",
          abs(series(3, 2, P32) - pi / 2) < mpf(10) ** (-58) and abs(series(3, 2, Y32)) < mpf(10) ** (-58)
          and abs(series(3, 2, Z32)) < mpf(10) ** (-58) and abs(series(4, 3, Z43)) < mpf(10) ** (-58)
          and abs(series(4, 3, G43) - 4 * sqrt(mpf(3)) * pi / 9) < mpf(10) ** (-58))
    # 3. the lattices: the five bases with relations, and base 5
    expect = [((2, 1), 24, 8, [1, 2, 3]), ((2, 1), 120, 13, [1, 2, 3, 5]), ((3, 1), 12, 3, [3]),
              ((3, 1), 24, 3, [3]), ((4, 1), 12, 2, [3]), ((3, 2), 24, 3, [1]), ((3, 2), 48, 3, [1]),
              ((4, 3), 12, 2, [3]), ((4, 3), 24, 2, [3]), ((5, 1), 24, 0, []), ((5, 1), 60, 0, []),
              ((5, 1), 120, 0, []), ((5, 2), 40, 0, []), ((9, 4), 24, 0, [])]
    for (p, q), N, rank, fields in expect:
        res = analyse(p, q, N)
        good = (res["rank"] == rank and res["support_ok"] and res["exact_ok"] and res["sum_zero"]
                and (fields is None or res["fields"] == fields))
        check("base %d/%d, N = %d: rank %d, values %s, zero rel. %d, bound %s"
              % (p, q, N, res["rank"], fields_text(res), res["zero_dim"], bits(res["bound"])), good)
        if (p, q, N) == (2, 1, 120):
            check("   base 2: values/pi of dimension 6 = 1 + 5, zero relations 7 (Theorem C: 13 = 8 + 5)",
                  res["value_dim"] == 6 and res["zero_dim"] == 7)
    # 4. the theory-free probe finds (a) and (b)
    A = probe_sums(3, 2, 24, ("pi",))
    ra = [0] * 0 + [-1] + [4 * x for x in to_pattern(Fraction(3, 2), 12, 24, FORMULA_A)]     # 4 S = pi
    check("probe on class sums, base 3/2, period 24: rank 3, pi occurs, formula (a) in the span",
          A["rank"] == 3 and A["with_target"][0] and in_span(A["rels"], ra))
    A = probe_sums(4, 3, 12, ("pi", "pi*sqrt3"))
    rb = [0, -1] + [9 * x for x in to_pattern(Fraction(4, 3), 6, 12, FORMULA_B)]
    check("probe on class sums, base 4/3, period 12: rank 2, pi sqrt3 occurs, pi does not, (b) in the span",
          A["rank"] == 2 and A["with_target"] == [False, True] and in_span(A["rels"], rb))
    A = probe_sums(3, 1, 12, ("pi", "pi*sqrt3"))
    check("probe on class sums, base 3, period 12: rank 3 (G, Z1, Z2 of Theorem C3), pi sqrt3 only",
          A["rank"] == 3 and A["with_target"] == [False, True]
          and in_span(A["rels"], [0, -1, 6, 0, -6, 0, 6, 0, -6, 0, 6, 0, -6, 0])
          and in_span(A["rels"], [0, 0, 0, 1, -2, 0, 1, 4, 0, 3, 2, 4, -1, 0]))
    A = probe_sums(5, 1, 24, ("pi", "pi*sqrt5"))
    check("probe on class sums, base 5, period 24: nothing", A["rank"] == 0)
    # 5. the size condition
    check("size condition: for q = 1, 5 <= p <= 16 it fails only at (5, 1, 6)",
          [(p, m) for p in range(5, 17) for m in sc_failures(p, 1)] == [(5, 6)])
    check("size condition: infinitely many failures exactly for 2/1 and 3/2 (p <= 16)",
          [pq for pq in coprime_pairs(16) if phi_bound(*pq) is None] == [(2, 1), (3, 2)])
    print("selftest: %s" % ("all ok" if ok else "FAILED"))
    return ok


if __name__ == "__main__":
    args = sys.argv[1:]
    cmd = args[0] if args else ""
    if cmd == "selftest":
        sys.exit(0 if cmd_selftest() else 1)
    elif cmd == "relations":
        p, q, N = (int(x) for x in args[1:4])
        analyse(p, q, N, nmax=max(N, 240), quiet=False, show=True)
    elif cmd == "table":
        ints = [int(x) for x in args[1:]]
        pmax, procs = (ints + [16, 8][len(ints):])[:2]
        cmd_table(pmax, procs)
    elif cmd == "extra":
        procs = int(args[1])
        cmd_table(0, procs, jobs=[tuple(int(x) for x in a.split(":")) for a in args[2:]])
    elif cmd == "scan":
        ints = [int(x) for x in args[1:]]
        pmax, nmax = (ints + [16, 240][len(ints):])[:2]
        cmd_scan(pmax, nmax)
    elif cmd == "size":
        cmd_size(int(args[1]) if len(args) > 1 else 16)
    elif cmd == "aurif":
        cmd_aurif(int(args[1]), int(args[2]), int(args[3]) if len(args) > 3 else 9)
    elif cmd == "describe":
        cmd_describe(int(args[1]), int(args[2]))
    elif cmd == "formulas":
        cmd_formulas()
    elif cmd == "sums":
        p, q, P = (int(x) for x in args[1:4])
        probe_sums(p, q, P, tuple(args[4:]) or ("pi",), quiet=False)
    elif cmd == "step":
        p, q, n, N = (int(x) for x in args[1:5])
        cmd_step(p, q, n, N)
    elif cmd == "steps":
        from multiprocessing import Pool
        procs = int(args[1])
        jobs = [tuple(int(x) for x in a.split(":")) for a in args[2:]]
        with Pool(procs) as pool:
            for r in pool.imap(step_one, jobs):
                print("base %d/%d, step %d, N = %d: rank %d, lifted %s, with 2 pi i: %s, bound %s"
                      % (r[0], r[1], r[2], r[3], r[4], "-" if r[5] is None else r[5],
                         "yes" if r[6] else "no", bits(r[7])))
                sys.stdout.flush()
    else:
        print(__doc__)
