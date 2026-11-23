"""Base b: exploration of the series  S(rho) = sum_{k>=1} rho(k) b^(-floor(k/2)) / k  for every b.

    python baseb_explore.py scan  [BMIN BMAX NMAX]   exceptional roots of unity, per base
    python baseb_explore.py check [BMAX NMAX]        the same, compared with the prediction
    python baseb_explore.py relations B N            the lattice of relations among 2 pi i and
                                                     the Log(1 - r/sqrt(B)), r^N = 1
    python baseb_explore.py table [BMIN BMAX NMAX]   scan + relations, one line per base
    python baseb_explore.py powers B N               bases B^2, ..., B^6 inside base B
    python baseb_explore.py deep BMIN BMAX N BITS    the relation search with more bits per number
    python baseb_explore.py bound [BMAX NMAX]        the crude size inequality: where it fails
    python baseb_explore.py base4                    the two formulas of base 4, checked
    python baseb_explore.py probe B P                theory-free search (base3_probe.py) in base B
    python baseb_explore.py selftest                 checks of the program itself

`scan`, `check`, `bound` and `selftest` need mpmath and sympy; the others also need
python-flint. Findings: research/2026-11-22-base5/06_other_bases_computations.md.
Nothing here is a proof. The setting is that of Parts III, V and VI of
notes/pi_formula_theorem.md, with t = sqrt(b) (an integer when b is a square):

    S(rho) = - sum over roots of unity r of d_r Log(1 - r/t).

Vocabulary used below.

  class       Roots of unity of the same order n whose numbers t - r are conjugate over Q.
              Write b = s^2 d with d squarefree and let f be the conductor of Q(sqrt(d)):
              f = 1 for d = 1, f = d for d = 1 mod 4, f = 4d otherwise. There are two classes
              ("+" and "-", by the Kronecker character chi of Q(sqrt(d)) at the exponent) when
              f divides n and not both 4 | n and f | n/2; this is the Aurifeuillian case.
              Otherwise there is one class ("all").
  norm        The absolute norm of t - r, an integer that depends on the class only. For one
              class it is Phi_n(sqrt(b)) (b a square) or a power of Phi_m(b), m the order of
              r^2. For two classes N+ N- = Phi_m(b)^e, e = 2 if 4 | n and 1 otherwise.
  good prime  A prime p dividing the norm and not dividing 2 b n. (Primes dividing b never
              divide the norm.) A prime ideal above p then contains t - r, and contains no
              t - r' for another root r' in a relation, unless r'/r has order a power of p.
  exceptional A class with no good prime.
  R0          The exceptional roots, closed under: if r' is in R0, p is an odd prime dividing
              both the order of r' and the norm of t - r', then the p'-part of r' is in R0.
              Every integer relation among the Log(1 - r/t) is supported on R0 (the argument
              of Part III, Step 2).
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


def kron(D, c):
    """Kronecker symbol (D / c) for a positive fundamental discriminant D and c >= 1."""
    from sympy import jacobi_symbol
    if gcd(D, c) > 1:
        return 0
    res = 1
    while c % 2 == 0:
        c //= 2
        res *= 1 if D % 8 in (1, 7) else -1
    return res * (int(jacobi_symbol(D % c, c)) if c > 1 else 1)


@lru_cache(maxsize=None)
def base_data(b):
    """(s, d, f): b = s^2 d, f the conductor of Q(sqrt(d)) (f = 1 when b is a square)."""
    s, d = sqfree_split(b)
    return s, d, conductor(d)


def is_split(b, n):
    """True when the roots of order n fall into two classes (the Aurifeuillian case)."""
    s, d, f = base_data(b)
    if d == 1 or n % f:
        return False
    return not (n % 4 == 0 and (n // 2) % f == 0)


def cyclo(m, x):
    """Phi_m(x) for an integer x >= 2, exactly."""
    from sympy import divisors, mobius
    num, den = 1, 1
    for dd in divisors(m):
        mu = mobius(m // dd)
        if mu == 1:
            num *= x ** dd - 1
        elif mu == -1:
            den *= x ** dd - 1
    assert num % den == 0
    return num // den


def strip(N, m):
    """Remove from N every prime factor of m; return the cofactor."""
    from sympy import primefactors
    for p in primefactors(m):
        while N % p == 0:
            N //= p
    return N


def show_int(N):
    from sympy import factorint
    if N == 1:
        return "1"
    if N > 10 ** 30:
        return "%d digits" % len(str(N))
    return "*".join("%d^%d" % (p, e) if e > 1 else str(p) for p, e in sorted(factorint(N).items()))


# ---------------------------------------------------------------------------------------
# 1. Classes, norms, exceptional roots, the set R0
# ---------------------------------------------------------------------------------------

@lru_cache(maxsize=None)
def classes(b, n):
    """The classes of roots of order n: a tuple of (label, norm, exponents).

    exponents is the tuple of a (1 <= a <= n, prime to n) with zeta_n^a in the class."""
    s, d, f = base_data(b)
    units = tuple(a for a in range(1, n + 1) if gcd(a, n) == 1)
    if d == 1:
        return (("all", abs(cyclo(n, isqrt(b))), units),)
    m = n // gcd(n, 2)                       # the order of r^2
    if not is_split(b, n):
        return (("all", abs(cyclo(m, b)), units),)
    D = f
    chi = {a: kron(D, a) for a in units}
    t_float = fsqrt(b)
    mp.dps = int(len(units) * flog(t_float + 1, 10)) + 60
    t = sqrt(mpf(b))
    zeta = {a: mp.expjpi(mpf(2 * a) / n) for a in units}
    out = []
    for eps in (1, -1):
        prod = mpc(1)
        for a in units:
            prod *= eps * chi[a] * t - zeta[a]
        val = int(mp.nint(prod.real))
        assert abs(prod.imag) < mpf(10) ** (-25) and abs(prod.real - val) < mpf(10) ** (-25), (b, n)
        out.append(("+" if eps == 1 else "-", abs(val),
                    tuple(a for a in units if chi[a] == eps)))
    e = 2 if n % 4 == 0 else 1
    assert out[0][1] * out[1][1] == abs(cyclo(m, b)) ** e, (b, n)      # N+ N- = Phi_m(b)^e
    return tuple(out)


def class_of(b, r):
    """(label, norm) of the class of the root r = exp(2 pi i r), r a Fraction."""
    n, a = r.denominator, r.numerator % r.denominator
    if n == 1:
        a = 1
    for label, N, exps in classes(b, n):
        if a in exps:
            return label, N
    raise ValueError((b, r))


def exceptional_classes(b, nmax):
    """[(n, label, norm, exponents)] for the classes of order <= nmax with no good prime."""
    out = []
    for n in range(1, nmax + 1):
        for label, N, exps in classes(b, n):
            if strip(N, 2 * b * n) == 1:
                out.append((n, label, N, exps))
    return out


def p_prime_part(r, p):
    """The p'-part of the root of unity exp(2 pi i r)."""
    n = r.denominator
    q = 1
    while (n // q) % p == 0:
        q *= p
    n1 = n // q
    # u = 1 mod n1, u = 0 mod q
    u = (q * pow(q, -1, n1)) % n if n1 > 1 else 0
    return Fraction(r.numerator * u, n) % 1


def closure_R0(b, exc):
    """The set R0 as a set of Fractions (r = a/n stands for exp(2 pi i a/n))."""
    from sympy import primefactors
    R0 = set()
    queue = []
    for n, label, N, exps in exc:
        for a in exps:
            r = Fraction(a, n) % 1
            R0.add(r)
            queue.append(r)
    while queue:
        r = queue.pop()
        n = r.denominator
        label, N = class_of(b, r)
        for p in primefactors(n):
            if p % 2 and N % p == 0:
                r1 = p_prime_part(r, p)
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


def cmd_scan(bmin, bmax, nmax, verbose=True):
    res = {}
    for b in range(bmin, bmax + 1):
        s, d, f = base_data(b)
        exc = exceptional_classes(b, nmax)
        R0 = closure_R0(b, exc)
        res[b] = (exc, R0)
        if verbose:
            kind = ("t = %d" % isqrt(b)) if d == 1 else ("d = %d, s = %d, f = %d" % (d, s, f))
            print("b = %d (%s)" % (b, kind))
            print("   exceptional classes, order <= %d (order, class: norm): %s"
                  % (nmax, describe_exc(exc)))
            unit = [(n, label) for n, label, N, _ in exc if N == 1]
            if unit:
                print("   of these, t - r is a unit for: %s"
                      % ", ".join("%d%s" % (n, "" if lab == "all" else lab) for n, lab in unit))
            print("   R0 (%d roots): %s" % (len(R0), describe_R0(R0)))
    return res


def predicted_exceptional(b):
    """The exceptional classes that the proof sketch predicts, as a list of (order, label).

    b = 2, 3, 4 are the three special bases. For b >= 5: b not a square: orders 1 and 2 when
    b - 1 is a power of 2, order 4 when b + 1 is a power of 2. b = c^2: order 1 when c - 1 is a
    power of 2, order 2 when c + 1 is a power of 2."""
    def pow2(x):
        return x >= 1 and x & (x - 1) == 0
    if b == 2:
        return [(1, "all"), (2, "all"), (8, "+"), (12, "all"), (24, "+"), (40, "+")]
    if b == 3:
        return [(1, "all"), (2, "all"), (4, "all"), (12, "+")]
    if b == 4:
        return [(1, "all"), (6, "all")]
    s, d, f = base_data(b)
    out = []
    if d == 1:
        c = isqrt(b)
        if pow2(c - 1):
            out.append((1, "all"))
        if pow2(c + 1):
            out.append((2, "all"))
    else:
        if pow2(b - 1):
            out += [(1, "all"), (2, "all")]
        if pow2(b + 1):
            out.append((4, "all"))
    return out


def cmd_check(bmax, nmax):
    """Compare the exceptional classes found with the prediction, for 2 <= b <= bmax."""
    from sympy import primefactors
    bad, listed = [], []
    smallest = {}
    nsplit = 0
    for b in range(2, bmax + 1):
        exc = [(n, label) for n, label, N, _ in exceptional_classes(b, nmax)]
        pred = [x for x in predicted_exceptional(b) if x[0] <= nmax]
        if exc != pred:
            bad.append((b, exc, pred))
        if exc:
            listed.append((b, exc))
        s, d, f = base_data(b)
        if d > 1:
            best = None
            for n in range(f, nmax + 1, f):
                if is_split(b, n):
                    p = max(primefactors(n))
                    cap = 1 if (p == 2 or b % p == 0) else p ** (2 if n % 4 == 0 else 1)
                    for label, N, exps in classes(b, n):
                        cof = strip(N, 2 * b * n)
                        # the part of the norm made of primes dividing 2bn divides the cap,
                        # and the norm is at least (sqrt(b) - 1)^phi(n)
                        assert cap % (N // cof) == 0, (b, n, label, N)
                        assert flog(N) >= 2 * len(exps) * flog(fsqrt(b) - 1) - 1e-9, (b, n)
                        nsplit += 1
                        if b >= 5 and (best is None or cof < best[0]):
                            best = (cof, n, label)
            if best:
                smallest[b] = best
    print("bases 2..%d, orders up to %d" % (bmax, nmax))
    print("bases with an exceptional class: %s"
          % ", ".join("%d (orders %s)" % (b, ",".join(str(n) + ("" if lab == "all" else lab)
                                                      for n, lab in exc)) for b, exc in listed))
    print("disagreements with the prediction: %s" % (bad or "none"))
    print("two-class case: %d classes looked at; in each, the part of the norm made of primes"
          " dividing 2bn divides the cap p^e" % nsplit)
    if smallest:
        cof, b = min((v[0], b) for b, v in smallest.items())
        print("two-class case, b >= 5: the smallest part of a norm prime to 2bn is %d (b = %d, n = %d%s)"
              % (cof, b, smallest[b][1], smallest[b][2]))
        few = sorted((v[0], b, v[1], v[2]) for b, v in smallest.items())[:6]
        print("   the six smallest, one per base: %s"
              % ", ".join("%d (b=%d, n=%d%s)" % x for x in few))


# ---------------------------------------------------------------------------------------
# 2. The lattice of relations
# ---------------------------------------------------------------------------------------

def log_values(b, N, prec):
    """[(Re, Im)] of Log(1 - zeta_N^a/sqrt(b)), a = 0..N-1, then (0, 2 pi); at precision prec."""
    mp.prec = prec
    t = sqrt(mpf(b))
    vals = []
    for a in range(N):
        w = log(1 - mp.expjpi(mpf(2 * a) / N) / t)
        vals.append((w.real, w.imag))
    vals.append((mpf(0), 2 * pi))
    return vals


def find_relations(b, N, bits_per=30, quiet=False):
    """Lattice reduction. Returns a dict with the relations found and a certificate.

    A row of the reduced basis is accepted as a relation only if the combination vanishes
    to the full working precision, 300 bits beyond what the lattice saw. The certificate:
    with the relations first, the Gram-Schmidt lengths of the other rows are computed; an
    integer relation z outside the span of those found has a lattice vector of length at
    most sqrt(3) * sum|z_i|, and at least the smallest of those Gram-Schmidt lengths."""
    from flint import fmpz_mat
    Wc = bits_per * (N + 1) + 300
    extra = 400
    vals = log_values(b, N, Wc + extra + 64)
    scale = mpf(2) ** Wc
    n = len(vals)
    rows = []
    for i, (re, im) in enumerate(vals):
        row = [0] * (n + 2)
        row[i] = 1
        row[n] = int(floor(re * scale))
        row[n + 1] = int(floor(im * scale))
        rows.append(row)
    t0 = time.time()
    red = fmpz_mat(rows).lll()
    t_lll = time.time() - t0
    rel_rows, other_rows = [], []
    for i in range(n):
        row = [int(red[i, j]) for j in range(n + 2)]
        coef = row[:n]
        re = sum(c * v[0] for c, v in zip(coef, vals))
        im = sum(c * v[1] for c, v in zip(coef, vals))
        tol = (sum(abs(c) for c in coef) + 1) * mpf(2) ** (-(Wc + extra - 100))
        (rel_rows if abs(re) < tol and abs(im) < tol else other_rows).append(row)
    # certificate: Gram-Schmidt with the relations first
    mp.prec = 600
    gs = []
    mu_min = None
    for idx, row in enumerate(rel_rows + other_rows):
        v = [mpf(c) for c in row]
        for g, gg in gs:
            c = sum(x * y for x, y in zip(v, g)) / gg
            v = [x - c * y for x, y in zip(v, g)]
        vv = sum(x * x for x in v)
        gs.append((v, vv))
        if idx >= len(rel_rows) and (mu_min is None or vv < mu_min):
            mu_min = vv
    bound = int(floor(sqrt(mu_min / 3))) if mu_min is not None else 0
    rels = [row[:n] for row in rel_rows]
    out = {"b": b, "N": N, "bits": Wc, "rels": rels, "rank": len(rels), "bound": bound,
           "vals": vals, "t_lll": t_lll}
    if not quiet:
        print("base %d, N = %d: %d logarithms and 2 pi i, %d bits; LLL %.0f s"
              % (b, N, N, Wc, t_lll))
        print("  relations found: %d" % len(rels))
        print("  certificate: every integer relation with sum of |coefficients| below 2^%d"
              % (bound.bit_length() - 1))
        print("               lies in the span of the relations found")
    return out


def rank_Q(rows):
    from flint import fmpz_mat
    if not rows or not rows[0]:
        return 0
    return fmpz_mat(rows).rank()


def galois_group(b, N):
    """The automorphisms of Q(zeta_N, t) as pairs (a, eps): zeta -> zeta^a, t -> eps t."""
    s, d, f = base_data(b)
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


def value_dimension(res):
    """The dimension over Q of the set of algebraic numbers gamma with S(rho) = gamma pi.

    For an automorphism g, sending t - r to eps t - r^a = eps (t - eps r^a), a relation z is
    sent to the relation g.z with (g.z) at eps r^a equal to z at r. The number sought is the
    rank of the matrix lambda(g.z_j), lambda = the coefficient of 2 pi i; the zero relations
    then form a space of dimension rank - (this number). Needs N even."""
    b, N, rels, vals = res["b"], res["N"], res["rels"], res["vals"]
    if not rels:
        return 0
    assert N % 2 == 0
    mp.prec = res["bits"] + 400
    two_pi = 2 * pi
    A = []
    for a, eps in galois_group(b, N):
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
    return rank_Q(A)


def verify_exact(b, N, z):
    """Exact check of prod (1 - r/t)^(z_r) = 1 in Z[zeta_M], M = lcm(N, f, 2).

    With T = 2t, an element of Z[zeta_M] (a Gauss sum), the identity reads
    prod (T - 2r)^(z_r) = T^(sum z_r); negative exponents are moved to the other side."""
    from flint import fmpz_poly
    s, d, f = base_data(b)
    M = N * f // gcd(N, f)
    if M % 2:
        M *= 2
    phi = fmpz_poly.cyclotomic(M)

    def red(p):
        return p % phi

    def mono(k):
        return fmpz_poly([0] * (k % M) + [1])

    if d == 1:
        T = fmpz_poly([2 * isqrt(b)])
    else:
        g = fmpz_poly([0])
        for c in range(1, f):
            ch = kron(f, c)
            if ch:
                g = g + ch * mono(c * (M // f))
        T = red((2 * s if f == d else s) * g)
        assert red(T * T) == fmpz_poly([4 * b]), "Gauss sum"
    lhs = fmpz_poly([1])
    rhs = fmpz_poly([1])
    Z = 0
    for k in range(N):
        e = z[k]
        if not e:
            continue
        Z += e
        fac = red(T - 2 * mono(k * (M // N)))
        for _ in range(abs(e)):
            if e > 0:
                lhs = red(lhs * fac)
            else:
                rhs = red(rhs * fac)
    for _ in range(abs(Z)):
        if Z > 0:
            rhs = red(rhs * T)
        else:
            lhs = red(lhs * T)
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


def analyse(b, N, R0=None, nmax=None, quiet=False, show=True):
    """Relations of base b on the N-th roots of unity, with all the checks."""
    res = find_relations(b, N, quiet=quiet)
    rels = res["rels"]
    if R0 is None:
        R0 = closure_R0(b, exceptional_classes(b, nmax or max(N, 120)))
    support = set()
    for z in rels:
        support |= {Fraction(a, N) % 1 for a in range(N) if z[a]}
    res["support"] = support
    res["support_ok"] = support <= R0
    res["with_pi"] = rank_Q([[z[N]] for z in rels]) if rels else 0
    res["exact_ok"] = all(verify_exact(b, N, z) for z in rels)
    res["value_dim"] = value_dimension(res) if rels and N % 2 == 0 else 0
    res["zero_dim"] = res["rank"] - res["value_dim"]
    if not quiet:
        if rels:
            print("  rank %d; relations that involve 2 pi i: %s (rank %d modulo the others)"
                  % (res["rank"], "yes" if res["with_pi"] else "no", res["with_pi"]))
            print("  each relation checked exactly in Z[zeta]: %s" % res["exact_ok"])
            print("  support inside R0: %s   (support has %d roots, R0 has %d)"
                  % (res["support_ok"], len(support), len(R0)))
            print("  patterns with value in (algebraic numbers) * pi: dimension %d;"
                  " their values/pi span dimension %d over Q; zero relations: dimension %d"
                  % (res["rank"], res["value_dim"], res["zero_dim"]))
            if show:
                print("  a basis (L(a/n) = Log(1 - exp(2 pi i a/n)/sqrt(%d))):" % b)
                for z in rels:
                    print("     " + format_relation(z, N))
    return res


def test_orders(b, R0):
    """The periods N used for base b in the table."""
    s, d, f = base_data(b)
    need = 1
    for r in R0:
        need = need * r.denominator // gcd(need, r.denominator)
    Ns = {24, 60, 120}
    if need > 1 and 120 % need:
        Ns.add(need if need % 2 == 0 else 2 * need)
    if d > 1 and 120 % f:
        base = f * 4 // gcd(f, 4)
        Ns.add(base)
        if 3 * base <= 160 and base % 3:
            Ns.add(3 * base)
    return sorted(Ns)


def cmd_table(bmin, bmax, nmax):
    print("| b | b = s^2 d | f | exceptional classes, order <= %d (order, class: norm) | R0 |"
          " N tested | rank | with 2 pi i | zero relations | no other relation with sum|z| below |"
          % nmax)
    print("|---|---|---|---|---|---|---|---|---|---|")
    summary = []
    for b in range(bmin, bmax + 1):
        s, d, f = base_data(b)
        exc = exceptional_classes(b, nmax)
        R0 = closure_R0(b, exc)
        ranks, bounds, ok = [], [], True
        last = None
        for N in test_orders(b, R0):
            res = analyse(b, N, R0=R0, quiet=True)
            ranks.append(res["rank"])
            bounds.append(res["bound"])
            ok = ok and res["support_ok"] and res["exact_ok"]
            last = res if (last is None or res["rank"] >= last["rank"]) else last
            sys.stderr.write("  b=%d N=%d rank=%d LLL %.0fs\n" % (b, N, res["rank"], res["t_lll"]))
        Ns = test_orders(b, R0)
        r0 = ("%d roots, orders %s" % (len(R0), sorted({r.denominator for r in R0}))) if R0 else "empty"
        rank_txt = str(ranks[0]) if len(set(ranks)) == 1 else "/".join(map(str, ranks))
        print("| %d | %s | %d | %s | %s | %s | %s | %s | %s | 2^%d |%s"
              % (b, ("%d^2" % s) if d == 1 else ("%d" % d if s == 1 else "%d^2 * %d" % (s, d)), f,
                 describe_exc(exc), r0, ", ".join(map(str, Ns)), rank_txt,
                 last["with_pi"], last["zero_dim"], min(bounds).bit_length() - 1,
                 "" if ok else "  CHECK FAILED"))
        sys.stdout.flush()
        summary.append((b, ranks, ok))
    bad = [b for b, ranks, ok in summary if not ok]
    withrel = [b for b, ranks, ok in summary if max(ranks) > 0]
    print()
    print("bases with a relation: %s" % (withrel or "none"))
    print("cross-checks (support inside R0, exact identity) failed for: %s" % (bad or "none"))


def cmd_powers(b, N):
    """The class of base b^j lies inside that of base b: 1 - s/t^j is the product of the
    1 - r/t over r^j = s. So the relations of base b^j are the relations of base b that are
    constant on the cosets r * (j-th roots of 1). Compares the two computations."""
    res = analyse(b, N, nmax=max(N, 200), quiet=True)
    rels = [z[:N] for z in res["rels"]]
    print("base %d, N = %d: rank %d" % (b, N, res["rank"]))
    for j in range(2, 7):
        if N % j:
            continue
        step = N // j
        inv = []
        for a in range(step):
            row = [0] * N
            for i in range(j):
                row[a + i * step] = 1
            inv.append(row)
        dim = (len(rels) + len(inv) - rank_Q(rels + inv)) if rels else 0
        direct = find_relations(b ** j, step, quiet=True)
        print("  base %d = %d^%d: relations of base %d invariant under the %d-th roots of 1:"
              " dimension %d; computed directly for base %d on the %d-th roots: rank %d  %s"
              % (b ** j, b, j, b, j, dim, b ** j, step, direct["rank"],
                 "(agree)" if dim == direct["rank"] else "(DISAGREE)"))


# ---------------------------------------------------------------------------------------
# 3. The crude size inequality
# ---------------------------------------------------------------------------------------

def cmd_bound(bmax, nmax):
    """An exceptional class in the Aurifeuillian case has |norm| in {1, p, p^2}, p the largest
    prime factor of n (odd, not dividing b), with p^2 only if 4 | n. And |norm| >=
    (sqrt(b) - 1)^phi(n). So a class is not exceptional when

        (sqrt(b) - 1)^phi(n)  >  cap(b, n),   cap = p^e (e = 2 if 4 | n, else 1), or 1 if
                                              there is no such p.

    Lists the pairs (b, n), n <= nmax, for which this fails, and looks at each directly."""
    from sympy import totient, primefactors
    fails, tight, count = [], [], 0
    for b in range(5, bmax + 1):
        s, d, f = base_data(b)
        if d == 1:
            continue
        lt = flog(fsqrt(b) - 1)
        for n in range(f, nmax + 1, f):
            if not is_split(b, n):
                continue
            count += 1
            p = max(primefactors(n))
            cap = 1 if (p == 2 or b % p == 0) else p ** (2 if n % 4 == 0 else 1)
            if totient(n) * lt <= flog(cap) + 1e-12:
                fails.append((b, n, cap))
            if cap > 1:
                tight.append((totient(n) * lt / flog(cap), b, n, cap))
    print("pairs (b, n) with 5 <= b <= %d, n <= %d and two classes: %d" % (bmax, nmax, count))
    # two cruder caps, for comparison: n^2, and p^e without using that p does not divide b
    crude1, crude2 = [], []
    for b in range(5, bmax + 1):
        s, d, f = base_data(b)
        if d == 1:
            continue
        lt = flog(fsqrt(b) - 1)
        for n in range(f, nmax + 1, f):
            if is_split(b, n):
                ph = totient(n)
                if ph * lt <= 2 * flog(n):
                    crude1.append((b, n))
                p = max(primefactors(n))
                if p > 2 and ph * lt <= (2 if n % 4 == 0 else 1) * flog(p):
                    crude2.append((b, n))
    print("with the cap n^2 the bound fails for %d pairs: %s%s"
          % (len(crude1), ", ".join("(%d,%d)" % x for x in crude1[:40]),
             " ..." if len(crude1) > 40 else ""))
    print("with the cap p^e, p the largest prime factor of n, it fails for %d pairs: %s"
          % (len(crude2), ", ".join("(%d,%d)" % x for x in crude2)))
    print("with the cap as defined (1 when p divides b or p = 2) it fails for: %d" % len(fails))
    tight.sort()
    print("the tightest cases with cap > 1 (ratio of logarithms, b, n, cap):")
    for ratio, b, n, cap in tight[:8]:
        print("  %.2f   b = %d, n = %d, cap = %d, phi(n) = %d" % (ratio, b, n, cap, totient(n)))
    # the inequality used in the proof sketch: (sqrt(b)-1)^(4(p-1)) > p^2 for p >= 5, b >= 5,
    # and (sqrt(8)-1)^8 > 9 for p = 3 (then b = 2 s^2 >= 8)
    assert all(4 * (p - 1) * flog(fsqrt(5) - 1) > 2 * flog(p) for p in range(5, 2000))
    assert (fsqrt(8) - 1) ** 8 > 9
    print("checked: (sqrt(5)-1)^(4(p-1)) > p^2 for 5 <= p < 2000, and (sqrt(8)-1)^8 = %.1f > 9"
          % ((fsqrt(8) - 1) ** 8))
    by = {}
    for b, n, cap in fails:
        by.setdefault(b, []).append(n)
    for b in sorted(by):
        print("  b = %d: n = %s" % (b, ", ".join(map(str, by[b]))))
    print("direct look at the pairs that fail with the cap p^e or with the cap as defined")
    print("(the two norms; a good prime exists if the part prime to 2bn is > 1):")
    allok = True
    look = sorted(set(fails) | {(b, n, 0) for b, n in crude2})
    for b, n, cap in look:
        if n > 400:
            print("  b = %d, n = %d: not computed" % (b, n))
            allok = False
            continue
        parts = []
        for label, N, exps in classes(b, n):
            cof = strip(N, 2 * b * n)
            parts.append("%s: %s%s" % (label, show_int(N), "" if cof > 1 else "  NO GOOD PRIME"))
            allok = allok and cof > 1
        print("  b = %d, n = %d: %s" % (b, n, ";  ".join(parts)))
    print("each of these pairs has a good prime in both classes: %s" % allok)
    return fails


# ---------------------------------------------------------------------------------------
# 4. Base 4, the theory-free probe, self-test
# ---------------------------------------------------------------------------------------

def series(b, rho, digits=60):
    """S(rho) by direct summation; rho is one period, for k = 1, 2, ..."""
    mp.dps = digits + 15
    P = len(rho)
    total, k, bp = mpf(0), 1, mpf(1)
    eps = mpf(10) ** (-(digits + 10))
    while True:
        term = bp / k
        if rho[(k - 1) % P]:
            total += rho[(k - 1) % P] * term
        if term < eps:
            break
        k += 1
        if k % 2 == 0:
            bp /= b
    return total


def cmd_base4():
    mp.dps = 75
    G4 = [1, 2, 0, -2, -1, 0]
    Z4 = [1, -6, -2, -6, 1, 0]
    a = series(4, G4)
    z = series(4, Z4)
    print("base 4, period 6, rho(k) for k = 1..6:")
    print("  G4 = %s:  S - 2 pi sqrt(3)/9 = %s" % (G4, mp.nstr(a - 2 * pi * sqrt(3) / 9, 5)))
    print("  Z4 = %s:  S = %s" % (Z4, mp.nstr(z, 5)))
    print("  exact reasons: (2 - w)(2 - 1/w) = 3 = (2 - 1)(2 + 1) for w a primitive 6th root of 1,")
    print("  and 1 - w/2 = (sqrt(3)/2) exp(-i pi/6).")
    res = analyse(4, 6, nmax=120)
    return res


def cmd_probe(b, P):
    import base3_probe

    def targets(bb):
        out = [("pi", pi)]
        for m in sorted({2, 3, 5, 6, 7, sqfree_split(bb)[1]} - {1}):
            out.append(("pi*sqrt(%d)" % m, pi * sqrt(mpf(m))))
        for p in (2, 3, 5, 7, 11, 13):
            out.append(("log %d" % p, log(mpf(p))))
        return out

    base3_probe.targets = targets
    base3_probe.LOG_PRIMES = None
    return base3_probe.probe(P, b)


def cmd_selftest():
    # 1. the Kronecker character: the Gauss sum is +sqrt(f)
    mp.dps = 40
    for b in range(2, 60):
        s, d, f = base_data(b)
        if d == 1:
            continue
        g = sum(kron(f, c) * mp.expjpi(mpf(2 * c) / f) for c in range(1, f))
        assert abs(g - sqrt(mpf(f))) < mpf(10) ** (-30), b
    print("Gauss sums: ok (b < 60)")
    # 2. one class: the numerical norm of t - r agrees with the formula
    for b in (2, 3, 4, 5, 6, 8, 9, 12, 18, 20):
        s, d, f = base_data(b)
        for n in range(1, 40):
            if is_split(b, n):
                continue
            units = [a for a in range(1, n + 1) if gcd(a, n) == 1]
            mp.dps = 80
            t = sqrt(mpf(b))
            prod = mpc(1)
            for a in units:
                z = mp.expjpi(mpf(2 * a) / n)
                prod *= (t - z) if d == 1 else (t - z) * (-t - z)
            val = abs(int(mp.nint(prod.real)))
            N = classes(b, n)[0][1]
            m = n // gcd(n, 2)
            if d == 1:
                assert val == N, (b, n)
            else:
                # the product of all (t - z)(-t - z) = z^2 - b is Phi_m(b)^e
                e = 2 if n % 4 == 0 else 1
                assert val == N ** e, (b, n, val, N)
    print("norms in the one-class case: ok")
    # 2b. one class although f | n (4 | n and f | n/2): the norm from Q(zeta_n) of t - zeta
    #     is Phi_(n/2)(b) for both signs of t
    cnt = 0
    for b in (2, 3, 5, 6, 8, 12, 13, 20):
        s, d, f = base_data(b)
        for n in range(4, 130, 4):
            if (n // 2) % f:
                continue
            units = [a for a in range(1, n + 1) if gcd(a, n) == 1]
            mp.dps = int(len(units) * flog(fsqrt(b) + 1, 10)) + 60
            t = sqrt(mpf(b))
            for eps in (1, -1):
                prod = mpc(1)
                for a in units:
                    prod *= eps * kron(f, a) * t - mp.expjpi(mpf(2 * a) / n)
                assert abs(int(mp.nint(prod.real))) == abs(cyclo(n // 2, b)), (b, n)
                assert abs(prod.imag) < mpf(10) ** (-25)
            cnt += 1
    print("norms when f | n/2 and 4 | n (one class): ok (%d cases)" % cnt)
    # 3. the known cases: base 5 (first norms), base 3, base 2
    assert [c[1] for c in classes(5, 5)] == [11, 71]
    assert sorted(c[1] for c in classes(5, 15)) == [181, 1741]
    exc3 = exceptional_classes(3, 200)
    assert [(n, lab) for n, lab, _, _ in exc3] == [(1, "all"), (2, "all"), (4, "all"), (12, "+")]
    exc2 = exceptional_classes(2, 200)
    R2 = closure_R0(2, exc2)
    assert len(R2) == 24 and len(closure_R0(3, exc3)) == 6
    print("base 2: R0 has 24 roots; base 3: R0 has 6 roots: ok")
    print("exceptional classes of base 2:", describe_exc(exc2))


if __name__ == "__main__":
    args = sys.argv[1:]
    cmd = args[0] if args else ""
    ints = [int(a) for a in args[1:]]
    if cmd == "scan":
        bmin, bmax, nmax = (ints + [2, 40, 300][len(ints):])[:3]
        cmd_scan(bmin, bmax, nmax)
    elif cmd == "relations":
        analyse(ints[0], ints[1], nmax=max(ints[1], 200))
    elif cmd == "table":
        bmin, bmax, nmax = (ints + [2, 40, 300][len(ints):])[:3]
        cmd_table(bmin, bmax, nmax)
    elif cmd == "bound":
        bmax, nmax = (ints + [200, 3000][len(ints):])[:2]
        cmd_bound(bmax, nmax)
    elif cmd == "powers":
        cmd_powers(ints[0], ints[1])
    elif cmd == "deep":
        # deep BMIN BMAX N BITS: the same search with BITS bits per number (default is 30)
        bmin, bmax, N, bits = ints
        for b in range(bmin, bmax + 1):
            res = find_relations(b, N, bits_per=bits, quiet=True)
            print("base %d, N = %d, %d bits: rank %d; no other relation with sum|z| below 2^%d"
                  % (b, N, res["bits"], res["rank"], res["bound"].bit_length() - 1))
            sys.stdout.flush()
    elif cmd == "check":
        bmax, nmax = (ints + [300, 120][len(ints):])[:2]
        cmd_check(bmax, nmax)
    elif cmd == "base4":
        cmd_base4()
    elif cmd == "probe":
        cmd_probe(ints[0], ints[1])
    elif cmd == "selftest":
        cmd_selftest()
    else:
        print(__doc__)
