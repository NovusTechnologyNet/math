"""Base b: which logarithms of rational numbers are values of the class F_b?

    python baseb_logs.py selftest
    python baseb_logs.py table B [MMAX]          the norm numbers of base B, indices up to MMAX
    python baseb_logs.py decide B Y [M]          is log Y a value of F_B?   (Y = 3/2, 11/25, 7, ...)
    python baseb_logs.py formula B Y             the same, with the series, checked to 100 digits
    python baseb_logs.py primes B [BOUND]        the primes p < BOUND with log p - w log B a value
    python baseb_logs.py index B [MMAX]          the same from the parts of index <= MMAX, any size
    python baseb_logs.py small B [PMAX]          log p for the primes p < PMAX, by linear algebra
    python baseb_logs.py list B [COUNT] [HEIGHT] the rationals of smallest height with log a value
    python baseb_logs.py chains [BMAX] [MMAX]    the chain configurations, bases 5..BMAX
    python baseb_logs.py weights [BMAX] [MMAX]   a positive weight on primes (Theorem N), checked

Needs sympy and mpmath. Report: research/2026-11-22-log-primes/00_summary.md.

The class F_b is the set of series  S(rho) = sum_{k>=1} rho(k) b^(-floor(k/2)) / k  with rho
rational and periodic; t = sqrt(b); S(rho) = - sum_r D_r Log(1 - r/t), r over roots of unity.

The criterion (summary, Theorem K_b; a paper proof from Baker's theorem). The Galois group acts
on the numbers 1 - r/t by r -> chi(sigma) sigma(r), where sigma(t) = chi(sigma) t. For an orbit
O put P_O = prod_{s in O} (1 - s/t), a positive rational number. Then, for a positive rational
y:  log y is a value of F_b  <=>  some power y^k (k >= 1) is a product of integer powers of the
numbers P_O. This program computes the P_O exactly and decides the right-hand side by exact
linear algebra on vectors of prime exponents. No floating point enters a decision; floating
point is used only in `selftest` and `formula`, to confirm numbers already computed exactly.

The orbits ("parts"), for b = s^2 d not a square, d squarefree, D the discriminant of
Q(sqrt(d)) (D = d if d = 1 mod 4, else 4d). The roots r whose square has order m form a set
R_m of 2 phi(m) roots, and prod_{r in R_m} (t - r) = Phi_m(b).

  * R_m is one orbit, with P = Phi_m(b) / b^phi(m), unless m is a "split" index;
  * m is split when (m odd and D | m) or (m even, D | 2m, D does not divide m), that is when
    m = d mod 2d (d = 1 mod 4) or m = 2d mod 4d (otherwise). Then R_m is two orbits O+, O- = -O+
    and Phi_m(b) = A+ A-, A+- = prod_{s in O+-} (t - s): the Aurifeuillian factors. They are
    computed exactly by Newton's identities from the power sums of O+ (Ramanujan sums for
    even exponents, Gauss sums of the Kronecker character for odd ones; this is Brent's
    algorithm). P = A+- / b^(phi(m)/2).

For b = c^2 the orbits are the sets of roots of a given order n and P = Phi_n(c) / c^phi(n).
A part is recorded as (index, label, A, deg) with P = A / t^deg, deg the number of roots.

What is a proof and what is not. The criterion and the statements quoted in the docstrings
are proved on paper in the summary; they are not machine-checked. `decide` is exact for the
roots of unity of index up to its bound M; when M is at least the order of b modulo every
prime of y (and at least 20 for b <= 4) the summary proves that no larger index can occur, and
the answer is then marked "complete". `primes`, `index` and `chains` evaluate the finite test
for a prime (summary, Theorem P), which is a consequence of the same paper proof; `weights`
builds, for the parts of index up to a bound, the positive weight on primes of Theorem N.
Primality of numbers above 2^64 is tested by sympy's strong probable-prime test. A search
over a bounded range is evidence, not a proof.
"""
import sys
import time
from collections import namedtuple
from fractions import Fraction
from functools import lru_cache
from math import gcd, log as flog, sqrt as fsqrt

from sympy import factorint, integer_nthroot, isprime, n_order, primerange

Part = namedtuple("Part", "index label A deg")


# ---------------------------------------------------------------------------------------
# 0. Small arithmetic
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


@lru_cache(maxsize=None)
def data(b):
    """(s, d, D): b = s^2 d, D the discriminant of Q(sqrt(d)); D = 0 when b is a square."""
    s, d = sqfree_split(b)
    if d == 1:
        return s, 1, 0
    return s, d, (d if d % 4 == 1 else 4 * d)


def order_base(b):
    """The number whose multiplicative orders index the parts: b, or c when b = c^2."""
    s, d, D = data(b)
    return s if d == 1 else b


@lru_cache(maxsize=None)
def fac(n):
    return {int(p): int(e) for p, e in factorint(n).items()}


@lru_cache(maxsize=None)
def phi(n):
    out = n
    for p in fac(n):
        out = out // p * (p - 1)
    return out


@lru_cache(maxsize=None)
def mu(n):
    f = fac(n)
    return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)


@lru_cache(maxsize=None)
def divs(n):
    out = [1]
    for p, e in fac(n).items():
        out = [x * p ** i for x in out for i in range(e + 1)]
    return tuple(sorted(out))


def jacobi(a, n):
    """Jacobi symbol (a/n), n odd and positive."""
    a %= n
    res = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                res = -res
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            res = -res
        a %= n
    return res if n == 1 else 0


def kron(D, a):
    """Kronecker symbol (D/a) for a positive fundamental discriminant D and a >= 1."""
    if gcd(D, a) > 1:
        return 0
    res = 1
    while a % 2 == 0:
        a //= 2
        if D % 8 not in (1, 7):
            res = -res
    return res * jacobi(D, a)


@lru_cache(maxsize=8192)
def cyclo(m, x):
    """Phi_m(x) for an integer x >= 2, exactly."""
    num, den = 1, 1
    for dd in divs(m):
        c = mu(m // dd)
        if c == 1:
            num *= x ** dd - 1
        elif c == -1:
            den *= x ** dd - 1
    assert num % den == 0
    return num // den


def ramanujan(m, j):
    """The Ramanujan sum c_m(j): the sum of the j-th powers of the primitive m-th roots of 1."""
    return sum(dd * mu(m // dd) for dd in divs(gcd(m, j)))


# ---------------------------------------------------------------------------------------
# 1. The parts (orbits) and their numbers
# ---------------------------------------------------------------------------------------

def is_split(b, m):
    """True when R_m is two orbits (the Aurifeuillian case)."""
    s, d, D = data(b)
    if d == 1:
        return False
    if m % 2:
        return m % D == 0
    return (2 * m) % D == 0 and m % D != 0


def gauss_gamma(b, m, k):
    """For a split index m and odd k: the integer g with  sum_{s in O+} s^k = g sqrt(d).

    O+ = { chi(a) zeta_n^a : a prime to n }, n = m (m odd) or 2m (m even), chi = (D/.). The
    sum is the Gauss sum of chi taken modulo n (halved when m is even), and for a character
    induced from a primitive one modulo D it equals sqrt(D) times
        sum over e | gcd(k, n/D) of  e chi(k/e) chi(n/(D e)) mu(n/(D e))
    (Montgomery and Vaughan, Multiplicative Number Theory I, Theorem 9.12). `selftest`
    compares this with the sum itself."""
    s, d, D = data(b)
    n = m if m % 2 else 2 * m
    q = n // D
    tot = 0
    for e in divs(gcd(k, q)):
        c = q // e
        if mu(c):
            tot += e * kron(D, k // e) * kron(D, c) * mu(c)
    return tot


@lru_cache(maxsize=4096)
def halves(b, m):
    """(A+, A-) for a split index m: A+ = prod_{s in O+} (t - s), A- the same for -O+.

    Newton's identities for F(X) = prod_{s in O+} (X - s) = sum (-1)^k e_k X^(deg-k). The
    power sums p_k are c_m(k/2) for even k and g_k sqrt(d) for odd k, so e_k = E_k for even k
    and E_k sqrt(d) for odd k with integers E_k, and
        F(+-t) = sum_{k even} E_k b^((deg-k)/2)  -+  d s sum_{k odd} E_k b^((deg-k-1)/2)."""
    s, d, D = data(b)
    deg = phi(m)
    pw = [0] * (deg + 1)
    for k in range(1, deg + 1):
        pw[k] = ramanujan(m, k // 2) if k % 2 == 0 else gauss_gamma(b, m, k)
    E = [1] + [0] * deg
    for k in range(1, deg + 1):
        acc = 0
        for j in range(1, k + 1):
            term = E[k - j] * pw[j]
            if j % 2 == 1 and k % 2 == 0:
                term *= d
            acc += term if j % 2 == 1 else -term
        assert acc % k == 0, (b, m, k)
        E[k] = acc // k
    U = sum(E[k] * b ** ((deg - k) // 2) for k in range(0, deg + 1, 2))
    V = d * s * sum(E[k] * b ** ((deg - k - 1) // 2) for k in range(1, deg + 1, 2))
    Ap, Am = U - V, U + V
    assert Ap > 0 and Am > 0 and Ap * Am == cyclo(m, b), (b, m)
    return Ap, Am


def parts_of_index(b, m):
    """The parts of index m, as Part(index, label, A, deg); the number is P = A / t^deg."""
    s, d, D = data(b)
    if d == 1:
        return [Part(m, "", abs(cyclo(m, s)), phi(m))]
    if is_split(b, m):
        Ap, Am = halves(b, m)
        return [Part(m, "+", Ap, phi(m)), Part(m, "-", Am, phi(m))]
    return [Part(m, "", cyclo(m, b), 2 * phi(m))]


def part_name(part):
    return "P%d%s" % (part.index, part.label)


def part_number(b, part):
    """The number P_O as a string 'A/b^w' (w may be a half-integer when b is a square)."""
    s, d, D = data(b)
    if d == 1:
        return "%s/%d^%d" % (show_int(part.A), s, part.deg)
    return "%s/%d^%d" % (show_int(part.A), b, part.deg // 2)


def part_roots(b, part):
    """The orbit as a sorted list of Fractions x, standing for the roots exp(2 pi i x)."""
    s, d, D = data(b)
    m = part.index
    if d == 1:
        return sorted(Fraction(a, m) % 1 for a in range(m) if gcd(a, m) == 1)
    if part.label == "":
        return sorted(Fraction(a, 2 * m) for a in range(2 * m) if gcd(a, m) == 1)
    n = m if m % 2 else 2 * m
    shift = Fraction(0) if part.label == "+" else Fraction(1, 2)
    out = set()
    for a in range(1, n + 1):
        if gcd(a, n) == 1:
            out.add((Fraction(a, n) + (Fraction(1, 2) if kron(D, a) == -1 else 0) + shift) % 1)
    return sorted(out)


def rho_part(b, part, k):
    """rho_O(k) = (sum of s^k over the orbit) / t^(k mod 2), a rational number, with
    log P_O = - sum_{k>=1} rho_O(k) b^(-floor(k/2)) / k."""
    s, d, D = data(b)
    m = part.index
    if d == 1:
        return Fraction(ramanujan(m, k), s if k % 2 else 1)
    if part.label == "":
        return Fraction(0) if k % 2 else Fraction(2 * ramanujan(m, k // 2))
    if k % 2 == 0:
        return Fraction(ramanujan(m, k // 2))
    g = gauss_gamma(b, m, k)
    return Fraction(g if part.label == "+" else -g, s)


def part_period(b, part):
    s, d, D = data(b)
    m = part.index
    return (m if m % 2 == 0 else 2 * m) if d == 1 else 2 * m


def c0_data(b, n):
    """For the roots r of order n in a base b that is not a square: a list of
    (label, d(r), |c0(r)|, part, kappa), where d(r) and c0(r) are the degree and the constant
    term of the minimal polynomial of t - r, and |c0(r)| / b^(d(r)/2) = P^kappa for the part."""
    s, d, D = data(b)
    assert d > 1
    m = n // gcd(n, 2)                       # the order of r^2
    out = []
    for part in parts_of_index(b, m):
        if part.label == "":
            if n % D:                        # t is not in Q(zeta_n)
                kappa = 2 if n % 4 == 0 else 1
                out.append(("", 2 * phi(n), part.A ** kappa, part, kappa))
            else:                            # then 4 | n and D | n/2
                out.append(("", phi(n), part.A, part, 1))
        else:
            kappa = 2 if n % 4 == 0 else 1
            out.append((part.label, phi(n), part.A ** kappa, part, kappa))
    return out


# ---------------------------------------------------------------------------------------
# 2. Exact linear algebra on prime exponents
# ---------------------------------------------------------------------------------------

@lru_cache(maxsize=None)
def primes_upto(T):
    return tuple(int(p) for p in primerange(2, T + 1))


@lru_cache(maxsize=None)
def primorial(T):
    out = 1
    for p in primes_upto(T):
        out *= p
    return out


def smooth_split(A, T):
    """A = prod p^e (p <= T) * cofactor, cofactor prime to every p <= T: ({p: e}, cofactor)."""
    g = gcd(A, primorial(T))
    f, cof = {}, A
    if g > 1:
        for p in primes_upto(T):
            if g % p == 0:
                e = 0
                while cof % p == 0:
                    cof //= p
                    e += 1
                f[p] = e
                g //= p
                if g == 1:
                    break
    return f, cof


def solve_exact(cols, target):
    """One rational solution x of sum_j x_j cols[j] = target, or None. Fractions only."""
    nr, nc = len(target), len(cols)
    M = [[Fraction(cols[j][i]) for j in range(nc)] + [Fraction(target[i])] for i in range(nr)]
    piv, r = [], 0
    for c in range(nc):
        if r == nr:
            break
        pr = next((i for i in range(r, nr) if M[i][c] != 0), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        inv = 1 / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    if any(M[i][nc] != 0 for i in range(r, nr)):
        return None
    x = [Fraction(0)] * nc
    for i, c in enumerate(piv):
        x[c] = M[i][nc]
    return x


def rat_factor(y):
    y = Fraction(y)
    assert y > 0
    f = dict(fac(y.numerator))
    for p, e in fac(y.denominator).items():
        f[p] = -e
    f.pop(1, None)
    return f


def complete_bound(b, primes):
    """An index bound beyond which no part can occur in a relation for a number with these
    primes (summary, Lemma T): the largest order of b modulo one of them (at least 2; at
    least 20 in the bases 2, 3, 4, where a few parts have no primitive prime)."""
    beta = order_base(b)
    M = 20 if b <= 4 else 2
    for p in primes:
        if b % p:
            M = max(M, int(n_order(beta, p)))
    return M


def usable_parts(b, M, T):
    """The parts of index <= M all of whose prime factors are <= T, with their factorizations.

    The other parts cannot occur in a relation for a number with primes <= T (T >= M): a
    prime factor above T of a part of index m <= M has order exactly m, so it divides no other
    part of index <= M (the two halves of a split index are coprime)."""
    assert T >= M
    out = []
    for m in range(1, M + 1):
        for part in parts_of_index(b, m):
            f, cof = smooth_split(part.A, T)
            if cof == 1:
                out.append((part, f))
    return out


def exponent_vector(b, coords, f, deg):
    """Twice the exponents of prod p^f[p] / t^deg at the primes in coords."""
    bf = fac(b)
    return [2 * f.get(p, 0) - deg * bf.get(p, 0) for p in coords]


def decide(b, y, M=None):
    """Is log y a value of F_b, using the parts of index <= M?

    Returns a dict: value (bool), M, complete (bool: M is at least complete_bound), and, when
    value is True, k and exps with  y^k = prod P_O^exps[O]  (k >= 1, integers)."""
    fy = rat_factor(y)
    Mc = complete_bound(b, fy)
    if M is None:
        M = Mc
    T = max([M, 2] + list(fy))
    use = usable_parts(b, M, T)
    coords = sorted(set(fy) | set(fac(b)) | {p for _, f in use for p in f})
    cols = [exponent_vector(b, coords, f, part.deg) for part, f in use]
    target = exponent_vector(b, coords, fy, 0)
    res = {"value": False, "M": M, "complete": M >= Mc}
    x = solve_exact(cols, target)
    if x is None:
        return res
    k = 1
    for c in x:
        k = k * c.denominator // gcd(k, c.denominator)
    exps = {part: int(c * k) for (part, f), c in zip(use, x) if c != 0}
    # the identity y^k = prod P^e, checked on the exponent vectors with integers
    for i, p in enumerate(coords):
        assert sum(e * exponent_vector(b, [p], dict(use)[part], part.deg)[0]
                   for part, e in exps.items()) == k * target[i]
    res.update(value=True, k=k, exps=exps)
    return res


def relation_text(res):
    num = " ".join("%s^%d" % (part_name(p), e) if e != 1 else part_name(p)
                   for p, e in sorted(res["exps"].items()) if e > 0)
    den = " ".join("%s^%d" % (part_name(p), -e) if e != -1 else part_name(p)
                   for p, e in sorted(res["exps"].items()) if e < 0)
    lhs = "y" if res["k"] == 1 else "y^%d" % res["k"]
    return "%s = %s%s" % (lhs, num or "1", (" / (%s)" % den) if den else "")


# ---------------------------------------------------------------------------------------
# 3. The series, and a numerical check
# ---------------------------------------------------------------------------------------

def formula(b, res):
    """The pattern rho (one period, k = 1..N) with  sum rho(k) b^(-floor(k/2))/k = log y."""
    N = 1
    for part in res["exps"]:
        per = part_period(b, part)
        N = N * per // gcd(N, per)
    rho = []
    for k in range(1, N + 1):
        rho.append(-sum(e * rho_part(b, part, k) for part, e in res["exps"].items()) / res["k"])
    return N, rho


def series(b, rho, digits=100):
    """sum_{k>=1} rho(k) b^(-floor(k/2)) / k by direct summation; rho is one period."""
    from mpmath import mp, mpf
    mp.dps = digits + 20
    N = len(rho)
    bound = int(max(abs(c) for c in rho)) + 2
    total, k, bp = mpf(0), 1, mpf(1)
    eps = mpf(10) ** (-(digits + 15))
    while True:
        c = rho[(k - 1) % N]
        if c:
            total += mpf(c.numerator) / (c.denominator * bp * k)
        if bound / bp < eps:
            break
        k += 1
        if k % 2 == 0:
            bp *= b
    return total


def check_formula(b, y, res, digits=100):
    """|series - log y|, computed with digits + 20 digits."""
    from mpmath import mp, mpf, log
    N, rho = formula(b, res)
    val = series(b, rho, digits)
    y = Fraction(y)
    return N, rho, abs(val - log(mpf(y.numerator) / y.denominator))


# ---------------------------------------------------------------------------------------
# 4. The finite test for a prime (summary, Theorem P)
# ---------------------------------------------------------------------------------------

def is_pow2(x):
    return x >= 1 and x & (x - 1) == 0


@lru_cache(maxsize=None)
def weight(b, p):
    """For a prime p: the rational w with  log p - w log b  a value of F_b, or None if there
    is none. Base b >= 5, b != 9. (Then log p itself is a value exactly when w = 0; the
    summary proves 0 < w <= phi(ord_p(b)) whenever w exists.)

    p odd, not dividing b, n = ord_p(b): the part of index n that p divides must be p^x R,
    with R = 1, or R the prime q dividing n and w(q) defined, or (n <= 2) R a power of 2 and
    w(2) defined. Then w(p) = (deg/2 - v(R) w(q)) / x. For p = 2: b - 1 or b + 1 must be a
    power of 2. (For b = c^2 read c for b in the orders and in c - 1, c + 1.)"""
    assert b >= 5 and b != 9
    if b % p == 0:
        return None
    beta = order_base(b)
    if p == 2:
        for m in (1, 2):
            part = parts_of_index(b, m)[0]
            if is_pow2(part.A):
                return Fraction(part.deg, 2 * (part.A.bit_length() - 1))
        return None
    n = int(n_order(beta, p))
    x, mod = 1, p * p
    while pow(beta, n, mod) == 1:
        x += 1
        mod *= p
    # every part of index n is at least (sqrt(b) - 1)^phi(n); it must be at most p^x n
    if n >= 3 and phi(n) * flog(fsqrt(b) - 1) > x * flog(p) + flog(n) + 1e-6:
        return None
    for part in parts_of_index(b, n):
        if part.A % p == 0:
            break
    else:
        raise AssertionError((b, p))
    assert part.A % p ** x == 0 and (part.A // p ** x) % p
    R = part.A // p ** x
    half = Fraction(part.deg, 2)
    if R == 1:
        return half / x
    if n >= 3:
        if n % R == 0 and isprime(R):
            wq = weight(b, R)
            return None if wq is None else (half - wq) / x
        return None
    if is_pow2(R):
        w2 = weight(b, 2)
        return None if w2 is None else (half - (R.bit_length() - 1) * w2) / x
    return None


def reachable_primes(b, bound):
    """[(p, w)] for the primes p < bound with w = weight(b, p) defined. Every prime is
    examined: a quick exact filter discards those whose order is too large."""
    beta = order_base(b)
    lt = flog(fsqrt(b) - 1)
    L = 2 * flog(bound) / lt + 1               # phi(n) <= L is necessary when x = 1
    N0 = max(n for n in range(1, int(7 * L) + 12) if phi(n) <= L)
    lam = 1
    for n in range(2, N0 + 1):
        lam = lam * n // gcd(lam, n)
    out = []
    for p in primerange(2, bound):
        p = int(p)
        if b % p == 0:
            continue
        if p > N0 + 1 and pow(beta, p - 1, p * p) != 1:
            # x = 1: the order n must satisfy phi(n) <= L, so n <= N0 and n | gcd(p - 1, lam)
            if pow(beta, gcd(p - 1, lam % (p - 1)), p) != 1:
                continue
        w = weight(b, p)
        if w is not None:
            out.append((p, w))
    return out


_FILTER = {}


def _maybe_power(n, e):
    """False only if n is certainly not an e-th power (e prime): residues modulo 3 primes."""
    if e not in _FILTER:
        ls, l = [], e + 1
        while len(ls) < 3:
            if isprime(l):
                ls.append(l)
            l += e
        _FILTER[e] = ls
    for l in _FILTER[e]:
        r = n % l
        if r and pow(r, (l - 1) // e, l) != 1:
            return False
    return True


def prime_power(n, lo=2):
    """(p, x) if n = p^x with p prime, p >= lo; else None."""
    if n < 2:
        return None
    if isprime(n):
        return (n, 1)
    maxe = int(n.bit_length() * flog(2) / flog(max(lo, 2))) + 1
    for e in primes_upto(max(maxe, 2)):
        if e > maxe:
            break
        if not _maybe_power(n, e):
            continue
        r, exact = integer_nthroot(n, e)
        if exact:
            pp = prime_power(int(r), lo)
            return None if pp is None else (pp[0], pp[1] * e)
    return None


def strip_nonprimitive(part):
    """(A', R): A = A' R with R the part of A made of primes that are not primitive for the
    index (the largest prime factor of the index, once; or the power of 2 for index <= 2)."""
    m, A, R = part.index, part.A, 1
    if m >= 3:
        q = max(fac(m))
        if A % q == 0:
            A //= q
            R = q
    else:
        while A % 2 == 0:
            A //= 2
            R *= 2
    return A, R


def weight_of_part(b, part):
    """(p, x, R, w) if the part is p^x R as in `weight`, with w = w(p) or None; else None."""
    A, R = strip_nonprimitive(part)
    pp = prime_power(A, part.index + 1)
    if pp is None:
        return None
    p, x = pp
    half = Fraction(part.deg, 2)
    if R == 1:
        return p, x, R, half / x
    if part.index >= 3:
        wq = weight(b, R)
        return p, x, R, (None if wq is None else (half - wq) / x)
    w2 = weight(b, 2)
    return p, x, R, (None if w2 is None else (half - (R.bit_length() - 1) * w2) / x)


def certificate(b, M):
    """A weight lam on primes with lam_p > 0 and  sum_p lam_p v_p(A) = deg/2  for every part
    (index, label, A, deg) of index <= M: the construction in the proof of Theorem N. Returns
    {p: lam_p} for the primes that divide a part of index <= M. Needs the full factorization
    of these parts. Base b >= 5, b != 9.

    A prime that divides a part and its index (or 2, for the indices 1 and 2) got its weight
    at a smaller index; what is left of deg/2 must be positive and is shared equally among
    the other prime factors, counted with multiplicity."""
    assert b >= 5 and b != 9
    lam = {}
    if order_base(b) % 2:
        p1, p2 = parts_of_index(b, 1)[0], parts_of_index(b, 2)[0]
        a = (p1.A & -p1.A).bit_length() - 1
        u = (p2.A & -p2.A).bit_length() - 1
        if is_pow2(p1.A):
            lam[2] = Fraction(p1.deg, 2 * a)
        elif is_pow2(p2.A):
            lam[2] = Fraction(p2.deg, 2 * u)
        else:
            lam[2] = Fraction(p1.deg, 4 * max(a, u))
    for m in range(1, M + 1):
        for part in parts_of_index(b, m):
            f = fac(part.A)
            rest = Fraction(part.deg, 2) - sum(lam[p] * e for p, e in f.items() if p in lam)
            new = {p: e for p, e in f.items() if p not in lam}
            if not new:
                assert rest == 0, (b, m)
            else:
                assert rest > 0, (b, m, rest)
                tot = sum(new.values())
                for p in new:
                    assert p == 2 or m == int(n_order(order_base(b), p)), (b, m, p)
                    lam[p] = rest / tot
    assert all(v > 0 for v in lam.values())
    return lam


def cmd_weights(bmax, M):
    t0 = time.time()
    nb = nprimes = 0
    low = None
    for b in range(5, bmax + 1):
        if b == 9:
            continue
        lam = certificate(b, M)
        nb += 1
        nprimes += len(lam)
        p = min(lam, key=lambda q: lam[q])
        if low is None or lam[p] < low[0]:
            low = (lam[p], b, p)
        # the forced values agree with the finite test
        for q in primes_upto(60):
            w = weight(b, q)
            if w is not None and q in lam:
                assert lam[q] == w, (b, q, lam[q], w)
    print("bases 5..%d (not 9), parts of index <= %d, all factored: a positive weight on the"
          % (bmax, M))
    print("   %d primes involved exists in each of the %d bases; smallest weight %s"
          " (b = %d, p = %d)   (%.0f s)" % (nprimes, nb, low[0], low[1], low[2], time.time() - t0))
    for b in (7, 10):
        if b <= bmax:
            lam = certificate(b, M)
            print("   base %d: %s"
                  % (b, ", ".join("%d: %s" % (q, lam[q]) for q in sorted(lam)[:14])))


# ---------------------------------------------------------------------------------------
# 5. Commands
# ---------------------------------------------------------------------------------------

def show_int(N):
    if N == 1:
        return "1"
    if N > 10 ** 40:
        return "(%d digits)" % len(str(N))
    return "*".join("%d^%d" % (p, e) if e > 1 else str(p) for p, e in sorted(fac(N).items()))


def cmd_table(b, mmax):
    s, d, D = data(b)
    if d == 1:
        print("base %d = %d^2: the parts are P_n = Phi_n(%d) / %d^phi(n)" % (b, s, s, s))
        for n in range(1, mmax + 1):
            part = parts_of_index(b, n)[0]
            print("  n = %3d   Phi_n(%d) = %s   deg %d" % (n, s, show_int(part.A), part.deg))
        return
    split = [m for m in range(1, 40 * d) if is_split(b, m)][:4]
    print("base %d = %d^2 * %d, D = %d; split indices: %s, ..." % (b, s, d, D, split))
    print("  m : orders n of r : class : d(r) : |c0(r)| : P = nu^(1/kappa)")
    for m in range(1, mmax + 1):
        orders = [m, 2 * m] if m % 2 else [2 * m]
        for n in orders:
            for label, deg, c0, part, kappa in c0_data(b, n):
                print("  m = %3d  n = %3d  %-1s  d = %3d  |c0| = %s%s%s   P = %s%s"
                      % (m, n, label, deg, "(" if kappa == 2 else "", show_int(part.A),
                         ")^2" if kappa == 2 else "", part_number(b, part),
                         "  (nu = P^2)" if kappa == 2 else ""))


def parse_rat(txt):
    return Fraction(txt)


def cmd_decide(b, y, M=None, with_formula=False):
    res = decide(b, y, M)
    how = "complete" if res["complete"] else "bounded search, not complete"
    if not res["value"]:
        print("base %d: log %s is NOT a value (parts of index <= %d; %s)" % (b, y, res["M"], how))
        return res
    print("base %d: log %s is a value (parts of index <= %d; %s)" % (b, y, res["M"], how))
    print("   " + relation_text(res))
    for part in sorted(res["exps"]):
        print("   %s = %s" % (part_name(part), part_number(b, part)))
    if with_formula:
        N, rho, err = check_formula(b, y, res)
        from mpmath import mp
        print("   period %d; rho(1..%d) = %s" % (N, N, " ".join(str(c) for c in rho)))
        print("   |sum rho(k) %d^(-floor(k/2))/k - log %s| = %s" % (b, y, mp.nstr(err, 3)))
        assert err < 1e-100
    return res


def cmd_primes(b, bound):
    t0 = time.time()
    found = reachable_primes(b, bound)
    print("base %d: primes p < %d with log p - w log %d a value of F_%d: %d   (%.0f s)"
          % (b, bound, b, b, len(found), time.time() - t0))
    print("   p (w): " + ", ".join("%d (%s)" % (p, w) for p, w in found))
    zero = [p for p, w in found if w == 0]
    neg = [p for p, w in found if w < 0]
    print("   with w = 0, that is with log p itself a value: %s" % (zero or "none"))
    print("   with w < 0: %s;  smallest w: %s" % (neg or "none", min(w for p, w in found)))
    return found


def cmd_index(b, mmax):
    t0 = time.time()
    rows = []
    for m in range(1, mmax + 1):
        for part in parts_of_index(b, m):
            got = weight_of_part(b, part)
            if got is not None and got[3] is not None:
                rows.append((part, got))
    print("base %d: parts of index <= %d of the form p^x R with w(p) defined: %d   (%.0f s)"
          % (b, mmax, len(rows), time.time() - t0))
    for part, (p, x, R, w) in rows:
        ptxt = str(p) if p < 10 ** 30 else "prime of %d digits" % len(str(p))
        print("   index %3d%-1s  p = %s%s%s   w = %s"
              % (part.index, part.label, ptxt, ("^%d" % x) if x > 1 else "",
                 (" (times %d)" % R) if R > 1 else "", w))
    ws = [got[3] for _, got in rows]
    print("   w = 0: %s;  smallest w: %s" % ([str(g[0]) for _, g in rows if g[3] == 0] or "none",
                                             min(ws) if ws else "-"))
    return rows


def cmd_small(b, pmax):
    """For each prime p < pmax: log p by exact linear algebra (complete), and the weight."""
    values, checked, withw = [], 0, []
    for p in primes_upto(pmax - 1):
        res = decide(b, p)
        assert res["complete"]
        checked += 1
        if res["value"]:
            values.append(p)
        if b >= 5 and b != 9 and b % p:
            w = weight(b, p)
            if w is not None:
                # log p - w log b must then be a value: test p^k / b^(w k), k the denominator
                k = w.denominator
                r2 = decide(b, Fraction(p ** k, b ** (w.numerator)))
                assert r2["value"], (b, p, w)
                withw.append((p, w))
            else:
                # no rational w at all: p must not be in the span of the parts and b
                assert span_with_base(b, p) is None, (b, p)
    print("base %d: primes p < %d: %d examined, log p a value for: %s"
          % (b, pmax, checked, values or "none"))
    if withw:
        print("   log p - w log %d a value, p (w): %s"
              % (b, ", ".join("%d (%s)" % x for x in withw)))
    return values


def span_with_base(b, p):
    """A rational w with log p - w log b a value, found by linear algebra alone (no theory of
    weights): the vector of p must lie in the span of the parts and of b. Returns w or None."""
    fy = rat_factor(p)
    M = complete_bound(b, fy)
    T = max([M, 2] + list(fy))
    use = usable_parts(b, M, T)
    coords = sorted(set(fy) | set(fac(b)) | {q for _, f in use for q in f})
    cols = [exponent_vector(b, coords, f, part.deg) for part, f in use]
    cols.append(exponent_vector(b, coords, fac(b), 0))
    x = solve_exact(cols, exponent_vector(b, coords, fy, 0))
    return None if x is None else x[-1]


def value_list(b, height):
    """All y = u/v > 1 in lowest terms with u, v <= height and log y a value of F_b, sorted by
    u then v. Complete for this height (summary, Lemma T)."""
    M = complete_bound(b, primes_upto(height))
    T = max(M, height)
    use = usable_parts(b, M, T)
    coords = sorted(set(primes_upto(height)) | set(fac(b)) | {p for _, f in use for p in f})
    rows = [exponent_vector(b, coords, f, part.deg) for part, f in use]
    # functionals that vanish on every part: the null space of the matrix of rows
    null = nullspace(rows, len(coords))
    sig = {}
    for u in range(1, height + 1):
        v = exponent_vector(b, coords, fac(u) if u > 1 else {}, 0)
        key = tuple(sum(a * c for a, c in zip(lam, v)) for lam in null)
        sig.setdefault(key, []).append(u)
    out = []
    for group in sig.values():
        for u in group:
            for v in group:
                if v < u and gcd(u, v) == 1:
                    out.append(Fraction(u, v))
    out.sort(key=lambda y: (y.numerator, y.denominator))
    return out


def nullspace(rows, n):
    """A basis (integer vectors) of { lam : lam . row = 0 for every row }."""
    M = [[Fraction(x) for x in row] for row in rows]
    piv, r = [], 0
    for c in range(n):
        pr = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        inv = 1 / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(n) if c not in piv]
    out = []
    for fcol in free:
        v = [Fraction(0)] * n
        v[fcol] = Fraction(1)
        for i, c in enumerate(piv):
            v[c] = -M[i][fcol]
        den = 1
        for x in v:
            den = den * x.denominator // gcd(den, x.denominator)
        out.append([int(x * den) for x in v])
    return out


def cmd_list(b, count, height):
    ys = value_list(b, height)
    print("base %d: %d rationals y = u/v > 1 with u, v <= %d and log y a value; the first %d:"
          % (b, len(ys), height, min(count, len(ys))))
    used = set()
    for y in ys[:count]:
        res = decide(b, y)
        assert res["value"] and res["complete"]
        used |= set(res["exps"])
        print("   %-9s %s" % (y, relation_text(res)))
    print("   where " + ", ".join("%s = %s" % (part_name(p), part_number(b, p))
                                  for p in sorted(used)))
    print("   integers among the %d: %s"
          % (len(ys), [str(y) for y in ys if y.denominator == 1] or "none"))
    return ys


def cmd_chains(bmax, mmax):
    """Bases 5..bmax (not 9), parts of index <= mmax that contain a non-primitive prime (or
    have index <= 2): which are p^x R, and is w(p) > 0 whenever it is defined?"""
    t0 = time.time()
    nparts = nchain = nlive = 0
    mingap, minw, examples = None, None, []
    for b in range(5, bmax + 1):
        if b == 9:
            continue
        beta = order_base(b)
        todo = {1, 2}
        for q in primes_upto(mmax):
            if b % q == 0:
                continue
            m = int(n_order(beta, q)) * q
            while m <= mmax:
                todo.add(m)
                m *= q
        for m in sorted(todo):
            for part in parts_of_index(b, m):
                A, R = strip_nonprimitive(part)
                if m >= 3 and R == 1:
                    continue
                nparts += 1
                got = weight_of_part(b, part)
                if got is None:
                    continue
                p, x, R, w = got
                if R > 1:
                    nchain += 1
                if w is None:
                    continue
                nlive += 1
                assert w > 0, (b, m, p, x, R, w)
                gap = w * x
                if R > 1 and (mingap is None or gap < mingap[0]):
                    mingap = (gap, b, m, part.label, p, x, R)
                if minw is None or w < minw[0]:
                    minw = (w, b, m, part.label, p, x, R)
                if R > 1 and m >= 3 and len(examples) < 12 and (x > 1 or b <= 12):
                    examples.append((b, m, part.label, p, x, R, w))
    print("bases 5..%d (not 9), indices <= %d: %d parts with a non-primitive prime or index <= 2"
          % (bmax, mmax, nparts))
    print("   of the form p^x R with R > 1: %d;  with w(p) defined (R = 1 allowed): %d   (%.0f s)"
          % (nchain, nlive, time.time() - t0))
    where = "  (b = %d, index %d%s, p = %d, x = %d, R = %d)"
    print(("   w(p) > 0 in every case; smallest w(p): %s" + where) % minw)
    print(("   smallest deg/2 - v(R) w(q) with R > 1: %s" + where) % mingap)
    for b, m, lab, p, x, R, w in examples:
        print("   example: b = %d, index %d%s: part = %d * %d^%d, w(%d) = %s"
              % (b, m, lab, R, p, x, p, w))


def cmd_selftest():
    from mpmath import mp, mpf, mpc, sqrt, expjpi
    mp.dps = 50
    # 1. the Kronecker character: the Gauss sum is +sqrt(D)
    for b in range(2, 80):
        s, d, D = data(b)
        if d == 1:
            continue
        g = sum(kron(D, c) * expjpi(mpf(2 * c) / D) for c in range(1, D))
        assert abs(g - sqrt(mpf(D))) < mpf(10) ** (-30), b
    print("1. Gauss sums of the Kronecker characters: ok (b < 80)")
    # 2. the formula for the power sums of O+ at odd exponents
    cnt = 0
    for b in (2, 3, 5, 6, 7, 10, 12, 13, 15, 20, 45):
        s, d, D = data(b)
        for m in [m for m in range(1, 8 * d + 1) if is_split(b, m)][:3]:
            part = Part(m, "+", 0, phi(m))
            roots = part_roots(b, part)
            assert len(roots) == phi(m)
            for k in range(1, 2 * m + 2, 2):
                direct = sum(expjpi(2 * k * mpf(x.numerator) / x.denominator) for x in roots)
                want = gauss_gamma(b, m, k) * sqrt(mpf(d))
                assert abs(direct - want) < mpf(10) ** (-25), (b, m, k)
                cnt += 1
    print("2. power sums of O+ against the closed formula: ok (%d sums)" % cnt)
    # 3. the orbits under the twisted Galois action are the parts, and P_O = A / t^deg
    cnt = 0
    for b in (5, 6, 7, 8, 10, 12, 13, 16, 20):
        s, d, D = data(b)
        for N in (24, 30, 40, 2 * D if D else 36):
            if N > 130:
                continue
            group = []
            for a in range(1, N + 1):
                if gcd(a, N) == 1:
                    if d == 1:
                        group.append((a, 1))
                    elif N % D == 0:
                        group.append((a, kron(D, a)))
                    else:
                        group += [(a, 1), (a, -1)]
            seen = set()
            for j in range(N):
                x = Fraction(j, N)
                if x in seen:
                    continue
                orb = sorted({(a * x + (Fraction(1, 2) if eps == -1 else 0)) % 1
                              for a, eps in group})
                seen |= set(orb)
                if d == 1:
                    idx = x.denominator
                else:
                    idx = x.denominator // gcd(x.denominator, 2)
                match = [p for p in parts_of_index(b, idx) if part_roots(b, p) == orb]
                assert len(match) == 1, (b, N, x)
                part = match[0]
                mp.dps = int(part.deg * flog(fsqrt(b) + 1, 10)) + 50
                t = sqrt(mpf(b))
                prod = mpc(1)
                for z in orb:
                    prod *= t - expjpi(2 * mpf(z.numerator) / z.denominator)
                assert abs(prod - part.A) < mpf(10) ** (-25), (b, N, x)
                cnt += 1
    mp.dps = 50
    print("3. orbits of the twisted action = parts, and prod (t - s) = A: ok (%d orbits)" % cnt)
    # 4. degree and constant term of the minimal polynomial of t - r
    cnt = 0
    for b in (5, 6, 7, 10, 12, 13):
        s, d, D = data(b)
        for n in list(range(1, 31)) + [D, 2 * D, 4 * D]:
            if n > 110:
                continue
            N = n * D // gcd(n, D)
            for label, deg, c0, part, kappa in c0_data(b, n):
                x0 = next(x for x in part_roots(b, part) if x.denominator == n)
                conj = set()
                for a in range(1, N + 1):
                    if gcd(a, N) == 1:
                        conj.add((kron(D, a), (a * x0) % 1))
                assert len(conj) == deg, (b, n, len(conj), deg)
                mp.dps = int(deg * flog(fsqrt(b) + 1, 10)) + 50
                t = sqrt(mpf(b))
                prod = mpc(1)
                for eps, z in conj:
                    prod *= eps * t - expjpi(2 * mpf(z.numerator) / z.denominator)
                assert abs(abs(prod) - c0) < mpf(10) ** (-25), (b, n)
                cnt += 1
    mp.dps = 50
    print("4. degree and constant term of the minimal polynomial of t - r: ok (%d classes)" % cnt)
    # 5. known halves
    assert halves(5, 5) == (11, 71) and sorted(halves(5, 15)) == [181, 1741]
    assert sorted(halves(2, 4)) == [1, 5] and sorted(halves(2, 12)) == [1, 13]
    assert sorted(halves(3, 6)) == [1, 7] and sorted(halves(3, 18)) == [19, 37]
    assert sorted(halves(12, 6)) == [7, 19] and sorted(halves(6, 12)) == [13, 97]
    assert sorted(halves(10, 20)) == [3541, 27961] and sorted(halves(7, 14)) == [113, 911]
    print("5. Aurifeuillian halves (bases 2, 3, 5, 6, 7, 10, 12): ok")
    # 6. cofactors above T are pairwise coprime
    for b, M in ((10, 60), (5, 60), (12, 48)):
        cofs = []
        for m in range(1, M + 1):
            for part in parts_of_index(b, m):
                f, cof = smooth_split(part.A, M)
                if cof > 1:
                    cofs.append(cof)
        for i in range(len(cofs)):
            for j in range(i):
                assert gcd(cofs[i], cofs[j]) == 1
    print("6. parts with their primes <= M removed are pairwise coprime: ok")
    # 7. Theorem K5
    for y in (Fraction(3, 2), Fraction(4, 5), Fraction(11, 25), Fraction(71, 25), Fraction(31, 25)):
        res = decide(5, y)
        assert res["value"] and res["complete"]
        N, rho, err = check_formula(5, y, res)
        assert err < mpf(10) ** (-100), (y, err)
    for y in (2, 3, 5):
        res = decide(5, y)
        assert not res["value"] and res["complete"]
        assert not decide(5, y, 200)["value"]
    print("7. base 5 (Theorem K5): log(3/2), log(4/5), log(11/25), log(71/25), log(31/25) are")
    print("   values (series checked to 100 digits); log 2, log 3, log 5 are not")
    # 8. bases 2 and 3: the machine-checked lists below 100
    yes2 = [p for p in primes_upto(100) if decide(2, p)["value"]]
    assert yes2 == [2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73], yes2
    no3 = [p for p in primes_upto(100) if not decide(3, p)["value"]]
    assert no3 == [17, 23, 29, 47, 53, 59, 67, 71, 79, 83, 89, 97], no3
    assert decide(9, 3)["value"] and decide(9, 2)["value"]
    for y in (2, 5, 10):
        assert not decide(10, y, 120)["value"]
    print("8. bases 2 and 3: the lists of primes below 100 of Theorems H and K3; base 9: log 3;")
    print("   base 10: log 2, log 5, log 10 are not values: ok")
    # 9. the weights against linear algebra
    for b in (5, 6, 7, 8, 10, 12, 13, 16, 17):
        for p in primes_upto(60):
            w = weight(b, p)
            assert w == span_with_base(b, p) or b % p == 0, (b, p, w)
            assert not decide(b, p)["value"]
    assert weight(5, 2) == Fraction(1, 2) and weight(5, 7) == Fraction(3, 2)
    assert weight(5, 521) == 4 and weight(7, 5) == Fraction(5, 6)
    print("9. weights of primes against linear algebra (9 bases, p < 60): ok")
    # 10. a formula in base 10 with an Aurifeuillian half
    res = decide(10, Fraction(3541, 10 ** 4))
    assert res["value"] and check_formula(10, Fraction(3541, 10 ** 4), res)[2] < mpf(10) ** (-100)
    res = decide(10, Fraction(37, 33))
    assert res["value"] and check_formula(10, Fraction(37, 33), res)[2] < mpf(10) ** (-100)
    print("10. base 10: log(3541/10^4) and log(37/33), series checked to 100 digits: ok")


if __name__ == "__main__":
    args = sys.argv[1:]
    cmd = args[0] if args else ""
    if cmd == "selftest":
        cmd_selftest()
    elif cmd == "table":
        cmd_table(int(args[1]), int(args[2]) if len(args) > 2 else 24)
    elif cmd in ("decide", "formula"):
        cmd_decide(int(args[1]), parse_rat(args[2]), int(args[3]) if len(args) > 3 else None,
                   with_formula=(cmd == "formula"))
    elif cmd == "primes":
        cmd_primes(int(args[1]), int(args[2]) if len(args) > 2 else 10 ** 6)
    elif cmd == "index":
        cmd_index(int(args[1]), int(args[2]) if len(args) > 2 else 200)
    elif cmd == "small":
        cmd_small(int(args[1]), int(args[2]) if len(args) > 2 else 200)
    elif cmd == "list":
        cmd_list(int(args[1]), int(args[2]) if len(args) > 2 else 30,
                 int(args[3]) if len(args) > 3 else 150)
    elif cmd == "weights":
        cmd_weights(int(args[1]) if len(args) > 1 else 60, int(args[2]) if len(args) > 2 else 24)
    elif cmd == "chains":
        cmd_chains(int(args[1]) if len(args) > 1 else 200, int(args[2]) if len(args) > 2 else 120)
    else:
        print(__doc__)
