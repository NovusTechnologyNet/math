"""Base 3: for which primes p does log p have a ternary BBP-type formula?

    python base3_criterion.py [BOUND]        (default BOUND = 1000000; needs sympy)

The class F3 is the set of series  sum rho(k) 3^(-floor(k/2)) / k  with rho rational and
periodic (Part V of notes/pi_formula_theorem.md).  With t = sqrt(-3) these are combinations
of Log(1 - r/t), r roots of unity, and the criterion of Theorem K carries over:

    for a positive rational y, log y is a value of F3 if and only if a power of y is a
    product of integer powers of 3, of the numbers 3^m - 1, and of the numbers
    3^n - 3^((n+1)/2) + 1 and 3^n + 3^((n+1)/2) + 1 (n odd).

The last two are the Aurifeuillian factors:  3^(3n) + 1 = (3^n + 1) L_n M_n  for odd n.
They are the norms |t^n - c|^2 with c a primitive cube or sixth root of unity.

For a prime p other than 3 this is a finite test.  Let n = ord_p(3) and let g be the
primitive part that contains p:

    g = Phi_n(3)                                         if n is not 6 (mod 12),
    g = the one of gcd(Phi_n(3), L_m), gcd(Phi_n(3), M_m) divisible by p,  m = n/6,
                                                         if n = 6 (mod 12)

(the two numbers in the second line are coprime and multiply to Phi_n(3)).  Write
g = p^x R with p not dividing R.  Then

    log p is a value of F3   <=>   R = 1,  or  R is a prime q dividing n and log q is.

log 3 is a value.  Status: the criterion and this test are machine-checked in Lean
(lean/Pilean/Base3/LogExplicit.lean and LogPrimeTest.lean, from Baker's theorem); the list
that this program prints is the test run on each prime, not a Lean proof prime by prime.
"""
import sys
from functools import lru_cache
from math import gcd

from sympy import divisors, isprime, mobius, n_order, primerange, totient, primefactors

BASE = 3
EXACT_PHI = 3000                 # compute the primitive part exactly up to this phi(n)


@lru_cache(maxsize=None)
def cyc_value(n, b=BASE):
    """Phi_n(b) = prod over d | n of (b^d - 1)^mu(n/d), exactly."""
    num = den = 1
    for d in divisors(n):
        mu = mobius(n // d)
        if mu == 1:
            num *= b ** d - 1
        elif mu == -1:
            den *= b ** d - 1
    assert num % den == 0
    return num // den


@lru_cache(maxsize=None)
def halves(n):
    """The two Aurifeuillian halves of Phi_n(3), n = 6 (mod 12)."""
    assert n % 12 == 6
    m = n // 6
    k = (m + 1) // 2
    L = 3 ** m - 3 ** k + 1
    M = 3 ** m + 3 ** k + 1
    assert L * M * (3 ** m + 1) == 3 ** (3 * m) + 1
    phi = cyc_value(n)
    a, b = gcd(phi, L), gcd(phi, M)
    assert a * b == phi and gcd(a, b) == 1, n
    return a, b


def valuation(p, n):
    """v_p(3^n - 1), which is v_p of the primitive part since p does not divide n."""
    x, mod = 1, p * p
    while pow(BASE, n, mod) == 1:
        x += 1
        mod *= p
    return x


@lru_cache(maxsize=None)
def has_formula(p):
    """True if log p is a value of the class F3 (the criterion), for a prime p."""
    if p == BASE:
        return True
    n = n_order(BASE, p)
    x = valuation(p, n)
    phi = int(totient(n))
    half = n % 12 == 6
    if phi > EXACT_PHI:
        # Phi_n(3) > 2^phi(n), and a half is at least 3^(phi(n)/2 - 2.4 * 2^omega(n)), since
        # it is a Moebius product of at most 2^omega(n) numbers |t^e - c|^2, each within a
        # factor ((1 +- 3^(-1/2))^2) of 3^e.  Either way R is far larger than n.
        lower_bits = (phi // 2 - 3 * 2 ** len(primefactors(n))) * 1.58 if half else phi
        assert lower_bits > (p ** x * n).bit_length() + 64, (p, n)
        return False
    if half:
        a, b = halves(n)
        g = a if a % p == 0 else b
        assert g % p == 0
    else:
        g = cyc_value(n)
    assert g % p ** x == 0 and (g // p ** x) % p != 0, (p, n)
    R = g // p ** x
    if R == 1:
        return True
    if n % R == 0 and isprime(R):
        return has_formula(R)
    return False


def explain(p):
    if p == BASE:
        return "the base"
    n = n_order(BASE, p)
    if n % 12 == 6:
        a, b = halves(n)
        g = a if a % p == 0 else b
        name = "a half of Phi_%d(3) = %d * %d," % (n, a, b)
    else:
        g = cyc_value(n)
        name = "Phi_%d(3) =" % n
    return "ord = %d, %s %d" % (n, name, g)


if __name__ == "__main__":
    bound = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
    # the bound used for large indices, checked where the halves are computed exactly
    for n in range(6, 3000, 12):
        if int(totient(n)) <= 400:
            a, b = halves(n)
            lo = 3 ** max(0, int(totient(n)) // 2 - 3 * 2 ** len(primefactors(n)))
            assert min(a, b) >= lo or lo == 1, n
    yes = [p for p in primerange(2, bound) if has_formula(p)]
    print("primes below %d whose logarithm passes the base-3 criterion: %d" % (bound, len(yes)))
    print(", ".join(str(p) for p in yes))
    print()
    full = [p for p in yes if p != 3 and n_order(3, p) % 12 != 6]
    half = [p for p in yes if p != 3 and n_order(3, p) % 12 == 6]
    print("of these, %d come from a full Phi_n(3) and %d from an Aurifeuillian half" %
          (len(full), len(half)))
    print()
    for p in [p for p in yes if p < 3000]:
        print("   %5d: %s" % (p, explain(p)))
    print()
    no = [p for p in primerange(2, 100) if not has_formula(p)]
    print("primes below 100 that fail: " + ", ".join(str(p) for p in no))
    for p in no:
        print("   %5d: %s" % (p, explain(p)))
