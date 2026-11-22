"""For which primes p does log p have a binary BBP-type formula?  The criterion, as a program.

    python log_prime_criterion.py [BOUND]        (default BOUND = 1000000; needs sympy)

Theorem K of notes/pi_formula_theorem.md.  For a positive rational y, log y is the value of
a series of the class F if and only if a power of y is a product of integer powers of 2, the
numbers 2^m - 1, and the numbers 2^n - 2^((n+1)/2) + 1, 2^n + 2^((n+1)/2) + 1 with n odd
(the two factors of 4^n + 1).  These are, up to squares, the norms |(1+i)^n - c|^2 with
c in {1, -1, i, -i}.

For a prime p this becomes a finite test.  Let n = ord_p(2), the order of 2 modulo p, and let
g be the "primitive part" that contains p:

    g = Phi_n(2)                               if n is not 4 (mod 8),
    g = the one of |Phi_d(1+i)|^2, |Phi_2d(1+i)|^2 divisible by p,  d = n/4,   if n = 4 (mod 8)

(the two numbers in the second line multiply to Phi_n(2)).  Write g = p^x R with p not
dividing R.  Then

    log p has a formula   <=>   R = 1,  or  R is a prime q dividing n and log q has a formula.

In words: p must be the only prime in its primitive part, apart from possibly one prime q
that divides the index n, and then q must pass the same test.  log 2 has a formula.

The program decides this for every prime below BOUND, exactly: the primitive part is
computed in full when it could be small enough, and otherwise the bound
Phi_n(2) > 2^(phi(n) - 2) (respectively the same for a half, with exponent phi(n)/2 - 12)
shows that R is too large to be 1 or a prime factor of n.
"""
import sys
from functools import lru_cache

from sympy import cyclotomic_poly, isprime, n_order, primerange, totient, Poly, Symbol

X = Symbol("x")


def gauss_mul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


@lru_cache(maxsize=None)
def norm_phi_at_t(m):
    """|Phi_m(1+i)|^2, exactly."""
    coeffs = [int(c) for c in Poly(cyclotomic_poly(m, X), X).all_coeffs()]
    acc = (0, 0)
    for c in coeffs:                                  # Horner at t = 1 + i
        acc = gauss_mul(acc, (1, 1))
        acc = (acc[0] + c, acc[1])
    return acc[0] * acc[0] + acc[1] * acc[1]


def valuation_of_part(p, n):
    """v_p of the primitive part containing p: v_p(2^n - 1), since p does not divide n."""
    x, mod = 1, p * p
    while pow(2, n, mod) == 1:
        x += 1
        mod *= p
    return x


@lru_cache(maxsize=None)
def has_formula(p):
    """True if log p is a value of the class F (Theorem K), for a prime p."""
    if p == 2:
        return True
    n = n_order(2, p)
    x = valuation_of_part(p, n)
    phi = int(totient(n))
    half = n % 8 == 4
    # R = g / p^x must be 1 or a prime factor of n, so g <= p^x * n
    limit_bits = (p ** x * n).bit_length()
    lower_bits = phi // 2 - 12 if half else phi - 2  # g > 2^lower_bits
    if lower_bits > limit_bits:
        return False
    if half:
        d = n // 4
        a, b = norm_phi_at_t(d), norm_phi_at_t(2 * d)
        assert a * b == int(cyclotomic_poly(n, 2))
        g = a if a % p == 0 else b
        assert g % p == 0 and (a if g is b else b) % p != 0
    else:
        g = int(cyclotomic_poly(n, 2))
    assert g % p ** x == 0 and (g // p ** x) % p != 0
    R = g // p ** x
    if R == 1:
        return True
    if n % R == 0 and isprime(R):
        return has_formula(R)
    return False


def explain(p):
    if p == 2:
        return "2"
    n = n_order(2, p)
    if n % 8 == 4:
        d = n // 4
        a, b = norm_phi_at_t(d), norm_phi_at_t(2 * d)
        g = a if a % p == 0 else b
        name = "|Phi_%d(1+i)|^2" % (d if g == a else 2 * d)
    else:
        g = int(cyclotomic_poly(n, 2))
        name = "Phi_%d(2)" % n
    return "ord = %d, %s = %d" % (n, name, g)


if __name__ == "__main__":
    bound = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
    yes = [p for p in primerange(2, bound) if has_formula(p)]
    print("primes below %d whose logarithm has a formula in the class F: %d" % (bound, len(yes)))
    print(", ".join(str(p) for p in yes))
    lean = {2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73}
    assert {p for p in yes if p < 100} == lean, "disagrees with the Lean theorem below 100"
    print("below 100 this is the list proved in Lean (Theorem H)")
    print()
    for p in [p for p in yes if p < 2000]:
        print("   %5d: %s" % (p, explain(p)))
