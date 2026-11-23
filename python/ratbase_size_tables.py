"""Rational bases p/q with 2 <= q < p <= 15: the table for the size condition, as a Lean file

    python ratbase_size_tables.py          check everything and print one line per pair
    python ratbase_size_tables.py write    the same, and write the Lean file
                                           lean/Pilean/RatBase/SizeSmallTable.lean

Needs only the standard library. Prints ASCII only. Exact integer arithmetic throughout.

The size condition SC(p, q, m), m >= 3, with Phi = Phi_m(p, q) the homogeneous cyclotomic value and
phi = phi(m):

    (sqrt p + sqrt q)^phi < Phi,   and   l (sqrt p + sqrt q)^phi < Phi
    for every prime l dividing both m and Phi.

The Lean statement PiFormula.RatBase.SizeSmall says that SC holds for all coprime 2 <= q < p <= 15
other than 3/2 and 4/3, and all m >= 3, outside the twelve triples of LEFTOVER below. The Lean
proof (lean/Pilean/RatBase/SizeSmallAux.lean, SizeSmallAuxCert.lean) checks one certificate for
each of the 55 pairs. This program computes the certificates, checks them with the same integer
tests as the Lean function certOK, and writes them as a Lean list.

A certificate for (p, q) is (a, b, F, rows):

  * a/b >= sqrt(pq), that is p q b^2 <= a^2. Then (sqrt p + sqrt q)^2 <= s/b, s = b (p + q) + 2 a.
    Here b = 1000 and a is the least such integer.
  * F is the least number with, for D = (p^2 + q^2 - p q) b,
        (F + 2)^2 s^(F+1) < D^(F+1)    and    (F + 3)^2 s <= (F + 2)^2 D.
    Then (n + 1)^2 s^n < D^n for every n > F, and from Phi^2 >= (p^2 - p q + q^2)^phi and
    l <= phi + 1 for a prime l dividing m, SC holds at every m with phi(m) > F.
  * If phi(m) <= F then m A <= F B, where A is the product of the l - 1 and B the product of the
    l over the primes l < F + 2. So m <= M = floor(F B / A).
  * rows: the factored forms [(l1, e1), ...] of m = 3, 4, ..., M. A row passes if (p, q, m) is in
    LEFTOVER, or phi(m) > F, or, with h = phi(m)/2 and N = Phi_m(p, q),
        s^h < N b^h,   and for each prime l of m:  l does not divide N,  or  l s^h < N b^h.

Phi_m(a, b) is computed from the factored form of m by Phi_1(a, b) = a - b and, for a prime l
not dividing n,  Phi_(l^e n)(a, b) = Phi_n(a^(l^e), b^(l^e)) / Phi_n(a^(l^(e-1)), b^(l^(e-1))).
"""

import os
import sys
from math import gcd, isqrt

PMAX = 15
B = 1000
LEFTOVER = {(5, 2, 3), (5, 2, 14), (5, 4, 6), (5, 4, 18), (6, 5, 22), (7, 2, 6), (7, 3, 10),
            (7, 5, 6), (8, 7, 6), (8, 7, 10), (11, 7, 6), (11, 10, 6)}
# the list smallPrimes of SizeSmallAux.lean: the primes below 400
SMALL_PRIMES = [x for x in range(2, 400) if all(x % d for d in range(2, isqrt(x) + 1))]


def factor(m):
    """The factored form of m: the list of (prime, exponent), primes increasing."""
    f = []
    for l in SMALL_PRIMES:
        if m % l == 0:
            e = 0
            while m % l == 0:
                m //= l
                e += 1
            f.append((l, e))
    if m != 1:
        raise ValueError("a prime factor is not below 400")
    return f


def prod_f(fm):
    r = 1
    for l, e in fm:
        r *= l ** e
    return r


def tot_f(fm):
    t = 1
    for l, e in fm:
        t *= l ** (e - 1) * (l - 1)
    return t


def wf_f(fm):
    for i, (l, e) in enumerate(fm):
        if l not in SMALL_PRIMES or e < 1 or prod_f(fm[i + 1:]) % l == 0:
            return False
    return True


def phi_n(fm, a, b):
    """Phi_m(a, b) for a > b, from the factored form of m (the Lean function phiN)."""
    if not fm:
        return a - b
    (l, e), rest = fm[0], fm[1:]
    num = phi_n(rest, a ** l ** e, b ** l ** e)
    den = phi_n(rest, a ** l ** (e - 1), b ** l ** (e - 1))
    return num // den


def phi_by_divisors(m, a, b, cache):
    """Phi_m(a, b) another way: (a^m - b^m) divided by the Phi_d(a, b), d a proper divisor."""
    if m not in cache:
        v = a ** m - b ** m
        for d in range(1, m):
            if m % d == 0:
                v, r = divmod(v, phi_by_divisors(d, a, b, cache))
                assert r == 0
        cache[m] = v
    return cache[m]


def primes_lt(n):
    return [l for l in SMALL_PRIMES if l < n]


def direct_ok(s, b, big_n, h, fm):
    if not s ** h < big_n * b ** h:
        return False
    return all(big_n % l != 0 or l * s ** h < big_n * b ** h for l, _ in fm)


def row_ok(p, q, a, b, big_f, m, fm):
    if (p, q, m) in LEFTOVER:
        return True
    if not (wf_f(fm) and prod_f(fm) == m):
        return False
    t = tot_f(fm)
    if big_f < t:
        return True
    return t % 2 == 0 and direct_ok(b * (p + q) + 2 * a, b, phi_n(fm, p, q), t // 2, fm)


def cert_ok(p, q, a, b, big_f, rows):
    s = b * (p + q) + 2 * a
    d = (p * p + q * q - p * q) * b
    pl = primes_lt(big_f + 2)
    prod_a = 1
    prod_b = 1
    for l in pl:
        prod_a *= l - 1
        prod_b *= l
    return (0 < q < p and 0 < b and p * q * b * b <= a * a
            and (big_f + 2) ** 2 * s ** (big_f + 1) < d ** (big_f + 1)
            and (big_f + 3) ** 2 * s <= (big_f + 2) ** 2 * d
            and big_f + 2 <= 400
            and big_f * prod_b < (3 + len(rows)) * prod_a
            and all(row_ok(p, q, a, b, big_f, 3 + i, fm) for i, fm in enumerate(rows)))


def make_cert(p, q):
    b = B
    n = p * q * b * b
    a = isqrt(n)
    if a * a < n:
        a += 1
    s = b * (p + q) + 2 * a
    d = (p * p + q * q - p * q) * b
    big_f = 0
    while not ((big_f + 2) ** 2 * s ** (big_f + 1) < d ** (big_f + 1)
               and (big_f + 3) ** 2 * s <= (big_f + 2) ** 2 * d):
        big_f += 1
        if big_f > 300:
            raise ValueError("no F for %d/%d" % (p, q))
    prod_a = 1
    prod_b = 1
    for l in primes_lt(big_f + 2):
        prod_a *= l - 1
        prod_b *= l
    big_m = (big_f * prod_b) // prod_a
    rows = [factor(m) for m in range(3, big_m + 1)]
    return a, b, big_f, rows


def pairs():
    return [(p, q) for p in range(3, PMAX + 1) for q in range(2, p)
            if gcd(p, q) == 1 and (p, q) not in ((3, 2), (4, 3))]


def wrap(tokens, indent, width=100):
    """Join the tokens with ', ' into lines of at most `width` characters."""
    lines = []
    cur = indent
    for i, tok in enumerate(tokens):
        piece = tok + ("," if i + 1 < len(tokens) else "")
        if cur.strip() == "":
            cand = cur + piece
        else:
            cand = cur + " " + piece
        if len(cand) > width and cur.strip() != "":
            lines.append(cur)
            cur = indent + piece
        else:
            cur = cand
    if cur.strip() != "":
        lines.append(cur)
    return lines


def lean_row(fm):
    return "[" + ", ".join("(%d, %d)" % (l, e) for l, e in fm) + "]"


HEADER = """import Pilean.RatBase.SizeSmallAuxCert

/-!
# The size condition for small rational bases: the table of certificates

Generated by `python/ratbase_size_tables.py write`. Do not edit by hand.

`smallCerts` has one certificate `⟨p, q, a, b, F, rows⟩` (see `SizeSmallAuxCert.lean`) for each
of the %d pairs `2 ≤ q < p ≤ 15`, `p` and `q` coprime, other than `(3, 2)` and `(4, 3)`. Here
`a/b ≥ √(p q)` with `b = %d`, the analytic bound gives the size condition for `φ(m) > F`, and
`rows` lists the factored forms of `m = 3, 4, …, M`, where `φ(m) ≤ F` forces `m ≤ M`. In all,
%d rows, of which %d are checked on the integers (the others have `φ(m) > F` or are in
`leftoverTriples`).

* `smallCerts_ok`: every certificate passes the check (kernel computation).
* `exists_smallCert`: every pair in the range has a certificate.
-/

namespace PiFormula

namespace RatBase

/-- One certificate for each pair `2 ≤ q < p ≤ 15`, coprime, other than `(3, 2)`, `(4, 3)`. -/
def smallCerts : List PairCert := [
"""

FOOTER = """
/-- Every certificate of the table passes the check. -/
theorem smallCerts_ok : ∀ c ∈ smallCerts, c.ok = true := by
  decide +kernel

/-- Every pair in the range has a certificate in the table. -/
theorem exists_smallCert : ∀ p, p < 16 → ∀ q, q < p →
    2 ≤ q ∧ Nat.Coprime p q ∧ ¬ (p = 3 ∧ q = 2) ∧ ¬ (p = 4 ∧ q = 3) →
    ∃ c ∈ smallCerts, c.p = p ∧ c.q = q := by
  decide +kernel

end RatBase

end PiFormula
"""


def main():
    write = len(sys.argv) > 1 and sys.argv[1] == "write"
    ps = pairs()
    certs = []
    n_rows = 0
    n_direct = 0
    seen_left = set()
    for p, q in ps:
        a, b, big_f, rows = make_cert(p, q)
        assert cert_ok(p, q, a, b, big_f, rows), (p, q)
        # the two ways to compute Phi_m(p, q) agree on every row
        cache = {}
        direct = 0
        for i, fm in enumerate(rows):
            m = 3 + i
            assert phi_n(fm, p, q) == phi_by_divisors(m, p, q, cache), (p, q, m)
            if (p, q, m) in LEFTOVER:
                seen_left.add((p, q, m))
                # a triple of the list fails the integer test even with this a/b (so it is needed
                # by this proof; that the size condition itself fails there is not claimed here)
                t = tot_f(fm)
                assert not direct_ok(b * (p + q) + 2 * a, b, phi_n(fm, p, q), t // 2, fm)
            elif tot_f(fm) <= big_f:
                direct += 1
        n_rows += len(rows)
        n_direct += direct
        certs.append((p, q, a, b, big_f, rows))
        print("%2d/%-2d  a/b = %d/%d  F = %2d  rows m = 3..%-3d  integer checks: %d"
              % (p, q, a, b, big_f, 2 + len(rows), direct))
    assert seen_left == LEFTOVER
    print("pairs: %d, rows: %d, integer checks: %d, all certificates pass"
          % (len(ps), n_rows, n_direct))
    if not write:
        return
    out = [HEADER % (len(ps), B, n_rows, n_direct)]
    lines = []
    for k, (p, q, a, b, big_f, rows) in enumerate(certs):
        last = k + 1 == len(certs)
        head = "  ⟨%d, %d, %d, %d, %d," % (p, q, a, b, big_f)
        if not rows:
            lines.append(head + " []⟩" + ("" if last else ","))
            continue
        lines.append(head)
        body = wrap([lean_row(fm) for fm in rows], "    ")
        body[0] = "    [" + body[0].lstrip()
        if len(body[0]) > 100:
            raise ValueError("line too long")
        body[-1] = body[-1] + "]⟩" + ("" if last else ",")
        if len(body[-1]) > 100:
            raise ValueError("line too long")
        lines.extend(body)
    lines.append("]")
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "..", "lean", "Pilean", "RatBase", "SizeSmallTable.lean")
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(out[0])
        f.write("\n".join(lines))
        f.write("\n")
        f.write(FOOTER)
    print("wrote lean/Pilean/RatBase/SizeSmallTable.lean")


if __name__ == "__main__":
    main()
