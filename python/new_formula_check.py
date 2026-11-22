"""Check the new formula by actually extracting hex digits of pi with it.

Run:  python new_formula_check.py [hex position, default 1000000] [winners file]

The formula is   pi/4 = sum over k >= 1 of  rho(k) * 2^(-floor(k/2)) / k,
rho rational with period 120, read from pi_formula_120.json (written on first run from
the winners file produced by cheaper_fast.py).

Checks:
  1. the series sums to pi/4 to 1000 digits;
  2. digits of pi after hex position n, extracted term by term with this formula,
     equal those from the independent block-rational program (pi_blocks.py);
  3. the per-prime state the window algorithm needs, counted prime by prime, for
     Euler's formula and for the new one.
"""
import json
import os
import pickle
import sys
import time
from fractions import Fraction
from math import gcd, log2

from mpmath import mp, mpf, pi

from cheaper_search import N, UNITS, euler_pattern, level_table

HERE = os.path.dirname(os.path.abspath(__file__))
FORMULA = os.path.join(HERE, "pi_formula_120.json")
BITS = 192


def load_formula(winners_file):
    if not os.path.exists(FORMULA):
        winners = pickle.load(open(winners_file, "rb"))
        def key(p):
            nz = [x for x in p if x != 0]
            return (len(nz), max(x.denominator for x in nz), max(abs(x.numerator) for x in nz))
        best = min(winners, key=key)
        den = 1
        for x in best:
            den = den * x.denominator // gcd(den, x.denominator)
        data = {"statement": "pi/4 = sum_{k>=1} rho(k) * 2^(-floor(k/2)) / k,  rho(k) = numerators[k mod 120] / denominator",
                "period": N, "denominator": den, "numerators": [int(x * den) for x in best]}
        json.dump(data, open(FORMULA, "w"), indent=1)
    data = json.load(open(FORMULA))
    return [Fraction(a, data["denominator"]) for a in data["numerators"]]


def series_sum(rho, digits):
    mp.dps = digits + 20
    total, k = mpf(0), 1
    while k // 2 <= mp.prec + 40:
        r = rho[k % N]
        if r:
            total += mpf(r.numerator) / r.denominator / (mpf(k) * mpf(2) ** (k // 2))
        k += 1
    return total


def extract(rho, n, count=24):
    """Hex digits n+1 .. n+count of pi, from frac(2^m * S) with m = 4n + 2."""
    m = 4 * n + 2
    acc = 0
    mask = (1 << BITS) - 1
    k = 1
    while True:
        e = m - k // 2
        if e < -BITS - 8:
            break
        r = rho[k % N]
        if r:
            a, mod = r.numerator, r.denominator * k
            if e >= 0:
                x = (a % mod) * pow(2, e, mod) % mod
                acc += (x << BITS) // mod
            else:
                acc += (a << BITS) // (mod << -e) if a > 0 else -((-a << BITS) // (mod << -e))
        k += 1
    acc &= mask
    return "%0*X" % (BITS // 4, acc)[:count] if False else ("%0*X" % (BITS // 4, acc))[:count]


def state_bits(rho, m):
    """Sum of log2(p) over the primes that occur in a denominator of a term k <= 2m + 1."""
    limit = 2 * m + 1
    zeros = frozenset(k for k in range(N) if rho[k] == 0)
    lv = level_table(zeros)
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    total, count = 0.0, 0
    for p in range(7, limit + 1):
        if sieve[p] and p * lv[p % N] <= limit:
            total += log2(p)
            count += 1
    return total, count


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
    winners = sys.argv[2] if len(sys.argv) > 2 else ""
    rho = load_formula(winners)
    euler = euler_pattern(0)
    nz = [k for k in range(N) if rho[k] != 0]
    print("new formula: %d of 120 entries non-zero; common denominator %d"
          % (len(nz), max(r.denominator for r in rho)))
    zeros = frozenset(k for k in range(N) if rho[k] == 0)
    lv = level_table(zeros)
    print("  first multiplier s by class of primes modulo 4:  p = 1 (mod 4): %s   p = 3 (mod 4): %s"
          % (sorted({lv[c] for c in UNITS if c % 4 == 1}), sorted({lv[c] for c in UNITS if c % 4 == 3})))

    diff = abs(series_sum(rho, 1000) - pi / 4)
    print("1. |series - pi/4| = %s  (1000-digit sum)" % mp.nstr(diff, 3))

    t = time.time()
    new_digits = extract(rho, n)
    t_new = time.time() - t
    t = time.time()
    old_digits = extract(euler, n)
    t_old = time.time() - t
    print("2. hex digits of pi after position %d" % n)
    print("     new formula   : %s   (%.1f s, term by term in Python)" % (new_digits, t_new))
    print("     Euler's       : %s   (%.1f s)" % (old_digits, t_old))
    try:
        from pi_blocks import pi_hex
        ref = pi_hex(n, 24, None)[0]
        print("     pi_blocks.py  : %s" % ref)
        print("     all three agree on the first 20 digits: %s" % (new_digits[:20] == old_digits[:20] == ref[:20]))
    except Exception as exc:                                   # the reference program is optional
        print("     (pi_blocks.py not available: %s)" % exc)
        print("     the two formulas agree on the first 20 digits: %s" % (new_digits[:20] == old_digits[:20]))

    m = 4 * n + 2
    print("3. per-prime state for a window at bit %d (primes that occur in a denominator):" % m)
    for label, pat in (("Euler's", euler), ("new", rho)):
        bits, count = state_bits(pat, m)
        print("     %-8s %9d primes, %12.0f bits = %.4f bits per bit of position" % (label, count, bits, bits / m))


if __name__ == "__main__":
    main()
