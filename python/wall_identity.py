"""Where the position cost comes from, checked numerically.

In the prime form, frac(2^m * pi) = sum over odd primes p of C_p / p (mod 1).
Working the algebra through for a prime p too large to have any multiple other
than itself in the head (p > la/3) gives a closed form with no loop at all:

    C_p = chi(p) * w * 2^m  (mod p),     chi(p) = +1 if p = 1 mod 4, else -1

    w = 2     for lb < p <= la
    w = 5/2   for lc < p <= lb
    w = 3     for la/3 < p <= lc

So each such prime contributes the fraction  chi(p) * w * 2^m / p  (mod 1): the
binary expansion of a fixed rational w/p, shifted m places. Moving the window
forward S bits multiplies every C_p by 2^S: each prime contributes a PERIODIC
bit stream (period dividing p-1), and the digits of pi far out are the carry-sum
of those streams. The "state" at position m is the list of all C_p, about 0.96*m
bits in total, and every window has to read all of it. That is the position cost.

This script checks the closed form against the coefficients the pipeline computes.
"""
import sys

import numpy as np

import pi_machin


def check(m, lo, hi, w_num, w_den, label):
    primes, acc = pi_machin.large_task((m, lo, hi))
    got = dict(zip(primes.tolist(), acc.tolist()))
    bad = 0
    count = 0
    for p in pi_machin.primes_between(lo, hi).tolist():
        chi = 1 if p % 4 == 1 else -1
        want = chi * w_num * pow(w_den, -1, p) * pow(2, m, p) % p
        count += 1
        if got.get(p, 0) != want:
            bad += 1
    print("%-22s primes %7d   mismatches %d" % (label, count, bad))
    return bad


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000
    m = 4 * n
    la, lb, lc, ld = pi_machin.head_limits(m)
    print("position %d (bit %d): la=%d lb=%d lc=%d ld=%d" % (n, m, la, lb, lc, ld))
    span = 300_000
    bad = check(m, lb + 10, min(la, lb + 10 + span), 2, 1, "lb < p <= la  (w=2)")
    bad += check(m, lc + 10, min(lb, lc + 10 + span), 5, 2, "lc < p <= lb  (w=5/2)")
    bad += check(m, la // 3 + 10, min(lc, la // 3 + 10 + span), 3, 1, "la/3 < p <= lc (w=3)")
    print("closed form holds" if bad == 0 else "CLOSED FORM FAILS")
