"""Probe of the gap in the wider theorem: series with ANY periodic rational pattern.

Theorem B covers coefficient patterns that are invariant under the Galois group.
The most general binary degree-1 BBP-type series is

    sum over k >= 1 of  r(k) * 2^(-floor(k/2)) / k,      r rational, periodic (period P).

It is a rational combination of the residue-class series
    S_j = sum over k = j (mod P) of 2^(-floor(k/2)) / k.

Its speed is half the smallest gcd(j, P) over the classes j that are used. So the
question "is there a formula for pi faster than Euler's 3/2?" becomes:

    is pi a rational combination of the S_j with gcd(j, P) >= 4 ?

This script asks that question with an integer-relation search (PSLQ), for the
periods it can afford, after a control run that must find a known formula.
A null result here is evidence, not proof.
"""
import sys
import time
from math import gcd

from mpmath import mp, mpf, pi, pslq


def class_series(j, period):
    s, k = mpf(0), j
    while k // 2 <= mp.prec + 30:
        s += mpf(1) / (mpf(k) * mpf(2) ** (k // 2))
        k += period
    return s


def hunt(period, min_gcd, maxcoeff=10 ** 6):
    classes = [j for j in range(1, period + 1) if gcd(j, period) >= min_gcd]
    vals = {j: class_series(j, period) for j in classes}
    names = list(classes)
    t = time.time()
    dropped = 0
    while names:
        rel = pslq([+pi] + [vals[j] for j in names], maxcoeff=maxcoeff, maxsteps=10 ** 7)
        if rel is None:
            print("period %3d, classes with gcd >= %d: %2d series; pi is NOT a combination "
                  "(coefficients up to %d), after removing %d null relations  [%.0fs]"
                  % (period, min_gcd, len(classes), maxcoeff, dropped, time.time() - t))
            return None
        if rel[0] != 0:
            used = [(c, j) for c, j in zip(rel[1:], names) if c]
            print("period %3d, classes with gcd >= %d: FOUND  %d*pi = %s   [%.0fs]"
                  % (period, min_gcd, -rel[0],
                     " ".join("%+d*S[%d]" % (c, j) for c, j in used), time.time() - t))
            print("      slowest class used: gcd %d (speed %.1f)"
                  % (min(gcd(j, period) for _, j in used), min(gcd(j, period) for _, j in used) / 2))
            return rel
        # a null relation: remove one series it involves and look again
        victim = max((abs(c), j) for c, j in zip(rel[1:], names) if c)[1]
        names.remove(victim)
        dropped += 1
    return None


if __name__ == "__main__":
    mp.dps = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    print("precision %d digits" % mp.dps)
    hunt(8, 1)          # control: period 8 contains the original 1995 formula
    hunt(40, 2)         # control: contains 2atan(1/2) - atan(1/7), speed 1
    hunt(24, 4)         # the question, period 24
    hunt(40, 4)         # the question, period 40
