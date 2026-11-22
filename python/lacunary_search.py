"""Search for a formula for pi that would remove the position cost.

What such a formula must look like
----------------------------------
Reading a window at bit position m costs one unit per series term that is still
"active" there. Every known digit-extraction formula for pi gains a fixed number
of bits per term, so about m terms are active: cost proportional to position.

A formula of the shape

    pi = sum over k of  a_k / ( q_k * 2^(g(k)) )

with small integers a_k, q_k (polynomial in k) but an exponent g(k) that grows
FASTER than linearly (k^2, k(k+1)/2, ...) would have only about sqrt(m) active
terms: reading a window would cost about sqrt(position). Nothing known rules
such a formula out, and none is known.

BBP itself was found by exactly this kind of computer search (integer relations,
PSLQ). This script runs that search over series with quadratic exponents, after a
positive control showing the search does find the BBP formula in its own family.
"""
import sys
import time

from mpmath import mp, mpf, pi, log, pslq

mp.dps = int(sys.argv[1]) if len(sys.argv) > 1 else 400
MAXCOEFF = 10 ** 6

EXPONENTS = {
    "k^2": lambda k: k * k,
    "k(k+1)/2": lambda k: k * (k + 1) // 2,
    "k(k+1)": lambda k: k * (k + 1),
    "2k^2": lambda k: 2 * k * k,
    "k(3k-1)/2": lambda k: k * (3 * k - 1) // 2,
    "k(3k+1)/2": lambda k: k * (3 * k + 1) // 2,
}
WEIGHTS = {
    "1": lambda k: 1,
    "1/(k+1)": lambda k: k + 1,
    "1/(2k+1)": lambda k: 2 * k + 1,
    "1/(4k+1)": lambda k: 4 * k + 1,
    "1/(4k+3)": lambda k: 4 * k + 3,
    "1/(3k+1)": lambda k: 3 * k + 1,
    "1/(3k+2)": lambda k: 3 * k + 2,
}


def series(expo, den, alternating):
    s, k = mpf(0), 0
    while True:
        e = expo(k)
        if e > mp.prec + 40:
            return s
        term = mpf(1) / (mpf(den(k)) * mpf(2) ** e)
        s += -term if (alternating and k % 2) else term
        k += 1


def hunt(label, names, values):
    t = time.time()
    rel = pslq(values, maxcoeff=MAXCOEFF, maxsteps=10 ** 6)
    took = time.time() - t
    if rel is None:
        print("%-34s %3d constants  no relation with coefficients up to %d  (%.0fs)"
              % (label, len(values), MAXCOEFF, took))
        return None
    shown = " ".join("%+d*[%s]" % (c, n) for c, n in zip(rel, names) if c)
    print("%-34s RELATION: %s  (%.0fs)" % (label, shown, took))
    return rel


if __name__ == "__main__":
    print("precision: %d decimal digits" % mp.dps)

    # ---- positive control: the search must rediscover BBP in the BBP family
    def bbp(j):
        s, k = mpf(0), 0
        while 4 * k <= mp.prec + 40:
            s += mpf(1) / (mpf(8 * k + j) * mpf(16) ** k)
            k += 1
        return s
    hunt("control: BBP family", ["pi"] + ["S%d" % j for j in range(1, 8)],
         [pi] + [bbp(j) for j in range(1, 8)])

    # ---- the hunt: one run per exponent law, all weights, both sign patterns
    found = []
    for ename, expo in EXPONENTS.items():
        names, values = ["pi", "log2", "1"], [+pi, log(2), mpf(1)]
        for wname, den in WEIGHTS.items():
            for alt in (False, True):
                names.append("%s%s/2^(%s)" % ("(-1)^k " if alt else "", wname, ename))
                values.append(series(expo, den, alt))
        rel = hunt("exponent " + ename, names, values)
        if rel is not None and rel[0] != 0:
            found.append((ename, rel))

    # ---- one combined run across exponent laws with the two simplest weights
    names, values = ["pi", "log2", "1"], [+pi, log(2), mpf(1)]
    for ename, expo in EXPONENTS.items():
        for wname in ("1", "1/(2k+1)"):
            for alt in (False, True):
                names.append("%s%s/2^(%s)" % ("(-1)^k " if alt else "", wname, ename))
                values.append(series(expo, WEIGHTS[wname], alt))
    rel = hunt("all exponent laws together", names, values)
    if rel is not None and rel[0] != 0:
        found.append(("combined", rel))

    print("formulas for pi found: %d" % len(found))
