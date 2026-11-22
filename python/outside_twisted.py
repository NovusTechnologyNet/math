"""What do the NEW relations of F_n produce?  Series for irrational multiples of pi.

Run:  python outside_twisted.py <n> <P> [bits per entry]     (needs python-flint)

Same lattice method as outside_probe.py, but the targets are

    pi * 2^(a/n) * beta_b,     a = 0..n-1,   beta_b = 2 cos(2 pi b / M)  (a basis of the
                                              real cyclotomic field of level M = lcm(P, 8)),

so it finds every period-P rational pattern whose series is pi times a number of
Q(2^(1/n), zeta_M) of that shape.  It then tests the component lemma:

    the part of the pattern on k = j (mod n1) sums to exactly the part of the value
    that carries 2^(a/n) with a = j (mod n1)          (n1 = n/2 for even n, n for odd n).

For j = 0 this is the statement used in the findings file: the sub-series on
k = 0 (mod n1), which is an F_2 (or F_1) series, carries the whole rational part.
"""
import sys
import time
from math import gcd

from flint import fmpz_mat
from mpmath import mp, mpf, pi, cos

from outside_probe import class_sums


def phi(m):
    return sum(1 for a in range(1, m + 1) if gcd(a, m) == 1)


def main():
    n, P = int(sys.argv[1]), int(sys.argv[2])
    bits_per = int(sys.argv[3]) if len(sys.argv) > 3 else 28
    M = P * 8 // gcd(P, 8)
    nb = phi(M) // 2
    ntar = n * nb
    total = ntar + P
    Wc = bits_per * total + 256
    W = Wc + 256
    mp.prec = W + 64
    S = class_sums(n, P, W)
    def fx(v):
        return int(mp.floor(v * mpf(2) ** W + mpf(1) / 2))
    targets, label = [], []
    for a in range(n):
        for b in range(nb):
            beta = mpf(1) if b == 0 else 2 * cos(2 * pi * b / M)
            targets.append(fx(pi * mpf(2) ** (mpf(a) / n) * beta))
            label.append((a, b))
    vals = targets + S
    rows = []
    for i, v in enumerate(vals):
        row = [0] * (total + 1)
        row[i] = 1
        row[total] = v >> (W - Wc)
        rows.append(row)
    t0 = time.time()
    red = fmpz_mat(rows).lll()
    rels = []
    for i in range(total):
        coef = [int(red[i, j]) for j in range(total)]
        if abs(sum(c * v for c, v in zip(coef, vals))) < (sum(abs(c) for c in coef) + 1) << 80:
            rels.append(coef)
    n1 = n // 2 if n % 2 == 0 else n
    only_targets = sum(1 for r in rels if not any(r[ntar:]))
    pure_rational = sum(1 for r in rels if any(r[ntar:]) and not any(c for c, (a, b) in zip(r[:ntar], label) if (a, b) != (0, 0)))
    twisted = [r for r in rels if any(c for c, (a, b) in zip(r[:ntar], label) if a % n1)]
    off = sum(1 for r in rels if any(c for j, c in enumerate(r[ntar:], start=1) if j % n1))
    print("n = %d, P = %d: %d targets (pi * 2^(a/%d) * real cyclotomic of level %d) + %d class sums; LLL %.0f s"
          % (n, P, ntar, n, M, P, time.time() - t0))
    print("  relations: %d   (among targets only: %d;  value in Q*pi or zero: %d)" % (len(rels), only_targets, pure_rational))
    print("  basis relations whose value involves 2^(a/%d) with a != 0 (mod %d): %d;   with entries off k = 0 (mod %d): %d"
          % (n, n1, len(twisted), n1, off))
    worst = 0
    for r in rels:
        for j in range(n1):
            part = sum(c * vals[ntar + k - 1] for k, c in enumerate(r[ntar:], start=1) if k % n1 == j)
            part += sum(c * vals[i] for i, (c, (a, b)) in enumerate(zip(r[:ntar], label)) if a % n1 == j)
            worst = max(worst, abs(part))
    print("  component lemma: largest mismatch 2^%d   (noise level about 2^%d)" % (worst.bit_length() - W, 90 - W))
    shown = [r for r in rels if any(c for j, c in enumerate(r[ntar:], start=1) if j % n1)]
    for r in shown[:3]:
        val = " ".join("%+d*pi*2^(%d/%d)*b%d" % (-c, a, n, b) for c, (a, b) in zip(r[:ntar], label) if c)
        sup = sorted({k % n1 for k, c in enumerate(r[ntar:], start=1) if c})
        nz = sum(1 for c in r[ntar:] if c)
        print("    example: %d non-zero entries on classes k mod %d in %s;  value = %s   (b_j = 2cos(2 pi j/%d))"
              % (nz, n1, sup, val, M))
        # independent check of this example by direct summation at 60 digits
        mp.dps = 60
        direct = mpf(0)
        k = 1
        while k // n <= 260:
            c = r[ntar + (k - 1) % P]
            if c:
                direct += mpf(c) / (mpf(k) * mpf(2) ** (k // n))
            k += 1
        want = -sum(mpf(c) * pi * mpf(2) ** (mpf(a) / n) * (mpf(1) if b == 0 else 2 * cos(2 * pi * b / M))
                    for c, (a, b) in zip(r[:ntar], label))
        print("             direct sum - value = %s" % mp.nstr(direct - want, 3))
        # the clean component: the pattern restricted to one class k = j (mod n1), j != 0
        for j in range(1, n1):
            pat = {k: c for k, c in enumerate(r[ntar:], start=1) if c and k % n1 == j}
            if not pat or P > 48:
                continue
            part, k = mpf(0), 1
            while k // n <= 260:
                c = pat.get((k - 1) % P + 1, 0)
                if c:
                    part += mpf(c) / (mpf(k) * mpf(2) ** (k // n))
                k += 1
            want_j = -sum(mpf(c) * pi * mpf(2) ** (mpf(a) / n) * (mpf(1) if b == 0 else 2 * cos(2 * pi * b / M))
                          for c, (a, b) in zip(r[:ntar], label) if a % n1 == j)
            comp = " ".join("%+d*pi*2^(%d/%d)*b%d" % (-c, a, n, b)
                            for c, (a, b) in zip(r[:ntar], label) if c and a % n1 == j)
            print("             class k = %d (mod %d) alone: rho = %s  (period %d)" % (j, n1, pat, P))
            print("               sums to %s;  direct sum - that = %s" % (comp or "0", mp.nstr(part - want_j, 3)))
        mp.prec = W + 64


if __name__ == "__main__":
    main()
