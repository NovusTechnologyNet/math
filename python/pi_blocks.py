"""Block-rational digit extraction for pi.

    python pi_blocks.py <position> <digit_count> [workers]

Prints <digit_count> hex digits of pi starting right after hex position <position>.

Idea
----
Classic BBP handles the series one term at a time: for every term k it reduces
16^(n-k) modulo a tiny denominator, then divides to the window's precision. A
window of B digits at position n therefore costs about n * B.

Here the terms are first fused, by binary splitting, into blocks. A block of m
consecutive terms becomes ONE exact fraction P/Q, where Q is about as big as the
window itself. The power of 16 is then reduced modulo that big Q once per block:

    frac(16^e * P/Q) = ((16^e mod Q) * P mod Q) / Q

So one modular exponentiation and one division serve m terms instead of one.
With fast multiplication a window of B digits at position n costs about
n * polylog(n), nearly independent of B, using memory proportional to B.
Reading all N digits of pi with memory S then costs about N^2 / S: a dial that
runs from plain BBP (tiny memory, N^2 time) to full-size methods (memory N, time ~N).

Every block is independent and stateless, so blocks can run on any number of
cores or machines, in any order, and a lost block is simply redone.

Uses pi = sum_k 16^-k * (120k^2+151k+47) / ((8k+1)(8k+5)(2k+1)(4k+3)).
"""
import sys
import time
from multiprocessing import Pool, cpu_count

try:
    from gmpy2 import mpz, powmod
except ImportError:  # works without gmpy2, just far slower on big windows
    mpz, powmod = int, pow

GUARD = 64


def split(a, b):
    """Exact P, Q with  sum_{k=a}^{b-1} 16^(b-1-k) * p(k)/q(k) = P/Q."""
    if b - a == 1:
        k = a
        return (mpz(120 * k * k + 151 * k + 47),
                mpz((8 * k + 1) * (8 * k + 5) * (2 * k + 1) * (4 * k + 3)))
    c = (a + b) // 2
    pl, ql = split(a, c)
    pr, qr = split(c, b)
    return ((pl * qr) << (4 * (b - c))) + pr * ql, ql * qr


def block(args):
    """Contribution of terms a..b-1 to frac(16^n * pi), scaled by 2^bits."""
    n, a, b, bits = args
    p, q = split(a, b)
    e = n - (b - 1)
    if e >= 0:
        r = powmod(mpz(16), e, q) * (p % q) % q
        return int((r << bits) // q)
    sh = bits + 4 * e
    return int((p << sh) // q if sh >= 0 else (p >> -sh) // q)


def plan(n, bits):
    """Cut the terms into blocks whose fused denominator is about `bits` long."""
    jobs = []
    end = n + 1 + bits // 4 + 2          # terms past this are below one unit
    a = 0
    while a < end:
        per_term = 9 + 4 * max(a, 2).bit_length()
        m = max(1, bits // per_term)
        stop = n + 1 if a <= n else end  # keep one boundary exactly at n+1
        b = min(a + m, stop)
        jobs.append((n, a, b, bits))
        a = b
    return jobs


def pi_hex(n, count, workers=None):
    bits = 4 * count + GUARD
    jobs = plan(n, bits)
    workers = workers or cpu_count()
    if workers > 1 and len(jobs) > 1:
        with Pool(workers) as pool:
            total = sum(pool.imap_unordered(block, jobs, chunksize=1))
    else:
        total = sum(block(j) for j in jobs)
    total &= (1 << bits) - 1
    return format(total >> GUARD, "0%dX" % count), len(jobs)


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 64
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else None
    t = time.time()
    digits, nblocks = pi_hex(n, count, workers)
    print(digits)
    print("position %d, %d hex digits, %d blocks, %.1fs"
          % (n, count, nblocks, time.time() - t), file=sys.stderr)
