"""Windowed BBP: read any window of pi's hex digits without computing or storing
the digits before it.

    python pi_window.py <position> <digit_count>

Prints <digit_count> hex digits of pi starting right after hex position <position>
(position 0 -> 243F6A88...). Memory use is a few integers of about digit_count*4
bits each, no matter how far out the position is. Work is split across all CPU
cores; every chunk is independent, so it would split across machines the same way.

Uses pi = sum 16^-k * (4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6)).
"""
import sys
import time
from multiprocessing import Pool, cpu_count

GUARD = 64  # extra bits that absorb the rounding error of the truncated divisions


def chunk_sum(args):
    """Fractional part of sum_{k=lo}^{hi-1} 16^(n-k) * c/(8k+j) over all four j,
    scaled by 2^bits. Only terms with k <= n (the modular-exponent part)."""
    n, lo, hi, bits = args
    mask = (1 << bits) - 1
    s = 0
    for k in range(lo, hi):
        e = n - k
        d = 8 * k + 1
        s += 4 * ((pow(16, e, d) << bits) // d)
        d += 3
        s -= 2 * ((pow(16, e, d) << bits) // d)
        d += 1
        s -= (pow(16, e, d) << bits) // d
        d += 1
        s -= (pow(16, e, d) << bits) // d
        if not k & 0xFFF:
            s &= mask
    return s & mask


def tail_sum(n, bits):
    """Terms with k > n: plain shrinking fractions, about bits/4 of them."""
    s = 0
    k = n + 1
    while True:
        shift = bits - 4 * (k - n)
        if shift < 0:
            return s
        one = 1 << shift
        s += 4 * one // (8 * k + 1) - 2 * one // (8 * k + 4)
        s -= one // (8 * k + 5) + one // (8 * k + 6)
        k += 1


def pi_hex(n, count, workers=None):
    bits = 4 * count + GUARD
    workers = workers or cpu_count()
    step = max(1, (n + 1) // (workers * 8) + 1)
    jobs = [(n, lo, min(lo + step, n + 1), bits) for lo in range(0, n + 1, step)]
    if len(jobs) > 1 and workers > 1:
        with Pool(workers) as pool:
            parts = pool.map(chunk_sum, jobs)
    else:
        parts = [chunk_sum(j) for j in jobs]
    total = (sum(parts) + tail_sum(n, bits)) & ((1 << bits) - 1)
    return format(total >> GUARD, "0%dX" % count)


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 64
    t = time.time()
    digits = pi_hex(n, count)
    print(digits)
    print("position %d, %d hex digits, %.1fs, working state ~%d bytes per core"
          % (n, count, time.time() - t, (4 * count + GUARD) // 8 * 3), file=sys.stderr)
