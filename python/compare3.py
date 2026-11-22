"""Faster-formula prime form (pi_machin) versus the BBP prime form (pi_primes).

    python compare3.py <position> <count> [count ...] [--solo] [--end-check]

--solo       run only pi_machin (for positions where pi_primes is too slow)
--end-check  also verify the last 32 digits against the independent
             term-by-term method (pi_window), run at the far end of the window
"""
import sys
import time

import pi_machin
import pi_primes
import pi_window

if __name__ == "__main__":
    args = sys.argv[1:]
    solo = "--solo" in args
    end_check = "--end-check" in args
    args = [a for a in args if not a.startswith("--")]
    n = int(args[0])
    print("position %d" % n)
    for count in map(int, args[1:]):
        st = {}
        t = time.time()
        new = pi_machin.pi_hex(n, count, stats=st)
        t_new = time.time() - t
        line = "%9d digits | new formula %6.1fs (word %.1f, head %.1f, tail %.1f)" % (
            count, t_new, st["t_word"], st["t_head"], st["t_tail"])
        if not solo:
            so = {}
            t = time.time()
            old = pi_primes.pi_hex(n, count, stats=so)
            t_old = time.time() - t
            line += " | BBP prime form %6.1fs (word %.1f, head %.1f, tail %.1f) | match %s" % (
                t_old, so["t_word"], so["t_head"], so["t_tail"], old == new)
        print(line, flush=True)
        print("    fraction data %.3g bits (BBP prime form %.3g, BBP term form %.3g); starts %s"
              % (st["den_bits"], st["bbp_prime_bits"], st["naive_bits"], new[:16]), flush=True)
        if end_check:
            t = time.time()
            end = pi_window.pi_hex(n + count - 32, 32)
            print("    last 32 digits %s | independent check %s (%.0fs)"
                  % (new[-32:], end == new[-32:], time.time() - t), flush=True)
