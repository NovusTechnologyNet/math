"""Prime form versus block form: same digits, how much less work?

    python compare2.py <position> <count> [count ...] [--no-block]
"""
import sys
import time

import pi_blocks
import pi_primes

if __name__ == "__main__":
    args = sys.argv[1:]
    run_block = "--no-block" not in args
    args = [a for a in args if a != "--no-block"]
    n = int(args[0])
    print("position %d" % n)
    for count in map(int, args[1:]):
        st = {}
        t = time.time()
        new = pi_primes.pi_hex(n, count, stats=st)
        t_new = time.time() - t
        line = "%9d digits | prime form %6.1fs (word %.1f, head %.1f, tail %.1f)" % (
            count, t_new, st["t_word"], st["t_head"], st["t_tail"])
        if run_block:
            t = time.time()
            old, _ = pi_blocks.pi_hex(n, count)
            t_old = time.time() - t
            line += " | block form %6.1fs | match %s" % (t_old, old == new)
        print(line, flush=True)
        print("    fraction data: %.3g bits prime form, %.3g bits term form (%.1fx smaller); starts %s"
              % (st["den_bits"], st["naive_bits"], st["naive_bits"] / st["den_bits"], new[:16]),
              flush=True)
