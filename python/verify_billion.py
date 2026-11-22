"""One million hex digits of pi starting after hex position one billion, with checks.

Check 1: the first digits against Bailey's published value at position 10^9
         (85895585A0428B, which starts one digit earlier).
Check 2: an overlapping second run that starts 32 digits before the window's end;
         its first 32 digits must equal the window's last 32.
"""
import time

import pi_machin

if __name__ == "__main__":
    n, count = 1_000_000_000, 1_000_000
    st = {}
    t = time.time()
    digits = pi_machin.pi_hex(n, count, stats=st)
    print("position %d, %d digits: %.1fs (word %.1f, head %.1f, tail %.1f)"
          % (n, count, time.time() - t, st["t_word"], st["t_head"], st["t_tail"]), flush=True)
    print("fractions %d, fraction data %.3g bits (BBP prime form %.3g, BBP term form %.3g)"
          % (st["fractions"], st["den_bits"], st["bbp_prime_bits"], st["naive_bits"]), flush=True)
    print("starts   %s" % digits[:24], flush=True)
    print("published 85895585A0428B -> match %s" % (digits[:13] == "5895585A0428B"), flush=True)
    with open("pi_hex_1e9_1M.txt", "w") as f:
        f.write(digits)
    t = time.time()
    tail = pi_machin.pi_hex(n + count - 32, 64)
    print("ends     %s" % digits[-32:])
    print("overlap  %s -> match %s (%.1fs)" % (tail[:32], tail[:32] == digits[-32:], time.time() - t))
