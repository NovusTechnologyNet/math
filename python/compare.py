"""Check the block method against the term-by-term method and time both.

    python compare.py <position> <count> [count ...] [--skip-old-above N]
"""
import sys
import time

import pi_blocks
import pi_window

if __name__ == "__main__":
    args = sys.argv[1:]
    skip_above = 10**18
    if "--skip-old-above" in args:
        i = args.index("--skip-old-above")
        skip_above = int(args[i + 1])
        del args[i:i + 2]
    n = int(args[0])
    print("position %d" % n)
    print("%10s %12s %12s %8s %7s" % ("digits", "term-by-term", "block", "speedup", "match"))
    for count in map(int, args[1:]):
        t = time.time()
        new, _ = pi_blocks.pi_hex(n, count)
        t_new = time.time() - t
        if count <= skip_above:
            t = time.time()
            old = pi_window.pi_hex(n, count)
            t_old = time.time() - t
            print("%10d %11.1fs %11.1fs %7.1fx %7s"
                  % (count, t_old, t_new, t_old / t_new, old == new), flush=True)
        else:
            print("%10d %12s %11.1fs %8s %7s" % (count, "-", t_new, "-", "-"), flush=True)
        print("           starts %s" % new[:24], flush=True)
