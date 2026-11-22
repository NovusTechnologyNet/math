"""Prime-form digit extraction for pi, built on  pi/4 = 2*atan(1/3) + atan(1/7).

    python pi_machin.py <position> <digit_count> [workers]

Prints <digit_count> hex digits of pi starting right after hex position <position>.

Why this formula
----------------
In the prime form (see pi_primes.py) the size of the fraction data depends only on
the largest denominator the formula reaches, i.e. on its slowest series. BBP needs
denominators up to 2 per bit of position; this formula needs only 2/3 per bit.

Both arctangents have power-of-two series (3+i = 4-(1-i), 7+i = 8-(1-i)), giving,
over ODD d only and with t = (d-1)/2:

    pi =  sum_d s1(d) * ( 2^(1-3t) + 2^(-1-5t) ) / d
        + sum_d s2(d) * ( 2^(-1-6t) + 2^(-4-10t) ) / d

    s1(d) = +1 if d mod 8 in {1,3} else -1;   s2(d) = +1 if d mod 4 == 1 else -1

Four series, called a, b, c, d below, with exponents  m + E0 - C*t  after scaling
by 2^m (m = bit position). Terms whose exponent is >= 0 form the head and are
reduced to one fraction per prime; the rest is a short convergent tail.

Word stage tricks (all exact):
  * 2^-t over the multiples of one prime is a geometric sequence, built by doubling.
  * For a large prime p and d = p*j, Fermat gives 2^-t = (2|p) * (1/2)^((j-1)/2),
    so stepping j -> j+2 is one multiplication by 1/2.
  * Cofactor inverses come from a product-tree batch inversion (small primes) or
    from the identity 1/j = (1 + p*(-1/p mod j)) / j (large primes).
"""
import sys
import time
from math import isqrt, log2
from multiprocessing import Pool, cpu_count

import numpy as np
from gmpy2 import mpz

import pi_blocks
from pi_primes import odd_primes_upto, pow2, powmod, primes_between, sum_block

U = np.uint64
GUARD = 64
CHUNK = 1 << 17          # multiples handled per numpy pass (stays in cache)
TASK = 1 << 20           # multiples per worker task
MIN_N = 2000
MIN_BLOCK_BITS = 1 << 18  # smallest head block, in bits of denominator
MAX_BLOCKS = 20000        # cap on head blocks, whatever the window size

#          C  E0  sign kind      exponent of series at t is  m + E0 - C*t
SERIES = ((3, 1, 1), (5, -1, 1), (6, -1, 2), (10, -4, 2))


def head_limits(m):
    """Largest odd d in the head of each series (exponent still >= 0)."""
    return tuple(2 * ((m + e0) // c) + 1 for c, e0, _ in SERIES)


# ---------------------------------------------------------------- word-stage helpers
def geometric(first, ratio, count, q):
    """first * ratio^i mod q for i < count, built by doubling."""
    out = np.empty(count, dtype=U)
    out[0] = first
    filled, rp = 1, ratio
    while filled < count:
        take = min(filled, count - filled)
        out[filled:filled + take] = out[:take] * U(rp) % U(q)
        filled += take
        rp = rp * rp % q
    return out


def batch_inverse(x, q):
    """Elementwise inverse mod q through a product tree (about 3 mults each)."""
    n = x.size
    levels = [x]
    while levels[-1].size > 1:
        a = levels[-1]
        if a.size % 2:
            a = np.append(a, U(1))
            levels[-1] = a
        levels.append(a[0::2] * a[1::2] % U(q))
    inv = np.array([pow(int(levels[-1][0]), -1, q)], dtype=U)
    for a in reversed(levels[:-1]):
        inv = inv[:a.size // 2]                        # drop the padding slot above
        nxt = np.empty(a.size, dtype=U)
        nxt[0::2] = inv * a[1::2] % U(q)
        nxt[1::2] = inv * a[0::2] % U(q)
        inv = nxt
    return inv[:n]


def count_le(jmax, j0, cnt):
    """How many of j0, j0+2, ... (cnt values) are <= jmax."""
    return 0 if jmax < j0 else min(cnt, (jmax - j0) // 2 + 1)


def euler_phi(j):
    r, x, f = j, j, 3
    while f * f <= x:
        if x % f == 0:
            while x % f == 0:
                x //= f
            r -= r // f
        f += 2
    if x > 1:
        r -= r // x
    return r


def inverse_of_small(j, ps):
    """j^-1 modulo each prime in ps (every prime exceeds j)."""
    r = ps % U(j)
    e = euler_phi(j) - 1
    if j < ps.size:
        rinv = powmod(np.arange(j, dtype=U), e, j)[r.astype(np.intp)]
    else:
        rinv = powmod(r, e, j)
    k = (U(j) - rinv) % U(j)
    return (U(1) + ps * k) // U(j)


# ---------------------------------------------------------------- stage A, small primes
def small_task(args):
    """Items: prime p, modulus q = p^E, first odd cofactor j0, how many cofactors."""
    m, items = args
    la, lb, lc, ld = head_limits(m)
    out = []
    for p, q, j0, cnt in items:
        uq = U(q)
        phi = q // p * (p - 1)
        h = (q + 1) // 2                               # 1/2 mod q
        big = pow(2, m, q)
        k1, k2, k4 = 2 * big % q, big * h % q, big * pow(h, 4, q) % q
        j = np.arange(j0, j0 + 2 * cnt, 2, dtype=U)
        d = j * U(p)
        g = geometric(pow(h, (p * j0 - 1) // 2 % phi, q), pow(h, p % phi, q), cnt, q)
        g2 = g * g % uq
        g3 = g2 * g % uq
        x = g3 * U(k1) % uq                            # series a: every d here
        nb = count_le(lb // p, j0, cnt)
        if nb:
            g5 = g3[:nb] * g2[:nb] % uq
            x[:nb] = (x[:nb] + g5 * U(k2) % uq) % uq   # series b
        r8 = d & U(7)
        x = np.where((r8 == 1) | (r8 == 3), x, uq - x)
        nc = count_le(lc // p, j0, cnt)
        if nc:
            y = g3[:nc] * g3[:nc] % uq * U(k2) % uq    # series c
            nd = count_le(ld // p, j0, cnt)
            if nd:
                y[:nd] = (y[:nd] + g5[:nd] * g5[:nd] % uq * U(k4) % uq) % uq   # series d
            y = np.where((d[:nc] & U(3)) == 1, y, uq - y)
            x[:nc] += y
        x %= uq
        # cofactor u = d / p^v and the scale p^(E-v)
        u = j.copy()
        mult = u % U(p) == 0
        if mult.any():
            pv = np.full(cnt, p, dtype=U)
            while mult.any():
                u[mult] //= U(p)
                pv[mult] *= U(p)
                mult = u % U(p) == 0
            scale = uq // pv
        else:
            scale = U(q // p)
        c = x * batch_inverse(u % uq, q) % uq
        c = c * scale % uq
        out.append((p, int(c.sum()) % q))
    return out


def small_plan(m, limit):
    la = head_limits(m)[0]
    tasks, cur, load = [], [], 0
    for p in odd_primes_upto(limit):
        q = p
        while q * p <= la:
            q *= p
        total = (la // p + 1) // 2                     # odd cofactors 1 .. la//p
        done = 0
        while done < total:
            cnt = min(CHUNK, total - done)
            cur.append((p, q, 1 + 2 * done, cnt))
            done += cnt
            load += cnt + 300
            if load >= TASK:
                tasks.append((m, cur))
                cur, load = [], 0
    if cur:
        tasks.append((m, cur))
    return tasks


# ---------------------------------------------------------------- stage A, large primes
def large_task(args):
    """All primes in (lo, hi]; each exceeds sqrt(limit), so it divides d only once."""
    m, lo, hi = args
    la, lb, lc, ld = head_limits(m)
    p = primes_between(lo, hi)
    acc = np.zeros(p.shape, dtype=U)
    if p.size == 0:
        return p, acc
    h = (p + U(1)) >> U(1)                              # 1/2 mod p
    big = pow2(U(m) % (p - U(1)), p)                    # 2^m mod p
    k1 = big * U(2) % p
    k2 = big * h % p
    h2 = h * h % p
    k4 = big * (h2 * h2 % p) % p
    r8 = p & U(7)
    g_all = np.where((r8 == 1) | (r8 == 7), U(1), p - U(1))    # (2|p), i.e. 2^-t at j = 1
    j = 1
    jmax = la // int(p[0])
    while j <= jmax:
        na = int(np.searchsorted(p, la // j, side="right"))
        if na == 0:
            break
        ps, g = p[:na], g_all[:na]
        g2 = g * g % ps
        g3 = g2 * g % ps
        x = g3 * k1[:na] % ps
        nb = int(np.searchsorted(p, lb // j, side="right"))
        if nb:
            pb = p[:nb]
            g5 = g3[:nb] * g2[:nb] % pb
            x[:nb] = (x[:nb] + g5 * k2[:nb] % pb) % pb
        d = ps * U(j)
        r8 = d & U(7)
        x = np.where((r8 == 1) | (r8 == 3), x, ps - x)
        nc = int(np.searchsorted(p, lc // j, side="right"))
        if nc:
            pc = p[:nc]
            y = g3[:nc] * g3[:nc] % pc * k2[:nc] % pc
            nd = int(np.searchsorted(p, ld // j, side="right"))
            if nd:
                pd = p[:nd]
                y[:nd] = (y[:nd] + g5[:nd] * g5[:nd] % pd * k4[:nd] % pd) % pd
            y = np.where((d[:nc] & U(3)) == 1, y, pc - y)
            x[:nc] += y
        x %= ps
        if j > 1:
            x = x * inverse_of_small(j, ps) % ps
        acc[:na] = (acc[:na] + x) % ps
        g_all[:na] = g * h[:na] % ps                    # step j -> j + 2
        j += 2
    keep = acc != 0
    return p[keep], acc[keep]


def large_plan(m, limit):
    la = head_limits(m)[0]
    tasks, lo = [], limit
    while lo < la:
        hi = min(la, max(lo + 1000, int(lo * 1.15)))
        tasks.append((m, lo, hi))
        lo = hi
    return tasks


# ---------------------------------------------------------------- tail
def tail_split(c, kind, a, b):
    """Exact P, Q with  sum_{t=a}^{b-1} sign(t) * 2^(c*(b-1-t)) / (2t+1) = P/Q."""
    if b - a == 1:
        plus = (a % 4 < 2) if kind == 1 else (a % 2 == 0)
        return mpz(1 if plus else -1), mpz(2 * a + 1)
    mid = (a + b) // 2
    pl, ql = tail_split(c, kind, a, mid)
    pr, qr = tail_split(c, kind, mid, b)
    return ((pl * qr) << (c * (b - mid))) + pr * ql, ql * qr


def tail_block(args):
    m, c, e0, kind, a, b, bits = args
    p, q = tail_split(c, kind, a, b)
    sh = bits + m + e0 - c * (b - 1)
    return int((p << sh) // q if sh >= 0 else (p >> -sh) // q)


def tail_plan(m, bits):
    jobs = []
    for c, e0, kind in SERIES:
        a = (m + e0) // c + 1                          # first t with negative exponent
        end = (m + e0 + bits + 2) // c + 2
        while a < end:
            step = max(1, bits // max(2, (2 * a + 1).bit_length()))
            b = min(a + step, end)
            jobs.append((m, c, e0, kind, a, b, bits))
            a = b
    return jobs


# ---------------------------------------------------------------- driver
def pi_hex(n, count, workers=None, stats=None):
    m = 4 * n
    la = head_limits(m)[0]
    if n < MIN_N or la >= 1 << 32:
        return pi_blocks.pi_hex(n, count, workers)[0]
    bits = 4 * count + GUARD
    workers = workers or cpu_count()
    limit = min(la, max(isqrt(la) + 1, int(la ** 0.57)))
    t0 = time.time()
    with Pool(workers) as pool:
        # ---- stage A
        small = {}
        for res in pool.imap_unordered(small_task, small_plan(m, limit)):
            for p, v in res:
                small[p] = small.get(p, 0) + v
        nums, dens = [], []
        for p, v in small.items():
            q = p
            while q * p <= la:
                q *= p
            if v % q:
                nums.append(v % q)
                dens.append(q)
        parts_n = [np.array(nums, dtype=U)]
        parts_d = [np.array(dens, dtype=U)]
        for pr, acc in pool.imap_unordered(large_task, large_plan(m, limit)):
            parts_d.append(pr)
            parts_n.append(acc)
        nums = np.concatenate(parts_n)
        dens = np.concatenate(parts_d)
        del parts_n, parts_d
        t1 = time.time()
        # ---- stage B
        size = np.cumsum(np.log2(dens.astype(np.float64)))
        total_bits = float(size[-1])
        # blocks of about `bits` bits of denominator, but never tiny: a small window
        # would otherwise be cut into millions of blocks
        per = max(bits, MIN_BLOCK_BITS, int(total_bits / MAX_BLOCKS) + 1)
        cuts = np.searchsorted(size, np.arange(per, total_bits, per)).tolist()
        del size
        edges = [0] + cuts + [len(dens)]
        jobs = [(nums[a:b], dens[a:b], bits) for a, b in zip(edges, edges[1:]) if b > a]
        total = sum(pool.imap_unordered(sum_block, jobs))
        t2 = time.time()
        total += sum(pool.imap_unordered(tail_block, tail_plan(m, bits)))
        t3 = time.time()
    total &= (1 << bits) - 1
    if stats is not None:
        naive = n * (2 * log2(8 * n) + log2(2 * n) + log2(4 * n) - 4 * 1.4427)
        stats.update(fractions=len(dens), den_bits=total_bits, bbp_prime_bits=8.66 * n,
                     naive_bits=naive, blocks=len(jobs),
                     t_word=t1 - t0, t_head=t2 - t1, t_tail=t3 - t2)
    return format(total >> GUARD, "0%dX" % count)


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 64
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else None
    st = {}
    t = time.time()
    digits = pi_hex(n, count, workers, st)
    print(digits)
    msg = "position %d, %d hex digits, %.1fs" % (n, count, time.time() - t)
    if st:
        msg += ("\n  fractions: %d" % st["fractions"]
                + "\n  denominator bits: %.3g  (BBP prime form %.3g, BBP term form %.3g)"
                % (st["den_bits"], st["bbp_prime_bits"], st["naive_bits"])
                + "\n  time: word stage %.1fs, head sum %.1fs (%d blocks), tail %.1fs"
                % (st["t_word"], st["t_head"], st["blocks"], st["t_tail"]))
    print(msg, file=sys.stderr)
