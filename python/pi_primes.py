"""Prime-form digit extraction for pi.

    python pi_primes.py <position> <digit_count> [workers]

Prints <digit_count> hex digits of pi starting right after hex position <position>.

Idea
----
BBP writes frac(16^n * pi) as a sum of about 4n fractions, one per series term,
with denominators 8k+1, 2k+1, 8k+5, 4k+3. Those denominators share prime factors
massively. Splitting every fraction into partial fractions (Plouffe's 1996
"splitting" step, here applied to the BBP sum itself) and collecting by prime gives

    frac(16^n * pi) = sum over primes p of  C_p / p^E   (mod 1)  +  short tail

with ONE word-sized fraction per prime. There are far fewer primes than terms, so
the total size of all denominators falls from about 4n*log2(8n) bits to under 9n
bits. The fractions have pairwise coprime denominators and are then summed exactly
in blocks by a product tree, one big division per block (as in pi_blocks.py).

Stage A (word-sized arithmetic, numpy here; ideal for SIMD or GPU):
    C_p = sum over multiples d of p of  +-2^e(d) * (d/p^v)^-1 * p^(E-v)  mod p^E
Stage B (big numbers, GMP): sum the C_p/p^E in blocks, divide to window precision.

The three families of head terms (k = 0 .. n-1), written by denominator d:
    T1: d = 1 mod 4, d <= 8n-3 : +-2^(4n+2-(d-1)/2) / d   (+ if d = 1 mod 8)
    T2: d odd,       d <= 2n-1 :  -2^(4n+1-2d)      / d
    T3: d = 3 mod 4, d <= 4n-1 :  -2^(4n+2-d)       / d
"""
import sys
import time
from math import isqrt, log2
from multiprocessing import Pool, cpu_count

import numpy as np
from gmpy2 import mpz

import pi_blocks

U = np.uint64
GUARD = 64
CHUNK = 1 << 20          # elements per small-prime task
MIN_N = 2000             # below this the plain block method is used


# ---------------------------------------------------------------- word-sized helpers
def pow2(e, mod):
    """2**e % mod, elementwise. e: uint64 array; mod: uint64 scalar or array."""
    mod = np.asarray(mod, dtype=U)
    r = np.ones(e.shape, dtype=U)
    if e.size == 0:
        return r
    for i in range(int(e.max()).bit_length() - 1, -1, -1):
        r = r * r % mod
        r <<= (e >> U(i)) & U(1)
        r -= np.where(r >= mod, mod, U(0))
    return r


def powmod(base, exp, mod):
    """base**exp % mod, elementwise (all uint64, mod < 2**32)."""
    mod = np.asarray(mod, dtype=U)
    base = np.asarray(base, dtype=U) % mod
    exp = np.array(np.broadcast_to(np.asarray(exp, dtype=U), base.shape))
    r = np.ones(base.shape, dtype=U)
    while exp.any():
        odd = (exp & U(1)).astype(bool)
        r = np.where(odd, r * base % mod, r)
        exp >>= U(1)
        if exp.any():
            base = base * base % mod
    return r


def odd_primes_upto(m):
    if m < 3:
        return []
    sieve = bytearray([1]) * (m + 1)
    for i in range(3, isqrt(m) + 1, 2):
        if sieve[i]:
            sieve[i * i::2 * i] = bytearray(len(range(i * i, m + 1, 2 * i)))
    return [i for i in range(3, m + 1, 2) if sieve[i]]


def primes_between(lo, hi):
    """Odd primes p with lo < p <= hi, as a uint64 array."""
    start = max(lo + 1, 3) | 1
    if hi < start:
        return np.zeros(0, dtype=U)
    size = (hi - start) // 2 + 1
    sieve = np.ones(size, dtype=bool)
    for q in odd_primes_upto(isqrt(hi)):
        first = max(q * q, (start + q - 1) // q * q)
        if first % 2 == 0:
            first += q
        if first <= hi:
            sieve[(first - start) // 2::q] = False
    return (start + 2 * np.nonzero(sieve)[0]).astype(U)


def exponent(typ, d, n):
    if typ == 1:
        return U(4 * n + 2) - (d - U(1)) // U(2)
    if typ == 2:
        return U(4 * n + 1) - U(2) * d
    return U(4 * n + 2) - d


# ---------------------------------------------------------------- stage A, small primes
def small_task(args):
    """Each item: prime p, modulus q = p^E, family, and a run of multiples of p."""
    n, items = args
    out = []
    for p, q, typ, start, stop, step in items:
        d = np.arange(start, stop, step, dtype=U)
        u = d // U(p)
        pv = np.full(d.shape, p, dtype=U)
        m = u % U(p) == 0
        while m.any():                      # strip higher powers of p
            u[m] //= U(p)
            pv[m] *= U(p)
            m = u % U(p) == 0
        phi = q // p * (p - 1)
        c = pow2(exponent(typ, d, n) % U(phi), q)
        c = c * powmod(u, phi - 1, q) % U(q)
        c = c * (U(q) // pv) % U(q)
        if typ == 1:
            plus = d % U(8) == 1
            total = int(c[plus].sum()) - int(c[~plus].sum())
        else:
            total = -int(c.sum())
        out.append((p, total % q))
    return out


def small_plan(n, limit):
    """Tasks covering every (prime <= limit, family, multiple) once."""
    top = 8 * n - 3
    tasks, cur, load = [], [], 0
    for p in odd_primes_upto(limit):
        q = p
        while q * p <= top:
            q *= p
        runs = ((1, p * (p % 4), 4 * p, 8 * n - 3),
                (2, p, 2 * p, 2 * n - 1),
                (3, p * (3 if p % 4 == 1 else 1), 4 * p, 4 * n - 1))
        for typ, first, step, last in runs:
            a = first
            while a <= last:
                b = min(last + 1, a + step * CHUNK)
                cur.append((p, q, typ, a, b, step))
                load += (b - a) // step + 200
                a += ((b - a + step - 1) // step) * step
                if load >= CHUNK:
                    tasks.append((n, cur))
                    cur, load = [], 0
    if cur:
        tasks.append((n, cur))
    return tasks


# ---------------------------------------------------------------- stage A, large primes
def large_task(args):
    """All primes in (lo, hi]; each is larger than sqrt(8n), so p divides d once."""
    n, lo, hi = args
    p = primes_between(lo, hi)
    acc = np.zeros(p.shape, dtype=U)
    if p.size == 0:
        return p, acc
    top1, top2, top3 = 8 * n - 3, 2 * n - 1, 4 * n - 1
    pm1 = p - U(1)
    j = 1
    while j * int(p[0]) <= top1:
        cnt = int(np.searchsorted(p, top1 // j, side="right"))
        ps, ph = p[:cnt], pm1[:cnt]
        d = ps * U(j)
        inv = None if j == 1 else powmod(np.full(cnt, j, dtype=U), ph - U(1), ps)
        r4 = d % U(4)
        # families 1 and 3 never overlap (d mod 4 differs): one pass for both
        use = (r4 == 1) | (d <= U(top3))
        e = np.where(r4 == 1, U(4 * n + 2) - (d - U(1)) // U(2),
                     U(4 * n + 2) - np.minimum(d, U(top3)))
        c = pow2(e[use] % ph[use], ps[use])
        if inv is not None:
            c = c * inv[use] % ps[use]
        plus = (d % U(8) == 1)[use]
        c = np.where(plus, c, ps[use] - c)
        acc[:cnt][use] = (acc[:cnt][use] + c) % ps[use]
        # family 2
        c2 = int(np.searchsorted(d, top2, side="right"))
        if c2:
            c = pow2((U(4 * n + 1) - U(2) * d[:c2]) % ph[:c2], ps[:c2])
            if inv is not None:
                c = c * inv[:c2] % ps[:c2]
            acc[:c2] = (acc[:c2] + ps[:c2] - c) % ps[:c2]
        j += 2
    keep = acc != 0
    return p[keep], acc[keep]


def large_plan(n, limit):
    top = 8 * n - 3
    tasks, lo = [], limit
    while lo < top:
        hi = min(top, max(lo + 1000, int(lo * 1.15)))
        tasks.append((n, lo, hi))
        lo = hi
    return tasks


# ---------------------------------------------------------------- stage B
def sum_block(args):
    """Exact sum of fractions num/den (pairwise coprime dens) -> frac scaled 2^bits."""
    nums, dens, bits = args
    if len(nums) % 2:
        nums = np.append(nums, U(0))
        dens = np.append(dens, U(1))
    if int(dens.max()) < 1 << 31:          # first tree level in machine words
        P = (nums[0::2] * dens[1::2] + nums[1::2] * dens[0::2]).tolist()
        Q = (dens[0::2] * dens[1::2]).tolist()
    else:
        P, Q = nums.tolist(), dens.tolist()
    P = [mpz(x) for x in P]
    Q = [mpz(x) for x in Q]
    while len(Q) > 1:
        if len(Q) % 2:
            P.append(mpz(0))
            Q.append(mpz(1))
        P = [P[i] * Q[i + 1] + P[i + 1] * Q[i] for i in range(0, len(Q), 2)]
        Q = [Q[i] * Q[i + 1] for i in range(0, len(Q), 2)]
    return int(((P[0] % Q[0]) << bits) // Q[0])


def tail_plan(n, bits):
    """Terms k >= n, as ordinary exact blocks (see pi_blocks)."""
    jobs, a, end = [], n, n + bits // 4 + 3
    while a < end:
        m = max(1, bits // (9 + 4 * max(a, 2).bit_length()))
        b = min(a + m, end)
        jobs.append((n, a, b, bits))
        a = b
    return jobs


# ---------------------------------------------------------------- driver
def pi_hex(n, count, workers=None, stats=None):
    if n < MIN_N or 8 * n >= 1 << 31:
        return pi_blocks.pi_hex(n, count, workers)[0]
    bits = 4 * count + GUARD
    workers = workers or cpu_count()
    top = 8 * n - 3
    limit = min(top, max(isqrt(top) + 1, int(top ** 0.57)))
    t0 = time.time()
    with Pool(workers) as pool:
        # ---- stage A
        small = {}
        for res in pool.imap_unordered(small_task, small_plan(n, limit)):
            for p, v in res:
                small[p] = small.get(p, 0) + v
        nums, dens = [], []
        for p, v in small.items():
            q = p
            while q * p <= top:
                q *= p
            if v % q:
                nums.append(v % q)
                dens.append(q)
        parts_n = [np.array(nums, dtype=U)]
        parts_d = [np.array(dens, dtype=U)]
        for pr, acc in pool.imap_unordered(large_task, large_plan(n, limit)):
            parts_d.append(pr)
            parts_n.append(acc)
        nums = np.concatenate(parts_n)
        dens = np.concatenate(parts_d)
        t1 = time.time()
        # ---- stage B: head blocks of about `bits` bits of denominator, then the tail
        size = np.cumsum(np.log2(dens.astype(np.float64)))
        # never cut tiny blocks: a small window would otherwise mean millions of them
        per = max(bits, 1 << 18, int(size[-1] / 20000) + 1)
        cuts = np.searchsorted(size, np.arange(per, size[-1], per)).tolist()
        edges = [0] + cuts + [len(dens)]
        jobs = [(nums[a:b], dens[a:b], bits) for a, b in zip(edges, edges[1:]) if b > a]
        total = sum(pool.imap_unordered(sum_block, jobs))
        t2 = time.time()
        total += sum(pool.imap_unordered(pi_blocks.block, tail_plan(n, bits)))
        t3 = time.time()
    total &= (1 << bits) - 1
    if stats is not None:
        terms = 4 * n
        naive = n * (2 * log2(8 * n) + log2(2 * n) + log2(4 * n) - 4 * 1.4427)
        stats.update(fractions=len(dens), terms=terms, den_bits=float(size[-1]),
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
        msg += ("\n  fractions: %d (BBP terms: %d)" % (st["fractions"], st["terms"])
                + "\n  denominator bits: %.3g prime form vs %.3g term form (%.1fx smaller)"
                % (st["den_bits"], st["naive_bits"], st["naive_bits"] / st["den_bits"])
                + "\n  time: word stage %.1fs, head sum %.1fs (%d blocks), tail %.1fs"
                % (st["t_word"], st["t_head"], st["blocks"], st["t_tail"]))
    print(msg, file=sys.stderr)
