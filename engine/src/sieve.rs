//! Prime sieves (odd primes only; 2 never appears among the denominators).

/// Odd primes up to `limit`.
pub fn odd_primes_upto(limit: u64) -> Vec<u64> {
    if limit < 3 {
        return Vec::new();
    }
    let n = ((limit - 1) / 2) as usize; // index i stands for 2i + 3
    let mut comp = vec![false; n];
    let mut i = 0usize;
    while (2 * i + 3) * (2 * i + 3) <= limit as usize {
        if !comp[i] {
            let p = 2 * i + 3;
            let mut k = (p * p - 3) / 2;
            while k < n {
                comp[k] = true;
                k += p;
            }
        }
        i += 1;
    }
    (0..n).filter(|&i| !comp[i]).map(|i| 2 * i as u64 + 3).collect()
}

/// Primes p = 3 (mod 4) with lo < p <= hi: the same sieve run over the progression
/// 4i + 3 only, so half the memory and half the crossing-off of `primes_in`.
pub fn primes_in_3mod4(lo: u64, hi: u64, base: &[u64]) -> Vec<u64> {
    let mut start = (lo + 1).max(3);
    while start % 4 != 3 {
        start += 1;
    }
    if hi < start {
        return Vec::new();
    }
    let total = ((hi - start) / 4 + 1) as usize; // index i stands for start + 4i
    let mut used: Vec<usize> = Vec::new();
    let mut next: Vec<usize> = Vec::new();
    for &b in base {
        if b * b > hi {
            break;
        }
        // first multiple of b in the progression: successive multiples of an odd b
        // run through all residues modulo 4
        let mut first = (b * b).max((start + b - 1) / b * b);
        while first % 4 != 3 {
            first += b;
        }
        used.push(b as usize);
        next.push(((first - start) / 4) as usize);
    }
    const SUB: usize = 1 << 18;
    let mut out = Vec::with_capacity(total / 8 + 16);
    let mut buf = vec![1u8; SUB.min(total)];
    let mut at = 0usize;
    while at < total {
        let n = SUB.min(total - at);
        let end = at + n;
        buf[..n].fill(1);
        for (b, o) in used.iter().zip(next.iter_mut()) {
            let mut k = *o;
            while k < end {
                buf[k - at] = 0;
                k += b;
            }
            *o = k;
        }
        for (i, &f) in buf[..n].iter().enumerate() {
            if f != 0 {
                out.push(start + 4 * (at + i) as u64);
            }
        }
        at = end;
    }
    out
}

/// Odd primes p with lo < p <= hi. `base` must hold every odd prime up to sqrt(hi).
pub fn primes_in(lo: u64, hi: u64, base: &[u64]) -> Vec<u64> {
    let start = (lo + 1).max(3) | 1;
    if hi < start {
        return Vec::new();
    }
    let total = ((hi - start) / 2 + 1) as usize; // index i stands for start + 2i
    let mut used: Vec<usize> = Vec::new();
    let mut next: Vec<usize> = Vec::new();
    for &b in base {
        if b * b > hi {
            break;
        }
        let mut first = (b * b).max((start + b - 1) / b * b);
        if first % 2 == 0 {
            first += b;
        }
        used.push(b as usize);
        next.push(((first - start) / 2) as usize);
    }
    const SUB: usize = 1 << 18; // stay inside the cache
    let mut out = Vec::with_capacity(total / 8 + 16);
    let mut buf = vec![1u8; SUB.min(total)];
    let mut at = 0usize;
    while at < total {
        let n = SUB.min(total - at);
        let end = at + n;
        buf[..n].fill(1);
        for (b, o) in used.iter().zip(next.iter_mut()) {
            let mut k = *o;
            while k < end {
                buf[k - at] = 0;
                k += b;
            }
            *o = k;
        }
        for (i, &f) in buf[..n].iter().enumerate() {
            if f != 0 {
                out.push(start + 2 * (at + i) as u64);
            }
        }
        at = end;
    }
    out
}
