//! Machine-word stage for the cheaper formula (Part III of pi_formula_theorem.md).
//!
//!     pi = sum over k >= 1 of  c(k) * 2^(-floor(k/2)) / k,     c(k) = 2 * NUM[k mod 120].
//!
//! Head = the terms with k <= k0 = 2*(m - 64); there 2^(m - floor(k/2)) / k has an
//! odd denominator, so the head splits by prime exactly as for Euler's formula.
//!
//! `reference` walks every k (slow, obviously right). `item2` is the fast form. It
//! indexes the terms by an odd number n and the multiplier g, k = g*n:
//!
//!     g = 3   (odd k divisible by 3)            g = 5   (odd k, 5 | k, 3 !| k)
//!     g = 6   (k = 2 mod 4, 3 | k)              g = 10  (k = 2 mod 4, 5 | k, 3 !| k)
//!     g = 4   (k = 4 mod 8)                     g = 8 * 2^b   (8 | k, 3 !| k)
//!
//! With n = 2t + 1 each family is a power-of-two series in t, and all of them share
//! the denominator n. After dividing out a common 3 the contributions at n are:
//!
//!     g = 3:  +-S3 for n = 3, 7 (mod 8), nothing for n = 1 (mod 4)       S3 = 2^(m+2-3t)
//!             (5 | n: +-5/12 or +-7/12 of S3, by n mod 40)
//!     g = 4:  +S4                                                         S4 = 2^(m-4t)
//!     g = 5:  +-S5, + for n = 1, 3 (mod 8); nothing when 3 | n            S5 = 2^(m-1-5t)
//!     g = 6:  +S6 for n = 1 (mod 4)  (5 | n: 7/12 or 5/12 of S6)          S6 = 2^(m-6t)
//!     g = 10: +-S10, + for n = 1 (mod 4); nothing when 3 | n              S10 = 2^(m-4-10t)
//!     g = 8*2^b: +V_b unless 3 | n                                        V_b = 6 * 2^(m-b-2^(b+2)*n)
//!
//! kernel.cu has the same routine for the GPU; the two must stay in step.

use crate::mont::Mont;

/// 2 * rho(k) for k mod 120 (from pi_formula_120.json).
pub const NUM: [i8; 120] = [
    0, 0, 0, 0, 8, 5, 24, 0, 24, 12, 10, 0, //
    8, 0, 0, 5, 24, 0, 0, 0, 8, -12, 0, 0, //
    0, -5, 0, 0, 8, 0, 14, 0, 24, 12, 0, -5, //
    8, 0, 0, 0, 24, 0, 0, 0, 8, -7, 0, 0, //
    0, 0, 10, 0, 8, 0, 24, 5, 24, 12, 0, 0, //
    8, 0, 0, 0, 24, -5, 0, 0, 8, -12, -10, 0, //
    0, 0, 0, -5, 8, 0, 24, 0, 24, 12, 0, 0, //
    8, 5, 0, 0, 24, 0, 10, 0, 8, -12, 0, 5, //
    0, 0, 0, 0, 8, 0, 24, 0, 24, 7, 0, 0, //
    8, 0, -10, 0, 24, 0, 0, -5, 8, -12, 0, 0, //
];

/// c(k): the integer coefficient of 2^(-floor(k/2)) / k in the series for pi.
#[inline]
pub fn coef(k: u64) -> i64 {
    2 * NUM[(k % 120) as usize] as i64
}

/// Deepest level of the family g = 8 * 2^b that can occur.
pub const LEVELS: usize = 56;

#[derive(Clone, Copy, Debug)]
pub struct Consts2 {
    /// Bit position of the window.
    pub m: u64,
    /// Last k of the head.
    pub k0: u64,
    /// Largest index n (k0 / 3): the reach of the slowest family.
    pub l3: u64,
}

impl Consts2 {
    pub fn new(m: u64) -> Consts2 {
        // Very near the start everything is left to the tail (no head at all).
        let k0 = if m < 1024 { 0 } else { 2 * (m - 64) };
        Consts2 { m, k0, l3: k0 / 3 }
    }
}

/// Largest power of p that is at most `limit` (p itself if p > limit).
pub fn top_power(p: u64, limit: u64) -> u64 {
    let mut q = p;
    while q <= limit / p {
        q *= p;
    }
    q
}

/// C_p by walking every multiple of p up to k0. Returns (C_p, q) with q the
/// largest power of p not above k0. For tests only.
pub fn reference(p: u64, k: &Consts2) -> (u64, u64) {
    let q = top_power(p, k.k0);
    let phi = q / p * (p - 1);
    let mt = Mont::new(q);
    let h = mt.to((q + 1) >> 1);
    let big = mt.pow2(k.m % phi);
    let mut total = 0u64;
    let mut j = 1u64;
    while j <= k.k0 / p {
        let kk = p * j;
        let c = coef(kk);
        if c != 0 {
            let (mut u, mut pv) = (j, p);
            while u % p == 0 {
                u /= p;
                pv *= p;
            }
            let w = mt.mul(big, mt.pow(h, (kk / 2) % phi));
            let mut x = mt.mul(w, mt.to(c.unsigned_abs() % q));
            x = mt.mul(x, mt.to((q / pv) % q));
            x = mt.mul(x, mt.pow(mt.to(u % q), phi - 1));
            if c < 0 {
                x = mt.neg(x);
            }
            total = mt.add(total, x);
        }
        j += 1;
    }
    (mt.from(total), q)
}

#[inline(always)]
fn half(x: u64, q: u64) -> u64 {
    if x & 1 == 1 {
        (x + q) >> 1
    } else {
        x >> 1
    }
}

/// C_p for a prime with the single index n = p (p > l3 / 3, p > 5), as a plain
/// residue: 2^m times a small rational that depends only on p mod 4 and on which
/// families reach p.
#[inline]
pub fn single(p: u64, k: &Consts2) -> u64 {
    let mut w8: i64 = 0; // eight times the rational
    let three = p & 3 == 3;
    if three {
        w8 -= 32;
    }
    if p <= k.k0 / 4 {
        w8 += 8;
    }
    if p <= k.k0 / 5 {
        w8 += if three { -4 } else { 4 };
    }
    if p <= k.k0 / 6 && !three {
        w8 += 8;
    }
    if p <= k.k0 / 8 {
        w8 += 3;
    }
    if w8 == 0 {
        return 0;
    }
    let mt = Mont::new(p);
    let big = mt.pow2(k.m % (p - 1));
    let mut x = mt.mul(big, mt.to(w8.unsigned_abs()));
    x = half(half(half(x, p), p), p);
    if w8 < 0 {
        x = mt.neg(x);
    }
    mt.from(x)
}

/// Share of C_p from the indices n = p*j, j = j0, j0+2, ... (`len` odd cofactors),
/// as a plain residue modulo q = p^E. Needs p >= 7 and p*j <= l3 throughout.
#[inline]
pub fn item2(p: u64, q: u64, phi: u64, j0: u64, len: u64, k: &Consts2) -> u64 {
    let e1 = q == p;
    if e1 && j0 == 1 && len == 1 {
        return single(p, k);
    }
    let mt = Mont::new(q);
    let h = mt.to((q + 1) >> 1); // 1/2
    let big = mt.pow2(k.m % phi); // 2^m
    let (lim4, lim5, lim6, lim10) = (k.k0 / 4, k.k0 / 5, k.k0 / 6, k.k0 / 10);

    // g = 2^-t at n0 = p*j0; r = ratio between consecutive odd cofactors (2^-p)
    let (g, r) = if e1 && j0 == 1 {
        let r8 = p & 7; // 2^-((p-1)/2) is the Legendre symbol (2|p)
        (if r8 == 1 || r8 == 7 { mt.one } else { q - mt.one }, h)
    } else {
        (mt.pow(h, ((p * j0 - 1) >> 1) % phi), if e1 { h } else { mt.pow(h, p % phi) })
    };
    let n0 = p * j0;
    let g2 = mt.mul(g, g);
    let g3 = mt.mul(g2, g);
    let g4 = mt.mul(g2, g2);
    let big2 = mt.add(big, big);
    let mut s3 = mt.mul(mt.add(big2, big2), g3); // 2^(m+2) g^3
    let (mut s4, mut s5, mut s6, mut s10) = (0u64, 0u64, 0u64, 0u64);
    let (mut g5, mut g8) = (0u64, 0u64);
    if n0 <= lim4 {
        s4 = mt.mul(big, g4);
    }
    if n0 <= lim5 {
        g5 = mt.mul(g4, g);
        s5 = mt.mul(half(big, q), g5);
    }
    if n0 <= lim6 {
        s6 = mt.mul(big, mt.mul(g3, g3));
        g8 = mt.mul(g4, g4);
    }
    if n0 <= lim10 {
        let b16 = half(half(half(half(big, q), q), q), q);
        s10 = mt.mul(b16, mt.mul(g5, g5));
    }
    // ratios
    let q2 = mt.mul(r, r);
    let r3 = mt.mul(q2, r);
    let r4 = mt.mul(q2, q2);
    let r5 = mt.mul(r4, r);
    let r6 = mt.mul(r3, r3);
    let r8 = mt.mul(r4, r4);
    let r10 = mt.mul(r5, r5);
    // levels g = 8 * 2^b: active while n <= k0 >> (b + 3)
    let mut nb = 0usize;
    while nb < LEVELS && n0 <= (k.k0 >> (nb + 3)) {
        nb += 1;
    }
    let mut v = [0u64; LEVELS];
    let mut rr = [0u64; LEVELS];
    if nb > 0 {
        let h2 = mt.mul(h, h);
        let mut y = mt.mul(g8, mt.mul(h2, h2)); // 2^(-4 n0)
        let mut cst = mt.add(big2, mt.add(big2, big2)); // 6 * 2^m
        let mut rb = r8;
        for b in 0..nb {
            v[b] = mt.mul(cst, y);
            rr[b] = rb;
            y = mt.mul(y, y);
            rb = mt.mul(rb, rb);
            cst = half(cst, q);
        }
    }
    // 5/12 and 7/12, for the indices divisible by 5
    let i12 = {
        let i3 = mt.to(if q % 3 == 1 { (2 * q + 1) / 3 } else { (q + 1) / 3 });
        half(half(i3, q), q)
    };
    let i12x2 = mt.add(i12, i12);
    let i12x4 = mt.add(i12x2, i12x2);
    let c512 = mt.add(i12x4, i12);
    let c712 = mt.add(c512, i12x2);

    let sc = if e1 { 0 } else { mt.to(q / p) }; // p^(E-1)
    let two = mt.add(mt.one, mt.one);
    let mut jm = mt.to(j0);
    let mut jr = j0 % p;
    let (mut nn, mut dd, mut j) = (0u64, mt.one, j0);
    let step = (2 * (p % 120)) % 120;
    let mut nm = n0 % 120;

    for _ in 0..len {
        let n = p * j;
        let n8 = nm & 7;
        let five = nm % 5 == 0;
        let three = nm % 3 == 0;
        let mut x = 0u64;
        // g = 3
        if !five {
            if n8 == 3 {
                x = s3;
            } else if n8 == 7 {
                x = mt.neg(s3);
            }
        } else {
            x = match nm % 40 {
                5 => mt.mul(s3, c512),
                15 => mt.neg(mt.mul(s3, c712)),
                25 => mt.neg(mt.mul(s3, c512)),
                _ => mt.mul(s3, c712),
            };
        }
        s3 = mt.mul(s3, r3);
        if n <= lim4 {
            x = mt.add(x, s4); // g = 4
            s4 = mt.mul(s4, r4);
            if n <= lim5 {
                if !three {
                    // g = 5
                    x = mt.add(x, if n8 == 1 || n8 == 3 { s5 } else { mt.neg(s5) });
                }
                s5 = mt.mul(s5, r5);
                if n <= lim6 {
                    // g = 6
                    if !five {
                        if n8 & 3 == 1 {
                            x = mt.add(x, s6);
                        }
                    } else {
                        x = mt.add(x, mt.mul(s6, if nm % 20 == 5 { c712 } else { c512 }));
                    }
                    s6 = mt.mul(s6, r6);
                    // g = 8 * 2^b
                    while nb > 0 && n > (k.k0 >> (nb + 2)) {
                        nb -= 1;
                    }
                    for b in 0..nb {
                        if !three {
                            x = mt.add(x, v[b]);
                        }
                        v[b] = mt.mul(v[b], rr[b]);
                    }
                    if n <= lim10 {
                        if !three {
                            // g = 10
                            x = mt.add(x, if n8 & 3 == 1 { s10 } else { mt.neg(s10) });
                        }
                        s10 = mt.mul(s10, r10);
                    }
                }
            }
        }
        if x != 0 {
            let mut um = jm;
            if !e1 {
                if jr != 0 {
                    x = mt.mul(x, sc);
                } else {
                    // p divides j: strip its powers
                    let (mut u, mut pv) = (j, p);
                    while u % p == 0 {
                        u /= p;
                        pv *= p;
                    }
                    um = mt.to(u);
                    x = mt.mul(x, mt.to(q / pv));
                }
            }
            nn = mt.add(mt.mul(nn, um), mt.mul(x, dd));
            dd = mt.mul(dd, um);
        }
        if !e1 {
            jr += 2;
            if jr >= p {
                jr -= p;
            }
        }
        jm = mt.add(jm, two);
        j += 2;
        nm += step;
        if nm >= 120 {
            nm -= 120;
        }
    }
    let inv = mt.pow(dd, phi - 1);
    mt.from(mt.mul(nn, inv))
}

/// C_p for any odd prime by the period of its terms (the analogue of closed.rs).
///
/// C_p = sum over v of p^(E-v) * B_v, and modulo p^v the terms of
///     B_v = sum over j (p !| j, p^v j <= k0) of c(p^v j) * 2^(m - floor(p^v j / 2)) / j
/// repeat with period 120 * p^v up to the constant factor y = 2^(-60 p^(2v)), whose
/// order divides p - 1. So one period (or the whole run, if shorter) is enough.
pub fn small_prime2(p: u64, k: &Consts2) -> (u64, u64) {
    let q = top_power(p, k.k0);
    if p > k.k0 {
        return (0, q);
    }
    let mut total: u128 = 0;
    let mut mv = 1u64; // p^v
    loop {
        if mv > k.k0 / p {
            break;
        }
        mv *= p;
        let jmax = k.k0 / mv;
        let period = 120u128 * mv as u128;
        let full = jmax as u128 >= period;
        let r_end = if full { period as u64 } else { jmax };
        let i0 = (jmax as u128 / period) as u64; // whole periods
        let rem = (jmax as u128 % period) as u64; // length of the partial period

        let mt = Mont::new(mv);
        let phi = mv / p * (p - 1);
        let h = mt.to((mv + 1) >> 1);
        let big = mt.pow2(k.m % phi);
        let rho = mt.pow(h, mv % phi); // 2^(-p^v): two steps of j
        let s_odd = mt.pow(h, ((mv - 1) / 2) % phi); // extra factor for odd j
        let mut cm = [0u64; 25]; // |NUM| in Montgomery form
        for (a, slot) in cm.iter_mut().enumerate() {
            *slot = mt.to(a as u64 % mv);
        }
        let (mut nn, mut dd) = (0u64, mt.one);
        let (mut snap_n, mut snap_d) = (0u64, mt.one);
        let mut pw = mt.one; // rho^(j div 2)
        let mut jm = mt.one; // j in Montgomery form
        let mut jr = 1 % p; // j mod p
        let step = (mv % 120) as usize;
        let mut km = step; // p^v * j mod 120
        let mut j = 1u64;
        while j <= r_end {
            if j & 1 == 0 {
                pw = mt.mul(pw, rho);
            }
            let c = NUM[km];
            if c != 0 && jr != 0 {
                let w = if j & 1 == 1 { mt.mul(pw, s_odd) } else { pw };
                let mut x = mt.mul(w, cm[c.unsigned_abs() as usize]);
                if c < 0 {
                    x = mt.neg(x);
                }
                nn = mt.add(mt.mul(nn, jm), mt.mul(x, dd));
                dd = mt.mul(dd, jm);
            }
            if j == rem {
                snap_n = nn;
                snap_d = dd;
            }
            jm = mt.add(jm, mt.one);
            jr += 1;
            if jr == p {
                jr = 0;
            }
            km += step;
            if km >= 120 {
                km -= 120;
            }
            j += 1;
        }
        let neg_one = mt.neg(mt.one);
        let part = mt.mul(snap_n, mt.pow(snap_d, phi - 1));
        let sum = if i0 == 0 {
            part
        } else {
            let whole = mt.mul(nn, mt.pow(dd, phi - 1)); // one full period
            let y = mt.pow(rho, ((60u128 * mv as u128) % phi as u128) as u64);
            // g_lo = 1 + y + ... + y^(i0-1), g_hi = g_lo + y^i0
            let (g_lo, y_top) = if y == mt.one {
                (mt.to(i0 % mv), mt.one)
            } else {
                let yi = mt.pow(y, i0 % phi);
                let inv = mt.pow(mt.add(y, neg_one), phi - 1);
                (mt.mul(mt.add(yi, neg_one), inv), yi)
            };
            // sum = whole * g_lo + part * y^i0
            mt.add(mt.mul(whole, g_lo), mt.mul(part, y_top))
        };
        // NUM is c/2: restore the factor 2 together with 2^m
        let bv = mt.from(mt.mul(mt.add(big, big), sum));
        total = (total + (q / mv) as u128 * bv as u128) % q as u128;
    }
    (total as u64, q)
}
