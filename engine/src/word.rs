//! Machine-word stage on the CPU. Mirrors `item` in kernel.cu line for line.
//!
//! pi/4 = 2*atan(1/3) + atan(1/7) gives four power-of-two series over odd d,
//! with t = (d-1)/2 and exponents (after scaling by 2^m):
//!     a: m + 1 - 3t     b: m - 1 - 5t     (sign + when d mod 8 is 1 or 3)
//!     c: m - 1 - 6t     d: m - 4 - 10t    (sign + when d mod 4 is 1)
//! Terms with exponent >= 0 are the head. Split by prime, the head becomes one
//! fraction C_p / p^E per odd prime; `item` computes (part of) one C_p.

use crate::mont::Mont;

/// (C, E0, sign kind): the exponent of a series at t is m + E0 - C*t.
pub const SERIES: [(u64, i64, u8); 4] = [(3, 1, 1), (5, -1, 1), (6, -1, 2), (10, -4, 2)];

#[derive(Clone, Copy, Debug)]
pub struct Consts {
    /// Bit position of the window.
    pub m: u64,
    /// Largest odd d in the head of each series (0 when the head is empty).
    pub la: u64,
    pub lb: u64,
    pub lc: u64,
    pub ld: u64,
}

impl Consts {
    pub fn new(m: u64) -> Consts {
        let lim = |i: usize| -> u64 {
            let (c, e0, _) = SERIES[i];
            let top = m as i128 + e0 as i128;
            if top < 0 {
                0
            } else {
                2 * (top / c as i128) as u64 + 1
            }
        };
        Consts { m, la: lim(0), lb: lim(1), lc: lim(2), ld: lim(3) }
    }
}

/// Share of C_p from the odd cofactors j0, j0+2, ... (`len` of them), as a plain
/// residue modulo q = p^E. `phi` is Euler's phi of q.
#[inline]
pub fn item(p: u64, q: u64, phi: u64, j0: u64, len: u64, k: &Consts) -> u64 {
    let mt = Mont::new(q);
    let h = mt.to((q + 1) >> 1); // 1/2
    let big = mt.pow2(k.m % phi); // 2^m
    let k1 = mt.add(big, big); // 2^(m+1)
    let k2 = mt.mul(big, h); // 2^(m-1)
    let h2 = mt.mul(h, h);
    let k4 = mt.mul(mt.mul(k2, h2), h); // 2^(m-4)

    let e1 = q == p;
    // g = 2^-t at j0; r = ratio between consecutive odd cofactors
    let (g, r) = if e1 && j0 == 1 {
        let r8 = p & 7; // 2^-((p-1)/2) is the Legendre symbol (2|p)
        (if r8 == 1 || r8 == 7 { mt.one } else { q - mt.one }, h)
    } else {
        (mt.pow(h, ((p * j0 - 1) >> 1) % phi), if e1 { h } else { mt.pow(h, p % phi) })
    };
    // The four series at j0. Each is a geometric sequence in j, so from here on
    // one multiplication per series per step keeps it current.
    let d0 = p * j0;
    let g2 = mt.mul(g, g);
    let g3 = mt.mul(g2, g);
    let mut sa = mt.mul(k1, g3);
    let (mut sb, mut sc4, mut sd, mut g5) = (0u64, 0u64, 0u64, 0u64);
    if d0 <= k.lb {
        g5 = mt.mul(g3, g2);
        sb = mt.mul(k2, g5);
    }
    if d0 <= k.lc {
        sc4 = mt.mul(k2, mt.mul(g3, g3));
    }
    if d0 <= k.ld {
        sd = mt.mul(k4, mt.mul(g5, g5));
    }
    if e1 && j0 == 1 && len == 1 {
        // a prime with the single cofactor 1
        let mut x = mt.add(sa, sb);
        let r8 = d0 & 7;
        if !(r8 == 1 || r8 == 3) {
            x = mt.neg(x);
        }
        if d0 <= k.lc {
            let mut y = mt.add(sc4, sd);
            if d0 & 3 != 1 {
                y = mt.neg(y);
            }
            x = mt.add(x, y);
        }
        return mt.from(x);
    }
    let q2 = mt.mul(r, r);
    let r3 = mt.mul(q2, r);
    let r5 = mt.mul(r3, q2);
    let r6 = mt.mul(r3, r3);
    let r10 = mt.mul(r5, r5);

    let sc = if e1 { 0 } else { mt.to(q / p) }; // p^(E-1)
    let two = mt.add(mt.one, mt.one);
    let mut jm = mt.to(j0);
    let mut jr = j0 % p;
    let (mut nn, mut dd, mut j) = (0u64, mt.one, j0);

    for _ in 0..len {
        let d = p * j;
        let mut x = sa; // series a
        sa = mt.mul(sa, r3);
        if d <= k.lb {
            x = mt.add(x, sb); // series b
            sb = mt.mul(sb, r5);
        }
        let r8 = d & 7;
        if !(r8 == 1 || r8 == 3) {
            x = mt.neg(x);
        }
        if d <= k.lc {
            let mut y = sc4; // series c
            sc4 = mt.mul(sc4, r6);
            if d <= k.ld {
                y = mt.add(y, sd); // series d
                sd = mt.mul(sd, r10);
            }
            if d & 3 != 1 {
                y = mt.neg(y);
            }
            x = mt.add(x, y);
        }
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
            jr += 2;
            if jr >= p {
                jr -= p;
            }
        }
        nn = mt.add(mt.mul(nn, um), mt.mul(x, dd));
        dd = mt.mul(dd, um);
        jm = mt.add(jm, two);
        j += 2;
    }
    let inv = mt.pow(dd, phi - 1);
    mt.from(mt.mul(nn, inv))
}

/// Work items for primes whose cofactor run is too long for one pass.
#[derive(Default)]
pub struct Items {
    pub p: Vec<u64>,
    pub q: Vec<u64>,
    pub phi: Vec<u64>,
    pub j0: Vec<u64>,
    pub len: Vec<u32>,
    /// Which small prime (index) each item belongs to.
    pub owner: Vec<u32>,
}

impl Items {
    pub fn clear(&mut self) {
        self.p.clear();
        self.q.clear();
        self.phi.clear();
        self.j0.clear();
        self.len.clear();
        self.owner.clear();
    }
}
