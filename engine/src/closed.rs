//! C_p for small primes without walking every cofactor.
//!
//! For a prime p with modulus q = p^E the coefficient splits by how often p
//! divides the denominator d = p^v * j' (j' odd, not divisible by p):
//!
//!     C_p = sum over v of  p^(E-v) * B_v   (mod p^E),
//!     B_v = sum over j' of  sign(d) * K * 2^(-gamma*(d-1)/2) / j'   (mod p^v),
//!
//! one such sum per series (gamma = 3, 5, 6, 10). Only B_v mod p^v matters, and
//! modulo p^v the summand is PERIODIC in j' with period 8*p^v:
//!   * the sign depends on d mod 8, so on j' mod 8;
//!   * 1/j' depends on j' mod p^v;
//!   * 2^(-gamma*p^v) has order dividing p-1 modulo p^v, so advancing j' by a
//!     whole period multiplies the term by the constant y = 2^(-4*gamma*p^(v-1)).
//! So the sum over all j' is a geometric series in y times one period's sum:
//! at most 4*p^v steps instead of la/(2*p^v). For p = 3 at a far position that is
//! tens of millions of steps instead of hundreds of trillions.
//!
//! When the run is shorter than one period this degenerates to the plain sum, so
//! the routine is exact for every odd prime.

use crate::mont::Mont;
use crate::word::Consts;

/// (C_p, q): the coefficient as a plain residue, and its modulus q = p^E.
pub fn small_prime(p: u64, k: &Consts) -> (u64, u64) {
    let lims = [k.la, k.lb, k.lc, k.ld];
    let mut q = p;
    while q <= k.la / p {
        q *= p;
    }
    let mut total: u128 = 0;
    let mut mv = 1u64; // p^v
    loop {
        if mv > k.la / p {
            break;
        }
        mv *= p;
        // j' runs over odd numbers up to jp[c] for series c
        let jp = [lims[0] / mv, lims[1] / mv, lims[2] / mv, lims[3] / mv];
        if jp[0] == 0 {
            break;
        }
        let period = 8u128 * mv as u128;
        let full = (jp[0] as u128) >= period; // some series wraps around the period
        let r_end = if full { (period - 1) as u64 } else { jp[0] };
        let mut i0 = [0u64; 4]; // whole periods
        let mut last = [0u64; 4]; // last odd r inside the partial period (0 = none)
        for c in 0..4 {
            i0[c] = (jp[c] as u128 / period) as u64;
            let rem = (jp[c] as u128 % period) as u64;
            last[c] = if rem % 2 == 1 { rem } else { rem.saturating_sub(1) };
        }

        let mt = Mont::new(mv);
        let phi = mv / p * (p - 1);
        let h = mt.to((mv + 1) >> 1); // 1/2
        let big = mt.pow2(k.m % phi); // 2^m
        let k2 = mt.mul(big, h);
        let kc = [mt.add(big, big), k2, k2, mt.mul(mt.mul(k2, mt.mul(h, h)), h)];
        let pows = |x: u64| -> [u64; 4] {
            let x2 = mt.mul(x, x);
            let x3 = mt.mul(x2, x);
            let x5 = mt.mul(x3, x2);
            [x3, x5, mt.mul(x3, x3), mt.mul(x5, x5)]
        };
        let tau = mt.pow(h, (mv / p) % phi); // (1/2)^(p^(v-1)): order divides p-1
        let rho = pows(tau); // factor per step of 2 in j', per series
        let mut s = pows(mt.pow(h, ((mv - 1) / 2) % phi)); // 2^(-gamma*(d-1)/2) at j' = 1

        let two = mt.add(mt.one, mt.one);
        let (mut n, mut d) = ([0u64; 4], mt.one); // running sums n[c] / d
        let (mut snap_n, mut snap_d) = ([0u64; 4], [mt.one; 4]);
        let mut rm = mt.one; // r in Montgomery form
        let mut rp = 1 % p; // r mod p
        let mut d8 = mv & 7; // d = p^v * r mod 8
        let step8 = (2 * (mv & 7)) & 7;
        let mut r = 1u64;
        while r <= r_end {
            if rp != 0 {
                let plus1 = d8 == 1 || d8 == 3;
                let plus2 = d8 & 3 == 1;
                let dd = d;
                d = mt.mul(d, rm);
                for c in 0..4 {
                    let plus = if c < 2 { plus1 } else { plus2 };
                    let a = if plus { s[c] } else { mt.neg(s[c]) };
                    n[c] = mt.add(mt.mul(n[c], rm), mt.mul(a, dd));
                }
            }
            for c in 0..4 {
                if r == last[c] {
                    snap_n[c] = n[c];
                    snap_d[c] = d;
                }
                s[c] = mt.mul(s[c], rho[c]);
            }
            rm = mt.add(rm, two);
            rp += 2;
            if rp >= p {
                rp -= p;
            }
            d8 = (d8 + step8) & 7;
            r += 2;
        }

        let neg_one = mt.neg(mt.one);
        let dinv = if full { mt.pow(d, phi - 1) } else { 0 };
        let mut b = 0u64;
        for c in 0..4 {
            let part = mt.mul(snap_n[c], mt.pow(snap_d[c], phi - 1));
            let sum = if i0[c] == 0 {
                part
            } else {
                let whole = mt.mul(n[c], dinv); // one full period
                let y = {
                    let y2 = mt.mul(rho[c], rho[c]);
                    mt.mul(y2, y2)
                };
                // g_lo = 1 + y + ... + y^(i0-1), g_hi = g_lo + y^i0
                let (g_lo, y_top) = if y == mt.one {
                    (mt.to(i0[c] % mv), mt.one)
                } else {
                    let yi = mt.pow(y, i0[c] % phi);
                    let inv = mt.pow(mt.add(y, neg_one), phi - 1);
                    (mt.mul(mt.add(yi, neg_one), inv), yi)
                };
                let g_hi = mt.add(g_lo, y_top);
                mt.add(mt.mul(g_hi, part), mt.mul(g_lo, mt.add(whole, mt.neg(part))))
            };
            b = mt.add(b, mt.mul(kc[c], sum));
        }
        let bv = mt.from(b);
        total = (total + (q / mv) as u128 * bv as u128) % q as u128;
    }
    (total as u64, q)
}
