//! Big-number stage: exact sums of many small fractions by product trees.

use malachite_base::num::basic::traits::{One, Zero};
use malachite_base::num::logic::traits::SignificantBits;
use malachite_nz::natural::Natural;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

/// Below this many fractions a subtree is summed on one thread.
const PAR: usize = 1 << 12;

/// Exact P/Q = sum of nums[i]/dens[i]. Needs nums[i] < dens[i] < 2^63.
pub fn frac_sum(nums: &[u64], dens: &[u64]) -> (Natural, Natural) {
    let k = nums.len();
    match k {
        0 => (Natural::ZERO, Natural::ONE),
        1 => (Natural::from(nums[0]), Natural::from(dens[0])),
        2 => {
            let p = nums[0] as u128 * dens[1] as u128 + nums[1] as u128 * dens[0] as u128;
            let q = dens[0] as u128 * dens[1] as u128;
            (Natural::from(p), Natural::from(q))
        }
        _ => {
            let mid = k / 2;
            if k >= PAR {
                let ((pl, ql), (pr, qr)) = rayon::join(
                    || frac_sum(&nums[..mid], &dens[..mid]),
                    || frac_sum(&nums[mid..], &dens[mid..]),
                );
                let (a, (b, q)) =
                    rayon::join(|| &pl * &qr, || rayon::join(|| &pr * &ql, || &ql * &qr));
                (a + b, q)
            } else {
                let (pl, ql) = frac_sum(&nums[..mid], &dens[..mid]);
                let (pr, qr) = frac_sum(&nums[mid..], &dens[mid..]);
                (&pl * &qr + &pr * &ql, ql * qr)
            }
        }
    }
}

/// Lowest 64 bits (used by the benchmark to keep results alive).
pub fn low_limb(x: &Natural) -> u64 {
    x.limbs().next().unwrap_or(0)
}

/// Thread-seconds spent building trees and dividing, in nanoseconds (for the report).
pub static TREE_NS: AtomicU64 = AtomicU64::new(0);
pub static DIV_NS: AtomicU64 = AtomicU64::new(0);

/// frac(sum of nums[i]/dens[i]) scaled by 2^bits, within a couple of units.
pub fn head_block(nums: &[u64], dens: &[u64], bits: u64) -> Natural {
    let t = Instant::now();
    let (p, q) = frac_sum(nums, dens);
    TREE_NS.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
    let t = Instant::now();
    let mut r = p % &q;
    let mut q = q;
    // Only `bits` bits of the quotient are wanted, so only the leading
    // bits + 64 bits of the divisor (and the matching part of r) matter.
    let qb = q.significant_bits();
    if qb > bits + 64 {
        let drop = qb - (bits + 64);
        r >>= drop;
        q >>= drop;
    }
    let v = (r << bits) / q;
    DIV_NS.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
    v
}

/// Signed exact P/Q = sum over t in [a, b) of sign(t) * 2^(c*(b-1-t)) / (2t+1).
/// Returns (negative?, |P|, Q).
fn tail_split(c: u64, kind: u8, a: u64, b: u64) -> (bool, Natural, Natural) {
    if b - a == 1 {
        let plus = if kind == 1 { a % 4 < 2 } else { a % 2 == 0 };
        return (!plus, Natural::ONE, Natural::from(2 * a + 1));
    }
    let mid = a + (b - a) / 2;
    let ((nl, pl, ql), (nr, pr, qr)) = if (b - a) as usize >= PAR {
        rayon::join(|| tail_split(c, kind, a, mid), || tail_split(c, kind, mid, b))
    } else {
        (tail_split(c, kind, a, mid), tail_split(c, kind, mid, b))
    };
    let left = (pl * &qr) << (c * (b - mid));
    let right = pr * &ql;
    let q = ql * qr;
    if nl == nr {
        (nl, left + right, q)
    } else if left >= right {
        (nl, left - right, q)
    } else {
        (nr, right - left, q)
    }
}

/// Tail of the cheaper formula. Signed exact P/Q = sum over k in [a, b) of
/// c(k) * 2^(H - floor(k/2)) / k with H = floor((b-1)/2). Returns (negative?, |P|, Q).
fn tail2_split(a: u64, b: u64) -> (bool, Natural, Natural) {
    if b - a == 1 {
        let c = crate::word2::coef(a);
        if c == 0 {
            return (false, Natural::ZERO, Natural::ONE);
        }
        return (c < 0, Natural::from(c.unsigned_abs()), Natural::from(a));
    }
    let mid = a + (b - a) / 2;
    let ((nl, pl, ql), (nr, pr, qr)) = if (b - a) as usize >= PAR {
        rayon::join(|| tail2_split(a, mid), || tail2_split(mid, b))
    } else {
        (tail2_split(a, mid), tail2_split(mid, b))
    };
    let left = (pl * &qr) << ((b - 1) / 2 - (mid - 1) / 2);
    let right = pr * &ql;
    let q = ql * qr;
    if nl == nr {
        (nl, left + right, q)
    } else if left >= right {
        (nl, left - right, q)
    } else {
        (nr, right - left, q)
    }
}

/// One block of that tail, scaled by 2^bits: (negative?, magnitude).
pub fn tail2_block(a: u64, b: u64, m: u64, bits: u64) -> (bool, Natural) {
    let (neg, p, q) = tail2_split(a, b);
    let sh = bits as i128 + m as i128 - ((b - 1) / 2) as i128;
    let v = if sh >= 0 { (p << (sh as u64)) / q } else { (p >> ((-sh) as u64)) / q };
    (neg, v)
}

/// One block of a tail series, scaled by 2^bits: (negative?, magnitude).
/// The series exponent at t is m + e0 - c*t.
pub fn tail_block(c: u64, e0: i64, kind: u8, a: u64, b: u64, m: u64, bits: u64) -> (bool, Natural) {
    let (neg, p, q) = tail_split(c, kind, a, b);
    let sh = bits as i128 + m as i128 + e0 as i128 - c as i128 * (b as i128 - 1);
    let v = if sh >= 0 { (p << (sh as u64)) / q } else { (p >> ((-sh) as u64)) / q };
    (neg, v)
}
