//! Montgomery arithmetic modulo an odd q below 2^63.

#[derive(Clone, Copy)]
pub struct Mont {
    pub q: u64,
    qi: u64,
    /// 1 in Montgomery form (2^64 mod q).
    pub one: u64,
    r2: u64,
}

impl Mont {
    #[inline]
    pub fn new(q: u64) -> Mont {
        let mut qi = q; // q^-1 mod 2^64 by Newton iteration
        for _ in 0..5 {
            qi = qi.wrapping_mul(2u64.wrapping_sub(q.wrapping_mul(qi)));
        }
        let one = q.wrapping_neg() % q;
        let r2 = ((one as u128 * one as u128) % q as u128) as u64;
        Mont { q, qi, one, r2 }
    }

    #[inline(always)]
    pub fn mul(&self, a: u64, b: u64) -> u64 {
        let t = a as u128 * b as u128;
        let lo = t as u64;
        let hi = (t >> 64) as u64;
        let mq = ((lo.wrapping_mul(self.qi) as u128 * self.q as u128) >> 64) as u64;
        let r = hi.wrapping_sub(mq);
        if hi < mq {
            r.wrapping_add(self.q)
        } else {
            r
        }
    }

    #[inline(always)]
    pub fn add(&self, a: u64, b: u64) -> u64 {
        let s = a + b;
        if s >= self.q {
            s - self.q
        } else {
            s
        }
    }

    #[inline(always)]
    pub fn neg(&self, a: u64) -> u64 {
        if a == 0 {
            0
        } else {
            self.q - a
        }
    }

    /// Plain value (any u64) into Montgomery form.
    #[inline(always)]
    pub fn to(&self, a: u64) -> u64 {
        self.mul(a, self.r2)
    }

    /// Montgomery form back to a plain residue.
    #[inline(always)]
    pub fn from(&self, a: u64) -> u64 {
        self.mul(a, 1)
    }

    #[inline]
    pub fn pow(&self, mut b: u64, mut e: u64) -> u64 {
        let mut r = self.one;
        while e != 0 {
            if e & 1 == 1 {
                r = self.mul(r, b);
            }
            b = self.mul(b, b);
            e >>= 1;
        }
        r
    }

    /// 2^e in Montgomery form.
    #[inline]
    pub fn pow2(&self, e: u64) -> u64 {
        let mut r = self.one;
        if e == 0 {
            return r;
        }
        for i in (0..(64 - e.leading_zeros())).rev() {
            r = self.mul(r, r);
            if (e >> i) & 1 == 1 {
                r = self.add(r, r);
            }
        }
        r
    }
}
