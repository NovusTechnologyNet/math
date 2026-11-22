// Machine-word stage of the prime-form pi window, for the GPU.
//
// One thread handles one work item: a prime p with modulus q = p^E and a run of
// odd cofactors j0, j0+2, ... (len of them). It returns the item's share of C_p,
// the numerator of the single fraction C_p / q that this prime contributes to
// frac(2^m * pi). The same routine exists in Rust (src/word.rs) for the CPU path;
// the two must stay in step.
//
// All arithmetic is Montgomery arithmetic modulo q (odd, below 2^63).

typedef unsigned long long u64;
typedef unsigned int u32;

__device__ __forceinline__ u64 mmul(u64 a, u64 b, u64 q, u64 qi) {
    u64 lo = a * b;
    u64 hi = __umul64hi(a, b);
    u64 t = __umul64hi(lo * qi, q);
    u64 r = hi - t;
    return hi < t ? r + q : r;
}

__device__ __forceinline__ u64 madd(u64 a, u64 b, u64 q) {
    u64 s = a + b;
    return s >= q ? s - q : s;
}

__device__ __forceinline__ u64 mneg(u64 a, u64 q) { return a ? q - a : 0; }

__device__ u64 mpow(u64 b, u64 e, u64 one, u64 q, u64 qi) {
    u64 r = one;
    while (e) {
        if (e & 1) r = mmul(r, b, q, qi);
        b = mmul(b, b, q, qi);
        e >>= 1;
    }
    return r;
}

// 2^e in Montgomery form
__device__ u64 mpow2(u64 e, u64 one, u64 q, u64 qi) {
    u64 r = one;
    if (!e) return r;
    for (int i = 63 - __clzll(e); i >= 0; --i) {
        r = mmul(r, r, q, qi);
        if ((e >> i) & 1) r = madd(r, r, q);
    }
    return r;
}

// a mod b for a < 2^53, using one floating-point division (far cheaper on a GPU
// than a 64-bit integer modulo); exact after the correction step.
__device__ __forceinline__ u64 fmod53(u64 a, u64 b) {
    u64 r = a - (u64)((double)a / (double)b) * b;
    if ((long long)r < 0) r += b;
    else if (r >= b) r -= b;
    return r;
}

__device__ u64 item(u64 p, u64 q, u64 phi, u64 j0, u64 len,
                    u64 m, u64 la, u64 lb, u64 lc, u64 ld) {
    u64 qi = q;                                   // q^-1 mod 2^64 (Newton)
    for (int i = 0; i < 5; ++i) qi *= 2 - q * qi;
    u64 one;                                      // 2^64 mod q
    if (q >= 4096) {                              // quotient below 2^52: one float division
        one = 0ULL - (u64)(18446744073709551616.0 / (double)q) * q;
        if ((long long)one < 0) one += q;
        else if (one >= q) one -= q;
    } else {
        one = (0ULL - q) % q;
    }
    u64 two = madd(one, one, q);
    u64 r2 = two;                                 // (2^64)*R = R^2 mod q: square 2 six times
    for (int i = 0; i < 6; ++i) r2 = mmul(r2, r2, q, qi);

    u64 h = mmul((q + 1) >> 1, r2, q, qi);        // 1/2
    u64 e = (m >> 53) ? m % phi : fmod53(m, phi);
    u64 big = mpow2(e, one, q, qi);               // 2^m
    u64 k1 = madd(big, big, q);                   // 2^(m+1)
    u64 k2 = mmul(big, h, q, qi);                 // 2^(m-1)
    u64 h2 = mmul(h, h, q, qi);
    u64 k4 = mmul(mmul(k2, h2, q, qi), h, q, qi); // 2^(m-4)

    bool e1 = (q == p);
    u64 g, r;                                     // g = 2^-t at j0, r = step ratio
    if (e1 && j0 == 1) {
        u64 r8 = p & 7;                           // 2^-((p-1)/2) = Legendre (2|p)
        g = (r8 == 1 || r8 == 7) ? one : q - one;
        r = h;
    } else {
        g = mpow(h, ((p * j0 - 1) >> 1) % phi, one, q, qi);
        r = e1 ? h : mpow(h, p % phi, one, q, qi);
    }
    // The four series at j0. Each is a geometric sequence in j, so from here on
    // one multiplication per series per step keeps it current.
    u64 d0 = p * j0;
    u64 g2 = mmul(g, g, q, qi), g3 = mmul(g2, g, q, qi);
    u64 sa = mmul(k1, g3, q, qi), sb = 0, sc4 = 0, sd = 0, g5 = 0;
    if (d0 <= lb) { g5 = mmul(g3, g2, q, qi); sb = mmul(k2, g5, q, qi); }
    if (d0 <= lc) sc4 = mmul(k2, mmul(g3, g3, q, qi), q, qi);
    if (d0 <= ld) sd = mmul(k4, mmul(g5, g5, q, qi), q, qi);
    if (e1 && j0 == 1 && len == 1) {              // a prime with the single cofactor 1
        u64 x = madd(sa, sb, q);
        u64 r8 = d0 & 7;
        if (!(r8 == 1 || r8 == 3)) x = mneg(x, q);
        if (d0 <= lc) {
            u64 y = madd(sc4, sd, q);
            if ((d0 & 3) != 1) y = mneg(y, q);
            x = madd(x, y, q);
        }
        return mmul(x, 1, q, qi);
    }
    u64 q2 = mmul(r, r, q, qi), r3 = mmul(q2, r, q, qi), r5 = mmul(r3, q2, q, qi);
    u64 r6 = mmul(r3, r3, q, qi), r10 = mmul(r5, r5, q, qi);

    u64 sc = e1 ? 0 : mmul(q / p, r2, q, qi);     // p^(E-1)
    u64 jm = mmul(j0, r2, q, qi);                 // j in Montgomery form
    u64 jr = j0 % p;                              // j mod p (only used when E > 1)
    u64 nn = 0, dd = one, j = j0;                 // running fraction nn / dd

    for (u64 it = 0; it < len; ++it) {
        u64 d = p * j;
        u64 x = sa;                               // series a
        sa = mmul(sa, r3, q, qi);
        if (d <= lb) {                            // series b
            x = madd(x, sb, q);
            sb = mmul(sb, r5, q, qi);
        }
        u64 r8 = d & 7;
        if (!(r8 == 1 || r8 == 3)) x = mneg(x, q);
        if (d <= lc) {                            // series c, d
            u64 y = sc4;
            sc4 = mmul(sc4, r6, q, qi);
            if (d <= ld) {
                y = madd(y, sd, q);
                sd = mmul(sd, r10, q, qi);
            }
            if ((d & 3) != 1) y = mneg(y, q);
            x = madd(x, y, q);
        }
        u64 um = jm;
        if (!e1) {
            if (jr != 0) {
                x = mmul(x, sc, q, qi);
            } else {                              // p divides j: strip its powers
                u64 u = j, pv = p;
                while (u % p == 0) { u /= p; pv *= p; }
                um = mmul(u, r2, q, qi);
                x = mmul(x, mmul(q / pv, r2, q, qi), q, qi);
            }
            jr += 2;
            if (jr >= p) jr -= p;
        }
        nn = madd(mmul(nn, um, q, qi), mmul(x, dd, q, qi), q);
        dd = mmul(dd, um, q, qi);
        jm = madd(jm, two, q);
        j += 2;
    }
    u64 inv = mpow(dd, phi - 1, one, q, qi);
    return mmul(mmul(nn, inv, q, qi), 1, q, qi);
}

// ---------------------------------------------------------------------------
// The cheaper formula (src/word2.rs has the same routines and the explanation).
// ---------------------------------------------------------------------------

#define LEVELS 56

__device__ __forceinline__ u64 mhalf(u64 x, u64 q) { return (x & 1) ? (x + q) >> 1 : x >> 1; }

__device__ __forceinline__ void msetup(u64 q, u64& qi, u64& one, u64& r2) {
    qi = q;                                       // q^-1 mod 2^64 (Newton)
    for (int i = 0; i < 5; ++i) qi *= 2 - q * qi;
    if (q >= 4096) {                              // 2^64 mod q by one float division
        one = 0ULL - (u64)(18446744073709551616.0 / (double)q) * q;
        if ((long long)one < 0) one += q;
        else if (one >= q) one -= q;
    } else {
        one = (0ULL - q) % q;
    }
    r2 = madd(one, one, q);                       // R^2 mod q: square 2 six times
    for (int i = 0; i < 6; ++i) r2 = mmul(r2, r2, q, qi);
}

// A prime with the single index n = p: C_p = 2^m * (small rational).
__device__ u64 single2(u64 p, u64 m, u64 k0) {
    long long w8 = 0;                             // eight times the rational
    bool three = (p & 3) == 3;
    if (three) w8 -= 32;
    if (4 * p <= k0) w8 += 8;
    if (5 * p <= k0) w8 += three ? -4 : 4;
    if (6 * p <= k0 && !three) w8 += 8;
    if (8 * p <= k0) w8 += 3;
    if (w8 == 0) return 0;
    u64 qi, one, r2;
    msetup(p, qi, one, r2);
    u64 phi = p - 1;
    u64 e = (m >> 53) ? m % phi : fmod53(m, phi);
    u64 big = mpow2(e, one, p, qi);
    u64 a = (u64)(w8 < 0 ? -w8 : w8);
    u64 x = mmul(big, mmul(a, r2, p, qi), p, qi);
    x = mhalf(mhalf(mhalf(x, p), p), p);
    if (w8 < 0) x = mneg(x, p);
    return mmul(x, 1, p, qi);
}

__device__ u64 item2(u64 p, u64 q, u64 phi, u64 j0, u64 len, u64 m, u64 k0) {
    bool e1 = (q == p);
    if (e1 && j0 == 1 && len == 1) return single2(p, m, k0);
    u64 qi, one, r2;
    msetup(q, qi, one, r2);
    u64 two = madd(one, one, q);
    u64 h = mmul((q + 1) >> 1, r2, q, qi);        // 1/2
    u64 e = (m >> 53) ? m % phi : fmod53(m, phi);
    u64 big = mpow2(e, one, q, qi);               // 2^m

    u64 g, r;                                     // g = 2^-t at n0, r = 2^-p
    if (e1 && j0 == 1) {
        u64 p8 = p & 7;                           // Legendre (2|p)
        g = (p8 == 1 || p8 == 7) ? one : q - one;
        r = h;
    } else {
        g = mpow(h, ((p * j0 - 1) >> 1) % phi, one, q, qi);
        r = e1 ? h : mpow(h, p % phi, one, q, qi);
    }
    u64 n0 = p * j0;
    u64 g2 = mmul(g, g, q, qi), g3 = mmul(g2, g, q, qi), g4 = mmul(g2, g2, q, qi);
    u64 big2 = madd(big, big, q);
    u64 s3 = mmul(madd(big2, big2, q), g3, q, qi);                 // 2^(m+2) g^3
    u64 s4 = 0, s5 = 0, s6 = 0, s10 = 0, g5 = 0, g8 = 0;
    if (4 * n0 <= k0) s4 = mmul(big, g4, q, qi);
    if (5 * n0 <= k0) { g5 = mmul(g4, g, q, qi); s5 = mmul(mhalf(big, q), g5, q, qi); }
    if (6 * n0 <= k0) { s6 = mmul(big, mmul(g3, g3, q, qi), q, qi); g8 = mmul(g4, g4, q, qi); }
    if (10 * n0 <= k0) {
        u64 b16 = mhalf(mhalf(mhalf(mhalf(big, q), q), q), q);
        s10 = mmul(b16, mmul(g5, g5, q, qi), q, qi);
    }
    u64 q2 = mmul(r, r, q, qi), r3 = mmul(q2, r, q, qi), r4 = mmul(q2, q2, q, qi);
    u64 r5 = mmul(r4, r, q, qi), r6 = mmul(r3, r3, q, qi), r8 = mmul(r4, r4, q, qi);
    u64 r10 = mmul(r5, r5, q, qi);

    int nb = 0;                                   // levels g = 8 * 2^b
    while (nb < LEVELS && n0 <= (k0 >> (nb + 3))) ++nb;
    u64 v[LEVELS], rr[LEVELS];
    if (nb > 0) {
        u64 h2 = mmul(h, h, q, qi);
        u64 y = mmul(g8, mmul(h2, h2, q, qi), q, qi);               // 2^(-4 n0)
        u64 cst = madd(big2, madd(big2, big2, q), q);              // 6 * 2^m
        u64 rb = r8;
        for (int b = 0; b < nb; ++b) {
            v[b] = mmul(cst, y, q, qi);
            rr[b] = rb;
            y = mmul(y, y, q, qi);
            rb = mmul(rb, rb, q, qi);
            cst = mhalf(cst, q);
        }
    }
    u64 i3 = mmul((q % 3 == 1) ? (2 * q + 1) / 3 : (q + 1) / 3, r2, q, qi);   // 1/3
    u64 i12 = mhalf(mhalf(i3, q), q);
    u64 i12x2 = madd(i12, i12, q), i12x4 = madd(i12x2, i12x2, q);
    u64 c512 = madd(i12x4, i12, q), c712 = madd(c512, i12x2, q);

    u64 sc = e1 ? 0 : mmul(q / p, r2, q, qi);     // p^(E-1)
    u64 jm = mmul(j0, r2, q, qi);
    u64 jr = j0 % p;
    u64 nn = 0, dd = one, j = j0;
    u32 step = (u32)((2 * (p % 120)) % 120);
    u32 nm = (u32)(n0 % 120);

    for (u64 it = 0; it < len; ++it) {
        u64 n = p * j;
        u32 n8 = nm & 7;
        bool five = (nm % 5) == 0, three = (nm % 3) == 0;
        u64 x = 0;
        if (!five) {                              // g = 3
            if (n8 == 3) x = s3;
            else if (n8 == 7) x = mneg(s3, q);
        } else {
            u32 n40 = nm % 40;
            if (n40 == 5) x = mmul(s3, c512, q, qi);
            else if (n40 == 15) x = mneg(mmul(s3, c712, q, qi), q);
            else if (n40 == 25) x = mneg(mmul(s3, c512, q, qi), q);
            else x = mmul(s3, c712, q, qi);
        }
        s3 = mmul(s3, r3, q, qi);
        if (4 * n <= k0) {                        // g = 4
            x = madd(x, s4, q);
            s4 = mmul(s4, r4, q, qi);
            if (5 * n <= k0) {                    // g = 5
                if (!three) x = madd(x, (n8 == 1 || n8 == 3) ? s5 : mneg(s5, q), q);
                s5 = mmul(s5, r5, q, qi);
                if (6 * n <= k0) {                // g = 6
                    if (!five) {
                        if ((n8 & 3) == 1) x = madd(x, s6, q);
                    } else {
                        x = madd(x, mmul(s6, (nm % 20 == 5) ? c712 : c512, q, qi), q);
                    }
                    s6 = mmul(s6, r6, q, qi);
                    while (nb > 0 && n > (k0 >> (nb + 2))) --nb;   // g = 8 * 2^b
                    for (int b = 0; b < nb; ++b) {
                        if (!three) x = madd(x, v[b], q);
                        v[b] = mmul(v[b], rr[b], q, qi);
                    }
                    if (10 * n <= k0) {           // g = 10
                        if (!three) x = madd(x, ((n8 & 3) == 1) ? s10 : mneg(s10, q), q);
                        s10 = mmul(s10, r10, q, qi);
                    }
                }
            }
        }
        if (x != 0) {
            u64 um = jm;
            if (!e1) {
                if (jr != 0) {
                    x = mmul(x, sc, q, qi);
                } else {                          // p divides j: strip its powers
                    u64 u = j, pv = p;
                    while (u % p == 0) { u /= p; pv *= p; }
                    um = mmul(u, r2, q, qi);
                    x = mmul(x, mmul(q / pv, r2, q, qi), q, qi);
                }
            }
            nn = madd(mmul(nn, um, q, qi), mmul(x, dd, q, qi), q);
            dd = mmul(dd, um, q, qi);
        }
        if (!e1) {
            jr += 2;
            if (jr >= p) jr -= p;
        }
        jm = madd(jm, two, q);
        j += 2;
        nm += step;
        if (nm >= 120) nm -= 120;
    }
    u64 inv = mpow(dd, phi - 1, one, q, qi);
    return mmul(mmul(nn, inv, q, qi), 1, q, qi);
}

// Primes above sqrt(l3): modulus p, every odd cofactor up to l3/p.
extern "C" __global__ void large_primes2(const u64* p, u64* out, u32 n, u64 m, u64 k0, u64 l3) {
    u32 i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= n) return;
    u64 q = p[i];
    u64 c = (l3 >> 53) ? l3 / q : (u64)((double)l3 / (double)q);
    while (c * q > l3) --c;
    while ((c + 1) * q <= l3) ++c;
    out[i] = item2(q, q, q - 1, 1, (c + 1) >> 1, m, k0);
}

extern "C" __global__ void small_items2(const u64* p, const u64* q, const u64* phi,
                                        const u64* j0, const u32* len, u64* out, u32 n,
                                        u64 m, u64 k0) {
    u32 i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= n) return;
    out[i] = item2(p[i], q[i], phi[i], j0[i], len[i], m, k0);
}

// Every prime is larger than sqrt(la): modulus p, all odd cofactors up to la/p.
extern "C" __global__ void large_primes(const u64* p, u64* out, u32 n,
                                        u64 m, u64 la, u64 lb, u64 lc, u64 ld) {
    u32 i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= n) return;
    u64 q = p[i];
    u64 c = (la >> 53) ? la / q : (u64)((double)la / (double)q);   // la / q, then exact
    while (c * q > la) --c;
    while ((c + 1) * q <= la) ++c;
    out[i] = item(q, q, q - 1, 1, (c + 1) >> 1, m, la, lb, lc, ld);
}

// Explicit work items: prime, modulus p^E, phi(p^E), first cofactor, run length.
extern "C" __global__ void small_items(const u64* p, const u64* q, const u64* phi,
                                       const u64* j0, const u32* len, u64* out, u32 n,
                                       u64 m, u64 la, u64 lb, u64 lc, u64 ld) {
    u32 i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= n) return;
    out[i] = item(p[i], q[i], phi[i], j0[i], len[i], m, la, lb, lc, ld);
}
