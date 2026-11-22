//! piwindow: hex digits of pi at any position, without the digits before it.
//!
//!     piwindow <position> <digits> [--formula euler|new] [--device auto|gpu|cpu]
//!              [--out FILE] [--expect HEX] [--check FILE] [--threads N] [--block-bits N]
//!     piwindow --check2 <position>     (self-test of the new formula's routines)
//!
//! Prints <digits> hex digits of pi starting right after hex position <position>.
//!
//! Two formulas are built in. `euler` is pi/4 = 2*atan(1/3) + atan(1/7). `new` is that
//! plus a logarithm series for zero (pi_formula_theorem.md, Part III): it needs about
//! 12% fewer primes, at the price of more work for each of the small ones.
//!
//! Method (prime form of the chosen series):
//!   frac(2^m * pi) = sum over odd primes p of C_p / p^E  (mod 1)  +  short tail
//! A word thread sieves primes and computes every C_p with machine-word arithmetic
//! (on the GPU when there is one). The main thread sums the resulting fractions
//! exactly in blocks with product trees, one big division per block. The two run
//! as a pipeline, so memory stays proportional to the window, not the position.

mod closed;
mod gpu;
mod mont;
mod sieve;
mod tree;
mod word;
mod word2;

use malachite_base::num::arithmetic::traits::{ModPowerOf2, PowerOf2};
use malachite_base::num::basic::traits::Zero;
use malachite_nz::natural::Natural;
use rayon::prelude::*;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{sync_channel, SyncSender, TryRecvError};
use std::sync::Arc;
use std::time::Instant;
use word::{Consts, Items, SERIES};
use word2::Consts2;

// The big-number stage allocates constantly from every thread; the default
// Windows heap serializes that.
#[global_allocator]
static ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

const GUARD: u64 = 64;
/// Longest cofactor run handled as a single pass over one prime.
const CHL: u64 = 2048;
/// Run length of one work item for the primes below that.
const CHS: u64 = 16384;
const ITEM_CAP: usize = 1 << 16;
/// Integers per parallel sieve task.
const SUBW: u64 = 1 << 22;

#[derive(Default)]
struct Stats {
    sieve_ns: AtomicU64,
    word_ns: AtomicU64,
    primes: AtomicU64,
}

enum Msg {
    Info(String),
    /// Numerators and denominators of head fractions, ready to be summed.
    Fractions(Vec<u64>, Vec<u64>),
}

/// Which series for pi the window is computed from.
#[derive(Clone, Copy)]
enum Formula {
    /// pi/4 = 2 atan(1/3) + atan(1/7).
    Euler(Consts),
    /// The cheaper formula of Part III (word2.rs).
    New(Consts2),
}

impl Formula {
    /// Largest odd index of the head; every prime up to here may be needed.
    fn reach(&self) -> u64 {
        match self {
            Formula::Euler(k) => k.la,
            Formula::New(k) => k.l3,
        }
    }
}

enum Engine {
    Cpu,
    Gpu(gpu::Gpu),
}

impl Engine {
    fn large(&self, primes: &[u64], f: &Formula) -> Vec<u64> {
        match (self, f) {
            (Engine::Cpu, Formula::Euler(k)) => primes
                .par_iter()
                .map(|&p| word::item(p, p, p - 1, 1, (k.la / p + 1) / 2, k))
                .collect(),
            (Engine::Cpu, Formula::New(k)) => primes
                .par_iter()
                .map(|&p| word2::item2(p, p, p - 1, 1, (k.l3 / p + 1) / 2, k))
                .collect(),
            (Engine::Gpu(g), Formula::Euler(k)) => g.large(primes, k),
            (Engine::Gpu(g), Formula::New(k)) => g.large2(primes, k),
        }
    }

    fn small(&self, it: &Items, f: &Formula) -> Vec<u64> {
        match (self, f) {
            (Engine::Cpu, Formula::Euler(k)) => (0..it.p.len())
                .into_par_iter()
                .map(|i| word::item(it.p[i], it.q[i], it.phi[i], it.j0[i], it.len[i] as u64, k))
                .collect(),
            (Engine::Cpu, Formula::New(k)) => (0..it.p.len())
                .into_par_iter()
                .map(|i| word2::item2(it.p[i], it.q[i], it.phi[i], it.j0[i], it.len[i] as u64, k))
                .collect(),
            (Engine::Gpu(g), Formula::Euler(k)) => g.small(it, k),
            (Engine::Gpu(g), Formula::New(k)) => g.small2(it, k),
        }
    }
}

fn isqrt(n: u64) -> u64 {
    let mut r = (n as f64).sqrt() as u64;
    while r * r > n {
        r -= 1;
    }
    while (r + 1) * (r + 1) <= n {
        r += 1;
    }
    r
}

/// Sieve primes and compute every C_p, sending finished fractions downstream.
fn word_stage(
    device: String,
    k: Formula,
    target_primes: u64,
    no_closed: bool,
    tx: SyncSender<Msg>,
    st: Arc<Stats>,
) {
    let engine = match device.as_str() {
        "cpu" => Engine::Cpu,
        want => match gpu::Gpu::new() {
            Ok(g) => {
                let _ = tx.send(Msg::Info(format!("word stage on GPU: {}", g.name)));
                Engine::Gpu(g)
            }
            Err(e) if want == "auto" => {
                let _ = tx.send(Msg::Info(format!("no GPU ({}); word stage on CPU", e)));
                Engine::Cpu
            }
            Err(e) => panic!("GPU requested but unavailable: {}", e),
        },
    };
    if let Engine::Cpu = engine {
        if device == "cpu" {
            let _ = tx.send(Msg::Info("word stage on CPU".into()));
        }
    }
    let la = k.reach();
    if la < 3 {
        return;
    }
    // New formula: a prime p = 1 (mod 4) above k0/4 has no term at all.
    let skip_above = match k {
        Formula::Euler(_) => u64::MAX,
        Formula::New(c) => c.k0 / 4,
    };
    let root = isqrt(la) + 1;
    // Primes up to `split` get explicit work items; above it each prime is one pass.
    let split = root.max(la / (2 * CHL) + 1).min(la);
    let base = Arc::new(sieve::odd_primes_upto(split.max(root)));
    let nsmall = base.partition_point(|&p| p <= split);

    // ---- a separate thread sieves the large primes in batches, ahead of the engine
    let (ptx, prx) = sync_channel::<Vec<u64>>(2);
    let siever = {
        let (base, st) = (base.clone(), st.clone());
        std::thread::spawn(move || {
            let mut lo = split;
            while lo < la {
                let width = ((target_primes as f64 * (lo.max(3) as f64).ln()) as u64).max(SUBW);
                let hi = la.min(lo.saturating_add(width));
                let t = Instant::now();
                let mut ranges = Vec::new();
                let mut a = lo;
                while a < hi {
                    let b = hi.min(a + SUBW);
                    ranges.push((a, b));
                    a = b;
                }
                let parts: Vec<Vec<u64>> = ranges
                    .par_iter()
                    .map(|&(a, b)| {
                        if a >= skip_above {
                            sieve::primes_in_3mod4(a, b, &base)
                        } else if b <= skip_above {
                            sieve::primes_in(a, b, &base)
                        } else {
                            let mut v = sieve::primes_in(a, skip_above, &base);
                            v.extend(sieve::primes_in_3mod4(skip_above, b, &base));
                            v
                        }
                    })
                    .collect();
                let primes = parts.concat();
                st.sieve_ns.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
                if ptx.send(primes).is_err() {
                    return;
                }
                lo = hi;
            }
        })
    };

    // ---- small primes
    let t = Instant::now();
    let mut cs = vec![0u64; nsmall];
    let mut qs = Vec::with_capacity(nsmall);
    // The smallest primes have the longest cofactor runs, but modulo p^v those
    // runs are periodic: closed.rs sums one period instead of the whole run.
    let ncf = match k {
        Formula::Euler(_) if no_closed => 0,
        Formula::Euler(_) => base.partition_point(|&p| p <= (isqrt(la / 8) / 4).min(split)),
        // 3 and 5 always go this way: the fast routine divides by 3 and assumes p > 5.
        Formula::New(_) if no_closed => base.partition_point(|&p| p <= 5),
        Formula::New(c) => base.partition_point(|&p| p <= (isqrt(c.k0 / 330) / 4).max(5).min(split)),
    };
    let t_closed = Instant::now();
    let closed: Vec<(u64, u64)> = base[..ncf]
        .par_iter()
        .map(|&p| match k {
            Formula::Euler(c) => closed::small_prime(p, &c),
            Formula::New(c) => word2::small_prime2(p, &c),
        })
        .collect();
    for (i, &(c, q)) in closed.iter().enumerate() {
        cs[i] = c;
        qs.push(q);
    }
    let closed_s = t_closed.elapsed().as_secs_f64();
    let mut items = Items::default();
    let flush = |items: &mut Items, cs: &mut Vec<u64>| {
        // Order the items by where their run starts. Neighbouring GPU threads then
        // have the same series active, instead of each paying for all of them.
        let mut idx: Vec<u32> = (0..items.p.len() as u32).collect();
        idx.sort_unstable_by_key(|&i| items.p[i as usize] * items.j0[i as usize]);
        let pick = |v: &Vec<u64>| idx.iter().map(|&i| v[i as usize]).collect::<Vec<u64>>();
        let sorted = Items {
            p: pick(&items.p),
            q: pick(&items.q),
            phi: pick(&items.phi),
            j0: pick(&items.j0),
            len: idx.iter().map(|&i| items.len[i as usize]).collect(),
            owner: idx.iter().map(|&i| items.owner[i as usize]).collect(),
        };
        let out = engine.small(&sorted, &k);
        for (i, &v) in out.iter().enumerate() {
            let o = sorted.owner[i] as usize;
            let s = cs[o] + v;
            cs[o] = if s >= sorted.q[i] { s - sorted.q[i] } else { s };
        }
        items.clear();
    };
    for &p in base[ncf..nsmall].iter() {
        let mut q = p;
        while q <= la / p {
            q *= p;
        }
        qs.push(q);
    }
    st.word_ns.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);

    // The item primes are worked through one batch at a time, and only while no
    // batch of large primes is waiting: the siever sets the pace of the whole run,
    // so the items fit into time the engine would otherwise spend idle.
    let (mut next, mut done) = (ncf, 0u64); // next small prime, cofactors done for it
    let mut items_s = 0f64;
    let mut small_batch = |cs: &mut Vec<u64>| -> bool {
        let t = Instant::now();
        while next < nsmall && items.p.len() < ITEM_CAP {
            let p = base[next];
            let q = qs[next];
            let total = (la / p + 1) / 2; // odd cofactors 1 ..= la/p
            while done < total && items.p.len() < ITEM_CAP {
                let len = CHS.min(total - done);
                items.p.push(p);
                items.q.push(q);
                items.phi.push(q / p * (p - 1));
                items.j0.push(1 + 2 * done);
                items.len.push(len as u32);
                items.owner.push(next as u32);
                done += len;
            }
            if done >= total {
                next += 1;
                done = 0;
            }
        }
        flush(&mut items, cs);
        st.word_ns.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
        items_s += t.elapsed().as_secs_f64();
        next < nsmall
    };
    let large_batch = |primes: Vec<u64>| -> bool {
        let t = Instant::now();
        let c = engine.large(&primes, &k);
        st.word_ns.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
        st.primes.fetch_add(primes.len() as u64, Ordering::Relaxed);
        tx.send(Msg::Fractions(c, primes)).is_ok()
    };
    let mut small_left = ncf < nsmall;
    loop {
        match prx.try_recv() {
            Ok(primes) => {
                if !large_batch(primes) {
                    break;
                }
            }
            Err(TryRecvError::Empty) if small_left => small_left = small_batch(&mut cs),
            Err(TryRecvError::Empty) => match prx.recv() {
                Ok(primes) => {
                    if !large_batch(primes) {
                        break;
                    }
                }
                Err(_) => break,
            },
            Err(TryRecvError::Disconnected) => break,
        }
    }
    while small_left {
        small_left = small_batch(&mut cs);
    }
    let _ = tx.send(Msg::Info(format!(
        "  small primes: {} by period in {:.2}s, {} by items in {:.2}s",
        ncf,
        closed_s,
        nsmall - ncf,
        items_s
    )));
    st.primes.fetch_add(nsmall as u64, Ordering::Relaxed);
    let _ = tx.send(Msg::Fractions(cs, qs));
    drop(prx);
    let _ = siever.join();
}

/// The convergent part of the cheaper formula: every term with k > k0.
fn tail2(k: &Consts2, bits: u64) -> (Natural, Natural) {
    let end = 2 * (k.m + bits + 4) + 2; // beyond this the terms are below 2^-bits
    let mut jobs = Vec::new();
    let mut a = k.k0 + 1;
    while a < end {
        let dbits = 64 - a.leading_zeros() as u64;
        let step = (2 * bits.max(4096) / dbits.max(2)).max(1);
        let b = end.min(a + step);
        jobs.push((a, b));
        a = b;
    }
    jobs.par_iter()
        .map(|&(a, b)| {
            let (neg, v) = tree::tail2_block(a, b, k.m, bits);
            if neg {
                (Natural::ZERO, v)
            } else {
                (v, Natural::ZERO)
            }
        })
        .reduce(|| (Natural::ZERO, Natural::ZERO), |x, y| (x.0 + y.0, x.1 + y.1))
}

/// The convergent part of the four series: (sum of positive blocks, sum of negative).
fn tail(k: &Consts, bits: u64) -> (Natural, Natural) {
    let mut jobs = Vec::new();
    for &(c, e0, kind) in SERIES.iter() {
        let top = k.m as i128 + e0 as i128;
        let mut a = (top.div_euclid(c as i128) + 1).max(0) as u64; // first negative exponent
        let end = ((top + bits as i128 + 2).div_euclid(c as i128) + 2).max(0) as u64;
        while a < end {
            let dbits = 64 - (2 * a + 1).leading_zeros() as u64;
            let step = (bits.max(4096) / dbits.max(2)).max(1);
            let b = end.min(a + step);
            jobs.push((c, e0, kind, a, b));
            a = b;
        }
    }
    jobs.par_iter()
        .map(|&(c, e0, kind, a, b)| {
            let (neg, v) = tree::tail_block(c, e0, kind, a, b, k.m, bits);
            if neg {
                (Natural::ZERO, v)
            } else {
                (v, Natural::ZERO)
            }
        })
        .reduce(|| (Natural::ZERO, Natural::ZERO), |x, y| (x.0 + y.0, x.1 + y.1))
}

struct Opts {
    n: u64,
    count: u64,
    device: String,
    out: Option<String>,
    expect: Option<String>,
    check: Option<String>,
    threads: Option<usize>,
    block_bits: Option<u64>,
    /// Walk every cofactor of the small primes instead of using their period.
    no_closed: bool,
    /// "euler" or "new".
    formula: String,
}

fn parse() -> Opts {
    let mut o = Opts {
        n: 1_000_000,
        count: 64,
        device: "auto".into(),
        out: None,
        expect: None,
        check: None,
        threads: None,
        block_bits: None,
        no_closed: false,
        formula: "euler".into(),
    };
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut pos = 0;
    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        let mut val = || {
            i += 1;
            args.get(i).cloned().unwrap_or_else(|| panic!("{} needs a value", a))
        };
        match a.as_str() {
            "--device" => o.device = val(),
            "--out" => o.out = Some(val()),
            "--expect" => o.expect = Some(val()),
            "--check" => o.check = Some(val()),
            "--threads" => o.threads = Some(val().parse().expect("--threads N")),
            "--block-bits" => o.block_bits = Some(val().parse().expect("--block-bits N")),
            "--no-closed" => o.no_closed = true,
            "--formula" => {
                o.formula = val();
                assert!(o.formula == "euler" || o.formula == "new", "--formula euler|new");
            }
            _ => {
                let v: u64 = a.replace('_', "").parse().expect("position and digits are integers");
                if pos == 0 {
                    o.n = v;
                } else {
                    o.count = v;
                }
                pos += 1;
            }
        }
        i += 1;
    }
    o
}

/// `piwindow --bench-tree`: single-thread cost of the fraction tree by size.
fn bench_tree() {
    let base = sieve::odd_primes_upto(50_000);
    let dens = sieve::primes_in(2_000_000_000, 2_000_000_000 + (1 << 25), &base);
    let nums: Vec<u64> = dens.iter().map(|&p| p / 3 + 12345).collect();
    let total = 1usize << 20;
    let mut prev = 0f64;
    eprintln!("fractions/tree  ns per denominator bit   added by last doubling");
    for lg in 1..=20 {
        let size = 1usize << lg;
        let t = Instant::now();
        let mut sink = 0u64;
        for c in 0..(total / size) {
            let (p, q) = tree::frac_sum(&nums[c * size..(c + 1) * size], &dens[c * size..(c + 1) * size]);
            sink ^= tree::low_limb(&p) ^ tree::low_limb(&q);
        }
        let per = t.elapsed().as_nanos() as f64 / (total as f64 * 31.0);
        eprintln!("{:>10}      {:>8.3}                 {:>8.3}   {}", size, per, per - prev, sink & 1);
        prev = per;
    }
}

/// `piwindow --check-closed <position>`: the periodic shortcut must give exactly
/// the same coefficient as walking every cofactor, for every prime tested.
fn check_closed(n: u64) {
    let k = Consts::new(4 * n);
    let limit = 60_000u64.min(k.la);
    let primes = sieve::odd_primes_upto(limit);
    let t = Instant::now();
    let fast: Vec<(u64, u64)> = primes.par_iter().map(|&p| closed::small_prime(p, &k)).collect();
    let t_fast = t.elapsed().as_secs_f64();
    let t = Instant::now();
    let slow: Vec<u64> = primes
        .par_iter()
        .map(|&p| {
            let mut q = p;
            while q <= k.la / p {
                q *= p;
            }
            word::item(p, q, q / p * (p - 1), 1, (k.la / p + 1) / 2, &k)
        })
        .collect();
    let t_slow = t.elapsed().as_secs_f64();
    let bad = fast.iter().zip(slow.iter()).filter(|(f, s)| f.0 != **s).count();
    eprintln!(
        "position {}: {} primes up to {}; mismatches {}; shortcut {:.2}s, full walk {:.2}s",
        n,
        primes.len(),
        limit,
        bad,
        t_fast,
        t_slow
    );
    if bad > 0 {
        for ((f, s), p) in fast.iter().zip(slow.iter()).zip(primes.iter()).filter(|((f, s), _)| f.0 != **s).take(5) {
            eprintln!("  p={} q={} shortcut={} walk={}", p, f.1, f.0, s);
        }
    }
}

/// `piwindow --check2 <position>`: for the cheaper formula, the fast routines must
/// give exactly the same coefficient as walking every term, for every prime tested.
fn check2(n: u64) {
    let k = Consts2::new(4 * n);
    let mut bad = 0u64;
    let mut tested = 0u64;
    // every prime up to a limit: period shortcut, and the item routine in chunks
    let limit = 4000u64.min(k.l3);
    let primes = sieve::odd_primes_upto(limit);
    let res: Vec<(u64, u64, u64, u64)> = primes
        .par_iter()
        .map(|&p| {
            let (want, q) = word2::reference(p, &k);
            let (fast, q2) = word2::small_prime2(p, &k);
            assert_eq!(q, q2);
            let mut it = u64::MAX;
            if p >= 7 {
                let phi = q / p * (p - 1);
                let total = (k.l3 / p + 1) / 2;
                let (mut done, mut acc) = (0u64, 0u64);
                while done < total {
                    let len = 1000u64.min(total - done);
                    acc = ((acc as u128 + word2::item2(p, q, phi, 1 + 2 * done, len, &k) as u128) % q as u128) as u64;
                    done += len;
                }
                it = acc;
            }
            (p, want, fast, it)
        })
        .collect();
    for &(p, want, fast, it) in &res {
        tested += 1;
        if want != fast || (it != u64::MAX && it != want) {
            bad += 1;
            if bad <= 8 {
                eprintln!("  p={} reference={} period={} item={}", p, want, fast, it as i64);
            }
        }
    }
    // primes around every boundary of the large range, as the engine calls them
    let base = sieve::odd_primes_upto(isqrt(k.k0) + 1);
    let mut probes = Vec::new();
    for g in [3u64, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 21, 25, 27, 32, 48, 64, 100, 250, 1000] {
        let c = k.k0 / g;
        if c > limit + 5000 {
            probes.extend(sieve::primes_in(c - 2500, (c + 2500).min(k.l3 + 1), &base));
        }
    }
    probes.sort_unstable();
    probes.dedup();
    let res: Vec<(u64, u64, u64)> = probes
        .par_iter()
        .map(|&p| {
            let (want, q) = word2::reference(p, &k);
            let got = if q == p { word2::item2(p, p, p - 1, 1, (k.l3 / p + 1) / 2, &k) } else { want };
            (p, want, got)
        })
        .collect();
    for &(p, want, got) in &res {
        tested += 1;
        if want != got {
            bad += 1;
            if bad <= 16 {
                eprintln!("  large p={} (p mod 8 = {}, k0/p = {}) reference={} item={}", p, p & 7, k.k0 / p, want, got);
            }
        }
    }
    eprintln!("position {}: k0 = {}, {} primes tested, mismatches {}", n, k.k0, tested, bad);
}

fn main() {
    if std::env::args().any(|a| a == "--bench-tree") {
        rayon::ThreadPoolBuilder::new().num_threads(1).build_global().unwrap();
        return bench_tree();
    }
    let argv: Vec<String> = std::env::args().collect();
    if let Some(i) = argv.iter().position(|a| a == "--check2") {
        let n = argv.get(i + 1).map(|s| s.replace('_', "").parse().expect("position")).unwrap_or(200_000);
        return check2(n);
    }
    if let Some(i) = argv.iter().position(|a| a == "--check-closed") {
        let n = argv.get(i + 1).map(|s| s.replace('_', "").parse().expect("position")).unwrap_or(10_000_000);
        return check_closed(n);
    }
    let o = parse();
    if let Some(t) = o.threads {
        rayon::ThreadPoolBuilder::new().num_threads(t).build_global().unwrap();
    }
    let threads = rayon::current_num_threads() as u64;
    let k = if o.formula == "new" {
        Formula::New(Consts2::new(4 * o.n))
    } else {
        Formula::Euler(Consts::new(4 * o.n))
    };
    let bits = 4 * o.count + GUARD;
    // Bits of denominator summed per block. Measured optimum: about two windows
    // for big windows (fewer divisions), and small blocks for small windows.
    let block = o.block_bits.unwrap_or(if bits <= 1 << 16 { bits.max(2048) } else { 2 * bits });
    let la_bits = (64 - k.reach().max(2).leading_zeros()) as u64;
    let target_primes = (2 * threads * block / la_bits).clamp(1 << 21, 1 << 26);

    let t0 = Instant::now();
    let st = Arc::new(Stats::default());
    let (tx, rx) = sync_channel::<Msg>(2);
    let worker = {
        let (device, st, no_closed) = (o.device.clone(), st.clone(), o.no_closed);
        std::thread::spawn(move || word_stage(device, k, target_primes, no_closed, tx, st))
    };

    let t = Instant::now();
    let (tail_pos, tail_neg) = match &k {
        Formula::Euler(c) => tail(c, bits),
        Formula::New(c) => tail2(c, bits),
    };
    let tail_s = t.elapsed().as_secs_f64();

    let mut acc = Natural::ZERO;
    let (mut tree_s, mut blocks, mut fractions) = (0f64, 0u64, 0u64);
    for msg in rx {
        match msg {
            Msg::Info(s) => eprintln!("{}", s),
            Msg::Fractions(nums, dens) => {
                if nums.is_empty() {
                    continue;
                }
                let t = Instant::now();
                let dbits = (64 - dens[dens.len() - 1].leading_zeros()) as u64;
                let per = (block / dbits.max(2)).max(2) as usize;
                acc += nums
                    .par_chunks(per)
                    .zip(dens.par_chunks(per))
                    .map(|(a, b)| tree::head_block(a, b, bits))
                    .reduce(|| Natural::ZERO, |x, y| x + y);
                tree_s += t.elapsed().as_secs_f64();
                blocks += nums.len().div_ceil(per) as u64;
                fractions += nums.len() as u64;
            }
        }
    }
    worker.join().expect("word stage failed");

    let modulus = Natural::power_of_2(bits);
    let total = ((acc + tail_pos).mod_power_of_2(bits) + &modulus - tail_neg.mod_power_of_2(bits))
        .mod_power_of_2(bits);
    let mut digits = format!("{:X}", total >> GUARD);
    if (digits.len() as u64) < o.count {
        digits = "0".repeat(o.count as usize - digits.len()) + &digits;
    }
    let secs = t0.elapsed().as_secs_f64();

    match &o.out {
        Some(path) => std::fs::write(path, &digits).expect("cannot write --out file"),
        None => println!("{}", digits),
    }
    eprintln!(
        "position {}, {} hex digits, formula {}: {:.2}s  ({} fractions, {} blocks)",
        o.n, o.count, o.formula, secs, fractions, blocks
    );
    eprintln!(
        "  word stage {:.2}s, sieve {:.2}s, big-number sums {:.2}s, tail {:.2}s",
        st.word_ns.load(Ordering::Relaxed) as f64 / 1e9,
        st.sieve_ns.load(Ordering::Relaxed) as f64 / 1e9,
        tree_s,
        tail_s
    );
    eprintln!(
        "  big-number thread time: trees {:.1}s, divisions {:.1}s (summed over {} threads)",
        tree::TREE_NS.load(Ordering::Relaxed) as f64 / 1e9,
        tree::DIV_NS.load(Ordering::Relaxed) as f64 / 1e9,
        threads
    );
    if let Some(e) = &o.expect {
        let e = e.to_uppercase();
        eprintln!("  expected start {}: {}", e, if digits.starts_with(&e) { "MATCH" } else { "MISMATCH" });
    }
    if let Some(path) = &o.check {
        let want = std::fs::read_to_string(path).expect("cannot read --check file");
        let want = want.trim().to_uppercase();
        let n = want.len().min(digits.len());
        let same = want[..n] == digits[..n];
        eprintln!("  compared {} digits with {}: {}", n, path, if same { "MATCH" } else { "MISMATCH" });
    }
}
