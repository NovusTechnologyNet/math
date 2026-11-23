# W2-Q18: proving that a specific large number is prime inside Lean 4 (state on 2026-11-22)

Marks: [READ] read on the source's own page, [SNIPPET] seen in a search result or an API/abstract
record only, [INFERRED] my own conclusion. Several sources came through a fetch tool that
summarizes the page, so "READ" means "read through that tool, not the raw bytes". Raw numbers
the project will rely on must be re-checked in the repositories.

## 1. Summary

1. Mathlib now has a primality tactic with a Lucas (Pratt-node) certificate checker (PR #45711,
   merged 2026-11-05) and a Pollard-rho producer for roughly 20-30 digits (PR #45899, merged
   2026-11-20). [READ] Larger primes need user-supplied factors of p-1 (recursively).
2. The best existing tool for big primes is PrimeCert (Bhavik Mehta, with contributions from
   another Mathlib contributor, MIT license): Pocklington plus the Brillhart-Lehmer-Selfridge
   variant that needs only a factored part F > N^(1/3) of N-1; kernel only, no native_decide;
   python script builds certificates. Its README shows a 60-digit example. [READ] I found no
   test of anything much larger in its public text.
3. Largest primes certified in Lean found: secp256k1 field prime and group order, 78 digits,
   Pratt tree of 15 certificates, about 1 minute total build (Lean 4.27). [READ]
4. Mathlib's Lucas-Lehmer file proves the Mersenne primes with exponent up to 4423 (1332
   digits). 9689 and 9941 pass locally but fail in CI with "deep recursion"; 11213 fails the
   same way locally. [READ] So the Lean frontier for a proved large prime is 2^4423-1.
5. Coq is far ahead: CoqPrime checks ECPP certificates (Primo output via the converter o2v);
   the README table runs from Mersenne 2281 (687 digits) up to exponent 216091 (65,050 digits),
   times from under 1 s to 8 h 27 min; a 1200-digit prime about 9 h, about 15 min on 20 cores
   when split. [READ]
6. No ECPP checker in Lean and no Primo/PARI-to-Lean translator was found (GitHub searches,
   two WebSearches). Isabelle has Pratt certificates (AFP, Wimmer-Noschinski); no Isabelle
   ECPP found. [READ for AFP; "not found" for the rest, weak]
7. Kernel arithmetic: Nat.add/sub/mul/div/mod/pow/gcd/shifts/land/lor/xor/beq/ble are
   GMP-accelerated in the kernel; Nat.pow needs an exponent below 2^32 and a result below
   128 MB; Nat.powMod is NOT a kernel primitive. [READ in type_checker.cpp] Kernel powMod
   costs: 1024-bit modulus about 1.5-15 ms depending on version; 8192 bits 45-240 ms;
   32768 bits (base 2) about 3.7 s with the pending speed-up PR. [READ, lean4 PR #15167]
8. Best realistic lead: kernel-check a Gaussian-Mersenne norm prime by a Proth-type test
   (one exponentiation, no factoring needed, see lead A) and Mersenne primes by Lucas-Lehmer
   in chunks beyond 4423. These are new to Lean as far as I could find.
9. Overlap with the project's own results: none. This is infrastructure for the "primes in
   our tables" side only.

## 2. What is known

### 2.1 Mathlib

- `Mathlib/NumberTheory/LucasPrimality.lean`: `lucas_primality` (a^(p-1)=1 and a^((p-1)/q)
  != 1 for every prime q | p-1 implies p prime), `reverse_lucas_primality`,
  `lucas_primality_iff`. Its TODO says to integrate Pratt certificates into norm_num. No
  Pocklington and no reduce_mod_char in that file. [READ]
- `Mathlib/Tactic/Primality/` (new, four files Lucas, Cert, Producers, Primality) from PR #45711:
  `LucasWitness` (root + list of prime factors of p-1), `lucasCheck`, `prime_of_lucasCheck`,
  tactic `primality` with a Config and CertMode; the proof term is closed by `reflBoolTrue`,
  i.e. the kernel evaluates the Boolean check. The author plans Pocklington next and
  possibly ECPP later; a client-side web page helps build certificate text because the Lean
  interpreter is too slow to factor. [READ]
- Kernel exponentiation inside it: `powMod` processes four bits of the exponent per step
  (b^e = (b^(e/16))^16 * b^(e%16), reduced mod m) using kernel Nat.pow/mod; there is a comment
  to switch to core `Nat.powMod` once lean4 PR #15167 lands. No size limits stated. [READ]
- PR #45899 producer: Pollard rho, Miller-Rabin, trial division, configurable `rhoSteps`;
  stated target "up to ~20-30 digits" without hints; test includes the Curve25519 field prime.
  PR #45840 merged the Fermat test with the factor-2 test (perf). [READ / SNIPPET]
- Plain `norm_num` for Nat.Prime is trial division in the kernel. Zulip 2024: works for 6-digit
  primes, a user hit trouble at 6-7 digits on a weak machine; Pratt generator existed
  unpolished then. [READ] The Erdos-647 arXiv abstract-level note says norm_num on a
  1.8e19 number costs about 2^31 kernel steps. [SNIPPET from WebSearch, not verified in the PDF text I extracted]
- `Mathlib/NumberTheory/Fermat.lean`: `pepin_primality` (3^(2^(2^n-1)) = -1 in ZMod F_n
  implies F_n prime) and `pepin_primality'`. No statement about which F_n were checked. No
  Proth theorem anywhere (search of the Mathlib source and a GitHub issue search for "Proth"
  returned nothing). [READ / not found]
- `Mathlib/NumberTheory/LucasLehmer.lean`: `lucas_lehmer_sufficiency` and `_necessity`;
  a norm_num extension `evalLucasLehmerTest` using kernel-reducible `sModNatTR`. Docs say
  `(2^4423 - 1).Prime` is proved and the squaring step is the bottleneck; the file suggests
  reducing mod 2^p-1 by folding (n mod 2^p + n div 2^p) to speed it up. [READ]
- `Archive/Examples/MersennePrimes.lean`: proved exponents 3, 5, 7, 13, 17, 19, 31, 61, 89,
  107, 127, 521, 607, 1279, 2203, 2281, 3217, 4253, 4423 (and 2 by decide); 11 and 23 shown
  composite. 9689 and 9941 commented out ("deep recursion" in CI, system dependent); 11213
  fails locally with kernel deep recursion. No timings in the file. [READ]
- Pocklington: a GitHub issue search in mathlib4 returned only the checker PR (mentions of
  Pocklington as planned). So Pocklington is not in Mathlib itself; it lives in PrimeCert. [READ / weak]

### 2.2 Outside Mathlib (Lean)

- PrimeCert (https://github.com/b-mehta/PrimeCert, in Reservoir, 13 stars, builds on Lean
  v4.36.0-rc2 as of 2026-11-06). Contents: `PrimeCert/Pocklington.lean`, `Pocklington3.lean`
  (cube-root variant), `PowMod.lean`, `Sieve*.lean`, `SmallPrimes.lean`, `MillerRabin/`.
  Syntax `pock% [...]` for small and `prime_cert% [...]` for large; `small{...}`/`pock3(...)`
  entries; `scripts/prime_cert.py` needs a factorization of N-1 (sympy, GNU factor, rho; for
  big ones the README says to factor on an online ECM page). [READ]
  The cube-root variant needs a fully factored even F | N-1 with F > N^(1/3), plus a sieve to a
  bound m and a non-square test on r^2 - 8s where R=(N-1)/F=2Fs+r. [READ]
  `powModK` is a Nat.rec accumulator with fuel b+1; its own header says Mathlib's norm_num
  PowMod is significantly slower. [READ]
- Lean core: `Nat.powMod` with GMP extern merged 2026-09-15 (PR #13490); kernel replay follows
  a well-founded definition. Open PR #15167 (windowed exponentiation) and issue #15166.
  Benchmarks in the PR (random odd moduli, base 2, kernel check): 32 bits 1.07 ms -> 0.07 ms;
  1024 bits 15.1 -> 1.5 ms; 8192 bits 239 -> 44.5 ms; 16384 bits 762 ms vs PrimeCert-style 1447
  ms; 32768 bits base 2 about 3.7 s; full-size bases at 24576/32768 bits timed out for both.
  The issue gives 255-bit: 7.35 ms (current) vs 1.59 ms (accumulator). [READ]
- secp256k1-primality-lean (github.com/wjbrob/secp256k1-primality-lean, updated 2026-11-16):
  p and n (78 digits) via 15 Pratt certificates; own `powMod` on Nat with fixed fuel and a
  bridge to ZMod; whole `lake build` about 1 min, order certificate about 15 s; norm_num ran
  out of memory; Sage supplied witnesses; axioms only propext, Choice, Quot.sound. [READ]
- Other Lean repositories found by name: a fork of PrimeCert, a front-end `guissmo/primecert-front`
  (2024), a Python ECPP prover with checker (unrelated to Lean). No Lean ECPP. [SNIPPET]
- Erdos-647 kernel certificate (arXiv 2608.17880): not about primes but shows how a
  hundred-million-line certificate is chunked: each chunk one `decide`, about 40 s per chunk,
  all recursion structural, GMP on literals, driver raises recursion/heartbeat limits. [READ]
  (Written with AI assistance, as it states.)

### 2.3 Coq and Isabelle

- CoqPrime (github.com/thery/coqprime): Pocklington certificates (C program based on ECM,
  suggested below 100 digits) and ECPP certificates (Primo in elliptic-curve-only mode, then
  OCaml `o2v` produces Coq); table of Mersenne primes from exponent 2281 to 216091 (65,050
  digits) with check times under 1 s to 8 h 27 min 25 s; 1200-digit prime about 9 h, about 15
  min on 20 cores with `o2v -split`. [READ] Theory: Thery-Hanrot, "Primality Proving with
  Elliptic Curves" (TPHOLs 2007) [SNIPPET].
- Isabelle: AFP "A Formalization of Pratt's Primality Certificates" (Wimmer, Noschinski),
  with an executable checker, efficient modular exponentiation, code generation and a
  `check-pratt-primes` command. [READ] No sizes stated in the text. No ECPP in Isabelle found.

### 2.4 Certificate formats and generators

- PARI/GP `primecert(N)`: default ECPP (Atkin-Morain) certificate: vector of
  [N_i, t_i, s_i, a_i, P_i], final prime at most 2^64; flag 1 gives an N-1 (Pocklington-
  Lehmer) certificate, "very slow"; `primecertisvalid` checks; `primecertexport` formats
  0 human, 1 Primo format 4, 2 Magma; N-1 certificates cannot be exported. Timing from the
  docs: a 600-digit number 24 s direct; `isprime` on 1000 digits 15-30 min. [READ]
- Primo 4.3.3 (Dec 2020): up to 50,000 digits, up to 64 processors on Linux; no converter to
  proof assistants mentioned on its page. [READ]
- Largest ECPP-proved prime on Wikipedia (as of Nov 2025): repunit R(109297), 109,297 digits
  (fastECPP, Enge's CM). [SNIPPET]
- OpenPFGW: I did not fetch its documentation; it gives PRP and N+-1 proofs when enough of
  N+-1 is factored (from memory, [INFERRED], not verified).
- Translators to Lean: none found. The only bridge that exists is Primo -> Coq (`o2v`).
  PrimeCert's own script is the only generator that emits Lean text. [not found; weak]

### 2.5 Interesting primes: what is proved and how

- Wagstaff (2^k+1)/3: proved up to k=83339; later terms are probable only; a(30), k=42737,
  was proved by FastECPP. [SNIPPET, OEIS A000978]
- Gaussian-Mersenne norms (A057429): terms listed up to 15317227. [SNIPPET]
- Repunits and variants: OEIS data lists indices only; PARI `isprime` vs `ispseudoprime` per
  sequence. [SNIPPET]
- Primes in the digits of pi: my OEIS query returned base-4/base-6/binary variants
  (A065840, A065832, A065574), not the decimal one; the decimal prefix primes I did not
  verify (from memory the third has 6 digits, 314159, and the next has 41). [not found; check]

## 3. What is open (precise)

- No kernel-checked ECPP in any Lean library (not found; PrimeCert/Mathlib authors list ECPP
  only as future work: stated by the Mathlib PR author). Open engineering problem.
- Mersenne exponents above 4423 in Lean: stated as fails by the Archive file (deep recursion).
  Whether chunking removes the barrier is untested (not found).
- Proth/Pocklington with a factored N-1 for special-form numbers inside Mathlib: not found.
- Speed of kernel powMod beyond about 30000 bits with full-size bases: PR #15167 reports
  timeouts, so a prime of 10,000 digits via exponent a^((N-1)/q) with q small is out of reach
  for generic Lucas steps with the present kernel. [READ for the timeout, INFERRED for the consequence]

## 4. Leads for this project, ranked

### A. Gaussian-Mersenne (and Eisenstein-Mersenne) norm primes by a Proth test, kernel-checked

Statement: for the primes p in the Gaussian-Mersenne list, N = 2^p - 2^((p+1)/2) + 1 (or with
+) is prime, proved in Lean with no hypothesis.
Why it fits [INFERRED]: N - 1 = 2^((p+1)/2) * (2^((p-1)/2) -+ 1) = k*2^n with k < 2^n, so
Proth's theorem applies: one witness a (a quadratic non-residue) with a^((N-1)/2) = -1 mod N
proves N prime. No factoring, no certificate tree, just about p/2+... squarings (the exponent
is (N-1)/2, a power of 2 times k, so about p squarings plus a few multiplications by a).
Proth's theorem is not in Mathlib (not found), but it is a short corollary of the Lucas-style
argument already in Mathlib (a Pocklington proof with F = 2^n > sqrt N and the single
prime factor 2). One must prove it (days). Cost: each step is a GMP mult/mod of a p-bit number;
for p up to about 10^4 that is under a few seconds of GMP; the real limit is kernel recursion
depth ("deep recursion" at about 11000 steps in the Lucas-Lehmer case), handled by chunking:
the 647 paper uses chunk theorems composed by transitivity, about 40 s per chunk.
Size: Proth lemma days; first 10-20 Gaussian-Mersenne exponents trivial; exponents to a few
thousand (primes of about 10^3 digits, 3000 bits... p ~ 4000) weeks at worst; to p ~ 10^5
a chunked certificate of 10^5 steps with 10^5-bit literals (certificate itself megabytes)
may need hours on 24 cores (guess, [INFERRED], to be measured).
What would be new: nothing like it found in Mathlib/Lean/Reservoir; a formal Proth theorem
plus the first kernel-checked proof that Gaussian-Mersenne norms are prime beyond toy sizes.
Modest novelty, but the primes are "named" and tied to the project's Gaussian/cyclotomic
interest, and the same code covers Fermat primes F_n (Pepin exists in Mathlib; F_n for n<=4
are trivial) and Proth primes in general.

### B. Mersenne primes beyond 4423 by chunked Lucas-Lehmer

Statement: (2^p - 1).Prime for p = 9689, 9941, 11213, 19937, 21701, ... in Lean without
native_decide. Mathlib's file says the first two work locally and the third fails with kernel
deep recursion. Fit: the existing `evalLucasLehmerTest` / `sModNatTR`; the change is to cut
the p-2 squarings into segments, each a `decide`-style lemma on literals (as in the 647 paper), with a short soundness
lemma for the segmented iteration (and optionally the fold n mod 2^p + n div 2^p instead of
%). Size: days to a week for a few thousand more; each step squares a p-bit number
(GMP mult of 11213-bit numbers is microseconds, so 10^4-10^5 steps run in seconds to
minutes of pure arithmetic; kernel term caching and memory for 10^5 distinct big literals
is the unknown) [INFERRED]. What is notable: pushes the Lean frontier from 1332 digits to
possibly 10^4+ digits, still far below the Coq frontier (65,050 digits, 8.5 h in 2000s hardware
classes, [READ] on the CoqPrime page, no date).

### C. A small ECPP (Goldwasser-Kilian/Atkin-Morain) checker in Lean for the project's tables

Statement: prime numbers of 100-300 digits in the project's tables certified by an ECPP
certificate checked in the kernel. Fit: needs elliptic-curve group law on Weierstrass curves
mod N inside the kernel (the secp256k1 repo already has inverse-free add/double step lemmas,
a 445-step chain checked by decide, for a fixed 256-bit case: reuse idea) and a proof of the
Goldwasser-Kilian criterion; Mathlib has the elliptic-curve group law over fields, but the
criterion for a modulus N not known prime needs a projective-line argument (CoqPrime did
exactly this, which gives a plan). Certificates: PARI `primecert` + a Python translator
written by us from the array format (documented above) to Lean literals; the checker
verifies everything, so the generator is not trusted. Size: weeks to months for the
formalization; a 300-digit certificate has about 1000 bits/ 10 stages, trivial for the kernel
(one scalar multiplication of 1000 bits per stage, about 1500 point operations on 1000-bit numbers).
New: no Lean ECPP found; but it is a general infrastructure piece, not tied to pi results.

### D. Use PrimeCert as is for primes whose N-1 is easy

For primes with a large smooth part of N-1 (up to 100 digits with PARI factoring; beyond with
ECM), PrimeCert's cube-root variant needs only one third of the digits of N-1 factored. Size:
days (a driver script). Prime candidates: the project's table entries; note that this
proves nothing new about pi, it just removes "probable" from a table. Time reference: the
Lucas tree at 78 digits builds in about 1 minute. Up to a few hundred digits, expect
kernel time dominated by 10-30 modular exponentiations per level at 1024-bit scale about 1.5-15
ms each [READ for per-powMod timings, INFERRED for the sum]: seconds. The real cost is
finding the factorization (not the kernel).

### E. Pi-digit primes, repunit primes, Wagstaff

Pi-digit prime of 16208 or more digits: no special form, N-1 unfactorable; only ECPP
applies (lead C) and a 16000-digit ECPP is a multi-core-month computation by PARI/Primo
(Primo page: 50,000 digits max; PARI docs: 1000 digits 15-30 min, scaling about n^4 so 16000
digits about 16^4 times 20 min is tens of years of single core, INFERRED: out of reach).
Only the first 41-digit pi prime is realistic (Pratt/PrimeCert). Repunits R(n) prime (n=19,
23, 317, 1031, from memory): N-1 = 10*R(n-1)... needs factoring, so ECPP; R(317) (317 digits)
and R(1031) are achievable only with ECPP (lead C). Wagstaff (2^p+1)/3: N-1 = 2*(2^p-2)/3 =
2(2^(p-1)-1)/3, algebraically factorable only partly, so cube-root Pocklington helps for
small p only. [INFERRED]

## 5. Overlap or conflict with the project's results

None. This thread is orthogonal to the BBP-type classification. The one connection is the
project's tables of primes: Statement G for bases >= 5 (prime lists "computed only") could
be upgraded for the specific primes involved if they are certified in the kernel.

## 6. Sources

- https://github.com/b-mehta/PrimeCert , https://reservoir.lean-lang.org/@b-mehta/PrimeCert
- https://github.com/leanprover-community/mathlib4/pull/45711 , /pull/45899 , /pull/45840
- https://github.com/leanprover-community/mathlib4 (Mathlib/NumberTheory/LucasPrimality.lean,
  LucasLehmer.lean, Fermat.lean, Tactic/Primality/Lucas.lean, Archive/Examples/MersennePrimes.lean)
- https://github.com/leanprover/lean4/pull/13490 , /pull/15167 , /issues/15166 ,
  src/kernel/type_checker.cpp
- https://github.com/wjbrob/secp256k1-primality-lean
- https://leanprover-community.github.io/archive/stream/116395-maths/topic/Practical.20ways.20to.20prove.20Nat.2EPrime.20N.html
- https://arxiv.org/pdf/2608.17880 (Erdos 647 kernel certificate)
- https://github.com/thery/coqprime
- https://www.isa-afp.org/browser_info/current/AFP/Pratt_Certificate/document.pdf
- https://pari.math.u-bordeaux.fr/dochtml/html/Arithmetic_functions.html
- https://www.ellipsa.eu/public/primo/primo.html
- OEIS A000978, A057429, A182300, A331861-A331869, A065840 (via oeis.org/search)
- https://en.wikipedia.org/wiki/Elliptic_curve_primality (record claim, snippet)

Page content addressed to me: none seen.

## 7. Search log

WebSearch (3): 1 "Lean 4 Mathlib Pratt certificate primality large prime kernel"; 2 "Lean 4
elliptic curve primality proving ECPP certificate kernel-checked formalization"; 3 "Isabelle
formalized primality certificate ECPP Atkin Morain verified checker largest prime".

Endpoint/fetch queries (about 60 fetches, of which about 40 returned useful content; failures
noted): 
1-7 GitHub repo search (primality certificate lean4; PrimeCert; pocklington lean; ecpp lean4;
primo converter; isabelle ecpp; lean4 primality pocklington; lean mersenne) - mostly empty;
8-10 GitHub issue search in mathlib4 (primality certificate; Pratt; LucasLehmer; Proth;
Pocklington; norm_num large primes); 11-12 lean4 issue search Nat.powMod; PR 15167, 13490,
issue 15166; mathlib PRs 45899, 45711; PrimeCert page, README (404 on main, found via
Reservoir), contents of three directories, commits, test and source files (several 404 on main,
Pocklington3/PowMod/Test via master); Mathlib raw files LucasLehmer, MersennePrimes, Fermat,
LucasPrimality, Lucas.lean (Primality.lean and MathlibTest 404); lean4 type_checker.cpp; secp
repo; Zulip archive; arXiv PDF 2608.17880 (text via pdftotext); AFP Pratt PDF (pdftotext);
CoqPrime; Crossref ECPP query; PARI docs; Primo page; OEIS queries (pi prefix primes;
Gaussian Mersenne; Wagstaff; repunit). Refused or failed: OpenAlex (429), Semantic Scholar
(429), arXiv API (429, twice), GitHub code search (401), GitHub contents of mathlib4 (403),
api.github search/repositories for Coq (403).
Totals: WebSearch calls 3; endpoint queries about 60 (counting the failed ones).
