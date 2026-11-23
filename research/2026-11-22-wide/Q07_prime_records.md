# Q07: computational records about primes (pi(x), gaps, Goldbach, tuples, certification)

Date of pass: 2026-11-22. Marks: [READ] = read on the source page/PDF through the fetch tool
(note: the fetch tool returns a model-made digest of a page, so "read" means "digest of the
full page"); [SNIPPET] = only in a search result / API record; [INFERRED] = my own conclusion
or estimate; [MEASURED] = I ran it myself here (Lean experiments, section 2.7).
Web pages contained no text addressed to me, except that GitHub repositories of several
"Goldbach / twin prime proof in Lean" projects make claims I regard as not credible (see 5).

## 1. Summary

1. pi(x) record is x = 10^29 = 1,520,698,109,714,272,166,094,258,063 (Baugh and Walisch,
   announced 2022-02-28). 10^27 (2015-09-06), 10^28 (2020-08-30) by the same pair. All with
   Walisch's primecount (Gourdon / Deleglise-Rivat style combinatorial method). [READ]
2. Verification status of the top values is thin. The primecount Records page says each result
   was computed twice with different "alpha" tuning parameters, nothing more; same code, same
   authors. Fully independent confirmation exists only up to 10^26 (Staple, separate code, two
   clusters, plus parity agreement with Lifchitz's unpublished algorithm). No second
   implementation and no parity check for 10^27, 10^28, 10^29 found. [READ]/[INFERRED]
3. Analytic (Platt/Buethe) method: unconditional pi(10^24) (Platt, 63,000 CPU hours, interval
   arithmetic) and pi(10^25) (Buethe et al.). Crossover with combinatorial method estimated at
   x ~ 4*10^31 by Platt, so the analytic route is not a desktop route. [READ]
4. Even Goldbach verified to 4*10^18 (Oliveira e Silva, Herzog, Pardi; reached April 2012),
   double-checked only to 4*10^17, effort about 782 single-core years. Nothing newer found;
   2026 GPU papers reach only 10^12 to 10^13. [READ]
5. Maximal prime gaps: 85 maximal gaps known, last is 1854 after 101412319996363309069
   (found 2026-05-08, verified 2026-05-22). Ranks 86-259 on the record list are unconfirmed
   (they are record-size gaps, not maximal ones). [READ]
6. Twin primes: pi_2(10^19) = 7237518093734545 entered OEIS A007508 in June 2026 and was
   corrected in July 2026, single contributor, so it is a prime candidate for "check me". [READ]
7. Certification: I found NO formally verified computation of pi(x) for large x, in any
   proof assistant (searched Lean, Coq, Isabelle; Mathlib has only the definition and Chebyshev
   style bounds). Certified small objects exist (Pratt certificates in Isabelle AFP and Lean).
   I measured that a naive kernel-evaluated count in Lean runs at roughly 10^4 elementary
   operations per second, so kernel-only certification stops near 10^6 to 10^7 without clever
   encoding. [MEASURED]/[INFERRED]
8. Best leads: (A) independent recomputation of pi(10^27) on 24 cores, weeks, with a memory
   measurement ladder first; (B) a tiered formally verified pi(10^n) ladder; (C) Lean-checked
   record objects (AP-27, a long Cunningham chain, CPAP-10) via Pratt-type certificates.

## 2. What is known

### 2.1 pi(x) records and who computed them

- Records page of primecount (primecount repository, doc/Records.md): pi(10^27)
  = 16,352,460,426,841,680,446,427,399 (2015-09-06); pi(10^28)
  = 157,589,269,275,973,410,412,739,598 (2020-08-30); pi(10^29)
  = 1,520,698,109,714,272,166,094,258,063 (2022-02-28). Credited to Kim Walisch and David
  Baugh. Also: 10^n-th prime for n = 23 (2015), 24 (2015), 25 (2022, Baugh);
  pi(2^87..2^92) (Baugh, 2018-2020); pi(e^48..e^62) (Baugh, 2015-2022); pi(10^(k/2)) for
  k = 47, 49, 51, 53. [READ]
- Same page: most records were run with a backup-capable build (version 6.4-backup) because
  runs last weeks or months; the page says 7.x is much faster, especially above 100 cores, and
  that all results were computed twice with different alpha tuning parameters. [READ]
- OEIS A006880 b-file (n = 0..29) ends with the same three values, verified by me against the
  b-file text; credit lines: 26 Staple (2014-12-02), 27 Baugh+Walisch via Greathouse
  (2016-06-01 in OEIS), 28 (2020-10-26), 29 (2022-02-28). [READ]
- OEIS A007053 (pi(2^n)): b-file to n = 92. n <= 75 Oliveira e Silva; 76-77 Franke et al.
  (2010); 78-80 first under RH (Franke et al.), then unconditional by Staple (2014); 81-86
  Staple; 87-92 Baugh with primecount. [READ]
- Staple, "The combinatorial algorithm for computing pi(x)", arXiv:1503.01839: time
  O(x^(2/3)/log^2 x), memory O(x^(1/3) log^2 x); computed pi(10^n) n <= 26 and pi(2^m) m <= 86.
  Hardware: IBM nodes, 16 cores, 64 or 128 GB. 10^26 took 2.98*10^7 node-seconds (about 15.1
  core-years) and 1.12*10^11 bytes per node with the first version; 4.16*10^10 bytes with the
  improved version of 2015-01. Table 3 gives 10^23: 2.2*10^5 node-s, 5.2*10^9 bytes (improved
  version). [READ]
- Staple's checking of the new values (10^26, 2^81..2^86): computed twice on separate
  clusters with different parameters; compared with li(x); parities of the new values agree
  with values computed by Lifchitz with an unpublished algorithm (suggested by Gerbicz).
  Values for 10^n n <= 25 and 2^m m <= 80 agreed with earlier authors. [READ]
- Platt, "Computing pi(x) analytically" (arXiv:1203.5712): rigorous implementation of the
  Lagarias-Odlyzko analytic method with interval arithmetic (MPFI), unconditional pi(10^24)
  = 18,435,599,767,349,200,867,866; about 63,000 CPU hours on a university cluster;
  sieve of 352,800 segments; the sum over zeros uses the first ~3.6*10^10 zeros made
  available by J. Bober; estimated crossover versus the combinatorial method at x ~ 4*10^31;
  Oliveira e Silva needed about a month on one machine for 10^23 with the combinatorial method.
  Agrees with the earlier conditional value of Buethe-Franke-Jost-Kleinjung. [READ]
- Buethe's page: 10^25 unconditional by a new variant of Franke's method; the values at 2^77,
  2^78, 2^79, 2^80 and 10^24 were first done assuming RH; the page says powers of 2 were not
  verified unconditionally (that page text predates Staple). [READ]
- MathWorld PrimeCountingFunction: independent computations by Oliveira e Silva and Gourdon
  agree for powers of 10 up to 10^22; an error was found in Gourdon's value at 10^23,
  settled by Oliveira e Silva on other hardware with other parameters. OEIS A006880 confirms:
  the original 10^23 entry was off by 14037804 (corrected 2007-11-28). [READ]
- Running times of current primecount (README benchmark, AMD EPYC Zen5, 32 cores, 4.5 GHz):
  Gourdon 0.72 s at 10^18, 10.7 s at 10^20, 42 s at 10^21, 159.5 s at 10^22. 128-bit limit:
  x <= 10^31 (man page). A tuning note dated 2026-11-04 (dual EPYC 7642, 96 cores, SMT off)
  gives all-thread times: D 283 s and S2_hard about 650 s at 10^23. [READ]
- primecount pull request 146 (merged 2026-10-27): hyperbola method for Gourdon's D, 17% faster
  at 10^20 on a Ryzen 9 9950X3D. So the code path used in 2026 differs from the one used for
  the 10^27..10^29 records. [SNIPPET]
- Memory: the man page asserts O(x^(2/3) log^3 x) memory for Gourdon (looks like a misprint;
  Staple states x^(1/3) type bounds); I found NO measured memory figure for primecount at
  10^27..10^29. [READ]: absent.

### 2.2 Maximal prime gaps

- Verified range: the Oliveira e Silva project found all gaps for all primes below 4*10^18
  (double-checked to 4*10^17) as a by-product of the Goldbach run; largest gap in that range
  1476, first found by him. [READ]
- Visser, arXiv:1904.00499 (2019): states the exhaustive search puts the 81st maximal gap
  beyond 2^64, so maximal gaps are known for all primes below 2^64. [SNIPPET + READ of
  abstract through digest]
- Current list (Andersen and Luhn, pzktupel.de, updated 2026-11-16): ranks 1-85 confirmed,
  85th is gap 1854 at 101412319996363309069, found by R. Smith with code by B. Kehrig
  (2026-05-08), verified 2026-05-22. Ranks 86-259 unconfirmed; top entry rank 259, gap
  16,045,848 (A. Hoeglund, 2024). The page does not state the exhaustive-search bound. [READ]
- Wikipedia (May 2026) table: 83rd 1676 after 20733746510561442863; 84th 1724 after
  68068810283234182907; 85th 1854 after 101412319996363309069. [READ]
- [INFERRED] A maximal gap can only be declared maximal after an exhaustive search of all
  smaller primes, so the community has exhaustive coverage to at least ~1.0*10^20, i.e. far
  past 2^64 (1.8*10^19). I did not find the page that documents who searched which ranges
  and whether each range was done twice. The Nicely table maintainer died in 2019; since then
  the list is kept by a mersenneforum group on GitHub (project site primegap-list-project).
  The exhaustive frontier for maximal gaps is therefore a community effort I could not audit;
  mersenneforum itself refused automated access (403).
- OEIS A005250 / A002386 / A000101 list 85 terms in b-files, with credit lines naming
  Nicholson, Ruiz-Huidobro, Kehrig; no errata shown. [READ]

### 2.3 Goldbach, twin primes, tuples, Cunningham chains, APs

- Binary Goldbach: checked to 4*10^18; double check only to 4*10^17; the project page says no
  more double-checking was planned (page note from May 2013). Interval of 10^12 near 10^18
  costs about 48 min on one 3.3 GHz Core i3 core; memory ~ 13*sqrt(N)/log N; total about
  781.8 core-years. Paper: Oliveira e Silva, Herzog, Pardi, Math. Comp. 83 (2014). [READ]
- 2026 GPU work: arXiv:2603.02621 (Llorente-Saguer, single author) exhaustive to 10^12 on one
  RTX 3070, claims O(1) memory, a CPU fallback "never invoked", no independent cross-check; a
  follow-up reaches 10^12 in 36.5 s on an RTX 5090 and 10^13 on four GPUs. These are 5 to 6
  orders of magnitude below the 2012 record, so nothing new in range. [READ abstract; SNIPPET
  for the follow-up]
- Weak (ternary) Goldbach: proved by Helfgott; Helfgott and Platt verified numerically up to
  8.875*10^30 (Experimental Math. 2013). [SNIPPET: Crossref record; READ in repo text]
- Twin primes: A007508 gives pi_2(10^n) to n = 19: a(17), a(18) by Oliveira e Silva (2008),
  a(19) = 7237518093734545 by Benjamin Chaffin (2026-06-02), corrected by him 2026-07-08.
  Earlier: a(16) corrected 2014 by Jacobsen; Nicely to 3*10^15, Sebah independently to
  5*10^15. a(19) has no second computer in the entry. [READ]
- Largest known twin primes: 2996863034895 * 2^1290000 +- 1 (388,342 digits, 2016) per
  Wikipedia. [READ]
- Cunningham chains (Wikipedia, as of 2026-10-28): longest known chain has length 20 (both
  kinds), by John Armitage 2026; 2026 saw many new records by Serge Batalov and others. [READ]
- Primes in AP: Wikipedia table lists AP-27 (19-digit terms, (4361612620 + 174505864 n) *
  23# + 184607939, n = 0..26), credited to Kai Presler / PrimeGrid; earlier AP-26 (Perichon
  2010), AP-25 (2008), AP-24 (2007). Wikipedia's prose and table disagree on the year (2019
  versus 2026); treat the date as uncertain. Consecutive-prime APs: CPAP-10 with 174 digits
  (Batalov, 2026). [READ]
- Prime k-tuplet records (largest tuples) could not be read: pzktupel.de returned only a
  title line. Not found.

### 2.4 Tables with known or suspected errors

- A006880: Lehmer's 10th term wrong by 1 (corrected); 11th term digit typo; 23rd term wrong by
  14037804 until 2007. [READ]
- A006988: a(23) corrected and a(24) added in 2015 using primecount (Baugh). [READ]
- A007508: a(16) fixed 2014, a(19) fixed within five weeks of being posted (2026). [READ]
- A000720 comments (digest of the page): a reversed inequality in the second Hardy-Littlewood
  comment, "equivalent to RH" overstated, a date mismatch for Ruiz-Sondow. [SNIPPET: digest
  only; should be checked by eye]
- Possible typo on primecount Records page for e^58: the digest returned a malformed digit
  group; may be an extraction artefact. Check the raw text. [READ, unverified]
- No OEIS table of pi(x), gaps or twin counts was found with a currently known open error;
  what exists is the pattern "values beyond 10^23 rest on one code base".

### 2.5 Formal and certified work (what exists)

- Mathlib: Nat.primeCounting defined as count of primes; finset lemmas; monotonicity and
  linear interval bound (Nat.primeCounting_add_le); a Chebyshev theta link (PR 32281, merged
  Dec 2025); no norm_num extension or computation tool for pi. [READ]
- Isabelle AFP "Pratt's Primality Certificates" (Wimmer, Noschinski 2013; updated 2024 with
  bulk checking). Lean: a project proving the secp256k1 field prime and group order prime with
  Pratt certificates without native_decide. Avigad et al. 2007: PNT (asymptotics) in Isabelle.
  [READ/SNIPPET]
- Lean 4 Goldbach-related GitHub projects found by search: gersh/ternary-goldbach-lean claims
  a full Lean proof of the ternary theorem conditional on a "finite and computational trust
  boundary" (93 named external atoms in the full build, no sorry; analytic inputs are
  Helfgott's; heavy computations enter as named admissions through a LeanCompCert pipeline);
  masalanice/goldbach-verified (certified computation "lane", no bound stated, replay script
  recomputes and diffs); nextsense-io/goldbach-lean4 (spectral scaffolding, no bound). [READ]
- openai/PrimeGaps186 (Lean 4, 2026): liminf of prime gaps <= 186, conditional on three
  explicit axioms (a Kloosterman bound, a correlation bound, and a numerical block of
  physical-integral bounds checked by a Python/FLINT certificate script, not discharged in
  Lean). AxiomMath/PrimeGapsLib (Lean, 2026): bounded gaps <= 246 and <= 600 from Bombieri-
  Vinogradov; large numerical certificates in a separate module. These concern bounded gaps,
  not the maximal-gap tables. [READ]
- DeepMind formal-conjectures: Lean statements of open problems; I found only one Cunningham
  file in the part of the tree I could scan. [READ]
- Nothing found for: a verified sieve counting primes to a large bound in Coq/Isabelle/Lean
  (several searches, see log), a verified Meissel-Lehmer or Gourdon implementation, a verified
  twin-prime or maximal-gap table beyond toy sizes.

### 2.6 Which outputs can be certified, and how (my analysis, [INFERRED])

| Output | Certificate / checkable object | Cost of checking vs. computing |
|---|---|---|
| Existence of AP-27, Cunningham-20, CPAP-10 | the numbers + primality proofs (Pratt, Pocklington or ECPP); CPAP also needs compositeness of in-between numbers | cheap; 19-digit to 100-digit numbers |
| pi(x) exact value | none shorter than redoing the count: Legendre/Meissel identity pi(x) = phi(x,a) + a - 1 - P2(x,a) can be formally proved, but evaluating phi is the computation | checker is as costly as the computation, times kernel slowdown |
| pi(x) parity | sublinear algorithms exist (Tao-Croot-Helfgott; Lelechenko, arXiv:1305.1639 gives explicit exponent); Lifchitz's is unpublished | cheaper, gives only 1 bit of 90 |
| Maximal-gap table | the claim "no gap > g below p" needs a full sieve | same as sieve |
| Goldbach to N | witnesses (n, p) are tiny but each n - p needs a primality proof; no shortcut | N-sized work |
| Analytic pi(x) | interval-arithmetic computation is already rigorous but not machine-checked | very heavy |

### 2.7 Measured here: Lean kernel speed (to size the "certified" ladder)

Scratch files, not in the project (run in the project's Lean 4.36 / Mathlib setup):
- Mathlib route: `Nat.primeCounting 10000 = 1229` by `decide +kernel` on Mathlib's decidable
  Nat.Prime: stopped with a (kernel) deterministic timeout after about 2.5 minutes. [MEASURED]
- Own trial-division counter (structural recursion on fuel, `Nat` operations with kernel
  GMP acceleration), `decide +kernel` with heartbeats off: pi(10^4) = 1229 in about 20 s
  wall time (including Lean start-up), pi(4*10^4) = 4203 in 2 min 34 s; scaling ~ N^1.5 as
  expected for trial division. At 10^5 the default heartbeat limit trips. That is roughly
  10^4 to 10^5 elementary operations per second in the kernel. [MEASURED]
- [INFERRED] a bit-packed segmented sieve using Nat.land / Nat.shiftLeft on big natural
  numbers (kernel-accelerated) could be several orders of magnitude better, but I did not
  test it. Plausible kernel-checked reach: pi(10^8) to pi(10^10). With the compiled-code
  route (native_decide or a LeanCompCert-style admission, which adds trusted axioms) 10^12
  to 10^14 on 24 cores is plausible with a straightforward sieve. Treat all as estimates.

## 3. What is open

- O1: independent confirmation of pi(10^27), pi(10^28), pi(10^29). Stated by nobody as open;
  my finding: the only verification statements are "computed twice with different alpha"
  (primecount Records) and, for 10^26 only, Staple's separate-code and parity checks. Not
  found: any second implementation or published parity values beyond 10^26. (Searched primecount
  docs, OEIS, MathWorld, Wikipedia, Staple, Platt, Buethe; mersenneforum thread t=20473 refused
  access, so details of the announcements are unread.)
- O2: Goldbach beyond 4*10^18, and double-check of 4*10^17 .. 4*10^18. The source states
  no further double-checking is planned. Open as a matter of work, not mathematics.
- O3: extension of the exhaustive maximal-gap frontier and an auditable record of who covered
  which ranges (not found).
- O4: pi_2(10^19) independent confirmation. Single source, already corrected once.
- O5: any formally verified evaluation of pi(x) beyond toy sizes (not found; absence of
  evidence only, six searches including Lean, Coq, Isabelle).
- O6: certified tables for first occurrences of maximal gaps; no formal artefact found.

## 4. Leads for this project, ranked

### Lead 1: independent recomputation of pi(10^27) (then 10^28) on the 24-core machine
Statement: with a current primecount build (7.x or 8.x, no backup version, UPS or
checkpoint by tee), compute pi(10^27) twice, `--double-check`, and compare with
16,352,460,426,841,680,446,427,399; then pi(10^28) against 157,589,269,275,973,410,412,739,598.
Why fits: pure computation; the code path (Gourdon D, new hyperbola method PR 146) differs
from the 6.4-backup runs, so agreement is mildly independent; no theory needed.
Cost estimate [INFERRED] by x^(2/3)/log^2 x scaling from two data sets (Zen5 32-core
159.5 s at 10^22; Zen2 96-core about 930 s at 10^23): 10^27 on 24 cores about 3 days (optimistic)
to 2 weeks; 10^28 about 2 weeks to 2 months; 10^29 about 2 to 9 months. Memory unknown:
first run 10^23, 10^24, 10^25 with /usr/bin/time and extrapolate; Staple's separate algorithm
needed 41 GB at 10^26, so 63 GB at 10^27 is not guaranteed for any code. A cheaper independent
partial check: pi(x) mod 2 for the three records (needs an algorithm; Lifchitz's is
unpublished; Lelechenko's is published).
Notice-worthiness: low-to-moderate (reconfirming a record with a different version and
hardware; worth a short post on mersenneforum and a line in Records.md). It is NOT independent
of the algorithm family; a genuinely independent check would be an implementation of the
analytic method (not desktop-feasible) or Staple-type separate code.

### Lead 2: a formally verified ladder pi(10^n) = value, with explicit trust levels
Statement: for n <= N_k, `Nat.primeCounting (10^n) = v_n` in Lean, where
 (a) tier 1: kernel only, no native axioms: N_1 about 8 to 10 (needs a bit-sieve encoding;
     my naive attempt got to 4*10^4 in 2.5 minutes, so the encoding is the whole work);
 (b) tier 2: a verified segmented sieve (proved equal to Nat.primeCounting in Lean), run
     through the compiler with a single named axiom (Lean.ofReduceBool), N_2 about 12 to 14;
 (c) tier 3: formal proof of the Legendre-Meissel identity and a verified evaluation of
     phi(x, a) and P2 by compiled code, N_3 about 15 to 17 [INFERRED guess; the identity
     itself is a modest formalization, the evaluation program is the hard part].
Why fits: the project already works in Lean 4 + Mathlib with attention to axiom lists;
Mathlib has the definition, and a verified count of this kind appears to be absent in the
literature I searched (O5). A parity-of-pi result is not needed.
Size: tier 1 about 1 to 2 weeks; tier 2 about 2 weeks; tier 3 about 1 to 2 months. Out of
reach: 10^20 and above (kernel) or any Gourdon-level formal proof.
Notice-worthiness: moderate for Lean/formalization audiences (formal-conjectures, Mathlib
Archive, Lean Zulip) rather than number theory; the headline would be "first machine-checked
value of pi(10^n) with n >= 12" if it holds (stated as absence in my searches only).

### Lead 3: Lean-certified record objects (small, quick)
Statement: Lean theorems (a) there are 27 primes in AP: (4361612620 + 174505864 n) * 23# +
184607939, n = 0..26 (19-digit); (b) the 20-chain Cunningham records (needs the numbers from
the source page, not copied here) are chains of primes; (c) CPAP-10 with in-between
numbers composite. Tools: Pratt or Pocklington certificates; a Lean Pratt checker exists
(the secp256k1 project) and the Isabelle AFP has the theory. Size: days. Value: modest, a
neat demonstration, and these are the only records of this thread whose output is really
certifiable by a short certificate. The AP-27 year and discoverer should be re-read at the
primary list before any claim.

### Lead 4: first-occurrence maximal-gap table, checked in Lean to the 10^9 .. 10^13 range
Statement: for the first k maximal gaps (A002386 / A005250 / A000101), the prime p_k
starts a gap g_k and every earlier gap is smaller. Tiered as in Lead 2; at kernel
level the first 30 or so terms (to ~10^9 for A000101 term 31, 1294268779) are plausible,
compiled-trust tier to the 10^13 range. Cost: a verified sieve already gives this for free
after Lead 2, so days on top of Lead 2. Value: low-moderate; gives a certified copy of the
A005250 prefix and a clean statement that conflicts with nothing in print.

### Lead 5 (not recommended): independent twin-prime count pi_2(10^19), Goldbach double-check
Estimates [INFERRED]: pi_2(10^19) at about 10^9 numbers per second per core would need ~9
core-years x 1 (about 4 months on 24 cores at best, more likely a year or more); Goldbach
double-check 4*10^17..4*10^18 about 3000 core-years at the published speed. Out of reach on
one desktop, apart from sampling slabs, which proves nothing about the whole.

## 5. Overlap or conflict with the project's results

None. This thread has no overlap with the BBP-type results (bases, classification of series,
Baker-based criteria). Connection only at the level of method (machine-checked computation
and certificates). Not credible claims met while searching: several GitHub repositories assert
Lean "proofs" of Goldbach or the twin prime conjecture by "synchronization" arguments with
no stated mathematics; ignore; the Zenodo claimed "disproofs" of Goldbach in search results
likewise.

## 6. Sources

- https://github.com/kimwalisch/primecount (README) and doc/Records.md; doc/primecount.txt;
  doc/StatusS2-tuning.md (raw.githubusercontent.com)
- https://oeis.org/A006880, A006988, A007053, A007508, A005250, A002386, A000101, A000720
  and b-files https://oeis.org/A006880/b006880.txt, A007053/b007053.txt, A007508/b007508.txt
- https://arxiv.org/abs/1503.01839 (Staple); https://arxiv.org/abs/1203.5712 (Platt);
  https://www.math.uni-bonn.de/people/jbuethe/topics/AnalyticPiX.html
- https://mathworld.wolfram.com/PrimeCountingFunction.html;
  https://en.wikipedia.org/wiki/Prime-counting_function, /Prime_gap, /Goldbach%27s_conjecture,
  /Twin_prime, /Cunningham_chain, /Primes_in_arithmetic_progression, /Prime_k-tuple
- https://sweet.ua.pt/tos/goldbach.html and https://sweet.ua.pt/tos/gaps.html
- https://www.pzktupel.de/RecordGaps/risinggap.php
- https://arxiv.org/abs/1904.00499 (Visser); https://arxiv.org/abs/2603.02621 (GoldbachGPU);
  https://arxiv.org/abs/1305.1639 (Lelechenko, parity)
- https://www.isa-afp.org/entries/Pratt_Certificate.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/PrimeCounting.html
- GitHub: openai/PrimeGaps186, AxiomMath/PrimeGapsLib, gersh/ternary-goldbach-lean,
  masalanice/goldbach-verified, nextsense-io/goldbach-lean4, gersh/leancompcert,
  wjbrob/secp256k1-primality-lean, primegap-list-project/primegap-list-project.github.io,
  google-deepmind/formal-conjectures
- Crossref records: Helfgott-Platt DOI 10.1080/10586458.2013.831742; Buethe DOI
  10.1007/s00229-016-0840-4; Deleglise-Rivat DOI 10.1090/s0025-5718-96-00674-6.

## 7. Search log

Refused or failed endpoints (counted in the totals): OpenAlex (429, repeatedly), arXiv API
(429, repeatedly), Semantic Scholar (429), zbMATH web (403), mersenneforum (403), AMS journal
page (403), Debian mirror Records.md (404), primerecords.dk (certificate mismatch), Google
(blocked, not a listed endpoint). Working: Crossref (until 429), zbMATH API (once), GitHub
API, OEIS pages, Wikipedia, arXiv abs/pdf pages.

WebSearch (6):
1. pi(10^29) prime counting record Platt Staple Baugh Walisch primecount
2. maximal prime gaps verified up to 2^64 new record gap project
3. formally verified computation of pi(x) prime counting Coq/Isabelle/Lean certified sieve
4. Goldbach conjecture verified up to 10^19 or 10^20 new computation GPU 2026
5. Lifchitz parity of pi(x) prime counting Gerbicz algorithm mersenneforum
6. Chaffin twin primes below 10^19 count mersenneforum

Endpoint queries through the fetch tool (93 attempts, about 76 returned content):
1 github primecount README; 2 OEIS A006880; 3 OEIS A000720; 4 OEIS A005250; 5 OpenAlex
"prime counting Lean formal" (429); 6 arXiv "prime counting verified" (429); 7 Debian
Records 8.2 (404); 8 Wikipedia Prime gap; 9 Crossref "formally verified prime counting
sieve"; 10 Semantic Scholar verified pi (429); 11 zbMATH API "Goldbach verification";
12 OEIS search "pi(10^n) wrong" (empty); 13 GitHub Records.md; 14 Debian Records 7.16;
15 Semantic Scholar Goldbach GPU (429); 16 zbMATH web (403); 17 Google (blocked);
18 Wikipedia Goldbach; 19 Wikipedia Twin prime; 20 Wikipedia Cunningham chain;
21 primerecords.dk (cert error); 22 OEIS json A007508; 23 OEIS A007508;
24 OpenAlex Goldbach GPU (429); 25 arXiv Goldbach GPU (429); 26 GitHub repos "prime counting
lean4 formal" (0); 27 GitHub repos verified sieve; 28 GitHub repos prime gaps cuda (0);
29 arXiv 2603.02621; 30 arXiv abs 1503.01839; 31 arXiv abs 1203.5712; 32 mersenneforum
t=20473 (403); 33 AMS Goldbach paper (403); 34 Platt PDF (text read locally with pdftotext);
35 Staple PDF (same); 36 tos goldbach; 37 tos gaps; 38 pzktupel RecordGaps; 39 Wikipedia AP
primes; 40 pzktupel home; 41 Wikipedia k-tuple; 42 GitHub repos primecount; 43 GitHub issues
mathlib prime counting; 44 OEIS A007053; 45 Crossref parity pi(x); 46 Crossref Lagarias
Odlyzko; 47 Crossref Pratt/Coq; 48-50 Crossref Goldbach formal, maximal gaps, Helfgott
(429); 51 Buethe page; 52 GitHub repos pratt lean; 53 GitHub repos goldbach lean4; 54 GitHub
code search (401); 55 formal-conjectures page; 56 arXiv abs 1904.00499; 57-59 GitHub pages
masalanice, nextsense, gersh; 60 GitHub repos primegap-list; 61 formal-conjectures git tree;
62 primegap-list site; 63 its maximal-gaps page (404); 64-65 GitHub repos gaps; 66-68
PrimeGaps186, PrimeGapsLib, commonwealthswarm; 69 OEIS A006880 again; 70 A006988;
71 A002386; 72 A000101; 73 arXiv max gap (429); 74 Semantic Scholar (429); 75 primecount
Algorithms.md (404); 76 arXiv abs 1305.1639; 77 primecount issues page; 78 primecount doc
listing; 79-80 primecount issue searches; 81 primecount.txt; 82 StatusS2-tuning; 83 doc
README; 84-86 OEIS b-files A007508, A006880, A007053; 87 OEIS A038754 (irrelevant);
88 AFP Pratt; 89 Crossref verified sieve (429); 90 Crossref Helfgott-Platt; 91 GitHub
leancompcert; 92 GitHub repos lean sieve (0); 93 MathWorld PrimeCountingFunction.
Also two local Lean experiments (section 2.7), nothing downloaded into the repository.

Totals: WebSearch calls = 6. Endpoint queries = 93 (about 17 refused or empty).
