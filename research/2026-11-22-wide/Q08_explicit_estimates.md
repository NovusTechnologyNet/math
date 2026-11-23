# Q08: explicit estimates in prime number theory and their formal verification

Date of pass: 2026-11-22. Marks: [READ] page/file read through the fetch tool (the fetch tool
returns a model-made summary of the page, not raw text, so "read" means "seen in that summary of
the source's own page"); [SNIPPET] seen in a search result or API record only; [INFERRED] my own
conclusion, or background knowledge that I did NOT check against a source in this pass.
Several endpoints refused access (arXiv API, OpenAlex, Semantic Scholar, one Crossref call: HTTP
429; GitHub code search: 401). PDFs of arXiv papers came back as binary, so I used abstract pages
and ar5iv instead.

## 1. Summary

1. The main formal effort is "PNT+" (PrimeNumberTheoremAnd) and its sub-project IEANTN (Integrated
   Explicit Analytic Number Theory Network; PIs Ryu, Shylakhtenko, Tao; sponsor Math Inc.). It
   holds Lean transcriptions of Dusart 2018, Buthe 2016/2018, Rosser-Schoenfeld, Trudgian,
   Johnston-Yang, FKS2, BKLNW, Platt-Trudgian, Kadiri, Chirre-Helfgott, Ramanujan-inequality
   papers. New IEANTN work moved on 2026-08 to teorth/IEANTN. [READ]
2. The great majority of the statements in these files are still "sorry". In Dusart.lean (2018
   paper, 36 results) only 3 have complete proofs, 33 are sorry. In Buthe.lean only a helper is
   proved. [READ]
3. The finite computations are the gating items. Example: Dusart Prop. 5.4 (a prime in
   (x, x(1+1/log^3 x)] for x >= 89693) has substep 89693 <= x <= 360653 left as sorry, and the
   formal "lcm(1..n) is not highly abundant for n >= 89693^2" depends on it. [READ]
4. Misformalisation is the dominant failure mode: the repository has about 30 closed issues
   tagged MISFORMALISATION (Nat division, index 0 vs 1, strict vs non-strict, wrong thresholds).
   [READ]
5. The formalisation process has found real errors in print (collected in section 2b): FKS2 missing
   side condition, Johnston-Yang range x>=2 should be x>=23, a Schoenfeld interval statement with
   counterexample x = 2010880, Ramanujan-prime papers (upper bound 0 should be log x), Ramare-
   Saouter Goldbach range slightly short, BKLNW Table 8 transcription. [READ]
6. Published corrigenda also exist: Cully-Hugill-Lee (Math. Comp. 2024, error in a closed form for
   an integral with the smoothing function; table of (Delta, x0) recomputed), Faber-Kadiri (Math.
   Comp. 2018, Corrigendum to New bounds for psi(x)), Buthe's arXiv v4 (missing summand in Thm 1).
   [READ/SNIPPET]
7. Mathlib has only crude Chebyshev bounds (theta <= x log 4, psi >= x log 2 for n>=7, pi(n) >=
   n log 2/log n for n>=4, Bertrand) and Mertens first/second theorem PRs are still open. Isabelle
   (Eberl, AFP) has sharper concrete Chebyshev bounds (psi >= 0.9x for x>=41 etc.). [READ]
8. Best fit for this project: finite verifications by exact enumeration (prime-gap style tables,
   threshold checks) that block big dependency chains, plus a systematic audit of finite-range
   constants. See section 4.

## 2. What is known

### 2a. Main explicit results (current forms)

Statements from sources I could actually see:

- Platt-Trudgian: RH holds for all nontrivial zeros with imaginary part up to 3*10^12, rigorous
  by interval arithmetic (arXiv 2004.09765, Bull. LMS). [READ abstract]
- Fiori-Kadiri-Swidinsky (arXiv 2204.02588): for x > 2,
  |psi(x)-x| <= 9.22 x (log x)^(3/2) exp(-0.8476 sqrt(log x)) (constants as seen in the search
  snippet: c about 0.8477, constant about 9.22). [SNIPPET]
  Their pi paper (arXiv 2206.12557): for x >= 2, |pi(x)-Li(x)| <= 9.2211 x sqrt(log x)
  exp(-0.8476 sqrt(log x)), and |pi(x)-Li(x)| <= 0.4298 x/log x for x >= 2; they use the
  Platt-Trudgian height 3*10^12; they cite an announced improved zero-free constant R = 5.5586915
  (Mossinghoff-Trudgian-Yang). [READ via ar5iv]
- Johnston-Yang (arXiv 2204.01980): |psi(x)-x| <= 9.39 x (log x)^1.515 exp(-0.8274 sqrt(log x)),
  x >= 2, plus bounds for theta, pi - li. [READ abstract; the "x >= 2" is the claim that
  IEANTN says should be x >= 23 for one statement, see 2b]
- Buthe (arXiv 1410.7015, Math. Comp. 85, 2016): partial RH up to height T gives the Schoenfeld
  bound whenever 4.92 sqrt(x/log x) <= T; v4 adds a missing summand to Theorem 1, tables remain
  valid. [READ abstract page]. Lean file transcribes Buthe's second paper: for 11 < x <= 10^19,
  |x - psi(x)| <= 0.94 sqrt x; x - theta(x) <= 1.95 sqrt x (x>=1423); li(x) - pi(x) > 0 for
  2 <= x <= 10^19 (Theorem 2 a-f). [READ Buthe.lean]
- Dusart 2018 (Explicit estimates of some functions over primes, Ramanujan J.), as transcribed in
  Dusart.lean: pi(x) >= x/log x for x >= 17; pi(x) <= 1.2551 x/log x for x > 1;
  pi(x) >= (x/log x)(1+1/log x+2/log^2 x) for x >= 88789; pi(x) > x/(log x - 1) for x >= 5393;
  pi(x) <= x/(log x - 1.112) for x > e^1.112; a prime in (x, x(1+1/log^3 x)] for x >= 89693; a
  prime in (x, x(1+1/(5000 log^2 x))] for x >= 468991632; p_k <= k(log k + log log k - 1 +
  (log log k - 2)/log k) for k >= 688383; p_k >= k(log k + log log k - 1 + (log log k - 2.1)/
  log k) for k >= 3; sums 1/p and (log p)/p and products (1-1/p) with explicit 0.2/log^3 x type
  errors for x >= 2278383. [READ Dusart.lean]
- Rosser-Schoenfeld: theta(x) - x = O(x/log^2 x) form, Mertens-type identities, psi(x) < c0 x for
  all x (c0 about 1.0388, as I recall; the file only says "c0") all transcribed; only the psi
  bound (RS Thm 12) is sorry. [READ RosserSchoenfeldPrime.lean]
- Trudgian 2016 (Updating the error term in the PNT): corollary giving a prime in
  [x, x(1+1/(111 log^2 x))] for x >= 2898239; transcribed, sorry. [READ SecondarySummary.lean]
- Bennett-Martin-O'Bryant-Rechnitzer, Explicit bounds for primes in arithmetic progressions,
  Illinois J. Math. 62 (2018), DOI 10.1215/ijm/1552442669. [SNIPPET: metadata only; content not
  read in this pass]
- Cully-Hugill: Explicit estimates for the distribution of primes (Bull. Aust. Math. Soc. 2023);
  Primes between consecutive powers (J. Number Theory 2023); Cully-Hugill-Lee, Explicit interval
  estimates for prime numbers (Math. Comp. 91, 2022: prime in (x(1-1/Delta), x] for x >= x0, table
  of pairs); Cully-Hugill-Dudek conditional and mean-value results. [SNIPPET: Crossref records]
- Lee (arXiv 2403.11814): error in the PNT in short intervals assuming RH, new smoothing argument.
  [READ abstract]
- Bordignon, Mawia, Ramare (Mobius), Aoudjit-Berkane-Dusart (primorials, 2021): Ramare and
  Zuniga-Alterman 2026 "From explicit estimates for the primes to ... Mobius function II" exists;
  zbMATH lists "Bounds for Mertens Sums" (Broadbent, Fiori, Kadiri, Ng, Wilk; arXiv 2608.01498,
  2026). I did not locate a Bordignon record (Crossref 429). [SNIPPET]
- Elementary results (Nagura 1952 "On the interval containing at least one prime number", Proc.
  Japan Acad.; Crossref record only). The statement "prime in (n, 6n/5) for n >= 25" is the
  one given in the task; I did not read Nagura. [SNIPPET]

### 2b. Known errors and corrections (collected)

From Tao's IEANTN log (Jan-Sep 2026) [READ]:
- FKS2: a missing constraint (B > C^2/(8R)) found by a contributor and confirmed by the authors;
  a hypothesis x0 >= 2 needed for eq. (30) and Theorem 3; several strict/non-strict typos.
- Johnston-Yang: a claimed range x >= 2 should be x >= 23.
- Schoenfeld (statement about (x(1-1/16597), x] on the TME-EMT wiki): false, counterexample
  x = 2010880; the wiki was corrected. (A Lean issue about Schoenfeld1976.has_prime_in_interval is
  tagged MISFORMALISATION, no. 1186.)
- A paper's inequality stated strict but proved only non-strict.
- Ramare-Saouter (2003): the claimed Goldbach verification bound is slightly short of the stated
  value; superseded by Kadiri-Lumley.
- Ramanujan-inequality papers (Dudek-Platt, Platt-Trudgian): an upper bound "0" should be
  log x; an assumption (m_a >= 0) fails in a needed case; authors acknowledged the sign issue.
- BKLNW Table 8: two versions exist and a digit was mistyped in transcription.
- Prime gap tables (e Silva-Herzog-Pardi): the converse (every record gap appears) not formalised;
  an axiom incomplete for gap zero.
- Rounding: constants computed in floating point were off in the last digit; 1% safety margins had
  to be added, weakening results.
Published corrigenda: Cully-Hugill and Lee, Math. Comp. 93 (2024) 1019-1025 [READ Crossref];
Faber-Kadiri, Math. Comp. 87 (2018) 1451-1455 [SNIPPET]; Buthe arXiv v4 [READ];
Johnston-Yang flag "a small error" in Buthe 2016 Theorem 1 (unaffected when alpha = 0) and a paper
reports "several errors" in Rosser-Schoenfeld-era work uncovered with Ramare. [SNIPPET, from a
search summary; I did not locate the exact papers]
Formalisation-side (misformalisation) issues in the repo, all closed [READ issue titles]:
Dusart1999.p_n_upper (n > 39017 and strict <); Rosser1941.p_n_upper; Dusart1999.pi_inequality;
Robin.p_n_lower_const1 missing n >= 2; MassiasRobin.p_n_lower (thresholds on p_n, not n);
Buthe2 theorem_2a-d; JY.psi_bound_1; Dusart.proposition_5_15; lemma_5_10a false for k = 4;
theorem_5_6, 5_9a, 5_9b trivial/false through Nat division; FKS Prop 3.11 last term and K versus
K+1; pi* and Buthe psi sums including index 0; li treated without principal value.

### 2c. Formal verification landscape

Lean:
- PNT+ blueprint (Kontorovich, Tao): goal is PNT with classical error term, PNT in arithmetic
  progressions, stretch goal Chebotarev. 357 stars, active on 2026-11-22. Contains Wiener-Ikehara
  (PRs to Mathlib), medium and strong PNT files, Backlund directory, Hadamard factorization,
  Borel-Caratheodory, Perron formula, zeta bounds, Brun-Titchmarsh, Euler-Maclaurin, Mertens
  files. [READ directory listing and README]
- Tao's ICERM slides (2026-05-15) and the search summary: the FKS error-term bound and PNT
  derived formally contingent on a Dusart (2018) tertiary estimate. [SNIPPET]
- IEANTN directory (74 entries) has: BKLNW, Buthe, CH2 (Chirre-Helfgott), Chebyshev, Dusart,
  Erdos392, FKS2 (many Cor 2.3/2.4 row files and "TrustedNumerics"/"CheckedNumerics"), Goldbach
  (small-n verification), Kadiri (zero-free region, zero counting, many eq files), KLN, Lcm,
  LeanCertEnclosures, Li2Bounds, LiSeries, Mertens, MobiusLemma, PrimeInInterval, Ramanujan,
  RosserSchoenfeld (RSPrimeLower, RosserSchoenfeldPrime, RosserSchoenfeldZeta), TMEEMT, eSHP.
  [READ listing]
- Status I could see: Chebyshev estimates (including psi <= 1.11x) done by 2026-02-28; lower bound
  merged to Mathlib 2026-05-11; Mertens 1-3 done by two contributors (upstreaming); Ramanujan
  inequality pi(x)^2 < (e x/log x) pi(x/e) completed (2000+ lines of AI-generated code) and
  uses Platt-Trudgian/BKLNW/LeanCert numerics; lcm result for n >= 89683^2 (89693^2 in the Lean
  file) done conditional on Dusart; Erdos 392 done; Costa Pereira inequalities merged to
  Mathlib; RS lower bound for p_n (n(log n + log log n - 3/2), n>1) proved from Dusart cor 5.3b
  (itself sorry). [READ Tao log, Lcm.lean, RSPrimeLower.lean]
- Lean-side verified RH: I found NO formal verification of Platt-Trudgian's zero computation. The
  interval-arithmetic zeros appear through "trusted numerics" files and external computation.
  [INFERRED from not found; searched: GitHub, ar5iv, two WebSearch queries]. A recent search hit
  mentions third-party Lean projects verifying zeros of zeta on the critical line with Arb
  certificates; these are not peer reviewed. [SNIPPET]
- Mathlib files: Mathlib.NumberTheory.Chebyshev has theta <= x log 4, psi <= x log 4 + 2 sqrt x
  log x, psi >= n log 2 - log(n+1), psi >= n log 2 (n >= 7), theta lower bound, pi(n) >= n log 2/
  log n (n>=4), pi(floor x) <= log4 x/log sqrt x + sqrt x, primorial = exp(theta), Costa Pereira.
  Mathlib.NumberTheory.Bertrand has Bertrand (n,2n]. [READ docs] Open PRs on 2026-11: Mertens first
  theorem (#46026), Mobius form of weak PNT (#45844), one-sided psi bound implies RH (#46028),
  Chebyshev lower bound on primorial (#37299). [READ PR list, truncated]
Isabelle: Eberl-Paulson, Prime Number Theorem (AFP, Newman proof, Chebyshev theta/psi, n-th
prime); Eberl, "Nine chapters of ANT in Isabelle/HOL" (ITP 2019); AFP Concrete bounds for
Chebyshev's prime counting functions (Eberl, 2024): psi(x) >= 0.9x for x >= 41, theta(x) >= 0.82x
for x >= 97, theta <= psi <= 1.2x, by Stirling plus brute force, with Bertrand as corollary; AFP
Bertrands_Postulate. [READ AFP + SNIPPET]
Other systems: Coq (Thery, PNT), HOL Light, Mizar (Riccardi), Metamath (Carneiro), Matita (Asperti-
Ricciotti: Chebyshev and Bertrand), Isabelle Selberg (Avigad et al.). [SNIPPET]

## 3. What is open

Stated by the sources as unfinished (IEANTN sorries and README) [READ]:
- Dusart 2018: 33 of 36 results sorry (listed in 2a); Prop 5.4c (89693 <= x <= 360653) is called
  by the source "a computation not formalizable in Lean" (I read that as a comment in the file;
  it is plainly a finite check, see Lead 1).
- Buthe Theorem 2 (RH-height-based, to 10^19) and its tables: sorry.
- RS Thm 12 (psi(x) < c0 x for all x): sorry. RS Theorem (sum (log p)/p < log x for x>1): issue
  1692 open (2026-07-21). pi(x) > x/log x for x >= 17: closed 2026-08-30.
- Trudgian 2016 Theorems 1, 2, Cor 2; Johnston-Yang Theorem 1.4; Platt-Trudgian Theorem 1 table:
  sorry. FKS2 and BKLNW are in progress; README says early stage for the new network (3 proof-of-
  concept nodes; one has a verification receipt).
- Verified zeta zeros to 3*10^12 and Buthe's range to 10^19 are not formal (my inference).
Not found by me: any formal proof of Nagura's (6/5, n >= 25), Breusch's 9/8, Ramanujan primes
(R_n) bounds as such (the Ramanujan.lean file I saw is about Ramanujan's INEQUALITY for pi, not
Ramanujan primes; the tail of the file was truncated). Searched: Mathlib, PNT+ file listing,
Crossref, one WebSearch.

## 4. Leads for this project, ranked

The toolkit: exact enumeration and finite verification in Lean, interval/rational estimates,
LLL-style searches, 24 cores. Mathlib analytic input available: theta <= x log 4; psi/theta lower
bounds with log 2; primorial = exp theta; Bertrand; Costa Pereira; Euler-Maclaurin; Mertens soon.

Lead 1 (days). Dusart 2018 Prop 5.4c: for every real x in [89693, 360653] there is a prime in
(x, x(1+1/log^3 x)]. Reduce to a statement about consecutive primes p < q below ~360653: whenever
q - p is a gap, the interval condition holds; check all primes (about 30000) by decide/
native_decide, mirroring the existing prime_gap_record machinery (PrimeInInterval.lean, proved).
Unblocks Dusart.proposition_5_4 and hence Lcm.L_not_HA_of_ge (n >= 89693^2) as unconditional.
Worth noticing: closes a dependency that the project itself marks as blocked. [INFERRED from the
file statuses.]

Lead 2 (days-weeks). Machine-check the finite-range threshold constants in Dusart 2018 that do
not need analysis: lemma 4.1 style table checks, Cor 5.2/5.3 for x below the analytic range, p_k
statements for small k (k < 688383 etc.), Theorem 5.6/5.7/5.9 for x < 2278383 using exact
rational enclosures. Each is "for all x >= x0" reduced to finitely many primes between thresholds
(monotone arguments). Why fits: exact enumeration, no analysis. Worth noticing: this is exactly
where print errors (digits, strict versus non-strict, Nat division) are being found. Missing:
analytic tails; the project would supply only the finite part, clearly labelled.

Lead 3 (weeks). A formal "audit" of misformalisation-prone small statements: Schoenfeld's
(x(1-1/16597), x] claim with the counterexample x = 2010880 (trivial check), the "n > 39017" and
"n >= 2" threshold statements of Dusart 1999 and Rosser 1941 for p_n (smallest n for which
p_n > n(log n + log log n - 1) and p_n < n(log n + log log n) hold). Compute the exact true
thresholds by enumeration and prove them with decide. Why fits: exact enumeration of
n up to a few million; the project's habit of correcting published thresholds.

Lead 4 (weeks). Port Eberl's concrete Chebyshev bounds (psi(x) >= 0.9x for x >= 41, theta(x) >=
0.82x for x >= 97) to Lean/Mathlib: Stirling bound on log n! (Mathlib has Stirling) plus Legendre/
lcm identities plus finite check below the threshold. Fits: finite check plus Mathlib Stirling.
Worth noticing: this would raise Mathlib's constant from log 2 (0.693) to 0.9 and feeds Nagura/
Breusch-type results. Not yet in Mathlib per my reading of the Chebyshev docs.

Lead 5 (weeks). Breusch/Nagura-type short intervals from Lead 4 plus finite verification: for
n >= 25 a prime in (n, 6n/5) (Nagura 1952, statement from the task) and Schoenfeld's
(x, x(1+1/16597)] for x >= 2010760 requires the strong analytic input and is out of reach without
the RH-height numerics; Nagura's 6/5 is the realistic target. I have NOT checked whether ratio 6/5
follows from psi >= 0.9x/psi <= 1.2x alone; likely not directly, one needs sharper Stirling-based
bounds (Nagura used Rosser-Schoenfeld-style estimates). [INFERRED] Fits with primorial/binomial
methods already used for Bertrand.

Lead 6 (weeks). Primorial bounds: Chebyshev lower bound on primorial (Mathlib PR #37299 open),
and Aoudjit-Berkane-Dusart-style explicit bounds on p_n# (Explicit estimates involving the
primorial integers and applications, 2021). Statement: p_n# > e^(...) via theta(p_n) lower bounds
from RS/Dusart: for k with p_k >= 10^11, theta(p_k) >= k(log k + log log k - 1 + (log log k -
2.050735)/log k) (Dusart Prop 5.11a, sorry) has finite range below 10^11 (verified by sieve,
n up to about 4*10^9 primes: heavy for Lean, plausible with a certified sieve outside Lean and
checked certificates). Fits partly.

Lead 7 (weeks). Rosser's theorem p_n > n log n for all n >= 1 (Rosser 1939): in Lean it follows
from RS lower bound already proved (p_n > n(log n + log log n - 3/2), n > 1) once log log n >= 3/2
- (nothing) i.e. for log log n > 3/2 - 0... this fails for small n, so finite check for
n up to e^(e^1.5) about 88 and use of the large case; chain depends on Dusart cor 5.3b (sorry).
Statement is easy to state, depends on one sorry, finite part is a few dozen primes. [INFERRED]

Lead 8 (weeks-months). pi(x) <= 1.25506 x/log x for x > 1 (Rosser-Schoenfeld; Dusart 5.2b) and
pi(x) > x/log x for x >= 17 (done). Needs an analytic input stronger than log 4 = 1.386. Possible
route: Chebyshev's method with Stirling-refined bounds (as in Lead 4: psi <= 1.2x bounds give
pi(x) <= 1.2 x/log x + O(x/log^2 x) after the psi-theta step; explicit tail needs work). Fits
only with Lead 4.

Lead 9 (weeks). Ramanujan primes R_n (largest x with pi(x)-pi(x/2) = n-1 plus 1): finite and
explicit statements such as R_n < p_{3n} (Laishram 2010, from memory [INFERRED]) and
2n log 2n < R_n (Sondow, from memory [INFERRED]) need explicit pi(x) bounds of Dusart type; none
of this is in the repository as far as the truncated listing shows. Why interesting: small
statement, little competition. Risk: depends on Leads 2/4/8.

Lead 10 (days-weeks, formal-methods flavour). Certified-numerics infrastructure: the repo files
named TrustedNumerics/CheckedNumerics (FKS2) and the LeanCert dependency (reverted for build time
and axiom issues) show the real bottleneck is rigorous rational/interval evaluation of constants
like exp, log, sqrt in Lean. A small standalone, axiom-clean verifier for "x0 >= e^b, epsilon from
a table" in FKS-type bounds (rational enclosures of log and exp, by Taylor remainders) would be
reusable by the project's own Baker/log bounds and would be noticed by the IEANTN network.
Based on the log: "safety margin of about 1%" was forced by floating-point rounding.

Ranking by value-for-effort: 1, 2, 3, 4, 10, 7, 5, 6, 9, 8.

## 5. Overlap or conflict with the project results

No overlap with BBP-type results or base classification. The only connection is methodological:
exact enumeration and finite verification in Lean (as in Lead 1-3) is the style of IEANTN, and
the project's Part III results (Theorems E, G, H, J, K) have a finite-verification flavour that
could be contributed as nodes. No conflict found.
Collaboration/publication note: the right place is the PNT+ Zulip stream (leanprover.zulipchat.com
channel PrimeNumberTheorem+), the IEANTN project board, and teorth/IEANTN (new contributions).
[READ README] Tao's log shows contributions by students and AI-assisted contributors, so
a Lean-checked fix to a finite item such as Lead 1 would fit their workflow.

## 6. Sources

- https://alexkontorovich.github.io/PrimeNumberTheoremAnd/blueprint/explicit-chapter.html
- https://www.ipam.ucla.edu/news-research/special-projects/integrated-explicit-analytic-number-theory-network/
- https://github.com/AlexKontorovich/PrimeNumberTheoremAnd (README, IEANTN/*.lean, wiki)
- https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/wiki/Terence-Tao's-personal-log
- https://github.com/teorth/IEANTN
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Chebyshev.html and Bertrand.html
- https://www.isa-afp.org/entries/Chebyshev_Prime_Bounds.html
- https://arxiv.org/abs/2004.09765, 2204.01980, 2204.02588, 2206.12557 (ar5iv), 1410.7015, 1002.0442, 2403.11814
- Crossref DOIs: 10.1090/mcom/3884, 10.1090/MCOM/3340, 10.1215/ijm/1552442669, 10.3792/pja/1195570997
- https://www21.in.tum.de/~eberlm/pubs/ant.html (Eberl, search result)
Prompt-injection notice: none of the pages contained text addressed to me.

## 7. Search log

WebSearch (6): 1 explicit PNT Lean PrimeNumberTheoremAnd Tao Kontorovich; 2 Fiori Kadiri
Swidinsky sharper bounds; 3 Isabelle Eberl PNT / Coq; 4 Mathlib Bertrand Chebyshev Nagura; 5 error
corrigendum explicit bound Dusart RS Platt Trudgian; 6 Lean verified zeta zeros.
Endpoint queries (49; 6 refused or unusable):
1 arXiv API explicit PNT (429). 2 GitHub repos PrimeNumberTheoremAnd. 3 OpenAlex errors in
explicit bounds (429). 4 PNT+ explicit chapter. 5 IPAM IEANTN page. 6 GitHub repos explicit
estimates (empty). 7 Crossref explicit estimates correction. 8 Semantic Scholar Dusart (429).
9 GitHub contents PNT+ dir. 10 PNT+ README raw. 11 GitHub issues "explicit Dusart". 12 PNT+ wiki.
13 GitHub contents IEANTN. 14 Tao log raw. 15 teorth/IEANTN. 16 GitHub issues misformalisation.
17 Dusart.lean. 18 contents RosserSchoenfeld. 19 PrimeInInterval.lean. 20 contents Ramanujan.
21 RosserSchoenfeldPrime.lean. 22 Ramanujan.lean. 23 Buthe.lean. 24 SecondarySummary.lean.
25 arXiv abs 2004.09765. 26 arXiv abs 2204.01980. 27 arXiv abs 1002.0442. 28 arXiv abs 1801.08029
(wrong paper). 29 arXiv abs 1410.7015. 30 Crossref BMOR. 31 Crossref Cully-Hugill. 32 zbMATH
Dusart. 33 Crossref Bordignon (429). 34 Crossref Nagura. 35 Crossref 10.1090/mcom/3884.
36 GitHub code search Bertrand (401). 37 GitHub issues Mathlib Chebyshev PRs. 38 AFP search
(empty form). 39 GitHub repos prime counting (empty). 40 arXiv pdf 2206.12557 (binary). 41 AFP
Chebyshev_Prime_Bounds. 42 Mathlib docs Bertrand. 43 arXiv pdf 2403.11814 (binary). 44 ar5iv
2206.12557. 45 arXiv abs 2403.11814. 46 Crossref 10.1090/MCOM/3340. 47 Mathlib docs Chebyshev.
48 Lcm.lean. 49 RSPrimeLower.lean.
Totals: WebSearch calls 6; endpoint queries 49.
