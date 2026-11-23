# Q04: prime number theory in Lean 4 / Mathlib and other provers, late 2026

Date of pass: 2026-11-22/23. Marks: [READ] = read on the source page (through the fetch tool, which
returns a summary written by a small model, so fine print may be lost; the Alpoge note itself was
read as extracted PDF text), [SNIPPET] = search result / API record only, [INFERRED] = my conclusion.
Statuses of Mathlib pull requests come from the GitHub search API, which shows merged_at as null for
everything; I trust a "[Merged by Bors]" title and say so.

## 1. Summary

1. The "Lean proof of the Riemann Hypothesis" is real as an announcement, not a rumour. On 2026-11-20
   Levent Alpoge (Anthropic), working with Claude, released a four-page note and a Lean 4 library
   (14 archive parts, about 175,000 modules, about 17 million lines) claiming RH and GRH for Dirichlet
   L-functions. The Lean and Mathlib communities (with Lean FRO and the Mathlib Initiative) posted a joint
   statement the next day certifying that the statement is Mathlib's own `RiemannHypothesis` and that the
   proof is valid. No human-readable proof exists; it is not refereed. Details in section 2.
2. Prime number theorem: in Mathlib there is now the weak PNT (psi(x) ~ x, pi(x) ~ x/log x, PNT in
   arithmetic progressions, theta ~ x), derived from a merged Wiener-Ikehara theorem. PNT+ has the
   classical error term in a separate repository ("MediumPNT is done" July 2025; strong-PNT zero-free
   region PR merged August 2026). Isabelle has had PNT with the classical error term in the AFP since 2024.
3. Dirichlet's theorem is in Mathlib since 2024-11 (PR "proof of Dirichlet's Theorem" merged
   2024-11-25 by title); Bertrand, Lucas-Lehmer (both directions), Lucas/Pratt primality, quadratic
   reciprocity, Chebyshev theta/psi bounds are in Mathlib.
4. Not in Mathlib (as of 2026-11-22): Zsigmondy (a 100-declaration PR was closed 2026-09-18 when the
   author deleted his fork), Mertens (PRs open), Brun, Selberg sieve beyond a basic upper-bound
   framework, Linnik, Bombieri-Vinogradov, Chebotarev, AKS (draft PR), Pocklington, ECPP.
5. lean-eval (leanprover) contains 48 number-theory problem statements, many about primes, stated with
   `sorry`: Linnik, bounded prime gaps (246), Brun's constant, Chen, Green-Tao, weak Goldbach,
   Friedlander-Iwaniec, Chebyshev sign change. Some say outright that Mathlib lacks a sieve.
6. Best small-project leads: Zsigmondy/Bang upstreaming, Mertens and Chebyshev completion, Brun's theorem
   via the existing Selberg framework, Pocklington/Proth certificates, Chebyshev's bias sign changes.
7. The RH news changes the conditional-theorem landscape: the Mathlib RH statement now has a proof, and
   the Mathlib PRs of the previous week that stated RH-equivalents were being closed (section 2).
8. Nothing here overlaps or contradicts the project's results (section 5).

## 2. What is known

### 2.1 The Lean RH announcement (question 3)

What I could confirm from primary or near-primary pages:

- [READ] The announcement note (alpo.ge/remark.pdf, read as extracted text): first person, by Alpoge.
  He says he believes he has, working with Claude, discovered a proof of RH, that the method extends to
  GRH and he expects the Extended RH with more time, and that he and Claude "formalized the arguments
  without assumptions". He says he is "presenting the world with a complete argument before having
  mastered" the mathematics around it, so he releases only the Lean (14 archive parts at alpo.ge). He
  states there is no human-readable proof yet and that one is to be written. The note gives a rough
  timeline (dated 2026-10-06 to 2026-11-16): a Stepanov-type determinant method, iterated theta lifts
  between unitary groups ("multiplicity" by chaining about X lifts for a von Mangoldt sum of length X),
  Iwasawa towers, a relative trace formula, a weakening of Vandiver, ending with GRH on 2026-11-16. He
  flags that the descriptions are partly paraphrased from AI summaries and may be wrong.
- [READ] Lean community blog "Lean verification of the Riemann Hypothesis" (leanprover-community.github.io
  /blog/posts/riemann-hypothesis/): a joint statement of the Lean and Mathlib communities, endorsed by the
  Lean FRO and the Mathlib Initiative, 2026-11-20/21. It says: the library (about 17 million lines, depends
  only on Mathlib) compiles for dozens of reporters with identical raw export; the statement is Mathlib's
  existing `RiemannHypothesis`; two comparison tools (`comparator`, `con-leche --compare`) confirm that
  the proven theorem matches a Mathlib-only statement file; several independent kernel checkers accepted
  the exported proof. They certify the RH statement and the proof, not GRH (the GRH statements are the
  author's own definitions). They also say the mathematical community still has to explain the ideas.
- [READ] Community mirror (github.com/leanprover-community/riemann-hypothesis; the page I fetched
  describes itself as community-maintained): five theorems in `src/Main.lean` (Mathlib RH; a
  Mathlib-independent restatement; nonvanishing of L(chi,s) for Re s > 1/2; zeros of L on the critical
  line; primitive-character version), axioms only propext, Classical.choice, Quot.sound by comparator;
  the submission carries no license; toolchain Lean 4.33.1; full build takes hours; about 664 stars and
  129 pull requests at fetch time. Its README refuses overhauls with a different proof path and claims
  about private builds.
- [READ] Andrew Sutherland's verification page (math.mit.edu/~drew/grh/): reports compiling all 175,187
  modules with zero errors, axiom check, `leanchecker` replay, acceptance by nanoda, con-leche, con-ron
  and lean4lean on the 61.6 GB export, a byte-identical sandbox re-export, and a determinism race in one
  module (Lean 4.33.1, fixed in 4.36.0). Still running on 2026-11-22: `lake comparator` and Lean's
  default and paranoid kernels on the full export. It gives no personal opinion on correctness and says
  GRH there means Dirichlet L-functions only.
- [READ] Third-party status pages (nasqret/riemann-rev, Nervous-Machine/DEBRIEF-math-riemann,
  keithadler/rh-trim, all created 2026-11-20/21 and written with AI help, as they say): "announced,
  machine-checked, not yet refereed"; no human has signed a reading of the formal statement; the author is
  an Anthropic employee and one record's agent is an Anthropic model (stated openly); one separate
  checker (tenet, by the repo author) and nanoda accepted the file; two other checkers declined because of
  an unsupported type kind (`con-leche`/`con-ron` per rh-trim, which conflicts with the blog and Sutherland,
  who say these two accepted it; I could not resolve this, so it is open). rh-trim measures that 99.35%
  of the proof sits under one statement.
- [SNIPPET] GitHub search shows at least 15 derivative repositories created 2026-11-20 to 23 (maps,
  visualisers, "validate at home", "compression leaderboard", a "human-readable account"). Hacker News:
  the Lean blog post had about 1,200 points and about 1,000 comments by 2026-11-21 evening; the MIT
  verification page about 127 points. A sample of comments (summary only) shows the usual concerns:
  misformalisation, kernel bugs, loss of understanding; nobody in the sample claimed a gap.
- [SNIPPET] Earlier context in 2026: Anthropic (Aug 2026) announced a Claude result raising the proven
  proportion of zeta zeros on the critical line from 41.6% to 67.2%, Lean-formalised and passing
  `comparator`, and stating it was not expected to lead to RH. [READ] Anthropic's own page
  (anthropic.com/research/riemann-zeta) confirms this and has no November update. [READ] Quanta
  (2026-10-19): OpenAI announced a "quasi-RH" (zeros in 1/8 < Re s < 7/8, 199-page, Lean-checked; then
  1/12 < Re s < 11/12, 49 pages, not yet Lean-checked); Lichtman, Radziwill, Dunn, Sarnak, Sawin, Bloom
  quoted, Sarnak "not a theorem until humans check the details". That article is a month before the
  November announcement and says full RH seemed out of reach.

What I could not confirm: any referee-level or named-expert review of the mathematics; any reaction by
Tao, Sarnak, Conrey, Soundararajan or Radziwill to the November claim (searched: web search for
reactions, HN comment endpoint, Zulip archive stream index that stops at 2026-02; the Zulip archive and
arXiv/Crossref/OpenAlex/Semantic Scholar endpoints returned HTTP 429 or are stale). Whether the five
Lean statements say what one means by RH (the Mathlib definition is accepted by the Lean community; I did
not inspect the Lean). A Zenodo "RH_CLOSED" record found by web search is an unrelated single-author
claim (the search summary calls its metadata inconsistent; my fetch of it returned HTTP 410). I found no
text in any page addressed to AI agents; the "Contributing" sections address humans.

[INFERRED] Practical reading: this is a machine-checked artefact plus community statement certification,
with the human mathematics pending. For this project: conditional results on RH become unconditional if
the proof stands; PNT-with-error-term and Dirichlet-type consequences also improve. Do not cite it as
"proved" in print without saying "announced 2026-11-20, machine-checked, not refereed". The 17 M-line
library has no license, so it cannot be copied into a project.

### 2.2 Formalized prime theory: where, and whether merged

PNT and analytic number theory

| Item | Where | Status |
|---|---|---|
| Wiener-Ikehara Tauberian theorem | Mathlib `NumberTheory/LSeries/WienerIkehara.lean` | [SNIPPET] PR #43233 titled "Merged by Bors", closed 2026-11-04; doc page [READ] exists |
| Weak PNT: psi ~ x, theta ~ x, pi ~ x/log x, PNT in AP, p_{n+1} ~ p_n, primes in (x,(1+e)x] | Mathlib `LSeries/WeakPNT.lean` | [READ] doc page exists; follow-up open PR #45844 (Mobius form) |
| Chebyshev theta, psi, lcm(1..n); theta <= x log 4; explicit pi bounds; Costa-Pereira | Mathlib `NumberTheory/Chebyshev.lean` | [READ] in Mathlib; parts upstreamed from PNT+ |
| Chebyshev lower bound on primorial | Mathlib PR #37299 | [SNIPPET] open |
| Zeros of zeta are discrete | Mathlib `LSeries/ZetaZeros.lean` | [READ] in Mathlib |
| Hardy Z function | Mathlib `LSeries/HardyZ.lean` | [SNIPPET] file exists |
| PNT with classical error term, strong PNT | PNT+ repository (Kontorovich-Tao) | [READ] Zulip: "MediumPNT is Done" 2025-07-29; [SNIPPET] zero-free region PR #1635 merged 2026-08-04; not in Mathlib |
| PNT in arithmetic progressions with error term | PNT+ | [SNIPPET] listed as goal; Zulip topic Jan 2026; no completion seen |
| PNT with remainder, pi(x)=Li(x)+O(x exp(-sqrt(log x)/3653)) | Isabelle AFP "PNT_with_Remainder" (Song, Yao, 2024; J. Autom. Reasoning 2025) | [SNIPPET] |
| PNT, Chebyshev, Mertens 1 and 2 (Newman proof) | Isabelle AFP (Eberl, Paulson, 2018) | [READ] |
| Dirichlet characters, L-functions, Dirichlet's theorem | Isabelle AFP (Eberl, 2017) | [READ] |
| Selberg's elementary PNT proof | Isabelle (Avigad et al.), Metamath (Carneiro) | [READ] mentioned on the AFP page, not checked |
| Explicit analytic NT network (IEANTN) | teorth/IEANTN, porting from PNT+ since 2026-08 | [READ] README notice; [SNIPPET] 30 stars, pushed 2026-11-23 |
| Bombieri-Vinogradov | lean-bombieri-vinogradov (blueprint), kimihiro64/bombieri-vinogradov, LargeSieveLib (proofs not yet attempted) | [SNIPPET] repository descriptions only; PNT+ links a project page (PR #1272). Status unverified |
| Chebotarev density | PNT+ (informal blueprint for the cyclotomic case, issue closed 2026-07-22), CBirkbeck/chebotarev-density (81 commits) | [SNIPPET]; I could not read its progress; not in Mathlib |
| Linnik, bounded gaps, Brun constant, Chen, Green-Tao, weak Goldbach | lean-eval statements with `sorry` | [READ] (section 3.3) |
| Bounded prime gaps H1 <= 246 | BigO-Hunter/prime-gaps-246-lean (2026-11-21) | [SNIPPET] one description line; unverified, the repo says it combines two other repos |

Elementary and algebraic

| Item | Where | Status |
|---|---|---|
| Dirichlet's theorem | Mathlib `LSeries/PrimesInAP.lean`, `Nat.infinite_setOfPred_prime_and_eq_mod` (Loeffler, Stoll) | [READ] doc page; PRs #19344 and #19421 titled "Merged by Bors", Nov 2024 |
| Bertrand's postulate | Mathlib `Bertrand.lean` (`Nat.bertrand`) | [READ] |
| Quadratic reciprocity (Legendre, Jacobi) | Mathlib | [READ] on the "100 theorems" page |
| Gauss sums; Jacobi sums (one file) | Mathlib `GaussSum.lean`, `JacobiSum/Basic.lean` | [SNIPPET] file listing; open PRs on the modulus of quadratic Gauss sums (#46030) |
| Cubic or Eisenstein reciprocity | not found in Mathlib | searched Mathlib PR titles for "cubic reciprocity": none seen |
| Lucas-Lehmer (iff) | Mathlib `LucasLehmer.lean` | [READ] both directions |
| Lucas / Pratt primality | Mathlib `LucasPrimality.lean` (iff); `Tactic/Primality` certificate checker | [READ] iff; [SNIPPET] checker PR #45711 and producer PR #45899 "Merged by Bors" 2026-11-05 and 2026-11-20 |
| Pocklington | not found in Mathlib | the docs list Pratt-in-norm_num as TODO (now partly done) |
| AKS | draft PR #34507, plus a 2025 GitHub repository | [SNIPPET] open draft; not merged |
| Elliptic-curve primality proving | not found | no Lean repository found (GitHub searches returned nothing relevant) |
| Selberg sieve | Mathlib `NumberTheory/SelbergSieve.lean` (BoundingSieve, Lambda-squared weights, upper-bound framework) | [READ]; weights PR #27707 open; PNT+ Zulip "Formalizing Selberg Sieve Weights & Errors" Oct 2025 |
| Zsigmondy/Bang | Mathlib PR #28895 (about 100 declarations) | [READ] closed, not merged, 2026-09-18 "by deleting the head repository" by its author; reason not stated |
| Mertens' theorems | Mathlib PRs #46026 (first theorem) and #40656 and #45477 (closed) | [SNIPPET] first-theorem PR open as of 2026-11-14; Isabelle AFP has both |
| Brun's theorem | none found | lean-eval says Mathlib lacks a Brun sieve |
| Lean 4 / Rocq / Isabelle Fermat-type: Fermat two squares, four squares, Wilson, Euler, Pell, perfect numbers, divergence of 1/p | Mathlib | [READ] 100-theorems page |

Dirichlet's theorem in Mathlib dates from November 2024 [SNIPPET, PR dates]. The "100 theorems" page says
all 100 are formalized in Lean [READ], with the PNT entry pointing to PNT+ (not Mathlib).
The "1000+ theorems" page lists for Lean: PNT (PNT+), Bertrand, Dirichlet, Dirichlet approximation,
Wiener-Ikehara (PNT+), Euclid [READ]; it does not list Brun, Chebotarev, Zsigmondy, Mertens, Linnik,
Bombieri-Vinogradov, Green-Tao, Chen, Vinogradov three primes, Siegel-Walfisz at all (so "missing" there
means missing from the list, not necessarily unformalized).

## 3. What is open (wanted lists)

3.1 Mathlib `proof_wanted`: the GitHub code-search endpoint refused anonymous access (HTTP 401) and the
Mathlib docs have no list of `proof_wanted` declarations, so I did not get a list. Not found. From PR and
file evidence only (not stated as "wanted" by the source): Zsigmondy, Mertens, Brun, Pocklington, cubic
reciprocity, Chebotarev, Selberg-sieve applications, Brun-Titchmarsh, explicit PNT in AP.

3.2 PNT+ [READ, Zulip stream index to 2026-02]: Chebotarev "domain expert needed" (Jan 2026), later the
cyclotomic informal blueprint was completed (issue closed 2026-07-22 [SNIPPET]); miniprojects Feb 2026:
primes in short intervals, Chebyshev bounds, odd Goldbach for small n, Ramanujan's inequality, Iwaniec-
Kowalski; explicit estimates (FKS2, BKLNW tables; one outside repo reports 132 of 430 cells of BKLNW
Table 15 closed [SNIPPET], and a PR merged 2026-06 proving `bklnw_thm_15`).

3.3 lean-eval (github.com/leanprover/lean-eval, 48 files in `NumberTheory/`; solves are tracked on a
leaderboard I could not read) [READ for the five files below]: `linnik` (least prime in a progression
<= c d^5.5, Heath-Brown), `bounded_prime_gaps` (liminf gap <= 246, file says mathlib lacks the sieve
machinery), `brun_constant_converges`, `weak_goldbach`, `chebyshev_sign_change` (prime race mod 4 changes
sign infinitely often), all with `sorry`. [SNIPPET] also: ChenTheorem, GreenTao, FriedlanderIwaniec,
VinogradovMeanValue, ErdosSupersingularPrimes, ChowlaAndTwinPrimeOverFqT, Mihailescu.

3.4 Formal Conjectures (google-deepmind/formal-conjectures, 1,378 stars, pushed 2026-11-21) [SNIPPET /
directory listing]: folders Wikipedia, ErdosProblems, OEIS, Mathoverflow and others; Wikipedia files for
Goldbach, Brocard, Andrica, Firoozbakht, Hardy-Littlewood, Bateman-Horn, Elliott-Halberstam, Artin primitive
roots, Feit-Thompson prime conjecture, and more. These are open conjectures, so they do not suggest
provable targets; their value is that statements already exist. Many third-party repositories host
(AI-generated) proofs of its easier items; I did not check any.

## 4. Leads for this project, ranked

Project toolkit assumed: Lean 4 + Mathlib, Baker's theorem imported, Bang/Zsigmondy-type prime arguments
already used, strong automation, 24 cores. "Prerequisites" are what I saw in Mathlib.

1. Zsigmondy/Bang theorem in Mathlib (a^n - b^n has a primitive prime divisor except (2,1,6) and
   a+b power of 2 for n=2). Prerequisites: cyclotomic polynomials, `orderOf`, `padicValInt`,
   `Polynomial.homogenize` (all merged). The only known Lean attempt (#28895, 100 declarations) is
   closed and its branch deleted, so the work may be recoverable only from the PR page. The project
   already uses primitive prime divisors, so this is the one lead with direct payoff. Size: days to
   2 weeks if the project's own lemma is general; worth noticing: a missing, classical Mathlib theorem
   (not on the 100 or 1000+ lists, so only Mathlib-specific credit).
2. Brun's theorem (sum over twin primes of 1/p + 1/(p+2) converges). Statement exists in lean-eval.
   Prerequisites: `SelbergSieve.lean` (upper-bound framework, Lambda-squared weights), Chebyshev.lean,
   `Nat.Prime`. Missing: the sieve bound pi_2(x) << x/log^2 x (needs the Selberg weights result,
   open PR #27707, or an elementary Brun/combinatorial sieve). Size: weeks. Noticed: a famous theorem
   absent from every Lean list and a lean-eval target.
3. Mertens' first and second theorems, with the O(1) and O(1/log x) terms, finished in Mathlib.
   Prerequisites: Chebyshev.lean, Abel summation (`AbelSummation.lean` exists), `SumPrimeReciprocals`.
   Several PRs were opened and closed (Jun, Oct 2026) and #46026 is open, so first check that nobody is
   finishing it. Size: days; low novelty, high usefulness (feeds Brun, Selberg, Brun-Titchmarsh).
4. Pocklington and Proth/Lucas-style primality certificates, plus a `norm_num` producer for them.
   Prerequisites: `lucas_primality_iff`, the new `Tactic/Primality` Lucas checker (Nov 2026). Statement:
   if F | n-1, F > sqrt(n), and for each prime q | F there is a with a^(n-1)=1 and gcd(a^((n-1)/q)-1,n)=1
   then n is prime; plus Proth. Size: days. Noticed: small, but it directly closes a stated TODO.
5. Chebyshev's bias sign change (lean-eval `chebyshev_sign_change`, unconditional Littlewood). Needs
   Landau-type theorem for Dirichlet series with real coefficients or the explicit formula and zeros of
   L(s,chi_4); Mathlib has Dirichlet L-functions, nonvanishing on Re s=1, Wiener-Ikehara. Size: weeks to
   months; high risk; a lean-eval target and unlisted anywhere else.
6. Prime-power / cyclotomic corollaries of Zsigmondy for the project's own series (for example full
   statement that b^n - 1 has a primitive prime divisor for each integer base |b| >= 2, n > 2 with the
   exceptional list) packaged as a library file with the exact exceptional cases, usable for the
   "base b with |b| a power of 2" theorem. Size: days once lead 1 is done.
7. Cubic (and Eisenstein) reciprocity from Jacobi sums. Prerequisites: `GaussSum.lean`,
   `JacobiSum/Basic.lean`, `Zsqrtd`, Eisenstein integers (exists as a ring). Statement: for primary
   primes pi, rho of Z[omega], (pi/rho)_3 = (rho/pi)_3. Size: weeks; absent from all lists (not found);
   the Jacobi-sum file was added recently, so upstream may be moving on it: check PRs first.
8. Brun-Titchmarsh (pi(x+y)-pi(x) <= 2y/log y) from the Selberg upper-bound framework. PNT+ has a
   Zulip topic and a "Brun-Titchmarsh type theorem" thread (2024). Size: weeks; depends on lead 2 work.
9. Pratt-certificate-based prime tables / large known prime verification (Mersenne: lucas_lehmer
   already exists; but a verified list of Mersenne exponents up to a few thousand using the 24 cores
   and `decide`-style kernel checks). Not a theorem but a verified computation the project could host.
   Size: days. Low novelty.
10. Elliptic-curve primality (Goldwasser-Kilian/Atkin) certificate checker. No Lean repository found.
    Prerequisites: elliptic curves over finite fields in Mathlib (Weierstrass curves, group law;
    `EllipticDivisibilitySequence.lean`), needs the Hasse-Weil bound only for the generation side, not for
    the checker. Size: months; the only big one; novelty high but little demand.

Out of reach for a small project: Linnik, bounded gaps (needs Bombieri-Vinogradov: three groups are
working on it), Chen, Green-Tao, weak Goldbach (circle method), Chebotarev (a dedicated repository exists),
a human-readable proof of the Alpoge argument.

## 5. Overlap or conflict with the project

No overlap with the project's classification results, optimality theorems, or the "|b| a power of 2"
theorem was found in the sources of this thread. Items that touch the project's tools: (a) Zsigmondy is
not in Mathlib (PR closed 2026-09-18), so the project's primitive-prime-divisor lemmas are novel to
Mathlib if packaged. (b) The RH announcement is relevant only through the use of Mathlib's
`RiemannHypothesis` and the unlicensed 17 M-line library; it does not affect Baker-based results.
(c) Mathlib's WeakPNT/Chebyshev files are available prerequisites for any prime-counting statement.

## 6. Sources

- https://leanprover-community.github.io/blog/posts/riemann-hypothesis/
- https://alpo.ge/remark.pdf (read through extracted text)
- https://github.com/leanprover-community/riemann-hypothesis
- https://math.mit.edu/~drew/grh/
- https://github.com/nasqret/riemann-rev ; https://github.com/Nervous-Machine/DEBRIEF-math-riemann ;
  https://github.com/keithadler/rh-trim
- https://www.anthropic.com/research/riemann-zeta ; https://quantamagazine.org/ai-proved-the-quasi-riemann-hypothesis-what-happens-now-20261019 ;
  https://techcrunch.com/2026/08/11/an-unreleased-anthropic-model-made-progress-on-one-of-maths-biggest-unsolved-problems/
- https://github.com/AlexKontorovich/PrimeNumberTheoremAnd ; https://github.com/teorth/IEANTN ;
  https://leanprover-community.github.io/archive/stream/423402-PrimeNumberTheorem+
- Mathlib docs: NumberTheory/{Bertrand, Chebyshev, LucasLehmer, LucasPrimality, SelbergSieve}.lean,
  LSeries/{PrimesInAP, WeakPNT, WienerIkehara, ZetaZeros}.lean; https://github.com/leanprover-community/mathlib4/pull/28895
- https://leanprover-community.github.io/100.html ; https://1000-plus.github.io/
- https://github.com/leanprover/lean-eval (and raw files LeanEval/NumberTheory/*.lean)
- https://github.com/google-deepmind/formal-conjectures
- https://www.isa-afp.org/entries/Prime_Number_Theorem.html ; /Dirichlet_L.html ; /PNT_with_Remainder.html
- https://github.com/CBirkbeck/chebotarev-density ; https://github.com/amellendijk/lean-bombieri-vinogradov

## 7. Search log

WebSearch (5 calls):
W1 Lean proof of RH announced November 2026. W2 PrimeNumberTheorem+ status 2026. W3 Alpoge RH Lean Claude
announcement. W4 Alpoge RH mathematicians react Tao Sarnak. W5 Song Yao PNT remainder term.

Fetch-tool queries and page reads (84 in total; the first 40 or so are search or API endpoints, the rest
page reads; items marked * failed):
GitHub API: 1 repos "prime number theorem lean4" (empty); 2 issues "Riemann hypothesis" mathlib4;
3 issues Dirichlet PRs; 4 issues Chebyshev PRs; 5 repos PrimeNumberTheoremAnd; 6 code search proof_wanted
(401*); 7 repos IEANTN; 8 repos formal-conjectures; 9 issues Brun/Selberg/Zsigmondy; 10 repos "Riemann
hypothesis lean4"; 11 repos lean-eval; 12 repos Zsigmondy (empty); 13 repos AKS; 14 repos Chebotarev;
15 repos Pocklington/ECPP; 16 PNT+ issues Chebotarev; 17 PNT+ strong-PNT PRs; 18 repos Bombieri-Vinogradov;
19 repos Brun (empty); 20 mathlib issues Pratt/Pocklington; 21 repos ECPP (empty); 22 mathlib issues
proof_wanted; 23 issues "alpoge"; 24 repos Mertens/Brun/Linnik (empty); 25 mathlib issues reciprocity;
26-31 contents listings (NumberTheory, LSeries, Real, JacobiSum, formal-conjectures, Wikipedia);
32 lean-eval contents; 33 lean-eval repo metadata; 34-39 six raw lean-eval files.
Other endpoints: 40 HN Algolia stories; 41 HN Algolia comments; 42 Crossref (429*); 43 arXiv (429*);
44 OpenAlex (429*); 45 OpenAlex (429*); 46 Semantic Scholar (429*); 47 zbMATH (4 results); 48 arXiv
Lean+PNT (429*); 49 AFP search page (empty); 50 Zulip general archive index; 51 Lean Zulip live (login page).
Page reads: Quanta; TechCrunch; Zenodo (410*); PNT+ Zulip stream index; PNT+ GitHub page; 100.html (two
chunks); 1000-plus; Mathlib doc pages (PrimesInAP, Bertrand, LucasLehmer, LucasPrimality, Chebyshev,
WeakPNT, SelbergSieve, WienerIkehara, ZetaZeros); Anthropic riemann-zeta page; alpo.ge/remark.pdf;
Deicyde/leanprover-community RH repo; Lean blog; MIT/Sutherland; nasqret; DEBRIEF; rh-trim; AFP PNT;
AFP Dirichlet_L; CBirkbeck repo; erdosproblems.com/latest (403*); lean-eval GitHub page; lean-eval
leaderboard README; PNT+ blueprint web (404*); PNT+ Zulip Strong PNT topic; mathlib PR 28895.
Local: pdftotext of the saved remark.pdf.

TOTALS: WebSearch calls: 5. Endpoint queries (search/API/list endpoints through the fetch tool): about 50,
of which 7 were refused (HTTP 401/403/429/410). Page or PDF reads: about 34.
