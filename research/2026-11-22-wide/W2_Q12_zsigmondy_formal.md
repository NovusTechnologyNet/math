# W2-Q12: Bang-Zsigmondy and primitive prime divisors in formal libraries

Date of pass: 22 November 2026. Marks: [READ] page/API record read in full on the source,
[SNIPPET] only seen in a search result, [INFERRED] my conclusion. Fetch tool summarises
pages with a small model, so [READ] means "read through the fetch tool", not byte-exact.

## 1. Summary

1. Mathlib PR #28895 "feat(NumberTheory): prove Zsigmondy's theorem" (author yury-harmonic,
   opened 2025-08-25) was closed unmerged on 2026-09-18. The timeline shows it was closed
   by the author deleting the head fork; no closing comment, no reason given. [READ]
2. It was a single new file Mathlib/NumberTheory/Zsigmondy.lean (1306 lines, 0 deletions)
   plus one line in Mathlib.lean. Only review: three comments on the copyright header. [READ]
3. No Mathlib file Mathlib/NumberTheory/Zsigmondy.lean exists on master now (raw and docs
   URLs return 404), and the Lean "1000+ theorems missing" list still lists "Bang's theorem"
   as not formalized. So Mathlib has no Zsigmondy as of today. [READ]
4. Tau Ceti merged its own Bang-Zsigmondy proof on 2026-11-15 (PR #39611, 568 additions),
   written for integers and naturals only (no number fields, no ideals). [READ]
5. Tau Ceti is Apache-2.0, AI-written, human roadmaps, incubated by Lean FRO and the Mathlib
   Initiative. Its roadmap list contains both "Primitive prime divisors and the
   Bang-Zsigmondy theorem" and "Linear forms in logarithms, Baker's theorem over C and C_p".
   [READ]
6. Isabelle AFP has "Lifting the Exponent" (2021, BSD) but no Zsigmondy entry found; nothing
   found in Coq/Rocq. [READ / not found]
7. Best route for the project: the exact needed statement is a short corollary of Tau Ceti's
   `exists_prime_orderOf_div_eq` plus a lifting step to a prime ideal (a Dedekind-style
   step Mathlib already supports). Details in section 4.

## 2. What is known

### 2.1 Mathlib PR #28895 and relatives

- Title, state, dates: opened 2025-08-25, closed 2026-09-18, merged_at null, draft flag
  still set, no labels at the end, 1307 additions, 0 deletions, 2 files, 5 issue comments
  (all bots), 3 review comments. [READ, GitHub API]
- Body: standard template plus a checklist of eight dependency PRs (#28879 Polynomial/
  Homogenize, #28825, #28833, #28888, #28830, #28765, #28886, #28934), all done; the bot
  listed all as merged by 2025-10-27. [READ]
- Content [READ, PR file patch]: `MvPolynomial.cyclotomic2` (homogenized cyclotomic
  polynomial, `(cyclotomic n R).homogenize (phi n)`); integer theorem
  `Int.exists_prime_pow_modEq_pow_forall_lt_not_pow_modEq_pow` for a^n-b^n with 0<b<a,
  coprime, and the two exceptions; `eq_two_one_six_of_zsigmondy`, `eq_add_one_of_zsigmondy`,
  n=2 case (a+b power of 2), specialisation a^n-1, orderOf restatements
  (`Int.exists_prime_orderOf_eq` etc.), a^n+b^n versions, Nat versions, and a LTE lemma
  `padicValInt_pow_sub_pow` / `Int.emultiplicity_pow_sub_pow'`.
- Review: dupuisf asked on 2025-08-25 whether the copyright header was a copy-paste error;
  the author answered that the first line was inherited from the Lean 3 file (Johan
  Commelin, 2022), that he wanted to keep it, and proposed a second line for Harmonic who
  paid for the work; dupuisf accepted. That is the whole human review. [READ]
- History: merge-conflict bot labels in Aug 2025, Nov 2025; author merged master several
  times (last visible Dec 2025, "Use public import" commit); then nothing visible until the
  closure by fork deletion in Sept 2026. [READ, page; timeline was truncated at 100k chars
  so later events could be missing]
- Origin: Zulip thread "Zsigmondy's theorem" (stream "Is there code for X?", 20-26 Aug
  2025). Yael Dillies: Mantas Baksys did it ~3 years earlier in Lean 3, never reached
  Mathlib. Baksys: his file is the latest, never polished. Kudryashov: has a Lean 4 proof
  written for Harmonic, permission to open-source, will open a series of PRs. 25 Aug:
  needs substantial cleanup; header credits Commelin, adds Alex J. Best and himself.
  Rothgang asked about 1000.yaml. Baksys: Commelin helped a lot, add him to authors. [READ]
- Why closed: not stated anywhere I could read. [INFERRED] likely candidates: the proof
  now exists in Tau Ceti, or Harmonic/author reorganised; the file was also at ~1300 lines
  while Mathlib reviewers prefer files under ~1000 (stated in an unrelated Zulip thread on
  Sylvester-Schur, [READ]). Pure speculation; ask on Zulip if it matters.
- Taken over? Not found. Searches: GitHub issue search "Zsigmondy" in mathlib4 returned
  only #28895 and #28879 (the latter, Homogenize, did get merged on 2025-08-27 by bors as
  the PR title says, though merged_at is null in the API; same artifact appears on all
  Bors-merged PRs). A direct fetch of master and of the docs page returned 404. The
  mathlib4 issue search for Birkhoff-Vandiver / "primitive prime" was refused (403), so I
  could not check other issues or PRs on those terms. [READ / not found]
- What Mathlib has today that is adjacent [READ, docs pages]:
  - Mathlib/NumberTheory/Multiplicity: LTE for odd p (`Int.emultiplicity_pow_sub_pow`,
    `..._pow_add_pow`, Nat versions), p=2 versions (`Int.two_pow_sub_pow`, ...),
    general `emultiplicity_pow_sub_pow_of_prime`; the padicValNat aliases were deprecated
    on 2026-10-28 in favour of `Nat.multiplicity_*`.
  - Cyclotomic/Eval: `sub_one_pow_totient_lt_cyclotomic_eval` ((q-1)^phi(n) < Phi_n(q)
    for real q>1, n>=2), upper bound `cyclotomic_eval_lt_add_one_pow_totient`, natAbs
    versions for integers, `eval_one_cyclotomic_prime(_pow)`, positivity lemmas.
  - Cyclotomic/Expand: characteristic p lemmas, `isRoot_cyclotomic_prime_pow_mul_iff_of_charP`.
  - Prime-divisors-of-cyclotomic-values and a Zsigmondy statement: not on the pages
    checked (Eval, Expand). I did not read the Cyclotomic.Basic or ZMod pages.

### 2.2 Tau Ceti

- What: "an AIs-welcome Lean library downstream of Mathlib"; AI agents write and review,
  humans write roadmaps and rubrics; depends on Mathlib master, defers to Mathlib designs,
  "does not push material upstream"; when Mathlib gets a result, Tau Ceti switches to it.
  Package on Reservoir: Apache-2.0, 260 stars, Lean toolchain v4.36.0-rc1 listed (site
  says v4.37.0-rc1 tagged 2026-11-20). [READ: github.com/TauCetiProject/TauCeti,
  taucetiproject.org, Reservoir, lean-lang.org/use-cases/tau-ceti]
- Who: incubated by the Lean FRO and the Mathlib Initiative. Scientific Advisory Board:
  Chris Birkbeck, Kevin Buzzard, Johan Commelin, Kim Morrison, Leonardo de Moura, David
  Roe. Repos: TauCeti, TauCetiRoadmap, TauCetiReview, TauCetiWorker, TauCetiWebsite. News:
  30 Oct 2026 "An Anthropic grant". [READ]
- License: Apache-2.0 (library, roadmaps, CFSG-related repos too). [READ]
- Contribution rules [READ, repo README]: no stacked PRs even drafts; review size capped at
  3000 added / 2000 removed lines, new .lean files at most 1250 lines; changes confined to
  TauCeti/, TauCeti.lean, Lake pins, docbuild references.bib; contributor registers
  intent before substantial roadmap work; AI-driven review against fixed open rubrics (ten
  rubrics: correctness, reuse, scope, attribution, api-design, generality, placement,
  naming, documentation, proof-quality); contributors pay for their own agent compute;
  workers run through `tauceti work --loop` under the contributor's own Claude/Codex
  account and GitHub account; humans approve roadmap changes. The CONTRIBUTING.md raw URL
  returned 404 on main, so details come from the README only. Scope statement: reusable
  foundational library, not frontier research. Also "students' registered projects take
  priority".
- Zsigmondy there [READ, GitHub API]: 9 PRs under label roadmap/PrimitivePrimeDivisors,
  2026-11-05 to 2026-11-15: #28985 (exponents 1 and 2), #29272 (divisibility criteria for
  q^k +-1 by the order of q), #28625 (order characterisation), #31585 (bounds), #36313
  (size estimates), #37645 (expansion identities), #38745 (prime divisors of homogeneous
  cyclotomic values), #39633 (exact multiplicities), and the final #39611 (author chrisflav,
  opened 2026-11-13, merged 2026-11-15 09:32 UTC by the queue bot, after two AI reviews, ten
  rubrics green each; three earlier attempts #40030, #41014, #41465 were closed). 
  The merged theorem (`TauCeti.exists_prime_dvd_pow_sub_pow`): for naturals 0<b<a,
  coprime, n>=2, n=2 not with a+b a power of 2, (a,b,n) != (2,1,6): there is a prime p with
  p | a^n-b^n and p not dividing a^k-b^k for 0<k<n. Plus an iff version, 
  `exists_prime_orderOf_div_eq` (a prime p not dividing ab where a/b has order exactly n in
  ZMod p, iff form too), `exists_prime_orderOf_eq` (a>=3, n>=3), `exists_prime_orderOf_two_eq_iff`
  (n not in {1,6}), `exists_prime_dvd_pow_add_pow`. Proof: homogeneous cyclotomic value
  Phi_n(a,b), size bound Phi_n(a,b) > largest prime factor of n except (2,1,6). Naturals,
  integers, reals only: no number fields. Sources credited: Zsigmondy 1892, Birkhoff-Vandiver
  1904, Roitman 1997, Avci 2023. 
- The roadmap text [READ, TauCetiRoadmap/PrimitivePrimeDivisors/README.md]: layers 0 to 3;
  "large Zsigmondy primes" explicitly out of scope (separate roadmap); only Mathlib
  dependencies; provenance note says formal proofs of two specialisations (base >= 3 and
  base 2) already exist in "the external CFSG repository" (AxiomMath/CFSG, Apache-2.0, 175
  stars, built on Mathlib and TauCeti, sorry-free). [READ]
- Review comments of #39611 do not mention Mathlib #28895 or upstreaming. [READ]
- Transcendence roadmap [READ]: TauCetiRoadmap/LinearFormsInLogarithms: Schneider-Lang
  criterion, Hermite-Lindemann, Gelfond-Schneider, Baker's theorem (layer 7, item 7.2) with
  corollary "nonzero linear form in logs with algebraic coefficients is transcendental"
  (7.3), plus p-adic Baker (layer 8). States that most of the development already exists,
  sorry-free, on two branches of a Mathlib fork, Apache-2.0, to be ported with credit.
  Effective bounds (quantitative Baker), Schanuel are explicitly out of scope. Also
  roadmaps listed: Diophantine approximation and transcendence (I, II), Roth/Subspace
  theorem, cyclotomic class groups and Stickelberger, perfect powers in arithmetic
  progressions, many analytic number theory items. The Baker roadmap does not depend on
  the Zsigmondy one. [READ; the roadmap README listing was truncated at ~100k chars]

### 2.3 Isabelle, Coq/Rocq

- AFP "Lifting the Exponent", author Maya Kadziolka, 27 April 2021, BSD licence; formalises
  the LTE lemma for the p-adic valuation of a^n +- b^n for positive integers (proof follows
  an Parvardi article); session Lifting_the_Exponent, theory LTE. Formal statements not
  read (the PDF was unreadable through the fetch tool). [READ abstract only]
- AFP "Zsigmondy's Theorem": no such entry found (AFP site search page is JS-only and
  returned nothing; a web search for AFP + Zsigmondy returned only the LTE entry).
  [not found; weak]
- Coq/Rocq: GitHub repository search "primitive prime divisor Coq" returned zero repos;
  "Zsigmondy Coq/Rocq/Isabelle" returned only unrelated ones. [not found; weak]. [INFERRED]
  Mathcomp's finite-group files use primitive prime divisors in the odd order theorem, but
  I did not verify that.
- Other formal Zsigmondy artifacts: nasqret/ZsigmondyChebyshev (Lean 4, Apache-2.0,
  updated 2025-12-18, formalises Baranczuk's paper on Zsigmondy for Chebyshev polynomials
  [arXiv 1909.12143], done with Harmonic's Aristotle; has blueprint). sovesti/zsigmondy
  (Lean, 2023, no licence). [READ page of the first; SNIPPET for the second]

### 2.4 Lean projects outside Mathlib and their rules (AI contributions)

- Mathlib itself accepts AI-assisted work with conditions: disclose tools in the PR; add
  the `LLM-generated` label for large amounts; write all comments yourself; understand
  everything; need Lean-expert supervision; low-effort PRs may be closed without comment;
  repeated violations can lead to a ban. [READ, leanprover-community contribute page]
  A Zulip thread shows maintainers (Buzzard, Mehta, Rothgang) objecting to unpolished
  AI-written large PRs and to files over ~1000 to 1500 lines. [READ]
- Tau Ceti: see 2.2; AI-first; the most welcoming. [READ]
- Formal Conjectures (Google DeepMind): Apache-2.0, Google CLA once per contributor, no AI
  policy beyond "follow Mathlib conventions"; proofs over 25-50 lines belong in an external
  repo linked by a `formal_proof` tag; only open or solved-problem statements. [READ]
- PrimeNumberTheorem+ (Kontorovich-Tao, Apache-2.0): no AI policy visible on the README;
  scope is analytic NT (PNT, Chebotarev stretch). [READ]
- AxiomMath/CFSG and CFSG-applications: Apache-2.0, no CONTRIBUTING file, one open PR; the
  applications repo (25 results) is for theorems that use the classification, so not a fit
  for Zsigmondy. [READ]

## 3. What is open

- Is classical Zsigmondy in Mathlib? Not as of today (404 on file, 1000+ list still
  "missing"). Stated as open by the 1000-missing list [READ]. Whether anyone has taken over
  #28895: not found (only #28895 and #28879 matched in the GitHub issue search; other
  searches refused).
- Primitive divisors over number fields (Schinzel: A^n - B^n in algebraic number fields, with
  an effective-form extension in the 1993 paper "An extension of the theorem on primitive
  divisors in algebraic number fields", Math. Comp. [SNIPPET: Crossref/zbMATH records]):
  no formal version found anywhere. Not found in Mathlib, Tau Ceti PR text ("works only with
  natural numbers and integers" [READ]), or AFP.
- Large Zsigmondy primes (Tau Ceti: separate, out of scope). Lucas/Lehmer sequences
  (Bilu-Hanrot-Voutier: Zsigmondy set within {1..30} [READ, Wikipedia]) formalised: not found.
- The statement of lead 1 below is not in any formal library I found.

## 4. Leads for this project (ranked)

Statement S. For an integer b >= 5 and every root of unity r in C with r^4 != 1 there is a
prime p not dividing 2*b*ord(r) and a prime ideal P of the ring of integers of
K = Q(r, sqrt b) lying over p with sqrt b - r in P.

[INFERRED] sketch. Let m = ord(r), zeta = r^2, m' = ord(zeta) in {m, m/2}.
Then (sqrt b - r)(sqrt b + r) = b - zeta. Steps: (i) Zsigmondy for a=b, base 1, exponent m':
prime p not dividing b with b of order m' in ZMod p (Tau Ceti: `exists_prime_orderOf_eq` needs
a>=3, n>=3, which covers b>=5, m'>=3; the case m' in {1,2} is where r^4 = 1 and is excluded
by hypothesis, at least for r^4 != 1 meaning m' >= 3 because r^4 = zeta^2). (ii) Need p not
dividing m': follows since the order m' divides p-1 (the order of b divides p-1), so p > m',
hence p does not divide m' nor 2m. (iii) Lift: a prime Q of Z[zeta] over p with
zeta ≡ b mod Q (exists since Phi_{m'}(b) ≡ 0 mod p and Phi_{m'} splits mod p with b a root;
Dedekind-Kummer or `Ideal.exists_ideal_over_maximal`-type argument plus a ring map
Z[zeta] -> ZMod p sending zeta to b). (iv) In K, take P over Q: since P contains
(sqrt b - r)(sqrt b + r), one factor lies in P; if only sqrt b + r does, use the automorphism
fixing r and negating sqrt b when sqrt b is irrational; when b is a perfect square c^2 treat
r and -r (note -r has the same square) so choose the sign via primes above different Q
(use the other root of x^2 = b in ZMod p, i.e. count both square roots via the
characteristic-p root of unity: both r mod P and -r mod P are candidates and P is chosen
over Q to make sqrt b - r vanish). Step (iv) is the only delicate point (sign choice) and I
have not verified it for perfect-square b. All of this should be checked before relying on it.

Lead 1 (days to 2 weeks): formal proof of S, stated as: exists p, p.Prime, not p dvd
2*b*orderOf r, exists a ring hom phi from the integer ring of Q(r,sqrt b) to an algebraic
closure of ZMod p, with phi(sqrt b) = phi(r). The ring-hom form avoids ideals, and
is the form Baker-style arguments use. Fits: Tau Ceti has the cyclotomic input and orderOf
statements; Mathlib has IsCyclotomicExtension, IsPrimitiveRoot, `Ideal.exists_ideal_over_maximal`
style lemmas and the integral-closure API. Missing: the lifting step is not in Tau Ceti
(its Zsigmondy files use naturals, integers, reals only). Worth noticing: yes, as a
number-field corollary of Zsigmondy that no library has; it is directly used by the
base b >= 5 results in your Lean development, so a self-contained module here also helps
the project's own proofs.

Lead 2 (days): contribute the classical Zsigmondy corollaries as already stated in
Tau Ceti `Zsigmondy.lean`/`Order.lean` into the project's Lean tree as a dependency
(Apache-2.0, so licence-compatible; credit its authors, rule "attribution" rubric).
Option: add Tau Ceti as a Lake dependency instead of copying. Check the Lean toolchain: Tau
Ceti tracks Mathlib master (toolchain v4.36/4.37-rc), and the project must match. A
fallback is to copy only the needed files with licence notices, but Tau Ceti prefers
dependents, not forks. Effort: small if toolchains agree, otherwise a Mathlib bump.

Lead 3 (2 to 4 weeks): propose the number-field statement S, with its generalisation
"for an algebraic integer alpha in K that is not a root of unity and a root of unity r,
primitive divisors of alpha^n - r^n for n large" (the Schinzel-type theorem), as a new
roadmap in TauCetiRoadmap (humans approve; README as the authoritative spec; optional
Suggested.lean; cite existing work, see CONTRIBUTING "Getting started"), or as an addition
to the existing PrimitivePrimeDivisors roadmap. Then register intent and run the worker
under your own Claude/Codex account. This is the contribution form Tau Ceti wants: AI
writes the code, humans write the roadmap. Cost: your own agent spend. Note: Tau Ceti's
scope says "reusable foundational library, not frontier research" and prioritises
registered student projects, so S may be viewed as peripheral; link it to the Baker
roadmap (Layer 7 corollaries) to justify.

Lead 4 (weeks, uncertain): upstream the classical Zsigmondy to Mathlib. Mathlib wants a
human-supervised, disclosed, label-marked PR with files under ~1000 lines, split in
stacked small PRs (allowed in Mathlib, forbidden in Tau Ceti). The closed #28895 (1300
lines in one file) and Tau Ceti's 9-PR chain are two ready-made decompositions. Before
trying, ask on Zulip (stream "Is there code for X?", the old thread) whether the PR author or
Tau Ceti intends to upstream, to avoid duplicating. Worth noticing: the 1000+ list entry
"Bang's theorem" becomes done. Probably not the best use of effort for the project's goals.

Lead 5 (small, days): record a result for the project's own bookkeeping: Tau Ceti's
`exists_prime_orderOf_two_eq_iff` gives the base-2 case, and the form for base b >= 3 in
`exists_prime_orderOf_eq` matches what the base-b classification uses; check that your
own Lean proofs of Zsigmondy consequences (Part III) can be replaced by these.

Form of any contribution: roadmap README plus Lean files under TauCeti/NumberTheory/...
with statement, docstring credit, no stacked PRs, one standalone PR under 3000 added lines and
files under 1250 lines. If the Lean toolchain of the project differs from Tau Ceti's, be ready to
bump.

## 5. Overlap or conflict

No conflict with the project's section-1 results. Overlap: Tau Ceti now proves the
classical Zsigmondy (a^n - b^n, base a >= 3 order version) that the project uses; the
project's number-field statement S (prime ideal in Q(r, sqrt b)) is not in Tau Ceti.
The Tau Ceti Baker roadmap (Layer 7) overlaps with the project's imported Baker proof
(Karatarakis's proof): mutual interest in porting, both Apache-2.0 compatible with a Lean
project. The roadmap itself says most is already written on a Mathlib fork, so the Tau Ceti
version of Baker may soon land and could replace the imported one. [INFERRED]

Note on page text addressed to me: none seen. One reviewer-bot comment on PR #39611 notes
a rubrics-drift warning; not an instruction.

## 6. Sources

- https://github.com/leanprover-community/mathlib4/pull/28895 and its API records
  (pulls/28895, /comments, /files, issues/28895/comments, /timeline)
- https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Zsigmondy's.20theorem.html
- https://github.com/TauCetiProject/TauCeti ; https://github.com/TauCetiProject/TauCetiRoadmap ;
  https://taucetiproject.org ; https://taucetiproject.org/people ;
  https://reservoir.lean-lang.org/@TauCetiProject/TauCeti ;
  https://lean-lang.org/use-cases/tau-ceti
- https://github.com/TauCetiProject/TauCeti/pull/39611 and /pull/28625 (API)
- raw: TauCetiRoadmap/PrimitivePrimeDivisors/README.md; LinearFormsInLogarithms/README.md
- https://github.com/AxiomMath/CFSG ; https://github.com/AxiomMath/CFSG-applications
- https://github.com/nasqret/ZsigmondyChebyshev
- https://www.isa-afp.org/entries/Lifting_the_Exponent.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Multiplicity.html ;
  .../RingTheory/Polynomial/Cyclotomic/Eval.html ; .../Expand.html
- https://leanprover-community.github.io/1000.html ; /1000-missing.html
- https://leanprover-community.github.io/contribute/index.html
- https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md
- https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
- https://en.wikipedia.org/wiki/Zsigmondy%27s_theorem
- Crossref/zbMATH records: Schinzel 1993 (doi 10.2307/2152966); Glasby-Luebeck-Niemeyer-
  Praeger 2017 "Primitive prime divisors and the n-th cyclotomic polynomial" [SNIPPET]

## Search log

WebSearch (5): 1 "Mathlib Zsigmondy theorem pull request Lean 4"; 2 "Tau Ceti Lean library
Bang-Zsigmondy formalization"; 3 AFP "Zsigmondy" OR "Lifting the Exponent" Isabelle;
4 mathlib4 Zsigmondy pull request closed Harmonic Aristotle 2026; 5 Lean Zulip Zsigmondy Tau
Ceti OR Mathlib 2026 Kudryashov PR closed.

Endpoint queries (60), through the fetch tool; refused/limited ones are marked:
1 GitHub issues search "Zsigmondy" mathlib4; 2 pulls/28895; 3 isa-afp search page (empty);
4 issues/28895/comments; 5 pulls/28895/comments; 6 pulls/28895/files; 7 Zulip archive
thread; 8 TauCeti repo page; 9 GitHub issues search Zsigmondy in TauCeti; 10 code search
TauCeti (401); 11 issues search Bang/primitive in TauCeti; 12 TauCetiRoadmap repo page;
13 lean-lang use-case page; 14 TauCeti pulls/39611; 15 pulls/39611/files; 16 raw roadmap
PrimitivePrimeDivisors; 17 code search Baker in roadmap (401); 18 Reservoir page;
19 mathlib issues search Birkhoff/LTE/primitive prime (403); 20 mathlib issues-only
Zsigmondy (403); 21 repositories Zsigmondy language:Lean; 22 raw Completed README (404);
23 code search Zsigmondy extension:lean (401); 24 issues/28895/timeline; 25 PR 28895 HTML
page; 26 ZsigmondyChebyshev repo; 27 raw mathlib master Zsigmondy.lean (404); 28 docs
LucasLehmer; 29 docs Multiplicity; 30 docs Cyclotomic/Eval; 31 docs Cyclotomic/Expand;
32 docs NumberTheory/Zsigmondy (404); 33 arXiv API (429); 34 OpenAlex (429); 35 Crossref
primitive prime divisors number field; 36 repositories Zsigmondy Coq/Rocq/Isabelle;
37 AFP Lifting_the_Exponent page; 38 AFP LTE document.pdf (unreadable); 39 repository
search CFSG Lean; 40 raw TauCeti CONTRIBUTING.md (404); 41 taucetiproject.org; 42 code
search AxiomMath/CFSG (401); 43 AxiomMath/CFSG page; 44 CFSG-applications page; 45 raw
LinearFormsInLogarithms roadmap; 46 taucetiproject.org/people; 47 formal-conjectures
CONTRIBUTING; 48 leanprover-community contribute page; 49 PrimeNumberTheoremAnd page;
50 Zulip Sylvester-Schur thread; 51 raw mathlib CONTRIBUTING.md (404); 52 Wikipedia
Zsigmondy; 53 Semantic Scholar (429); 54 zbMATH search; 55 repository search primitive
prime divisor Coq (0 hits); 56 1000.html; 57 1000-missing.html; 58 TauCeti pulls/39611/
comments (403); 59 TauCeti issues/39611/comments; 60 TauCeti pulls/28625.

Totals: WebSearch calls 5; endpoint queries 60 (of which 11 failed or were refused).
