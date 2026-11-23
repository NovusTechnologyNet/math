# P09: pi in Lean 4 / Mathlib and in other proof assistants (report of 2026-11-22)

Marks: [READ] = read on the source's own page/file (through the fetch tool, which summarizes
with a small model, so details are as reliable as that); [SNIPPET] = only a search result or
API record; [INFERRED] = my conclusion. Limits: GitHub code search needs login (401), arXiv API
and Semantic Scholar answered 429, so "not found" claims below are weak.

## 1. Summary

1. Mathlib's own Chudnovsky file defines the series but has NO proof of the formula; the
   identity `chudnovskySum = pi^-1` is a `proof_wanted` and also an unsolved problem on the
   lean-eval site. The header invites anyone to adopt it. [READ]
2. Mathlib has no BBP formula, no Bellard formula, no digit-extraction algorithm. Searches of
   the mathlib4 issue/PR lists for BBP, Bellard, "digit extraction", spigot, Bailey, "digits of
   pi" returned nothing relevant. [READ API, weak: "not found"]
3. Numeric bounds in Mathlib stop at 20 decimals (pi_gt_d20 / pi_lt_d20), by the square-root
   (Archimedes-type, sqrtTwoAddSeries) method with rational witnesses, not by Machin. [READ]
4. Machin's formula (4 arctan(1/5) - arctan(1/239) = pi/4) is in Mathlib since Feb 2024; also
   Leibniz, Wallis, Basel and zeta(2k), zeta(4), irrationality of pi, Stirling. Transcendence
   of pi is NOT in Mathlib (100-theorems list: links only, no declaration). [READ]
5. A public Lean repo with BBP exists: a one-author repo (updated Nov 2026) claims the BBP
   identity, hex-digit certificates for n <= 10000, and an all-n guard bound from a Mahler-type
   irrationality measure. Not independently checked; looks unreviewed. [READ README/tree]
6. Coq: Bertot-Rideau-Thery formalized BBP digit extraction (partial correctness, with a
   two-sided interval check) and computed the billionth hex digit, 1e6 decimals. [READ]
7. Isabelle: no AFP entry for BBP/Machin/Chudnovsky found; HOL-Analysis has an
   "Approximations" example theory for pi by arctan series. [SNIPPET, weak]
8. Formal Conjectures: only "pi is normal in base 10" (open) and transcendence/irrationality
   statements about combinations of pi and e (open); nothing on BBP. [READ]
9. Mathlib AI policy: disclose AI use in the PR text, label `LLM-generated`, you must understand
   and defend the code, no LLM-written comments on GitHub/Zulip. [READ]
10. Best leads: (a) a Mathlib-quality BBP identity PR; (b) BBP digit extraction proved correct
    with explicit guard (the all-n statement needs an irrationality measure of pi; the project
    has Baker, not that); (c) Bellard / more digits; (d) Chudnovsky is too big (needs elliptic
    curves).

## 2. What is known

### Mathlib, definition and files [READ unless stated]
- Real.pi is defined from the sine zero (Mathlib.Analysis.SpecialFunctions.Trigonometric);
  directory Mathlib/Analysis/Real/Pi/ contains Bounds, Chudnovsky, Irrational, Leibniz, Wallis
  (directory listing via API). [READ listing]
- Bounds.lean (van Doorn, Carneiro): 3 < pi < 4, d2, d4, d6, d20. The d20 pair is
  3.14159265358979323846 < pi < 3.14159265358979323847, proved with 34 iterations, 46-digit
  rational witnesses and custom tactics `pi_lower_bound`, `pi_upper_bound`; the witnesses were
  generated with a Mathematica script kept in a comment. No TODO or proof_wanted in the file.
- Leibniz.lean (Davidson, Tan 2020): `Real.tendsto_sum_pi_div_four`, via Abel's limit theorem
  and the arctan power series.
- Wallis.lean (Zhang 2021): `Real.tendsto_prod_pi_div_two`, via integrals of sin^n.
- Irrational.lean: `irrational_pi`, Cartwright-style integral proof (as on Wikipedia).
- Machin: `Real.four_mul_arctan_inv_5_sub_arctan_inv_239` in
  Trigonometric/Arctan.lean, together with `Real.arctan_add` and variants. PR 9847 by
  Parcly-Taxel: opened 2024-01-19, merged 2024-02-14 (about 4 weeks); the PR credits it to the
  "My 100 theorems"-style issue 6091. [READ PR page]
- ZetaValues.lean: `hasSum_zeta_nat` (zeta(2k) with Bernoulli numbers), `hasSum_zeta_two`
  (Basel, pi^2/6), `hasSum_zeta_four` (pi^4/90), and `hasSum_L_function_mod_four_eval_three`
  (pi^3/32), via Fourier series of Bernoulli polynomials.
- docs/100.yaml: #14 Basel (hasSum_zeta_two), #26 Leibniz (tendsto_sum_pi_div_four), #90
  Stirling (Stirling.tendsto_stirlingSeq_sqrt_pi); #53 "pi is transcendental" has links only,
  no declaration (so not in Mathlib).
- Chudnovsky.lean (Morrison, 2025; PR 29170 opened 2025-08-31, merged 2025-09-01): definitions
  chudnovskyNum, chudnovskyDenom, chudnovskyTerm, chudnovskySum = 12/640320^(3/2) * sum of
  terms. Docstring: no proof yet, anyone welcome to adopt; the identity sum = pi^-1 "is stated
  using `proof_wanted` in Wanted/Analysis/Real/Pi/Chudnovsky.lean" (I could not fetch that
  path; 404 at the guessed URL, so its current location may differ). Future work listed: use
  the formula to approximate pi; Heegner-number analogues with j((1+sqrt(-163))/2) =
  -640320^3. References: Milla (arXiv 1809.00533), Chen-Glebov (arXiv 1609.05778). PR text: the
  proof needs much more elliptic-curve material than Mathlib has; the author also said the
  estimates could give millions of digits in later PRs. PR 43920 (2026-09-18) moved the
  sanity-check `#eval` to MathlibTest. [READ file and PR]
- Open/closed PRs with pi in the title: PR 29653 (2025-09-14) only renamed deprecated Real.Pi
  module references. Search of the issue list for "BBP", "Bailey", "Bellard", "digit
  extraction", "spigot", "digits of pi": no hits (the "Bailey" hits were irrelevant). Open PR
  33281 (2025-12-25) about the integral of 1/sqrt(1-x^2) is the only open pi-adjacent item
  that surfaced. [READ API]

### Other Lean repositories
- metasecdev/math-proofs (GitHub; single author; 50 commits; 0 stars; updated 2026-11-01, last
  push 2026-11-16): Lean 4 "BBP formula, verified hex-digit extraction, irrationality measure
  at 16^n". 264 Lean files, of which about 250 are generated certificate files. The README
  claims: `bbpSeries_eq_pi` (BBP identity; file BBPPiIdentity.lean about 190 lines; proof by
  integral of a rational kernel and an arctan/log antiderivative: the standard route);
  guarded digit certificates (if lower and upper interval agree, the common value is
  floor(16^n pi)); an all-n result with guard depth about 570 n + 1.8 million digits, using a
  sharp Mahler-type irrationality measure of pi at 16^k; checked unconditionally for n <=
  2000 in CI and n <= 10000 locally (needs 10-16 GB RAM per file). It also records that the
  earlier capped certificate is refuted for huge n (n around 2^272). No statement about AI use
  in the README. I did not build it or run #print axioms. [READ README, tree, two files]
- Search for Lean repositories on GitHub (queries "bbp pi language Lean", "digits of pi
  lean4", "bailey borwein plouffe lean4"): only the repo above (plus an unrelated geometry
  repo). Coq/Isabelle GitHub queries: none (one 403). [READ API, weak]
- arXiv 2610.26539 (G. V. Chudnovsky): irrationality exponent of the lemniscate period, "a
  determinant proof with a Lean 4 formalization". The PDF came back compressed, so I read only
  the title. Related to pi through Gamma(1/4); worth a look. [SNIPPET]

### Coq
- Bertot, Rideau, Thery, "Distant decimals of pi: formal proofs of some algorithms computing
  them and guarantees of exact computation", J. Automated Reasoning (2017/2019; arXiv
  1709.01743). Section 2.1: BBP (spigot) proved in Coq with Coquelicot; digit function
  `NpiDigit` proved correct only in a partial-correctness sense: it works mod 2^p, keeps an
  under- and over-approximation, returns a digit only when both agree, otherwise None
  (28 bits for the millionth digit). Also two AGM algorithms (Brent-Salamin, Borwein) with
  fixed-point error bounds. Runs: millionth hex digit under 2 minutes; billionth hex digit
  about 19 hours on four cores, value 8; 1 million decimals. Bellard not mentioned. [READ ar5iv]
  [INFERRED] So "BBP proved correct" in Coq means: sound when it answers, not that it always
  answers.

### Isabelle
- AFP analysis list (2004-2026) shows: irrationality of zeta(5) (Hyman, 2026), Eberl's special
  functions, isoperimetric inequality. I saw no entry for BBP/Machin/Chudnovsky. [READ page,
  but only the visible list; weak]
- HOL-Analysis ex/Approximations.thy: approximates pi (and e, ln 2, gamma) using the simplifier
  with arctan series; digit count not read (page truncated). [READ partly]
- Wikipedia/UNSW Top 100 page refused (403), so status of the 100 theorems in other provers
  not checked.

### Formal Conjectures (Google DeepMind) and lean-eval
- Formal Conjectures: FormalConjectures/Wikipedia/NormalityOfPi.lean has one statement,
  `pi_normal_base_ten`, tagged research open; no mention of BBP, Bailey-Crandall.
  Wikipedia/Irrational.lean: e+pi, e*pi, e^e, pi^e, pi^pi, ln(pi), algebraic independence of e
  and pi, gamma: all open; Catalan's constant irrational marked "solved by an internal OpenAI
  model in September 2026" (file has sorry placeholders with a link). Wikipedia/
  Transcendental.lean: e+pi, e*pi, e^(pi^2), pi^e, pi^sqrt2, pi^pi, pi^(pi^pi), log pi: open;
  "one of pi+e, pi*e is transcendental" textbook. RiemannZetaValues.lean: no pi statement.
  Constants.lean: Gompertz and Catalan only. Rules: one problem per file; solved research
  problems are linked through a Palomar entry; proofs over 25-50 lines go to your own repo.
  The repo has about 1,400 stars and many open PRs (numbers near 8000). The tree has no BBP or
  Borwein-named file (I saw `Books/BorweinSineSeries.lean` and the tree up to about 654k
  characters, apparently complete). [READ]
- lean-eval (lean-lang.org/eval): problems are `@[eval_problem]` theorems with sorry, solutions
  verified by `comparator`; leaderboard top entry 207 solved (Axiom Prover) [SNIPPET].
  Problem "Chudnovsky formula for pi inverse" is listed, not solved, source Milla's paper
  (arXiv 1809.00533). The problem index did not load in the fetch tool, so I could not list
  other pi problems. [READ]

### Mathlib contribution rules (2026) [READ contribute page; Formal Conjectures defers to it]
- Disclose AI use in the PR description (tools and how). Substantial LLM-generated code gets
  the `LLM-generated` label (comment it). You must understand the code and justify design
  without AI. Using an LLM to write GitHub or Zulip comments is not allowed ("use your own
  words"). Low-quality LLM PRs may be closed without comment; repeated violations can mean a
  ban from PRs and Zulip.
- Review time: no promise; the page says over 2600 open PRs in mid 2026, so waiting is normal.
  Data points: PR 29170 (statement-only, small, by a core maintainer) merged in 1 day;
  PR 9847 (Machin, outside contributor) 26 days. [READ]; typical outside PRs may wait months
  (open PRs from Jan 2026 are still open: 33948, 34106, 34650) [READ API list].
- Small lemmas and extensions of existing theories are "almost always welcome". Reviewers need
  not be maintainers; reviewing others' PRs speeds your own; discuss in #mathlib on Zulip first.

## 3. What is open

- Chudnovsky's formula in Mathlib: stated as a wanted theorem by Mathlib's own file and by
  lean-eval (not solved). [READ, stated by the sources]
- Pi transcendental in Mathlib: not formalized (100.yaml), although Lindemann-Weierstrass is a
  known gap; not checked beyond 100.yaml. [READ]
- More digits in Mathlib: only 20 decimals; the Chudnovsky file lists "approximations for pi" as
  future work. [READ]
- BBP/Bellard/digit extraction in Mathlib: not found (weak).
- Normality of pi in any base: open, listed in Formal Conjectures. [READ]
- Correctness of digit extraction for all n: a guard-digit argument needs the digit n+g not to
  start a long run of 0s/15s, i.e. a lower bound on |16^k pi - integer|, an irrationality
  measure. [INFERRED] The Coq paper only gets partial correctness; the Lean repo above uses
  Mahler's measure (claimed). The sharp known measure for pi is around 7.1 (Zeilberger-Zudilin
  2020), not from my reading; [INFERRED from memory, not checked this session].

## 4. Leads for this project, ranked

1. **BBP identity (and Huvent's, Bellard's) as a clean Mathlib PR.** Statement:
   sum_k 16^(-k) (4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6)) = pi in Real, plus its
   `HasSum` form, put in Mathlib/Analysis/Real/Pi/ (like Leibniz.lean). The project already has
   the proof; the standard integral proof is about 190 lines in the other repo, so the PR would
   be small and fits "single result, existing theory". Size: days of porting and style, then
   weeks to months of review. Noticeable: first BBP in Mathlib (not found there), a natural
   companion to the wanted Chudnovsky. Caveats: AI disclosure and the LLM label required; the
   owner must be able to defend every line; comments in his own words.
2. **BBP digit extraction proved correct, with an explicit guard.** Statement: for every n, the
   hex digit of pi at position n equals the digit computed by the integer BBP algorithm with
   guard g(n) given as a function, with a proof that the guard works. This is the exact gap
   between Coq's partial correctness and a total statement. The needed input is a lower
   bound |16^k pi - m| > 16^(-c k) for all large k, an irrationality measure; the project
   has Baker for logarithms, but pi's measure is a different (Mahler/Hata type) theorem; the
   other Lean repo claims to have done it with Mahler's method (unverified). Options:
   (a) cheap and safe: certify specific ranges (n up to N) by interval arithmetic and
   `decide`, as the Coq work did; (b) all-n with an imported measure as a hypothesis, stated
   explicitly. Size: weeks. Worth noticing only if all-n is truly unconditional and checked
   against that repo; otherwise a verified-up-to-N statement is modest.
3. **Bellard's formula and the full list of base-2 formulas with Huvent's** (already
   classified here). Statement: Bellard's 1997 series for pi (ten terms over 2^10 j) and
   Huvent's (2/3 non-zero terms per bit) as `HasSum` theorems in Real. Fits: the project's
   classification gives these as special cases. Size: days each given the existing proofs.
   Noticed: not in Mathlib or the formal repos I found; also a good demonstration of
   "optimal formula, machine-checked". Mathlib may judge them as too special; a PR could
   instead go to a separate library (a Lake package) and Formal Conjectures does not list
   them, since they are theorems, not conjectures.
4. **More digits of pi in Mathlib** (pi_gt_d30, d50 ... or via Machin with the already merged
   Machin identity): smallest of all; each is a numeric lemma with `norm_num`. Low value,
   but a good trial PR to learn the review process. Statement: e.g. 3.14159265358979323846264338327
   < pi < ...328; needs rational witnesses (the file's Mathematica script can be copied) or a
   Machin-based series bound. Size: days.
5. **Chudnovsky identity.** Size: out of reach (needs modular forms and elliptic-curve theory;
   the Mathlib author said so). Not for this toolkit.
6. **Lean-eval / Formal Conjectures submissions.** Formal Conjectures wants conjectures, not
   proved theorems; the project's open items could be submitted as statements if they are
   open (e.g. "log b has a degree-1 BBP formula in base b iff b is a power of 2 or 3" is now
   proved here, so it belongs in the Palomar/"solved" category, which requires a link to a
   proof in a separate repo). The base-10 statement "no degree-1 BBP formula for pi in base
   10" was listed here as stated as known in print, so it may not qualify as a conjecture.
   Size: days; value: visibility only. [INFERRED]
7. **Compare with the metasecdev repo** (independent claim of BBP digit extraction in Lean).
   Not a lead to prove, but a cross-check: file BBPPiIdentity.lean as a reference for the
   BBP proof route, and its BBPCapRefutation for a known failure mode of capped digit
   extraction. Size: a day.

## 5. Overlap or conflict with section 1 of the rules file

- No conflict with the classification, optimality, base-3, base>=5 or logarithm results: I
  found nothing in Mathlib, Formal Conjectures, lean-eval, Coq or Isabelle that proves or states
  them.
- Partial overlap on the BBP identity and digit extraction itself: the metasecdev Lean repo
  (BBP identity; guarded digit extraction with Mahler-type irrationality measure) and Coq
  (Bertot-Rideau-Thery, partial correctness). Neither covers classification or optimality.
- Page content addressed to me: none observed.

## 6. Sources

- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Real/Pi/Chudnovsky.lean
  (read via raw.githubusercontent.com, same path for Bounds, Leibniz, Wallis, Irrational)
- https://github.com/leanprover-community/mathlib4/pull/29170 , /pull/9847 , /pull/43920 , /pull/29653
- https://raw.githubusercontent.com/leanprover-community/mathlib4/master/docs/100.yaml
- https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/NumberTheory/ZetaValues.lean
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.html
- https://leanprover-community.github.io/contribute/index.html
- https://lean-lang.org/eval/problems/chudnovsky_formula_for_pi_inv/ , https://lean-lang.org/eval/
- https://github.com/google-deepmind/formal-conjectures (files NormalityOfPi, Irrational,
  Transcendental, RiemannZetaValues, CONTRIBUTING.md under FormalConjectures/Wikipedia)
- https://github.com/metasecdev/math-proofs (README, BBPPiIdentity.lean, BBPSpigot.lean)
- https://arxiv.org/abs/1709.01743 (via https://ar5iv.labs.arxiv.org/html/1709.01743)
- https://arxiv.org/abs/1809.00533 (Milla), https://arxiv.org/pdf/1609.05778 (Chen-Glebov)
- https://arxiv.org/pdf/2610.26539 (G. V. Chudnovsky, lemniscate period, Lean 4; title only)
- https://www.isa-afp.org/topics/mathematics/analysis/ ;
  https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/library/HOL/HOL-Analysis-ex/Approximations.html

## 7. Search log

WebSearch (4 calls):
1. "Chudnovsky formula Lean 4 Mathlib proof pi formalization"
2. "lean-eval benchmark formal statements Lean"
3. "Distant decimals of pi formal verification Coq Bertot Rideau Thery"
4. "Isabelle Archive of Formal Proofs pi digits BBP Machin Chudnovsky"

Endpoint / fetch queries (about 62 fetch calls, of which these are the distinct ones; items
marked * failed or were empty):
GitHub issue search on mathlib4: 1 "pi BBP"*, 2 Chudnovsky, 3 Machin, 4 "Real.pi" in title,
5 "Chudnovsky in:title", 6 Bailey, 7 Basel, 8 "digits of pi", 9 "Bellard OR digit extraction OR
spigot"*, 10 "pi approximation", 11 "Chudnovsky open PRs", 12 "AI generated policy"*, 13
"LLM-generated" count; GitHub code search: 14 proof_wanted pi (401), 15 proof_wanted Analysis
(401), 16 Machin (401), 17 Chudnovsky language:lean (401); GitHub repository search: 18 "BBP pi
language:Lean", 19 "digits of pi lean4", 20 formal-conjectures, 21 "bbp formula lean", 22
"bailey borwein plouffe lean4"*, 23 "bbp pi coq"*, 24 "pi digits isabelle" (403); GitHub
issues of formal-conjectures: 25 BBP*, 26 pi; GitHub trees: 27-33 formal-conjectures tree in
seven pages, 34 mathlib4 tree (only first 100k chars), 35 metasecdev tree, 36 mathlib4
contents/Pi directory, 37 contents of Wanted (404); raw files: 38 Bounds, 39 Chudnovsky (twice),
40 Wanted/.../Chudnovsky (404), 41 docs/100.yaml, 42 Irrational, 43 Wallis, 44 Leibniz, 45
ZetaValues, 46-50 formal-conjectures NormalityOfPi, Irrational, Transcendental,
RiemannZetaValues, Constants, 51 its CONTRIBUTING, 52-54 metasecdev README, BBPPiIdentity,
BBPSpigot; pages: 55 PR 29170, 56 PR 9847, 57 CONTRIBUTING.md (mathlib), 58 contribute page,
59 lean-eval problem page, 60 lean-eval home, 61 mathlib docs Arctan, 62 ar5iv Coq paper, 63
arXiv abs 1709.01743, 64 arXiv PDFs (1709.01743, 2610.26539; compressed), 65 arXiv API x2 (429),
66 OpenAlex "formal proof BBP...", 67 Semantic Scholar (429), 68 Crossref BBP formal, 69 AFP
search page and topics page, 70 Isabelle Approximations, 71 UNSW Top100 (403).

Totals: WebSearch calls: 4. Endpoint/fetch queries: about 65 (of which about 20 were empty or
refused).
