# W2-Q13: open, well-defined tasks in the Lean prime number theorem projects

Pass date: 2026-11-22. Marks: [READ] seen through the fetch tool on the source's own page or raw file
(the fetch tool returns a model-made summary of the page, so quoted Lean code is only as exact as that
summary), [SNIPPET] seen only in a search result or API record, [INFERRED] my own conclusion.
Own computations (PowerShell, my own code, nothing from the web) are marked [COMPUTED].
Refused endpoints: GitHub contents API for two subdirectories (403), GitHub code search (403), one
Zulip archive URL (404). Items in the teorth/IEANTN issue list carry timestamps of 2026-11-23 UTC.

## 1. Summary

1. The task named in the brief is real and is still `sorry` today, in the PNT+ file Dusart.lean, as
   `proposition_5_4c`. Exact statement in section 2. No GitHub issue exists for it (the blueprint node
   has no discussion number), so nobody has claimed it. [READ]
2. The source's own comment calls it "a computer computation, likely not formalizable within Lean". My
   count says it is small: 22115 pairs of consecutive primes, or a witness chain of only 2745 primes.
   Tightest case: x = 89693 itself (next prime 89753, allowed length 60.47, needed 60). [COMPUTED]
3. Correction to the earlier report (Q08): closing 5.4c does not by itself make Lcm unconditional.
   `proposition_5_4` combines 5.4a, 5.4b, 5.4c; 5.4b is proved in Lean but uses `eSHP.table_8`, whose
   verification (`table_8_prime_gap`) is `sorry`; 5.4a uses BKLNW Table 15 and Dusart Theorem 4.2
   (the latter `sorry`). [READ] In the new IEANTN repo the whole proposition is one literature stub
   (`Dusart2018.v1.proposition_5_4`, no issue number) and `Lcm.v1` imports it. [READ]
4. Related finite tasks: the small-prime part of `table_8_prime_gap` (the entries needed by 5.4b are
   below about 1.8e7), and Buethe numerics stubs in teorth/IEANTN (`lemma_3_constant_nonpos`,
   `li_minus_pi_below_1e7`, `eq_6_2`).
5. There is a ready-made technique in an open PR: kernel-checked segmented sieve with `decide +kernel`,
   no `native_decide`, for psi bounds up to 1e10 (PNT+ PR #1804, by an outside contributor with Claude
   as co-author). [READ]
6. Rules: claim by commenting `claim`; at most 3 open AI-assisted PRs; disclose the tool in the PR body
   (a CI job labels it); contributor must understand the diff; new IEANTN material belongs in
   teorth/IEANTN. Mathlib has its own AI section (disclose, no LLM-written comments). [READ]
7. IEANTN receipts are checked by Comparator with only the three standard axioms, so `native_decide`
   disqualifies a receipt (it must be marked `lean-noncompliant`). PNT+ itself does use `native_decide`
   (Chebyshev.lean `allChecks_11723`). [READ]
8. Active hazard: tasks are sometimes false as printed. Issues #260 and #268 in teorth/IEANTN show two
   Buethe numerics conclusions that are false as stated. Audit a statement (small script) before
   starting a proof. [READ]

## 2. What is known

### 2.1 The Dusart Proposition 5.4 task (question 1)

- File: `PrimeNumberTheoremAnd/IEANTN/Dusart.lean` in AlexKontorovich/PrimeNumberTheoremAnd (main).
  [READ, raw file]
- Exact Lean (as reported by the summary of the raw file):
  `theorem proposition_5_4c (x : ℝ) (hx : x ∈ Set.Icc 89693 360653) : HasPrimeInInterval x (x / (log x)^(3:ℝ)) := sorry`
  Blueprint node `Dusart_prop_5_4c`, "substep 3", no `discussion` number; proof string says it is a
  computer computation, likely not formalizable in Lean. [READ]
- Definitions (teorth/IEANTN Vocabulary/PrimeGaps.lean): `HasPrimeInInterval x h := ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ (p : ℝ) ≤ x + h`;
  `HasPrimeInInterval.logPower X₀ k := ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x) ^ k)`. [READ]
- Assembly: `proposition_5_4 : HasPrimeInInterval.log_thm 89693 3` is a three-way case split
  (x <= 360653 uses 5.4c; x >= 4e18 uses 5.4a; between uses 5.4b). Closing 5.4c leaves 5.4 depending
  only on whatever 5.4a and 5.4b depend on. [READ]
- 5.4a (x >= 4e18): proved, via BKLNW Table 15 row at exp 29, M2 = 2.4334e-2 and `Eθ.hasPrimeInInterval`.
  5.4b (360653 < x < 4e18): closed 2026-06-19 (issue #911, PR #1124, "prove proposition_5_4b"); the
  proof splits at 370261, 492113, 2010733, 17051707 with gap records 112, 114, 148, 180 from
  `eSHP.table_8`, then uses an `nth_prime` argument with the bound 1476 for gaps. [READ]
- Status of the table: `eSHP.table_8_prime_gap (p g) (h : (p, g) ∈ table_8) : prime_gap_record p g`
  is `sorry` ("verified by computer, unlikely formalizable except for small values"); the converse
  `table_8_prime_gap_complete (hp : p ≤ 4 * 10 ^ 18)` is `sorry`; only tests for p < 30 are proved
  (`table_8_prime_gap_test`, `..._complete_test`). `max_prime_gap` (all gaps up to 4e18 are at most
  1476) is proved from the `sorry` converse. [READ eSHP.lean]
- Claims and activity: searches of PNT+ issues for "5.4c", "89693", "360653" return only a merged
  fix PR (#539, `prod_epsilon_ge`). The Dusart issues open on 2026-11-22 are #1762, #1773, #1774, #1775
  (Table 4.2 rows, `pi_inequality`), all unassigned, and PR #1799 (AI-labelled, label `cursor`,
  open, no review) that removes duplicate restatements in TMEEMT.lean; none touches 5.4c. [READ]
- Zulip: the miniproject "Primes in short intervals" (opened 2026-02-08, tasks PNT#900-913) says the
  small-x check for Proposition 5.4 is infeasible to formalize in Lean; it quotes the range as
  89693 to 360353, which differs from the Lean file's 360653 (a typo on Zulip or an earlier version;
  I did not resolve it). The Lean file has 360653, which is a prime (the end of a record gap 96). [READ summary / COMPUTED]
- In the new repo teorth/IEANTN: `Dusart2018.v1.proposition_5_4 := IEANTN.HasPrimeInInterval.logPower 89693 3`,
  status `stub`, designated justification is literature (the paper), notes suggest splitting the
  analytic branch and the gap table into separate nodes; the paper is said to prove it from three
  pieces: analytic argument above 4e18, a gap table 360653 to 4e18, direct verification on
  [89693, 360653]; no issue number; `Lcm.v1.lcmUpto_not_highlyAbundant` (n >= 89693^2) imports it, and
  has a Comparator receipt that is an implication from this import only. `Lcm.v2` takes the prime-gap
  statement `logPower X₀ 3` as a hypothesis with X₀ abstract. [READ]
- Could not read Dusart 2018 itself (Ramanujan J. 45): arXiv 1002.0442 is the earlier 2010 paper and
  has no Prop. 5.4. So the statement is checked only against the Lean file and the IEANTN audit
  note, not against the printed paper. [READ]

### 2.2 My finite computation for 5.4c [COMPUTED]

For x in [p, q) between consecutive primes, the interval (x, x + x/log^3 x] contains a prime iff
q <= x + x/log^3 x; the right side increases for x > e^3, so the worst x in each block is its left end
(x = max(p, 89693)). So 5.4c is equivalent to: for every consecutive prime pair (p, q) with q > 89693,
p <= 360653: q - max(p, 89693) <= max(p,89693)/log^3(max(p,89693)).
- Number of pairs: 22115. All satisfy it (double precision).
- Smallest slack (allowed minus needed): pair (89689, 89753) at x = 89693: allowed 60.47, needed 60,
  slack 0.47. Next: (107377, 107441), slack 5.08; (155921, 156007), gap 86 vs 91.21, slack 5.21.
- Greedy witness chain (pick the farthest prime within the allowed length, margin 1e-6): 2745 primes
  from 89693 to 360653. So a proof needs about 2.7 thousand `Nat.Prime` facts (numbers below 4e5, the
  size where `norm_num`'s primality extension is fine) plus one rational upper bound on log per block.
- A rigorous proof needs a rational upper bound for log x on blocks of x; the 0.47 slack at 89693
  means log 89693 must be known to within about 0.3 percent (log 89693 is about 11.40).
These are my numbers; they are not in any source.

### 2.3 How finite checks are done (question 4) [READ unless marked]

- Table data: separate `*_tables.lean` files with minimal imports (rule in PULL_REQUEST_STYLE);
  `eSHP_tables.lean` holds `table_8 : List (ℕ × ℕ)` (first entries (2,1), (3,2), (7,4), (23,6),
  (89,8), (113,14); last (1425172824437699411, 1476)). `PrimeTables.lean`: `Nat.count Nat.Prime`
  bounds proved by `simp only [count_ofNat]; norm_num`; large primes (3999999999999999791 etc.)
  by `prime_cert%` Pocklington certificates (library PrimeCert by Bhavik Mehta and Kenny Lau, no
  `native_decide`, kernel only, certificates generated by a python script needing a factorization of N-1).
- `decide` for small primality (Goldbach.lean small case, eSHP tests). Goldbach base cases to 4e14
  and 4e18 are left `sorry`. [READ Goldbach.lean]
- `native_decide`: used in PNT+ Chebyshev.lean (`allChecks_11723`, base case for psi <= 1.11 x),
  the linter is switched off in PrimeTables.lean. In teorth/IEANTN, Comparator allows only
  propext, Classical.choice, Quot.sound; a proof needing `native_decide` is to be marked
  `lean-noncompliant` with a note, never given a fake receipt. [READ]
- Kernel sieve: PNT+ PR #1804 (open, 36 commits, labels ai, claude; author Garald1): kernel-checked
  bounds |psi(x) - x| <= (4/5) sqrt x for 1500 <= x <= 1e10 and <= sqrt x for 8 < x <= 1e10 using
  `decide +kernel` over a segmented sieve (about 38186 segments in 955 generated modules); stated
  axioms standard only; Comparator said ok. [READ]
- Real-number bounds: LeanCert (alerad/leancert, interval arithmetic for Lean 4, 51 stars, pushed
  2026-11-05) with PNT+ `LeanCertEnclosures.lean` (checked interval enclosures for pi, Li, E_pi; Li by
  192 checked quadrature panels per endpoint). Also `interval_decide` in Goldbach.lean and in an
  earlier report; the project reverted LeanCert once for build time (Q08). Issue #258 (closed by
  PR #264, solution PR #236): E_pi floor on [e, e^6] by exact prime counts on 80 half-open cells with
  kernel-checked quadrature, no `sorry`, no `native_decide`. [READ]
- Verified zeta zeros: IEANTN issue #214 ports ten range proofs (height 0 to 10000, 10142 zeros) from an
  external repository built by Garald1; one range can take more than three hours in Comparator, the CI
  limit is 180 minutes; v11 assembles them. Statement of method (interval arithmetic) not given in the issue. [READ]
  A web search also found an outside repo (n0zer0d4y/simple-zeros-hilbert-robin-epstein, 1 star) with
  Arb-style certificates plus Lean, and a repo `anthropics/zeta-23-lean` described as sorry-free with
  certificate bounds computed outside Lean. [SNIPPET]
- Trusted external code is acceptable to the maintainer for real-number checks (Zulip, Goldbach
  subproject); the `TrustedNumerics` files in FKS2 are the in-repo form. [READ summary / Q08]

### 2.4 Rules for contributions (question 3) [READ]

PNT+ (AlexKontorovich/PrimeNumberTheoremAnd):
- CONTRIBUTING.md: tasks are GitHub issues; comment `claim` (auto-assigned if free), `disclaim`;
  do not work on an issue assigned to someone without talking to them; fork, branch from main;
  `propose #PR` (only the claimant); `awaiting-review` after green CI; ask on Zulip stream
  PrimeNumberTheorem+ if unsure. New IEANTN contributions go to teorth/IEANTN; claimed tasks may continue here.
- PULL_REQUEST_STYLE.md: one motivation per PR, under about 500 lines ideal; do not weaken
  hypotheses; keep `@[blueprint]` metadata; heavy numerics in `*_tables.lean` siblings; a PR closing a
  sorry must not add sorries; run `lake build` for the module and `lake build :blueprint` first;
  PR body with Motivation, Scope, Test plan; conventional prefix titles (`feat(Dusart): ...`).
  AI-assisted section: disclose the tool in the PR body (CI reads it and adds labels ai, claude, cursor,
  gpt, gemini, aristotle ...); consolidate; actually run the test plan; check reuse of the paper's
  precursors; "the AI wrote it" is not an acceptable answer to a reviewer; respect the claim
  workflow, no unclaimed mass edits; at most 3 open AI-assisted PRs at once. Reviewers may close PRs with
  undisclosed AI use or inlined heavy computation. Zulip thread (Jan 2026) shows no formal policy
  beyond this disclosure practice at that date; Tao asked for tool disclosure and Co-Authored-By trailers.
- teorth/IEANTN CONTRIBUTING.md: comment `claim`/`disclaim`/`propose PR #n` on board issues; claims do
  not expire; work in order of blast radius (solutions, then conclusions, then vocabulary); a solution
  is a separate Lake project `Solutions/<Family>.<version>/` (script `new-solution`), `progress` counts
  holes; verification by Comparator is dispatched by a maintainer after approval; never edit a
  conclusion others depend on, make a new version; receipts are never written by hand. AI policy:
  one-line disclosure in the PR body, the contributor must be able to defend the diff; disclosure is for
  calibrating review, not disqualification. CLAUDE.md/AGENTS.md exist for coding agents. Every file
  needs the four-line copyright header; license Apache 2.0.
- Mathlib (contribute page): disclose AI use in the PR description naming tool and use; label
  substantial LLM-generated code `LLM-generated`; no LLM-written GitHub or Zulip comments; understand
  and justify everything; low-quality LLM PRs may be closed, repeat violations can lead to a ban. [READ]

## 3. What is open (question 2)

Stated by the sources as unproved unless marked. "Finite" = reduces to a bounded check.

### 3.1 PNT+ Dusart.lean (32 sorries at read time) [READ]
- Finite or near-finite: `proposition_5_4c` (above). Everything else listed analytic in nature; but
  these have an elementary small-range part: `lemma_5_10a {k} (hk : k ≥ 4) : nth_prime' k ≤ k * Real.log (nth_prime' k)`,
  `lemma_5_10b {k} (hk : k ≥ 2) : Real.log (nth_prime' k) ≤ Real.log k + Real.log (Real.log k) + 1`,
  `proposition_5_16 {k} (hk : k ≥ 3) : nth_prime' k ≥ k * (log k + log log k - 1 + (log log k - 2.1)/log k)`,
  `proposition_5_15` (k >= 688383), `lemma_5_14` (k >= 178974), `proposition_5_12` (k >= 781),
  `corollary_5_2_a..f` (x >= 17, 88789, 599, ...), `corollary_5_3_a..d` (x >= 5393, 468049, ...),
  `theorem_5_6/5_7/5_9` (x >= 2278383, 912560, 2278382). The file carries no `proof :=` strings for these.
  Which of them need a small-range enumeration depends on Dusart's own proofs (not read). [INFERRED]
- Issues open: #1762 `pi_inequality` from `corollary_5_3_a` (Dusart 1999 version) and #1773, #1774, #1775
  (theta absolute bounds from Table 4.2 rows). Analytic restatements; none assigned. [READ]

### 3.2 Other PNT+ open items [READ]
- `RS_prime.theorem_d` (sum (log p)/p < log x for x > 1), issue #1692, assigned (The56thSpirit, since
  2026-10-28); suggested route: finite range by computation plus large range from Mertens constant
  and theta bounds; a finite-range stepping-stone PR #1693 on (1, 40] existed. `theorem_c` (sum 1/p >
  log log x) closed 2026-11-11 (#1694). Claimed, so not a lead unless the claimant disclaims.
- `RS_prime.theorem_12` (`ψ x < c₀ * x` for x > 0) is `sorry` in Chebyshev.lean; elementary-looking but
  the constant is 1.03883 (analytic input needed); `psi_upper_clean` (psi <= 1.11 x) is proved.
- TMEEMT.lean sorries (about 80 statements: Buethe 2a-2d, RS, Dusart 1999, Ramare, Mawia, Trevino,
  Deleglise-Nicolas, Rosser, Robin, Axler, De Koninck-Letendre, short-interval results from
  Schoenfeld 1976 to Cully-Hugill, zeta bound statements). Flagged by the file's own reader as finite
  or computation-heavy: `Robin.p_n_lower_const1` (p_n > n(log n + log log n - 1) for n >= 2 and p_n <= 1e11)
  and `ChengGraham2004.zeta_half_bound_small` (|zeta(1/2+it)| <= 2.657 for 0 <= t <= e). Neither is
  elementary. [READ summary; the classification is the summary's]
- BKLNW tasks: #1761 "Verify Table 15" (claimed, lsmeng, no activity since 2026-08-26), #1257 "Verify
  Table 11" (claimed, giuseppesorge; PR #1727 merged a split-domain theta bound for it), FKS2 #722
  (Cor 23), #1429 (Cor 24) claimed. Kadiri task issues #1476-#1546 claimed (Robby955). IK (Ivic-Krishna
  style identities, Mathlib-flavoured) tasks #1685, #1688, #1690, #1240, #1011 etc. are algebra and
  not finite checks. Open PRs: #1804 psi finite check, #1768 BKLNW Lemma 10, three ZeroDensity PRs. [READ]
- Issue #1814 (2026-11-22, by a new account) asks the maintainers to formalize a claimed proof of the
  Riemann Hypothesis from a Zenodo manuscript; not a task. No text addressed to AI agents seen. [READ]

### 3.3 teorth/IEANTN (stub and finite nodes, STATE.md) [READ]
Node count 91 versions: 48 active (receipt), 14 awaiting-solution, 2 awaiting-verification, 27 stubs.
- `ButheNumerics.v1` (5 stubs). Exact statements:
  `lemma_3_constant_nonpos : primeCounting 1500 - li 1500 + (1500 - Chebyshev.theta 1500) / Real.log 1500 ≤ 0`;
  `li_minus_pi_below_1e7 : ∀ x, 2 ≤ x → x ≤ 10^7 → li x - primeCounting x ≤ margin 0 * (sqrt x / log x * (1.95 + 3.9/log x + 19.5/(log x)^2))`;
  `li_minus_riemann_pi_below_1e7` (|li x - riemannPrimeCounting x| < margin 0 * sqrt x / log x, same range);
  `eq_6_2 : ∀ t, 100 ≤ t → t ≤ 5*10^10 → -0.8 ≤ (t - psi t)/sqrt t ∧ (t - psi t)/sqrt t ≤ 0.81`;
  `lemma_3_constant_gt_at_10 : 0.1 < primeCounting 10 - li 10 + (10 - theta 10)/log 10` is reported
  FALSE as stated (issue #260, open). Also `Buthe.v2.lemma_3_bounds` false as printed (issue #268, sign
  of the A term, counterexample at a = 3e6, b = 1e7+1000, x = 1e7). Hold until those are resolved.
- `FKS2Numerics.v1` (5 stubs): `table6_row2_floor` (now solved, issue #258), `nu_asymp_e30_le`,
  `theta_asymp_ge_one_below_e30`, `corollary_22_mid_range` (all x in [2, e^20000]), `corollary_23_mid_range`.
- `PrimesBetweenCubes.v1.prime_between_successive_cubes`: ∀ n >= exp(exp 32.76), prime in (n^3, (n+1)^3)
  (stub, analytic, out of reach). `Dusart2018.v1.proposition_5_4` (stub, above).
- `ZetaZeroLocations.v1-v10` (issue #214: v1 informally taken by one contributor, another offered to
  take v2, v3), `LowZeroes.v1` (sum_inv_ordinates_below_2e4, no_zeroes_below_first_ordinate),
  `ZetaLogDerivValues.v1` (logDeriv_two ...), `BKLNWNumerics.v1`, `DudekPlattNumerics.v1-v3`,
  `FKSNumerics.v1`, `Buthe2016.v1`.
- Issue #215: no node asserts `RiemannHypothesisUpTo 1894438.5122` although ten conclusions assume it;
  fix is a conclusion with citation justification (Rosser-Yohe-Schoenfeld 1969) and a spare bridge from
  `Platt2017.v1.rh_up_to` (RH up to about 3.06e10). In progress by one contributor (PR #207 reopened).
  Issue #253: `psi_le_below_11723` threshold is an artefact (decision pending, not a blocker).
- Open on 2026-11-23: 26 items (issues and PRs), 6 not read.

### 3.4 Related projects [SNIPPET / Q08]
Kontorovich-Tao main blueprint (Wiener-Ikehara, medium and strong PNT, Brun-Titchmarsh, ZeroDensity,
Kadiri) is analytic; verified zeros and Goldbach base verifications are in IEANTN as above. I did not
check the DeepMind Formal Conjectures repository or Erdos problem pages in this pass.

## 4. Leads for this project, ranked (question 5)

Lead 1 (days to one or two weeks). Close `proposition_5_4c`.
- Exact statement: the `sorry` quoted in 2.1.
- Plan: (a) reduce to a lemma on naturals, `∀ i < 2745, (p i : ℕ).Prime ∧ p (i+1) - p i <= bound` for the
  witness chain, with the chain as a `List ℕ` in a `*_tables.lean` sibling (generated outside Lean,
  checked inside; the chain is data, not trusted); (b) primality of each entry by `norm_num` or `decide`
  (numbers below 4e5); (c) real part: for x in [p_i, p_{i+1}) show x + x/log^3 x >= p_{i+1} by
  monotonicity of x/log^3 x ... (increasing for log x > 3) and a rational upper bound of log p_i per
  block (use `Real.log_le_sub_one_of_pos`-style or `Real.exp_one_lt_d9` based bounds; a few blocks);
  (d) edge cases x = 89693 (slack 0.47) and x = 360653.
- Why the toolkit fits: exact enumeration plus rational bounds; our own sieve gives the chain. 
- Risks: the Lean statement uses `Real.rpow` with exponent `(3:ℝ)` (convert to `^ 3`); the real-valued
  step needs care; reviewers may ask that the heavy list sit in a tables file.
- Worth noticing: removes a sorry labelled "not formalizable"; it also supports the IEANTN suggestion to
  split `Dusart2018.v1` into sub-nodes. Honest scope: this alone does not make `proposition_5_4` or `Lcm`
  unconditional (see summary item 3). Venue: PNT+ PR `feat(Dusart): prove proposition_5_4c`, with an
  AI disclosure line and Co-Authored-By trailer; claim first (there is no issue: ask on Zulip or open
  one, since the claim flow needs an issue on the project board). Also consider a node in teorth/IEANTN
  (new work is directed there) with a Solution project.

Lead 2 (one to three weeks). The small part of `eSHP.table_8_prime_gap`.
- Statement: `∀ p g, (p, g) ∈ table_8 → p ≤ 17051707 → prime_gap_record p g` (the entries 5.4b uses are
  at or below 17051707 plus those with gap 180 or less; the exact bound needed must be read from the
  proof of 5.4b; `prime_gap_record`'s definition I did not see). [INFERRED]
- Method: the kernel sieve of PR #1804 (`decide +kernel`, standard axioms) scales this: 1.8e7 is
  about 550 times smaller than the 1e10 of that PR; or `Nat.Prime` per entry plus a Bool-checked gap
  scan. The full table (to 1.4e18) is out of reach; but the converse `table_8_prime_gap_complete`
  needs all primes to 4e18: out of reach.
- Why it matters: it makes 5.4b's use of the table honest for x below 1.8e7 (the table beyond that
  stays a `sorry`). Worth noticing as a partial result, clearly labelled.

Lead 3 (one to three weeks, after audit). `ButheNumerics.v1.lemma_3_constant_nonpos` and
`li_minus_pi_below_1e7`.
- Statements: section 3.3. First task: a numerical audit (do the statements hold? issues #260 and
  #268 show two siblings that are false). Then: pi(1500) = 239 and theta(1500) as an exact sum of
  logs with rational enclosures, li(1500) by checked quadrature (LeanCert or a Taylor series
  `LiSeries.lean` exists in PNT+). For `li_minus_pi_below_1e7` one needs, for each of the 664579 prime
  cells below 1e7, a certified bound on li between primes (cell certificates as in the PR for #258).
  Heavy, weeks. Fits our enumeration; the real-analysis part (li quadrature) is where the work is.
- Worth noticing: closes a numerics stub that the IEANTN network lists as open; but requires
  Comparator-clean proofs (no `native_decide`).

Lead 4 (days to weeks). Small-range pieces of Dusart's k-th prime statements.
- Statements: `lemma_5_10a`, `lemma_5_10b`, `proposition_5_16` (k >= 3, lower bound with 2.1),
  `proposition_5_12` (k >= 781), `lemma_5_14` (k >= 178974), `proposition_5_15` (k >= 688383), exact Lean in 3.1.
- Plan: for each, the range below the analytic threshold is finite (k up to 688383: about 7.8e6 primes
  below, 1.6 times the size of the table in lead 2 for k to 688383 => p_k about 1e7);
  check with a kernel sieve or with a list of p_k, and use rational enclosures of log log. Whether the
  statements follow from other sorried items (Corollary 5.2/5.3) was not checked; open the file
  and see which proofs are "finite part + analytic part". [INFERRED]
- Caution: `lemma_5_10a` was once misformalised (false for k = 4 in an earlier version). Audit by
  script before proving.

Lead 5 (weeks, stretch). `Robin.p_n_lower_const1` (n >= 2, p_n <= 1e11 implies p_n > n(log n + log log n - 1))
or the finite half of `RS_prime.theorem_d`.
- 1e11 is 10 times the largest range PR #1804 has done (1e10); would need that sieve infrastructure
  merged first, and real-number bounds at about 4.1e9 primes (an `n`-cell certificate scheme as for Buethe);
  `theorem_d` is claimed. Marked a lead only if the sieve of #1804 lands.

Not recommended: Goldbach base cases (4e14, 4e18), Dusart Theorem 4.2 analytic parts, anything under
"Kadiri", "ZeroDensity", `PrimesBetweenCubes`: out of reach or claimed.

Process advice for any lead [INFERRED from sections 2.3 and 2.4]: (1) write the audit script first (the
network finds false statements regularly); (2) comment `claim` or post on Zulip before building;
(3) keep the generated data in a separate tables file; (4) state tools (Claude, Fable) in the PR body
and Co-Authored-By trailer; (5) at most 3 open AI-assisted PRs; (6) for IEANTN receipts avoid
`native_decide`; (7) the project's Lean/Mathlib pin differs from ours: build against its lake manifest.

## 5. Overlap or conflict with the project results

No overlap with the BBP and base classification results (nothing in these projects concerns BBP series
or Baker's theorem). Conflict with the earlier Q08 report: Q08 said 5.4c "blocks" the lcm(1..n) result;
precisely, 5.4c is one of three sorry-dependent pieces; 5.4b rests on `table_8_prime_gap`, and the
IEANTN version of Lcm imports a literature stub. Also Q08 said Dusart.lean has 3 proofs and 33 sorries;
at read time 5.4a and 5.4b are proved, 32 sorries remain.

## 6. Sources

https://github.com/AlexKontorovich/PrimeNumberTheoremAnd (CONTRIBUTING.md, PULL_REQUEST_STYLE.md,
README.md, PrimeNumberTheoremAnd/IEANTN/{Dusart,Lcm,Goldbach,PrimeTables,TMEEMT,Chebyshev,LeanCertEnclosures,PrimeInInterval}.lean,
eSHP/eSHP.lean, eSHP/eSHP_tables.lean, RosserSchoenfeld/RosserSchoenfeldPrime.lean; issues 1692, 1761, 1814, 911, 913, 902; PR 1799, 1804)
https://github.com/teorth/IEANTN (README.md, CONTRIBUTING.md, CLAUDE.md, AGENTS.md, STATE.md,
docs/NODES.md, IEANTN/Vocabulary/PrimeGaps.lean, Nodes/Dusart2018/v1, Nodes/Lcm/v1 and v2,
Nodes/ButheNumerics/v1, Nodes/FKS2Numerics/v1, Nodes/PrimesBetweenCubes/v1; issues 64, 214, 215, 253, 257, 258, 268)
https://github.com/b-mehta/PrimeCert ; https://github.com/alerad/leancert
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/NormNum/Prime.html
https://leanprover-community.github.io/contribute/index.html
https://leanprover-community.github.io/archive/stream/423402-PrimeNumberTheorem+/ (topics: Disclosure of AI tools in PRs; New miniproject: Primes in short intervals; New subproject: Odd goldbach for small n)
https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/policy.20proposal.3A.20mention.20AI.20use.20in.20PR.20description.3F.html
https://ar5iv.labs.arxiv.org/html/1002.0442 (Dusart 2010; no Prop. 5.4)

Prompt-injection notice: no page contained text addressed to me. Issue #1814 is a request to the
maintainers, not to an agent.

## 7. Search log

WebSearch (2): 1 "Lean 4 formal verification zeros of the Riemann zeta function interval arithmetic
certificate height 10000 Mathlib"; 2 "Mathlib policy AI-generated pull requests contributions disclosure
leanprover zulip".
Endpoint queries (76, fetch tool; 4 refused or missing):
1 raw Dusart.lean (5.4). 2 GitHub contents PNT+ root. 3 issues search Dusart open. 4 CONTRIBUTING.md.
5 PULL_REQUEST_STYLE.md. 6 issues search 5.4c/89693/360653. 7 open issues list. 8 teorth/IEANTN root.
9 teorth open issues. 10 PR 1799. 11 PrimeInInterval.lean. 12 IEANTN CONTRIBUTING. 13 IEANTN README.
14 STATE.md. 15 AGENTS.md. 16 IEANTN/Nodes contents (403). 17 CLAUDE.md. 18 Dusart2018 dir.
19 Dusart2018 Conclusions. 20 Dusart2018 formalization.yaml. 21 docs/NODES.md. 22 PrimesBetweenCubes dir
(403). 23 PrimesBetweenCubes Conclusions. 24 ButheNumerics. 25 FKS2Numerics. 26 Vocabulary/PrimeGaps.
27 Dusart.lean (proof strings 5.4). 28 GitHub code search (403). 29 PNT+ IEANTN directory. 30 eSHP dir.
31 PrimeTables.lean. 32 Goldbach.lean. 33 eSHP.lean. 34 eSHP_tables.lean. 35 Lcm.lean. 36 IEANTN issue 215.
37 issue 214. 38 issue 253. 39 issue 64. 40 Zulip AI disclosure topic. 41 Zulip mathlib policy topic.
42 Mathlib contribute page. 43 Zulip stream index. 44 Zulip short intervals topic. 45 Zulip odd Goldbach
topic. 46 Zulip outstanding tasks v2 (404). 47 PNT+ issue 913. 48 issue 911. 49 issue 902.
50 IEANTN issues search Dusart. 51 IEANTN issues search 89693/prime gap. 52 PNT+ open task-label issues.
53 Lcm v2 Conclusions. 54 Lcm v1 yaml. 55 Lcm v1 Conclusions. 56 Dusart.lean (5.2-5.16 statements).
57 PNT+ issue 1761. 58 issue 1692. 59 issue 1814. 60 repo search zeta zeros lean interval. 61 repo search
prime gap lean4 (empty). 62 IEANTN issue 268. 63 PrimeCert repo. 64 Mathlib NormNum.Prime docs.
65 repo search LeanCert. 66 LeanCertEnclosures.lean. 67 TMEEMT.lean. 68 RosserSchoenfeldPrime.lean.
69 Chebyshev.lean. 70 ar5iv 1002.0442. 71 issues search native_decide. 72 PNT+ README. 73 PR 1804.
74 IEANTN issue 257. 75 IEANTN issue 258. 76 (repeat check of Dusart.lean via query 1/27 counted once).
Own computations (not queries): sieve to 400000 and the gap check, chain of 2745 (PowerShell).
Totals: WebSearch calls 2; endpoint queries 75 (query 76 above is not an extra fetch).
