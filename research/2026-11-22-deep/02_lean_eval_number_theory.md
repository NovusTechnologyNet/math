# lean-eval number-theory and transcendence problems: statements, sources, prerequisites, status

Date: 2026-11-22. WebSearch calls used: **13** of 29. WebFetch calls were not limited.

Evidence tags: **[READ]** = I opened the page/file/API record. Note that WebFetch returns a model-made digest of a page, not the verbatim page, so [READ] means "read through the fetch tool"; the two PDFs (Dimitrov, Lagarias) I converted to text locally with pdftotext, which is the closest to verbatim. **[SNIPPET]** = seen only in search-result text. **[BACKGROUND]** = my own mathematical knowledge, not checked on a page. "Not found" is followed by what was tried. Quotes are under 15 words.

---

## Summary

1. **Update to the coordinator's lead: confirmed.** The site's JSON feed (`https://lean-lang.org/eval/site-data/v2/...`) lists Baker-Wüstholz with **4 accepted solutions**, the first by Axiom Prover (Axiom Math) on 2026-09-21. All four are private or withheld; **no source is public** under any license [READ].
2. **The lean-eval Baker-Wüstholz statement is NOT the qualitative theorem with algebraic coefficients.** It has rational-integer coefficients and an explicit lower bound with constant C(n,d). It does not give the Q-bar-linear independence your library assumes (details in section 1).
3. The coordinator's "accepted 2026-11-20 to 11-22" for Linnik, Schmidt, Vinogradov, Chen is true but misleading: those are the **latest** accepted solutions (Infinigence AI, Forge), not first solves. Schmidt had 8 acceptances, first on 2026-08-22 [READ].
4. **Dimitrov, Lagarias, Schmidt, CDT, Baker-Wüstholz are all solved** (accepted) by AI systems: 12, 7, 8, 4, 4 accepted solutions. "Being first" is gone for all of them.
5. **Public sources exist for two of the three problems you flagged:** Dimitrov (`mlgraham/lean-eval-dimitrov-submission`, 86 modules, 13,167 lines, Apache-2.0) and Lagarias (`kimihiro64/Robin1984`, Apache-2.0). For Baker-Wüstholz none.
6. Dimitrov's proof is short on paper (27-page arXiv paper; main proof on pp. 15-16) and your recollection is right: Dubinin plus a Pólya-Carlson-Bertrandias rationality theorem, plus a mod-4 Euler-Frobenius congruence. The public Lean proof replaces Dubinin by Konyagin-Lev and uses Faber polynomials.
7. Lagarias's own paper is 9 pages; everything hard is Robin 1984 (J. Math. Pures Appl. 63, pp. 187-213), which the public repo formalizes on top of PrimeNumberTheoremAnd.
8. Mathlib has house, Siegel's lemma over number fields, Mahler measure with Kronecker and Northcott, Legendre's continued-fraction theorem. It has **no** transfinite diameter, no Dubinin, no Bertrandias, no Baker, no Roth (Roth lives in `rwst/Subspace-Theorems`).
9. Zero accepted solutions (among those I checked): weak Goldbach, Ramanujan-Petersson (tau), Sylvester's cubes, Erdős supersingular primes, Dirichlet Weyl bound, Faltings, Fermat's Last Theorem.
10. Shortlist: (1) Dimitrov, (2) Lagarias, (3) cyclotomic-integer house at most 2. Baker-Wüstholz is the one you need but is not feasible solo; watch for a public release.

---

## 0. How lean-eval publishes results (needed to read the numbers below)

- Statements: `https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/<File>.lean`; problem manifests in `manifests/problems/*.toml` [READ].
- Per-problem JSON with accepted solutions: `https://lean-lang.org/eval/site-data/v2/problems/<id>.json`; index at `.../v2/index.json` (snapshot generated 2026-11-22: 311 problems, 1,968 solutions in the main group; open-problems group has 0 problems) [READ].
- Each accepted row carries a publication status (private / planned / published / withheld) and a release status. I saw `public_solution.available = false` for essentially every row, including rows whose submitter declared a public repo; so "public" below means "the submitter's own repo is visible on GitHub", which I checked only where stated [READ].
- Release rule: the lean-eval README (read in the earlier report) says accepted sources are published under Apache 2.0 two UTC months after acceptance. In the feeds, rows that should be past that date (for example Baker-Wüstholz row 2, NEAR AI, "planned 2026-11-12") still show "unavailable" [READ]. So that rule has not yet produced any public Baker-Wüstholz source.
- Recent-solutions page `https://lean-lang.org/eval/recent/` shows only "Loading" to a fetch; the JSON feed `v2/recent-solutions.json` is the usable source (5 MB; I read the first 100 kB).

---

## 1. Baker-Wüstholz theorem on linear forms in logarithms (`bakerWustholz_linearForms_logs`)

**1. Lean statement.** File: https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/BakerWustholz.lean. Submitter Ralf Stephan; source Baker-Wüstholz, J. reine angew. Math. 442 (1993), 19-62; status active; no informal solution on the page [READ].

In words, the theorem takes:
- `n > 0`, a number field `K` (Mathlib `NumberField`), a ring embedding `φ : K →+* ℂ`;
- `α : Fin n → K`, all nonzero;
- **`b : Fin n → ℤ`: rational-integer coefficients**, with an independent natural number `B ≥ 2` and `|b i| ≤ B` for all i;
- the nonvanishing hypothesis that Λ = Σ (b i : ℂ) · Complex.log (φ (α i)) is nonzero (principal branch `Complex.log`).

Conclusion: `Real.log ‖Λ‖ ≥ -( C(n,d) · max(log B, 1/d) · ∏ modifiedHeight φ (α i) )`, with d = `Module.finrank ℚ K`. Definitions in the file: `C n d = 18 (n+1)! n^(n+1) (32 d)^(n+2) log(2nd)` and `modifiedHeight` = the max of (logHeight₁ α)/d, ‖Complex.log (φ α)‖/d, and 1/d, using Mathlib's `Height.logHeight₁`. The proof is `sorry` [READ].

**Answers to the coordinator's question (1).**
- Coefficients are **integers**, not algebraic numbers [READ].
- It is a **quantitative lower bound with the explicit constant**, not the qualitative theorem [READ].
- Does the qualitative theorem with algebraic coefficients follow from it? **No, not by any short formal argument.** [BACKGROUND, my judgment] The statement only says: if an integer combination is nonzero, it is not too small. Whether it is nonzero is a hypothesis (it is what Q-linear independence of the logarithms supplies). It says nothing about combinations with algebraic coefficients β_i, and "logs of algebraic numbers that are Q-linearly independent are Q-bar-linearly independent" is exactly a statement about such combinations. That needs Baker's theorem with algebraic coefficients (Baker 1966-67, or the algebraic-coefficient versions in the Baker-Wüstholz book), which is a different and stronger statement than this lean-eval theorem. I did not find a derivation on any page; treat this as unverified.
- Consequence for your library: even a full proof of the lean-eval problem would discharge only the integer-coefficient quantitative form, not your Baker hypothesis as currently phrased.

**2. Source proof.** Baker-Wüstholz 1993: 44 pages (pp. 19-62) [READ, via the DOI record in a search result: SNIPPET for the page count]. Machinery, per a search snippet quoting Wikipedia's "Analytic subgroup theorem": Wüstholz's multiplicity estimates on group varieties give the final form of the bound [SNIPPET]. The later monograph (Cambridge, 2007, *Logarithmic Forms and Diophantine Geometry*) gives the quantitative theory [SNIPPET]. Karatarakis-Wiedijk say a Baker formalization would reuse the Gelfond-Schneider strategy (auxiliary functions, extrapolation) with "significant complexity" [READ, earlier report, local PDF text]. I did not read the 1993 paper itself (not found openly; queries 8, 13).

**3. Existing infrastructure.**
- Mathlib: `Height.logHeight₁` and Northcott for log height (`Mathlib/NumberTheory/Height/*.lean`: Basic, EllipticCurve, MvPolynomial, Northcott, NumberField, Projectivization) [READ]; `NumberField.house` and Siegel's lemma over number fields (`Mathlib/NumberTheory/NumberField/House.lean`, `exists_ne_zero_int_vec_house_le`) [READ].
- Gelfond-Schneider: Karatarakis-Wiedijk, arXiv 2603.24823; Mathlib PR #42911 "the Gelfond-Schneider theorem", ~5,066 added lines, still **open**, last updated 2026-09-12 [READ, API]. Zulip thread: Commelin estimated about 50 PRs to upstream it [SNIPPET, search 9]. Fork `mkaratarakis/mathlib4`.
- Mathlib PRs titled "Baker": none (GitHub issue search, 0 results) [READ].
- Rational-case bound `mjtb49/Bounds-on-linear-forms-in-logarithms` (from the earlier report) [READ earlier].
- `rwst/Subspace-Theorems` has a `FaltingsWustholz1994` directory (Faltings-Wüstholz, "Diophantine approximations on projective spaces"), but its README never mentions logarithmic forms [READ]. Ralf Stephan, the Baker-Wüstholz submitter, owns that repo; the link, if any, is not documented.
- Another Stephan preprint (arXiv 2607.14774, 2026) treats Baker-Wüstholz only as an input; the abstract page does not say how [READ]; a search snippet said the Lean proofs instantiate C at (n,d) = (4,1) [SNIPPET].

**4. Announced work / status.** 4 accepted solutions, none retracted [READ]:

| Row | Solver | Submitter | Accepted | Publication | Release |
|---|---|---|---|---|---|
| 1 | Axiom Prover (Axiom Math) | vilin97 | 2026-09-21 (first) | not declared | withheld |
| 2 | NEAR AI w/ DeepSeek V4 | skidanovalex | 2026-09-30 | planned for 2026-11-12 | unavailable |
| 3 | Humanifa + GPT 5.6 sol | hongzhoulin89 | 2026-10-02 | private | unavailable |
| 4 | GenProof (declared "max gp (GPT-6)") | ma4ypic4y | 2026-10-13 | private | unavailable |

Row 3's repo URL (`hongzhoulin89/lean-eval-baker-wustholz-linear-forms-logs`) returns 404. The JSON feed has no license field; the only license text is a note in row 4 that the benchmark itself is Apache 2.0 [READ]. The submission issue for row 3 says the proof was AI-developed and passed a 4,621-job build with two kernels, but states no hypotheses or axioms [READ]. I found no announcement beyond that. No Zulip thread on Baker (queries 5, 9, 13).

**Coordinator question (2): is any accepted source public?** No. **Question (3)/(4)** are answered in the table in section 10.

**5. Difficulty.** Missing theories (my count): (a) Gelfond-Schneider layer not yet in Mathlib; (b) multi-variable auxiliary functions and extrapolation; (c) multiplicity estimates on commutative group varieties (Wüstholz), or Baker's older route with explicit but weaker constants; (d) careful constant management giving exactly this C(n,d); (e) algebraic-coefficient version for your hypothesis. Roughly 4 to 5 missing theories, each the size of a full project. Natural chunks: GS in Mathlib; Baker for n = 2; general n; explicit constants. **Not feasible solo**; four labs have done it privately in about two weeks each, which also means a public release may arrive.

---

## 2. Dimitrov's lower bound for the house (`dimitrov`)

**1. Lean statement.** https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/SchinzelZassenhaus.lean (file name differs from problem id; the manifest is `manifests/problems/dimitrov.toml`, submitter Zou Jinping, source McKee-Smyth, *Around the Unit Circle*, ch. 4, Thm 4.1, and Dimitrov 2019) [READ].

```lean
theorem dimitrov {K : Type*} [Field K] [NumberField K] (α : K)
    (α_int : IsIntegral ℤ α) (α_ne_zero : α ≠ 0) (α_not_rootOfUnity : ¬ IsOfFinOrder α) :
    (2 : ℝ) ^ (1 / (4 * (Finset.univ.image fun σ : K →+* ℂ ↦ (σ α).arg).card) : ℝ) ≤ NumberField.house α
```

In words: a nonzero algebraic integer that is not a root of unity has house at least 2^(1/(4d')), where d' is the number of **distinct phases** among its conjugates (d' is at most the degree, so this is at least as strong as the degree form in Dimitrov's abstract, which has 4n). Uses `IsIntegral`, `IsOfFinOrder`, `NumberField.house`, `Complex.arg`, `Real.rpow` [READ].

**2. Source proof.**
- Dimitrov, arXiv:1912.12545, submitted 28 Dec 2019, 27 pages, 26 KB listing [READ]; Annals of Math. (an Annals page exists in a search result [SNIPPET]). McKee-Smyth chapter 4 (Springer, paywalled; not read; the page count is not found).
- Theorem 1 is proved on pp. 15-16 using only Lemma 2.1, Proposition 2.2, Lemma 2.3 and Corollary 5 [READ].
- **Your description is right, with additions.** The proof: (i) an Euler-Frobenius type congruence P4 ≡ P2 mod 4 (Arnold-Smyth; short proof by symmetric powers) giving integer coefficients for the power series f = sqrt(P2·P4) in Z[[1/X]]; (ii) Dubinin's theorem (Thm 3): the "hedgehog" of n radial segments has transfinite diameter at most max|a_i|^(n/4)... (cited from Dubinin 1985 and his 2014 book, section 4.4); (iii) Bertrandias's rationality theorem (Cor. 5: an integer power series analytic off a compact set of transfinite diameter below 1 is rational; this is the Carlson-Pólya-Bertrandias algebraization theorem); (iv) Lemma 2.3: P2·P4 a square forces a root of unity. Smyth's theorem (non-reciprocal case) is used for the reduction but the paper says the reduction is not necessary [READ].
- Dimitrov's paper notes Andre's rationality theorem as an alternative to Bertrandias, with worse constants [READ].

**3. Existing infrastructure.**
- Mathlib: `NumberField.house` with `one_le_house_of_isIntegral` (nonzero algebraic integer has house ≥ 1); no roots-of-unity or Kronecker in `House.lean` [READ].
- Mathlib Mahler measure file (`Mathlib/NumberTheory/MahlerMeasure.lean`): Northcott (`finite_mahlerMeasure_le`), measure 1 implies root of unity, cyclotomic divisor; no Lehmer or Dobrowolski [READ]. Merged PR "Kronecker's Theorem for the Mahler Measure" (#33336, 2025-12-27 to 2026-01-19, "[Merged by Bors]" in the title) [READ].
- Not in Mathlib (my searches): transfinite diameter, logarithmic capacity, Dubinin, Bertrandias, Pólya-Carlson. GitHub PR title search for "transfinite diameter / capacity" found 0 results [READ]; web searches 10-11 found no Lean or Isabelle formalization [SNIPPET].
- **Public complete Lean proof:** `mlgraham/lean-eval-dimitrov-submission`: 86 modules, 13,167 lines, no `sorry`, axioms only propext/Classical.choice/Quot.sound, Lean v4.33.0, Mathlib pinned at a commit, Apache-2.0 [READ]. Route: Konyagin-Lev (following a proof by "fedja") **replaces Dubinin**; then exterior map and omitted set, arm matching, containment, Faber polynomials and a Pólya criterion, descent. Stage names are from module names; the README does not describe how Faber/Pólya are used [READ]. The site lists the first solve as "github.com/mlgraham (Claude Fable 5)" [READ].

**4. Status.** 12 accepted solutions; first 2026-08-28 (mlgraham); others include Axiom Prover (08-29), Tau (09-05), NEAR AI (09-12), Forge (09-15), Bogatyy (09-19, adapts mlgraham, Apache-2.0 retained), Midas (09-22), Humanifa (09-23), GenProof (10-03, reuses mlgraham's repo), DeepScientist Math + GPT-6.1 (10-16, public repo `LikC1606/deepscientist-math-proofs`), Infinigence AI (11-22) [READ]. Rows 1 and 3 are the same source tree. No Zulip thread found (query 3).

**5. Difficulty for a solo person plus assistant.** If the goal is "own a verified, understood Dimitrov", the work is porting and auditing 13k lines, not discovering a proof. Missing theories if rebuilt from scratch: (a) hedgehog capacity bound (Konyagin-Lev or Dubinin); (b) rational-function approximation / Faber-Pólya-Bertrandias; (c) the mod-4 congruence and integrality of sqrt series (easy, elementary); (d) assembly. About 2 hard theories plus easy algebra. Chunks: (c) first, then Pólya rationality, then Konyagin-Lev, then glue. **Most approachable on this list**, because a public proof and a 27-page source exist and the algebraic side overlaps with your cyclotomic and order-of-2 machinery.

---

## 3. Calegari-Dimitrov-Tang linear independence (`cdt_linearIndependent`)

**1. Lean statement.** https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/CalegariDimitrovTangLinearIndependent.lean; submitter Junyan Xu [READ]. In words: with χ the character mod 3 given by `![0, 1, -1]`, the family `![1, riemannZeta 2, ZMod.LFunction χ 2]` is linearly independent over ℚ; and for integers m, n not in {-1, 0} with 10^6 |m-n| < |n|, log(1+1/m)·log(1+1/n) is irrational, and (if m ≠ n) 1, log(1+1/m), log(1+1/n), product are Q-linearly independent. Uses `LinearIndependent`, `riemannZeta`, `ZMod.LFunction`, `Irrational`, `Real.log`. Proof `sorry` [READ].

**2. Source.** Calegari, Dimitrov, Tang, arXiv:2408.15403 (27 Aug 2024; v2 16 Sep 2024), **218 pages** [READ]. Machinery: arithmetic holonomy bounds applied to a Zagier construction; per the lean-eval note, Theorems A and C each have two routes: §6 (multivariable, measure concentration) or §7 (single variable, Arakelov theory and Bost's evaluation-height inequality) [READ]. Follow-up arXiv 2510.04156 (2025) [SNIPPET].

**3. Infrastructure.** No Lean or other formalization found (queries 7, 12). Arakelov theory and Bost's inequality are absent from Mathlib [BACKGROUND, not searched]. `rwst/Subspace-Theorems` has an `Arakelov.lean` in `ArithmeticHeights` [READ, file list only]; relevance unchecked.

**4. Status.** 4 accepted: NEAR AI (2026-09-30, first), GenProof (10-09), Humanifa (10-13), Axiom Prover (10-13); no public source; NEAR AI and Humanifa planned releases for 2026-11-12 and 11-20, not materialized [READ].

**5. Difficulty.** Missing: Arakelov heights with evaluation estimates (or measure-concentration route), holonomy bounds, Zagier's Apéry-type construction, plus the arithmetic of the linear forms. 4+ large theories and 218 pages. **Hopeless solo.**

---

## 4. Schmidt's subspace theorem (`schmidt_subspace`)

**1. Lean statement.** https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/SchmidtSubspace.lean; submitter Junyan Xu; source Schmidt, LNM 785, chapters V-VII [READ]. In words: for an index type σ with at least 2 elements, an algebraic coefficient matrix `L : σ → σ → ℂ` (`IsAlgebraic ℚ`) that is linearly independent over ℂ, and ε > 0, there is a finite set of nonzero integer linear forms such that every integer point x with |∏ᵢ Σⱼ Lᵢⱼ xⱼ| below ‖x‖^(-ε) (as stated in the file; I read only a digest) satisfies one of them. Mathlib items: `Fintype`, `LinearIndependent`, `IsAlgebraic`, norms, `Finset.prod/sum` [READ].

**2. Source proof.** Schmidt 1980, chapters V-VII (book; length not checked). Machinery: geometry of numbers (Minkowski second theorem, successive minima), Roth-type auxiliary polynomial, Faltings product theorem or Schmidt's parametric approach [BACKGROUND].

**3. Infrastructure (important).** `rwst/Subspace-Theorems` (Apache-2.0, 52 commits, created 2026-09-15, last push 2026-11-06, Ralf Stephan): libraries `ArithmeticHeights` (62 files: Northcott, Kronecker, Siegel, Bombieri-Vaaler, successive minima, Minkowski second, MahlerMeasure, SUnit theorem, etc.) and `DiophantineApproximation` (Roth over number fields, Ridout, geometry of numbers, Subspace Theorem, unit equations); 203 library files, 5,048 declarations audited [READ]. Its `formalization.yaml` claims 0 `sorry` in the libraries and 26 headline statements checked by `comparator`, with the caveat that no human review of statement fidelity has occurred and Evertse's quantitative interval theorem is assumed in general (proved only for two variables) [READ, digest]. The README says files are meant to move to the Tau Ceti library [READ]. The same repo is vendored by a GenProof submission [READ].

**4. Status.** 8 accepted: first 2026-08-22 (Humanize RLCR GPT-5.6-sol, ZhengyangZhang06); then Humanifa, Axiom Prover (08-29), NEAR AI (09-15), Midas (09-29), GenProof (10-06), Forge (11-18), Infinigence AI (11-22); all private or withheld, no public source [READ]. Stephan's arXiv papers 2610.30937 and 2611.16536 claim machine-verified quantitative subspace results in Lean 4 [READ, abstracts].

**5. Difficulty.** Missing theories if starting from Mathlib: heights of subspaces, Siegel and Bombieri-Vaaler, geometry of numbers, Roth, subspace: 5 or more. But `rwst/Subspace-Theorems` supplies them publicly. A solo person can read and use it, not rebuild it. Not a good new target, but a strong *source of infrastructure* (Northcott, Kronecker, Siegel over number fields) that overlaps with your library's needs.

---

## 5. Lagarias criterion is equivalent to RH (`riemann_hypothesis_iff_lagarias_elementary_criterion`)

**1. Lean statement.** https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/Lagarias.lean; submitter Kim Morrison; source arXiv math/0008177 [READ].

```lean
theorem riemann_hypothesis_iff_lagarias_elementary_criterion : RiemannHypothesis ↔ LagariasElementaryCriterion
```
`LagariasElementaryCriterion`: for every n > 0, `σ 1 n ≤ harmonic n + Real.exp (harmonic n) * Real.log (harmonic n)` (cast to ℝ). Uses Mathlib's `RiemannHypothesis`, `harmonic`, `ArithmeticFunction.sigma` [READ]. Note: the file's criterion says "at most" for all n > 0 (equality at n = 1), matching Lagarias.

**2. Source proof.** Lagarias, *An elementary problem equivalent to the Riemann hypothesis*, arXiv math/0008177 (22 Aug 2000, v2 6 May 2001), 9 pages; Amer. Math. Monthly 109 (2002) 534-543 [READ]. I read the text locally. Structure [READ]:
- Lemma 3.1 (exp(H_n) log H_n ≤ e^γ n log log n, for n ≥ 3) and Lemma 3.2 (H_n + exp(H_n) log H_n ≤ e^γ n log log n + 7n/log n, for n ≥ 20): elementary calculus from H_n = log n + γ + small error. Short.
- RH implies inequality for n ≥ 5041: Robin Proposition 3.1 (RH implies σ(n) < e^γ n log log n for n ≥ 5041) plus Lemma 3.1. For 1 ≤ n ≤ 5040 a computer check, equality only at n = 1.
- Inequality for all n implies RH: contrapositive via Robin Proposition 3.2 (if RH fails there are θ in (0,1/2), C > 0 and infinitely many n with σ(n) ≥ e^γ n log log n + (log n)^(-θ) C n / log log n... as printed); this contradicts Lemma 3.2. Proposition 3.2 is credited to Robin, §4 Prop 1, using Nicolas's version of a Landau argument.
- **What must be formalized, in order:** (i) Lemmas 3.1, 3.2 and the harmonic-number asymptotics (easy); (ii) the finite check n ≤ 5040 (`decide +kernel` territory, your strength); (iii) **Robin's Theorem 1** (the unconditional-on-nothing hard step: RH implies σ(n) < e^γ n log log n for n ≥ 5041): this needs explicit sharp bounds on Chebyshev's θ(x) under RH, the structure of colossally abundant numbers (Alaoglu-Erdős), Mertens-type products, and a numerical range [BACKGROUND]; (iv) **Robin's Proposition 3.2**: if RH is false then θ(x) − x is not O(x^b) for some b > 1/2, a Landau-type oscillation theorem for Dirichlet integrals with a zero off the line, then construction of colossally abundant numbers realizing it [BACKGROUND]. Robin 1984 is 27 pages (187-213) [READ, from Lagarias's reference list].

**3. Infrastructure.**
- Mathlib: `RiemannHypothesis`, `harmonic`, `ArithmeticFunction.sigma`, `Chebyshev.lean`, `PrimeCounting`, `Harmonic/`, `ZetaValues`, `LSeries/`, Dirichlet theorem; Mertens PRs are **open** (#46026 first theorem, 2026-11-14; #41394 "the Mertens theorems", 2026-07-06; #44061/#44062) [READ]. No explicit-formula bounds, no PNT with error term in the pieces I checked (not exhaustively).
- Mathlib PR #37585 "formal statements of Robin's and Lagarias' inequalities equivalent to RH": statement-only with `sorry`, by an external contributor, **closed unmerged** on 2026-11-11 [READ].
- **Public complete proof:** `kimihiro64/Robin1984` (Apache-2.0, optional CC-BY-4.0 paper): proves both directions of Robin's criterion and the colossally-abundant version and Lagarias's criterion; the converse uses a reconstruction of the Nicolas-Landau oscillation argument; finite ranges handled by kernel-checked certificates up to log n = 74500; depends on `PrimeNumberTheoremAnd` from a temporary fork and on `leancert`; Lean v4.33.1; axioms only the standard three; built with OpenAI Codex agents; "no independent expert mathematical review" claimed; line count not stated [READ]. The first accepted lean-eval solution is from this repo (see below).
- Unrelated: a June 2026 paper (arXiv 2606.15096) verifies finite Lagarias inequalities for n ≤ 1000 in Coq [SNIPPET]; the Zulip "Lean Formalization of the Riemann Hypothesis" thread was a spurious RH claim [SNIPPET].

**4. Status.** 7 accepted: Codex 5.6 Sol + HITL (kimihiro64) on 2026-09-13 (first; published, `Robin1984`), Axiom Prover (09-25), NEAR AI (09-26), Humanifa (10-01), GenProof (10-04), Forge (11-18), Infinigence AI (11-22); only the first has a public repo [READ]. Note: Quanta item (from the earlier report) about a claimed RH proof by Alpöge is separate and not verified.

**5. Difficulty.** Missing theories (my count): (a) PNT-strength explicit estimates on θ and ψ with an RH-conditional version (partly in PrimeNumberTheoremAnd, not Mathlib); (b) Landau oscillation theorem for Mellin or Dirichlet integrals; (c) colossally abundant numbers and Robin's inequalities; (d) the elementary harmonic-number calculus. About 3 real theories. Chunks: elementary lemmas and finite check; Robin Theorem 1; Robin Proposition 3.2; assembly. **Moderate-to-hard for a solo person, but a public proof and a 9-page wrapper exist; much of the effort would be pulling in PrimeNumberTheoremAnd.** Relevance to pi: none directly.

---

## 6. Dimitrov-adjacent: cyclotomic integers with house at most 2 (`cyclotomic_integer_house_le_two`, `cyclotomic_integer_house_between_two_and_76_33`)

Not on your list but unusually relevant to your cyclotomic-integer machinery.

**1. Statement.** https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/SmallHouse.lean [READ]. For a cyclotomic extension K of ℚ of level n and an algebraic integer β in the maximal real subfield: if house β ≤ 2 then house β = 2 or house β = 2 cos(π/m) for some m ≥ 1; the second theorem classifies the case 2 < house β < 76/33 as one of five listed values. Source Calegari-Morrison-Snyder, arXiv:1004.0665 (April 2010), 47 pages with an appendix by Ostrik, Theorem 1.0.5 [READ]. Mathlib: `IsCyclotomicExtension`, `maximalRealSubfield`, `house` [READ].

**2-3. Proof and infrastructure.** I did not read the proof. The abstract says it is number theory on cyclotomic integers (Kronecker, Cassels-type) applied to fusion categories [READ]; the appendix and subfactor parts are not needed for the statement. Mathlib has house, cyclotomic fields, Kronecker (Mahler measure) [READ].

**4. Status.** `le_two`: 12 accepted, first Aleph Prover 2026-05-08; public repo `mlgraham/lean-eval-cyclotomic-house-submission` (declared published; commit 960b540; the replay flag still says unavailable) [READ]. `between_two_and_76_33`: 3 accepted (first 2026-08-03); the one listed repo link is "permanently unavailable" [READ].

**5. Difficulty.** Unread; guess [BACKGROUND]: 2 or 3 missing theories (Cassels/Kronecker for conjugates on the unit circle, Galois-theoretic induction on cyclotomic level, a classification step). Unknown without reading the proof or the public repo; treat the rank below as provisional.

---

## 7. "On approximation to a real number by algebraic numbers of bounded degree" (`annals_on_approximation_of_reals`)

**1. Statement.** https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/OnApproximationOfReals.lean; by Hristova and Buzzard [READ]. For n ≥ 2 and ξ transcendental real, ω⋆_n(ξ) ≥ n / (2 − log 2) (as `(ω⋆ n ξ : EReal) ≥ a * n` with a = 1/(2 − log 2)). File-local definitions: `classicalExponent`, `ω_stars`, `AlgebraicDegLE`, `height` (from `minpoly`, `Polynomial.coeff`, `Rat.num/den`) [READ].

**2. Source.** A. Poëls, Annals of Math 201(1), 2025; arXiv 2405.08341, 21 pages; method from parametric geometry of numbers [READ, arXiv API digest; "0.765" constant given in the abstract].

**3. Infrastructure.** Mathlib: `Mathlib/NumberTheory/DiophantineApproximation/{Basic,ContinuedFractions,Hurwitz}.lean`, Dirichlet approximation, Liouville; parametric geometry of numbers is absent [BACKGROUND].

**4. Status.** 9 accepted, first 2026-08-19 (Humanifa); latest Infinigence AI 2026-11-22; no public source [READ].

**5. Difficulty.** Short paper (21 pages) but needs parametric geometry of numbers (Schmidt-Summerer, Roy). 2 to 3 missing theories. Possible but a real research-reading effort; unranked.

---

## 8. "Algebraic integers with conjugates in a prescribed distribution" (`annals_algebraic_integers`)

**1. Statement.** https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/AlgebraicIntegers.lean; credited Justus Springer (2026). Statement: `lambda_SSS < 1.89831`, where `lambda_SSS` is a supremum over totally positive algebraic integers' trace-to-degree ratios (file-local `lambda_SSS`, `trace`, `degree`, `IsTotallyPositive`; Mathlib `minpoly`, `aroots`, `IsIntegral`) [READ].

**2. Source.** A. Smith, Annals 200(1), 2024; arXiv 2111.12660, 47 pages [READ]. Compact-set potential theory (Fekete-Szegő style) and construction of integers with prescribed conjugate distributions [BACKGROUND].

**3-4.** No Lean formalization found. 10 accepted, first 2026-08-20; one public repo `LikC1606/deepscientist-math-proofs` (declared published 2026-10-16, ref 43cffcc; statement says no license in the record) [READ]. The top-level listing of that repo did not show an algebraic-integers directory (`in-progress/` and three other directories are there) [READ].

**5.** Needs capacity theory, the same missing area as Dimitrov, but more of it. Unranked.

---

## 9. Other items

| Problem (id) | Statement file | Source, length | What it needs / what exists | Accepted | Public source |
|---|---|---|---|---|---|
| Enumerating number fields (`annals_enumerating_number_fields`) | `EnumeratingNumberFields.lean` [READ] | Couveignes, Annals 192(2) 2020, arXiv 1907.13617 (length not given) | Statement uses schemes: `Spec`, irreducible components, `rootDiscr`; heavy algebraic geometry; no infrastructure found | 6 (first 2026-08-22, latest Forge 2026-10-26) | none |
| Weak Goldbach (`weak_goldbach`) | `WeakGoldbach.lean`: `∀ odd n > 5, ∃ p q r prime, n = p+q+r` [READ] | Helfgott, about 300 pages [BACKGROUND] | circle method, large sieve, numerical verification | **0** | n/a. Separately, a Quanta item (earlier report) says a Helfgott formalization exists outside lean-eval [snippet, earlier] |
| Duffin-Schaeffer (`duffin_schaeffer`, `annals_duffin_schaeffer_conjecture`) | `DuffinSchaefferConjecture.lean`, 4 theorems (Hristova-Buzzard) [READ] | Koukoulopoulos-Maynard, Annals 192(1) 2020 | measure theory plus a long combinatorial argument | `duffin_schaeffer` 9 (first 2026-08-16); the Annals version also solved (Infinigence 2026-11-22 02:02 in the feed) | none |
| Linnik (`linnik`) | not opened | Linnik's L = 5.5 | zero-density, large sieve | 5 (first 2026-09-25 Axiom) | none |
| Vinogradov mean value (`vinogradov_mean_value`) | not opened | Bourgain-Demeter-Guth (decoupling) | harmonic analysis | 8 (first 2026-08-16) | none |
| Chen (`chen_theorem`) | not opened | Chen 1973 | sieve theory | 8 (first 2026-08-31, Cond-t) | **two public repos**: `Cond-t/thema-chen-theorem-lean-eval`, `lixiang90/chen_theorem` (submitter repos; record says `public_solution.available` false) |
| Green-Tao (`green_tao`) | not opened | Green-Tao 2008 | ergodic or Gowers norms, transference | 9 (first 2026-08-01) | none |
| Friedlander-Iwaniec (`friedlander_iwaniec`) | not opened | X^2+Y^4 primes | sieve with bilinear forms | 4 (first 2026-09-21) | none |
| 290 theorem (`two_ninety_theorem`) | `TwoNinetyTheorem.lean` (Numina Team) [READ] | Bhargava-Hanke | quadratic form computations | 1 (2026-11-14, Codex+HITL, private) | none |
| Ramanujan-Petersson / tau (`ramanujan_petersson`) | not opened | Deligne | Weil conjectures | **0** | n/a |
| Flat Littlewood polynomials (`annals_flat_littlewood_poly`) | not opened | Balister-Bollobás-Morris-Sahasrabudhe-Tiba | probabilistic construction | 7 (first 2026-08-19) | none |
| Erdős, supersingular primes, short character sums (`annals_erdos_supersingular_primes`) | not opened | Annals paper | character sums | **0** | n/a |
| Smallness of exceptional set to Littlewood (`einsiedler_katok_lindenstrauss`) | not opened | Einsiedler-Katok-Lindenstrauss | measure rigidity | 4 (first 2026-09-28 NEAR AI) | none |
| Bounded gaps (`zhang_bounded_prime_gaps`) | `BoundedPrimeGaps.lean` (not opened) | Zhang / Maynard | sieve | 5 (first 2026-08-29 Axiom) | one repo declared: `the-omega-institute/trureturing-lean-eval` |
| Thue-Siegel-Roth (`thue_siegel_roth`) | `ThueSiegelRoth.lean`: irrational algebraic x is `IsDiophantine` (irrationality measure ≤ 2) [READ] | Roth 1955 | Roth is in `rwst/Subspace-Theorems` [READ]; status "archived" in the manifest [READ] | 5 (first 2026-06-22, Aristotle) | none |
| Pell solutions are convergents (`pell_solution_convergent`) | `PellConvergent.lean`: x²−dy²=1 implies x/y is a convergent of √d [READ] | Lagrange | Mathlib `Real.exists_convs_eq_rat` (Legendre, \|ξ−q\| < 1/(2·den²)) plus an easy bound [READ] | 13 (first 2026-06-01); five declared public repos incl. `test1-deepthought/lean-eval-solutions`, `savarin/lean-eval-speedrun`, `mlgraham/lean-eval-pell-submission` | several repos listed (some unavailable) |
| Sylvester's cubes (`sylvester`) | `Sylvester.lean`: prime p ≡ 4,7,8 mod 9 is a sum of two rational cubes (and p² too) [READ] | Dasgupta-Voight [BACKGROUND] | Heegner points, Kolyvagin | **0** | n/a |
| Faltings (`faltings`), FLT (`fermat_last_theorem`), Dirichlet Weyl bound (`annals_dirichlet_weyl_bound`) | not opened | | | **0** each (empty `solutions`) | n/a |

Checked but not fetched: Mazur torsion, Mihailescu, Brun, Lindemann, Lindemann-Weierstrass, Chebyshev sign change (several archived in the manifests [READ, earlier]). **Chudnovsky 1/pi** is also solved publicly: `ldct/lean-eval-chudnovsky` (about 20k lines, 30 modules, produced by Claude models with human direction, axioms standard) [READ; accepted-count not fetched]. That is directly pi-related and public.

---

## 10. Coordinator questions (3) and (4), consolidated

**(3) Accepted solutions and public-source status per problem on your list** (snapshot 2026-11-22, from `v2/problems/<id>.json`) [READ]:

| Problem | Accepted | First accepted | Public source |
|---|---|---|---|
| Baker-Wüstholz | 4 | 2026-09-21 Axiom Prover | none |
| Dimitrov | 12 | 2026-08-28 | yes: mlgraham repo (Apache-2.0 per its README), also DeepScientist repo |
| CDT | 4 | 2026-09-30 | none |
| Schmidt subspace | 8 | 2026-08-22 | none (the donor library `rwst/Subspace-Theorems` is public, Apache-2.0) |
| Lagarias | 7 | 2026-09-13 | yes: kimihiro64/Robin1984 (Apache-2.0) |
| Poëls approximation | 9 | 2026-08-19 | none |
| Smith algebraic integers | 10 | 2026-08-20 | one repo (LikC1606), license not stated |
| Enumerating number fields | 6 | 2026-08-22 | none |
| Duffin-Schaeffer | 9 | 2026-08-16 | none |
| Weak Goldbach | 0 | none | n/a |
| Chen | 8 | 2026-08-31 | two submitter repos |
| Linnik | 5 | 2026-09-25 | none |
| Vinogradov mean value | 8 | 2026-08-16 | none |
| Green-Tao | 9 | 2026-08-01 | none |
| Friedlander-Iwaniec | 4 | 2026-09-21 | none |
| 290 theorem | 1 | 2026-11-14 | none |
| Ramanujan tau | 0 | none | n/a |
| Flat Littlewood | 7 | 2026-08-19 | none |
| Erdős supersingular | 0 | none | n/a |

**(4) Zero accepted (among those I fetched):** weak Goldbach, Ramanujan-Petersson (tau), Erdős supersingular primes, Sylvester's cubes, Faltings, Fermat's Last Theorem, Annals Dirichlet Weyl bound. Not checked: Mazur torsion, Mihailescu, Brun, Lindemann items, Neukirchuh-Uchida, Mihailescu, the Shafarevich items, others in the 311-problem list. A full count needs the 1 MB group JSON and the per-problem JSONs; I read only the first 100 kB of the group list, which does not carry counts.

**License question (2):** no row I read states a license for its solution. Where licenses appear they are submitter-declared Apache-2.0 (README of `mlgraham/lean-eval-dimitrov-submission`; `kimihiro64/Robin1984`; `rwst/Subspace-Theorems`) or a note that the benchmark is Apache 2.0.

---

## Ranked shortlist (most approachable first, for a solo person plus an AI assistant)

1. **Dimitrov's house bound.** 27-page source, main proof two pages given three lemmas; a complete public Lean proof exists (13,167 lines, Apache-2.0), so you can read it, extract the Pólya/Faber stage, and rebuild or port it in chunks. It uses Mathlib's house and your cyclotomic and order machinery; the genuinely missing parts are a capacity/hedgehog bound and a Pólya-Bertrandias rationality criterion. Risk: the public proof is AI-written and unreviewed; the McKee-Smyth chapter (the exact d'-version) was not read.
2. **Lagarias criterion.** 9-page wrapper, a public Lean proof (`Robin1984`), elementary finite check suited to `decide +kernel`. The difficulty is Robin 1984, which needs RH-conditional explicit prime estimates and a Landau-type oscillation theorem, so you would depend on `PrimeNumberTheoremAnd` (a fork). Fits only loosely with pi.
3. **Cyclotomic-integer house at most 2 (Calegari-Morrison-Snyder Thm 1.0.5).** Directly in your Gaussian and cyclotomic integer territory; 12 accepted solutions and a public repo to compare; 47-page source of which only the number-theory part is needed. Provisional: I did not read the proof, so the difficulty is a guess.

Warm-up outside the list: Pell solutions are convergents; Mathlib already has Legendre's theorem, so it is a short exercise (many public solutions).

## Hopeless at this scale

- **Baker-Wüstholz** (and Baker with algebraic coefficients): no public source, 44-page paper depending on multiplicity estimates on group varieties; even the Gelfond-Schneider layer it would sit on is a 5,000-line open Mathlib PR. Four labs have private solutions; watch the leaderboard for a release and for rwst/Karatarakis.
- **Calegari-Dimitrov-Tang**: 218 pages, Arakelov theory.
- **Duffin-Schaeffer, Linnik, Vinogradov mean value, Chen, Green-Tao, Friedlander-Iwaniec, weak Goldbach, bounded gaps, 290 theorem, Ramanujan tau (Deligne), Faltings, FLT, Sylvester, Erdős supersingular, flat Littlewood, Littlewood exceptional set.**
- **Enumerating number fields** (scheme-theoretic statement) and **Smith's algebraic integers** (capacity and construction; also 47 pages with capacity theory that Mathlib lacks): only with a lot of new infrastructure.
- **Schmidt subspace theorem** from scratch: use the public `rwst/Subspace-Theorems` instead.

## Queries used (WebSearch, 13 total)

1. Dimitrov Schinzel-Zassenhaus conjecture proof house algebraic integer 2^{1/4d} Rhin Wu arXiv
2. Lean 4 formalization Robin's inequality Riemann hypothesis sum of divisors Lagarias
3. Lean Zulip Schinzel-Zassenhaus Dimitrov formalization house algebraic integer
4. Schmidt subspace theorem formalization Lean Mathlib
5. Baker-Wüstholz linear forms in logarithms Lean formalization project
6. Tau Ceti Lean library number theory formalization github
7. Calegari Dimitrov Tang linear independence 1, zeta(2), L(2,chi_-3) arithmetic holonomy Lean formalization
8. Baker Wüstholz "Logarithmic forms and group varieties" Crelle 442 1993 pages 19-62
9. leanprover zulip Baker's theorem linear forms in logarithms Mathlib Gelfond-Schneider next step
10. Lean 4 Mathlib transfinite diameter logarithmic capacity compact set formalization Fekete
11. Pólya-Carlson theorem integer coefficients power series rational or natural boundary formalization Lean Isabelle
12. Humanifa GPT Lean lean-eval Lagarias criterion Riemann hypothesis Robin theorem formalized proof repository
13. "linear forms in logarithms" Baker theorem formally verified Lean 4 AI 2026 Wüstholz

Not found: any Zulip thread about Baker, Dimitrov or Lagarias (queries 3, 5, 9, 12, 13); any Lean or Isabelle formalization of transfinite diameter, Dubinin, or Pólya-Carlson (10, 11); the McKee-Smyth chapter text (Springer paywall redirect); the Baker-Wüstholz 1993 paper text.

## Sources

- [lean-eval repository](https://github.com/leanprover/lean-eval) and files: [BakerWustholz.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/BakerWustholz.lean), [SchinzelZassenhaus.lean (dimitrov)](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/SchinzelZassenhaus.lean), [Lagarias.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/Lagarias.lean), [CalegariDimitrovTangLinearIndependent.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/CalegariDimitrovTangLinearIndependent.lean), [SchmidtSubspace.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/SchmidtSubspace.lean), [OnApproximationOfReals.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/OnApproximationOfReals.lean), [EnumeratingNumberFields.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/EnumeratingNumberFields.lean), [AlgebraicIntegers.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/AlgebraicIntegers.lean), [SmallHouse.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/SmallHouse.lean), [ThueSiegelRoth.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/ThueSiegelRoth.lean), [PellConvergent.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/PellConvergent.lean), [WeakGoldbach.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/WeakGoldbach.lean), [DuffinSchaefferConjecture.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/DuffinSchaefferConjecture.lean), [TwoNinetyTheorem.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/TwoNinetyTheorem.lean), [Sylvester.lean](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/Sylvester.lean)
- Site data: [index.json](https://lean-lang.org/eval/site-data/v2/index.json), [Baker-Wüstholz record](https://lean-lang.org/eval/site-data/v2/problems/bakerWustholz_linearForms_logs.json), [dimitrov](https://lean-lang.org/eval/site-data/v2/problems/dimitrov.json), [Lagarias](https://lean-lang.org/eval/site-data/v2/problems/riemann_hypothesis_iff_lagarias_elementary_criterion.json), [schmidt_subspace](https://lean-lang.org/eval/site-data/v2/problems/schmidt_subspace.json), [cdt](https://lean-lang.org/eval/site-data/v2/problems/cdt_linearIndependent.json), [recent-solutions.json](https://lean-lang.org/eval/site-data/v2/recent-solutions.json), [problem page](https://lean-lang.org/eval/problems/bakerWustholz_linearForms_logs/), [leaderboard repo README](https://raw.githubusercontent.com/leanprover/lean-eval-leaderboard/main/README.md)
- [lean-eval-submissions](https://github.com/leanprover/lean-eval-submissions) (issues #1915, #1926, #1954, #1992, #2019, #2084)
- Public proofs: [mlgraham/lean-eval-dimitrov-submission](https://github.com/mlgraham/lean-eval-dimitrov-submission), [kimihiro64/Robin1984](https://github.com/kimihiro64/Robin1984), [rwst/Subspace-Theorems](https://github.com/rwst/Subspace-Theorems), [ldct/lean-eval-chudnovsky](https://github.com/ldct/lean-eval-chudnovsky), [LikC1606/deepscientist-math-proofs](https://github.com/LikC1606/deepscientist-math-proofs)
- Papers: [Dimitrov, arXiv 1912.12545](https://arxiv.org/abs/1912.12545), [Lagarias, arXiv math/0008177](https://arxiv.org/abs/math/0008177), [Calegari-Dimitrov-Tang, arXiv 2408.15403](https://arxiv.org/abs/2408.15403), [Calegari-Morrison-Snyder, arXiv 1004.0665](https://arxiv.org/abs/1004.0665), [Poëls, arXiv 2405.08341](https://arxiv.org/abs/2405.08341), [Smith, arXiv 2111.12660](https://arxiv.org/abs/2111.12660), [Couveignes, arXiv 1907.13617](https://arxiv.org/abs/1907.13617), [Karatarakis-Wiedijk, arXiv 2603.24823](https://arxiv.org/abs/2603.24823), [Stephan arXiv 2610.30937](https://arxiv.org/abs/2610.30937), [Stephan arXiv 2611.16536](https://arxiv.org/abs/2611.16536), [Stephan arXiv 2607.14774](https://arxiv.org/abs/2607.14774), [Baker-Wüstholz DOI](https://www.degruyterbrill.com/document/doi/10.1515/crll.1993.442.19/html), [McKee-Smyth ch. 4](https://link.springer.com/chapter/10.1007/978-3-030-80031-4_4), [Wikipedia: analytic subgroup theorem](https://en.wikipedia.org/wiki/Analytic_subgroup_theorem)
- Mathlib: [House.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/NumberTheory/NumberField/House.lean), [MahlerMeasure.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/NumberTheory/MahlerMeasure.lean), [Height/Northcott.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/NumberTheory/Height/Northcott.lean), [ContinuedFractions.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean), [PR 42911 (Gelfond-Schneider)](https://github.com/leanprover-community/mathlib4/pull/42911), [PR 37585 (Robin/Lagarias statements)](https://github.com/leanprover-community/mathlib4/pull/37585), [PR 46026 (Mertens)](https://github.com/leanprover-community/mathlib4/pull/46026), [PR 33336 (Kronecker for Mahler measure)](https://github.com/leanprover-community/mathlib4/pull/33336)
- Context: [Zulip, Gelfond-Schneider](https://leanprover-community.github.io/archive/stream/116395-maths/topic/Gelfond-Schneider.20theorem.html), [Tau Ceti on Reservoir](https://reservoir.lean-lang.org/@TauCetiProject/TauCeti), [earlier report](../2026-11-22/larger_targets.md)
