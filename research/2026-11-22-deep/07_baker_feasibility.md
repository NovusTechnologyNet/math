# Baker's theorem: formalization feasibility (research report, 2026-11-22)

Evidence labels: [READ] = I opened the page, file or API data and saw it. [SNIPPET] = seen only in search-result text. "unverified" = not seen on a docs or source page. Quotes are under 15 words. GitHub data was read through the GitHub API (`gh`), which returns raw file contents.

WebSearch calls used: **12 of 29** (listed under "Queries used"). WebFetch and GitHub API reads were not counted.

## Summary

1. **Headline: a complete-looking Lean 4 proof of the qualitative Baker theorem (algebraic coefficients, nonhomogeneous) already exists on a public fork branch.** It is `baker` in `github.com/mkaratarakis/mathlib4`, by the author of the Gelfond-Schneider formalization. [READ]
2. Its tip commit is dated 2026-09-24; it holds 19 files under `Mathlib/NumberTheory/Transcendental/Baker/`, 7,383 lines in total, with zero occurrences of `sorry`, `axiom`, `native_decide` or `opaque` (grep of every file). [READ]
3. Its main theorem `Transcendental.baker` has exactly your hypothesis shape: `IsAlgebraic ℚ (exp (l i))`, `LinearIndependent ℚ l`, algebraic `β₀`, `β i`, relation `β₀ + ∑ β i * l i = 0`, conclusion all coefficients zero. [READ]
4. It follows Waldschmidt (2000) Chapter 4: Baker from the Schneider-Lang criterion for products of groups (Bertrand-Masser), not Baker's original route. [READ]
5. **Caveats:** I did not build it. It is unmerged and unannounced (no Mathlib PR, no Zulip thread found), built on Lean v4.35.0-rc2, and the file header of `Basic.lean` is stale (says later files "will be" written). A `baker-padic` branch (2026-09-25) also exists. [READ]
6. Gelfond-Schneider is still not in Mathlib: PR #42911 and its dependency PRs are open. Lindemann-Weierstrass PR #28013 is open. [READ]
7. The lean-eval problem "Baker-Wüstholz" has 4 accepted solutions (first 2026-09-22), all private. It is the integer-coefficient effective bound, so it would not give your algebraic-coefficient hypothesis anyway. [READ]
8. Verdict: do not re-prove Baker. Import and audit the fork branch (build against your Lean/Mathlib, `#print axioms`), then adapt your hypothesis to it.

## Status of formalizations

| Theorem | System | Who | Date | URL / evidence |
|---|---|---|---|---|
| Baker's theorem, qualitative, algebraic coefficients (`Transcendental.baker`, plus Theorems 2.2-2.4 of Baker 1975, pi, Gelfond-Schneider as corollaries) | Lean 4, fork branch `baker` (not in Mathlib) | M. Karatarakis (first commit says co-authored with an AI model) | setup commit 2026-07-06; port and proof 2026-09-23/24 | https://github.com/mkaratarakis/mathlib4/tree/baker [READ] |
| p-adic Baker (branch `baker-padic`, 10 files under `Baker/Padic/`) | Lean 4, fork branch | same | 2026-09-25 | https://github.com/mkaratarakis/mathlib4/tree/baker-padic [READ, file list only; completeness not checked] |
| Schneider-Lang criterion for C^d0 x (C*)^d1 (Cor. 4.2 of Waldschmidt), with Hermite-Lindemann and Gelfond-Schneider as special cases | Lean 4, same branch (`Baker/SchneiderLang.lean`, `CriterionMain.lean`) | same | 2026-09-23/24 | same [READ] |
| Gelfond-Schneider | Lean 4 | Karatarakis and Wiedijk | arXiv 2026-03-25; Zulip announcement 2025-11-23 | https://arxiv.org/abs/2603.24823 ; Mathlib PR #42911 open [READ] |
| Baker-Wüstholz (effective, integer coefficients) | Lean 4 (lean-eval) | 4 accepted solutions, all with private source: Axiom Prover 2026-09-22, NEAR AI/DeepSeek V4 2026-09-30, Humanifa/GPT 5.6 2026-10-02, "max gp" 2026-10-13 | see dates | https://github.com/leanprover/lean-eval-submissions/tree/main/results [READ] |
| Baker-type bound for logs of positive rationals, eventual lower bound | Lean 4 | mjtb49 repository (from the earlier report) | pushed 2026-10-14 | https://github.com/mjtb49/Bounds-on-linear-forms-in-logarithms [READ in earlier report, not re-read] |
| Baker's theorem, any version | Isabelle, Rocq, HOL Light, Mizar | none found | as of 2026-11-22 | searches 1, 2, 4 and the Gelfond-Schneider paper's related-work section [READ/SNIPPET; absence of evidence only] |
| Hermite-Lindemann-Weierstrass (Baker's formulation) | Isabelle AFP | M. Eberl | 2021-03-03 (outline revised 2026-02) | https://www.isa-afp.org/entries/Hermite_Lindemann.html [READ] |
| Transcendence of e and pi | Rocq (Bernard, Bertot, Rideau, Strub); HOL Light (e, Bingham); Mizar (Watase) | per the Gelfond-Schneider paper | n/a | https://arxiv.org/pdf/2603.24823 [READ] |
| Lindemann-Weierstrass | Lean/Mathlib | Mathlib has only the analytic part; PR #28013 "Lindemann-Weierstrass Theorem" open, updated 2026-11-06 | | https://github.com/leanprover-community/mathlib4/pull/28013 [READ] |
| Lindemann-Weierstrass, lean-eval problems `lindemann` and `lindemann_weierstrass` | Lean 4 | 8 accepted each, from 2026-06-14; some public (gists, `humanfia/lean-eval`, speedrun repos) | | results JSON files [READ]; I did not open the public sources |
| Six exponentials | any | none found | | search 4 snippet [SNIPPET; absence of evidence] |
| Schneider-Lang (general meromorphic version) | any | none found; the special case for group products is in the Baker branch | | [READ] for the branch |

### lean-eval data (the coordinator's lead), checked directly

Source: all 65 `results/*.json` files in `github.com/leanprover/lean-eval-submissions`, 2,124 accepted results over 277 problems, of which 695 have a public source and 1,429 are private. [READ]

- **Baker-Wüstholz (`bakerWustholz_linearForms_logs`): 4 accepted, not 3 or 5. First is 2026-09-22 (00:48 UTC), not 09-21, by Axiom Prover.** All four have `public: false`. Metadata: Humanifa and "max gp" entries say `solution_publication_status: private`; the NEAR AI entry says publication planned for 2026-11-12, but its repository returned 404 when I tried it today; Axiom's has no publication metadata. The four repositories I tried (Axiom, NEAR AI, hongzhoulin89, ma4ypic4y) all return 404 to the GitHub API, so no source is public. [READ]
- The submissions README says accepted scheduled source is released under Apache License 2.0 exactly two UTC calendar months after acceptance, and a public repository must use scheduled publication. [READ] The first Baker acceptance is 2026-09-22, so the earliest release would be 2026-11-22 (today); `leanprover/lean-eval-releases` is described as "Disabled-by-default delayed source release tooling" and I found no release for Baker in it. [READ] So: not public today, license would be Apache-2.0 when released, release date uncertain. Size and Mathlib version are unknown; one entry's metadata mentions a Lean 4.35 migration and a 4,621-job workspace build.
- **Exact statement** (read from `LeanEval/NumberTheory/BakerWustholz.lean`): `n ≥ 1`, number field `K` with embedding `φ : K →+* ℂ`, nonzero `α : Fin n → K`, **integer** coefficients `b i` with `|b i| ≤ B`, `B ≥ 2`, and the linear form `Λ = ∑ b i * Complex.log (φ (α i))` nonzero. Conclusion: `Real.log ‖Λ‖ ≥ -(C n d * max (log B) (1/d) * ∏ modifiedHeight φ (α i))` with `C n d = 18 (n+1)! n^(n+1) (32 d)^(n+2) log(2nd)`. It is quantitative and has **integer, not algebraic, coefficients**. [READ] Mathlib's `Height.logHeight₁` is used.
- **Does it give your hypothesis?** No (my own reasoning, flagged as such). Your hypothesis is "Q-independent logs of algebraic numbers stay independent over Q-bar". With integer coefficients, Q-independence already makes `Λ ≠ 0` for nonzero integer vectors, so the effective bound adds nothing about algebraic coefficients. Getting algebraic coefficients needs the full Baker 1966-68 argument (or the Baker-Wüstholz group-variety argument with algebraic coefficients); I estimate essentially all of the work remains, in the sense that none of the integer-coefficient proof's key step (the transcendence argument over a number field of coefficients) is reused automatically. Treat as unverified, since the private proofs cannot be read.
- **Chudnovsky (`chudnovsky_formula_for_pi_inv`): 10 accepted, first 2026-07-05** (ldct, Claude Opus 4.8 + Fable 5 multi-agent, and rishistyping, same day), then Seed Prover 07-21, Aristotle 08-09, two speedruns 08-17, Humanifa 08-31 and 09-23, Tau 09-05, Axiom 09-25. Three are marked public: ldct, savarin, Vilin97 (speedrun). [READ]
  - Only `ldct/lean-eval-chudnovsky` was reachable: public, GitHub reports no license (the repository has no LICENSE file in its tree), size about 283 KB, `lean-toolchain` is `v4.32.0-rc1`. Its README says about 20k lines in 30 modules under `Submission/Pi/`, following Milla's proof (arXiv 1809.00533v6). [READ] The other two "public" repositories returned 404 today.
  - Mathlib itself still has only the definition `chudnovskySum` and a `proof_wanted` in `Wanted/Analysis/Real/Pi/Chudnovsky.lean`; the file `Mathlib/Analysis/Real/Pi/Chudnovsky.lean` was last touched 2026-11-21 (unrelated cleanup). [READ]
- **Other transcendence problems:** Schmidt subspace (`schmidt_subspace`): 8 accepted from 2026-08-22, all private. Thue-Siegel-Roth: 5 accepted, all private. Lindemann and Lindemann-Weierstrass: see table. **No Gelfond-Schneider problem exists in lean-eval** (not in the results). [READ]
- **Gelfond-Schneider in Mathlib: no.** PR #42911 (+5,066 lines) is open and "blocked"; dependency PRs #35735, #35743, #35744, #39874 and #39875 are all open (the last updated 2026-11-19). Code search of Mathlib master for "GelfondSchneider" returns nothing, and the master file tree has no such directory. [READ]

## What Mathlib has

Checked against Mathlib master (file listing and raw source read today). Declaration names are as they appear in the source; namespaces were not always checked.

| Need | Declaration or "missing" | Where |
|---|---|---|
| Siegel's lemma over Z | `Int.Matrix.exists_ne_zero_int_vec_norm_le` (and primed variant), bound `(|β| * max 1 ‖A‖)^(|α|/(|β|-|α|))` | `Mathlib/NumberTheory/SiegelsLemma.lean` |
| Siegel over rings of integers of number fields | `NumberField.house.exists_ne_zero_int_vec_house_le` and `NumberField.house.basis_repr_norm_le_const_mul_house`, listed on the Mathlib docs page for `House.lean` (the docs build may be newer than master's file; PR #39875 "expose Siegel lemma infrastructure" is still open, so check) | `Mathlib/NumberTheory/NumberField/House.lean` [READ docs page] |
| House of an algebraic number | `NumberField.house`, `house_add_le`, `house_mul_le`, `house_pow`, `house_prod_le`, `norm_embedding_le_house`, `one_le_house_of_isIntegral`, `norm_norm_le_norm_mul_house_pow` | same file |
| Heights | `Height.mulHeight₁`, `Height.logHeight₁`, `one_le_mulHeight₁`, Northcott (`finite_setOfPred_logHeight₁_le`) | `Mathlib/NumberTheory/Height/Basic.lean`, `.../NumberField.lean`, `.../Northcott.lean` |
| Liouville-type lower bound for algebraic numbers | only the real-number Liouville statement `exists_pos_real_of_irrational_root` (for the Liouville-number theory); the number-field version (nonzero algebraic integer has norm at least 1 across conjugates) must be assembled from `Algebra.norm` and `house` lemmas; no ready declaration seen | `Mathlib/NumberTheory/Transcendental/Liouville/Basic.lean`; the Baker branch has its own `Baker/Liouville.lean`, `AlgSize.lean` |
| Norms, conjugates | `Algebra.norm`, `NumberField.RingOfIntegers.norm` lemmas (`isUnit_norm`, `norm_norm`) | `Mathlib/NumberTheory/NumberField/Norm.lean` |
| Number field embeddings | `NumberField.InfinitePlace`, canonical embedding (used by `house`) | `Mathlib/NumberTheory/NumberField/Basic.lean` and neighbours |
| Cauchy integral formula | `DiffContOnCl.circleIntegral_sub_inv_smul`, `circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`, `DifferentiableOn.analyticOnNhd` | `Mathlib/Analysis/Complex/CauchyIntegral.lean` |
| Cauchy estimates | `norm_deriv_le_of_forall_mem_sphere_norm_le`, `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` | `Mathlib/Analysis/Complex/Liouville.lean` |
| Maximum modulus | `norm_le_of_forall_mem_frontier_norm_le`, `norm_eqOn_closure_of_isPreconnected_of_isMaxOn` | `Mathlib/Analysis/Complex/AbsMax.lean` |
| Schwarz lemma (one variable) | `norm_le_norm_of_mapsTo_ball`, `dist_le_div_mul_dist_of_mapsTo_ball`, `norm_dslope_le_div_of_mapsTo_ball` | `Mathlib/Analysis/Complex/Schwarz.lean` |
| Jensen's formula | `MeromorphicOn.circleAverage_log_norm`, `AnalyticOnNhd.sum_divisor_le` | `Mathlib/Analysis/Complex/JensenFormula.lean` |
| Order of vanishing | `analyticOrderAt`, `analyticOrderNatAt` | `Mathlib/Analysis/Analytic/Order.lean`; isolated zeros in `.../IsolatedZeros.lean` |
| Entire functions of several variables, Schwarz lemma for products | missing from what I saw; the Baker branch proves its own (`SchwarzProduct.lean`, 910 lines, "Newton division one coordinate at a time") | Baker branch [READ] |
| Linear independence of exponentials | not found in Mathlib master (unverified); the Baker branch has `ExpIndep.lean` | Baker branch |
| Vandermonde determinant | `Matrix.det_vandermonde`, `det_vandermonde_ne_zero_iff` | `Mathlib/LinearAlgebra/Vandermonde.lean` |
| Lindemann-Weierstrass | only the analytic part: `LindemannWeierstrass.exp_polynomial_approx_aux` etc. (216 lines); the theorem is PR #28013 (open) | `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean` |
| Transcendence of e, pi | not found in master (unverified); `Mathlib/Analysis/Real/Pi/Irrational.lean` has irrationality only; the Baker branch derives `transcendental_pi` from Baker | |
| Kummer theory | `Mathlib/FieldTheory/KummerExtension.lean`, `KummerPolynomial.lean` exist (contents not read) | |
| L(1, chi) nonzero | `DirichletCharacter.LFunction_apply_one_ne_zero`, `LFunction_ne_zero_of_one_le_re` | `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` |
| Gelfond-Schneider | missing (PRs open) | see status |

## Candidate blueprints compared

| Source | Length / form | Tools | Hard to formalize | Note |
|---|---|---|---|---|
| Baker, *Transcendental Number Theory* (1975), Ch. 2 (Theorem 2.1) | book chapter; I could not open it | one-variable auxiliary function, Siegel lemma, extrapolation, Liouville bound, special interpolation polynomial (Lemmas 3-7) per the Baker branch's own summary [READ] | extrapolation bookkeeping and long inequality chains; no Kummer step | Harper and Dasgupta follow it; the doc comment in the Baker branch cites it as the theorem source |
| Harper, "A version of Baker's theorem" (Warwick, 2010) | 7 pages [READ] | weak form (needs 2*pi*i among the independent logs); one-variable function, Siegel lemma, Schwarz-type lemma, Liouville-type norm argument | constants and exponents, the extrapolation loop | shortest complete-looking human proof I found; https://warwick.ac.uk/fac/sci/maths/people/staff/harper/bakernotes.pdf |
| Dasgupta, "Ranks of matrices of logarithms I" (arXiv 2303.02037), Section 2 | about 9 pages for Baker (pp. 4-13) in a 45-page note [READ] | same method; adds a clean Vandermonde step (Theorem 2.2: nonzero polynomial vanishing on (L+1)^n powers gives a multiplicative relation) and "bootstrapping" to drop 2*pi*i | same as Harper | Vandermonde step maps directly to `Matrix.det_vandermonde_ne_zero_iff` |
| Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (Springer 2000) Ch. 4 | book, about 640 pages in total [SNIPPET for the page count, not checked]; Ch. 4 is the Schneider-Lang route | Baker deduced from the Schneider-Lang criterion on C^d0 x (C*)^d1 (Bertrand-Masser); Schwarz lemma for products, Thue-Siegel lemma, one transcendence argument | the several-variable Schwarz lemma and parameter choice; no zero estimate needed for this special group | **this is the route the Baker branch actually formalized** (7,383 lines) [READ] |
| Baker-Wüstholz 1993 / Waldschmidt book later chapters | long; I did not open them | multiplicity estimates (zero estimates) on commutative algebraic groups; Philippon-Waldschmidt, Masser-Wüstholz | zero estimates (heavy algebraic geometry) | needed for effective bounds, not for qualitative Baker; not recommended |
| Laurent's interpolation determinants | in Waldschmidt's *Linear Independence of Logarithms of Algebraic Numbers* (one chapter), and Laurent 1994 [SNIPPET] | determinants replace the auxiliary function; the search result suggests Siegel's lemma may still appear as an auxiliary result | determinant non-vanishing and Liouville estimates; less pigeonhole, more algebra | better for effective two- and three-logarithm bounds; not clearly shorter for the qualitative theorem |
| Bugeaud, *Linear Forms in Logarithms and Applications* (IRMA 2018) | 240 pages [READ on the publisher page] | exposition focused on applications; the publisher page does not say whether Baker's theorem is proved in full (it reads as a black box, my inference) | n/a | not a proof blueprint |
| Bilu's notes | not opened | | | unverified |

Ranking for a from-scratch project (only relevant if the fork branch turns out unusable): Dasgupta Section 2 for the plan, Baker 1975 Ch. 2 for the details; Waldschmidt Ch. 4 is the route that is already done in the fork.

## Easier special cases

- **n = 2 is Gelfond-Schneider**, already formalized (not yet in Mathlib). I found no source saying n = 3 is notably easier for the qualitative statement; the extra logarithm adds a variable to the auxiliary function and the extrapolation. Mignotte-Voutier's "kit" for three logarithms is for effective bounds [SNIPPET].
- **Cyclotomic or abelian numbers:** I found no simpler proof of qualitative Baker for numbers in an abelian extension. Searching for one returned only sources that use Baker's theorem: Murty's use of Ramachandra units shows that L(1, chi) values for non-trivial even characters mod q are independent over Q-bar, via Baker [SNIPPET]. For odd characters L(1, chi) is an algebraic multiple of pi [SNIPPET]. The dependence runs the other way from what you want: non-vanishing of L(1, chi) (in Mathlib as `LFunction_apply_one_ne_zero`) is a consequence of the class number formula and does not give independence over Q-bar of logarithms of cyclotomic numbers by itself. I found no route that avoids transcendence theory.
- **Rational logarithms with integer coefficients:** a weaker eventual bound exists in Lean (mjtb49), but it does not give algebraic coefficients.
- **p-adic route:** the Gelfond-Schneider paper suggests a p-adic Gelfond-Schneider via Schnirelmann integrals as future work [READ]; the `baker-padic` branch exists, but p-adic independence does not give the complex statement you need.
- **Weak form:** Harper and Dasgupta prove the version where 2*pi*i is added to the independent set. For your application (logs of 1 - r/(1+i) and primes) the extra 2*pi*i can be handled by the bootstrapping step, but it is moot if you import the full theorem.

## Staged plan with size estimates

Yardstick from the Gelfond-Schneider formalization: the paper reports **no line counts and no person-months** [READ: I searched its full text for lines, person, month, week, year and found none; the only effort figures are secondhand]. Secondhand figures: Mathlib PR #42911 is +5,066 lines [READ]; the fork's `GelfondSchneider` directory at commit 9710b82 is about 480 KB over 14 files, the largest `Main.lean` at 232 KB [READ]; the Zulip thread (earlier report) says the main file exceeds 6,000 lines and upstreaming would be "more like 50 PRs" [page, second-hand]. The Baker branch is 7,383 lines, written mostly 2026-09-23/24 after a July 2026 setup, with AI assistance.

**Plan A (recommended): import, do not re-prove.**

| Chunk | Task | Estimate (mine) |
|---|---|---|
| 0 | Fetch branch `baker` (commit tip 2026-09-24), build the 19 files against your Lean 4.36 Mathlib (the branch is on v4.35.0-rc2; expect small port fixes: deprecations, `module` syntax already used) | hours to 2 days |
| 1 | Audit: `#print axioms Transcendental.baker` (expect the three standard axioms), check no `sorry`, read the statements of `baker`, `schneiderLang`, `theorem45` | 1 day |
| 2 | Replace your hypothesis by `Transcendental.baker` (same shape); keep your hypothesis form as a thin wrapper | 1-3 days |
| 3 | License and credit: files carry Apache-2.0 headers (author Michail Karatarakis); the fork has no extra license I checked, so contact the author for permission to vendor or for a tagged release | email |

**Plan B (only if the fork fails the audit): re-prove, following Dasgupta Section 2 / Baker 1975 Ch. 2.** Rough sizes (my estimates, anchored on GS at about 5-6k lines of Lean):

| Chunk | Content | Lines | Notes |
|---|---|---|---|
| B1 | Vandermonde reduction (Dasgupta Thm 2.2), algebraic-integer size lemmas (Lemma 2.3), Liouville norm bound | 800-1,500 | Mathlib has Vandermonde, house, norms |
| B2 | Auxiliary function by Siegel's lemma (Thm 2.5), derivative vanishing from the dependence relation | 1,500-2,500 | `Int.Matrix.exists_ne_zero_int_vec_norm_le` is in Mathlib |
| B3 | Analytic lemma (Baker's Lemma: Schwarz/max-modulus bound for functions vanishing with derivatives) | 1,000-2,000 | Mathlib has Schwarz, Cauchy estimates, max modulus |
| B4 | Extrapolation loop and parameter choice | 2,000-3,500 | the hard part; constants as in GS (c1..c15 there) |
| B5 | Bootstrapping to the full statement and to algebraic `beta_0` | 500-1,000 | |
| Total | | 6,000-10,000 | similar to or somewhat above GS; the branch needed 7,383 by the Waldschmidt route |

## Alternative targets

**(a) Chudnovsky formula for 1/pi.**
- Mathlib: definition `chudnovskySum` in `Mathlib/Analysis/Real/Pi/Chudnovsky.lean`; the statement `chudnovskySum = π⁻¹` is a `proof_wanted` in `Wanted/Analysis/Real/Pi/Chudnovsky.lean`. [READ] The file says it does not yet contain a proof and calls the gap large; it cites Milla and Chen-Glebov. [READ]
- Proofs on paper: Milla, arXiv 1809.00533 (6 versions, last 2021-03-16; bilingual v2 with two 42-page editions; self-contained except one chapter) [SNIPPET]; Guillera, arXiv 2003.06668 (uses Weber modular equations) [SNIPPET]; Chen-Glebov, arXiv 1609.05778, "On Chudnovsky-Ramanujan Type Formulae" [SNIPPET]. My search did not confirm the "modular-free" description for Chen-Glebov; Milla's proof is built on Eisenstein series [SNIPPET].
- Formalization: **done outside Mathlib**: 10 accepted lean-eval solutions since 2026-07-05; the public one I could read (`ldct/lean-eval-chudnovsky`) is about 20k lines, Lean v4.32.0-rc1, no license file. [READ] Not upstreamed. So it is no longer a "first".

**(b) Dimitrov's proof of the Schinzel-Zassenhaus conjecture.**
- arXiv 1912.12545, submitted 2019-12-28, published in the Annals; the proof uses a Diophantine rationality theorem (Polya-type) and an idea from Bell-Nguyen-Zannier [SNIPPET]. Dubinin's theorem appears in the hedgehog/Mahler-measure literature as the potential-theoretic input [SNIPPET]. The PDF could not be read (compressed content), so page count and exact structure are unverified.
- Formalization: none found in Lean, Isabelle or Rocq (search 12; absence of evidence only). Mathlib has the pieces the earlier report named (house, heights, Northcott), but not Dubinin's theorem (not seen) and I did not check Polya's criterion.

## Honest verdict

**Is Baker within reach of one person plus an AI assistant in months?** From scratch, yes but only at roughly Gelfond-Schneider scale: 6-10k lines, several months, with the extrapolation step as the risk. That question is now mostly moot, because **a qualitative Baker proof of exactly the form you need is already on a public fork branch** (7,383 lines, no `sorry`, dated 2026-09-24, same author as the Gelfond-Schneider formalization). It is unbuilt by me, unmerged, and apparently unannounced, so the right plan is to import and audit it, not to re-prove it. The Baker-Wüstholz solutions on lean-eval are private (earliest scheduled release possibly today), carry integer coefficients, and would not supply your hypothesis even when released; Chudnovsky has public solutions, but they are not relevant to Baker.

**First chunk:** build branch `baker` (tip 2026-09-24) in a scratch copy against your Lean 4.36 Mathlib, run `#print axioms Transcendental.baker`, and check it prints only the three standard axioms; then email the author about license and a stable tag. If the build fails in a way that is not a port issue, switch to Plan B and start with chunk B1 (Vandermonde reduction and norm lower bound).

Things I did not verify: that the branch compiles (the fork's "main" check-run reported success, but I do not know what it runs and the "ci" run was skipped), whether it has been reviewed by anyone, and whether the stale docstring in `Basic.lean` reflects an unfinished state. Treat "complete" as a claim by the commit messages and a clean grep, not as a checked fact.

## Queries used (12 WebSearch calls in total)

1. Baker's theorem linear forms in logarithms Lean 4 formalization Mathlib Karatarakis
2. Lean Zulip Baker linear forms in logarithms Schneider-Lang formalized
3. Archive of Formal Proofs Hermite-Lindemann-Weierstrass transcendence Eberl
4. six exponentials theorem formalization proof assistant Lean Isabelle Coq
5. Waldschmidt Diophantine Approximation on Linear Algebraic Groups Baker theorem Schneider-Lang criterion Chapter 4 lecture notes
6. Laurent interpolation determinants method linear forms in logarithms without Siegel lemma extrapolation Roy Waldschmidt
7. Bugeaud Linear Forms in Logarithms and Applications IRMA Lectures 2018 Baker Wüstholz proof outline
8. linear independence of logarithms of cyclotomic units algebraic numbers Baker Brumer without transcendence L(1,chi) nonvanishing
9. Milla detailed proof of the Chudnovsky formula with means of basic complex analysis arXiv
10. Chen Glebov Chudnovsky formula 1/pi elementary proof without modular forms
11. Dimitrov proof of the Schinzel-Zassenhaus conjecture arXiv
12. formalization Schinzel-Zassenhaus conjecture Lean OR Isabelle OR Coq Mahler measure Dubinin

Total: **12 WebSearch calls (of 29)**. All other lookups were WebFetch calls and GitHub API reads (`gh api`), which are not limited. (In the Dimitrov and Chudnovsky parts, "search 16" in the text means search 12 here.)

## Sources

- Baker branch: https://github.com/mkaratarakis/mathlib4/tree/baker (files `Mathlib/NumberTheory/Transcendental/Baker/*.lean`, read via the GitHub contents API)
- p-adic branch: https://github.com/mkaratarakis/mathlib4/tree/baker-padic
- Gelfond-Schneider paper: [arXiv 2603.24823](https://arxiv.org/abs/2603.24823)
- Mathlib PRs: [#42911](https://github.com/leanprover-community/mathlib4/pull/42911), [#28013](https://github.com/leanprover-community/mathlib4/pull/28013), [#39875](https://github.com/leanprover-community/mathlib4/pull/39875)
- lean-eval: [problem page](https://lean-lang.org/eval/problems/bakerWustholz_linearForms_logs/), [statement file](https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/BakerWustholz.lean), [results](https://github.com/leanprover/lean-eval-submissions/tree/main/results), [release tooling](https://github.com/leanprover/lean-eval-releases)
- Chudnovsky: [lean-eval problem](https://lean-lang.org/eval/problems/chudnovsky_formula_for_pi_inv/), [public submission](https://github.com/ldct/lean-eval-chudnovsky), [Mathlib file](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Real/Pi/Chudnovsky.lean), [Milla](https://arxiv.org/abs/1809.00533), [Guillera](https://arxiv.org/abs/2003.06668), [Chen-Glebov](https://arxiv.org/pdf/1609.05778)
- Schinzel-Zassenhaus: [Dimitrov](https://arxiv.org/abs/1912.12545)
- Blueprints: [Harper notes](https://warwick.ac.uk/fac/sci/maths/people/staff/harper/bakernotes.pdf), [Dasgupta, arXiv 2303.02037](https://arxiv.org/pdf/2303.02037), [Waldschmidt book page](https://www.springer.com/us/book/9783540667858), [Bugeaud book](https://ems.press/books/irma/157), [Laurent 1994](https://geodesic.mathdoc.fr/articles/10.4064/aa-66-2-181-199)
- AFP: [Hermite-Lindemann](https://www.isa-afp.org/entries/Hermite_Lindemann.html)
- Zulip thread where Baker is only a hypothesis: [Collatz thread](https://leanprover-community.github.io/archive/stream/113488-general/topic/Conditional.20no-cycle.20proof.20for.20Collatz.20.E2.80.94.20feedback.20welcome.html)
- Mathlib docs and sources read: [SiegelsLemma](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/SiegelsLemma.html), [House](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/House.html), plus raw files under `Mathlib/Analysis/Complex/`, `Mathlib/Analysis/Analytic/`, `Mathlib/LinearAlgebra/Vandermonde.lean`, `Mathlib/NumberTheory/Height/`, `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`
