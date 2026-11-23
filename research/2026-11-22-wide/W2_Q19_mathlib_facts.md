# W2-Q19: which classical prime-and-pi facts are in Mathlib (checked 22 Nov 2026)

Method: I read the Mathlib source itself, from the project's own checkout at
`C:\Users\Spontaneous\Documents\github\math\lean\.lake\packages\mathlib`, which is commit
fc4f59e577 ("chore: bump toolchain to v4.36.0 (#46085)", committed 16 Nov 2026). Everything
marked [READ] below was read in that source tree (grep plus reading the files). Open and
closed pull requests were read through the GitHub REST API (unauthenticated; the search
endpoint hit its rate limit once and was retried with pauses). Nothing was run from the web.
Declaration names are as in that tree. Changes merged after 16 Nov 2026 are not seen.

## 1. Summary

1. The Basel problem, zeta(2k) with Bernoulli numbers, the Euler product of zeta and of
   Dirichlet L (Re s > 1), L(1,chi) != 0, and Dirichlet's theorem are all in Mathlib.
2. The prime number theorem IS in Mathlib itself now: `Nat.isEquivalent_primeCounting`
   in `Mathlib/NumberTheory/LSeries/WeakPNT.lean` (merged 11 Nov 2026, #43238), plus the
   version in arithmetic progressions. The docs file `docs/100.yaml` still points to the
   PrimeNumberTheoremAnd repository; it is out of date on this.
3. Natural density of coprime pairs (6/pi^2) and of squarefree numbers: NOT in Mathlib; no
   natural-density notion exists in Mathlib either (only Schnirelmann density). A density PR
   (#42540) was closed unmerged on 14 Nov 2026.
4. Euler products at s = 1 (including prod p/(p - chi_4(p)) = pi/4): NOT in Mathlib. The
   Euler product theorems need `1 < s.re`. No theorem gives L(chi_4, 1) = pi/4, but the
   Leibniz series itself is there.
5. Mertens' theorems: NOT merged. Three open PRs (#41394, #44061, #46026). Only a helper
   file on log-sums exists.
6. Leibniz series, Wallis product, Euler's sine product, Machin-type formulas (four of
   them, including Machin's own), rigorous decimal bounds on pi up to 20 digits, and
   irrationality of pi are in. No BBP formula; Chudnovsky is only a definition plus a
   `proof_wanted`.
7. Generalized continued fractions: a real theory exists (`GenContFract`, convergents, Euler
   continued fractions, the regular continued fraction of a real number and its
   convergence). No continued fraction for pi, e, or Brouncker's is proved.
8. Dilogarithm/polylogarithm: not merged; one open PR (#44531, polylog). Normal numbers /
   Borel's theorem: absent. Zsigmondy: absent (PR #28895 closed unmerged).
9. Earlier conflicting answers are settled in section 4.

## 2. What is known, item by item

### (1) Basel and zeta(2k)  -- IN
- `hasSum_zeta_two : HasSum (fun n : N => 1/(n:R)^2) (pi^2/6)`, file
  `Mathlib/NumberTheory/ZetaValues.lean` [READ]. Listed in docs/100.yaml (Euler's
  summation, authors Masdeu and Loeffler) [READ].
- `hasSum_zeta_nat {k} (hk : k != 0)`: sum of 1/n^(2k) = (-1)^(k+1) 2^(2k-1) pi^(2k)
  bernoulli(2k)/(2k)!, same file [READ]. `hasSum_zeta_four` (pi^4/90) also there.
- `riemannZeta_two : riemannZeta 2 = pi^2/6`, `riemannZeta_four`, `riemannZeta_two_mul_nat`
  (Bernoulli form), `riemannZeta_neg_nat_eq_bernoulli` in
  `Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean` [READ].
- Also a mod-4 value L(chi,3) = pi^3/32 style statement in the same file (the docstring
  at ZetaValues.lean "Explicit formula for L(chi,3)") [READ the docstring; I did not
  read the full statement].

### (2) Euler products  -- IN, for Re s > 1 only
- File `Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean` [READ]:
  `riemannZeta_eulerProduct_hasProd`, `riemannZeta_eulerProduct_tprod`,
  `riemannZeta_eulerProduct` (all `1 < s.re`);
  `DirichletCharacter.LSeries_eulerProduct_hasProd / _tprod / LSeries_eulerProduct`
  (product over `Nat.Primes` of (1 - chi(p) p^(-s))^(-1), `1 < s.re`);
  exp-log forms `riemannZeta_eulerProduct_exp_log`, `DirichletCharacter.LSeries_eulerProduct_exp_log`,
  `riemannZeta_eq_exp_LSeries`, `log_riemannZeta_eq`.
- General engine in `EulerProduct/Basic.lean`: `EulerProduct.eulerProduct_hasProd`,
  `eulerProduct_completely_multiplicative_hasProd` etc., with hypothesis absolute
  summability (`Summable (fun n => ||f n||)`) [READ]. That hypothesis is exactly what fails at s = 1.

### (3) L(1,chi) != 0 and Dirichlet's theorem  -- IN
- `DirichletCharacter.LFunction_ne_zero_of_one_le_re` (non-vanishing on Re s >= 1 unless
  chi trivial and s = 1) in `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` [READ].
- `Nat.infinite_setOfPred_prime_and_eq_mod`, `Nat.forall_exists_prime_gt_and_eq_mod`,
  `Nat.forall_exists_prime_gt_and_modEq`, `Nat.infinite_setOfPred_prime_and_modEq`
  (a coprime to q), in `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` [READ]. In 100.yaml
  [READ]. Also `ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div`
  (sum of 1/p over a residue class diverges) [READ].
- Bonus: Dirichlet class number formula residue,
  `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`, in
  `Mathlib/NumberTheory/NumberField/DedekindZeta.lean` [READ].

### (4) Densities of coprime pairs and squarefree numbers  -- NOT IN
- Searched the whole tree for: `natDensity`, `upperDensity`, `lowerDensity`, "natural
  density", "asymptotic density", `6 / pi`, "coprime ... density/probab/asymptotic",
  "squarefree ... density/asympt" [READ: no hits other than below].
- The only density notion is `schnirelmannDensity` in `Mathlib/Combinatorics/Schnirelmann.lean`;
  its docstring lists "lower and upper asymptotic density, and the natural density" as
  to-do [READ].
- Squarefree material is only algebraic (Moebius: `moebius_ne_zero_iff_squarefree`
  etc.); no counting asymptotics. The sum of totient is only the exact identity
  `Nat.sum_totient` (sum over divisors = n) [READ]; no asymptotic of sum phi(n).
- PR #42540 "asymptotic / natural density and linear-growth bridge" (new
  `Combinatorics/AsymptoticDensity.lean`): CLOSED, not merged, 14 Nov 2026, after a
  reviewer asked for a more general design [READ via API; 20 comments, I read the first five].
- Component pieces that would be needed are in: `Nat.totient`, `ArithmeticFunction.moebius`,
  `sum_moebius`-type convolution identities, `hasSum_zeta_two`, Abel summation
  (`Mathlib/NumberTheory/AbelSummation.lean`). So 6/pi^2 would be a derivation, not a
  find. [INFERRED]

### (5) Conditionally convergent Euler product at s = 1  -- NOT IN
- Searched: `eulerProduct` with `1 <= re` hypotheses; chi4 / `chi_4` / "L(chi_4)"; "pi_div_four"
  products; none [READ: no hits]. All Euler product theorems carry `1 < s.re`
  [READ] (list above).
- What IS there that bears on it: the Leibniz series
  `Real.tendsto_sum_pi_div_four` (partial sums of (-1)^i/(2i+1) -> pi/4) in
  `Mathlib/Analysis/Real/Pi/Leibniz.lean`, proved by Abel's limit theorem [READ]; non-vanishing
  of L at Re s >= 1; and the continuation of L-functions (`DirichletContinuation.lean`).
  The identity L(chi_4,1) = pi/4 (Leibniz series = value of the analytically continued
  `DirichletCharacter.LFunction` at 1) is not stated; linking the two would need
  the equality of the series with the continuation on Re s = 1 (not in Re s > 1).
  [INFERRED from not finding it]
- No theorem about convergence of prod p/(p - chi(p)) in increasing order of primes.

### (6) Mertens' theorems  -- NOT MERGED
- No declaration named for Mertens in the tree [READ]. Support only:
  `Mathlib/Analysis/SpecialFunctions/Log/Sum.lean` (Tao, 2026), whose docstring says it is
  for the proof of Mertens' theorems: `sum_log_eq_log_factorial`, `sum_log_le`, `le_sum_log`
  [READ]; Chebyshev bounds in `Mathlib/NumberTheory/Chebyshev.lean`
  (`theta_le_log4_mul_x`, `psi_le_const_mul_self`, `psi_ge`, `theta_ge`, ...) [READ];
  `Chebyshev.isLittleO_sum_vonMangoldt_with_sum_prime_log_with` [READ, name only];
  `LSeries_vonMangoldt_eq` [READ, name only]; Euler-Mascheroni constant
  `Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean` (existence, `tendsto_eulerMascheroniSeq`) [READ].
- Open PRs [READ via API]: #41394 "the Mertens theorems" (all three, explicit error terms;
  labelled blocked-by-other-PR, t-number-theory, 5 files; depends on the split-out
  #44061 "abstract theory of Mertens weights" and #44062 "prime and von Mangoldt weights");
  #46026 "Mertens' first theorem" (new contributor, labelled LLM-generated, 14 Nov 2026).
  Closed unmerged: #45477 (first and second, explicit constants), #40656, #39532.
- Also open: #45844 "Moebius form of the PNT" (sum mu(n) = o(x)), labelled LLM-generated.

### (7) Leibniz, Wallis, Machin, bounds, BBP
- Leibniz: `Real.tendsto_sum_pi_div_four`, `Mathlib/Analysis/Real/Pi/Leibniz.lean` [READ];
  in docs/100.yaml.
- Wallis: `Real.tendsto_prod_pi_div_two` (product of (2k)(2k)/((2k-1)(2k+1)) -> pi/2),
  with `Real.Wallis.W`, `W_le`, `le_W`, `Mathlib/Analysis/Real/Pi/Wallis.lean` [READ].
- Euler sine product: `Complex.tendsto_euler_sin_prod`, `Real.tendsto_euler_sin_prod` in
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean` [READ]. Cotangent
  expansion in `Trigonometric/Cotangent.lean` [READ, file exists].
- Machin-type, `Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean` [READ]:
  `arctan_add`, `arctan_inv_2_add_arctan_inv_3` (pi/4), `two_mul_arctan_inv_2_sub_arctan_inv_7`,
  `two_mul_arctan_inv_3_add_arctan_inv_7`, `four_mul_arctan_inv_5_sub_arctan_inv_239`
  (Machin). Series for arctan: `Real.hasSum_arctan` (|x| < 1), `Complex.hasSum_arctan`,
  `Mathlib/Analysis/SpecialFunctions/Complex/Arctan.lean` [READ].
- Bounds, `Mathlib/Analysis/Real/Pi/Bounds.lean` [READ]: `pi_gt_sqrtTwoAddSeries`,
  `pi_lt_sqrtTwoAddSeries`, `pi_gt_three`, `pi_lt_four`, `pi_gt_d2/d4/d6/d20` and
  `pi_lt_d2/d4/d6/d20` (20 decimals), `floor_pi_eq_three`.
- `irrational_pi`, `Mathlib/Analysis/Real/Pi/Irrational.lean` [READ].
- Chudnovsky: `Mathlib/Analysis/Real/Pi/Chudnovsky.lean` only DEFINES `chudnovskySum`
  and says it contains no proof; the statement `chudnovskySum_eq_pi_inv` is a
  `proof_wanted` in `Wanted/Analysis/Real/Pi/Chudnovsky.lean` [READ].
- BBP / Bailey / Plouffe: no hit in Mathlib, Archive, Counterexamples, Wanted [READ: grep];
  GitHub issue/PR search "BBP" in mathlib4 gave 0 results [READ via API].
- Transcendence of pi: docs/100.yaml lists it as in external forks only (Morris; Zhao) [READ];
  in the tree only `Transcendental/Lindemann/AnalyticalPart.lean` exists (no Lindemann-Weierstrass
  statement), so `Real.transcendental_pi` is not in Mathlib at this commit. [READ the directory;
  did not read the file contents beyond the name list]

### (8) Generalized continued fractions  -- THEORY IN, NO PI CF
- Directory `Mathlib/Algebra/ContinuedFractions/` [READ]: `Basic.lean` (gcf, scf, rcf,
  `GenContFract.convs`, `convs'`, `nums`, `dens`), `ContinuantsRecurrence.lean`,
  `ConvergentsEquiv.lean` (`GenContFract.convs_eq_convs'` under positivity),
  `Determinant.lean`, `Euler.lean` (`GenContFract.IsEuler`, `euler`, `toEuler`,
  `convs_euler`, `convs_toEuler`: Euler's continued-fraction equivalence, algebraic form only),
  `TerminatedStable.lean`, `Translations.lean`, and `Computation/` (the algorithm
  `GenContFract.of v`, `ContFract.of`, `TerminatesIffRat.lean` terminates iff rational,
  `Approximations.lean`, `ApproximationCorollaries.lean` with `GenContFract.of_convergence`
  and the bound `abs_sub_convs_le`).
- So: the continued fraction of a REAL number v computed by the standard algorithm
  converges to v and terminates iff v is rational. NOT in: a general convergence theorem for
  arbitrary gcf (Seidel-Stern, Pringsheim, Worpitzky), the continued fraction of e, of
  sqrt 2 / quadratic irrationals (periodicity), of pi, Brouncker's
  4/pi = 1 + 1^2/(2 + 3^2/(2 + ...)) , or Lambert's tan continued fraction. Searched the
  tree for Brouncker, "continued fraction"+pi, e, golden/periodic, `HasSimpleContFrac` [READ: no hits];
  GitHub search "Brouncker" in mathlib4: 0 results [READ via API].
- Diophantine side, `Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean`:
  convergents are the good rational approximations (Legendre-type) [READ, file exists; not
  read in detail].

### (9) Dilogarithm / polylogarithm  -- NOT MERGED
- No definition of `Li_s` or the dilogarithm in the tree [READ: grep "polylog|dilog"]. The
  only mention is a docstring in `Mathlib/Analysis/SpecialFunctions/Integrals/Log.lean`
  (the integral of log sin "involves the dilogarithm, this can be seen as computing special
  values of Li_2") [READ].
- Open PR #44531 "add the polylogarithm function" (5 Oct 2026, t-analysis; files
  `Analysis/SpecialFunctions/Polylog/Basic.lean` + a Topology file): defines
  `Complex.polylog`, integral representation, power series, the recurrence
  z * deriv (Li_(s+1)) z = Li_s z, analyticity off the branch cut [READ via API].

### (10) Normal numbers / Borel's theorem  -- ABSENT
- grep for "normal number", `isNormal`, "simply normal", equidistribution, Weyl, "strong law":
  no number-theoretic hit (only unrelated "normal" structures) [READ]. Digit infrastructure
  exists: `Mathlib/Analysis/Real/OfDigits.lean` (`Real.ofDigits`, `ofDigits_digits`,
  `hasSum_ofDigitsTerm_digits`, continuity, surjectivity) [READ], and
  `MeasureTheory/OuterMeasure/BorelCantelli.lean` [READ, file exists]. No strong law
  of large numbers for digits and no "almost every real is normal" statement.
  GitHub search "normal number Borel": 4 hits, none relevant [READ via API].

### (11) Zsigmondy / Bang  -- ABSENT
- No `Zsigmondy`, no "primitive prime divisor" in Mathlib [READ: grep]. PR #28895
  "prove Zsigmondy's theorem" (`Mathlib/NumberTheory/Zsigmondy.lean`, opened 25 Aug 2025) was CLOSED without
  merging on 18 Sep 2026 after a long stretch of "has conflicts" notices [READ via API].
  GitHub search "Bang theorem primitive prime divisor": 0 results. The tools in tree
  (lifting the exponent in `Mathlib/NumberTheory/Multiplicity.lean`, cyclotomic polynomials
  in `NumberTheory/Cyclotomic/`, `Polynomial.cyclotomic` evaluation) are what a proof would use.
  [INFERRED]

### (12) Prime number theorem  -- IN MATHLIB (not only PNT+)
- `Nat.isEquivalent_primeCounting : pi ~ x / log x` and
  `Nat.isEquivalent_card_prime_modEq` (PNT in progressions) in
  `Mathlib/NumberTheory/LSeries/WeakPNT.lean` [READ], deduced from the Wiener-Ikehara
  theorem `WienerIkehara.tendsto_sum_div` (`LSeries/WienerIkehara.lean`) [READ]. Also
  `Chebyshev.isEquivalent_psi_id`, `isEquivalent_theta_id`, `Nat.eventually_exists_prime_mem_Ioc`
  (prime in (x,(1+eps)x] for large x), `Nat.isEquivalent_nth_prime_succ`,
  `Nat.isEquivalent_log_primorial_id`. The file header says its results could later
  be superseded by approaches with error terms [READ].
- The latest commit touching it is 99fb99cb2, 11 Nov 2026, "the (weak) prime number theorem
  (#43238)" [READ via git log in the checkout].
- Not in Mathlib: PNT with error term (that is "MediumPNT" in PrimeNumberTheoremAnd) [READ
  from docs/100.yaml link text; docs/100.yaml still credits PNT+ only].
- The Mathlib file also ships PNT for progressions, so a statement such as "primes
  1 mod 4 have density 1/2 among primes" follows from it. [INFERRED]

## 3. What is open (in Mathlib), with what is missing

| Item | Missing | Where it stands |
|---|---|---|
| density of coprime pairs, squarefree numbers | the notion of natural density, then the two theorems | PR #42540 closed; nothing open found [READ API] |
| Euler product at s = 1, L(chi_4,1) = pi/4 as an Euler product | any statement at Re s = 1 | not found; no PR found |
| Mertens 1-3 | all | PRs #41394 (stack with #44061, #44062), #46026 open |
| BBP-type formula | any | none found (0 GitHub hits) |
| Chudnovsky | the proof | `proof_wanted`, definition merged |
| CF of pi, e; Brouncker | all | none found |
| polylog / dilog | all (dilog) / merge (polylog) | PR #44531 open |
| normal numbers | all | none found |
| Zsigmondy | all | PR #28895 closed unmerged |
| PNT with error term | all | in PrimeNumberTheoremAnd, not Mathlib |
Each "none found" is weak evidence: it means grep over the tree and GitHub issue search
found nothing, not that nobody has code elsewhere (forks, other repositories).

## 4. Earlier conflicting answers, settled

- (4) coprime / squarefree density: the correct answer is "not in Mathlib, and not even the
  density notion". Anyone who said otherwise was probably thinking of Schnirelmann density or
  of the closed PR #42540.
- (5) Euler product at s = 1: absent; all Euler product lemmas need `1 < s.re`.
- (8) continued fractions: theory exists (more than just a definition), but no
  continued fraction of a named constant; Euler's form is algebraic only.
- (9) dilogarithm: not merged; polylog PR open (#44531). The docstring mention of Li_2 is not a definition.
- (10) normal numbers: absent. Digits (`Real.ofDigits`) exist but nothing about normality.
- PNT: the "only in PrimeNumberTheoremAnd" answer is outdated as of 11 Nov 2026.

## 5. Leads for this project (ranked)

1. Natural density of coprime pairs / squarefree numbers is a free, citable gap: a project
   file proving 6/pi^2 from `hasSum_zeta_two`, `Nat.totient`, Moebius inversion and
   Abel summation would be new to Mathlib. Days to a couple of weeks; the tools (zeta(2),
   Moebius) are all in. Worth noticing only as a library contribution, not research.
2. The conditionally convergent Euler product prod p/(p - chi_4(p)) = pi/4 (ordered by
   size) is a gap, and it is a real theorem that depends on L(chi_4,1) = pi/4 plus a
   Mertens-type/PNT argument for convergence at s = 1. With PNT now in Mathlib it is
   within reach but weeks of work; it would be the pi-and-primes bridge the project lacks.
3. Zsigmondy is absent after the PR was closed. The project already uses primitive prime
   divisors, so its own formal proof of the needed case would also fill a library gap
   (the previous Mathlib attempt may be a starting point). Days to weeks.
4. Brouncker's continued fraction and a BBP formula are both absent; the project's BBP
   classification is therefore, as far as this tree shows, the only machine-checked treatment
   of pi series of that type. No overlap with any Mathlib file.

## 6. Overlap or conflict with the project's results

None found. No BBP-type, base-b, or Baker-type statement exists in Mathlib; the
only partial overlap is that `Real.hasSum_arctan` and the Machin-type identities in
`Arctan.lean` give the classical arctan formulas the project's "Machin-type" discussions
relate to. Note for the project's imported Baker proof: the Lindemann file
(`Transcendental/Lindemann/AnalyticalPart.lean`) holds only the analytic part, so no
transcendence of pi is available in Mathlib itself.

## 7. Sources

- Mathlib source (local checkout, commit fc4f59e577, tag v4.36.0), files named above.
- https://github.com/leanprover-community/mathlib4 (pull requests 28895, 41394, 42540,
  44061, 44531, 45477, 45844, 46026, and the search API results listed in the log).
- docs/100.yaml and docs/1000.yaml in the same checkout.

## 8. Search log

Totals: WebSearch calls: 0. Endpoint queries: 41 successful GitHub REST calls (plus 10 that
returned a rate-limit error and were retried later). I used curl and Python urllib to the
GitHub API rather than the fetch tool, because the JSON results needed filtering; no
personal details were sent. Beyond that, about 40 grep/read passes over the local Mathlib tree.

GitHub issue/PR search, repo leanprover-community/mathlib4 (q = query):
1 coprime density; 2 squarefree density; 3 Mertens; 4 normal number; 5 Zsigmondy;
6 polylogarithm; 7 dilogarithm; 8 continued fraction pi; 9 BBP; 10 Euler product s=1;
11-17 pull-request detail for 28895, 44531, 41394, 46026, 44061, 45844, 45477;
18 natural density; 19 asymptotic density; 20 coprime pairs probability; 21 Chudnovsky;
22 Brouncker; 23 Bang theorem primitive prime divisor; 24 Schnirelmann;
25 Mertens third theorem; 26 normal number Borel; 27 continued fraction convergents e;
28 Liouville/Hermite transcendental; 29-37 pull-request detail, comments and file lists for
42540, 28895, 44531 (3 calls each).
Rate-limited and retried: queries on natural density primes, Basel, Euler-Mascheroni,
squarefree count, and others (retried under 18-28 above).
Local tree reads: ZetaValues.lean, HurwitzZetaValues.lean, EulerProduct/*, Nonvanishing.lean,
PrimesInAP.lean, WeakPNT.lean, WienerIkehara.lean, Chebyshev.lean, Log/Sum.lean,
Pi/{Leibniz,Wallis,Bounds,Chudnovsky,Irrational}.lean, Arctan.lean, ContinuedFractions/*,
OfDigits.lean, Schnirelmann.lean, DedekindZeta.lean, Wanted/, docs/100.yaml, docs/1000.yaml.
No web page contained text addressed to me.
