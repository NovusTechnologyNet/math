# R01: what a formal proof of Baker's theorem makes possible

Date of pass: 22 November 2026. Marks: [READ] read on the source page, [SNIPPET] seen only in a
search result / API record / abstract, [INFERRED] my own conclusion or recollection (to be checked).

## 1. Summary

1. The formal Baker proof (Karatarakis, branch `baker` of his mathlib4 fork, 19 files) proves the
   QUALITATIVE theorem with constant term: Q-independent logs l_i of algebraic numbers and a
   relation beta0 + sum beta_i l_i = 0 with algebraic beta force all beta = 0 [READ, local
   `lean/Baker/README.md`, `Basic.lean`]. No effective bound, no Baker-Wustholz, no p-adic part there.
2. Not announced in any paper I found. The only public paper is Karatarakis-Wiedijk,
   arXiv 2603.24823, on Gelfond-Schneider (GS) only [READ]. It calls Baker "the most natural
   extension" and names Schneider-Lang, p-adic (Mahler, Veldkamp), measures, elliptic functions,
   Schanuel-conditional work as other directions [READ]. I found no Baker-specific paper or Zulip post.
3. Mathlib status (22 Nov 2026): GS is not merged as a whole. Karatarakis's PR #42911 (GS
   statement, 117 commits) is open, "blocked-by-other-PR", no reviews; the analytic-lemma parts
   1-5 by another author are merged; Lindemann-Weierstrass PR #28013 (astrainfinita) is open,
   label awaiting-author, reviewers want a module docstring, last pushes 6 Nov 2026 [READ].
   Baker itself: no PR found [searched mathlib4 issues for "Baker linear forms logarithms": 0 hits].
4. Effective Baker (Baker-Wustholz 1993) is an OPEN formalization problem on lean-eval: statement
   with `sorry`, no submissions [READ]. The Tau Ceti roadmap puts qualitative Baker in its
   "Linear forms in logarithms" roadmap and effective bounds (its items 3.6, 3.7) in the
   "Diophantine approximation and transcendence" roadmap [READ].
5. So every classical corollary that needs only the qualitative theorem is now formally reachable;
   everything effective (class number one, explicit Diophantine equations) is not.
6. Best targets for this project: (i) the unweighted Chowla/ASST theorem (periodic algebraic f,
   sum f(n)/n is 0 or transcendental; L(1,chi) transcendental), a direct generalisation of what
   the project already did for weights 2^(-floor(k/2)); (ii) Baker corollary layer
   (transcendence of pi + log alpha, prod alpha^beta, exp(beta0)prod alpha^beta) to hand to Mathlib /
   Tau Ceti; (iii) digamma / Euler-Lehmer "at most one algebraic".
7. Other formal transcendence in 2026 is moving fast but mostly AI-written and unreviewed:
   six exponentials and strong six exponentials (two public Lean repos), Schneider-Lang inside the
   Karatarakis branch, Roth in Tau Ceti (per its roadmap).
8. No overlap or conflict with the project's results; the statement "values are 0 or transcendental"
   is the ASST 2001 theorem and the README already says so.

## 2. What is known

### 2.1 The formalisations (question 1)

- [READ, local file `lean/Baker/README.md`] `Transcendental.baker`: l_i complex, Q-linearly
  independent, each exp(l_i) algebraic, beta0 + sum beta_i l_i = 0 with algebraic beta => all zero.
  Follows Waldschmidt, Diophantine approximation on linear algebraic groups, ch. 4; equals Theorem 2.1
  of Baker's 1975 book. The same file derives GS and transcendence of pi. Source commit
  1d51891b (24 Sep 2026), not merged, 76 commits ahead of Mathlib a0e13008, only 19 new files;
  `#print axioms` gives the three standard axioms. File list includes `SchneiderLang.lean`,
  `ThueSiegel.lean` (Siegel-lemma constants), `Liouville.lean`, `Interpolation.lean`,
  `CriterionMain.lean`: so a Schneider-Lang criterion (the Waldschmidt ch. 4 form, with d0 <= n < d0+d1)
  is inside the proof [INFERRED from file names and from the roadmap below].
- [READ, Tau Ceti roadmap `LinearFormsInLogarithms/README.md`] Planned layers: Schneider-Lang
  criterion (5.7), Hermite-Lindemann (6.3, "x != 0, exp x algebraic => x transcendental"), GS (6.4),
  Baker over C (7.1-7.3: `Baker.eq_zero_of_add_sum_mul_eq_zero`, `Baker.transcendental_sum_mul`,
  `Baker.add_sum_mul_ne_zero`, `Baker.transcendental_exp_add_sum_mul`,
  `Baker.transcendental_exp_sum_mul`, `Baker.transcendental_prod_cpow`), and p-adic Baker (8.10,
  Brumer form; `PadicBaker.transcendental_exp_prime`). Stated consequences: e, pi, exp(pi),
  2^sqrt2, log 2, log2/log3, pi + log 2 transcendental. The roadmap says most of this exists
  sorry-free on branches of `mkaratarakis/mathlib4`. It explicitly excludes effective bounds,
  Laurent, class number, Siegel's integral-points theorem, Schanuel.
- [READ] Karatarakis-Wiedijk, arXiv 2603.24823 (25 Mar 2026, cs.LO): theorem
  `transcendental_cpow_of_isAlgebraic_of_irrational`; house of an algebraic number; Siegel's lemma
  for rings of integers (descended from Mathlib's integer version); sanity check sqrt2^sqrt2. Code is
  on a mathlib4 fork under `Mathlib/NumberTheory/Transcendental/GelfondSchneider`; "parts" already
  integrated in Mathlib. Authors say the analytic part of Lindemann-Weierstrass has been formalised
  by others and that Isabelle's AFP has Hermite-Lindemann-Weierstrass. Future work: Baker, Schneider-Lang,
  p-adic analogues, measures, Weierstrass p-function, decision procedures, Schanuel-conditional.
  No repository link on the arXiv abstract page; I did not find a Baker paper.
- [READ] lean-eval problem `bakerWustholz_linearForms_logs`: n >= 1, number field K with
  embedding into C, nonzero alpha_i in K, integers b_i with |b_i| <= B, B >= 2, Lambda != 0
  => log|Lambda| >= -C(n,[K:Q]) max(log B, 1/[K:Q]) prod modified heights. Status: `sorry`, no
  solutions listed (page's leaderboard not loaded).
- [READ] lean-eval `thue_siegel_roth`: open, `sorry`; the page says Mathlib has Liouville,
  Dirichlet approximation and `ae_not_liouvilleWith` but no Roth lemma / auxiliary polynomials.
  [READ, Tau Ceti Diophantine-approximation roadmap]: states Roth's theorem is "already proved in Tau Ceti"
  (not verified in the Tau Ceti code, its file tree was too large to fetch).
- [SNIPPET/READ] Third-party Lean repos (all AI-written, unreviewed by experts per their own READMEs):
  `carlok/diaz-modulus-lean` (729 results, claims Hermite-Lindemann, Lindemann-Weierstrass, GS,
  Baker, six exponentials, only the three standard axioms; I could not see its Baker proof, so I do not
  know whether it is independent of Karatarakis);
  `carlok/six-exponentials-lean` (six exponentials, d+l<dl version, Schneider's method via Lang-Ramachandra;
  registered "Palomar" 22 Nov 2026); `telaviv/strong-six-exponentials` (Roy's strong six exponentials,
  Philippon multiplicity estimate, ~13k lines, Lean 4.35). Mathlib PR #43144 (pi transcendental via an
  external, Claude-written formalisation, for the 100-theorems list) was closed 3 Oct 2026 by a maintainer
  with the remark that AI-generated entries are not wanted in that file [READ]. Consequence for the
  project: any upstreaming of AI-assisted work may meet that policy.
- [READ] Mathlib docs: `NumberTheory/Transcendental/Liouville` is the transcendence file I could confirm;
  `Liouville.transcendental`. Hermite-Lindemann in Mathlib is not confirmed (see section 3).

### 2.2 Classical consequences of the qualitative theorem (question 2)

Common core (Baker 1966-68, book ch. 2): [READ, Wikipedia + ar5iv 1604.02896] a form
beta1 log a1 + ... + betan log an with algebraic beta, a nonzero algebraic, is 0 or transcendental;
the qualitative theorem with constant term says 1, l_1..l_n are linearly independent over the algebraic
numbers when the l_i are Q-independent logs. Wikipedia: if beta0 != 0 the independence can be dropped.

(a) Algebraic combinations of logs. [READ] Theorem (Baker): beta0 + sum beta_i log alpha_i is 0 or
    transcendental. Formal: this is what `baker_const` in the project (`PiFormula/Transcendence.lean`)
    already proves from `BakerTheorem` for a finite family without the independence hypothesis.
    [INFERRED] The same statement follows from `Transcendental.baker` by choosing a Q-basis of the span.
(b) Exponentials: e^(beta0) alpha1^beta1 ... alphan^betan is transcendental for algebraic alpha_i != 0
    (log branches fixed), beta_i algebraic, beta0 != 0 [READ, Baker 1966 as cited by Wikipedia and in the
    Tau Ceti roadmap names `transcendental_exp_add_sum_mul`, `transcendental_prod_cpow`].
    Gelfond's e^pi, and 2^sqrt2, are special cases [READ roadmap].
(c) pi + log alpha: [INFERRED] pi = -i log(-1), so pi + log alpha is an algebraic combination of the logs of
    -1 and alpha; it is 0 or transcendental, and 0 would make alpha = e^(-pi) algebraic, contradicting
    Gelfond (e^pi transcendental). The roadmap lists "pi + log 2 transcendental" [READ].
(d) Integrals: [INFERRED] int_0^1 dx/(1+x^3) = (log 2 + pi/sqrt3)/3, a non-zero algebraic combination of
    logs of 2 and -1, hence transcendental. General principle: integral of a rational function with algebraic
    coefficients over algebraic endpoints is 0 or transcendental if the path avoids the poles (Baker's book
    ch. 2 states this; I did not read the chapter, so details of hypotheses are unchecked).
(e) Sums of periodic rational functions: Adhikari-Saradha-Shorey-Tijdeman, "Transcendental infinite sums",
    Indag. Math. 12 (2001) 1-14 [SNIPPET, zbMATH review by Bundschuh, Zbl 0991.11043]: (i) f algebraic-valued,
    periodic mod q, sum f(n)/n convergent: the sum is not a non-zero algebraic number (it may be 0), and L(1,chi)
    is transcendental for every non-principal Dirichlet character, q >= 3; (ii) Q with simple, rational,
    non-non-negative-integer roots: convergent sum f(n)/Q(n) is an effectively computable algebraic number or
    transcendental; (iii) roots in [-1,0): never a non-zero algebraic number, e.g. sum 1/((3n+1)(3n+2)(3n+3))
    transcendental; (iv) numerators exponential polynomials, e.g. sum F_n/(2^n n) (Fibonacci) transcendental.
    Earlier root: Bundschuh, "Zwei Bemerkungen ueber transzendente Zahlen", 1979 [SNIPPET, zbMATH review]:
    purely periodic algebraic sequence, the power series at h/k is 0 or transcendental. The sum with weights
    2^(-floor(k/2)) in this project is the same mechanism.
(f) L(1,chi): [READ, 1604.02896] odd chi: L(1,chi) is a non-zero algebraic multiple of pi; even non-principal chi:
    a non-zero algebraic multiple of a sum of logs of units (Ramachandra units); transcendence follows from Baker.
    Murty-Murty, "Transcendental values of class group L-functions" (2011) [SNIPPET, zbMATH review by Gun]:
    L(1,chi) and pi are linearly independent over the algebraic closure of Q, via Kronecker's limit formula
    and Baker. Murty-Murty/Okada: L(1,chi), chi even non-trivial mod q, linearly independent over algebraic
    numbers [SNIPPET].
(g) Chowla's problem and Baker-Birch-Wirsing (1973), "On a problem of Chowla", J. Number Theory 5 [bibliography
    entry only; theorem seen second-hand]: for algebraic-valued periodic f (f(n)=0 for 1<(n,q)<q) not identically
    zero, sum f(n)/n != 0 if the q-th cyclotomic polynomial is irreducible over Q(f(1..q)) [READ, ar5iv 1604.02896,
    Theorem 11, quoting the condition on irreducibility]. Murty-Murty 2011 "A problem of Chowla revisited"
    [SNIPPET, review Bundschuh, zbMATH 1241.11083] replace that condition by one on the odd part f_o; it recovers
    Okada. This is the one place where Baker is used for NON-VANISHING (not only transcendence).
    [INFERRED] the proof needs Baker (to make 1, log of cyclotomic units independent over Q-bar) plus a Galois/cyclotomic
    argument; Mathlib has irreducibility of cyclotomic polynomials over Q.
(h) Digamma and Euler-Lehmer constants: Murty-Saradha, J. Number Theory 125 (2007) 298-318 [READ via ar5iv
    1308.6451 which restates it]: for n > 1, at most one of the phi(n)+1 numbers {gamma} U {psi(r/n), (r,n)=1} is
    algebraic. Chatterjee-Gun, Acta Arith. 162 (2014) [READ]: across all n, at most one element of
    {gamma} U {psi(r/n)} is algebraic. Proof: difference of two algebraic psi values would be an algebraic combination
    of logs (Gauss's formula), non-zero as psi is strictly increasing. Murty-Saradha, "Euler-Lehmer constants and a
    conjecture of Erdos", J. Number Theory 130 (2010) [SNIPPET]: at most one gamma(a,q) algebraic; Erdos's conjecture on
    sum f(n)/n partly proved (q = 3 mod 4). Gun-Saha-Sinha, J. Number Theory 145 (2014) [SNIPPET]: generalised constants
    over finite prime sets, "at most one algebraic". Weatherby 2010-11 [SNIPPET]: multi-index and Chowla-type infinite sums
    via digamma + Baker; k > 1 variables needs Schanuel. p-adic versions use the p-adic Baker (Kaufman, Brumer).
    Whether gamma itself is transcendental, or even irrational, is open [READ, 1604.02896 and 1308.6451].
(i) Class number one and Diophantine equations: Baker (1966-71) via the EFFECTIVE bound; Heegner and Stark also solved
    it without Baker. [READ Wikipedia] The bounds need the quantitative theorem (Baker 1977 or Baker-Wustholz 1993
    form: log|Lambda| > -C h(alpha_1)...h(alpha_n) log max|b_i|, C = 18(n+1)! n^(n+1) (32d)^(n+2) log(2nd)).
    Not available in the formal proof.

### 2.3 Other formal transcendence results (question 4)

- Lindemann-Weierstrass: Mathlib PR #28013 open (see 1.3) [READ]. Isabelle AFP has Hermite-Lindemann-Weierstrass [READ,
  via the GS paper]. Earlier Coq: Bernard 2017, "Formalization of the Lindemann-Weierstrass theorem", Springer chapter [SNIPPET, Crossref].
- GS: Mathlib PRs 33050, 34836-34838, 35315-35317 (analytic lemmas) merged; 35733-35735, 39874, 42911 (Karatarakis) mostly
  open or closed-and-resubmitted [SNIPPET from the GitHub search API; merge flag not shown, titles say "Merged by Bors"].
  An older Lean 4 GS repo `raghuram-13/Gelfond-Schneider-in-lean` (last update Feb 2024, 0 stars) [SNIPPET].
- Six exponentials and strong six exponentials: two Lean repos, AI-written, axiom-clean by their own claim [READ READMEs].
- Siegel's lemma: integer version in Mathlib; number-field version in the GS paper [READ].
- Thue-Siegel-Roth: open on lean-eval; Tau Ceti roadmap says Roth is proved there (unverified).
- Schneider-Lang: inside Karatarakis's Baker files (`SchneiderLang.lean`), roadmap target 5.7; the "algebraically independent
  entire functions" general form is excluded from the roadmap [READ].
- Mason-Stothers (Baek-Lee, arXiv 2408.15180) fully in Mathlib [READ abstract]; function-field analogue, not transcendence.

## 3. What is open

- Formal effective Baker (Baker-Wustholz, Matveev, Laurent): open; stated as an open challenge by lean-eval and as a later roadmap
  item by Tau Ceti. [READ]
- Merging into Mathlib of GS, LW, Baker: open as of today; Baker not yet under review. Policy risk for AI-written files (PR #43144). [READ]
- Hermite-Lindemann as a stated theorem in Mathlib: not confirmed. I searched mathlib4 issues for "Lindemann Weierstrass"
  (found only #28013) and did not open the docs for `Transcendental` e; weak evidence.
- Transcendence/irrationality of Euler's constant: open [READ].
- Schanuel's conjecture, four exponentials conjecture, algebraic independence of logs: open, not reached by Baker [READ Wikipedia].
- Chowla's problem in full generality (non-vanishing of sum f(n)/n for all algebraic periodic f vanishing off the units) is not fully
  solved by Baker-Birch-Wirsing; Murty-Murty extend it [SNIPPET]. The exact present state I did not verify (no source read on it).

## 4. Leads for this project, ranked

Ranking columns: effort (a), number-theorist interest (b), Lean-community interest (c).

| # | Statement | (a) effort | (b) | (c) |
|---|-----------|-----------|-----|-----|
| 1 | Unweighted ASST: algebraic periodic f mod q, sum f(n)/n 0 or transcendental; L(1,chi) transcendental | 1-3 weeks | medium (2001 result, but first formal) | high |
| 2 | Baker corollary layer (items a, b, c, d) with a clean Mathlib-style API | days | low | high |
| 3 | Murty-Saradha / Chatterjee-Gun: at most one of gamma, psi(r/n) algebraic | 3-6 weeks | medium | medium |
| 4 | Baker-Birch-Wirsing + Murty-Murty (non-vanishing of sum f(n)/n) | 4-8 weeks | high | high |
| 5 | Effective Baker, class number one | months to years | very high | very high |

Lead 1 (rank 1). Exact statement: for q >= 1, f : N -> Qbar periodic mod q with sum_{n} f(n)/n convergent (equivalently sum_{a<=q} f(a)=0),
the sum S(f) is 0 or transcendental; for chi a non-principal Dirichlet character mod q, L(1,chi) is transcendental. Why this toolkit
fits: the project already proves the weighted version (`PiFormula/Transcendence.lean`: `baker_const`, `alg_eq_zero_of_hasSum_add_mul_pi`) with
the same pipeline (finite-index sum of logs of cyclotomic numbers plus pi, rational coefficients). The unweighted case is simpler (weight 1,
so the algebraic input is 1 - zeta^a, with log(1 - zeta^a) real part and pi cot-type imaginary part). Missing piece: the Gauss formula for
sum f(n)/n as a finite combination of log(1 - zeta^a), i.e. the project's Abel-summation step with b = 1; likely already close to the base-b
machinery. Noticeable because it would be the first formal ASST and a clean Mathlib-friendly corollary (Mathlib already proves L(1,chi) != 0
for Dirichlet's theorem [INFERRED, not checked]; transcendence is a strict strengthening).

Lead 2 (rank 2). Exact statement: (i) pi + log alpha, (ii) e^(beta0) prod alpha_i^beta_i, (iii) log alpha / log beta for algebraic alpha, beta
with log alpha/log beta irrational, are transcendental or (when stated) 0; all from `Transcendental.baker`. Why it fits: `baker_const` in our
Transcendence.lean already removes the independence hypothesis, which is the step the roadmap lists as 7.2/7.3. Missing: Mathlib-style naming,
branch conventions of complex logs. Rough size: days. Worth noticing: hand to Tau Ceti roadmap owners (their 7.3 is exactly this) rather than
compete. Caveat: they treat the Karatarakis branch as starting point only, and Mathlib's policy on AI-generated files could bar the upstreaming.

Lead 3 (rank 3). Statement: for the Lean digamma/Hurwitz-zeta layer of Mathlib (existence of ψ at rationals is not confirmed [INFERRED]), the
Murty-Saradha theorem. Missing: Gauss's digamma theorem psi(r/n) = -gamma - log(2n) - (pi/2) cot(pi r/n) + 2 sum cos(2 pi k r/n) log sin(pi k/n)
(my recollection of the classical formula; not read in a source this pass) and Euler's constant as Mathlib object (`Real.eulerMascheroniConstant`
exists [INFERRED]). Size: weeks. Notice: first formal digamma transcendence.

Lead 4 (rank 4). Baker-Birch-Wirsing nonvanishing needs both Baker and Galois theory of cyclotomic fields; Mathlib has cyclotomic irreducibility
[INFERRED]. High payoff (Chowla's problem; Okada's theorem on linear independence of cot values by Girstmair's remark [SNIPPET]). Risky: I have
not read the BBW proof; its exact hypotheses must be checked in the 1973 paper.

Lead 5 (rank 5). Out of reach with the present theorem: all effective uses (class number one, Thue/Mahler equations, Catalan-type
explicit bounds) need the quantitative Baker-Wustholz theorem; lean-eval lists it as open. Large project (Wustholz's analytic subgroup
theorem proof, 60+ pages), and Tau Ceti has assigned it already.

What is gained by having the qualitative theorem: all of (a)-(h) in 2.2 except (i). Reading of rank by (c): Lean people care about
corollaries with short statements stateable without number-theory background (leads 1, 2, 4).

## 5. Overlap or conflict with the project

- No conflict. The project's README states "Known in print (Adhikari, Saradha, Shorey, Tijdeman, 2001)" for "values are 0 or
  transcendental"; this is consistent with what the zbMATH review says (2.2 (e)). Our classes (weights b^(-floor(k/2))) are not literally
  in ASST; the unweighted theorem (lead 1) is, so lead 1 is a formalisation of a known result, not a new result.
- One caution on provenance: the project's `lean/Baker/README.md` says the proof is not announced. Public evidence agrees (no Baker paper;
  Tau Ceti's roadmap treats the branch as a starting point). The roadmap says "most of the development ... sorry-free on branches of
  mkaratarakis/mathlib4", so more files may exist than the 19 in the vendored folder (SchneiderLang, Layer 8 p-adic?). Worth asking
  or re-checking the branch before relying on its form.

## 6. Sources

- https://arxiv.org/abs/2603.24823 and https://arxiv.org/html/2603.24823v1 (Karatarakis-Wiedijk)
- https://lean-lang.org/eval/problems/bakerWustholz_linearForms_logs/ and .../thue_siegel_roth/
- https://github.com/leanprover-community/mathlib4/pull/28013 , /pull/42911 , /pull/43144
- https://raw.githubusercontent.com/TauCetiProject/TauCetiRoadmap/main/TauCetiRoadmap/LinearFormsInLogarithms/README.md
- https://raw.githubusercontent.com/TauCetiProject/TauCetiRoadmap/main/TauCetiRoadmap/DiophantineApproximationAndTranscendence/README.md
- https://github.com/carlok/diaz-modulus-lean , https://github.com/carlok/six-exponentials-lean , https://github.com/telaviv/strong-six-exponentials
- https://en.wikipedia.org/wiki/Baker%27s_theorem
- https://ar5iv.labs.arxiv.org/html/1308.6451 (Chatterjee-Gun), https://ar5iv.labs.arxiv.org/html/1604.02896 (Euler-Briggs constants)
- https://arxiv.org/abs/2408.15180 (Mason-Stothers)
- zbMATH Open API records and reviews (Murty-Saradha, ASST, Murty-Murty, Gun-Saha-Sinha, Bundschuh 1979, Weatherby)
- Local: lean\Baker\README.md, \lean\Baker\Basic.lean (not opened in full), \lean\Pilean\PiFormula\Transcendence.lean

Page text that addressed an agent: none seen.
Endpoints that refused automated access: export.arxiv.org API (HTTP 429, repeatedly), OpenAlex (429 with a long Retry-After),
Crossref (429 after the first few calls), Semantic Scholar (429/403), GitHub code search (401), queensu.ca PDFs (redirect).
Not read: Murty-Saradha 2007 PDF, BBW 1973, Waldschmidt book, Murty-Rath book chapters.

## 7. Search log

WebSearch (4): 1 Baker formalization Lean Karatarakis Wiedijk; 2 Karatarakis mathlib4 Baker branch; 3 Thue-Siegel-Roth / six
exponentials / Schneider-Lang Lean 2026; 4 Murty Saradha Euler-Lehmer digamma Baker arXiv.

Endpoint queries (about 85 fetches including about 15 refusals):
arXiv API x3 (all 429; "Baker's theorem Lean", "Gelfond-Schneider Lean", "Baker transcendental math.NT"); arXiv abs pages 2603.24823,
1008.4107 (wrong id, irrelevant), 2602.12891, 2408.15180; arXiv html 2603.24823v1; ar5iv 1308.6451, 1604.02896; arXiv pdf 1303.1856 (unreadable).
OpenAlex x2 (429). Crossref: Baker formalization; digamma Murty Saradha (429); Euler-Lehmer (429); ASST (429); Chowla BBW (429);
LW formalization. Semantic Scholar: citations of 2603.24823 (empty), LW formalization (429), web search (403).
zbMATH (13): formalization Lean transcendence; Euler-Lehmer; Chowla Dirichlet Baker (404); digamma Baker; periodic rational function sums;
class number one Baker; L(1,chi) transcendence; ASST; BBW; Chowla revisited; polygamma; digamma Murty-Saradha; Okada; Gun-Saha-Sinha.
GitHub API: repos "Gelfond Schneider lean"; "Karatarakis"; "Baker theorem linear forms lean4" (2 variants, empty / 403);
"transcendence lean4 LW Schneider-Lang" (empty); "six exponentials lean"; "Lindemann-Weierstrass lean4"; "TauCeti org";
issues in mathlib4: Baker (0), Lindemann Weierstrass, Gelfond Schneider, Siegel lemma; code search (401); tree of TauCetiRoadmap and TauCeti (too large).
GitHub pages/raw: mathlib4 PR 28013, 43144, 42911; carlok/diaz-modulus-lean (page, README 404 x2, docs 404 x2, contents API);
carlok/six-exponentials-lean; telaviv/strong-six-exponentials; TauCetiRoadmap README + two roadmap READMEs; TauCetiProgress README.
Other: Wikipedia Baker's theorem; lean-eval pages x2; Mathlib docs Liouville; OEIS (empty); queensu.ca PDF (redirect).

Totals: WebSearch calls = 4. Endpoint queries = about 85 (counted from my call list; about 15 returned errors).
