# 13 Gap filler: Takahashi, Baker branch, pi*sqrt formulas, Bilu-Luca (2026-11-22)

Tags: [READ] = seen in fetched content (including PDFs I text-extracted or looked at as images); [SNIPPET] = only in a search snippet or a WebFetch summarizer's paraphrase; "reconstructed" and "from memory, unverified" as stated. Numerical checks marked [CHECKED] were done by me with a short high-precision script on the formulas as read (50-60 digits); they confirm the transcription, not any claim of the source.

## Summary (10 lines)

1. Gap 1 SOLVED. The author's accepted manuscript of Takahashi 2020 is open access in the Tsukuba repository (record 2001720); I read it in full [READ]. Both proposed formulas are base -2^30 (terms (-1)^k/2^(30k)), with denominators 12k+j, 20k+j, 30k+j, 10k+5; they are (23) and (26) of the paper, written out in Gap 1 (a). Both [CHECKED] to 59 digits.
2. His cost model counts terms: a base-b formula with t terms per period costs t * (4n/log2 b) terms for starting position n (in hex digits). Huvent twice = 16n/3; pair (23)+(26) = 64n/15, because the 15 terms S(30,j) are shared. 64/15 divided by 16/3 = 0.8, i.e. 20% fewer.
3. Huvent's formulas are base 2^12, period 24, 8 terms each, read from French Wikipedia; both [CHECKED]. Takahashi's text uses only the first one (his eq. (10), 8 terms, (8/3)n per run).
4. "Least number of terms" is only a statement of folklore ("known as") in the abstract; no proof or conjecture of minimality found anywhere. Bailey's compendium cites the Borwein-Galway-Borwein 2004 result that degree-1 BBP formulas for pi exist only in power-of-two bases (from the compendium, [READ]).
5. y-cruncher: only the version history mentions it. v0.8.4 (21 Feb 2024) added Huvent's BBP formula "slightly faster than Bellard's"; v0.8.5 (1 Jul 2024) made it the default. No ranking table beyond that, no mention of Takahashi or of two-formula verification. [READ]
6. Gap 2: NO paper, PR, Zulip thread or announcement of the Baker proof found. Only indirect public traces: a TauCetiRoadmap PR (#451) that cites branch `baker` at commit 1d51891b5b, and an open TauCeti PR (#42369) that says a parallel formalisation exists in Karatarakis's fork. The branch is 76 commits on top of upstream Mathlib commit a0e13008 (2026-09-23), toolchain Lean v4.35.0-rc2. A roadmap STATUS.md of 2026-11-19 still says Baker "not started" (inconsistent).
7. Gap 3: pi*sqrt2, pi*sqrt3, pi*sqrt5 have binary formulas (Bailey compendium 20, 21, 22; periods 12, 6, 40; also MathWorld shorter ones, period 6; Adegoke et al. pi*sqrt3 base 2^12 period 24). pi/sqrt3 follows from pi*sqrt3 by a rational factor. Nothing found for pi times 2cos(pi/10) or tan(pi/10).
8. Gap 4: Bilu-Luca is arXiv:2607.28857 (30 July 2026), "Multiplicative dependence in the sumset of multiplicative groups". It is about x+y with x in Gamma, y in Delta (finitely generated, almost disjoint), not specifically about alpha - zeta or 1 - zeta*alpha. Preface by Bilu: Luca died during final preparation.
9. Its canonical family (1.7) is exactly the cyclotomic relation prod_j (x - zeta^j y) = x^(m-1) - y^(m-1); Conjecture 1.6 says these are, up to finitely many exceptions, the only minimal dependences. Theorem 1.2 (m = 2) is proved; m = 3 only under abc.
10. No arXiv result found that states the lemma "multiplicative relations among alpha - zeta, zeta over all roots of unity" directly. Closest: Drungilas-Dubickas (PAMS 2019) on m - zeta_k and n - zeta_k [SNIPPET]. Web searches used: 12 of 18.

## Gap 1: Takahashi's two BBP-type formulas for pi

Source for everything in this section unless stated: D. Takahashi, accepted manuscript of Ramanujan J. 51 (2020) 177-186, https://tsukuba.repo.nii.ac.jp/records/2001720 (file RJ_51-1-177.pdf, 72 KB, "Open access", accepted version, pre-copyedit). I extracted it with pdftotext and looked at pages 7-8 as images. Equation numbers below are those of this manuscript; the published version may renumber. [READ]

The abstract matches what you quoted: two BBP-type formulas, computation and verification with the two needs 20% fewer terms than verification by shifting the starting position with Huvent's formula, "known as the BBP-type formula with the least number of terms".

### (a) The two formulas

Notation (his (25), (28)): S(m,j) = sum_{k>=0} (-1)^k / ( 2^(30k) (m k + j) ). So the series are in the "base" -2^30 (alternating sign, 2^30 = 2^(4*7.5), 30 bits per step). Denominators of different lengths (12, 20, 30, 10) are mixed; the common period is 60 (lcm), so in Bailey's P(s,b,n,A) notation this would be b = -2^30, n = 60 after merging, with zero coefficients at the other positions. Takahashi keeps them separate (that is what makes the term counts what they are).

Formula (23)/(24), "first proposed formula", 6 + 15 = 21 terms per k:

pi = -2^-1 S(12,1) - 2^-6 S(12,3) + 2^-11 S(12,5) + 2^-16 S(12,7) - 2^-21 S(12,9) - 2^-26 S(12,11)
   + 2^2 S(30,1) - S(30,3) - 2^-4 S(30,5) - 2^-4 S(30,7) + 2^-6 S(30,9) - 2^-8 S(30,11) + 2^-10 S(30,13) + 2^-14 S(30,15) + 2^-14 S(30,17) - 2^-16 S(30,19) + 2^-18 S(30,21) - 2^-20 S(30,23) - 2^-24 S(30,25) - 2^-24 S(30,27) + 2^-26 S(30,29).

Origin: it is Bellard's formula (his (9)) expanded three times in k, i.e. (12) pi = 8 arctan(1/2) - 4 arctan(1/7) with arctan(1/2) expanded 15 times and arctan(1/7) from Bellard's relation (17) with a = 8, then merged. Only odd j appear. [CHECKED] error about 1e-59.

Formula (26)/(27), "second proposed formula", 1 + 10 + 15 = 26 terms per k:

pi = 2^-14 S(10,5) + S(20,1) + 2^-3 S(20,3) - 2^-6 S(20,5) - 2^-9 S(20,7) + 2^-12 S(20,9) + 2^-15 S(20,11) - 2^-18 S(20,13) - 2^-21 S(20,15) + 2^-24 S(20,17) + 2^-27 S(20,19)
   + 2^1 S(30,1) + 2^-2 S(30,3) + 2^-3 S(30,5) - 2^-5 S(30,7) - 2^-8 S(30,9) - 2^-9 S(30,11) + 2^-11 S(30,13) - 2^-13 S(30,15) + 2^-15 S(30,17) - 2^-17 S(30,19) - 2^-20 S(30,21) - 2^-21 S(30,23) + 2^-23 S(30,25) + 2^-26 S(30,27) + 2^-27 S(30,29).

Origin: from (11) pi = 4 arctan(1/2) + 4 arctan(1/3), with arctan(1/2) expanded 15 times, arctan(1/3) expanded 5 times. Takahashi notes (p. 7) that 2^-14 S(10,5) and -2^-13 S(30,15) could be merged but deliberately is not, so that an error in S(30,15) shows up as a disagreement. [CHECKED] error 0 to 59 digits.

Shared terms: the 15 series S(30,j), j odd 1..29, occur in both formulas (with different coefficients). Verification of (23) by (26) needs only S(10,5) and S(20,j), j = 1,3,...,19, i.e. 11 new series.

Also in the paper (not new): Adamchik-Wagon (7) base 4, 3 terms; his (8) = a base 4 / base 2^10 formula "requires 20% fewer terms than BBP" (from Borwein-Bailey 2003 and Adegoke-Lafont-Layeni 2011); Bellard (9) base 2^10, 7 terms, "30% fewer terms than BBP". Takahashi's own source for the two arctangent-based formulas is Machin-type two-term relations (11)-(14) and Bellard's relation (17).

### (b) Huvent's formulas and the term counts Takahashi uses

In Takahashi's manuscript (his (10), citing Huvent, "Formules BBP", web document 2001, URL http://gery.huvent.pagesperso-orange.fr/pi/huvent_seminaire.pdf; I could not open that host, certificate error) [READ]:

pi = (1/128) sum_{k>=0} 1/2^(12k) * ( 768/(24k+3) + 512/(24k+4) + 128/(24k+6) - 16/(24k+12) - 16/(24k+14) - 12/(24k+15) + 2/(24k+20) - 1/(24k+22) ).

Base 2^12, period 24, 8 terms. He says it "requires approximately 33% fewer terms than the BBP formula" (Table 1: 16n/3 total vs 8n, ratio 0.667).

Both Huvent pi formulas, from French Wikipedia "Formule BBP", section "Formules derivees" (flattened text on the page, I rewrote them; [SNIPPET]-grade reading of a garbled rendering, but both then [CHECKED] numerically to 49 digits, so the transcription is right):

H1 = H(10) above: pi = (1/128) sum 2^-12k (768/(24k+3) + 512/(24k+4) + 128/(24k+6) - 16/(24k+12) - 16/(24k+14) - 12/(24k+15) + 2/(24k+20) - 1/(24k+22)).
H2: pi = (1/256) sum 2^-12k (2048/(24k+2) - 1024/(24k+4) + 192/(24k+9) + 128/(24k+10) + 32/(24k+12) - 4/(24k+18) - 4/(24k+20) - 3/(24k+21)).

Both: base 4096, period 24, 8 nonzero coefficients. Takahashi uses only H1. Other Huvent formulas on that page are for pi^3 and pi^4 (not needed). I did not find a source stating which of H1/H2 y-cruncher uses. y-cruncher's own page says only "Huvent's BBP formula".

Term counts used by Takahashi (his Table 1; n = starting hex-digit position; one "term" = one modular-exponentiation term of a series S; lower-order tail ignored) [READ, table looked at as an image]:

| Formula | terms, computation | terms, verification | total | ratio to BBP |
|---|---|---|---|---|
| Adamchik-Wagon | 6n | 6n | 12n | 1.500 |
| BBP | 4n | 4n | 8n | 1.000 |
| Bellard | (14/5)n | (14/5)n | (28/5)n | 0.700 |
| Huvent | (8/3)n | (8/3)n | (16/3)n | 0.667 |
| Proposed (23) | (14/5)n | (14/5)n | (28/5)n | 0.700 |
| Proposed (26) | (52/15)n | (52/15)n | (104/15)n | 0.867 |
| Proposed (23)+(26) | (14/5)n | (22/15)n | (64/15)n | 0.533 |

(The pdftotext layout shifts some rows; the image shows the table above.)

### (c) The cost model, exactly

- Position n is in hexadecimal digits, so 4n bits. A formula with base 2^B needs the sum over k up to about 4n/B (terms beyond that are only tail, ignored). Each (series, k) pair is one modular-exponentiation term.
- BBP: B = 4, 4 series: 4n terms. Huvent: B = 12, 8 series: 8 * n/3 = 8n/3. Bellard: B = 10, 7 series: 7 * 2n/5 = 14n/5. Proposed (23): B = 30, 21 series: 21 * 2n/15 = 14n/5. Proposed (26): 26 series: 26 * 2n/15 = 52n/15.
- Standard verification (everyone but the pair): recompute at position n-1 or n+1 with the same formula, so cost twice: Huvent 16n/3 = 80n/15.
- The pair: compute with (23) (14n/5 = 42n/15), then verify with (26) but reuse the 15 series S(30,j) already computed, so only 11 new series: 11 * 2n/15 = 22n/15. Total 64n/15.
- 64/15 divided by 80/15 = 0.8. So "20% fewer terms" compares "(23) then (26) with shared S(30,j)" (64n/15) against "Huvent run twice" (16n/3). Without sharing, (23)+(26) would be 14/5 + 52/15 = 94/15 n, which is worse than Huvent twice. The gain is entirely from sharing.
- Measured on Intel Xeon Phi 7250, hex digit 10^11 (Table 2): Huvent 331.25 s + 331.26 s = 662.51 s; pair 353.93 s + 185.39 s = 539.32 s, ratio 0.814 ("approximately 19% less execution time"). [READ]
- Typo in the text: the sentence on p. 8 says "Huvent's formula in (7)"; it means (10).
- Caveat: a pair-based check verifies at the same position n; Huvent-shift verification checks position n-1, which also checks different series evaluations (different residues). The paper does not discuss relative detection strength beyond the remark on S(30,15).

### (d) Statements that some formula has the least number of terms

- Takahashi (abstract, intro, conclusion): Huvent's formula "is known as the BBP-type formula with the least number of terms" [READ]. No proof, no conjecture of optimality, no reference given for this claim except Huvent's own document (and Bailey's compendium for the formulas in general). In his own table, Huvent has the lowest total for single-formula verification (0.667); the pair (0.533) beats it, so "least" there means among single formulas known to him.
- No other statement found (proved or conjectured). arXiv 2208.07696 (Kristensen-Mathiasen) and arXiv 2507.20428: searched, neither mentions Takahashi, Huvent, or a minimal number of terms [SNIPPET from fetch summary; the first PDF could not be decoded by the fetcher, I did text-extract it and grep'd "takahashi|huvent|least": no hits [READ]].
- Related proved structure result (from Bailey's compendium text [READ]): Borwein, Galway, Borwein (2004): there are no degree-1 BBP-type formulas for pi except those whose base is a power of two. That restricts the base but says nothing about minimal term count.
- Bailey's compendium (2023 version) lists as binary degree-1 pi formulas only: (1) BBP base 16 period 8 (4 nonzero coefficients: 4,0,0,-2,-1,-1,0,0), (2)/(17) 1/4 P(1,16,8,(8,8,4,0,-2,-2,-1,0)) and (18) P(1,-4,4,(2,2,1,0)) (Adamchik-Wagon, Euler), (3)/(19) base -2^30 period 60 (Euler, Pschill). It does not list Huvent's pi formula or Takahashi's (the compendium has Huvent only for Catalan's constant, formula 39, and for relations 45-54).
- Question I could not settle: whether Bailey/Craig-Wood's Euler formula (3) in the compendium (base -2^30, period 60, 21 nonzero coefficients per the list: 3*2^27, 5*2^25, 3*2^26, ... ) is the same as Takahashi's (23). Plausibly yes (Takahashi's (23) is Bellard expanded three times, which gives base -2^30 and 21 terms; the compendium says (19)/(3) is "originally found by Euler" and appeared in Hardy-style sources as Pschill). From memory, unverified; I did not compare coefficients.

### y-cruncher documentation: exactly what it says

All from https://numberworld.org/y-cruncher/version_history.html and https://www.numberworld.org/y-cruncher/news/2024.html [READ via fetch summaries; short wording only]:

- v0.6.8.9458 (14 Mar 2015): BBP side project revived and integrated (digit extractor for pi). v0.7.8.9503 (27 Oct 2019): digit extractor revamped; table of offset limits for "Original Formula" and "Bellard's Formula": before v0.7.8: 2^46 both; v0.7.8 without AVX2: about 2^48 (original) and 2^49 (Bellard); with AVX2 or later: about 2^58 and 2^59. Higher offsets slower, less linear and predictable.
- v0.8.4.9537 (21 Feb 2024): "The BBP digit extractor now supports Huvent's BBP formula which is slightly faster than Bellard's."
- v0.8.5.9539 (1 Jul 2024): BBP extractor becomes a formal CPU-only benchmark; command-line options; "The default BBP algorithm has been changed to Huvent's formula."; validation files produced; slower because of ICX vs ICC compiler.
- So the documented ranking is only: Huvent slightly faster than Bellard, which is faster than the original BBP (the last by implication of the offset table, not an explicit ranking). No term counts, no numbers for Huvent's offset limit, no mention of Takahashi, of his two formulas, or of verifying with two different formulas. Pages https://numberworld.org/y-cruncher/features/bbp.html, /guides/bbp.html, /internals/bbp.html, /algorithms/pi.html, /features/custom_formulas.html all returned 404. The formulas page (internals/formulas.html) lists Huvent (2006) only for Catalan's constant (removed in v0.8.3) and pi via Chudnovsky/Ramanujan; nothing about BBP.
- Takahashi's own 100-quadrillionth-digit record page (https://www.hpcs.cs.tsukuba.ac.jp/~daisuke/pihex.html): Bellard's formula for both runs (position 10^17 and 10^17-1); no term counts. [READ]
- Takahashi's later publication list (https://www.hpcs.cs.tsukuba.ac.jp/~daisuke/pub.html): Ramanujan J. 59 (2022) 211-219 "On the use of Montgomery multiplication in the computation of binary BBP-type formulas for mathematical constants"; NUMTA 2023, LNCS 14477 (2025) "On the Division in the Computation of Binary BBP-Type Formulas for Mathematical Constants". No downloadable links on that page. I did not obtain those texts. [READ for titles]

## Gap 2: is the public Lean proof of Baker's theorem announced?

Result: no paper, no Mathlib PR, no Zulip thread, no stated upstreaming plan found. Only indirect traces on the TauCeti side. Searches were not exhaustive for Zulip (the archive search page is JavaScript; 404 on the stream search URL) and social media (not searchable by this tool).

### Branch facts [READ via GitHub API fetches]

- Branch head: 1d51891b5be7ceeca95b4583cad39e0681c5e453, 2026-09-24 22:37:56 UTC, "Split MultiIndex and SchwarzProduct into four files, all under 1000 lines". Branch not protected.
- Directory Mathlib/NumberTheory/Transcendental/Baker/ lists 19 files: AlgSize, AnalyticTsum, AuxiliaryFunction, Basic, CoordinateDivision, Criterion, CriterionMain, ExpIndep, ExpPoly, Interpolation, Liouville, MultiIndex, Polydisc, Reduction, SchneiderLang, SchwarzProduct, Setup, TaylorCoeff, ThueSiegel. No README in that directory (the repo README is upstream's).
- lean-toolchain on branch baker: `leanprover/lean4:v4.35.0-rc2`.
- Base: `compare/master...mkaratarakis:baker` on leanprover-community/mathlib4: diverged, 76 commits ahead, 1475 behind upstream master at fetch time; merge base a0e130082e752dfb35cd7d3b9b95f1854fd78d92, 2026-09-23 15:35:41 UTC, message "doc(Algebra/Polynomial/Div): delete extra space (#44128)". (Comparing against the fork's own stale master instead gives merge base d72a3c31... of 2026-02-03 and 6856 commits, which is not informative.)
- Commit log (API, per_page=30 and page 2; all by Michail Karatarakis, all dated 2026-09-24 UTC in what I saw; I saw 59 of the 76 commits, from 09:35:07 to 22:37:56; the 17 oldest, between the merge base and 09:35, I did not retrieve):
  - 15:29:18 "Keep everything under Transcendental/Baker" (body: reverts House.lean and SiegelsLemma.lean to upstream; additions live in Baker/Liouville.lean and Baker/ThueSiegel.lean)
  - 15:33:09 "Lemma 4.12: Thue-Siegel for complex forms" (body: real and imaginary parts give 2*card k real forms; the sqrt 2 is the cost of recombining)
  - 15:55 "Lemma 4.13: truncated Taylor interpolation"; 16:01 "Cauchy's inequality on a polydisc"; 16:11 "Prop 4.10: the auxiliary function"; 16:28-16:42 Newton division / uniqueness of the Newton main term; 16:55-16:56 "Prop 4.7: Schwarz's lemma for Cartesian products", "Prop 4.7 for R >= 5r"; 17:03-17:35 series products, Lemma 4.9, exponential polynomials independent, Liouville for algebraic numbers, Taylor coefficients; 17:39 "The auxiliary function is not zero; linear changes of variables"; 17:46 "The transcendence argument, parameters as hypotheses"; 17:51 "Corollary 4.2 from the core, modulo the choice of parameters"; 17:58-18:22 Liouville factor, extrapolation inequality, vanishing inequality, conditions of Prop 4.10 for large q;
  - 18:25:30 "Choose the parameters: Baker's theorem is proved"
  - 18:30:45 "Docs: the proof is complete; note on the change of variables"
  - 22:37:56 the file split above.
  - Earlier that day (09:35-15:23): "Drop a duplicate: use Pi.norm_single", "Division by a coordinate, and clear the linter warnings", "Write down what's left of Chapter 4, next to the sorry" (10:04), "Zero warnings across the tree" (12:27), "Lemma 4.8 (a): vanishing kills the coefficients", "Pin down the one computation part (b) still needs" (14:15), ... "Liouville's inequality" (15:19), "Thue-Siegel over arbitrary index types" (15:23).
  - Reading: the lemma/proposition numbers (4.7, 4.8, 4.9, 4.10, 4.12, 4.13, Corollary 4.2) follow a textbook chapter 4 (the TauCeti roadmap says Waldschmidt, Ch. 4). The log shows a `sorry` remaining until about 10:04 and then discharged over roughly nine hours; commit messages say nothing about who or what wrote the code.

### Announcements and discussion found

- arXiv: author search for Karatarakis returns four papers: 2603.24823 "A formalization of the Gelfond-Schneider theorem" (Karatarakis, Wiedijk, 25 Mar 2026; abstract only mentions Hilbert's seventh problem; no Baker content visible), two monogenity papers with Sumandeep Kaur (29-30 Sep 2026), and the 2025 Hopfield paper. Author search for Wiedijk: nothing after March 2026. Keyword searches (Baker + formalization/Lean/Lean 4; "linear forms in logarithms" + Lean/formalization) for Sept-Nov 2026: no relevant entries. [READ, API results]
- Mathlib PRs: `repo:leanprover-community/mathlib4 Baker transcendental` and `... Schneider-Lang`: total_count 0 each. Author mkaratarakis has 70 issues/PRs in Mathlib; the relevant one is #42911 "feat(NumberTheory): the Gelfond-Schneider theorem (Hilbert's seventh problem)", open since 2026-08-18, no reviews; its description does not mention Baker's theorem, a baker branch or AI; says `#print axioms` shows only propext, Classical.choice, Quot.sound; commit messages credit Cursor as co-author (fetch summary, [SNIPPET]). It depends on #35744.
- TauCeti side (GitHub search `Baker transcendence Karatarakis` found 5 items):
  - TauCetiProject/TauCetiRoadmap PR #451 "Add roadmap: linear forms in logarithms, Baker's theorem over C and C_p", opened by mkaratarakis 2026-09-26, merged (by a review bot) in November. The description (via fetch summary, [SNIPPET]) gives provenance: complex part = `mkaratarakis/mathlib4` branch `baker` at commit 1d51891b5b (the current head); p-adic part = branch `baker-padic` at 65cdef5722. It says most of the material is already formalised without sorry. The author states Claude (Opus 5.5 in Claude Code) was used to draft the roadmap text and Suggested.lean, help with the Lean formalisation, check citations against Waldschmidt and Baker, and run review rubrics. Reviews labelled AI-assisted by several models.
  - TauCeti PR #42369 (open, 2026-11-15, by account tauceti-ai-for-science, "Prepared with Claude Code"): Liouville's inequality and Schwarz's lemma at an ultrametric place; says "a parallel formalisation exists in Karatarakis's Mathlib fork", cites it but copies no code. Also TauCeti PRs #41040, #41378, #41683 (merged; Cauchy inequalities on polydiscs, exponential polynomials, multi-index Taylor coefficients) overlap in content with the Baker/ files (separate authorship, by chrisflav).
  - Roadmap file STATUS.md (generated, snapshot 2026-11-19, commit b2350004c4): says polydisc estimates, auxiliary function, Schneider-Lang criterion, Baker's theorem "have not begun" in the Tau Ceti tree, while the Thue-Siegel lemma (3.4) and a branch-free Gelfond-Schneider are done. This refers to Tau Ceti's own formalisation, not the fork, so there is no contradiction about the fork, but the roadmap does not treat the fork's proof as available inside Tau Ceti.
  - "Coordination with Mathlib" section of the roadmap README: plans to adopt Mathlib's Gelfond-Schneider (#42911) and Lindemann-Weierstrass statements and drop duplicates; it states no plan to upstream the Baker files.
- Zulip: a search result points to a Nov 2025 thread "Gelfond-Schneider theorem" in the maths stream (https://leanprover-community.github.io/archive/stream/116395-maths/topic/Gelfond-Schneider.20theorem.html) [SNIPPET]; nothing on Baker found. Conference pages (CPP 2027, ITP, CICM), blogs, social media: not found via the searches done.
- How produced/checked: the only statements are (i) author's PR #451 text above (Claude Opus 5.5 assisted), (ii) `#print axioms` remark on #42911 for Gelfond-Schneider (not for Baker). No statement on how the branch was built or that it compiles under a given CI; branch has no CI badge info retrievable. I did not build anything.

## Gap 3: binary BBP-type formulas for pi times a square root

Compendium notation (Bailey, April 8 2023 version, which I text-extracted and viewed as an image, page 9) [READ]: P(s,b,n,A) = sum_{k>=0} 1/b^k sum_{j=1..n} a_j/(kn+j)^s.

| Constant | Formula | Base, period | Source (as stated) |
|---|---|---|---|
| pi*sqrt2 | (1/8) P(1, 64, 12, (32,0,8,0,8,0,-4,0,-1,0,-1,0)) [CHECKED] | 2^6, 12 | compendium formula 20; "appeared in [14]" = BBP 1997 paper |
| pi*sqrt2 | sum 1/(-8)^k (4/(6k+1) + 1/(6k+3) + 1/(6k+5)) [CHECKED] | -8 (2^3, alternating), 6 | MathWorld "BBP-Type Formula" eq. (17), not attributed [SNIPPET of fetch; I verified numerically] |
| pi*sqrt3 | (9/32) P(1, 64, 6, (16,8,0,-2,-1,0)) [CHECKED] | 2^6, 6 | compendium formula 21, attributed to Knuth, TAOCP vol 2 p. 628 |
| pi*sqrt3 | (1/4) sum 1/64^k (20/(6k+1) + 6/(6k+2) - 1/(6k+3) - 3/(6k+4) - 1/(6k+5)) [CHECKED] | 2^6, 6 | MathWorld eq. (23), not attributed |
| pi*sqrt3 | (9/2^12) P(1, 2^12, 24, (2^11,0,0,2^10,2^9,0,2^8,2^8,0,0,2^6,0,-2^5,0,0,-2^4,-2^3,0,-2^2,-2^2,0,0,-1,0)) [CHECKED, constant 9/2^12 confirmed numerically] | 2^12, 24 | Adegoke-Lafont-Layeni, arXiv 1603.07395, eq. (6.4)-(6.5) (derived from a general base-2^(12p) family, p = 1) |
| pi/sqrt3 | = (1/3) * (pi*sqrt3); e.g. (3/32) P(1,64,6,(16,8,0,-2,-1,0)) | 2^6, 6 | derived by me, trivial rational multiple; no separate source found |
| pi*sqrt5 | (5/2^19) P(1, 2^20, 40, (2^19, 2^19, -2^18, 0, 0, 2^17, 2^16, 0, 2^15, 0, 2^14, 0, 2^13, 2^13, 0, 0, -2^11, 2^11, 2^10, 0, -2^9, -2^9, 2^8, 0, 0, -2^7, -2^6, 0, -2^5, 0, -2^4, 0, -2^3, -2^3, 0, 0, 2, -2, -1, 0)) | 2^20, 40 | compendium formula 22, attributed to Adegoke ("A Binary BBP-type Formula for pi*sqrt5", manuscript 2013, adegoke.atwebpages.com/bbp-type/pi_root5.pdf; host had a certificate error, not read). The coefficient list is read off the page image; I did NOT numerically check this one. |

Related constants in the same compendium (page 9) [READ], arctangents of golden-ratio powers (phi = (1+sqrt5)/2), Adegoke 2013 manuscripts and arXiv 1603.06307: arctan phi = (1/16) P(1,16,8,(8,16,4,0,-2,-4,-1,0)); arctan phi^3 = (1/8) P(1,16,8,(8,4,4,0,-2,-1,-1,0)); arctan phi^5 = (1/16) P(1,16,8,(8,32,4,0,-2,-8,-1,0)); arctan phi^7 = (3/2^12) P(1, 2^12, 24, (...)). Also sqrt2 log(1+sqrt2) = (1/8) P(1,16,8,(8,0,4,0,2,0,1,0)) and sqrt2 arctan(1/sqrt2) = (1/8) P(1,16,8,(8,0,-4,0,2,0,-1,0)) (Knuth). Section 13 of the compendium: two formulas that are not true BBP (irrational base 2/phi, and a Lucas-sequence-coefficient formula for arctan-type constant), from Bailey-Crandall 2001.

On "pi times 2cos(pi/10) or tan(pi/10)":
- phi = 2cos(pi/5), so 2cos(pi/10) is the other golden-field element sqrt((5+sqrt5)/2) of degree 4; tan(pi/10) is also in the degree-4 field Q(sqrt(5-2sqrt5)). I found no BBP-type formula (binary or otherwise) in the compendium, MathWorld, Adegoke's arXiv papers I opened, or Chan's work for pi * 2cos(pi/10), pi * 2cos(3pi/10), or tan(pi/10)-type multiples. The compendium contains only the arctan(phi^k) family above (arctangents, not pi times an algebraic number) plus pi*sqrt5. Nothing found does not prove nonexistence; my selection of papers was limited (Adegoke's FQ papers and his 2013 manuscripts not opened).
- Chan (Fibonacci Quarterly 44 (2006) 141-144, "pi in terms of phi"), Zhang (JMAA 398 (2013)), Bailey-Crandall: formulas in the irrational base phi or related; Adegoke notes these are not BBP in the digit-extraction sense because phi is not an integer (arXiv 1603.06307 section 5.3, [READ]). Adegoke's phi-base formula (5.23) for a constant I could not identify from the extracted text; not used.
- Comparison with your five series (periods 24, 12, 40, 40, 40): published periods are pi*sqrt3 (and pi/sqrt3): 6 base 2^6 (or 24 base 2^12 in Adegoke et al.), your period 24 is that scale; pi*sqrt2: published 12 base 2^6 (or 6 base -8), your 12 matches the compendium's; pi*sqrt5: published period 40 base 2^20, your 40 matches. So the first three of your series have published counterparts; the two involving 2cos(pi/10) and 2cos(3pi/10) (period 40) have none that I found.

## Gap 4: the Bilu-Luca 2026 preprint

Found. arXiv:2607.28857v1 [math.NT], submitted 30 July 2026 (PDF dated August 3, 2026), Yuri Bilu and Florian Luca, "Multiplicative dependence in the sumset of multiplicative groups". DOI 10.48550/arXiv.2607.28857. [READ, abstract page and full PDF text]

Abstract (paraphrase): Gamma and Delta finitely generated multiplicative groups of algebraic numbers with Gamma intersect Delta finite ("almost disjoint"). Up to finitely many exceptions, nonzero sums x1+y1 and x2+y2 (x_i in Gamma, y_i in Delta) are multiplicatively dependent only if x1/x2 = y1/y2 is a root of unity. For m >= 3 the possible shapes of m dependent sums are discussed; for m = 3 they are classified, up to finitely many exceptions, assuming the abc conjecture.

Main results [READ]:
- Theorem 1.1: only finitely many (x,y) in Gamma x Delta with x+y a root of unity (classical binary unit equation, Baker; effective). No almost-disjointness needed.
- Theorem 1.2 (m = 2): as in the abstract; non-effective in general, effective when both groups have rank 1 (Remark 6.1). Almost disjointness cannot be dropped (Example 1.3: <-1,3> + <2,3> contains all powers of 3).
- Theorem 1.5 (m = 3, assuming the weak abc Conjecture 3.9 in K): apart from finitely many exceptions, up to permutation and roots-of-unity factors, either (x1,x2,x3) = (x, zeta2 x, zeta3 x^2) with (y1,y2,y3) = (-y, zeta2 y, -zeta3 y^2) ["x - y, x + y, x^2 - y^2" family, (1.1)] or x3 = zeta x2^-1, y3 = zeta y2^-1 with x1+y1 and x2 y2 multiplicatively dependent ["(1.2)" family].
- Canonical m-pairs (1.7): if Gamma contains a primitive (m-1)-th root of unity zeta and x^(m-1) = y^(m-1), then x - y, x - zeta y, ..., x - zeta^(m-2) y, x^(m-1) - y^(m-1) are multiplicatively dependent (the cyclotomic product relation). Conjecture 1.6 says that every minimally multiplicatively dependent m-tuple is, up to torsion-equivalence and finitely many exceptions, canonical or a concatenation of twisted pairs; proved for m = 2 (Thm 1.2), for m = 3 under abc (Thm 1.5). Section 7 ("technical heart") studies x-1, y-1, z-1 dependent modulo a group (Theorem 7.3), using gcd and primitive-divisor arguments.
- Preface (by Bilu): "Mu coauthor and friend Florian Luca died suddenly during the final preparation of this manuscript." Disclaimer: "No AI tool was used in preparing this article." Acknowledgment: David Masser.

Does it concern 1 - zeta*alpha or alpha - zeta? Not as a stated problem. Sums x + y with x in a finitely generated Gamma and y in Delta; alpha - zeta is of this shape only with Gamma = <alpha> and Delta = <-1, zeta> for a FIXED finitely generated group of roots of unity (a finite group, so only roots of unity of bounded order). The theorem then gives: for two such differences alpha - zeta1, alpha - zeta2 (x1 = x2 = alpha; y1/y2 = zeta1/zeta2), dependence forces x1/x2 = 1 = y1/y2, so zeta1 = zeta2, with finitely many exceptions, but the finite exception set is not uniform over larger and larger Delta, and ranging over all roots of unity makes Delta not finitely generated. So it does not give your core lemma for zeta over all roots of unity. Their canonical family (1.7) is the relation that always exists: prod over n-th roots zeta of (alpha - zeta) = alpha^n - 1, which is the obvious dependence among alpha - zeta's your lemma has to exclude or account for. Nothing in the text directly treats alpha = 1 + i. (From grep of the extracted text; I read the introduction and the plan fully, not every proof.)

Other arXiv results (API search `all:"multiplicative relations" AND all:"roots of unity"` returned 0 entries; broader `all:"roots of unity" AND all:"multiplicatively dependent"` returned 3):
- Bilu-Luca 2607.28857 above.
- Ostafe, Sha, Shparlinski, Zannier, "On abelian multiplicatively dependent points on a curve in a torus", arXiv 1704.04694 (2017): points on curves whose coordinates are multiplicatively dependent are, up to finitely many, preimages of roots of unity under characters. [SNIPPET]
- C. Magagna, math/0610277: matrices, not relevant.
- Web search (not arXiv): Drungilas-Dubickas, "Multiplicative dependence of two integers shifted by a root of unity", Proc. AMS 147 (2019): for integers m > n and k >= 3, m - zeta_k and n - zeta_k are multiplicatively independent except (n,k) = (1,6); Madritsch-Ziegler (arXiv 1408.3991): -m + zeta_k and -n + zeta_k independent for m > n > C(k). [SNIPPET] These are results with alpha varying over integers and zeta fixed order, not alpha fixed and zeta over roots of unity.
- Not found: a theorem of the form "for fixed algebraic alpha (not a root of unity) the multiplicative relations among alpha - zeta, zeta in mu_infinity, are exactly those generated by the cyclotomic product relations". From memory, unverified: classical results on relations among 1 - zeta (Ramachandra-Bass: the multiplicative relations among cyclotomic units 1 - zeta_n^a are generated by distribution relations and 1 - zeta = -zeta(1 - zeta^-1)); this is the alpha = 1 case, so Bilu-Luca-type statements for general alpha would be the generalisation.

## Queries used (WebSearch, 12 of 18)

1. Takahashi "BBP-type formulas" pi computation verification two formulas Huvent least number of terms
2. y-cruncher BBP-type formula Huvent pi hexadecimal digits verification
3. Takahashi computation of the 100 quadrillionth hexadecimal digit of pi Parallel Computing BBP formula
4. Daisuke Takahashi Huvent BBP-type formula pi 2025 Montgomery multiplication division hexadecimal digits
5. Takahashi "On the use of Montgomery multiplication in the computation of binary BBP-type formulas for mathematical constants"
6. Huvent BBP formula pi base 2^12 or 2^20 fewest terms "Huvent" pi formula hexadecimal
7. Gery Huvent "Formules BBP" pi
8. y-cruncher BBP digit extractor "Bellard" "Huvent" formula table speed offset limit (allowed domain numberworld.org)
9. multiplicative relations among algebraic numbers alpha minus root of unity multiplicatively dependent 1 - zeta alpha cyclotomic units generalization
10. Adegoke "BBP-type formula" "pi sqrt 5" binary golden ratio arctangent tan(pi/10) OR cos(pi/10) digit extraction
11. Karatarakis Baker's theorem linear forms in logarithms Lean 4 Mathlib formalization
12. leanprover Zulip Baker's theorem transcendence formalized Schneider-Lang Mathlib 2026

## Pages fetched (WebFetch, most important)

GitHub API: mkaratarakis/mathlib4 commits?sha=baker (pages 1, 2), compare/master...baker, branches/baker, raw lean-toolchain on baker; leanprover-community/mathlib4 compare (two variants), search/issues (Baker transcendental; Schneider-Lang; author:mkaratarakis; Baker transcendence Karatarakis); github.com mkaratarakis/mathlib4 tree/baker (and Baker dir); mathlib4 PR 42911; TauCetiRoadmap PR 451, LinearFormsInLogarithms dir and STATUS.md raw; TauCeti PR 42369.
arXiv: API queries (multiplicative relations + roots of unity; roots of unity + multiplicatively dependent; au:Karatarakis; au:Wiedijk; au:Bilu+au:Luca; Baker + formalization; linear forms in logarithms + Lean), abs/2603.24823, abs/2607.28857, pdf/2607.28857 (text-extracted), pdf/2208.07696 (text-extracted, grep), pdf/1603.07395 and 1603.06307 (text-extracted), html/2507.20428v1.
Takahashi: tsukuba.repo.nii.ac.jp/records/2001720 and the repository PDF (via a signed storage redirect from the same repository; read-only, text-extracted), api.crossref.org (reference list), api.openalex.org (OA locations), hpcs.cs.tsukuba.ac.jp/~daisuke/ (index, pihex.html, pub.html), Wikipedia (Daisuke Takahashi; Bellard's formula), Springer link (paywalled, redirect not followed), johndcook.com blog.
y-cruncher: numberworld.org version_history.html (pages 0-100000 and 100000+), news/2024.html, internals/formulas.html, index; several 404 pages.
BBP data: davidhbailey.com/dhbpapers/bbp-formulas.pdf (text-extracted and page 9 viewed as image), bbp-alg.pdf (not decoded), fr.wikipedia.org Formule BBP, mathworld BBP-TypeFormula (twice). Failed/unreadable: ams.org BBP 1997 PDF (403), adegoke.atwebpages.com (certificate), gery.huvent.pagesperso-orange.fr (certificate), mdpi (403), semanticscholar API (404), bvbvf1.bib-bvb.de (DNS).

## Sources

- Takahashi 2020 accepted manuscript: https://tsukuba.repo.nii.ac.jp/records/2001720 ; published: https://doi.org/10.1007/s11139-018-0104-x ; Crossref reference list: https://api.crossref.org/works/10.1007/s11139-018-0104-x
- Takahashi pages: https://www.hpcs.cs.tsukuba.ac.jp/~daisuke/pihex.html , https://www.hpcs.cs.tsukuba.ac.jp/~daisuke/pub.html
- Huvent formulas: https://fr.wikipedia.org/wiki/Formule_BBP (Huvent's own: "Formules BBP" 2001, not read)
- Bellard: https://en.wikipedia.org/wiki/Bellard%27s_formula
- y-cruncher: https://numberworld.org/y-cruncher/version_history.html , https://www.numberworld.org/y-cruncher/news/2024.html , https://www.numberworld.org/y-cruncher/internals/formulas.html
- Bailey compendium: https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf (April 8, 2023 version)
- MathWorld: https://mathworld.wolfram.com/BBP-TypeFormula.html
- Adegoke, Lafont, Layeni: https://arxiv.org/abs/1603.07395 ; Adegoke golden ratio: https://arxiv.org/abs/1603.06307
- Kristensen-Mathiasen: https://arxiv.org/abs/2208.07696
- Baker branch: https://github.com/mkaratarakis/mathlib4/tree/baker ; API https://api.github.com/repos/mkaratarakis/mathlib4/commits?sha=baker ; https://api.github.com/repos/leanprover-community/mathlib4/compare/master...mkaratarakis:baker
- Mathlib PR: https://github.com/leanprover-community/mathlib4/pull/42911
- TauCeti: https://github.com/TauCetiProject/TauCetiRoadmap/pull/451 , https://github.com/TauCetiProject/TauCeti/pull/42369
- Karatarakis-Wiedijk: https://arxiv.org/abs/2603.24823
- Bilu-Luca: https://arxiv.org/abs/2607.28857
- Drungilas-Dubickas: https://www.ams.org/proc/2019-147-02/S0002-9939-2018-14136-2/ ; Madritsch-Ziegler: https://arxiv.org/abs/1408.3991 ; Ostafe-Sha-Shparlinski-Zannier: https://arxiv.org/abs/1704.04694
