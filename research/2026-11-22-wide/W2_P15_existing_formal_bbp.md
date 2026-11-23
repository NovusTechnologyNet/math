# W2-P15: existing formal work on BBP-type formulas (read at the source)

Marks: [READ] read on the source's own page/file (through the fetch tool, which summarizes
pages with a small model, so details are second-hand to that extent); [SNIPPET] search result
or API record only; [INFERRED] my conclusion. Nothing was run or downloaded. No code copied.

## 1. Summary

1. The public Lean repo exists: github.com/metasecdev/math-proofs (author given as Brian
   Bernard Taylor, sole author, 0 stars/forks, Apache-2.0, created 2026-10-31, public since
   2026-11-01, last push 2026-11-16, 50 commits, 20 self-merged PRs, 77 CI runs, latest ones green).
2. What it proves (Lean 4, pinned Mathlib commit, toolchain v4.29.0-rc8): the BBP base-16
   series for pi equals Real.pi (analytic proof, integral + FTC); a soundness theorem for an
   integer "guarded" hex-digit certificate; a unconditional guard depth for EVERY position n
   via an explicit irrationality measure for 16^k*pi (exponent 570, constant 2^-7182802,
   proved in-repo by Mahler's method, not imported); structure results on runs of 0/F digits.
   It is only about the ONE base-16 formula for pi. No Bellard, Huvent, other BBP formulas,
   no classification, no optimality, no other bases of BBP type.
3. Trust: CI gate checks that headline theorems use only the 3 standard axioms and greps for
   sorry/admit/native_decide/axiom. One file I read (BBPConditionalAllN) is explicitly
   conditional on an unproved hypothesis (PiEffectiveMeasure), but it is excluded from the
   default build and the headline theorem is a different, unconditional file. Heavy
   certificates (n<=10000) were checked only on the author's laptop. No external review:
   PRs have zero comments; arXiv submission stalled for lack of an endorser (Bailey declined,
   Zudilin asked 1 Nov, no reply as of 13 Nov).
4. Earlier formal work on BBP: (a) HOL Light has a BBP formalization (Harrison, 2010, per
   Bertot et al.); (b) Coq: Bertot-Rideau-Thery 2017/2018 prove the BBP identity AND a
   partially correct digit-extraction algorithm; (c) Lean: Braams's lean-DLMF (Oct-Nov 2026)
   has hasSum_bbp_pi and several other proved BBP-type series, see below.
5. Surprise: lean-DLMF (bjbraams) DLMF/Constants/BBP.lean proves, with no sorry, BBP for pi
   plus log 3, log 2, and BBP-type series for 4 log 5 (base 16) and (8/3) log 3 (base 64),
   and Gauss's Machin-like formula. A second file (BBPFamily) states a general theory for
   arbitrary radix with all three theorems left as sorry.
6. Mathlib has: irrational_pi, Leibniz series (Real.tendsto_sum_pi_div_four), a Chudnovsky
   file that only DEFINES the sum (statement only, proof wanted; PR 29170 statement only).
   No BBP in Mathlib that I could find. Isabelle AFP: Pi_Transcendental, E_Transcendental
   (Eberl), Pi_Irrational (Niven); I found no BBP entry in AFP.
7. Conclusion: "the BBP formula proved in Lean" is NOT new (metasecdev, Braams both earlier
   than the project's date; HOL Light and Coq did it years ago). What the project can still
   claim is in section 5.

## 2. Q1: metasecdev/math-proofs, in detail

Facts from the API and raw files.
- [READ] Description: Lean 4 project formalizing the BBP formula for pi with verified
  hex-digit extraction and an irrationality measure at denominators 16^n. Created
  2026-10-31T22:33Z, pushed 2026-11-16T13:59Z, default branch main, size ~1.4 MB, Apache-2.0
  (paper CC BY 4.0), archived on Zenodo with v1.0.1 DOI (I searched Zenodo for the title words
  and for the account name; the Zenodo API returned nothing relevant, so the record itself
  was not read).
- [READ] Commit history: first commits 2026-10-31/11-01 are "Import ..." from the author's
  private development repos ("irrational-gap-mobius" is named in the lakefile as the source
  of heavy certificates). So the development predates the repo; actual work dates unknown.
  Commit messages show no AI trailers, but the paper's acknowledgements disclose AI
  assistants (named "Grok Bot") used for drafting Lean proofs, computations, editing.
- [READ] lakefile: package math_proofs; Mathlib pinned to commit 816ff4582a01..., Lean
  toolchain leanprover/lean4:v4.29.0-rc8 (a release candidate); autoImplicit false;
  default target library Thoughts; non-default library BBPHeavyCerts (needs >10 GB RAM per
  process).
- [READ] CI (ci.yml): ubuntu, lake build, then `lake env lean Thoughts/Axioms.lean`, then
  scripts/check_axioms.py. The script fails if any axiom outside propext, Classical.choice,
  Quot.sound appears in the printed axiom lists, if the logs show "declaration uses sorry"
  or errors, and if any .lean file (comments and strings stripped) contains sorry, admit,
  native_decide, an `axiom` declaration at line start, implemented_by or extern. Weakness
  (as the script is written): attribute-prefixed `axiom` declarations would slip through the
  source scan, but the log check on `#print axioms` would still catch their use in the
  checked theorems. Runs 45-48 (Nov 13-16) all "success" [READ, API; 8 of 77 runs seen].
  Thoughts/Axioms.lean runs #print axioms on ~50 headline theorems incl. the BBP identity.
- Sorry/axiom: [INFERRED] the headline files contain none (README and paper claim none; CI
  gate enforces it on the default target). I did not read all ~150 files. Of those I read
  (BBPPiIdentity, MahlerSharp7b, BBPBaseQ, BBPConditionalAllN) I saw no sorry. Caveat: the
  fetch tool paraphrases files, so a literal grep was not possible.
- README main-results table (Lean names in namespace BBPPi / FinitistProved), described:
  * bbpSeries_eq_pi: sum_k 16^-k (4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6)) = Real.pi.
    Proof [READ]: term-by-term integral over [0,1] of (x^8/16)^k (4 - 2x^3 - x^4 - x^5),
    dominated convergence, closed form kernel p(x)/(1 - x^8/16), antiderivative with logs
    and arctan, FTC. (Same overall idea as Bertot et al. and lean-DLMF; classical.)
  * Certificate soundness (BBPGuardAgreesAt.floor_pi, .digit_pi): integer lower and upper
    approximations of 16^n*pi built from the series with a tail guard; if they have the same
    floor, then it is floor(16^n pi) and the residue mod 16 is the n-th hex digit.
  * Existence of an agreeing guard for every n (exists_guard_floor_digit_eq).
  * pi_pow16_irrationality_measure (MahlerSharp7b): for all k>=1 and integers p,
    |16^k pi - p| * 16^(570k) > 2^(-7182802) * 16^k. Proof by Mahler's method (auxiliary
    polynomial/Pade-type construction at i*pi/2, lcm(1..n) <= exp(1.4063 n + 8760) Chebyshev
    bound, parameter m=141). Paper says proved in-repo, not imported. This is a weak
    measure (known best ~7.1 by Zeilberger-Zudilin), chosen to be fully explicit.
  * Theorem 6.1: guard depth >= 569n + floor(log16(n+1)) + 1 + 1795710 certifies the floor
    and digit; simplified: depth >= 570n + 1795711 (also a variant with exponent 658,
    constant 430009). Therefore: the correctness of the digit-extraction certificate for ALL
    n, at an explicit (impractically large) precision.
  * PiDigitStructure: forced structure of runs of 0 and F, a kernel-checked finite fact
    (run(77)=0, gap(78)=49), relations between distance to nearest integer and needed guard.
  * Appendix: the "capped" certificate (fixed small cap on guard) gives a WRONG digit in a
    stated window near n ~ 2^272 (proved), correct for n<=2000 (CI) and n<=10000 (laptop).
  * BBPBaseQ: for every base q>=2, any A within a small relative distance of q^n*pi has the
    right floor and base-q digit; uses the weak measure (mu=658); not a BBP spigot for
    non-powers of 2 (header says so).
  * BBPConditionalAllN: guard depths conditional on an hypothesis PiEffectiveMeasure /
    PiPow16Measure (research file, outside default build).
- External review [READ, API]: all 20 PRs by the owner, merged by the owner, 0 comments.
  No issues from others. PLAN.md: arXiv math.NT (cs.LO cross-list) blocked on endorsement;
  Bailey declined (does not submit to arXiv), Zudilin asked on 1 Nov 2026. A "plain-language
  overview (Medium)" is linked. No journal. [INFERRED] Not peer reviewed; the only
  verification is the Lean kernel, CI, and the author's own local build.
- Self-stated limits [READ, paper main.tex]: no normality claims; guard depths far above
  minimal; the capped certificate is unproven for 10001 <= n < ~2^272; n<=10000 result not
  in CI; "gap" statements carry unproven hypotheses for general positions.
- The paper's related work [READ] cites Bertot-Rideau-Thery (Coq), says HOL Light has a
  BBP formalization, cites Braams's lean-DLMF for a Lean BBP identity, and says it does not
  claim priority for the identity. It mentions Eberl's Isabelle pi transcendence and Mathlib's
  irrationality of pi, and a "Prove2Me" site with irrationality-measure goals.
- [INFERRED] The repo covers only the base-16 pi formula. It contains no Bellard (base 1024),
  Huvent, log, arctan, or other BBP-type formulas, no zero relations, no classification, no
  optimality statement (file names and README table checked; no such name appears).

## 3. Q2: other formalizations mentioning BBP etc.

GitHub repository search (unauthenticated API, limited; code search returns 403, several
queries returned zero hits or 429):
- Query "Bailey-Borwein-Plouffe": 35 repos, all those visible (19) are implementations
  (JS, Python, C++, Rust, Julia, Haskell, Ada, ...). None formal. [READ]
- "BBP pi language:Lean": only metasecdev/math-proofs. "Bellard formula pi": 6 implementations,
  no formal ones. "lean-dlmf": bjbraams/lean-DLMF (and an index repo and an erf repo).
- Zero results for Coq/Isabelle/HOL Light/Chudnovsky/Machin queries on GitHub (queries
  were awkward, so [weak evidence] only).

Found formalizations:
1. bjbraams/lean-DLMF (Lean 4 + Mathlib; Bastiaan J Braams; Apache-2.0; renamed from
   an earlier project 2026-10-21; pushed 2026-11-20; ~1,058 admitted statements on 2026-11-03,
   820 by Nov 13, so a library with many sorries overall) [READ].
   - DLMF/Constants/BBP.lean (title: BBP-type formulas and Gauss's Machin formula; cites
     Duverney, An Introduction to Hypergeometric Functions, sec 8.4): proved, no sorry, no
     axiom: lemma hasSum_pow_div_mul_add (sum a^k/(mk+j) = integral of y^(j-1)/(1 - a y^m));
     HasSum statements: hasSum_bbp_pi (BBP base 16 for pi, denominators 8k+1,4,5,6);
     log 3 = sum (1/4)^k/(2k+1); sum (1/9)^k/(2k+1) = (3/2) log 2; 4 log 5 as a base-16
     series with denominators 4k+1,2,3; (8/3) log 3 as a base-64 series with denominators
     6k+2,3,4; and gauss_machin: 12 arctan(1/18) + 8 arctan(1/57) - 5 arctan(1/239) = pi/4.
     It does not mention the Compendium, Bellard or Huvent. I did not see commit dates (API 403),
     but the repo/ file copyright is 2026 and the metasecdev paper says the theorem was
     published online in October 2026.
   - DLMF/Constants/BBPFamily.lean: general definition bbpSeries for an integer radix a,
     length h, order n, complex coefficients; three theorems (summability, unit-interval
     integral representation, polylog root-of-unity evaluation) all stated with sorry. General
     theory, no specific named formula instantiated.
   - Bailey.lean there is about Bailey pairs (q-series), unrelated.
2. HOL Light: a BBP formalization exists in the HOL Light library [SNIPPET, from Bertot et
   al.'s related-work section, which I read on ar5iv: it attributes it to Harrison, 2010, and
   says their contribution is to link the statement to the algorithm]. I could not find the
   file (repository code search needs login; the tree API returned 403; the Multivariate
   transcendentals.ml visible part had no BBP). So its exact statement is NOT verified by me.
   Probably the identity as a real series [INFERRED].
3. Coq: Bertot-Rideau-Thery (below); Bertot-Allais, Coq study of pi formulas including
   Leibniz-type series and Machin's 1706 equality [SNIPPET].
4. Isabelle: Machin-like formulas in the HOL basic transcendental theory [SNIPPET via Bertot
   et al.]; HOL-Analysis-ex Approximations (numerical bounds, a distribution example)
   [SNIPPET]. No BBP found.
5. Mathlib [READ on raw files]: irrational_pi (B. Mehta, 2022); Real.tendsto_sum_pi_div_four
   (Leibniz); Mathlib/Analysis/Real/Pi/Chudnovsky.lean (K. Morrison, 2025): definitions of
   the terms and of the sum only, theorem not proved ("proof wanted"); PR 29170 "statement
   only of Chudnovsky's formula for pi". PR 43920 (Sep 2026) tidied it. No BBP issue or PR
   found (search for BBP in mathlib4 issues: 0 hits).
6. Lean 4 transcendence of pi: samuelborza/IsTranscendentalPi (Niven's proof, Reservoir,
   updated Apr 2026) [READ]. Not about BBP.
7. Spigot/Machin/Chudnovsky/"pi_digits" repository searches: only programs, no formal ones.

## 4. Q3: Bertot, Rideau, Thery, "Distant decimals of pi"

Source: J. Automated Reasoning 61 (2018) 33-71, DOI 10.1007/s10817-017-9444-2 (Crossref
record read); arXiv 1709.01743, read in HTML (ar5iv). Springer and HAL were blocked (Anubis).
- [READ] The BBP identity pi = sum 16^-i (4/(8i+1) - 2/(8i+4) - 1/(8i+5) - 1/(8i+6)) is
  proved in Coq (with Coquelicot: power series, integrals, uniform convergence of derivatives).
  Proof outline: S_k = sum 1/(16^i (8i+k)) written as integral of x^(k-1)/(1-x^8) over
  [0, 1/sqrt 2], combined, substitution, antiderivatives, giving -4 arctan(-1).
  Lemma names: Sk_Rint, RInt_PSeries, fill_holes, PSeries_hole, PS_cv, RInt_comp_lin,
  RInt_Spart1-3.
- [READ] Digit extraction: to get digit d, scale by 16^(d-1) 2^p, use modular integer
  arithmetic; error bound delta = d + p/4 + 1; NpiDigit produces lower and upper
  approximations (Y, Y+8 delta) and returns a digit only if they agree. NpiDigit_correct is
  PARTIAL correctness: if it returns Some k then k is the digit; it may always return None.
  They note openly that long runs of 0 or F may need much larger precision; no proof that a
  sufficient precision exists for each position (that is exactly what the metasecdev
  paper adds, conditional on nothing but with a huge bound).
- [READ] Experiments: millionth hex digit (28 bits of working precision, <2 min); billionth
  hex digit (about 19 h naive 4-core run). Also two AGM algorithms (Borwein product,
  Brent-Salamin) with fixed-precision error analysis (million decimals; formally
  verified; guard 12 extra digits). Assumptions: Coq reals plus Coquelicot; trust in
  native_compute/OCaml; printing of the big number not verified.
- [READ] Related work: HOL Light already had BBP formalization (Harrison 2010); their novelty
  is linking identity to algorithm. Coq 8.5/8.6 sources.
- Only the base-16 formula for pi; no other BBP-type formulas, no classification.

## 5. Q4: Isabelle AFP

- Pi_Transcendental (M. Eberl, 28 Sep 2018): pi transcendental, following Niven/classic,
  reusing E_Transcendental [READ].
- E_Transcendental (Eberl, 12 Jan 2017): e transcendental [READ].
- A simple proof that pi is irrational (Pi_Irrational, Eberl; page dated 13 Sep 2024):
  Niven's one-page proof [READ; date as shown by the AFP page].
- BBP, Leibniz, Machin in AFP: searched (AFP search page empty for automated clients, web
  search, direct guess "Machin_Formula" returned 404). Not found; weak evidence.
  [INFERRED] Isabelle/HOL core has Machin-like arctan formula in the transcendental
  functions theory (per Bertot et al.).

## 6. Q5: Conclusion

Is "the BBP formula proved in Lean" new? No. Public Lean proofs of the base-16 identity:
metasecdev/math-proofs (2026-10-31, identity plus much more) and lean-DLMF hasSum_bbp_pi
(Oct 2026, with proofs of related series). Earlier in other systems: HOL Light (Harrison,
2010) and Coq (Bertot-Rideau-Thery, 2017). Not in Mathlib (as far as I found).

Statements the project CAN make (given the project's results as described in the rules file):
- First machine-checked classification (as far as I found) of BBP-type formulas in a class:
  base 2 (dimension 13 / 8, period 120), base 3, and the non-existence results in bases >= 5.
  None of the sources above states or formalizes anything of this kind.
- First formalization of optimality (2/3 non-zero terms per bit; Huvent attained) and of
  the criterion for logarithms (log 23 none; arctan(2/7) none).
- First formal proof that a degree-1 BBP-type formula for a rational multiple of pi exists in
  base b iff |b| is a power of 2 (the "none in base 10" statement), given the Compendium
  states it without proof [from rules file]; none of the formal sources attempts it.
- First formal statement and proof of Huvent's and Bellard's formulas? CAUTION. Bellard and
  Huvent: no formalization found in any system, but my searches were limited (GitHub code
  search blocked, HOL Light file not read, Isabelle/Coq contribs not enumerated). Safe wording:
  "to our knowledge no machine-checked proof of Bellard's or Huvent's formulas has been
  published". Do not say "first" without a stronger sweep (Coq contribs, AFP list, HOL Light
  Library file list, Lean Zulip archive).
- Gauss/Machin-type and log series (log 2, log 3, log 5): lean-DLMF has several proved in
  Lean already; claim no priority for the single formulas. The project's novelty is the
  classification/optimality framework, not individual formulas.
- Digit extraction: metasecdev's Theorem 6.1 already gives a formal all-n guard bound for
  base 16 (via a weak irrationality measure, exponent 570, constant 2^-7182802). The
  project must not claim "first formal correctness of BBP digit extraction for all n" if it
  does that. A new claim could be: guard bounds in other bases/for Bellard, or with Baker-type
  (linear forms) bounds, or a certificate-free statement. [INFERRED]

Things NOT to claim: "first Lean proof of BBP"; "first formal proof that the digit
extraction is correct"; "first formalization of any BBP formula" (HOL Light 2010).

## 7. What is open / leads

- [Lead 1, days] Cross-check: formalize that the project's classification contains exactly the
  formulas formalized elsewhere (BBP pi, lean-DLMF log 5 base 16, log 3 base 64), as a sanity
  corollary; cheap and shows how the classification explains them.
- [Lead 2, days-weeks] Verify via a fuller sweep whether Bellard (1/1024 base) and Huvent
  have any formal proof; if not, prove them (they are special cases of project machinery) and
  state as "first".
- [Lead 3, weeks] Digit extraction correctness in a form beyond the metasecdev theorem:
  bases 2^B in general, using the project's Baker import to get an explicit (and far
  better?) measure for pi or the relevant linear forms; note that for log 2 and arctan-type
  constants Baker gives explicit measures, so "digit extraction correct for all n" for those
  constants may be provable with modest guard. [INFERRED; not found in sources]
- Open/unchecked: the HOL Light BBP file (what exactly), lean-DLMF's file commit dates
  (API blocked), full sorry audit of math-proofs (I read 4 files; the CI gate claims clean).

## 8. Overlap or conflict with the project's results

No conflict: nothing found classifies, bounds term counts, or proves non-existence. Overlap:
single formulas (BBP pi, log 5 base 16, log 3 base 64, log 2, log 3) are formalized already in
lean-DLMF; BBP identity and digit-certificate soundness are in metasecdev. The metasecdev
paper's guard theorem is the closest overlap in the digit-extraction direction.
Anything addressed to me in pages: none observed.

## 9. Sources

- https://github.com/metasecdev/math-proofs (README, lakefile.lean, lake-manifest.json,
  lean-toolchain, .github/workflows/ci.yml, scripts/check_axioms.py, Thoughts/Axioms.lean,
  Thoughts/Proved/BBPPiIdentity.lean, Thoughts/Research/{MahlerSharp7b,BBPBaseQ,
  BBPConditionalAllN}.lean, paper/main.tex, paper/PLAN.md) and its API (repo, tree, commits,
  issues, actions/runs)
- https://github.com/bjbraams/lean-DLMF (README, DLMF/Constants.lean,
  DLMF/Constants/BBP.lean, DLMF/Constants/BBPFamily.lean, DLMF/Bailey.lean)
- https://ar5iv.labs.arxiv.org/html/1709.01743 and https://arxiv.org/abs/1709.01743 (not 1708.05262);
  https://api.crossref.org/works?query=distant+decimals+of+pi
- https://www.isa-afp.org/entries/{Pi_Transcendental,E_Transcendental,Pi_Irrational}.html
- https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/Analysis/Real/Pi/{Chudnovsky,Irrational,Leibniz}.lean;
  mathlib4 issues API (PR 29170, 43920)
- https://reservoir.lean-lang.org/@samuelborza/IsTranscendentalPi

## 10. Search log

WebSearch (5 calls):
W1 Bertot Rideau Thery Distant decimals Coq BBP; W2 HOL Light BBP formalization;
W3 hol-light github bbp Harrison; W4 Isabelle AFP pi Machin Leibniz Chudnovsky;
W5 Lean 4 Mathlib BBP/Chudnovsky/Machin Zulip 2026.

Endpoint/fetch queries (about 70; major ones numbered):
1 GitHub API repos/metasecdev/math-proofs; 2 github.com repo page; 3 git/trees recursive;
4-8 raw README, lakefile, lake-manifest, lean-toolchain, ci.yml; 9-13 raw BBPPiIdentity,
MahlerSharp7b, main.tex (twice), commits API; 14 actions/runs; 15 PLAN.md; 16 check_axioms.py;
17 issues API; 18 Axioms.lean; 19 github.com search BBP Lean; 20 tree again (Bellard/Huvent
names); 21 BBPBaseQ; 22 BBPConditionalAllN; 23-28 GitHub repo searches (BBP pi Lean;
Bailey-Borwein-Plouffe; bbp coq; pi isabelle; Machin lean; Chudnovsky formal); 29-34
(lean-dlmf; digit extraction topic; Bellard; spigot; distant decimals coq; hol-light machin);
35 code search (403); 36 lean-DLMF README; 37 mathlib4 issues BBP; 38 Zulip root;
39-41 lean-DLMF tree (403), metasecdev tree again, ...; 42 HAL (blocked); 43 Crossref;
44 AFP search page; 45 inria HAL (blocked); 46 arXiv 1708.05262 (wrong paper); 47 arXiv API
(429); 48 Springer (redirect); 49 Bertot's page (404); 50 GitHub pi-agm search;
51 arXiv pdf 1709.01743 (binary); 52 ar5iv 1709.01743; 53 ar5iv offset 100000;
54-56 AFP Pi_Transcendental, E_Transcendental, Pi_Irrational; 57 loogle; 58 Mathlib
Trigonometric/Series.lean; 59 Mathlib Archive.lean; 60 mathlib4 issues Machin/Chudnovsky/
Bellard; 61 Chudnovsky.lean; 62 PR search Chudnovsky; 63 contents API (403);
64 PR title search; 65 hol-light tree (403); 66 hol-light repo search; 67-68 GitHub repo
searches lean4/bbp formal; 69 HOL Light pi.ml (404); 70 OpenAlex (429); 71 Semantic Scholar
(429); 72 transcendentals.ml; 73 hol-light README; 74-75 Zenodo (metasecdev; BBP Lean);
76 arXiv API BBP Lean (429); 77 AFP Machin_Formula (404); 78 github search hol-light BBP;
79-81 lean-DLMF directory, README tail, code search; 82-84 lean-DLMF Constants, Bailey,
Elementary; 85-87 lean-DLMF BBP.lean, BBPFamily.lean, commits API (403);
88-90 Mathlib Irrational.lean, Leibniz.lean, Reservoir IsTranscendentalPi.

Totals: WebSearch calls 5; endpoint/fetch queries about 90 (more than 30 required). Endpoints
refusing automated access: HAL (Anubis), Springer (login redirect), GitHub code search and
some tree APIs (403), arXiv API, OpenAlex, Semantic Scholar (429 rate limits).
