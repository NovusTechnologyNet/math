# Larger formalization targets for the pi / Baker project: survey of facts

Date of survey: 2026-11-22. About 19 web searches used (cap 30), plus direct page fetches and GitHub API reads.

Evidence labels used below:
- **[raw]** = I read the raw file or API data (GitHub API, local PDF text).
- **[page]** = I fetched the page; the fetch tool returns a model-made summary of the page, not the verbatim page, so treat details as "read, but second-hand".
- **[snippet]** = seen only in a search-result summary; not confirmed on a primary page.
- **[not opened]** = I could not open it.

Quotes are kept under 15 words.

---

## 1. Formalization status of Baker's theorem and relatives

### 1a. Karatarakis and Wiedijk, "A formalization of the Gelfond-Schneider theorem" (arXiv 2603.24823)

- Submitted 25 March 2026, cs.LO. Authors Michail Karatarakis and Freek Wiedijk. https://arxiv.org/abs/2603.24823 [page; abstract only]
- I read the full PDF text locally (https://arxiv.org/pdf/2603.24823) [raw]. Facts from it:
  - Statement formalized: for algebraic alpha (not 0, 1) and algebraic irrational beta, alpha^beta is transcendental. Sanity check proved: 2^sqrt(2) is transcendental.
  - Priority claim: "no proof assistant currently includes a formalization of the Gelfond-Schneider theorem" before this work.
  - Infrastructure built or used:
    - The **house** of an algebraic number: defined as the sup norm of the canonical embedding (`house`, `house_eq_sup`), following a structural suggestion from Mathlib reviewers. Mathlib has `Mathlib/NumberTheory/NumberField/House.lean`.
    - **Siegel's lemma over rings of integers of number fields**: built on Mathlib's classical integer Siegel lemma (`Mathlib/NumberTheory/SiegelsLemma.lean`). New theorems `basis_repr_norm_le_const_mul_house` and `exists_ne_zero_int_vec_house_le`.
    - An explicit chain of constants c1..c15 depending on the field degree, because big-O arguments cannot be used.
    - The **auxiliary function** S(z): a quotient with removable singularities at integers, so they built a piecewise total function from local power series and proved it analytic with Mathlib's analytic-function library.
    - A final contradiction between an analytic upper bound and an algebraic Liouville-type lower bound.
  - Where the code lives: "a mathlib branch". The PDF hyperlinks point to `github.com/mkaratarakis/mathlib4`, under `Mathlib/NumberTheory/Transcendental/GelfondSchneider/` with files `MainAlg`, `MainOrder`, `MainAnalytic`, `MainPostAnalytic`, `MainHol`, `MainBounds`, `statement.lean`. The paper says parts are already integrated into Mathlib.
  - Related-work map of other systems:
    - HOL Light: Bingham, transcendence of e.
    - Rocq: Bernard, Bertot, Rideau, Strub, transcendence of e and pi.
    - Isabelle AFP: Eberl, Hermite-Lindemann-Weierstrass; Koutsoukou-Argyraki, Li, Paulson on irrationality and transcendence criteria for series.
    - Mizar: Watase, transcendence of e.
    - Lean: Liouville numbers; the analytic part of Lindemann-Weierstrass.
  - **Future work** (Sections 4 and 5):
    - Baker's theorem on linear forms in logarithms is "the most natural extension". Same strategy (auxiliary functions, extrapolation) but "significant complexity" in multi-variable analysis and sharper constant management.
    - p-adic Gelfond-Schneider (Mahler, Veldkamp), replacing Cauchy integrals with Schnirelmann integrals.
    - Quantitative transcendence measures (Feldman), since the constants are explicit.
    - Elliptic-curve analogue with the Weierstrass wp function.
    - The Schneider-Lang theorem.
    - Decision procedures for linear independence of specific logarithms via interval arithmetic.
    - Support for conditional verification of Schanuel's conjecture.
- Mathlib upstreaming status (GitHub API, queried 2026-11-22) [raw]:
  - Mathlib PR #42911 "feat(NumberTheory): the Gelfond-Schneider theorem (Hilbert's seventh problem)", author mkaratarakis, opened 2026-08-18, about +5066 lines, still **open**. https://github.com/leanprover-community/mathlib4/pull/42911
  - Open: #35735, #35743, #35744, #39874 (splits of the same work). Merged: #35316 (analytic lemmas Part 4/5) and #39872 (`natDenominator` API), among others.
  - So the theorem is **not yet in Mathlib**; it is being upstreamed in pieces. The fork `mkaratarakis/mathlib4` was pushed on 2026-11-18.
- Zulip thread "Gelfond-Schneider theorem" (#maths) [page]: https://leanprover-community.github.io/archive/stream/116395-maths/topic/Gelfond-Schneider.20theorem.html
  - Karatarakis announced on 2025-11-23 with a fork.
  - On 2025-11-24 Johan Commelin and Kevin Buzzard congratulated him. The summary says the main file exceeds 6,000 lines and that upstreaming would be "more like 50 PRs", starting with missing basic API. (A search snippet attributed the 50-PR remark to Commelin and the fetch to Buzzard; I did not resolve which.)
  - No mention of Baker or Lindemann-Weierstrass in the thread.

### 1b. Baker's theorem and Baker-Wustholz

- No public Lean blueprint, GitHub repo, Zulip thread or Mathlib PR for a full Baker theorem was found. Searches: two web searches, `gh search` of Mathlib PRs for "Baker", GitHub repo searches. This is absence of evidence only; Zulip itself was not searched directly.
- Freek Wiedijk's "Formalizing 100 theorems" page (last modified 2026-11-01) lists "Baker's Theorem on Linear Forms in Logarithms" among italicized items, which it says means not formalized yet. It is in the list of theorems that are NOT numbered 1-100. [page] https://cs.ru.nl/~freek/100/ (the italics were read by the fetch tool; moderately reliable).
- Lean-eval has a statement-only problem "Baker-Wüstholz theorem on linear forms in logarithms" (section 2). I read the Lean source [raw]: it uses Mathlib's `Height.logHeight₁`, a ring-hom embedding into the complex numbers, the constant C(n,d) = 18 (n+1)! n^(n+1) (32 d)^(n+2) log(2nd), and the theorem body is `sorry`. https://github.com/leanprover/lean-eval/blob/main/LeanEval/NumberTheory/BakerWustholz.lean
- A **different, weaker, AI-produced result** exists and is directly relevant: repository `mjtb49/Bounds-on-linear-forms-in-logarithms` (pushed 2026-10-14) [raw README]. It formalizes an eventual lower bound |p + sum a_i log alpha_i| >= H^(-nu) for integer coefficients and logs of **positive rationals** (multiplicatively independent), for every nu > k, with no explicit H0. The README says ChatGPT 5.6 produced the proof with minimal human input, and `lake comparator --paranoid` passed on 2026-10-13 with six kernel checkers. https://github.com/mjtb49/Bounds-on-linear-forms-in-logarithms . This is NOT Baker's theorem for algebraic numbers and algebraic coefficients, but it shows the neighbourhood is being worked on, by AI.
- Other systems:
  - Isabelle: Eberl's Hermite-Lindemann-Weierstrass is in the AFP (per the Gelfond-Schneider paper) [raw PDF].
  - Rocq: e and pi transcendence (Bernard et al.). HOL Light: e transcendence (Bingham). Per the paper.
  - Metamath: nothing found.
  - Baker's theorem: nothing found in any system.
  - Six exponentials: no formalization found in any system (no hit; not proof of absence).
  - Gelfond-Schneider: only the Lean work above.
- Lindemann-Weierstrass in Lean:
  - Mathlib has `Mathlib/NumberTheory/Transcendental/` containing `Lindemann` and `Liouville` [raw dir listing].
  - Mathlib PR #28013 "feat: Lindemann-Weierstrass Theorem" is open, last updated 2026-11-06; it continues earlier PR #6718 and lists about 14 dependency PRs, all ticked. https://github.com/leanprover-community/mathlib4/pull/28013
  - The Lean 100-theorems page says item 53 (pi is transcendental) has two external formalizations (Trevor Morris, Yuyang Zhao) and item 56 (Hermite-Lindemann) is Zhao's fork plus PR #28013. [page] https://leanprover-community.github.io/100.html

---

## 2. https://lean-lang.org/eval/ (lean-eval)

- What it is [page + raw README]: a public leaderboard for `lean-eval`, a comparator-based Lean benchmark of formalization problems, statements mostly in Mathlib vocabulary, "difficult for current publicly available frontier models" (site wording). https://lean-lang.org/eval/ , repo https://github.com/leanprover/lean-eval , leaderboard source https://github.com/leanprover/lean-eval-leaderboard
- Who runs it: the `leanprover` GitHub organization. The README tells people to contact Kim Morrison on Lean Zulip for configuration updates. I found no named list of maintainers. The Baker-Wustholz problem is attributed to submitter "Ralf Stephan" in its manifest [raw].
- Rules ([page/raw]):
  - Solutions are judged only by `comparator`; "solved" means comparator accepts. Code style is not graded.
  - Submit solutions or new problems through GitHub issue templates; submissions are verified automatically.
  - Mathlib is allowed; helper code must live in the submission workspace; Stacks and CFSG imports allowed in submissions.
  - At most four active submissions per owner.
  - Accepted source is published under Apache 2.0 two UTC months after acceptance.
  - Problems that a single query to Aristotle could solve are dropped, so Aristotle is handicapped.
  - Problems should be hard but usually not open; a public informal solution is preferred.
- Catalog facts from the manifests (321 files under `manifests/problems/` on 2026-11-21) [raw]:
  - Groups: 319 `formalization-evaluation`, 2 `software-verification`, and **0 in `open-problems`** (the group exists in the schema, docs/catalog-metadata.md, but I found no problem filed there).
  - Lifecycle status: 134 active, 179 archived, 8 draft. Archived problems I looked at carry `reason = "policy"` dated 2026-08-20; the docs do not say what policy. I do not know whether "archived" means solved, retired, or too easy.
  - **Solved/unsolved per problem: not obtainable by me.** The leaderboard pages load data by script and my fetches returned only "Loading leaderboard data...". The results state repo (`leanprover/lean-eval-state`) is private.
  - Search snippets of the leaderboard (not opened): one snapshot has Axiom Prover (Axiom Math) first with 207 solved; another has Seed Prover (ByteDance) first with 45. They disagree; unreliable. https://lean-lang.org/eval/legacy/ , https://leanprover.github.io/lean-eval-leaderboard/ [snippet]
- Most relevant problems (exact titles from the manifests; Lean files read raw for several):
  1. **"Baker-Wüstholz theorem on linear forms in logarithms"**: active. https://lean-lang.org/eval/problems/bakerWustholz_linearForms_logs/
  2. **"Chudnovsky formula for pi inverse"**: statement `chudnovskySum = π⁻¹`; archived. Mathlib defines `chudnovskySum` but has no proof.
  3. **"Linear independence results of Calegari–Dimitrov–Tang"**: 1, zeta(2), L(2, chi_-3) linearly independent over Q, plus irrationality of log(1+1/m) log(1+1/n) near m=n; active; source arXiv 2408.15403 (218 pages).
  4. **"The Lindemann–Weierstrass theorem"** and **"Lindemann's theorem (e and π transcendental)"**: both archived.
  5. **"Thue–Siegel–Roth theorem (irrationality measure ≤ 2 for algebraic irrationals)"**: archived.
  6. **"Schmidt's subspace theorem"**: active.
  7. **"Mihăilescu's theorem"**: archived.
  8. **"Brun's theorem (convergence of the twin-prime reciprocal sum)"**: archived.
  9. **"Weak Goldbach theorem"**: active.
  10. **"Duffin-Schaeffer conjecture"** and **"On the Duffin-Schaeffer conjecture"**: active.
  - Others in number theory: "Fermat's Last Theorem" (active), "Green–Tao theorem", "Chen's theorem", "Linnik's theorem (L = 5.5)", "Bounded gaps between primes", "Sylvester's conjecture", "Mazur's torsion theorem", "Ramanujan's conjecture for the τ-function (Deligne's theorem)", "Lagarias criterion is equivalent to RH".
  - Nothing in the catalog about digits of pi or normality. Pi-related items are only Chudnovsky, Lindemann, and Calegari-Dimitrov-Tang (zeta(2) = pi^2/6).
- These are mostly published theorems rather than unsolved problems; the "open problems" group is not populated in what I could read.

---

## 3. Other public lists of targets

### 3a. Wiedijk's "Formalizing 100 theorems"
- Page last modified 2026-11-01; shows Lean 100/100 and HOL Light 99. [page] https://cs.ru.nl/~freek/100/
- Lean's own page also shows 100 formalized, 17 via external proofs (items 5, 6, 8, 12, 13, 21, 24, 28, 29, 31, 32, 36, 41, 43, 50, 53, 56); FLT is mixed. [page, truncated after item 64] https://leanprover-community.github.io/100.html
- Lean community "100 missing" page says 0 missing. [page] https://leanprover-community.github.io/100-missing.html
- So there is **no "first" left on the 100 list**. Wiedijk's page also keeps a list of theorems not on 1-100 and not formalized (italics), including: Atiyah-Singer Index Theorem, **Baker's Theorem on Linear Forms in Logarithms**, Classification of semisimple Lie groups, Green-Tao, Hilbert-Waring, IP=PSPACE, Lie's work relating algebras and groups, **Thue-Siegel-Roth**, and the ZF+DC+IHC model result. [page]
- A Zulip thread on the remaining items (Ceva etc.) [snippet] https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Remaining.20100.20theorems.html

### 3b. "1000+ theorems"
- Lean page: 243 formalized, 1 statement-only. [page, first 100k of 490k characters] https://leanprover-community.github.io/1000.html
- Missing list: 956 theorems. [page] https://leanprover-community.github.io/1000-missing.html . My own selection (the page is not tagged by topic):
  - Transcendence and irrationality: **Gelfond–Schneider**, **Lindemann–Weierstrass**, Schneider–Lang, Apéry's theorem, Rationality theorem.
  - Diophantine: Faltings, Mordell–Weil, Thue's theorem, **Thue–Siegel–Roth**, Tijdeman, Skolem–Mahler–Lech, Khinchin, Hilbert irreducibility, Davenport-Schmidt.
  - Number theory: FLT, Mihăilescu, Modularity, Mazur torsion, Linnik, Brun, Chen, Green–Tao, Vinogradov, Erdős–Kac, Siegel–Walfisz, Hilbert–Waring, Kronecker-Weber.
  - No entry for pi itself, and no Baker that I saw.
  - These lists may lag: Gelfond-Schneider now exists in a fork, and an arXiv paper "A Formal Proof of the Irrationality of ζ(3) in Lean 4" (2503.07625) exists although Apéry is listed missing. [snippet] https://arxiv.org/pdf/2503.07625

### 3c. Mathlib lists
- Mathlib "undergrad TODO" (https://mathlib.org/undergrad_todo.html) [page]: no number theory, transcendence or pi items.
- Mathlib has a `Wanted/` folder of `proof_wanted` statements [raw dir listing]. The only number or pi item is `Wanted/Analysis/Real/Pi/Chudnovsky.lean`. The Mathlib Chudnovsky file [raw] says it "does not (yet!) contain a proof", anyone may adopt it, but "we are a long way off". Future work it lists: approximations of pi, the formula for 1/pi, Heegner numbers / class number 1 and the 163 case with j((1+sqrt(-163))/2) = -640320^3, Eisenstein series. References: Milla, "A detailed proof of the Chudnovsky formula"; Chen and Glebov. https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Real/Pi/Chudnovsky.lean
- `Mathlib/Analysis/Real/Pi/` holds Bounds, Chudnovsky (definition only), Irrational, Leibniz, Wallis [raw].

### 3d. Google DeepMind "formal-conjectures"
- Directory tree read via API [raw]: Arxiv, Books, ErdosProblems, GreensOpenProblems, HilbertProblems, Kourovka, LittProblems, Mathoverflow, Millennium, OEIS, OpenQuantumProblems, OptimizationConstants, Other, Paper, Subsets, Wikipedia, WrittenOnTheWallII. https://github.com/google-deepmind/formal-conjectures
- Pi, transcendence and irrationality items, all tagged `research open` in the Lean files I read [raw]:
  - `Wikipedia/NormalityOfPi.lean`: `pi_normal_base_ten`.
  - `Wikipedia/Irrational.lean`: algebraic independence of e and pi; irrationality of e+pi, e*pi, e^e, pi^e, pi^pi, ln pi, etc.
  - `Wikipedia/Transcendental.lean`: e+pi, e*pi, exp(pi^2), exp(exp 1), pi^e, pi^sqrt(2), pi^pi.
  - `Wikipedia/Schanuel.lean`: Schanuel's conjecture. `Wikipedia/Exponentials.lean`: four exponentials conjecture.
  - `Wikipedia/RiemannZetaValues.lean`: irrationality of zeta(7), zeta(9), zeta(11) open; zeta(3) and zeta(5) tagged solved.
  - These are genuinely open; not realistic targets.
- Size [snippet, May 2026 papers https://arxiv.org/pdf/2605.22763 and https://arxiv.org/html/2605.13171v1]: 2615 statements, 1029 open, 836 solved; Erdős problems the largest source (1318). Erdős milestone: formalize the main statement of every unsolved problem on erdosproblems.com, shown 54 percent complete (undated). https://github.com/google-deepmind/formal-conjectures/milestone/1
- DeepMind's AlphaProof Nexus reports 44 of 492 open conjectures proved and 9 of 353 open Erdős problems [snippet].

### 3e. Erdős problems site
- I found no Erdős problem specifically about pi or transcendence. A search [snippet] reported Erdős #1196 solved from GPT-5.4 Pro output posted by an amateur, checked by a team including Tao, with a Lean version; secondary report dated 2026-11-08, not opened. Epoch AI's "FrontierMath Erdős" uses 68 open conjectures, 50 statements from formal-conjectures [snippet] https://epoch.ai/benchmarks/frontiermath-erdos . Quanta (Aug 2026): Erdős problems are falling to AI [snippet] https://www.quantamagazine.org/why-the-legendary-erdos-problems-are-falling-to-ai-20260803 . erdosproblems.com itself was not opened.

---

## 4. AI-for-mathematics news, about 22 Oct to 22 Nov 2026

Main source is Quanta's weekly column "Transformation" (Konstantin Kakaes). I read two copies of the page [page]: https://www.quantamagazine.org/update/169054/ and https://www.quantamagazine.org/update/168049/ . Items below are as reported by Quanta; I did not open primary sources unless stated.

- **Oct 25-26**: proof of the local smoothing conjecture announced with a Lean verification so many people could check it ([page] https://www.quantamagazine.org/update/168664/).
- **Oct 29**: OpenAI released three claimed results (math, CS, physics) with different disclosure approaches; Anthropic published its own version of the CS result.
- **Nov 5**: mathematicians posted shorter versions of OpenAI's proof that Landau-Siegel zeros do not exist; Ben Green's simplified version was praised by Tao.
- **Nov 9-11**: Anthropic said its Fermat's Last Theorem formalization, which took 11 days in September, would now take about 30 hours (a search of other sources found only the 11-day figure). Axiom Math announced formalizations of the classification of finite simple groups, the Stacks Project, the Weil conjectures and cluster algebras; experts reportedly satisfied; about 96 minor errors in published papers reportedly found. **Helfgott's ternary Goldbach proof formally verified as of Nov 10.** The Lean project is reported by one non-English source (https://eu.36kr.com/de/p/4067629942707072, snippet) as a 194,000-line Lean 4 library by an independent developer, mostly written with Claude Code, no `sorry`, but relying outside Lean on two numerical verifications; repo name given was calr3/ternary-goldbach (not opened).
- **Nov 19**: AI-assisted searches found many elliptic curves of rank 30 and 31; the rank-32 record stands.
- **Nov 20**: Levent Alpöge (Anthropic) posted a four-page paper claiming a proof of the Riemann hypothesis developed with Claude, with about 17 million lines of Lean as verification of the generalized Riemann hypothesis and no human-readable version. Independent Lean groups had compiled it; checks for hidden redefinitions were still running. A separate 940-page human-written GRH claim (Alessandro Masullo) is under scrutiny. I have not verified either; Quanta says verification is ongoing.
- **Earlier, needed as context**: Sept 4 Anthropic's FLT formalization (about 13 million lines, 30,300 theorems checked, only the three standard axioms, comparator confirmed the statement matches Mathlib's FLT; dozens of agents coordinating through a DAG of statements) [page] https://www.anthropic.com/news/formalizing-fermats-last-theorem . Oct 6 OpenAI released 722 manuscripts in 372 families on GitHub, many with Lean, after consulting an IAS advisory group [page] https://community.openai.com/t/first-look-at-mathematics-manuscripts-from-an-internal-frontier-model-at-openai/1403886 (Quanta says 377 results). One, preprint dated 2026-09-24, concerns the irrationality exponent of pi ("as hard as it can possibly be" per Quanta); I did not open it. G. Chudnovsky posted arXiv 2610.28079 (20 Oct 2026) extending the method to logarithms, with ancillary Lean files: 53 of 62 numbered results are checked endpoints, 9 rest on named classical theorems [page] https://arxiv.org/abs/2610.28079 .
- **What made these credible**:
  - A machine-checked artifact (Lean, often with `comparator` and a statement check) that others compile independently within hours.
  - The statement cross-checked against Mathlib's own definition (FLT) or a short human-readable `Challenge.lean`.
  - Named experts quoted (Buzzard on FLT; Tao on simplifications; Lichtman on quasi-RH), plus an advisory group (IAS) for OpenAI's release.
  - Open caveats stated publicly: Lean only checks the stated theorem; misformalization is a known risk; results with no human-readable proof draw criticism.
- Where announced: company blogs, GitHub repos (including small personal ones such as mjtb49's), arXiv, Lean Zulip, and Quanta's weekly column. I did not search social media.

---

## 5. How large formalization projects are split into pieces

- **leanblueprint** (Patrick Massot) [page] https://github.com/PatrickMassot/leanblueprint :
  - A plasTeX plugin: a LaTeX "blueprint" of the proof with each statement and proof labelled and linked to Lean declarations.
  - `\lean{...}` names the Lean declaration; `\uses{...}` gives dependency edges; `\leanok` marks done; `\notready`, `\discussion` (links a GitHub issue), `\mathlibok`.
  - Builds a web page, a PDF and a **dependency graph** that colours finished nodes; `leanblueprint checkdecls` checks the declaration names exist; GitHub Actions publishes to Pages.
  - The page does not describe how work is claimed.
- **PFR project** (Tao, Yaël Dillies maintainers) [page] https://teorth.github.io/pfr/ and [snippets]:
  - Started mid-November 2023; Tao's Zulip post of 2023-12-05 reports no `sorry` left, about three weeks (my arithmetic). Tao estimated he wrote about 5 percent of the lines. Tao's blog said the dependency graph gives a snapshot of progress and the blueprint was detailed enough for experts to write the formal proofs easily. https://leanprover-community.github.io/archive/stream/412902-Polynomial-Freiman-Ruzsa-conjecture/topic/Project.20completed!.20.20Thoughts.20and.20reflections.3F.html
  - Participation through a dedicated Zulip stream and GitHub; later phases extended the result and upstreamed to Mathlib.
- **Fermat's Last Theorem project** (Kevin Buzzard, Imperial) [page] https://github.com/ImperialCollegeLondon/FLT : multi-author open source; blueprint at https://ImperialCollegeLondon.github.io/FLT/blueprint/ ; EPSRC-funded to 2029; 1,716 commits, 29 open issues, 38 PRs when I read it; contribution rules are in `CONTRIBUTING.md` (**not opened**). Anthropic's autoformalization adapted pieces of this project and flt-regular [page].
- **Prime Number Theorem And...** (Kontorovich, Tao) [snippet] https://github.com/AlexKontorovich/PrimeNumberTheoremAnd : blueprint at https://alexkontorovich.github.io/PrimeNumberTheoremAnd/web/sect0001.html ; Zulip stream; named occasional contributors (Helfgott's lemma turned into blueprint entries by Tao); newer work moved to teorth/IEANTN.
- **How outsiders contribute** (consistent across the above): read the blueprint, pick a node whose dependencies are done, discuss it on the project's Zulip stream or the linked GitHub issue, submit a PR proving the node, maintainer marks `\leanok`. I found no explicit claiming protocol on the pages I opened. Buzzard's general advice (snippet): reviewing PRs is a meaningful contribution. Mathlib's "How to contribute" page was seen as a title only: https://leanprover-community.github.io/contribute/how-to-contribute.html
- New fact: Anthropic's September FLT run used an agent-maintained DAG of statements instead of a human blueprint (Prove2Me) [page]. The same idea applies at small scale to a human-plus-AI pair.

---

## Ranked shortlist

### 1. Baker's theorem (qualitative first, Baker-Wustholz bound later), as a staged blueprint project
- **What**: Linear independence over Q-bar of logarithms of algebraic numbers (Baker 1966), then the effective Baker-Wustholz lower bound (the lean-eval problem).
- **Why recognized**: No formalization in any system found; on Wiedijk's not-formalized list; an active lean-eval problem; the Gelfond-Schneider authors name it as the natural next step; it would discharge the exact hypothesis your library already carries.
- **How it splits**: (a) reuse the Gelfond-Schneider layer (house, Siegel over number fields, auxiliary-function and Liouville-lower-bound pattern); (b) Baker for 2 logarithms as a first milestone, then general n via Baker's induction (Baker, *Transcendental Number Theory*, ch. 2-3, per the paper's reference list); (c) explicit constants (Baker-Wustholz). Each stage has a clean Lean statement.
- **Builds on**: Mathlib's Siegel lemma, house and Height API; the Karatarakis-Wiedijk branch and open PR series (#42911 etc.); your Q-linear algebra, certificates and cyclotomic work for the algebraic side; the mjtb49 rational-case repo as a partial map.
- **Main risk**: Size and losing the "first". Gelfond-Schneider alone is a 6,000-line main file plus years of API work; AI labs now produce multi-million-line formalizations in days, and lean-eval exposes the Baker-Wustholz statement to AI solvers. The GS code is not yet in Mathlib, so Baker work would depend on an external fork until it merges.

### 2. Chudnovsky's formula for 1/pi
- **What**: Prove `chudnovskySum = π⁻¹` (a Mathlib `proof_wanted` and a lean-eval problem).
- **Why recognized**: The pi-specific item Mathlib itself lists as wanted ("a long way off"); written by Kim Morrison so it is visible to Lean people; fits a project about pi formulas.
- **How it splits**: Following Milla's "detailed proof": Eisenstein series and the j-function, the CM point at (1+sqrt(-163))/2, the Heegner-number constants, then the series identity. Early pieces can use your Taylor-series and Fourier infrastructure.
- **Builds on**: Your finite Fourier analysis and series work (marginally); Mathlib's modular forms (I did not check how much exists).
- **Main risk**: The lean-eval entry is archived, possibly because it was solved or retired (I could not tell), so a proof may already exist that I did not find. Mathlib's modular-form support may be too thin, making most of the work general modular forms rather than pi.

### 3. Schneider-Lang theorem and the six exponentials theorem, built on the Gelfond-Schneider formalization
- **What**: Schneider-Lang for meromorphic functions of finite order satisfying algebraic differential equations, then six exponentials as a corollary.
- **Why recognized**: Schneider-Lang is named as a follow-up in the paper and is on the 1000+ missing list; no formalization of six exponentials found.
- **How it splits**: Follow the GS auxiliary-function structure, with Siegel's lemma, then a gap argument; the six exponentials as a final corollary.
- **Builds on**: The same infrastructure as target 1, so work is shared.
- **Main risk**: Depends on the GS code being upstreamed and its API stabilizing. I did not confirm six exponentials is absent elsewhere (only that I found nothing). Less recognizable than Baker.

### 4. Thue-Siegel-Roth (irrationality measure of algebraic numbers at most 2)
- **What**: Roth's theorem.
- **Why recognized**: On Wiedijk's not-formalized list and the 1000+ missing list; a lean-eval problem (archived).
- **How it splits**: Roth's lemma with auxiliary polynomial, Siegel's lemma (in Mathlib), index and height estimates, the gap argument; milestones Liouville (already in Mathlib), Thue, Siegel, Dyson, Roth.
- **Builds on**: Mathlib's Siegel lemma, heights and Liouville numbers; your Diophantine-approximation and linear-algebra certificates.
- **Main risk**: Not about pi; Roth's lemma is intricate; the archived lean-eval status may mean it is already done (unconfirmed).

### 5. Quicker fallback: join the Lindemann-Weierstrass PR, or formalize ingredients of the 2026 "irrationality exponent of pi" work
- **What**: Help land Mathlib PR #28013, or formalize the determinant and interpolation method behind OpenAI's irrationality-exponent-of-pi preprint (2026-09-24) and G. Chudnovsky's follow-up (arXiv 2610.28079).
- **Why recognized**: Very current and pi-specific; Lean people would notice; mjtb49's repo shows the method already has a Lean skeleton.
- **How it splits**: Statement first (the public Lean statement reportedly covers only the eventual-approximation inequality); pieces are determinant non-vanishing and the interpolation estimates.
- **Builds on**: Your linear algebra over Q with certificates and your Taylor series; Mathlib's `Mathlib/Analysis/Real/Pi/Irrational`.
- **Main risk**: Low novelty. OpenAI and Chudnovsky already ship Lean supplements for parts of it, and #28013 is someone else's PR. I did not open the OpenAI preprint, so the status of its Lean proof is unverified.

---

## All URLs used

Opened (page or raw):
- https://arxiv.org/abs/2603.24823
- https://arxiv.org/pdf/2603.24823
- https://lean-lang.org/eval/
- https://lean-lang.org/eval/problems/
- https://lean-lang.org/eval/open-problems/
- https://leanprover.github.io/lean-eval-leaderboard/problems/
- https://lean-lang.org/eval/problems/bakerWustholz_linearForms_logs/
- https://github.com/leanprover/lean-eval (README, docs/catalog-metadata.md, manifests/problems/*.toml, LeanEval/**.lean via GitHub API)
- https://github.com/leanprover/lean-eval-leaderboard (tree via API)
- https://github.com/leanprover/lean-eval-submissions (tree via API)
- https://leanprover-community.github.io/archive/stream/116395-maths/topic/Gelfond-Schneider.20theorem.html
- https://github.com/leanprover-community/mathlib4 (PR searches and file reads via API: PRs 42911, 28013; Mathlib/Analysis/Real/Pi/Chudnovsky.lean; Mathlib/NumberTheory/Transcendental/; Wanted/)
- https://github.com/mkaratarakis/mathlib4 (push date via API)
- https://github.com/mjtb49/Bounds-on-linear-forms-in-logarithms (README via API)
- https://cs.ru.nl/~freek/100/
- https://leanprover-community.github.io/100.html
- https://leanprover-community.github.io/100-missing.html
- https://leanprover-community.github.io/1000.html
- https://leanprover-community.github.io/1000-missing.html
- https://leanprover-community.github.io/undergrad_todo.html
- https://mathlib.org/undergrad_todo.html
- https://github.com/google-deepmind/formal-conjectures (tree and files via API)
- https://www.quantamagazine.org/update/169054/
- https://www.quantamagazine.org/update/168049/
- https://www.quantamagazine.org/update/168664/
- https://www.anthropic.com/news/formalizing-fermats-last-theorem
- https://community.openai.com/t/first-look-at-mathematics-manuscripts-from-an-internal-frontier-model-at-openai/1403886
- https://arxiv.org/abs/2610.28079
- https://github.com/PatrickMassot/leanblueprint
- https://teorth.github.io/pfr/
- https://github.com/ImperialCollegeLondon/FLT

Snippet only (not opened):
- https://lean-lang.org/eval/legacy/ (fetch failed: page too large)
- https://leanprover.github.io/lean-eval-leaderboard/
- https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Remaining.20100.20theorems.html
- https://arxiv.org/pdf/2605.22763 and https://arxiv.org/html/2605.13171v1
- https://github.com/google-deepmind/formal-conjectures/milestone/1
- https://epoch.ai/benchmarks/frontiermath-erdos
- https://www.quantamagazine.org/why-the-legendary-erdos-problems-are-falling-to-ai-20260803
- https://eu.36kr.com/de/p/4067629942707072
- https://arxiv.org/pdf/2503.07625
- https://leanprover-community.github.io/archive/stream/412902-Polynomial-Freiman-Ruzsa-conjecture/topic/Project.20completed!.20.20Thoughts.20and.20reflections.3F.html
- https://alexkontorovich.github.io/PrimeNumberTheoremAnd/web/sect0001.html and https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
- https://leanprover-community.github.io/contribute/how-to-contribute.html

Gaps (not opened): Lean Zulip search for "Baker"; FLT project CONTRIBUTING.md; OpenAI's pi irrationality-exponent preprint; Alpöge's RH claim; erdosproblems.com; isa-afp.org Hermite_Lindemann entry (cited in the GS paper only).
