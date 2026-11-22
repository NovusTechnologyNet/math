# 11. Formalization opportunities: what is missing from Lean / Mathlib

Date of all status information: fetched 2026-11-22 (Mathlib master and GitHub API as of that day; the 1000+ data comes from `docs/1000.yaml` on master).
Tags: [READ] = seen in fetched content; [SNIPPET] = only seen in a search snippet; "unverified" = not checked on a docs or source page.
Method note: WebFetch returns a summary produced by a small model, so [READ] means "reported by the fetch of that page", not a byte-exact view. The rendered 1000+ page was too large (490k characters) and only its first 100k were read; the YAML source was used for statuses instead.

## Summary (10 lines)

1. Mathlib (master, 2026-11-22) has Leibniz, Wallis, `irrational_pi`, numerical bounds for pi, and the definition (not the proof) of the Chudnovsky sum [READ]. No BBP, Bellard or Machin file was seen in `Mathlib/Analysis/Real/Pi` (5 files listed; listing incomplete) [READ].
2. Chudnovsky's formula is still a `proof_wanted` (`chudnovskySum_eq_pi_inv`, file `Wanted/Analysis/Real/Pi/Chudnovsky.lean`) [READ]. I found no sign that it has been proved.
3. In `1000.yaml`, no Lean declaration for: Zsigmondy, Bang, Baker, Gelfond-Schneider, Lindemann-Weierstrass, Proth, Wolstenholme, Brun, Linnik, Vinogradov, Roth, Kronecker, Kronecker-Weber, Hilbert 90 [READ].
4. Zsigmondy: Mathlib PR #28895 (57 commits) was CLOSED (not merged) on 2026-09-18 when its author deleted the fork; a clean new attempt is open ground [READ].
5. Big transcendence work is already in flight in Mathlib PRs: Lindemann-Weierstrass (#28013, open, 510 commits) and Gelfond-Schneider (#42911 plus a chain of PRs, open) [READ]. Not a gap to fill; at most a review to help with.
6. Pi transcendental and e transcendental exist only outside Mathlib (external links in `100.yaml`) [READ].
7. Mathlib AI policy (mid-2026): disclose AI use, no LLM-written comments, you must defend every line; unsupervised AI PRs may be closed without comment. Several AI-heavy number theory PRs were closed in Sep-Oct 2026 (Stormer #42040, pi-transcendence list entry #43144) [READ].
8. `1000.yaml`/`100.yaml` may soon accept only in-Mathlib formalizations (PR #44115, undecided) [READ]; so a separate Reservoir package would not be "credited" on those pages.
9. A zero-star repo claims a Lean 4 BBP proof plus hex digit certificates (`metasecdev/math-proofs`, pushed 2026-11-16; claims unchecked) [READ]. The Coq BBP work (Bertot-Rideau-Thery) is the only established formal BBP digit extraction I confirmed.
10. Best gaps for this library: BBP/Bellard as proved series (Archive or a package), Bang / Zsigmondy for base 2 (then general bases), Proth, Wolstenholme, Machin-type arctan identities; all are small to medium; Chudnovsky and Baker are research-scale.

## 1000+ and 100 theorem lists

100 list page [READ]: header says 100 of 100 formalized, 0 statement-only; the page was truncated after entry 64, so 65-100 were not individually read. Since Oct 2026 several entries are credited to external proofs (PRs #44489, #45151): pi transcendental (#53), Hermite-Lindemann (#56), FLT (#33), e transcendental (#67), and others [READ]. Entries in `Archive/` seen: #9, #16, #30, #37, #42, #46, #54 [READ]. fpvandoorn says only about 20 of the 100 remain in the "external" sense (unclear wording) [READ, PR #44115 discussion].

Status below is from `1000.yaml` ("None" = no `decl` field) unless stated. PR data from GitHub API search, 2026-11-22.

| Theorem | Status in Lean (Mathlib) | Open PR or project | Relevance to this library |
|---|---|---|---|
| Zsigmondy (Q8074796) | None; comment "TODO: Find the code" [READ] | PR #28895 closed 2026-09-18 (fork deleted), last commits Dec 2025 [READ]; Zulip thread Aug 2025 [READ]; external: `nasqret/ZsigmondyChebyshev` (Chebyshev-polynomial variant, 2026-01) [READ]; Lean 3 file in mathlib3 [READ] | High: base 2 and base 1+i primitive divisors |
| Bang (Q7686760) | None [READ] | none found (search not exhaustive) | High: special case of Zsigmondy |
| Baker (Q3527009) | None [READ] | none in Mathlib found; `carlok/diaz-modulus-lean` claims Baker plus Hermite-Lindemann, L-W, G-S, 729 results, 1 star, claims unchecked [READ] | High: library uses it as hypothesis |
| Gelfond-Schneider (Q976033) | None [READ] | PR #42911 open (117 commits, blocked-by-other-PR, no reviews), prerequisites #35744 etc. open; analytic parts #34836-#35317 merged [READ]; paper arXiv 2603.24823 Karatarakis-Wiedijk [READ] | Medium |
| Lindemann-Weierstrass (Q1572474) | None (comment on WIP PR) [READ] | PR #28013 open, 510 commits, awaiting-author, reviewers jcommelin/ocfnash/tb65536, activity Nov 2026 [READ] | Medium; do not duplicate |
| Apery (Q1095330) | URL only (Zulip) [READ] | not checked | Low |
| Niven (Q4116459) | Formalized `niven` [READ] | - | - |
| Stormer | Not in `1000.yaml` [READ] | PR #42040 closed 2026-09-22 by bot for AI-use standards [READ] | Low (Pell) |
| Mihailescu/Catalan (Q174955) | Statement only (comment) [READ] | PR #44066 open (docs note to external `cadamcat/catalan-lean4`, AI-assisted, on hold pending a policy decision) [READ] | Low |
| Bertrand (Q632546) | Formalized `Nat.bertrand` [READ] | - | - |
| Proth (Q3771212) | None [READ] | none found | Medium: ties to order of 2 mod primes; Mathlib just merged a Lucas primality certificate checker (#45711, 2026-11-05) [READ] |
| Pocklington | Not in `1000.yaml` [READ]; Mathlib status unverified | - | Medium |
| Lucas-Lehmer | Not in `1000.yaml`; but `Mathlib.NumberTheory.LucasLehmer` exists (`lucas_lehmer_sufficiency`, `lucas_lehmer_necessity`) [READ] | - | done |
| Wolstenholme (Q1724049) | None [READ] | PR #29675 closed 2026-09-18 (fork deleted; AI-generated draft); a commenter has an independent ~663-line proof elsewhere, not planning to PR [READ] | Medium |
| Lagrange four squares | Formalized `Nat.sum_four_squares` [READ] | - | - |
| Fermat two squares | Formalized `Nat.Prime.sq_add_sq` [READ] | - | - |
| Dirichlet, primes in progressions (Q550402) | Formalized [READ] | - | - |
| Prime number theorem (Q386292) | Formalized (`decls`, incl. `Chebyshev.isEquivalent_theta_id`) [READ] | PNT+ project (`AlexKontorovich/PrimeNumberTheoremAnd`; 27 open issues) [READ]; weak PNT PR #45844 open [READ] | - |
| Brun (Q844612) | None [READ] | none found | Low |
| Mertens (Q1196729) | URL only [READ] | PRs #41394, #44061, #46026 open, overlapping, #46026 flagged LLM-generated [READ] | Crowded |
| Chebyshev bounds | no standalone entry; a Chebyshev theta result is a decl under PNT [READ] | - | - |
| Linnik (Q2703389), Vinogradov (Q1694565) | None [READ] | none found | Out of scope |
| BBP formula | Not an entry in `1000.yaml` [READ]; not seen in Mathlib | external repo `metasecdev/math-proofs` (see section "What Mathlib has about pi") | Core |
| Machin, Leibniz, Wallis | Not in `1000.yaml` by name [READ]. Leibniz (`Real.tendsto_sum_pi_div_four`) and Wallis (`Real.tendsto_prod_pi_div_two`) in Mathlib [READ]; Leibniz is 100-list #26 [READ]; Machin-type formula: none seen in `Pi/Bounds` [READ], elsewhere unverified | - | Machin is a small gap (unverified) |
| Basel (Q810431) | Formalized `hasSum_zeta_two` [READ] | - | - |
| Stirling (Q470877) | Formalized [READ] | - | - |
| Irrationality of pi | Formalized `irrational_pi` [READ] | - | - |
| Irrationality of e | unverified | - | - |
| Transcendence of pi, e | Not in Mathlib; external only: pi by Trevor Morris and Yuyang Zhao, e by Jujian Zhang (`jjaassoonn/transcendental`) [READ] | pi entry PR #43144 closed 2026-10-03 by maintainer tb65536 ("not including AI-generated entries") [READ] | via L-W PR |
| Liouville (approximation) | LiouvilleWith exists in Mathlib (unverified from docs); 100-list #18 is formalized [READ] | PR #43595 open (irrationals are LiouvilleWith for 1 < p <= 2) [READ] | - |
| Roth (Q751120) | None [READ] | none found | Out of scope |
| Kronecker (Q848810), Kronecker-Weber (Q1369453), Hilbert 90 (Q1420905) | None [READ] | none found | Cyclotomic: Medium for Hilbert 90 |
| Quadratic reciprocity (Q472883) | Formalized (Legendre, Jacobi) [READ] | - | - |
| Cubic reciprocity | not in `1000.yaml`; unverified | - | Gaussian/Eisenstein: Medium |
| Class number formula | Only Stark-Heegner appears (statement only); the formula itself unverified [READ] | PR #46181 (Stickelberger) open [READ] | Out of scope |
| Dirichlet unit theorem (Q1227702) | Formalized `NumberField.Units.*` [READ] | - | - |
| Minkowski (Q1097021) | Formalized [READ] | - | - |

Other number-theory-flavored entries without a Lean declaration in `1000.yaml` [READ]: Herbrand-Ribet, Chen, Franel-Landau, Khinchin Diophantine, Chebotarev, Skolem-Mahler-Lech, Thue, Hilbert-Speiser, Jacobi four-square, Sophie Germain, Carmichael, Siegel-Walfisz, Erdos-Kac, Green-Tao, Hardy-Ramanujan, Hilbert irreducibility, Schneider-Lang, Vantieghem, Nicomachus (comment only), plus tauberian/series: Hardy-Littlewood tauberian, Wiener tauberian, Cesaro, Stolz-Cesaro, Riemann series, Ostrowski-Hadamard gap, Denjoy-Carleman.

## proof_wanted items

- GitHub code search (needs authentication) was not used. What I could verify: Mathlib keeps a top-level `Wanted/` directory with subfolders AlgebraicGeometry/Group, Analysis, CategoryTheory, Combinatorics/SimpleGraph, Computability, Geometry, GroupTheory, LinearAlgebra, Order, Probability, RingTheory [READ]. Under `Wanted/Analysis` only `Convex/Cone` and `Real/Pi` were shown [READ]; `Wanted/Analysis/Real/Pi` contains only `Chudnovsky.lean` [READ]. No NumberTheory folder was in the top-level list I saw, so number-theory `proof_wanted` items live elsewhere (inline in `Mathlib/`), and I did not find a page listing them: **unverified, incomplete**.
- **Chudnovsky: yes, a `proof_wanted`.** File (14 lines, author Kim Morrison, 2025) states `proof_wanted chudnovskySum_eq_pi_inv : chudnovskySum = pi⁻¹` [READ]. The definitions (`chudnovskyNum`, `chudnovskyDenom`, `chudnovskyTerm`, `chudnovskySum`) are in `Mathlib/Analysis/Real/Pi/Chudnovsky.lean`; its docstring says the proof is absent and lists future work: approximate pi, prove the identity, generalize to other Heegner numbers [READ]. A PR on 2026-09-18 (#43920) only moved a `#eval` sanity check [READ]. **Not proved as of 2026-11-22** (no PR found in the API search that proves it; search non-exhaustive).
- PR #39046 "fill two proof_wanted declarations" (LinearAlgebra, not number theory) shows `proof_wanted` items do get filled by PR [READ].

## What Mathlib has about pi

Directory `Mathlib/Analysis/Real/Pi/` on master: `Bounds.lean`, `Chudnovsky.lean`, `Irrational.lean`, `Leibniz.lean`, `Wallis.lean` (listing ended with "View all files", so possibly incomplete) [READ].
- `Bounds`: `Real.pi_gt_sqrtTwoAddSeries`, `Real.pi_lt_sqrtTwoAddSeries`, `pi_gt_three`, `pi_lt_four`, `pi_gt_d2/d4/d6/d20` and `pi_lt_d2/d4/d6/d20`, `floor_pi_eq_three`, `ceil_pi_eq_four`, `round_pi_eq_three`, plus tactics proving `a < pi` / `pi < a` from witness sequences. No Machin-like formula appears on that page [READ].
- `Irrational`: `irrational_pi` (Cartwright-style integral proof) [READ].
- `Leibniz`: `Real.tendsto_sum_pi_div_four` via Abel's limit theorem and the arctan series [READ].
- `Wallis`: `Real.Wallis.W`, `W_eq_factorial_ratio`, `tendsto_W_nhds_pi_div_two`, `Real.tendsto_prod_pi_div_two` [READ].
- `Chudnovsky`: four definitions only [READ].
- Transcendence of pi: not in Mathlib (external proofs only; see table).
- BBP in Mathlib: not seen in the directory above; docs-site declaration search not run, so "not present" is **unverified beyond the directory listing**. Bellard: same, unverified.
- BBP elsewhere in Lean: `metasecdev/math-proofs` (Brian Bernard Taylor; Apache-2.0; 50 commits; 0 stars, 0 forks; pushed 2026-11-16) claims `bbpSeries_eq_pi`, guarded hex-digit certificates checked by `decide +kernel`, and an irrationality-measure bound with guard depth 570n+1795711; heavy certificates not built by CI (more than 10 GB RAM each); claims are the author's own and not checked by me [READ]. A web search (search 1) found no other Lean BBP formalization [SNIPPET].
- Coq: Bertot, Rideau, Thery, "Distant decimals of pi" (J. Automated Reasoning 2018; arXiv 1709.01743) proves the BBP series equals pi (via integrals, arctan(1) = pi/4, Coquelicot) and a digit-extraction function with a partial-correctness lemma `NpiDigit_correct`; it also treats AGM algorithms [READ, first 100k characters of the arXiv HTML]. A formal guarantee of the same style in Lean 4 for BBP and Bellard/Huvent formulas is the closest analogue of what this library already does.
- Lean 4 transcendence in the wild: `carlok/diaz-modulus-lean` (Apache-2.0, 1 star) claims Hermite-Lindemann, L-W, G-S and Baker with 3 standard axioms [READ; unchecked].

## Contribution rules and AI policy

Mathlib contribution guide (https://leanprover-community.github.io/contribute/index.html, mirrored at mathlib.org/contribute/index.html), read 2026-11-22; the page states its time frame as "mid-2026" [READ]:
- Comments: using an LLM to write GitHub or Zulip comments is not allowed.
- Disclosure: if AI tools are used in code, say which tools and how in the PR description; for substantial LLM-generated code, comment `LLM-generated` to add the label (new contributors cannot add it themselves; a maintainer may) [READ, plus PR threads #42293 and #42888].
- Understanding: you must understand all AI-written content and justify design decisions to reviewers without AI help.
- Quality bar: the page says code written by AI without supervision by a Lean subject expert fails the bar by a large margin (as of mid-2026).
- Enforcement: low-quality LLM PRs, especially without prior discussion, "will summarily close without comment"; repeated violations can lead to suspension or a permanent ban from PRs and Zulip.
- Observed practice: bot-closed Stormer PR #42040 (self-described "bots coded, human understands mostly") on 2026-09-22 [READ]; maintainer closed AI-assisted `100.yaml` pi-transcendence entry #43144 on 2026-10-03 [READ]; maintainer Kim Morrison removed AI systems from `authors` fields ("AIs can't be authors") [READ, PR #44489].
- New contributors: no dedicated onboarding process is described; ask in the `#mathlib` Zulip channel if a topic fits; look for a reviewer; consider a standalone repository depending on Mathlib [READ]. PRs by new contributors get the `new-contributor` label [READ].
- Review time: not stated; "over 2600 open PRs" in mid-2026 and "may take time" [READ]. Observed: the Lindemann-Weierstrass PR has been open since 2025-08-05 and is still under review [READ]; Mertens PRs overlap each other [READ].
- Style (https://mathlib.org/contribute/style.html) [READ]: all files must be `module`s (`module` keyword on its own line after the copyright header; `public import` first); line length at most 100 characters; module docstring with title, summary, notation, references; references go in `docs/references.bib`. The style page does NOT mention a file length limit, `native_decide` or `decide +kernel` (so I cannot report a rule from it; "unverified"; check the linter and naming pages). `decide +kernel` is used by the external BBP repo, which is a reason to expect pushback in Mathlib (unverified).
- Archive: formalizations that "don't have a good place in mathlib", usually few dependents; submitted by PR; style less strict; naming not required [READ]. Contents seen: `Archive/Wiedijk100Theorems/` (AbelRuffini, AreaOfACircle, BallotProblem, BirthdayProblem, BuffonsNeedle, CubingACube, FriendshipGraphs, InverseTriangleSum, Konigsberg, PerfectNumbers, SolutionOfCubicQuartic, SumOfPrimeReciprocalsDiverges), `ZagierTwoSquares.lean`, `Imo/`, `Examples/` (includes `MersennePrimes.lean`) [READ]. No BBP or Zsigmondy there.
- Counterexamples/: 31 files seen, e.g. `Cyclotomic105`, `EulerSumOfPowers`, `IrrationalPowerOfIrrational`, `Girard`; README not visible [READ]. Purpose (from names): counterexamples to plausible statements.
- Reservoir (https://reservoir.lean-lang.org): no submission step; it indexes public GitHub repos about daily. Criteria: public non-fork repo, root `lake-manifest.json`, OSI-approved license detected by GitHub, at least 2 stars [READ].
- Isabelle AFP (https://isa-afp.org/submission/): submit via form; refereed; no `sorry`; author must maintain the entry; no AI policy stated on the page; credit by authorship of the entry [READ]. The Isabelle AFP already has transcendence of e and pi (Eberl), per the Karatarakis-Wiedijk paper [SNIPPET].

## Other venues

| Venue | What it is | AI / credit rules | Number-theory task an outsider could take today |
|---|---|---|---|
| Formal Conjectures (google-deepmind/formal-conjectures, ~1.4k stars) | Lean statements of open conjectures, proofs `sorry`; folders include ErdosProblems, OEIS, Wikipedia, MathOverflow, Arxiv, Books, Kourovka, HilbertProblems [READ] | Google CLA; credit "The Formal Conjectures Authors" plus optional `AUTHORS` file; AI contributions follow Mathlib's conventions; AGENTS.md exists with strict faithfulness rules [READ] | Yes: add statements (AMS tag 11) for open problems about BBP-type formulas, digit normality, irrationality measures, only if a published source states them (whether they already exist: unverified) |
| lean-eval (https://lean-lang.org/eval/) | Benchmark of hard problems statable in Mathlib; problems submitted for review; solutions checked by `comparator` [READ] | Page does not describe the PR process or AI rules; problems solvable in one Aristotle query are dropped [READ] | Possible: a Baker-based or Zsigmondy-type problem; details unverified |
| Annals of Formalized Mathematics (afm.episciences.org) | Diamond open access overlay journal, 2024-, code artifact required, no fees, CC-BY 4.0, single-blind review [SNIPPET + READ] | publishing-policies page has no AI-specific rule; mentions originality and conflicts [READ] | A paper on "primitive divisors in Z[i] and a verified BBP certificate chain" is possible; needs mathematical lessons, not novelty [SNIPPET] |
| PNT+ (AlexKontorovich/PrimeNumberTheoremAnd) | PNT with error term, PNT in progressions, Chebotarev stretch goal; 27 open issues, 29 open PRs; Zulip "PrimeNumberTheorem+" [READ] | no AI policy on the README page | Yes (analytic), but not this library's area |
| IEANTN (teorth/IEANTN) | Graph of claims in explicit analytic number theory; claim open work by commenting `claim` on the board; contains CLAUDE.md and AGENTS.md for agents [READ] | no explicit AI policy on README | Yes (explicit bounds), tangential |
| FLT, Carleson, sphere packing blueprints | Not fetched successfully (leanprover-community project pages returned 404) | - | unverified |
| Karatarakis-Wiedijk G-S paper (arXiv 2603.24823, March 2026) | Says transcendence formalization is early-stage [SNIPPET] | - | Algebraic-number machinery for Baker: possible |
| Isabelle AFP | see above | no AI rule on page | Any of the entries in the ranked list |
| 2026 blueprint for transcendence | search 4 found none [SNIPPET] | - | - |

## Ranked list of ten

Ranking criterion: credible gap, fit with the library, size, and chance of being credited. Sizes are my estimates, not from sources. Credit risk: Mathlib's AI policy applies to anything AI-assisted; a human must author, understand and defend the PR, so for Mathlib a standalone package or an AFM paper may be the realistic record.

1. **BBP formula for pi as a proved series, plus Bellard/Huvent, with exact digit extraction.** Exists: this library's proved series; Mathlib has Leibniz and arctan only; external unreviewed `metasecdev/math-proofs`; Coq precedent. Missing: a reviewed, small, kernel-friendly (no `native_decide`) development in Mathlib style; a `Wanted`-style entry. Size: about 500-2000 lines. Record: Archive (PR) or Reservoir package (2 stars needed) plus an AFM paper; not on `1000.yaml` (no entry).
2. **Bang's theorem (a^n - 1 primitive prime divisors) for base 2, in Mathlib style.** Exists: library's primitive prime divisors of 2^n - 1; `1000.yaml` Q7686760 has no decl. Missing: a Mathlib-ready statement and proof. Size: 500-1500 lines. Record: `1000.yaml` Q7686760 if merged in Mathlib.
3. **Zsigmondy's theorem for general coprime bases.** Exists: base 2 and Gaussian analogues in the library; old Lean 3 file; closed PR #28895 (57 commits, history may be recoverable only through the fork; deleted). Missing: general bases and the exceptions (2,1,6 and 2^k - 1 cases). Size: 2000-4000 lines. Record: `1000.yaml` Q8074796 (comment says "TODO: Find the code"). Risk: previous attempt was AI-generated in part and a maintainer-level author; duplicate effort possible.
4. **Proth's theorem and a Pocklington-type criterion using orders of 2 modulo primes and the certificate checker.** Exists: library's orders of 2 and certificate checker; Mathlib's new Lucas certificate checker (#45711). Missing: Proth (Q3771212 no decl); Pocklington unverified. Size: 200-600 lines. Record: `1000.yaml` Q3771212 or NumberTheory file.
5. **Wolstenholme's theorem.** Exists: closed PR #29675 (AI draft, one lemma listed); an independent ~663-line proof by another user. Missing: a cleaned PR. Size: 300-700 lines. Record: `1000.yaml` Q1724049. Fit with this library is weak (binomial/p-adic), but cheap and visible.
6. **Machin-type and Gaussian-integer arctan identities (Machin, Euler, Gauss) with proofs in Z[i].** Exists: library's concrete Z[i] arithmetic and arctan identities; Mathlib Pi files show none (unverified elsewhere). Size: 200-600 lines. Record: Archive; no `1000.yaml` entry.
7. **Statements of Baker's theorem and its corollaries (linear forms in logarithms) as a self-contained, proved-or-sorried Lean statement file, then a proof track.** Exists: the library takes Baker as a hypothesis; `1000.yaml` Q3527009 no decl; `carlok/diaz-modulus-lean` claims it (unchecked). Missing: proof (research-scale, 10k+ lines). Record: `1000.yaml` Q3527009 only if merged in Mathlib; lean-eval or Formal Conjectures cannot take proved theorems unless framed as problems. Realistic deliverable now: a careful statement in Mathlib style, to unify with the existing hypothesis.
8. **Hilbert 90 / Kronecker-type results on cyclotomic integers.** Exists: library's cyclotomic-integer arithmetic. Missing: Hilbert 90 (Q1420905), Kronecker (Q848810), Kronecker-Weber (Q1369453) all have no decl in `1000.yaml`; Mathlib may already contain pieces (unverified; Hilbert 90 may exist under a different name). Size: 300-1500 lines for Hilbert 90. Record: `1000.yaml`.
9. **Chudnovsky formula (`proof_wanted`).** Exists: definitions in Mathlib; this library has series machinery for pi but not modular forms. Missing: j-invariant/Heegner (163) machinery, which Mathlib lacks. Size: very large (more than 5000 lines, estimate). Record: remove the `proof_wanted` in `Wanted/Analysis/Real/Pi/Chudnovsky.lean`; the most visible `proof_wanted` for pi, but too big for this library alone. A Ramanujan-type formula with an elementary proof of a weaker series could be a partial, credited step (unverified).
10. **Statements for Formal Conjectures: BBP-type open questions (normality of pi in base 16 digit questions; existence of BBP-type formulas for specific constants).** Exists: library's classification theorems (dims 13 and 8, log 23 has no binary BBP-type formula in class F, given Baker). Missing: a sourced statement file under AMS 11 with a citation. Size: 50-200 lines. Record: Formal Conjectures (credit "The Formal Conjectures Authors"; add yourself to `AUTHORS`). Whether such entries already exist: unverified.

Not recommended: Lindemann-Weierstrass, Gelfond-Schneider, Mertens, Stormer, Mihailescu (crowded or AI-policy-blocked, see table).

Strategic point [READ]: PR #44115 (open, undecided) would limit `1000.yaml` to formalizations in Mathlib, Archive, Counterexamples, so credit on those pages needs a Mathlib merge; and the maintainers treat AI-generated entries skeptically (#43144, #44066).

## Pages fetched (about 70 WebFetch calls; WebSearch: 5 of 5 used)

Lean community and Mathlib docs: leanprover-community.github.io/1000.html; /100.html; raw `docs/1000.yaml` and GitHub blob `docs/1000.yaml`, `docs/100.yaml`; mathlib4_docs pages Chudnovsky, Irrational, Bounds, Leibniz, Wallis, LucasLehmer; mathlib4_docs Zsigmondy (404); GitHub trees: `Mathlib/Analysis/Real/Pi`, `Wanted`, `Wanted/Analysis`, `Wanted/Analysis/Real/Pi`, `Wanted/RingTheory`, `Archive`, `Archive/Wiedijk100Theorems`, `Counterexamples`; `Wanted/Analysis/Real/Pi/Chudnovsky.lean`; `Archive/README.md`; CONTRIBUTING.md (404), `.github/CONTRIBUTING.md`; contribute/index, how_to_contribute (404), style (redirect); mathlib.org contribute/index and style; reservoir.lean-lang.org and inclusion-criteria; lean-projects.html (404); teorth.github.io/pnt-and-beyond (404); Zulip archive Zsigmondy thread.
GitHub API searches: Zsigmondy; Zsigmondy open; Chudnovsky proof_wanted; Chudnovsky; Lindemann Weierstrass; Gelfond Schneider; Wolstenholme; Bertrand/Brun/Mertens/Baker; LLM policy; Stormer/Mihailescu/Catalan/Pocklington/Proth; Kronecker-Weber/Hilbert 90/Roth/Liouville; Apery/Brun/Baker/primitive prime divisor; transcendence of e/Hermite; repository searches for BBP, Zsigmondy, Gelfond/Baker.
PRs: mathlib4 #28895, #28013, #42911, #43144, #44489, #44066, #44115, #42040, #29675, #46026.
Other: github.com/google-deepmind/formal-conjectures (README, CONTRIBUTING.md, AGENTS.md, FormalConjectures tree); lean-lang.org/eval; github.com/AlexKontorovich/PrimeNumberTheoremAnd; github.com/teorth/IEANTN; github.com/metasecdev/math-proofs; github.com/carlok/diaz-modulus-lean; arxiv.org/abs/2603.24823; arxiv.org/pdf/1709.01743 (binary, unreadable) and ar5iv.labs.arxiv.org/html/1709.01743; isa-afp.org/submission; afm.episciences.org/page/publishing-policies.
Searches (5): (1) BBP Lean 4 formalization; (2) Zsigmondy Lean 4 formalization; (3) Bertot-Rideau-Thery Coq BBP; (4) Lean blueprint 2026 number theory transcendence; (5) Annals of Formalized Mathematics guidelines.

## Sources

- https://leanprover-community.github.io/1000.html
- https://leanprover-community.github.io/100.html
- https://raw.githubusercontent.com/leanprover-community/mathlib4/master/docs/1000.yaml
- https://github.com/leanprover-community/mathlib4/blob/master/docs/100.yaml
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Pi/Chudnovsky.html
- https://github.com/leanprover-community/mathlib4/blob/master/Wanted/Analysis/Real/Pi/Chudnovsky.lean
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Pi/Irrational.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Pi/Bounds.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Pi/Leibniz.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Pi/Wallis.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LucasLehmer.html
- https://mathlib.org/contribute/index.html and https://mathlib.org/contribute/style.html
- https://github.com/leanprover-community/mathlib4/pull/28895, /28013, /42911, /43144, /44489, /44066, /44115, /42040, /29675, /46026
- https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Zsigmondy's.20theorem.html
- https://reservoir.lean-lang.org/inclusion-criteria
- https://github.com/leanprover-community/mathlib4/blob/master/Archive/README.md
- https://github.com/google-deepmind/formal-conjectures (CONTRIBUTING.md, AGENTS.md)
- https://lean-lang.org/eval/
- https://github.com/metasecdev/math-proofs ; https://github.com/carlok/diaz-modulus-lean ; https://github.com/nasqret/ZsigmondyChebyshev
- https://arxiv.org/abs/1709.01743 ; https://arxiv.org/abs/2603.24823
- https://github.com/AlexKontorovich/PrimeNumberTheoremAnd ; https://github.com/teorth/IEANTN
- https://isa-afp.org/submission/ ; https://afm.episciences.org/page/publishing-policies
- GitHub search API URLs listed in "Pages fetched" (api.github.com/search/issues and /search/repositories)
