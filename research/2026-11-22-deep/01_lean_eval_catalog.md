# lean-eval (Lean AI formalization leaderboard): catalog, rules, status

Research date: 2026-11-22. Tags: [READ] = I opened the page or file and saw it; [SNIPPET] = seen only in search-result text; [INFER] = my inference, flagged. Quotes are kept under 15 words.

## Summary (10 lines)
1. lean-eval is a comparator-checked Lean 4 + Mathlib benchmark and public leaderboard; repo `leanprover/lean-eval`, Apache-2.0, created 2026-04-10 (GitHub API). [READ]
2. It lives in the `leanprover` GitHub org; Kim Morrison is the named maintainer contact and a major problem submitter. No Lean FRO announcement post was found. [READ]/[INFER]
3. A problem is "solved" iff comparator accepts the submission; code quality is not judged. [READ]
4. Anyone with a GitHub login may submit (the site's data shows about 65 individual logins plus labs such as Axiom, Harmonic, ByteDance, Infinigence AI, Forge); at most 4 active submissions per owner. [READ]
5. Source is private or published under Apache-2.0 two UTC months after acceptance; model and production notes are self-reported; "replay" is a LeanEval re-run measurement of accepted solutions. [READ]
6. Axioms are not discussed on the Submit page or README; the AnnalsChallenge paper (via snippet) says proofs are checked without additional axioms. [READ]/[SNIPPET]
7. Site data (generated 2026-11-22T05:54Z): 311 formalization problems, 1,968 accepted solutions; 2 software-verification drafts, 9 solutions; the "Open problems" group has 0 problems. [READ]
8. Scope "LeanEval v1": frozen 2026-08-20, 118 members, +10 on 2026-08-21 = 128 (the site JSON appears to show about 127). "v2": 2 members, not frozen. [READ]
9. Baker-Wuestholz (linear forms in logarithms) is in v1 and already has 4 accepted solutions (first 2026-09-21), all with source withheld or private. [READ]
10. Solutions are mostly by AI labs and individual people orchestrating frontier models; Nov 2026 saw a burst (Infinigence AI, Forge) on Annals problems. Press attention found is thin and mostly about Axiom, not lean-eval. [READ]/[SNIPPET]

## What it is
- Description: "Comparator-based Lean formal mathematics eval"; owner `leanprover` (organization); license Apache-2.0; created 2026-04-10T07:11:10Z; homepage https://lean-lang.org/eval/ (GitHub API). [READ]
- Aim (site text): hard problems stateable mostly with existing Mathlib definitions, usually not open, ideally with a public informal solution; readability and Lean style are not evaluated. [READ]
- Aristotle (Harmonic) handicap: a problem that a single Aristotle query could solve is dropped from the eval set. [READ]
- The home page text is first person and credits Aristotle, Claude Code and Codex for helping prepare problems, but does not name the author. Kim Morrison is the named contact for configuration updates in the README, and the problem manifests list "Kim Morrison" as submitter of several problems; the Reservoir/Lean FRO hits fit a Lean FRO role but I did not read a page stating that lean-eval is a Lean FRO project. [READ]/[INFER]
- Launch: repo created 2026-04-10; leaderboard repo created 2026-04-11 [SNIPPET]; first public seed submissions accepted 2026-05-01 (e.g. a trivial `two_plus_two` problem submitted by many models); the hosted submission service began 2026-09-02; LeanEval v1 frozen 2026-08-20. [READ] No official launch announcement or date found.
- Repos: benchmark https://github.com/leanprover/lean-eval ; results site https://github.com/leanprover/lean-eval-leaderboard ; submissions/results store https://github.com/leanprover/lean-eval-submissions ; a state repo `leanprover/lean-eval-state` is cited in site data. [READ]
- Statement format: Lean statements live in modules under `LeanEval/`, tagged `@[eval_problem]`, with one TOML manifest per problem (`holes` names the theorem(s) to prove; fields: id, title, group, status, visible, statement_revision, tags, module, submitter, source, status_history). Generated comparator workspaces are built by CI under `generated/`. The web page shows the statement with `sorry` (the problem page for Baker-Wuestholz displays a `sorry` placeholder). [READ]
- "Annals Challenge" tag: one registered tag `annals`, described as "problem imported from the Imperial College London Annals Challenge corpus." The corpus (arXiv 2610.18301, Browning, Hristova, Ledvinka, Springer, Su, McKoen, Buzzard; submitted 2026-10-13) has 50 hand-written Lean statements, each the main theorem of an Annals of Mathematics paper from 2020 on, released without proofs. [READ] (arXiv abstract page; manifest and tags.toml)
- Group counts of problems in repo: about 55 `annals_*` manifests in the first 98 listed; many other problem names (e.g. classification_finite_simple_groups, brouwer_fixed_point, chen_theorem, Chudnovsky, Mihailescu, Linnik, Schmidt subspace, Vinogradov mean value, Weak Goldbach, Green-Tao, Fermat's Last Theorem modules exist under `LeanEval/NumberTheory/`). [READ] (module file names; a module existing does not mean an active problem)

## Rules for submitting
- Who: sign in with GitHub; the submitter must be authorized to submit the exact source and metadata. No requirement to be an AI lab: the data lists about 65 individual GitHub logins with results, and standings include "Codex (with human in the loop)" and "Claude Opus ... (human-orchestrated)" for individuals. Max 4 active submissions per owner. [READ]
- Primary path: https://lean-lang.org/eval/submit/ (production intake from 2026-09-02). Older GitHub-issue intake was a fallback "through at least 2026-09-30". [READ]
- Disclosure: submission metadata and results become public on acceptance. Model name is a free-form declared string. An optional `production_description`, and (per docs) self-reported production time, tokens and estimated API-equivalent cost, are shown labeled as self-reported. LeanEval itself measures build and checker time (noted as noisy). No mandatory disclosure of human help or compute was found; it is optional and self-reported. [READ]
- Replay: (a) re-submitting the exact same submission returns the original receipt; (b) on result pages, "replay" is a later LeanEval re-run measurement of an accepted solution (statuses seen: accepted, failed, not-materialized, not-enqueued). [READ]
- Source release: default is scheduled release under Apache-2.0 two UTC calendar months after acceptance. A private repo may instead withhold source (the result stays public, marked withheld). Public repos must use scheduled release; private-to-scheduled is irreversible. Group policy text: "Private-source submissions; accepted solutions are released after the publication delay." Many existing results are marked withheld or private. [READ]
- Axioms: not addressed on the Submit page, the README, or catalog docs I read. An independent snippet states proofs are checked "without additional axioms" in a sandbox. Treat as [SNIPPET]; the standard comparator behavior (it restricts axioms to a permitted list) should be confirmed in https://github.com/leanprover/comparator. [SNIPPET]
- Dependencies: Mathlib freely. Other helper code must live in `Submission.lean` and `Submission/**/*.lean`; only these are overlaid on a pristine workspace (other files, including a modified lakefile, are ignored). Solutions may additionally import the pinned libraries Lean Pool, CFSG, or Stacks (problem statements may not); Stacks and CFSG need different Mathlib snapshots and are submitted separately. [READ]
- Checking: comparator, run in a sandbox (bubblewrap 0.12.0 on Linux for local `lake test`). `lake exe lean-eval run-eval` gives a local score. lean4checker is not mentioned in anything I read. Toolchains: stable v4.36.0, previous-stable v4.35.0, rc v4.37.0-rc1, latest (default). [READ]
- Eligible problems: formalization problems must be visible and active to accept submissions; software-verification problems may be draft too. [READ]

## Current state (as of site data generated 2026-11-22T05:54:12Z) [READ]
Counts: formalization-evaluation 311 problems / 1,968 solutions (default scope v1); software-verification 2 / 9 (default scope draft); open-problems 0 / 0.
Scopes: LeanEval v1 (frozen, published 2026-08-20; 118 selected automatically from results of 2026-08-20 by "fewer than 3 accepted results and no public source", plus 10 added 2026-08-21 = 128); LeanEval v2 (not frozen, unpublished, members: classification_finite_simple_groups, hopf_s6_complex_structure); Draft (6 members); Active; Archive (archived is the most common among problems seen). Status is separate from a `visible` flag.

Standings (formalization, v1, sorted by unique solves; partial excerpt, top of list):

| Solver label | Unique | First | Total | Credited logins |
|---|---|---|---|---|
| Codex (with human in the loop) | 1 | 2 | 2 | plby |
| Claude Opus 5.5 and earlier (human-orchestrated) | 1 | 1 | 1 | littlebin530 |
| Humanifa + GPT 5.6 sol | 0 | 30 | 89 | ZhengyangZhang06, antoinegg1, hongzhoulin89, juihuichung |
| Axiom Prover (Axiom Math) | 0 | 23 | 90 | Vilin97 |
| NEAR AI w/ DeepSeek V4 | 0 | 12 | 88 | skidanovalex |
| GenProof | 0 | 4 | 92 | ma4ypic4y |

Example solved problems (all from per-problem site JSON, [READ]):

| Problem | Solver | Date (UTC) | Source |
|---|---|---|---|
| bakerWustholz_linearForms_logs (v1, active; submitted by Ralf Stephan) | Axiom Prover (Vilin97), first | 2026-09-21 | https://lean-lang.org/eval/site-data/v2/problems/bakerWustholz_linearForms_logs.json |
| same | NEAR AI w/ DeepSeek V4 (skidanovalex) | 2026-09-30 | same |
| same | Humanifa + GPT 5.6 sol (hongzhoulin89) | 2026-10-02 | same |
| same | GenProof, declared "max gp (GPT-6)" (ma4ypic4y) | 2026-10-13 | same |
| chudnovsky_formula_for_pi_inv (archived 2026-08-20; submitted by Kim Morrison) | Claude Opus 4.8 + Fable 5 multi-agent (ldct), first | 2026-07-05 | https://lean-lang.org/eval/site-data/v2/problems/chudnovsky_formula_for_pi_inv.json |
| same (10 solutions in all) | Stealth Model; Seed Prover; Aristotle; Humanifa; Tau; Axiom, etc. | 2026-07-05 to 2026-09-25 | same |
| chen_theorem | Forge | 2026-11-20 | https://lean-lang.org/eval/site-data/v2/recent-solutions.json |
| martinet_totally_real_towers | Forge | 2026-11-21 | same |
| linnik, schmidt_subspace, vinogradov_mean_value, annals_optimal_moebius, annals_duffin_schaeffer_conjecture, annals_on_approximation_of_reals, annals_unit_conjecture, riemann_hypothesis_iff_lagarias_elementary_criterion and others | Infinigence AI (24 listed) | 2026-11-21 to 2026-11-22 | same |
| (7 Forge solutions) erdos_unit_distance_conjecture_false, annals_on_property_t, aspherical_integer_homology_four_sphere, pardon_torus_knot_distortion, smooth_knot_has_quadrisecant | Forge | 2026-11-20 to 2026-11-21 | same |
| seed problems, e.g. two_plus_two, cubic_decay_asymptotic, bvp_comparison, finite_graph_ramsey_theorem | Many models, Aristotle (submitted by kim-em, as test seeds) | 2026-05-01 to 2026-05-03 | https://raw.githubusercontent.com/leanprover/lean-eval-submissions/main/results/kim-em.json |

Notes: the recent-solutions feed I read showed only the first 31 of a very large file (5.3 MB), covering 2026-11-20 to 11-22; the full chronological list was not read. Model labels are self-declared and inconsistent (the same site data flags consolidation of names; one entry's description contradicts its label). Many "solved" results have unavailable or withheld source, so I could not inspect any proof of the number-theory problems.

Software verification tab: 2 draft problems: `coc_strong_normalization` (strong normalization and consistency of the calculus of constructions with universe hierarchy) and `rcf_quantifier_elimination` (quantifier elimination for real closed fields). 9 accepted results (e.g. Humanifa + GPT 5.6 sol on both; Axiom Prover, Forall (Astrio) on both; others on one). Standings are "provisional until the first frozen set." [READ]

## Open problems tab
The group exists ("LeanEval-owned open problems, reviewed and published independently of external catalogs") but its data file has zero problems, scopes, tags and standings as of 2026-11-22T05:54Z. So at present nothing is listed as an open research problem. Site text elsewhere says problems are "usually not open." Some v1/other problems have open-looking titles (e.g. `erdos_unit_distance_conjecture_false`, `riemann_hypothesis_iff_lagarias_elementary_criterion`, an Erdos-Faber-Lovasz Annals item) but these are statements whose proofs exist or are equivalences; I did not verify each. [READ]/[INFER]

## Proposing a problem
- Process: add the statement to a module under `LeanEval/` with `@[eval_problem]`, add a manifest in `manifests/problems/`, open a pull request; CI regenerates workspaces; new problems start as draft revision 1 and may join future releases/sets. Instances in statements must be named; every problem must compile warning-free on all declared configurations and support `latest`. Statement edits increment `statement_revision` and are logged. [READ]
- Criteria stated on the site: hard for current public frontier models, mostly Mathlib-statable, ideally a public informal solution, and the single-Aristotle-query handicap. No formal standing requirement is stated: manifests list individual submitters (e.g. Kim Morrison, Ralf Stephan, Thomas Browning), so outsiders such as Ralf Stephan evidently have proposed problems. [READ]/[INFER]
- CONTRIBUTING.md returned 404 at `main`; the README and `docs/catalog-metadata.md` are the sources. Maintainer for configuration updates: Kim Morrison on Lean Zulip. [READ]

## Attention it has received
- Press/blog coverage specifically on lean-eval: none found (searches 1, 6 below). [not found]
- Lean Zulip: the "Hard proof-based auto-formalization benchmark" thread (opened 2025-04-27 by Jason Rute, run to 2025-05-13) is the precursor discussion; Kim Morrison posted a Robin/Lagarias test statement there. It does not mention lean-eval by name. A Zulip PDF "Live lean triathlon" lists Lean-Eval beside CombiBench and FATE [SNIPPET]. No direct lean-eval thread found. [READ]/[SNIPPET]
- Third-party: Axios (2026-05-26) reported Axiom's proofs in journals; I could not open it (403) and it is about Axiom, not lean-eval. eWeek and CompleteAITraining covered Axiom's AxiomProver math results (snippet only, not lean-eval specific). [SNIPPET]
- Annals Challenge paper at AI-MATH@NeurIPS 2026 describes lean-eval use. [READ] (arXiv abstract) / [SNIPPET] (NeurIPS listing)
- Social media threads by known researchers: not searched (search engine returns little of this); not found.

## Related benchmarks
- Formal Conjectures (Google DeepMind): Lean 4 statements of open and solved conjectures; paper arXiv 2605.13171 (2026-05) reports 2,615 statements, 1,029 open; Apache-2.0. https://github.com/google-deepmind/formal-conjectures [SNIPPET]
- Erdos problems: erdosproblems.com (Thomas Bloom) database; its Lean statements are mainly in formal-conjectures; DeepMind agent reported 9 of 353 open problems resolved (May 2026); Aristotle's Erdos #728 proof (arXiv 2601.07421); a wiki maintained by Terence Tao tracks AI contributions. https://www.erdosproblems.com/ [SNIPPET]
- AnnalsChallenge (Imperial College London): 50 Annals theorem statements; paper https://arxiv.org/abs/2610.18301 ; code under the ImperialCollegeLondon GitHub organization, v1.0.0 (the manifest cites commit e32eb14 of the "AnnalsChallenge" repo); exact URL not given on the arXiv page. [READ]
- PutnamBench (UT Austin, Trishul lab): Lean/Isabelle/Coq Putnam problems; leaderboard https://trishullab.github.io/PutnamBench/leaderboard.html ; Aleph Prover reported leading in early 2026. [SNIPPET]
- miniF2F: olympiad-level, reported saturated by several labs (Zulip remark). [SNIPPET] https://github.com/openai/miniF2F
- Also seen in listings: CombiBench, FATE, LeanCat (Zulip archive titles only). [SNIPPET]

## Queries used (WebSearch count: 9 of 28)
1. lean-eval Lean FRO benchmark leaderboard announcement
2. Lean "lean-eval" AI formalization leaderboard Annals Challenge solved
3. Imperial College Annals of Mathematics formalization challenge Lean AnnalsChallenge
4. Lean Zulip lean-eval leaderboard
5. Formal Conjectures Google DeepMind Lean repository
6. Kim Morrison lean-eval benchmark Lean FRO blog
7. Axiom Math Lean Eval solved problems formal proofs Annals
8. Erdős problems site Lean formalization Thomas Bloom formal-conjectures AI solved
9. PutnamBench leaderboard Lean 4 miniF2F saturated

## Sources
- [lean-eval site](https://lean-lang.org/eval/) and [problems](https://lean-lang.org/eval/problems/), [submit](https://lean-lang.org/eval/submit/) (the problems page loads data by script; I read the JSON feeds instead)
- [Site data index](https://lean-lang.org/eval/site-data/v2/index.json), [recent solutions](https://lean-lang.org/eval/site-data/v2/recent-solutions.json), [formalization group](https://lean-lang.org/eval/site-data/v2/groups/formalization-evaluation.json), [software verification](https://lean-lang.org/eval/site-data/v2/groups/software-verification.json), [open problems](https://lean-lang.org/eval/site-data/v2/groups/open-problems.json)
- [Baker-Wuestholz problem data](https://lean-lang.org/eval/site-data/v2/problems/bakerWustholz_linearForms_logs.json), [Chudnovsky problem data](https://lean-lang.org/eval/site-data/v2/problems/chudnovsky_formula_for_pi_inv.json)
- [leanprover/lean-eval](https://github.com/leanprover/lean-eval), [README](https://raw.githubusercontent.com/leanprover/lean-eval/main/README.md), [catalog-metadata](https://raw.githubusercontent.com/leanprover/lean-eval/main/docs/catalog-metadata.md), [v1-set](https://raw.githubusercontent.com/leanprover/lean-eval/main/docs/v1-set.md), [v2.toml](https://raw.githubusercontent.com/leanprover/lean-eval/main/manifests/sets/v2.toml), [tags.toml](https://github.com/leanprover/lean-eval/blob/main/manifests/tags.toml), [GitHub API repo record](https://api.github.com/repos/leanprover/lean-eval)
- [leanprover/lean-eval-leaderboard](https://github.com/leanprover/lean-eval-leaderboard), [site-data-v2 doc](https://raw.githubusercontent.com/leanprover/lean-eval-leaderboard/main/docs/site-data-v2.md), [compute-reporting doc](https://raw.githubusercontent.com/leanprover/lean-eval-leaderboard/main/docs/compute-reporting.md)
- [leanprover/lean-eval-submissions](https://github.com/leanprover/lean-eval-submissions), [kim-em results](https://raw.githubusercontent.com/leanprover/lean-eval-submissions/main/results/kim-em.json)
- [Reservoir entry](https://reservoir.lean-lang.org/@leanprover/lean-eval)
- [AnnalsChallenge paper, arXiv 2610.18301](https://arxiv.org/abs/2610.18301)
- [Zulip: Hard proof-based auto-formalization benchmark](https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Hard.20proof-based.20auto-formalization.20benchmark.html)
- [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures), [arXiv 2605.13171](https://arxiv.org/pdf/2605.13171)
- [Axios on Axiom](https://axios.com/2026/05/26/axiom-ai-math-journal) (not opened, 403; snippet only)
- [PutnamBench leaderboard Zulip thread](https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/PutnamBench.html)
