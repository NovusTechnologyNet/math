# Related formal work, Baker upstream status, Zsigmondy in Lean (22 November 2026)

Tags: [READ] opened the source; [SNIPPET] search-result text only; [INFERRED] my deduction. Note: WebFetch returns summaries made by a small model, so "READ" means the page was fetched and summarized, not that raw bytes were seen.

## Key findings

1. **No upstream Mathlib PR for Baker's theorem exists.** The title search `repo:leanprover-community/mathlib4 Baker in:title` returned total_count 0; the PR list for head `mkaratarakis:baker` is empty [READ]. The `baker` branch of mkaratarakis/mathlib4 still ends at 1d51891 (24 Sep 2026, "Split MultiIndex and SchwarzProduct into four files, all under 1000 lines"); no later commit [READ]. A sibling branch `baker-padic` has commits of 25 Sep 2026 (p-adic Baker theorem, "parameters and the main statement" newest) [READ]. The vendored commit is therefore the final complex-case state.
2. **No paper, blueprint, or Zulip thread about the Baker formalization was found.** Karatarakis-Wiedijk's arXiv paper (2603.24823, 25 Mar 2026) is on Gelfond-Schneider only; it names Baker's theorem as the natural next extension [READ]. The branch has no blueprint directory [READ]. The only Zulip thread found (Nov 2025) is about Gelfond-Schneider and does not mention Baker [READ].
3. **Parallel Baker work exists in Tau Ceti.** `TauCeti/NumberTheory/Transcendental/` contains `Baker/` (Delta.lean, MDeriv.lean only), `Lindemann/` (7 files incl. Theorem.lean), `GelfondSchneider/`, `Waldschmidt/`, `AlgebraicLogs.lean` [READ]. A Tau Ceti roadmap "Linear forms in logarithms, Baker's theorem over C and C_p" (Waldschmidt route via Schneider-Lang; p-adic analogue) was proposed for the Atlas math graph on 17 Nov 2026 (facebookresearch/atlas-lean #4507, open) [READ]. Several open Tau Ceti PRs (Waldschmidt matrix, Schwarz lemma, p-adic exp, Schanuel) [READ]. No finished Baker theorem on Tau Ceti main yet [INFERRED from the two-file Baker folder]. Different proof route from Karatarakis's.
4. **Gelfond-Schneider by the same author is NOT merged into Mathlib**: PR #42911 (open, label blocked-by-other-PR, depends on #35744; +5066 lines; only bot comments) plus open preparatory PRs #35735, #35743, #35744, #39874 [READ]. Six exponentials: no trace by this author [READ for the paper; INFERRED for Mathlib]. Lindemann-Weierstrass in Mathlib: only `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`; the full theorem is open PR #28013 by astrainfinita (updated 6 Nov 2026) [READ]. Mathlib's `docs/1000.yaml` lists no declaration for Baker, Gelfond-Schneider, Zsigmondy or Bang [READ].
5. **Zsigmondy/Bang is not in Mathlib.** `Mathlib/NumberTheory/Zsigmondy.lean` is a 404 on master [READ]; the only PR, #28895 (Harmonic, Aug 2025, +1307 lines), was closed unmerged on 18 Sep 2026 after repeated merge-conflict bot messages [READ]. A complete proof is in Tau Ceti (PR #39611, merged 15 Nov 2026) [READ].
6. **Mathlib has the ingredients for the cyclotomic-value route** (section 2): a root of Phi_n in ZMod p is a primitive n-th root when p does not divide n; `orderOf_root_cyclotomic_dvd`; characteristic-p expansion identities; lifting-the-exponent in `Mathlib/NumberTheory/Multiplicity.lean`. `Nat.exists_prime_gt_modEq_one` is a worked instance.
7. **Related-work correction.** "Formal proofs of degree 5 binary BBP-type formulas" (2013) is by Kunle Adegoke, not Bertot-Rideau-Thery, and "formal" there most likely means rigorous, not machine-checked [READ author, year, journal; INFERRED the rest]. The Coq BBP work is Bertot-Rideau-Thery, "Distant decimals of pi" (2017). See section 3.
8. **Venues.** No Lean-only-proof journal policy found; see section 4.

## 1. Baker upstream status

Endpoints and what they returned:
- `api.github.com/repos/mkaratarakis/mathlib4/branches/baker`: head 1d51891b5be7ceeca95b4583cad39e0681c5e453, 2026-09-24T22:37:56Z, unsigned, not protected; parent 3fbeb0d [READ].
- `.../commits?sha=baker&per_page=20`: 20 commits all dated 24 Sep 2026 (newest 1d51891; "Choose the parameters: Baker's theorem is proved" 9414010 at 18:25 UTC; "Docs: the proof is complete" 3fbeb0d at 18:30; file split 1d51891 at 22:37) [READ]. [INFERRED: dense hours-long bursts suggest heavy machine assistance or a replayed history; not inspected.]
- `api.github.com/search/issues?q=repo:leanprover-community/mathlib4+Baker+in:title`: total_count 0 [READ].
- `.../pulls?head=mkaratarakis:baker&state=all`: empty [READ].
- `api.github.com/repos/mkaratarakis/mathlib4`: fork of mathlib4, pushed_at 2026-11-18T16:52:14Z (some other branch changed after Baker), 84 branches incl. `baker`, `baker-padic`, `cyclotomic-iterates`, `gs-*` [READ].
- `baker-padic` newest 65cdef5 (25 Sep 2026, "p-adic Baker theorem: parameters and the main statement") [READ]; completeness not checked.
- Author's other Mathlib PRs: Gelfond-Schneider series, ComputablePolynomial series #41342-41356, Quiver path series #45032-45035 (Oct 2026), mostly open [READ].
- Zulip: only the Nov 2025 thread (Karatarakis announced Gelfond-Schneider on a `final` branch; main file over 6,000 lines; Buzzard estimated about 50 PRs to upstream) [READ].
- Web search for a Baker announcement found none [SNIPPET]; it surfaced the Lean-eval problem "Baker-Wüstholz" (statement only, no solution) [SNIPPET].
- Reviewer comments on Baker: none, there is no PR. On GS PR #42911: bot comments only [READ].

## 2. Primitive prime divisors in Lean

Mathlib (master, raw files fetched; names as reported by the page summary):
- `Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean`: `isRoot_cyclotomic_iff` (NeZero (n:R); mu is a root of cyclotomic n R iff IsPrimitiveRoot mu n), `isRoot_cyclotomic_iff_charZero`, `cyclotomic.roots_to_finset_eq_primitiveRoots`, `isRoot_of_unity_iff` [READ].
- `Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean`: `coprime_of_root_cyclotomic` (root in ZMod p is coprime to p), `orderOf_root_cyclotomic_dvd` (order of such a root divides n), `cyclotomic_prime`, `prod_cyclotomic_eq_X_pow_sub_one` [READ].
- `Mathlib/RingTheory/Polynomial/Cyclotomic/Expand.lean`: `cyclotomic_expand_eq_cyclotomic_mul`, `cyclotomic_expand_eq_cyclotomic`, `cyclotomic_mul_prime_eq_pow_of_not_dvd`, `cyclotomic_mul_prime_dvd_eq_pow`, `cyclotomic_mul_prime_pow_eq`, `isRoot_cyclotomic_prime_pow_mul_iff_of_charP` [READ].
- `Mathlib/RingTheory/Polynomial/Cyclotomic/Eval.lean`: `eval_one_cyclotomic_prime`, `eval_one_cyclotomic_not_prime_pow`, `cyclotomic_pos_and_nonneg`, `sub_one_pow_totient_lt_natAbs_cyclotomic_eval`, `sub_one_lt_natAbs_cyclotomic_eval` and real-valued bounds [READ].
- `Mathlib/NumberTheory/PrimesCongruentOne.lean`: `Nat.exists_prime_gt_modEq_one`, a worked instance of "p divides Phi_k(b), p does not divide b, so k = orderOf (b : ZMod p), so k divides p-1" [READ].
- `Mathlib/NumberTheory/Multiplicity.lean` (lifting the exponent): `Int.emultiplicity_pow_sub_pow`, `Int.emultiplicity_pow_add_pow`, `Nat.emultiplicity_pow_sub_pow`, `Nat.emultiplicity_pow_add_pow`, `Int.two_pow_sub_pow`, `Int.two_pow_sub_pow'`, `Nat.two_pow_sub_pow`, `Nat.multiplicity_pow_sub_pow`, `Nat.multiplicity_pow_add_pow`, `emultiplicity_pow_sub_pow_of_prime`; the `padicValNat.pow_sub_pow` names are deprecated aliases dated 2026-10-28 [READ]. Code written before that date will warn.
- Not found: a single named lemma "p prime, p divides Phi_n(a), p does not divide n, then orderOf a in ZMod p = n"; it is the combination of `isRoot_cyclotomic_iff` with the ZMod cast [INFERRED].
- Zsigmondy/Bang: not in Mathlib (file 404; `1000.yaml` has a "TODO: find the code" note under Zsigmondy naming a 2022 Lean 3 author, and nothing for Bang) [READ]. PR #28895 closed 18 Sep 2026 unmerged [READ]. No other open Zsigmondy PR in the title search [READ]. Other open cyclotomic PRs: #45220 (when is zeta-1 a unit), #38606 (vanishing sums of roots of unity), #45512, #46022 (Stickelberger) [READ].

Tau Ceti (https://github.com/TauCetiProject/TauCeti, site taucetiproject.org) [READ]:
- Lean library on Mathlib that welcomes AI contributions: AI implements and reviews, humans write roadmaps and review rubrics; incubated by the Lean FRO and the Mathlib Initiative; self-described "experiment". License Apache-2.0. Created 2 Jun 2026; 313 stars, 159 forks, 2368 open issues and PRs; pushed 22 Nov 2026 (commits every few minutes by the account tauceti-ai-for-science). Tracks Mathlib master and does not push upstream. Stacked PRs prohibited; new files capped at 1250 lines; automatic PR review currently off.
- Bang-Zsigmondy: PR #39611 "prove the Bang-Zsigmondy theorem and its order corollaries" merged 15 Nov 2026 after three closed duplicates (#40030, #41014, #41465); earlier merged: #28625 (primitive prime divisors by multiplicative order, 8 Nov), #31585 (estimates), #37645 (homogeneous cyclotomic values); #42330 open.
- [INFERRED] Very high churn and AI-written code; the vendored copy should stay pinned (VENDORED.md already records the fetch date).

## 3. Related formal work to cite

- Bernard, Bertot, Rideau, Strub, "Formal proofs of transcendence for e and pi as an application of multivariate and symmetric polynomials", CPP 2016, Coq; transcendence of e and pi; arXiv 1512.02791 [SNIPPET].
- Sophie Bernard, "Formalization of the Lindemann-Weierstrass theorem", ITP 2017, Coq (MathComp, Coquelicot), following Baker's formulation; described as the first formalization of the theorem in any assistant; HAL hal-01647563 [SNIPPET].
- Manuel Eberl, AFP "Hermite_Lindemann" (3 Mar 2021, Isabelle/HOL): follows Baker's formulation, derives transcendence of e and pi [READ]; AFP "Pi_Transcendental" (announced 2024, Niven-style) [SNIPPET].
- Karatarakis and Wiedijk, "A formalization of the Gelfond-Schneider theorem", arXiv 2603.24823, March 2026, Lean 4/Mathlib; claims first formalization in any prover; says parts are already in Mathlib; code on the author's fork; future work lists Baker's theorem [READ].
- Mahboubi and Sibut-Pinote, "A formal proof of the irrationality of zeta(3)", LMCS 17(1), Feb 2021, Coq/MathComp; the key recurrence is checked after the fact against Maple output, an external-certificate pattern [READ abstract].
- Liu, Zhang, Zhi, irrationality of zeta(3) in Lean 4, arXiv 2503.07625, 2025 [SNIPPET]; an Isabelle proof by Eberl (Beukers route) [SNIPPET, thin].
- Mathlib: Liouville numbers are transcendental and Liouville constants, under `Mathlib/NumberTheory/Transcendental/Liouville` [directory READ; content SNIPPET]; Lindemann `AnalyticalPart.lean` only [READ].
- BBP and digit extraction: Bertot, Rideau, Thery, "Distant decimals of pi: formal proofs of some algorithms computing them and guarantees of exact computation", arXiv 1709.01743 (Sept 2017), Journal of Automated Reasoning; Coq; BBP spigot formula for the billionth hexadecimal digit plus two AGM methods; one million decimals [READ abstract]. Also Bertot and Allais, "Views of Pi", J. Formalized Reasoning 2014 [SNIPPET]. No Isabelle AFP entry on BBP or Machin-like formulas turned up; the search was thin [SNIPPET].
- Not machine-checked: Adegoke, "Formal proofs of degree 5 binary BBP-type formulas", Functiones et Approximatio 48(1), 2013 [READ author, year].
- Classification or impossibility with external certificates: Gallicchio, Codel, Avigad, Heule, "An end-to-end verification of Keller's conjecture", ITP 2026, LIPIcs 382, art. 26 (16 Jul 2026), Lean 4 plus mechanically checkable SAT proofs, all dimensions [READ]; the original SAT result of Brakensiek et al. (IJCAR 2020) and a 2026 formalization of the empty-hexagon result [SNIPPET]; Lean tools LRAT-Catcher and PBLean for importing certificates [SNIPPET].
- Baker-Wüstholz used as an assumption: Ralf Stephan, arXiv 2607.14774 (Jul 2026), binary digits of powers of 3; a search snippet says its Lean development takes Baker-Wüstholz as an axiom [SNIPPET; the arXiv page did not confirm]. A natural user of an unconditional Baker.

## 4. Venues and channels (new relative to report 15)

- Axiom Math: five peer-reviewed journals reported to have accepted AxiomProver proofs that were Lean-verified before submission, as a conventional paper plus formal certificates (Axios, 26 May 2026; Axios page returned 403, summary via aiweekly) [SNIPPET].
- arXiv: since May 2026 a one-year ban for clear evidence of unchecked LLM output (hallucinated references, leftover chatbot remarks); authors answer for content; nothing specific about Lean [SNIPPET].
- Annals of Mathematics (Princeton) does not consider AI-generated papers and requires AI-use disclosure; Mizar's Formalized Mathematics allows AI only for language polishing [SNIPPET]. No policy found for Annals of Formalized Mathematics, Experimental Mathematics or JAR.
- CPP 2027 (11-12 Jan 2027, Mexico City, with POPL) follows the ACM AI policy: AI tools allowed, authors answer for correctness; the call cites concern over the volume of AI-assisted proofs and autoformalization [SNIPPET]. The ITP 2026 call (Lisbon) lists AI methods as a topic; no ITP 2027 call found [SNIPPET].
- Lean Zulip thread "Discussion: AI-written mathematical proofs" (ML for Theorem Proving, Nov 2025): Riehl proposed formal verification as the bar for AI-written proofs; Morrison's criterion: a `MainTheorem.lean` stating the result as a Prop with only Mathlib imports, and a `ProofOfMainTheorem.lean` with a single theorem; Tao favored disclosing AI use and sharing prompts [READ]. Mathlib's draft policy on disclosing AI use in PR descriptions (website PR #767) was unadopted as of Feb 2026 [READ]. The statement-file pattern fits our `Unconditional` module.
- Announcement channels: Zulip streams (ML for Theorem Proving, maths, new members), the Simons Foundation feature "From Trust to Verification" (Jun/Jul 2026), Leo de Moura's 2026 talks on Erdos-problem results proved with ChatGPT and verified in Lean [SNIPPET; resting on talks and press].

## What could not be opened or verified

- Axios article (403); Project Euclid page of the Adegoke paper had no abstract; TauCetiRoadmap raw README and contents (404, repository name unknown); `search/code` API needs authentication (401), so Mathlib declaration names rest on raw-file summaries and not on a grep; recheck exact signatures before citing.
- Whether `baker-padic` is complete; any review of Baker outside GitHub; Zulip threads from late 2026 (no archive search tool); Isabelle/AFP BBP or Machin entries; Mathlib Liouville file names.
- Page 2 of the issue-search results (only the first 100,000 characters were read), so other related Mathlib PRs may exist.
- No ITP 2027 call found.

## Search log (17 of 35 WebSearch calls)

1. Karatarakis Baker's theorem linear forms in logarithms Lean 4 formalization
2. Lean Zulip Baker's theorem linear forms in logarithms formalized mathlib branch
3. Bertot Rideau Thery "Formal proofs of degree 5 binary BBP-type formulas"
4. Bertot Rideau Thery Coq formal proof Plouffe pi digit extraction BBP hexadecimal
5. Archive of Formal Proofs Machin-like formulas pi arctan
6. Lindemann-Weierstrass theorem formalized Lean mathlib Isabelle AFP Coq transcendence of pi
7. formal proof irrationality of zeta(3) Apery Lean OR Coq OR Isabelle
8. Isabelle AFP BBP formula OR "digit extraction" pi formalization Eberl
9. Bernard Bertot Rideau Strub formalization of Lindemann-Weierstrass Coq transcendence e pi
10. formal verification SAT certificate Lean Keller's conjecture OR empty hexagon OR Schur number verified proof checker
11. Liouville number transcendental Lean mathlib formalization; Gelfond-Schneider Lean Karatarakis Wiedijk paper
12. Lean 4 formalization of Baker's theorem linear forms in logarithms 2026 announcement (extended)
13. Annals of Formalized Mathematics submission policy AI-assisted formal proofs 2026
14. ITP 2027 OR CPP 2027 call for papers AI-generated formalizations policy
15. arXiv policy AI-generated mathematics papers formalized in Lean 2026 math.NT
16. Lean community blog 2026 new theorem proved by AI formalized Lean first published result
17. journal accepts paper whose proof is only formalized in Lean referee 2026 ...

## Sources (opened)

- https://api.github.com/repos/mkaratarakis/mathlib4/branches/baker
- https://api.github.com/repos/mkaratarakis/mathlib4/commits?sha=baker&per_page=20
- https://api.github.com/repos/mkaratarakis/mathlib4/commits?sha=baker-padic&per_page=8
- https://api.github.com/repos/mkaratarakis/mathlib4/branches?per_page=100
- https://api.github.com/repos/mkaratarakis/mathlib4
- https://api.github.com/search/issues?q=repo:leanprover-community/mathlib4+Baker+in:title
- https://api.github.com/repos/leanprover-community/mathlib4/pulls/42911
- https://api.github.com/repos/leanprover-community/mathlib4/pulls/28895
- https://api.github.com/search/issues?q=repo:leanprover-community/mathlib4+Zsigmondy
- https://api.github.com/repos/leanprover-community/mathlib4/contents/Mathlib/NumberTheory/Transcendental
- [Mathlib Cyclotomic/Roots.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean)
- [Mathlib Cyclotomic/Basic.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean)
- [Mathlib Cyclotomic/Expand.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/RingTheory/Polynomial/Cyclotomic/Expand.lean)
- [Mathlib Cyclotomic/Eval.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/RingTheory/Polynomial/Cyclotomic/Eval.lean)
- [Mathlib Multiplicity.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/NumberTheory/Multiplicity.lean)
- [Mathlib PrimesCongruentOne.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/NumberTheory/PrimesCongruentOne.lean)
- [Mathlib 1000.yaml](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/docs/1000.yaml)
- [Tau Ceti repo API](https://api.github.com/repos/TauCetiProject/TauCeti)
- [Tau Ceti README](https://raw.githubusercontent.com/TauCetiProject/TauCeti/main/README.md)
- [Tau Ceti Transcendental/Baker](https://api.github.com/repos/TauCetiProject/TauCeti/contents/TauCeti/NumberTheory/Transcendental/Baker)
- [Atlas issue 4507](https://github.com/facebookresearch/atlas-lean/issues/4507)
- [arXiv 2603.24823](https://arxiv.org/abs/2603.24823) and [HTML](https://arxiv.org/html/2603.24823v1)
- [Zulip: Gelfond-Schneider theorem](https://leanprover-community.github.io/archive/stream/116395-maths/topic/Gelfond-Schneider.20theorem.html)
- [arXiv 1709.01743](https://arxiv.org/abs/1709.01743)
- [arXiv 1912.06611](https://arxiv.org/abs/1912.06611)
- [AFP Hermite_Lindemann](https://isa-afp.org/entries/Hermite_Lindemann.html)
- [ITP 2026 Keller paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2026.26)
- [arXiv 2607.14774](https://arxiv.org/abs/2607.14774)
- [Zulip: AI use in PR description](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/policy.20proposal.3A.20mention.20AI.20use.20in.20PR.20description.3F.html)
- [Zulip: AI-written mathematical proofs](https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.20proofs.html)
- [Adegoke record](https://portal.mardi4nfdi.de/wiki/Publication:1948707)
