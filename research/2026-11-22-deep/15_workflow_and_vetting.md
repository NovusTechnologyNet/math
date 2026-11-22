# 15. Workflow and vetting of AI-assisted Lean mathematics (survey as of 22 Nov 2026)

Tags: [READ] = seen in fetched page content (WebFetch returns a model summary of the page, so wording is the fetcher's); [SNIPPET] = from a WebSearch result only; "from memory, unverified" = not confirmed this session. WebSearch used: 8 of 8. Quotes are under 15 words.

## Summary
1. Buzzard's 12 Nov 2026 post lists four checks: statement matches the informal one; code compiles; `lake comparator` shows the proved theorem equals the trusted statement with only standard axioms; `lake comparator --paranoid` for multiple kernels. [READ]
2. comparator is now merged into Lean core (v4.35.0) as `lake comparator`/`lake check`; the standalone repo is archived. [READ]
3. Lean's reference manual page on validating proofs gives the ladder: no-warning build, `#print axioms`, `lean4checker`/`leanchecker`, comparator. None of them checks that the statement means what you intend. [READ]
4. External/verified kernels as of Oct-Nov 2026: nanoda, lean4lean, con-leche (Lean, proven consistent relative to set theory), con-ron (Rust). [READ]
5. The Lean/Mathlib community statement on the RH proof (21 Nov 2026) used four criteria: statement vetted against Mathlib's definition; reproducible compile; comparator and `con-leche --compare`; several independent checkers on an inert export. [READ]
6. The main residual risk named by everyone is misformalization (wrong definition, vacuous hypotheses). Example: a `ContDiff ℝ ⊤` bug found after announcement in a solo AI-assisted project. [READ]
7. Novelty: AI "solutions" are often literature rediscoveries. A 2026 AxiomProver paper was found to restate Mirsky (1947) and was withdrawn from journal plans. Tao's wiki gives a 9-step procedure. [READ]
8. arXiv: two submissions per calendar month, max three active, from 1 Oct 2026; endorsement still required for first submission; significant AI use must be disclosed. [READ/SNIPPET]
9. Community norms (Leiden Declaration, June 2026): disclose tool use, humans keep responsibility for correctness, attribute prior work actively. [READ, via fetch summary of the site]
10. Unaffiliated routes: Zenodo (open registration), GitHub + Reservoir (license and 2 stars needed), JIS (free, email submission, strict AI rules). Verified individual-author discovery examples for 2025-26 were NOT found; see Discovery section.

## Verification checklist (numbered, with source)
1. Write the theorem statement in a short standalone file importing only Mathlib (a "challenge" file, proofs `sorry`) and have a human read every definition it uses. Source: comparator README; Lean ref manual ValidatingProofs; Hales/Tao post (statement audit is easier than proof audit). [READ]
2. Check the Lean statement against the informal statement in your paper, line by line; look for vacuous hypotheses, wrong coercions, notation, and instances. Source: Buzzard 12 Nov 2026 criterion 1; Lean ref manual caveat. [READ]
3. Add a non-vacuousness lemma showing the hypotheses are satisfiable by a concrete example. Source: Ilin arXiv 2603.15929 (added at expert suggestion). [READ]
4. Build from clean: `lake build` with no errors or warnings, no `sorry`; pin toolchain (`lean-toolchain`) and commit `lake-manifest.json`. Source: Lean ref manual; Reservoir criteria (manifest). [READ]
5. Run `#print axioms` on each headline theorem; expect only `propext`, `Classical.choice`, `Quot.sound`. `sorryAx` = hole; `_native` = native evaluation (`decide +native`, `bv_decide`) which external checkers cannot verify; anything else = custom axiom. Source: Lean ref manual. [READ]
6. Run `leanchecker` (formerly lean4checker) via `lake check` or `lake env leanchecker --fresh <Module>`. Replays declarations through the kernel; assumes `.olean` files are well formed. Source: Lean ref manual; lean-action README (`lean4checker` deprecated alias for `leanchecker`; bundled on v4.28.0-rc1 and newer). [READ]
7. Run `lake comparator` (config JSON: `challenge_module`, `solution_module`, `theorem_names`, `permitted_axioms`, optional `definition_names`, `external_kernels`) and then `lake comparator --paranoid` (official kernel plus nanoda, lean4lean, con-leche, con-ron). Sandboxed (landrun) on Linux. Source: comparator README; Lean ref manual; Demoura 15 Oct 2026 post. [READ] Note: the standalone repo needs `landrun` and `lean4export` on PATH; the merged version needs Lean >= v4.35.0 (per README). Whether your project's Lean version has it must be checked locally.
8. Avoid native-evaluation tactics in headline proofs if you want the external-kernel checks to apply. Source: Lean ref manual. [READ]
9. Do not trust AI-written definitions unreviewed: have a human or independent model formalize or review the statement separately. Source: Tao erdosproblems wiki FAQ step 7. [READ]
10. Run the build in a sandbox if the code is untrusted (bubblewrap named by Buzzard; landrun used by comparator). Source: Buzzard post. [READ]
11. CI: `leanprover/lean-action@v1` (build, test, lint, `mk_all --check`, Reservoir eligibility check, leanchecker, nanoda, axiom audit options). Source: lean-action README. [READ]
12. Have a second, different model (and ideally a human expert) review statement and definitions; ask explicitly for criticism because models tend toward sycophancy. Source: Tao wiki FAQ step 5. [READ]
13. Make prompts, commit history and logs public where feasible (Ilin published 229 prompts and 213 commits). Source: arXiv 2603.15929. [READ]
14. State in the paper exactly what is and is not verified: "Lean checks the formal statement; the match to the informal one was reviewed by X." Source: Buzzard (PDF and Lean proofs can diverge); Calegari/Tao guest post. [READ]
15. Optional, kernel-bug paranoia: check the Lean Kernel Arena result for the exported proof. Source: Buzzard post (arena link). [READ]

## Tools named (what, where, how)
- comparator: checks a `Solution` module proves the same theorems as a trusted `Challenge` module, with permitted axioms only, kernel-replayed. Repo https://github.com/leanprover/comparator (archived; merged into Lean core v4.35.0 as `lake comparator` and `lake check`). [READ]
- leanchecker / lean4checker: replay `.olean` declarations through the kernel. `lean4checker --fresh <Module>`. [READ]
- nanoda: independent Rust kernel; usable via comparator `external_kernels` and lean-action. [READ]
- con-leche (Lean-written, proven consistent relative to set theory), con-ron (Rust, proof of refinement with Aeneas), lean4lean (partially verified): Demoura post of 15 Oct 2026 (URL in Sources). `con-leche --compare` is also a statement-comparison tool per the 21 Nov statement. [READ]
- Lean Kernel Arena: https://arena.lean-lang.org (about 25 kernels per Hales). [READ]
- Statement-isolation file importing only Mathlib: this is the comparator "Challenge" idea plus the RH statement's reliance on Mathlib as the only dependency. No source says "must import only Mathlib" as a rule; that is my inference. [READ for comparator; inference noted]
- Tao's page of 9 Oct 2026 titled "What mathematicians should know about the Lean Theorem Prover" appears, per the fetched text, to be a guest post by Hales (the fetcher repeatedly attributes statements to Hales, with Carneiro mentioned). Treat authorship as unconfirmed; it reports a 2026 "Summer of Soundness Bugs" (a kernel bug giving an illicit Collatz disproof, since repaired) and recommends multiple independent kernels, human audit of statements, supporting verified kernels. [READ]
- I could not find a separate Tao post titled on "misformalization"; the closest are the 9 Oct post above and the erdosproblems wiki guidance (misformalization warning signs: suspiciously short proof, proves more than asked, unused hypotheses). [READ]

## Workflow models
Blueprints and tooling
- leanblueprint (https://github.com/PatrickMassot/leanblueprint): `pip install leanblueprint`; `leanblueprint new`, `pdf`, `web`, `checkdecls`, `all`, `serve`; GitHub Actions template; publishes to GitHub Pages with API docs at /docs/. About 40 example projects listed. [READ] LeanArchitect (blueprint extraction for humans and AI provers) was presented at ITP 2026. [SNIPPET]
- doc-gen4 (https://github.com/leanprover/doc-gen4): add a `docbuild` subproject requiring doc-gen4; `lake build YourLib:docs`. [READ]
- Reservoir (https://reservoir.lean-lang.org/inclusion-criteria): public non-fork GitHub repo (template-generated counts as fork), root `lake-manifest.json`, OSI-approved license recognised by GitHub, at least 2 stars. [READ]
- CI: leanprover/lean-action@v1 with Mathlib cache by default; Dependabot recommended. [READ]
- Pinning: commit `lean-toolchain` and `lake-manifest.json`; the AxiomProver repos say other Lean versions (4.26.0) may not work. [READ]
- "Statement first, proof later": Tao's wiki procedure formalizes after review and has statements written by a human/third party; Ilin's project had the human pose the conjecture and check the final statement. [READ] Proposing problems to benchmarks: no source found this session; the Fields medalists' declaration criticizes using problems as benchmarks (see Ethics). [READ]
- Human-readable paper alongside Lean: AxiomProver papers state the human-written paper is for people and Lean files for the kernel. [READ]
- Multi-model review: Ilin used Gemini DeepThink (math), Claude Code (Lean), Aristotle (lemmas); Tao wiki recommends a critical AI review step. [READ]

Models (individuals, not labs). Honest caveat: I found one clearly individual project; the rest are lab or company projects.
1. Vasily Ilin, "Semi-Autonomous Formalization of the Vlasov-Maxwell-Landau Equilibrium", arXiv 2603.15929 (March 2026). Repo https://github.com/Vilin97/aristotle (branch `landau`); Reservoir page https://reservoir.lean-lang.org/@Vilin97/aristotle. Credible because: single mathematician supervising about 50 hours; all prompts, commits, logs public; an external Mathlib maintainer (Gouëzel) found and got a definition bug fixed; non-vacuousness theorem added; paper admits remaining unaudited definitions. About 10,445 lines, zero sorry (Reservoir listing, [SNIPPET]). Weaknesses: cost figures conflict across sources; no formal AI-disclosure section found. [READ unless noted]
2. Nikhil Garg's EconCSLib (a researcher formalizing his own papers; 11 papers). Only seen in a search snippet; not fetched. [SNIPPET]
3. Company case studies, useful as templates but not individuals: AxiomMath/dead-ends and AxiomMath/partial-regularity (problem.lean = statement, solution.lean = proof, Lean 4.26.0 pinned; human-written paper). [READ] Dead-ends was later found to restate Mirsky 1947 (see Novelty).
- Not found: a small, individual-run, well-regarded blueprint project that I could verify. The leanblueprint README list is the place to look; I did not open individual entries.

## Discovery methods
For each: result type, and a 2025-26 example by an individual. I could not verify an individual-author example for any method this session (limited searches); where the table says "none verified" that is a real gap.

| Method | Yields | 2025-26 individual example |
|---|---|---|
| PSLQ / LLL integer relations (Bailey-Borwein practice) | Conjectured identities and BBP-type formulas, then proved separately | None verified. Search found only a self-published May 2026 dev.to draft whose own scope section says PSLQ found only classical rewritings [SNIPPET, weak]. |
| Ramanujan Machine / Ramanujan Library | Continued-fraction and constant formulas, conjectures | Team work: Ramanujan Library (Technion team) generated 75 new formulas with PSLQ, ICLR 2025 [SNIPPET]. Not individual. |
| OEIS-driven conjecturing | Conjectures and sequence connections; JIS wants OEIS-linked papers | None verified. JIS scope statement read [READ]. |
| AlphaEvolve / FunSearch-style search | Constructions and small bound improvements | Lab work: Quanta (Apr 2026) says AlphaEvolve improved 23 of 67 problems slightly [SNIPPET]; arXiv 2511.02864 DeepMind plus mathematicians [SNIPPET]. FunSearch details from memory, unverified. |
| Computer algebra: WZ, creative telescoping, HolonomicFunctions, Sigma | Machine proofs of identities and recurrences | Not searched; from memory, unverified. |
| SAT/SMT with verified certificates | Finite combinatorial results with checkable proofs | Not searched; from memory, unverified. |
| AI prover plus Lean (AxiomProver, Aristotle, Gemini DeepThink plus Claude Code) | Proofs of stated conjectures with Lean files | Ilin (individual, above) [READ]; AxiomProver papers (company) [READ]. |

## Novelty-checking procedure
Recommended by Tao's erdosproblems wiki FAQ "What to do when I think I managed to get AI to solve an Erdős problem?" [READ]:
1. Check you can explain the argument and each hypothesis's use without the AI output.
2. Check the problem statement against the original sources (you may have solved a different version).
3. Literature review: Google Scholar, MathSciNet, zbMATH; forward and backward citation searches from the key papers; AI deep-research as an aid; ask a domain expert, respecting their time.
4. Compare with the literature; warning signs are a suspiciously short or elementary proof, proving more than asked, unused hypotheses.
5. Get a critical AI review (ask for criticism explicitly).
6. Write to professional standards.
7. Formalize in Lean with an independently reviewed statement; watch for exploits.
8. Post on the problem's forum with links and summaries.
9. Do not publicize widely until the community has responded.
What the maintainers/Tao say about rediscoveries [SNIPPET unless noted]: Oct 2025 OpenAI claims about "open" problems turned out to be literature already existing; Tao reportedly said AI helped move about 100 problems to "solved" mostly via literature search; he warned of survivor bias; the wiki (data as of 30 Jun 2026, no longer updated) has categories distinguishing AI alone, AI alongside later-found literature, AI building on known literature, and notes obscurity vs difficulty [READ]. I could not fetch erdosproblems.com (HTTP 403).
A concrete rediscovery case [READ]: the AxiomMath "Dead ends in square-free digit walks" paper carries an update that Soundararajan pointed out Mirsky (1947) had the main result; the authors will not submit it for journal publication.
Tools for novelty checks: zbMATH Open, MathSciNet, OpenAlex citation graphs, MathOverflow, emailing the closest paper's authors, arXiv posting. These are named in the task; I did not fetch pages for them, so no claims about their current features. Tao wiki names Google Scholar, MathSciNet, zbMATH explicitly [READ].

## Being taken seriously (do / do not)
Do
- State the theorem plainly, give the shortest human-readable proof you can, and separate "what Lean checks" from "what is interpretation" (Buzzard; Leiden "support the needs of reviewing"). [READ]
- Make a reproducible artifact: public repo, pinned toolchain, statement file, CI, comparator output. [READ]
- Give precise and complete references; if attribution is incomplete say so (Leiden). [READ]
- Disclose AI use, specifically (JIS requires "explicit, detailed description"; arXiv requires reporting significant use; Leiden asks for a tool-use section). [READ]
- Explain why the result is interesting and how it connects (Calegari guest post: judge work as if AI-assisted, ask what ideas it adds). [READ]
- Allow time for expert review before announcing (Tao wiki step 9; Fields declaration warns against rushed announcements). [READ]
Do not
- Do not let a model write the paper text for journals with such rules (JIS forbids LLM-written text, names ChatGPT, Claude, Grok, Gemini). [READ]
- Do not claim proofs of famous conjectures at JIS (immediate rejection for Goldbach, RH, Collatz). [READ]
- Do not rely on a Lean badge as proof the statement is right. [READ]
- Do not mass-submit; arXiv caps and May 2026 penalty for unchecked LLM output (a 1-year ban then venue-first requirement) reported, with disputed timing. [SNIPPET]
- Editors' red-flag lists beyond these (desk-reject patterns): no primary source found this session beyond the above; I could not confirm a general editor survey. Tao's MathHelm post says mathematicians have no obligation to check AI-generated papers. [READ]

## Venues table
| Venue | Unaffiliated authors | AI policy | Notes |
|---|---|---|---|
| arXiv | Allowed, but first submission needs endorsement (institutional email helps; or personal endorsement from an author with qualifying papers 3 months to 5 years old) [READ] | Report significant use; AI cannot be an author; authors fully responsible [READ] | Cap: 2 submissions per calendar month, max 3 active, from 1 Oct 2026, described as stopgap; announced papers do not count; rejected count [READ via Register and arXiv blog]. Endorsement page itself does not mention the cap. |
| Zenodo (DOI) | Yes: "anyone may register"; must have rights; license required [READ] | Page links to a separate "AI usage notice" I did not read | Not peer reviewed; DOI revoked if out of scope. |
| GitHub + Reservoir | Yes | n/a | Needs OSI license, 2 stars, root manifest [READ]. |
| Lean Zulip | Open community (from memory, unverified) | not checked | Good for statement review. |
| Journal of Integer Sequences | No affiliation requirement stated; free; email to editor [READ] | Strict: no LLM-written text; AI help allowed only with explicit credit and checking; undisclosed use means rejection [READ] | Needs LaTeX, OEIS links; no brute-force term computation. |
| INTEGERS | Not stated; no fees [READ] | Not stated on main page | Submission guidelines page not read. |
| Annals of Formalized Mathematics | Not stated [READ] | Not stated on page read | Needs a code artifact; diamond open access. |
| Formalized Mathematics (Mizar) | Not stated [READ] | Not stated | Mizar-checked only, so not for Lean. |
| Experimental Mathematics | Not checked (403) | Not checked | Fits PSLQ-style results; from memory, unverified. |
| AFP (Isabelle) | Not checked (404) | Not checked | Isabelle only. |
| HAL | Not checked | Not checked | |
| viXra | Open | AI-assisted work not accepted on viXra; goes to ai.viXra.org; rxiVerse accepts with or without AI [READ] | Reputation issue: founded as response to arXiv moderation [READ]; a mark of low standing is common view, from memory, unverified. |
| MathHelm (Tao post 13 Nov 2026) | Real names; post does not say affiliation required (comments claim institutional email; unconfirmed) [READ] | Forum is neutral on AI | For discussion of AI papers, not publication. |

## AI-contribution statements
Real examples (paraphrased):
1. AxiomMath/Ono et al., arXiv 2602.05090 (4 Feb 2026) and 2602.05095: humans wrote the paper without AI; AxiomProver produced the Lean statement formalization and proof from a natural-language statement with no human assistance; Lean version pinned; repository linked. [READ] Note the same group's second paper was found to be a rediscovery (Mirsky 1947) and withdrawn from journal plans.
2. Ilin, arXiv 2603.15929 (Mar 2026): Gemini DeepThink supplied the natural-language proof, Claude Code wrote all the Lean from prompts, Aristotle proved lemmas; the human posed the problem and checked the statement; prompts and commits public. [READ]
A third (2026 arXiv paper saying Claude-family agents were instruments under the author's direction, all claims kernel-checked, following the journal's AI policy) is [SNIPPET] only; I did not identify the paper.
Template, following the Leiden Declaration's five recommendations [READ]: (a) which tools, for what; (b) what humans wrote and checked; (c) what Lean verifies and who audited the statement; (d) which prior work was searched and how; (e) a sentence that the authors take responsibility for correctness and attribution; (f) a link to prompts or logs if feasible.
Declarations. Leiden Declaration on AI and Mathematics: published 2 Jun 2026 on Zenodo (DOI 10.5281/zenodo.20302944); IMU circular 8/2026 dated 2 Jun 2026 links to it, and the IMU is said to have endorsed it [SNIPPET]; EMS (the Edinburgh Mathematical Society, not the European one) welcomed it on 12 Jun 2026 [READ]. Five individual recommendations read at leidendeclaration.ai [READ]: disclose tool use; support reviewing; retain responsibility for correctness; affirm humanity of authorship; put effort into attribution. Fields medalists' declaration: 11 Sep 2026, on Tao's blog, 25 signatories at start: benchmark-driven problem solving harms mathematics; announce with proper writeups; isolate methods; cite prior work [READ]. Association for Human Mathematics (https://www.ahmath.org/statements): Communications Working Group statements (about 7 Oct 2026 responding to OpenAI's release of 6 Oct; 20 Nov 2026 on the RH proof): critical of corporate AI, calls for independence from AI companies [READ]. DMV presidium position paper (date not seen): binding journal disclosure rules, human responsibility, formal verification not a substitute for human understanding [READ]. AMS and LMS statements: not found. IMU full circular text not readable (PDF). The task's mention of the "Association for Human Mathematics position" matches the AHM page; the primary text for the 21 Nov RH statement was not separately read.

## Queries used (8 of 8 WebSearch)
1. Fields medalists declaration artificial intelligence mathematics 2026 Leiden declaration
2. arXiv October 2026 submission limit policy AI-generated papers new rule
3. erdosproblems.com AI solution already in literature Terence Tao literature search rediscovery
4. solo author AI-assisted Lean 4 formalization repository blueprint Mathlib 2026 independent researcher new theorem GitHub
5. 2026 independent mathematician PSLQ OR "Ramanujan Machine" OR AlphaEvolve new formula discovered arXiv individual author
6. AMS EMS LMS IMU statement use of AI in mathematical publishing 2026 journals policy authors disclosure
7. arXiv 2026 mathematics paper "AI contribution statement" OR "use of AI" acknowledgment Lean verified proof generated with GPT Claude Gemini
8. Vasily Ilin Vlasov-Maxwell-Landau Lean formalization GitHub repository Gemini DeepThink Claude Code (the author name came from search 4's result)

## Pages fetched
Buzzard Xena post; leanprover-community blog front page (RH statement); arXiv endorsement page; comparator repo; Tao blog front page; erdosproblems.com/faq (403); Demoura kernel post; Lean ref manual ValidatingProofs; Tao 9 Oct 2026 post; MathHelm post; Tao 21 Nov and 6 Nov posts; AHM statements; Etingof PDF (unreadable); Tao 1 Nov post (Calegari guest); DMV paper; Zenodo Leiden record and PDF (headings only); The Register article; arXiv rate-limit blog; Tao erdosproblems wiki pages (AI contributions, FAQ); Tao 11 Sep post; arXiv moderation page; leanblueprint, lean-action, Reservoir and its inclusion criteria, doc-gen4; JIS, AFM, INTEGERS pages; arXiv 2602.05090 (abs and html), 2602.05095, 2602.13695 (unreadable), 2605.22763 (unreadable); leidendeclaration.ai; EMS (Edinburgh) page; IMU circular (unreadable); Ilin arXiv html; Zenodo policies; Formalized Mathematics; vixra.org. Failed: erdosproblems.com FAQ (403), Experimental Mathematics instructions (403), AFP submitting page (404), Lean blog posts index (404), leanblueprint under leanprover-community (404).

## Sources
- https://xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/
- https://leanprover-community.github.io/blog/ (RH statement, 21 Nov 2026)
- https://github.com/leanprover/comparator
- https://lean-lang.org/doc/reference/latest/ValidatingProofs/
- https://leodemoura.github.io/blog/2026-10-15-lean-now-ships-with-verified-kernels/
- https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/
- https://terrytao.wordpress.com/2026/09/11/a-severe-misalignment-of-ai-in-mathematics/
- https://terrytao.wordpress.com/2026/11/01/mathematics-has-changed-lets-act-like-it/
- https://terrytao.wordpress.com/2026/11/13/introducing-mathhelm-a-place-to-discuss-ai-generated-papers/
- https://github.com/teorth/erdosproblems/wiki (AI contributions page; FAQ "What to do when I think I managed to get AI to solve an Erdős problem?")
- https://info.arxiv.org/help/endorsement.html ; https://info.arxiv.org/help/moderation/index.html ; https://blog.arxiv.org/2026/10/01/updated-rate-limit-policy/ ; https://theregister.com/ai-and-ml/2026/10/02/arxiv-imposes-rate-limit-on-paper-submissions-to-stem-the-ai-slop-tide/5300899
- https://leidendeclaration.ai ; https://zenodo.org/records/20302944 ; https://www.ems.ac.uk/2026/06/leiden-declaration-on-artificial-intelligence-and-mathematics/
- https://www.ahmath.org/statements ; https://www.mathematik.de/dmv-blog/5362-dmv-pr%C3%A4sidium-zur-bedeutung-der-ki-f%C3%BCr-die-mathematik
- https://github.com/PatrickMassot/leanblueprint ; https://github.com/leanprover/lean-action ; https://github.com/leanprover/doc-gen4 ; https://reservoir.lean-lang.org/inclusion-criteria
- https://cs.uwaterloo.ca/journals/JIS/ ; https://afm.episciences.org/ ; https://math.colgate.edu/~integers/ ; https://about.zenodo.org/policies/ ; https://vixra.org/ ; https://reference-global.com/journal/FORMA
- https://arxiv.org/abs/2602.05090 ; https://arxiv.org/html/2602.05095 ; https://arxiv.org/html/2603.15929 ; https://github.com/Vilin97/aristotle
