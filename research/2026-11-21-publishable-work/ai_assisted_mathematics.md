# AI-assisted research mathematics, 2023 to November 2026: what is real, how it was received, and the rules for publishing it

Research date: 21 November 2026. Source handling: items marked (search summary) come from a search-result summary whose page I did not open; everything else was read from the linked page. Nature, Science, NPR, the AMS policy page, the COPE statement and erdosproblems.com refused or timed out on direct fetch, so anything attributed to them is secondhand and flagged. Direct quotation is kept to a minimum; statements are paraphrased with attribution.

## 1. The Alpöge / Claude Riemann Hypothesis claim, and other claimed AI proofs of famous conjectures (2024-2026)

### Takeaway
The claim is real and one day old: on Friday 20 November 2026 Levent Alpöge (Anthropic) posted a four-page note and a 14-part Lean 4 archive claiming a proof, found with Claude, of the Riemann Hypothesis and of GRH for Dirichlet L-functions. As of 21 November the Lean code has been independently compiled and kernel-checked, and the Lean and Mathlib communities say they are fully confident that both statement and proof are correct, but there is no human-readable proof, no peer review, no expert has yet digested the argument, and the Clay Institute still lists the problem as unsolved.

### Cited Findings

The claim itself
- Alpöge's note says: "I believe I have, working with Claude, discovered a proof of the Riemann Hypothesis", adds that the method extends to the Generalized Riemann Hypothesis and that he expects the Extended Riemann Hypothesis to follow with more time, and gives the proof only as fourteen files `lean.tar.gz.part01` to `part14` on his site — [Alpöge, "Remark" (PDF)](https://alpo.ge/remark.pdf)
- Date and venue: posted on his personal website on Friday 20 November 2026; Scientific American ran it as breaking news the same day and describes him as a mathematician employed by Anthropic — [Scientific American, 20 Nov 2026](https://www.scientificamerican.com/article/anthropic-mathematician-claims-to-prove-riemann-hypothesis-most-famous-problem-in-all-of-math/)
- The six-weeks figure: the note does not use that phrase, but the Claude-compiled timeline in it dates the proof ingredients from 6 October 2026 (a Stepanov-type determinant) to 16 November 2026 (the entry for GRH itself), i.e. 41 days. The note also says the decisive steps came late on Sunday night (15 November) and that he and Claude had been working broadly together over recent months — [Alpöge, "Remark"](https://alpo.ge/remark.pdf); a secondary write-up describes the development as taking several months — [CASRAI, 21 Nov 2026](https://casrai.org/news/anthropic-levent-alpoge-claude-lean-riemann-hypothesis-claim-2026)
- Division of labor as he describes it: he steered toward the right setting; Claude outpaced him near the end, and he says he has little mastery of automorphic forms on higher-rank groups, which the argument uses. He states that parts of his own timeline paraphrase a model-written summary that may not make sense, and that he chose to release Lean only rather than an unreadable document (his footnote says a prose rendering exceeded 250,000 pages) — [Alpöge, "Remark"](https://alpo.ge/remark.pdf)
- Which model: not stated in the note. Tao describes it as an internal AI model — [Tao, 20 Nov 2026](https://terrytao.wordpress.com/2026/11/20/unforced-euler-singularity-unforced-navier-stokes-singularity-and-the-generalized-riemann-hypothesis/); press coverage says the specific Claude version is not identified — [IBM Think, 20 Nov 2026](https://www.ibm.com/think/news/anthropic-claude-riemann-hypothesis-math-proof)
- Size: 175,187 Lean 4 files in 14 tar parts totalling 239.3 MB, more than 61.5 GB unpacked — [CASRAI](https://casrai.org/news/anthropic-levent-alpoge-claude-lean-riemann-hypothesis-claim-2026); about 17 million lines of Lean — [Lean community blog, 21 Nov 2026](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)
- Timing controversy: the post came one day after Anthropic began trading on Nasdaq (19 November); Alpöge writes that the cynical reading of the timing is false and that he consulted Dario Amodei and a few mathematicians before posting — [The Next Web](https://thenextweb.com/news/anthropic-alpoge-claude-riemann-hypothesis-proof-lean); [Alpöge, "Remark"](https://alpo.ge/remark.pdf)

Verification status (as of 21 November 2026)
- Andrew Sutherland (MIT) reports: all 175,187 modules compile under Lean v4.33.1 / Mathlib v4.33.1 with no errors; the five headline theorems depend only on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`); Mathlib files match the official cache byte for byte; independent kernels (nanoda, con-leche, leanchecker, lean4lean) accept the exported proof. Page last updated 21 Nov 2026 12:55 UTC with some checks (default and paranoid kernel runs, end-to-end `lake comparator`) still running. He ran the checks using Claude Code — [Sutherland verification page](https://math.mit.edu/~drew/grh/)
- What the Lean file proves: (1) RH as Mathlib's `RiemannHypothesis`; (2) a restatement; (3)-(5) non-vanishing and critical-line statements for every Dirichlet L-function, including the usual primitive-character GRH. Scope limit: Dedekind zeta, Hecke and general automorphic L-functions are not covered. Combined with an existing formalization of Robin's 1984 theorem it yields Robin's and Lagarias's inequalities unconditionally — [Sutherland verification page](https://math.mit.edu/~drew/grh/)
- The Lean and Mathlib communities, in a joint statement endorsed by the Lean FRO and the Mathlib Initiative (21 Nov 2026, 13:55), say they are fully confident the proof is correct: the statement is Mathlib's own expert-vetted definition, dozens of people reproduced the build, `comparator` and `con-leche --compare` confirm the proved theorem is exactly Mathlib's statement, and several independent checkers accept the exported proof — [Lean community blog](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)
- Not yet done: no human-readable paper, no journal submission, no peer review; Alpöge says he intends to understand, simplify and write it up — [Alpöge, "Remark"](https://alpo.ge/remark.pdf); [The Next Web](https://thenextweb.com/news/anthropic-alpoge-claude-riemann-hypothesis-proof-lean)
- Clay Mathematics Institute's page still shows the Riemann Hypothesis as Unsolved and mentions no claim — [Clay Mathematics Institute](https://www.claymath.org/millennium/riemann-hypothesis/). Secondary reports say the prize rules need publication in a qualifying venue, a two-year wait and general acceptance, so no award before 2028 — [DataCamp, 20 Nov 2026](https://www.datacamp.com/blog/ai-solved-riemann-hypothesis)

Reception among mathematicians
- Terence Tao lists it last of three Alpöge-linked results in decreasing order of how digested they are, says digestion will take time, that very early analysis suggests the proof uses the full strength of modern Langlands-program and arithmetic-geometry developments, and points to the Lean Zulip thread as the place to follow verification — [Tao, 20 Nov 2026](https://terrytao.wordpress.com/2026/11/20/unforced-euler-singularity-unforced-navier-stokes-singularity-and-the-generalized-riemann-hypothesis/)
- Sutherland called it a historic moment and said much work remains to understand the mathematics; Hector Pasten and Carlo Pagano gave conditional, positive comments — [Scientific American](https://www.scientificamerican.com/article/anthropic-mathematician-claims-to-prove-riemann-hypothesis-most-famous-problem-in-all-of-math/)
- James Maynard (Oxford) said he suspects the proof will turn out correct and that it would be a historic milestone, but that verifying it may not explain why it works; Youness Lamzouri said understanding could take months or years — [IBM Think](https://www.ibm.com/think/news/anthropic-claude-riemann-hypothesis-math-proof)
- Criticism: Brian Conrad (Stanford) is reported, via the New York Times, to have strongly objected to releasing a proof its author does not fully understand; the same report has Maynard at 98-99 percent confidence (secondhand; NYT not opened) — [The Next Web](https://thenextweb.com/news/anthropic-alpoge-claude-riemann-hypothesis-proof-lean)
- Elliot Glazer posted that the formalized statement really is GRH and that a Lean bug is technically possible but unlikely; Thomas Bloom posted that Lean experts were investigating — [OfficeChai round-up of X posts, 20 Nov 2026](https://officechai.com/ai/how-mathematicians-have-reacted-to-claimed-riemann-hypothesis-proof-by-anthropics-levent-alpoge/)
- Same-day human rival: AMS president Ravi Vakil posted an all-human draft by Alessandro Masullo claiming GRH, which Conrad had been checking for months; about eight hours later Vakil reported that several people had found problems in it using AI models — [The Next Web](https://thenextweb.com/news/anthropic-alpoge-claude-riemann-hypothesis-proof-lean); [DataCamp](https://www.datacamp.com/blog/ai-solved-riemann-hypothesis). Tao says the Masullo manuscript is closer to Deninger's strategy and will also take time to digest — [Tao, comments, 20 Nov 2026](https://terrytao.wordpress.com/2026/11/20/unforced-euler-singularity-unforced-navier-stokes-singularity-and-the-generalized-riemann-hypothesis/)

Earlier Riemann-related AI results (not proofs of RH)
- 10 August 2026: Anthropic reported that an unreleased research version of Claude raised the proven proportion of zeta zeros on the critical line from 41.6% to 67.2%, as a by-product of a request to attempt RH itself; two Claude Code sessions, about 31 million output tokens, about 60 subagents; checked by Alpöge and Ralph Furman internally and by Brian Conrey and Dan Goldston externally on short notice; Lean formalization on GitHub; Anthropic said it did not expect the techniques to lead to RH — [Anthropic research post](https://www.anthropic.com/research/riemann-zeta)
- Scientific American's headline was that AI had not solved RH; Maynard said the result seemed to supply a needed new idea but offered no pathway to RH, and called Anthropic's post restrained — [Scientific American, 12 Aug 2026](https://scientificamerican.com/article/no-ai-didnt-just-solve-the-thorniest-problem-in-math)
- 6 October 2026: OpenAI released a claimed quasi-Riemann hypothesis: version 1 (199 pages, dated 30 Sept) puts all nontrivial zeros in 1/8 < Re s < 7/8 and is Lean-verified; version 2 (49 pages) gives 1/12 to 11/12 and is not yet formally verified. Experts (Sarnak, Radziwiłł, Dunn, Lichtman) studied the shorter paper for weeks and largely agree it is correct; Radziwiłł says the exposition falls well short of the field's standards; Sawin doubts the method reaches 1/2; Sarnak will not call it a theorem until humans check all details — [Quanta, 19 Oct 2026](https://quantamagazine.org/ai-proved-the-quasi-riemann-hypothesis-what-happens-now-20261019)

Other famous conjectures
- Navier-Stokes: on 8 September 2026 OpenAI announced that an internal model (described as significantly more capable than GPT-6 Astra; about 10,000 concurrent agents, about 88 hours, roughly 130 billion output tokens) proved finite-time blow-up for 3D incompressible Navier-Stokes with a smooth force, which it says establishes statements C and D of the Clay formulation; Lean repo published; author listed as OpenAI; OpenAI says it will not claim the prize — [OpenAI announcement](https://openai.com/index/navier-stokes-solution/)
- That claim is contested on two fronts. Credit: Tristan Buckmaster (NYU) alleged OpenAI learned of his and Alpöge's progress and used the same method; Bubeck denied using their prompts or proofs but said the Navier-Stokes proof used a similar method — [Scientific American, 8 Sept 2026](https://scientificamerican.com/article/openai-claims-blockbuster-math-breakthrough-amid-swirl-of-controversy). Fidelity: Bastounis, Circelli and Hansen argue the Lean formalization does not correspond to the natural-language blow-up proof, so the Lean check does not validate the paper — [arXiv:2610.08144](https://arxiv.org/abs/2610.08144)
- On 20 November 2026 Tao also reported a human-readable, Lean-formalized blow-up proof for unforced 3D Euler (Alpöge, Buckmaster, Coiculescu, heavy AI assistance) and a Lean-formalized blow-up proof for unforced 3D Navier-Stokes (Alpöge, Buckmaster) that he calls technically human-readable with a broadly clear strategy but still needing a professional write-up — [Tao, 20 Nov 2026](https://terrytao.wordpress.com/2026/11/20/unforced-euler-singularity-unforced-navier-stokes-singularity-and-the-generalized-riemann-hypothesis/)
- Jacobian conjecture (July 2026): a degree-seven polynomial map in three dimensions with constant Jacobian determinant -2 that sends three distinct points to one point, found using Anthropic's Fable model and announced by Alpöge; Tao says a brief calculation verifies it and that the conjecture remains open in two dimensions — [Tao, 21 July 2026](https://terrytao.wordpress.com/2026/07/21/a-digestion-of-the-jacobian-conjecture-counterexample/); checked in Lean within a day; Akhil Mathew (who suggested the problem) said it is checkable but lacks a story — [Fortune, 21 July 2026](https://www.fortune.com/2026/07/21/ai-solves-jacobian-conjecture-levant-alpoge-claude-fable-5/)
- Collatz: on 25 July 2026 Ramana Kumar published an AI-assisted Lean project presented as a disproof, accepted by Lean and by the independent checker nanoda; it turned out to exploit a Lean kernel soundness bug (nested inductive types) plus a separate nanoda bug. Fixed in Lean 4.32.2 on 28 July. Collatz remains open — [GIGAZINE, 3 Aug 2026](https://gigazine.net/gsc_news/en/20260803-collatz-lean-kernel-bug/)
- Twin primes / bounded gaps: no proof of the twin prime conjecture. The bound on infinitely recurring prime gaps went 246 to 240 (Julia Stadlmann, human, 31 Aug 2026), to 212 (Axiom Math, AI theorem prover, about three days later), to 186 (OpenAI GPT-6 Astra, 3 Sept 2026). Mathematicians were still digesting OpenAI's paper, and several criticized OpenAI for working on the same problem without contacting Stadlmann — [Science News](https://www.sciencenews.org/article/human-math-record-twin-primes-openai)
- Goldbach: no accepted proof found; AI-assisted "proofs" exist on the unrefereed ai.viXra archive (search summary) — [ai.viXra number theory listing](https://ai.vixra.org/numth/)

### Inferences
- The RH claim has cleared the formal-proof bar the brief set (independent builds, statement match against Mathlib, multiple kernels), which is far more than any earlier claimed RH proof, but it is still under 48 hours old and has cleared nothing on the human side. The prudent wording is: formally verified according to the Lean community, not yet understood, not peer reviewed, not accepted by Clay.
- The July 2026 Collatz episode is the reason the multi-kernel and comparator checks matter; the RH archive was checked by more independent kernels than that exploit defeated, and Buzzard argues a simultaneous break of many kernels is not a practical concern (see section 7).
- Three of the largest 2026 claims (Jacobian, unforced Navier-Stokes, GRH) trace to one person with privileged access to unreleased Anthropic models, and the OpenAI results use unreleased OpenAI models. None of this is reproducible by an amateur with public tools.

### Gaps
- Nature and Science articles on the RH claim exist ([Nature](https://www.nature.com/articles/d41586-026-03812-7), [Science](https://www.science.org/content/article/ai-may-have-solved-math-s-greatest-mystery-can-humans-understand-answer)) but could not be opened; the NYT quotes from Conrad and Maynard are secondhand.
- I found no official Anthropic statement about the RH claim and no statement from Buzzard, Gowers, Litt or Kedlaya on it (search budget ran out before I could look specifically).
- Whether any expert has found a mathematical gap, or a problem with Mathlib's definitions, is unknown this early.
- P vs NP: no credible AI-assisted claim surfaced in anything I read; I could not run a dedicated search.
- Current status of the OpenAI forced Navier-Stokes proof after the "lost in translation" critique is unconfirmed; the NPR follow-up timed out.

## 2. Verified AI results in mathematics, 2023-2026

### Takeaway
There is a solid record of real results, moving from constructions and bound improvements (2023-2025) through autonomous solutions of obscure-to-moderate open problems (early 2026) to results experts call journal-worthy (unit distance, May 2026) and claimed resolutions of major problems (autumn 2026). The repeated failure modes are rediscovery passed off as novelty, unverified volume, weak exposition, and formalizations that do not match the paper.

### Cited Findings

2023-2025
- FunSearch (DeepMind, Dec 2023, published in Nature): an LLM proposing programs plus an automated evaluator found the largest cap sets then known in some settings, described as the largest increase in 20 years — [DeepMind blog, 14 Dec 2023](https://deepmind.google/discover/blog/funsearch-making-new-discoveries-in-mathematical-sciences-using-large-language-models/)
- IMO 2024: AlphaProof plus AlphaGeometry 2 scored 28/42 (silver level), solving four of six problems after humans translated the problems into Lean and with up to three days of compute; AlphaProof's methodology paper appeared in Nature on 12 Nov 2025 — [DeepMind blog, 25 July 2024](https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/)
- IMO 2025: Gemini Deep Think scored 35/42 (gold), five of six problems, in natural language within the 4.5-hour limit, graded by IMO coordinators — [DeepMind blog, 21 July 2025](https://deepmind.google/discover/blog/advanced-version-of-gemini-with-deep-think-officially-achieves-gold-medal-standard-at-the-international-mathematical-olympiad/). Harmonic's Aristotle reported gold-equivalent performance with Lean-verified proofs — [arXiv:2510.01346](https://arxiv.org/abs/2510.01346)
- AlphaEvolve (May 2025): 4x4 complex matrix multiplication in 48 scalar multiplications; kissing number lower bound in 11 dimensions raised to 593; on 50+ open problems it matched the state of the art in about 75% and improved it in about 20% — [DeepMind blog, 14 May 2025](https://deepmind.google/discover/blog/alphaevolve-a-gemini-powered-coding-agent-for-designing-advanced-algorithms/)
- Georgiev, Gómez-Serrano, Tao and Wagner tested AlphaEvolve on 67 problems in analysis, combinatorics, geometry and number theory: mostly rediscovery of best-known constructions, several improvements, some finite results generalized to formulas — [arXiv:2511.02864](https://arxiv.org/abs/2511.02864)
- Equational Theories Project (Tao and 33 co-authors): all 22,028,942 implications among 4,694 magma laws settled by a mix of human and automated proofs, all validated in Lean — [arXiv:2512.07087](https://arxiv.org/abs/2512.07087)
- GPT-5 in research: an 89-page OpenAI-led paper with Gowers and Sawhney among the authors reports four new mathematical results verified by the human authors and describes the contributions as modest in scope — [arXiv:2511.16072](https://arxiv.org/abs/2511.16072)

Erdős problems and the literature-search dispute
- October 2025: OpenAI's Kevin Weil posted that GPT-5 had solved 10 open Erdős problems; the solutions were already in the literature and the post was deleted (search summary) — [GIGAZINE, 20 Oct 2025](https://gigazine.net/gsc_news/en/20251020-openai-researcher-announced-gpt-5-math-breakthrough); Thomas Bloom had called that post a dramatic misrepresentation — [Slashdot summary of TechCrunch, 21 May 2026](https://science.slashdot.org/story/26/05/21/0351218/openai-claims-it-solved-an-80-year-old-math-problem)
- Scientific American reported about 100 Erdős problems moved to solved with AI help since October 2025, mostly by enhanced literature search (search summary) — [Scientific American](https://www.scientificamerican.com/article/ai-uncovers-solutions-to-erdos-problems-moving-closer-to-transforming-math/)
- DeepMind's Gemini study screened 700 problems marked open: 13 addressed, of which 5 were apparently novel autonomous solutions and 8 already existed in the literature; the authors attribute open status to obscurity rather than difficulty and warn of subconscious plagiarism by AI — [arXiv:2601.22401](https://arxiv.org/abs/2601.22401)
- The community wiki tracking AI contributions (frozen at 30 June 2026) lists 19 fully resolved entries (18 problems) in its strictest class (AI standalone, no comparable literature known, non-significant human involvement), six of them formalized in Lean, credited variously to GPT-5.2/5.4/5.5 Pro, OpenAI internal models, Aristotle, DeepMind agents, Aletheia, Claude Mythos and Claude Fable 5. It also lists about 10 incorrect entries in that class, and carries disclaimers on selection bias, obscurity versus difficulty, incomplete literature review, and that an Erdős solution is not automatically a publishable paper — [AI contributions wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)
- May 2026: a second DeepMind study reports its agent autonomously resolved 9 of 353 formally stated open problems at a few hundred dollars each — [Quanta, 3 Aug 2026](https://quantamagazine.org/why-the-legendary-erdos-problems-are-falling-to-ai-20260803)
- 20 May 2026, unit distance problem: an internal OpenAI general-purpose model disproved Erdős's 1946 conjecture by giving configurations with at least n^(1+δ) unit distances; external mathematicians checked it and wrote a companion paper; Gowers called it a milestone, Tsimerman said he would accept it for any journal, Sawin extracted δ = 0.014. Author listed as OpenAI; hosted on OpenAI's site, not arXiv — [OpenAI, 20 May 2026](https://openai.com/index/model-disproves-discrete-geometry-conjecture/)
- 1 August 2026: OpenAI announced 10 more advances by an unreleased model called Astra, including three more Erdős problems — [Quanta, 3 Aug 2026](https://quantamagazine.org/why-the-legendary-erdos-problems-are-falling-to-ai-20260803); Gowers notes one was the first construction of a non-sofic group — [Gowers, 12 Aug 2026](https://gowers.wordpress.com/2026/08/12/what-sort-of-maths-are-llms-good-at/)

Bulk releases and benchmarks
- 6 October 2026: OpenAI published 722 manuscripts (372 result families, 17 fields) from an unreleased model; only 162 have a computer-checked main result and three were withdrawn within a day (search summary) — [DataCamp](https://www.datacamp.com/blog/openai-math-breakthroughs-what-the-latest-results-mean). Buzzard found that of 290 of these papers with Lean code, about 38 do not even state the paper's main theorem in Lean — [Xena project, 12 Nov 2026](https://xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/)
- FrontierMath: 338 problems (295 in Tiers 1-3, 43 in Tier 4); v2 (12 June 2026) corrected 123 Tier 1-3 and 12 Tier 4 problems; OpenAI funded the benchmark and has exclusive access to a subset (search summary) — [Epoch AI](https://epoch.ai/benchmarks/frontiermath)
- FrontierMath Open Problems (machine-checkable unsolved problems): of 49 listed, 5 are marked solved by AI, 5 solved by human + AI, 39 unsolved. A human + AI label was added on 16 Sept 2026 for cases where AI was instrumental but not autonomous. One provisional entry (Hadamard matrix of order 668) credits three humans and Claude — [Epoch AI Open Problems](https://epoch.ai/frontiermath/open-problems)
- Scale of adoption: among 32,944 arXiv mathematics submissions from 1 March to 20 August 2026, 3,575 disclosed AI use and 1,712 disclosed a substantive mathematical contribution; substantive use rose from 1.39% in March to 14.09% in August; 717 named open-problem claims, 71% self-described as fully resolved — [Jin, Ke and Sui, arXiv:2608.24961](https://arxiv.org/abs/2608.24961)

Results credited to Claude models
- Claude Opus 4.6 found the construction settling the odd case of a Hamiltonian-cycle decomposition problem Knuth had worked on for weeks, prompted by Filip Stappers; Knuth wrote the proof himself, Kim Morrison formalized it in Lean, and the even case was later handled with GPT-5.3-codex and GPT-5.4 Pro — [Knuth, "Claude's Cycles", 28 Feb 2026, revised 14 Apr 2026](https://www-cs-faculty.stanford.edu/~knuth/papers/claude-cycles.pdf)
- An internal Anthropic model formalized a complete proof of Fermat's Last Theorem in Lean (over 13.4 million lines, about 11 days); Buzzard compiled it, ran comparator and checked the statement himself, and says it tells us essentially nothing new mathematically but shows what autoformalization can do — [Xena project, 4 Sept 2026](https://xenaproject.wordpress.com/2026/09/04/flt-anthropic-has-beaten-me-to-it/)
- Others covered in section 1: zeta zeros 41.6% to 67.2% (unreleased Claude), Jacobian counterexample (Fable), Euler/Navier-Stokes blow-up and GRH (internal models).

Formulas for constants (Ramanujan Machine line)
- The Ramanujan Machine (2019 onward) generates conjectured continued-fraction formulas; the conservative matrix field (CMF) framework unifies many of them — [arXiv:2308.11829](https://arxiv.org/abs/2308.11829)
- "From Euler to AI" (NeurIPS 2025): LLMs harvested formulas from 455,050 arXiv papers; 385 distinct π formulas validated, relations proven for 360 (94%), and 166 (43%) derivable from a single CMF. LLMs did harvesting and validation; a symbolic algorithm did the unification — [arXiv:2502.17533](https://arxiv.org/abs/2502.17533)
- Ramanujan Challenge (July-August 2026): a benchmark of research-level number theory problems about formulas for constants; correct submissions included a proof of one published open conjecture; an AI-assisted judging pipeline cut false-positive verdicts on natural-language proofs from 23% to 6% — [arXiv:2610.40551](https://arxiv.org/abs/2610.40551)

### Inferences
- The hype-versus-real line that held through mid-2025 (AI = literature search plus optimization of constructions) no longer holds: by mid-2026 named experts accept some AI proofs as journal-quality. But the denominators are large (OpenAI kept 722 papers from about 4,000 problems posed, per search summary; DeepMind 9 of 353), incorrect entries are common, and vendor-authored announcements precede independent review.
- Even a one-shot LLM judge passed 23% of wrong natural-language proofs in the Ramanujan Challenge, which is a direct warning against using a chatbot as the only checker of an AI-produced proof.

### Gaps
- Nature pages for FunSearch and AlphaProof could not be opened; details come from DeepMind's blogs.
- I could not verify the OpenAI 722-paper figures against the repository README.
- Per-model FrontierMath scores for late 2026 were not retrieved.

## 3. Number theory specifically

### Takeaway
Number theory is where the largest 2026 claims sit, but the verified, attributable results an amateur could realistically emulate are small: elementary divisibility arguments (Erdős #728), counterexample and construction searches, improved numerical constants, and unification or proof of formulas for constants.

### Cited Findings
- Erdős #728 (math.NT): for suitable constants there are infinitely many triples with a!b! dividing n!(a+b-n)! and a+b-n of order log n; proved via Kummer's theorem and a counting argument by GPT-5.2 Pro, formalized by Aristotle, operated by Kevin Barreto; the write-up notes the strategy resembles earlier work of Erdős and Pomerance. Type: full proof of a minor open problem — [Sothanaphan, arXiv:2601.07421](https://arxiv.org/abs/2601.07421)
- Another Erdős problem solved by ChatGPT in about 15 minutes for Neel Somani used Legendre's formula and Bertrand's postulate and drew on a 2013 MathOverflow answer by Noam Elkies; formalized with Aristotle — [TechCrunch, 14 Jan 2026](https://techcrunch.com/2026/01/14/ai-models-are-starting-to-crack-high-level-math-problems/)
- Erdős #1196: resolved in a May 2026 paper co-authored by Tao, Lichtman, Barreto, Price and others; the wiki credits GPT-5.4 Pro (13 Apr 2026) — [Quanta](https://quantamagazine.org/why-the-legendary-erdos-problems-are-falling-to-ai-20260803); [AI contributions wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)
- Zeros on the critical line, 41.6% to 67.2% (unreleased Claude, Aug 2026): improvement of a constant by a new idea within an existing line of work (Bombieri; Baluyot-Goldston-Suriajaya-Turnage-Butterbaugh), Lean-verified — [Anthropic](https://www.anthropic.com/research/riemann-zeta)
- Bounded prime gaps 246 to 240 (human) to 212 (Axiom) to 186 (OpenAI): optimization of sieve weights building on a human's new idea — [Science News](https://www.sciencenews.org/article/human-math-record-twin-primes-openai)
- Quasi-RH (OpenAI, Oct 2026): full proof of a major statement via metaplectic forms and a 2021 Dunn-Radziwiłł formula; experts call it a surprising synthesis of known ideas — [Quanta](https://quantamagazine.org/ai-proved-the-quasi-riemann-hypothesis-what-happens-now-20261019)
- GRH for Dirichlet L-functions (Alpöge and Claude, Nov 2026): claimed full proof, Lean only — [Sutherland](https://math.mit.edu/~drew/grh/)
- FrontierMath Open Problems solved by AI include many rational points on a genus-2 curve (Diophantine), a genus-2 curve with a rational torsion point of prime order at least 31, and a presentation of the absolute Galois group of Q_2; an Apéry-style irrationality-proof problem is listed as solved by human + AI. These are construction or search problems with programmatic verifiers — [Epoch AI Open Problems](https://epoch.ai/frontiermath/open-problems)
- π: the AI-credited work is discovery and unification of formulas (Ramanujan Machine, CMF, 43% of validated π formulas from one object), not new theorems about π's arithmetic nature — [arXiv:2502.17533](https://arxiv.org/abs/2502.17533). An ICML 2026 paper reports an elementary proof that all 17 of Ramanujan's 1914 series for 1/π come from one CMF template (search summary) — [ICML 2026](https://icml.cc/virtual/2026/74816)
- Suvrit Sra reports more than 15 counterexamples found with GPT Pro over about a year, some in number theory — [arXiv:2608.29595](https://arxiv.org/abs/2608.29595)

### Inferences
- For an amateur's π-and-primes result, the closest accepted precedents are (a) a short, elementary, Lean-checked proof of a catalogued open problem and (b) a numerically checkable formula or bound with a proof. Both were received well only after a literature search and an independent or formal check.
- "Key idea credited to AI" in refereed number theory journals is still rare in what I could read; most credits are in preprints, vendor posts, or community databases.

### Gaps
- I could not open erdosproblems.com to confirm subject tags or the arXiv ID of the #1196 paper.
- Details of the Apéry-style irrationality result (which constants, which AI) were not retrievable.
- I found no AI-credited theorem on the irrationality or normality of π.

## 4. How experts describe capability and limits (2025-2026)

### Takeaway
Expert opinion shifted sharply during 2026, from useful-but-error-prone assistant to systems that resolve real open problems, with wide agreement that understanding, exposition, theory-building and attribution lag behind raw problem-solving.

### Cited Findings
- Tao (Jan 2026): counted eight Erdős problems with meaningful autonomous AI progress and six more built on located prior work; said AI suits the long tail of obscure problems with straightforward solutions — [TechCrunch, 14 Jan 2026](https://techcrunch.com/2026/01/14/ai-models-are-starting-to-crack-high-level-math-problems/). By September he criticized AI efforts that give up on human understanding in favor of benchmarks — [Science News](https://www.sciencenews.org/article/human-math-record-twin-primes-openai). He frames results by how digested they are — [Tao, 20 Nov 2026](https://terrytao.wordpress.com/2026/11/20/unforced-euler-singularity-unforced-navier-stokes-singularity-and-the-generalized-riemann-hypothesis/)
- Gowers: in May 2026 ChatGPT 5.5 Pro produced what he judged PhD-level research in about an hour with no serious input from him; he adds that impressive arguments often turn out to have precedents — [Gowers, 8 May 2026](https://gowers.wordpress.com/2026/05/08/a-recent-experience-with-chatgpt-5-5-pro/) (read via the blog's front-page excerpt); in August he noted the most famous AI solutions were mostly counterexamples and that LLMs are not better than all humans at all of mathematics — [Gowers, 12 Aug 2026](https://gowers.wordpress.com/2026/08/12/what-sort-of-maths-are-llms-good-at/); in September he expected publicly available models better at problem-solving than nearly all mathematicians, and predicted the credit system will collapse while insisting humans be credited properly meanwhile — [Gowers, 17 Sept 2026](https://gowers.wordpress.com/2026/09/17/why-i-didnt-sign-the-fields-medallists-letter/)
- Buzzard: models are solving hard problems humans could not, with far less evidence for theory-building or conjecture-making; AI-written mathematics is tiring to read, stresses trivialities and is vague on technical details — [Xena project, "To grieve, or not to grieve?", 1 Oct 2026](https://xenaproject.wordpress.com/2026/10/01/to-grieve-or-not-to-grieve/) (read via the blog's front page); [Xena project, "The Annals Challenge", 13 Aug 2026](https://xenaproject.wordpress.com/2026/08/13/the-annals-challenge/); in July 2026 he said current models cannot yet reliably produce long multi-step proofs without unjustified gap-filling — [Fortune](https://www.fortune.com/2026/07/21/ai-solves-jacobian-conjecture-levant-alpoge-claude-fable-5/)
- Litt: in Feb 2026, ChatGPT 5.2 Pro regularly proved lemmas that are involved but routine for experts while still making many errors, and he worried about polluting the commons with incorrect mathematics; by Sept 2026 he wrote that systems are autonomously resolving major open questions, still arguably behind humans at theory-building, asking questions and exposition, and that restricting AI use would only push people to conceal it — [Litt, "Mathematics in the Library of Babel", Feb 2026](https://www.daniellitt.com/blog/2026/2/20/mathematics-in-the-library-of-babel/) (excerpt read via the blog index); [Litt, 13 Sept 2026](https://www.daniellitt.com/blog/2026/9/13/a-beginning-for-mathematics/)
- Bloom: AI is heavily used by non-mathematicians who post 100-200 page papers no human has read or will read — [Quanta](https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/)
- Noga Alon stopped working on Erdős problems once AI began solving them; Jacob Tsimerman left academia for OpenAI in July 2026 — [Quanta](https://quantamagazine.org/why-the-legendary-erdos-problems-are-falling-to-ai-20260803)
- Fields medalists' declaration (11 Sept 2026; press reported 25 initial signatories, the site listed 28 names when read, including Tao, Scholze, Maynard, Viazovska, Deligne): AI companies' goals and the community's are severely misaligned; solving problems as a benchmark harms mathematics; it criticizes rushed announcements without proper write-ups, isolation of new methods, or citation of prior work — [mathandai.org](https://mathandai.org/); [Scientific American, 14 Sept 2026](https://www.scientificamerican.com/article/25-winners-of-maths-nobel-prize-decry-the-ai-invasion-of-their-discipline/)
- Leiden Declaration (over 3,000 signatures by July 2026): results must be attributable to human authors who take credit and responsibility, arguments transparent and independently verifiable, results published in peer-reviewed outlets; Gowers declined to sign over points he is unsure about, including whether AI-found results should be credited to humans at all — [Gowers, 26 July 2026](https://gowers.wordpress.com/2026/07/26/thoughts-about-the-leiden-declaration/)
- Barreto (who operated the #728 solution): current LLMs combine existing ideas well but cannot create the new concepts the hardest problems need — [Varsity, 6 Feb 2026](https://www.varsity.co.uk/science/31116). This was said nine months before the GRH claim.

### Inferences
- Statements about limits have a short shelf life; several January-to-July 2026 assessments were overtaken by autumn. A report should date every expert quote.
- The durable consensus is about norms rather than capability: correct but undigested is not accepted mathematics, and attribution to prior literature is the commonest failure.

### Gaps
- No statement by Kiran Kedlaya was found.
- The Academy for the Mathematical Sciences report (Oct 2026) returned 403 and was not read.
- Tao's own September 2026 posts on the declaration were not located; his blog that month was mostly guest posts.

## 5. Publishing norms: arXiv, journals, disclosure, authorship

### Takeaway
Every policy I read agrees on three points: an AI cannot be an author, the human authors carry full responsibility for every line, and AI use must be disclosed. For a newcomer the practical hurdle is arXiv: since December 2025 a first-time mathematics submitter needs a personal endorsement regardless of email address, and since May 2026 leaving unchecked LLM output in a paper risks a one-year ban.

### Cited Findings

arXiv
- 31 Jan 2023 policy: generative AI tools must not be listed as authors; significant use of such tools must be reported in the work; authors take full responsibility for all content however generated — [arXiv blog](https://blog.arxiv.org/2023/01/31/arxiv-announces-new-policy-on-chatgpt-and-similar-tools/); still the text on the moderation page, which also says submissions may be declined for lacking originality, novelty or significance — [arXiv moderation](https://info.arxiv.org/help/moderation/index.html)
- 31 Oct 2025: in the computer science category only, review articles and position papers must already be accepted at a peer-reviewed journal or conference; the reason given is LLM-driven volume of surveys that are little more than annotated bibliographies. Mathematics is not included, though other categories may follow — [arXiv blog](https://blog.arxiv.org/2025/10/31/attention-authors-updated-practice-for-review-articles-and-position-papers-in-arxiv-cs-category/)
- 10 Dec 2025: new submitters to any arXiv Math category are auto-endorsed only with both an institutional email and prior authorship of an accepted arXiv math paper; otherwise they need personal endorsement from an established arXiv author in the area, whatever their email. Stated aim: stemming low-quality, non-scientific submissions — [arXiv blog](https://blog.arxiv.org/2025/12/10/updated-endorsement-policy-for-arxiv-mathematics/); extended to all categories on 21 Jan 2026 — [arXiv blog](https://blog.arxiv.org/2026/01/21/attention-authors-updated-endorsement-policy/)
- Endorsement mechanics: at least one positive endorsement per endorsement domain; endorsers must have authored enough papers in the domain between three months and five years ago; endorsement is not peer review, but endorsers should know the author or have seen the paper and should not endorse people unfamiliar with the field's basics; do not mass-email potential endorsers; arXiv staff cannot endorse — [arXiv endorsement help](https://info.arxiv.org/help/endorsement.html)
- May 2026: incontrovertible evidence that authors did not check LLM output (hallucinated references, leftover model comments) brings a one-year ban, after which submissions must first be accepted by a reputable peer-reviewed venue; one strike, confirmed by section chairs, appealable; this is not a ban on LLM use — [TechCrunch, 16 May 2026](https://techcrunch.com/2026/05/16/research-repository-arxiv-will-ban-authors-for-a-year-if-they-let-ai-do-all-the-work)
- Full English version required from 11 Feb 2026 — [CASRAI summary](https://casrai.org/news/arxiv-2026-endorsement-english-ai-policy-changes)
- Background: Litt found six of eight arXiv papers mentioning the Hodge conjecture in one month of 2025 were LLM-generated nonsense with hallucinated references — [Litt, 17 July 2025](https://www.daniellitt.com/blog/2025/7/17/arxiv-in-trouble)

Journals and societies
- London Mathematical Society (policy updated October 2026): AI cannot be an author; every manuscript must contain a section headed AI Declaration stating all AI use, with tool name and model number, or stating none; substantial mathematical software is declared separately; authors must check accuracy and plagiarism and bear full responsibility; referees and editors may not upload manuscripts to AI tools — [LMS AI policy](https://www.lms.ac.uk/publications/policies/AI)
- AMS (publisher of Mathematics of Computation): has adopted COPE's February 2023 position that AI tools cannot be authors because they cannot take responsibility, declare conflicts or manage copyright (search summary; page returned 403) — [AMS, Use of Artificial Intelligence](https://ams.org/publications/journals/policies/UseofArtificialIntelligence)
- Elsevier (updated June 2026): no AI authors; a separate AI declaration statement placed just before the references, naming the tool and purpose; generating manuscript sections without genuine intellectual contribution is prohibited; authors must verify output, especially references — [Elsevier generative AI policy](https://www.elsevier.com/about/policies-and-standards/generative-ai-policies-for-journals)
- Cambridge University Press: AI use must be declared and explained; AI may not be listed as an author; authors are accountable for accuracy, integrity and originality including any AI use — [Cambridge authorship policy](https://www.cambridge.org/core/services/publishing-ethics/authorship-and-contributorship-journals)
- Taylor & Francis (publisher of Experimental Mathematics): AI cannot be an author; a specific AI usage statement must give the tool's full name and version, how and why it was used; text or code generation without rigorous revision is prohibited; reviewers may not use AI to write reports — [Taylor & Francis AI policy](https://taylorandfrancis.com/our-policies/ai-policy/)
- Springer Nature: human accountability cannot be transferred to AI systems; transparency about AI use is expected (general policy page only; detailed author guidance not retrieved) — [Springer Nature editorial policies](https://www.springernature.com/gp/policies/editorial-policies)
- AGMAI, "Responsible Release of AI-Generated Mathematics" (29 Sept 2026), addressed to labs: write traditional human-readable papers with precise statements; survey the literature and cite sources even for independently found ideas; deposit in citable repositories not controlled by a lab; formalize where possible and state formalization status; publish model name, prompts, summarized reasoning, time and compute; do not use results as marketing. Its background norm for individuals: authors should understand the argument, take full responsibility, post a preprint, submit for peer review and give talks — [AGMAI](https://agmai.org/general-sep29/)

How papers have actually acknowledged AI
- AI named in the title with a human sole author: Sothanaphan's write-up of Aristotle's Lean proof for #728, with the operator (Barreto) and both systems named in the abstract — [arXiv:2601.07421](https://arxiv.org/abs/2601.07421); Knuth's note names Claude in the title and narrates what the model did and what he proved himself — [Knuth](https://www-cs-faculty.stanford.edu/~knuth/papers/claude-cycles.pdf)
- Mixed human author lists that include the AI operators alongside professionals (the #1196 paper) — [Quanta](https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/)
- Corporate authorship with a separate human companion paper (OpenAI unit distance; Navier-Stokes) — [OpenAI](https://openai.com/index/model-disproves-discrete-geometry-conjecture/)
- A one-line disclosure of chatbot use for discussion and checking calculations (Tao's Jacobian post) — [Tao, 21 July 2026](https://terrytao.wordpress.com/2026/07/21/a-digestion-of-the-jacobian-conjecture-counterexample/)
- By August 2026 about one in seven new arXiv math submissions disclosed substantive AI use — [arXiv:2608.24961](https://arxiv.org/abs/2608.24961)

### Inferences
- Disclosure is now ordinary and does not by itself stigmatize a paper; concealment is the risk. A safe template is a dedicated declaration naming tool and version, what it did (idea, proof search, formalization, literature search, drafting), and what the human verified.
- For an unaffiliated author the endorsement step is the real gate. Endorsers are told not to vouch for work they have not seen from someone unfamiliar with the field, so a clean, short, checked manuscript and a relevant endorser matter more than the result's size.
- No arXiv rule forbids review or expository articles in mathematics, but the moderation page lets moderators decline work lacking original or substantive research, and the CS rule may spread.

### Gaps
- Could not read the AMS page or COPE statement directly; the AMS summary is from a search snippet.
- No journal-specific AI text was found for Experimental Mathematics or Mathematics of Computation beyond their publishers' policies.
- Springer Nature's detailed author rules (where to document use, copy-editing exemption) were not retrieved in current form.
- The primary arXiv text of the May 2026 ban policy was not found; details are from press reports of a section chair's posts.

## 6. Amateurs and non-academics who published mathematics with AI help (2024-2026)

### Takeaway
There are genuine, well-received cases, nearly all on Erdős problems, and all share a pattern: a public problem database, a professional or formal check, and a readable write-up. The same period produced false starts from the same people and a flood of unread AI papers that the community treats as a nuisance.

### Cited Findings
- Kevin Barreto (Cambridge undergraduate) and Liam Price (hobbyist who left college; says he cannot verify the solutions himself): their first claim, a GPT-5.2 proof of Erdős #333 posted 25 Dec 2025, was wrong as a novelty claim because Erdős had solved it in 1977; Barreto admitted the error and urged more literature searching. By 4 Jan 2026 they had #728 via GPT-5.2 Pro, checked with Aristotle in Lean. Price's method was to have a fresh chatbot instance check another's solution repeatedly; Barreto then recruited mathematicians to check. Their #1196 paper has Tao and Lichtman as co-authors — [Quanta](https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/)
- Reception of Barreto: New York Times and New Scientist coverage, job approaches from OpenAI, DeepMind and Harmonic; he himself says anyone interested could have done it — [Varsity](https://www.varsity.co.uk/science/31116)
- Nat Sothanaphan (software engineer) wrote up #728 for arXiv (math.NT), five versions in two weeks, verification by Lean — [arXiv:2601.07421](https://arxiv.org/abs/2601.07421); [Quanta](https://quantamagazine.org/why-the-legendary-erdos-problems-are-falling-to-ai-20260803)
- Neel Somani (software engineer, former quant) got a full solution from ChatGPT in about 15 minutes, checked it and formalized it with Aristotle — [TechCrunch](https://techcrunch.com/2026/01/14/ai-models-are-starting-to-crack-high-level-math-problems/)
- Wouter van Doorn (customer-service worker with an unfinished master's): solved #1102 without AI, accepted by Tao on the forum; later says much of the credit for his recent papers belongs to AI while he simplifies and generalizes the model's ideas into more readable proofs — [Quanta](https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/)
- Filip Stappers posed Knuth's problem to Claude Opus 4.6 and coached it; Knuth credited him and the model by name, wrote the proof, and a Lean formalization followed — [Knuth](https://www-cs-faculty.stanford.edu/~knuth/papers/claude-cycles.pdf)
- Bloom says most early new AI results came from hobbyists and undergraduates with public models, not corporate labs, and also that long AI papers nobody has read are now a huge challenge — [Quanta](https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/)
- Negative examples: LLM-generated Hodge conjecture papers on arXiv — [Litt](https://www.daniellitt.com/blog/2025/7/17/arxiv-in-trouble); the Collatz "disproof" that passed Lean through a kernel bug — [GIGAZINE](https://gigazine.net/gsc_news/en/20260803-collatz-lean-kernel-bug/)

### Inferences
- What was received well: modest, precisely stated, catalogued problems; open acknowledgment of the AI; fast correction when prior literature surfaced; Lean proof or a professional's sign-off; a human-digested write-up.
- What was received badly: grand claims on famous conjectures, length, self-checking by the same model, missing literature review.
- I found no case of an amateur's AI-assisted result on a famous conjecture being accepted.

### Gaps
- I found no documented case of an amateur AI-assisted paper passing peer review at a named journal; the cases above are arXiv preprints, forum-accepted solutions and database entries. Journal acceptance may exist but was not located.
- No amateur example specifically about π or prime-counting was found.

## 7. The role of formal verification (Lean)

### Takeaway
A Lean proof checked the right way is now the strongest credential an AI-assisted result can carry and is what moved the GRH claim from ignorable to serious within a day. It certifies that a formal statement follows from the axioms; it does not certify that the statement is the theorem you meant, that an accompanying PDF is correct, or that anyone understands the proof.

### Cited Findings
- Buzzard's four checks for AI-generated Lean: (1) read the headline statement and confirm it matches the informal theorem; (2) build the whole repository, in a sandbox, since Lean code can run arbitrary commands; (3) run `lake comparator` to confirm the theorem in a trusted file is identical to the one proved and that only standard axioms are used; (4) run comparator in paranoid mode to check with several independent kernels — [Xena project, 12 Nov 2026](https://xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/)
- Ways it goes wrong, from the same post: a two-line Fermat statement that compiles but is false because Lean's naturals include 0; statements resting on tens of thousands of lines of unvetted definitions; Lean files that prove only a corollary of the paper's headline result — [Xena project, 12 Nov 2026](https://xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/)
- Kernel bugs are real: the July 2026 Collatz episode passed both Lean and an independent checker; the fix shipped within hours and further kernel implementation errors were then found and fixed — [GIGAZINE](https://gigazine.net/gsc_news/en/20260803-collatz-lean-kernel-bug/)
- Formal and informal versions can diverge: the critique of OpenAI's Navier-Stokes release argues its Lean code does not correspond to its written proof — [arXiv:2610.08144](https://arxiv.org/abs/2610.08144)
- For the GRH archive the community applied exactly this protocol: Mathlib's own statement, many independent builds, two comparison tools, multiple kernels including ones with formal soundness proofs — [Lean community blog](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)
- Vacuous correctness: DeepMind notes some technically valid AI solutions were mathematically empty because the problem statement was misread (search summary) — [arXiv:2601.22401](https://arxiv.org/abs/2601.22401)
- Formalization tools reachable by outsiders: Harmonic's Aristotle was used by Barreto and Somani to formalize chatbot proofs — [TechCrunch](https://techcrunch.com/2026/01/14/ai-models-are-starting-to-crack-high-level-math-problems/)
- Only six of the 19 strictest-class AI solutions on the Erdős wiki were Lean-formalized; the rest rest on human checking — [AI contributions wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)
- AGMAI asks that released AI proofs be formalized where possible and that formalization status be stated clearly otherwise — [AGMAI](https://agmai.org/general-sep29/)

### Inferences
- For an amateur, a Lean proof whose final statement uses only Mathlib definitions and passes comparator answers the first question any expert will ask (is it even correct) without needing anyone's time, and it is the documented route by which outsiders' results were accepted in 2026.
- It does not replace a short human-readable proof, a literature search, and a plain disclosure; the community's complaint about the GRH release is precisely that it is Lean only.

### Gaps
- No source quantifies how often journals now request or weigh a formal proof.
- Long-run reliability of comparator-style checks against adversarial AI-written code is asserted by Buzzard and the Lean community but has little track record.

## Search log

Web searches run (21 executed; a 22nd was refused because the session-wide search budget was exhausted):

1. Levent Alpoge Riemann Hypothesis proof Claude
2. Alpöge Anthropic Riemann Hypothesis announcement six weeks
3. AI proof Riemann Hypothesis 2026 mathematicians verification
4. Erdős problems AI solved GPT-5 literature search dispute
5. Alpöge Riemann Hypothesis Lean proof Tao Buzzard reaction
6. Claude Jacobian conjecture July 2026
7. OpenAI Navier-Stokes Buckmaster Alpöge dispute September 2026
8. Terence Tao blog Riemann hypothesis Lean proof Alpöge November 2026
9. 25 Fields Medalists declaration AI proofs September 2026
10. OpenAI 722 papers October 6 2026 mathematics results
11. arXiv policy AI-generated papers review articles endorsement 2026
12. arXiv one-year ban LLM-generated hallucinated references code of conduct authors responsible
13. AlphaEvolve Tao "mathematical exploration and discovery at scale" kissing number results
14. Erdős problems AI contributions wiki autonomous solutions count 2026
15. amateur mathematician AI proof Erdős problem Lean Aristotle
16. Epoch AI FrontierMath 2026 results tier 4 open problems
17. journal policy AI authorship disclosure mathematics AMS Springer Elsevier Cambridge
18. Ramanujan Machine AI discovered formulas pi 2025 2026 conservative matrix field
19. AI claimed proof Collatz conjecture OR Goldbach OR "twin prime" 2026 status
20. OpenAI Navier-Stokes proof verification status Tao Lean October 2026
21. Kevin Buzzard Daniel Litt Timothy Gowers AI mathematics capability limits 2026
22. (not performed, budget exhausted) Tao "digestion of the Jacobian conjecture counterexample" — the post was instead reached through Tao's July 2026 blog archive.

Total: 21 searches executed, 1 refused. In addition about 80 pages were fetched directly (primary pages on alpo.ge, math.mit.edu, leanprover-community.github.io, terrytao.wordpress.com, xenaproject.wordpress.com, gowers.wordpress.com, daniellitt.com, arxiv.org, blog.arxiv.org, info.arxiv.org, openai.com, anthropic.com, deepmind.google, epoch.ai, mathandai.org, agmai.org, publisher policy pages, Quanta, Scientific American, Science News and others). Pages that refused or failed: nature.com (login redirect), science.org (403), npr.org (timeout), ams.org (403), publicationethics.org (403), erdosproblems.com (403), acadmathsci.org.uk (403), nacionale.com (403), livescience.com (body truncated), one epoch.ai problem URL (404).
