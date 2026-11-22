# AI and mathematics landscape, September to November 2026

Compiled 22 November 2026. Web research only. 28 of 28 WebSearch calls used.

Labels: [READ] = I opened the page (via WebFetch, which returns a model-written digest of the page, not raw text) and the fact was in that digest. [SNIPPET] = seen only in search-result text. Dates are given for every news item; where a date is only inferred, it says so. Quotes are kept under 15 words.

Important caution about this whole map: several of the biggest stories (the Riemann hypothesis claim of 20 November, the OpenAI bulk release, the Axiom formalizations) were less than three weeks old at the time of writing, and verification and expert judgment were still moving. Anything below could change within days.

---

## Summary (10 lines)

1. The landscape changed scale in autumn 2026. The news is no longer "AI helps with a lemma" but lab-scale claims: Anthropic's Lean formalization of Fermat's Last Theorem (4 Sep), OpenAI's bulk release of 722 manuscripts (6 Oct), Axiom's formalization of the classification of finite simple groups (27 Oct), and Anthropic researcher Alpöge's claimed Lean proof of the Riemann hypothesis (20 Nov). [READ]
2. Lean verification is now the currency of credibility. The Lean and Mathlib communities issued a joint statement on 21 Nov certifying the Riemann hypothesis statement and proof, using the comparator tool and independent checkers. [READ]
3. There is also a strong backlash: 25 Fields medalists' declaration (11-17 Sep, 7,400+ endorsements), an Association for Human Mathematics boycott call (7 Oct), complaints that the OpenAI papers are unreadable, and three withdrawn papers. [READ via Quanta digests]
4. The standard objections are: Lean checks the formal statement, not that it says what was meant (misformalization); no human understands the output; unreadable bulk papers; credit and priority disputes; selection bias and obscurity of "solved" problems; literature rediscovery. [READ]
5. Unreleased lab models drive most headline results. Hobbyists did contribute (Erdos #1196, April 2026; a 3D tile claim, Sept 2026; a 3-page Landau-Siegel proof, Nov 2026), but the amateur angle is now familiar rather than novel. [READ]
6. Our work (BBP-type formulas, optimality and classification theorems, log 23 result conditional on Baker) is small, human-scale, machine-checked and explicit about its hypothesis. That is the kind of thing the community says it wants, but it competes for attention with claims of enormously larger scale.
7. arXiv is hard for outsiders now: for any math category, a first-time submitter needs an institutional email plus a prior accepted arXiv math paper for automatic endorsement, otherwise a personal endorsement from an established author. Since 1 Oct 2026 there is also a limit of 2 submissions per month. [READ]
8. Journal of Integer Sequences states the words of the paper must be the author's own and any AI role must be fully described, or the paper may be rejected. [READ] Other journals' pages were mostly not retrievable.
9. Lean venues: Reservoir indexes automatically if the repo is public on GitHub, has a lake-manifest.json, an OSI-approved license, and at least 2 stars. [READ] Mathlib bans LLM-written Zulip and GitHub comments. [READ]
10. Nothing I found confirms any YouTube channel's coverage numbers; YouTube pages could not be read. I could confirm one Wes Roth video (about 22 minutes, early October, date inferred) via a transcript site.

---

## Timeline September to November 2026

Status column: Verified = Lean-checked and/or independently confirmed per the source; Pending = still under review; Disputed = significant expert objection.

| Date (2026) | Event | By whom | Formal check | Reaction / status | Source tag |
|---|---|---|---|---|---|
| 28 Aug (background) | Claude-generated proof that theta(p_c)=0 in dimensions 3 to 10 posted to GitHub with no formal announcement | Anthropic (Justin Leder named by Quanta) | Lean | Experts: clever, not much new; Kozma withholding judgment until a readable version exists (Quanta, 1 Oct) | [READ] Quanta digest |
| 1 Sep | FrontierMath Erdos benchmark announced: 68 significant open Erdos problems chosen by Thomas Bloom, Lean statements, comparator checking | Epoch AI (Adamczewski, Burnham) | Lean (50 statements from Formal Conjectures, 18 AI-formalized) | GPT-6 Astra solved 2 of 68 on the benchmark run; others 0%. Authors say they are not Lean experts and wanted review | [READ] epoch.ai |
| 4 Sep | First complete computer-checked Fermat's Last Theorem in Lean, written by Claude agents in 11 days, about 13 million lines | Anthropic (Tianyi Peng, Columbia group) | Lean kernel, standard axioms, comparator | Buzzard: adds nothing mathematically, but shows formalization could become fast; code cannot enter Mathlib. A Trail of Bits post (9 Sep) showed a separate Lean checker-bug exploit that "proved" FLT via native code, a trust-boundary warning | [READ] anthropic.com, TNW (6 Sep), Trail of Bits |
| Sept (various) | Several Epoch-reported results with GPT-6 Astra: Kothe conjecture disproof, Dittert conjecture proof, N-conjecture n=4 counterexample, others | Epoch AI with Adamczewski and others | Mostly Lean; one "?" and one "independent review pending" | Listed in Wikipedia table; I did not open the individual papers | [READ] Wikipedia list only |
| 8-10 Sep | OpenAI says internal agents found a Navier-Stokes singularity; Alpoge (Anthropic) claims complex structure on S^6 (open since 1947) | OpenAI; Alpoge | S^6: Lean version of statement by Boris Alexeev (OpenAI) | Abouzaid: poorly written, will take a while to check; Engel: early signs true. Navier-Stokes controversial, priority disputed (Buckmaster) | [READ] Quanta digests; Datacamp |
| 11-17 Sep | Declaration by 25 Fields medalists criticizing AI companies treating problems as benchmarks; 7,400+ endorsed within days | Fields medalists | n/a | Tao quoted by Quanta: situation has "deteriorated markedly" | [READ] Quanta digest |
| 16-23 Sep | 3D aperiodic monotile "Chair44" claimed with GPT-6 Astra by Ioannis Tsiokos, a software developer | Individual outsider | Partial | Goodman-Strauss condensed the 61-page paper to 8 pages and affirmed it; said original and its formalization were not readable enough to check | [READ] Quanta digest (two columns agree) |
| 23 Sep | arXiv receives multiyear philanthropic commitments, becomes independent nonprofit | arXiv | n/a | Context only | [READ] arXiv blog list |
| 29 Sep | Advisory Group on Mathematics and AI issues recommendations | Advisory group | n/a | Calls the release process "the beginning, not the completion" | [READ] Datacamp (secondary) |
| 1 Oct | arXiv rate limit: 2 submissions per calendar month, max 3 active | arXiv | n/a | Described as a stopgap; AI use allowed if disclosed | [READ] arXiv blog |
| 1 Oct | OpenAI releases claimed proof that Landau-Siegel zeros do not exist | OpenAI | not stated | Granville: emotional; simpler proofs followed, including a 3-page one by Kevin Barreto (Quanta 5 Nov) | [READ] Quanta digests |
| 5 Oct | Subquadratic 3SUM and subcubic all-pairs shortest path preprint, discovery and Lean formalization credited to an Anthropic internal model | Alman and Vassilevska Williams (humans) with Anthropic | Lean | Example of human authors, AI credited | [READ] Wikipedia list |
| 6 Oct | OpenAI posts 722 manuscripts (372 or 377 result "families", counts vary by source) on GitHub from an unreleased model; about 42% with Lean | OpenAI | About 42% | Three algebraic geometry papers withdrawn over a sign error; Commelin: some formalizations may prove weaker statements; Dafermos: some papers too vague; AHM boycott call (7 Oct); Moshkovitz: unreadable | [READ] Quanta digests, Datacamp, Wikipedia |
| 6-19 Oct | Quasi-Riemann hypothesis (zeros in strip 1/12 to 11/12 in version 2, 49 pages) from the OpenAI release | OpenAI | Version 1 Lean-verified; version 2 not yet | Lichtman: most significant AI-for-math achievement so far. Radziwill, others: poorly written. Sarnak: will not call it a theorem until humans check details | [READ] Quanta 19 Oct |
| 8 Oct | DeepMind AlphaProof Nexus paper reported in Science: 9 of 353 open Erdos problems | Google DeepMind | Lean; experts reviewed | Science page paywalled; I could not read it | [SNIPPET] |
| 9 Oct | Tao blog post on what mathematicians should know about Lean reliability and AI | Terence Tao | n/a | See "Claims that failed" for content | [READ] |
| 13 Nov | MathHelm forum announced for discussing AI-generated papers (guest post on Tao's blog by its committee) | Committee | n/a | Principle: mathematicians have no obligation to check AI papers | [READ] |
| 22 Oct | Caltech "Mathathon" refocused to new proofs of old results after criticism | Caltech | n/a | Tao involved in the new format | [READ] Quanta digest |
| 26-27 Oct | OpenAI: proof of local smoothing conjecture in all dimensions, disproof of Exponential Time Hypothesis, QFT result; Anthropic released its own ETH version hours later | OpenAI, Anthropic | Lean-verified per Lean FRO timeline (not independently confirmed by me) | Williams (MIT): still checking; QFT manuscript held back for physicists | [READ] Al Jazeera, Quanta, Lean FRO |
| 27 Oct | Axiom announces Lean formalization of the classification of finite simple groups (about 43 million lines, 24 days) | Axiom Math | Lean; independent rebuild not described as done at announcement | Roney-Dougal impressed, but worries few people can extract understanding. Formalization reportedly found errors in the human proof | [READ] IEEE Spectrum (18 Nov); [SNIPPET] unite.ai |
| 5-11 Nov | Quanta: Anthropic says FLT formalization now takes 30 hours; Helfgott ternary Goldbach formally verified (10 Nov); Axiom also reports Stacks Project, Weil conjectures, cluster algebras | Anthropic, Axiom | Lean | Epoch/Glazer 292-billion-variable polynomial announcement "drew controversy"; I could not confirm details | [READ] Quanta digest |
| 6 Nov | Paper "When Proofs Are Abundant, What Is a Paper For?" (arXiv 2611.12943) | Charles-Albert Lehalle | n/a | Argues correctness is no longer the scarce thing; shared understanding is | [READ] arXiv abstract |
| 20 Nov | Alpoge posts a 4-page paper and about 17 million lines of Lean claiming the Riemann hypothesis (Lean verifies the generalized version) with Claude; Tao reports on same day | Levent Alpoge (Anthropic mathematician) | Lean; comparator check | Nuccio: gorgeous. Radziwill: Lean-only proof short-circuits understanding. Tao: digestion will take time, discussion on Lean Zulip. Anthropic had not officially announced (per Quanta 20 Nov) | [READ] Quanta, Tao blog |
| 21 Nov | Lean and Mathlib communities, with Lean FRO and Mathlib Initiative, publish a joint statement certifying statement and proof | Lean community | Dozens of independent compiles; comparator; con-leche; third-party checkers | They add they look forward to humans explaining the ideas | [READ] Lean community blog |

Items I looked for and could not confirm in September to November 2026:
- A Harmonic (Aristotle) or Math Inc (Gauss) announcement dated September to November 2026: none found. [SNIPPET: search returned nothing newer than early 2026 for Harmonic; sources conflict on Gauss dates.] Aristotle does appear as a helper on the Lean Eval page and in June coverage of Erdos #728. [READ]
- New Erdos problem tracking: the community wiki of AI contributions says it is no longer updated, with latest data as of 30 June 2026. [READ] Thomas Bloom announced in early October a restructuring of erdosproblems.com away from "scoreboard" treatment (Quanta, 9 Oct digest). [READ] The erdosproblems.com site itself returned 403, so I could not read it.
- Kevin Buzzard's Xena blog: not read. His comments on FLT come via The Next Web (6 Sep). [READ]
- The Lean AI formalization leaderboard (lean-lang.org/eval) exists; the Lean FRO timeline says it launched in June 2026. [READ] The page content loaded dynamically ("Loading leaderboard data"), so I could not read current rankings. A search snippet claimed Axiom Prover at the top with 207 solved, but different snapshots disagree. [SNIPPET]
- Annals-related formalization challenge: not found.
- Older context (before September, labelled as older): Anthropic's zeta-zero result of 10 Aug (proportion of zeros on the critical line raised from 41.6% to 67.2%; not a Riemann proof; Lean formalization; Conrey and Goldston looked at it) [READ]; OpenAI unit-distance counterexample claim (20 May) [READ via Quanta 3 Aug]; Erdos #1196 solved by amateur Liam Price with GPT-5.4 Pro, mid-April 2026 [READ SciAm 24 Apr].

---

## Claims that failed and why

All items carry their date. "Failed" here includes retracted, found trivial, found to be literature, or still unverified despite headline claims.

1. **Erdos #333 "autonomous solution" (Christmas 2025, older).** Already in a 1977 Erdos paper; the poster retracted. Lesson: a "new" result can be a literature rediscovery. [READ via Quanta 3 Aug 2026]
2. **Erdos "solutions" that were literature identifications or obscurity effects (DeepMind Aletheia paper, January 2026, older).** The authors themselves say open status of resolved problems may reflect obscurity rather than difficulty. [SNIPPET]
3. **Community wiki caveats (as of 30 June 2026).** Eleven disclaimers, including: not a benchmark; selection bias; problems sometimes misstated; many problems lack a thorough literature check; a solution is not automatically a publishable paper. [READ]
4. **OpenAI bulk release (6 Oct).** Three papers withdrawn within days over a sign error; some Lean statements possibly weaker than the claimed result; some papers too vague to check; only about 42% with Lean; prompts and full reasoning not released (summaries for 10 results only). [READ Quanta digest 9 Oct, Datacamp, Wikipedia]
5. **Credit and priority disputes.** Buckmaster alleged unpublished work influenced the OpenAI Navier-Stokes effort; OpenAI denied. Unresolved. [READ Datacamp] (Buckmaster later co-authored with Alpoge, per Tao 20 Nov [READ].)
6. **Navier-Stokes Millennium claim (8 Sept, OpenAI).** Wikipedia's table says it had not been verified by the wider community. [READ]
7. **Axiom CFSG (27 Oct).** Founding claims rest on company materials; one outside expert quoted; no independent audit described at the time of the IEEE piece. [READ]
8. **Alpoge Riemann (20 Nov).** Verified at the Lean level by the Lean community, but experts note the informal writeup contains what Radziwill called nonsensical statements, and a 250,000-page informal output was not released. A rival 940-page human GRH claim by Masullo is unverified and his earlier attempt did not hold up. [READ Quanta 20 Nov]
9. **Tao's Lean reliability post (9 Oct).** Kernel soundness bugs were found in summer 2026 by security researchers using AI, including one that produced a bogus disproof of Collatz; all fixed. Mitigations: independent kernels, verified kernels (Con-Leche), audit of statements and axioms using comparator. [READ]
10. **Trail of Bits (9 Sep).** A mismatch between the logical and native-compiled definition of a string-slice function let a "proof" of FLT pass; relies on `native_decide`, which adds the compiler to the trusted base. Not a kernel bug. [READ]
11. **Alleged non-peer-reviewed secondary claims.** A site (tech-insider.org) catalogued criticisms but marks most as second-hand; treat as weak evidence. [READ]
12. **Unreliable aggregator claims I saw in search snippets** (for example a "Wang's Conjecture cracked overnight" headline) were not checked; treat as unverified. [SNIPPET]

### Standard objections, and how this work can pre-empt them

| Objection | Source | Pre-emption for this work |
|---|---|---|
| Lean checks the formal statement, not that it says what you mean | Tao 9 Oct; Quanta 9 Oct [READ] | Put the headline theorems in a single short file with Mathlib-only imports, plain-language comments, and a statement a human can audit in minutes. Run the comparator tool against that file. List axioms used (`#print axioms`). |
| Hidden axioms, `sorry`, `native_decide`, custom tactics | Tao 9 Oct; Trail of Bits [READ] | State clearly that none are used (if true). Show the Baker hypothesis as an explicit hypothesis, not an axiom. |
| "AI said so" | de Moura slides snippet; Riehl thread [READ Zulip archive, Nov 2025, older] | Say what a human did and understands. Name the human who can answer questions. |
| Unreadable, bulk, unexplained | Quanta 9 Oct, Calegari, Dafermos [READ] | Short paper, one clear main theorem, informal proof sketch that matches the Lean structure. |
| Obscure problem, easy because ignored | Erdos wiki disclaimers [READ] | Cite the BBP literature (Bailey, Borwein, Plouffe, and later work) precisely; say what is new relative to it. |
| Rediscovery of existing literature | #333 case [READ] | Do a literature check and show it. Ask a specialist to check novelty before public claims. |
| Conditional on a deep theorem | (inferred) | Say "conditional on Baker's theorem" in the title or first line of the abstract; note that Baker's theorem itself is classical and published, which is not like an unproven conjecture. |
| Claims of priority or hype | OpenAI disputes [READ] | Do not use the word "solved"; use "classification" and "optimality" language. |

---

## Who covers this

I could not read any YouTube channel page (the fetches returned only the footer), so I cannot give subscriber counts. I also could not find any YouTube video about the Anthropic FLT result through search. Everything here is what I could actually read.

| Outlet | Type | What it covered Sept to Nov 2026 | Angle | Audience size | Source tag |
|---|---|---|---|---|---|
| Quanta Magazine, "Transformation" column | Weekly news column / newsletter | Dated items from 23 Aug to 20 Nov: S^6, percolation, Fields medalists' declaration, Chair44, OpenAI release, quasi-Riemann (19 Oct feature), elliptic curve ranks, Alpoge RH | Skeptical-but-serious; names verification status for each claim | not stated | [READ] |
| Terence Tao, "What's new" blog | Mathematician's blog | 9 Oct Lean reliability; 13 Nov MathHelm; 6 Nov link roundup; 20 Nov Euler/Navier-Stokes/GRH; guest posts by Buckmaster, Calegari, AHM statement | Insider hub; this is where the community discusses AI claims | not stated | [READ] |
| Lean community blog | Community blog | 21 Nov joint statement certifying the RH Lean proof (the only post in Sept to Nov on the page) | Official certification of Lean proofs | not stated | [READ] |
| Wes Roth (YouTube) | AI-focused video channel | About 22-minute video on the OpenAI 722 papers; date inferred as early October ("six days into the month") | Hype-leaning "model broke math" framing; notes the Fields medalist letter | not found | [READ] via sozai.app transcript |
| Unnamed channel, video "OpenAI Dropped 722 Math Papers Overnight. Mathematicians Lost It." (video id Pp1siLlt-dI) | YouTube | Listed claims such as pi irrationality exponent exactly 2 and plane chromatic number; treats papers as first drafts | Cautious about Lean not confirming intent | channel and date not stated by the summary site | [READ] via youtubesummary.com |
| Axios | News | 8 Sep "AI is changing math"; 8 Oct "OpenAI's math breakthrough points beyond math" | Business/AI-industry angle | not stated | [SNIPPET] (page returned 403 when opened) |
| Al Jazeera | News | 27 Oct OpenAI announcement | Wire-style | not stated | [READ] |
| The Next Web, SiliconANGLE, Decrypt, TechRadar | Tech press | FLT formalization (4 to 6 Sep) | Quoted Buzzard; scale of 13 million lines | not stated | [READ] TNW; [SNIPPET] others |
| IEEE Spectrum | Magazine | 18 Nov on Axiom CFSG and Stacks | Quotes Roney-Dougal | not stated | [READ] |
| Hacker News (via zeli.app summary) | Forum | 12 Oct discussion of Nisheeth Vishnoi essay on the OpenAI release | Extraction and verification capacity | 35 comments on that thread | [READ] |
| Julia Discourse "Mathpocalypse" | Forum | OpenAI release reaction | Mixed; readers call the release unreadable | not stated | [SNIPPET] |
| Peter Woit's blog | Blog | AI-written physics papers and disclosure | Skeptic | not stated | [SNIPPET] |
| Dwarkesh Podcast | Podcast | Tao interview, 20 Mar 2026 (older; outside the three-month window) | Long-form with Tao | not stated | [SNIPPET] |
| Numberphile, 3Blue1Brown, Two Minute Papers, AI Explained, Matt Parker | YouTube | Could not read any channel page or find any dated video on these topics in the window | n/a | not found | not confirmed |

Reading across: the outlets that take small independent verified results seriously are the mathematician-run ones (Tao's blog, Lean Zulip, Lean community blog), not the commentary channels, which cover lab announcements.

---

## Case studies of announcements

### 1. Anthropic: Fermat's Last Theorem in Lean (4 Sep 2026) [READ]
- Order: lab blog post (research page) plus public GitHub repository (anthropics/fermats-last-theorem) and a walkthrough on 4 Sep; independent compile and review by Kevin Buzzard, who blogged within days; tech press 4-6 Sep; Columbia group blog post 9 Sep; Trail of Bits critique 9 Sep. An arXiv paper by the Prove2Me platform group is cited.
- Who vouched: Buzzard (compiled it himself, asked an agent to flag non-definition, non-proof lines, ran comparator) and Lean's kernel check with the three standard axioms.
- What the post pre-empted: said it formalizes an existing proof, not new mathematics; admitted the proof is far longer than needed; said failed early attempts contributed about 7% of non-boilerplate lines; used comparator to tie the statement to Mathlib's.
- Outcome: widely covered; not mergeable into Mathlib.
- Links: https://www.anthropic.com/news/formalizing-fermats-last-theorem ; https://thenextweb.com/news/anthropic-claude-fermat-last-theorem-lean-buzzard ; https://blog.trailofbits.com/2026/09/09/a-proof-of-fermats-last-theorem-that-fits-the-margin/

### 2. Erdos #1196: amateur plus public models, with experts (April to May 2026; older, outside window but the template for an outsider) [READ + SNIPPET]
- Order: the solver, Liam Price (23, no advanced training), posted the model output on erdosproblems.com in mid-April 2026; collaborator Kevin Barreto recognized its significance and contacted experts; Tao and Lichtman reviewed it and shortened the proof; formalization with Math Inc's software [SNIPPET]; a 35-page arXiv preprint on 1 May with eight authors including Tao and Lichtman [SNIPPET]; Scientific American coverage 24 Apr [READ].
- Who vouched: Tao and Lichtman, and Lean verification [SNIPPET].
- Key lesson: the outsiders did not publish alone; they brought named experts in early and let the experts co-author.
- Links: https://scientificamerican.com/article/amateur-armed-with-chatgpt-vibe-maths-a-60-year-old-problem ; https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/

### 3. Alpoge: Riemann hypothesis in Lean (20-21 Nov 2026) [READ]
- Order: short 4-page paper plus Lean library released by Alpoge on 20 Nov; Lean Zulip thread (Tao directs readers there); independent compiles by Sutherland and DeDeo; Tao blog post on 20 Nov; Quanta column 20 Nov; Lean and Mathlib communities' joint certification on the Lean community blog 21 Nov.
- Who vouched: the Lean community, not Anthropic (Quanta says there was no official Anthropic announcement as of 20 Nov).
- What made certification possible: a small, auditable statement file importing only Mathlib; comparator and con-leche cross-checks; checking an inert export so malicious code in the sources could not matter.
- Links: https://leanprover-community.github.io/blog/ (post "riemann-hypothesis", 2026-11-21); https://terrytao.wordpress.com/2026/11/20/unforced-euler-singularity-unforced-navier-stokes-singularity-and-the-generalized-riemann-hypothesis/ ; https://www.quantamagazine.org/update/169054/

### 4. Counter-example: OpenAI bulk release (6 Oct 2026) [READ]
- Order: 722 manuscripts to GitHub on 6 Oct; press the same day; Tao-blog guest posts (AHM 7 Oct, Buckmaster 21 Oct, Calegari 1 Nov); withdrawals by 9 Oct; Lean community debate on whether Lean statements matched.
- Outcome: the scale triggered a boycott call and a forum (MathHelm) designed to handle AI papers. A cautionary example of what not to do: no human-readable narrative, no prior contact with the experts in each field.
- Link: https://www.datacamp.com/blog/openai-math-breakthroughs-what-the-latest-results-mean ; https://www.quantamagazine.org/update/168181/

### Also useful
- Anthropic zeta-zero result, 10 Aug (older): paper PDFs, informal note, transcripts, Lean repository (anthropics/zeta-23-lean), two named internal mathematicians plus two outside experts. No arXiv submission mentioned. [READ] https://www.anthropic.com/research/riemann-zeta
- Alman and Vassilevska Williams, 5 Oct: preprint by two named human authors, Anthropic model credited for discovery and Lean formalization. [READ via Wikipedia list]

---

## Practicalities

### arXiv [READ unless stated]

- **Endorsement, any math category (including math.NT and math.HO).** Policy effective 10 Dec 2025: automatic endorsement needs both an institutional email address and prior authorship of an accepted arXiv Mathematics paper; otherwise you need a personal endorsement from an established arXiv author in the same area. arXiv staff cannot provide endorsements. Authors already endorsed keep status. https://blog.arxiv.org/arxiv/2025/12/10/updated-endorsement-policy-for-arxiv-mathematics
- **All sections from 21 Jan 2026.** An institutional email alone is no longer enough; the two paths are (1) institutional email plus a prior accepted paper in the same endorsement domain, or (2) personal endorsement. arXiv gave a "flood of low-quality submissions" as the reason. https://blog.arxiv.org/2026/01/21/attention-authors-updated-endorsement-policy/ (and the page https://info.arxiv.org/help/endorsement.html)
- **cs.LO.** The cs endorsement page I opened gave no category-specific rule. By the 21 Jan policy, the same two paths apply; I did not find cs.LO named anywhere. [not confirmed for cs.LO specifically]
- **math.HO.** Falls under the math rule above; I did not find any separate rule.
- **Rate limit (1 Oct 2026).** Two submissions per calendar month, no more than three active at once; rejected submissions count. Described as a stopgap while arXiv decides best practice for AI use. https://blog.arxiv.org/2026/10/01/updated-rate-limit-policy/
- **AI use policy.** Signing as author means taking full responsibility for the contents however they were produced; significant use of text-to-text generative AI should be reported; AI tools cannot be listed as authors; papers can be declined for lack of originality, plagiarism or misrepresentation. https://info.arxiv.org/help/moderation/index.html
- **One-year ban (reported 16 May 2026).** TechCrunch reports arXiv will impose a one-year ban for incontrovertible evidence that authors did not check LLM output (hallucinated references, leftover chatbot text); afterwards, submissions need prior acceptance at a reputable peer-reviewed venue. Announced by the cs section chair; moderators and section chairs confirm; appeal is possible. LLM use itself is not banned. https://techcrunch.com/2026/05/16/research-repository-arxiv-will-ban-authors-for-a-year-if-they-let-ai-do-all-the-work (a secondary report; I did not find the arXiv primary text)
- **Review and position papers in cs (31 Oct 2025, older).** These must already be accepted by a journal or conference with peer review and DOI before submission; this is not a formal policy change but a moderation practice. It affects position-style writing in cs, not original research. https://blog.arxiv.org/2025/10/31/attention-authors-updated-practice-for-review-articles-and-position-papers-in-arxiv-cs-category/

Practical implication: without an institutional email and a prior accepted math paper, the realistic route is a personal endorsement. One route I did not find documented in any source I read: asking the Lean community people who have already engaged with the work. I would not rely on it.

### Journals

| Journal / venue | What I could read | Policy on AI | Policy on formal proofs | Tag |
|---|---|---|---|---|
| Journal of Integer Sequences | Author guidelines | Authors must not use an LLM to write the English text of the paper; undisclosed AI use is grounds for rejection unless the role is explicitly and fully described; an LLM may suggest proof techniques or proofs only if the paper credits it and authors check every detail; the journal may screen submissions with AI detectors. Papers must be LaTeX, must focus on integer sequences and cite OEIS A-numbers; brute-force extension of terms is not accepted; preprints are allowed | Lean or Coq not mentioned | [READ] https://cs.uwaterloo.ca/journals/JIS/ |
| Taylor and Francis (publisher of Experimental Mathematics, American Mathematical Monthly) | Publisher authorship policy | AI cannot be an author; use of generative AI must be declared with tool name and version, how and why used; content generation goes in the Acknowledgments; the page does not name the two journals, so journal-specific rules may exist | n/a | [READ] https://authorservices.taylorandfrancis.com/editorial-policies/defining-authorship-research-paper/ |
| Springer Nature (publisher of Journal of Automated Reasoning) | Policy page redirected to a login; read only through search-result text | LLMs do not meet authorship criteria; LLM use should be documented in the Methods section (or a suitable alternative part); AI-assisted copy editing need not be declared | n/a | [SNIPPET] |
| AMS (publisher of Mathematics of Computation) | Page returned 403; search text only | Authors must state which AI tool was used and how; authors fully responsible | n/a | [SNIPPET] |
| London Mathematical Society (for comparison) | Policy page | Mandatory "AI Declaration" section for every manuscript, naming tools and model numbers and the extent of contribution; use covers idea generation, calculation, constructing or verifying proofs; substantial other software must be declared under a separate heading; AI cannot be an author | not addressed | [READ] https://www.lms.ac.uk/publications/policies/AI |
| Elsevier (for comparison) | Policy page | Declaration statement before references; names tool, purpose, author oversight; AI used in the research process (data analysis, code) goes in the Methods, not the declaration; basic grammar tools exempt | n/a | [READ] |
| Annals of Formalized Mathematics | Journal home page | Not addressed on the page | Diamond open access overlay journal, founded 2024; papers aimed at mathematicians, centered on the mathematics; must be accompanied by a code artifact; new proofs not required | [READ] https://afm.episciences.org/ |
| CPP 2027 (conference) | Call for papers | Follows the ACM AI policy: AI tools allowed if no plagiarism or falsification, the work reflects the authors' own intellectual contribution, authors take responsibility; may be desk-rejected otherwise | Supplementary material (proof scripts) strongly encouraged but not required. Paper deadline was 10 Sep 2026, notifications 10 Nov, so the 2027 round is closed | [READ] https://popl27.sigplan.org/home/CPP-2027 |
| Integers (De Gruyter), Mathematics of Computation instructions, American Mathematical Monthly instructions, Experimental Mathematics instructions, ITP | Not retrievable (403, 405, or not found) | not confirmed | not confirmed | not confirmed |

Note on JIS: the guidelines ask that a paper on formulas for integer sequences cite OEIS A-numbers; BBP-type formulas for logarithms are not obviously "integer sequence" topics, so fit with the journal's scope should be checked before submission (my inference).

### Where Lean results are announced and published

- **Reservoir (reservoir.lean-lang.org).** Indexing is automatic. Inclusion criteria, all four required: public GitHub source repository (private repos and forks, including repos generated from a template, are not indexed); a root file named `lake-manifest.json`; an OSI-approved license as detected by GitHub; at least 2 GitHub stars. Index updates about daily; if it does not appear after a few days, file an issue on Reservoir's tracker. https://reservoir.lean-lang.org/inclusion-criteria [READ]. It also builds packages on new toolchains and shows "builds" or "fails to build". [READ]
- **Mathlib policy on AI-written contributions.** Disclose AI use in the PR description; label substantial AI-generated code with the `LLM-generated` label; writing Zulip and GitHub comments with an LLM is not allowed; low-quality AI PRs may be closed without comment; repeated violations may lead to a ban from PRs and from Zulip. The page suggests a standalone repository depending on Mathlib. https://leanprover-community.github.io/contribute/index.html [READ]. This matters: any Zulip post announcing our work must be written by the human, in their own words.
- **Lean Zulip.** The AI-written proofs discussion (8 Nov to 15 Dec 2025, older) shows the community's norms: disclose, share prompts if possible, Kim Morrison proposed a MainTheorem.lean-style structure with a separate proof file; Chow warned against rules that push people to conceal AI use. [READ] https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.20proofs.html I could not read the Zulip "announce" channel or any other channel directly, so I cannot say which channel suits a post.
- **Lean community blog.** Only one post appears for September to November (the 21 Nov RH statement). I could not find submission instructions. [READ]
- **Lean Eval leaderboard.** Public benchmark of hard formalization problems; submissions of new problems are reviewed, and solutions are verified automatically with comparator. Not a place to announce an unrelated result unless the problems fit. [READ]
- **Palomar registry of Lean-verified mathematics (launched August 2026 per the Lean FRO timeline).** I found nothing on how to submit. [READ timeline only]
- **Lean Together.** My search returned only the unrelated Lean Enterprise Institute; I could not find a 2027 Lean Together page. [not confirmed]

---

## AI-disclosure norms

What the sources require or show (I could not retrieve full text of acknowledgments from specific real 2026 papers, so I give only the policy wording and structures I could actually read):

- **arXiv:** report significant use; AI cannot be an author; authors responsible for everything. [READ]
- **London Mathematical Society:** dedicated "AI Declaration" naming each tool and model number and how far it contributed, including proof construction and verification. [READ]
- **Elsevier:** declaration before references; tool, purpose, human oversight. Illustrative template (not official wording): the author used a named tool for a stated purpose, reviewed and edited the output, and accepts responsibility. [READ]
- **Taylor and Francis:** full tool name and version, how and why used; content generation acknowledged in Acknowledgments. [READ]
- **Springer Nature:** document in Methods; copy editing exempt. [SNIPPET]
- **JIS:** words must be the author's own; if an LLM suggested a proof, the paper must explicitly credit it. [READ]
- **Mathlib:** disclose in the PR; label; no LLM comments. [READ]
- **CPP/ACM:** work must reflect the authors' own intellectual contribution. [READ]
- **Community norms:** Tao has suggested disclosing AI use and sharing prompts and conversations, while saying that is not a complete solution (Nov 2025 Zulip thread, older). [READ] On 20 Nov 2026, his own post flagged AI involvement in each result and linked the Lean code; commenters asked for more detail on compute and prompting. [READ]
- **Example of real practice:** Anthropic's FLT post states that Claude agents wrote the proof and that human input was occasional high-level instruction. [READ] Alman and Vassilevska Williams credit an internal model for the discovery and formalization. [READ via Wikipedia]

Suggested disclosure content that would satisfy every policy above (my synthesis, not a quote): the tool name and version; what it did (idea generation, Lean proof search, drafting, literature search); what the human did and verified; that the final theorem statements were written or audited by the human; where prompts or transcripts are available if they are kept; and an explicit sentence that no AI is listed as an author.

---

## An honest read of what would make this work noticeable and what would not

What the evidence says is currently valued:
1. **A statement that can be audited in minutes.** The Lean community certified the 17-million-line RH proof because a small statement file, comparator and several checkers existed. [READ] Our results are far smaller and should be able to meet that bar easily.
2. **A named human who understands the mathematics** and can answer questions (Tao stressed Alpoge is a human author who can answer questions). [READ]
3. **Experts brought in early.** The Erdos #1196 case and the Goodman-Strauss tile case show outsiders' results became credible when specialists rewrote or co-authored them. [READ]
4. **Honest scope.** The FLT post and the Anthropic zeta post both state what they are not. [READ]

What is probably not going to work:
1. **Competing on headlines.** In the same three months the news has been dominated by Riemann, Navier-Stokes, Fermat, the finite simple groups. A BBP-type digit-extraction result has no natural hook against that. Coverage outlets I could read (Quanta Transformation, Tao's blog) cover claims from labs and well-known mathematicians; I found no example in the last three months of an outsider's small result getting coverage there, except the 3D tile (which had a medalist-level expert to condense it) and Barreto's 3-page proof (Barreto was already a co-author on #1196). [READ]
2. **An "AI solved it" framing.** The backlash (Fields medalists' declaration, AHM boycott, MathHelm) makes this a negative signal to mathematicians. YouTube commentators prefer big-lab framing. [READ]
3. **Posting to arXiv without endorsement.** Not possible; and a first submission that reads as AI-assisted from an unknown author is exactly what the rate limit and ban policies target. [READ]
4. **Zulip posts written with an LLM.** Banned on Mathlib's Zulip. [READ]
5. **A claim that rests on an unproven hypothesis without being loud about it.** Baker's theorem is proven, but the work says it takes it as a hypothesis; if that is presented as "conditional" it invites the wrong reading. (My inference.)

Realistic goal: not mass visibility, but acceptance by the small group who can check it: a public repository indexed on Reservoir with an OSI license, a one-file statement, a short human-readable note, a Zulip post written by the human in the appropriate channel (not confirmed which), and an approach to one or two named number theorists or Lean people for endorsement. I could not confirm that any named individual would respond to unsolicited requests.

---

## Queries used (28 WebSearch calls)

1. Erdős problems AI solved November 2026
2. Terence Tao AI mathematics Lean formalization October 2026
3. Lean AI formalization leaderboard lean-lang.org eval
4. AI mathematics breakthrough proof announced October 2026
5. Harmonic Aristotle OR "Math Inc" Gauss OR Axiom announcement Lean formalization September 2026
6. Kevin Buzzard Xena blog AI Lean Fermat Last Theorem formalization 2026
7. Levent Alpöge Riemann hypothesis Lean proof Claude Anthropic
8. Riemann hypothesis proof Claude Lean 17 million lines November 21 2026
9. YouTube video Claude Fermat's Last Theorem Lean proof AI math explained
10. Numberphile OR 3Blue1Brown OR "Two Minute Papers" OR "Matt Parker" OR "AI Explained" AI proves Riemann OR Erdős OR Fermat 2026 video
11. MathHelm forum discuss AI-generated papers
12. arXiv policy authors responsible AI-generated content cannot be author generative AI tools
13. arXiv math endorsement policy December 2025 math.NT new submitters
14. Journal of Integer Sequences OR Experimental Mathematics OR Integers journal policy generative AI authors disclosure
15. Springer Nature editorial policy AI authorship LLM cannot be author disclosure methods section
16. American Mathematical Society policy generative AI authors journals disclosure
17. Barreto Price Erdős problem 1196 Tao arXiv amateurs GPT paper
18. podcast episode 2026 AI mathematics Terence Tao OR Kevin Buzzard OR Jared Lichtman interview Lean proofs
19. newsletter AI for math weekly Lean formalization news roundup 2026
20. youtube.com OpenAI 722 math papers quasi-Riemann video explained reaction
21. YouTuber video "Fermat's Last Theorem" Claude Lean 13 million lines reaction channel
22. Axiom Math Classification of Finite Simple Groups Lean formalization October 2026 reactions mathematicians
23. Epoch AI FrontierMath GPT-6 Astra open problems Glazer polynomial variables controversy
24. Google DeepMind AlphaProof Formal Conjectures Gemini mathematics announcement October 2026
25. Harmonic Aristotle new release OR Math Inc Gauss announcement November 2026
26. Lean Together 2027 workshop dates
27. Experimental Mathematics journal instructions for authors AI tools Taylor Francis OR Integers journal De Gruyter AI policy
28. independent researcher amateur AI-assisted proof Lean Zulip announcement number theory 2026 how verified

Noted conflicts: search 8's summary said it found no evidence of a Riemann hypothesis proof in November and treated Anthropic's August 10 zeta-zero result as the only event; the Quanta column (20 Nov), Tao's blog (20 Nov) and the Lean community blog (21 Nov), all opened directly, show a 20 Nov claim by Alpoge. I trust the pages I opened over the search summary.

---

## Sources

- [Anthropic: formalizing Fermat's Last Theorem (4 Sep 2026)](https://www.anthropic.com/news/formalizing-fermats-last-theorem)
- [The Next Web: Buzzard on Claude's FLT formalization (6 Sep 2026)](https://thenextweb.com/news/anthropic-claude-fermat-last-theorem-lean-buzzard)
- [Trail of Bits: a "proof" of FLT that fits the margin (9 Sep 2026)](https://blog.trailofbits.com/2026/09/09/a-proof-of-fermats-last-theorem-that-fits-the-margin/)
- [Anthropic: Riemann zeta zeros result (10 Aug 2026)](https://www.anthropic.com/research/riemann-zeta)
- [Quanta Transformation, 20 Nov 2026 (Alpoge RH)](https://www.quantamagazine.org/update/169054/)
- [Quanta Transformation, items to 20 Nov](https://www.quantamagazine.org/update/168181/)
- [Quanta Transformation, Sep to Oct](https://www.quantamagazine.org/update/167694/)
- [Quanta Transformation, Aug to Oct](https://www.quantamagazine.org/update/166812/)
- [Quanta Transformation, 9 Oct](https://www.quantamagazine.org/update/167703/)
- [Quanta: AI proved the quasi-Riemann hypothesis (19 Oct 2026)](https://www.quantamagazine.org/ai-proved-the-quasi-riemann-hypothesis-what-happens-now-20261019/)
- [Quanta: how AI tore through a mathematical community (3 Aug 2026)](https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/)
- [Lean community blog](https://leanprover-community.github.io/blog/) (post of 21 Nov 2026 certifying the RH Lean proof)
- [Tao: Euler, Navier-Stokes, GRH (20 Nov 2026)](https://terrytao.wordpress.com/2026/11/20/unforced-euler-singularity-unforced-navier-stokes-singularity-and-the-generalized-riemann-hypothesis/)
- [Tao: What mathematicians should know about Lean (9 Oct 2026)](https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/)
- [Tao blog home (MathHelm, link roundups)](https://terrytao.wordpress.com/)
- [Wikipedia: list of mathematical discoveries made with AI](https://en.wikipedia.org/wiki/List_of_mathematical_discoveries_made_with_artificial_intelligence)
- [Datacamp: OpenAI math breakthroughs](https://www.datacamp.com/blog/openai-math-breakthroughs-what-the-latest-results-mean)
- [Al Jazeera: OpenAI discoveries (27 Oct 2026)](https://www.aljazeera.com/economy/2026/10/27/ai-makes-discoveries-in-mathematics-computer-science-physics-openai-says)
- [Tech-insider: pushback catalogue (secondary)](https://tech-insider.org/openai-math-problems-fields-medalists-2026/)
- [zeli.app: Vishnoi essay discussion (12 Oct 2026)](https://zeli.app/story/50061985)
- [Wes Roth video transcript (sozai.app)](https://sozai.app/transcript/openai-secret-model-breaks-math/)
- [Video summary, id Pp1siLlt-dI](https://youtubesummary.com/summary/Pp1siLlt-dI)
- [IEEE Spectrum: Axiom CFSG (18 Nov 2026)](https://spectrum.ieee.org/enormous-theorem-ai)
- [Epoch AI: FrontierMath Erdos (1 Sep 2026)](https://epoch.ai/latest/announcing-frontiermath-erdos)
- [Lean AI formalization leaderboard](https://lean-lang.org/eval/)
- [Lean FRO timeline](https://lean-lang.org/fro/about/)
- [Erdos problems AI contributions wiki (frozen 30 Jun 2026)](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)
- [Scientific American: amateur and Erdos #1196 (24 Apr 2026)](https://scientificamerican.com/article/amateur-armed-with-chatgpt-vibe-maths-a-60-year-old-problem)
- [Lean Zulip: AI-written proofs discussion (Nov 2025)](https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.20proofs.html)
- [arXiv: Lehalle, "When Proofs Are Abundant, What Is a Paper For?"](https://arxiv.org/abs/2611.12943)
- [arXiv endorsement help](https://info.arxiv.org/help/endorsement.html)
- [arXiv blog: updated endorsement policy (21 Jan 2026)](https://blog.arxiv.org/2026/01/21/attention-authors-updated-endorsement-policy/)
- [arXiv blog: math endorsement policy (10 Dec 2025)](https://blog.arxiv.org/arxiv/2025/12/10/updated-endorsement-policy-for-arxiv-mathematics)
- [arXiv blog: rate limit policy (1 Oct 2026)](https://blog.arxiv.org/2026/10/01/updated-rate-limit-policy/)
- [arXiv blog: review and position papers in cs (31 Oct 2025)](https://blog.arxiv.org/2025/10/31/attention-authors-updated-practice-for-review-articles-and-position-papers-in-arxiv-cs-category/)
- [arXiv moderation page (AI policy)](https://info.arxiv.org/help/moderation/index.html)
- [TechCrunch: arXiv one-year ban (16 May 2026)](https://techcrunch.com/2026/05/16/research-repository-arxiv-will-ban-authors-for-a-year-if-they-let-ai-do-all-the-work)
- [Journal of Integer Sequences](https://cs.uwaterloo.ca/journals/JIS/)
- [Taylor and Francis authorship and AI policy](https://authorservices.taylorandfrancis.com/editorial-policies/defining-authorship-research-paper/)
- [London Mathematical Society AI policy](https://www.lms.ac.uk/publications/policies/AI)
- [Elsevier generative AI policy](https://www.elsevier.com/en-au/about/policies-and-standards/generative-ai-policies-for-journals)
- [Springer Nature AI policy (search text only)](https://www.springer.com/us/editorial-policies/artificial-intelligence--ai-/25428500)
- [AMS use of AI policy (search text only)](https://ams.org/publications/journals/policies/UseofArtificialIntelligence)
- [Annals of Formalized Mathematics](https://afm.episciences.org/)
- [CPP 2027 call for papers](https://popl27.sigplan.org/home/CPP-2027)
- [Reservoir inclusion criteria](https://reservoir.lean-lang.org/inclusion-criteria)
- [Mathlib contribution policy incl. AI](https://leanprover-community.github.io/contribute/index.html)
