# R03: AI-assisted mathematics 2025-2026, what got attention and how it was received

Date of pass: 22 November 2026. Helper thread R03.
Marking: [READ] = read on the fetched page (the fetch tool returns a model-made digest of the page,
so details such as exact numbers are as reported by that digest); [SNIPPET] = seen only in a
search result; [INFERRED] = my own conclusion. Nothing in this report is quoted verbatim.
Many sources are news pages and aggregators dated within the last weeks; the situation around
the Riemann-hypothesis claim changes by the hour.

## 1. Summary

1. The big picture [READ]: from late 2025 AI systems (public GPT models, Gemini agents, Harmonic's
   Aristotle, OpenAI and Anthropic internal models) moved from literature search to genuine
   solutions of Erdos problems, then (2026) to results that experts call serious: the unit
   distance disproof (May), cycle double cover (July), a Jacobian-conjecture counterexample
   in dimension 3 (July), a large partial result on zeta zeros (August), the "quasi-Riemann
   hypothesis" (October), and on 20 November 2026 a Lean-only claim of the Riemann hypothesis.
2. Riemann hypothesis, 20-22 Nov 2026 [READ, secondary sources]: CONFIRMED: a note and a Lean
   development (about 17 million lines, 175,187 modules) were posted by Levent Alpoge (Anthropic)
   with Claude; independent Lean checkers (Sutherland's page: kernel, nanoda, lean4lean and others)
   accept it using only the three standard axioms; the Lean community and Mathlib Initiative issued a
   joint statement of confidence on 21 Nov. NOT CONFIRMED: that humans understand it; any readable
   proof; peer review; Clay prize (still listed unawarded); one public critique (Nielsen) says a
   geometry predicate is defined as True deep in the dependency chain, with no public rebuttal
   found.
3. Norms have crystallised in 2026: the Leiden Declaration (2 June 2026, IMU-endorsed, 4,458
   signatories) says disclose AI use, humans stay responsible, hunt for prior work, give formal
   proofs where feasible. Mathlib requires AI disclosure in the PR text (merged 27 Jan 2026) and
   a label `LLM-generated`; arXiv bans unchecked LLM content (one-year ban, May 2026).
4. Outsiders: the first AI-era Erdos successes were by hobbyists and undergraduates, but they
   survived only with (a) literature checks, (b) a named expert verifying, (c) often a Lean
   check. The failure modes are exactly: "already in the literature", unreadable length,
   misformalized statements, overclaiming.
5. For this project [INFERRED]: the best-received form of an outsider contribution in 2026 is a
   short, human-explained, literature-checked result with a formal proof whose statement was
   cross-checked by a third party, disclosed as AI-assisted, posted where specialists look
   (arXiv math.NT plus a pointer in the relevant community), not a press-style announcement.
   A Lean proof of a "known but unproved in print" claim fits the category the Erdos
   community calls "formalization / secondary contribution" and is valued as such; it is not
   a headline but it is safe from the "novelty" attack if the framing is honest.
6. Mathlib is NOT a good first destination for large AI-written development: maintainers want
   small, understood, human-supervised PRs, not wholesale AI output; keep the work downstream
   as its own repository first.

## 2. What is known

### 2.1 Dated list of results that drew attention (Q1)

Informal = natural-language proof judged by humans; formal = Lean-checked.

- Jul 2025, IMO: OpenAI and DeepMind each claimed gold-level performance in natural language;
  Tao and Buzzard criticised the lack of reproducible conditions and fair comparison; one
  OpenAI solution reportedly scored zero when graded [READ, Wikipedia IMO page]. Aristotle (Harmonic) also
  reported top-level performance [READ, Wikipedia Harmonic page; the page does not say "gold"].
- Oct 2025: OpenAI executives said GPT-5 solved ten open Erdos problems; Thomas Bloom called this a
  dramatic misrepresentation, since the model had located existing literature [READ, Wikipedia
  "Erdos problems"]. Origin of the "already in the literature" reflex.
- Oct-Nov 2025: Wouter van Doorn (non-professional) progressed Problem 1102, accepted by Tao
  in the comments [READ, Quanta 2026-08-03].
- 25 Dec 2025: Kevin Barreto posted an apparently autonomous AI solution of Erdos 333; it was an
  old Erdos result of 1977. He retracted and urged literature searches [READ, Quanta].
- 4 Jan 2026: Barreto and Liam Price, GPT-5.2 Pro, solved Erdos 728; Aristotle checked the logic;
  Nat Sothanaphan had ChatGPT write the formalized version [READ, Quanta]. Informal proof plus
  Lean check. Tao called it little human intervention [READ, Wikipedia].
- 29 Jan 2026 (v3 5 Feb): Google DeepMind team (24 authors incl. Barreto, Tao-circle number theorists),
  Gemini screening of 700 open Erdos problems: 13 addressed, 5 apparently novel solutions, 8
  matched to existing literature; conclusion: "open" often means obscure, not hard; they flag
  "subconscious plagiarism" risk. arXiv:2601.22401 [READ abstract].
- Feb 2026, "First Proof": 10 research-level lemmas posed by 11 mathematicians (Abouzaid,
  Hairer, Williams and others); AIs produced confident proofs for all, only two correct at first
  look; most outside submissions unconvincing [READ, Scientific American]. Second batch June
  2026 (arXiv:2606.18119): fully autonomous, blind expert grading, 4 systems, 7 of 10 problems
  got an acceptable solution [READ, via Boldt's paper intro].
- 24 Apr 2026: internal OpenAI model, Erdos 1196 (primitive sets); Price had earlier posted a
  GPT-5.4 Pro proof; a paper with Tao, Lichtman, Barreto, Price resolved 1196 in May [READ,
  Quanta; PhysicsWorld; Wikipedia]. Lichtman: fits Erdos's idea of a "Book proof".
- 20 May 2026: OpenAI internal model disproves Erdos's unit distance conjecture (1946) by a
  construction from algebraic number theory; Alon, Bloom, Gowers, Litt, Sawin, Shankar,
  Tsimerman, Wood wrote "Remarks" (arXiv:2605.20695); Lean formalization one month later
  [READ, Boldt; Quanta]. Gowers: a human paper of this quality would be accepted quickly at a
  top journal [READ, Quanta]. NYT: some experts saw it as close to earlier human work
  [SNIPPET].
- 2 Jun 2026: Leiden Declaration on AI and Mathematics (see 2.3) [READ].
- 8 Jun 2026: Science paper on AI-driven formal proof search (cited) [READ, Wikipedia AI&math].
- 10 Jul 2026: OpenAI proof of the cycle double cover conjecture, prompt published, Lean
  formalization of the prior work and the proof on GitHub [READ, Boldt].
- 20 Jul 2026: Jacobian conjecture counterexample in dimension 3 (explicit degree-7 map,
  checkable by a short calculation), announced by Levent Alpoge on X with a Claude model;
  Tao wrote a "digestion" on 21 Jul and disclosed his own chatbot use; attribution disputed in
  comments; an independent OpenAI Codex finding of the same example was also reported
  [READ, Tao blog; Boldt]. Informal, but verifiable by hand.
- 1 Aug 2026: OpenAI "Astra" announcement, ten advances including non-sofic group (reported) and
  three Erdos problems [READ, Quanta; Wikipedia AI&math].
- 11-12 Aug 2026: Anthropic: unreleased Claude raised the proved proportion of zeta zeros on the
  critical line from 41.6% to 67.2%, from combining prior work; Lean formalization (by a human
  with Claude) passes the "comparator" tool; two Anthropic mathematicians vetted it. Maynard:
  genuinely interesting, but no route to the real Riemann hypothesis [READ, Anthropic page;
  Scientific American].
- 7 Sep 2026: Nature news: Anthropic AI formalizes the proof of Fermat's last theorem
  (title and date only, via Crossref; article behind a login) [SNIPPET].
- 8 Sep 2026: OpenAI claims an unbounded counterexample to Navier-Stokes regularity; not
  externally verified; a preprint found statement mismatches between its Lean and written
  versions [READ, Wikipedia AI&math; Science News].
- 6 Sep 2026: FrontierMath Erdos benchmark (Adamczewski, Bloom, arXiv:2609.25050): 68 open
  problems to prove or disprove in Lean at $300 per problem; only the best system solved 3%
  [READ abstract].
- 29 Sep 2026: Advisory Group on Mathematics and AI urged companies to stop testing models on
  open problems [READ, Wikipedia AI&math; Science News].
- 6 Oct 2026: OpenAI posted 722 AI-written manuscripts, many with Lean proofs; 8 Oct DeepMind's
  AlphaProof Nexus (Science, peer reviewed) solved 9 Erdos problems; Bloom stopped
  labelling Erdos problems open or solved and closed comments; he praised DeepMind, said he
  does not want to referee AI output [READ, Science News].
- 30 Sep / 5-6 Oct 2026: OpenAI "quasi-Riemann hypothesis": a 199-page version (zeros between
  1/8 and 7/8, Lean-verified) and a 49-page human-edited version (1/12 to 11/12, not formally
  verified, the one experts study). Radziwill can sketch the core in half a page; Sarnak will not
  call it a theorem until humans check; Lichtman: most significant AI-for-math result so far;
  both papers poorly written [READ, Quanta 2026-10-19].
- 13 Nov 2026: MathHelm forum announced (Tao blog) for discussing AI papers; principle: mathematicians
  have no obligation to check such papers, partial comments welcome [READ].
- 20 Nov 2026: Alpoge, Buckmaster, Coiculescu (heavy AI help): human-readable proof of Euler
  finite-time blowup with Lean; Alpoge and Buckmaster similar Navier-Stokes claim; Tao: readable
  strategy but needs professional writing [READ, Tao blog].
- 20 Nov 2026: Alpoge's Lean-only proof of GRH (see Summary item 2). Details below.

### 2.2 The Riemann hypothesis claim of 20 November 2026: confirmed vs claimed

- Claim: note dated Friday 20 Nov on the author's site, hedged ("I believe"); method also gives GRH
  (Dirichlet L-functions); Lean code only, about 17.4 million lines; development period 6 Oct to
  16 Nov; no readable paper (a 4-page sketch exists; a figure of 250,000 pages for a prose version
  is an unsourced commenter figure) [READ: Wikipedia RH, OfficeChai, explainx digest].
- Verified by machine [READ, secondary, relaying Sutherland's page]: 175,187 modules compile
  with zero errors (Lean v4.33.1); nanoda and lean4lean accept; a comparator-type check matches
  the five challenge theorems; headline theorems use only the three standard axioms; end-to-end
  `lake comparator` and full kernel replay were still running at 04:35 UTC on 22 Nov. Elliot Glazer
  says the formal statement is GRH.
- Endorsed: Lean community and Mathlib Initiative joint statement, 21 Nov 13:55 UTC, "full
  confidence" [READ, explainx digest of the Lean blog].
- Not established: human understanding. Tao's preliminary view: it appears to use the full
  modern Langlands and arithmetic-geometry machinery; Granville criticised the clarity of the
  4-page sketch and the timing; Radziwill: the formalization lacks human-level understanding;
  Alpoge predicts large simplification; Kit Yates, others: humans must confirm the Lean
  statement means what it says; a Nielsen critique (PhilArchive, DEV audit) about a predicate
  defined as True, unrebutted publicly [READ digests; I did not open the primary Lean sources].
- Institutional: Millennium table says claimed, prize pending; an AHM statement and a DMV paper
  on the announcement were linked by Tao on 21 Nov [READ, Tao blog]. A September declaration
  by 25 Fields medalists warned against rushed AI proof releases [READ, OfficeChai digest].
- Earlier "RH" items that are NOT proofs of RH: Anthropic's 67.2% zeros result (August) and
  OpenAI's quasi-RH (October). Scientific American's headline "no, AI did not solve the
  thorniest problem" (Aug) concerns the August item [READ].
- My own judgment [INFERRED]: the Lean side is about as well checked as anything of this size
  can be within two days; the unresolved question is human-level statement fidelity (definitions)
  and interpretability; treat as "machine-checked, community certified, not yet understood".

### 2.3 Current norms (Q3)

- Leiden Declaration on AI and Mathematics, 2 Jun 2026, IMU-endorsed, 4,458 signatories [READ]:
  disclose any use of AI or automated tools; humans remain fully accountable for correctness and
  citations; authors must actively search for prior work because AI attribution is weak, and say so
  when attribution is impossible; formal proofs encouraged where feasible but translation errors
  are a risk; referees follow publisher rules; institutions should demand human-written
  explanations of key arguments, cross-checking and external pre-submission review; results
  should still go through peer review, not press releases.
- Boldt, arXiv:2608.29401 (29 Aug 2026), math.HO [READ, PDF]: authors reporting LLM results
  should give human explanations, formal verification, and the exact model, prompt and harness;
  a higher burden of proof than for human authors is defended as protecting the pipeline; he
  would not demand Mathlib-canonical formalizations from authors.
- Mathlib / Lean community [READ]: the contribute page has a "Use of AI" section: LLM text must not
  be used for GitHub or Zulip comments; unsupervised AI-written code does not meet standards;
  low-quality LLM PRs may be closed without comment, especially if the idea was not discussed
  first; repeated violations can lead to suspension or ban; AI use must be explained in the PR
  description (tools and how); `LLM-generated` label for substantial AI input; the contributor must
  understand and be able to justify everything without AI. The policy PR (leanprover-community
  website #767) was merged on 27 Jan 2026 [READ]. A resubmitted Mathlib PR (45946, Nov 2026) is
  noted as following the close of an original PR (44790) for undisclosed AI use [READ, GitHub
  search digest]. Many `LLM-generated` PRs are open in Nov 2026 (Mertens' theorem, Gauss sum
  modulus, Pascal hexagon and others), so AI-written PRs are accepted for review when disclosed
  [READ].
- Maintainer opinion (Commelin, Feb 2026, stated as personal): AI code is too cheap to justify
  reviewer time; wholesale adoption endangers quality; battle-test downstream first; Mathlib is not
  interested in "proved reductions" of known results; check for duplicates of existing Mathlib;
  statements without proofs are not accepted [READ, Zulip thread "Potentially useful results from
  an AI-assisted formalization"]. Loeffler found `def X : Prop` placeholders and a `True`
  placeholder in an AI-written repository [READ].
- Zulip debate on AI proofs (Nov-Dec 2025) [READ]: Riehl proposes a higher, formal standard for
  AI-generated mathematical text; Tao: machine proofs can be right yet lack insight; Chow:
  origin should not decide credibility, verification should, and high bars encourage hiding;
  Morrison proposed that AI-generated Lean repositories be accepted as "counting" only with a
  `MainTheorem.lean`-style file stating the theorem; Chow reminded that a formal proof can still
  be wrong if the statement or trusted base is flawed.
- Tao's PrimeNumberTheorem+ practice [READ]: `Co-authored-by` trailers for AI tools, a PR template
  with a disclosure question, noting which parts were manual and which done by Aristotle, optional
  session logs.
- arXiv [READ, THE and arXiv blog]: 31 Oct 2025, CS category requires accepted peer review
  for review and position papers (response to LLM-generated surveys); this does not apply to
  research papers. May 2026: general policy (announced by Dietterich): a first offence with
  incontrovertible evidence of unchecked LLM content (hallucinated references, leftover chatbot
  text) brings a one-year ban, then a peer-reviewed paper is required before posting again;
  appeals allowed; enforceability questioned. I did not find a math-specific AI policy page; the
  arXiv policies index fetched had no AI text [READ, not found].
- Journals: I could not read the Springer, Elsevier or AMS AI policy pages (login redirect and
  403). [Not found.] The Leiden Declaration says many journals already require a tool-use
  section [READ]. Commonly stated publisher rule (AI is not an author, human authors answer for
  content, disclose use) is from my background knowledge [INFERRED], not verified in this pass.
- Erdos problems site (Bloom) and Tao's wiki [READ]: the wiki ("no longer updated", data to 30 Jun
  2026) classes AI work as standalone, alongside literature, building on literature, collaborative
  and secondary (literature search, formalization, rewriting, computation); encourages Lean
  formalization; its disclaimers warn about incomplete literature reviews, misstated problems,
  obscurity versus difficulty, misformalization, and that a solution alone does not guarantee a
  journal paper. Bloom in October 2026 stopped open/solved labels and closed comments [READ,
  Science News]. Plasma AI launched a rival tracker that welcomes AI results [READ].
- Referee treatment [READ/INFERRED]: Bloom does not want to referee AI output; MathHelm says
  mathematicians owe no checking; the Advisory Group asks labs to stop testing on open problems;
  Kra worries about leaks of unpublished ideas to models. Expect specialists to give partial,
  voluntary review, so the submitter must lower the checking cost.

### 2.4 Non-professionals and AI-assisted proofs (Q2)

Worked [READ, Quanta, PhysicsWorld, Wikipedia]:
- Price (left college, uses one chatbot to critique another, recruits mathematicians to verify),
  Barreto (Cambridge undergraduate), Sothanaphan (software engineer), van Doorn (customer-service
  employee, near-finished master's). Common elements: public problem forum with comments,
  an expert reading it (Tao, Bloom), Lean via Aristotle, short proofs, honest credit to AI,
  co-authorship with professionals on the paper (Erdos 1196).
- Bloom: most early AI results came from hobbyists and undergraduates using public models.

Failed or dismissed:
- Erdos 333 (already solved in 1977), the October 2025 "ten problems" claim (literature
  search, not new). Cause: no literature check.
- Large unread AI papers (100 to 200 pages) posted by people who cannot verify them: Bloom calls
  this a huge challenge [READ, Quanta].
- Most outside First Proof submissions unconvincing [READ].
- Lean repositories written by AI swarms with placeholders: statements as `def ... : Prop`,
  duplicates of Mathlib, "reductions" of known results; maintainers declined interest
  [READ, Zulip].
- Misformalization: Lean proves what is stated; statement mismatches found in OpenAI's
  Navier-Stokes Lean [READ, Science News]; Tao's wiki warns about proofs that exploit
  unproved axioms or misread problems.
- Why dismissed [INFERRED, summarising the above]: (1) novelty (prior literature),
  (2) unverifiable text (length, no human explanation), (3) overclaiming (headline before
  verification), (4) statement fidelity, (5) volume fatigue of the reviewers.
- Tao's FAQ for people who think AI solved an Erdos problem (ten steps) [READ]: stay skeptical;
  check you can explain it without the AI text; confirm you solve the intended statement (read
  Erdos's original); do a literature review forward and backward; be suspicious of a suspiciously
  short or elementary proof or one not using all hypotheses; ask another AI for critical review
  (AI flatters); write to professional standards; formalize in Lean and have a human or third
  party formalize the statement; announce with links on the problem page; avoid social media
  announcements first; be patient.

## 3. What is open

- Whether the 20 Nov RH/GRH Lean development is a proof of the intended statement at the level
  of human definitions: asserted by the Lean community, disputed in one public critique; no
  readable proof [READ digests; stated as unresolved by the sources].
- Mathlib's formal policy on how much AI-written Lean may be merged: contribution page rules
  exist; no explicit threshold for "substantial" use found [not found].
- Journal-by-journal policy for AI-assisted number theory papers: not read (paywalls); unknown.
- Whether arXiv math moderators treat AI-assisted math preprints from unaffiliated authors
  differently (endorsement, math.GM/math.NT): not found.
- Credit and authorship of AI results is inconsistent (the unit distance paper credited only
  "OpenAI"; the Jacobian attribution disputed) [READ].

## 4. Leads for this project (ranked; these concern presentation and placement) [INFERRED]

1. Write the base-10 / "power of 2" theorem as a "formalization of a claim that is stated in print
   without proof" paper. Exact statement to present: for integer base b with |b| not a power of 2
   there is no degree-1 BBP-type formula for a non-zero rational multiple of pi; the literature
   (Bailey Compendium citing Borwein-Borwein-Galway) states it as known but proves only the
   Machin-type case. Fit: this is the "secondary contribution / literature gap" class that the
   Erdos wiki and the Leiden Declaration value (prior work found, claim attributed honestly,
   formal proof supplied). Size: days to write, with an honest "what the cited paper proves"
   section. Notice-worthy because it corrects a citation chain, which is what number theorists
   care about.
2. Add a short human-written explanation (Boldt, Leiden, Tao FAQ step 2): a 3-5 page note that
   states the theorems, the key idea (Baker, primitive prime divisors, cyclotomic prime ideals),
   and what the Lean files add. Size: days. Reason: the single most repeated complaint is
   unexplained machine output.
3. Third-party statement check: publish a `Main.lean`/`MainTheorem.lean` file with only the
   statements and definitions, using Mathlib definitions where possible, and ask a Lean user to
   review them (Tao FAQ step 8; Morrison proposal; Chow's warning). Run `lean4checker` or
   the comparator tool and state axioms used (the Riemann-claim checks use the same
   tools). Size: days.
4. Venue plan: arXiv math.NT (with moderate-length paper and a "Use of AI" statement); then a
   journal for computational/experimental number theory or an elementary journal [INFERRED, not
   verified in this pass]; keep the Lean repository downstream (own repository, released with a
   Zenodo DOI), and consider PRs to Mathlib only for small general lemmas written or fully
   understood by a human, with disclosure and the `LLM-generated` label.
5. Consider whether to contribute statements to google-deepmind/formal-conjectures [READ: open to
   issues and PRs with human review; AI-formalization policy not stated on its front page]. This
   is for open problems only; the project's results are proved, so low value unless a clean open
   question comes out (for example the "uniqueness in Theorem E" gap in the project notes).
6. Keep the "AI use" statement specific: tool, version, role, prompts or session logs if they
   can be shared (Boldt; Tao PR practice), and list who checked what. Size: hours.

## 5. Overlap or conflict with the project results

None found in this thread. R03 covers norms and publicity, not BBP-type formulas. One
indirect point: the project already meets several 2026 requests (Lean, standard axioms, no
hypothesis); what it still lacks relative to the norms is the human explanation and an
independent statement check [INFERRED].

## 6. Sources

Read (fetched): 
- https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/
- https://www.quantamagazine.org/why-the-legendary-erdos-problems-are-falling-to-ai-20260803
- https://quantamagazine.org/ai-proved-the-quasi-riemann-hypothesis-what-happens-now-20261019
- https://www.anthropic.com/research/riemann-zeta
- https://scientificamerican.com/article/no-ai-didnt-just-solve-the-thorniest-problem-in-math
- https://www.scientificamerican.com/article/first-proof-is-ais-toughest-math-test-yet-the-results-are-mixed/
- https://arxiv.org/abs/2601.22401 ; https://arxiv.org/abs/2609.25050 ; https://arxiv.org/abs/2608.29401 (PDF read)
- https://physicsworld.com/a/ai-led-solutions-of-erdos-problems-spark-debate-over-the-future-of-mathematics/
- https://www.sciencenews.org/article/math-human-ai-age
- https://en.wikipedia.org/wiki/Riemann_hypothesis ; /Erd%C5%91s_problems ; /Artificial_intelligence_and_mathematics ; /International_Mathematical_Olympiad ; /Harmonic_(company)
- https://officechai.com/ai/how-mathematicians-have-reacted-to-claimed-riemann-hypothesis-proof-by-anthropics-levent-alpoge/
- https://explainx.ai/blog/levent-alpoge-anthropic-riemann-hypothesis-claude-lean-proof-claimed-vs-verified-2026
- https://terrytao.wordpress.com/ ; https://terrytao.wordpress.com/2026/07/21/a-digestion-of-the-jacobian-conjecture-counterexample/
- https://leidendeclaration.ai/
- https://leanprover-community.github.io/contribute/index.html
- https://github.com/leanprover-community/leanprover-community.github.io/pull/767
- https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/policy.20proposal.3A.20mention.20AI.20use.20in.20PR.20description.3F.html
- https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Potentially.20useful.20results.20from.20an.20AI-assisted.20formalization.html
- https://leanprover-community.github.io/archive/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.20proofs.html
- https://leanprover-community.github.io/archive/stream/423402-PrimeNumberTheorem+/topic/Disclosure.20of.20AI.20tools.20in.20PRs.html
- https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems (and the Disclaimers and FAQ pages)
- https://blog.arxiv.org/?p=1740 ; https://www.timeshighereducation.com/news/ban-authors-submitting-ai-content-welcome-unenforceable
- https://github.com/google-deepmind/formal-conjectures
Snippet only: Nature news (DOI 10.1038/d41586-026-02822-9, login wall); the-decoder (paywall);
NYT report on the unit distance result (via search result); search-result pages on the RH claim
(pasqualepillitteri.it, cryptobriefing, felloai, shattered.io: aggregators, not used for facts).
Page content addressed to me: none found.

### Search log

WebSearch (6): 
1. Erdos problems solved by AI 2026 mathematicians reaction
2. Riemann Hypothesis proof claim AI November 2026
3. Mathlib policy AI-generated contributions
4. arXiv policy AI-generated papers 2026 review articles position papers moderation
5. Riemann hypothesis claimed proof Lean formalized announcement mathematicians skeptical
6. amateur AI-assisted proof dismissed mathematicians LLM crank submissions journals ...

Endpoint and page queries via the fetch tool (62; about 12 failed: 403 for erdosproblems.com,
AMS, erdosproblems forum; 429 for the GitHub API (second try), arXiv API (two), OpenAlex
(two), Semantic Scholar (two); 404 for Wikipedia AlphaProof and Seed-Prover; login redirect for
Nature and Springer):
1 erdosproblems.com; 2 GitHub issues API mathlib4 "AI policy"; 3 arXiv API Erdos+AI;
4 Quanta 20260803a; 5 Quanta quasi-RH; 6 Anthropic riemann-zeta; 7 SciAm no-ai; 8 arXiv 2601.22401;
9 Zulip policy proposal; 10 Lean contribute page; 11 website PR 767; 12 GitHub label API;
13 OpenAlex RH+AI; 14 arXiv API RH+Lean; 15 Tao wiki AI contributions; 16 Crossref AI proof
policy; 17 Semantic Scholar AlphaProof; 18 Quanta 20260803b; 19 PhysicsWorld; 20 arXiv blog;
21 Wikipedia RH; 22 OfficeChai; 23 explainx; 24 arXiv PDF 2608.29401; 25 Zulip AI-written proofs;
26 Science News; 27 arXiv abs 2608.29401; 28 Nature; 29 Crossref Nature FLT; 30 Semantic Scholar
Seed-Prover; 31 formal-conjectures; 32 SciAm First Proof; 33 doi.org Nature; 34 lean-lang blog;
35 OpenAlex Aristotle; 36 Crossref Erdos LLM; 37 The Decoder; 38 Epoch PDF; 39 Nature retry;
40 arXiv 2609.25050; 41 Tao blog home; 42 Springer; 43 arXiv policies index; 44 THE;
45 Springer retry; 46 AMS; 47 Wikipedia Erdos problems; 48 Wikipedia AlphaProof; 49 Wikipedia AI and
mathematics; 50 erdosproblems forum; 51 Wikipedia Harmonic; 52 Wikipedia Seed-Prover; 53 Wikipedia
IMO; 54 Zulip potentially useful; 55 Zulip disclosure; 56 LiveScience; 57 Tao blog 2026-11-13;
58 Tao wiki home; 59 Leiden Declaration; 60 Tao FAQ; 61 Tao disclaimers; 62 Tao Jacobian post.
(Plus one local read of the saved Boldt PDF.)

Totals: WebSearch calls = 6; endpoint/page queries = 62.
