# R04: where an unaffiliated author can publish machine-checked number theory (late 2026)

Date of pass: 22 November 2026. Marks: [READ] = read on the source's own page through the fetch
tool (note: the fetch tool returns a model-made summary of the page, not raw text, so
"read" here means "page content as summarized by the fetch tool"); [SNIPPET] = only in a
search result or API record; [INFERRED] = my own conclusion.
Many publisher sites (Springer, T&F, AMS, MAA, fq.math.ca, MathOverflow) refused
automated access (403/redirect to login); where so, the item is marked "not obtained".

## 1. Summary

1. arXiv math tightened sharply: since 10 Dec 2025 (extended to all sections 21 Jan 2026)
   a first-time submitter to math needs a PERSONAL endorsement unless they have both an
   academic e-mail and a claimed, accepted math paper. For an unaffiliated author with no
   prior papers, personal endorsement is the only route. [READ]
2. arXiv added a rate limit on 1 Oct 2026: 2 submissions per calendar month per submitter,
   on top of 3 active at once; rejected papers count. [READ, secondary: Socket article
   summarizing the arXiv post; the arXiv post itself was not retrievable]
3. arXiv AI policy (May 2026): LLM use is not forbidden, but evidence of unchecked LLM
   output (fake references, leftover prompts) gives a one-year ban, after which new
   submissions must first be accepted by a peer-reviewed venue. [READ]
4. The best-fitting venue for "paper plus public Lean repository" is the Annals of Formalized
   Mathematics (AFM, diamond open access, no fees, formal artifact mandatory). BUT: it states
   that only human-authored manuscripts are accepted, requires an AI-use disclosure for
   text and code, and its scope excludes formalizations of known results without new
   mathematical insight. Our results (new classification theorems) are in scope; the
   author-side wording is the risk. [READ]
5. Journal of Integer Sequences (JIS) forbids LLM-written text; undisclosed AI use means
   rejection and possibly a lifetime ban; LLM-suggested proof ideas must be credited.
   Median time to final decision, vol. 28 (2025): 197 days. No fees. [READ]
6. ITP 2027 (Glasgow, 2-7 Aug 2027): abstract 8 Feb 2027, paper 15 Feb 2027, 16 pages, formal
   artifact required, double-blind, substantial AI-generated text not allowed, AI use in
   formalization must be described. CPP 2027 deadlines (10 Sep 2026) have passed; the next CPP
   deadline will be about September 2027 [INFERRED from the 2027 pattern]. [READ]
7. Precedents exist for exactly this kind of paper on arXiv math.NT with Lean and AI
   assistance: Banwait (Ramanujan-Nagell in Lean, math.NT + cs.LO), Fukui (Lean, Zenodo +
   GitHub), Kimura (class number <= 2000, Lean, AI contributions stated in abstract),
   van Doorn-Monticone-Tang (Lean proof by the Aristotle system stated in abstract). [READ]
8. Lean community now wants specific things from a claimed Lean proof of a notable result
   (project builds with lake build, #print axioms only standard, statement faithful,
   expert check). Our repository should be made to satisfy this checklist verbatim. [READ]
9. Reservoir (Lean package index) needs: public GitHub repo, root lake-manifest.json,
   OSI-approved license, at least 2 stars. [READ]
10. Informal advice from mathematicians agrees: short, personal, one named recipient, a
    narrow question about one step, work polished; many will not answer. [READ, thin]

## 2. What is known

### 2.1 Journals (question 1)

Evidence that these journals take BBP-type/computational papers from non-mainstream
authors (found through Crossref and zbMATH records):

- Integers: Adegoke, "A novel approach to the discovery of binary BBP-type formulas for
  polylogarithm constants", Jan 2012. [SNIPPET]
- Notes on Number Theory and Discrete Mathematics (NNTDM): Adegoke, Oliver Lafont, Layeni,
  "A class of digit extraction BBP-type formulas in general binary bases", vol. 17 no. 4,
  2011. [SNIPPET]
- Fibonacci Quarterly: Adegoke, "A new binary BBP-type formula for sqrt5 log phi", 2014; the
  record lists a physics department in Nigeria. [SNIPPET]
- Journal of Integer Sequences: Adegoke and Oliver Lafont, golden-ratio-base expansions of
  log and arctan of Fibonacci and Lucas numbers, vol. 26 no. 5, 2023. [SNIPPET]
- The Ramanujan Journal: Takahashi, BBP-type formulas computation and verification (2019/20);
  Montgomery multiplication in binary BBP computation (2022). [SNIPPET]
- Euleriana (Univ. of the Pacific): Craig-Wood, "Euler found the first binary digit
  extraction formula for pi in 1779", 2023; affiliation recorded as none. [SNIPPET]
- Functiones et Approximatio: Adegoke, formal proofs of degree 5 binary BBP-type formulas,
  2013. [SNIPPET]
- Canadian J. Math 2004 (Borwein-Borwein-Galway), Acta Arithmetica 2021 (Barsky-Munoz-
  Perez-Marco, genesis of BBP formulas), Math. Comp. 1997 (Bailey-Borwein-Plouffe) are the
  mainstream anchors. [SNIPPET]
- [INFERRED] Small specialist journals (JIS, Integers, NNTDM, Fibonacci Quarterly) are
  where BBP-type papers by non-academic authors actually appear; no Math. Comp. or
  Monthly paper by an unaffiliated author on BBP was found (not found is weak evidence).

Journal by journal (scope, fees, time, AI, formal supplement):

| Journal | Scope | Fees | Time | AI policy | Formal artifact |
|---|---|---|---|---|---|
| JIS | integer sequences, explicit link to sequences, cite OEIS | none, no APC; editors unpaid [READ] | median 197 d to final decision (vol 28); referees asked for 2 months, finding one can take months [READ] | no LLM-written text; LLMs may find references (verify) or suggest proof ideas (credit them, check); undisclosed use = rejection, possible lifetime ban; editors may use AI for screening [READ] | not mentioned; LaTeX source only, one archive [READ] |
| Integers | combinatorial number theory, additive/multiplicative NT, sequences [READ] | free to submit, no charges [READ] | not stated | not stated on the page I could read (the instructions page returned 404) | not found |
| Experimental Mathematics (T&F) | results inspired by experiment, conjectures, supporting data; must have experimental aspect and relevance to math proper [SNIPPET] | APC/open-access option not obtained | single-anonymized review [SNIPPET]; time not obtained | T&F general policy: AI cannot be an author; a "Declaration of generative AI use" naming tool, version, purpose is required; AI copy-editing allowed with verification of references [READ] | experiments must be repeatable, programs encouraged; referees may request code [SNIPPET]. A Lean repository fits this spirit [INFERRED] |
| Ramanujan Journal (Springer) | not obtained | not obtained | not obtained | Springer site blocked; common Springer rule (AI not an author, disclose) is [INFERRED], not read | not obtained |
| Math. Comp. (AMS) | not obtained (site 403) | not obtained | not obtained | not obtained | not obtained |
| Amer. Math. Monthly (MAA) | not obtained (403) | | | | |
| Fibonacci Quarterly | not obtained (site 404) | | | | |
| NNTDM | elementary NT, arithmetic functions, primes, Fibonacci, Diophantine, combinatorics [READ] | no author charges; only print copies cost money (60 EUR/copy) [READ] | not stated | not stated (ethics page not found) | not found |

[INFERRED] None of the classical number theory journals advertises acceptance of a formal
proof artifact as a supplement; the safe course is to cite the repository in the paper
and archive a tagged release (see 2.4). Experimental Mathematics and AFM are the two where
code/artifact is in the journal's own culture.

Also relevant: Annals of Mathematics requires an AI-use declaration with every submission;
AI cannot be an author. [READ] Not a target, but shows the 2026 norm.

### 2.2 Formalization venues (question 2)

- Annals of Formalized Mathematics (AFM; Episciences overlay; MathOA). [READ]
  - Diamond open access, CC BY 4.0, no charge to publish or read; single-blind review.
  - Procedure: first deposit the manuscript in an open archive (HAL, arXiv or Zenodo),
    then submit through Episciences (or through HAL's publishing service); accepted papers
    stay in that archive. Zenodo suffices, so arXiv endorsement is NOT needed for AFM.
  - "All AFM submissions must correspond to a formal artifact"; main results must link
    explicitly to code; code open source and accessible to referees; a Software Heritage
    identifier (SWHID) is invited.
  - AI: only human-authored manuscripts; mandatory disclosure of whether AI was used for the
    manuscript, the code or both, with tools and tasks; funding and subsidized tool access
    must be disclosed.
  - Scope: new mathematical novelty or insight; formalizing known results without insight
    is out of scope "even if AI tools were used"; authors must show how formal statements
    match informal ones and flag possible mismatches; reviewers' criteria include novelty of
    the mathematics, generality, library integration, readability of code. Papers should
    address a general mathematical audience.
  - Volume sizes: AFM 1 (2025) and AFM 2 (2026) contain Lean papers such as Loeffler-Stoll
    (zeta and L-functions), Mercuri (adele ring), Manthe (Borel determinacy). [SNIPPET, zbMATH]
  - [INFERRED] AFM is young; time to decision not stated anywhere I could read.
- Journal of Automated Reasoning (Springer): scope is automated reasoning and mechanical
  verification of theorems [READ, Wikipedia]. Publishes Lean/Mathlib library papers (Baanen
  et al. 2022; Dupuis-Lewis-Macbeth 2024). [SNIPPET] Submission guidelines, fees and AI
  policy not obtained (login redirect). [INFERRED] Better fit for tooling/library papers
  than for new classification theorems.
- ITP 2027 (Glasgow, 2-7 Aug 2027) [READ, call for papers]:
  abstract 8 Feb 2027; full paper 15 Feb 2027; notification 26 Apr; camera-ready 25 May.
  Regular 16 pages excluding references, short 6 pages; LIPIcs style; HotCRP.
  Supplementary: anonymized formalization sources required as evidence of a working
  implementation. Double-blind. AI: substantive AI use must be disclosed in the main text
  (counts toward pages); AI in developing formalizations must be described in the
  methodology; substantial AI-generated text not allowed; violation may mean rejection
  without review; reviewers may not use AI. Limit: at most four ITP submissions per person.
  [INFERRED] The venue wants formalization-method content (design lessons), not only
  mathematics.
- CPP 2027 (Mexico City, 11-12 Jan 2027, with POPL) [READ]: abstract 3 Sep 2026, paper
  10 Sep 2026, notification 10 Nov 2026: closed. 12 pages, ACM SIGPLAN style, anonymous,
  supplementary archive at submission, AI must follow ACM policy, authors responsible.
  [INFERRED] CPP 2028 would have a September 2027 deadline; not announced.
- Archive of Formal Proofs (AFP): Isabelle only. Rules read: no sorry; must build in current
  Isabelle with PDF; ROOT file; cite sources; abstract; reviewed and maintained by the
  editors; updates monotone. [READ] Not applicable to Lean work. A Lean-to-Isabelle port is
  out of the question.
- Lean community venues:
  - Lean Together: free virtual meeting; 2026 edition 19-23 Jan 2026, open call for talks by
    online form, deadline 1 Dec 2025, talks recorded to the community YouTube channel. [READ]
    2027 page not found (404); [INFERRED] the call will again close in early December and
    anyone can submit.
  - Lean community blog: lists posts by project teams (Mathlib reviewer bootcamp, Sphere
    Packing, class field theory workshop). How to contribute a post was not on the page. A
    21 Nov 2026 post on a claimed Lean proof of the Riemann Hypothesis is listed (joint
    statement by Lean and Mathlib communities certifying statement and proof). [READ via fetch
    tool; striking, treat as one source only]. [INFERRED] Attention to claimed Lean results
    is currently very high, so scrutiny of ours will be too.
  - Reservoir: inclusion criteria (public GitHub repo not a fork or template copy, root
    lake-manifest.json, OSI-approved license recognized by GitHub, at least 2 stars). [READ]
    Noting the project's own spelling rule: choose a license such as Apache-2.0 or MIT.
  - Mathlib: contributions welcome via PRs; new theories should fit what a math department
    teaches; mid-2026 over 2600 open PRs, so a standalone repository depending on Mathlib is
    the recommended route for fast or outside-expertise work. AI policy for PRs: disclose
    tools in the PR description, label LLM-generated, author must understand and be able to
    defend everything without AI, no LLM-written Zulip or GitHub comments, low-quality
    LLM PRs may be closed, repeat violations can mean a ban. [READ]
  - Zulip thread "Standards for Lean proofs of unsolved problems": community worries about
    claims by outsiders, cranks and AI tools; discussion of comparator/SafeVerify,
    lean4checker, misformalization as the main non-adversarial risk; participants note that
    misstated definitions are the commonest failure. [READ]
  - "Did you prove it" checklist (community page) [READ]: proper Lean project, builds with
    lake build, main theorem in the build, #print axioms shows only propext,
    Classical.choice, Quot.sound, statement faithful (redefined notions can fake a famous
    statement), and for results not in Mathlib a Lean expert must confirm the statement.

### 2.3 arXiv and alternatives (question 3)

- Endorsement basics [READ, arXiv help]: required before first submission and for each new
  category; automatic only with institutional e-mail and claimed authorship; otherwise a
  personal endorsement from an established author. Endorser needs papers in the domain
  submitted 3 months to 5 years ago (number varies by area). At least one positive endorsement
  per domain; endorsement is not peer review, endorsers check topical fit, do not verify
  correctness, and keep the paper confidential. arXiv staff cannot endorse.
- Math change [READ]: since 10 Dec 2025 no auto-endorsement on institutional e-mail alone;
  needs academic e-mail AND a claimed, accepted math paper; no prior math co-authorship
  means personal endorsement regardless of e-mail. Extended to all sections 21 Jan 2026.
- How people without contacts get endorsed (arXiv's own advice) [READ]: look at recent arXiv
  papers close to your topic (especially ones you cite), use the "Which authors of this
  paper are endorsers?" link on abstract pages, e-mail a few endorsers individually; do not
  mass-mail and do not repeatedly ask the same person; register as author of your own
  papers. Forum threads (HN, Physics Forums, Hugging Face) show independent authors mostly
  ask cited authors or workshop contacts; one commenter says arXiv gives no credibility
  and that math journals accept direct uploads. [READ, anecdotal]
- Rate limit (1 Oct 2026): 2 submissions per calendar month per submitter, plus 3 active
  at once; rejected papers count; independent of seniority; arXiv calls it a stopgap. [READ,
  via Socket summary] The arXiv blog list confirms the post "Fair moderation, equitable
  access, and AI: arXiv's updated rate limit policy" dated 1 Oct 2026. [READ]
- AI text policy [READ]: authors must report significant text-to-text generative AI use;
  AI cannot be listed as an author; authors fully responsible; May 2026 sanction of a
  one-year ban for clear evidence of unchecked output (invented references, leftover prompt
  text), confirmed by moderator and section chair, with appeal; afterwards submissions must be
  accepted at a peer-reviewed venue first. The policy does not forbid LLM use.
- cs.LO: the endorsement page does not name it; [INFERRED] it falls under the computer
  science domain, requiring its own endorsement. A paper whose primary class is math.NT with
  cs.LO as cross-list needs endorsement only in math (cross-list is not a submission
  category in its own right) [INFERRED, check]. Banwait's Lean paper is math.NT with cs.LO
  cross-list. [READ]
- arXiv also stopped (Nov 2025) accepting unrefereed CS review and position papers. [READ,
  Wikipedia] Not relevant to a research paper.
- arXiv became an independent nonprofit on 1 Jul 2026. [READ, Wikipedia]
- arXiv moderation is for "professional members of the scientific community"; may decline
  papers lacking originality; no statement on independent researchers. [READ]
- Precedents on arXiv in 2026 (math.NT, Lean, AI) [READ abstracts]:
  - Kimura, class number at most 2000: key steps proved in Lean, two independent kernels,
    AI contributions "stated in the paper"; code and Lean on GitHub.
  - Fukui, APN lifts: Lean 4, blueprint, v2.0.0 on Zenodo and GitHub.
  - van Doorn-Monticone-Tang, multiplicative Sidon gaps: bound proved and verified by an AI
    prover (Aristotle), stated in abstract.
  - Banwait, Ramanujan-Nagell in Lean, math.NT + cs.LO.
  - Lau-Lee-Ono, formalized q-series (Rogers-Ramanujan), math.NT, 2026. [SNIPPET]
  So AI-assisted, Lean-checked math.NT papers by little-known authors are being accepted.
- Alternatives:
  - Zenodo (CERN): accepts research artifacts from all fields, any file type, public files
    need a license, DOI per version; out-of-scope content is removed and its DOI revoked.
    No peer review. [READ] Perception: one commenter calls most Zenodo posts low quality.
    [READ, anecdotal] But AFM accepts a Zenodo deposit as the pre-submission archive.
    [READ] Zenodo also mints versioned DOIs for GitHub releases [INFERRED from the Fukui
    record that uses Zenodo and GitHub together].
  - HAL (France): AFM explicitly lists it with arXiv and Zenodo as acceptable deposit.
    [READ] HAL's own deposit rules were not obtained (site blocked). Deposit may need
    affiliation or scientific-quality moderation [INFERRED, unverified].
  - OSF Preprints: hosts several preprint servers, one math-oriented, with a moderation
    policy; details not obtained. [READ, thin]
  - viXra: accepts without affiliation or quality threshold, created 2009 for authors
    rejected by arXiv; widely seen as hosting fringe work; a citation of a viXra paper is
    regarded as a negative signal. [READ, Wikipedia] [INFERRED] avoid.

### 2.4 Approaching an expert (question 4)

Sources found are informal; nothing authoritative specific to "check my Lean-verified
paper". [READ unless marked]

- Poonen (MIT) personal page: he reads mail from outsiders when he is the sole recipient,
  addressed by name; the writer says why him specifically; full sentences; full name; asks
  that the question be interesting and relevant to his expertise; he does not have time to
  check others' work unless it relates to his articles; suggests asking local professors,
  then Math StackExchange/MathOverflow, then asking local professors for referrals.
- Search snippet summary [SNIPPET]: unsolicited work is often ignored; framing as learning
  gets better answers; default assumption of readers is that a claimed proof of an
  important result is wrong, so credibility comes from first proving a few hard but
  uncontroversial things.
- Hacker News thread [READ, anecdotal]: take the best rigorous attempt to a mathematician at
  a local university; presentation, correct definitions, references to prior work; get
  introductions; poster at a conference.
- Physics Forums on endorsers [READ, anecdotal]: even if the person cannot endorse, they may
  suggest someone who can; an endorser must find the work interesting and worth being
  associated with.
- arXiv's own etiquette [READ]: contact a few endorsers individually; do not mass-mail.
- Tao's career-advice page "write a polite email to an expert" returned 404; MathOverflow
  and its meta could not be fetched (blocked); no mathematician blog post on "what makes me
  answer" other than Poonen's was obtained. Not found is weak evidence.
- [INFERRED] What a Lean-checked claim changes: the expert is asked to judge statements,
  not proofs. So the e-mail should contain: a one-sentence theorem, the exact Lean
  statement of the main theorem (a few lines, with definitions) and the standard-axioms
  output, the pointer to prior literature (the book or paper that asserts it without proof,
  page and line), a one-page note on what the checker does and does not cover, and a single
  narrow question ("is this statement the one you meant; is it known; would you endorse for
  math.NT"). Offer to send nothing else.

## 3. What is open (about venues)

- Whether JAR, Math. Comp., Experimental Mathematics, Ramanujan J., Monthly and Fibonacci
  Quarterly accept a Lean repository as a supplement, and their 2026 AI wording and
  fees: not obtained (sites blocked). Searched: publisher pages, T&F author services, AMS
  ethics page, MAA guidelines, Springer policies (login wall).
- Whether arXiv's new rate limit and endorsement rules have exceptions for authors with a
  peer-reviewed or archived Lean artifact: not found.
- AFM time to decision, number of unaffiliated authors published: not found.
- Whether "human-authored only" (AFM) and "no LLM-written text" (JIS) is enforced against
  a paper whose text the author wrote and rewrote with AI assistance, and how a disclosure
  like "proofs checked in Lean, code largely AI-generated" is judged: not found. [INFERRED]
  the policy text is strict enough that the author must write and own the paper text.

## 4. Leads for this project: recommended sequence

Premise: paper proving a statement that a standard reference asserts without proof (our
"b is a power of 2 iff a degree-1 BBP-type formula for pi exists", asserted in Bailey's
Compendium citing Borwein-Borwein-Galway 2004, who prove only the Machin-type case) plus a
public Lean repository. Ranked steps, with sources:

Step 1 (days). Make the Lean repository publishable. Public GitHub repo, not a fork; root
lake-manifest.json; OSI-approved license (MIT/Apache-2.0 recognized by GitHub); builds with
lake build; main theorems in the default build; #print axioms output captured in README;
a short "statement dictionary" that gives each informal claim, its Lean name and any
definitions that differ from Mathlib; run lean4checker/comparator-style checks.
Sources: Lean "did you prove it" page, Reservoir inclusion criteria, AFM instructions.
Add 2 stars (e.g. ask Lean community members) for Reservoir. Tag a release.

Step 2 (days). Archive and cite: Zenodo DOI for the tagged release; Software Heritage SWHID.
Sources: Zenodo policies, AFM instructions, Fukui precedent.

Step 3 (days to a week). Write the paper yourself, in your own words, as the author:
state the claim, quote exactly where the reference asserts it without proof, and say
what Borwein-Borwein-Galway do and do not prove. Include a disclosure paragraph on AI
(tools, version, tasks for text, proofs and code) in the style T&F, AFM, ITP and arXiv
ask for. Verify every reference by hand. [Sources: JIS, AFM, ITP, arXiv policies]. Do not
let any LLM write sentences of the paper; the strictest policies (JIS, AFM) forbid it.
Keep a hand-written account of every statement that a Lean proof does not cover.

Step 4 (1-3 weeks). Seek a courtesy check from 1-3 named experts: authors of the reference
(Bailey; Borwein-Galway lineage; Barsky/Perez-Marco; Adegoke on binary BBP), plus a Lean
person for the statement check (Zulip #mathlib or #general). Use the e-mail pattern in 2.4;
one person per message; no mass mailing. Ask also for arXiv endorsement in math.NT here.

Step 5 (days). Post to arXiv math.NT (cross-list cs.LO), after endorsement; one submission
per month limit matters, so submit only the final version. Candidates for an endorser:
the authors of cited recent math.NT arXiv papers with Lean (via the "which authors are
endorsers" link). If no endorsement arrives within about a month, deposit on Zenodo and
proceed to Step 6 anyway; do not use viXra.

Step 6 (weeks). Choose a journal by fit:
- AFM (best fit: artifact mandatory, free, open; deposit may be Zenodo): accepts only
  human-authored text; needs mathematical insight beyond the formalization; needs a
  general-audience introduction and an informal-vs-formal statement audit.
- JIS or Integers (classical home of BBP-type papers by non-academics; no fees; JIS
  median decision 197 days; JIS bans LLM text): suits the mathematical paper; cite the
  repository.
- Experimental Mathematics (code culture; T&F AI-use declaration; fees unknown).
- NNTDM (no fees; lower prestige; fast?) Not verified.
ITP 2027 (15 Feb 2027, 16 pages) only if the paper is rewritten as formalization-method
work (what was hard, how Baker's theorem was imported, design lessons); mathematics alone
will not suit it. Lean Together (call about December; a short talk, recorded) gives
visibility and informal expert feedback at no cost.

Step 7 (optional, weeks to months). Offer a small PR to Mathlib only for general lemmas; keep
the main development as a standalone repository, as the Mathlib guide advises.

What would make it noticed: a concrete corrected citation in a standard reference (the
Compendium statement), a repository that passes the community checklist without effort,
a one-page statement dictionary, and an endorsement or comment from a named expert.

## 5. Overlap or conflict with the project's results

None found about the results themselves; this thread did not search the mathematics. One
procedural point: AFM and JIS policy texts say the paper must be human-authored; the
project works with AI assistance, so the author needs to decide what can be honestly
declared and rewrite the paper text personally before submission.

Notes on page content addressed to me: none of the fetched pages contained instructions
directed at the assistant. One sidebar headline on Tao's site ("MathHelm: a place to discuss
AI-generated papers") was noted but not followed.

## 6. Sources (URLs)

- https://info.arxiv.org/help/endorsement.html
- https://blog.arxiv.org/arxiv/2025/12/10/updated-endorsement-policy-for-arxiv-mathematics
- https://techcrunch.com/2026/05/16/research-repository-arxiv-will-ban-authors-for-a-year-if-they-let-ai-do-all-the-work
- https://socket.dev/blog/arxiv-rate-limiting-slop
- https://blog.arxiv.org/category/arxiv-updates
- https://arxiv.org/mirrorhelp/endorsement.html
- https://info.arxiv.org/help/submit/index.html
- https://info.arxiv.org/help/moderation/index.html
- https://en.wikipedia.org/wiki/ArXiv
- https://cs.uwaterloo.ca/journals/JIS/
- http://math.colgate.edu/~integers/ (Integers home)
- https://nntdm.net/ and https://nntdm.net/about/pricing/
- https://afm.episciences.org/ (and /page/instructions-for-authors, /page/publishing-policies,
  /page/aims-and-scope)
- https://www.isa-afp.org/submission/ and https://www.isa-afp.org/help/
- https://itp-conference-2027.github.io/call-for/papers.html
- https://popl27.sigplan.org/home/CPP-2027
- https://reservoir.lean-lang.org/inclusion-criteria
- https://leanprover-community.github.io/blog/
- https://leanprover-community.github.io/lt2026/
- https://leanprover-community.github.io/did_you_prove_it.html
- https://leanprover-community.github.io/contribute/index.html
- https://leanprover-community.github.io/archive/stream/113488-general/topic/Standards.20for.20Lean.20proofs.20of.20unsolved.20problems.html
- https://authorservices.taylorandfrancis.com/editorial-policies/defining-authorship-research-paper/
- https://annals.math.princeton.edu/submission-guidelines
- http://about.zenodo.org/policies/
- https://en.wikipedia.org/wiki/ViXra
- https://en.wikipedia.org/wiki/Experimental_Mathematics_(journal)
- https://en.wikipedia.org/wiki/Journal_of_Integer_Sequences
- https://en.wikipedia.org/wiki/Journal_of_Automated_Reasoning
- https://math.mit.edu/~poonen/questions.html
- https://hn.nuxt.dev/item/46243256 , https://hn.nuxt.dev/item/45161827
- https://www.physicsforums.com/threads/how-can-i-find-an-endorser-for-my-prime-number-papers-on-arxiv.329971/
- arXiv abs pages 2610.21511 (Kimura), 2604.09808 (Banwait), 2610.21178 (Fukui),
  2605.02064 (van Doorn-Monticone-Tang)

## 7. Search log

WebSearch (6 calls, the maximum):
1. arXiv endorsement policy 2026 first-time submitters math.NT cs.LO AI policy
2. Experimental Mathematics / Ramanujan J. / Math. Comp. AI policy (no useful hits)
3. advice mathematician how to email an expert to check your proof
4. MathOverflow meta arXiv endorsement independent researcher
5. Annals of Formalized Mathematics author guidelines AI policy
6. Experimental Mathematics aims and scope; Monthly guidelines (Monthly part found nothing)

Endpoint queries (fetch tool) that were searches against search/API endpoints:
Crossref: 7. BBP digit extraction; 8. formalized proof Lean number theory;
9. journals "integers" (0 hits); 10. container AFM (429); 11. JIS + BBP (0);
12. Euler/Craig-Wood; 13. Adegoke general binary bases; 14. golden ratio (429);
15. Formalized q-series; 16. MathArXiv; 17. Lean arXiv endorsement (noise).
zbMATH: 18. BBP formula; 19. Lean formalization number theory; 20. "BBP so:Integers" (404);
21. digit extraction pi; 22. Lean 4 + AFM; 23. BBP log JIS; 24. Experimental Mathematics
Bailey Borwein BBP; 25. Baker + Lean (404); 26. JIS + Lean/Coq/Isabelle (404).
OEIS: 27. BBP formula; 28. BBP Lean formalization (empty).
GitHub: 29. lean4 number theory pi formula (0); 30. topic:lean4 topic:number-theory.
OpenAlex: 31. BBP digit extraction (429); 32. AFM (429).
arXiv API: 33. "Annals of Formalized Mathematics" (404 after 429); 34. Lean + math.NT (429).
Semantic Scholar: 35. BBP type formula (429).
Others: 36. Google search (blocked); 37. MathOverflow tag (blocked); 38. MO meta search
(blocked).
Counts: about 38 endpoint queries attempted; 21 returned usable content; 11 were refused
or empty (429, 403, 404). Pages read (fetch tool): about 45, including those listed in
sources.

TOTALS: WebSearch calls = 6. Endpoint queries = 38 attempted (about 21 productive).
