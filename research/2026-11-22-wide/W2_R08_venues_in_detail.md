# W2-R08: venues for a machine-checked number theory result, read at the source

Date of reading: 2026-11-22. Marks: [READ] = read on the source's own page; [SNIPPET] = only in a search
result or API record; [INFERRED] = my conclusion; [BLOCKED] = page refused automated access.
Quotations: none used. A few pages were fetched through a summarising fetch tool (it returns a model's
digest of the page, not raw text); where wording matters, check the page once more by hand.

## 1. Summary

1. Best fit by far: Annals of Formalized Mathematics (AFM, afm.episciences.org), a diamond open access
   overlay journal, no fees. [READ] It requires a formal artifact for every paper, open source and
   accessible to referees. [READ] The paper must FIRST be deposited in HAL, arXiv or Zenodo; so arXiv is
   NOT required, HAL or Zenodo suffice. [READ]
2. AFM's AI rule is the strictest point: "only human-authored manuscripts" and mandatory disclosure of AI
   use for manuscript, code, or both, with tools and tasks, plus funding including subsidized tool
   access. [READ] Its scope page says formalizing known results without new mathematical insight is out of
   scope. [READ] The project's results (classification, new theorems on BBP-type formulas) are new
   mathematics, so they fit the scope; the text must be written by the human author.
3. AFM publishes single authors with no affiliation shown in Crossref (Karayel, Mercuri, Manthe) but
   those people are in fact academics (affiliation fields are simply empty in the record) [SNIPPET,
   INFERRED]. AFM states manuscripts are judged regardless of institutional affiliation. [READ]
4. ITP 2027 (Glasgow, deadline 15 Feb 2027, 16 pages, double-blind, LIPIcs) allows GenAI for
   formalizations if disclosed in the methodology, but forbids substantial AI-generated text; it wants
   formalization papers to offer proof-assistant-specific design or reusable libraries, not artifact size
   alone. [READ] CPP 2027 (11-12 Jan 2027) is closed (deadline was 10 Sep 2026); CPP 2028 page not found.
5. Journal of Integer Sequences: free, no page limit, email submission to the editor-in-chief, LaTeX
   only; AI rule: text must be the author's own, LLM-written or LLM-translated text is prohibited,
   LLM-suggested proofs must be credited, undisclosed AI use means rejection; median 197 days to a final
   decision in 2025. [READ] Integers: free, email submission, wording must be the author's own,
   statement of AI use required at the end of the manuscript. [READ]
6. Journal of Formalized Reasoning (Bologna): the archive page shows the latest issue as Vol. 13 No. 1
   (2020) [READ]; it looks dormant [INFERRED]. Its pages carry no AI policy. [READ]
7. Springer journals (Journal of Automated Reasoning, Ramanujan Journal, Research in Number Theory),
   Taylor and Francis (Experimental Mathematics, American Mathematical Monthly) and AMS (Mathematics of
   Computation) refused automated access: [BLOCKED]. Only Springer Nature's generic AI position and
   a search snippet on the AMS AI policy were seen.
8. HAL accepts independent researchers: the API shows 8,515 records with an "Independent researcher"
   affiliation label, and one independent company-affiliated author deposits Lean 4 reports. [SNIPPET
   from HAL API] The HAL pages I could read did not state a rule on depositors without affiliation.
9. Zenodo: no mathematics-specific or preprint-specific policy found; but its content policy puts
   content "produced largely by generative AI without a verifiable connection to human research" out of
   scope. [READ] That is the likely reason behind the removal reported earlier [INFERRED].
10. arXiv: since 10 Dec 2025 (Math) and 21 Jan 2026 (all sections) a first-time author needs personal
    endorsement unless they have BOTH an institutional email AND a prior accepted paper in that domain.
    [READ] arXiv also reports a one-year suspension rule for unchecked LLM output. [READ]
11. The Leiden Declaration (June 2026, IMU-endorsed) asks for a "tool and computational resource
    disclosure" section, human responsibility, formal proofs where feasible, and does not ban AI. [READ]

## 2. What is known, venue by venue

### 2.1 Annals of Formalized Mathematics (AFM)
Pages read: home, aims-and-scope, instructions-for-authors, publishing-policies (all afm.episciences.org).
- Scope [READ]: papers must add mathematical value to formalization: new mathematical insight into a
  subject or into the use of proof assistants. Formalizing known results without new insight is out of
  scope, whether manual or AI-assisted. Many branches and proof-assistant ecosystems. Written for
  mathematicians with an accessible introduction. Formal proof artifacts expected with every paper;
  without them, "AI-derived mathematical insight" is not in scope. Authors must help "proof auditing":
  state the correspondence between informal and formal statements and flag possible mismatches.
  Encouraged (not required) qualities: novelty of mathematics and of the formalization, insight,
  generality, integration with libraries, reproducibility, complexity, foundational influence, code quality,
  usability and documentation of interfaces.
- Article types, length [READ]: no article types or length limits are stated on the pages read. No official
  style file; use any LaTeX class. In-text code should only complement the text. Not found = weak
  evidence (searched: aims, instructions, policies pages).
- Formal artifact [READ]: every submission must correspond to a formal artifact; at least the main
  results must link explicitly to specific code; the code must be open source and accessible to referees;
  the manuscript need not contain extracted files; Software Heritage persistent identifiers (SWHID) are
  invited upon acceptance. No DOI-archive (Zenodo release) requirement is stated; I found no "archived
  release" rule beyond the SWHID invitation.
- Preprint requirement [READ]: authors must first deposit the manuscript in HAL, arXiv or Zenodo (PDF not
  inside a zip). HAL authors use HAL's route to the publishing service; others make an Episciences
  account and use the submission page. Accepted papers are uploaded as final versions to the original
  archive and published on the AFM site. Authors may suggest a handling editor.
  Answer to the question asked: it is an overlay journal on arXiv, HAL and Zenodo alike; arXiv is not required.
- HAL route [READ, doc.hal.science]: HAL account, deposit type "Preprints, Working Papers", visibility
  immediate, CC-BY recommended, a human technical check, then automatic transfer to the chosen Episciences
  journal. One can also tick a transfer to arXiv.
- AI [READ]: only human-authored manuscripts accepted; authors disclose whether AI was used for the
  manuscript, the code, or both, with the tools and tasks; disclose all related funding including
  subsidized access to tools or software.
- Fees [READ]: none to publish or to read. CC-BY 4.0; authors sign a non-exclusive copyright transfer
  and may self-archive. One issue per year, papers appear on acceptance.
- Review [READ]: single-blind; authors may update versions on the open repository during review;
  review time not stated on the pages read.
- Founded 2024, supported by MathOA (Netherlands). [READ]
- Single-author examples [SNIPPET, Crossref]: Karayel (Derandomization with Pseudorandomness, 2025),
  Riou (derived categories, 2025; Paris-Saclay), Mercuri (local compactness of the adele ring, 2025), Manthe
  (Borel determinacy, 2026). Crossref lists no affiliation for three of them; this is a metadata
  gap, not evidence of unaffiliated authors [INFERRED]. I found no AFM paper confirmed as written by a
  truly independent author. Volume 1 has 5 articles, volume 2 has 3 [READ]; the journal is small.
  Several AFM papers are Lean/Mathlib number theory (Fermat's Last Theorem for regular primes; zeta and
  L-functions; adele ring; Bruhat-Tits tree) [SNIPPET], so number theory in Lean is on topic.
- How to submit [READ]: deposit on HAL/arXiv/Zenodo, then submit through Episciences (account, submission
  page); contact afm@episciences.org.

### 2.2 Journal of Automated Reasoning (Springer, EiC Jasmin Blanchette per a search snippet)
- [BLOCKED]: link.springer.com submission-guidelines and aims-and-scope redirect to an authentication
  host; www.springer.com redirects likewise. Nothing read from the journal.
- [SNIPPET] (search result): theory, implementation and applications of logical reasoning by computer;
  hybrid OA; editor-in-chief Blanchette. APC, article types, artifact rules: not found.
- Springer Nature general AI policy [READ, springernature.com editorial policies page]: AI may support
  but not replace scholarly judgement; human accountability cannot be delegated; disclosure builds trust.
  Detailed rules (LLM not an author, disclosure of AI-generated text) were on linked pages I could not reach.
  Common knowledge from before 2026 (Springer: LLMs not authors; AI-assisted copy editing need not be
  disclosed) is [INFERRED], not confirmed now.

### 2.3 Journal of Formalized Reasoning (Bologna, jfr.unibo.it)
- Scope [READ]: significant automated or semi-automated formalization efforts in any area, emphasis on
  proof techniques and methodologies; formal scripts preferably included.
- Length [not found]. Format [READ]: single PDF, or one tar file with executable scripts; LaTeX
  encouraged (jfrarticle.cls); LaTeX sources after acceptance; the work must not be under review elsewhere.
- No artifact-archive/DOI rule stated. Reproducibility: raw data must be provided and kept available. [READ]
- AI policy: none on the pages read (about, editorial policies, submissions). [READ]
- Fees [READ]: none. CC BY 3.0, authors keep copyright; preprints and postprints allowed.
- Review time [READ]: authors told within 15 days; two anonymous reviewers, about 2 months; decision
  within 15 days; 1 month for minor changes.
- Activity [READ]: the issue archive's most recent issue is Vol. 13 No. 1 (2020). [INFERRED] dormant;
  Crossref search by journal title returned nothing. Do not rely on it.
- Submit: online submission system on the journal site (OJS) [INFERRED from layout].

### 2.4 Formalized Mathematics (Mizar; fm.mizar.org, Sciendo/Reference Global)
- Scope [READ at fm.mizar.org and reference-global.com/journal/FORMA]: original, mechanically checked
  formalized mathematics, all areas, plus related automated reasoning. All papers are checked by the Mizar
  System. So it is Mizar-only in practice (a Lean result would have to be re-done in Mizar) [INFERRED];
  no page I read states an explicit prohibition of other systems.
- Open access CC BY-SA 4.0; uses iThenticate; EiC Cezary Kaliszyk; submission contact mml@mizar.uwb.edu.pl.
  Fees, AI policy, length: not found (instructions PDF returned 404).
- Single-author examples [SNIPPET, Crossref]: Karol Pak, Artur Kornilowicz, Mario Carneiro (prime
  reciprocals, 2022), Taneli Huuskonen (Tampere, Finland, 2025, no institution shown), Sebastian Koch.
  So single authors with little or no affiliation do appear.
- Verdict [INFERRED]: not a fit for Lean-checked work.

### 2.5 ITP 2027 (read itp-conference-2027.github.io/call-for/papers.html) [READ]
- Place and date: Glasgow; the header says 2-7 Aug 2027 (conference proper: 3-6 Aug 2027 per the CFP body;
  confirm). Abstract 8 Feb 2027, paper 15 Feb 2027, notification 26 Apr 2027, camera-ready 25 May 2027
  (all AoE). 18th ITP; PC co-chairs Traytel and Weirich.
- Length: regular 16 pages excluding references, no appendix; short papers 6 pages. LaTeX, lipics-v2021,
  PDF through HotCRP, double-blind (anonymous). At most four submissions per author.
- Artifact: anonymised supplementary material giving verifiable evidence of an implementation, such as the
  formalization sources. No separate artifact-evaluation track, no DOI rule stated. Proofs must be
  complete, possibly relying on explicitly stated assumptions.
- Value criteria: formalization papers need proof-assistant-specific design, reusable libraries or tooling,
  or corrections of published arguments; size alone is not a contribution.
- AI policy for authors: all use critically checked by humans; any substantive use disclosed in the main
  text (counts toward page limit); violations may be rejected without review; GenAI may be used for
  formalizations and tooling if explicitly disclosed in the methodology, including role and costs;
  substantial AI-generated text is not permitted; copy-editing allowed with review. Reviewers may not use GenAI.
- Proceedings: LIPIcs, gold OA, CC-BY 4.0. Two review rounds, two first-round reviewers.
- Fit [INFERRED]: a pure number-theory classification with a big Lean development is a weak ITP fit
  (the focus is on proof assistant technique). Only a paper about the formalization method itself
  (for example how Baker's theorem was imported or how the finite prime test was verified) would suit.
- Cost: not stated; LIPIcs gold OA is normally covered by the conference [INFERRED, not confirmed].

### 2.6 CPP 2027 / CPP 2028 [READ at popl27.sigplan.org/home/CPP-2027]
- CPP 2027: 11-12 Jan 2027, Mexico City, co-located with POPL 2027. Deadlines already passed: abstract
  3 Sep 2026, paper 10 Sep 2026, notification 10 Nov 2026, camera-ready 25 Nov 2026. No extensions.
- 12 pages excluding bibliography and clear appendices; acmart sigplan, 10pt; HotCRP; lightweight
  double-blind. No formal artifact evaluation; supplementary material (proof scripts) encouraged as an
  archive uploaded at submission, not a URL.
- AI: follows the ACM policy; tools allowed if they do not plagiarize or misrepresent, the work is not
  primarily generated by the tool, authors take responsibility; PC may desk-reject violations.
- CPP 2028: no page found (conf.researchr.org/home/CPP-2028 returned 404). Expect a similar mid-September
  2027 deadline [INFERRED from the pattern, unverified].

### 2.7 Journal of Integer Sequences (JIS; cs.uwaterloo.ca/journals/JIS) [READ]
- Scope: integer sequences and closely related topics; cite OEIS A-numbers, submit new sequences to OEIS
  first. Rejects claimed proofs of famous conjectures (Goldbach, RH, Collatz).
- Submission: by email to the editor-in-chief (Jeffrey Shallit), subject line "Submission to the Journal of
  Integer Sequences"; LaTeX only (12pt), no PDF/DOC submission; English; no cover letter; one paper at a
  time. Authors suggest 2-3 referees.
- Length: no page limit; supplementary code and tables welcome. Formal artifact: no rule; supplementary
  files are allowed [READ].
- AI [READ]: the text must be the author's own; using an LLM to write or translate it is prohibited; any
  AI use must be explicitly and in detail stated in the paper, undisclosed use leads to rejection;
  LLM-suggested proofs or techniques must be credited in the text; editors may use software to detect
  machine-written text.
- Fees: none, no APC; payment invoices are scams. Copyright stays with authors; arXiv postings allowed.
- Review time: median 197 days submission to final decision for Volume 28 (2025); 4 days acceptance to
  publication. Volume 28 had 64 articles; volume 29 (2026) had 10 so far.
- Examples of unaffiliated authors: not checked in detail (a Crossref query returned nothing relevant).
- Fit [INFERRED]: the BBP-type series with rational weights and digit extraction connect to sequences
  (OEIS A104885 finding); strongest classical fit of the non-formal journals.

### 2.8 Integers (math.colgate.edu/~integers) [READ]
- Scope: combinatorial number theory, original research in combinatorics and number theory; no fees.
- Submit: email PDF to the journal Gmail address given on submit.html with MSC codes, keywords, and a
  confirmation of AI-policy compliance; LaTeX source after acceptance in the Integers style.
- AI: tools may help but never replace critical thinking; authors answer for all statements and
  references; narrative and wording must be the author's own (spell/grammar checkers exempt); any other
  AI use is declared in a statement at the end of the manuscript. Editors may use AI to assess papers.
- Review: acknowledgment within days; blind refereeing (referees know authors); criteria novelty,
  correctness, interest, writing. Review time, length and artifact rules: not stated.
- Fit [INFERRED]: scope is combinatorial; BBP classification is more analytic number theory, so only partial.

### 2.9 Experimental Mathematics, Mathematics of Computation, American Mathematical Monthly,
### Ramanujan Journal, Research in Number Theory
- [BLOCKED] for all author guidelines: tandfonline.com (403), ams.org (403), link.springer.com
  (authentication redirect), researchinnumbertheory.springeropen.com (404 on the paths tried), maa.org (403).
  I cannot report scope, article types, length, artifact rules, fees or review times from the sources.
- [SNIPPET] only: AMS has a general "Use of Artificial Intelligence" policy; authors state how and which
  tool was used and stay fully responsible. Mathematics of Computation is peer reviewed, single-anonymous
  (reviewers know the authors, authors do not know reviewers). Nothing seen about the Monthly's AI rules.
- Springer Nature general AI position: see 2.2.
- [INFERRED] RINT is a SpringerOpen-family journal, which usually charges an APC; I could not confirm
  its current APC or whether it is still APC-based. Do not quote this.
- What to do: read these pages in a normal browser, or ask for them to be pasted. These are the gaps.

## 3. Cross-cutting services

### 3.1 HAL (depositors without affiliation)
- doc.hal.science home [READ]: states HAL is for researchers affiliated with academic institutions
  (French text), but this is a one-line description, not a deposit rule. The FAQ [READ] lists moderation
  checks: file readable, affiliation correct, publisher authorization; refused types: theses/memoires only,
  table of contents only, bibliography only, CV, watch bulletins; the page does not address independent
  researchers and says to contact support.
- Practice [SNIPPET, HAL API api.archives-ouvertes.fr]: query for the phrase "independent researcher" found
  8,515 records; the affiliation label appears as "Independent researcher" or the bilingual label
  "Chercheur independant = Independent researcher". A "Catskills Research Company" author has deposited
  Lean 4 formalization reports (June to September 2026), single author, document type REPORT.
  So independent and small-company authors do deposit and get online. HAL also hosts the AFM overlay route.
- Not found: any written rule that forbids unaffiliated depositors. Pages tried: doc.hal.science
  deposit-rules (404), guide-utilisateur pages (404 for several); HAL search pages are behind a bot filter.
- Practical [INFERRED]: use the affiliation "Independent researcher"; HAL then requires a human technical
  check; for the Episciences route choose document type "Preprints, Working Papers".

### 3.2 Zenodo
- Policies page [READ]: all fields and all research artifact types; removal of out-of-scope content with
  revocation of the Zenodo DOI; no mention of preprints, mathematics or AI on that page.
- Support pages [READ] (support.zenodo.org help 2/141 and 13/227): Zenodo is a repository, not a quality
  reviewer; content produced largely by generative AI with no verifiable connection to human research is
  out of scope; AI may be used as a tool but not as the source of the research; AI cannot be an author;
  substantive AI use should be described in the record (tools, purpose, affected parts), non-disclosure
  alone is not grounds for removal; reviewed AI-written code is acceptable; unacceptable: raw LLM output,
  speculative claims presented as findings, bulk AI submissions; warning signs: core ideas originating
  from AI, fabricated references, internal contradictions, unchecked claims. Disputed claims: may be
  labelled or removed under a separate procedure; Zenodo does not judge correctness.
- No mathematics-specific preprint policy was found. The earlier report's removal is consistent with the
  AI clause [INFERRED]; I did not find that specific incident.
- Fit: a Zenodo record with a DOI for the Lean repository and the paper is acceptable if the
  record describes the AI role and the human research basis [INFERRED].

### 3.3 arXiv
- Endorsement [READ: info.arxiv.org/help/endorsement and the blog posts of 10 Dec 2025 and 21 Jan 2026]:
  endorsement is required before a first submission to a new category. Since 10 Dec 2025 (Math) and
  21 Jan 2026 (all sections), automatic endorsement needs BOTH an academic or research institutional email
  AND previous authorship of a paper accepted in that endorsement domain. Otherwise one needs personal
  endorsement from an established author in the same domain; arXiv staff cannot endorse or waive. Endorsers
  must have authored enough papers in the domain submitted between 3 months and 5 years ago. Existing
  authors keep status. Do not mass-mail potential endorsers. math-ph follows the physics rules.
  math/cs.LO specifics beyond this: not found (page math endorsement 404); cs is a domain of its own so
  separate endorsement for cs.LO [INFERRED].
- English: a full English version is required from 11 Feb 2026 [SNIPPET: CASRAI summary, not arXiv].
- AI [READ: info.arxiv.org/help/moderation]: significant use of text-to-text generative AI must be
  reported consistent with subject norms; authors are responsible; AI tools may not be listed as authors.
  A CERN Courier article of 23 Jul 2026 [READ] reports a "one strike" rule: incontrovertible evidence of
  unchecked LLM output (fake references, leftover meta-comments) risks up to one year suspension, with
  possible peer-review-first reinstatement; it describes this as a clarification of existing policy.
- CS review articles and position papers need prior peer review since Oct 2025 [READ blog]; research
  papers are not affected.
- Implication [INFERRED]: an unaffiliated first-time author needs a personal endorser in math.NT (or cs.LO);
  using HAL or Zenodo instead avoids this for AFM.

## 4. The Leiden Declaration and similar statements [READ leidendeclaration.ai and the Leiden news page]
- Published June 2026 by 16 researchers from 15 universities, after a Sept 2025 NIAS-Lorentz workshop; IMU
  endorsed; over 2,000 signatories within a week per a VU Amsterdam report [SNIPPET].
- Acceptable practice as described: not a ban on AI; human authors alone carry responsibility for
  correctness, adequacy and citations; credit goes to humans, not systems; disclose tools including LLMs,
  ML systems, proof assistants and other software in a "tool and computational resource disclosure"
  section; make a proactive effort to credit enabling sources, or say explicitly when attribution is not
  possible; supply formal proofs where feasible and appropriate; for automated results insist on human
  descriptions of central arguments, formal verification when appropriate, cross-checking and external
  pre-submission review; results stay in peer-reviewed venues, with press releases and blogs only as
  supplements; support less resource-intensive tools for individual researchers.
- Fit with this project [INFERRED]: Lean verification plus honest disclosure of AI roles (who proved,
  who wrote, which prompts) is exactly the practice described; the one thing journals will still
  demand is a human-written text and a human who can answer for the statements (proof auditing).
- Similar statements: I did not find, within budget, other 2025-2026 statements to read. Wadham College
  (Oxford) news item only points to the declaration [READ].
- Prompt-injection note: the OpenAlex API response for one query contained a message addressed to AI agents
  (asking them to request an API key by emailing a link); ignored.

## 5. Ranking of the venues for this project [INFERRED]
1. AFM: formal artifact required and centered, no fees, no institution test; needs a human-written paper
   and AI disclosure; preprint on HAL or Zenodo first. Risk: single-blind and small editorial board;
   review time unknown.
2. JIS: free, no length limit, code welcome, fits sequence/series theme; strict AI rules (human-written
   text, credit LLM proofs); slow (about 200 days).
3. Integers: free; scope is more combinatorial.
4. Research in Number Theory / Ramanujan Journal / Experimental Mathematics / Mathematics of Computation:
   plausible mathematically, but rules unread; a formal artifact is a bonus, not required [INFERRED].
5. ITP (15 Feb 2027): only with a methods angle on the formalization; CPP 2027 is past.
6. Not recommended: Formalized Mathematics (Mizar), Journal of Formalized Reasoning (dormant).

## 6. What is open or unread
- Springer, T&F, AMS and MAA author guidelines (blocked); JAR article types; fees for RINT; Monthly policy.
- Whether AFM has an explicit length limit or expects an archived release (not stated on pages read).
- Any AFM paper by a verified unaffiliated author (none confirmed).
- HAL's written position on unaffiliated depositors (not found; practice shows it works).
- CPP 2028 call; other 2025-2026 AI-in-mathematics statements.

## 7. Sources
- https://afm.episciences.org/ , /page/aims-and-scope , /page/instructions-for-authors , /page/publishing-policies
- https://doc.hal.science/en/deposit/submitting-preprint-to-publishing-service/ , https://doc.hal.science/faq/
- https://api.archives-ouvertes.fr/search/ (queries above)
- https://jfr.unibo.it/about , /about/submissions , /about/editorialPolicies , /issue/archive
- https://fm.mizar.org/ , https://reference-global.com/journal/FORMA
- https://itp-conference-2027.github.io/ , /call-for/papers.html
- https://popl27.sigplan.org/home/CPP-2027
- https://cs.uwaterloo.ca/journals/JIS/ ; http://math.colgate.edu/~integers/ and /submit.html
- https://www.springernature.com/gp/policies/editorial-policies
- https://info.arxiv.org/help/endorsement.html , https://info.arxiv.org/help/moderation/index.html ,
  https://info.arxiv.org/help/submit/index.html , blog.arxiv.org posts of 2025-12-10 and 2026-01-21 and 2025-10-31
- https://cerncourier.com/a/arxivs-one-strike-rule-on-ai/ ; https://casrai.org/news/arxiv-2026-endorsement-english-ai-policy-changes
- https://about.zenodo.org/policies/ , /terms , /principles/ ; https://support.zenodo.org/help/en-gb/2/141 and /13/227
- https://leidendeclaration.ai/ ; https://www.universiteitleiden.nl/en/news/2026/06/leiden-declaration-warns-ai-is-challenging-the-core-values-of-mathematics
- https://ams.org/publications/journals/policies/UseofArtificialIntelligence (title only, 403)
- Blocked: link.springer.com/journal/10817, /40993; tandfonline.com; ams.org journals; maa.org; researchinnumbertheory.springeropen.com.

## 8. Search log
WebSearch (4 of 6 allowed used... see totals):
W1 ITP 2027 Glasgow call for papers AI policy; W2 Leiden Declaration AI mathematics 2026;
W3 arXiv math endorsement policy change December 2025; W4 Zenodo removed preprint out of scope mathematics;
W5 JAR submission guidelines / RINT APC; W6 Mathematics of Computation AMS AI policy / Monthly.
Endpoint and page queries via the fetch tool (numbered, grouped):
1-8 AFM pages (about 404, home, instructions, policies, aims, volumes browse; zbMATH serial query 404).
9-14 Springer JAR (submission-guidelines, aims-and-scope, 3 redirects), Springer Nature policies, AI page 404s.
15-22 arXiv: endorsement (3 paths), policies index, moderation, submit, blog posts x3.
23-29 HAL docs: deposit-rules 404, deposit, submitting preprint, home, FAQ, auteurs-et-affiliations 404,
 compte-et-profil 404, verification 404, guide deposer 404, search page (bot block).
30-36 Zenodo: policies, terms, principles, help 404s, support 2/141, support 13/227.
37-42 ITP: itp-conference.github.io, itp-conference-2027 home, cfp 404 x2, call-for/papers.html.
43-45 CPP: researchr redirect, popl27 page, CPP-2028 404.
46-50 JFR: submissions, about, editorialPolicies, archive, Crossref journal lookup (empty).
51-54 Mizar: fm.mizar.org, instructions 404, about 404, reference-global.
55-58 JIS: emis redirect, uwaterloo page; Integers home and submit.html.
59-64 blocked: tandfonline x3, ams x3, springeropen x3 404, maa 403, semantic scholar 403.
65-72 Crossref/OpenAlex: AFM works (container title, ISSN journals, prefix 10.46298), OpenAlex source search
 (429), journals query JFR (empty), JIS/Integers/RINT/Ramanujan/JAR Crossref filters (429/empty).
73-77 HAL API: Lean formalization, Ericson author query, independent researcher phrase, structName tests,
 arXiv API math.NT Lean (429).
78-80 Leiden: leidendeclaration.ai, Leiden news page, Wadham.
Totals: WebSearch calls = 6; endpoint/page queries via the fetch tool = about 100 (including roughly 35
that returned 403/404/429 and are listed above as blocked or failed).
