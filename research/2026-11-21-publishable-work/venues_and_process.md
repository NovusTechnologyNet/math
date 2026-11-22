# Venues and process: how an independent researcher can publish a number theory paper on pi formulas (and a companion digit-extraction software paper) in 2026-2027

Notes compiled 21 November 2026. Policy pages are dated where the page itself shows a date. Several official pages could not be read directly (Taylor and Francis, ScienceDirect, pubs.ams.org, dl.acm.org, zbMATH, World Scientific all returned a bot check or HTTP 403); where that happened the finding is marked "via search summary" or "third party" and should be re-checked on the official page before relying on it. The shared web-search budget ran out after 41 searches, so later gaps were filled only by direct reads of known official URLs.

Paper (1) = classification of binary Machin-type and degree-1 BBP-type formulas for pi (closing a case left open by Borwein, Borwein and Galway 2004). Paper (2) = digit-extraction algorithm and GPU program with benchmarks against y-cruncher.

---

## Key Question 1: arXiv in 2025-2026 (endorsement, policy changes, AI rules) and the alternatives if endorsement is hard

### Takeaway
Since 10 December 2025 (mathematics) and 21 January 2026 (all of arXiv), an unaffiliated first-time author can only get onto arXiv through a personal endorsement from an established arXiv author in the same endorsement domain; arXiv staff will not endorse anyone. arXiv also tightened AI-related enforcement in 2026 (a reported one-year ban for unchecked LLM output, and a two-papers-per-month cap from 1 October 2026), so a clean, human-checked manuscript and one well-chosen endorser request matter more than before; Zenodo is the credible fallback for a timestamped DOI, while viXra carries a reputational cost.

### Cited Findings

**Endorsement rules**
- As of 10 December 2025 the arXiv Mathematics section stopped accepting an institutional email address as the sole qualifier for automatic endorsement. Automatic endorsement in all math categories now needs both an academic/research institution email and "previous authorship on an existing paper which has been accepted to the arXiv Mathematics section". Authors with no co-authored paper in arXiv Mathematics must get a personal endorsement "regardless of email affiliation"; arXiv staff cannot personally endorse. The stated reason is "the flood of low-quality, non-scientific submissions to the arXiv Math section". — [arXiv blog, 10 Dec 2025](https://blog.arxiv.org/arxiv/2025/12/10/updated-endorsement-policy-for-arxiv-mathematics)
- On 21 January 2026 the same rule was extended to every arXiv section: new submitters need an institutional email plus previous authorship on an accepted arXiv paper in the endorsement domain, or else a personal endorsement from an established arXiv author in that domain. Endorsement domains are high-level subject areas (physics is the exception). Endorsement can be revoked for policy violations. — [arXiv blog, 21 Jan 2026](https://blog.arxiv.org/2026/01/21/attention-authors-updated-endorsement-policy/)
- Mechanics of a personal endorsement (arXiv help page): start a new submission and pick the category; arXiv emails an endorsement request containing a link and a six-character code; find related arXiv papers (especially recent ones your paper cites), open the abstract page and use "Which authors of this paper are endorsers?"; send the eligible endorser the request email, optionally with an ORCID/scholarly profile or the draft. At least one positive endorsement is needed per category. — [arXiv help: endorsement](https://info.arxiv.org/help/endorsement.html)
- Who can endorse: someone who has authored a certain number of papers in the endorsement domain (the page does not give the number), counting only papers submitted between three months and five years ago, registered as author of those papers, and holding an active endorsement themselves. — [arXiv help: endorsement](https://info.arxiv.org/help/endorsement.html)
- What endorsers are asked to check: endorsement "is not peer review"; the endorser should know the person or have seen the paper; they need not verify correctness but should confirm the work is appropriate for the subject area; they should not endorse authors who lack basic knowledge of the field or whose work is unconnected to current research. The paper sent for endorsement is confidential. — [arXiv help: endorsement](https://info.arxiv.org/help/endorsement.html)
- Etiquette stated by arXiv: "it is inappropriate to email large numbers of potential endorsers at once", and repeatedly emailing the same endorser is also inappropriate. The page suggests choosing someone you know who works in the subject area. — [arXiv help: endorsement](https://info.arxiv.org/help/endorsement.html)

**Other 2025-2026 arXiv changes**
- 31 October 2025: arXiv CS now requires review/survey articles and position papers to have been accepted at a peer-reviewed journal or conference (with journal reference and DOI) before posting; workshop review does not count. Original research papers are not affected. The reason given is the "unmanageable influx of review articles and position papers to arXiv CS"; other categories may adopt similar practices. — [arXiv blog, 31 Oct 2025](https://blog.arxiv.org/2025/10/31/attention-authors-updated-practice-for-review-articles-and-position-papers-in-arxiv-cs-category/)
- arXiv's AI policy for authors (in force since 31 January 2023): authors must report "any significant use of sophisticated tools", which includes text-to-text generative AI; each author takes "full responsibility for all its contents" by signing; "generative AI language tools should not be listed as an author". — [arXiv help: moderation](https://info.arxiv.org/help/moderation/index.html); [arXiv blog, 31 Jan 2023](https://blog.arxiv.org/2023/01/31/arxiv-announces-new-policy-on-chatgpt-and-similar-tools)
- May 2026 "one-strike" enforcement, as reported by the press (announced by CS section chair Thomas Dietterich on X; I did not find the text on arXiv's own site): a submission with incontrovertible evidence that the authors did not check LLM output (hallucinated references, leftover chatbot meta-comments) leads to a one-year ban, followed by a requirement that later submissions first be accepted at a peer-reviewed venue. Moderators flag and section chairs confirm; authors can appeal. AI use itself is not banned. — [TechCrunch, 16 May 2026](https://techcrunch.com/2026/05/16/research-repository-arxiv-will-ban-authors-for-a-year-if-they-let-ai-do-all-the-work); [CERN Courier, 23 Jul 2026](https://cerncourier.com/a/arxivs-one-strike-rule-on-ai/); [Times Higher Education](https://timeshighereducation.com/news/ban-authors-submitting-ai-content-welcome-unenforceable) (all read via search summary only)
- 1 October 2026 rate limit: "arXiv now limits submitters to up to two submissions per calendar month" with "a limit of three total active submissions at any given time", for all submitters and categories; rejected submissions count. arXiv received 40,363 submissions in September 2026 versus 20,569 in September 2024 and links the growth to AI tools. — [arXiv blog, 1 Oct 2026](https://blog.arxiv.org/2026/10/01/updated-rate-limit-policy/)
- arXiv moderators may decline work for poor scholarly form (incomplete sections or references), lack of originality or significance, or because it "needs significant revision", and may reclassify to a different category. — [arXiv help: moderation](https://info.arxiv.org/help/moderation/index.html)
- Since 11 February 2026 every submission needs a full English version; arXiv became an independent nonprofit (arXiv, Inc.) on 1 July 2026. — [CASRAI summary citing arXiv blog posts](https://casrai.org/news/arxiv-2026-endorsement-english-ai-policy-changes) (secondary source)

**Categories relevant to the two papers**
- math.NT: "Prime numbers, diophantine equations, analytic number theory, algebraic number theory, arithmetic geometry, Galois theory". cs.MS (Mathematical Software): "Roughly includes material in ACM Subject Class G.4." cs.DS covers data structures and analysis of algorithms; cs.SC is symbolic computation; cs.DC covers parallel and distributed computation; math.GM is "Mathematical material of general interest, topics not covered elsewhere"; math.HO includes recreational mathematics. — [arXiv category taxonomy](https://arxiv.org/category_taxonomy)
- A current example of a Machin-formula paper on math.NT with no affiliation shown: "Constrained PSLQ Search for Machin-like Identities Achieving Record-Low Lehmer Measures" by Nick Craig-Wood, submitted 8 August 2025, revised 16 September 2026, primary math.NT, 26 pages, CC BY-NC-ND. — [arXiv:2508.08307](https://arxiv.org/abs/2508.08307)

**Journals that assume or require arXiv**
- Indagationes Mathematicae states that only papers uploaded to arXiv are considered. — [Elsevier journal page](https://shop.elsevier.com/journals/indagationes-mathematicae/0019-3577)
- AMS journals allow authors to post prepublication versions (up to the accepted manuscript) on arXiv with no embargo. — [AMS open access page](https://www.ams.org/publications/journals/open-access/open-access)
- ACM: posting a preprint to arXiv "is not considered a prior or current publication venue". JOSS: "Submission to a preprint server is not considered a previous publication." — [ACM Policy on Authorship, updated 14 May 2026](https://www.acm.org/publications/policies/new-acm-policy-on-authorship); [JOSS submission docs](https://joss.readthedocs.io/en/latest/submitting.html)

**Alternatives**
- Zenodo (CERN): "Anyone may register as user of Zenodo"; scope is "All fields of research. All types of research artifacts"; any stage of the research lifecycle is accepted; Zenodo issues DOIs; a license must be specified for public files; withdrawal is exceptional and leaves a tombstone page with the DOI retained; items are kept for the lifetime of the repository. The policy page says nothing about affiliation. — [Zenodo General Policies v1.0](https://about.zenodo.org/policies/)
- viXra describes itself as an open alternative to arXiv with no endorsement requirement, "open to anybody for both reading and submitting articles", rejecting only extreme abuse; it openly says the archive will contain work many scientists consider wrong but argues authors should be able to record ideas and priority claims. — [viXra: why](https://vixra.org/why)
- viXra's reputation: the site "has a reputation among physicists for hosting material of no interest", and Gerard 't Hooft has written that a paper appearing on viXra is usually a sign that it is unlikely to contain acceptable results. — [Wikipedia: viXra](https://en.wikipedia.org/wiki/ViXra)
- HAL (French national archive): open to "researchers from academic institutions in France and abroad"; "At least one affiliation is mandatory in the deposit"; deposits with a file are checked manually before going online, which can take a few days. — [CCSD: HAL publishing workflow](https://static.ccsd.cnrs.fr/en/publishing-workflow/)
- GitHub alone is weak as an archive: a release is a snapshot that can be deleted or changed; Zenodo's GitHub integration archives each release and issues a version DOI plus a concept DOI for all versions. — [GitHub docs: referencing and citing content](https://docs.github.com/en/repositories/archiving-a-github-repository/referencing-and-citing-content); [Zenodo help: archive a GitHub release](https://help.zenodo.org/docs/github/archive-software/github-upload)

### Inferences
- For an unaffiliated author the only route into math.NT is now a personal endorsement. The most natural endorsers are active arXiv authors of the papers that paper (1) cites (Machin/BBP literature). Sending one polite, specific request with the PDF attached, to one person at a time, matches arXiv's own stated etiquette.
- Because endorsement domains are high-level (math is one domain, cs another), an endorsement obtained for math.NT probably does not cover a cs.MS or cs.DS primary listing for paper (2); the simplest path is to make math.NT primary for both and cross-list paper (2) to cs.MS. This is an inference from the "endorsement domain" wording, not something an arXiv page states for this case.
- The 2026 enforcement climate means any AI-assisted manuscript must have every reference and every claim checked by hand before submission, and the AI use should be disclosed in the paper: a single hallucinated reference is reported to be enough for a one-year ban.
- Indagationes Mathematicae (which published the closest 2023 paper) is effectively closed to an author who cannot get onto arXiv.
- Recommended order of operations if endorsement is slow: deposit the PDF on Zenodo first (DOI and timestamp within minutes, no affiliation needed), keep seeking one endorser, and post to arXiv when endorsed. Avoid viXra: the timestamp it gives is no better than Zenodo's and the association can count against the paper.

### Gaps
- The exact number of papers an endorser needs in the math domain is not stated on the pages I could read (the dedicated math endorsement help URL returned 404).
- I found no reliable source on ResearchGate or OSF Preprints policies for unaffiliated mathematicians; nothing is asserted about them here.
- The "one-year ban" policy was read only through press summaries; arXiv's own wording was not located.
- Whether Zenodo-only preprints are treated as prior publication by any of the target journals was not checked journal by journal.

---

## Key Question 2: Journals that fit paper (1): scope, length, speed, fees, track record on Machin/BBP papers, AI policy

### Takeaway
The subject has a clear publication trail: BBP in Mathematics of Computation (1997), Borwein-Borwein-Galway in the Canadian Journal of Mathematics (2004), Gasull-Luca-Varona in Indagationes Mathematicae (2023), plus BBP/Machin papers in Experimental Mathematics, the Ramanujan Journal, Integers, the Journal of Integer Sequences, the Monthly, the Mathematical Gazette and NNTDM. None of the subscription or diamond journals charge the author; only optional open access costs money (about USD 3,100-3,800 at the Springer journals). AI rules differ sharply: the Journal of Integer Sequences forbids LLM-written text, Integers requires author-written wording plus a declaration, and society and commercial publishers require disclosure.

### Cited Findings

**Fit ranking (my ordering; the evidence for each row follows below)**

| Rank | Journal | Why it fits | Main obstacle |
|---|---|---|---|
| 1 | Mathematics of Computation (AMS) | Home of the original BBP paper; scope names computational number theory; no author fee | Demanding; third-party estimate of about 7 months review; max 3 submissions per 12 months |
| 2 | Canadian Journal of Mathematics / Canadian Mathematical Bulletin | The 2004 paper being completed appeared in CJM | CJM wants 25-40 pages and is a selective general journal; CMB caps at 24 pages |
| 3 | Experimental Mathematics (T and F) or Journal of Experimental Mathematics (AMR, diamond) | Proof plus computer verification plus search is their stated model | Must have a real experimental component; JXM is young and its indexing is unverified |
| 4 | Indagationes Mathematicae | Published the 2023 two-term Machin classification | Requires the paper to be on arXiv |
| 5 | Journal of Number Theory, Research in Number Theory, Ramanujan Journal, Int. J. Number Theory | Specialist number theory journals; JNT explicitly welcomes computational number theory; Ramanujan J. published a 2020 BBP paper | Topic may be judged too elementary or too "pi-recreational" at the desk; Springer median first decisions of 3-12 days suggest fast desk screening |
| 6 | Integers; Journal of Integer Sequences | Free, reputable, have published BBP-type and Machin-like papers | Scope (combinatorial number theory; integer sequences) and strict AI rules |
| 7 | American Mathematical Monthly; Mathematical Gazette | Long history of arctangent-formula papers | Expository style required; Monthly is highly selective |
| 8 | Notes on Number Theory and Discrete Mathematics | Published BBP-type papers; no fees | Lower standing; repeated submission pauses |
| n/a | Involve; Rose-Hulman Undergraduate Mathematics Journal | - | Not open to a non-student solo author |

**Mathematics of Computation (AMS)**
- Scope: articles must be of significant computational interest and contain original and substantial mathematical analysis or development of computational methodology; areas include "computational discrete mathematics, including number theory, algebra and combinatorics". Authors are limited to three submissions within any 12-month period. — [AMS: Math. Comp.](https://www.ams.org/mcom) (via search summary; pubs.ams.org blocked direct reading)
- Track record: Bailey, Borwein and Plouffe, "On the Rapid Computation of Various Polylogarithmic Constants", Math. Comp. 66 (1997), no. 218, 903-913; Ferguson, Bailey and Arno, "Analysis of PSLQ", Math. Comp. 68 (1999), 351-369. — [Bailey, Compendium of BBP-type formulas, 8 Apr 2023, refs 14 and 23](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)
- Fees: AMS lists only two gold open access journals with article charges (Proc. AMS Series B at USD 1,500 and Trans. AMS Series B at USD 2,750); its other subscription journals are green open access, where the author may post the accepted manuscript on arXiv or a personal page with no embargo. — [AMS open access models](https://www.ams.org/publications/journals/open-access/open-access)
- Submission: PDF upload through AMS Centralized Manuscript Processing; the author may suggest an appropriate editor. — [AMS initial submission page](https://www.ams.org/publications/authors/journals/peer-review/peer-review-submission)
- Review time: no official figure found; a third-party aggregator lists about 7 months average. — [LetPub](https://www.letpub.com/journal-selector/journal/5741) (unverified third party)
- AI policy (AMS, adapted from COPE February 2023): AI tools "cannot be listed as an author"; authors who use AI tools in writing, images, or data collection and analysis "must be transparent in disclosing in the Materials and Methods (or similar section) of the paper how the AI tool was used and which tool was used"; authors are fully responsible for content, including AI-produced parts; editors and referees may not upload papers under review to an LLM. — [AMS: Use of Artificial Intelligence](https://www.ams.org/publications/journals/policies/UseofArtificialIntelligence)

**Canadian Journal of Mathematics / Canadian Mathematical Bulletin (Canadian Mathematical Society, Cambridge University Press)**
- CJM "publishes original, high-quality research papers in all branches of mathematics"; submitted papers should be "between 25 pages and 40 pages long", shorter papers go to the Bulletin. — [CJM: about](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/information/about-this-journal)
- CMB papers should be "at most 24 pages long". — [CMB: about](https://www.cambridge.org/core/journals/canadian-mathematical-bulletin/information/about-this-journal)
- Track record: Borwein, Borwein and Galway, "Finding and Excluding b-ary Machin-Type Individual Digit Formulae", Canad. J. Math. 56(5), 2004, 897-925, DOI 10.4153/CJM-2004-041-2; the paper shows pi has no Machin-type BBP arctangent formula for base b not equal to 2 and uses factorization over the Gaussian integers. — [Cambridge Core article page](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/finding-and-excluding-bary-machintype-individual-digit-formulae/BB7919C8E1AE66878AE8D7BC7F0EBFA3)
- AI policy (Cambridge): "AI use must be declared and clearly explained"; AI "may not be listed as an author"; authors are accountable for accuracy, integrity and originality. — [Cambridge: authorship and contributorship, journals](https://www.cambridge.org/core/services/publishing-ethics/authorship-and-contributorship-journals)

**Experimental Mathematics (Taylor and Francis)**
- Scope (via search summary of the publisher page): papers need both an experimental component and relevance to mathematics proper; suitable work includes experiments yielding new theorems or conjectures and algorithms for exploring mathematical problems; computer experiments should be reported so others can repeat them and programs ideally shared; initial appraisal by the Editors-in-Chief, then single-anonymized peer review. — [T and F: Experimental Mathematics](https://www.tandfonline.com/journals/uexm20) (via search summary; direct read blocked)
- Published by A K Peters until 2010, now Taylor and Francis; current editor-in-chief listed as Alexander Kasprzyk; indexed in MathSciNet, zbMATH, Scopus and Web of Science. — [Wikipedia: Experimental Mathematics (journal)](https://en.wikipedia.org/wiki/Experimental_Mathematics_(journal))
- Track record: Bailey and Crandall, "On the Random Character of Fundamental Constant Expansions", Experimental Mathematics 10(2), 2001, 175-190 (the BBP-normality paper). — [Bailey compendium, ref 16](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)
- AI policy (Taylor and Francis): generative AI tools "must not be listed as an author"; any use must be acknowledged with tool name and version, how and why it was used; journal articles need an AI usage disclosure statement; "text or code generation without rigorous revision" is not permitted; idea generation, language improvement and coding assistance are permitted with oversight; some journals allow AI only for language improvement. — [Taylor and Francis AI policy](https://taylorandfrancis.com/our-policies/ai-policy/) (no date on page; footer 2026)

**Journal of Experimental Mathematics (JXM; Association for Mathematical Research)**
- Launched June 2023 (announcement dated 28 June 2023); diamond open access with "no charges to authors nor readers"; "publishes research articles in all branches of mathematics that feature experimental results with important implications"; peer reviewed; authors retain copyright and are encouraged to post on arXiv; submissions through ef.msp.org. — [JXM: about](https://journals.publicknowledgeproject.org/default2/index.php/jem/about)
- Origin: "the editorial board of Experimental Mathematics resigned en masse and founded the diamond open access" Journal of Experimental Mathematics, a flip facilitated by the AMR. — [Kontorovich, "Diamond Open Access: The AMR Experiment", arXiv:2601.02910, 6 Jan 2026](https://arxiv.org/html/2601.02910)
- Output so far: Vol. 2 No. 1 (2026), published 1 March 2026, has 9 articles on pages 1-207 (average of about 23 pages per article). — [jexpmath.org](https://jexpmath.org/)

**Indagationes Mathematicae (Elsevier, for the Royal Dutch Mathematical Society KWG)**
- Publishes "original mathematical research papers of high quality" of interest to a broad audience; only papers uploaded to arXiv are considered; hybrid open access; impact factor 0.8. — [Elsevier journal page](https://shop.elsevier.com/journals/indagationes-mathematicae/0019-3577)
- Track record: Gasull, Luca and Varona, "Three essays on Machin's type formulas", Indag. Math. (N.S.) 34 (2023), 1373-1396, DOI 10.1016/j.indag.2023.07.002; 22 pages; classifies two-term Machin formulas with 2-integer arguments; arXiv v1 1 February 2023, v2 16 July 2023. — [arXiv:2302.00154](https://www.arxiv.org/abs/2302.00154)

**Journal of Number Theory (Elsevier)**
- JNT "features selected research articles that represent the broad spectrum of interest in contemporary number theory", encourages "high quality, long articles where most or all of the technical details are included", and "now considers and welcomes also papers in Computational Number Theory". Impact factor 0.7. — [Elsevier: Journal of Number Theory](https://shop.elsevier.com/journals/journal-of-number-theory/0022-314X)
- Hybrid journal; open access charge listed by a third-party site as USD 3,550; the subscription route has no author fee. — [MPDL journal record](https://oapublishing.mpdl.mpg.de/journals/Record/Elsevier-0022314X); [third-party listing](https://m.wanweixueshu.com/sci/detail/52675) (APC figure unverified)
- AI policy (Elsevier, "Policy updated June 2026"): a separate AI declaration is required at submission and is published, placed "immediately before the references", titled "Declaration of generative AI and AI-assisted technologies in the manuscript preparation process"; AI use in the research itself goes in the Methods section; "Basic checks of grammar, spelling and punctuation do not need a declaration statement"; "Authors should not list AI tools as an author or co-author". — [Elsevier generative AI policies for journals](https://www.elsevier.com/about/policies-and-standards/generative-ai-policies-for-journals)

**The Ramanujan Journal (Springer)**
- "Publishes high-quality papers in all areas of mathematics influenced by Srinivasa Ramanujan" (hypergeometric series, number theory, Fourier analysis); Editor-in-Chief Ken Ono; impact factor 0.8 (2025); median submission to first decision 3 days; indexed in Science Citation Index Expanded, Mathematical Reviews, zbMATH, Scopus. — [Springer: The Ramanujan Journal](https://link.springer.com/journal/11139) (read 21 Nov 2026)
- Hybrid; open access charge GBP 2,190 / USD 3,090 / EUR 2,490; subscription publishing has no charge and the choice is offered after acceptance. — [Ramanujan Journal: how to publish](https://link.springer.com/journal/11139/how-to-publish-with-us)
- Track record: Daisuke Takahashi, "On the computation and verification of pi using BBP-type formulas", Ramanujan J. 51(1), 2020, 177-186, DOI 10.1007/s11139-018-0104-x (two BBP-type formulas for pi; 20% fewer terms for verification). — [MaRDI portal record](https://portal.mardi4nfdi.de/wiki/Publication:2301911)

**Research in Number Theory (Springer)**
- "International, peer-reviewed Hybrid Journal" covering number theory and arithmetic geometry, publishing "high-quality original articles that make a significant contribution"; Editors-in-Chief Jennifer Balakrishnan, Ken Ono, Andrew Sutherland; impact factor 0.8 (2025); median submission to first decision 12 days; indexed in Mathematical Reviews, zbMATH, Scopus, ESCI. — [Springer: Research in Number Theory](https://link.springer.com/journal/40993); [aims and scope](https://link.springer.com/journal/40993/aims-and-scope) (read 21 Nov 2026)
- Open access charge GBP 2,590 / USD 3,790 / EUR 2,990; no charge under the subscription model. — [RNT: how to publish](https://link.springer.com/journal/40993/how-to-publish-with-us)
- Springer Nature AI policy (via search summary): LLMs do not meet authorship criteria; LLM use should be documented in the Methods section (or a suitable alternative part); AI-assisted copy editing for readability, grammar and style need not be declared, but that exemption excludes generative editorial work and autonomous content creation. Springer pages differ on whether copy editing must be declared. — [Springer editorial policies: AI](https://www.springer.com/us/editorial-policies/artificial-intelligence--ai-/25428500); [Springer Nature AI guidance](https://group.springernature.com/gp/group/ai/ai-guidance-for-our-researchers-and-communities)

**International Journal of Number Theory (World Scientific)**
- Publishes original research papers and review articles on all areas of number theory, including computational number theory; third-party listings say there is no page charge and that copyright transfers to World Scientific on acceptance; an article charge applies only if the author opts for gold open access. — [Wikipedia: IJNT](https://www.wikipedia.org/wiki/International_Journal_of_Number_Theory); [LetPub listing](https://www.letpub.com/journal-selector/journal/3823) (official submission page returned 403; treat as unverified)

**Integers: Electronic Journal of Combinatorial Number Theory**
- "Integers is a refereed electronic journal devoted to research in the area of combinatorial number theory"; welcomes original research in combinatorics and number theory, preferring work connected to both; free to read; "does not levy any charges or fees for the submission of articles, nor for the processing of articles"; CC BY 4.0; author keeps copyright. — [Integers home page](https://math.colgate.edu/~integers/); [Integers policies](https://math.colgate.edu/~integers/policies.html)
- Indexing claimed by the journal: MathSciNet, zbMATH Open, Scopus, DOAJ, Free Journal Network. — [Integers policies](https://math.colgate.edu/~integers/policies.html)
- Process: email a PDF to the journal with MSC codes, keywords and a confirmation that the article complies with the AI policy; acknowledgment within several days; unsuitable articles are normally answered within 1-2 weeks; referees know the authors' names; decision normally within two weeks of the last report; editors may check correctness with AI assistance. — [Integers instructions for authors](https://math.colgate.edu/~integers/submit.html); [Integers policies](https://math.colgate.edu/~integers/policies.html)
- AI policy (current page): authors "may use AI tools to support them" but tools "must never be used as a substitute for human critical thinking"; "The narrative and all the wording in the paper must be those of the authors, and not be AI-generated" (spell and grammar checkers excepted); any other AI use must be declared in a statement at the end of the manuscript at first submission. — [Integers instructions for authors](https://math.colgate.edu/~integers/submit.html); a search-engine snippet of the same page showed an older or different wording saying the journal "will not consider any article that makes use of artificial intelligence in producing mathematics, computer code, bibliographic information, or other content" — [same URL via search](https://math.colgate.edu/~integers/submit.html). The two versions conflict; the direct read on 21 Nov 2026 showed the permissive-with-declaration version.
- Track record: Kunle Adegoke, "A Novel Approach to the Discovery of Binary BBP-type Formulas for Polylogarithm Constants", Integers 12 (2012), 345-371. — [Bailey compendium, ref 4](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)
- The journal announced the death of its long-serving Editor-in-Chief Florian Luca on 28 July 2026; papers published in 2027 may be dedicated to him in a memorial Volume 27A. — [Integers home page](https://math.colgate.edu/~integers/)

**Journal of Integer Sequences (University of Waterloo)**
- "Devoted to papers dealing with integer sequences and closely related topics"; papers must deal explicitly with this topic and justify relevance (for example by citing OEIS sequences); "completely free for both authors and readers"; the site warns that invoices for publication are a scam; LaTeX only, emailed to Editor-in-Chief Jeffrey Shallit; suggest two or three referees; one paper at a time; authors retain copyright and may post to arXiv; not currently in the DOAJ. Editorial board includes N. J. A. Sloane (founding editor), Jeffrey Lagarias and Simon Plouffe. — [JIS home page](https://cs.uwaterloo.ca/journals/JIS/)
- Speed: Volume 28 (2025) median time from submission to final decision was 197 days; acceptance to publication 4 days; referees are asked to report within two months. — [JIS home page](https://cs.uwaterloo.ca/journals/JIS/)
- AI policy: do not use an LLM to write the text ("the words of your paper must be your own"); LLMs may help locate references but each must be checked; LLM-suggested proofs or techniques must be explicitly credited and carefully checked; undisclosed AI use is grounds for "immediate rejection" and possibly a lifetime ban. — [JIS home page](https://cs.uwaterloo.ca/journals/JIS/)
- Immediately rejected topics: claimed proofs of Goldbach, twin primes, Riemann hypothesis, 3x+1, Fermat and similar; brute-force extension of sequences is not accepted. — [JIS home page](https://cs.uwaterloo.ca/journals/JIS/)
- Track record: Marc Chamberland, "Binary BBP-Formulae for Logarithms and Generalized Gaussian-Mersenne Primes", J. Integer Seq. 6 (2003), Article 03.3.7 — [JIS volume 6](https://cs.uwaterloo.ca/journals/JIS/vol6.html); Abrarov, Siddiqui, Jagpal and Quine, "A New Form of the Machin-like Formula for pi by Iteration with Increasing Integers", J. Integer Seq. 25 (2022), Article 22.4.5, received 25 Nov 2021, published 10 Apr 2022 — [JIS article page](https://www.cs.uwaterloo.ca/journals/JIS/VOL25/Abrarov/abrarov5.html)

**American Mathematical Monthly (MAA, published by Taylor and Francis)**
- "An international, peer-reviewed journal that publishes high-quality, original expository research"; prioritizes articles that are "clear, informative, engaging, and accessible to a broad audience"; English only; "double-anonymous review policy"; article types include Articles and Notes; new submissions must include a title page and cover letter and use the Monthly LaTeX style; editor listed as Annalisa Crannell. — [MAA: The American Mathematical Monthly](https://maa.org/publication/the-american-mathematical-monthly/) (read 21 Nov 2026)
- Articles generally run 6-20 pages (via search summary of the MAA page); an aggregator lists an acceptance rate of 11% as of January 2025. — [MAA page](https://maa.org/publication/the-american-mathematical-monthly/); [aggregator](https://web.osu.cz/~Zusmanovich/links/j/data/a/american-mathematical-m.html) (acceptance figure is third party and unverified)
- Track record: D. H. Lehmer, "On Arccotangent Relations for pi", Amer. Math. Monthly 45(10), 1938, 657-664 — [Wikipedia: Machin-like formula, ref 4](https://en.wikipedia.org/wiki/Machin-like_formula); Adamchik and Wagon, "A Simple Formula for Pi", Amer. Math. Monthly, Nov. 1997, 852-855 — [Bailey compendium, ref 1](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)

**The Mathematical Gazette (The Mathematical Association)**
- Publishes articles about the teaching and learning of mathematics and "fascinating expositions of attractive areas of mathematics" for teachers, lecturers, students and others; Cambridge University Press stopped publishing it at the end of 2025 and submission guidelines now sit on the Taylor and Francis site. — [Cambridge Core: Mathematical Gazette](https://www.cambridge.org/core/journals/mathematical-gazette); [Mathematical Association](https://www.m-a.org.uk/the-mathematical-gazette)
- Track record: Michael Wetherfield, "The Enhancement of Machin's Formula by Todd's Process", Math. Gazette 80(488), 333-344; Hwang Chien-Lih, "More Machin-Type Identities", Math. Gazette 81(490) (1997), source of the most efficient known Machin-like formula per Wikipedia. — [Wikipedia: Machin-like formula](https://en.wikipedia.org/wiki/Machin-like_formula) (the page dates the Wetherfield item 2016, which does not match volume 80; verify)

**Notes on Number Theory and Discrete Mathematics (NNTDM; Bulgarian Academy of Sciences)**
- Published since 1995, four issues a year; scope covers elementary number theory, arithmetic functions, primes, recurrences, Diophantine equations, combinatorics; official publication of the "Prof. Marin Drinov" Publishing House of the Bulgarian Academy of Sciences since 2013. — [NNTDM home](https://nntdm.net/)
- Indexing listed by the journal: Web of Science Emerging Sources Citation Index, CrossRef, DOAJ, OpenAlex, ROAD, Scilit, WorldCat. Journal Impact Factor 0.6 (2024) and 0.5 (2025), quartile Q3 in both years (Q4 in 2023). Scopus, zbMATH and MathSciNet are not on its list. — [NNTDM indexing](https://nntdm.net/indexing/); [NNTDM news](https://nntdm.net/author/admin/)
- No article processing charges. — [DOAJ record](https://doaj.org/toc/2367-8275)
- Submissions were suspended four times in two years because volume exceeded volunteer editor capacity: 15 Dec 2024-15 Feb 2025, 1 Jul-30 Sep 2025, 1 Dec 2025-1 Feb 2026, and 1 Jun-31 Aug 2026; no resumption notice was visible on the news page. — [NNTDM news](https://nntdm.net/author/admin/)
- Track record: Adegoke, "A Novel Approach to the Discovery of Ternary BBP-type Formulas for Polylogarithm Constants", NNTDM 17(1), 2011, 4-20; Adegoke, Lafont and Layeni, "A class of digit extraction BBP-type formulas in general binary bases", NNTDM 17(4), 18-32. — [Bailey compendium, refs 5 and 12](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)

**Involve and the Rose-Hulman Undergraduate Mathematics Journal**
- Involve requires "a minimum of one-third student authorship" and states that "faculty co-authorship is required"; no author fees. — [Involve: about](https://msp.org/involve/about/journal/about.html)
- RHUMJ publishes work done by undergraduates (completed before graduation), and each paper "must be sponsored by a mathematician familiar with the student's work". — [RHUMJ](https://scholar.rose-hulman.edu/rhumj/)

**For the optional Lean formalization**
- Annals of Formalized Mathematics, founded 2024, is a "diamond open access overlay journal" for formalized mathematics and mathematical applications of proof assistants; papers must come with a code artifact and should describe lessons learned in formalization. — [Annals of Formalized Mathematics](https://afm.episciences.org/)

**General advice on choosing among them**
- Terence Tao: look at "journals which have accepted papers similar to yours in the past"; check that the editorial board "contains at least one member who is expert enough"; a borderline submission to a top journal can mean "a lengthy process"; "a journal devoted to research mathematics is unlikely to accept any paper whose primary focus lies in recreational mathematics"; after rejection, revise and move "from more selective to less selective journals". — [Tao: Submit to an appropriate journal](https://terrytao.wordpress.com/advice-on-writing-papers/submit-to-an-appropriate-journal/)
- Henry Cohn: pick a journal that publishes work like yours in topic, style, length and importance, starting with the journals that published the papers you cite. — [Cohn: Advice for amateur mathematicians](https://cohn.mit.edu/advice)

### Inferences
- The strongest framing for paper (1) is "completes Borwein-Borwein-Galway 2004 and connects it to Gasull-Luca-Varona 2023". That points to CJM/CMB, Indagationes, and Math. Comp. as the three venues whose editors and referees already know the problem. CJM's 25-40 page window fits a full classification with proofs; CMB (at most 24 pages) fits a tightened version.
- A realistic submission ladder for a first-time independent author: (a) Math. Comp. or CJM if an expert who has read the paper says the result is strong enough; otherwise (b) Experimental Mathematics, JXM, Journal of Number Theory or Research in Number Theory; then (c) Integers or the Journal of Integer Sequences. Each rung costs months (for example, 197 days median at JIS), so the first choice should be made with informal expert input rather than optimism.
- The very short Springer medians (3 days at the Ramanujan Journal, 12 at Research in Number Theory) are medians to first decision and almost certainly reflect many quick desk rejections; they are not referee turnaround times.
- Money is not an obstacle anywhere on this list if the subscription route is chosen; the author should decline hybrid open access (USD 3,090-3,790) and rely on arXiv/Zenodo for free access.
- AI-assisted drafting is the largest practical constraint. If an LLM wrote any of the prose, the Journal of Integer Sequences is ruled out and Integers requires the wording to be rewritten by the author plus a declaration. AMS, Elsevier, Springer, Cambridge and Taylor and Francis journals accept disclosed AI use. If an AI suggested proof steps, JIS and AMS-style policies both imply stating that explicitly.
- Paper (1) uses heavy but classical tools (Z[i] factorization, Bang-Zsigmondy, Baker). A Monthly submission would need to be rewritten as exposition around one striking statement (for example the optimal digit-extraction formula) rather than the full classification.

### Gaps
- Official time-to-first-decision, acceptance rate and open access price for Experimental Mathematics, Journal of Number Theory, Indagationes, IJNT and Math. Comp. could not be read (publisher sites blocked automated access). The 7-month Math. Comp. figure and USD 3,550 JNT charge are third party.
- Whether Experimental Mathematics or JXM has published a Machin-type (arctangent) classification paper specifically was not established; only the BBP-related Bailey-Crandall paper was confirmed.
- JXM's indexing in MathSciNet/zbMATH/Scopus was not stated on its pages and could not be checked on zbMATH (blocked).
- No Monthly-specific or Gazette-specific AI policy text was read; both are distributed by Taylor and Francis, so its policy likely applies, but that is an assumption.
- Typical accepted length was only available for CJM, CMB, the Monthly and (by calculation) JXM.

---

## Key Question 3: Venues that fit paper (2), the algorithm and GPU software paper

### Takeaway
There is no perfect home: Mathematics of Computation wants substantial mathematical analysis behind the computation, ACM TOMS wants a complete, portable, refereed software package, and JOSS (free, fast-moving) now refuses projects with less than six months of public development history or without evidence of research use. The realistic plan is arXiv (math.NT with a cs.MS cross-list) plus a Zenodo-archived release now, with TOMS or Math. Comp. as the journal target and JOSS as a later add-on once the repository has history and users.

### Cited Findings

**Mathematics of Computation** (see Key Question 2 for scope, fees and AI policy)
- Articles must be "of significant computational interest and contain original and substantial mathematical analysis or development of computational methodology". — [AMS: Math. Comp.](https://www.ams.org/mcom) (via search summary)

**ACM Transactions on Mathematical Software (TOMS)**
- TOMS "publishes significant research results concerning the development, evaluation and use of mathematical software". Paper types include research papers, algorithm papers (a complete, well-engineered package, published in the Collected Algorithms of the ACM), remarks and certifications. — [TOMS author information (page last changed July 2013)](https://www.cs.kent.ac.uk/projects/toms/Authors.html)
- Algorithm policy: the code must offer a capability not readily available or do a task better than previous work, with efficiency claims backed by evidence across a wide range of practical problems; the package must be "complete, portable, well documented, and well structured", with a test driver, testing material and a build file; portability evidence is successful runs on three platform/compiler combinations; all material including code is refereed; copyright transfers to ACM on acceptance. — [TOMS Algorithms Policy (revised August 2007)](https://www.cs.kent.ac.uk/projects/toms/AlgPolicy.html)
- TOMS runs a Replicated Computational Results (RCR) review in which an independent reviewer confirms the results are replicable; described on the archived page as optional. — [TOMS RCR initiative](https://cs.kent.ac.uk/projects/toms/RCR.html) (via search summary; older page)
- ACM authorship policy, "Updated on May 14, 2026": authors must be identifiable humans and supply an ORCID; AI used to conduct the research, expressly including "coding" and "creation of artifacts ... such as code", "must be described in detail in the methods section"; for AI used to assist with writing, "ACM no longer requires the disclosure"; authors are accountable for any problematic content regardless of source. — [ACM Policy on Authorship](https://www.acm.org/publications/policies/new-acm-policy-on-authorship)

**Journal of Open Source Software (JOSS)**
- Requirements: OSI-approved open source license; repository browsable and cloneable without registration; "The repository must have been public for more than six months prior to submission" with active development across that period; "There must be evidence that the software is being used for research"; the submitter must be a major contributor with a GitHub account; the paper lives in the repository as paper.md. — [JOSS: submitting](https://joss.readthedocs.io/en/latest/submitting.html)
- Scope limits: "Your paper must not focus on new research results accomplished with the software"; "minor utility" and single-function packages are not acceptable; failing the screening gates is a "not yet" and authors can resubmit after six months. — [JOSS: submitting](https://joss.readthedocs.io/en/latest/submitting.html)
- The scope change was announced on 5 January 2026 because "the marginal cost of code generation is rapidly approaching zero"; evaluation moved to research impact, design thinking and open development history; "Projects developed in private are not eligible until there is a public record of open development". — [JOSS blog, January 2026](https://blog.joss.theoj.org/2026/01/preparing-joss-for-a-generative-ai-future)
- AI: use is permitted but an "AI usage disclosure" (tools and versions, scope of assistance, confirmation of human review and of human design decisions) is mandatory; incomplete disclosure "may be considered an ethical breach"; AI may not be used for conversation with editors or reviewers except translation. — [JOSS: submitting](https://joss.readthedocs.io/en/latest/submitting.html)
- Cost and rights: "There are no fees for submitting or publishing in JOSS"; papers are CC BY 4.0 with author copyright; accepted papers get a Crossref DOI; preprints are welcome. — [JOSS: about](https://joss.theoj.org/about); [JOSS: submitting](https://joss.readthedocs.io/en/latest/submitting.html)

**Journal of Symbolic Computation (Elsevier)**
- Directed at "mathematicians and computer scientists who have a particular interest in symbolic computation"; a forum for "the algorithmic treatment of all types of symbolic objects"; areas include computational algebra and design and implementation of symbolic computation systems; impact factor 0.9. — [Elsevier: Journal of Symbolic Computation](https://shop.elsevier.com/journals/journal-of-symbolic-computation/0747-7171)

**Experimental Mathematics / Journal of Experimental Mathematics**
- Algorithms for solving or exploring mathematical problems are in scope at Experimental Mathematics, which favors theoretical impact over applications and asks that programs be shared where possible. — [T and F: Experimental Mathematics](https://www.tandfonline.com/journals/uexm20) (via search summary)

**The Ramanujan Journal as a precedent for pi-computation papers**
- Takahashi's 2020 paper on computing and verifying pi with BBP-type formulas is a computation-and-verification paper in a number theory journal. — [MaRDI portal record](https://portal.mardi4nfdi.de/wiki/Publication:2301911)

**Conferences**
- ISSAC (International Symposium on Symbolic and Algebraic Computation) is the annual venue for symbolic mathematical computation; ISSAC 2027 is in Tsukuba, Japan, 12-15 July 2027, and ISSAC 2028 in Madrid in July 2028. — [ISSAC](https://www.issac-conference.org/)
- ARITH (IEEE International Symposium on Computer Arithmetic): the 33rd edition was in Fulda, Germany, 28 June-1 July 2026; the community site showed nothing yet for 2027. — [ARITH symposium site](http://www.arithsymposium.org/)

**The benchmark target**
- y-cruncher (Alexander J. Yee): current version 0.8.7 Build 9547, released 23 November 2025; development is on hiatus; downloading requires accepting a license agreement; "Two algorithms are available for most constants. One for computation and one for verification"; the official Mersenneforum subforum is its main community forum. Page last updated 25 October 2026. — [y-cruncher home page](https://www.numberworld.org/y-cruncher/)

**arXiv categories** — cs.MS is defined as ACM class G.4 (mathematical software); cs.DS as data structures and analysis of algorithms; cs.DC as parallel and cluster computing. — [arXiv category taxonomy](https://arxiv.org/category_taxonomy)

### Inferences
- A brand-new GPU pi program fails two JOSS gates on day one (six months of public history; evidence of research use). Making the repository public now starts the clock; JOSS becomes feasible around mid-2027 if there are releases, issues and at least one external user or citing paper. JOSS also says the paper must not centre on new research results, so the algorithmic novelty belongs in a separate paper.
- TOMS is the best match for "algorithm plus program plus benchmarks", but its portability requirement (three platform/compiler combinations, minimal machine dependence) is awkward for GPU code tied to one vendor; a CPU reference implementation alongside the GPU path would help. The Kent policy pages are old (2007-2013), so the current ACM instructions must be checked.
- Math. Comp. is plausible for paper (2) only if the paper contains a real analysis (error bounds for the windowed digit extraction, complexity, proof of correctness of the rounding), not just engineering and timings.
- Splitting is cleaner than merging: paper (1) carries the optimal formula as a theorem; paper (2) cites it and contributes the algorithm, the correctness analysis and reproducible benchmarks. Journals forbid simultaneous submission of the same paper, but two distinct papers to two journals is normal.
- ISSAC 2027 (July 2027, Tsukuba) is the natural conference; conference papers at ACM venues normally require an author to register and present, which is a cost for a self-funded author. ARITH is about hardware and software arithmetic and fits only if the paper's core is the modular-exponentiation and fixed-point arithmetic kernel.
- Benchmarks against y-cruncher should name the exact version (0.8.7 Build 9547) and should be run under the terms of its license agreement, which I did not read.

### Gaps
- No SIAM journal information was gathered; the search budget ran out before SIAM (for example SIAM J. Sci. Comput.) scope and AI policy could be checked.
- ISSAC 2027 and ARITH 2027 calls for papers, deadlines and page limits were not found.
- Current TOMS author guidelines on dl.acm.org, its open access charge and current RCR status were blocked; only archived editorial pages were read.
- JOSS end-to-end review time and current acceptance statistics were not found.
- y-cruncher's license terms on publishing benchmarks were not read.
- Whether Mersenneforum has an active thread culture for third-party BBP/digit-extraction tools was not checked beyond y-cruncher's statement.

---

## Key Question 4: Do journals accept papers from independent or amateur authors in practice?

### Takeaway
Yes: journals do not require an affiliation, and there are documented recent cases (a prison inmate as first author in Research in Number Theory in 2020; a biogerontologist in Geombinatorics in 2018; a retired printer as first author of the 2023 aperiodic monotile paper; an unaffiliated author publishing pi digit-extraction history in Euleriana in 2023). The consistent advice from mathematicians is that the barrier is credibility, not credentials: write to professional norms, show command of the literature, get a knowledgeable reader before the referee, and avoid looking like the crank submissions editors screen out.

### Cited Findings

**Examples, 2015-2026**
- Christopher Havens, serving a 25-year sentence in Washington State and largely self-taught, is first author of a paper in Research in Number Theory (January 2020, DOI 10.1007/s40993-020-0187-5) on continued fractions. Contact began in January 2013 with a letter asking about a subscription to Annals of Mathematics, which was forwarded to the production editor at Mathematical Sciences Publishers, who connected him with number theorist Umberto Cerruti (University of Torino); the paper was co-authored with mathematicians in Italy. — [The Conversation, 14 May 2020](https://theconversation.com/an-inmates-love-for-math-leads-to-new-discoveries-130123)
- Aubrey de Grey, a biogerontologist working on mathematics in his spare time, posted "The chromatic number of the plane is at least 5" on arXiv in April 2018; it was published in Geombinatorics 28 (2018), no. 1, 18-31. — [arXiv:1804.02385](https://arxiv.org/abs/1804.02385); [MathOverflow thread 44244](https://mathoverflow.net/questions/44244/what-recent-discoveries-have-amateur-mathematicians-made)
- David Smith, listed as a retired printer, is first author (with Myers, Kaplan and Goodman-Strauss) of "An aperiodic monotile", arXiv March 2023, 91 pages, with a copyedited journal version (related DOI 10.5070/C64163843). — [arXiv:2303.10798](https://arxiv.org/abs/2303.10798); [Wikipedia: List of amateur mathematicians](https://en.wikipedia.org/wiki/List_of_amateur_mathematicians)
- Nick Craig-Wood, with no affiliation shown, published "Euler Found the First Binary Digit Extraction Formula for pi in 1779" in Euleriana 3(1), 2023, 23-30 (DOI 10.56031/2693-9908.1049); David Bailey's BBP compendium cites it; the same author has the 2025-2026 Machin-like PSLQ preprint on arXiv math.NT. — [Euleriana](https://scholarlycommons.pacific.edu/euleriana/vol3/iss1/3); [Bailey compendium, ref 22](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf); [arXiv:2508.08307](https://arxiv.org/abs/2508.08307)
- Earlier cases collected by mathematicians: Ahcène Lamari, then a high-school teacher, published a proof about compact complex surfaces in Annales de l'Institut Fourier (1999); Marjorie Rice (no training beyond high school) found new pentagonal tilings; Greg Egan (science fiction writer) co-authored peer-reviewed papers; Kenneth Perko (lawyer) found the Perko pair. — [MathOverflow thread 44244](https://mathoverflow.net/questions/44244/what-recent-discoveries-have-amateur-mathematicians-made)
- 2026 AI-assisted case: a hobbyist, Liam Price, used ChatGPT to prove a 60-year-old Erdős conjecture on primitive sets; the raw proof was reported as rough and was streamlined by Jared Lichtman and Terence Tao. No journal citation was found. — [Scientific American](https://www.scientificamerican.com/article/amateur-armed-with-chatgpt-vibe-maths-a-60-year-old-problem/) (via search summary)

**How journals treat affiliation**
- Integers states that articles "will be evaluated exclusively on the basis of their mathematical interest and importance". — [Integers policies](https://math.colgate.edu/~integers/policies.html)
- The Monthly uses double-anonymous review, so referees do not see the author's name or affiliation. — [MAA: The American Mathematical Monthly](https://maa.org/publication/the-american-mathematical-monthly/)
- Anecdote from a mathematician with no academic post: the affiliation field was left blank, the paper went to press, and the copy editor asked for an affiliation only after acceptance. — [Physics Forums thread](https://www.physicsforums.com/threads/publishing-maths-papers-with-no-affiliation.274099/post-1970678) (forum anecdote)
- Incepta Mathematica (California State University) explicitly welcomes submissions from amateur mathematicians and scholars without a PhD. — [Incepta Mathematica: about](https://journals.calstate.edu/im/about) (via search summary)
- What editors screen out: the Journal of Integer Sequences immediately rejects claimed proofs of Goldbach, twin primes, the Riemann hypothesis, 3x+1 and similar. — [JIS home page](https://cs.uwaterloo.ca/journals/JIS/)

**Advice from mathematicians**
- Henry Cohn (MIT): "There's no reason why amateurs can't make worthwhile research contributions in mathematics", but "If you want anyone to take your work seriously, you need to develop a track record that separates you from the cranks"; the easiest way is to publish some modest, uncontroversial papers first. — [Cohn: Advice for amateur mathematicians on writing and publishing papers](https://cohn.mit.edu/advice) (undated)
- Cohn's practical list: use standard terminology and notation; spend a few hours searching the literature (MathSciNet through a library); write an introduction that explains the topic, relevance and techniques without bragging; include a one-paragraph abstract and do not force a generic science-paper format; use LaTeX; get friends or collaborators to criticise the draft because referees should not be the first readers; submit to one journal at a time; provide code the work relies on; check receipt after a couple of weeks and inquire after about six months; after a substantive rejection, revise before sending elsewhere. — [Cohn](https://cohn.mit.edu/advice)
- Terence Tao: "you should be submitting a final draft, not a first draft"; use the introduction to sell the key points; describe the results accurately; "a positive rejection rate is to be expected if one is submitting to reputable journals". — [Tao: advice on writing papers](https://terrytao.wordpress.com/advice-on-writing-papers/); [Tao: Submit to an appropriate journal](https://terrytao.wordpress.com/advice-on-writing-papers/submit-to-an-appropriate-journal/)
- Tao notes his career advice is aimed at academic careers and that he has no specially informed advice for other paths. — [Tao: career advice](https://terrytao.wordpress.com/career-advice/)
- Background caution: amateurs often struggle for recognition because their work can be overshadowed by the prevalence of unfounded claims from cranks. — [EBSCO Research Starters: amateur mathematicians](https://www.ebsco.com/research-starters/education/amateur-mathematicians)

### Inferences
- The two candidate papers are well positioned by Cohn's criteria: they are not claims about famous open problems, they extend a named 2004 paper, and they come with verifiable computation and (possibly) a Lean proof. That profile reads as "serious, uncontroversial contribution", which is what earns a referee's attention.
- In most documented amateur successes a professional was involved before publication (Havens with Cerruti; Smith with three academics; Price with Lichtman and Tao). An expert reader or co-author is the single most reliable accelerator, and also solves the arXiv endorsement problem.
- Practical first-timer details: put "Independent researcher" plus city and country (or leave affiliation blank), use a stable email address, create an ORCID (ACM requires one), and typeset in the target journal's LaTeX class.
- A Lean formalization of the first theorem directly addresses the main worry a referee has about an unknown author (is the proof right?) and should be mentioned in the abstract and cover letter.

### Gaps
- I did not find systematic data on acceptance rates for unaffiliated authors; evidence is case-based.
- I could not read the well-known Academia Stack Exchange discussions on outsider submissions (site blocked), so no advice is attributed to them.
- I did not find AMS Notices articles specifically about amateurs publishing; the Notices items located concern predatory journals (see Key Question 6).
- Affiliations of several example authors (for instance Kunle Adegoke, who published many BBP-type papers) were not verified, so they are not presented as amateur cases.

---

## Key Question 5: Publisher and journal policies on generative AI (authorship, disclosure) and mathematics-specific guidance, 2024-2026

### Takeaway
Every publisher checked bars AI from authorship and holds the human author fully responsible; almost all require disclosure, but they differ on where it goes and what is exempt, and two specialist number theory journals are much stricter about AI-written prose. Mathematics societies have moved toward explicit declarations (the LMS has required an "AI Declaration" in every manuscript as of its October 2026 policy), while ACM moved the other way in May 2026 and dropped disclosure for writing assistance.

### Cited Findings

| Publisher / venue | AI as author | Disclosure rule | Notable specifics | Source (date on page) |
|---|---|---|---|---|
| AMS | Not allowed | Disclose in Materials and Methods or similar section how the tool was used and which tool | Authors liable for AI-produced parts; referees and editors may not upload papers to an LLM | [AMS](https://www.ams.org/publications/journals/policies/UseofArtificialIntelligence) (adapted from COPE Feb 2023; undated) |
| London Mathematical Society | Not allowed | Every manuscript must contain an "AI Declaration" section, either describing all AI use (tool name and model number, how it contributed) or stating none was used | Substantial use of other mathematical software or code must be declared separately; uploading a manuscript to an AI tool for review is misconduct | [LMS](https://www.lms.ac.uk/publications/policies/AI) (updated October 2026) |
| Taylor and Francis | Not allowed | AI usage disclosure statement with tool name, version, how and why | "Text or code generation without rigorous revision" not permitted; coding assistance and language improvement permitted; some journals allow language use only | [T and F](https://taylorandfrancis.com/our-policies/ai-policy/) (undated; 2026 footer) |
| Springer Nature | Not allowed | Document LLM use in the Methods section or suitable alternative | AI-assisted copy editing exempt on journal-level pages; group page is stricter; pages conflict | [Springer](https://www.springer.com/us/editorial-policies/artificial-intelligence--ai-/25428500); [Springer Nature group](https://group.springernature.com/gp/group/ai/ai-guidance-for-our-researchers-and-communities) (via search summary) |
| Elsevier | Not allowed | Separate declaration before the references naming tool, purpose and oversight; research use in Methods | Grammar/spelling checks exempt; fabricated references may lead to rejection; generating sections without genuine intellectual contribution not permitted | [Elsevier](https://www.elsevier.com/about/policies-and-standards/generative-ai-policies-for-journals) ("Policy updated June 2026") |
| Cambridge University Press | Not allowed | "AI use must be declared and clearly explained", as with other software and tools | Journals may set stricter rules | [Cambridge](https://www.cambridge.org/core/services/publishing-ethics/authorship-and-contributorship-journals) |
| Wiley | Not allowed (authors fully responsible) | Disclose on submission; substantial use in Methods or a disclosure/acknowledgments statement | Spelling, grammar and general editing tools exempt; AI use should not cause automatic rejection; guidance issued March and October 2025 | [Wiley newsroom](https://newsroom.wiley.com/press-releases/press-release-details/2025/New-Wiley-Guidelines-Give-Researchers-Clear-Path-Forward-in-Responsible-AI-Use/default.aspx); [Enago summary](https://www.enago.com/responsible-ai-movement/publisher-ai-guidelines/wiley-ai-guidelines/) (via search summary; secondary) |
| ACM | Authors must be identifiable humans | AI used in the research (including coding) must be described in detail in the methods section; AI used for writing no longer needs disclosure | Rejection or retraction if AI-related integrity problems are found | [ACM](https://www.acm.org/publications/policies/new-acm-policy-on-authorship) (updated 14 May 2026) |
| arXiv | Not allowed | Report significant use of sophisticated tools including generative AI | Reported one-year ban for unchecked LLM output (May 2026) | [arXiv moderation](https://info.arxiv.org/help/moderation/index.html); [TechCrunch](https://techcrunch.com/2026/05/16/research-repository-arxiv-will-ban-authors-for-a-year-if-they-let-ai-do-all-the-work) |
| JOSS | n/a | Mandatory "AI usage disclosure" with tools, versions, scope and confirmation of human review | No AI in conversations with editors and reviewers | [JOSS](https://joss.readthedocs.io/en/latest/submitting.html) |
| Journal of Integer Sequences | n/a | LLM-suggested proofs or techniques must be explicitly credited | LLM must not write the text; undisclosed use means immediate rejection and possible lifetime ban | [JIS](https://cs.uwaterloo.ca/journals/JIS/) |
| Integers | n/a | Declaration at end of manuscript for any AI use beyond spell/grammar check; submission email must confirm compliance | Wording must be the authors' own; editors may use AI to check correctness | [Integers](https://math.colgate.edu/~integers/submit.html) |

- Elsevier's recommended declaration text: "During the preparation of this work the author(s) used [NAME OF TOOL/SERVICE] in order to [REASON]. After using this tool/service, the author(s) reviewed and edited the content as needed" and take full responsibility for the content. — [Elsevier](https://www.elsevier.com/about/policies-and-standards/generative-ai-policies-for-journals)
- The LMS also tells authors to review an AI tool's terms to confirm it does not claim ownership of their content. — [LMS AI policy](https://www.lms.ac.uk/publications/policies/AI)
- The EMS guidance on predatory publishing points to joint IMU and ICIAM recommendations published in the Notices of the AMS, November 2025, pp. 1179-1182. — [EMS: predatory publishing](https://euromathsoc.org/predatory-publishing)

### Inferences
- A single disclosure paragraph satisfies nearly every venue if it names the tool and version, says exactly what it was used for (literature search, code drafting, proof exploration, language editing), and affirms that the author verified every statement, proof, computation and reference. Placing it in a short "AI declaration" section before the references (and repeating the research-use part in the computational methods section) covers AMS, LMS, Elsevier, Springer, Taylor and Francis and Cambridge at once.
- Where AI contributed mathematical ideas, the honest and safest wording is explicit credit in the text at the point of use; JIS demands this and no publisher forbids it.
- Machine-checked proof (Lean) and published verification code are the strongest answer to referee doubts about AI-assisted mathematics; they move the question from "who wrote it" to "is it checked".
- Journals with prose restrictions (JIS, Integers) require the author to write the wording personally; if that is not how the manuscript was produced, pick a different journal rather than under-declare, since undisclosed use is the offence that carries bans.

### Gaps
- Springer Nature's and Wiley's policies were read only through search summaries; Springer's own pages reportedly conflict on copy-editing disclosure.
- No AI policy was found for the Journal of Experimental Mathematics, NNTDM, IJNT, or the Monthly and Gazette specifically.
- Two 2026 arXiv papers on the topic surfaced by title only and were not read: "Generative AI in Publishing: An Editors' Panel on Ethics and Policies" (arXiv:2610.10224) and "Expectations and Practices around AI Disclosure in CS Research" (arXiv:2608.23271).

---

## Key Question 6: Predatory journals, and the standing of NNTDM, Integers and the Journal of Integer Sequences

### Takeaway
The mathematics-specific test is simple: a serious journal is covered by zbMATH Open or MathSciNet, has editors you can recognise, describes real peer review, and does not solicit you or charge surprise fees. Integers and the Journal of Integer Sequences are reputable free journals run by known mathematicians; NNTDM is a legitimate but lower-tier society journal (ESCI, Q3) rather than a predatory one.

### Cited Findings
- EMS definition: predatory journals are "Journals that neglect scientific quality checks via peer review in the sole interest of cashing in on publication fees". — [EMS: On predatory publishing](https://euromathsoc.org/predatory-publishing) (undated)
- EMS red flags: unusually quick promised acceptance; solicitation by mass email or by someone unconnected to your field; hidden or later-revealed fees; a very large editorial board for the journal's size; a makeshift website or a publisher with many unrelated journals; and "It is not listed in either zbMATH Open or MathSciNet" ("You should not proceed unless you know that the journal is new and credible"). — [EMS](https://euromathsoc.org/predatory-publishing)
- EMS signs of a serious journal: recent papers by authors you respect, at least one editor you respect near your area, and a clear editorial policy, scope and peer review process. It adds that "Open Access and APCs are not themselves a good indication" either way, and warns that hybrid journals may charge large fees after publication. — [EMS](https://euromathsoc.org/predatory-publishing)
- Think.Check.Submit checklist: do you know the journal; can you identify and contact the publisher; is peer review clearly described without guaranteed acceptance or very short review times; are articles indexed and archived with persistent identifiers; are fees clear; are license and copyright terms clear; is the publisher in COPE, DOAJ or OASPA. Submit only if you can answer yes to most questions. — [Think.Check.Submit: journals](https://thinkchecksubmit.org/journals/)
- Beall's List was taken down in early 2017 and archived copies are not regularly updated; some university libraries advise against relying on it because of bias and lack of reproducibility. — [University library guides surfaced in search, e.g. University of Malta](https://www.um.edu.mt/library/openscience/predatorypublishing/) (via search summary; which guide made which statement was not verified)
- Forum caution: paying a journal to publish "independent research" is a bad idea, since journals that sell this are generally predatory. — [Physics Forums](https://www.physicsforums.com/threads/publishing-maths-papers-with-no-affiliation.274099/post-1970678) (single commenter)

**Integers**
- States it is indexed in MathSciNet, zbMATH Open and Scopus, and listed in DOAJ and the Free Journal Network; no submission or processing fees; CC BY 4.0; ethics statement based on COPE. — [Integers policies](https://math.colgate.edu/~integers/policies.html); Scopus listing corroborated by the [ISSN Portal record](https://portal.issn.org/resource/issn/1553-1732) (via search summary)

**Journal of Integer Sequences**
- Free for authors and readers, with an explicit warning that any invoice is a scam; edited by Jeffrey Shallit with N. J. A. Sloane as founding editor and Lagarias and Plouffe on the board; publishes its own turnaround statistics; states it is not in the DOAJ and explains why. Its page does not list indexing services. — [JIS home page](https://cs.uwaterloo.ca/journals/JIS/)

**NNTDM**
- Published under the Bulgarian Academy of Sciences since 1995; indexed in Web of Science ESCI and DOAJ; Journal Impact Factor 0.5 (2025), Q3; no author fees. Its own indexing list does not include Scopus, zbMATH or MathSciNet. — [NNTDM indexing](https://nntdm.net/indexing/); [NNTDM news](https://nntdm.net/author/admin/); [DOAJ](https://doaj.org/toc/2367-8275)
- A third-party metrics site using OpenAlex data ranks it Q4 with a score of 0.3. — [journalmetrics.org](https://www.journalmetrics.org/journal/notes-on-number-theory-and-discrete-mathematics) (third party)
- Cited by David Bailey's BBP compendium for two BBP-type papers, which shows working researchers in this niche read it. — [Bailey compendium, refs 5 and 12](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)

### Inferences
- None of the three journals shows predatory markers: none charges fees, none solicits, each has a named academic editorial structure and a stated review process. They differ in prestige, not legitimacy: Integers and JIS are respected specialist journals; NNTDM sits lower and its repeated intake pauses suggest an overloaded volunteer operation.
- For this project the real risk is not these journals but unsolicited invitations that will follow any arXiv or Zenodo posting (special issues, "rapid publication" with fees). Apply the EMS test: if the journal is not in zbMATH Open or MathSciNet, do not submit.
- Publishing a strong result in a weak venue has a cost: it cannot be resubmitted elsewhere. Lower-tier venues are a fallback after better options decline, not a first choice.

### Gaps
- zbMATH Open could not be queried (bot check), so I could not independently confirm zbMATH or MathSciNet coverage for JIS, NNTDM or JXM; for JIS and NNTDM this remains unverified and should be checked at zbmath.org/serials before submitting.
- Scimago quartiles for the target journals were not retrieved.
- No named list of predatory number theory journals from an authoritative source was found (the EMS page deliberately names none).

---

## Key Question 7: Getting an informal expert review first

### Takeaway
MathOverflow explicitly does not check work or accept result announcements, so it is useful only for sharp, self-contained sub-questions; the workable route is a short, specific email to one or two authors of the directly related papers, with the PDF, the exact statement, and how it relates to their theorem. One planned contact is no longer possible: Florian Luca, co-author of the 2023 Machin paper, died on 28 July 2026.

### Cited Findings
- MathOverflow's help centre: the site is for "mathematical questions related to current research in mathematics"; "the intended audience is professional mathematicians, mathematics graduate students, and undergraduates involved in research"; non-mathematicians "are likely to get a better response" on Mathematics Stack Exchange. — [MathOverflow help: on-topic](https://mathoverflow.net/help/on-topic) (read 21 Nov 2026)
- Verbatim: "MathOverflow is not for asking people to check your (or other people's) work. Nor is MathOverflow intended as a place to announce mathematical results." Questions should be precise and have a specific answer, of the type "Can this hypothesis in that theorem be relaxed in this way?" — [MathOverflow help: on-topic](https://mathoverflow.net/help/on-topic)
- A MathOverflow Meta discussion reports community agreement that asking for evaluations of preprints is off-base and that such questions get closed as off-topic. — [MathOverflow Meta thread 1265](https://meta.mathoverflow.net/questions/1265/using-math-overflow-to-check-whether-or-not-a-proof-is-correct) (via search summary of a mirror; older thread)
- Cohn: ask friends or collaborators to find problems and ask for criticism, not praise; "referees should not be your first readers"; rereading after a few months reveals unclear passages. — [Cohn](https://cohn.mit.edu/advice)
- arXiv's guidance on approaching potential endorsers applies equally to asking for a read: contact people whose recent papers yours cites, include the draft or a scholarly profile, and do not mass-email or repeatedly email. — [arXiv help: endorsement](https://info.arxiv.org/help/endorsement.html)

**Who works on exactly this**
- Gasull, Luca and Varona, "Three essays on Machin's type formulas" (2023); the PDF is hosted on Juan L. Varona's University of La Rioja page. — [arXiv:2302.00154](https://www.arxiv.org/abs/2302.00154); [Varona's copy](https://www.unirioja.es/cu/jvarona/downloads/Machin.pdf)
- Florian Luca died on 28 July 2026. — [Integers home page](https://math.colgate.edu/~integers/)
- Tomohiro Yamada, "Three-term Machin-type formulae" (finitely many nondegenerate three-term formulas, explicit bounds), arXiv 2018, sixth version 2 March 2025. — [arXiv:1811.09273](https://arxiv.org/abs/1811.09273)
- Simon Kristensen and Oskar Mathiasen, "BBP-type formulas — an elementary approach" (search algorithm with Sage code), arXiv August 2022. — [arXiv:2208.07696](https://arxiv.org/abs/2208.07696)
- Nick Craig-Wood, Machin-like PSLQ searches (2025-2026) and the Euler BBP history paper. — [arXiv:2508.08307](https://arxiv.org/abs/2508.08307)
- David H. Bailey maintains the Compendium of BBP-Type Formulas (version dated 8 April 2023), which cites manuscripts and private communications from contributors as well as journal papers. — [Bailey compendium](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)
- Borwein, Borwein and Galway (2004) affiliations at publication: Dalhousie, Western Ontario, Simon Fraser. — [Cambridge Core](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/finding-and-excluding-bary-machintype-individual-digit-formulae/BB7919C8E1AE66878AE8D7BC7F0EBFA3)
- Abrarov, Siddiqui, Jagpal (Epic College of Technology) and Quine (York University) publish on Machin-like formulas. — [JIS article](https://www.cs.uwaterloo.ca/journals/JIS/VOL25/Abrarov/abrarov5.html)
- Daisuke Takahashi published on BBP-based computation and verification of pi (2020). — [MaRDI record](https://portal.mardi4nfdi.de/wiki/Publication:2301911)

**Lists and forums**
- NMBRTHRY: the only description found is a 1992 list review giving a BITNET-era LISTSERV address at North Dakota State. — [List Review Service, January 1992](https://www.umsl.edu/~munsr/proddir/rev1n05.htm)
- Mersenneforum hosts the official y-cruncher subforum, described by its author as the main community forum. — [y-cruncher home page](https://www.numberworld.org/y-cruncher/)
- The Havens case shows that a plain letter to a mathematics publisher can reach a willing expert. — [The Conversation](https://theconversation.com/an-inmates-love-for-math-leads-to-new-discoveries-130123)

### Inferences
- What makes a cold email succeed (synthesised from the Cohn, Tao, arXiv and MathOverflow norms above): a subject line naming their paper; three or four sentences stating the theorem precisely and how it settles the case their paper left open; the PDF attached, typeset in LaTeX with a full bibliography; one concrete request (for example "is Lemma 3 already known?" or "would you be willing to endorse for math.NT if it looks sound?"); mention of independent verification (code repository, Lean file); no claims of revolution; one follow-up at most.
- Best first contacts for paper (1), in order: Juan L. Varona and Armengol Gasull (surviving authors of the closest paper), Tomohiro Yamada (active on Machin-type finiteness via Baker-type bounds), William Galway (surviving author of the 2004 paper, if reachable), then David Bailey for the BBP side and for possible inclusion in the compendium. For paper (2): Daisuke Takahashi and the y-cruncher community on Mersenneforum.
- On MathOverflow the right use is a narrow technical question whose answer you need (for example about primitive prime divisors of a specific sequence in Z[i]), written to stand alone, with the preprint linked only as context. "Please check my proof" will be closed.
- A positive reply from any of these people typically yields three things at once: an error check, an arXiv endorsement, and a suggestion of which journal and which editor.

### Gaps
- NMBRTHRY's current status, posting rules and archive could not be verified (the archive server failed a certificate check); it is unknown from this research whether announcements of preprints by unaffiliated authors are accepted in 2026.
- Current contact details and availability of the 2004 authors were not verified; check before writing.
- Mersenneforum's norms for announcing new software or asking for mathematical review were not read.
- The Lean community (Zulip) was not researched as a review channel for the formalization.

---

## Key Question 8: Priority, credit, and licensing of code and data

### Takeaway
A public, immutable, dated deposit establishes priority: arXiv versions carry submission dates, and Zenodo gives a DOI-stamped record that anyone can create without affiliation; a GitHub repository alone is weaker because releases can be altered or deleted. License choices are partly irreversible (arXiv) and partly constrained by venue (JOSS needs an OSI license; ACM CALGO takes copyright), so they should be chosen with the target venues in mind.

### Cited Findings
- arXiv records versioned submission dates on each abstract page (for example v1 1 Feb 2023 and v2 16 Jul 2023 for the Gasull-Luca-Varona paper). — [arXiv:2302.00154](https://www.arxiv.org/abs/2302.00154)
- arXiv license options: CC BY 4.0, CC BY-SA 4.0, CC BY-NC-SA 4.0, CC BY-NC-ND 4.0, the arXiv perpetual non-exclusive license 1.0, and CC Zero. "The license chosen is irrevocable and cannot be changed", though different versions can carry different licenses. arXiv advises checking journal policies first (for example with Sherpa Romeo); many publishers accept preprints under CC BY. — [arXiv help: license](https://info.arxiv.org/help/license/index.html)
- Zenodo: anyone may register; DOIs are issued; data files are versioned; a license must be specified; withdrawal leaves a tombstone with the DOI; retention is for the lifetime of the repository (hosted by CERN). Supported licenses include all Creative Commons licenses and those in the SPDX vocabulary. — [Zenodo General Policies v1.0](https://about.zenodo.org/policies/); [Zenodo help: about records](https://help.zenodo.org/docs/deposit/about-records) (second item via search summary)
- GitHub and Zenodo: Zenodo archives the repository and issues a new DOI each time a GitHub release is created, with a concept DOI covering all versions; with the integration a DOI cannot be reserved in advance (a manual upload can reserve one). A GitHub release by itself is a snapshot that can be deleted, renamed or changed. — [GitHub docs](https://docs.github.com/en/repositories/archiving-a-github-repository/referencing-and-citing-content); [Zenodo help: GitHub](https://help.zenodo.org/docs/github/archive-software/github-upload) (via search summary)
- viXra's stated rationale includes letting authors record "priority claims". — [viXra: why](https://vixra.org/why)
- Software licenses: MIT is short and permissive with no patent grant; Apache 2.0 is permissive with an express patent grant and a requirement to state changes; GPLv3 is strong copyleft requiring source disclosure under the same license. — [choosealicense.com](https://choosealicense.com/licenses/)
- Venue constraints: JOSS requires an OSI-approved license and publishes papers under CC BY 4.0 with author copyright. — [JOSS: about](https://joss.theoj.org/about). TOMS algorithm papers transfer copyright to ACM, with liberal noncommercial reuse. — [TOMS Algorithms Policy (2007)](https://www.cs.kent.ac.uk/projects/toms/AlgPolicy.html). Integers and JIS leave copyright with the author (Integers under CC BY 4.0). — [Integers policies](https://math.colgate.edu/~integers/policies.html); [JIS](https://cs.uwaterloo.ca/journals/JIS/). Springer open access articles are CC BY or CC BY-NC-ND with author copyright. — [RNT: how to publish](https://link.springer.com/journal/40993/how-to-publish-with-us). AMS allows posting the accepted manuscript on arXiv. — [AMS open access](https://www.ams.org/publications/journals/open-access/open-access)
- y-cruncher is distributed under its own license agreement and its page does not describe it as open source. — [y-cruncher](https://www.numberworld.org/y-cruncher/)
- Credit conventions in this niche include informal channels: Bailey's compendium cites private communications, manuscripts and OEIS wiki pages alongside journals. — [Bailey compendium](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)

### Inferences
- Minimum priority package, achievable in one day without any endorsement: (1) deposit the PDF of each paper on Zenodo (DOI, date); (2) tag a GitHub release of the code, verification scripts, Lean files and digit data and archive it to Zenodo for a software DOI; (3) cite both DOIs in the papers. Add arXiv as soon as an endorsement arrives; arXiv is what number theorists actually read.
- Because the arXiv license is irrevocable, choose it deliberately. CC BY 4.0 is the most widely compatible with journal policies; the arXiv non-exclusive license is the most conservative if a target journal's policy is unclear.
- For code, Apache 2.0 or MIT maximise reuse and satisfy JOSS; GPLv3 prevents closed-source reuse. If ACM TOMS (CALGO) is a target, expect to transfer copyright in the submitted package to ACM, which is easier if the author holds all rights and has not bundled copyleft third-party code.
- Computed digit windows are facts and are best released under CC0 or CC BY with checksums, so others can verify and cite them.
- Zenodo deposits are permanent (tombstoned, not erased), so only deposit a version the author is prepared to have on record; errors are fixed by new versions, not deletion.

### Gaps
- No authoritative mathematics-specific statement was found on how priority disputes weigh an arXiv date against a Zenodo or GitHub date; the ordering above follows general practice, not a cited rule.
- I did not check each target journal's preprint and license policy in Sherpa Romeo.
- Whether y-cruncher's license restricts publishing comparative benchmarks was not read.
- Software citation tooling (for example CITATION.cff) was not researched.

---

## Search log (required by the assignment)

Web searches actually executed: 41. Five further queries (42-46) were refused because the shared search budget for the session was exhausted; those topics were covered, where possible, by reading known official URLs directly.

1. arXiv endorsement policy change 2026 first-time submitters institutional email
2. arXiv cs review articles position papers peer review requirement October 2025
3. arXiv policy generative AI language tools authors
4. Experimental Mathematics journal aims and scope submission statement
5. Machin-type formulas 2023 paper arctangent relations classification
6. amateur mathematician published number theory journal independent researcher
7. arXiv one-year ban unchecked LLM content May 2026 policy hallucinated references
8. viXra reputation mathematicians alternative to arXiv Zenodo HAL independent researcher preprint
9. Mathematics of Computation AMS journal scope submission guidelines review time
10. Journal of Number Theory Elsevier guide for authors time to first decision article publishing charge
11. Ramanujan Journal BBP-type formulas paper
12. Research in Number Theory Springer journal article processing charge submission to first decision days
13. Integers Electronic Journal of Combinatorial Number Theory indexed MathSciNet Scopus no fees
14. Notes on Number Theory and Discrete Mathematics Scopus indexed quartile reputation
15. Journal of Integer Sequences Machin arctangent OR "BBP" formula pi paper
16. JOSS Journal of Open Source Software submission requirements scope research software AI usage policy 2026
17. ACM Transactions on Mathematical Software scope algorithm papers author guidelines replicated computational results
18. American Mathematical Society policy generative AI authors journals disclosure
19. Taylor & Francis AI policy authors generative AI disclosure authorship
20. Springer Nature AI authorship policy LLM documented methods section copy editing exemption
21. Elsevier generative AI policies for journals authors declaration 2025
22. Cambridge University Press AI contributions research publishing policy authorship declared
23. Wiley generative AI guidelines authors journals disclosure 2025
24. MathOverflow meta amateur asking for review of own paper proof policy "off-topic"
25. Henry Cohn advice for amateur mathematicians on writing and publishing papers
26. NMBRTHRY mailing list listserv number theory how to subscribe post announcement
27. how to recognize predatory mathematics journals checklist Think Check Submit Beall's list
28. academia.stackexchange publish mathematics paper without affiliation independent researcher journal accept
29. "Journal of Experimental Mathematics" new journal diamond open access launched
30. Zenodo preprint DOI timestamp establish priority mathematics GitHub release archive
31. Borwein Borwein Galway "Finding and excluding b-ary Machin-type" individual digit formulae Canadian Journal of Mathematics 2004 open question
32. "amateur mathematician" paper published journal 2022 OR 2023 OR 2024 OR 2025 number theory proof accepted peer-reviewed
33. American Mathematical Monthly submission guidelines acceptance rate article length AI policy
34. International Journal of Number Theory World Scientific submission guidelines open access fee scope
35. Integers journal combinatorial number theory instructions for authors LLM generative AI policy referee time
36. Experimental Mathematics Taylor Francis editorial board resigned 2023 current status journal article publishing charge
37. arXiv math endorsement how many papers endorser needs math.NT "endorsement domain" independent researcher experience 2026
38. HAL open archive deposit without institutional affiliation independent researcher moderation mathematics
39. Terence Tao career advice "submit to an appropriate journal" OR "don't prematurely obsess on a single big problem" amateur famous problems advice
40. Zenodo general policies who can upload content accepted preprints DOI versioning license no affiliation required
41. Journal of Number Theory journal insights submission to first decision weeks acceptance rate "JNT Prime" computational section

Attempted but not executed (budget exhausted):

42. AMS journals "Use of Artificial Intelligence" policy "AI tool" "cannot be listed as an author" manuscript must state
43. Indagationes Mathematicae aims scope Royal Dutch Mathematical Society open access charge review time
44. Canadian Journal of Mathematics Canadian Mathematical Bulletin submission page length review time open access fee
45. Involve journal of mathematics student coauthor requirement; Rose-Hulman Undergraduate Mathematics Journal eligibility undergraduate authors
46. ISSAC 2027 call for papers symbolic algebraic computation submission deadline

Total distinct searches run: 41 (minimum required for this thread: 18).
