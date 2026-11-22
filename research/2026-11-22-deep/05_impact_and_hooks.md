# Impact and hooks: who would care about the binary degree-1 BBP classification

Date: 2026-11-22. WebSearch calls used: **27 of 28** (two of them returned an error for a blocked domain; counted anyway). WebFetch calls were unlimited.

Marking convention
- **[READ]** = I opened the page or PDF. Where I saved a PDF and extracted its text with pdftotext (Lagarias, Bailey compendium, Sze, Bailey-Borwein), I read the text myself. Pages fetched through WebFetch were summarised by a small model, so fine details carry that risk.
- **[SNIPPET]** = seen only in search-result text. Not verified.
- **[EARLIER]** = taken from the earlier report `research/2026-11-22/impact_on_other_work.md` (where it was marked as read there); not re-opened in this session.
- Quotes are at most 15 words. "Consequence" and "might interest" are kept apart.

---

## Summary (10 lines)

1. y-cruncher verifies pi records by running a BBP digit extractor to the matching hexadecimal offset; the bundled extractor supported Plouffe's and Bellard's formulas, and from v0.8.4/0.8.5 (2024) Huvent's [READ/SNIPPET, see Q1].
2. Cost is compared by measured run time (hours, seconds per CPU build), not by a term-count theory. Nobody I found claims or asks for a provably fastest formula, except Bellard's own 1997 "open question" remark [READ].
3. IMPORTANT caveat for our optimality claim: Takahashi (Ramanujan J. 2020) reports two new BBP-type formulas using about 20% fewer terms than Huvent's formula in a shifted-start verification scheme [SNIPPET]. I could not open the paper. Check this before claiming "2/3 is optimal and only Huvent attains it" without qualification.
4. Far-bit records: PiHex (2000), Yahoo/Sze (2010, Bellard's formula, read), Karrels GPUs (2013, Bellard reported in a snippet), Takahashi (2016, 10^17-th hex digit, Bellard, read).
5. Normality: Hypothesis A (Bailey-Crandall 2001) is unproven and described as likely intractable. A classification of formulas has no stated consequence for it. I found no 2015-2026 progress.
6. Explicit open questions exist but are few: Bellard (faster formula?), Bailey (arctan(2/7), which primes, zero relations "mysterious"), BBG problems (2), (3), (10), Zudilin (other bases), Lagarias (two-base question), Tijdeman ("is S rational?").
7. No complete classification of n-term Machin formulas exists. Two-term cases are classified by Gaussian-integer factorisation (Størmer; Gasull-Luca-Varona 2023); three-term finiteness by Yamada. Our Baker-hypothesis method is different and does not appear in that literature.
8. Media: I found no Numberphile / Stand-up Maths / Mathologer / 3Blue1Brown / Quanta / New Scientist piece on BBP itself. Coverage of Plouffe's 2022 formula (IFLScience) and 2026 "AI does math" stories are plentiful.
9. 2026 AI-math coverage centres on amateurs plus public LLMs (Erdős problems), with Lean as an auditing step; Lean experts (Buzzard, Tao) stress statement fidelity and disclosure of AI use.
10. Most promising hook: a clean, self-contained statement (Bellard's open question + Bailey's mysterious zero relations), posted on arXiv with a Lean repository that passes a Comparator-style check, with honest disclosure that Baker's theorem is a hypothesis.

---

## Q1. Record computations of pi: verification, formulas, cost, "provably fastest"

**How y-cruncher verifies.**
- Records page [READ, https://numberworld.org/y-cruncher/records.html]: a pi record needs no second full computation if the main run uses the built-in Chudnovsky or Ramanujan formula in swap mode with hexadecimal digits, digit output and "Verify Output" enabled, and a BBP run to the matching hex offset reproduces the last hex digits. The page says BBP is much faster than the main computation. The current record listed is 314 trillion digits (StorageReview, finished 19 Nov 2025, announced 11 Dec 2025). The page does not say which BBP formula was used for that record.
- Programs page [READ, https://numberworld.org/programs/]: the stand-alone y-cruncher BBP (v1.0, April 2010) was written for verifying the 5-trillion-digit record. It offers Plouffe's and Bellard's formulas; v1.0 benchmarks show Bellard faster at large positions (e.g. 12.95 h vs 18.50 h at the 100-billion position on a Pentium D). v2.0 gives times in seconds per instruction-set build (SSE3 to AVX2). Superseded by the version built into y-cruncher.
- 2024 news page [READ, https://numberworld.org/y-cruncher/news/2024.html]: BBP is a formal benchmark from v0.8.5 (no memory, embarrassingly parallel); the 105-trillion-digit run was checked by a 4-day BBP verification. The page does not mention Huvent.
- Version history [EARLIER; also a search snippet this session]: v0.8.4.9537 (Feb 2024) added Huvent's formula, "slightly faster than Bellard's"; v0.8.5.9539 made it the default.
- Algorithms page [READ, https://numberworld.org/y-cruncher/algorithms.html]: bundled "BBPv2" app, hexadecimal offset limit 2^46 - 1 (an implementation limit). No verification theory.
- 10-trillion run [SNIPPET]: Bellard's BBP took 1.86 days as primary check, Plouffe's 4.94 days as secondary.

**How cost is compared.** By wall-clock time on specific CPUs [READ], and by a rough count of terms or divisions per bit. Wikipedia's BBP page [READ] quotes "30 binary digits per 21 divisions" for Euler's second formula versus Bellard's "10 per 7" (both are 0.7 divisions per bit; the page calls them tantamount). Bellard's page [READ, https://www.bellard.org/pi/pi_bin/pi_bin.html] claims his formula is 43% faster than BBP. No benchmark of Huvent against Bellard found.

**Has anybody claimed or asked for a provably fastest formula?**
- Bellard (1997): says whether a still faster formula exists is an open question [READ]. This is the only explicit request I found.
- Takahashi, "On the computation and verification of pi using BBP-type formulas", Ramanujan J. 51 (2020) 177-186 [SNIPPET only]: proposes two BBP-type formulas needing about 20% fewer terms than Huvent's formula used with a shifted starting position, and calls Huvent's formula the previous record holder for fewest terms. **This competes with, or at least must be reconciled with, our optimality statement.** Possible explanations (all unverified): a different cost model (shifted start, verifying a block of digits), a formula outside the class (different structure, not 2^(-floor(k/2))/k with periodic rho), or a count that includes shared terms. I could not open the paper (Springer redirected to a login page).
- Takahashi's own computation page [READ, https://www.hpcs.cs.tsukuba.ac.jp/~daisuke/pihex.html] shows Bellard's formula in both runs of the 10^17 hex-digit record and says nothing about newer formulas.
- Forum posts / Stack Exchange / mersenneforum on "fastest BBP formula": **not found.** Two attempts with domain filters failed (blocked domain error) and two unfiltered searches returned no forum thread. A 2000 Usenet thread about whether a decimal-digit algorithm can match BBP [SNIPPET, python-list 2000] is a different question.

**Would a proof of optimality interest this community?** Consequence: it would settle Bellard's 1997 question inside the class and justify the choice of Huvent in y-cruncher. Might interest: the y-cruncher author and Takahashi-type verifiers, because verification time matters for records. Counterweight: BBP runs are already short compared with the main computation (records page [READ]), the practical gain over Huvent is a modest percent, and no one posted a request. Interest is therefore "might", not "will".

## Q2. Individual-bit records

| Record | Who, when | Formula, cost model | Status |
|---|---|---|---|
| 10^9-th bit (152 bits) | Bellard, 1997 | Bellard's formula; 12 days on 20+ workstations, 180 CPU days | [READ, Sze 2010 text] |
| 5e12, 4e13, 1e15-th bit | PiHex (Percival), 1998-2000 | BBP-type; 1734 machines in 56 countries, 250 CPU-years (per Sze). Formula not named on the pages I opened | [READ] cost; formula [not found] |
| 2e15-th bit | Yahoo / Sze, 2010 | Bellard's formula (equation 1.2 in the paper); 23 days on a 1000-node cluster, about 503 CPU-years; two runs at n and n-4, only agreeing bits accepted | [READ, full text] |
| 8e15-th bit | Karrels, 2013 (Pi Day) | GPUs (CUDA, GTX 570s); a Japanese report says Bellard's formula | [SNIPPET] |
| 10^17-th hex digit | Takahashi, 2016 | Bellard's formula in both runs; Oakforest-PACS | [READ] |

Cost model in Sze's paper [READ]: number of terms is linear in n; each term is a modular exponentiation plus a floating-point division; the running time is quoted as O(p(n^(1+eps)+p)) bit operations for p-bit precision. So "terms per bit" is a reasonable proxy there, but implementation details (GPU, modular arithmetic) dominate in practice. Bellard's page [READ] gives the 1000-billionth binary digit (Sept 1997) and PiHex's 10^15 record but no formula for PiHex. I did not find a "100-quadrillionth bit" record other than Takahashi's 10^17 hex digit (about 4x10^17 bits) [READ].

## Q3. Normality and Hypothesis A

- Definition and status [READ, Lagarias, Experimental Math. 10 (2001), full text]: BBP-number to base b = sum p(n)/q(n) b^(-n) with integer polynomials. Bailey-Crandall's Hypothesis A implies such a number is rational or normal to base b. Lagarias says proving it "appears intractable". He relates it to G-functions and Furstenberg's conjecture and notes no known relation to Furstenberg in either direction.
- Lagarias asks whether all BBP-numbers that are special values of G-functions have BBP-expansions in two multiplicatively independent bases [READ]. He observes log 2 (bases 2 and 32) and pi^2 (bases 2 and 34, Broadhurst) have two-base expansions, and suggests constants with two-base expansions as the smallest class where Hypothesis A may be natural [READ]. Bailey's compendium repeats this as "special significance" for two-base constants [READ].
- Bailey-Borwein survey [READ, https://www.davidhbailey.com/dhbpapers/normality-digits-pi.pdf, text extracted]: no proof of the hypothesis is known, "even proofs in specific instances would be quite interesting". Gives the two concrete iterations (for log 2 and for pi) whose equidistribution would give normality.
- 2015-2026 developments: **none found.** A 2016 Adegoke paper treats normality as open [SNIPPET]; Barsky-Munoz-Perez-Marco (2023 version) still lists normality of pi as open [SNIPPET]; a recent Zenodo preprint "Nest, Run, Fold" on the Bailey-Crandall recurrence exists [SNIPPET, not peer reviewed; page returned HTTP 410 when I tried to open it]. I treat it as unreliable.
- **Consequence for us:** none stated anywhere. Hypothesis A concerns the dynamics of a given expansion, not which constants have formulas. 
- **Might interest:** (a) Lagarias's "two bases" class: our result that pi has no degree-1 formula in some bases would be a negative statement about membership in that class, if extended to non-binary bases (not done). (b) "log 23 has no binary formula" tells us log 23 is outside the degree-1 binary BBP-number class, so Hypothesis A would not say anything about its binary normality via this route. That is a boundary statement, not a normality result.

## Q4. Open questions in Bailey's compendium and the BBP literature

See the table below. Notes on the specific items asked about:

- **arctan(2/7):** Bailey says it is not known whether it has a binary BBP formula [READ, compendium text]. Our method plausibly reaches it (Z[i], 7+2i has norm 53) [EARLIER, inference].
- **Base-3 formula for pi:** none exists in the compendium's ternary section (its pi-related ternary items are for 3*arctan, pi*sqrt(3), pi^2 and logs) [READ]. A search summary says Galway showed no degree-1 formula for pi exists in non-power-of-2 bases [SNIPPET]. **Careful:** the earlier report [EARLIER] read BBG itself and found they prove it only for Machin-type generators; the "no degree-1 formula in any base not a power of 2" statement in Bailey's compendium looks like a folklore upgrade. A full proof for general degree-1 is not found. Higher degree: pi^2 has a ternary formula (Formula 76) [READ], so degree matters.
- **Base 10:** the compendium has log(10/9)-type formulas in base 10 (degree 1) [READ]. For pi, Zudilin's "base 5" paper (earlier title said base 10 [SNIPPET]) is a joke-flavoured proposal with an "obvious flaw" [EARLIER].
- **Golden-ratio base:** formulas for pi^2 in golden-ratio base: Cloitre arXiv 2508.03743 [EARLIER, abstract]; Adegoke golden-ratio work cited in the compendium [READ]. Not in our class.
- **Catalan's constant (degree 2):** compendium credits Adegoke with a binary formula [EARLIER/READ list of references]; Broadhurst's 1998 ladders paper proves Catalan, zeta(3), zeta(5) have BBP-type formulas [SNIPPET]. No stated open question found. Degree >= 2 is out of reach of Baker-type input [EARLIER].
- **zeta(3), zeta(5) (Broadhurst):** zeta(5) has a 22-term binary BBP-type formula (Broadhurst eq. 72) [SNIPPET, from a 2024 arXiv paper]. No stated open question found.
- **pi^2:** binary and ternary formulas exist [READ].

### Open questions stated in the literature

| Question | Source | Year | Could the method apply? | Why |
|---|---|---|---|---|
| Does a still faster formula than Bellard's exist for the n-th binary digit? ("remains an open question") | Bellard, pi_bin page [READ] | 1997 | **Yes (answered inside the class)** | Our optimum 2/3 is a statement about terms per bit in the class; not about formulas outside it (see Takahashi caveat) |
| Is arctan(2/7) given by a binary BBP formula? ("not known") | Bailey compendium [READ] | 2023 version | **Yes** | Needs the Z[i] part only; same exclusion argument as for log 23 |
| Which primes p have a binary BBP formula for log p? Finite or infinite? | Bailey compendium [READ] | 2023 version | **Yes** (finite check for p < 100 done; infinite question needs structure) | Our classification gives the criterion; global answer needs number theory of ord_2(p) |
| Does log 23 have a binary formula? | Chamberland 2003 [EARLIER] | 2003 | **Yes (answered: no, with Baker as a hypothesis)** | Already our Theorem G |
| Why do zero relations occur for some (s, b, n) only? ("not understood") | Bailey compendium section 12 [READ] | 2023 version | **Yes for s = 1, b = 2^B; no for s >= 2** | Baker covers logs, not higher polylogarithms |
| How many Q-independent binary Machin-type zero relations exist; bounds? (Problem 2) | Borwein-Borwein-Galway [EARLIER] | 2004 | **Yes (answered for arctans in base 2)** | Our dimension count |
| Simple derivation of the original BBP from a Machin-type combination? (Problem 3) | BBG [EARLIER] | 2004 | **Maybe** | Our 8-dim space gives structure; a "derivation" is a different request |
| Decide if pi is a combination of L(1, b^m, n, j) for fixed b (Problem 10) | BBG [EARLIER] | 2004 | **Yes for b = 2; maybe for others** | Needs Q(zeta_n, b^(1/n)) and effective Zsigmondy over number fields (Problem 7) |
| Do BBP-numbers that are special values of G-functions have BBP expansions in two independent bases? | Lagarias [READ] | 2001 | **No** | About existence in two bases, not exclusion; our method only excludes |
| Does Hypothesis A hold / is any BBP-number normal? | Bailey-Crandall; Lagarias; Bailey-Borwein [READ] | 2001-2013 | **No** | Dynamical statement; no link to classification |
| Is there a working BBP-style algorithm for pi in base 5 / over Q(i)? ("An obvious flaw") | Zudilin, arXiv 2409.10097 [EARLIER] | 2024 | **Maybe** | We could say whether a rational-coefficient degree-1 formula exists with Gaussian generators; the "flaw" is a convergence issue, not independence |
| Is S = sum alpha^n P(n)/Q(n) rational when algebraic? | Tijdeman survey [EARLIER] | 2001+ | **Maybe** | Our setting is alpha = 2^-B, linear denominators |
| Are there two-term Machin-like formulas with Lehmer measure as small as we want? | Gasull, Luca, Varona, arXiv 2302.00154 [READ] | 2023 | **No** (they answer it) | Different problem; Gaussian factorisation, not linear forms |
| Classification of all N-term Machin formulas for N > 2 | same paper says its method is "not enough in general" [READ]; Yamada proves finiteness for three terms [READ abstract] | 2023, 2025 | **Maybe** | See Q5 |
| Is pi given by a ternary (base 3) degree-1 formula? | Not stated as an open question anywhere I read; compendium lists none [READ] | n/a | **Maybe** | Needs Eisenstein / Q(zeta_3) analogue; BBG only exclude Machin-type generators |
| Which degree 2-4 zero relations / formulas exist (Table 1 of compendium)? | Bailey compendium [READ] | 2023 version | **No** | Needs independence of polylogarithms of order >= 2 |

(Wording is paraphrased except for the short quotes shown. I did not find explicit open-question statements for Catalan's constant, zeta(3) or zeta(5) in the BBP literature.)

## Q5. Related areas: Machin-type formulas, ladders, Mahler measure

- **Størmer and two-term formulas.** Wikipedia [READ]: with all numerators 1 there are exactly four two-term solutions (Machin era); Størmer's 1896 and 1899 papers give complete solutions for two terms and his 1897 paper applies complex-integer theory. A MathWorld/CRC snippet says Machin-like formulas exist iff a product of Gaussian-integer factors equals a power of (1-i) [SNIPPET]. A Størmer criterion (necessary and sufficient, for given integers) is reported in a snippet from the Gasull-Luca-Varona paper [SNIPPET].
- **Gasull, Luca, Varona, Indag. Math. 2023, arXiv 2302.00154** [READ, ar5iv text via WebFetch]: classify two-term Machin-type formulas with arguments b/2^a (ten sporadic ones plus two parametric families) and with powers of the golden section. Method: rewrite as equality of powers of (1 +/- i z_k), factor in Z[i], reduce to exponential Diophantine equations such as x^2+1 = 2y^n and x^2+2^a = y^n using known solution lists, then finite computer checks; primitive divisors for Fibonacci/Lucas in the golden case. The summary I read did not mention Baker or linear forms in logarithms. They say their N-term method does not cover all N > 2.
- **Yamada, arXiv 1811.09273 (v6, 2025)** [READ abstract]: only finitely many nondegenerate three-term Machin-type formulas; explicit bounds. Method not read.
- **Lehmer measure, Todd, Wetherfield, Chien-Lih** [READ, Wikipedia]: smallest known Lehmer measure about 1.51244 (Chien-Lih 1997); Todd's process refines formulas; Wetherfield 2016 Gazette article. These are search-and-construct results, not classifications. Wikipedia lists no open-problems section.
- **Is a complete n-term classification over Gaussian integers known?** **Not found.** Two terms: yes (Størmer, with Gaussian integers; plus Gasull et al. for restricted arguments). Three terms: finiteness only. General n: nothing found.
- **Relevance to our method.** Our result classifies Q-linear relations among arctan/log generators for a fixed base 2 using Baker plus primitive divisors. Machin formulas ask for relations among arctan(1/b) with arbitrary b. A Baker-type approach for "which finite sets of Gaussian integers satisfy a Q-linear relation" would be an analogue, but I found no literature doing it. That is an opportunity and also a warning: I could not confirm novelty beyond my searches.
- **Polylogarithm ladders** [SNIPPET + abstracts]: Cohen-Lewin-Zagier (1992) 16th-order ladder; Bailey-Broadhurst (1999) 17th-order ladder found with PSLQ; Gangl (2010, 2014) proves some ladders using new functional equations; Zagier's criterion for functional equations. Relevant link: Bailey's compendium cites Broadhurst's "Vanishing Polylogarithmic Ladders" [READ, reference list]. Ladders concern order >= 2, so our Baker-based degree-1 method does not apply; no linear-independence classification found.
- **Mahler measure / cyclotomic numbers** [SNIPPET]: Baker's theorem is used to approximate Mahler measure; van der Poorten-Loxton on multiplicative relations. **No source found** for a complete classification of Q-linear relations among logarithms of numbers 1 - zeta*x. This is the closest published-gap statement I can offer, and it is an absence-of-evidence claim only.

## Q6. Media coverage and angles

| Outlet | What I found | Angle | Status |
|---|---|---|---|
| Numberphile | Pi category page showed no BBP episode | none | [SNIPPET, absence] |
| Stand-up Maths (Matt Parker) | Pi videos are about calculating pi by hand; none about BBP found | "hand computation, comedy" | [SNIPPET] |
| Mathologer, 3Blue1Brown | Nothing on BBP found | none | [not found] |
| Quanta, New Scientist | No BBP / digit-extraction piece found | none | [not found] |
| Hacker News | No thread found by search | none | [not found] |
| IFLScience, 20 Jan 2023 | Plouffe's decimal-digit formula | "established mathematician; formula works in any base; impractical" | [READ] |
| John D. Cook blog, 14 Mar 2025 | Explains BBP digit extraction | explainer | [SNIPPET] |
| MetaFilter Ask thread | "Formula that only works in some bases" | curiosity | [SNIPPET] |

"AI proves math" coverage 2026:
- Scientific American, 24 Apr 2026 [READ]: 23-year-old amateur (Liam Price) solves Erdős problem #1196 with GPT-5.4 Pro; Tao and Lichtman shorten the proof. Angle: amateur plus LLM; expert verification; no Lean mentioned.
- Quanta, 3 Aug 2026, "How AI tore through a mathematical community" [READ]: Erdős problems as a test bed; erdosproblems.com forum is the venue; errors caught (a problem already solved in 1977); amateurs credit the AI; Bloom warns of unread 100-200 page papers; Alon and Gowers quoted.
- Quanta, April 2026, "The AI Revolution in Math Has Arrived" [SNIPPET]: tipping point summer 2025; Lean as verification, with caveat that Lean statements need human checking.
- Science News, Smithsonian, Physics World, heise, TechCrunch (Jan 2026) [SNIPPET]: Erdős problem stories.
- Terence Tao's blog, 9 Oct 2026 [READ]: what mathematicians should know about Lean reliability; soundness bugs found in summer 2026 and fixed; advice to disclose AI use and not claim AI-generated Lean alone establishes an argument.
- Xena Project (Buzzard), 12 Nov 2026 [READ]: four checks for any Lean repository (statement, compilation, proof fidelity with `lake comparator`, kernel exploits).
- Nov 2026 Riemann-hypothesis claim attributed to an Anthropic researcher: reported by OfficeChai (20 Nov 2026) [READ: a website note with Lean code and no paper; mixed reactions], Wikipedia list [READ: internally inconsistent about "verified" vs "review pending"], and search snippets claiming a Lean community statement [SNIPPET]. **I could not corroborate this from a primary source and I do not rely on it.** It matters only as context: the market for "AI + Lean" stories is currently crowded and sceptical, with attention on statement fidelity.

## Q7. Precedents: hobbyist + AI + Lean accepted by experts, 2025-2026

- **Erdős #728** [READ, arXiv 2601.07421]: single-author write-up by Nat Sothanaphan; GPT-5.2 Pro produced the argument and Aristotle (Harmonic), operated by Kevin Barreto, produced the Lean proof (Jan 2026). Presented as arXiv paper with Lean proof; the page names no external verifier. [SNIPPET: Tao's wiki records it as first near-autonomous solution.]
- **Erdős #1196** [READ via SciAm and Quanta]: Price/Barreto posted on erdosproblems.com; Tao and Lichtman reviewed and shortened; arXiv paper in May 2026 with Lean verification [SNIPPET].
- **Tao's AI-contributions wiki** [READ]: about 150 primary rows; section 1(d) "AI collaborating with humans" about 140; green (full) entries for independent contributors (e.g. #42, #283, #351, #330, #202, #863, #603, #1151, #865). Venue: erdosproblems.com problem pages; wiki does not state arXiv/GitHub per result.
- **Wikipedia list of AI discoveries** [READ]: Sendov's conjecture (Mazur, Aug 2026, Tao streamlined with shorter Lean version); Erdős 4 by pseudonym "DottedCalculator" posted on GitHub; Adamczewski Lean results mostly on GitHub; Lamzouri reviewed a zeta-zeros improvement.
- **Lean + transcendence**: Gelfond-Schneider formalised in Lean 4 by Karatarakis and Wiedijk (2026) [SNIPPET]; Baker-Wüstholz appears as a statement in the Lean community evaluation set [SNIPPET], so Baker's theorem is a problem statement there, not (as far as I can see) a proven Mathlib theorem. That supports presenting Baker as an explicit hypothesis, and invites a reader to ask whether the hypothesis is the proved theorem or a weaker one.
- **Presentation pattern that worked:** a public forum thread or GitHub repository, an expert who reads and simplifies, and (increasingly) Lean checked with statement and axiom checks. I found no case of a pure-hobbyist Lean number-theory result accepted without a named professional reading it. Lean Zulip: not found by search.

## Honest assessment of what would get attention

Consequences (what the result actually settles, within the class):
- Bellard's 1997 question about a faster formula, inside binary degree 1.
- Bailey's "zero relations are mysterious" for s = 1 binary.
- The list of primes p < 100 with binary log p formulas, including a negative result for 23, conditional on Baker.

Things that might interest, but are not consequences:
- y-cruncher and Takahashi-type verifiers; but the speed gain over Huvent is small, and a published 20% claim (Takahashi) must be reconciled first.
- Lagarias/normality circle: only as a boundary statement.
- Machin-formula community: only if the method yields a new classification statement there; unproven.

Likely reception:
- A number-theory or experimental-mathematics audience (Bailey, Borwein's students, Adegoke, Galway, Zudilin, Takahashi) is the realistic readership. A short arXiv note titled around "complete classification of binary degree-1 BBP formulas" with explicit tables would be understandable to them.
- General media attention is unlikely for the mathematics alone. The 2026 "AI does math" story is saturated, so "amateur + AI + Lean" is not a new angle by itself; what would count is clean Lean statement checks, explicit AI disclosure, and a verifiable, narrow claim. A hobbyist label may help human-interest coverage but also invites the scepticism Tao and Buzzard describe.
- The conditional nature (Baker as hypothesis) is the weak point; experts will ask for the exact statement of the hypothesis and whether it is a known theorem. State it as the Baker-Wüstholz/Baker theorem for linear forms in logarithms with the exact number field and exponents used.

Three most promising leads:
1. Reconcile with Takahashi 2020 (get the paper from the author or arXiv; his formulas may sit outside the class), then state the optimality claim precisely.
2. Post a short arXiv note plus Lean repo, with a Comparator-style statement check and explicit AI disclosure, and send it to Bailey, Zudilin, Takahashi, and to the y-cruncher author.
3. Extend to arctan(2/7) and non-binary degree-1 (base 3, 5) as the next stated open questions (BBG Problem 10, Zudilin's base-5 question), since these are the ones the literature explicitly asks.

## Queries used (WebSearch, 27 calls)

1. Bailey Crandall "Hypothesis A" BBP normality binary expansion random numbers chaotic
2. y-cruncher BBP digit extraction Huvent formula Bellard faster hexadecimal verification pi record
3. fastest BBP-type formula for pi optimal digit extraction mersenneforum OR stackexchange
4. mersenneforum BBP formula pi hexadecimal digit extraction Bellard Huvent faster
5. Takahashi "BBP-type formulas" computation and verification of pi hexadecimal digits
6. Takahashi Ramanujan Journal 2020 new BBP-type formulas pi fewer terms than Huvent arXiv
7. PiHex Colin Percival quadrillionth bit of pi computation Bellard formula 1998 2000 distributed
8. normality of pi BBP-type constants Hypothesis A progress 2020 2024 2025 arXiv base 2 normal numbers digit extraction (extended)
9. Karrels GPU eight quadrillionth bit of pi BBP Bellard formula CUDA
10. does pi have a BBP-type formula in base 3 ternary open problem Adegoke Broadhurst
11. classification of all Machin-like formulas arctangent relations Gaussian integers Stormer theorem primitive prime factors two-term
12. polylogarithm ladders Lewin Cohen Zagier Broadhurst "vanishing" ladders linear independence logarithms cyclotomic units classification
13. Mahler measure multiplicative relations cyclotomic numbers 1 - zeta linear forms in logarithms Baker complete classification relations among logs of cyclotomic numbers
14. Numberphile OR Mathologer OR "Stand-up Maths" OR 3Blue1Brown video BBP formula compute any digit of pi without previous digits
15. Quanta Magazine OR "New Scientist" pi digits BBP formula Plouffe Bellard digit extraction article
16. Hacker News BBP formula pi hexadecimal digit extraction discussion
17. AI proves theorem Lean formalized amateur hobbyist 2026 mathematicians react arXiv (extended)
18. Erdos problems solved by AI GPT Aristotle Harmonic Lean formal proof amateur Terence Tao 2026 (extended)
19. Quanta Magazine 2026 AI mathematics proof Lean formalization mathematicians
20. New Scientist 2026 AI solves maths problem amateur Erdos
21. BBP formula pi digits (domain filter; returned an error, no results; counted)
22. Broadhurst zeta(5) BBP-type formula base 2 degree 5 open Catalan constant degree 2 BBP formula
23. BBP formula pi hexadecimal digits Bellard Huvent (domain filter; returned an error, no results; counted)
24. Matt Parker Stand-up Maths pi digits video Bailey Borwein Plouffe spigot
25. "BBP" normal numbers 2-normal proof constants digit extraction recent arXiv 2023 2024 2025 Bailey Crandall hypothesis chaotic maps equidistribution (extended)
26. independent researcher AI Lean formalized result number theory accepted mathematicians Lean Zulip announcement GitHub repository 2026 (extended)
27. Baker's theorem linear forms in logarithms formalization Lean Mathlib Gelfond-Schneider formalized

## Sources

- [y-cruncher records](https://numberworld.org/y-cruncher/records.html)
- [y-cruncher programs (BBP v1.0, v2.0)](https://numberworld.org/programs/)
- [y-cruncher news 2024](https://numberworld.org/y-cruncher/news/2024.html)
- [y-cruncher algorithms](https://numberworld.org/y-cruncher/algorithms.html)
- [y-cruncher version history](https://numberworld.org/y-cruncher/version_history.html)
- [Bellard, binary digits of pi](https://www.bellard.org/pi/pi_bin/pi_bin.html)
- [Bellard, pi_hexa records](https://www.bellard.org/pi/pi_hexa.html)
- [Sze 2010, two quadrillionth bit (arXiv 1008.3171)](https://arxiv.org/abs/1008.3171)
- [Takahashi 10^17 hex digit page](https://www.hpcs.cs.tsukuba.ac.jp/~daisuke/pihex.html)
- [Takahashi, Ramanujan J. 2020 (catalogue entry, snippet)](https://bvbvf1.bib-bvb.de/vufind/PrimoRecord/cdi_proquest_journals_2332363489)
- [Karrels GPU record (TechRadar, snippet)](https://techradar.com/news/computing-components/graphics-cards/nvidia-gpus-help-pi-researcher-calculate-eight-quadrillionth-place-1138118)
- [PiHex (Wikipedia, snippet)](https://en.wikipedia.org/wiki/PiHex)
- [Wikipedia: BBP formula](https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula)
- [Bailey, compendium of BBP-type formulas](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)
- [Bailey-Borwein, Normality and the digits of pi](https://www.davidhbailey.com/dhbpapers/normality-digits-pi.pdf)
- [Lagarias, On the normality of arithmetical constants](https://arxiv.org/abs/math/0101055)
- [Barsky, Munoz, Perez-Marco, On the genesis of BBP formulas](https://arxiv.org/abs/1906.09629)
- [Adegoke, binary BBP-type for polylogarithm constants (snippet)](https://arxiv.org/pdf/1603.05810)
- [Broadhurst, polylogarithmic ladders, zeta(3), zeta(5) (snippet)](https://arxiv.org/pdf/math/9803067)
- [Zudilin, BBP-style computation for pi in base 5](https://arxiv.org/abs/2409.10097)
- [Gasull, Luca, Varona, Machin-type formulas](https://arxiv.org/abs/2302.00154)
- [Yamada, three-term Machin-type formulae](https://arxiv.org/abs/1811.09273)
- [Wikipedia: Machin-like formula](https://en.wikipedia.org/wiki/Machin-like_formula)
- [Bailey-Broadhurst, 17th-order ladder (snippet)](https://arxiv.org/abs/math/9906134)
- [IFLScience on Plouffe's formula](https://www.iflscience.com/there-s-a-formula-to-calculate-any-digit-of-pi-and-nobody-noticed-for-centuries-67178)
- [Scientific American, amateur and Erdos problem](https://scientificamerican.com/article/amateur-armed-with-chatgpt-vibe-maths-a-60-year-old-problem)
- [Quanta, How AI tore through a mathematical community](https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/)
- [Quanta, The AI revolution in math has arrived (snippet)](https://quantamagazine.org/the-ai-revolution-in-math-has-arrived-20260413/)
- [Tao, What mathematicians should know about Lean](https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/)
- [Xena Project, and the proof is checked in Lean](https://xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/)
- [Tao's wiki: AI contributions to Erdos problems](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)
- [Resolution of Erdos Problem #728 (arXiv 2601.07421)](https://arxiv.org/abs/2601.07421)
- [Wikipedia: list of mathematical discoveries made with AI](https://en.wikipedia.org/wiki/List_of_mathematical_discoveries_made_with_artificial_intelligence)
- [OfficeChai on the Riemann-hypothesis claim (context only)](https://officechai.com/ai/how-mathematicians-have-reacted-to-claimed-riemann-hypothesis-proof-by-anthropics-levent-alpoge/)
- [Lean eval: Baker-Wustholz statement (snippet)](https://lean-lang.org/eval/problems/bakerWustholz_linearForms_logs/)
- [Gelfond-Schneider in Lean, Karatarakis-Wiedijk (snippet)](https://arxiv.org/html/2603.24823v1)
- Earlier report: `research/2026-11-22/impact_on_other_work.md` (BBG, Tijdeman, Chamberland, Cloitre, Kristensen-Mathiasen sources are listed there)
