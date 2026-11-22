# State of prime number research as of 21 November 2026, with a view to amateur + AI + one-laptop contributions

Reader warnings before anything else:

- **Everything dated 2026 below comes only from web pages fetched in this session** (arXiv listings, Wikipedia, Quanta, Scientific American, Science News, the Lean community blog, an MIT verification page, Tao's blog, project pages). I could not cross-check any of it against prior knowledge. Items from August to November 2026 are especially fresh, and the Riemann Hypothesis claim is one day old on the date of writing.
- Status labels used: **[peer-reviewed]**, **[preprint]**, **[press/blog]**, **[project page]**, **[formal-check claim]** (a Lean proof that named people say they compiled and kernel-checked, with no journal review).
- The shared web-search budget ran out after 29 executed searches (4 more were refused). Later material was gathered by fetching known primary URLs directly. Gaps caused by this are listed under each question.
- Statements by named people are paraphrased, not quoted.

---

## 1. Famous open problems and their status (RH, twin primes and bounded gaps, Goldbach, Legendre, Landau's problems, Guth-Maynard, Artin, Mersenne/Wieferich infinitude)

### Takeaway
As of 21 November 2026 the landscape is in upheaval: a 17-million-line Lean proof of RH and of GRH for Dirichlet L-functions was released on 20 November 2026 and the Lean and Mathlib communities say they are fully confident in it, but there is no human-readable proof, no peer review, and some kernel checks were still running. Twin primes, binary Goldbach, Legendre, n^2+1, and the infinitude of Mersenne and of Wieferich primes all remain open, and every one of them is out of reach for an amateur; the 2026 advances came from frontier AI labs or specialists.

### Cited Findings

**Riemann Hypothesis**
- Numerical verification: Platt and Trudgian verified RH up to height 3,000,175,332,800, covering the lowest 12,363,153,437,138 zeros, using interval arithmetic. Published in Bull. London Math. Soc. 2021. **[peer-reviewed]** No later extension of the height was found. — [arXiv:2004.09765](https://arxiv.org/abs/2004.09765v1)
- Proportion of zeros on the critical line, history: Levinson 1/3 (1974), Conrey 2/5 (1989), Pratt-Robles-Zaharescu-Zeindler 5/12 (2020). — [Wikipedia: Riemann hypothesis](https://en.wikipedia.org/wiki/Riemann_hypothesis)
- August 2026: Alpöge and Furman, "More than two thirds of the zeta zeros are simple and on the critical line". Unconditionally at least 2/3 of nontrivial zeros are simple and on the line (0.6725 with the Montgomery-Taylor window), and at least 5/6 are distinct. The arXiv comment attributes the discovery of the proof to Claude working autonomously, with the two authors verifying and communicating it, and says a Lean 4 formalization exists. **[preprint + formal-check claim]** — [arXiv:2608.13637](https://arxiv.org/abs/2608.13637)
- Anthropic's own account: an unreleased research Claude was asked to make a serious attempt at RH, failed, and produced the bound as a by-product; about 31 million output tokens, about 60 subagents over about a day and a half, 2,400 shell commands, thousands of numerical checks against known zeros. Anthropic states it is not a proof of RH and does not expect the techniques to lead to one. **[press/blog]** — [Anthropic: riemann-zeta](https://www.anthropic.com/news/riemann-zeta)
- Independent re-derivation: Lamzouri gave a different, simpler proof of the same 67.25% and 83.62% bounds via a single Hilbert space inequality, plus two new estimates (88.76% of zeros are simple or on the line). **[preprint]** — [arXiv:2609.02882](https://arxiv.org/abs/2609.02882)
- October 2026, "quasi-RH": OpenAI released two manuscripts. Version 1 (30 Sep 2026, 199 pages, Lean-verified) claims all nontrivial zeros have real part between 1/8 and 7/8. Version 2 (5 Oct 2026, 49 pages, the only one edited by a person, not formally verified at the time) claims the weaker strip 1/12 to 11/12. Quanta reports that experts largely accept the shorter argument; Radziwiłł said the papers were written so badly that a journal would reject them outright; Sarnak will not call it a theorem until humans have checked the details. **[press/blog + formal-check claim for the 7/8 version]** — [Quanta, 19 Oct 2026](https://quantamagazine.org/ai-proved-the-quasi-riemann-hypothesis-what-happens-now-20261019)
- Mild conflict: the Wikipedia RH page says the quasi-RH proof had not been independently verified as of October 2026, while Quanta reports broad expert acceptance of the 11/12 version. — [Wikipedia: Riemann hypothesis](https://en.wikipedia.org/wiki/Riemann_hypothesis)
- The same OpenAI release (6 Oct 2026, 722 manuscripts in 372 topics, roughly half with Lean proofs) also claims non-existence of Siegel zeros; Tao posted a sketch of that proof on 19 Oct 2026. Three papers were withdrawn within 24 hours (a sign error in algebraic-geometry papers, not primes) and 14 revised; some Lean formalizations prove weaker statements than the papers claim. **[press/blog]** — [Wikipedia: OpenAI bulk release](https://en.wikipedia.org/wiki/OpenAI_bulk_release_of_mathematical_papers); [Retraction Watch, 8 Oct 2026](https://retractionwatch.com/2026/10/08/openai-withdraws-preprints-722-manuscripts-unsolved-math-problems/)
- 20 November 2026: Levent Alpöge (Anthropic) posted a four-page note stating his belief that, working with Claude, he has found a proof of RH, backed by about 17 million lines of Lean and no human-readable proof (attempts to produce prose gave over 250,000 pages). Andrew Sutherland (MIT) compiled it first; Simon DeDeo also compiled it. Radziwiłł criticized the absence of understanding and said the note contains statements that make no sense. **[press/blog]** — [Quanta update, 20 Nov 2026](https://www.quantamagazine.org/update/169569/)
- 21 November 2026 joint statement of the Lean and Mathlib communities (endorsed by the Lean FRO and the Mathlib Initiative): they are fully confident the proof is correct, the theorem matches Mathlib's `RiemannHypothesis` definition, dozens of people reproduced the build, and the exported proof passed Lean's kernel and several independent checkers. It says the mathematical community still has to explain the ideas. **[formal-check claim]** — [Lean community blog](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)
- Sutherland's verification page (updated 21 Nov 2026, 12:55 UTC): five theorems, including RH and the statement that zeros of every Dirichlet L-function in the critical strip have real part 1/2. Scope is Dirichlet L-functions only; Dedekind, Hecke and automorphic L-functions are not covered. Axioms: `propext`, `Classical.choice`, `Quot.sound`. The export is 61.57 GB unpacked, 175,187 modules. nanoda accepted it in 27 min 42 s on 80 threads; con-leche in 3 min 15 s on 64 threads with about 50 GB RAM; a full check needs about 100 GB RAM. Lean's default and paranoid kernels and parts of `lake comparator` were still running. Robin's inequality (n > 5040) and Lagarias's inequality were already derived as unconditional Lean corollaries by a third party. **[formal-check claim]** — [math.mit.edu/~drew/grh](https://math.mit.edu/~drew/grh/)
- Tao's 20 Nov 2026 post describes it as a very large Lean-only proof of GRH produced with an internal AI model, says its strategy appears to draw on modern Langlands and arithmetic geometry, and that digesting it will take time. **[press/blog]** — [Tao's blog](https://terrytao.wordpress.com/)
- Same day, a competing human claim: Ravi Vakil posted Alessandro Masullo's 940-page manuscript claiming GRH, described as entirely human work; Brian Conrad had reviewed it for months; Masullo had an earlier RH attempt that did not hold up; many number theorists withhold judgment. Wikipedia adds that Vakil later acknowledged problems needing resolution. **[press/blog, unverified]** — [Quanta update](https://www.quantamagazine.org/update/169569/); [Wikipedia: Riemann hypothesis](https://en.wikipedia.org/wiki/Riemann_hypothesis)
- Conflict to carry forward: the Wikipedia RH page says the 2026 claimed proofs are still being evaluated and none has general acceptance, while the Lean community statement expresses full confidence in the formal proof. — [Wikipedia: Riemann hypothesis](https://en.wikipedia.org/wiki/Riemann_hypothesis); [Lean community blog](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)
- Example of an ordinary failed claim: a November 2026 arXiv paper on zeros of zeta and its derivative was withdrawn within days because of an error in the proof of its main results. — [arXiv:2611.12438](https://arxiv.org/abs/2611.12438)

**Guth-Maynard 2024 and consequences**
- Guth and Maynard, "New large value estimates for Dirichlet polynomials": N(sigma, T) <= T^(30(1-sigma)/13 + o(1)), replacing Huxley's 12/5 by 30/13; asymptotic for primes in all intervals of length x^(17/30+o(1)) and in almost all intervals of length x^(2/15+o(1)). Now published in Annals of Mathematics 203-2 (2026). **[peer-reviewed]** — [Annals of Mathematics](https://annals.math.princeton.edu/2026/203-2/p06); [arXiv:2405.20552](https://arxiv.org/pdf/2405.20552)
- Follow-ups include a version with characters giving zero density for Dirichlet L-functions, and a 2025 paper on arithmetic progressions of primes in intervals [x, x+x^theta] for theta > 17/30 (identifier likely the second link, not confirmed). **[preprints]** — [arXiv:2507.08296](https://arxiv.org/pdf/2507.08296); [arXiv:2509.04883](https://arxiv.org/pdf/2509.04883v1)
- The Analytic Number Theory Exponent Database (Tao, Trudgian, Yang) tracks zero-density, large-value and prime-distribution exponents with Python code and accepts outside corrections and contributions through GitHub. **[project page]** — [ANTEDB](https://teorth.github.io/expdb/)

**Twin primes and bounded gaps**
- Zhang 2013 (70,000,000), Maynard 2013 (600), Polymath8b 2014 (246; 12 under Elliott-Halberstam, 6 under generalized EH). The twin prime conjecture itself is open. **[peer-reviewed]** — [Wikipedia: Twin prime](https://en.wikipedia.org/wiki/Twin_prime); [arXiv:1407.4897](https://arxiv.org/pdf/1407.4897)
- 2026 flurry, none peer-reviewed: Stadlmann 240 (arXiv, 31 Aug 2026, combining Bombieri-Vinogradov with newer equidistribution estimates for smooth moduli); 240 also claimed by Hanxin Zhang with GPT-5.6 Sol (Zenodo); 236 (Shiva Kintali, GitHub); 212 (Axiom Math, within three days of Stadlmann); 186 (OpenAI with GPT-6 Astra, 3 Sep 2026, within two hours of Axiom). **[preprints / company PDFs]** — [arXiv:2608.31126](https://arxiv.org/abs/2608.31126); [Wikipedia: Prime gap](https://en.wikipedia.org/wiki/Prime_gap); [Science News, 11 Sep 2026](https://www.sciencenews.org/article/human-math-record-twin-primes-openai)
- A search result attributed a 236 preprint to Zhao Song and Song Yue (IACR ePrint 2026/1893) rather than Kintali; attribution of the 236 claim is therefore uncertain. — [IACR ePrint 2026/1893](https://eprint.iacr.org/2026/1893.pdf)
- Reactions: Soundararajan praised Stadlmann's work; Granville questioned how OpenAI treated her; Tao criticized the choice to give up on producing human understanding. OpenAI says it does not plan to push the number further. — [Science News](https://www.sciencenews.org/article/human-math-record-twin-primes-openai)
- Large gaps: claimed 2026 improvements to the Ford-Green-Konyagin-Maynard-Tao lower bound (GPT-5.6 Sol, then an OpenAI Lean formalization) are described as not fully verified. — [Wikipedia: Prime gap](https://en.wikipedia.org/wiki/Prime_gap)

**Goldbach**
- Binary Goldbach is open; verified for all even numbers up to 4 x 10^18 by Oliveira e Silva, Herzog and Pardi (Math. Comp. 2014), double-checked to 4 x 10^17. No 2025-2026 mathematical advance or AI claim is recorded on the Wikipedia page (last edited 9 Nov 2026). Helfgott's ternary proof was accepted for the Annals of Mathematics Studies series but the book is not recorded as published. — [Wikipedia: Goldbach's conjecture](https://en.wikipedia.org/wiki/Goldbach%27s_conjecture); [Math. Comp. 83 (2014)](https://www.ams.org/journals/mcom/2014-83-288/S0025-5718-2013-02787-1)
- Partial results: explicit Chen theorem (Bordignon, Johnston, Starichkova); exceptional set E(x) < x^0.72 (Pintz); two primes plus at most 8 powers of 2 (Pintz-Ruzsa 2020). — [Wikipedia: Landau's problems](https://en.wikipedia.org/wiki/Landau%27s_problems)

**Legendre and Landau's problems**
- All four Landau problems are listed as unresolved as of 2026. — [Wikipedia: Landau's problems](https://en.wikipedia.org/wiki/Landau%27s_problems)
- n^2+1: Iwaniec 1978 (infinitely many with at most two prime factors); Grimmelt and Merikoski 2025 (greatest prime factor at least n^1.312 infinitely often, preprint); Green-Sawhney 2024 (primes p^2 + nq^2). — [Wikipedia: Landau's problems](https://en.wikipedia.org/wiki/Landau%27s_problems); [arXiv:2505.00493](https://arxiv.org/abs/2505.00493)
- Legendre: Ingham 1937 gives primes between consecutive cubes for large n; Järviniemi 2022 bounds the number of exceptional primes with gaps above 2 sqrt(p) by x^(7/100+eps). — [Wikipedia: Landau's problems](https://en.wikipedia.org/wiki/Landau%27s_problems)
- Under RH: Chamberland and Straub (Feb 2026) combine Carneiro-Milinovich-Soundararajan with the Sorenson-Webster computation to get primes between x^(2+delta) and (x+1)^(2+delta) for all real x >= 1 when delta >= 1/4; Legendre itself (delta = 0) is not reached even under RH. **[preprint]** — [arXiv:2602.22502](https://arxiv.org/abs/2602.22502)

**Artin's primitive root conjecture**
- Classical: Hooley 1967 (conditional on GRH), Heath-Brown 1986 (at most two prime bases fail; one of 2, 3, 5 is a primitive root for infinitely many primes). — [Wikipedia: Artin's conjecture](https://en.wikipedia.org/wiki/Artin%27s_conjecture_on_primitive_roots)
- 2025: Goldmakher, Martin, Péringuey propose refinements about the finer distribution of ord_p(a), proved under GRH, weaker versions unconditionally; Fan and Pollack give, under GRH, a uniform Artin-Hooley asymptotic and a bound O(log^19(2|g|)) for the least prime with primitive root g; Klurman, Shparlinski, Teräväinen (BLMS 57(8), 2025) on Artin on average. — [arXiv:2502.19601](https://arxiv.org/abs/2502.19601); [arXiv:2505.05601](https://arxiv.org/abs/2505.05601); [Wikipedia: Artin's conjecture](https://en.wikipedia.org/wiki/Artin%27s_conjecture_on_primitive_roots)
- 2026: Murty and Naik show Artin follows from an unproven non-abelian large sieve inequality (conditional). — [arXiv:2608.21573](https://arxiv.org/pdf/2608.21573)
- 2026 unconditional claims, all unreviewed: OpenAI paper 029 (4 Oct 2026) claims every admissible base is a primitive root for infinitely many primes with a lower bound of order x/(log x)^2, below the conjectured density; a Bhargava preprint (14 Oct 2026) reportedly upgrades this to positive lower relative density; a Vojdanovski preprint (Nov 2026) with a Lean formalization extends to simultaneous primitive roots. The last two are hosted on sites I do not recognise (hexagonmath.org, palomar-registry.org) and I did not open them. **[preprints, unverified]** — [Wikipedia: Artin's conjecture](https://en.wikipedia.org/wiki/Artin%27s_conjecture_on_primitive_roots)
- Cautionary example: Carella's single-author arXiv paper claiming an unconditional proof has been revised at least 14 times since 2017 with no independent verification found. — [arXiv:1707.06517](https://arxiv.org/abs/1707.06517)

**Mersenne and Wieferich infinitude**
- It is unknown whether there are finitely or infinitely many Mersenne primes, and also unknown whether infinitely many Mersenne numbers with prime exponent are composite. 52 Mersenne primes are known. — [Wikipedia: Mersenne prime](https://en.wikipedia.org/wiki/Mersenne_prime)
- Wieferich: only 1093 and 3511 are known as of 2026; infinitude is open; Silverman 1988 shows abc implies infinitely many non-Wieferich primes; a prime divisor p of M_q is Wieferich iff p^2 divides M_q. — [Wikipedia: Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime)

### Inferences
- None of these problems is a realistic target for an amateur with a public AI model. The 2026 advances used unreleased frontier models with very large token budgets or came from specialists such as Stadlmann, and even a specialist's record on bounded gaps lasted three days.
- If the Lean RH/GRH proof stands, every "assuming RH" theorem about primes becomes unconditional once its deduction is itself checked. That includes the explicit prime gap bound of Carneiro-Milinovich-Soundararajan and the Chamberland-Straub delta >= 1/4 result cited above. Legendre, twin primes, binary Goldbach and n^2+1 do not follow from RH or GRH and stay open.
- The formal proof covers Dirichlet L-functions only. Hooley's proof of Artin's conjecture needs GRH for Dedekind zeta functions of Kummer fields, so Artin's conjecture with its exact density is not an immediate corollary (background knowledge about Hooley's hypothesis, not re-verified in this session).
- Much unconditional explicit work exists only because RH was unproven. A confirmed RH would reduce the value of several explicit programmes in section 2 and shift value toward formalizing the conditional-to-unconditional deductions.

### Gaps
- I could not read Alpöge's note, the Nature and Financial Times articles (paywall redirects), or the Zulip discussion. Whether the remaining kernel runs have finished is unknown.
- No information on how the Clay prize rules will treat a Lean-only proof.
- I did not open the OpenAI GitHub repository, so the exact statements of papers 003 and 029 are second-hand.
- No source found for a 2025-2026 verification of RH beyond height 3 x 10^12.

---

## 2. Explicit and computational analytic number theory: what is known and which parts have room for a laptop-scale contribution

### Takeaway
The headline computational records (Goldbach to 4 x 10^18, pi(10^29), RH to 3 x 10^12, Legendre to about 10^13 in n, primes between cubes to 1.6 x 10^40) were set with hundreds of cores for months or with distributed networks and are not laptop targets. The parts that individuals demonstrably still move are prime gap records beyond 2^64 and derived explicit constants, where the bottleneck is careful analysis and bookkeeping, not compute.

### Cited Findings

**Primes between consecutive powers**
- Dudek: a prime between n^3 and (n+1)^3 for all n >= exp(exp(33.217)). — [arXiv:1401.4233](https://arxiv.org/pdf/1401.4233)
- Cully-Hugill: a prime between n^155 and (n+1)^155 for all n >= 1, using a new explicit version of Goldston's 1983 estimate. J. Number Theory 247 (2023). **[peer-reviewed]** — [arXiv:2107.14468](https://arxiv.org/abs/2107.14468)
- Cubes threshold after Dudek: sources conflict. A 2022 zero-free-region paper says Cully-Hugill improved it to exp(exp(32.892)); Johnston et al. (2026) say exp(exp(32.537)), from her PhD thesis. — [arXiv:2212.06867](https://arxiv.org/pdf/2212.06867); [arXiv:2601.15564](https://arxiv.org/abs/2601.15564v2)
- Johnston, Sorenson, Thomas, Webster (Jan 2026, revised Mar 2026): a computation shows a prime between n^3 and (n+1)^3 whenever n^3 <= 1.649 x 10^40; with a Richert-weighted sieve, there is always a number with at most 2 prime factors between consecutive cubes for all n >= 1. The paper regards closing the cubes gap by the analytic route as hopeless with current zero estimates. **[preprint]** — [arXiv:2601.15564](https://arxiv.org/abs/2601.15564v2)
- Sorenson and Webster: algorithm verifying Oppermann's (hence Legendre's) conjecture for n up to 3.33 x 10^13 in the arXiv version, primes up to 27 digits; it ran about half a year on four Intel Xeon Phi 7210 processors, 256 cores in total. A later published version exists (DOI 10.1007/s40993-024-00589-4). — [arXiv:2401.13753](https://arxiv.org/abs/2401.13753)

**Explicit bounds for psi(x), theta(x), pi(x)**
- Fiori, Kadiri, Swidinsky: for x > 2, |psi(x) - x| < 9.22022 x (log x)^(3/2) exp(-0.8476836 sqrt(log x)); a companion paper gives |pi(x) - Li(x)| <= 9.2211 x sqrt(log x) exp(-0.8476 sqrt(log x)) and best numeric bounds for all x up to exp(1.8 x 10^9). — [arXiv:2204.02588](https://arxiv.org/abs/2204.02588); [arXiv:2206.12557](https://arxiv.org/pdf/2206.12557.pdf)
- Johnston uses the 3 x 10^12 verification height (a partial verification of RH) to tighten prime-counting bounds. — [arXiv:2109.02249](https://arxiv.org/pdf/2109.02249)
- Mossinghoff, Trudgian, Yang (Dec 2022) give four explicit zero-free regions improving Ford (2002). — [Wikipedia: Riemann hypothesis](https://en.wikipedia.org/wiki/Riemann_hypothesis); [arXiv:2212.06867](https://arxiv.org/pdf/2212.06867)
- Fiori and Jaskari (Sep 2026, revised Oct 2026): for x >= 21, |psi(x) - x| < 0.239 x exp(-0.1982767 (1 + logloglog x / (15 loglog x)) (log x)^(3/5) (loglog x)^(-1/5)); and, taking as input the zero-free half-plane Re(s) > 7/8 from the October 2026 OpenAI announcement, |psi(x) - x| < 0.04934 x^(3/4) (log x)^2 + 0.02636425 x^(7/8). **[preprint; second bound conditional on an unreviewed claim]** — [arXiv:2609.23222](https://arxiv.org/abs/2609.23222)

**Goldbach verification**
- The record remains 4 x 10^18 (2014). A March 2026 arXiv paper still calls it the state of the art. — [Math. Comp. 83 (2014)](https://www.ams.org/journals/mcom/2014-83-288/S0025-5718-2013-02787-1); [arXiv:2603.02621](https://arxiv.org/abs/2603.02621)
- Unreviewed 2025 extension claims: a Preprints.org manuscript claims checks from 4 x 10^18 up to 6 x 10^18 with probabilistic primality tests; a Medium post claims 4 x 10^18 + 7 x 10^13 by grid computing; a Zenodo record checks one million even numbers above 4 x 10^18 on Google Colab. **[non-peer-reviewed]** — [Preprints.org 202503.0949](https://www.preprints.org/manuscript/202503.0949); [Medium / Gridbach](https://medium.com/@jay_gridbach/grid-computing-shatters-world-record-for-goldbach-conjecture-verification-1ef3dc58a38d); [Zenodo 17308645](https://zenodo.org/records/17308645)

**pi(x) records**
- Largest pi(x) in primecount's records file: pi(10^29) = 1,520,698,109,714,272,166,094,258,063, computed 2022-02-28 by Kim Walisch and David Baugh. The latest dated entry in the file is 2022-04-11; there is no 10^30 entry. nth-prime record: the 10^25-th prime (Baugh, 2022-04-07). — [primecount Records.md](https://github.com/kimwalisch/primecount/blob/master/doc/Records.md)
- primecount accepts x up to 10^31; its documentation says record computations commonly run for weeks or months. — [primecount docs (Debian copy)](https://sources.debian.org/src/primecount/8.2%2Bds-1/doc/Records.md)

**Maximal prime gaps and first occurrences**
- Maximal gaps are known for all x below 2^64. — [arXiv:2012.03771](https://www.arxiv.org/pdf/2012.03771)
- Largest known maximal gap: 1854 after 101412319996363309069 (about 1.01 x 10^20), credited to Robert Smith running Brian Kehrig's code, the 85th maximal gap, merit about 40.25, dated 2026. Before that: 1676 after 20733746510561442863 (Kehrig), 1572 after 18571673432051830099 (Loizides). — [Wikipedia: Prime gap](https://en.wikipedia.org/wiki/Prime_gap)
- MathWorld states that as of 16 October 2026 the confirmed records extend through the gap of length 1854, citing Andersen and Luhn, "Record Prime Gaps" (12 Oct 2026). OEIS A005250 carries a b-file for n = 1..85 by Brian Kehrig. — [MathWorld: Prime Gaps](https://mathworld.wolfram.com/PrimeGaps.html); [OEIS A005250](https://oeis.org/A005250)
- Other records held by individuals: top merit 42.5192 by Mario Vojvoda in 2026 (gap 59724, 611-digit prime); largest gap with probable-prime ends 16,045,848 (385,713-digit PRPs) by Andreas Höglund, March 2024; largest with proven ends 1,113,106 (Cami, Jansen, Andersen). — [Wikipedia: Prime gap](https://en.wikipedia.org/wiki/Prime_gap)
- Tom Nicely's lists (1999 to 2019) are continued by a MersenneForum group on GitHub as a community-curated list of record first-occurrence gaps. — [Prime Gap List](https://primegap-list-project.github.io/); [history](https://gapcoin-project.github.io/gapcoin/2021/05/06/history-of-the-prime-gap-list)
- Related published work with an empirical flavour: Kourbatov and Wolf on first occurrences of gaps between primes in residue classes (J. Integer Sequences 23 (2020), Article 20.9.3). — [arXiv:2002.02115](https://arxiv.org/abs/2002.02115)

### Inferences
- Goldbach: the fastest published single-GPU figure (section 7) is 10^13 in 3246 s on an RTX 5090, about 3.1 x 10^9 even numbers per second. At that rate 4 x 10^18 would take about 1.3 x 10^9 s, roughly 41 years, before the superlinear sieve cost. Extending the Goldbach record is not a laptop project.
- Legendre/Oppermann: about 128 core-years on Xeon Phi hardware. A 24-core laptop would need on the order of a year or more just to replicate, so an extension needs a new algorithm (possibly GPU-based), not more patience.
- pi(10^30): no hardware or runtime figures were found, but the 10^29 record has stood since February 2022 with the two people who hold all recent records, which suggests it is well beyond a 64 GB machine.
- Prime gaps: individuals, not institutions, hold every current gap record, and the confirmed frontier moved from 2^64 to about 10^20 through one person's code. This is the computational area with the clearest evidence of individual-scale contribution. Credit comes as list entries, OEIS b-files and MathWorld citations; papers are rare.
- Explicit-constant work (Fiori-Jaskari within weeks of the OpenAI claim; Chamberland-Straub) shows a pattern of small publishable papers: take a new input (a zero-free region, a zero-density estimate, a verification height, a large computation) and push it through existing explicit machinery. The barrier is mastering the explicit-formula literature, which an AI system can help with; compute needs are modest.
- If RH is accepted, the same pattern applies with RH itself as the new input: RH-conditional bounds and gap results become unconditional, and a paper or Lean development that carefully records the consequences has value for a short window.

### Gaps
- Hardware and runtime for the gap search from 2^64 to 10^20, and whether it used GPUs, were not found (the Andersen record page returned no text; the relevant MersenneForum thread was not located).
- Hardware and runtime for pi(10^29) and for the 1.649 x 10^40 cubes computation were not found.
- Büthe's and Broadbent et al.'s specific bounds were not re-fetched; they appear here only through later papers.
- The bound in the published Sorenson-Webster paper may be larger than the arXiv v1 figure; not checked.

---

## 3. Primitive prime divisors: Bang, Zsigmondy, Birkhoff-Vandiver, Schinzel, Stewart, Bilu-Hanrot-Voutier, number fields, and open small questions

### Takeaway
The integer and Lucas-Lehmer theory is essentially closed (Zsigmondy 1892; Bilu-Hanrot-Voutier 2001 with Abouzaid's 2006 complete list), and I found no 2023-2026 paper extending it. The live edges are number fields and other rings, where existence is known only for n beyond an effectively computable bound, and the record tables for primitive parts and Gaussian Mersenne primes, where recent entries come from one or two people.

### Cited Findings
- Zsigmondy (1892): for coprime a > b > 0, a^n - b^n has a primitive prime divisor except n = 1 with a - b = 1; n = 2 with a + b a power of two; and (a, b, n) = (2, 1, 6). For a^n + b^n the only exception is 2^3 + 1^3. Bang (1886) is the case a = 2, b = 1. — [Wikipedia: Zsigmondy's theorem](https://en.wikipedia.org/wiki/Zsigmondy%27s_theorem)
- Carmichael: the Zsigmondy set of Fibonacci is {1, 2, 6, 12}, of Pell is {1}. Bilu, Hanrot, Voutier (J. Reine Angew. Math. 539, 2001): for Lucas and Lehmer sequences the Zsigmondy set lies in {1,...,30}, with 13 possible values 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 18, 30. — [Wikipedia: Zsigmondy's theorem](https://en.wikipedia.org/wiki/Zsigmondy%27s_theorem)
- Abouzaid (J. Théor. Nombres Bordeaux 18, 2006) completed Voutier's list of defective Lucas and Lehmer numbers, making the list exhaustive. — [Numdam](https://www.numdam.org/item/JTNB_2006__18_2_299_0)
- Stewart: the greatest prime factor of the n-th Lucas or Lehmer number exceeds n exp(log n / (104 log log n)), resolving a 1962 question of Schinzel and a 1965 conjecture of Erdős; the first general improvement on Bang (1886) and Carmichael (1912). — [arXiv:1008.1274](https://arxiv.org/abs/1008.1274)
- Number fields: Schinzel (1974) proved that for coprime algebraic integers A, B with A/B not a root of unity, A^n - B^n has a primitive divisor for n > N(d), where d is the degree of A/B and N(d) is effectively computable. — [ar5iv:0708.2190](https://ar5iv.arxiv.org/html/0708.2190)
- Schinzel (Math. Comp. 61, 1993) extended this to A^n - zeta_k B^n (known here from a search snippet only; the page refused a direct fetch). — [AMS Math. Comp. 1993](https://www.ams.org/mcom/1993-61-203/S0025-5718-1993-1189523-2/)
- Quadratic integer rings: Steidl, Hänler, Tasche, "On a number-theoretic result of Zsigmondy in domains of quadratic integers", Arch. Math. 1989. Only the title and venue were retrievable. — [Springer](https://link.springer.com/article/10.1007/BF01194869)
- Other settings: Flatters on norms of u^n - 1 for units u in real quadratic fields (identifies the terms without a primitive divisor); Min Sha on Lucas and Lehmer sequences in polynomial rings; Barańczuk on Chebyshev polynomials; polynomial Zsigmondy theorems; Silverman and Ingram-Silverman on elliptic divisibility sequences (finite Zsigmondy set, ineffective). — [arXiv:0708.2190](https://arxiv.org/abs/0708.2190); [arXiv:2005.01940](https://arxiv.org/pdf/2005.01940); [arXiv:1909.12143](https://arxiv.org/pdf/1909.12143); [arXiv:1002.4829](https://arxiv.org/pdf/1002.4829); [Wikipedia: Zsigmondy's theorem](https://en.wikipedia.org/wiki/Zsigmondy%27s_theorem)
- Imaginary quadratic analogue of Schinzel-Wójcik: for nonzero non-root-of-unity alpha, beta in the ring of integers of an imaginary quadratic field there are infinitely many maximal ideals P with equal orders mod P (Just and Pollack, 2021). — [arXiv:2102.00370](https://arxiv.org/abs/2102.00370)
- Aurifeuillian link: Wagstaff notes that Aurifeuillian factorizations cut across the cyclotomic ones and can be used to show that certain b^n ± 1 have at least two primitive prime factors (example: 3^27 + 1 has primitive prime factors 19441 and 19927). Granville and Pleasants showed that Schinzel found all such identities under their definition, yet the Cunningham tables contain unexplained near-equal splits such as 6^106 + 1 and 12^193 - 1 (two 77-digit primes). Wagstaff's systematic search of the tables for new identities reports a number of interesting findings. — [Wagstaff, Integers 12A (2012) A16](https://homes.cerias.purdue.edu/~ssw/cun/mine.pdf)
- Existence criterion for an Aurifeuillian factorization of Phi_n(b) with b = s^2 t, t squarefree: t ≡ 1 (mod 4) and n ≡ t (mod 2t), or t ≡ 2, 3 (mod 4) and n ≡ 2t (mod 4t). Algorithms: Brent (explicit formulae); Allombert and Belabas 2008. — [Wikipedia: Aurifeuillean factorization](https://en.wikipedia.org/wiki/Aurifeuillean_factorization); [arXiv:1004.5466](https://arxiv.org/pdf/1004.5466); [Numdam](https://www.numdam.org/articles/10.5802/jtnb.641)
- Gaussian Mersenne primes: (1 ± i)^n - 1 is a Gaussian prime iff n = 2 or n is odd and the norm is a rational prime; the norm is 2^n - 2^(1+n/2) cos(n pi/4) + 1. — [PrimePages glossary](https://t5k.org/glossary/xpage/GaussianMersenne.html); [MathWorld: Gaussian Mersenne Prime](https://mathworld.wolfram.com/GaussianMersennePrime.html)
- 41 Gaussian Mersenne exponents are listed: 2, 3, 5, 7, 11, 19, 29, 47, 73, 79, 113, ..., 3704053, 4792057, 15317227. The search is recorded as exhaustive for exponents below 5,000,000 (Batalov, Sep 2014). The largest, 15317227 (norm of 4,610,945 digits), is credited to Ryan Propper and Serge Batalov and appears on PrimePages with its rank marked as uncertain (41 with a question mark). A MersenneForum thread coordinates the search. — [OEIS A057429](https://oeis.org/A057429); [PrimePages top 20](https://t5k.org/top20/page.php?id=41)
- Date conflict: PrimePages shows the top Gaussian Mersenne norm as found July 2020 (prover code L5123), while OEIS records the term as added 20 June 2023. — [PrimePages top 20](https://t5k.org/top20/page.php?id=41); [OEIS A057429](https://oeis.org/A057429)
- Eisenstein Mersenne exponents are listed up to 2,237,561. The Aurifeuillian factor 536903681 of 2^58 + 1 is a Gaussian Mersenne norm. — [Wikipedia: Mersenne prime](https://en.wikipedia.org/wiki/Mersenne_prime); [Wikipedia: Aurifeuillean factorization](https://en.wikipedia.org/wiki/Aurifeuillean_factorization)
- Lucas Aurifeuillian primitive parts: the PrimePages top 20 are all ECPP proofs; the nine largest (16,176 to 23,012 digits) date from 2022 to 2024 under one prover code (E1), the rest from 2015 to 2019 under another (c77). — [PrimePages top 20, id 21](https://t5k.org/top20/page.php?id=21)
- A small paper in the area by a single author with no affiliation shown: Tejas Rao (2018, 11 pages) gives a formula for primitive indexes of composites in k^u ± h^u and a formula that produces Zsigmondy numbers. **[preprint]** — [arXiv:1810.11456](https://arxiv.org/abs/1810.11456)

### Inferences
- For odd n the norm formula gives 2^n ∓ 2^((n+1)/2) + 1, which are exactly the two Aurifeuillian halves of 2^(2n) + 1 in identity (1) of Wagstaff's paper. So "primitive divisors of Gaussian Mersenne numbers" and "primitive divisors of each Aurifeuillian factor" are the same question for base 2, and Schinzel's 1962 two-primitive-factors result is the relevant prior art.
- Candidate small problems, each requiring a literature check before any novelty claim:
  1. An explicit Zsigmondy theorem with a complete exception list for alpha^n - beta^n in Z[i] or Z[omega] when alpha, beta are not conjugate (so the pair is not a Lucas or Lehmer pair and Bilu-Hanrot-Voutier does not apply). Schinzel 1974 gives only an effective bound; Steidl-Hänler-Tasche 1989 may already contain the answer.
  2. Explicit exception lists for the statement that each Aurifeuillian factor L and M has its own primitive prime divisor, for bases 2, 3, 5, 6, 7, 10, 11, 12, checked against the Cunningham tables.
  3. Extending Wagstaff's 2012 search for Aurifeuillian-like near-equal splits to the factors added since 2012 and to factordb data, looking for structure in the unexplained examples.
  4. Closing or documenting the Gaussian Mersenne exponent range between 5,000,000 and 15,317,227 (the uncertain rank), and the analogous Eisenstein range.
  5. New ECPP-proved primitive parts (Lucas Aurifeuillian, or primitive parts of other sequences) for the PrimePages top-20 lists.
- Items 1 to 3 are theorem-plus-computation notes of the kind Integers and the Journal of Integer Sequences publish; items 4 and 5 give list credit, not papers. Item 4 in full is too large for one machine (several hundred thousand prime exponents, each a multi-million-digit test); a partial range is feasible.

### Gaps
- I found no 2023-2026 paper on primitive divisors in Gaussian integers or on primitive divisors of Aurifeuillian factors. The search budget ran out before I could query arXiv listings or zbMATH, so absence here is weak evidence.
- Schinzel 1962 and Birkhoff-Vandiver 1904 were not retrieved; the exact exception list in Schinzel's two-primitive-factors theorem is unconfirmed.
- The content of Steidl-Hänler-Tasche 1989 (Springer paywall) and of Schinzel 1993 (AMS returned 403) could not be read.
- Search limits for Eisenstein Mersenne exponents were not found.

---

## 4. Order of 2 modulo p, Artin-type statistics, Wieferich primes, Fermat quotients, Aurifeuillian factorizations, the Cunningham project

### Takeaway
Base-2 Wieferich and Wall-Sun-Sun searches are closed to 2^64 by a 2020-2022 PrimeGrid project, but the generalized searches (other bases, Wilson, Wolstenholme, Pell and tribonacci analogues) stop between 10^9 and 5 x 10^13 and are the clearest laptop-plus-GPU targets in this survey. The Cunningham project is active (page 150, updated November 2026), but its wanted numbers are 216 to 347 digits and are handled by NFS@Home.

### Cited Findings
- Wieferich history: Lehmer to 6 x 10^9 (about 1980); 2.5 to 3 x 10^15 by 2006; Dorais and Klyve to 6.7 x 10^15 (J. Integer Sequences 14, 2011); Wieferich@Home (2007-2016) and PrimeGrid (2011-2017) passed 10^17 but neither reported results that could be relied on, and the PrimeGrid work was later described as wasted. PrimeGrid's 2020-2022 combined Wieferich and Wall-Sun-Sun project, with checksums for double-checking each subinterval, ended in December 2022 and established that a third Wieferich prime must exceed 2^64. — [Wikipedia: Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime)
- Near-misses from that project: 378 with |A| <= 1000, 37 with |A| <= 100, 2 with |A| <= 10: Wall-Sun-Sun near-miss 7665762181374748069 (A = -1) and Wieferich near-miss 3156824277937156367 (A = +7). — [PrimeGrid WW statistics](https://www.primegrid.com/stats_ww.php)
- Wall-Sun-Sun: none below 2^64. Generalizations: Lucas-Wieferich primes for other discriminants are conjectured infinite for every fundamental discriminant; Pell-Wieferich primes 13, 31, 1546463 with no others below 10^9 (OEIS A238736); no tribonacci-Wieferich primes below 10^11. — [Wikipedia: Wall-Sun-Sun prime](https://en.wikipedia.org/wiki/Wall%E2%80%93Sun%E2%80%93Sun_prime)
- Fermat quotients in other bases: the table of base-a Wieferich primes for a up to 30 is labelled as checked to 5 x 10^13, sourced to Richard Fischer's fermatquotient.com; examples include base 3: 11, 1006003; base 5: ..., 188748146801; base 22: ..., 9809862296159; bases 21 and 29 have only p = 2. — [Wikipedia: Fermat quotient](https://en.wikipedia.org/wiki/Fermat_quotient)
- Wilson primes: only 5, 13, 563; any other exceeds 2 x 10^13 (Costa, Gerbicz, Harvey, Math. Comp. 83, 2014); no later extension is recorded. — [Wikipedia: Wilson prime](https://en.wikipedia.org/wiki/Wilson_prime)
- Wolstenholme primes: only two known up to 10^11 (Booker, Hathi, Mossinghoff, Trudgian, Ramanujan J., 2022). — [Wikipedia: Wolstenholme prime](https://en.wikipedia.org/wiki/Wolstenholme_prime)
- Order statistics: Goldmakher-Martin-Péringuey (2025) conjecture finer distribution laws for ord_p(a), proved under GRH; Just-Pollack (2021) prove ord_p(A) > ord_p(2) for infinitely many p for almost all positive integers A. — [arXiv:2502.19601](https://arxiv.org/abs/2502.19601); [arXiv:2102.00370](https://arxiv.org/abs/2102.00370)
- Recent small papers in this neighbourhood: Wagstaff, "Two Mersenne Prime Conjectures" (JIS 2025, Article 25.7.2); Klaška, "Fermat Numbers Modulo a Prime" (JIS 25.8.7) and "Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers" (Integers 2026, A77); Roettger and Williams on the Lucas-Lehmer test (JIS 25.2.5); Ballot, "On Absolute Lucas Pseudoprimes" (Integers 2026, A102). — [JIS vol. 28](https://cs.uwaterloo.ca/journals/JIS/vol28.html); [Integers vol. 26](https://math.colgate.edu/~integers/vol26.html)
- Cunningham project: begun 1925, bases 2, 3, 5, 6, 7, 10, 11, 12; open-ended by design because exponent limits are raised as factoring improves. Main page last modified 20 November 2026; main tables include all factors through #6901 on Page 150; wanted lists issued 15 November 2026; the contact is Sam Wagstaff. — [Cunningham Project](https://homes.cerias.purdue.edu/~ssw/cun/index.html); [Wikipedia: Cunningham Project](https://en.wikipedia.org/wiki/Cunningham_Project)
- Current wanted list: ten "most wanted" from C248 (2,1139+) to C334 (11,326+); twenty "more wanted" from C236 to C347; six "smaller-but-needed" from C216 to C219 (2,1421+; 10,407-; 2,1415-; 7,917L; 11,371-; 2,1415+). — [want149.txt](https://homes.cerias.purdue.edu/~ssw/cun/want149.txt)
- All seven numbers in the "who is factoring what" file are assigned to NFS@Home by SNFS (c236 to c334). — [who.txt](https://homes.cerias.purdue.edu/~ssw/cun/who.txt)
- The project page still links a 2012 press release about 75- and 79-digit prime factors found by the Elliptic Curve Method. — [Cunningham Project](https://homes.cerias.purdue.edu/~ssw/cun/index.html)

### Inferences
- The gap between base 2 (2^64, about 1.8 x 10^19) and bases 3 to 30 (5 x 10^13) is over five orders of magnitude. PrimeGrid's software reached 2^64 with volunteers in about two years; one 24 GB GPU plus 24 cores could plausibly push selected bases, or the Pell and tribonacci analogues, one to three orders of magnitude in weeks to months. Results would be OEIS updates plus a short computational note in the style of Dorais-Klyve (JIS 2011).
- Any such search must include a double-check design. The earlier PrimeGrid and Wieferich@Home efforts are described as wasted for lack of reliable results, and the successful rerun used per-interval checksums.
- Wilson and Wolstenholme searches depend on specialised algorithms (Costa-Gerbicz-Harvey; Booker et al.). Extending them is an algorithm-engineering project where a GPU port could be new, but I found no evidence either way.
- Numerical tests of the Goldmakher-Martin-Péringuey refined conjectures (order statistics of 2, 3, 5 modulo all primes to 10^12 or beyond) are feasible on a GPU and would be new data if not already in their paper. Their conjectures need GRH for Kummer fields, which the November 2026 Lean proof does not cover, so they remain conjectural.
- Cunningham: the remaining composites have survived extensive ECM, so a laptop running ECM has a low but nonzero chance of a credited factor; NFS on C216+ is out of reach for one machine.

### Gaps
- No source fetched for factordb, for current ECM depth on Cunningham composites, or for Wagstaff's submission procedure beyond the contact address.
- No source for numerical Artin-constant or order-of-2 statistics computations (the search was refused for budget reasons).
- Whether the PrimeGrid WW application ran on GPUs was not confirmed.
- fermatquotient.com was not opened; the 5 x 10^13 bound is from Wikipedia and may be stale.

---

## 5. Distributed and volunteer projects where individuals get credit, and which lead to publications

### Takeaway
GIMPS, PrimeGrid, the prime gap and k-tuplet lists, the Cunningham tables, PrimePages and OEIS all credit individuals by name, and all remain active in November 2026. They give list credit, not papers; publications arise when someone writes up a completed search with a clear bound (Dorais-Klyve, Costa-Gerbicz-Harvey, Booker et al.) or analyses the data (Kourbatov-Wolf).

### Cited Findings
- GIMPS: the latest new prime is M136279841 (41,024,320 digits), proved 12 October 2024 by Luke Durant, announced 21 October 2024; official credit goes to Durant, Preda, Woltman, Blosser and others; $3,000 research discovery award per new Mersenne prime; EFF $150,000 for the first 100-million-digit prime. No new Mersenne prime in 2025 or 2026. The 2025-2026 news is verification: M74207281 confirmed as 49th (23 Jun 2025), M77232917 as 50th (8 Sep 2025), M82589933 as 51st (4 Sep 2026). All exponents below 84,106,643 are tested and verified; all below 142,869,329 are tested at least once. — [mersenne.org](https://www.mersenne.org/)
- Durant's find was the first by GPU; he reportedly used thousands of cloud GPUs across 17 countries for about a year at a cost of about $2 million. — [Wikipedia: Largest known prime number](https://en.wikipedia.org/wiki/Largest_known_prime_number); [Popular Science](https://www.popsci.com/science/largest-prime-number/)
- PrimeGrid (snapshot 21 Nov 2026): 102,277 primes found, 3,828 mega primes, 38,214 reported to the PrimePages Top 5000. Recent individual finds: generalized Fermat mega prime 13427472^524288 + 1 (3,737,122 digits) by Jean-Luc Garambois on an RTX 4080 SUPER (3 Mar 2025); generalized Cullen 4052186 · 69^4052186 + 1 (7,451,366 digits) by Mark Williams (16 Apr 2025); a Sierpinski/Riesel base 5 prime eliminating k = 67612, leaving 27 k's (8 Apr 2025). The site links a published-results page whose contents I did not open. — [primegrid.com](https://www.primegrid.com/)
- Top non-Mersenne primes continue to arrive: a generalized Fermat prime of 13,426,224 digits (12 Oct 2025) and one of 7,188,671 digits (12 Aug 2026). — [Wikipedia: Largest known prime number](https://en.wikipedia.org/wiki/Largest_known_prime_number)
- Prime k-tuplets: maintained by Norman Luhn (Tony Forbes from 1997 to August 2021), last updated 8 November 2026; submissions by email; numbers up to about 1000 digits are double-checked by the maintainer, larger ones need a stated proof method (BLS, APR-CL, ECPP, Primo, CM). — [pzktupel.de](https://www.pzktupel.de/ktuplets.php)
- Prime gap records: maintained by the MersenneForum-based Prime Gap List community on GitHub; the record-gaps page is maintained by Andersen and Luhn as of 2026. — [Prime Gap List](https://primegap-list-project.github.io/); [OEIS A005250](https://oeis.org/A005250)
- Cunningham tables: page 150, factors through #6901, updated November 2026. — [Cunningham Project](https://homes.cerias.purdue.edu/~ssw/cun/index.html)
- Formalization projects with claimable tasks: PNT+ (Kontorovich; prime number theorem with classical error term, PNT in arithmetic progressions, stretch goal Chebotarev), coordinated on Lean Zulip with a blueprint, a contributing guide and claimable issues, under the Apache 2.0 license; the Integrated Explicit Analytic Number Theory network material is moving to teorth/IEANTN (notice dated August 2026). — [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
- MathHelm (announced 13 Nov 2026) is a nonprofit forum for discussing AI-generated papers, including the 722 OpenAI manuscripts; its principle is that mathematicians have no obligation to check such papers but useful observations are valuable. — [Tao's blog](https://terrytao.wordpress.com/)
- Publications that grew out of search efforts: Dorais and Klyve (JIS 2011); Costa, Gerbicz, Harvey (Math. Comp. 2014); Booker, Hathi, Mossinghoff, Trudgian (Ramanujan J. 2022); Oliveira e Silva, Herzog, Pardi (Math. Comp. 2014); Kourbatov and Wolf (JIS 2020). — [Wikipedia: Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime); [Wikipedia: Wilson prime](https://en.wikipedia.org/wiki/Wilson_prime); [Wikipedia: Wolstenholme prime](https://en.wikipedia.org/wiki/Wolstenholme_prime); [arXiv:2002.02115](https://arxiv.org/abs/2002.02115)

### Inferences
- For publication purposes the useful distinction is between joining a project (credit on a list, co-credit on a discovery) and owning a bounded search (a paper). The papers cited all have the form: we searched X up to B with method M, double-checked, and found the following.
- GIMPS odds are poor for one laptop: no prime in two years, with all first-time tests now above exponent 142 million.
- PrimeGrid GPU subprojects (generalized Fermat, AP27) are where a single consumer GPU produced a top-100 prime in 2025, so a 24 GB GPU is competitive there for list credit.
- Formalization tasks in PNT+ and IEANTN, and commentary on MathHelm, are the lowest-barrier routes to named credit that sit close to the 2026 developments.

### Gaps
- Current largest k-tuplets by k and their finders were not retrieved (sub-pages not fetched; search refused).
- factordb and OEIS contribution norms were not fetched.
- PrimeGrid's published-results page was not opened, so I cannot say which PrimeGrid work led to journal papers.

---

## 6. Examples 2015-2026 of prime-number papers by amateurs or independent researchers, and by people using AI or large-scale computer search, with venues

### Takeaway
There are real examples of non-professionals contributing in 2024-2026, but they cluster in three forms: record computations credited in lists, Erdős-problem solutions obtained with public chatbots and then written up with professionals, and arXiv or Zenodo software papers. I found no 2025-2026 example of an amateur getting a prime-number theorem into Mathematics of Computation or Experimental Mathematics, and the Erdős window is being closed by lab-scale sweeps.

### Cited Findings
- Luke Durant, a former NVIDIA engineer, found the 52nd Mersenne prime in October 2024 (GIMPS credit, no paper). — [mersenne.org](https://www.mersenne.org/); [Smithsonian](https://www.smithsonianmag.com/smart-news/amateur-mathematician-discovers-the-largest-known-prime-number-with-more-than-41-million-digits-180985321/)
- Liam Price, 23, with no advanced mathematics training, obtained a proof of Erdős problem #1196 (primitive sets) from a single prompt to GPT-5.4 Pro in April 2026; Tao and Lichtman shortened and clarified it; Lichtman judged the raw AI output poor and in need of expert interpretation. — [Scientific American, 24 Apr 2026](https://www.scientificamerican.com/article/amateur-armed-with-chatgpt-vibe-maths-a-60-year-old-problem/)
- The resulting paper: Alexeev, Barreto, Li, Lichtman, Price, Shah, Tang, Tao, "Primitive sets and von Mangoldt chains: Erdős Problem #1196 and beyond" (1 May 2026, 35 pages); the abstract credits GPT-5.4 Pro output with suggesting the method; it also proves #1217 and gives a short proof of the Erdős primitive set conjecture. **[preprint]** — [arXiv:2605.00301](https://arxiv.org/abs/2605.00301)
- Other cases from Quanta's account: Barreto (Cambridge undergraduate) and Price solved #728 with GPT-5.2 Pro in January 2026, checked with Harmonic's Aristotle; their December 2025 claim on #333 turned out to be in a 1977 Erdős paper; Wouter van Doorn, who works at a customer service company, made progress on #1102 (squarefree integers) without AI, checked by Tao. Bloom noted that most early results came from hobbyists and undergraduates using public models. — [Quanta, 3 Aug 2026](https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/)
- Benjamin Grayzel, a Dartmouth master's student, used Gemini 3 Pro for Erdős #659 and posted to arXiv. — [Dartmouth CS news](https://web.cs.dartmouth.edu/news/2026/04/student-ideates-ai-longstanding-math-problem)
- Lab-scale competition: a DeepMind-led team (Jan 2026) solved four Erdős problems and found forgotten solutions to nine; a DeepMind agent (May 2026) resolved 9 of 353 open Erdős problems without human help at a few hundred dollars per problem; OpenAI's Astra (Aug 2026) made 10 advances. Bloom's database stood at 565 solved, 652 open. — [Quanta, 3 Aug 2026](https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/)
- Warnings from the same community: Bloom says non-mathematicians post AI-generated papers of 100 to 200 pages that no person has read or will read; Tao stepped back from the Erdős site; Noga Alon stopped working on the problems. — [Quanta, 3 Aug 2026](https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/)
- Independent software papers: Isaac Llorente-Saguer (described as an independent researcher), "GoldbachGPU" (arXiv cs.MS, 2 Mar 2026) and a follow-up whose v2 (7 Oct 2026) corrects two concurrency defects and withdraws its four-GPU results. **[preprints]** — [arXiv:2603.02621](https://arxiv.org/abs/2603.02621); [arXiv:2603.07850](https://arxiv.org/abs/2603.07850)
- Independent claims on bounded gaps in 2026: Hanxin Zhang with GPT-5.6 Sol (240, Zenodo) and Shiva Kintali (236, GitHub), neither peer-reviewed. — [Wikipedia: Prime gap](https://en.wikipedia.org/wiki/Prime_gap)
- Record computations by individuals: Robert Smith and Brian Kehrig (maximal gap 1854, 2026), Mario Vojvoda (merit record, 2026), Andreas Höglund (2024), Kim Walisch and David Baugh (pi(10^29), 2022), Ryan Propper and Serge Batalov (largest Gaussian Mersenne). — [Wikipedia: Prime gap](https://en.wikipedia.org/wiki/Prime_gap); [primecount Records.md](https://github.com/kimwalisch/primecount/blob/master/doc/Records.md); [OEIS A057429](https://oeis.org/A057429)
- Venue samples. Journal of Integer Sequences 2025: Wagstaff "Two Mersenne Prime Conjectures"; Cohen "Conjectures about Primes and Cyclic Numbers"; Klaška "Fermat Numbers Modulo a Prime"; Hercher "On One of Erdős' Problems - An Efficient Search for Benelux Pairs". JIS 2026: Cheng, Kinlaw, Nguyen "The Reciprocal Sum of Even Pseudoprimes". Integers 2026: Chamberland "The Erdős-Straus Conjecture and the Structure of Primes" (A42); Winkler "Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m" (A90); Marques "Bonse's Inequality along Subsequences of Primes" (A99); Wright "(a,a)-Carmichael Numbers ..." (A123); Moore and Sorenson "Explicit Bounds and Parallel Algorithms for Counting Multiply Gleeful Numbers" (A84). — [JIS vol. 28](https://cs.uwaterloo.ca/journals/JIS/vol28.html); [JIS vol. 29](https://cs.uwaterloo.ca/journals/JIS/vol29.html); [Integers vol. 26](https://math.colgate.edu/~integers/vol26.html)
- Non-peer-reviewed Goldbach record claims from 2025 (Preprints.org, Medium, Zenodo) show what does not count as a publishable result. — [Preprints.org](https://www.preprints.org/manuscript/202503.0949); [Medium](https://medium.com/@jay_gridbach/grid-computing-shatters-world-record-for-goldbach-conjecture-verification-1ef3dc58a38d)
- Institutional context: OpenAI reports about three hours of ChatGPT Pro-equivalent compute per released result and about 4,000 attempted problems; a Simons Foundation effort ($15M, with $5M from OpenAI) aims to help mathematicians navigate AI results. — [OpenAI, 6 Oct 2026](https://openai.com/index/sharing-ai-progress-in-mathematics/)

### Inferences
- JIS and Integers are the realistic venues: their 2025-2026 tables of contents contain short papers on conjectures, pseudoprimes, Fermat numbers and efficient searches of the kind a careful amateur could produce. Author affiliations are not shown on the index pages, so I cannot say how many are independent.
- The Erdős route worked for amateurs between December 2025 and about May 2026. With labs sweeping hundreds of problems at a few hundred dollars each, the remaining open problems are selected for resisting exactly the tool an amateur would use.
- What a public model cannot do cheaply is run a months-long computation with a verified double-check, maintain a table, or own a niche sequence. Those are the forms of contribution that the 2026 record lists show individuals still providing.
- AI-generated long manuscripts on famous problems are now actively unwelcome; a submission's credibility depends on being short, checkable, and ideally formalized or accompanied by reproducible code.

### Gaps
- No 2015-2026 examples located for amateurs in Mathematics of Computation, Experimental Mathematics, Notes on Number Theory and Discrete Mathematics or the American Mathematical Monthly; the relevant search was refused for budget reasons, so this is not evidence of absence.
- AlphaEvolve and FunSearch prime-related results were not researched.
- Whether Llorente-Saguer's papers were submitted to a journal is unknown.

---

## 7. GPU-accelerated number theory: what has been done for primes, and gaps

### Takeaway
GPUs are standard for Mersenne PRP testing, trial factoring and generalized Fermat searches, and 2026 brought the first open-source GPU Goldbach frameworks. I found no published GPU work on Fermat-quotient searches in general bases, Wilson or Wolstenholme searches, pi(x), or order-of-a statistics, though my coverage of this question is thin.

### Cited Findings
- GIMPS GPU software: GpuOwl, now called PRPLL, is an OpenCL program for PRP tests with proofs; mfaktc does trial factoring on NVIDIA GPUs; CUDALucas does Lucas-Lehmer tests. GIMPS lists PRPLL as the GPU option for first-time PRP testing; a BOINC project offers GPU trial factoring. — [GpuOwl repository](https://github.com/preda/gpuowl); [mersenne.org glossary](https://www.mersenne.org/various/glossary.php); [mersenne.org](https://www.mersenne.org/)
- A 2026 NVIDIA developer forum post reports that the NTT build of PRPLL now runs on CUDA as well as OpenCL, using FP64 FFT or integer NTT. — [NVIDIA developer forum](https://forums.developer.nvidia.com/t/prpll-ntt-now-supports-both-cuda-and-opencl/367918)
- M136279841 was flagged probable prime on an NVIDIA A100 and confirmed by Lucas-Lehmer on an H100, the first GIMPS discovery on data-centre GPUs. — [heise](https://heise.de/en/news/M136279841-New-largest-known-Mersenne-prime-number-confirmed-with-GPU-9989146.html)
- PrimeGrid GPU applications: Generalized Fermat Prime Search n = 16 to 22 (CPU and GPU), the n = 23 "Do You Feel Lucky?" subproject (GPU only), AP27 search (CPU and GPU), factorial/compositorial sieve (GPU). All other subprojects are CPU-only. — [primegrid.com](https://www.primegrid.com/)
- PrimeGrid's Wieferich/Wall-Sun-Sun application was updated with about a 3x speed-up and its limit raised from 2^62 to 2^64. — [PrimeGrid forum](https://www.primegrid.com/forum_thread.php?id=9508)
- GoldbachGPU (Mar 2026): exhaustive verification to 10^12 on one RTX 3070 with 8 GB VRAM; bit-packed primes, segmentation, GPU fast path with CPU fallback; earlier GPU approaches hit a memory ceiling near 10^11. Follow-up (v2, Oct 2026): 10^12 in 145 s and 10^13 in 3246 s on one RTX 5090; sieve cost grows as N·pi(sqrt N). — [arXiv:2603.02621](https://arxiv.org/abs/2603.02621); [arXiv:2603.07850](https://arxiv.org/abs/2603.07850)
- Checking the RH Lean export is partly within reach of a workstation: con-leche needs about 50 GB RAM and under four minutes on 64 threads; the full kernel check needs about 100 GB RAM and 70 GB disk. — [math.mit.edu/~drew/grh](https://math.mit.edu/~drew/grh/)

### Inferences
- A 24 GB consumer GPU is in the same class as the cards that found PrimeGrid mega primes in 2025, so for generalized Fermat and AP27 work the hardware is competitive.
- GoldbachGPU's v2 corrections show that GPU number-theory code by individuals gets posted with concurrency bugs; a carefully validated, reproducible GPU implementation of a search with no existing GPU code would itself be a publishable software contribution (the precedent is arXiv cs.MS).
- Candidate gaps for a GPU port, each needing a prior-art check: Fermat quotients in bases 3 to 30 beyond 5 x 10^13; Pell and tribonacci Wieferich analogues; near-Wilson and Wolstenholme searches; large-scale order-of-a statistics; Aurifeuillian and primitive-part PRP sieving.
- With 64 GB RAM the con-leche replay of the RH proof might just fit; the full kernel check will not.

### Gaps
- Searches for GPU work on Wilson, Wolstenholme and order statistics were refused for budget reasons; "no published GPU work found" is therefore weakly supported.
- Whether the gap search to 10^20 or the PrimeGrid WW application used GPUs is unconfirmed.
- No benchmark data for ECPP or ECM on a 24-core laptop was gathered.

---

## 8. Synthesis for the practical aim: within reach versus out of reach for an amateur with an AI system and one strong laptop

### Takeaway
Out of reach: every famous conjecture and every flagship verification record. Within reach: bounded searches for special primes in under-searched variants, record-list entries (gaps, primitive parts, generalized Fermat), small explicit or exception-list theorems in primitive-divisor theory after a literature check, OEIS and JIS/Integers notes, and formalization or digestion work around the 2026 AI results.

### Cited Findings
- Out of reach, with evidence: RH/GRH (17 million lines of Lean from an unreleased model) — [Lean community blog](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/); bounded gaps (a specialist's record overtaken in three days by two AI labs) — [Science News](https://www.sciencenews.org/article/human-math-record-twin-primes-openai); Goldbach to 4 x 10^18 (distributed, unbeaten since 2014) — [Wikipedia: Goldbach's conjecture](https://en.wikipedia.org/wiki/Goldbach%27s_conjecture); Legendre verification (256 cores for half a year) — [arXiv:2401.13753](https://arxiv.org/abs/2401.13753); Cunningham wanted numbers (C216 to C347, NFS@Home) — [want149.txt](https://homes.cerias.purdue.edu/~ssw/cun/want149.txt); a new Mersenne prime (about $2 million of cloud GPU for the last one) — [Wikipedia: Largest known prime number](https://en.wikipedia.org/wiki/Largest_known_prime_number).
- Within reach, with evidence of individuals doing it: prime gap records — [Wikipedia: Prime gap](https://en.wikipedia.org/wiki/Prime_gap); ECPP primitive-part records at 16,000 to 23,000 digits — [PrimePages](https://t5k.org/top20/page.php?id=21); generalized Fermat mega primes on a consumer GPU — [primegrid.com](https://www.primegrid.com/); bounded special-prime searches written up in JIS — [Wikipedia: Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime); short conjecture and search notes in JIS and Integers — [JIS vol. 28](https://cs.uwaterloo.ca/journals/JIS/vol28.html), [Integers vol. 26](https://math.colgate.edu/~integers/vol26.html); explicit-constant follow-ups to new inputs — [arXiv:2609.23222](https://arxiv.org/abs/2609.23222); Lean corollaries of the RH proof produced by a third party within a day — [math.mit.edu/~drew/grh](https://math.mit.edu/~drew/grh/).
- Under-searched ranges documented above: Fermat quotients in bases 3 to 30 only to 5 x 10^13 — [Wikipedia: Fermat quotient](https://en.wikipedia.org/wiki/Fermat_quotient); Pell-Wieferich to 10^9, tribonacci-Wieferich to 10^11 — [Wikipedia: Wall-Sun-Sun prime](https://en.wikipedia.org/wiki/Wall%E2%80%93Sun%E2%80%93Sun_prime); Wilson to 2 x 10^13 — [Wikipedia: Wilson prime](https://en.wikipedia.org/wiki/Wilson_prime); Wolstenholme to 10^11 — [Wikipedia: Wolstenholme prime](https://en.wikipedia.org/wiki/Wolstenholme_prime); Gaussian Mersenne exponents exhaustive only below 5,000,000 — [OEIS A057429](https://oeis.org/A057429).

### Inferences
Ranked by my estimate of the chance of a publishable or citable outcome on the stated hardware (all rankings are judgment, not sourced):

1. **Bounded search with a write-up.** Pick one family (generalized Wieferich in bases 3 to 30, Pell-Wieferich, tribonacci-Wieferich, Lucas-Wieferich for other discriminants), build a CPU+GPU search with interval checksums and an independent double-check, extend the bound by at least two orders of magnitude, and publish near-miss tables. Target: JIS or Integers, plus OEIS. Barrier: correct modular arithmetic near 2^64 on a GPU and a double-check design. The outcome is publishable whether or not a new prime is found.
2. **Explicit exception-list theorem in primitive-divisor theory.** A Zsigmondy-type statement for Z[i] or Z[omega] with non-conjugate bases, or a statement that each Aurifeuillian factor has its own primitive prime divisor with explicit exceptions for Cunningham bases, supported by computation. Target: Integers, JIS. Barrier: confirming novelty against Schinzel 1962, 1974 and Steidl-Hänler-Tasche 1989, which I could not read.
3. **Data paper on order statistics.** Large-scale tabulation of ord_p(a) testing the Goldmakher-Martin-Péringuey refinements, or Wieferich-style near-miss statistics against heuristics. Target: Experimental Mathematics, Integers. Barrier: knowing what the authors already computed.
4. **Record-list contributions.** High-merit or first-occurrence prime gaps; ECPP proofs of primitive parts; partial Gaussian or Eisenstein Mersenne ranges; PrimeGrid GFN on the GPU. Outcome: named credit on PrimePages, the gap list, OEIS; usually no paper.
5. **Formalization and digestion.** PNT+ or IEANTN tasks; Lean proofs of known "RH implies X" statements about primes on top of the new library; careful commentary on specific AI-generated papers at MathHelm. Barrier: Lean skill; a 64 GB machine is marginal for replaying the RH export. This area is moving daily and may be saturated by labs within weeks.
6. **Explicit-constant follow-ups.** Deriving improved explicit prime bounds from the newest inputs. Barrier: high analytic skill; specialists (Fiori, Johnston, Trudgian, Yang, Cully-Hugill) do this within weeks of each new input, and a confirmed RH would make much of it moot.

Cross-cutting cautions:
- Any project started now should be checked against what RH/GRH for Dirichlet L-functions would trivialise.
- Novelty checks matter more than before: AI literature search has repeatedly found that supposedly new results were already known (Erdős #333).
- A long AI-written manuscript on a famous problem is the least likely output to be read.

### Gaps
- No benchmarks were gathered for the specific laptop (ECPP digits per week, GPU modular-exponentiation throughput), so the feasibility ranking is unquantified.
- zbMATH and MathSciNet were not consulted; novelty of items 1 to 3 is unverified.
- arXiv endorsement requirements and journal policies on AI use were not researched.

---

## Search log

Web searches executed (29):

1. Riemann Hypothesis claimed proof 2025 2026 reception
2. Guth Maynard zero density estimate consequences primes short intervals
3. bounded gaps between primes 246 Polymath8b status 2025
4. Goldbach conjecture verification beyond 4*10^18 2025
5. primes between consecutive cubes explicit Cully-Hugill Johnston
6. pi(x) record primecount 10^30 2025 2026
7. Platt Trudgian Riemann hypothesis true up to 3*10^12 later extension
8. explicit bounds psi(x) Fiori Kadiri Swidinsky sharper prime number theorem
9. maximal prime gaps first occurrence search beyond 2^64 status
10. Zsigmondy theorem primitive prime divisors Gaussian integers arXiv
11. Wieferich prime search limit PrimeGrid WW project results
12. Cunningham project status 2026 remaining composites Wagstaff (returned irrelevant results about composite materials)
13. Cunningham project factorization b^n±1 tables "most wanted" Wagstaff
14. Aurifeuillian factorization primitive part recent paper arXiv
15. Artin primitive root conjecture recent progress 2024 2025
16. GIMPS new Mersenne prime 2025 2026 discovery
17. PrimeGrid 2026 mega prime discovery announcement
18. GPU Goldbach verification arXiv 2603.02621
19. primitive divisors Lucas Lehmer sequences Bilu Hanrot Voutier extension 2023 2024 2025
20. Wieferich Wall-Sun-Sun search completed 2^64 PrimeGrid 2022 result
21. prime gap records list Nicely Loizides first known occurrence 2025 mersenneforum
22. Legendre conjecture Landau problems status n^2+1 primes recent results
23. amateur mathematician AI-assisted proof Erdős problem 2026 number theory published
24. GPU primality testing sieve mfaktc PRPLL gpuowl 2025
25. OpenAI October 2026 math results list prime numbers twin primes Artin conjecture
26. Gaussian Mersenne primes primitive divisors (1+i)^n-1 search status
27. Alpöge Riemann hypothesis Lean proof November 2026 mathlib verification
28. exhaustive prime gap search beyond 2^64 GPU Kehrig mersenneforum maximal gap 1854
29. "primitive divisors" algebraic number fields Schinzel A^n - B^n Gaussian integers exceptions list

Searches attempted but refused because the shared search budget was exhausted (4, not counted):

30. Wolstenholme Wilson primes search limit Booker Hathi Mossinghoff Trudgian Vandiver
31. prime k-tuplets records 2026 pzktupel largest known
32. Journal of Integer Sequences 2025 primes computation independent researcher OEIS sequence extended
33. multiplicative order of 2 modulo p distribution computation Artin constant numerical primes up to

**Total executed: 29 searches** (the requirement was at least 18), plus roughly 75 direct page fetches of primary sources (arXiv abstract pages, Wikipedia, project pages, news articles). Topics 30 to 33 were partly recovered by fetching known pages directly (Wikipedia pages for Wilson and Wolstenholme primes, pzktupel.de, the JIS and Integers volume indexes, arXiv:2502.19601).
