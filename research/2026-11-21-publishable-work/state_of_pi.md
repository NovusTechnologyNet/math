# State of research on the number pi (as of 21 November 2026)

Reading conventions used throughout these notes:

- Evidence labels: **[PR]** peer-reviewed publication; **[PP]** preprint (arXiv, Zenodo, GitHub) not confirmed as refereed; **[REF]** reference site (Wikipedia, MathWorld, OEIS, numberworld.org); **[PRESS]** press, vendor or blog claim.
- "2026 flag": the item is dated 2026 and rests only on the web pages retrieved in this session. Nothing dated after mid-2026 could be cross-checked against independent knowledge, and several 2026 items are AI-produced claims that their own sources call unverified. Treat every 2026-flagged item as provisional.
- The web search budget for this research run was exhausted after 42 executed searches (it is shared with the other research threads). The later part of the work used direct fetches of primary pages (arXiv abstracts, numberworld.org, Wikipedia, MathWorld, GitHub, journal pages). Venue-by-venue checks of some journals could not be completed; see the Gaps sections.

## 1. Computation of all digits: record, limits, Chudnovsky, faster series, algorithm papers

### Takeaway
The record is still 314 trillion decimal digits (StorageReview, y-cruncher, Chudnovsky series, run 31 July to 18-19 November 2025, about 110 days); the y-cruncher records page updated 25 October 2026 lists no later pi record. The binding constraints are storage capacity, storage bandwidth and run reliability, not the formula: series with more digits per term than Chudnovsky exist on paper (Borwein class number 2 and 4, Bagis-Glasser, Campbell) but have algebraic-irrational coefficients and none is used by y-cruncher, whose only pi formulas are Chudnovsky and Ramanujan.

### Cited Findings

Record and its status
- **[PRESS, primary vendor report]** 314,000,000,000,000 digits; start 31 July 2025, end 18 November 2025; wall time 9,463,226 s (about 109.5 days); y-cruncher v0.8.6.9545, Chudnovsky; one 2U Dell PowerEdge R7725 with 2 x AMD EPYC 9965 (384 cores), 1.5 TB DDR5, 40 x 61.44 TB Micron 6550 Ion NVMe (34 drives, about 2.1 PB, as y-cruncher swap in JBOD without redundancy; 6 in software RAID10 for output). Peak logical disk usage 1.43 PiB; largest checkpoint 774 TiB; 132 PiB read and 112 PiB written in total; about 7.3 PB written per drive; average power about 1,600 W; 4,305 kWh total. Article dated 11 December 2025. — [StorageReview](https://www.storagereview.com/review/storagereview-sets-new-pi-record-314-trillion-digits-on-a-dell-poweredge-r7725)
- **[REF]** numberworld.org lists the record as completed 19 November 2025, announced 11 December 2025, holders Kevin O'Brien, Divyansh Jain, Brian Beeler (StorageReview), 2 x AMD Epyc 9965, 1.5 TB, 110 days compute. The site's front page has no 2026 news items; latest y-cruncher is v0.8.7 Build 9547 (23 November 2025). — [numberworld.org y-cruncher](http://www.numberworld.org/y-cruncher/)
- **[REF, 2026 flag]** The y-cruncher records page was updated 25 October 2026 and still shows 314 trillion as the pi record. 2026 records on that page are for other constants only: Log(10) 2.5 trillion (6 January 2026), Gamma(1/5) 300 billion (28 July 2026), Log(2) 3.3 trillion (25 October 2026), Sqrt(11) 3 trillion (27 February 2026). — [y-cruncher records](https://numberworld.org/y-cruncher/records.html)
- **[PRESS, 2026 flag]** Guinness World Records published a news item on 1 June 2026 crediting StorageReview and Micron (with Dell and AMD) with "most accurate value of pi". Its headline says "340 trillionth digit" but the body says 314 trillion; the headline appears to be an error, not a new record. — [Guinness World Records](https://www.guinnessworldrecords.com/news/commercial/2026/6/pi-high-computing-achievement-technology-companies-calculate-pi-to-340-trillionth-digit)
- **[REF]** Record chain 2019-2025, all with y-cruncher and Chudnovsky: 31.4 trillion (Iwao/Google, March 2019), 50 trillion (Mullican, January 2020), 62.8 trillion (Grisons, 14 August 2021), 100 trillion (Iwao/Google, 2022), 105 trillion (StorageReview, 14 March 2024), 202 trillion (StorageReview, 28 June 2024), 300 trillion (Linus Media Group and Kioxia, 2 April 2025), 314 trillion (StorageReview, 2025). — [Wikipedia: Approximations of pi](https://en.wikipedia.org/wiki/Approximations_of_pi); [Wikipedia: Chudnovsky algorithm](https://en.wikipedia.org/wiki/Chudnovsky_algorithm)
- **[REF]** The 300 trillion run (2 x AMD Epyc 9684X, 3.0 TB RAM, y-cruncher v0.8.5.9543) ran 19 August 2024 to 2 April 2025: 225 days including about 50 days of downtime from power and cooling failures. The 314 trillion run was a single contiguous run with no interruptions, StorageReview's third attempt at one. — [y-cruncher news 2025](https://numberworld.org/y-cruncher/news/2025.html)

What limits such runs
- **[PRESS]** StorageReview attributes the record to the storage layer (40 NVMe bays reaching up to about 280 GB/s in aggregate) and compares energy: about 4,305 kWh for 314 trillion against an estimated 33,600 kWh for the 300 trillion run on a shared-storage cluster. — [StorageReview](https://www.storagereview.com/review/storagereview-sets-new-pi-record-314-trillion-digits-on-a-dell-poweredge-r7725); [Tom's Hardware](https://www.tomshardware.com/pc-components/storage/pi-calculating-record-shattered-at-314-trillion-digits-with-a-four-month-run-on-a-single-server-storagereview-retakes-the-crown-thanks-to-storage-bandwidth)
- **[REF]** Yee's comment on the record: long runs normally depend on checkpoint-restart to survive outages; he estimates that waiting for faster hardware will soon beat starting a computation, on a roughly 2-3 year horizon, with storage scaling as the key factor. He also states that y-cruncher development is on hiatus (maintenance only; major algorithm redesigns on hold). — [y-cruncher news 2025](https://numberworld.org/y-cruncher/news/2025.html)
- **[REF]** Software ceilings: v0.8.4 (February 2024) raised the hard limit to 108 x 10^15 decimal digits; v0.8.5 (July 2024) allows up to 500 trillion digits without developer authorization. The swap-mode radix conversion was rewritten with checkpointing (v0.8.4); the large-multiplication algorithms were rewritten in 2023 (VT3, N63; Hybrid NTT, N64, C17 and VST removed). No 2023-2025 entry mentions GPU or distributed computing. — [y-cruncher version history](https://numberworld.org/y-cruncher/version_history.html)
- **[REF]** Record rules: two computationally independent computations with matching digits, or, for pi only, one Chudnovsky or Ramanujan run in swap mode with hexadecimal output plus a BBP-formula spot check of the final hex digits. — [y-cruncher records](https://numberworld.org/y-cruncher/records.html)
- **[REF]** Bellard's 2009 record FAQ already described the computation as I/O bound, so more processing power (including GPUs) would not help much. — [Bellard FAQ](https://www.bellard.org/pi/pi2700e9/faq.html)

Why Chudnovsky is used
- **[REF]** The Chudnovsky series (1988) is a Ramanujan-Sato series built on d = -163 and j((1+i sqrt(163))/2) = -640320^3; consecutive terms shrink by a factor with log10 about 14.18, so about 14 digits per term; with binary splitting the cost is O(n (log n)^3). — [Wikipedia: Chudnovsky algorithm](https://en.wikipedia.org/wiki/Chudnovsky_algorithm)
- **[REF]** Yee's notes: AGM-type algorithms have the better asymptotic complexity, O(n log(n)^2), against O(n log(n)^3) for series, but the AGM's constant factor is large because every iteration needs full precision, so Chudnovsky with binary splitting is faster in practice. — [numberworld.org notes](https://numberworld.org/notes.html)
- **[REF]** Wikipedia adds that iterative algorithms are used less for records because they are memory-intensive. — [Wikipedia: Approximations of pi](https://en.wikipedia.org/wiki/Approximations_of_pi)
- **[REF]** y-cruncher's formula page (updated 25 October 2023) lists exactly two pi formulas, Chudnovsky (1988) and Ramanujan (1910), both O(n log(n)^3). — [y-cruncher formulas](https://numberworld.org/y-cruncher/internals/formulas.html)

Series claimed to be faster than Chudnovsky
- **[REF]** Borwein series with class number 2 (1989) give about 25 digits per term, and class number 4 (1993) about 50 digits per term. — [Wikipedia: Borwein's algorithm](https://en.wikipedia.org/wiki/Borwein%27s_algorithm)
- **[PP]** Campbell, "An extension of the Chudnovsky algorithm" (arXiv:2403.07291, March 2024, submitted for publication): states that the previous record was a Bagis-Glasser extension at about 110 digits per term and gives a series with about 153 digits per term. Its coefficients involve nested radicals; the author offers a PARI/GP implementation, and no benchmark against y-cruncher is reported. — [arXiv:2403.07291](https://arxiv.org/abs/2403.07291)
- **[PP, to appear in J. Number Theory per arXiv comments]** Campbell, "On a Ramanujan-type series associated with the Heegner number 163" (arXiv:2402.08485): proves a 2013 Bagis-Glasser conjecture and obtains an infinite family of series for 1/pi generalizing the Chudnovsky algorithm. — [arXiv:2402.08485](https://arxiv.org/abs/2402.08485)
- **[PP, 2026 flag]** Mendusic, "Class-Number-One Cubic Fricke Companions on Gamma_0(2)+ and an Exact Chudnovsky Bridge" (arXiv:2607.05028, 6 July 2026): classifies series for D = -11, -19, -43, -67, -163 and identifies the D = -163 case as a level-two transport of the Chudnovsky form; makes no speed claim. — [arXiv:2607.05028](https://arxiv.org/abs/2607.05028)

Yee's notes and algorithm work
- **[REF]** Binary splitting page (updated 12 October 2023): y-cruncher has four binary-splitting implementations; GCD factorization (keeping prime factorizations to cancel common factors globally) is reported to give 20-30% speedups for Chudnovsky pi, but y-cruncher does not implement it. Cost is tied strongly to polynomial degree, and shifting adjacent terms can cut cost (one example falls from 8.656 to 5.771). — [y-cruncher binary splitting](https://numberworld.org/y-cruncher/internals/binary-splitting.html)
- **[REF]** A recursion library page (updated May 2024) dumps the binary-splitting recursions y-cruncher uses. — [Binary Splitting Recursion Library](https://numberworld.org/y-cruncher/internals/binary-splitting-library.html)
- **[PP, technical paper hosted by the University of Illinois]** Yee and Kondo, "10 Trillion Digits of Pi": parallel shared-memory binary splitting; 5 trillion digits in 90 days, 10 trillion in 371 days. — [University of Illinois IDEALS](https://ideals.illinois.edu/items/28571/bitstreams/96266/data.pdf)
- **[REF]** Formula improvements that did change practice in 2023-2025 were for other constants: Jorge Zuniga's formulas for Log(2), Log(3), Log(5), Zeta(3), Catalan and the lemniscate constant (v0.8.3-v0.8.6), and a Zeta(5) formula by Zhi-Wei Sun that Zuniga converted into a y-cruncher custom formula, nearly twice as fast as the previous best (January 2025). In May 2025 Yee noted a new class of fastest log(x) formulas from Zuniga that he had not yet worked out how to implement generally. — [y-cruncher version history](https://numberworld.org/y-cruncher/version_history.html); [y-cruncher news 2025](https://numberworld.org/y-cruncher/news/2025.html)

### Inferences
- No series is known to beat Chudnovsky for pi in practice. The higher-class-number series gain digits per term by replacing rational coefficients with algebraic irrationals (quadratic, quartic or nested radicals), which raises the cost per term in binary splitting; the absence of any such formula from y-cruncher's pi list, despite Yee actively adopting faster formulas for other constants, supports this. This is an inference from the sources above, not a statement found in one source.
- The one documented, unimplemented algorithmic gain for record pi runs is GCD factorization in binary splitting (20-30% per Yee). With y-cruncher development on hiatus, this is unlikely to be picked up by the author soon.
- Setting a pi digit record is a hardware and operations project (about 2 PB of fast flash for months); it is not a route to a mathematical publication, and the published outputs are vendor write-ups.

### Gaps
- Could not confirm whether any pi record attempt beyond 314 trillion finished between 25 October and 21 November 2026; numberworld.org and Guinness show none.
- Found no 2020-2026 peer-reviewed paper on GPU or distributed all-digit pi computation, out-of-core multiplication, or radix conversion specific to pi; the search on this point returned only cryptography-oriented GPU NTT papers. The search budget ran out before a second pass.
- Did not find a source that benchmarks a class-number-2 or higher series against Chudnovsky inside the same binary-splitting framework.
- Digits-per-term figures for Ramanujan-Sato levels are not given on the Wikipedia page for that topic.

## 2. New formulas for pi, 2015-2026

### Takeaway
New pi formulas of the last decade are almost all of theoretical or structural interest, not computational: none displaces Chudnovsky. The live activity is in proving and classifying formulas (WZ methods, Ramanujan-Sato levels, conservative matrix fields) and, in 2025-2026, in AI-assisted harvesting, unification and proof of formulas.

### Cited Findings

Saha-Sinha series (2024)
- **[PR]** Saha and Sinha, "Field Theory Expansions of String Theory Amplitudes", Phys. Rev. Lett. 132, 221601 (2024). The series has a free parameter lambda; its sum is independent of lambda but its convergence rate is not; lambda to infinity recovers the Gregory (Madhava-Leibniz) series. — [MathWorld: Saha-Sinha Formula](https://mathworld.wolfram.com/Saha-SinhaFormula.html)
- **[PRESS]** The authors do not claim it is the fastest pi series; the claim is faster convergence than the Madhava series (Scientific American: at lambda = 3 about four terms reach within 0.01 of pi, where the Madhava series needs roughly 100). Some mathematicians criticized the publicity; a MathOverflow thread by Timothy Chow (26 June 2024) asked whether the series was new. — [IISc](https://www.iisc.ac.in/events/iisc-physicists-find-a-new-way-to-represent-pi/); [Scientific American](https://www.scientificamerican.com/article/string-theorists-accidentally-find-a-new-formula-for-pi/); [Peter Woit's blog](https://math.columbia.edu/~woit/wordpress/?p=14001)
- **[PR]** Rosengren, "String theory amplitudes and partial fractions", Ramanujan J. 67, 26 (2025): rigorous proofs and generalizations of the Saha-Sinha expansions by limits of finite partial fractions. — [arXiv:2409.06658](https://arxiv.org/abs/2409.06658); [Chalmers record](https://research.chalmers.se/en/publication/546007)
- Verdict: theoretical interest; not competitive for computation.

Ramanujan Machine and conservative matrix fields
- **[PR]** The Ramanujan Machine (Raayoni et al.) appeared in Nature in 2021; it generates continued-fraction conjectures for constants by numerical matching, without proofs; several conjectures were then proved by the community. — [Nature](https://www.nature.com/articles/s41586-021-03229-4); [arXiv:1907.00205](https://arxiv.org/abs/1907.00205v3)
- **[PP]** Elimelech et al. (2023) introduced conservative matrix fields (CMFs), which unify many formulas and yield new ones and relations between constants. — [arXiv:2308.11829](https://arxiv.org/abs/2308.11829)
- **[PR, NeurIPS 2025]** Raz, Shalyt et al., "From Euler to AI: Unifying Formulas for Mathematical Constants": an LLM pipeline (GPT-4o per press) harvested 385 validated pi formulas from 455,050 arXiv papers; relations were proved between 360 (94%), and 166 (43%) derive from a single CMF. — [NeurIPS proceedings](https://papers.neurips.cc/paper_files/paper/2025/hash/b394adff21327520268aaf565b63414c-Abstract-Conference.html); [arXiv:2502.17533](https://arxiv.org/abs/2502.17533)
- **[PRESS, 2026 flag]** Scientific American (13 March 2026): 43% of known pi formulas descend from one CMF, 51% sit in broader clusters still being worked out, 6% are orphans; open questions include whether a richer CMF captures all formulas. David Bailey summarized the same result on Pi Day 2026. — [Scientific American](https://www.scientificamerican.com/article/mathematicians-find-one-pi-formula-to-rule-them-all/); [Math Scholar](https://mathscholar.org/2026/03/researchers-use-ai-to-catalog-pi-formulas/)
- **[PP, math.GM, 2026 flag]** Chao Wang, "A Rigorous Proof of a Ramanujan Machine Identity for -pi/4 via Exact Recurrence Solving" (arXiv:2601.08461, January 2026, revised April 2026): single-author proof of one conjectured polynomial continued fraction via an explicit recurrence solution and a Beta integral. — [arXiv:2601.08461](https://arxiv.org/abs/2601.08461)
- **[REF, 2026 flag]** The Ramanujan Machine site invites the public to run its code, propose proofs and develop algorithms, with results credited by name. It ran a "Ramanujan Challenge" from 1 July to 1 August 2026: explicit formulas for constants, checkable numerically, to be proved; submissions ranked by format (Lean/Rocq/Isabelle first, then CAS derivations, then human-readable proofs). — [ramanujanmachine.com](https://www.ramanujanmachine.com/); [Ramanujan Challenge](https://www.ramanujanmachine.com/ramanujan-challenge/)
- **[PP, 2026 flag]** Challenge results paper (Sorani et al., arXiv:2610.40551, 29 October 2026): 10 problems (8 questions, 2 open conjectures); pi appears in a continued fraction for 6/(3-pi), a limit equal to pi+e, a fast limit for sqrt(10005)/pi and a conjectured integral equal to 4 pi^2/85. 228 submissions; participants included amateur mathematicians, a person without higher mathematical education, young independent researchers and a high-school student. 54 of 137 natural-language proofs were judged correct. The pi^2 conjecture received a correct Lean-formalized proof; the second conjecture (on Apery's bound for zeta(3)) remains open. Natural-language proofs backed by CAS verification were correct 52% of the time, by Lean 38%, by numerical checks only 6%. — [arXiv:2610.40551](https://arxiv.org/abs/2610.40551)

Ramanujan-type and Ramanujan-Sato series (Guillera, Zudilin, Cooper, Chan, Sun, Au, Campbell)
- **[REF]** Ramanujan-Sato levels and their discoverers: level 5 (Chan and Cooper 2012), 6A (Chan, Tanigawa, Yang, Zudilin), 6B (Sato 2002), 6C (Chan, Chan, Liu 2004), 6D (Chan and Verrill 2009), 7 (Cooper 2012), part of 8 (Almkvist and Guillera 2012), 10 (Yang; Chan and Cooper), 11 (Cooper). The article's newest reference is from 2013. — [Wikipedia: Ramanujan-Sato series](https://en.wikipedia.org/wiki/Ramanujan%E2%80%93Sato_series)
- **[PP]** Guillera, "The fastest series for 1/pi due to Ramanujan. Proofs from modular polynomials" (arXiv:1911.03968, v13 July 2025), with a Maple program for automatic proofs; Guillera, "Proof of Chudnovskys' series for 1/pi" (arXiv:2003.06668, 6 pages); Guillera, "WZ proofs of Ramanujan-type series (via 2F1 evaluations)" (arXiv:2001.08104, revised December 2023). — [arXiv:1911.03968](https://arxiv.org/abs/1911.03968); [arXiv:2003.06668](https://arxiv.org/abs/2003.06668); [arXiv:2001.08104](https://arxiv.org/abs/2001.08104)
- **[PR]** Kam Cheong Au, "Wilf-Zeilberger seeds and non-trivial hypergeometric identities", J. Symbolic Comput. 130 (2025) 102421: a systematic way to generate WZ pairs; proves conjectures of Sun, Guillera and Zhao, including two Ramanujan-type 1/pi^4 formulas and one 1/pi^3 formula. Follow-ups: q-analogues (arXiv:2403.04555) and harmonic-number series (arXiv:2602.08721, 2026 flag). — [arXiv:2312.14051](https://arxiv.org/abs/2312.14051); [arXiv:2403.04555](https://arxiv.org/abs/2403.04555v3); [arXiv:2602.08721](https://arxiv.org/html/2602.08721v1)
- **[PP]** Campbell, "Three-parameter generalizations of formulas due to Guillera" (arXiv:2502.15249, February 2025): new rational hypergeometric series for 1/pi^2 with the convergence rates of Guillera's series. — [arXiv:2502.15249](https://arxiv.org/abs/2502.15249)
- **[PP, 2026 flag]** Campbell, Cooper and Ye, "Quadratic irrational analogues of Ramanujan's series for 1/pi" (arXiv:2602.09352, February 2026): classification covering Ramanujan's 17 series and later ones, extended to genus-zero groups Gamma_0(l)+. — [arXiv:2602.09352](https://arxiv.org/abs/2602.09352)
- **[PP, 2026 flag]** Campbell, "On a problem on Ramanujan-Sato series of level 11" (arXiv:2610.00551, 30 September 2026): solves a problem posed by Cooper et al. in 2015 by giving a double binomial sum for the level-11 coefficients. — [arXiv:2610.00551](https://arxiv.org/abs/2610.00551)
- **[PP]** Hemmecke, Paule and Radu (2025): computer-assisted construction of Ramanujan-Sato series for 1/pi. — [JKU research portal](https://research.jku.at/de/publications/computer-assisted-construction-of-ramanujan-sato-series-for-1-ove/)
- **[PP / PR]** Zhi-Wei Sun's conjecture lists: arXiv:1102.5649 (v47, 2014) lists 234 conjectural series, 178 of them for 1/pi, marking which have complete proofs; "Series with summands involving harmonic numbers" (arXiv:2210.07238; published in Combinatorial and Additive Number Theory VI, Springer 2025) poses 70 conjectures from 2022-2023. — [arXiv:1102.5649](https://arxiv.org/abs/1102.5649); [arXiv:2210.07238](https://arxiv.org/abs/2210.07238)

BBP-type and digit-extraction formulas
- **[PP]** Zudilin, "A BBP-style computation for pi in base 5" (arXiv:2409.10097, September 2024): a short note on extracting base-5 digits of pi from a given position. — [arXiv:2409.10097](https://arxiv.org/abs/2409.10097)
- **[PP]** Cloitre (2025): proof of a BBP-type formula for pi^2 in the golden-ratio base (found empirically in 2004), and a BBP-type identity for the remainder of the Madhava-Gregory-Leibniz series. — [arXiv:2508.03743](https://arxiv.org/abs/2508.03743v1); [arXiv:2507.20428](https://arxiv.org/pdf/2507.20428)
- **[PR]** Kristensen and Mathiasen, "BBP-type formulas: an elementary approach", J. Number Theory (2023), reports a new BBP-type formula involving pi. — [Bohrium record](https://www.bohrium.com/paper-details/bbp-type-formulas-an-elementary-approach/864980214101311497-975)
- **[PP]** Plouffe, "A formula for the n-th decimal digit or binary of pi and powers of pi" (arXiv:2201.12601, 2022): uses asymptotics of Bernoulli and Euler numbers; limited by the cost of computing huge Bernoulli numbers, and Wikipedia notes it effectively computes the preceding digits. — [arXiv:2201.12601](https://arxiv.org/abs/2201.12601); [Wikipedia: BBP formula](https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula)
- **[REF]** No systematic method for finding BBP-type formulas is known; they are found experimentally. — [Wikipedia: BBP formula](https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula)

Machin-like (arctangent) formulas
- **[PP]** Craig-Wood, "Constrained PSLQ Search for Machin-like Identities Achieving Record-Low Lehmer Measures" (arXiv:2508.08307, August 2025; v2 September 2026; math.NT with cs.AI cross-list): new 5-term and 6-term relations with Lehmer measures 1.4572 and 1.3291; the 5-term record had stood since Stormer (1896). — [arXiv:2508.08307](https://arxiv.org/abs/2508.08307)
- **[PP]** Abrarov and collaborators (2025) and Alferov (2023) give iterative and recurrent constructions of Machin-like formulas. — [arXiv:2509.25221](https://arxiv.org/pdf/2509.25221); [Wikipedia: Machin-like formula](https://en.wikipedia.org/wiki/Machin-like_formula)

Formalization
- **[REF, 2026 flag]** Mathlib contains a definition of the Chudnovsky series, but the identity that it equals 1/pi is an unsolved item on the lean-eval leaderboard (the Lean statement is still marked with sorry); the suggested route is Milla's complex-analytic proof. — [lean-lang.org eval](https://lean-lang.org/eval/problems/chudnovsky_formula_for_pi_inv/)
- **[PP]** Milla, "A detailed proof of the Chudnovsky formula with means of basic complex analysis" (arXiv:1809.00533, v6 2021), plus a follow-up in the Ramanujan Journal on determining the coefficients efficiently. — [arXiv:1809.00533](https://arxiv.org/abs/1809.00533v2)

Physics-derived formulas
- **[PR]** Friedmann and Hagen (2015) derived the Wallis product from the hydrogen atom (J. Math. Phys.). — [AIP Publishing](https://publishing.aip.org/publications/latest-content/new-derivation-of-pi-links-quantum-physics-and-pure-math/)

### Inferences
- For each formula family the verdict on speed: Saha-Sinha, Ramanujan Machine continued fractions, BBP variants in other bases, Plouffe 2022 and the physics-derived formulas are of theoretical interest; Machin-like records matter only for arctangent-based methods, which are not used for all-digit records; Ramanujan-Sato and higher-class-number series are the only ones in the same efficiency class as Chudnovsky and none is shown to beat it in practice.
- The productive, repeatable activity is "prove a numerically verified identity" (Sun's lists, Guillera's conjectures, Ramanujan Machine output). Au's 2025 paper and the 2026 Challenge show that this task is now within reach of computer algebra plus AI assistance, and that formal or CAS verification is what separates correct from incorrect submissions.

### Gaps
- Could not establish a current count of which Ramanujan Machine conjectures remain unproven; the site's community-results page returned a 404 and the Results pages were not retrieved.
- The current proof status of each of Sun's 234 series is marked only inside the PDF, which was not read.
- Did not find a 2024-2026 Guillera or Zudilin paper with a new pi series; the targeted search was cut off by the budget.
- "Formulas found by AI" in the strict sense (a new pi formula discovered, not harvested or proved, by an LLM) were not found.

## 3. Open problems: normality, irrationality measure, algebraic independence

### Takeaway
Normality and the algebraic independence of pi and e remain untouched: nothing found for 2020-2026 beyond conditional statements. The irrationality measure is the opposite: after the refereed bound 7.1032 (Zeilberger-Zudilin, 2020) stood for six years, autumn 2026 brought a small AI-assisted improvement (7.1019, preprint) and then an OpenAI preprint claiming the exact value 2, which reference sources describe as unverified by independent specialists.

### Cited Findings

Normality
- **[REF]** It is not known whether pi, e, sqrt(2) or ln 2 is normal in any base; it has not even been proven that every digit occurs infinitely often in their decimal expansions; no irrational algebraic number is proven normal in any base. — [Wikipedia: Normal number](https://en.wikipedia.org/wiki/Normal_number)
- **[REF, 2026 flag]** Wikipedia's list of unsolved problems still lists "Is pi a normal number" and "Are all irrational algebraic numbers normal", with no 2026 qualifier. — [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- **[PRESS on PR work]** Bailey and Crandall (2001): if their "Hypothesis A" on the equidistribution of orbits attached to BBP-type formulas holds, then pi and log 2 are normal in base 2; Bailey stressed this is not a proof. — [Berkeley Lab](https://www2.lbl.gov/Science-Articles/Archive/pi-random.html)
- **[PR]** Bailey and Borwein, "Pi Day is upon us again and we still do not know if Pi is normal", Amer. Math. Monthly 121(3), 2014, reviews the state of the question. — [Monthly PDF](https://www.cs.umb.edu/~eb/piday/MonthlyMarch2014.pdf)
- **[PP]** A 2025 preprint on constructing "transcendentally normal" numbers notes that normality of specific constants such as e and pi remains wide open. — [arXiv:2508.09319](https://arxiv.org/html/2508.09319v1)
- **[REF, 2026 flag]** OpenAI's October 2026 release (721 manuscripts in 373 families per its README; 722 papers on 377 problems per Bailey's blog) contains one pi result (the irrationality exponent) and a claimed irrationality proof for Catalan's constant; a scan of its contents file found no entry on normality, on pi+e or on algebraic independence of pi and e. — [openai/math CONTENTS.md](https://raw.githubusercontent.com/openai/math/main/CONTENTS.md)

Irrationality measure (irrationality exponent) of pi
- **[PR]** Zeilberger and Zudilin: mu(pi) <= 7.103205334137..., Moscow J. Comb. Number Theory 9(4), 2020, improving Salikhov's 7.606308 (2008) by a variant of his integral and the Almkvist-Zeilberger algorithm. — [arXiv:1912.06345](https://arxiv.org/abs/1912.06345); [MSP journal PDF](https://msp.org/cnt/2020/9-4/moscow-v9-n4-p06-s.pdf)
- **[REF]** If the Flint Hills series converges then mu(pi) <= 5/2 (Alekseyev 2011); Meiburg (2022) proved that mu(pi) < 5/2 is sufficient for convergence. The boundary case mu(pi) = 5/2 is not settled by either criterion. — [Wikipedia: Irrationality measure](https://en.wikipedia.org/wiki/Irrationality_measure); [Wikipedia: Flint Hills series](https://en.wikipedia.org/wiki/Flint_Hills_series)
- **[PP, 2026 flag]** Yufei Bai, "The irrationality measure of pi is at most 7.101862832357" (arXiv:2609.11276, 10-11 September 2026): two independent numerator exponents in the Zeilberger-Zudilin integral, both set to 1857/2785; improvement about 0.00134 (0.019%). The paper carries a generative-AI disclosure: OpenAI's GPT-5.6 Sol and GPT-6 Astra assisted throughout with parameter exploration, proof development and checking, computation and drafting; the author takes responsibility for the mathematics. It proves only a local minimum of its auxiliary bound, not global optimality. Single author, no affiliation shown, no journal reference. — [arXiv:2609.11276](https://arxiv.org/abs/2609.11276)
- **[PP, 2026 flag, unverified]** OpenAI, "The irrationality exponent of pi is 2" (dated 24 September 2026, GitHub preprint, author line "OpenAI"): claims that for every nu > 2, |pi - p/q| >= q^(-nu) for all sufficiently large q, with an ineffective threshold; corollary: the Flint Hills series converges. It does not claim bounded partial quotients. Method: an interpolation-determinant argument, not an extension of the Hata-Salikhov-Zeilberger-Zudilin integrals. The paper itself notes that an earlier convergence claim by Mantzakouras and Lopez Zapata was withdrawn in September 2026 and that Carella's claim of exponent 2 contains a sign obstruction in a stronger assertion. — [OpenAI preprint PDF](https://github.com/openai/math/blob/main/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf)
- **[REF, 2026 flag]** Verification status of that claim: MathWorld (page updated 20 November 2026) records that OpenAI announced mu(pi) = 2, attributes it to an unreleased internal model, and says that as of 7 October 2026 no independent specialist verification of the full proof had been reported; it keeps the established bound 7.1032 separate. Wikipedia calls it an unverified proof. The community tracker VibeMathed lists it as "Candidate (review pending)", not refereed, with a Lean comparator statement present in the release but not rebuilt by the tracker. — [MathWorld: Irrationality Measure](https://mathworld.wolfram.com/IrrationalityMeasure.html); [Wikipedia: Irrationality measure](https://en.wikipedia.org/wiki/Irrationality_measure); [VibeMathed](https://vibemathed.com/problem/irrationality-exponent-of-pi)
- **[REF, 2026 flag]** The OpenAI repository describes its contents as raw research data at different stages of verification, with about 42% of top-line results formalized in Lean (300 of 719 on 7 October 2026), and warns that unformalized results may have issues. On 7 October 2026 three manuscripts (on Hodge-type conjectures) were withdrawn for a sign error and 14 others repaired. A Lean scope page for the pi result exists (it states the exponent-2 theorem; the Flint Hills corollary is outside the formalized statement). — [openai/math README](https://raw.githubusercontent.com/openai/math/main/README.md); [openai/math history](https://raw.githubusercontent.com/openai/math/main/history.md); [Lean doc 017](https://raw.githubusercontent.com/openai/math/main/lean/docs/017.md)
- **[PP, 2026 flag]** G. V. Chudnovsky, "Irrationality exponents of logarithmic numbers: Values, quotients, and graded approximation" (arXiv:2610.28079, 20 October 2026) states that it starts from the interpolation and determinant method of the OpenAI pi preprint and proves, among other things, an upper bound of 3 for ratios of logarithms of multiplicatively independent positive rationals; it ships a Lean supplement. — [arXiv:2610.28079](https://arxiv.org/abs/2610.28079)
- **[PRESS, 2026 flag]** David Bailey's summary (7 October 2026, updated 25 October): OpenAI released 722 papers on 377 problems on 6 October 2026, including the pi exponent claim, a claimed irrationality proof for Catalan's constant, and zero-free-strip results short of the Riemann hypothesis; only part has been machine-checked and mathematicians have not yet sorted major advances from incremental ones. — [Math Scholar](https://mathscholar.org/2026/10/openai-stuns-mathematicians-with-722-new-papers/)

Irrationality measure of pi^2 (zeta(2)) and neighbours, autumn 2026
- **[PP, 2026 flag]** Niedbala Giraudin: mu(zeta(2)) <= 5.0193784 (arXiv:2610.02912, 2 October 2026), improving Zudilin's 5.095412 (2014); the abstract reports an intermediate, machine-checked 5.0495243 made public by J. Kleid in September 2026. Constants certified in ball arithmetic with ancillary Python scripts. — [arXiv:2610.02912](https://arxiv.org/abs/2610.02912)
- **[PP, 2026 flag]** Leibtag, Barkan, Kalisch, Weinbaum, Shalyt, Kaminer, "New Directions in Irrationality" (arXiv:2610.27799, 20 October 2026): a CMF framework unifying Apery-type constructions; mu(zeta(2)) < 4.62675, mu(zeta(3)) < 5.4197, and linear independence of 1, zeta(3), zeta(4) over Q. — [arXiv:2610.27799](https://arxiv.org/abs/2610.27799)
- **[REF, 2026 flag]** MathWorld also lists further October 2026 claims without independent verification (Casper on rational arctangents; Zhang and Li on a quadratic-field criterion) and a Zenodo preprint claiming zeta(5) is irrational (Fauzan). — [MathWorld: Irrationality Measure](https://mathworld.wolfram.com/IrrationalityMeasure.html)

Algebraic independence and transcendence
- **[REF]** Schanuel's conjecture would imply that e and pi are algebraically independent and that e+pi, e*pi, pi^e, pi^pi, e^e are transcendental; it is unproven. Known: Lindemann-Weierstrass (pi and e transcendental), Gelfond-Schneider (e^pi transcendental), Baker. — [Wikipedia: Schanuel's conjecture](https://en.wikipedia.org/wiki/Schanuel%27s_conjecture)
- **[PP citing PR]** Nesterenko's theorem: pi and e^pi are algebraically independent; not even irrationality is known for pi+e, pi*e, pi^e, pi^pi, e^e, ln pi. — [arXiv:1310.7289](https://arxiv.org/abs/1310.7289v3); [nLab: Schanuel's conjecture](https://ncatlab.org/nlab/show/Schanuel%27s+conjecture)
- **[REF, 2026 flag]** Still listed as unsolved: whether pi and e are algebraically independent; which combinations such as e+pi and e*pi are transcendental; the irrationality measure of pi and gamma; whether gamma and Catalan's constant are irrational. — [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- **[PP]** 2025 work is on variants only: Bertolin and Waldschmidt propose Schanuel-type conjectures for elliptic and quasi-elliptic functions. — [arXiv:2504.14048](https://arxiv.org/pdf/2504.14048)

Continued fraction of pi
- **[REF, 2026 flag]** Neither the Khinchin limit nor the Levy limit is proven for pi's partial quotients. Computed terms: 30,113,021,586 (S. Fahad, 27 April 2021) and 653,520,000,000 (M. Frank, 1 November 2025), with largest partial quotient 845,188,380,288. — [MathWorld: Pi Continued Fraction](https://mathworld.wolfram.com/PiContinuedFraction.html)

### Inferences
- Classification: normality of pi (any base), algebraic independence of pi and e, and irrationality of pi+e are famous and out of reach; no partial result was found and the 2026 AI release does not claim any of them.
- The irrationality exponent of pi has moved from "slow incremental bounds" to "claimed solved, pending verification". If the OpenAI proof stands, incremental bounds for mu(pi) (Bai's 7.1019) lose their value, while the neighbouring questions (effective versions, bounded partial quotients, exponents of pi^2, zeta(3), logarithm ratios) become the active frontier, as the Chudnovsky and Leibtag et al. preprints already show. If it fails, the parameter-optimization route that Bai used with AI assistance remains a realistic small project.
- Bai's and Niedbala Giraudin's preprints are direct evidence that single authors, with AI and computer-algebra support, produced new numerical irrationality bounds in 2026; neither is refereed yet.

### Gaps
- Could not retrieve the New York Times, The Verge or New Scientist coverage of the OpenAI release that Wikipedia cites, so expert reactions specific to the pi result were not read first-hand.
- No statement was found, as of 21 November 2026, that any named specialist has verified or refuted the OpenAI pi proof; the latest dated status found is 7 October 2026 (MathWorld, VibeMathed).
- Whether the Lean comparator proof for the pi theorem builds without extra axioms was not independently confirmed by any source read.
- No 2020-2026 progress on Hypothesis A or on digit-frequency lower bounds for pi was found; the dedicated search was cut off by the budget.

## 4. Statistical studies of the digits

### Takeaway
Published digit statistics stop at 22.4 trillion decimal digits (Trueb 2016, arXiv only) and about 4 trillion hexadecimal digits (Bailey et al. 2012, Experimental Mathematics); no analysis of the 100, 202, 300 or 314 trillion digit datasets was found. Every study is consistent with normality, and the 314 trillion digit dataset is now publicly retrievable, so a larger-scale replication is feasible but offers confirmation, not a new theorem.

### Cited Findings
- **[PP]** Trueb, "Digit Statistics of the First 22.4 Trillion Decimal Digits of Pi" (arXiv:1612.00489, November 2016): frequencies of all 1-, 2- and 3-digit strings in base 10 and base 16; everything consistent with normality; no deviation above four standard deviations. No journal reference on arXiv. — [arXiv:1612.00489](https://arxiv.org/abs/1612.00489)
- **[PR]** Bailey, Borwein, Calude, Dinneen, Dumitrescu and Yee, "An Empirical Approach to the Normality of pi", Experimental Mathematics 21(4), 2012: tests on roughly four trillion hexadecimal digits. — [Project Euclid](https://projecteuclid.org/journals/experimental-mathematics/volume-21/issue-4/An-Empirical-Approach-to-the-Normality-of-%cf%80/em/1356038820.full)
- **[PR]** Bailey, Borwein, Brent and Reisi, "Reproducibility in Computational Science: A Case Study: Randomness of the Digits of Pi", Experimental Mathematics 26(3): reproduces Ganz's specific findings of non-randomness but rejects his conclusion after further statistical analysis. — [eScholarship](https://escholarship.org/uc/item/02w5n10q)
- **[PP]** Roba and Podnieks, "Digits of pi: limits to the seeming randomness II" (arXiv:2504.10394, April 2025): tests 12 constants (one billion digits each, ten billion for pi) against the central limit theorem and the law of the iterated logarithm; reports a null finding within those limits. 22 pages, no journal reference. — [arXiv:2504.10394](https://arxiv.org/abs/2504.10394)
- **[PRESS, 2026 flag]** Backblaze hosts the 314 trillion digit dataset: over 130 TB in 200 GB objects, available on request with credentials and downloadable with rclone; the layout supports partial retrieval. — [Backblaze](https://www.backblaze.com/blog/backblaze-now-serving-314-trillion-digits-of-pi/)
- **[REF]** Wikipedia's Pi article notes that digit analyses (Kanada's and later) are consistent with normality and that the conjecture is neither proven nor disproven. — [Wikipedia: Pi](https://en.wikipedia.org/wiki/Pi)

### Inferences
- Venue pattern: digit-statistics papers that reached a journal did so in Experimental Mathematics and were written by established experimental mathematicians with a methodological point (new test, reproducibility). Pure "we counted more digits" studies (Trueb) stayed on arXiv. A newcomer's replication on 314 trillion digits is plausible as an arXiv note or data paper; a journal would likely require a new statistic or method.
- The practical barrier is data handling (130 TB download, streaming counts), not mathematics. Block-wise counting over partial retrievals makes it feasible without storing the full set.
- A less crowded variant is continued-fraction statistics: 653.52 billion partial quotients were computed in 2025 and the Khinchin and Levy limits are unproven for pi.

### Gaps
- No paper analyzing the 100 trillion (2022), 202 trillion (2024), 300 trillion (2025) or 314 trillion (2025) digit datasets was found; it is possible one exists outside arXiv.
- The file formats (decimal, hexadecimal) and license terms of the Backblaze dataset are not stated on the page read.
- Whether Google's 100 trillion digit dataset is still served publicly was not checked.

## 5. Papers about pi by amateurs, students and independent researchers, 2015-2026, and their venues

### Takeaway
Independent authors do publish on pi, mostly as arXiv preprints, with a minority reaching journals (Ramanujan Journal, Journal of Symbolic Computation, Mathematical Gazette). The recurring successful types are: efficient-formula searches validated by record computations, proofs of conjectured identities, large-scale digit or continued-fraction computations, and short expository notes. In 2026 AI-assisted amateur results became common, and so did warnings about unverified AI-generated manuscripts.

### Cited Findings
- **[PRESS + PP]** Jorge Zuniga, described as an independent civil engineer, found by PARI/GP and LLL search the fastest known series for log 2, log 3, log 5 (and formulas for zeta(3), Catalan and the lemniscate constant) that were adopted in y-cruncher; a 3 trillion digit log 2 run took 42.7 hours against 98.9 days for the 2021 record of 1.5 trillion (about 50x efficiency gain in three years). He then wrote "Fast Ramanujan-type Series for Logarithms", Parts I and II (arXiv:2506.08245, arXiv:2506.10321; June 2025, Part II revised May 2026), proved via WZ certificates. No journal reference listed. — [StorageReview guest post](https://www.storagereview.com/review/the-math-of-performance-stress-testing-hardware-for-math-changing-results); [arXiv:2506.08245](https://arxiv.org/abs/2506.08245); [arXiv:2506.10321](https://arxiv.org/abs/2506.10321)
- **[PP]** Nick Craig-Wood (no affiliation listed): record-low Lehmer measures for 5- and 6-term Machin-like formulas by constrained PSLQ search (arXiv:2508.08307); Wikipedia's BBP article also cites a 2023 Craig-Wood piece on Euler's discovery of two BBP-type formulas. — [arXiv:2508.08307](https://arxiv.org/abs/2508.08307); [Wikipedia: BBP formula](https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula)
- **[PP + PR]** Lorenz Milla: detailed, self-contained proof of the Chudnovsky formula (arXiv:1809.00533, bilingual German and English, six versions 2018-2021), and a follow-up in the Ramanujan Journal on determining the series coefficients. — [arXiv:1809.00533](https://arxiv.org/abs/1809.00533v2)
- **[PP]** Peter Trueb: digit statistics of the 22.4 trillion digit computation of 2016 (arXiv:1612.00489), no affiliation listed, no journal reference. — [arXiv:1612.00489](https://arxiv.org/abs/1612.00489)
- **[PR]** Kam Cheong Au (no affiliation shown on arXiv): WZ-seed proofs of conjectured 1/pi^3 and 1/pi^4 series, J. Symbolic Comput. 130 (2025). — [arXiv:2312.14051](https://arxiv.org/abs/2312.14051)
- **[PP]** Simon Plouffe: n-th digit formula via Bernoulli and Euler numbers (arXiv:2201.12601, 2022). — [arXiv:2201.12601](https://arxiv.org/abs/2201.12601)
- **[PP]** Benoit Cloitre: BBP-type results (arXiv:2507.20428, arXiv:2508.03743; 2025), one proving a formula he found empirically in 2004. — [arXiv:2508.03743](https://arxiv.org/abs/2508.03743v1)
- **[PP, 2026 flag]** Yufei Bai: new upper bound for mu(pi) with disclosed assistance from two OpenAI models (arXiv:2609.11276). — [arXiv:2609.11276](https://arxiv.org/abs/2609.11276)
- **[PP, math.GM, 2026 flag]** Chao Wang: proof of a Ramanujan Machine continued fraction for -pi/4 (arXiv:2601.08461). — [arXiv:2601.08461](https://arxiv.org/abs/2601.08461)
- **[REF, 2026 flag]** M. Frank: 653.52 billion terms of the continued fraction of pi (1 November 2025), cited by MathWorld; S. Fahad: 30 billion terms (2021). — [MathWorld: Pi Continued Fraction](https://mathworld.wolfram.com/PiContinuedFraction.html)
- **[PR]** Mathematical Gazette, 2025: Aritra Bhattacharyya, Note 109.07, a proof of the irrationality of pi using series of circular functions (vol. 109, issue 574, March 2025); Note 109.43, "look-see" proofs of an inequality between e and pi (October 2025; the title's symbols were not fully rendered in the page read); Ludovit Spachal, an article approximating pi with metallic means and the unit hyperbola (issue 575, July 2025). — [Cambridge Core, Note 109.07](https://www.cambridge.org/core/journals/mathematical-gazette/article/10907-a-proof-of-the-irrationality-of-using-series-of-circular-functions/083DB123CEE90E466D4A0AFFB2E6F8B0); [Cambridge Core, Note 109.43](https://www.cambridge.org/core/journals/mathematical-gazette/article/10943-looksee-proofs-that-e/8F9CA3EADCB28DC3FFD0F4677138D828)
- **[PR, outside the date window]** Involve (a journal for student research) published "A new series for pi via polynomial approximations to arctangent" (Bouey, Medina, Meza, 2012). — [Project Euclid](https://projecteuclid.org/journals/involve-a-journal-of-mathematics/volume-5/issue-4/A-new-series-for-pi-via-polynomial-approximations-to-arctangent/10.2140/involve.2012.5.421.full)
- **[PP, 2026 flag]** Ramanujan Challenge 2026: participants included amateurs, a person with no higher mathematical education and a high-school student; one published open conjecture (an integral equal to 4 pi^2/85) received a correct Lean-formalized proof. — [arXiv:2610.40551](https://arxiv.org/abs/2610.40551)
- **[PRESS, 2026 flag]** AI-assisted amateur results outside pi: Liam Price (23, no advanced training) obtained a proof of Erdos problem 1196 from GPT-5.4 Pro; Kevin Barreto (Cambridge undergraduate) recognized it; Lichtman and Tao had to interpret and shorten the AI's initially poor write-up. Earlier, Barreto and Price claimed problem 333, which Erdos had already settled in 1977. — [Scientific American](https://www.scientificamerican.com/article/amateur-armed-with-chatgpt-vibe-maths-a-60-year-old-problem/); [Quanta Magazine](https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/)
- **[PRESS, 2026 flag]** Thomas Bloom reports non-mathematicians posting 100-200 page AI-generated papers that no human has read, and calls this a major problem; Wouter van Doorn, a customer-service worker, made accepted progress on Erdos problem 1102 without AI. — [Quanta Magazine](https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/)

### Inferences
- Venue map from the examples actually found: arXiv math.NT for formula searches, bounds and proofs by independent authors (math.GM when moderators judge the work elementary); Ramanujan Journal and Journal of Symbolic Computation for proofs with real technical content; Mathematical Gazette for short notes; Involve for student work; Experimental Mathematics for computational studies with a methodological point; numberworld.org, MathWorld and OEIS as citable registries for computational records.
- What made the independent contributions stick was external validation: a record computation with independent verification (Zuniga), a WZ certificate or CAS-checkable proof (Au, Zuniga), a Lean proof (Challenge), or an expert co-reader (Price and Barreto with Tao and Lichtman).
- The 2026 reports imply a higher bar for AI-assisted submissions: short, verified, literature-checked results fare well; long unverified AI manuscripts are being ignored.

### Gaps
- The search budget ran out before venue-specific checks of the American Mathematical Monthly, Mathematical Intelligencer, Integers, Journal of Integer Sequences, and Notes on Number Theory and Discrete Mathematics for 2015-2026 pi papers; no examples from those five venues are documented here except the 2014 Monthly survey by Bailey and Borwein cited in section 3.
- Affiliation or amateur status is not stated on arXiv for Craig-Wood, Trueb, Au, Bai, Wang or Cloitre; "independent" is inferred from the missing affiliation, except for Zuniga, whom StorageReview describes explicitly.
- The exact title of Gazette Note 109.43 was not rendered fully by the page read; the description above is approximate.

## 6. Connections between pi and prime numbers as research topics

### Takeaway
The pi-prime links are classical (Euler product for zeta(2), coprimality probability 6/pi^2) and no active research program aimed at pi through primes was found. The live threads are peripheral: zeta-regularized products over primes (equal to 4 pi^2), normality of prime-built constants as a contrast to pi, BBP-type digit extraction and Hypothesis A, and recreational searches for primes among the digits.

### Cited Findings
- **[REF]** zeta(2) = pi^2/6 (Euler 1735); the probability that two random integers are coprime is the product over primes of (1 - 1/p^2) = 6/pi^2; this is a special case of Weil's conjecture on Tamagawa numbers; the functional equation of the zeta function also contains pi explicitly. — [Wikipedia: Pi](https://en.wikipedia.org/wiki/Pi)
- **[PR]** Munoz Garcia and Perez-Marco (Commun. Math. Phys. 277, 2008): the zeta-regularized product over all primes equals 4 pi^2. — [Springer](https://link.springer.com/article/10.1007%2Fs00220-007-0350-z)
- **[PP, 2026 flag]** Krapivsky and Luck, "Zeta-regularization and natural boundaries: Sums and products of integers and primes" (arXiv:2606.24536, June 2026): extends that result to a regularized sum of all primes and to regularized products of integers and primes in the nine imaginary quadratic fields with unique factorization. — [arXiv:2606.24536](https://arxiv.org/abs/2606.24536)
- **[REF]** The Copeland-Erdos constant (concatenated primes) is proven normal in base 10 (1946), and Bailey-Crandall perturbations of Stoneham numbers give explicit normal numbers; pi has no comparable result. — [Wikipedia: Normal number](https://en.wikipedia.org/wiki/Normal_number)
- **[REF]** Digit extraction: the BBP formula (1995/1997) gives hexadecimal digits at arbitrary positions; Bellard's variant is faster; in 1997 Bellard improved Plouffe's any-base n-th digit algorithm from O(n^3 log(n)^3) to O(n^2). — [Wikipedia: BBP formula](https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula); [bellard.org/pi](https://bellard.org/pi/)
- **[PP]** Position records for binary digit extraction: the two-quadrillionth bit (Yahoo Hadoop, 2010), doubling the PiHex position. — [arXiv:1008.3171](https://arxiv.org/pdf/1008.3171)
- **[REF]** Primes among the leading digits of pi (OEIS A005042): prefixes of 1, 2, 6 and 38 digits are prime; the next is a 16,208-digit probable prime found by Ed T. Prothro in 2001; a heuristic argument suggests infinitely many. — [OEIS A005042](https://oeis.org/A005042)
- **[PP]** Other Euler-product items found are not about pi itself: a generalization of Morrie's law and Euler-type products for sinc (arXiv:2403.09698, 2024); Franca and LeClair's contested claim that the Euler product is valid for Re(s) > 1/2 in a Cesaro sense (arXiv:1410.3520); a March 2026 preprint on continuing the Euler product under the Riemann hypothesis (arXiv:2603.28808). — [arXiv:2403.09698](https://arxiv.org/pdf/2403.09698); [arXiv:1410.3520](https://arxiv.org/abs/1410.3520v5); [arXiv:2603.28808](https://arxiv.org/html/2603.28808v1)

### Inferences
- "Pi and primes" is not a recognized active research front for pi itself. A project framed that way has to attach to one of: (i) regularized products and sums over primes (Krapivsky-Luck style), (ii) BBP-type formulas and the dynamics behind Hypothesis A, (iii) computational searches (prime prefixes, digit extraction at record positions), or (iv) expository notes on Euler products evaluating to rational multiples of powers of pi.
- The prime-prefix search has had no new term since 2001; extending the search limit is a concrete computational contribution but belongs in OEIS, not a journal.
- Background knowledge not verified in this session: the Plouffe-Bellard-Gourdon n-th decimal digit algorithms work by computing a pi series modulo small prime powers and recombining, which is the one place where primes enter pi digit extraction directly.

### Gaps
- No research on "prime-indexed series for pi" or new Euler-type prime products for pi from 2020-2026 was found; the one search aimed at it returned only tangential results and a second attempt was blocked by the budget.
- The current verified search limit for the next prime prefix of pi after 16,208 digits is not stated on the OEIS page read (A060421 was not fetched).

## 7. Synthesis: which pi problems are (a) famous and out of reach, (b) active with recent progress, (c) small enough for an amateur working with an AI system

### Takeaway
(a) Normality, algebraic independence of pi and e, irrationality of pi+e. (b) Irrationality exponents (pi claimed settled by AI in September 2026 but unverified; pi^2 and zeta(3) bounds improved three times in two months), unification and proof of pi formulas (CMFs, WZ seeds, Ramanujan-Sato classification), fast formulas for other constants. (c) Proofs of individual conjectured identities, Lean formalization of known pi results, formula and parameter searches with rigorous certification, and large-scale digit or continued-fraction statistics; each has a 2025-2026 precedent by an independent author.

### Cited Findings
- **[REF]** Open and listed as unsolved in November 2026: normality of pi; algebraic independence of pi and e; transcendence of e+pi and e*pi; the irrationality measure of pi. — [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- **[REF, 2026 flag]** The exponent-2 claim for pi is unverified by independent specialists as of the latest dated status (7 October 2026). — [MathWorld: Irrationality Measure](https://mathworld.wolfram.com/IrrationalityMeasure.html)
- **[PP, 2026 flag]** Single-author numerical irrationality bounds appeared in 2026 with AI or computer-algebra support (Bai for pi; Niedbala Giraudin for zeta(2)). — [arXiv:2609.11276](https://arxiv.org/abs/2609.11276); [arXiv:2610.02912](https://arxiv.org/abs/2610.02912)
- **[PP, 2026 flag]** In the Ramanujan Challenge, amateurs and a high-school student submitted proofs; correctness rates were 52% with CAS verification, 38% with Lean, 6% with numerical checks only; one-shot LLM judging of proofs had a 23% false-positive rate before the authors' pipeline cut it to 6%. One open conjecture (on zeta(3)) remains unsolved. — [arXiv:2610.40551](https://arxiv.org/abs/2610.40551)
- **[REF, 2026 flag]** The Chudnovsky identity is still unproved in Lean on the lean-eval leaderboard. — [lean-lang.org eval](https://lean-lang.org/eval/problems/chudnovsky_formula_for_pi_inv/)
- **[REF]** GCD factorization in binary splitting is a known 20-30% gain for Chudnovsky pi that y-cruncher does not implement. — [y-cruncher binary splitting](https://numberworld.org/y-cruncher/internals/binary-splitting.html)
- **[PRESS]** An independent engineer's formula searches changed the record software for several constants. — [StorageReview guest post](https://www.storagereview.com/review/the-math-of-performance-stress-testing-hardware-for-math-changing-results)
- **[PP]** Record-low Machin-like formulas were found by a constrained PSLQ search in 2025. — [arXiv:2508.08307](https://arxiv.org/abs/2508.08307)
- **[PRESS, 2026 flag]** The 314 trillion digit dataset is publicly retrievable; no statistical paper on it was found. — [Backblaze](https://www.backblaze.com/blog/backblaze-now-serving-314-trillion-digits-of-pi/)
- **[REF, 2026 flag]** 653.52 billion continued-fraction terms of pi exist (2025); Khinchin and Levy limits unproven. — [MathWorld: Pi Continued Fraction](https://mathworld.wolfram.com/PiContinuedFraction.html)
- **[PRESS, 2026 flag]** Experts warn that unread, long AI-generated manuscripts from non-mathematicians are a growing problem, and the documented amateur successes involved literature checks, formal or expert verification, and short arguments. — [Quanta Magazine](https://www.quantamagazine.org/how-ai-tore-through-a-mathematical-community-20260803/)

### Inferences
The classification below is the researcher's judgment built on the findings above.

(a) Famous and out of reach
- Normality of pi in base 2 or 10 (even "each digit occurs infinitely often" is unproven).
- Algebraic independence of pi and e; irrationality or transcendence of pi+e, pi*e, pi^e; Schanuel's conjecture.
- Khinchin or Levy behaviour of pi's continued fraction; bounded or unbounded partial quotients.
- A new all-digit record: out of reach financially and operationally for an individual, and not a mathematical contribution.

(b) Active, with recent progress
- Irrationality exponents: pi (claimed exactly 2, September 2026, unverified), pi^2 and zeta(3) (three successive 2026 preprints), logarithm ratios (Chudnovsky 2026). The main open task right now is verification and digestion of the OpenAI argument.
- Structure of pi formulas: conservative matrix fields (43% of harvested formulas unified; 51% in clusters not yet resolved; 6% orphans), WZ seeds, classification of Ramanujan-Sato series by level, level-11 coefficient formula (2026).
- Fast series for other constants and their adoption in y-cruncher (2023-2026 records for log, zeta(3), zeta(5), Catalan, Gamma values).
- BBP-type formulas in non-standard bases (base 5, golden ratio).

(c) Plausible for an amateur with an AI system, with the closest precedent
1. Prove a specific conjectured identity for pi: an unproven Ramanujan Machine continued fraction, one of Sun's still-unproven series, or an "orphan" formula's link to a CMF. Precedents: Wang (2026), Au (2025), Challenge participants (2026). Deliverable: a short proof with a WZ certificate, CAS script or Lean file. Venues: arXiv math.NT; Ramanujan Journal, Journal of Symbolic Computation, or Integers for a batch of related proofs.
2. Formalize a classical pi theorem in Lean: the Chudnovsky identity is an explicit open target with an informal proof already written out (Milla). Deliverable: a Mathlib contribution plus an arXiv or formal-methods venue write-up.
3. Certified search for efficient formulas: Machin-like relations (Craig-Wood), hypergeometric series for constants other than pi (Zuniga). For pi itself the realistic variant is a rational or low-degree Ramanujan-Sato series with a measured binary-splitting cost, or an implementation and measurement of GCD factorization for Chudnovsky. Deliverable: formula plus proof plus benchmark; registry entry at numberworld.org if it sets a record.
4. Parameter optimization in irrationality-measure constructions for constants near pi (pi^2, pi/sqrt(3), logarithms), in the style of Bai and Niedbala Giraudin, with ball-arithmetic certification. Risk: the field is moving weekly in late 2026 and results can be superseded before submission; for pi itself this is moot if the exponent-2 proof is confirmed.
5. Digit statistics on the 314 trillion digit dataset, or statistics of the 653.52 billion continued-fraction terms. Deliverable: arXiv note with reproducible code; journal publication would need a new test or a methodological contribution (Experimental Mathematics precedent).
6. Short expository or elementary-proof notes (new proof of irrationality, a neat inequality, a geometric approximation). Precedent: three pi items in the Mathematical Gazette in 2025.
7. Computational registry contributions: extending the search for prime prefixes of pi beyond the 2001 result, more continued-fraction terms, digit-extraction position records. These are citable in OEIS or MathWorld but rarely publishable alone.

Working rules implied by the 2026 evidence
- Check the literature first (the Erdos 333 episode); the "From Euler to AI" catalogue of 385 pi formulas is a ready-made novelty check for formulas.
- Attach machine-checkable evidence: in the Challenge, proofs supported only by numerical checks were correct 6% of the time.
- Keep results short and scoped; state AI assistance explicitly as Bai did.
- Background knowledge not verified in this session: a first arXiv submission in math.NT normally needs an endorsement from an established author, and moderators may reclassify elementary work to math.GM, which many readers ignore.

### Gaps
- No source ranks these candidate projects by acceptance likelihood; the ranking is judgment.
- The number and identity of still-unproven Ramanujan Machine pi conjectures and Sun series, which determines how much room option 1 has, was not established.
- Journal policies on AI-assisted submissions (Monthly, Gazette, Ramanujan Journal, Integers, Experimental Mathematics) were not checked.
- All late-2026 developments could change quickly; the status of the OpenAI pi proof in particular should be rechecked before any project on irrationality measures is started.

## Search log

Executed web searches (42), in order:

1. pi digits world record 2026
2. StorageReview 314 trillion digits pi y-cruncher
3. Saha Sinha pi series string theory Physical Review Letters 2024
4. irrationality measure of pi Zeilberger Zudilin 7.103 improvement
5. Ramanujan Machine conjectures proven pi continued fractions conservative matrix field
6. normality of pi open problem recent progress Bailey Crandall hypothesis
7. series faster than Chudnovsky for computing pi in practice class number
8. numberworld y-cruncher formulas algorithms binary splitting notes Alexander Yee
9. Guillera Ramanujan-like series 1/pi^2 proof arXiv 2024 2025
10. new BBP-type formula pi arXiv 2023 2024 2025
11. statistical analysis digits of pi 100 trillion randomness tests paper
12. Schanuel conjecture pi e algebraic independence recent progress 2025
13. amateur mathematician new formula for pi published journal independent researcher
14. pi prime numbers Euler product formula new result arXiv
15. Ramanujan-Sato series new level 2025 arXiv Cooper Chan Zudilin
16. Plouffe formula nth digit of pi Bernoulli Euler numbers 2022
17. "From Euler to AI" unifying formulas mathematical constants pi
18. AI discovered new formula pi 2026 GPT AlphaEvolve mathematical constants
19. Zhi-Wei Sun conjectural series for 1/pi proved 2023 2024 2025
20. Math Scholar David Bailey blog pi 2026
21. normal numbers pi base 2 arXiv 2025 new result discrepancy BBP constants
22. Lorenz Milla proof Chudnovsky formula teacher arXiv
23. Machin-like formula new record Lehmer measure 2020..2025
24. Ramanujan Machine unproven conjectures list community proofs pi
25. transcendence of e+pi or e*pi open problem status "at least one" Nesterenko e^pi
26. Mathematical Gazette note pi series proof 2024 2025
27. GPU computation of pi binary splitting NTT multiplication trillion digits paper
28. continued fraction of pi partial quotients record computation billion terms
29. Saha Sinha pi formula criticism mathematicians not new MathOverflow
30. pi record attempt 2026 y-cruncher 500 trillion OR quadrillion digits
31. Jorge Zuniga fast series y-cruncher independent researcher hypergeometric Catalan zeta(3) record
32. Kam Cheong Au Wilf-Zeilberger seeds hypergeometric identities pi series proved conjectures
33. Rosengren Saha-Sinha formula proof partial fractions 2025
34. BBP digit extraction pi record quadrillionth bit hexadecimal position verification Bellard formula
35. undergraduate student paper new series for pi published Involve OR "College Mathematics Journal" OR "Integers"
36. 314 trillion digits pi digit frequency statistics analysis normality check
37. Euler product over primes for pi generalization identities "primes" "pi" arXiv 2024 2025 new infinite product
38. y-cruncher v0.8 new large multiplication algorithm swap mode improvements checkpoint 300 trillion bottleneck
39. Quanta Magazine pi irrationality OR normality OR formula 2025
40. Lean formalization Chudnovsky formula pi mathlib 2026
41. amateur AI-assisted proof Erdos problem published 2026 non-mathematician ChatGPT
42. Ramanujan Machine 2026 new results conservative matrix fields irrationality zeta(5) pi hypergeometric

Attempted but not performed (6): the shared web search budget of 200 calls for the whole research run was exhausted, so these returned no results:

43. "Ramanujan Challenge" 2026 Ramanujan Machine proofs formulas constants participants
44. Guillera arXiv 2026 Ramanujan series pi new
45. American Mathematical Monthly 2025 pi note proof irrationality OR series OR Wallis
46. Notes on Number Theory and Discrete Mathematics pi series new formula 2024 2025
47. normality of pi survey 2024 arXiv what is known digits pi base 2 infinitely many digits lower bound
48. primes in decimal expansion of pi probable prime record digits prefix OEIS A005042

Totals: 42 distinct searches executed (requirement: at least 18), 6 further distinct queries attempted and refused by the budget, plus 83 direct fetches of primary pages (arXiv abstracts and PDFs, numberworld.org, StorageReview, Wikipedia, MathWorld, OEIS, GitHub, Math Scholar, Quanta, Scientific American, Cambridge Core, lean-lang.org, ramanujanmachine.com, vibemathed.com, Backblaze, bellard.org). No personal names of the user were used in any query.
