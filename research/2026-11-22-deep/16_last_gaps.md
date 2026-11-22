# 16. Last gaps: forums, arctan(2/7), removed 2026 preprint series

Date of search: 22 November 2026. Tags: [READ] = seen in fetched content; [SNIPPET] = search-result text only; "from memory, unverified" otherwise.

## Summary

1. Gap A: no thread found on MathOverflow, Math StackExchange, mersenneforum, Reddit, Hacker News or the Lean Zulip that bears on the results. Caveat: mathoverflow.net and reddit.com are blocked for the search tool (4 calls errored), and 4 site-restricted or topic queries returned only arXiv, Wikipedia and MathWorld pages. So this is "no prior statement found in 13 searches", NOT evidence that no thread exists.
2. Gap B: arctan(2/7) is stated open twice [READ]: Bailey's compendium, section 3, and Borwein-Borwein-Galway 2004, section 2.5 ("first arctangent ... unable to find"). No source found that proves an exclusion for it.
3. BBG 2004 Theorem 1 (section 2.6) gives an exclusion criterion for arctan(y/x) (b-ary Machin-type, Z-linear) via a prime p = 1 mod 4 with odd valuation of x^2+y^2 and either p | b or 4 not dividing ord_p(b). For 7+2i (norm 53) and b = 2: ord_53(2) = 52 (computed by me, from memory of the criterion; the criterion's exact wording was garbled in text extraction), so it appears NOT to exclude it. Treat as unverified.
4. No table of "binary-BBP-representable Gaussian primes" found. Bailey's compendium lists rationals q with formulas (lists 14 and 16) and says "not all small rationals appear".
5. Gap C: all Zenodo records of the Kulik series return HTTP 410 Gone [READ]. Only OpenAlex abstracts survive (not full text). Wayback Machine has a snapshot of records/22007472 dated 2026-09-08 [READ, availability API], but web.archive.org is blocked for my fetch tool, so the text was not read.
6. The three named papers: no claim of classifying ALL binary BBP-type formulas for pi was found in the abstracts. Claims are about specific frames (b, n) such as (16, 8), (64, 6), and about "towers".
7. Closest overlap in method: the 22007471 abstract (via inverted index) reduces the annihilator lattice to S-unit relations among 1 - alpha_j, uses log(1 - alpha_j), and reportedly invokes Baker's theorem. It credits Borwein-Galway 2004. It also reports numerics (120 digits) and a sieve over 2,233 frames; it lists many killed claims. Details of what is proved are not recoverable from abstracts.
8. A sibling record, "Kernel, Frame, Winding, Residue", reports an 8-unknown system with a 7-dimensional solution surface (abstract). That is a different count from the 8-dimensional space of formulas in result (1); the frame is only the base-16 octal one.
9. Nothing found on optimality (2/3 non-zero term per bit), Huvent, or log 23 in any of these papers' abstracts.
10. Limits: abstracts only; full texts gone. Do not treat the lack of a claim in an abstract as proof the full text lacks it.

## Gap A: question-and-answer sites and forums

| Site | Thread found | URL | Date | What it establishes |
|---|---|---|---|---|
| MathOverflow | none reachable | n/a | n/a | Domain blocked for WebSearch (API error); not checked |
| Math StackExchange | none found | n/a | n/a | Searches returned no StackExchange pages |
| mersenneforum.org | none found | n/a | n/a | One query on Huvent/Bellard/fewest terms: no forum page returned |
| Reddit r/math | none reachable | n/a | n/a | Domain blocked for WebSearch |
| Hacker News | none found | n/a | n/a | Included in two queries; no HN page returned |
| Lean Zulip | none found | n/a | n/a | Included in two queries; none returned |

Non-forum items surfaced by the same queries (all [SNIPPET] unless noted):
- Bailey, "A compendium of BBP-type formulas", which says it is not exhaustive [SNIPPET]. Compendium section 3 text read [READ] (see Gap B).
- Barsky, Munoz, Perez-Marco, "On the genesis of BBP formulas" (arXiv 1906.09629) [READ, via pdftotext]: asks "if all null BBP formulas of degree 1 can be obtained" by combining their formulas for different s (Remark after Theorem 1.1). So a complete list of degree-1 zero relations was posed as a question there. Describes origin of null formulas as "somewhat mysterious". It also defines an efficiency measure m'/log b (non-zero coefficients over log of base) in Remark 1.2.
- Kristensen and Mathiasen, "BBP-type formulas, an elementary approach" (arXiv 2208.07696) [READ partially; search snippet says it handles degree 1 only and that completeness of zero formulas for other numbers is unknown [SNIPPET]].
- Adegoke et al., "A class of digit extraction BBP-type formulas in general binary bases" (arXiv 1603.07395) [READ outline]: binary formulas for logs of an infinite set of primes and arctangents of an infinite set of rationals; section 6.1.4 arctan(1/6); section 6.3 binary zero relations.

Topics with no hit: "BBP for log 23", "null BBP", Huvent, base 3 / base 10 impossibility, BBP with Baker's theorem (a snippet-level search found nothing mentioning Baker).

## Gap B: arctan(2/7)

1. Bailey compendium, section 3 (arctangents) [READ, via pdftotext of bbp-formulas.pdf at davidhbailey.com]: after list (16) of additional rationals, says not all small rationals appear, and "it is not known whether arctan(2/7) possesses a binary BBP formula". Also says Adegoke, Lafont and Layeni showed arctan(5/36) has one (his reference [12]). Also: BBP formulas in non-binary bases for arctangents of certain rationals can be obtained from variants of his formulas 11 and 12. Lists: (14) is the first list of rationals, (16) the PSLQ-extended list including 5/7, 1/11, 4/13, 7/16, ..., 41/50. The edition read is the Bailey PDF at davidhbailey.com; the 2004 version has the same wording in the snippet.
2. Borwein, Borwein, Galway, "Finding and excluding b-ary Machin-type individual digit formulae", Canad. J. Math 2004 [READ, via pdftotext]:
   - Section 2.5: among values missing in Bailey's list, "the first arctangent for which we have been unable to find a binary Machin-type BBP formula is arctan(2/7)". They find arctan(1/6), arctan(5/6), arctan(1/11) by hand factorization over Z[i].
   - Section 2.6, Theorems 1 and 2: exclusion criteria for Z-linear Machin-type BBP arctangent formulas in base b. Theorem 1: prime p = 1 mod 4 with odd p-adic order of x^2+y^2, and either p | b or 4 does not divide the order of b mod p. The proof for b > 2 uses Gaussian-integer factors b^m - i; the case b = 2 has extra Aurifeuillian generators (1 + i) 2^-m. Examples 1-2: no b-ary formula for arctan(1/2) if 5 | b; arctan(1/5) if 13 | b; arctan(2/3) in base 3. Note the scope: "Machin-type" means Z- (or Q-)linear combinations of the generators arctan(b^-m) (and arctan(1/(1-2^m)) when b = 2). This is a narrower class than all BBP-type formulas of degree 1.
   - The abstract says pi has no Machin-type BBP arctangent formula for b not 2 (consistent with the user's result (2)-type statements, base 2 excepted); Baker's theorem is not mentioned in my grep of the text for "Baker" (no hits).
3. Adegoke 2013-14 and the 1603.07395 paper: infinite sets of rationals whose arctangents have binary BBP formulas [READ outline; SNIPPET]. No statement about 2/7 found in grep of the text ("2/7" gave no hit outside Bailey).
4. Not checked or not reachable: Borwein-Bailey "Mathematics by Experiment" (no copy fetched), Chamberland 2003 (cited by Adegoke; not fetched), BBP 1997 (not fetched), OEIS, MathWorld "BBP-type formula" page (appeared in results; not opened). MathWorld snippet gave nothing on 2/7.
5. Answer to the question "has anyone proved an exclusion or listed which arctan(p/q) have formulas": the lists are lists (14) and (16) of Bailey and the infinite families of Adegoke et al.; the only exclusion theorem found is BBG Theorem 1 (Machin-type scope), which does not appear to cover 2/7. No source found stating a necessary-and-sufficient criterion for arctan(q). No prior statement found in 13 searches that settles arctan(2/7).

## Gap C: the Kulik series

Access status: zenodo.org/records/22007472, 21971619, 21707507, 21830435, 21841198, 23357949, 21707308 all returned HTTP 410 Gone [READ]. Wayback availability API: records/22007472 has snapshot 2026-09-08 10:46:29 UTC, status 200 [READ]; records/22007471 has none [READ]. web.archive.org itself is blocked for the fetch tool, so the snapshot text was not read (someone with a normal browser can open http://web.archive.org/web/20260908104629/https://zenodo.org/records/22007472). OpenAlex records survive with abstracts; no GitHub, OSF or ResearchGate copy was found in the one search used for that. The OpenAlex-based descriptions below were produced by a small summarizing model reading the inverted index, so they are approximate [READ via summarizer].

Wider series (OpenAlex titles, all Zenodo, 2026, same author): Kernel, Frame, Winding (2026-07-30, DOI 10.5281/zenodo.21707307); Kernel, Frame, Winding, Residue (2026-07-30, .21707506); The Angle Register (2026-07-30, .21703380); Building The Void (2026-08-07, .21830434); Rational Integral Operators with Distinguished Fibres (2026-08-07, .21841197); The Two-Angle Admissibility Theorem (2026-08-08, .21845064); The Analog Read-Head (2026-08-04); The Seam Isomorphism (2026-05-30); Nest, Run, Fold (2026-10-14, .23357948). Plus an assessment-style item "Isolating Novelty in Theoretical Frameworks" (2026-07-31). These were not requested individually but give context.

### C1. "Objects as Closures: Constraint Meshing as a Primitive of Mathematical Construction"
- Date 2026-08-16; DOI 10.5281/zenodo.21970408 (and .21970409); Zenodo, CC-BY-NC; removed (410). Readable only as OpenAlex abstract.
- Claims: an object is the residue of a relation; two constraints imposed together give a "mesh". Case study: base-64, period-6 tower; pole geometry alone leaves a 2-dimensional admissible space of coefficient vectors inside a 5-dimensional space; adding a zero-sum condition selects a unique line, signature 9 x [4, -2, -1, -1], the same as the base-16 BBP signature. Says it is derived from Re(z_char) = 1. Family b = sec^n(theta).
- Status: algebraic derivations stated; coefficient match numerical; "why the coefficients" left open. No classification of all BBP formulas, no Baker, no logarithm claims, no optimality.

### C2. "Exactly Two Seeds: A Constraint-Derived Classification of the Digit-Extraction Towers, with Predicted Members and Inverse Recovery"
- Date 2026-08-17; DOI 10.5281/zenodo.21971618 (and .21971619); removed.
- Claims: pole annihilation plus zero-sum select the weights [4, -2, -1, -1], radix b = sec^m(2 pi/m), shell support {1, m-4, m-3, m-2}. Classification "for integers m > 1 exactly m = 6 and m = 8" via a Galois-abelian argument (Q(2cos(2 pi/m)) abelian versus Q(2^(1/e))). Non-primitive indices are lifts (n = km, b = b_seed^k). Four predicted towers constructed and verified numerically; an inverse map round-trips 8 cases. Negative controls; "same architecture" in other settings (crypto round, oscillator, quantum problem).
- Status: the m in {6, 8} classification is stated analytically; the rest numerical or claimed. This classifies towers of one type with fixed weights, not all binary BBP-type formulas for pi. No Baker, no logarithm claims, no optimality.

### C3. "The Reader and the Frame: The Annihilator Lattice of the Digit-Extraction Towers, its Instrument-Dependence, and the Condition that Makes the Classical Formula Unique"
- Date 2026-08-19; DOI 10.5281/zenodo.22007471 (and .22007472); removed 2026-10-30 (per the request); Wayback snapshot 2026-09-08 exists.
- Claims, from the abstract: studies the annihilator lattice (coefficient vectors giving zero) of "producers" returning pi or pi/sqrt(3) from shell sums over frames (b, n). The lattice depends on the "reader" (field of readout). Uniqueness of the classical formula holds exactly when the zero-sum condition C1 selects a functional that is injective on the kernel K. Across eight towers, uniqueness for seven, fails for (4096, 24) with four dimensions unfixed. Reduction of the kernel to an S-unit relation lattice (norm/orbit argument, factorizations of monic polynomials g, norms g(1)/g(0)). Logarithms L_j = log(1 - alpha_j) and their Q-linear relations; the summarizer reports Baker's theorem is invoked but could not say for which steps. Odd-prime content of the frame identified. An exclusion sieve removes 1,952 of 2,233 candidate frames, with "false exclusions" mentioned. Grading theorem: when class-pure detection is complete. Numerics verified to 120 digits for several frames. Corrections: a winding identity, an ancestry-closure claim, a draft formula; a third seed kernel found. Section 13 lists killed claims (six from earlier work, five from this one; "every forward claim died, every backward derivation survived"). Research Problem 10 (how many Q-linearly independent binary Machin-type relations) said to be underdetermined, with criticism of Borwein et al. 2004; the paper credits their valuation-vector method.
- Proved versus numerical: grading theorem and m in {6, 8} stated as proved; sieve, 120-digit checks and the eight-tower uniqueness census numerical. I could not separate every claim.
- Not found in the abstract: any classification of ALL binary BBP-type formulas for pi, a dimension count like 13 or 8, primitive prime divisors, optimality, any log p result, or the 2/3 per bit bound. "Primitive prime divisor/Zsigmondy" did not appear in the summarizer's reading.
- Overlap assessment: shared themes are (i) multiplicative relations among 1 - alpha for roots alpha of x^N - b, (ii) Baker's theorem on logarithms, (iii) the annihilator (zero relation) lattice. Differences visible at abstract level: frames of the base-16/base-64 tower type only, "producer" vectors rather than general degree-1 formulas, no stated global dimension theorem. A reader should check the Wayback snapshot or a copy of the full text before claiming no overlap.

## Queries used (13 WebSearch calls; 4 returned API errors because mathoverflow.net or reddit.com is blocked; all counted)

1. site:mathoverflow.net BBP formula pi classification all binary BBP-type formulas zero relations
2. site:math.stackexchange.com BBP-type formula logarithm which log have BBP formula Baker theorem
3. site:mersenneforum.org BBP formula pi Huvent Bellard fewest terms digit extraction
4. arctan(2/7) binary BBP formula not known 7+2i Bailey compendium
5. Dean Kulik "Exactly Two Seeds" OR "Objects as Closures" OR "The Reader and the Frame" digit-extraction towers (no hit)
6. (error) are there other BBP formulas for pi base 2 classification ... [domains incl. mathoverflow]
7. (error) BBP formula logarithm prime log 23 ... [domains incl. reddit]
8. (error) BBP formula pi base 10 or base 3 impossible Baker's theorem ... [domains incl. reddit]
9. (error) BBP formula pi Bellard Huvent fastest formula number of terms [domains incl. reddit]
10. BBP formula pi other formulas classification Bellard Huvent logarithm BBP-type question [domains math.stackexchange, mersenneforum, HN, Lean Zulip]: arXiv papers only
11. Kulik annihilator lattice digit-extraction towers BBP Zenodo OR GitHub OR OSF OR ResearchGate: found the Zenodo titles listed above
12. "BBP" formula pi "other BBP formulas" OR "all BBP formulas" mathoverflow OR stackexchange OR mersenneforum: MathWorld, Wikipedia, arXiv
13. Lean Zulip OR Hacker News OR reddit BBP formula pi digit extraction Baker's theorem logarithm 23 binary: no forum pages

## Pages fetched

- api.openalex.org: search "annihilator lattice digit-extraction"; search "Exactly Two Seeds"; search "Objects as Closures"; works by DOI 22007471, 21971618, 21970408 (abstract index); filters for DOIs 21707307/506, 21841197, 21830434, 23357948, 21845064; a year-2026 Kulik digit-extraction search (25 titles).
- archive.org/wayback/available for records/22007472 (snapshot found) and 22007471 (none).
- web.archive.org snapshot: blocked for the tool (not read).
- zenodo.org/records/22007472, 21971619, 21707507, 21830435, 21841198, 23357949, 21707308: all HTTP 410.
- PDFs, read via pdftotext: Cambridge CJM BBG 2004; Bailey bbp-formulas.pdf; arXiv 1603.07395; arXiv 1906.09629; arXiv 2208.07696 (only grep for keywords).

## Sources

- Bailey, "A compendium of BBP-type formulas" (https://www.davidhbailey.com//dhbpapers/bbp-formulas.pdf), section 3 on arctan(2/7), arctan(5/36).
- Borwein, Borwein, Galway, Canad. J. Math 2004, https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf
- Adegoke, Lafont, Layeni and others, arXiv 1603.07395.
- Barsky, Munoz, Perez-Marco, arXiv 1906.09629.
- Kristensen, Mathiasen, arXiv 2208.07696.
- OpenAlex API records listed above; DOIs 10.5281/zenodo.21970408, 21971618, 22007471, 21707307, 21707506, 21830434, 21841197, 21845064, 23357948.
- MathWorld BBP-Type Formula page (https://mathworld.wolfram.com/BBP-TypeFormula.html): appeared in results, not opened.

Privacy: only the author name printed on the papers is recorded; no other personal data collected.
