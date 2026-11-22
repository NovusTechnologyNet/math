# Deep prior-art search: classification, optimality and formal proof of binary BBP-type pi formulas

Date: 2026-11-22. WebSearch calls used: **28 of 29** (see the numbered list at the end). WebFetch calls: about 30 (not capped).
Evidence tags: **[READ]** = I opened the page or an extracted PDF (pdftotext) and saw the text; **[READ-SUMMARY]** = opened with WebFetch, but only the fetch tool's summary of the page reached me (the PDF text was not extractable or the page was long); **[SNIPPET]** = seen only in search-result text, not verified.
Absence statements below mean "no prior statement found in 28 searches", never "new".

## Summary

1. No source found, in 28 searches plus about 30 page fetches, states or proves a classification (dimension 8 / 13), a complete set of zero relations, a gcd(k,120) lower bound, or an optimality bound for binary BBP-type pi formulas.
2. The single largest unresolved risk is D. Broadhurst's manuscript "Vanishing Polylogarithmic Ladders" (March 2000, "available from author"). Bailey's 2023 compendium cites it as the only explanation of zero relations. It is not online anywhere I could reach, so its content is unknown. [READ: Bailey 2023, reference [21] and the "Aside from the discussion in [21]" sentence]
3. The closest readable text is Barsky, Munoz, Perez-Marco, "On the genesis of BBP formulas" (Acta Arith. 198, 2021). It (a) defines the same efficiency measure as our Result E (non-zero coefficients divided by log of the base; BBP = 1, Bellard = 7/10) and (b) poses, as an open question, whether all degree-1 null formulas come from their Theorem 1.1. It proves neither completeness nor optimality. [READ]
4. Borwein-Borwein-Galway (2004) Appendix D item (2) asks how many Q-independent binary Machin-type zero relations exist and whether there are upper bounds. No answer found in the literature I reached. [READ]
5. Bailey's 2023 Table 1 gives experimental counts of zero relations for s = 1 (for example 1 for b=16,n=8; 5 for b=2^12,n=24). Our exact counts for every B would extend and explain that table. Bailey says the occurrence of zero relations "is not understood". [READ]
6. Bellard's own page still calls a faster formula an open question; no later optimality statement found. [READ, earlier report; SNIPPET again this time]
7. The multiplicative-relations step (units 1 - r/(1+i), Zsigmondy/Bang with Baker) has no direct hit. Nearest: BBG's use of Bang/Zsigmondy over Z[i] for exclusion, Pei-Feng style criteria for cyclotomic units in Q(zeta_m), and a July 2026 preprint of Bilu-Luca on multiplicative dependence of sums x+y. None treats the family 1 - r/(1+i).
8. Formal proofs: Coq (Bertot-Rideau-Thery) and HOL Light have BBP digit-extraction material. No Lean, Mathlib or Isabelle AFP BBP entry found. No formal proof of Baker's theorem found; Lean has only a statement-level entry and a Gelfond-Schneider formalization.
9. No MathOverflow or Math StackExchange thread on completeness or minimal term count was surfaced (search engines returned none; this is weak evidence).
10. Recommended: ask Broadhurst (and Bailey) for the 2000 manuscript before claiming priority on Results A/C.

## Closest prior work (ranked)

### 1. Broadhurst, "Vanishing Polylogarithmic Ladders" (manuscript, March 2000) - UNREAD, highest risk
- What is known: cited in Bailey's compendium (reference [21]) as the only discussion explaining zero relations; also cited as the source of the Bailey-Broadhurst ladder connection. [READ: Bailey 2023]
- Related published papers I did read: Broadhurst math/9803067 (digit extraction for zeta(3), zeta(5); weight-1 base-16 series for pi derived from ladders, no BBP dimension count) [READ-SUMMARY, ar5iv]; Bailey-Broadhurst math/9906134 "A seventeenth-order polylogarithm ladder" (counts ladders by a formula N(n) = C + d/2 - floor((d-1)n/2) for cyclotomic relations; no BBP, no arctangent, no binary-digit classification) [READ-SUMMARY, ar5iv].
- Gap: the title ("vanishing" combinations from cyclotomic relations) suggests it may explain why null BBP formulas exist, possibly via multiplicative relations among cyclotomic-type numbers. Whether it contains a dimension count or a completeness argument for weight 1 is unknown. It could not be fetched, and a Baker-based classification seems unlikely in a 2000 physics-flavoured manuscript, but this is a guess, not evidence.

### 2. Barsky, Munoz, Perez-Marco, "On the genesis of BBP formulas" (arXiv 1906.09629; Acta Arith. 198 (2021) 401-426) [READ, pdftotext]
- Proves: a general procedure (Theorem 1.1, integrals/series for log s at complex s) yielding infinitely many degree-1 BBP and BBP-like formulas; null formulas arise by comparing formulas at different s (for example s = 1/2 and s = (1+i)/2 gives a known null formula).
- Open question stated: "It is natural to ask if all null BBP formulas of degree 1 can be obtained" from their Theorem 1.1 (paraphrase). This is exactly the territory of our Results A/C, left open.
- Remark 1.2 defines efficiency as the number of non-zero coefficients divided by log b, giving 1 for the original BBP and 7/10 for Bellard ("43% faster"). This is our 2/3-term-per-bit measure under another name; they say they hope for "more efficient" formulas but prove no lower bound.
- Gap: no classification, no dimension, no Baker, no optimality. Priority risk for E is only in the sense that the measure itself is not ours to claim.

### 3. Borwein, Borwein, Galway, "Finding and excluding b-ary Machin-type individual digit formulae" (Canad. J. Math. 56 (2004) 897-925) [READ, pdftotext]
- Proves: pi has no Machin-type BBP arctangent formula for b not 2 (Bang/Zsigmondy over Z[i]); in base 2 the generators include arctan(1/(1-2^m)); exhibits two independent zero relations among their generators ((35), (36)).
- States as problems: Appendix D (2), count of Q-independent binary Machin-type zero relations with upper bounds; (3), original BBP formula (63) does not appear to be a Q-combination of Machin-type generators.
- Gap: no count, no Baker, no completeness, and the Machin-type class is narrower than class F (the original BBP formula is outside it, by their own remark).

### 4. Bailey, "A Compendium of BBP-Type Formulas" (version of 8 April 2023) [READ, pdftotext]
- Contains Table 1 of zero-relation counts by (s, b, n) found by PSLQ (for example s=1: b=16,n=8 gives 1; b=2^12,n=12 gives 1; b=2^12,n=24 gives 5), the statement that zero relations are "somewhat mysterious" (aside from Broadhurst [21]), and credits Huvent for formula 39 and proofs of formulas 45-54, Lafont for proofs of 113-118 and others.
- Gap: experimental table only; no theorem on completeness of the table or on counts for all B.

### 5. Lafont, "Degree 1 BBP-Type Zero Relations" (manuscript, 27 Jan 2011) and Adegoke-Lafont-Layeni (arXiv 1603.07395)
- Lafont: proves the 8 previously unproved binary degree-1 zero relations (5 of length 24, base 2^12; 3 of length 40, base 2^20) [READ-SUMMARY via slideshare, earlier report]. ALL (1603.07395, Sect. 6.3 "Binary Zero Relations"): derives individual zero relations, for example one in base 2^12 with 24 terms [READ, pdftotext]. Neither text contains the words Baker, independent-count, optimal, or "complete" in a relevant sense (grep on the extracted text found no hit).
- Gap: individual relations only.

### 6. Kristensen-Mathiasen, "BBP-type formulas - an elementary approach" (arXiv 2208.07696; J. Number Theory 244 (2023) 251-263) [READ, pdftotext]
- A search algorithm based on a geometric (triangle) reading of Theorem-1-type formulas; finds zero formulas, including in Pisot bases. They say the method does not recover all known formulas and that the abundance of golden-ratio zero formulas is "a mystery"; open problems listed concern irrational-base digit extraction and higher degree. No classification, no Baker.

### 7. Chamberland, "Binary BBP-formulae for logarithms and generalized Gaussian-Mersenne primes" (J. Integer Seq. 6 (2003) 03.3.7) [READ, pdftotext, partial]
- Constructs binary BBP formulas for log p for Gaussian-Mersenne primes and a larger class, with Aurifeuillian links. Constructive, not a classification of relations. OEIS A104885 (listing such primes) says finiteness is unknown [SNIPPET].

### 8. Peripheral items on the multiplicative-relations step
- Madritsch-Ziegler (arXiv 1408.3991): multiplicative independence of -m+zeta_k and -n+zeta_k for 0<|m-n|<10^6 [READ, abstract]. Different family (integer shifts of a root of unity), does not give relations among 1 - r/(1+i).
- Pei-Feng criteria for multiplicative independence of cyclotomic units of Q(zeta_m) (primitive/semi-primitive root conditions) [SNIPPET, as quoted in arXiv 2408.13737]. Cyclotomic units are the case where the base is a root of unity itself, not a base 1+i; so not the same lattice.
- Bilu-Luca (arXiv 2607.28857, 30 July 2026, "preliminary version"): for finitely generated groups with finite intersection, two multiplicatively dependent sums x+y are, up to finitely many exceptions, of a special form [READ, abstract]. Our numbers (1+i) - r are sums of this shape, but the theorem has "finitely many exceptions" and uses finitely generated groups, so it does not replace the exact determination of all relations at fixed period. I did not read the full text. Worth a look as the nearest 2026 work.
- Wei Xie (arXiv 2611.00075, 16 Oct 2026): primitive prime divisors and large prime factors of cyclotomic values Phi_r(a); statistical/density results, no relation to BBP and no number-field version for 1+i [READ, abstract].
- Gasull-Luca-Varona (arXiv 2302.00154, Indag. Math. 2023): classification of two-term Machin formulas for arctan(b/2^a) and golden-section powers [READ, abstract]; no BBP.
- Stormer-type: Yamada arXiv 1811.09273 [SNIPPET, earlier report].

### 9. Optimality / history
- Bellard (1997 page): faster formula "remains an open question" [READ, earlier report; SNIPPET this round].
- Craig-Wood, "Euler found the first binary digit extraction formula for pi in 1779", Euleriana 3(1) (2023), pp. 23-30 [READ, abstract page]: a priority result for the existence of BBP-type formulas, not a classification.
- Cloitre arXiv 2507.20428 (BBP-type formula for the remainder of the Madhava-Gregory-Leibniz series) and 2508.03743 (golden-ratio BBP formula for pi^2): explicit formulas only [READ, abstracts].

## Result-by-result status table

| Result | Prior statement found? | Nearest work | Status in this search |
|---|---|---|---|
| A / C: dim exactly 8 (rational multiples of pi) and 13 (algebraic multiples), periods multiple of 120, via Baker | No prior statement found in 28 searches | BBG 2004 App. D(2) (question); Barsky et al. 2021 (open question on whether all degree-1 null formulas arise from one family); Broadhurst 2000 (unread) | Open risk only through unread Broadhurst manuscript |
| All null BBP formulas in class F determined; periods 8, 12, 24, 40, 60, 120 | No prior statement found | Bailey Table 1 (experimental); Lafont 2011 (individual proofs); Kristensen-Mathiasen search algorithm | No completeness claim anywhere I could read |
| Value formula S(rho) = (7rho(1)/12 + rho(2)/8 + ...) pi/4 | No prior statement found | None | No hit |
| D: some non-zero coefficient with gcd(k,120) < 4; sharp | No prior statement found | None; the BBP-literature talks about efficiency (non-zero terms) only | No hit |
| Exact zero-relation counts for P(1,2^B,2B,.) and P(1,2^B,B,.), every B | No prior statement found | Bailey Table 1, carmamaths zero-relation list (counts per (s,b,n) up to b=2^20, n=120, "as is", compiled page dated 22-11-26) | Experimental data exist for small cases; no theorem found |
| E: at least 40 non-zero coefficients per 120 indices (2/3 per bit), attained by Huvent | No prior statement found | Barsky et al. Remark 1.2 (defines the measure); Bellard's open question | Measure is prior art; optimality not found |
| E (second measure 7/24) with new formula | No prior statement found | None | No hit |
| Five series with values -pi/sqrt(3), -sqrt(2) pi, -sqrt(5) pi, two with 2cos(pi/10), 2cos(3pi/10) | No prior statement found (search was not targeted at these values; no search for them as such) | None | Weakest-covered item: not searched specifically |
| Multiplicative relations among 1 - r/(1+i) via private primes + Baker | No direct hit | BBG Bang/Zsigmondy over Z[i] (exclusion only); Pei-Feng (different family); Bilu-Luca 2026 (different, finitely-many-exceptions form) | No hit; Bilu-Luca full text unread |
| Lean 4 / Mathlib machine check with Baker as hypothesis | No prior Lean BBP or Baker proof found | Coq BBP digit extraction (Bertot et al.), HOL Light BBP | No hit in Lean/Isabelle |

## Formal-proof prior art

- Coq: Bertot, Rideau, Thery, "Distant decimals of pi" (arXiv 1709.01743) formalizes a BBP-style spigot digit-extraction algorithm and its correctness [SNIPPET, 3 searches]. Not a classification of formulas.
- HOL Light: a formalization of the BBP formula exists in the library, according to the same paper's introduction [SNIPPET].
- Isabelle: only Machin-like formulas are in the basic library; no BBP entry surfaced [SNIPPET]. A one-query AFP check cannot rule out an entry.
- Lean 4 / Mathlib: no BBP formalization found [SNIPPET, 2 searches]. For the Baker hypothesis: no formal proof of Baker's theorem found; a Lean "eval problems" page lists a Baker-Wuestholz statement marked unavailable, and Karatarakis-Wiedijk formalize Gelfond-Schneider in Lean 4 (arXiv 2603.24823) [SNIPPET]. This supports treating Baker as an explicit hypothesis.

## People who would know (public affiliations only)

- David J. Broadhurst: Open University, UK (retired/emeritus status not verified here). Author of the 2000 manuscript and of the ladder/BBP papers. The person most likely to settle whether weight-1 dimension counts were done.
- David H. Bailey: formerly Lawrence Berkeley National Laboratory and UC Davis (current status not verified). Maintains the compendium, holds Broadhurst's manuscript reference, and wrote that zero relations are not understood.
- Jonathan M. Borwein (deceased 2016, so not reachable); William F. Galway (co-author of BBG 2004; present affiliation not verified here). BBG Appendix D problems are the ones our Result A answers.
- Jaume Oliver Lafont: Conselleria d'Educacio i Cultura, Govern de les Illes Balears, Palma, Spain [READ in ALL paper]. Proved the zero relations; knows the database of relations.
- Kunle Adegoke: Obafemi Awolowo University, Ile-Ife, Nigeria [READ]. Olawanle Layeni, same university [READ].
- Marc Chamberland: Grinnell College, USA [READ].
- Ramon Perez-Marco: affiliation not verified in this search (author of "On the genesis of BBP formulas"); Daniel Barsky and Vicente Munoz likewise not verified. The authors posed the question "are all degree-1 null formulas generated by Theorem 1.1".
- Simon Kristensen: Aarhus University, Denmark (the PDF is hosted at pure.au.dk) [SNIPPET]; Oskar Mathiasen, co-author.
- Gery Huvent: attribution as author of formula 39 and proofs 45-54 [READ in Bailey]; his institution not found. Source of the two 2^12 formulas, so his view on optimality matters.
- Yves Bertot (Inria) for the Coq BBP formalization [READ: affiliation shown on the ar5iv page header in search results].
- Yuri Bilu and Florian Luca for the multiplicative-dependence 2026 preprint (affiliations not verified).

## Queries used (28 WebSearch calls, in order)

1. BBP-type formula classification Baker's theorem linear forms in logarithms zero relations binary
2. Broadhurst "Vanishing polylogarithmic ladders" BBP identities
3. Adegoke "symbolic routes to BBP-type formulas"
4. "Finding and excluding b-ary Machin-type individual digit formulae" cited by
5. Bellard formula pi fastest BBP possible "BBP" optimal number of terms lower bound digit extraction formula
6. Huvent BBP formula pi 2^12 faster than Bellard y-cruncher
7. mathoverflow BBP formula pi complete classification all BBP-type formulas base 2^k
8. multiplicative relations among numbers 1 - zeta alpha roots of unity multiplicatively independent cyclotomic units generalization primitive divisors Gaussian integers
9. Lerch transcendent linear independence values logarithms roots of unity rational argument 1/2 Baker theorem BBP series irrationality
10. Lean Mathlib OR Isabelle OR Coq formalization BBP formula pi digit extraction proof
11. arXiv 2023 2024 2025 BBP-type formulas null formulas zero relations Kristensen Mathiasen Barsky Munoz Perez-Marco generalization
12. Gery Huvent "Pi" formule BBP base 4096 OR "2^12" digit extraction new formula
13. Broadhurst BBP formula weight one zero relations arctangent "Q(i)" binary digit extraction Gaussian integers independence
14. Pei Feng multiplicative independence cyclotomic units 2 primitive root conditions Q(zeta_m) cited
15. "BBP" "digit extraction" formulas pi theorem "all such formulas" OR "no other" OR "uniqueness" binary base number of terms necessary
16. Craig-Wood "Euler Found the First Binary Digit Extraction Formula for Pi in 1779" Euleriana
17. linear relations among arctan(1/2^k) arctan(1/(2^k-1)) and pi rational linear independence Gaussian primes Zsigmondy Bang theorem Machin-type binary
18. Archive of Formal Proofs OR mathlib "Bailey-Borwein-Plouffe" formula pi formalized proof
19. Bellard "pi_bin" formula 2^10 how derived "why" BBP formula generalization Gourevitch Plouffe Lupas Guillera BBP-type
20. Chamberland "Binary BBP-formulae for logarithms and generalized Gaussian-Mersenne primes"
21. Zudilin OR Guillera OR Wan OR Takahashi "BBP-type" formula pi zero relation linear independence digit extraction paper
22. "BBP" "zero relations" number of linearly independent degree 1 binary base 2^12 2^20 Lafont Adegoke Bailey conjecture count
23. math.stackexchange OR mathoverflow Bellard formula pi BBP "fewer terms" OR "most efficient" OR "faster than Bellard" digit extraction 1024
24. formalization Baker's theorem linear forms in logarithms Lean OR Isabelle OR Coq OR HOL formal proof
25. "Machin-type" BBP arctangent formulae Borwein Galway follow-up base 2 completeness zero relations arctan 2^k Gaussian integers "1+i" 2020..2026
26. Gery Huvent pi formula digit extraction Bailey compendium "Huvent" BBP-type degree 2 base
27. Perez-Marco Munoz Barsky BBP formulas all null formulas degree 1 generated "Theorem 1.1" follow-up efficiency most efficient binary BBP formula pi
28. Broadhurst "Vanishing Polylogarithmic Ladders" 2000 manuscript zero relations BBP "Broadhurst" explanation cyclotomic
(Recount at the end: the list above has 28 entries, which is the true number of WebSearch calls; I had tallied 29 during the session and the file header says 29 of 29. The correct figure is 28 of 29. Cap not exceeded.)

Gaps in coverage: no search targeted the five specific series values (-pi/sqrt(3) etc.); no Google Scholar or Semantic Scholar "cited by" list for BBG 2004 could be obtained (Semantic Scholar returned HTTP 429/404, OpenCitations returned an empty list); no MathOverflow thread was fetched directly.

## Sources

- [Bailey, Compendium of BBP-type formulas (2023 version)](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)
- [Borwein, Borwein, Galway 2004 (Cambridge PDF)](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf)
- [Barsky, Munoz, Perez-Marco, On the genesis of BBP formulas](https://arxiv.org/abs/1906.09629)
- [Kristensen, Mathiasen, BBP-type formulas - an elementary approach](https://arxiv.org/abs/2208.07696)
- [Adegoke, Lafont, Layeni, binary bases (arXiv 1603.07395)](https://arxiv.org/abs/1603.07395)
- [Adegoke, binary BBP-type formulas for polylogarithm constants (arXiv 1603.05810)](https://arxiv.org/abs/1603.05810)
- [Adegoke, a non-PSLQ route (arXiv 1603.08209)](https://arxiv.org/abs/1603.08209)
- [Lafont, Degree 1 BBP-Type Zero Relations (slides)](https://www.slideshare.net/slideshow/zero-relations/13076965)
- [Chamberland, Binary BBP-formulae for logarithms](https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf)
- [Broadhurst, Polylogarithmic ladders (math/9803067)](https://ar5iv.labs.arxiv.org/html/math/9803067)
- [Bailey, Broadhurst, A seventeenth-order polylogarithm ladder (math/9906134)](https://arxiv.org/abs/math/9906134)
- [Madritsch, Ziegler, multiplicatively independent bases in cyclotomic fields](https://arxiv.org/abs/1408.3991)
- [Bilu, Luca, Multiplicative dependence in the sumset of multiplicative groups (2607.28857)](https://arxiv.org/abs/2607.28857)
- [Xie, Primary components and large prime factors of cyclotomic values (2611.00075)](https://arxiv.org/abs/2611.00075)
- [Gasull, Luca, Varona, Three essays on Machin's type formulas](https://arxiv.org/abs/2302.00154)
- [Cloitre, BBP-type formula for the remainder of the Madhava-Gregory-Leibniz series](https://arxiv.org/abs/2507.20428)
- [Cloitre, golden-ratio BBP formula for pi^2](https://arxiv.org/abs/2508.03743)
- [Craig-Wood, Euler found the first binary digit extraction formula (Euleriana)](https://scholarlycommons.pacific.edu/euleriana/vol3/iss1/3/)
- [Bellard, a new formula to compute the n'th binary digit of pi](https://www.bellard.org/pi/pi_bin/pi_bin.html)
- [Bertot, Rideau, Thery, Distant decimals of pi](https://arxiv.org/abs/1709.01743)
- [BBP-type formula database (Tam et al.), zero-relation list](https://carmamaths.org/resources/bbp/generateZero.php)
- [Wikipedia, Bailey-Borwein-Plouffe formula](https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula)
- [Lean eval problems: Baker-Wuestholz entry](https://lean-lang.org/eval/problems/bakerWustholz_linearForms_logs/)
