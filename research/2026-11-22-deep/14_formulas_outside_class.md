# 14. Degree-1 binary BBP-type formulas outside the families n = B and n = 2B

Date: 2026-11-22. Tags: [READ] = seen in fetched content (PDFs were converted locally with pdftotext, so those are direct reads); [SNIPPET] = from a search result summary only; "from memory, unverified" = not seen. Statements marked [MY DERIVATION] are my own mathematics, not literature.

## Summary

1. No known binary degree-1 formula for pi (or any rational multiple of pi) has ratio n/B outside {1, 2} up to the rewritings (b,n) -> (b^m, nm), zero padding, and the power rule below. Every degree-1 binary formula in Bailey's compendium that I could parse has n = B or n = 2B (or is a zero-padded version, such as n = B/2 for x = 1/4) [READ]. The compendium's table of s=1 binary zero relations also has only n = B or n = 2B in every row [READ].
2. Sub-case structure [MY DERIVATION]: if x = y^m then sum x^k/k = m * sum over l divisible by m of y^l / l. So a class with radix x = 2^(-s) sits inside the class with radix 2^(-s/m). In ratio terms (r = n/B = 1/s): ratio r is a sub-case of ratio m*r for every integer m >= 1. Hence ratios 1/t and 2/j (j >= 1) all lie inside ratio 2; ratio 1 lies inside ratio 2; ratio 1/2 (x = 1/4) lies inside ratio 1, with zeros on odd residues. Ratios 3 (x = 2^(-1/3)), 4, 3/2, 4/3, 6 ... are NOT sub-cases of 1 or 2 (6 contains 1, 2, 3).
3. So the question is whether any formula for pi lives in a class with radix 2^(-1/m), m >= 3, or 2^(-p/m) with m not dividing 2. I found none in the literature, and no paper that studies those radices for pi.
4. Exclusion: Borwein-Borwein-Galway 2004 only treat "Machin-type" formulas (logs of elements of Q[i], integer base b); they prove pi has none for integer b not equal to 2 [READ abstract; the inequality glyph is lost in the PDF text but MathWorld confirms the "not binary" statement]. Their paper does not mention radix 2^(-1/m) or Baker or Kummer (searched in the text for these words: no hits) [READ]. Bailey's compendium overstates this as "no other degree-1 BBP-type for pi" with non-power-of-2 base [READ]; the theorem is about Machin-type only.
5. Non-integer bases: Cloitre (golden ratio, pi^2), Adegoke (golden ratio, pi, log 2, ...), Chan (pi in powers of 1/phi), Kristensen-Mathiasen (Pisot bases 1+sqrt3 etc., null formulas and a pi formula). No source treats 2^(1/3) or 2^(1/4).
6. Kristensen-Mathiasen (2022) have a general framework for any algebraic radix r in (0,1) via arg(1 + r e^{i theta}); their formula for pi/ rational multiples in base 2^(-1/2) recovers Lafont's null formula; they search only integers and Pisot numbers, and say non-integer bases are "largely unexplored" [READ].
7. Fewest terms: Takahashi (Ramanujan J. 2020) says Huvent's formula is the BBP-type formula with the least number of terms [SNIPPET, two searches]. I found no other source (Bailey, Wikipedia, MathWorld, Bellard) saying this.
8. Term counts: BBP 4 terms/4 bits; Bellard 7 fractions/10 bits [READ, Bellard page]; Huvent 8 terms/12 bits [READ, French-language numbers page, counted from displayed formula]; Adamchik-Wagon 3 terms/2 bits [READ, compendium formula (18) and numbers page]. Per bit: BBP 1.0, A-W 1.5, Bellard 0.70, Huvent 0.667.
9. Open question: Bellard's own page says whether a faster formula exists remains open [READ via summary of bellard.org/pi/pi_bin/pi_bin.html]. No source I found asks whether Huvent's 8/12 is optimal.
10. Searches used: 8 of 8. Many WebFetches.

## Catalog table

Ratio = n/B with b = 2^B (sign of b ignored; negative b means alternating signs, same radius). Compendium numbers refer to Bailey's April 2023 PDF. Glyphs for pi and sqrt are lost in the PDF text; constants marked (?) are inferred from MathWorld's list or from the context, not read directly.

| Constant | Source | b | n | B | n/B | Inside n=B or 2B? |
|---|---|---|---|---|---|---|
| pi | BBP 1997, compendium (1),(6) | 16 | 8 | 4 | 2 | yes (2B) |
| pi | Euler 1779 via Craig-Wood; Adamchik-Wagon, compendium (2),(18) | -4 | 4 | 2 | 2 | yes (2B) |
| pi | Euler/Pschill, compendium (3),(19) | -2^30 | 60 | 30 | 2 | yes (2B) |
| pi | Bellard 1997 (7 fractions, factor 1/2^(10n) with sign (-1)^n) | -2^10 | 20 (as in the user's P(1,2^10,20)); the formula has periods 4n and 10n | 10 | 2 | yes (2B) |
| pi | Huvent 2001 (8 terms, factor 2^(12i)) | 2^12 | 24 | 12 | 2 | yes (2B) |
| pi | compendium (17) (Ferguson, constant garbled; from the (18) note it is pi) | 16 | 8 | 4 | 2 | yes |
| pi*sqrt2 (?) | compendium (20) | 2^6 | 12 | 6 | 2 | yes (2B) |
| pi*sqrt3 (?) | compendium (21), Knuth | 2^6 | 6 | 6 | 1 | yes (B) |
| pi*sqrt3 | Adegoke et al. 1603.07395, bases 2^(12p), p odd | 2^12p | not read | 12p | not read | not read |
| sqrt5 * (arctan-type constant, garbled) | compendium (22), Adegoke | 2^20 | 40 | 20 | 2 | yes (2B) |
| sqrt2 log(1+sqrt2)/2 type | compendium (23) | 16 | 8 | 4 | 2 | yes (2B) |
| arctan(1/2) | Adamchik-Wagon, compendium (10) | 16 | 8 | 4 | 2 | yes (2B) |
| arctan(1/sqrt 2)-type, arctan(sqrt5), arctan(sqrt3), arctan(sqrt 7) | compendium (24)-(28), Adegoke | 2^4 or 2^12 | 8 or 24 | 4 or 12 | 2 | yes (2B) |
| arctan(4/5) | compendium (13) | 2^20 | 40 | 20 | 2 | yes (2B) |
| arctan of the ~190 rationals in lists (14)-(16) | compendium, via (1+i)^u/(1-2^v) type products | powers of 2 | not tabulated | | in class x = 2^(-j/2): n/B = 2/j, sub-case of 2 [MY DERIVATION] | yes (inside 2B; terms 1 + i/2^t give n/B = 1/t, inside B) |
| log 2 | compendium (7) | 2 | 1 | 1 | 1 | yes (B) |
| log 3 | compendium (8) | 4 | 2 | 2 | 1 | yes (B) |
| log p for 46 primes listed (2,3,5,7,11,13,17,19,29,31,37,41,43,61,73,...) | compendium (9), Harley/Aurifeuille, Borwein | powers of 2 | not tabulated | | built from Re log(1 +/- (1+i)^k/2^n), so radix 2^(-1/2) or 1/2; inside B or 2B | yes (stated structure, not each formula parsed) |
| arctan(2/7) | compendium: "not known" to have a binary formula | - | - | - | - | - |
| Zero relations, s=1, b=2^B | compendium Table 1 (all rows parsed): (B,n) = (4,8), (6,6), (8,16), (12,12), (12,24), (16,32), (18,18), (20,40), (24,24), (24,48), (28,56), (30,30), (30,60), (32,64), (36,36), (36,72), (40,80), (42,42), (42,84), (44,88), (48,48), (48,96), (52,104), (54,54), (56,112), (60,60), (60,120) | | | | all 1 or 2 | yes |
| Ternary and other bases (log 2 base 9, base 3^6 pi? no) | compendium sect. 10-11, (67)-(89); no ternary pi formula known | 3^m, 5^m, 10^m | | | n/a (not binary) | n/a |
| pi^2 in base phi | Cloitre; MathWorld eq. (34) | phi (irrational) | | | n/a | n/a |

Not read: Bellard's formula exact (b,n) as printed on Bailey's compendium (the compendium text I parsed has no "Bellard" hit), and Huvent's pi formula as printed there (compendium credits Huvent only for degree 2-3 formulas). The (b,n) for those two are therefore the user's values plus the structure read on Bellard's and Huvent's pages (period 10 with 4, and 12).

Rewriting note: (2^B, n) -> (2^(mB), mn) preserves n/B. Padding by zeros: a formula with ratio r is a formula with ratio mr (see Summary point 2). The same radix x with a different period n is the same ratio, e.g. P(1,2^B,n) and P(1,2^(2B),2n).

## Other ratios and irrational bases

What the literature has for radix other than 1/2 and 2^(-1/2):

- Kristensen and Mathiasen, "BBP-type formulas, an elementary approach", arXiv 2208.07696 (J. Number Theory 2022) [READ, full text converted]. Theorem 1: arg(1 + r e^{i theta}) = BBP(1, 1/r^b, b, A), A_j = r^j (-1)^(j+1) sin(j theta), theta = 2 pi a/b, any r in (0,1) (their "base" is r^(-b), with b their period). So radix r is arbitrary; formulas for pi arise when the triangle with vertices 0, 1, 1 + r e^{i theta} has both base angles rational multiples of pi. Their algorithm fixes an algebraic r and an even b, and finds relations with LLL. They study integer bases 2^4, 2^6, 2^12, 3^6, 2^20 with r = 1/sqrt2, 1/2, 1/sqrt2, 1/3, 1/sqrt2, and non-integer Pisot bases: golden ratio (pi = 10 BBP(1,15,15,.)? form: a pi formula in base phi with reduced period 15), 1+sqrt3 (a pi formula, period 12), x^2-2x-1 (2.414...), x^2-3x+1 (2.618...), x^3-x-1 (1.3247...), x^4-x^3-1. They state: "searching for BBP-type formulas in non-integer bases appear to be largely unexplored territory" (<15 words). They also say they cannot extract digits from these irrational-base formulas (open problem). A new pi formula in base 1+sqrt3 and a new formula for sqrt3*pi in base 2^12 are in the abstract/text. In their r = 1/sqrt2 examples (Lafont's null formulas, b=24) the integer base is 2^12, n/B = 2. No r = 2^(-1/3) or 2^(-1/4) is tried.
- Adegoke, "The golden ratio, Fibonacci numbers and BBP-type formulas" (Fibonacci Quart. 52 (2014), arXiv 1603.06307) [SNIPPET: abstract; the PDF text was unreadable]. phi-nary formulas for pi, log 2, log phi, sqrt2 arctan sqrt2; a snippet says the series are "technically not BBP-type" because they give no digit extraction, since phi is not an integer. Coefficients in Z[phi]. Adegoke also has "A non-PSLQ route" (1603.08209) [READ: abstract only] and arXiv 1603.07395 "general binary bases" [READ abstract]: bases b = 2^(12p), p odd; new binary formulas for pi*sqrt3, pi*sqrt3*log 2, sqrt3*Cl_2(pi/3), logs of an infinite set of primes, arctangents of an infinite set of rationals, new zero relations. These are about general integer binary b, not general radix.
- Chan: "pi in terms of phi" (Fibonacci Quart. 2006) and "More formulas for pi" (Amer. Math. Monthly 2006) [SNIPPET]. Pi in powers of 1/phi; Machin-like relations.
- Cloitre, arXiv 2508.03743 [READ abstract]: BBP-type pi^2 formula in base phi (found 2004), proof via fifth roots of unity; new Machin-like formula for zeta(3). MathWorld lists it as eq. (34) [READ].
- Cloitre arXiv 2507.20428 [READ listing]: base 16, remainder of Madhava-Gregory-Leibniz series.
- Pardeshi 2022 "Pi in golden ratio base phi" and Pain 2022 (arXiv 2205.08617 "Relations between pi and the golden ratio in BBP-type formulas") [SNIPPET].
- A 2024 note (arXiv 2409.10097, "A BBP-style computation for pi in base 5") [READ abstract and a summary]: says it is an open question whether this type of computation is possible for pi in bases not powers of 2 (the claimed "base 5 sqrt5" formula comes from Gaussian integers 1 +/- 2i and has a flaw in the tail bound per its own text). It asks about quadratic and more general algebraic extensions.
- Zhang's and Wei's work: not found in these searches; Adegoke 2023 (J. Integer Sequences vol. 26, "ade7") is said to cite Zhang for base-alpha expansions of pi*sqrt(alpha)*sqrt5 [SNIPPET]. Not read. Zhang: from memory, unverified.
- Borwein-Chamberland "Integer powers of arcsin": not searched or read; from memory, unverified, it concerns Maclaurin series of arcsin^k and BBP-like series for zeta values, with radix from central binomials, not radix 2^(-1/m).
- Any formula for pi in base 2^(1/4) or 2^(1/3): none found in any fetched page or search result. Last search explicitly looked for it.

## Exclusion results

- Borwein-Borwein-Galway, Canad. J. Math. 56 (2004) 897-925 [READ, full text]. Setup: b integer >= 2, not a proper power; "b-ary Machin-type BBP formula" = Q-linear combination of arctan(-b^(-m)), plus terms arctan(1/(1-2^m)) when b = 2. They work in the multiplicative group Q[i]^* (Gaussian integer factorization), with Bang/Zsigmondy primitive prime divisors and p-adic valuations (keywords list: Mersenne primes, Bang's theorem, Zsigmondy's theorem, primitive prime factors, p-adic analysis). Main result: pi has no Machin-type formula for b not 2; also for log 2-type: Theorem 7 (no Q-linear b-ary Machin-type ... for b > 2, not proper power) [READ, line truncated]. They say to their knowledge, when no Machin-type formula exists, no BBP formula of any form is known [READ]. Their own notation L(s,b,n,j) allows any n, but Machin-type restricts the arguments to Q[i], so it fixes integer radix. I found no mention of radix 2^(-1/m), roots of 2, Baker's theorem, or Kummer theory in the paper (grep for baker|kummer|root|algebraic returned only: algebraic closure, algebraic factoring into cyclotomic polynomials, algebraic number theory in appendix) [READ].
- MathWorld "BBP-Type Formula" [READ]: Borwein et al. 2004 showed pi has no non-binary Machin-type BBP arctangent formula; this does not rule out a different digit-extraction scheme in other bases. A search summary says a later survey claims "no base-n degree-1 BBP formula for pi unless n is a power of two" and calls the general question open [SNIPPET, source not identified].
- Bailey compendium [READ]: states that BGB 2004 "showed that there are no other degree-1 BBP-type for pi" except power-of-two bases. This is stronger than the theorem (Machin-type only).
- Barsky-Munoz-Perez-Marco, "On the genesis of BBP formulas", arXiv 1906.09629 (not Takahashi, I fetched it by mistake; it is relevant) [READ]: no base-3 formula for pi is known; degree-1 only; null formulas explained.
- Baker/Kummer: my searches found no paper using Baker's theorem or Kummer theory to exclude formulas in radix 2^(-1/m). Not found in the compendium either. So the exclusion for m >= 3 appears to be open in the literature, as far as these 8 searches and about 20 fetches show.
- [MY DERIVATION, not in literature] Why the field matters: a degree-1 formula with radix x = 2^(-1/m) and period n is a Q-combination of Re/Im log(1 - zeta x), zeta an n-th root of unity, in K = Q(zeta, 2^(1/m)). A pi formula needs a multiplicative relation in K^* among 1 - zeta x elements and roots of unity; this is where Kummer theory (degree of K(2^(1/m))/Q(zeta)) and prime factorization in K, or Baker-type independence, would enter. Not worked out here.

## Fewest-terms statements

- Takahashi, Ramanujan J. 51 (2020) 177-186, DOI 10.1007/s11139-018-0104-x [SNIPPET twice]: two new BBP-type formulas for pi; computation and verification need about 20 percent fewer terms than the digit-shift method using Huvent's formula, "known as the BBP-type formula with the least number of terms". Abstract page itself not read (publisher mirror returned 503 for the one that I tried).
- Bellard, bellard.org/pi/pi_bin/pi_bin.html [READ]: 43 percent faster than the previous formula (BBP); seven fractions per summand against BBP's four; author says whether a faster formula exists remains an open question.
- Wikipedia "Bellard's formula" [READ]: "about 43% faster" than BBP; no term counts; no Huvent. Wikipedia "BBP formula" [READ summary]: about 10 binary digits per 7 divisions for Bellard against 30 per 21 for Euler's second formula; no Huvent; no fewest-term claim.
- MathWorld "Pi Formulas" and "BBP-Type Formula" [READ]: no fewest-term claim, no Huvent.
- Bailey's compendium [READ]: no fewest-term claim; no Huvent pi formula listed (Huvent credited for degree 2, 3 formulas); no Bellard.
- French numbers page (Plouffe/Huvent collection, numbers.computation.free.fr, via the fr.wikipedia-style listing; fetched URL was fr.wikipedia.org/wiki/Formule_BBP) [READ summary]: counts displayed terms: Plouffe 4, Bellard 7, Huvent 8 (base 2^12, prefactors 1/128 and 1/256), A-W 3 (base 4), Huvent pi^3 and pi^4 also; says nothing explicit about fewest.
- y-cruncher documentation: URL returned 404; not read. Wikipedia "Pi formulas"/other pages not checked.
- Rates: BBP 4 terms per 4 bits (1.0 per bit); Bellard 7 per 10 (0.70); Huvent 8 per 12 (0.667); Adamchik-Wagon 3 per 2 (1.5 per bit; fewest terms per summand but slowest per bit). "Fewest terms" in Takahashi's sense is per computation, i.e. per bit; I did not verify this reading.
- Does any source ask whether one can do better? Only Bellard (faster formula "remains an open question", about his own formula in 1997). Barsky et al. and Kristensen-Mathiasen pose problems about extracting digits in irrational bases and higher degree, not about term count.

## Queries used (8 of 8 WebSearch)

1. Takahashi 2020 Bellard Huvent formula pi fewest terms BBP-type formula computing pi digits
2. Borwein Borwein Galway "Finite and infinite arctangent sums" BBP-type Machin-type base power of two
3. Huvent "Formules BBP" Gery Huvent pi formula 2^12 24 terms
4. BBP-type formula pi non-integer base cube root of 2 OR "fourth root" digit extraction polylogarithm radix algebraic
5. Chan golden ratio base BBP-type formula pi Adegoke "golden ratio" Fibonacci BBP digit extraction
6. Takahashi "On the computation and verification of pi using BBP-type formulas" Ramanujan Journal abstract
7. BBP formula pi base 2^(1/3) OR "cube root of 2" OR "2^{1/4}" impossible Baker theorem linear forms in logarithms Kummer BBP-type
8. Huvent BBP formula pi "Huvent" 2^12 "fewest terms" OR "fewer terms" OR "least number of terms" y-cruncher pi verification

## Pages fetched

Bailey compendium PDF (read via pdftotext; the full s=1 list and zero-relation table); MathWorld BBP-Type Formula; MathWorld Pi Formulas; Wikipedia Bellard's formula; Wikipedia BBP formula; arXiv API listing for "BBP-type" (31 entries); arXiv 2208.07696 abstract and PDF (Kristensen-Mathiasen, full text via pdftotext); arXiv 1603.07395 abstract; arXiv 1603.04561 abstract; arXiv 1603.08209 abstract; arXiv 2508.03743 abstract; arXiv 1603.06307 PDF (unreadable, outline only); arXiv 1906.09629 abstract and PDF (Barsky-Munoz-Perez-Marco, via pdftotext); arXiv 2409.10097 v2 (base 5 note); BGB 2004 Cambridge PDF (via pdftotext); davidhbailey.com digits.pdf (unreadable); bellard.org/pi/ and bellard.org/pi/pi_bin/pi_bin.html; fr.wikipedia Formule_BBP; portal.mardi4nfdi.de Takahashi record (503). Failed: numbers.computation.free.fr pages (two), bellard.org pibbp.html (404), y-cruncher page (404), arxiv 2203.00000 (404, placeholder).

## Sources

- https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf
- https://mathworld.wolfram.com/BBP-TypeFormula.html
- https://mathworld.wolfram.com/PiFormulas.html
- https://en.wikipedia.org/wiki/Bellard%27s_formula
- https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula
- https://arxiv.org/abs/2208.07696 (Kristensen, Mathiasen)
- https://arxiv.org/abs/1603.07395 , 1603.04561 , 1603.08209 , 1603.06307 (Adegoke and coauthors)
- https://arxiv.org/abs/2508.03743 (Cloitre)
- https://arxiv.org/abs/1906.09629 (Barsky, Munoz, Perez-Marco)
- https://arxiv.org/abs/2409.10097 (BBP-style computation, base 5)
- https://doi.org/10.4153/CJM-2004-041-2 (Borwein, Borwein, Galway)
- https://doi.org/10.1007/s11139-018-0104-x (Takahashi, abstract seen via search snippets only)
- https://bellard.org/pi/pi_bin/pi_bin.html
- https://fr.wikipedia.org/wiki/Formule_BBP
- Search-result pages: arXiv 2205.08617 (Pain), Adegoke FQ 52(2) and JIS 26 (ade7), Chan FQ 44(2) quartheichichan02, metafilter thread (forum, not authoritative)
