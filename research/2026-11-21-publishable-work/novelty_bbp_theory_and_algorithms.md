# Novelty check: BBP-type formula theory and digit-extraction algorithms (state of knowledge, 21 November 2026)

Scope: prior art for (1) the classification of all degree-1 binary BBP-type series for pi, (2) the prime-based cost measure and the optimal formula (7/24 against 1/3), (3) the "prime form" window algorithm. Verdict labels used throughout: **(a) already known**, **(b) close**, **(c) nothing found**.

Overall result in four lines. The dimension counts behind result 1 are already in print as unexplained PSLQ counts (Bailey's Table 1: 1, 5, 3 and 7 zero relations at lengths 8, 24, 40 and 120), and Borwein-Borwein-Galway posed the classification question explicitly in 2004; I found no proof, no use of Baker's theorem and no "period 120 is the end" statement anywhere. For result 2, a cost model exists (non-zero terms per bit; Bellard 7/10, Huvent 8/12) and Huvent (2001) already minimised term counts heuristically inside a parametrised family; the prime-based cost and any optimality proof were not found. For result 3, splitting a digit-extraction sum by primes is Plouffe 1996 / Bellard 1997 for decimal digits; no source applies it to the binary BBP sum, gives a per-prime closed form, or computes million-digit windows. Important limit: the shared web-search budget ran out after 17 searches, so the search behind result 3 and behind "records 2020-2026" is thin (see the search log).

## 1. BBP-type formula theory: is there a classification or dimension count of binary degree-1 formulas for pi, any use of Baker's theorem, any "period 120" or "finite set of roots of unity" statement?

### Takeaway
No classification, no Baker-type argument and no finiteness statement was found. What exists is (i) an experimental table of zero-relation counts that agrees with our dimensions, (ii) the classification question posed as open research problems by Borwein, Borwein and Galway, and (iii) repeated statements, up to 2023, that the zero relations are "mysterious".

### Cited Findings

**(a) Already known**

- Bailey's compendium (version dated April 8, 2023), Section 12 "Zero relations", Table 1, tabulates "the total number of linearly independent zero relations for various choices of s, b and n, including rewritings and unlisted relations", found with PSLQ. For degree 1, binary: (b, n) = (16, 8): 1; (64, 6): 1; (2^12, 24): 5; (2^20, 40): 3; (2^60, 120): 7; and 1, 5, 5, 5, 3 at (2^8,16), (2^24,48), (2^36,72), (2^48,96), (2^40,80); 27 binary degree-1 rows in all, none with n above 120. **Partly contains result 1**: the numbers, not the proof or the completeness. — [Bailey, "A Compendium of BBP-Type Formulas for Mathematical Constants", 2023](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)
- The same section states: "Aside from the discussion in [21], these zero relations are somewhat mysterious — it is not understood why zero relations occur for certain s, b and n, but not others." Reference [21] is Broadhurst, "Vanishing Polylogarithmic Ladders", manuscript, March 2000, "available from author" (unpublished). — [Bailey 2023](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)
- Bailey lists four degree-1 binary formulas for pi: the BBP formula P(1,16,8,(4,0,0,-2,-1,-1,0,0)); Formula 17 (Ferguson) P(1,16,8,(8,8,4,0,-2,-2,-1,0))/4; Formula 18 (Adamchik-Wagon, alternating base -4); Formula 19, P(1,-2^30,60,...) with 21 non-zero entries, "ascribed to Pschill" in Arndt-Haenel, *Pi Unleashed* (2001), p. 227. He adds that Formulas 18 and 19 "were originally found by Euler, as recently noted by Craig-Wood". Formula 19 is the binary series of pi/4 = 2 arctan(1/3) + arctan(1/7), the formula our notes call "Euler's". **Contains** the base formula of result 2. — [Bailey 2023](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf); [Craig-Wood, "Euler Found the First Binary Digit Extraction Formula for pi in 1779", Euleriana 3(1) (2023), 23-30, DOI 10.56031/2693-9908.1049](https://scholarlycommons.pacific.edu/euleriana/vol3/iss1/3)
- Borwein, Borwein and Galway (BBG), Canad. J. Math. 56 (5) (2004), 897-925: Theorem 7, "Given b > 2 and not a proper power, there is no Q-linear b-ary Machin-type BBP arctangent formula for pi", proved with Bang's theorem and valuations in Z[i] (keywords: "Bang's theorem, Zsigmondy's theorem, primitive prime factors, p-adic analysis"). For b = 2 they find by "a hand search" the factorizations (2-i)(3-i) = 5-5i, (2-i)^2(7+i) = 25-25i, (3-i)^2(7-i) = 50-50i, i.e. the three relations pi/4 = arctan(1/2)+arctan(1/3) (Euler 1738), 2arctan(1/2)-arctan(1/7) (Hermann 1706), 2arctan(1/3)+arctan(1/7) (Hutton 1776). **Contains** the three relations R1-R3 of our Theorem A; **does not contain** the statement that there are no others. — [BBG 2004, DOI 10.4153/CJM-2004-041-2](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf)
- Bailey summarises BBG more strongly than BBG prove: "there are no other degree-1 BBP-type for pi, except those ... whose 'base' is a power of two"; Bailey, Borwein, Mattingly and Wightwick (2013) word it correctly: "no degree-1 BBP-type formulas of Machin-type for pi, except those whose base is a power of two". — [Bailey 2023](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf); [Bailey-Borwein-Mattingly-Wightwick, "The Computation of Previously Inaccessible Digits of pi^2 and Catalan's Constant", 2013](https://www.davidhbailey.com/dhbpapers/bbp-bluegene.pdf)

**(b) Close**

- BBG, Appendix D "Comments and Research Problems", poses our questions as open: "(2) How many Q-linearly-independent binary Machin-type BBP arctangent zero relations exist? Are there good upper bounds?"; (3) the BBP formula "does not appear to be a Q-linear combination of Machin-type BBP generators ... Is there a simple way to derive (63) from a Machin-type formula?"; (7) Zsigmondy's theorem in number fields (their references: Schinzel, "Primitive divisors of the expression A^n - B^n in algebraic number fields", J. Reine Angew. Math. 268/269 (1974), 27-33; Bilu, Hanrot and Voutier, "Existence of primitive divisors of Lucas and Lehmer numbers", J. Reine Angew. Math. 539 (2001), 75-122) "should give an effective version of Zsigmondy's theorem for Q[i], providing an exclusion criterion"; "(10) ... L(1,b,n,j) = -(1/n) b^(j/n) sum_r zeta_n^(-rj) ln(1 - zeta_n^r b^(-1/n)) ... Can our techniques be applied to determine whether kappa is a linear combination of L(1, b^m, n, j), with b, and perhaps n, fixed? This would probably require a good understanding of Q[zeta_n, b^(1/n)], among other things"; "(11) How can we justify the idea that our limited set of 'Machin-type' BBP generators gives all (or most) 'interesting' arctans and logs?" **Poses, does not solve**: problem (2) is our Theorems A/B, problem (10) is the setting of our Parts III and IV (Fourier decomposition into logarithms of 1 - zeta x, the field Q(zeta, 2^(1/n))). — [BBG 2004](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf)
- Chamberland, "Binary BBP-Formulae for Logarithms and Generalized Gaussian-Mersenne Primes", J. Integer Sequences 6 (2003), Article 03.3.7: builds binary BBP formulas for log p from Re log Phi_m((+-1+i)/2^n) and Re log Phi_m((+-1+sqrt(3) i)/2^n), with the subclass Re log Phi_m((1+i)/2) and a link to Aurifeuillian factorizations (cites Schinzel 1962, Stevenhagen, Brent). Real parts only; no arctangents, no pi, no zero-relation count, no classification; "it is still unknown whether log 23 has a binary BBP-formula". **Partly contains** the atoms of our Part II (cyclotomic polynomials evaluated at 1+i, Aurifeuillian norms); **does not address** the classification. — [Chamberland 2003](https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf)
- Barsky, Munoz and Perez-Marco, "On the genesis of BBP formulas", Acta Arith. 198 (2021), 401-426, arXiv:1906.09629: a general procedure generating BBP formulas from log(1 - s) at complex s (they use s = 1+i, (1+i)/2, (7+i)/8 and the factorization 1+i = ((2+i)/2)^2 ((7+i)/8)^(-1) for Bellard's formula). They write "Although we do not find new BBP formulas, we recover the most important ones", "The origin of null BBP formulas is somewhat mysterious", and ask "if all null BBP formulas of degree 1 can be obtain[ed] combining formulas from Theorem 1.1 for different values of s". No Baker, no cyclotomic fields, no dimension count. **Poses a version of the completeness question; does not answer it.** — [arXiv:1906.09629](https://arxiv.org/abs/1906.09629); [full text](https://ar5iv.labs.arxiv.org/html/1906.09629)
- Kristensen and Mathiasen, "BBP-type formulas -- an elementary approach", arXiv:2208.07696 (2022): LLL search over series for arg(1 + r e^(i theta)), theta a rational multiple of pi (so implicitly over roots of unity). Their Table 1 lists known null formulas: base 2^4: 1; 2^6: 1; 2^12: 5; 2^20: 3; 3^6: 2; they state "it is entirely possible that we have just not found all zero formulas". New formula: sqrt(3) pi = (9/2^12) P(1, 2^12, 24, ...). No Baker, no completeness. **Does not contain** result 1. — [arXiv:2208.07696](https://arxiv.org/abs/2208.07696); [full text](https://ar5iv.labs.arxiv.org/html/2208.07696)
- Huvent, "Formules BBP" (22 February 2001): an 11-parameter family of integrals with denominator y^120 - 2^60 whose degree-0 value is a combination of pi, ln 2, ln 3, ln 5 and arctan 2; from it he derives pi formulas of base 2^4, 2^12, 2^20 (which collapses to the alternating base -2^10 form) and 2^60 (length 120, 42 non-zero coefficients). Length 120 is the largest he uses; he does not say it is the largest possible. **Partly contains** the period-120 structure as a construction, not as a theorem. — [Huvent 2001 (PDF)](https://c8cf35d7-ad1f-4031-84c6-bb15d656c101.filesusr.com/ugd/a97b48_b22c37a8b999457f85fe6d8528582dfa.pdf)
- Broadhurst (1998): polylogarithmic ladders whose arguments "satisfy z^8 = 1/16^p, with p = 1, 3, 5", i.e. moduli 2^(-1/2), 2^(-3/2), 2^(-5/2), the three scales of arctan(1), arctan(1/3), arctan(1/7). Higher weight, no classification. — [arXiv:math/9803067](https://arxiv.org/abs/math/9803067)
- Gasull, Luca and Varona, "Three essays on Machin's type formulas", Indag. Math. 34 (2023), 1373-1396, arXiv:2302.00154: finds all two-term Machin formulas with both arguments of the form b/2^a. Two terms only; not BBP series. — [arXiv:2302.00154](https://arxiv.org/abs/2302.00154)
- Adegoke, Lafont and Layeni, Notes on Number Theory and Discrete Mathematics 17(4) (2011), 18-32 (arXiv:1603.07395): explicit degree-1 and degree-2 formulas in bases 2^(12p), p odd, including five base-2^12 zero relations; no completeness claim. — [NNTDM page](https://nntdm.net/?p=675); [arXiv:1603.07395](https://ar5iv.labs.arxiv.org/html/1603.07395)

**(c) Nothing found**

- No source uses Baker's theorem (linear forms in logarithms) on BBP-type series for pi. Checked: BBG 2004, Bailey 2023, Barsky et al. 2021, Kristensen-Mathiasen 2022, Chamberland 2003, Lafont 2011, Adegoke 2012 (same links as above); the one web search aimed at this (query 1) returned none. The Wikipedia article on Baker's theorem lists no such application. — [Baker's theorem, Wikipedia](https://en.wikipedia.org/wiki/Baker%27s_theorem)
- No source states that all degree-1 binary formulas for pi have period dividing 120, that only finitely many roots of unity occur, or that the pi-or-zero patterns form an 8-dimensional space. No source states a "sub-series lemma" or uses Kummer theory for bases 2^(1/n); BBG's problem (10) only names the field Q[zeta_n, b^(1/n)] as what one would need to understand. — [BBG 2004](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf)

### Inferences
- Bailey's counts match our dimensions exactly where I can compare: our pi-or-zero spaces at periods 8, 24, 40, 120 have dimension 2, 6, 4, 8 (outside_family_findings.md), i.e. 1, 5, 3, 7 zero relations plus one dimension for pi; Bailey's table has 1, 5, 3, 7. His rows at lengths 16, 32, 48, 64, 72, 80, 96 show no growth beyond the lifts of 8, 24, 40, as "only 24 roots of unity matter" predicts, and his base-2^n, length-n rows (our F_1) are all 1, matching our one-dimensional F_1. A paper should present Theorem C as the explanation and proof of Bailey's Table 1 (27 published data points) and derive every row from it; that is both the strongest validation and the correct statement of what is new.
- What is new relative to the literature, if the proofs hold: completeness (no further relations at any period), the reduction to 24 roots and 13 multiplicative relations, the Baker step, the answer to BBG's problems (2) and (10) for kappa = pi and b = 2, and Part IV (bases 2^(1/n)). The count "7 at length 120" must not be claimed as a discovery.
- BBG's problem (3) (deriving the 1995 BBP formula from Machin-type generators) is answered by "arctan(1) series plus a logarithm-type zero series", which Bailey already records as Formula 17 = BBP + (1/4) x Relation 111; that part is known.

### Gaps
- Broadhurst's "Vanishing Polylogarithmic Ladders" (2000) is unpublished and I could not read it. It is the only item Bailey credits with any explanation of zero relations; its content should be checked (by writing to the author) before claiming the first structural account.
- From memory, not verified in this session (publisher pages returned HTTP 403): the transcendence literature has the same method in the unweighted case. Baker, Birch and Wirsing, "On a problem of Chowla", J. Number Theory 5 (1973), 224-236, classify periodic f with sum f(n)/n = 0 by Baker's theorem and cyclotomic fields; Adhikari, Saradha, Shorey and Tijdeman, "Transcendental infinite sums", Indag. Math. 12 (2001), 1-14, apply Baker's theory to sums with periodic numerators and geometric factors. If these recollections are right, our Step 1 is a known technique applied to a new family, and the paper should cite them. This needs a dedicated search.
- I could not date Table 1 (the 2004 version of the compendium was unreachable); Lafont (2011) and Kristensen-Mathiasen (2022) show the counts 5 and 3 were known by then.
- MathOverflow and Mersenneforum were not searched (budget exhausted).

## 2. Zero relations ("null BBP formulas"): who catalogued them, and is adding a zero relation to minimise extraction cost in the literature?

### Takeaway
Zero relations are catalogued (Bailey; proofs by Lafont and Adegoke) and it is standard that adding one gives a variant formula. Choosing the variant with the fewest terms was done heuristically by Huvent in 2001. No source optimises against a prime-based cost or proves an optimum.

### Cited Findings

**(a) Already known**

- Catalogue: Bailey's Section 12 lists degree-1 binary relations 111 (base 16), 112 (base 64), 113-118 (base 2^12, length 24), 119-122 (base 2^20, length 40); larger ones are "omitted — although the author has a complete set". Credits: "Relation 111 appeared in [BBP 1997]. Relation 112 and 113 were given in [Bailey-Crandall 2001]. Relations 114 and 122 are due to Jaume Oliver Lafont. Lafont subsequently proved 113 through 121." — [Bailey 2023](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)
- Proofs: Lafont, "Degree 1 BBP-Type Zero Relations" (manuscript, 27 January 2011) proves eight relations (five of length 24 in base 2^12, three of length 40 in base 2^20) by Fourier analysis of the coefficient vectors; it claims only that "All degree-1 binary formulas currently listed in the Compendium are now proved". Lafont's OEIS wiki page obtains zero relations by subtracting two expansions of the same constant (Bellard's formula minus Ferguson's formula gives one of the form 0 = P(1, 2^20, 40, A)). — [Lafont 2011](https://www.slideshare.net/slideshow/zero-relations/13076965); [Lafont, OEIS wiki](https://oeis.org/wiki/User:Jaume_Oliver_Lafont/BBP)
- Higher-degree zero relations (degrees 2 to 4, bases 2^12 and 2^60): Adegoke, Integers 12 (2012), 345-371, arXiv:1603.05810; no count, no completeness claim. — [arXiv:1603.05810](https://ar5iv.labs.arxiv.org/html/1603.05810)
- The device: "by simply adding a rational multiple of one of these zero relations to one [of] the formulas above ... one can produce a valid variant of that formula. Clearly infinitely many variants can be produced in this manner." Formulas 17 and 18 "can be obtained from the original BBP formula for pi (formula 1) by adding 1/4 times relation 111". — [Bailey 2023](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)
- A database with a zero-relation list: the CARMA BBP-type formula database (Tam, with Allingham, Bailey, Borwein, Mattingly; 2011). — [CARMA BBP database](https://carmamaths.org/resources/bbp/)

**(b) Close**

- Huvent (2001) chooses the free parameters of his family to minimise the number of terms: "Pour avoir des formules BBP ayant peu de termes ..."; "On choisit les autres coefficients de maniere a annuler le plus de coefficients de P ... Le meilleur choix semble etre ..." giving pi = (1/128) sum 2^(-12i) (768/(24i+3) + 512/(24i+4) + 128/(24i+6) - 16/(24i+12) - 16/(24i+14) - 12/(24i+15) + 2/(24i+20) - 1/(24i+22)), 8 terms per 12 bits; and for base 2^60, "Le choix qui conduit a une formule ayant le moins de termes possible semble etre ..." (42 non-zero coefficients, which he rewrites as two alternating series in bases -1024 and -64, the Hutton/Euler formula). "Semble etre" = heuristic; no proof. **Partly contains result 2**: systematic cost minimisation over a linear family of pi formulas, with cost = number of terms. — [Huvent 2001 (PDF)](https://c8cf35d7-ad1f-4031-84c6-bb15d656c101.filesusr.com/ugd/a97b48_b22c37a8b999457f85fe6d8528582dfa.pdf); formulas as transcribed in [Formule BBP, Wikipedia (fr)](https://fr.wikipedia.org/wiki/Formule_BBP)
- Barsky et al. (2021) call null formulas "very interesting and useful for rewrit[ing] BBP formulas" and hope the approach "can be useful in finding more efficient BBP-formulas for pi"; they give none. — [arXiv:1906.09629](https://ar5iv.labs.arxiv.org/html/1906.09629)
- Bellard's own derivation (1997) uses pi/4 = 2 arctan(1/2) - arctan(1/7) and two series; the page (as summarised; its formulas are images) mentions no null relation. — [Bellard, "A new formula to compute the n'th binary digit of pi"](https://www.bellard.org/pi/pi_bin/pi_bin.html)

**(c) Nothing found**

- No source minimises a cost other than the number of terms, and none proves that a formula is optimal in any class (sources as above; Bellard: whether a faster formula exists "remains an open question"). — [Bellard 1997](https://www.bellard.org/pi/pi_bin/pi_bin.html)

### Inferences
- Our note says the Bellard formula was found by adding a zero series. For the 1995 BBP formula this is documented (Bailey, Formula 17). For Bellard's formula the documented route is a Machin-type relation plus merging of terms with equal denominators; the wording should be corrected or checked against Bellard's PDF.
- Huvent's family has 11 parameters and 4 linear conditions to kill ln 2, ln 3, ln 5 and arctan 2, so it is at most 7-dimensional, against our 8 (my reading of his equation (4); not checked in detail). His 2^60 formula with 42 coefficients is our "Euler" formula; our optimal formula (55 non-zero entries per period 120) is therefore not a fewest-terms formula and lies outside what a term-count search would select.

### Gaps
- I did not find Jauregui's work on zero relations (named in the brief); no search could be run for it.
- Whether Huvent's "fewest terms" choices are optimal in our 8-dimensional space is a question our classification can settle and the literature does not.

## 3. Digit-extraction algorithms: does any source split the binary BBP sum by primes, give a closed form per prime, or compute long windows at a far position?

### Takeaway
Splitting by primes is the core of the decimal-digit algorithms of Plouffe (1996), Bellard (1997) and Gourdon (2003), applied to series with binomial denominators and costing n^2 or more. Every binary implementation I could read evaluates the BBP sum term by term with one modular exponentiation per term. I found no per-prime closed form for the binary sum, no product-tree summation, and no window longer than about 1,000 bits at a far position; this "nothing found" rests on few searches.

### Cited Findings

**(a) Already known**

- Plouffe (written 30 November 1996; arXiv:0912.0303, 2009): uses pi + 3 = sum n 2^n n!^2/(2n)! and "a new algorithm that simply splits an ordinary fraction into its components": 1/M is written modulo 1 as a sum of fractions with prime-power denominators, each handled with word-size arithmetic; the abstract claims roughly O(n^3 log^3 n) time and very little memory. He states "I have not found a faster algorithm or proved that it cannot exist." **Contains the general device of result 3** (partial fractions by prime, sum of C_p/p^e modulo 1), for a non-BBP series. — [arXiv:0912.0303](https://arxiv.org/abs/0912.0303)
- Bellard (1997), "Computation of the n'th digit of pi in any base in O(n^2)": a sum over primes a with 2 < a < 2N, per-prime modular loop with a modular inversion; "slower than the BBP algorithm but works in any base". Gourdon (11 February 2003), "Computation of the n-th decimal digit of pi with low memory": per Plouffe, "not based on the same idea but inspired from it ... can reach 4000000 digits in a matter of hours". — [Bellard, pi_n2](https://www.bellard.org/pi/pi_n2/pi_n2.html); [arXiv:0912.0303](https://arxiv.org/pdf/0912.0303); [Gourdon reference in Wikipedia](https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula)
- The standard binary algorithm: fractional parts of sums of 16^(d-k)/(8k+j) by binary exponentiation modulo each denominator; run time "increase[s] roughly linearly with the position d"; a result is checked by repeating at position d - 1. — [Bailey, "The BBP Algorithm for Pi", 2006](https://www.davidhbailey.com/dhbpapers/bbp-alg.pdf)
- Sze (2010): Bellard's formula, sum split at k < (n+x)/4 into terms needing modular exponentiation and a short tail; successive squaring or Montgomery's method; cost O(p (n^(1+eps) + p)) bit operations for p bits at position n; about 0.7 n terms. The fetch of the full text reported no per-prime method anywhere in the paper (the tool's reading, not a sentence of Sze's). — [arXiv:1008.3171](https://arxiv.org/abs/1008.3171); [full text](https://ar5iv.labs.arxiv.org/html/1008.3171)
- Takahashi's BBP papers concern the arithmetic of the term-by-term method: "Computation of the 100 quadrillionth hexadecimal digit of pi on a cluster of Intel Xeon Phi processors", Parallel Computing 75 (2018), 1-10; "On the computation and verification of pi using BBP-type formulas", Ramanujan J. 51 (2020), 177-186; "On the use of Montgomery multiplication in the computation of binary BBP-type formulas for mathematical constants", Ramanujan J. 59 (2022), 211-219; "On the Division in the Computation of Binary BBP-Type Formulas for Mathematical Constants", NUMTA 2023, LNCS 14477, 323-330 (Springer, 2025). — [Takahashi, publication list](https://www.hpcs.cs.tsukuba.ac.jp/~daisuke/pub.html)
- y-cruncher's BBP digit extractor (integrated March 2015, revamped October 2019, formal benchmark since July 2024) is a term-by-term program for a short run of hexadecimal digits at an offset. — [y-cruncher version history](https://www.numberworld.org/y-cruncher/version_history.html)
- Formal verification of a BBP computation (billionth hexadecimal digit, in Coq): Bertot, Rideau and Thery, "Distant decimals of pi", arXiv:1709.01743, J. Automated Reasoning. — [arXiv:1709.01743](https://arxiv.org/abs/1709.01743)

**(b) Close**

- Window lengths in published far-position runs: Bellard 152 bits at the trillionth bit; PiHex 64 bits at 10^15; Sze 1,000 bits at 10^13+1, 992 bits at 10^14+1, 228 bits at 10^15+1, 256 bits at 2x10^15; Takahashi 32 hexadecimal digits per run at 10^17; Bailey's table about 14 hexadecimal digits per position. Sze's cost formula is linear in the window length p times the position n. — [arXiv:1008.3171](https://ar5iv.labs.arxiv.org/html/1008.3171); [Bailey 2006](https://www.davidhbailey.com/dhbpapers/bbp-alg.pdf); [Takahashi, record page](https://www.hpcs.cs.tsukuba.ac.jp/~daisuke/pihex.html)

**(c) Nothing found**

- No source splits the binary BBP sum by primes, states frac(2^m pi) = sum over odd primes of C_p/p^E (mod 1), gives C_p = +-w 2^m mod p, uses a periodic shortcut for small primes, or sums the fractions with product trees. Searched: queries 16 and 17 (no relevant hit); read: Bailey 2006, Sze 2010, Plouffe 1996, Bellard pi_n2, y-cruncher version history, Takahashi's titles (links above).
- No source computes a window of millions of digits at a far position or analyses "block"/"window"/"segment" BBP beyond Sze's O(p (n^(1+eps) + p)). — [arXiv:1008.3171](https://ar5iv.labs.arxiv.org/html/1008.3171)

### Inferences
- The accurate framing for result 3: "the splitting-by-primes idea of Plouffe and Bellard, applied to the binary BBP sum, where Fermat's little theorem collapses each prime's contribution to one modular power". Plouffe 1996 and Bellard 1997 must be cited as the origin of the device.
- A context figure for timing claims: y-cruncher needed about 20 hours (Bellard) and 28 hours (4-term BBP) for the hexadecimal check near position 2.6x10^13 on an Intel i9-7900X in December 2018. Scaled linearly this is roughly 280 s per 10^11 positions on that 10-core CPU, the same order as our 107-114 s for 64 hexadecimal digits at 10^11 on a GPU laptop. For short windows the prime form is therefore not obviously faster than the best term-by-term code; the claim that survives is the long window. Different hardware and years; indicative only. — source of the y-cruncher figures: [Yee, "Google Cloud Topples the Pi Record", 2019](https://www.numberworld.org/blogs/2019_3_14_pi_record/)

### Gaps
- Gourdon's paper, Karrels's own description of his GPU code and the abstracts of Takahashi's four papers could not be opened (site unreachable or publisher redirect). My recollection that Takahashi (2020) exploits terms shared between two BBP-type formulas to cheapen verification is unverified.
- No search of Mersenneforum, MathOverflow, GitHub or arXiv listings for "prime-by-prime BBP" could be run. A per-prime BBP evaluation in a forum post or code repository cannot be excluded. This is the weakest part of the check.

## 4. Current records for binary digit extraction of pi, and 2020-2026 work on faster BBP evaluation

### Takeaway
The farthest position I could document is Takahashi's 10^17-th hexadecimal digit (December 2016). The only 2020-2026 developments found are Takahashi's arithmetic papers (2020, 2022, 2025) and y-cruncher's switch from Bellard's to Huvent's formula (2024). I could not search for records after 2016.

### Cited Findings
- Bellard: 400 billionth bit (7 October 1996), 1,000 billionth bit (September 1997), 152 bits, 12 days on about 20 workstations. — [Formule BBP, Wikipedia (fr)](https://fr.wikipedia.org/wiki/Formule_BBP); [Bailey 2006](https://www.davidhbailey.com/dhbpapers/bbp-alg.pdf)
- PiHex (Percival), Bellard's formula: 5 trillionth bit (30 August 1998), 40 trillionth (9 February 1999), quadrillionth (11 September 2000; 1,734 computers in 56 countries, 1.2 million CPU-hours). — [PiHex, Wikipedia](https://en.wikipedia.org/wiki/PiHex)
- Sze (Yahoo, July 2010): 256 bits ending at bit 2,000,000,000,000,252; 23 days, 503 CPU-years, Hadoop, Bellard's formula; published in IEEE CloudCom 2010, pp. 727-732. — [Sze's page](https://szetszwo.github.io); [arXiv:1008.3171](https://arxiv.org/abs/1008.3171)
- Karrels (2013): bits near position 8x10^15 on NVIDIA GPUs (one machine with four GTX 690, one with two GTX 680, 24 with one GTX 570); 35 days, then a 26-day verification run. Press reports only. — [SlashGear, 15 March 2013](https://www.slashgear.com/nvidia-powered-computers-break-pi-calculation-record-15274237)
- Takahashi (declared 18 December 2016): hexadecimal digits from the 10^17-th (A937EB59439E485E); two runs of 32 hexadecimal digits at 10^17 and 10^17 - 1, Bellard's formula, 512 nodes of Oakforest-PACS (Xeon Phi 7250), about 320.5 hours each. — [Takahashi, record page](https://www.hpcs.cs.tsukuba.ac.jp/~daisuke/pihex.html)
- BBP as verifier of full computations: Kondo-Yee 2010 (5 trillion digits; 64 hours of BBP); 31.4 trillion digits (2019; Bellard 7-term about 20 h, BBP 4-term about 28 h). Current full-digit record on the y-cruncher page: 314 trillion digits (completed 19 November 2025). — [Bailey et al. 2013](https://www.davidhbailey.com/dhbpapers/bbp-bluegene.pdf); [Yee 2019](https://www.numberworld.org/blogs/2019_3_14_pi_record/); [y-cruncher records](https://www.numberworld.org/y-cruncher/records.html)
- y-cruncher: v0.7.8 (27 October 2019) raised the extractor's offset limit (from 2^46 to about 2^59 with Bellard's formula on AVX2, as I read the garbled exponents); v0.8.4 (21 February 2024): "The BBP digit extractor now supports Huvent's BBP formula which is slightly faster than Bellard's"; v0.8.5 (1 July 2024): "The default BBP algorithm has been changed to Huvent's formula." — [y-cruncher version history](https://www.numberworld.org/y-cruncher/version_history.html)
- Other recent BBP papers, not about speed or classification: Plouffe, arXiv:2201.12601 (2022, digits via Euler/Bernoulli numbers); Cloitre, arXiv:2507.20428 (2025, BBP-type formula for the remainder of the Leibniz series). — [arXiv:2201.12601](https://arxiv.org/abs/2201.12601); [arXiv:2507.20428](https://arxiv.org/abs/2507.20428)

### Inferences
- Records are stated as a position with tens of digits. A "window" record (10^6 hexadecimal digits at 10^10) has no published counterpart to compare with; it is a different quantity and should be described so, not as a digit-extraction record.

### Gaps
- Records after December 2016 and any GPU BBP work from 2020-2026: the search (query 18) was refused for budget. Absence in these notes is not evidence of absence.

## 5. Published cost models for BBP formulas and optimality statements

### Takeaway
The published cost model is "non-zero terms per bit" (equivalently divisions or modular exponentiations per bit). Under it the best formula in use is Huvent's (8 terms per 12 bits), and nobody claims or proves an optimum. A cost defined by the first multiple of each prime that enters a denominator was not found.

### Cited Findings
- Bellard (1997): his formula computes the n-th binary digit "43% faster" than the BBP formula; whether a faster one exists "remains an open question". — [Bellard 1997](https://www.bellard.org/pi/pi_bin/pi_bin.html)
- Barsky et al. (2021): "We can measure the efficiency of a BBP-like formula ... as m/log b, where m is the number of non-zero coefficients"; BBP has efficiency 1, Bellard's 7/10, "a 43% faster"; Bellard's "seems to be the most efficient one for the purpose of computation of deep binary digits of pi". — [arXiv:1906.09629](https://ar5iv.labs.arxiv.org/html/1906.09629)
- Wikipedia (BBP formula): Euler's second formula "obtains asymptotically 30 binary digits per 21 divisions", "tantamount to the simpler Bellard's formula's 10 per 7"; the algorithm is "linearithmic". — [BBP formula, Wikipedia](https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula)
- Sze (2010): about 0.7 n terms for position n with Bellard's formula. — [arXiv:1008.3171](https://ar5iv.labs.arxiv.org/html/1008.3171)
- Huvent (2001) counts terms and picks the minimum he can find ("semble etre"); y-cruncher (2024) calls his formula "slightly faster than Bellard's". — [Huvent 2001](https://c8cf35d7-ad1f-4031-84c6-bb15d656c101.filesusr.com/ugd/a97b48_b22c37a8b999457f85fe6d8528582dfa.pdf); [y-cruncher version history](https://www.numberworld.org/y-cruncher/version_history.html)

### Inferences
- Computed by me from the cited formulas (script check: both Huvent formulas equal pi to double precision):

| formula | terms per bit (published measure) | mean(1/s) (our measure) |
|---|---|---|
| BBP 1995 | 4/4 = 1 | 3/4 |
| Bellard 1997 | 7/10 = 0.700 | 1/2 |
| Hutton/Euler, Bailey Formula 19 | 21/30 = 0.700 | 1/3 |
| Huvent 2001, base 2^12 (both variants) | 8/12 = 0.667 | 5/12 |
| ours (Theorem E) | 55/60 = 0.917 | 7/24 |

- Consequences. (i) The two measures rank formulas differently; ours is only meaningful for the prime form, and under the published measure our formula is slower than Bellard's. The paper must say so. (ii) "12.5% better than Euler's" should be accompanied by the comparison with Huvent's formula, the current y-cruncher default (5/12 against 7/24 in our measure). (iii) Barsky et al.'s 2021 remark that Bellard's formula seems the most efficient overlooked Huvent's 2001 formula. (iv) The minimum number of terms per bit over all degree-1 binary formulas is an open, natural question that our 8-dimensional classification could settle (is 8/12 optimal?); a proven answer would matter to implementers more than the 7/24 result.
- That y-cruncher's "Huvent's formula" is one of the two 8-term base-2^12 formulas is my inference from "slightly faster" (4.8% fewer terms per bit); the changelog does not print the formula.

### Gaps
- No source defining cost by primes, by state per bit, or by the multiplier s was found; one general search (query 7) covered cost models.
- Lehmer's measure for Machin-like arctangent formulas is an established cost model for full-precision computation; a 2025 arXiv paper on it (arXiv:2508.08307, "Constrained PSLQ Search for Machin-like Identities Achieving Record-Low Lehmer Measures") appeared in results but I did not read it; Gasull-Luca-Varona (2023) prove two-term formulas with arbitrarily small Lehmer measure exist ([arXiv:2302.00154](https://arxiv.org/abs/2302.00154)). It is the nearest analogue of "optimising a formula against a cost".

## Search log and method notes

Web searches run: **17** (the brief asked for at least 18; the 18th was refused with "this turn's web search budget is used up (limit: 200 WebSearch calls per turn, shared by every agent in it)"). No workaround was used. After that point I worked only by fetching primary-source pages directly.

1. classification of BBP-type formulas for pi Baker's theorem linear forms in logarithms
2. Bailey "A compendium of BBP-type formulas for mathematical constants" zero relations
3. Borwein Borwein Galway "Finding and excluding b-ary Machin-type individual digit formulae"
4. Chamberland "Binary BBP-formulae for logarithms and generalized Gaussian-Mersenne primes"
5. Plouffe "On the computation of the n'th decimal digit of various transcendental numbers"
6. Sze "The two quadrillionth bit of pi is 0" Hadoop BBP Bellard formula
7. Bellard formula pi 43% faster BBP "terms" efficiency digit extraction
8. Karrels GPU BBP pi hexadecimal digits record CUDA quadrillionth
9. y-cruncher BBP digit extraction verification hexadecimal digits Bellard formula implementation
10. "Distant decimals of pi" arXiv 1709.01743
11. Gourdon "N-th digit computation" Bellard algorithm O(n^2) decimal digit pi
12. Lafont "Degree 1 BBP-type zero relations" binary proofs
13. Huvent formula pi BBP y-cruncher "slightly faster than Bellard"
14. Gery Huvent "Formules BBP" pi formula 2001
15. Takahashi "100 quadrillionth hexadecimal digit of pi" Xeon Phi Parallel Computing 2018
16. BBP digit extraction "prime" decomposition partial fractions binary digits pi "modulo p" sum over primes hexadecimal
17. compute block of hexadecimal digits of pi at far offset faster than digit by digit BBP "binary splitting" window segment
18. (refused, not run) BBP hexadecimal digit of pi record position 2020..2026 beyond "100 quadrillionth" new record digit extraction GPU

Full texts read (converted from PDF or fetched): Bailey 2023 compendium; BBG 2004; Plouffe 1996/2009; Huvent 2001; Chamberland 2003; Bailey 2006; Bailey-Borwein-Mattingly-Wightwick 2013. Read through a summarising fetch (quotations are as returned by the tool and should be re-checked against the originals before being printed): Barsky-Munoz-Perez-Marco; Kristensen-Mathiasen; Sze; Lafont; Adegoke; Adegoke-Lafont-Layeni; Bellard's pages; y-cruncher pages; Wikipedia pages.

Could not be opened: Gourdon 2003 (numbers.computation.free.fr unreachable); Karrels's site; ScienceDirect, Springer and AMS pages (403 or login redirect); the 2004 compendium copy; Craig-Wood's full text; Broadhurst's unpublished manuscript.
