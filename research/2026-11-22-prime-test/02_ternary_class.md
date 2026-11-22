# Ternary (base 3) degree-1 BBP-type formulas: what is known, what is open, what would change

Date of research: 2026-11-22. Tags: [READ] = I opened the source and saw it; [SNIPPET] = search-result text only; [INFERRED] = my own reasoning; [COMPUTED] = I ran code (scripts in the session scratchpad, results quoted below).

## Key findings (most important first)

1. **Borwein-Borwein-Galway (BBG 2004) exclude much less than the folklore says.** Their Theorem 7 says: for b > 2 not a proper power, pi is not a Q-linear combination of the generators arctan(b^(-m)) (m >= 1) [READ, p. 918]. That is all. It does not cover real arguments b^(-m/2) (so not pi*sqrt(3)-type generators), complex or Gaussian/Eisenstein bases, series with other periods, or any degree above 1. Bailey's compendium (April 2023 version) states the result more broadly, as "no other degree-1 BBP-type for pi except those whose base is a power of two" [READ, p. 2]. That wording overstates what BBG prove. MathWorld [READ] and the BBG abstract [READ] state it correctly (Machin-type only).

2. **BBG's own open problem (their list "D Comments and Research Problems", item 10, p. 924) is exactly the question your method answers for b = 2 and could answer for b = 3.** Restated: with n and b fixed (and perhaps varying powers of b), can one decide whether pi is a Q-linear combination of the numbers L(1, b^m, n, j) = sum over k >= 0 of 1/((nk+j) b^(mk)), 1 <= j <= n? They add that this "would probably require a good understanding" of Q[zeta_n, b^(1/n)] [READ]. The "Problem 10" in the earlier research is this item. Items 7 (Zsigmondy over Q[i]) and 9 (allow b in Z[i]) are also relevant.

3. **Zudilin's base-5 question is weaker than described, and its flaw is structural.** The question is one sentence in section 2 of arXiv:2409.10097: it is open whether a BBP-type computation is possible for pi in other bases [READ]. The "base 5" series is the arctangent series at 1/(1 - 2i), whose terms have numerators b_n obeying a linear recurrence with characteristic roots of norm 25, so they are NOT periodic [READ + INFERRED]. It is therefore not in the BBP class (periodic coefficients) at all. The paper calls itself a joke, and section 3 ("An obvious flaw") asks for better formulas over quadratic or higher algebraic extensions.

4. **I found no classification of base-3 degree-1 series, no proof that pi (as opposed to pi*sqrt(3)) lacks one, and no criterion for which log p have ternary formulas.** Evidence: OpenAlex citing lists (BBG: 22 works; Chamberland 2003: 13; Adegoke ternary: 0 indexed; Barsky-Munoz-Perez-Marco: 6; Kristensen-Mathiasen: 2) contain nothing of the kind by title [READ titles only]; web searches on Baker's theorem, Eisenstein integers and ternary BBP found nothing [SNIPPET]. This supports novelty but does not prove it (see "could not verify").

5. **The OEIS list A165132 (log p for p = 2,3,5,7,11,13) is not even closed under elementary identities.** Using Bailey's general-base generators, log 41, log 61 and log 73 also have ternary formulas: 3^4+1 = 2*41, 3^5+1 = 4*61, 3^6+1 = 2*5*73 [COMPUTED]. I checked numerically that log 41 = (sum of k>=1 of (-1)^(k-1)/(k*81^k)) + 4 log 3 - log 2 to 30 digits [COMPUTED]; the series is a degree-1 series in base 3^8. So the "known" list reflects what was found by PSLQ, not a closure. [INFERRED: I found no source listing 41, 61, 73 as ternary.]

6. **Base 3 has a clean Eisenstein analogue of the binary set-up.** With t = 1 - omega (omega a primitive cube root of 1, norm 3) one has t^2 = -3*omega, exactly parallel to (1+i)^2 = 2i [COMPUTED]. So 3^(-floor(k/2)) = t^(-2 floor(k/2)) (-omega)^(floor(k/2)) and the series is a combination of Log(1 - r/t) with r roots of unity, the ring being Z[omega] (units mu_6, ramified prime t over 3, inert 2, split p = 1 mod 3), instead of Z[i] (units mu_4, ramified 1+i over 2, inert 3, split p = 1 mod 4) [INFERRED]. The numbers N(t^n - c), c in mu_6, are the Eisenstein-Mersenne norms of OEIS A066408; I verified the first terms (n = 2, 5, 7, 11, 17, 19) and the Aurifeuillian pair (see Q4) [COMPUTED].

7. **Exploratory computation (not a theorem).** Analogue of the project's Theorem K(b): test whether log p lies in the Q-span of log 3 and log N(t^n - c) (n <= 54, c in mu_6). Primes below 100 that pass: 2, 3, 5, 7, 11, 13, 19, 31, 37, 41, 43, 61, 73. Failing (n <= 54): 17, 23, 29, 47, 53, 67, 79, 97. Not appearing at all up to n = 54: 59, 71, 83, 89 (inconclusive: their index is large) [COMPUTED]. Restricting to real generators 3^m +- 1 gives only 2, 3, 5, 7, 11, 13, 41, 61, 73. So the Eisenstein (sqrt(3)-twisted) structure adds 19, 31, 37, 43 in this heuristic test, with 19 and 37 being the Aurifeuillian pair of 3^9+1 = 28*19*37. The implication (b) => (a) (each log N(t^n - c) is a series value) looks routine [INFERRED, not proved here]; the converse needs Baker's theorem as in Part III.

8. **pi*sqrt(3) is the base-3 "pi", and it is easy.** It is a degree-1 base-9 series: pi*sqrt(3)/6 = (1/3) P(1, 9, 4, (3, 0, -1, 0)), the Gregory series at 1/sqrt(3) (Bailey's general formula 92 at b = 3) [READ formula, COMPUTED check to 30 digits]. Compendium formula 69 for pi*sqrt(3) in base 3^6 is a longer period-12 version [READ + COMPUTED]. A rational-coefficient ternary series giving pi itself (not times sqrt(3)) would need Q(sqrt(3))-coefficients; whether any rational-coefficient ternary series equals pi is the open question your method would settle [INFERRED].

## Details per question

### Q1. Known ternary degree-1 formulas

Bailey's compendium (version dated April 8, 2023), section 9 "Ternary (base-3) formulas", pp. 24-25 [READ, text and rendered pages]. Notation P(s, b, n, A) as in the compendium.

| No. | Constant | Formula (restated) | Credit given there |
|---|---|---|---|
| 67 | log 2 | (2/3) P(1, 9, 2, (1, 0)) | appeared in ref. [16] |
| 68 | sqrt(3) arctan(sqrt(3)/7) | (1/6) P(1, 27, 3, (3, -1, 0)) | ref. [16] |
| 69 | pi*sqrt(3) | (1/9) P(1, 3^6, 12, (81, -54, 0, -9, 0, -12, -3, -2, 0, -1, 0, 0)) | Broadhurst |
| 70 | log 3 | (1/9) P(1, 9, 2, (9, 1)) | Povolotsky, simplified by Oliver Lafont |
| 71 | log 3 | (1/3^6) P(1, 3^6, 6, (729, 81, 81, 9, 9, 1)) | |
| 72 | log 5 | (4/27) P(1, 3^4, 4, (9, 3, 1, 0)) | Oliver Lafont |
| 73 | log 7 | (1/3^5) P(1, 3^6, 6, (405, 81, 72, 9, 5, 0)) | Oliver Lafont |
| 74 | log 11 | (1/(2*3^9)) P(1, 3^10, 10, (85293, 10935, 9477, 1215, 648, 135, 117, 15, 13, 0)) | Oliver Lafont |
| 75 | log 13 | (1/3^5) P(1, 3^6, 6, (567, 81, 36, 9, 7, 0)) | Oliver Lafont |
| 76-78 | pi^2, log^2 3, pi*sqrt(3) log 3 (degree 2) | base 3^6, n = 12 | Broadhurst |
| 79-83 | degree 3, 4, 5 constants (zeta(3), Cl_4(pi/3), zeta(5) combinations) | base 3^6 or 3^2, -27 | Adegoke (79-83); 82 first found by Broadhurst |

I verified 67, 68, 70, 69, 72 numerically to about 30 digits [COMPUTED]. Other base facts from the same document:

- Section 2 (p. 6): "BBP formulas in non-binary bases for the logarithms of certain integers and rational numbers" exist; example is the base-ten formula 84, log(9/10) = -(1/10) P(1, 10, 1, (1)) [READ].
- Section 3 (p. 8): the same remark for arctangents of rationals "by employing appropriate variants" of the binary formulas [READ].
- Section 10 (p. 26), other specific bases: formula 85, log(3/2) in base 25, and 86, sqrt(5) log(phi) in base 5 (both credited to Oliver Lafont); 87-88 base 5^5; 89 base 10^10. Section 11 (pp. 26-28): general-base families 90-110, among them (92) sqrt(b) arctan(1/sqrt(b)) = (1/b) P(1, b^2, 4, (b, 0, -1, 0)), (101)-(103) logs of (b +- 1)/b and sqrt(b) log((sqrt(b)+1)/(sqrt(b)-1)) = 2P(1, b, 2, (1, 0)). These give the generic "twisted" series for any b [READ].
- Introduction (pp. 2-3): pi^2 has both a base-2 formula (29) and a base-3 formula (76); Lagarias' work suggests constants with formulas in two or more bases are special [READ].
- Section 2 (p. 6): states the list of primes with binary log formulas (9) is "certainly not complete" and that it is unknown whether all primes have this property [READ].

Other sources:

- OEIS A165132 (Lafont, Oct 2009): primes 2, 3, 5, 7, 11, 13, with log formulas in P-notation as above; companion sequences A154920 (denominators, ternary log 3) and A164985 (denominators, ternary log 5) [READ via JSON API for A165132; names of the other two via search]. No criterion, no statement of completeness.
- Adegoke, arXiv:1603.04974 (published Notes Number Theory Discrete Math. 17(1), 2011, 4-21): ternary formulas of degree 1 for ln 2, ln 3 and one more constant, ternary zero relations; degrees 2 to 5; it says only relatively few ternary formulas are known [READ abstract page and table of contents and introduction; formulas not read in detail].
- Adegoke-Oliver Lafont-Layeni, arXiv:1603.07395: binary formulas for pi*sqrt(3), pi*sqrt(3) log 2, sqrt(3) Cl_2(pi/3) in bases 2^(12p); log of an infinite set of primes; arctan of an infinite set of rationals [READ abstract]. Adegoke's "Symbolic routes ... any degree in arbitrary bases" (2011) [READ via OpenAlex abstract].
- Broadhurst, arXiv:math/9803067 (1998): the hexadecimal paper; its abstract points to a companion paper hep-th/9803091, "Massive 3-loop Feynman diagrams reducible to SC* primitives of algebras of the sixth root of unity" (Eur. Phys. J. C 8 (1999) 311-333), whose abstract introduces a base-3 set SC*(3) built from sixth roots of unity [READ abstracts]. That is the historical origin of the ternary formulas and the closest existing appearance of the Eisenstein structure; I did not read the bodies.
- Kristensen-Mathiasen, arXiv:2208.07696 (J. Number Theory 2022): "geometric" proof that arg(1 + r e^(i theta)) is a degree-1 series in base 1/r^... for theta a rational multiple of pi (Theorem 1), software for BBP-type formulas, a new formula for 3*pi, and formulas for pi in the irrational Pisot bases golden ratio and 1 + sqrt(3) [READ]. Their remark: BBP-type formulas in non-integer bases look largely unexplored, and extracting digits from them is open. Relevant to base 3 only as a method (real part gives log|1 + r e^(i theta)|, so logs too).
- Barsky-Munoz-Perez-Marco, "On the genesis of BBP formulas", Acta Arith. 198 (2021): general generation method, explains null formulas; abstract only [READ].
- Berrizbeitia-Iskra, "Gaussian Mersenne and Eisenstein Mersenne primes", Math. Comp. 2010: primality tests via biquadratic and cubic reciprocity; no BBP content [READ via abstract].
- Chamberland 2003 (J. Integer Sequences 6, Article 03.3.7): binary only. It treats Re log of m(1+i)/2... giving log of Gaussian-Mersenne primes and "generalized Gaussian-Mersenne" numbers, and section 3 connects to Aurifeuillian identities; it notes it is still unknown whether log 23 has a binary formula, and refers to BBG for related questions [READ, text]. Nothing on base 3.
- Zhang: I could not identify a relevant paper by a "Zhang" on this topic (OpenAlex search "BBP-type formula digit extraction Zhang" returned unrelated or non-matching items) [READ].

### Q2. Exact open questions and negative results

Negative result (BBG, Canad. J. Math. 56 (2004) 897-925) [READ full text via the publisher PDF]:

- Definition 1 (p. 903): for 2 <= b not a proper power, a b-ary Machin-type BBP arctangent formula for a constant is a Z- or Q-linear combination of the generators arctan(-b^(-m)) = arg(1 - i b^(-m)) = b^(-3m) P(1, b^(4m), 4, [-b^(2m), 0, 1, 0]), m >= 1; for b = 2 additionally the "Aurifeuillian" generators arctan(1/(1 - 2^m)). Definition 3 (p. 904) gives the logarithmic generators ln(1 - b^(-m)) (and, for b = 2, ln|1 - (1+i)2^(-m)|).
- Theorem 7 (p. 918): for b > 2 not a proper power, no Q-linear b-ary Machin-type BBP arctangent formula for pi exists. Proof: Bang's (Zsigmondy's) theorem gives a primitive prime factor p of b^(4M) - 1 that is 1 mod 4 and splits in Z[i], and a p-adic valuation argument finishes. No Baker.
- Theorems 1 and 2 (pp. 908-909): exclusion criteria for arctan(y/x) in terms of a prime p = 1 mod 4 with ord_p(x^2+y^2) odd (Thm 1, Z-linear) or with nonzero Gaussian valuation difference when 4 does not divide ord_b(p) (Thm 2a). Examples (pp. 908-909): no 3-ary Q-linear Machin-type formula for arctan(2/3) (p = 13, ord_3(13) = 3) and none for arctan(1/4) (via 17 and 193, both with ord_3 = 16, Thm 2b); binary exclusions for arctan(3/8) and arctan(5/8) and non-Aurifeuillian exclusions for 2/7, 4/9, 5/9, leaving arctan(2/7), 4/9, 5/9 "in limbo". [READ]
- Theorem 4 and Example 4 (pp. 914, 916): no non-Aurifeuillian binary formula for ln 23, ln 89; and when Bang's exceptional case does not occur (M_b = 0) there is no b-ary Machin-type formula for ln b (so none for ln 10 in base 10); they say it seems unlikely any ln n has one but they failed to prove it. For b = 3, Bang's exception b = 2^N - 1 with N = 2 does occur (M_3 = 2), so log 3 itself is reachable, consistent with compendium formula 70 [READ + INFERRED].
- Not excluded by BBG: any series outside the class above, including (a) generators with half-integer powers (the sqrt(b) twist: formulas 92-103 of the compendium), (b) complex bases, (c) all other periodic coefficient patterns (period n, any j), (d) degree > 1, (e) combinations involving several bases. BBG themselves note (item 3 of their problem list) that the original 1996 BBP formula for pi does not appear to be a Q-linear combination of Machin-type generators, and ask for a simple derivation of it from one [READ].

Open problems listed by BBG (Appendix D, pp. 923-925; I give the ones touching bases other than 2):

- Item 4: if infinitely many primes p = 1 (mod 4) with 4 not dividing ord_b(p) exist, Theorem 2 yields infinitely many bases b with no b-ary Machin-type arctangent formula for a given arctangent. Does their existence follow from Chebotarev's density theorem or another known result? [READ]
- Item 7: Zsigmondy's theorem is known over number fields with effective bounds; this should give an effective Zsigmondy over Q[i] and hence an exclusion criterion for Machin-type arctangent formulas analogous to Theorem 6. [READ]
- Item 9: allow sums of b^(-k) p(k)/q(k) with b in Z[i], p, q in Z[i][k], to treat arctangents and logarithms together; might give cleaner or more general results. [READ]
- Item 10: the question stated in Key finding 2 (Q-linear combinations of L(1, b^m, n, j) with b, perhaps n, fixed; Knuth's Exercise 4.3.1.39 is cited for an explicit formula of L(1, b, n, j) as a sum of Log(1 - zeta^r b^(-1/n)) terms). [READ]
- Item 11: how to justify that Machin-type generators give all (or most) "interesting" arctangents and logarithms. [READ]

Zudilin, arXiv:2409.10097 (Sept 2024, 3 pages) [READ, full text]: section 2 says BBP-type formulas for pi are known for bases that are powers of 2 and calls it an open question whether such computation is possible for pi with other bases. It then uses identity (1), an arctan-type series at 1/(1 -+ 2i) (Salikhov; Zeilberger-Zudilin), calls it a base-5 BBP-type formula because the norm is 5, and section 3 shows the denominator (5^(2n+1)) breaks the modular-exponentiation trick; it asks whether other constants or formulas over quadratic or larger algebraic extensions fix this. Not a base-3 statement. I found no statement anywhere that "pi has no base-3 or base-10 BBP-type formula of degree 1" is proved; the statement that appears (Compendium p. 2, attributed to BBG) is an overreading [READ]. Wikipedia's BBP page says nothing on this and notes a 2022 decimal formula by Plouffe that effectively needs earlier digits [READ].

### Q3. Is a full classification in base 3 new?

- OpenAlex works citing BBG 2004 (22): general experimental-mathematics books, Machin-type pi formulas (Gaussian integers; golden ratio), Adegoke's binary polylog paper, Barsky et al., "Sagan numbers" and similar; none classifies degree-1 series in any base [READ titles].
- Citing Chamberland 2003 (13): includes Adegoke's binary and ternary polylog papers, Wagstaff's "The search for Aurifeuillian-like factorizations" (Integers 2012; a computer search through the Cunningham tables for new Aurifeuillian-type factorizations, abstract only), Sagan-type and a 2025 paper on ternary digits of powers of two (normality context). None applies Baker or classifies [READ titles/abstracts].
- Baker's theorem in this area: the only uses I know are the periodic-coefficient theorems of Baker-Birch-Wirsing and Adhikari-Saradha-Shorey-Tijdeman cited in the project note; no BBP paper found uses them [SNIPPET + project note].
- Searches on "Eisenstein" with "BBP", and "BBP and Baker or cyclotomic or Gaussian" on the arXiv API returned nothing relevant (the arXiv hits for BBP were random-matrix papers; 0 results for BBP with Eisenstein) [READ].
- Conclusion: I found no classification of base-3 series, no criterion for log p, no proof about pi in base 3. [INFERRED: claim only "not found in the places searched".]

### Q4. What would change in base 3

- Ring and twist: see Key findings 6. Bailey's formulas 67-75 are all instances of Log(1 - r/t) with t = sqrt(3) up to a twelfth root of unity (compendium n = 6, 12 and base 3^6 patterns) [INFERRED]. The natural field is Q(zeta_12) = Q(i, omega); the rationality condition on rho fixes the Galois action over Q(omega) [INFERRED], so the primes to study are Eisenstein primes (p = 1 mod 3 split, 2 inert, 3 ramified), and the role of "4 | ord(p)" in BBG's Theorem 2 would be played by a condition mod 6 or 3 [INFERRED].
- sqrt(3): the real arguments in the compendium (92) with b = 3 give pi*sqrt(3), not pi. In the Eisenstein setting pi would appear through arg(t^n - c) with c in mu_6; the rational multiples of pi are then those arg values that are rational multiples of pi, and BBG-style dimension counts would need the cyclotomic part for 12th roots of unity [INFERRED]. Bailey (68) arctan(sqrt(3)/7) is the argument of an Eisenstein integer of norm 13 (indeed t^2 + 1 = 1 - 3 omega has norm 13) [COMPUTED].
- Aurifeuillian structure in base 3: 3^(6k-3) + 1 = (3^(2k-1) + 1)(3^(2k-1) - 3^k + 1)(3^(2k-1) + 3^k + 1) (k = 1: 28 = 4*1*7; k = 2: 19684 = 28*19*37) [COMPUTED]. Equivalently, Phi_6(3^n) = (3^n - 3^((n+1)/2) + 1)(3^n + 3^((n+1)/2) + 1) for odd n, and each factor is N(t^n - c) for suitable c, giving the Eisenstein-Mersenne norm 3^n - (3/n) 3^((n+1)/2) + 1 with (3/n) the Legendre symbol when n is a prime above 3 [READ in OEIS A066408; COMPUTED: identity for n = 1, 5, 7, 11]. This is the base-3 analogue of L, M = 2^n -+ 2^((n+1)/2) + 1 (4^n + 1 factors) in the project's Theorem K. OEIS A239842 (Eisenstein-Mersenne cofactors EQ(n) = norm of ((1-omega)^n + 1)/(2-omega), terms 5, 11, 31, 37, 47, 53, 97, 163, 167, ...) says it explicitly uses the Aurifeuillian factorization of 3^(3k) + 1 for odd k, as T(k) = (3^k + 1) * EM(k) * EQ(k) * 7 [READ]. Wagstaff's paper and Chamberland section 3 are the general references for Aurifeuillian factors [READ abstract, text].
- OEIS A066408 (n such that N((1 - omega)^n - 1) is prime): 2, 5, 7, 11, 17, 19, 79, 163, 193, 239, 317, 353, 659, 709, 1049, 1103, 1759, 2029, 5153, 7541, 9049, 10453, 23743, 255361, 534827, 2237561, 2888387, 4043119; comments say the actual norms are "generalized unique primes" (Batalov 2014), the search went above 4.4 million (2023); A066413 lists the norms 7, 271, 2269, 176419, ...; A057429 is the Gaussian analogue [READ]. I verified for n < 60 that the n giving prime norm are exactly 2, 5, 7, 11, 17, 19 [COMPUTED]. The Prime Pages glossary page for "Generalized Unique prime" returned no match when I fetched it, so I could not read that definition.
- In the project's binary Theorem K the useful structure is: p must be alone (or with one prime dividing the index) in its primitive part. In base 3 the primitive part is Phi_n(3), or in the Eisenstein setting one of the Aurifeuillian pieces N(t^n - c). The exploratory table in Key finding 7 is what this predicts for primes below 100 [COMPUTED]. Per-prime data (order of 3 mod p in parentheses): in span: 19 (18), 31 (30), 37 (18), 43 (42) beyond the real ones; not: 17 (16: 3^8+1 = 2*17*193, both primitive), 23 (11), 29 (28), 47 (23), 53 (52), 67 (22), 79 (78), 97 (48) [COMPUTED, cutoff n <= 54 so negative entries with large order are not conclusive].

## Table: constant / base-3 formula known? / source / status of the converse

| Constant | Base-3 degree-1 formula known? | Source | Converse (is the rest excluded?) |
|---|---|---|---|
| pi*sqrt(3) | Yes (base 9, n = 4; also base 3^6, n = 12) | Bailey compendium (92), (69); Broadhurst | not applicable |
| pi (without sqrt(3)) | None found | none | Only excluded inside the Machin-type class (BBG Thm 7); general case open (BBG item 10) [READ] |
| log 2, log 3 | Yes | Compendium 67, 70, 71 | n/a |
| log 5, 7, 11, 13 | Yes | Oliver Lafont (compendium 72-75; OEIS A165132) | n/a |
| log 41, 61, 73 | Yes by elementary identities (3^4+1, 3^5+1, 3^6+1) | [COMPUTED/INFERRED]; not listed in any source I saw | n/a |
| log 19, 31, 37, 43 | Not found; plausible via Eisenstein-Mersenne norms | [COMPUTED test only] | no theorem |
| log 17, 23, 29, 47, 53, 67, 79, 97 | None found | n/a | Not excluded in the literature; heuristic test negative up to n = 54; BBG exclude ln b only when no Bang exception and only in the Machin-type class |
| arctan(sqrt(3)/7) (times sqrt(3)) | Yes | Compendium 68 | n/a |
| arctan(2/3), arctan(1/4) | Not in ternary Machin-type class | BBG Examples 2-3 (Theorems 1, 2) [READ] | Excluded only for 3-ary Machin-type (arctan(3^(-m)) combinations) |
| pi^2, zeta(3), zeta(5), Cl values (degrees 2-5) | Yes | Compendium 76-83 (Broadhurst, Adegoke) | not applicable here |
| arctan(2/7) (binary) | Unknown binary | BBG, compendium | Open in binary too |

## What could not be opened or verified

- Chamberland 2003 HTML pages (404 for one URL; I read the PDF); Adegoke 1603.04974 body formulas (read abstract, table of contents, introduction only); Broadhurst's two 1998 papers (abstract pages only); Wagstaff, Berrizbeitia-Iskra (abstract level via OpenAlex); Lafont's OEIS entry text beyond the JSON summary; Prime Pages definition of "generalized unique prime" (no match found).
- I could not identify the "Zhang" reference.
- The OpenAlex citation lists may lag (the Adegoke ternary paper shows 0 citers, while an earlier pass found it cited by other papers); title-level reading only. The absence of a ternary classification is therefore "not found", not "does not exist". An earlier-pass search for Baker's theorem in BBP papers likewise returns nothing, but Google Scholar and MathSciNet were not available.
- Key finding 7 is a heuristic computation: finite cutoff (n <= 54); factorization by sympy; the implication from "in span" to "has a formula" is not proven here; the converse (not in span implies no formula) needs Baker plus the cyclotomic analysis, not carried out. The "absent" primes (59, 71, 83, 89) are inconclusive.
- The Compendium's claim attribution ("Galway" or BBG) appears in different sources with different scope; I compared only the compendium and the BBG text.

## Search log

WebSearch (6 of 35 used):
1. Kristensen Mathiasen "BBP-type formulas" elementary approach 3pi irrational bases Pisot
2. Chamberland "Binary BBP-formulae for logarithms and generalized Gaussian-Mersenne primes" Journal of Integer Sequences
3. "ternary" BBP formula "log" prime 3-ary Machin-type formula Aurifeuillian base 3 Eisenstein integers digit extraction logarithm
4. is there a BBP-type formula for pi in base 3 open problem digit extraction "base 3" pi
5. BBP-type formulas "Baker's theorem" linear forms in logarithms nonexistence rational combinations arctangent bases
6. "Eisenstein" BBP-type formula base 3 "pi" sqrt(3) Gregory series arctan(1/sqrt 3) digit extraction ternary

Machine endpoints (no search cap used):
- OpenAlex: search by title for BBG (W2112047337, 22 citers), Chamberland (W2171765010, 13 citers), Wagstaff, Adegoke "Symbolic routes", Kristensen-Mathiasen (W4307054502); `cites:` filters for BBG, Chamberland, Adegoke ternary (W2963940819, 0), Barsky et al. (W2951905460, 6), Kristensen-Mathiasen (2); queries "BBP formula Baker theorem linear forms in logarithms classification", "ternary BBP digit extraction formula base 3", "BBP-type formula digit extraction Zhang", "Gaussian Mersenne and Eisenstein Mersenne primes".
- arXiv: abs pages 1603.04974, 1603.07395, 1603.04561, 1906.09629, 2409.10097, math/9803067, hep-th/9803091, 2508.03743, 2507.20428; arXiv API queries all:BBP AND all:Eisenstein (0 results); all:BBP with Gaussian/Baker/cyclotomic (random-matrix noise); abs:BBP AND abs:ternary (Adegoke only).
- OEIS JSON: A165132, A066408, A239842, A104885, search "Eisenstein Mersenne", search "ternary BBP".
- Other: MathWorld BBP-type formula page; Wikipedia BBP page; Prime Pages glossary (no match).
- Own computations: Python (sympy, mpmath) scripts in the session scratchpad (norm tests in Z[omega], Aurifeuillian identity, formula checks).

## Sources (opened)

- [Bailey, A Compendium of BBP-Type Formulas (April 2023)](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)
- [Borwein, Borwein, Galway, Finding and Excluding b-ary Machin-Type Individual Digit Formulae (Canad. J. Math. 2004)](https://doi.org/10.4153/CJM-2004-041-2) (publisher PDF read)
- [Zudilin, A BBP-style computation for pi in base 5, arXiv:2409.10097](https://arxiv.org/abs/2409.10097)
- [Kristensen and Mathiasen, BBP-type formulas, an elementary approach, arXiv:2208.07696](https://arxiv.org/abs/2208.07696)
- [Adegoke, ternary BBP-type formulas for polylogarithm constants, arXiv:1603.04974](https://arxiv.org/abs/1603.04974)
- [Adegoke, Oliver Lafont, Layeni, general binary bases, arXiv:1603.07395](https://arxiv.org/abs/1603.07395)
- [Adegoke, new binary formula for sqrt(5) log phi, arXiv:1603.04561](https://arxiv.org/abs/1603.04561)
- [Barsky, Munoz, Perez-Marco, On the genesis of BBP formulas, arXiv:1906.09629](https://arxiv.org/abs/1906.09629)
- [Chamberland, Binary BBP-formulae for logarithms and generalized Gaussian-Mersenne primes (JIS 6, 03.3.7)](https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf)
- [Broadhurst, Polylogarithmic ladders, arXiv:math/9803067](https://arxiv.org/abs/math/9803067)
- [Broadhurst, Massive 3-loop Feynman diagrams ... sixth root of unity, arXiv:hep-th/9803091](https://arxiv.org/abs/hep-th/9803091)
- [Cloitre, pi^2 in the golden ratio base, arXiv:2508.03743](https://arxiv.org/abs/2508.03743)
- [Cloitre, remainder of the Madhava-Gregory-Leibniz series, arXiv:2507.20428](https://arxiv.org/abs/2507.20428)
- [OEIS A165132](https://oeis.org/A165132), [A066408](https://oeis.org/A066408), [A239842](https://oeis.org/A239842), [A104885](https://oeis.org/A104885)
- [MathWorld, BBP-type formula](https://mathworld.wolfram.com/BBP-TypeFormula.html)
- [Wikipedia, Bailey-Borwein-Plouffe formula](https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula)
- [OpenAlex API (citation lists and abstracts)](https://api.openalex.org/works)
