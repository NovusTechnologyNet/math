# Pi and primes: concrete open or under-explored questions (survey, 2026-11-22)

Conventions. [READ] = seen in fetched content (page text, API output, or a PDF I converted with pdftotext). [SNIPPET] = only seen in a WebSearch result snippet. "From memory, unverified" = my own background knowledge, not checked this session. "Analysis" = my own reasoning, not a sourced claim. Years are given for records. No quote exceeds 15 words.

Tool use: 5 of 5 WebSearch calls used. About 84 WebFetch calls (listed at the end, including failures and one no-op).

Caveat on dates: many 2026 items below (OpenAI preprint, arXiv IDs 26xx.xxxxx) were reported by the fetch tool's summaries of pages dated after my own knowledge. I did not independently confirm them. A couple of arXiv IDs look odd (for example 2609.37459 has an unusually large serial number), so treat items marked "(2026, tool-reported)" as needing a direct check before anyone cites them.

---

## Summary (10 lines)

1. The method (relations among 1 - r/(1+i) in Z[i], plus Baker) is the same toolkit as Borwein-Borwein-Galway 2004 (BBG, Canad. J. Math. 56), who used p-adic orders on Z[i] and Bang/Zsigmondy but not Baker. [READ]
2. BBG's Appendix D lists 11 research problems; several are exactly what your method can do (zero-relation counts, Aurifeuillian exclusions, effective Zsigmondy in Z[i], Gaussian-integer bases). [READ] This is the single best map of open work.
3. BBG Theorem 7: for b > 2 not a proper power, pi has no Q-linear b-ary Machin-type BBP arctangent formula. [READ] So base 3, 5, 10 are closed inside that class; outside it, existence is open.
4. Zudilin 2024 (3 pages, "partly a joke") does digit extraction of pi in base 5 using the Gaussian integer 1-2i of norm 5, and says whether other bases work is open. [READ] A Gaussian-base BBP classification is a natural new target.
5. Machin-type: two-term is closed (Stormer, exactly four, 1895); three-term is finite modulo combinations of those four (Yamada, linear forms in three logs, arXiv 2018, v6 2025). [READ] Full explicit enumeration of three-term and finiteness for n >= 4 are open.
6. Records moved recently: Craig-Wood (arXiv 2508.08307, rev. 2026) reports a 6-term relation with Lehmer measure 1.3291 beating Wetherfield's 2004 values; Wikipedia still lists 1.51244 (Hwang 1997). [READ]
7. Irrationality measures are in flux: classic table has pi 7.10320 (Zeilberger-Zudilin 2020), but 2026 items claim mu(pi)=2 (OpenAI preprint, unverified, partial Lean) and mu(log r)=2 (Liu-Jiang-Zhang). [READ, tool-reported] Experimenting here is no longer a good use of a hobbyist's time.
8. Formal verification is where one person plus an AI can plausibly be "first": Lean has pi(10^5)=9592 and Goldbach to 2*10^5 (Lean 3, Mehta); nothing like 10^9; PNT+ has Mertens done and an open "odd Goldbach for small n" subproject (Tao, Feb 2026). [READ]
9. Normality, Hypothesis A, Sun's series, Wieferich, prime gaps, and Goldbach are marked hard or hopeless below; only the Stoneham-type normality results are provable and already done (Bailey-Crandall 2002). [READ]
10. Top picks: Gaussian-base BBP classification; BBG zero-relation count and exclusion tables; full three-term Machin list; Lean formalization of Stormer/Zsigmondy; contributing to PNT+ explicit estimates.

---

## A. Machin-type arctangent formulas for pi

Known.
- Machin 1706: pi/4 = 4 arctan(1/5) - arctan(1/239). [READ, Craig-Wood]
- Stormer 1895 proved the four two-term formulas (Machin, Euler/Hutton/Hermann types) are all of them; 1896 gave a necessary and sufficient criterion for given x_i to admit a relation and 102 three-term formulas. [READ, Yamada intro] Wikipedia agrees "exactly four" for two terms. [READ]
- Stormer's criterion in Z[i]: a relation among arctan(1/x_i) exists iff the numbers x_i + i have multiplicative relations modulo real numbers, i.e. a statement about factorization of x + i. [READ, Yamada; also BBG section 2 on the "group of slopes" Q(i)^x / Q^x]
- So for a fixed finite set of x_i the full rational linear relation space is computable by linear algebra on valuation vectors (v_p(x+i) at Gaussian primes above p = 1 mod 4, plus the (1+i) exponent mod 8 which pins down the rational multiple of pi). [READ BBG, Craig-Wood section 2.2; the "computable" phrasing is my analysis]
- Three terms: Yamada proved only finitely many nondegenerate three-term formulas exist (not coming from combinations of the four two-term ones) and gives explicit upper bounds on the variables, answering Stormer's question in the negative. [READ] Tool: linear forms in three logarithms and Ramanujan-Nagell type equations (keywords in the paper). Revised to v6 March 2025 with corrections; depends on Yamada arXiv:1906.00419 (lower bound for the argument of an algebraic power). [READ]
- Records (Lehmer measure lambda, smaller is better), from Craig-Wood 2025/2026 [READ]: 2-term Machin (1.8511); 3-term Gauss (1863) 1.7866; 4-term Stormer (1896) 1.5860; 5-term Nimbran (2009) 1.6121 beaten by the new 1.4572; 6-term Hwang Chien-Lih (1997) 1.5124, Wetherfield (2004) 1.3562, new 1.3291 (stated as lowest overall known, excluding formulas with millions of digits); 7-term Wetherfield (2004) 1.3408; 9-term Wetherfield (2009) 1.4140. Wikipedia still gives lambda 1.51244 (Hwang 1997) as smallest. [READ]
- Kanada 2002 used two Stormer formulas for 1.24 trillion digits; Chudnovsky is now used for records (current 314 trillion digits, 23 Nov 2025, O'Brien-Jain-Beeler). [READ] So Lehmer measure is of historical/curiosity value only.
- Gasull-Luca-Varona 2023 (arXiv 2302.00154): classify all two-term formulas with 2-integer arguments b/2^a, give a method producing N-term formulas, show two-term formulas (non-unit numerators) with Lehmer measure arbitrarily small, and fix an oversight about golden-section arctangents. [READ] Farhi (arXiv 2601.10300, Jan 2026) refines two-term formulas with continued fractions. [READ, API summary]
- Calcut, "Gaussian integers and arctangent identities for pi", Amer. Math. Monthly 116 (2009). [READ only as a citation in Gasull et al.]; Todd 1949, Wetherfield 1996, Tweddle 1991, Lehmer 1938 are cited there too. Arndt's role: from memory, unverified (pi-computation books, Arndt-Haenel); not checked.

Open.
- Complete explicit list of three-term formulas (Yamada's bounds are finite but, from the abstract alone, not checked to be small enough to enumerate; I did not read the size of the bounds). Stormer found 102 in 1896. [READ for 102]
- Finiteness for each n >= 4: Craig-Wood poses it as a question (4.3). [READ] Baker with n logs gives finiteness only if the number of logs stays bounded, so this is hard.
- Better search methods (his Q4.2: prime-group selection for PSLQ). [READ]

Does the method apply? Directly yes: Yamada's three-term work and Craig-Wood's filters are the same Z[i] valuation framework. Baker's theorem is what Yamada-type finiteness proofs use. Feasibility for a hobbyist: enumeration of three-term formulas = medium to hard; n >= 4 = hard.

---

## B. BBP-type formulas in other bases

Known.
- BBP formula (1995/1996), base 16, digit extraction of pi. [READ] Original BBP/Bailey notes it computes hexadecimal (hence binary) digits, not decimal. [READ Wikipedia]
- BBG 2004 [READ, full paper text]: "Machin-type BBP formula" class: pi = sum a_m arctan(-b^-m), a_m in Q (b > 2, b not a proper power; for b = 2 add terms arctan(1/(1-2^m))). Results: Theorem 1/2 exclusion criteria via a prime p = 1 mod 4 with ord_p odd or with order of b mod p not divisible by 4; Example: arctan(2/3) has no ternary Q-linear formula (p = 13); Theorem 7: pi has no Q-linear b-ary Machin-type BBP formula for b > 2 not a proper power; for b = 2 formulas exist. Binary arctan(2/7), (4/9), (5/9) were "in limbo" then excluded for non-Aurifeuillian by Theorem 2(b). They state that when there is no Machin-type BBP formula "no BBP formula of any form is known" for that constant. [READ]
- BBG Appendix D, research problems (verbatim summary, all [READ]): (1) 3+i = 2+(1+i) = 4-(1-i) gives two distinct formulas for arctan(1/3): trivial zero relation? (2) count Q-independent binary Machin-type zero relations, get upper bounds; (3) the original BBP formula (63) does not appear to be a Machin-type combination; derive it from one?; (4) are there infinitely many primes p = 1 mod 4 with 4 not dividing ord, and does Chebotarev give it?; (5) use Jacobi-symbol characters as extra exclusion bits; (6) combine the approach with PSLQ; (7) Zsigmondy in Q(i) with effective exceptional cases (Schinzel 1974, Bilu-Hanrot-Voutier 2001) gives an exclusion criterion analogous to Theorem 6; (8) Aurifeuillian generators in binary log formulas; (9) allow Gaussian-integer bases b and p, q in Z[i][k]; (10) determine whether pi is a combination of L(1, b^m, n, j) with n varying, which needs Q[zeta_n, b^(1/n)]; (11) why do the minimal generators give "all interesting" arctans and logs?
- Kristensen-Mathiasen 2022 (arXiv 2208.07696): LLL-based search, Sage code; new BBP-type formula for sqrt(3) pi; formula for pi in the Pisot base 1+sqrt(3) with integer coefficients; they note the golden-ratio base gives an unexplained abundance of null (zero) formulas and that their search probably misses formulas in base (3+sqrt5)/2. [READ] They state non-integer-base digit expansions (beta-expansions) as the natural setting for digit extraction.
- Cloitre 2025 (arXiv 2508.03743): proof of a BBP-type formula for pi^2 in the golden ratio base (found empirically 2004), via a geometric identity linking phi and fifth roots of unity, plus a Machin-like formula for zeta(3). [READ abstract]
- Zudilin 2024 (arXiv 2409.10097, 3 pp., "partly a joke"): digit extraction of pi in base 5 starting at position d, using 1-2i (norm 5). Method: fractional part of 5^d * xi with xi = 8 * sum (1/(2n+1)) (1/(1-2i))^(2n+1); reduce modulo m, where 2n+1 = 5^k m; condition on digit position; tail bound ~5^(1/2-2r). He calls it an open question whether such computations are possible in other bases and whether better formulas exist over quadratic or higher extensions. [READ] I did not find a base-10 version; WebSearch snippet mentions a 2022 Plouffe decimal-digit formula whose details I did not verify. [SNIPPET]
- Adegoke 2010-2016 (arXiv 1603.04974 and others): ternary and general-base BBP-type formulas for polylogarithm constants (not pi). [READ API summaries] Broadhurst's hexadecimal Catalan formula quoted in BBG. [READ] Euler credited with BBP-type formulas, 2023 observation. [READ Wikipedia]
- Barsky-Munoz-Perez-Marco 2021 (Acta Arith. 198; arXiv 1906.09629): a procedure producing infinitely many BBP and BBP-like formulas for pi and log 2, explains null formulas. [READ]
- Pi in base 3: I found no ternary BBP-type formula for pi and no proof of nonexistence outside the Machin-type class. [SNIPPET: Wikipedia-derived statement that BBG shows no degree-1 BBP formula for pi unless the base is a power of 2 (called "Galway 2004"), higher-degree cases open]. Treat that wording as unverified.
- Catalan's constant, 2020-2026 progress: only Broadhurst (hex, older) and general polylog papers (Olaikhan 2025, arXiv 2507.04205) found. [READ summaries]

Open.
- Any BBP-type formula for pi (with polynomial denominators of degree >= 2 or non-Machin generators) in a base not a power of 2: open. Complex or Pisot bases: open and under-explored. [READ Zudilin, K-M]
- BBG Appendix D items above.

Method applicability: direct for Gaussian bases and Machin-type classes (this is your framework). Baker enters because linear independence over Q-bar of logs of algebraic numbers turns the multiplicative relations in Z[i] into complete answers. For non-Machin generators (degree >= 2 denominators) the method as described does not apply.

---

## C. Digit extraction and normality

Known.
- Bailey-Crandall (2002/2003, "Random generators and normal numbers", read via PDF) [READ]: prove b-normality of sum 1/(c^n b^(c^n)) for coprime b, c > 1 (generalized Stoneham), Korobov class, and an uncountable explicit class; the googol-th binary bit of alpha_{2,3} is 0. Wikipedia: Stoneham 1973 needed c an odd prime and b a primitive root of c^2. [READ]
- Hypothesis A (Bailey-Crandall) [READ]: if the perturbation r_n = p(n)/q(n) is a non-singular rational function with deg q > deg p >= 0, then x_n = (b x_{n-1} + r_n) mod 1 is equidistributed or has a finite attractor. They say it is unknown whether this is true, and that normality of many constants (log 2, pi via BBP) would follow. Conditional result: on Hypothesis A, log 2 and related constants are 2-normal. [READ]
- BBG intro [READ]: the dynamical map x_n = (2 x_{n-1} + 1/n) mod 1 equidistributed would make log 2 binary normal.
- Pi is widely believed normal; no proof, and it is not even known that every digit string occurs. No irrational algebraic number is proven normal. [READ Wikipedia]
- Lagarias's dynamical work: my arXiv API query returned zero results, so I did not read it. From memory, unverified: Lagarias, "On the normality of arithmetical constants" (Experimental Math 2001).

Open (exactly stated).
1. Hypothesis A. 2. Is log 2 normal in base 2? 3. Is pi normal in base 16? Equivalent: equidistribution of {16^n pi} (standard; from memory). All hard; no known partial results short of the explicit Stoneham-type classes.

Applicability: none to normality itself. The method only classifies which constants have BBP formulas (the hypothesis side of the conditional statements).

---

## D. Irrationality and transcendence around pi

Known (classic table from Wikipedia "Irrationality measure", [READ]; each with the cited source):
- pi: 7.10320 (Zeilberger-Zudilin 2020, arXiv 1912.06345; refines Salikhov 2008 value ~7.606308). Their proof is a human-checkable variant of Salikhov's method found by a Maple package. [READ]
- pi^2: 5.09541 (Zudilin 2014). log 2: 3.57455 (Nesterenko 2010). log 3: 5.11620 (source titled "Symmetrized polynomials..."; authorship and year not read). zeta(3): 5.51389. pi/sqrt(3): 4.60105 (Androsenko 2015, Polyanskii 2018). [READ]
- 2026 claims (all tool-reported, none independently verified by me):
  - OpenAI, "The irrationality exponent of pi is 2", 24 Sep 2026, listed on Wikipedia as unverified [READ]; a citing paper (G. Chudnovsky, arXiv 2610.28079, Oct 2026) says there is a public Lean scope statement for the eventual approximation inequality (not the Flint Hills consequence) and that the bound is "eventual" and ineffective. [READ, and SNIPPET]
  - Liu-Jiang-Zhang, arXiv 2610.10192 (7 Oct 2026, v3 5 Nov): mu(log r) = 2 for every positive rational r != 1. [READ abstract]
  - arXiv 2610.27799 "New Directions in Irrationality": mu(zeta(2)) < 4.62675, mu(zeta(3)) < 5.4197, linear independence of 1, zeta(3), zeta(4). [READ abstract]
  - Bai, arXiv 2608.19782: mu(arctan(1/2)) <= 8.585166. [READ API summary]
  - Giraudin, arXiv 2609.37459 (suspicious ID, internally inconsistent summary): claims Bai's point is optimal in the SZZ family. [READ API summary, low confidence]
  - Several unverified/withdrawn amateur claims (Carella 2019 and 2021 "mu(pi)=2", Mantzakouras-Lopez Zapata withdrawn 2.5 bound). [READ]
  - OpenAI released 722 AI-written manuscripts on 6 Oct 2026; one survey says it compiled no Lean. [READ arXiv 2610.17090] So verification status is "mixed".
- Computer search is active: Zeilberger-Zudilin used a Maple package; Zudilin's older essay (arXiv math/0404523) surveys log 2, pi, log 3 methods. [READ] Ramanujan-Machine-style tools are for series/continued fractions (see E).
- Zeta(3) irrationality is formalized in Lean 4 (Liu-Zhang-Zhi, arXiv 2503.07625, 2025). [READ]
- Linear independence of pi and logs: Baker's theorem says logarithms of algebraic numbers linearly independent over Q are linearly independent over Q-bar; since i pi = log(-1), pi and log 2, log 3,... are covered. From memory, unverified (standard statement); nothing was fetched on it.

Open and concrete.
- Whether mu(pi) = 2 holds (now claimed). Flint Hills series convergence is linked to irrationality measure of pi (arXiv 2510.27041, 2603.09719 as summarized; the 2025 version claiming 2.5 was withdrawn). [READ summaries]
- Better measures for pi^2, log 3, pi/sqrt(3), zeta(3), zeta(2), arctan values. All research-level.

Applicability: Baker gives only lower bounds for linear forms; irrationality measure for pi is a different machine. Hobbyist feasibility: low, given 2026 developments.

---

## E. Series and continued fractions for pi

Known.
- Ramanujan-Sato levels: levels 1-4 are Ramanujan's, level 1 family by Chudnovsky 1989, level 2 by Bailey-Borwein-Borwein 1989, level 5 Chan-Cooper 2012, level 6 partly proven (Sato, Chan-Chan-Liu, Chan-Verrill, Chan-Tanigawa-Yang-Zudilin); the complement-based level 6 and level 10 formulas "apparently do not yet have a rigorous proof"; no pi formula known with j7B; closed forms for the last three level 10 sequences unknown. [READ Wikipedia]
- Guillera: 1/pi^2 formulas; WZ-method proofs (arXiv 1104.1994 proves identities linked to 1/pi and 1/pi^2 series; 1604.00193 re-proves Borwein algorithms). Almkvist transformed Guillera's formulas (arXiv 0911.4849). [READ] Which individual Guillera 1/pi^2 series are still unproven: not established by what I read.
- Zhi-Wei Sun's conjectured series: my arXiv queries returned zero relevant hits and Wikipedia does not mention Sun. [READ negative] From memory, unverified: Sun posted hundreds of conjectural pi series; many have been proved by others, many not.
- Ramanujan Machine (Raayoni et al., arXiv 1907.00205, Nature 2021) [READ]: numerically found continued-fraction conjectures. Proof progress: Dougherty-Bliss-Zeilberger 2020 (arXiv 2004.00090); Brier-Naccache-Yifrach-Stav 2022 (2211.01058, an algebraic observation proving many at once); Yamamoto 2024 (2403.09729: 38 conjectures proven by solving a second-order difference equation, 31 generalized); C. Wang 2026 (2601.08461 for -pi/4; 2602.03027 for 8/pi^2; 2601.11892 family for arctan(p/q)); Shvets 2026 (2604.06239, conjecture "Z2"). [READ API summaries] Naccache-Yifrach-Stav (2210.15669) generate Catalan-constant relations they do not claim proven. [READ] ESMA algorithm (2212.09470), Raz et al. 2025 mining pi formulas from 455,050 arXiv papers (2502.17533). [READ]

Open: unproved Ramanujan-Machine entries (check the project's catalog; I did not fetch it); unproved level 6/10 complement series; unproved Sun and Guillera cases (unknown count).

Applicability: not the Gaussian-Baker method (these are modular/hypergeometric or recurrence arguments). The Ramanujan Machine conjectures are the most AI-friendly: each has a recurrence-solving proof template (Yamamoto).

---

## F. Primes in the BBP world and nearby

Known.
- Chamberland 2003 (J. Integer Seq. 6, article 03.3.7) [READ full text]: binary BBP formulas for log p for all Gaussian-Mersenne primes and for "generalized Gaussian-Mersenne primes" (m such that the numerator of exp(2 Re log(m (1+i)/2)) is prime); list checked for m < 3000 starting 2, 3, 4, 5, 7, 9, 10, 11, 12, 14, ...; connection to Aurifeuillian factorizations; notes Pomerance showed 23 cannot be written in the form (1) but "it is still unknown whether log 23 has a binary BBP-formula" as of 2003. [READ] (Your work settles log 23 within your class F.)
- Barsky-Munoz-Perez-Marco [READ]: 2 and 2^N-1 generate a multiplicative subgroup of Q; for k in it there are binary BBP formulas for log k; "the first prime that it is not in this subgroup is k = 23": 2^11 - 1 = 23*89 and 23, 89 always appear together (order of 2 mod 23 is 11; 2^N+1 never divisible by 23).
- OEIS A104885: primes with known binary BBP logs: 2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73, 109, ..., 312709 (46 terms shown); comment: unknown whether finite or infinite; most found by PSLQ. [READ] Related: A182300/A057429 Gaussian-Mersenne primes (search to a(n) < 5,000,000 complete), A088962/A207040 generalized Gaussian-Mersenne, A124112 only proved prime up to exponent 12583. [READ]
- BBG Theorem 3-6 [READ]: Bang's theorem (1886) as exclusion tool, Aurifeuillian generators in binary, link to Cunningham project (b in {2,3,5,6,7,10,11,12}). Zsigmondy: a^n - b^n has a primitive prime divisor except n=1 (a-b=1), n=2 (a+b power of 2), and 2^6 - 1; a^n + b^n except 2^3+1. [READ Wikipedia] Bilu-Hanrot-Voutier 2001: Lucas/Lehmer sequences, indices within 1..30. [READ] The Wikipedia page does not cover Gaussian integers; BBG says the number-field generalization exists (Schinzel 1974, BHV 2001). [READ BBG]
- Primitive divisor multiplicities: Riasat (arXiv 2611.20650, 16 Nov 2026): under the abc conjecture, most Lucas indices have a primitive divisor with multiplicity one; links to Wall-Sun-Sun. [READ API summary]
- Wieferich primes: only 1093 and 3511 known; searches to > 2^64 (PrimeGrid 2020-2022, ended Dec 2022); Dorais-Klyve 2011 gave > 6.7*10^15; infinitely many Wieferich primes conjectured with ~log log x growth, unproven; Silverman 1988: abc implies infinitely many non-Wieferich. [READ] 2026 items: Siegel, "An Asymptotic for Non-Wieferich Numbers" (2610.28685); Laniewski on radical defects and Wieferich (2609.00039); Lenny Jones on Wieferich and monogenic trinomials (2605.13460). [READ API summaries]
- Aurifeuillian factorization: table for bases 2..24 (for example 2^(4k+2)+1, 3^(6k+3)+1, 5^(10k+5)-1, 6^(12k+6)+1, 7^(14k+7)+1, 10^(20k+10)+1). [READ Wikipedia, with garbled entries]
- Cunningham Project: bases 2,3,5,6,7,10,11,12; exponent limits 1500 (base 2), 900 (3), 600 (5), 550 (6), 500 (7), 450 (10), 400 (11), 400 (12), doubled for Aurifeuillian ranges; last printed edition 2002. [READ]
- Mersenne primes: 52 known; largest 2^136279841 - 1 (Oct 2024, Durant, GIMPS). [READ]

Open and concrete.
- Characterize (or extend by computation) primes p whose log has a binary BBP formula in the full class (powers of 2 with Gaussian/Aurifeuillian generators) beyond your < 100 classification; table of "first excluded prime" per base b (3, 5, 6, 7, 10, 11, 12) following the Pomerance/23 pattern.
- Finite or infinite (A104885). Hard: tied to primality of cyclotomic values Phi_d(2).
- Gaussian analogue: which Gaussian primes lie in the group generated by 2^m - (1+i) and relatives (BBG D8/D9 generalization).
- Wieferich/Wall-Sun-Sun: famous hard.

Applicability: direct and strongest here. The relevant step is solving linear systems over Z on valuation vectors of Phi_d(2) (from Cunningham-style factorizations) and invoking Baker for independence.

---

## G. Prime-number computation and formal verification

Records (with year).
- Goldbach (even) verified to 4*10^18 by Oliveira e Silva, Herzog, Pardi (search to 2013, published 2014); 4*10^17 double-checked. [READ Wikipedia]
- Ternary Goldbach proven by Helfgott (2013 submission). [READ]
- pi(10^29) = 1,520,698,109,714,272,166,094,258,063 (Walisch, 2022); pi(10^28) Baugh 2020; pi(10^27) 2015. [READ]
- Largest known maximal prime gap 1854 after 101412319996363309069 (Smith/Kehrig, 85th maximal gap); highest merit 42.5192 (Vojvoda, 2026). [READ]
- Riemann zeros: verified to height about 3.0001753328*10^12 (Platt-Trudgian 2021). The article also says "first 12 trillion nontrivial zeros" citing a label I could not confirm. [READ, with doubt]
- Twin primes: 808,675,888,577,436 pairs below 10^18 (Oliveira e Silva tables, 2008, cited by Wikipedia); largest known twin pair 2996863034895 * 2^1290000 +- 1 (2016); H <= 246 unconditional. [READ]
- Pi digits record 314 trillion, 23 Nov 2025. [READ]

Formal verification status.
- Lean 4 / Mathlib: Mehta verified in Lean 3 pi(10^5) = 9592 and Goldbach up to 2*10^5 (no sorry); Carneiro-Morrison posted a Lean 4 sieve-correctness proof in 2024; no formally verified Goldbach bound above that was reported in the thread. [READ, Zulip "Checking the Goldbach conjecture"] Timings: Goldbach to 10^9 in ~101 s in an unverified Lean 4 program (Lovett). [READ]
- PNT+ (Kontorovich-Tao): goals are PNT with classical error term and PNT in arithmetic progressions; stretch Chebotarev. Mertens' theorems (7.1.1-7.1.8) all marked done in the blueprint; two proofs have unresolved cross-references; upstreaming to Mathlib not complete. [READ] Explicit-estimates work (Tao, Jan 2026): tasks 3a (lcm(1..n) not highly abundant for n > 89693^2, uses Dusart) and 3b (Erdos 392, uses Rosser-Schoenfeld type bounds), with open items such as 3a.8 (Dusart) and 3b.4, 3b.8-3b.11; Tao assumed Dusart-type bounds "as a black box" in Nov 2025. [READ + SNIPPET] The IEANTN material is moving to teorth/IEANTN. [READ]
- "Odd Goldbach for small n" subproject (Tao, Feb 2026): bootstrap from even Goldbach to 4*10^18 (target 4*10^30), Ramare-Saouter used 1.13256*10^22; ladder of Proth primes would need ~10^12 primes; Helfgott suggests ~10^27 may suffice; Pratt certificates to ~50 digits (Mehta) and Pocklington to 70 digits; exploratory. [READ]
- Zeta(3) irrationality and PNT with an error term were formalized (arXiv 2503.07625). [READ]
- Primality certificates at scale in Lean: only the Pratt/Pocklington work above; Mersenne record verified by Lucas-Lehmer outside proof assistants (the article does not say). [READ]

What is wanted but not done (analysis, based on the above): verified sieve values of pi(x) beyond 10^5; a Lean statement-and-proof of explicit Chebyshev/Rosser-Schoenfeld/Dusart bounds (needs zero-free regions and verified zero heights, which is heavy); formal verification of any prime-gap record.

Hard/hopeless here: Goldbach, twin primes, Cramer, Legendre, Wieferich-type questions, Riemann hypothesis.

---

## H. Pi-and-primes crossovers

Known.
- Probability two random integers are coprime = 6/pi^2 (Cesaro 1881; Hardy-Wright Thm 332; Nymann 1972 for k integers 1/zeta(k)). [READ Wikipedia] Formal status in Lean/Mathlib: from memory, unverified (Mathlib has Basel; not sure about the coprime density).
- OEIS A086785: primes among numerators of pi's continued fraction convergents: six known terms; for m <= 10000 the only both-prime numerator/denominator is 833719/265381; finite-or-infinite not stated. [READ] A120843 (initial digit of the 10^n-th prime) is "almost certainly correct but unproven". [READ]
- Buffon's needle: nothing open on the page; Lazzarini 1901 3408 tosses gave 355/113 and is regarded as a fraud or non-experiment. [READ]
- Stoneham/Korobov normal numbers connect to BBP (C above).
- Sondow 2007 (arXiv 0710.1862) uses an irrationality measure of 6/pi^2 to quantify Euclid-type bounds on the next prime; Burt et al. (0709.2184) use mu(zeta(2)) for explicit lower bounds for pi(x). [READ API summaries]
- Pi-primes (primes among the decimal digits of pi): heuristic only. Without normality of pi nothing is provable (analysis).

Open: infinitely many prime numerators among pi's convergents (needs structure of the CF of pi, hopeless); "proof rather than computation" items: normality-driven statements. Nothing found in Euler-product territory that is both open and concrete beyond formalization.

---

## Ranked list of the 15 most promising concrete questions

Legend for "G+B applies": Y = Gaussian-integer valuation method with Baker applies directly; P = partly; N = no.

1. **Gaussian-integer bases for BBP digit extraction.**
   Statement: for which beta in Z[i] (starting with 1-2i, norm 5; also 2+i, 1+2i, 3+2i...) does pi (or log, arctan constants) have a BBP-type formula in base beta giving digit extraction in base N(beta)? Classify Machin-type formulas with generators 1 - i/beta^m.
   Source: Zudilin 2024 (arXiv 2409.10097), BBG D(9) and D(10). Status: open; Zudilin says whether this works for other bases is open [READ].
   Feasibility: medium-high. Same ring, same exclusion machinery (BBG Theorem 1/2 adapted to beta-adic orders). Answer = a classification theorem (list of beta admitting a formula; proof of exclusion for the rest) plus a verified digit-extraction check. G+B: Y.

2. **Count and bound binary Machin-type BBP zero relations (BBG D(2)); decide whether the two formulas for arctan(1/3) are "interesting" (D(1)).**
   Status: open as posed in 2004. Feasibility: high given your multiplicative-relation lattice (the relation module is a finitely generated Z-module; rank and a basis are computable per truncation; Baker gives the exact lattice). An answer = rank formula (dimension of the zero-relation space per generator bound M) plus a proof it is exactly that. G+B: Y.

3. **"First excluded prime" per base b, and extend your binary classification beyond 100.**
   Statement: for b in {2,3,5,6,7,10,11,12}, find all primes p < N with a Machin-type b-ary BBP formula for log p, and the first one that fails (generalizing Pomerance's p = 23 for b = 2; Barsky et al.).
   Source: BBG Theorems 4, 6; Barsky et al.; OEIS A104885 (list to 312709, comment "unknown whether finite"). Feasibility: high, needs Cunningham factor tables. Answer = new OEIS-style sequences with proofs of exclusion for each missing prime. G+B: Y.

4. **Exclusion criteria with Aurifeuillian generators for b > 2 (BBG D(8) beyond binary).**
   Statement: for b with Aurifeuillian factorizations (3, 5, 6, 7, 10, 11, 12, ...), do extra log generators from Phi_n(b^(2k+1)) change which primes have formulas? Source: BBG D(8), Wikipedia table [READ]. Feasibility: medium. G+B: Y.

5. **Complete the list of three-term Machin-type formulas.**
   Statement: enumerate all nondegenerate three-term relations (those not coming from the four two-term ones). Source: Stormer 1896 (102 found), Yamada (finite with explicit bounds). Status: finiteness proved; completeness of list unknown to me. Feasibility: medium to hard (bounds from three-log linear forms are astronomically large, then reduction with LLL/Gaussian smooth searches). Answer = a rigorously complete list. G+B: Y (same Z[i] equations; Baker is the finiteness tool).

6. **Is the number of n-term Machin-type formulas finite for every n >= 4?** (Craig-Wood Q4.3; Stormer's Z[i] framework.) Status: open; Baker with 4+ logs plus an unbounded prime support is hard. Feasibility: low. G+B: P.

7. **Lean 4: formalize Stormer's two-term theorem and machine-check the record Machin-like formulas.**
   Statement: exactly four two-term formulas (Machin, Euler/Hutton/Hermann types); verify Craig-Wood's and Wetherfield's relations by Gaussian-integer multiplication (Gasull et al. note direct multiplication suffices). Source: Stormer 1895; Yamada intro; Craig-Wood data on Zenodo. Status: no formalization found in my searches (not checked in Mathlib). Feasibility: high; two-term proof is elementary. G+B: P (the finiteness/classification step uses Z[i] but not Baker for n = 2).

8. **Lean 4: Zsigmondy/Bang theorem for a^n - b^n and a Z[i] version.**
   Statement: primitive prime divisors exist except the listed cases; then Bilu-Hanrot-Voutier-style effective version over Q(i) (BBG D(7)). Status: from memory, unverified whether Mathlib has it; I did not search. Feasibility: medium for the integer case, hard for number fields. G+B: Y (it is the exclusion engine).

9. **Contribute to PNT+ explicit estimates or the "odd Goldbach for small n" subproject.**
   Open items found: Dusart-based task 3a.8, 3b.4, 3b.8-3b.11, Mertens cross-reference cleanup, certificate/ladder pieces for odd Goldbach. Source: PNT+ repo, Zulip threads Jan-Feb 2026. Feasibility: medium; it is contributor-run, tasks are claimed on GitHub, and AI-assisted proofs are explicitly part of the workflow [READ]. Answer = merged Lean PRs. G+B: N.

10. **First formally verified pi(x) beyond 10^5 (Lean 4 verified sieve).**
   Status: Lean 3 pi(10^5)=9592 (Mehta); Lean 4 sieve proof exists (Carneiro-Morrison 2024); unverified Lean programs reach Goldbach to 10^9. Source: Zulip thread. Feasibility: medium for 10^6 to 10^9 (kernel vs compiled evaluation is the issue), then Legendre/Meissel-Lehmer correctness for larger x is hard. Answer = a Lean theorem pi(10^9) = 50847534 (value from memory, unverified) with a trust statement. G+B: N.

11. **Prove unproved Ramanujan Machine continued fractions (recurrence method).**
   Source: Yamamoto 2024 (38 proven), Wang 2026, Shvets 2026; catalog is the Ramanujan Machine site (not fetched). Feasibility: medium, AI-friendly, each is a small research note. G+B: N.

12. **Lean: density of coprime pairs = 6/pi^2.**
   Source: Cesaro 1881; Hardy-Wright. Status: unknown whether in Mathlib (from memory, unverified). Feasibility: medium-high (needs Basel, which Mathlib has per my memory, unverified; plus Mobius counting). A fine "formal pi meets primes" result. G+B: N.

13. **Are there infinitely many primes with a binary BBP log formula (A104885)?**
   Status: open per OEIS. Equivalent to structure of Phi_d(2) lattice; likely needs primes of special form. Feasibility: low (conditional heuristics possible). G+B: P.

14. **Hypothesis A / normality of log 2 and pi in BBP bases.**
   Status: open, famous hard; only Stoneham-type explicit normals are proven. Feasibility: very low. G+B: N.

15. **mu(pi) = 2, Flint Hills series, third Wieferich prime, Riemann hypothesis, Goldbach.**
   Status: hard or claimed; mu(pi)=2 claimed unverified 2026. A feasible modest project is checking what the public Lean scope of the OpenAI pi statement actually states (is the statement faithful?). Source: Wikipedia, arXiv 2610.28079, 2610.17090. Feasibility: low to medium for the audit, nil for the rest. G+B: N.

---

## Pages fetched (84 WebFetch calls; failures marked)

Wikipedia: Machin-like formula; Bailey-Borwein-Plouffe formula; Normal number; Irrationality measure (twice); Prime-counting function; Goldbach's conjecture; Prime gap; Wieferich prime; Ramanujan-Sato series; Zsigmondy's theorem; Aurifeuillean factorization; Cunningham Project; Riemann hypothesis; Stoneham number; Coprime integers; Chudnovsky algorithm; Chronology of computation of pi; Buffon's needle problem; Twin prime; Mersenne prime; "Pi (disambiguation)" (no-op, unrelated, ignore).
arXiv API queries: Machin-type; BBP formula; irrationality measure pi; Gaussian Mersenne / BBP logarithm; Ramanujan Machine; Guillera pi; explicit PNT Lean (0 results); Lagarias BBP (0); BBP normal digit extraction (0); Machin arctangent Gaussian integers; Lean formalization Chebyshev (0); Riemann zeros verification Platt (0); Sun Ramanujan-type (0); Ramanujan-type conjectured proof (0); Machin-like (sorted by date); Wieferich/Wall-Sun-Sun; Goldbach verification formal.
arXiv abs/pdf/html: 1811.09273 (abs and pdf); 2302.00154 (abs and pdf); 2208.07696 (abs and pdf); 2508.03743; 1906.09629; 1906.00419; 1912.06345; 2508.08307 (pdf); math/0407031 (wrong paper); 2610.28079; 2503.07625; 2604.23784; 2610.27799; 2610.10192; 2610.17090; 2409.10097 (abs and html).
OEIS: A104885; Machin/arctan search; pi-primes-convergents search; Gaussian Mersenne search; binary BBP logarithm search; Wieferich/Aurifeuillian/Machin search (empty).
Other: MathWorld BBP formula; MathWorld Machin's formula; MathWorld MachinLikeFormulas (404); Bailey bbp-formulas.pdf (twice, unreadable binary); Bailey bbp-alg.pdf (twice, unreadable); Bailey-Crandall bcnormal.pdf (read by pdftotext afterwards); carma.newcastle.edu.au BBG PDF (DNS failure); GitHub AlexKontorovich/PrimeNumberTheoremAnd; PNT+ blueprint explicit chapter; Lean Zulip: odd Goldbach subproject; Checking Goldbach; Explicit estimates outstanding tasks; Tertiary estimate projects; JSTOR (Calcut; error page); stackexchange API x3 (blocked by the tool, so no MathOverflow/Math.SE results).
Local PDF/text extractions: Borwein-Borwein-Galway, Chamberland, Barsky-Munoz-Perez-Marco, Craig-Wood, Yamada, Gasull-Luca-Varona, Kristensen-Mathiasen, Bailey-Crandall were read from text I extracted with pdftotext from PDFs the fetch tool saved, plus pre-existing text extractions in the scratchpad whose provenance I did not independently verify; BBG, Chamberland and Barsky were read mainly from those scratchpad copies. Treat quotes from those three as "READ (local copy)".

WebSearch (5 of 5 used): (1) irrationality exponent of pi 2026 verification; (2) Lean explicit bounds PrimeNumberTheoremAnd; (3) formal verification of Goldbach / prime gaps; (4) BBP in base 3/5/10 and Machin-type excluded; (5) "The irrationality exponent of pi is 2" preprint and Lean.

## Sources

- Borwein, Borwein, Galway, "Finding and Excluding b-ary Machin-Type Individual Digit Formulae", Canad. J. Math. 56 (2004) 897-925 (doi 10.4153/CJM-2004-041-2).
- Chamberland, "Binary BBP-Formulae for Logarithms and Generalized Gaussian-Mersenne Primes", J. Integer Seq. 6 (2003), 03.3.7.
- Barsky, Munoz, Perez-Marco, "On the genesis of BBP formulas", arXiv:1906.09629; Acta Arith. 198 (2021).
- Kristensen, Mathiasen, arXiv:2208.07696. Zudilin, arXiv:2409.10097. Cloitre, arXiv:2508.03743.
- Yamada, arXiv:1811.09273 and 1906.00419. Gasull-Luca-Varona, arXiv:2302.00154. Craig-Wood, arXiv:2508.08307 (data: Zenodo 10.5281/zenodo.16758216; code: github.com/ncw/find_arctan_formulae). Farhi, arXiv:2601.10300.
- Bailey, Crandall, "Random Generators and Normal Numbers" (2003).
- Zeilberger, Zudilin, arXiv:1912.06345. Liu-Jiang-Zhang, arXiv:2610.10192. Chudnovsky, arXiv:2610.28079. arXiv:2610.27799, 2610.17090, 2608.19782 (all 2026, tool-reported). OpenAI, "The irrationality exponent of pi is 2" (24 Sep 2026; not fetched directly).
- Liu-Zhang-Zhi, arXiv:2503.07625. PrimeNumberTheoremAnd (github.com/AlexKontorovich/PrimeNumberTheoremAnd); Lean Zulip archive threads cited above.
- OEIS A104885, A057429, A088962, A207040, A182300, A124112, A086785, A120843.
- Wikipedia articles listed above; MathWorld pages (BBP formula, Machin's formula).
