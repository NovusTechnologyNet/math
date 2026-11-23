# W2-Q17: Chamberland (2003), "Binary BBP-formulae for logarithms and generalized Gaussian-Mersenne primes" -- complete list of claims

Paper: J. Integer Sequences 6 (2003), Article 03.3.7, 10 pp. Received 15 Jul 2003, revised 24 Oct 2003, published 25 Oct 2003. MSC 11Y05; 11A41, 11B99, 11T22, 11Y60. "Concerned with A057429".
Source read: the LaTeX source `chamberland60.tex` (875 lines, 27 KB) served at cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/ (the directory is open; the .pdf and .html live there too under the name chamberland60). The whole text was read. The source has no page numbers, so locations are given by section (Sec. 1 Introduction, Sec. 2 Cyclotomic polynomials and generalized GM primes, Sec. 3 Aurifeuillian factorizations). Note: the paper is only about 8 pages of text; there is NO proof anywhere that any table prime has a formula -- the table is "modest calculations with Maple" (Sec. 2).
Marking: [READ] = on the paper's own source or an OEIS/other page I read; [SNIPPET] = only in an API record or search result; [INFERRED] = my own conclusion; [COMPUTED] = my own exact computation (Python, own code, nothing taken from the web).

## 1. Summary

1. The paper contains 1 theorem (Thm 3.1, a clean statement and proof), 0 other numbered lemmas, 3 examples of Aurifeuillian identities, one definition (generalized Gaussian-Mersenne), two tables of primes (a 90-prime table of "primes whose log has a binary BBP formula", and a list of 108 values of m), 41 listed products of two primes, and about 6 explicit formulas used as evidence. [READ]
2. The entry 38737 is NOT justified anywhere in the paper: it appears only in the bare list (Sec. 2), is not underlined (so not from Bailey's list) and has no formula, factorization or product attached. [READ]
3. [COMPUTED] 38737 is almost certainly a mistake: 2 has order 72 modulo 38737; 2^24-2^12+1 = Phi_72(2) = 433 x 38737; in EVERY relation of the paper's types that I generated (about 2100 generators, Phi_m(2^k), norms of Phi_m((+-1+i)/2^n), Phi_m((+-1+sqrt(-3))/2^n), and norms of 2^(nj) - w^j) in which 38737 occurs, the prime 433 occurs too, and 433 is not in the table. Rank test over a large prime field: every table prime that my generators reach lies in the span except 38737; the pair {433, 38737} lies in the span, 433 alone and 38737 alone do not. So the likely truth: the product 433 x 38737 belongs in the "products of two primes" list, and 38737 was misfiled as a single prime. (Bounded computation; not a proof that no larger relation exists -- see Sec. 4.)
4. OEIS A104885 ("Primes whose logarithms are known to possess binary BBP formulas", Adamson, Mar 2005) contains 38737 and 433 is absent. Its 46 terms are the paper's table cut at 312709 [READ, compared by eye]; the record cites only Bailey-Borwein-Plouffe and Borwein-Bailey, not Chamberland. So the error propagated there [INFERRED: same list, no other source given].
5. All 41 printed two-prime products check out [COMPUTED: each e_p + e_q lies in the span of the generators]. The four formulas I tested numerically (14449, 331, 599479, Gaussian Mersenne case) are right. The paper's printed identity Re log(1 - ((1+sqrt3 i)/2) x) = log(1-x^3) - log(1-x) is WRONG as printed (correct: (1/2)[log(1+x^3) - log(1+x)]); harmless to the logic.
6. The list of 108 generalized Gaussian-Mersenne values m < 3000 is reproduced exactly by my computation (probable-prime test of the numerator for every m <= 3000: same 108 values, no missing, no extra). [COMPUTED]
7. Later literature: no correction or extension of the table found. Citations found: Adegoke 2016 (three arXiv papers), Adegoke-Lafont-Layeni; Borwein-Borwein-Galway 2004 cites the draft; OEIS A057429/A088962/A207040. Bailey's Compendium (Apr 2023 version) does not cite it and its list of primes is exactly the paper's 46 underlined primes.
8. Divisibility (Q5): every prime divisor of 2^p +- 2^((p+1)/2) + 1 (p odd prime) is 1 mod 4p, except the prime 5, which divides exactly one of the two factors. [INFERRED, short proof below; a one-line corollary of ord_q(2)=4p for q | 2^(2p)+1]. In print I found only the weaker "q = 1 mod p" (Ordowski comment in A182300).

## 2. What is known: numbered list of every claim in the paper

### Abstract and Section 1 (Introduction)
C1. Setting: constants C = sum p(k)/(q(k) b^k), p,q integer polynomials, deg p < deg q, p/q non-singular for k >= 0, b >= 2 (abstract) or b a positive integer (Sec.1). Claim: n-th base-b digit computable in (essentially) linear time without the earlier digits (attributed to BBP 1997). [READ] Verification: literature statement; not proved in the paper.
C2. Such constants are "conjectured to be either rational or normal to base b" (attributed to Bailey-Crandall, Experiment. Math. 10 (2001)). [READ] Stated as a conjecture.
C3. BBP's pi formula displayed (16^-k, 4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6)). [READ] Standard.
C4. Attribution: Bailey's Compendium (preprint 2000) "catalogued" BBP formulas. [READ]
C5. Definition used: Gaussian-Mersenne primes (Sloane A057429) are the primes p such that ((1+i)^p - 1)((1-i)^p - 1) is prime. [READ] (note: p is the exponent; the prime norm is called q below)
C6. Claim: log q has a BBP formula for every Gaussian-Mersenne prime q (norm), and for a "much broader" class of generalized GM primes. [READ] Proved in Sec. 2 (C16-C18).

### Section 2 (cyclotomic polynomials, table)
C7. log 2 = sum_{k>=1} 1/(k 2^k). [READ] Classical.
C8. BBP (1997) sought all integers m with log m having a binary BBP formula (base 2^l). [READ] Attribution.
C9. Bailey-Crandall: the set of constants with a binary BBP formula is a linear space; if C1 has base 2^l1 and C2 base 2^l2, C1 + C2 has base 2^lcm(l1,l2). [READ] Easy; attributed.
C10. log(2^n - 1) - n log 2 = -sum 1/(k 2^(kn)), so log(2^n - 1) and log(2^n + 1) have binary formulas, hence log of any integer of the form prod(2^a_i - 1)/prod(2^b_j - 1) (eq. big_frac). [READ] Elementary.
C11. BBP gave a list of primes of that form; Bailey extended it using Re log(1 +- (1+i)^k / 2^n) "suggested by R. Harley and J. Borwein". [READ] Attribution. Displayed derivation: log(1 - (1+i)/2^n) = -sum_{j>=0} 2^(-(8n-4)j) sum_{k=1..8} ((1+i)/2^n)^k/(8j+k). [READ] Correct (a degree-1 formula of base 2^(8n-4), N = 8). [INFERRED correct: (1+i)^8 = 16.]
C12. Cyclotomic facts: b^n - 1 = prod_{d|n} Phi_d(b); Phi_d(x) = prod_{k|d} (1 - x^(d/k))^mu(k). [READ] Standard.
C13. Attribution: BBP "state that" log Phi_m(2) has a binary BBP formula for all m >= 1. Extension: log Phi_m(2^k) for all integers k. [READ] Follows from C10 and C12 (all Phi_m(2) are products of factors 2^a - 1).
C14. Eq. root2_eq: Re log Phi_m((+-1+i)/2^n) = sum_{d|m} mu(d) Re log(1 - ((+-1+i)/2^n)^(m/d)); each term is a binary BBP formula (as in C11); the advantage "implicitly some cancellation may take place". [READ]
C15. Eq. root3_eq: the same with (+-1 + sqrt3 i)/2^n. [READ] Each term is a BBP series (|z|<1 and z^6 = real power of 2 times a sign; correct [INFERRED]).
C16. Example 1: Re log Phi_6((1+i)/16) = (1/2)[log 14449 - 14 log 2]; hence 14449 joins the list. [READ] [COMPUTED: checked numerically to 1e-16: both sides -0.0628400204228.] Verification needed: Phi_6(z) = 1 - z + z^2 evaluated at z = (1+i)/16; the norm |256 - 16(1+i) + 2i|^2... i.e. a one-line integer computation giving 14449 x 2^power. 14449 = 2^14 - 2^... (prime).
C17. Example 2: Re log Phi_5((1+sqrt3 i)/4) = (1/2)[log 331 - 8 log 2]; hence 331. [READ] [COMPUTED: checked numerically, both sides 0.12847046544875.]
C18. Claim: results of type root3_eq are again "linear combinations of earlier formulae" because "Re log(1 - ((1+sqrt3 i)/2) x) = log(1-x^3) - log(1-x)". [READ] WRONG AS PRINTED [COMPUTED]. Correct: 1 - e^(i pi/3) x has |.|^2 = 1 - x + x^2 = (1+x^3)/(1+x), so Re log = (1/2)[log(1+x^3) - log(1+x)]. Numerics at x = 0.37: true value -0.132699, printed formula 0.410055, corrected formula -0.132699. The conclusion (a linear combination of binary formulas) is still right.
C19. TABLE A (Sec. 2): "Modest calculations with Maple" give an augmentation of Bailey's list of primes whose log has a binary BBP formula; 90 primes, in increasing order; 46 underlined (given by Bailey) and 44 new. Full list in Sec. 3 of this report (Table A). [READ] No proof, no formula, no factorization for any entry in the paper; justification = "calculation".
C20. Products: "products of two primes, three primes, etc. were found to be on the list"; keeping track of products helps generate new single primes. Example: 2^11 - 1 = 23 x 89, so 23 x 89 is on the list; Re log Phi_6((1+sqrt3 i)/2^12) = (1/2)[log 7 + 2 log(23 x 89) + log 599479 - 44 log 2], which is how 599479 was obtained. [READ] [COMPUTED: numerically correct, -0.000244200307262 both sides; and 599479 lies in the span of my generators.] Verification needed: the integer N = |Phi_6 numerator|^2 factorization 7 x (23x89)^2 x 599479 x power of 2 (this is a short exact check; uses 2^11-1 = 23 x 89).
C21. TABLE B: 41 products of two primes "on the list" (explicit list, Sec. 3 of this report). [READ] Plus the commented-out (not printed) lines in the TeX source: 103 x 2143 x 1119(?), 173 x 101653 x 500177, 233 x 1103 x 2089, 431 x 9719 x 2099869, 881 x 3191 x 201961, 2351 x 4513 x 13264529, 6361 x 69431 x 20394401: seven triples commented out of the printed version. [READ] Note the "1119" in the first comment is not prime (1119 = 3 x 373) -- a typo in a comment only. [INFERRED: 1119 = 3 x 373] The commented triples are not claimed in the published text.
C22. Claim: "all the primes up to 101 are on the list, either alone or multiplied by one other prime." [READ] Checked against Tables A and B [INFERRED]: 23 (with 89), 47 (178481), 53 (157), 59 (3033169), 67 (20857), 71 (122921), 79 (121369), 83 (8831418697), 97 (673), 101 (8101); 89 via 23 x 89; the rest are in Table A. All consistent.
C23. Claim: every odd prime p is on the list alone or in a multiple product, since 2^(p-1) - 1 is on the list and p | 2^(p-1) - 1. [READ] Correct as logic of "log of a prime in a product" only: it shows p divides an integer whose log has a formula, NOT that log p has a formula; the sentence is about membership in "some multiple product of primes". [INFERRED: this is a statement about products, weak.]
C24. Attribution: Pomerance (in BBP 1997) showed 23 cannot be written in the form big_frac; "it is still unknown whether log 23 has a binary BBP-formula". Related questions treated in Borwein-Borwein-Galway (BBG). [READ] Stated as open in 2003. (Project result: log 23 has no formula in the class; see 00_RULES section 1. BBG 2004 proves log 23 and log 89 have no non-Aurifeuillian binary Machin-type formula [READ in BBG text].)
C25. Eq. GMP-form: the subclass Re log Phi_m((1+i)/2). For m = p = 4k+1 prime: Phi_p((1+i)/2) = 1 + i(1 - (-1/4)^k); hence Re log Phi_p((1+i)/2) = (1/2) log(2 x 16^k - 2(-4)^k + 1) - 2k log 2 = (1/2) log[((1+i)^p - 1)((1-i)^p - 1)/2^(4k)]. [READ] [COMPUTED: the closed form Phi_p = 1 + i(1-(-1/4)^k) checked for p = 5, 13, 17; and the chain of equalities is right since (1+i)^4 = -4.]
C26. "A similar calculation may be done for p = 4k-1", and "so if q is a Gaussian-Mersenne prime, then log q admits a binary BBP formula." [READ] No calculation shown for p = 4k-1. Correct [INFERRED: Phi_p(z) = (z^p - 1)/(z - 1) with z = (1+i)/2, z-1 = (-1+i)/2, a unit times a power of 2 inverse: same computation with (1+i)^(4k-1) = (-4)^(k-1)(-1)(...)(1-i)... no obstacle]. Also the converse gap: q here is the NORM; it is the norm (prime) whose log has the formula, not p.
C27. Definition D1 (generalized Gaussian-Mersenne primes): the question "for which positive integers m is the numerator of exp(2 Re log Phi_m((1+i)/2)) prime?" Those primes are the generalized GM primes; they include the regular GM primes (m = prime) and many composite m. [READ] The paper does not say what "numerator" is taken of: it is of the rational number |Phi_m((1+i)/2)|^2 in lowest terms [INFERRED; my computation of this reproduces the paper's list exactly].
C28. TABLE C: the m < 3000 for which the numerator is prime: 108 values (list in Sec. 3 below), regular GM (m prime) underlined: 2,3,5,7,11,19,29,47,73,79,113,151,157,163,167,239,241,283,353,367,379,457,997,1367 (24 values). [READ] [COMPUTED: reproduced exactly by a probable-prime test (gmpy2, 25 rounds) for every m <= 3000: no extra, no missing m. m = 2995 gives a prime of over 700 digits, as stated.] Verification of each entry = primality test of a huge numerator. Not proved prime in the paper (probable primes are what a computation gives; certified primality is open for the largest ones).
C29. Claim: "Some of the primes produced by (GMP) have been put on the previous list" (i.e. appear in Table A). [READ] Consistent: e.g. 5, 13, 29, 37, 41, 61, 109, 113, 397, 1321, 1429, 1613, 2113, 14449, 26317 all in Table A; OEIS A207040 lists the first 31 such primes.

### Section 3 (Aurifeuillian factorizations)
C30. Phi_5(x) = (x^2+3x+1)^2 - 5x(x+1)^2; with x = 5^(2k-1) this gives a factorization Phi_5(5^(2k-1)) = [5^(4k-2) + 3.5^(2k-1) + 1 -+ 5^k(5^(2k-1)+1)]. [READ] Correct as polynomial identity [INFERRED: (x^2+3x+1)^2 - 5x(x+1)^2 = x^4+x^3+x^2+x+1].
C31. Attribution: identities first noted by A. Aurifeuille and generalized by E. Lucas; references Brillhart et al. 1983 (Factorizations of b^n +- 1), Schinzel 1962, Stevenhagen 1987, Brent 1995. [READ]
C32. Bailey's identity: Re log(1 +- (1+i)/2^n) = (1/2 - n) log 2 + (1/2) log(2^(2n-1) +- 2^n + 1); so 2^(2n-1) +- 2^n + 1 join the list; multiplying them gives 2^(4n-2) + 1 = (2^(2n-1)+2^n+1)(2^(2n-1)-2^n+1): "explains why some calculations were redundant". [READ] Correct (|1 - (1+i)/2^n|^2 = 1 - 2^(1-n) + 2^(1-2n)). [INFERRED]
C33. THEOREM 3.1: for gcd(m,n) = 1 and max(m,n) > 2: Phi_{mn}(x) = prod_{j=1..phi(m)} Phi_n(x zeta_j) over primitive m-th roots of unity zeta_j. [READ] Proof given (degree, monic, root matching via Euclid). Proof reading: sound; the proof of leading coefficient uses prod zeta_j = 1 which holds for phi(m) even i.e. m > 2, and for m = 2 (prod = -1, phi(n)... ) fails for odd phi(n), which is why "max > 2" is needed -- the hypothesis is about right but note for m = 1,2 the statement is fine for m = 1 (trivial) and the exclusion is only needed for m = 2 with phi(n) odd, i.e. n = 1,2. [INFERRED] Acknowledged to A. Adelberg.
C34. Identities used: Phi_{2^k n}(x) = Phi_n(-x^(2^(k-1))) for n odd, and Phi_{pn}(x) = Phi_n(x^p) for p prime not dividing n. [READ] Standard (the second needs n coprime to p and Phi_n(x^p) = Phi_pn(x)Phi_n(x), so as printed it is WRONG unless one reads it for p | n: precisely, Phi_{pn}(x) = Phi_n(x^p) holds when p | n, and Phi_{pn}(x) = Phi_n(x^p)/Phi_n(x) when p does not divide n). [INFERRED from standard theory.] The error is in the text; the examples later use only the p | n case in effect (n even), so the examples stay correct (checked numerically below).
C35. Example 1 (m = 4, n odd): Phi_n(-x^2) = Phi_{4n}(x) = Phi_n(ix)Phi_n(-ix); and Phi_n(x^2) = Phi_n(x)Phi_n(-x). Attributed to Schinzel's formula (12). [READ] Correct for n odd [INFERRED].
C36. Example 2 (m = 8, n odd): Phi_{8n}(x) = product of four Phi_n(x zeta); with x -> sqrt2 x: Phi_n(-4x^4) = Phi_{4n}(2x^2) = [Phi_n(x(1+i)) Phi_n(x(1-i))][Phi_n(x(-1+i))Phi_n(x(-1-i))], each bracket an integer polynomial for real x. [READ] Correct [INFERRED].
  Subcases with x = 2^k: n=1: 2^(4k+2) + 1 = (2^(2k+1) + 2^(k+1) + 1)(2^(2k+1) - 2^(k+1) + 1). [READ] Correct.
  n=15: 2^(32k+16) + 2^(28k+14) - 2^(20k+10) - 2^(16k+8) - 2^(12k+6) + 2^(4k+2) + 1 = L.R with L,R a 17-term expression with +- signs on odd-index terms. [READ] [COMPUTED: identity verified exactly for k = 1..5, and left side equals Phi_15(-4 x^4) at x = 2^k.]
C37. Redundancy relation (x = 2^-k): Re log Phi_{4n}(1/2^(2k-1)) = 2[Re log Phi_n((1+i)/2^k) + Re log Phi_n((-1+i)/2^k)]; "so terms from (pow2) and (root2_eq) appear in some factorizations." [READ] Follows from C36 [INFERRED].
C38. Example 3 (m = 12, 2,3 not dividing n): Phi_{12n}(x) = prod of four Phi_n(x zeta) (zeta = (+-sqrt3 +- i)/2); with x -> 2 sqrt3 x: Phi_{6n}(12x^2) = [Phi_n(x(3 + sqrt3 i))Phi_n(x(3 - sqrt3 i))][Phi_n(x(-3 + sqrt3 i))Phi_n(x(-3 - sqrt3 i))]. [READ] Correct [INFERRED].
  n=1, x = 2^(k-1): 9.2^(4k) - 3.2^(2k) + 1 = (3.2^(2k) - 3.2^k + 1)(3.2^(2k) + 3.2^k + 1). [READ] Correct [INFERRED, direct expansion].
  n=5: a 9-term product identity for Phi_30(12x^2) with x = 2^(k-1): the left side printed as 2^(16k)3^8 + 2^(14k)3^7 - 2^(10k)3^5 - 2^(8k)3^4 - 2^(6k)3^3 + 2^(2k).3 + 1. [READ] The product is printed without a multiplication sign between the left side and the first factor ("... + 1 ( 2^(8k)... )") -- typographical omission of "=". [COMPUTED: identity verified exactly for k = 1..5 with that omission corrected.]
C39. Second redundancy (m = 12): Phi_{6n}(((1+sqrt3 i)/2) x^2) = Phi_n(((1+sqrt3 i)/2)x) Phi_n(-((1+sqrt3 i)/2)x) Phi_n(x) Phi_n(-x), hence with x = 1/2^(k-1) a relation among Re log Phi_{6n}((1+sqrt3 i)/2^(2k-1)), Re log Phi_n((+-1+sqrt3 i)/2^k) and log Phi_n(+-1/2^(k-1)). [READ] Plausible and consistent with Thm 3.1; not checked in full [INFERRED].
C40. Acknowledgements: Bailey, Borwein, Wagstaff; Adelberg for Thm 3.1. References: 8 items (Bailey Compendium 2000; BBP 1997; Bailey-Crandall 2001; BBG "submitted, CECM preprint 2003:195"; Brent 1995; Brillhart et al. 1983; Schinzel 1962; Stevenhagen 1987). [READ]

"It is unknown whether ..." statements in the paper: (i) whether log 23 has a binary BBP formula (C24). That is the only explicit one. The abstract/intro conjecture (C2) is attributed. The paper does NOT claim the table is complete, and does not say whether the prime list is finite (Bailey's Compendium says "certainly not complete ... unknown whether finite or infinite" [READ in Bailey 2023 text]).

## 3. Tables, entry by entry

### Table A (90 primes; U = underlined = in Bailey's list)
U: 2 3 5 7 11 13 17 19 29 31 37 41 43 61 73 109 113 127 151 241 257 337 397 683 1321 1613 2113 2731 5419 8191 43691 61681 87211 131071 174763 262657 524287 2796203 15790321 18837001 22366891 4278255361 4562284561 2932031007403 4363953127297 4432676798593 (46 primes; identical to the list (9) in Bailey's Compendium, Apr 2023 version [READ]).
New (44), with my status [COMPUTED unless noted]:
 331 (paper's example), 1429, 14449 (paper's example), 26317, 65537 (= Phi_32(2), trivial), 246241, 268501, 279073, 312709, 525313, 599479 (paper's example), 4327489, 7416361, 29247661, 47392381, 107367629, 536903681 (= Gaussian Mersenne norm, p = 29), 1326700741, 40388473189, 77158673929, 118750098349, 415878438361, 1133836730401, 3630105520141, 4981857697937, 108140989558681, 140737471578113 (= GM norm p = 47), 1041815865690181, 96076791871613611, 18446744069414584321 (= Phi_6(2^32)), 5302306226370307681801, 17059410504738323992180849, 84159375948762099254554456081
   -> status: IN the rational span of the generators (so a BBP formula exists by the paper's method): all 33 listed here.
 38737 -> NOT in span (see Sec. 4).
 10 large entries beyond my size bound (not reachable with generators of at most 104 bits, so untested, neither confirmed nor refuted): 2048568835297380486760231, 134304196845099262572814573351, 19177458387940268116349766612211, 304832756195865229284807891468769, 1339272539833668386958920468400193, 3652124453410972878264128353955921, 1772303994379887829769795077302561451, 6113142872404227834840443898241613032969, 1461503031127477825099979369543473122548042956801, 867988564747274927163124868127898657976489313137639569 (the last has 54 digits).
 All underlined entries and 2: in the span (2 trivial) [COMPUTED].
What a verification needs per entry (general recipe): an explicit parameter (m, n, sign/field) such that the integer |A|^2 (A = 2^(n.deg) Phi_m(w/2^n), w one of +-1 +- i, +-1 + sqrt(-3)) factors into the table prime, powers of 2, and primes whose logs already have formulas, OR a product of (2^a - 1)-type values; then one linear solve over Q. The paper gives only 3 witnesses (331, 14449, 599479). For the 10 large primes the factorization of a 40-100 digit cyclotomic value is needed: all probably follow from the Cunningham tables of Phi_m(2) and Aurifeuillian L, M factors (e.g. 18446744069414584321 = 2^64 - 2^32 + 1).

### Table B: 41 two-prime products (each [COMPUTED] to lie in the span; so the claim "on the list" is correct)
23x89, 47x178481, 53x157, 59x3033169, 67x20857, 71x122921, 79x121369, 83x8831418697, 97x673, 101x8101, 137x953, 139x168749965921, 149x184481113, 181x54001, 193x22253377, 197x19707683773, 229x457, 223x616318177, 251x4051, 277x30269, 281x86171, 283x165768537521, 313x1249, 353x2931542417, 571x160465489, 593x231769777, 601x1801, 631x23311, 641x6700417, 1013x1657, 1777x25781083, 3121x21841, 3761x7484047069, 5581x384773, 8681x49477, 10169x43249589, 13367x164511353, 32377x1212847, 92737x649657, 179951x3203431780337, 181549x12112549.
Remark: 433 x 38737 is NOT among them. 641 x 6700417 = 2^32+1 (trivial); 229x457, 601x1801, 3121x21841 etc. are the factorizations of Phi_m(2) / (2^a +- 1).

### Table C (generalized GM, m < 3000): 108 values, all reproduced [COMPUTED]
2,3,4,5,7,9,10,11,12,14,15,18,19,21,22,26,27,29,30,33,34,35,42,45,47,49,51,54,55,58,63,65,66,69,70,73,79,85,86,87,105,106,110,111,113,114,126,129,138,147,151,157,163,167,178,186,189,217,231,239,241,242,283,319,323,350,353,363,367,375,379,385,391,457,462,522,543,566,602,621,633,651,679,741,779,819,871,885,997,1062,1114,1126,1150,1226,1275,1317,1329,1367,1382,1434,1477,1710,1926,1970,2331,2422,2446,2995.
(The paper's table is the m for which the numerator is prime; the primes themselves are not listed except those reaching Table A.) Verification = primality of an integer with up to ~700 digits (m = 2995): done as probable prime.

## 4. The entry 38737, exactly

- Where: Sec. 2 list, 35th entry, between 26317 and 43691. Not underlined. No formula, no factorization, no mention in the text; the only examples given in the text are 14449, 331, 599479. [READ]
- Arithmetic [COMPUTED]: 38737 is prime; 38736 = 2^4 . 3^2 . 269; the multiplicative order of 2 mod 38737 is 72 (and also mod 433); 2^24 - 2^12 + 1 = 16773121 = 433 x 38737, and 433 is prime. 433 is not in Table A, B or in OEIS A104885.
- Hits (parameters (m,n,w) for the family Re log Phi_m(w/2^n), norm numerator divisible by 38737, m <= 72, n <= 8, w in {1+i, -1+i, 1+sqrt-3, -1+sqrt-3}): (4,7,sqrt-3), (8,4,sqrt-3), (9,5,sqrt-3), (12,7,sqrt-3), (16,5,i), (18,5,sqrt-3), (24,4,sqrt-3), (36,3,sqrt-3), (48,2,i), (72,2,sqrt-3) and a few more; for those I fully factored (bit length <= 110), the prime factors besides 2 are always: {433, 38737} or {17, 241, 433, 38737}. 17 and 241 have formulas; 433 does not appear alone anywhere.
- Rank test: with 2143 generators (Phi_m(2^k); 2^a +- 1; norms of 2^(nj) - w^j for the 4 values of w, n <= 12, nj <= 75) the span contains all reached table primes except 38737; it contains 433 + 38737 and does not contain 433 or 38737 alone.
- Reading: the table entry looks like the pair 433 x 38737 = Phi_72(2) that was misfiled as a single prime. This matches the project's finding that A104885's entry 38737 fails, and shows its source is the 2003 table (not Bailey's list, which never had it). [INFERRED]
- Caveat: bounded search. A rigorous refutation needs the Q(zeta_72)-ideal argument (the project's criterion for log y: every prime above 38737 and 433 enters only through units of fixed ratio), which I did not attempt here.
- Also: Bailey's Compendium list (9) has neither 38737 nor 433 [READ].

## 5. Later citations (who extended or corrected)

All access to OpenAlex, Semantic Scholar and the arXiv API returned HTTP 429 (rate-limited with long Retry-After) after the first queries, so a full forward-citation list could not be obtained; what was found:
- Borwein-Borwein-Galway, "Finding and excluding b-ary Machin-type individual digit formulae", Canad. J. Math. 56 (2004) 897-925: cites Chamberland's DRAFT (as "Binary BBP-formulas for logarithms, cyclotomic polynomials and Aurifeuillian identities, draft c. Dec 2001") and says it gives further discussion of cyclotomic polynomials and Aurifeuillian factorizations for finding BBP formulae. [READ] BBG prove log 23 and log 89 have no non-Aurifeuillian binary Machin-type formula [READ, Prop. near eq. (47) ff.]. They do not extend the table.
- Adegoke, arXiv 1603.04974 (ternary), 1603.05810 (binary), and Adegoke-Lafont-Layeni arXiv 1603.07395 (binary, general bases): each cites it as ref [5] [READ in the reference lists]. They use it only as background for binary formulas; no correction.
- Bailey, "A compendium of BBP-type formulas" (Apr 2023 version): text read; the name Chamberland does not occur, and the list (9) of primes equals Table A's underlined entries only [READ].
- OEIS: A057429, A088962 (author Chamberland, 28 Oct 2003), A207040 (Wesolowski, May 2012) link the paper [READ]. A104885 (Adamson 2005) copies the table without credit.
- Berrizbeitia-Iskra, "Gaussian Mersenne and Eisenstein Mersenne primes", Math. Comp. 79 (2010): its reference list (16 items, via Crossref) does not include Chamberland. [READ]
- Crossref: 4 citations recorded for Berrizbeitia-Iskra; 0 for most others; no record for Chamberland (no DOI). EuDML and zbMATH (Zbl 1073.11076) list no citers [READ].
- Nobody found who "extended or corrected" the table; "not found" after the above, weak evidence because of the rate limits. Also not found: any paper that tests whether log 433 or log 38737 has a binary formula.

## 6. Generalized Gaussian-Mersenne primes: definition and comparison with OEIS

- Paper's definition: C27. A057429 as the paper uses it = exponents p with prime norm N_p = ((1+i)^p - 1)((1-i)^p - 1) = 2^p - 2 cos(p pi/4) 2^(p/2) + 1 = 2^p -+ 2^((p+1)/2) + 1 (sign +: p = +-3 mod 8; sign -: p = +-1 mod 8).
- OEIS A057429 (R. G. Wilson v, Sep 2000): 41 terms, 2, 3, 5, 7, 11, 19, 29, 47, 73, 79, 113, 151, 157, 163, 167, 239, 241, 283, 353, 367, 379, 457, 997, 1367, 3041, ... 15317227; exhaustive below 5,000,000 (Batalov 2014); last term added June 2023. [READ] The paper's underlined m (24 values below 3000) agree with it; the next term is 3041 > 3000, consistent.
- A182300: the norms themselves (12 terms listed); comment by Ordowski (2019): norms are 2^p +- 2^((p+1)/2) + 1 and satisfy q = 1 mod p. [READ]
- A007670 (2^k - 2^((k+1)/2) + 1 prime) and A007671 (2^k + 2^((k+1)/2) + 1 prime): the two halves (sign) of the Aurifeuillian pair, Brillhart. [READ]
- A088962 ("Values of n that generate Generalized Gaussian-Mersenne primes", Chamberland, Oct 2003): data stop at 283 (59 terms); the paper has 108 terms up to 2995. So OEIS carries only the part of Table C up to 283: an extension of A088962 to 2995 (my 108 values, probable primes) is available. [READ for the data; the extension is [COMPUTED]]. Formula in A088962 and A207040 is the paper's expression; T. D. Noe's Mathematica program (2012) tests n <= 100.
- A207040 ("Generalized Gaussian-Mersenne primes", Wesolowski, May 2012): 31 terms: 5, 13, 29, 37, 41, 61, 109, 113, 397, 1321, 1429, 1613, 2113, 14449, 26317, 246241, 279073, 312709, 525313, 4327489, 7416361, 29247661, 47392381, 107367629, 536903681, 1326700741, 40388473189, 118750098349, 275415303169, 415878438361, 1759217765581 (computed with n up to 2^7; so ordered). Cross-check [INFERRED] with Table A: 77158673929 (Table A) is absent from A207040 and 275415303169, 1759217765581 (A207040) are absent from Table A (Table A is a table of primes with log formulas, not of numerators for m < 3000 only; 77158673929 may come from m larger than 128 or from a product, not tested).
- A104885: the prime list that comes from the paper plus 38737 (see Sec. 4).
- PrimePages (Caldwell, "Gaussian Mersenne", Prime Glossary; [READ]): states the Aurifeuillian identity 2^(4m-2) + 1 = (2^(2m-1) + 2^m + 1)(2^(2m-1) - 2^m + 1); no congruence conditions on the divisors; Spira 1961, McDaniel 1973/74, Hausmann-Shapiro 1976 for the origin. Wikipedia "Aurifeuillean factorization" mentions "536903681 is an example of a Gaussian Mersenne norm" [READ] and has no divisor congruences.

## 7. Divisibility of the norms 2^p +- 2^((p+1)/2) + 1

Claim [INFERRED; short proof]: let p be an odd prime and F_+ = 2^p + 2^((p+1)/2) + 1, F_- = 2^p - 2^((p+1)/2) + 1. Then F_+ F_- = 2^(2p) + 1 = Phi_4(2) Phi_{4p}(2) = 5 . Phi_{4p}(2). If q is an odd prime dividing 2^(2p) + 1 then the order of 2 mod q divides 4p but not 2p, so it is 4 or 4p. Order 4 forces q | 15 and q = 5; otherwise 4p | q - 1. Hence every prime divisor q of F_+ F_- is either 5 or satisfies q = 1 mod 4p (so q = 1 mod 8 and q > 4p). By lifting the exponent v_5(2^(2p) + 1) = 1 for p different from 5, so 5 divides exactly one of the two factors, once: it divides the factor that is NOT the Gaussian-Mersenne norm (for p = 7: norm 113 = 2^7 - 2^4 + 1, other factor 145 = 5 x 29; for p = 5: norm 41, other factor 25). [COMPUTED check of the two small cases by hand]. Therefore: all prime divisors of the Gaussian-Mersenne norm N_p are = 1 mod 4p. Cross-check via Gaussian integers (independent argument): if q | N_p with q = 1 mod 4, pi | q in Z[i], then (1+i) has order exactly p in (Z[i]/pi)^* = F_q^*, so p | q - 1; q = 3 mod 4 is impossible (it would force 2^p = 1 and 2^((p-1)/2) = +-1 mod q, hence 2 = 1). [INFERRED]
What is in print: "q = 1 mod p" for the norms (Ordowski, comment in A182300, 18 Apr 2019) [READ]; "primes dividing 2^(2p)+1 are 1 mod 4p" for p odd would be in Brillhart's 1962 paper "Concerning the number 2^(2p)+1, p prime" (Math. Comp. 16, 424-430; listed as a link in A007670; I did not read it -- [SNIPPET: title only]) and in Brillhart et al., Factorizations of b^n +- 1. Berrizbeitia-Iskra 2010 abstract says they "describe other properties of these norms that help in searching for large primes" [SNIPPET from Crossref/AMS, abstract only; AMS page returned 403] -- very probably includes q = 1 mod 4p [not confirmed]. Chamberland's own paper has no divisibility statement.
Consequence for this project [INFERRED]: for the log criterion, the prime ideals above N_p all have residue degree dividing p-1 and the relevant primes sit in Q(zeta_{4p}); this is the same structure as the Phi_{4p}(2) primitive divisors.

## 8. Open points (precise)

O1. Whether log 38737 (equivalently log 433) has a binary BBP formula: not settled by the paper; my bounded computation says it does not come from the paper's methods; a proof either way would use the project's criterion (log y: iff the ideal factorization of y in the relevant cyclotomic/Gaussian fields gives a vector in the span). Open as far as my search shows (not stated as open by any source).
O2. Whether log 23 has a binary BBP formula: stated open in the paper (C24); settled negatively by the project.
O3. Whether the set of primes with binary BBP formulas is finite: stated open in Bailey's Compendium [READ].
O4. Certified primality of the large numerators in Table C (m near 3000): not claimed in the paper; I only did probable-prime tests.
O5. Extension of A088962 (59 terms there vs 108 in the paper) and the table beyond m = 3000: possible (days of computing); A057429 shows the next regular GM exponent is 3041.

## 9. Leads for this project, ranked

1. Verify the whole Table A against the project's exact criterion (Theorem K: log y has a formula iff ...). Exact statement: for each of the 90 primes decide membership and list the minimal certificate (explicit (m, n, w) combination); the 10 large entries need a 40-100 digit factorization from the Cunningham tables or ECM. Size: days; our tools fit (Baker not needed; this is linear algebra over Z in the primes dividing a few thousand cyclotomic norms). Worth noticing: this documents the first known error in the standard list of primes with binary log formulas (38737, and OEIS A104885 inherits it); a short note or OEIS correction request.
2. Prove 38737 and 433 have no binary BBP formula (or find the missing relation). Statement: log 433 and log 38737 are not in the Q-span of binary-BBP-type logarithms. Size: days with the project's criterion (primes above 433, 38737 in Q(zeta_72)). Worth noticing: a clean counterexample to an OEIS entry; pairs with the Theorem K criterion already formalized.
3. Extend A088962 from 59 to 108 terms (my probable-prime computation up to m = 3000 agrees with the paper) and beyond (m up to 10000 would take hours; 24 cores): a straightforward computation that completes the OEIS record. Days or less.
4. Fix the stated errors in the paper in a short erratum-style note: the sqrt3 identity (C18), Phi_{pn}(x) = Phi_n(x^p) (C34), the missing "=" in the n = 5 identity, the non-prime "1119" in a commented line. Hours.
5. State and prove the divisibility fact of Sec. 7 for Gaussian-Mersenne norms in the Lean development (every prime divisor of N_p is 5 or 1 mod 4p), using the order argument already formalized for primitive divisors. Days. Useful as a lemma for the criterion for log of Gaussian-Mersenne type primes.

## 10. Overlap or conflict with the project results (00_RULES section 1)

- The paper's question on log 23 (C24) is answered by the project's result "log 23 has no formula in class F"; the paper states it as open, consistent.
- The project's criterion for logarithms vs the table: the paper's entry 38737 conflicts with the criterion if the project's tool decides log 38737 is not a formula value (project memory already records this finding: "OEIS A104885's entry 38737 fails, traced to Chamberland 2003"); this report adds the concrete reason (433 x 38737 = Phi_72(2)).
- Nothing in the paper conflicts with the classification statements for pi.

## 11. Notes on process

- Files in the shared scratchpad: I created the directory `...\scratchpad\ch` (the downloaded paper source and PDF) and scripts t.py (this OVERWROTE an existing scratchpad file named t.py -- I did not check it first), u.py, v.py, v2.py, v3.py, v4.py, w3.py, w4.py, w5.py, gm.py, chk.py plus gens*.pkl and gm3000.out. Nothing outside the scratchpad and this report was written. Nothing from the web was executed; only the paper's text and records were read, and my own Python code was run.
- Prompt-injection: none seen in any page.
- Pages read in full: the paper (TeX source), OEIS A057429, A088962, A207040, A104885, A182300, A007670, A007671, Crossref record of Berrizbeitia-Iskra, zbMATH and EuDML records, PrimePages Gaussian Mersenne, Wikipedia "Aurifeuillean factorization", MathWorld Gaussian Mersenne, plus (via pdftotext, already saved by the fetch tool) the reference lists of Adegoke's three arXiv papers and the Canad. J. Math. paper BBG, and Bailey's Compendium text (Apr 2023 version).

## 12. Sources
- https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.tex (also .pdf, .html in the same directory; the names chamberland.pdf / chamberland10.pdf return 404)
- https://eudml.org/doc/51705 ; https://zbmath.org/2000853 (Zbl 1073.11076)
- https://oeis.org/A057429 , A088962, A207040, A104885, A182300, A007670, A007671
- https://api.crossref.org/works/10.1090/S0025-5718-10-02324-0 (Berrizbeitia-Iskra, Math. Comp. 79 (2010) 1779-1791; AMS page 403)
- https://t5k.org/glossary/xpage/GaussianMersenne.html ; https://mathworld.wolfram.com/GaussianMersennePrime.html ; https://en.wikipedia.org/wiki/Aurifeuillean_factorization
- https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf (BBG, CJM 56 (2004))
- https://arxiv.org/pdf/1603.05810 , https://arxiv.org/pdf/1603.07395 , arXiv 1603.04974 (Adegoke et al.); https://arxiv.org/abs/1906.09629 (Barsky-Munoz-Perez-Marco; page did not show whether it cites Chamberland)

## 13. Search log
WebSearch calls (total 1):
 W1. "Chamberland Binary BBP-formulae for logarithms and generalized Gaussian-Mersenne primes cited"
Endpoint / page queries (total 41, of which 11 returned an error: 3 x 404, 1 x 403, 7 x 429 as listed):
 1 cs.uwaterloo .../Chamberland/chamberland10.pdf (404)
 2 .../Chamberland/chamberland.html (404)
 3 .../Chamberland/chamberland.pdf (404)
 4 .../Chamberland/ directory listing (found chamberland60.*)
 5 OpenAlex works?search=title (429)
 6 chamberland60.tex download (read in full)
 7 chamberland60.pdf download (same text; not separately read)
 8 OEIS id:A057429
 9 Crossref search title
10 Semantic Scholar search (429)
11 OEIS q=Chamberland Gaussian-Mersenne
12 OEIS id:A088962
13 OEIS id:A207040
14 OEIS id:A104885
15 OEIS id:A007670
16 zbMATH Open search
17 Semantic Scholar again (429)
18 OpenAlex search (429)
19 OEIS id:A182300
20 PrimePages Gaussian Mersenne glossary
21 AMS page of Berrizbeitia-Iskra (403)
22 Crossref works/10.1090/S0025-5718-10-02324-0
23 arXiv author page Berrizbeitia (404)
24 EuDML 51705
25 OpenAlex works/doi:10.1090/S0025-5718-10-02324-0 (id W2032759317)
26 OpenAlex works filter title/author (429)
27 OpenAlex search generalized GM (429)
28 arXiv abs 1906.09629
29 arXiv pdf 1603.05810 (via pdftotext)
30 arXiv pdf 1603.07395 (via pdftotext)
31 Cambridge BBG pdf (via pdftotext)
32 OEIS id:A007671
33 OEIS q=BBP logarithm binary primes
34 arXiv API all:"Gaussian Mersenne" (429)
35 arXiv API abs:Aurifeuillian (429)
36 t5k.org page id=125069 (irrelevant record)
37 t5k.org glossary generalized unique (no match)
38 Wikipedia Aurifeuillean factorization
39 Wikipedia Gaussian integer
40 GitHub search repositories "Gaussian Mersenne BBP" (0 results)
41 MathWorld Gaussian Mersenne Prime
Totals: WebSearch = 1; endpoint queries = 41.
