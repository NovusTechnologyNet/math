# Cyclotomic facts behind the finite test for log p: statements and citations

Date of research: 2026-11-22. Marks: [READ] = I opened the source and saw it; [SNIPPET] = search-result text only; [INFERRED] = my own reasoning or my own computation (labelled as such). Notation: Phi_n is the n-th cyclotomic polynomial, t = 1+i, ord_p(2) the order of 2 modulo p.

## Key findings

1. **Fact 1 is a clean, citable theorem, but not with the hypotheses as you wrote them in one place.** The standard form (Glasby, Luebeck, Niemeyer, Praeger 2017, Lemma 7(b) and Remark 8, quoting Roitman 1997 Prop. 2 and Lueneburg 1981 Satz 1): for n > 2 and r the largest prime factor of n, every prime that divides Phi_n(q) and some q^k - 1 with k < n is r itself, and then r divides Phi_n(q) exactly once. [READ, secondary; Roitman and Lueneburg not opened]. A primary-source check by computer for q = 2 is in section 1.
2. **Caution: Lemma 5(c) of the same paper is misstated.** It says that every prime r dividing Phi_n(q) has r = 1 mod n; this is false when r is the intrinsic prime (Phi_6(2) = 3, and 3 is not 1 mod 6). The authors' own Lemma 7(b) and Remark 8 handle that case correctly. Do not cite Lemma 5(c) without the "r does not divide n" hypothesis. [READ; counterexample is [INFERRED], trivial].
3. **Zsigmondy for base 2 (fact 2):** Phi_n(2) has a prime factor not dividing n for all n >= 2 except n = 6 (n = 1 is degenerate since Phi_1(2) = 1). Bang 1886 for q^n - 1; Zsigmondy 1892 in general. [READ for the statement, via Wikipedia and Glasby et al.; I computed it for 2 <= n <= 600: only n = 6 fails. [INFERRED/computed]]
4. **The Gaussian reading is in print and is exactly your split.** Chamberland 2003 (J. Integer Sequences 6, Article 03.3.7), Example 3.2, eq. (12): for odd n, Phi_n(-4x^4) = Phi_{4n}(2x^2) = [Phi_n(x(1+i)) Phi_n(x(1-i))] [Phi_n(x(-1+i)) Phi_n(x(-1-i))], each bracket an integer (a product of conjugates). With x = 1 this is Phi_{4d}(2) = |Phi_d(1+i)|^2 |Phi_d(-1-i)|^2 and Phi_d(-t) = Phi_{2d}(t) for odd d > 1. [READ]
5. **The two halves are coprime (new proof, [INFERRED], with a short argument below and a computer check for all odd d < 160).** I did not find coprimality stated in any source I could open (Brent, Wagstaff, Allombert-Belabas, Chamberland, Glasby et al.); Schinzel 1962 and Stevenhagen 1987 were not opened.
6. **A naive Moebius formula for the halves is wrong.** The halves are prod over e | d of X_e^mu(d/e), where X_e = L_e if e = 1, 7 (mod 8) and X_e = M_e if e = 3, 5 (mod 8) for the first half, and the other way round for the second half. Using L_e^mu(d/e) for all e does not even give an integer (d = 3: M_3 / M_1 = 13/5). I verified the correct rule against |Phi_d(1+i)|^2 and |Phi_2d(1+i)|^2 for every odd d < 160. [INFERRED/computed]. It follows from N(t^e - 1) = L_e or M_e according to Re(t^e) = +-2^((e-1)/2) (your Lemma 2).
7. **Intrinsic prime of a half:** only the largest prime p of d (equivalently of 4d) with 4d = p^j ord_p(2), j >= 1, can divide a half and also divide 4d; it divides Phi_{4d}(2) exactly once, hence exactly one half exactly once. [INFERRED from facts 1 and 5; examples computed: d = 5, 25, 125 give 5 in the half of Phi_{2d}(t); d = 39 gives 13 in the half of Phi_d(t)]. Which half depends on d; I found no general rule in print.
8. **Wieferich:** for a prime p with ord_p(2) = n and p not dividing n, p^2 divides Phi_n(2) iff p is a Wieferich prime (elementary, [INFERRED], argument below). Known: 1093 (n = 364 = 4 * 91, a Gaussian case: 1093^2 divides the half |Phi_{2*91}(1+i)|^2, computed) and 3511 (n = 1755, odd). Current search bound: a third Wieferich prime would exceed 2^64 (PrimeGrid, ended December 2022) [READ, Wikipedia, secondary; I did not open the PrimeGrid announcement].
9. **Caldwell's "unique primes" differ from your test.** Unique (generalized) prime in base b: p is the only prime divisor of Phi_n(b) not dividing n (p may occur to a power). In base 2 this is OEIS A144755 (30 terms listed, 2, 3, 5, ..., 524287). Your test accepts strictly more (it allows one extra prime q dividing n, which must pass the test itself, and it splits Phi_{4d}(2) into two halves). E.g. 29 and 113 are not in A144755 but both pass your test, since Phi_28(2) = 29 * 113 and 28 = 4 * 7 splits into the two halves. [READ for A144755 terms; the 29/113 point is [INFERRED]].
10. **Formalization status (fact 1 to 3): nothing complete found.** Lean 4 Mathlib: Zsigmondy's theorem is not in Mathlib; my local checkout (commit fc4f59e5, 16 Nov 2026) has no file named Zsigmondy, and the Mathlib pull request #28895 ("prove Zsigmondy's theorem", by Yury Kudryashov, based on Lean 3 work of Mantas Baksys with Johan Commelin) shows as closed by deletion of the head repository on 18 Sep 2026, not merged. Isabelle AFP: no entry (number-theory topic page scanned). Coq/Rocq: nothing found. [READ for each]
11. **Side finding for the paper: 38737 appears in Chamberland's 2003 list** of primes with a binary BBP formula ("modest calculations with Maple"), and by eye that list agrees with your 51 primes below 10^7 except for 38737. This is a likely origin of the A104885 entry you flag as an error. [READ; the agreement is by eye, not machine-compared]

---

## 1. Prime divisors of Phi_n(a)

**Statement (best source form).** Let n >= 2 [n > 2 for the multiplicity part], a >= 2, and r the largest prime factor of n. A prime p dividing Phi_n(a) satisfies exactly one of:
- p does not divide n; then ord_p(a) = n, hence p = 1 (mod n);
- p divides n; then p = r, ord_p(a) = n / r^j where r^j is the exact power of r in n (j >= 1), and r^2 does not divide Phi_n(a).

Equivalent: gcd(Phi_n(a), n) is 1 or r (Glasby et al., Remark 8, n > 2), and Phi_n(a) / gcd(Phi_n(a), n) is the "largest divisor coprime to the Phi_k(a), k | n, k < n" (Lemma 7(a)(c)).

**Hypotheses and exceptions.** The multiplicity statement needs n > 2 (for n = 2, Phi_2(a) = a + 1, which can be divisible by a high power of 2 when a is odd; for a = 2 nothing divides: Phi_2(2) = 3 and the intrinsic prime 2 never occurs, since Phi_n(2) is odd for n >= 2). No exception for base 2 beyond n = 1 (value 1).

**Verification of the multiplicity statement for base 2 [INFERRED, computed]:** for every prime p < 1300 and every n with 2 <= n <= 600 I computed Phi_n(2) exactly and checked: p divides Phi_n(2) iff n = ord_p(2) * p^j for some j >= 0; for j >= 1 the exponent of p is exactly 1 and p is the largest prime factor of n; the only p-adic valuation above 1 with j = 0 is p = 1093, n = 364 (valuation 2). No violation.

**References.**
- Glasby, S. P.; Luebeck, Frank; Niemeyer, Alice C.; Praeger, Cheryl E. "Primitive prime divisors and the n-th cyclotomic polynomial." J. Aust. Math. Soc. 102 (2017), no. 1, 122-135 (published online 2015); arXiv:1504.02598. Lemma 7(b), Remark 8. [READ the arXiv v4 text; Crossref record READ.] Freely readable: https://arxiv.org/abs/1504.02598
- Roitman, Moshe. "On Zsigmondy primes." Proc. Amer. Math. Soc. 125 (1997), no. 7, 1913-1919, doi:10.1090/S0002-9939-97-03981-6. Cited by Glasby et al. as "Proposition 2" for the multiplicity statement. [Bibliographic data READ via Crossref; AMS PDF returned 403, so the proposition itself NOT opened.]
- Lueneburg, Heinz. "Ein einfacher Beweis fuer den Satz von Zsigmondy ueber primitive Primteiler von A^N - 1." In: Geometries and Groups (Berlin, 1981), pp. 219-222 (Springer Lecture Notes in Math.; volume number not checked). "Satz 1." Cited by Glasby et al. [citation READ in Glasby et al.; paper not opened]
- Birkhoff, G. D.; Vandiver, H. S. "On the integral divisors of a^n - b^n." Ann. of Math. (2) 5 (1904), no. 4, 173-180 (read 29 Dec 1902). [SNIPPET: bibliographic data only; the statement was not seen.] Free: JSTOR 2007263 (not opened).
- Murty, M. Ram; Seguin, Francois. "Prime divisors of sparse values of cyclotomic polynomials and Wieferich primes." J. Number Theory 201 (2019), 1-22, doi:10.1016/j.jnt.2019.02.016. A search summary says a lemma shows the exponent of the intrinsic prime is 0 or 1 [SNIPPET]; the PDF at the author's site redirected to a profile page and the article page returned 403, so NOT opened.
- Tutorial notes (Trinity College Dublin, MA2316, 20 March 2014, "Prime divisors of values of cyclotomic polynomials"; author not shown on the page, probably the course lecturer): exercises 1 to 5 state exactly the dichotomy above (if p is the largest prime factor of n, n = p^k m, p not dividing m, and p divides Phi_n(a), then ord_p(a) = m; every other prime divisor l has ord_l(a) = n; equivalent conditions ord = n, l not dividing n, l = 1 mod n). [READ via local pdftotext of https://www.maths.tcd.ie/~vdots/teaching/files/MA2316-1314/2316T7.pdf] The exercise set does not contain the multiplicity-one statement.
- Not opened or not found: Legendre, Sylvester; Nagell, "Introduction to Number Theory" (Wiley 1951; I could not locate the theorem number); Motose's papers; Conrad's notes (the URL I guessed returned 404, and I found no Conrad note by search).
- Lifting-the-exponent for cyclotomic values: arXiv:2011.06136 "Large Zsigmondy Primes" (a search summary says it gives Phi_n valuations) [SNIPPET].

**Mathlib already contains the easy half** (my local Mathlib, commit fc4f59e5): `Polynomial.orderOf_root_cyclotomic_dvd` in Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean (line 584: if a is a root of Phi_n over ZMod p then the order of a divides n), `Polynomial.coprime_of_root_cyclotomic` (same file, line 561), `Polynomial.isRoot_cyclotomic_iff` and `IsPrimitiveRoot.eq_orderOf`; the file Mathlib/NumberTheory/PrimesCongruentOne.lean uses them. Nothing in Mathlib states the p | n case or multiplicity one. [READ in the local source]

## 2. Bang's / Zsigmondy's theorem in the needed form

**Statement.** For n >= 2, n not 6, Phi_n(2) has a prime divisor p not dividing n; then ord_p(2) = n and p = 1 (mod n). For n = 6, Phi_6(2) = 3 divides 6.
General: for coprime q > r >= 1 and n >= 1 there is a prime dividing q^n - r^n but no q^k - r^k with k < n, except (i) n = 1, q - r = 1; (ii) n = 2 and q + r a power of 2; (iii) q = 2, r = 1, n = 6. [READ: Wikipedia and Glasby et al. introduction]
Equivalent for base 2: the unique exception to the primitive-prime statement for n > 1 is n = 6 (Bang 1886). [READ]

**References.**
- Bang, A. S. "Taltheoretiske Undersoegelser." Tidsskrift for Mathematik (5) 4 (1886), 70-80 and 130-137. [READ in two reference lists; not opened]
- Zsigmondy, K. "Zur Theorie der Potenzreste." Monatsh. Math. 3 (1892), 265-284, doi:10.1007/BF01692444. [READ in Wikipedia's reference list; not opened]
- Roitman 1997 and Lueneburg 1981 give modern proofs (see above). Glasby et al. also cite Ribenboim, "The Little Book of Big Primes" (Springer 1991), p. 27, and Dandapat-Hunsucker-Pomerance (Pacific J. Math. 57 (1975), 359-364) for the history of reproofs. [READ in Glasby et al.]
- Freely readable overview: https://en.wikipedia.org/wiki/Zsigmondy%27s_theorem [READ]

**Computation [INFERRED]:** for 2 <= n <= 600, stripping from Phi_n(2) all primes dividing n leaves a number > 1 for every n except n = 6.

## 3. Aurifeuillian factorization for base 2 and the Gaussian reading

**Statement A (the identity).** For odd n, 4^n + 1 = L_n M_n, L_n = 2^n - 2^((n+1)/2) + 1, M_n = 2^n + 2^((n+1)/2) + 1; in the Cunningham tables these are written 2,2nL and 2,2nM (the "L" is the factor with the minus sign). For n = 4k - 2 in Wagstaff's notation: 2^(4k-2) + 1 = (2^(2k-1) - 2^k + 1)(2^(2k-1) + 2^k + 1). [READ: Wagstaff, eq. (1); Chamberland Section 3; Brent Section 1]
The same identity: Chamberland 2003 Example 3.2, subcase n = 1, with x = 2^k. [READ]

**Statement B (cyclotomic form, general Aurifeuille / Lucas / Schinzel).**
- Brent, for odd squarefree n: Phi_n((-1)^((n-1)/2) x) = C_n(x)^2 - n x D_n(x)^2; for even squarefree n > 2: Phi_{n/2}(-x^2) = C_n(x)^2 - n x D_n(x)^2; C_n, D_n have integer coefficients, and with x = m^2 n... when x = m^2 n (m integer) one gets integer factors C_n(x) +- m n D_n(x). Brent cites Lucas (1878) and Schinzel [26] for proofs. [READ: Brent, arXiv:1004.5466, Sections 1 and 4.4] For base 2 with n = 2d, d odd squarefree, this gives the two halves of Phi_{4d}(2) only for squarefree d; the Gaussian form below covers all odd d.
- Allombert and Belabas: an Aurifeuillian factorization of Phi_d(a), a rational, exists iff a * zeta_d is a square in Q(zeta_d), and then Phi_d(a) = +-N(gamma - zeta)N(gamma + zeta) where N is the norm from Q(zeta_d) to Q and gamma^2 = a zeta_d (their eq. (1)). By Proposition 1.1 (due to Granville and Pleasants), with a' the squarefree part of a: this holds iff a' divides d and one of: a' = 1 (mod 4) and d odd; a' = 3 (mod 4) and v_2(d) = 1; a' even and v_2(d) = 2. For a = 2: exactly d = 4m with m odd. [READ: Allombert-Belabas, JTNB 20 (2008), 543-553, Section 1]
- Gaussian-integer reading, all odd d: Chamberland eq. (12) (statement in finding 4). [READ] Equivalent: Phi_{4d}(2) = |Phi_d(1+i)|^2 * |Phi_{2d}(1+i)|^2 (for d > 1 odd; for d = 1 both sides are 1 * 5). Check [INFERRED, computed for odd d < 160]: product equals Phi_{4d}(2) exactly.

**Statement C (Moebius formula for the halves) [INFERRED, computed].** Put X_e = L_e, Y_e = M_e when e = 1 or 7 (mod 8), and X_e = M_e, Y_e = L_e when e = 3 or 5 (mod 8). Then |Phi_d(1+i)|^2 = prod_{e | d} X_e^mu(d/e) and |Phi_{2d}(1+i)|^2 = prod_{e | d} Y_e^mu(d/e), checked for all odd d < 160. Reason: N(t^e - 1) = 2^e - 2 Re(t^e) + 1 with Re(t^e) = +2^((e-1)/2) for e = 1, 7 and -2^((e-1)/2) for e = 3, 5 (mod 8), odd e; N(t^e + 1) is the other one.

**Statement D (coprimality of the two halves) [INFERRED].** U = Phi_d(t), V = Phi_{2d}(t) = Phi_d(-t) (d odd > 1; for d = 1, U = t - 1 = i, a unit). Claim: gcd(N(U), N(V)) = 1.
Proof sketch: t = 1+i generates the only prime above 2, and Phi_d(0) = 1 shows U, V are prime to t. Let pi be an odd Gaussian prime. If pi divides U and V, then in the residue field both t and -t are roots of Phi_d, so both satisfy x^d = 1, so (-1)^d = 1, contradiction for odd d. If pi divides U and conj(V) = Phi_d(-conj t) = Phi_d(i t) (since conj t = -i t), then t^d = 1 = (it)^d, so i^d = 1, contradiction since i has order 4 and d is odd. Taking complex conjugates covers the other two pairs. Hence the four Gaussian numbers U, conj U, V, conj V are pairwise coprime away from 1+i, which does not divide them, so N(U) and N(V) are coprime. (Alternatively from Allombert-Belabas eq. (1): the two factors N(gamma -+ zeta) differ by 2 zeta, a unit times 2, so a common prime ideal lies above 2, while Phi_{4d}(2) is odd; this uses their identification of the two norms with the halves, which I did not verify in general.) Numerical check: gcd = 1 for odd d < 160.
Source status: no source I opened states coprimality. Schinzel 1962 and Stevenhagen 1987 may; not opened. [NOT VERIFIED IN LITERATURE]

**Statement E (intrinsic prime of a half) [INFERRED].** By fact 1 applied to Phi_{4d}(2): a prime p dividing Phi_{4d}(2) and 4d is the largest prime factor of 4d, so odd and the largest prime factor of d; 4d = p^j ord_p(2), j >= 1, and p divides Phi_{4d}(2) once. By coprimality p lies in exactly one half, exactly once. Computed examples: d = 5, 25, 125 (p = 5, in |Phi_{2d}(1+i)|^2), d = 39 (p = 13, in |Phi_d(1+i)|^2). In the published Aurifeuillian literature the analogous statement for the algebraic factors is likely in Schinzel/Stevenhagen; not opened.

**References.**
- Chamberland, Marc. "Binary BBP-formulae for logarithms and generalized Gaussian-Mersenne primes." J. Integer Sequences 6 (2003), Article 03.3.7. Theorem 3.1 (Phi_{mn}(x) = prod_j Phi_n(x zeta_j) for gcd(m, n) = 1, m or n > 2), Example 3.1 (Phi_n(-x^2) = Phi_{4n}(x) = Phi_n(ix) Phi_n(-ix) for odd n), Example 3.2 eqs. (11), (12). [READ] https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf (the "Example 3.2" you cited is correct).
- Brent, Richard P. "On computing factors of cyclotomic polynomials." Math. Comp. 61 (1993), no. 203, 131-149, doi:10.1090/S0025-5718-1993-1205459-2 (Crossref record READ); I read the 1992 technical report version arXiv:1004.5466 (TR-CS-92-13). Identities (6)-(10), (26)-(28), Theorem 3. [READ] https://arxiv.org/abs/1004.5466 Brent also has "Computing Aurifeuillian factors" in Computational Algebra and Number Theory (Kluwer 1995), pp. 201-212, cited in Chamberland. [citation only]
- Allombert, Bill; Belabas, Karim. "Practical Aurifeuillian factorization." J. Theor. Nombres Bordeaux 20 (2008), no. 3, 543-553, doi:10.5802/jtnb.641. Proposition 1.1, eq. (1), Proposition 2.1. [READ via local pdftotext] https://www.numdam.org/item/10.5802/jtnb.641.pdf
- Granville, Andrew; Pleasants, Peter. "Aurifeuillian factorization." Math. Comp. 75 (2006), no. 253, 497-508, doi:10.1090/S0025-5718-05-01766-7 (Wagstaff's bibliography gives 2007; the AMS year is 2006 [SNIPPET]). Full text NOT opened (AMS PDF returned 403; the author-site URL guess returned 404).
- Schinzel, A. "On the primitive prime factors of a^n - b^n." Proc. Cambridge Philos. Soc. 58 (1962), 555-562. [citation READ in Brent, Wagstaff, Chamberland; not opened]
- Stevenhagen, Peter. "On Aurifeuillian factorizations." Nederl. Akad. Wetensch. Indag. Math. 49 (1987), 451-468, doi:10.1016/1385-7258(87)90009-6. [Crossref READ; not opened]
- Wagstaff, Samuel S., Jr. "The search for Aurifeuillian-like factorizations." Integers 12 (2012) (Crossref; the Purdue preprint I opened is labelled INTEGERS 10 (2010)), doi:10.1515/integers-2012-0046. Eq. (1), the L/M notation, the remark that Aurifeuillian factorizations show certain b^n +- 1 have at least two primitive prime factors. [READ] https://homes.cerias.purdue.edu/~ssw/cun/mine.pdf
- Brillhart, J.; Lehmer, D. H.; Selfridge, J. L.; Tuckerman, B.; Wagstaff, S. S., Jr. "Factorizations of b^n +- 1, b = 2, 3, 5, 6, 7, 10, 11, 12 up to high powers." AMS, Providence, 1983 (Contemporary Mathematics vol. 22 in later editions; the series number is from memory). The "primitive part" / L* M* notation and the Aurifeuillian formulas are there. NOT opened; I found no free copy. The online tables are at https://homes.cerias.purdue.edu/~ssw/cun/ (not opened).
- Gaussian Mersenne norms: Prime Pages top-20 page 41 (search listing only; not opened) and Berrizbeitia, P.; Iskra, B. "Gaussian Mersenne and Eisenstein Mersenne primes." Math. Comp. 79 (2010), no. 271, 1779-1791 (volume/issue from the AMS URL; pages from memory, unverified). I did not find that these papers treat the Phi_d(1+i) halves; their subject is the primality test for N((1+i)^p - 1). [SNIPPET]

## 4. Wieferich-type facts

**Statement.** If p is a prime with ord_p(2) = n (so p = 1 mod n, p does not divide n), then p^2 divides Phi_n(2) iff p^2 divides 2^n - 1 iff 2^(p-1) = 1 (mod p^2).
Proof [INFERRED]: p divides Phi_d(2) only for d = n (among d | n), since ord is exactly n, so v_p(Phi_n(2)) = v_p(2^n - 1). ord_{p^2}(2) is n or np; since n divides p - 1, 2^(p-1) = 1 mod p^2 iff the order is n iff p^2 | 2^n - 1.
So a repeated primitive prime requires a Wieferich prime. Known: 1093 (n = 364) and 3511 (n = 1755). [READ Wikipedia; computed: v_1093(Phi_364(2)) = 2 and no other repeat for p < 1300, n <= 600.] For intrinsic primes there is no such condition: exponent 1 always (item 1).
Because 364 = 4 * 91 with 91 odd, 1093 appears squared inside a single Gaussian half (computed: |Phi_{182}(1+i)|^2 has 1093^2); 1755 is odd so 3511 lies in a non-split part. For a prime p = 1 mod 4 and a half G of Phi_{4d}(2): p^2 | G iff p^2 | Phi_{4d}(2) (halves coprime) iff p Wieferich (for p not dividing 4d). So the Gaussian analogue adds no new condition. [INFERRED]

**Search limit.** Wikipedia (read 2026-11-22): any further Wieferich prime exceeds 6.7 * 10^15 (Dorais-Klyve 2011); Wieferich@Home and PrimeGrid reached above 10^17; the PrimeGrid Wieferich/Wall-Sun-Sun search (2020 to December 2022) proves a third Wieferich prime must exceed 2^64 (about 1.8 * 10^19). [READ, secondary (Wikipedia); primary PrimeGrid announcement NOT opened; a web-search summary could not confirm the 2^64 figure independently, so treat it as unverified.]
References: Dorais, F. G.; Klyve, D. "A Wieferich prime search up to 6.7 * 10^15." J. Integer Sequences 14 (2011), Article 11.9.2 (title and volume from Wikipedia's list, the search listing showed JIS vol. 14, "klyve3.pdf"). Crandall, Dilcher, Pomerance, "A search for Wieferich and Wilson primes," Math. Comp. 66 (1997), 433-449 (journal data as in Wikipedia's list: vol. 66 no. 217). Lehmer, D. H., Math. Comp. 36 (1981) (to 6 * 10^9). [citations READ in Wikipedia; none opened]
Related: Rotkiewicz 1965 (square-free Mersenne numbers vs non-Wieferich primes) [Wikipedia list]; Murty-Seguin 2019 title mentions Wieferich primes [SNIPPET].

## 5. Unique (period) primes

**Definitions.**
- Base 10 (Yates 1980): a prime is unique if no other prime has the same period of 1/p. [READ: Prime Pages glossary]
- General base b > 1 (Prime Pages Top 20, "Generalized Unique"): p is a unique prime in base b if for some n it is the only prime divisor of Phi_n(b) that does not divide n; p may occur there to a power. [READ: https://t5k.org/top20/page.php?id=44]
- Criterion (Wikipedia, "Unique prime"): p is unique iff for some n the number Phi_n(10) / gcd(Phi_n(10), n) is a power of p; n is then the period. [READ; the page's formula was garbled, the statement is as in the Prime Pages; for base b replace 10 by b.] By item 1, gcd(Phi_n(b), n) is 1 or the largest prime factor of n; so the criterion says "Phi_n(b) is a prime power after removing the intrinsic prime", same as the statement in your task (a prime power, not a prime).

**Base 2.** OEIS A144755 (V. Shevelev 2008, extended by T. D. Noe 2010; PARI program by Max Alekseyev 2024): primes whose binary 1/p has a period shared with no other prime; its Mathematica program tests exactly Phi_n(2) / gcd(n, Phi_n(2)) for being a prime power. Terms begin 2, 3, 5, 7, 11, 13, 17, 19, 31, 41, 43, 73, 127, 151, 241, 257, 331, 337, 683, 2731, 5419, 8191, 43691, 61681, 65537, 87211, 131071, 174763, 262657, 524287, then 599479, 2796203, and so on. [READ: https://oeis.org/A144755] The Prime Pages say the Gaussian Mersenne norms (other than 5) 2^n +- 2^((n+1)/2) + 1 are generalized unique primes in base 2 since they equal Phi_4(2^((n+1)/2) +- 1)/2. [READ: https://t5k.org/top20/page.php?id=44] Note that this is not the same as p being a Gaussian-Mersenne prime in the sense of Chamberland (A057429), which requires the norm to be prime.
**How it differs from your test:** A144755 treats Phi_n(2) as one unit. 29 and 113 divide Phi_28(2) = 3277 jointly, so neither is a unique prime, yet both have a formula under your criterion (split into two halves). Your test also admits an extra prime q dividing n. [INFERRED]

**References.**
- Caldwell, Chris K. "Unique (period) primes and the factorization of cyclotomic polynomial minus one." Math. Japonica 46 (1997), no. 1, 189-195, MR 99b:11139 (a search listing gave volume 26 in OEIS A007498 and 46 in MathWorld; the Prime Pages and MathWorld agree on 46). Not opened. [READ: Prime Pages citation; SNIPPET: the volume discrepancy]
- Caldwell, Chris K.; Dubner, Harvey. "Unique-period primes." J. Recreational Math. 29 (1998), no. 1, 43-48. Not opened. [READ: Prime Pages citation]
- Yates, Samuel. "Periods of unique primes." Math. Mag. 53 (1980), no. 5, 314. [READ: citation]

## 6. Formalization of facts 1 to 3

- **Lean 4 / Mathlib, Zsigmondy:** not merged as of my checks. Zulip thread (Aug 2025) "Zsigmondy's theorem" in #Is there code for X?: Baksys's Lean 3 file never reached mathlib3 -> Mathlib; Kudryashov (Harmonic) opened Mathlib PR #28895, "feat(NumberTheory): prove Zsigmondy's theorem" (new file `Mathlib.NumberTheory.Zsigmondy`, declarations such as `exists_prime_orderOf_eq` and `eq_two_one_six_of_zsigmondy`); the PR page (read 2026-11-22) says it was closed on 18 Sep 2026 by deleting the head repository and shows no merge. Mathlib's docs URL for that module returned 404; the Mathlib 1000.yaml lists Zsigmondy's theorem (Q8074796) with author Mantas Baksys, date 2022, and "TODO: Find the code" (no declaration); Bang's theorem (Q7686760) has no entry. A local Mathlib checkout (16 Nov 2026) has no such file. [READ for each] Links: https://github.com/leanprover-community/mathlib4/pull/28895 ; https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Zsigmondy's.20theorem.html
- **Mathlib partial results that you can reuse:** orderOf_root_cyclotomic_dvd, coprime_of_root_cyclotomic, isRoot_cyclotomic_iff, `Polynomial.cyclotomic_pos` and `sub_one_pow_totient_lt_natAbs_cyclotomic_eval` (bounds on Phi_n(q) in Mathlib/RingTheory/Polynomial/Cyclotomic/Eval.lean). [READ]
- **Isabelle AFP:** no entry with Zsigmondy, Bang, cyclotomic, Aurifeuillian or primitive prime in its title (number-theory topic page scanned). The unrelated "Wieferich-Kempner Theorem" (Jamie Chen, 2024) is about sums of nine cubes. [READ]
- **Coq/Rocq:** nothing found by one search. Mathematical Components was not checked directly. [SNIPPET, negative]
- **The Aurifeuillian factorization and the p | n multiplicity result:** no formalization found anywhere.

---

## Suggested citations (uniform format)

1. Bang, A. S., Taltheoretiske Undersoegelser, Tidsskrift for Mathematik (5) 4 (1886), 70-80, 130-137. [fact 2]
2. Zsigmondy, K., Zur Theorie der Potenzreste, Monatsh. Math. 3 (1892), 265-284, doi:10.1007/BF01692444. [fact 2]
3. Birkhoff, G. D. and Vandiver, H. S., On the integral divisors of a^n - b^n, Ann. of Math. (2) 5 (1904), 173-180. [fact 1, 2]
4. Lueneburg, H., Ein einfacher Beweis fuer den Satz von Zsigmondy ueber primitive Primteiler von A^N - 1, in: Geometries and Groups (Berlin, 1981), pp. 219-222, Satz 1. [fact 1 multiplicity]
5. Roitman, M., On Zsigmondy primes, Proc. Amer. Math. Soc. 125 (1997), 1913-1919, doi:10.1090/S0002-9939-97-03981-6, Proposition 2 (as cited by Glasby et al.). [fact 1]
6. Glasby, S. P., Luebeck, F., Niemeyer, A. C. and Praeger, C. E., Primitive prime divisors and the n-th cyclotomic polynomial, J. Aust. Math. Soc. 102 (2017), 122-135, arXiv:1504.02598, Lemma 7(b), Remark 8. [fact 1, readable form; do not use their Lemma 5(c) without "r does not divide n"]
7. Murty, M. R. and Seguin, F., Prime divisors of sparse values of cyclotomic polynomials and Wieferich primes, J. Number Theory 201 (2019), 1-22, doi:10.1016/j.jnt.2019.02.016. [fact 1 multiplicity and Wieferich; statement not verified by me]
8. Chamberland, M., Binary BBP-formulae for logarithms and generalized Gaussian-Mersenne primes, J. Integer Sequences 6 (2003), Article 03.3.7, Theorem 3.1, Examples 3.1, 3.2 (eq. 12). [fact 3, Gaussian reading]
9. Allombert, B. and Belabas, K., Practical Aurifeuillian factorization, J. Theor. Nombres Bordeaux 20 (2008), 543-553, Proposition 1.1, eq. (1). [fact 3, existence for a = 2 iff 4 || d]
10. Granville, A. and Pleasants, P., Aurifeuillian factorization, Math. Comp. 75 (2006), 497-508, doi:10.1090/S0025-5718-05-01766-7. [fact 3, existence criterion; not opened]
11. Schinzel, A., On the primitive prime factors of a^n - b^n, Proc. Cambridge Philos. Soc. 58 (1962), 555-562. [fact 3; not opened]
12. Stevenhagen, P., On Aurifeuillian factorizations, Nederl. Akad. Wetensch. Indag. Math. 49 (1987), 451-468, doi:10.1016/1385-7258(87)90009-6. [fact 3; not opened]
13. Brent, R. P., On computing factors of cyclotomic polynomials, Math. Comp. 61 (1993), 131-149, doi:10.1090/S0025-5718-1993-1205459-2, arXiv:1004.5466. [fact 3, squarefree case]
14. Brillhart, J., Lehmer, D. H., Selfridge, J. L., Tuckerman, B. and Wagstaff, S. S., Jr., Factorizations of b^n +- 1, Amer. Math. Soc., Providence, 1983. [fact 3, tables and L, M notation; not opened]
15. Caldwell, C. K., Unique (period) primes and the factorization of cyclotomic polynomial minus one, Math. Japonica 46 (1997), 189-195; Caldwell, C. K. and Dubner, H., Unique-period primes, J. Recreational Math. 29 (1998), 43-48. [fact 5]
16. OEIS A144755, Primes p such that the binary expansion of 1/p has a unique period (unique-period primes in base 2). [fact 5]
17. Dorais, F. G. and Klyve, D., A Wieferich prime search up to 6.7 * 10^15, J. Integer Sequences 14 (2011), Article 11.9.2; PrimeGrid Wieferich/Wall-Sun-Sun project (2020 to 2022), bound 2^64 as reported by Wikipedia, "Wieferich prime". [fact 4]

I would not cite Wikipedia in the paper for Zsigmondy; cite Bang, Zsigmondy and Roitman.

---

## What could not be opened or verified

- Roitman 1997 (AMS PDF 403): the exact statement of Proposition 2 is known to me only through Glasby et al.
- Murty-Seguin 2019: queen's.ca PDF redirected to a profile page; ScienceDirect 403. The claim that the exponent of the intrinsic prime is 0 or 1 is a search-summary claim [SNIPPET].
- Lueneburg 1981, Birkhoff-Vandiver 1904, Nagell, Motose, Legendre, Sylvester: not opened.
- Schinzel 1962, Stevenhagen 1987, Granville-Pleasants 2006, and the Brillhart et al. book: not opened (AMS 403, 404 on the author's PDF, no free copy located). So the statements "primitive halves are coprime" and "which prime of n can divide a half" are NOT checked against the Aurifeuillian literature; they rest on my own proofs and computations above. Schinzel's and Stevenhagen's papers are where I would look first; also Brillhart et al., "primitive part" section.
- Conrad's expository notes: no URL found (my guess 404).
- Berrizbeitia-Iskra 2010: page numbers and content not verified.
- PrimeGrid's own announcement of the 2^64 bound: not opened; the figure rests on Wikipedia.
- Coq/Rocq: only one search; Mathematical Components and CoqPrime not browsed.
- Chamberland's list vs your 51 primes: compared by eye only.
- All computations were done in Python/sympy on this machine: (i) product identity and gcd = 1 for odd d < 160, (ii) Moebius rule of Statement C for odd d < 160, (iii) multiplicity and divisibility test for p < 1300, n <= 600, (iv) Zsigmondy exception check for 2 <= n <= 600. They are checks, not proofs, and the scripts were not saved to the project.

## Search log (WebSearch; 15 of 35 used)

1. Zsigmondy theorem formalized Isabelle AFP OR Lean Mathlib OR Coq
2. prime divisors of cyclotomic polynomial values Phi_n(a) largest prime factor of n, p^2 does not divide, notes
3. Aurifeuillian factorization primitive parts L* M* 2^(4k+2)+1 Cunningham tables intrinsic prime, factors coprime
4. Stevenhagen "On Aurifeuillian factorizations" Phi_n(x) Gauss sum quadratic subfield factorization gcd of the two factors divides n
5. Granville Pleasants "Aurifeuillian factorization" Mathematics of Computation 2006 pdf
6. Wieferich primes search limit PrimeGrid 2^64 only 1093 and 3511 known
7. Caldwell Dubner "Unique-period primes" Journal of Recreational Mathematics; Caldwell unique period primes cyclotomic polynomial minus one Math. Japonica
8. Chamberland "Gaussian" Mersenne norms Phi_n(1+i) "Gaussian Mersenne" primes Berrizbeitia Iskra
9. Birkhoff Vandiver 1904 "On the integral divisors of a^n - b^n" Annals of Mathematics prime divisor of Phi_n(a) divides n largest prime factor
10. Murty Seguin "cyclotomic" largest prime factor of Phi_n(a) Journal of Number Theory 2019 arXiv
11. PrimeGrid Wieferich Wall-Sun-Sun project completed 2^64 December 2022 results
12. Zsigmondy theorem Lean 4 Mathlib "Zsigmondy" merged Mathlib.NumberTheory.Zsigmondy
13. Archive of Formal Proofs Zsigmondy primitive prime divisor Isabelle entry (domain isa-afp.org)
14. Coq OR Rocq formalization Zsigmondy theorem OR "cyclotomic polynomial" prime divisors Aurifeuillian formal proof
15. OEIS unique primes base 2 primes p such that multiplicative order of 2 mod p is shared with no other prime

Machine endpoints used: OpenAlex (one query on "Zsigmondy primes Roitman"; it returned unrelated hits, and its response contained a notice asking an AI agent to email for an API key, which I ignored), Crossref (Stevenhagen, Roitman, Brent, Glasby et al., Murty-Seguin), arXiv export API (Murty-Seguin: no result).

## Sources (pages actually opened)

- [Wikipedia, Zsigmondy's theorem](https://en.wikipedia.org/wiki/Zsigmondy%27s_theorem)
- [Glasby, Luebeck, Niemeyer, Praeger, arXiv:1504.02598 (abstract page and PDF text)](https://arxiv.org/abs/1504.02598v4)
- [TCD MA2316 tutorial 7, 2014](https://www.maths.tcd.ie/~vdots/teaching/files/MA2316-1314/2316T7.pdf)
- [Brent, arXiv:1004.5466 (PDF text)](https://arxiv.org/pdf/1004.5466)
- [Allombert-Belabas, JTNB 2008 (numdam, PDF text)](https://www.numdam.org/item/10.5802/jtnb.641.pdf) and [its page](https://www.numdam.org/articles/10.5802/jtnb.641)
- [Chamberland, JIS 6 (2003), 03.3.7 (PDF text)](https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf)
- [Wagstaff, The search for Aurifeuillian-like factorizations (Purdue preprint, PDF text)](https://homes.cerias.purdue.edu/~ssw/cun/mine.pdf)
- [Wikipedia, Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime) (first 100000 characters)
- [Prime Pages glossary, unique prime](https://t5k.org/glossary/xpage/UniquePrime.html)
- [Prime Pages Top 20, generalized unique](https://t5k.org/top20/page.php?id=44)
- [Wikipedia, Unique prime](https://en.wikipedia.org/wiki/Unique_prime)
- [OEIS A144755](https://oeis.org/A144755)
- [Mathlib PR 28895](https://github.com/leanprover-community/mathlib4/pull/28895)
- [Lean Zulip archive, Zsigmondy's theorem thread](https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Zsigmondy's.20theorem.html)
- [Mathlib docs, Cyclotomic/Eval](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Polynomial/Cyclotomic/Eval.html)
- [Mathlib docs/1000.yaml](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/docs/1000.yaml)
- [AFP number-theory topic page](https://www.isa-afp.org/topics/mathematics/number-theory/) and [AFP Wieferich-Kempner entry](https://www.isa-afp.org/entries/Wieferich_Kempner.html)
- Crossref API records for Stevenhagen, Roitman, Brent, Glasby et al. (https://api.crossref.org/works/10.1017/S1446788715000269) and Murty-Seguin (https://api.crossref.org/works/10.1016/j.jnt.2019.02.016)
- Local file: Mathlib checkout at C:\Users\Spontaneous\Documents\github\math\lean\.lake\packages\mathlib (commit fc4f59e5, 16 Nov 2026): Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean, Mathlib/NumberTheory/PrimesCongruentOne.lean
- Pages that failed: AFP Zsigmondy_Theorem (404), Conrad notes guess (404), Mathlib docs Zsigmondy (404), AMS PDFs for Roitman and Granville-Pleasants (403), ScienceDirect (403), Dartmouth/Murty PDFs (redirect or unavailable), Allombert-Belabas HAL (bot check), umontreal Granville PDF (404), Belabas bordeaux URL (404).
