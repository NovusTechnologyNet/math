# W2-Q15: the exact statements of Schinzel's theorems on primitive prime factors

Marks: [READ] = read on the source's own page/PDF; [SNIPPET] = seen only in a search result,
review or API record; [INFERRED] = my own conclusion or computation.
Notation: Phi_n(b) is the n-th cyclotomic polynomial at b; P(n) is the largest prime factor of n;
"primitive prime" of Phi_n(b) means a prime p with ord_p(b) = n exactly.

## 1. Summary

1. Schinzel's 1962 paper (Proc. Camb. Phil. Soc. 58, 555-562) is itself about Aurifeuillian
   factorizations: its reference list is Aurifeuille, Lucas, Beeger, Kraitchik, Birkhoff-Vandiver,
   Zsigmondy, Rotkiewicz [READ, Cambridge Core page]. Brent (1993) says the Aurifeuillian
   polynomial identities are proved there "essentially" [READ].
2. I could NOT read the theorem text of the 1962 paper (paywalled; Cambridge shows only the first
   sentence, which sets up coprime a, b with |a| > |b| > 0 and the cyclotomic form Phi_n(a,b))
   [READ]. The only statement of it that I found in print is Stewart's (2013) quotation [READ]:
   a, b coprime and ab a square or twice a square gives P(a^n - b^n) >= 2n + 1, except n = 4, 6, 12
   when a = 2, b = 1; proved by exhibiting at least two primitive divisors via an Aurifeuillian
   factorization.
3. The fuller statement is Schinzel's Lehmer-numbers paper I (Acta Arith. 8, 1963), restating and
   generalizing 1962; Aigner's zbMATH review gives it [SNIPPET]: k = squarefree part of
   M*max(K,L), eta = 1 if k = 1 mod 4 else 2, n/(k*eta) an odd integer, n not in {1,2,3,4,6}:
   at least two primitive prime factors, with a finite explicit exception list when K > 0 (and
   n > n1(L,M) effective when K < 0). For 2^n - 1 this is n = 8m+4 (k = 2, eta = 2).
4. Postnikova-Schinzel 1968 (Mat. Sb. 75) I read in full (English translation, mathnet.ru, free):
   Theorem 1 (n > n0(a,b), computable, via Gelfond), a refinement for purely real fields, and
   Theorem 2 (fixed n and b, all but finitely many a, via Siegel). Details in section 2.
5. Schinzel 1974 (Crelle 268/269): exact text not read (De Gruyter paywall; GDZ page not found).
   Its statement is given in a zbMATH review of Schinzel's 1993 sequel: a constant n0(d) depending
   only on d = degree of A/B, effective (Baker's method) [SNIPPET].
6. Schinzel's Selecta (2007): not readable online by me (zbMATH review only; EMS page 404;
   Google Books API quota exhausted; no archive.org copy).
7. THE KEY ANSWER: the Aurifeuillian claim "each factor has a prime of order exactly n, except
   an explicit finite list" is NOT a formal consequence of the 1962 theorem as quoted (P >= 2n+1)
   and not even of "at least two primitive primes" (those count primes of Phi_n(b), not per
   factor). It is equivalent to: neither factor lies in {1, P(n)}. Checked by exact computation
   for n <= 140: the only failures are (b,n) = (2,4), (2,12), (3,6) where a factor is 1, and
   (2,20) where a factor is 5 = P(20). b = 5: no failure.
8. The earlier helper's doubt at a = 2, b = 1, n = 20 is NOT a misreading. It is a true exception
   of the Aurifeuillian-factor claim: Phi_20(2) = 205 = 5 * 41 and 5 has order 4 mod 5, not 20.
   But it does not contradict Schinzel as quoted by Stewart (41 = 2*20+1, so P >= 2n+1 holds with
   equality); it does mean n = 20 must be on the exception list of any "two primitive primes"
   statement for ab = 2.

## 2. What is known

### (a) Schinzel 1962, Proc. Cambridge Philos. Soc. 58 (1962) 555-562
- Metadata: DOI 10.1017/S0305004100040561, zbMATH 0114.02605 (no review text), MR 0143728;
  OpenAlex W1969888613, 86 citing works, not open access [SNIPPET].
- Cambridge Core page shows only: let a, b be relatively prime integers with |a| > |b| > 0; for
  n > 0 let Phi_n be the n-th cyclotomic polynomial (formula missing), zeta_n a primitive n-th root
  of unity. No theorem on the page. 14 references (Aurifeuille/Le Lasseur via Lucas 1877-78,
  Beeger 1951, Bickmore 1895-97, Birkhoff-Vandiver 1904, Cunningham 1915, Dickson, Dirichlet,
  Kanold 1950, Kraitchik 1922/1924, Lucas 1878 twice, Rotkiewicz 1961, Zsigmondy 1892) [READ].
- Stewart 2013 (Acta Math. 211, arXiv 1008.1274, Introduction) [READ]: Schinzel proved: if a and b
  are coprime and ab is a square or twice a square then P(a^n - b^n) >= 2n+1, provided n = 4, 6, 12
  are excluded when a = 2 and b = 1. The proof shows a^n - b^n has at least two primitive
  divisors, using an Aurifeuillian factorization. Rotkiewicz then extended the argument to Lucas
  numbers and Schinzel to Lehmer numbers (papers I-III), giving (3) with n+1 in place of n-1.
  (In my computation below, the exception list "2, 4, 6, 12" for a = 2, b = 1 is exactly the
  set of n <= 60 with P(2^n - 1) < 2n+1; n = 2 is only excluded if n >= 3 is understood.)
- Stewart also records that Schinzel (1962) ASKED whether some a, b with ab different from +-2c^2
  and +-c^h (h >= 2) have P(a^n - b^n) > 2n for all large n [READ]. Hong (arXiv 2204.01858)
  states the same question; his extracted text reads "ab =" where Stewart's reads "different
  from" (a lost symbol in PDF extraction is likely; I could not tell) [READ].
- Rotkiewicz 1962 (Bull. Acad. Polon. 10, 229-232), zbMATH review by Entringer: using Schinzel's
  method, conditions on L, M, n so that the Lucas number L_n has at least two intrinsic prime
  divisors (a prime dividing L_n but not L_1...L_{n-1} n) [SNIPPET].
- Brent, "On computing factors of cyclotomic polynomials", Math. Comp. 61 (1993) [READ,
  maths-people.anu.edu.au/~brent/pd/rpb135.pdf]: the identities Phi_n((-1)^((n-1)/2) x) =
  C_n^2 - n x D_n^2 (n odd squarefree) and Phi_{n/2}(-x^2) = C_n^2 - n x D_n^2 (n even squarefree)
  are proved in Lucas or Schinzel [1962]; "Schinzel essentially shows" L_n(x) = C_n(x^2) -
  s x n D_n(x^2) (his (26)); his Theorem 3 gives the Aurifeuillian factors F_n^-(x), F_n^+(x) of
  F_n(x) for x = m^2 n by a rounding formula (the displayed formula has a lost square-root sign;
  it expresses F^- as about sqrt(F_n(x)) times a factor close to 1) [READ, garbled].
  So both Aurifeuillian factors have size about the square root of Phi-type value [INFERRED].

### Schinzel, Lehmer numbers I-III (the generalization; Acta Arith. 8 (1963) 213-223, 251-257;
15 (1968) 49-70) [SNIPPET only; full text blocked, matwbn/impan return 403]
- zbMATH 0118.27901 review (Aigner, in German) of I-II: P_n a Lehmer number with parameters
  L > 0, M != 0, (L,M) = 1, K != 0, alpha/beta not a root of unity; k = squarefree kernel of
  M*max(K,L); eta = 1 for k = 1 mod 4, eta = 2 for k = 2, 3 mod 4; n/(k*eta) an odd integer.
  Then P_n, n not in {1,2,3,4,6}, has at least two primitive prime factors: for K > 0 up to
  finitely many explicitly listed exceptions; for K < 0 once n > n1(L,M), effectively computable.
  The review says: for 2^n - 1 (L = 9, M = 2) this gives the known fact about 2^(8m+4) - 1 =
  2^(4m+2)+1 (Aurifeuillian numbers). Proof uses character-sum estimates and Polya-Schur bounds.
  Part II: at least e primitive prime factors for e = 3, 4, 6 via cyclotomic fields of those
  orders. Part III (review): negative discriminant, explicit bounds, with a correction withdrawing
  an earlier lower bound on the largest prime factor.
- Mapping to a^n - b^n (rational a, b coprime): k = squarefree kernel of ab. [INFERRED]
  ab = 2: k = 2, eta = 2, n = 4*odd. ab = 3: k = 3, eta = 2, n = 6*odd. ab = 5: k = 5, eta = 1,
  n = 5*odd. These are exactly the n for which Aurifeuillian factorizations of Phi_n(b) exist.

### (b) Schinzel 1974, J. reine angew. Math. 268/269, 27-33
- DOI 10.1515/crll.1974.268-269.27, zbMATH 3450340 / Zbl 0287.12014 (no review; MSC 11R27, 11R04,
  11B39) [SNIPPET]. De Gruyter PDF not accessible; GDZ/digizeitschriften search URL gave 404.
- Statement as given by Boyd's review of Schinzel's 1993 sequel (Math. Comp. 61, 1993, zbMATH
  427910) [SNIPPET]: A, B algebraic integers, (A,B) = 1, AB != 0, A/B of degree d, not a root of
  unity. There is a constant n0(d) such that for n > n0(d), A^n - B^n has a prime ideal factor
  not dividing A^m - B^m for any m < n. The 1993 extension: for A^n - zeta_k B^n, n > c(d,eps)
  (1+log k)^(1+eps).
- How Stewart 2013 phrases it [READ]: in 1962 Schinzel (via Gelfond) obtained a threshold C
  effective in terms of alpha and beta (Ark. Mat. paper, non-real case); in 1974 Schinzel used
  Baker's estimate to replace C by C0 not depending on alpha, beta. DIFFERENCE: zbMATH says n0
  depends on d; Stewart says independent of alpha, beta. Both are consistent if d is regarded
  as fixed (Lucas/Lehmer case d = 2). Bilu-Hong-Gun (arXiv 2108.09857) say the Stewart threshold
  depends only on Q(alpha) [READ].
- Tools quoted from it [READ, Hong 2204.01858 and Bilu-Hong-Gun 2108.09857]: Lemma 4 of Schinzel
  1974: if n >= 2^(d+1) and p is not a primitive divisor of alpha^n - 1 then ord_p Phi_n(alpha)
  <= ord_p(n); and the lower bound for |Phi_n(alpha)| (now with explicit constants, Bilu-Luca
  Acta Arith. 198 (2021)).
- Later numeric values (Stewart 2013 introduction) [READ]: Stewart 1977 got C0 = e^452467; Voutier
  30030; Bilu-Hanrot-Voutier: for n > 30 every Lucas/Lehmer term has a primitive divisor;
  Stewart 1977 also showed 6 (Lucas) and 12 (Lehmer) up to finitely many exceptions. Mignotte's
  zbMATH review of Narkiewicz's survey says: n >= 7, n not in {8,10,12}, finitely many
  exceptions [SNIPPET]. The two descriptions of Stewart 1977 differ (6/12 versus 7 and excluding
  8,10,12); I did not see Stewart 1977 itself.

### (c) Postnikova and Schinzel, Mat. Sb. 75(117) (1968) no. 2; Math. USSR-Sb. 4 (1968) 153-159
[READ in full: English PDF, mathnet.ru/php/getFT.phtml?jrnid=sm&paperid=3975&what=fullteng; the
text layer is partly garbled, so inequalities below are paraphrased]
- Setting: alpha, beta integers of a number field K of degree l, principal ideals (alpha), (beta)
  coprime. A prime ideal divisor P of alpha^n - beta^n is primitive if it divides no
  alpha^m - beta^m with m < n.
- Theorem 1: if alpha/beta is not a root of unity, then for n > n0(alpha, beta) the number
  alpha^n - beta^n has a primitive divisor; n0 is computable. Proof: Lemma 1 (p-adic lifting of
  A^p - B^p) and Lemma 2 (if P | Phi_n(alpha,beta) is not primitive then ord_P Phi_n <= ord_P n,
  for n above a bound of size 2^l(2^l - 1)); then a lower bound for |N(Phi_n(alpha,beta))| from
  Gelfond's theorem on divisibility by prime-ideal powers, plus Kronecker's theorem when beta is a
  unit.
- Theorem 1 (second version, purely real fields: all conjugate fields real): n0 independent of
  alpha, beta: n0 = 2^l(2^l - 1) for l >= 5 (the extract is garbled but this is what it reads);
  for l < 5 the proof treats n > 1000 separately. Proof uses only elementary bounds
  |a^m - b^m| and the inequality 2^nu(n) < 39 sqrt-type bound on the number of squarefree divisors.
- Remark in the paper: it would be interesting to prove n0 depends only on K (open then; done in
  Schinzel 1974 via Baker, per the zbMATH description above).
- Theorem 2: n >= 2 fixed, b fixed, a varying over integers of K coprime to b: all but finitely
  many a give a^n - b^n a primitive divisor. Proof: Lemma 2' (a non-primitive P dividing
  Phi_n(a,b) divides n) plus Siegel's theorem (1921) that Phi_n(x,b) has a prime ideal divisor
  of large norm.
- zbMATH 3311010 (no review text).

### (d) Stewart 1977 and how Stewart quotes (a)
- Stewart, "Primitive divisors of Lucas and Lehmer numbers", in Transcendence Theory (Baker-
  Masser eds.), Academic Press 1977: not available online; known only through citations [READ in
  Stewart 2013: C0 = e^452467; 6 and 12 with finitely many exceptions, to be found by Thue
  equations; carried out by Bilu-Hanrot-Voutier].
- Stewart 1977/1975/1981 line: P(a^n - b^n)/n -> infinity for n with few prime factors; the
  2n+1 bound of Schinzel 1962 was "the first unconditional refinement" of P >= n+1 [READ].

### (e) Selecta 2007 (EMS, 2 vols, 100 papers, 13 sections)
- zbMATH 5138337 (Mignotte's review; he says the deepest results of Schinzel have long lists of
  special cases and could not be reproduced) [SNIPPET]. No readable commentary found online.

### Differences among the quotations
- Stewart 2013: "ab a square or twice a square, P >= 2n+1, except n = 4,6,12 (a=2, b=1)".
  Aigner 1963: "k, eta, n/(k eta) odd, n not in {1,2,3,4,6}, at least two primitive factors,
  finite explicit list when K > 0". These are different statements (a bound on P versus a count of
  primitive primes). The second implies the first for n in the Aurifeuillian class once the list
  is dealt with, because two distinct primes congruent to 1 mod n force one to be >= 2n+1.
  [INFERRED]
- The hypothesis "ab square or twice a square" (Stewart) versus "n/(k eta) odd" (Aigner) are not
  the same shape: the second restricts n. I could not see the 1962 hypotheses on n. I only saw
  that the later paper (Lehmer I, as reviewed) restricts n to odd multiples of k*eta.

## 3. Hand computations (all re-checked by exact computation; section 4 gives the sweep)

a = 2, b = 1. Phi_n(2) for n = 4m, m odd. Identity: 2^(4k+2)+1 = (2^(2k+1)+2^(k+1)+1)(2^(2k+1)-2^(k+1)+1).
- n = 4: Phi_4(2) = 5. Factor pair (5, 1): trivial.
- n = 12: Phi_12(x) = x^4 - x^2 + 1, so Phi_12(2) = 13. 2^6+1 = 65 = 13 * 5, where 5 = Phi_4(2) is
  not a factor of Phi_12(2). Pair (13, 1): trivial. Primitive primes of 2^12 - 1: only 13.
  P(2^12 - 1) = 13 < 25 = 2n+1: this is why n = 12 is excepted in Stewart's quotation.
- n = 20: Phi_20(x) = x^8 - x^6 + x^4 - x^2 + 1, Phi_20(2) = 256 - 64 + 16 - 4 + 1 = 205 = 5 * 41.
  2^10 + 1 = 1025 = (2^5+2^3+1)(2^5-2^3+1) = 41 * 25, and 25 = 5 * 5 with one 5 = Phi_4(2);
  so the two Aurifeuillian factors of Phi_20(2) are L = 41 and M = 5.
  Orders: 2 mod 5 has order 4 (2,4,3,1), so 5 is the non-primitive prime P(20) = 5 of
  Phi_20(2); 2^10 = 1024 = 41*25 - 1 = -1 mod 41, so ord_41(2) divides 20, not 10, and 16, 32
  are not 1 mod 41, so ord_41(2) = 20. Primitive primes of 2^20 - 1: only 41.
  Consequence: M = 5 has NO prime of order exactly 20. P(2^20 - 1) = 41 = 2*20+1, so the
  bound P >= 2n+1 holds with equality; Stewart's quoted exception list rightly omits 20.
- n = 28: 2^14+1 = 16385 = 5 * 29 * 113; Phi_28(2) = 29 * 113 (primitive both; 29 = n+1,
  113 = 4n+1). n = 36: 37 * 109 (each = 1 mod 36). n = 44: 397 * 2113. n = 52: 1613 and
  8321 = 53 * 157. n = 60: 61 * 1321.
  Also n = 8 (not Aurifeuillian, 8/4 even): Phi_8(2) = 17 = 2n+1 exactly, one primitive prime.

a = 3, b = 1. Aurifeuillian for n = 6m, m odd. 3^(6k+3)+1 = (3^(2k+1)+1)(3^(2k+1) + 3^(k+1) + 1)(3^(2k+1) - 3^(k+1) + 1).
- n = 6: Phi_6(3) = 9 - 3 + 1 = 7; pair (7, 1), trivial.
- n = 18: Phi_18(3) = 3^6 - 3^3 + 1 = 703 = 19 * 37. 3^9+1 = 19684 = 28 * 703. ord_19(3):
  3^3 = 8, 3^6 = 7, 3^9 = 56 = -1, so order 18. ord_37(3): 3^3 = 27, 3^6 = 729 = 26,
  3^9 = 26 * 27 = 702 = -1, so order 18. Both primitive.
- n = 30: 31 * 271 (each = 1 mod 30). n = 42: Phi_42(3) = 301 * 2269 with 301 = 7 * 43 and 7 = P(42);
  43 is primitive (43 = 1 mod 42), so this factor is saved by 43, not by 7. n = 54: 19441 * 19927.

a = 5, b = 1. Aurifeuillian for n = 5m, m odd.
- n = 5: Phi_5(5) = 625+125+25+5+1 = 781 = 11 * 71 (= 4*(5^2+... ) Aurifeuillian pair (11, 71)).
  5^5 = 3125 = 11 * 284 + 1 = 71 * 44 + 1, so both have order 5. Both primitive.
- n = 15: 181 * 1741 (181 = 12*15+1, 1741 = 116*15+1). n = 25: 9384251 and 101 * 251 * 401.
  n = 35: 85280581 and 211 * 631 * 4201. n = 45: 1171 * 169831 and 297315901. n = 55:
  two composites with primes all = 1 mod 55. (Computed, not by hand.)

## 4. The decisive reduction and computed sweep [INFERRED]

Reduction: let Phi_n(b) = L * M be an Aurifeuillian factorization (b = 2, 3, 5; n in the class
above). Every prime p dividing L (or M), with p not dividing n, has ord_p(b) = n, because p |
Phi_n(b) and p does not divide n. A prime p dividing n and Phi_n(b) must equal P(n) and divide
it only to the first power (n > 2; this is the classical statement, and the p-adic form is Lemma
4 of Schinzel 1974 / Lemma 2 of Postnikova-Schinzel). Hence a factor has a primitive prime
if and only if it is not 1 and not P(n). So the claim is equivalent to: neither |L| nor |M|
lies in {1, P(n)}. This is a SIZE statement; it needs only min(|L|,|M|) > n.

Sweep (exact, polynomial factorization of Phi_n(b y^2) over Z by computer algebra, then evaluation
at y = 1; n up to 140 in each class):
- b = 2, n = 4 mod 8: 18 values of n; failures n = 4 (pair 1,5), n = 12 (1,13), n = 20 (5,41).
  All 15 others have both factors primitive (n = 28, ..., 140).
- b = 3, n = 6 mod 12: 12 values; failure only n = 6 (pair 1,7).
- b = 5, n = 5 mod 10: 14 values; no failure (including n = 5).
Also P(a^n - 1) >= 2n+1 for n <= 60: fails for a = 2 exactly at n = 2, 4, 6, 12; a = 8, 4, 18: no
failure; a = 9: n = 1 only; a = 3: n = 1, 2, 4; a = 5: n = 1, 2.
For n above 140 I did not compute. [INFERRED] Brent's Theorem 3 indicates both factors are about
the square root of the full value, which grows like b^(phi(n)/2), so no failures are expected;
a rigorous bound on min(|L|,|M|) would complete it (I did not find it in print).

## 5. The two questions asked

(1) Is the Aurifeuillian-factor claim for b = 2, 3, 5 a consequence of (a) as stated?
- From Stewart's quotation (P(a^n - b^n) >= 2n+1): No. That bounds one prime of the whole number.
- From "at least two primitive prime factors" (Aigner's form of the generalization): not by logic
  alone: two primitive primes of Phi_n(b) might both lie in L with M in {1, P(n)}. It follows
  only if one knows the primitive primes are distributed over both factors. [INFERRED]
- Schinzel's PROOF, per Stewart ("by means of an Aurifeuillian factorization"), plausibly shows
  exactly that each factor is large enough to carry a primitive prime; I could not confirm it
  because I could not read the proof. [INFERRED]
- So the claim is true by computation to n = 140 with the explicit list above, and reduces to a
  size bound for L and M for larger n. For a publication, state it as: "each factor has a
  primitive prime iff it is neither 1 nor P(n)", cite Schinzel 1962 and Brent 1993 for the
  Aurifeuillian identities, and prove the size bound from Brent's formula or a direct
  estimate. The finite list known to me: (2,4), (2,12), (2,20), (3,6) [computed].

(2) Is the doubt about a = 2, b = 1, n = 20 real or a misreading?
- The quoted form (Stewart's) has exceptions n = 4, 6, 12 and does not list 20. It is NOT
  violated at 20 (P = 41 = 2n+1). So there is no contradiction with the quotation.
- But the doubt about "L = 5? M = 41?" is a real phenomenon, not a misreading: Phi_20(2) = 205 =
  5 * 41, and the factor 5 = P(20) is not primitive. The claim "each factor has a prime of order
  exactly n" is false at (2, 20). Likewise n = 4, 12 for b = 2 and n = 6 for b = 3, where one
  factor is 1.
- For the version "at least two primitive primes" the case n = 20, a = 2, b = 1 has exactly
  one (41), so n = 20 must be on that theorem's finite exception list [INFERRED from the
  computation; the list itself in Lehmer I is behind a paywall].

## 6. What is open (gaps in what I could read)
- The exact theorems and exception list of the 1962 paper: not read (Cambridge shows only the
  first sentence). Candidates to obtain: the Selecta volume (library copy), Schinzel's Lehmer I
  introduction (matwbn.icm.edu.pl and impan.pl return 403 for my client), Stewart 1977.
- The exact statement of the 1974 paper: only via a zbMATH review of its 1993 sequel.
- A published size bound min(|L|,|M|) > n for Aurifeuillian factors of Phi_n(b), n beyond the
  exceptions: not found.

## 7. Leads for this project
1. (days) Prove and formalize: for b in {2,3,5} and n in the Aurifeuillian class, each Aurifeuillian
   factor has a prime of order n unless (b,n) in {(2,4),(2,12),(2,20),(3,6)}. Statement: the
   equivalence in section 4 plus a lower bound for |L|,|M| (Brent's Theorem 3 or the Lucas
   polynomial identity). Fits the Zsigmondy/cyclotomic toolkit already in the project;
   the finite check up to the bound is exact enumeration. Worth noticing because the printed
   version (Schinzel 1962) is hard to access and its exception list is unclear.
2. (days) State cleanly, with the exceptions, "at least two primitive primes" for ab in {2,3,5}
   as a corollary; and the corollary P >= 2n+1 (exceptions 2, 4, 6, 12 for 2^n - 1 by computation).
3. (weeks) Acquire the 1962 and Lehmer I texts through a library to settle the exact theorem and
   exception list; then compare with this computed list.

## 8. Overlap or conflict with section 1 of the rules file
None found. The project's use of Aurifeuillian-type primitive primes for base-2 and base-3
classification is consistent with the above; the exception (2,20) (factor 5 not primitive) is the
only item to double-check wherever the project uses "each Aurifeuillian factor has a primitive
prime".

## 9. Sources
- https://cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/on-primitive-prime-factors-of-anbn/FF4F8CB4D5BEDD2854151670559F36C6
- https://www.mathnet.ru/php/getFT.phtml?jrnid=sm&paperid=3975&what=fullteng&option_lang=eng (Postnikova-Schinzel)
- https://arxiv.org/pdf/1008.1274 (Stewart 2013)
- https://arxiv.org/pdf/2204.01858 (Hong), https://arxiv.org/pdf/2108.09857 (Bilu-Hong-Gun)
- https://maths-people.anu.edu.au/~brent/pd/rpb135.pdf (Brent 1993)
- zbMATH Open API records: 3193035 (Aigner on Lehmer I-II), 3221514 (Entringer on Rotkiewicz),
  427910 (Boyd on Schinzel 1993), 3450340, 3311010, 5138337, 1305300, 7349955
- Crossref/OpenAlex records for DOIs 10.1017/s0305004100040561, 10.1515/crll.1974.268-269.27,
  10.1070/sm1968v004n02abeh002783; eudml.org/doc/207294 (Lehmer II, PDF link 403).

## 10. Search log
WebSearch (1): W1 "Schinzel On primitive prime factors of a^n - b^n 1962 theorem exceptions"
(it returned the Cambridge page, Stewart's arXiv paper, a Waterloo report, MathWorld, an AMS
Math. Comp. page).
Endpoint/fetch queries:
1 Crossref query Schinzel primitive prime factors a^n-b^n; 2 zbMATH ti/au Schinzel primitive prime
factors; 3 OpenAlex search (HTTP 429); 4 arXiv 1008.1274 PDF (text read locally); 5 Cambridge
Core page (WebFetch); 6 uwaterloo Schinzel report PDF (no content); 7 AMS Math. Comp. 1993 page
(403); 8 AMS Granville-Pleasants PDF (403); 9 Crossref Aurifeuillian factorization; 10 Semantic
Scholar (429); 11 arXiv API abs:Aurifeuillian (429); 12 arXiv 0708.3924 PDF (no Schinzel); 13
umontreal Aurifeuillian.pdf (404); 14 digizeitschriften search (404); 15-16 mathnet paper pages
(wrong paper ids); 17 IOP page (403); 18 Crossref DOI record for PS 1968; 19 mathnet
eng/sm/v117/i2/p171 (found); 20 zbMATH Postnikova Schinzel; 21 zbMATH Schinzel A^n-B^n number
fields (10 reviews); 22 mathnet PDF (curl, read in full); 23 Cambridge PDF/HTML (curl, no theorem
text); 24 Google Books feed; 25 Google Books API (429); 26 doi.org Lehmer I (redirect); 27 OpenAlex
DOI record of the 1962 paper; 28 MathWorld Aurifeuillian page (404); 29 impan Lehmer I (HTML only);
30 OpenAlex citing works of the 1962 paper (50 of 84 listed); 31 Crossref Voutier/Lucas-Lehmer
query; 32 Crossref BHV query; 33 OpenAlex x3 (429); 34 AMS Wagstaff 1996 PDF (403); 35 AMS Brent
1993 PDF (403); 36 ScienceDirect Kanold-type PDF (403); 37 arXiv 2204.01858 PDF; 38 arXiv
2108.09857 PDF; 39 Crossref Bilu-Hanrot-Voutier / Voutier DOIs; 40 arXiv API Bilu-Luca (empty);
41 zbMATH Bilu-Luca review; 42 zbMATH 3193035; 43 zbMATH 5138337; 44 zbMATH 1305300; 45 zbMATH
Rotkiewicz 0136.32503 (review via 3221514); 46 zbMATH Stewart 1977 (no result); 47 eudml 207294;
48 matwbn aa8115/116/114 PDFs (403, curl); 49 matwbn WebFetch (403); 50 pldml (403); 51 EMS
Press Selecta page (404); 52 Google Books API curl (429); 53 archive.org advanced search "Schinzel
selecta" (0 hits); 54 De Gruyter 1974 PDF (202, empty); 55 Crossref 1974 paper record; 56 eudml
search page (no hit); 57 AMS 1993 PDF WebFetch (403); 58 zbMATH 427910 (review text); 59 zbMATH
3450340; 60 De Gruyter BHV html (405); 61 Brent PDF (anu.edu.au, read); 62 arXiv 1004.4079 (not
relevant); 63 umontreal Aurifeuillian2.pdf (404); 64 AMS GP 2006 alt URL (403).
Local computations (not web queries): sympy factorization sweeps for Phi_n(b y^2), b = 2,3,5, n
<= 140; and P(a^n - 1) vs 2n+1 for n <= 60.
Totals: WebSearch calls = 1. Endpoint/fetch queries = about 64 (counts include some repeated
host failures: 403/404/429 responses).
Page content judged as instructions: none found.
