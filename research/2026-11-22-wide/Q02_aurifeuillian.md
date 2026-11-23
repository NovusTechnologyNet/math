# Q02: Aurifeuillian factorizations and the primes of each factor

Marks: [READ] = read on the source's own page/PDF; [SNIPPET] = seen only in a search result,
abstract or API record; [INFERRED] = my own conclusion; [COMPUTED] = my own computation (script
described in section 2.6; nothing was run from the web).

## 1. Summary

1. The existence criterion is classical and fully pinned down (Granville-Pleasants, as quoted by
   Allombert-Belabas): write b = t*s^2 with t squarefree. Phi_n(b) splits as L*M over Z (the
   "Aurifeuillian factorization") iff t | n and: n odd if t = 1 mod 4; v2(n) = 1 if t = 3 mod 4;
   v2(n) = 2 if t is even. [READ]
2. I could NOT obtain the text of Schinzel 1962 (paywalled; two secondary accounts only). What
   secondary sources attribute to it is "ab a square or twice a square implies a^n - b^n has at
   least two primitive divisors (hence P(a^n-b^n) >= 2n+1), except n = 4, 6, 12 for a=2, b=1".
   [READ in Stewart's arXiv paper; also the Waterloo commentary, which is vaguer.] That is NOT
   the statement "each of L and M has a primitive prime divisor". The project's statement is a
   different (stronger, and for bases 3, 5 not covered by that hypothesis) claim; I found it in
   no source.
3. [COMPUTED] For the project's statement, with L, M the Aurifeuillian parts of Phi_n(b):
   for b in {2,3,5,6,7,10,11,12,13,14,15} and all admissible n = N0*h, h odd < 40, both L and M
   have a prime factor with full order n, EXCEPT: b = 2: n = 4, 12, 20; b = 3: n = 6. (b = 2,
   n = 4, 12: L = 1; n = 20: Phi_20(2) = 205 = 5*41 and the "L" part is 5 = P(20), which is not
   primitive.) So a blanket statement "for b = 2, 3, 5 each of L, M has a primitive prime" needs
   these four exceptions.
4. Observation on Schinzel's exception list as quoted: (a,b,n) = (2,1,20) has only ONE primitive
   divisor (41), yet is not in the list n = 4, 6, 12. So the literal reading "at least two
   primitive divisors except n = 4, 6, 12" is false at n = 20; the real statement must be
   weaker (the bound P >= 2n+1 holds there, since 41 = 2*20+1). [COMPUTED/INFERRED]
5. Granville-Pleasants: they discuss Schinzel's list of identities, argue it is complete, and
   PROVE completeness under THEIR definition of an Aurifeuillian-type identity. [READ the
   Crossref abstract; Wagstaff's paper paraphrases it the same way.] Wagstaff 2012 searched the
   Cunningham tables empirically and found no new infinite families, but exhibits examples
   (6^106 + 1, 12^193 - 1) with two nearly equal prime cofactors not explained by any known
   identity. [READ]
6. Formal-proof landscape: Mathlib has no merged Zsigmondy theorem; the draft PR #28895 was
   closed on 18 Sep 2026 (author deleted the fork). [READ]
7. OEIS has the explicit L, M families (A220978-A220990, A207262, A230377-9, A352400/1,
   A352711/732) and "primitive part is prime" sequences only for base 2 (A250197/8) and the
   Lucas case (A061442/3). None found for bases 3, 5, 6, 7, 10, 12. A250197's term 10 is the
   N = 20 exception above (see 4.3).
8. Best leads: (i) a finite, machine-checkable theorem "L and M each have a primitive prime
   divisor, except the four listed cases" for the explicit families, bases 2, 3, 5, 6, 7, 10, 12;
   (ii) a table/erratum for the base-2 "primitive part" OEIS entries; (iii) re-deriving the
   statement for general squarefree t via Gauss sums + the Allombert-Belabas size bounds.

## 2. What is known

### 2.1 Existence criterion and structure

- Gauss (n odd prime), Dirichlet (odd squarefree n): 4*Phi_n(x) = A_n(x)^2 - (-1)^((n-1)/2) n
  B_n(x)^2. Aurifeuille / Le Lasseur / Lucas: Phi_n((-1)^((n-1)/2) x) = C_n(x)^2 - n x D_n(x)^2
  for odd squarefree n, and Phi_{n/2}(-x^2) = C_n(x)^2 - n x D_n(x)^2 for even squarefree n > 2.
  C_n, D_n have integer coefficients. [READ, Brent arXiv 1004.5466, eqs (6)-(8)]
- If x = m^2 n then n x = (m n)^2, so Phi(x) = (C - m n D)(C + m n D): two integer factors.
  [READ, Brent rpb127 section 4.3]
- Allombert-Belabas, Prop 1.1 (attributed to Granville-Pleasants): for a in Q, zeta a primitive
  d-th root of unity, alpha = squarefree representative of a modulo squares; a*zeta is a square
  in Q(zeta) iff alpha | d and one of: alpha = 1 mod 4 and d odd; alpha = 3 mod 4 and v2(d) = 1;
  alpha even and v2(d) = 2. Then Phi_d(a) = N(gamma - zeta') N(gamma + zeta') (N = norm from
  Q(zeta_d)), and for |a| > 4 both factors are > 1 because every conjugate satisfies
  |sigma(gamma +- zeta')| >= sqrt|a| - 1; "both factors have roughly the same size".
  [READ, JTNB 20 (2009), section 1; the PDF text is partly garbled, so the exact exponent in
  the size statement is [INFERRED]]
- Wikipedia's equivalent form: b = s^2 t, t squarefree: t = 1 mod 4 needs n = t mod 2t; t = 2, 3
  mod 4 needs n = 2t mod 4t. [READ; agrees with the previous item.]
- Explicit families (Cunningham "L" = minus sign, "M" = plus sign), h odd, k = (h+1)/2: [READ
  MathWorld, OEIS]
  - b = 2: 2^(2h) + 1 = L*M, L,M = 2^h + 1 -+ 2^k. (Phi_4(x) = (x+1)^2 - 2x, x = 2^h)
  - b = 3: 3^(3h) + 1 = (3^h+1) L M, L,M = 3^h + 1 -+ 3^k. (Phi_6(x) = (x+1)^2 - 3x)
  - b = 5: 5^(5h) - 1 = (5^h-1) L M, L,M = 5^(2h) + 3*5^h + 1 -+ 5^k (5^h+1). (Phi_5)
  - b = 6: L,M = x^2 + 3x + 1 -+ 6^k (x+1), x = 6^h, index 12 (OEIS A220981/2). [READ OEIS]
  - b = 12: index 6, L,M = x + 1 -+ 2^h 3^k, x = 12^h (OEIS A220989/90). [READ OEIS]
  - b = 7: index 14, b = 10: index 20 (OEIS A220983/4, A220985/6), b = 11: index 22
    (A220987/8). [READ OEIS names]
  - Index N0 and Phi_{N0}(b^h) = prod over e | h ... Phi_{N0 e}(b) when gcd conditions hold;
    the primitive part Phi_{N0 h}(b) is gcd(L_h, Phi_{N0 h}(b)) times gcd(M_h, ...) [COMPUTED:
    product equals Phi_{N0 h}(b) exactly in all cases tested].
- Example: 3^27 + 1 has the two primitive prime factors 19441 (= "3,27L") and 19927 ("3,27M");
  Phi_54(3) = 19441*19927. [READ Wagstaff 2012; I re-verified Phi_54(3) = 3^18 - 3^9 + 1 =
  387400807 = 19441*19927 by hand arithmetic.]
- Brent's asymptotics: for x = m^2 n, F_n^+(x)/F_n^-(x) = exp(2/m) + O(1/n), so the two
  factors are nearly equal in size. [READ, Brent arXiv, Corollary 1]
- Not all Aurifeuillian-type identities are "algebraic factors of Phi": Beeger/Schinzel
  identities such as Phi_15(x) = (x^4+2x^3+3x^2+2x+1)^2 - 5x(x^3+x^2+x+1)^2 give factors over
  Q(sqrt(-5)) of Phi_15(-x) but, as Brent notes, no factors not already available from (10) and
  gcds. [READ Brent arXiv 1.3]

### 2.2 Schinzel 1962: what I could and could not establish

- Bibliographic: A. Schinzel, "On primitive prime factors of a^n - b^n", Proc. Cambridge Philos.
  Soc. 58 (1962), 555-562 (Cambridge Core says 556-562), DOI 10.1017/S0305004100040561; a, b
  coprime, |a| > |b| > 0. [READ record; full text paywalled, not read]
- Stewart's commentary (Waterloo, Selecta of Schinzel): primitive divisors of a^n - b^n are the
  prime factors of Phi_n(a,b) with at most one exception, a prime factor of n; Schinzel gave new
  Aurifeuillian factorizations, used them to give conditions for at least two primitive
  divisors; Stevenhagen and Brent showed how to compute them; Granville-Pleasants show Schinzel
  found all of them. [READ]
- Stewart, "On divisors of Lucas and Lehmer numbers" (Acta Math 2013, arXiv 1008.1274): if a, b
  coprime and ab is a square or twice a square then P(a^n - b^n) >= 2n+1, excluding n = 4, 6, 12
  when a = 2, b = 1; Schinzel proved it by showing at least two primitive divisors, using an
  Aurifeuillian factorization of Phi_n. Rotkiewicz extended it to Lucas numbers; Schinzel's
  Lehmer papers (Acta Arith 8 (1963) 213, 251; 15 (1968) 49) give conditions for at least k
  primitive prime factors, k = 2, 3, 4, 6, 8. [READ]
- Consequences: (a) the hypothesis "ab square or twice a square" with b = 1 means a = c^2 or
  2c^2; Aurifeuillian factorizations of Phi_n(a) for a with squarefree part 3 or 5 (b = 3,
  5) fall outside it [INFERRED]; the 1962 paper may contain a more general theorem than Stewart
  quotes [not found]. (b) "at least two primitive divisors" is a statement about the pair
  {L, M}-primes only if each of L, M contributes one; this is not stated in what I read.
  (c) (a,b,n) = (2,1,20): 2^20 - 1 = 3*5^2*11*31*41, only 41 is primitive; so the "two
  primitive divisors" reading has another exception unless Schinzel's theorem is only the
  P >= 2n+1 bound. [COMPUTED]
- Verdict on the project's use: "for b = 2, 3, 5 each of L and M has a prime of full order" is
  not exactly Schinzel's theorem. It is, however, easy to see as a consequence of: (i) every
  prime p dividing Phi_n(b) either has ord_p(b) = n or is the largest prime factor of n, and
  then p exactly divides Phi_n(b) (n > 2) [standard Bang/Zsigmondy lemma, not re-read here];
  (ii) gcd(L, M) is tiny; (iii) L, M > P(n). So the statement is equivalent to
  "L, M not in {1, P(n)}", which is a size statement plus the finite exceptions found in 1.3.
  [INFERRED]

### 2.3 Granville-Pleasants (Math. Comp. 75 (2006) 497-508)

- Abstract (Crossref record): discusses Schinzel's 1962 list of identities for factoring
  b^n +- 1, argues Schinzel identified all numbers factorable this way, and proves this under
  their definition of such an identity; then extends the method to f(b^n) for any polynomial f,
  using Faltings (finiteness) and Fried (classification of finite simple groups, monodromy).
  [READ Crossref; full text not obtained: ams.org returned 403, author page 404, zbMATH
  contents unavailable for licensing]
- Wagstaff (Integers 12 (2012) A16): G-P showed Schinzel found all such identities "provided
  one accepts their (reasonable) definition"; some Cunningham numbers suggest other identities
  might exist (6^106 + 1 = 37*26713*P39*P39, 12^193 - 1 = two 77-digit primes), neither coming
  from a cyclotomic or Aurifeuillian factorization; his table search found no new family with
  infinitely many cases and he believes Schinzel's list is complete. [READ]
- So: yes in a precise, definition-dependent sense; the precise definition could not be read.

### 2.4 Other related literature (records only unless marked)

- Stevenhagen, Indag. Math. 49 (1987) 451-468: simple existence argument, coprimality of the
  factors, Euclidean-algorithm computation of the polynomials. [SNIPPET zbMATH review; full
  text 403]
- Brent, "On computing factors of cyclotomic polynomials", Math. Comp. 61 (1993) 131-149 (arXiv
  1004.5466) and "Computing Aurifeuillian factors" (1995, Kluwer, preliminary version rpb127).
  Contains generating functions F_n^+-(x) = Phi_n(x) exp(+- sqrt(n) g_n(x)), O(n^2) algorithms,
  rounding formula, the example 105^105 - 1. [READ both]
- Allombert-Belabas, JTNB 20 (2009): factors for any a in Q, d > 0, via Gauss sums and p-adic
  lifting, PARI/GP implementation (factor_Aurifeuille); runs in deterministic time about
  O~(d^2 L) assuming a suitable RH. [READ]
- Hahn 1994, Math. Japon. 39: Gauss sums and norms from cyclotomic fields. Sun Qi et al.
  (1995-99): q^q +- 1 for q = p^n, and "a new class" Phi_n(eps M) for M = m d^2, n = m k odd
  (example M = 44, n = 253). Duursma 1996: geometric explanation via hyperelliptic Jacobians.
  Wagstaff 1996 (Math. Comp. 65): Bell-number periods via N_p = (p^p - 1)/(p - 1).
  Roettger-Williams 2022 (J. Integer Seq. 25): generalization of Jarden's theorem on V_{mn}
  using palindromic Aurifeuillian cyclotomic factors. Ballot 2023 "Some further properties of
  the Lucas sequences" and Halbeisen-Hungerbuehler-Lemmermeyer 2026 (Integers 26 A30,
  1 + p^n + ... + p^{(p-1)n} as sums of two squares) cite or use the identities. [SNIPPET]
- Rotkiewicz 2005 (Acta Math. Univ. Ostrav. 13): "Aurifeuillian pseudoprimes" (two kinds);
  Wagstaff: Aurifeuillian factorizations imply infinitely many composite pseudoprimes to every
  base b > 1. [SNIPPET; READ for the Wagstaff remark]
- Chamberland 2003 (J. Integer Seq. 6, 03.3.7), "Binary BBP-formulae for logarithms and
  generalized Gaussian-Mersenne primes": builds BBP-type formulas for log p for
  Gaussian-Mersenne p and connects them to Aurifeuillian factorizations. [SNIPPET, zbMATH
  summary] This is the same paper the project already traced OEIS A104885 to; Aurifeuillian
  parts L, M of 2^(4k+2) + 1 are the "Gaussian-Mersenne" norms (e.g. 2^58 + 1).

### 2.5 OEIS (queried by JSON search)

- Base 2: A207262 (2^(4n-2)+1) [SNIPPET]; A153443 "Aurifeuillian primes of the form 2^k+1" (real
  factor of x^k + 1 at x = 2) [READ]; A250197 / A250198: k such that the left / right Aurifeuillian
  primitive part of 2^k + 1 is prime (data of A250197: 10, 14, 18, 22, 26, 30, 42, ...; all
  k = 2 mod 4; defined with L*(n) = gcd(L(n), Phi_2n(2)), L(n) = 2^(n/2) - 2^((n+2)/4) + 1)
  [READ A250197].
- Base 3: A220978 (3^(2n+1) - 3^(n+1) + 1, left factor of 3^(6n+3) + 1). Base 5: A220979,
  A220980 (left/right of 5^(10n+5) - 1). Base 6: A220981, A220982. Base 7: A220983, A220984.
  Base 10: A220985, A220986. Base 11: A220987, A220988. Base 12: A220989, A220990. [SNIPPET]
- k^k +- 1: A230377 (left of k^k + 1, k = 0,2,3 mod 4 squarefree), A230378 (right of k^k - 1,
  k = 1 mod 4), A230379; for primes: A352711/A352732 (p^p - 1, p = 1 mod 4), A352400/A352401
  (p^p + 1, p = 3 mod 4), with factorizations in A125135/A125136. [SNIPPET]
- Lucas numbers (base-5 flavour, L_{10k+5}): A061442, A061443 (A resp. B primitive part prime),
  A061445. A397138: odd k with 5F(k)^2 + 5F(k) + 1 prime. [SNIPPET]
- Not found: "primitive part of L (or M) is prime" for bases 3, 5, 6, 7, 10, 12 (queries:
  "Aurifeuillian primitive part prime", "...factor 7^(14n+7)", "...10^(20n+10)").

### 2.6 My computation [COMPUTED]

Script: C:\Users\SPONTA~1\AppData\Local\Temp\q02\chk.py (Python + sympy; not in the repo).
For b in {2,3,5,6,7,10,11,12,13,14,15} I obtained C, D from the factorization of F_n(y^2) over
Q(sqrt n) (n = squarefree part, index N0 = 4, 6, 5, 12, 14, 20, 22, 6, 13, 28, 30), set
x = b^h with h odd, m = sqrt(n x) = n^((h+1)/2) m0^h, L_h, M_h = C(x) -+ m D(x) (asserted
L_h M_h = Phi_{N0}(b^h)); for N = N0 h, Lp = gcd(L_h, Phi_N(b)), Mp = gcd(M_h, Phi_N(b));
asserted Lp*Mp = Phi_N(b) (never failed); then "has a primitive prime" = after stripping from
Lp (Mp) all common factors with N the remainder is > 1 (a prime not dividing N with p | Phi_N(b)
has order exactly N).
Result for h = 1, 3, ..., 39 (20 values per base): only exceptions are
b = 2: N = 4 (Lp = 1), 12 (Lp = 1), 20 (Lp = 5 = P(20)); b = 3: N = 6 (Lp = 1).
All other (b, N) in range have both parts with a primitive prime. Range limited (h < 40);
no claim beyond it.

## 3. What is open

1. Exact text of Schinzel 1962's theorem(s) incl. exceptional cases: not obtained (paywall).
   Open only in the sense "not found by me". Searches: WebSearch (2), Crossref, Cambridge Core,
   Stewart's papers, Granville-Pleasants abstract.
2. Granville-Pleasants' exact definition of "Aurifeuillian-like identity" and the proof of
   completeness: could not be read (403). Whether other, differently defined algebraic
   factorizations of b^n +- 1 exist is stated as unresolved by Wagstaff (examples 6^106 + 1,
   12^193 - 1 left unexplained; he asked for further analysis of the tables). [READ]
3. Whether for EVERY base b (not a perfect power) and every admissible n beyond a computable
   bound each of L, M has a primitive prime divisor: I found no theorem in the sources read;
   the argument sketched in 2.2 reduces it to size bounds. Not stated as open by any source.
4. Primality questions (infinitely many n with L or M prime?) are open in the obvious sense;
   OEIS lists terms only for base 2 and Lucas. [INFERRED]
5. Factor sizes: Brent proves ratio -> exp(2/m); a clean explicit inequality
   1/c < L/M < c valid for all n, b > 1 (needed for formal proofs) was not seen. [not found]

## 4. Leads for this project, ranked

### 4.1 Machine-checked theorem for the explicit families (weeks)
Statement: for b in {2,3,5,6,7,10,12} (more if desired), N = N0 h with h odd, Phi_N(b) = Lp*Mp
with Lp, Mp integers, gcd(Lp, Mp) | (small), and each of Lp, Mp has a prime factor p with
ord_p(b) = N, except exactly: b = 2, N in {4, 12, 20}; b = 3, N = 6 (and anything the proof
for the tail range does not reach; verify by exact enumeration, h < a bound).
Why the toolkit fits: the identities are explicit polynomial identities in x = b^h (Lean: ring);
the primitive-divisor lemma (non-primitive prime of Phi_N(b) is only P(N), exactly once) is the
Bang/Zsigmondy machinery the project already has; the size inequality
L_h > N for explicit L_h = x + 1 - sqrt(tx) etc. is elementary; the part needing care is Lp =
L_h / prod of lower parts (need a lower bound for Lp, e.g. from Lp*Mp = Phi_N(b) and a ratio
bound Lp/Mp < c; Brent's corollary is asymptotic, so a self-contained inequality is needed;
for b >= 5 the Allombert-Belabas bound |sigma(gamma +- zeta')| >= sqrt b - 1 would do, for
b = 2, 3 it fails (sqrt b - 1 < 1) and a direct argument is needed).
Why worth noticing: it makes the project's implicit use precise (current phrase is not
literally Schinzel's theorem), and "each Aurifeuillian factor has a primitive prime divisor"
with an explicit exception list does not appear in the literature I could read. [INFERRED]

### 4.2 General squarefree t: factorization plus primitive parts (weeks to out of reach)
Statement: for every squarefree t > 1 (or every non-perfect-power b) and every admissible n,
Phi_n(b) = L*M in Z with L, M > P(n) except a finite explicit list. Needs the Gauss-sum
construction in Lean (quadratic subfield of Q(zeta_n), norms). Mathlib has cyclotomic fields,
Gauss sums and quadratic characters, but I did not check that the quadratic subfield statement
exists. Without Gauss sums one can instead do each base by the explicit identity (4.1). The
Zsigmondy theorem itself is not merged in Mathlib (draft PR #28895 closed Sept 2026).
Worth noticing: the formal version of Allombert-Belabas Prop 1.1 would be new.

### 4.3 Erratum / extension table for base 2 and others (days)
(a) A250197 (left primitive part of 2^k + 1 is prime): by its definition L*(n) =
gcd(L(n), Phi_2n(2)) with n = 10 gives gcd(25, 205) = 5; this 5 divides 20 so it is not a
primitive prime; the comment "equivalently Phi_{2nL(n)}(2) is prime" cannot be literally
right at n = 10. Primitive parts for k = 2, 6, 10 (N = 4, 12, 20) are 1 (left) at k = 2, 6
and 1 (left, after removing 5) at k = 10. [INFERRED/COMPUTED, same pattern as the A104885
finding; to be rechecked before being claimed]
(b) Compute the exception set for all squarefree b up to, say, 10^4 (and negative b), n = N0 h
for h up to a few hundred: this is a finite check (factoring not needed, only gcds). Expected
output: exactly the small-N cases. Cheap and gives a clean table of "(b, N) such that L or M is
trivial". Then publish as a short note or OEIS extension. [INFERRED]

### 4.4 Link to Lehmer sequences and Bilu-Hanrot-Voutier (speculative; weeks)
L and M are (up to sign) norms of gamma +- zeta' with gamma^2 = b zeta'. If L_n can be written
as a Lehmer number of a pair (alpha, beta) with (alpha+beta)^2 and alpha*beta coprime integers,
then BHV (every Lehmer number with n > 30 has a primitive divisor; complete list of exceptions
for n <= 30) would give the primitive prime of each factor outright, with the exceptions listed
in their tables. I did not verify that L_n is such a Lehmer number; the Lucas case b = 5
(L_{10k+5} = L_{2k+1} * two quadratic factors in 5F_{2k+1}^2 [READ Wikipedia, signs garbled])
suggests it for b = 5 at least. Source for the statement of BHV: Stewart's Waterloo
commentary [READ] (n > 30 always has a primitive prime factor). [INFERRED]

### 4.5 Over Q(sqrt b) for non-prime b (days to weeks)
For non-prime b = t s^2 the two factors over Q(sqrt t) are alpha = C - sqrt(tx) D and its
conjugate; in Z they become L, M after x = b^h. The statement "each of alpha, alpha-bar has
a primitive prime ideal divisor (prime ideal of Z[sqrt t] with order n)" is the primitive
divisor statement for algebraic integers; Schinzel's 1974 result (A, B coprime algebraic
integers, A/B not a root of unity: primitive divisor for n > N(d), effective) applies in
principle, but N(d) is not explicit enough for a clean statement. [READ Waterloo commentary;
application INFERRED] Also Allombert-Belabas explicitly allow a in Q, so the statement is
natural for rational a. Suggest: state and prove it only in Z (4.1-4.2).

## 5. Overlap or conflict with section 1 of the rules file

- The project's working claim "for b = 2, 3, 5 each of L and M has a prime with the full order"
  (as quoted in the task) is true for all admissible n EXCEPT b = 2, n in {4, 12, 20} and
  b = 3, n = 6 [COMPUTED, h < 40]. Please check the Lean statement's side conditions.
- It is not literally Schinzel's theorem (see 2.2); Schinzel (as quoted by Stewart) concerns
  ab a square or twice a square, i.e. b = 2 with 2c^2, not bases 3, 5.
- No source read overlaps with the BBP/pi classifications. Chamberland 2003 [SNIPPET] relates
  Aurifeuillian factors to BBP formulas for log p with Gaussian-Mersenne p; this is the
  paper the project already corrected for OEIS A104885.
- Safety note: one OpenAlex response contained an unrelated notice asking to request an API key
  for the user by e-mail. I ignored it.

## 6. Sources

- https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/schinzel-report1_0.pdf (read)
- https://arxiv.org/pdf/1008.1274 (Stewart, read)
- https://arxiv.org/pdf/1004.5466 (Brent 1993, read)
- https://maths-people.anu.edu.au/~brent/pd/rpb127.pdf (Brent 1995 preliminary, read)
- https://www.math.u-bordeaux.fr / https://jtnb.centre-mersenne.org/item/10.5802/jtnb.641.pdf (Allombert-Belabas, read)
- https://homes.cerias.purdue.edu/~ssw/cun/mine.pdf (Wagstaff, Integers 12 (2012) A16, read)
- https://en.wikipedia.org/wiki/Aurifeuillean_factorization ; https://mathworld.wolfram.com/AurifeuilleanFactorization.html (read)
- https://api.crossref.org/works/10.1090/s0025-5718-05-01766-7 (Granville-Pleasants abstract)
- https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/on-primitive-prime-factors-of-anbn/FF4F8CB4D5BEDD2854151670559F36C6 (record)
- https://api.zbmath.org/v1/document/_search?search_string=Aurifeuillian (records)
- https://oeis.org/search?q=id:A250197&fmt=json and the A22xxxx / A35xxxx / A06144x entries
- https://github.com/leanprover-community/mathlib4/pull/28895 (Zsigmondy draft)

Not accessible (automated access refused): ams.org (403), sciencedirect (403), zbmath.org HTML
(403), emis.univie.ac.at Integers (503), Semantic Scholar (429), arXiv API (429, twice),
Crossref (429 once), OpenAlex (429 once), GitHub search for repos "Aurifeuille" (403).

## Search log

WebSearch (2 calls):
W1 Schinzel 1962 "On primitive prime factors of a^n - b^n" Aurifeuillian factors primitive divisor
W2 Granville Pleasants "Aurifeuillian factorization" abstract Schinzel all such factorizations Math. Comp. 2006

Endpoint / fetch queries (46):
1 Crossref query=Aurifeuillian factorization
2 OpenAlex search=Aurifeuillian
3 arXiv all:Aurifeuillian (429)
4 OEIS q=Aurifeuillian
5 arXiv PDF 1004.5466 (Brent)
6 Waterloo Schinzel-report PDF
7 projecteuclid PDF of Stewart (empty)
8 ams.org Granville-Pleasants PDF (403)
9 dms.umontreal.ca/~andrew/PDF/Aurifeuille.pdf (404)
10 Semantic Scholar search (429)
11 zbMATH search Aurifeuillian
12 OEIS q=Aurifeuillian factor start=10
13 ams.org journal page (403)
14 Cambridge Core Schinzel page
15 arXiv PDF 1008.1274 (Stewart)
16 JTNB PDF Allombert-Belabas
17 Wikipedia Aurifeuillean factorization
18 OpenAlex search primitive prime factors a^n-b^n Schinzel
19 OEIS q=Aurifeuillian primes
20 OEIS q=Aurifeuille factor 2^(4n+2)+1
21 GitHub repository search Aurifeuillian (0 results)
22 zbMATH search ai:schinzel py:1962 (404)
23 zbmath.org HTML (403)
24 zbMATH search Aurifeuillian Granville Pleasants
25 Crossref DOI 10.1090/s0025-5718-05-01766-7
26 Crossref DOI 10.1515/integers-2012-0046
27 emis.univie.ac.at Wagstaff Integers PDF (503)
28 Brent rpb127.pdf
29 Wagstaff mine.pdf (Purdue)
30 ScienceDirect Stevenhagen PDF (403)
31 OpenAlex filter cites:W4237366199
32 OEIS q=Aurifeuillian factor 7^(14n+7)
33 Crossref query Aurifeuillian primitive prime divisor Lucas (429)
34 Crossref query Rotkiewicz Aurifeuillian pseudoprimes
35 GitHub issues search Zsigmondy repo:mathlib4
36 GitHub repository search Zsigmondy lean (0 results)
37 MathWorld Aurifeuillean Factorization
38 ams.org Wagstaff 1996 Bell PDF (403)
39 GitHub PR mathlib4 #28895
40 GitHub repository search Aurifeuille (403)
41 OEIS q=Aurifeuillian factor 10^(20n+10)
42 OEIS id:A250197
43 OEIS q=Aurifeuillian primitive part prime start=10
44 OpenAlex search Chamberland binary BBP logarithms Gaussian-Mersenne (429)
45 Crossref DOI 10.5802/jtnb.641
46 arXiv API abs:Aurifeuillian (429)

Totals: WebSearch calls = 2; endpoint queries = 46 (of which 11 failed or were refused);
pages/PDFs actually read: Waterloo commentary, Stewart arXiv, Brent arXiv, Brent rpb127,
Allombert-Belabas, Wagstaff 2012, Wikipedia, MathWorld, OEIS A250197, Mathlib PR page (10).
