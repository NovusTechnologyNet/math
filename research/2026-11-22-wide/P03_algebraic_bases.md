# P03: BBP-type formulas in non-integer and algebraic bases

Helper report, 22 Nov 2026. Marking: [READ] read on the source itself (PDF text extracted locally with
pdftotext from the fetched file, or page); [SNIPPET] seen only in a record or search result;
[INFERRED] my own conclusion; [COMPUTED] my own numerical check with mpmath (40-60 digits, a
sanity check, not a proof; counts as [INFERRED] for rigor). Notation: P(s,b,N,A) as in Bailey; "Q-coefficients"
means a_i rational; "Q(beta)-coefficients" means a_i in the base field.

## 1. Summary

1. The literature on BBP-type formulas in non-integer bases is small and informal: Adegoke (golden
   ratio, 2014 and 2023 with Lafont), Chan (Machin-type, not BBP), Cloitre (pi^2 in base phi^5, found 2004,
   proved 2025), Pardeshi (OEIS, 2022 and Aug 2026), Pain (2022), Kristensen-Mathiasen (K-M, JNT 2023).
   No classification and no non-existence theorem for a non-integer base was found. [READ/SNIPPET]
2. K-M themselves say that digit extraction from their irrational-base formulas is an open problem and that
   the extra abundance of null formulas for the golden ratio is "a mystery". Adegoke-Lafont say plainly that
   their series give no digit extraction. [READ]
3. Gaussian-integer base: Borwein-Borwein-Galway (BBG 2004) Comment 9 only suggests allowing b in Z[i] and
   p,q in Z[i,k] to unify arctangents and logarithms; Comment 7 asks for an effective Zsigmondy over Q[i].
   No follow-up found (6 citing records listed, none on this). [READ]
4. NEW (my computation): there are degree-1 formulas with RATIONAL coefficients in RATIONAL NON-INTEGER
   bases: pi/4 in base (3/2)^12 = 531441/4096 and sqrt(3)*pi in base (4/3)^6 = 4096/729 (exact coefficients
   in 3.2). I found nothing like them in print. [COMPUTED]
5. The K-M abstract says integer coefficients; the formulas they display (golden ratio base, 1+sqrt3) are
   triangle formulas whose coefficient vectors are NOT rational. [COMPUTED] (e.g. base -phi^15, entries in a
   degree-4 field; base (1+sqrt3)^12, entries in Q(sqrt3) minus Q).
6. Every "single triangle" formula (K-M Theorem 1) is a formula with Q(r)-ish coefficients; with these, "pi in
   algebraic base" is cheap (e.g. arctan(1/beta)=pi/m for beta=cot(pi/m)). The honest object is the
   rational-coefficient class. [INFERRED]
7. The pi-formula structure has a clean description: value = -(1/N) sum over N-th roots of unity of
   (coefficient)*log(1 - zeta x), x^N = beta^(-B); Baker then reduces everything to multiplicative
   relations among the numbers y - zeta (y = 1/x), i.e. to prime-ideal factorization in a Kummer field.
   This is exactly the project's method; the new ingredient for quadratic beta is that primitive primes may
   be fixed by complex conjugation (p = -1 mod n), which explains the golden-ratio abundance. [INFERRED]
8. A complete list of rational-angle triangles whose side ratio r is rational or quadratic (denominators up
   to 60) has 13 values of r<1 (3.4). Rational r^2 occurs only for r^2 in {1/4,1/3,1/2,2/3,3/4}, i.e.
   bases 4, 3, 2, 3/2, 4/3. [COMPUTED]
9. Digit extraction: plausible in Gaussian/Eisenstein-type bases (a complex base whose fractional parts
   tile the plane, e.g. Penney's base -1+i), because the BBP numerators land in Z[i]/(m), a torus.
   For real quadratic beta the same argument fails (Z[beta] is dense in R). [INFERRED]
10. Best leads: (a) classify rational bases; (b) rational-coefficient question in quadratic bases;
    (c) Zsigmondy-type exclusion for Machin-type formulas in Z[phi] (Carmichael); see section 4.

## 2. What is known (with sources)

### 2.1 Golden ratio base
- Adegoke, "The golden ratio, Fibonacci numbers and BBP-type formulas", Fibonacci Quarterly 52 (2014)
  129-138 [SNIPPET: Crossref record; text not read]. K-M describe its formulas as having coefficients in
  Z[phi], "a little unnatural". [READ in K-M]
- Adegoke and Lafont, arXiv 2303.13374 (2023), "Golden ratio base expansions of the logarithm and inverse
  tangent of Fibonacci and Lucas numbers" [READ via ar5iv summary, one fetch]. In their notation
  P(1, alpha^m, N, A) with entries rational multiples of powers of beta=-1/alpha. Examples: log 2 =
  P(1,alpha^12,6,(b^2,3b^4,4b^6,3b^8,b^10,0)); log 3 = P(1,alpha^8,4,(2b^2,4b^4,2b^6,0));
  log alpha = P(1,alpha,2,(0,-b)); log 5 = P(1,alpha^4,2,(4b^2,0)); pi/4 = arctan(1/F_2) =
  P(1,alpha^12,12,(-b,0,-2b^3,0,-b^5,0,b^7,0,2b^9,0,b^11,0)); also arctan(1/4), arctan(1/sqrt5),
  arctan(1/2). They state the series do not yield digit extraction because the base alpha^n is not an
  integer. They cite Chan, "A golden example solved" (Borwein-Chamberland, undated manuscript), Zhang and K-M.
- Chan, "Machin-type formulas expressing pi in terms of phi", Fibonacci Quarterly 46/47 (2008/9) 32-37
  [SNIPPET; Pain quotes e.g. pi = 4 arctan(1/phi)+4 arctan(1/phi^3), pi = 8 arctan(1/phi^2)+4
  arctan(1/phi^6), pi = 12 arctan(1/phi^3)+4 arctan(1/phi^5)]. These are Machin-type, not BBP.
- Pain, arXiv 2205.08617 (2022) [READ]: pi = 5 * sum_k x^(4pk+1) sum_{i<2p} (-1)^i x^(2i)/(4pk+2i+1)
  with x = sqrt((3-phi)/2)-type argument [tan(pi/5) = sqrt(3-phi)... text is Gregory series for arctan at
  tan(pi/5)]; coefficients live in Q(sqrt(3-phi)). Base is a power of x^(-1). Cheap type (7 above).
- Pardeshi, OEIS A102243 (May 2022) and note "Pi in golden ratio base phi" [READ]: pi = 4/phi + sum_n
  phi^(-12n) [ 8phi^-3/(12n+3) + 4phi^-5/(12n+5) - 4phi^-7/(12n+7) - 8phi^-9/(12n+9) - 4phi^-11/(12n+11) +
  4phi^-13/(12n+13) ] (signs as I read them; garbled in extraction) from the identity pi/4 = arctan(1/phi)
  + arctan(1/phi^3). OEIS A398722 (Aug 2026, same author) [SNIPPET]: pi = sum_n b^(-12n)[2 b^-1/(12n+1) +
  10 b^-3/(12n+3) + 2 b^-5/(12n+5) - 2 b^-7/(12n+7) - 10 b^-9/(12n+9) - 2 b^-11/(12n+11)], b=sqrt(phi),
  from pi/2 = arctan(phi^-1/2) + 2 arctan(phi^-3/2). Integer numerators but weights b^-k irrational.
- Cloitre, arXiv 2508.03743 (2025) [READ]: pi^2/50 = sum_k phi^(-5k) [ phi^-2/(5k+1)^2 - phi^-1/(5k+2)^2 -
  phi^-1.../(5k+3)^2 ... ] i.e. the series T = sum_n cos(2 pi n/5) phi^(-n)/n^2 = pi^2/100, dissected mod 5
  (so base phi^5, coefficients in Z[phi]); found by lindep in Dec 2004; MathWorld cites an unpublished
  manuscript "A BBP Formula for pi^2 in Golden Base" (Cloitre, Borwein, Chamberland 2005) and Bailey et al.
  2007 p. 277. Key lemma: 1 - phi^-1 e^(2 pi i/5) = e^(-i pi/5) (pentagon). Cloitre states that a pure BBP
  formula for zeta(3) in base phi was not found (only a Machin-like polynomial identity), and calls
  extension to other polygons (octagon, sqrt2) "a challenging open question". [READ]
- Bailey's Compendium (2017 version fetched) [READ, section 13 "Curiosities", and 10]: formula (132) is a
  degree-1 formula in the irrational base (2/phi)^10 = (2phi-2)^10 with INTEGER coefficients (256, 1283, 644,
  324, 0, -86, -48, -29, -9, 0), left-hand constant garbled in my extraction (involves 5^(5/4)); formula (133)
  cos^-1(9/10)-type series with Lucas-sequence coefficients D_{k+1}=D_k-5D_{k-1} in base 10, where Bailey
  says a variant of the BBP algorithm "is possible" via exponential ladders for Lucas sequences. He calls both
  "technically not BBP-type". Credits Borwein-Chamberland [16] for (132), (133). This is the only
  rational-coefficient irrational-base formula I met in print. Sections 4 and 10-11 have only integer bases.
- MathWorld, "BBP-Type Formula" [READ]: eq. 34 (Cloitre's pi^2) called "a beautiful example in a non-integer
  base"; notes BBG 2004 excluded only Machin-type non-binary formulas for pi and that this does not rule
  out a different scheme.
- OEIS: A102243 pi in golden base (Bergman-style digits), A238897 pi in base sqrt2, A239199 pi in base sqrt3
  [SNIPPET]: these are beta-expansions of pi (numeration), unrelated to BBP.

### 2.2 Kristensen-Mathiasen, "BBP-type formulas, an elementary approach", JNT 244 (2023) 251-263,
arXiv 2208.07696 [READ completely]
- Definition: BBP(d,b,n,A) = sum_k b^-k sum_j a_j/(kn+j)^d; allow real b (their "base" is actually beta^n, see
  below). Theorem 1: for theta = (a/b)*2pi, 2 | b, r in (0,1): arg(1 + r e^(i theta)) = BBP(1, r^-b, b, A),
  A_j = r^j (-1)^(j+1) sin(j theta). Geometric meaning: triangle with vertices 0, 1, 1 + r e^(i theta); if the
  angle at 0 is a rational multiple of pi you get a formula for pi. Method of Barsky-Munoz-Perez-Marco
  (Acta Arith. 198 (2021), arXiv 1906.09629) made elementary. Algorithm: LLL on the vectors CTB_b(r,a),
  exact check that a product of (q + r e^(i theta_i))^(a_i) is real.
- Results: recovers Lafont's null formula in base 2^12; a new formula for sqrt3*pi in base 2^12 (their
  abstract writes "pi sqrt3 3"); Table 2: null formulas for Pisot bases found with b=60 (24 for x^4-x^3-1): phi: 12;
  1+sqrt3 (x^2-2x-2): 4; 1+sqrt2: 0; (3+sqrt5)/2: 1; (3+sqrt13)/2: 1... (cells garbled). Note Table 2 counts
  NULL formulas only and b=60 is not divisible by 8, so it cannot see the octagon. [READ + INFERRED]
- Displayed formulas: for phi, four null formulas (CTB60 combinations) and "pi = 10 BBP(1,15,15,CTB(1/phi,2))";
  for 1+sqrt3: null formula in "base 12" and pi = 12 BBP(1,12,12,CTB12(1/beta,2)) = 12 BBP(...,5).
  They say searching irrational bases "appears to be largely unexplored territory".
- Open problems listed by the authors (section 5) [READ]: (i) why the golden ratio has so many null formulas;
  they think it is not about Pisot-ness; (ii) it is not clear how to extract digits (beta-expansions of Renyi
  and Parry), naive spigot extension "fails miserably"; obtaining digit information remains open; (iii) only
  degree 1 handled; geometric approach to higher degree open.
- Citations of K-M in OpenAlex: only Adegoke-Lafont 2023 and Batir 2024 ("A note on some classes of series for
  the logarithmic function"); no follow-up on Pisot bases found. [SNIPPET]
- My checks of their displayed formulas [COMPUTED]: with the sign convention of Theorem 1, the golden ratio
  formula is pi = 10*BBP(1, -phi^15, 15, CTB15(1/phi, 2)) (base is -phi^15 because (-1)^(n-1) has period 2
  and N=15 is odd; with N=30 it is phi^30); error 5e-41. The 1+sqrt3 formula is exact with base beta^12.
  Entries: for 1+sqrt3 all entries lie in Q(sqrt3) \ Q; for phi^10 (pentagon triangle, A=36, C=72) every
  entry lies in sqrt(10+2sqrt5)*Q(sqrt5). So these are NOT rational-coefficient formulas, contrary to the
  abstract's "integer coefficients" and to "as is the case with integer bases". Possibly their claim concerns
  a different normalization; I could not resolve it (PDF symbols garbled).

### 2.3 Gaussian integers and Z[i]
- BBG, Canad. J. Math. 56 (2004) 897-925 [READ the PDF text, appendix D "Comments and Research Problems"].
  Their b-ary BBP formula uses integer b, p,q in Z[k]; the whole method works in Z[i] (arctangents as
  arguments of b^m - i). Comment 9: generalize to sum b^-k p(k)/q(k) with b in Z[i], p,q in Z[i,k], to treat
  arctan and log together. Comment 7: Zsigmondy has been generalized to number fields (Schinzel 1974,
  Bilu-Hanrot-Voutier 2001) and an effective version for Q[i] should give an exclusion criterion analogous
  to their Theorem 6. Comment 10: whether pi is a Q-combination of L(1,b^m,n,j) (b, n fixed) would need
  understanding of Q[zeta_n, b^(1/n)]. Comment 4 asks about Chebotarev for infinitely many p = 1 mod 4 with
  4 | order b. These are stated as open by the source. No paper answering them was found (zbMATH/Crossref
  searches on "BBP Gaussian integer base" gave only Calcut, "Gaussian integers and arctangent identities
  for pi", Monthly 2009, which concerns Machin-type identities, and Adegoke/Zhang BBP papers in integer
  bases). [READ + SNIPPET]
- Zhang, "New formulae of BBP-type with different moduli" (JMAA 2013) and Zhang-Zhang "modulo 6" (2014):
  integer bases, SNIPPET only.
- Nothing found on BBP over Eisenstein integers, sqrt(-2), (1+sqrt(-7))/2. [searches: see log]
- [INFERRED] Base beta = 1+i, sqrt(-2), sqrt(-3) has beta^m rational for small m (beta^4=-4, beta^2=-2,
  beta^2=-3), so formulas with B multiple of that m are formulas in the integer bases -4, -2, -3: for
  example Bailey's pi = P(1,-4,4,(2,2,1,0)). With B=1: sum_k (1+i)^-k/k = (log 2)/2 - i pi/4, a complex-base,
  degree-1 identity whose real and imaginary parts are the old log 2 and pi series.

### 2.4 Zsigmondy over number fields
- Schinzel (1974) and "An extension of the theorem on primitive divisors in algebraic number fields",
  Math. Ann. 1993 [SNIPPET: zbMATH record]. Bilu-Hanrot-Voutier (2001): Lucas and Lehmer sequences have a
  primitive divisor for n > 30 [SNIPPET via Wikipedia]. Carmichael (1913) for Fibonacci/Lucas [recall, not
  checked on a source]. Mathlib: only a closed draft PR #28895 "prove Zsigmondy's theorem" [SNIPPET: GitHub
  search]; the project's own formalization over Q is therefore ahead of Mathlib.

## 3. My new computations and observations

### 3.1 Reduction (the project's method, extended) [INFERRED]
Series sum_j beta^(-Bj) sum_i a_i/(Nj+i). Put x with x^N = beta^(-B), y = 1/x. Then
value = -(1/N) sum_{zeta^N=1} [ sum_i a_i (zeta x)^(-i) ] log(1 - zeta x), and 1 - zeta x = (y - zeta)/y.
Baker's theorem: Q-linear independence of logs of algebraic numbers implies Q-bar-linear independence with 1.
Hence the value is in Q-bar*pi iff the coefficient vector lies in the Q-bar-span of the multiplicative
relation lattice of {y - zeta} (mod roots of unity and powers of y). For real beta the relevant relations
are antisymmetric under zeta -> conj(zeta): prod_k ((y - zeta^k)/(y - zeta^-k))^(m_k) is a root of unity.
Ideal-theoretically: for every prime P not above N*beta, P divides at most one y - zeta (their differences
divide N), so the relation forces: for each primitive prime P dividing y - zeta^k, either m_k = 0 or
P = conj(P) (P also divides y - zeta^-k). For integer b every primitive prime of Phi_n(b) is 1 mod n,
splits completely in Q(zeta_n) and is never conjugation-fixed for n > 2: this is the mechanism behind the
classification. For quadratic beta the primitive primes of beta^n - 1 have residue degree <= 2, so p = +-1
mod n; the case p = -1 mod n has Frobenius equal to complex conjugation on Q(zeta_n), so conjugation-fixed
primes occur (compare Fibonacci/Lucas primes p = +-1 mod n, (5/p)=-1 iff p = -1 mod n for primitive
divisors). This predicts more relations (null formulas) for quadratic bases than for integer bases, and is a
plausible answer to K-M open problem (i); it is not a proof, and I did not test it against their counts.

### 3.2 Rational non-integer bases: explicit formulas [COMPUTED, 60 digits, exact rational coefficients]
(a) pi/4 = sum_{k>=0} (4096/531441)^k sum_{j=1}^{24} a_j/(24k+j), i.e. base (3/2)^12, with
a = (1/2, 1/3, 0, 0, 2/9, 8/27, 4/27, 0, 0, 16/243, 16/243, 0, -32/729, -64/2187, 0, 0, -128/6561,
-512/19683, -256/19683, 0, 0, -1024/177147, -1024/177147, 0).
Source: triangle with angles 45, 60, 75 degrees, r = sin45/sin60 = sqrt(2/3), theta = 105 degrees, N=24.
All entries of CTB24(r,7) split into the basis 1, sqrt2, sqrt3, sqrt6; the sqrt2, sqrt3, sqrt6 parts
sum to zero (null formulas) and the "1" part sums to pi/4. Genuine rational coefficients.
(b) sqrt3 * pi = 9 sum_k (729/4096)^k sum_{j=1}^{12} c_j/(12k+j), base (4/3)^6, with
c = (1/4, 3/8, 3/8, 9/32, 9/64, 0, -27/256, -81/512, -81/512, -243/2048, -243/4096, 0).
Source: triangle 30-60-90 with r = sqrt3/2, theta = 150 degrees, N = 12; entries are sqrt3 times rationals.
Neither is in the sources I read; K-M say non-integer bases are unexplored; Bailey's compendium has only
integer bases (plus the curiosities 132, 133). Whether rational bases are covered by some older reference
(e.g. the Borwein-Chamberland manuscript "A golden example solved", not retrievable) I could not check.

### 3.3 Why rational coefficients for rational bases but not for phi [INFERRED, partly COMPUTED]
For r^2 in Q the entries r^j sin(j theta) lie in a field where the irrational parts separate cleanly (above),
so a rational vector can be extracted. For the pentagon triangle every sin(36 k degrees) lies in
s*Q(sqrt5), s = sqrt(10+2 sqrt5), and r^j in Q(sqrt5); so every triangle vector at N=10 has entries in
s*Q(sqrt5), and no nonzero rational vector lies in their Q-bar span (provided the full solution space at
N=10 is spanned by triangle vectors, not checked). So at B=N=10 no rational-coefficient formula; this
suggests that rational-coefficient formulas for pi in an irrational quadratic base may not exist at all
(OPEN, not found by me in the literature; the Bailey (132) formula shows rational coefficients are possible
for some irrational base and some constant).

### 3.4 Single-triangle bases (finite list) [COMPUTED]
Rational angles A, C (denominators up to 60, A+C<180), r = sin A / sin C < 1 that is rational or quadratic
irrational (13 values; also r=1/2 etc.); each gives a formula for A (a rational multiple of pi) in base
r^-N, N = minimal even integer with theta = A + C an integer multiple of 2pi/N, coefficients CTB_N(r, a):
r=2-sqrt3 (A15,C75,N4); (sqrt5-1)/4 (18,90,N10); (sqrt3-1)/2 (15,45,N6); (3-sqrt5)/2 (18,54,N10);
sqrt2-1 (22.5,67.5,N4); 1/2 (30,90,N6); 1/sqrt3 (30,60,N4); (sqrt5-1)/2 = 1/phi (36,72,N10);
1/sqrt2 (45,90,N8); sqrt3-1 -> (sqrt3-1)... (45,75,N6) r = 0.7320508 = sqrt3-1; (1+sqrt5)/4 (54,90,N10);
sqrt(2/3) (45,60,N24); sqrt3/2 (60,90,N12). Rational r^2 only for r^2 in {1/4, 1/3, 1/2, 2/3, 3/4}.
(I did not prove that the list is complete beyond denominator 60; completeness would follow from a
Conway-Jones / Mann type classification with quadratic coefficients.) The bases generated: beta^N with
beta = 1/r; powers of these bases are of course also bases (regroup j in blocks).

### 3.5 Digit extraction heuristics [INFERRED]
BBP's trick: beta^(n-Bk) mod (Nk+i) is computed in Z[beta]/(m), so one learns S*beta^n modulo the module
Z[beta] (not modulo 1). If Z[beta] is a lattice in the space where digits live, this suffices: for a complex
base such as Penney's -1+i (digits 0,1; fractional parts fill the twindragon, a fundamental domain of Z[i])
the fractional part IS determined by the class in C/Z[i], so digit extraction of the complex value
sum (1+i)^-k/k style sums should work, by the same argument as in base 2 (note (-1+i)^4 = -4, so it is a
disguised base -4). For real quadratic beta, Z[beta] is dense in R, the class mod Z[beta] says nothing about
the beta-expansion digits of S (K-M's "fails miserably"). Possible rescue: when both conjugates of beta
have modulus > 1 the conjugate series converges too, giving a point of R^2 = K tensor R modulo the lattice;
this extracts digits of the pair (S, S') in a lattice numeration, not of S alone. Not found in print.
Bailey's remark on (133) (Lucas-sequence numerators, ladder computation) is the only digit-extraction
suggestion for a non-integer setting that I found.

## 4. What is open (precise)

O1 [stated open by K-M, 2022]: digit extraction (beta-expansion digits) from BBP-type formulas in irrational
   Pisot bases.
O2 [stated open by K-M]: why base phi has so many null formulas (they doubt Pisot-ness is the reason).
O3 [stated open by K-M]: higher-degree (s > 1) formulas in irrational bases beyond Cloitre's pi^2.
O4 [stated open by Cloitre 2025]: analogues of the pi^2 formula for other polygons (octagon, sqrt2); a pure
   BBP formula for zeta(3) in base phi (found only a Machin-like identity).
O5 [stated open by BBG 2004, Comment 7 and 9]: effective Zsigmondy for Z[i] and a Gaussian-base BBP
   framework; classification statements for Machin-type formulas in Z[i]-bases.
O6 [not found by me; my question]: any non-existence theorem for BBP-type formulas for pi in a non-integer
   base. None in print (searches: arXiv/OpenAlex/zbMATH/Crossref, see log; several endpoints were rate
   limited, so "not found" is moderate evidence).
O7 [my question]: do rational-coefficient degree-1 formulas for pi exist in an irrational real quadratic
   base? (K-M claim yes; my computation says their displayed ones are not; see 2.2, 3.3.)

## 5. Leads for this project (ranked)

L1. Rational bases (days to 2 weeks). Statement to prove: for coprime p > q >= 1 with p/q not an integer,
    a nonzero algebraic multiple of pi has a degree-1 formula with rational coefficients in some base
    (p/q)^B iff p/q is a power of 3/2 or of 4/3 (and for p/q integer the known powers of 2 and 3). Evidence:
    formulas 3.2(a), 3.2(b), and the finite triangle list 3.4 (only r^2 in {1/4,1/3,1/2,2/3,3/4}). Tools:
    this is the project's integer-base argument with b replaced by p/q: Kummer field Q(zeta_N, (p/q)^(1/N)),
    primitive prime divisors of p^n - q^n (Zsigmondy for a^n - b^n, exceptions n=2 with p+q a power of 2
    and (2,1) n=6), prime ideals above p and q as extra S-primes, plus Baker. Missing: nothing new in
    kind, but the case q > 1 introduces valuations at primes above q (they appear with the same sign in all
    y - zeta, so they cancel in antisymmetric combinations; needs a check). Then the following also
    classify 3.2(a)-(b) as "formal theorems": formal verification of the two identities by exact algebra
    (sin/cos of 15-degree multiples) is easy. Worth noticing: a "non-integer base" BBP-type pair of formulas
    with rational coefficients that nobody listed, and a classification theorem with the same shape as the
    integer-base "iff power of 2".
L2. Quadratic bases, rational-coefficient question O7 (1-3 weeks, computational). For beta = phi,
    1+sqrt2, 1+sqrt3, 2+sqrt3, sqrt(2)+1... and B*N up to about 60, compute the Q-dimension of {a in Q^N:
    P(1,beta^B,N,a) in Q-bar pi}: via exact multiplicative relations among y - zeta (numerical LLL on log
    absolute values at all embeddings of K = Q(beta, zeta_N, y), then exact check; K has degree up to 4N;
    N <= 30 is feasible on the 24-core machine). Expected outcome by 3.3: dimension 0 for phi at N=10,
    perhaps positive in other cases (cf. Bailey 132). Either answer is publishable as a short note and
    answers K-M's question on "integer coefficients".
L3. Golden-ratio Machin-type exclusion (weeks). Analogue of BBG Theorem for the generators arctan(1/phi^m)
    = arg(phi^m + i) in Z[phi, i]: show only finitely many m give Q-linear Machin-type formulas. Norms of
    phi^n - 1 are -L_n (n odd) and L_n - 2 (n even), so Carmichael's theorem (every Lucas number L_n, n not
    in {1,3,6}, and every F_n, n not in {1,2,6,12}, has a primitive prime divisor) is the Bang theorem
    needed; BHV 2001 covers all Lucas/Lehmer sequences. Missing in the project: a formal Carmichael/BHV
    statement (or a Zsigmondy over Z[phi]); Mathlib has none. Worth noticing: first non-integer analogue of
    the BBG exclusion theorem; explains Chan's finite list.
L4. Single-triangle classification for quadratic bases (days): prove the list 3.4 complete (Conway-Jones /
    Mann with quadratic coefficients; or a computer-algebra check using the degree bound), giving a
    theorem "r = sin A / sin C quadratic or rational iff ...", and thereby all K-M style formulas obtainable
    from one triangle. Small, but it would give a clean citeable table and corrects/clarifies K-M.
L5. Gaussian / Eisenstein bases (weeks). Statement: for beta in Z[i] or Z[omega] not a root of unity,
    pi (algebraic multiple) has a formula sum beta^(-Bj) sum a_i/(Nj+i), a_i in Q(i) (complex values; real
    parts), iff beta^m is rational for some m (i.e. beta/conj(beta) is a root of unity: beta = unit times
    integer times (1+i) or sqrt(-3), sqrt(-2)... as appropriate). The "if" is Section 2.3; the "only if" needs
    Zsigmondy over Q[i] (effective) which is BBG Comment 7; for the half-line of fields with class number
    one (Z[i], Z[omega], Z[sqrt-2], Z[(1+sqrt-7)/2]) the ideal arithmetic is simple. Missing: Zsigmondy over
    imaginary quadratic fields in Lean (Schinzel's theorem with effective bound is heavy; but for rank-one
    unit group, one can use Q-Zsigmondy applied to the norm N(beta^n - 1) = Phi-type integer, if the
    sequence |beta^n|^2-type quantities are Lucas sequences: beta^n - conj(beta)^n quotient version; BHV
    applies). Worth noticing: answers the Comment 9 direction of BBG.
L6. Digit extraction in a complex base (weeks, mostly algorithmic): implement BBP digit extraction for a
    base -1+i / (1+i) formula via Z[i]/(m) arithmetic and verify digits of the complex number
    (log 2)/2 - i pi/4 in the twindragon system. Not a theorem, but an actual demonstration of "digit
    extraction in a non-integer base", which O1 says nobody has done.
L7. Out of reach / long: classification of all rational-coefficient degree-1 formulas in a quadratic base for
    all (B, N), including the "mystery" of the golden ratio; needs L2 plus a size bound on N (a lower bound
    for norms of y - zeta via Baker), and handling primes above N (the wild primes).

## 6. Overlap or conflict with the project's results (section 1 of the rules)

- No conflict with "Every integer base: a formula exists iff |b| is a power of 2": the rational bases 3/2
  and 4/3 in 3.2 are not integers. But note the neighboring statement in the rules: "In print this is stated
  as known (Bailey's Compendium, citing BBG 2004), but that paper proves only the Machin-type case". I
  confirm from BBG's text that the exclusion proved there is for Machin-type generators (their Theorem 6
  and the closing Comment 11 questions whether Machin-type generators capture everything). [READ]
- The project's base-3 result (only rational multiples of pi*sqrt3) is consistent with my 30-60-90
  computation (r = 1/sqrt3 gives sqrt3*pi). [COMPUTED]
- K-M's claim of integer coefficients in irrational Pisot bases is at odds with my numerical check
  (2.2). This does not affect the project's integer-base theorems.
- K-M's Table 2 counts only null formulas, and uses b=60 (octagon invisible). [READ]
- Possible naming trap: Bailey's P(s,b,n,A) with irrational b appears in his Compendium (132) as a
  "curiosity", so a claim "no BBP-type formula in a non-integer base is known" would be false.

## 7. Sources
- arXiv 2208.07696 (Kristensen-Mathiasen) https://arxiv.org/pdf/2208.07696 (JNT 244 (2023), doi
  10.1016/j.jnt.2022.09.001); arXiv 1906.09629 (Barsky-Munoz-Perez-Marco, read only the first page);
  arXiv 2508.03743 (Cloitre); arXiv 2205.08617 (Pain); arXiv 2303.13374 (Adegoke-Lafont, via ar5iv);
  Bailey compendium https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf; BBG 2004 doi
  10.4153/CJM-2004-041-2 (Cambridge PDF); MathWorld https://mathworld.wolfram.com/BBP-TypeFormula.html;
  OEIS A102243, A398722, A238897, A239199; Pardeshi note https://oeis.org/A000796/a000796.pdf;
  Wikipedia pages (BBP formula, Zsigmondy); zbMATH Open records; Crossref records; GitHub mathlib4 PR 28895.

## 8. Search log

WebSearch (2 calls, of the 6 allowed): W1 "BBP-type formulas an elementary approach Kristensen Mathiasen Pisot
base"; W2 "BBP formula golden ratio base digit extraction pi phi-nary".

Endpoint queries (through the fetch tool; E = rate limited or empty, noted):
1 arXiv API BBP+Pisot (HTTP 429); 2 arXiv API BBP+golden ratio (429); 3 arXiv API BBP+Gaussian integers (0 hits);
4 OpenAlex "BBP-type formulas elementary approach"; 5 arXiv PDF 2208.07696 (read via pdftotext);
6 arXiv PDF 1906.09629; 7 arXiv PDF 2508.03743; 8 arXiv PDF 2205.08617; 9 Crossref BBP Gaussian base (429);
10 Crossref BBG title; 11 Crossref Adegoke golden ratio; 12 Semantic Scholar API non-integer base (429);
13 OpenAlex Machin golden Chan; 14 zbMATH BBP golden ratio; 15 ar5iv 2303.13374; 16 Bailey compendium PDF;
17 MathWorld BBP-type formula; 18 CECM P213 (wrong paper); 19 CECM BBGal (404); 20 OpenAlex BBG;
21 Semantic Scholar web (403); 22 Cambridge BBG PDF (read via pdftotext); 23 OpenAlex "BBP digit extraction
beta-expansion Pisot" (0 hits); 24 OpenAlex "BBP Gaussian integer base complex base"; 25 OpenAlex cites K-M;
26 OpenAlex cites BBG (22 works); 27 OpenAlex cites Barsky et al. (6 works); 28 OpenAlex digit extraction
non-integer base; 29-34 six OpenAlex queries (Schinzel, Zsigmondy number fields, Calcut, Zhang, Chamberland,
normal numbers Pisot) all HTTP 429 (shared rate limit, Retry-After about 19 h); 35 zbMATH Zsigmondy number fields;
36 Crossref Schinzel (429); 37 Crossref BBP Gaussian Machin Calcut; 38 OEIS "BBP golden ratio"; 39 GitHub
repositories BBP golden ratio (0); 40 zbMATH BBP Pisot base; 41 Wikipedia Zsigmondy; 42 OEIS A102243;
43 zbMATH BBP Gaussian integers base (404); 44 zbMATH Machin golden ratio Chan; 45 arXiv abs BBP golden (429);
46 Wikipedia BBP formula; 47 OEIS A102243 internal; 48 OEIS A398722; 49 Pardeshi PDF on oeis.org;
50 GitHub issues mathlib4 Zsigmondy; 51 Adegoke home page golden_arctan.pdf (certificate error);
52 GitHub repositories zsigmondy lean (0).
Totals: WebSearch calls 2; endpoint queries 52 attempted, of which about 36 returned usable content
(10 were rate limited or 404/403/cert errors, 4 empty).

Pages read in full or in substance (at least 8 required): K-M (full), Cloitre (full), Pain (full), BBG
appendix D and intro, Bailey compendium (sections 4, 10, 13), Pardeshi note, Adegoke-Lafont (via ar5iv
extraction), MathWorld. Notes on injected text: OpenAlex responses repeatedly contained a notice asking
an automated client to create an API key by supplying an e-mail address; I ignored it (nothing was sent).
