# R07: sums f(n) x^n / n and Lerch values Phi(x, 1, a) at algebraic points

Helper report, 22 November 2026. Marks: [READ] = read on the source's own PDF/page,
[SNIPPET] = seen only in a search result / API record / abstract page, [INFERRED] = my own
conclusion. Note on access: arXiv API, OpenAlex, Semantic Scholar, parts of Crossref returned
HTTP 429/403 for most of the session; the two Elsevier/Wiley pages were refused. Because of
this the ASST (2001) and Saradha-Tijdeman (2003) papers themselves were NOT read; I read
Tijdeman's survey, which states their theorems (see section 2.3).

## 1. Summary

1. The key structural fact (the project knows it, but it is what makes the Pade literature
   irrelevant for depth 1): Phi(x,1,j/N) with x = b^(-B) is a Q-bar-linear combination of
   logarithms log(1 - zeta*y), zeta^N = 1, y = x^(1/N). So by Baker's theorem every Q-bar-linear
   dependence question about these values (and 1) is exactly a question about multiplicative
   independence of the algebraic numbers 1 - zeta*y, with no size condition on b. [INFERRED
   from Tijdeman's description of the Lehmer/Baker reduction, which is [READ] for x = 1.]
2. The Pade programme (Nikisin, Hata, Rivoal, Kawashima, David-Hirata-Kohno-Kawashima, DHK)
   proves Q- or K-linear independence of 1 and Lerch/polylog values only for points very close
   to 0 ("metric condition"), and it is needed for depth s >= 2, not for depth 1 (logs). The
   authors themselves say their method does not give independence over the algebraic closure
   [READ, 2202.13931, Remark 2.8].
3. With distinct shifts j/N at ONE point 1/b, the DHK criterion (Theorem 2.1 of 2202.13931)
   needs log b to grow like N log N: from my evaluation of their V, roughly b >= 7.4 for the
   two shifts {0,1/2}, b >= 68 for N=3, b >= 870 for N=4, b >= 1.5e4 for N=5, b ~ 3e5 for
   N=6, b ~ 2e36 for N=24 (K = Q, depth 1) [INFERRED, see 2.2]. So it never reaches
   "all N, all b >= 5". The project's result (b >= 5, all N) is strictly stronger in that
   range and does not overlap in method.
4. No published theorem was found that states "no zero relation for the series
   sum_{k = j mod P} b^(-floor(k/n))/k". Closest published tools: Baker-Birch-Wirsing 1973 and
   Okada 1982 (the case "x = 1", periodic f, classification of vanishing), and
   Adhikari-Saradha-Shorey-Tijdeman 2001, Theorem 4, which (as reported by Tijdeman) covers
   sums alpha^n P(n)/Q(n) with alpha algebraic: such a sum is 0 or transcendental (see 2.3 for
   the precise reading and a caveat).
5. Missing in print (not found): an Okada-type CRITERION for when sum f(k) alpha^k/k vanishes,
   for algebraic alpha != 1. That is precisely the project's "zero relations" question for
   x = 1/b^B. This is the most natural thing to state as a theorem in a paper.
6. Euler-Lehmer constants: Lehmer 1975 gives the closed form via logs of 1 - zeta; Murty-
   Saradha 2010: among gamma and psi(r/q) (gcd(r,q)=1), at most one is algebraic; extended by
   Chatterjee-Gun to all q at once [READ abstract-level on ar5iv]. All of this is the x = 1
   (b = 1) analogue; no analogue with geometric weights was found.

## 2. What is known

### 2.1 The Pade/Lerch line (independence of values, G-function type)

- [READ, 1912.03811] Lerch function Phi_s(x,z) = sum_{k>=0} z^(k+1)/(k+x+1)^s, 0 <= x < 1
  rational. Theorem 2.1 (David, Hirata-Kohno, Kawashima, 2020, Moscow J. Comb. Number Theory
  9): for pairwise distinct algebraic alpha_1..alpha_m in a number field K, beta in K with
  max|alpha_i| < |beta| at a fixed place v0 and an explicit inequality V(alpha, beta, x) > 0,
  the rm+1 numbers 1, Phi_s(x, alpha_j/beta) are linearly independent over K. FIXED shift x,
  varying points. Condition V depends on denominators of alpha, beta, den(x), the factor
  mu(x) = den(x) * prod_{q | den(x)} q^(1/(q-1)), and the field degree. The intro says
  explicitly that it is the first criterion for distinct algebraic points of arbitrary degree.
- [READ, 1912.03811 intro] History they cite: Nikisin 1979 (polylogs at one rational point);
  Kawashima (Lerch, one point); Hirose-Kawashima-Sato (algebraic points); Hata 1990
  (J. Math. Pures Appl. 69, linear independence of Li_s(alpha) and Lerch values at one rational
  point); Hata 1993 (Li_2(1/q) irrational for integer q >= 7 or q <= -5); Rhin-Viola 2005
  (Li_2(1/q), q >= 6); Viola-Zudilin 2018 (1, Li_1(1/q), Li_2(1/q), Li_2(1/(1-q)) independent
  over Q for integer q >= 9 or q <= -8); Rhin-Toffin 1986 (logs of rational/imaginary
  quadratic numbers very close to 0). Galochkin, Vaananen, Flicker, Chudnovsky give criteria
  for G-functions that, as they point out, fail to cover N = 1 with fields of degree >= 3.
- [READ, 2202.13931] David-Hirata-Kohno-Kawashima, "Linear independence criteria for
  generalized polylogarithms with distinct shifts" (arXiv 2022; ~Kyoto/Osaka series). Theorem
  2.1: for distinct shifts x_1..x_d in [0,1), depths r_j, distinct algebraic points
  alpha_i/beta (i = 1..m), if V(alpha, x, beta) > 0 then 1 and all Phi_{s_j}(x_j, alpha_i/beta)
  are linearly independent over K. V = log|beta| - m h(alpha,beta) - m log||alpha|| +
  m log||(alpha,beta)|| - sum_j r_j log mu(x_j) - m log 2 + rho log(m+1) +
  m log((m+1)/m) - max_j(r_j) * (max den x_j)^m (rho = sum r_j). [my transcription of a
  garbled text layer; the exponent/product at the end I read as max_j(r_j) * b^m with
  b = max den(x_j); for m = 1 it is just b]. Corollary 2.4: infinitely many beta in any K work.
  Theorem 2.6 / Corollary 2.7 cover periodic coefficients (b(z) = prod (z^q - alpha_i^q)); there
  the point set is {alpha_i * zeta_q^l}, so K must contain roots of unity and the degree of
  K enters V. Remark 2.8: "linear independence over some larger but specific fields" is
  reachable, but the methods do not give linear independence over the algebraic closure, nor
  transcendence. Section 6 example: with p shifts k/p, depth 10, and algebraic beta of degree g
  the thresholds on log(beta) are in the thousands (e.g. 3158 for g=2, p=2, q=1); this is
  much larger than for depth 1 because rho = 10p.
  Also stated: Hata treated the single rational point with distinct shifts; Zudilin showed
  Phi_1..Phi_r algebraically independent over C(z); the Pade method needs |z| small.
- [READ, 2202.13931 intro] They list Rivoal, Marcovecchio, Fischler, Fischler-Sprang-Zudilin,
  Lai-Yu and Nishimoto as results on dimension lower bounds for spans of zeta/L-values and say
  that, because their z must be near 0, their method does not directly give anything for
  zeta or Dirichlet L-values (z = 1).
- [READ, Tsukuba J. Math. 38 (2014) 171-188] Kawashima: Nikisin's result extended to
  Lerch: Theorem 0.2: x positive rational, z = a'/b' NEGATIVE rational with explicit size
  inequality (b'^(s-1) < |a'| * exp(...)) implies dim_Q of span of F_1(x,1/z)..F_s(x,1/z)
  with 1 is >= s+1. Positive points 1/b are therefore not covered; fixed shift x again. Notes
  a gap in Nikisin's original proof (corrected condition). Says Hata computed such dimensions
  by a different method (Hata 1990, Theorem 2.1; I could not read it).
- [SNIPPET] Hirata-Kohno, Muroi, Washio (arXiv 2406.10820): effective approximation measures
  for the shifted logarithm (1+x) Phi_1(x, 1/beta) at algebraic beta, |beta| > 1; built on
  Kawashima-Poels Pade approximants (J. Number Theory 2023, DOI 10.1016/j.jnt.2022.05.009,
  title: Pade approximation for a class of hypergeometric functions and parametric geometry
  of numbers). Smallest irrationality exponent bound in their table ~2.064 (a Gaussian-
  integer example). They remark that the DHK linear independence results lack asymptotic
  estimates so are weaker.
- [SNIPPET] Rivoal 2009 (Canad. J. Math. 61, "Simultaneous polynomial approximations of the
  Lerch function"); Ulanskii 2009 (Moscow Univ. Math. Bull. 64, 70-72, "Linear independence
  of values of Lerch functions", uses Nesterenko's criterion; not read); Nesterenko 1985
  criterion.
- [SNIPPET] Nishimoto: only appears as a name in the DHK introductions (dimension bounds for
  zeta/L spans); I found no record of the paper in Crossref/search.

### 2.2 What the Pade results reach for x = 1/b, shifts j/N (my evaluation)

[INFERRED] Take K = Q, m = 1, alpha = 1, beta = b, depth r = 1, all N shifts j/N (j = 0..N-1)
in DHK 2202.13931 Theorem 2.1. Then h(1,b) = log b and V = log b - sum_j log mu(j/N) +
N log 2 - N (the m-terms cancel). Setting V > 0 gives:

    N :   1     2     3     4      5       6       8       12      24      60
    b >= 1.4   7.4    68    870   1.5e4   2.9e5   2e8     3.5e14  2e36    5e114

(N = 1 is the trivial statement that log(1 - 1/b) is irrational for b >= 2.) So
log b ~ N log N + O(N): the threshold is superexponential in N, and for fixed N = 2 gives
b >= 8 (the project's b >= 5 result for n = 2 is stronger and for all n). Caveat: the
transcription of V from the PDF text layer is not fully reliable (the last term), so treat
the numbers as an order-of-magnitude statement; with periodic coefficients of period P the
field degree enters and the thresholds get worse. It is a statement about K-linear
independence of {1, Phi(1/b,1,j/N)}, it does not by itself describe relations with algebraic
coefficients (see 2.4).

### 2.3 Sums of f(n)/Q(n) and with algebraic alpha: Baker-method line

- [READ, Tijdeman survey, pub.math.leidenuniv.nl/~tijdemanr/tijsho3.pdf] Procedure: for Q with
  simple rational zeros, partial fractions give sums sum_n c_mu/(k_mu n + r_mu); Lehmer's
  formula (ASST Lemma 5) expresses such a convergent combination as a combination, with
  algebraic coefficients, of logs of 1 - (k-th root of unity); then Baker's theorem (a Q-bar-
  linear combination of logs of algebraic numbers is 0 or transcendental).
  Theorem 1 (ASST, Theorem 4 and Corollary 4.1, as printed in the survey): P, Q in Q[x],
  alpha algebraic, Q with simple rational zeros only, S := sum_{n>=1} alpha^n P(n)/Q(n)
  convergent. Then S is rational or transcendental [the printed symbols for the field are
  garbled in my text layer; I read the conclusion as "S in Q or S not algebraic"]; if all
  zeros of Q lie in [-1,0) then S = 0 or S transcendental. For alpha != 1 the survey says the
  formula is "slightly more complicated (proof of Theorem 4 of ASST)". I did NOT read ASST;
  [SNIPPET, Yuan-Li] confirms ASST proved: for periodic f with reduced Q, the sum is 0 or
  transcendental.
- [READ, same survey] Saradha-Tijdeman 2003 (J. London Math. Soc. 67, 580-592), Theorem 2:
  S = sum_{n>=0} (a n + b)/((q n + s_1)(q n + s_2)(q n + s_3)) with s_i distinct integers
  not all congruent mod q (plus the side condition) is transcendental; degree-3 classified
  completely via Okada's criterion. Degree 4: Yuan-Li (arXiv 0909.2387 [READ intro]) give
  necessary and sufficient conditions when q-th cyclotomic polynomial is irreducible over the
  coefficient field; the example sum (16n^2+12n-1)/((4n+1)(4n+2)(4n+3)(4n+4)) = 0 shows
  vanishing does happen for degree 4. Degree 2: transcendental iff s_1 not = s_2 mod q.
- [READ, Yuan-Li intro] Baker-Birch-Wirsing 1973 (S = sum f(n)/n != 0 for rational periodic
  f with f(r) = 0 when 1 < gcd(r,q) < q and Phi_q irreducible over Q(f(1..q)); also shown
  false if either hypothesis is dropped); Okada 1982 (complete description of vanishing
  for the Phi_q-irreducible case, using Baker and L(1,chi) != 0); ASST 2001 (S = 0 or
  transcendental).
- [READ, Tijdeman survey] Open items stated: Conjecture: for a rational function f the sum
  over n >= 0 of f(n), if algebraic, is rational (known for simple rational poles by the
  above); "I do not know any case where S is irrational and algebraic"; "It is an open problem
  to obtain new transcendence results using the theory of G-functions" (hypergeometric
  1+1F_m with ratio tending to a constant; related to Beukers-Wolfart).
- [READ] Okada-type linear independence: Gun-Murty-Saha (arXiv 1604.02896) prove Q-bar
  independence of the relevant log p and L(1,chi) values (their Theorems 12, 13; Theorem 13
  due to Gun-Saha-Sinha) - proof reduces to logs of cyclotomic and Ramachandra units. They
  contain no geometric weights x^n.
- [SNIPPET] Chatterjee-Dhillon (Canad. Math. Bull. 63 (2020) 31-45): new proof of Livingston's
  conjecture (logs of sine values at rationals independent over Q-bar after a coprimality
  condition; Pathak 2017 disproved the unrestricted version); identification of a maximal
  independent subset. This is the x = 1 analogue of "which multiplicative relations exist
  among the 1 - zeta*y": relations exist (cyclotomic) so the rank is < number of terms.

### 2.4 Why depth 1 is a multiplicative-rank problem (the bridge to the project)

[INFERRED, standard] For x = y^N, |y| < 1, and 0 <= j < N:
sum_{n>=0} x^n/(n + j/N) = N y^(-j) sum_{m = j mod N} y^m/m
= -y^(-j) sum_{zeta^N = 1} zeta^(-j) log(1 - zeta y)   (principal logs).
The matrix (zeta^(-j)) is invertible over Q-bar. Hence span_{Q-bar}{1, Phi(x,1,j/N)} equals
span_{Q-bar}{1, log(1 - zeta y)} when y^(-j) is algebraic (it is). By Baker, 1 and
log(1 - zeta y) are Q-bar-independent iff the logs are Q-independent. So: dimension of the
Q-bar-span = 1 + rank (modulo roots of unity, with care for the branch: relation product = 1
versus product = exp(2 pi i k) in principal branch) of the group generated by the numbers
1 - zeta y. The Pade method (Remark 2.8 above) cannot supply this because it works over
K, not the algebraic closure; Baker does it without size condition. The same holds with
periodic coefficients in k (extra roots of unity zeta in the formulas, as in the project's
classes sum_{k = j mod P}).

## 3. What is open (stated by sources / not found)

1. [stated by Tijdeman survey, READ] Algebraic irrational values of sums of rational functions:
   conjecture that an algebraic S is rational for any rational function f (open beyond simple
   rational poles); G-function transcendence results (hypergeometric, ratio tending to a
   constant) open as a method.
2. [stated, READ DHK 2202.13931 Remark 2.8] Independence over the algebraic closure and
   transcendence cannot be reached by the Pade method; only K-linear independence for points
   close to 0.
3. [stated, SNIPPET Murty-Saradha / Chatterjee-Gun] gamma and all psi(r/q) conjecturally
   transcendental; only "at most one algebraic" known. (Gun-Murty-Saha: even irrationality of
   Euler's constant open.)
4. [not found; marked as my search negative] A published Okada-type criterion for
   sum_{k} f(k) alpha^k / k (alpha algebraic, 0 < |alpha| < 1) saying exactly when it is 0,
   and a published statement that for alpha = 1/b, b >= 5 (or b large) no non-trivial
   combination of the sums over residue classes with weights b^(-floor(k/n)) vanishes.
   Searched: Crossref/OEIS/arXiv-mirror queries "Okada", "geometric weights", "Lerch
   Baker", "BBP linear independence", plus 2 WebSearch calls; found nothing. Weak
   evidence, since the relevant journals' full texts were mostly unreachable.
5. [stated, SNIPPET] Hata, Rhin-Viola, Viola-Zudilin line: irrationality of Li_2 at
   1/q for small q (q = 2..5 open or conditional) - not relevant to depth 1 but shows the
   size conditions for depth >= 2 are far from sharp.

## 4. Leads for this project (ranked)

1. **Okada-type criterion for geometric weights (publishable framing).**
   Statement: for algebraic y, |y|<1, and the N points zeta*y, the Q-bar-dimension of
   span{1, Phi(y^N,1,j/N)} equals 1 + rank of <1 - zeta y>; plus for the project's classes
   (base b, step n, period P), the dimension of the space of formulas equals the number of
   non-torsion independent factors, and every zero relation is "visible" in the factorisation
   of 1 - zeta*b^(-1/n) into primes. Fit: Baker (already formal), prime ideals in Kummer/
   cyclotomic extensions (already used), Lean. Size: days to a week for a statement
   plus proof sketch for all b >= 5 (the project has the main arguments); formalising the
   general-N rank equals N when b is not a perfect power and b >= 5 is perhaps weeks.
   Noticed because: published Okada/BBW classify only x = 1 and ASST proves only 0-or-
   transcendental; a classification for x = 1/b^B (including the b = 2, 3, 4 and perfect-
   power exceptional cases) would fill the gap. [INFERRED]
2. **Settle "no zero relation" for all steps n and all b >= 5.** Statement: for every integer
   b >= 5, n >= 1, P >= 1, the P*n distinct series sum_{k = j mod P} b^(-floor(k/n))/k
   (j mod P) and 1 have no non-trivial Q-bar-relation unless forced by the sum of residues
   identity (e.g. sum over all j equals the full series). The numerical searches
   (bases 5..12, n <= 6) say yes; the proof is the multiplicative independence of
   {1 - zeta b^(-1/n)} over roots of unity of order dividing nP, which should follow from
   primitive prime divisors of b^k - 1 (Bang-Zsigmondy) combined with Kummer theory when
   b is not a perfect power; the exceptional perfect-power bases (b = 8 = 2^3, 9, 16 etc.) need
   a separate analysis as y rational or lower-degree. Size: days (case b not an r-th power)
   to weeks; the computation already done is the sanity check.
3. **Show Pade-type theorems are strictly weaker here (sharpness remark).** Statement: for
   x = 1/b and all N, the DHK thresholds grow like log b ~ N log N (table above) while the
   true answer is "all b >= 5 (and all b except small exceptions)". Cheap to include
   in an introduction: a few lines; value: it pre-empts the question "is this not already
   known from the Lerch literature?". Size: hours, after confirming the constants against the
   published formula (I could not extract the last term of V exactly).
4. **Prime-ideal proof of an unconditional dimension formula for y of larger degree.**
   Possibly a theorem for arbitrary algebraic y with a "Mahler measure/heights" condition
   (like |y| < 1/(some function of degree)): the multiplicative independence of
   1 - zeta y follows from a prime ideal dividing 1 - zeta y but not the other conjugates.
   Size: weeks; uncertain.
5. **Euler-Lehmer analogue with geometric weights.** Define gamma_b(r, q) =
   sum over residue classes of b^(-floor(k/n))/k - (limit constant); Lehmer-type closed
   forms exist for x = 1; with weights the sums are pure logs (no gamma-like constant as the
   series converges absolutely). So this is just lead 1. Not independent.

## 5. Overlap or conflict with the results in section 1 of the rules file

- No conflict found. DHK 2202.13931 and 1912.03811 do not claim anything about vanishing of
  BBP-type combinations; their hypotheses (points close to 0, thresholds growing with the
  number of shifts and degree) leave the project's "b >= 5, all N, no size condition"
  statement untouched. Nothing in print found that states the project's base >= 5 theorem.
- Partial overlap in philosophy: ASST Theorem 4 (as reported by Tijdeman: algebraic alpha,
  rational simple poles) already gives "0 or transcendental" for each single sum, so the new
  content of the project is the decision of the zero case (the lattice structure), as with
  Okada 1982 for x = 1. The first sentences of the project description ("explains the zero-
  relation counts in Bailey's Compendium") sit exactly in this gap.
- The project's "no degree-1 formula for any algebraic multiple of pi in base b >= 5" is
  consistent with the line [READ, Tijdeman survey]: for x = 1, Baker + L(1,chi) != 0 (Okada)
  decide everything; nothing for x = 1/b was found.

## 6. Sources

- https://arxiv.org/pdf/1912.03811 (DHK 2020) [READ]
- https://arxiv.org/pdf/2202.13931.pdf (DHK 2022, distinct shifts) [READ]
- https://ar5iv.labs.arxiv.org/html/2010.09167 (DHK, Linear forms in polylogarithms) [READ partly]
- https://arxiv.org/html/2406.10820v2 (Hirata-Kohno, Muroi, Washio) [SNIPPET-level read]
- https://tsukuba.repo.nii.ac.jp/record/53608/files/tkbjm038-02-171.pdf (Kawashima 2014) [READ]
- https://pub.math.leidenuniv.nl/~tijdemanr//tijsho3.pdf (Tijdeman survey) [READ]
- https://arxiv.org/pdf/0909.2387 (Yuan-Li) [READ intro]
- https://ar5iv.labs.arxiv.org/html/1604.02896 (Gun-Murty-Saha) [READ abstract + theorems 12, 13]
- https://ar5iv.labs.arxiv.org/html/1308.6451 (Chatterjee-Gun, digamma) [READ]
- https://arxiv.org/pdf/1303.1856 (Lagarias survey on Euler's constant), only the first part
- Crossref records: ASST 10.1016/s0019-3577(01)80001-x; Saradha-Tijdeman
  10.1112/s0024610702003988; Murty-Saradha 10.1016/j.jnt.2010.07.004; Lehmer
  10.4064/aa-27-1-125-142; Chatterjee-Dhillon 10.4153/s0008439519000468; Pathak
  10.4153/cmb-2016-065-1; Rivoal 10.4153/cjm-2009-063-6; Ulanskii 10.3103/s0027132209020065;
  Kawashima-Poels 10.1016/j.jnt.2022.05.009; Gun-Saha-Sinha 10.1016/j.jnt.2014.06.010.
- Web page text (WebSearch results) contained no instructions addressed to me.

## 7. Search log

WebSearch (5 calls):
1. Lerch independence algebraic points Pade Kawashima Poels Hirata-Kohno
2. Saradha Tijdeman transcendence of infinite sums of rational functions theorem
3. arXiv Euler-Lehmer constants transcendence residue classes Baker digamma
4. Hata Lerch transcendent irrationality linear independence Phi(1/q,1,a)
5. transcendence of sum x^n P(n)/Q(n) algebraic x Baker 1-zeta alpha Okada generalization

Endpoint / fetch queries (46; the counts include refused or rate-limited ones, marked):
1 arXiv API Lerch + linear independence (429)
2 arXiv API ti:"linear forms in polylogarithms" (429)
3 OpenAlex ASST (429)
4 OpenAlex Euler-Lehmer transcendence (429)
5 arXiv PDF 1912.03811
6 arXiv PDF 2202.13931
7 Crossref "transcendental infinite sums rational functions"
8 Semantic Scholar Euler-Lehmer constants (429)
9 zbMATH API "Lerch linear independence"
10 Crossref "Lerch transcendent linear independence irrationality"
11 Crossref "Euler-Lehmer constants Murty Saradha"
12 zbMATH web Saradha Tijdeman (403)
13 OEIS "Lerch transcendent"
14 Crossref Hata dilogarithm Lerch (429)
15 ScienceDirect Murty-Saradha (403)
16 Crossref DOI Murty-Saradha (429)
17 Crossref DOI ASST
18 Crossref DOI Saradha-Tijdeman
19 ScienceDirect ASST PDF (403)
20 core.ac.uk search (403)
21 doi.org Saradha-Tijdeman (redirect)
22 Semantic Scholar web ASST (403)
23 Tijdeman survey PDF
24 arXiv PDF 0909.2387
25 Murty-Saradha PDF at Queen's (redirect)
26 Wiley Saradha-Tijdeman (403)
27 arXiv API Lerch AND "linear independence" (429)
28 ar5iv 1604.02896
29 ar5iv 1308.6451
30 ar5iv 2010.09167
31 arXiv html 2406.10820v2
32 Crossref "Kawashima Poels Pade Lerch"
33 Crossref "Nishimoto Lerch" 
34 Crossref DOI Chatterjee-Dhillon
35 Cambridge page Chatterjee-Dhillon (404)
36 Semantic Scholar web Chatterjee-Dhillon (403)
37 GitHub repositories "Lerch transcendent linear independence" (0 hits)
38 Crossref DOI Ulanskii
39 Crossref Pathak/Livingston
40 Crossref Rivoal Lerch
41 Crossref Hessami Pilehrood (429)
42 OEIS "Lehmer Euler constants arithmetic progressions"
43 Tsukuba repository PDF Kawashima (downloaded to scratch, read)
44 Kyoto RIMS PDF 1710-18 (Waldschmidt survey, not relevant)
45 Crossref Kawashima-Poels
46 Crossref Nishimoto (second try); also Crossref BBP/Baker/Bailey; Crossref
   Gun-Murty-Rath (429); Chatterjee harmonic numbers (429); Okada (429); arxiv.org/a/ author
   pages (404, two); Google (blocked); Murty p-adic digamma PDF (redirect); ar5iv 1303.1856
   (first half only).

Totals: WebSearch calls = 5; endpoint/fetch queries = about 55 (46 numbered above plus the
extra ones listed in item 46), of which about 25 returned usable content.
