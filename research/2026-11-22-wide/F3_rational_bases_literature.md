# F3: BBP-type formulas for pi in rational non-integer bases (base 3/2, 4/3): what is in print

Date: 2026-11-22. Marks: [READ] read on the source's own page or PDF; [SNIPPET] seen in a search
result, abstract or API record only; [INFERRED] my own conclusion. Numerical checks that I ran
myself are marked [CHECKED].

## 1. Summary

1. The general principle is in print, with real (not only integer) parameter: the series
   sum_k p^k sin(kx)/k = arctan(p sin x/(1 - p cos x)) with REAL p and rational multiples of pi
   for x is stated by Adegoke (J. Math. Res. 2010, "A non-PSLQ route") and used again in
   Adegoke-Layeni (2013). [READ, arXiv copy of the 2010 paper]
2. The cleanest statement of the principle is the geometric one of Kristensen-Mathiasen (J. Number
   Theory 2023, arXiv 2208.07696): Theorem 1 holds for ANY r in (0,1) and angle a rational
   multiple of pi with even denominator b; the formula has base r^(-b); triangle with vertices
   0, 1, 1 + r e^(i theta). They also say searching in non-integer bases is "largely unexplored"
   and that they found no earlier examples besides Adegoke's golden-ratio ones. [READ]
3. Neither paper writes down a formula for pi in a RATIONAL non-integer base such as 3/2. All
   of Adegoke's/Layeni's general-base formulas take the parameter t (or u) to be a positive
   integer; Kristensen-Mathiasen search integer bases (powers of 2, 3) and Pisot bases
   (golden ratio, 1+sqrt 3, ...). [READ] Not found in print: pi in base 3/2 (searched, see log).
4. A formula for pi*sqrt(3) with ratio -27/64 = -(3/4)^3 (so base -(4/3)^3, length 6, i.e. the
   family of base 4/3) IS in print: Adegoke-Layeni, "The higher derivatives of the inverse
   tangent function and rapidly convergent BBP-type formulas for pi", Applied Math. E-Notes 10
   (2010) 70-75, eq. (4.4), arXiv 1603.08540 (posted 2016). The authors say it is "technically
   speaking" not a BBP-type formula. [READ on ar5iv] I checked it to 40 digits [CHECKED].
   So the base-4/3 pi*sqrt(3) result is a rediscovery (possibly an identical series regrouped);
   the base-3/2 formula for pi is not found.
5. No classification of the bases (rational or algebraic) admitting formulas for pi exists in
   print. Borwein-Borwein-Galway (2004) treat only integer bases and only Machin-type formulas.
   Kristensen-Mathiasen list as open: irrational-base digit extraction, higher degree, and the
   unexplained abundance of golden-ratio zero formulas. [READ]
6. Digit extraction in base 3/2 has no standard meaning: the Akiyama-Frougny-Sakarovitch rational
   base system is built from least significant digits of INTEGERS, and the real expansions are
   not read through the BBP trick. Kristensen-Mathiasen say plainly that naive digit extraction
   fails for irrational bases. [READ for K-M; SNIPPET for AFS]
7. Recommended description of the base-3/2 pi formula: "an instance of a known construction
   (Adegoke 2010; Adegoke-Layeni 2013; Kristensen-Mathiasen 2022 Theorem 1) with a parameter
   (r^2 = 2/3, angles multiples of pi/12 in the (45,60,75) triangle) that the literature did not
   use; not a digit-extraction formula." New as an explicit formula; routine as mathematics.
   Do not call it a BBP digit-extraction formula (section 4).
8. A real open question the literature leaves, and which fits the project's toolkit: classify
   the r with r^2 rational for which a rational combination of the angles arg(1 + r e^(i theta))
   equals pi (section 5, lead 1).

## 2. What is known (marked statements)

### 2.1 Where the general real-parameter principle appears

- Adegoke 2010 (J. Math. Res. 2(2), 56-64; arXiv 1603.08209 posted 2016). Starts with
  -ln(1 - z) = sum z^k/k, sets z = p cos x + i p sin x with REAL p and x, and gets
  arctan(p sin x/(1 - p cos x)) = sum p^k sin(kx)/k and -(1/2) ln(1 - 2p cos x + p^2) =
  sum p^k cos(kx)/k, then chooses x = pi/2, pi/3, pi/4, pi/6 and p = 1/u etc. He keeps u an
  integer (or u^2 an integer) so that the base is an integer: "a BBP-type formula if u^2 is a
  positive integer". [READ]
  Example [READ]: arctan(1/u)*u = sum (1/u^2)^k (u/(4k+1) - 1/(4k+3))... i.e. base u^2 or u^4
  for any u; the same text covers x = pi/3, pi/4 with p = 1/n, 2/u, ... The identities are valid
  for non-integer u; only the label "BBP-type" is lost.
- Adegoke-Layeni 2013 (Notes Number Theory Discrete Math. 19(3), 33-54). Title says "general
  bases, for arctangents of real numbers". The constants are K = sum over m of eps_m * Im
  Li_1(t^(-1/2) exp(i m pi/n)) with t a POSITIVE INTEGER and n in {1,2,3,4,5,6,8,10,12,15,20,24,
  30,40,60}. They note that for n=3 the formula is BBP-type "only if t is rational" and then
  substitute t -> t^2. Highlight: first formula for pi*sqrt(5). [READ]
  This is exactly the scheme of the new formula with t = 3/2 and n = 24 (angles multiples of
  pi/12); the restriction t integer is what keeps it from covering base 3/2. [INFERRED]
- Barsky-Munoz-Perez-Marco, "On the genesis of BBP formulas" (Acta Arith. 198 (2021) 401-426,
  arXiv 1906.09629): general complex parameter s, geometric ratio 1 - s; they take s with 1/(1-s)
  = integer or Gaussian-rational (e.g. s = 1+i, (7+i)/8, 1+i/2) and extract real and imaginary
  parts. They state the base must be an integer in their definition of classical BBP form; they
  also use s = 3/2 only for log(3/2) (ratio -1/2, base 2). No pi formula in a rational
  non-integer base. [READ]
- Kristensen-Mathiasen (arXiv 2208.07696; J. Number Theory 244 (2023) 251-263). Theorem 1: for
  theta = (a/b) 2 pi, 2 | b, r in (0,1):  arg(1 + r e^(i theta)) = BBP(1, r^(-b), b, A),
  A_j = r^j (-1)^(j+1) sin(j theta)  [with their normalisation]. Geometric reading: triangle 0, 1,
  1 + r e^(i theta); if both the angle at 0 and at 1 are rational multiples of pi you get a
  formula for pi. Lemma 2: linearity in A. Algorithm: fix algebraic r, even b, LLL on the
  vectors CTB_b(r, a), exact algebraic verification of the output (the output is itself a
  geometric proof). Their search: integer bases (2^4, 2^6, 2^12, 2^20, 3^6), Pisot bases
  (golden ratio, 1+sqrt 3, x^2-3x+1, ...). They found a new formula for sqrt(3) pi in base 2^12,
  and for pi in two Pisot bases: pi = 10 BBP(1, 15, 15, CTB(-1,2)) in the first quadratic
  Pisot base treated in their Table 2 (the golden ratio line; the text there is garbled in my
  extraction, so the identification is uncertain) and pi = 12 BBP(1,12,12,CTB12(-1,2)) in base
  1 + sqrt 3. [READ]
  Statements in the paper [READ, paraphrased]: "searching for BBP-type formulas in non-integer
  bases appears to be largely unexplored territory"; Adegoke's golden-ratio formulas have
  coefficients in Z[phi] which "seems a little unnatural"; the abundance of golden-ratio zero
  formulas "is somewhat of a mystery"; getting digit information out of the irrational-base
  formulas "remains an open problem"; naive extension of spigot algorithms "fails miserably".
  They search only for integer coefficients; rational r^2 is never singled out. Their r =
  1/sqrt 2, 1/sqrt 3, 1/2 are the integer-base cases of the same theorem.
- Applied Math. E-Notes 10 (2010) 70-75 (Adegoke-Layeni, arXiv 1603.08540), eq. (4.4) [READ on
  ar5iv]:
      pi*sqrt(3) = (9/64) sum_{n>=0} (-1)^n (3/4)^(3n)
                   [16/(6n+1) + 24/(6n+2) + 24/(6n+3) + 18/(6n+4) + 9/(6n+5)].
  Derived from pi/2 - theta = sum (1/n) cos^n(theta) sin(n theta), theta = pi/6, i.e. from the
  (30,60,90) triangle. Ratio (-27/64) per 6 terms. The paper says "technically speaking" it is
  not BBP-type. [CHECKED numerically: equals pi*sqrt 3 to 40 digits.]
  Also checked: the new base-3/2 pi/4 series in the task statement, to 40 digits [CHECKED].

### 2.2 Non-integer bases in the BBP literature (the Pisot / golden ratio strand)

- Adegoke, "The golden ratio, Fibonacci numbers and BBP-type formulas", Fibonacci Quart. 52(2)
  (2014) 129-138 (arXiv 1603.06307). Base-phi formulas obtained by choosing the base "to be a
  power of phi" in the general formulas of the 2013 paper. He says that because phi is not an
  integer these series "do not really lead to any digit extraction formulas, but rather
  correspond to base phi expansions". He also says phi-nary formulas for pi appear in refs
  [4,6,7] (Bailey's compendium; Chan; Cloitre). [READ]
- Bailey's Compendium (2017 version), section 13 "Curiosities", formula (132): a formula (132) for a constant with sqrt(3)
  and 5^(5/4) in the irrational base 2/phi (phi the golden mean) [READ]; the author says
  "neither, technically speaking, is a BBP-type formula". Section 11 "General bases" lists
  formulas valid in a free parameter b (arctan, log) - all stated with integer b in the notation
  P(s,b,l,A). [READ]
- Wikipedia (BBP article): "the P notation can be also generalized to the case where b is not an
  integer", with the arctan(1/b) series as example. [READ]
- MathWorld "BBP-Type Formula": only non-integer base named is phi (formula for pi^2, Cloitre);
  repeats the Borwein-Borwein-Galway no-go for Machin-type pi formulas outside base 2. [READ]
- Cloitre 2025 (arXiv 2508.03743): pi^2 in base phi, proof via the regular pentagon; says that
  extension to other irrational algebraic bases "seems unlikely" without a similar geometric
  counterpart and leaves the octagon / sqrt 2 analogue open. [READ]
- Adegoke-Lafont 2023 (J. Integer Seq. 26, 23.5.5, arXiv 2303.13374): base-alpha expansions of
  log F_n, log L_n, arctan(1/F_n), arctan(1/L_n). [SNIPPET]
- Zudilin 2024 (arXiv 2409.10097), "A BBP-style computation for pi in base 5": 3 pages, abstract
  says it jokes about computing base-5 digits of pi from a given place; uses the norm-5 Gaussian
  integers 1 +- 2i (as I read the snippets). [SNIPPET]
- Plouffe 2022: a decimal-digit formula for pi that still needs the earlier digits (Wikipedia).
  [SNIPPET via Wikipedia]

### 2.3 Classical series in powers of 2/3, 3/4 (question 1b)

- MathWorld "Pi Formulas" and Wikipedia "List of formulae involving pi": I found no series for
  pi with ratio 2/3 or sqrt(2/3) and rational AP-denominator coefficients. The nearest items:
  Euler-type series sum (n!)^2 2^n/(2n+1)! (ratio 1/2), Gosper's (sqrt 3 pi/9) = (1/2) sum
  (i!)^2/(2i+1)! (ratio 1/3), Vardi/Flajolet pi = sum (3^k-1) zeta(k+1)/4^k (ratio 3/4 but with
  zeta values), Sharp's sqrt(12)-series (ratio -1/3), Ramanujan-type series with ratios 2/27,
  1/9, 1/64, -1/8 (hypergeometric, not BBP-type). [READ MathWorld; Wikipedia]
- Euler's transform arctan x = sum 2^(2n)(n!)^2/(2n+1)! x^(2n+1)/(1+x^2)^(n+1) has geometric
  ratio x^2/(1+x^2); x^2 = 2 gives ratio 2/3 and x^2 = 3 gives 3/4. But the coefficients are
  central-binomial type (n!)^2 4^n/(2n+1)!, not rational functions of n over an arithmetic
  progression, so these are not BBP-type and cannot be rewritten as one. [INFERRED]
- OEIS searches (A000796 formula lines etc.) show no (2/3)^k or (3/4)^k BBP-type pi entry.
  Jaume Oliver Lafont's OEIS wiki BBP page lists only integer bases (2,3,9,27,64,1024) and the
  ratio -1/27 etc.; no 3/2, 4/3 or golden ratio. [READ]

### 2.4 Who first (question 2)

- The identity sum x^k sin(kt)/k = arctan(x sin t/(1 - x cos t)) is classical (Euler-era
  complex logarithm series); I did not trace the first print. [INFERRED]
- First to use it for BBP-type formulas with a free real parameter and rational angles
  (pi/2, pi/3, pi/4, pi/6): Adegoke, J. Math. Res. 2010; Adegoke-Layeni 2013 extend to angles
  pi/n for n up to 60 and arbitrary t = integer. Geometric / triangle reading and full real
  r in (0,1) with arbitrary rational angles: Kristensen-Mathiasen 2022. In the integer-base
  cases the same shape (z = 1 - 1/b etc.) is in Bailey-Borwein-Plouffe-era work
  (Adamchik-Wagon 1997, Bellard, Broadhurst 1998 as cited by Adegoke). [READ Adegoke intro]
- The pi*sqrt(3) formula with ratio -(3/4)^3: Adegoke-Layeni 2010 (E-Notes). [READ]

## 3. What is open

(Each "stated" means the source itself says so; "not found" means only that I searched.)

- Digit information from irrational-base BBP-type formulas: stated open by Kristensen-Mathiasen
  (concluding remarks). Same caveat in Adegoke 2014 and Bailey section 13. [READ]
- Higher-degree analogue of the triangle construction: stated open by Kristensen-Mathiasen.
- Why the golden ratio has so many zero formulas: stated open by Kristensen-Mathiasen. [READ]
- Other irrational bases (e.g. via the octagon, sqrt 2): stated open/"challenging" by Cloitre
  for degree-2 constants (pi^2). [READ]
- Classification of the (rational or algebraic) bases admitting a degree-1 formula for pi (or a
  given algebraic multiple of pi): not found in print, and not posed as a question except
  implicitly by the K-M remarks. [Not found: searched arXiv, Crossref, zbMATH, OEIS, MathWorld,
  Wikipedia for "rational base", "non-integer base", "which bases"]
- Borwein-Borwein-Galway 2004 state (abstract) that for b > 2 not a proper power pi has no
  b-ary Machin-type BBP arctan formula, and that no BBP formula of any form is known when no
  such formula exists. [SNIPPET: Crossref abstract record; zbMATH] This is about integer bases.
- Mahler's 3/2 problem and the irrationality of K(3/2) = 1.62227...: open (a 2026 paper by Stephan
  states the irrationality has been open since 1977; its results are conditional on automaticity).
  [SNIPPET, arXiv 2609.19007 abstract] This is the arithmetic obstruction for base 3/2 (section 4).

## 4. Question (4): digit extraction in base 3/2

- Akiyama-Frougny-Sakarovitch (Israel J. Math. 168 (2008) 53-91): represent each positive
  integer N uniquely as N = sum (a_i/2)(3/2)^i with digits a_i in {0,1,2}, computed from the
  RIGHT (least significant first) by the map N -> (2N' ...) rule; the language is not regular
  but addition is by a right letter-to-letter transducer; every real has at least one expansion;
  fractional parts {xi (p/q)^n} and the Josephus constant K(p) appear. Cited as the base of
  Mahler's Z-number problem. [SNIPPET: HAL abstract; Crossref reference list (Mahler 1968,
  Flatto-Lagarias-Pollington, Dubickas)] The full paper was not reachable (HAL Anubis block,
  Springer redirect).
- Related: Morgenbesser-Steiner-Thuswaldner 2013 (digit patterns, normal numbers in rational
  base), Akiyama-Marsault-Sakarovitch 2014, Andrieu-Eliahou-Vivion 2025 (normality conjecture),
  Eliahou-Verger-Gaugry 2025 (3/2 and the 3x+1 problem), Stephan 2026. None connects to BBP
  series or to computing a given digit of a constant. [SNIPPET]
- My reasoning (INFERRED, not found in print): the BBP trick needs {b^n S} with b an integer,
  so that b^(n-k) mod (nk+j) is computed by modular exponentiation. For b = 3/2 the
  corresponding quantity is {(3/2)^(12 n) S} and the terms for k < n are
  3^(e) /(2^(e) m) mod 1, whose denominator 2^e m grows with n; no short modular reduction
  exists, and {(3/2)^n x} is the hard object of Mahler's problem. So no practical spigot
  results, consistent with Kristensen-Mathiasen's "fails miserably".
  So "base 3/2" here means only: the series has geometric ratio (2/3)^12; it is a base-3/2
  numeration of the value only in the loose sense used by Adegoke ("expansions"), not in the AFS
  sense.

## 5. Leads for this project (ranked)

### Lead 1: which rational bases r^(-N) arise from rational-angle triangles
Statement: the single-triangle formulas of K-M Theorem 1 need r = sin A / sin C for a triangle
with all three angles rational multiples of pi (law of sines). With r^2 = p/q rational, the
possible r are given by the ratios of sines of rational angles with rational square; this is the
trigonometric diophantine problem (Conway-Jones 1976 style classification, not read here).
Known members: r = 1/2, 1/sqrt 2, 1/sqrt 3 (the integer bases 2, 2, 3 powers), sqrt(3)/2 (base
4/3), sqrt(2/3) (base 3/2), and phi-related ones (irrational base). Prove: the finite list of
r^2 in Q (up to r -> 1/r and complement) for which a single triangle gives a formula for pi; and,
with Baker plus the lattice reduction already used, whether any combination of arg(1 + r e^(i
theta)) with r^2 rational outside this list equals a rational multiple of pi. [INFERRED]
Why it fits: same toolkit as the base-2/3 classification (cyclotomic norms, prime ideals,
Baker). Size: weeks (finite list from literature, check by exact computation: days).
Noticeable because it would be the first classification of rational non-integer bases (K-M
call the area unexplored), and would give "exactly these rational bases carry a pi formula".

### Lead 2: exhaustive search, rational base p/q up to a bound
Compute, for r^2 = p/q with p, q <= ~200, all denominators b | 120 (and more), the
rational-coefficient relations among arg(1 + r e^(i m pi/b)) containing pi (LLL as in K-M plus
exact check); tabulate "length per bit" using the 2/3-term measure of the project. Size: days
on the 24-core machine. K-M restricted to integer coefficients and Pisot bases, so this is
unmapped. Worth noticing: a table of bases and shortest formulas.

### Lead 3: formal proof (Lean) of the base-3/2 and base-4/3 formulas
Statement: pi/4 = sum (2/3)^(12k) sum a_j/(24k+j) and the sqrt(3) pi formula, from the Mathlib
series for arctan / Complex.log of 1 + z with z = sqrt(2/3) e^(i theta). Toolkit exists
(Parts I-II machine-checked). Size: days. Worth noticing: Lean-checked versions of the
Adegoke-Layeni 4.4 formula and K-M Theorem 1 for all real r (statement for general r in (0,1)
and rational angle) would be a clean reusable lemma.

### Lead 4: cost per unit of information in non-integer bases
Extend the 2/3-term lower bound (section 1 of the rules file) to rational bases by replacing
log b by the logarithm of the base, to see whether base 3/2 or 4/3 beats the binary optimum 2/3
non-zero terms per bit when "bit" means log_2 of the ratio. Size: weeks; depends on a
convention for "digits per term" since digit extraction is unavailable (section 4), so this is
a measurement of convergence rate per non-zero term only. Noticeable only as a remark.

### Lead 5: the formal impossibility of BBP digit extraction in base 3/2
Not a theorem I can state precisely; the obstruction is Mahler's open problem. Out of reach as
a theorem; at most a remark.

## 6. Overlap or conflict with the project's results (section 1 of the rules file)

- No conflict. The integer-base theorem ("a formula for a rational multiple of pi in integer
  base b exists iff |b| is a power of 2") is not contradicted by K-M, which use real r; their
  base r^(-b) is an integer only for r^2 = 1/2, 1/3, 1/4,... (their integer-base tables
  confirm the bases 2^4, 2^6, 2^12, 2^20, 3^6, 3^20).
- Overlap: the base-4/3 pi*sqrt(3) formula = Adegoke-Layeni 2010 (4.4) (ratio -(3/4)^3, length
  6). Period-12 regrouping of the sqrt(3)/2, pi/6 series with ratio (3/4)^6 gives the same
  number; whether it is term-for-term your formula I cannot see without your coefficients.
  [INFERRED; formula (4.4) checked numerically]
- Overlap: the base-3/2 formula is a special case of Adegoke-Layeni 2013's scheme and of K-M
  Theorem 1 (r = sqrt(2/3), b = 24, theta = a pi/12). Not previously written in print as far as
  my search shows.
- The statement "In print this is stated as known (Bailey's Compendium, citing BBG 2004)" about
  integer bases is consistent with what I read: BBG abstract is about Machin-type formulas and
  says nothing more general. [SNIPPET]

## 7. Conclusion (question 5): how to describe the base-3/2 formula

Say: "a degree-1 formula for pi with rational coefficients and geometric ratio (2/3)^12, obtained
from the (45,60,75) triangle by the Adegoke / Kristensen-Mathiasen construction (the series for
arg(1 + r e^(i theta)) with r^2 = 2/3); it is the first explicit formula of this kind in a rational
non-integer base that I could find, but the construction is known and it is not a digit-extraction
formula in the sense of BBP, since no digit extraction is known for non-integer bases." Do not
claim "new method". "New" is defensible only for the explicit base-3/2 formula, and only as
"not found in a search of arXiv, Crossref, zbMATH, OEIS, MathWorld, Wikipedia and general web
search". The base-4/3 formula for pi*sqrt(3) should be credited to Adegoke-Layeni 2010 (E-Notes)
as a rediscovery (modulo regrouping). Suggested citations: Adegoke 2010; Adegoke-Layeni 2013;
Kristensen-Mathiasen 2023; Barsky-Munoz-Perez-Marco 2021.

## 8. Sources (URLs)

- https://arxiv.org/abs/2208.07696 and https://arxiv.org/pdf/2208.07696 (Kristensen-Mathiasen) [READ]
- https://arxiv.org/pdf/1603.08209 (Adegoke 2010) [READ]
- http://nntdm.net/papers/nntdm-19/NNTDM-19-3-33-54.pdf (Adegoke-Layeni 2013) [READ]
- https://ar5iv.labs.arxiv.org/html/1603.08540 (Adegoke-Layeni 2010 E-Notes) [READ]
- https://arxiv.org/pdf/1603.06307 (Adegoke, golden ratio) [READ]
- https://arxiv.org/pdf/1603.07395 (Adegoke-Lafont-Layeni, general binary bases) [READ in part]
- https://arxiv.org/pdf/1906.09629 (Barsky-Munoz-Perez-Marco) [READ in part]
- https://arxiv.org/pdf/2508.03743 (Cloitre) [READ in part]
- https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf (Bailey Compendium) [READ sections 10, 11, 13]
- https://mathworld.wolfram.com/BBP-TypeFormula.html ; https://mathworld.wolfram.com/PiFormulas.html
- https://en.wikipedia.org/wiki/Bailey-Borwein-Plouffe_formula ; List_of_formulae_involving_pi
- https://oeis.org/wiki/User:Jaume_Oliver_Lafont/BBP
- https://arxiv.org/abs/2609.19007 (Stephan 2026); https://arxiv.org/abs/2409.10097 (Zudilin)
- Crossref DOI 10.1007/s11856-008-1056-4 (AFS); HAL hal-00159696 (AFS abstract via HAL API);
  Crossref DOI 10.4153/cjm-2004-041-2 (BBG)
- Note: no page contained text addressed to me.

## 9. Search log

WebSearch (4 of 6 used):
W1 BBP-type formula pi rational base "3/2" OR "non-integer base" digit extraction
W2 series for pi geometric ratio 2/3 arctan 1/sqrt(2) rational coefficients (2/3)^n
W3 BBP-type formulas which bases admit formula for pi open problem non-integer base ... beta-expansion
W4 "base 3/2" OR "base 4/3" OR "rational base" BBP formula pi sqrt(3) (3/4)^k series arctan

Endpoint queries (fetch tool), numbered:
1 arXiv API all:"BBP"+"rational base" (HTTP 429)
2 arXiv API all:"BBP-type"+pi (429)
3 OpenAlex works search BBP formula pi arbitrary base (429)
4 Crossref BBP type formula pi rational base
5 Semantic Scholar BBP non-integer base (429)
6 zbMATH BBP formula pi
7 arXiv PDF 1603.06307
8 MathWorld BBP-TypeFormula
9 Crossref general bases arctangents real numbers
10 Crossref Kristensen Mathiasen
11 OEIS 2/3 pi BBP
12 arXiv author page Kristensen (404)
13 arXiv API ti:"BBP-type formulas" (429)
14 Semantic Scholar web search (403)
15 OpenAlex elementary approach (429)
16 arXiv abs 2507.20428
17 arXiv listing search KM title
18 arXiv HTML 2507.20428
19 Bailey Compendium PDF (read via pdftotext)
20 Wikipedia BBP formula
21 arXiv PDF 2208.07696
22 arXiv abs 2208.07696
23 Crossref AFS rational base
24 Crossref rational base number system (429)
25 zbMATH rational base number system
26 zbMATH BBP type formula arctangent base
27 Crossref Chan pi^2 golden base
28 Crossref digit extraction non-integer base (429)
29 arXiv abs 2609.19007
30 Springer AFS (redirect, not read)
31 OEIS 2/3 arctan series pi
32 MathWorld Pi Formulas
33 arXiv search BBP formula rational base
34 arXiv search BBP-type formula (16 hits)
35 arXiv search digit extraction pi non-integer base (0 hits)
36 arXiv search Machin-type BBP arctangent algebraic base triangle (0 hits)
37 arXiv search Adegoke general bases arctangents (429)
38 arXiv abs 2508.03743
39 arXiv abs 1603.08209
40 arXiv search Barsky Munoz Perez-Marco (429)
41 arXiv PDF 1603.08209
42 arXiv PDF 1603.07395
43 OEIS pi "(2/3)^k" series
44 OEIS BBP "base 3/2" (empty)
45 OEIS Pi*sqrt(3) (3/4)^k
46 OEIS Lafont BBP zero relation (empty)
47 Crossref BBG record
48 Crossref BMPM (429)
49 arXiv PDF 2508.03743
50 arXiv search genesis of BBP formulas
51 arXiv search Adegoke Lafont golden ratio base
52 arXiv PDF 1906.09629
53 arXiv abs 2409.10097
54 HAL AFS document (Anubis block)
55 Crossref AFS full record (references)
56 HAL API search rational base number systems
57 arXiv search rational base number system 3/2
58 Wikipedia Non-integer base of numeration
59 Wikipedia BBP (second pass, P notation sentence)
60 Crossref Adegoke-Layeni general bases
61 ar5iv 1603.08540
62 OEIS Lafont BBP pi base
63 OEIS wiki Lafont BBP page
64 Crossref Adegoke-Layeni higher derivatives
65 zbMATH Adegoke BBP general bases
66 zbMATH irrational base BBP Pisot (404)
67 MDPI Wu-Chen-Zhu (403)
68 NNTDM landing page 33-54
69 NNTDM PDF
70 pure.au.dk published K-M PDF
71 ar5iv 1603.08540 (eq. 4.4 detail)
72 Crossref Wu-Chen-Zhu DOI
73 Wikipedia List of formulae involving pi
74 Crossref Wei BBP
75 Crossref Zhang Fibonacci BBP
76 arXiv abs 1409.6455
77 Crossref "Symbolic routes ..."
78 arXiv search "Symbolic routes ..." (0 hits)

Totals: WebSearch calls: 4. Endpoint queries: 78 (of which 12 returned errors or blocks: 429 x9,
403 x2, 404 x2 counted among them; arXiv API, OpenAlex and Semantic Scholar refused automated
access at this time, so arXiv listing pages, Crossref, zbMATH, HAL API and OEIS were used instead).
Pages or PDFs actually read in full or in large part: K-M (arXiv), Adegoke 2010, Adegoke-Layeni
2013, Adegoke golden ratio (section 5), Adegoke-Layeni E-Notes (ar5iv), Bailey Compendium
(sections 10-13), BMPM (introduction and sections 2, 5), Cloitre (intro and conclusion),
MathWorld, Wikipedia (two articles), Lafont OEIS wiki.
