# R02: constants other than pi with BBP-type formulas, and constants that cannot have them

Thread R02 of the wide pass of 22 November 2026. Plain ASCII. Marks: [READ] read on the
source itself (page or PDF text extracted locally with pdftotext), [SNIPPET] seen only in a
search result or API record, [INFERRED] my own conclusion.

## 1. Summary

1. There is no published "iff" description of which numbers have degree-1 base-b formulas. What
   exists: generators (Taylor series of log(1 - z) at z = zeta/beta), the Machin-type theory
   of Borwein-Borwein-Galway (BBG) for Q(i)-logarithms only, and the structure statement
   in Lagarias 2001 (Theorem 5.3 and its proof). [READ]
2. Lagarias (Exp. Math. 2001) proves, via Baker, that a BBP series with a denominator
   that splits into distinct linear factors over Q has a value that is rational or
   transcendental, with an algorithm to decide which. The partial-fraction step he sketches
   (log(1 - exp(2 pi i k/q) z) terms) is the "values are logarithms" theory in print. [READ]
3. "e has no degree-1 formula" is NOT a consequence of Baker. It is equivalent to a special
   case of "e is not in the algebraic-number span of logarithms of algebraic numbers". Waldschmidt
   and Wikipedia: it is not known that e is not a period, and no explicit non-period is
   known. It follows from Schanuel's conjecture [INFERRED, short argument in 4.2].
   Bailey says e is "as far as anyone can tell" not polylogarithmic, not proved. [READ]
4. Same for Euler's gamma (conjectured not a period, not even an exponential period) and for
   degree-1 versus pi^2, zeta(3), Catalan: only conjectural exclusion in print. [READ]
5. Catalogue of degree-1 constants other than pi and logs in Bailey's Compendium (April
   2023 version): pi*sqrt(2), pi*sqrt(3) (bases 2^k and 3^k), (1/2)log(1+sqrt 2)-type value,
   a golden-ratio constant (Adegoke), many arctan values (list of ~250 rationals, plus the
   "unknown" arctan(2/7)), logs of 46 primes up to ~4.4e12, general-base families (Adegoke).
   Every real Dirichlet L(1,chi) of conductor 3,4,5,8 appears; the others (7, 11, 12, ...) not found.
6. Two bases: Lagarias (Question in section 6) asks whether all BBP numbers that are G-function
   special values have formulas in two multiplicatively independent bases; examples log 2
   (bases 2, 9, 3^2...), pi^2 (bases 2^k and 3^k, but at DEGREE 2, not degree 1). No theorem found.
7. Barsky-Munoz-Perez-Marco (Acta Arith. 2021, v4 2023) say no base-3 formula for pi is known:
   the project proves none exists. Zudilin (2024 joke note) says base-5 digit
   extraction for pi is "an open question". Both are overlaps with project results (section 5).
8. Zudilin's note and BBG Example 4 contain open-flavoured statements that the project's
   Theorem K (log criterion for every y and base) may settle (see 3 and 5).
9. Best new lead: a table/theorem of which real Dirichlet characters chi (equivalently which
   pi*sqrt(d), and sqrt(d)*h*log(eps_d)) have degree-1 formulas in base 2 and base 3, using the
   existing finite prime test. Not found in print.

## 2. What is known

### 2.1 Catalogue (Bailey, Compendium, version dated April 8, 2023) [READ]

All items are P(s, b, n, A) with s = 1 (degree 1) unless stated.

- Logs. log 2 base 2 (and base 9, formula 67, 2/3 log 2 = P(1,9,2,(1,0))); log 3 in bases 4,
  9, 3^6 (formulas 8, 70, 71); log 5, 7, 11, 13 in base 3^k (formulas 72-75, Oliver Lafont);
  log 10 related: log(9/10) in base 10 (formula 84), log(32/25) base 25 (85); base-b general
  families (formulas 90-110, Adegoke 2013, e.g. b*log(b/(b-1)) style).
  Primes with a binary log formula (list (9)): 2,3,5,7,11,13,17,19,29,31,37,41,43,61,73,109,113,127,
  151,241,257,337,397,683,1321,1613,2113,2731,5419,8191,43691,61681,87211,131071,174763,262657,
  524287,2796203,15790321,18837001,22366891,4278255361,4562284561,2932031007403,
  4363953127297,4432676798593. Bailey: not known whether all primes, or only finitely many,
  have this. (Project: Theorem H classifies primes below 100: consistent, 23 is absent.)
- Arctangents. Binary formulas for arctan q for a large set of rationals (lists (14), (16));
  Bailey observes (experimentally) these coincide with q = |Im T/Re T| for T a product of
  (1+i)^u/(1 - 2^-v...)-type terms; BBG 2004 give the structure theory. Stated unknown:
  arctan(2/7). arctan(5/36) done by Adegoke-Oliver Lafont-Layeni.
- Algebraic multiples of pi and logs: pi*sqrt(2) (formula 20-type, base 64, Knuth/Compendium
  formula 20; MathWorld cites eq. 17 base -8), pi*sqrt(3) (formula 21 binary, Knuth;
  formulas 69 and 68 give ternary: 3*arctan(3/7)-type in base 27 and a pi*sqrt(3) formula in
  base 36, Broadhurst 1998), a 'sqrt 2 * log(1+sqrt 2)' value (formula 23, binary, Knuth),
  a golden-ratio value (formula 22, base 2^20, Adegoke; Adegoke 2014 title: binary BBP-type
  formula for sqrt(5)*log(phi)), arctan values of tan-type numbers (formulas 24-28, Adegoke),
  arctan(1/sqrt 2)-type (formula 24). Formulas 24-27 are in base 16.
  (Some left-hand sides are garbled in my text extraction: I name only those I could identify.)
- Higher degree (not degree 1): pi^2 (formula 29, base 2^4 and formula 76 in base 3^6, degree 2),
  log^2 2, Catalan G (degree 2, base 2^12), pi*log 2, Cl_2(pi/3) type, zeta(3) (degree 3,
  binary, Broadhurst), zeta(5) (degree 5), pi^2 in golden base. The degree matters: for degree 1
  only logarithm-type constants occur.
- Non-integer base: pi^2 in base phi^5 (MathWorld eq. 34 [READ]); Kristensen-Mathiasen found pi in
  base 1+sqrt 3 and in a golden-type Pisot base. [READ]
- Zero relations (section 12): Bailey explicitly puts e, e^2, ..., e^5 into the PSLQ vector to
  exclude zero relations, noting that e is, "as far as anyone can tell" (not proven), not
  polylogarithmic. [READ] This is the only place in Bailey where "e" appears as a presumed non-value.

### 2.2 Theory of what degree-1 values are

- Generators: -log(1 - z) = sum z^k/k with z = zeta/beta. Adegoke ("A non-PSLQ route", arXiv
  1603.08209, 2016) takes z = p*e^{ix}, giving arctan(p sin x/(1 - p cos x)) and
  -(1/2)log(1 - 2p cos x + p^2) as BBP series for general bases. [READ, intro and section 2]
- Kristensen-Mathiasen (J. Number Theory 2023, arXiv 2208.07696): Theorem 1 (elementary): for
  theta a rational multiple of 2*pi, arg(1 + r e^{i theta}) is a degree-1 BBP value of base
  1/r^b-type; the same with the real part gives log |1 + r e^{i theta}|. Geometric picture: a triangle with
  vertices 0, 1, 1 + r e^{i theta}. Their search found: pi*sqrt(3) formula, a base 1+sqrt 3 Pisot
  formula for pi, many null formulas in golden base. Open problems they pose: digits from
  Pisot-base formulas; degree > 1. [READ]
- Barsky-Munoz-Perez-Marco (Acta Arith. 198 (2021), arXiv 1906.09629 v4): general complex
  parameter s = (rational) times root of unity construction of degree-1 formulas for log 2 and
  pi, explaining null formulas and the log 2 / pi relation as real/imaginary parts.
  They state that no base 3 formula for pi is known. [READ, intro]
- BBG (Canad. J. Math. 56 (2004) 897-925) [READ in full text]: define "Machin-type" = Q-linear
  combinations of Re or Im of logs of numbers in Q(i)^*, chosen so the series is BBP in base b.
  Theorem 1 excludes arctan(y/x) when a prime p = 1 mod 4 has odd p-adic order of x^2+y^2 and
  either p | b or 4 | ord_b(p)-type condition. Theorem 4: no non-Aurifeuillian binary Machin-type
  formula for ln 23 or ln 89 (ln 113 has an Aurifeuillian one). Theorem 6 and Example 4:
  when b has no "exceptional" Bang case (M_b = 0), there is no b-ary Machin-type formula for ln b
  (for example none in base 10), and they write that it seems unlikely there is one for any
  ln n, "but we have failed to prove this" (Example 4). Theorem 7: no b-ary Machin-type formula for pi,
  b > 2 not a proper power. Abstract: no b-ary BBP formula "of any form" is known for a constant
  without a Machin-type formula. Appendix B: every Machin-type formula can be written in
  Bailey's P form; the sets of b-ary BBP numbers form a Q-vector space; also reduce
  to combos of L(s,b,n,j) with only j varying.
- Lagarias (Exp. Math. 10 (2001) 355-368, arXiv math/0101055) [READ]: BBP numbers
  (b >= 2 an integer, rational function with q(n) != 0); Theorem 5.2: a BBP series is a
  G-function special value at 1/b iff q splits into linear factors over Q; Theorem 5.3: if
  q has distinct linear factors over Q then f(r) is rational or transcendental, effectively
  decidable, by partial fractions into terms with log(1 - exp(2 pi i j/q)z) at algebraic
  points and Baker. He says Adhikari-Saradha-Shorey-Tijdeman (Indag. Math. 2001) obtained the
  same. Degree-1 BBP series of Bailey type (denominators Nk+i) satisfy the hypothesis.
- Waldschmidt ("Transcendence of periods: the state of the art", PDF) [READ]: Baker's Theorem: a
  nonzero Qbar-linear combination of logs of algebraic numbers is transcendental; any such
  combination is a period. It is not known that there exist two algebraically independent
  logarithms of algebraic numbers (Conjecture 43 says all Q-independent logs are algebraically
  independent). No explicit non-period is known; e and e^2 are candidates; e is an exponential
  period (Wikipedia). Euler's gamma: transcendence unproven, conjectured not a period (Conj. 47).

### 2.3 Dirichlet L-values of degree 1 (my reading, [INFERRED] from class number formulas)

For a primitive real character chi_D: L(1, chi_D) is, for D < 0, 2*pi*h/(w*sqrt|D|) and for D > 0,
2*h*log(eps_D)/sqrt(D). So "pi*sqrt(d) up to rational factor" = L(1, chi_{-d}) and
"sqrt(D)*log(eps) up to rational" = L(1, chi_D). Catalogue by conductor, from items in 2.1:
chi_{-4}: pi (base 2^k only: BBG + project). chi_{-3}: pi*sqrt3 (bases 2^k and 3^k). chi_{-8}:
pi*sqrt2 (binary). chi_8: sqrt2*log(1+sqrt2) (binary, formula 23). chi_5: sqrt5*log(phi)
(binary, Adegoke 2014). I found no degree-1 base-b formula in print for chi_{-7}, chi_{-11},
chi_{12}, chi_{13}, ... (Bailey lists Cl_2 / L_{-7}(2) only at degree 2). "Not found" is weak:
I did not read Adegoke's papers 1603.07395 and 1603.06307 in full.
Complex (non-real) characters: values L(1,chi) are algebraic combos of logs of cyclotomic units
(or pi*algebraic); with rational a_i only particular combinations appear. No source found.

### 2.4 Constants "that cannot"

- Rational or algebraic irrational: a degree-1 value is 0 or transcendental (Lagarias Thm 5.3,
  ASST 2001; Baker). So no nonzero rational (other than via telescoping, a trivial case) and no
  algebraic irrational such as sqrt 2 or phi has one. [READ]
- pi: no formula in base not a power of 2 in the Machin-type class (BBG, Theorem 7); in print
  the full degree-1 statement is credited to BBG by Bailey's Compendium (see the project note).
- e: only "not expected" (Bailey) and "not known to be a non-period" (Waldschmidt, Wikipedia).
  I searched for a proof that e has no BBP-type formula (Crossref, zbMATH, OEIS, four web
  searches): not found. No source claims it as a theorem. [READ for Bailey, Waldschmidt]
- gamma, zeta(3) in degree 1, Catalan in degree 1, pi^2 in degree 1: nothing in print beyond
  conjectures that they are not in the Qbar-span of logs. zeta(3) has a degree-3 binary formula
  (Compendium (40)), pi^2 and G have degree-2 formulas, so the degree is what excludes them, not
  the base. [READ]

## 3. What is open (with who says so)

O1. Which numbers have degree-1 formulas in base b? Exact statement not in print. Bailey's
    Compendium says the list of primes with binary log formulas is "certainly not complete"
    and whether all primes qualify is unknown (stated open by the source). The project's
    Theorem H, K go beyond this (primes < 100 and an iff for every rational y).
O2. BBG, Example 4: for b with M_b = 0 (e.g. 10), is there a b-ary Machin-type formula for any
    ln n? They say it seems unlikely, "failed to prove" (stated by the source). With
    log(9/10) a base-10 value (Compendium 84), the correct question concerns ln n for natural
    n >= 2 only; Theorem K of the project (iff criterion for log y) presumably answers it in the
    Machin-type class (and in all of degree 1, since the project works with general P).
O3. Lagarias's Question: do all BBP numbers that are G-function special values have BBP
    expansions in two multiplicatively independent bases? Stated open by the source (2001).
    Known examples: log 2 (bases 2 and 3^2), pi*sqrt 3 (2^k and 3^k, degree 1), pi^2 (degree 2).
O4. Is e (or gamma, pi^2 at degree 1, zeta(3) at degree 1) a Qbar-combination of logarithms
    of algebraic numbers? Open (equivalent to part of "e is not a period" for e). Stated open
    by Waldschmidt/Kontsevich-Zagier context.
O5. Zudilin 2024 (arXiv 2409.10097): "an open question whether this type of computation is
    possible for pi related to other bases" (about digit extraction in general, not only
    degree-1 BBP); his base-5 expansion by (1 +- 2i) powers fails, because the formula has
    denominators of the form 5^(2n+1) in a Gaussian setting ("An obvious flaw"). [READ]
O6. Non-integer (Pisot) bases: digit extraction from such formulas, and degree > 1 geometric
    interpretation. Stated open by Kristensen-Mathiasen. [READ]
O7. Why zero relations exist for some (s, b, n): Bailey says "somewhat mysterious"
    in the Compendium; BMP explain part of them for degree 1. [READ]
O8. arctan(2/7) in binary: stated unknown by Bailey; the project settles it (Theorem I).

## 4. Leads for this project, ranked

### 4.1 (Rank 1, days to 2 weeks) Table/theorem: which real Dirichlet L(1, chi), equivalently
pi*sqrt(d) and sqrt(D)*h*log(eps_D), have a degree-1 formula in base 2 and in base 3.
Exact statement: for each fundamental discriminant D with |D| < some bound (say 200), decide
whether L(1, chi_D) (or the rational line through it) lies in the Q-span of degree-1 base-2^m
(resp. 3^m) series; and, if possible, a closed criterion (a prime-ideal condition on
Q(zeta_N, 2^(1/n)) or Q(zeta_N, 3^(1/n))).
Fit: the project already has (a) the exact description of base-2 values (Theorem C for pi),
(b) the finite prime test (Theorem K) for logs, (c) lattice reduction. The values pi*sqrt(d)
and logs of units are Qbar-combos of the same logs, and Baker gives the standard "primitive
prime divisor" exclusion argument. Known data to calibrate: d = 1, 2, 3 yes (base 2), d = 3 yes
(base 3), chi_5 and chi_8 yes (base 2), nothing found for 7, 11, 12, 13.
Worth noticing: first complete answer for "L(1, chi) with a binary formula"; the Compendium
asks for no such classification, Adegoke found cases by search. Risk: the answer may be
a short list (then it is a clean theorem); the formal Lean proof needs class number input,
but can be stated directly as "pi*sqrt(d)" and "sqrt(D)*log(eps)" to avoid it.

### 4.2 (Rank 2, days, formal) "Degree-1 values are Qbar-combinations of logs of algebraic numbers,
hence 0 or transcendental, and e is excluded under Schanuel."
Exact statement: (i) unconditional: a degree-1 BBP value (rational a_i) is zero or transcendental
(in the project's Baker import this is a direct corollary; Lagarias 5.3 gives the printed
source). (ii) conditional: Schanuel's conjecture implies e, and pi^2, are not degree-1 values.
Short argument [INFERRED]: write the value as a combination beta_0 + sum beta_j log alpha_j
with the logs and 1 Q-linearly independent (Baker); if it equals e then the set
{1, log alpha_j, e, alpha_j} has transcendence degree at most n (e is algebraic over Q(logs)),
while Schanuel on x = (1, log alpha_1, ..., log alpha_n) forces degree n+1: contradiction.
(For pi^2 take the logs to include i*pi, same argument.) Unconditional exclusion of e is
equivalent to an open problem (e not in the Qbar-span of logarithms), so do not promise it.
Fit: statement (i) is already inside the toolkit (Baker is imported); (ii) needs Schanuel as an
explicit hypothesis (as Baker used to be). Size: days. Worth noticing: the sentence "e has no
BBP-type formula" is usually asserted without proof; stating exactly what is and is not provable
is a short, citable note.

### 4.3 (Rank 3, weeks) Which bases b admit a formula for log q (q prime): the "two bases" question.
Exact statement: for q in {2, 3, 5, 7, 11, 13} known (Compendium) to have formulas in bases 2^k and
3^k: determine the full set B(q) = {b : log q has a degree-1 base-b formula}, and show that the
set of constants having formulas in both base 2^a and 3^c equals the Q-span of log p (p in a finite
set P_{2,3}) and pi*sqrt(3) and (maybe) a few more. This answers Lagarias's question for degree 1.
Fit: the project's Theorem K (log criterion) in bases 2, 3, 5, plus base-5 results,
plus the computed (not proved) Statement G for all b >= 5. A theorem "B(2) = {2^i, 3^j}" would extend
the project's "log b iff b is a power of 2 or 3" to all q.
Worth noticing: a direct answer to a question posed in Experimental Mathematics 2001, with
examples. Expect the finite set P_{2,3} to be computable (primes p for which ord_2 and ord_3
conditions both hold). 

### 4.4 (Rank 4, days) Close BBG Example 4 and Lagarias-type statements in print terms:
"for b with no Bang-exceptional case (b = 10 e.g.), log n for natural n >= 2 has no degree-1
base-b formula unless ...". The project already has the iff (Theorem K); the lead is to
state its corollary for b = 10 and for 3 <= b < 100, and compare with Compendium formula 84
(log 9/10, base 10), which shows the right form of the statement is about log of a rational
y with a specific factorisation, not about ln n.
Fit: pure corollary. Size: a day. Worth noticing: it resolves a "we have failed to prove"
remark from a Canad. J. Math. paper.

### 4.5 (Rank 5, out of reach as stated) Unconditional proof that e has no degree-1 BBP-type formula
in any integer base. Equivalent to e not in the Qbar-span of logarithms of algebraic numbers:
open, not provable by Baker. I found no short proof and none in print. Only 4.2 (ii).

### 4.6 (Rank 6, weeks, computational) Degree-1 formulas in non-integer (Pisot) bases:
classification of the null relations and values, following Kristensen-Mathiasen (golden ratio
has "mysteriously many" null formulas; they ask for a reason). Fit: the Kummer-extension
prime-ideal machinery is the right tool; but base is not an integer so digit extraction is
unclear (they say so). Low priority.

## 5. Overlap or conflict with section 1 of the rules file

- "pi has a degree-1 formula in base b iff |b| is a power of 2": consistent with Compendium
  ("no other degree-1 BBP-type for pi except base a power of two", citing BGB 2004) and
  with BMP v4 (2023): "no base 3 formula for pi is known" (the project proves none exists:
  a gap in the literature the project fills). BBG itself proves only Machin-type (Theorem 7
  and abstract), as the rules already note. [READ]
- Zudilin 2024 (arXiv 2409.10097), section 2: "It is an open question whether this type
  of computation is possible for pi related to other bases". The project's theorem answers
  the degree-1 BBP case (no), not digit extraction in general. Worth citing as the context in
  which a base-5 no-go result is a response. [READ]
- "log b has a degree-1 formula of base b iff b is 2^i or 3^j": compare BBG Example 4 (none for
  bases with M_b = 0, e.g. 10) and the closing remark that other ln n are "unlikely", unproved.
  Consistent: no conflict, the project is stronger. (Note Compendium's base-10 formula 84
  is for log(9/10), not log 10.)
- "arctan(2/7) has no formula": Compendium says "not known"; consistent.
- "log 23 has none": consistent with Compendium list (9) (no 23) and BBG Theorem 4
  (non-Aurifeuillian binary Machin-type only; the project covers all degree-1 formulas).
- No contradiction found anywhere.

## 6. Sources

- Bailey, Compendium of BBP-type formulas (April 8, 2023): https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf
- Borwein-Borwein-Galway, Canad. J. Math 56 (2004): https://doi.org/10.4153/CJM-2004-041-2 (Cambridge PDF)
- Lagarias, On the normality of arithmetical constants: https://arxiv.org/abs/math/0101055
- Kristensen-Mathiasen: https://arxiv.org/abs/2208.07696 (J. Number Theory 2023)
- Barsky-Munoz-Perez-Marco: https://arxiv.org/abs/1906.09629 (Acta Arith. 2021)
- Adegoke, A non-PSLQ route: https://arxiv.org/abs/1603.08209 ; novel approach to polylog constants: https://arxiv.org/abs/1603.05810 ;
  general binary bases (Adegoke, Oliver Lafont, Layeni): https://arxiv.org/abs/1603.07395 [SNIPPET only] ;
  golden ratio paper: https://arxiv.org/abs/1603.06307 [SNIPPET only]
- Zudilin, base 5: https://arxiv.org/abs/2409.10097
- Cloitre 2025: https://arxiv.org/abs/2507.20428
- Waldschmidt, Transcendence of periods: https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/TranscendencePeriods.pdf
- Wikipedia, Period (algebraic geometry): https://en.wikipedia.org/wiki/Period_(algebraic_geometry)
- MathWorld BBP-type formula: https://mathworld.wolfram.com/BBP-TypeFormula.html
- Adhikari-Saradha-Shorey-Tijdeman, Transcendental infinite sums, Indag. Math. 2001: DOI 10.1016/s0019-3577(01)80001-x [SNIPPET only]
- OEIS A088962, A207040 (Chamberland, JIS 2003) [SNIPPET]

Notes: Chamberland's 2003 JIS paper could not be fetched (404 on two URLs). Several arXiv, OpenAlex and
Semantic Scholar endpoint calls returned HTTP 429 (rate limited); Crossref and zbMATH worked.
No page contained instructions addressed to me. Zero text in this report quotes a source
for more than 15 words (one quotation only: "as far as anyone can tell").

## 7. Search log

WebSearch (6): 
1. BBP-type formula which constants have digit extraction base b logarithms classification
2. Borwein Borwein Galway "Finding and excluding b-ary Machin-type..." pdf
3. Lagarias normality of arithmetical constants BBP two bases G-function
4. e in Q-bar span of logarithms Baker Schanuel e not a period Waldschmidt
5. Barsky Munoz Perez-Marco On the genesis of BBP formulas arXiv
6. BBP pi sqrt(2) / sqrt(3) base 3 / base 8 Adegoke Lafont general bases

Endpoint / fetch queries (numbered):
1 arXiv API all:BBP+formula (429); 2 OpenAlex "BBP-type formula digit extraction" (429); 3 Crossref "BBP-type formulas
constants"; 4 Semantic Scholar BBP (429); 5 zbMATH "BBP formula"; 6 arXiv abs math/0106230 (wrong paper);
7 arXiv API abs:BBP (429); 8 tandfonline Lagarias (403); 9 Crossref Lagarias normality; 10 Crossref Kristensen
Mathiasen (429); 11 Crossref digit extraction logarithm BBP Adegoke; 12 Crossref Chamberland cyclotomic;
13 Crossref ASST (429); 14 Crossref Chan BBP (429); 15 zbMATH BBP Adegoke; 16 zbMATH Baker logs digit extraction
(404); 17 OEIS BBP digit extraction; 18 Wikipedia Period (algebraic geometry); 19 Crossref Takahashi;
20 zbMATH Machin-type (404); 21 zbMATH polylog constants (404); 22 Crossref Adegoke arctangent general bases;
23 MathWorld BBP-type; 24 zbMATH "BBP formula logarithm"; 25 zbMATH "BBP normal numbers"; 26 Crossref Bailey Crandall;
27 Crossref pi sqrt 3 ternary; 28 Crossref Catalan Clausen (429); 29 OEIS "BBP log 2 base 9"; 30 OEIS Gaussian Mersenne BBP;
31 GitHub repositories BBP base 3 (0 results); 32 Crossref ASST retry; 33 Crossref golden ratio Fibonacci log arctan;
34 Crossref Craig-Wood Euler (429); 35 zbMATH Hypothesis A; 36 zbMATH linear forms logs infinite series;
37 Crossref transcendence infinite series Tijdeman (429); 38 Cambridge PDF (BBG) read; 39 arXiv PDF Lagarias read;
40 arXiv PDF 2208.07696 read; 41 arXiv PDF 1906.09629 read; 42 arXiv PDF 2409.10097 read; 43 arXiv PDF 1603.08209 read;
44 arXiv HTML 2507.20428 read; 45 Waldschmidt PDF read; 46 Bailey Compendium PDF read (3 fetches); 47 ar5iv 1603.05810 read;
48 Bailey "BBP algorithm for pi" PDF (saved, skimmed only); 49 Chamberland JIS (404 x2); 50 other failed URLs
(carma.newcastle host not found; Lagarias umich 404; cmi.ac.in 404; Google 0 results).
Totals: WebSearch calls: 6. Endpoint queries (items 1-37 are search-endpoint queries, 37 of them): 37, plus about 13 direct page or PDF reads.
