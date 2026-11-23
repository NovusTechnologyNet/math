# P06: Machin-type arctangent formulas for pi

Thread report, 22 November 2026. Marks: [READ] read on the source's own page/PDF, [SNIPPET] seen only in a
search result, abstract or API record, [INFERRED] my own conclusion.

## 1. Summary

1. Two terms, integer arguments: Stormer 1895 proved that exactly four relations x1 arctan(1/m1) + x2 arctan(1/m2) = pi/4
   exist (rational x_k, integers m_k >= 2): Machin, Euler, Hermann, Hutton. This is a complete theorem, not a computation. [READ]
2. Three terms: Yamada (arXiv 1811.09273, v6 March 2025) proves only FINITELY many nondegenerate three-term relations exist, with
   astronomically large explicit bounds (x_i < exp(8.8e9) in the worst case). No complete list is known. Stormer 1896 gave
   a criterion plus 102 three-term formulas (per Yamada). The question "infinitely many?" was Stormer's, answered by Yamada. [READ]
3. For four or more terms nothing is proved: finiteness for each length is explicitly an open question (Craig-Wood 2025, Question 4.3). [READ]
4. Gasull-Luca-Varona 2023 (Indag. Math. 34): complete list of two-term relations with arguments b/2^a: ten sporadic
   solutions plus two parametric families. Also two-term formulas with arbitrarily small Lehmer measure, and a corrected
   classification (16 identities) for golden-section powers. All proved. [READ]
5. Formalization: Mathlib has the four two-term formulas (Machin, Euler, Hermann, Hutton) as lemmas (PR 9847, merged Feb 2024).
   No formalization of Stormer's classification, of Yamada, or of Gaussian-integer criteria found in Lean, Coq or Isabelle. [SNIPPET/INFERRED, "not found"]
6. Machin-type BBP (Borwein-Borwein-Galway 2004) is the nearest neighbour to the project's results. Their problem (2),
   "how many Q-linearly-independent binary Machin-type BBP arctangent zero relations exist", may now be answered by the project's counts. [READ, INFERRED]
7. Best leads: (A) a certified exhaustive enumeration of all Machin-type relations of every length with arguments x <= X (Stormer
   criterion in Z[i]; days; 24 cores); (B) formal proof in Lean of Stormer's two-term theorem (weeks, needs Ljunggren-type input);
   (C) all-rational-arguments two-term classification (open? see section 3).
8. Recent activity 2025-26 is computational/applied: Craig-Wood (PSLQ + Gaussian filter, new 5- and 6-term records lambda 1.4572, 1.3291),
   Farhi (refinement by continued fractions, Jan 2026), Kroesche-Littlejohn-Reinhart "Carl Stormer and his Numbers" (Nov 2025). [READ/SNIPPET]

## 2. What is known

### 2.1 Definitions and the Gaussian-integer criterion
- An n-term Machin-type formula: y1 arctan(1/x1)+...+yn arctan(1/xn) = r pi/4 with integers, r != 0. [READ, Yamada]
- Stormer's criterion (1896): for given integers x_i > 1, a relation exists iff the numbers (x_i + i)/(x_i - i) satisfy a multiplicative
  dependence in Z[i] modulo units, i.e. (x_i+i)/(x_i-i) = unit * product of powers of n-1 Gaussian integers; equivalently
  x_i^2+1 = 2^v * m_1^a * ... * m_{n-1}^b with compatibility conditions. This turns the transcendental question into a question
  on exponent vectors of Gaussian primes. [READ, Yamada intro, eqs (11)-(15)]
- The same Z[i] technique is used in Borwein-Borwein-Galway (BBG) section 2 (they spell the pi/4 congruence mod pi as a product of (a+i)^e being a negative rational);
  they say Stormer used it in 1897 to settle Graves' problem (exactly four integer solutions of m arctan(1/u) + n arctan(1/v) = k pi/4). [READ]

### 2.2 Two terms
- Stormer 1895 ("Solution complete en nombres entiers m, n, x, y, k de l'equation m arctg 1/x + n arctg 1/y = k pi/4"): only (1)-(4). [READ via Yamada refs and Gasull et al.]
  Key inputs needed in the proof: Lebesgue (x^m = y^2+1 impossible), Ljunggren (X^2+1 = 2Y^4 has only 1, 239) [READ, Yamada refs 8, 9, 12].
- Gasull-Luca-Varona Theorem 1: all solutions of x1 arctan z1 + x2 arctan z2 = pi/4 in nonzero rational x_k, rational z1<z2 in (0,1) of the form 2^a/b or b/2^a:
  ten sporadic quadruples (e.g. (-1,1/239,4,1/5), (1,1/41,2,1/5)-type...) and two parametric families, in a2 in N:
  (1, 2^(a2)/(2^(2a2+1)+1)... see paper eq. in Theorem 1). Proof uses the Z[i] route plus the known solutions of x^2+1 = 2y^n and x^2+2^a = y^n (n>=3). [READ, abstract and theorem; exact families are garbled in my text extraction, take them from the paper]
- Same paper, section 3 ("Machin's formula machine", rational functions R_j(n,x)): produces infinitely many N-term relations; for N=2
  gives two-term formulas n arctan(1/b1) - arctan(a2/b2) = pi/4 with Lehmer measure less than any epsilon>0 (Theorem 3, via continued fraction convergents of pi). [READ]
- Section 4 (golden section): classifies x1 arctan(tau^a)+x2 arctan(tau^b) = rational pi: essentially sixteen identities. This corrects an
  oversight in Luca-Stanica (the case (5,1) with opposite signs was missed). Proof by prime ideals in Q(i, sqrt 5) and primitive divisors of Fibonacci/Lucas. [READ]
  [INFERRED] This is the same toolkit as the project (primitive divisors, ideals in a biquadratic field).
- Alferov (arXiv 2403.09654, Nov 2023) and Abrarov-Quine (arXiv 1706.08835) also give constructions with arbitrarily small Lehmer measure
  (Abrarov-Quine: lambda about 0.2453 for a two-term formula with 2^(k-1) arctan(1/u1)+arctan(1/u2), k=27, u1=85445659). [READ abstract / SNIPPET]
  The two-term formulas with huge, non-small-height rational arguments are not "Stormer-type" (arguments a/b not 1/m).

### 2.3 Three terms
- Yamada 2018 (v6 2025): "only finitely many three-term Machin-type formulae not arising from linear combinations of the four two-term ones" with explicit bounds
  (Theorem 1.1: cases by size of m1 m2 vs 10^10; e.g. m2 < e^40000 in one case, x_i < exp(8813999998) in another, |y_i| < 4.5e18). Tools: lower bounds for linear forms in
  three logarithms (Mignotte-Voutier), two logarithms (Laurent), Ramanujan-Nagell type equations, Evertse S-units. Computation in PARI/GP. [READ]
- Known nontrivial three-term relations (Yamada): Simson 1723 (8 arctan 1/10 - arctan 1/239 - 4 arctan 1/515 = pi/4); Gauss 1863 (12,8,-5 with 18, 57, 239);
  and the Wrench-attributed (5 arctan 1/2 + 2 arctan 1/53 + arctan 1/4443 = 3pi/4) and two relatives. Yamada says the Wrench formulas cannot be found in Wrench 1938. [READ]
- Stormer 1896 (Arch. Math. Naturv. 19, 96 pages): criterion for any n and 102 three-term formulas (Yamada's count). [READ, secondary]
- Stormer asked whether there are infinitely many other three-term formulas. Yamada answers negatively (finite). [READ]
- Todd 1949 (Amer. Math. Monthly 56, "A problem on arc tangent relations") and Lehmer 1938 ("On arccotangent relations for pi", Amer. Math. Monthly 45): both exist and are the classical sources
  for relations among Stormer numbers; I did NOT read them. [SNIPPET: Crossref record, references of the 2023 paper]
  Todd's process (reduce arctan(a/b) to 1/x terms) is "enhanced" by Wetherfield (Math. Gaz. 80, 1996). [SNIPPET, Wikipedia + Craig-Wood]

### 2.4 Four terms and more, record formulas
- Craig-Wood (arXiv 2508.08307 v2): table of best known Lehmer measures by length: 2: 1.851 (Machin), 3: 1.786 (Gauss), 4: 1.586 (Stormer), 5: 1.457 (new), 6: 1.329 (new),
  7: 1.340 (Wetherfield 2004), 8: 1.416, 9: 1.414 (Wetherfield 2009), 10-15 new. The search is NOT exhaustive; PSLQ plus Gaussian-integer filters; arguments x < 2^64. No completeness or
  optimality claim for any length. [READ, through summary of the HTML]
  (Older record quoted in Wikipedia and Gasull et al.: six terms lambda = 1.51244, Chien-Lih 1997.) [READ]
- Wikipedia (Machin-like formula): "exactly four solutions" with two terms and numerators 1; no classification for three or more; Stormer 4-term 1896 formula
  (44,7,-12,24 with 57, 239, 682, 12943; primes 2,5,13,61) used in the 2002 record computation; Chien-Lih 6-term (primes 2,5,13,229,457,1201). [READ]
- Reducibility: A005528 (Stormer numbers: largest prime factor of n^2+1 at least 2n) and A002312 (arc-cotangent reducible numbers); OEIS cites Everest-Harman for a conjectured growth
  law; Kowalski Monthly article on reducibility of arctangents of integers. [SNIPPET, OEIS]
  Meaning: if n is a Stormer number, arctan(1/n) is not a Q-combination of arctan(1/m) with m < n, so n can appear in a relation only with other large partners. [INFERRED, standard]
- Kroesche-Littlejohn-Reinhart, "Carl Stormer and his Numbers" (arXiv 2511.03030, v3 April 2026): necessary and sufficient conditions for n to be a "Stormer number" of a prime p = 1 mod 4 (smallest x0 with x0^2 = -1 mod p),
  history of Stormer's pi work. [SNIPPET abstract]. Different notion from OEIS "Stormer numbers" (same man, different object). [INFERRED]

### 2.5 Borwein-Borwein-Galway 2004 (Canad. J. Math. 56, 897-925)
- Defines Machin-type BBP formulae pi = sum a_m arctan(-b^-m) (and for b=2 also terms arctan(1/(1-2^m))); proves pi has none for b=2 [as stated in their abstract]; and
  Theorems 1-2 exclude many generators via primitive divisors (Bang/Zsigmondy) and p-adic/ord homomorphisms on Z[i]. [READ]
- Section D "Comments and Research Problems" (all stated as open there): (2) how many Q-independent binary Machin-type BBP arctangent zero relations exist and are there good upper bounds;
  (3) can the first BBP formula for pi, pi = sum (4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6)) 16^-k, be derived from Machin-type generators (they say it does not appear to be a Q-combination);
  (4) infinitely many bases b without Machin-type formula via Chebotarev?; (6) combine with PSLQ; (7) effective Zsigmondy over Q(i) via Bilu-Hanrot-Voutier for number fields; (9) generalize BBP to Gaussian base b in Z[i]. [READ]

### 2.6 Formalization
- Mathlib: Real.arctan_add, two_mul_arctan, and the four Machin-like lemmas arctan_inv_2_add_arctan_inv_3, two_mul_arctan_inv_2_sub_arctan_inv_7, two_mul_arctan_inv_3_add_arctan_inv_7,
  four_mul_arctan_inv_5_sub_arctan_inv_239 (PR 9847 by Parcly-Taxel, merged 14 Feb 2024; item "Machin" in the 100-theorems tracker #6091). [READ]
- Not found (searches: GitHub repos for "machin formula lean", "machin arctan pi coq/isabelle/lean4", Mathlib issues "machin arctan", AFP search page (empty result), one WebSearch): any formalization of Stormer's classification, of Yamada, of
  the Z[i] criterion, or Machin-type BBP exclusion. GitHub code search needs authentication (401). "Not found" is weak evidence. [INFERRED]

## 3. What is open

1. Complete list of three-term Machin-type formulas. Finite (Yamada) but with bounds around exp(10^10), so no list; whether only the 102+3 known are all is not settled. Source says finiteness is new, and
   lists as known only Simson, Gauss, Wrench-type relations beyond the two-term ones. [READ; open status = Yamada's intro and the fact that no enumeration is claimed]
2. Finiteness for each length n >= 4 (Craig-Wood Open Question 4.3; also his conjecture "likely finite number of a given length"). [READ, stated as open by the source]
3. Optimal (smallest) Lehmer measure for each length, and whether the infimum over all lengths is 0 for integer-argument (1/x) formulas. Two-term with general rational arguments gets arbitrarily small (Gasull et al., Alferov, Abrarov-Quine); for formulas with ALL arguments 1/x_i
   the best known is 1.3291 (6 terms, Craig-Wood). Whether lambda has a positive lower bound for 1/x formulas: not found stated. [INFERRED/not found]
4. Craig-Wood Question 4.1: relations with arctan(a/b), a != 1, are under-explored. [READ]
5. Stormer-number side: Everest-Harman asymptotics of Stormer numbers conjectured, not proved. [SNIPPET, OEIS]
6. Classification of all two-term relations a*arctan(r) + b*arctan(s) = pi/4 with arbitrary rational r, s, a, b: I found no statement that this is classified; the families in section 3 of Gasull et al. show infinitely many exist, and
   the classification of those in which numerator is 1 (Stormer) and in which denominator/numerator is a power of 2 (Gasull et al.) are the two solved subfamilies. The general case is a two-variable problem in Z[i]:
   (a+i)^p (b+i)^q ~ unit * (1+i)^t * (rational), unbounded height, so it is not a finite-list question. [INFERRED]
7. BBG problems (2), (3), (4), (6), (7), (9) above. [READ, stated as open in 2004]
8. Wetherfield's "Todd's process" and the Lehmer-Todd literature produce relations but have no completeness statement. [SNIPPET]

## 4. Leads for this project, ranked

### Lead A (best): certified exhaustive census of Machin-type relations below a bound
- Statement: "For every n and every set {x_1,...,x_n}, 2 <= x_i <= X, determine all Q-linear relations among arctan(1/x_i) and pi/4; list all that are minimal (circuits)", for X = 10^9 or larger,
  with the output verified exactly in Z[i] (products of Gaussian integers) and the rank statement checked. In particular: "the complete list of three-term relations with all x_i <= X" and "four-term with x_i <= X".
- Why the toolkit fits: Stormer's criterion is an exact linear-algebra statement on the Gaussian-prime valuation vectors of x_i + i; the project already uses prime ideals in cyclotomic fields, exact enumeration, LLL.
  Algorithm [INFERRED]: sieve the factorization of x^2+1 for x <= X (segmented, 24 cores); each odd Gaussian prime of norm p dividing x^2+1 must appear in at least two of the x_i of a minimal relation (otherwise its valuation cannot cancel);
  so discard x with a prime factor p >= 2x ("Stormer numbers", A005528: these can only occur paired with larger partners), then do rank computations over the hypergraph of remaining x. Relations among n elements of bounded size reduce to small
  integer-matrix kernels. Cross-check with an independent PSLQ run, and certify a final list by exact Z[i] multiplication in Lean/Python. For X = 10^7 trivial (hours), 10^9-10^10 feasible (days) with ~63 GB.
- Missing: efficient factoring to 10^10 (sieve is fine); large Stormer-number partners (a relation can involve a very large x; the bound X limits only the search, the census is "complete below X").
- Size: days. Notice: gives the first rigorous public table of all 3-term and 4-term relations with bounded arguments, which the literature states only as finite (3) or open (4+); Craig-Wood explicitly says his search was not exhaustive; Yamada's finiteness bounds do not give a list.
  Check that the 102 + Stormer 1896 three-term formulas (and Wrench-type) are reproduced.

### Lead B: formal proof of Stormer's 1895 two-term theorem in Lean
- Statement: if x1, x2, rational coefficients, integers m1,m2 >= 2 with a1 arctan(1/m1)+a2 arctan(1/m2) = pi/4 (a_i != 0, m1 != m2), then (a1,m1,a2,m2) is one of the four classical solutions (up to order).
- Fit: Mathlib has the Gaussian integers (norm-Euclidean, UFD), the four formulas, arctan addition. Reduction to x^2+1 = 2^v m^k leads to Lebesgue (x^2+1 = y^n has only trivial solution, proof via Z[i] is elementary and
  formalizable) and Ljunggren (x^2+1 = 2y^4: x = 1, 239; Steiner-Tzanakis proof uses Baker; the project has Baker imported, so an effective-bound plus finite check is conceivable).
  Alternative: avoid Ljunggren using a modern Mignotte-style argument? Not found; INFERRED.
- Missing: x^2+1=2y^n for n>=3 (Cohn 1996 uses modular methods, out of reach); for n=4 Ljunggren is enough only for the two-term case with integer arguments, so that restricted statement is feasible.
- Size: weeks (Lebesgue plus Z[i] criterion plus Ljunggren via Baker). Notice: first formalized classification theorem in this area; consistent with "Machin proofs exist, classification proofs do not" (not found).

### Lead C: formalize Stormer's criterion (the equivalence with Z[i] factorization) as a general theorem
- Statement: for integers x_i > 1, there is a nonzero rational relation among arctan(1/x_i) and pi iff (x_i+i)/(x_i-i) satisfy the multiplicative dependence in Z[i]/units.
- Fit: direct Mathlib (arg, Gaussian integers, UFD); pure algebra with unique factorization. Size: days to 2 weeks. Value: backbone for Lead A (certified output) and Lead D, and a base for a library of Machin results.
  Probably the cleanest first deliverable.

### Lead D: Machin-type relations over Q(sqrt d) or with golden-section arguments
- Gasull-Luca-Varona section 4 is exactly an S-unit / primitive-divisor computation in Q(i, sqrt 5) and found an oversight in a published proof (Luca-Stanica). Statement: classify all
  x1 arctan(alpha^a) + x2 arctan(alpha^b) = rational pi for other quadratic units alpha (silver ratio 1+sqrt 2, 2+sqrt 3, ...), or for any fixed unit of a real quadratic field. [INFERRED: not found in the literature I searched]
- Fit: primitive divisor theorem for Lucas sequences (the project already uses Bang/Zsigmondy and prime ideals in Kummer/cyclotomic fields). Size: weeks for a first case (silver ratio), plus a proof check. Notice: new family, extends published classification; also an independent check of the 2023 theorem (the 2023 text itself corrects a prior error, so a Lean check is valuable).

### Lead E: two-term formulas with rational arguments, structural classification
- Statement: for coprime a_i, b_i, all (a1/b1, a2/b2) with x1 arctan(a1/b1)+x2 arctan(a2/b2) = pi/4 in which a_i, b_i are supported on a given finite set S of primes: finitely many?; relation to S-unit equation in Z[i]. [INFERRED]
- Fit: S-unit equations (Evertse) in Q(i); needs effective Baker bounds (imported) and a certified search; Yamada's own three-term proof is the model. Size: weeks to months. Value: would complement Gasull et al.'s 2-adic case with arbitrary prime sets; not found in literature.

### Lead F: BBG problem (2) and (3), binary Machin-type zero relations
- Statement: BBG ask for the number of Q-independent binary Machin-type BBP zero relations, and whether (63) (Bailey-Borwein-Plouffe's first formula) follows from Machin-type generators. [READ] The project's Base-2 classification (dimension 13 for the full class, 8 for rational multiples) and zero-relation counts
  probably answer (2) for the degree-1 class with weights 2^(-floor(k/2)). [INFERRED]. Worth stating explicitly in any write-up as "answers BBG Problem D(2) in the class considered", after checking that their class (arctan generators only) is a subclass. Size: days (reading plus comparing the two classes).

### Not recommended
- Finiteness of N-term formulas for N >= 4: out of reach (even N=3 needs three logarithms and gives astronomical bounds).
- Best Lehmer measure: computational race (Craig-Wood, Wetherfield); no proof content, and 1.3291 is already a heuristic frontier.

## 5. Overlap or conflict with the results in the project summary

- No conflict found. BBG 2004 proves non-existence only within "Machin-type BBP" formulas; the project's statement ("that paper proves only the Machin-type case and poses the general case as a question") matches
  what I read: their abstract defines the formulas as sum a_m arctan(-b^-m), (b > 2, b not a proper power; for b = 2 extra terms), and concludes "pi has no Machin-type BBP arctangent formula when b = 2".
  [CAUTION, READ] The abstract says "no Machin-type BBP formula for pi when b = 2" while the project's classification says pi HAS binary degree-1 formulas (Huvent etc.) -- there is no conflict, because those are not in BBG's Machin-type subclass (BBG item (3) says exactly this about BBP's first formula).
- BBG problem D(2) (count of independent binary Machin-type zero relations) overlaps the project's zero-relation counts; I have not compared the two counts.
- Gasull-Luca-Varona's (and Luca-Stanica's) use of primitive divisors and prime ideals in Q(i, sqrt 5) overlaps in method with the project's toolkit, not in result.
- Page notices: each OpenAlex response carried a notice asking an AI agent to create an API key by sending the user's e-mail address. Ignored.

## 6. Sources

- https://ddd.uab.cat/pub/artpub/2023/289990/indmat_a2023m11v34n6p1373-1396.pdf ; arXiv 2302.00154 (Gasull-Luca-Varona), read in full text extraction (partly garbled)
- https://arxiv.org/pdf/1811.09273 (Yamada, Three-term Machin-type formulae, v6), read first 170 lines plus references
- https://arxiv.org/html/2508.08307v2 (Craig-Wood, Constrained PSLQ search), read via summarizer
- https://arxiv.org/abs/2601.10300 (Farhi, refinements of two-term Machin-like formulas); https://arxiv.org/abs/2511.03030 (Kroesche et al.); https://arxiv.org/abs/1706.08835 (Abrarov-Quine); https://arxiv.org/pdf/2403.09654 (Alferov)
- https://doi.org/10.4153/CJM-2004-041-2 (BBG), read PDF text incl. section "Comments and Research Problems"
- https://en.wikipedia.org/wiki/Machin-like_formula ; https://en.wikipedia.org/wiki/St%C3%B8rmer%27s_theorem
- https://oeis.org (A005528, A002312, A071931 via search)
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.html ; https://github.com/leanprover-community/mathlib4/pull/9847
- Crossref: Todd 1949 DOI 10.1080/00029890.1949.11999434; Chien-Lih 1997 DOI 10.2307/3618793
- Not read, to fetch next: Calcut, "Gaussian integers and arctangent identities for pi", Amer. Math. Monthly 116 (2009) 515-530 (cited by Yamada; elementary Z[i] treatment); Stormer 1895/1896 originals; Wetherfield/Chien-Lih list site (archive.org refused); Lehmer 1938; Todd 1949.

## 7. Search log

WebSearch (2 calls):
 W1. "Gasull Luca Varona two-term Machin-type formulas arctan b/2^a Indagationes Mathematicae"
 W2. "Machin-like formula pi arctangent Isabelle OR Coq OR Lean formalization proof Stormer classification"

Endpoint / fetch queries (42 attempted, 35 returned content; refusals marked):
 1 OpenAlex search "Machin-type formulas arctangent pi"
 2 arXiv API all:"Machin-type" (HTTP 429)
 3 Wikipedia Machin-like formula
 4 MathWorld MachinLikeFormulas (404)
 5 arXiv PDF 2302.00154 (saved, read via pdftotext)
 6 OpenAlex cites W4385076198
 7 Crossref "Stormer arc tangent relations three terms"
 8 Semantic Scholar search (429)
 9 zbMATH API "Machin arctangent relations"
10 arXiv abs 2508.08307
11 OpenAlex "refinements of two-term Machin-like formulas"
12 OpenAlex "Stormer arccotangent relations pi Lehmer Todd"
13 OEIS json "Machin arctan Stormer" (null)
14 GitHub repos "machin formula lean"
15 arXiv abs 2601.10300
16 OEIS text "Machin-like arctan"
17 GitHub repos "machin arctan pi coq OR isabelle OR lean4"
18 GitHub issues mathlib4 "machin arctan"
19 Mathlib docs Arctan.html
20 OpenAlex BBG title
21 OEIS "Stormer numbers"
22 Wikipedia Stormer's theorem
23 CECM Borwein home page (403)
24 BBG PDF (cambridge.org, saved, read)
25 arXiv PDF 2403.09654
26 GitHub PR mathlib4 #9847
27 OpenAlex "Kowalski reducibility of arctangents of integers"
28 Crossref "Chien-Lih More Machin-type identities"
29 arXiv HTML 2508.08307v2
30 arXiv PDF 1706.08835
31 OpenAlex "arc cotangent irreducible numbers Stormer Everest Harman"
32 OpenAlex "Machin formula arctangent Gaussian integers S-unit linear forms logarithms"
33 zbmath.org web search (403)
34 OpenAlex W2900754802 (Yamada)
35 arXiv abs 2511.03030
36 arXiv abs 1706.08835
37 curl of arXiv PDF 1811.09273 (arXiv, read)
38 OpenAlex "Gaussian integers and arctangent identities for pi Calcut" (Calcut record not returned; related papers only)
39 OpenAlex cites W2900754802 (Yamada has 2 citing works: Yamada 2025 note, Farhi 2026)
40 GitHub code search (401)
41 Isabelle AFP search page (empty)
42 web.archive.org machination page (refused by fetch tool)

Totals: WebSearch calls = 2. Endpoint queries = 42 attempted (35 successful, 7 refused or empty).
