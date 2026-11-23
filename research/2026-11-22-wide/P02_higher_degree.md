# P02: BBP-type formulas of degree 2 and higher (polylogarithmic)

Helper report, 22 November 2026. Marks: [READ] = read on the source's own page or PDF,
[SNIPPET] = seen only in a search result, abstract or API record, [INFERRED] = my own conclusion.
Convention: P(s,b,N,a) = sum_{k>=0} b^(-k) sum_{i=1..N} a_i/(Nk+i)^s; s is the degree.

## 1. Summary

1. Degree-2 formulas are known in base 2 (and powers of 2) for pi^2, log^2 2, Catalan's G,
   G - log(2)/8-type combinations, pi*log 2, Cl_2(pi/3); in base 3 (powers of 3) for pi^2, log^2 3,
   pi*sqrt(3)*log 3, sqrt(3)*Cl_2(pi/3). Degree 3 to 5 are known in base 2 (zeta(3), zeta(5),
   log^3 2, ... up to degree 5) and degree 3 to 5 in base 3 (zeta(3), Cl_4, zeta(5), ...). [READ]
   (Bailey Compendium; Adegoke 2011, 2016.)
2. All of them are proved or found by explicit polylogarithm ladders (Kummer/Abel/Coxeter-type
   functional equations); many were first found by PSLQ and proved later by Adegoke. [READ]
3. I found NO theorem of non-existence for any BBP-type formula of degree >= 2 in any base
   (searches listed below). In print, the closest are: Borwein-Borwein-Galway 2004 (degree 1,
   Machin-type only) and Bailey's remark that the pattern of zero relations is "not understood". [READ]
4. [INFERRED] A BBP sum of degree s is a Q(zeta_N, b^(1/N))-linear combination of Li_s at the N
   points w with w^N = 1/b. So non-existence statements are statements about linear relations
   among polylog values at algebraic points, i.e. periods; the only tool in the project
   (Baker) covers weight 1 only. Unconditional non-existence at degree 2 looks out of reach.
5. Unconditional linear independence of dilogarithm values is thin: Li_2(1/q), 1, log(q/(q-1))
   independent for integers q >= 6 (Rhin-Viola, Viola-Zudilin); irrationality of Li_2(1/2),
   Li_2(1/3), Li_2(1/4) is still open as of the 2026 literature I saw (a September 2026
   arXiv preprint by Prellberg claims Li_2(1/5), Li_2(-1/4), Li_2(-1/3)). Even Li_2(1/2) =
   pi^2/12 - log^2(2)/2 irrational is open. [READ/SNIPPET]
6. Conjecturally the whole question is governed by the Bloch group / symbol (Zagier,
   Goncharov); Zagier's polylogarithm conjecture is a theorem for weights 2, 3 and 4. But that
   concerns Dedekind zeta values, not the transcendence statement needed for non-existence. [SNIPPET/INFERRED]
7. Best concrete lead: a finite, exact, conditional (or "motivic") classification of degree-2
   sums for fixed (b,N) via the symbol map into wedge square of S-units of the Kummer field,
   checkable against Bailey's Table 1 zero-relation counts for s = 2. Fits the project's
   prime-ideal toolkit. Days to weeks.
8. Second lead: Lean formalisation of Bailey's degree-2 binary and ternary formulas (all
   points lie inside the unit disc, so power series and differentiation suffice); Mathlib seems
   to have no dilogarithm. Weeks.
9. A heuristic explanation (mine, to be checked) why bases 2, 3 (and 4) are special for degree 2:
   the points with 1-w = conj(w), |w|^2 = 1/b exist exactly for b <= 4.
10. Nothing found that conflicts with section 1 of the rules file. One overlap: Barsky-Munoz-
    Perez-Marco restrict to degree 1 and leave higher degree open.

## 2. What is known

### 2.1 Which constants have formulas of degree >= 2

- Broadhurst 1998 (arXiv math/9803067): proves digit extraction (base 2, in
  hexadecimal form, time O(d log^3 d), space O(log d)) for Catalan's G, pi^3, log^3 2, zeta(3),
  pi^4, log^4 2, log^5 2, zeta(5) and six products of powers of pi and log 2; pi, log 2, pi^2,
  log^2 2 were already known (Bailey-Borwein-Plouffe). Method: polylogarithm ladders with
  Kummer's functional equations at z^8 = 16^(-p), p = 1,3,5, reduced by computer algebra, up to
  order 11; a p = 5 generator is an unresolved "impasse"; zeta(7), zeta(9), zeta(11) only appear
  combined with products of pi and log 2. [READ: ar5iv text and arXiv abstract]
  Degree-2 generators there: pi^2 = 32 S_{2,1}(1,-1,-1,-2,-1,-1,1,0); G = 3 S_{2,1}(...) - 2 S_{2,3}(...)
  (period-8 coefficient vectors, weights 2^(-floor((pk+p)/2)) k^(-n)). [READ]
- Broadhurst, hep-th/9803091 (Eur. Phys. J. C 8, 1999): a new set SC*(3) of constants "of base 3"
  (from 3-loop massive tetrahedron diagrams, sixth roots of unity, Cl_2(pi/3)^2 appears). [READ abstract]
- Bailey, "A Compendium of BBP-Type Formulas" (2006 version, local copy read): section 5 degree-2
  binary formulas (29)-(39): pi^2 (base 2^4 length 8; base 2^6 length 6), log^2 2 (two), G - log2/8 type,
  pi*log 2 and Cl_2(pi/3)-type formulas, G in base 2^12 length 24 (formulas 38, 39; 39 by Huvent);
  section 6 degree 3 (zeta(3), log^3 2, pi^2 log 2 ... in bases 2^12 and 2^60); section 7 degree 4
  (Cl_4 etc.); section 8 degree 5 (zeta(5) in base 2^60, length 120). [READ]
  Section 9 "ternary": degree 1 (log 2, log 3, log 5, 7, 11, 13, arctan, pi*sqrt 3) and the
  higher-degree ones: formula 76 pi^2 (base 3^6, length 12), 77 log^2 3, 78 pi*sqrt3*log 3 (degree 2, base 3^6),
  79 (degree 3, base 3^2 length 2: involves zeta(3), log 3, log^3 3), 80, 81 (degree 4),
  82 (Cl_4(pi/3)-type, base -27), 83 (degree 5, zeta(5)). Credited to Broadhurst (69, 76-78)
  and Adegoke (79-83). [READ]
- Adegoke, Integers 11 (2011) = arXiv 1603.05810 (binary) and Notes Number Theory Discrete Math 17
  (2011) = arXiv 1603.04974 (ternary): proofs from polylog functional equations (Kummer's two-variable
  dilogarithm equation, Abel's equation, trilogarithm and degree 4/5 equations); proves
  formulas that had only been found by PSLQ; ternary degree 2 for pi^2, log^2 3, pi*sqrt3*log 3,
  sqrt3*Cl_2(pi/3); degree 3, 4, 5 ternary; two ternary zero relations. The binary paper states
  that no proved explicit binary digit-extraction formulas were known for zeta(3) and pi^2 log 2
  before it. [READ]
- Adegoke-Oliver Lafont-Layeni, "A class of digit extraction BBP-type formulas in general binary
  bases": families of formulas for pi*sqrt3, sqrt3*Cl_2(pi/3), polylog constants, logs of an infinite
  set of primes, binary zero relations. [SNIPPET: OpenAlex/zbMATH/Cambridge-linked abstract]
- Cloitre, arXiv 2508.03743 (Aug 2025): proof of a degree-2 BBP-type formula for pi^2 in base
  the golden ratio (found empirically 2004), via a geometric identity linking phi to fifth roots
  of unity; also a Machin-like formula for zeta(3). [READ abstract only]
  [INFERRED] This is the Coxeter/Landen ladder Li_2(rho^6) = 4 Li_2(rho^3)+3 Li_2(rho^2)-6 Li_2(rho)+7 pi^2/30,
  rho = 1/phi (stated on the Wikipedia polylogarithm page [READ]) turned into a BBP sum; non-integer base.
- Adegoke, golden ratio / Fibonacci BBP-type formulas (2014), and a binary formula for sqrt5*log phi (2016). [SNIPPET]
- Bailey's remark: Lagarias suggests special significance for constants with BBP formulas in
  two bases (e.g. 2 and 3), tied to G-functions and Furstenberg's x2,x3 conjecture. [READ]
- Catalan's constant and zeta(3) in base 3: I found no formula in print (Compendium ternary section has
  no G, no zeta(3) except in combination 79). [INFERRED from reading the section, not a proof]

### 2.2 Structure of a degree-s sum (needed for what follows) [INFERRED, elementary]

With z = b^(-1/N) and m = Nk+i one gets P(s,b,N,a) = sum_{m>=1} g(m) z^m / m^s with
g(m) = a_{m mod N} z^(-(m mod N)), periodic of period N. Expanding g in characters of Z/N,
P = sum_{j mod N} ghat(j) Li_s(zeta_N^j z), a Q(zeta_N, b^(1/N))-linear combination of Li_s at the
N points w with w^N = 1/b (all of modulus < 1, so only power series occur, no analytic continuation).
This is exactly the shape of the periodic-coefficient functions L(f,i,z0) = sum f(m) z0^m/m^i of
Mistiaen 2026 (below). Known formulas correspond to ladders: relations among such Li_s(w) from
the Kummer/Abel functional equations specialised at roots of unity and 2-power or 3-power radii.

### 2.3 Barsky-Munoz-Perez-Marco, "On the genesis of BBP formulas" (Acta Arith. 2021, arXiv 1906.09629)

Elementary procedure (from asymptotics of Gamma and Barnes functions) producing all classical
degree-1 BBP formulas for pi and log p, explaining rearrangements and "null" (zero) formulas
and the relation between log 2 and pi formulas (real and imaginary parts of one complex formula).
Explicitly restricted to degree 1; says extending to higher degree would be interesting; asks
whether all degree-1 null formulas come from their construction. [READ: arXiv text]

### 2.4 Non-existence

- Borwein-Borwein-Galway, Canad. J. Math 2004: pi has no b-ary Machin-type BBP arctangent
  formula for b != 2 (b not a proper power); authors say that when no Machin-type formula exists
  no BBP formula of any form is known. Degree 1 only; no statement for polylog constants. [READ abstract on Cambridge page]
- Bailey 2006: zero relations (BBP sums equal to 0) occur for certain (s,b,N) and not others; "it is
  not understood why"; Table 1 lists numbers of independent zero relations. For s = 2: (b,N) =
  (2^12,24): 2; (2^20,40): 1; (2^24,48): 2; (2^36,72): 2; (2^40,80): 1; (2^48,96): 2; (2^60,120): 4.
  For s = 3: (2^12,24): 1; (2^24,48): 1; (2^36,72): 1. [READ] Bailey also notes e is assumed
  "not polylogarithmic", used only as heuristic filler in PSLQ. [READ]
- I found nothing in print proving that pi^2 (or zeta(3), G, log^2 b) has no BBP formula in any
  base outside {2,3}-powers, nor any statement that the known list at degree 2 is complete. Searches:
  see log (BBP + nonexistence, Bloch, Zagier, motivic, Kummer field). This is "not found", weak evidence.
- Also open and unconditional hardness: the number pi^2/12 - log^2(2)/2 = Li_2(1/2) (a trivial degree-2
  N = 1 base-2 sum) has unknown irrationality (see 2.5); so general "no formula" proofs at degree 2
  cannot be obtained from irrationality or independence theorems currently in print. [INFERRED]

### 2.5 Linear independence / irrationality of dilogarithm and polylog values

- Hata (1993): rational approximations to Li_2; irrationality of Li_2(1/s) for integers s >= 7 and s <= -5 [SNIPPET,
  as quoted by Prellberg 2026; the Viola-Zudilin text quotes older ranges q >= 12 (Hata) and q >= 14 (Chudnovsky) in DHK].
- Rhin-Viola (Ann. Sc. Norm. Super. Pisa 2005, "The permutation group method for the dilogarithm"):
  1, Li_1(1/z), Li_2(1/z) linearly independent over Q for integers z >= 6 (permutation group method).
  Rhin-Viola 2019 (Moscow J. Comb. Number Theory 8): extension to negative x, linear independence of 1, Li_1(x), Li_2(x),
  integers z <= -5 in the range quoted by Prellberg. [READ Viola-Zudilin intro; SNIPPET for 2019]
- Viola-Zudilin (Crelle 736 (2018), MPIM preprint 2014-26): 1, Li_1(1/z), Li_2(1/z), Li_2(1/(1-z))
  linearly independent over Q for integers z >= 9 or z <= -8 and rationals z = s/r, 1 - s/r with
  1 < r < s, s large in comparison with r; quantitative forms (irrationality/independence measures).
  Miladi's thesis had z >= 11. [READ abstract and introduction]
- Marcovecchio (2009, two papers: "Linear independence of linear forms in polylogarithms",
  "The Rhin-Viola method for log 2"): linear independence of polylog values at algebraic points. [SNIPPET: titles via Crossref]
- David-Hirata-Kohno-Kawashima, "Can polylogarithms at algebraic points be linearly independent?"
  (Moscow J. 2020, arXiv 1912.03811); "Linear forms in polylogarithms" (Ann. Sc. Norm. Super. Pisa 2021,
  arXiv 2010.09167); "... generalized polylogarithms with distinct shifts" (Acta Arith. 2022, arXiv 2202.13931):
  Lerch functions Phi_s(x,z), criteria for linear independence of 1 and the values at several algebraic points
  alpha_j when the points are close to 0 at a fixed place (metric condition); Wronskian of Hermite-type
  Pade approximants. Qualitative; the points must be small, so they do not reach |w| = b^(-1/N)
  for small b and N. [READ abstract + intro of 1912.03811]
- Fischler, "Linear independence of odd zeta values using Siegel's lemma" (JLMS 2026, arXiv 2109.10136): at
  least 0.21 sqrt(s)/sqrt(log s) of 1, zeta(3), ..., zeta(s) are Q-independent; adapted to
  Li_1,...,Li_s at a fixed algebraic point in the unit disc, improving Rivoal and Marcovecchio. [READ abstract]
- Mistiaen (arXiv 2610.09774, Oct 2026): for nonzero periodic f of period N and algebraic z0 off
  certain half-lines, dim over Q(z0) of span of L(f,i,z0) = sum f(m) z0^m/m^i, i up to s, is at least of order
  sqrt(s/log s); covers |z0| > 1 by continuation. [READ abstract] [INFERRED] Applies to BBP sums with
  f(m) = a_{m mod N} z0^(-(m mod N)), z0 = b^(-1/N) (f valued in Q(z0)). It shows that BBP sums of
  increasing degree cannot all collapse into a bounded family, but says nothing about a fixed degree 2.
- Calegari-Dimitrov-Tang (arXiv 2408.15403): 1, zeta(2), L(2,chi_{-3}) linearly independent over Q (so
  L(2,chi_{-3}) irrational), by arithmetic holonomy bounds applied to a Zagier construction. [READ abstract]
  Relevant to base 3, where pi^2 and Cl_2(pi/3) (L(2,chi_-3) up to algebraic factor) occur together.
- Prellberg (arXiv 2609.06895, 7 Sept 2026, unrefereed): irrationality of Li_2(-1/4), Li_2(1/5),
  Li_2(-1/3), via Rhin-Viola and Viola-Zudilin constructions with "exact executable certificates". States that
  Li_2(1/s) for s in {-4,-3,-2,2,3,4,5} were recorded as unresolved in Calegari-Dimitrov-Tang (Remark 2.8.2, 15.2);
  hence as of its date Li_2(1/2), Li_2(1/3), Li_2(1/4), Li_2(-1/2) remain open. [READ intro]
- Tan-Zhang (arXiv 2611.01066, 31 Oct 2026, preprint): Li_2(p/q) irrational when q > (4e^4/27) p^3;
  Li_2(5/q) irrational for q >= 418. [READ abstract via arXiv page]

### 2.6 Governing conjectures (Bloch group, Zagier, Goncharov)

- Bloch group B_2(K): kernel-cohomology of A(K) -> wedge^2 K^*, [x] -> x wedge (1-x), A(K) = free
  group on K - {0,1} modulo the five-term relation; Bloch-Wigner D(z) = Im Li_2(z) + arg(1-z) log|z|, real analytic, five-term relation;
  volume of an ideal hyperbolic tetrahedron; Suslin: indecomposable K_3 and B_2 agree up to torsion/Z/2. [READ: Wikipedia Bloch group]
- Zagier's polylogarithm conjecture: zeta_F(n) is expressed via a determinant of values of the
  single-valued polylogarithm D_n on n-th Bloch group elements. Status: weight 2 theorem (Zagier; via Borel),
  weight 3 Goncharov (about 1993), weight 4 Goncharov-Rudenko (2018); Bourbaki survey Gangl-et-al. 2021
  (arXiv 2109.01702) treats recent progress. [SNIPPET: search-result summaries; I did not read the survey]
- [INFERRED] None of these is a transcendence statement. For BBP non-existence at degree 2 one needs:
  (a) the motivic claim that the symbol (coproduct component wedge^2 of S-units) detects all Q-relations among
  the motivic versions of the Li_2(w_j) modulo products of weight-1 periods (pi, logs) -- this is plausible
  unconditionally by Brown's theory of mixed Tate motives over Z[1/N] (I did not verify applicability to
  the Kummer field K = Q(zeta_N, b^(1/N)) with 1/b-units; for K with S-units one is in mixed Tate motives
  over O_{K,S}, where the motivic Galois group is known only when the relevant K-groups vanish/are controlled
  by Beilinson-Soulé, which is a conjecture in general; flag); and (b) the period conjecture (Grothendieck-
  Kontsevich-Zagier) to pass from motivic to numerical relations. The classical way to say this: Q-relations
  among Li_2(w_j) beyond functional-equation consequences are not expected.

## 3. What is open (precise statements)

O1. (Not stated as open in one place; assembled by me.) For which (b,N) and which rational vectors a is
    P(2,b,N,a) in Q-bar pi^2 + span{log p log q, pi log p}? Expected answer: those a whose
    symbol in K tensor wedge^2(S-units of K) vanishes (modulo Sym^2 part), but no theorem.
O2. Source: Bailey 2006 (stated as not understood): why zero relations of degree s occur for some (s,b,N)
    and not for others (Table 1 above). Also his observation that in most cases with a zero relation,
    non-trivial formulas exist with the same parameters. [READ]
O3. Source: Broadhurst 1998: whether lambda(n), beta(n) (e.g. beta(4), beta(5), zeta(7) alone) belong to the class
    of constants with digit extraction; his PSLQ search found no relation (coefficients below 300 digits
    for the order-11 set). [READ ar5iv summary] Genuinely open, stated as open.
O4. Source: Compendium section 9 and Adegoke 2016: no ternary BBP formula known for G or for zeta(3) alone; the
    ternary set at higher degree is small. [READ; "not found" for completeness]
O5. Irrationality of Li_2(1/2) = pi^2/12 - log^2(2)/2, and of Li_2(1/3), Li_2(1/4). Source: Prellberg 2026 citing CDT. [READ]
O6. Algebraic independence/linear independence of pi^2, log^2 2, pi log 2 beyond Gelfond-Schneider-level facts: pi^2 and log^2 2
    are Q-bar-independent by Gelfond-Schneider (my deduction: pi^2 = alpha log^2 2 would make pi/log 2 algebraic, whereas
    log 2/(i pi) is transcendental), but independence of products like log 2 log 3, log^2 2, ... over Q-bar is Schanuel-level. [INFERRED]
O7. Whether the base-3 and base-2 lists at degree 2 are complete; whether a degree-2 formula for pi^2 exists in any
    integer base not a power of 2 or 3 (e.g. 5, 6, 7, 10); no source claims either. [not found]

## 4. Leads for this project, ranked

### Lead A (best): symbol-kernel computation for degree 2, checked against Bailey's Table 1
Statement to compute: for each (b,N) (start with b = 2^m, 3^m and N up to 120; then b = 5, 6, 7, 10 and
other small bases, N up to a few dozen), build the Q-vector space V(b,N) of vectors a in Q^N, map
a -> symbol(P(2,b,N,a)) in K tensor wedge^2(O_{K,S}^* tensor Q) where S = primes above b(b-1)N, using the
Kummer-field prime-ideal and S-unit relations the project already uses for degree 1, and compute dim ker.
Prediction (conditional, motivic): dim ker modulo Sym^2 part counts the zero relations plus formulas for pi^2,
log^2 b, etc. Test: reproduce the s = 2 counts (2,1,2,2,1,2,4) of Table 1; predict which (b,N) at b not 2^m, 3^m have any
pi^2 / zero relation. A negative result for all small bases other than 2, 3, 4 would be strong conjectural evidence for
a degree-2 analogue of the degree-1 classification ("pi^2 has a formula in base b iff b is a power of 2 or 3"?).
Why it fits: exact linear algebra over cyclotomic/Kummer fields, prime-ideal valuations, no PSLQ needed. Missing: a
clean statement of the symbol map for Li_2 at points w with coefficients in K (Q-bar-linear Bloch-type space, not
only Q-linear) and the treatment of the pi^2 term (Li_2(1) and real-part issue), plus a conditional (not provable)
converse. Size: days for a first computation; weeks to write up honestly as "conditional on motivic/period
conjecture". Worth noticing: it would be the first explanation of the degree-2 zero-relation counts and a
concrete falsifiable prediction; if a (b,N) outside the known list shows a symbol-kernel element, PSLQ at high precision
could confirm a NEW degree-2 formula (the more valuable outcome).
Risk: the counts in Table 1 include "rewritings" (relations obtained by changing base b -> b^r, N -> rN), so
normalisation is needed; also dependence on whether Q-bar-coefficient symbol is the right invariant (Galois
descent to rational a gives a Q-subspace).

### Lead B: Lean formalisation of degree-2 formulas (pi^2 base 2^4/N=8; pi^2 base 3^6/N=12; log^2 2; G)
Statement: Bailey (29), (31), (33), ternary (76), (77), (78) as theorems about explicit series. Method:
(i) power series of Li_2(w) for complex |w| < 1 (Mathlib has zeta(2) = pi^2/6 and Complex.log; no dilogarithm
found: a GitHub code search for "polylog" in mathlib4 returned 0 files, weak evidence, a failed second
search for "dilogarithm"); (ii) prove Kummer/Abel two-variable identity by differentiating in a parameter
(identity of analytic functions on a polydisc, constants fixed at a point) specialised at the 8th/12th roots of unity
times 2^(-1/2) or 3^(-1/2). Adegoke's papers give the exact generators and substitutions. Size: weeks (the analytic
bookkeeping dominates, the identities are finite). Worth noticing: first machine-checked BBP formulas of degree >= 2 and the
pi^2 formulas. Not a new mathematical result.

### Lead C: degree-1 classification in non-integer algebraic bases (golden ratio, other quadratic units)
Statement: for which algebraic bases beta (e.g. phi, 1+sqrt 2, 2+sqrt 3) does a degree-1 formula
sum_j beta^(-Bj) sum_i a_i/(Nj+i) for a non-zero algebraic multiple of pi (or log of an algebraic) exist?
Evidence of such objects: Cloitre 2025 (degree 2 pi^2 in base phi), Adegoke (sqrt5 log phi in base phi). Tools
fit: Baker + prime ideals in Q(phi, zeta_N) (the project's degree-1 method works for any algebraic base once the
character-sum/unit structure is set up). Missing: the meaning of "digit extraction" for non-integer base (not needed for the
mathematical classification). Size: weeks. Worth noticing: extends the "|b| power of 2" theorem to algebraic bases and gives
the first systematic account behind Cloitre's formula.

### Lead D: check Cloitre and Adegoke's degree-2 constructions for the symbol-kernel prediction
Small, 1-3 days: verify that every proved degree-2 formula in Compendium (29)-(39),(76)-(78) has vanishing wedge^2 symbol
modulo Sym^2 (a sanity test of the framework of Lead A before scaling up).

### Lead E (low value, unconditional, days): N = 1 and N = 2 statements from Viola-Zudilin
For integer q >= 6, a Li_2(1/q) is not in Q + Q log(q/(q-1)) (from independence of 1, Li_1, Li_2 at 1/q).
So within degree-2 sums with N = 1 and base q >= 6, no value is a rational combination of 1 and log(q/(q-1)). This does not
exclude pi^2, so it does not answer the main question; I flag it only as the one unconditional theorem touching the family.

### Lead F (out of reach): unconditional non-existence of a degree-2 formula for pi^2 in a base like 5 or 10
Would require independence of Li_2 values at algebraic points from pi^2 and each other (open: even Li_2(1/2)'s
irrationality is). Not feasible with Baker-type tools.

## 5. Overlap or conflict with section 1 of the rules file

- No conflict. The rules file claims degree-1 results only; nothing in the sources contradicts them.
- Overlap: Barsky-Munoz-Perez-Marco (2021) reproduces degree-1 BBP formulas for pi and log p by an elementary construction but
  does not classify, and it asks whether all degree-1 null formulas arise from it. [READ] The project's complete classification
  in base 2 (dimension 13 and 8, all of period 120) answers a related question for the base-2 class with weights 2^(-floor(k/2))/k,
  and explains the s = 1 rows of Bailey's Table 1 (1, 1, 1, 1, 5, ... zero relations). [INFERRED, consistent with my reading of the table]
- Note on the claim in the rules file about Borwein-Borwein-Galway: confirmed that the abstract states only the Machin-type
  case ("pi has no Machin-type BBP arctangent formula when b != 2"). [READ]
- Possible small oversight in print: Compendium text calls the zero-relation pattern not understood (as in 2006 version); the
  project's degree-1 explanation is therefore genuinely new relative to it.

## 6. Sources

- Bailey, A Compendium of BBP-Type Formulas: https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf (read through local PDF text)
- Broadhurst: https://arxiv.org/abs/math/9803067 ; https://ar5iv.labs.arxiv.org/html/math/9803067 ; https://arxiv.org/abs/hep-th/9803091
- Adegoke: https://arxiv.org/abs/1603.05810 ; https://arxiv.org/abs/1603.04974 ; (golden ratio) OpenAlex W4402831587
- Adegoke-Oliver Lafont-Layeni: https://arxiv.org/abs/1603.07395
- Barsky-Munoz-Perez-Marco: https://arxiv.org/abs/1906.09629
- Borwein-Borwein-Galway: https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/finding-and-excluding-bary-machintype-individual-digit-formulae/BB7919C8E1AE66878AE8D7BC7F0EBFA3
- Cloitre: https://arxiv.org/abs/2508.03743
- Viola-Zudilin: https://archive.mpim-bonn.mpg.de/1914/1/preprint_2014_26.pdf ; doi 10.1515/crelle-2015-0030
- Rhin-Viola 2019: https://msp.org/moscow/2019/8-1/moscow-v8-n1-p08-s.pdf ; Rhin-Viola 2005 doi 10.2422/2036-2145.2005.3.02
- David-Hirata-Kohno-Kawashima: https://arxiv.org/abs/1912.03811 ; https://arxiv.org/abs/2010.09167 ; https://arxiv.org/abs/2202.13931
- Fischler: https://arxiv.org/abs/2109.10136 ; Mistiaen: https://arxiv.org/abs/2610.09774
- Calegari-Dimitrov-Tang: https://arxiv.org/abs/2408.15403
- Prellberg: https://arxiv.org/abs/2609.06895 ; Tan-Zhang: https://arxiv.org/abs/2611.01066
- Marcovecchio: doi 10.4064/aa139-2-5 and 10.2422/2036-2145.2006.1.01
- Zagier conjecture survey: https://arxiv.org/abs/2109.01702 ; Zagier 1991 doi 10.1007/978-1-4612-0457-2_19 ; Goncharov-Levin doi 10.1007/s002220050228
- Wikipedia: Bloch group, Polylogarithm, Lerch zeta function
- Loxton, Special values of the dilogarithm function, Acta Arith. 43 (1984), doi 10.4064/aa-43-2-155-166 (title only seen; not read)

Page-instruction note: OpenAlex responses contained a notice inviting an automated agent to create an API key by submitting an e-mail address;
ignored, nothing submitted.
Unreliable/unrelated hits: arXiv 1905.04388 and math/0012104 (my guessed ids) were unrelated papers; discarded.

### Search log
WebSearch (4 of 6 used):
W1. BBP-type formulas polylogarithmic constants degree 2 Catalan zeta(3) base 2 base 3 Broadhurst
W2. Viola Zudilin "Linear independence of dilogarithmic values" arXiv Li_2(1/z) irrationality measure Rhin Viola Hata
W3. Zagier polylogarithm conjecture status proved n=2 n=3 Goncharov ... Bloch-Wigner relations
W4. BBP-type formula non-existence conjecture polylogarithm motivic mixed Tate symbol Kummer field digit extraction
Endpoint/fetch queries (about 64, about 20 of which failed or were rate-limited: 429 arXiv API/Semantic Scholar/OpenAlex after the first 9, 403 zbMATH/pure.mpg, 404, DNS):
1 arXiv API abs BBP+polylogarithm (429); 2 arXiv API linear independence dilogarithm (timeout);
3 OpenAlex BBP type formulas polylogarithm constants; 4 OpenAlex linear independence values of dilogarithm;
5 Crossref digit extraction polylogarithm BBP; 6 arXiv abs math/9803067; 7 ar5iv math/9803067;
8 arXiv abs 1603.05810; 9 arXiv abs 1603.04974; 10 arXiv abs 1905.04388 (unrelated); 11 OpenAlex W2951905460;
12 Bailey bbp-formulas.pdf; 13 arXiv abs 1906.09629; 14 arXiv pdf 1906.09629; 15 OpenAlex W2562703749;
16 OpenAlex W7220954236; 17 OpenAlex W2886892991; 18 OpenAlex Bloch/Zagier/digit extraction (0 hits);
19 OpenAlex Broadhurst ladders; 20 OpenAlex linear independence polylogarithms Fischler Rivoal;
21 Semantic Scholar BBP polylog (429); 22 zbMATH API BBP formula; 23 arXiv abs 2508.03743;
24 OpenAlex W2993973661; 25 OpenAlex W3188773499; 26 OpenAlex W7221007225; 27 OpenAlex W4313123010;
28 arXiv abs 2611.01066; 29 arXiv API au:Fischler (429); 30 OpenAlex Fischler (429); 31 OpenAlex W3201068003;
32 OpenAlex Zagier (429); 33 OpenAlex ladders (429); 34 Crossref irrationality dilogarithm Rhin Viola;
35 Crossref Zagier conjecture Bloch group; 36 Semantic Scholar lin. indep. dilogarithm (429);
37 zbMATH API dilogarithm irrationality (socket error); 38 Wikipedia Bloch group; 39 Wikipedia Polylogarithm;
40 zbMATH Viola Zudilin (403); 41 zbMATH Rhin (403); 42 hdl.handle.net Viola-Zudilin (redirect);
43 arXiv abs 1912.03811; 44 arXiv abs 2109.10136; 45 arXiv abs 2610.09774; 46 pure.mpg.de PDF (403);
47 Zagier PDF people.mpim (404); 48 Wikipedia Lerch zeta; 49 Crossref Lagarias normality;
50 arXiv abs hep-th/9803091; 51 Bailey digits.pdf (unreadable binary; fetch tool only); 52 arXiv abs math/0012104 (unrelated);
53 Crossref Zagier conjecture proof Goncharov; 54 arXiv API Zagier's polylogarithm conjecture (429);
55 Crossref Calegari Dimitrov Tang; 56 Crossref Marcovecchio Rhin-Viola; 57 GitHub mathlib4 search polylog;
58 GitHub API code search dilogarithm (401); 59 arXiv abs 2109.01702; 60 arXiv abs 1603.07395;
61 corpora.tika.apache.org copy of Compendium (DNS failure); 62 Cambridge BBG abstract;
63 arXiv abs 2408.15403; 64 Crossref Loxton dilogarithm.
Plus direct PDF reads (curl to scratch directory, outside the repo, read with pdftotext): Viola-Zudilin MPIM preprint, Prellberg 2609.06895,
David-Hirata-Kohno-Kawashima 1912.03811, Adegoke 1603.04974 and 1603.05810, Barsky et al 1906.09629, Bailey Compendium.
Totals: WebSearch calls = 4; endpoint queries = 64 (about 44 returned content).
