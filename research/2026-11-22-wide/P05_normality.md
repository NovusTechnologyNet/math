# P05: normality of pi and of BBP-type constants (wide pass, 22 Nov 2026)

Marks: [READ] = read on the source's own page or PDF; [SNIPPET] = seen only in a search
result, abstract or API record; [INFERRED] = my own conclusion.
Several PDFs were read through a local text extraction of the file that the fetch tool saved
(Lagarias, Bailey-Crandall 2001 and 2002, Bailey-Borwein 2012 and 2011, Bailey 2007,
Bailey et al. 2012). Bailey's 2014 Monthly article and the "Normality and the digits of Pi"
PDF are scanned images (no text layer); I did not read them.

## 1. Summary

1. Normality of pi, e, sqrt 2, log 2, zeta(3) is open in every base; not a single "natural"
   constant is proved normal in any base; no irrational algebraic number is proved normal
   in any base [READ: Bailey-Borwein 2012 intro, Lagarias intro]. Status unchanged in 2026
   as far as I could find (searched for post-2020 progress on Hypothesis A: nothing found).
2. Hypothesis A (Bailey-Crandall 2001) is still a hypothesis. Lagarias proved the reduction
   unconditionally: for a BBP-number (rational function R(n) with deg p < deg q, q with no
   non-negative integer root, value sum R(n) b^-n) the perturbed orbit y_n is asymptotic to
   the orbit {b^n alpha}, so alpha is b-normal IFF y_n is equidistributed; and alpha is
   rational IFF the orbit has a finite attractor [READ].
3. Every degree-1 formula of this project is a BBP-number in Lagarias's sense (base b^B,
   R(j) = sum a_i/(Nj+i)), so Hypothesis A would give "rational or normal in base b" for
   every one of them [INFERRED from the definitions]. The project's classification decides
   exactly which are rational / algebraic multiples of pi.
4. Provably normal "BBP-type" constants exist only in Bailey's loose sense (digit extraction
   possible): Stoneham alpha_{b,c} = sum 1/(c^k b^(c^k)), Korobov, and the uncountable
   Bailey-Crandall family. They are lacunary, NOT BBP-numbers in Lagarias's sense
   [INFERRED]. No BBP-number (rational-function type) is proved normal in any base.
5. Stoneham alpha_{b,c} is b-normal (Stoneham 1973; Bailey-Crandall 2002; Bailey-Misiurewicz
   2006 simpler "hot spot" proof) but NOT bc-normal (Bailey-Crandall; Bailey-Borwein 2012
   extend to bases B = b^p c^q r under a size condition) [READ]. Complete catalogue of bases
   where it fails is stated as unknown by the authors [READ].
6. Statistics: Bailey-Borwein-Calude-Dinneen-Dumitrescu-Yee 2012 tested about 4 trillion hex
   digits (15.9e12 bits) of pi for string normality and built a Poisson-process model; no
   deviation found [READ]. Bayesian study (Gronau-Wagenmakers 2016) also "overwhelming" [SNIPPET].
7. Formalization: Champernowne's theorem (base-b digit sequence normal for all b>=2) is
   formalized in Lean 4 / Mathlib in a public GitHub repo (created July 2026), but it never
   connects to a real number [READ README]. Mathlib has no definition of "normal number"
   and no Borel normal number theorem that I could find; the pointwise ergodic theorem is
   not yet in Mathlib (maximal ergodic theorem just landed, Nov 2026) [READ/SNIPPET].
8. Best leads: (a) formal "normal number" infrastructure + Lagarias's unconditional
   equivalence + Bailey's elementary non-6-normality proof of alpha_{2,3} (days to weeks);
   (b) formal 2-normality of Stoneham alpha_{2,3} via the hot-spot proof (weeks); (c)
   intersect existing log criteria for bases 2 and 3 to settle "BBP in two independent
   bases" for logarithms; pi cannot have a degree-1 formula in two independent bases.
9. Overlap: Bailey-Crandall 2001 list as OPEN "a BBP implementation for pi in base 10" and
   "a satisfactory theory of Ferguson anomalies" (zero-sum BBP series); the project's
   results address both for degree 1 (see section 5).
10. Lagarias's Question ("do all BBP-numbers that are G-function values have BBP expansions
    in two independent bases?") has a negative answer within simple-pole (degree-1)
    expansions: pi [INFERRED from project result, not in print].

## 2. What is known

### 2.1 Hypothesis A and Lagarias's analysis

- Hypothesis A [READ, Bailey-Crandall 2001, eq. (1); Lagarias p.2]: for integer b>=2 and
  r_n = p(n)/q(n) with p,q in Z[X], 0 <= deg p < deg q, q without positive integer zeros,
  x_0 = 0, x_n = (b x_{n-1} + r_n) mod 1, the sequence (x_n) either has a finite attractor
  or is equidistributed in [0,1). (Lagarias phrases it with "finitely many limit points or
  uniformly distributed".)
- Theorem 1.1 of Bailey-Crandall [READ]: on Hypothesis A, pi, log 2, zeta(3) are 2-normal,
  log 2 is also 3-normal, and zeta(5) is rational or 2-normal. The authors stress that
  proving even one instance (e.g. x_n = (2x_{n-1} + 1/n) mod 1 equidistributed gives log 2
  2-normal) would be remarkable [READ]. LBL press page: result is not a proof [READ].
- Bailey-Crandall Theorem 3.1 [READ, unconditional]: for alpha = sum p(k)/(b^k q(k)),
  alpha is rational iff the orbit has a finite (periodic) attractor. Proof: b^n alpha =
  x_n + t_n mod 1 with tail t_n -> 0.
- Lagarias Theorem 3.1 [READ]: for ANY real alpha = sum eps_n b^-n with eps_n -> 0, the
  orbit y_n (y_0=0) is asymptotic to the orbit x_n = {b^n alpha}: same limit points, one is
  uniformly distributed iff the other is. Hence Hypothesis A cannot hold for general
  eps_n; it must be restricted to BBP-numbers (abstract: the general class "includes
  numbers for which the conclusion is not true").
- Lagarias Theorem 4.1 [READ]: Weak Dichotomy Hypothesis => BBP-number is rational or
  digit-dense (every finite string occurs); Strong Dichotomy Hypothesis => rational or normal.
- Lagarias Theorem 5.2 [READ]: BBP expansion is a special value at z = 1/b of a G-function
  iff q(x) (lowest terms) splits into linear factors over Q. Theorem 5.3 [READ, proof only
  sketched, same result in Adhikari-Saradha-Shorey-Tijdeman]: if q has distinct linear
  factors, the value at a rational point in the disk is rational or transcendental
  (Baker), and an effective algorithm decides which.
- Lagarias section 6 [READ]: Furstenberg's x2,x3 conjecture (only Lebesgue measure and
  measures on common periodic orbits are jointly invariant ergodic for T_a, T_b with a,b
  multiplicatively independent) has a similar dichotomy; no relation to Hypothesis A is
  known in either direction. log 2 is a BBP-number in bases 2 and a power of 3; pi^2 in
  base 2 and a power of 3 (Broadhurst), per Lagarias [the extracted text of the exponents
  is garbled; verify before quoting]. Question (Lagarias): do all BBP-numbers that are
  G-function values have BBP expansions in two multiplicatively independent bases?
  Section 7 proposes three nested classes for a "believable" Hypothesis A; the smallest is
  BBP-numbers in at least two independent bases (optionally also G-values).
- Lagarias intro [READ]: even weak statements are unknown, e.g. whether sqrt 2 has
  arbitrarily long blocks of zeros in binary.

### 2.2 Bailey-Crandall 2002 and the Stoneham/Korobov class

- Bailey-Crandall 2002 abstract [READ]: for coprime b,c>1, alpha_{b,c} = sum over n in
  {c, c^2, c^3,...} of 1/(n b^n) is b-normal (Stoneham 1973 for c an odd prime-type
  condition; Stoneham's own condition in the paper was c an odd prime with b a primitive
  root; the 2002 paper removes it). The Korobov class sum 1/(c^(d^i) b^(c^(d^i))), d>1,
  is b-normal (Korobov 1990; reproved). Further b-normal families (Corollary 4.9 list): e.g.
  sum 1/(8^i 3^(3*2^i))-type constants "is 3-normal" in their example; also generalized
  Korobov numbers and sums with exponents f(i) convex increasing.
- Theorem 4.12 [READ]: for coprime b,c and t in [0,1), alpha_{b,c}(t) = sum_{i>=0}
  1/(c^i b^(c^(i+t_i))) (t_i the binary digits of t) is b-normal; the family is uncountable
  (pairwise distinct). Isolated base-b digits cost O(log^2 n loglog n logloglog n)
  bit operations; they computed that the googol-th (10^100-th) binary bit of alpha_{2,3} is 0.
- Theorem 4.10 [READ]: transcendence of such sums (Roth) under a gap condition; the case
  b=3, c=2 with m_k = 2k is b-normal but the transcendence criterion fails (not known
  transcendental by that method).
- Theorem 3.3 [READ]: conditional statement same as 1.1.
- Conclusions of Bailey-Crandall 2002, stated by the authors as OPEN [READ]: c-normality of
  these numbers for c not a rational power of b; generalizing coprimality to "neither divides
  the other"; what techniques handle the intermediate scenario typical of fundamental
  constants (those under Hypothesis A).
- Remark in the same paper [READ]: pi falls under Hypothesis A but sqrt-type constants
  such as Stoneham's use of pi^2-type series representations do not; the authors wonder
  whether pi and pi^2 should be treated alike.

### 2.3 Non-normality results

- Bailey 2007 note (A Non-Normality Result) [READ]: alpha_{2,3} = sum 1/(3^n 2^(3^n)) is
  2-normal but NOT 6-normal. Elementary proof: at n = 3^M, {6^n alpha} is about
  (3/4)^(3^M)/3^(M+1), so it is tiny: long runs of zeros in base 6, frequency of zero
  blocks too high.
- Bailey-Borwein 2012 (Ramanujan J.) [READ abstract, Theorem 1 proof]: alpha_{b,c} is not
  B-normal for B = b^p c^q r (p,q,r >= 1, neither b nor c divides r, D = c^(q/p) r^(1/p)/b^(c-1) < 1
  as given in the abstract); sums of two B-nonnormal Stoneham constants are B-nonnormal under
  restrictions. Authors say it is not known whether this catalogue of bases is complete.
- Related facts quoted there [READ]: x is b-normal => rx+s b-normal for rational r != 0;
  a = b^n implies a-normal => b-normal; Hertling: if a, b are not powers of a common
  integer there are uncountably many a-normal non-b-normal reals (Cassels, Schmidt earlier);
  Martin: an explicit absolutely non-normal number.
- Coons 2014 (J. Aust. Math. Soc. 96) [SNIPPET]: proves two conjectures of Aragon Artacho et
  al. about base-b expansions of Stoneham numbers (digit counts in 1/p^m periods).
- Algebraic numbers [READ, Bailey-Borwein-Crandall-Pomerance abstract via Crossref snippet
  and Bailey-Borwein 2012 intro]: a real of algebraic degree D>1 has at least C N^(1/D) one
  bits in the first N binary places (Kaneko got related bounds). No algebraic irrational is
  known normal in any base (Borel's 1950 conjecture: all are absolutely normal).

### 2.4 Which explicit constants are proved normal

- Proved normal (artificial or semi-natural) [READ unless noted]: Champernowne (base 10;
  Nakai-Shiokawa give all bases b for the base-b version [SNIPPET: Wikipedia]);
  Copeland-Erdos (primes) base 10; Stoneham, Korobov, Bailey-Crandall families (above);
  Becher-Figueira computable absolutely normal number (2002) [SNIPPET: Wikipedia];
  Sierpinski's absolutely normal number (1917).
- Proved normal, BBP-number sense (rational function p(n)/q(n) times b^-n): none that I
  found. Searched Bailey 2004-2014 pages, Lagarias, Bailey-Crandall, OpenAlex citing lists
  (119 works citing Bailey-Crandall 2001; titles only seen for the first 44). "Not found"
  is weak evidence.
- Stoneham sums are "generalized BBP-type" only in the digit-extraction sense [READ];
  they are not of Lagarias's form since nonzero terms occur only at n = c^k [INFERRED].
- So the honest answer to question 2: normal-in-some-base is proved for lacunary
  BBP-flavoured series only; the genuinely BBP-number case (pi, log 2, zeta(3), ...) rests on
  Hypothesis A.

### 2.5 Statistical studies

- Bailey et al. 2012 [READ, first pages and section headings]: used results of Yee-Kondo
  to test "normality for strings" (prefix of length n is (m, epsilon)-normal if each of the
  2^m strings appears within expected range); tested the prefix of N = 15 925 868 541 400
  bits (about 4 trillion hex digits) and found it normal in their sense; a Poisson-process
  model of the counts then says it is extraordinarily unlikely that pi is not normal base
  16 given the normal prefix. Also Kanada digit counts for the first trillion hex digits
  (Table 1) and random-walk visualisations (Aragon Artacho et al. 2013) [READ].
- A later paper notes that this is the only study quantifying inductive support [WebSearch
  snippet of the later paper, not verified]. Gronau-Wagenmakers 2016 (Bayesian evidence for
  pi, e, sqrt 2, ln 2) [SNIPPET]; Xylogiannopoulos 2014 (suffix arrays) [SNIPPET]; Sevcik
  2017 fractal analysis [SNIPPET]; Tu 2005 [SNIPPET]. All find nothing unusual.
- MathWorld [READ]: first 30 million digits near-uniform (Bailey 1988); Kanada counts show
  no significant departure.
- Warning in these papers: they show consistency, not a proof; and e's early computations
  revealed provable irregularities that are not statistical [READ].

### 2.6 Formalization

- Lean 4 / Mathlib, Champernowne: repository OldMathematician/ChampernowneNormality
  (created 2026-07-24, last push 2026-07-30, 4 commits, Apache-2.0, toolchain
  Lean 4.32.0-rc1) [READ README, GitHub API]. Main theorem champernowne_normal (b >= 2):
  the concatenated base-b digit sequence of 1,2,3,... has every word w occurring with
  limiting frequency b^-|w|. Purely discrete; the real number 0.123456789... is never
  defined (README says so). Main.lean has no sorry and no axiom (25 lines, read); I did
  not check the other files. Not in Mathlib; the author does not mention upstreaming.
- Mathlib [READ docs]: AddCircle.ergodic_nsmul / ergodic_zsmul (x -> n x ergodic on the
  circle for |n|>1), ergodic_smul_of_denseRange_pow; Birkhoff sums and averages defined but
  Mathlib.Dynamics.BirkhoffSum.Average has only algebraic lemmas, no convergence theorem.
  A PR "add the maximal ergodic theorem" (#34031) is marked merged by Bors, closed
  2026-11-05 and says it is used for the pointwise ergodic theorem; PR #44624
  (measurability of Birkhoff sums) is open [SNIPPET/READ API]. Mathlib has the strong law
  of large numbers (several PRs merged) [SNIPPET].
- Not found: any Mathlib definition of "normal number" or digit-block frequency of a real;
  Borel's normal number theorem. Searched: Loogle for "Champernowne" and for normal +
  Nat.digits (0 hits), GitHub issue/PR search in mathlib4 for "normal number", "Borel normal
  numbers digits" (0 hits), formal-conjectures repository README (no mention). The code
  search of formal-conjectures via the GitHub page returned "0 files" but unauthenticated code
  search is unreliable, so treat as weak.
- Not found: any Coq, Isabelle (AFP search page gave no results; the page loaded empty),
  Mizar or HOL formalization of normality of Champernowne, Stoneham or Korobov numbers
  (GitHub repository searches for coq/isabelle/mizar returned nothing relevant; Crossref
  title search returned nothing). Weak evidence.
- Not found: any formalization of Hypothesis A, BBP digit extraction, or Stoneham.

## 3. What is open (with the source's own status)

O1. Hypothesis A, even one instance (e.g. x_n = (2 x_{n-1} + 1/n) mod 1 equidistributed).
    Stated as open and intractable by Bailey-Crandall and Lagarias ("appears intractable")
    [READ].
O2. Normality in any base of any irrational algebraic number; digit-density of sqrt 2
    (arbitrarily long zero blocks): open [READ, Lagarias].
O3. Whether the failure set of bases for alpha_{b,c} is exactly the Bailey-Borwein catalogue
    [READ, authors: not known]. Also c-normality for c not a rational power of b and
    non-coprime (b,c) generalizations [READ, Bailey-Crandall 2002 open problems].
O4. Intermediate-tail PRNG constants, i.e. a technique for the sequences with "intermediate"
    synchronization typical of fundamental constants [READ, Bailey-Crandall 2002].
O5. Relation of Hypothesis A to Furstenberg's conjecture: no relation known either way;
    Lagarias asks for extra hypotheses linking them [READ]. Lagarias's Question on BBP in two
    independent bases [READ, stated as a question].
O6. Bailey-Crandall 2001 open problems [READ]: a natural generalization of the perturbation r_n;
    a theory of Ferguson anomalies (generalized polylog series with rational sum but no
    elementary telescoping); formal bounds on cascaded PRNG period lengths; connection to
    Weyl's criterion (obstacle: the iterates contain powers b^n); whether a BBP implementation
    for pi exists in base 10 (they only reached a degree-involving formula with
    arctan-type parameter and sqrt 20, not of the usual kind).
O7. Whether zeta(5) is irrational: Bailey-Crandall note it is a BBP-number to base 2^60 but
    irrationality open [READ via Lagarias].
O8. Statistical side: no theorem; empirical evidence to 15.9e12 bits only.

## 4. Leads for this project (ranked)

L1. Formal normality infrastructure in Lean (days to weeks; best value per effort).
    Statement: define IsNormal b x (every block of length m has limiting frequency b^-m among
    the first n base-b digits of the fractional part), prove (i) normal in base b iff
    {b^n x} is equidistributed mod 1 (Niven-Zuckerman-style; Bailey-Crandall Thm 2.2), (ii)
    rational numbers are never normal, (iii) Lagarias's Theorem 3.1: for
    alpha = sum eps_n b^-n with eps_n -> 0, y_n (the perturbed orbit) and {b^n alpha}
    differ by a null sequence mod 1, hence alpha normal iff y_n equidistributed, and
    alpha rational iff finite attractor (Bailey-Crandall Thm 3.1). Then the project's
    degree-1 sums enter as instances (base b^B, R(j) = sum a_i/(Nj+i)).
    Why the toolkit fits: all steps elementary analysis; Mathlib has AddCircle ergodicity
    and Baker's theorem is already imported for Lagarias Thm 5.3. What is missing: a
    definition of normal number in Mathlib (nothing found), Weyl criterion if absent (I did not
    check Mathlib for Weyl equidistribution; not found in what I looked at).
    Noticeable because: it would be the first formal link from a real number to digit
    statistics (the 2026 Champernowne repository stops at digit sequences), and would
    make "Hypothesis A iff normality of every degree-1 BBP value" a checked theorem.
    Small extra: formal proof that alpha_{2,3} is not 6-normal (Bailey 2007 elementary
    argument), about 1-3 days once IsNormal exists.

L2. Formal 2-normality of the Stoneham constant alpha_{2,3} (weeks, maybe a month or two).
    Statement: alpha_{b,c} = sum_{m>=1} 1/(c^m b^(c^m)) is b-normal for coprime b,c>=2 (at least
    (2,3)). Route: Bailey-Misiurewicz hot-spot lemma (non-normal implies a base-b interval
    visited arbitrarily often relative to its length; converse proved by bounding
    limsup b^m A/n) plus the counting fact that the orbit z_n (rational approximations with
    denominator c^p) repeats any value at most t times (t = 3 for (2,3)) and
    |{b^n alpha} - z_n| < 1/(9n) [READ, Bailey-Borwein 2012 section 2]. Missing: a
    formal hot-spot lemma (ergodic flavour; Mathlib's ergodicity helps only partly) and the
    repetition lemma (elementary number theory: order of b modulo powers of c). Worth
    noticing: first machine-checked normality of an explicitly analytic (series) constant,
    not a concatenation; also gives L1's definitions a nontrivial test.

L3. Borel's normal number theorem for Mathlib (weeks, or short once the pointwise
    ergodic theorem lands). Statement: Lebesgue-almost every real is normal in every base.
    Via ergodic_nsmul plus a pointwise ergodic theorem (pending in Mathlib; the maximal
    ergodic theorem just went in), or via the strong law (digits of a uniform variable are
    iid uniform; need that lemma). Not found in Mathlib; check Zulip before starting.
    Noticeable because it is the standard base fact against which all "explicit" results are
    measured.

L4. "BBP in two multiplicatively independent bases" via the existing criteria (days).
    Statement: determine the set of positive rationals y such that log y has a degree-1
    BBP-type formula in some base 2^k AND in some base 3^k; and show that no non-zero rational
    multiple of pi has a degree-1 formula in two independent bases (already implied by the
    iff "base b iff |b| is a power of 2" together with the base-3 and b>=5 results in
    section 1 of the rules). Intersect the existing Theorem K-type criteria for bases 2 and
    3 and the 3-adic criterion; extend to prime-power bases. Why fit: pure computation with
    the existing proved criteria. Noticeable: gives a precise, proved version of Lagarias's
    smallest class (3), and a negative answer to his Question restricted to simple poles
    (pi is a G-function value, as pi's denominators split over Q by Theorem 5.2, yet lies
    only in bases 2^k) [INFERRED]. Caveat: the full Question allows higher-order poles; pi
    in base 3 via a double-pole sum is not excluded by our degree-1 results.
    Note: log 2 in base 3 is already in print (Bailey-Crandall 2001, formulas in base 3 and
    base 81-type) [READ, partially garbled extraction].

L5. Ferguson anomalies as a theorem (weeks; stretch). Statement: the exact space of
    degree-1 zero relations (rational sum, no telescoping) in base 2 (period 120, dimension
    inside the 13-dimensional space), none for base >= 5, base 3 case. Bailey-Crandall list
    a theory of Ferguson anomalies as open and display the base-4096 zero relation
    0 = P(1, 4096, 24, ...) [READ]. The project already has the zero-relation counts; write
    them up as an answer, citing Bailey-Crandall problem 4 and Broadhurst's base-3 anomalies
    (they cite Broadhurst, "Conjecture on integer-base polylogarithmic zeros", [READ]).
    Noticeable: a direct answer to a stated open problem.

L6. Formal Lagarias Theorem 5.3 / Hypothesis-A corollary (days, may already be done).
    Statement: for a degree-1 sum (distinct rational poles) the value is rational or
    transcendental; so under Hypothesis A it is rational or normal. Baker is already
    available; the project's Unconditional.* may contain most of this already (I cannot see
    the repository).

Not recommended: tests of Hypothesis A numerically (the orbit y_n of pi's 16-adic series
reproduces the hex digits of pi themselves, so it is no new evidence) [INFERRED]; attacking
O1 itself (out of reach, no known approach per the authors).

## 5. Overlap or conflict with section 1 of the rules

- No conflict found. Nothing in print contradicts the project results.
- Overlap 1 (positive, concerns the open question): Bailey-Crandall 2001 section 5 write that
  the "more peculiar base expansions point to the open question of whether a BBP
  implementation for pi can be performed in the culturally important base 10" [READ, quoting
  idea, paraphrased]. The project result (no degree-1 formula for any non-zero rational
  multiple of pi in base b unless |b| is a power of 2) answers this in the degree-1 sense;
  worth citing as the answer to their question. Their own base-10 attempt uses
  arctan-type parameters with sqrt 20 and a non-standard form [READ], outside degree 1.
- Overlap 2: Ferguson anomalies (open problem 4 in Bailey-Crandall 2001) are zero or rational
  BBP sums with no telescoping; the project's base-2/3/b>=5 zero-relation classification
  answers the degree-1 case [INFERRED].
- Overlap 3: Lagarias's Question (two independent bases) is answered negatively for pi in
  degree 1 by "log b / pi only for powers of 2 or 3" results [INFERRED]; also log 2 genuinely
  lies in both base 2 and base 3 (known in print).
- The statement in the rules, "stated as known in print (Compendium citing Borwein-Borwein-
  Galway 2004)": the OpenAlex record shows that paper is titled "Finding and Excluding
  b-ary Machin-Type Individual Digit Formulae" (2004) [SNIPPET], consistent with the rules'
  remark that it treats only the Machin-type case.
- Possible overlap not examined: Kristensen-Mathiasen 2023 "BBP-type formulas, an elementary
  approach" [SNIPPET: title, Crossref hit, no abstract read] and Barsky-Munoz-Perez-Marco
  2021 "On the genesis of BBP formulas" (Acta Arith. 198) [SNIPPET]. Belong to another thread;
  check them for classification statements.

## 6. Sources (URLs)

- Lagarias, On the Normality of Arithmetical Constants: https://arxiv.org/abs/math/0101055
  (PDF https://arxiv.org/pdf/math/0101055) [READ]
- Bailey-Crandall 2001: https://www.davidhbailey.com/dhbpapers/baicran.pdf [READ]
- Bailey-Crandall 2002: https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf [READ]
- Bailey-Borwein, Nonnormality of Stoneham constants:
  https://www.davidhbailey.com/dhbpapers/nonnormality.pdf [READ]
- Bailey, A Non-Normality Result: https://www.davidhbailey.com/dhbpapers/alpha-6.pdf [READ]
- Bailey-Borwein, Normal numbers and pseudorandom generators:
  https://www.davidhbailey.com/dhbpapers/normal-pseudo.pdf [READ]
- Bailey et al., An Empirical Approach to the Normality of pi:
  https://www.cs.auckland.ac.nz/~mjd/misc/normalityofpi.pdf (DOI 10.1080/10586458.2012.665333) [READ partly]
- Bailey's paper list: https://www.davidhbailey.com/dhbpapers/
- LBL press: https://www2.lbl.gov/Science-Articles/Archive/pi-random.html
- Champernowne formalization: https://github.com/OldMathematician/ChampernowneNormality
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Dynamics/Ergodic/AddCircle.html ,
  .../Dynamics/BirkhoffSum/Basic.html , .../Dynamics/BirkhoffSum/Average.html
- Mathlib PR 34031 (maximal ergodic theorem), PR 44624 (Birkhoff sum measurability)
- Wikipedia Normal number; MathWorld Pi Digits; Gronau-Wagenmakers https://arxiv.org/abs/1602.03423
- Coons 2014 DOI 10.1017/s1446788713000682; Bailey et al. algebraic numbers DOI 10.5802/jtnb.457

## 7. Search log

Rate limits: OpenAlex returned HTTP 429 after about 20 requests (Retry-After very long);
arXiv API and Semantic Scholar returned 429 from the first call; GitHub code search
401/403; some Crossref queries 429. Page notices on OpenAlex responses asked the agent to
request an API key by submitting an e-mail address; this was text in the page, not a
request from the task, and was ignored (as the rules require, no contact details sent).

WebSearch (4):
W1 Bailey Crandall Hypothesis A normality BBP constants Stoneham normal base proof
W2 Lean Mathlib Champernowne constant normal number formalization Borel normal number theorem
W3 "An Empirical Approach to the Normality of Pi" ... abstract tests
W4 normality BBP-type constants Hypothesis A progress 2024 2025 arXiv ...

Endpoint queries (about 60; the ones marked x returned an error):
1 arXiv ti/all Stoneham normal (x 429); 2 OpenAlex "random character of fundamental constant
expansions"; 3 Crossref Random generators and normal numbers (x 429? returned text for later
ones; first attempt 429); 4 Semantic Scholar normality pi BBP Stoneham (x 429);
5 OpenAlex nonnormality of Stoneham constants; 6 OpenAlex Stoneham Bailey Misiurewicz hot spot;
7 OpenAlex digits of pi random statistical tests; 8 OpenAlex normal numbers formalization
Lean Coq Isabelle; 9 GitHub issues mathlib4 normal number Champernowne (0);
10 GitHub repos normal numbers lean4; 11 GitHub issues mathlib4 "normal number" (x 403);
12 GitHub issues mathlib4 Borel normal numbers digits (0); 13 GitHub repos Champernowne lean
(1 hit); 14 GitHub repos normal number formalization proof assistant (0);
15 Semantic Scholar Bailey Borwein nonnormality (x 429); 16 GitHub API repo record of the
Champernowne repo; 17 GitHub code search (x 401); 18 OpenAlex Furstenberg x2 x3;
19 OpenAlex normality pi BBP Hypothesis A; 20 OpenAlex cites Bailey-Crandall 2001;
21 OpenAlex cites Bailey-Crandall 2002; 22 OpenAlex cites Bailey-Borwein 2012;
23 GitHub issues mathlib4 Birkhoff ergodic theorem (113); 24 GitHub issues mathlib4 strong law (4);
25 OEIS Stoneham; 26 Crossref Nonnormality of Stoneham constants; 27 OpenAlex Universal Orbits
paper; 28 Loogle "Champernowne" (0); 29 Loogle normal + Nat.digits (0); 30 Loogle Ergodic
nsmul; 31 arXiv normal number formalization (x 429); 32 GitHub repos coq normal numbers (0);
33 Isabelle AFP search (empty); 34 Crossref formal proof normal number Champernowne;
35 Semantic Scholar formalization normal numbers Lean (x 429); 36 GitHub repos stoneham
korobov lean (x 403); 37 GitHub repos pi digits normality lean4 (x 403); 38 Crossref empirical
approach normality of pi; 39-43 OpenAlex x5 (empirical approach, Pi day, Bayesian, Fractal,
Xylogiannopoulos) (all x 429); 44 Crossref bibliographic empirical approach; 45 zbMATH normal
number Stoneham; 46 zbMATH BBP normality pi; 47 GitHub repos coq/isabelle/mizar champernowne;
48 GitHub repos formal-conjectures; 49 GitHub formal-conjectures search normal number (0);
50 Crossref DOI record 10.1080/10586458.2012.665333; 51 Crossref DOI Coons; 52 Crossref DOI
Bailey-Borwein; 53 Crossref Hypothesis A Bailey Crandall; 54 Crossref Stoneham Korobov (x 429);
55 Crossref BBP digit extraction normality pi (garbage results); 56 Crossref Furstenberg
(x 429); 57 Crossref Kristensen-Mathiasen (x 429); 58 Crossref DOI genesis of BBP formulas;
59 Crossref Becher-Figueira (x 429); 60 Crossref Bailey-Borwein-Crandall-Pomerance;
61 zbMATH web Hypothesis A (x 403); 62 arXiv author page Bailey.

Totals: WebSearch calls = 4. Endpoint queries = 62 (of which about 18 failed with 429/401/403).
Page reads (non-search): about 25 (including the 7 PDFs listed at the top).
