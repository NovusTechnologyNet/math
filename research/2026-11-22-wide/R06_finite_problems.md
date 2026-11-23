# R06: number-theory problems that are "finite but large" (certified computation + formal proof)

Note on marks: [READ] means seen on the source page through the fetch tool (which returns a
model-made summary of the page, so numbers should be re-checked before being quoted in print);
[SNIPPET] means seen only in a search result or record; [INFERRED] is my own conclusion.
Rate limits: arXiv API and OpenAlex returned 429 (OpenAlex Retry-After about 19 hours), Semantic
Scholar 429, erdosproblems.com 403, Mossinghoff's site not reachable (404 / DNS). I used other
endpoints. No page contained text addressed to me.

## 1. Summary

1. The cleanest "finite but large, certifiable, citable" target is a Lean-checked, hypothesis-free
   list of all solutions of x+y=1 in S-units over Q (equivalently, consecutive S-smooth pairs,
   Stormer) for S = first k primes, with k beyond what is currently proved. Unconditional OEIS data
   stop at k = 23 for the count of pairs (A002071); beyond that the large terms (A002072, k up to 37)
   are abc-conditional or solver-based. The project already has Baker's theorem formally, LLL
   relations checked exactly, and case trees, so this is the best fit. No formal S-unit solver
   exists anywhere that I could find.
2. Mathlib has no Stormer theorem: a PR (#42040) was closed unmerged on 2026-09-22 for AI-use
   policy reasons, not mathematics. A Dirichlet S-unit theorem PR (#40791) is open. [READ/SNIPPET]
3. Erdos-Straus: verified for all n up to 10^17 (Salez 2014) and, in a 2025 arXiv preprint, up to
   10^18 in about two weeks on a "medium setup". Nothing is formally certified. A certified-checker
   version (witness for every prime, residue-class coverage proved in Lean) would be new.
4. Lehmer/Mahler: Lehmer's number is the minimum for every even degree up to 54 and the list of
   measures below 1.3 is complete for degree <= 44 (Mossinghoff-Rhin-Wu 2008); beyond that
   searches are heuristic. A 2024 paper adds 10 new Salem numbers in (1.3, 49/37) and says
   openly it is not exhaustive. Nothing is formal.
5. Isabelle has a verified LLL (AFP, 2018) and a verified LLL-based polynomial factorization; I
   found no Lean/Coq verified LLL, and no verified Baker-Davenport reduction anywhere.
6. Incomplete/wrong published lists are rare in my search, but there is one clean case: a missing
   solution in an earlier version of a Bennett-Billerey proposition on sums of two S-units, noticed
   by von Kanel and Matschke. Wikipedia also gives two different counts (41 vs 42) of remaining
   Riesel candidates in different revisions.
7. Open and stated open: odd covering problem; Pillai; Goormaghtigh; Sierpinski (5 candidates) and
   Riesel (about 41 candidates as of Dec 2022) problems; Lehmer's problem. Verger-Gaugry has an
   arXiv preprint claiming Lehmer's conjecture (2017, 164 pages); no acceptance seen; treat as
   unproved.
8. Ranked leads are in section 4.

## 2. What is known

### 2.1 Complete lists proved by bounded search

Stormer / consecutive smooth numbers
- Statement: for a finite set P of primes there are finitely many pairs of consecutive
  P-smooth integers; Lehmer's version solves 2^k - 1 Pell equations x^2 - 2q y^2 = 1 (q a
  P-smooth squarefree number other than 1, 2 in P) and checks the first max(3,(p_k+1)/2)
  solutions of each; bound 3^k - 2^k (Stormer) or (2^k-1) max(3,(p_k+1)/2) (Lehmer). [READ,
  Wikipedia "Stormer's theorem"]
- Pair counts for the first k primes (A002071): 1, 4, 10, 23, 40, 68, 108, 167, 241, 345 for
  k = 1..10; the largest listed value is 9179 at k = 23, and the comments say terms 22 and 23
  were computed unconditionally. [READ, OEIS search page]
- A002072 (largest m such that for every larger k one of k, k+1 has a prime factor above
  prime(n)): data shown to n = 27 (about 1.93e22); a b-file has n up to 37 from a solver by K.
  Clements (July 2026). Values a(27)..a(33) are only predicted under an effective abc
  conjecture (L. Brown) and Clements's computation agrees with that prediction; a(37) needed a
  search "well beyond" earlier terms. Earlier extension work: Reble 2005, Schneider 2006, Kulsha
  2011 (from Jim White's computations to p = 127 in "Results to P = 127"). The page does not say the
  newest terms are unconditional. [READ]
- Conrey-Holmstrom-McLaughlin (2013) describe a fast procedure that finds many but not all such
  pairs (empirical). [READ via Wikipedia]
- A391602: the last m where a certain minimum "d" drops to 6, verified only for m <= 10^15. [SNIPPET-level
  from OEIS fetch]

S-unit equations
- Software: Alvarado, Koutsianas, Malmskog, Rasmussen, Vincent, West, SageMath implementation for
  x+y=1 over number fields (arXiv 1903.00977); it computes exponent bounds in many small-degree
  fields with small S, an asymptotic Fermat result for totally real cubic fields, and some cubic
  Ramanujan-Nagell equations. [READ, abstract page] I could not read the PDF body (binary), so
  whether its output is certified or heuristic is not checked. [INFERRED: it uses real/p-adic
  LLL reductions like de Weger, so the output is rigorous only if the code is.]
- Gyory (arXiv 1901.11289) improves effective bounds in terms of S. [READ, abstract]
- Bennett-Billerey (arXiv 1603.07922) solve x+y=z^n type equations with S={2,3}, {3,5,7},
  {2,3,5,7} and {2,3,p}, p<100, by Frey curves and level lowering instead of Baker. For S={3,5,7}
  the level-lowering bound without sieving is of order 10^18991, and the authors say the
  computations approach the limit of off-the-shelf technology. They recover de Weger's ch. 7
  results (S={2,3,5,7}, by linear forms in logs and lattice reduction). [READ, ar5iv]
- Ziegler, arXiv 2609.15487, "On the number of solutions to S-unit equations" (title only). [SNIPPET]

Catalan / Pillai / perfect powers
- Catalan (Mihailescu 2002/2004) is a theorem; Tijdeman 1976 + Langevin gave an effective bound
  earlier. Pillai's conjecture (each positive integer is a difference of perfect powers
  finitely often) is open; ABC would imply it. Wikipedia lists computed solutions for differences
  1..13 with perfect powers below 10^18. [READ]
- Fibonacci and Lucas perfect powers: Bugeaud-Mignotte-Siksek, Annals 2006 (Fibonacci perfect
  powers are 0, 1, 8, 144); Lucas sequences and products of terms: Compositio/Crelle/IJNT papers.
  [SNIPPET, Crossref records]
- Repunits as perfect powers: Nagell-Ljunggren (x^n-1)/(x-1)=y^q; Bugeaud-Mignotte, Math. Scand.
  101 (2007). I could not read the abstract (redirect to the journal page not followed), so the
  exact open cases are not checked. [SNIPPET, title only]
- Goormaghtigh: only 31 and 8191 are known; He-Togbe 2008 (for fixed x and y at most one
  solution); Yuan 2005 (m = 3, n odd); searches only for small x or small x^m. Stated open. [READ,
  Wikipedia]

Egyptian fractions
- Erdos-Straus, 4/n = 1/x+1/y+1/z: true for all n < 10^17 (Salez 2014). [READ, Wikipedia
  "Egyptian fraction" and "Erdos-Straus conjecture"]. Earlier: Obláth 1950 (n <= 10^5), Swett
  1999 (10^14), Bello-Hernandez et al. 2012 (2e14) [SNIPPET].
- Mihnea-Dumitru (arXiv 2509.00128, Aug 2025): extends Salez's filter method with an extra filter
  (S_29), 2,101,514 residue classes modulo 25,878,772,920 to check, each candidate tested against
  about 140,000 precomputed prime filters; reaches primes up to 10^18; about two weeks "medium
  setup" (cores not stated); no independent certification described. [READ]
- Mordell identities cover everything except n = 1, 121, 169, 289, 361, 529 (mod 840); smallest
  uncovered prime 1009; no covering by identities is possible (Mordell: residue must be a
  non-residue); Elsholtz-Tao: average number of solutions bounded polylogarithmically; counter-
  example density zero (Webb and others). [READ, Wikipedia]
- Several 2025/2026 arXiv items claim proofs or "almost complete" proofs (2508.07367, 2508.07383,
  2602.20036). The one I read (2602.20036) has an informal density argument and no Lean. I
  treat these as unreliable. [READ for 2602.20036; SNIPPET for the others]
- Many GitHub repositories claim verification or partial results (one says to 8e13 on Kaggle,
  another to 10^11); one is a Lean 4 "fixed-divisor offset construction" repository (not a
  proof). All self-described, unchecked. [SNIPPET]

Covering systems
- Hough 2015 (Annals) solved Erdos's minimum modulus problem negatively: there is a largest N,
  below 10^16, that can be the minimum modulus of a covering system with distinct moduli. Known
  examples: 20 (Choi), 40 (Nielsen), 42 (Owens). [READ, Wikipedia; Crossref record of the Annals paper]
  So the interval between 42 and 10^16 for the best minimum modulus is open (I did not read
  later improvements, e.g. Balister-Bollobas-Morris-Sahasrabudhe-Tiba; not checked).
- Odd covering problem (Erdos-Selfridge): open. For squarefree odd moduli the lcm would need at
  least 22 prime factors (Guo-Sun, as cited). [READ, Wikipedia]

Sierpinski and Riesel
- 78557 conjectured smallest Sierpinski number (Selfridge 1962, covering set {3,5,7,13,19,37,73});
  remaining candidates: 21181, 22699, 24737, 55459, 67607 (PrimeGrid). 271129 is smallest known prime
  Sierpinski number; prime Sierpinski search ongoing. [READ, Wikipedia]
- 509203 conjectured smallest Riesel number (covering set {3,5,7,13,17,241}); as of Dec 2022 41 of
  101 candidates remained; PrimeGrid searched to n = 14.9 million in Jan 2023; Propper found
  107347*2^23427517-1 prime in Aug 2024 (7,052,391 digits) [READ, Wikipedia; the exponent printed in the fetch was
  garbled, so check it]. Different revisions of the article give 41 or 42 remaining. [SNIPPET]
- These conjectures are open for an analytic reason (a prime must be found for each remaining k);
  the covering side is finite and trivial to certify. [INFERRED]

### 2.2 Lehmer's problem and Mahler measure
- Lehmer's number 1.17628... (degree 10) is conjectured to be the smallest Mahler measure > 1.
  Smyth 1971: non-reciprocal case, measure at least 1.3247 (root of x^3-x-1), sharp. Dobrowolski/
  Voutier give a (log log D / log D)^3-type lower bound with constant at least 1/4. [READ]
- Mossinghoff-Rhin-Wu, Experimental Math. 17 (2008) 451-458: minimal measure for each even
  degree up to 54, all primitive irreducible noncyclotomic polynomials of measure below 1.3 and
  degree at most 44; consequently any measure in (1, Lehmer) needs degree at least 56. [SNIPPET
  twice; one fetch summary of MathWorld said "degree at most 54" for the Lehmer minimum, consistent]
- Mossinghoff 1998 (Math. Comp.): search to degree 24, found 4 new Salem numbers below 1.3; website
  lists 47 Salem numbers below 1.3 (39 Boyd 1977 + 4 Boyd 1978 + 4 Mossinghoff 1993, per snippet,
  with the 1998 four possibly accounting for the difference; I did not reconcile). [SNIPPET]
- arXiv 2409.11159 (2024): lists Salem numbers between 1.3 and 49/37, 10 new, degrees 26-44, by
  random sampling plus integer feasibility in Gurobi; the author states exhaustiveness is not
  guaranteed; the earlier list below 1.3 is complete up to degree 44 and the degree-46 entry is
  not certified. [READ]
- Boyd limit point 1.2554...; Boyd conjecture on closedness of the set of Mahler measures
  (many variables), which implies Lehmer. [READ]
- Chervonyi et al. 2026: polynomials with measure below Boyd's limit point for every even degree
  12..2000 (upper bounds only). [SNIPPET, from MathWorld]
- Verger-Gaugry (arXiv 1709.03771, 2017, 164 pages): claims a proof of Lehmer's and Schinzel-Zassenhaus
  conjectures. No journal reference seen. [READ, abstract page] [INFERRED: not accepted by the
  community since the problem is still listed open on MathWorld/Wikipedia.]

### 2.3 Formal proofs
- Isabelle AFP "A verified LLL algorithm" (Bottesch, Divason, Haslbeck, Joosten, Thiemann,
  Yamada, Feb 2018): soundness and formal complexity bounds, a faster integer implementation;
  used by the verified factorization of integer polynomials; also by entries on hardness of
  lattice problems and on lattice reduction/HNF. [READ]
- Lean: Størmer PR to mathlib (#42040, proof-based, bound 3^s - 2^s, Pell/Lucas coefficients) closed
  unmerged 2026-09-22 by the triage bot (AI-use policy). A Dirichlet S-unit theorem PR (#40791) is
  open. [READ for 42040; SNIPPET for 40791]
- Lean formalization of Gardam's disproof of the Kaplansky unit conjecture (deductive proofs
  plus verified computation) exists. [SNIPPET]
- Google DeepMind's formal-conjectures repository: Lean 4 statements of open conjectures (not
  proofs); its own README page did not mention these topics, but the directory contains Erdos
  problem files. Several third-party repositories attach Lean proofs to those statements. [READ
  the README; SNIPPET for repo list]
- Not found: a formally verified S-unit equation solver, a verified Baker-Davenport reduction, a
  verified Lehmer/Mahler computation, a Coq/Lean verified LLL. [searches: WebSearch on formal S-unit
  solving; GitHub and AFP; "not found" is weak evidence]

## 3. What is open (exact statements)
1. Odd covering problem: does there exist a covering system with distinct odd moduli > 1? Stated
   open (Wikipedia, Erdos-Selfridge conjecture says no).
2. Minimum modulus: what is the largest minimum modulus of a covering system with distinct
   moduli? Known only: at least 42, below 10^16 (Hough). Stated open as a gap by implication.
3. Erdos-Straus for all n; computed to 10^17 (accepted), 10^18 (preprint).
4. Sierpinski: eliminate k = 21181, 22699, 24737, 55459, 67607. Riesel: eliminate about 41
   values below 509203 (list on Wikipedia, Dec 2022). Prime Sierpinski: confirm 271129.
5. Pillai (Ax^n - By^m = C finitely many solutions) and Goormaghtigh (only 31, 8191): open.
6. Lehmer's problem: open; also Salem numbers below 1.3 beyond degree 44 not certified.
7. Unconditional values of A002072 beyond about k = 26 (Stormer-Lehmer needs 2^k - 1 Pell
   equations; at k = 27 that is 1.3e8 equations whose fundamental solutions can be astronomically
   large [INFERRED]; so the unconditional route needs a different method).

## 4. Leads for this project, ranked

Lead 1. Formal, hypothesis-free S-unit / Stormer table in Lean for S = first k primes.
- Statement: for each k in a range, the exact list of pairs of consecutive p_k-smooth
  integers (A002071 counts 1, 4, 10, 23, 40, 68, ...), and the corresponding solution set of
  x + y = 1 in S-units of Q (and x+y=z for S-units with signs).
- Why it fits: this is exactly Baker + LLL reduction + exhaustive enumeration of a small box, the
  workflow of the project; Baker's theorem is already imported; the final step is a certified
  enumeration. The Stormer-Lehmer route (Pell) also fits: the finite check is a list of Pell
  fundamental solutions, which can be certified by exhibiting solutions and (the hard part)
  proving minimality, a standard continued-fraction certificate.
- Missing: nothing in Mathlib for Stormer (the closed PR is a base, licensed on submission as
  Apache; its code could be read for ideas but it was AI-written, check license and policy before
  reuse). A certified Baker-Davenport reduction step (LLL output checked exactly) is the new
  ingredient.
- Size: k up to about 12-13 (Lehmer went to p = 41, k = 13; White to p = 127 by computer) is
  days; k beyond 23 is out of reach by Stormer-Lehmer. Medium to long.
- Notice: a first machine-checked S-unit result (no such thing found) and an independent check
  of A002071; OEIS comments show people care. A discrepancy with the OEIS values or the
  abc-conditional terms of A002072 would be notable.

Lead 2. Certified Erdos-Straus verification (witness checker plus coverage proof).
- Statement: for every prime p < N (N = 10^17 or 10^18) there are positive integers x,y,z with
  4/p = 1/x+1/y+1/z, proved in Lean from (a) a verified residue-class reduction (identities of
  Mordell type for the classes not needing a filter) and (b) a certificate for each remaining
  class/batch.
- Why it fits: exhaustive certified case trees; the residue-class bookkeeping (modulus
  25,878,772,920, 2,101,514 classes) is exactly the kind of thing to prove once and check.
- Missing: raw compute is large: the 2025 preprint reports about two weeks for 10^18 on a
  "medium setup"; 24 cores could reach 10^17 or 10^18 in weeks [INFERRED], but storing a witness
  per prime is impossible (about 2.4e16 primes), so the certificate must be filter-based. Value is
  doubtful: nobody doubts the numerical claim.
- Size: weeks for the computation; certificate design is weeks more. Notice: moderate, since a
  verified bound would be the first; but a bound of 10^19 would be more cited.

Lead 3. Lehmer's number is the minimum Mahler measure for polynomials of low degree, with a
  certified proof.
- Statement: for every irreducible non-cyclotomic integer polynomial of degree at most D (D =
  12, 14, ..., as far as achievable), M(P) >= 1.17628... Currently proved computer-assisted to
  degree 54 (even degrees; MRW 2008), not formally.
- Why it fits: a finite search on coefficients bounded via auxiliary-function arguments and
  exact integer interval arithmetic; the exhaustive branch-and-bound tree can be certified in
  Lean. Interesting side result: formal Smyth bound 1.3247 for non-reciprocal polynomials.
- Missing: the MRW search is heavy (details not read); formalizing the bounding lemmas requires
  Mahler-measure and Newton-sum theory beyond Mathlib's current state. [INFERRED]
- Size: degree <= 12 or 14 plausible in weeks; the record 54 is out of reach. Notice: a formal
  certificate for any non-trivial degree would be new.

Lead 4. A certified search for covering systems with larger minimum modulus (a construction, not a
  proof of impossibility).
- Statement: find a covering system with distinct moduli and minimum modulus > 42 (exists
  maximum below 10^16 by Hough); or prove a bound for restricted lcm shapes. Certificates of
  covering are tiny to check in Lean (a decidable statement over Z/L).
- Why it fits: certificate checking is trivial; the search is where compute goes (heuristic
  search over divisor lattices of a smooth L, covering by dynamic/greedy or SAT/ILP). Owens's 42
  has stood since 2014 (per Wikipedia). I did not read about recent attempts (Balister et al.).
- Missing: success is not guaranteed; no estimate for L needed. [INFERRED]
- Size: weeks, uncertain. Notice: high if successful (breaks a long-standing record), nil if not.
  Related variant: lower bound on the number of prime factors in an odd squarefree covering (Guo-Sun
  22): improve by exhaustive case tree. Size: possibly out of reach.

Lead 5. Formal covering-set theorems for Sierpinski/Riesel and small cases, plus a verified
  eliminations check.
- Statement: 78557 * 2^n + 1 and 509203 * 2^n - 1 have a prime factor in the stated covering sets for
  every n (period 36 / 24 checks), with all k below those bounds having no such covering set of the
  same lcm (finite check over primes < 1000?), and a formally checked primality (Proth) of each
  eliminating prime.
- Why it fits: the covering side is a finite periodic check, trivial. The elimination side is
  numeric (primality proofs for million-digit numbers are not feasible in Lean).
- Size: hours to days for covering; elimination of remaining candidates is out of reach (PrimeGrid
  scale). Notice: low, because Selfridge's covering is classical; a formalization is a showcase only.

Other candidates noted but not ranked:
- Certified list of "perfect powers with a given small difference" below 10^18 (Pillai table): low
  value, since unconditional beyond a box.
- Goormaghtigh / Nagell-Ljunggren small cases (x below a bound, exponents bounded): effective
  Baker bounds plus reductions, possibly weeks; needs reading Bugeaud-Mignotte first.
- Verified LLL certificate checker in Lean (the project already checks relations exactly): a
  reusable tool; Isabelle has a full verified algorithm, so a Lean version of "certified lattice reduction
  output" (basis change matrix with determinant 1 plus short vector bound) is days.

## 5. Overlap or conflict
No overlap with the base-2/base-3 results in section 1 of the rules file. Relevant method overlap:
the project's Baker import plus exact LLL relations is the same chain as de Weger / Alvarado et al.
for S-unit equations (formal version missing), and Bennett-Billerey's note that Frey-curve methods
avoid linear forms in logarithms is a warning that for bigger S the Baker route runs into huge
bounds (their 10^18991 figure).

## 6. Sources
- https://en.wikipedia.org/wiki/St%C3%B8rmer%27s_theorem
- https://oeis.org/A002072 and https://oeis.org/search?q=Stormer+consecutive+smooth&fmt=json
- https://arxiv.org/abs/1903.00977 (and /pdf; PDF unreadable through the fetch tool)
- https://arxiv.org/abs/1901.11289
- https://arxiv.org/pdf/1603.07922 and https://ar5iv.labs.arxiv.org/html/1603.07922
- https://arxiv.org/pdf/2609.15487 (Ziegler; metadata only)
- https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Straus_conjecture
- https://arxiv.org/html/2509.00128v1 (Mihnea-Dumitru)
- https://arxiv.org/html/2602.20036v1 ; https://arxiv.org/pdf/2608.24035 (metadata only)
- https://en.wikipedia.org/wiki/Covering_system ; https://api.crossref.org/works?query=Hough+... (Annals 2015)
- https://en.wikipedia.org/wiki/Sierpi%C5%84ski_number ; https://en.wikipedia.org/wiki/Riesel_number
- https://en.wikipedia.org/wiki/Lehmer%27s_conjecture ; https://mathworld.wolfram.com/LehmersMahlerMeasureProblem.html
- https://arxiv.org/html/2409.11159v3 ; https://arxiv.org/abs/1709.03771
- https://www.isa-afp.org/entries/LLL_Basis_Reduction.html
- https://github.com/leanprover-community/mathlib4/pull/42040
- https://github.com/google-deepmind/formal-conjectures
- https://en.wikipedia.org/wiki/Goormaghtigh_conjecture ; https://en.wikipedia.org/wiki/Pillai%27s_conjecture ; https://en.wikipedia.org/wiki/Catalan%27s_conjecture ; https://en.wikipedia.org/wiki/Egyptian_fraction
- https://projecteuclid.org/journals/experimental-mathematics/volume-17/issue-4/Minimal-Mahler-Measures/em/1243429958.short (via search, not opened)

## 7. Search log
WebSearch (6):
1. formally verified S-unit equation solutions Lean Isabelle Coq
2. Lehmer's problem Mahler measure Mossinghoff list small Salem numbers verified range
3. Erdos-Straus verified up to 10^18 or 10^19, 2025 2026
4. Riesel Sierpinski problem remaining candidates PrimeGrid 2026 status
5. published list found incorrect incomplete ... erratum exhaustive search
6. Mossinghoff Rhin Wu minimal Mahler measures small degree complete degree 44

Endpoint / fetch queries (64; about 19 failed: arXiv API x6 429/timeout, OpenAlex x6 429, Semantic
Scholar 429, erdosproblems.com 403, cecm.sfu.ca 404, wayback DNS, Crossref x3 429, rieselprime 503, doi redirect not followed):
1-6 arXiv API (S-unit; Erdos-Straus; covering systems; Mahler/Salem; formalized Diophantine Lean) - failed
7-12 OpenAlex (Erdos-Straus; odd covering; verified LLL; repunits perfect powers; Sierpinski/Riesel; Stormer) - failed
13 Crossref Erdos-Straus verification; 14 Semantic Scholar verified LLL (429); 15 zbMATH S-unit; 16 OEIS Stormer search; 17 erdosproblems.com/242 (403); 18 GitHub repo search erdos straus
19 OEIS A002072; 20 Wikipedia Erdos-Straus; 21 Wikipedia Sierpinski number; 22 Wikipedia Covering system; 23 Wikipedia Repunit; 24 MathWorld Lehmer
25 Mossinghoff wayback (DNS); 26 arXiv html 2409.11159; 27 arXiv pdf 1903.00977; 28 erdosproblems.com; 29 GitHub search formal-conjectures
30 AFP LLL; 31 PrimeGrid forum; 32 Wikipedia Riesel; 33 Wikipedia Stormer; 34 Wikipedia Catalan; 35 Wikipedia Pillai
36 arXiv abs 1903.00977; 37 arXiv abs 1901.11289; 38 arXiv pdf 2609.15487; 39 arXiv abs 1709.03771; 40 GitHub formal-conjectures
41 cecm.sfu.ca Salem list (404); 42 arXiv abs 0812.0396 (irrelevant, wrong id); 43 GitHub issues mathlib Stormer/S-unit; 44 GitHub repos Sierpinski lean; 45 Wikipedia Mahler measure; 46 Wikipedia Goormaghtigh
47 mathlib PR 42040; 48 Crossref Hough; 49 Crossref Nagell-Ljunggren; 50 Crossref Salez (429); 51 Crossref MRW (429); 52 Crossref perfect powers Lucas (429)
53 Wikipedia Lehmer's conjecture; 54 doi Math. Scand. (redirect); 55 Wikipedia Salem number; 56 Wikipedia Egyptian fraction; 57 Wikipedia ABC
58 arXiv html 2509.00128; 59 arXiv html 2602.20036; 60 arXiv pdf 2608.24035; 61 arXiv pdf 1603.07922; 62 rieselprime Riesel problem (503)
63 ar5iv 1603.07922; 64 arXiv pdf 2610.08310 (metadata only)
Totals: WebSearch calls 6; endpoint queries 64 (about 45 succeeded).
