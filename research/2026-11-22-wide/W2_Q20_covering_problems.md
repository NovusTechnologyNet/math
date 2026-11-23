# W2-Q20: covering congruences and prime-free sequences (report, 22 Nov 2026)

Marks: [READ] read on the source page/PDF, [SNIPPET] only in a search result/API record/abstract,
[INFERRED] my own conclusion, [COMPUTED] my own small computation (Python, sympy, not Lean-checked).
erdosproblems.com itself returned HTTP 403 to every automated fetch (pages, /latex/, forum thread), so
the site's comments on #203 could NOT be read directly; I used a mirror and the machine-readable
list by Tao (teorth/erdosproblems), and the Lean statement in Google DeepMind's Formal Conjectures.
arXiv API, OpenAlex and Semantic Scholar answered HTTP 429 (rate limited) for all queries.

## 1. Summary

1. Erdos 203 (is there m coprime to 6 with 2^k 3^l m + 1 never prime?) is OPEN in the sources I
   could read: Tao's list says open (status updated 2025-08-31, tags primes + covering systems,
   forum with 15 posts, no prize), Formal Conjectures has it as "research open" with `sorry`.
   A mirror (primereboot/DumbPrime) printed the label "SOLVED" but gave no answer; I treat that
   as a scraping artefact (conflict noted, cannot be resolved without the live page).
2. No paper found that settles 203, or that treats 2^k 3^l m + 1 at all. The citations the task
   suggested (Banks-Finch-Luca-Pomerance-Stanica; Cohen-Selfridge) do NOT contain it: BFLPS is
   about Carmichael numbers of form 2^n k + 1 (read abstract+intro); Cohen-Selfridge 1975 is
   "not every number is a sum or difference of two prime powers" (record only).
3. [COMPUTED] Structural obstruction for 203: a covering is a covering of Z^2 (exponents k,l)
   by cosets of lattices L_p = {(k,l): 2^k 3^l = 1 mod p}, density 1/s_p with
   s_p = lcm(ord_p 2, ord_p 3). For all (A,B) up to 120 (and the grid of divisors/multiples of
   60 up to 400, e.g. 360 x 360) the total density of ALL primes whose lattices contain AZ x BZ
   is at most 0.683 (0.800 at 360 x 360) < 1, so no covering has "period box" in that range.
   The sum of 1/s_p over all primes p < 3e5 is only 2.65. A covering, if it exists, needs a
   far larger, very efficient structure. Heuristically unlikely to be findable; no proof either way.
4. Sierpinski problem (SoB): still five k left in the PrimeGrid table I read: 21181, 22699,
   24737, 55459, 67607, all complete to about n = 4.78e7 (page undated). 10223 was eliminated
   (prime 10223*2^31172165+1). 78557 conjectured smallest.
5. Riesel: 509203 conjectured smallest; per Wikipedia 41 candidates were left at Dec 2022,
   one more prime Aug 2024 (107347*2^23427517-1, 7,052,391 digits) so about 40 now (unverified).
6. Covering systems: minimum modulus <= 10^16 (Hough 2015), <= 616,000 (BBMST); best example
   42 (Owens), earlier 40 (Nielsen 2009), 25 (Gibson 2009, computer search). Odd covering problem
   open; no odd squarefree covering exists (BBMST); an odd covering needs 9 or 15 | lcm.
7. Formal verification: a complete Lean 4 proof of Erdos 2 (the negative answer, bound 616000, BBMST
   probability sieve) is listed in Formal Conjectures, in the repo linrock/math-proofs (2026),
   README claims axioms only propext/Classical.choice/Quot.sound. I did not check it.
8. Nothing found formally verifying any explicit Sierpinski covering set (78557 etc.) or Nielsen's
   system in Lean/Mathlib (GitHub repo search found nothing; absence is weak evidence).
9. Best concrete cheap leads: (a) Lean certificates for the classic covering sets (formalization of
   known results, days); (b) an exact finite search "no covering of Z^2 by 2^k3^l-lattices inside a
   given box" with a Lean-checkable infeasibility certificate (new but weak result, days);
   (c) bounded versions of the odd covering problem (finite lcm), mostly known.

## 2. What is known

### 2.1 Erdos 203
- Statement [READ, mirror + Lean file]: is there an integer m with gcd(m,6)=1 such that 2^k 3^l m + 1
  is composite for all k,l >= 0? Lean: `exists m, m.Coprime 6 /\ forall k l, not (2^k*3^l*m+1).Prime`,
  category "research open, question" (Formal Conjectures, Erdos203, with a TODO to add
  statements about covering systems).
- Mirror comments [READ]: the variant with q_1...q_r m + 1 (each q_i = 1 mod 4) has the trivial
  answer m = 1 (comment by a user "Dogmachine"), perhaps "m even" was meant; the page says Erdos
  and Graham also ask the version p_1^{k_1}...p_r^{k_r} m + 1 for distinct primes p_i; related
  entries: Sierpinski numbers = problem 1113; mirror last verified 14 Jan 2026.
- Tao's list [READ]: 203 open, no OEIS, comments none, forum 15 posts (content unreadable to me).
- Source of the problem: Erdos-Graham 1980 (monograph) [INFERRED from reference lists of 1113; not read].
- A GitHub issue titled "research: Erdos 203 - exact two-base composite covering construction"
  exists in an unrelated organisation's repository [SNIPPET]; I did not open it; treat as unreliable.

### 2.2 Sierpinski, Riesel, Brier, dual
- Sierpinski numbers: odd k, k*2^n+1 composite for all n. Infinitely many (Sierpinski 1960), 78557
  (Selfridge 1962), covering set {3,5,7,13,19,37,73} [READ, Wikipedia and BFLPS intro]. Second
  smallest known 271129 (covering {3,5,7,13,17,241}), also smallest known prime Sierpinski [READ].
- Remaining candidates [READ, Wikipedia + PrimeGrid SoB stats page]: 21181, 22699, 24737, 55459,
  67607. (BFLPS 2012 listed six: those plus 10223.)
- Erdos 1113 [READ via mirror + Lean file]: is there a Sierpinski number with NO finite covering set?
  Marked solved, yes: Izotov 1995, m = 734110615000775^4 (a perfect power). Filaseta-Finch-Kozek
  2008 conjecture: every Sierpinski number is a perfect power or has a finite covering set (Lean:
  `erdos_1113.variants.filaseta_finch_kozek`, `sorry`). FFK also showed for each l some m has
  2^k m^i + 1 composite for all 1 <= i <= l (J. Number Theory 2008, "On powers associated with
  Sierpinski numbers, Riesel numbers and Polignac's conjecture"; abstract only via zbMATH record).
- Generalized Sierpinski numbers: Filaseta-Groth-Luckner, Colloq. Math. 174 (2023) 191-201
  [SNIPPET: Crossref record, no abstract; I could not get the text]. Powers of Sierpinski numbers
  base b: Caldwell-Komatsu 2010 [SNIPPET, zbMATH]. Somer-Krizek 2025 on Sierpinski-type [SNIPPET, title
  unavailable]. Ismailescu-Park 2013: Fibonacci/Sierpinski/Riesel intersections [SNIPPET].
- Riesel: 509203 conjectured smallest; covering sets e.g. {3,5,7,13,17,241}; dual Riesel
  (|2^n - k| composite) conjectured the same set as Riesel; base-3 conjectured smallest Riesel
  63064644938 [READ, Wikipedia].
- Brier (Sierpinski and Riesel): smallest known 3316923598096294713661 [READ, Wikipedia]; OEIS
  A076335, A289110 (counts of covering sets by modulus 2n), A395816 / A397300 (Brier numbers with
  >= 2 or >= 3 minimal covering sets) [SNIPPET, OEIS name list].
- Sierpinski in several bases at once: nothing found specifically. [INFERRED] trivial by CRT once
  each base has a covering set built from disjoint prime sets, so "simultaneous in bases 2 and 3"
  (m*2^n+1 and m*3^n+1 both composite for all n) is easy, unlike 203 which needs ONE covering of
  the 2D family. Searches: "simultaneous Sierpinski", "Sierpinski numbers in several bases"
  (Crossref, zbMATH): only the items above, nothing on this.

### 2.3 Covering systems
- Erdos 1950 introduced covering systems for number theory; min modulus problem: Erdos expected
  arbitrarily large (his "favourite" problem) [READ, mirror of #2].
- Churchhouse 9 (1968), Krukenberg 18 (1971), Choi 20 (1971), Morikawa 24 (1981), Gibson 25 (2008,
  computer search with two reduction theorems) [READ, Dalton-Trifonov JIS 2022 + Crossref abstract];
  Nielsen 40 (J. Number Theory 129 (2009) 640-666: recursive construction); Owens 42 (refinement of
  Nielsen's method, thesis; cited in Dalton-Trifonov) [READ]. Nielsen himself expected the answer
  "bounded" [READ, Dalton-Trifonov quoting him].
- Upper bound: Filaseta-Ford-Konyagin-Pomerance-Yu 2007 (JAMS; Erdos-Selfridge and Erdos-Graham
  conjectures, density of uncovered set) [READ abstract]; Hough 2015 (Annals 181) <= 10^16;
  Balister-Bollobas-Morris-Sahasrabudhe-Tiba <= 616,000 ("distortion method"; survey arXiv
  2211.01417) [READ]. Squarefree moduli: Cummings-Filaseta-Trifonov 2025 (Acta Math. Hungar. 175)
  explicit bound [SNIPPET]; BBMST: no covering with all moduli odd and squarefree [READ]. Hough-Nielsen
  2019 (Duke): modulus divisible by 2 or 3 [READ]. BBMST: lcm divisible by 2, 9 or 15 [READ].
  Gyarmati, arXiv 2606.05251 (2026): "The Case of the Second Smallest Modulus" [READ title/sections
  only; PDF body unreadable by the fetch tool].
- Krukenberg (unpublished thesis 1971): classification of coverings with lcm 2^a 3^b; m<=4;
  least largest modulus 12 (m=2), 36 (m=3), 60 (m=4); squarefree with least modulus 3 still open
  [READ, Dalton-Trifonov]. Dalton-Trifonov prove the constants 60, 120, 360 are best possible
  (finite exhaustive arguments) [READ abstract].
- Odd covering (Erdos-Selfridge): open; Selfridge $2000 for an example, Erdos $25 for a "no"
  [READ, #7]. Formal Conjectures `erdos_7` is `sorry`.
- Adenwalla (arXiv 2501.15170, Dec 2025 v3): no n has its divisors >1 as moduli of a covering that
  is "as disjoint as possible" (Erdos 204), answering Erdos-Graham [READ abstract].
- Formal: Erdos 2 negative answer in Lean 4 (linrock/math-proofs, erdos-2; Solution.lean exports 4
  theorems, ~100 lines, delegating to `Erdos2.Noncoverage`; README says it follows the BBMST sieve,
  with vendored PrimeNumberTheoremAnd files, passes verify.sh and a comparator with nanoda_bin)
  [READ README summary; proof body not read]. Listed also in "Palomar" registry of Lean-verified
  results (entry page empty to my fetch).

## 3. What is open (with source)

- O1: Erdos 203, existence of m coprime to 6 with 2^k 3^l m + 1 never prime. Open per Tao's list
  and Formal Conjectures; Erdos-Graham ask the p_1^{k_1}...p_r^{k_r} m + 1 generalisation too (mirror).
  (Not found: any paper on it; searched Crossref, zbMATH, Wikipedia, GitHub, the web.)
- O2: Sierpinski problem: are 21181, 22699, 24737, 55459, 67607 Sierpinski? Stated open (PrimeGrid;
  Wikipedia).
- O3: Riesel problem (smallest 509203?), the smallest Brier number, a smaller prime Sierpinski
  number than 271129 (all stated open on Wikipedia).
- O4: Odd covering problem (Erdos 7, source: site page). Also the squarefree covering with least
  modulus 3 (Krukenberg, per Dalton-Trifonov, "still open" in 2022).
- O5: FFK conjecture on perfect powers/covering sets; infinitely many Sierpinski numbers without
  covering set (Erdos 1113 and variants).
- O6: Erdos 276 (Lucas-type sequences, composite terms, no covering): listed "conjecturally solved"
  (Graham 1964 covering; Ismailescu-Son 2014 explicit sequence believed covering-free).
- O7: Erdos 279 (primes with residues a_p such that all but finitely many integers are a_p+tp,
  t>=k); k=3 "seems difficult" [READ mirror]; the mirror labels it solved, Tao's list open: conflict.
- Gap between 616,000 and 42 in the minimum modulus problem (open, truth unknown).

## 4. Leads for this project (ranked)

L1. Lean certificates for the classic finite coverings. Statement: for 78557, 271129, 509203,
 and the smallest known Brier number, for all n, some prime of the covering set divides
 k*2^n + 1 (or - 1). Object: a prime set P (7 primes), orders ord_p(2) | 36 (lcm 36 for 78557) and
 the residue of n mod 36 for each p; certificate: `decide`/`norm_num` on the finite table
 n mod L in Fin L, plus a general lemma "p | k*2^a+1 and a = n mod ord -> p | k*2^n+1". Also
 "78557 is not itself covering-trivially prime": the smallest-prime-value side (k*2^n+1 > p) must
 be handled: every term exceeds the covering prime, easy. Size: days. Result: formalization of
 known results (nothing in Lean found); mild novelty, useful as library and test for the
 pipeline. Also feasible: Formal Conjectures `HasFinitePrimeCoveringSet 78557`. Worth noticing
 only as a contribution to Formal Conjectures/Mathlib.

L2. Erdos 203, finite search for a covering of the lattice Z^2 (exact object). Choose a finite
 abelian quotient G = Z/A x Z/B; for each prime p with ord_p(2)|A, ord_p(3)|B (primes dividing
 gcd(2^A-1, 3^B-1), rigorous to factor), L_p has index s_p = lcm(ord_p 2, ord_p 3), and the free
 choice of m mod p picks any coset. Find an exact cover/set-cover of G by distinct-prime cosets;
 certificate = list of (p, coset), checked by `decide` on |G| = A*B points, plus a lemma lifting it
 to all (k,l) and CRT for m. Necessary condition: sum of 1/s_p >= 1. [COMPUTED] this fails
 for all A,B <= 120 and for the 60-multiples/divisors grid to 360: best 0.683 and 0.800. So
 search space inside any box that a normal machine can handle is provably empty (infeasible
 certificate, easy to make Lean-checkable: finitely many primes and orders). Beyond that the needed
 lcm is astronomically larger. Size: infeasibility certificates for boxes: days; real covering:
 probably out of reach (heuristic, my reading of the densities, INFERRED). If a covering were
 found it is a new result solving an open Erdos problem (answer yes) and would be noticed; failure
 gives a "no covering with exponent period in a box" statement, weak. One cheap refinement: allow
 the covering to use also the thin lines l = 0 and k = 0 and the prime 3 (p=3 covers the l=0
 line only) and cases where 2^k 3^l m + 1 equals a covering prime: no gain in density.
 Also note a no-answer is not provable by covering methods: it would need showing every m has a
 prime (not available even for Sierpinski), so only "yes" is plausible to certify.

L3. Odd covering problem, bounded lcm. Statement: no distinct covering system with odd moduli > 1
 and lcm L, for each odd L up to some bound. Necessary: sigma(L)/L - 1 >= 1, so L abundant; the
 smallest odd abundant number is 945 = 3^3*5*7 (INFERRED, standard). Finite object: SAT/ILP over
 residues mod L for divisors d>1 of L; certificate = DRAT/LRAT proof or a decision-tree proof
 checked by Lean `decide`. Size: L up to ~10^5 to 10^6 feasible per instance on 24 cores with good
 SAT; the list of abundant odd L grows but only ones with 9|L or 15|L matter (BBMST). This is
 probably known in the literature (Guo-Sun, Simpson-Zeilberger; I did not look these up, so treat
 as INFERRED/unverified) so success would be formalization/extension of known bounds, not a
 resolution. Worth noticing only if the bound is pushed beyond published values.

L4. Covering systems with large minimum modulus: reproducing and certifying an explicit covering
 with least modulus m >= 25 (Gibson 25) or Nielsen 40 / Owens 42 in Lean: finite object is a list of
 a few thousand congruences with lcm about 10^30-10^40 (Nielsen's recursion; I do not know the size,
 not read), verification by a recursive density/decision procedure, not `decide` on the whole
 residue ring. Nobody found formalizing this. Size: weeks (need the explicit data; Nielsen's
 paper gives a construction, Owens's thesis was not found online). Result: formalization of
 known results. Finding a covering with modulus 43 or more would be a new record (the 42
 record dates from the 2010s; Gibson/Nielsen needed expert tuning): out of reach in practice.

L5. Related small Erdos items of the same flavour (tag "covering systems"; status per Tao's list):
 #2 (solved, Lean proof exists), #7 (open, odd covering), #8 (disproved, Lean), #27 (disproved,
 $100), #202 (solved, Lean), #204 (disproved, Adenwalla 2025; Lean status unknown),
 #275-#281 (mixed; #276 and #279 open or conjecturally solved per mirror), #947 (proved, Lean),
 plus Erdos 1113/Filaseta-Finch-Kozek. Only #203, #276, #279 and #7 look like candidates for
 a search with a certificate. Not tagged computational by site (the only tag seen was "verifiable"
 on unrelated entries such as 835 and 850 (Erdos-Woods)). Size: not assessed.

## 5. Overlap or conflict with the project's results
None. The project's tools (Baker, primitive divisors, LLL) do not apply to covering systems.
Only structural link: lattices L_p and orders ord_p(2), ord_p(3) use the same Zsigmondy/primitive
prime machinery (a prime with small s_p divides gcd(2^s-1,3^s-1) and is a primitive divisor of
some 2^a 3^b - 1), which could organize the L2 enumeration.
Conflicts in sources: Erdos 203 "SOLVED" (mirror) vs open (Tao, Formal Conjectures); Erdos 279 and 276
labelled solved on the mirror but open in Tao's list. Not resolved (live site blocked).
Injected text: none noticed in any page.

## 6. Sources
- https://primereboot.pages.dev/erdos/problem/203 (also /1113, /276, /7, /279, /2, /278, /204)
- https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/203.lean
  (also 2.lean, 7.lean, 1113.lean)
- https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml
- https://github.com/linrock/math-proofs/tree/7caa4144741e10f96cf79d6f7313a0efd9a18b67/erdos-2
- https://en.wikipedia.org/wiki/Sierpi%C5%84ski_number , /Riesel_number , /Brier_number , /Seventeen_or_Bust
- https://www.primegrid.com/stats_sob_llr.php
- https://math.dartmouth.edu/~carlp/CarmSier10.pdf (BFLPS)
- https://cs.uwaterloo.ca/journals/JIS/VOL25/Trifonov/trif3.pdf (Dalton-Trifonov)
- arXiv abs: math/0507374, 1703.02133, 2211.01417, 2501.15170, 2606.05251
- Crossref: 10.1016/j.jnt.2008.09.016 (Nielsen), 10.1090/s0025-5718-08-02154-6 (Gibson),
  10.4007/annals.2015.181.1.6 (Hough), 10.4064/cm9156-9-2023, 10.1007/s10474-024-01496-x
- Computation: scratchpad scripts s.py, g.py (sympy; orders and gcd factorization); not saved to the repository.

## 7. Search log
WebSearch (2 calls):
 W1 "Erdos problem 203 2^k 3^l m + 1 never prime covering congruences"
 W2 "Sierpinski Carmichael numbers Banks Finch Luca Pomerance Stanica covering 2^k 3^l m+1 composite"
Endpoint/fetch queries (about 70 attempted; ~47 returned content, rest 403/404/429/refused):
 1 erdosproblems.com/203 (403)   2 arXiv API Sierpinski+covering (429)   3 OpenAlex simultaneous Sierpinski (429)
 4 primereboot 203   5 formal-conjectures 203.lean   6 Crossref "Sierpinski numbers in several bases"
 7 Semantic Scholar (429)   8-9 teorth problems.yaml (two offsets)   10 primereboot 1113
 11 erdosproblems forum 203 (403)   12 Wikipedia Sierpinski   13 primereboot 276   14 primegrid forum
 15 Wikipedia Seventeen or Bust   16 primereboot 7   17 primereboot 279   18 primereboot 2
 19 arXiv abs 1411.3167 (wrong id)   20 OEIS json (empty)   21 zbMATH "Sierpinski numbers covering"
 22 Crossref "covering systems minimum modulus Nielsen Owens"   23 GitHub repos covering lean sierpinski
 24 arXiv API (429)   25 Crossref FFL Generalized Sierpinski   26 Filaseta slides (cert expired)
 27 arXiv pdf 2606.05251   28-31 arXiv abs math/0507374, 1703.02133, 2211.01417, 2501.15170
 32-33 erdosproblems.com/203, /latex/203 (403)   34 GitHub issues "erdos 203 covering"   35 Dalton-Trifonov PDF (read via pdftotext)
 36 primegrid forum 11140 (bad id)   37 OpenAlex (429)   38 Wikipedia Riesel   39 Wikipedia Brier
 40 primegrid sb_status (404)   41 primegrid stats_sob_llr   42 Wikipedia Sierpinski (2nd query)
 43 erdosproblems forum (403)   44 Crossref BFLPS   45 Crossref Cohen-Selfridge   46 Crossref FFK (429)
 47-50 formal-conjectures 2.lean, 7.lean; GitHub code search (403); Crossref Owens/Nielsen
 51-54 2.lean attributes; 1113.lean; Crossref Gibson; Crossref Nielsen DOI (429)
 55-57 linrock/math-proofs tree, Solution.lean, Palomar entry   58-61 teorth yaml offset 300000; primereboot 278, 202, 204
 62-65 impan page, doi.org Generalized Sierpinski, Crossref Somer-Krizek, BFLPS PDF (read via pdftotext)
 66-69 GitHub repos (sierpinski lean; erdos lean covering), CRUS (refused), OEIS text "Sierpinski Riesel Brier"
Totals: WebSearch 2; endpoint queries about 69 (counting failed ones; well over 30).
