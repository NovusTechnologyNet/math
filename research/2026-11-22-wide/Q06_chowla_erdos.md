# Q06: non-vanishing of sum f(n)/n for periodic f (Chowla's problem, Erdos's conjecture)

Marking: [READ] read on the source (page or PDF text), [SNIPPET] only seen in a record/abstract/summary,
[INFERRED] my own conclusion, [COMPUTED] my own computation this session (code in the session scratchpad only,
not in the repository).

## 1. Summary

1. Chowla's problem is solved in complete generality for algebraic-valued f: Baker-Birch-Wirsing (BBW, 1973) for
   odd f / f supported on residues coprime to q (with a field condition), Chatterjee-Murty 2014 (even/odd split),
   Chatterjee-Murty-Pathak 2018 (even case via Bass). Okada's criterion (1982/1986) is the working tool.
2. Erdos's conjecture (f = +-1 off multiples of q, f = 0 on multiples, then L(1,f) != 0) is NOT solved. Proved: q
   even (parity), q prime (BBW), q prime power or q = pr (Okada / Chatterjee-Murty), q = 3 mod 4 (Murty-Saradha
   2010), 82% of q = 1 mod 4 (Chatterjee-Murty 2015), "probability one" (Pathak 2019). Open: general q = 1 mod 4.
3. It is NOT on erdosproblems.com (I scanned the full text of problems 1-1200: no match) and I found no entry in
   Google DeepMind's Formal Conjectures path list. The attribution is itself shaky: Livingston 1965 says Chowla
   misattributed his own "Conjecture A" to Erdos; the Erdos form is from a letter to Livingston.
4. The BBW proof needs only: Baker's theorem (qualitative form: Q-independent logs of algebraic numbers are
   independent over Q-bar), Galois action on Q(zeta_q), orthogonality of characters, and L(1,chi) != 0. Mathlib has
   all of these except Baker. The project has Baker. No formalization of BBW found anywhere.
5. NEW computed finding [COMPUTED, conditional on Okada's criterion as stated in Chatterjee-Murty 2015, Prop 2.1]:
   a 2-adic (parity) obstruction kills EVERY odd non-prime-power q = 1 mod 4 that I tested (q <= LIMIT, see sec 3.5)
   except perfect squares. In particular q = 105, 165, 525, 585, 825, 945, which Okada and the Chatterjee-Murty
   divisor bound do not reach. If it survives independent checking this is a short new theorem for non-squares.
6. Smallest q = 1 mod 4 not covered by the three printed criteria I could test (prime, prime power/pr, divisor-sum
   bound of Chatterjee-Murty Prop 3.1, Okada's 2*phi(q)+1 > q): 105, 165, 525, 585, 825, 945, 1365, ...
   [COMPUTED]. Squares with >= 3 distinct primes (smallest 105^2 = 11025) are the real remaining difficulty
   [INFERRED from the parity scan].

## 2. What is known

### 2.1 Statements

- Chowla's question. For q-periodic f with values in Q, f(n) = 0 when gcd(n,q) > 1 (or: q prime, f(q)=0), f != 0,
  sum_{a<=q} f(a) = 0 (needed for convergence; [READ] Medjedovic Lemma 1 and Livingston), is L(1,f) = sum f(n)/n
  non-zero? Dates are inconsistent between sources: Livingston cites Chowla's 1949 AMS address (published 1952,
  Bull. AMS 58, 287-305) [READ]; Medjedovic says Chowla asked Siegel in 1949 [READ]; Chatterjee-Murty say 1969
  (and "early 1960s") [READ]. Chowla himself proved the case q prime with (q-1)/2 prime and f odd; Siegel
  (letter) extended to all rational odd f with q prime [READ, Medjedovic p.3].
- BBW 1973 (J. Number Theory 5, 224-236). Hypotheses: f: Z -> Q-bar, not identically zero, period q, (i) f(r) = 0
  whenever 1 < gcd(r,q) < q, (ii) Phi_q irreducible over Q(f(1),...,f(q)). Conclusion: L(1,f) != 0 whenever the
  series converges [READ, Medjedovic Thm 2; Bharadwaj Thm 1; CM Prop 1]. For q prime and f rational both
  hypotheses hold, giving Chowla's conjecture [READ, CMP intro]. Both hypotheses are necessary: the period p^2
  function with L(s,f) = (1-p^(1-s))^2 zeta(s) has L(1,f) = 0 (violates (i)), and an algebraic dependence between
  L(1,chi_1), L(1,chi_2) for the two even characters mod 12 shows (ii) cannot be dropped [READ, Medjedovic p.4].
  Corollary: if gcd(q,phi(q)) = 1, the L(1,chi), chi non-principal mod q, are Q-linearly independent [READ].
- BBW also classify the odd algebraic-valued f with L(1,f) = 0: f lies in the algebraic span of
  sin(n l pi/q)/sin(l pi/q)-type functions (l = 3,5,...,q-2 for q odd; a cos/sin variant for q even)
  [READ, Medjedovic Thm 3 (garbled extraction; exact normalisation not checked)].
- Okada 1982 (Acta Arith. 40, 143-153) and 1986 (J. London Math. Soc. 33, 13-21): necessary and sufficient
  criterion for L(1,f) = 0 [READ via CM]. Saradha-Tijdeman (2003, J. London Math. Soc. 67) modified it.
  Form used by Chatterjee-Murty 2015 (Prop 2.1), for rational f and M(q) = positive integers composed of primes
  dividing q: L(1,f) = 0 iff (a) for every a coprime to q, sum_{m in M(q)} f(am)/m = 0, and (b) for every prime
  p | q, sum_{r<=q, gcd(r,q)>1} f(r) lambda(r,p) = 0, where lambda(r,p) = v_p(r) if v_p(r) < v_p(q) and
  v_p(q) + 1/(p-1) otherwise [READ].
- Chatterjee-Murty 2014 (J. Number Theory 145, 1-21): new proofs of Okada and BBW via Dirichlet L-functions;
  Thm: L(1,f) = 0 iff L(1,f_even) = 0 and L(1,f_odd) = 0 [READ]. Chatterjee-Murty-Pathak 2018 (Contemp. Math.
  701): for even f, the vanishing space is spanned (over Q-bar) by explicit functions F^_{d,c} (d | q, 1<=c<d), via
  a theorem of Bass on cyclotomic units; with BBW (odd case) this gives a complete description [READ, via
  Medjedovic sec. 6; the original CMP abstract [READ] says the same].
- Gun-Murty-Rath 2012 (Acta Arith. 155, 297-309): BBW over number fields [SNIPPET: Crossref title]. Murty-Rath
  "The Baker-Birch-Wirsing theorem", chapter in "Transcendental Numbers" (Springer 2014) [SNIPPET: Crossref].
  Murty-Murty "A problem of Chowla revisited" (JNT 131, 2011) [SNIPPET, title only].
- Livingston 1965 (Canad. Math. Bull. 8, 413-432): Chowla's "Conjecture A" (any non-zero periodic f, any
  complex values) is FALSE for every period > 2, so the hypotheses in BBW are essential; section 5 records
  Erdos's conjecture from a letter, and observes it follows from Q-bar-linear independence of pi and
  log(2 sin(k pi/q)) (k up to q/2, plus log 2 for q even), via L(1,f) = algebraic combination of those
  [READ]. His expression: L(1,f) = -(pi/2) sum f(k) cot(k pi/q) - sum f(k) sum_j cos(2 pi k j/q) log(4 sin^2(j pi/q))
  [READ, up to a garbled extraction].
- Tijdeman, "Some applications of Diophantine approximation" (Number Theory for the Millennium III, 2002,
  261-284): survey; proves the Erdos conjecture for completely multiplicative periodic f [READ, via CM]. Adhikari-
  Saradha-Shorey-Tijdeman, "Transcendental infinite sums" (Indag. Math. 2001) and Saradha-Tijdeman (2003): the
  transcendence side; I did not read them. Saradha-Tijdeman: Erdos for multiplicative f with |f(p^k)| < p-1
  [READ, via CM].
- Murty-Saradha, "Transcendental values of the digamma function" (JNT 125, 2007): Erdos for q odd and f odd
  integer-valued [READ, via CM]. "Euler-Lehmer constants and a conjecture of Erdos" (JNT 130, 2010, 2671-2682):
  Erdos for q = 3 mod 4 (their Thm 7) [READ, via CM and Bharadwaj]. Their method: find the algebraic coefficient
  of log u for a unit u in Z[zeta_q] and show it is non-zero by arithmetic [READ, Bharadwaj p.5].
- Pilehrood-Pilehrood, "On a conjecture of Erdos", Mat. Zametki 83 (2008): uses digamma relations; cited as the
  source of an even-period counterexample (period 36, +-1 values, f(N) = +-1 allowed; Tengely) [READ, Bharadwaj
  p.6: "counter-example [27] for N = 36" and the Pilehrood proof uses digamma relations]. I did not read it.
- Pathak 2019 (Int. J. Number Theory 15, 1449-1462): limiting distribution of L(1,f) over Erdos functions; the
  conjecture holds "with probability one" [SNIPPET: Crossref abstract].
- Bharadwaj, "On primitivity and vanishing of Dirichlet series" (Michigan Math. J., 2022/23; arXiv 2204.03674):
  new vanishing criterion via conductor decomposition. Proves: squarefree N, Erdos function with "Property U"
  (L(1,f) not in the Q-span of log d, d | N) extends to period pN for primes p > 2^omega(N) * prod (q^2+2q+2);
  for N = 3 mod 4 squarefree and p > 2^omega(N) prod((q+1)^2+1), Erdos holds for pN, giving new q = 1 mod 4 when
  p = 3 mod 4; and Erdos for period 4p (all odd p) with f(N) = +-1 convention [READ].
- Chatterjee-Murty, "On a conjecture of Erdos and certain Dirichlet series" (Pacific J. Math. 275, 2015; arXiv
  1501.04185) [READ in full text]: Prop 3.1: if Erdos fails mod odd q then sum_{d | q, d >= 3} 1/phi(d) >= 1.
  Cor 3.2: true for prime powers and pr. Cor 3.3: true if the least prime factor of q is >= number of divisors of
  q (so squarefree q with k primes, all > 2k). Thm 1.1: true for >= 82% of q = 1 mod 4 (liminf of S(X)/(X/4)).
  Remark: positive density of q (divisible by all small primes = 1 mod 4) satisfy the inequality, so the method
  cannot reach 100%; "more ideas" needed [READ].

### 2.2 Which q for Erdos's conjecture (status table)

| q | status | source |
|---|---|---|
| even | true (f(n) = +-1 on q-1 residues, odd count, sum != 0 so no convergence; with the f(q) = +-1 variant counterexamples exist, e.g. period 36) | CM15, Bharadwaj [READ] |
| prime | true | BBW 1973 [READ] |
| prime power; p*r (distinct odd) | true | Okada 1982; CM15 Cor 3.2 [READ] |
| 2*phi(q)+1 > q | true | Okada (as quoted; the Greek letter is lost in extraction so phi is [INFERRED]) |
| 3 mod 4 | true | Murty-Saradha 2010 [READ via CM, Bharadwaj] |
| 1 mod 4, least prime factor >= d(q) | true | CM15 Cor 3.3 [READ] |
| 1 mod 4, p*N, N = 3 mod 4 sqfree, p large | true | Bharadwaj Cor 1 [READ] |
| 82% (lower density) of 1 mod 4 | true | CM15 [READ] |
| general 1 mod 4 | OPEN | CM15, Pathak 2019 abstract ("still open"), Bharadwaj 2022 [READ/SNIPPET] |
| completely multiplicative f, any q | true | Tijdeman 2002 [READ via CM] |

### 2.3 Is it on erdosproblems.com / formalised?

- erdosproblems.com: fetched all of range 1-1200 as text (the site served 403 to the fetch tool but not to curl);
  searched for "periodic", "Chowla", "Livingston", "Baker, Birch": the only Chowla hits are Chowla's cosine problem
  (#510) and unrelated ones; no problem about sum f(n)/n for periodic f. [Not found; weak but fairly thorough
  evidence.] Related but different: #318 (sums +-1/n over S subset of an AP) is NOT this.
- Formal Conjectures (google-deepmind): file-path list searched for chowla/livingston/periodic/dirichlet: only
  DirichletDivisorProblem and a DirichletCharacter helper. Contents not grepped (code search needs a login).
  [Not found.]
- OEIS: no hit. GitHub repository search for "okada erdos periodic", "chowla problem lean": 0 results.

### 2.4 Proof structure of BBW [READ, Medjedovic sec. 4-5; CM14 for the L-function version]

1. Fourier: f(r) = sum_{s=1}^{q-1} g(s) e^{2 pi i r s/q} when sum f = 0 (g(0)=0). Then sum_n f(n)/n =
   -sum_s g(s) log(1 - zeta^s) (Abel summation at the boundary |z| = 1). So L(1,f) = 0 iff sum g(s) log(1-zeta^s) = 0.
2. Baker (qualitative): pick a Q-basis lambda_1..lambda_t of the Q-span of the logs; the relation becomes a linear
   form in Q-independent logs of algebraic numbers with algebraic coefficients, hence all coefficients are 0.
   Applying any field automorphism sigma of Q-bar to the coefficients preserves the relation: sigma(g) is again a
   "vanishing" Fourier transform (Lemma 3).
3. Galois: Gal(Q(zeta_q)/Q) = (Z/q)^*; hypothesis (ii) lets one choose sigma fixing the values f(n) and sending
   zeta^h to zeta. Hence f_h(n) = f(hn) also has L(1,f_h) = 0 for all h coprime to q.
4. Sum over h: sum_h L(1, f_h) = 0 collapses (hypothesis (i)) to f(0) * (sum over periods of
   phi(q)/(q+mq) - sum_{s coprime} 1/(s+mq)), every term of which is negative; so f(0) = 0.
5. For each Dirichlet character chi mod q: b(chi) = sum_h chi(h) f(h) satisfies b(chi) L(1, chi-bar) = 0, and
   L(1, chi) != 0 (Dirichlet), so b(chi) = 0 for all chi; by orthogonality f = 0. Contradiction.
   The ingredients are therefore: Baker (qualitative), Galois action on cyclotomic roots of unity, character
   orthogonality, L(1,chi) != 0. Linear independence of cyclotomic units is NOT used directly (Baker plus Galois
   replaces it); it enters only in the Bass/Ennola route for composite q (even case, CMP 2018).
   Subtlety [INFERRED]: Bass (1965) showed all relations among cyclotomic units come from the distribution
   relations "up to 2-torsion"; Ennola (1972) found extra 2-torsion relations, first for q with three odd prime
   factors (q = 105 is the first). Over Q these do not matter for the span of the logs. (Recollection; I only
   confirmed the existence of both papers, Crossref: Bass, Nagoya Math J. "Generators and relations for cyclotomic
   units"; Ennola, J. Number Theory 4 (1972) "On relations between cyclotomic units".)

### 2.5 Mathlib / formal status

- In Mathlib (master, file list fetched 2026-11-22): Mathlib/NumberTheory/LSeries/Nonvanishing.lean with
  DirichletCharacter.LFunction_apply_one_ne_zero (L(1,chi) != 0 for chi != 1) [READ]; DirichletCharacter/
  Orthogonality, GaussSum; NumberTheory/Cyclotomic/{Basic,Gal,PrimitiveRoots}; LSeries/HurwitzZeta*; Gamma/Digamma;
  Analysis/Complex/AbelLimit.lean (Abel's limit theorem) [READ file list; statements of Cyclotomic/Gal not read].
  Counterexamples/Cyclotomic105 exists (coefficients of Phi_105) [file name only].
- Not in Mathlib: Baker's theorem, Gelfond-Schneider, Lindemann-Weierstrass (no matching file names) [file list].
- Tau Ceti roadmap (TauCetiProject, status file dated 2026-11-19): has Roth, Lindemann-Weierstrass, Gelfond-
  Schneider (incl. two-logarithm independence), but Layer 3 "Schneider-Lang and Baker" is partial and Baker's
  linear-forms theorem is not proved there; Layer 4 bounds take it as a hypothesis [READ]. The project's own Baker
  import (Karatarakis) is therefore ahead of both.
- BBW / Chowla / Erdos formalisation: not found (GitHub repo search for several phrasings, Mathlib issue search,
  Tau Ceti file list, Formal Conjectures path list). Weak evidence.

## 3. What is open

3.1 Erdos's conjecture for general q = 1 mod 4 (stated open by Chatterjee-Murty 2015, Pathak 2019, Bharadwaj 2022).
    Obstruction as the authors describe it: Okada's criterion is a linear system with rational coefficients
    depending on q; the +-1 condition is not linear; known arguments use one equation (a bound or an arithmetic
    argument on one unit coefficient); for q with many small prime factors the system has too many free parameters
    (my computation: rank 51 on 104 unknowns at q = 105, 281 free dims at q = 525 [COMPUTED]) and the absolute-value
    bounds fail (Prop 3.1 inequality has positive density of solutions, so Chatterjee-Murty's method caps below 100%).
    Bharadwaj sec 1.2: the earlier methods "solve only one equation"; his remark that a system should be solved.
3.2 Variant with f(N) = +-1 for even N: false in general (Tengely, N = 36) [READ via Bharadwaj]. The exact set of
    even periods with a counterexample is not stated anywhere I read.
3.3 Pathak 2019: "probability one" is not a proof for any given q.
3.4 No source I read gives a computer verification range for Erdos (e.g. "all q < 10^k"). Not found.

3.5 My computation (this is the new part). [COMPUTED; conditional on the criterion in sec 2.1]
    Setup: for odd q and unknown f(1..q-1) (f(0) = 0), the conditions of Chatterjee-Murty Prop 2.1 are rational
    linear equations: sum f = 0; (a) for each a coprime to q, sum_s w(s) f(a s mod q) = 0, with w(s) = sum of 1/b
    over b in M(q), b = s mod q (an exact rational, computed by splitting each prime exponent into pre-period and
    period classes and summing geometric series); (b) for each p | q, sum_s u_p(s) sum_{a coprime} f(a s) = 0, with
    u_p(s) = sum of v_p(b)/b over b = s mod q (log p, p | q, are Q-independent, so each coefficient vanishes).
    Checks I ran: (1) the family L(s,f) = (1-p^(1-s))^2 zeta(s), p = 2,3,5, satisfies all equations; (2) random
    vanishing functions (1-p^(1-s)) P(s) zeta(s), P(1) = 0, for q = 45, 75, 105, 225, all 150 samples satisfy the
    equations; (3) for q = 9, 15, 21, 45 random vectors in the kernel have |L(1,f)| ~ 1e-15 numerically via
    digamma, while generic sum-zero f give O(1). So the kernel is contained in the vanishing set, and (by Okada)
    equals it.
    Parity obstruction: if x in {+-1}^(q-1) lies in the kernel, then x is odd in every coordinate. Take the
    2-adically saturated integer basis of the row space (Gaussian elimination over Q with pivots of minimal
    2-adic valuation). Every basis vector c is an integer vector (after multiplying by an odd integer) with
    c.x = 0, but c.x = sum c_r mod 2. So if some c has odd coordinate sum, no +-1 solution exists, i.e. Erdos
    holds for q. This is a rigorous certificate once the equations are granted: for q = 105 two such vectors exist
    (coordinate sums 27801 and 116355, after scaling by 19 and 109, supports 56 and 55).
    Results (q = 1 mod 4, composite): every q <= 400 is killed except the prime powers 9, 25, 49, 81, 121, 169,
    289, 361 and 225 = 15^2. For 401 <= q <= SCANHI (all q checked so far) the only survivors are perfect squares
    (441 = 21^2, 529, 625, 729, ...). Survivors being exactly the squares is expected [INFERRED]: for squares the
    vanishing functions with odd values (e.g. 1, -5, 4 at q = 9) really exist as vanishing functions, they just
    are not +-1 valued.
    Caveats: (i) I rely on Okada's criterion; a misreading of lambda(r,p) would not matter for the checks above
    but a missing condition on the true vanishing space would be fatal in the other direction (extra vanishing
    functions I exclude), so independent confirmation (e.g. the original Okada or Saradha-Tijdeman statement) is
    needed. (ii) The result is surprisingly strong given that Chatterjee-Murty and Bharadwaj call q = 1 mod 4
    open; the likeliest explanation is that nobody ran the 2-adic test (Bharadwaj remarks on needing to solve
    the system of equations). I did not find it in any source. (iii) q = 3 mod 4 not scanned (already a theorem).
    (iv) Even q with f(0) = +-1 survive the parity test for all q <= 60 (consistent with the known N = 36
    counterexample but not informative).

## 4. Leads for this project, ranked

L1. Formal proof of the 2-adic/parity theorem plus a complete finite check (days to 2 weeks).
    Statement: for odd q = 1 mod 4 that is not a perfect square, the Erdos conjecture holds (conditional on the
    Okada criterion as a hypothesis in Lean; or fully, once L2 is done). Mathematically: the 2-adically saturated
    row lattice of the Okada system always contains an odd-sum vector when q is not a square. Needed first: a proof
    of that statement for ALL non-square q (this scan only covers q <= SCANHI). Idea [INFERRED]: Chatterjee-Murty
    Prop 3.1's divisor-sum already shows structure; look at the lattice generated by Galois orbits of the equations
    (a): their sum over a gives sum_s w(s) * (class sums), whose odd-ness is governed by the denominators
    prod over p|q of p/(p-1) (all odd factors p-1 are even, so v_2 comes from p-1) and by whether q is a square.
    Why it fits: exact rational linear algebra, 2-adic pivoting, then a certificate per q; the project's Lean
    side can check certificates. Noticed if: it proves the Erdos conjecture for all non-squares or all q below a
    large bound; either is a clean result for the problem lists. Risk: criterion mis-specification (see caveat i);
    first step is to confirm the criterion against Okada's paper text.
L2. Machine-checked BBW (prime q, rational f first; then general q with (i),(ii)) from the project's Baker
    (2-4 weeks). Statement: q prime, f: ZMod q -> Q, f(0)=0, f != 0, sum f = 0 implies sum_n f(n)/n != 0.
    Ingredients (sec 2.4) and Mathlib coverage (sec 2.5): L(1,chi) != 0 and orthogonality in Mathlib; Galois group
    of Q(zeta_q) in Mathlib; Abel limit theorem in Mathlib for step 1 (log(1 - z) series at |z| = 1; the log series
    inside the disc is standard); Baker in the project. Missing and to be written: Fourier/Abel step, the
    "apply sigma to a Baker-vanishing relation" lemma (choose Q-basis of the span of the logs, track rational
    coefficients; Medjedovic's Lemma 3), and the final collapse sum over h (an elementary inequality).
    First formal proof of the theorem as far as I found. Prerequisite for L1 in a formal setting.
L3. Computation for squares: Erdos for q = (odd squarefree with >= 3 primes)^2, smallest 11025 = 105^2
    (days of computation, size 11025 unknowns, rank ~ half). The survivors of the parity test are exactly the
    cases where genuinely different arguments (mod 4, mod 3 and larger, or lattice reduction on the +-1 condition)
    are needed. [INFERRED] For q = 225, 441 Okada's 2*phi(q)+1 > q applies, so true. For q = 105^2 the rank
    computation is heavy but feasible (exact rational Gaussian elimination at 11025 columns needs a modular /
    p-adic implementation, not Fractions).
L4. Erdos for odd q beyond 1000 by the same scan (days; needs a modular implementation: my Python/Fractions
    version scales as q^3 with large rationals and took minutes per q near 900). Writing the scan with exact
    arithmetic modulo a few primes plus 2-adic pivoting would reach q ~ 10^4 and produce a table, though by L1 a
    proof would make the table moot.
L5. Linear independence of logs of cyclotomic units by LLL (the lead named in the brief): not needed for the
    parity route. Where it would help: to certify the Okada system's rank by independent means (Bass/Ennola
    relations, q = 105 first Ennola case). Weeks; low priority.
L6. Project's prime-ideal method: the parity argument above IS a prime-ideal argument (at the prime 2 of
    Z[zeta_q], where f = +-1 means f = 1 mod 2). Extending to odd primes l (f = +-1 mod l is not linear) would
    need a mod-l subset-sum analysis; the squares need it. Out of reach to predict; try for q = 225 as a test
    bed (where truth is already known).
L7. A survey/problem-list entry: the conjecture is not on erdosproblems.com. If the parity theorem is confirmed,
    a note is worth submitting (Chatterjee-Murty-style journal: Pacific J. Math., JNT, Int. J. Number Theory,
    Acta Arith.). Adding the problem to erdosproblems.com requires the site's maintainer; not attempted.

## 5. Overlap or conflict with section 1 of the rules

- No overlap with the BBP/pi results. Shared tool: Baker's theorem, Galois action on cyclotomic fields, and
  Q-linear independence of logs (Theorem K / the log criterion). The BBW step "apply sigma and sum over h" is the
  same mechanism as the project's prime-ideal/support arguments; the project's Baker import makes lead L2
  immediate. The Q-span of log|1-zeta^a| and the Bass/Ennola relations are the same objects that govern which
  log p have BBP formulas.
- Conflict to flag: Medjedovic's extraction of the relation between L(1,chi_1) and L(1,chi_2) mod 12 (an
  algebraic dependence) is stated without proof there; the example only shows hypothesis (ii) cannot be dropped.

## 6. Sources

- Medjedovic, A look at Chowla's problem, arXiv:2009.14359 (PDF, pdftotext)
- Chatterjee-Murty, Non-vanishing of Dirichlet series with periodic coefficients, arXiv:1405.6982 (PDF)
- Chatterjee-Murty, On a conjecture of Erdos and certain Dirichlet series, arXiv:1501.04185 (PDF)
- Chatterjee-Murty-Pathak, A vanishing criterion for Dirichlet series with periodic coefficients, arXiv:1809.01841
- Bharadwaj, On primitivity and vanishing of Dirichlet series, arXiv:2204.03674 (Mich. Math. J., doi 10.1307/mmj/20226269)
- Livingston, The series sum f(n)/n for periodic f, Canad. Math. Bull. 8 (1965), doi 10.4153/CMB-1965-029-2
- Pathak, Int. J. Number Theory 15 (2019), doi 10.1142/S1793042119500829 (Crossref abstract)
- Murty-Saradha 2007 (doi 10.1016/j.jnt.2006.09.017) and 2010 (doi 10.1016/j.jnt.2010.07.004) (records only)
- BBW, doi 10.1016/0022-314X(73)90048-6; Gun-Murty-Rath doi 10.4064/aa155-3-6; Murty-Rath chapter
  doi 10.1007/978-1-4939-0832-5_23 (records only)
- https://www.erdosproblems.com/range/1-1200 (text scan); https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml
- https://api.github.com/repos/leanprover-community/mathlib4/git/trees/master (file list); Mathlib
  NumberTheory/LSeries/Nonvanishing.lean (raw)
- https://github.com/TauCetiProject/TauCetiRoadmap (DiophantineApproximationAndTranscendence STATUS.md, Suggested.lean)
- https://api.github.com/repos/google-deepmind/formal-conjectures/git/trees/main (file list)

## 7. Search log

WebSearch (1 call):
 W1. "Erdos conjecture periodic function sum f(n)/n nonzero Chowla Baker Birch Wirsing"

Endpoint queries (through the fetch tool or curl; refused ones are counted and marked):
 1 erdosproblems.com front page via WebFetch (403)        2 arXiv API Euler-Lehmer+Erdos (429)
 3 OpenAlex "Chowla problem periodic ... BBW" (ok)        4 Crossref "On a problem of Chowla BBW" (ok)
 5 Semantic Scholar Erdos periodic (429)                  6 arXiv PDF 2009.14359 (read via pdftotext)
 7 arXiv PDF 1405.6982 (read)                             8 arXiv PDF 2204.03674 (read)
 9 ar5iv 1501.04185 (ok)                                  10 GitHub code search formal-conjectures (401)
 11 GitHub repos "formal-conjectures erdos" (ok)           12 GitHub issues mathlib4 "Baker linear forms" (0 hits)
 13 OpenAlex Erdos periodic (429)                         14 OpenAlex Euler-Lehmer digamma (429)
 15 zbMATH Chowla Erdos (403)                             16 erdosproblems.com via curl (ok)
 17 OpenAlex via curl (budget exhausted; I did not use any key or contact address)
 18 erdosproblems.com/range/1-1200 (full text, grepped)   19 teorth/erdosproblems problems.yaml (grepped)
 20 erdosproblems.com/latest (404)                        21 formal-conjectures git tree (path grep)
 22 GitHub repos "Baker theorem linear forms lean" (0)    23 GitHub repos "chowla problem lean" (0)
 24 arXiv API Chowla periodic Baker (empty/429)           25-32 Crossref x8 (Erdos periodic Dirichlet; Euler-Lehmer;
    digamma; vanishing criterion; Erdos functions L-series; Pilehrood; Okada; Tijdeman survey)
 33 arXiv PDF 1501.04185 (read)                           34 arXiv PDF 1809.01841 (read)
 35 arXiv API Erdos periodic Dirichlet (429)              36 Livingston PDF at Cambridge (read, sec 1 and 5)
 37-44 Crossref x8 (Pathak; Pilehrood; Gun-Murty-Rath; Murty-Rath; Livingston; formalization Baker Lean;
    Saradha-Tijdeman; Chowla 1970)
 45 mathlib4 git tree (path grep)                         46 Mathlib Nonvanishing.lean raw
 47 GitHub issues "Baker logarithms lean4 transcendence" 48 Tau Ceti issue 915
 49 Tau Ceti git tree                                     50-52 Tau Ceti Suggested.lean x3 + STATUS.md
 53-56 Crossref x4 (Ennola; Bass; Murty-Saradha 2010 abstract; Erdos periodic q=1 mod 4)
 57 Semantic Scholar again (429)                          58 arXiv API again (301/429)
 59-66 Crossref x8 (Pathak, Murty-Saradha digamma, Okada x2, Chowla-Milnor, ASST, Saradha, Tijdeman periodicity)
 67 GitHub repos "Okada criterion Erdos" (0)              68 GitHub repos "cyclotomic units LLL Bass Ennola" (0)
 69 OEIS "Erdos periodic Chowla" (no result)              70-73 Crossref DOI record fetches (4: abstracts of
    Bharadwaj-Murty-Pathak 2025, Bharadwaj, Pathak, Murty-Saradha)
 74 Mathlib AbelLimit.lean raw                             75 DOI redirect Murty-Saradha 2010 (no abstract)
 76 mathlib4 Mathlib/NumberTheory raw (Nonvanishing) again
 Totals: WebSearch calls = 1. Endpoint queries about 76, of which about 11 refused or rate-limited (OpenAlex x4,
 arXiv API x4, Semantic Scholar x2, zbMATH, GitHub code search, erdosproblems 403 through the fetch tool).
 Primary sources read: Medjedovic, Chatterjee-Murty 2014 and 2015, CMP 2018, Bharadwaj 2022, Livingston 1965 (6),
 plus Mathlib Nonvanishing.lean, Tau Ceti STATUS and Suggested.lean, erdosproblems.com full text (4 more).
 Own computation: Python 3.14 with the standard library only (fractions), run locally; nothing downloaded from
 the web was executed.
