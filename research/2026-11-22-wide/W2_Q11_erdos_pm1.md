# W2-Q11: Erdos's conjecture on sum f(n)/n for f = +-1 (period q, f = 0 on multiples of q): exact state of the art, and a check of the Q06 parity claim

Marking: [READ] read on the source (page, PDF text, or page image of a scanned PDF), [SNIPPET] only in a search result / abstract / API
record, [INFERRED] my own conclusion, [COMPUTED] my own computation this session (code only in the session scratchpad, standard
library plus numpy, nothing from the web executed).

## 1. Summary

1. I obtained OKADA'S ORIGINAL 1982 PAPER (Acta Arith. 40, 143-153; scanned PDF at matwbn.icm.edu.pl, read as page images) and
   read Theorem 10, the criterion, in the original. I also read Chatterjee-Murty 2015, Bharadwaj 2022, Pathak 2018 and 2019 in full
   text. The 1986 J. London Math. Soc. paper and Tijdeman's survey were not obtainable; Murty-Saradha 2010 and Pilehrood-Pilehrood
   2008 were not obtainable either (records only).
2. State of the art (Erdos for f = +-1 off multiples of q, f(q) = 0): TRUE for q even (trivial, no convergence), q prime
   (Baker-Birch-Wirsing 1973), 2*phi(q)+1 > q (Okada 1982, Cor. 16; covers prime powers and q = p*r), q = 3 mod 4 (Murty-Saradha
   2010), least prime factor >= number of divisors (Chatterjee-Murty 2015), at least 82 percent of q = 1 mod 4 in the lower-density
   sense (Chatterjee-Murty 2015), and some products p*N (Bharadwaj 2022). OPEN for general q = 1 mod 4; all three later papers say so.
3. Obstruction as the literature describes it: the vanishing condition is a rational linear system whose size depends on q; the
   printed proofs use ONE equation (absolute values, or one unit coefficient), and the absolute-value method provably cannot reach
   100 percent. Nobody in print (that I found) solves the whole system.
4. Q06's claim [reproduced]: using Okada's system, a 2-adic parity argument kills EVERY composite non-prime-power q = 1 mod 4 that I
   tested except perfect squares. I rebuilt the system independently in a second code, verified it against Okada's original Theorem 10
   (same row space for q = 9, 15, 21, 45, 75, 105 and same dimension count as Okada), validated the parity routine on 300 synthetic
   solvable systems (no false kill), and reproduced the result: composite non-prime-power q = 1 mod 4 below 480: the ONLY survivors
   are 225 and 441 (squares). q = 3 mod 4 below 200: no survivors.
5. Verdict: the claim is mathematically sound as a finite computation and reproducible; I found nothing in print that states it
   (weak evidence: searches of titles/abstracts and full texts of the main papers). It is NOT proved for all non-squares; and the
   survivors (squares) are exactly where the question stays open. So: "plausibly new for a finite range, unproved in general, likely
   provable"; the right next step is a proof, not a larger table (section 4).
6. Livingston's conjecture (Q-bar-linear independence of pi-free log(2 sin(pi a/q)) values, the route he proposed to Erdos) is FALSE
   for composite q >= 4 (Pathak 2018) and true for prime q; Chatterjee-Dhillon 2019 reproved this and gave a corrected statement.
7. Not on erdosproblems.com (the machine-readable problems.yaml, 1221 entries, has no entry about periodic f; it only has
   Chowla's cosine problem). Erdos's own attribution is only a letter to Livingston; Pathak calls it "folklore".
8. A new small exact question in print (Bharadwaj 2022, section 8): is there an odd N with signs a_d = +-1 (d | N, d > 1, a_1 = 0)
   such that sum a_d phi(d) = 0 and then f(n) = a_(N/gcd) type functions land in the Q-span of log p? I searched the whole
   gcd-type subfamily by exhaustive enumeration (all odd N below 3500 with at most 25 divisors, and N = 11025 = 105^2): NO solution
   [COMPUTED]. Only the subfamily, not the conjecture.

## 2. What is known (marked)

### 2.1 Okada's criterion, exact statement [READ in the original, Acta Arith. 40 (1982) pp. 143-153]

Setting [READ]: q >= 2, f: Z -> algebraic numbers with period q, hypothesis (B): Phi_q (q-th cyclotomic polynomial) irreducible
over Q(f(1),...,f(q)). Notation: P = primes dividing q, J = {a: 1<=a<=q, (a,q)=1}, L = {r: 1<=r<=q, 1<(r,q)<q}, L' = L union {q}.
For r in L' put P(r) = {p in P : v_p(r) >= v_p(q)}, and eps(r,p) = v_p(q) + 1/(p-1) if p in P(r), else v_p(r).
For r in L and a in J: A(r,a) = (1/(r,q)) * prod_{p in P(r)} (1 - p^(-phi(q)))^(-1) * sum over n in S(r) of delta(r,a,n)/n, where
S(r) = {prod_{p in P(r)} p^(a(p)) : 0 <= a(p) < phi(q)} and delta(r,a,n) = 1 if r = a*(r,q)*n mod q, else 0.
Theorem 10 [READ]: if f satisfies (B), then sum f(n)/n = 0 (convergent) iff (f(1),...,f(q)) solves the phi(q)+t(q) homogeneous
rational linear equations (t(q) = number of primes dividing q):
   f(a) + sum_{r in L} f(r) A(r,a) + f(q)/phi(q) = 0   for each a in J,
   sum_{r in L'} f(r) eps(r,p) = 0                      for each p in P.
Consequences stated by Okada [READ]: Cor. 16: if 2*phi(q)+1 > q then Erdos's conjecture is true for q; example: true if the smallest
prime factor p0 >= t/log 2 + 1. Okada cites Livingston 1965 p. 430 for the conjecture ("partial answer"). Convergence is equivalent
to sum_{r=1..q} f(r) = 0 (Lemma 1 there). Remark at the end: for EVEN f the irreducibility hypothesis is not needed.
Okada's proof is a modification of Baker-Birch-Wirsing and rests on Baker's linear forms in logarithms plus Lehmer's formula
sum f(n)/n = sum f(r) H(r), H(n) = -(1/q) sum_(r<q) zeta^(-rn) log(1 - zeta^r) [READ]. The 1986 J. London Math. Soc. paper
("Dirichlet series with periodic algebraic coefficients") I could not obtain; only its title and the citation by others
[SNIPPET].
Saradha-Tijdeman (2003) rewrote the criterion into the form quoted by Chatterjee-Murty 2015, Prop. 2.1 [READ]:
(a) for each a coprime to q: sum_(m in M(q)) f(am)/m = 0 (M(q) = integers composed of primes dividing q), and
(b) for each p | q: sum_(r<=q, (r,q)>1) f(r) lambda(r,p) = 0, lambda(r,p) = v_p(r) if v_p(r) < v_p(q), else v_p(q)+1/(p-1).
[COMPUTED] these two forms have the SAME solution space: for q = 9, 15, 21, 45, 75, 105 the row spaces (original Okada Theorem 10
rows, and the Chatterjee-Murty rows together with the row sum f = 0) coincide; both have rank phi(q)+t(q) (51 at q = 105).
The solution space with f(q) = 0 therefore has dimension q - phi(q) - 1 - t(q) (e.g. 53 at q = 105) [COMPUTED, matches Okada's count].
Bharadwaj 2022 (Theorem 4) gives a different necessary and sufficient condition for rational f, with d(N)+omega(N) conditions,
using primitive-character decomposition [READ].

### 2.2 Theorems and which q they cover

- Baker-Birch-Wirsing 1973 (J. Number Theory 5, 224-236): algebraic f, f(r) = 0 for 1 < (r,q) < q, (B); then L(1,f) != 0 when
  f != 0. Gives q prime [READ, as quoted by Okada, Bharadwaj, CM].
- Okada 1982: 2*phi(q)+1 > q, hence prime powers and p*r (distinct odd primes) [READ, original].
- Tijdeman 2002 (Number Theory for the Millennium III): Erdos for completely multiplicative periodic f; Saradha-Tijdeman 2003
  (J. London Math. Soc. 67): multiplicative f with |f(p^k)| < p-1 [READ, via Chatterjee-Murty 2015 intro].
- Murty-Saradha 2007 (J. Number Theory 125): q odd and f odd integer-valued; 2010 (J. Number Theory 130, 2671-2682): q = 3 mod 4
  (their Theorem 7) [READ via CM 2015 and Bharadwaj]. Method: find a unit u in Z[zeta_q] whose log coefficient in L(1,f) is non-zero
  by an arithmetic argument, i.e. a single equation (Bharadwaj, sec. 1.2) [READ]. Original not read.
- Murty-Saradha / Murty-Pathak: for q = 2 mod 4 and f = +-1 (including f(q) = +-1 in that convention), L(1,f) != 0 because the
  coefficient of log 2 is non-zero "owing to a parity obstruction" [READ, Bharadwaj sec. 5, citing Murty-Pathak, The Okada space and
  vanishing of L(1,f), Funct. Approx. Comment. Math. 2022, doi 10.7169/facm/1952; abstract SNIPPET: builds an explicit Q-basis of the
  Okada space O(N) = {f mod N rational, L(1,f) = 0} and extends BBW and Murty-Saradha]. I did not obtain this paper's text.
  So parity arguments ARE in print, for even N; I did not find one for odd q.
- Tengely (exhaustive search, reported by Tijdeman 2008, "Periodicity and almost-periodicity", Bolyai Soc. Math. Stud. 15, 381-405):
  a period-36 function with all 36 values +-1 (f(36) = +1) with L(1,f) = 0 [READ the table in Bharadwaj sec. 5.1]. So the "f(N) = +-1"
  variant is false in general; it is NOT Erdos's conjecture (f(q) = 0).
- Chatterjee-Murty 2015 (Pacific J. Math. 275, 103-... ; arXiv 1501.04185) [READ in full]: Prop. 3.1: if Erdos fails for odd q then
  sum_(d | q, d >= 3) 1/phi(d) >= 1. Cor. 3.2: prime powers, p*r. Cor. 3.3: true if the least prime factor >= d(q) (so squarefree q with
  k primes, all > 2k). Thm 1.1: liminf S(X)/(X/4) >= 0.82 for q = 1 mod 4 up to X (first moment 0.67, second 0.78, moment r = 3.85
  gives 0.82). They say the method cannot give 100 percent ("more ideas are needed").
- Pathak, Int. J. Number Theory 15 (2019), arXiv 1909.03972 [READ intro]: values L(k,f) over Erdos functions have a limiting
  distribution; the conjecture holds "with probability one"; the abstract says the conjecture "is still open in the case q = 1 mod 4"
  (the abstract text also mentions the condition 2*phi(q)+1 <= q; the extraction is garbled).
- Bharadwaj, Michigan Math. J. (2025 record; arXiv 2204.03674, single version, April 2022) [READ]: Theorem 2 (descent: Erdos with
  Property U for squarefree N extends to pN for primes p > 2^omega(N) * prod_(q | N)(q^2+2q+2)); Corollary 1 (N = 3 mod 4 squarefree,
  p > 2^omega(N) * prod((q+1)^2+1): Erdos holds for pN, giving new q = 1 mod 4 when p = 3 mod 4); Theorem 3 (period 4q, q odd prime,
  values +-1: L(1,f) != 0). Property U: L(1,f) not in Q-span of log d, d | N.
- Bharadwaj-Murty-Pathak 2025 [SNIPPET: a Crossref record title/abstract seen in the earlier helper's log, not opened by me].
- Gun-Murty-Rath 2012 (Acta Arith. 155) and Murty-Rath 2014 (chapter in Transcendental Numbers): number-field generalizations
  [SNIPPET, records only].

### 2.3 Which q are proved today (table)

| q | status | source |
|---|---|---|
| even | true (no convergence for f(q)=0) | Chatterjee-Murty, Bharadwaj [READ] |
| prime | true | BBW 1973 [READ via Okada] |
| 2*phi(q)+1 > q (prime powers, p*r, many others) | true | Okada 1982 Cor. 16 [READ] |
| 3 mod 4 | true | Murty-Saradha 2010 [READ via CM, Bharadwaj] |
| least prime factor >= d(q) | true | CM 2015 Cor. 3.3 [READ] |
| 82 percent (lower density) of 1 mod 4 | true | CM 2015 Thm 1.1 [READ] |
| p*N, N = 3 mod 4 squarefree, p large, p = 3 mod 4 | true | Bharadwaj Cor. 1 [READ] |
| general 1 mod 4 (e.g. smallest not covered by the printed criteria: 105, 165, 525, 585, 825, 945) | OPEN in print | CM 2015, Pathak 2019, Bharadwaj [READ] |
| completely multiplicative f, any q | true | Tijdeman 2002 [READ via CM] |
| finite verification range (e.g. "all q below 10^k") | not found | searched; not stated in any paper read |

[COMPUTED, conditional on Okada's theorem which is a published theorem]: from the parity scan below, Erdos also holds for all
composite non-prime-power q = 1 mod 4 below 480 other than 225 and 441, and those two are covered by Okada's 2*phi(q)+1 > q
(2*phi(225)+1 = 241 > 225; 2*phi(441)+1 = 505 > 441).

## 3. The obstruction for q = 1 mod 4, and the Q06 claim

### 3.1 What the authors say
- The system is linear with rational coefficients; the +-1 condition is not linear; proofs use one equation at a time
  (absolute values, or an arithmetic argument on one unit's coefficient) [READ, Bharadwaj sec. 1.2].
- Chatterjee-Murty: positive density of q (those with many small prime factors) satisfy sum 1/phi(d) >= 1, so their divisor-sum
  inequality cannot show 100 percent; q = 1 mod 4 needs "a novel idea" [READ].
- Bharadwaj warns that for odd N there may be Erdos-type functions with L(1,f) in the Q-span of log p (units contribute nothing),
  and asks whether an odd N with a +-1 divisor-sign pattern with sum a_d phi(d) = 0 exists [READ].

### 3.2 The parity argument, stated exactly (my derivation [INFERRED], confirmed [COMPUTED])
Let V be the Q-row space of Okada's system on the unknowns f(1..q-1) (f(q)=0) and V' = V intersected with Z_(2)^(q-1)
(rational vectors with odd denominators... more precisely 2-adically integral). If x in {+-1}^(q-1) is in the kernel, then for every c in V'
the rational number c.x is 0, but c.x = sum c_r x_r = sum c_r (mod 2) because every x_r is an odd integer and c_r are 2-adic integers.
So if some c in V' has 2-adic-unit coordinate sum, no +-1 solution exists. A 2-adically saturated basis of V' is obtained by
Gaussian elimination with pivots of minimal 2-adic valuation; the test is "some basis row has odd coordinate sum".
This is an elementary rigorous certificate for each q once Okada's theorem is granted. It is the "prime 2 of Z[zeta_q]" version of the
BBW/Okada idea (f = +1 mod 2). Intuition for why non-squares die [INFERRED, not a proof]: in Okada's form, f(a) = -sum_(r in L)
f(r) A(r,a), and A(r,a) has 2-adically large negative valuation (factor (1 - p^(-phi(q)))^(-1), denominator p^phi(q) - 1, divisible by a
high power of 2) exactly for r with P(r) non-empty; forcing |f(a)| = 1 then needs congruences whose consistency is a parity count of
residues, and for squares symmetries make those counts even.

### 3.3 My checks of the claim [COMPUTED]
(1) Independent encoding: I wrote the Chatterjee-Murty form from the formulas (own code: geometric series for the weights
    w(s) = sum of 1/m over m in M(q), m = s mod q) AND Okada's 1982 form from Theorem 10 (own code, sums over S(r)); row spaces agree for
    q = 9, 15, 21, 45, 75, 105 (the first set also includes the row sum f = 0, implied by the second). Ranks: 7, 10, 14, 26, 42, 51.
(2) Necessity direction (the one the exclusion needs: L(1,f)=0 implies the equations): the family of coefficient functions of
    prod(1 - p^(1-s)) zeta(s), for (q; primes) = (9; 3,3), (15; 3,5), (21; 3,7), (45; 3,3,5), (45; 3,5), all genuinely vanishing at s = 1,
    satisfies every equation of my encoding exactly (including the lambda(r,p) weights and f(q) free).
(3) Parity routine tested on 300 random solvable systems (known +-1 solution, random 2-adic denominators): zero false kills; a system
    forcing sum of three odd numbers to vanish is killed as it should be.
(4) Independent brute force that does not use the parity argument: in Okada's reduced form the unknowns are the +-1 values on L
    (|L| = q - phi(q) - 1), t equations only involve L, then f(a) is determined; enumerate all 2^|L| sign vectors. q = 15, 21, 33, 35,
    39, 45, 51, 55, 65, 91: no Erdos function; the best deviation of some |f(a)| from 1 among vectors satisfying the t equations
    was at least 0.52 (so not a numerical near miss).
(5) Scan with the parity test (own code, exact Fractions): composite non-prime-power q = 1 mod 4, 9 <= q < 480: survivors only 225 and
    441. q = 3 mod 4, 9 <= q < 200 (prime powers excluded): no survivors. At q = 105 two odd-sum basis vectors (same count as Q06).
    Speed: about 12 s for ten q near 150-225, minutes for q near 450, scaling like q^3 with big rationals.
Caveat that remains: everything rests on Okada's theorem (published, 1982, refereed, with a corrigendum-style acknowledgement of
referee-found errors in the manuscript [READ, acknowledgement]; re-proved by Chatterjee-Murty 2014 [READ via earlier helper]) and
on the irreducibility hypothesis (B), automatic for rational f.

### 3.4 Is it already in print?
Not found. Searched: Crossref (about 20 queries on Erdos/periodic/Okada/vanishing/Livingston/Chowla titles), arXiv API
(mostly rate-limited), Semantic Scholar citation lists for the six main arXiv papers (the cited-by lists show no paper with a title
about parity or 2-adic methods for Erdos), full text of Chatterjee-Murty 2015, Bharadwaj, Pathak 2018/2019, Okada 1982. Not read:
Murty-Saradha 2010 (the q = 3 mod 4 paper), Murty-Pathak 2022 (Okada space), Bharadwaj-Murty-Pathak 2025, Saradha 2006/2008 notes,
Tijdeman 2008, Okada 1986. The first three are the likeliest places for a related argument: a parity obstruction for q = 2 mod 4
is there (Murty-Pathak Thm 4.8, via Bharadwaj), and Murty-Saradha's coefficient argument for q = 3 mod 4 may well be a 2-adic
argument too. "Surprising if not in print" is right: I rate "some form already in print" at roughly 40 percent [INFERRED], and the
authors of the three later papers still call q = 1 mod 4 open, which argues against a full parity theorem in print.

## 4. Verdict on the earlier claim, and what a careful check must do

Verdict [INFERRED from sections 2 and 3]: the claim as a statement about q < 480 is TRUE (reproduced, validated, cross-checked by brute
force). As a theorem "for every non-square q = 1 mod 4" it is UNPROVED. The pattern (survivors exactly the squares 225, 441) is
suggestive but a pattern in 30-odd cases is not a proof. If it extends it would settle all non-square q = 1 mod 4 and reduce the
conjecture to squares; squares with at least three odd prime factors (smallest 11025 = 105^2, where Okada's bound fails:
2*phi(11025)+1 = 10081 < 11025) would be the real remaining case.
A careful check/proof would have to:
 (a) Prove, for general q, that the 2-adic saturation of Okada's lattice contains an odd-sum vector iff q is not a square. Work in
     Okada's reduced form (unknowns on L, then f(a) = -sum f(r) A(r,a)); identify which denominators of A(r,a) are 2-adically large
     (those with P(r) non-empty) and show the resulting congruence has an odd count for non-squares. Natural first targets: q = p^a r^b
     and squarefree q (where Okada/CM already give many cases, so the new content is non-covered q like 105, 165, 585).
 (b) Check the unproven link "Okada's criterion gives ALL vanishing f" at least in the necessary direction (done computationally above
     for the encoding; the original theorem is the actual proof).
 (c) Read the three unread papers above to settle priority; contact-free check: look for "2-adic", "parity", "mod 2" in Murty-Saradha 2010.
 (d) For squares: run the same test on larger squares with more than two primes (q = 11025 has 11024 unknowns; needs a modular
     rank/2-adic implementation; exact Fractions are too slow), and see whether the survivors continue to be exactly squares.
 (e) Formalize: the certificate for each q is a short integer vector (coordinate sum odd) plus the exact rational equations; Lean can
     check a single q by `norm_num`-style rational arithmetic; the general statement needs (a) first.

## 5. Related statements and status

- Livingston's conjecture (Livingston, Canad. Math. Bull. 8 (1965) 413-432; stated in Pathak 2018, arXiv 1808.09944 [READ]): for
  q >= 3 the numbers log(2 sin(pi a/q)), 1 <= a < q/2 (q odd), together with log 2 when q is even, are linearly independent over the
  field of algebraic numbers. Livingston expected a proof of this to settle Erdos [READ, Pathak]. Status: FALSE for composite q >= 4
  (Pathak 2018, Theorem 1.1: for composite q >= 6 the logs are even Q-dependent), TRUE for odd prime q (Pathak, Theorem 1.2; also
  from BBW). Chatterjee-Dhillon 2019 (Canad. Math. Bull., doi 10.4153/s0008439519000468) give a new proof, add a coprimality
  condition under which the conjecture has necessary and sufficient conditions, and identify a maximal independent subset
  [SNIPPET, Crossref abstract]. Consequence [INFERRED]: Livingston's route to Erdos cannot work as stated for composite q, which
  is why the later work uses Okada's system.
- Chowla's original problem (f rational, q prime) is solved: BBW; for general q and algebraic f the Okada criterion decides.
- 2020-2026 progress that I found: Bharadwaj 2022 (arXiv; published 2025), Murty-Pathak 2022 (Okada space), Chatterjee-Dhillon 2019,
  Pathak 2018/2019, Banerjee-Khoai-Kundu 2026 (Complex Var. Elliptic Equ., "Uniqueness results of Dirichlet series with periodic
  coefficients"; a different question; SNIPPET only). No new covered classes for the Erdos conjecture itself after Bharadwaj 2022 in
  what I found.
- Problem lists: not in erdosproblems.com (problems.yaml from github, 1221 entries, grep for periodic, Livingston, Okada, Chowla,
  Baker, Birch, Wirsing: only the cosine problem entry). Not in Google's Formal Conjectures path list (checked by the earlier helper).
  Source for the conjecture itself: Erdos's letter to Livingston (Livingston 1965, sec. 5, via Okada's p. 430 citation) [READ].

## 6. Open (precise)

O1. Erdos for q = 1 mod 4, q not covered by 2*phi(q)+1 > q, least prime factor >= d(q), Bharadwaj's p*N, or the 82 percent density
    (stated open by Chatterjee-Murty 2015, Pathak 2019, Bharadwaj 2022).
O2. Whether the parity theorem (all non-square q = 1 mod 4) is true for every q (my finding; unproved).
O3. Squares of odd squarefree numbers with at least 3 primes (smallest 11025).
O4. Bharadwaj's divisor-sign question (odd N with a_d = +-1, a_1 = 0, sum a_d phi(d) = 0, giving a pure log-p value): stated open
    as a question in the paper; my enumeration found none for odd N < 3500 with at most 25 divisors and for N = 11025 [COMPUTED].
    Not stated as proved-impossible anywhere.

## 7. Leads for this project (ranked)

1. Prove the parity theorem for non-square q (days to weeks). Statement: for odd q = 1 mod 4 not a perfect square, no +-1 function with
   f(q) = 0 has L(1,f) = 0. Toolkit fit: exact lattice/2-adic reasoning on Okada's explicit system; certificates formalizable;
   Baker is not even needed beyond Okada's theorem (which would be an imported hypothesis, or proved from the project's Baker import
   following BBW, 2-4 weeks). Noticeable because it settles an unsolved conjecture for infinitely many q if it works; first test: write
   the general-q argument for squarefree q with 3 primes (the smallest uncovered family) and check against the table.
2. Computation range extension plus modular code (days): run the parity test for all odd composite q up to about 3000 using exact
   arithmetic mod several primes plus 2-adic pivoting (my Fraction code does q = 450 in minutes), and record survivors, to see if survivors
   are always squares. Gives evidence and the exact first uncovered square.
3. Squares (weeks, maybe out of reach): 105^2 = 11025 by the same lattice method plus a mod-3, mod-5 variant of the parity test (f = +-1
   mod l is not linear but f = 1 mod 2 is; for odd l a subset-sum analysis). Test bed: 225, 441, where truth is known.
4. Divisor-sign question (days): extend the gcd-type enumeration to odd N up to 10^5 with meet-in-the-middle; either finds a first
   Erdos-type counterexample (a pure-log value, which would be a major find) or a table. Cheap.
5. Machine-checked BBW/Okada from the project's imported Baker (2-4 weeks): the finite sets of equations then become Lean data and
   leads 1-2 get formal certificates. (Overlaps the earlier helper's lead L2.)

## 8. Overlap or conflict with section 1 of the rules
No overlap with the BBP/pi results. Shared tools: Baker's theorem (via Okada/BBW), Galois action on cyclotomic fields, logs of cyclotomic
units and primes independent over Q, primitive prime divisors/2-adic reasoning at the prime 2. No conflict found.

## 9. Sources
- Okada, Acta Arith. 40 (1982) 143-153: https://matwbn.icm.edu.pl/ksiazki/aa/aa40/aa4023.pdf (scanned; read as images)
- Chatterjee-Murty, arXiv:1501.04185; Pathak arXiv:1808.09944 and arXiv:1909.03972; Bharadwaj arXiv:2204.03674;
  Chatterjee-Murty arXiv:1405.6982, Chatterjee-Murty-Pathak arXiv:1809.01841 (downloaded, not re-read this session)
- Murty-Pathak, Okada space: doi 10.7169/facm/1952; Chatterjee-Dhillon: doi 10.4153/s0008439519000468; Murty-Saradha 2010:
  doi 10.1016/j.jnt.2010.07.004; Banerjee-Khoai-Kundu: doi 10.1080/17476933.2025.2612289
- https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml
- Page text contained no instructions directed at me; one OpenAlex response suggested requesting an API key by sending an e-mail
  address (ignored, not supplied).

## 10. Search log
WebSearch (3): W1 "Erdos conjecture periodic function f(n)=+-1 sum f(n)/n nonzero q = 1 mod 4 Okada criterion progress" (returned only
 Erdos discrepancy hits); W2 "Livingston conjecture periodic arithmetic function series f(n)/n Okada Acta Arith 1982" (gave Pathak
 1808.09944, Livingston PDF); W3 "arXiv 2023 2024 2025 Erdos conjecture Dirichlet series periodic coefficients +-1 non-vanishing" (nothing new).
Endpoint queries (51; refused or rate-limited ones marked):
 1 arXiv API Erdos periodic Dirichlet (429)   2 Crossref Erdos periodic Dirichlet nonvanishing   3 arXiv abs 2204.03674
 4 arXiv PDF 1501.04185 via WebFetch (binary)   5 OpenAlex cites (empty)   6 OpenAlex search (429)   7 Crossref Bharadwaj Murty Pathak
 8 Semantic Scholar search (429)   9-12 curl arXiv PDFs 1501.04185, 1405.6982, 1809.01841, 2204.03674   13-14 curl 1808.09944, 1909.03972
 15-24 Crossref x10 (Okada 1982 ok; Murty-Saradha ok; Okada 1986, Tijdeman, Pilehrood, Tengely, Saradha-Tijdeman, Erdos functions,
 Bharadwaj-Pathak, cyclotomic units returned nothing/rate-limited)   25-26 matwbn Okada-neighbour PDFs (aa4024 wrong paper), doi.org Okada
 27 impan.pl Okada page   28-30 matwbn aa4023 (Okada, ok), aa4025, aa4022   31 arXiv API Erdos functions/Okada criterion (empty)
 32-37 Semantic Scholar citation lists of the six arXiv papers (one 429)   38-40 Semantic Scholar title searches (429 x3)
 41-44 Crossref: Uniqueness results Dirichlet periodic; Livingston/Chatterjee-Dhillon; non-vanishing Erdos; Pilehrood
 45 Crossref DOI record Chatterjee-Dhillon (abstract)   46 teorth problems.yaml   47 GitHub code search (401)   48 GitHub repos
 49 Crossref Murty-Pathak Okada space   50-51 arXiv API Okada space (empty, x2)
 Totals: WebSearch calls = 3. Endpoint queries = 51 (about 11 refused/rate-limited or empty).
 Pages read in full or in part: Okada 1982 (5 of 6 page images), CM 2015, Bharadwaj 2022, Pathak 2018, Pathak 2019 intro.
 Own code in the session scratchpad (not in the repository): okada.py (both systems, parity test), ok82.py, bf.py (brute force),
 syn.py (synthetic validation), scan.py, gcdtype.py/run.py (divisor-sign search).
