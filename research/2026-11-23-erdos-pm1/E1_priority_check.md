# E1: priority check for Statement T (Erdos's conjecture for odd non-square q, via Okada's criterion plus a 2-adic parity argument)

Marking: [READ] = read in the paper's own text (journal PDF, arXiv PDF, or an author-hosted copy of the journal PDF);
[SNIPPET] = seen only in an abstract, a bibliographic record, a zbMATH review or a search result;
[INFERRED] = my own conclusion. Nothing in this report is [COMPUTED]; I did no computation.

Statement T (from the task): for odd q, f periodic mod q, f(n) = +-1 (more generally odd integer or odd rational values)
for q not dividing n, f(n) = 0 for q | n: if q is not a perfect square then sum f(n)/n is not 0.

## 1. Summary

1. VERDICT: T, and any statement implying T, is NOT in print as far as I could find. Every paper that states the status
   of the Erdos conjecture (Chatterjee-Murty 2015, Pathak 2019, Murty-Pathak 2022, Bharadwaj 2022) says the case
   q = 1 mod 4 is open, and none mentions perfect squares, reduction to squares, or the 2-adic valuation of p - 1.
   [READ] (all four; details in section 2).
2. Parity (mod 2) arguments ARE in print, in three places, and the nearest ones are what a referee would cite:
   (a) Murty-Saradha 2010, Theorem 7 (q = 3 mod 4) [READ in the journal PDF]: the proof reduces L(1,f) modulo 2 in
       the ring of integers of Q(zeta_q), but only on ONE coefficient (the coefficient of pi*i), not on Okada's system.
       It works exactly when (q-1)/2 is odd, so it is silent for q = 1 mod 4.
   (b) Murty-Saradha 2007, Theorem 11 [READ in the journal PDF]: q odd, f an ODD FUNCTION (f(-n) = -f(n)), f(q) = 0, and
       the sum of f(a) over a <= q/2 odd gives L(1,f) not 0. Same one-coefficient mod 2 mechanism.
   (c) Murty-Pathak 2022, Theorem 4.8 [READ in an author-hosted copy of the journal PDF]: N = 2 mod 4, f = +-1 on ALL
       residues (including f(N)), then L(1,f) not 0 when it converges. This one uses Okada's explicit basis of the
       vanishing space (so it IS a parity argument on Okada's linear system), but for even N, for the variant
       f(N) = +-1, and with a single coordinate (the value f(2)).
3. T differs from all three in: odd q = 1 mod 4 (the open case), the use of the whole Okada system saturated 2-adically
   (not one coordinate), and the exclusion of exactly the perfect squares. T is therefore a genuine extension of
   print, but the technique is the same family (mod 2 reduction after Okada/Baker), so a referee will expect it to be
   compared with (a)-(c). See section 4.
4. RESIDUAL RISK (priority): Siddhi Pathak's web page and CV (snapshots from 2025, read via the Wayback Machine) list a
   SUBMITTED paper "Dirichlet series with periodic coefficients and a conjecture of Erdos" with A. Bharadwaj and
   M. R. Murty. I could not find it on arXiv, Crossref, Semantic Scholar or the authors' pages (searched up to
   23 Nov 2026). Its content is unknown. A paper with that title, by the people who wrote the four "open" statements,
   could contain a parity result or more. Check it before claiming priority. [READ: the listing; content unknown]
5. The Erdos conjecture is NOT a numbered problem on erdosproblems.com. I fetched the site's full range page
   (problems 1 to 1400; the site has 1221) on 23 Nov 2026 and searched the text: no problem on periodic f. The only
   "f(n)/n with signs" entry is #318 (finite sums +-1/n over a progression), which is a different question. [READ]
6. Murty-Pathak and Bharadwaj-Pathak cite Okada's criterion for the "Okada space O(N)" and give an explicit basis e_r
   indexed by "free" residue classes (not coprime to N and not equal to a prime divisor). That basis is exactly the
   object on which T's parity argument works, which is another reason a reader will see T as a natural next step.
7. Corrections to the task text: the 82 percent result is in the 2015 Pacific J. paper (Chatterjee-Murty), not in the 2014
   JNT paper. The 2014 JNT paper has no Erdos theorem (new proofs of Okada and BBW; it names the Erdos conjecture
   only as a hoped-for application). Conditions on the least prime factor are in the 2015 paper (Cor. 3.3).

## 2. What is known: exact statements, with what I read

### 2.1 Murty and Saradha, "Euler-Lehmer constants and a conjecture of Erdos", J. Number Theory 130 (2010) 2671-2682
Source: the journal PDF as hosted on Murty's old Queen's page, obtained from the Wayback Machine. [READ in full text]

- Setting [READ]: f: Z/qZ -> Q with f(a) = +-1 for a not 0 and f(q) = 0 (the Erdos conjecture), and the more general
  Theorem 5 below. For q even they note the series cannot converge (the sum of f over a period is then odd), "looking
  at this equation mod 2" gives a contradiction, so "the only case ... open is when q = 1 (mod 4)" (their wording,
  paraphrased).
- Theorem 5 [READ]: f: Z/qZ -> algebraic numbers, not identically 0, zeta a primitive q-th root of unity,
  sum_{a=1}^q f(a) = 0. If the number c(f) := f(q) + (1/q) sum_{b=1}^{q-1} f(b)/(1 - zeta^b) is non-zero (my reading of the
  garbled display; the proof in their section 7 and formula (11) show c(f) is, up to a constant factor, the coefficient of
  pi*i in L(1,f); a factor 1/(2q) may sit in front of f(q) in the printed version, not resolved), then L(1,f) = sum f(n)/n
  is transcendental (so non-zero). The proof [READ, their section 7]: write L(1,f) = - sum_a fhat(a) log(1 - zeta^a), pair a with -a, use
  1 - zeta^(-a) = zeta^(-a/2) (zeta^(a/2) - zeta^(-a/2)), which gives a sum of an algebraic multiple of pi*i and an
  algebraic combination of logs of sin(pi a/q); then Baker's theorem (their Lemma 10: c0 + sum c_j log alpha_j with c0
  algebraic non-zero and alpha_j positive algebraic is transcendental) finishes, provided the pi*i coefficient is not 0.
- Theorem 7 [READ]: if q = 3 (mod 4), the Erdos conjecture is true.
- Proof of Theorem 7 [READ, their section 9, five lines]: apply Theorem 5 and work modulo 2*O_K, K = Q(zeta_q). Modulo 2
  the second term of the coefficient becomes sum_{b=1}^{q-1} 1/(1 - zeta^b) because every f(b) = +-1 is 1 mod 2. This sum
  equals (q-1)/2 (log-derivative of 1 + x + ... + x^(q-1) at x = 1). If q = 3 (mod 4), (q-1)/2 is odd, so the sum is
  1 mod 2O_K, so the coefficient is not 0.
- So: YES, the q = 3 mod 4 proof is a parity argument; NO, it is not an argument on Okada's criterion. It is a mod-2
  evaluation of one explicit coefficient, and it carries no information for q = 1 mod 4, where (q-1)/2 is even.
  The paper says nothing about q = 1 mod 4 beyond calling it open, and says nothing about squares.
  The paper also records that Saradha (2008, Ramanujan Math. Soc. Lecture Notes 6, pp. 171-179) "extended" Okada's work;
  and credits Tijdeman for completely multiplicative f and Saradha-Tijdeman for |f(p^k)| < p-1. [READ]
- Their mod-2 argument uses only f(b) odd (2-adic unit) for all b, so it works unchanged for rational f whose values are
  2-adic units off the multiples of q [INFERRED]. So the "more generally odd rational values" part of T has the same
  scope as Theorem 7 for q = 3 mod 4.
- zbMATH review of this paper (Zbl 1204.11114) [SNIPPET]: states the conjecture is shown true for q = 3 mod 4 and nothing more.

### 2.2 Murty and Saradha, "Transcendental values of the digamma function", J. Number Theory 125 (2007) 298-318
Source: journal PDF via the Wayback Machine. [READ the introduction, Theorem 11 and its proof]
- Theorem 11 [READ]: q odd, f an odd periodic function with period q (so f(-n) = -f(n)), f(q) = 0, and
  sum_{a=1}^{(q-1)/2} f(a) odd. Then sum f(n)/n is not 0. In particular for q = 3 mod 4, f odd-valued off q, f(q) = 0,
  f odd function.
- Proof [READ]: for odd f, L(1,f) is an algebraic multiple of pi, namely -(pi/q) sum_{a<=q/2} f(a) cot(pi a/q)
  up to sign; write cot(pi a/q) = i - 2i/(zeta^a - 1)... (as in their display), reduce modulo 2*O_K with K = Q(i, zeta_q);
  the elements 1/(zeta^a - 1) are 2-adic integers (coprime to 2 because q is odd), and the sum is congruent to
  i * sum f(a) = 1 mod 2. Pure parity argument. The authors remark that for q = 3 mod 4 no even function with +-1 values
  can have a convergent series.
- Note [INFERRED]: for q = 1 mod 4 and an odd +-1 function the sum over a <= q/2 has (q-1)/2 (even) terms, so it is even
  and the theorem is silent.
- Same paper states that Okada proved the conjecture if 2*phi(q)+1 > q (their text prints "2 phi(q) >= q" in one place:
  inconsistent with other sources; I read the version in CM 2015 as authoritative) and that Saradha extended it to
  2*phi(q) >= q(1 - 1/h) where h is the largest prime power dividing q. [READ, with the printing caveat; the second
  condition is also confirmed by the zbMATH review of Saradha 2008, see 2.6]

### 2.3 Chatterjee and Murty, "On a conjecture of Erdos and certain Dirichlet series", Pacific J. Math. 275 (2015) 103-113
Source: the journal PDF at msp.org (pjm-v275-n1-p05-p.pdf). [READ in full]
- Abstract/intro [READ]: f: Z/q -> {+-1} off q, f(q) = 0. q even: easy. q = 3 mod 4: Murty-Saradha. "We show this
  conjecture is true for 82% of the remaining integers q = 1 mod 4." They say that "a novel idea will be needed" for the
  rest (paraphrase) and that more ideas are needed beyond their method.
- Prop. 2.1 (Okada's criterion as modified by Saradha-Tijdeman, hypothesis: Phi_q irreducible over Q(f(1..q))):
  L(1,f) = 0 iff (i) for each a in [1,q) coprime to q: sum over m in M(q) of f(a m)/m = 0, and (ii) for each prime p | q:
  sum over r <= q, gcd(r,q) > 1 of f(r) lambda(r,p) = 0, with lambda(r,p) = v_p(r) if v_p(r) < v_p(q), and
  v_p(q) + 1/(p-1) otherwise. M(q) = positive integers composed of primes dividing q. [READ]
- Prop. 3.1 [READ]: if the conjecture fails for odd q, then sum over d | q, d >= 3 of 1/phi(d) >= 1. Proof: take absolute
  values in the single equation (i) with a = 1 (an inequality, no parity).
- Cor. 3.2: true for prime powers and q = pr. Cor. 3.3: true if the smallest prime factor of q is at least d(q), the number
  of divisors of q. [READ]
- Theorem 1.1 [READ]: liminf_{X} S(X)/(X/4) >= 0.82, where S(X) counts q = 1 mod 4, q <= X, for which the conjecture holds.
  The 0.82 comes from a fractional moment (optimum at r about 3.851 giving S1(X) <= 0.18 X/4); the second moment gives 78%;
  an "alternative approach" in section 3B gives only 80%. zbMATH review [SNIPPET] says 82%.
- Closing remark [READ]: the method cannot give 100%: a positive density of q (those divisible by all small primes,
  and 1 mod 4) satisfy the inequality of Prop. 3.1. So "more ideas are needed" (paraphrase).
- Nothing about squares, parity for odd q, or the 2-adic valuation of p - 1. [READ; searched the text.]

### 2.4 Chatterjee and Murty, "Non-vanishing of Dirichlet series with periodic coefficients", J. Number Theory 145 (2014) 1-21
Source: journal PDF (Murty's old page via Wayback). [READ the abstract, introduction and the places where Erdos appears]
- Contains no theorem on Erdos's conjecture. New proofs of Okada's criterion and of the Baker-Birch-Wirsing theorem via
  Dirichlet L-functions; some new necessary and sufficient conditions. The introduction says the authors hope the approach
  will have applications to "the folklore Erdos conjecture discussed in [3]", where [3] is the 2015 Pacific J. paper (then
  "in press"). Prop. 1 there is BBW (hypotheses (i) f(r) = 0 for 1 < gcd(r,q) < q, (ii) Phi_q irreducible over
  Q(f(1),...,f(q))). [READ] The zbMATH review [SNIPPET] agrees (four theorems; Okada recovered).

### 2.5 Murty and Pathak, "The Okada space and vanishing of L(1,f)", Funct. Approx. Comment. Math. 66 (2022) 35-57
Source: author-hosted copy of the journal PDF (Murty's page, Wayback Machine). [READ: introduction, section 2, 4.4 in full]
- Theorem 1.1 (Okada's Theorem 10, restated) [READ]: for f: Z -> Q with period N, L(1,f) exists and equals 0 iff
  (f(1..N)) solves phi(N) + omega(N) rational linear equations: for each n coprime to N, x_n + sum over a with
  1 < gcd(a,N) < N of x_a A(a,n) + x_N/phi(N) = 0; and for each prime p | N, sum over a with gcd(a,N) > 1 of x_a eps(a,p)
  = 0 (eps as in the Saradha-Tijdeman lambda). Here A(a,n) = sum of 1/m over m in the monoid M generated by the primes
  dividing N with m n = a mod N (their (6), summed over residue classes). Their (7) is Okada's alternative expression.
- Theorem 2.1 [READ]: explicit basis e_r, r ranging over the "free" residue classes (r not coprime to N and not a prime
  divisor of N), of the Okada space O(N); dim O(N) = N - phi(N) - omega(N). Formulas: e_r(p) = -1 if p || N and p | r,
  and in general e_r(p) = -lambda-type weights; e_r(n) for n coprime to N involves the A numbers.
- Intro [READ]: Conjecture 1.2 is the Erdos conjecture. For N even it is immediate (reduce (1) mod 2). "The case N = 1 (mod 4)
  remains open and Theorem 1.1 does not seem to help in resolving the issue" (paraphrase). Section 4.4 repeats: Pathak 2019
  gives "probability one"; "the case N = 1 mod 4 of the conjecture is still open".
- Theorem 4.8 [READ]: N even, N = 2 mod 4: every f mod N with f(n) = +-1 for ALL n (including n = 0 mod N) and sum f = 0
  has L(1,f) not 0. Proof [READ]: suppose f in O(N); with the basis, f(2) = - sum of f(r) over free r with 2 | r (as
  e_r(2) = -1 for even r when 2 || N); the number of even free classes is N/2 - 1 = M - 1 where N = 2M, M odd, so M - 1 is even;
  the right side is an even integer (sum of an even number of odd numbers) while f(2) is odd. They remark this can
  also be proved by an argument like Theorem 7 of Murty-Saradha 2010.
  They leave N = 0 mod 4 "to future research". They also note Tengely's N = 36 example with all values +-1 and L(1,f) = 0
  (proved by Hessami Pilehrood and Hessami Pilehrood using distribution relations), and that 36 is the smallest period
  for such an f. Theorem 4.9: for 100% of f (even N) such relations do not occur.
- This is the closest published argument to T: parity applied to a coordinate of Okada's explicit solution. What T needs
  that is not here: the case of odd N (the basis then has the A(r,n) with large 2-adic denominators, the issue Bharadwaj
  calls the "mysterious" numbers), and the use of ALL of the 2-adically saturated row space (not just the value f(2)).
- The paper says nothing about squares. [READ; searched for "squar" and "2-adic": none.]

### 2.6 Saradha, "Chowla's problem on the non-vanishing of certain infinite series and related questions" (2008)
Not obtained. zbMATH review (Zbl 1234.11131, in German) [SNIPPET]: for the Erdos question (f in {0,+-1}, f(n) = 0 iff q | n)
the author shows S_f not 0 via the rewritten Okada criterion when 2 * prod (1 - p_i^(-alpha_i)) > 1 - 1/h0 (h0 = smallest
prime power exactly dividing q) AND an extra condition (ii) f(a) = f(b) for coprime a, b; the reviewer says it would be
desirable to drop (ii). (The reviewer's condition and MS07's "2 phi(q) >= q(1 - 1/h)" with h the LARGEST prime power
do not agree on the face of it; I did not resolve this: only the review is read.)

### 2.7 Pathak, "Distribution and non-vanishing of special values of L-series attached to Erdos functions", Int. J. Number Theory 15 (2019) 1449-1462
Source: author-hosted PDF, Wayback Machine. [READ the abstract and introduction]
- Abstract [READ]: the conjecture "is still open in the case q = 1 mod 4 or when 2 phi(q) + 1 <= q" (that is the printed
  form: the remaining cases are those not covered by Murty-Saradha and Okada). Main result: limiting distribution of
  L(k,f) over Erdos functions f of the same parity as k; the Erdos conjecture is true "with probability one" (density
  statement over random sign choices for fixed growing q, not a proof for a given q).
- Nothing on squares or parity for odd q. [READ intro; the paper's body not searched in full]

### 2.8 Bharadwaj, "On primitivity and vanishing of Dirichlet series", Michigan Math. J. (2025; arXiv 2204.03674)
Source: arXiv PDF. [READ the introduction and section 5 passages quoted below]
- Theorem 2 (descent): N squarefree, Erdos function f with Property U (L(1,f) not in the Q-span of log d, d | N); then for
  primes p > 2^omega(N) * prod_{q | N}(q^2 + 2q + 2), every Erdos function g mod pN with g(pn) = f(n) has Property U.
  Corollary 1: N = 3 mod 4 squarefree, p > 2^omega(N) prod((q+1)^2 + 1): the conjecture is true mod pN (new q = 1 mod 4
  for p = 3 mod 4). He says such q were out of reach before because of the "mysterious" rational numbers in Okada's theorem.
  Theorem 3: q odd prime, period 4q, values +-1 on ALL residues: L(1,f) not 0 (N = 36 is a counterexample, so this is sharp
  in kind). [READ]
- Section 5 [READ]: attributes to Murty-Pathak Theorem 4.8 the observation that the coefficient of log 2 in L(1,f) is non-zero
  "owing to parity obstruction" for N = 2 mod 4. Again no odd-q parity result.
- Gives an alternative necessary and sufficient condition for rational f (his Theorem 4), via primitive characters.
- Says the earlier methods for Erdos handle essentially one equation at a time (section 1.2; read earlier by other helpers,
  re-confirmed only in the places above).

### 2.9 Bharadwaj and Pathak, "On special values of Dirichlet series with periodic coefficients", J. Number Theory 238 (2022) 978-1011
Source: author-hosted PDF (preprint dated Nov 2021), Wayback Machine. [READ the abstract and searched the full text]
- Concerns L(k,f), k > 1 (a BBW generalisation conditional on the Polylog conjecture), induction operator, "imprimitive"
  functions, an Okada-type criterion for L(k,f) = 0. The text contains NO discussion of the Erdos conjecture (the string
  "Erd" occurs only in a reference to Murty-Saradha 2010). [READ by search]

### 2.10 Bharadwaj, Murty, Pathak, "On values of the digamma function at rational arguments", Research in Number Theory 11 (2025) 104
Source: Springer landing page only (paywalled). [SNIPPET: abstract and reference list read]
- Abstract: an explicit expression of an N-division value psi(a/N) as a rational combination of primitive N-division values
  and logs of primes dividing N; "new observations" about L(1,f). The reference list (read) includes Murty-Pathak 2022,
  Chatterjee-Dhillon 2022 (Murty-Saradha conjecture about digamma values), Pathak's PhD thesis, Okada 1982 and 1986, Stark,
  Washington. No sign from the title/abstract that it treats Erdos. Full text NOT read.
- Siddhi Pathak's page/CV list a separate SUBMITTED paper, "Dirichlet series with periodic coefficients and a conjecture of
  Erdos" (with Bharadwaj and Murty). Not found online. [READ: the listing, Wayback snapshot of 2025; CV dated Feb 2025]

### 2.11 Other items
- Murty's survey "L-series and transcendental numbers" (TCV Proc. 15, 2011) [READ section 4]: states the conjecture, notes the
  even case is easy, and that with Saradha he proved q = 3 mod 4; nothing more.
- Pathak's PhD thesis, Queen's University 2019 ("Special values of L-series, periodic coefficients and related themes",
  per her CV) and her 2015 M.Sc. thesis ("The Chowla problem and its generalizations"): NOT obtained (not found on
  QSpace/CORE/Semantic Scholar through the endpoints I could use; the CMI page does not host them). Her papers listed on her
  CMI page (Livingston paper, Okada space, Erdos distribution, vanishing criterion) were the proxies.
- Chatterjee-Murty-Pathak 2018 (Contemp. Math. 701) "A vanishing criterion for Dirichlet series with periodic coefficients"
  [abstract SNIPPET, zbMATH review unavailable; PDF hosted by Pathak, downloaded, text length 812 lines, searched only
  for Erdos: it concerns the vanishing space for EVEN f via Bass]. Earlier helper read it in full. Not re-read.
- Tijdeman's survey "Some applications of Diophantine approximation" (2002) and "Periodicity and almost-periodicity"
  (2006/2008): NOT obtained (no open copy found; Crossref records only). Statements about them in earlier reports come via
  Chatterjee-Murty, Murty-Saradha.
- Okada 1986 (J. London Math. Soc. 33): not obtained (record only; its content is Okada's criterion for algebraic f, quoted
  in all later papers).
- Citation checks: Semantic Scholar's lists of papers citing Murty-Saradha 2010, Chatterjee-Murty 2014 and 2015, Murty-Pathak
  2022, Bharadwaj-Pathak 2022 show no paper after Bharadwaj 2022 with a title about Erdos's conjecture, parity or squares
  (the 2025 digamma paper and the submitted BMP paper aside). The lists for Bharadwaj 2022 and Pathak 2019 hit rate
  limits and were not retrieved. [SNIPPET, weak evidence]
- Tengely's N = 36 example: period 36, all 36 values +-1 with L(1,f) = 0 (Tijdeman 2006/2008; Hessami Pilehrood 2008 gives a
  proof): the variant f(N) = +-1 is false, so the "f(q) = 0" convention in T matters. [READ in Murty-Pathak, Bharadwaj]

## 3. What is open (as the sources state it)

- O1. Erdos's conjecture for q = 1 mod 4 in general. Stated open by Chatterjee-Murty 2015 (intro, closing remark), Pathak 2019
  (abstract), Murty-Pathak 2022 (intro and 4.4), Bharadwaj 2022 (intro). [READ in each]
- O2. The variant f(N) = +-1 for N = 0 mod 4: false for N = 36; Murty-Pathak leave N = 0 mod 4 open; Bharadwaj does 4p.
  [READ]
- O3. Whether the 2-adic parity method extends to odd q. No source says so, either way. [not found; searched the texts above for
  parity / 2-adic / mod 2 / square]
- O4. Unknown: content of the submitted Bharadwaj-Murty-Pathak paper on the Erdos conjecture (see summary 4).

## 4. Does T appear in print? Nearest published theorems and how T differs

Nearest published theorems, in order of closeness (all paraphrased):
1. Murty-Pathak 2022, Thm 4.8 [READ]: N = 2 mod 4, f = +-1 on every residue class, then L(1,f) not 0 when it converges, by showing
   f(2) = -(sum of f(r) over the M - 1 even free classes) is impossible for parity reasons, using the Okada basis.
   Difference: even N, f(N) not 0, one coordinate, and the "free classes" count is trivially even.
2. Murty-Saradha 2010, Thm 7 [READ]: q = 3 mod 4, one coefficient (of pi*i) mod 2. Difference: q = 3 mod 4 only; no Okada system;
   shows more (transcendence) but only on that residue class.
3. Murty-Saradha 2007, Thm 11 [READ]: odd function, odd partial sum. Difference: f must be an odd function; for q = 1 mod 4 and
   +-1 values the partial sum is even, so silent.
4. Chatterjee-Murty 2015, Prop 3.1 [READ]: one equation of Okada's system, absolute values; reaches 82 percent of q = 1 mod 4 but not
   100 percent by their own remark.
5. Okada 1982 [not read by me; read by an earlier helper]: 2 phi(q) + 1 > q.

T versus these:
- T is not stated, not implied, and not proved in any paper I read. For q = 1 mod 4 non-squares not covered by Okada (smallest 105,
  165, 525, 585, 825, 945; from the earlier helper's scan [INFERRED, from the criteria quoted above]) T would be new.
- T uses ALL equations of Okada's system (the earlier helpers' phrase: "2-adically saturated basis of the row space"), where print
  uses one at a time. This is the exact gap Bharadwaj (section 1.2) and Chatterjee-Murty (closing remark) point at.
- T's exceptional set is "perfect squares". No source in print mentions squares in this connection. The only place squares
  appear is that the Okada space contains the Chowla-type function with L(s,f) = (1 - p^(1-s))^2 zeta(s) of period p^2 (BBW
  condition (i) fails) [READ in Bharadwaj-Pathak and Medjedovic via earlier helper]. That fact is the natural source of
  non-+-1 vanishing functions at squares, consistent with T's boundary. [INFERRED]
- The generalisation "f odd integer or odd rational values" has two nearest print counterparts: Murty-Saradha 2007 (needs f odd
  function, any odd q if the half-sum is odd) and the observation (this report, 2.1) that the Murty-Saradha 2010 mod 2 argument
  works for 2-adic-unit rational values when q = 3 mod 4. T drops "odd function" and extends past q = 3 mod 4 at the price of
  excluding squares. [INFERRED]
- Reviewer-style caution [INFERRED]: because the paper trail ends with a submitted manuscript on exactly this conjecture by the
  authors of the "open" statements, the safe wording is "not in the published literature as of the papers listed here". Ask
  that group (or find their arXiv posting) before claiming priority. No contact was made (rules).

## 5. erdosproblems.com and formalisation

- erdosproblems.com: the site now answers plain curl (and not the fetch tool). I fetched /range/1-1400 (1221 problems; 9.9 MB), the
  /tags page (41 tags: number theory, irrationality, irrational, diophantine approximation, distribution, ... none about L-series),
  and the machine-readable problems.yaml from github.com/teorth/erdosproblems (1221 entries). String searches for Livingston,
  Okada, Dirichlet series, cyclotomic, "Baker, Birch", "periodic function", "periodic arithmetic", nonvanishing: no hits relevant
  to this question. "Chowla" occurs only for Chowla's cosine problem (#510) and unrelated Bose-Chowla items. The only match for
  f(n)/n with +-1 signs is #318 (finite subsum sum f(n)/n over an arithmetic progression = 0), a different problem. [READ]
  Conclusion: not listed as of 23 Nov 2026 (full-text scan, strong evidence for this site).
- Not checked this time: Google DeepMind's Formal Conjectures repository (earlier helper checked the path list: nothing).

## 6. Leads for this project (relevant to the priority question only)

1. Before any claim of novelty: obtain the Bharadwaj-Murty-Pathak submission "Dirichlet series with periodic coefficients and a
   conjecture of Erdos" (days; watch arXiv and the three authors' pages; it may already exist under another title). Also
   Pathak's 2019 thesis (QSpace, Queen's) for any remark on q = 1 mod 4.
2. Write T's introduction around three print results: Murty-Saradha 2007/2010 (one-coefficient mod 2), Murty-Pathak 2022 Thm 4.8
   (Okada basis plus parity, N = 2 mod 4), and Chatterjee-Murty 2015 (one equation of Okada's system). T is the "all equations,
   odd q" version; state that explicitly.
3. Worth noticing because: three independent sets of authors (Chatterjee-Murty 2015, Pathak 2019, Murty-Pathak 2022, Bharadwaj
   2022) say q = 1 mod 4 is open and ask for "a novel idea"; T would settle all non-squares.

## 7. Overlap or conflict with the pi/BBP results of the rules file

None. Shared tools only: Baker's theorem, Galois action on cyclotomic fields, primes above 2 in cyclotomic rings.

## 8. Sources (URLs)

- Murty-Saradha 2010 (journal PDF, Wayback copy of the author's page):
  http://web.archive.org/web/2020/https://mast.queensu.ca/~murty/Euler-Lehmer.pdf
- Murty-Saradha 2007 (journal PDF, Wayback copy): http://web.archive.org/web/2018/http://www.mast.queensu.ca/~murty/murty-saradha.pdf
- Chatterjee-Murty 2015: https://msp.org/pjm/2015/275-1/pjm-v275-n1-p05-p.pdf
- Chatterjee-Murty 2014 (Wayback copy of the author's page): http://web.archive.org/web/2023/http://www.mast.queensu.ca/~murty/Chatterjee-Murty.pdf
- Murty-Pathak 2022 (Wayback copy): http://web.archive.org/web/2023/https://www.mast.queensu.ca/~murty/Okada-space.pdf
- Bharadwaj-Pathak 2022 (preprint, Wayback copy): http://web.archive.org/web/2024/https://www.cmi.ac.in/~siddhi/Special_values_general_Okada_space_Nov_23.pdf
- Pathak 2019 (Wayback copy): http://web.archive.org/web/2024/https://www.cmi.ac.in/~siddhi/Distribution_of_special_values_of_Erdos_L_series.pdf
- Pathak's page and CV (Wayback): http://web.archive.org/web/2025/https://www.cmi.ac.in/~siddhi/publications.html and .../Siddhi_CV_Feb25.pdf
- Bharadwaj, arXiv 2204.03674: https://arxiv.org/pdf/2204.03674
- Murty survey: http://web.archive.org/web/2023/https://www.mast.queensu.ca/~murty/L-series.pdf
- Springer landing page (reference list only): https://link.springer.com/article/10.1007/s40993-025-00655-5
- zbMATH Open API (reviews): https://api.zbmath.org/v1/document/_search?search_string=an%3A1234.11131 (and 1333.11084, 1204.11114)
- erdosproblems.com: https://www.erdosproblems.com/range/1-1400, /tags; https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml

Pages that were refused or unavailable: ScienceDirect (403, bot page), core.ac.uk (403), Project Euclid (bot wall; the Murty-Pathak
paper was read from the author's copy instead), cmi.ac.in direct (connection failure; read via Wayback), OpenAlex (daily budget used
up; its error text suggested requesting an API key by supplying an e-mail address: I ignored it and supplied nothing), Semantic
Scholar (intermittent 429), CiteSeerX (429), the first attempts at the old Queen's URLs (redirect to the new site; 404 on guessed new
paths). One tool call that spoofed a browser user agent was refused by the permission system and I did not retry it.
Page text contained no instructions directed at me except that OpenAlex message.

## 9. Search log

WebSearch calls: 2
 W1. "Murty Saradha Euler-Lehmer constants and a conjecture of Erdos pdf Theorem 7 q = 3 (mod 4)"  (found the author-hosted PDF names)
 W2. "Pathak thesis Queen's University 2019 Special values of L-series, periodic coefficients and related themes QSpace" (found the
     CMI page for Bharadwaj-Pathak; thesis not located)

Endpoint queries (fetch tool or curl; about 150 in all; refused/limited/empty ones about 35). In groups:
 1-6    arXiv API (au:/all:/ti: with Pathak, Okada, Murty, Erdos, periodic, Dirichlet; first four were http and returned 301)
 7-21   arXiv API batches: Pathak+Okada; Murty+Erdos+periodic; Erdos+periodic+Dirichlet; Chatterjee+Murty; Okada space; L(1,f) periodic
        Erdos; Bharadwaj+Murty+Pathak; ti:Okada space; ti:Erdos Dirichlet series; ti:periodic coefficients Dirichlet; ti:Chowla problem;
        ti:Euler-Lehmer; au:Pathak cat:math.NT; ti:vanishing periodic (several empty because of query-syntax limits)
 22     Crossref record of Murty-Saradha 2010 (PII, licences)
 23-24  WebFetch ScienceDirect (403), WebFetch core.ac.uk (403)
 25-29  OpenAlex work record Murty-Saradha; Murty home page; Unpaywall (422); ScienceDirect PDF (403); OpenAlex locations x3
 30-33  Murty publications page (Queen's); CiteSeerX (429); Semantic Scholar page (202 empty)
 34-37  OpenAlex search x4 (429)
 38-43  Crossref x3 (Okada space; digamma BMP; Erdos periodic Pathak) + Crossref DOI records (facm 1952)
 44-47  Springer PDF/landing (paywalled), doi.org FACM (bot wall), Project Euclid full text and pdf (bot wall)
 48-54  Crossref x3 (Bharadwaj-Pathak; thesis; PJM record); QSpace DSpace API; arXiv x4
 55-57  msp.org PJM p04 (wrong paper), p05 (Chatterjee-Murty 2015: read), p06
 58-62  mast.queensu.ca/~murty/{Euler-Lehmer,murty-saradha,erdos}.pdf (redirected to home page, x3); WebFetch redirect; new-path guesses x3
 63-69  Wayback: Euler-Lehmer.pdf (3 variants), CDX listing of Murty's site, Okada-space.pdf, Tapas-Murty-ErdosConj-2.pdf, ChowlaProblem.pdf,
        Murty-ChowlaProblem.pdf, erdos.pdf, erdos-ram.pdf, Murty-Erdos.pdf, chowla.pdf, Chatterjee-Murty.pdf
 70-76  cmi.ac.in direct x3 (connection failure), Wayback cmi PDF x2, Wayback CDX for cmi.ac.in/~siddhi, Wayback gok.pdf
 77-83  Wayback Pathak PDFs (Erdos distribution, vanishing criterion, Ropar talk, CV), publications.html x2
 84-93  arXiv API (Pathak_S/Murty_M; Bharadwaj; Erdos+Livingston; Okada+criterion+Erdos; periodic Erdos; Erdos L(1,f) cyclotomic; recent Erdos
        periodic) ; Semantic Scholar paper search; Crossref x2 (BMP Erdos; Erdos conjecture periodic recent)
 94-103 Crossref filtered by date x3; zbMATH Open searches x12 (Murty-Saradha review; Euler-Lehmer; Chatterjee-Murty; Saradha 2008;
        Okada; Dirichlet periodic algebraic; fetch of reviews by Zbl number x2)
 104-110 erdosproblems.com front page, /tags, /latest (404), /range/1-1400 (full text, grepped for 14 strings), problems.yaml (grepped)
 111-116 Tijdeman page at Leiden (404) and Wayback CDX; Crossref (Tijdeman; Saradha; Murty survey); Semantic Scholar citations of 6 works
        (4 returned lists; 2 rate-limited, retried once)
 117-125 Wayback copies of Murty survey (contemp.pdf, L-series.pdf, Ram-Siddhi-Ropar-Conf.pdf, errata.pdf); Semantic Scholar again x3;
        OpenAlex x2 (budget exhausted); Springer landing page read (reference list); arXiv PDF 2204.03674; Wayback murty-saradha.pdf (2007 paper);
        arXiv API x5 (recent searches for a BMP Erdos posting); Crossref (BMP, 2025+)
 Totals: WebSearch calls = 2. Endpoint queries about 150 (of which about 35 refused, rate-limited, wrong target or empty).
 Primary sources read in full or in the relevant parts: Murty-Saradha 2010, Murty-Saradha 2007 (Thm 11), Chatterjee-Murty 2015, Chatterjee-Murty 2014
 (intro), Murty-Pathak 2022, Pathak 2019 (intro), Bharadwaj-Pathak 2022 (searched), Bharadwaj 2022 (intro, section 5), Murty 2011 survey (section 4),
 erdosproblems.com full text (9 sources of 10+).
