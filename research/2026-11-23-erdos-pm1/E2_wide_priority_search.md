# E2: wide search for prior statements of Statement T (Erdos's +-1 conjecture, non-square q)

Date of search: 2026-11-23. Helper thread E2 (complementary to the helper reading Murty-Saradha 2010,
Chatterjee-Murty 2014/2015, Murty-Pathak, Pathak's thesis).

Statement T (as given): Erdos's conjecture (f periodic mod q, f(n) = +-1 for q not dividing n,
f(q) = 0 implies sum f(n)/n != 0) holds for every q that is not a perfect square, via Okada's
criterion and a 2-adic congruence argument.

Marking: [READ] = read in the source's own text (PDF text extracted locally, or page); [SNIPPET] =
only an abstract, API record, review, or search snippet; [INFERRED] = my conclusion.

## 1. Summary

1. No source I found states or implies Statement T. [INFERRED] from reading the 2022 statement of
   open cases in Bharadwaj (below), plus no hit in 60+ queries.
2. Latest accessible statements of the status (all say open for q = 1 mod 4 when 2^omega(q)+1 <= q):
   Pathak 2019 abstract [READ]; Bharadwaj arXiv 2022 / Michigan Math. J. 2025 [READ arXiv v1; journal
   only SNIPPET]. Zbmath review of Chatterjee-Murty 2015 says "till date it is open" [SNIPPET].
3. Best published coverage of q (for +-1, f(q)=0): even q (trivial, series does not converge);
   odd prime q (Baker-Birch-Wirsing 1973); q with 2^omega(q) + 1 > q, i.e. prime powers and
   products of two distinct odd primes (Okada 1982); q = 3 mod 4 (Murty-Saradha 2010, Thm 7 of
   their paper); at least 82 percent of q = 1 mod 4 (Chatterjee-Murty 2015); "probability one"
   (Pathak 2019); new squarefree families q = pN with N = 3 mod 4 and p large and = 3 mod 4
   (Bharadwaj, Cor. 1). All [READ] in Chatterjee-Murty, Pathak 2019, Bharadwaj.
4. Earliest source of the conjecture: Livingston 1965, Section 5, quoting a written communication
   from Erdos. [READ] (exact wording in section 2.1).
5. Chowla's 1949 problem (any nonzero periodic f) is a different, FALSE-in-general statement;
   Livingston showed it false for every period p > 2 and notes Chowla wrongly credited Erdos.
   [READ, Livingston section 1.]
6. A square-related hint exists only in a variant: Bharadwaj states a counterexample (due to
   Tengely, his reference [27]) for period N = 36 for the variant f(N) in {+-1}, N even, which
   is NOT Erdos's setting (f(N)=0). Reported in his Section 5. [READ] This is mildly consistent
   with squares being special, but it is a different problem. [INFERRED]
7. No 2-adic / group ring of 2-group argument found in this literature for the +-1 problem; the
   only parity use is the elementary one (even q: sum over a period is odd, so non-convergent)
   and Murty-Pathak Thm 4.8 (N = 2 mod 4, f=+-1 incl. at N: coefficient of log 2 nonzero by
   parity). [READ via Bharadwaj's description, Section 5; Murty-Pathak itself not read.]
8. So Statement T, if correct, would settle all q = 1 mod 4 non-squares (q with divisor-sum >= 1, e.g. 45)
   beyond the 82 percent: a large advance on a problem the field calls open. [INFERRED]
9. Direct claim check: Chatterjee-Murty Prop. 3.1/3.6: if the conjecture fails for odd q then
   sum over d|q, d>=3 of 1/phi(d) >= 1. Squares are not excluded by it either way. [READ]
10. Search tooling: OpenAlex and part of Crossref/Semantic Scholar rate-limited (429); OpenCitations
    worked and gave full citing lists for both Okada and Livingston.

## 2. What is known (dated list of results on the conjecture)

### 2.1 The statement and its earliest source
- Livingston, Canad. Math. Bull. 8 (1965) 413-432, Section 5 "Erdos' Conjecture". [READ, scanned
  PDF text-extracted]. Livingston quotes Erdos's written communication: as Erdos remembered it, he
  had assumed f(n) = -1 (sic, text OCR as f(n) = +-1) for n not divisible by p and f(m)=0 if
  p divides m. Formal statement there: p a positive integer, f with period p, f(n) in {-1, 1}
  for n = 1,...,p-1 and f(p) = 0; then sum f(n)/n != 0 whenever convergent. Livingston says he
  cannot settle it; it would follow if the logs of 2 sin(k pi/p) (with pi, and log 2 for p even)
  were linearly independent over the algebraic numbers. (Paraphrase; the sentence "I remember
  correctly" is Erdos's.)
- Livingston section 1: Chowla's 1949 AMS-address problem (any period p, any nonzero complex f)
  was misattributed to Erdos; Livingston proves it false for p > 2 (Cor. 2.1) and true for
  p = 2 (Thm 1.1). [READ]
- Not found: Erdos's own problem papers, Guy's UPINT, erdosproblems.com entry (erdosproblems.com
  returned HTTP 403 to the fetch tool; WebSearch did not surface a page). So the Livingston 1965
  record is the earliest I can document. [not found; weak evidence]

### 2.2 Results, chronological
- 1973 Baker-Birch-Wirsing, J. Number Theory 5: f nonzero rational with f(n)=0 when
  1<gcd(n,N)<N implies L(1,f) != 0. Gives Erdos for N an odd prime. [READ via Bharadwaj, Chatterjee-
  Murty statements; original not read]
- 1982 Okada, Acta Arith. 40, 143-153: criterion for L(1,f)=0 (as modified by Saradha-Tijdeman
  2003, and Okada 1986 JLMS 33); consequence: Erdos holds if 2^omega(q)+1 > q (prime powers, two
  distinct odd primes). [READ via Chatterjee-Murty; zbMATH record of Okada: SNIPPET, keywords
  "linear independence, logarithms of algebraic numbers"]
- 2002 Tijdeman: Erdos holds for periodic completely multiplicative f; 2003 Saradha-Tijdeman:
  periodic multiplicative f with |f(p^k)| < p-1. [READ in Chatterjee-Murty intro, as claims.]
- 2007 Murty-Saradha: q odd and f odd integer-valued gives conclusion. [READ in Chatterjee-
  Murty intro]
- 2008 Hessami Pilehrood x2, "On a conjecture of Erdos", Mat. Zametki 83 (2008) 312-315;
  title in Russian; cites Okada and Livingston per OpenCitations. [SNIPPET: citing record only,
  and Bharadwaj's reference list [READ]; content of this paper NOT seen; its subject is
  unknown to me - possibly a different Erdos conjecture.] Worth reading.
- 2010 Murty-Saradha, J. Number Theory 130, "Euler-Lehmer constants and a conjecture of Erdos":
  Erdos holds for q = 3 mod 4. [READ as quoted in Chatterjee-Murty, Pathak, Bharadwaj]
- 2014 Chatterjee-Murty, J. Number Theory 145, 1-21, "Non-vanishing of Dirichlet series with
  periodic coefficients": new proofs of Okada's criterion and of BBW. [READ outline only (PDF
  headings); abstract via arXiv API SNIPPET]
- 2015 Chatterjee-Murty, Pacific J. Math. 275, 103-113 (arXiv 1501.04185): Erdos for >= 82 percent
  of q = 1 mod 4 via Prop 3.1: failure at odd q forces sum_{d|q,d>=3} 1/phi(d) >= 1; Cor 3.3:
  holds if smallest prime factor of q is >= d(q); hence squarefree q with k prime factors and
  smallest prime > 2k. They remark 100 percent cannot be reached by their method. [READ, text]
- 2016/2018 Pathak, "On a conjecture of Livingston" (arXiv 1808.09944, Canad. Math. Bull. 2019?):
  Livingston's linear-independence conjecture fails for composite q >= 4 (so Livingston's route
  to Erdos fails), true for odd prime q. Abstract and intro [READ]; Corollary 1 for prime q.
- 2018 Chatterjee-Murty-Pathak, Contemp. Math. 701 (Momose memorial), "A vanishing criterion for
  Dirichlet series with periodic coefficients" (arXiv 1809.01841): complete characterization
  of algebraic periodic f with L(1,f)=0 via odd and even parts. [SNIPPET abstract; PDF headings
  READ]. No Erdos statement in abstract.
- 2019 Pathak, Int. J. Number Theory 15 (arXiv 1909.03972): limiting distribution of L(k,f) over
  Erdos functions; Erdos conjecture true with "probability" one. Abstract says conjecture still
  open for q = 1 mod 4 or when 2^omega(q)+1 <= q. [READ intro and abstract]
- 2019 Chatterjee-Khurana, Proc. Japan Acad. A 95 (6) 58-63, "Erdosian functions and an identity
  of Gauss". [SNIPPET abstract] About digamma values, not the conjecture itself.
- 2020 (online Dec 2019) Chatterjee-Dhillon, Canad. Math. Bull. 63, "Linear independence of
  logarithms of cyclotomic numbers and a conjecture of Livingston": new proof of Pathak's
  disproof, modified conjecture. [SNIPPET]
- 2022 Murty-Pathak, "The Okada space and vanishing of L(1,f)", Funct. Approx. Comment. Math.
  66, 35-57: explicit basis of the Q-space of N-periodic f with L(1,f)=0; Thm 4.8: N = 2 mod 4,
  f in {+-1} implies L(1,f) != 0 whenever convergent (as described by Bharadwaj, [READ at second
  hand]; zbMATH review SNIPPET). Paper itself: fetch failed twice; left to the other helper.
- 2022 Bharadwaj, "On Primitivity and Vanishing of Dirichlet Series" (arXiv 2204.03674v1; Michigan
  Math. J. 75 (2025) 725-759 per Crossref, SNIPPET): Thm 4 new vanishing criterion (via primitive
  characters); Thm 2 (squarefree N, descent to pN for p > 2^omega(N) prod (q^2+2q+2)); Cor 1
  (N = 3 mod 4 squarefree, p > 2^omega(N) prod ((q+1)^2+1): conjecture true for period pN, giving
  new N = 1 mod 4 cases with p = 3 mod 4); Thm 3: q odd prime, period 4q, f in {+-1} (including
  at multiples of 4q, i.e. not Erdos's setting), L(1,f) != 0; counterexample of Tengely for
  N = 36 in that +-1-at-N setting; open question about odd N with a1 = 0, a_d in {+-1}
  sum a_d psi(d) = 0 (Section 8). [READ, full text extracted] States in the intro that
  parity makes even N vacuous and that "most attempts rely on Okada's criterion"
  (citing Chatterjee-Murty, Saradha 2006/2008, Saradha-Tijdeman).
- 2022 Bharadwaj-Pathak, J. Number Theory 238, 978-1011: values at k >= 2 under polylog
  conjecture. [SNIPPET, zbMATH review]
- 2022 Gun-Kandhil arXiv 2212.00376 and 2212.00366 (Q-independence of L-values of Erdosian
  functions for distinct prime periods; extension of Okada's cotangent result). [SNIPPET
  abstract]
- 2025 Bharadwaj-Murty-Pathak, Res. Number Theory 11:104, "On values of the digamma function at
  rational arguments": Okada constants. [SNIPPET, zbMATH review]
- 2017 Bettin-Martin, J. Number Theory 180, "On the non-vanishing of certain Dirichlet series" cites
  Okada (OpenCitations) [SNIPPET title only; probably about non-vanishing of L(s) for other
  periodic series, not Erdos]. 2023 Wang-Chakraborty-Kanemitsu, Mathematics 11:655 (Chowla's
  problem and Maillet-Demyanenko determinants) and 2025 Chakraborty-Kanemitsu-Kuzumaki (Springer
  book chapter) cite Livingston or Okada [SNIPPET]: class numbers, not Erdos.
- 2024-11/2026: arXiv math.NT listings with "periodic coefficients" (see 2.3): none concerns the
  conjecture.

### 2.3 arXiv listings (periodic coefficients / Okada), 2018-2026
All titles seen through the arXiv API [SNIPPET: titles and abstracts as summarised]. One line
each on Erdos:
- 2611.22795 (2026) Zheng, totient bound / cyclotomic polynomials gaps: no.
- 2610.33505 (2026) Hong, cubic L-functions over function fields: no.
- 2608.02085 (2026) Liu-Tang-Xin-Zhang, minimum period conjecture for restricted partition
  functions: no (periodic coefficients of partition quasi-polynomials).
- 2605.15740 (2026) Lovejoy-Osburn-Storzer, Bailey pairs/Eichler integrals: no.
- 2604.01191 (2026): no. 2512.20398 (2025) Rubinstein, Sylvester waves: no.
- 2012.02457 (2020) Goswami-Osburn, partial theta series with periodic coefficients: no.
- 2008.02570 (2020) Nakamura, Riemann functional equation, real zeros of L: no.
- 2007.14008 (2020) Sourmelidis-Steuding-Suriajaya, value distribution near critical line: no.
- 2204.03674 (2022) Bharadwaj: yes (new families).
- 1909.03972 (2019) Pathak: yes. 1808.09944 (2018) Pathak: yes (Livingston route). 1809.01841
  (2018) CMP: criterion, no Erdos claim in abstract.
- 2212.00366, 2212.00376 (2022) Gun-Kandhil: related (Erdosian-type families, prime periods).
- Queries "Erdos + Okada" in abstracts, "Erdos functions", "Erdos + periodic + nonvanishing",
  returned no further hit: [not found, weak evidence]. Searches with the exact phrases
  "perfect square" + "periodic" + Erdos returned nothing relevant (WebSearch 1 and 3).

## 3. What is open (as stated by sources)

- Erdos's conjecture for q = 1 mod 4 not covered by Okada or by Chatterjee-Murty Prop 3.1
  (the q with sum_{d|q,d>=3} 1/phi(d) >= 1). My own computation [INFERRED, exact arithmetic]:
  q = 45 gives 1.083, q = 225 gives 1.167, q = 441 gives 0.984 (so 441 IS settled), q = 21 gives
  0.75 (settled). So the first non-square open q is 45 (if no other route covers it) and
  the first open square is 225. Stated open by: Chatterjee-Murty 2015 intro [READ]; Pathak 2019
  abstract [READ]; Bharadwaj 2022 intro [READ]; zbMATH review of CM15 [SNIPPET].
  Note: q = 45 = 1 mod 4 is not a perfect square: under Statement T it would be settled.
  Also q = 1 mod 4 and q = 3 mod 4 both contain squares only in 1 mod 4 (odd squares are
  1 mod 8), consistent with T's "odd squares are the only exceptions" and Murty-Saradha.
  [INFERRED]
- Chatterjee-Murty state their method cannot give 100 percent of q = 1 mod 4 (remark after
  Prop 3.6, density of q with sum >= 1 is positive but small) and that "more ideas are needed";
  Bharadwaj notes (Example 5.1) even moduli exist where f in {+-1} has L(1,f) in the Q-span of
  log p (property U fails), so unit methods can fail in variants. [READ]
- Bharadwaj's explicit question (Section 8): is there odd N with 1 < ... a_d in {+-1} for d != 1,
  a_1 = 0, sum a_d psi(d) = 0 (psi = Okada-type weights)? A positive answer would refute
  Erdos's conjecture (L(1,f) in Q-span of log p). [READ, paraphrased; the exact formula
  involves d|N and a_d; see his Section 8]
- Status of squares: no source singles out squares. [not found]

## 4. Leads for this project (ranked)

1. Check Statement T against the literature's partial data. Statement: for odd q not a square,
   there is no Erdos function f with L(1,f) = 0. Data points available to test: Okada's range
   (prime powers, two odd primes), q = 3 mod 4 (Murty-Saradha), CM15 numerics. Test with the
   project's exact Okada-criterion enumerations at small q such as 45 (first non-square not
   covered by CM15 Prop 3.1), 117, 153, and squares 9, 25, 49, 81, 121, 225 (the criterion is a linear system plus +-1 constraints;
   exact enumeration small up to q about 40 via the congruence mod 2^(v_2(p-1)+1)). Size: days.
   Worth noticing: a proof of T would cover about 100 percent minus density-0 of the open q.
2. Formalize Okada's criterion and the 2-adic congruence in Lean (the criterion is stated in
   [Chatterjee-Murty Prop 2.1; Saradha-Tijdeman form]); needs L(1,f) as a linear form in logs via
   Plancherel and Baker (available as imported theorem). Size: weeks. Worth noticing: first
   machine-checked proof on this problem.
3. What T proves for squares: whether odd squares (q = 9, 25, 49, 225 ...) admit f with
   L(1,f)=0. Prime-power squares are covered by Okada. First open odd square: q = 225 = 15^2.
   (Check: 2^omega + 1 = 5 < 225; sum_{d|225,d>=3} 1/phi(d) = 1.167 >= 1 by my computation, so
   CM15 Prop 3.1 does not settle it.) Size: days.
4. Read Hessami Pilehrood-Hessami Pilehrood, Mat. Zametki 83 (2008) 312-315 and Tengely's
   counterexample (N = 36 variant) to see if a square pattern is documented. Size: hours.
5. Publishing: results on this conjecture appear in J. Number Theory, Pacific J. Math., Canad.
   Math. Bull., Michigan Math. J., Funct. Approx.; the active group is Murty, Pathak, Chatterjee,
   Bharadwaj (a circle of about 5 authors). Contact point is ordinary referee process. [INFERRED]

## 5. Overlap or conflict

- No overlap with Statement T found. Conflict check: T implies Erdos for non-squares q = 1 mod 4,
  which Chatterjee-Murty 2015 (82 percent) and Pathak 2019 / Bharadwaj 2022 describe as open;
  so T is either new or has an error. [INFERRED]
- Possible tension to check: Bharadwaj Thm 3 / Section 5 setting (f(N) = +-1 for even N) has a
  counterexample at N = 36 and Example 5.1 (period 12, property U fails); T's 2-adic argument
  is for f(q)=0, so it does not apply, but any 2-adic argument should be re-tested on those
  examples to confirm that the square obstruction appears at N = 36 (a perfect square).
  [INFERRED]
- Prime power/two-prime coverage by Okada and q = 3 mod 4 by Murty-Saradha are consistent
  with T (no non-square counterexample would contradict them).

## 6. Sources

- https://www.cambridge.org/core/journals/canadian-mathematical-bulletin (Livingston 1965 PDF fetched
  from cambridge.org aop-cambridge-core, DOI 10.4153/CMB-1965-029-2)
- https://arxiv.org/abs/1501.04185 (Chatterjee-Murty 2015); https://arxiv.org/abs/1405.6982
- https://arxiv.org/abs/1808.09944 ; https://arxiv.org/abs/1909.03972 ; https://arxiv.org/abs/1809.01841
- https://arxiv.org/abs/2204.03674 (Bharadwaj) ; https://arxiv.org/abs/2212.00366 ; 2212.00376
- https://api.zbmath.org/v1/document/_search (records for Okada, CM15, Murty-Pathak, BP2022)
- https://api.opencitations.net/index/v2/citations/doi:10.4064/aa-40-2-143-153 (19 citing)
- https://api.opencitations.net/index/v2/citations/doi:10.4153/CMB-1965-029-2 (17 citing)
- https://api.semanticscholar.org/graph/v1/paper/DOI:10.4064/aa-40-2-143-153/citations
- https://api.crossref.org/works (several records)
- No instruction text was found in any page addressed to an assistant.

Computation note: sums computed by me with exact phi in plain Python (no web code).

## 7. Search log

WebSearch calls (4 used):
W1 Erdos conjecture periodic f(n)=+-1 perfect square Okada criterion
W2 Erdos conjecture L(1,f) periodic Okada arXiv 2023-2026 odd modulus
W3 Tijdeman / Murty-Rath transcendental numbers periodic Erdos conjecture
W4 Erdos problem periodic +-1 Livingston erdosproblems / Guy / Chowla

Endpoint queries (fetch tool):
1 OpenAlex search Okada title (429)
2 OpenAlex search Livingston title (429)
3 zbMATH search Erdos conjecture periodic L(1,f)
4 arXiv abs "periodic coefficients" math.NT (sorted by date)
5 zbMATH Okada periodic arithmetical function
6 Semantic Scholar search Okada (429)
7 Crossref Erdos conjecture periodic nonvanishing
8 arXiv Erdos+periodic+"L(1" (empty)
9 zbMATH Erdos Dirichlet series periodic nonvanishing (404)
10 zbMATH Livingston series (404)
11 arXiv Erdos+periodic+nonvanishing (empty)
12 arXiv all:Okada math.NT
13 zbMATH Chatterjee Murty conjecture of Erdos
14 PDF arXiv 2204.03674 (Bharadwaj; read locally with pdftotext)
15 PDF arXiv 1501.04185
16 arXiv abs:Erdos+abs:Okada (empty)
17 arXiv Erdos+periodic+Dirichlet series (empty)
18 arXiv "Erdos functions" (empty)
19 arXiv Okada space / Euler-Lehmer / conjecture of Erdos
20 zbMATH Pathak Okada space
21 zbMATH Pilerhood (404)
22 zbMATH Saradha nonvanishing infinite sums (404)
23 PDF arXiv 1808.09944
24 zbMATH Tengely counterexample (404)
25 arXiv au:Pathak
26 arXiv ti:Dirichlet series periodic
27 PDF arXiv 1909.03972
28 PDF arXiv 1809.01841
29 PDF arXiv 1405.6982
30 PDF Livingston 1965 (CMB), read locally
31 MathOverflow via StackExchange API (blocked by fetch tool)
32 Math.SE via StackExchange API (blocked)
33 erdosproblems.com forum search (403)
34 Crossref Okada
35 Crossref Dirichlet periodic vanishing Erdos (429)
36 OpenCitations citations of Okada
37 OpenCitations citations of Livingston
38 Semantic Scholar citations of Okada
39-46 Crossref single-DOI records for citing works (8 calls, select param 400 error)
47-52 Crossref single-DOI records (6 calls, three succeeded, others 429)
53 Crossref filter=doi list of 5 citing works
54 zbMATH Bharadwaj-Murty-Pathak digamma
55 Scribd abstract (Khurana poster; no content)
56 arXiv abs 0909.2387
57 Waldschmidt/Tijdeman list PDF (two fetches 302 then PDF; no relevant)
58 Murty-Pathak Okada space (cmi.ac.in, 2 failures; queensu.ca redirect)
59 arXiv abs 2212.00376
60 arXiv abs 1809.01841
61 arXiv abs 2204.03674

Totals: WebSearch calls: 4. Endpoint queries: about 62 (61 listed, several counted twice for
retries).
