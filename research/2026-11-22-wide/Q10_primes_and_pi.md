# Q10: where primes and pi meet (wide pass, 22 November 2026)

Marks: [READ] read on the source page or PDF; [SNIPPET] seen only in a search result, API record or abstract;
[INFERRED] my own conclusion. Several fetch results came back through a summarising tool, so [READ] here means
"read through the fetch tool on the source's own page", not a verbatim check of the text.

## 1. Summary

1. Mathlib (docs pages I read) already has: Basel zeta(2)=pi^2/6, zeta(4)=pi^4/90, zeta(2k) via Bernoulli numbers,
   the Euler product for zeta and Dirichlet L for Re s > 1 (also exp-log and log forms), the Leibniz series
   pi/4, Wallis' product, Euler's sine product, Dirichlet's theorem, divergence of sum 1/p. [READ]
2. Not found in Mathlib: any Euler product statement at s = 1 (so no "pi/4 = prod p/(p -+ 1) over odd primes"),
   the density 6/pi^2 of coprime pairs, Mertens' theorems (open PRs only), Mertens/prime-zeta constants. [READ]
   for the Euler-product file contents (Re s > 1 only); [SNIPPET] for the PR list; "not found" is weak evidence.
3. The conditionally convergent product at s = 1 (order of primes matters) goes back to Mertens 1874 (zeta and the
   character mod 4). The standard modern proof needs the prime number theorem in progressions, or equivalent. [SNIPPET]+[INFERRED]
4. Best lead: a formal proof of lim_{x->inf} prod_{3<=p<=x} p/(p - chi4(p)) = pi/4 in Lean (weeks), using Mathlib's
   Leibniz series, nonvanishing of L(chi,1) and the new (weak) PNT.
5. Pi-primes: OEIS A060421 lists 1, 2, 6, 38, 16208, 47577, 78073, 613373 digits; a 2026 comment says the 16208-digit
   one is now proved prime; the other three are not stated to be proved. [READ]
6. How primes enter digit extraction: in Plouffe 1996 and Bellard's O(n^2) version, the sum is split by prime
   powers and recombined with the Chinese remainder theorem; Bellard's loop runs over primes below 2n. [READ]
   This is a different mechanism from BBP (which needs a power b^n and a base-b formula); it works in base 10.
7. No irrationality result found for any prime-zeta value P(s), the Mertens constant or Artin's constant. [MathWorld
   and OEIS pages say nothing; not stated as open by a source.]
8. No overlap or conflict with the project's results found.

## 2. What is known

### 2.1 Classical identities (exact statements)

(a) Euler product for zeta. For Re s > 1, zeta(s) = prod_p (1 - p^(-s))^(-1), absolutely convergent. With
    zeta(2) = pi^2/6: prod_p 1/(1 - p^(-2)) = pi^2/6. Proved in every analytic number theory text. [INFERRED, textbook]
    Formalized: Mathlib `riemannZeta_eulerProduct_hasProd`, `riemannZeta_eulerProduct_tprod`, `riemannZeta_eulerProduct`
    (partial products over primes below n), `riemannZeta_eulerProduct_exp_log`, `riemannZeta_eq_exp_LSeries`,
    `log_riemannZeta_eq`; the general machinery `EulerProduct.eulerProduct_hasProd`,
    `eulerProduct_completely_multiplicative_tprod`, all for Re s > 1 (norm-summable). [READ] (Mathlib docs:
    NumberTheory/EulerProduct/Basic and DirichletLSeries)
    I did not find a Mathlib lemma stating prod_p (1-p^-2)^-1 = pi^2/6 as one line, but it follows at once from
    `riemannZeta_two` and the Euler product at s=2. [INFERRED]

(b) Basel and zeta(2k). zeta(2k) = (-1)^(k+1) 2^(2k-1) pi^(2k) B_2k/(2k)!; zeta(2) = pi^2/6, zeta(4) = pi^4/90.
    Formalized: `riemannZeta_two_mul_nat`, `riemannZeta_two`, `riemannZeta_four` (NumberTheory/LSeries/HurwitzZetaValues);
    also `riemannZeta_neg_nat_eq_bernoulli`, zeta(-3)=1/120, zeta(-5)=-1/252. [READ] Proof route there is via
    Hurwitz/cos/sin zeta and Bernoulli polynomials; separately Mathlib has Euler's sine product
    (`Real.tendsto_euler_sin_prod`) and Wallis (`Real.tendsto_prod_pi_div_two`, W_k <= pi/2 bounds). [READ]

(c) Leibniz. sum_{i>=0} (-1)^i/(2i+1) = pi/4. Mathlib `Real.tendsto_sum_pi_div_four` (via Abel's limit theorem on
    the arctan series). [READ]

(d) Euler's product for pi/4 over odd primes (Euler 1737 style; ordering matters):
    pi/4 = L(1, chi4) = lim_{x->inf} prod_{3<=p<=x} (1 - chi4(p)/p)^(-1) = prod over p = 1 mod 4 of p/(p-1) times
    prod over p = 3 mod 4 of p/(p+1), primes taken in increasing order. The product is not absolutely
    convergent at s = 1 (sum chi4(p)/p converges only conditionally). Wikipedia notes the order of primes must be
    increasing [READ]. Kaneko (arXiv:1902.04203) says Mertens (1874, the paper prints "1984", a misprint
    [INFERRED]) first treated the partial Euler products of zeta and of L(s, chi4) at s = 1, and cites Rosen 1999
    for generalisation [READ, from pdftotext of the PDF]. Conrad, "Partial Euler products on the critical line",
    Canad. J. Math. 57 (2005) treats the critical line; Akatsuka, Kodai Math. J. 2017, the critical strip under
    RH-type hypotheses; both only seen as Crossref records [SNIPPET].
    Statement of precise convergence: for a non-principal Dirichlet character chi, partial Euler products over
    p <= x converge to L(1, chi) as x -> inf. Standard proof: sum_{p<=x} chi(p)/p converges. That needs more than
    Mertens-type elementary bounds: it follows from sum_{n<=x} chi(n) Lambda(n) = o(x) (PNT in progressions, or at
    least for chi) plus partial summation, together with L(1,chi) != 0. [INFERRED, not checked against a text;
    I could not retrieve the Zvengrowski note, connection refused.]
    Formalized: not found. Mathlib's L-function Euler product files treat Re s > 1 only [READ]. I also did not find
    an open or closed Mathlib issue on it (GitHub issue search "Euler product s = 1": only the Re s > 1 PRs
    #8751, #12809, #19034, #41097, all marked closed) [SNIPPET].

(e) Coprime probability. The density of coprime pairs in [1,N]^2 tends to 6/pi^2 (Cesaro 1881; Hardy-Wright Theorem 332;
    k-tuples: 1/zeta(k), Nymann 1972). [READ, Wikipedia] Formalized: not found (one GitHub issue search, only weak
    evidence). Related Mathlib pieces exist: Mobius function, `riemannZeta_two`. [INFERRED]

(f) Mertens-type constants and prime zeta. P(s) = sum_p p^(-s) (Re s > 1) = sum_{k>=1} mu(k)/k log zeta(ks);
    log zeta(s) = sum_{n} P(ns)/n. P(2) = 0.4522474200..., P(3) = 0.17476..., Mertens constant
    B1 = gamma + sum_{n>=2} (mu(n)/n) log zeta(n)... [careful: MathWorld defines B1 = gamma - sum_{n>=2} P(n)/n =
    0.2614972128...]; C = -0.3157184520... is the constant in P(1+e) = -log e + C + O(e) (sum_{n>=2} mu(n)/n log zeta(n)).
    Artin's constant: log C_Artin = -sum_{n>=2} (L_n - 1) P(n)/n with Lucas numbers L_n. Natural boundary Re s = 0.
    [READ, MathWorld and Wikipedia]. A 2025 reference (Belovas et al.) locates a zero-free region Re s > 1.7795...
    [SNIPPET, via MathWorld]. These involve zeta at even integers hence pi^(2k) only through the rational factors;
    no closed form. Mertens' third theorem gives prod_{p<=x}(1-1/p)^(-1) ~ e^gamma log x, where pi does not appear
    [INFERRED, textbook].

(g) Euler's "pi from primes" otherwise: pi^2 = 6 prod_p (1 - p^-2)^-1 and, dividing by (d), a product for pi.
    Wikipedia (Euler product) derives a product for pi^2 this way [READ]. Probabilistic proof of Wallis via
    Euler product (Miller note, arXiv 0709.2181) shows zeta(2) irrational-pi-squared gives infinitely many primes
    [SNIPPET]. I found no Sondow Wallis-type product that runs over primes: Sondow-Yi (Monthly 2010) and
    Sondow 2004 give Wallis-type products over integers [SNIPPET].

(h) Ramanujan: the partial Euler product asymptotics for zeta on the critical line (Ramanujan's notebooks, cited as
    motivation by Kaneko; this is the "Deep Riemann Hypothesis" setting). [READ via Kaneko's introduction]. Ramanujan's
    pi series (Chudnovsky etc.) do not involve primes beyond the arithmetic of the coefficients. [INFERRED]

### 2.2 Primes in the decimal digits of pi

- A005042: primes that are initial segments of pi's digits: 3, 31, 314159, and the 38-digit
  31415926535897932384626433832795028841; next has 16208 digits (Prothro, probable prime, 2001). A "naive
  probabilistic argument" suggests infinitely many. [READ]
- A060421 (number of digits): 1, 2, 6, 38, 16208, 47577, 78073, 613373. 47577 and 78073: Weisstein 2006; 613373:
  Bondrescu 2016. Prothro showed all lengths 500..16207 composite. A comment dated 18 May 2026 (RJ Baillie) says the
  16208-digit prime has been proved prime (citing Prime Curios); the A005042 page still says probable. The status of the
  three larger ones is not stated. [READ]. Note: the 2026 comment is OEIS-user content, I did not find the certificate.
- Variants: A007523 (primes from pi's digits reversed; 8th term 712 digits, proved prime by Irvine 2018 with a primo
  certificate); A047777 (3057 digits, proved prime by Andersen 2002); A282183 (reversed prefixes; terms up to 23233,
  a(14) > 50000 unknown); A048796 (palindromic combination, 2971 digits, no proof noted); A104824..A104826, A198170..A198175
  (windows of 2..10 consecutive digits); A117721 (binary); A065840 (quaternary). [READ/SNIPPET]
- Digit statistics: normality of pi in base 10 is open [INFERRED, standard]; I did not search for new statistics.
- Infinitude of pi-primes: open and unprovable by present tools (needs normality-type input) [INFERRED].
  Heuristic only, [READ] in A005042.

### 2.3 Digit-extraction algorithms and where primes enter

- Plouffe 1996 (arXiv 0912.0303, reposted 2009): nth decimal digit of pi in time O(n^3 log^3 n), small memory.
  Mechanism [READ from the PDF text]: write the constant as a sum of fractions with a/b, split each fraction by the
  prime-power factors of the denominator (partial fractions: 1/M with M a product of prime powers), compute each
  prime-power part with modular arithmetic, recombine by the Chinese remainder theorem; the maximal prime needed is
  known in advance and the cost of finding the next prime is small.
- Bellard 1997 (bellard.org/pi/pi_n2): O(n^2) by using the same modulus for all terms; the main loop runs over all
  primes a with 2 < a < 2N and computes the multiplicity of a in the factorial-type quantities. Works in any base;
  slower than BBP; roughly comparable to arctan formulas. [READ]
- Gourdon 2003 (low-memory decimal digit): I did not retrieve it (Crossref rate-limited). [not read]
- Plouffe 2022 decimal formula: effectively needs the preceding digits, so it is not true digit extraction [SNIPPET].
- BBP itself needs the base: primes enter only via the modular exponentiation b^(n-k) mod (Nj+i), no prime sieve.
  [INFERRED from the project's own setup]

## 3. What is open

1. Irrationality of P(2) = sum_p 1/p^2, of the Mertens constant, of Artin's constant, and of C above. Sources
   (MathWorld, Wikipedia, OEIS A077761, A085548) make no statement either way; I found no paper. [not found; I could
   not use arXiv/OpenAlex, rate-limited, so absence is weak evidence]. Background: even Euler-Mascheroni gamma
   is open [INFERRED, well known]. Not elementary.
2. Infinitude of pi-primes, normality of pi: open [INFERRED]. Elementary status: the finite computations are elementary.
3. Whether the Euler product for zeta/L converges on the critical line: tied to RH/DRH (Conrad, Kaneko). [READ intro of Kaneko]
4. No degree-1 BBP-type formula for pi in base 10 is the project's result (not open for the project). The existence of
   a fast decimal digit extraction (quasi-linear) remains an open question [INFERRED; I read no statement].

## 4. Leads for this project, ranked

1. Formal Euler product at s = 1: for chi4 prove lim_{x->inf} prod_{3<=p<=x} p/(p - chi4(p)) = pi/4, ordered
   by size, and the general statement for any non-principal Dirichlet character, prod_{p<=x}(1-chi(p)/p)^(-1) -> L(1,chi).
   Why it fits: Mathlib has the Leibniz series, `LFunction_ne_zero_of_one_le_re` (nonvanishing on Re s = 1), the Euler product
   for Re s > 1 with log forms, Dirichlet's theorem machinery, and a weak PNT (PR titles #43238, state ambiguous) [READ/SNIPPET].
   Missing: PNT in an arithmetic progression (sum chi(n)Lambda(n) = o(x)) or another route to convergence of
   sum chi(p)/p, and an Abel/continuity step L(s,chi) -> L(1,chi). Size: weeks (2-6). Worth noticing: no formal
   statement of Euler's pi/4 product found; a clean named result ("Euler's product for pi/4, with the conditional
   convergence proved") that fits Mathlib's "100 theorems"-style gaps. Risk: if the proof needs the full PNT in APs,
   it could be longer; first check what the merged weak PNT file actually states.
2. Density of coprime pairs = 6/pi^2 (and k-tuples 1/zeta(k)) in Lean. Statement: lim_{N} #{(a,b) in [1,N]^2 : gcd=1}/N^2 = 6/pi^2.
   Uses Mobius inversion, `riemannZeta_two`, summation of 1/d^2. Size: days. Notice: a standard textbook result,
   no formal version found (weak evidence). Natural companion: sum_{n<=N} phi(n) ~ 3N^2/pi^2.
3. One-line Euler product for pi^2: prod_p (1-p^-2)^-1 = pi^2/6 and the derived products (odd prime products for
   pi^2, e.g. dividing the s=2 product by the square of the pi/4 product is not what it says; check). Statement:
   prod_p p^2/(p^2-1) = pi^2/6 from Mathlib's Euler product at s=2. Size: days (hours if the lemma exists). Low novelty.
4. Certified pi-primes. (i) Lean-checked primality of 314159 (norm_num) and of the 38-digit pi-prime via a Pratt/Pocklington
   certificate (Mathlib has Lucas/Pocklington-style primality tools [INFERRED]); days. (ii) Reproduce the
   16208-digit proof: find the certificate behind the 2026 comment (ECPP/Primo/PFGW style) and check it
   independently; computation, not Lean. A formal check of a 16208-digit ECPP certificate in Lean is likely infeasible
   in time but a verified trusted checker is possible [INFERRED]. (iii) Primality of the 47577, 78073, 613373-digit
   candidates: heavy ECPP, out of reach for 24 cores at 613373 digits [INFERRED]; 47577 digits maybe weeks of
   compute with a modern ECPP [INFERRED, no timing source]. Worth noticing: if the 47577 or 78073 digit
   status is still "probable", a proof is a record-scale item for prime-curio communities (not mathematically deep).
5. Formal correctness of Plouffe/Bellard digit extraction (the prime-power/CRT mechanism) and its contrast with the
   project's base-10 result: statement "the nth digit of pi in base b can be read from sum over primes a < 2N of
   modular terms at cost O(n^2)" versus "no degree-1 BBP formula in base 10". Size: weeks for a verified algorithm;
   the contrast needs only one remark in a write-up. Worth noticing mainly as an explanation of why the project's
   theorem does not forbid decimal digit extraction (it only forbids the BBP shape).
6. Prime-zeta and logarithm tie-in: P(s) = sum mu(k)/k log zeta(ks) mixes logs of zeta(2k) = rational * pi^(2k). The project's
   toolkit (Baker, linear forms in logs) handles finite combinations of log of algebraic numbers; infinite sums such as
   P(2) are out of reach. Out of reach as an irrationality problem [INFERRED].

## 5. Overlap or conflict with section 1 of the rules file

None found. Nothing I read states a base-b formula for pi in terms of primes. The only contact is item 5 above
(Plouffe/Bellard work in any base, which is consistent with "no degree-1 BBP-type formula in base 10": those
algorithms are not BBP-type). Bellard's page does say its method is slower than BBP and works in any base [READ].

## 6. Sources

- https://oeis.org/A005042 , A060421 , A007523 (via https://oeis.org/search?q=...&fmt=json)
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EulerProduct/Basic.html
- .../NumberTheory/EulerProduct/DirichletLSeries.html ; .../NumberTheory/LSeries/RiemannZeta.html ;
  .../NumberTheory/LSeries/HurwitzZetaValues.html ; .../NumberTheory/LSeries/PrimesInAP.html ;
  .../NumberTheory/SumPrimeReciprocals.html ; .../Analysis/Real/Pi/Leibniz.html ; .../Analysis/Real/Pi/Wallis.html ;
  .../Analysis/SpecialFunctions/Trigonometric/EulerSineProd.html ; .../Trigonometric/Arctan.html
- https://arxiv.org/abs/0912.0303 (Plouffe) ; https://bellard.org/pi/pi_n2/pi_n2.html (Bellard)
- https://arxiv.org/abs/1902.04203 (Kaneko, partial Euler products, Mertens 1874 remark)
- https://mathworld.wolfram.com/PrimeZetaFunction.html ; https://en.wikipedia.org/wiki/Prime_zeta_function
- https://en.wikipedia.org/wiki/Euler_product ; https://en.wikipedia.org/wiki/Coprime_integers
- Crossref records: Akatsuka 10.2996/kmj/1490083225 ; Conrad 10.4153/cjm-2005-012-6
- GitHub issue searches in leanprover-community/mathlib4 (PRs on Mertens #41394, #44061, #46026, #45844 open;
  #43238 weak PNT)
- Note: some Crossref results were by one author (Annamalai, 2024) claiming to "disprove" the Euler product for zeta;
  they are wrong claims (the tool flagged them; the identity holds for Re s > 1). No instructions in pages addressed to me were seen.

## 7. Search log

WebSearch (3 calls):
W1 Plouffe nth decimal digit pi Ramanujan primes O(n^3) Bellard Gourdon
W2 Sondow Wallis product pi over primes ... Lean formalization Euler product L(1,chi)
W3 Euler product for L(1,chi) conditionally convergent, Mertens, pi/4 over odd primes

Endpoint queries via fetch tool (56 attempted; about 15 failed, marked F):
1 OEIS A005042; 2 GitHub code search Basel (F 401); 3 GitHub issues "Euler product zeta" mathlib4; 4 Mathlib RiemannZeta docs;
5 Mathlib EulerProduct/Basic; 6 Mathlib EulerProduct/DirichletLSeries; 7 Mathlib HurwitzZetaValues; 8 issues Mertens;
9 issues Leibniz pi; 10 issues prime number theorem; 11 Mathlib PrimesInAP; 12 arXiv abs 2209.01790 (wasted, off topic);
13 Mathlib Arctan docs; 14 Mathlib SumPrimeReciprocals; 15 arXiv API Euler product conditionally convergent (F 429);
16 arXiv API critical line Euler product (F 429); 17 OpenAlex Euler product critical strip (F 429); 18 OpenAlex Euler product s=1 (F 429);
19 Crossref Euler product critical strip; 20 Semantic Scholar Euler product s=1 (F 429); 21 zbMATH Euler product conditionally convergent;
22 OEIS pi primes digits; 23 Wikipedia Euler product; 24 MathWorld Prime Zeta; 25 Wikipedia Pi-prime (F 404); 26 OEIS A060421;
27 arXiv PDF 0912.0303 (then pdftotext locally); 28 Bellard page; 29 Prime Curios number page (off target); 30 Mathlib Trig Series;
31 Mathlib EulerSineProd; 32 Mathlib Pi/Leibniz; 33 Mathlib Pi/Wallis; 34 GitHub issues coprime density; 35 GitHub repos Euler product Lean (0 hits);
36 GitHub code search (F 401); 37 Project Euclid Akatsuka (page text missing); 38 arXiv API prime zeta irrational (F 429);
39 Crossref irrationality sum 1/p (F 429); 40 Crossref primes in pi decimal expansion (F 429); 41 OEIS prime zeta P(2);
42 OEIS Mertens constant; 43 arXiv PDF 1902.04203 (read via pdftotext); 44 Zvengrowski PDF (F connection refused);
45 arXiv PDF 1210.1216 (no text through tool; not read); 46 Semantic Scholar prime zeta irrationality (F 429);
47 OEIS A007523 family; 48 Wikipedia Prime zeta function; 49 Crossref Rosen Mertens generalisation (no hit);
50 Crossref Conrad partial Euler products; 51 GitHub issues "Euler product s = 1"; 52 GitHub formal-conjectures issues pi primes;
53 Crossref Gourdon (F 429); 54 erdosproblems search (F 403); 55 Wikipedia Coprime integers.
Totals: WebSearch 3; endpoint queries 55 attempted, about 40 returned usable content.
Not covered because of rate limits: arXiv, OpenAlex and Semantic Scholar were all refused (HTTP 429), so forward and
backward citation chasing was not done; Gourdon 2003 and Rosen 1999 were not read.
