# P04: algorithms and complexity for isolated digits of pi (22 Nov 2026)

Marks: [READ] = read on the source's own page or PDF (through the fetch tool, PDFs converted with
pdftotext); [SNIPPET] = only a search result, abstract or API record; [INFERRED] = my own
conclusion. Several PDFs could be read only after local text conversion; those that I could not
read are said so. Pages that were summarised by the fetch tool and not read verbatim are marked
[SNIPPET].

## 1. Summary

1. BBP 1995/97 (preprint text read): O(n) terms, O(log n) operations per term, precision
   O(log n); bit cost O(n log n M(log n)), so O(n log^3 n) with schoolbook multiplication.
   Memory is "minuscule" but no formal space bound; the claim "pi is in SC" was NOT proved there.
2. Chee Yap (preliminary version, June 2010) proved that pi has n-th bit computable in time
   polynomial in n and space O(log n), using (a) a BBP-like series with weights 2^(-kc) and
   (b) a finite irrationality measure of pi. He also notes the BBP algorithm itself is not
   shown to be an algorithm (carry/run-of-ones ambiguity); Lipton (2009, 2010) says the same. I
   found no published (journal) version of Yap's paper.
3. Plouffe 1996 (reprinted on arXiv 2009): decimal digit in O(n^3 log^3 n) time, "very little
   memory", no proof that it cannot be faster. Bellard 1997 (web page): O(n^2), any base, small
   memory. Gourdon 2003: I could NOT retrieve the paper; Plouffe's text says it uses a series
   plus its asymptotic representation and reaches about 4 million digits in hours. The
   claims "O(n^2) time, O(sqrt n) memory" for Gourdon are from memory only, not confirmed.
4. Plouffe 2022 (arXiv 2201.12601, read): an "explicit expression" for the n-th digit via Bernoulli
   and Euler numbers. It needs B_2n or E_2n with n of the size of the position; no complexity
   claim; practical limit 10^8 (Bernoulli), 2.3*10^6 (Euler). It is not isolated-digit
   extraction in the BBP sense (cost grows like computing the number itself).
5. Open-problem status: BBP's own questions (decimal digit of pi in SC, pi in SC in all bases,
   e and sqrt 2, log 2 in base 10, log 23 in base 2) are stated open in the preprint [READ].
   Zudilin's September 2024 note "BBP-style computation for pi in base 5": v1 claimed bases 5
   and 10; v2 (17 Sep 2024) calls itself a joke and its section 3 is titled "An obvious flaw":
   the identity used fails for large terms, tail uncontrolled. So base 10 is still open there,
   and the paper states the question for other bases is open [READ v1 and v2].
6. Records: PiHex (Percival) quadrillionth bit, Sept 2000, Bellard's formula; Sze (Yahoo) 2010,
   bit 2*10^15 with 256 bits, Bellard's formula, 503 CPU-years; Takahashi 2016, hex digit
   10^17 (bit about 4*10^17), Bellard's formula, 320 h on 512 Xeon Phi nodes.
7. Terms per bit: BBP formula 4 non-zero terms per 4 bits = 1 per bit; Bellard 7 per 10 bits =
   0.7 per bit ("43% faster", = 1/0.7); Euler 1779 (found 2023) 30 bits per 21 divisions = 0.7
   (the Wikipedia article, not read in the Euleriana paper itself). Project's value 2/3 (Huvent
   2001) is better than both; I did not find Huvent's formula in a fetched primary source (his
   home page failed on a certificate error).
8. No lower-bound or optimality theorem for terms per bit, nor for time, nor "no polylog-space
   quasi-linear base-10 algorithm", found in print (Bellard 1997 himself asks whether a faster
   formula exists). The project's "no degree-1 formula beats 2/3 terms per bit" would be a new
   statement in the literature as far as I can see.
9. Wider family in print: Kristensen-Mathiasen (arXiv 2208.07696, J. Number Theory 2022) search
   BBP-type formulas with irrational (Pisot) bases and integer coefficients, found one for pi in
   base 1+sqrt(3). Whether such formulas give digit extraction is not addressed there [READ
   abstract; body partly].
10. Safety note: every OpenAlex response contained a notice asking an AI agent to create an API
    key by submitting the user's e-mail address. I ignored it (not part of the task).

## 2. What is known

### 2.1 BBP (1995 preprint, 1997 paper)

- The preprint text (davidhbailey.com/dhbpapers/digits.pdf, read in the extracted part from
  section 3 to the end) states: to compute the n-th binary or hex digit one sums O(n) terms,
  each needs O(log n) arithmetic operations, precision O(log n) digits; total bit complexity
  O(n log(n) M(log n)); "even with ordinary multiplication" O(n log^3 n). [READ]
- It says this is slower by a factor of log log log n than the fastest known algorithm that
  produces all first n digits (Schoenhage-Strassen based), and calls the comparison "totally
  misleading" since the strength is simple implementation without FFT. [READ]
- Error control: if the working precision (IEEE 64 bit) is used for sums of n terms, at most
  log2(2n) bits of the result are corrupted; "check significance" by also computing at n+1 or
  n-1. No rigorous bound for the length of a run of 1s (the 0.5 +- eps problem). [READ] The
  same ambiguity is quoted by Yap as an acknowledged "possible ambiguity ... in practice does
  not arise". [READ, Yap]
- Extension: any S = sum p(k)/(c^k q(k)) with integer polynomials p, q, integer c is said to be
  handled "similarly". Constants computed: pi, log 2, pi^2, log^2 2, log(9/10) (decimal digit
  of log(9/10) via log(9/10) = -Li_1(1/10)) at positions 10^6 .. 10^10. [READ]
- Section 5: log of a rational m of the form product (2^a-1)/product (2^b-1) is computable in
  base 2; primes below 19 all are; 2^11-1 = 23*89 so log 23 and log 89 are both or neither
  computable; Pomerance: no identity of that type for 23 (cyclotomic values at 2 have a new
  prime factor); Harley: 29 and 37 via Aurifeuillian factors. [READ] (This is exactly the
  project's Theorem criterion for logs; see section 5.)
- Section 6 "Relation bounds": PSLQ found no identity of the form
  pi = a0^-1 sum n^-k (a1/(mk+1)+...+am+1/(mk+m)) for bases n in 2..128, m <= min(n,32), norm
  <= 10^12, except n = 16 (power of 2 aside). J. P. Buhler "has reported a proof" that any
  such identity must have n = 2^K. Stated not to exclude more complicated formulas. [READ]
  (This is the earliest print statement of the project's "iff power of 2"; an unpublished
  proof report. The published 1997 text may differ; I read the preprint only.)
- Section 7 Questions (verbatim sense): (1) find an n-th decimal digit algorithm for pi in SC;
  not even clear pi is in SC in base 10; (2) show pi in SC in all bases; (3) are e and
  sqrt 2 in SC in any base; (4) is log 2 in SC in base 10; (5) is log 23 in SC in base 2. [READ]

### 2.2 Bellard 1997

- Formula: pi = 2^-6 sum (-1)^n 2^-10n ( -2^5/(4n+1) - 1/(4n+3) + 2^8/(10n+1) - 2^6/(10n+3)
  - 2^2/(10n+5) - 2^2/(10n+7) + 1/(10n+9) ). Seven terms per 10 bits. Page says it gives the
  n-th binary digit "43% faster" than BBP using the BBP algorithm; ends by saying whether an
  even faster formula exists is an open question. No big-O claim. [READ, bellard.org]
- Bellard's second page ("n-th digit of pi in any base in O(n^2)", Jan 1997, alpha version):
  builds on Plouffe; Chinese remainder / same modulus for all terms; uses primes a < 2N;
  precision control by small margin; no high-precision arithmetic except one modular inverse;
  "slower than BBP but works in any base"; memory small. Formulas were images and did not
  load, so exact bounds are as stated by Plouffe: O(n^2). The page does not mention Gourdon.
  [READ]

### 2.3 Plouffe 1996 (decimal digit)

- Claim: n-th decimal digit of pi in O(n^3 log(n)^3) time, "very little memory"; method splits
  1/M for M = binomial(2n,n) into sum of fractions with prime-power denominators by the
  Euclidean algorithm, then BBP-type modular exponentiation. About 8 word-size memory cells
  plus n. Applies to pi+3 type series with central binomial coefficients, zeta(3), pi*sqrt 3,
  pi^2, (2/sqrt5) log phi. Says e does not qualify (1/n! has huge powers of 2). He "has neither
  found a faster algorithm nor proved that none exists". [READ]
- It does not address the rounding/carry issue explicitly; whether the algorithm is proved
  correct for every n is not stated. [INFERRED from reading]
- Plouffe's note says the algorithm shows pi in two classes: "SC(2)" (BBP) and the new class,
  and credits Bellard (1997, O(n^2)) and Gourdon (later; "inspired but not same idea", uses a
  series and its asymptotic representation, "4000000 digits in hours"). [READ]

### 2.4 Gourdon 2003

- Paper "N-th digit computation" / "Computation of the n-th decimal digit of pi with low
  memory", numbers.computation.free.fr/Constants/Algorithms/nthdecimaldigit.pdf. Every fetch of
  that host failed ("Command failed with no output") and the web archive is blocked for my
  fetch tool; three search attempts did not return its text. So: complexity (time O(n^2)?
  memory O(sqrt n)?) NOT CONFIRMED by me. Wikipedia cites it as a reference only [SNIPPET].

### 2.5 Plouffe 2022

- arXiv 2201.12601 (read): from the inequalities of Abramowitz-Stegun 23.1.x for B_2n and E_2n
  (pi^(2n) = 2(2n)! zeta(2n)/|B_2n| (2^(2n-1)) style, isolating pi) one obtains pi to an error
  below 2^-n or 10^-n for n >= 10 (Bernoulli, adding Euler-product terms 2,3,5,7 for decimal).
  So "the n-th digit" needs B_2n (record 10^8 at the time) or E_2n (his own run reaches
  2,300,000 on an i9-9900K). No complexity bound; convergence of any all-digits use is only
  polynomial. The Wikipedia article says it effectively needs the preceding digits. [READ]
  [INFERRED] it is not isolated-digit extraction in the BBP sense: the cost is that of one
  huge Bernoulli/Euler number, which grows at least linearly in the position.

### 2.6 Proved complexity statements

- Yap, "Pi is in Log Space" (Preliminary Version, 22 June 2010), Theorem 1: if alpha > 0 has
  a finite irrationality measure and a BBP-like series (terms 2^(-kc) p(k)/q(k), integer
  polynomials, c >= 1) then its n-th bit is decidable in O(log|n|) space; polynomial time
  (stated in Lipton's report). Corollary: pi, pi^2, log 2. Uses mu(pi) <= 7.6804 (Salikhov) in
  that version; now mu(pi) <= 7.103205... (Zeilberger-Zudilin 2015). Open per Yap/Lipton: which
  numbers are in Logspace; whether the plain BBP algorithm works as claimed. [READ Yap
  introduction and section 2; READ Lipton 2010 post]
- Lipton 2009 post: "pi in SC" stated as an unproved claim of BBP; precision issue near 0.5;
  he conjectured it (via irrationality measure). [READ]
- Allender et al. (arXiv 1112.4295): bits of algebraic numbers in C=NC1 within L for unary
  position, counting hierarchy for binary position; "virtually no lower bounds". Their
  Theorem 1: bounded irrationality measure plus convergent series with FTC0 terms gives TC0
  for unary n. Contents of the PDF not read beyond intro/related work. [READ partially]
- Yap's base is 2 (weights 2^(-kc)). [INFERRED] The same proof works for base b^(-kc), b integer
  (replace 2 by b in lemmas 3-6, since only the geometric decay of the tail and the bound
  |pi - p/q| > q^-K are used). So any decimal BBP-type formula would put pi in Logspace in
  base 10; conversely absent such a formula (project result) the known base-10 algorithms are
  the Plouffe/Bellard/Gourdon family, whose SC status I did not find proved.

### 2.7 Formal verification

- Bertot, Magaud, Zimmermann, "Distant decimals of pi: formal proofs of some algorithms
  computing them and guarantees of exact computation", J. Automated Reasoning 2017
  (arXiv 1709.01743, read after text conversion). Coq proof of the BBP formula and of the
  digit algorithm with an a posteriori guarantee (the computed bounds exclude carries); they
  compute in Coq the millionth hex digit (2) in under 2 minutes (25 s four cores) and the
  billionth (8) in 19 h; HOL Light has a formalisation of the BBP identity itself. The
  guarantee is per-run (it can decline), not a worst-case theorem. [READ]
- I found no Lean or Mathlib formalisation of BBP digit extraction (GitHub issue search in
  mathlib4 "BBP pi": 0 results; GitHub repositories "lean4 BBP": 0). [READ endpoint output]

### 2.8 Other print items touching the topic

- Bailey 2006 "The BBP algorithm for pi" (osti 983322, read after conversion): run time grows
  roughly linearly in position d; d = 10^7 takes 51 s (Apple G5); 10^15 is "roughly the
  present-day limit"; table: 10^6..10^10, 1.25*10^12, 2.5*10^14. [READ]
- Bailey Compendium (April 2023, read): says Borwein-Galway-Borwein 2004 "showed that there
  are no other degree-1 BBP-type [formulas] for pi" except those with base a power of 2; Euler
  1779 formulas (2),(3) listed; 2023 Craig-Wood. Lagarias suggests special significance for
  constants with formulas in two or more bases. [READ] The Compendium thus states more than the
  Borwein-Galway abstract proves (that abstract: b-ary Machin-type formulas for pi do not exist
  for b != 2) [READ abstract via Crossref/OpenAlex]. This agrees with the project's section 1.
- Takahashi, Ramanujan J. 2019 "On the computation and verification of pi using BBP-type
  formulas" and 2021 "Montgomery multiplication in binary BBP-type formulas": exist [SNIPPET,
  titles only; not read].
- Kristensen-Mathiasen 2022: definition BBP(d,b,n,A); Theorem 1: arg(1 + r e^(i theta)) =
  BBP(1, 1/(r^b)-type base, b, A) for theta in a rational multiple of 2pi / 2|b; search
  algorithm with Pisot bases, pi in base 1+sqrt 3. [READ abstract and Theorem 1]
- Barsky-Munoz-Perez-Marco "On the genesis of BBP formulas" (arXiv 1906.09629; Acta Arith. 2021):
  general generating method, null formulas; no completeness or optimality claim. [READ
  abstract]

## 3. Complexity table (time, space, what is proved)

| Method | Base | Time | Space | Proved? |
|---|---|---|---|---|
| BBP 1995/97 | 2^k | O(n log n M(log n)), O(n log^3 n) schoolbook [READ] | "minuscule", O(log n) words informally | cost yes; correctness (carry ambiguity) not proved in the paper [READ Yap/Lipton] |
| BBP + Yap 2010 | 2 | poly(n) | O(log n) | Yes, assuming finite irrationality measure of pi (known); preliminary version only [READ] |
| Bellard 1997 formula | 2^10 | about 0.7 of BBP's term count [READ] | as BBP | same as BBP |
| Plouffe 1996 | any | O(n^3 log^3 n) [READ] | about 8 words + n | claimed; no carry analysis seen |
| Bellard 1997 (n^2) | any | O(n^2) [READ page, formula in image] | small | claimed on web page |
| Gourdon 2003 | 10 | not confirmed | not confirmed | not confirmed |
| Plouffe 2022 | 2, 10 | cost of B_2n / E_2n, no claim [READ] | n/a | formula with explicit error bound; practical limit 10^8 |
| Euler 1779 | 2 | 30 bits per 21 divisions [SNIPPET Wikipedia] | as BBP | identity classical |

All-digits comparison: the fastest all-digits methods are quasi-linear in time but need linear
space (BBP 1997 preprint, Yap introduction) [READ].

## 4. What is open (with sources)

O1. Decimal digit of pi in SC; pi in SC in every base; e and sqrt 2; log 2 base 10; log 23 base 2.
    Stated open in BBP preprint section 7 [READ]. Status 2026 as far as I found: only the
    base-2 (and base 2^k) cases are settled for pi, log 2 (Yap 2010, preliminary). I found no
    paper settling base 10; Zudilin 2024 v2 withdrew the base-10 claim [READ]. Not found does
    not prove absent; searched arXiv/OpenAlex/Crossref for "digit extraction", "base 10",
    "SC", "log space", Plouffe 2022 citations (OpenAlex showed 3 citations of Plouffe 2022,
    titles not read).
O2. Rigorous version of BBP correctness without irrationality measure (the carry/0.5 problem):
    stated open as "make BBP an algorithm" by Lipton 2010 [READ]; Yap's theorem fixes it for
    pi using mu(pi) < infinity. The remaining open part is effective: Yap's bounds depend on K;
    the actual working precision needed is unknown beyond n bits-ish (Bertot et al. get exact
    guarantees per run).
O3. Whether pi is in Logspace in base 10 (or has any polylog-space algorithm): no source states
    it besides BBP's questions. [not found]
O4. Is there a formula faster than Bellard's / any lower bound on terms per bit: asked by Bellard
    1997 as an open question [READ]. No answer found in print. (Project has 2/3.)
O5. Time lower bounds: none found. Plouffe 1996 explicitly says he has not proved a faster
    algorithm cannot exist [READ]. Allender et al.: "virtually no lower bounds" for bits of
    algebraic numbers [READ].
O6. Digit extraction in bases other than powers of 2 using non-BBP formulas (Zudilin's question
    for "formulae defined over quadratic or more general algebraic extensions" ends his
    section 3) [READ].
O7. Whether the Pisot-base formulas of Kristensen-Mathiasen yield any digit extraction. Not
    addressed in the abstract [READ].

## 5. Leads for this project, ranked

L1. (days to 2 weeks) Formal "BBP is an algorithm": for every degree-1 formula of base 2^B
    for pi, a Lean theorem: the bit decision is correct provided the working precision p
    satisfies p >= c + (K-1)n-type bound where K is any irrationality measure of pi, and
    that K exists unconditionally. Exact statement: for all n, for all m with 2^m (B-power)
    large enough, the sign of {S_m}_(n-1) - 1/2 decides bit n (Yap Lemma 6). Fit: the
    project has Baker's theorem formalised. [INFERRED] The inhomogeneous linear form
    q*(i*pi) - i*p = q*log(-1) - i*p (beta_0 = -ip, alpha_1 = -1, nonzero since pi is
    irrational) falls under Baker's inhomogeneous theorem, giving |pi - p/q| > q^-C for an
    effective C, i.e. a finite irrationality measure of pi, which is all Yap's Theorem 1
    needs. CAUTION: I have not checked that the form in the imported Lean statement allows
    beta_0 != 0; also known measures of pi come from Mahler 1953 and Salikhov, not Baker, so
    check that Baker's inhomogeneous case really gives a polynomial bound (it does in
    Baker-Wuestholz style for fixed alphas; verify). Worth noticing: a machine-checked proof
    that BBP digit extraction for pi is correct with a stated precision and space O(log n)
    does not seem to exist (Bertot et al. have per-run guarantees only; no Lean BBP found).
    The project's classification gives the exact class of formulas for which it applies.
L2. (weeks) A verified implementation: a Lean 4 program computing the n-th hex digit by
    Bellard's formula (or Huvent's, 2/3 term per bit) with the proof of L1, tested against the
    published digits (Takahashi: hex digits from 10^17: A937EB59439E485E; Sze: 2*10^15 bit
    string above; Bailey table: position 10^10 hex 921C73C6838FB2 etc. as given in the 1997
    preprint). Fit: Bertot et al. give a blueprint (Coq): real-number formula, rounded
    arithmetic with error bounds, modular exponentiation inside. Noticeable: first formally
    verified isolated-digit extraction in Lean/Mathlib; also the project's 2/3 formula in an
    executable form.
L3. (weeks) State and prove the optimality theorem cleanly with the right measure and compare
    with print: measure = non-zero rational coefficients per bit (Bellard's own measure, 43%
    faster). The theorem "no degree-1 BBP-type formula for pi (any base) has fewer than 2/3
    non-zero terms per bit" answers Bellard's 1997 question [READ] for degree 1. Cite and
    position: Bellard's page (question), Takahashi 2019/2021 (implementation costs), the
    Compendium (formulas), Craig-Wood 2023 (Euler: 0.7 per bit), Bailey/Borwein-Galway
    (classification of bases). The right journal places: Experimental Mathematics, Math.
    Comp., J. Number Theory, Amer. Math. Monthly; the Bailey Compendium maintainer and
    Craig-Wood/Euleriana would notice. One needs to state which time measure: cost per term
    is modular exponentiation of O(log n) multiplications of word size, so total time
    proportional to (terms per bit) * n up to log factors. [INFERRED]
L4. (weeks to months, uncertain) Optimality for a wider family: degree-1 formulas whose
    denominators are irreducible polynomials over Q of degree >= 2 in the index (not split
    over Q), or denominators linear forms over a number field (Gaussian integers as in
    Zudilin, Pisot base as in Kristensen-Mathiasen). Exact question: for weights beta^(-j)
    with beta in Z[i] or a Pisot unit/algebraic integer, is "formula for an algebraic multiple
    of pi gives digit extraction in an integer base" ever true? Zudilin's flaw (v2 section 3)
    is exactly that the tail has uncontrolled denominators 5^(2n+1-d+k) when 2n+1 > d-k. A
    theorem "no BBP-type digit extraction in a base not a power of 2 for any series
    sum_j alpha^j / (qj + r) with alpha algebraic" would settle Zudilin's question and
    extend the project (primitive prime divisors in number fields, Baker already in hand).
    [INFERRED] first step: formalise why the real-part and imaginary-part terms have
    denominators that do not clear mod m, then derive a p-adic obstruction.
L5. (days) A rigorous statement for "decimal digit extraction from a degree-1 formula": the
    project result shows no such formula exists in base 10 for pi; add the consequence for
    Yap's framework: pi in Logspace in base 10 cannot be proved by Yap's method with a
    degree-1 formula. Small, but it explains exactly what is missing for BBP's question 1.
    [INFERRED]
L6. (out of reach / long) Prove Plouffe/Bellard/Gourdon-type decimal digit algorithms correct
    (carry control) and bound their space; needs Gourdon's text (not retrieved) and an
    irrationality-measure argument for pi in base 10 (Yap's argument adapts, [INFERRED]),
    but the algorithms' rounding analysis is not in the pages I read.

## 6. Overlap or conflict with section 1 of the rules file

- "In print this is stated as known (Bailey's Compendium, citing Borwein-Borwein-Galway 2004),
  but that paper proves only the Machin-type case": confirmed. The Compendium sentence (read)
  is "showed that there are no other degree-1 BBP-type for pi, except those ... whose base is a
  power of two"; the Borwein-Galway abstract (read) proves non-existence for b-ary Machin-type
  formulas for pi, b != 2. BBP 1997 preprint section 6 (read) also cites a reported proof by
  Buhler for the form with n^-k weights and denominators mk+j (n=2^K), without a published
  proof. So the project's "iff power of 2" goes beyond what is in print, but earlier
  unpublished Buhler claim is for a restricted shape; credit it.
- BBP preprint section 5 vs project's log-criterion: the print statement is Pomerance's remark
  that no (2^a-1)-quotient identity exists for 23 [READ]; project's result "log 23 has none
  in class F" is the stronger classification. The BBP Question 5 ("is log 23 in SC in base 2")
  remains open since "no formula of this type" does not give "not in SC". [INFERRED]
- Zudilin 2024 v1 (base 10 claim) conflicts with "none in base 10" only superficially: his
  formula has non-constant-rational coefficients (b_n from a recurrence) and v2 retracts it
  as flawed. No conflict with the project's theorem.
- 2/3 terms per bit vs print: Bellard 0.7, Euler 0.7; no print item claims better. No conflict.

## 7. Sources

- BBP preprint: https://www.davidhbailey.com/dhbpapers/digits.pdf
- Bailey 2006: https://www.osti.gov/servlets/purl/983322 ; Compendium:
  https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf
- Plouffe 1996/2009: https://arxiv.org/abs/0912.0303 ; Plouffe 2022: https://arxiv.org/abs/2201.12601
- Bellard: https://bellard.org/pi/pi_bin/pi_bin.html ; https://www.bellard.org/pi/pi_n2/pi_n2.html
- Yap: https://cs.nyu.edu/~exact/doc/pi-log.pdf ; Lipton:
  https://rjlipton.com/2009/03/15/cooks-class-contains-pi/ and
  https://rjlipton.com/2010/07/14/making-an-algorithm-an-algorithm-bbp/
- Allender et al.: https://arxiv.org/abs/1112.4295
- Zudilin: https://arxiv.org/abs/2409.10097 (v1 html, v2 pdf)
- Kristensen-Mathiasen: https://arxiv.org/abs/2208.07696 ; Barsky et al.: https://arxiv.org/abs/1906.09629
- Bertot-Magaud-Zimmermann: https://arxiv.org/abs/1709.01743
- Sze: https://arxiv.org/abs/1008.3171 ; Takahashi record page:
  https://www.hpcs.cs.tsukuba.ac.jp/~daisuke/pihex.html
- Borwein-Galway-Borwein 2004: doi 10.4153/cjm-2004-041-2 (abstract only)
- Craig-Wood 2023: doi 10.56031/2693-9908.1049 (abstract page only)
- Wikipedia: BBP formula, PiHex, Bellard's formula, Chronology of computation of pi
- y-cruncher records page: https://www.numberworld.org/y-cruncher/records.html (314T digits,
  Dec 2025; method page says verify by running BBP at the matching hex offset)
- OEIS A104885 (primes with binary BBP log formulas) appeared in an OEIS search (title only).

## Records (question 3), as read

| Year | Who | Formula | What | Cost |
|---|---|---|---|---|
| 1997 | Bellard | Bellard | 152 bits ending at bit 10^12 + 151 | 12 days, 20 workstations [READ Bailey, Sze] |
| 1998-99 | Percival, PiHex | Bellard | 5e12 bit, 4e13 bit | 13,500 and 84,500 CPU h [SNIPPET Wikipedia] |
| 2000 | PiHex | Bellard | quadrillionth bit = 0 (64 bits to 10^15+60) | 250 CPU-years (Bailey, Sze) vs "1.2 million CPU hours" (Wikipedia): discrepancy |
| 2010 | Sze (Yahoo) | Bellard (eq. 1.2) | 256 bits ending at bit 2e15+252 | 23 days, 503 CPU-years, 1000-node cluster [READ] |
| 2016 | Takahashi | Bellard | 32 hex digits from hex position 1e17 | 320.5 h, 512 Xeon Phi nodes [READ] |
| 2009-2022 | Bellard, Kondo, Trueb, Iwao, DAViS | Bellard, BBP | verification of long decimal runs via hex digits | 2021: 34 h for 62.8T; 2022: 12.6 h for 10^14 [SNIPPET: Wikipedia chronology, table partly garbled by the fetch tool] |
| 2025 | O'Brien et al. | not named | 314T decimal digits | verification 4.37 h (page does not say which formula) |

I did not find a BBP-type record above hex position 10^17 or a 2026 y-cruncher BBP record.

## Search log

WebSearch calls (6 allowed): 
1. BBP digit extraction lower bound complexity polylog space base 10
2. Gourdon "N-th digit computation" ...
3. Gourdon nthdecimaldigit.pdf ...
4. Chee Yap "Pi is in Log Space" ...
5. Takahashi "BBP-type formulas" ...
6. lower bound or optimality number of terms BBP-type formula ...

Endpoint and page fetches (fetch tool), numbered; (x) = failed or no content:
1 arXiv API all:"BBP formula"; 2 OpenAlex search "digit extraction pi BBP"; 3 Crossref Gourdon (429);
4 Semantic Scholar digit extraction (429); 5 arxiv.org/html 2409.10097v1; 6 Lipton 2009; 7 Wikipedia BBP;
8 Bailey digits.pdf; 9 arXiv 0912.1015 (irrelevant guess, discarded); 10 arXiv abs 2201.12601;
11 arXiv pdf 2201.12601; 12 numbers.computation nthdigits.html (x); 13 bellard pi_bin.html (404);
14-18 arXiv API queries: "nth digit" pi, "two quadrillionth", decimal digit transcendental, BBP+digit
extraction, Bailey-Borwein-Plouffe (all 429); 19-22 OpenAlex (400, bad select); 23 OpenAlex "two
quadrillionth bit of pi"; 24 OpenAlex "nth decimal digit transcendental Plouffe"; 25 OpenAlex "BBP type
formulas base 10"; 26 OpenAlex "rapid computation polylogarithmic constants"; 27-30 OpenAlex cites W2073085121
with title filters lower bound / complexity / digit / space; 31 OpenAlex "Pi is in Log Space";
32 arXiv abs 0912.0303; 33 OpenAlex cites ... decimal; 34 OpenAlex Distant Decimals; 35 cs.nyu pi-log-space.pdf
(404); 36 researchgate (403); 37 arXiv abs 1912.05319 (Sze fast pi, not relevant); 38 HAL (blocked);
39 cs.nyu yap/papers (404); 40 OpenAlex cites ... Pi; 41 OpenAlex Borwein-Galway abstract; 42 doi cloudcom
(redirect); 43-46 OpenAlex (429, rate limit lasting a day); 47 Crossref BBP computation verification;
48 zbMATH API "BBP digit extraction"; 49 arXiv abs 1008.3027 (wrong guess, irrelevant);
50 bellard.org/pi/pi_bin/; 51 numbers.computation nthdigit.html (x); 52 Semantic Scholar (429);
53-54 bellard pi_bin.html (twice); 55 Wikipedia Bellard's formula; 56 Wikipedia Chronology of pi;
57 bellard pi_n2.html; 58 arXiv pdf 1709.01743; 59 arXiv pdf 0912.0303; 60 crummy.com (404);
61-62 web.archive.org (blocked); 63 cs.nyu pi-log.pdf (Yap, read); 64 Lipton 2010; 65 arXiv 1112.4295;
66 arXiv abs 2409.10097; 67 Semantic Scholar citations (empty); 68 zbmath.org (403); 69 arXiv pdf 2409.10097v2;
70 Semantic Scholar (429); 71 erdosproblems.com (403); 72 osti 983322; 73 numberworld pi.html (404);
74 numberworld records; 75 Crossref Xeon Phi; 76 Crossref Hadoop (429); 77 Crossref Euler 1779;
78 doi Euleriana; 79 craig-wood.com; 80 pacific.edu page; 81 pacific.edu pdf (403); 82 GitHub repos
"BBP pi lean4" (0); 83 GitHub repos bellard bbp (0); 84 GitHub issues mathlib4 BBP pi (0);
85 OEIS "Bellard BBP" (null); 86 GitHub repos "pi bbp"; 87 arXiv API BBP+digit extraction (429);
88 OEIS "BBP formula"; 89 Bailey Compendium pdf; 90 numbers.computation piApprox (x);
91 Crossref rigorous error bound BBP; 92-93 Crossref (429); 94 Wikipedia Normal number; 95 Takahashi pihex page;
96 arXiv abs 2208.07696; 97 johndcook BBP post; 98 arXiv pdf 2208.07696; 99 cms.math.ca (404);
100 doi CJM Borwein-Galway (redirect); 101 arXiv abs 0807.0872; 102 Wikipedia Spigot algorithm;
103 arXiv pdf 1008.3171; 104 arXiv abs 2507.20428; 105 Huvent page (certificate error);
106 MathWorld BBP formula.

Totals: WebSearch calls = 6 (all used).
Endpoint/fetch queries = 106, of which about 55 returned usable content (many arXiv, OpenAlex, S2 and
Crossref calls were rate limited with HTTP 429). Search-endpoint queries proper (arXiv, OpenAlex,
Crossref, Semantic Scholar, zbMATH, OEIS, GitHub) = about 47.
Pages or PDFs read in substance: BBP preprint, Plouffe 1996, Plouffe 2022, Yap, Zudilin v1 and v2,
Bailey 2006, Compendium (partly), Bertot et al. (searched text), Kristensen-Mathiasen (intro and
Theorem 1), Sze 2010 (first pages), Bellard (both pages), Lipton (both posts), Takahashi page.
