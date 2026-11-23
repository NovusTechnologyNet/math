# W2-P14: Gibbons's conjecture (Monthly 2006) and correctness of spigot / digit-extraction algorithms for pi

Marking: [READ] read on the source's own page or PDF (PDFs converted with pdftotext and read
by me), [SNIPPET] seen only in a search result, abstract or API record, [INFERRED] my own
conclusion or computation. Several web pages went through a summarising fetch tool; those
are marked [READ via tool] where it matters. Some fetch results (OpenAlex, Semantic Scholar,
arXiv API) were HTTP 429 and gave nothing. No page contained instructions addressed to me.

## 1. Summary

1. Gibbons's Conjecture 1 is a single statement: in the Gosper-series streaming algorithm, if
   one strictly alternates "consume one series term, produce one digit", the safety test
   always succeeds (the two floors agree). Exact definitions are in section 2.1. [READ]
2. I checked it myself with exact integers: no violation for the first 20000 terms (Gibbons:
   1000; the earlier helper P13: 12000). The tightest case is n = 1 (slack 12.5 interval
   widths); for n >= 2 the smallest slack is 87.5 widths (n = 3). [INFERRED, own computation]
3. The conjecture is equivalent to a statement about the decimal digits of pi alone (section
   3.1): for every n, the interval of width about C n^(-3/2) (2/27)^n around pi contains no
   multiple of 10^-(n-1) except possibly an endpoint. Equivalent: the distance from 10^(n-1) pi
   to the nearest integer is at least about 10^(-0.1303 n) times a power of n, with a
   computable one-sided offset. [INFERRED]
4. So it is a genuinely Diophantine, "digit run" type statement: no run of 0s or 9s of length
   about 0.13 n starting at decimal place n. It does NOT follow from any irrationality measure
   of pi: even the optimal measure 2 only gives ||10^m pi|| >= 10^(-(1+eps) m), far weaker than
   the 10^(-0.13 m) needed. (For algebraic numbers Roth would give it; for pi nothing is known.)
   [INFERRED]
5. Heuristically it is almost certainly true (probability of a violation at step n is about
   C n^(-3/2) 10^(-0.13 n), summable) and it cannot be refuted from the known 3*10^14 digits
   of pi unless a run of 40 trillion zeros exists. Out of reach to prove; easy to prove
   conditionally. [INFERRED]
6. No proof, partial proof or discussion of the conjecture found after 2006 (Crossref, zbMATH,
   OEIS, GitHub, web searches, Oxford errata page). The only update is errata and a 2024
   corrected version; the paper's own text keeps "we have not been able to prove". [READ]
7. BBP: Yap 2010 ("Pi is in Log Space") needs only a finite irrationality measure K of pi (for
   dyadic denominators); with K and a BBP-like series the n-th bit is decided from about
   2(K-1)n+4 series terms. Explicit constants: Mahler's 1953 K = 42 is enough in principle
   (guard about 41 n bits); the 2020 record 7.1032 (and 2026: 7.1018) would give about 6.1 n
   bits if its threshold on q is made explicit, which I did not find. [READ / SNIPPET]
8. NEW and relevant: in Sept 2026 OpenAI posted a preprint claiming mu(pi) = 2 (ineffective:
   "for every exponent > 2 and all large q"), with a Lean repository covering the eventual
   inequality. If correct it gives K = 2+eps but non-constructively. Status: claimed, unreviewed
   by me beyond secondary reports. [READ secondary, SNIPPET]
9. Best lead: formalise the equivalence and a conditional theorem (conjecture follows from a
   stated digit-run hypothesis beyond an explicit N0, with the finite range checked by exact
   computation in the Lean kernel), and a verified piG with the safe test (productive and
   correct, needing only the Gosper series identity and irrationality of pi).

## 2. What is known

### 2.1 The conjecture, exactly [READ: author's PDF spigot.pdf, current corrected version]

Gosper's series (Gibbons eq. (6)): pi = 3 + (1*1)/(3*4*5) (8 + (2*3)/(3*7*8) (13 + ... ))
with i-th term 5i - 2 + i(2i-1)/(3(3i+1)(3i+2)) times the tail. Write j_i = 3(3i+1)(3i+2).
Each term is the Mobius map (linear fractional transformation)
  M_i(x) = (i(2i-1) x + j_i (5i-2)) / j_i,  matrix (i(2i-1), j_i(5i-2); 0, j_i),
increasing in x. Tail X_i (value of the series from term i on) lies in
  [a_i, b_i] = [(27i-12)/5, (675i-216)/125]   (width 84/125 = 0.672 for every i).
Streaming state: a matrix z (acting as 10^(k) times pi-minus-digits) and an index. Production
of digit y is z -> (10, -10y; 0, 1) z; consumption of term i is z -> z M_i. A digit is "safe"
when floor z(a) = floor z(b) (Gibbons writes the two points as (27i-12)/5 and (675i-216)/125,
with i the index of the next unconsumed term). The program piG tests safety; piG2 (strict
alternation: consume one, produce floor z(a), repeat, no test) and its optimised form piG3
(about 5 times faster, per Gibbons) are correct if and only if the test would never fail.

Conjecture 1 (suggested by C. Haenel; printed with definitions n, p, c, s, u_0 = (identity,1),
v_i = c(u_(i-1), x_i), y_i = n(v_i), u_i = p(v_i, y_i)): for all i >= 1, s(v_i, y_i) holds,
i.e. floor z(a) = floor z(b) for the state v_i reached after the i-th consumption in the
alternating run. Gibbons: not proved, verified for the first thousand terms; "perhaps some
diligent reader" could prove it. Errata (Oxford abstract page [READ via tool]): the matrix
product in p was the wrong way round, x in piG should be 27i-12, extr did not typecheck;
reprinted in "Pi: The Next Generation" (Springer 2016, pp. 245-257); a 2024 corrected version
exists. The index convention in the corrected paper is: after i consumptions the next-term
index is i+1, so the test points are a_(i+1), b_(i+1). [READ, and consistent with piG3's
start g(1,180,60,2).]

Independent restatement [INFERRED]: let T_n = M_1 ... M_n (increasing). The first n
consumptions and n-1 productions give a state whose value at x is 10^(n-1) T_n(x) minus
10 * floor(10^(n-2) pi) (when the earlier digits are the true ones). The n-th digit d_n is
floor(10^(n-1) T_n(a_(n+1))) reduced mod 10 (d_1 = 3 is the integer part). Conjecture 1 holds
for all n iff for all n:
  floor(10^(n-1) T_n(a_(n+1))) = floor(10^(n-1) T_n(b_(n+1))),
with the true digits all the way (induction on n: while it holds, the digits produced are
the digits of pi, because T_n(a) <= pi <= T_n(b)).

### 2.2 What was verified, precisely

- Gibbons 2006: first 1000 terms [READ].
- P13_computation.md (read by me): says it tested the recurrence (init (1,0,0,1), term
  (i(2i-1), j(5i-2), 0, j), next with x = 27i-12 divided by 5, safe test with x = 675i-216
  divided by 125), exact Python integers, and found the safe test holding for i = 1..12000,
  output beginning 3141592653589793238462643383279502884197. [READ the report; not re-run
  by me line for line, but my independent run (next item) agrees.]
- My own run [INFERRED, own computation, Python exact integers, gcd reduction, the piG3
  recurrence with the safe test attached]: no violation for n = 1..20000. I also measured,
  for each n, slack = min(distance of the lower end z(a) above its floor, distance of the
  upper end z(b) below the next integer), divided by the width w_n = z(b) - z(a): minimum
  over n >= 1 is 12.5 (n = 1), over n >= 2 it is 87.5 (n = 3); width in the 10^(n-1)-scaled
  units is 10^(-17.55) at n = 100, 10^(-136.35) at n = 1000, 10^(-397.73) at n = 3000, local
  slope about 0.1307 decades per step. The theoretical slope is log10(27/2) - 1 = 0.1303 plus
  a polynomial factor n^(-3/2) (the term ratio i(2i-1)/(3(3i+1)(3i+2)) = (2/27)(1 - 3/(2i) + ...)).
  The scripts are in the scratchpad (not kept in the repository).
- Beyond 20000 terms nothing was found in print. A heuristic bound (section 3.2) says a
  violation at any n > 200 would need 25 or more consecutive 0s or 9s in the decimal
  expansion of pi at place n; this is excluded for all places up to the known 3.14*10^14
  digits if the longest such runs in the computed digits are short [INFERRED: I did not
  scan the digits; the published statistics I know of say runs of that kind are absent, but I
  did not find a source in this pass, so treat as unchecked].

### 2.3 Related spigot literature [READ unless marked]

- Rabinowitz-Wagon 1995 (Monthly 102): bounded spigot, last digits may be wrong because of
  carries. Gibbons 2006 adds streaming, Lambert's continued fraction (piL: safe test
  required, consumes more than it produces) and Gosper's series.
- Arndt-Haenel, "Pi Unleashed" (2001), chapter "Spigot algorithms" (Crossref record) is the
  source Gibbons cites for the series. [SNIPPET]
- Gibbons's earlier "Streaming representation-changers" (2004) / "Metamorphisms" (Sci. Comput.
  Program. 2007): general correctness theory of streaming conversions (Crossref: 8 and 11
  citations) [SNIPPET]. The zbMATH review of the Monthly paper (R. Wegmann) praises the left
  to right method and the Haskell introduction; it mentions no proof of the conjecture
  [READ via tool].
- Rosetta Code "Pi" page: the C++ and Ada entries use Gibbons's spigot "based on the Gospers
  series" (plain safety-tested form); a bc entry remarks that fixed guard digits eventually
  fail because pi can contain arbitrarily long runs of 9s or 0s [READ via tool, partial
  page: first 100000 characters only].
- Citing works: searches for citations (Crossref, zbMATH, OEIS A000796 references, GitHub
  repositories, two web searches) found no paper proving or disproving Conjecture 1 and no
  Coq/Isabelle/Lean formalisation of any Gibbons algorithm. Not found is weak evidence.
- Bertot-Rideau-Thery (J. Autom. Reasoning, arXiv 1709.01743) [READ pdf text]: Coq BBP hex
  digit with the function NpiDigit, correctness stated only as partial correctness: if it
  returns a digit, the digit is right (computes lower and upper approximations, accepts when
  both agree). They say a long sequence of 0 (or F) may require very high precision, and
  that nothing guarantees termination. Millionth hex digit with 28 bits of precision (27 for
  two tests, 28 for the equality test) in under 2 minutes; billionth digit in 19 hours.
  They do not use an irrationality measure and do not discuss Gibbons.

### 2.4 Yap 2010 and the irrationality measure [READ]

C. Yap, "Pi is in Log Space" (preliminary version, 22 June 2010, cs.nyu.edu/~exact/doc/pi-log.pdf):
- Definition: K is an irrationality measure of alpha if 0 < |alpha - p/q| <= q^(-K) has only
  finitely many solutions; N(K) is a bound such that for all q >= N(K) the inequality
  |alpha - p/q| > q^(-K) holds. Key use is with q = 2^n: for 2^n >= N(K),
  distance(2^(n-1) alpha, Z) > 2^(-(K-1)n - 1).
- BBP-like series: terms t_k = 2^(-kc) p(k)/q(k) with fixed integer polynomials p, q, c >= 1.
- Theorem 1: a positive real with finite measure and a BBP-like series has its n-th bit
  computable in O(log |n|) space; Corollary: pi, pi^2, log 2 (measures cited: log 2 <= 3.575,
  pi^2 <= 5.442, pi <= 7.6804 in his text, which differs from Salikhov's published 7.606308,
  apparently a slip in the preliminary version).
- Algorithm: not the classical BBP: sum the terms k = 0..m exactly as bit arrays with
  m = max{7, 2(K-1)n + 4}, decide whether the fractional part of the truncated sum is >= 1/2;
  the guard is chosen so the tail 2^(n-1) R_m is below 2^(-(K-1)n - 2) = the measure gap. The
  predicate is decided by the carry sum column by column in O(log n) space.
- Remarks (Section 3): (a) the original BBP algorithm's SC status "remains open"; (b)
  irrationality measure is "highly non-constructive": even for explicit K the exceptional q
  below N(K) are not bounded, so the implicit constants in the O are unknown; (c) base 10:
  extensive search for BBP-like series unsuccessful, so unknown for base 10. [READ]
- Lipton's blog (rjlipton.com, 14 July 2010) [READ via tool]: BBP is only "correct with high
  probability" in the sense of carries; Yap's fix uses the measure; comments note that
  correctness without a bound on run length is only conditional on normality.

Bounds on mu(pi) [READ: Zeilberger-Zudilin PDF intro; SNIPPET for the table at teorth.github.io]:
Mahler 1953: 42; Mignotte 1974: 20.6; Chudnovsky 1982: 19.89 (table) or 14.65 (another
source; sources disagree); Hata 1993: 8.016; Salikhov 2008 (published 2010): 7.606308;
Zeilberger-Zudilin 2020: 7.103205334137 (Moscow J. Comb. Number Th. 9, 407-419, arXiv
1912.06345); Bai 2026: below 7.101862832357 (arXiv 2609.11276) [SNIPPET abstract]. The
Zeilberger-Zudilin introduction defines the measure with "all p, q with sufficiently large
q" and gives no explicit threshold. A search snippet (user-generated page) says Hata and
Salikhov exponents "can be made effective with absurdly large constants" and that no explicit
q0 was written down beyond Mahler [SNIPPET, low reliability].

### 2.5 The 2026 claim mu(pi) = 2 [READ secondary; SNIPPET]

- OpenAI preprint "The irrationality exponent of pi is 2", dated 24 Sept 2026, in the
  openai/math repository (preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026,
  README plus paper.pdf; I could read only the README, not the PDF) [READ via tool].
- Chudnovsky (arXiv 2610.28079, read pdf text) describes it: the proof combines weighted
  interpolation along logarithmic curves with a nonzero determinant; "proves an eventual bound
  for every exponent greater than 2, without asserting an effective denominator threshold";
  the public Lean scope covers the eventual approximation inequality and the supremum
  characterisation, not the Flint Hills series consequence; proof repository revision cited,
  endpoint lean/OAI/NumberTheory/PiExponent/Main.lean [READ pdf text].
- The docs file lean/docs/017.md (OpenAI math repository) states the scope: for every nu > 2
  all sufficiently large q give |pi - p/q| >= q^(-nu) [READ via tool]. Wikipedia and MathWorld
  list the result as unverified/with independent checks; Quanta (update page) mentions it
  among ten results released 6 Oct with reasoning traces and gives no verification status;
  a GitHub audit repository claims 869 of 869 Lean modules verified (self-reported)
  [SNIPPET]. Another table (teorth.github.io) does not mention it and still says mu(pi) = 2
  is conjectured. [READ via tool]
- I am not able to certify it. Treat "mu(pi) = 2, ineffectively" as claimed and plausible
  but not independently confirmed in this pass.

## 3. What kind of statement is the conjecture

### 3.1 Reduction to digit statistics of pi [INFERRED]

By the equivalence in 2.1, the conjecture asserts: for every n >= 1 the real interval
J_n = [T_n(a_(n+1)), T_n(b_(n+1))] (which contains pi, since T_n is increasing and the tail
X_(n+1) is in [a_(n+1), b_(n+1)]) contains no point of 10^(-(n-1)) Z in its interior or
upper endpoint (the lower endpoint may be on the grid). Its length is
  W_n = (b-a) * T_n'(...) ~ C n^(-3/2) (2/27)^n,
i.e. about 10^(-1.1303 n) (my numerics: slope 0.1307 per step after multiplying by 10^n).
Thus the conjecture is exactly

  (G)  for all n: pi is not within the specified asymmetric window of any decimal fraction
       p/10^(n-1) (window of size W_n, position fixed by the tail X_(n+1)).

A necessary condition for a violation at n is |10^(n-1) pi - N| < 10^(n-1) W_n for some
integer N, which means: the decimal digits of pi from place n on start with a run of about
0.13 n - O(log n) zeros or nines. A sufficient condition for no violation is
||10^(n-1) pi|| > 10^(n-1) W_n (the distance to the nearest integer larger than the width).
The statement does not mention pi's digits being "random", but it is exactly a quantitative
statement about them. The structure of the Gosper series gives no extra leverage: the
rational T_n(a_(n+1)) has a denominator of size n!-like, so its distance from the grid is
no better than the trivial bound 1/denominator, far below the width.

### 3.2 Which tools could give it

- Irrationality measure (Mahler 42, ..., 7.1032, even 2): |pi - p/q| > q^(-K) with q = 10^m
  gives ||10^m pi|| > 10^(-(K-1) m). We need exponent about 0.13 (or, for a uniform proof,
  anything below 1.1303 - 1 = 0.1303 in the exponent of ||10^m pi||). K - 1 >= 1 for every
  irrational (Dirichlet applies to all q, but along powers of ten the restricted measure is
  not even known to be below 2). So no measure bound, however good, proves (G).
  This is a statement about approximation by decimal fractions, of the same nature as
  "pi has no long runs of 0s or 9s": Roth's theorem gives it for algebraic irrationals;
  for pi nothing in the literature I found gives it. [INFERRED]
- Monotonicity or an invariant: the tail window [a_i, b_i] is an exact invariant for the
  series (proved in the paper) but the position of 10^(n-1) pi modulo 1 is not controlled by
  any recurrence. No monotone quantity separates the grid from J_n. [INFERRED]
- Probabilistic heuristic: if the digits behave like random digits, the chance that J_n
  contains a grid point is at most 2 * 10^(n-1) W_n ~ 2 C n^(-3/2) 10^(-0.1303 n); the sum
  over n > 200 is below 10^-20. So the conjecture is overwhelmingly likely, and a
  counterexample is essentially impossible to find; since the first violation could only
  occur beyond known digits, "not provable with known methods" is the right classification.
- The reverse implication: (G) for all n >= N0 implies pi has no digit run of length above
  0.1303 n + O(log n) after place n (up to the sign of the window offset), a nontrivial
  property that no existing theorem on pi's digits covers (normality is not proved; even
  under normality run lengths of order 0.13 n are not excluded by frequency statements).

### 3.3 What can be proved: guarded variants [INFERRED]

If, instead of strict alternation, one consumes k_n terms before producing digit n, safety
holds as soon as W_(k_n) * 10^(n-1) < ||10^(n-1) pi||. Using the effective measure K (for all
q >= 2): ||10^(n-1) pi|| > 10^(-(K-1)(n-1)), so it suffices that
  k_n >= (K (n-1))/(log10(27/2)) + O(log n) = K (n-1)/1.1303 + O(log n):
with Mahler K = 42: about 37.2 (n-1) terms; K = 20.6: about 18.2 n; with K = 7.1032 (if its
threshold q0 were explicit): about 6.28 n; with K = 2+eps (non-constructive): about 1.77 n.
All are far above the 0.885 terms per digit that piG3 uses in practice. So no provable
guarded version competes with the tested piG; the whole point of the conjecture is to
remove the test, and that is exactly the unproven digit-run statement. (The tested piG is
always correct, and always productive because pi is irrational; only its running time per
digit cannot be bounded a priori from known measures.)

## 4. BBP digit extraction: what bound is needed [READ Yap, Bertot; INFERRED for constants]

Two separate properties:
1. Soundness (never output a wrong digit): unconditional if the algorithm outputs a digit
   only when lower and upper approximations (with a rigorous tail bound) agree. This is
   Bertot et al.'s partial correctness lemma. No irrationality input needed.
2. Totality / bounded cost (a digit is always output, with guard length bounded in n):
   needs that ||b^n pi|| is not extremely small, i.e. a bound |pi - p/b^n| > b^(-K n) for
   all n (or n >= n0 plus a table). Yap's Theorem 1 uses exactly this with b = 2: one needs
   a finite K with an explicit threshold N(K) (all q >= N(K)), then
   guard m = 2(K-1)n + 4 terms (about (K-1)n bits of tail, or (K-1) n / 4 hexadecimal
   digits in base-16 grouping, ignoring the O(1)).
- Does the known measure suffice? Yes in principle for existence of an algorithm with a
  proved bound: any finite K. For explicit constants:
  - Mahler's K = 42 (1953) is explicit for all q >= 2 as far as the sources say (the
    Zeilberger-Zudilin introduction attributes the first bound 42 to Mahler; I did not read
    Mahler's paper to confirm "all q >= 2"; a snippet says one arXiv paper states the
    inequality for all p, q): for binary place m the guard is about 41 m bits; at hexadecimal
    place n (m = 4n) that is about 164 n bits. Constants fully explicit and uniform. [INFERRED]
  - Zeilberger-Zudilin's 7.1032 (and Bai's 7.1018): the proofs construct explicit integer
    linear forms, so an explicit threshold q0 should be extractable, but I found no
    written value; guard about 4 (K - 1) n = 24.4 n bits at hex place n. Effective status not
    stated [SNIPPET: "absurdly large but explicit"].
  - OpenAI's mu = 2: guard (1+eps) 4n bits but with an uncomputable threshold: gives
    existence of an O(n) bound for each fixed eps, not an explicit algorithm.
  - Baker route [INFERRED, not checked against the Lean statement]: the inhomogeneous form
    q*pi - p = -i q log(-1) - p is a linear form in logarithms with algebraic
    coefficients beta_1 = -i q, beta_0 = -p and alpha_1 = -1; Baker's inhomogeneous theorem
    (with beta_0 allowed) gives |q pi - p| > exp(-C log max(p, q)) with a huge but explicit
    C. If the imported formal Baker theorem in the project includes the inhomogeneous
    version, it yields a fully formal effective K (no table needed), with a large
    constant. Needs a check of what exactly was imported.
- Which formula matters: the argument is for every BBP-like series (Yap); the choice of
  base-16 BBP or Bellard or Huvent changes only c and the constants. Yap notes it does not
  settle the classical BBP algorithm itself (SC status "remains open").
- Not needed for the use in verifying record computations: there one just compares hex
  digits at a given offset; the soundness is checked per run (Bertot-type certificate).

## 5. What is open

1. Gibbons's Conjecture 1: stated open by the author (2006, and kept in the 2024 revised
   version per the Oxford page). Any proof requires a lower bound for ||10^m pi|| of
   exponential type 10^(-0.13 m): not stated as open in the literature in that form; this
   reformulation is mine.
2. Effective irrationality measure of pi with explicit q0 for the exponents below 20: not
   found (searched Crossref, web); Mahler's 42 and Mignotte's 20.6 appear in tables as
   effective-looking but I did not read the original papers. Open for me, not stated open.
3. Whether the 2026 OpenAI mu(pi) = 2 holds and whether it can be made effective: claimed;
   verification status unknown to me.
4. Classical BBP (as opposed to Yap's algorithm): proof that it runs in polynomial time and
   O(log n) space: stated open by Yap 2010 (SC status). With K effective it is also easy to
   formalise a guard-length version.
5. Whether pi has any BBP-type formula in a base that is not a power of 2: stated open by
   Zudilin 2024 and Yap 2010 (for base 10); relevant to the project's result "iff |b| is a
   power of 2" (no conflict, same as in P13).

## 6. Leads for this project, ranked

1. Formal reduction and conditional theorem for Conjecture 1.
   Exact statement (Lean): define the integer recurrence for piG2/piG3 (state q, r, t, i);
   prove (a) by induction, while the safe test holds the produced digits are the digits of
   floor(10^(n-1) pi); (b) Conjecture 1 for all n  <=>  for all n,
   floor(10^(n-1) T_n(a_(n+1))) = floor(10^(n-1) T_n(b_(n+1))) = floor(10^(n-1) pi);
   (c) a conditional theorem: if for all n >= N0 one has ||10^(n-1) pi|| >= 10^(-n/7)
   (or any exponent below 0.1303 + a margin; note 1/7 = 0.1429 suffices once n^(-3/2) is
   taken into account), then Conjecture 1 holds for n >= N0 (needs only the width estimate
   W_n <= C (2/27)^n, polynomial inequalities in n; project has done similar closed-form
   inductions); (d) the finite range n < N0 by exact integer evaluation with the kernel
   (a few thousand steps of numbers up to about 10^4 digits; my Python run took 7 s for
   n up to 8000, so a kernel check up to a few thousand is plausible without
   native_decide, and N0 can be taken small, about 300, because 10^(n/7) beats the n^(3/2)
   factor quickly; I did not check the constant).
   Fit: exactly the project's style (exact arithmetic, induction, inequalities); gives a
   precise "Gibbons's conjecture is equivalent to (G), and holds if pi has no digit run
   longer than n/7 at place n". Size: days to 2 weeks. Worth noticing: first mathematical
   analysis of the conjecture in print; clean statement; also tells Haskell users exactly
   what they are assuming.
2. Formally verified unbounded spigot for pi (piG with the safe test).
   Statement: the stream produced by piG equals the decimal digits of pi, and it is
   productive (every digit is eventually emitted). Needs (i) Gosper's series identity
   pi = sum_(n>=0) (50n - 6)/(binom(3n, n) 2^n) and its Mobius-composition form (not in
   Mathlib as far as I know; unchecked), (ii) the tail invariant X_i in [a_i, b_i] (an
   elementary induction by the paper), (iii) irrationality of pi (Mathlib has it I believe;
   unchecked) for productivity. Bertot et al. did BBP and AGM in Coq; nothing formal for
   spigots found. Size: 2-4 weeks. Notice: no formally verified unbounded spigot found
   in Coq/Isabelle/Lean searches (weak evidence).
3. Effective, formal digit-extraction totality via Baker or Mahler.
   Statement: |pi - p/q| > q^(-C) for explicit C and all q >= 2, derived from the imported
   Baker theorem (if it contains an inhomogeneous or "beta_0" version); then a Lean
   BBP/Huvent hex-digit function with guard m = C*n + O(1) and theorem "returns the correct
   digit for every n, no table, no ineffective constant". This is the missing totality
   part that Bertot et al. flag and Yap handles non-constructively. Size: 3-6 weeks if the
   import has the right form; otherwise out of reach (re-deriving Mahler's argument).
   Worth noticing: first formal BBP with a total correctness bound; overlaps the
   third-party Lean repository found by P13 (guard about 570 n + 1.8 million), which I
   did not inspect.
4. Heuristic / probabilistic note on the conjecture (small): the expected number of
   violations past n = 200 is below 10^-20; combined with lead 1 gives a precise statement
   of how far from provable it is. Size: hours.
5. Cross-check of the OpenAI preprint's claim for use in leads 3 and 4: only if the
   project wants constants: even mu = 2 is too weak for Conjecture 1 (section 3.2). Not
   recommended as a priority.

## 7. Overlap or conflict with the project's results

- None with section 1 of the rules file. The conjecture lives in decimal base 10 and in a
  Gosper-series (Mobius) setting; the project's classification statements concern BBP-type
  binary formulas. Related fact: Zudilin 2024 and Yap 2010 both say the existence of
  BBP-type formulas for pi in base 10 / bases other than powers of 2 is open; the project's
  iff statement answers it for degree-1 rational formulas.
- Possible tension to note: the new OpenAI claim (mu(pi) = 2) would settle the existence
  (not constructive) of Yap-type digit extraction with guard (1+eps)4n bits; it does not
  interact with the project's results.

## 8. Sources

- https://www.cs.ox.ac.uk/jeremy.gibbons/publications/spigot.pdf (paper, read via pdftotext)
- https://www.cs.ox.ac.uk/publications/publication1674-abstract.html (errata, versions)
- https://cs.nyu.edu/~exact/doc/pi-log.pdf (Yap 2010, read via pdftotext)
- https://rjlipton.com/2010/07/14/making-an-algorithm-an-algorithm-bbp/
- https://arxiv.org/pdf/1709.01743 (Bertot-Rideau-Thery, read via pdftotext)
- https://arxiv.org/pdf/2409.10097 (Zudilin 2024, read via pdftotext)
- https://arxiv.org/pdf/1912.06345 and https://arxiv.org/abs/1912.06345 (Zeilberger-Zudilin)
- https://arxiv.org/abs/2609.11276 (Bai 2026, abstract)
- https://arxiv.org/pdf/2610.28079 (Chudnovsky, describes the OpenAI preprint)
- https://github.com/openai/math (preprint folder and lean/docs/017.md)
- https://teorth.github.io/optimizationproblems/constants/7a.html (table of bounds)
- https://en.wikipedia.org/wiki/Irrationality_measure, https://mathworld.wolfram.com/IrrationalityMeasure.html
- https://www.quantamagazine.org/update/168664/
- https://en.wikipedia.org/wiki/Spigot_algorithm, https://rosettacode.org/wiki/Pi
- Crossref/zbMATH/OEIS/GitHub API result pages as listed in the log.
- Local scripts (scratchpad, not in the repository): conj.py, conj3.py (exact integer test).

## 9. Search log

WebSearch (5):
W1 Gibbons unbounded spigot algorithm pi Gosper series conjecture proof "Conjecture 1" Haenel
W2 Yap 2010 "BBP" digit extraction correctness irrationality measure of pi carry guard digits rigorous
W3 OpenAI 2026 proof irrationality measure of pi equals 2 effective constants
W4 Gibbons spigot "piG3" OR "Conjecture 1" Gosper series pi streaming without safety test proved OR proof OR counterexample
W5 effective irrationality measure of pi explicit q^{-42} Mahler Mignotte Chudnovsky Hata all integers q>=2 effective

Endpoint / page fetches (x = failed or empty):
1 Gibbons spigot.pdf (via fetch, then pdftotext of the saved file)
2 OpenAlex "unbounded spigot algorithms for the digits of pi" (x, 429)
3 Oxford publication1674 abstract page
4 arXiv API all:spigot AND all:pi (x, 429)
5 Crossref "Gosper series pi spigot streaming conjecture"
6 Semantic Scholar unbounded spigot (x, 429)
7 zbMATH "spigot algorithm digits pi"
8 GitHub repositories "gibbons spigot pi haskell"
9 Wikipedia Spigot algorithm
10 Crossref "Yap BBP digit extraction irrationality measure correctness"
11 zbMATH "BBP digit extraction irrationality measure pi"
12 GitHub repositories "spigot pi gosper haskell streaming"
13 OEIS search "Gibbons spigot" (x, 404 on first call; result page seen via the json call)
14 Crossref "BBP algorithm digit extraction pi rigorous carry propagation"
15 Crossref "Zeilberger Zudilin irrationality measure pi 7.103"
16 Crossref "Bailey Borwein Plouffe computation binary digits pi 1997"
17 Yap "Pi is in Log Space" PDF (read via pdftotext)
18 Lipton blog 2010
19 Zudilin arXiv 2409.10097 PDF (read via pdftotext)
20 arXiv abs 1912.06345
21 Wikipedia Irrationality measure
22 MathWorld Irrationality Measure
23 arXiv API search page (x, 404)
24 Quanta update page 168664
25 arXiv abs 2610.27799
26 arXiv abs 2609.11276
27 arXiv PDF 2610.28079 (Chudnovsky; read via pdftotext)
28 Crossref "The irrationality exponent of pi is 2"
29 GitHub repositories "irrationality exponent pi lean"
30 GitHub openai/math preprint directory
31 raw.githubusercontent openai/math lean/docs/017.md
32 Crossref "streaming algorithm digits of pi linear fractional transformations Gosper"
33 Crossref "Gibbons Streaming representation-changers metamorphisms"
34 zbMATH "Gibbons Jeremy unbounded spigot" (review text)
35 Bertot et al. PDF arXiv 1709.01743 (pdftotext)
36 Zeilberger-Zudilin PDF arXiv 1912.06345 (pdftotext)
37 Rosetta Code Pi page (first 100000 chars)
38 Williams College copy of spigot.pdf (x, certificate rejected)
39 Gibbons publications page (x, 403)
40 Crossref Mignotte (x, 429)
41 Crossref Mahler "On the approximation of pi"
42 Crossref "Lambert continued fraction pi spigot correctness Haskell" (x, 429)
43 Crossref "Bertot Gosper series spigot Coq Haskell streams"
44 raw.githubusercontent openai/math PiExponent.lean (x, 404)
45 teorth.github.io optimizationproblems 7a

Totals: WebSearch calls = 5. Endpoint / page fetches = 45 (about 36 returned usable content).
Local computation (not web): Python exact-integer test of Conjecture 1 to n = 20000 and
width/slack measurements; pdftotext on five downloaded PDFs.
