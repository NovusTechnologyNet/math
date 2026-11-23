# P10: continued fractions for pi and the Ramanujan Machine conjectures (22 Nov 2026)

Marking: [READ] = read on the source's page/PDF through the fetch tool (which returns an
extracted or summarized text, so tiny details of formulas may be garbled; I re-computed what I
could); [SNIPPET] = only a search result, abstract or API record; [INFERRED] = my conclusion;
[COMPUTED] = I ran it (sympy/mpmath, 60-80 digits, in the scratchpad).

## 1. Summary

1. The Ramanujan Machine (RM) list in the Nature paper (arXiv 1907.00205, tables of PCFs for
   e, pi, pi^2, zeta(3), Catalan G) is, as far as I can verify, almost entirely proved by 2026.
   Yamamoto (arXiv 2403.09729) proves 38 of them (all the pi^2 and G entries of degree (2,4),
   log 2, and several zeta values). 24/pi^2 is proved (Tonien, Math. Intelligencer 2026),
   8/(7 zeta(3)) is in Batut-Olivier and re-derived by Shvets, 12/(7 zeta(3)) by Shvets (2026).
2. What I could NOT find a proof for: 18/pi^2 (a_n = n(5n+6)+2, b_n = -4n^4+2n^3) and three
   e-entries (6e/(2e-3), 3/(4e-10), 4e/(2e-1)); "not found" only, not stated open by anyone.
3. The genuinely open list of 2026 is the "Ramanujan Challenge for AI" (arXiv 2607.09721, 27 Jun
   2026): only TWO stated open problems (a knot-polynomial integral for pi^2-type value, and
   gcd(d_n a_n, d_n b_n) = e^{o(n)} for Apery's zeta(3) sequences). Neither is a pi CF.
   The same paper's "proved but hidden" items include a PCF for pi: value 6/(3-pi)
   with a_n = -220n^3-484n^2-301n-42, b_n = 4n^2(2n+1)^2(5n-4)(5n+6) [COMPUTED: matches].
4. Other open items: "factorial reduction" (gcd of convergents collapses factorial growth to
   exponential) is itself only an observed property, stated by its authors as a conjecture;
   three degree-5 PCFs with unidentified limits; uniqueness of the conservative matrix field per
   constant.
5. Regular CF of pi: nothing proved about partial quotients beyond what follows from
   irrationality measure mu(pi) <= 7.1032 (Zeilberger-Zudilin 2020). Unbounded? Khinchin?
   Every integer appearing? all open.
6. Proof methods: (a) reduce to a 2nd-order recurrence and find a hypergeometric solution
   (Petkovsek) then Lemma 3.1 of Yamamoto (CF = telescoped series); (b) generating function /
   hypergeometric ODE; (c) Apery limits via modular forms (Shvets 2026); (d) Bauer-Muir
   transform; (e) Euler's CF-series transformation. sympy rsolve_hyper finds no hypergeometric
   solution for 8/pi^2, 18/pi^2, 24/pi^2 [COMPUTED], so route (a) is not universal.
7. Lean/Mathlib: GenContFract exists with convergents, determinant formula, error bounds for
   the REGULAR CF of a real; no convergence theory for generalized CFs (no Pincherle, Worpitzky,
   Seidel-Stern), no Brouncker/Lange/RM identity. A PR "Euler's continued fraction" is listed.
   I found no Lean formalization of any RM identity.
8. Best leads: formal Lean proofs of Yamamoto-type identities (days for the Petkovsek ones,
   weeks for 8/pi^2), Brouncker's 4/pi via Euler transform from Leibniz (days-weeks), and a
   cheap exact computation of gcd(p_n,q_n) data for factorial reduction.
9. No overlap or conflict with the project's BBP results (CF and BBP worlds are separate).

## 2. What is known

### 2.1 The RM tables and their proof status

- [READ] The Nature paper (arXiv 1907.00205, ar5iv text) says: conjectures labeled "known"
  (in the literature), "new and proven" (proved after posting), "new and unproven" (at time of
  writing). It says community members proved all formulas of the first manuscript within months,
  and a group around Zeilberger proved and generalized part. Algorithms: MITM-RF (hash table on
  one side, 10-digit prefilter) and Descent&Repel (gradient descent with repulsion plus lattice
  step). Convergence classes: deg b = 2 deg a exponential; deg b < 2 deg a superexponential;
  deg b > 2 deg a polynomial. Conjecture formulas verified to 2000 digits.
- [READ via ar5iv extraction] Entries listed there (CF = a_0 + b_1/(a_1 + b_2/(a_2 + ...))),
  status as in the paper (v3):
  pi, proved: 4/(pi-2) [2n+3, n(n+2)]; 8/(3pi-8) [2n+5, n(n+4)]; 2/pi [3n+1, -n(2n-1)];
  2/(pi-2) [3n+2, -n(2n-1)]; 1+pi/2 [3n+3, -(n+1)(2n-1)]; and 9 more of degree (1,2).
  pi^2, "unproven" then: 8/pi^2 [3n(n+1)+1, -(2n-1)n^3]; 16/(4+pi^2) [3n(n+1)+1, -2n^4+3n^3];
  24/pi^2 [7n(n+1)+2, 8n^4]; 18/pi^2 [n(5n+6)+2, -4n^4+2n^3]; 16/(pi^2-4)
  [n(3n+7)+3, -(n+1)^2(n+3)(2n+1)]; 32/pi^2 [n(3n+7)+3, -n^2(n+2)(2n-3)]; 16/(pi^2-8)
  [n(3n+11)+9, -n(n+2)^2(2n-1)]; 16/(12-pi^2) [n(3n+11)+9, -n(n+2)^2(2n+1)];
  32/(32-3pi^2) [n(3n+15)+15, -n(n+2)(n+4)(2n+1)]; (16+3pi^2)/(16-pi^2)
  [n(3n+9)+7, -(n+1)^3(2n-3)]; 18/(pi^2-8) [n(5n+14)+10, -2n^3(2n+3)].
  zeta(3), unproven then: 8/(7 zeta(3)) [(2n+1)(3n(n+1)+1), -n^6];
  12/(7 zeta(3)) [(2n+1)(5n(n+1)+2), -16n^6]. Catalan, unproven then: 2/(2G-1)
  [n(3n+7)+3, -2n^3(n+2)]; 4/(6G-5) [n(3n+11)+9, -2n^2(n+2)^2]; 6/(17-18G)
  [n(3n+13)+13, -2n(n+1)^2(n+3)]. e, unproven then: 6e/(2e-3), 3/(4e-10), 4e/(2e-1)
  (a, b polynomials of degree (2,3); my re-computation of 3/(4e-10) with the transcribed
  data fails, so that row is probably garbled by the fetch tool).
  Caveat: the extraction may misprint signs; I re-checked numerically 8/pi^2, 24/pi^2,
  18/pi^2, 8/(7 zeta 3), 12/(7 zeta 3), 6e/(2e-3), 4e/(2e-1) to 60 digits [COMPUTED].
- [READ] Yamamoto, arXiv 2403.09729 (PDF read): proves 38 conjectures. Theorem 2.1:
  CF[n(n+a)(n+b)... , -2n(n+a)(n+b)(n+c)...] = 4/ (sum over n of 2^n ... ) via the hypergeometric
  ODE; Theorem 2.2 gives a contiguity recurrence in the shift; Corollaries 2.1-2.22 are all the
  Catalan entries (1/(2G), 2/(2G-1), 24/(18G-11), 4/(6G-5), 6/(17-18G), ...); Corollaries
  2.23-2.30 give 8/pi^2, 16/(4+pi^2), 16/(pi^2-4), 32/pi^2, 16/(pi^2-8), 16/(12-pi^2),
  32/(32-3pi^2), (16+3pi^2)/(16-pi^2); Cor 2.23 (8/pi^2) was already proved by a prior source
  (his ref [9], Thm 3); Cor 2.31 is log 2. Section 3 (Petkovsek): 7 more, e.g. Thm 3.1
  CF[5n^2+14n+10, -2n^3(2n+3)] = 18/(pi^2-8) (solution y_n = 2^n n! (2n+3)!!), Thm 3.2
  CF[3n+3, -2n^2] = 1/(2 log 2 - 1), Thm 3.3-3.7 for combinations of zeta(2),(3),(4),(5),(7)
  with b_n = -n^8, -n^10, -n^14 and hypergeometric y_n = (2n+1)(n!)^4, (3n^2+3n+1)(n!)^5, ...
  Method: CF = limit A_n/B_n; given a solution y_n of the recurrence, Lemma 3.1 gives
  CF = (a_0 - y_1/y_0 ... ) via a series sum (-1)^k prod b_i /(y_k y_{k+1}).
- [READ] Tonien, Math. Intelligencer 48(3), Sept 2026, pp. 222-227: "Franel Numbers and a
  Continued Fraction Conjecture Discovered by the Ramanujan Machine"; a web-search snippet says
  its Theorem 1 proves the 24/pi^2 identity and that most RM formulas remain unproven [SNIPPET
  for the last clause; I think "most" refers to the RM's later, larger database].
- [READ] Shvets, arXiv 2604.06239 (preprint, single author, not refereed): Domb Apery limit
  B_n/D_n -> (7/24) zeta(3) and sum 64^n/(n^3 D_n D_{n-1}) = (56/3) zeta(3), hence
  conjecture Z2 = 12/(7 zeta(3)). arXiv 2604.14219: level-8 Apery limit B_n/s_n -> 7 zeta(3)/32;
  says PCF((2n+1)(3n^2+3n+1), -n^6) = 8/(7 zeta(3)) (the RM entry "Z1") is in Batut-Olivier
  and the limit was proved by Golyshev (Beukers's Atkin-Lehner method). Zenodo 19504666
  claims a uniform Eichler-integral proof for all three known sporadic Apery limits in Q zeta(3).
  Zenodo titles (not read in full) also claim "all cubic/sextic RM conjectures for zeta(3)".
- [READ] Wang, arXiv 2602.03027 (v3, Mar 2026): analytic proof of 8/pi^2 = 1 + K(a_n/b_n),
  b_n = 3n^2+3n+1, a_n = -(2n-1)n^3, via the (arcsin)^2 binomial series and Pincherle; a fetch-tool
  review lists gaps (overstated Pincherle iff, minimality not checked) but says the closed forms
  A_n, B_n already give the limit. Wang, arXiv 2601.08461: "rigorous" proof of -pi/4 CF
  (b_n = -(3n-2), a_n = -(n-1)(2n-5)); the same review lists real gaps (no Lean, claimed
  equivalence between a_n and a rescaled sequence not shown). Treat both as unrefereed.
- [SNIPPET] Brier-Naccache-Yifrach-Stav, arXiv 2211.01058: an algebraic observation explaining
  many RM relations and generating infinitely many (automatic proof of many, not all).
  Dougherty-Bliss and Zeilberger (Ramanujan J. 61, 2023): automatic conjecturing and proving
  of infinite families of CF values [SNIPPET, crossref metadata only]. Kures (Math. Intell.
  44, 2022) note on 8/pi^2 [SNIPPET]. Chen-Liu (Mathematics 2025): Bauer-Muir transform covers
  RM conjectures for pi and log 2 with quadratic numerators [SNIPPET]. Kadyrov et al. (2025):
  new log 2 PCFs [SNIPPET].
- [READ] Further RM-group papers: Elimelech et al., arXiv 2308.11829 (conservative matrix
  fields, CMF, distributed factorial reduction algorithm on BOINC, unifies thousands of
  formulas, new irrationality-type proofs); Ben David et al., arXiv 2111.04468 / Arnold Math. J.
  10 (2024): Apery's method extended to general PCFs, convergence rates and irrationality
  measure bounds for RM PCFs [abstract read]; Weinbaum et al., arXiv 2507.08138 (CMF, continuous
  asymptotics; conjectures) [abstract read]; Raz et al., arXiv 2502.17533 ("From Euler to AI":
  385 validated formulas for pi from 455,050 arXiv papers, 360 linked, 166 derived from one
  object) [abstract read]; Ramanujan Library, arXiv 2412.12361 (PSLQ-built hypergraph; 75 new
  relations; formulas linking pi and e) [abstract read].
- [READ] Challenge paper arXiv 2607.09721, problems 2.1-2.8 are proved-but-hidden, including
  2.1 (PCF for pi: a_n = -220n^3-484n^2-301n-42, b_n = 4n^2(2n+1)^2(5n-4)(5n+6) = 6/(3-pi);
  value garbled in extraction but I identified it by PSLQ [COMPUTED]); 2.2 gamma as Apery limit;
  2.3 pi+e as Apery limit; 2.4 harmonic-number series; 2.5 Catalan 3x3 matrix product;
  2.6/2.7 zeta(2)+zeta(3); 2.8 10005/pi.

### 2.2 Classical CFs for pi and the regular CF

- [READ, MathWorld] Brouncker (1655): 4/pi = 1 + 1^2/(2 + 3^2/(2 + 5^2/(2 + ...))); convergents 1,
  3/2, 15/13, 105/76. Stern (1833): pi/2 = 1 - 1/(3 - 2*3/(1 - 1*2/(3 - ...))).
  [READ, Wikipedia] arcsine-derived pi = 4/(1 + 1^2/(3 + 2^2/(5 + 3^2/(7 + ...)))) converges
  linearly; Nilakantha-derived pi = 3 + 1^2/(6 + 3^2/(6 + 5^2/(6 + ...))). Lange's
  "An elegant continued fraction for pi" is Amer. Math. Monthly 106 (1999) [crossref record];
  I did not read its content, so the exact attribution of the 6-series to Lange is
  [INFERRED] (recalled, not verified). Lambert's tan x CF gave the first irrationality proof.
- [READ, MathWorld/OEIS] Regular CF of pi: 653.52 billion terms computed (M. Frank, 1 Nov
  2025); largest term among them 845,188,380,288. The geometric-mean (Khinchin) and
  q_n^{1/n} (Levy) limits are not rigorously established. OEIS A001203 states no conjecture.
- [READ, Wikipedia] Khinchin's constant property is not proven for pi (nor gamma), indeed not
  for any real "not constructed for the purpose"; pi cannot have a periodic CF (transcendental).
- [READ] mu(pi) <= 7.103205334137... (Zeilberger-Zudilin, arXiv 1912.06345; Moscow J.
  Comb. Number Theory 2020; improves Salikhov's 7.6063).
  [INFERRED, standard] Consequence: for large n, a_{n+1}(pi) < q_n^{5.1033+eps} (since
  |pi - p_n/q_n| ~ 1/(a_{n+1} q_n^2) and mu - 2 = 5.1032). That is the only bound known on the
  partial quotients (growth upper bound); no lower bound, no boundedness, no unboundedness.
- Normality of pi is unproven [READ, Wikipedia].

### 2.3 Proof methods for PCF identities

- Euler-Wallis recurrence A_{n+1} = a_n A_n + b_n A_{n-1}; equivalence transformation
  (scale partial quotients by c_n); Euler's CF formula turning a sum into a CF
  a_0 + a_0a_1 + ... = a_0/(1 - a_1/(1+a_1 - a_2/(1+a_2 - ...))) [READ, Wikipedia]; determinant
  A_{n-1}B_n - A_nB_{n-1} = (-1)^n prod b_i [READ]. Pincherle: CF converges iff the recurrence
  has a minimal solution [textbook; Wang uses it].
- Yamamoto's two routes (above) [READ]: generating function plus ODE (hypergeometric), and
  Petkovsek's hypergeometric-solution algorithm plus Lemma 3.1.
- Apery-like and modular: limits of B_n/A_n as periods of weight-4 Eichler integrals
  (Shvets 2026, Beukers/Golyshev Atkin-Lehner) [READ abstracts].
- WZ pairs: Apery limits and WZ (Experimenting with Apery Limits and WZ pairs, 2021;
  Zeilberger-Zudilin's "Automatic discovery of irrationality proofs", 2020) [SNIPPET].
- Factorial reduction [READ, arXiv 2308.11829 Section 2.1]: p_n, q_n grow like (n!)^d but
  p_n/g_n, q_n/g_n, g_n = gcd(p_n, q_n), grow at most exponentially. Found in every RM formula
  and every classical CF checked by the authors; rare in general (a lower-dimensional
  subspace); the Apery PCF for zeta(3) is the one in its family with it. The authors call the
  search algorithm "itself based on a conjecture".

### 2.4 Formalization

- [READ, Mathlib docs] Mathlib.Algebra.ContinuedFractions: structures Pair, GenContFract,
  SimpContFract, ContFract; nextConts/convs/convs'; for the regular CF of a real v:
  |v - A_n/B_n| <= 1/(B_n B_{n+1}), Fibonacci lower bound on denominators, convergence in
  ApproximationCorollaries; terminates iff rational. Page has no theorem on convergence of
  general (a_n, b_n) CFs, no analytic CF theory.
- [READ, GitHub API] mathlib4 PRs: #37997 generalize determinant formula to GenContFract
  (merged); #38214 "add Euler's continued fraction" (euler, GenContFract.toEuler; the API shows
  merged_at null though the title says merged); #43281 Hurwitz approximation theorem (merged);
  #44131 lower bound on convergent error (closed); #39212 open. I found no issue/PR for
  Brouncker, Lange, Pincherle, Worpitzky, Stern-Stolz, or the RM conjectures; GitHub code search
  was refused (401), so "not found" is weak.
- [READ] github.com/laichunwing/Tom_Lai_Machine (created 2026-07-10, 0 stars): "automated
  proof generation for PCF conjectures of the RM"; Python, no README read. No Lean repo found.

## 3. What is open

(Each marked: stated open by the source, or only not found by me.)

O1. [Stated open, Challenge 3.2] For Apery's zeta(3) sequences (n+1)^3 u_{n+1} - (34n^3+51n^2+
    27n+5)u_n + n^3 u_{n-1} = 0, a_0=0, a_1=6, b_0=1, b_1=5, d_n = lcm(1..n)^3:
    gcd(d_n a_n, d_n b_n) = e^{o(n)} (Apery's irrationality-measure bound is tight for his data).
O2. [Stated open, Challenge 3.1] The Godbillon-Vey-type integral of log x dy/y - log y dx/x over
    the A-polynomial curve of knot 7_2 between two real roots equals 42 pi^2/85 (value
    "pi^2" per extraction, the 42/85 coefficient read from the text; garbled symbols; read
    the PDF to confirm).
O3. [Stated by authors as conjecture] Factorial reduction holds for every PCF converging to a
    classical constant; more specifically, every PCF whose reduced convergents grow
    exponentially converges to a "mathematical constant". No proof even for a single infinite
    family beyond Apery-type ones [INFERRED].
O4. [Stated open] CMF paper Table 1: six degree-5 PCFs with b_n = -n^10 or -64 n^10, of which
    three have limits found by PSLQ as combinations of zeta(5), zeta(3), and three have
    unidentified numerical limits 1.20426..., 2.45174..., 22.8410... (no closed form known).
    E.g. a_n = 8(n^5+(n+1)^5) + 20(n^3+(n+1)^3) - 5(2n+1), b_n = -64n^10 is among them
    (which row maps to which number is garbled in my extraction).
O5. [Stated open] Does each constant have a unique CMF; what is the maximal dimension per
    constant; do 2x2 CMFs exist for all polynomial degrees (only up to degree 3 shown);
    is there a CMF for zeta(5)? (arXiv 2308.11829 Section 4.3 and 3.6).
O6. [Classical open] Irrationality of zeta(5), of Catalan's G; CMF paper says "long-standing
    open question" for zeta(5).
O7. [Not found, not claimed open] 18/pi^2 = CF[n(5n+6)+2, -4n^4+2n^3] and the e entries
    6e/(2e-3) = CF[n(n+6)+7, -(n+3)n^2], 4e/(2e-1) = CF[n(n+3)+3, -(n+2)n^2],
    3/(4e-10) (as transcribed, fails numerically). I found no proof in the sources read.
    Numerically true at 60 digits for the first three [COMPUTED].
O8. [Stated by source as conjectures, not read] New conjectures in Ben David et al. 2024 on
    irrationality measures of RM PCFs, and in Weinbaum et al. 2025 on CMF asymptotics.
O9. [Open, classical] Regular CF of pi: (i) are the a_n bounded (conjecturally no)? (ii) do
    Khinchin's constant and Levy's constant govern the geometric means and q_n^{1/n}?
    (iii) does every positive integer occur as a partial quotient? (iv) is pi normal? (v) a
    lower bound for the sup of a_n; (vi) lower irrationality measure bounds (mu(pi) >= 2 is
    all that is known, the upper bound is 7.1032). All stated unproven in MathWorld/Wikipedia;
    I did not find a source stating (iii) as a formal problem beyond the empirical table
    (smallest missing integers 49004, 50471, ... in the first 1.5e10 terms) [READ].
O10. [Not found] Any list of exactly which RM-website conjectures remain open in 2026: the
    site's results pages returned 404/redirects; I could not obtain a current table.

## 4. Leads for this project, ranked

L1. Formal proofs in Lean of Yamamoto-type identities (the Petkovsek family). Exact
    statement: for y_n hypergeometric solution of y_{n+1} = a_n y_n + b_n y_{n-1}, y_n != 0,
    prove (general Lemma) CF[a_n,b_n] = a_0... = limit and instantiate with
    CF[3n+3, -2n^2] = 1/(2 log 2 - 1) (y_n = 2^n (n+2) n!, series sum 2^{-k}/((k+1)(k+2)(k+3))
    elementary with Mathlib's log 2 series) and
    CF[n^4+(n+1)^4+2(n^2+(n+1)^2), -n^8] = -1/(zeta(4)+4 zeta(2)-8) (y_n = (2n+1)(n!)^4; telescoping
    partial fractions; Mathlib has zeta(2), zeta(4)). Why the toolkit fits: finite algebra
    (ring/field_simp), convergence by telescoping, zeta values present. Missing: a general
    theorem that CF value = limit of A_n/B_n for non-regular CFs (about 200 lines; the
    determinant formula is already in Mathlib), plus the pi connection is weak. Size: days
    each. Worth noticing: first machine-checked RM identities; nothing found in Lean.
L2. Formal proof of 8/pi^2 = CF[3n^2+3n+1, -(2n-1)n^3] (also 4/pi-type ones). Statement:
    A_n/B_n -> 8/pi^2 with explicit A_n, B_n (partial sums of sum_m 2^m/(m^2 binom(2m,m)))
    and the Lehmer identity sum 2^m/(m^2 binom(2m,m)) = pi^2/8, i.e. 2 arcsin^2 (1/sqrt 2).
    Fit: recurrence check is algebra; Mathlib has arcsin and Wallis-type machinery but I did
    not find the series of arcsin^2 (would need an ODE or Taylor argument; weeks). Existing
    proofs: Yamamoto Cor 2.23 (via the 1/(2n+1)^2 sum), Wang 2026 with noted gaps; a formal proof
    would also settle Wang's loose points. Size: 2-4 weeks. Noticed because pi-related and
    machine checked.
L3. Brouncker and the Euler transform in Lean. Statement: 4/pi = 1 + 1^2/(2 + 3^2/(2 + ...))
    from Leibniz's series via the series-to-CF identity (a_0 + a_0a_1 + ... as above;
    Mathlib has the Leibniz series and #38214 has the Euler-CF object). Fit: Euler formula is
    a finite telescoping identity plus a limit. Size: days to 2 weeks. Worth noting: a classical
    CF for pi (and then Stern/Nilakantha variants) formalized; no Lean source found.
L4. Cheap exact computation of factorial reduction data (24 cores, exact integers): for the
    RM PCFs for pi, pi^2, G, zeta(3) compute g_n = gcd(p_n, q_n) to n ~ 10^4 and fit
    log g_n / (n log n) and the prime-by-prime valuation pattern; test the conjecture that
    v_p(g_n) follows a Kummer/Lucas-type rule, then prove it for one family. Why: arithmetic
    structure is the core of both factorial reduction and O1. Size: days for data, weeks for a
    theorem on one family. Worth noticing: the property is an unexplained observation for 5 years.
L5. Settle O7 by recurrence plus computer algebra: for 18/pi^2 and the three e entries find a
    proof via contiguous relations or the generating function route of Yamamoto, or via a
    Bauer-Muir transform to an already-proved CF. Test: sympy rsolve_hyper returned no
    hypergeometric solution for 8/pi^2, 18/pi^2, 24/pi^2, 12/(7 zeta 3) recurrences
    [COMPUTED], so Petkovsek alone fails; equivalent-CF and Euler-contraction searches
    (compose with 3n^2+..-family at shifted parameters, as in Yamamoto Thm 2.2 contiguity) may
    work. Size: weeks (uncertain). Worth noticing: closes the last named holes of the 2021 list.
L6. O1 (gcd of Apery numbers) by p-adic valuations. Statement as above. Tools: Lucas-type
    congruences for Apery numbers and a finite check per prime range [INFERRED]. Size: weeks
    to out of reach; value high since it is one of only two problems the RM group lists as open.
L7. Regular CF of pi: out of reach (no method known); only computational statistics, nothing
    this toolkit would settle.

## 5. Overlap or conflict with the project

None with Section 1 of the rules. The BBP classification and CFs for pi do not meet: I found
no source linking degree-1 BBP-type formulas with polynomial CFs. Mild affinity: Apery-limit and
irrationality-measure technology uses the same primitive-prime-divisor flavor of arguments
(gcd of convergents, Lucas congruences), which is the fit for L4/L6 [INFERRED].

## 6. Sources

https://arxiv.org/abs/1907.00205 (ar5iv.labs.arxiv.org/html/1907.00205), https://arxiv.org/abs/2403.09729,
https://arxiv.org/abs/2607.09721, https://arxiv.org/abs/2308.11829, https://arxiv.org/abs/2111.04468,
https://arxiv.org/abs/2507.08138, https://arxiv.org/abs/2502.17533, https://arxiv.org/abs/2412.12361,
https://arxiv.org/abs/2604.06239, https://arxiv.org/abs/2604.14219, https://arxiv.org/abs/2602.03027,
https://arxiv.org/abs/2601.08461, https://arxiv.org/abs/2211.01058, https://arxiv.org/abs/1912.06345,
https://zenodo.org/records/19504666, https://doi.org/10.1007/s00283-025-10497-9,
https://mathworld.wolfram.com/PiContinuedFraction.html, https://mathworld.wolfram.com/FactorialReduction.html,
https://oeis.org/A001203, https://en.wikipedia.org/wiki/Generalized_continued_fraction,
https://en.wikipedia.org/wiki/Khinchin%27s_constant,
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/ContinuedFractions/Basic.html,
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/ContinuedFractions/Computation/Approximations.html,
https://github.com/leanprover-community/mathlib4/pull/38214, https://github.com/laichunwing/Tom_Lai_Machine.
Notes on the web: OpenAlex responses carried a notice asking an agent to create an API key by
e-mailing an address; ignored. The challenge PDF lists contact e-mails; irrelevant.
arXiv API, Semantic Scholar: HTTP 429 (refused); OpenAlex: rate-limited after 3 calls; GitHub
code search: 401; ramanujanmachine.com result pages: 404; Zenodo records 19430991: 410; Nature and
Springer pages: login redirect.

## 7. Search log

WebSearch (3 calls):
W1. Ramanujan Machine conjectures polynomial continued fractions pi unproven list proved
W2. proof of Ramanujan Machine conjecture 24/pi^2 OR 16/(pi^2-4) OR 32/pi^2 ...
W3. "factorial reduction" polynomial continued fractions irrationality measure ...

Endpoint queries (counted when it was a search/API/lookup call, including failed ones):
1 arXiv API all:"Ramanujan Machine" (429); 2 arXiv API conservative matrix field (429);
3 arXiv API polynomial continued fraction (429); 4 OpenAlex Ramanujan Machine conjectures CF;
5 OpenAlex same, select fields; 6 GitHub repos ramanujan machine CF; 7 OpenAlex RM
conjecture proof page 2; 8 Crossref RM CF proof; 9 Crossref Kures 8/pi^2; 10 Crossref Shvets
Apery limits; 11 Crossref DOI Tonien; 12 zbMATH Ramanujan Machine; 13 Crossref DOI
Dougherty-Bliss-Zeilberger; 14 Crossref Lange elegant CF pi; 15 GitHub issues GenContFract
(mathlib4); 16 OEIS A001203; 17 Semantic Scholar (429); 18 Semantic Scholar (429); 19 OpenAlex
Apery Eichler (429); 20 GitHub issues irrational pi (mathlib4); 21 GitHub issues CF
Pincherle/Worpitzky; 22 GitHub repos lean4 continued fraction; 23 GitHub code Ramanujan Machine
lean (401); 24 GitHub code irrational_pi (401); 25 OEIS Ramanujan Machine; 26 zbMATH
polynomial CF Apery limit; 27 Crossref Apery limits experiments and proofs; 28 arXiv API
ti:continued fraction + RM (429); 29 Crossref DOI Ben David et al.; 30 Crossref DOI
Bauer-Muir; 31 Crossref DOI log 2 PCF; 32 Crossref DOI Lynch derangements; 33 Crossref CF
conjecture RM e proof Zeilberger; 34 Crossref Naccache Yifrach-Stav; 35 zbMATH CF pi Brouncker
Lange (404); 36 Crossref irrationality measure pi; 37 OEIS Brouncker CF pi; 38 zbMATH
irrationality measure pi; 39 Crossref WZ CF Apery; 40 GitHub issues Wallis/Brouncker mathlib4;
41 Crossref Gosper continued logarithm; 42 GitHub API PR 38214; 43 GitHub API repo Tom_Lai_Machine;
44 Zenodo API 19696993; 45 Zenodo API 20527726; 46 Zenodo API 20431177; 47 Zenodo API 19430991
(410); 48 Zenodo API 19504666 page.
Totals: WebSearch 3; endpoint queries 48 (of which about 12 failed with 429/401/404/410).
Pages and PDFs read (besides records): ar5iv 1907.00205 (twice), Yamamoto PDF (full),
Challenge PDF (full), CMF PDF 2308.11829 (sections 2, 3.6, 4.3), arXiv abstract/html pages of
2403.09729, 2601.08461, 2602.03027, 2604.06239, 2604.14219, 2507.08138, 2412.12361, 2502.17533,
2211.01058, 2212.09470, 1912.06345, MathWorld (2), Wikipedia (5), ramanujanmachine.com home,
Mathlib docs (2). Own computations: /scratchpad p10/chk.py, c21.py, hyp.py.
