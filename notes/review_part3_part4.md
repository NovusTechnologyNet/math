# Referee report on Parts III and IV of pi_formula_theorem.md

Second independent review, 21 November 2026. Scope: pi_formula_theorem.md from "## Part III"
to the end (the version of 11:29 with the Bailey section and the two cost measures),
outside_family_findings.md, and the programs full_class_theorem.py, cheaper_formula.py,
cheaper_fast.py, cheaper_search.py, exact_optimum.py, derive_bailey_table.py,
new_formula_check.py, decompose_formula.py, outside_probe.py, outside_structure.py,
outside_twisted.py, pi_formula_120.json and pi_space_basis_120.json.

Method. I re-derived every step by hand, ran the author's programs, and wrote my own
checks that do not reuse the author's code for the decisive computations:

| script | what it checks, and how it differs from the author's route |
|---|---|
| review_valuations.py | valuations of t - zeta_120^j at all 8 primes above 3 and 5, by Hensel-lifted local factors of Phi_120 and resultants (sympy only); absolute norms of the 24 atoms |
| review_space.py | the 13 relations re-verified in flint; a *rigorous* rank certificate in ball arithmetic; W (13-dim) and V (8-dim) built as an exact rational nullspace (no floating point, no rational reconstruction); Theorem D thresholds, the F_1 claim and the json formula, all in exact arithmetic |
| review_vertex_exact.py | exact integer enumeration of all vertices of the 35-condition arrangement on my own V (DFS with exact kernels, no modular arithmetic, no floating point); both cost measures; Pareto front |
| review_flats2_exact.py | the same for all 2-dimensional flats (needed for the "attained by 22 formulas" count) |
| review_formulas.py | the formula table of Part III (BBP, Bellard, Euler, the two 2/3 formulas, the json formula) rebuilt from their BBP forms by my own code, summed to 200 digits, tested exactly for membership in V, scored in both measures; pi_space_basis_120.json compared with my V |
| review_named_check.py | the 8 named basis series of Theorem C lie exactly in V and are independent |
| review_minimizer_families.py | whether the 22 winners of mean(1/s) = 7/24 are isolated; builds an optimal formula that is not one of them |

Verdict vocabulary: **correct** (I could reproduce it and found no flaw), **gap** (the
conclusion holds but the written argument is incomplete or imprecise), **error** (a
statement is false as written).

---

## 1. Step 1 (Baker's theorem)

**Verdict: correct, with two presentational gaps.** Location: Part III, "Setting" and
"Step 1".

*The series.* With t = 1 + i, t^2 = 2i, so 2^(-floor(k/2)) = u(k) t^(-k) with
u(k) = t^(k mod 2) i^(floor(k/2)) (period 8). Writing rho(k)u(k) = sum_r c_r r^k over the
lcm(P, 8)-th roots and using |r/t| = 2^(-1/2) < 1,
S = sum_r c_r sum_k (r/t)^k / k = -sum_r c_r Log(1 - r/t), with the *principal* Log
(the power series converges to it). With d_r = -2i c_r this is the note's
S = (1/2i) sum d_r Log w_r and D(k) = -2i rho(k) u(k) (as in cheaper_formula.d_exact).
So there is no branch problem: the logarithms in the identity are the principal ones,
and Baker's theorem holds for any choice of logarithms anyway.

*Both directions.* If d = sum_a x_a e_a with prod w_r^(e_a(r)) a root of unity, then
sum_r e_a(r) Log w_r = q_a i pi with q_a rational and S = (pi/2) sum x_a q_a. Conversely
suppose S = alpha pi, alpha algebraic. Then sum d_r Log w_r - 2 alpha (i pi) = 0. Choose a
Q-basis lambda_1..lambda_m of the Q-span of {Log w_r} together with i pi = Log(-1), write
every log in it with a rational matrix Q; Baker's homogeneous theorem forces
(d, -2 alpha) Q = 0, and the kernel of a rational matrix over Qbar is spanned by its
rational kernel, i.e. by the Q-linear relations among the logs and i pi. Their projections
to the r-coordinates are exactly the integer vectors e with prod w^e a root of unity
(scaled). So the reduction is right in both directions, including the value 0.

*One to one, and equivariance.* rho -> rho*u -> c -> d is a composition of injective
maps on patterns of period dividing P' = lcm(P, 8), so it is one to one. The image is not
"Galois-equivariant" in the naive sense (Part II's phrase). The exact condition I derive
is: for sigma in Gal(Q(zeta_P')/Q(i)), d_(sigma r) = sigma(d_r); and for complex
conjugation, d_(i conj r) = -conj(d_r) (because conj(u(k)) = (-i)^k u(k)). Conversely
every d with these two properties comes from a rational rho. So it is equivariance for a
*twisted* action (r -> i conj r, with a sign). This twist is harmless for the theorems,
because the relation space M is stable under it (sigma(w_r) = w_(sigma r) for sigma fixing
i, conj(w_r) = w_(i conj r)), and by Speiser's lemma the rational patterns with d in
K (x) M form a Q-space of dimension dim M. That is the conceptual reason why Theorem C's
two numbers 13 (relations) and 13 (patterns) coincide. The note never states this; it
gets 13 by computation, which I have confirmed exactly (item 4).

*Gaps to repair.* (a) State the twisted equivariance correctly in Part II/III instead
of "Galois-equivariant". (b) In Part IV and in a remark here: a BBP formula whose
denominators are shifted (i outside 1..N) differs from an F_n series by a rational
constant; Baker's inhomogeneous form (1, lambda_1, ..., lambda_m independent over Qbar)
forces that constant to vanish, so such formulas are covered too. One sentence suffices.

Cosmetic: outside_family_findings.md, proof step (1)/(3) of the lemma, has two cancelling
sign slips: from sum_r d_r Log(1 - r x) = -q pi one gets sum_j x_j eps_j = +i q, not -i q;
and -i pi * h(-i q) equals -q pi, not q pi. With the correct sign, -i pi * h(i q) = q pi.
The conclusion is unaffected.

## 2. Step 2 (which roots of unity can occur)

**Verdict: the conclusion is correct; the written argument has a gap (the induction is
misstated and one row of the atom table is not covered by Lemma 3). Here is a complete
proof.** Location: Part III, "Step 2"; full_class_theorem.step_a.

Facts used (all elementary):

* (F1) No prime above 2 divides t - r: t = 1 + i lies in every prime above 2 and r is a
  unit. So v_P(w_r) = -v_P(t) for P | 2, and the condition at P | 2 reads
  sum_r e_r = 0 (this is the all-ones row of valuation_rows, which the note never
  explains). For P above an odd p, v_P(w_r) = v_P(t - r) and the condition is
  sum_r e_r v_P(t - r) = 0.
* (F2) If P | t - r and P | t - r' (r' != r), then P | r(1 - r'/r), so r'/r has order
  a power of the residue characteristic p of P. In particular, if p does not divide
  n = ord(r), then ord(r') = n p^a > n.
* (F3) Exceptional roots (every prime of t - r lies over a prime dividing ord r). The
  rational primes under t - r are those of N(z_O), the atom of its Q(i)-orbit, so this
  is an orbit property. Rows m, 2m (m odd) and 4m: Lemma 2/Lemma 3 of Part II give a
  prime p = 1 mod 4m (so p does not divide 4m) except for O_1, O_2, O_6, O_10 and their
  partners. Rows 2^(j+3)m: Bang for Phi_(2^(j+2)m)(2) gives p = 1 mod 2^(j+2)m. **Row 8m
  (self-paired orbits) is not covered by Lemma 3**, which is about pair representatives;
  it needs its own two lines: the orbits of order 8m are {+-zeta_8 s} and {+-zeta_8^3 s}
  (s primitive m-th), and prod (t^2 - i s^2) = i^phi(m) Phi_m(2),
  prod (t^2 + i s^2) = i^phi(m) Phi_m(-2) = +-Phi_(2m)(2). Bang then gives a prime
  p = 1 mod m (resp. 2m), not dividing 8m, except Phi_1(2) = 1 (the orbit +-zeta_8) and
  Phi_6(2) = 3 with 3 | 24 (the orbit zeta_24^(1,5,13,17) = +-zeta_8^3 zeta_3^(+-1)).
  The table's entry "Phi_m(2), Phi_2m(2)" is right, but nowhere proved; it is now.
  Result: the exceptional roots are exactly the 20 listed (units: 1, i, +-zeta_8,
  zeta_6^(+-1), zeta_12^(1,5); prime 5: the primitive 10th roots and zeta_20^(3,7,11,19);
  prime 3: zeta_24^(1,5,13,17)). I confirmed every norm exactly (review_valuations.py:
  norms 1, 5^4 and 3^8 respectively).
* (F4) Let R0 = E u {p'-part of r : r in E, p | N(t - r)}. The p'-parts are -1 (from the
  10th roots, p = 5), -i (from all four 20th roots), zeta_8^3 and zeta_8^7 (from the 24th
  roots, p = 3). So R0 is the note's 24 roots; R0 \ E consists of roots of 2-power order.

*Proof that every relation is supported on R0.* Suppose the support S of a relation is
not inside R0 and let r be an element of S \ R0 of **largest order among the elements of
S \ R0** (not of S: the largest order in S may well belong to an exceptional 24th
root). r is not exceptional, so some P | t - r has odd residue characteristic p with
p not dividing n = ord r. If r' in S, r' != r, has v_P(t - r') > 0, then by (F2)
ord r' = n p^a > n, so r' is in R0. If r' is in E, then p divides N(t - r') and r is the
p'-part of r', so r is in R0: contradiction. If r' is in R0 \ E, its order is a power of
2 while p | ord r' with p odd: impossible. So P divides no other t - r' in the relation,
(F1) gives e_r v_P(t - r) = 0, and e_r = 0: contradiction. QED.

Answers to the specific questions. The list of 24 is complete and the exceptional roots
are correctly identified. A prime ideal of characteristic p not dividing ord(r) *can*
divide t - r' for another root, but only for r' = r * (p-power root), of strictly larger
order; this breaks the induction "largest order in the relation" as literally written,
but not the corrected induction above, because R0 is closed under taking p'-parts of
exceptional roots by construction (that closure is what step_a computes). Independently,
review_valuations.py shows that among all 120 roots zeta_120^j, the only ones with a
positive valuation at a prime above 3 or 5 are the 24 of R0.

Repair: replace the paragraph by the proof above, and add the 8m-row computation to
the atom table or to Lemma 3. (full_class_theorem.step_a only searches orders up to 576;
that is fine as a check, but the theorem rests on the argument.)

## 3. Step 3 (13 relations, and no more)

**Verdict: correct. The hard-coded valuation table is right; the certificate is valid
in substance, and I have made it rigorous.** Location: full_class_theorem.valuation_rows,
certify_rank; Part III "Step 3".

*Valuation table.* review_valuations.py computes, for p = 3 and 5, the p-adic factors
G_i(x) = h_i(x^p)/h_i(x) of Phi_120 (h_i the Hensel-lifted factors of Phi_40 mod 3,
resp. Phi_24 mod 5), and v_(P_i)(t - zeta^j) = v_p(Res(G_i, 1 + x^30 - x^j)) / f for all
120 values of j. Result: there are 4 primes above 3 (f = 4, e = 2) and 4 above 5 (f = 2,
e = 4), but they give only **2 distinct rows each**, and these are exactly the four rows
of valuation_rows():

    above 3: {45: 2, 5: 1, 85: 1} (twice),  {105: 2, 25: 1, 65: 1} (twice)
    above 5: {60: 4, 12: 1, 36: 1, 84: 1, 108: 1} (twice),  {90: 4, 18: 1, 42: 1, 66: 1, 114: 1} (twice)

The same table follows by hand: modulo a prime P above 5 the reduction mu_24 -> F_25^*
is bijective, so exactly one u in mu_24 is congruent to t, namely u = -1 when
2 + i is in P and u = -i when 1 + 2i is in P; then v_P(t - u zeta_5^b) = 1 for b != 0 and
v_P(t - u) = 4. Above 3, t^4 = -4 = -1 mod 3 forces u in {zeta_8^3, zeta_8^7}, with
valuations 2 and 1. The absolute norms (5^16, 3^16, 5^4, 3^8, 1) are exhausted by these
valuations, so 2, 3 and 5 are the only primes involved (2 only through t). The note's
phrase "valuations (primes over 2, 3, 5)" should say that the 8 primes over 3 and 5 give
4 distinct rows and the primes over 2 give the row sum(e) = 0.

*Certificate.* Using a subset of the place rows is legitimate for the upper bound: every
row is a homomorphism that vanishes on every relation, so full column rank on 11 columns
already excludes a relation among them. With 13 exact relations, each introducing a new
root, the relation space then has dimension exactly 13. The 16 embeddings
zeta -> zeta^a, a = 1 mod 4, represent all 16 complex-conjugate pairs, and sigma_a(t) = t
for these a, so the log rows are right. Smallest singular value 0.72 from a 200-digit SVD
is convincing but is not by itself a proof (it trusts the SVD routine). review_space.py
replaces it by ball arithmetic: the Gram determinant of the 21 x 11 place matrix on the
columns {0, 60, 90, 20, 15, 45, 105, 12, 36, 84, 5} is [1.521005012e9 +/- 0.415], which
excludes 0. All 13 relations were re-verified exactly in Z[zeta_120] with flint, their
angles re-computed in ball arithmetic, and every relation lies in the kernel of the full
place matrix (24 columns). outside_structure.py 2 (LLL on the complex logs, a different
search) also returns 13.

## 4. Theorems C and D (dimensions 13 and 8; step C)

**Verdict: correct. Both dimensions and the step-C table reproduced exactly by a
different method, and dimension 8 also theory-free.** Location: Part III Theorem C,
Theorem D; cheaper_formula.step_d; full_class_theorem.step_c.

*Different method.* The author solves for rho numerically (complex constraints at 200
digits, numerical RREF, rational reconstruction, exact re-check). I instead used the
annihilator M^perp (11 rational vectors on the 24 roots): rho is in W iff
d_j(rho) = 0 for the 96 roots outside R0 and sum_j f_j d_j(rho) = 0 for f in M^perp. Each
d_j(rho) is an element of Q(zeta_120), so these are 3424 exact rational linear equations
in 120 unknowns. The value is value/pi = (1/2) sum_j c_j d_j(rho) for any rational c with
c . e_a = content_a. Results (review_space.py, all exact):

* dim W = 13; the values/pi of W span a 6-dimensional Q-space, so dim V = 13 - 6 + 1 = 8;
  V computed directly also has dimension 8; it has the same span as
  pi_space_basis_120.json, whose stored pi contents match direct summation to 80 digits.
* The 8 named series of Theorem C lie exactly in V and are independent.
* Entries identically zero on V: only k = 0 (mod 120); 35 distinct conditions.
* Theory-free: outside_probe.py 2 120 run by me with 30 bits per entry (the author used
  28) finds dimension 8, 35 conditions and optimum 7/12 = 2 * 7/24; the gap between
  relations (squared length <= 920) and non-relations (about 2^74) is wide.

*Theorem D / step C.* Over Q in W, the number of rational solutions vanishing on all k
with gcd(k, 120) < g is 6, 3, 1, 1, 0, 0 for g = 2, 3, 4, 5, 6, 8, and a solution with
non-zero value exists only for g = 2, 3. This matches step C's complex computation
(by Galois descent the complex solution space is defined over Q, so the two must agree).
Step C itself is described as an "exact rank computation"; it is not quite: the rank is
a mod-241 lower bound plus a numerical SVD upper bound. The exact check above closes
that. Theorem D is correct as stated (slowest term, gcd <= 3).

Minor point on Theorem C's wording: "all of period 120" means "of period dividing 120".

## 5. Theorem E and the optimality proof

**Verdict: the optimum values 7/24 and 2/3 and the Pareto front are correct (reproduced by
an independent exact enumeration); the claim "attained by 22 formulas" is an error; two
smaller rigour gaps.** Location: Part III "Two cost measures", Theorem E,
"Proof of optimality"; cheaper_fast.py, exact_optimum.py.

*The formula.* pi_formula_120.json lies exactly in W with exact value/pi = 1/4 (no
irrational part), sums to pi/4 to 1000 digits (error 5.5e-1011), has 55 non-zero
entries, all half-integers, levels s = 4 for p = 1 (mod 4) and s = 3 for p = 3 (mod 4),
mean(1/s) = 7/24 and 55/60 = 11/12 terms per bit. decompose_formula.py writes it exactly
as Euler + Z with the displayed Z, and I checked the five logarithm identities in Z by
hand (|Phi_6(t)/t^2| = 1/2, (t^2 - i)/t^2 = 1/2, (t^4 - i t^2 - 1)/t^4 = 3/4,
(t^2 + i)/t^2 = 3/2, |1 - 1/t| = 2^(-1/2)). So the json file is really a series for pi/4
with mean(1/s) = 7/24.

*The cost model.* For p not dividing 120, rho(s p) depends on s and p mod 120, so s depends
on p mod 120; a window at bit m needs exactly the primes p with s_p p <= 2m(+O(1)); by the
prime number theorem in progressions the sum of log2 p over them is
2m * log2(e) * mean(1/s) * (1 + o(1)). Correct as a model. It is a model of the cost, not
a theorem about running time; the note says so in its measurements section.

*Reduction to vertices.* Both costs are functions of the zero set and are monotone under
adding zeros. The argument in the note (if the flat has dimension >= 2 and every
remaining coordinate were proportional to the pi functional on it, the coordinate map
would have rank 1, contradicting injectivity) is correct, so both minimum *values* are
attained at vertices. Every vertex is cut out by 7 independent conditions among the 35,
so C(35, 7) covers all of them. Correct.

*Exactness of the search.* cheaper_fast.py (floating point) found 7/24 and 22 winners;
its margins in my run were 7.5e-14 (largest "zero") against 4.2e-5 (smallest
"non-zero"), and 1.2e-16 against 2.0e-5 for dependence. The old sentence "no computed
value came within nine orders of magnitude of a threshold" was not literally true (the
smallest non-zero value is 2.4 orders above the threshold 1e-7); what was true is that the
two populations are separated by about nine orders. The new exact_optimum.py replaces
this; I checked its logic: the Hadamard bound for every 8 x 8 determinant det[C; c] is
the product of the 7 largest condition norms times the largest of |c|, |q| (correct, no
sqrt(8) needed because the determinant is bounded directly), and the score arithmetic
(lcm(1..40)) fits in int64. One rigour gap: when the 7 x 8 matrix has rank 7 over Q but
rank < 7 modulo one of the four primes, that prime is treated as "zero" (`(D == 0) | ~r7`),
so the remaining three primes (product about 2^93) do not exceed the bound 2^97/2^98. The
probability is negligible (about 6.7e6 * 4 / 2^62), but the claim "zero modulo every prime
means zero" should be made true by asserting rank 7 modulo every prime or recomputing
those cases exactly.

*The enumeration, reproduced.* I ran exact_optimum.py: 6,724,520 choices, 6,044,222 of
rank 7, 1,519,237 distinct vertices carrying pi, minima 7/24 (22 vertices) and 2/3 (2
vertices), Pareto front {(7/24, 11/12), (1/3, 7/10), (5/12, 2/3)}, exactly as the note
says. Independently, review_vertex_exact.py enumerates the vertices of the arrangement on
*my* V (review_space.py) with exact integer kernels and no modular or floating-point
step: 6,044,222 choices of rank 7, 1,529,496 distinct vertices of which
1,519,237 carry pi; minimum mean(1/s) = 7/24 at 22 vertices (next value 1/3); minimum
terms per bit 2/3 at 2 vertices (next value 7/10); Pareto front
{(7/24, 11/12), (1/3, 7/10), (5/12, 2/3)}. Every number agrees with exact_optimum.py, by a
route that shares no code with it (different basis of V, exact big-integer kernels instead
of determinants modulo primes). The winners also coincide with cheaper_fast.py's 22.

*The two 2/3 formulas* (the "Huvent rate"): rebuilt from their printed BBP forms by
review_formulas.py; both lie exactly in V, sum to pi/4 to 190 digits, have 8 non-zero
entries per 24 (2/3 terms per bit) and mean(1/s) = 5/12. Because the terms count drops
strictly whenever an entry is made zero, every minimiser of terms per bit is a vertex, so
"exactly two formulas up to scaling" is correct.

**Error: "the least mean(1/s) is 7/24, attained by 22 formulas".** The 22 winners are 22
*vertices*, not 22 formulas. The cost mean(1/s) is not strictly monotone in the zero set,
and the optimum is attained on whole flats: review_minimizer_families.py shows that the 22
winners split into two groups of 11, each group spanning only a **2-dimensional**
subspace of V whose common zero set (57 entries) already has cost 7/24. So every pattern
of either plane with non-zero pi content (outside the 11 special lines) has
mean(1/s) = 7/24; normalised to value pi/4, the optimal formulas form **two one-parameter
families** (two affine lines), on which the 22 vertices are the points with extra zeros.
Concretely, (v1 + 2 v2 + 5 v3)/8 for three winners of one group is a series for pi/4 with
mean(1/s) = 7/24 and 63 non-zero entries, proportional to none of the 22.

review_flats2_exact.py confirms this from the other side: over all
1,550,974 independent 6-subsets (695,422 distinct 2-dimensional flats, 694,167 carrying
pi), the minimum of mean(1/s) at a generic member is again 7/24, attained by exactly
**two** 2-dimensional flats; no 3-dimensional flat can do as well (its pi-carrying
2-dimensional subflats would all have to be one of these two planes, which forces the
coordinate map on it to have rank <= 2).
Repair: say "attained exactly on two 2-dimensional flats of V (22 vertices); among the
optimal formulas the fewest terms is 55 per 120 (the json formula)". The optimum value
7/24 is unaffected. The same caveat applies to cheaper_fast.py's "22 patterns" and to
the earlier text of the note.

*Other checks.* new_formula_check.py (re-run): series = pi/4 to 1000 digits; hex digits
after position 1,000,000 6C65E52CB459350050E4BB17 from the new formula, from Euler's and
from pi_blocks.py; primes for a window at bit 4,000,002: 194,397 (0.9612) against
171,693 (0.8412). All as stated.

## 6. Part IV: the sub-series lemma and Theorem F

**Verdict: correct (with the cosmetic sign slip noted in item 1).** Location: Part IV,
Lemma and Theorem F; outside_family_findings.md, "The argument".

*Reduction of BBP formulas to F_n.* With g = gcd(B, N), B = gB', N = gN', v = N' and
K = B'(Nj + i): floor(K/v) = Bj + floor(B' i / N'), so
2^(-Bj)/(Nj + i) = B' 2^(floor(B'i/N')) * 2^(-floor(K/v)) / K. Every
sum_j 2^(-Bj) sum_i a_i/(Nj + i) is therefore an F_v series supported on multiples of B'
with rational periodic coefficients; alternating signs (base -2^B, as in Bellard) are
absorbed by doubling the period. Correct. (Add the remark of item 1(b) for shifted
denominators.)

*Kummer step.* c^(n1) is 2 (n odd) or sqrt(2) in Q^ab (n even). Capelli over K = Q^ab:
a = y^p with y in Q^ab would put 2^(1/p) (n odd, p odd) or 2^(1/(2p)) (n even) in Q^ab,
whose subfields are all normal over Q, while Q(2^(1/m)) is not normal for m >= 3;
sqrt(2) = -4 y^4 would put 2^(1/8) in Q^ab. So X^(n1) - c^(n1) is irreducible over Q^ab,
Q^ab(c)/Q^ab is a Kummer extension of degree n1, and for every eta in mu_(n1) there is an
automorphism h with h(c) = eta c fixing every root of unity; extend it to Qbar. Correct.

*h(d_r) = d_(r/eta).* d_r = (1/P) sum_k rho(k) c^(k mod n) r^(-k); h fixes rho(k) and r,
and eta^(k mod n) = eta^k because n1 | n. So h(d_r) = (1/P) sum_k rho(k) eta^k c^(k mod n)
r^(-k) = d_(r/eta), which is the weight vector of the (complex) pattern eta^k rho(k).
Because d = sum_j x_j e_j with *rational* e_j, h(d) = sum_j h(x_j) e_j, and that series has
value -i pi h(sum_j x_j eps_j) = -i pi h(i q) = q pi. Averaging over eta keeps exactly the
terms with n1 | k. Correct; this is a clean argument. (It needs q rational, or at least
fixed by h, which the "component lemma" generalises.)

*Theorem F.* For n even, k = n1 j turns the sub-series into (1/n1) sum_j rho(n1 j)
2^(-floor(j/2))/j, an F_2 series; for n odd, k = n j gives an F_1 series, i.e. an F_2
pattern on even k. Costs: p first enters at k = n1 s' p, so n * mean(1/s) =
(n/n1) mean(1/s') = 2 mean(1/s'), the F_2 cost (and the F_1 cost for odd n); terms per
bit also match (P/n bits per period in both). Removing terms never lowers either cost.
The odd case needs "V has no pattern on even k with non-zero value": confirmed exactly
(review_space.py: the even-supported part of V is 1-dimensional with value 0, the
log(3/4) = log(3/2) + log(1/2) series). Note that W (algebraic multiples) does contain an
even-supported series with non-zero value (e.g. sum Im(zeta_6^k)/(k 2^k) = pi/6 gives a
rational F_1 pattern for pi*sqrt(3)/9), so the "rational" in "no rational-pi series" is
essential and correct. The claims "these are all binary degree-1 BBP-type formulas" and
"for odd n there is no rational-pi series" are proved.

*Computations.* I re-ran outside_probe for (n, P) = (3, 18), (3, 36), (4, 48), (4, 80),
(5, 60), (6, 72), (12, 24), (2, 120), outside_twisted 3 18 and outside_structure 2 3 5;
every row I ran matches the tables in outside_family_findings.md, the splitting holds to
the noise level, and the displayed formula
pi sqrt(3) 2^(1/3) = 9 sum_j 4^(-j) (1/(6j+1) - 1/(6j+4)) holds to 60 digits. These
tables are evidence, not proof (relations with coefficients above about 2^25 would be
missed), and the theorem does not depend on them.

## 7. The new material (Bailey's table, the second measure)

*Bailey's Table 1.* I compared the dictionary BAILEY in derive_bailey_table.py with the
text of Bailey's compendium (8 April 2023, Table 1; a text extraction of the PDF found in
the session scratch folder, bailey/c.txt): all 27 binary degree-1 rows (b, n, count) agree, and all have
n = 2B or n = B. The translation (n = 2B: patterns of V0 with period dividing gcd(n, 120);
n = B: patterns of V0 on even k with period dividing gcd(2n, 120)) is correct, and the
script reproduces all 27 counts. **Correct.** V0 has dimension 1, 1, 5, 3, 1, 7 at
periods 8, 12, 24, 40, 60, 120 and there is a pi formula exactly at 8, 24, 40, 120.
**Error (small):** "within n <= 120 these are (2^6, 12), (2^18, 36) and (2^54, 108)" is
incomplete: the script itself also lists the F_1 rows (2^B, B) for B = 66, 72, ..., 120
(each with 1 relation). The sentence is true only for b <= 2^60 (the range of Bailey's
table); say so. The attribution of the earlier explanation to Broadhurst's unpublished
"Vanishing Polylogarithmic Ladders" (Bailey's reference [21]) is accurate.

*The formula table.* review_formulas.py rebuilt every row from the published BBP forms
and scored it exactly: BBP (3/4, 1), Bellard (1/2, 7/10), Euler/Hutton (1/3, 7/10),
the two base-2^12 formulas (5/12, 2/3), the json formula (7/24, 11/12); each lies in V
and sums to its stated value to 190 digits. **Error (wording):** "Bellard's is beaten in
both measures by Euler's" is false: both have 7/10 terms per bit; Euler's is better only
in mean(1/s). Also "no formula is better than another in both measures except as
follows" is garbled; what is meant (and true, see item 5) is that the Pareto front
consists of exactly the three value pairs listed.

*Huvent's paper.* A text of G. Huvent, "Formules BBP" (22 February 2001), appeared in the
session scratch folder during this review (huvent/h.txt; I did not fetch it and have not
verified its provenance beyond its title page). **Both** optimal formulas of Theorem E's
standard-measure bullet are printed in it: pi = (1/128) BBP0(2^12, 24; -y^21 + 2y^19 -
12y^14 - 16y^13 - 16y^11 + 128y^5 + 512y^3 + 768y^2), his "meilleur choix" in an
11-parameter family, is the first (his y^e is the term 1/(24i + e + 1)), and
pi = (1/256) BBP0(2^12, 24; -3y^20 - 4y^19 - 4y^17 + 32y^11 + 128y^9 + 192y^8 - 1024y^3
+ 2048y), a few pages later, is the second. So the parenthesis "(Which of the two is
Huvent's has not been checked ...)" should become: both are Huvent's; what is new is the
proof that 2/3 is optimal and that these two are the only optimal formulas. I could not
check the y-cruncher claim.

---

## Overall verdicts

| theorem | verdict | confidence |
|---|---|---|
| **C** (13-dim space of algebraic-pi patterns, 8-dim V, period 120, the 8 named basis series) | **Correct.** Both dimensions, the basis and the period reproduced exactly by an independent construction, the relation count certified in ball arithmetic, dimension 8 also found theory-free. The written Step 2 has a gap (fixed in item 2) and Step 1 should state the twisted equivariance. | 97% (residual risk: the Part II lemmas it rests on, Lemma 2 and Bang, which I did not re-review) |
| **D** (no algebraic-pi series with all terms at gcd(k,120) >= 4) | **Correct.** Reproduced exactly over Q; step C itself is numerical-plus-mod-p, not exact as claimed. | 97% |
| **E** (optima 7/24 and 2/3, Pareto front) | **The optimum values and the front are correct** (two exact enumerations: the author's modular one and my integer one on an independently built V). **Error:** 7/24 is attained by two one-parameter families of formulas (two 2-dimensional flats), not by "22 formulas"; 22 is the number of vertices. "Exactly two formulas" for 2/3 is correct. Wording errors about Bellard and the old "nine orders" sentence. Both 2/3 formulas are Huvent's. The cost measure mean(1/s) is a model of the window algorithm, not a theorem about time. | 95% for the values 7/24 and 2/3; the count statement is false as written |
| **F** (no F_n beats 0.5833; odd n has no rational-pi series; extends to all binary degree-1 BBP formulas) | **Correct.** The sub-series lemma (Kummer automorphism, Capelli, h(d_r) = d_(r/eta)) is a valid proof; the reduction of BBP formulas to F_v, the cost bookkeeping and the odd case all check out. Cosmetic sign slips in outside_family_findings.md. It inherits whatever is wrong in E (so "the formula of Theorem E is optimal" should read "the optimal formulas of Theorem E"). | 93% (conditional on C and E) |

**Most serious problems, in order.**

1. Theorem E's "attained by 22 formulas" is false: the 22 vertices lie on two planes of
   V on which mean(1/s) is constantly 7/24 (review_minimizer_families.py gives an explicit
   63-term optimal formula proportional to none of the 22). The optimum itself stands.
2. Step 2 as written does not prove what it claims: the induction must run over the roots
   of the relation *outside* R0 and use the closure of R0 under p'-parts, and the
   self-paired 8m row of the atom table is not covered by Lemma 3. Item 2 gives a complete
   proof; the conclusion (24 roots, period 120) is right.
3. Several claims of exactness are slightly overstated: step C (Theorem D) is a mod-p lower
   bound plus a numerical SVD; the Step 3 certificate is a floating SVD; exact_optimum.py
   treats a prime at which the rank drops as "zero" although three primes alone do not
   exceed the Hadamard bound. All three are closed here (exact rational computation, ball
   arithmetic, and an exact integer enumeration), so nothing changes, but the text should
   not call them exact as they stand.
4. Small factual or wording errors: "Bellard's is beaten in both measures by Euler's"
   (equal terms per bit); "within n <= 120" the unlisted Bailey rows also include the F_1
   rows b = 2^66, ..., 2^120 (true only for b <= 2^60); the sign slips in the Part IV
   proof in outside_family_findings.md; "Galois-equivariant" without the twist
   d_(i conj r) = -conj(d_r).

Nothing I found affects the headline numbers 13, 8, 7/24, 2/3, 0.5833 or the
classification of Bailey's 27 rows.

