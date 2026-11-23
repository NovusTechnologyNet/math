# Referee report on `00_summary.md` (Erdos's conjecture for f = +-1, odd non-square period)

Date 2026-11-23. Referee: an independent agent that did not write the proof. I read `00_summary.md` in full,
checked every step of sections 1, 4, 5, 6 by hand, and wrote my own program `python/erdos_pm1_referee.py`
from the definitions (I did not open, import or run `python/erdos_pm1_check.py`). No web access, so nothing
about the literature is checked. Companion file: `02_proof_part_II.md` (my own write-up of Part II).

## 1. Verdict

**Correct.** I found no wrong step and no counterexample. There are a few omissions in the exposition,
each closed in one to five lines (G1 to G3 in section 3, G4 to G6 in section 4), one false side remark that
the proof does not use (G7), and notation that reuses letters (G8). The repairs are additions of omitted
justifications; none changes a statement or the structure of the proof. The result is conditional only on
classical theorems that I did not re-derive (listed in section 2).

## 2. The statement I certify

**Theorem.** Let q >= 1 be an odd integer and f : Z -> Q with f(n+q) = f(n) for all n, f(n) = 0 when q | n,
and f(n) a rational number with odd numerator and odd denominator when q does not divide n. If the series
sum_{n>=1} f(n)/n converges and its sum is 0, then q is a perfect square.

Used and taken from the literature, not re-derived by me: (T1) Baker's theorem in its homogeneous qualitative
form (logarithms of non-zero algebraic numbers that are linearly independent over Q are linearly independent
over the algebraic numbers; any determination of the logarithms); (T2) Gauss's formula for psi(a/q);
(T3) zeta(s,x) = 1/(s-1) - psi(x) + O(s-1) and Abel's limit theorem for Dirichlet series; (T4) L(1,chi) != 0
for every non-principal Dirichlet character mod q. No other hypothesis is used: not q = 1 mod 4, not "q is
not a prime power", not |f| = 1. For even q the statement is void for a trivial reason (the sum over a
period is a unit of Z_(2), so the series diverges).

Unconditional parts that I certify separately:
- **Theorem C (pure algebra, `02_proof_part_II.md`).** f : Z/q -> Q, q odd, f(0) = 0, f(r) odd for r != 0,
  (a) and (b) of section 1 imply that every v_p(q) is even. More precisely Theorem A ((a) gives
  ell_p = (p-1) k_p mod 2^(s_p+1)) and Theorem B (c_p = 0 gives ell_p = 0 mod 2^(s_p+1)).
- **The formula** of section 1 for sum f(n)/n (given T3) and the direction "(a) and (b) imply sum = 0".
- **The converse for squares (6.3).** For every odd square q the explicit f of 6.3 is odd-valued and
  satisfies (a), (b), so sum f(n)/n = 0. I checked the argument by hand and the function exactly for
  q = 9, 25, 49, 81, 225, 441.

Not certified: every statement about what is known or new (sections 0, 6.2, 7, 8 of the summary), and the
computations of section 3 of the summary as such (I did not run them; mine agree where they overlap).

## 3. Part I, line by line (summary lines 24 to 59)

1. n = m k with m in M(q), gcd(k,q) = 1: unique (m = product of p^(v_p(n)), p in P). For s > 1 everything
   converges absolutely, k = a mod q with a a unit, and sum_{k = a mod q} k^(-s) = q^(-s) zeta(s,a/q). So
   L(s,f) = sum_a F_s(a) q^(-s) zeta(s,a/q). Correct. F_s(a) is a finite combination of geometric series,
   analytic for Re s > 0. Correct.
2. sum_a F_1(a) = sum_r f(r): I checked it by counting, not only by the residue remark: for r with
   gcd(r,q) = d, N = q/d with set of primes n, the pairs (a,m) with am = r have m = d prod_{p not in n} p^j_p,
   a is fixed mod N (phi(q)/phi(N) choices), and (phi(q)/phi(N)) (1/d) prod_{p not in n} (1-1/p)^(-1) = 1.
3. Expansion at s = 1 with (T3): the pole cancels, the term -log q sum_a F_1(a) vanishes, and
   sum f(n)/n = -(1/q) [sum_a g(a) psi(a/q) - sum_a F_1'(a)], F_1'(a) = -sum_m f(am)(log m)/m. Correct.
4. The exact form of lam(r,p): the same count with the weight v_p(m) gives v_p(r) if v_p(r) < k_p, and
   (sum_{j>=0} (k_p+j) p^(-j)) (1 - 1/p) = k_p + 1/(p-1) otherwise. Correct. Verified exactly by my program
   (sum over units a and over M(q) in closed form against sum_r f(r) lam(r,p)) for
   q = 9, 15, 21, 27, 45, 63, 75, 99, 105, 135, 225, random rational f.
5. "If": clear ((a) gives sum_r f(r) = sum_a g(a) = 0, hence convergence, and the formula gives 0).
6. Gauss's formula as quoted is correct for 0 < a < q, q odd (checked to 60 digits for q = 9, 15, 21, 25,
   45, all a). **Gap G1**: the terms -gamma - log 2q are multiplied by sum_a g(a), which is 0 by
   convergence; the summary does not say so. This is what makes the relation homogeneous: no constant term
   and no gamma, so the homogeneous Baker theorem is enough.
7. The linear form: beta_0 log(-1) + sum_{0<j<q/2} beta_j log sin(pi j/q) + sum_p c_p log p = 0 with
   beta_0 = -(1/2) sum_a g(a) (zeta^a + 1)/(zeta^a - 1) (because pi cot(pi a/q) = log(-1) (zeta^a+1)/
   (zeta^a-1) with log(-1) = i pi), beta_j = sum_a g(a)(zeta^(aj) + zeta^(-aj)), zeta = exp(2 pi i/q).
   All coefficients are in Q(zeta_q) (c_p rational); -1, sin(pi j/q), p are non-zero algebraic numbers. Correct.
8. **Gap G3** (compressed step, supplied): let mu_1..mu_d be a Q-basis of the Q-span of the logarithms
   l_i, l_i = sum_k r_ik mu_k with r_ik rational. sum_i beta_i l_i = 0 means sum_k (sum_i beta_i r_ik) mu_k
   = 0, hence by Baker sum_i beta_i r_ik = 0 for all k; apply a field automorphism sigma (r_ik is fixed):
   sum_i sigma(beta_i) l_i = 0. For sigma_h : zeta -> zeta^h this turns cot(pi a/q) into cot(pi a h/q) and
   cos(2 pi a j/q) into cos(2 pi a h j/q); using Gauss's formula backwards (and sum g = 0 again) the
   conjugated relation is sum_a g(a) psi(<ah>/q) + C = 0, i.e. T(h) + C = 0 as stated. Correct.
9. sum_h T(h) = (sum_b g(b)) (sum_a psi(a/q)) = 0, so C = 0, so all c_p = 0 (rational c_p, unique
   factorization). Correct.
10. T(h) = 0 for all h; pairing with chi gives (sum_b chibar(b) g(b)) (sum_a chi(a) psi(a/q)) = 0 and
   sum_a chi(a) psi(a/q) = -q L(1,chi) for chi != 1 (also for imprimitive chi). **Gap G2**: this kills the
   components of g at chi != 1 only. The trivial component is sum_b g(b), which is 0 by convergence (or:
   for chi = 1 the factor is sum_a psi(a/q) < 0). With that, g = 0 on the units. Correct.
11. Solution space (lines 56 to 59): g = Mop f on the units and c_p = sum of (Mop f)(n) over
   {n : gcd(n,q) = p^i, 1 <= i <= k_p}: correct (hand check; exact check by program for the same eleven q).
   **G7**: the dimension q - 1 - phi(q) - t is wrong for q prime (the set for p is {0} and the space is 0, not
   of dimension -1). Not used anywhere.

Numerical tests of Part I (my code, mpmath, 75 digits working precision, tolerance 1e-60), for
q = 9, 15, 21, 25, 27, 33, 35, 45, 49, 63, 75, 81, 99, 105, 135, 147, 165, 225:
- the formula against -(1/q) sum f(r) psi(r/q) for random rational f with sum 0: worst deviation 2e-75;
  for q <= 35 also against a direct evaluation of the series without digamma (Richardson on the partial
  sums over whole periods, 20 digits). Remark: mpmath's `nsum` with default settings gave only 5 correct
  digits on this series; I do not use it.
- "if": random rational f with (a), (b): |sum| < 1e-60.
- "only if", as far as numerics can go: f with (a) but not (b) has sum = -(1/q) sum c_p log p != 0;
  f with (b) but not (a) has sum != 0; the matrix [psi(<hb>/q)] over the units is non-singular (q = 9, 15,
  21, 25, 45); LLL (python-flint, 220 digits) on {psi(r/q)} with the constraint sum f = 0 finds exactly
  q - 1 - phi(q) - t short relations for q = 9, 15, 21, 25, 27, 33, 35, 39, 45, all inside the space of (a),
  (b); the next lattice vector has squared norm at least 10^17.

## 4. Part II, line by line (summary lines 103 to 211); list of gaps

I rewrote every proof (`02_proof_part_II.md`). Findings, most serious first; none is an error in the
mathematics.

- **G4 (Lemma 2, lines 139 to 140).** "As a runs over A_x, a mod N runs uniformly over the units mod N of
  class x_n" is asserted without proof. True: a -> (a mod N, [a]_{P-n}) is a surjective homomorphism
  (Z/q)^* -> (Z/N)^* x S_{P-n} (Chinese remainder theorem, product of surjections), and A_x is a full
  preimage. Supplied as (C2).
- **G5 (Lemma D, lines 157 to 160).** (F1) speaks of a_n acting on O[S_m'], where a_n does not live; what is
  used (three times) is that the image of a_n under t_r -> 1, the image in L/N_r L, and a_r itself are of
  the form "integer minus a unit of finite order", to which the argument of (F1) applies. The integer must
  avoid 1 and -1 (0 is harmless). If |C_r| = 1 the ring O' = O[C_r]/(N_r) is the zero ring; the induction
  still goes through, but it should be said that the zero ring is allowed (in the application |C_p| >= 2).
  The "finite subgroup Gamma of O^x" can be replaced by "u_p = zeta_p sigma_p with zeta_p of finite order
  in O", which is what the induction really produces.
- **G6 (Lemma KL, lines 177 to 185).** "p" is an integer pi_p with |C_p| dividing pi_p - 1, and Lemma D
  needs pi_p not in {1, -1}; fine for odd primes. Step (i) uses that a full Z_(2)-lattice equals its double
  dual; true, should be cited. Otherwise every line of (i) to (iv) is correct; (iii) is the one place where
  the lift from Q[S_m] to Q[G] is not formal, and it is right (gam_n^* a_k N_{m-k} is integral or zero).
- **G8 (notation).** c_p is the coefficient of log p (line 30), the generator of C_p (line 120), and c_0 is an
  integer in 5.5 (line 202); phi is Euler's function, a function of a set of primes and "a function on S_n";
  n is an integer and a set; m is an element of M(q) and the set P - p_0; N is q/gcd, a norm element, and
  N(r). A reader can resolve all of them; a formalizer should rename.
- Lemma 1 (lines 130 to 133): correct. The count phi(N)/2^(s_n) = (N/rad N) o(n) is odd because C_p is the
  whole 2-part quotient.
- Lemma 2 (lines 135 to 148): correct, including the constant |A_x| 2^(s_n)/(d phi(N)) = 2^(-s_{P-n})
  prod_{p not in n}(1 - 1/p), the cancellation of D_n^(-1), and the direction u_p = ubar_p^(-1). (The
  conclusion of Theorem A does not depend on whether u_p or its inverse appears: Lemmas D and KL hold for
  arbitrary u_p, and my abstract test uses random u_p.) f(0) = 0 is used exactly here (the term n empty).
- Lemma D (lines 150 to 174): correct; steps (1), (2), (3) checked one by one, including the two different
  induction hypotheses (ring O' in step 2, ring O in step 3) and N_r a_n = N_r abar_n.
- Theorem A (lines 192 to 205): correct: the split of (M); B = N_0 w; Z = -(p_0 - u_0) w; eps(Z) = 2^(s_m) ell;
  c_0 = k_0 prod (1 + (p-1) k_p) = k_0 mod 2; B_e in I; Lemma KL; the final congruence (the sign is
  immaterial modulo 2^(s_0+1)). The case of a prime power (m empty) is covered.
- Theorem B (lines 207 to 211): correct ((p-1)^2 = 0 mod 2^(s+1) because s >= 1; (p-1)k + 1 odd).
- Corollary (line 109): correct.
- Section 6.3 (lines 229 to 238): correct (g_n = prod_{p in n}(sum_{j=1..k_p} (-1)^j) Theta_n = 0; f is
  constant on the orbits of the odd-order kernel, so g is constant on each A_x and vanishes; (b) by the
  alternating sum over the exponent of a second prime).

Where "2-group", "cyclic", "odd", "unit of Z_(2)" and f(0) = 0 enter: see section 7 of `02_proof_part_II.md`.

## 5. Independent computations (`python/erdos_pm1_referee.py`; `selftest` passes in about 13 s)

All exact unless marked numerical. The 2-adic linear algebra is my own: elimination modulo 2^64 with
pivots of least valuation over the whole remaining matrix (every operation is then exact modulo 2^64; the
largest pivot valuation met in the sweeps was 14), checked against brute force on 200 random small lattices.

Tests of the lemmas and theorems:
- Lemma 1 and Theorem B: random odd-valued rational f, 18 values of q (four functions each); Theorem B also
  on odd-valued f constructed with c_p = 0 exactly. Lemma 1 fails, as it should, when one value is made even.
- Lemma 2: (M) holds exactly for random rational solutions of (a) and fails for random f (q = 15, 21, 45,
  63, 75, 105, 117, 135, 165, 225, 273, 315).
- Theorem A on explicit odd-valued rational solutions of (a) that I constructed by 2-adic elimination and
  then verified exactly, independently of how they were found (all values odd; g(a) = 0 at every unit for
  q <= 400, and for the larger q at one unit of each class of S_P after checking that f is constant on the
  orbits; in addition g(a) = 0 from the definition as a sum over M(q) on random units):
  308 (function, prime) pairs, 35 values of q:
  9, 21, 25, 45, 49, 81, 105, 117, 153, 165, 189, 225, 273, 357 (full system, functions not constant on
  orbits) and 65, 289, 525, 585, 625, 765, 833, 1105, 1225, 1365, 1625, 1921, 2025, 2465, 2993, 6069,
  17289, 26937, 34241, 83521, 86657 (orbit system): squares and non-squares, prime powers, up to four
  primes, primes 5, 13, 29 (1 mod 4), 41, 73 (1 mod 8), 17, 113, 97, 353, 193, 449 (1 mod 16 and beyond).
  For each of them every relation in the proof of 5.5 holds (B = N_0 w, Z = -(p_0 - u_0) w,
  eps(w) = k_0 2^(s_m) mod 2^(s_m+1), 2^(s_m) ell = eps(Z)), and for k_p odd the coefficient c_p is a 2-adic
  unit (so (b) fails), as the Corollary predicts. For q = 27, 63, 147, 221, 325, 5763, 462961 there is no
  odd-valued solution of (a) at all (Theorem A is void).
- Lemma D on 400 random instances (cyclic groups of orders 2, 3, 4, 6, 8, up to three factors, signs +-1 in
  u_p, integers pi from -9 to 13): I^# computed as a kernel, then I^# inside I and I inside I^# by lattice
  membership. With one generator of I removed the equality fails in 86 of 133 instances.
- Lemma KL on 400 random instances (C_0 of order up to 8, also non-cyclic): the lattice {w : N_0 w in I}
  computed as a kernel, eps(w) = 0 mod |S_m| for all of it. Without "|C_p| divides p - 1" the conclusion fails
  in 196 of 400 instances.
- Theorem A from (M) and the shape of Lemma 1 alone, with arbitrary u_p and arbitrary odd integers in
  place of primes: holds on all 173 solvable instances out of 400 (so no arithmetic is hidden).
  (These three counts are from `abstract 400`; three further seeds with 300 instances each: no failure.)
- The "(a) alone" rule of section 6.1: confirmed for all 205 odd composite q <= 640 (full system).

## 6. Attempts to refute the Theorem

Question for each q: is there f with f(0) = 0, all other values odd, (a) and (b)? Decided exactly (basis
of the solution space with the non-unit values as parameters, 2-saturation, is the all-odd vector in the
lattice modulo 2?).
1. Full system (unknowns f(1..q-1), no symmetry assumed): all 511 odd composite q <= 1500. Survivors:
   exactly the 18 squares 9, 25, ..., 1369. Also q = 1649, 1737, 2313, 3315 (killed), 2601 (survives).
   For q = 9, 15, 21, 25, 27 also by plain enumeration of all residue patterns, no linear algebra.
2. Orbit-reduced system (f constant on the orbits of the odd-order kernel H of (Z/q)^* -> S_P; enough,
   because the average over H of an odd-valued solution is an odd-valued solution; my derivation, and the
   two systems agree for every q <= 1500): all 4562 odd composite q <= 12000. Survivors: exactly the 54
   squares 9, ..., 11881. (The sweep `orbit` decides 4555 of them; the seven with more than 3000 orbits,
   3855, 4369, 8995, 9843, 10023, 11535, 11565, were run one by one: killed.) Also 1180 of the 1184 odd
   composite q in 12001..15000 (13073, 13107, 14135, 14841 not run): survivors are the six squares.
3. Special q, all killed: 15015, 19635, 285285 = 3.5.7.11.13.19, 3129357 = 3.7.11.19.23.31, 3003, 5005;
   51, 85, 153, 291, 485, 579, 965, 771, 1285, 2313 (primes 17, 97, 193, 257 times a small factor);
   1649 = 17.97, 4369 = 17.257, 18721 = 97.193, 24929 = 97.257, 49601 = 193.257, 1921, 2993, 5763; 1105,
   5525, 32045 = 5.13.17.29; 867, 28033 = 17^2.97, 4913 = 17^3, 97^3, 4131, 3375, 675, 1575. Squares, all
   surviving: 2601, 7225, 9409, 11025, 27225, 37249, 99225.
4. The algebraic core with the arithmetic removed (item "Theorem A from (M)" above).
5. Converse: explicit odd-valued solutions for q = 9, 25, 49, 81, 225, 441, both the formula of 6.3 and
   three functions per q produced by my elimination; (a), (b) exact, |sum f(n)/n| < 1e-73 (numerical).
No counterexample, and no discrepancy with any number in the summary that I recomputed.

## 7. Scope

The argument proves the statement for every odd q that is not a perfect square, with no silent extra
condition. Things I looked for and did not find: a use of q = 1 mod 4 or of two distinct primes (the proof
of Theorem A with m empty is the prime-power case); a use of |f| = 1 or of integrality (only "unit of
Z_(2)"); a use of reciprocity or of the actual values chi_{p'}(p) (Lemmas D, KL hold for all u_p). What is
used: q odd (every p - 1 is even, and p is not 1 or -1), f(q) = 0, f rational (the coefficients g(a), c_p
must be fixed by the Galois group in step 8 of section 3). The method cannot reach squares (6.3).

## 8. Remaining doubts

- This is one referee's reading plus computation, not a formal proof. Part II is elementary enough to be
  formalized; `02_proof_part_II.md` is written for that.
- Part I rests on (T1) to (T4) as stated in section 2; the "only if" direction cannot be tested
  numerically beyond small height. I checked the deduction from Baker's theorem by hand only.
- I cannot say whether the result is new or agrees with the literature (Okada's criterion is attributed
  from second-hand reports; I checked the criterion itself, not the attribution).
- The computations of section 6 are finite; they support the theorem but prove nothing beyond their range.
