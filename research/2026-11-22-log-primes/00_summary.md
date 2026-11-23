# Logarithms in a base b >= 5: the criterion, and no logarithm of an integer

22 November 2026. Paper proofs, exact computations, a plan for Lean. Nothing here is
machine-checked; where an input is machine-checked its Lean name is given. Program:
`python/baseb_logs.py` (sympy and mpmath; `selftest` passes). No literature search was made.

## Results

1. **Theorem K_b (criterion; paper proof from Baker's theorem).** For every base b >= 2 and positive
   rational y: log y is a value of F_b if and only if some power y^k, k >= 1, is a product of
   integer powers of the orbit numbers P_O (section 1). "If" needs no Baker.
2. **Theorem N (paper proof). The conjecture on primes is true, and more holds.** For b >= 5, b !=
   9: log n is a value of F_b for no integer n >= 2. So in a base that is not a power of 2 or 3, no
   number q pi + q' log n (n >= 2 an integer, q' != 0) has a degree-1 BBP-type formula. In base 10:
   no log n at all; log(11/9) and log(37/33) have one.
3. **Theorem P (paper proof).** The finite test for "log p - w log b is a value for some rational
   w", with w = w(p) > 0 explicit: p must be alone in its part (so p is a unique prime of base b,
   or alone in an Aurifeuillian half), up to one prime dividing the index that passes the same
   test. Section 5: the computations agree.

## 1. Setting and the orbit numbers

b >= 2, t = sqrt(b), b = s^2 d with d squarefree; for d > 1, D is the discriminant of Q(sqrt(d)):
D = d if d = 1 mod 4, else 4d. V_b is the set of values of F_b, a vector space over Q. Every sigma
in the Galois group G of Q(roots of unity), which contains t, has sigma(t) = chi(sigma) t with
chi(sigma) = +-1, and

    sigma(1 - r/t) = 1 - (sigma*r)/t,      sigma*r = chi(sigma) sigma(r):

an action of G on the roots of unity. Its orbits O are closed under complex conjugation
(which has chi = 1). Put

    P_O = prod_{s in O} (1 - s/t),     rho_O(k) = t^(-(k mod 2)) * sum_{s in O} s^k.

**Lemma 1 (no Baker).** P_O is a positive rational number, rho_O is rational and periodic, and
log P_O = - sum_{k>=1} rho_O(k) b^(-floor(k/2)) / k. So log P_O is in V_b.

*Proof.* P_O is fixed by G, so it is rational; it is a product of numbers |1 - s/t|^2 and 1 -+ 1/t,
so it is positive. sigma maps sum s^k to chi(sigma)^k sum s^k: for even k the sum is rational, for
odd k it is a rational multiple of sqrt(d), hence of t. Expand Log(1 - s/t) = - sum (s/t)^k / k and
use t^(-k) = b^(-floor(k/2)) t^(-(k mod 2)). QED

*Norm numbers.* The conjugates of t - r are the numbers chi(sigma) (t - sigma*r). So with c0(r),
d(r) the constant term and the degree of the minimal polynomial of t - r over Z, the number
nu(r) = |c0(r)| / b^(d(r)/2) is P_O^kappa, O the orbit of r, with kappa = 2 if -(t - r) is a
conjugate of t - r and kappa = 1 otherwise. The nu and the P_O generate the same group up to powers.

## 2. Theorem K_b

**Theorem K_b.** Let b >= 2 and y a positive rational. Equivalent: (a) log y is in V_b; (b) y^k =
prod_O P_O^(e_O) for some k >= 1 and integers e_O, almost all 0. Moreover (a'): if q pi + q' log y
is in V_b with q, q' rational and q' != 0, then (b) holds.

*Proof.* (b) => (a): Lemma 1, with the series rho = -(1/k) sum e_O rho_O. (a') => (b): the value
is a combination sum_r D_r Log(1 - r/t) with D_r algebraic, r^N = 1. By Baker's theorem the vector
of coefficients of this relation among log y, i pi and the Log(1 - r/t) is a combination of integer
relations; one of them has a coefficient m != 0 at log y: y^m prod_r (1 - r/t)^(z_r) = +-1. Apply
each sigma in G_N, the Galois group of Q(zeta_N, t), and multiply. For fixed r, sigma*r runs
through the orbit O of r, each element |G_N|/|O| times, so y^(m |G_N|) is, up to sign, the product
over the orbits of P_O^(-(|G_N|/|O|) sum_{r in O} z_r); both sides are positive. QED

For b = 2, 3, 5 this is Theorem K, K3, K5 of the note in another generating set; `selftest` recovers
the machine-checked lists of primes below 100 of bases 2 and 3 from it.

## 3. The numbers P_O explicitly (b not a square)

Let R_m be the set of roots r with r^2 of order m: 2 phi(m) roots, stable under the action, and
prod_{r in R_m} (t - r) = Phi_m(b). Call m **split** if (m odd and D | m) or (m even, D | 2m, D not
dividing m): m = d mod 2d when d = 1 mod 4, m = 2d mod 4d otherwise.

**Proposition 2.** If m is not split, R_m is one orbit and P = Phi_m(b) / b^phi(m). If m is split,
R_m is two orbits O+, O- = -O+ of phi(m) roots; A+- = prod_{s in O+-} (t - s) are positive integers
with A+ A- = Phi_m(b) and gcd(A+, A-) = 1, and P = A+- / b^(phi(m)/2). (If b = c^2 the orbits are
the roots of a given order n and P = Phi_n(c) / c^phi(n).)

*Proof.* t lies in Q(zeta_n) iff D | n. If D does not divide n (n the order of r), some sigma fixes
zeta_n and has chi = -1, so the orbit of r is {+-r'} = R_m. If D | n the orbit is {chi(a) r^a}; it
contains -r iff 4 | n and chi(1 + n/2) = 1 iff 4 | n and D | n/2; otherwise R_m is two orbits. In
terms of m this is the condition above. Coprimality: let F(X) = prod_{s in O+} (X - s), with
coefficients in Z[sqrt(d)], so that Phi_m(X^2) = F(X) F(-X), A+- = F(+-t). A common prime l of A+
and A- has l^2 | Phi_m(b), so l does not divide 2m (a prime factor of m divides Phi_m(b) at most
once, m >= 3, and 2 divides Phi_m(b) only if m is a power of 2). Modulo a prime of Z[sqrt(d)] above
l, t would be a root of F(X) and of F(-X), a double root of Phi_m(X^2), which is separable mod l.
QED

*Formula and algorithm (classical: Aurifeuille, Lucas, Schinzel; Brent's algorithm).*
F(X) = U(X^2) - sqrt(d) X V(X^2) with U, V in Z[Y], so

    Phi_m(Y) = U(Y)^2 - d Y V(Y)^2,        A+- = U(b) -+ d s V(b).

U, V come from Newton's identities: the power sums of O+ are the Ramanujan sums c_m(k/2) for even k
and g_k sqrt(d) for odd k, with g_k = sum over e | gcd(k, n/D) of e chi(k/e) chi(n/(De)) mu(n/(De)),
n = m or 2m (m odd or even), chi = (D/.). Examples: b = 5, m = 5: U = Y^2 + 3Y + 1, V = Y + 1,
A = 41 -+ 30 = 11, 71; b = 12, m = 6: U = Y + 1, V = 1, A = 13 -+ 6 = 7, 19; b = 7, m = 14:
U = (Y+1)^3, V = Y^2 + Y + 1, A = 512 -+ 399. The series: rho_O(2j) = 2 c_m(j), rho_O(odd) = 0 (not
split: a plain base-b series); rho_O(2j) = c_m(j), rho_O(k) = +- g_k / s for odd k (split).

*c0(r), in every case* (n the order of r, m the order of r^2; checked numerically, 214 classes):

| case | d(r) | abs c0(r) | nu(r) |
|---|---|---|---|
| D does not divide n, 4 does not divide n | 2 phi(m) | Phi_m(b) | P |
| D does not divide n, 4 divides n | 4 phi(m) | Phi_m(b)^2 | P^2 |
| 4 divides n and D divides n/2 (t in Q(zeta_n), no split) | 2 phi(m) | Phi_m(b) | P |
| D divides n, 4 does not divide n (m split, odd) | phi(m) | A+ or A- | P |
| D divides n, 4 divides n, D does not divide n/2 (m split, even) | 2 phi(m) | (A+-)^2 | P^2 |

*Table (computed): Phi_m(b), factored; "x / y" are the two halves A+ / A- of a split index.*

| m | b = 5 | b = 6 | b = 7 | b = 10 | b = 12 | b = 13 |
|---|---|---|---|---|---|---|
| 1 | 2^2 | 5 | 2*3 | 3^2 | 11 | 2^2*3 |
| 2 | 2*3 | 7 | 2^3 | 11 | 13 | 2*7 |
| 3 | 31 | 43 | 3*19 | 3*37 | 157 | 3*61 |
| 4 | 2*13 | 37 | 2*5^2 | 101 | 5*29 | 2*5*17 |
| 5 | 11 / 71 | 5*311 | 2801 | 41*271 | 22621 | 30941 |
| 6 | 3*7 | 31 | 43 | 7*13 | 7 / 19 | 157 |
| 7 | 19531 | 55987 | 29*4733 | 239*4649 | 659*4943 | 5229043 |
| 8 | 2*313 | 1297 | 2*1201 | 73*137 | 89*233 | 2*14281 |
| 9 | 19*829 | 19*2467 | 3*37*1063 | 3*333667 | 37*80749 | 3*1609669 |
| 10 | 521 | 11*101 | 11*191 | 9091 | 19141 | 11*2411 |
| 12 | 601 | 13 / 97 | 13*181 | 9901 | 20593 | 28393 |
| split m | 5 mod 10 | 12 mod 24 | 14 mod 28 | 20 mod 40 | 6 mod 12 | 13 mod 26 |
| more halves | 15: 181 / 1741 | 36: 73*541 / 55117 | 14: 113 / 911 | 20: 3541 / 27961 | 18: 1657 / 1801 | 13: 1803647 / 53*264031 |

## 4. No logarithm of an integer (Theorem N), and the test for a prime (Theorem P)

Let b >= 5 be a non-square (squares: remark 1). Write P_O = A_O / b^(w_O), w_O = |O|/2: either
A_O = Phi_m(b), w_O = phi(m), or A_O = A+-, w_O = phi(m)/2; m is the *index*. A prime factor pi of
A_O is *primitive* if it does not divide m. Four facts:

- F1. A prime pi | A_O does not divide b, and m = ord_pi(b) pi^j with j >= 0. (Standard.)
- F2. If j >= 1 and m >= 3, pi is the largest prime factor of m and pi^2 does not divide Phi_m(b).
  For m = 2 the only such prime is 2. (Lean: `nonprimitive_facts`.)
- F3. The two halves of a split index are coprime. (Proposition 2.)
- F4. Every A_O of index m >= 3 has a primitive prime. (This is step 1 of Theorem G: the proof of
  `goodPrimesB` gives a prime factor of c0(r) not dividing m, and c0(r) = +-A_O or A_O^2. For b = 5
  it is the lemma `primitiveHalves5` with Zsigmondy's theorem.)

So a prime pi not dividing b is primitive in exactly one part, its *home* H_pi, of index ord_pi(b),
and divides other parts only at the indices ord_pi(b) pi^j, j >= 1, once each (except that
v_2(b + 1) can be larger than 1).

**Theorem N.** Let b >= 5, b != 9. There is a function lambda on the primes with
lambda_pi > 0 for every prime, such that Lambda(y) = sum_pi lambda_pi v_pi(y) vanishes on
every P_O. Hence:
(i) if log y is in V_b then Lambda(y) = 0; so y is not an integer >= 2 nor the inverse of one;
(ii) q pi + q' log n is in V_b for no integer n >= 2 and rationals q, q' with q' != 0;
(iii) if b >= 2 is not a power of 2 or 3, no series sum_j b^(-Bj) sum_{i<=N} a_i/(Nj + i)
with rational a_i has the value q pi + q' log n, n >= 2 an integer, q' != 0.

*Proof.* Wanted: (W) sum_pi lambda_pi v_pi(A_O) = w_O for every part. Then, with any positive
lambda on the primes of b such that Lambda(b) = 1, Lambda(P_O) = w_O - w_O = 0. Construct lambda on
the primes not dividing b, part by part in order of the index.
The prime 2 (b odd): let a = v_2(b-1), u = v_2(b+1); one of them is 1, and b - 1, b + 1 are not both
powers of 2. Put lambda_2 = 1/a if b - 1 = 2^a, 1/u if b + 1 = 2^u, and 1/(2 max(a,u)) otherwise.
Then a lambda_2 <= 1 and u lambda_2 <= 1, with equality only for a part that is a power of 2.
A part O of index m: its non-primitive primes (and 2, if m <= 2) have weights already. Let omega be
w_O minus their contribution to (W). If omega > 0 and O has a primitive prime, share omega among the
primitive primes (equally, with multiplicity): (W) holds for O, all weights are positive, and
lambda_pi <= w_O <= phi(m) for the new primes. So it remains to see omega > 0. For m <= 2 this is
the choice of lambda_2 (omega = 0 exactly when the part is a power of 2, where nothing is left to
share). For m >= 3 the non-primitive part is 1 or one prime q, once (F2); m = n q^j with
n = ord_q(b) dividing q - 1, and lambda_q <= phi(n). For q = 2: m = 2^j >= 4 is not split (b is
odd) and w_O = 2^(j-1) >= 2 > 1 >= lambda_2. For q >= 5: w_O >= phi(m)/2 >= phi(n)(q-1)/2, which is
at least 2 phi(n). For q = 3: n <= 2, lambda_3 <= 1, and w_O >= 2 unless m is 3 or 6 and split; but
3 is never split, and 6 is split only for d = 3, and then 3 | b and 3 does not divide A_O. A
primitive prime exists by F4. This proves (W).
(i): by Theorem K_b, y^k is a product of powers of the P_O, so k Lambda(y) = 0; an integer n >= 2
has Lambda(n) > 0. (ii): the same with (a') of Theorem K_b. (iii): as in the proof of Theorem M
(`no_log_bailey`): the base is a^j with a >= 5 not a perfect power, and by the sub-series lemma
(`subseries_log_of_kummerHom`) the value would be in V_a. QED

*Remarks.* (1) Squares b = c^2, c >= 4: the same proof with the parts Phi_n(c), w = phi(n)/2 and
Bang's theorem for F4. It fails for c = 3: 2 = Phi_1(3) and 4 = Phi_2(3), and log 2, log 3 are
values of F_9. (2) Letting lambda vary on the primes of b gives Theorem M again. (3) The A_O are
multiplicatively independent: in a relation the part of largest index has a primitive prime that
nothing cancels (Lemma T).

**Lemma T (top part).** Let Y = prod A_O^(e_O), not all e_O zero, and let O have the largest index
m1 with e_O != 0. Then v_pi(Y) = e_O v_pi(A_O) != 0 for every primitive prime pi of O (F1, F3). So
by F4, unless the top part is b + 1 = 2^u, m1 = ord_pi(b) for a prime pi of Y: a relation for a
rational y only involves parts of index at most max(2, max ord_p(b)), p over the primes of y not
dividing b. This makes `decide` complete.

**Theorem P (finite test).** Let b >= 5 be a non-square and p a prime not dividing b. There
is a rational w with log p - w log b in V_b if and only if
- p = 2: b - 1 or b + 1 is a power of 2 (b - 1 = 2^a: w = 1/a; b + 1 = 2^u: w = 1/u);
- p odd, n = ord_p(b): the home part is H_p = p^x R, where R = 1, or n >= 3 and R = q is the
  prime dividing n and q passes the test, or n <= 2 and R = 2^v and 2 passes the test.
Then w is unique, w(p) = (w_H - v w(q)) / x (v = 1 for n >= 3), and 0 < w(p) <= phi(n); it
is the value lambda_p of every lambda as in Theorem N. So log p itself is never a value.

*Proof.* "If" is clear. "Only if": let p^k = prod A_O^(e_O). By Lemma T and F4 the top part is H_p,
alone at its index (F3), and all its primitive primes equal p; no other part of the relation
contains p, so k = x e_H, and R^(-e_H) is the product over the other parts: R = 1 (remark 3) or a
relation for q. The top part b + 1 = 2^u and the indices 1, 2 are checked by hand ((b-1)/2 and
(b+1)/2 are coprime). Uniqueness of w: remark 3. QED

Example: base 7, Phi_4(7) = 2 * 5^2 and b + 1 = 2^3 give w(2) = 1/3 and w(5) = (2 - 1/3)/2 = 5/6.
In base 5 the test gives the weights found numerically in Part VI of the note (1/2 for 2 and 3, ...).

## 5. Computations (exact integer arithmetic; evidence, not proof)

Bases B in {5, 6, 7, 10, 11, 12, 13, 14, 15}; counts are listed in this order.

- `selftest`: Gauss sums and the formula for g_k (646 cases); the orbits computed from the
  definition are the parts, with prod (t - s) = A (220 orbits); c0(r), d(r) (214 classes); **base 5:
  log(3/2), log(4/5), log(11/25) are values (series checked to 100 digits), log 2, log 3, log 5 are
  not**; bases 2, 3: the lists of primes below 100 of Theorems H and K3.
- `small B 1000`: for each of the 168 primes p < 1000, exact linear algebra on prime exponents over
  all parts of index up to max ord (complete by Lemma T): **log p is not a value, in all 9 bases**;
  the w(p) found by linear algebra alone agree with Theorem P.
- `primes B 100000000`: every prime below 10^8; w(p) is defined for 18, 15, 13, 12, 4, 12, 5, 5, 9
  primes and is positive each time. Base 10: 3, 11, 37, 101, 3541, 9091, 9901, 27961, 333667,
  909091, 39526741, 99990001 (unique primes of base 10, and three alone in a half).
- `index B 300`: parts of index <= 300 of the form p^x R, p of any size (probable primes above
  2^64): 49, 40, 38, 26, 22, 41, 22, 22, 25 parts; w > 0 always.
- `chains 3000 400`: bases 5..3000 (not 9), the parts of index <= 400 with a non-primitive prime or
  of index <= 2: 59707 parts; 4361 are p^x R with R > 1 (Phi_4(7) = 2 * 5^2, Phi_5(6) = 5 * 311,
  ...); w(p) is defined for 1030 parts, always positive, smallest 1/7 (b = 2186, b + 1 = 3^7). The
  chains m, m q^a never give w = 0: no sporadic configuration.
- `weights 200 20`, `weights 20 36`: the weight lambda of Theorem N on all primes of the parts of
  index <= 20 (bases 5..200) and <= 36 (bases 5..20): positive throughout. `list B 0 1000`: among
  the y = u/v > 1 with u, v <= 1000 and log y a value (1735, 255, 304, 49, 73, 96, 55, 35, 43 of
  them) there is no integer.
- With no theory (`baseb_explore.py probe`, lattice reduction on the sums of one period): base 10,
  period 12: the values among 13 targets are log 3 - (1/2) log 11, log 10 - log 11, log 7 + log 13 -
  2 log 11, and no single log p; base 7, period 8: log p - w log 7 for p = 2, 3, 5 with w = 1/3,
  2/3, 5/6; base 6, period 24: log 5, log 7, log 6, each minus (1/2) log 13. All as predicted,
  including the weight 5/6.

## 6. Which logarithms do have formulas

All y = u/v > 1 with u, v <= 150 and log y a value (complete, by `list`; height = max(u, v)).

**Base 10** (30 numbers; P1 = 9/10, P2 = 11/10, P3 = 111/100, P4 = 101/100, P6 = 91/100): 10/9,
11/9 = P2/P1, 11/10, 37/27 = P3/P1^2, 37/30 = P3/P1, 37/33 = P3/(P1 P2), 91/81, 91/90,
99/91 = P1 P2/P6, 100/81, 100/91, 100/99, 101/81, 101/90, 101/91, 101/99, 101/100, 110/81, 110/91,
110/101, 111/91, 111/100, 111/101, 111/110, 121/81, 121/90, 121/91, 121/100, 121/101, 121/111.

**Base 6** (52; generators 5/6, 7/6, 43/36, 37/36, 31/36, 13/36, 97/36): 6/5, 7/5, 7/6, 25/13,
30/13, 31/13, 31/25, 31/30, 35/13, 35/31, 36/13, 36/25, 36/31, 36/35, 37/13, 37/25, 37/30,
37/31, 37/35, 37/36, 42/13, 42/25, 42/31, 42/37, 43/13, 43/25, 43/30, 43/31, 43/35, 43/36, ...

**Base 7** (55; 6/7, 8/7, 57/49, 50/49, 43/49): 4/3, 7/6, 8/7, 14/9, 16/9, 19/9, 19/12, 19/14,
19/16, 25/18, 25/21, 25/24, 28/25, 32/21, 32/25, 38/21, 38/25, 43/27, 43/36, 43/42, 48/43, 49/27,
49/36, 49/43, 49/48, 50/27, 50/43, 50/49, 56/27, 56/43, ...

**Base 12** (35; 11/12, 13/12, 145/144, 7/12, 19/12): 11/7, 12/7, 12/11, 13/7, 13/11, 13/12, 19/7,
19/11, 19/12, 19/13, 121/49, 121/84, 121/91, 132/49, 132/91, 133/121, 133/132, 143/49, 143/84,
143/133, 144/49, 144/77, 144/91, 144/121, 144/133, 144/143, 145/49, 145/77, 145/84, ...

Shapes (each checked to 100 digits by `formula`; rho is one period, k = 1, 2, ...):
- base 10: log(11/9) = 2 sum_{j odd} 10^(-j)/j, rho = (0, 4, 0, 0); log(37/33), period 12,
  rho = (0, 2, 0, 6, 0, -4, 0, 6, 0, 2, 0, 0);
- base 10: log(3541/10^4), period 40, the first that uses odd k (sqrt(10)): rho =
  (-1,0,-1,-2,0,0,1,2,-1,0,1,-2,-1,0,0,2,1,0,1,8, 1,0,1,2,0,0,-1,-2,1,0,-1,2,1,0,0,-2,-1,0,-1,-8);
- base 12: log(19/7) = sum_{k odd} (12/k) 12^(-(k-1)/2)/k, where (12/k) is +1 for
  k = +-1, -1 for k = +-5 (mod 12), 0 otherwise; base 6: log(97/13) =
  2 sum_{k odd} (24/k) 6^(-(k-1)/2)/k; base 7: log(4/3) = 2 sum_{j odd} 7^(-j)/j.

Every y has numerator and denominator > 1 (Theorem N) and Lambda(y) = 0; in base 10 the weights
are 1/2, 1, 3/2, 2 for 3, 11, 37, 101, with 2 for 7 * 13 and 1 for 2 * 5.

## 7. A plan for Lean

*What exists* (`lean/Pilean/BaseB`): `goodPrimesB`; `exists_cofactor`, `cyclo_data` (c0(r) divides
a power of Phi_m(b)); `prime_facts_of_dvd_cyclotomic`, `nonprimitive_facts` (F1, F2);
`relationNatB_of_intRel` (only for y with primes dividing b); `subseries_log_of_kummerHom` (any y);
`Base5.log_mem_span_iff_pow_rat` (usable as it is). The method of `Base5/LogConverse.lean`
(explicit Gauss sum, zeta -> zeta^a, closed forms) does not carry over.

*Interface to fix first.* No orbits and no Aurifeuillian formulas in the statements:

    def nuSq (b : N) (r : C) : Q :=       -- nu(r)^2; a square, so no parity of the degree
      ((minpoly Z (tB b - r)).eval 0)^2 / b^((minpoly Z (tB b - r)).natDegree)
    def InBaseSpan (b : N) (y : Q) : Prop := exists k >= 1, exists S (e : C -> Z),
      (forall r in S, IsOfFinOrder r) and y^k = prod r in S, nuSq b r ^ e r
    theorem isFBValue_log_of_pow : InBaseSpan b y -> IsFBValue b (log y)         -- no Baker
    theorem isFBValue_log_rat_iff_pow (hB : BakerTheorem) (hb : 2 <= b) (hy : 0 < y) :
      IsFBValue b (log y) <-> InBaseSpan b y                                     -- K_b
    def PosWeight (b : N) : Prop := exists lam : N -> Q, (forall p, p.Prime -> 0 < lam p) and
      forall r, IsOfFinOrder r -> (sum over primes p, lam p * padicValRat p (nuSq b r)) = 0
    theorem posWeight (hb : 5 <= b) (hb9 : b != 9) : PosWeight b
    theorem not_isFBValue_mul_pi_add_log_nat (hB) (hb : 5 <= b) (hb9 : b != 9) (hn : 2 <= n)
      (hq' : q' != 0) : not IsFBValue b (q * pi + q' * log n)                    -- N

*Four independent pieces* (as for Theorem G: fix the statements, then work in parallel).

- (A) Values, no Baker. L = Q(zeta_N, t) inside C. Every embedding sigma of L in C has
  sigma(t) = +-t = chi_sigma t, so sum_sigma (chi_sigma sigma(r))^k is Tr(r^k) for even k and
  Tr(t r^k)/t for odd k. The pattern rho(k) = -Tr(r^k), resp. -Tr(t r^k)/b, is rational and
  periodic, and its sum is log |Norm_{L/Q}(1 - r/t)| (`Algebra.norm_eq_prod_embeddings`,
  `trace_eq_sum_embeddings`). No Galois group, no Gauss sum, no orbit.
- (B) The converse, from Baker. Generalize `relationNatB_of_intRel` to any y (conclusion
  v/u = y^(-m)) and take Norm_{L/Q} of the cleared relation. For A and B one needs
  Norm_{L/Q}(x) = ((-1)^d c0)^[L:Q(x)] for x = t - r: `Algebra.norm_norm`,
  `Algebra.norm_algebraMap`, `PowerBasis.norm_gen_eq_coeff_zero_minpoly`, and `minpoly Z` against
  `minpoly Q`. (Mathlib names from memory; to be checked against the pinned version.)
- (C) Arithmetic of c0(r), one structure of statements: coprime to b; F1, F2 (exist); F4 as "c0(r)
  has a prime factor not dividing m" (inside `hasGoodPrimeB_of_sizeCond`, to be exported; for b = 5
  from `primitiveHalves5`); F3 as: if r^2, r'^2 have the same order m and a prime not dividing 2m
  divides c0(r) and c0(r'), then nuSq b r = nuSq b r'. Proof with ideals as in `Support.lean`: a
  prime ideal P over that prime contains a root +-(t - s) of each minimal polynomial; s != +-s'
  would put m in P (s^2 - s'^2 is in P, and the 1 - rho, rho^m = 1, rho != 1, have product m); so
  the polynomials agree up to X -> -X.
- (D) Weights: lambda by strong recursion on the prime (home part, one smaller prime), the
  inequality omega > 0, then Theorem N in three lines. Theorem P is not needed for N. Then (iii) as
  `no_log_bailey` in `LogBase.lean`, with Theorem N in place of Theorem M.

*Where the difficulty is.* (1) Galois symmetrization: replaced by norm and trace over embeddings;
the only fact used about t is sigma(t)^2 = b. (2) Norms against constant terms: the exponent
[L:Q(x)] and the signs are harmless ("some power"; nuSq is a square). (3) The coprimality of the two
factors (F3): the one new arithmetic lemma, phrased with minimal polynomials. (4) The bookkeeping of
(D) at the indices 1, 2 and for the prime 2. Concrete values of c0(r) (Phi_m(b), the halves) are
needed only for examples.

## 8. Limits

- Theorems K_b, N, P and Proposition 2 are proved on paper here, in one session, and are not
  machine-checked; they rest on machine-checked inputs (Baker's theorem, good primes, the sub-series
  lemma) and on standard facts about Phi_m(b). No literature search was made.
- The computations are exact but bounded (primes below 10^8, indices up to 300 or 400, bases up to
  3000 for the chains); the primes above 2^64 are probable primes.
- Not covered: the bases 2^k, 3^k (there many log p are values) and F_9; irrational multiples;
  degree >= 2; non-integer bases.