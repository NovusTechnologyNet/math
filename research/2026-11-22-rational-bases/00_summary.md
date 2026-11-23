# Rational bases p/q: which have degree-1 BBP-type formulas for pi

22-23 November 2026. Numerics and paper proofs; no Lean in this pass. Written in one sitting,
reviewed by nobody. Program: `python/ratbase_explore.py` (new; `selftest`: 38 checks, all ok).
The formulas (a), (b) of `research/2026-11-22-wide/P03_algebraic_bases.md` are machine-checked
elsewhere (`lean/Pilean/RatBase`); what is in print: `F3_rational_bases_literature.md`, same folder.

## 1. The question and the answer

p > q >= 1 coprime integers, beta = p/q, t = sqrt(p/q). The class F_beta:

    S(rho) = sum over k >= 1 of rho(k) (q/p)^floor(k/2) / k,     rho rational and periodic,
    S(rho) = - sum over roots of unity r of D_r Log(1 - r/t),    1 - r/t = x_r / sqrt(p),
    x_r = sqrt(p) - r sqrt(q),    x_r x_(-r) = p - r^2 q,
    product over the primitive m-th roots s of (p - s q) = Phi_m(p, q)  (homogeneous cyclotomic).

**Theorem R (rational bases, step 2).**
1. A non-zero rho with S(rho) = gamma pi, gamma algebraic (0 included), exists if and only if
   beta is one of 2, 3, 4, 3/2, 4/3. For every other rational beta > 1 the numbers 2 pi i and
   Log(1 - r/t), r over all roots of unity, are linearly independent over Q: no zero relation, no
   algebraic multiple of pi, at most one formula for a number, every non-zero value transcendental.
2. The five classes: the space of such rho has dimension 13, 3, 2, 3, 2 and period 120, 12, 6,
   24, 12 for beta = 2, 3, 4, 3/2, 4/3; the gamma that occur are Q sqrt 3 for 3, 4 and 4/3, and Q
   for 3/2 (base 2: a space of dimension 6 over Q); the zero relations have dimension 7, 2, 1, 2, 1.
3. A non-zero rational multiple of pi is a value of F_beta exactly for beta = 2 and beta = 3/2.

**Theorem L' (every B and N).** Let beta be rational, |beta| > 1. A series
sum_j beta^(-Bj) sum_{i=1..N} a_i/(Nj+i) with rational a_i and B, N >= 1 whose value is a non-zero
rational multiple of pi exists if and only if |beta| is a power of 2 or a power of 3/2. In a base
(3/2)^B such a formula needs 12 | B: the smallest base is (3/2)^12, formula (a).

The conjecture of the brief holds in both parts. Status (section 8): proved on paper, given
Baker's theorem, up to finite computations; base 2 is taken from Theorem C of the note.

## 2. Numerics (python/ratbase_explore.py)

### 2.1 The table

Probe: integer relations among 2 pi i and the N numbers Log(1 - r sqrt(q/p)), r^N = 1, with the
guard and the certificate of `baseb_explore.py` (30 bits per number + 300; a row counts only if
it vanishes with 400 more bits; every relation with sum of |coefficients| below the bound is in
the span found). Each relation is then checked exactly in Z[zeta], has exponent sum 0 and support
inside R0 (3.2). The rank is the dimension of the rational patterns of period N with value in
(algebraic numbers) pi (Baker and descent). "Values": the quadratic characters of
Gal(Q(zeta_N, t)/Q) on which the coefficient of 2 pi i does not vanish.

`table 16 18`: all 79 coprime pairs with p <= 16, N = 24, 48, 60, 72, 84, 96, 120, and lcm(f, 4)
when it is at most 168 and f does not divide 120 (27 pairs; f the conductor of Q(sqrt(pq))):
580 runs, 689 s on 18 cores, smallest bound 2^57.

| p/q | exceptional classes (order, class: norm) | rank at the seven N | values | zero rel. | period |
|---|---|---|---|---|---|
| 2 | 1: 1, 2: 1, 8+: 1, 12: 3, 24+: 1, 40+: 5^2 | 8, 8, 3, 8, 3, 8, 13 | pi, pi sqrt 2, sqrt 3, sqrt 5, + 2 | 7 | 120 |
| 3 | 1: 2, 2: 2, 4: 2^2, 12+: 1 | 3 | pi sqrt 3 | 2 | 12 |
| 4 | 1: 1, 6: 3 | 2 | pi sqrt 3 | 1 | 6 |
| 3/2 | 1: 1, 2: 1, 24+: 1 | 3, 3, 0, 3, 0, 3, 3 | pi | 2 | 24 |
| 4/3 | 1: 1, 2: 1, 12+: 1 | 2 | pi sqrt 3 | 1 | 12 |
| the other 74 | only orders 1, 2, 4 (p - q or p + q a power of 2), or none (40 pairs) | 0 | - | - | - |

`extra`: 17/16, 20/19, 21/20, 25/24, 49/48, 81/80, 100/99, 1000/999, 27/8, 32/27, 64/27, 125/64,
243/32, 256/243, 16/9, 25/9, 17, 18/7, 24/5, 27/2 at N = 24, 48, 60, 120: rank 0, bounds 2^60.
`scan 40 400`: exact norms of all classes of order <= 400 for the 489 pairs with p <= 40; a class
without a good prime outside the fourth roots exists for 2, 3, 4, 3/2, 4/3 only.

### 2.2 Base 3/2 in full

Put z = exp(i pi/12), t = sqrt(3/2). Six roots are exceptional, and all six x_r are units:

    x_1 x_(-1) = (sqrt 3 - sqrt 2)(sqrt 3 + sqrt 2) = 1,
    x_z = ((sqrt 3 - 1)/2)(1 - i),   x_(z^5) = ((sqrt 3 + 1)/2)(1 - i),   x_z x_(z^5) = -i,

and the conjugates x_(1/z), x_(1/z^5). With L(r) = Log(1 - r/t): L(z) - L(1/z) = L(z^5) - L(1/z^5)
= -i pi/2 and L(1) + L(-1) - L(z) - L(z^5) = i pi/2. Three patterns, written for k = 1, ..., 24:

    P = (1, 1, 0, 0, 1, 2, 1, 0, 0, 1, 1, 0, -1, -1, 0, 0, -1, -2, -1, 0, 0, -1, -1, 0),
    Y = (1, 0, -2, -3, -1, 0, -1, -3, -2, 0, 1, 0, -1, 0, 2, 3, 1, 0, 1, 3, 2, 0, -1, 0),
    Z = (-1, 2, 0, 1, -1, 2, 1, 3, 0, 2, 1, 4, 1, 2, 0, 3, 1, 2, -1, 1, 0, 2, -1, 0).

**Theorem C(3/2).** Let rho be rational and periodic. S(rho) is an algebraic multiple of pi if and
only if rho = a P + b Y + c Z with a, b, c rational, and then S(rho) = a pi/2. So:

- every such series has period 24; the patterns of period N form a space of dimension exactly 3
  when 24 | N, and there are none otherwise;
- the multiples of pi that occur are the rational ones (not pi sqrt 2, pi sqrt 3, pi sqrt 6);
- the zero relations are the b Y + c Z: dimension 2;
- a formula for a non-zero multiple of pi has at least 14 non-zero terms per period (7 per 6
  digits of base 3/2), with equality exactly for the multiples of P, P + Z, P - Z;
- no such pattern has a period below 24, and none is supported on even k.

Formula (a) is S(P/2) = pi/4 (Lean: `RatBase.pi_base_three_halves`). Proof: section 4. Checks
(`describe 3 2`): the sums to 60 digits; rank 3 with pi the only value at N = 24, 48, 72, 120; the
theory-free probe (pi, pi sqrt 2, pi sqrt 3, pi sqrt 6 and the class sums) agrees at these periods.

### 2.3 Base 4/3 in full

Put w = exp(i pi/6), t = 2/sqrt 3. Four roots are exceptional:

    x_1 x_(-1) = (2 - sqrt 3)(2 + sqrt 3) = 1,     x_w = 2 - sqrt 3 w = exp(-i pi/3)  (a root of unity).

Relations: L(w) - L(1/w) = -2 pi i/3 and L(1) + L(-1) - L(w) - L(1/w) = 0 (that is 1 - 3/4 = (1/2)^2).

    G  = (1, 2, 2, 2, 1, 0, -1, -2, -2, -2, -1, 0),        S(G) = 4 pi sqrt(3)/9,
    Z' = (-3, 2, 0, 6, 3, 8, 3, 6, 0, 2, -3, 0),           S(Z') = 0.

**Theorem C(4/3).** S(rho) is an algebraic multiple of pi if and only if rho = a G + b Z', and then
S(rho) = 4a pi sqrt(3)/9. Period 12; dimension exactly 2 for 12 | N, else 0; the multiples that
occur are Q pi sqrt 3 (pi itself is not a value); zero relations: Q Z'; at least 8 non-zero terms
per period, attained exactly by the multiples of 3G + Z' = (0, 8, 6, 12, 6, 8, 0, 0, -6, -4, -6, 0)
and 3G - Z'. Formula (b) is S(9G/4) = pi sqrt 3 (Lean: `RatBase.sqrt_three_pi_base_four_thirds`;
in print in an equivalent form, see F3). Checks (`describe 4 3`): as for 3/2, N = 12, 24, 36, 60, 120.

### 2.4 Other steps (command `steps`)

2 pi i and Log(1 - r (q/p)^(1/n)), r^N = 1, N up to 96. Base 3/2: n = 1, 3: rank 0; n = 4 (N = 48,
96), 6 (N = 72), 8 (N = 96): rank 3, all lifted from step 2. Base 4/3: n = 1, 3: rank 0; n = 4, 6:
rank 2, lifted. 9/4 and 16/9: rank 0 at step 2, the class of 3/2, 4/3 at step 4. 5/2, 5/3, 5/4,
7/5 at some of the steps 1, 3, 4, 6: rank 0. So nothing outside step 2 was found in these bases
(base 3 has two series at steps 4 and 6). 40 runs; evidence only.

## 3. Good primes for sqrt(p) - r sqrt(q)

### 3.1 Three facts, and the vocabulary

(F1) x_r is an algebraic integer. A prime ideal P (of the ring of all algebraic integers) that
contains a prime factor of p contains sqrt p and not sqrt q, so it contains no x_r; the same for
q. So the x_r are prime to pq.
(F2) An integer relation is prod (1 - r/t)^(z_r) = root of unity, that is
prod x_r^(z_r) = xi sqrt(p)^(sum z_r). At a prime above p, (F1) gives sum z_r = 0.
(F3) If P contains x_r and x_r' (r != r') and a prime l not dividing q, it contains
(r' - r) sqrt q, hence 1 - r'/r: the order of r'/r is a power of l.

A *good prime* for r (of order n): a prime ideal containing x_r and a rational prime l not
dividing 2pqn. *Class*, *norm*, *exceptional*, *R0*: as in `baseb_explore.py`, with d the
squarefree part of pq (docstring of the program). The classes are the Galois orbits of
r/t = r sqrt(pq)/p. Two classes of roots of order n occur exactly when d > 1, f | n and not
(4 | n and f | n/2); then m = ord(r^2) is an odd multiple of d or of 2d.

### 3.2 Support

**Every integer relation is supported on R0.** As in Part III, Step 2 of the note: take r in the
support, outside R0, of largest order among those; a good prime P of r contains, by (F3), only
x_r' with ord r' = n l^a > n; such r' lie in R0, r is the l'-part of r', so r is in R0 by the
closure. So P contains no other x_r' of the relation, and z_r = 0 (by (F1) the valuation at P
sees the x_r only).

### 3.3 A good prime from a size condition (generalizes Step 1 of Theorem G)

Let r have order n, r^4 != 1, m >= 3 the order of r^2, k = phi(n)/phi(m) (1 or 2), q0 the largest
prime factor of m, g = q0 if q0 divides Phi_m(p, q) and g = 1 otherwise. Two conditions:

    SC(p, q, m):   Phi_m(p, q) > g (sqrt p + sqrt q)^phi(m)       (`SizeCond` with sqrt b + 1 replaced),
    SC2(p, q, m):  Phi_m(p, q) > g U_m(p, q),
                   U_m(p, q) = product over the primitive m-th roots s of (p + q + sqrt(2pq(1 + Re s)))^(1/2).

U_m <= (sqrt p + sqrt q)^phi(m), so SC implies SC2.
**Proposition S.** If SC2(p, q, m) holds, some prime ideal contains x_r and a prime l = 1 (mod m).
Such an l is odd and prime to pqn: a good prime.

*Proof.* One square root: u = sqrt(pq), y = u - q r = sqrt(q) x_r, an algebraic integer. Let mu
be its minimal polynomial over Z, delta its degree, c0 = mu(0).
(a) A prime l dividing c0 lies under a prime ideal containing y (`hasPrime_of_dvd_minpoly_eval_zero`,
unchanged). If l does not divide q, the ideal contains x_r.
(b) For G in Z[X], S_G(z) = G(u - qz) G(-u - qz) is in Z[z]: G(+-u - qz) = A(z) +- u B(z) by
induction, S_G = A^2 - pq B^2. In the same way
T(z) = Phi_n(u - z, q) Phi_n(-u - z, q) = product over the primitive n-th roots r' of ((z + q r')^2 - pq)
is monic in Z[z] of degree 2 phi(n). Its roots are the 2 phi(n) different numbers +-u - q r'
(u - q r' = -u - q r'' would give |r'' - r'| = 2t > 2), T(y) = 0, and T(0) = q^phi(n) Phi_m(p, q)^k.
So mu divides T. And S_mu(r) = 0, so Phi_n divides S_mu: for every r', mu vanishes at u - q r' or
at -u - q r'. Hence delta >= phi(n), and the cofactor H = T/mu has at most one root in each pair
{u - q r', -u - q r'}.
(c) Divide every root by sqrt q: C = |c0| q^(-delta/2) is the product of the |+-sqrt p - r' sqrt q|
over the roots of mu, C' the same for H, and C C' = Phi_m(p, q)^k. C^2 and C'^2 are rational
numbers and algebraic integers, hence positive integers. So a prime factor l of C^2 divides
Phi_m(p, q), does not divide pq, divides c0, and by (a) lies under a prime ideal containing x_r.
Size: the larger of |sqrt p +- r' sqrt q|^2 is p + q + 2 sqrt(pq) |Re r'| > 1, |Re r'|^2 =
(1 + Re r'^2)/2, and r' -> r'^2 is k to 1 onto the primitive m-th roots. So C' <= U_m(p, q)^k and
C >= (Phi_m(p, q)/U_m(p, q))^k.
(d) Primes of Phi_m(p, q), m >= 3 (the lemma behind Zsigmondy's theorem, for coprime p, q): a
prime factor l not dividing m has ord_l(p/q) = m, so l = 1 (mod m); a prime factor dividing m is
q0, and q0^2 does not divide Phi_m(p, q). If no l = 1 (mod m) divides C^2, then C^2 is a power of
q0 dividing Phi_m^(2k), so C <= g^k, against (c) and SC2. QED
(New compared with the integer case: sqrt(pq) for sqrt b, the homogeneous T, C^2, and U_m.)

### 3.4 Where the size condition holds

**Lemma (lower bounds), m >= 2.**
(M) Phi_m(p, q) >= (p^2 - pq + q^2)^(phi(m)/2). Indeed |p - sq|^2 = (p - q)^2 + pq |1 - s|^2, the
product of the |1 - s| is Phi_m(1) >= 1, and prod (a_i + b_i)^(1/N) >= prod a_i^(1/N) + prod b_i^(1/N)
(the arithmetic-geometric inequality applied to the a_i/(a_i + b_i) and to the b_i/(a_i + b_i)).
(E) Phi_m(p, q) = p^phi(m) prod_{d | m} (1 - (q/p)^d)^mu(m/d) >= p^phi(m) prod_{d >= 1} (1 - (q/p)^d).

**Proposition (proved).** For p >= 16, SC(p, q, m) holds for every m >= 3 and every q.
Proof: p^2 - pq + q^2 >= 3p^2/4 and (sqrt p + sqrt q)^2 < 4p, so by (M)
Phi_m(p, q)/(sqrt p + sqrt q)^phi(m) > (3p/16)^(phi(m)/2) >= 3^(phi(m)/2) >= phi(m) + 1 >= q0.

**p <= 15 (computed; `size 16`).** For each pair, (M) or (E) and q0 <= phi(m) + 1 give a number F
with the condition true for phi(m) > F; every m with phi(m) <= F (so m <= 2F^2) is tested, with
25 to 60 guard digits. All coprime p > q with p <= 16 (79 pairs):

- SC holds for every m >= 3 for 64 pairs. It fails for infinitely many m exactly for 2/1 and 3/2
  (p < sqrt p + sqrt q, and Phi_m(p, q) < p^phi(m)/prod(1 - (q/p)^d)). It fails at 29 triples:
  3/1: m = 4, 6, 8, 20, 39, 42. 4/1: 3, 10. 4/3: 6, 10, 12, 14, 15, 20, 55, 78. 5/1: 6. 5/2: 3, 14.
  5/4: 6, 18. 6/5: 22. 7/2: 6. 7/3: 10. 7/5: 6. 8/7: 6, 10. 11/7: 6. 11/10: 6.
  (For q = 1, p >= 5: only (5, 1, 6), as in the note. With g = q0 always there are many more.)
- SC2 holds for every m >= 3 for 67 pairs. It fails for infinitely many m only for 2/1
  (p^2 < p + q + sqrt(2pq)). For 3/2 it holds for phi(m) >= 274 (527 values of m tested below).
  It fails at 27 triples: 3/2: m = 6, 10, 12, 14, 15, 21, 22, 42, 50, 52, 57. 3/1: 4, 6, 20.
  4/1: 3, 10. 4/3: 6, 14, 20. 8/7: 6, 10. 5/1, 5/4, 7/2, 7/5, 11/7, 11/10: 6.

### 3.5 The triples that are left

*Direct look* (computed): the norm of each class at these triples is factored. Every class has a
prime factor not dividing 2pqn, except four: 3/1, order 12, class + (norm 1); 4/1, order 6
(norm 3); 4/3, order 12, class + (norm 1); 3/2, order 24, class + (norm 1). A prime factor l of
the norm of the class of r, not dividing 2pqn, gives a good prime for r: a prime ideal above l
contains a conjugate of +-x_r (Galois group of Q(zeta_n, sqrt p, sqrt q)).

*Exact cofactor test* (computed; no Galois theory). In (c), C'^2 is a product of numbers
p + q -+ 2 sqrt(pq) Re r', at most one sign for each r', the same choice for r' and its conjugate;
and if r has no good prime, C' = Phi_m^k/C with C^2 = q0^j, 0 <= j <= 2k. The program lists all
3^(phi(n)/2) selections. Of the 27 triples where SC2 fails it was run at 24: no selection has
such a product (smallest gap of logarithms 0.018), except one selection at each of the four
triples just named. Not run (too many selections): 3/2 at m = 50, 52, 57. Control in base 2: a
match at m = 4, 6, 12, 20, at no other m tested. For m = 6 there is a proof by hand: the factors are
A +- B, A = p + q, B = sqrt(3pq), (A + B)(A - B) = Phi_6(p, q); if 3pq is not a square, C^2 rational
forces C^2 = Phi_6^a with a >= 2, so every prime factor of Phi_6(p, q) is under x_r, and one of
them is not 3 unless (p, q) = (2, 1).

**Consequence.** For coprime p > q >= 1 other than (2, 1): every root of unity r with r^4 != 1 has
a good prime, except the roots of order 12 with x_r a unit for 3/1 and 4/3, of order 6 for 4/1,
of order 24 with x_r a unit for 3/2. (Base 2: 20 exceptional roots, Part III of the note.)

### 3.6 The classical route, and why the list is what it is

One class (m >= 3): Zsigmondy gives a primitive prime l of p^m - q^m unless (p, q, m) = (2, 1, 6);
a prime ideal above l contains some x_r' with ord(r'^2) = m, and these are conjugate up to sign.
(For p = a^2, q = b^2: x_r = a - rb, norm Phi_n(a, b); the exception is base 4, order 6.) Two
classes: the norms satisfy N+ N- = Phi_m^k and |log(N-/N+)| <= 2 sqrt(f) t/(t^2 - 1), from the bound
sqrt(f) gcd(j, n) for the Gauss sums of chi over the units modulo n (from memory; checked
numerically by `aurif`). For 3/2 this and (M) give a good prime in both classes of order 24j
for odd j >= 5; j = 3 is computed (norms 181^2, 37^2 73^2). A second proof for base 3/2.
The exceptions are those of Schinzel's theorem (1962) on a^n - b^n with n/(eta k(ab)) an odd
integer: as I recall the list, (a, b, n) = (2, 1, 4), (2, 1, 12), (2, 1, 20), (3, 1, 6), (4, 1, 3),
(4, 3, 6), (3, 2, 12) for a > b > 0, n >= 3. **From memory, not checked against the paper** (the
project could not obtain it: research/2026-11-23-schinzel). It matches every computation here.

## 4. The four roots, and the proofs of Theorems R, C(3/2), C(4/3)

**Four roots.** Let a relation be supported on 1, -1, i, -i with exponents z1, z2, z3, z4. Absolute
values: (sqrt p - sqrt q)^(2 z1) (sqrt p + sqrt q)^(2 z2) (p + q)^(z3 + z4) = p^(z1+z2+z3+z4).
*pq not a square.* omega = (sqrt p + sqrt q)/(sqrt p - sqrt q) = (p + q + 2 sqrt(pq))/(p - q) has
conjugate 1/omega and omega > 1, so no power of it is rational: z1 = z2. A prime factor of p divides
neither p - q nor p + q: 2 z1 + z3 + z4 = 0. Then ((p - q)/(p + q))^(2 z1) = 1, so z1 = 0.
*p = a^2, q = b^2.* A prime factor of a gives sum z = 0; a^2 + b^2 has an odd prime factor, which
does not divide a^2 - b^2: z3 + z4 = 0; then ((a - b)/(a + b))^(2 z1) = 1.
In both cases the relation reads w^(z3) = root of unity, w = x_i/x_(-i), w + 1/w = 2(p - q)/(p + q).
If z3 != 0 this is an integer strictly between 0 and 2, so p = 3q. **A relation supported on the
fourth roots exists only in base 3** (there w is a sixth root of unity: Theorem C3).

**Theorem R.** By 3.5, for a base outside {2, 3, 4, 3/2, 4/3} the set R0 lies in the fourth roots
(the closure only adds l'-parts for odd l), so every relation is supported there, and there is
none; Baker's theorem then gives part 1 as in Part VI of the note. Bases 2 and 3: Theorems C and
C3. Base 4 is inside base 2; directly, R0 = {1, -1, v, 1/v} with v of order 6, x_1 = 1, x_(-1) = 3,
(2 - v)(2 - 1/v) = 3 and 2 - v = sqrt(3) exp(-i pi/6): rank 2.

**Theorem C(3/2).** R0 is the six roots of 2.2. For a relation on R0, absolute values give
(z_1 - z_(-1)) log(sqrt 3 + sqrt 2) = (1/2)(z_z + z_(1/z) - z_(z^5) - z_(1/z^5)) log(2 - sqrt 3),
and the two logarithms are independent over Q (apply sqrt 2 -> -sqrt 2 to a relation between the
two units). With (F2): three independent linear conditions on six exponents, so the lattice has
rank at most 3, and the three relations of 2.2 are independent. By Baker's theorem D is a
combination of them with algebraic coefficients; its twisted pattern c(k) = sum D_r r^k is a
combination of 2 sin(k pi/4) cos(k pi/6), 2 cos(k pi/4) sin(k pi/6) and
1 + (-1)^k - 2 cos(k pi/4) cos(k pi/6), and rho(k) = c(k)/t^(k mod 2): the first and third give P
and Z, sqrt(3) times the second gives Y; a rational pattern in the complex span of P, Y, Z is in
their rational span. The value is (i pi/4)(D_z - D_(1/z) + D_(z^5) - D_(1/z^5)): pi/2 for P, 0 for Y
and Z. The count of terms and the periods are a finite computation on the three patterns.
**Theorem C(4/3)**: the same with four roots; conditions z_1 = z_(-1) and sum z = 0, rank 2;
sequences sin(k pi/6) and 1 + (-1)^k - 2 cos(k pi/6); value (pi i/3)(D_w - D_(1/w)), in Q pi sqrt 3.

## 5. Every B and N: the sub-series lemma and the Kummer step for p/q

The reductions of Part VII of the note use the base only through c = beta^(1/n) and the fact that
the numbers 1 - r/c are algebraic. I went through them with beta = p/q:

1. *The base.* beta = a^j with a > 1 rational and not a perfect power in Q; j is the gcd of the
   exponents v_l(p/q) over the primes l dividing pq. "Not a perfect power" becomes: this gcd is 1.
   (4/3 is not a perfect power; 9/4 and 27/8 are.)
2. *Bailey's form is a series of step n* = N/gcd(B, N): the identity is formal in the base.
3. *The sub-series lemma*: unchanged (sigma(c) = eta c, sigma fixes the roots of unity and the
   rational coefficient of pi). For beta = a^j the modulus is n1/gcd(n1, j), as for integers.
4. *The Kummer step.* L = Q(zeta_(Mn)), f the minimal polynomial of c over L, of degree d: the
   constant term of f is a root of unity times c^d, so c^d is in L; every conjugate of the real
   number c^d is real, so c^(2d) is rational; (c^(2d))^n = (p/q)^(2d), and if p/q is not a perfect
   power then n | 2d (compare exponents at each prime). It goes through; c need not be integral.
5. *The sub-series is in F_a.* By Theorem R, part 3, a is 2 or 3/2 (a = 3 and a = 4/3 give
   multiples of pi sqrt 3 only; 4 is a perfect power).

This is the "only if" of Theorem L'. "If": regroup the BBP formula, or formula (a), in blocks.
The condition 12 | B: the sub-series is a pattern of F_(3/2) of period dividing 2B with non-zero
value, and by Theorem C(3/2) its period is a multiple of 24. Not covered, as for integer bases:
algebraic multiples and zero relations at steps n >= 3 (2.4: nothing found).

## 6. Negative bases, bases between 0 and 1

*Negative.* (-beta)^(-Bj) is beta^(-Bj) for even B. For odd B, pairing j = 2j', 2j' + 1 gives the
base beta^(2B) with 2N terms, a'_i = a_i, a'_(N+i) = -beta^(-B) a_i, still rational; and a formula
of base beta^B is one of base (-beta)^(2B). In the class itself (-q/p)^floor(k/2) =
(-1)^floor(k/2) (q/p)^floor(k/2), so F_(-beta) = F_beta. Theorems R and L' hold with |beta|.
*0 < |beta| < 1.* The block b_j = sum a_i/(Nj+i) is a non-zero rational function of j when a != 0,
so beta^(-Bj) b_j does not tend to 0: the series diverges. Written with positive exponents,
sum beta^(Bj) (...), it is the base 1/beta > 1. (|beta| = 1 is not a base.)

## 7. Lean plan

Integer development: `lean/Pilean/BaseB`; `lean/Pilean/RatBase` has `seriesTermRat`,
`baileyBlockRat` and the two formulas.

- *By substitution* (b becomes (p, q); sqrt b becomes u = sqrt(pq), or the pair sqrt p, sqrt q;
  Phi_m(b) becomes `TauCeti.homogeneousCyclotomic m p q`, through which `Reduction.lean` already
  gets its prime facts): `Defs`, `Symmetrize` (`exists_split` with G(u - qz) = A + uB; the step X
  gives (pq B - q X A, A - q X B)), `ReductionCyclo` (T(0) = q^phi(n) Phi^k), `Reduction`,
  `GoodPrimes`, `Support` (add (F1), (F2)), `TheoremG`, `Subseries`, `SubseriesAux`, `Reindex`,
  `BaileyForm`, `NegativeBase`, `NoPi`.
- *Small new lemmas:* `ReductionRoots.exists_cofactor` (the factor sqrt q: state it for the
  integers C^2, C'^2; "a rational algebraic integer is an integer"); `Classification` (the four
  roots as in section 4); `Kummer` (the last step, and `NotPerfectPower`, for a rational).
- *New work.* (1) `Size`: Mathlib's (b - 1)^phi(m) < Phi_m(b) has no homogeneous form; prove (M),
  or the cruder (p - q)^phi(m) and (pq)^(phi(m)/2), which give SC for p >= 20; then a table for the
  small p (a threshold on phi(m) and a list of m per pair, by `norm_num`). (2) The left-over
  triples: 26 with SC; with SC2 only 8 outside the five bases, seven with m = 6 (the lemma of
  3.5) and (8, 7, 10) (cofactor test, 81 selections). U_m has the closed upper bound
  (p + q + sqrt(2pq(1 + mu(m)/phi(m))))^(phi(m)/2), from the sum mu(m) of the primitive roots.
  (3) Base 4/3, needed for Theorem L' because relations exist there: good primes outside four
  roots (SC2 leaves m = 6, where the other class is 3 - omega of norm 13, and m = 14, 20), then
  Theorem C(4/3), a smaller copy of `Base3/Dimension.lean`. (4) Base 3/2 is not needed for
  Theorem L' beyond the formula. Its classification is the hard part: SC fails for all large m,
  SC2 holds only for phi(m) >= 274. More realistic: Zsigmondy for (3, 2) and an Aurifeuillian
  lemma for Phi_(12j)(3, 2), the analogue of `primitiveHalves3`, in Z[zeta_24n], where
  i x_r = sqrt(-3) - r sqrt(-2) is a polynomial in one root of unity (`hasPrime_conj` applies).

**Main obstacle:** (2) and (4), the roots where size alone does not decide. The integer case had
one such triple, (5, 1, 6), and it took a development of its own (Base5).

## 8. What is proved, what is computed, where the gaps are

*Proved on paper here* (given Baker's theorem, and for (d) the lemma behind Zsigmondy):
(F1)-(F3), the support theorem, Proposition S, the lemma (M), (E), SC for p >= 16, the four roots,
the reduction of Theorem R to good primes, the lattices of 3/2 and 4/3 on R0 (ranks exactly 3 and
2), the patterns P, Y, Z, G, Z' and their values, the m = 6 lemma, sections 5 and 6.
*Computed:* for p <= 15 the failures of SC and SC2 (thresholds in double precision with margins,
tests with 25 to 60 guard digits, no interval arithmetic); the norms of the direct look; the
cofactor tests; the term counts and periods of 2.2, 2.3; all lattice ranks (evidence only).

*Gaps and reservations.*
1. Base 2 is not re-proved: SC2 fails there for all large m; Theorem C of the note is used.
2. Base 3/2 at m = 50, 52, 57: cofactor test not run; these rest on the direct look (one class, a
   primitive prime found by factoring, Galois conjugation) or on 3.6. The other class at an
   exceptional m (norms 7^2, 7, 13^2, 61^2) also gets its good prime by conjugation.
3. Section 3.6 uses two classical statements from memory (the Gauss sum bound, Schinzel's list).
   The main line (3.3 to 3.5) does not depend on them.
4. Steps n >= 3: only rational multiples of pi are covered (Theorem L'); zero relations and
   algebraic multiples are open there, as for integer bases.
5. Novelty was not assessed here: see F3 (formula (b) and the construction are in print; no
   formula for pi in base 3/2 and no classification of bases were found).

*Found on the way.* (i) The size condition of Theorem G cannot treat base 3/2 (it fails for every
large m); the bound U_m brings it back, up to 11 values of m. (ii) The cofactor has finitely many
possible sizes: a finite test replaces Galois theory at the left-over triples. (iii) Bases with
x_1 a unit (25/24, 49/48, 81/80) have no relation: units alone do not make formulas.
