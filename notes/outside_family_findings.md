# Outside the family F: do other binary BBP-type families give a cheaper formula for pi?

Working note, 21 November 2026. Written in one sitting, checked only by the programs
named here. Nothing in this note has been reviewed by anyone else.

## The question

Part III of pi_formula_theorem.md settles the family

    F = F_2 :  sum over k >= 1 of rho(k) * 2^(-floor(k/2)) / k,     rho rational, periodic,

and finds that the cheapest formula for pi in it costs 2 * 7/24 = 0.5833 (Euler's
costs 0.6667). The other degree-1 binary families are

    F_n :  S(rho) = sum over k >= 1 of rho(k) * 2^(-floor(k/n)) / k,     x = 2^(-1/n).

**These are all of them.** A BBP-type formula sum_j 2^(-Bj) sum_{i=1..N} a_i/(Nj+i) is a
series of F_v with v = N / gcd(B, N), supported on the multiples of B / gcd(B, N).
And F_n is contained in F_(n n') (replace k by n' k).

Cost, comparable across families: a prime p first enters a denominator at k = s*p and
is needed up to n*m/s for a window at bit m, so

    cost(F_n) = n * mean(1/s)      (mean over the classes of primes modulo the period).

## Answer

**No.** No series in any F_n for a non-zero rational multiple of pi is cheaper than
0.5833, and for odd n there is no such series at all. The reason is a short general
argument (below), and every computation I ran agrees with it.

What does exist outside F, and is new to this project:

* new multiplicative relations in F_3, F_4, F_6, F_8, F_9, F_10, F_12;
* series for irrational multiples of pi, for example

      pi * sqrt(3) * 2^(1/3) = 9 * sum over j >= 0 of 4^(-j) * ( 1/(6j+1) - 1/(6j+4) )

  (checked to 40 digits by direct summation);
* new series whose value is exactly zero, in F_4 (period 240), F_6 (periods 72 and
  120) and F_12 (period 144).

None of these helps with pi: see "Why the new series cannot help".

## The argument (sub-series lemma)

Let n1 = n/2 if n is even, n1 = n if n is odd.

**Lemma.** Let rho be rational and periodic, and suppose S(rho) = q*pi with q rational.
Then for every n1-th root of unity eta,

    sum over k of  eta^k * rho(k) * 2^(-floor(k/n)) / k  =  q*pi.

Averaging over eta: **the sub-series over k = 0 (mod n1) alone already equals q*pi,
and the rest of the series sums to zero.**

*Proof.* Put c = 2^(1/n), x = 1/c. Then 2^(-floor(k/n)) = c^(k mod n) * x^k, and with
d_r = (1/P) sum_k rho(k) c^(k mod n) r^(-k) (r over the P-th roots of unity, n | P),

    S(rho) = - sum_r d_r * Log(1 - r x),         d_r in Q(c, zeta_P).

(1) Baker's theorem: logarithms of algebraic numbers that are independent over Q are
independent over the algebraic numbers. So the relation sum_r d_r Log(1 - r x) = -q*pi
is an algebraic combination of rational ones: d = sum_j x_j e_j with e_j rational
vectors satisfying sum_r e_j(r) Log(1 - r x) = eps_j * i*pi (eps_j rational), the x_j in
a Galois number field K, and sum_j x_j eps_j = -i q.

(2) Kummer theory: over the field of all roots of unity, X^n1 - c^n1 is irreducible
(c^n1 is 2 or sqrt(2); neither is a p-th power in a cyclotomic field, because
Q(2^(1/p)) and Q(2^(1/4)) are not normal over Q; Capelli's criterion). So for each eta
there is an automorphism h of K with h(c) = eta*c that fixes every root of unity.

(3) Apply h to d entry by entry. From the formula for d_r, h(d_r) = d_(r/eta). From
(1), h(d) = sum_j h(x_j) e_j. So the series with coefficients d_(r/eta), which is the
series with rho(k) replaced by eta^k rho(k), has value -i*pi*h(sum_j x_j eps_j)
= -i*pi*h(-i q) = q*pi, because h fixes i and q. QED.

The same proof gives more (the *component lemma*): if S(rho) = alpha*pi with alpha
algebraic, the sub-series over k = j (mod n1) carries exactly the part of alpha that
is 2^(j/n) times a cyclotomic number.

**Theorem.** For every n, a series of F_n equal to a non-zero rational multiple of pi
has cost at least 0.5833. For odd n no such series exists.

*Proof.* Let rho0 be rho restricted to k = 0 (mod n1). By the lemma S(rho0) = q*pi.
Written in the index k/n1, rho0 is a series of F_2 (n even) or of F_1, inside F_2
(n odd), with the same cost as it has in F_n. Removing the other entries of rho can
only delay the first appearance of each prime, so cost(rho) >= cost(rho0), and
cost(rho0) >= 0.5833 by Theorem E of Part III. For odd n, rho0 is an F_1 series, i.e.
an F_2 pattern supported on even k; by Theorem C of Part III the only such pattern
with value in Q*pi is the zero series log(3/4) = log(3/2) + log(1/2), so q = 0. QED.

This rests on: Baker's theorem (proved, 1966); the irreducibility step (standard, but
written by me and unreviewed); and Part III (F_2: the 8-dimensional space and its
optimum 7/24), which is itself unreviewed.

## Why the new series cannot help

A new zero series of F_n lives on the classes k not divisible by n1. Adding it to a
formula for pi cannot cancel any term of the formula's F_2 part, which lives on
k = 0 (mod n1); it only adds terms, and each added term can only bring a prime in
earlier.

## Computations

All three programs use lattice reduction (LLL, python-flint 0.9.0) to find every integer
relation with small coefficients among a list of real numbers; each relation found is
re-checked with 256 more bits. In every run the gap between relations (squared length
at most a few thousand) and non-relations (about 2^66 or more) is wide.

### outside_probe.py n P : the space of all period-P patterns with value in Q*pi

Theory-free: it only uses the numbers S_j = sum over k = j (mod P) of 2^(-floor(k/n))/k
and pi. Columns: dimension of the space; its part on k = 0 (mod n1); its part on the
other classes (new zero series); cheapest pattern carrying pi.

| n | P | dimension | on k = 0 (mod n1) | new zero series | cheapest with pi |
|---|---|---|---|---|---|
| 2 | 8 | 2 | 2 | - | 1.5 (BBP 1995) |
| 2 | 24 | 6 | 6 | - | 0.75 |
| 2 | 120 | 8 | 8 | - | control: matches Part III (dimension 8) |
| 1 | 120 | 1 | 1 | - | none carries pi |
| 3 | 18, 36, 72 | 1 | 1 | 0 | none carries pi |
| 5 | 20 | 0 | 0 | 0 | none |
| 5 | 60 | 1 | 1 | 0 | none carries pi |
| 7 | 84 | 1 | 1 | 0 | none carries pi |
| 9 | 36 | 0 | 0 | 0 | none |
| 4 | 16 | 2 | 2 | 0 | 1.5 |
| 4 | 48 | 6 | 6 | 0 | 0.75 |
| 4 | 80 | 4 | 4 | 0 | 0.75 |
| 4 | 240 | 10 | 8 | 2 | **7/12 = 0.5833** |
| 6 | 72 | 8 | 6 | 2 | 0.75 |
| 6 | 120 | 8 | 4 | 4 | 0.75 |
| 6 | 360 | not completed (stopped after about 12 minutes) | | | |
| 8 | 32 | 2 | 2 | 0 | 1.5 |
| 8 | 96 | 6 | 6 | 0 | 0.75 |
| 8 | 160 | 4 | 4 | 0 | 0.75 |
| 10 | 80 | 2 | 2 | 0 | 1.5 |
| 12 | 24 | 0 | 0 | 0 | none |
| 12 | 72 | 1 | 1 | 0 | none carries pi |
| 12 | 144 | 8 | 6 | 2 | 0.75 |

In every run: each relation splits into a relation on k = 0 (mod n1) plus a relation
on the other classes with no pi (the lemma), to within the rounding noise of the run
(for n = 4, P = 240: 2^-7255 against a noise level of 2^-7170); the part on
k = 0 (mod n1) has exactly the dimension of the corresponding F_2 space; and the
cheapest pattern with pi is the cheapest F_2 pattern of the corresponding period.
(0.75 and 1.5 are the F_2 optima for the small periods 24, 40 and 8; the overall F_2
optimum 0.5833 needs period 120, i.e. P = 60 n.)

The run n = 4, P = 240 (241 numbers at 7004 bits, LLL 560 s) is the one that reaches
that period. It is also an independent check of Part III: by a different method (no
roots of unity, no Baker) it finds the same dimension 8 for the F_2 part and the same
optimum 7/12 = 2 * 7/24, from all C(35, 7) = 6,724,520 vertices. The two new zero
series it finds live on odd k; the first begins
k: 3, 5, 7, 9, 11, 13, 15, 19, 21, ... with coefficients 1, -3, -1, 3, -1, -2, -1, 1, 5, ...
(102 non-zero entries per 240).

An exact check with the patterns of Part III (rational arithmetic): the patterns of
its 8-dimensional space that are supported on even k form a 1-dimensional space with
pi-content 0. So F_1 has no series for a rational multiple of pi, as used in the
theorem for odd n.

### outside_structure.py : multiplicative relations among the numbers 1 - r x

Candidate roots r: those with r^n in {1, -1, primitive 6th roots} (n odd), or with
zeta_8 * r^(n/2) among the 24 roots of Part III (n even). (Same private-prime argument
as Part III, applied to the product over the coset r * mu_n1; not written out in full.)

| n | roots | relations | of which F_2 / F_1 in disguise | new |
|---|---|---|---|---|
| 2 | 24 | 13 | 13 | 0 (control: matches full_class_theorem.py) |
| 3 | 12 | 4 | 2 | 2 |
| 4 | 48 | 19 | 13 | 6 |
| 5 | 20 | 2 | 2 | 0 |
| 6 | 72 | 25 | 13 | 12 |
| 7 | 28 | 2 | 2 | 0 |
| 8 | 96 | 23 | 13 | 10 |
| 9 | 36 | 4 | 2 | 2 |
| 10 | 120 | 29 | 13 | 16 |
| 12 | 144 | 31 | 13 | 18 |

Example of a new relation (n = 3, c = 2^(1/3), w a cube root of unity):
(c+1)^2 (c-1) = (c+w)(c+w^2), from (c+1)^3 (c-1) = 3. Its conjugates carry angles.

### outside_twisted.py n P : what the new relations produce

Targets pi * 2^(a/n) * (real cyclotomic numbers). Found, and each example re-summed
directly to 60 digits:

* n = 3, P = 18: exactly two new series, with values pi*sqrt(3)*2^(1/3) (on
  k = 1 mod 3) and pi*sqrt(3)*2^(2/3) (on k = 2 mod 3). The first is the formula
  displayed at the top. No rational multiple.
* n = 4, P = 48: four new series on odd k, with values pi * 2^(1/4) * (numbers of the
  real cyclotomic field of level 48).
* n = 6, P = 72: eight new series off k = 0 (mod 3).
* n = 5, P = 20: none.
* The component lemma holds in every case to within rounding noise.

## What is proved, what is evidence

* **Proved, given the three inputs listed after the theorem:** no F_n beats 0.5833;
  odd n has no rational-pi series.
* **Evidence only:** the tables. They cover the periods listed, and relations whose
  coefficients are larger than about 2^25 would not be found. The full candidate
  period was reached for n = 3, 5, 7, 9 (rational-pi question) and n = 4 (P = 240);
  not for n = 6 (360; run stopped unfinished), n = 8 (480), n = 10 (600), n = 12 (720).
  For those the theorem, not the tables, carries the conclusion.
* The vertex enumeration behind "cheapest" is floating point with an exact
  recomputation of the winner, as in cheaper_fast.py.

## Corrections to what was assumed going in

* I expected no new relations for even n. Wrong: n = 4 has 6, n = 6 has 12.
* The guess that the new n = 3 relations give multiples like sqrt(3)*2^(1/3)*pi and
  no rational multiple is confirmed.
* The heavy route (numeric constraints on weights, RREF) was not needed: lattice
  reduction on the class sums gives the pattern space directly.

## The directions that remain (assessment, no computing)

* **Higher degree (polylogarithm-type) formulas.** Terms rho(k) x^k / k^s with s >= 2
  give pi^2, Catalan's constant, zeta(3) and the like. pi has weight 1. Under the
  standard conjectures on polylogarithm values, numbers of different weight satisfy no
  linear relations, so a mixed formula for pi would be a degree-1 formula plus
  higher-degree series for zero. Those cannot cancel a 1/k term (a term a/k + b/k^2
  still has p in its denominator at k = s*p unless a = 0). So no gain is expected.
  The independence of weights is conjectural, not proved.
* **Other bases.** Borwein, Borwein and Galway proved that pi has no Machin-type
  arctangent formula in a base that is not a power of 2. Decimal digit extraction
  (Plouffe, Bellard, Gourdon) uses series with binomial denominators and costs about
  n^2, because every prime below the index occurs in every later term.
* **Non-linear exponents.** A series with exponents growing faster than linearly and
  small denominators would cut the cost for real. None is known for pi; my earlier
  search over six quadratic-exponent families found none. There is no theorem
  excluding one.
* **Hypergeometric series** (Chudnovsky and relatives) converge far faster, but they
  give 1/pi, their base is not a power of two, and every prime up to a multiple of the
  index divides the denominators of all later terms, so a single prime costs a sum
  over the whole range rather than one modular power.
* **Lower bounds.** There is no proof that the n-th bit of pi needs time linear in n,
  or even that it cannot be found in time polynomial in log n. The known method
  (BBP) is linear up to logarithms. So "better than linear" is open in the strict
  sense: nothing forbids it, and nothing is known that achieves it.

Bottom line: inside degree-1 binary BBP-type formulas, of any base 2^B and any period,
0.5833 (0.842 bits of state per bit) is the floor. A larger gain needs a formula of a
different kind, and for that there is at present neither a candidate nor a proof of
impossibility.
