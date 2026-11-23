# Other bases: computations, a general statement, and a plan of proof (22 November 2026)

Program: `python/baseb_explore.py` (new; it changes no other file). The setting is that of
Parts III, V and VI of `notes/pi_formula_theorem.md`.

**Nothing in this file is proved by a computation.** Section 10 lists what is computed, what
is proved elsewhere, and what is only argued here.

## 1. Summary

1. For every base b from 2 to 40 (squares, prime powers and non-squarefree bases included)
   we computed the exceptional roots of unity up to order 300 and the lattice of integer
   relations among 2 pi i and the numbers Log(1 - r/sqrt(b)).
2. **A relation exists for b = 2, 3 and 4, and for no other base up to 40.** The ranks are
   13, 3 and 2.
3. Base 4 has relations: one zero relation and one formula for pi sqrt(3). Both are known and
   both live inside base 2.
4. Bases 8, 9, 16, 25, 27, 32 have **no** relation, although they are powers of 2, 3 and 5.
   So the right list is {2, 3, 4}, not "the powers of 2 and 3". The reason: the class of
   base c^j is the small part of the class of base c made of the patterns supported on the
   multiples of j, and the relations of base 2 and base 3 do not survive that restriction
   (except j = 2 in base 2).
5. The pattern has a reason, and the reason gives a short argument for every b >= 5 at once:
   Zsigmondy's theorem for the roots with one class, and a size inequality for the
   Aurifeuillian case. **The size inequality has no exception at all for b >= 5**: no pair
   (b, n) needs a separate verification. No theorem of Schinzel type is needed.
6. Statement G (section 8): for b >= 5 there is no relation, so the class F_b has no zero
   relation and contains no non-zero algebraic multiple of pi.

## 2. Setting and words

For an integer b >= 2, F_b is the class of series

    S(rho) = sum over k >= 1 of rho(k) b^(-floor(k/2)) / k,      rho rational and periodic.

Put t = sqrt(b) > 0. Then rho(k) b^(-floor(k/2)) = c(k) t^(-k) with c(k) = rho(k) t^(k mod 2),
and c(k) = sum over r of d_r r^k (finite Fourier expansion over roots of unity r), so

    S(rho) = - sum over r of d_r Log(1 - r/t).

For b = 2 and b = 3 the note uses t = 1 + i and t = sqrt(-3). These differ from sqrt(b) by a
root of unity, so the numbers 1 - r/t are the same; only the names of the roots change
(r here = r in the note times zeta_8^(-1) for base 2, times -i for base 3).

**Relation.** An integer vector (z_r; z_0), finitely many z_r non-zero, with

    sum of z_r Log(1 - r/t) + z_0 * 2 pi i = 0.

Equivalently the product of the (1 - r/t)^(z_r) is 1. By Baker's theorem the patterns rho
with S(rho) an algebraic multiple of pi (zero included) correspond to the combinations of
such relations with algebraic coefficients. Their space has dimension equal to the rank of
the lattice of relations (Galois descent; section 5 uses this).

**Classes.** Write b = s^2 d with d squarefree. Let f be the conductor of Q(sqrt(d)): f = 1 if
d = 1, f = d if d = 1 mod 4, f = 4d otherwise. Let chi be the Kronecker character of
Q(sqrt(d)). For a root r of order n let m be the order of r^2.

- (A) b = c^2 is a square. Then t = c and the norm of c - r is Phi_n(c). One class.
- (B) b is not a square and the roots of order n form one class. This happens when f does
  not divide n, and also when 4 | n and f | n/2. The norm of t - r is a power of Phi_m(b).
- (C) b is not a square, f divides n, and not both 4 | n and f | n/2. This is the
  Aurifeuillian case. sqrt(d) lies in Q(zeta_n). The conjugates of t - zeta are the
  chi(c) t - zeta^c. There are two classes: "+" (exponents a with chi(a) = 1) and "-". Their
  norms N+ and N- are integers with N+ N- = Phi_m(b)^e, where e = 2 if 4 | n and e = 1
  otherwise.

**Good prime.** A prime p that divides the norm of t - r and does not divide 2 b n. A prime
ideal above p then contains t - r. A prime dividing b never divides the norm (it would
contain t, hence r). A class with no good prime is **exceptional**.

**R0.** The exceptional roots, closed under this rule: if r' is in R0 and an odd prime p
divides both the order of r' and the norm of t - r', then the p'-part of r' is in R0. As in
Part III, Step 2, every relation is supported on R0. (Take a root of the relation outside R0
of largest order among those outside R0. Its good prime ideal P contains no other t - r' of
the relation: such an r' would be r times a root of p-power order, so of larger order, so in
R0, and then r, its p'-part, would be in R0.)

## 3. What the method predicts for a general base

Three standard facts.

- F1 (Zsigmondy). Phi_m(b) has a prime factor p with ord_p(b) = m, except for
  (b, m) = (2, 1), (2, 6), and m = 2 with b + 1 a power of 2. Such a p is 1 mod m.
- F2. A prime factor of Phi_m(b) that divides m is the largest prime factor of m. If it is
  odd, it divides Phi_m(b) only once. Every other prime factor p has ord_p(b) = m.
- F3. For odd b, a prime ideal above 2 contains t - r only if the order of r is a power
  of 2.

Consequences, case by case.

- **(A)** c - r has a good prime unless n = 1 and c - 1 is a power of 2, or n = 2 and c + 1
  is a power of 2, or (c, n) = (2, 6).
- **(B)** t - r has a good prime unless m = 1 and b - 1 is a power of 2 (r = 1, -1), or
  m = 2 and b + 1 is a power of 2 (r = i, -i), or (b, m) = (2, 6).
- **(C)** By F2 and F3, an exceptional class has |norm| equal to 1, p or p^2, where p is the
  largest prime factor of n, p is odd, p does not divide b, and p^2 is possible only if
  4 | n. Call this bound cap(b, n) (it is 1 if there is no such p). On the other hand every
  conjugate of t - r has absolute value at least sqrt(b) - 1, so

      |norm| >= (sqrt(b) - 1)^phi(n).

  For b >= 5 this is larger than cap(b, n) in every case (section 9). So for b >= 5 no class
  of case (C) is exceptional. For b = 2 and b = 3, sqrt(b) - 1 < 1, the bound says nothing,
  and exceptional classes do occur (orders 8, 24, 40 in base 2; order 12 in base 3).

**Prediction.** The exceptional classes are:

| base | exceptional classes |
|---|---|
| 2 | orders 1, 2 (units), 8+ (unit), 12 (norm 3^2), 24+ (unit), 40+ (norm 5^2) |
| 3 | orders 1, 2 (norm 2), 4 (norm 2^4), 12+ (unit) |
| 4 | order 1 (2 - 1 = 1, a unit), order 6 (norm 3) |
| b >= 5, not a square | orders 1 and 2 if b - 1 is a power of 2; order 4 if b + 1 is a power of 2; otherwise none |
| b = c^2 >= 9 | order 1 if c - 1 is a power of 2; order 2 if c + 1 is a power of 2; otherwise none |

For b >= 5 the norms of the exceptional classes are powers of 2, so the closure adds
nothing and R0 has at most two elements. These are multiplicatively independent:

- b - 1 = 2^k, b not a square, R0 = {1, -1}. If (1 - 1/t)^x (1 + 1/t)^y = 1, the norm to Q
  gives ((b-1)/b)^(x+y) = 1, so y = -x, and then ((t-1)/(t+1))^x = 1 with 0 < (t-1)/(t+1) < 1
  gives x = 0.
- b + 1 = 2^k, b >= 7, R0 = {i, -i}. Absolute values give y = -x. The number
  u = (t - i)/(t + i) = (b - 1 - 2it)/(b + 1) has trace 2(b-1)/(b+1), which is an integer only
  if b + 1 divides 4. So for b >= 5, u is not an algebraic integer, hence not a root of
  unity, and x = 0. (For b = 3, u is a primitive 6th root of unity. That is the formula for
  pi sqrt(3).)
- b = c^2: the numbers (c-1)/c and (c+1)/c. For c = 3 these are 2/3 and 4/3, independent.
  For c >= 5 at most one of them is in R0.

So the method predicts: **for b >= 5 there is no relation at all.**

## 4. Tables

### 4.1 Bases 2 to 40

Columns. *b = s^2 d*, *f*: as in section 2. *exceptional*: the exceptional classes of order
at most 300, as "order and class: number"; the number is the norm for two classes and for
squares, and Phi_m(b) for one class (the norm is then this number or its square). *R0*: its
size and the orders of its roots. *N*: the periods on which lattice reduction was run (all
N-th roots of unity together with 2 pi i). *rank*: the rank of the lattice of relations
found (for base 2 at N = 24 / 60 / 120). *2 pi i*: 1 if some relation involves 2 pi i (then
some multiple of pi is a value), else 0. *zero*: the dimension of the space of zero
relations. *bound*: no relation outside the span of those found has sum of |z| below this
(see section 4.4; the smallest over the N tested).

| b | b = s^2 d | f | exceptional (order: number) | R0 | N | rank | 2 pi i | zero | bound |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 2 | 8 | 1: 1, 2: 1, 8+: 1, 12: 3, 24+: 1, 40+: 5^2 | 24 roots, orders 1, 2, 4, 8, 12, 24, 40 | 24, 60, 120 | 8/3/13 | 1 | 7 | 2^67 |
| 3 | 3 | 12 | 1: 2, 2: 2, 4: 2^2, 12+: 1 | 6 roots, orders 1, 2, 4, 12 | 24, 60, 120 | 3 | 1 | 2 | 2^62 |
| 4 | 2^2 | 1 | 1: 1, 6: 3 | 4 roots, orders 1, 2, 6 | 24, 60, 120 | 2 | 1 | 1 | 2^61 |
| 5 | 5 | 5 | 1: 2^2, 2: 2^2 | 2 roots, orders 1, 2 | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 6 | 6 | 24 | none | empty | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 7 | 7 | 28 | 4: 2^3 | 2 roots, order 4 | 24, 28, 60, 84, 120 | 0 | 0 | 0 | 2^60 |
| 8 | 2^2 * 2 | 8 | none | empty | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 9 | 3^2 | 1 | 1: 2, 2: 2^2 | 2 roots, orders 1, 2 | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 10 | 10 | 40 | none | empty | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 11 | 11 | 44 | none | empty | 24, 44, 60, 120, 132 | 0 | 0 | 0 | 2^60 |
| 12 | 2^2 * 3 | 12 | none | empty | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 13 | 13 | 13 | none | empty | 24, 52, 60, 120, 156 | 0 | 0 | 0 | 2^58 |
| 14 | 14 | 56 | none | empty | 24, 56, 60, 120 | 0 | 0 | 0 | 2^60 |
| 15 | 15 | 60 | 4: 2^4 | 2 roots, order 4 | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 16 | 4^2 | 1 | none | empty | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 17 | 17 | 17 | 1: 2^4, 2: 2^4 | 2 roots, orders 1, 2 | 24, 60, 68, 120 | 0 | 0 | 0 | 2^60 |
| 18 | 3^2 * 2 | 8 | none | empty | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 19 | 19 | 76 | none | empty | 24, 60, 76, 120 | 0 | 0 | 0 | 2^60 |
| 20 | 2^2 * 5 | 5 | none | empty | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 21 | 21 | 21 | none | empty | 24, 60, 84, 120 | 0 | 0 | 0 | 2^60 |
| 22 | 22 | 88 | none | empty | 24, 60, 88, 120 | 0 | 0 | 0 | 2^60 |
| 23 | 23 | 92 | none | empty | 24, 60, 92, 120 | 0 | 0 | 0 | 2^60 |
| 24 | 2^2 * 6 | 24 | none | empty | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 25 | 5^2 | 1 | 1: 2^2 | 1 root, order 1 | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 26 | 26 | 104 | none | empty | 24, 60, 104, 120 | 0 | 0 | 0 | 2^60 |
| 27 | 3^2 * 3 | 12 | none | empty | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 28 | 2^2 * 7 | 28 | none | empty | 24, 28, 60, 84, 120 | 0 | 0 | 0 | 2^60 |
| 29 | 29 | 29 | none | empty | 24, 60, 116, 120 | 0 | 0 | 0 | 2^60 |
| 30 | 30 | 120 | none | empty | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 31 | 31 | 124 | 4: 2^5 | 2 roots, order 4 | 24, 60, 120, 124 | 0 | 0 | 0 | 2^60 |
| 32 | 4^2 * 2 | 8 | none | empty | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 33 | 33 | 33 | 1: 2^5, 2: 2^5 | 2 roots, orders 1, 2 | 24, 60, 120, 132 | 0 | 0 | 0 | 2^59 |
| 34 | 34 | 136 | none | empty | 24, 60, 120, 136 | 0 | 0 | 0 | 2^59 |
| 35 | 35 | 140 | none | empty | 24, 60, 120, 140 | 0 | 0 | 0 | 2^59 |
| 36 | 6^2 | 1 | none | empty | 24, 60, 120 | 0 | 0 | 0 | 2^60 |
| 37 | 37 | 37 | none | empty | 24, 60, 120, 148 | 0 | 0 | 0 | 2^58 |
| 38 | 38 | 152 | none | empty | 24, 60, 120, 152 | 0 | 0 | 0 | 2^58 |
| 39 | 39 | 156 | none | empty | 24, 60, 120, 156 | 0 | 0 | 0 | 2^58 |
| 40 | 2^2 * 10 | 40 | none | empty | 24, 60, 120 | 0 | 0 | 0 | 2^60 |

Bases with a relation: 2, 3, 4. Cross-check (c): in every case the support of every relation
found lies in R0 (base 2: support 24 roots, R0 24 roots; base 3: 6 and 6; base 4: 4 and 4).
Every relation found was also verified exactly, as an identity in Z[zeta] (section 4.4).

The exceptional column agrees with the prediction of section 3 in every row.

### 4.2 A wider scan of the exceptional roots

`check 300 120`: for every b from 2 to 300 and every order up to 120, the exceptional classes
are exactly those predicted. The bases with an exceptional class are

    2, 3, 4;  5, 17, 33, 65, 129, 257 (orders 1, 2);  7, 15, 31, 63, 127, 255 (order 4);
    9 (orders 1, 2);  25, 81, 289 (order 1);  49, 225 (order 2).

`check 40 400` gives the same for b up to 40 and orders up to 400. In case (C) the program
also checks, for each of 920 classes (resp. 846), that the part of the norm made of primes
dividing 2bn divides cap(b, n), and that the norm is at least (sqrt(b) - 1)^phi(n).

For b >= 5 the smallest "good part" of a norm in case (C) is 11 (b = 5, order 5: the norms
are 11 and 71). The next are 25 (b = 8, order 8: norms 25 and 169), 49 (b = 12, order 12),
169 (b = 6, order 24), 169 (b = 18, order 8), 251 (b = 20, order 5). Nothing is close to 1.

The units among the t - r (norm 1): base 2, orders 1, 2, 8+, 24+ (8 roots); base 3, order
12+ (2 roots); base 4, r = 1. No other base has one, and none can: every conjugate of
sqrt(b) - r has absolute value at least sqrt(b) - 1, which is above 1 for b >= 5.

### 4.3 A search with no theory

`probe B P` runs `base3_probe.py` (lattice reduction on the P class sums of the series
itself, with pi, pi sqrt(2), pi sqrt(3), pi sqrt(5), pi sqrt(6), pi sqrt(7), pi sqrt(d) and
log p for p <= 13 as targets).

- P = 60, every b from 2 to 40: the number of zero relations of period 60 is 1, 2, 1 for
  b = 2, 3, 4 and 0 for every other b. A multiple of pi is a value only for b = 2
  (pi sqrt(2), pi sqrt(3) at this period), b = 3 (pi sqrt(3)) and b = 4 (pi sqrt(3)).
- P = 24 and P = 120 for b = 4, 8, 9, 16, 25, 27, 32: one zero relation for b = 4 and
  pi sqrt(3) a value; no zero relation and no multiple of pi for the six others.
- By the way: in base 9, log 2, log 3, log 5, log 7, log 11, log 13 are all values
  (1 - 1/3 = 2/3 and 1 + 1/3 = 4/3 give log 2 and log 3). In bases 8, 16, 25, 27, 32 no
  single log p with p <= 13 is a value at these periods.

### 4.4 How sound the lattice search is

- **A vector is accepted as a relation** only if the combination vanishes to the full
  working precision, 300 bits beyond what the lattice saw. A vector that is merely short has
  a residue of the size the lattice saw.
- **Exact check.** Each accepted relation is then verified as an identity
  prod (T - 2r)^(z_r) = T^(sum z_r) in Z[zeta_M], with T = 2 sqrt(b) written as a Gauss sum
  (python-flint polynomials modulo the cyclotomic polynomial). All relations found pass.
- **Completeness, up to a bound.** With the relations placed first, the program computes the
  Gram-Schmidt lengths of the other vectors of the reduced basis. A relation outside the
  span of those found would give a lattice vector of length at most sqrt(3) times its sum of
  |z|, and at least the smallest of these lengths. This gives the last column: no other
  relation with sum of |z| below about 2^60. This is a statement about the computed
  lattice, in floating point; it is strong evidence, not a proof.
- `deep 2 40 24 120` repeats the search on the 24th roots with 120 bits per number: same
  ranks (8, 3, 2, then 0), and no other relation with sum of |z| below 2^253.
- **Galois check.** The lattice found is stable under the Galois group of Q(zeta_N, t) (each
  image of a basis relation is again a relation, with an integer coefficient of 2 pi i). The
  program uses this to compute the dimension of the zero relations (section 5).

## 5. The three bases with relations

Notation: L(a/n) = Log(1 - exp(2 pi i a/n)/sqrt(b)).

**Base 2.** Rank 13 on N = 120, supported on the 24 roots of R0 (orders 1, 2, 4, 8, 12, 24,
40). One basis vector may be taken to involve 2 pi i. The Galois computation gives: the
patterns with value in (algebraic numbers) pi form a space of dimension 13; their values
divided by pi span a space of dimension 6 over Q; the zero relations have dimension 7. This
is Theorem C of the note (13; the rational multiples of pi and zero: 8 = 7 + 1). The basis
found is printed by `relations 2 120`.

**Base 3.** Rank 3, on the six roots 1, -1, i, -i, zeta_12, zeta_12^(-1):

    -L(1/12) + L(1/4) - L(3/4) + L(11/12) = 0
    -L(0) + L(1/12) - L(1/2) + L(3/4) = 0
    -L(0) + 4 L(1/12) + 3 L(1/4) - L(1/2) - 2 L(3/4) - 3 L(11/12) + 2 pi i = 0

Dimension 3, values in Q pi sqrt(3), zero relations of dimension 2. This is Theorem C3.

**Base 4.** Here t = 2 and F_4 is the class of the series sum of c(k) 2^(-k)/k. Rank 2, on
the four roots 1, -1, w, 1/w (w a primitive 6th root of unity):

    -L(0) + L(1/6) - L(1/2) + L(5/6) = 0             (2 - w)(2 - 1/w) = 3 = (2 - 1)(2 + 1)
    6 L(1/6) - 6 L(5/6) + 2 pi i = 0                  1 - w/2 = (sqrt(3)/2) exp(-i pi/6)

In patterns of period 6 (rho(k) for k = 1, ..., 6):

    G4 = (1, 2, 0, -2, -1, 0),     S(G4) = 2 pi sqrt(3)/9,
    Z4 = (1, -6, -2, -6, 1, 0),    S(Z4) = 0.

Both are checked to 70 digits by direct summation (`base4`). So in base 4: S(rho) is an
algebraic multiple of pi exactly for rho = a G4 + c Z4, with value a * 2 pi sqrt(3)/9. The
zero relations have dimension 1. pi sqrt(3) is a value and pi is not. In Bailey's notation
these are pi sqrt(3) = (9/32) P(1, 64, 6, (16, 8, 0, -2, -1, 0)) and
0 = P(1, 64, 6, (16, -24, -8, -6, 1, 0)). Both are known formulas (from memory, they are in
Bailey's compendium; the source was not re-read in this pass). Nothing here is new: base 4
is the part of base 2 supported on even k (section 6), and Part IV of the note already says
that these patterns carry no rational multiple of pi.

Why three bases. The rank is (number of roots in R0) minus (rank of the group they
generate): 24 - 11 = 13, 6 - 3 = 3 (generators 2, sqrt(3), 2 + sqrt(3)), 4 - 2 = 2
(generators 2, 3). For b >= 5 it is 2 - 2, 1 - 1 or 0 - 0.

## 6. Powers of 2 and of 3

For b = c^j the class F_b lies inside F_c:

    a series of F_(c^j) with pattern rho  =  the series of F_c with pattern rho',
    rho'(jk) = j c^(floor(j/2) (k mod 2)) rho(k),    rho' = 0 off the multiples of j.

So F_(c^j) is exactly the set of series of F_c whose pattern is supported on the multiples
of j. For the logarithms: 1 - s/t^j is the product of the 1 - r/t over r^j = s, so the
relations of base c^j are the relations of base c that are constant on the cosets of the
j-th roots of unity.

`powers 2 120` and `powers 3 72` compute both sides:

| base | invariant relations of base 2 or 3 | direct computation |
|---|---|---|
| 4 = 2^2 | 2 | 2 |
| 8 = 2^3 | 0 | 0 |
| 16 = 2^4 | 0 | 0 |
| 32 = 2^5 | 0 | 0 |
| 64 = 2^6 | 0 | 0 |
| 9 = 3^2 | 0 | 0 |
| 27 = 3^3 | 0 | 0 |
| 81 = 3^4 | 0 | 0 |
| 729 = 3^6 | 0 | 0 |

For the powers of 3 this is a consequence of the machine-checked Theorem C3, by hand. The
entries of a G + b Z1 + c Z2 at k = 1, ..., 5 are 6a + c, b - 3c, -(6a + 2b + 4c), -3c,
6a + b + c. Support on even k forces the entries at 1, 3, 5 to vanish, so a = b = c = 0.
Support on the multiples of 3 forces the entries at 1, 2, 4 to vanish, so again
a = b = c = 0. A pattern of period 12 supported on the multiples of j is zero unless j
divides 12. Hence: **for every j >= 2 the class of base 3^j has no zero relation and no
algebraic multiple of pi.** In particular pi sqrt(3) is not a value in base 9.

For the powers of 2 the same reasoning with Theorem C (period 120; a divisor of 120 that is
at least 3 is divisible by 3, 4 or 5) gives: **base 4 has the two relations above, and for
every j >= 3 the class of base 2^j has none.** Here the finite step (no pattern of the
13-dimensional space is supported on the multiples of 3, of 4 or of 5; those supported on
even k have dimension 2) was done by the program in exact integer arithmetic on its own
basis of 13 relations, not in Lean.

Caution on words. The 1995 BBP formula is P(1, 16, 8, .). It belongs to F_2 (weights
2^(-floor(k/2)), period 8), not to F_16. The class F_16 is P(1, 16^B, 2B, .), that is,
the series sum of c(k) 4^(-k)/k. So "F_16 contains no multiple of pi" does not contradict
the BBP formula.

## 7. Why 2, 3 and 4: the hypotheses, tested

1. *"A relation needs t - r to be a unit, or to share all its primes with other roots of
   the relation."* True, and it is the whole mechanism: for every prime ideal P the sum of
   z_r v_P(t - r) must vanish. Two numbers t - r and t - r' share a prime above p only if
   r'/r has order a power of p. The table shows it: every root in the support of a relation
   is in R0.
2. *"|sqrt(b) - r| = 1 is possible only for b <= 4."* True. Every conjugate of sqrt(b) - r
   has absolute value at least sqrt(b) - 1. So a unit needs sqrt(b) - 1 <= 1. Units: 8 roots
   in base 2, 2 in base 3, one in base 4 (2 - 1), none for b >= 5 (section 4.2).
3. *Small norms without units.* Three causes, all for small b: the exception (2, 6) of
   Zsigmondy's theorem (Phi_6(2) = 3; orders 12 in base 2 and 6 in base 4); b - 1 or b + 1 a
   power of 2; and an Aurifeuillian half equal to a prime dividing n (order 40 in base 2,
   norm 5^2). For b >= 5 only the second cause remains.
4. *"b - 1 or b + 1 a power of 2" (b = 5, 7, 9, 15, 17, 25, 31, 33).* The roots 1, -1 (or
   i, -i) are exceptional: their only prime is 2. But two numbers that generate a group of
   rank 2 have no relation (section 3). The scan and the lattice search agree: R0 has one or
   two roots and the rank is 0. Base 3 is the only base where b - 1 and b + 1 are both
   powers of 2, and the only one where (t - i)/(t + i) is a root of unity.
5. *b = 4, 8, 9, 16, 27, 32.* Section 6. Only 4 keeps relations.

So base 2 is special because sqrt(2) - 1 < 1 gives many units, and because of Phi_6(2) = 3
and the factor 5 at order 40. Base 3 is special because sqrt(3) - zeta_12 is a unit, 2 and 4
are the neighbours of 3, and (sqrt(3) - i)/(sqrt(3) + i) is a root of unity. Base 4 is
special because 2 - 1 = 1 and Phi_6(2) = 3 = 2 + 1.

## 8. Statement G

For an integer b >= 2 let Lambda_b be the group of all relations of base b (section 2),
over all roots of unity.

**Statement G (a conjecture for b >= 5 outside the powers of 2 and 3; see below).**

- Lambda_2 has rank 13, Lambda_3 has rank 3, Lambda_4 has rank 2.
- Lambda_b = 0 for every b >= 5. That is: the numbers 2 pi i and Log(1 - r/sqrt(b)), r
  running over all roots of unity, are linearly independent over Q.

**Consequences, by Baker's theorem.** For b >= 5 and rho rational and periodic (algebraic
would do):

- (a) S(rho) = 0 only for rho = 0. The class F_b has no zero relation: a number has at most
  one formula of this class.
- (b) S(rho) is an algebraic multiple of pi only for rho = 0. In particular pi, pi sqrt(b)
  and every pi sqrt(m) are not values.
- (c) More: S(rho) is transcendental for every rho other than 0.

For b = 2, 3, 4 the spaces are:

| base | patterns with value in (algebraic) * pi | values | zero relations | period |
|---|---|---|---|---|
| 2 | dimension 13 | a space of dimension 6 over Q, times pi; it contains pi | dimension 7 | 120 |
| 3 | dimension 3: a G + b Z1 + c Z2 | Q pi sqrt(3) | dimension 2 | 12 |
| 4 | dimension 2: a G4 + c Z4 | Q pi sqrt(3) | dimension 1 | 6 |

So: F_b has a zero relation exactly for b = 2, 3, 4. F_b contains a non-zero algebraic
multiple of pi exactly for b = 2, 3, 4. F_b contains pi itself only for b = 2.

**Status of each part.**

- b = 2, b = 3: proved and machine-checked (Theorems C and C3).
- b = 3^j, j >= 2: follows from Theorem C3 by the hand computation of section 6.
- b = 4 and b = 2^j, j >= 3: follows from Theorem C and a finite computation done by the
  program (section 6).
- every other b >= 5: not proved. Evidence: section 4, for b <= 40 (lattices) and b <= 300
  (exceptional roots). A plan of proof with no missing idea: section 9.

**Evidence, in one list.** (1) Exceptional classes exactly as predicted, b <= 40 to order
400, b <= 300 to order 120. (2) Lattice reduction on the logarithms: rank 0 for every b from
5 to 40, on N = 24, 60, 120 and on a multiple of f; no relation with sum of |z| below about
2^58; on N = 24, below 2^253. (3) The search with no theory: no zero relation of period 60
for b from 5 to 40. (4) The two computations of section 6 agree. (5) The size inequality
holds in all 34145 cases tried (section 9).

In print (see `00_summary.md`): Borwein, Borwein and Galway proved that pi has no
Machin-type formula in a base b > 2 that is not a proper power. Statement G would extend this
to the whole class F_b, add the square roots and the absence of zero relations, and cover
proper powers too. We did not search the literature in this pass.

What Statement G does not cover: the series with weights b^(-floor(k/n)), n >= 3 (the
analogue of Part IV). For base 2 these contain new relations for irrational multiples of pi.
A general-base version of the sub-series lemma of Part IV would be needed to say that pi has
no degree-1 BBP-type formula of any shape in a base that is not a power of 2. This was not
examined here.

## 9. Plan of proof for b >= 5, and the inequalities

The steps. Each is standard; none was written out in full or checked by a second reader.

1. **The series as a combination of logarithms**, with t = sqrt(b). A copy of
   `Base3/Series.lean` without the sign.
2. **Good primes, cases (A) and (B).** Zsigmondy's theorem for the base c or b (in the Tau
   Ceti library for every base), exactly as in section 3. Exceptions: only b - 1 or b + 1 (or
   c - 1, c + 1) a power of 2, since (2, 6) needs base 2.
3. **Good primes, case (C).** The size argument. Let H be the norm of t - r from Q(zeta_n).
   - (I1) |H| >= (sqrt(b) - 1)^phi(n): each of the phi(n) conjugates is +-t - r' and
     |+-t - r'| >= t - 1.
   - (I2) H divides Phi_m(b)^e (as N+ N- = Phi_m(b)^e). If H has no good prime, every prime
     factor of H divides n (not b; not 2, by F3, because n is not a power of 2 when b is
     odd). By F2 the only such prime is p, the largest prime factor of n, and p divides
     Phi_m(b) once. So |H| divides p^e: |H| <= cap(b, n).
   - (I3) If cap > 1 then p is odd and does not divide b, so p does not divide f. As f | n
     and p | n, phi(n) >= (p - 1) phi(f) >= 4 (p - 1). (phi(f) >= 4 for every conductor
     f >= 5.)
   - (I4) For p >= 5 and b >= 5: (sqrt(b) - 1)^(4(p-1)) >= (sqrt(5) - 1)^(4(p-1)) > p^2.
     At p = 5 this is 29.7 > 25, and the left side grows faster. For p = 3: all odd prime
     factors of n are 3 and 3 does not divide f, so f = 8, b = 2 s^2 >= 8, and
     (sqrt(8) - 1)^8 = 124.9 > 9.
   - If cap = 1: |H| = 1 contradicts (I1), since sqrt(b) - 1 > 1.
   So every class of case (C) has a good prime. No pair (b, n) is left over.
4. **The support theorem.** Every relation is supported on R0 (section 2). As in
   `Base3/PiValue.lean`.
5. **No relation on R0.** The three small independence facts of section 3.
6. **Baker's theorem**, as for bases 2 and 3.

**The inequality, checked numerically** (`bound 2000 3000`). For 5 <= b <= 2000, b not a
square, and every n <= 3000 in case (C): 34145 pairs.

- With cap(b, n) as defined: **no failure**. The tightest cases, as the ratio
  phi(n) log(sqrt(b) - 1) / log(cap): 2.20 (b = 8, n = 24, cap 9), 2.61 (b = 5, n = 35 and
  70, cap 7), 3.00 (b = 8, n = 40, cap 25), 3.54 (b = 5, n = 55 and 110), 3.69 (b = 6,
  n = 120). A ratio above 1 is what is needed.
- With the cruder cap p^e that forgets "p does not divide b": two failures, (b, n) = (5, 5)
  and (5, 10). There the norms are 11 and 71, so a direct look settles them.
- With the crudest cap n^2: 19 failures, all with b <= 12:
  b = 5, n = 5, 10, 15, 25, 30, 35, 45, 50, 70, 75, 90, 110, 150, 210; (6, 24); (7, 28);
  (8, 8); (8, 24); (12, 12). All are settled by the scan of section 4 (every class has a good
  prime).

So a uniform size argument is not only plausible: with the cap p^e and p not dividing b it
has no exceptional case. The reason it was hard for b = 2 and b = 3 is that sqrt(b) - 1 < 1
there; the proofs of Lemma 2 and Lemma H needed the finer bound through the Moebius product.
For b >= 5 the trivial bound is enough, and no statement about primitive primes of the
Aurifeuillian factors has to be taken from the literature. (The argument does prove, for
b >= 5, that each of the two classes has a primitive prime factor, which is the statement of
Schinzel's type. We do not claim it is new.)

**What a machine-checked proof would cost.** Steps 1, 2, 4, 5, 6 follow the base-3 files.
Step 3 is the new work: it needs the norm of t - r from the field Q(zeta_n) as an integer, the
product formula over embeddings for (I1), and the identity N+ N- = Phi_m(b)^e. In base 3 this
was done by hand in Z[w]; for a general b it needs Mathlib's cyclotomic fields and norms. It
can be arranged without knowing that sqrt(d) lies in Q(zeta_n): work in K = Q(t, zeta_n), of
degree g phi(n) with g = 1 or 2; then |N_K(t - r)| >= (sqrt(b) - 1)^(g phi(n)) and the part
without good primes divides p^(e g), so the same inequality decides, whatever g is. This
replaces the plan of Part VI for base 5 (a lemma on L_h and M_h in Z[zeta_5]) by one
argument for all bases.

**Where the sketch could be wrong.** (i) F2 and F3 are used in the form stated; F2 for odd p
is the lemma behind Zsigmondy's theorem that the Lean proof of Lemma H already uses. (ii)
The description of the classes for b not squarefree (t = s sqrt(d)) was checked numerically
only (the products are integers and N+ N- = Phi_m(b)^e for every case computed; `selftest`
also checks that there is one class, of norm Phi_(n/2)(b), when 4 | n and f | n/2). (iii) The
closure R0 and the support argument are those of Part III, where a first version was wrong
and a reviewer corrected it; the general version deserves the same review.

## 10. Computed, proved, argued

Proved and machine-checked elsewhere (not here): Theorem C (base 2), Theorem C3 (base 3),
Lemma 2 and Lemma H.

Follows from those by a short argument given here (not machine-checked): no relation for
base 3^j, j >= 2 (by hand); the relations of base 4 and none for base 2^j, j >= 3 (with a
finite computation by the program).

Computed only:

- the exceptional classes and R0, b <= 40 to order 300 or 400, b <= 300 to order 120;
- the relation lattices of the table (ranks, bases, supports, exact verification of each
  relation found, the bound on other relations);
- the dimensions 13 / 6 / 7 (base 2), 3 / 1 / 2 (base 3), 2 / 1 / 1 (base 4) from the lattice
  and the Galois action;
- the two base-4 values to 70 digits;
- the search with no theory, P = 60 for b <= 40, P = 24 and 120 for the prime powers;
- the size inequality on 34145 pairs.

Argued here, not proved: sections 3 and 9 (the prediction and the plan), hence Statement G
for the bases b >= 5 that are not powers of 2 or 3.

Not done: any search of the literature; the wider classes with weights b^(-floor(k/n)).

## 11. Commands

From `python/`, in Git Bash, with python-flint on the path:

    P="env -u PYTHONPATH PYTHONPATH=/c/Users/SPONTA~1/AppData/Local/Temp/claude/36baf50e44845f2a/661d1602-dac7-4b86-a51f-ebc082afae1e/scratchpad/pylib python"

    $P baseb_explore.py selftest             # checks of the program (1 s)
    $P baseb_explore.py scan 2 40 300        # exceptional classes and R0 (6 s)
    $P baseb_explore.py check 300 120        # the same against the prediction (2 s)
    $P baseb_explore.py check 40 400         # (2 s)
    $P baseb_explore.py table 2 40 300       # the table of 4.1 (about one hour; it can be
                                             #   split: table 2 6 300, table 7 11 300, ...)
    $P baseb_explore.py relations 2 120      # one base, with the basis (45 s)
    $P baseb_explore.py relations 3 12
    $P baseb_explore.py base4                # the two formulas of base 4
    $P baseb_explore.py deep 2 40 24 120     # 24th roots, 120 bits per number (7 s)
    $P baseb_explore.py powers 2 120         # section 6 (1 min)
    $P baseb_explore.py powers 3 72
    $P baseb_explore.py bound 2000 3000      # the size inequality (3 s)
    $P baseb_explore.py probe 4 24           # the search with no theory; also probe B 60
                                             #   for B = 2..40, probe B 120 for prime powers

`scan`, `check`, `bound`, `selftest` need only mpmath and sympy.
