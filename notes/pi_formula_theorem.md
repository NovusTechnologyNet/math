# The binary Machin-type formulas for pi: a classification

Working note, 20-21 November 2026. Status: Parts I and II are written out, checked by
computer, and have had one independent adversarial review (no error found in the
theorems; its corrections are applied below). Parts III and IV are checked by the
programs named in them, reproduce all 27 binary degree-1 rows of Bailey's published
table of zero relations, and have had one independent review (corrections applied;
see review_part3_part4.md). A literature
check (research/2026-11-21-publishable-work/report.md) found no earlier statement of
the classification; what is already in print is credited where it is used.

Naming: the identity pi/4 = 2 arctan(1/3) + arctan(1/7) is Hutton's (1776). Its binary
digit-extraction series (Bailey's compendium, Formula 19) is ascribed to Pschill in
Arndt and Haenel, *Pi Unleashed* (2001), and was traced back to Euler (1779) by
Craig-Wood, Euleriana 3(1) (2023). This note and the code call it "Euler's"; a paper
should say "the Hutton-Euler formula".

**Headline of Parts III and IV:** among all binary degree-1 BBP-type formulas for pi,
the best possible cost is now known exactly in two measures. Under the standard
measure (terms per bit) the optimum is 2/3, attained only by Huvent's two 2001
formulas (y-cruncher uses his rate); nobody had proved it optimal. Under the per-prime measure of the
window algorithm the optimum is 7/24, attained by a new formula that needs 12% fewer
primes than Euler's (and is slower than Huvent's and Bellard's by the standard measure).

## Setting

Borwein, Borwein and Galway (Canad. J. Math. 56 (2004), 897-925; "BBG") define a
*binary Machin-type BBP arctangent formula* as a rational linear combination of the
generators

    b_m = arctan(1 / 2^m)            (m >= 1),
    a_m = arctan(1 / (2^m - 1))      (m >= 1),   so a_1 = pi/4.

Each generator has a power-of-two series, which is what makes digit extraction work.
BBG prove that pi has no such formula in any base other than 2 (their Theorem 7, by
Bang's theorem and a "private prime" argument in Z[i]), and for base 2 they list the
three formulas below, found by a hand search. Their Appendix D leaves the binary case
open: Research Problem (2) asks "How many Q-linearly-independent binary Machin-type BBP
arctangent zero relations exist?", Problem (7) suggests Zsigmondy-type results in Q(i)
as the tool, and Problem (10) asks the general question behind Parts III and IV below.

The two-term case of the theorem below is Stormer's classical theorem on
arctangent relations (completed by Ljunggren, 1942). The proof uses BBG's own method.

## Theorem

**Every rational linear relation between pi and the generators b_m, a_m (m >= 1) is a
rational combination of these three:**

    (R1)   arctan(1)                     = pi/4
    (R2)   arctan(1/2) +   arctan(1/3)   = pi/4
    (R3)  2arctan(1/2) -   arctan(1/7)   = pi/4

Equivalently: apart from arctan(1), arctan(1/2), arctan(1/3) and arctan(1/7), the
generators are linearly independent over the rationals, together with pi and with
each other. In particular arctan(1/2^m) for m >= 2 and arctan(1/(2^m - 1)) for m >= 4
occur in no relation at all.

**Corollary 1 (larger generator set).** If arctan(1/(2^m + 1)) is also allowed (BBG's
"full set"), the relations are spanned by R1, R2, R3 and the elementary identities

    arctan(1/(2^m - 1)) - arctan(1/(2^m + 1)) = arctan(1/2^(2m-1))      (m >= 1).

**Corollary 2 (speed).** Call the *speed* of a generator the number of bits its series
gains per unit of denominator: m for arctan(1/2^m), and m - 1/2 for
arctan(1/(2^m -+ 1)). Every binary Machin-type formula for pi contains arctan(1)
(speed 1/2), arctan(1/2) (speed 1), arctan(1/3) or arctan(1/5) (speed 3/2). So the
slowest series in any such formula has speed at most 3/2. In the minimal generator
set the only formula attaining 3/2 is Euler's

    pi/4 = 2 arctan(1/3) + arctan(1/7),

up to scaling.

**Answer to BBG's Research Problem (2).** Among the minimal generators there are
exactly two independent zero relations, R2 - R1 and R3 - R1; with the full set,
these and the elementary identities of Corollary 1 (which also settles BBG's
Problem (1), on the duplicate series for arctan(1/3)).

**Remark (CORDIC angles).** In particular pi and the angles arctan(2^(-k)), k >= 1,
used by the CORDIC algorithm are linearly independent over Q. This follows from
Bang's theorem alone and is probably folklore, but no statement of it was found.

## Notation and three facts

For a generator g let z_g be its Gaussian integer: 2^m + i for b_m, and 2^m - 1 + i
for a_m, so that arg z_g = g.

*Fact 1 (unique factorization in Z[i]).* For a rational prime p = 1 (mod 4) fix a
Gaussian prime P above p and put e_p(z) = ord_P(z) - ord_Pbar(z). If
sum c_g * g is a rational multiple of pi (c_g integers), then some power of
prod z_g^(c_g) is real, hence sum_g c_g * e_p(z_g) = 0 for every p.
Consequence ("private prime"): if e_p(z_g) is non-zero for exactly one g in the
relation, then c_g = 0.

*Fact 2.* z_g - conj(z_g) = 2i, so no odd rational prime divides z_g. Hence for every
odd prime p dividing the norm N(z_g), exactly one of P, Pbar divides z_g and
e_p(z_g) is non-zero.

*Fact 3 (norms).* N(2^m + i) = 4^m + 1. For odd n put

    L_n = 2^n - 2^((n+1)/2) + 1,     M_n = 2^n + 2^((n+1)/2) + 1,

so L_n * M_n = 4^n + 1 (Aurifeuille) and gcd(L_n, M_n) = 1. Then
N(2^m - 1 + i) = 2 * L_(2m-1).

A prime p divides 4^m + 1 exactly when the order of 2 mod p is 4d with d | m and
m/d odd. Call p *primitive for 4n* if that order is 4n. Define the *top index* of
b_m as 4m and of a_m as 4(2m - 1). A prime that is primitive for 4n divides N(z_g)
only if top(g) is 4n times an odd number; in particular top(g) >= 4n.

## Two lemmas

**Lemma 1 (Bang, 1886).** For every N >= 2 except N = 6 there is a prime p with the
order of 2 mod p equal to N.

**Lemma 2 (Schinzel 1962, the case a = 2, b = 1).** For every odd n >= 1, M_n has a
prime factor that is primitive for 4n. For every odd n >= 7, so does L_n.
(L_1 = 1, L_3 = 5 and L_5 = 25 do not.)

This is in substance a special case of Schinzel's theorem on primitive prime factors
of a^n - b^n through Aurifeuillian factorizations (Proc. Cambridge Philos. Soc. 58
(1962), 555-562; Stewart, arXiv:1008.1274, describes the result). Equivalently, since
L_n and M_n are the norms of (1+i)^n -+ 1, it is a statement about primitive prime
divisors of the Gaussian Mersenne numbers. The factorization Phi_4n(2) = A_n * A'_n
used below is Example 3.2 of Chamberland, J. Integer Sequences 6 (2003), 03.3.7.
The prime factorization of cyclotomic values in Z[i], with primitive prime ideals,
is the subject of Drauschke and Tasche, "Prime factorizations for values of
cyclotomic polynomials in Z[i]", Arch. Math. 49 (1987), 292-300, which extends the
Sylvester-Kronecker-Zsigmondy theorem to Gaussian integers and improves Redei (1958)
and Sachs (1957); of Steidl and Tasche, Math. Nachr. 140 (1989), 233-247, for any
number field; and of Steidl, Hanler and Tasche, Arch. Math. 53 (1989), 30-39, for
quadratic integers. One of these may contain Lemma 2 (and the existence part of
Lemma 3) outright. Schinzel, Math. Comp. 61 (1993), 441-444, proves that
A^n - zeta_k B^n has a primitive prime ideal for all sufficiently large n, without
an explicit bound. None of the four earlier papers has been read for this note
(copies were requested through interlibrary loan on 21 November 2026); the
self-contained proof below is offered as a re-derivation.

*Proof.* Let t = 1 + i. For odd n, |t^n - 1|^2 and |t^n + 1|^2 are L_n and M_n in
some order (their real parts differ by 2 Re t^n = +-2^((n+1)/2)). Also

    t^n - 1 =   prod over d | n of Phi_d(t),
    t^n + 1 = - prod over d | n of Phi_d(-t),

where Phi_d is the d-th cyclotomic polynomial. Write A_n = |Phi_n(t)|^2 and
A'_n = |Phi_n(-t)|^2. From Phi_d(X) Phi_d(-X) = +-Phi_d(X^2) one gets
A_d * A'_d = Phi_(4d)(2) for odd d. A prime that is primitive for 4n divides
Phi_(4d)(2) only for d = n, so the primitive primes of L_n and M_n are exactly those
of A_n and A'_n. Classically, Phi_(4n)(2) has at most one prime factor that is not
primitive, namely a prime divisor q of n, occurring to the first power. So if
A_n > n and A'_n > n, each has a primitive prime factor.

For |z| = sqrt(2), |Phi_n(z)| is the product of |z^d - 1|^mu(n/d) over d | n, and
2^(d/2) - 1 <= |z^d - 1| <= 2^(d/2) + 1, whence

    A_n, A'_n  >=  2^phi(n) * (c1/c2)^2,
    c1 = prod over odd d of (1 - 2^(-d/2)) = 0.129898...,
    c2 = prod over odd d of (1 + 2^(-d/2)) = 3.22886...

With phi(n) >= sqrt(n) this exceeds n for every odd n >= 309. For odd n from 7 to 801
the statement was checked directly by computer (machin_theorem.py, Parts 0 and 1), and
M_1, M_3, M_5 = 5, 13, 41 are primitive for 4, 12, 20. QED.

In Schinzel's language, the exceptions are n = 4, 12 and 20 for 2^n - 1 (the cases
4m with m = 1, 3, 5, where one Aurifeuillian part has no primitive prime). That list
comes from the computation above, not from Schinzel's paper. One secondary summary
gives 4, 6 and 12 for a related statement; the original must be checked before
quoting either list.

## Proof of the theorem

The argument is BBG's proof of their Theorem 7 (a generator of largest index has a
prime that no other generator in the relation has), with Lemma 2 supplying the
primes that Bang's theorem cannot supply in base 2.

Take a relation and let S be the set of generators with non-zero coefficient. Let S'
be S without a_1, a_2, a_3 (whose Gaussian integers 1+i, 3+i, 7+i have norms 2, 10,
50, involving only the primes 2 and 5).

Suppose S' contains a generator other than b_1. Among the elements of S' pick g with
the largest top index, preferring b_n over a_m in a tie.

* g = b_n with n even. By Lemma 1 there is a prime p primitive for 4n (4n >= 8). It
  divides 4^n + 1 = N(z_g). It divides no other norm in S: a b_m needs n | m with m/n
  odd and m <= n; an a_m needs n | 2m - 1, impossible for even n; and p is not 5.
* g = b_n with n odd, n >= 3. By Lemma 2 there is a prime p | M_n primitive for 4n.
  The only other generator of top index 4n is a_((n+1)/2), with norm 2 * L_n, coprime
  to M_n. Generators of smaller top index are not divisible by p, and p is not 5.
* g = a_m with n = 2m - 1 >= 7. By the tie rule b_n is not in S. By Lemma 2 there is a
  prime p | L_n primitive for 4n, and it divides no other norm in S.

In every case g has a private prime, so by Facts 1 and 2 its coefficient is zero, a
contradiction. Hence S is contained in {b_1, a_1, a_2, a_3}.

Finally, with u = arctan(1/2): a_1 = pi/4, a_2 = pi/4 - u, a_3 = 2u - pi/4 (from
3 + i = (1+i)(2-i) and 7 + i = -i(1+i)(2+i)^2), and u/pi is irrational. So the
relations among pi, b_1, a_1, a_2, a_3 form a 3-dimensional space, spanned by R1, R2,
R3. QED.

Corollary 1 follows by substituting the elementary identity. For Corollary 2: a
formula all of whose series have speed at least 2 uses only b_m (m >= 2), a_m (m >= 3)
and arctan(1/(2^m + 1)) (m >= 3); rewritten in the minimal set it involves only b_m
(m >= 2) and a_m (m >= 3), so by the theorem only a_3 survives, and arctan(1/7) is not
a rational multiple of pi. The uniqueness statement: a combination x*R1 + y*R2 + w*R3
without arctan(1) and arctan(1/2) has x = 0 and y = -2w, which is Euler's formula.

## Computer checks (machin_theorem.py)

* Part 0/1: for odd n up to 801 the only n for which L_n or M_n lacks a primitive
  prime factor are n = 1, 3, 5 (L_n = 1, 5, 25). The size bound covers n >= 309.
* Part 2: among arctan(1/N), N in {1, 2, 3, 5, 7, 8, 9, 32}, the relation space has
  dimension 5 (R1, R2, R3 and two elementary identities); restricted to
  {7, 8, 9, 32} the single relation carries no pi.
* Part 3 (beyond the theorem): for the wider family of series
  Im log(Phi_d(y) / y^deg), y = unit * (1+i)^n, d in {1,3,5,7,9,11,13,15,21}, norms up
  to 2^60, there are 169 series of speed >= 2 and 81 relations among them, none
  giving pi; at speed >= 1.5 there are 12 that do.

## Part II. The wider theorem: all cyclotomic-type binary series

### Setting

Let t = 1 + i. For a root of unity r put

    g(r) = Im Log(1 - r/t)          (principal value; |r/t| < 1, so |g(r)| <= pi/4).

Call two roots of unity *equivalent* if they have the same minimal polynomial over
Q(i); an equivalence class O is an *orbit*. Put gamma(O) = sum of g(r) over r in O,
and let C be the set of rational combinations Gamma = sum c_O * gamma(O).

Expanding the logarithm, Gamma = - sum over k >= 1 of Im( chat(k) * t^(-k) ) / k, where
chat(k) = sum c_O * (sum of r^k over r in O) is a Gaussian integer combination. Since
t^2 = 2i, this is a base-2 BBP-type series. For y = unit * t^n and d odd,

    Im Log( Phi_d(y) / y^deg ) = sum of g(r) over { r : unit * r^n is a primitive d-th root of unity },

a union of orbits; BBG's generators are the case d = 1 (b_m: y = unit * t^(2m);
a_m: y = unit * t^(2m-1)). So C contains every formula of Part I, and every formula
built from cyclotomic polynomials evaluated at unit * t^n.

**C is not every periodic pattern.** The coefficients c_O are constant on orbits, so
the patterns in C are the Galois-invariant ones. A general periodic rational pattern
corresponds to coefficients on individual roots of unity that are algebraic and
Galois-equivariant (for instance a character times a Gauss sum). Those "twisted"
series are outside C. See the last section.

### Structure

*Pairing.* For an orbit O let O* = { i * conj(r) : r in O }. Because
conj(1 - r/t) = 1 - (i conj r)/t, we have g(i conj r) = -g(r), hence

    gamma(O*) = -gamma(O),

and the two series cancel term by term. If O* = O then gamma(O) = 0.

*Atoms.* Put z_O = prod over r in O of (t - r), a Gaussian integer. Then
gamma(O) = arg(z_O) - |O| * pi/4 (mod 2 pi). By order of the roots (m odd):

| order | orbits | atom z_O | index |
|---|---|---|---|
| m | one, O_m | Phi_m(t) | 4m |
| 2m | one, O_2m | Phi_m(-t) | 4m |
| 4m | two | the partners (O_m)*, (O_2m)* | |
| 8m | two, each self-paired | real up to a unit: Phi_m(2), Phi_2m(2) | |
| 2^(j+3) m, j >= 1 | two, partners of each other | unit * Phi_m(+-i * 2^(2^j)) | 2^(j+2) m |

So a set of representatives, one from each pair with O* different from O, is: O_m and
O_2m for every odd m, and one orbit for every (m, j >= 1). The norm of the atom is the
Aurifeuillian part A_m or A'_m of Phi_(4m)(2) in the first two rows, and
Phi_(2^(j+2) m)(2) in the last.

**Lemma 3 (private primes).** Every representative atom, other than those of O_1, O_2,
O_6 and O_10, is divisible by a prime p that is primitive for its index, with
e_p non-zero, and p divides no other representative atom of the same or smaller index.
The exceptional atoms are: z(O_1) = i and z(O_6) = i (units), and
z(O_2) = 2 + i, z(O_10) = -(2 + i), which share the prime 2 + i.

*Proof.* Existence of p: Lemma 2 for the first two rows with m >= 7; directly for
Phi_3(t) = 2 + 3i (13) and Phi_5(t) = -4 + 5i (41); Bang for the last row (index >= 8).
A prime primitive for index N divides Phi_M(2) only for M = N * p^j, so it divides no
atom of smaller index, and the only other representative of the same index is the
second of the pair Phi_m(t), Phi_m(-t). If a prime P above p divided both Phi_m(t) and
one of Phi_m(-t), conj Phi_m(-t) = Phi_m(it), conj Phi_m(t) = Phi_m(-it), then one of
-1, i, -i would be an m-th root of unity modulo P; as m is odd this forces P | 2.
(p does not divide m, being 1 mod 4m.) The same argument with -1 handles the last
row. This gives both e_p non-zero and privacy. The exceptional values are a direct
computation. QED.

### Theorem B

**The rational linear relations among pi and the numbers gamma(O) are spanned by**

    gamma(O) + gamma(O*) = 0           for every orbit O,
    gamma(O_1)  = pi/4,
    gamma(O_6)  = 0,
    gamma(O_10) - gamma(O_2) = pi/4.

(Here gamma(O_2) = arctan(1/2) - pi/4 and gamma(O_10) = arctan(1/2).)

*Proof.* Using the pairing, write a relation over representatives. As in Fact 1, if
sum c_O gamma(O) is a rational multiple of pi, then sum c_O e_p(z_O) = 0 for every p
(the powers of t only contribute multiples of pi/4). Let T be the set of
representatives with non-zero coefficient, other than O_1, O_2, O_6, O_10. If T is not
empty, take the element of largest index. By Lemma 3 it has a private prime p; p is
not 5 because its index is at least 8. So its coefficient is zero, a contradiction.
Hence only O_1, O_2, O_6, O_10 remain, and the prime 5 forces the coefficients of O_2
and O_10 to be opposite. The four values follow from (t-1)/t = i/(1+i),
Phi_6(t)/t^2 = 1/2, (t+1)/t = (2+i)/(1+i) and Phi_10(t)/t^4 = (2+i)/4. QED.

**Corollary B1 (all series for pi).** If Gamma in C is a non-zero rational multiple of
pi, its series coincides with that of

    alpha * gamma(O_1) + beta * gamma(O_6) + delta * (gamma(O_10) - gamma(O_2)),

with value (alpha + delta) * pi/4. Its coefficients come from roots of unity of order
dividing 60. So the cyclotomic-type binary series for pi form a three-parameter family.

**Corollary B2 (speed, and uniqueness of Euler's formula).** The k-th term of that
series is -E(k) * Im(t^(-k)) / k, where, with c_6 and c_10 the Ramanujan sums,

    E(k) = alpha + beta * c_6(k) + delta * (c_10(k) - (-1)^k).

Im(t^(-k)) vanishes exactly when 4 | k, and E(k) depends only on gcd(k, 30):

| gcd(k, 30) | 1 | 2 | 3 | 5 | 6 | 10 | 15 | 30 |
|---|---|---|---|---|---|---|---|---|
| E | a+b+2d | a-b-2d | a-2b+2d | a+b-3d | a+2b-2d | a-b+3d | a-2b-3d | a+2b+3d |

(a, b, d for alpha, beta, delta.) A term with k = s * p, p a large prime, puts p into a
denominator, so the speed of the series is s/2 where s is the least gcd(k, 60) with a
non-zero term. Speed above 3/2 needs E = 0 for gcd 1, 2 and 3; those three equations
have only the zero solution. Speed exactly 3/2 needs E = 0 for gcd 1 and 2, whose
solutions are the multiples of (alpha, beta, delta) = (0, -2, 1), and

    gamma(O_10) - gamma(O_2) - 2 gamma(O_6) = 2 arctan(1/3) + arctan(1/7) = pi/4.

**So among all series for pi in the class C, none is faster than 3/2 bits per unit of
denominator, and Euler's is the only one that fast, up to scaling.**

Part I follows from Theorem B for BBG's generators (and has its own proof above).

*Correction.* An earlier version of this note had a remark here claiming that
logarithm-type terms (series for log |1 - r/t|) cannot cancel the slow terms of a
formula for pi. That remark was false, as the independent review showed: the original
1995 BBP formula is the arctan(1) series plus a logarithm-type series for zero, and
the same device improves on Euler's formula. Part III treats the question properly.

### Computer check (wider_theorem.py)

144 orbits (orders up to 252), 24 self-paired. Pairing holds to 120 digits. Among the
60 representatives, involving 77 primes, there are exactly 3 independent relations,
the three of Theorem B, and only orbits of order 1, 2, 6, 10 occur in them. The
table of E(k) and both linear-algebra statements are confirmed exactly.

## Part III. The full class, and a cheaper formula

### Setting

Let F be the set of all series

    S(rho) = sum over k >= 1 of  rho(k) * 2^(-floor(k/2)) / k,      rho rational and periodic.

In BBP notation these are the degree-1 formulas sum_j 2^(-bj) sum_i a_i / (nj + i) with
n = 2b. F contains the 1995 BBP formula, Bellard's formula, everything in Parts I and
II, the logarithm-type series, and the "twisted" series (for pi*sqrt(3) and the like).

With t = 1 + i and w_r = 1 - r/t, every such series is

    S(rho) = (1/2i) * sum over roots of unity r of  d_r * Log(w_r),

where d is the finite Fourier transform of rho(k) * t^(k mod 2) * i^(floor(k/2)); the
correspondence between rho and d is one to one, and the k-th term of the series is a
non-zero multiple of D(k) = sum d_r r^k. Rationality of rho corresponds to a twisted
equivariance of d: d_(sigma r) = sigma(d_r) for automorphisms sigma fixing i, and
d_(i conj r) = -conj(d_r). (BBP formulas with shifted denominators, 1/(nj + i) with i
not 1..n, add only rational numbers to the value, which the inhomogeneous form of
Baker's theorem handles in the same way.)

### Step 1: Baker's theorem

Log(w_r) and i*pi are logarithms of algebraic numbers. By Baker's theorem, logarithms
of algebraic numbers that are independent over Q are independent over the algebraic
numbers. So S(rho) is an algebraic multiple of pi exactly when d is an algebraic
combination of *multiplicative relations*: integer vectors e with
prod w_r^(e_r) a root of unity.

Applying Baker's theorem to series with periodic coefficients is an established
technique: Baker, Birch and Wirsing (J. Number Theory 5 (1973), 224-236) used it for
Chowla's problem on sum f(n)/n, and Adhikari, Saradha, Shorey and Tijdeman (Indag.
Math. 12 (2001), 1-14) for sums of periodic f(n) P(n)/Q(n); Murty's survey
arXiv:2009.14359 describes both. Those are unweighted sums (the point 1 rather than
1/(1+i)); what is new here is the family and the classification that follows.

### Step 2: which roots of unity can occur

Call a root r of order n *exceptional* if every prime ideal dividing t - r lies over a
prime dividing n. These are the 20 roots 1, i, +-zeta_8, the primitive 6th roots,
zeta_12 and zeta_12^5, the primitive 10th roots, zeta_20^(3,7,11,19), and
zeta_24^(1,5,13,17). For the rows m, 2m, 4m and 2^(j+3)m of the atom table this is
Lemma 3 (with Bang for the last row). The self-paired row 8m needs its own two lines:
its orbits are {+-zeta_8 s} and {+-zeta_8^3 s} with s primitive of order m, and their
atoms are prod (t^2 - i s^2) = i^phi(m) Phi_m(2) and prod (t^2 + i s^2) = +-Phi_2m(2);
Bang gives a prime not dividing 8m except for Phi_1(2) = 1 (the orbit +-zeta_8) and
Phi_6(2) = 3 (the orbit zeta_24^(1,5,13,17)).

Let R0 be the exceptional roots together with the p'-parts of the exceptional roots r
for the primes p dividing N(t - r): these are -1 (from the 10th roots, p = 5), -i (from
the 20th roots, p = 5), and zeta_8^3, zeta_8^7 (from the 24th roots, p = 3). So R0 has
24 elements, all 120th roots of unity, and R0 minus the exceptional roots consists of
roots of 2-power order.

**Every multiplicative relation among the w_r is supported on R0.** Two facts: no prime
above 2 divides t - r (t lies in every prime above 2 and r is a unit), so for P above
an odd prime the condition of a relation at P reads sum_r e_r v_P(t - r) = 0; and if P
divides both t - r and t - r', then r'/r has order a power of the residue
characteristic of P. Now suppose the support S of a relation is not inside R0, and let
r be an element of S minus R0 of *largest order among the elements of S minus R0* (not
of S, whose largest order may belong to an exceptional 24th root). As r is not
exceptional, some P dividing t - r has odd residue characteristic p not dividing
n = ord r. If another r' in S has v_P(t - r') > 0, then ord r' = n p^a > n, so r' lies
in R0; if r' is exceptional, r is its p'-part and lies in R0, a contradiction; if r'
lies in R0 minus the exceptional roots, its order is a power of 2 yet divisible by the
odd prime p, impossible. So P divides no other t - r' in the relation, and e_r = 0, a
contradiction. Hence period 120 covers every period. (This version of the argument is
due to the independent review, review_part3_part4.md, section 2, which found that
"take a root of largest order in the relation", as first written, does not work.)

### Step 3: the relations (full_class_theorem.py)

Among the 24 numbers w_r there are exactly 13 independent multiplicative relations.
Each is verified exactly in Z[zeta_120]. That there are no more is certified by the
matrix of valuations (primes over 2, 3, 5, the only primes involved) and absolute
values (16 embeddings) on the 11 remaining roots: it has full column rank. Rigorously,
its Gram determinant is 1.521e9 +- 0.4 in ball arithmetic (review_valuations.py; the
program's own floating-point check gives smallest singular value 0.72).

**Theorem C (classification of F).** The rational patterns rho whose series is an
algebraic multiple of pi form a 13-dimensional space over Q, all of period 120. Those
whose series is a *rational* multiple of pi (or zero) form an 8-dimensional subspace V,
spanned by (ARG(O) = sum of Im Log w_r, LOG(O) = sum of log |w_r| over r in O):

    ARG(O_1) = pi/4,   ARG(O_6) = 0,   ARG(O_10) - ARG(O_2) = pi/4      (Theorem B)
    LOG(O_6) - 2 LOG(O_1) = 0,          LOG(O_8a) - 2 LOG(O_1) = 0,
    LOG(O_10) - LOG(O_2) - 3 LOG(O_1) = 0,   LOG(O_24) - LOG(O_8b) - 2 LOG(O_1) = 0,
    one sqrt(3)-twisted series with value 0 (roots of order 24 and 6).

(O_8a = {+-zeta_8}, O_8b = {+-zeta_8^3}, O_24 = {zeta_24^(1,5,13,17)}.)
cheaper_formula.py builds V and checks every basis pattern exactly and to 170 digits;
the basis is stored exactly in pi_space_basis_120.json.

*The other five dimensions (five_series_check.py).* The 13 relations span a space that is
stable under zeta -> zeta^b (b = 1 mod 4), and it splits by the characters of that group.
The trivial character gives the seven untwisted series above, and the character of sqrt(3)
the twisted one. The remaining five dimensions (one more for sqrt(3), one each for sqrt(2)
and sqrt(5), two for the quartic characters of Q(zeta_20) over Q(i)) are five more
arctangent-type series sum_j e_j arg w_j, with real coefficients e_j that are conjugate
under zeta -> zeta^b, so that the patterns are rational:

    sqrt(3) (arg w_{zeta_6} - arg w_{zeta_6^5})                          = -pi/sqrt(3)
    a sqrt(2)-twisted series on the roots of order 8 and 24              = -sqrt(2) pi
    a sqrt(5)-twisted series on the roots of order 10 and 20             = -sqrt(5) pi
    two series twisted by th1 = 2cos(pi/10), th3 = 2cos(3pi/10),
      on the roots of order 10 and 20           = (th1 - 3 th3) pi/5 and (3 th1 + th3) pi/5

The last two values equal -pi tan(pi/10) and pi tan(3pi/10) (elementary; this rewriting is
not in Lean). The patterns have periods 24, 12, 40, 40, 40. The first one is the simplest
new series: its power sum is 3i (1, 1, 0, -1, -1, 0) for k = 1, ..., 6. The five values and
the independence of the thirteen patterns are machine-checked without Baker's theorem, and
with it the dimension is exactly 13 (lean/Pilean/PiFormula/FiveSeries.lean, TheoremC3.lean).

### Theorem C explains Bailey's table (derive_bailey_table.py)

Bailey's compendium (version of 8 April 2023, Table 1) lists, for 27 binary degree-1
cases P(1, 2^B, n, .), the number of independent zero relations found by PSLQ, and
says "it is not understood why zero relations occur for certain s, b and n, but not
others." All 27 rows have n = 2B or n = B. Writing k = nj + i, the case n = 2B is the
subspace of V0 (the 7-dimensional zero part of V) of period dividing n, and the case
n = B is the part of V0 on even k of period dividing 2n. By Theorem C only gcd(n, 120)
matters, and V0 has dimension 1, 1, 5, 3, 1, 7 at periods 8, 12, 24, 40, 60, 120 (and 0
at the others), plus one formula for pi at 8, 24, 40 and 120.

**All 27 counts follow, and agree with Bailey's.** For example (2^24, 48), (2^36, 72)
and (2^48, 96) have 5 because gcd(n, 120) = 24; (2^30, 60) and (2^42, 84) have 1 and no
formula for pi because the only zero relation at periods 12 and 60 is the logarithmic
one of (64, 6). The theorem also predicts the rows Bailey does not list: within his
range of bases (b <= 2^60) these are (2^6, 12), (2^18, 36) and (2^54, 108), each with 1
relation, all rewritings of the (64, 6) relation (and every (2^n, n) with 6 | n has
that one relation). And nothing new can appear beyond n = 120. Both families are
machine-checked for every B >= 1, in Bailey's notation: P(1, 2^B, 2B, .) has the count of
gcd(2B, 120), and P(1, 2^B, B, .) has one zero relation if 6 | B and none otherwise.

As a theory-free check of that last claim, a lattice search over all 240 residue-class
sums at period 240 (outside_probe.py 2 240) finds exactly the same 8-dimensional space
and 35 conditions (gap between relations and non-relations: squared length at most
2,769 against about 2^73).

So Theorem C should be presented as the proof and explanation of Bailey's table, not
as a discovery of the counts. Bailey credits the only earlier explanation to
Broadhurst's unpublished manuscript "Vanishing Polylogarithmic Ladders" (2000), which
has not been seen; its author should be asked before any priority is claimed.

**Theorem D (no uniformly faster formula).** No series in F whose value is a non-zero
algebraic multiple of pi has all its terms at k with gcd(k, 120) >= 4. So the bound
"3/2" of Corollary B2 holds in all of F, twisted and logarithm-type series included,
*if speed is measured by the slowest term*. (Step C of full_class_theorem.py computes
the ranks modulo a prime and by SVD; the review recomputed them exactly over Q,
review_space.py.)

**The value formula (sharper, for rational multiples; value_formula_check.py).** If rho is
a rational pattern whose series is a rational multiple of pi, then

    S(rho) = ( 7 rho(1)/12 + rho(2)/8 + rho(3)/6 - 7 rho(7)/12 + rho(9)/6 - rho(14)/8 ) * pi/4.

So the multiple of pi is read off from six terms, all at k with gcd(k, 120) <= 3, and
Theorem D for rational multiples follows at once. Checks: for the BBP formula rho(1) =
rho(9) = 4 and rho(14) = -8 give 4, that is pi; for Bellard's formula rho(2) = 16 and
rho(14) = -16 give pi; for the new formula only rho(9) = 6 is non-zero, giving pi/4. The
six positions are one choice: the value is a linear functional on the 8-dimensional V, and
other sets of positions represent it too. The formula is machine-checked from Baker's
theorem (`PiFormula.value_formula`). It came out of formalizing Theorem D: the certificate
Lean needed was this identity.

Two more facts, both machine-checked and recomputed exactly by the same script:

* *Sharp form* (`PiFormula.theoremD_sharp`, `PiFormula.finrank_fast`, and for algebraic
  multiples `PiFormula.theoremD_alg_sharp`, from Baker's theorem). The patterns of V, and
  even of the 13-dimensional space, with no term at gcd(k, 120) < 4 form a line, spanned by
  -2 [LOG(O_8a) - 2 LOG(O_1)] + 2 [LOG(O_10) - LOG(O_2) - 3 LOG(O_1)]
  + [LOG(O_24) - LOG(O_8b) - 2 LOG(O_1)], of value 0. So there is exactly one "uniformly
  fast" series with a rational value, and it is a zero relation. It has no term at
  gcd(k, 120) = 4 either, and it has one at k = 5. The proof uses only the seven positions
  k = 1, 2, 3, 7, 9, 11, 14: a pattern of V that vanishes there is a multiple of this one.
* *Best possible* (`PiFormula.theoremD_best_possible`, no Baker). For each two of the three
  classes gcd(k, 120) = 1, 2, 3 there is a formula for pi with no term in those two
  classes. With A_1 = ARG(O_1), A_6 = ARG(O_6), A_10 = ARG(O_10) - ARG(O_2):
  A_10 - 2 A_6 = pi/4 has no term at gcd 1 or 2 (this is the (0, -2, 1) of Corollary B2);
  2 A_1 - A_10 = pi/4 has none at gcd 1 or 3; 6 A_1 + 4 A_6 + A_10 = 7 pi/4 has none at
  gcd 2 or 3. Only all three classes together cannot be avoided.

### Logarithms: log 23 has no binary BBP-type formula (log23_probe.py)

Bailey's compendium lists the primes p for which log p has a binary BBP-type formula
(2, 3, 5, 7, 11, 13, 17, 19, 29, 31, ...) and says it is unknown whether all primes have
one. The first prime not on the list is 23. Chamberland (J. Integer Seq. 6, 2003) records
the case of log 23 as open. Borwein, Borwein and Galway (2004, Theorem 4) exclude the
non-Aurifeuillian Machin-type formulas for log 23 and log 89, and say that they could not
exclude the Aurifeuillian ones.

**Theorem G (log 23).** No series of F has a non-zero algebraic multiple of log 23 as its
value. In Bailey's notation: for every B >= 1 and rational A, neither P(1, 2^B, 2B, A) nor
P(1, 2^B, B, A) is a non-zero algebraic multiple of log 23.

*Proof.* (i) *Multiplicative part, without Baker.* If prod (1 - r/t)^(e_r) = xi * 23^m with
the r and xi roots of unity, then m = 0. The private-prime argument of Step 2 works for
relations up to a power of 23, provided each root outside R0 has a good prime whose residue
characteristic is not 23. The primes given by Lemma 3 are 1 mod 4. The primes given by
Bang's theorem have ord_p(2) equal to the index of the atom, and ord_23(2) = 11, so 23 can
only occur for the atom Phi_11(2) = 2047 = 23 * 89; there we take 89. So the relation is
supported on R0. For r in R0 and a prime P above 23, t - r is not in P, because t - r
divides t^120 - r^120 = 2^60 - 1, which is prime to 23. Comparing the two sides at P gives
m = 0. (ii) *Baker's theorem.* A relation sum d_r Log(1 - r/t) = q log 23 with algebraic
d_r and q is a combination of integer relations among the Log(1 - r/t), i pi and log 23.
Each of these is a multiplicative relation as in (i), so none involves log 23, and q = 0.

*Numerical check, free of theory (log23_probe.py).* Lattice reduction on log 2, log 3,
log 5, log 23, log 89, log 683 and the 88 residue-class sums of period 88 finds that log 2,
log 3, log 5, log 683 and log 23 + log 89 are values of period-88 series, and that log 23
alone is not (relations have squared length at most 2,263; non-relations about 2^69).
That is the picture behind the proof: 2^11 - 1 = 23 * 89 and 2^11 + 1 = 3 * 683.

*Limits.* The theorem is for the class F, which contains every P(1, 2^B, n, A) with
n = 2B or n = B. For the other binary families the reduction of Part IV is written for pi
only; for log 23 it has not been checked. Whether Theorem G was already known has been
checked only by literature searches (research/2026-11-22/log23_status.md and
research/2026-11-22-deep/04_novelty_logarithms.md): nothing was found after
Chamberland 2003 and Bailey 2023. The proof is machine-checked
(`PiFormula.no_log23`, from Baker's theorem; `PiFormula.no_rel_23`, unconditional).

### Logarithms of the primes below 100

**Theorem H (primes below 100).** For a prime p < 100, log p is the value of a series of F
if and only if p is one of

    2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73.

The ten primes 23, 47, 53, 59, 67, 71, 79, 83, 89, 97 have no formula in F. So the list of
primes in Bailey's compendium is complete below 100, within F. The "yes" half needs no
Baker; the "no" half is from Baker's theorem.

*Proof, the fifteen primes (no Baker).* Let n >= 1 and let c be a unit of Z[i]. The n roots
r of X^n = c satisfy prod (t - r) = t^n - c, so

    sum over r of log |1 - r/t|  =  (1/2) log N(t^n - c) - (n/2) log 2,

and the left side is a series of F of period 8n: its pattern is -Re(P(k) U_k)/2, with the
power sums P(k) = n c^(k/n) if n divides k and P(k) = 0 otherwise. For (n, c) = (1, 1),
t - 1 = i and the value is -(1/2) log 2; so log 2 is a value, and then log N(t^n - c) is a
value for every n and c. The values of F form a rational vector space, so it is enough to
reach each prime by products and quotients of such norms:

| p | n | c | N(t^n - c) | | p | n | c | N(t^n - c) |
|---|---|---|---|---|---|---|---|---|
| 2 | 1 | 1 | 1 | | 37 | 9 | 1 | 13 * 37 |
| 5 | 1 | -1 | 5 | | 11 | 10 | -i | (3 * 11)^2 |
| 3 | 2 | -i | 3^2 | | 31 | 10 | i | 31^2 |
| 13 | 3 | 1 | 13 | | 43 | 14 | i | (3 * 43)^2 |
| 17 | 4 | i | 17 | | 61 | 15 | 1 | 13 * 41 * 61 |
| 41 | 5 | 1 | 41 | | 19 | 18 | -i | (27 * 19)^2 |
| 7 | 6 | -i | 7^2 | | 73 | 18 | i | (7 * 73)^2 |
| 29 | 7 | -1 | 5 * 29 | | | | | |

*Proof, the ten primes (from Baker).* The proof of Theorem G uses two facts about 23: it
does not divide 2^60 - 1, and every root of unity outside R0 has a good prime of residue
characteristic other than 23. Both hold for each of the ten primes. A prime l can be the
good prime of an atom only if the index of the atom matches ord_l(2), and in each case that
atom has a second prime factor, a "partner", which is used instead:

| l | ord_l(2) | the atom that contains l | partner |
|---|---|---|---|
| 23, 89 | 11 | Phi_11(2) = 2047 = 23 * 89 | each other |
| 47 | 23 | Phi_23(2) = 47 * 178481 | 178481 |
| 53 | 52 | Phi_13(1+i), of norm 53 * 157 | 157 |
| 59 | 58 | Phi_29(-2) = 59 * 3033169 | 3033169 |
| 67 | 66 | Phi_33(-2) = 67 * 20857 | 20857 |
| 71 | 35 | Phi_35(2) = 71 * 122921 | 122921 |
| 79 | 39 | Phi_39(2) = 79 * 121369 | 121369 |
| 83 | 82 | Phi_41(-2) = 83 * 8831418697 | a prime factor of the cofactor |
| 97 | 48 | Phi_3(16i), of norm 97 * 673 | 673 |

So the picture is the same in all 25 cases: log p is a value when p can be separated from
the other primes by norms N(t^n - c), and it is not when p only ever occurs together with
a partner. For example log 23 + log 89 = log(2^11 - 1) is a value (n = 22, c = -i, where
t^22 + i = -2047 i), although neither log 23 nor log 89 is.

*Limits.* As for Theorem G, the statement is for the class F (n = B or n = 2B). Each of
the ten primes needed its own partner in Lean. The criterion for all primes at once is
Theorem K below.
Machine-checked: `PiFormula.log_primes_below_100` (from Baker's theorem),
`PiFormula.isFValue_log_of_mem` (the fifteen primes, unconditional),
`PiFormula.not_isFValue_log_of_mem` (the ten primes, from Baker's theorem),
`PiFormula.isFValue_log_23_add_log_89`.

### Which logarithms have a formula: the criterion (log_prime_criterion.py, log_probe.py)

**Theorem K (criterion).** Let y be a positive rational number. The following are
equivalent.

(a) log y is the value of a series of F.

(b) log y is a rational combination of log 2 and the numbers log N((1+i)^n - c), with
    n >= 1 and c in {1, -1, i, -i}.

(c) Some power y^M, M >= 1, is a product of integer powers of 2, of the numbers 2^m - 1
    (m >= 1), and of the numbers 2^n - 2^((n+1)/2) + 1 and 2^n + 2^((n+1)/2) + 1 (n odd),
    the two factors of 4^n + 1.

Moreover (d): if log y is the value of a binary degree-1 series P(1, 2^B, n, A), for any B
and any n, then (c) holds. So no other binary family reaches a logarithm of a rational that
F does not reach.

*For a prime p this is a finite test.* Let n = ord_p(2) and let g be the primitive part
that contains p: g = Phi_n(2) if n is not 4 modulo 8; if n = 4d with d odd, g is the one of
|Phi_d(1+i)|^2, |Phi_2d(1+i)|^2 that p divides (their product is Phi_n(2)). Write
g = p^x R with p not dividing R. Then log p is a value of F if and only if R = 1, or R is a
prime q dividing n and log q is a value of F. In words: p must be alone in its primitive
part, apart from at most one prime q dividing the index, which must pass the same test.

*Proof.* (b) => (a), without Baker. Each log N(t^n - c) is a value (proof of Theorem H),
log 2 is a value, and the values of F form a rational vector space.

(b) <=> (c). For n = 2m, t^n = 2^m i^m, so N(t^n - c) is (2^m - 1)^2, (2^m + 1)^2 or
4^m + 1, and 2^m + 1 = (2^(2m) - 1)/(2^m - 1), 4^m + 1 = (2^(4m) - 1)/(2^(2m) - 1). For n
odd, N(t^n - 1) and N(t^n + 1) are the two factors of 4^n + 1 (Lemma 2), and so are
N(t^n - i), N(t^n + i). Conversely (2^m - 1)^2 = N(t^(2m) - i^m). Logarithms of different
primes are independent over the rationals, which turns (b) into (c).

(a) => (c), from Baker's theorem. Let log y = sum d_r Log(1 - r/t), the sum over the N-th
roots of unity r (Step 1). The relation sum d_r Log(1 - r/t) - log y = 0 has algebraic
coefficients, so it is a combination of integer relations among the Log(1 - r/t), i pi and
log y, and one of them has a non-zero coefficient m at log y:

    prod (1 - r/t)^(e_r) = xi y^m,        xi a root of unity.

Take the norm from K = Q(i, zeta_N) to Q(i). The norm of t - r is a power of
a_O = prod over s in O of (t - s), where O is the set of conjugates of r over Q(i); a_O is
a Gaussian integer. So y^(mD), D = [K : Q(i)], is, up to a unit, a product of integer
powers of t and of numbers a_O. Each a_O is a product of integer powers of numbers t^n - c:
if r has order M, put g = gcd(M, 4), n = M/g and c = r^n; the roots of X^n = c are the
conjugates of r together with roots of unity of smaller order, which come in full sets of
conjugates; so a_O = (t^n - c) / prod a_O', and one concludes by induction on M. Taking
absolute values gives (b) for a multiple of log y.

(d), sketch. The series P(1, 2^B, n, A) is sum c(k) x^k / k with x = 2^(-B/n) and c
periodic with values in Q(x), so its value is a combination of the Log(1 - r x) with
algebraic coefficients, and Baker's theorem gives prod (1 - r x)^(e_r) = xi y^m as before.
Write 1/x = 2^(b/n') in lowest terms and let L be a cyclotomic field containing the r, xi
and zeta_8. The norm from L(2^(1/n')) to L of 2^(b/n') - r is, up to sign,
2^b - r^(n') if n' is odd and sqrt(2)^b - r^(n'/2) if n' is even; in both cases it is a
root of unity times t^(b') - r' for some b' and some root of unity r', and
t^(b') - r' = prod over s^(b') = r' of (t - s). So a power of y is again, up to roots of
unity and powers of t, a product of powers of numbers t - s, and the argument for (a) => (c)
applies.

The test for a prime. The numbers of (c) are generated, up to powers, by 2 and the
primitive parts: Phi_m(2) for m not 4 modulo 8, and for m = 4d the two numbers
|Phi_d(1+i)|^2, |Phi_2d(1+i)|^2. A prime p divides the primitive parts of index
ord_p(2) p^j only; for j >= 1 exactly once. In a relation p^M = 2^s prod g^(E_g), take the
part g of largest index with E_g non-zero: its primes of exact order equal to that index
occur in no other part of the relation, so they all equal p; this part is the g of the
test, and its other prime, if any, divides the index. Dividing out leaves a relation for q
among parts of smaller index.

*What is machine-checked.* The equivalence of (a), (b) and (c), in full, for every positive
rational y (22 November 2026).

- (b) => (a), without Baker: `PiFormula.logSpan_le_fValues`, with the families
  `PiFormula.isFValue_log_two_pow_sub_one` (log(2^m - 1), every m),
  `PiFormula.isFValue_log_L` and `PiFormula.isFValue_log_M` (the two factors of 4^n + 1,
  every odd n).
- (a) => (b), from Baker's theorem: `PiFormula.mem_logSpan_of_isFValue_log`, and the
  equivalence `PiFormula.isFValue_log_rat_iff` (`isFValue_log_iff` for a quotient a/b of
  positive integers, `isFValue_log_nat_iff` for a positive integer).
- (b) <=> (c): `PiFormula.logSpan_eq_baseSpan` and `PiFormula.log_mem_span_iff_pow`.
- (a) <=> (c), the criterion in elementary terms: `PiFormula.isFValue_log_rat_iff_pow`.
  Its statement uses only the definition of a series of F and the set
  `PiFormula.baseNumbers` = {2} ∪ {2^m - 1} ∪ {2^(2j+1) - 2^(j+1) + 1} ∪
  {2^(2j+1) + 2^(j+1) + 1}: log y is a value of F if and only if there are k >= 1, base
  numbers g_1, ..., g_n and integers e_1, ..., e_n with y^k = g_1^(e_1) ... g_n^(e_n), an
  identity between rational numbers. The half (c) => (a) alone needs no Baker:
  `PiFormula.isFValue_log_of_pow`.
- With the formal proof of Baker's theorem in the library these hold with no hypothesis:
  `PiFormula.Unconditional.isFValue_log_rat_iff_pow` and the others. They depend on the
  three standard axioms only.

*The formal proof of (a) => (b)* takes a route that avoids the norm. From Baker's theorem
(`baker_no_extra`) a formula for log(a/b) gives a relation
prod (1 - r/t)^(e_r) = xi (a/b)^m with m non-zero; cleared of denominators it is an identity
between two products of numbers t - r, powers of t and positive integers, up to xi. With
zeta = exp(2 pi i/N), N = 4K a common multiple of the orders, and i = zeta^K, the identity
is the value at zeta of a polynomial identity with integer coefficients. So it holds at
zeta^a for every a prime to N (same minimal polynomial; `aeval_pow_of_coprime`), and for
a = 1 modulo 4 this fixes i and t and replaces every r by r^a (`cleared_conj`). Taking
logarithms of absolute values and adding over these a, m log(a/b) becomes an integer
combination of log 2 and of the sums of log|t - r^a| over a. By Möbius inversion over the
condition "a prime to N" each such sum is an integer combination of sums over all a = 1
modulo 4 that are multiples of an odd divisor d of N (`sum_filter_coprime`), and such a sum
runs over a full set {u^j x} of roots of X^M = x^M, each the same number of times, with x^M
a fourth root of unity; so it is a multiple of log|t^M - c| (`sum_log_coset_mem`,
`sum_log_mod_four_mem`, `sum_log_coprime_mem`). This replaces the induction on the order in
the proof above by one explicit formula.

*The test for a prime is machine-checked too* (22 November 2026, `LogPrimeTest.lean`).
`PiFormula.primPart ℓ` is the primitive part that contains ℓ: with n the order of 2 modulo
ℓ, it is Phi_n(2) if n is not 4 modulo 8, and for n = 4d the one of N(Phi_d(1+i)),
N(Phi_d(-1-i)) that ℓ divides.

- `PiFormula.isFValue_log_prime_iff_explicit`: for an odd prime ℓ that does not divide
  2^60 - 1, log ℓ is a value of F if and only if the primitive part is ℓ^x, or ℓ^x q with q a
  prime dividing n and log q a value of F. This is the test as stated above.
- `PiFormula.isFValue_log_prime_iff`: the same in the form "every prime q other than ℓ that
  divides the primitive part divides n and has log q a value of F";
  `PiFormula.primPart_intrinsic_unique`: there is at most one such q.
- `PiFormula.isFValue_log_of_dvd`: the twelve primes that divide 2 (2^60 - 1), which are
  2, 3, 5, 7, 11, 13, 31, 41, 61, 151, 331, 1321, all have log p a value of F.
- `PiFormula.isFValue_log_prime_classification`: the two together, for every prime.
- With the formal proof of Baker's theorem these hold with no hypothesis
  (`PiFormula.Unconditional.isFValue_log_prime_classification` and the others).

How the formal proof goes. (i) The logarithm of every primitive part is a value of F, with
no Baker (`isFValue_log_cyclotomic_two`, `isFValue_log_Aplus`, `isFValue_log_Aminus`): by
induction on n from prod over d | n of Phi_d(x) = x^n - 1, starting from the values
log(2^n - 1) and log N(t^n -+ 1). So log ℓ is a value as soon as the other primes of the part
have logarithms that are values, and conversely when there is only one other prime.
(ii) A second prime q of order n in the same part excludes ℓ
(`not_isFValue_log_of_partner`, from Baker's theorem): this is the argument of Theorem G made
general. A prime of Phi_n(2) that does not divide n has order n; for n = 4d the two halves
have no common prime of order n (`not_dvd_norm_P_and_Q`, from Lemma 3); so every orbit of
roots of unity whose atom contains ℓ also has the good prime q, and `goodPrimes_ne`,
`not_isFValue_log` apply. (iii) A prime of Phi_n(2) that divides n is the largest prime
factor of n and divides Phi_n(2) once (from the Tau Ceti library, where these facts are
proved for Bang's theorem), which gives the form ℓ^x q.

Not machine-checked: (d). Also, Lean proves the test as a theorem; evaluating it for all
primes below 10^7 (the list below) is a computation by python/log_prime_criterion.py in
exact arithmetic, and is not a Lean proof prime by prime. In Lean prime by prime: the 15
primes below 100 with a formula and the ten without (Theorem H), the twelve primes that
divide 2 (2^60 - 1), and 433 and 38737 below.

*The list.* The test decides every prime. Below 10^7 exactly 51 primes have a formula:

    2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73, 109, 113, 127, 151, 241, 257,
    331, 337, 397, 683, 1321, 1429, 1613, 2113, 2731, 5419, 8191, 14449, 26317, 43691,
    61681, 65537, 87211, 131071, 174763, 246241, 262657, 268501, 279073, 312709, 524287,
    525313, 599479, 2796203, 4327489, 7416361.

*Comparison with the published lists.* The list A104885 of the OEIS ("primes whose
logarithms are known to possess binary BBP formulas", 46 terms up to 312709, from Borwein
and Bailey's book of 2004) passes the test with one exception, 38737, and the test finds no
other prime below 312709. Bailey's compendium of 2023, which says that its list is not
complete, has no entry that fails the test; it does not contain 38737, and it omits, for
example, 331 = Phi_30(2) and 65537 = Phi_32(2) (as transcribed in
research/2026-11-22-deep/04_novelty_logarithms.md).

*38737.* Phi_72(2) = 2^24 - 2^12 + 1 = 433 * 38737, and neither prime occurs anywhere else.
So log 433 + log 38737 is a value of F and neither logarithm is. Both statements are
machine-checked, with no hypothesis: `PiFormula.Unconditional.not_isFValue_log_38737`,
`PiFormula.Unconditional.not_isFValue_log_433`, `PiFormula.isFValue_log_433_add_log_38737`.
A numerical search that uses none of the theory agrees (python/log_probe.py, period 144:
it finds log 2 and log 433 + log 38737 and neither log 433 nor log 38737; relations have
squared length at most 7,539, non-relations about 2^69). So the entry 38737 of A104885
appears to be an error, unless it rests on a formula of a kind that (d) does not cover; we
know of none.

*Where 38737 comes from* (research report
research/2026-11-22-prime-test/01_38737_and_unique_primes.md, which read the sources). The
entry is already in the list of Chamberland's paper of 2003 (J. Integer Seq. 6, Article
03.3.7), which says the list was obtained by calculations with Maple and gives no formula
for 38737; 433 is not on his list, and the product 433 * 38737 is not among the products of
two primes he lists. Borwein and Bailey's book (second edition, 2008, p. 130) and the OEIS
entry (2005, unchanged since) repeat it. A possible cause, which is our guess and not stated
anywhere: Chamberland's construction with Phi_144((1+i)/2^n) gives the logarithm of
|Phi_144(1+i)| = 2^24 - 2^12 + 1 = 433 * 38737, a product, and one factor was kept. No
erratum was found.

*Unique primes.* A prime p is called unique in base 2 (Caldwell and Dubner) if it is the
only prime of its order, that is, if Phi_n(2) divided by gcd(Phi_n(2), n) is a power of p;
these are OEIS A144755. The 51 primes of the list are 2, the 31 unique primes of base 2
below 10^7, and 19 further primes that are alone only in one of the two halves of a
Phi_4d(2) (29 and 113, from Phi_28(2) = 29 * 113; 37 and 109; and so on). We checked the
count (28 primes with n not 4 modulo 8, and 5, 13, 41 with n = 4, 12, 20). The research
report found no earlier link between unique primes and BBP-type formulas for logarithms.
An example where the exponent x of the test is 2: the Wieferich prime 1093 has order
364 = 4 * 91, and 1093^2 divides its half |Phi_182(1+i)|^2 (checked); the half has other
prime factors, so log 1093 is not a value of F.

*Limits.* The equivalence of (a), (b), (c) and the test for a prime are machine-checked.
The statement (d) is proved here on paper and is not machine-checked. The list above is the
output of the test, computed in exact arithmetic by a program; Lean proves the test, and
proves the individual primes named above, but does not run the test on the other primes of
the list.

### Arctangents: arctan(2/7) has no binary BBP-type formula (arctan_probe.py)

Bailey's compendium says that it is not known whether arctan(2/7) possesses a binary BBP
formula, and Borwein, Borwein and Galway (2004, section 2.5) name it as the first
arctangent for which they could find none.

**Theorem I (arctan(2/7)).** No series of F has a non-zero algebraic multiple of
arctan(2/7) as its value. In Bailey's notation: for every B >= 1 and rational A, neither
P(1, 2^B, 2B, A) nor P(1, 2^B, B, A) is a non-zero algebraic multiple of arctan(2/7). The
same holds for arctan(5/8) and arctan(4/9). On the other hand

    arctan(2/7) + arctan(6/11)  =  pi/4 - arctan(1/129)

is a value of F.

*Proof.* The number 7 + 2i has norm 53. Put a = 7 + 2i and b = 7 - 2i, so that a b = 53 and
exp(2i arctan(2/7)) = a/b. (i) *Multiplicative part, without Baker.* If
prod (1 - r/t)^(e_r) = xi (a/b)^m with the r and xi roots of unity, then m = 0. The proof of
Theorem G applies with a/b in place of 23. Every root of unity outside R0 has a good prime
of residue characteristic other than 53 (the table of Theorem H: the only atom that
contains 53 is Phi_13(1+i), of norm 53 * 157, and 157 is used). Such a prime contains
neither a nor b, so the relation is supported on R0. A prime P above 53 contains exactly
one of a and b (both would give a + b = 14 in P), and no t - r with r in R0, because
t^120 - r^120 = 2^60 - 1 is prime to 53. Comparing the two sides at P gives m = 0.
(ii) *Baker's theorem*, as in Theorem G, with the logarithm 2i arctan(2/7) in place of
log 23.

The same proof gives arctan(y/x) whenever x^2 + y^2 is one of the ten primes of Theorem H
that is 1 modulo 4: 53 = 7^2 + 2^2, 89 = 8^2 + 5^2 and 97 = 9^2 + 4^2.

*The positive half (no Baker).* The arctangent-type sum over the thirteenth roots of unity
is a series of F of period 104. Its value is arg((t^13 - 1)/t^13) = arg(129 - i)
= -arctan(1/129), up to a multiple of 2 pi. So arctan(1/129) is a value of F. Since
(7 + 2i)(11 + 6i) = 65 + 64i and (65 + 64i)(129 + i) = 8321 (1 + i), the sum
arctan(2/7) + arctan(6/11) equals pi/4 - arctan(1/129). This is the same picture as for
log 23 and log 89: Phi_13(1+i) = -64 + 65i = i (7 + 2i)(11 + 6i), so 7 + 2i only ever
comes with its partner 11 + 6i, of norm 157.

*Numerical check, free of theory (python/arctan_probe.py).* Lattice reduction on pi,
arctan(1/2), arctan(2/7), arctan(6/11) and the 104 residue-class sums of period 104 finds
that pi, arctan(1/2) and arctan(2/7) + arctan(6/11) are values of period-104 series, and
that arctan(2/7) alone is not (relations have squared length at most 2,177; non-relations
about 2^68).

*Limits.* As for Theorem G, the theorem is for the class F (n = B or n = 2B). Whether it
was already known has been checked only by a literature search
(research/2026-11-22-deep/16_last_gaps.md): the question is stated as open in the two
sources above, and no proof of exclusion was found. Machine-checked, with no hypothesis:
`PiFormula.Unconditional.not_isFValue_arctan_two_sevenths`,
`PiFormula.Unconditional.no_arctan_two_sevenths` and the two Bailey forms;
`PiFormula.isFValue_arctan_two_sevenths_add` and `PiFormula.isFValue_arctan_inv_129`
(these two do not use Baker's theorem at all).

### Two cost measures, and the optimum in each

*Standard measure (published).* Terms per bit: the number of non-zero entries per
period divided by the bits gained per period. This is the cost of the classical BBP
algorithm, by which Bellard's formula (0.7) is "43% faster" than BBP's (1).

*Prime measure (this note).* A prime p first enters a denominator at k = s*p, where s
is the least multiplier with rho(s*p) non-zero; s depends on p modulo 120. A window at
bit m then needs p only up to 2m/s. So the per-prime state of the window algorithm is

    1.44 * 2 * mean(1/s)   bits per bit of position,

the mean over the 32 classes of primes modulo 120.

The two measures rank formulas differently (exact_optimum.py, all exact):

| formula | terms per bit | mean(1/s) | state, bits per bit |
|---|---|---|---|
| BBP 1995 | 1 | 3/4 | 2.16 |
| Bellard 1997 | 7/10 | 1/2 | 1.44 |
| Euler (Hutton-Euler) | 7/10 | 1/3 | 0.962 |
| best by terms per bit (Huvent's rate) | **2/3** | 5/12 | 1.20 |
| best by mean(1/s) (Theorem E) | 11/12 | **7/24** | 0.842 |

**Theorem E (the optimum, both measures).** Over all series in F for a non-zero
rational multiple of pi:

* the least number of terms per bit is 2/3, attained (up to scaling) by exactly two
  formulas, both of base 2^12 and length 24 with 8 terms:

      pi/4 = (1/512)  sum_j 2^(-12j) [ 768/(24j+3) + 512/(24j+4) + 128/(24j+6) - 16/(24j+12)
                                        - 16/(24j+14) - 12/(24j+15) + 2/(24j+20) - 1/(24j+22) ],
      pi/4 = (1/1024) sum_j 2^(-12j) [ 2048/(24j+2) - 1024/(24j+4) + 192/(24j+9) + 128/(24j+10)
                                        + 32/(24j+12) - 4/(24j+18) - 4/(24j+20) - 3/(24j+21) ];

  both formulas are Huvent's: they appear, with exactly these coefficients, among his
  formulas for pi with denominator y^24 - 2^12 ("Formules BBP", 2001), and his rate
  8/12 is the default of y-cruncher's digit extractor. Bellard asked in 1997 whether
  a formula faster than his exists; Huvent found these two; what is new is that 2/3
  cannot be beaten and that these two are the only formulas attaining it.
* the least mean(1/s) is 7/24. It is attained on exactly two 2-dimensional subspaces
  of V (which contain the 22 optimal vertices), so the optimal formulas, normalised to
  value pi/4, form two one-parameter families; the fewest terms among them is 55 per
  120 (the formula below). An earlier version said "attained by 22 formulas", which
  the review showed to be wrong (it built a 63-term optimal formula that is none of
  the 22);
* no formula is better than another in both measures except as follows: the
  non-dominated pairs (mean(1/s), terms per bit) are exactly (7/24, 11/12),
  (1/3, 7/10) and (5/12, 2/3). Euler's formula is one of them; Bellard's ties with it
  in terms per bit (7/10) and is worse in mean(1/s) (1/2 against 1/3).

By Theorem F (Part IV) the same optima hold for every binary degree-1 BBP-type formula
of any base and length, since the terms outside the F_2 part can only add terms.

The prime-measure optimum is attained, for example, by

    pi/4 = 2 arctan(1/3) + arctan(1/7) + Z,

    Z =   2 log|1 - 1/t + 1/t^2|  -  2 log(1 - 1/2)
        +   log|1 - i/t^2 - 1/t^4|  -  log(1 + 1/2)  -  2 log|1 - 1/t|,

where every logarithm is expanded as a power series in 1/t. As a number Z is zero
(2 log(1/2) - 2 log(1/2) + log(3/4) - log(3/2) + log 2), but its series is not zero
term by term: it cancels the terms k = 3p of Euler's series for every prime
p = 1 (mod 4). In closed form the result is

    pi = 4 * sum over k >= 1 of rho(k) * 2^(-floor(k/2)) / k,

with rho of period 120 given in pi_formula_120.json (55 non-zero entries, all
half-integers).

*Proof of optimality.* Both costs depend only on which entries of rho vanish, and
adding zeros never raises them. If a pattern carrying pi lies in a flat (the subspace
cut out by its zero entries) of dimension >= 2, some further entry can be made zero
while keeping pi (otherwise the pi functional would be proportional to every
remaining coordinate, forcing dimension 1). So both minima are attained at vertices:
patterns fixed up to scale by their zero entries. V has dimension 8 and its 119
non-trivial entries give only 35 distinct conditions "entry = 0", so every vertex
solves 7 of the 35: 6,724,520 candidates, all tried exactly (exact_optimum.py). For each
choice the vertex is the line through the vector m of signed 7x7 minors, a condition
vanishes on it iff an integer determinant is 0, and all these integers are below the
Hadamard bound 2^97; they are computed modulo four primes with product above 2^124,
so "zero modulo every prime" means zero. 6,044,222 choices have rank 7; they give
1,519,237 distinct vertices carrying pi. The optima are 7/24 (22 vertices) and 2/3 (2
vertices). Each optimal formula is then recomputed in rational arithmetic and summed
to 60 digits. (An earlier floating-point search, cheaper_fast.py, found the same 7/24
and the same 22 winners.)

*A short proof of the two bounds (theorem_e_experiment.py; machine-checked).* The
enumeration is not needed for the bounds themselves. The 119 conditions fall into 35
classes, and the 32 classes of primes into four types (c mod 12 = 1, 5, 7, 11), so
mean(1/s) is the mean of four numbers 1/s. A case tree with 13 leaves gives 7/24: if a
unit entry is non-zero some s is 1; otherwise all unit entries vanish; then the entries at
2c are handled the same way; if all entries with gcd(k, 120) <= 2 vanish, either the two
classes at 3c with c = 7, 11 (mod 12) are non-zero (two types have s = 3, the other two
s <= 4) or they vanish (two types have s = 3, the other two s = 4, by Theorem D). For the
bound 40 a branch-and-bound tree of about 1,500 nodes suffices.

### Computing pi and checking it with two formulas (verify_pair_optimum.py)

Takahashi (Ramanujan J. 51 (2020), 177-186) computes hexadecimal digits of pi with one
formula and checks them with a second formula that shares most of its series, instead of
running one formula twice at shifted positions. He reports 64 terms per 60 bits for his two
formulas (base -2^30), against 80 for Huvent's formula run twice, and calls Huvent's the
BBP-type formula with the least number of terms.

In F this is a question about zero relations. Scale two formulas for pi to the same value
and let z be their difference; z is a zero relation. A wrong value of one series changes the
two results differently exactly at the positions where z is not zero. A series on which the
two formulas agree therefore has to be computed twice (Takahashi does this with his S(10,5)
and S(30,15), which are the same series). So the cost of a checked computation is

    |supp z|  +  2 |supp rho minus supp z|,

minimised over the zero relations z and the formulas rho of F.

**Theorem J (the cheapest checked computation).** Let rho_1 and rho_2 be two different
series of F with the same non-zero rational multiple of pi as value. Then the cost of
computing with one and checking with the other is at least 60 terms per 120 positions, that
is, one term per bit. Takahashi's two formulas attain it: their cost is exactly 60.

For comparison, per 120 positions (60 bits):

- Huvent's formula twice: 80, and no single formula run twice does better (Theorem E).
- Huvent's two formulas as a pair: 40 + 40 - 15 = 65.
- Takahashi's pair: 60. In the coordinates of Theorem C his formulas are 8 A1 - 4 A10 and
  4 A1 - 4 A6; they have 42 and 50 terms, share 34 positions and agree at two of them
  (30 and 90), so the cost is 42 + 50 - 32 = 60.

His own count, 64, treats S(12,3) and S(20,5) as different series, and likewise S(12,9) and
S(20,15); they are the same series up to the factors 3 and 5. Merged, his pair costs 60, and
no pair in F costs less. Merging means one modular exponentiation modulo 15(4k+1) instead of
two; whether that is free in an implementation has not been tested.

*Proof.* A search tree on the 35 classes of positions. The tree first branches on the zero
relation z: "class i vanishes or not". A branch is closed when the classes known not to
vanish have weight at least 60. Exactly twelve branches end in a single zero relation with
fewer than 60 terms (43, 50, 55, 55, 55, 56, 56, 57, 57, 59, 59, 59 terms). There the tree
continues with rho inside the zero set of z, until (terms of z) + 2 (terms of rho where z
vanishes) is at least 60. Every step comes with an integer linear identity. The tree has
8,083 nodes on z and 180 on rho, with 17,953 derived facts; Lean checks it with a verified
checker (`PiFormula.checkPair_sound`, `PiFormula.pairCert_ok`).

*Also computed, not in Lean (python/verify_pair_optimum.py).* Takahashi's pair is the only
one at 60. If no series may be computed twice, the least cost is 63, attained by seven
supports of period 120. In base 2^12 alone the least cost is 65.

*Limits.* The statement is for the class F and for this way of counting: one for each
series that is computed, and a series on which the two formulas agree counted twice.
Machine-checked: `PiFormula.Unconditional.pairCost_ge` (no hypothesis),
`PiFormula.pairCost_takahashi`, `PiFormula.takahashi1_formula`,
`PiFormula.takahashi2_formula` (his two formulas in Bailey's notation P(1, 2^60, 120, A),
both equal to pi), `PiFormula.pairCost_huvent`.

### Checks on the new formula (new_formula_check.py, decompose_formula.py)

* The series equals pi/4: proved in Lean (`PiFormula.new_formula_series`, standard axioms
  only), with rho exactly as in pi_formula_120.json; also checked to 1000 digits.
* Hex digits of pi after position 1,000,000 extracted term by term with the new
  formula: 6C65E52CB459350050E4BB17, identical to Euler's formula and to the
  independent block-rational program.
* Primes actually needed for a window at bit 4,000,002: Euler 194,397 (0.9612 bits
  per bit), new 171,693 (0.8412 bits per bit).

### Measured in the native engine (21 November 2026)

Both formulas now run through the same Rust + CUDA program (`piwindow --formula
euler|new`; engine/src/word2.rs and kernel.cu hold the new one). The fast routines for
the new formula agree with a term-by-term reference on every prime tested (about
39,000 primes at five positions, no mismatch), and the program's output agrees with
Euler's at every position tried, on GPU and CPU.

| window | Euler | new | change |
|---|---|---|---|
| primes used, position 10^10 | 1,161,504,905 | 1,021,859,656 | -12.0% |
| 1,000,000 hex digits at 10^9 | 9.47 - 9.53 s | 8.38 - 8.52 s | -11% |
| 1,000,000 hex digits at 10^10 | 92.8 s | 80.5 s | -13% |
| 64 hex digits at 10^9 | 1.15 s | 1.14 s | none |
| 64 hex digits at 10^10 | 11.5 - 12.3 s | 11.1 - 11.3 s | about -4% |
| 64 hex digits at 10^11 | 114.1 s | 107.5 s | -6% |

(Core Ultra 9 275HX, RTX 5090 Laptop GPU; alternating runs, three per formula at 10^9
and for the short window at 10^10, one per formula otherwise; the 10^11 pair ran
while another job used part of the CPU. The million-digit outputs match the stored
reference digits, and both runs at 10^11 reproduce the published digits
9C381872D27596F81D0E48B95A6C46.)

Long windows gain the full 12%, because their cost is the exact summation of one
fraction per prime. Short windows gain little: they are limited by the prime sieve,
which covers the same range for both formulas (the new one only lets the sieve skip
the residue class 1 mod 4 in the top quarter), and each small prime costs more work
with the new formula (six series instead of four).

### What this does and does not give

It gives a formula that needs 12% fewer primes than Euler's in the window algorithm,
a proof that no formula in F does better in that measure, a proof that Huvent's rate
of 2/3 terms per bit is optimal in the standard measure, and a measured 11-13% saving
of time on long windows. The new formula is worse than Huvent's and Bellard's for the
classical term-by-term algorithm. None of this is a route to a record for all digits
of pi.

## Part IV. Every other binary degree-1 family

(Details, tables and programs: outside_family_findings.md, outside_probe.py,
outside_structure.py, outside_twisted.py.)

F is the family with weights 2^(-floor(k/2)). The other binary degree-1 BBP-type
series have weights 2^(-floor(k/n)) for some n:

    F_n :  S(rho) = sum over k >= 1 of rho(k) * 2^(-floor(k/n)) / k,     rho rational, periodic.

Every formula sum_j 2^(-Bj) sum_i a_i / (Nj + i) is of this kind (n = N / gcd(B, N)),
F = F_2, and F_n lies inside F_(n n'). Costs compare as n * mean(1/s); F's optimum is
2 * 7/24 = 0.5833 and Euler's formula costs 0.6667.

**Lemma (sub-series).** Let n1 = n/2 for even n and n1 = n for odd n. If a series of
F_n equals q*pi with q rational, then its sub-series over the k divisible by n1 already
equals q*pi, and the remaining terms sum to zero.

*Proof.* Put c = 2^(1/n) and x = 1/c, so 2^(-floor(k/n)) = c^(k mod n) x^k and
S(rho) = - sum_r d_r Log(1 - r x) with d_r = (1/P) sum_k rho(k) c^(k mod n) r^(-k).
By Baker's theorem, d is an algebraic combination sum_j x_j e_j of rational relation
vectors e_j (those with sum_r e_j(r) Log(1 - r x) a rational multiple of i*pi).
Over the field of all roots of unity the polynomial X^n1 - c^n1 is irreducible
(c^n1 is 2 or sqrt(2); neither is a p-th power there, nor of the form -4y^4, because
no 2^(1/m) with m >= 3 lies in a cyclotomic field). So for each n1-th root of unity
eta there is a field automorphism h with h(c) = eta*c fixing every root of unity.
Applying h to d gives h(d_r) = d_(r/eta), which is the weight vector of the series with
rho(k) replaced by eta^k rho(k); and h(d) = sum_j h(x_j) e_j, so that series has the
value h applied to the coefficient of pi, which is q again. Averaging over eta leaves
exactly the terms with n1 | k. QED.

**Theorem F.** For every n, a series of F_n for a non-zero rational multiple of pi
costs at least 0.5833; for odd n there is none at all. So among all binary degree-1
BBP-type formulas for pi, of any base 2^B and any period, the formula of Theorem E is
optimal.

*Proof.* The sub-series over n1 | k is, in the index k/n1, a series of F_2 (n even)
or of F_1 inside F_2 (n odd) with the same cost; the other terms can only bring
primes in earlier. Apply Theorem E. For odd n, Theorem C shows that F_2 patterns
supported on even k carry no pi. QED.

*Computations.* Lattice-reduction searches over the class sums (theory-free) for
n = 1, ..., 10 and 12 at the periods listed in outside_family_findings.md agree in
every case: the space of pi-patterns is the F_2 space on the classes n1 | k, plus new
series for zero on the other classes. The families F_3, F_4, F_6, ... do contain new
relations and new series, for instance (checked numerically)

    pi * sqrt(3) * 2^(1/3) = 9 * sum over j >= 0 of 4^(-j) * ( 1/(6j+1) - 1/(6j+4) ),

but only for irrational multiples of pi or for zero, and by the lemma none of them
can shorten a formula for pi.

## Part V. Base 3 (begun 22 November 2026)

The same programme for base 3. One theorem is proved and machine-checked (the criterion for
logarithms); the statements about pi are computed and not yet proved. Each paragraph says
which.

### Setting

The class F3 is the set of series

    S(rho) = sum over k >= 1 of rho(k) 3^(-floor(k/2)) / k,      rho rational and periodic.

In Bailey's notation these are the series P(1, 3^B, n, A) with n = B or n = 2B. Put
t = sqrt(-3) = i sqrt(3). Then t^2 = -3, so rho(k) 3^(-floor(k/2)) = c(k) t^(-k) with
c(k) = rho(k) t^(k mod 2) (-1)^floor(k/2), of period lcm(N, 4), and as in Part III

    S(rho) = sum over r^N = 1 of d_r Log(1 - r/t).

The role of Z[i] and 1 + i (with (1+i)^2 = 2i) is played by the Eisenstein integers Z[w],
w = (-1 + t)/2 a cube root of unity, and t, of norm 3. The units are the six roots +-1,
+-w, +-w^2.

### Theorem K3: which logarithms have a base-3 formula (machine-checked)

**Theorem K3.** Let y be a positive rational number. The following are equivalent.

(a) log y is the value of a series of F3.

(b) log y is a rational combination of log 3 and the numbers log |t^n - c|, n >= 1, c a cube
    root of unity.

(c) Some power y^k, k >= 1, is a product of integer powers of 3, of the numbers 3^m - 1
    (m >= 1), and of the numbers 3^n - 3^((n+1)/2) + 1 and 3^n + 3^((n+1)/2) + 1 (n odd).

The last two are the Aurifeuillian factors: 3^(3n) + 1 = (3^n + 1) L_n M_n for odd n.

*Proof.* The proof of Theorem K, with w in place of i. (b) => (a): the roots of X^n = c have
product of (t - r) equal to t^n - c, the power sums of these roots are n c^(k/n) or 0, and
Re(w^e) and Re(w^e / t) are the rational numbers 1, -1/2, -1/2 and 0, 1/2, -1/2; so
log |t^n - c| - n log |t| is a series of F3 of period 12n. Also t - w = -w^2 is a unit, which
gives log 3. (a) => (b): Baker's theorem gives a relation prod (1 - r/t)^(e_r) = xi y^m with
m non-zero; cleared, it is an integer polynomial identity at zeta = exp(2 pi i/N), N = 3K,
with w = zeta^K and t = w - w^2; it holds at zeta^a for a prime to N, and a = 1 modulo 3 fixes
t; adding logarithms of absolute values over these a and applying Moebius inversion leaves
the numbers log |t^M - c| with c^3 = 1. (b) <=> (c): |t^n - c|^2 is (3^m -+ 1)^2 or
9^m +- 3^m + 1 for n = 2m, and 3^n + 1 or L_n or M_n for n odd; and
9^m + 3^m + 1 = (27^m - 1)/(3^m - 1), 9^m - 3^m + 1 = (27^m + 1)/(3^m + 1).

*Machine-checked* (lean/Pilean/Base3, standard axioms only, no hypothesis with the formal
proof of Baker's theorem): `PiFormula.Base3.isF3Value_log_rat_iff_pow` is (a) <=> (c);
`isF3Value_log_rat_iff` is (a) <=> (b); `logSpan3_le_f3Values` and `isF3Value_log_of_pow`
are the half that needs no Baker; `PiFormula.Base3.Unconditional.*` have no hypothesis.
Also in Lean, with no Baker: log 2, log 3, log 5, log 7, log 11, log 13, log 19, log 37 and
pi sqrt(3) are values of F3 (`isF3Value_log_19`, `isF3Value_pi_sqrt3`, and so on).

### The test for a prime, and the list (computed; python/base3_criterion.py)

For a prime p other than 3, let n = ord_p(3) and let g be the primitive part that contains
p: g = Phi_n(3) if n is not 6 modulo 12; if n = 6m with m odd, g is the one of
gcd(Phi_n(3), L_m), gcd(Phi_n(3), M_m) that p divides (they are coprime and their product is
Phi_n(3)). Write g = p^x R. Then log p is a value of F3 if and only if R = 1, or R is a prime
q dividing n and log q is a value of F3. This follows from (c) by the argument given for
base 2; it is not machine-checked for base 3.

Below 10^6 the test accepts 31 primes:

    2, 3, 5, 7, 11, 13, 19, 31, 37, 41, 43, 61, 73, 271, 547, 757, 1093, 1181, 2269, 4561,
    6481, 19441, 19927, 25411, 176419, 368089, 387631, 398581, 530713, 755551, 797161.

Of these, 17 come from a full Phi_n(3) and 13 from an Aurifeuillian half (19 and 37 are the
two halves of Phi_18(3) = 703; 31 and 271 those of Phi_30(3)). Below 100 the primes that
fail are 17, 23, 29, 47, 53, 59, 67, 71, 79, 83, 89, 97; for example Phi_16(3) = 2 * 17 * 193.

*Numerical check, with no theory* (python/base3_probe.py, lattice reduction on the values of
the series of a given period): at period 32, log 17 + log 193 is a value and neither is
alone; at period 44, log 67 + log 661 and log 23 + log 3851 are values and no single one is;
at period 84, log 43 and log 2269 are values. All as the test predicts.

*In print* (research/2026-11-22-base3/01_ternary_formulas_inventory.md): only log 2, 3, 5,
7, 11, 13 appear as base-3 formulas (Bailey's compendium, formulas 67 to 75; OEIS A165132).
The general families of the compendium, at b = 3^m, contain formulas for 19, 37 and others,
but no source lists them as ternary, and none states a criterion. No list of the unique
primes of base 3 was found in the OEIS
(research/2026-11-22-base3/02_base3_unique_primes_data.md).

### pi in base 3 (computed; the proof is the next step)

Six roots of unity are exceptional: 1, -1, i, -i, w, -w^2. Indeed

    t - 1 = 2w,   t + 1 = -2w^2,   t - w = -w^2,   t + w^2 = w,
    (t - i)(t + i) = -2,           (t + i)/(t - i) = 2 + sqrt(3).

So among the six numbers 1 - r/t for these r there are three independent multiplicative
relations up to roots of unity (they lie in the group generated by 2, t and 2 + sqrt(3)).
Every other orbit of roots of unity should have a private prime, as in Lemma 3: this needs
a primitive prime in Phi_n(3) and in each Aurifeuillian half for n = 6 modulo 12, n >= 18.
That lemma is not proved yet.

Computed (lattice reduction, every period 12, 24, ..., 144, 180):

- there are exactly two independent zero relations, both of period 12:

      (1, 0, -10, -3, 4, 12, -1, 12, 10, 15, -4, 0),   (0, 1, -2, 0, 1, 4, 0, 3, 2, 4, -1, 0);

- the patterns whose series is a rational multiple of pi sqrt(3) form a space of dimension
  3, all of period 12;
- pi itself is not found as a value at any of these periods.

**Statement C3 (not proved).** Every series of F3 whose value is an algebraic multiple of pi
has period 12; these series form a space of dimension 3; and the value is a rational
multiple of pi sqrt(3). In particular pi is not the value of any series of F3.

This would answer, for base 3 and this class, the research problem 10 of Borwein, Borwein
and Galway (2004, p. 924), who proved only that pi is not a rational combination of the
numbers arctan(3^(-m)). Given the lemma on private primes, the proof is the one of Theorem
C: by Baker's theorem the coefficients d_r lie in the span of the relations, which are
supported on the six exceptional roots, all of order dividing 12.

**The cheapest formula (computed).** Among the formulas for pi sqrt(3) of period 12, the
fewest non-zero terms is 6 per period, one term per base-3 digit, and exactly two formulas
attain it:

    pi sqrt(3) = S(6, 0, -6, 0)                      (the Gregory series at 1/sqrt(3)),
    pi sqrt(3) = S(0, 18, 18, 18, 0, 0, 0, -18, -18, -18, 0, 0).

The formulas in print found by the research (Adegoke's 2.14 and 2.15, the compendium's 92 at
b = 3, all forms of the Gregory series; and the compendium's 69, with 7 terms per 6 digits)
do not include the second one. So in base 3 nothing beats the Gregory series, in contrast
with base 2, where there are many zero relations and the optimum 2/3 is below every
classical formula.

Other values (each checked to 50 digits): log 2 = S(0, 4, 0, 0); log 3 = S(0, 6, 0, 2);
sqrt(3) log(2 + sqrt(3)) = S(2, 0); arctan(1/3) = S(0, 2, 0, 0, 0, -2, 0, 0).

### What is and is not established in base 3

- Proved and machine-checked: Theorem K3, and the values named above.
- Proved on paper only: the test for a prime (by the argument for base 2).
- Computed only: the list of 31 primes; the two zero relations and that there are no others;
  that pi is not a value; the cheapest formula.
- Next: the lemma on private primes in Z[w] (the analogue of Lemma 2 and Lemma 3), then
  statement C3; then the test for a prime in Lean.

## Why this matters for digit extraction

In the prime form of the window algorithm, the per-prime state a window must read is
2.88 * mean(1/s) bits per bit of position (Part III). An earlier version of this note
claimed that Euler's 0.96 could not be improved by another formula of this type. That
was wrong: the optimum is 0.84, attained by the formula of Theorem E. For the
classical term-by-term algorithm the optimum is Huvent's 2/3 terms per bit. Parts III
and IV establish both as the end of the road for binary degree-1 BBP-type formulas of
every base and period: a larger gain needs a formula of a different kind, for which
there is at present neither a candidate nor a proof of impossibility.

## What is not established

* **Novelty.** A 200-search literature check (21 November 2026) found no statement
  of Theorems A to F. What is in print, and credited above: the three formulas and
  the method (BBG 2004), the two-term case (Stormer), Lemma 2 in substance (Schinzel
  1962), the factorization behind it (Chamberland 2003), the zero-relation counts
  (Bailey's Table 1, found by PSLQ, unexplained), Baker's theorem on periodic sums
  (Baker-Birch-Wirsing 1973; Adhikari et al. 2001), and the device of adding a zero
  relation to a formula (Bailey's Formula 17 is the BBP formula plus 1/4 of zero
  relation 111). Bellard's formula, by his own account, comes from
  2 arctan(1/2) - arctan(1/7) by reordering terms, not from a zero relation. Huvent
  (2001) minimised terms per bit heuristically inside an 11-parameter family.
  Adjacent recent work: Gasull, Luca and Varona, Indag. Math. 34 (2023), which
  classifies two-term formulas with arguments b/2^a and cites neither BBG nor Bailey.
  The literature databases MathSciNet and zbMATH were not searched.
* **Still to read before submission:** Schinzel 1962, Drauschke-Tasche 1987,
  Steidl-Tasche 1989 and Steidl-Hanler-Tasche 1989 (interlibrary loan requested
  21 November 2026, needed by 19 December), and Broadhurst's unpublished manuscript
  (ask the author). Huvent's paper has been read: both optimal formulas of Theorem E
  are his.
* **Parts III and IV have had one independent review** (review_part3_part4.md,
  21 November 2026). It rebuilt V by a different exact method, recomputed the
  valuation table and the vertex enumeration with its own code, and confirmed
  Theorems C, D and F and the optimum values of Theorem E (its confidence: 97%, 97%,
  93%, and 95% for E's values). It found the false count "22 formulas", the gap in
  Step 2 (both corrected above) and two wording slips. It also flagged a possible gap
  in exact_optimum.py when the rank drops modulo one prime; that case is sound,
  because the minors are then all 0 modulo that prime, so D_c = 0 modulo it holds
  genuinely and all four primes still count. The lattice searches of Part IV would
  miss relations with coefficients above about 2^25.
* **Other kinds of formula.** Nothing here addresses higher-degree
  (polylogarithm-type) terms, non-linear exponents, numerators that grow with k, or
  methods that are not series of this shape at all. For higher degree the standard
  conjectures predict no gain; for non-linear exponents there is neither a candidate
  nor a proof that none exists; and there is no proof at all that the n-th bit of pi
  needs time linear in n.
* **Running time.** Measured only on one laptop, at positions 10^9, 10^10 and 10^11,
  one to three runs each. The new formula has not been run beyond 10^11, and a long
  window at 10^11 has not been timed.
* **Machine checking (lean/README.md).** Theorem A is proved in Lean 4 against Mathlib,
  unconditionally: `PiFormula.theoremA : TheoremA`, with no `sorry` and only the three
  standard axioms (`propext`, `Classical.choice`, `Quot.sound`; checked with
  `#print axioms`). The formal proof covers every step:
  - the bridge from arctangent relations to Gaussian integers;
  - Facts 1 and 2 and the private-prime theorem;
  - the order of 2 modulo p and the Aurifeuillian norms;
  - Bang's theorem, vendored from the Tau Ceti library;
  - the largest-index argument, the irrationality of arctan(1/2)/pi, and the last step;
  - Lemma 2, Schinzel's Aurifeuillian primitive-divisor result in the case needed. Its
    proof has four parts. First, a reduction to a size bound. Second, the Gaussian
    factorization: A_n A'_n = Phi_4n(2), via Phi_2n(X) = Phi_n(-X) for odd n > 1,
    proved from the roots of unity. Third, the size bound A_n, A'_n > n for odd n >= 7,
    by Moebius inversion, then the bound A_n prod M_d >= 2^phi(n) prod 2^d, then
    prod M_d <= 9 prod 2^d and phi(n)^2 >= n for n >= 82, with a kernel computation
    for the odd n from 7 to 81. Fourth, the small cases.

  What remains to trust is that the formal statement `TheoremA` matches Theorem A as
  written here.

  Theorem B is also proved in Lean (`PiFormula.theoremB`, standard axioms only), in its
  form on representatives: relations among pi and the arguments of the atoms Phi_m(t),
  Phi_m(-t) and Phi_m(i 2^(2^j)). The proof includes Lemma 3 (a primitive, private
  Gaussian prime for every non-exceptional atom, from Lemma 2 and Bang) and the
  largest-index argument. Theorem B is also proved in its gamma form
  (`PiFormula.theoremBgamma`). It uses gamma(O) exactly as defined above, over explicit
  orbits: the roots of Phi_m(kappa X^N), which for the first two rows are the primitive
  m-th and 2m-th roots of unity; their partners; and the self-paired orbits of order 8m.
  The proof includes:
  - the identity gamma(O) = arg z_O - |O| pi/4 (mod 2 pi);
  - the pairing gamma(O*) = -gamma(O);
  - the bound |g(r)| <= pi/4;
  - the exact values gamma(O_1) = pi/4, gamma(O_6) = 0, gamma(O_2) = arctan(1/2) - pi/4
    and gamma(O_10) = arctan(1/2).

  The table is also in Lean (`PiFormula.galois_table`), with the orbits defined as in the
  note: classes of roots of unity with the same minimal polynomial over Q(i). Each
  explicit set is such a class, and the orbit of every root of unity is one of them. The
  key step is that Phi_m(kappa X^N) is irreducible over Q(i). It follows from
  [Q(i)(r) : Q] = 2 [Q(i)(r) : Q(i)] and the degree of a primitive root of unity in
  Q(i)(r): i·kappa·r, of order 4m, or r, of order 4mN. **So Theorem B, as stated in
  Part II, is machine-checked.**

  Corollaries B1 and B2 are also in Lean (`PiFormula.series_of_relation`,
  `PiFormula.corollaryB2`):
  - the series of gamma from the Taylor series of log;
  - the term-by-term cancellation of partner and self-paired series (B1);
  - the terms -E(k) Im(t^(-k))/k, with the Ramanujan sums c_6, c_10 computed for every k
    and E(k) depending only on gcd(k, 30), as in the table;
  - Im(t^(-k)) = 0 exactly when 4 | k.
  With speed defined as above (s/2, s the least gcd(k, 60) of a non-zero term), every
  series for a non-zero multiple of pi in the class C has speed at most 3/2, and speed
  3/2 exactly for (0, -2, 1) up to scaling, whose value is that of Euler's formula. That
  this speed counts bits per unit of denominator is the convention above, not a theorem.

  Of Part III, the following is proved in Lean:
  - **The new formula's series** (`PiFormula.new_formula_series`): pi/4 = sum
    rho(k) 2^(-floor(k/2))/k with the 120-periodic rho of pi_formula_120.json.
  - **The 13 multiplicative relations of Step 3**, exactly (`PiFormula.relation_1` ...
    `relation_13`), as polynomial identities modulo Phi_20 or Phi_24.
  - **The lower half of Theorem C** (`PiFormula.V_lower_bound`). The 8 named series are
    rational patterns of period 120 with values pi/4, 0, pi/4, 0, 0, 0, 0, 0, and they are
    linearly independent; the sqrt(3)-twisted series is among them.

  - **Step 2** (`PiFormula.support_subset_R0'`, with `PiFormula.goodPrimes`). Every
    multiplicative relation among the 1 - r/t, at any period, is supported on the 24
    roots of R0. The proof gives every root of unity r outside R0 a prime ideal of the
    algebraic integers containing t - r and an odd prime not dividing the order of r.
    The prime comes from Lemma 3 or from Bang's theorem. The Galois table supplies the
    minimal polynomial of r over Q(i), and lying over for the map X -> r from Z[i][X]
    gives the prime ideal for the given r directly. (On paper one takes a prime dividing
    the atom, which divides t - r' for some r' in the orbit of r, and moves it to r by a
    Galois automorphism.)

  - **Step 3, the rank** (`PiFormula.relations_span`, `PiFormula.rel_independent`). The 13
    relations are linearly independent, and every multiplicative relation among the 24
    numbers is a rational combination of them (4 times it is an integer combination). So
    the 24 numbers generate a group of rank 11. The Lean proof is exact and does not use
    the numerical Gram determinant above. It conjugates a relation by zeta -> zeta^a with
    a = 1 mod 4, takes absolute values, and needs only the signs of a few differences of
    the numbers log |w_r|, plus private primes above 3 and 5 for four roots.
    `PiFormula.relations_classified` states Steps 2 and 3 together.

  So Steps 2 and 3, the algebraic input to Theorem C, are machine-checked.

  - **The setting and Step 1** (`PiFormula.series_eq_logs`, `PiFormula.baker_step1`,
    `PiFormula.series_step1`). Baker's theorem is not in Mathlib and is not proved in Lean.
    It is stated as a proposition (`PiFormula.BakerTheorem`, Theorem 2.1 of Baker's book),
    and the theorems that use it carry it as an explicit hypothesis. Proved without it:
    S(rho) = sum of d_r Log(1 - r/t) over the N-th roots of unity, with d the finite
    Fourier transform described in the Setting. Proved from it: if S(rho) is an algebraic
    multiple of pi, then d vanishes outside R0 and on R0 is a combination of the 13
    relations with algebraic coefficients. The converse needs no Baker
    (`PiFormula.step1_converse`).

  - **Theorem C, the rational part** (`PiFormula.finrank_ratSpace`,
    `PiFormula.span_namedFam`, `PiFormula.theoremC_bounds`, from Baker's theorem). For
    every period N divisible by 120: a rational pattern whose series is an algebraic
    multiple of pi has period 120; the patterns whose series is a rational multiple of pi
    (or zero) form a space V of dimension exactly 8, spanned by the eight named series.
    The count 8 is proved without new series: rational values are invariant under the
    Galois conjugations zeta -> zeta^b with b = 1 mod 4 (`PiFormula.conj_value`), every
    arg w_r is an explicit rational combination of pi, arg w_(-1) and arg w_(zeta_24)
    (`PiFormula.garg_table`), and five conjugations give five independent constraints.
  - **The exact multiples of i pi** of the 13 relations (`PiFormula.lf_1_1` ...
    `lf_1_13`): -1/2, -1/2, -1/2, -1/2, 1/3, -5/6, -11/10, -39/10, -7/10, 17/10, -4/3,
    -1/6, 1/4.
  - **Theorem D for rational multiples of pi, and the value formula**
    (`PiFormula.theoremD`, `PiFormula.exists_slow_term`, `PiFormula.value_formula`, from
    Baker's theorem). Every rational pattern whose series is a rational multiple of pi is a
    combination of the eight named patterns, with value (q_0 + q_2) pi/4; the value formula
    and Theorem D are then identities in the coordinates q.
  - **The sharp form of Theorem D, and its sharpness** (`PiFormula.theoremD_sharp`,
    `PiFormula.fast_eq`, `PiFormula.finrank_fast`, from Baker's theorem;
    `PiFormula.theoremD_best_possible`, unconditional): the series of V with no term at
    gcd(k, 120) < 4 form a line, a zero relation; and any two of the classes gcd = 1, 2, 3
    can be avoided by an explicit formula for a non-zero multiple of pi.
  - **Bailey's table** (`PiFormula.finrank_zeroSpace`, `PiFormula.finrank_zeroSpaceEven`,
    `PiFormula.bailey_F2`, `PiFormula.bailey_F1`, from Baker's theorem). For every n >= 1,
    a rational pattern of period n whose series is 0 has period gcd(n, 120)
    (`PiFormula.zeroSpace_gcd`), and these patterns form a space of dimension 1, 1, 5, 3,
    1, 7 when gcd(n, 120) is 8, 12, 24, 40, 60, 120, and 0 otherwise, with explicit bases.
    With support on even k there is exactly one, when 12 divides gcd(n, 120). The 27
    counts of Bailey's Table 1 are the cases n = 2B (17 rows) and n = B (10 rows).
    They are also proved in Bailey's own notation (`PiFormula.bailey_table`): the
    coefficient vectors A with P(1, 2^B, n, A) = 0, written as his double sum, form a
    space of the stated dimension. The step k = nj + i between his sums and our
    patterns needs no Baker (`PiFormula.hasSum_bailey_F2`, `PiFormula.hasSum_bailey_F1`).
    For every B >= 1: P(1, 2^B, 2B, .) has the count of gcd(2B, 120)
    (`PiFormula.bailey_count_F2`), and P(1, 2^B, B, .) has one zero relation if 6 | B
    and none otherwise (`PiFormula.bailey_count_F1`).

  - **Theorem C in full** (`PiFormula.theoremC`, `PiFormula.finrank_algSpace`, from Baker's
    theorem; `PiFormula.fam13_linearIndependent` and the five values
    `PiFormula.hasSum_extraS3` ... `hasSum_extraT2`, unconditional). The patterns whose
    series is an algebraic multiple of pi form a space of dimension exactly 13: the eight
    named series and the five series listed after Theorem C, with values -pi/sqrt(3),
    -sqrt(2) pi, -sqrt(5) pi, (th1 - 3 th3) pi/5 and (3 th1 + th3) pi/5. Each power sum is
    checked against a table of Gaussian integers modulo Phi_24 or Phi_20.
  - **Theorem D as stated, for algebraic multiples** (`PiFormula.theoremD_alg`,
    `PiFormula.theoremD_alg_sharp`, `PiFormula.exists_slow_term_alg`, from Baker's theorem).

  So Theorems C and D, and Bailey's counts, are machine-checked from one hypothesis,
  Baker's theorem.

  - **Theorem E, the two optima** (`PiFormula.theoremE`, from Baker's theorem;
    `PiFormula.huvent1_formula`, `PiFormula.huvent2_formula`, `PiFormula.primeCost_rhoNew`,
    `PiFormula.cost_table`, unconditional). Every series of F for a non-zero rational
    multiple of pi has at least 40 non-zero entries per period of 120 (2/3 terms per bit)
    and mean(1/s) at least 7/24. Huvent's two formulas, stated in Bailey's notation
    P(1, 2^12, 24, A), have exactly 40; the new formula has exactly 7/24. The enumeration of
    6,724,520 cases is replaced by search trees: 13 cases for 7/24, written out by hand, and
    1,517 nodes for 40, as a certificate checked inside Lean by a verified checker and the
    kernel. No `native_decide`: the same three standard axioms.

  - **Theorem G, log 23** (`PiFormula.no_log23`, `PiFormula.bailey_no_log23_F2`,
    `PiFormula.bailey_no_log23_F1`, from Baker's theorem; `PiFormula.no_rel_23`,
    `PiFormula.goodPrimes_ne_23`, unconditional). No series of F, and no P(1, 2^B, 2B, A)
    or P(1, 2^B, B, A), is a non-zero algebraic multiple of log 23.

  - **Theorem H, the primes below 100** (`PiFormula.log_primes_below_100`, from Baker's
    theorem; `PiFormula.isFValue_log_of_mem`, unconditional;
    `PiFormula.not_isFValue_log_of_mem`, from Baker's theorem). For a prime p < 100, log p
    is a value of F exactly for the fifteen primes 2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37,
    41, 43, 61, 73.

  - **Theorem I, arctan(2/7)** (`PiFormula.no_arctan_two_sevenths`,
    `PiFormula.not_isFValue_arctan_two_sevenths`, `not_isFValue_arctan_five_eighths`,
    `not_isFValue_arctan_four_ninths`, the Bailey forms, from Baker's theorem;
    `PiFormula.no_rel_gaussian`, `PiFormula.isFValue_arctan_two_sevenths_add`,
    `PiFormula.isFValue_arctan_inv_129`, unconditional). arctan(2/7), arctan(5/8) and
    arctan(4/9) are not values of F; arctan(2/7) + arctan(6/11) is.

  - **Theorem J, the cheapest checked computation** (`PiFormula.pairCost_ge`, from Baker's
    theorem; `PiFormula.pairCost_takahashi`, `PiFormula.takahashi1_formula`,
    `PiFormula.takahashi2_formula`, `PiFormula.pairCost_huvent`). Any two different formulas
    of F with the same value cost at least 60 as a checked pair, and Takahashi's two
    formulas cost exactly 60. The search tree (8,083 + 180 nodes, 17,953 derived facts) is
    a certificate checked inside Lean by a verified checker and the kernel.

  - **Theorem K, the criterion** (`PiFormula.isFValue_log_rat_iff_pow`,
    `PiFormula.isFValue_log_rat_iff`, `PiFormula.mem_logSpan_of_isFValue_log`, from Baker's
    theorem; `PiFormula.logSpan_le_fValues`, `PiFormula.isFValue_log_of_pow`,
    `PiFormula.logSpan_eq_baseSpan`, `PiFormula.isFValue_log_two_pow_sub_one`,
    `PiFormula.isFValue_log_L`, `PiFormula.isFValue_log_M`, unconditional). For a positive
    rational y, log y is a value of F if and only if a power of y is a product of integer
    powers of 2, the numbers 2^m - 1 and the two factors of 4^n + 1, n odd. Both halves, for
    every y. Also the pair 433, 38737 (`PiFormula.not_isFValue_log_38737`,
    `PiFormula.not_isFValue_log_433`, `PiFormula.isFValue_log_433_add_log_38737`).

  - **Theorem K, the finite test for a prime** (`PiFormula.isFValue_log_prime_iff_explicit`,
    `PiFormula.isFValue_log_prime_iff`, `PiFormula.not_isFValue_log_of_partner`,
    `PiFormula.isFValue_log_prime_classification`, from Baker's theorem;
    `PiFormula.isFValue_log_of_dvd`, `PiFormula.primPart_facts`, unconditional). For a prime
    ℓ outside 2 (2^60 - 1): log ℓ is a value of F if and only if the primitive part that
    contains ℓ is a power of ℓ, or a power of ℓ times one prime q that divides the order of 2
    modulo ℓ and has log q a value. Not in Lean: the statement (d) on the other binary
    families, and the evaluation of the test on each prime of the list of 51.

  - **Baker's theorem, and the theorems above without a hypothesis.** Since 22 November
    2026 the library contains a formal proof of Baker's theorem by Michail Karatarakis
    (lean/Baker, Apache License 2.0; lean/Baker/README.md gives the source, the checks and
    the three one-line adjustments made). `PiFormula.bakerTheorem` derives the hypothesis
    from it, and `PiFormula.Unconditional.theoremC`, `theoremD_sharp`, `theoremE`,
    `no_log23`, `log_primes_below_100`, `bailey_table` and the others restate the theorems
    with no hypothesis. They depend only on the three standard axioms. That proof is not
    ours and has not been through Mathlib's review; Lean's kernel has checked it.

  Not in Lean yet:
  - of Theorem E: that the optima are attained only by the stated formulas, and the list
    of non-dominated pairs.

  The plan is lean/PART3_PLAN.md.
  Nothing of Part IV is in Lean.
