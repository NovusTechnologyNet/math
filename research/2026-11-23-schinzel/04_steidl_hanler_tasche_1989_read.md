# Steidl, Hanler and Tasche 1989, read in the paper itself (23 November 2026)

G. Steidl, M. Hanler and M. Tasche, "On a number-theoretic result of Zsigmondy in domains of
quadratic integers", Arch. Math. 53 (1989), 30-39. Interlibrary-loan copy obtained by the user
on 23 November 2026; local file `papers/steidl_hanler_tasche1989_zsigmondy_quadratic.pdf` (the
folder `papers/` is not in git). All ten pages of the article were read on the page images;
the statements below are restated in this project's words, not quoted.

## 1. What the paper proves

Setting: D a square-free integer with abs(D) >= 2, O_K the ring of integers of K = Q(sqrt D),
e in O_K with abs(N(e)) >= 2, ord_P(e) the multiplicative order of e modulo a prime ideal P.

**Theorem 1.3 (main result, p. 30).** For n >= 5, n != 6, there is a prime ideal P of O_K with
ord_P(e) = n, except for (n, e) = (12, +-sqrt 2). (The cases of rational integers, Theorem 1.1,
and of Gaussian integers, Theorem 1.2, are quoted from Zsigmondy and from Drauschke-Tasche.)

**Lemma 2.1 (p. 31; a sharp lower bound).** For n > 2 and real x >= 0:
Phi_n(x) >= Phi_n(1) x^(phi(n)/2), with equality only at x = 1. Proof: Phi_n(x) Phi_n(1/x)
- Phi_n(1)^2 is a difference of two products over the primitive roots whose factors compare
termwise. They remark that the exponent phi(n)/2 is best possible and that a bound
x^(2 phi(n)/3), proved elsewhere for integers x, cannot hold for all real x.
Corollary 2.2: Phi_n(x) >= abs(x)^(phi(n)/2) for all real x when n is not a power of 2, and
Phi_n(x) >= 2 abs(x)^(2^(t-1)) for n = 2^(t+1).

**Lemmas 3.1 to 3.3, Theorem 3.4 (real quadratic fields).** N(Phi_n(e)) > abs(N(e))^(phi(n)/2)
(n not a power of 2); N(Phi_n(e)) > p^2 for the greatest prime factor p of n, for n >= 5,
n != 6, except (12, +-sqrt 2), where N(Phi_12(sqrt 2)) = 9.

**Lemma 3.5, Theorem 3.6 (imaginary quadratic fields).** abs(Phi_n(e)) > p except for a list M
of eight pairs (n, e) with n in {5, 7, 10, 14} and N(e) = 2, for which p does not divide
N(Phi_n(e)).

**Theorem 4.2 (quoted from Steidl-Tasche, Math. Nachr., then in print).** The ideal
Phi_n(e) O_K is A times the product of P^s(P) over the prime ideals with ord_P(e) = n, with an
explicit ideal A whose norm lies in {1, p, p^2} (or in {1, 3, 4, 9, 12, 36} when n = 3 * 2^r).
With Theorems 3.4 and 3.6 this gives Theorem 1.3.

## 2. What this means for the project

1. **A lower bound of ours is in print.** Lemma 2.1 is the inequality proved in
   `lean/Pilean/RatBase/SizeR.lean` as `sqrt_pow_totient_mul_eval_one_lt_cyclotomic_eval`
   (sqrt(x)^phi(m) Phi_m(1) < Phi_m(x) for x > 1, m >= 3), used for the size condition in
   rational bases. Cite Steidl-Hanler-Tasche, Lemma 2.1, for it.
2. **The nearest printed relative of the good-prime lemma behind Theorem G.** Take
   e = sqrt b (b >= 2 not a square, so e is an integer of Q(sqrt b) of norm -b). Theorem 1.3
   gives, for every n >= 5, n != 6, a prime ideal of Q(sqrt b) modulo which sqrt b has order
   exactly n, with the single exception b = 2, n = 12. That is a primitive prime for *some*
   primitive n-th root of unity r (a prime ideal above it contains some sqrt b - r).
   Theorem G needs a good prime for *every* r. When sqrt b is not in Q(zeta_n) all
   sqrt b - r with r of order n are conjugate over Q(sqrt b), and their theorem suffices; when
   sqrt b lies in Q(zeta_n) the cyclotomic polynomial splits over Q(sqrt b) into two factors
   (the Aurifeuillian situation) and one primitive prime ideal settles only one of the two
   classes. The project's size condition (`Pilean/BaseB/Size.lean`, `Reduction.lean`) treats
   both classes. So Theorem G's lemma is not in this paper, but the method (lower bounds for
   Phi_n at a quadratic integer against the greatest prime factor of n) is the same family,
   and the paper should be cited next to Schinzel (1962).
3. **Consistency checks.** Their only exception, (12, +-sqrt 2), is base 2 at order 12:
   Phi_12(sqrt 2) = 3. In the project this is the Aurifeuillian factor L_3 = 5 without a
   primitive prime, and order 12 is among the exceptional roots of base 2. Their exclusion of
   n = 6 matches the place where the project also needs a separate argument (the triple
   (5, 1, 6) in base 5 and the m = 6 triples for rational bases).
4. **The base-3 and base-5 Aurifeuillian lemmas** (`primitiveHalves3`, `PrimitiveHalves5`:
   a primitive prime in *each* half) are not consequences of Theorem 1.3, for the reason in
   item 2. Schinzel's proof remains the closest source for them.

## 3. Still unread

Steidl and Tasche, "On a number-theoretic result of Sylvester-Kronecker-Zsigmondy", Math.
Nachr. 140 (1989), 233-247 (the source of Theorem 4.2 above; any number field). Also Redei
1958 and Sachs 1957.
