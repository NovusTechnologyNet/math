# Schinzel 1962, read in the paper itself (23 November 2026)

A. Schinzel, "On primitive prime factors of a^n - b^n", Proc. Cambridge Philos. Soc. 58 (1962),
555-562. Library copy obtained by the user on 23 November 2026; local file
`papers/schinzel1962_primitive_prime_factors.pdf` (the folder `papers/` is not in git). All
eight pages were read on the page images; the statements below are restated in this
project's words and notation, not quoted.

## 1. What the paper proves

Throughout: a, b coprime integers, |a| > |b| > 0; Phi_n(a, b) the homogeneous cyclotomic value;
k(m) the square-free kernel of m; q(m) the greatest prime factor of m. A primitive prime
factor of a^n - b^n divides it and no a^v - b^v with 0 < v < n.

**Theorem 1 (p. 556; Aurifeuillian identities for every square-free n).** Let n > 1 be
square-free and m a divisor of n with n/m odd. There are integer polynomials P, Q (depending
on n, m) with

    Phi_n(x)  = P(x)^2 - (-1|m) m x Q(x)^2          (m odd),
    Phi_2n(x) = P(-x)^2 + (-1|m) m x Q(-x)^2        (m odd),
    Phi_2n(x) = P(x)^2 - m x Q(x)^2                 (m even),

and P(x^2) - sqrt(+-m) x Q(x^2) is an explicit product over half of the primitive roots of
unity (selected by the Jacobi symbol (s|m)). By Phi_n(x) = Phi_n*(x^(n/n*)) (n* the largest
square-free divisor), "n square-free" can be weakened to "m square-free". The case n = m is
credited to Lucas; odd n, m to Cunningham; the second part and the lemma behind it are said
to be new.

**Theorem 2 (pp. 555-556; the main result).** Put eta = 1 if k(ab) = 1 (mod 4) and eta = 2 if
k(ab) = 2 or 3 (mod 4). If n/(eta k(ab)) is an odd integer, then a^n - b^n has at least two
primitive prime factors, except in the following cases:

| n | (a, b) |
|---|---|
| 1 | a = +-(2^alpha + 1)^2, b = +-(2^alpha - 1)^2; or 4a = +-(p^alpha + 1)^2, 4b = +-(p^alpha - 1)^2 |
| 2 | the same with the opposite sign for b |
| 3 | a = +-3, b = -+1; a = +-4, b = +-1; a = +-4, b = -+3 |
| 4 | abs(a) = 2, abs(b) = 1 |
| 6 | a = +-3, b = +-1; a = +-4, b = -+1; a = +-4, b = +-3 |
| 12 | abs(a) = 2, abs(b) = 1; or abs(a) = 3, abs(b) = 2 |
| 20 | abs(a) = 2, abs(b) = 1 |

For a > b > 0 and n >= 3 the exceptions are therefore
(a, b, n) = (4, 1, 3), (2, 1, 4), (3, 1, 6), (4, 3, 6), (2, 1, 12), (3, 2, 12), (2, 1, 20).

*How it is proved (section 3, pp. 559-561).* With nu = eta k(ab) l, l the product of the
primes of n not dividing eta k(ab), and A = a^(n/nu), B = b^(n/nu), Theorem 1 splits
Phi_n(a, b) = phi^(1) phi^(-1) into two integers (the two Aurifeuillian factors). Their common
prime factors divide 2 nu B, so apart from n = 1 they are coprime, and by Zsigmondy's theorem
every prime factor of either is a primitive prime factor of a^n - b^n, except possibly
q(n) to the first power. So it is enough that each factor exceeds 1 (or q(l), when
q(l) = q(n)): inequality (24). This is proved from upper and lower bounds for the two
factors, and finitely many small cases are examined directly; they give the table.
So where (24) holds, **each of the two Aurifeuillian factors has a primitive prime factor**:
that is what the proof shows, although the theorem is stated as "at least two".

**Lemma 2, Lemma 3, Theorem 3 (p. 561; greatest prime factor).** For n > 2 (one case
excluded) q(a^n - b^n) >= n + 1, and >= 2n + 1 if n is not divisible by 4 (two cases
excluded). If k(ab) divides n and n > 2, then q(a^n - b^n) >= 2n + 1, excluding n = 4, 6, 12
with abs(a) = 2, abs(b) = 1. Theorem 3: the same bound for all n > 2 when k(ab) = +-2, with the
same three exclusions; it also holds for k(ab) = +-1 and for ab = +-c^h, h >= 2.

Three problems are posed (three primitive prime factors for some n, for infinitely many n;
q(a^n - b^n) > 2n for all large n outside the cases above).

## 2. What this settles for the project

1. **The two lists that did not agree are two different theorems.** The exceptions
   n = 4, 12, 20 for 2^n - 1 belong to Theorem 2 (two primitive prime factors); the
   exclusions n = 4, 6, 12 belong to Theorem 3 (greatest prime factor at least 2n + 1), which
   is the statement Stewart's summary describes. Both are in the paper.
2. **Lemma 2 of the note (base 2).** For a = 2, b = 1: k = 2, eta = 2, and Theorem 2 says that
   2^(4n) - 1 has two primitive prime factors for every odd n except n = 1, 3, 5. The note's
   Lemma 2 (M_n has a prime that is primitive for 4n for every odd n; L_n for odd n >= 7; not
   for L_1 = 1, L_3 = 5, L_5 = 25) is the "one in each factor" form, which is what Schinzel's
   proof gives. The exceptions agree exactly. The citation "Lemma 2 in substance (Schinzel
   1962)" is right, and can now be made precise: Theorem 2 and inequality (24) of its proof.
3. **The base-3 lemma** (`primitiveHalves3`: for odd E >= 3 each of 3^E -+ 3^((E+1)/2) + 1 has
   a prime p with ord_p(3) = 6E). For a = 3, b = 1: k = 3, eta = 2, n = 6E, and the only
   exception with abs(a) = 3, abs(b) = 1 and n/6 odd is n = 6 (E = 1). Same relation as in 2.
4. **The base-5 statement** (`PrimitiveHalves5`: for every odd h each of L_h, M_h has a prime
   p with ord_p(5) = 5h). For a = 5, b = 1: k = 5, eta = 1, n = 5h, and the table has no
   exception with abs(a) = 5. Consistent, including h = 1 (5^5 - 1 = 4 * 11 * 71).
5. **The list used from memory in the rational-base work is confirmed.**
   `research/2026-11-22-rational-bases/00_summary.md`, section 3.6, quoted the exceptions
   (2,1,4), (2,1,12), (2,1,20), (3,1,6), (4,1,3), (4,3,6), (3,2,12) from memory. They are
   exactly the exceptions of Theorem 2 with a > b > 0, n >= 3.
6. **An observation.** The pairs a > b > 0 that occur in that list are (2,1), (3,1), (4,1),
   (3,2), (4,3): the five bases of Theorem R (`PiFormula.RatBase.hasRelation_iff`), and no
   others. In each of them the exceptional n is where one Aurifeuillian factor is 1 (a unit
   sqrt(a) - r sqrt(b)), which is where the relations of Theorem R come from: (3,1,6) is the
   unit of order 12 in base 3, (4,1,3) the factor 2 - v of norm 3 in base 4, (4,3,6) and
   (3,2,12) the units of order 12 and 24 in bases 4/3 and 3/2, and (2,1,4), (2,1,12),
   (2,1,20) are L_1, L_3, L_5 in base 2. Schinzel's paper has nothing on series or on pi;
   the link is ours.

## 3. What it does not give

- The lemmas of the project are not formal consequences of the *statement* of Theorem 2:
  "at least two primitive prime factors" does not say that they lie in different
  Aurifeuillian factors. The proof does say it wherever inequality (24) holds, and the small
  cases are "examined directly" without details. The project's own proofs (Lean:
  `Pilean/PiFormula`, `Pilean/Base3/Halves.lean`, `Pilean/Base5/Halves.lean`) therefore
  stay; cite Schinzel for the result and the method.
- Nothing on the Gauss-sum bound used in section 3.6 of the rational-base summary; that
  statement is still from memory there (the main line does not depend on it).
- Still unread: Drauschke-Tasche 1987, Steidl-Tasche 1989, Steidl-Hanler-Tasche 1989.
