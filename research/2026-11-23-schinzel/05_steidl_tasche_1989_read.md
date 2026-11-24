# Steidl and Tasche 1989, read in the paper itself (24 November 2026)

G. Steidl and M. Tasche, "On a Number-Theoretic Result of Sylvester-Kronecker-Zsigmondy",
Math. Nachr. 140 (1989), 233-247. Interlibrary-loan copy obtained by the user on 24 November
2026; local file `papers/steidl_tasche1989_sylvester_kronecker_zsigmondy.pdf` (the folder
`papers/` is not in git). Read on the page images: the abstract and introduction, Lemma 3.3,
Theorem 3.4, section 4 (quadratic fields: Lemmas 4.1 to 4.3, Theorem 4.4, Corollary 4.5) and
section 5 up to Corollary 5.4. Sections 2 and 6 (preliminaries; number-theoretic transforms)
and most proofs were only skimmed in the text layer, which is a poor scan. The statements
below are restated in this project's words, not quoted.

## 1. What the paper proves

Setting: K a number field, O_K its ring of integers, e in O_K with Phi_n(e) != 0, ord_P(e) the
multiplicative order of e modulo a prime ideal P.

**The classical statement it generalizes (introduction).** For a rational integer e,
abs(e) >= 2, and n > 2: Phi_n(e) = q * product of z^s(z) over the primes z > 2 with
ord_z(e) = n, where q is the greatest prime factor p of n if ord_p(e) = n/p^t, and 1 otherwise.

**Lemma 3.3 (p. 237).** For n = p^t m (p prime, p not dividing m) and a prime ideal P above p
with ramification index lambda: P divides Phi_n(e) iff ord_P(e) = m; then N(P) = 1 (mod m);
if N(P) is p or p^2 and n is not 3 * 2^r, then p is the greatest prime factor of n; and the
exact power of P dividing Phi_n(e) is given in terms of lambda and of a number a attached to
e (part iv, which the authors mark as new).

**Exceptional exponents (p. 239).** n is exceptional for O_K if some prime p with n = p^t m and
some prime ideal P above p of ramification index lambda satisfy (p - 1) p^(t-1) | lambda and
N(P) = 1 (mod m). For a quadratic field these are a few small n among 2, 3, 4, 6, listed in
Lemma 4.2 according to the behaviour of 2 and 3.

**Theorem 3.4 (main result, p. 239).** If n > 1 is not exceptional, then
Phi_n(e) O_K = A * product of P^s(P) over the prime ideals P with ord_P(e) = n, where P^s(P)
is the exact power of P in (e^n - 1), and A is an explicit product of the prime ideals P above
prime divisors p of n with ord_P(e) = n/p^t, each to an explicit small power.

**Theorem 4.4 (quadratic fields, p. 241).** For a non-exceptional n with greatest prime factor
p, the ideal A is 2^q times one of p O_K, a prime ideal above p, or O_K, according to the
Kronecker symbol of p and the orders of e modulo the primes above p; q is 1 only in a special
case with n = 3 * 2^r.
**Corollary 4.5** makes this explicit for Z[sqrt 2], **Corollary 5.4** for the Eisenstein
integers Z[theta], theta^2 + theta + 1 = 0. Section 5 does the same for cyclotomic fields
(Lemmas 5.1 to 5.3, with a table of exceptional exponents).

The paper is about the *shape* of the factorization. It proves no existence statement for
primitive prime ideals; that is in Steidl-Hanler-Tasche (1989), which quotes this paper's
Theorem 3.4 for quadratic fields (see `04_steidl_hanler_tasche_1989_read.md`).

## 2. What this means for the project

1. **The "lemma behind Zsigmondy" in number fields is in print.** The project uses, in every
   base, the fact that the non-primitive part of a cyclotomic value is at most one prime
   (the greatest prime factor of the index), to a small power: for integers through the Tau
   Ceti library, and for sqrt(b) - r through its own symmetrization argument
   (`Pilean/BaseB/Symmetrize.lean`, `ReductionRoots.lean`, `nonprimitive_factsR`). Theorem 3.4
   and Theorem 4.4 are the published general form of that fact for a quadratic field. Cite
   them where the note describes the reduction "a divisor of the cyclotomic value that is
   neither 1 nor that prime has a primitive prime factor".
2. **Base 2 and base 3 in particular.** Corollary 4.5 is the ring Z[sqrt 2] of the binary
   class F, and Corollary 5.4 the ring Z[theta] containing sqrt(-3), which is where the base-3
   Aurifeuillian halves live. They describe the non-primitive part there completely.
3. **No change to what is claimed.** Like the other two papers of this group, this one works
   with one prime ideal of the quadratic field at a time. The project's lemmas that need a
   primitive prime in *each* of the two Aurifeuillian classes (Theorem G, the base-3 and
   base-5 halves) are not stated in it. I did not find a way to deduce them from Theorems 3.4
   and 4.4 together with the existence theorem of Steidl-Hanler-Tasche, and did not try
   hard: the project has its own proofs, checked in Lean.

## 3. The loan request is complete

All four papers requested on 21 November 2026 have arrived and been read: Schinzel 1962
(`02_paper_read.md`), Drauschke-Tasche 1987 (`03_...`), Steidl-Hanler-Tasche 1989 (`04_...`)
and this one. Still unread among the sources they point to: Redei 1958 and Sachs 1957.
