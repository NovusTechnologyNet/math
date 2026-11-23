# Drauschke and Tasche 1987, read in the paper itself (23 November 2026)

G. Drauschke and M. Tasche, "Prime factorizations for values of cyclotomic polynomials in
Z[i]", Arch. Math. 49 (1987), 292-300. Interlibrary-loan copy obtained by the user on
23 November 2026; local file `papers/drauschke_tasche1987_cyclotomic_gaussian.pdf` (the folder
`papers/` is not in git). All nine pages of the article were read on the page images; the
statements below are restated in this project's words, not quoted.

## 1. What the paper proves

Setting: e a Gaussian integer with N(e) >= 2; ord_z(e) the multiplicative order of e modulo a
Gaussian prime z; Phi_n the n-th cyclotomic polynomial.

**The classical theorem they extend (section 1; Sylvester, Kronecker, Zsigmondy, Kanold,
Richter).** For a rational integer e, abs(e) >= 2, and n > 2: Phi_n(e) = q * product of z^s(z)
over the primes z > 2 with ord_z(e) = n, where q is the greatest prime factor p of n if
ord_p(e) = n/p^t (p^t the exact power of p in n) and q = 1 otherwise; and there is at least one
such prime z unless (n, e) = (3, -2) or (6, 2).

**Theorem 3.1 (p. 293).** For n > 4 and e in Z[i], N(e) >= 2: Phi_n(e) = i^h * q * product of
z^s(z) over the Gaussian primes z with N(z) > 2 and ord_z(e) = n (z^s(z) the exact power in
e^n - 1), where q is 2, or the greatest rational prime factor p of n, or a Gaussian prime c of
norm p, or 1, according to an explicit list of cases. Except for
(n, e) = (5, -1 +- i), (6, 1 +- i), (6, 2), (10, 1 +- i), at least one such z exists.

**Theorem 4.1 (p. 296; estimates).** For complex x with abs(x) > 1 and n >= 2,

    ((X - 1)/X)^(2^(s-1)) abs(x)^phi(n)  <=  abs(Phi_n(x))  <  (X/(X - 1))^(2^(s-1)) abs(x)^phi(n),

with X = abs(x)^(n/v), v the product of the different prime factors of n, and s the number of
odd prime factors of n (s = 1 when n is a power of 2). They improve estimates of Klobe,
Richter and Sachs.

**Theorem 4.2 (p. 297).** The existence statement of Theorem 3.1 (a Gaussian prime z, N(z) > 2,
with ord_z(e) = n, for n > 4 outside the four exceptional pairs), proved from Theorem 4.1 by
showing abs(Phi_n(e)) > p in a case analysis. It is headed "see [10], [12]": the authors
attribute it to Redei (Acta Sci. Math. 19, 1958) and Sachs (Wiss. Z. Halle, 1957) and say they
improve those results.

## 2. What this settles for the project

**Lemma 2 of the note is in print, in Gaussian form.** Lemma 2 says: for odd n, M_n has a prime
factor p with ord_p(2) = 4n, and so does L_n when n >= 7 (not for L_1 = 1, L_3 = 5, L_5 = 25),
where L_n, M_n are the norms of (1+i)^n -+ 1 in some order.

Take e = 1 + i in Theorem 4.2, at the index n and at the index 2n (n odd, n >= 5). It gives
Gaussian primes z, z' of norm > 2 with ord_z(1+i) = n and ord_z'(1+i) = 2n, that is, z
divides (1+i)^n - 1 and z' divides (1+i)^n + 1, primitively. The only exceptions with
e = 1 +- i are the indices 6 and 10, which are (1+i)^3 + 1 (norm 5 = L_3) and (1+i)^5 + 1
(norm 25 = L_5); the index 2 (n = 1, where (1+i) - 1 = i is a unit, L_1 = 1) is below the range
n > 4 of the theorem. These are exactly the exceptions of Lemma 2.

From a primitive Gaussian prime to the order of 2 (two lines, ours): let p be the rational
prime below z and d = ord_p(2). Since (1+i)^8 = 16, n divides 8d, so n divides d; and
d divides 4n. From (1+i)^n = +-1 modulo z we get (2i)^n = 1, so 2^n = +-i and 4^n = -1 modulo
z: d does not divide 2n. Hence d = 4n.

So for n >= 5 Lemma 2 is the case e = 1 + i of Theorem 4.2 of Drauschke and Tasche, which they
credit to Redei and Sachs; the cases n = 1, 3 are direct. This is a closer match than Schinzel
(1962), whose Theorem 2 gives "two primitive prime factors of 2^(4n) - 1" and only through its
proof "one in each Aurifeuillian factor" (see `02_paper_read.md`). The correct credit for
Lemma 2 is therefore: Redei 1958 and Sachs 1957 (not read), as stated and improved by
Drauschke and Tasche 1987 (read), and Schinzel 1962 (read) for the Aurifeuillian form.

**The size bound.** Theorem 4.1 is a cleaner bound than the one in the note's proof of Lemma 2
(A_n, A'_n >= 2^phi(n) (c1/c2)^2). The Lean proof (`Pilean/PiFormula`, Moebius inversion and a
telescoping product) is unaffected; a shorter proof along Theorem 4.1 is possible but not
needed.

**Not covered by this paper:** bases other than those with e in Z[i]. The base-3 and base-5
lemmas of the project concern sqrt(-3) and sqrt(5); the papers that may contain them are
Steidl and Tasche (1989, any number field) and Steidl, Hanler and Tasche (1989, quadratic
integers), both still unread, and Schinzel (1962).

## 3. Still unread from the same request

Steidl-Tasche, Math. Nachr. 140 (1989), 233-247; Steidl-Hanler-Tasche, Arch. Math. 53 (1989),
30-39. Also not read: Redei 1958 and Sachs 1957, the sources Drauschke and Tasche credit.
