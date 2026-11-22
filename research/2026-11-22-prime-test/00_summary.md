# Research pass of 22 November 2026 (evening): the prime test, base 3, related formal work

Four helpers ran in parallel while the finite test for a prime was being formalized. They
used 73 web searches in total (the cap is 200) and many direct page and API reads. Each
report marks its statements [READ], [SNIPPET] or [INFERRED]. This summary says which
statements we checked ourselves.

| Report | Subject | Searches |
|---|---|---|
| 01_38737_and_unique_primes.md | Where 38737 comes from; unique primes; data to extend the list | 35 |
| 02_ternary_class.md | Base 3: what is known, what is open, what would change | 6 |
| 03_related_formal_work.md | Baker's theorem upstream; Zsigmondy in Lean; related formal work | 17 |
| 04_cyclotomic_facts.md | Classical facts on primes of Phi_n(2), with references | 15 |

## What changes for us

1. **38737 comes from Chamberland's paper of 2003.** His list (obtained, he writes, by
   calculations with Maple) already contains 38737, with no formula; 433 is not on it, and
   433 x 38737 is not among the products of two primes he lists. The book of Borwein and
   Bailey (2nd edition, 2008, p. 130) and OEIS A104885 (2005, never changed) repeat the
   list. No erratum was found. A possible cause (the helper's guess, and ours): his
   construction with Phi_144 gives |Phi_144(1+i)| = 2^24 - 2^12 + 1 = 433 x 38737.
   *Checked by us:* the arithmetic 4096^2 - 4096 + 1 = 16773121 = 433 x 38737. *Not checked
   by us:* the reading of the paper and of the book.
   Consequence: a remark about 38737 is a correction to a published list of 2003 that has
   stood for 23 years, and we have a machine-checked proof for it. It should be worded as
   "appears to be a slip", sent to the author first as a courtesy, and only then to OEIS.

2. **Our list is "unique primes" plus a new half.** The 51 primes below 10^7 are: 2; the 31
   primes that are unique in base 2 in the sense of Caldwell and Dubner (OEIS A144755); and
   19 primes that are alone only in one of the two halves of a Phi_4d(2). *Checked by us:*
   28 of the 51 have order not 4 modulo 8, and 5, 13, 41 (orders 4, 12, 20) are unique as
   well, which gives 31; the other 19 are 29, 37, 61, 109, 113, 397, 1321, 1429, 1613, 2113,
   14449, 26317, 246241, 268501, 279073, 312709, 525313, 4327489, 7416361. The helper found
   no earlier link between unique primes and BBP-type formulas, and no name for "unique in a
   half". This is a clean way to state Theorem K for a reader who knows unique primes: *the
   primes with a binary BBP-type formula for log p are the unique primes of base 2 and of
   base 1 + i, up to the intrinsic prime.*

3. **Data exist to push the list far beyond 10^7 without factoring ourselves:** the
   factorizations of Phi_n(2) for n up to 1280 split into halves (attached to OEIS A250197),
   A161508 and A161509 (179 terms), A072226 (289 values of n with Phi_n(2) prime, n up to
   130002), A057429 (Gaussian-Mersenne), A124112 and A125742, A153443. The helper checked
   Chamberland's 38 primes above 10^7 against our test: 34 pass, 4 were not checked (order
   above 600). *Not checked by us.*

4. **Base 3 looks open and has the same shape.** No classification of base-3 series of
   degree 1 was found, no criterion for log p, and no proof that pi is not the value of a
   base-3 series with rational coefficients (only "not found"). Borwein, Borwein and Galway's
   Theorem 7 excludes only rational combinations of arctan(b^(-m)); the wording in Bailey's
   compendium is broader than what is proved. Their research problem 10 (p. 924) is the
   question our method answers for base 2. With t = 1 - omega (omega a cube root of unity),
   t^2 = -3 omega, as (1+i)^2 = 2i; the ring is Z[omega], with six units instead of four.
   OEIS A165132 (primes with a known ternary formula: 2, 3, 5, 7, 11, 13) is not closed:
   41, 61, 73 follow from 3^4 + 1, 3^5 + 1, 3^6 + 1. A heuristic span test by the helper
   (not a theorem) gives 2, 3, 5, 7, 11, 13, 19, 31, 37, 41, 43, 61, 73 below 100.
   *Checked by us:* t^2 = -3 omega and the three factorizations. *Not checked:* the
   readings and the heuristic list.
   Zudilin's "base 5" series is not periodic, so it is outside the class.

5. **Baker's theorem is not in Mathlib and has no pull request.** The branch we took the
   proof from still ends at the commit we use (24 September 2026). There is no paper,
   blueprint or forum thread about it. Gelfond-Schneider by the same author is an open pull
   request (#42911, blocked); Lindemann-Weierstrass is an open pull request by another
   author (#28013). The Tau Ceti project is building its own Baker development, not
   finished. Zsigmondy's theorem is not in Mathlib (pull request #28895 closed unmerged);
   Tau Ceti merged Bang's theorem on 15 November. So our hypothesis-free statements rest on
   a proof that nobody upstream has reviewed; this must stay in the paper's limits.

6. **Related formal work to cite:** Bertot, Rideau and Thery, "Distant decimals of pi"
   (Coq, 2017), is the formalization of a BBP computation. "Formal proofs of degree 5 binary
   BBP-type formulas" (2013) is by Adegoke and is not machine-checked. Also: Bernard (Coq),
   Eberl (Isabelle, Hermite-Lindemann), Mahboubi and Sibut-Pinote (Apery, Coq), Keller
   (Lean, ITP 2026).

7. **References for the classical facts** (report 04): prime divisors of Phi_n(a) that
   divide n (the largest prime factor of n, exactly once for n > 2): Glasby, Lubeck,
   Niemeyer, Praeger, J. Aust. Math. Soc. 102 (2017), Lemma 7(b) and Remark 8 (their Lemma
   5(c) is misstated: it forgets this prime). The Gaussian split of Phi_4n: Chamberland
   2003, Example 3.2. Existence for a = 2: Allombert and Belabas, J. Theor. Nombres
   Bordeaux 20 (2008), Prop. 1.1. No source that the helper could open states that the two
   halves are coprime at primitive primes; in our library it is `not_dvd_norm_P_and_Q`.
   The Wieferich prime 1093 has order 364 = 4 x 91 and its square divides its half
   (*checked by us*).

## Next leads, in the order we would take them

1. Write the paper around Theorems C, E, J and K, with the 38737 remark and the unique-prime
   reading of the list.
2. Base 3: the same programme in Z[omega]. New, and the literature states the question.
3. Extend the list of primes with the published factorization tables, and compare with
   Chamberland's long list.
4. A courtesy note to Chamberland about 38737 before anything public (the user's decision
   and words).

## Limits

The helpers could not open: the first edition (2004) of Borwein and Bailey's book, the
underlining in Chamberland's list (which marks Bailey's primes), Roitman 1997, Luneburg
1981, Schinzel 1962, Stevenhagen 1987. "Not found" in a search is weak evidence.
