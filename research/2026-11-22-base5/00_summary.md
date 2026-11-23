# Base 5: what is in print (22 November 2026)

Two research helpers, about 50 searches and page reads. Reports:
`01_base5_formulas_inventory.md` and `02_base5_aurifeuillian_primes.md`. Statements are the
helpers' unless marked *checked by us*. Our own computations are in Part VI of
`notes/pi_formula_theorem.md` and in `python/base5_explore.py`.

## Findings

1. **Formulas in print.** Bailey's compendium, section 10: formula 85, a base-25 series for
   log(3/2); 86, sqrt(5) log(phi) in base 5; 87 and 88 in base 5^5. Adegoke: sqrt(5)
   arctan(1/sqrt(5)) in base 25, and some arctangent combinations in base 5^6. The general
   families of section 11 of the compendium have base-5 instances that nobody lists.
   *Checked by us:* sum of 25^(-k)/(2k+1) is (5/2) log(3/2), and our probe finds log(3/2)
   as a value; it finds no single log p as a value, which agrees with item 4.

2. **pi in base 5.** No formula in print, and no proof that none exists for a class as wide
   as ours. Borwein, Borwein and Galway (2004), Theorem 7: for a base b > 2 that is not a
   proper power, pi has no "Machin-type" formula, that is, no rational combination of the
   series of arctan(b^(-m)). That class is narrower than ours (ours also has the series with
   sqrt(b), such as sqrt(5) arctan(1/sqrt(5))). Zudilin's note on base 5 (arXiv 2409.10097)
   uses a series over Z[i] with coefficients that are not periodic; it is outside our class.

3. **Zero relations in base 5.** None in print, and no statement about them.

4. **Logarithms of primes.** No formula for a single log p in base 5 was found in print;
   only log(3/2).

5. **Aurifeuillian factorization for base 5.** For odd h,
   5^(4h) + 5^(3h) + 5^(2h) + 5^h + 1 = L M with
   L, M = 5^(2h) + 3*5^h + 1 -+ 5^((h+1)/2) (5^h + 1); for h = 1 this is 781 = 11 * 71.
   Confirmed in Wagstaff's slides and elsewhere. *Checked by us* by multiplying out
   (x^4 + 3x^2 + 1)^2 - 5x^2 (x^2 + 1)^2 = x^8 + x^6 + x^4 + x^2 + 1.

6. **A primitive prime in each of L and M.** Not found in print for base 5 (as for base 3).
   The helper's reading of a secondary summary is that Schinzel's 1962 theorem is stated
   for ab a square or twice a square, which would not cover a = 5, b = 1; this is not
   verified, since the paper itself was not read. *Our computation:* for every order n up to
   150, each class of sqrt(5) - r has a prime factor not dividing 2n.

7. **Zsigmondy for base 5.** 5^n - 1 has a primitive prime factor for every n >= 2; no
   exception. (In Lean this is in the Tau Ceti library for every base.)

8. **Data.** No OEIS list of the unique primes of base 5 was found. Related: A143665 (least
   prime of given order of 5), A138935 (Phi_k(5) prime). Cunningham tables:
   https://homes.cerias.purdue.edu/~ssw/cun/index.html

## Second pass (three more helpers; reports 03, 04, 05)

9. **Schinzel's theorem, third attempt** (`03_schinzel_statement.md`). The 1962 paper could
   not be read (paywalled). Stewart's 2013 paper (arXiv 1008.1274) states it as: for coprime
   a, b with ab a square or twice a square, a^n - b^n has at least two primitive divisors,
   with the exceptions (2,1,4), (2,1,6), (2,1,12). In that form it does not cover (3,1) or
   (5,1). Wagstaff (Integers 10, 2010) says 3^(3(2k-1)) + 1 has at least two primitive prime
   factors for k > 1. No source read says that each Aurifeuillian factor has one. So our
   Lemma H (base 3, proved in Lean) and the base-5 analogue are not covered by anything we
   could read; we still do not claim they are new.

10. **Sums that vanish** (`04_vanishing_periodic_sums.md`). Adhikari, Saradha, Shorey and
    Tijdeman (2001), as restated in Tijdeman's survey: for algebraic alpha and rational
    functions P/Q with simple rational poles, the sum of alpha^n P(n)/Q(n) is rational or
    transcendental, and 0 or transcendental when the poles lie in [-1, 0). So "a value of our
    class is 0 or transcendental" is known. They give no classification of the vanishing
    case for alpha other than 1; Baker, Birch and Wirsing (1973) and Okada (1982) classify it
    for alpha = 1 only. The compendium says zero relations are not understood. No
    classification of zero sums and no independence result for x = 1/b or 1/sqrt(b) was
    found. This is the right prior art to cite for transcendence.

11. **pi in other bases, and base-3 zero relations** (`05_pi_other_bases_claims.md`).
    - No rational-coefficient degree-1 formula for pi in an integer base that is not a power
      of 2 was found in any source. Kristensen and Mathiasen (arXiv 2208.07696) have pi only
      in irrational Pisot bases. Bailey's compendium words the theorem of Borwein, Borwein
      and Galway more broadly than it is.
    - **Base-3 zero relations are in print.** The compendium's relations 130 and 131 (base
      729, found experimentally) and Adegoke's ternary zero relation (NYJM 2010; quoted by
      Kristensen and Mathiasen). *Checked by us* (`python/base3_classification_check.py`):
      relation 130 is 243 Z1, Adegoke's is 243 Z2, relation 131 is 243 (Z2 - Z1), and
      Broadhurst's formula 69 is G - 9 Z1 + 3 Z2, in the notation of Part V of the note.
    - The second formula with 6 terms, (0, 18, 18, 18, 0, 0, 0, -18, -18, -18, 0, 0), is
      formula 69 minus 1/27 of relation 131: not printed as such, but immediate from printed
      identities.

## What this changes

- **Base 3:** the two zero relations and the formulas were known. What Theorem C3 adds is
  completeness (dimension exactly 2 and exactly 3, period 12), a proof of a relation that
  the compendium records as experimental, and the reason for the relations. The note now
  says so. The same caution applies to base 2, where the zero relations are Lafont's and
  others'.
- The absence of pi in base 5 for a class wider than "Machin-type" is, as far as this pass
  shows, not in print. Our computations say more: no zero relations and no relation at all
  among the logarithms. "Not found" is weak evidence; a proof would be the real content.
- The same computations for bases 6, 7, 10, 11, 13, 14, 15, 17 show no relation either. The
  natural general statement extends the theorem of Borwein, Borwein and Galway from
  Machin-type formulas to the whole class. It must be presented as an extension of theirs.

Sources: the URLs are in the two reports.
