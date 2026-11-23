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

## What this changes

- The absence of pi in base 5 for a class wider than "Machin-type" is, as far as this pass
  shows, not in print. Our computations say more: no zero relations and no relation at all
  among the logarithms. "Not found" is weak evidence; a proof would be the real content.
- The same computations for bases 6, 7, 10, 11, 13, 14, 15, 17 show no relation either. The
  natural general statement extends the theorem of Borwein, Borwein and Galway from
  Machin-type formulas to the whole class. It must be presented as an extension of theirs.

Sources: the URLs are in the two reports.
