# Research pass of 22 November 2026 (night): base 3

Two helpers ran while the base-3 criterion was being formalized. They used 7 web searches
(the cap is 200) and many direct reads. Each report marks its statements [READ], [SNIPPET],
[INFERRED], [CHECKED] or [COMPUTED].

| Report | Subject | Searches |
|---|---|---|
| 01_ternary_formulas_inventory.md | Every base-3 degree-1 formula in print, formula by formula | 4 |
| 02_base3_unique_primes_data.md | Unique primes of base 3, OEIS sequences, factor tables | 3 |

## What they found, and what we checked

1. **Logarithms in print.** Bailey's compendium (formulas 67 to 75) has base-3 formulas for
   log 2, 3, 5, 7, 11, 13, for pi sqrt(3) and for sqrt(3) arctan(sqrt(3)/7). OEIS A165132
   lists the same six primes. The general families of the compendium (formulas 90 to 110,
   due to Adegoke), at b = 3^m, contain formulas for log 19 and log 37 and several more, but
   no source lists them as ternary and none states a criterion. Nothing was found for 17,
   23, 29, 47. *Our program* (python/base3_criterion.py) gives 31 primes below 10^6, and
   says that 17, 23, 29, 47 and eight more primes below 100 have no formula. *Checked by
   us numerically*, with no theory: log 17 + log 193 is a value at period 32 and neither is
   alone; the same for 67 and 661, and 23 and 3851.

2. **pi sqrt(3) in print.** Cheapest: one term per base-3 digit, in three forms of the
   Gregory series (Adegoke 2.14 and 2.15, compendium 92 at b = 3). Broadhurst's formula
   (compendium 69) costs 7 terms per 6 digits. *Our computation:* the formulas for
   pi sqrt(3) form a 3-dimensional space of period 12, the minimum is 6 terms per period,
   and it is attained by the Gregory series and by one other formula,
   (0, 18, 18, 18, 0, 0, 0, -18, -18, -18, 0, 0), which is not in the inventory.

3. **pi itself.** No base-3 formula for pi, no statement that none exists, and no statement
   of the question was found in these sources. Bailey's compendium (p. 2) describes the
   theorem of Borwein, Borwein and Galway more broadly than what they prove. *Our
   computation:* pi is not a value at any period up to 180.

4. **Unique primes of base 3.** No OEIS sequence lists them (the base-2 sequences A144755,
   A161508, A161509 have no base-3 counterpart). The helper computed them below 20000:
   2, 5, 7, 11, 13, 41, 61, 73, 547, 757, 1093, 1181, 4561, 6481, and the primes that are
   alone only in an Aurifeuillian half: 19, 37, 31, 271, 43, 2269, 19441, 19927. *This
   agrees with our program's list below 20000.* The two halves always multiplied back to
   Phi_n(3).

5. **Data.** Phi_n(3) prime: A138933. (3^n - 1)/2 prime: A028491. (3^n + 1)/4 prime: A007658.
   Eisenstein-Mersenne: A066408, A066413. Aurifeuillian halves prime: A125743, A125744,
   A239842. Wieferich primes of base 3: 11 and 1006003 (A014127). Cunningham tables for base
   3 (n up to 900) at Purdue.

## What this means

- A list of the primes whose logarithm has a base-3 formula, with a proof of the criterion
  checked by machine, looks new: the literature has six primes and no criterion.
- "pi has no base-3 formula of this class, and the Gregory series is optimal for pi sqrt(3)"
  is a clean statement that the literature does not have. It is computed, not proved; the
  proof needs the lemma on private primes in the Eisenstein integers.

## Limits

"Not found" is weak evidence. Not opened: Adegoke's 2010 and 2011 papers, Plouffe's pages,
Broadhurst's reference for pi sqrt(3), the b-files, Brent's factor tables.
