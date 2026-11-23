# Bailey's Compendium (8 April 2023): summary of the ledger

Paper: D. H. Bailey, "A Compendium of BBP-Type Formulas for Mathematical Constants", 38 pages
(local copy `papers/bailey_compendium_2023-04-08.pdf`, not in git). Files of this folder:

- `ledger.json`: one entry per item of the paper (the source of truth; all coefficient vectors).
- `LEDGER.md`: the same as tables, generated.
- `python/compendium_check.py`: the checks. `python compendium_check.py --write` recomputes
  every field `checks` and `status` and rewrites `LEDGER.md` (5 seconds); `--lll` adds the lattice
  counts for Table 1 (needs python-flint, about 10 minutes).

How the paper was read: every page was rendered and looked at. The coefficient vectors were taken
from the text layer of the PDF, with the exponents recovered from the positions of the
superscript glyphs; left sides, prefactors and short vectors were read on the page images. No
entry is marked "uncertain reading": every formula was then confirmed numerically, which a wrong
coefficient would not survive (changing one entry of a 120-term vector by 1 is detected).

## 1. Counts

542 entries: 139 formulas (21 of them zero relations), 41 rows of Table 1, 284 list entries
(46 primes; 160 + 15 + 63 rationals), 78 prose assertions. The 139 formulas are the paper's
numbered ones (133 numbers, of which 5, 9, 11, 12, 14, 15, 16 are a definition or lists; (109)
counts twice, for its two signs), the unnumbered formula between (79) and (80) (tag 80a), and
11 formulas given without number in the text.

| degree s | base 2 | base 3 | base 5 | base 10 | general base b | other | total |
|---|---|---|---|---|---|---|---|
| 1 | 36 | 13 | 4 | 3 | 23 | 1 (base (2/phi)^10) | 80 |
| 2 | 14 | 3 | | | | 1 (definition of G) | 18 |
| 3 | 18 | 3 | | | | | 21 |
| 4 | 9 | 2 | | | | | 11 |
| 5 | 4 | 1 | | | | | 5 |
| none | | | | | | 4 (three arctangent identities, Aurifeuille's factorization) | 4 |

Zero relations (counted above): 14 of degree 1 (111-122, 130-131), 3, 3, 1 of degrees 2, 3, 4.

**Numerics.** 138 of the 139 formulas have a numerical content; all 138 agree to at least 90
digits (working precision 100; required 60). The 139th is an identity between integers, checked
exactly. The 23 formulas with a parameter b were evaluated at b = 2, 3, 5, 10, 7/2, 3/2 (formula
91 at b = 2, 3, 4, 5, 10). **No formula of the paper disagrees numerically.**

**Degree 1 (80 formulas) against the project.**

| status | count | entries |
|---|---|---|
| the same statement is a Lean theorem | 9 (6 theorems) | 1, 6 (`bbp_formula`); 4, 7 (`hasSum_log_two`); 70, p25.c (`hasSum_log_three`); 69 (`broadhurst_formula`); 130, 131 (`relation130`, `relation131`) |
| follows from the classification, exact coordinates in the ledger | 20 more (25 with 1, 6, 69, 130, 131) | pi: 2, 3, 17, 18, 19; sqrt(2) pi, sqrt(3) pi, sqrt(5) pi: 20, 21, 22 (thirteen patterns); zero relations 111-122 |
| existence is a Lean theorem, the printed series is not | 8 | 8 (log 3, base 2); 67, 71-75 (log 2, 3, 5, 7, 11, 13, base 3); 85 (log(3/2), base 5) |
| in a class of the project, value outside the classification theorems | 13 | base 2: 10, 13, 23-28; base 3: 68, p25.b; base 5: 86, 87, 88 |
| restatements and steps of derivations | 3 | p02.g (formula 1 as one fraction), p05.c (the steps to formula 8), p05.e (Harley's identity) |
| base 10, general base b, and the two curiosities | 27 | 84, 89; 90-110 (22 entries) and p04.b; 132, 133 |

Also a Lean theorem: Aurifeuille's factorization (p05.g, `PiFormula.aurifeuille`). In all, 10
entries are already Lean theorems, as 7 theorems.

Every degree-1 formula with rational base and coefficients is in a class with step 1
(weights b^(-k), n = B) or step 2 (weights b^(-floor(k/2)), n = 2B). Among the instances
b = 2 and b = 3 of the general-base formulas the exceptions are 95, 96, 106, 107 at b = 2
(base 2^12, n = 8) and 98, 99, 109 at b = 3 (base 3^18, n = 12): they have step 2 in base 8
and in base 27, so they are binary and ternary formulas outside the classes F and F3; Theorem
G applies to them (bases 8 and 27), the classifications of bases 2 and 3 do not. Formulas 25-28
(arctan of odd powers of phi) reduce to pi and arctangents of rationals:
arctan phi = pi/4 + arctan(1/2)/2, arctan phi^3 = pi/2 - arctan(1/2)/2,
arctan phi^5 = pi/2 - arctan(2/11)/2, arctan phi^7 = pi/2 - arctan(2/29)/2.

**Degree >= 2 (55 formulas).** All confirmed numerically. No Lean proof attempted; each entry
names the ingredients a proof needs (polylogarithm ladders of order s at 1/2, (1+-i)/2 and
2^(-1/2) times roots of unity for base 2; at 1/3, -1/3 and e^(i pi m/6)/sqrt(3) for base 3).
The eight relations the text states between formulas (38 = 39 + ..., 34, 35, 42, 43, 44, 126 =
40 - 48, 17 = 1 + (1/4) 111) are identities between coefficient vectors and were checked
exactly; seven hold, one does not as printed (erratum 1 below).

**Table 1 (41 rows).** The 28 rows of degree 1 (27 of base 2, one of base 3) equal the counts
of Theorems C and C3, which are Lean theorems (`bailey_count_F2`, `bailey_count_F1`,
`bailey_table`, `bailey3_count_F2`). For the 13 rows of degree 2, 3, 4 there is no theorem;
the printed relations, rewritten to the row's base and length, have rank at most the printed
count in every row (equal in 12 rows; 3 against 4 for s = 2, b = 2^60, n = 120, where the paper
says that some relations are not listed). A numerical count by lattice reduction (`--lll`,
more than 8000 bits for n = 120) gives the printed number in all 41 rows, including the fourth
relation for s = 2, b = 2^60, n = 120; for the 13 rows of degree >= 2 this is evidence, not proof.

**List (9), 46 primes.** Every one passes the criterion of Theorem K. The list is not complete
below its largest entry 4432676798593: 74 primes up to there pass the criterion, so 28 are
missing: 331, 1429, 14449, 26317, 65537, 246241, 268501, 279073, 312709, 525313, 599479,
4327489, 7416361, 29247661, 47392381, 107367629, 536903681, 715827883, 1326700741, 2147483647,
40388473189, 77158673929, 118750098349, 275415303169, 415878438361, 1133836730401,
1759217765581, 3630105520141. (24 of them are in Chamberland's table of 2003, see
`research/2026-11-22-wide/W2_Q17_chamberland_claims.md`; 715827883 = (2^31+1)/3, 2147483647 =
2^31 - 1, 275415303169 and 1759217765581 are in neither.) The enumeration assumes that 1093 and
3511 are the only primes p below 4.5e12 with p^2 dividing 2^(p-1) - 1 (published searches).

**Lists (14), (15), (16): 160, 15, 63 rationals.** For each, an exact certificate in Z[i] that
arctan q is a rational combination of pi and arguments of the atoms Phi_m(1+i), Phi_m(-1-i),
Phi_m(i 2^(2^(e+1))); so each is a value of class F (the positive half, as in `Arctan.lean`).
The set (15) is linearly independent over Q, exactly (unique factorization in Z[i]); the paper
says "appear to be". It spans lists (14) and (16), and it contains pi in its span:
arctan(1/2) + arctan(1/3) = pi/4. Of the 773 reduced fractions y/x with y < x <= 50, 226 have
a certificate; the lists (with 1/6, 5/6) contain 222 of them. Missing: 23/30, 5/36, 31/41,
37/41. The values with denominator <= 50 span 16 dimensions modulo Q pi, the set (15) only 14:
arctan(23/30) and arctan(5/36) are outside its span. None of 2/7, 5/8, 4/9, 6/11 is listed,
in agreement with Theorem I. (That the 547 fractions without certificate are not values follows
from Baker's theorem by the argument of Theorem I; in Lean only for 2/7, 5/8, 4/9.)

**Prose assertions (78).** 33 confirmed (15 of them by an exact computation), 4 settled or made
precise by theorems of the project (section 3), 2 attributions that overstate or could not be
confirmed, 1 false as printed, 5 editorial or citation slips, 3 definitions, 3 open, 17
attributions not checked (the sources are not in the repository), 10 conditional statements,
methods and remarks not checked.

## 2. Candidate errata and overstatements

Each was re-read on the page image; the formulas involved are confirmed numerically, so these
are not misreadings of ours.

1. **Page 11, text after formula 39.** "Formula 35 = Formula 36 + 27/2^9 x Relation 123 -
   9/2^10 x Relation 124." As an identity of coefficient vectors this is false; the exact
   identity is Formula 35 = Formula 36 **-** 27/2^9 x Relation 123 - 9/2^10 x Relation 124.
   (The two similar sentences for formulas 38 and 34 hold exactly as printed.)
2. **Page 26, formula (91).** The vector is printed as (b^(b-2), b^(b-3), ..., b^2, b, 1),
   which has b - 1 entries for length n = b. The identity holds with a final entry 0, as in
   formula (89), its case b = 10.
3. **Page 27, formula (100).** The closing parenthesis of P(...) is missing.
4. **Page 35, formula (133).** The recurrence D_(k+1) = D_k - 5 D_(k-1) is stated for k >= 2,
   which leaves D_2 undefined; the formula holds with k >= 1 (D_2 = -4).
5. **Pages 28-29.** The text says that the five zero relations with s = 1, b = 2^12, n = 24 are
   formulas 113 through 118: these are six relations, of rank 5 (the count 5 is right, a Lean
   theorem). The positions of the last non-zero entries are said to be 23, 22, 21, 20, 19;
   they are 23, 23, 22, 21, 20, 19. The sentences fit the list without relation 114.
   (119-122 are four relations of rank 3, as Table 1 says; the paper does not comment.)
6. **Page 8, list (16).** 15/21 and 8/26 are not in lowest terms and equal 5/7 and 4/13, which
   are in the same list; 27/41 is also in list (14), although (16) is a list of additional
   rationals.
7. **Cross-references.** Page 4: the zero relations are said to be in Section 11; they are in
   Section 12. Page 35: the golden mean is said to be in Section 9; it is in Sections 4 and 10.
8. **Reference [18], page 37.** Pages "1339-1342" and the order of the authors do not match the
   paper (local copy: Canad. J. Math. 56 (5), 2004, pp. 897-925; J. M. Borwein, D. Borwein,
   W. F. Galway). Also: the formula printed between (79) and (80), page 25, has no number.

Overstatements:

- **Page 2.** The paper attributes to Borwein, Galway and Borwein (2004) the statement that pi
  has no degree-1 BBP-type formula in a base that is not a power of two. That paper proves it
  for Machin-type arctangent formulas only (its Theorem 7) and poses the general question (its
  problem (10)). The statement itself is true: Theorem L of the project
  (`PiFormula.BaseB.no_pi_bailey`, `bailey_pi_iff`, Lean, no hypothesis).
- **Page 8.** arctan(5/36) is said to have been shown to have a binary formula in [12]. The
  statement is true (exact certificate: 36 + 5i has norm 1321, an atom of index 60). The
  attribution could not be confirmed: the local copy of [12] (arXiv:1603.07395v1) gives a
  formula for arctan(1/6), and 5/36 does not occur in its text.

## 3. "Unknown" statements that the project's theorems settle

| page | statement of the paper | status |
|---|---|---|
| 6 | unknown whether log p has a binary formula for every prime p | No. Theorem G (`no_log23`), Theorem H (below 100: exactly 15 primes), Theorem K (a finite test for every prime). Scope: P(1, 2^B, n, A) with n = B or 2B |
| 8 | not known whether arctan(2/7) has a binary formula | No. Theorem I (`not_isFValue_arctan_two_sevenths`, `no_arctan_two_sevenths`); also 5/8 and 4/9 |
| 29 | not understood why zero relations occur for some (s, b, n) and not others | Degree 1: explained and counted for every B. Base 2: `bailey_count_F2`, `bailey_count_F1`; base 3: `bailey3_count_F2`, `bailey3_count_F1`; every base >= 5: none (Theorem G). Open for s >= 2 |
| 2 | no degree-1 formula for pi outside bases 2^m (attributed, see above) | Theorem L, in full generality for P(1, b^B, N, A) |
| 6 | "certainly not complete" (list (9)) | made precise: 28 primes missing below the largest entry |
| 7 | the set (15) "appears" linearly independent | proved, exactly |
| 29 | zero relations exist "in most but not all cases" together with formulas | made precise for degree 1, base 2: Theorem C says in which rows of Table 1 a multiple of pi is a value |
| 6 | non-binary formulas for logarithms | Theorems K3, K5, M: log b has a base-b formula iff b is a power of 2 or 3 |

Not settled: whether the set of primes of list (9) is infinite (page 6; Theorem K reduces it to
a question of Mersenne type); whether e satisfies a BBP-type relation (page 29); Hypothesis A
(page 3); every "why" for degree >= 2.

## 4. Proposed order of work for the Lean proofs

1. **Generated from coordinates (20 formulas, no new mathematics).** Formulas 2, 3, 17, 18, 19
   (pi), 20, 21, 22 (sqrt(2) pi, sqrt(3) pi, sqrt(5) pi) and zero relations 111-122. The ledger
   has for each the exact coordinates q in `namedA1 ... namedTW` (and `extraS2, extraS3,
   extraS5`). Proof template, as in `Base3/Bailey.lean`: `hasSum_bailey_F2` or `hasSum_bailey_F1`,
   the pattern equals `namedComb q` on 120 residues by `decide +kernel`, then
   `hasSum_namedComb`. Negative bases (2, 3, 18, 19): `hasSum_baileyBlockInt_pair`. A generator
   can write the file from `ledger.json`. With it: "113-118 have rank 5", "119-122 have rank
   3", and the eight vector identities of the prose, erratum 1 included.
2. **Explicit logarithm series (22 formulas, routine).** 8; 67, 71-75, p25.b; 84, 85, 89; the
   general-base logarithms 90, 91, 101, 102, 104-107, 109 and the telescoping example. All are
   finite combinations of the Mercator series; the tools are `hasSum_pow_div_nat`, the
   regrouping lemma `hasSum_blocks_iff` and the generator lemmas `hasSum_gen`, `hasSum_gen3`.
   The general-base ones are identities in a real parameter b > 1 and need no classification.
3. **Arctangents and radicals in degree 1 (24 formulas, new but of known type).** 10, 13,
   25-28 (arguments of Gaussian integers: `hasSum_gamma`, `exp_gamma`, with the half-angle
   identities above); 23, 24 (sqrt(2)-twisted, as `extraS2`); 68 (base 3); 86, 87, 88
   (base 5); the general-base arctangents 92-100 and 103, 108, 110. One lemma does most of it:
   the sum over k = j mod n of x^k/k as a combination of Log(1 - zeta x).
4. **The lists.** (9): evaluate the finite test `isFValue_log_prime_iff_explicit` for each of
   the 46 primes (needs ord_p(2) and the primitive part; the largest has 13 digits). (14),
   (16): 223 statements `IsFValue (arctan q)`, generated from the certificates in the ledger
   with `isFValue_gamma_gen` and `exp_gamma`, as `isFValue_arctan_inv_129`. (15): independence
   from unique factorization in Z[i] (new, small).
5. **Degree >= 2 (55 formulas, out of reach now).** Needs Li_s on the closed unit disc with its
   functional equations, which Mathlib does not have. Order: the distribution relation (a
   rearrangement of series), then Li_2 (reflection, Landen) for 29-39 and 123-125, then Li_3
   for 40-54 and 126-128, then orders 4, 5 and base 3. Nine vectors serve at two degrees: the
   zero relations 111, 112, 114, 126, 129 are, one degree higher, formulas 29, 30 (and 45), 39,
   55, 63; also 17/33, 70/79, 78/80a, 81/83. Vectors and numerical checks are in place.
6. **Outside the project's classes:** 132 (base (2/phi)^10) and 133 (a Lucas sequence). Direct
   computations; low priority.
