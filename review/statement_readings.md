# Statement readings

Each headline statement is read by someone who did not write it and has not seen its proof or
our description of it (`PRACTICES.md`, section 2). This file records the outcome. The reader's
full text and the exact text the reader was given are kept in `review/readings/`.

A reading by an AI agent removes the author's blind spot. It is not the judgment of a
specialist: for the theorems we would claim as new, a person who knows the field should still
read the statement.

## Batch 1: 25 November 2026

- **Reader:** an AI agent (Claude Opus) in a fresh session. It was given one file, the output of
  `scripts/statement_view.py` for the nine theorems, and was allowed to look up Mathlib
  definitions. It was told not to open the repository, the README, the notes or the Lean
  sources, and it did not run Lean.
- **Text read:** `review/readings/2026-11-25-batch1-view.txt` (made from the Lean sources of commit `013827a`).
- **Reader's report:** `review/readings/2026-11-25-batch1-reading.md`.
- **Outcome:** nine statements read, each with confidence "high"; none is vacuous; no convention
  of Lean (division by zero, floor division, where sums start) changes what any of them means.
  The Lean statements needed no change. Three sentences of the README were looser than the
  Lean and were tightened the same day.

| Theorem | What the reader says it states | Compared with our description |
|---|---|---|
| `PiFormula.theoremA` | If a finite rational combination of the angles arctan(1/2^m) and arctan(1/(2^m - 1)), m >= 1, equals q pi with q rational, then only arctan(1/2), arctan 1, arctan(1/3), arctan(1/7) occur, with b1 - a2 + 2 a3 = 0 and q = (a1 + a2 - a3)/4. | Agrees. The converse (every such combination is a relation) is a separate theorem, `combination_is_relation`. |
| `PiFormula.Unconditional.theoremC` | For N > 0 divisible by 120: every N-periodic rational pattern whose series is an algebraic multiple of pi has period 120; those patterns form a space of dimension 13, and the ones with a rational multiple a space of dimension 8. The multiple 0 is allowed in both. | **Wording tightened.** The README said "the formulas for pi form a space of dimension 8"; the space also holds the zero relations. It now says so. |
| `PiFormula.BaseB.no_pi_bailey` | For b >= 2 not a power of 2, B >= 1, N >= 1: if sum_j b^(-Bj) sum_{i=1..N} c_i/(Nj+i) = q pi with rational c_i and q, then q = 0. | Agrees with the "only if" half of Theorem L for positive bases. The "if" half and negative bases are other theorems (`bailey_pi_iff`, `bailey_int_pi_iff`), not read in this batch. |
| `PiFormula.RatBase.hasRelation_iff` | For coprime 0 < q < p: a non-zero periodic rational pattern whose series sum rho(k) (q/p)^floor(k/2)/k is an algebraic multiple of pi, zero allowed, exists if and only if (p, q) is (2,1), (3,1), (4,1), (3,2) or (4,3). | Agrees. The reader's caution, that "has a relation" does not mean "has a formula for pi", is what the README already says: it defines a relation with "0 allowed" and lists separately which bases have formulas. |
| `PiFormula.Compendium.formula_29` | pi^2 = sum_j 16^(-j) [16/(8j+1)^2 - 16/(8j+2)^2 - 8/(8j+3)^2 - 16/(8j+4)^2 - 4/(8j+5)^2 - 4/(8j+6)^2 + 2/(8j+7)^2]. The reader checked the first two blocks numerically: 9.8699 against 9.8696. | Agrees. |
| `PiFormula.Erdos.erdos_pm_one_nat` | For odd q that is not a perfect square: no f with period q, f = 0 on the multiples of q and f = +-1 elsewhere, has partial sums sum_{n<N} f(n)/n tending to 0. This includes the case where the partial sums diverge. | Agrees. |
| `PiFormula.Erdos.erdos_pm_one_lt_11025` | The same for every q with 2 <= q < 11025, squares and even numbers included. The reader notes that q = 1 has to be excluded, as it is. | Agrees. |
| `PiFormula.Erdos.okadaCriterionGeneral` | For q >= 1 and a rational-valued f on the residues mod q: the partial sums of sum f(n)/n tend to 0 if and only if (A) for every unit a, the sum of f(am)/m over the m >= 1 all of whose primes divide q is 0, and (B) for every prime p dividing q, sum_{r=1..q} f(r) lambda_p(r) = 0, with lambda_p(r) = v_p(r) if v_p(r) < v_p(q) and v_p(q) + 1/(p-1) otherwise. The reader checked q = 1 and q = 2 by hand, and that the infinite sum in (A) converges, so Lean's convention for divergent sums plays no part. | **Wording tightened.** The README did not say that the values are rational; it now does. |
| `PiFormula.Erdos.exists_oddValued_sumIsZero_iff` | For odd q > 1: an f with f(0) = 0, every other value a rational with odd numerator and odd denominator, and partial sums tending to 0, exists if and only if q is a perfect square. "Odd-valued" does not mean +-1 and does not mean an odd function. | **Wording tightened.** The README said "odd-valued f"; it now spells out the values and says that this is not a counterexample to the conjecture. |

Conventions the reader checked and found harmless: the terms with index 0 vanish because Lean
sets x/0 = 0, and periodicity still ties rho(0) to rho(N); arctan(1/(2^0 - 1)) = arctan 0 = 0;
in Theorem A the hypothesis b(0) = 0 is essential (arctan 1 = pi/4) and a(0) = 0 only fixes a
coefficient that the sum never sees; condition (B) sums over r = 1, ..., q, so the valuation of
0 never occurs.

## Batches 2, 3 and 4: 25 November 2026

- **Readers:** three AI agents (Claude Opus), each in its own fresh session with one batch, under
  the same rules as batch 1. They ran no Lean; two of them used a short throw-away program for
  arithmetic.
- **Texts read:** `review/readings/2026-11-25-batch2-view.txt`, `...-batch3-view.txt`,
  `...-batch4-view.txt` (from the Lean sources of commit `013827a`). **Reports:** the files
  `...-batch2-reading.md`, `...-batch3-reading.md`, `...-batch4-reading.md` beside them.
- **Outcome:** 47 statements read. No Lean statement needed a change. Two statements could not be
  typed from the text the readers had (see "What the readers could not see"); the tool was
  improved and both were settled. The README was corrected in two places and one definition is
  now described for what it is.

### Batch 2: the binary class F

| Theorem | What the reader says it states | Compared with our description |
|---|---|---|
| `PiFormula.theoremB` | If a finite rational combination of the arguments of the cyclotomic values Phi_{2k+1}(1+i), Phi_{2k+1}(-1-i) and Phi_{2k+1}(i 2^(2^(e+1))) equals q pi with q rational, then only four exceptional atoms carry weight, two of the weights cancel, and q is given by the other two. | Agrees. The README is brief ("the same for the wider cyclotomic family"); the statement is on these representative atoms, and the form over orbits is another theorem (`theoremBgamma`), not read. |
| `Unconditional.value_formula` | Every periodic rational pattern whose series is a rational multiple of pi has the value (7/12 rho(1) + 1/8 rho(2) + 1/6 rho(3) - 7/12 rho(7) + 1/6 rho(9) - 1/8 rho(14)) pi/4. | Agrees. |
| `Unconditional.theoremD_sharp` | Such a pattern that vanishes at every k with gcd(k, 120) in {1, 2, 3} is a rational multiple, possibly 0, of one fixed pattern `zD`. | Agrees with "no formula for pi avoids the slowly converging terms": by `value_formula` such a pattern has value 0. The reader notes that this statement alone does not say `zD` is non-zero or a relation; "a line, of dimension exactly 1" is the separate theorem `finrank_fast`. |
| `Unconditional.bailey_table` | For each of 27 listed triples (B, n, d): the rational vectors a of length n with sum_j 2^(-Bj) sum_i a_i/(nj+i) = 0 form a space of dimension d. | Agrees. |
| `Unconditional.theoremE` | Every periodic rational pattern whose series is r pi with r rational and not 0 has at least 40 non-zero values among rho(0), ..., rho(119), and prime cost at least 7/24. | Agrees: 120 positions are 60 bits, so 40 is 2/3 of a term per bit. That 7/24 is attained is a separate pair of theorems (`primeCost_rhoNew`, `new_formula_series`), not part of this statement. |
| `Unconditional.termCount_eq_forty_iff` | Exactly 40 holds if and only if the pattern is a non-zero rational multiple of one of two explicit patterns (Huvent's). The reader computed their values, 128 pi and 256 pi, and their counts, 40 each. | Agrees. |
| `Unconditional.no_log23` | No periodic rational pattern has a series equal to q log 23 with q a non-zero real algebraic number. | Agrees. |
| `Unconditional.log_primes_below_100` | For a prime p < 100: log p is a value of the class exactly for p in {2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73}. | Agrees. |
| `Unconditional.isFValue_log_rat_iff_pow` | For rational y > 0: log y is a value if and only if some positive power of y is a product of integer powers of 2, the numbers 2^m - 1, and the numbers 2^(2k+1) -+ 2^(k+1) + 1. | Agrees. |
| `Unconditional.isFValue_log_prime_classification` | For a prime l: log l is a value if and only if l divides 2 (2^60 - 1), or every prime q other than l dividing the "primitive part" attached to l divides the order of 2 modulo l and has log q a value. | Agrees, once the type is known: see below. |
| `Unconditional.not_isFValue_arctan_two_sevenths` | arctan(2/7) is not the value of any series of the class. | Agrees. |
| `Unconditional.pairCost_ge` | Two different periodic patterns with the same value r pi, r not 0, have pair cost at least 60, where the pair cost is the number of positions among 0, ..., 119 where at least one is non-zero, plus the number where both have the same non-zero coefficient. | Agrees: 120 positions are 60 bits. |
| `Unconditional.checkedPair` | The same, and two explicit patterns (Takahashi's) both have value pi and pair cost exactly 60. The reader computed: supports of 42 and 50 positions, 58 in the union, 2 equal coefficients. | Agrees. |
| `Unconditional.not_isFValue_log_38737` | log 38737 is not the value of any series of the class. | Agrees. |

The reader also notes that the hypotheses "120 divides N" and "8 divides N" restrict nothing:
a pattern of period N also has period 120 N.

### Batch 3: other bases

| Theorem | What the reader says it states | Compared with our description |
|---|---|---|
| `Base3.Unconditional.isF3Value_log_rat_iff_pow` | For rational y > 0: log y is a value of the base-3 class if and only if some positive power of y is a product of integer powers of 3, the numbers 3^m - 1, and 3^(2k+1) -+ 3^(k+1) + 1. | Agrees. |
| `Base3.Unconditional.not_isF3Value_pi` | pi is not the value of any series sum rho(k)/(3^floor(k/2) k) with rho rational and periodic. | Agrees. |
| `Base3.Unconditional.isF3Value_mul_pi_iff` | For real algebraic gamma: gamma pi is such a value if and only if gamma is a rational multiple of sqrt 3. | Agrees. |
| `Base3.Unconditional.theoremC3` | For N > 0 divisible by 12: every N-periodic rational pattern whose series is an algebraic multiple of pi has period 12; these form a space of dimension 3, and those with value 0 a space of dimension 2. | Agrees. |
| `Base3.Unconditional.theoremE3` | A periodic rational pattern with value gamma pi, gamma algebraic and not 0, has at least 6 non-zero values among rho(0), ..., rho(11); exactly 6 if and only if it is a rational multiple of one of two explicit patterns. The reader checked numerically that both have value sqrt(3) pi. | Agrees. The reader notes that the count is over the fixed window 0, ..., 11, which is one period only because of `theoremC3`. |
| `Base5.Unconditional.eq_zero_of_hasSum_mul_pi` | In base 5: a periodic rational pattern whose series is gamma pi with gamma algebraic, 0 allowed, is identically 0. | Agrees: the README says "no zero relation" as well as "pi is not a value". |
| `Base5.Unconditional.isF5Value_log_rat_iff_pow` | For rational y > 0: log y is a value of the base-5 class if and only if some positive power of y is a product of integer powers of the numbers of an explicit set; the set does not contain 5. | Agrees: the README lists log 5 as not a value. |
| `BaseB.Unconditional.eq_zero_of_hasSum_mul_pi` | The same as the base-5 statement, for every natural base b >= 5. | Agrees. **README corrected**: it said the relation in base 4 was "computed"; it is the Lean theorem `RatBase.hasSum_rhoFour`. **README completed**: for a perfect-power base such as 16 this class is smaller than "the formulas of base 16". |
| `BaseB.Unconditional.transcendental_of_isFBValue` | For b >= 2: every non-zero value of the class of base b is transcendental. | Agrees (the README states it for bases 2, 3, 5 and for b >= 5). |
| `BaseB.bailey_pi_iff` | For a fixed natural b >= 2: a series sum_j b^(-Bj) sum_{i=1..N} c_i/(Nj+i) equal to q pi with q rational and not 0 exists, for some B, N and rational c, if and only if b is a power of 2. | Agrees. |
| `BaseB.bailey_int_pi_iff` | The same for an integer base beta with absolute value at least 2: if and only if the absolute value is a power of 2. | Agrees. |
| `BaseB.no_pi_bailey_ten` | In base 10, a series of this form equal to q pi with q rational has q = 0. | Agrees. |
| `BaseB.bailey_log_self_iff` | For b >= 2: a series of this form in base b equal to log b exists if and only if b is a power of 2 or of 3. | Agrees. |
| `BaseB.no_log_nat_bailey` | If b >= 2 is neither a power of 2 nor of 3: no series of this form in base b equals q pi + q' log n with q, q' rational, q' not 0, and n >= 2 a natural number. | Agrees. |
| `BaseB.terms_per_bit` | If a series of this form in base b equals q pi with q not 0, then b = 2^e and 2 e B <= 3 times the number of non-zero c_i. | Agrees: at least 2/3 of a term per bit. |
| `BaseB.terms_per_bit_attained` | A vector c of length 24 with exactly 8 non-zero entries has sum_j 2^(-12j) sum_i c_i/(24j+i) = q pi with q not 0. | Agrees: equality, 24 = 24. |

### Batch 4: Erdos's conjecture, rational bases, a sample of the Compendium

For every concrete series the reader computed the first terms and compared with the claimed
value; all agree.

| Theorem | What the reader says it states | Compared with our description |
|---|---|---|
| `Erdos.erdos_pm_one_of_cases` | For q >= 2 that is even, or not a perfect square, or has q/phi(q) <= 2: no f with period q, 0 on the multiples of q and +-1 elsewhere, has partial sums of sum f(n)/n tending to 0. | Agrees. |
| `Erdos.erdos_even_nat` | For even q >= 2 and such an f, the partial sums do not converge to any real number. | Agrees. |
| `Erdos.erdos_size_nat` | The same conclusion as the first row for q >= 2 with q/phi(q) <= 2, the inequality not strict. | Agrees. |
| `Erdos.isSquare_of_condA_condB` | If q is odd and f on the residues mod q has f(0) = 0, every other value a rational with odd numerator and denominator, and satisfies conditions (A) and (B), then q is a perfect square. | Agrees. The reader notes that this statement does not mention the series; the link is `okadaCriterionGeneral`, read in batch 1. |
| `Erdos.not_cases_11025` | 11025 is odd, a perfect square, and has q/phi(q) = 35/16 > 2. | Agrees. |
| `RatBase.TheoremR.eq_zero_of_hasSum_mul_pi` | For coprime 0 < q < p outside the five pairs: a periodic rational pattern whose series sum rho(k) (q/p)^floor(k/2)/k is gamma pi, gamma algebraic, is identically 0. | Agrees. |
| `RatBase.pi_base_three_halves` | A series of period 24 in powers of (2/3)^12 with explicit rational coefficients has the value pi/4. | Agrees. |
| `RatBase.sqrt_three_pi_base_four_thirds` | A series of period 12 in powers of (3/4)^6 has the value sqrt(3) pi/9. | Agrees. |
| `RatBase.hasSum_rhoFour` | sum rho(k) 4^(-floor(k/2))/k = sqrt(3) pi/9 for the pattern (1/2, 1, 0, -1, -1/2, 0) of period 6. | Agrees. |
| `Compendium.formula_1` | pi = sum_j 16^(-j) (4/(8j+1) - 2/(8j+4) - 1/(8j+5) - 1/(8j+6)). | Agrees: the formula of Bailey, Borwein and Plouffe. |
| `Compendium.formula_102_real` | For every real b with absolute value greater than 1: log((b-1)/b) = -(1/b^2) sum_j b^(-2j) (b/(2j+1) + 1/(2j+2)). The reader checked a negative b as well. | Agrees. |
| `Compendium.formula_93` | For every natural b >= 2: b^2 sqrt(3) arctan(sqrt(3)/(2b-1)) = (3/2) sum_j (-b^3)^(-j) (b/(3j+1) + 1/(3j+2)). | Agrees. |
| `Compendium.formula_88`, `formula_132` | Two identities with the golden ratio and the powers 5^(1/4), 5^(13/4), 5^(5/4). | Agree, once the type is known: see below. |
| `Compendium.formula_69` | pi sqrt(3) = (1/9) sum_j 3^(-6j) sum_i a_i/(12j+i) with a = (81, -54, 0, -9, 0, -12, -3, -2, 0, -1, 0, 0). | Agrees. |
| `Compendium.formula_76` | pi^2 = (2/27) sum_j 3^(-6j) sum_i a_i/(12j+i)^2 with a = (243, -405, 0, -81, -27, -72, -9, -9, 0, -5, 1, 0). | Agrees. |
| `Compendium.formula_p10_a` | The series sum (-1)^k/(2k+1)^2 converges and its sum is `catalanConst`, which is defined as that same sum. | **README corrected.** It counted this among eight proved formulas of degree 2. The statement is the paper's definition of Catalan's constant and says only that the series converges; the README now says so and counts seven. |

### What the readers could not see

The text given to the readers printed numerals without their types. Two things could not be
decided from it.

- In `formula_88` and `formula_132`, `5 ^ (1/4)`: a real power, or a natural-number power, which
  would be `5 ^ 0`? The reader worked out that the identities hold for real powers and fail for
  natural ones.
- In `isFValue_log_prime_classification`, `orderOf 2`: the order of 2 modulo l, or of the
  natural number 2, which would be 0 and would make the statement say something false?

Both are as they should be: the sources have `(5 : ℝ) ^ ((1 : ℝ) / 4)` and
`orderOf (2 : ZMod ℓ)`. `scripts/statement_view.py` now prints every numeral with its type, and
`review/readings/2026-11-25-typed-check-view.txt` is its output for these three statements. The
views of batches 1 to 4 are kept as the readers saw them.

## Not read yet

- The Compendium has 104 Lean theorems; nine were read (one in batch 1, eight in batch 4).
- Theorems that the README names beside the ones read: `theoremBgamma`, `finrank_fast`,
  `exists_coords3`, `no_pi_L_comb`, the forms of Theorems G, I and K in Bailey's notation, and
  the base-3 identities in Bailey's notation.
- None of the statements has been read by a specialist.
