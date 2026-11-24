module

public import Pilean.Base5.LogNonValues

/-!
# Base 5: examples for the criterion on logarithms

The criterion (`isF5Value_log_rat_iff_pow` of `Base5/LogConverse.lean`, from Baker's theorem):
for a positive rational `y`, `log y` is the value of a series `∑ ρ(k) 5^(-⌊k/2⌋)/k` with `ρ`
rational and periodic if and only if some power `y^k`, `k ≥ 1`, is a product of integer powers
of the base numbers `(5^m - 1)/5^m`, `L_h/5^(2h)`, `M_h/5^(2h)` (`h` odd).

Values, with no hypothesis:

* `isF5Value_log_four_fifths`: `4/5 = (5 - 1)/5`;
* `isF5Value_log_24_25`, `isF5Value_log_124_125`: `(5^2 - 1)/5^2` and `(5^3 - 1)/5^3`;
* `isF5Value_log_11_25`, `isF5Value_log_71_25`: `11 = L_1`, `71 = M_1`;
* `isF5Value_log_three_halves`: `3/2 = (24/25) (4/5)^(-2)`;
* `isF5Value_log_6_5`, `isF5Value_log_9_5`, `isF5Value_log_31_25`.

So `log 2 - (1/2) log 5`, `log 3 - (1/2) log 5`, `log 11 - 2 log 5`, `log 31 - 2 log 5` and
`log 71 - 2 log 5` are values of the class F5.

Not values, from Baker's theorem and good primes (`Base5/LogNonValues.lean`): `log 5` and
`log 2` (`not_isF5Value_log_five_of_goodPrimes5`, `not_isF5Value_log_two_of_goodPrimes5`), and
hence `log 3` (`not_isF5Value_log_three_of_goodPrimes5`).
-/

@[expose] public section

namespace PiFormula

namespace Base5

/-! ## 1. Values -/

/-- `4/5 = (5 - 1)/5`. -/
theorem isF5Value_log_four_fifths : IsF5Value (Real.log (4 / 5)) := by
  have h := isF5Value_log_pow_sub_one (m := 1) one_pos
  have e : ((5 : ℝ) ^ 1 - 1) / 5 ^ 1 = 4 / 5 := by norm_num
  rwa [e] at h

/-- `24/25 = (5^2 - 1)/5^2`. -/
theorem isF5Value_log_24_25 : IsF5Value (Real.log (24 / 25)) := by
  have h := isF5Value_log_pow_sub_one (m := 2) (by norm_num)
  have e : ((5 : ℝ) ^ 2 - 1) / 5 ^ 2 = 24 / 25 := by norm_num
  rwa [e] at h

/-- `124/125 = (5^3 - 1)/5^3`. -/
theorem isF5Value_log_124_125 : IsF5Value (Real.log (124 / 125)) := by
  have h := isF5Value_log_pow_sub_one (m := 3) (by norm_num)
  have e : ((5 : ℝ) ^ 3 - 1) / 5 ^ 3 = 124 / 125 := by norm_num
  rwa [e] at h

/-- `11/25 = L_1/5^2`. -/
theorem isF5Value_log_11_25 : IsF5Value (Real.log (11 / 25)) := by
  have h := isF5Value_log_L5 (h := 1) odd_one
  have e : ((L5 1 : ℤ) : ℝ) / 5 ^ (2 * 1) = 11 / 25 := by
    rw [L5_one]
    norm_num
  rwa [e] at h

/-- `71/25 = M_1/5^2`. -/
theorem isF5Value_log_71_25 : IsF5Value (Real.log (71 / 25)) := by
  have h := isF5Value_log_M5 (h := 1) odd_one
  have e : ((M5 1 : ℤ) : ℝ) / 5 ^ (2 * 1) = 71 / 25 := by
    rw [M5_one]
    norm_num
  rwa [e] at h

/-- `3/2 = (24/25) (4/5)^(-2)`. -/
theorem isF5Value_log_three_halves : IsF5Value (Real.log (3 / 2)) := by
  have h := isF5Value_log_24_25.sub (isF5Value_log_four_fifths.const_mul 2)
  have e : Real.log (24 / 25) - ((2 : ℚ) : ℝ) * Real.log (4 / 5) = Real.log (3 / 2) := by
    rw [show (24 / 25 : ℝ) = 3 / 2 * (4 / 5) ^ 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  rwa [e] at h

/-- The same example through the criterion: `(3/2)^1 = (24/25)^1 (4/5)^(-2)`. -/
theorem isF5Value_log_three_halves' : IsF5Value (Real.log ((3 / 2 : ℚ) : ℝ)) := by
  refine isF5Value_log_of_pow (y := 3 / 2) (by norm_num) (k := 1) one_pos (n := 2)
    (g := ![24 / 25, 4 / 5]) (e := ![1, -2]) ?_ ?_
  · intro i
    fin_cases i
    · exact Or.inl ⟨2, by norm_num, by norm_num⟩
    · exact Or.inl ⟨1, one_pos, by norm_num⟩
  · rw [Fin.prod_univ_two]
    norm_num

/-- `6/5 = (24/25) (4/5)^(-1)`. -/
theorem isF5Value_log_6_5 : IsF5Value (Real.log (6 / 5)) := by
  have h := isF5Value_log_24_25.sub isF5Value_log_four_fifths
  have e : Real.log (24 / 25) - Real.log (4 / 5) = Real.log (6 / 5) := by
    rw [show (24 / 25 : ℝ) = 6 / 5 * (4 / 5) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rwa [e] at h

/-- `9/5 = (24/25)^2 (4/5)^(-3)`. -/
theorem isF5Value_log_9_5 : IsF5Value (Real.log (9 / 5)) := by
  have h := (isF5Value_log_24_25.const_mul 2).sub (isF5Value_log_four_fifths.const_mul 3)
  have e : ((2 : ℚ) : ℝ) * Real.log (24 / 25) - ((3 : ℚ) : ℝ) * Real.log (4 / 5) =
      Real.log (9 / 5) := by
    have h1 : Real.log (24 / 25) = Real.log (6 / 5) + Real.log (4 / 5) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have h2 : Real.log (9 / 5) = 2 * Real.log (6 / 5) - Real.log (4 / 5) := by
      rw [show (9 / 5 : ℝ) = (6 / 5) ^ 2 / (4 / 5) by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_pow]
      push_cast
      ring
    rw [h1, h2]
    push_cast
    ring
  rwa [e] at h

/-- `31/25 = (124/125) (4/5)^(-1)`. -/
theorem isF5Value_log_31_25 : IsF5Value (Real.log (31 / 25)) := by
  have h := isF5Value_log_124_125.sub isF5Value_log_four_fifths
  have e : Real.log (124 / 125) - Real.log (4 / 5) = Real.log (31 / 25) := by
    rw [show (124 / 125 : ℝ) = 31 / 25 * (4 / 5) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rwa [e] at h

/-- `log 2 - (1/2) log 5` is a value of the class F5. -/
theorem isF5Value_log_two_sub : IsF5Value (Real.log 2 - 1 / 2 * Real.log 5) := by
  have h := isF5Value_log_four_fifths.const_mul (1 / 2)
  have e : ((1 / 2 : ℚ) : ℝ) * Real.log (4 / 5) = Real.log 2 - 1 / 2 * Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast
    ring
  rwa [e] at h

/-- `log 3 - (1/2) log 5` is a value of the class F5. -/
theorem isF5Value_log_three_sub : IsF5Value (Real.log 3 - 1 / 2 * Real.log 5) := by
  have h := isF5Value_log_three_halves.add isF5Value_log_two_sub
  have e : Real.log (3 / 2) + (Real.log 2 - 1 / 2 * Real.log 5) =
      Real.log 3 - 1 / 2 * Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    ring
  rwa [e] at h

/-! ## 2. Not values (from Baker's theorem and good primes) -/

/-- **`log 3` is not the value of any series of the class F5** (from Baker's theorem and good
primes): `log 3 - log 2 = log (3/2)` is a value, and `log 2` is not. -/
theorem not_isF5Value_log_three_of_goodPrimes5 (hB : BakerTheorem) (hG : GoodPrimes5) :
    ¬ IsF5Value (Real.log 3) := by
  intro h
  apply not_isF5Value_log_two_of_goodPrimes5 hB hG
  have h1 := h.sub isF5Value_log_three_halves
  have e : Real.log 3 - Real.log (3 / 2) = Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    ring
  rwa [e] at h1

/-- From Baker's theorem and good primes: no power `5^k`, `k ≥ 1`, is a product of integer
powers of base numbers. -/
theorem five_pow_ne_prod_of_goodPrimes5 (hB : BakerTheorem) (hG : GoodPrimes5) {k : ℕ}
    (hk : 0 < k) {n : ℕ} {g : Fin n → ℚ} {e : Fin n → ℤ} (hg : ∀ i, g i ∈ baseNumbers5) :
    (5 : ℚ) ^ k ≠ ∏ i, g i ^ e i := by
  intro h
  apply not_isF5Value_log_five_of_goodPrimes5 hB hG
  have h1 := isF5Value_log_of_pow (y := 5) (by norm_num) hk hg h
  simpa using h1

end Base5

end PiFormula
