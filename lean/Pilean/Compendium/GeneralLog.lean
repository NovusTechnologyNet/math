import Pilean.Compendium.GeneralCore

/-!
# Bailey's Compendium, general bases: logarithms of rational functions of `b`

Formulas (90), (91), (101), (102), (104) to (107), (109) of the Compendium (pages 26 to 28) and
the telescoping example of page 4, as printed. For each formula `N` there are two theorems:
`formula_N_real`, for a real parameter `b`, in the form `BaileyFormulaReal`; and `formula_N`,
for a natural number `b ≥ 2`, in the form `BaileyFormula` / `BaileyFormulaInt` of the other
formulas of the Compendium.

The paper states no range for `b`. The ranges proved here:

* (90), (101), (102), (104), (105): every real `b` with `|b| > 1`;
* (106), (107): every real `b` with `2b² > 1`;
* (109), both signs: every real `b` with `3b² > 1`;
* (91) (length `b`): every natural `b ≥ 2`;
* the example of page 4: every real `b` with `|b| > 1`.

Each proof takes one of the series of `GeneralCore.lean` at `v = ±1/b`, `±1/(2b)` or
`±1/(3b)`, multiplies it by a constant, and checks the vector entry by entry.

Formula (91) is printed with the vector `(b^(b-2), b^(b-3), …, b², b, 1)`, which has `b - 1`
entries for the length `b`; it is stated with the last entry `a_b = 0`, as the ledger records
it (formula (89) is the case `b = 10`, printed with that `0`).
-/

namespace PiFormula

namespace Compendium

open BaseB

/-! ## 1. Formulas (101), (102): `log ((b ± 1) / b)` -/

/-- **Formula (102)** of the Compendium (page 27), real parameter:
`log ((b - 1)/b) = -(1/b²) P(1, b², 2, (b, 1))` for `|b| > 1`. -/
theorem formula_102_real {b : ℝ} (hb : 1 < |b|) :
    BaileyFormulaReal (Real.log ((b - 1) / b)) (-(1 / b ^ 2)) (b ^ 2) 2 ![b, 1] := by
  have hb0 := param_ne_zero hb
  have h := hasBaileyValueReal_pow (N := 2) (by norm_num) (v := 1 / b) (β := b ^ 2)
    (by field_simp) (param_abs_inv_lt_one hb)
  refine ((h.smul (b ^ 2)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp
  · have e : 1 - 1 / b = (b - 1) / b := by field_simp
    rw [e]
    field_simp

/-- **Formula (101)** of the Compendium (page 27), real parameter:
`log ((b + 1)/b) = (1/b²) P(1, b², 2, (b, -1))` for `|b| > 1`. -/
theorem formula_101_real {b : ℝ} (hb : 1 < |b|) :
    BaileyFormulaReal (Real.log ((b + 1) / b)) (1 / b ^ 2) (b ^ 2) 2 ![b, -1] := by
  have hb0 := param_ne_zero hb
  have h := hasBaileyValueReal_pow (N := 2) (by norm_num) (v := -(1 / b)) (β := b ^ 2)
    (by field_simp) (by rw [abs_neg]; exact param_abs_inv_lt_one hb)
  refine ((h.smul (-b ^ 2)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp
  · have e : 1 - -(1 / b) = (b + 1) / b := by
      field_simp
      ring
    rw [e]
    field_simp

/-! ## 2. Formulas (104), (105), (90): `log (b² ± b + 1)` -/

/-- **Formula (104)** of the Compendium (page 28), real parameter:
`log ((b² + b + 1)/b²) = (1/b³) P(1, b³, 3, (b², b, -2))` for `|b| > 1`. -/
theorem formula_104_real {b : ℝ} (hb : 1 < |b|) :
    BaileyFormulaReal (Real.log ((b ^ 2 + b + 1) / b ^ 2)) (1 / b ^ 3) (b ^ 3) 3
      ![b ^ 2, b, -2] := by
  have hb0 := param_ne_zero hb
  have h := hasBaileyValueReal_w3_re (v := 1 / b) (β := b ^ 3) (by field_simp)
    (param_inv_sq_lt_one hb)
  refine ((h.smul (-2 * b ^ 3)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp
  · have e : 1 + 1 / b + (1 / b) ^ 2 = (b ^ 2 + b + 1) / b ^ 2 := by
      field_simp
    rw [e]
    field_simp

/-- **Formula (105)** of the Compendium (page 28), real parameter:
`log ((b² - b + 1)/b²) = -(1/b³) P(1, -b³, 3, (b², -b, -2))` for `|b| > 1`. -/
theorem formula_105_real {b : ℝ} (hb : 1 < |b|) :
    BaileyFormulaReal (Real.log ((b ^ 2 - b + 1) / b ^ 2)) (-(1 / b ^ 3)) (-b ^ 3) 3
      ![b ^ 2, -b, -2] := by
  have hb0 := param_ne_zero hb
  have h := hasBaileyValueReal_w3_re (v := -(1 / b)) (β := -b ^ 3) (by field_simp)
    (by rw [neg_sq]; exact param_inv_sq_lt_one hb)
  refine ((h.smul (2 * b ^ 3)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp
  · have e : 1 + -(1 / b) + (-(1 / b)) ^ 2 = (b ^ 2 - b + 1) / b ^ 2 := by
      field_simp
      ring
    rw [e]
    field_simp

/-- **Formula (90)** of the Compendium (page 26), real parameter:
`b² log ((b² + b + 1)/(b² - 2b + 1)) = 3 P(1, b³, 3, (b, 1, 0))` for `|b| > 1`. The series is
the one of `-log (1 - 1/b)` minus the one of `-(1/2) log (1 + 1/b + 1/b²)`, times `2b²/3`. -/
theorem formula_90_real {b : ℝ} (hb : 1 < |b|) :
    BaileyFormulaReal (b ^ 2 * Real.log ((b ^ 2 + b + 1) / (b ^ 2 - 2 * b + 1))) 3 (b ^ 3) 3
      ![b, 1, 0] := by
  have hb0 := param_ne_zero hb
  have h1 := hasBaileyValueReal_pow (N := 3) (by norm_num) (v := 1 / b) (β := b ^ 3)
    (by field_simp) (param_abs_inv_lt_one hb)
  have h2 := hasBaileyValueReal_w3_re (v := 1 / b) (β := b ^ 3) (by field_simp)
    (param_inv_sq_lt_one hb)
  refine (((h1.sub h2).smul (2 * b ^ 2 / 3)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp <;> ring
  · have hv := abs_lt.1 (param_abs_inv_lt_one hb)
    have h1v : 1 - 1 / b ≠ 0 := by linarith [hv.2]
    have hpos : 0 < 1 + 1 / b + (1 / b) ^ 2 := by nlinarith [sq_nonneg (1 / b + 1 / 2)]
    have hb1 : b - 1 ≠ 0 := by
      intro h0
      have e1 : b = 1 := by linarith
      rw [e1, abs_one] at hb
      linarith
    have e : (b ^ 2 + b + 1) / (b ^ 2 - 2 * b + 1) =
        (1 + 1 / b + (1 / b) ^ 2) / (1 - 1 / b) ^ 2 := by
      have e2 : b ^ 2 - 2 * b + 1 = (b - 1) ^ 2 := by ring
      rw [e2]
      field_simp
    rw [e, Real.log_div hpos.ne' (pow_ne_zero 2 h1v), Real.log_pow]
    push_cast
    ring

/-! ## 3. Formulas (106), (107): `log (2b² ± 2b + 1)` -/

/-- **Formula (106)** of the Compendium (page 28), real parameter:
`log ((2b² - 2b + 1)/(2b²)) = -(1/(2b⁴)) P(1, -4b⁴, 4, (2b³, 0, -b, -1))` for `2b² > 1`. -/
theorem formula_106_real {b : ℝ} (hb : 1 < 2 * b ^ 2) :
    BaileyFormulaReal (Real.log ((2 * b ^ 2 - 2 * b + 1) / (2 * b ^ 2))) (-(1 / (2 * b ^ 4)))
      (-4 * b ^ 4) 4 ![2 * b ^ 3, 0, -b, -1] := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    norm_num at hb
  have h := hasBaileyValueReal_gauss_re (v := 1 / (2 * b)) (β := -4 * b ^ 4)
    (by field_simp; ring) (param_gauss hb)
  refine ((h.smul (4 * b ^ 4)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp <;> ring
  · have e : 1 - 2 * (1 / (2 * b)) + 2 * (1 / (2 * b)) ^ 2 =
        (2 * b ^ 2 - 2 * b + 1) / (2 * b ^ 2) := by
      field_simp
    rw [e]
    field_simp
    ring

/-- **Formula (107)** of the Compendium (page 28), real parameter:
`log ((2b² + 2b + 1)/(2b²)) = (1/(2b⁴)) P(1, -4b⁴, 4, (2b³, 0, -b, 1))` for `2b² > 1`. -/
theorem formula_107_real {b : ℝ} (hb : 1 < 2 * b ^ 2) :
    BaileyFormulaReal (Real.log ((2 * b ^ 2 + 2 * b + 1) / (2 * b ^ 2))) (1 / (2 * b ^ 4))
      (-4 * b ^ 4) 4 ![2 * b ^ 3, 0, -b, 1] := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    norm_num at hb
  have h := hasBaileyValueReal_gauss_re (v := -(1 / (2 * b))) (β := -4 * b ^ 4)
    (by field_simp; ring) (by rw [neg_sq]; exact param_gauss hb)
  refine ((h.smul (-4 * b ^ 4)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp <;> ring
  · have e : 1 - 2 * -(1 / (2 * b)) + 2 * (-(1 / (2 * b))) ^ 2 =
        (2 * b ^ 2 + 2 * b + 1) / (2 * b ^ 2) := by
      field_simp
      ring
    rw [e]
    field_simp
    ring

/-! ## 4. Formula (109): `log (3b² ± 3b + 1)` -/

/-- **Formula (109)** of the Compendium (page 28), lower signs, real parameter:
`log ((3b² - 3b + 1)/(3b²)) = -(1/(27b⁶)) P(1, -27b⁶, 6, (27b⁵, 9b⁴, 0, -3b², -3b, -2))` for
`3b² > 1`. -/
theorem formula_109_minus_real {b : ℝ} (hb : 1 < 3 * b ^ 2) :
    BaileyFormulaReal (Real.log ((3 * b ^ 2 - 3 * b + 1) / (3 * b ^ 2)))
      (-(1 / (27 * b ^ 6))) (-27 * b ^ 6) 6
      ![27 * b ^ 5, 9 * b ^ 4, 0, -3 * b ^ 2, -3 * b, -2] := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    norm_num at hb
  have h := hasBaileyValueReal_eis_re (v := 1 / (3 * b)) (β := -27 * b ^ 6)
    (by field_simp; ring) (param_eis hb)
  refine ((h.smul (54 * b ^ 6)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp <;> ring
  · have e : 1 - 3 * (1 / (3 * b)) + 3 * (1 / (3 * b)) ^ 2 =
        (3 * b ^ 2 - 3 * b + 1) / (3 * b ^ 2) := by
      field_simp
    rw [e]
    field_simp
    ring

/-- **Formula (109)** of the Compendium (page 28), upper signs, real parameter:
`log ((3b² + 3b + 1)/(3b²)) = (1/(27b⁶)) P(1, -27b⁶, 6, (27b⁵, -9b⁴, 0, 3b², -3b, 2))` for
`3b² > 1`. -/
theorem formula_109_plus_real {b : ℝ} (hb : 1 < 3 * b ^ 2) :
    BaileyFormulaReal (Real.log ((3 * b ^ 2 + 3 * b + 1) / (3 * b ^ 2)))
      (1 / (27 * b ^ 6)) (-27 * b ^ 6) 6
      ![27 * b ^ 5, -9 * b ^ 4, 0, 3 * b ^ 2, -3 * b, 2] := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    norm_num at hb
  have h := hasBaileyValueReal_eis_re (v := -(1 / (3 * b))) (β := -27 * b ^ 6)
    (by field_simp; ring) (by rw [neg_sq]; exact param_eis hb)
  refine ((h.smul (-54 * b ^ 6)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp <;> ring
  · have e : 1 - 3 * -(1 / (3 * b)) + 3 * (-(1 / (3 * b))) ^ 2 =
        (3 * b ^ 2 + 3 * b + 1) / (3 * b ^ 2) := by
      field_simp
      ring
    rw [e]
    field_simp
    ring

/-! ## 5. The same formulas for a natural number `b ≥ 2` -/

/-- **Formula (90)** of the Compendium (page 26), `b ≥ 2` natural:
`b² log ((b² + b + 1)/(b² - 2b + 1)) = 3 P(1, b³, 3, (b, 1, 0))`. -/
theorem formula_90 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormula ((b : ℝ) ^ 2 * Real.log (((b : ℝ) ^ 2 + b + 1) / ((b : ℝ) ^ 2 - 2 * b + 1)))
      3 b 3 3 ![(b : ℚ), 1, 0] := by
  refine (formula_90_real (one_lt_abs_natCast hb)).to_nat rfl fun i => ?_
  fin_cases i <;> simp

/-- **Formula (101)** of the Compendium (page 27), `b ≥ 2` natural:
`log ((b + 1)/b) = (1/b²) P(1, b², 2, (b, -1))`. -/
theorem formula_101 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormula (Real.log (((b : ℝ) + 1) / b)) (1 / (b : ℝ) ^ 2) b 2 2 ![(b : ℚ), -1] := by
  refine (formula_101_real (one_lt_abs_natCast hb)).to_nat rfl fun i => ?_
  fin_cases i <;> simp

/-- **Formula (102)** of the Compendium (page 27), `b ≥ 2` natural:
`log ((b - 1)/b) = -(1/b²) P(1, b², 2, (b, 1))`. -/
theorem formula_102 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormula (Real.log (((b : ℝ) - 1) / b)) (-(1 / (b : ℝ) ^ 2)) b 2 2 ![(b : ℚ), 1] := by
  refine (formula_102_real (one_lt_abs_natCast hb)).to_nat rfl fun i => ?_
  fin_cases i <;> simp

/-- **Formula (104)** of the Compendium (page 28), `b ≥ 2` natural:
`log ((b² + b + 1)/b²) = (1/b³) P(1, b³, 3, (b², b, -2))`. -/
theorem formula_104 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormula (Real.log (((b : ℝ) ^ 2 + b + 1) / (b : ℝ) ^ 2)) (1 / (b : ℝ) ^ 3) b 3 3
      ![(b : ℚ) ^ 2, b, -2] := by
  refine (formula_104_real (one_lt_abs_natCast hb)).to_nat rfl fun i => ?_
  fin_cases i <;> simp

/-- **Formula (105)** of the Compendium (page 28), `b ≥ 2` natural:
`log ((b² - b + 1)/b²) = -(1/b³) P(1, -b³, 3, (b², -b, -2))`. -/
theorem formula_105 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormulaInt (Real.log (((b : ℝ) ^ 2 - b + 1) / (b : ℝ) ^ 2)) (-(1 / (b : ℝ) ^ 3))
      (-(b : ℤ) ^ 3) 1 3 ![(b : ℚ) ^ 2, -b, -2] := by
  refine (formula_105_real (one_lt_abs_natCast hb)).to_int (by push_cast; ring) fun i => ?_
  fin_cases i <;> simp

/-- **Formula (106)** of the Compendium (page 28), `b ≥ 2` natural:
`log ((2b² - 2b + 1)/(2b²)) = -(1/(2b⁴)) P(1, -4b⁴, 4, (2b³, 0, -b, -1))`. -/
theorem formula_106 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormulaInt (Real.log ((2 * (b : ℝ) ^ 2 - 2 * b + 1) / (2 * (b : ℝ) ^ 2)))
      (-(1 / (2 * (b : ℝ) ^ 4))) (-4 * (b : ℤ) ^ 4) 1 4 ![2 * (b : ℚ) ^ 3, 0, -b, -1] := by
  have hb' := one_lt_natCast_of_two_le hb
  refine (formula_106_real (by nlinarith)).to_int (by push_cast; ring) fun i => ?_
  fin_cases i <;> simp

/-- **Formula (107)** of the Compendium (page 28), `b ≥ 2` natural:
`log ((2b² + 2b + 1)/(2b²)) = (1/(2b⁴)) P(1, -4b⁴, 4, (2b³, 0, -b, 1))`. -/
theorem formula_107 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormulaInt (Real.log ((2 * (b : ℝ) ^ 2 + 2 * b + 1) / (2 * (b : ℝ) ^ 2)))
      (1 / (2 * (b : ℝ) ^ 4)) (-4 * (b : ℤ) ^ 4) 1 4 ![2 * (b : ℚ) ^ 3, 0, -b, 1] := by
  have hb' := one_lt_natCast_of_two_le hb
  refine (formula_107_real (by nlinarith)).to_int (by push_cast; ring) fun i => ?_
  fin_cases i <;> simp

/-- **Formula (109)** of the Compendium (page 28), lower signs, `b ≥ 2` natural:
`log ((3b² - 3b + 1)/(3b²)) = -(1/(27b⁶)) P(1, -27b⁶, 6, (27b⁵, 9b⁴, 0, -3b², -3b, -2))`. -/
theorem formula_109_minus {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormulaInt (Real.log ((3 * (b : ℝ) ^ 2 - 3 * b + 1) / (3 * (b : ℝ) ^ 2)))
      (-(1 / (27 * (b : ℝ) ^ 6))) (-27 * (b : ℤ) ^ 6) 1 6
      ![27 * (b : ℚ) ^ 5, 9 * b ^ 4, 0, -3 * b ^ 2, -3 * b, -2] := by
  have hb' := one_lt_natCast_of_two_le hb
  refine (formula_109_minus_real (by nlinarith)).to_int (by push_cast; ring) fun i => ?_
  fin_cases i <;> simp

/-- **Formula (109)** of the Compendium (page 28), upper signs, `b ≥ 2` natural:
`log ((3b² + 3b + 1)/(3b²)) = (1/(27b⁶)) P(1, -27b⁶, 6, (27b⁵, -9b⁴, 0, 3b², -3b, 2))`. -/
theorem formula_109_plus {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormulaInt (Real.log ((3 * (b : ℝ) ^ 2 + 3 * b + 1) / (3 * (b : ℝ) ^ 2)))
      (1 / (27 * (b : ℝ) ^ 6)) (-27 * (b : ℤ) ^ 6) 1 6
      ![27 * (b : ℚ) ^ 5, -9 * b ^ 4, 0, 3 * b ^ 2, -3 * b, 2] := by
  have hb' := one_lt_natCast_of_two_le hb
  refine (formula_109_plus_real (by nlinarith)).to_int (by push_cast; ring) fun i => ?_
  fin_cases i <;> simp

/-! ## 6. The telescoping example of page 4 -/

/-- **The telescoping example** of the Compendium (page 4, without number), real parameter:
`∑_{k ≥ 1} (1/b^k) (b²/k - 1/(k + 2)) = b + 1/2` for `|b| > 1`. The sum over `k ≥ 1` is
written over `k ≥ 0` with `k + 1` in place of `k`. With `x = 1/b` the two halves are
`b² ∑_{k ≥ 1} x^k / k` and `b² ∑_{k ≥ 3} x^k / k`, and the difference is `b² (x + x²/2)`. -/
theorem formula_p04_b_real {b : ℝ} (hb : 1 < |b|) :
    HasSum (fun k : ℕ => 1 / b ^ (k + 1) *
      (b ^ 2 / ((k + 1 : ℕ) : ℝ) - 1 / (((k + 1 : ℕ) : ℝ) + 2))) (b + 1 / 2) := by
  have hb0 := param_ne_zero hb
  have h0 := hasSum_pow_div (param_abs_inv_lt_one hb)
  have h1 := (hasSum_nat_add_iff' 1).2 h0
  have h3 := (hasSum_nat_add_iff' 3).2 h0
  have h := (h1.mul_left (b ^ 2)).sub (h3.mul_left (b ^ 2))
  convert h using 1
  · funext k
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hk3 : ((k : ℝ) + 1 + 2) ≠ 0 := by positivity
    have e3 : b ^ (k + 3) = b ^ (k + 1) * b ^ 2 := by ring
    rw [one_div_pow, one_div_pow, e3]
    push_cast
    field_simp
    ring
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    field_simp
    ring

/-- **The telescoping example** of the Compendium (page 4, without number), `b ≥ 2` natural:
`∑_{k ≥ 1} (1/b^k) (b²/k - 1/(k + 2)) = b + 1/2`. -/
theorem formula_p04_b {b : ℕ} (hb : 2 ≤ b) :
    HasSum (fun k : ℕ => 1 / (b : ℝ) ^ (k + 1) *
      ((b : ℝ) ^ 2 / ((k + 1 : ℕ) : ℝ) - 1 / (((k + 1 : ℕ) : ℝ) + 2))) ((b : ℝ) + 1 / 2) :=
  formula_p04_b_real (one_lt_abs_natCast hb)

/-! ## 7. Formula (91): length `b` -/

/-- **Formula (91)** of the Compendium (page 26), `b ≥ 2` natural:
`b^(b-2) log ((b^b - 1)/(b - 1)^b) = P(1, b^b, b, (b^(b-2), b^(b-3), …, b, 1, 0))`.
The print has the `b - 1` entries `b^(b-2), …, b, 1` for the length `b`; the last entry `0` is
supplied here, as in the ledger. The entry `a_i` (`1 ≤ i ≤ b`) is `b^(b-1-i)` for `i < b` and
`0` for `i = b`. The series is `∑_{k ≥ 1} g(k) b^(-k) / k` with `g(k) = b` for `b ∤ k` and
`g(k) = 0` for `b ∣ k`, times `b^(b-2)`. -/
theorem formula_91 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormula ((b : ℝ) ^ (b - 2) * Real.log (((b : ℝ) ^ b - 1) / ((b : ℝ) - 1) ^ b)) 1
      b b b (fun i => if (i : ℕ) + 1 < b then (b : ℚ) ^ (b - 2 - (i : ℕ)) else 0) := by
  have hb0 : 0 < b := by omega
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb0.ne'
  have h := hasBaileyValue_step_one (b := b) (N := b) hb hb0 [(1, (b : ℚ)), (b, -(b : ℚ))]
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨one_pos, one_dvd b⟩
      · exact ⟨hb0, dvd_refl b⟩)
  refine ((h.smul ((b : ℚ) ^ (b - 2))).of_eq ?_ rfl).formula ?_
  · funext i
    have hi := i.isLt
    simp only [Pi.smul_apply, smul_eq_mul, listPat, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, one_dvd, ite_true, add_zero]
    by_cases hlt : (i : ℕ) + 1 < b
    · have hnd : ¬ b ∣ (i : ℕ) + 1 := Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) hlt
      rw [ite_eq_left hlt, ite_eq_right hnd, add_zero]
      have e1 : b - 2 = (b - 2 - (i : ℕ)) + (i : ℕ) := by omega
      have e2 : (b : ℚ) ^ (b - 2) = (b : ℚ) ^ (b - 2 - (i : ℕ)) * (b : ℚ) ^ (i : ℕ) := by
        rw [← pow_add, ← e1]
      rw [e2, pow_succ]
      field_simp
    · have he : (i : ℕ) + 1 = b := by omega
      have hd : b ∣ (i : ℕ) + 1 := by rw [he]
      rw [ite_eq_right hlt, ite_eq_left hd]
      ring
  · have t1 : logTerm b 1 = Real.log b - Real.log ((b : ℝ) - 1) / (1 : ℕ) :=
      logTerm_eq (b := b) (d := 1) (m := (b : ℝ) - 1) hb one_pos (by ring)
    have tb : logTerm b b = Real.log b - Real.log ((b : ℝ) ^ b - 1) / (b : ℕ) :=
      logTerm_eq (b := b) (d := b) (m := (b : ℝ) ^ b - 1) hb hb0 (by ring)
    have hpow : (1 : ℝ) < (b : ℝ) ^ b := one_lt_pow₀ (by linarith) hb0.ne'
    have hb1 : (b : ℝ) - 1 ≠ 0 := by
      have : (0 : ℝ) < (b : ℝ) - 1 := by linarith
      exact this.ne'
    have hbR0 : (b : ℝ) ≠ 0 := by positivity
    rw [listVal_cons, listVal_cons, listVal_nil, t1, tb,
      Real.log_div (by linarith : (b : ℝ) ^ b - 1 ≠ 0) (pow_ne_zero b hb1), Real.log_pow]
    push_cast
    field_simp
    ring

end Compendium

end PiFormula
