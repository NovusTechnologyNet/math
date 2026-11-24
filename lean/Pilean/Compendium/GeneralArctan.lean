module

public import Pilean.Compendium.GeneralCore

/-!
# Bailey's Compendium, general bases: arctangents of rational functions of `b`

Formulas (93), (94), (95), (96), (98), (99) of the Compendium (page 27), as printed. For each
formula `N` there are two theorems: `formula_N_real`, for a real parameter `b`, in the form
`BaileyFormulaReal`; and `formula_N`, for a natural number `b ≥ 2`, in the form `BaileyFormula`
/ `BaileyFormulaInt` of the other formulas of the Compendium.

The paper states no range for `b`. The ranges proved here:

* (93), (94): every real `b` with `|b| > 1`;
* (95), (96): every real `b` with `2b² > 1`;
* (98), (99): every real `b` with `3b² > 1`.

Each proof takes one of the series of `GeneralCore.lean` at `v = ±1/b`, `±1/(2b)` or
`±1/(3b)`, multiplies it by a constant, and checks the vector entry by entry.
-/

@[expose] public section

namespace PiFormula

namespace Compendium

open BaseB

theorem sqrt3_ne_zero : Real.sqrt 3 ≠ 0 := Base3.sqrt3_pos.ne'

/-- `3 / √3 = √3`. -/
theorem three_div_sqrt3 : (3 : ℝ) / Real.sqrt 3 = Real.sqrt 3 := Real.div_sqrt

/-- `1 / √3 = √3 / 3`. -/
theorem one_div_sqrt3 : 1 / Real.sqrt 3 = Real.sqrt 3 / 3 := by
  rw [div_eq_div_iff sqrt3_ne_zero (by norm_num)]
  linear_combination -Base3.sqrt3_mul_self

/-! ## 1. Formulas (93), (94): `arctan (√3 / (2b ∓ 1))` -/

/-- **Formula (94)** of the Compendium (page 27), real parameter:
`b² √3 arctan (√3/(2b + 1)) = (3/2) P(1, b³, 3, (b, -1, 0))` for `|b| > 1`. -/
theorem formula_94_real {b : ℝ} (hb : 1 < |b|) :
    BaileyFormulaReal (b ^ 2 * Real.sqrt 3 * Real.arctan (Real.sqrt 3 / (2 * b + 1))) (3 / 2)
      (b ^ 3) 3 ![b, -1, 0] := by
  have hb0 := param_ne_zero hb
  have hs := sqrt3_ne_zero
  have h := hasBaileyValueReal_w3_im (v := 1 / b) (β := b ^ 3) (by field_simp)
    (param_inv_sq_lt_one hb)
  refine ((h.smul (2 * b ^ 2 / Real.sqrt 3)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp
  · have h2 : 2 * b + 1 ≠ 0 := by
      rcases lt_abs.1 hb with h1 | h1 <;> intro h0 <;> linarith
    have e : Real.sqrt 3 * (1 / b) / (2 + 1 / b) = Real.sqrt 3 / (2 * b + 1) := by
      have e1 : 2 + 1 / b = (2 * b + 1) / b := by field_simp
      rw [e1]
      field_simp
    rw [e]
    linear_combination (-(b ^ 2 * Real.arctan (Real.sqrt 3 / (2 * b + 1)))) * three_div_sqrt3

/-- **Formula (93)** of the Compendium (page 27), real parameter:
`b² √3 arctan (√3/(2b - 1)) = (3/2) P(1, -b³, 3, (b, 1, 0))` for `|b| > 1`. -/
theorem formula_93_real {b : ℝ} (hb : 1 < |b|) :
    BaileyFormulaReal (b ^ 2 * Real.sqrt 3 * Real.arctan (Real.sqrt 3 / (2 * b - 1))) (3 / 2)
      (-b ^ 3) 3 ![b, 1, 0] := by
  have hb0 := param_ne_zero hb
  have hs := sqrt3_ne_zero
  have h := hasBaileyValueReal_w3_im (v := -(1 / b)) (β := -b ^ 3) (by field_simp)
    (by rw [neg_sq]; exact param_inv_sq_lt_one hb)
  refine ((h.smul (-(2 * b ^ 2 / Real.sqrt 3))).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp
  · have h2 : 2 * b - 1 ≠ 0 := by
      rcases lt_abs.1 hb with h1 | h1 <;> intro h0 <;> linarith
    have e : Real.sqrt 3 * -(1 / b) / (2 + -(1 / b)) = -(Real.sqrt 3 / (2 * b - 1)) := by
      have e1 : 2 + -(1 / b) = (2 * b - 1) / b := by
        field_simp
        ring
      rw [e1]
      field_simp
    rw [e, Real.arctan_neg]
    linear_combination (-(b ^ 2 * Real.arctan (Real.sqrt 3 / (2 * b - 1)))) * three_div_sqrt3

/-! ## 2. Formulas (95), (96): `arctan (1 / (2b ∓ 1))` -/

/-- **Formula (95)** of the Compendium (page 27), real parameter:
`b⁷ arctan (1/(2b - 1)) = (1/16) P(1, 16b⁸, 8, (8b⁶, 8b⁵, 4b⁴, 0, -2b², -2b, -1, 0))` for
`2b² > 1`. -/
theorem formula_95_real {b : ℝ} (hb : 1 < 2 * b ^ 2) :
    BaileyFormulaReal (b ^ 7 * Real.arctan (1 / (2 * b - 1))) (1 / 16) (16 * b ^ 8) 8
      ![8 * b ^ 6, 8 * b ^ 5, 4 * b ^ 4, 0, -2 * b ^ 2, -2 * b, -1, 0] := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    norm_num at hb
  have h := hasBaileyValueReal_gauss_im (v := 1 / (2 * b)) (β := 16 * b ^ 8)
    (by field_simp; ring) (param_gauss hb)
  refine ((h.smul (16 * b ^ 7)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp <;> ring
  · have h2 : 2 * b - 1 ≠ 0 := by
      intro h0
      have e1 : b = 1 / 2 := by linarith
      rw [e1] at hb
      norm_num at hb
    have e : 1 / (2 * b) / (1 - 1 / (2 * b)) = 1 / (2 * b - 1) := by
      have e1 : 1 - 1 / (2 * b) = (2 * b - 1) / (2 * b) := by field_simp
      rw [e1]
      field_simp
    rw [e]
    ring

/-- **Formula (96)** of the Compendium (page 27), real parameter:
`b⁷ arctan (1/(2b + 1)) = (1/16) P(1, 16b⁸, 8, (8b⁶, -8b⁵, 4b⁴, 0, -2b², 2b, -1, 0))` for
`2b² > 1`. -/
theorem formula_96_real {b : ℝ} (hb : 1 < 2 * b ^ 2) :
    BaileyFormulaReal (b ^ 7 * Real.arctan (1 / (2 * b + 1))) (1 / 16) (16 * b ^ 8) 8
      ![8 * b ^ 6, -8 * b ^ 5, 4 * b ^ 4, 0, -2 * b ^ 2, 2 * b, -1, 0] := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    norm_num at hb
  have h := hasBaileyValueReal_gauss_im (v := -(1 / (2 * b))) (β := 16 * b ^ 8)
    (by field_simp; ring) (by rw [neg_sq]; exact param_gauss hb)
  refine ((h.smul (-(16 * b ^ 7))).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp <;> ring
  · have h2 : 2 * b + 1 ≠ 0 := by
      intro h0
      have e1 : b = -(1 / 2) := by linarith
      rw [e1] at hb
      norm_num at hb
    have e : -(1 / (2 * b)) / (1 - -(1 / (2 * b))) = -(1 / (2 * b + 1)) := by
      have e1 : 1 - -(1 / (2 * b)) = (2 * b + 1) / (2 * b) := by
        field_simp
        ring
      rw [e1]
      field_simp
    rw [e, Real.arctan_neg]
    ring

/-! ## 3. Formulas (98), (99): `arctan (1 / (√3 (2b ∓ 1)))` -/

/-- **Formula (98)** of the Compendium (page 27), real parameter:
`9 b⁵ √3 arctan ((1/√3) (1/(2b - 1))) = (1/2) P(1, -27b⁶, 6, (9b⁴, 9b³, 6b², 3b, 1, 0))` for
`3b² > 1`. -/
theorem formula_98_real {b : ℝ} (hb : 1 < 3 * b ^ 2) :
    BaileyFormulaReal
      (9 * b ^ 5 * Real.sqrt 3 * Real.arctan (1 / Real.sqrt 3 * (1 / (2 * b - 1)))) (1 / 2)
      (-27 * b ^ 6) 6 ![9 * b ^ 4, 9 * b ^ 3, 6 * b ^ 2, 3 * b, 1, 0] := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    norm_num at hb
  have hs := sqrt3_ne_zero
  have h := hasBaileyValueReal_eis_im (v := 1 / (3 * b)) (β := -27 * b ^ 6)
    (by field_simp; ring) (param_eis hb)
  refine ((h.smul (54 * b ^ 5 / Real.sqrt 3)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp <;> ring
  · have h2 : 2 * b - 1 ≠ 0 := by
      intro h0
      have e1 : b = 1 / 2 := by linarith
      rw [e1] at hb
      norm_num at hb
    have e : Real.sqrt 3 * (1 / (3 * b)) / (2 - 3 * (1 / (3 * b))) =
        1 / Real.sqrt 3 * (1 / (2 * b - 1)) := by
      have e1 : 2 - 3 * (1 / (3 * b)) = (2 * b - 1) / b := by field_simp
      rw [e1, one_div_sqrt3]
      field_simp
    rw [e]
    linear_combination (-(9 * b ^ 5 * Real.arctan (1 / Real.sqrt 3 * (1 / (2 * b - 1))))) *
      three_div_sqrt3

/-- **Formula (99)** of the Compendium (page 27), real parameter:
`9 b⁵ √3 arctan ((1/√3) (1/(2b + 1))) = (1/2) P(1, -27b⁶, 6, (9b⁴, -9b³, 6b², -3b, 1, 0))` for
`3b² > 1`. -/
theorem formula_99_real {b : ℝ} (hb : 1 < 3 * b ^ 2) :
    BaileyFormulaReal
      (9 * b ^ 5 * Real.sqrt 3 * Real.arctan (1 / Real.sqrt 3 * (1 / (2 * b + 1)))) (1 / 2)
      (-27 * b ^ 6) 6 ![9 * b ^ 4, -9 * b ^ 3, 6 * b ^ 2, -3 * b, 1, 0] := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    norm_num at hb
  have hs := sqrt3_ne_zero
  have h := hasBaileyValueReal_eis_im (v := -(1 / (3 * b))) (β := -27 * b ^ 6)
    (by field_simp; ring) (by rw [neg_sq]; exact param_eis hb)
  refine ((h.smul (-(54 * b ^ 5 / Real.sqrt 3))).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp <;> ring
  · have h2 : 2 * b + 1 ≠ 0 := by
      intro h0
      have e1 : b = -(1 / 2) := by linarith
      rw [e1] at hb
      norm_num at hb
    have e : Real.sqrt 3 * -(1 / (3 * b)) / (2 - 3 * -(1 / (3 * b))) =
        -(1 / Real.sqrt 3 * (1 / (2 * b + 1))) := by
      have e1 : 2 - 3 * -(1 / (3 * b)) = (2 * b + 1) / b := by
        field_simp
        ring
      rw [e1, one_div_sqrt3]
      field_simp
    rw [e, Real.arctan_neg]
    linear_combination (-(9 * b ^ 5 * Real.arctan (1 / Real.sqrt 3 * (1 / (2 * b + 1))))) *
      three_div_sqrt3

/-! ## 4. The same formulas for a natural number `b ≥ 2` -/

/-- **Formula (93)** of the Compendium (page 27), `b ≥ 2` natural:
`b² √3 arctan (√3/(2b - 1)) = (3/2) P(1, -b³, 3, (b, 1, 0))`. -/
theorem formula_93 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormulaInt
      ((b : ℝ) ^ 2 * Real.sqrt 3 * Real.arctan (Real.sqrt 3 / (2 * (b : ℝ) - 1))) (3 / 2)
      (-(b : ℤ) ^ 3) 1 3 ![(b : ℚ), 1, 0] := by
  refine (formula_93_real (one_lt_abs_natCast hb)).to_int (by push_cast; ring) fun i => ?_
  fin_cases i <;> simp

/-- **Formula (94)** of the Compendium (page 27), `b ≥ 2` natural:
`b² √3 arctan (√3/(2b + 1)) = (3/2) P(1, b³, 3, (b, -1, 0))`. -/
theorem formula_94 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormula
      ((b : ℝ) ^ 2 * Real.sqrt 3 * Real.arctan (Real.sqrt 3 / (2 * (b : ℝ) + 1))) (3 / 2)
      b 3 3 ![(b : ℚ), -1, 0] := by
  refine (formula_94_real (one_lt_abs_natCast hb)).to_nat rfl fun i => ?_
  fin_cases i <;> simp

/-- **Formula (95)** of the Compendium (page 27), `b ≥ 2` natural:
`b⁷ arctan (1/(2b - 1)) = (1/16) P(1, 16b⁸, 8, (8b⁶, 8b⁵, 4b⁴, 0, -2b², -2b, -1, 0))`. -/
theorem formula_95 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormula ((b : ℝ) ^ 7 * Real.arctan (1 / (2 * (b : ℝ) - 1))) (1 / 16) (16 * b ^ 8) 1 8
      ![8 * (b : ℚ) ^ 6, 8 * b ^ 5, 4 * b ^ 4, 0, -2 * b ^ 2, -2 * b, -1, 0] := by
  have hb' := one_lt_natCast_of_two_le hb
  refine (formula_95_real (by nlinarith)).to_nat (by push_cast; ring) fun i => ?_
  fin_cases i <;> simp

/-- **Formula (96)** of the Compendium (page 27), `b ≥ 2` natural:
`b⁷ arctan (1/(2b + 1)) = (1/16) P(1, 16b⁸, 8, (8b⁶, -8b⁵, 4b⁴, 0, -2b², 2b, -1, 0))`. -/
theorem formula_96 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormula ((b : ℝ) ^ 7 * Real.arctan (1 / (2 * (b : ℝ) + 1))) (1 / 16) (16 * b ^ 8) 1 8
      ![8 * (b : ℚ) ^ 6, -8 * b ^ 5, 4 * b ^ 4, 0, -2 * b ^ 2, 2 * b, -1, 0] := by
  have hb' := one_lt_natCast_of_two_le hb
  refine (formula_96_real (by nlinarith)).to_nat (by push_cast; ring) fun i => ?_
  fin_cases i <;> simp

/-- **Formula (98)** of the Compendium (page 27), `b ≥ 2` natural:
`9 b⁵ √3 arctan ((1/√3) (1/(2b - 1))) = (1/2) P(1, -27b⁶, 6, (9b⁴, 9b³, 6b², 3b, 1, 0))`. -/
theorem formula_98 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormulaInt
      (9 * (b : ℝ) ^ 5 * Real.sqrt 3 * Real.arctan (1 / Real.sqrt 3 * (1 / (2 * (b : ℝ) - 1))))
      (1 / 2) (-27 * (b : ℤ) ^ 6) 1 6 ![9 * (b : ℚ) ^ 4, 9 * b ^ 3, 6 * b ^ 2, 3 * b, 1, 0] := by
  have hb' := one_lt_natCast_of_two_le hb
  refine (formula_98_real (by nlinarith)).to_int (by push_cast; ring) fun i => ?_
  fin_cases i <;> simp

/-- **Formula (99)** of the Compendium (page 27), `b ≥ 2` natural:
`9 b⁵ √3 arctan ((1/√3) (1/(2b + 1))) = (1/2) P(1, -27b⁶, 6, (9b⁴, -9b³, 6b², -3b, 1, 0))`. -/
theorem formula_99 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormulaInt
      (9 * (b : ℝ) ^ 5 * Real.sqrt 3 * Real.arctan (1 / Real.sqrt 3 * (1 / (2 * (b : ℝ) + 1))))
      (1 / 2) (-27 * (b : ℤ) ^ 6) 1 6
      ![9 * (b : ℚ) ^ 4, -9 * b ^ 3, 6 * b ^ 2, -3 * b, 1, 0] := by
  have hb' := one_lt_natCast_of_two_le hb
  refine (formula_99_real (by nlinarith)).to_int (by push_cast; ring) fun i => ?_
  fin_cases i <;> simp

end Compendium

end PiFormula
