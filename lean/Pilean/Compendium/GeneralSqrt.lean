module

public import Pilean.Compendium.GeneralCore

/-!
# Bailey's Compendium, general bases: the formulas with `√b`

Formulas (92), (97), (100), (103), (108), (110) of the Compendium (pages 27 and 28), as
printed. For each formula `N` there are two theorems: `formula_N_real`, for every real `b > 1`,
in the form `BaileyFormulaReal`; and `formula_N`, for a natural number `b ≥ 2`, in the form
`BaileyFormula` / `BaileyFormulaInt` of the other formulas of the Compendium. The paper states
no range for `b`; the series of these six formulas have the ratio `1/b`, `1/b²`, … and the
left sides contain `√b` and `b - 1` or `√b - 1` in a denominator, so `b > 1` is the natural
range.

* (103) and (92) are the series of `log ((1 + x)/(1 - x))` and of `arctan x` at `x = 1/√b`
  (`hasSum_inv_odd`, `hasSum_alt_inv_odd`).
* (97) and (108) are the series of `GeneralCore.lean` for `1 + i` at `v` and at `-v`, with
  `v = √b √2 / (2b)` (so `2 b v² = 1`), subtracted: the terms with an even index cancel.
* (100) and (110) are the series for `(3 + i√3)/2` at `v` and at `-v`, with
  `v = √b √3 / (3b)` (so `3 b v² = 1`), subtracted.
-/

@[expose] public section

namespace PiFormula

namespace Compendium

open BaseB

/-! ## 0. The parameters `v = √b √2 / (2b)` and `v = √b √3 / (3b)` -/

theorem sqrt2_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- The number `v = √b √2 / (2b) = 1/(√2 √b)`. -/
theorem exists_param_sqrt2 {b : ℝ} (hb : 1 < b) :
    ∃ v : ℝ, 0 < v ∧ 2 * v ^ 2 < 1 ∧ 2 * b * v ^ 2 = 1 ∧
      2 * b * v = Real.sqrt b * Real.sqrt 2 := by
  have hb0 : 0 < b := by linarith
  have h2 : 2 * b * (Real.sqrt b * Real.sqrt 2 / (2 * b)) ^ 2 = 1 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hb0.le, Real.sq_sqrt (by norm_num)]
    field_simp
  refine ⟨Real.sqrt b * Real.sqrt 2 / (2 * b), by positivity, ?_, h2, by field_simp⟩
  have e : 2 * (Real.sqrt b * Real.sqrt 2 / (2 * b)) ^ 2 = 1 / b := by
    rw [eq_div_iff hb0.ne']
    linear_combination h2
  rw [e, div_lt_one hb0]
  exact hb

/-- The number `v = √b √3 / (3b) = 1/(√3 √b)`. -/
theorem exists_param_sqrt3 {b : ℝ} (hb : 1 < b) :
    ∃ v : ℝ, 0 < v ∧ 3 * v ^ 2 < 1 ∧ 3 * b * v ^ 2 = 1 ∧
      3 * b * v = Real.sqrt b * Real.sqrt 3 ∧ Real.sqrt 3 * b * v = Real.sqrt b := by
  have hb0 : 0 < b := by linarith
  have h2 : 3 * b * (Real.sqrt b * Real.sqrt 3 / (3 * b)) ^ 2 = 1 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hb0.le, Real.sq_sqrt (by norm_num)]
    field_simp
  have h3 : Real.sqrt 3 * b * (Real.sqrt b * Real.sqrt 3 / (3 * b)) = Real.sqrt b := by
    field_simp
    linear_combination Base3.sqrt3_mul_self
  refine ⟨Real.sqrt b * Real.sqrt 3 / (3 * b), by positivity, ?_, h2, by field_simp, h3⟩
  have e : 3 * (Real.sqrt b * Real.sqrt 3 / (3 * b)) ^ 2 = 1 / b := by
    rw [eq_div_iff hb0.ne']
    linear_combination h2
  rw [e, div_lt_one hb0]
  exact hb

theorem one_lt_sqrt {b : ℝ} (hb : 1 < b) : 1 < Real.sqrt b := by
  rw [Real.lt_sqrt (by norm_num)]
  simpa using hb

/-! ## 1. Formulas (103) and (92) -/

/-- **Formula (103)** of the Compendium (page 27), real parameter:
`√b log ((√b + 1)/(√b - 1)) = 2 P(1, b, 2, (1, 0))` for `b > 1`. -/
theorem formula_103_real {b : ℝ} (hb : 1 < b) :
    BaileyFormulaReal (Real.sqrt b * Real.log ((Real.sqrt b + 1) / (Real.sqrt b - 1))) 2 b 2
      ![1, 0] := by
  have hs1 := one_lt_sqrt hb
  have hs0 : 0 < Real.sqrt b := by linarith
  have hv : HasBaileyValueReal b 2 ![1, 0] (Real.sqrt b / 2 *
      (Real.log (1 + 1 / Real.sqrt b) - Real.log (1 - 1 / Real.sqrt b))) := by
    refine (hasSum_inv_odd hb).congr_fun fun j => ?_
    simp [baileyBlockReal, Fin.sum_univ_two]
  refine hv.formula ?_
  have h1 : 0 < 1 + 1 / Real.sqrt b := by positivity
  have h2 : 0 < 1 - 1 / Real.sqrt b := by
    rw [sub_pos, div_lt_one hs0]
    exact hs1
  have hm : Real.sqrt b - 1 ≠ 0 := by
    have : 0 < Real.sqrt b - 1 := by linarith
    exact this.ne'
  have e : (Real.sqrt b + 1) / (Real.sqrt b - 1) =
      (1 + 1 / Real.sqrt b) / (1 - 1 / Real.sqrt b) := by
    rw [div_eq_div_iff hm h2.ne']
    field_simp
  rw [e, Real.log_div h1.ne' h2.ne']
  ring

/-- **Formula (92)** of the Compendium (page 27), real parameter:
`√b arctan (1/√b) = (1/b) P(1, b², 4, (b, 0, -1, 0))` for `b > 1`. -/
theorem formula_92_real {b : ℝ} (hb : 1 < b) :
    BaileyFormulaReal (Real.sqrt b * Real.arctan (1 / Real.sqrt b)) (1 / b) (b ^ 2) 4
      ![b, 0, -1, 0] := by
  have hb0 : b ≠ 0 := by
    have : 0 < b := by linarith
    exact this.ne'
  have h := (hasSum_group two_pos (hasSum_alt_inv_odd hb)).mul_left b
  have hv : HasBaileyValueReal (b ^ 2) 4 ![b, 0, -1, 0]
      (b * (Real.sqrt b * Real.arctan (1 / Real.sqrt b))) := by
    refine h.congr_fun fun j => ?_
    have s0 : (-1 : ℝ) ^ (2 * j + 0) = 1 := Even.neg_one_pow ⟨j, by ring⟩
    have s1 : (-1 : ℝ) ^ (2 * j + 1) = -1 := Odd.neg_one_pow ⟨j, rfl⟩
    have h1 : (4 * (j : ℝ) + 1) ≠ 0 := by positivity
    have h3 : (4 * (j : ℝ) + 3) ≠ 0 := by positivity
    rw [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, s0, s1]
    simp only [baileyBlockReal, Fin.sum_univ_four]
    simp
    field_simp
    ring
  refine hv.formula ?_
  field_simp

/-! ## 2. Formulas (97) and (108): `√2 √b` -/

/-- **Formula (97)** of the Compendium (page 27), real parameter:
`b³ √b √2 arctan ((√b/(b - 1)) √2) = 2 P(1, b⁴, 8, (b³, 0, b², 0, -b, 0, -1, 0))` for
`b > 1`. -/
theorem formula_97_real {b : ℝ} (hb : 1 < b) :
    BaileyFormulaReal
      (b ^ 3 * Real.sqrt b * Real.sqrt 2 * Real.arctan (Real.sqrt b / (b - 1) * Real.sqrt 2)) 2
      (b ^ 4) 8 ![b ^ 3, 0, b ^ 2, 0, -b, 0, -1, 0] := by
  obtain ⟨v, hv0, hlt, hv2, hv'⟩ := exists_param_sqrt2 hb
  have hb0 : b ≠ 0 := by
    have : 0 < b := by linarith
    exact this.ne'
  have hβ : v ^ 8 * 16 * b ^ 4 = 1 := by
    have e : v ^ 8 * 16 * b ^ 4 = (2 * b * v ^ 2) ^ 4 := by ring
    rw [e, hv2, one_pow]
  have hβ' : (-v) ^ 8 * 16 * b ^ 4 = 1 := by
    have e : (-v) ^ 8 = v ^ 8 := by ring
    rw [e, hβ]
  have h1 := hasBaileyValueReal_gauss_im (v := v) (β := b ^ 4) hβ hlt
  have h2 := hasBaileyValueReal_gauss_im (v := -v) (β := b ^ 4) hβ'
    (by rw [neg_sq]; exact hlt)
  refine (((h1.sub h2).smul (b ^ 4 * v)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp [-zero_eq_mul, -mul_eq_zero] <;> try ring1
    · linear_combination (-b ^ 3) * hv2
    · linear_combination (-b ^ 2 * (2 * b * v ^ 2 + 1)) * hv2
    · linear_combination (b * ((2 * b * v ^ 2) ^ 2 + 2 * b * v ^ 2 + 1)) * hv2
    · linear_combination ((2 * b * v ^ 2) ^ 3 + (2 * b * v ^ 2) ^ 2 + 2 * b * v ^ 2 + 1) * hv2
  · have hv1 : v < 1 := by nlinarith
    have hm : 1 - v ≠ 0 := by linarith
    have hp : 1 + v ≠ 0 := by linarith
    have hb1 : b - 1 ≠ 0 := by linarith
    have h12 : 1 - 2 * v ^ 2 ≠ 0 := by linarith
    have hx : v / (1 - v) + v / (1 + v) = 2 * v / ((1 - v) * (1 + v)) := by
      field_simp
      ring
    have hxy : 1 - v / (1 - v) * (v / (1 + v)) = (1 - 2 * v ^ 2) / ((1 - v) * (1 + v)) := by
      field_simp
      ring
    have hlt1 : v / (1 - v) * (v / (1 + v)) < 1 := by
      have hpos : 0 < (1 - 2 * v ^ 2) / ((1 - v) * (1 + v)) :=
        div_pos (by linarith) (mul_pos (by linarith) (by linarith))
      linarith [hxy]
    have hsum : Real.arctan (v / (1 - v)) + Real.arctan (v / (1 + v)) =
        Real.arctan (Real.sqrt b / (b - 1) * Real.sqrt 2) := by
      rw [Real.arctan_add hlt1, hx, hxy, div_div_div_cancel_right₀ (mul_ne_zero hm hp),
        div_mul_eq_mul_div]
      congr 1
      rw [div_eq_div_iff h12 hb1]
      linear_combination (2 * v) * hv2 + (1 - 2 * v ^ 2) * hv'
    have e1 : -v / (1 - -v) = -(v / (1 + v)) := by rw [sub_neg_eq_add, neg_div]
    rw [e1, Real.arctan_neg, sub_neg_eq_add, hsum]
    linear_combination (-(b ^ 3 * Real.arctan (Real.sqrt b / (b - 1) * Real.sqrt 2))) * hv'

/-- **Formula (108)** of the Compendium (page 28), real parameter:
`(b √b/√2) log ((b + √2 √b + 1)/(b - √2 √b + 1)) = 2 P(1, -b², 4, (b, 0, -1, 0))` for
`b > 1`. -/
theorem formula_108_real {b : ℝ} (hb : 1 < b) :
    BaileyFormulaReal
      (b * Real.sqrt b / Real.sqrt 2 * Real.log ((b + Real.sqrt 2 * Real.sqrt b + 1) /
        (b - Real.sqrt 2 * Real.sqrt b + 1))) 2
      (-b ^ 2) 4 ![b, 0, -1, 0] := by
  obtain ⟨v, hv0, hlt, hv2, hv'⟩ := exists_param_sqrt2 hb
  have hb0 : b ≠ 0 := by
    have : 0 < b := by linarith
    exact this.ne'
  have hr0 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hβ : v ^ 4 * (-4) * (-b ^ 2) = 1 := by
    have e : v ^ 4 * (-4) * (-b ^ 2) = (2 * b * v ^ 2) ^ 2 := by ring
    rw [e, hv2, one_pow]
  have hβ' : (-v) ^ 4 * (-4) * (-b ^ 2) = 1 := by
    have e : (-v) ^ 4 = v ^ 4 := by ring
    rw [e, hβ]
  have h1 := hasBaileyValueReal_gauss_re (v := v) (β := -b ^ 2) hβ hlt
  have h2 := hasBaileyValueReal_gauss_re (v := -v) (β := -b ^ 2) hβ'
    (by rw [neg_sq]; exact hlt)
  refine (((h1.sub h2).smul (b ^ 2 * v)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp [-zero_eq_mul, -mul_eq_zero] <;> try ring1
    · linear_combination (-b) * hv2
    · linear_combination (2 * b * v ^ 2 + 1) * hv2
  · have hP : 0 < 1 + 2 * v + 2 * v ^ 2 := by positivity
    have hM : 0 < 1 - 2 * v + 2 * v ^ 2 := by nlinarith [sq_nonneg (1 - v), sq_nonneg v]
    have hnum : b + Real.sqrt 2 * Real.sqrt b + 1 = b * (1 + 2 * v + 2 * v ^ 2) := by
      linear_combination -hv' - hv2
    have hden : b - Real.sqrt 2 * Real.sqrt b + 1 = b * (1 - 2 * v + 2 * v ^ 2) := by
      linear_combination hv' - hv2
    have hκ : b * Real.sqrt b / Real.sqrt 2 = b ^ 2 * v := by
      rw [div_eq_iff hr0]
      linear_combination (-(b * Real.sqrt b / 2)) * sqrt2_mul_self +
        (-(b * Real.sqrt 2 / 2)) * hv'
    have e : 1 - 2 * -v + 2 * (-v) ^ 2 = 1 + 2 * v + 2 * v ^ 2 := by ring
    rw [hκ, hnum, hden, mul_div_mul_left _ _ hb0, Real.log_div hP.ne' hM.ne', e]
    ring

/-! ## 3. Formulas (100) and (110): `√3 √b` -/

/-- **Formula (100)** of the Compendium (page 27), real parameter:
`b² √b arctan (√b/(b - 1)) = P(1, -b³, 6, (b², 0, 2b, 0, 1, 0))` for `b > 1`. (The closing
parenthesis of `P(…)` is missing in the print.) -/
theorem formula_100_real {b : ℝ} (hb : 1 < b) :
    BaileyFormulaReal (b ^ 2 * Real.sqrt b * Real.arctan (Real.sqrt b / (b - 1))) 1
      (-b ^ 3) 6 ![b ^ 2, 0, 2 * b, 0, 1, 0] := by
  obtain ⟨v, hv0, hlt, hv2, -, hv3⟩ := exists_param_sqrt3 hb
  have hb0 : b ≠ 0 := by
    have : 0 < b := by linarith
    exact this.ne'
  have h3 := Base3.sqrt3_mul_self
  have hβ : v ^ 6 * (-27) * (-b ^ 3) = 1 := by
    have e : v ^ 6 * (-27) * (-b ^ 3) = (3 * b * v ^ 2) ^ 3 := by ring
    rw [e, hv2, one_pow]
  have hβ' : (-v) ^ 6 * (-27) * (-b ^ 3) = 1 := by
    have e : (-v) ^ 6 = v ^ 6 := by ring
    rw [e, hβ]
  have h1 := hasBaileyValueReal_eis_im (v := v) (β := -b ^ 3) hβ hlt
  have h2 := hasBaileyValueReal_eis_im (v := -v) (β := -b ^ 3) hβ'
    (by rw [neg_sq]; exact hlt)
  refine (((h1.sub h2).smul (Real.sqrt 3 * b ^ 3 * v)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp [-zero_eq_mul, -mul_eq_zero] <;> try ring1
    · linear_combination (-b ^ 2) * hv2 + (-(b ^ 3 * v ^ 2)) * h3
    · linear_combination (-2 * b * (3 * b * v ^ 2 + 1)) * hv2 + (-(6 * b ^ 3 * v ^ 4)) * h3
    · linear_combination (-((3 * b * v ^ 2) ^ 2 + 3 * b * v ^ 2 + 1)) * hv2 +
        (-(9 * b ^ 3 * v ^ 6)) * h3
  · have hv1 : 3 * v < 2 := by nlinarith
    have hm : 2 - 3 * v ≠ 0 := by linarith
    have hp : 2 + 3 * v ≠ 0 := by linarith
    have hb1 : b - 1 ≠ 0 := by linarith
    have h12 : 4 - 12 * v ^ 2 ≠ 0 := by linarith
    have hx : Real.sqrt 3 * v / (2 - 3 * v) + Real.sqrt 3 * v / (2 + 3 * v) =
        4 * Real.sqrt 3 * v / ((2 - 3 * v) * (2 + 3 * v)) := by
      rw [div_add_div _ _ hm hp]
      congr 1
      ring
    have hprod : Real.sqrt 3 * v / (2 - 3 * v) * (Real.sqrt 3 * v / (2 + 3 * v)) =
        3 * v ^ 2 / ((2 - 3 * v) * (2 + 3 * v)) := by
      rw [div_mul_div_comm]
      congr 1
      linear_combination (v ^ 2) * h3
    have hxy : 1 - Real.sqrt 3 * v / (2 - 3 * v) * (Real.sqrt 3 * v / (2 + 3 * v)) =
        (4 - 12 * v ^ 2) / ((2 - 3 * v) * (2 + 3 * v)) := by
      rw [hprod, eq_div_iff (mul_ne_zero hm hp), sub_mul, div_mul_cancel₀ _ (mul_ne_zero hm hp)]
      ring
    have hlt1 : Real.sqrt 3 * v / (2 - 3 * v) * (Real.sqrt 3 * v / (2 + 3 * v)) < 1 := by
      have hpos : 0 < (4 - 12 * v ^ 2) / ((2 - 3 * v) * (2 + 3 * v)) :=
        div_pos (by linarith) (mul_pos (by linarith) (by linarith))
      linarith [hxy]
    have hsum : Real.arctan (Real.sqrt 3 * v / (2 - 3 * v)) +
        Real.arctan (Real.sqrt 3 * v / (2 + 3 * v)) = Real.arctan (Real.sqrt b / (b - 1)) := by
      rw [Real.arctan_add hlt1, hx, hxy, div_div_div_cancel_right₀ (mul_ne_zero hm hp)]
      congr 1
      rw [div_eq_div_iff h12 hb1]
      linear_combination (4 * Real.sqrt 3 * v) * hv2 + (4 - 12 * v ^ 2) * hv3
    have e1 : Real.sqrt 3 * -v / (2 - 3 * -v) = -(Real.sqrt 3 * v / (2 + 3 * v)) := by
      rw [mul_neg, mul_neg, sub_neg_eq_add, neg_div]
    rw [e1, Real.arctan_neg, sub_neg_eq_add, hsum]
    linear_combination (-(b ^ 2 * Real.arctan (Real.sqrt b / (b - 1)))) * hv3

/-- **Formula (110)** of the Compendium (page 28), real parameter:
`(b² √b/√3) log ((b + √3 √b + 1)/(b - √3 √b + 1)) = 2 P(1, -b³, 6, (b², 0, 0, 0, -1, 0))` for
`b > 1`. -/
theorem formula_110_real {b : ℝ} (hb : 1 < b) :
    BaileyFormulaReal
      (b ^ 2 * Real.sqrt b / Real.sqrt 3 * Real.log ((b + Real.sqrt 3 * Real.sqrt b + 1) /
        (b - Real.sqrt 3 * Real.sqrt b + 1))) 2
      (-b ^ 3) 6 ![b ^ 2, 0, 0, 0, -1, 0] := by
  obtain ⟨v, hv0, hlt, hv2, hv', hv3⟩ := exists_param_sqrt3 hb
  have hb0 : b ≠ 0 := by
    have : 0 < b := by linarith
    exact this.ne'
  have hs : Real.sqrt 3 ≠ 0 := Base3.sqrt3_pos.ne'
  have hβ : v ^ 6 * (-27) * (-b ^ 3) = 1 := by
    have e : v ^ 6 * (-27) * (-b ^ 3) = (3 * b * v ^ 2) ^ 3 := by ring
    rw [e, hv2, one_pow]
  have hβ' : (-v) ^ 6 * (-27) * (-b ^ 3) = 1 := by
    have e : (-v) ^ 6 = v ^ 6 := by ring
    rw [e, hβ]
  have h1 := hasBaileyValueReal_eis_re (v := v) (β := -b ^ 3) hβ hlt
  have h2 := hasBaileyValueReal_eis_re (v := -v) (β := -b ^ 3) hβ'
    (by rw [neg_sq]; exact hlt)
  refine (((h1.sub h2).smul (b ^ 3 * v)).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp [-zero_eq_mul, -mul_eq_zero] <;> try ring1
    · linear_combination (-b ^ 2) * hv2
    · linear_combination ((3 * b * v ^ 2) ^ 2 + 3 * b * v ^ 2 + 1) * hv2
  · have hP : 0 < 1 + 3 * v + 3 * v ^ 2 := by positivity
    have hM : 0 < 1 - 3 * v + 3 * v ^ 2 := by nlinarith [sq_nonneg (1 - 2 * v), sq_nonneg v]
    have hnum : b + Real.sqrt 3 * Real.sqrt b + 1 = b * (1 + 3 * v + 3 * v ^ 2) := by
      linear_combination -hv' - hv2
    have hden : b - Real.sqrt 3 * Real.sqrt b + 1 = b * (1 - 3 * v + 3 * v ^ 2) := by
      linear_combination hv' - hv2
    have hκ : b ^ 2 * Real.sqrt b / Real.sqrt 3 = b ^ 3 * v := by
      rw [div_eq_iff hs]
      linear_combination (-b ^ 2) * hv3
    have e : 1 - 3 * -v + 3 * (-v) ^ 2 = 1 + 3 * v + 3 * v ^ 2 := by ring
    rw [hκ, hnum, hden, mul_div_mul_left _ _ hb0, Real.log_div hP.ne' hM.ne', e]
    ring

/-! ## 4. The same formulas for a natural number `b ≥ 2` -/

/-- **Formula (92)** of the Compendium (page 27), `b ≥ 2` natural:
`√b arctan (1/√b) = (1/b) P(1, b², 4, (b, 0, -1, 0))`. -/
theorem formula_92 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormula (Real.sqrt b * Real.arctan (1 / Real.sqrt b)) (1 / (b : ℝ)) b 2 4
      ![(b : ℚ), 0, -1, 0] := by
  refine (formula_92_real (one_lt_natCast_of_two_le hb)).to_nat rfl fun i => ?_
  fin_cases i <;> simp

/-- **Formula (97)** of the Compendium (page 27), `b ≥ 2` natural:
`b³ √b √2 arctan ((√b/(b - 1)) √2) = 2 P(1, b⁴, 8, (b³, 0, b², 0, -b, 0, -1, 0))`. -/
theorem formula_97 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormula
      ((b : ℝ) ^ 3 * Real.sqrt b * Real.sqrt 2 *
        Real.arctan (Real.sqrt b / ((b : ℝ) - 1) * Real.sqrt 2)) 2
      b 4 8 ![(b : ℚ) ^ 3, 0, b ^ 2, 0, -b, 0, -1, 0] := by
  refine (formula_97_real (one_lt_natCast_of_two_le hb)).to_nat rfl fun i => ?_
  fin_cases i <;> simp

/-- **Formula (100)** of the Compendium (page 27), `b ≥ 2` natural:
`b² √b arctan (√b/(b - 1)) = P(1, -b³, 6, (b², 0, 2b, 0, 1, 0))`. -/
theorem formula_100 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormulaInt
      ((b : ℝ) ^ 2 * Real.sqrt b * Real.arctan (Real.sqrt b / ((b : ℝ) - 1))) 1
      (-(b : ℤ) ^ 3) 1 6 ![(b : ℚ) ^ 2, 0, 2 * b, 0, 1, 0] := by
  refine (formula_100_real (one_lt_natCast_of_two_le hb)).to_int (by push_cast; ring)
    fun i => ?_
  fin_cases i <;> simp

/-- **Formula (103)** of the Compendium (page 27), `b ≥ 2` natural:
`√b log ((√b + 1)/(√b - 1)) = 2 P(1, b, 2, (1, 0))`. -/
theorem formula_103 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormula
      (Real.sqrt b * Real.log ((Real.sqrt b + 1) / (Real.sqrt b - 1))) 2 b 1 2 ![1, 0] := by
  refine (formula_103_real (one_lt_natCast_of_two_le hb)).to_nat (pow_one _).symm fun i => ?_
  fin_cases i <;> simp

/-- **Formula (108)** of the Compendium (page 28), `b ≥ 2` natural:
`(b √b/√2) log ((b + √2 √b + 1)/(b - √2 √b + 1)) = 2 P(1, -b², 4, (b, 0, -1, 0))`. -/
theorem formula_108 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormulaInt
      ((b : ℝ) * Real.sqrt b / Real.sqrt 2 *
        Real.log (((b : ℝ) + Real.sqrt 2 * Real.sqrt b + 1) /
          ((b : ℝ) - Real.sqrt 2 * Real.sqrt b + 1))) 2
      (-(b : ℤ) ^ 2) 1 4 ![(b : ℚ), 0, -1, 0] := by
  refine (formula_108_real (one_lt_natCast_of_two_le hb)).to_int (by push_cast; ring)
    fun i => ?_
  fin_cases i <;> simp

/-- **Formula (110)** of the Compendium (page 28), `b ≥ 2` natural:
`(b² √b/√3) log ((b + √3 √b + 1)/(b - √3 √b + 1)) = 2 P(1, -b³, 6, (b², 0, 0, 0, -1, 0))`. -/
theorem formula_110 {b : ℕ} (hb : 2 ≤ b) :
    BaileyFormulaInt
      ((b : ℝ) ^ 2 * Real.sqrt b / Real.sqrt 3 *
        Real.log (((b : ℝ) + Real.sqrt 3 * Real.sqrt b + 1) /
          ((b : ℝ) - Real.sqrt 3 * Real.sqrt b + 1))) 2
      (-(b : ℤ) ^ 3) 1 6 ![(b : ℚ) ^ 2, 0, 0, 0, -1, 0] := by
  refine (formula_110_real (one_lt_natCast_of_two_le hb)).to_int (by push_cast; ring)
    fun i => ?_
  fin_cases i <;> simp

end Compendium

end PiFormula
