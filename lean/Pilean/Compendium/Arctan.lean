import Pilean.Compendium.Base2Pi
import Pilean.Compendium.Base2Zero
import Pilean.Base3.PiValue

/-!
# Bailey's Compendium: arctangents and square roots in degree 1

Formulas of the Compendium whose value is not an algebraic multiple of `π` and not a logarithm
of a rational number, stated as printed.

* `formula_68`: `√3 arctan (√3/7)` (base 27, length 3), from the imaginary part of the series
  of `-log (1 - ω/3)` for the cube root of unity `ω = (-1 + i√3)/2` (`hasSum_im_w3`).
* `formula_23`, `formula_86`: `√2 log (1 + √2)` (base 16) and `√5 log φ` (base 5), from the
  series of `log ((1 + x) / (1 - x))` at `x = 1/√2`, `1/√5` (`hasSum_inv_odd`).
* `formula_24`: `√2 arctan (1/√2)` (base 16), from the series of the arctangent at `x = 1/√2`
  (`hasSum_alt_inv_odd`).
* `formula_10`, `formula_25`, `formula_26`, `formula_27`: `arctan 2`, `arctan φ`,
  `arctan φ^3`, `arctan φ^5` (base 16, length 8). Each vector is the vector of formula (17),
  of value `4π`, plus a multiple of the vector `(0, 1, 0, 0, 0, -1/4, 0, 0)` of the series of
  `arctan (1/2)` (`hasBaileyValue_arctan`); the closed forms are `arctan 2 = π/2 - α`,
  `arctan φ = π/4 + α/2`, `arctan φ^3 = π/2 - α/2`, `arctan φ^5 = π/4 + 3α/2` with
  `α = arctan (1/2)`.
* `formula_28`: `arctan φ^7` (base `2^12`, length 24). The vector is `256 V - 2048 U₁ -
  (4096/3) U₃`, where `V` is the vector of formula (17) and `U₁` the vector of `arctan (1/2)`,
  both regrouped to length 24 (`HasBaileyValue.regroup`), and `U₃` is the vector of
  `arctan (1/8)`; `arctan φ^7 = 3π/4 - 3α/2 - arctan (1/8)`.
* `formula_13`: `arctan (4/5)` (base `2^20`, length 40). The vector is `16384 V - 262144 U₁ +
  131072 U₅ + (1/4) R₁₁₉ + (3/4) R₁₂₀ + (5/4) R₁₂₁` with `V`, `U₁` regrouped to length 40,
  `U₅` the vector of `arctan (1/32)` and the zero relations (119), (120), (121);
  `arctan (4/5) = π/2 - 2α + arctan (1/32)`.

The equalities between vectors are checked by `decide +kernel`. Here `φ` is
`Real.goldenRatio`.
-/

namespace PiFormula

namespace Compendium

open BaseB

/-! ## 1. Two series with square roots -/

/-- `∑_{j ≥ 0} c^(-j) / (2j + 1) = (√c / 2) (log (1 + 1/√c) - log (1 - 1/√c))` for `c > 1`. -/
theorem hasSum_inv_odd {c : ℝ} (hc : 1 < c) :
    HasSum (fun j : ℕ => 1 / c ^ j / (2 * (j : ℝ) + 1))
      (Real.sqrt c / 2 * (Real.log (1 + 1 / Real.sqrt c) - Real.log (1 - 1 / Real.sqrt c))) := by
  have hc0 : 0 < c := by linarith
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  have hs1 : 1 < Real.sqrt c := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using hc
  have hx : |1 / Real.sqrt c| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hs]
    exact hs1
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one hx).mul_left (Real.sqrt c / 2)
  refine h.congr_fun fun k => ?_
  have e : (1 / Real.sqrt c) ^ (2 * k + 1) = 1 / Real.sqrt c * (1 / c ^ k) := by
    rw [pow_succ, pow_mul, div_pow, one_pow, Real.sq_sqrt hc0.le, div_pow, one_pow]
    ring
  rw [e]
  field_simp

/-- `∑_{j ≥ 0} (-1)^j c^(-j) / (2j + 1) = √c arctan (1/√c)` for `c > 1`. -/
theorem hasSum_alt_inv_odd {c : ℝ} (hc : 1 < c) :
    HasSum (fun j : ℕ => (-1) ^ j / c ^ j / (2 * (j : ℝ) + 1))
      (Real.sqrt c * Real.arctan (1 / Real.sqrt c)) := by
  have hc0 : 0 < c := by linarith
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  have hs1 : 1 < Real.sqrt c := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using hc
  have hx : ‖1 / Real.sqrt c‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one hs]
    exact hs1
  have h := (Real.hasSum_arctan hx).mul_left (Real.sqrt c)
  refine h.congr_fun fun k => ?_
  have e : (1 / Real.sqrt c) ^ (2 * k + 1) = 1 / Real.sqrt c * (1 / c ^ k) := by
    rw [pow_succ, pow_mul, div_pow, one_pow, Real.sq_sqrt hc0.le, div_pow, one_pow]
    ring
  rw [e]
  push_cast
  field_simp

/-- `log (1 + 1/√c) - log (1 - 1/√c) = 2 log y` when `(1 + 1/√c) = y² (1 - 1/√c)`. -/
theorem log_sub_log_inv_sqrt {c : ℝ} (hc : 1 < c) {y : ℝ} (hy : 0 < y)
    (h : 1 + 1 / Real.sqrt c = y ^ 2 * (1 - 1 / Real.sqrt c)) :
    Real.log (1 + 1 / Real.sqrt c) - Real.log (1 - 1 / Real.sqrt c) = 2 * Real.log y := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 (by linarith)
  have hs1 : 1 < Real.sqrt c := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using hc
  have hpos : 0 < 1 - 1 / Real.sqrt c := by
    rw [sub_pos, div_lt_one hs]
    exact hs1
  rw [h, Real.log_mul (by positivity) hpos.ne', Real.log_pow]
  push_cast
  ring

/-! ## 2. Formulas (23), (24), (86) -/

/-- **Formula (86)** of the Compendium (page 26): `√5 log φ = P(1, 5, 2, (1, 0))`. -/
theorem formula_86 : BaileyFormula (Real.sqrt 5 * Real.log Real.goldenRatio) 1 5 1 2
    ![1, 0] := by
  have hb : HasBaileyValue 5 1 2 ![1, 0] (Real.sqrt 5 / 2 *
      (Real.log (1 + 1 / Real.sqrt 5) - Real.log (1 - 1 / Real.sqrt 5))) := by
    refine (hasSum_inv_odd (c := 5) (by norm_num)).congr_fun fun j => ?_
    simp [BaseB.baileyBlock, Fin.sum_univ_two]
  refine hb.formula ?_
  have hs2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hinv : 1 / Real.sqrt 5 = Real.sqrt 5 / 5 := by
    rw [div_eq_div_iff hs.ne' (by norm_num)]
    linear_combination -hs2
  rw [log_sub_log_inv_sqrt (c := 5) (by norm_num) Real.goldenRatio_pos (by
    rw [hinv, Real.goldenRatio]
    linear_combination ((Real.sqrt 5 - 3) / 20) * hs2)]
  ring

/-- **Formula (23)** of the Compendium (page 9):
`√2 log (1 + √2) = (1/8) P(1, 16, 8, (8, 0, 4, 0, 2, 0, 1, 0))`. -/
theorem formula_23 : BaileyFormula (Real.sqrt 2 * Real.log (1 + Real.sqrt 2)) (1 / 8) 16 1 8
    ![8, 0, 4, 0, 2, 0, 1, 0] := by
  have h := (hasSum_group (m := 4) (by norm_num)
    (hasSum_inv_odd (c := 2) (by norm_num))).mul_left 8
  have hb : HasBaileyValue 16 1 8 ![8, 0, 4, 0, 2, 0, 1, 0] (8 * (Real.sqrt 2 / 2 *
      (Real.log (1 + 1 / Real.sqrt 2) - Real.log (1 - 1 / Real.sqrt 2)))) := by
    refine h.congr_fun fun j => ?_
    have e16 : (16 : ℝ) ^ j = 2 ^ (4 * j) := by
      rw [pow_mul]
      norm_num
    simp only [BaseB.baileyBlock, Fin.sum_univ_eight, Fin.sum_univ_four, one_mul]
    simp only [Nat.cast_ofNat, e16]
    simp
    field_simp
    ring
  refine hb.formula ?_
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    rw [div_eq_div_iff hs.ne' (by norm_num)]
    linear_combination -hs2
  rw [log_sub_log_inv_sqrt (c := 2) (by norm_num) (y := 1 + Real.sqrt 2) (by positivity) (by
    rw [hinv]
    linear_combination (Real.sqrt 2 / 2) * hs2)]
  ring

/-- **Formula (24)** of the Compendium (page 9):
`√2 arctan (1/√2) = (1/8) P(1, 16, 8, (8, 0, -4, 0, 2, 0, -1, 0))`. -/
theorem formula_24 :
    BaileyFormula (Real.sqrt 2 * Real.arctan (1 / Real.sqrt 2)) (1 / 8) 16 1 8
    ![8, 0, -4, 0, 2, 0, -1, 0] := by
  have h := (hasSum_group (m := 4) (by norm_num)
    (hasSum_alt_inv_odd (c := 2) (by norm_num))).mul_left 8
  have hb : HasBaileyValue 16 1 8 ![8, 0, -4, 0, 2, 0, -1, 0]
      (8 * (Real.sqrt 2 * Real.arctan (1 / Real.sqrt 2))) := by
    refine h.congr_fun fun j => ?_
    have e16 : (16 : ℝ) ^ j = 2 ^ (4 * j) := by
      rw [pow_mul]
      norm_num
    have s0 : (-1 : ℝ) ^ (4 * j) = 1 := Even.neg_one_pow ⟨2 * j, by ring⟩
    simp only [BaseB.baileyBlock, Fin.sum_univ_eight, Fin.sum_univ_four, one_mul]
    simp only [Nat.cast_ofNat, e16]
    simp [pow_add, s0]
    field_simp
    ring
  refine hb.formula ?_
  ring

/-! ## 3. The series of `arctan (1 / 2^m)` -/

/-- **The series of `arctan (1 / 2^m)`** in the class F:
`arctan (1/2^m) = P(1, 2^(4m), 8m, a)` with `a_(2m) = 2m / 2^m`, `a_(6m) = -2m / 2^(3m)` and
`a_i = 0` otherwise. Block `j` is the sum of the terms `4j + 1` and `4j + 3` of the series
`∑ (-1)^n x^(2n+1) / (2n+1)` at `x = 1/2^m`. -/
theorem hasBaileyValue_arctan {m : ℕ} (hm : 0 < m) :
    HasBaileyValue 2 (4 * m) (8 * m)
      (((2 * m : ℚ) / 2 ^ m) • unitVec (8 * m) (2 * m)
        + (-((2 * m : ℚ) / 2 ^ (3 * m))) • unitVec (8 * m) (6 * m))
      (Real.arctan (1 / 2 ^ m)) := by
  have hy1 : (1 : ℝ) < 2 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
  have hx : ‖(1 / 2 ^ m : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one (by positivity)]
    exact hy1
  refine (hasSum_group two_pos (Real.hasSum_arctan hx)).congr_fun fun j => ?_
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have e1 : ((2 : ℕ) : ℝ) ^ (4 * m * j) = ((2 : ℝ) ^ m) ^ (4 * j) := by
    rw [← pow_mul, Nat.cast_ofNat]
    congr 1
    ring
  have e3 : (2 : ℝ) ^ (3 * m) = ((2 : ℝ) ^ m) ^ 3 := by
    rw [← pow_mul]
    congr 1
    ring
  have s0 : (-1 : ℝ) ^ (2 * j + 0) = 1 := Even.neg_one_pow ⟨j, by ring⟩
  have s1 : (-1 : ℝ) ^ (2 * j + 1) = -1 := Odd.neg_one_pow ⟨j, rfl⟩
  rw [baileyBlock_add, baileyBlock_smul, baileyBlock_smul,
    baileyBlock_unitVec 2 (4 * m) (by omega) (by omega),
    baileyBlock_unitVec 2 (4 * m) (by omega) (by omega), Fin.sum_univ_two, Fin.val_zero,
    Fin.val_one, s0, s1, e1]
  push_cast
  rw [e3, one_div_pow, one_div_pow]
  generalize (2 : ℝ) ^ m = y at hy1
  have hy0 : y ≠ 0 := by positivity
  field_simp
  ring

/-- The vector of formula (17) in base 2: `P(1, 2^4, 8, (8, 8, 4, 0, -2, -2, -1, 0)) = 4π`. -/
theorem hasBaileyValue_pi :
    HasBaileyValue 2 4 8 ![8, 8, 4, 0, -2, -2, -1, 0] (4 * Real.pi) :=
  (HasBaileyValue.to_pow (a := 2) (j := 4) (B := 1) (formula_17.value (by norm_num))).of_eq
    rfl (by ring)

/-- The series of `arctan (1/2)`: `P(1, 2^4, 8, (0, 1, 0, 0, 0, -1/4, 0, 0)) = arctan (1/2)`. -/
theorem hasBaileyValue_arctan_half :
    HasBaileyValue 2 4 8 ![0, 1, 0, 0, 0, -1 / 4, 0, 0] (Real.arctan (1 / 2)) :=
  (hasBaileyValue_arctan (m := 1) one_pos).of_eq (by decide +kernel) (by norm_num)

/-! ## 4. Closed forms -/

/-- `arctan 2 = π/2 - arctan (1/2)`. -/
theorem arctan_two : Real.arctan 2 = Real.pi / 2 - Real.arctan (1 / 2) := by
  rw [← Real.arctan_inv_of_pos (by norm_num)]
  congr 1
  norm_num

/-- For `x > 1` with `2x / (1 - x²) = -r`: `2 arctan x = π - arctan r`. -/
theorem two_mul_arctan_of_eq {x r : ℝ} (hx : 1 < x) (h : 2 * x = -r * (1 - x ^ 2)) :
    2 * Real.arctan x = Real.pi - Real.arctan r := by
  have hne : 1 - x ^ 2 ≠ 0 := ne_of_lt (by nlinarith)
  have e : 2 * x / (1 - x ^ 2) = -r := by
    rw [div_eq_iff hne]
    exact h
  rw [Real.two_mul_arctan_add_pi hx, e, Real.arctan_neg]
  ring

/-- `arctan φ = π/4 + arctan (1/2) / 2`. -/
theorem arctan_goldenRatio :
    Real.arctan Real.goldenRatio = Real.pi / 4 + Real.arctan (1 / 2) / 2 := by
  have h := two_mul_arctan_of_eq (r := 2) Real.one_lt_goldenRatio
    (by linear_combination (-2 : ℝ) * Real.goldenRatio_sq)
  rw [arctan_two] at h
  linarith

/-- `arctan φ^3 = π/2 - arctan (1/2) / 2`. -/
theorem arctan_goldenRatio_pow_three :
    Real.arctan (Real.goldenRatio ^ 3) = Real.pi / 2 - Real.arctan (1 / 2) / 2 := by
  have h := two_mul_arctan_of_eq (x := Real.goldenRatio ^ 3) (r := 1 / 2)
    (one_lt_pow₀ Real.one_lt_goldenRatio (by norm_num))
    (by linear_combination (-Real.goldenRatio ^ 4 / 2 - Real.goldenRatio ^ 3 / 2
      - Real.goldenRatio ^ 2 + Real.goldenRatio / 2 - 1 / 2) * Real.goldenRatio_sq)
  linarith

/-- `arctan (2/11) = π/2 - 3 arctan (1/2)`. -/
theorem arctan_two_elevenths :
    Real.arctan (2 / 11) = Real.pi / 2 - 3 * Real.arctan (1 / 2) := by
  have h1 : 2 * Real.arctan (1 / 2) = Real.arctan (4 / 3) := by
    rw [Real.two_mul_arctan (by norm_num) (by norm_num)]
    congr 1
    norm_num
  have h2 : Real.arctan (4 / 3) + Real.arctan (1 / 2) = Real.arctan (11 / 2) := by
    rw [Real.arctan_add (by norm_num)]
    congr 1
    norm_num
  have h3 : Real.arctan (2 / 11) = Real.pi / 2 - Real.arctan (11 / 2) := by
    rw [← Real.arctan_inv_of_pos (by norm_num)]
    congr 1
    norm_num
  linarith

/-- `arctan φ^5 = π/4 + 3 arctan (1/2) / 2`. -/
theorem arctan_goldenRatio_pow_five :
    Real.arctan (Real.goldenRatio ^ 5) = Real.pi / 4 + 3 * Real.arctan (1 / 2) / 2 := by
  have h := two_mul_arctan_of_eq (x := Real.goldenRatio ^ 5) (r := 2 / 11)
    (one_lt_pow₀ Real.one_lt_goldenRatio (by norm_num))
    (by linear_combination (-2 * Real.goldenRatio ^ 8 / 11 - 2 * Real.goldenRatio ^ 7 / 11
      - 4 * Real.goldenRatio ^ 6 / 11 - 6 * Real.goldenRatio ^ 5 / 11
      - 10 * Real.goldenRatio ^ 4 / 11 + 6 * Real.goldenRatio ^ 3 / 11
      - 4 * Real.goldenRatio ^ 2 / 11 + 2 * Real.goldenRatio / 11 - 2 / 11) *
      Real.goldenRatio_sq)
  rw [arctan_two_elevenths] at h
  linarith

/-- `arctan (2/29) = 3 arctan (1/2) + 2 arctan (1/8) - π/2`. -/
theorem arctan_two_twentyninths :
    Real.arctan (2 / 29) =
      3 * Real.arctan (1 / 2) + 2 * Real.arctan (1 / 8) - Real.pi / 2 := by
  have h1 : Real.arctan (1 / 2) + Real.arctan (1 / 8) = Real.arctan (2 / 3) := by
    rw [Real.arctan_add (by norm_num)]
    congr 1
    norm_num
  have h2 : 2 * Real.arctan (2 / 3) = Real.arctan (12 / 5) := by
    rw [Real.two_mul_arctan (by norm_num) (by norm_num)]
    congr 1
    norm_num
  have h3 : Real.arctan (12 / 5) + Real.arctan (1 / 2) = -Real.arctan (29 / 2) + Real.pi := by
    rw [Real.arctan_add_eq_add_pi (by norm_num) (by norm_num), ← Real.arctan_neg]
    congr 2
    norm_num
  have h4 : Real.arctan (2 / 29) = Real.pi / 2 - Real.arctan (29 / 2) := by
    rw [← Real.arctan_inv_of_pos (by norm_num)]
    congr 1
    norm_num
  linarith

/-- `arctan φ^7 = 3π/4 - 3 arctan (1/2) / 2 - arctan (1/8)`. -/
theorem arctan_goldenRatio_pow_seven :
    Real.arctan (Real.goldenRatio ^ 7) =
      3 * Real.pi / 4 - 3 * Real.arctan (1 / 2) / 2 - Real.arctan (1 / 8) := by
  have h := two_mul_arctan_of_eq (x := Real.goldenRatio ^ 7) (r := 2 / 29)
    (one_lt_pow₀ Real.one_lt_goldenRatio (by norm_num))
    (by linear_combination (-2 * Real.goldenRatio ^ 12 / 29 - 2 * Real.goldenRatio ^ 11 / 29
      - 4 * Real.goldenRatio ^ 10 / 29 - 6 * Real.goldenRatio ^ 9 / 29
      - 10 * Real.goldenRatio ^ 8 / 29 - 16 * Real.goldenRatio ^ 7 / 29
      - 26 * Real.goldenRatio ^ 6 / 29 + 16 * Real.goldenRatio ^ 5 / 29
      - 10 * Real.goldenRatio ^ 4 / 29 + 6 * Real.goldenRatio ^ 3 / 29
      - 4 * Real.goldenRatio ^ 2 / 29 + 2 * Real.goldenRatio / 29 - 2 / 29) *
      Real.goldenRatio_sq)
  rw [arctan_two_twentyninths] at h
  linarith

/-- `arctan (4/5) = π/2 - 2 arctan (1/2) + arctan (1/32)`. -/
theorem arctan_four_fifths :
    Real.arctan (4 / 5) =
      Real.pi / 2 - 2 * Real.arctan (1 / 2) + Real.arctan (1 / 32) := by
  have h1 : 2 * Real.arctan (1 / 2) = Real.arctan (4 / 3) := by
    rw [Real.two_mul_arctan (by norm_num) (by norm_num)]
    congr 1
    norm_num
  have h2 : Real.arctan (4 / 5) + Real.arctan (4 / 3) = -Real.arctan 32 + Real.pi := by
    rw [Real.arctan_add_eq_add_pi (by norm_num) (by norm_num), ← Real.arctan_neg]
    congr 2
    norm_num
  have h3 : Real.arctan (1 / 32) = Real.pi / 2 - Real.arctan 32 := by
    rw [← Real.arctan_inv_of_pos (by norm_num)]
    congr 1
    norm_num
  linarith

/-! ## 5. Formulas (10), (25), (26), (27): base 16, length 8 -/

/-- **Formula (10)** of the Compendium (page 6):
`arctan 2 = (1/8) P(1, 16, 8, (8, 0, 4, 0, -2, 0, -1, 0))`. -/
theorem formula_10 : BaileyFormula (Real.arctan 2) (1 / 8) 16 1 8
    ![8, 0, 4, 0, -2, 0, -1, 0] := by
  refine (HasBaileyValue.of_pow (a := 2) (j := 4) (B := 1) (HasBaileyValue.of_eq
    (hasBaileyValue_pi.add (hasBaileyValue_arctan_half.smul (-8)))
    (by decide +kernel) rfl)).formula ?_
  rw [arctan_two]
  push_cast
  ring

/-- **Formula (25)** of the Compendium (page 9):
`arctan φ = (1/16) P(1, 16, 8, (8, 16, 4, 0, -2, -4, -1, 0))`. -/
theorem formula_25 : BaileyFormula (Real.arctan Real.goldenRatio) (1 / 16) 16 1 8
    ![8, 16, 4, 0, -2, -4, -1, 0] := by
  refine (HasBaileyValue.of_pow (a := 2) (j := 4) (B := 1) (HasBaileyValue.of_eq
    (hasBaileyValue_pi.add (hasBaileyValue_arctan_half.smul 8))
    (by decide +kernel) rfl)).formula ?_
  rw [arctan_goldenRatio]
  push_cast
  ring

/-- **Formula (26)** of the Compendium (page 9):
`arctan φ^3 = (1/8) P(1, 16, 8, (8, 4, 4, 0, -2, -1, -1, 0))`. -/
theorem formula_26 : BaileyFormula (Real.arctan (Real.goldenRatio ^ 3)) (1 / 8) 16 1 8
    ![8, 4, 4, 0, -2, -1, -1, 0] := by
  refine (HasBaileyValue.of_pow (a := 2) (j := 4) (B := 1) (HasBaileyValue.of_eq
    (hasBaileyValue_pi.add (hasBaileyValue_arctan_half.smul (-4)))
    (by decide +kernel) rfl)).formula ?_
  rw [arctan_goldenRatio_pow_three]
  push_cast
  ring

/-- **Formula (27)** of the Compendium (page 9):
`arctan φ^5 = (1/16) P(1, 16, 8, (8, 32, 4, 0, -2, -8, -1, 0))`. -/
theorem formula_27 : BaileyFormula (Real.arctan (Real.goldenRatio ^ 5)) (1 / 16) 16 1 8
    ![8, 32, 4, 0, -2, -8, -1, 0] := by
  refine (HasBaileyValue.of_pow (a := 2) (j := 4) (B := 1) (HasBaileyValue.of_eq
    (hasBaileyValue_pi.add (hasBaileyValue_arctan_half.smul 24))
    (by decide +kernel) rfl)).formula ?_
  rw [arctan_goldenRatio_pow_five]
  push_cast
  ring

/-! ## 6. Formulas (28) and (13): lengths 24 and 40 -/

/-- **Formula (28)** of the Compendium (page 9):
`arctan φ^7 = (3/2^12) P(1, 2^12, 24, A)` with the 24 entries below. -/
theorem formula_28 : BaileyFormula (Real.arctan (Real.goldenRatio ^ 7)) (3 / 2 ^ 12) 2 12 24
    ![2 ^ 11, 0, 2 ^ 10, 0, -2 ^ 9, -2 ^ 10, -2 ^ 8, 0, 2 ^ 7, 0, 2 ^ 6, 0, -2 ^ 5, 0, -2 ^ 4, 0,
      2 ^ 3, 2 ^ 4, 2 ^ 2, 0, -2, 0, -1, 0] := by
  have hP := (hasBaileyValue_pi.regroup (m := 3) (by norm_num)).smul 256
  have hU := (hasBaileyValue_arctan_half.regroup (m := 3) (by norm_num)).smul (-2048)
  have hV := (hasBaileyValue_arctan (m := 3) (by norm_num)).smul (-4096 / 3)
  refine (HasBaileyValue.of_eq ((hP.add hU).add hV) (by decide +kernel) rfl).formula ?_
  rw [arctan_goldenRatio_pow_seven, show (1 : ℝ) / 2 ^ 3 = 1 / 8 by norm_num]
  push_cast
  ring

/-- **Formula (13)** of the Compendium (page 7):
`arctan (4/5) = (1/2^17) P(1, 2^20, 40, A)` with the 40 entries below. -/
theorem formula_13 : BaileyFormula (Real.arctan (4 / 5)) (1 / 2 ^ 17) 2 20 40
    ![0, 2 ^ 19, 0, -3 * 2 ^ 17, -15 * 2 ^ 15, 0, 0, 5 * 2 ^ 15, 0, 2 ^ 15, 0, -3 * 2 ^ 13, 0, 0,
      5 * 2 ^ 10, 5 * 2 ^ 11, 0, 2 ^ 11, 0, 2 ^ 10, 0, 0, 0, 5 * 2 ^ 7, 15 * 2 ^ 5, 128, 0, -96, 0,
      0, 0, 40, 0, 8, -5, -6, 0, 0, 0, 0] := by
  have hP := (hasBaileyValue_pi.regroup (m := 5) (by norm_num)).smul 16384
  have hU := (hasBaileyValue_arctan_half.regroup (m := 5) (by norm_num)).smul (-262144)
  have hV := (hasBaileyValue_arctan (m := 5) (by norm_num)).smul 131072
  have h119 := (baileyFormula_one_iff.1 formula_119).smul (1 / 4)
  have h120 := (baileyFormula_one_iff.1 formula_120).smul (3 / 4)
  have h121 := (baileyFormula_one_iff.1 formula_121).smul (5 / 4)
  refine (HasBaileyValue.of_eq (((((hP.add hU).add hV).add h119).add h120).add h121)
    (by decide +kernel) rfl).formula ?_
  rw [arctan_four_fifths, show (1 : ℝ) / 2 ^ 5 = 1 / 32 by norm_num]
  push_cast
  ring

/-! ## 7. Formula (68): base 27 -/

/-- The imaginary part of a term of the series of `-log (1 - ω/3)`. -/
theorem im_w3_term (n : ℕ) :
    ((Base3.w3 / 3) ^ n / (n : ℂ)).im = (Base3.w3 ^ n).im / 3 ^ n / n := by
  have e : (Base3.w3 / 3) ^ n / (n : ℂ) = Base3.w3 ^ n * (((1 / 3 ^ n / n : ℝ)) : ℂ) := by
    push_cast
    rw [div_pow]
    ring
  rw [e, Complex.im_mul_ofReal]
  ring

/-- `∑_{n ≥ 1} Im (ω^n) 3^(-n) / n = arctan (√3/7)` for the cube root of unity
`ω = (-1 + i√3)/2`: the imaginary part of the series of `-log (1 - ω/3)`, and
`1 - ω/3 = (7 - i√3)/6`. -/
theorem hasSum_im_w3 :
    HasSum (fun n : ℕ => (Base3.w3 ^ n).im / 3 ^ n / n) (Real.arctan (Real.sqrt 3 / 7)) := by
  have hz : ‖Base3.w3 / 3‖ < 1 := by
    rw [norm_div, Base3.norm_w3]
    norm_num
  have h := Complex.hasSum_im (Complex.hasSum_taylorSeries_neg_log hz)
  have hre : (1 - Base3.w3 / 3).re = 7 / 6 := by
    simp [Base3.w3]
    norm_num
  have him : (1 - Base3.w3 / 3).im = -(Real.sqrt 3 / 6) := by
    simp [Base3.w3]
    ring
  have e : (-Complex.log (1 - Base3.w3 / 3)).im = Real.arctan (Real.sqrt 3 / 7) := by
    rw [Complex.neg_im, Complex.log_im, Base3.arg_eq_arctan (by rw [hre]; norm_num), hre, him,
      ← Real.arctan_neg]
    congr 1
    ring
  rw [e] at h
  exact h.congr_fun fun n => (im_w3_term n).symm

/-- **Formula (68)** of the Compendium (page 24):
`√3 arctan (√3/7) = (1/6) P(1, 27, 3, (3, -1, 0))`. Block `j` is `6√3` times the terms
`3j + 1`, `3j + 2`, `3j + 3` of the series of `hasSum_im_w3`. -/
theorem formula_68 : BaileyFormula (Real.sqrt 3 * Real.arctan (Real.sqrt 3 / 7)) (1 / 6) 27 1 3
    ![3, -1, 0] := by
  have hs := (hasSum_blocks_iff (n := 3) (by norm_num) hasSum_im_w3.summable (by simp) _).2
    hasSum_im_w3
  have hb : HasBaileyValue 27 1 3 ![3, -1, 0]
      (6 * Real.sqrt 3 * Real.arctan (Real.sqrt 3 / 7)) := by
    refine (hs.mul_left (6 * Real.sqrt 3)).congr_fun fun j => ?_
    have s3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have p1 : Base3.w3 ^ (3 * j + 0 + 1) = Base3.w3 := by
      rw [add_zero, pow_add, pow_mul, Base3.w3_pow_three, one_pow, one_mul, pow_one]
    have p2 : Base3.w3 ^ (3 * j + 1 + 1) = Base3.w3 ^ 2 := by
      rw [add_assoc, pow_add, pow_mul, Base3.w3_pow_three, one_pow, one_mul]
    have p3 : Base3.w3 ^ (3 * j + 2 + 1) = 1 := by
      rw [show 3 * j + 2 + 1 = 3 * (j + 1) by ring, pow_mul, Base3.w3_pow_three, one_pow]
    have e27 : (27 : ℝ) ^ j = 3 ^ (3 * j) := by
      rw [pow_mul]
      norm_num
    have i1 : Base3.w3.im = Real.sqrt 3 / 2 := rfl
    have key : ∀ a b c d : ℝ, 6 * Real.sqrt 3 *
        (Real.sqrt 3 / 2 / a / b + -(Real.sqrt 3 / 2) / c / d + 0) = 9 / a / b - 9 / c / d :=
      fun a b c d => by linear_combination (3 / a / b - 3 / c / d) * s3
    rw [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, p1, p2, p3, Base3.w3_sq, i1,
      Complex.one_im, zero_div, zero_div]
    dsimp only
    rw [key]
    simp only [BaseB.baileyBlock, Fin.sum_univ_three, one_mul]
    simp only [Nat.cast_ofNat, e27]
    simp
    field_simp
    ring
  refine hb.formula ?_
  ring

end Compendium

end PiFormula
