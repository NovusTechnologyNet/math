/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Polylog.DilogComplex

/-!
# The dilogarithm at `e^(iπ/6)/√3`

The point `z₃ = e^(iπ/6)/√3 = 1/2 + (√3/6) i` (`pointThree`) lies on the line `Re z = 1/2`, so
`1 - z₃ = conj z₃`, and it has `‖z₃‖² = 1/3`, `arg z₃ = π/6`. It is the point behind the
degree-2 formulas of base 3 (`z₃^12 = 3^(-6)`).

* `pointThree_sq : z₃² = z₃ - 1/3`, hence the recurrence
  `Re(z₃^(m+2)) = Re(z₃^(m+1)) - Re(z₃^m)/3` (`pointThree_pow_re`) with rational values;
* `pointThree_pow_six : z₃^6 = -1/27`, `pointThree_pow_twelve : z₃^12 = 1/729`;
* `polylog_two_pointThree_re : Re Li_2(z₃) = 5π²/72 - (log 3)²/8` (reflection formula).
-/

@[expose] public section

namespace PiFormula

namespace Polylog

open Complex

/-- The point `z₃ = e^(iπ/6)/√3 = 1/2 + (√3/6) i`. -/
noncomputable def pointThree : ℂ := (3 + ((Real.sqrt 3 : ℝ) : ℂ) * I) / 6

theorem pointThree_re : pointThree.re = 1 / 2 := by
  simp [pointThree]
  norm_num

theorem pointThree_im : pointThree.im = Real.sqrt 3 / 6 := by
  simp [pointThree]

theorem ofReal_sqrt_three_sq : (((Real.sqrt 3 : ℝ) : ℂ)) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- `z₃² = z₃ - 1/3`: the point is a root of `z² - z + 1/3`. -/
theorem pointThree_sq : pointThree ^ 2 = pointThree - 1 / 3 := by
  rw [pointThree]
  linear_combination (1 / 12 : ℂ) * Complex.I_sq + (I ^ 2 / 36) * ofReal_sqrt_three_sq

/-- `z₃^6 = -1/27`. -/
theorem pointThree_pow_six : pointThree ^ 6 = -1 / 27 := by
  linear_combination (pointThree ^ 4 + pointThree ^ 3 + 2 / 3 * pointThree ^ 2
    + 1 / 3 * pointThree + 1 / 9) * pointThree_sq

/-- `z₃^12 = 1/729 = 3^(-6)`. -/
theorem pointThree_pow_twelve : pointThree ^ 12 = ((1 / 729 : ℝ) : ℂ) := by
  have h : pointThree ^ 12 = (pointThree ^ 6) ^ 2 := by rw [← pow_mul]
  rw [h, pointThree_pow_six]
  push_cast
  norm_num

/-- The recurrence `Re(z₃^(m+2)) = Re(z₃^(m+1)) - Re(z₃^m)/3`. -/
theorem pointThree_pow_re (m : ℕ) :
    (pointThree ^ (m + 2)).re = (pointThree ^ (m + 1)).re - (pointThree ^ m).re / 3 := by
  have h : pointThree ^ (m + 2) =
      pointThree ^ (m + 1) - ((1 / 3 : ℝ) : ℂ) * pointThree ^ m := by
    rw [pow_add, pointThree_sq, pow_succ]
    push_cast
    ring
  rw [h, Complex.sub_re, Complex.re_ofReal_mul]
  ring

theorem norm_pointThree_sq : ‖pointThree‖ ^ 2 = 1 / 3 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [Complex.sq_norm, Complex.normSq_apply, pointThree_re, pointThree_im]
  nlinarith [h3]

theorem norm_pointThree_lt : ‖pointThree‖ < 1 := by
  by_contra hge
  have h1 : (1 : ℝ) ≤ ‖pointThree‖ ^ 2 := one_le_pow₀ (not_lt.1 hge)
  rw [norm_pointThree_sq] at h1
  norm_num at h1

theorem log_norm_pointThree : Real.log ‖pointThree‖ = -Real.log 3 / 2 := by
  have h2 : Real.log (‖pointThree‖ ^ 2) = 2 * Real.log ‖pointThree‖ := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [norm_pointThree_sq, one_div, Real.log_inv] at h2
  linarith

theorem arg_pointThree : pointThree.arg = Real.pi / 6 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e : Real.sqrt 3 / 6 / (1 / 2) = (Real.sqrt 3)⁻¹ := by
    rw [eq_comm, inv_eq_iff_eq_inv, inv_div, div_div_eq_mul_div, eq_div_iff hpos.ne']
    nlinarith [h3]
  rw [arg_eq_arctan_of_re_pos (by rw [pointThree_re]; norm_num), pointThree_re,
    pointThree_im, e, Real.arctan_inv_sqrt_three]

/-- **`Re Li_2(e^(iπ/6)/√3) = 5π²/72 - (log 3)²/8`.** -/
theorem polylog_two_pointThree_re :
    (polylog 2 pointThree).re = 5 * Real.pi ^ 2 / 72 - Real.log 3 ^ 2 / 8 := by
  rw [re_polylog_two_of_re_eq_half norm_pointThree_lt pointThree_re, log_norm_pointThree,
    arg_pointThree]
  ring

end Polylog

end PiFormula
