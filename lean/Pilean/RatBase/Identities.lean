module

public import Pilean.RatBase.ThreeHalves
public import Pilean.RatBase.FourThirds

/-!
# The multiplicative identities behind the two formulas, in terms of roots of unity

The points of `ThreeHalves` and `FourThirds` are `x r` with `x = √(q/p)` and `r` a root of unity:

* base `4/3`: `w = (√3/2) e^(iπ/6)` (`wFT_eq_exp`), and the identity `1 - w = (1/2) e^(-iπ/3)`
  reads `2 - √3 ζ_12 = ζ_6⁻¹` (`two_sub_sqrt_three_mul_exp`);
* base `3/2`: `w₁ = √(2/3) e^(iπ/12)` and `w₂ = √(2/3) e^(5iπ/12)` (`wTH₁_eq_exp`,
  `wTH₂_eq_exp`), and the identity `(1 - w₁)(1 - w₂) = -i/3` reads
  `(√3 - √2 ζ)(√3 - √2 ζ^5) = -i` for `ζ = ζ_24 = e^(iπ/12)` (`sqrt_three_sub_sqrt_two_mul`).

So, in the form of `BaseB.hasSum_periodic_logs`, the two formulas are

  `π√3/9 = -(1/√3) Im Log(1 - x ζ_12)` at `x = √(3/4)`,
  `π/4 = -(1/2) Im (Log(1 - x ζ_24) + Log(1 - x ζ_24^5))` at `x = √(2/3)`.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace RatBase

/-! ## 1. Base `4/3` -/

/-- `w = (√3/2) e^(iπ/6)`. -/
theorem wFT_eq_exp : wFT = ((Real.sqrt 3 / 2 : ℝ) : ℂ) * exp ((Real.pi / 6 : ℝ) * I) := by
  apply Complex.ext
  · rw [re_ofReal_mul, exp_ofReal_mul_I_re, Real.cos_pi_div_six]
    change (3 / 4 : ℝ) = _
    linear_combination (-1 / 4 : ℝ) * sqrt_three_sq
  · rw [im_ofReal_mul, exp_ofReal_mul_I_im, Real.sin_pi_div_six]
    change Real.sqrt 3 / 4 = _
    ring

/-- **The identity behind the formula in base `4/3`**: `2 - √3 ζ_12 = ζ_6⁻¹`. -/
theorem two_sub_sqrt_three_mul_exp :
    2 - (Real.sqrt 3 : ℂ) * exp ((Real.pi / 6 : ℝ) * I) = exp ((-(Real.pi / 3) : ℝ) * I) := by
  apply Complex.ext
  · rw [sub_re, re_ofReal_mul, exp_ofReal_mul_I_re, exp_ofReal_mul_I_re, Real.cos_neg,
      Real.cos_pi_div_six, Real.cos_pi_div_three, re_ofNat]
    linear_combination (-1 / 2 : ℝ) * sqrt_three_sq
  · rw [sub_im, im_ofReal_mul, exp_ofReal_mul_I_im, exp_ofReal_mul_I_im, Real.sin_neg,
      Real.sin_pi_div_six, Real.sin_pi_div_three, im_ofNat]
    ring

/-! ## 2. Base `3/2` -/

/-- Two complex numbers with the same square and positive real parts are equal. -/
theorem eq_of_sq_eq_of_re_pos {u v : ℂ} (h : u ^ 2 = v ^ 2) (hu : 0 < u.re) (hv : 0 < v.re) :
    u = v := by
  have h1 : (u - v) * (u + v) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact sub_eq_zero.1 h2
  · have h3 := congrArg Complex.re h2
    rw [add_re, zero_re] at h3
    linarith

theorem sqrt_two_thirds_pos : (0 : ℝ) < Real.sqrt (2 / 3) := Real.sqrt_pos.2 (by norm_num)

theorem wTH₁_sq_eq_exp : wTH₁ ^ 2 = ((2 / 3 : ℝ) : ℂ) * exp ((Real.pi / 6 : ℝ) * I) := by
  apply Complex.ext
  · rw [re_ofReal_mul, exp_ofReal_mul_I_re, Real.cos_pi_div_six]
    simp only [wTH₁, sq, mul_re]
    ring
  · rw [im_ofReal_mul, exp_ofReal_mul_I_im, Real.sin_pi_div_six]
    simp only [wTH₁, sq, mul_im]
    linear_combination (-1 / 18 : ℝ) * sqrt_three_sq

theorem wTH₂_sq_eq_exp :
    wTH₂ ^ 2 = ((2 / 3 : ℝ) : ℂ) * exp ((Real.pi - Real.pi / 6 : ℝ) * I) := by
  apply Complex.ext
  · rw [re_ofReal_mul, exp_ofReal_mul_I_re, Real.cos_pi_sub, Real.cos_pi_div_six]
    simp only [wTH₂, sq, mul_re]
    ring
  · rw [im_ofReal_mul, exp_ofReal_mul_I_im, Real.sin_pi_sub, Real.sin_pi_div_six]
    simp only [wTH₂, sq, mul_im]
    linear_combination (-1 / 18 : ℝ) * sqrt_three_sq

/-- `w₁ = √(2/3) e^(iπ/12)`. -/
theorem wTH₁_eq_exp :
    wTH₁ = ((Real.sqrt (2 / 3) : ℝ) : ℂ) * exp ((Real.pi / 12 : ℝ) * I) := by
  refine eq_of_sq_eq_of_re_pos ?_ ?_ ?_
  · rw [wTH₁_sq_eq_exp, mul_pow, ← ofReal_pow, Real.sq_sqrt (by norm_num), ← exp_nat_mul]
    congr 2
    push_cast
    ring
  · change 0 < (3 + Real.sqrt 3) / 6
    positivity
  · rw [re_ofReal_mul, exp_ofReal_mul_I_re]
    exact mul_pos sqrt_two_thirds_pos (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)

/-- `w₂ = √(2/3) e^(5iπ/12)`. -/
theorem wTH₂_eq_exp :
    wTH₂ = ((Real.sqrt (2 / 3) : ℝ) : ℂ) * exp ((5 * Real.pi / 12 : ℝ) * I) := by
  refine eq_of_sq_eq_of_re_pos ?_ ?_ ?_
  · rw [wTH₂_sq_eq_exp, mul_pow, ← ofReal_pow, Real.sq_sqrt (by norm_num), ← exp_nat_mul]
    congr 2
    push_cast
    ring
  · change 0 < (3 - Real.sqrt 3) / 6
    linarith [sqrt_three_lt_three]
  · rw [re_ofReal_mul, exp_ofReal_mul_I_re]
    exact mul_pos sqrt_two_thirds_pos (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)

/-- **The identity behind the formula in base `3/2`**: `(√3 - √2 ζ)(√3 - √2 ζ^5) = -i` for
`ζ = ζ_24 = e^(iπ/12)`. -/
theorem sqrt_three_sub_sqrt_two_mul :
    ((Real.sqrt 3 : ℂ) - (Real.sqrt 2 : ℂ) * exp ((Real.pi / 12 : ℝ) * I)) *
      ((Real.sqrt 3 : ℂ) - (Real.sqrt 2 : ℂ) * exp ((Real.pi / 12 : ℝ) * I) ^ 5) = -I := by
  have h2 : (Real.sqrt 2 : ℂ) = (Real.sqrt 3 : ℂ) * ((Real.sqrt (2 / 3) : ℝ) : ℂ) := by
    rw [← ofReal_mul, ← Real.sqrt_mul (by norm_num)]
    norm_num
  have h5 : exp ((Real.pi / 12 : ℝ) * I) ^ 5 = exp ((5 * Real.pi / 12 : ℝ) * I) := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  have h3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, sqrt_three_sq, ofReal_ofNat]
  have e1 := wTH₁_eq_exp
  have e2 := wTH₂_eq_exp
  have h := one_sub_wTH_mul
  rw [h5, h2, mul_assoc, mul_assoc, ← e1, ← e2]
  linear_combination (Real.sqrt 3 : ℂ) ^ 2 * h + (-I / 3) * h3

end RatBase

end PiFormula
