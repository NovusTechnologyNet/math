/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.RatBase.Defs

/-!
# A degree-1 BBP-type formula for `π` in base `3/2`

`π / 4 = ∑_{j ≥ 0} (2/3)^(12j) ∑_{i=1}^{24} a_i / (24j + i)` with

  `a = (1/2, 1/3, 0, 0, 2/9, 8/27, 4/27, 0, 0, 16/243, 16/243, 0)`, then `-(2/3)^6 a`

(`pi_base_three_halves`). In the pattern form (`hasSum_rhoTH`):

  `π / 4 = ∑_{k ≥ 1} ρ(k) (2/3)^⌊k/2⌋ / k`,
  `ρ = (1/2, 1/2, 0, 0, 1/2, 1, 1/2, 0, 0, 1/2, 1/2, 0)`, then `-ρ`,

of period 24. With `x = √(2/3)` this is `∑ g(k) x^k / k` for the pattern
`g(k) = ρ(k) √(3/2)^(k mod 2) = (sin(kπ/12) + sin(5kπ/12)) / 2`, with values in `ℚ(√6)`
(`hasSum_rhoTH_sqrt`).

The proof. Let `ζ = e^(iπ/12)` and

  `w₁ = x ζ = ((3 + √3) + (3 - √3) i) / 6`,   `w₂ = x ζ^5 = ((3 - √3) + (3 + √3) i) / 6`

(`wTH₁`, `wTH₂`). The multiplicative identities behind the formula are

  `1 - w₁ = ((3 - √3)/6) (1 - i)`,   `1 - w₂ = ((3 + √3)/6) (1 - i)`,

that is `√3 - √2 ζ = ((√3 - 1)/2)(1 - i)` and `√3 - √2 ζ^5 = ((√3 + 1)/2)(1 - i)`, with the
product `(√3 - √2 ζ)(√3 - √2 ζ^5) = -i`. (The triangle `0, 1, w₂` has the angles 75°, 45°,
60°; the triangle `0, 1, w₁`, its conjugate under `√3 ↦ -√3`, has the angles 15°, 45°, 120°.)
So

  `∑_{k ≥ 1} Im(w₁^k) / k = ∑_{k ≥ 1} Im(w₂^k) / k = -arg(1 - i) = π/4`.

Each of the two series has weights in `ℚ(√3)`; their mean has rational weights:
`w₁ + w₂ = 1 + i` and `w₁ w₂ = 2i/3`, so the power sums `w₁^k + w₂^k` lie in `ℚ(i)`, and
`w₁^6 = w₂^6 = 8i/27` gives `Im(w₁^k + w₂^k) = 2 ρ(k) (2/3)^⌊k/2⌋` (`wTH_pow_add`).
-/

@[expose] public section

open Complex

namespace PiFormula

namespace RatBase

/-! ## 1. The points `w₁ = √(2/3) e^(iπ/12)` and `w₂ = √(2/3) e^(5iπ/12)` -/

/-- `w₁ = √(2/3) e^(iπ/12) = ((3 + √3) + (3 - √3) i) / 6`. -/
noncomputable def wTH₁ : ℂ := ⟨(3 + Real.sqrt 3) / 6, (3 - Real.sqrt 3) / 6⟩

/-- `w₂ = √(2/3) e^(5iπ/12) = ((3 - √3) + (3 + √3) i) / 6`. -/
noncomputable def wTH₂ : ℂ := ⟨(3 - Real.sqrt 3) / 6, (3 + Real.sqrt 3) / 6⟩

theorem sqrt_three_lt_three : Real.sqrt 3 < 3 := by
  nlinarith [sqrt_three_sq, Real.sqrt_nonneg 3]

theorem wTH_add : wTH₁ + wTH₂ = 1 + I := by
  apply Complex.ext
  · simp only [wTH₁, wTH₂, add_re, one_re, I_re]
    ring
  · simp only [wTH₁, wTH₂, add_im, one_im, I_im]
    ring

theorem wTH_mul : wTH₁ * wTH₂ = 2 / 3 * I := by
  apply Complex.ext
  · simp only [wTH₁, wTH₂, mul_re, I_re, I_im, mul_zero, mul_one, re_ofNat, im_ofNat,
      div_ofNat_re, div_ofNat_im]
    ring
  · simp only [wTH₁, wTH₂, mul_im, I_re, I_im, mul_zero, mul_one, re_ofNat, im_ofNat,
      div_ofNat_re, div_ofNat_im]
    linear_combination (1 / 18 : ℝ) * sqrt_three_sq

/-- `w₁` is a root of `X^2 - (1 + i) X + 2i/3`. -/
theorem wTH₁_sq : wTH₁ ^ 2 = (1 + I) * wTH₁ - 2 / 3 * I := by
  linear_combination wTH₁ * wTH_add - wTH_mul

/-- `w₂` is the other root of `X^2 - (1 + i) X + 2i/3`. -/
theorem wTH₂_sq : wTH₂ ^ 2 = (1 + I) * wTH₂ - 2 / 3 * I := by
  linear_combination wTH₂ * wTH_add - wTH_mul

/-- A root of `X^2 - (1 + i) X + 2i/3` has `w^6 = 8i/27`. -/
theorem pow_six_of_sq {w : ℂ} (h : w ^ 2 = (1 + I) * w - 2 / 3 * I) : w ^ 6 = 8 / 27 * I := by
  have h3 : w ^ 3 = 4 / 3 * I * w + (2 - 2 * I) / 3 := by
    linear_combination (w + (1 + I)) * h + (w - 2 / 3) * I_sq
  rw [show w ^ 6 = (w ^ 3) ^ 2 by ring, h3]
  linear_combination (16 / 9 * I ^ 2) * h + (16 / 9 * I * w + 4 / 9 - 32 / 27 * I) * I_sq

/-- The identity behind the formula: `1 - w₁` is a positive multiple of `1 - i`. -/
theorem one_sub_wTH₁ : 1 - wTH₁ = (((3 - Real.sqrt 3) / 6 : ℝ) : ℂ) * (1 - I) := by
  apply Complex.ext
  · simp only [wTH₁, sub_re, one_re, mul_re, ofReal_re, ofReal_im, I_re, sub_im, one_im, I_im]
    ring
  · simp only [wTH₁, sub_im, one_im, mul_im, ofReal_re, ofReal_im, I_im, sub_re, one_re, I_re]
    ring

/-- The identity behind the formula: `1 - w₂` is a positive multiple of `1 - i`. -/
theorem one_sub_wTH₂ : 1 - wTH₂ = (((3 + Real.sqrt 3) / 6 : ℝ) : ℂ) * (1 - I) := by
  apply Complex.ext
  · simp only [wTH₂, sub_re, one_re, mul_re, ofReal_re, ofReal_im, I_re, sub_im, one_im, I_im]
    ring
  · simp only [wTH₂, sub_im, one_im, mul_im, ofReal_re, ofReal_im, I_im, sub_re, one_re, I_re]
    ring

/-- `(1 - w₁)(1 - w₂) = -i/3`, that is `(√3 - √2 ζ)(√3 - √2 ζ^5) = -i` for `ζ = e^(iπ/12)`. -/
theorem one_sub_wTH_mul : (1 - wTH₁) * (1 - wTH₂) = -I / 3 := by
  linear_combination -wTH_add + wTH_mul

theorem norm_wTH₁_lt_one : ‖wTH₁‖ < 1 := by
  have h : ‖wTH₁‖ ^ 2 = 2 / 3 := by
    rw [Complex.sq_norm, normSq_apply]
    change (3 + Real.sqrt 3) / 6 * ((3 + Real.sqrt 3) / 6) +
      (3 - Real.sqrt 3) / 6 * ((3 - Real.sqrt 3) / 6) = 2 / 3
    linear_combination (1 / 18 : ℝ) * sqrt_three_sq
  nlinarith [norm_nonneg wTH₁]

theorem norm_wTH₂_lt_one : ‖wTH₂‖ < 1 := by
  have h : ‖wTH₂‖ ^ 2 = 2 / 3 := by
    rw [Complex.sq_norm, normSq_apply]
    change (3 - Real.sqrt 3) / 6 * ((3 - Real.sqrt 3) / 6) +
      (3 + Real.sqrt 3) / 6 * ((3 + Real.sqrt 3) / 6) = 2 / 3
    linear_combination (1 / 18 : ℝ) * sqrt_three_sq
  nlinarith [norm_nonneg wTH₂]

/-! ## 2. The power sums `w₁^k + w₂^k` -/

theorem wTH_rec (k : ℕ) : wTH₁ ^ (k + 2) + wTH₂ ^ (k + 2) =
    (1 + I) * (wTH₁ ^ (k + 1) + wTH₂ ^ (k + 1)) - 2 / 3 * I * (wTH₁ ^ k + wTH₂ ^ k) := by
  linear_combination wTH₁ ^ k * wTH₁_sq + wTH₂ ^ k * wTH₂_sq

theorem wTH_pow_two : wTH₁ ^ 2 + wTH₂ ^ 2 = 2 / 3 * I := by
  linear_combination wTH₁_sq + wTH₂_sq + (1 + I) * wTH_add + I_sq

theorem wTH_pow_three : wTH₁ ^ 3 + wTH₂ ^ 3 = 0 := by
  linear_combination wTH_rec 1 + (1 + I) * wTH_pow_two - 2 / 3 * I * wTH_add

theorem wTH_pow_four : wTH₁ ^ 4 + wTH₂ ^ 4 = 4 / 9 := by
  linear_combination wTH_rec 2 + (1 + I) * wTH_pow_three - 2 / 3 * I * wTH_pow_two
    - 4 / 9 * I_sq

theorem wTH_pow_five : wTH₁ ^ 5 + wTH₂ ^ 5 = 4 / 9 * (1 + I) := by
  linear_combination wTH_rec 3 + (1 + I) * wTH_pow_four - 2 / 3 * I * wTH_pow_three

/-! ## 3. The pattern -/

/-- The pattern `(1/2, 1/2, 0, 0, 1/2, 1, 1/2, 0, 0, 1/2, 1/2, 0)`, then its negative; period
24. -/
def rhoTH (k : ℕ) : ℚ :=
  (-1) ^ (k / 12) * match k % 12 with
    | 1 | 2 | 5 | 7 | 10 | 11 => 1 / 2
    | 6 => 1
    | _ => 0

theorem rhoTH_add_twelve (k : ℕ) : rhoTH (k + 12) = -rhoTH k := by
  have h1 : (k + 12) / 12 = k / 12 + 1 := by omega
  have h2 : (k + 12) % 12 = k % 12 := by omega
  simp only [rhoTH, h1, h2, pow_succ]
  ring

theorem rhoTH_periodic (k : ℕ) : rhoTH (k + 24) = rhoTH k := by
  rw [show k + 24 = k + 12 + 12 from rfl, rhoTH_add_twelve, rhoTH_add_twelve, neg_neg]

/-- `w₁^k + w₂^k = 2 (2/3)^⌊k/2⌋ (ρ(k + 6) + ρ(k) i)`. -/
theorem wTH_pow_add (k : ℕ) : wTH₁ ^ k + wTH₂ ^ k =
    ((2 * ((rhoTH (k + 6) : ℝ) * (2 / 3 : ℝ) ^ (k / 2)) : ℝ) : ℂ) +
      ((2 * ((rhoTH k : ℝ) * (2 / 3 : ℝ) ^ (k / 2)) : ℝ) : ℂ) * I := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 6 with hk | hk
    · interval_cases k
      · norm_num [rhoTH]
      · rw [pow_one, pow_one, wTH_add]
        norm_num [rhoTH]
      · rw [wTH_pow_two]
        norm_num [rhoTH]
      · rw [wTH_pow_three]
        norm_num [rhoTH]
      · rw [wTH_pow_four]
        norm_num [rhoTH]
      · rw [wTH_pow_five]
        norm_num [rhoTH]
        ring
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
      have h := ih m (by omega)
      have e : (m + 6) / 2 = m / 2 + 3 := by omega
      rw [pow_add, pow_add, pow_six_of_sq wTH₁_sq, pow_six_of_sq wTH₂_sq, ← add_mul, h,
        show m + 6 + 6 = m + 12 from rfl, rhoTH_add_twelve, e, pow_add]
      push_cast
      linear_combination (16 / 27 * (rhoTH m : ℂ) * (2 / 3 : ℂ) ^ (m / 2)) * I_sq

/-! ## 4. The formula -/

/-- **The pattern form**: `∑_{k ≥ 1} ρ(k) (2/3)^⌊k/2⌋ / k = π / 4`. -/
theorem hasSum_rhoTH : HasSum (seriesTermRat 3 2 rhoTH) (Real.pi / 4) := by
  have h3 := sqrt_three_lt_three
  have h0 := Real.sqrt_nonneg 3
  have e1 : wTH₁.im / (1 - wTH₁.re) = 1 := by
    change (3 - Real.sqrt 3) / 6 / (1 - (3 + Real.sqrt 3) / 6) = 1
    rw [div_eq_one_iff_eq (by linarith)]
    ring
  have e2 : wTH₂.im / (1 - wTH₂.re) = 1 := by
    change (3 + Real.sqrt 3) / 6 / (1 - (3 - Real.sqrt 3) / 6) = 1
    rw [div_eq_one_iff_eq (by linarith)]
    ring
  have h1 := hasSum_im_pow_div norm_wTH₁_lt_one
  have h2 := hasSum_im_pow_div norm_wTH₂_lt_one
  rw [e1, Real.arctan_one] at h1
  rw [e2, Real.arctan_one] at h2
  have h := (h1.add h2).mul_left (1 / 2)
  have e3 : 1 / 2 * (Real.pi / 4 + Real.pi / 4) = Real.pi / 4 := by ring
  rw [e3] at h
  refine h.congr_fun fun k => ?_
  have e4 := congrArg Complex.im (wTH_pow_add k)
  rw [add_im, add_im, ofReal_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
    add_zero, zero_add] at e4
  rw [seriesTermRat, ← add_div, e4]
  push_cast
  ring

/-- The pattern form at `x = √(2/3)`: `∑_{k ≥ 1} g(k) x^k / k = π / 4` for the pattern
`g(k) = ρ(k) √(3/2)^(k mod 2)` of period 24, with values in `ℚ(√6)`. -/
theorem hasSum_rhoTH_sqrt : HasSum (fun k : ℕ =>
    (rhoTH k : ℝ) * Real.sqrt (3 / 2) ^ (k % 2) * Real.sqrt (2 / 3) ^ k / (k : ℝ))
    (Real.pi / 4) := by
  refine hasSum_rhoTH.congr_fun fun k => ?_
  rw [seriesTermRat_eq_sqrt (by norm_num) (by norm_num), Nat.cast_ofNat, Nat.cast_ofNat]

/-- **A degree-1 BBP-type formula for `π` in base `3/2`.** -/
theorem pi_base_three_halves :
    HasSum (baileyBlockRat 3 2 12 24 ![1/2, 1/3, 0, 0, 2/9, 8/27, 4/27, 0, 0, 16/243, 16/243, 0,
      -32/729, -64/2187, 0, 0, -128/6561, -512/19683, -256/19683, 0, 0, -1024/177147,
      -1024/177147, 0]) (Real.pi / 4) := by
  have h := hasSum_baileyBlockRat_of_pattern 3 2 (B := 12) (N := 24) rfl (by norm_num)
    rhoTH_periodic hasSum_rhoTH
  have e : (![1/2, 1/3, 0, 0, 2/9, 8/27, 4/27, 0, 0, 16/243, 16/243, 0,
      -32/729, -64/2187, 0, 0, -128/6561, -512/19683, -256/19683, 0, 0, -1024/177147,
      -1024/177147, 0] : Fin 24 → ℚ) = fun i : Fin 24 =>
      rhoTH ((i : ℕ) + 1) * (((2 : ℕ) : ℚ) / ((3 : ℕ) : ℚ)) ^ (((i : ℕ) + 1) / 2) := by
    funext i
    fin_cases i <;> norm_num [rhoTH]
  rw [e]
  exact h

end RatBase

end PiFormula
