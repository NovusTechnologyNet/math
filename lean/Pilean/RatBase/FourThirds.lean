/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.RatBase.Defs

/-!
# A degree-1 BBP-type formula for `π√3` in base `4/3`

`π√3 / 9 = ∑_{j ≥ 0} (3/4)^(6j) ∑_{i=1}^{12} c_i / (12j + i)` with

  `c = (1/4, 3/8, 3/8, 9/32, 9/64, 0, -27/256, -81/512, -81/512, -243/2048, -243/4096, 0)`

(`sqrt_three_pi_base_four_thirds`). In the pattern form (`hasSum_rhoFT`):

  `π√3 / 9 = ∑_{k ≥ 1} ρ(k) (3/4)^⌊k/2⌋ / k`,   `ρ = (1/4, 1/2, 1/2, 1/2, 1/4, 0)`, then `-ρ`,

of period 12.

The proof. Let `x = √3/2` and `w = x e^(iπ/6) = 3/4 + (√3/4) i` (`wFT`). The multiplicative
identity behind the formula is

  `1 - w = (1/4)(1 - √3 i) = (1/2) e^(-iπ/3)`,   that is   `2 - √3 ζ_12 = ζ_6⁻¹`,

so `∑_{k ≥ 1} Im(w^k) / k = -arg(1 - w) = arctan √3 = π/3`. On the other hand
`w^2 = (3/2) w - 3/4` and `w^6 = -27/64`, which give `Im(w^k) = √3 ρ(k) (3/4)^⌊k/2⌋`
(`wFT_pow_im`): the weights `x^k sin(kπ/6)` are `√3` times rational numbers.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace RatBase

/-! ## 1. The point `w = (√3/2) e^(iπ/6)` -/

/-- `w = (√3/2) e^(iπ/6) = 3/4 + (√3/4) i`. -/
noncomputable def wFT : ℂ := ⟨3 / 4, Real.sqrt 3 / 4⟩

/-- `w` is a root of `X^2 - (3/2) X + 3/4`. -/
theorem wFT_sq : wFT ^ 2 = ((3 / 2 : ℝ) : ℂ) * wFT - ((3 / 4 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [wFT, sq, mul_re, sub_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    linear_combination (-1 / 16 : ℝ) * sqrt_three_sq
  · simp only [wFT, sq, mul_im, sub_im, ofReal_re, ofReal_im, zero_mul, add_zero, sub_zero]
    ring

theorem wFT_pow_three : wFT ^ 3 = ((3 / 2 : ℝ) : ℂ) * wFT - ((9 / 8 : ℝ) : ℂ) := by
  have h := wFT_sq
  push_cast at h ⊢
  linear_combination (wFT + 3 / 2) * h

theorem wFT_pow_four : wFT ^ 4 = ((9 / 8 : ℝ) : ℂ) * wFT - ((9 / 8 : ℝ) : ℂ) := by
  have h := wFT_sq
  push_cast at h ⊢
  linear_combination (wFT ^ 2 + 3 / 2 * wFT + 3 / 2) * h

theorem wFT_pow_five : wFT ^ 5 = ((9 / 16 : ℝ) : ℂ) * wFT - ((27 / 32 : ℝ) : ℂ) := by
  have h := wFT_sq
  push_cast at h ⊢
  linear_combination (wFT ^ 3 + 3 / 2 * wFT ^ 2 + 3 / 2 * wFT + 9 / 8) * h

/-- `w^6 = -27/64`. -/
theorem wFT_pow_six : wFT ^ 6 = ((-(27 / 64) : ℝ) : ℂ) := by
  have h := wFT_sq
  push_cast at h ⊢
  linear_combination
    (wFT ^ 4 + 3 / 2 * wFT ^ 3 + 3 / 2 * wFT ^ 2 + 9 / 8 * wFT + 9 / 16) * h

/-- The identity behind the formula: `1 - w = (1/4)(1 - √3 i)`. -/
theorem one_sub_wFT : 1 - wFT = ((1 / 4 : ℝ) : ℂ) * (1 - (Real.sqrt 3 : ℂ) * I) := by
  apply Complex.ext
  · simp only [wFT, sub_re, one_re, mul_re, ofReal_re, ofReal_im, I_re, sub_im, one_im, I_im,
      mul_im]
    ring
  · simp only [wFT, sub_im, one_im, mul_im, ofReal_re, ofReal_im, I_im, sub_re, one_re, I_re,
      mul_re]
    ring

theorem norm_wFT_lt_one : ‖wFT‖ < 1 := by
  have h : ‖wFT‖ ^ 2 = 3 / 4 := by
    rw [Complex.sq_norm, normSq_apply]
    change (3 / 4 : ℝ) * (3 / 4) + Real.sqrt 3 / 4 * (Real.sqrt 3 / 4) = 3 / 4
    linear_combination (1 / 16 : ℝ) * sqrt_three_sq
  nlinarith [norm_nonneg wFT]

/-! ## 2. The pattern -/

/-- The pattern `(1/4, 1/2, 1/2, 1/2, 1/4, 0, -1/4, -1/2, -1/2, -1/2, -1/4, 0)` of period 12. -/
def rhoFT (k : ℕ) : ℚ :=
  (-1) ^ (k / 6) * match k % 6 with
    | 1 | 5 => 1 / 4
    | 2 | 3 | 4 => 1 / 2
    | _ => 0

theorem rhoFT_add_six (k : ℕ) : rhoFT (k + 6) = -rhoFT k := by
  have h1 : (k + 6) / 6 = k / 6 + 1 := by omega
  have h2 : (k + 6) % 6 = k % 6 := by omega
  simp only [rhoFT, h1, h2, pow_succ]
  ring

theorem rhoFT_periodic (k : ℕ) : rhoFT (k + 12) = rhoFT k := by
  rw [show k + 12 = k + 6 + 6 from rfl, rhoFT_add_six, rhoFT_add_six, neg_neg]

/-- `Im(w^k) = √3 ρ(k) (3/4)^⌊k/2⌋`. -/
theorem wFT_pow_im (k : ℕ) :
    (wFT ^ k).im = Real.sqrt 3 * ((rhoFT k : ℝ) * (3 / 4 : ℝ) ^ (k / 2)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 6 with hk | hk
    · interval_cases k
      · simp [rhoFT]
      · simp [rhoFT, wFT]
        ring
      · rw [wFT_sq]
        simp [rhoFT, wFT]
        ring
      · rw [wFT_pow_three]
        simp [rhoFT, wFT]
        ring
      · rw [wFT_pow_four]
        simp [rhoFT, wFT]
        ring
      · rw [wFT_pow_five]
        simp [rhoFT, wFT]
        ring
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
      have h := ih m (by omega)
      have e : (m + 6) / 2 = m / 2 + 3 := by omega
      rw [pow_add, wFT_pow_six, mul_im, ofReal_re, ofReal_im, mul_zero, zero_add, h,
        rhoFT_add_six, e, pow_add]
      push_cast
      ring

/-! ## 3. The formula -/

/-- **The pattern form**: `∑_{k ≥ 1} ρ(k) (3/4)^⌊k/2⌋ / k = π√3 / 9`. -/
theorem hasSum_rhoFT : HasSum (seriesTermRat 4 3 rhoFT) (Real.sqrt 3 * Real.pi / 9) := by
  have h := (hasSum_im_pow_div norm_wFT_lt_one).mul_left (Real.sqrt 3 / 3)
  have e1 : wFT.im / (1 - wFT.re) = Real.sqrt 3 := by
    change Real.sqrt 3 / 4 / (1 - 3 / 4) = Real.sqrt 3
    ring
  rw [e1, Real.arctan_sqrt_three] at h
  have e2 : Real.sqrt 3 / 3 * (Real.pi / 3) = Real.sqrt 3 * Real.pi / 9 := by ring
  rw [e2] at h
  refine h.congr_fun fun k => ?_
  rw [seriesTermRat, wFT_pow_im]
  push_cast
  linear_combination
    (-1 / 3 * (rhoFT k : ℝ) * (3 / 4 : ℝ) ^ (k / 2) / (k : ℝ)) * sqrt_three_sq

/-- **A degree-1 BBP-type formula for `π √3` in base `4/3`.** -/
theorem sqrt_three_pi_base_four_thirds :
    HasSum (baileyBlockRat 4 3 6 12 ![1/4, 3/8, 3/8, 9/32, 9/64, 0, -27/256, -81/512, -81/512,
      -243/2048, -243/4096, 0]) (Real.sqrt 3 * Real.pi / 9) := by
  have h := hasSum_baileyBlockRat_of_pattern 4 3 (B := 6) (N := 12) rfl (by norm_num)
    rhoFT_periodic hasSum_rhoFT
  have e : (![1/4, 3/8, 3/8, 9/32, 9/64, 0, -27/256, -81/512, -81/512, -243/2048, -243/4096,
      0] : Fin 12 → ℚ) = fun i : Fin 12 =>
      rhoFT ((i : ℕ) + 1) * (((3 : ℕ) : ℚ) / ((4 : ℕ) : ℚ)) ^ (((i : ℕ) + 1) / 2) := by
    funext i
    fin_cases i <;> norm_num [rhoFT]
  rw [e]
  exact h

end RatBase

end PiFormula
