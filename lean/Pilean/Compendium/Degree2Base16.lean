/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Polylog.Catalan

/-!
# Bailey's Compendium, degree 2, base 16: Catalan's constant and formulas (29), (31), (33)

Section 5 of the Compendium (page 10), stated as printed:

* the definition `G = 1 - 1/3² + 1/5² - 1/7² + ⋯` of Catalan's constant (`formula_p10_a`);
  the constant is `Polylog.catalanConst`, and the statement is that the series converges
  to it. The decimal value `0.9159655941…` printed in the paper is not proved here;
* (29) `π² = P(2, 16, 8, (16, -16, -8, -16, -4, -4, 2, 0))`;
* (31) `log² 2 = 1/6 · P(2, 16, 8, (16, -40, -8, -28, -4, -10, 2, -3))`;
* (33) `G - (1/8) π log 2 = 1/16 · P(2, 16, 8, (8, 8, 4, 0, -2, -2, -1, 0))`.

With `m = 8k + j` the weight `16^(-k)` is `2^(j/2) · 2^(-m/2)`. Put `z₀ = (1 + i)/2`, so that
`z₀^8 = 1/16`. The three vectors are `a_j = u(j)` with

  `u(m) = p Re(z₀^m) + q Im(z₀^m) + r [2 ∣ m] 2^(-m/2)`   (`gauss16 p q r`),

and `∑_m u(m)/m² = p Re Li_2(z₀) + q Im Li_2(z₀) + r Li_2(1/2)/4` (`hasSum_gauss16`), with
`(p, q, r) = (32, 0, -32)`, `(32, 0, -80)`, `(0, 16, 0)`. The values are
`Re Li_2(z₀) = 5π²/96 - (log 2)²/8` (reflection formula), `Im Li_2(z₀) = G - π log 2/8`
(Landen's identity and `Li_2(-i)`) and `Li_2(1/2) = π²/12 - (log 2)²/2`.
-/

@[expose] public section

namespace PiFormula

namespace Compendium

open Polylog Complex

/-- **The definition of Catalan's constant** (Compendium, page 10):
`G = 1 - 1/3² + 1/5² - 1/7² + ⋯`; the series converges, and `Polylog.catalanConst` is its
sum. -/
theorem formula_p10_a :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2) catalanConst :=
  hasSum_catalanConst

/-- The sequence `u(m) = p Re(z₀^m) + q Im(z₀^m) + r [2 ∣ m] 2^(-m/2)` with
`z₀ = (1 + i)/2`. -/
noncomputable def gauss16 (p q r : ℝ) (m : ℕ) : ℝ :=
  p * (((1 + I) / 2 : ℂ) ^ m).re + q * (((1 + I) / 2 : ℂ) ^ m).im
    + r * (if 2 ∣ m then (1 / 2) ^ (m / 2) else 0)

theorem half_add_half_I_pow_eight : ((1 + I) / 2 : ℂ) ^ 8 = ((1 / 16 : ℝ) : ℂ) := by
  have h2 : ((1 + I) / 2 : ℂ) ^ 2 = I / 2 := by
    linear_combination (1 / 4 : ℂ) * Complex.I_sq
  have h8 : ((1 + I) / 2 : ℂ) ^ 8 = (((1 + I) / 2 : ℂ) ^ 2) ^ 4 := by rw [← pow_mul]
  rw [h8, h2, div_pow, Complex.I_pow_four]
  push_cast
  norm_num

theorem gauss16_add_eight (p q r : ℝ) (m : ℕ) :
    gauss16 p q r (m + 8) = gauss16 p q r m / ((16 : ℕ) : ℝ) ^ 1 := by
  have d2 : 2 ∣ m + 8 ↔ 2 ∣ m := by omega
  have q2 : (m + 8) / 2 = m / 2 + 4 := by omega
  simp only [gauss16, d2, q2]
  rw [pow_add ((1 + I) / 2 : ℂ), half_add_half_I_pow_eight, Complex.re_mul_ofReal,
    Complex.im_mul_ofReal, pow_add (1 / 2 : ℝ)]
  push_cast
  split_ifs <;> ring

/-- `∑_{m ≥ 1} u(m)/m² = p Re Li_2(z₀) + q Im Li_2(z₀) + r Li_2(1/2)/4` for
`u = gauss16 p q r`, `z₀ = (1 + i)/2`. -/
theorem hasSum_gauss16 (p q r : ℝ) :
    HasSum (fun m : ℕ => gauss16 p q r m / (m : ℝ) ^ 2)
      (p * (polylog 2 ((1 + I) / 2)).re + q * (polylog 2 ((1 + I) / 2)).im
        + r * (polylogReal 2 (1 / 2) / 4)) := by
  have hz := norm_half_add_half_I_lt.le
  have h1 := (hasSum_re_polylog_nat (s := 2) le_rfl hz).mul_left p
  have h2 := (hasSum_im_polylog_nat (s := 2) le_rfl hz).mul_left q
  have h3 := (hasSum_dvd (d := 2) two_pos (hasSum_polylogReal_nat (s := 2) le_rfl (x := 1 / 2)
    (by rw [abs_of_pos] <;> norm_num))).mul_left r
  have h := (h1.add h2).add h3
  have e : (fun m : ℕ => gauss16 p q r m / (m : ℝ) ^ 2) = fun m : ℕ =>
      p * ((((1 + I) / 2 : ℂ) ^ m).re / (m : ℝ) ^ 2)
        + q * ((((1 + I) / 2 : ℂ) ^ m).im / (m : ℝ) ^ 2)
        + r * (if 2 ∣ m then (1 / 2) ^ (m / 2) / (m : ℝ) ^ 2 else 0) := by
    funext m
    simp only [gauss16]
    split_ifs <;> ring
  rw [e]
  convert h using 1
  norm_num

/-- **Vectors of base 16 and length 8 from the point `(1 + i)/2`.** If `a_i = u(i)` for
`u = gauss16 p q r` (`1 ≤ i ≤ 8`), then
`P(2, 16, 8, a) = p Re Li_2(z₀) + q Im Li_2(z₀) + r Li_2(1/2)/4`, `z₀ = (1 + i)/2`. -/
theorem hasBaileyValueDeg_gauss16 (p q r : ℝ) (a : Fin 8 → ℚ)
    (ha : ∀ i : Fin 8, gauss16 p q r ((i : ℕ) + 1) = (a i : ℝ)) :
    HasBaileyValueDeg 2 16 1 8 a
      (p * (polylog 2 ((1 + I) / 2)).re + q * (polylog 2 ((1 + I) / 2)).im
        + r * (polylogReal 2 (1 / 2) / 4)) :=
  hasBaileyValueDeg_of_quasiperiodic two_ne_zero (by norm_num) (gauss16_add_eight p q r) ha
    (hasSum_gauss16 p q r)

/-- The real and imaginary parts of `((1 + i)/2)^m` for `m = 1, …, 8`. -/
theorem half_add_half_I_pow_table :
    ((((1 + I) / 2 : ℂ) ^ 1).re = 1 / 2 ∧ (((1 + I) / 2 : ℂ) ^ 1).im = 1 / 2) ∧
    ((((1 + I) / 2 : ℂ) ^ 2).re = 0 ∧ (((1 + I) / 2 : ℂ) ^ 2).im = 1 / 2) ∧
    ((((1 + I) / 2 : ℂ) ^ 3).re = -1 / 4 ∧ (((1 + I) / 2 : ℂ) ^ 3).im = 1 / 4) ∧
    ((((1 + I) / 2 : ℂ) ^ 4).re = -1 / 4 ∧ (((1 + I) / 2 : ℂ) ^ 4).im = 0) ∧
    ((((1 + I) / 2 : ℂ) ^ 5).re = -1 / 8 ∧ (((1 + I) / 2 : ℂ) ^ 5).im = -1 / 8) ∧
    ((((1 + I) / 2 : ℂ) ^ 6).re = 0 ∧ (((1 + I) / 2 : ℂ) ^ 6).im = -1 / 8) ∧
    ((((1 + I) / 2 : ℂ) ^ 7).re = 1 / 16 ∧ (((1 + I) / 2 : ℂ) ^ 7).im = -1 / 16) ∧
    ((((1 + I) / 2 : ℂ) ^ 8).re = 1 / 16 ∧ (((1 + I) / 2 : ℂ) ^ 8).im = 0) := by
  have h1 : ((1 + I) / 2 : ℂ) ^ 1 = (1 + I) / 2 := pow_one _
  have h2 : ((1 + I) / 2 : ℂ) ^ 2 = I / 2 := by
    linear_combination (1 / 4 : ℂ) * Complex.I_sq
  have h3 : ((1 + I) / 2 : ℂ) ^ 3 = (-1 + I) / 4 := by
    rw [pow_succ, h2]
    linear_combination (1 / 4 : ℂ) * Complex.I_sq
  have h4 : ((1 + I) / 2 : ℂ) ^ 4 = -1 / 4 := by
    rw [pow_succ, h3]
    linear_combination (1 / 8 : ℂ) * Complex.I_sq
  have h5 : ((1 + I) / 2 : ℂ) ^ 5 = -(1 + I) / 8 := by
    rw [pow_succ, h4]
    ring
  have h6 : ((1 + I) / 2 : ℂ) ^ 6 = -I / 8 := by
    rw [pow_succ, h5]
    linear_combination (-1 / 16 : ℂ) * Complex.I_sq
  have h7 : ((1 + I) / 2 : ℂ) ^ 7 = (1 - I) / 16 := by
    rw [pow_succ, h6]
    linear_combination (-1 / 16 : ℂ) * Complex.I_sq
  have h8 : ((1 + I) / 2 : ℂ) ^ 8 = 1 / 16 := by
    rw [pow_succ, h7]
    linear_combination (-1 / 32 : ℂ) * Complex.I_sq
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  simp

/-- **Formula (29)** of the Compendium (page 10):
`π² = P(2, 16, 8, (16, -16, -8, -16, -4, -4, 2, 0))`. -/
theorem formula_29 :
    BaileyFormulaDeg (Real.pi ^ 2) 1 2 16 1 8 ![16, -16, -8, -16, -4, -4, 2, 0] := by
  obtain ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, ⟨a6, b6⟩, ⟨a7, b7⟩, a8, b8⟩ :=
    half_add_half_I_pow_table
  refine (hasBaileyValueDeg_gauss16 32 0 (-32) _ fun i => ?_).formula ?_
  · fin_cases i <;> norm_num [gauss16, a1, a2, a3, a4, a5, a6, a7, a8]
  · rw [polylog_two_half_add_half_I_re, polylogReal_two_half]
    ring

/-- **Formula (31)** of the Compendium (page 10):
`log² 2 = 1/6 P(2, 16, 8, (16, -40, -8, -28, -4, -10, 2, -3))`. -/
theorem formula_31 :
    BaileyFormulaDeg (Real.log 2 ^ 2) (1 / 6) 2 16 1 8 ![16, -40, -8, -28, -4, -10, 2, -3] := by
  obtain ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, ⟨a6, b6⟩, ⟨a7, b7⟩, a8, b8⟩ :=
    half_add_half_I_pow_table
  refine (hasBaileyValueDeg_gauss16 32 0 (-80) _ fun i => ?_).formula ?_
  · fin_cases i <;> norm_num [gauss16, a1, a2, a3, a4, a5, a6, a7, a8]
  · rw [polylog_two_half_add_half_I_re, polylogReal_two_half]
    ring

/-- **Formula (33)** of the Compendium (page 10):
`G - (1/8) π log 2 = 1/16 P(2, 16, 8, (8, 8, 4, 0, -2, -2, -1, 0))`, `G` Catalan's constant. -/
theorem formula_33 :
    BaileyFormulaDeg (catalanConst - 1 / 8 * Real.pi * Real.log 2) (1 / 16) 2 16 1 8
      ![8, 8, 4, 0, -2, -2, -1, 0] := by
  obtain ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, ⟨a6, b6⟩, ⟨a7, b7⟩, a8, b8⟩ :=
    half_add_half_I_pow_table
  refine (hasBaileyValueDeg_gauss16 0 16 0 _ fun i => ?_).formula ?_
  · fin_cases i <;> norm_num [gauss16, b1, b2, b3, b4, b5, b6, b7, b8]
  · rw [polylog_two_half_add_half_I_im]
    ring

end Compendium

end PiFormula
