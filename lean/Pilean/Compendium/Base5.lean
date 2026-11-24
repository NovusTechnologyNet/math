/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Compendium.Defs

/-!
# Bailey's Compendium: formula (87) in base 5

`(25/2) log ((781/256) ((57 - 5√5)/(57 + 5√5))^√5) = P(1, 5^5, 5, (0, 5, 1, 0, 0))`,
stated as printed (`formula_87`).

The series is `125 ∑ 5^(-k) / k` over the `k ≡ 2, 3 (mod 5)`. The indicator of these residues
is `1/2 - (1/2) [5 ∣ k] - (1/√5) (cos (2πk/5) - cos (4πk/5))`, so the value is a combination of
`log (1 - 1/5)`, `log (1 - 5^(-5))` and of the two series `∑ cos (kθ) x^k / k =
-(1/2) log (1 - 2x cos θ + x²)` (`hasSum_cos_pow_div`, the real part of the series of
`-log (1 - x e^(iθ))`) at `θ = 2π/5, 4π/5`, where `cos (2π/5) = (√5 - 1)/4` and
`cos (4π/5) = -(√5 + 1)/4`.
-/

@[expose] public section

namespace PiFormula

namespace Compendium

open BaseB

/-! ## 1. The series `∑ cos (kθ) x^k / k` -/

/-- `∑_{k ≥ 1} cos (kθ) x^k / k = -(1/2) log (1 - 2x cos θ + x²)` for `|x| < 1`. -/
theorem hasSum_cos_pow_div {x : ℝ} (hx : |x| < 1) (θ : ℝ) :
    HasSum (fun k : ℕ => Real.cos (k * θ) * x ^ k / k)
      (-(1 / 2) * Real.log (1 - 2 * x * Real.cos θ + x ^ 2)) := by
  have hnz : ‖(x : ℂ) * Complex.exp (θ * Complex.I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
    exact hx
  have h := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hnz)
  have ez : ∀ k : ℕ, (((x : ℂ) * Complex.exp (θ * Complex.I)) ^ k / (k : ℂ)).re =
      Real.cos (k * θ) * x ^ k / k := by
    intro k
    have e1 : ((x : ℂ) * Complex.exp (θ * Complex.I)) ^ k / (k : ℂ) =
        ((x ^ k / k : ℝ) : ℂ) * Complex.exp (((k * θ : ℝ) : ℂ) * Complex.I) := by
      rw [mul_pow, ← Complex.exp_nat_mul, ← mul_assoc]
      push_cast
      ring
    rw [e1, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    ring
  have hn : ‖1 - (x : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 =
      1 - 2 * x * Real.cos θ + x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re, Complex.sub_im, Complex.one_im, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im]
    linear_combination x ^ 2 * Real.sin_sq_add_cos_sq θ
  have hval : (-Complex.log (1 - (x : ℂ) * Complex.exp (θ * Complex.I))).re =
      -(1 / 2) * Real.log (1 - 2 * x * Real.cos θ + x ^ 2) := by
    rw [Complex.neg_re, Complex.log_re, ← hn, Real.log_pow]
    push_cast
    ring
  rw [hval] at h
  exact h.congr_fun fun k => (ez k).symm

/-! ## 2. The cosines of the multiples of `2π/5` -/

theorem sqrt_five_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- `cos (2π/5) = (√5 - 1)/4`. -/
theorem cos_two_pi_div_five : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  linear_combination (1 / 8 : ℝ) * sqrt_five_sq

/-- `cos (4π/5) = -(√5 + 1)/4`. -/
theorem cos_four_pi_div_five : Real.cos (4 * Real.pi / 5) = -(Real.sqrt 5 + 1) / 4 := by
  rw [show 4 * Real.pi / 5 = Real.pi - Real.pi / 5 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_five]
  ring

/-- `cos ((5j + r) θ) = cos (rθ)` when `5θ` is a multiple of `2π`. -/
theorem cos_five_mul_add (j r m : ℕ) (θ : ℝ) (hθ : 5 * θ = m * (2 * Real.pi)) :
    Real.cos (((5 * j + r : ℕ) : ℝ) * θ) = Real.cos (r * θ) := by
  have e : ((5 * j + r : ℕ) : ℝ) * θ = r * θ + ((j * m : ℕ) : ℝ) * (2 * Real.pi) := by
    push_cast
    linear_combination (j : ℝ) * hθ
  rw [e, Real.cos_add_nat_mul_two_pi]

/-- The values of `cos (2πr/5)` for `r = 1, …, 5`. -/
theorem cos_two_pi_div_five_mul :
    Real.cos (((1 : ℕ) : ℝ) * (2 * Real.pi / 5)) = (Real.sqrt 5 - 1) / 4 ∧
    Real.cos (((2 : ℕ) : ℝ) * (2 * Real.pi / 5)) = -(Real.sqrt 5 + 1) / 4 ∧
    Real.cos (((3 : ℕ) : ℝ) * (2 * Real.pi / 5)) = -(Real.sqrt 5 + 1) / 4 ∧
    Real.cos (((4 : ℕ) : ℝ) * (2 * Real.pi / 5)) = (Real.sqrt 5 - 1) / 4 ∧
    Real.cos (((5 : ℕ) : ℝ) * (2 * Real.pi / 5)) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.cast_one, one_mul, cos_two_pi_div_five]
  · rw [show ((2 : ℕ) : ℝ) * (2 * Real.pi / 5) = 4 * Real.pi / 5 by push_cast; ring,
      cos_four_pi_div_five]
  · rw [show ((3 : ℕ) : ℝ) * (2 * Real.pi / 5) = 2 * Real.pi - 4 * Real.pi / 5 by
      push_cast; ring, Real.cos_two_pi_sub, cos_four_pi_div_five]
  · rw [show ((4 : ℕ) : ℝ) * (2 * Real.pi / 5) = 2 * Real.pi - 2 * Real.pi / 5 by
      push_cast; ring, Real.cos_two_pi_sub, cos_two_pi_div_five]
  · rw [show ((5 : ℕ) : ℝ) * (2 * Real.pi / 5) = 2 * Real.pi by push_cast; ring,
      Real.cos_two_pi]

/-- The values of `cos (4πr/5)` for `r = 1, …, 5`. -/
theorem cos_four_pi_div_five_mul :
    Real.cos (((1 : ℕ) : ℝ) * (4 * Real.pi / 5)) = -(Real.sqrt 5 + 1) / 4 ∧
    Real.cos (((2 : ℕ) : ℝ) * (4 * Real.pi / 5)) = (Real.sqrt 5 - 1) / 4 ∧
    Real.cos (((3 : ℕ) : ℝ) * (4 * Real.pi / 5)) = (Real.sqrt 5 - 1) / 4 ∧
    Real.cos (((4 : ℕ) : ℝ) * (4 * Real.pi / 5)) = -(Real.sqrt 5 + 1) / 4 ∧
    Real.cos (((5 : ℕ) : ℝ) * (4 * Real.pi / 5)) = 1 := by
  have h2 := Real.cos_add_nat_mul_two_pi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.cast_one, one_mul, cos_four_pi_div_five]
  · rw [show ((2 : ℕ) : ℝ) * (4 * Real.pi / 5) = 2 * Real.pi - 2 * Real.pi / 5 by
      push_cast; ring, Real.cos_two_pi_sub, cos_two_pi_div_five]
  · rw [show ((3 : ℕ) : ℝ) * (4 * Real.pi / 5) = 2 * Real.pi / 5 + ((1 : ℕ) : ℝ) * (2 * Real.pi)
      by push_cast; ring, h2, cos_two_pi_div_five]
  · rw [show ((4 : ℕ) : ℝ) * (4 * Real.pi / 5) =
      (2 * Real.pi - 4 * Real.pi / 5) + ((1 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring, h2,
      Real.cos_two_pi_sub, cos_four_pi_div_five]
  · rw [show ((5 : ℕ) : ℝ) * (4 * Real.pi / 5) = 0 + ((2 : ℕ) : ℝ) * (2 * Real.pi) by
      push_cast; ring, h2, Real.cos_zero]

/-! ## 3. Formula (87) -/

/-- The term of the series of formula (87): `w(k) 5^(-k) / k` with
`w(k) = 1/2 - (1/2) [5 ∣ k] - (1/√5) (cos (2πk/5) - cos (4πk/5))`, which is 1 for
`k ≡ 2, 3 (mod 5)` and 0 otherwise. -/
noncomputable def term87 (k : ℕ) : ℝ :=
  1 / 2 * ((1 / 5 : ℝ) ^ k / k) - 1 / 2 * (if 5 ∣ k then (1 / ((5 : ℕ) : ℝ)) ^ k / (k : ℝ) else 0)
    - 1 / Real.sqrt 5 * (Real.cos (k * (2 * Real.pi / 5)) * (1 / 5 : ℝ) ^ k / k
      - Real.cos (k * (4 * Real.pi / 5)) * (1 / 5 : ℝ) ^ k / k)

/-- The value of the series of `term87`. -/
noncomputable def value87 : ℝ :=
  1 / 2 * -Real.log (1 - 1 / 5) - 1 / 2 * logTerm 5 5
    - 1 / Real.sqrt 5 * (-(1 / 2) * Real.log (1 - 2 * (1 / 5) * Real.cos (2 * Real.pi / 5)
        + (1 / 5) ^ 2)
      - -(1 / 2) * Real.log (1 - 2 * (1 / 5) * Real.cos (4 * Real.pi / 5) + (1 / 5) ^ 2))

theorem hasSum_term87 : HasSum term87 value87 := by
  have hx : |(1 / 5 : ℝ)| < 1 := by
    rw [abs_of_pos] <;> norm_num
  exact (((hasSum_pow_div hx).mul_left (1 / 2)).sub
    ((hasSum_logTerm (b := 5) (by norm_num) (d := 5) (by norm_num)).mul_left (1 / 2))).sub
    (((hasSum_cos_pow_div hx (2 * Real.pi / 5)).sub
      (hasSum_cos_pow_div hx (4 * Real.pi / 5))).mul_left (1 / Real.sqrt 5))

/-- The terms of `term87` at `k = 5j + r`, `r = 1, …, 5`. -/
theorem term87_values (j : ℕ) :
    term87 (5 * j + 1) = 0 ∧
    term87 (5 * j + 2) = (1 / 5 : ℝ) ^ (5 * j + 2) / ((5 * j + 2 : ℕ) : ℝ) ∧
    term87 (5 * j + 3) = (1 / 5 : ℝ) ^ (5 * j + 3) / ((5 * j + 3 : ℕ) : ℝ) ∧
    term87 (5 * j + 4) = 0 ∧ term87 (5 * j + 5) = 0 := by
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hinv : 1 / Real.sqrt 5 * Real.sqrt 5 = 1 := by
    field_simp
  have t1 : 5 * (2 * Real.pi / 5) = ((1 : ℕ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  have t2 : 5 * (4 * Real.pi / 5) = ((2 : ℕ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  obtain ⟨a1, a2, a3, a4, a5⟩ := cos_two_pi_div_five_mul
  obtain ⟨b1, b2, b3, b4, b5⟩ := cos_four_pi_div_five_mul
  have n1 : ¬ 5 ∣ 5 * j + 1 := by omega
  have n2 : ¬ 5 ∣ 5 * j + 2 := by omega
  have n3 : ¬ 5 ∣ 5 * j + 3 := by omega
  have n4 : ¬ 5 ∣ 5 * j + 4 := by omega
  have n5 : 5 ∣ 5 * j + 5 := ⟨j + 1, by ring⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [term87, ite_eq_right n1, cos_five_mul_add j 1 1 _ t1, cos_five_mul_add j 1 2 _ t2,
      a1, b1]
    linear_combination (-(1 / 2 : ℝ) * ((1 / 5 : ℝ) ^ (5 * j + 1) /
      ((5 * j + 1 : ℕ) : ℝ))) * hinv
  · rw [term87, ite_eq_right n2, cos_five_mul_add j 2 1 _ t1, cos_five_mul_add j 2 2 _ t2,
      a2, b2]
    linear_combination ((1 / 2 : ℝ) * ((1 / 5 : ℝ) ^ (5 * j + 2) /
      ((5 * j + 2 : ℕ) : ℝ))) * hinv
  · rw [term87, ite_eq_right n3, cos_five_mul_add j 3 1 _ t1, cos_five_mul_add j 3 2 _ t2,
      a3, b3]
    linear_combination ((1 / 2 : ℝ) * ((1 / 5 : ℝ) ^ (5 * j + 3) /
      ((5 * j + 3 : ℕ) : ℝ))) * hinv
  · rw [term87, ite_eq_right n4, cos_five_mul_add j 4 1 _ t1, cos_five_mul_add j 4 2 _ t2,
      a4, b4]
    linear_combination (-(1 / 2 : ℝ) * ((1 / 5 : ℝ) ^ (5 * j + 4) /
      ((5 * j + 4 : ℕ) : ℝ))) * hinv
  · rw [term87, ite_eq_left n5, cos_five_mul_add j 5 1 _ t1, cos_five_mul_add j 5 2 _ t2,
      a5, b5]
    push_cast
    ring

/-- The value of the series in closed form. -/
theorem value87_eq : 25 / 2 * Real.log (781 / 256 *
    ((57 - 5 * Real.sqrt 5) / (57 + 5 * Real.sqrt 5)) ^ Real.sqrt 5) = 125 * value87 := by
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hs3 : Real.sqrt 5 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hm : 0 < 57 - 5 * Real.sqrt 5 := by linarith
  have hp : 0 < 57 + 5 * Real.sqrt 5 := by linarith
  have hinv : 1 / Real.sqrt 5 = Real.sqrt 5 / 5 := by
    rw [div_eq_div_iff hs.ne' (by norm_num)]
    linear_combination -sqrt_five_sq
  have eA : 1 - 2 * (1 / 5) * Real.cos (2 * Real.pi / 5) + (1 / 5 : ℝ) ^ 2 =
      (57 - 5 * Real.sqrt 5) / 50 := by
    rw [cos_two_pi_div_five]
    ring
  have eB : 1 - 2 * (1 / 5) * Real.cos (4 * Real.pi / 5) + (1 / 5 : ℝ) ^ 2 =
      (57 + 5 * Real.sqrt 5) / 50 := by
    rw [cos_four_pi_div_five]
    ring
  have t5 : logTerm 5 5 = Real.log 5 - Real.log 3124 / 5 := by
    exact_mod_cast logTerm_eq (b := 5) (d := 5) (m := 3124) (by norm_num) (by norm_num)
      (by norm_num)
  have l4 : Real.log (1 - 1 / 5) = 2 * Real.log 2 - Real.log 5 := by
    rw [show (1 - 1 / 5 : ℝ) = 2 ^ 2 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  have l3124 : Real.log 3124 = 2 * Real.log 2 + Real.log 781 := by
    rw [show (3124 : ℝ) = 2 ^ 2 * 781 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  have l256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [value87, eA, eB, t5, l4, l3124, Real.log_mul (by norm_num) (by positivity),
    Real.log_rpow (by positivity), Real.log_div (by norm_num) (by norm_num), l256,
    Real.log_div hm.ne' hp.ne', Real.log_div hm.ne' (by norm_num),
    Real.log_div hp.ne' (by norm_num), hinv]
  ring

/-- **Formula (87)** of the Compendium (page 26):
`(25/2) log ((781/256) ((57 - 5√5)/(57 + 5√5))^√5) = P(1, 5^5, 5, (0, 5, 1, 0, 0))`. -/
theorem formula_87 : BaileyFormula (25 / 2 * Real.log (781 / 256 *
    ((57 - 5 * Real.sqrt 5) / (57 + 5 * Real.sqrt 5)) ^ Real.sqrt 5)) 1 5 5 5
    ![0, 5, 1, 0, 0] := by
  have h0 : term87 0 = 0 := by
    simp [term87]
  have hs := (hasSum_blocks_iff (n := 5) (by norm_num) hasSum_term87.summable h0 _).2
    hasSum_term87
  have hb : HasBaileyValue 5 5 5 ![0, 5, 1, 0, 0] (125 * value87) := by
    refine (hs.mul_left 125).congr_fun fun j => ?_
    obtain ⟨v1, v2, v3, v4, v5⟩ := term87_values j
    have e5 : (5 : ℝ) ^ (5 * j) ≠ 0 := by positivity
    rw [Fin.sum_univ_five]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, add_zero]
    rw [show (3 : Fin 5).val = 3 from rfl, show (4 : Fin 5).val = 4 from rfl, v1, v2, v3, v4,
      v5]
    simp only [BaseB.baileyBlock, Fin.sum_univ_five, one_div_pow, pow_add]
    simp
    field_simp
    ring
  refine hb.formula ?_
  rw [one_mul, value87_eq]

end Compendium

end PiFormula
