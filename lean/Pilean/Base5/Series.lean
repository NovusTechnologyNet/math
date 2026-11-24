/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Base5.Defs

/-!
# Base 5: the series of the class F5 as combinations of logarithms

The class F5 is the set of series

  `S(ρ) = ∑_{k ≥ 1} ρ(k) 5^(-⌊k/2⌋) / k`,   `ρ` rational and periodic.

With `t = √5` one has `t² = 5`, so `ρ(k) 5^(-⌊k/2⌋) = c(k) t^(-k)` for the twisted pattern
`c(k) = ρ(k) t^(k mod 2)`, which has every even period of `ρ` as a period. As in base 2
(`Fourier.lean`) and base 3 (`Base3/Series.lean`), finite Fourier inversion gives

  `S(ρ) = ∑_{r^N = 1} d_r Log(1 - r/t)`                      (`series_eq_logs5`).

Base 3 uses `t = √-3` and needs a sign `(-1)^⌊k/2⌋` in the twist; here `t² = +5` and there is
no sign, so the period only has to be even.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace Base5

/-! ## 1. The numbers `1 - r/t` -/

theorem w5_eq (r : ℂ) : 1 - r / t5 = (t5 - r) / t5 := by
  rw [sub_div, div_self t5_ne_zero]

theorem w5_ne_zero {r : ℂ} (hr : IsOfFinOrder r) : 1 - r / t5 ≠ 0 := by
  rw [w5_eq]
  exact div_ne_zero (t5_sub_ne_zero (norm_root hr)) t5_ne_zero

/-! ## 2. The terms of the series -/

theorem seriesTerm5_add (ρ ρ' : ℕ → ℚ) (k : ℕ) :
    seriesTerm5 (ρ + ρ') k = seriesTerm5 ρ k + seriesTerm5 ρ' k := by
  simp only [seriesTerm5, Pi.add_apply]
  push_cast
  ring

theorem seriesTerm5_smul (q : ℚ) (ρ : ℕ → ℚ) (k : ℕ) :
    seriesTerm5 (q • ρ) k = q * seriesTerm5 ρ k := by
  simp only [seriesTerm5, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem seriesTerm5_sub (ρ ρ' : ℕ → ℚ) (k : ℕ) :
    seriesTerm5 (ρ - ρ') k = seriesTerm5 ρ k - seriesTerm5 ρ' k := by
  simp only [seriesTerm5, Pi.sub_apply]
  push_cast
  ring

theorem seriesTerm5_zero : seriesTerm5 0 = fun _ => 0 := by
  funext k
  simp [seriesTerm5]

theorem isF5Value_zero : IsF5Value 0 := by
  refine ⟨1, 0, one_pos, fun _ => rfl, ?_⟩
  rw [seriesTerm5_zero]
  exact hasSum_zero

/-! ## 3. The twisted pattern and the series as a combination of logarithms -/

/-- `c(k) = ρ(k) t^(k mod 2)`, so that `ρ(k) 5^(-⌊k/2⌋) = c(k) t^(-k)`. -/
noncomputable def twist5 (ρ : ℕ → ℚ) (k : ℕ) : ℂ := (ρ k : ℂ) * t5 ^ (k % 2)

theorem t5_inv_pow_mul (m e : ℕ) : t5⁻¹ ^ (2 * m + e) * t5 ^ e = 1 / 5 ^ m := by
  have h1 : t5⁻¹ ^ e * t5 ^ e = 1 := by rw [← mul_pow, inv_mul_cancel₀ t5_ne_zero, one_pow]
  have h2 : t5⁻¹ ^ 2 = 1 / 5 := by
    rw [inv_pow, t5_sq]
    norm_num
  calc t5⁻¹ ^ (2 * m + e) * t5 ^ e
      = (t5⁻¹ ^ 2) ^ m * (t5⁻¹ ^ e * t5 ^ e) := by rw [pow_add, pow_mul, mul_assoc]
    _ = 1 / 5 ^ m := by rw [h1, h2, mul_one, div_pow, one_pow]

theorem twist5_mul (ρ : ℕ → ℚ) (k : ℕ) : twist5 ρ k * t5⁻¹ ^ k = (ρ k : ℂ) / 5 ^ (k / 2) := by
  have h := t5_inv_pow_mul (k / 2) (k % 2)
  rw [Nat.div_add_mod] at h
  rw [twist5, mul_assoc, mul_comm (t5 ^ (k % 2)), h]
  ring

theorem twist5_periodic {N : ℕ} (h2 : 2 ∣ N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) (k : ℕ) :
    twist5 ρ (k + N) = twist5 ρ k := by
  obtain ⟨n, rfl⟩ := h2
  have h1 : (k + 2 * n) % 2 = k % 2 := by omega
  rw [twist5, twist5, hρ, h1]

/-- The coefficient `d_r` of `Log (1 - r/t)` in `S(ρ)`. -/
noncomputable def fourierD5 (N : ℕ) (ρ : ℕ → ℚ) (r : ℂ) : ℂ := -coeffAt N (twist5 ρ) r

/-- **The setting in base 5.** For a rational pattern `ρ` of even period `N`,
`S(ρ) = ∑_k ρ(k) 5^(-⌊k/2⌋) / k = ∑_{r^N = 1} d_r Log(1 - r/t)`, `t = √5`. -/
theorem series_eq_logs5 {N : ℕ} (hN : 0 < N) (h2 : 2 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (fun k : ℕ => (ρ k : ℂ) / 5 ^ (k / 2) / k)
      (∑ r ∈ rootsN N, fourierD5 N ρ r * Complex.log (1 - r / t5)) := by
  rw [sum_rootsN hN]
  have hc := twist5_periodic h2 hρ
  have hterm : ∀ a ∈ Finset.range N,
      HasSum (fun k : ℕ => fourierD5 N ρ (zetaN N ^ a) * -((zetaN N ^ a / t5) ^ k / k))
        (fourierD5 N ρ (zetaN N ^ a) * Complex.log (1 - zetaN N ^ a / t5)) := by
    intro a _
    have hr : ‖zetaN N ^ a‖ = 1 := norm_root (isOfFinOrder_zetaN_pow hN a)
    have h := (hasSum_taylorSeries_neg_log (norm_div_t5_lt hr)).neg
    rw [neg_neg] at h
    exact h.mul_left _
  have hfun : (fun k : ℕ => (ρ k : ℂ) / 5 ^ (k / 2) / k) = fun k : ℕ =>
      ∑ a ∈ Finset.range N, fourierD5 N ρ (zetaN N ^ a) * -((zetaN N ^ a / t5) ^ k / k) := by
    funext k
    have e : ∑ a ∈ Finset.range N,
        fourierD5 N ρ (zetaN N ^ a) * -((zetaN N ^ a / t5) ^ k / k) =
        (∑ a ∈ Finset.range N, coeffAt N (twist5 ρ) (zetaN N ^ a) * (zetaN N ^ a) ^ k)
          * t5⁻¹ ^ k / k := by
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [fourierD5]
      ring
    rw [e, fourier_inversion hN hc k, twist5_mul]
  rw [hfun]
  exact hasSum_sum hterm

/-- The same for the real series `seriesTerm5`. -/
theorem seriesTerm5_hasSum_logs {N : ℕ} (hN : 0 < N) (h2 : 2 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (fun k : ℕ => ((seriesTerm5 ρ k : ℝ) : ℂ))
      (∑ r ∈ rootsN N, fourierD5 N ρ r * Complex.log (1 - r / t5)) := by
  have h1 := series_eq_logs5 hN h2 hρ
  have e : (fun k : ℕ => (ρ k : ℂ) / 5 ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTerm5 ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTerm5]
  rwa [e] at h1

/-- The coefficients `d_r` are algebraic numbers. -/
theorem isAlgebraic_fourierD5 (N : ℕ) (ρ : ℕ → ℚ) {r : ℂ} (hr : IsOfFinOrder r) :
    IsAlgebraic ℚ (fourierD5 N ρ r) := by
  rw [fourierD5, coeffAt]
  refine IsAlgebraic.neg (IsAlgebraic.mul ?_ (isAlgebraic_sum' _ _ fun m _ => ?_))
  · rw [one_div]
    exact (isAlgebraic_natCast N).inv
  · refine IsAlgebraic.mul ?_ ((isAlgebraic_root hr).inv.pow m)
    rw [twist5]
    exact IsAlgebraic.mul (isAlgebraic_ratCast ℚ (A := ℂ) (ρ m)) (isAlgebraic_t5.pow _)

end Base5

end PiFormula
