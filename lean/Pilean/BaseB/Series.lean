/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.BaseB.Defs

/-!
# A general base `b`: the series of the class `F_b` as combinations of logarithms

The class `F_b` is the set of series

  `S(ρ) = ∑_{k ≥ 1} ρ(k) b^(-⌊k/2⌋) / k`,   `ρ` rational and periodic.

With `t = √b` one has `t² = b`, so `ρ(k) b^(-⌊k/2⌋) = c(k) t^(-k)` for the twisted pattern
`c(k) = ρ(k) t^(k mod 2)`, which has every even period of `ρ` as a period. As in base 5
(`Base5/Series.lean`), finite Fourier inversion gives, for `b ≥ 2`,

  `S(ρ) = ∑_{r^N = 1} d_r Log(1 - r/t)`                      (`series_eq_logsB`).

Nothing here depends on `b` being a square or not: when `b = c²` the number `t = c` is
rational and the statement is the same.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace BaseB

/-! ## 1. The numbers `1 - r/t` -/

theorem wB_eq {b : ℕ} (hb : 2 ≤ b) (r : ℂ) : 1 - r / tB b = (tB b - r) / tB b := by
  rw [sub_div, div_self (tB_ne_zero hb)]

theorem wB_ne_zero {b : ℕ} (hb : 2 ≤ b) {r : ℂ} (hr : IsOfFinOrder r) : 1 - r / tB b ≠ 0 := by
  rw [wB_eq hb]
  exact div_ne_zero (tB_sub_ne_zero hb (norm_root hr)) (tB_ne_zero hb)

/-! ## 2. The twisted pattern and the series as a combination of logarithms -/

/-- `c(k) = ρ(k) t^(k mod 2)`, so that `ρ(k) b^(-⌊k/2⌋) = c(k) t^(-k)`. -/
noncomputable def twistB (b : ℕ) (ρ : ℕ → ℚ) (k : ℕ) : ℂ := (ρ k : ℂ) * tB b ^ (k % 2)

theorem tB_inv_pow_mul {b : ℕ} (hb : 2 ≤ b) (m e : ℕ) :
    (tB b)⁻¹ ^ (2 * m + e) * tB b ^ e = 1 / (b : ℂ) ^ m := by
  have h1 : (tB b)⁻¹ ^ e * tB b ^ e = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (tB_ne_zero hb), one_pow]
  have h2 : (tB b)⁻¹ ^ 2 = 1 / (b : ℂ) := by
    rw [inv_pow, tB_sq, one_div]
  calc (tB b)⁻¹ ^ (2 * m + e) * tB b ^ e
      = ((tB b)⁻¹ ^ 2) ^ m * ((tB b)⁻¹ ^ e * tB b ^ e) := by rw [pow_add, pow_mul, mul_assoc]
    _ = 1 / (b : ℂ) ^ m := by rw [h1, h2, mul_one, div_pow, one_pow]

theorem twistB_mul {b : ℕ} (hb : 2 ≤ b) (ρ : ℕ → ℚ) (k : ℕ) :
    twistB b ρ k * (tB b)⁻¹ ^ k = (ρ k : ℂ) / (b : ℂ) ^ (k / 2) := by
  have h := tB_inv_pow_mul hb (k / 2) (k % 2)
  rw [Nat.div_add_mod] at h
  rw [twistB, mul_assoc, mul_comm (tB b ^ (k % 2)), h]
  ring

theorem twistB_periodic (b : ℕ) {N : ℕ} (h2 : 2 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) (k : ℕ) : twistB b ρ (k + N) = twistB b ρ k := by
  obtain ⟨n, rfl⟩ := h2
  have h1 : (k + 2 * n) % 2 = k % 2 := by omega
  rw [twistB, twistB, hρ, h1]

/-- The coefficient `d_r` of `Log (1 - r/t)` in `S(ρ)`. -/
noncomputable def fourierDB (b N : ℕ) (ρ : ℕ → ℚ) (r : ℂ) : ℂ := -coeffAt N (twistB b ρ) r

/-- **The setting in base `b`.** For a rational pattern `ρ` of even period `N`,
`S(ρ) = ∑_k ρ(k) b^(-⌊k/2⌋) / k = ∑_{r^N = 1} d_r Log(1 - r/t)`, `t = √b`. -/
theorem series_eq_logsB {b : ℕ} (hb : 2 ≤ b) {N : ℕ} (hN : 0 < N) (h2 : 2 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (fun k : ℕ => (ρ k : ℂ) / (b : ℂ) ^ (k / 2) / k)
      (∑ r ∈ rootsN N, fourierDB b N ρ r * Complex.log (1 - r / tB b)) := by
  rw [sum_rootsN hN]
  have hc := twistB_periodic b h2 hρ
  have hterm : ∀ a ∈ Finset.range N,
      HasSum (fun k : ℕ => fourierDB b N ρ (zetaN N ^ a) * -((zetaN N ^ a / tB b) ^ k / k))
        (fourierDB b N ρ (zetaN N ^ a) * Complex.log (1 - zetaN N ^ a / tB b)) := by
    intro a _
    have hr : ‖zetaN N ^ a‖ = 1 := norm_root (isOfFinOrder_zetaN_pow hN a)
    have h := (hasSum_taylorSeries_neg_log (norm_div_tB_lt hb hr)).neg
    rw [neg_neg] at h
    exact h.mul_left _
  have hfun : (fun k : ℕ => (ρ k : ℂ) / (b : ℂ) ^ (k / 2) / k) = fun k : ℕ =>
      ∑ a ∈ Finset.range N,
        fourierDB b N ρ (zetaN N ^ a) * -((zetaN N ^ a / tB b) ^ k / k) := by
    funext k
    have e : ∑ a ∈ Finset.range N,
        fourierDB b N ρ (zetaN N ^ a) * -((zetaN N ^ a / tB b) ^ k / k) =
        (∑ a ∈ Finset.range N, coeffAt N (twistB b ρ) (zetaN N ^ a) * (zetaN N ^ a) ^ k)
          * (tB b)⁻¹ ^ k / k := by
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [fourierDB]
      ring
    rw [e, fourier_inversion hN hc k, twistB_mul hb]
  rw [hfun]
  exact hasSum_sum hterm

/-- The same for the real series `seriesTermB`. -/
theorem seriesTermB_hasSum_logs {b : ℕ} (hb : 2 ≤ b) {N : ℕ} (hN : 0 < N) (h2 : 2 ∣ N)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (fun k : ℕ => ((seriesTermB b ρ k : ℝ) : ℂ))
      (∑ r ∈ rootsN N, fourierDB b N ρ r * Complex.log (1 - r / tB b)) := by
  have h1 := series_eq_logsB hb hN h2 hρ
  have e : (fun k : ℕ => (ρ k : ℂ) / (b : ℂ) ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTermB b ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTermB]
  rwa [e] at h1

/-- The coefficients `d_r` are algebraic numbers. -/
theorem isAlgebraic_fourierDB (b N : ℕ) (ρ : ℕ → ℚ) {r : ℂ} (hr : IsOfFinOrder r) :
    IsAlgebraic ℚ (fourierDB b N ρ r) := by
  rw [fourierDB, coeffAt]
  refine IsAlgebraic.neg (IsAlgebraic.mul ?_ (isAlgebraic_sum' _ _ fun m _ => ?_))
  · rw [one_div]
    exact (isAlgebraic_natCast N).inv
  · refine IsAlgebraic.mul ?_ ((isAlgebraic_root hr).inv.pow m)
    rw [twistB]
    exact IsAlgebraic.mul (isAlgebraic_ratCast ℚ (A := ℂ) (ρ m)) ((isAlgebraic_tB b).pow _)

end BaseB

end PiFormula
