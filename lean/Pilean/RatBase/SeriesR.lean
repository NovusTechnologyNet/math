/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.RatBase.ClassDefs
public import Pilean.BaseB.SubseriesAux

/-!
# A rational base `p/q`: the series of the class as combinations of logarithms

The class `F_(p/q)` (`p > q ≥ 1`) is the set of series

  `S(ρ) = ∑_{k ≥ 1} ρ(k) (q/p)^⌊k/2⌋ / k`,   `ρ` rational and periodic.

Put `u = √(pq)` (the number `BaseB.tB (p * q)`) and `x = q/u = √(q/p)` (`xRat p q`), so that
`x² = q/p` and `0 < x < 1`. Then `ρ(k) (q/p)^⌊k/2⌋ = c(k) x^k` for the twisted pattern
`c(k) = ρ(k) x^(-(k mod 2))` (`twistRat`), which has every even period of `ρ` as a period, and
by `BaseB.hasSum_periodic_logs`

  `S(ρ) = ∑_{r^N = 1} d_r Log(1 - r x)`,   `1 - r x = (u - q r) / u`
  (`seriesTermRat_hasSum_logs`, `wR_eq`).

For `q = 1` these are the objects of `BaseB/Series.lean`: `x = 1/√p`.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace RatBase

/-! ## 1. The point `x = √(q/p)` and the numbers `1 - r x` -/

/-- `x = √(q/p)`, written `q/√(pq)`: the point at which the power series is taken. -/
noncomputable def xRat (p q : ℕ) : ℂ := (q : ℂ) / BaseB.tB (p * q)

theorem two_le_mul_of_lt {p q : ℕ} (hq : 0 < q) (hqp : q < p) : 2 ≤ p * q :=
  le_trans (by omega : 2 ≤ p * 1) (Nat.mul_le_mul_left p hq)

theorem tB_mul_ne_zero {p q : ℕ} (hq : 0 < q) (hqp : q < p) : BaseB.tB (p * q) ≠ 0 :=
  BaseB.tB_ne_zero (two_le_mul_of_lt hq hqp)

theorem xRat_ne_zero {p q : ℕ} (hq : 0 < q) (hqp : q < p) : xRat p q ≠ 0 :=
  div_ne_zero (Nat.cast_ne_zero.2 hq.ne') (tB_mul_ne_zero hq hqp)

/-- `x² = q/p`. -/
theorem xRat_sq {p q : ℕ} (hq : 0 < q) (hqp : q < p) : xRat p q ^ 2 = (q : ℂ) / (p : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  rw [xRat, div_pow, BaseB.tB_sq, Nat.cast_mul]
  field_simp

/-- `|x| < 1`, since `q < p`. -/
theorem norm_xRat_lt_one {p q : ℕ} (hq : 0 < q) (hqp : q < p) : ‖xRat p q‖ < 1 := by
  have hpos : (0 : ℝ) < Real.sqrt ((p * q : ℕ) : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast Nat.mul_pos (by omega) hq)
  rw [xRat, norm_div, BaseB.norm_tB, Complex.norm_natCast, div_lt_one hpos,
    Real.lt_sqrt (Nat.cast_nonneg q)]
  exact_mod_cast (by nlinarith : q ^ 2 < p * q)

/-- `1 - r x = (u - q r)/u`. -/
theorem wR_eq {p q : ℕ} (hq : 0 < q) (hqp : q < p) (r : ℂ) :
    1 - r * xRat p q = (BaseB.tB (p * q) - (q : ℂ) * r) / BaseB.tB (p * q) := by
  rw [xRat, sub_div, div_self (tB_mul_ne_zero hq hqp)]
  ring

theorem wR_ne_zero {p q : ℕ} (hq : 0 < q) (hqp : q < p) {r : ℂ} (hr : IsOfFinOrder r) :
    1 - r * xRat p q ≠ 0 := by
  intro h
  have h1 : ‖r * xRat p q‖ < 1 := by
    rw [norm_mul, norm_root hr, one_mul]
    exact norm_xRat_lt_one hq hqp
  rw [← sub_eq_zero.1 h, norm_one] at h1
  exact lt_irrefl _ h1

/-- `u - q r ≠ 0` for a root of unity `r`. -/
theorem tB_sub_mul_ne_zero {p q : ℕ} (hq : 0 < q) (hqp : q < p) {r : ℂ} (hr : IsOfFinOrder r) :
    BaseB.tB (p * q) - (q : ℂ) * r ≠ 0 := fun h0 =>
  wR_ne_zero hq hqp hr (by rw [wR_eq hq hqp, h0, zero_div])

/-- `u - q r` is an algebraic integer. -/
theorem isIntegral_tB_sub_mul (p q : ℕ) {r : ℂ} (hr : IsOfFinOrder r) :
    IsIntegral ℤ (BaseB.tB (p * q) - (q : ℂ) * r) :=
  (BaseB.isIntegral_tB _).sub ((isIntegral_natCast' q).mul (isIntegral_of_finOrder hr))

theorem isAlgebraic_xRat (p q : ℕ) : IsAlgebraic ℚ (xRat p q) := by
  rw [xRat, div_eq_mul_inv]
  exact (isAlgebraic_natCast q).mul (BaseB.isAlgebraic_tB _).inv

/-! ## 2. The twisted pattern and the series as a combination of logarithms -/

/-- `c(k) = ρ(k) x^(-(k mod 2))`, so that `ρ(k) (q/p)^⌊k/2⌋ = c(k) x^k`. -/
noncomputable def twistRat (p q : ℕ) (ρ : ℕ → ℚ) (k : ℕ) : ℂ :=
  (ρ k : ℂ) * (xRat p q)⁻¹ ^ (k % 2)

theorem twistRat_mul {p q : ℕ} (hq : 0 < q) (hqp : q < p) (ρ : ℕ → ℚ) (k : ℕ) :
    twistRat p q ρ k * xRat p q ^ k = (ρ k : ℂ) * ((q : ℂ) / (p : ℂ)) ^ (k / 2) := by
  have h1 : (xRat p q)⁻¹ ^ (k % 2) * xRat p q ^ (k % 2) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (xRat_ne_zero hq hqp), one_pow]
  have h2 : xRat p q ^ k = (xRat p q ^ 2) ^ (k / 2) * xRat p q ^ (k % 2) := by
    conv_lhs => rw [← Nat.div_add_mod k 2]
    rw [pow_add, pow_mul]
  rw [twistRat, h2, xRat_sq hq hqp]
  linear_combination ((ρ k : ℂ) * ((q : ℂ) / (p : ℂ)) ^ (k / 2)) * h1

theorem twistRat_periodic (p q : ℕ) {N : ℕ} (h2 : 2 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) (k : ℕ) : twistRat p q ρ (k + N) = twistRat p q ρ k := by
  obtain ⟨n, rfl⟩ := h2
  have h1 : (k + 2 * n) % 2 = k % 2 := by omega
  rw [twistRat, twistRat, hρ, h1]

/-- The coefficient `d_r` of `Log (1 - r x)` in `S(ρ)`. -/
noncomputable def fourierDRat (p q N : ℕ) (ρ : ℕ → ℚ) (r : ℂ) : ℂ :=
  -coeffAt N (twistRat p q ρ) r

/-- **The setting in the base `p/q`.** For a rational pattern `ρ` of even period `N`,
`S(ρ) = ∑_k ρ(k) (q/p)^⌊k/2⌋ / k = ∑_{r^N = 1} d_r Log(1 - r x)`, `x = √(q/p)`. -/
theorem seriesTermRat_hasSum_logs {p q : ℕ} (hq : 0 < q) (hqp : q < p) {N : ℕ} (hN : 0 < N)
    (h2 : 2 ∣ N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (fun k : ℕ => ((seriesTermRat p q ρ k : ℝ) : ℂ))
      (∑ r ∈ rootsN N, fourierDRat p q N ρ r * Complex.log (1 - r * xRat p q)) := by
  have h := BaseB.hasSum_periodic_logs hN (twistRat_periodic p q h2 hρ)
    (norm_xRat_lt_one hq hqp)
  have e : (fun k : ℕ => twistRat p q ρ k * xRat p q ^ k / k) =
      fun k : ℕ => ((seriesTermRat p q ρ k : ℝ) : ℂ) := by
    funext k
    rw [twistRat_mul hq hqp, seriesTermRat]
    push_cast
    rfl
  rw [e] at h
  exact h

/-- The coefficients `d_r` are algebraic numbers. -/
theorem isAlgebraic_fourierDRat (p q N : ℕ) (ρ : ℕ → ℚ) {r : ℂ} (hr : IsOfFinOrder r) :
    IsAlgebraic ℚ (fourierDRat p q N ρ r) := by
  rw [fourierDRat, coeffAt]
  refine IsAlgebraic.neg (IsAlgebraic.mul ?_ (isAlgebraic_sum' _ _ fun m _ => ?_))
  · rw [one_div]
    exact (isAlgebraic_natCast N).inv
  · refine IsAlgebraic.mul ?_ ((isAlgebraic_root hr).inv.pow m)
    rw [twistRat]
    exact IsAlgebraic.mul (isAlgebraic_ratCast ℚ (A := ℂ) (ρ m))
      ((isAlgebraic_xRat p q).inv.pow _)

end RatBase

end PiFormula
