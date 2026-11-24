/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.OkadaDefs
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The value of `∑ f(n)/n` as a linear form in logarithms

`okadaFourierLimit : OkadaFourierLimit`: for `f : ℤ/q → ℚ` with `∑_r f(r) = 0`, the partial
sums of `∑_{n ≥ 1} f(n)/n` tend to `-∑_{a ≠ 0} f^(a) Log(1 - ζ^a)`, where `ζ = e^(2πi/q)` and
`f^(a) = (1/q) ∑_r f(r) ζ^(-ar)`.

The steps:

* `tendsto_circle_log`: for `|z| = 1`, `z ≠ 1`, the partial sums of `∑_{n ≥ 1} z^n/n` tend to
  `-Log(1 - z)`. The series converges by Dirichlet's test (`exists_limit_circle`); its sum is
  the limit of `-Log(1 - z x)` as `x → 1⁻` by Abel's limit theorem, and `Log` is continuous at
  `1 - z`, which has positive real part.
* `fourier_inversion_zmod`: `f(n) = ∑_a f^(a) ζ^(a n)`.
* The term `a = 0` vanishes because `f^(0) = (1/q) ∑_r f(r) = 0`.
-/

@[expose] public section

open scoped BigOperators

open Filter Finset

namespace PiFormula

namespace Erdos

namespace Okada

/-! ## 1. The series `∑ z^n/n` on the unit circle -/

theorem one_sub_mem_slitPlane {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    1 - z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  rw [not_or, not_lt, not_not] at hcon
  obtain ⟨hre, him⟩ := hcon
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im] at hre him
  have him' : z.im = 0 := by linarith
  have hsq : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hz]
    norm_num
  rw [him'] at hsq
  have hre1 : z.re = 1 := by nlinarith
  exact hz1 (Complex.ext (by rw [hre1, Complex.one_re]) (by rw [him', Complex.one_im]))

/-- Dirichlet's test: for `|z| = 1`, `z ≠ 1`, the series `∑ z^n/n` converges. -/
theorem exists_limit_circle {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ l : ℂ, Tendsto (fun N : ℕ => ∑ n ∈ range N, z ^ n / (n : ℂ)) atTop (nhds l) := by
  have hanti : Antitone (fun i : ℕ => 1 / max (i : ℝ) 1) := by
    intro i j hij
    exact one_div_le_one_div_of_le (lt_max_of_lt_right one_pos)
      (max_le_max (Nat.cast_le.2 hij) le_rfl)
  have hzero : Tendsto (fun i : ℕ => 1 / max (i : ℝ) 1) atTop (nhds 0) := by
    refine (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with i hi
    rw [max_eq_left (by exact_mod_cast hi)]
  have hb : ∀ n : ℕ, ‖∑ i ∈ range n, z ^ i‖ ≤ 2 / ‖z - 1‖ := by
    intro n
    rw [geom_sum_eq hz1, norm_div]
    have h1 : ‖z ^ n - 1‖ ≤ 2 := by
      calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by
          rw [norm_pow, hz, one_pow, norm_one]
          norm_num
    exact div_le_div_of_nonneg_right h1 (norm_nonneg _)
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete
    (hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero hb)
  refine ⟨l - 1, (hl.sub_const 1).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN,
    Finset.sum_eq_sum_Ico_succ_bot hN]
  have hterm : ∀ i ∈ Ico (0 + 1) N, (1 / max (i : ℝ) 1) • z ^ i = z ^ i / (i : ℂ) := by
    intro i hi
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (mem_Ico.1 hi).1
    rw [max_eq_left hi1, Complex.real_smul]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm]
  simp only [Nat.cast_zero, max_eq_right zero_le_one, div_one, pow_zero, one_smul, div_zero]
  ring

/-- For `|z| = 1`, `z ≠ 1`: `∑_{n ≥ 1} z^n/n = -Log(1 - z)`, as a limit of partial sums. -/
theorem tendsto_circle_log {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, z ^ n / (n : ℂ)) atTop
      (nhds (-Complex.log (1 - z))) := by
  obtain ⟨l, hl⟩ := exists_limit_circle hz hz1
  have hA := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  rw [Filter.tendsto_map'_iff] at hA
  have hcont : Tendsto (fun x : ℝ => -Complex.log (1 - z * (x : ℂ)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (-Complex.log (1 - z))) := by
    have h1 : ContinuousAt (fun x : ℝ => 1 - z * (x : ℂ)) 1 := by fun_prop
    have h2 : ContinuousAt Complex.log (1 - z * ((1 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_one, mul_one]
      exact continuousAt_clog (one_sub_mem_slitPlane hz hz1)
    have h3 : Tendsto (fun x : ℝ => -Complex.log (1 - z * (x : ℂ))) (nhds 1)
        (nhds (-Complex.log (1 - z * ((1 : ℝ) : ℂ)))) :=
      (ContinuousAt.comp (f := fun x : ℝ => 1 - z * (x : ℂ)) h2 h1).neg.tendsto
    rw [Complex.ofReal_one, mul_one] at h3
    exact h3.mono_left nhdsWithin_le_nhds
  have heq : ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Iio 1),
      ((fun w : ℂ => ∑' n : ℕ, z ^ n / (n : ℂ) * w ^ n) ∘ Complex.ofReal) x =
        -Complex.log (1 - z * (x : ℂ)) := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with x hx
    have hnorm : ‖z * (x : ℂ)‖ < 1 := by
      rw [norm_mul, hz, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
      exact hx.2
    rw [← (Complex.hasSum_taylorSeries_neg_log hnorm).tsum_eq]
    simp only [Function.comp_apply]
    refine tsum_congr fun n => ?_
    rw [mul_pow]
    ring
  rw [← tendsto_nhds_unique (hA.congr' heq) hcont]
  exact hl

/-! ## 2. Finite Fourier inversion -/

/-- `f(n) = ∑_a f^(a) ζ^(a n)`. -/
theorem fourier_inversion_zmod (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (n : ZMod q) :
    ∑ a : ZMod q, fourierCoeff q f a * ZMod.stdAddChar (a * n) = (f n : ℂ) := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne q)
  have e : ∀ a : ZMod q, fourierCoeff q f a * ZMod.stdAddChar (a * n) =
      (q : ℂ)⁻¹ * ∑ r : ZMod q, (f r : ℂ) * ZMod.stdAddChar (a * (n - r)) := by
    intro a
    unfold fourierCoeff
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  have horth : ∀ r : ZMod q, ∑ a : ZMod q, (ZMod.stdAddChar (a * (n - r)) : ℂ) =
      if n - r = 0 then (q : ℂ) else 0 := by
    intro r
    rw [AddChar.sum_mulShift (n - r) (ZMod.isPrimitive_stdAddChar q), ZMod.card]
    split_ifs <;> simp
  simp only [e]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, horth]
  rw [Finset.sum_eq_single n]
  · simp only [sub_self, ↓reduceIte]
    field_simp
  · intro r _ hr
    have hne : n - r ≠ 0 := sub_ne_zero.2 (Ne.symm hr)
    simp only [hne, ↓reduceIte, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ n) h

end Okada

open Okada

/-! ## 3. The theorem -/

/-- **The value of the series.** If `∑_r f(r) = 0`, the partial sums of `∑ f(n)/n` tend to
`-∑_{a ≠ 0} f^(a) Log(1 - ζ^a)`. -/
theorem okadaFourierLimit : OkadaFourierLimit := by
  intro q _ _ f _ hsum
  have h0 : fourierCoeff q f 0 = 0 := by
    unfold fourierCoeff
    simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
    rw [← Rat.cast_sum, hsum, Rat.cast_zero, mul_zero]
  have hterm : ∀ a : ZMod q, Tendsto (fun N : ℕ => fourierCoeff q f a *
      ∑ n ∈ range N, (ZMod.stdAddChar a : ℂ) ^ n / (n : ℂ)) atTop
      (nhds (-(if a = 0 then 0 else
        fourierCoeff q f a * Complex.log (1 - ZMod.stdAddChar a)))) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      simp only [↓reduceIte, h0, zero_mul, neg_zero]
      exact tendsto_const_nhds
    · simp only [ha, ↓reduceIte]
      have hn : ‖(ZMod.stdAddChar a : ℂ)‖ = 1 := by
        rw [ZMod.stdAddChar_apply]
        exact Circle.norm_coe _
      have h1 : (ZMod.stdAddChar a : ℂ) ≠ 1 := fun h =>
        ha (ZMod.injective_stdAddChar (by rw [AddChar.map_zero_eq_one]; exact h))
      have h2 := (tendsto_circle_log hn h1).const_mul (fourierCoeff q f a)
      rwa [mul_neg] at h2
  have hlim := tendsto_finsetSum (Finset.univ : Finset (ZMod q)) fun a _ => hterm a
  have hval : ∑ a : ZMod q, -(if a = 0 then 0 else
      fourierCoeff q f a * Complex.log (1 - ZMod.stdAddChar a)) =
      -logForm q (fourierCoeff q f) := by
    unfold logForm
    rw [Finset.sum_neg_distrib]
  rw [hval] at hlim
  refine hlim.congr fun N => ?_
  unfold partialSum
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← fourier_inversion_zmod q f (n : ZMod q), Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : (ZMod.stdAddChar (a * (n : ZMod q)) : ℂ) = ZMod.stdAddChar a ^ n := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]
  rw [e]
  ring

end Erdos

end PiFormula
