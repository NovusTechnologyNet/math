/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.BaseB.Subseries

/-!
# The sub-series lemma for a value `q π + q' log y`

**Theorem** (`subseries_log_of_kummerHom`, from Baker's theorem and `KummerHom b n`). Let `ρ`
be a rational periodic pattern, `n ≥ 1` and `n₁ = halfIfEven n`. If

  `∑_{k ≥ 1} ρ(k) b^(-⌊k/n⌋) / k = q π + q' log y`,   `q`, `q'` rational, `y > 0` rational,

then the sub-series over the `k` divisible by `n₁` already has the value `q π + q' log y`.

This is the sub-series lemma of `Subseries` (the case `q' = 0`) with one more logarithm in
the relation of Baker's theorem:

* `baker_galoisF_log`: if `∑ d_r L_r = q π + q' Λ` with `q`, `q'` rational, `Λ` and the `L_r`
  logarithms of algebraic numbers and the `d_r` in a field `F` of algebraic numbers that
  contains `i`, then `∑ σ(d_r) L_r = q π + q' Λ` for every embedding `σ` of `F` that fixes
  `i`. It follows from `baker_galoisF`: `Λ` is one more logarithm, with the rational
  coefficient `-q'`, which `σ` fixes.
* `twisted_value_log`: so for every `η` with `η^(n₁) = 1` the series with the pattern
  `η^k ρ(k)` has the value `q π + q' Λ` too.
* The mean over the `n₁` roots `η` of `X^(n₁) = 1` gives the theorem, with `Λ = log y`:
  `exp(log y) = y` is rational.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace BaseB

/-! ## 1. Baker's theorem and Galois conjugation, with one more logarithm -/

/-- **Baker's theorem and Galois conjugation, with one more logarithm.** Let
`∑ d_r L_r = q π + q' Λ` with `q`, `q'` rational, `Λ` and the `L_r` logarithms of algebraic
numbers, and the `d_r` in a field `F` of algebraic numbers that contains `i`. If `σ` is an
embedding of `F` fixing `i`, the identity remains true with `σ(d_r)` in place of `d_r`. -/
theorem baker_galoisF_log (hB : BakerTheorem) {F : IntermediateField ℚ ℂ}
    (hF : ∀ x ∈ F, IsAlgebraic ℚ x) (hI : I ∈ F) {S : Finset ℂ} {L : ℂ → ℂ}
    (hL : ∀ r ∈ S, IsAlgebraic ℚ (Complex.exp (L r))) {d : ℂ → ℂ} (hd : ∀ r ∈ S, d r ∈ F)
    {q q' : ℚ} {Λ : ℂ} (hΛ : IsAlgebraic ℚ (Complex.exp Λ)) (σ : F →ₐ[ℚ] ℂ)
    (hσI : extF σ I = I) (h : ∑ r ∈ S, d r * L r = q * Real.pi + q' * Λ) :
    ∑ r ∈ S, extF σ (d r) * L r = q * Real.pi + q' * Λ := by
  classical
  -- one more index `r₀`, with the logarithm `Λ` and the coefficient `-q'`
  obtain ⟨r₀, hr₀⟩ := Infinite.exists_notMem_finset S
  have hne : ∀ r ∈ S, r ≠ r₀ := fun r hr e => hr₀ (e ▸ hr)
  have hq'F : -(q' : ℂ) ∈ F := by
    have h1 := F.algebraMap_mem q'
    rw [eq_ratCast] at h1
    exact F.neg_mem h1
  have hL' : ∀ r ∈ insert r₀ S, IsAlgebraic ℚ (Complex.exp (Function.update L r₀ Λ r)) := by
    intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · rwa [Function.update_self]
    · rw [Function.update_of_ne (hne r hr)]
      exact hL r hr
  have hd' : ∀ r ∈ insert r₀ S, Function.update d r₀ (-(q' : ℂ)) r ∈ F := by
    intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · rwa [Function.update_self]
    · rw [Function.update_of_ne (hne r hr)]
      exact hd r hr
  have hsum : ∑ r ∈ insert r₀ S,
      Function.update d r₀ (-(q' : ℂ)) r * Function.update L r₀ Λ r = q * Real.pi := by
    have e : ∑ r ∈ S, Function.update d r₀ (-(q' : ℂ)) r * Function.update L r₀ Λ r =
        ∑ r ∈ S, d r * L r :=
      Finset.sum_congr rfl fun r hr => by
        rw [Function.update_of_ne (hne r hr), Function.update_of_ne (hne r hr)]
    rw [Finset.sum_insert hr₀, Function.update_self, Function.update_self, e, h]
    ring
  have key := baker_galoisF hB hF hI hL' hd' σ hσI hsum
  have e : ∑ r ∈ S, extF σ (Function.update d r₀ (-(q' : ℂ)) r) * Function.update L r₀ Λ r =
      ∑ r ∈ S, extF σ (d r) * L r :=
    Finset.sum_congr rfl fun r hr => by
      rw [Function.update_of_ne (hne r hr), Function.update_of_ne (hne r hr)]
  have e2 : extF σ (-(q' : ℂ)) = -(q' : ℂ) := by
    have h1 := extF_ratCast σ (-q')
    rwa [Rat.cast_neg] at h1
  rw [Finset.sum_insert hr₀, Function.update_self, Function.update_self, e, e2] at key
  linear_combination key

/-! ## 2. The twisted series have the same value -/

/-- **The twisted series** (from Baker's theorem and `KummerHom`). If the series of `ρ` is
`q π + q' Λ` with `q`, `q'` rational and `Λ` a logarithm of an algebraic number, then for
every `η` with `η^(n₁) = 1` the series of the pattern `η^k ρ(k)` is `q π + q' Λ` too. -/
theorem twisted_value_log (hB : BakerTheorem) {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n)
    (hK : KummerHom b n) {P : ℕ} (hP : 0 < P) (h4 : 4 ∣ P) (hnP : n ∣ P) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + P) = ρ k) {q q' : ℚ} {Λ : ℂ} (hΛ : IsAlgebraic ℚ (Complex.exp Λ))
    (h : HasSum (fun k : ℕ => (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k) (q * Real.pi + q' * Λ))
    {η : ℂ} (hη : η ^ halfIfEven n = 1) :
    HasSum (fun k : ℕ => η ^ k * (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k)
      (q * Real.pi + q' * Λ) := by
  have hηn : η ^ n = 1 := by
    obtain ⟨m, hm⟩ := halfIfEven_dvd n
    calc η ^ n = η ^ (halfIfEven n * m) := by rw [← hm]
      _ = 1 := by rw [pow_mul, hη, one_pow]
  have hηP : η ^ P = 1 := by
    obtain ⟨m, rfl⟩ := hnP
    rw [pow_mul, hηn, one_pow]
  obtain ⟨M, rfl⟩ := h4
  have hM : 0 < M := by omega
  obtain ⟨σ, hσc, hσz⟩ := hK (4 * M) hP η hη
  have hσc' : σ (gc (4 * M) b n) = η * cB b n := hσc _ rfl
  have hσz' : σ (gz (4 * M) b n) = zetaN (4 * M) := hσz _ rfl
  -- the series of `ρ` as a combination of logarithms
  have h0 := twisted_series_logs hb hn hP hnP (η := 1) (one_pow _) hρ
  have e0 : (fun k : ℕ => (1 : ℂ) ^ k * (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k) =
      fun k : ℕ => (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k := by
    funext k
    rw [one_pow, one_mul]
  rw [e0] at h0
  have h1 := h0.unique h
  -- `i` lies in `F` and is fixed by `σ`
  have hI : I ∈ FB (4 * M) b n := by
    rw [← zetaN_four_mul_pow hM]
    exact (FB (4 * M) b n).pow_mem (zetaN_mem_FB _ _ _) M
  have hσI : extF σ I = I := by
    have h2 := extF_coe σ (gz (4 * M) b n ^ M)
    rw [map_pow, hσz', zetaN_four_mul_pow hM] at h2
    have e : ((gz (4 * M) b n ^ M : FB (4 * M) b n) : ℂ) = I := zetaN_four_mul_pow hM
    rwa [e] at h2
  -- the coefficients lie in `F`, and the logarithms are logarithms of algebraic numbers
  have hmem : ∀ r ∈ rootsN (4 * M),
      -coeffAt (4 * M) (twistBN b n 1 ρ) r ∈ FB (4 * M) b n := by
    intro r hr
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hr
    rw [← coe_coeffFB]
    exact (FB (4 * M) b n).neg_mem (coeffFB (4 * M) b n ρ a).2
  have hL : ∀ r ∈ rootsN (4 * M),
      IsAlgebraic ℚ (Complex.exp (Complex.log (1 - r * (cB b n)⁻¹))) := by
    intro r hr
    have hr' := isOfFinOrder_of_mem_rootsN hP hr
    have hne : 1 - r * (cB b n)⁻¹ ≠ 0 := by
      intro h0
      have h3 : ‖r * (cB b n)⁻¹‖ < 1 := by
        rw [norm_mul, norm_root hr', one_mul]
        exact norm_inv_cB_lt hb hn
      rw [← sub_eq_zero.1 h0, norm_one] at h3
      exact lt_irrefl _ h3
    rw [Complex.exp_log hne]
    exact isAlgebraic_one.sub ((isAlgebraic_root hr').mul (isIntegral_cB b hn).isAlgebraic.inv)
  -- Baker's theorem: the value does not change under `σ`
  have h2 := baker_galoisF_log hB (fun x hx => isAlgebraic_of_mem_FB hP hn hx) hI hL hmem hΛ
    σ hσI h1
  have e3 : ∑ r ∈ rootsN (4 * M),
      -coeffAt (4 * M) (twistBN b n η ρ) r * Complex.log (1 - r * (cB b n)⁻¹) =
      q * Real.pi + q' * Λ := by
    rw [← h2, sum_rootsN hP, sum_rootsN hP]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e4 : extF σ (-coeffAt (4 * M) (twistBN b n 1 ρ) (zetaN (4 * M) ^ a)) =
        -coeffAt (4 * M) (twistBN b n η ρ) (zetaN (4 * M) ^ a) := by
      rw [← coe_coeffFB, ← sigma_coeffFB hηn hσc' hσz' ρ a]
      have h5 := extF_coe σ (-coeffFB (4 * M) b n ρ a)
      rw [map_neg] at h5
      exact h5
    rw [e4]
  have h3 := twisted_series_logs hb hn hP hnP hηP hρ
  rwa [e3] at h3

/-! ## 3. The theorem -/

/-- `exp(log y) = y` is algebraic, for a positive rational `y`. -/
private theorem isAlgebraic_exp_log_rat {y : ℚ} (hy : 0 < y) :
    IsAlgebraic ℚ (Complex.exp ((Real.log y : ℝ) : ℂ)) := by
  have hy' : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have e : Complex.exp ((Real.log y : ℝ) : ℂ) = algebraMap ℚ ℂ y := by
    rw [← Complex.ofReal_exp, Real.exp_log hy', Complex.ofReal_ratCast, eq_ratCast]
  rw [e]
  exact isAlgebraic_algebraMap y

/-- **The sub-series lemma for `q π + q' log y`** (from Baker's theorem and `KummerHom b n`).
If a series `∑ ρ(k) b^(-⌊k/n⌋) / k` with `ρ` rational and periodic is `q π + q' log y` with
`q`, `q'` rational and `y` a positive rational, then its sub-series over the `k` divisible by
`halfIfEven n` is `q π + q' log y` too. -/
theorem subseries_log_of_kummerHom (hB : BakerTheorem) {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n)
    (hK : KummerHom b n) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k)
    {q q' : ℚ} {y : ℚ} (hy : 0 < y)
    (h : HasSum (seriesTermBN b n ρ) (q * Real.pi + q' * Real.log y)) :
    HasSum (seriesTermBN b n (fun k => if halfIfEven n ∣ k then ρ k else 0))
      (q * Real.pi + q' * Real.log y) := by
  obtain ⟨n₁, hn₁⟩ : ∃ n₁, n₁ = halfIfEven n := ⟨_, rfl⟩
  have hn₁pos : 0 < n₁ := hn₁ ▸ halfIfEven_pos hn
  have hn₁C : (n₁ : ℂ) ≠ 0 := by exact_mod_cast hn₁pos.ne'
  have hP : 0 < N * (4 * n) := by positivity
  -- the value, in `ℂ`
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℂ, Λ = ((Real.log y : ℝ) : ℂ) := ⟨_, rfl⟩
  have hΛ : IsAlgebraic ℚ (Complex.exp Λ) := hΛdef ▸ isAlgebraic_exp_log_rat hy
  have hval : (((q : ℝ) * Real.pi + (q' : ℝ) * Real.log y : ℝ) : ℂ) =
      (q : ℂ) * Real.pi + (q' : ℂ) * Λ := by
    rw [hΛdef, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_mul,
      Complex.ofReal_ratCast, Complex.ofReal_ratCast]
  -- the complex series
  have hC : HasSum (fun k : ℕ => (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k)
      ((q : ℂ) * Real.pi + (q' : ℂ) * Λ) := by
    have h2 := Complex.hasSum_ofReal.2 h
    rw [hval] at h2
    simp only [seriesTermBN] at h2
    push_cast at h2
    exact h2
  -- every twisted series has the value `q π + q' log y`
  have hall : ∀ j ∈ Finset.range n₁,
      HasSum (fun k : ℕ => (zetaN n₁ ^ j) ^ k * (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k)
        ((q : ℂ) * Real.pi + (q' : ℂ) * Λ) := by
    intro j _
    refine twisted_value_log hB hb hn hK hP ⟨N * n, by ring⟩ ⟨N * 4, by ring⟩
      (periodic_mul hρ (4 * n)) hΛ hC ?_
    rw [← hn₁, ← pow_mul, mul_comm, pow_mul, (zetaN_prim hn₁pos).pow_eq_one, one_pow]
  -- the mean over the `n₁` roots of unity
  have hsum := (hasSum_sum hall).mul_left (1 / (n₁ : ℂ))
  have eval : 1 / (n₁ : ℂ) * ∑ _j ∈ Finset.range n₁, ((q : ℂ) * Real.pi + (q' : ℂ) * Λ) =
      (q : ℂ) * Real.pi + (q' : ℂ) * Λ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have efun : (fun k : ℕ => 1 / (n₁ : ℂ) * ∑ j ∈ Finset.range n₁,
      (zetaN n₁ ^ j) ^ k * (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k) =
      fun k : ℕ => ((seriesTermBN b n (fun k => if n₁ ∣ k then ρ k else 0) k : ℝ) : ℂ) := by
    funext k
    have e1 : ∑ j ∈ Finset.range n₁, (zetaN n₁ ^ j) ^ k * (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k =
        (∑ j ∈ Finset.range n₁, (zetaN n₁ ^ j) ^ k) * (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k := by
      rw [Finset.sum_mul, Finset.sum_div, Finset.sum_div]
    rw [e1, sum_roots_pow hn₁pos k]
    simp only [seriesTermBN]
    by_cases hd : n₁ ∣ k
    · simp only [hd, ↓reduceIte]
      push_cast
      rw [mul_div_assoc, mul_div_assoc, ← mul_assoc, one_div, inv_mul_cancel₀ hn₁C, one_mul]
    · simp only [hd, ↓reduceIte]
      simp
  rw [efun, eval, ← hval] at hsum
  rw [← hn₁]
  exact Complex.hasSum_ofReal.1 hsum

end BaseB

end PiFormula
