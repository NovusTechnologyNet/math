/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.BaseB.SubseriesAux

/-!
# The sub-series lemma for a general base and a general step

**Theorem** (`subseries_of_kummerHom`, from Baker's theorem and `KummerHom b n`). Let `ρ` be a
rational periodic pattern, `n ≥ 1` and `n₁ = halfIfEven n`. If

  `∑_{k ≥ 1} ρ(k) b^(-⌊k/n⌋) / k = q π`,   `q` rational,

then the sub-series over the `k` divisible by `n₁` already has the value `q π`.

The proof (Part IV of `notes/pi_formula_theorem.md`, Lemma (sub-series), for a general base).
Put `c = b^(1/n)` and let `P` be a common period of `ρ` with `4 ∣ P` and `n ∣ P`.

* `b^(-⌊k/n⌋) = c^(k mod n) c^(-k)`, so for every `η` with `η^P = 1` the series with the
  pattern `η^k ρ(k)` is `-∑_{r^P = 1} D_r(η) Log(1 - r/c)`, where `D_r(η)` is the Fourier
  coefficient of the twisted pattern `η^k ρ(k) c^(k mod n)` (`twisted_series_logs`).
* The `D_r(1)` lie in `F = ℚ(ζ_P, c)`, which contains `i` (`coe_coeffFB`).
* For `η^(n₁) = 1` let `σ` be the homomorphism of `KummerHom`: `σ(c) = η c`, `σ(ζ_P) = ζ_P`.
  Then `σ(D_r(1)) = D_r(η)`, because `η^(k mod n) = η^k` (`sigma_coeffFB`), and `σ(i) = i`.
* By Baker's theorem the value `q π` does not change when `σ` is applied to the coefficients
  (`baker_galoisF`). So the series with the pattern `η^k ρ(k)` is `q π` too (`twisted_value`).
* The mean of `η^k` over the `n₁` roots `η` of `X^(n₁) = 1` is `1` for `n₁ ∣ k` and `0`
  otherwise (`sum_roots_pow`).
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-! ## 1. `c = b^(1/n)` and `halfIfEven` -/

theorem cB_pow (b : ℕ) {n : ℕ} (hn : 0 < n) : cB b n ^ n = b := by
  rw [cB, ← Complex.ofReal_pow, one_div, Real.rpow_inv_natCast_pow (Nat.cast_nonneg b) hn.ne']
  simp

theorem one_lt_norm_cB {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) : 1 < ‖cB b n‖ := by
  have h1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h3 := Real.one_lt_rpow h1 (one_div_pos.2 hn')
  rw [cB, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg b) _)]
  exact h3

theorem cB_ne_zero {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) : cB b n ≠ 0 := by
  intro h
  have h1 := one_lt_norm_cB hb hn
  rw [h, norm_zero] at h1
  linarith

theorem norm_inv_cB_lt {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) : ‖(cB b n)⁻¹‖ < 1 := by
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀ (one_lt_norm_cB hb hn)

theorem isIntegral_cB (b : ℕ) {n : ℕ} (hn : 0 < n) : IsIntegral ℚ (cB b n) := by
  refine ⟨X ^ n - C (b : ℚ), monic_X_pow_sub_C _ hn.ne', ?_⟩
  simp [cB_pow b hn]

theorem halfIfEven_dvd (n : ℕ) : halfIfEven n ∣ n := by
  unfold halfIfEven
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    exact ⟨2, by omega⟩
  · exact dvd_rfl

theorem halfIfEven_pos {n : ℕ} (hn : 0 < n) : 0 < halfIfEven n := by
  unfold halfIfEven
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    omega
  · exact hn

/-! ## 2. The twisted pattern and the series as a combination of logarithms -/

/-- The twisted pattern `η^k ρ(k) c^(k mod n)`, so that
`η^k ρ(k) b^(-⌊k/n⌋) = twistBN b n η ρ k * c^(-k)`. -/
noncomputable def twistBN (b n : ℕ) (η : ℂ) (ρ : ℕ → ℚ) (k : ℕ) : ℂ :=
  η ^ k * ((ρ k : ℂ) * cB b n ^ (k % n))

theorem cB_inv_pow_mul {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) (k : ℕ) :
    cB b n ^ (k % n) * (cB b n)⁻¹ ^ k = 1 / (b : ℂ) ^ (k / n) := by
  have hc := cB_ne_zero hb hn
  have h1 : (cB b n)⁻¹ ^ k = ((cB b n)⁻¹ ^ n) ^ (k / n) * (cB b n)⁻¹ ^ (k % n) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h2 : (cB b n)⁻¹ ^ n = 1 / (b : ℂ) := by rw [inv_pow, cB_pow b hn, one_div]
  have h3 : cB b n ^ (k % n) * (cB b n)⁻¹ ^ (k % n) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hc, one_pow]
  rw [h1, h2, mul_left_comm, h3, mul_one, div_pow, one_pow]

theorem twistBN_mul {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) (η : ℂ) (ρ : ℕ → ℚ) (k : ℕ) :
    twistBN b n η ρ k * (cB b n)⁻¹ ^ k / k = η ^ k * (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k := by
  have h := cB_inv_pow_mul hb hn k
  rw [twistBN, mul_assoc, mul_assoc, h]
  ring

theorem twistBN_periodic {b n P : ℕ} (hnP : n ∣ P) {η : ℂ} (hη : η ^ P = 1) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + P) = ρ k) (k : ℕ) : twistBN b n η ρ (k + P) = twistBN b n η ρ k := by
  have h1 : (k + P) % n = k % n := by
    obtain ⟨m, rfl⟩ := hnP
    exact Nat.add_mul_mod_self_left k n m
  rw [twistBN, twistBN, hρ, h1, pow_add, hη, mul_one]

/-- **The series as a combination of logarithms.** For a rational pattern `ρ` of period `P`
(`n ∣ P`) and `η^P = 1`,
`∑_k η^k ρ(k) b^(-⌊k/n⌋) / k = -∑_{r^P = 1} D_r Log(1 - r/c)`, `c = b^(1/n)`. -/
theorem twisted_series_logs {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) {P : ℕ} (hP : 0 < P)
    (hnP : n ∣ P) {η : ℂ} (hη : η ^ P = 1) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + P) = ρ k) :
    HasSum (fun k : ℕ => η ^ k * (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k)
      (∑ r ∈ rootsN P,
        -coeffAt P (twistBN b n η ρ) r * Complex.log (1 - r * (cB b n)⁻¹)) := by
  have h := hasSum_periodic_logs hP (twistBN_periodic (b := b) hnP hη hρ)
    (norm_inv_cB_lt hb hn)
  have e : (fun k : ℕ => twistBN b n η ρ k * (cB b n)⁻¹ ^ k / k) =
      fun k : ℕ => η ^ k * (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k := by
    funext k
    exact twistBN_mul hb hn η ρ k
  rwa [e] at h

/-! ## 3. The field `F = ℚ(ζ_P, c)` -/

/-- `F = ℚ(ζ_P, c)`, the field of `KummerHom` for `M = P`. -/
noncomputable abbrev FB (P b n : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({zetaN P, cB b n} : Set ℂ)

theorem zetaN_mem_FB (P b n : ℕ) : zetaN P ∈ FB P b n :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)

theorem cB_mem_FB (P b n : ℕ) : cB b n ∈ FB P b n :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)

theorem isAlgebraic_of_mem_FB {P b n : ℕ} (hP : 0 < P) (hn : 0 < n) {x : ℂ}
    (hx : x ∈ FB P b n) : IsAlgebraic ℚ x := by
  have hS : ∀ y ∈ ({zetaN P, cB b n} : Set ℂ), IsIntegral ℚ y := by
    intro y hy
    rcases hy with rfl | rfl
    · exact ((zetaN_prim hP).isIntegral hP).tower_top
    · exact isIntegral_cB b hn
  have : Algebra.IsAlgebraic ℚ (FB P b n) := IntermediateField.isAlgebraic_adjoin hS
  have h1 : IsAlgebraic ℚ (algebraMap (FB P b n) ℂ ⟨x, hx⟩) :=
    (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : FB P b n)).algebraMap
  exact h1

/-- `ζ_(4M)^M = i`. -/
theorem zetaN_four_mul_pow {M : ℕ} (hM : 0 < M) : zetaN (4 * M) ^ M = I := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have e : (M : ℂ) * (2 * Real.pi * I / ((4 * M : ℕ) : ℂ)) = Real.pi / 2 * I := by
    push_cast
    field_simp
    ring
  rw [zetaN, ← Complex.exp_nat_mul, e, Complex.exp_pi_div_two_mul_I]

/-- `ζ_P` as an element of `F`. -/
noncomputable def gz (P b n : ℕ) : FB P b n := ⟨zetaN P, zetaN_mem_FB P b n⟩

/-- `c` as an element of `F`. -/
noncomputable def gc (P b n : ℕ) : FB P b n := ⟨cB b n, cB_mem_FB P b n⟩

/-- The Fourier coefficient at `ζ^a` of the twisted pattern `ρ(k) c^(k mod n)`, as an element
of `F`. -/
noncomputable def coeffFB (P b n : ℕ) (ρ : ℕ → ℚ) (a : ℕ) : FB P b n :=
  1 / ((P : ℕ) : FB P b n) * ∑ m ∈ Finset.range P,
    (((ρ m : ℚ) : FB P b n) * gc P b n ^ (m % n)) * ((gz P b n ^ a)⁻¹) ^ m

theorem coe_coeffFB (P b n : ℕ) (ρ : ℕ → ℚ) (a : ℕ) :
    ((coeffFB P b n ρ a : FB P b n) : ℂ) = coeffAt P (twistBN b n 1 ρ) (zetaN P ^ a) := by
  have hz : algebraMap (FB P b n) ℂ (gz P b n) = zetaN P := rfl
  have hc : algebraMap (FB P b n) ℂ (gc P b n) = cB b n := rfl
  change algebraMap (FB P b n) ℂ (coeffFB P b n ρ a) = _
  simp only [coeffFB, coeffAt, twistBN, map_mul, map_div₀, map_one, map_natCast, map_sum,
    map_ratCast, map_pow, map_inv₀, hz, hc, one_pow, one_mul]

/-- A homomorphism with `σ(c) = η c`, `η^n = 1`, and `σ(ζ_P) = ζ_P` sends the coefficient of
the pattern `ρ(k)` to the coefficient of the pattern `η^k ρ(k)`. -/
theorem sigma_coeffFB {P b n : ℕ} {η : ℂ} (hη : η ^ n = 1) {σ : FB P b n →ₐ[ℚ] ℂ}
    (hσc : σ (gc P b n) = η * cB b n) (hσz : σ (gz P b n) = zetaN P) (ρ : ℕ → ℚ) (a : ℕ) :
    σ (coeffFB P b n ρ a) = coeffAt P (twistBN b n η ρ) (zetaN P ^ a) := by
  have hmod : ∀ m : ℕ, η ^ (m % n) = η ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, hη, one_pow, one_mul]
  simp only [coeffFB, coeffAt, twistBN, map_mul, map_div₀, map_one, map_natCast, map_sum,
    map_ratCast, map_pow, map_inv₀, hσc, hσz, mul_pow, hmod]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-! ## 4. The twisted series have the same value -/

/-- **The twisted series** (from Baker's theorem and `KummerHom`). If the series of `ρ` is
`q π` with `q` rational, then for every `η` with `η^(n₁) = 1` the series of the pattern
`η^k ρ(k)` is `q π` too. -/
theorem twisted_value (hB : BakerTheorem) {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n)
    (hK : KummerHom b n) {P : ℕ} (hP : 0 < P) (h4 : 4 ∣ P) (hnP : n ∣ P) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + P) = ρ k) {q : ℚ}
    (h : HasSum (fun k : ℕ => (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k) (q * Real.pi))
    {η : ℂ} (hη : η ^ halfIfEven n = 1) :
    HasSum (fun k : ℕ => η ^ k * (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k) (q * Real.pi) := by
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
  have h2 := baker_galoisF hB (fun x hx => isAlgebraic_of_mem_FB hP hn hx) hI hL hmem σ hσI h1
  have e3 : ∑ r ∈ rootsN (4 * M),
      -coeffAt (4 * M) (twistBN b n η ρ) r * Complex.log (1 - r * (cB b n)⁻¹) =
      q * Real.pi := by
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

/-! ## 5. The mean over the roots of unity, and the theorem -/

/-- `∑_{η^m = 1} η^k` is `m` if `m ∣ k`, and `0` otherwise. -/
theorem sum_roots_pow {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∑ j ∈ Finset.range m, (zetaN m ^ j) ^ k = if m ∣ k then (m : ℂ) else 0 := by
  have hζ := zetaN_prim hm
  have e : ∑ j ∈ Finset.range m, (zetaN m ^ j) ^ k =
      ∑ j ∈ Finset.range m, (zetaN m ^ k) ^ j :=
    Finset.sum_congr rfl fun j _ => by rw [← pow_mul, ← pow_mul, mul_comm]
  have hu : (zetaN m ^ k) ^ m = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [e, geom_sum_root hu]
  simp only [hζ.pow_eq_one_iff_dvd]

/-- **The sub-series lemma** (from Baker's theorem and `KummerHom b n`). If a series
`∑ ρ(k) b^(-⌊k/n⌋) / k` with `ρ` rational and periodic is `q π` with `q` rational, then its
sub-series over the `k` divisible by `halfIfEven n` is `q π` too. -/
theorem subseries_of_kummerHom (hB : BakerTheorem) {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n)
    (hK : KummerHom b n) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {q : ℚ}
    (h : HasSum (seriesTermBN b n ρ) (q * Real.pi)) :
    HasSum (seriesTermBN b n (fun k => if halfIfEven n ∣ k then ρ k else 0)) (q * Real.pi) := by
  obtain ⟨n₁, hn₁⟩ : ∃ n₁, n₁ = halfIfEven n := ⟨_, rfl⟩
  have hn₁pos : 0 < n₁ := hn₁ ▸ halfIfEven_pos hn
  have hn₁C : (n₁ : ℂ) ≠ 0 := by exact_mod_cast hn₁pos.ne'
  have hP : 0 < N * (4 * n) := by positivity
  -- the complex series
  have hC : HasSum (fun k : ℕ => (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k) ((q : ℂ) * Real.pi) := by
    have h2 := Complex.hasSum_ofReal.2 h
    simp only [seriesTermBN] at h2
    push_cast at h2
    exact h2
  -- every twisted series has the value `q π`
  have hall : ∀ j ∈ Finset.range n₁,
      HasSum (fun k : ℕ => (zetaN n₁ ^ j) ^ k * (ρ k : ℂ) / (b : ℂ) ^ (k / n) / k)
        ((q : ℂ) * Real.pi) := by
    intro j _
    refine twisted_value hB hb hn hK hP ⟨N * n, by ring⟩ ⟨N * 4, by ring⟩
      (periodic_mul hρ (4 * n)) hC ?_
    rw [← hn₁, ← pow_mul, mul_comm, pow_mul, (zetaN_prim hn₁pos).pow_eq_one, one_pow]
  -- the mean over the `n₁` roots of unity
  have hsum := (hasSum_sum hall).mul_left (1 / (n₁ : ℂ))
  have eval : 1 / (n₁ : ℂ) * ∑ _j ∈ Finset.range n₁, (q : ℂ) * Real.pi =
      (((q : ℝ) * Real.pi : ℝ) : ℂ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
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
  rw [efun, eval] at hsum
  rw [← hn₁]
  exact Complex.hasSum_ofReal.1 hsum

end BaseB

end PiFormula
