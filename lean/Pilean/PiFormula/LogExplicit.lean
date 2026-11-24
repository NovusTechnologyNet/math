/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula.LogConverse

/-!
# Theorem K in elementary terms

`LogConverse.lean` proves the criterion in the form: `log y` is a value of the class F if and
only if it is a rational combination of `log 2` and the numbers `log N((1+i)^n - c)`.
This file removes the Gaussian integers from the statement.

* `baseNumbers`: the integers `2`, `2^m - 1` (`m ≥ 1`), and
  `2^(2k+1) - 2^(k+1) + 1`, `2^(2k+1) + 2^(k+1) + 1` (the two factors of `4^(2k+1) + 1`).
* `logSpan_eq_baseSpan`: the rational combinations of `log 2` and the `log N((1+i)^n - c)`
  are the rational combinations of the logarithms of the base numbers. (For even `n` the norm
  is `(2^m - 1)^2`, `(2^m + 1)^2` or `4^m + 1`; for odd `n` it is one of the two factors.)
* `isFValue_log_rat_iff_pow` (from Baker's theorem): **for a positive rational number `y`,
  `log y` is the value of a series of the class F if and only if some power `y^k`, `k ≥ 1`,
  is a product of integer powers of base numbers.**
* `isFValue_log_of_pow`: the "if" half, which needs no Baker.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

/-! ## 1. The base numbers -/

/-- The base numbers: `2`, the numbers `2^m - 1` (`m ≥ 1`), and the two factors
`2^n - 2^((n+1)/2) + 1`, `2^n + 2^((n+1)/2) + 1` of `4^n + 1` for odd `n = 2k + 1`. -/
def baseNumbers : Set ℤ :=
  {g | g = 2 ∨ (∃ m : ℕ, 0 < m ∧ g = 2 ^ m - 1) ∨
    (∃ k : ℕ, g = 2 ^ (2 * k + 1) - 2 ^ (k + 1) + 1) ∨
    ∃ k : ℕ, g = 2 ^ (2 * k + 1) + 2 ^ (k + 1) + 1}

theorem baseNumbers_pos {g : ℤ} (hg : g ∈ baseNumbers) : 0 < g := by
  rcases hg with rfl | ⟨m, hm, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · norm_num
  · have h1 : (1 : ℤ) < 2 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
    linarith
  · have h1 : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have e : (2 : ℤ) ^ (2 * k + 1) - 2 ^ (k + 1) + 1 = 2 * 2 ^ k * (2 ^ k - 1) + 1 := by ring
    rw [e]
    have h2 : (0 : ℤ) ≤ 2 * 2 ^ k * (2 ^ k - 1) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  · positivity

/-- The rational combinations of the logarithms of the base numbers. -/
noncomputable def baseSpan : Submodule ℚ ℝ :=
  Submodule.span ℚ ((fun g : ℤ => Real.log (g : ℝ)) '' baseNumbers)

theorem log_mem_baseSpan {g : ℤ} (hg : g ∈ baseNumbers) : Real.log (g : ℝ) ∈ baseSpan :=
  Submodule.subset_span ⟨g, hg, rfl⟩

theorem rat_mul_mem_baseSpan {x : ℝ} (hx : x ∈ baseSpan) (q : ℚ) :
    (q : ℝ) * x ∈ baseSpan := by
  have h := baseSpan.smul_mem q hx
  rwa [Rat.smul_def] at h

theorem log_mersenne_mem_baseSpan {m : ℕ} (hm : 0 < m) :
    Real.log ((2 : ℝ) ^ m - 1) ∈ baseSpan := by
  have h := log_mem_baseSpan (g := 2 ^ m - 1) (Or.inr (Or.inl ⟨m, hm, rfl⟩))
  have e : (((2 : ℤ) ^ m - 1 : ℤ) : ℝ) = (2 : ℝ) ^ m - 1 := by push_cast; ring
  rwa [e] at h

/-- `log (2^m + 1) = log (2^(2m) - 1) - log (2^m - 1)`. -/
theorem log_two_pow_add_one_mem_baseSpan {m : ℕ} (hm : 0 < m) :
    Real.log ((2 : ℝ) ^ m + 1) ∈ baseSpan := by
  have h1 : (1 : ℝ) < 2 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
  have e : Real.log ((2 : ℝ) ^ m + 1) =
      Real.log ((2 : ℝ) ^ (2 * m) - 1) - Real.log ((2 : ℝ) ^ m - 1) := by
    have h2 : (2 : ℝ) ^ (2 * m) - 1 = ((2 : ℝ) ^ m + 1) * ((2 : ℝ) ^ m - 1) := by ring
    rw [h2, Real.log_mul (by linarith) (by linarith)]
    ring
  rw [e]
  exact sub_mem (log_mersenne_mem_baseSpan (by omega)) (log_mersenne_mem_baseSpan hm)

/-! ## 2. The norms `N((1+i)^n - c)` -/

theorem gI_re : gI.re = 0 := rfl

theorem gI_im : gI.im = 1 := rfl

theorem gaussian_norm_pow (z : GaussianInt) (m : ℕ) : (z ^ m).norm = z.norm ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Zsqrtd.norm_one]
  | succ m ih => rw [pow_succ, pow_succ, Zsqrtd.norm_mul, ih]

/-- The fourth roots of unity of `ℤ[i]` are `1, -1, i, -i`. -/
theorem gaussian_unit_cases {c : GaussianInt} (hc : c ^ 4 = 1) :
    c = 1 ∨ c = -1 ∨ c = gI ∨ c = -gI := by
  have h1 : c.norm ^ 4 = 1 := by rw [← gaussian_norm_pow, hc, Zsqrtd.norm_one]
  have h2 : c.norm = 1 :=
    (pow_eq_one_iff_of_nonneg (GaussianInt.norm_nonneg c) (by norm_num)).1 h1
  obtain ⟨x, y⟩ := c
  rw [Zsqrtd.norm_def] at h2
  simp only at h2
  have hx1 : -1 ≤ x := by nlinarith [mul_self_nonneg y, mul_self_nonneg x]
  have hx2 : x ≤ 1 := by nlinarith [mul_self_nonneg y, mul_self_nonneg x]
  have hy1 : -1 ≤ y := by nlinarith [mul_self_nonneg y, mul_self_nonneg x]
  have hy2 : y ≤ 1 := by nlinarith [mul_self_nonneg y, mul_self_nonneg x]
  interval_cases x <;> interval_cases y <;> first | (norm_num at h2; done) | decide

/-- `(1+i)^(2m)` is `±2^m` or `±2^m i`. -/
theorem tG_pow_even (m : ℕ) :
    ((tG ^ (2 * m)).re ^ 2 = (2 ^ m) ^ 2 ∧ (tG ^ (2 * m)).im = 0) ∨
      ((tG ^ (2 * m)).re = 0 ∧ (tG ^ (2 * m)).im ^ 2 = (2 ^ m) ^ 2) := by
  induction m with
  | zero => left; simp
  | succ m ih =>
    have hpow : tG ^ (2 * (m + 1)) = tG ^ (2 * m) * ⟨0, 2⟩ := by
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, tG_sq]
    rw [hpow]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      constructor
      · linear_combination (-2 : ℤ) * h2
      · linear_combination 4 * h1 + (4 * (tG ^ (2 * m)).re * 0) * h2
    · left
      constructor
      · linear_combination 4 * h2
      · linear_combination (2 : ℤ) * h1

/-- For even `n = 2m`, the norm of `(1+i)^n - c` is `(2^m - 1)^2`, `(2^m + 1)^2` or
`4^m + 1`. -/
theorem norm_even_cases (m : ℕ) {c : GaussianInt} (hc : c ^ 4 = 1) :
    (tG ^ (2 * m) - c).norm = (2 ^ m - 1) ^ 2 ∨ (tG ^ (2 * m) - c).norm = (2 ^ m + 1) ^ 2 ∨
      (tG ^ (2 * m) - c).norm = (2 ^ m) ^ 2 + 1 := by
  have key : ∀ s : ℤ, s ^ 2 = (2 ^ m) ^ 2 → s = 2 ^ m ∨ s = -2 ^ m := fun s hs =>
    eq_or_eq_neg_of_sq_eq_sq s (2 ^ m) hs
  rw [Zsqrtd.norm_def]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
  rcases tG_pow_even m with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases key _ h1 with h | h <;> rw [h, h2] <;>
      rcases gaussian_unit_cases hc with rfl | rfl | rfl | rfl <;>
      simp only [Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_neg, Zsqrtd.im_neg, gI_re, gI_im] <;>
      first | (left; ring1) | (right; left; ring1) | (right; right; ring1)
  · rcases key _ h2 with h | h <;> rw [h, h1] <;>
      rcases gaussian_unit_cases hc with rfl | rfl | rfl | rfl <;>
      simp only [Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_neg, Zsqrtd.im_neg, gI_re, gI_im] <;>
      first | (left; ring1) | (right; left; ring1) | (right; right; ring1)

/-- For odd `n = 2k + 1`, the norm of `(1+i)^n - c` is one of the two factors of
`4^n + 1`. -/
theorem norm_odd_cases (k : ℕ) {c : GaussianInt} (hc : c ^ 4 = 1) :
    (tG ^ (2 * k + 1) - c).norm = 2 ^ (2 * k + 1) - 2 ^ (k + 1) + 1 ∨
      (tG ^ (2 * k + 1) - c).norm = 2 ^ (2 * k + 1) + 2 ^ (k + 1) + 1 := by
  obtain ⟨hre, him⟩ := tG_pow_odd k
  have h4 : (4 : ℤ) ^ k = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have key : ∀ s : ℤ, s ^ 2 = 4 ^ k →
      (2 * 4 ^ k + 1 - 2 * s = 2 ^ (2 * k + 1) - 2 ^ (k + 1) + 1) ∨
        (2 * 4 ^ k + 1 - 2 * s = 2 ^ (2 * k + 1) + 2 ^ (k + 1) + 1) := by
    intro s hs
    rcases eq_or_eq_neg_of_sq_eq_sq s (2 ^ k) (by rw [hs, h4]) with h | h
    · left
      rw [h, h4]
      ring
    · right
      rw [h, h4]
      ring
  rcases gaussian_unit_cases hc with rfl | rfl | rfl | rfl
  · have e : (tG ^ (2 * k + 1) - 1).norm = 2 * 4 ^ k + 1 - 2 * (tG ^ (2 * k + 1)).re := by
      rw [Zsqrtd.norm_def]
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
      linear_combination hre + him
    rw [e]
    exact key _ hre
  · have e : (tG ^ (2 * k + 1) - -1).norm =
        2 * 4 ^ k + 1 - 2 * (-(tG ^ (2 * k + 1)).re) := by
      rw [Zsqrtd.norm_def]
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_neg,
        Zsqrtd.im_neg]
      linear_combination hre + him
    rw [e]
    exact key _ (by rw [neg_sq]; exact hre)
  · have e : (tG ^ (2 * k + 1) - gI).norm = 2 * 4 ^ k + 1 - 2 * (tG ^ (2 * k + 1)).im := by
      rw [Zsqrtd.norm_def]
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, gI_re, gI_im]
      linear_combination hre + him
    rw [e]
    exact key _ him
  · have e : (tG ^ (2 * k + 1) - -gI).norm =
        2 * 4 ^ k + 1 - 2 * (-(tG ^ (2 * k + 1)).im) := by
      rw [Zsqrtd.norm_def]
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_neg, Zsqrtd.im_neg, gI_re, gI_im]
      linear_combination hre + him
    rw [e]
    exact key _ (by rw [neg_sq]; exact him)

/-! ## 3. The two spans are equal -/

/-- Every `log N((1+i)^n - c)` is a rational combination of logarithms of base numbers. -/
theorem generator_mem_baseSpan {n : ℕ} (hn : 0 < n) {c : GaussianInt} (hc : c ^ 4 = 1) :
    Real.log (((tG ^ n - c).norm : ℤ) : ℝ) ∈ baseSpan := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hm : 0 < m := by omega
    rcases norm_even_cases m hc with h | h | h <;> rw [h] <;> push_cast
    · rw [Real.log_pow]
      exact_mod_cast rat_mul_mem_baseSpan (log_mersenne_mem_baseSpan hm) 2
    · rw [Real.log_pow]
      exact_mod_cast rat_mul_mem_baseSpan (log_two_pow_add_one_mem_baseSpan hm) 2
    · have e : ((2 : ℝ) ^ m) ^ 2 + 1 = (2 : ℝ) ^ (2 * m) + 1 := by ring
      rw [e]
      exact log_two_pow_add_one_mem_baseSpan (by omega)
  · rcases norm_odd_cases m hc with h | h <;> rw [h]
    · exact log_mem_baseSpan (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩)))
    · exact log_mem_baseSpan (Or.inr (Or.inr (Or.inr ⟨m, rfl⟩)))

theorem logSpan_le_baseSpan : logSpan ≤ baseSpan := by
  refine Submodule.span_le.2 ?_
  rintro x (rfl | ⟨n, c, hn, hc, rfl⟩)
  · have h := log_mem_baseSpan (g := 2) (Or.inl rfl)
    simpa using h
  · exact generator_mem_baseSpan hn hc

theorem baseSpan_le_logSpan : baseSpan ≤ logSpan := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨g, hg, rfl⟩
  change Real.log (g : ℝ) ∈ logSpan
  rcases hg with rfl | ⟨m, hm, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simpa using log_two_mem_logSpan
  · have hgen : Real.log (((tG ^ (2 * m) - gI ^ m).norm : ℤ) : ℝ) ∈ logSpan :=
      Submodule.subset_span (Or.inr ⟨2 * m, gI ^ m, by omega, gI_pow_pow_four m, rfl⟩)
    rw [norm_tG_pow_two_mul] at hgen
    have h := rat_mul_mem_logSpan hgen (1 / 2)
    have e : ((1 / 2 : ℚ) : ℝ) * Real.log ((((2 : ℤ) ^ m - 1) ^ 2 : ℤ) : ℝ) =
        Real.log (((2 : ℤ) ^ m - 1 : ℤ) : ℝ) := by
      push_cast
      rw [Real.log_pow]
      push_cast
      ring
    rw [e] at h
    exact h
  · have hL : L (2 * k + 1) = 2 ^ (2 * k + 1) - 2 ^ (k + 1) + 1 := by
      unfold L
      rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega]
    rw [← hL]
    rcases Uplus_Uminus_odd k with ⟨h, -⟩ | ⟨-, h⟩
    · rw [← h]
      exact Submodule.subset_span (Or.inr ⟨2 * k + 1, 1, by omega, one_pow 4, rfl⟩)
    · rw [← h, Uminus_odd]
      exact Submodule.subset_span (Or.inr ⟨2 * k + 1, -1, by omega, neg_one_pow_four', rfl⟩)
  · have hM : M (2 * k + 1) = 2 ^ (2 * k + 1) + 2 ^ (k + 1) + 1 := by
      unfold M
      rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega]
    rw [← hM]
    rcases Uplus_Uminus_odd k with ⟨-, h⟩ | ⟨h, -⟩
    · rw [← h, Uminus_odd]
      exact Submodule.subset_span (Or.inr ⟨2 * k + 1, -1, by omega, neg_one_pow_four', rfl⟩)
    · rw [← h]
      exact Submodule.subset_span (Or.inr ⟨2 * k + 1, 1, by omega, one_pow 4, rfl⟩)

/-- The rational combinations of `log 2` and the `log N((1+i)^n - c)` are the rational
combinations of the logarithms of the base numbers. -/
theorem logSpan_eq_baseSpan : logSpan = baseSpan :=
  le_antisymm logSpan_le_baseSpan baseSpan_le_logSpan

/-! ## 4. Rational combinations of logarithms and powers -/

/-- For positive integers `Γ` and a positive rational `y`: `log y` is a rational combination
of the `log g`, `g ∈ Γ`, if and only if some power `y^k`, `k ≥ 1`, is a product of integer
powers of elements of `Γ`. -/
theorem log_mem_span_iff_pow {Γ : Set ℤ} (hΓ : ∀ g ∈ Γ, 0 < g) {y : ℚ} (hy : 0 < y) :
    Real.log (y : ℝ) ∈ Submodule.span ℚ ((fun g : ℤ => Real.log (g : ℝ)) '' Γ) ↔
      ∃ k : ℕ, 0 < k ∧ ∃ (n : ℕ) (g : Fin n → ℤ) (e : Fin n → ℤ),
        (∀ i, g i ∈ Γ) ∧ y ^ k = ∏ i, (g i : ℚ) ^ e i := by
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  constructor
  · intro h
    obtain ⟨n, f, g', hsum⟩ := Submodule.mem_span_set'.1 h
    have hex : ∀ i, ∃ γ : ℤ, γ ∈ Γ ∧ Real.log (γ : ℝ) = (g' i : ℝ) := fun i => (g' i).2
    choose γ hγΓ hγ using hex
    set D : ℕ := ∏ i, (f i).den with hD
    have hDpos : 0 < D := Finset.prod_pos fun i _ => (f i).den_pos
    let e : Fin n → ℤ := fun i => (f i).num * ((D / (f i).den : ℕ) : ℤ)
    have he : ∀ i, ((e i : ℤ) : ℝ) = (D : ℝ) * ((f i : ℚ) : ℝ) := by
      intro i
      obtain ⟨q, hq⟩ : (f i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have hdiv : D / (f i).den = q := by
        rw [hq]
        exact Nat.mul_div_cancel_left q (f i).den_pos
      have hden : ((f i).den : ℝ) ≠ 0 := by exact_mod_cast (f i).den_pos.ne'
      have hfi : ((f i : ℚ) : ℝ) = ((f i).num : ℝ) / ((f i).den : ℝ) := Rat.cast_def _
      simp only [e, hdiv]
      rw [hfi, hq]
      push_cast
      field_simp
    have hγpos : ∀ i, (0 : ℝ) < ((γ i : ℤ) : ℝ) := fun i => by
      exact_mod_cast hΓ _ (hγΓ i)
    refine ⟨D, hDpos, n, γ, e, hγΓ, ?_⟩
    have h1 : Real.log ((y : ℝ) ^ D) = Real.log (∏ i, ((γ i : ℤ) : ℝ) ^ e i) := by
      rw [Real.log_pow, Real.log_prod (fun i _ => (zpow_pos (hγpos i) _).ne'), ← hsum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.log_zpow, he, hγ, Rat.smul_def]
      ring
    have h2 : (y : ℝ) ^ D = ∏ i, ((γ i : ℤ) : ℝ) ^ e i :=
      Real.log_injOn_pos (Set.mem_Ioi.2 (pow_pos hyR D))
        (Set.mem_Ioi.2 (Finset.prod_pos fun i _ => zpow_pos (hγpos i) _)) h1
    have h3 : ((y ^ D : ℚ) : ℝ) = ((∏ i, (γ i : ℚ) ^ e i : ℚ) : ℝ) := by
      simp only [Rat.cast_pow, Rat.cast_prod, Rat.cast_zpow, Rat.cast_intCast]
      exact h2
    exact Rat.cast_injective h3
  · rintro ⟨k, hk, n, g, e, hg, hprod⟩
    have hgpos : ∀ i, (0 : ℝ) < ((g i : ℤ) : ℝ) := fun i => by exact_mod_cast hΓ _ (hg i)
    have h1 : (y : ℝ) ^ k = ∏ i, ((g i : ℤ) : ℝ) ^ e i := by
      have h0 := congrArg (fun q : ℚ => (q : ℝ)) hprod
      simp only [Rat.cast_pow, Rat.cast_prod, Rat.cast_zpow, Rat.cast_intCast] at h0
      exact h0
    have h2 := congrArg Real.log h1
    rw [Real.log_pow, Real.log_prod (fun i _ => (zpow_pos (hgpos i) _).ne')] at h2
    simp only [Real.log_zpow] at h2
    have hmem : (k : ℝ) * Real.log (y : ℝ) ∈
        Submodule.span ℚ ((fun g : ℤ => Real.log (g : ℝ)) '' Γ) := by
      rw [h2]
      refine Submodule.sum_mem _ fun i _ => ?_
      have h3 := Submodule.smul_mem (Submodule.span ℚ ((fun g : ℤ => Real.log (g : ℝ)) '' Γ))
        (e i : ℚ) (Submodule.subset_span ⟨g i, hg i, rfl⟩)
      rw [Rat.smul_def] at h3
      exact_mod_cast h3
    have h4 := Submodule.smul_mem _ ((k : ℚ)⁻¹) hmem
    rw [Rat.smul_def] at h4
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have e2 : (((k : ℚ)⁻¹ : ℚ) : ℝ) * ((k : ℝ) * Real.log (y : ℝ)) = Real.log (y : ℝ) := by
      push_cast
      field_simp
    rw [e2] at h4
    exact h4

/-! ## 5. The criterion in elementary terms -/

/-- **The "if" half, without Baker.** If some power `y^k`, `k ≥ 1`, of a positive rational
`y` is a product of integer powers of base numbers, then `log y` is the value of a series of
the class F. -/
theorem isFValue_log_of_pow {y : ℚ} (hy : 0 < y) {k : ℕ} (hk : 0 < k) {n : ℕ} {g : Fin n → ℤ}
    {e : Fin n → ℤ} (hg : ∀ i, g i ∈ baseNumbers) (h : y ^ k = ∏ i, (g i : ℚ) ^ e i) :
    IsFValue (Real.log (y : ℝ)) := by
  have h1 : Real.log (y : ℝ) ∈ baseSpan :=
    (log_mem_span_iff_pow (fun g hg => baseNumbers_pos hg) hy).2 ⟨k, hk, n, g, e, hg, h⟩
  rw [← logSpan_eq_baseSpan] at h1
  exact isFValue_of_mem_logSpan h1

/-- **Theorem K in elementary terms** (from Baker's theorem). For a positive rational number
`y`, `log y` is the value of a series `∑ ρ(k) 2^(-⌊k/2⌋)/k` with `ρ` rational and periodic if
and only if some power `y^k`, `k ≥ 1`, is a product of integer powers of the numbers `2`,
`2^m - 1`, `2^(2j+1) - 2^(j+1) + 1` and `2^(2j+1) + 2^(j+1) + 1`. -/
theorem isFValue_log_rat_iff_pow (hB : BakerTheorem) {y : ℚ} (hy : 0 < y) :
    IsFValue (Real.log (y : ℝ)) ↔
      ∃ k : ℕ, 0 < k ∧ ∃ (n : ℕ) (g : Fin n → ℤ) (e : Fin n → ℤ),
        (∀ i, g i ∈ baseNumbers) ∧ y ^ k = ∏ i, (g i : ℚ) ^ e i := by
  rw [isFValue_log_rat_iff hB hy, logSpan_eq_baseSpan]
  exact log_mem_span_iff_pow (fun g hg => baseNumbers_pos hg) hy

end PiFormula
