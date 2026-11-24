/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Base3.LogConverse
public import Pilean.PiFormula.LogExplicit

/-!
# Base 3: the criterion for logarithms in elementary terms

* `baseNumbers3`: the integers `3`, `3^m - 1` (`m ≥ 1`), and
  `3^(2k+1) - 3^(k+1) + 1`, `3^(2k+1) + 3^(k+1) + 1`, the two Aurifeuillian factors of
  `3^(3n) + 1 = (3^n + 1) (3^n - 3^((n+1)/2) + 1) (3^n + 3^((n+1)/2) + 1)`, `n = 2k + 1`.
* `logSpan3_eq_baseSpan3`: the rational combinations of `log 3` and the `log |t^n - c|`
  (`t = √-3`, `c^3 = 1`) are the rational combinations of the logarithms of the base numbers.
  Indeed `|t^n - c|^2` is `(3^m ∓ 1)^2` or `9^m ± 3^m + 1` for `n = 2m`, and `3^n + 1` or one
  of the two Aurifeuillian factors for `n` odd (`norm_sq_even`, `norm_sq_odd`).
* `isF3Value_log_rat_iff_pow` (from Baker's theorem): **for a positive rational number `y`,
  `log y` is the value of a series `∑ ρ(k) 3^(-⌊k/2⌋)/k` with `ρ` rational and periodic if
  and only if some power `y^k`, `k ≥ 1`, is a product of integer powers of base numbers.**
* `isF3Value_log_of_pow`: the "if" half, which needs no Baker.
* Examples (no Baker): `log 2, 5, 7, 11, 13, 19, 37` are values of the class F3.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace Base3

/-! ## 1. The base numbers -/

/-- The base numbers in base 3. -/
def baseNumbers3 : Set ℤ :=
  {g | g = 3 ∨ (∃ m : ℕ, 0 < m ∧ g = 3 ^ m - 1) ∨
    (∃ k : ℕ, g = 3 ^ (2 * k + 1) - 3 ^ (k + 1) + 1) ∨
    ∃ k : ℕ, g = 3 ^ (2 * k + 1) + 3 ^ (k + 1) + 1}

theorem baseNumbers3_pos {g : ℤ} (hg : g ∈ baseNumbers3) : 0 < g := by
  rcases hg with rfl | ⟨m, hm, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · norm_num
  · have h1 : (1 : ℤ) < 3 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
    linarith
  · have h1 : (1 : ℤ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    have e : (3 : ℤ) ^ (2 * k + 1) - 3 ^ (k + 1) + 1 = 3 * 3 ^ k * (3 ^ k - 1) + 1 := by ring
    rw [e]
    have h2 : (0 : ℤ) ≤ 3 * 3 ^ k * (3 ^ k - 1) := mul_nonneg (by positivity) (by linarith)
    linarith
  · positivity

/-- The rational combinations of the logarithms of the base numbers. -/
noncomputable def baseSpan3 : Submodule ℚ ℝ :=
  Submodule.span ℚ ((fun g : ℤ => Real.log (g : ℝ)) '' baseNumbers3)

theorem log_mem_baseSpan3 {g : ℤ} (hg : g ∈ baseNumbers3) : Real.log (g : ℝ) ∈ baseSpan3 :=
  Submodule.subset_span ⟨g, hg, rfl⟩

theorem rat_mul_mem_baseSpan3 {x : ℝ} (hx : x ∈ baseSpan3) (q : ℚ) :
    (q : ℝ) * x ∈ baseSpan3 := by
  have h := baseSpan3.smul_mem q hx
  rwa [Rat.smul_def] at h

theorem log_three_mem_baseSpan3 : Real.log 3 ∈ baseSpan3 := by
  have h := log_mem_baseSpan3 (g := 3) (Or.inl rfl)
  simpa using h

theorem log_pow_sub_one_mem {m : ℕ} (hm : 0 < m) : Real.log ((3 : ℝ) ^ m - 1) ∈ baseSpan3 := by
  have h := log_mem_baseSpan3 (g := 3 ^ m - 1) (Or.inr (Or.inl ⟨m, hm, rfl⟩))
  have e : (((3 : ℤ) ^ m - 1 : ℤ) : ℝ) = (3 : ℝ) ^ m - 1 := by push_cast; ring
  rwa [e] at h

/-- `log (3^m + 1) = log (3^(2m) - 1) - log (3^m - 1)`. -/
theorem log_pow_add_one_mem {m : ℕ} (hm : 0 < m) : Real.log ((3 : ℝ) ^ m + 1) ∈ baseSpan3 := by
  have h1 : (1 : ℝ) < 3 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
  have e : Real.log ((3 : ℝ) ^ m + 1) =
      Real.log ((3 : ℝ) ^ (2 * m) - 1) - Real.log ((3 : ℝ) ^ m - 1) := by
    have h2 : (3 : ℝ) ^ (2 * m) - 1 = ((3 : ℝ) ^ m + 1) * ((3 : ℝ) ^ m - 1) := by ring
    rw [h2, Real.log_mul (by linarith) (by linarith)]
    ring
  rw [e]
  exact sub_mem (log_pow_sub_one_mem (by omega)) (log_pow_sub_one_mem hm)

/-- `log (9^m + 3^m + 1) = log (3^(3m) - 1) - log (3^m - 1)`. -/
theorem log_sq_add_mem {m : ℕ} (hm : 0 < m) :
    Real.log (((3 : ℝ) ^ m) ^ 2 + 3 ^ m + 1) ∈ baseSpan3 := by
  have h1 : (1 : ℝ) < 3 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
  have e : Real.log (((3 : ℝ) ^ m) ^ 2 + 3 ^ m + 1) =
      Real.log ((3 : ℝ) ^ (3 * m) - 1) - Real.log ((3 : ℝ) ^ m - 1) := by
    have h2 : (3 : ℝ) ^ (3 * m) - 1 =
        (((3 : ℝ) ^ m) ^ 2 + 3 ^ m + 1) * ((3 : ℝ) ^ m - 1) := by ring
    rw [h2, Real.log_mul (by positivity) (by linarith)]
    ring
  rw [e]
  exact sub_mem (log_pow_sub_one_mem (by omega)) (log_pow_sub_one_mem hm)

/-- `log (9^m - 3^m + 1) = log (3^(3m) + 1) - log (3^m + 1)`. -/
theorem log_sq_sub_mem {m : ℕ} (hm : 0 < m) :
    Real.log (((3 : ℝ) ^ m) ^ 2 - 3 ^ m + 1) ∈ baseSpan3 := by
  have h1 : (1 : ℝ) < 3 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
  have hpos : (0 : ℝ) < ((3 : ℝ) ^ m) ^ 2 - 3 ^ m + 1 := by nlinarith
  have e : Real.log (((3 : ℝ) ^ m) ^ 2 - 3 ^ m + 1) =
      Real.log ((3 : ℝ) ^ (3 * m) + 1) - Real.log ((3 : ℝ) ^ m + 1) := by
    have h2 : (3 : ℝ) ^ (3 * m) + 1 =
        (((3 : ℝ) ^ m) ^ 2 - 3 ^ m + 1) * ((3 : ℝ) ^ m + 1) := by ring
    rw [h2, Real.log_mul hpos.ne' (by linarith)]
    ring
  rw [e]
  exact sub_mem (log_pow_add_one_mem (by omega)) (log_pow_add_one_mem hm)

theorem log_L_mem (k : ℕ) :
    Real.log ((3 : ℝ) ^ (2 * k + 1) - 3 ^ (k + 1) + 1) ∈ baseSpan3 := by
  have h := log_mem_baseSpan3 (g := 3 ^ (2 * k + 1) - 3 ^ (k + 1) + 1)
    (Or.inr (Or.inr (Or.inl ⟨k, rfl⟩)))
  have e : (((3 : ℤ) ^ (2 * k + 1) - 3 ^ (k + 1) + 1 : ℤ) : ℝ) =
      (3 : ℝ) ^ (2 * k + 1) - 3 ^ (k + 1) + 1 := by push_cast; ring
  rwa [e] at h

theorem log_M_mem (k : ℕ) :
    Real.log ((3 : ℝ) ^ (2 * k + 1) + 3 ^ (k + 1) + 1) ∈ baseSpan3 := by
  have h := log_mem_baseSpan3 (g := 3 ^ (2 * k + 1) + 3 ^ (k + 1) + 1)
    (Or.inr (Or.inr (Or.inr ⟨k, rfl⟩)))
  have e : (((3 : ℤ) ^ (2 * k + 1) + 3 ^ (k + 1) + 1 : ℤ) : ℝ) =
      (3 : ℝ) ^ (2 * k + 1) + 3 ^ (k + 1) + 1 := by push_cast; ring
  rwa [e] at h

/-! ## 2. The numbers `|t^n - c|^2` -/

theorem t3_pow_even (m : ℕ) : t3 ^ (2 * m) = (((-3 : ℝ) ^ m : ℝ) : ℂ) := by
  rw [pow_mul, t3_sq]
  push_cast
  rfl

theorem t3_pow_odd (m : ℕ) :
    t3 ^ (2 * m + 1) = (((-3 : ℝ) ^ m * Real.sqrt 3 : ℝ) : ℂ) * I := by
  rw [pow_succ, t3_pow_even, t3]
  push_cast
  ring

theorem norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem neg_three_pow_cases (m : ℕ) : (-3 : ℝ) ^ m = 3 ^ m ∨ (-3 : ℝ) ^ m = -3 ^ m := by
  rw [neg_pow]
  rcases neg_one_pow_eq_or ℝ m with h | h <;> rw [h]
  · left; ring
  · right; ring

/-- `|t^(2m) - ω^u|^2`, with `s = (-3)^m`: `(s - 1)^2` for `u ≡ 0`, and `s^2 + s + 1`
otherwise. -/
theorem norm_sq_even (m u : ℕ) :
    ‖t3 ^ (2 * m) - w3 ^ u‖ ^ 2 =
      if u % 3 = 0 then ((-3 : ℝ) ^ m - 1) ^ 2 else ((-3 : ℝ) ^ m) ^ 2 + (-3 : ℝ) ^ m + 1 := by
  have h3 := sqrt3_mul_self
  rw [norm_sq_eq, t3_pow_even, w3_pow_mod u]
  have h : u % 3 < 3 := Nat.mod_lt _ (by norm_num)
  obtain ⟨x, hx⟩ : ∃ x, u % 3 = x := ⟨_, rfl⟩
  rw [hx] at h ⊢
  interval_cases x
  · simp only [pow_zero, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, ↓reduceIte]
    ring
  · simp only [pow_one, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      w3, one_ne_zero, ↓reduceIte]
    linear_combination (1 / 4 : ℝ) * h3
  · rw [w3_sq]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      OfNat.ofNat_ne_zero, ↓reduceIte]
    linear_combination (1 / 4 : ℝ) * h3

/-- `|t^(2m+1) - ω^u|^2`, with `s = (-3)^m`: `3 s^2 + 1`, `3 s^2 - 3 s + 1`, `3 s^2 + 3 s + 1`
for `u ≡ 0, 1, 2`. -/
theorem norm_sq_odd (m u : ℕ) :
    ‖t3 ^ (2 * m + 1) - w3 ^ u‖ ^ 2 =
      if u % 3 = 0 then 3 * ((-3 : ℝ) ^ m) ^ 2 + 1
      else if u % 3 = 1 then 3 * ((-3 : ℝ) ^ m) ^ 2 - 3 * (-3 : ℝ) ^ m + 1
      else 3 * ((-3 : ℝ) ^ m) ^ 2 + 3 * (-3 : ℝ) ^ m + 1 := by
  have h3 := sqrt3_mul_self
  rw [norm_sq_eq, t3_pow_odd, w3_pow_mod u]
  have h : u % 3 < 3 := Nat.mod_lt _ (by norm_num)
  obtain ⟨x, hx⟩ : ∃ x, u % 3 = x := ⟨_, rfl⟩
  rw [hx] at h ⊢
  interval_cases x
  · simp only [pow_zero, Complex.sub_re, Complex.sub_im, Complex.mul_I_re, Complex.mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, ↓reduceIte]
    linear_combination ((-3 : ℝ) ^ m) ^ 2 * h3
  · simp only [pow_one, Complex.sub_re, Complex.sub_im, Complex.mul_I_re, Complex.mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, w3, one_ne_zero, ↓reduceIte]
    linear_combination ((-3 : ℝ) ^ m - 1 / 2) ^ 2 * h3
  · rw [w3_sq]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_I_re, Complex.mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, OfNat.ofNat_ne_zero, ↓reduceIte,
      show (2 : ℕ) ≠ 1 by norm_num]
    linear_combination ((-3 : ℝ) ^ m + 1 / 2) ^ 2 * h3

theorem log_norm_eq_half (z : ℂ) : Real.log ‖z‖ = (1 / 2 : ℝ) * Real.log (‖z‖ ^ 2) := by
  rw [Real.log_pow]
  push_cast
  ring

/-! ## 3. The two spans are equal -/

/-- Every `log |t^n - c|` is a rational combination of logarithms of base numbers. -/
theorem generator_mem_baseSpan3 {n : ℕ} (hn : 0 < n) {c : ℂ} (hc : c ^ 3 = 1) :
    Real.log ‖t3 ^ n - c‖ ∈ baseSpan3 := by
  obtain ⟨u, rfl⟩ := eq_w3_pow_of_cube hc
  rw [log_norm_eq_half]
  have key : Real.log (‖t3 ^ n - w3 ^ u‖ ^ 2) ∈ baseSpan3 := by
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have hm : 0 < m := by omega
      rw [norm_sq_even]
      split_ifs
      · rcases neg_three_pow_cases m with h | h <;> rw [h]
        · rw [Real.log_pow]
          exact_mod_cast rat_mul_mem_baseSpan3 (log_pow_sub_one_mem hm) 2
        · rw [show (-(3 : ℝ) ^ m - 1) ^ 2 = ((3 : ℝ) ^ m + 1) ^ 2 by ring, Real.log_pow]
          exact_mod_cast rat_mul_mem_baseSpan3 (log_pow_add_one_mem hm) 2
      · rcases neg_three_pow_cases m with h | h <;> rw [h]
        · exact log_sq_add_mem hm
        · rw [show (-(3 : ℝ) ^ m) ^ 2 + -(3 : ℝ) ^ m + 1 = ((3 : ℝ) ^ m) ^ 2 - 3 ^ m + 1 by ring]
          exact log_sq_sub_mem hm
    · rw [norm_sq_odd]
      split_ifs
      · rcases neg_three_pow_cases m with h | h <;> rw [h]
        · rw [show 3 * ((3 : ℝ) ^ m) ^ 2 + 1 = (3 : ℝ) ^ (2 * m + 1) + 1 by ring]
          exact log_pow_add_one_mem (by omega)
        · rw [show 3 * (-(3 : ℝ) ^ m) ^ 2 + 1 = (3 : ℝ) ^ (2 * m + 1) + 1 by ring]
          exact log_pow_add_one_mem (by omega)
      · rcases neg_three_pow_cases m with h | h <;> rw [h]
        · rw [show 3 * ((3 : ℝ) ^ m) ^ 2 - 3 * (3 : ℝ) ^ m + 1 =
            (3 : ℝ) ^ (2 * m + 1) - 3 ^ (m + 1) + 1 by ring]
          exact log_L_mem m
        · rw [show 3 * (-(3 : ℝ) ^ m) ^ 2 - 3 * -(3 : ℝ) ^ m + 1 =
            (3 : ℝ) ^ (2 * m + 1) + 3 ^ (m + 1) + 1 by ring]
          exact log_M_mem m
      · rcases neg_three_pow_cases m with h | h <;> rw [h]
        · rw [show 3 * ((3 : ℝ) ^ m) ^ 2 + 3 * (3 : ℝ) ^ m + 1 =
            (3 : ℝ) ^ (2 * m + 1) + 3 ^ (m + 1) + 1 by ring]
          exact log_M_mem m
        · rw [show 3 * (-(3 : ℝ) ^ m) ^ 2 + 3 * -(3 : ℝ) ^ m + 1 =
            (3 : ℝ) ^ (2 * m + 1) - 3 ^ (m + 1) + 1 by ring]
          exact log_L_mem m
  have h := rat_mul_mem_baseSpan3 key (1 / 2)
  convert h using 2
  push_cast
  ring

theorem logSpan3_le_baseSpan3 : logSpan3 ≤ baseSpan3 := by
  refine Submodule.span_le.2 ?_
  rintro x (rfl | ⟨n, c, hn, hc, rfl⟩)
  · exact log_three_mem_baseSpan3
  · exact generator_mem_baseSpan3 hn hc

/-- `log |t^(2m) - 1| = log |(-3)^m - 1|`. -/
theorem log_norm_even_one (m : ℕ) :
    Real.log ‖t3 ^ (2 * m) - 1‖ = Real.log ((-3 : ℝ) ^ m - 1) := by
  have h := norm_sq_even m 0
  simp only [pow_zero, Nat.zero_mod, ↓reduceIte] at h
  rw [log_norm_eq_half, h, Real.log_pow]
  push_cast
  ring

theorem gen_even_one_mem (m : ℕ) (hm : 0 < m) : Real.log ‖t3 ^ (2 * m) - 1‖ ∈ logSpan3 :=
  log_norm_t3_pow_sub_mem (by omega) (one_pow 3)

theorem log_pow_sub_one_mem_logSpan3 {m : ℕ} (hm : 0 < m) :
    Real.log ((3 : ℝ) ^ m - 1) ∈ logSpan3 := by
  have h1 : (1 : ℝ) < 3 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
  rcases neg_three_pow_cases m with h | h
  · have hA := gen_even_one_mem m hm
    rwa [log_norm_even_one, h] at hA
  · -- `|(-3)^m - 1| = 3^m + 1`, and `|(-3)^(2m) - 1| = (3^m - 1)(3^m + 1)`
    have hA := gen_even_one_mem m hm
    rw [log_norm_even_one, h, show -(3 : ℝ) ^ m - 1 = -((3 : ℝ) ^ m + 1) by ring,
      Real.log_neg_eq_log] at hA
    have hB := gen_even_one_mem (2 * m) (by omega)
    have e2 : (-3 : ℝ) ^ (2 * m) = ((3 : ℝ) ^ m) ^ 2 := by
      rw [pow_mul]
      norm_num
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [log_norm_even_one, e2,
      show ((3 : ℝ) ^ m) ^ 2 - 1 = ((3 : ℝ) ^ m - 1) * ((3 : ℝ) ^ m + 1) by ring,
      Real.log_mul (by linarith) (by linarith)] at hB
    have h5 := sub_mem hB hA
    convert h5 using 1
    ring

theorem baseSpan3_le_logSpan3 : baseSpan3 ≤ logSpan3 := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨g, hg, rfl⟩
  change Real.log (g : ℝ) ∈ logSpan3
  rcases hg with rfl | ⟨m, hm, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simpa using log_three_mem_logSpan3
  · have h := log_pow_sub_one_mem_logSpan3 hm
    have e : (((3 : ℤ) ^ m - 1 : ℤ) : ℝ) = (3 : ℝ) ^ m - 1 := by push_cast; ring
    rwa [← e] at h
  · -- one of `ω`, `ω²` gives this factor
    have e : (((3 : ℤ) ^ (2 * k + 1) - 3 ^ (k + 1) + 1 : ℤ) : ℝ) =
        (3 : ℝ) ^ (2 * k + 1) - 3 ^ (k + 1) + 1 := by push_cast; ring
    rw [e]
    rcases neg_three_pow_cases k with h | h
    · have hg := log_norm_t3_pow_sub_mem (n := 2 * k + 1) (by omega)
        (w := w3 ^ 1) (by rw [← pow_mul]; exact w3_pow_three)
      have hn := norm_sq_odd k 1
      simp only [Nat.one_mod, one_ne_zero, ↓reduceIte] at hn
      rw [h, show 3 * ((3 : ℝ) ^ k) ^ 2 - 3 * (3 : ℝ) ^ k + 1 =
        (3 : ℝ) ^ (2 * k + 1) - 3 ^ (k + 1) + 1 by ring] at hn
      rw [← hn, Real.log_pow]
      exact_mod_cast rat_mul_mem_logSpan3 hg 2
    · have hg := log_norm_t3_pow_sub_mem (n := 2 * k + 1) (by omega)
        (w := w3 ^ 2) (by rw [← pow_mul, mul_comm, pow_mul, w3_pow_three, one_pow])
      have hn := norm_sq_odd k 2
      simp only [Nat.mod_succ, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte] at hn
      rw [h, show 3 * (-(3 : ℝ) ^ k) ^ 2 + 3 * -(3 : ℝ) ^ k + 1 =
        (3 : ℝ) ^ (2 * k + 1) - 3 ^ (k + 1) + 1 by ring] at hn
      rw [← hn, Real.log_pow]
      exact_mod_cast rat_mul_mem_logSpan3 hg 2
  · have e : (((3 : ℤ) ^ (2 * k + 1) + 3 ^ (k + 1) + 1 : ℤ) : ℝ) =
        (3 : ℝ) ^ (2 * k + 1) + 3 ^ (k + 1) + 1 := by push_cast; ring
    rw [e]
    rcases neg_three_pow_cases k with h | h
    · have hg := log_norm_t3_pow_sub_mem (n := 2 * k + 1) (by omega)
        (w := w3 ^ 2) (by rw [← pow_mul, mul_comm, pow_mul, w3_pow_three, one_pow])
      have hn := norm_sq_odd k 2
      simp only [Nat.mod_succ, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte] at hn
      rw [h, show 3 * ((3 : ℝ) ^ k) ^ 2 + 3 * (3 : ℝ) ^ k + 1 =
        (3 : ℝ) ^ (2 * k + 1) + 3 ^ (k + 1) + 1 by ring] at hn
      rw [← hn, Real.log_pow]
      exact_mod_cast rat_mul_mem_logSpan3 hg 2
    · have hg := log_norm_t3_pow_sub_mem (n := 2 * k + 1) (by omega)
        (w := w3 ^ 1) (by rw [← pow_mul]; exact w3_pow_three)
      have hn := norm_sq_odd k 1
      simp only [Nat.one_mod, one_ne_zero, ↓reduceIte] at hn
      rw [h, show 3 * (-(3 : ℝ) ^ k) ^ 2 - 3 * -(3 : ℝ) ^ k + 1 =
        (3 : ℝ) ^ (2 * k + 1) + 3 ^ (k + 1) + 1 by ring] at hn
      rw [← hn, Real.log_pow]
      exact_mod_cast rat_mul_mem_logSpan3 hg 2

theorem logSpan3_eq_baseSpan3 : logSpan3 = baseSpan3 :=
  le_antisymm logSpan3_le_baseSpan3 baseSpan3_le_logSpan3

/-! ## 4. The criterion in elementary terms -/

/-- **The "if" half, without Baker.** If some power `y^k`, `k ≥ 1`, of a positive rational
`y` is a product of integer powers of base numbers, then `log y` is the value of a series of
the class F3. -/
theorem isF3Value_log_of_pow {y : ℚ} (hy : 0 < y) {k : ℕ} (hk : 0 < k) {n : ℕ}
    {g : Fin n → ℤ} {e : Fin n → ℤ} (hg : ∀ i, g i ∈ baseNumbers3)
    (h : y ^ k = ∏ i, (g i : ℚ) ^ e i) : IsF3Value (Real.log (y : ℝ)) := by
  have h1 : Real.log (y : ℝ) ∈ baseSpan3 :=
    (log_mem_span_iff_pow (fun g hg => baseNumbers3_pos hg) hy).2 ⟨k, hk, n, g, e, hg, h⟩
  rw [← logSpan3_eq_baseSpan3] at h1
  exact isF3Value_of_mem_logSpan3 h1

/-- **The criterion for base 3 in elementary terms** (from Baker's theorem). For a positive
rational number `y`, `log y` is the value of a series `∑ ρ(k) 3^(-⌊k/2⌋)/k` with `ρ` rational
and periodic if and only if some power `y^k`, `k ≥ 1`, is a product of integer powers of the
numbers `3`, `3^m - 1`, `3^(2j+1) - 3^(j+1) + 1` and `3^(2j+1) + 3^(j+1) + 1`. -/
theorem isF3Value_log_rat_iff_pow (hB : BakerTheorem) {y : ℚ} (hy : 0 < y) :
    IsF3Value (Real.log (y : ℝ)) ↔
      ∃ k : ℕ, 0 < k ∧ ∃ (n : ℕ) (g : Fin n → ℤ) (e : Fin n → ℤ),
        (∀ i, g i ∈ baseNumbers3) ∧ y ^ k = ∏ i, (g i : ℚ) ^ e i := by
  rw [isF3Value_log_rat_iff hB hy, logSpan3_eq_baseSpan3]
  exact log_mem_span_iff_pow (fun g hg => baseNumbers3_pos hg) hy

/-! ## 5. Examples -/

theorem isF3Value_log_int {g : ℤ} (hg : g ∈ baseNumbers3) : IsF3Value (Real.log (g : ℝ)) := by
  have h := log_mem_baseSpan3 hg
  rw [← logSpan3_eq_baseSpan3] at h
  exact isF3Value_of_mem_logSpan3 h

/-- `2 = 3 - 1`. -/
theorem isF3Value_log_2 : IsF3Value (Real.log 2) := by
  have h := isF3Value_log_int (g := 2) (Or.inr (Or.inl ⟨1, one_pos, by norm_num⟩))
  simpa using h

/-- `7 = 3 + 3 + 1`. -/
theorem isF3Value_log_7 : IsF3Value (Real.log 7) := by
  have h := isF3Value_log_int (g := 7) (Or.inr (Or.inr (Or.inr ⟨0, by norm_num⟩)))
  simpa using h

/-- `19 = 3^3 - 3^2 + 1`. -/
theorem isF3Value_log_19 : IsF3Value (Real.log 19) := by
  have h := isF3Value_log_int (g := 19) (Or.inr (Or.inr (Or.inl ⟨1, by norm_num⟩)))
  simpa using h

/-- `37 = 3^3 + 3^2 + 1`. -/
theorem isF3Value_log_37 : IsF3Value (Real.log 37) := by
  have h := isF3Value_log_int (g := 37) (Or.inr (Or.inr (Or.inr ⟨1, by norm_num⟩)))
  simpa using h

/-- `13 = (3^3 - 1) / 2`. -/
theorem isF3Value_log_13 : IsF3Value (Real.log 13) := by
  have h26 := isF3Value_log_int (g := 26) (Or.inr (Or.inl ⟨3, by norm_num, by norm_num⟩))
  have h := h26.sub isF3Value_log_2
  have e : Real.log ((26 : ℤ) : ℝ) - Real.log 2 = Real.log 13 := by
    rw [show ((26 : ℤ) : ℝ) = 13 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rwa [e] at h

/-- `5 = (3^4 - 1) / 2^4`. -/
theorem isF3Value_log_5 : IsF3Value (Real.log 5) := by
  have h80 := isF3Value_log_int (g := 80) (Or.inr (Or.inl ⟨4, by norm_num, by norm_num⟩))
  have h := h80.sub (isF3Value_log_2.const_mul 4)
  have e : Real.log ((80 : ℤ) : ℝ) - ((4 : ℚ) : ℝ) * Real.log 2 = Real.log 5 := by
    rw [show ((80 : ℤ) : ℝ) = 5 * 2 ^ 4 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  rwa [e] at h

/-- `11^2 = (3^5 - 1) / 2`. -/
theorem isF3Value_log_11 : IsF3Value (Real.log 11) := by
  have h242 := isF3Value_log_int (g := 242) (Or.inr (Or.inl ⟨5, by norm_num, by norm_num⟩))
  have h := (h242.sub isF3Value_log_2).const_mul (1 / 2)
  have e : ((1 / 2 : ℚ) : ℝ) * (Real.log ((242 : ℤ) : ℝ) - Real.log 2) = Real.log 11 := by
    rw [show ((242 : ℤ) : ℝ) = 11 ^ 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  rwa [e] at h

end Base3

end PiFormula
