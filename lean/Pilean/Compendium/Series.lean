/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Compendium.Base2Pi
public import Pilean.Compendium.Logs

/-!
# Bailey's Compendium: the formulas printed as explicit series only

Four formulas of degree 1 are printed as a series in `k`, not in the notation `P`. They are
stated as `HasSum` of the printed term. The file also has the chain of equalities that leads
to formula (8), a closed form, and formulas (1) and (2) as the series that are printed.

* `formula_p05_c` (page 5, without number): the four steps from `log 3 = 2 log 2 +
  log (1 - 1/4)` to formula (8), each as a statement about convergent series.
* `formula_p05_e` (page 5, without number): Harley's identity
  `Re log (1 ± (1 + i)/2^n) = (1/2 - n) log 2 + (1/2) log (2^(2n-1) ± 2^n + 1)`, for `n ≥ 1`.
* `formula_1_series`, `formula_2_series`: formulas (1) and (2) as printed, from `formula_1`
  and `formula_2` (which state them in the notation `P`, as the ledger records them).

* `formula_4` (page 2): `log 2 = ∑_{k ≥ 1} 1 / (k 2^k)`. The sum over `k ≥ 1` is written over
  `k ≥ 0` with `k + 1` in place of `k`. It is `BaseB.hasSum_log_two`.
* `formula_p02_g` (page 2, without number): formula (1) with its four fractions combined,
  `π = ∑_{k ≥ 0} (47 + 151 k + 120 k²) / (16^k (15 + 194 k + 712 k² + 1024 k³ + 512 k⁴))`.
  It is `BaseB.bbp_formula`.
* `formula_p25_c` (page 25, without number):
  `log 3 = ∑_{k ≥ 0} (9/(2k+1) + 1/(2k+2)) / 9^(k+1)`. It is `BaseB.hasSum_log_three`.
* `formula_p25_b` (page 25, without number):
  `log 3 = 1/4 + (1/4) ∑_{k ≥ 0} (27/(2k+1) + 4/(2k+2) + 1/(2k+3)) / 9^(k+1)`. The term is three
  times the term of `formula_p25_c` plus `(1/(2k+2) + 1/(2k+3)) / 9^(k+1)`, and the second
  series is the series `∑_{m ≥ 1} g(m) 3^(-m) / m` of `log 3` (`g = 3` for odd `m`, `g = 1` for
  even `m`) without its first term, which is 1. So the sum is `4 log 3 - 1`.
-/

@[expose] public section

namespace PiFormula

namespace Compendium

open BaseB

/-- **Formula (4)** of the Compendium (page 2): `log 2 = ∑_{k ≥ 1} 1 / (k 2^k)`. -/
theorem formula_4 :
    HasSum (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) * 2 ^ (k + 1))) (Real.log 2) := by
  have h : HasSum (BaseB.baileyBlock 2 1 1 ![1 / 2]) (Real.log 2) := hasSum_log_two
  have e : BaseB.baileyBlock 2 1 1 ![1 / 2] =
      fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) * 2 ^ (k + 1)) := by
    funext k
    simp only [BaseB.baileyBlock, Fin.sum_univ_one, Matrix.cons_val_zero, Fin.val_zero,
      one_mul, add_zero]
    push_cast
    field_simp
    ring
  rw [e] at h
  exact h

/-- **The formula of Bailey, Borwein and Plouffe as one fraction** (page 2 of the Compendium,
without number):
`π = ∑_{k ≥ 0} (47 + 151 k + 120 k²) / (16^k (15 + 194 k + 712 k² + 1024 k³ + 512 k⁴))`. -/
theorem formula_p02_g :
    HasSum (fun k : ℕ => (47 + 151 * (k : ℝ) + 120 * (k : ℝ) ^ 2) /
      (16 ^ k * (15 + 194 * (k : ℝ) + 712 * (k : ℝ) ^ 2 + 1024 * (k : ℝ) ^ 3 + 512 * (k : ℝ) ^ 4)))
      Real.pi := by
  have h : HasSum (BaseB.baileyBlock 16 1 8 ![4, 0, 0, -2, -1, -1, 0, 0]) Real.pi := bbp_formula
  have e : BaseB.baileyBlock 16 1 8 ![4, 0, 0, -2, -1, -1, 0, 0] = fun k : ℕ =>
      (47 + 151 * (k : ℝ) + 120 * (k : ℝ) ^ 2) /
        (16 ^ k * (15 + 194 * (k : ℝ) + 712 * (k : ℝ) ^ 2 + 1024 * (k : ℝ) ^ 3
          + 512 * (k : ℝ) ^ 4)) := by
    funext k
    have h1 : (8 * (k : ℝ) + 1) ≠ 0 := by positivity
    have h4 : (8 * (k : ℝ) + 4) ≠ 0 := by positivity
    have h5 : (8 * (k : ℝ) + 5) ≠ 0 := by positivity
    have h6 : (8 * (k : ℝ) + 6) ≠ 0 := by positivity
    have hd : (15 + 194 * (k : ℝ) + 712 * (k : ℝ) ^ 2 + 1024 * (k : ℝ) ^ 3
        + 512 * (k : ℝ) ^ 4) ≠ 0 := by positivity
    simp only [BaseB.baileyBlock, Fin.sum_univ_eight, one_mul]
    simp
    field_simp
    ring
  rw [e] at h
  exact h

/-- **A series for `log 3`** (page 25 of the Compendium, without number):
`log 3 = ∑_{k ≥ 0} (9/(2k+1) + 1/(2k+2)) / 9^(k+1)`. -/
theorem formula_p25_c :
    HasSum (fun k : ℕ => (9 / (2 * (k : ℝ) + 1) + 1 / (2 * (k : ℝ) + 2)) / 9 ^ (k + 1))
      (Real.log 3) := by
  have h : HasSum (BaseB.baileyBlock 3 2 2 ![1, 1 / 9]) (Real.log 3) := hasSum_log_three
  have e : BaseB.baileyBlock 3 2 2 ![1, 1 / 9] =
      fun k : ℕ => (9 / (2 * (k : ℝ) + 1) + 1 / (2 * (k : ℝ) + 2)) / 9 ^ (k + 1) := by
    funext k
    have e9 : (3 : ℝ) ^ (2 * k) = 9 ^ k := by
      rw [pow_mul]
      norm_num
    have h1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    simp only [BaseB.baileyBlock, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, add_zero, e9, Nat.cast_ofNat]
    push_cast
    field_simp
    ring
  rw [e] at h
  exact h

/-- The series of `log 3` without its first term:
`∑_{k ≥ 0} (1/(2k+2) + 1/(2k+3)) / 9^(k+1) = log 3 - 1`. -/
theorem hasSum_log_three_tail :
    HasSum (fun k : ℕ => (1 / (2 * (k : ℝ) + 2) + 1 / (2 * (k : ℝ) + 3)) / 9 ^ (k + 1))
      (Real.log 3 - 1) := by
  have hL := hasSum_listPat (b := 3) (by norm_num) [(1, 3), (2, -2)] (by decide)
  have t1 : logTerm 3 1 = Real.log 3 - Real.log 2 / 1 := by
    exact_mod_cast logTerm_eq (b := 3) (d := 1) (m := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have t2 : logTerm 3 2 = Real.log 3 - Real.log 8 / 2 := by
    exact_mod_cast logTerm_eq (b := 3) (d := 2) (m := 8) (by norm_num) (by norm_num)
      (by norm_num)
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  have hv : listVal 3 [(1, 3), (2, -2)] = Real.log 3 := by
    rw [listVal_cons, listVal_cons, listVal_nil, t1, t2, l8]
    push_cast
    ring
  rw [hv] at hL
  -- drop the terms at `m = 0, 1` and sum in pairs
  have h2 := (hasSum_nat_add_iff' 2).2 hL
  have h3 := hasSum_group two_pos h2
  have e : (fun j : ℕ => ∑ t : Fin 2,
      (((listPat [(1, 3), (2, -2)] (2 * j + t + 2) : ℚ) : ℝ) / ((3 : ℕ) : ℝ) ^ (2 * j + t + 2) /
        ((2 * j + t + 2 : ℕ) : ℝ))) =
      fun k : ℕ => (1 / (2 * (k : ℝ) + 2) + 1 / (2 * (k : ℝ) + 3)) / 9 ^ (k + 1) := by
    funext j
    have e9 : ((3 : ℕ) : ℝ) ^ (2 * j) = 9 ^ j := by
      rw [pow_mul]
      norm_num
    have p0 : listPat [(1, 3), (2, -2)] (2 * j + 0 + 2) = 1 := by
      have hd : 2 ∣ 2 * j + 0 + 2 := ⟨j + 1, by ring⟩
      simp only [listPat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_dvd,
        hd, ↓reduceIte]
      norm_num
    have p1 : listPat [(1, 3), (2, -2)] (2 * j + 1 + 2) = 3 := by
      have hd : ¬ 2 ∣ 2 * j + 1 + 2 := by omega
      simp only [listPat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_dvd,
        hd, ↓reduceIte]
      norm_num
    have h2 : (2 * (j : ℝ) + 2) ≠ 0 := by positivity
    have h3 : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, p0, p1, pow_add, e9]
    push_cast
    field_simp
    ring
  rw [e] at h3
  convert h3 using 1
  simp [Finset.sum_range_succ, listPat]

/-- **A series for `log 3`** (page 25 of the Compendium, without number):
`log 3 = 1/4 + (1/4) ∑_{k ≥ 0} (27/(2k+1) + 4/(2k+2) + 1/(2k+3)) / 9^(k+1)`. -/
theorem formula_p25_b : ∃ S : ℝ,
    HasSum (fun k : ℕ => (27 / (2 * (k : ℝ) + 1) + 4 / (2 * (k : ℝ) + 2) + 1 / (2 * (k : ℝ) + 3)) /
      9 ^ (k + 1)) S ∧ Real.log 3 = 1 / 4 + 1 / 4 * S := by
  refine ⟨3 * Real.log 3 + (Real.log 3 - 1), ?_, by ring⟩
  have h := (formula_p25_c.mul_left 3).add hasSum_log_three_tail
  refine h.congr_fun fun k => ?_
  ring

/-! ## 2. The steps that lead to formula (8) -/

/-- `∑_{k ≥ 1} 1 / (k 4^k) = -log (1 - 1/4)`. -/
theorem hasSum_inv_mul_four_pow :
    HasSum (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) * 4 ^ (k + 1))) (-Real.log (1 - 1 / 4)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / 4)
    (by rw [abs_of_pos] <;> norm_num)
  refine h.congr_fun fun k => ?_
  rw [one_div_pow]
  push_cast
  field_simp

/-- **The derivation of formula (8)** (page 5 of the Compendium, without number), step by step:
`log 3 = 2 log 2 + log (1 - 1/4) = 2 ∑_{k ≥ 1} 1/(k 2^k) - ∑_{k ≥ 1} 1/(k 4^k)`
`= (1/2) ∑_{k ≥ 0} (2/(2k+1) + 1/(2k+2)) / 4^k - (1/4) ∑_{k ≥ 0} (2/(2k+2)) / 4^k`
`= ∑_{k ≥ 0} (1/(2k+1)) / 4^k`. -/
theorem formula_p05_c :
    Real.log 3 = 2 * Real.log 2 + Real.log (1 - 1 / 4) ∧
    (∃ S T : ℝ, HasSum (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) * 2 ^ (k + 1))) S ∧
      HasSum (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) * 4 ^ (k + 1))) T ∧
      Real.log 3 = 2 * S - T) ∧
    (∃ S T : ℝ,
      HasSum (fun k : ℕ => (2 / (2 * (k : ℝ) + 1) + 1 / (2 * (k : ℝ) + 2)) / 4 ^ k) S ∧
      HasSum (fun k : ℕ => 2 / (2 * (k : ℝ) + 2) / 4 ^ k) T ∧
      Real.log 3 = 1 / 2 * S - 1 / 4 * T) ∧
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) / 4 ^ k) (Real.log 3) := by
  have h1 : Real.log 3 = 2 * Real.log 2 + Real.log (1 - 1 / 4) := by
    rw [show (1 - 1 / 4 : ℝ) = 3 / 2 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  refine ⟨h1, ⟨_, _, formula_4, hasSum_inv_mul_four_pow, by linarith⟩,
    ⟨4 * Real.log 2, 4 * -Real.log (1 - 1 / 4), ?_, ?_, ?_⟩, ?_⟩
  · -- the series of `log 2`, summed in pairs
    refine ((hasSum_group two_pos formula_4).mul_left 4).congr_fun fun k => ?_
    have e4 : (2 : ℝ) ^ (2 * k) = 4 ^ k := by
      rw [pow_mul]
      norm_num
    have h1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_add, e4]
    push_cast
    field_simp
    ring
  · refine (hasSum_inv_mul_four_pow.mul_left 4).congr_fun fun k => ?_
    have h2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · linarith
  · have h := baileyFormula_one_iff.1 formula_8
    refine HasSum.congr_fun h fun k => ?_
    simp only [BaseB.baileyBlock, Fin.sum_univ_two, one_mul]
    simp
    ring

/-! ## 3. Formulas (1) and (2) as they are printed -/

/-- **Formula (1)** of the Compendium (page 1), as the explicit series that is printed:
`π = ∑_{k ≥ 0} 16^(-k) (4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6))`. -/
theorem formula_1_series :
    HasSum (fun k : ℕ => 1 / 16 ^ k * (4 / (8 * (k : ℝ) + 1) - 2 / (8 * (k : ℝ) + 4)
      - 1 / (8 * (k : ℝ) + 5) - 1 / (8 * (k : ℝ) + 6))) Real.pi := by
  have h := baileyFormula_one_iff.1 formula_1
  refine HasSum.congr_fun h fun k => ?_
  simp only [BaseB.baileyBlock, Fin.sum_univ_eight, one_mul]
  simp
  ring

/-- **Formula (2)** of the Compendium (page 2), as the explicit series that is printed:
`π = ∑_{k ≥ 0} (-1)^k 4^(-k) (2/(4k+1) + 2/(4k+2) + 1/(4k+3))`. -/
theorem formula_2_series :
    HasSum (fun k : ℕ => (-1) ^ k / 4 ^ k * (2 / (4 * (k : ℝ) + 1) + 2 / (4 * (k : ℝ) + 2)
      + 1 / (4 * (k : ℝ) + 3))) Real.pi := by
  obtain ⟨S, hS, e⟩ := formula_2
  rw [one_mul] at e
  rw [e]
  refine HasSum.congr_fun hS fun k => ?_
  have e4 : ((-4 : ℤ) : ℝ) ^ k = (-1) ^ k * 4 ^ k := by
    rw [← mul_pow]
    norm_num
  have hs : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have hm : (-1 : ℝ) ^ k / 4 ^ k = 1 / ((-1) ^ k * 4 ^ k) := by
    rw [div_eq_div_iff (by positivity) (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by positivity))]
    linear_combination (4 : ℝ) ^ k * hs
  simp only [baileyBlockInt, Fin.sum_univ_four, one_mul, e4, hm]
  simp
  ring

/-! ## 4. A closed form -/

/-- The identity of `formula_p05_e` for one sign `s = ±1`. -/
theorem log_re_one_add (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    (Complex.log (1 + (s : ℂ) * (1 + Complex.I) / 2 ^ n)).re =
      (1 / 2 - n) * Real.log 2 + 1 / 2 * Real.log (2 ^ (2 * n - 1) + s * 2 ^ n + 1) := by
  have hY : (0 : ℝ) < 2 ^ n := by positivity
  have hY2 : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hpow : (2 : ℝ) ^ (2 * n - 1) = (2 ^ n) ^ 2 / 2 := by
    rw [eq_div_iff (by norm_num), ← pow_succ, ← pow_mul, show 2 * n - 1 + 1 = n * 2 by omega]
  have hss : s ^ 2 = 1 := by
    rcases hs with rfl | rfl <;> norm_num
  have hW : 0 < (2 : ℝ) ^ (2 * n - 1) + s * 2 ^ n + 1 := by
    rw [hpow]
    rcases hs with rfl | rfl <;> nlinarith [sq_nonneg ((2 : ℝ) ^ n - 1)]
  have ez : (1 + (s : ℂ) * (1 + Complex.I) / 2 ^ n) =
      1 + ((s / 2 ^ n : ℝ) : ℂ) * (1 + Complex.I) := by
    push_cast
    ring
  have hnorm : ‖1 + ((s / 2 ^ n : ℝ) : ℂ) * (1 + Complex.I)‖ ^ 2 =
      2 * (2 ^ (2 * n - 1) + s * 2 ^ n + 1) / (2 ^ n) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hpow]
    simp only [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul, Complex.I_re, add_zero,
      mul_one, Complex.add_im, Complex.one_im, Complex.im_ofReal_mul, Complex.I_im, zero_add]
    field_simp
    linear_combination 2 * hss
  have hlog : Real.log ‖1 + ((s / 2 ^ n : ℝ) : ℂ) * (1 + Complex.I)‖ =
      1 / 2 * Real.log (‖1 + ((s / 2 ^ n : ℝ) : ℂ) * (1 + Complex.I)‖ ^ 2) := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [ez, Complex.log_re, hlog, hnorm, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by norm_num) hW.ne', Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- **Harley's identity** (page 5 of the Compendium, without number): for `n ≥ 1`,
`Re log (1 ± (1 + i)/2^n) = (1/2 - n) log 2 + (1/2) log (2^(2n-1) ± 2^n + 1)`. -/
theorem formula_p05_e (n : ℕ) (hn : 1 ≤ n) :
    (Complex.log (1 + (1 + Complex.I) / 2 ^ n)).re =
        (1 / 2 - n) * Real.log 2 + 1 / 2 * Real.log (2 ^ (2 * n - 1) + 2 ^ n + 1) ∧
      (Complex.log (1 - (1 + Complex.I) / 2 ^ n)).re =
        (1 / 2 - n) * Real.log 2 + 1 / 2 * Real.log (2 ^ (2 * n - 1) - 2 ^ n + 1) := by
  have hp := log_re_one_add n hn (s := 1) (Or.inl rfl)
  have hm := log_re_one_add n hn (s := -1) (Or.inr rfl)
  constructor
  · rw [Complex.ofReal_one, one_mul, one_mul] at hp
    exact hp
  · have e : (1 - (1 + Complex.I) / 2 ^ n : ℂ) =
        1 + ((-1 : ℝ) : ℂ) * (1 + Complex.I) / 2 ^ n := by
      push_cast
      ring
    rw [e, hm, neg_one_mul, ← sub_eq_add_neg]

end Compendium

end PiFormula
