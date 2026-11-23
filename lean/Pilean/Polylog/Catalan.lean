import Pilean.Polylog.DilogComplex

/-!
# Catalan's constant and the dilogarithm at `i` and `(1 + i)/2`

Mathlib has no Catalan constant. Here `catalanConst = ∑_{k ≥ 0} (-1)^k / (2k+1)²`.

* `hasSum_catalanConst`: the series converges (to `catalanConst`);
* `polylog_two_I_im : Im Li_2(i) = G`, `polylog_two_I_re : Re Li_2(i) = -π²/48`;
* `polylog_two_half_add_half_I_re : Re Li_2((1+i)/2) = 5π²/96 - (log 2)²/8`
  (reflection formula: `1 - z = conj z`);
* `polylog_two_half_add_half_I_im : Im Li_2((1+i)/2) = G - π log 2 / 8`
  (Landen's identity: `z / (z - 1) = -i`).
-/

namespace PiFormula

namespace Polylog

open Complex

/-- **Catalan's constant** `G = 1 - 1/3² + 1/5² - 1/7² + ⋯`. -/
noncomputable def catalanConst : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2

theorem I_pow_two_mul (k : ℕ) : I ^ (2 * k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
  rw [pow_mul, I_sq]
  simp

theorem I_pow_two_mul_add_one (k : ℕ) : I ^ (2 * k + 1) = (((-1 : ℝ) ^ k : ℝ) : ℂ) * I := by
  rw [pow_succ, I_pow_two_mul]

/-- The series of Catalan's constant is the imaginary part of the series of `Li_2(i)`. -/
theorem hasSum_im_polylog_two_I :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2) (polylog 2 I).im := by
  have h := hasSum_im_polylog_nat (s := 2) le_rfl (z := I) (by simp)
  have hinj : Function.Injective fun k : ℕ => 2 * k + 1 := fun a b hab => by
    have hab' : 2 * a + 1 = 2 * b + 1 := hab
    omega
  have hoff : ∀ m ∉ Set.range (fun k : ℕ => 2 * k + 1), (I ^ m).im / (m : ℝ) ^ 2 = 0 := by
    intro m hm
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [I_pow_two_mul, Complex.ofReal_im, zero_div]
    · exact absurd ⟨k, rfl⟩ hm
  have h2 := (hinj.hasSum_iff hoff).2 h
  refine h2.congr_fun fun k => ?_
  simp only [Function.comp_apply]
  rw [I_pow_two_mul_add_one, Complex.im_ofReal_mul, Complex.I_im, mul_one]
  push_cast
  ring

/-- **The series of Catalan's constant converges**:
`∑_{k ≥ 0} (-1)^k / (2k+1)² = G`. -/
theorem hasSum_catalanConst :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2) catalanConst :=
  hasSum_im_polylog_two_I.summable.hasSum

/-- `Im Li_2(i) = G`. -/
theorem polylog_two_I_im : (polylog 2 I).im = catalanConst :=
  hasSum_im_polylog_two_I.unique hasSum_catalanConst

/-- `Li_2(-i) = conj Li_2(i)`. -/
theorem polylog_two_neg_I : polylog 2 (-I) = (starRingEnd ℂ) (polylog 2 I) := by
  rw [← polylog_conj, Complex.conj_I]

/-- `Re Li_2(i) = -π²/48`. -/
theorem polylog_two_I_re : (polylog 2 I).re = -(Real.pi ^ 2 / 48) := by
  have h := polylog_dup (s := 2) le_rfl (z := I) (by simp)
  have e2 : polylog 2 (I ^ 2) = ((polylogReal 2 (-1) : ℝ) : ℂ) := by
    rw [I_sq, ← polylog_ofReal]
    simp
  have h4 : (2 : ℂ) ^ 2 = ((4 : ℝ) : ℂ) := by norm_num
  rw [polylog_two_neg_I, e2, polylogReal_two_neg_one, h4] at h
  have h5 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [h5] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.add_re, Complex.conj_re,
    Complex.ofReal_re] at h2
  linarith

/-! ## The point `(1 + i)/2` -/

theorem norm_half_add_half_I_sq : ‖(1 + I) / 2‖ ^ 2 = 1 / 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  norm_num

theorem norm_half_add_half_I_lt : ‖(1 + I) / 2‖ < 1 := by
  by_contra hge
  have h1 : (1 : ℝ) ≤ ‖(1 + I) / 2‖ ^ 2 := one_le_pow₀ (not_lt.1 hge)
  rw [norm_half_add_half_I_sq] at h1
  norm_num at h1

theorem log_norm_half_add_half_I : Real.log ‖(1 + I) / 2‖ = -Real.log 2 / 2 := by
  have h2 : Real.log (‖(1 + I) / 2‖ ^ 2) = 2 * Real.log ‖(1 + I) / 2‖ := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [norm_half_add_half_I_sq, one_div, Real.log_inv] at h2
  linarith

theorem arg_half_add_half_I : ((1 + I) / 2 : ℂ).arg = Real.pi / 4 := by
  have hre : ((1 + I) / 2 : ℂ).re = 1 / 2 := by simp
  have him : ((1 + I) / 2 : ℂ).im = 1 / 2 := by simp
  rw [arg_eq_arctan_of_re_pos (by rw [hre]; norm_num), hre, him, div_self (by norm_num),
    Real.arctan_one]

/-- **`Re Li_2((1+i)/2) = 5π²/96 - (log 2)²/8`.** -/
theorem polylog_two_half_add_half_I_re :
    (polylog 2 ((1 + I) / 2)).re = 5 * Real.pi ^ 2 / 96 - Real.log 2 ^ 2 / 8 := by
  rw [re_polylog_two_of_re_eq_half norm_half_add_half_I_lt (by simp),
    log_norm_half_add_half_I, arg_half_add_half_I]
  ring

/-- **`Im Li_2((1+i)/2) = G - π log 2 / 8`.** -/
theorem polylog_two_half_add_half_I_im :
    (polylog 2 ((1 + I) / 2)).im = catalanConst - Real.pi * Real.log 2 / 8 := by
  have hne : ((1 + I) / 2 - 1 : ℂ) ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    simp at h2
    norm_num at h2
  have hdiv : ((1 + I) / 2 : ℂ) / ((1 + I) / 2 - 1) = -I := by
    rw [div_eq_iff hne]
    linear_combination (1 / 2 : ℂ) * Complex.I_sq
  have h := im_polylog_two_of_re_eq_half norm_half_add_half_I_lt.le (by simp)
  rw [hdiv, polylog_two_neg_I, Complex.conj_im, polylog_two_I_im, log_norm_half_add_half_I,
    arg_half_add_half_I] at h
  rw [h]
  ring

end Polylog

end PiFormula
