import Pilean.Polylog.Catalan
import Pilean.Polylog.PointBase3

/-!
# The Clausen function `Cl_2`

`Cl_2(θ) = Im Li_2(e^(iθ)) = ∑_{k ≥ 1} sin(kθ) / k²` (`clausen`). Mathlib has no Clausen
function.

* `hasSum_clausen`: the series;
* `clausen_pi_div_two : Cl_2(π/2) = G` (Catalan's constant);
* `clausen_two_mul : Cl_2(2θ) = 2 Cl_2(θ) - 2 Cl_2(π - θ)` (duplication of `Li_2` on the unit
  circle);
* `clausen_two_pi_div_three : Cl_2(2π/3) = (2/3) Cl_2(π/3)`;
* `polylog_two_pointThree_im : Im Li_2(e^(iπ/6)/√3) = (2/3) Cl_2(π/3) - π log 3 / 12`
  (Landen's identity: the image of `e^(iπ/6)/√3` is `e^(-2πi/3)`).

These are the first steps towards the formulas of the Compendium with imaginary parts
(`literature/bailey-compendium/DEGREE2_PLAN.md`, work package F).
-/

namespace PiFormula

namespace Polylog

open Complex

/-- **The Clausen function** `Cl_2(θ) = Im Li_2(e^(iθ)) = ∑_{k ≥ 1} sin(kθ)/k²`. -/
noncomputable def clausen (θ : ℝ) : ℝ := (polylog 2 (Complex.exp ((θ : ℂ) * I))).im

theorem exp_mul_I_pow (θ : ℝ) (m : ℕ) :
    Complex.exp ((θ : ℂ) * I) ^ m = Complex.exp ((((m : ℝ) * θ : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `Cl_2(θ) = ∑_{k ≥ 1} sin(kθ)/k²` (the term at `k = 0` is `0`). -/
theorem hasSum_clausen (θ : ℝ) :
    HasSum (fun m : ℕ => Real.sin ((m : ℝ) * θ) / (m : ℝ) ^ 2) (clausen θ) := by
  have h := hasSum_im_polylog_nat (s := 2) le_rfl (z := Complex.exp ((θ : ℂ) * I))
    (Complex.norm_exp_ofReal_mul_I θ).le
  refine h.congr_fun fun m => ?_
  rw [exp_mul_I_pow, Complex.exp_ofReal_mul_I_im]

/-- A complex number with real part `cos θ` and imaginary part `sin θ` is `e^(iθ)`. -/
theorem exp_mul_I_eq {θ : ℝ} {z : ℂ} (hre : z.re = Real.cos θ) (him : z.im = Real.sin θ) :
    Complex.exp ((θ : ℂ) * I) = z := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, hre]
  · rw [Complex.exp_ofReal_mul_I_im, him]

/-- `Cl_2(π/2) = G`. -/
theorem clausen_pi_div_two : clausen (Real.pi / 2) = catalanConst := by
  rw [clausen, exp_mul_I_eq (z := I) (by rw [Complex.I_re, Real.cos_pi_div_two])
    (by rw [Complex.I_im, Real.sin_pi_div_two]), polylog_two_I_im]

/-- **Duplication**: `Cl_2(2θ) = 2 Cl_2(θ) - 2 Cl_2(π - θ)`. -/
theorem clausen_two_mul (θ : ℝ) :
    clausen (2 * θ) = 2 * clausen θ - 2 * clausen (Real.pi - θ) := by
  have h := polylog_dup (s := 2) le_rfl (z := Complex.exp ((θ : ℂ) * I))
    (Complex.norm_exp_ofReal_mul_I θ).le
  have e1 : Complex.exp ((θ : ℂ) * I) ^ 2 = Complex.exp (((2 * θ : ℝ) : ℂ) * I) := by
    rw [exp_mul_I_pow]
    norm_num
  have e2 : -Complex.exp ((θ : ℂ) * I) =
      (starRingEnd ℂ) (Complex.exp (((Real.pi - θ : ℝ) : ℂ) * I)) := by
    apply Complex.ext
    · rw [Complex.neg_re, Complex.conj_re, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_re, Real.cos_pi_sub]
    · rw [Complex.neg_im, Complex.conj_im, Complex.exp_ofReal_mul_I_im,
        Complex.exp_ofReal_mul_I_im, Real.sin_pi_sub]
  have h4 : (2 : ℂ) ^ 2 = ((4 : ℝ) : ℂ) := by norm_num
  have h5 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [e1, e2, polylog_conj, h4] at h
  rw [h5] at h
  have h2 := congrArg Complex.im h
  rw [Complex.im_ofReal_mul, Complex.im_ofReal_mul, Complex.add_im, Complex.conj_im] at h2
  simp only [clausen]
  linarith

/-- `Cl_2(2π/3) = (2/3) Cl_2(π/3)`. -/
theorem clausen_two_pi_div_three :
    clausen (2 * Real.pi / 3) = 2 / 3 * clausen (Real.pi / 3) := by
  have h := clausen_two_mul (Real.pi / 3)
  have e1 : 2 * (Real.pi / 3) = 2 * Real.pi / 3 := by ring
  have e2 : Real.pi - Real.pi / 3 = 2 * Real.pi / 3 := by ring
  rw [e1, e2] at h
  linarith

/-- **`Im Li_2(e^(iπ/6)/√3) = (2/3) Cl_2(π/3) - π log 3 / 12`.** -/
theorem polylog_two_pointThree_im :
    (polylog 2 pointThree).im =
      2 / 3 * clausen (Real.pi / 3) - Real.pi * Real.log 3 / 12 := by
  have hne : pointThree - 1 ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    rw [Complex.sub_re, pointThree_re, Complex.one_re, Complex.zero_re] at h2
    norm_num at h2
  have hdiv : pointThree / (pointThree - 1) = 1 - 3 * pointThree := by
    rw [div_eq_iff hne]
    linear_combination (3 : ℂ) * pointThree_sq
  have hc : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  have hs : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
      Real.sin_pi_div_three]
  have hexp : (1 - 3 * pointThree : ℂ) =
      (starRingEnd ℂ) (Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) := by
    have e1 : (1 - 3 * pointThree : ℂ).re = 1 - 3 * pointThree.re := by simp
    have e2 : (1 - 3 * pointThree : ℂ).im = -(3 * pointThree.im) := by simp
    apply Complex.ext
    · rw [Complex.conj_re, Complex.exp_ofReal_mul_I_re, hc, e1, pointThree_re]
      norm_num
    · rw [Complex.conj_im, Complex.exp_ofReal_mul_I_im, hs, e2, pointThree_im]
      ring
  have hcl : (polylog 2 (Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).im =
      clausen (2 * Real.pi / 3) := rfl
  have h := im_polylog_two_of_re_eq_half norm_pointThree_lt.le pointThree_re
  rw [hdiv, hexp, polylog_conj, Complex.conj_im, hcl, clausen_two_pi_div_three,
    log_norm_pointThree, arg_pointThree] at h
  rw [h]
  ring

end Polylog

end PiFormula
