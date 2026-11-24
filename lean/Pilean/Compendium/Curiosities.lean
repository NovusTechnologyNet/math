module

public import Pilean.Compendium.GeneralCore

/-!
# Bailey's Compendium: the two "curiosities" of section 13, and formula (88)

* `formula_133` (page 35): `(1/√19) arccos (9/10) = (1/10) ∑_{k ≥ 0} D_k / (10^k (k + 1))`,
  where `D_0 = D_1 = 1` and `D_(k+1) = D_k - 5 D_(k-1)`. The paper prints the recurrence "for
  `k ≥ 2`", which leaves `D_2` free; the formula holds with the recurrence for `k ≥ 1`
  (`D_2 = -4`), and this is the hypothesis here. The theorem is stated for every real sequence
  `D` with these properties. With `α = (1 + i√19)/2`, a root of `z² = z - 5`, one has
  `D_k = Im(α^(k+1)) / Im(α)` (`im_cLucas_pow`), so the series is the imaginary part of the
  series of `-log (1 - α/10)`, and its value `(2/√19) arctan (1/√19)` is
  `(1/√19) arccos (9/10)`.
* `formula_132` (page 35): `3π√φ / 5^(5/4) = (1/2⁹) P(1, (2/φ)^10, 10, A)` with the irrational
  base `(2/φ)^10` and the vector `A = (256φ, 128φ³, 64φ⁴, 32φ⁴, 0, -8φ⁶, -4φ⁸, -2φ⁹, -φ⁹, 0)`,
  stated with `BaileyFormulaReal` (`GeneralDefs.lean`); `φ` is `Real.goldenRatio` and
  `5^(5/4)` a real power. The series is `(512 / sin (π/5)) ∑_{k ≥ 1} x^k sin (kπ/5) / k` at
  `x = φ/2 = cos (π/5)` (`hasSum_sin_pow_div`, `sin_pi_div_five_table`), of value
  `(512 / sin (π/5)) arctan (cot (π/5)) = (512 / sin (π/5)) (3π/10)`, and
  `2 sin (π/5) √φ = 5^(1/4)`.
* `formula_88` (page 26, section 10 "Other specific bases"; it is here because it uses the same
  series): `(1/√φ) arctan ((5^(1/4)/√φ) (233 - 329√5)/5938) +
  √φ arctan ((5^(1/4)/√φ) (939 + 281√5)/5938) = (1/(2·5^(13/4))) P(1, 5^5, 5, (125, -25, 5,
  -1, 0))`, in the form `BaileyFormula` of the other formulas. The series is
  `625 ∑_{k ≥ 1} h(k) 5^(-k) / k` with `h = (1, -1, 1, -1, 0)` of period 5, and
  `h(k) = (φ - 1) w sin (2kπ/5) + (φ + 1) w sin (4kπ/5)` with `w = 1/(sin (π/5) (φ + 2))`
  (`pattern_88`). So the value is a combination of `θ₁ = arctan (sin (2π/5)/(5 - cos (2π/5)))`
  and `θ₂ = arctan (sin (4π/5)/(5 - cos (4π/5)))`, and the two arctangents of the print are
  `θ₂ - θ₁` and `θ₁ + θ₂` (`arctan_add_88`).
-/

@[expose] public section

namespace PiFormula

namespace Compendium

open BaseB

/-! ## 1. Formula (133) -/

theorem sqrt19_mul_self : Real.sqrt 19 * Real.sqrt 19 = 19 := Real.mul_self_sqrt (by norm_num)

/-- The complex number `α = (1 + i√19)/2`, a root of `z² = z - 5`. -/
noncomputable def cLucas : ℂ := ⟨1 / 2, Real.sqrt 19 / 2⟩

theorem cLucas_re : cLucas.re = 1 / 2 := rfl

theorem cLucas_im : cLucas.im = Real.sqrt 19 / 2 := rfl

theorem normSq_cLucas : Complex.normSq cLucas = 5 := by
  rw [Complex.normSq_apply, cLucas_re, cLucas_im]
  linear_combination (1 / 4 : ℝ) * sqrt19_mul_self

theorem cLucas_sq : cLucas ^ 2 = cLucas - 5 := by
  rw [pow_two]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.re_ofNat, cLucas]
    linear_combination (-1 / 4 : ℝ) * sqrt19_mul_self
  · simp only [Complex.mul_im, Complex.sub_im, Complex.im_ofNat, cLucas]
    ring

/-- For a sequence with `D_0 = D_1 = 1` and `D_(k+1) = D_k - 5 D_(k-1)` (`k ≥ 1`):
`Im(α^(k+1)) = (√19/2) D_k`. -/
theorem im_cLucas_pow (D : ℕ → ℝ) (h0 : D 0 = 1) (h1 : D 1 = 1)
    (hD : ∀ k, 1 ≤ k → D (k + 1) = D k - 5 * D (k - 1)) (k : ℕ) :
    (cLucas ^ (k + 1)).im = Real.sqrt 19 / 2 * D k := by
  have key : ∀ k : ℕ, (cLucas ^ (k + 1)).im = Real.sqrt 19 / 2 * D k ∧
      (cLucas ^ (k + 2)).im = Real.sqrt 19 / 2 * D (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [zero_add, pow_one, cLucas_im, h0, mul_one]
      · rw [zero_add, cLucas_sq, Complex.sub_im, Complex.im_ofNat, cLucas_im, h1]
        ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have e : cLucas ^ (k + 1 + 2) = cLucas ^ (k + 2) - 5 * cLucas ^ (k + 1) := by
        rw [pow_add, cLucas_sq]
        ring
      have hk := hD (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
      rw [Nat.add_sub_cancel] at hk
      rw [e, Complex.sub_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, ih.1, ih.2, hk]
      ring
  exact (key k).1

/-- `arccos (9/10) = 2 arctan (√19/19)`. -/
theorem arccos_nine_tenths : Real.arccos (9 / 10) = 2 * Real.arctan (Real.sqrt 19 / 19) := by
  have hs0 : 0 ≤ Real.sqrt 19 := Real.sqrt_nonneg 19
  have hs : Real.sqrt 19 < 19 := by nlinarith [sqrt19_mul_self]
  have hsq : Real.sqrt (1 - (9 / 10 : ℝ) ^ 2) = Real.sqrt 19 / 10 := by
    rw [show (1 - (9 / 10 : ℝ) ^ 2) = 19 / 10 ^ 2 by norm_num, Real.sqrt_div (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [Real.arccos_eq_arctan (by norm_num), Real.two_mul_arctan (by linarith) (by linarith), hsq]
  congr 1
  rw [div_eq_div_iff (by norm_num) (by nlinarith [sqrt19_mul_self])]
  linear_combination (-(Real.sqrt 19) / 3610) * sqrt19_mul_self

/-- **Formula (133)** of the Compendium (page 35):
`(1/√19) arccos (9/10) = (1/10) ∑_{k ≥ 0} (D_k / 10^k) (1/(k + 1))` for every sequence with
`D_0 = D_1 = 1` and `D_(k+1) = D_k - 5 D_(k-1)` for `k ≥ 1`. The paper prints the recurrence for
`k ≥ 2`, which does not determine `D_2`; the range is corrected here to `k ≥ 1`, as in the
ledger. -/
theorem formula_133 (D : ℕ → ℝ) (h0 : D 0 = 1) (h1 : D 1 = 1)
    (hD : ∀ k, 1 ≤ k → D (k + 1) = D k - 5 * D (k - 1)) :
    ∃ S : ℝ, HasSum (fun k : ℕ => D k / 10 ^ k * (1 / ((k : ℝ) + 1))) S ∧
      1 / Real.sqrt 19 * Real.arccos (9 / 10) = 1 / 10 * S := by
  have hs : Real.sqrt 19 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hz : (1 / 10 : ℝ) ^ 2 * Complex.normSq cLucas < 1 := by
    rw [normSq_cLucas]
    norm_num
  have h := hasSum_pow_im_div (norm_smul_lt_one hz)
  rw [Complex.im_ofReal_mul, Complex.re_ofReal_mul, cLucas_im, cLucas_re] at h
  have e : (1 / 10 : ℝ) * (Real.sqrt 19 / 2) / (1 - 1 / 10 * (1 / 2)) = Real.sqrt 19 / 19 := by
    rw [div_eq_div_iff (by norm_num) (by norm_num)]
    ring
  rw [e] at h
  have h2 := ((hasSum_nat_add_iff' 1).2 h).mul_left (20 / Real.sqrt 19)
  refine ⟨20 / Real.sqrt 19 * Real.arctan (Real.sqrt 19 / 19), ?_, ?_⟩
  · convert h2 using 1
    · funext k
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      rw [smul_pow_im, im_cLucas_pow D h0 h1 hD k, one_div_pow]
      push_cast
      field_simp
      ring
    · simp
  · rw [arccos_nine_tenths]
    field_simp
    norm_num

/-! ## 2. Formula (132) -/

/-- `∑_{k ≥ 1} x^k sin (kθ) / k = arctan (x sin θ / (1 - x cos θ))` for `|x| < 1`: the
imaginary part of the series of `-log (1 - x e^(iθ))`. -/
theorem hasSum_sin_pow_div {x : ℝ} (hx : |x| < 1) (θ : ℝ) :
    HasSum (fun k : ℕ => x ^ k * Real.sin (k * θ) / k)
      (Real.arctan (x * Real.sin θ / (1 - x * Real.cos θ))) := by
  have hnz : ‖(x : ℂ) * Complex.exp (θ * Complex.I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
    exact hx
  have h := hasSum_pow_im_div hnz
  rw [Complex.im_ofReal_mul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_re] at h
  refine h.congr_fun fun k => ?_
  have e1 : ((x : ℂ) * Complex.exp (θ * Complex.I)) ^ k =
      ((x ^ k : ℝ) : ℂ) * Complex.exp (((k * θ : ℝ) : ℂ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul, ← mul_assoc]
    push_cast
    ring
  rw [e1, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- `sin (2π/5) = φ sin (π/5)`. -/
theorem sin_two_pi_div_five :
    Real.sin (2 * (Real.pi / 5)) = Real.sin (Real.pi / 5) * Real.goldenRatio := by
  rw [Real.sin_two_mul, Real.cos_pi_div_five, Real.goldenRatio]
  ring

/-- The values of `sin (kπ/5)` for `k = 3, …, 10` and `k = 12, 16, 20`. -/
theorem sin_mul_pi_div_five :
    Real.sin (3 * (Real.pi / 5)) = Real.sin (Real.pi / 5) * Real.goldenRatio ∧
    Real.sin (4 * (Real.pi / 5)) = Real.sin (Real.pi / 5) ∧
    Real.sin (5 * (Real.pi / 5)) = 0 ∧
    Real.sin (6 * (Real.pi / 5)) = -Real.sin (Real.pi / 5) ∧
    Real.sin (7 * (Real.pi / 5)) = -(Real.sin (Real.pi / 5) * Real.goldenRatio) ∧
    Real.sin (8 * (Real.pi / 5)) = -(Real.sin (Real.pi / 5) * Real.goldenRatio) ∧
    Real.sin (9 * (Real.pi / 5)) = -Real.sin (Real.pi / 5) ∧
    Real.sin (10 * (Real.pi / 5)) = 0 ∧
    Real.sin (12 * (Real.pi / 5)) = Real.sin (Real.pi / 5) * Real.goldenRatio ∧
    Real.sin (16 * (Real.pi / 5)) = -Real.sin (Real.pi / 5) ∧
    Real.sin (20 * (Real.pi / 5)) = 0 := by
  have s2 := sin_two_pi_div_five
  have s6 : Real.sin (6 * (Real.pi / 5)) = -Real.sin (Real.pi / 5) := by
    rw [show 6 * (Real.pi / 5) = Real.pi / 5 + Real.pi by ring, Real.sin_add_pi]
  refine ⟨?_, ?_, ?_, s6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 3 * (Real.pi / 5) = Real.pi - 2 * (Real.pi / 5) by ring, Real.sin_pi_sub, s2]
  · rw [show 4 * (Real.pi / 5) = Real.pi - Real.pi / 5 by ring, Real.sin_pi_sub]
  · rw [show 5 * (Real.pi / 5) = Real.pi by ring, Real.sin_pi]
  · rw [show 7 * (Real.pi / 5) = 2 * (Real.pi / 5) + Real.pi by ring, Real.sin_add_pi, s2]
  · rw [show 8 * (Real.pi / 5) = 2 * Real.pi - 2 * (Real.pi / 5) by ring,
      Real.sin_two_pi_sub, s2]
  · rw [show 9 * (Real.pi / 5) = 2 * Real.pi - Real.pi / 5 by ring, Real.sin_two_pi_sub]
  · rw [show 10 * (Real.pi / 5) = 2 * Real.pi by ring, Real.sin_two_pi]
  · rw [show 12 * (Real.pi / 5) = 2 * (Real.pi / 5) + 2 * Real.pi by ring,
      Real.sin_add_two_pi, s2]
  · rw [show 16 * (Real.pi / 5) = 6 * (Real.pi / 5) + 2 * Real.pi by ring,
      Real.sin_add_two_pi, s6]
  · rw [show 20 * (Real.pi / 5) = 2 * Real.pi + 2 * Real.pi by ring, Real.sin_add_two_pi,
      Real.sin_two_pi]

/-- The values of `sin (kπ/5)` for `k = 1, …, 10`: `sin (π/5)` times
`(1, φ, φ, 1, 0, -1, -φ, -φ, -1, 0)`. -/
theorem sin_pi_div_five_table :
    (fun i : Fin 10 => Real.sin ((((i : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 5))) =
      fun i : Fin 10 => Real.sin (Real.pi / 5) *
        ![1, Real.goldenRatio, Real.goldenRatio, 1, 0, -1, -Real.goldenRatio,
          -Real.goldenRatio, -1, 0] i := by
  have s2 := sin_two_pi_div_five
  obtain ⟨s3, s4, s5, s6, s7, s8, s9, s10, -, -, -⟩ := sin_mul_pi_div_five
  funext i
  fin_cases i <;> simp [s2, s3, s4, s5, s6, s7, s8, s9, s10]

/-- `5^(5/4) = 5 √(√5)`. -/
theorem five_rpow_five_fourths : (5 : ℝ) ^ ((5 : ℝ) / 4) = 5 * Real.sqrt (Real.sqrt 5) := by
  have e1 : (5 : ℝ) ^ ((5 : ℝ) / 4) = (5 : ℝ) ^ (1 : ℝ) * (5 : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have e2 : Real.sqrt (Real.sqrt 5) = (5 : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [e1, e2, Real.rpow_one]

/-- `2 sin (π/5) √φ = √(√5)`. -/
theorem two_sin_pi_div_five_mul_sqrt :
    2 * Real.sin (Real.pi / 5) * Real.sqrt Real.goldenRatio = Real.sqrt (Real.sqrt 5) := by
  have hs : 0 < Real.sin (Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsq : (2 * Real.sin (Real.pi / 5) * Real.sqrt Real.goldenRatio) ^ 2 = Real.sqrt 5 := by
    have e1 : Real.sin (Real.pi / 5) ^ 2 = 1 - ((1 + Real.sqrt 5) / 4) ^ 2 := by
      rw [← Real.cos_pi_div_five]
      linear_combination Real.sin_sq_add_cos_sq (Real.pi / 5)
    rw [mul_pow, mul_pow, Real.sq_sqrt Real.goldenRatio_pos.le, e1, Real.goldenRatio]
    linear_combination (-(Real.sqrt 5 + 3) / 8) * h5
  rw [← hsq, Real.sqrt_sq (by positivity)]

/-- `arctan (cos (π/5) sin (π/5) / (1 - cos² (π/5))) = 3π/10`. -/
theorem arctan_pi_div_five :
    Real.arctan (Real.goldenRatio / 2 * Real.sin (Real.pi / 5) /
      (1 - Real.goldenRatio / 2 * Real.cos (Real.pi / 5))) = 3 * Real.pi / 10 := by
  have hs : 0 < Real.sin (Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hc : Real.goldenRatio / 2 = Real.cos (Real.pi / 5) := by
    rw [Real.cos_pi_div_five, Real.goldenRatio]
    ring
  have e : Real.goldenRatio / 2 * Real.sin (Real.pi / 5) /
      (1 - Real.goldenRatio / 2 * Real.cos (Real.pi / 5)) =
        Real.tan (Real.pi / 2 - Real.pi / 5) := by
    rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, inv_div, hc,
      div_eq_div_iff (by nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 5)]) hs.ne']
    linear_combination (Real.cos (Real.pi / 5)) * Real.sin_sq_add_cos_sq (Real.pi / 5)
  rw [e, Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

/-- **Formula (132)** of the Compendium (page 35), with the irrational base `(2/φ)^10`:
`3π√φ / 5^(5/4) = (1/2⁹) P(1, (2/φ)^10, 10, (256φ, 128φ³, 64φ⁴, 32φ⁴, 0, -8φ⁶, -4φ⁸, -2φ⁹,
-φ⁹, 0))`, in the real-parameter form `BaileyFormulaReal`. The series is
`(512 / sin (π/5)) ∑_{k ≥ 1} (φ/2)^k sin (kπ/5) / k`, and `φ/2 = cos (π/5)`. -/
theorem formula_132 :
    BaileyFormulaReal (3 * Real.pi * Real.sqrt Real.goldenRatio / (5 : ℝ) ^ ((5 : ℝ) / 4))
      (1 / 2 ^ 9) ((2 / Real.goldenRatio) ^ 10) 10
      ![256 * Real.goldenRatio, 128 * Real.goldenRatio ^ 3, 64 * Real.goldenRatio ^ 4,
        32 * Real.goldenRatio ^ 4, 0, -8 * Real.goldenRatio ^ 6, -4 * Real.goldenRatio ^ 8,
        -2 * Real.goldenRatio ^ 9, -Real.goldenRatio ^ 9, 0] := by
  have hφ0 : Real.goldenRatio ≠ 0 := Real.goldenRatio_pos.ne'
  have hs : 0 < Real.sin (Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hs0 := hs.ne'
  have hx : |Real.goldenRatio / 2| < 1 := by
    rw [abs_of_pos (by linarith [Real.goldenRatio_pos]), div_lt_one (by norm_num)]
    exact Real.goldenRatio_lt_two
  have hβ : (Real.goldenRatio / 2) ^ 10 * (2 / Real.goldenRatio) ^ 10 = 1 := by
    rw [← mul_pow]
    field_simp
  have hβ0 : (2 / Real.goldenRatio) ^ 10 ≠ 0 := by positivity
  have hu : ∀ n : ℕ, (Real.goldenRatio / 2) ^ (n + 10) *
      Real.sin (((n + 10 : ℕ) : ℝ) * (Real.pi / 5)) =
        (Real.goldenRatio / 2) ^ n * Real.sin ((n : ℝ) * (Real.pi / 5)) /
          (2 / Real.goldenRatio) ^ 10 := by
    intro n
    have e : ((n + 10 : ℕ) : ℝ) * (Real.pi / 5) = (n : ℝ) * (Real.pi / 5) + 2 * Real.pi := by
      push_cast
      ring
    rw [e, Real.sin_add_two_pi, pow_add, eq_div_iff hβ0]
    linear_combination ((Real.goldenRatio / 2) ^ n * Real.sin ((n : ℝ) * (Real.pi / 5))) * hβ
  have h := hasBaileyValueReal_of_quasiperiodic (N := 10)
    (u := fun n => (Real.goldenRatio / 2) ^ n * Real.sin ((n : ℝ) * (Real.pi / 5)))
    (by norm_num) hu (hasSum_sin_pow_div hx (Real.pi / 5))
  have e : (fun i : Fin 10 => (Real.goldenRatio / 2) ^ ((i : ℕ) + 1) *
      Real.sin ((((i : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 5))) =
      fun i : Fin 10 => (Real.goldenRatio / 2) ^ ((i : ℕ) + 1) * (Real.sin (Real.pi / 5) *
        ![1, Real.goldenRatio, Real.goldenRatio, 1, 0, -1, -Real.goldenRatio,
          -Real.goldenRatio, -1, 0] i) := by
    funext i
    exact congrArg (fun y => (Real.goldenRatio / 2) ^ ((i : ℕ) + 1) * y)
      (congrFun sin_pi_div_five_table i)
  rw [e, arctan_pi_div_five] at h
  refine ((h.smul (512 / Real.sin (Real.pi / 5))).of_eq rfl ?_ rfl).formula ?_
  · funext i
    fin_cases i <;> simp <;> field_simp <;> ring
  · have hq : (0 : ℝ) < Real.sqrt (Real.sqrt 5) :=
      Real.sqrt_pos.2 (Real.sqrt_pos.2 (by norm_num))
    rw [five_rpow_five_fourths, ← two_sin_pi_div_five_mul_sqrt]
    have hg : Real.sqrt Real.goldenRatio ≠ 0 := (Real.sqrt_pos.2 Real.goldenRatio_pos).ne'
    field_simp
    ring

/-! ## 3. Formula (88) -/

theorem sin_pi_div_five_pos : 0 < Real.sin (Real.pi / 5) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

/-- `sin² (π/5) = (5 - √5)/8`. -/
theorem sin_pi_div_five_sq : Real.sin (Real.pi / 5) ^ 2 = (5 - Real.sqrt 5) / 8 := by
  have h := Real.sin_sq_add_cos_sq (Real.pi / 5)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [Real.cos_pi_div_five] at h
  linear_combination h - (1 / 16 : ℝ) * h5

/-- `5^(1/4) = √(√5)`. -/
theorem five_rpow_one_fourth : (5 : ℝ) ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt 5) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `5^(13/4) = 125 √(√5)`. -/
theorem five_rpow_thirteen_fourths :
    (5 : ℝ) ^ ((13 : ℝ) / 4) = 125 * Real.sqrt (Real.sqrt 5) := by
  have e1 : (5 : ℝ) ^ ((13 : ℝ) / 4) = (5 : ℝ) ^ ((3 : ℕ) : ℝ) * (5 : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  rw [e1, Real.rpow_natCast, five_rpow_one_fourth]
  norm_num

/-- The two sums of arctangents of formula (88), as identities in `s = sin (π/5)`, `r = √5`
and `φ`: with `t₁ = s φ (21 + r)/109` and `t₂ = s (21 - r)/109`,
`arctan t₁ + arctan t₂ = arctan (2s (939 + 281 r)/5938)` and
`arctan t₂ - arctan t₁ = arctan (2s (233 - 329 r)/5938)`. The coefficients of the three
`linear_combination` were computed with a computer algebra system (division by the relations
`φ = (1 + r)/2`, `s² = (5 - r)/8`, `r² = 5`). -/
theorem arctan_add_88 {s r φ : ℝ} (hφ : φ = (1 + r) / 2) (hs2 : s ^ 2 = (5 - r) / 8)
    (hr2 : r ^ 2 = 5) (hr0 : 0 < r) (hr3 : r < 3) :
    Real.arctan (s * φ * (21 + r) / 109) + Real.arctan (s * (21 - r) / 109) =
        Real.arctan (2 * s * ((939 + 281 * r) / 5938)) ∧
      Real.arctan (s * (21 - r) / 109) - Real.arctan (s * φ * (21 + r) / 109) =
        Real.arctan (2 * s * ((233 - 329 * r) / 5938)) := by
  have hprod : s * φ * (21 + r) / 109 * (s * (21 - r) / 109) = r / 109 := by
    linear_combination (-s ^ 2 * (r - 21) * (r + 21) / 11881) * hφ +
      (-(r - 21) * (r + 1) * (r + 21) / 23762) * hs2 + ((r ^ 2 - 4 * r - 441) / 190096) * hr2
  constructor
  · have hlt : s * φ * (21 + r) / 109 * (s * (21 - r) / 109) < 1 := by
      rw [hprod]
      linarith
    have hden : 1 - s * φ * (21 + r) / 109 * (s * (21 - r) / 109) ≠ 0 := by
      rw [hprod]
      have : 0 < 1 - r / 109 := by linarith
      exact this.ne'
    rw [Real.arctan_add hlt]
    congr 1
    rw [div_eq_iff hden]
    linear_combination
      (-s * (r + 21) * (281 * r ^ 2 * s ^ 2 - 4962 * r * s ^ 2 - 19719 * s ^ 2 - 323621) /
        35274689) * hφ +
      (-s * (r - 21) * (r + 1) * (r + 21) * (281 * r + 939) / 70549378) * hs2 +
      (s * (281 * r ^ 3 - 185 * r ^ 2 - 127677 * r + 2664933) / 564395024) * hr2
  · have hprod' : s * (21 - r) / 109 * -(s * φ * (21 + r) / 109) = -(r / 109) := by
      rw [mul_neg, mul_comm, hprod]
    have hlt : s * (21 - r) / 109 * -(s * φ * (21 + r) / 109) < 1 := by
      rw [hprod']
      linarith
    have hden : 1 - s * (21 - r) / 109 * -(s * φ * (21 + r) / 109) ≠ 0 := by
      rw [hprod']
      have : 0 < 1 - -(r / 109) := by linarith
      exact this.ne'
    rw [sub_eq_add_neg, ← Real.arctan_neg, Real.arctan_add hlt]
    congr 1
    rw [div_eq_iff hden]
    linear_combination
      (-s * (r + 21) * (329 * r ^ 2 * s ^ 2 - 7142 * r * s ^ 2 + 4893 * s ^ 2 + 323621) /
        35274689) * hφ +
      (-s * (r - 21) * (r + 1) * (r + 21) * (329 * r - 233) / 70549378) * hs2 +
      (s * (329 * r ^ 3 - 1549 * r ^ 2 - 144157 * r - 1912439) / 564395024) * hr2

/-- The pattern of formula (88): with `w = 1/(sin (π/5) (φ + 2))`,
`(φ - 1) w sin (2kπ/5) + (φ + 1) w sin (4kπ/5) = 1, -1, 1, -1, 0` for `k = 1, …, 5`. -/
theorem pattern_88 {w : ℝ} (hw : Real.sin (Real.pi / 5) * (Real.goldenRatio + 2) * w = 1) :
    (fun i : Fin 5 =>
      (Real.goldenRatio - 1) * w *
          Real.sin (((2 * ((i : ℕ) + 1) : ℕ) : ℝ) * (Real.pi / 5)) +
        (Real.goldenRatio + 1) * w *
          Real.sin (((4 * ((i : ℕ) + 1) : ℕ) : ℝ) * (Real.pi / 5))) =
      ![1, -1, 1, -1, 0] := by
  have gsq := Real.goldenRatio_sq
  have s2 := sin_two_pi_div_five
  obtain ⟨-, s4, -, s6, -, s8, -, s10, s12, s16, s20⟩ := sin_mul_pi_div_five
  funext i
  fin_cases i <;> simp [s2, s4, s6, s8, s10, s12, s16, s20]
  · linear_combination (w * Real.sin (Real.pi / 5)) * gsq + hw
  · linear_combination (-(w * Real.sin (Real.pi / 5))) * gsq - hw
  · linear_combination (w * Real.sin (Real.pi / 5)) * gsq + hw
  · linear_combination (-(w * Real.sin (Real.pi / 5))) * gsq - hw

/-- The last step of formula (88), as an identity between real numbers. -/
theorem assemble_88 {g gi c w s φ T1 T2 : ℝ} (hg2 : g ^ 2 = φ) (hgi : g * gi = 1)
    (hc : 500 * c * s * g = 1) (hw2 : 5 * w = 4 * s) :
    gi * (T2 - T1) + g * (T1 + T2) =
      c * (625 * ((φ - 1) * w * T1 + (φ + 1) * w * T2)) := by
  linear_combination (gi * (T1 + T2)) * hg2 - (g * (T1 + T2)) * hgi
    - (gi * ((φ - 1) * T1 + (φ + 1) * T2)) * hc
    + (500 * c * s * ((φ - 1) * T1 + (φ + 1) * T2)) * hgi
    - (125 * c * ((φ - 1) * T1 + (φ + 1) * T2)) * hw2

/-- **Formula (88)** of the Compendium (page 26):
`(1/√φ) arctan ((5^(1/4)/√φ) (233 - 329√5)/5938) + √φ arctan ((5^(1/4)/√φ) (939 + 281√5)/5938)
= (1/(2·5^(13/4))) P(1, 5^5, 5, (125, -25, 5, -1, 0))`. -/
theorem formula_88 : BaileyFormula
    (1 / Real.sqrt Real.goldenRatio * Real.arctan ((5 : ℝ) ^ ((1 : ℝ) / 4) /
        Real.sqrt Real.goldenRatio * ((233 - 329 * Real.sqrt 5) / 5938)) +
      Real.sqrt Real.goldenRatio * Real.arctan ((5 : ℝ) ^ ((1 : ℝ) / 4) /
        Real.sqrt Real.goldenRatio * ((939 + 281 * Real.sqrt 5) / 5938)))
    (1 / (2 * (5 : ℝ) ^ ((13 : ℝ) / 4))) 5 5 5 ![125, -25, 5, -1, 0] := by
  have hs := sin_pi_div_five_pos
  have hs2 := sin_pi_div_five_sq
  have hr2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hr3 : Real.sqrt 5 < 3 := by nlinarith
  have hφ : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  have hφ0 := Real.goldenRatio_pos
  have hg0 : 0 < Real.sqrt Real.goldenRatio := Real.sqrt_pos.2 hφ0
  have hg2 : Real.sqrt Real.goldenRatio ^ 2 = Real.goldenRatio := Real.sq_sqrt hφ0.le
  -- the weights of the two series
  obtain ⟨w, hw⟩ : ∃ w : ℝ, Real.sin (Real.pi / 5) * (Real.goldenRatio + 2) * w = 1 := by
    have h2 : Real.goldenRatio + 2 ≠ 0 := by linarith
    exact ⟨1 / (Real.sin (Real.pi / 5) * (Real.goldenRatio + 2)), by field_simp⟩
  have h54 : 4 * Real.sin (Real.pi / 5) ^ 2 * (Real.goldenRatio + 2) = 5 := by
    linear_combination (4 * Real.sin (Real.pi / 5) ^ 2) * hφ +
      (2 * (Real.sqrt 5 + 5)) * hs2 + (-1 / 4 : ℝ) * hr2
  have hw2 : 5 * w = 4 * Real.sin (Real.pi / 5) := by
    linear_combination (-w) * h54 + (4 * Real.sin (Real.pi / 5)) * hw
  -- the series
  have hx : |(1 / 5 : ℝ)| < 1 := by
    rw [abs_of_pos (by norm_num)]
    norm_num
  have h1 := (hasSum_sin_pow_div hx (2 * (Real.pi / 5))).mul_left
    ((Real.goldenRatio - 1) * w)
  have h2 := (hasSum_sin_pow_div hx (4 * (Real.pi / 5))).mul_left
    ((Real.goldenRatio + 1) * w)
  have hsum : HasSum (fun n : ℕ => (1 / 5 : ℝ) ^ n *
      ((Real.goldenRatio - 1) * w * Real.sin (((2 * n : ℕ) : ℝ) * (Real.pi / 5)) +
        (Real.goldenRatio + 1) * w * Real.sin (((4 * n : ℕ) : ℝ) * (Real.pi / 5))) / (n : ℝ))
      ((Real.goldenRatio - 1) * w * Real.arctan (1 / 5 * Real.sin (2 * (Real.pi / 5)) /
          (1 - 1 / 5 * Real.cos (2 * (Real.pi / 5)))) +
        (Real.goldenRatio + 1) * w * Real.arctan (1 / 5 * Real.sin (4 * (Real.pi / 5)) /
          (1 - 1 / 5 * Real.cos (4 * (Real.pi / 5))))) := by
    refine (h1.add h2).congr_fun fun n => ?_
    have e1 : ((2 * n : ℕ) : ℝ) * (Real.pi / 5) = (n : ℝ) * (2 * (Real.pi / 5)) := by
      push_cast
      ring
    have e2 : ((4 * n : ℕ) : ℝ) * (Real.pi / 5) = (n : ℝ) * (4 * (Real.pi / 5)) := by
      push_cast
      ring
    rw [e1, e2]
    ring
  have hu : ∀ n : ℕ, (1 / 5 : ℝ) ^ (n + 5) *
      ((Real.goldenRatio - 1) * w * Real.sin (((2 * (n + 5) : ℕ) : ℝ) * (Real.pi / 5)) +
        (Real.goldenRatio + 1) * w * Real.sin (((4 * (n + 5) : ℕ) : ℝ) * (Real.pi / 5))) =
      (1 / 5 : ℝ) ^ n *
      ((Real.goldenRatio - 1) * w * Real.sin (((2 * n : ℕ) : ℝ) * (Real.pi / 5)) +
        (Real.goldenRatio + 1) * w * Real.sin (((4 * n : ℕ) : ℝ) * (Real.pi / 5))) /
          5 ^ 5 := by
    intro n
    have e1 : ((2 * (n + 5) : ℕ) : ℝ) * (Real.pi / 5) =
        ((2 * n : ℕ) : ℝ) * (Real.pi / 5) + 2 * Real.pi := by
      push_cast
      ring
    have e2 : ((4 * (n + 5) : ℕ) : ℝ) * (Real.pi / 5) =
        ((4 * n : ℕ) : ℝ) * (Real.pi / 5) + 2 * Real.pi + 2 * Real.pi := by
      push_cast
      ring
    rw [e1, e2, Real.sin_add_two_pi, Real.sin_add_two_pi, Real.sin_add_two_pi, pow_add]
    ring
  have hB := hasBaileyValueReal_of_quasiperiodic (N := 5) (β := 5 ^ 5)
    (u := fun n : ℕ => (1 / 5 : ℝ) ^ n *
      ((Real.goldenRatio - 1) * w * Real.sin (((2 * n : ℕ) : ℝ) * (Real.pi / 5)) +
        (Real.goldenRatio + 1) * w * Real.sin (((4 * n : ℕ) : ℝ) * (Real.pi / 5))))
    (by norm_num) hu hsum
  have e : (fun i : Fin 5 => (1 / 5 : ℝ) ^ ((i : ℕ) + 1) *
      ((Real.goldenRatio - 1) * w *
          Real.sin (((2 * ((i : ℕ) + 1) : ℕ) : ℝ) * (Real.pi / 5)) +
        (Real.goldenRatio + 1) * w *
          Real.sin (((4 * ((i : ℕ) + 1) : ℕ) : ℝ) * (Real.pi / 5)))) =
      fun i : Fin 5 => (1 / 5 : ℝ) ^ ((i : ℕ) + 1) * ![1, -1, 1, -1, 0] i := by
    funext i
    exact congrArg (fun y => (1 / 5 : ℝ) ^ ((i : ℕ) + 1) * y) (congrFun (pattern_88 hw) i)
  rw [e] at hB
  refine BaileyFormulaReal.to_nat ((hB.smul 625).formula ?_) (by norm_num) fun i => ?_
  · -- the value
    have hc1 : Real.cos (2 * (Real.pi / 5)) = (Real.sqrt 5 - 1) / 4 := by
      rw [Real.cos_two_mul, Real.cos_pi_div_five]
      linear_combination (1 / 8 : ℝ) * hr2
    have hc2 : Real.cos (4 * (Real.pi / 5)) = -(1 + Real.sqrt 5) / 4 := by
      rw [show 4 * (Real.pi / 5) = Real.pi - Real.pi / 5 by ring, Real.cos_pi_sub,
        Real.cos_pi_div_five]
      ring
    have hd1 : 1 - 1 / 5 * ((Real.sqrt 5 - 1) / 4) ≠ 0 := by
      have : 0 < 1 - 1 / 5 * ((Real.sqrt 5 - 1) / 4) := by linarith
      exact this.ne'
    have hd2 : 1 - 1 / 5 * (-(1 + Real.sqrt 5) / 4) ≠ 0 := by
      have : 0 < 1 - 1 / 5 * (-(1 + Real.sqrt 5) / 4) := by linarith
      exact this.ne'
    have e1 : 1 / 5 * Real.sin (2 * (Real.pi / 5)) / (1 - 1 / 5 * Real.cos (2 * (Real.pi / 5))) =
        Real.sin (Real.pi / 5) * Real.goldenRatio * (21 + Real.sqrt 5) / 109 := by
      rw [sin_two_pi_div_five, hc1, div_eq_div_iff hd1 (by norm_num)]
      linear_combination (Real.sin (Real.pi / 5) * Real.goldenRatio / 20) * hr2
    have e2 : 1 / 5 * Real.sin (4 * (Real.pi / 5)) / (1 - 1 / 5 * Real.cos (4 * (Real.pi / 5))) =
        Real.sin (Real.pi / 5) * (21 - Real.sqrt 5) / 109 := by
      rw [sin_mul_pi_div_five.2.1, hc2, div_eq_div_iff hd2 (by norm_num)]
      linear_combination (Real.sin (Real.pi / 5) / 20) * hr2
    obtain ⟨hY, hX⟩ := arctan_add_88 hφ hs2 hr2 hr0 hr3
    have hq : (5 : ℝ) ^ ((1 : ℝ) / 4) =
        2 * Real.sin (Real.pi / 5) * Real.sqrt Real.goldenRatio := by
      rw [five_rpow_one_fourth, two_sin_pi_div_five_mul_sqrt]
    have hqg : (5 : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt Real.goldenRatio =
        2 * Real.sin (Real.pi / 5) := by
      rw [hq, mul_div_assoc, div_self hg0.ne', mul_one]
    have hgi : Real.sqrt Real.goldenRatio * (1 / Real.sqrt Real.goldenRatio) = 1 :=
      mul_one_div_cancel hg0.ne'
    have hc : 500 * (1 / (2 * (5 : ℝ) ^ ((13 : ℝ) / 4))) * Real.sin (Real.pi / 5) *
        Real.sqrt Real.goldenRatio = 1 := by
      rw [five_rpow_thirteen_fourths, ← two_sin_pi_div_five_mul_sqrt]
      field_simp
      ring
    rw [e1, e2, hqg, ← hX, ← hY]
    exact assemble_88 hg2 hgi hc hw2
  · fin_cases i <;> simp <;> norm_num

end Compendium

end PiFormula
