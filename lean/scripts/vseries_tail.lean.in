
theorem psTW_eq (k : ℕ) : psTW k = ((PTWZ k : GaussianInt) : ℂ) := by
  rw [psTW_reduce, PTWZ]
  exact psTW_small (k % 24) (Nat.mod_lt _ (by norm_num))

/-- The twisted pattern. -/
def namedTW : ℕ → ℚ := rhoA PTWZ

/-! ### Explicit values -/

theorem sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  push_cast
  rfl

theorem z24_sq_trig : z24 ^ 2 =
    Complex.cos ((Real.pi / 6 : ℝ) : ℂ) + Complex.sin ((Real.pi / 6 : ℝ) : ℂ) * I := by
  rw [z24, ← pow_mul, ζ120, ← Complex.exp_nat_mul,
    show ((5 * 2 : ℕ) : ℂ) * (2 * Real.pi * I / 120) = ((Real.pi / 6 : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_mul_I]

theorem z24_sq : z24 ^ 2 = ((Real.sqrt 3 : ℝ) : ℂ) / 2 + I / 2 := by
  rw [z24_sq_trig, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_six,
    Real.sin_pi_div_six]
  push_cast
  ring

theorem z24_ne_zero : z24 ≠ 0 := z24_prim.ne_zero (by norm_num)

theorem z24_pow_10 : z24 ^ 10 = -((Real.sqrt 3 : ℝ) : ℂ) / 2 + I / 2 := by
  have h : z24 ^ 10 * z24 ^ 2 = -1 := by rw [← pow_add]; exact z24_pow_12
  have hc : (-((Real.sqrt 3 : ℝ) : ℂ) / 2 + I / 2) * z24 ^ 2 = -1 := by
    rw [z24_sq]; linear_combination (-1 / 4 : ℂ) * sqrt3_sq + (1 / 4 : ℂ) * Complex.I_sq
  exact mul_right_cancel₀ (pow_ne_zero 2 z24_ne_zero) (h.trans hc.symm)

/-- `ζ_24^2 - ζ_24^10 = √3`. -/
theorem dTW_eq : dTW = ((Real.sqrt 3 : ℝ) : ℂ) := by
  rw [dTW, z24_sq, z24_pow_10]
  ring

theorem z24_pow_4 : z24 ^ 4 = 1 / 2 + ((Real.sqrt 3 : ℝ) : ℂ) / 2 * I := by
  rw [show z24 ^ 4 = (z24 ^ 2) ^ 2 by ring, z24_sq]
  linear_combination (1 / 4 : ℂ) * sqrt3_sq + (1 / 4 : ℂ) * Complex.I_sq

theorem z24_pow_20 : z24 ^ 20 = 1 / 2 - ((Real.sqrt 3 : ℝ) : ℂ) / 2 * I := by
  rw [show z24 ^ 20 = (z24 ^ 10) ^ 2 by ring, z24_pow_10]
  linear_combination (1 / 4 : ℂ) * sqrt3_sq + (1 / 4 : ℂ) * Complex.I_sq

theorem z24_pow_13 : z24 ^ 13 = -z24 := by rw [pow_succ, z24_pow_12]; ring

theorem norm_z24_pow (n : ℕ) : ‖z24 ^ n‖ = 1 := by
  rw [norm_pow, z24_prim.norm'_eq_one (by norm_num), one_pow]

theorem conj_z24 : conj z24 = z24 ^ 23 := by
  have h1 : z24 * conj z24 = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, z24_prim.norm'_eq_one (by norm_num)]
    norm_num
  have h2 : z24 * z24 ^ 23 = 1 := by rw [← pow_succ']; exact z24_prim.pow_eq_one
  exact mul_left_cancel₀ z24_ne_zero (h1.trans h2.symm)

theorem gfun_z24_5 : gfun (z24 ^ 5) = -gfun z24 := by
  have e : I * conj z24 = z24 ^ 5 := by
    rw [conj_z24, I_z24, ← pow_add, z24_pow_mod]
  rw [← e]
  exact gfun_partner (by simpa using norm_z24_pow 1)

theorem gfun_z24_17 : gfun (z24 ^ 17) = -gfun (z24 ^ 13) := by
  have e : I * conj (z24 ^ 13) = z24 ^ 17 := by
    rw [map_pow, conj_z24, I_z24, ← pow_mul, ← pow_add, z24_pow_mod]
  rw [← e]
  exact gfun_partner (norm_z24_pow 13)

theorem inv_two_I : (2 * I)⁻¹ = -I / 2 := by
  refine inv_eq_of_mul_eq_one_right ?_
  linear_combination (-1 : ℂ) * Complex.I_sq

theorem arg_real_mul_trig {c θ : ℝ} (hc : 0 < c) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    arg ((c : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * I)) = θ := by
  rw [Complex.arg_real_mul _ hc, Complex.arg_cos_add_sin_mul_I hθ]

theorem pi_div_six_mem : Real.pi / 6 ∈ Set.Ioc (-Real.pi) Real.pi := by
  have := Real.pi_pos
  constructor <;> linarith

theorem neg_pi_div_six_mem : -(Real.pi / 6) ∈ Set.Ioc (-Real.pi) Real.pi := by
  have := Real.pi_pos
  constructor <;> linarith

theorem sqrt3_gt_one : 1 < Real.sqrt 3 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem trig_pi_div_six :
    Complex.cos ((Real.pi / 6 : ℝ) : ℂ) + Complex.sin ((Real.pi / 6 : ℝ) : ℂ) * I =
      ((Real.sqrt 3 : ℝ) : ℂ) / 2 + I / 2 := by
  rw [← z24_sq_trig, z24_sq]

theorem trig_neg_pi_div_six :
    Complex.cos ((-(Real.pi / 6) : ℝ) : ℂ) + Complex.sin ((-(Real.pi / 6) : ℝ) : ℂ) * I =
      ((Real.sqrt 3 : ℝ) : ℂ) / 2 - I / 2 := by
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast
  ring

/-- `g(ζ) + g(ζ^13) = π/6`: `w(ζ) w(-ζ) = 1 - ζ²/t² = (√3/2) ζ²`. -/
theorem gfun_z24_add_13 : gfun z24 + gfun (z24 ^ 13) = Real.pi / 6 := by
  have h1 := abs_gfun_le (by simpa using norm_z24_pow 1 : ‖z24‖ = 1)
  have h13 := abs_gfun_le (norm_z24_pow 13)
  rw [gfun_eq_arg, gfun_eq_arg] at h1 h13 ⊢
  have hw1 : 1 - z24 / tC ≠ 0 := by
    rw [show 1 - z24 / tC = (tC - z24) / tC by rw [sub_div, div_self tC_ne_zero]]
    exact div_ne_zero (tC_sub_ne_zero (by simpa using norm_z24_pow 1)) tC_ne_zero
  have hw13 : 1 - z24 ^ 13 / tC ≠ 0 := by
    rw [show 1 - z24 ^ 13 / tC = (tC - z24 ^ 13) / tC by rw [sub_div, div_self tC_ne_zero]]
    exact div_ne_zero (tC_sub_ne_zero (norm_z24_pow 13)) tC_ne_zero
  have hmem : arg (1 - z24 / tC) + arg (1 - z24 ^ 13 / tC) ∈ Set.Ioc (-Real.pi) Real.pi := by
    have := Real.pi_pos
    rw [abs_le] at h1 h13
    constructor <;> linarith [h1.1, h1.2, h13.1, h13.2]
  rw [← Complex.arg_mul hw1 hw13 hmem]
  have e : (1 - z24 / tC) * (1 - z24 ^ 13 / tC) =
      ((Real.sqrt 3 / 2 : ℝ) : ℂ) * (Complex.cos ((Real.pi / 6 : ℝ) : ℂ) +
        Complex.sin ((Real.pi / 6 : ℝ) : ℂ) * I) := by
    rw [trig_pi_div_six, z24_pow_13]
    have : (1 - z24 / tC) * (1 - -z24 / tC) = 1 - z24 ^ 2 * (tC ^ 2)⁻¹ := by
      field_simp [tC_ne_zero]
      ring
    rw [this, tC_sq, inv_two_I, z24_sq]
    push_cast
    linear_combination (1 / 4 : ℂ) * Complex.I_sq - (1 / 4 : ℂ) * sqrt3_sq
  rw [e, arg_real_mul_trig (by positivity) pi_div_six_mem]

/-- `g(ζ^4) = -π/6`: `w(ζ_6) = ((√3 - 1)/2) e^(-iπ/6)`. -/
theorem gfun_z24_4 : gfun (z24 ^ 4) = -(Real.pi / 6) := by
  rw [gfun_eq_arg]
  have e : 1 - z24 ^ 4 / tC = (((Real.sqrt 3 - 1) / 2 : ℝ) : ℂ) *
      (Complex.cos ((-(Real.pi / 6) : ℝ) : ℂ) + Complex.sin ((-(Real.pi / 6) : ℝ) : ℂ) * I) := by
    rw [trig_neg_pi_div_six, div_eq_mul_inv, tC_inv, z24_pow_4]
    push_cast
    linear_combination (1 / 4 : ℂ) * sqrt3_sq + ((1 : ℂ) / 4 - ((Real.sqrt 3 : ℝ) : ℂ) / 4) *
      Complex.I_sq
  rw [e, arg_real_mul_trig (by linarith [sqrt3_gt_one]) neg_pi_div_six_mem]

/-- `g(ζ^20) = π/6`: `w(ζ_6^5) = ((1 + √3)/2) e^(iπ/6)`. -/
theorem gfun_z24_20 : gfun (z24 ^ 20) = Real.pi / 6 := by
  rw [gfun_eq_arg]
  have e : 1 - z24 ^ 20 / tC = (((1 + Real.sqrt 3) / 2 : ℝ) : ℂ) *
      (Complex.cos ((Real.pi / 6 : ℝ) : ℂ) + Complex.sin ((Real.pi / 6 : ℝ) : ℂ) * I) := by
    rw [trig_pi_div_six, div_eq_mul_inv, tC_inv, z24_pow_20]
    push_cast
    linear_combination (1 / 4 : ℂ) * sqrt3_sq + ((1 : ℂ) / 4 + ((Real.sqrt 3 : ℝ) : ℂ) / 4) *
      Complex.I_sq
  rw [e, arg_real_mul_trig (by positivity) pi_div_six_mem]

/-- The bracket of the twisted series vanishes. -/
theorem tw_bracket : gfun z24 - gfun (z24 ^ 5) + gfun (z24 ^ 13) - gfun (z24 ^ 17) +
    gfun (z24 ^ 4) - gfun (z24 ^ 20) = 0 := by
  rw [gfun_z24_5, gfun_z24_17, gfun_z24_4, gfun_z24_20]
  linarith [gfun_z24_add_13]

/-- **The twisted series**: its pattern is rational, and its value is 0. -/
theorem hasSum_namedTW : HasSum (seriesTerm namedTW) 0 := by
  have hz1 : ‖z24‖ = 1 := by simpa using norm_z24_pow 1
  have h := ((((((hasSum_gfun hz1).sub (hasSum_gfun (norm_z24_pow 5))).add
    (hasSum_gfun (norm_z24_pow 13))).sub (hasSum_gfun (norm_z24_pow 17))).add
    (hasSum_gfun (norm_z24_pow 4))).sub (hasSum_gfun (norm_z24_pow 20))).mul_left
    (Real.sqrt 3)
  rw [tw_bracket, mul_zero] at h
  convert h using 1
  funext k
  have e : seriesTerm namedTW k = -((psTW k * tC⁻¹ ^ k).im / k) := by
    rw [psTW_eq, mul_tC_inv_pow_im, seriesTerm, namedTW, rhoA]
    push_cast
    ring
  rw [e, psTW, dTW_eq, mul_assoc, Complex.im_ofReal_mul]
  simp only [Pi.sub_apply, Pi.add_apply, sub_mul, add_mul, Complex.sub_im, Complex.add_im]
  ring

/-! ## 4. Period 120 -/

theorem UZ_add_120 (k : ℕ) : UZ (k + 120) = UZ k := by
  have h2 : 2 ∣ k + 120 ↔ 2 ∣ k := by omega
  have e2 : (k + 120) / 2 = k / 2 + 4 * 15 := by omega
  simp only [UZ, h2, e2, pow_add_four_mul negI_pow_four]

theorem rhoA_add_120 {P : ℕ → GaussianInt} (hP : ∀ k, P (k + 120) = P k) (k : ℕ) :
    rhoA P (k + 120) = rhoA P k := by simp only [rhoA, hP, UZ_add_120]

theorem rhoL_add_120 {P : ℕ → GaussianInt} (hP : ∀ k, P (k + 120) = P k) (k : ℕ) :
    rhoL P (k + 120) = rhoL P k := by simp only [rhoL, hP, UZ_add_120]

theorem models_add_120 (k : ℕ) :
    P1Z (k + 120) = P1Z k ∧ P2Z (k + 120) = P2Z k ∧ P6Z (k + 120) = P6Z k ∧
      P10Z (k + 120) = P10Z k ∧ P8aZ (k + 120) = P8aZ k ∧ P8bZ (k + 120) = P8bZ k ∧
      P24Z (k + 120) = P24Z k ∧ PTWZ (k + 120) = PTWZ k := by
  have h2 : 2 ∣ k + 120 ↔ 2 ∣ k := by omega
  have h3 : 3 ∣ k + 120 ↔ 3 ∣ k := by omega
  have h5 : 5 ∣ k + 120 ↔ 5 ∣ k := by omega
  have h6 : 6 ∣ k + 120 ↔ 6 ∣ k := by omega
  have h10 : 10 ∣ k + 120 ↔ 10 ∣ k := by omega
  have e2 : (k + 120) / 2 = k / 2 + 4 * 15 := by omega
  have e6 : (k + 120) / 6 = k / 6 + 4 * 5 := by omega
  have e24 : (k + 120) % 24 = k % 24 := by omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [P2Z, P6Z, P10Z, P8aZ, P8bZ, P24Z, PTWZ, h2, h3, h5, h6, h10, e2, e6, e24,
      pow_add_four_mul gI_pow_four, pow_add_four_mul negI_pow_four]

/-- The eight patterns have period 120. -/
theorem named_periodic (k : ℕ) :
    namedA1 (k + 120) = namedA1 k ∧ namedA6 (k + 120) = namedA6 k ∧
      namedA10 (k + 120) = namedA10 k ∧ namedL6 (k + 120) = namedL6 k ∧
      namedL8 (k + 120) = namedL8 k ∧ namedL10 (k + 120) = namedL10 k ∧
      namedL24 (k + 120) = namedL24 k ∧ namedTW (k + 120) = namedTW k := by
  have hm := fun k => models_add_120 k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [namedA1, namedA6, namedA10, namedL6, namedL8, namedL10, namedL24, namedTW,
      rhoA_add_120 (fun k => (hm k).1), rhoA_add_120 (fun k => (hm k).2.1),
      rhoA_add_120 (fun k => (hm k).2.2.1), rhoA_add_120 (fun k => (hm k).2.2.2.1),
      rhoA_add_120 (fun k => (hm k).2.2.2.2.2.2.2),
      rhoL_add_120 (fun k => (hm k).1), rhoL_add_120 (fun k => (hm k).2.1),
      rhoL_add_120 (fun k => (hm k).2.2.1), rhoL_add_120 (fun k => (hm k).2.2.2.1),
      rhoL_add_120 (fun k => (hm k).2.2.2.2.1), rhoL_add_120 (fun k => (hm k).2.2.2.2.2.1),
      rhoL_add_120 (fun k => (hm k).2.2.2.2.2.2.1)]

/-! ## 5. Linear independence -/

