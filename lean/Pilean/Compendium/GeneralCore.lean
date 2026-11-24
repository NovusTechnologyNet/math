module

public import Pilean.Compendium.GeneralDefs
public import Pilean.Compendium.Arctan

/-!
# Bailey's Compendium, general bases: the seven series behind the formulas

Every formula of the section "General bases" is one of the following series, at a value of `v`
that is a multiple of `1/b` or of `1/√b`, multiplied by a constant. Each series is the real or
the imaginary part of `∑_{n ≥ 1} (v c)^n / n = -log (1 - v c)` for a complex number `c` with a
real power `c^N` (`hasBaileyValueReal_im`, `hasBaileyValueReal_re`), cut into blocks of
length `N`:

* `hasBaileyValueReal_pow` (`c = 1`): `a_i = v^i`, value `-log (1 - v)`;
* `hasBaileyValueReal_gauss_im`, `hasBaileyValueReal_gauss_re` (`c = 1 + i`, `c^4 = -4`):
  values `arctan (v / (1 - v))` and `-(1/2) log (1 - 2v + 2v²)`, for `2v² < 1`;
* `hasBaileyValueReal_w3_im`, `hasBaileyValueReal_w3_re` (`c = ω = (-1 + i√3)/2`, `c^3 = 1`):
  values `arctan (√3 v / (2 + v))` and `-(1/2) log (1 + v + v²)`, for `v² < 1`;
* `hasBaileyValueReal_eis_im`, `hasBaileyValueReal_eis_re` (`c = (3 + i√3)/2`, `c^6 = -27`):
  values `arctan (√3 v / (2 - 3v))` and `-(1/2) log (1 - 3v + 3v²)`, for `3v² < 1`.

The coefficient vectors are `a_i = v^i t_i` with the table `t` of the imaginary or real parts
of `c, c², …, c^N`.
-/

@[expose] public section

namespace PiFormula

namespace Compendium

open BaseB

/-! ## 0. The parameter -/

theorem param_ne_zero {b : ℝ} (hb : 1 < |b|) : b ≠ 0 := by
  rintro rfl
  rw [abs_zero] at hb
  linarith

theorem param_abs_inv_lt_one {b : ℝ} (hb : 1 < |b|) : |1 / b| < 1 := by
  rw [abs_div, abs_one, div_lt_one (by linarith)]
  exact hb

theorem param_inv_sq_lt_one {b : ℝ} (hb : 1 < |b|) : (1 / b) ^ 2 < 1 := by
  rw [← sq_abs]
  exact pow_lt_one₀ (abs_nonneg _) (param_abs_inv_lt_one hb) two_ne_zero

theorem param_gauss {b : ℝ} (hb : 1 < 2 * b ^ 2) : 2 * (1 / (2 * b)) ^ 2 < 1 := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    norm_num at hb
  have e : 2 * (1 / (2 * b)) ^ 2 = 1 / (2 * b ^ 2) := by
    field_simp
  rw [e, div_lt_one (by positivity)]
  exact hb

theorem param_eis {b : ℝ} (hb : 1 < 3 * b ^ 2) : 3 * (1 / (3 * b)) ^ 2 < 1 := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    norm_num at hb
  have e : 3 * (1 / (3 * b)) ^ 2 = 1 / (3 * b ^ 2) := by
    field_simp
  rw [e, div_lt_one (by positivity)]
  exact hb

theorem one_lt_natCast_of_two_le {b : ℕ} (hb : 2 ≤ b) : (1 : ℝ) < (b : ℝ) := by
  exact_mod_cast hb

theorem one_lt_abs_natCast {b : ℕ} (hb : 2 ≤ b) : (1 : ℝ) < |(b : ℝ)| := by
  rw [Nat.abs_cast]
  exact one_lt_natCast_of_two_le hb

/-! ## 1. The series of `-log (1 - v)` -/

/-- **The pattern `v^n`.** For `|v| < 1` and `β v^N = 1`:
`P(1, β, N, (v, v², …, v^N)) = -log (1 - v)`. -/
theorem hasBaileyValueReal_pow {N : ℕ} (hN : 0 < N) {v β : ℝ} (hβ : v ^ N * β = 1)
    (hv : |v| < 1) :
    HasBaileyValueReal β N (fun i => v ^ ((i : ℕ) + 1)) (-Real.log (1 - v)) := by
  have hβ0 : β ≠ 0 := fun h0 => by simp [h0] at hβ
  have hu : ∀ n : ℕ, v ^ (n + N) = v ^ n / β := by
    intro n
    rw [pow_add, eq_div_iff hβ0]
    linear_combination (v ^ n) * hβ
  exact hasBaileyValueReal_of_quasiperiodic (u := fun n => v ^ n) hN hu (hasSum_pow_div hv)

/-! ## 2. The constant `1 + i` -/

/-- The complex number `1 + i`. -/
noncomputable def cGauss : ℂ := 1 + Complex.I

theorem cGauss_re : cGauss.re = 1 := by simp [cGauss]

theorem cGauss_im : cGauss.im = 1 := by simp [cGauss]

theorem cGauss_sq : cGauss ^ 2 = 2 * Complex.I := by
  rw [cGauss, add_sq, Complex.I_sq]
  ring

theorem cGauss_pow_four : cGauss ^ 4 = ((-4 : ℝ) : ℂ) := by
  rw [show 4 = 2 * 2 by norm_num, pow_mul, cGauss_sq, mul_pow, Complex.I_sq]
  push_cast
  ring

theorem cGauss_pow_eight : cGauss ^ 8 = ((16 : ℝ) : ℂ) := by
  rw [show 8 = 4 * 2 by norm_num, pow_mul, cGauss_pow_four]
  push_cast
  ring

theorem normSq_cGauss : Complex.normSq cGauss = 2 := by
  rw [Complex.normSq_apply, cGauss_re, cGauss_im]
  norm_num

/-- The imaginary parts of `(1 + i)^n` for `n = 1, …, 8`. -/
theorem cGauss_im_table :
    (fun i : Fin 8 => (cGauss ^ ((i : ℕ) + 1)).im) = ![1, 2, 2, 0, -4, -8, -8, 0] := by
  have p3 : cGauss ^ 3 = cGauss ^ 2 * cGauss := pow_succ _ _
  have p5 : cGauss ^ 5 = cGauss ^ 4 * cGauss := pow_succ _ _
  have p6 : cGauss ^ 6 = cGauss ^ 4 * cGauss ^ 2 := by rw [← pow_add]
  have p7 : cGauss ^ 7 = cGauss ^ 4 * (cGauss ^ 2 * cGauss) := by rw [← pow_succ, ← pow_add]
  funext i
  fin_cases i <;>
    simp [p3, p5, p6, p7, cGauss_sq, cGauss_pow_four, cGauss_pow_eight, cGauss_re, cGauss_im] <;>
    norm_num

/-- The real parts of `(1 + i)^n` for `n = 1, …, 4`. -/
theorem cGauss_re_table :
    (fun i : Fin 4 => (cGauss ^ ((i : ℕ) + 1)).re) = ![1, 0, -2, -4] := by
  have p3 : cGauss ^ 3 = cGauss ^ 2 * cGauss := pow_succ _ _
  funext i
  fin_cases i <;> simp [p3, cGauss_sq, cGauss_pow_four, cGauss_re, cGauss_im]

/-- **The series of `arctan (v / (1 - v))`.** For `2v² < 1` and `16 β v^8 = 1`:
`P(1, β, 8, a) = arctan (v / (1 - v))` with `a_i = v^i Im((1 + i)^i)`, that is
`a = (v, 2v², 2v³, 0, -4v⁵, -8v⁶, -8v⁷, 0)`. -/
theorem hasBaileyValueReal_gauss_im {v β : ℝ} (hβ : v ^ 8 * 16 * β = 1) (hv : 2 * v ^ 2 < 1) :
    HasBaileyValueReal β 8 (fun i => v ^ ((i : ℕ) + 1) * ![1, 2, 2, 0, -4, -8, -8, 0] i)
      (Real.arctan (v / (1 - v))) := by
  have h := hasBaileyValueReal_im (N := 8) (by norm_num) cGauss_pow_eight (v := v) (β := β) hβ
    (by rw [normSq_cGauss]; linarith)
  have e : (fun i : Fin 8 => v ^ ((i : ℕ) + 1) * (cGauss ^ ((i : ℕ) + 1)).im) =
      fun i : Fin 8 => v ^ ((i : ℕ) + 1) * ![1, 2, 2, 0, -4, -8, -8, 0] i := by
    funext i
    rw [← cGauss_im_table]
  rw [e, cGauss_im, cGauss_re, mul_one] at h
  exact h

/-- **The series of `-(1/2) log (1 - 2v + 2v²)`.** For `2v² < 1` and `-4 β v^4 = 1`:
`P(1, β, 4, a) = -(1/2) log (1 - 2v + 2v²)` with `a_i = v^i Re((1 + i)^i)`, that is
`a = (v, 0, -2v³, -4v⁴)`. -/
theorem hasBaileyValueReal_gauss_re {v β : ℝ} (hβ : v ^ 4 * (-4) * β = 1)
    (hv : 2 * v ^ 2 < 1) :
    HasBaileyValueReal β 4 (fun i => v ^ ((i : ℕ) + 1) * ![1, 0, -2, -4] i)
      (-(1 / 2) * Real.log (1 - 2 * v + 2 * v ^ 2)) := by
  have h := hasBaileyValueReal_re (N := 4) (by norm_num) cGauss_pow_four (v := v) (β := β) hβ
    (by rw [normSq_cGauss]; linarith)
  have e : (fun i : Fin 4 => v ^ ((i : ℕ) + 1) * (cGauss ^ ((i : ℕ) + 1)).re) =
      fun i : Fin 4 => v ^ ((i : ℕ) + 1) * ![1, 0, -2, -4] i := by
    funext i
    rw [← cGauss_re_table]
  have e2 : (1 - v * 1) ^ 2 + (v * 1) ^ 2 = 1 - 2 * v + 2 * v ^ 2 := by ring
  rw [e, cGauss_im, cGauss_re, e2] at h
  exact h

/-! ## 3. The cube root of unity `ω = (-1 + i√3)/2` -/

theorem w3_im : Base3.w3.im = Real.sqrt 3 / 2 := rfl

theorem normSq_w3 : Complex.normSq Base3.w3 = 1 := by
  rw [Complex.normSq_apply, Base3.w3_re, w3_im]
  linear_combination (1 / 4 : ℝ) * Base3.sqrt3_mul_self

theorem w3_pow_three_ofReal : Base3.w3 ^ 3 = ((1 : ℝ) : ℂ) := by
  rw [Base3.w3_pow_three, Complex.ofReal_one]

/-- The imaginary parts of `ω, ω², ω³`. -/
theorem w3_im_table : (fun i : Fin 3 => (Base3.w3 ^ ((i : ℕ) + 1)).im) =
    ![Real.sqrt 3 / 2, -(Real.sqrt 3 / 2), 0] := by
  funext i
  fin_cases i <;> simp [Base3.w3_sq, Base3.w3_pow_three, w3_im]

/-- The real parts of `ω, ω², ω³`. -/
theorem w3_re_table : (fun i : Fin 3 => (Base3.w3 ^ ((i : ℕ) + 1)).re) =
    ![-1 / 2, -1 / 2, 1] := by
  funext i
  fin_cases i <;> simp [Base3.w3_sq, Base3.w3_pow_three, Base3.w3_re]

/-- **The series of `arctan (√3 v / (2 + v))`.** For `v² < 1` and `β v^3 = 1`:
`P(1, β, 3, a) = arctan (√3 v / (2 + v))` with `a_i = v^i Im(ω^i)`, that is
`a = (√3 v / 2, -√3 v² / 2, 0)`. -/
theorem hasBaileyValueReal_w3_im {v β : ℝ} (hβ : v ^ 3 * β = 1) (hv : v ^ 2 < 1) :
    HasBaileyValueReal β 3
      (fun i => v ^ ((i : ℕ) + 1) * ![Real.sqrt 3 / 2, -(Real.sqrt 3 / 2), 0] i)
      (Real.arctan (Real.sqrt 3 * v / (2 + v))) := by
  have h := hasBaileyValueReal_im (N := 3) (by norm_num) w3_pow_three_ofReal (v := v) (β := β)
    (by rw [mul_one]; exact hβ) (by rw [normSq_w3]; linarith)
  have e : (fun i : Fin 3 => v ^ ((i : ℕ) + 1) * (Base3.w3 ^ ((i : ℕ) + 1)).im) =
      fun i : Fin 3 => v ^ ((i : ℕ) + 1) * ![Real.sqrt 3 / 2, -(Real.sqrt 3 / 2), 0] i := by
    funext i
    rw [← w3_im_table]
  have hv1 : -1 < v := by nlinarith
  have e2 : v * (Real.sqrt 3 / 2) / (1 - v * (-1 / 2)) = Real.sqrt 3 * v / (2 + v) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  rw [e, w3_im, Base3.w3_re, e2] at h
  exact h

/-- **The series of `-(1/2) log (1 + v + v²)`.** For `v² < 1` and `β v^3 = 1`:
`P(1, β, 3, a) = -(1/2) log (1 + v + v²)` with `a_i = v^i Re(ω^i)`, that is
`a = (-v/2, -v²/2, v³)`. -/
theorem hasBaileyValueReal_w3_re {v β : ℝ} (hβ : v ^ 3 * β = 1) (hv : v ^ 2 < 1) :
    HasBaileyValueReal β 3 (fun i => v ^ ((i : ℕ) + 1) * ![-1 / 2, -1 / 2, 1] i)
      (-(1 / 2) * Real.log (1 + v + v ^ 2)) := by
  have h := hasBaileyValueReal_re (N := 3) (by norm_num) w3_pow_three_ofReal (v := v) (β := β)
    (by rw [mul_one]; exact hβ) (by rw [normSq_w3]; linarith)
  have e : (fun i : Fin 3 => v ^ ((i : ℕ) + 1) * (Base3.w3 ^ ((i : ℕ) + 1)).re) =
      fun i : Fin 3 => v ^ ((i : ℕ) + 1) * ![-1 / 2, -1 / 2, 1] i := by
    funext i
    rw [← w3_re_table]
  have e2 : (1 - v * (-1 / 2)) ^ 2 + (v * (Real.sqrt 3 / 2)) ^ 2 = 1 + v + v ^ 2 := by
    linear_combination (v ^ 2 / 4) * Base3.sqrt3_mul_self
  rw [e, w3_im, Base3.w3_re, e2] at h
  exact h

/-! ## 4. The constant `(3 + i√3)/2` -/

/-- The complex number `(3 + i√3)/2 = 2 + ω`, of modulus `√3` and argument `π/6`. -/
noncomputable def cEis : ℂ := ⟨3 / 2, Real.sqrt 3 / 2⟩

theorem cEis_re : cEis.re = 3 / 2 := rfl

theorem cEis_im : cEis.im = Real.sqrt 3 / 2 := rfl

theorem normSq_cEis : Complex.normSq cEis = 3 := by
  rw [Complex.normSq_apply, cEis_re, cEis_im]
  linear_combination (1 / 4 : ℝ) * Base3.sqrt3_mul_self

theorem cEis_sq : cEis ^ 2 = ⟨3 / 2, 3 * Real.sqrt 3 / 2⟩ := by
  rw [pow_two]
  apply Complex.ext
  · simp only [Complex.mul_re, cEis]
    linear_combination (-1 / 4 : ℝ) * Base3.sqrt3_mul_self
  · simp only [Complex.mul_im, cEis]
    ring

theorem cEis_pow_three : cEis ^ 3 = ⟨0, 3 * Real.sqrt 3⟩ := by
  rw [pow_succ, cEis_sq]
  apply Complex.ext
  · simp only [Complex.mul_re, cEis]
    linear_combination (-3 / 4 : ℝ) * Base3.sqrt3_mul_self
  · simp only [Complex.mul_im, cEis]
    ring

theorem cEis_pow_four : cEis ^ 4 = ⟨-9 / 2, 9 * Real.sqrt 3 / 2⟩ := by
  rw [pow_succ, cEis_pow_three]
  apply Complex.ext
  · simp only [Complex.mul_re, cEis]
    linear_combination (-3 / 2 : ℝ) * Base3.sqrt3_mul_self
  · simp only [Complex.mul_im, cEis]
    ring

theorem cEis_pow_five : cEis ^ 5 = ⟨-27 / 2, 9 * Real.sqrt 3 / 2⟩ := by
  rw [show 5 = 3 + 2 by norm_num, pow_add, cEis_pow_three, cEis_sq]
  apply Complex.ext
  · simp only [Complex.mul_re]
    linear_combination (-9 / 2 : ℝ) * Base3.sqrt3_mul_self
  · simp only [Complex.mul_im]
    ring

theorem cEis_pow_six : cEis ^ 6 = ((-27 : ℝ) : ℂ) := by
  rw [show 6 = 3 + 3 by norm_num, pow_add, cEis_pow_three]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re]
    linear_combination (-9 : ℝ) * Base3.sqrt3_mul_self
  · simp only [Complex.mul_im, Complex.ofReal_im]
    ring

/-- The imaginary parts of `c, c², …, c⁶` for `c = (3 + i√3)/2`. -/
theorem cEis_im_table : (fun i : Fin 6 => (cEis ^ ((i : ℕ) + 1)).im) =
    ![Real.sqrt 3 / 2, 3 * Real.sqrt 3 / 2, 3 * Real.sqrt 3, 9 * Real.sqrt 3 / 2,
      9 * Real.sqrt 3 / 2, 0] := by
  funext i
  fin_cases i <;>
    simp [cEis_sq, cEis_pow_three, cEis_pow_four, cEis_pow_five, cEis_pow_six, cEis_im]

/-- The real parts of `c, c², …, c⁶` for `c = (3 + i√3)/2`. -/
theorem cEis_re_table : (fun i : Fin 6 => (cEis ^ ((i : ℕ) + 1)).re) =
    ![3 / 2, 3 / 2, 0, -9 / 2, -27 / 2, -27] := by
  funext i
  fin_cases i <;>
    simp [cEis_sq, cEis_pow_three, cEis_pow_four, cEis_pow_five, cEis_pow_six, cEis_re]

/-- **The series of `arctan (√3 v / (2 - 3v))`.** For `3v² < 1` and `-27 β v^6 = 1`:
`P(1, β, 6, a) = arctan (√3 v / (2 - 3v))` with `a_i = v^i Im(c^i)`, `c = (3 + i√3)/2`, that is
`a = (√3/2) (v, 3v², 6v³, 9v⁴, 9v⁵, 0)`. -/
theorem hasBaileyValueReal_eis_im {v β : ℝ} (hβ : v ^ 6 * (-27) * β = 1)
    (hv : 3 * v ^ 2 < 1) :
    HasBaileyValueReal β 6
      (fun i => v ^ ((i : ℕ) + 1) * ![Real.sqrt 3 / 2, 3 * Real.sqrt 3 / 2, 3 * Real.sqrt 3,
        9 * Real.sqrt 3 / 2, 9 * Real.sqrt 3 / 2, 0] i)
      (Real.arctan (Real.sqrt 3 * v / (2 - 3 * v))) := by
  have h := hasBaileyValueReal_im (N := 6) (by norm_num) cEis_pow_six (v := v) (β := β) hβ
    (by rw [normSq_cEis]; linarith)
  have e : (fun i : Fin 6 => v ^ ((i : ℕ) + 1) * (cEis ^ ((i : ℕ) + 1)).im) =
      fun i : Fin 6 => v ^ ((i : ℕ) + 1) * ![Real.sqrt 3 / 2, 3 * Real.sqrt 3 / 2,
        3 * Real.sqrt 3, 9 * Real.sqrt 3 / 2, 9 * Real.sqrt 3 / 2, 0] i := by
    funext i
    rw [← cEis_im_table]
  have hv1 : 3 * v < 2 := by nlinarith
  have e2 : v * (Real.sqrt 3 / 2) / (1 - v * (3 / 2)) = Real.sqrt 3 * v / (2 - 3 * v) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  rw [e, cEis_im, cEis_re, e2] at h
  exact h

/-- **The series of `-(1/2) log (1 - 3v + 3v²)`.** For `3v² < 1` and `-27 β v^6 = 1`:
`P(1, β, 6, a) = -(1/2) log (1 - 3v + 3v²)` with `a_i = v^i Re(c^i)`, `c = (3 + i√3)/2`, that
is `a = (3v/2, 3v²/2, 0, -9v⁴/2, -27v⁵/2, -27v⁶)`. -/
theorem hasBaileyValueReal_eis_re {v β : ℝ} (hβ : v ^ 6 * (-27) * β = 1)
    (hv : 3 * v ^ 2 < 1) :
    HasBaileyValueReal β 6
      (fun i => v ^ ((i : ℕ) + 1) * ![3 / 2, 3 / 2, 0, -9 / 2, -27 / 2, -27] i)
      (-(1 / 2) * Real.log (1 - 3 * v + 3 * v ^ 2)) := by
  have h := hasBaileyValueReal_re (N := 6) (by norm_num) cEis_pow_six (v := v) (β := β) hβ
    (by rw [normSq_cEis]; linarith)
  have e : (fun i : Fin 6 => v ^ ((i : ℕ) + 1) * (cEis ^ ((i : ℕ) + 1)).re) =
      fun i : Fin 6 => v ^ ((i : ℕ) + 1) * ![3 / 2, 3 / 2, 0, -9 / 2, -27 / 2, -27] i := by
    funext i
    rw [← cEis_re_table]
  have e2 : (1 - v * (3 / 2)) ^ 2 + (v * (Real.sqrt 3 / 2)) ^ 2 = 1 - 3 * v + 3 * v ^ 2 := by
    linear_combination (v ^ 2 / 4) * Base3.sqrt3_mul_self
  rw [e, cEis_im, cEis_re, e2] at h
  exact h

end Compendium

end PiFormula
