import Pilean.RatBase.FourThirds

/-!
# A relation in base 4: a series for `π√3`

`π√3 / 9 = ∑_{k ≥ 1} ρ(k) (1/4)^⌊k/2⌋ / k`,   `ρ = (1/2, 1, 0, -1, -1/2, 0)` of period 6

(`hasSum_rhoFour`). So base 4 has a relation in the class of series `∑ ρ(k) 4^(-⌊k/2⌋) / k`;
it is one of the five rational bases that do (`TheoremR.lean`).

The proof is that of `FourThirds.lean` at the point `w = (1/2) e^(iπ/3) = 1/4 + (√3/4) i`:
`1 - w = (√3/2) e^(-iπ/6)`, so `∑ Im(w^k) / k = arctan(1/√3) = π/6`, and `w³ = -1/8` gives
`Im(w^k) = (√3/2) ρ(k) (1/4)^⌊k/2⌋`.
-/

open Complex

namespace PiFormula

namespace RatBase

/-- `w = (1/2) e^(iπ/3) = 1/4 + (√3/4) i`. -/
noncomputable def wFour : ℂ := ⟨1 / 4, Real.sqrt 3 / 4⟩

/-- `w` is a root of `X^2 - (1/2) X + 1/4`. -/
theorem wFour_sq : wFour ^ 2 = ((1 / 2 : ℝ) : ℂ) * wFour - ((1 / 4 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [wFour, sq, mul_re, sub_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    linear_combination (-1 / 16 : ℝ) * sqrt_three_sq
  · simp only [wFour, sq, mul_im, sub_im, ofReal_re, ofReal_im, zero_mul, add_zero, sub_zero]
    ring

theorem wFour_pow_three : wFour ^ 3 = ((-(1 / 8) : ℝ) : ℂ) := by
  have h := wFour_sq
  push_cast at h ⊢
  linear_combination (wFour + 1 / 2) * h

theorem wFour_pow_six : wFour ^ 6 = ((1 / 64 : ℝ) : ℂ) := by
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, wFour_pow_three]
  push_cast
  ring

theorem norm_wFour_lt_one : ‖wFour‖ < 1 := by
  have h : ‖wFour‖ ^ 2 = 1 / 4 := by
    rw [Complex.sq_norm, normSq_apply]
    change (1 / 4 : ℝ) * (1 / 4) + Real.sqrt 3 / 4 * (Real.sqrt 3 / 4) = 1 / 4
    linear_combination (1 / 16 : ℝ) * sqrt_three_sq
  nlinarith [norm_nonneg wFour]

/-- The pattern `(1/2, 1, 0, -1, -1/2, 0)` of period 6. -/
def rhoFour (k : ℕ) : ℚ :=
  match k % 6 with
    | 1 => 1 / 2
    | 2 => 1
    | 4 => -1
    | 5 => -(1 / 2)
    | _ => 0

theorem rhoFour_periodic (k : ℕ) : rhoFour (k + 6) = rhoFour k := by
  have h : (k + 6) % 6 = k % 6 := by omega
  simp only [rhoFour, h]

/-- `Im(w^k) = (√3/2) ρ(k) (1/4)^⌊k/2⌋`. -/
theorem wFour_pow_im (k : ℕ) :
    (wFour ^ k).im = Real.sqrt 3 / 2 * ((rhoFour k : ℝ) * (1 / 4 : ℝ) ^ (k / 2)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 6 with hk | hk
    · interval_cases k
      · simp [rhoFour]
      · simp [rhoFour, wFour]
        ring
      · rw [wFour_sq]
        simp [rhoFour, wFour]
        ring
      · rw [wFour_pow_three]
        simp [rhoFour]
      · rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, wFour_pow_three, pow_one]
        simp [rhoFour, wFour]
        ring
      · rw [show (5 : ℕ) = 3 + 2 from rfl, pow_add, wFour_pow_three, wFour_sq]
        simp [rhoFour, wFour]
        ring
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
      have h := ih m (by omega)
      have e : (m + 6) / 2 = m / 2 + 3 := by omega
      rw [pow_add, wFour_pow_six, mul_im, ofReal_re, ofReal_im, mul_zero, zero_add, h,
        rhoFour_periodic, e, pow_add]
      ring

/-- **A relation in base 4**: `∑_{k ≥ 1} ρ(k) (1/4)^⌊k/2⌋ / k = π√3 / 9`. -/
theorem hasSum_rhoFour : HasSum (seriesTermRat 4 1 rhoFour) (Real.sqrt 3 * Real.pi / 9) := by
  have h := (hasSum_im_pow_div norm_wFour_lt_one).mul_left (2 * Real.sqrt 3 / 3)
  have e0 : Real.sqrt 3 / 3 = (Real.sqrt 3)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by linear_combination (1 / 3 : ℝ) * sqrt_three_sq)
  have e1 : wFour.im / (1 - wFour.re) = (Real.sqrt 3)⁻¹ := by
    rw [← e0]
    change Real.sqrt 3 / 4 / (1 - 1 / 4) = Real.sqrt 3 / 3
    ring
  rw [e1, Real.arctan_inv_sqrt_three] at h
  have e2 : 2 * Real.sqrt 3 / 3 * (Real.pi / 6) = Real.sqrt 3 * Real.pi / 9 := by ring
  rw [e2] at h
  refine h.congr_fun fun k => ?_
  rw [seriesTermRat, wFour_pow_im]
  push_cast
  linear_combination
    (-1 / 3 * (rhoFour k : ℝ) * (1 / 4 : ℝ) ^ (k / 2) / (k : ℝ)) * sqrt_three_sq

end RatBase

end PiFormula
