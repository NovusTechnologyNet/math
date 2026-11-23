import Pilean.Polylog.Dilog

/-!
# Bailey's Compendium, degree 2, base 64: formulas (30) and (32)

Formulas (30) and (32) of the Compendium (page 10), stated as printed:

* (30) `π² = 9/8 · P(2, 64, 6, (16, -24, -8, -6, 1, 0))`;
* (32) `log² 2 = 1/32 · P(2, 64, 6, (64, -160, -56, -40, 4, -1))`.

With `m = 6k + j` the weight `64^(-k)` is `2^j · 2^(-m)`, so `P(2, 64, 6, A)` is
`∑_m c(m) 2^(-m) / m²` with `c(j) = 2^j a_j` of period 6. Both vectors have a pattern of the
form `c = c₁ + c₂ [2 ∣ m] + c₃ [3 ∣ m] + c₆ [6 ∣ m]`, and the sub-series over the multiples of
`d` is `Li_2(2^(-d)) / d²` (`Polylog.hasSum_dvd`). So

  `P(2, 64, 6, A) = c₁ Li_2(1/2) + c₂ Li_2(1/4)/4 + c₃ Li_2(1/8)/9 + c₆ Li_2(1/64)/36`

(`hasBaileyValueDeg_ladder64`), with `(c₁, c₂, c₃, c₆) = (32, -128, -96, 192)` for (30) and
`(128, -768, -576, 1152)` for (32). The values follow from the ladder
`6 Li_2(1/2) - 6 Li_2(1/4) - 2 Li_2(1/8) + Li_2(1/64) = π²/6` (`Polylog.dilog_ladder_two`) and
`Li_2(1/2) = π²/12 - (log 2)²/2` (`Polylog.polylogReal_two_half`); only the real dilogarithm
is used (Landen's identity, duplication, the value at `1/2`).
-/

namespace PiFormula

namespace Compendium

open Polylog

/-- The sequence `u(m) = c(m) 2^(-m)` of a pattern
`c = c₁ + c₂ [2 ∣ m] + c₃ [3 ∣ m] + c₆ [6 ∣ m]`. -/
noncomputable def ladder64 (c₁ c₂ c₃ c₆ : ℝ) (m : ℕ) : ℝ :=
  c₁ * (1 / 2) ^ m + c₂ * (if 2 ∣ m then (1 / 4) ^ (m / 2) else 0)
    + c₃ * (if 3 ∣ m then (1 / 8) ^ (m / 3) else 0)
    + c₆ * (if 6 ∣ m then (1 / 64) ^ (m / 6) else 0)

theorem ladder64_add_six (c₁ c₂ c₃ c₆ : ℝ) (m : ℕ) :
    ladder64 c₁ c₂ c₃ c₆ (m + 6) = ladder64 c₁ c₂ c₃ c₆ m / ((64 : ℕ) : ℝ) ^ 1 := by
  have d2 : 2 ∣ m + 6 ↔ 2 ∣ m := by omega
  have d3 : 3 ∣ m + 6 ↔ 3 ∣ m := by omega
  have d6 : 6 ∣ m + 6 ↔ 6 ∣ m := by omega
  have q2 : (m + 6) / 2 = m / 2 + 3 := by omega
  have q3 : (m + 6) / 3 = m / 3 + 2 := by omega
  have q6 : (m + 6) / 6 = m / 6 + 1 := by omega
  simp only [ladder64, d2, d3, d6, q2, q3, q6, pow_add]
  push_cast
  split_ifs <;> ring

/-- `∑_{m ≥ 1} u(m) / m² = c₁ Li_2(1/2) + c₂ Li_2(1/4)/4 + c₃ Li_2(1/8)/9 + c₆ Li_2(1/64)/36`
for `u = ladder64 c₁ c₂ c₃ c₆`. -/
theorem hasSum_ladder64 (c₁ c₂ c₃ c₆ : ℝ) :
    HasSum (fun m : ℕ => ladder64 c₁ c₂ c₃ c₆ m / (m : ℝ) ^ 2)
      (c₁ * polylogReal 2 (1 / 2) + c₂ * (polylogReal 2 (1 / 4) / 4)
        + c₃ * (polylogReal 2 (1 / 8) / 9) + c₆ * (polylogReal 2 (1 / 64) / 36)) := by
  have h1 := (hasSum_polylogReal_nat (s := 2) le_rfl (x := 1 / 2)
    (by rw [abs_of_pos] <;> norm_num)).mul_left c₁
  have h2 := (hasSum_dvd (d := 2) two_pos (hasSum_polylogReal_nat (s := 2) le_rfl (x := 1 / 4)
    (by rw [abs_of_pos] <;> norm_num))).mul_left c₂
  have h3 := (hasSum_dvd (d := 3) three_pos (hasSum_polylogReal_nat (s := 2) le_rfl
    (x := 1 / 8) (by rw [abs_of_pos] <;> norm_num))).mul_left c₃
  have h6 := (hasSum_dvd (d := 6) (by norm_num) (hasSum_polylogReal_nat (s := 2) le_rfl
    (x := 1 / 64) (by rw [abs_of_pos] <;> norm_num))).mul_left c₆
  have h := ((h1.add h2).add h3).add h6
  have e : (fun m : ℕ => ladder64 c₁ c₂ c₃ c₆ m / (m : ℝ) ^ 2) = fun m : ℕ =>
      c₁ * ((1 / 2) ^ m / (m : ℝ) ^ 2)
        + c₂ * (if 2 ∣ m then (1 / 4) ^ (m / 2) / (m : ℝ) ^ 2 else 0)
        + c₃ * (if 3 ∣ m then (1 / 8) ^ (m / 3) / (m : ℝ) ^ 2 else 0)
        + c₆ * (if 6 ∣ m then (1 / 64) ^ (m / 6) / (m : ℝ) ^ 2 else 0) := by
    funext m
    simp only [ladder64]
    split_ifs <;> ring
  rw [e]
  convert h using 1
  norm_num

/-- **Vectors of base 64 and length 6 with a ladder pattern.** If `a_i = u(i)` for
`u = ladder64 c₁ c₂ c₃ c₆` (`1 ≤ i ≤ 6`), then
`P(2, 64, 6, a) = c₁ Li_2(1/2) + c₂ Li_2(1/4)/4 + c₃ Li_2(1/8)/9 + c₆ Li_2(1/64)/36`. -/
theorem hasBaileyValueDeg_ladder64 (c₁ c₂ c₃ c₆ : ℝ) (a : Fin 6 → ℚ)
    (ha : ∀ i : Fin 6, ladder64 c₁ c₂ c₃ c₆ ((i : ℕ) + 1) = (a i : ℝ)) :
    HasBaileyValueDeg 2 64 1 6 a
      (c₁ * polylogReal 2 (1 / 2) + c₂ * (polylogReal 2 (1 / 4) / 4)
        + c₃ * (polylogReal 2 (1 / 8) / 9) + c₆ * (polylogReal 2 (1 / 64) / 36)) :=
  hasBaileyValueDeg_of_quasiperiodic two_ne_zero (by norm_num) (ladder64_add_six c₁ c₂ c₃ c₆) ha
    (hasSum_ladder64 c₁ c₂ c₃ c₆)

/-- **Formula (30)** of the Compendium (page 10):
`π² = 9/8 P(2, 64, 6, (16, -24, -8, -6, 1, 0))`. -/
theorem formula_30 : BaileyFormulaDeg (Real.pi ^ 2) (9 / 8) 2 64 1 6 ![16, -24, -8, -6, 1, 0] := by
  refine (hasBaileyValueDeg_ladder64 32 (-128) (-96) 192 _ fun i => ?_).formula ?_
  · fin_cases i <;> norm_num [ladder64]
  · linear_combination (-6 : ℝ) * dilog_ladder_two

/-- **Formula (32)** of the Compendium (page 10):
`log² 2 = 1/32 P(2, 64, 6, (64, -160, -56, -40, 4, -1))`. -/
theorem formula_32 :
    BaileyFormulaDeg (Real.log 2 ^ 2) (1 / 32) 2 64 1 6 ![64, -160, -56, -40, 4, -1] := by
  refine (hasBaileyValueDeg_ladder64 128 (-768) (-576) 1152 _ fun i => ?_).formula ?_
  · fin_cases i <;> norm_num [ladder64]
  · linear_combination (-1 : ℝ) * dilog_ladder_two + 2 * polylogReal_two_half

end Compendium

end PiFormula
