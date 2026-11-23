import Pilean.Polylog.PointBase3

/-!
# Bailey's Compendium, degree 2, base 3: formulas (76) and (77)

Formulas (76) and (77) of the Compendium (page 24), stated as printed:

* (76) `π² = 2/27 · P(2, 3^6, 12, (243, -405, 0, -81, -27, -72, -9, -9, 0, -5, 1, 0))`;
* (77) `log² 3 = 1/3^6 · P(2, 3^6, 12, (4374, -13122, 0, -2106, -486, -1944, -162, -234, 0,
  -162, 18, -8))`.

With `m = 12k + j` the weight `3^(-6k)` is `3^(j/2) · 3^(-m/2)`. Put
`z₃ = e^(iπ/6)/√3 = 1/2 + (√3/6) i` (`Polylog.pointThree`), so that `z₃^12 = 3^(-6)`. Both
vectors are `a_j = u(j)` with

  `u(m) = p Re(z₃^m) + r₁ [2 ∣ m] (1/3)^(m/2) + r₂ [2 ∣ m] (-1/3)^(m/2)`   (`eis3 p r₁ r₂`),

and `∑_m u(m)/m² = p Re Li_2(z₃) + r₁ Li_2(1/3)/4 + r₂ Li_2(-1/3)/4` (`hasSum_eis3`), with
`(p, r₁, r₂) = (486, -972, 486)` for (76) and `(8748, -29160, 14580)` for (77). The values:
`Re Li_2(z₃) = 5π²/72 - (log 3)²/8` (reflection formula, `1 - z₃ = conj z₃`) and
`Li_2(-1/3) = 2 Li_2(1/3) - π²/6 + (log 3)²/2` (Landen's identity and duplication); `Li_2(1/3)`
cancels.

Formula (78) (`π √3 log 3`) needs the imaginary parts of `Li_2` at `z₃` and at `i/√3`
(Clausen values); it is not proved here.
-/

namespace PiFormula

namespace Compendium

open Polylog Complex

/-- The sequence `u(m) = p Re(z₃^m) + r₁ [2 ∣ m] (1/3)^(m/2) + r₂ [2 ∣ m] (-1/3)^(m/2)` with
`z₃ = e^(iπ/6)/√3`. -/
noncomputable def eis3 (p r₁ r₂ : ℝ) (m : ℕ) : ℝ :=
  p * (pointThree ^ m).re + r₁ * (if 2 ∣ m then (1 / 3) ^ (m / 2) else 0)
    + r₂ * (if 2 ∣ m then (-1 / 3) ^ (m / 2) else 0)

theorem eis3_add_twelve (p r₁ r₂ : ℝ) (m : ℕ) :
    eis3 p r₁ r₂ (m + 12) = eis3 p r₁ r₂ m / ((3 : ℕ) : ℝ) ^ 6 := by
  have d2 : 2 ∣ m + 12 ↔ 2 ∣ m := by omega
  have q2 : (m + 12) / 2 = m / 2 + 6 := by omega
  simp only [eis3, d2, q2]
  rw [pow_add pointThree, pointThree_pow_twelve, Complex.re_mul_ofReal, pow_add (1 / 3 : ℝ),
    pow_add (-1 / 3 : ℝ)]
  push_cast
  split_ifs <;> ring

/-- `∑_{m ≥ 1} u(m)/m² = p Re Li_2(z₃) + r₁ Li_2(1/3)/4 + r₂ Li_2(-1/3)/4` for
`u = eis3 p r₁ r₂`. -/
theorem hasSum_eis3 (p r₁ r₂ : ℝ) :
    HasSum (fun m : ℕ => eis3 p r₁ r₂ m / (m : ℝ) ^ 2)
      (p * (polylog 2 pointThree).re + r₁ * (polylogReal 2 (1 / 3) / 4)
        + r₂ * (polylogReal 2 (-1 / 3) / 4)) := by
  have h1 := (hasSum_re_polylog_nat (s := 2) le_rfl norm_pointThree_lt.le).mul_left p
  have h2 := (hasSum_dvd (d := 2) two_pos (hasSum_polylogReal_nat (s := 2) le_rfl (x := 1 / 3)
    (by rw [abs_of_pos] <;> norm_num))).mul_left r₁
  have h3 := (hasSum_dvd (d := 2) two_pos (hasSum_polylogReal_nat (s := 2) le_rfl
    (x := -1 / 3) (by rw [abs_le]; constructor <;> norm_num))).mul_left r₂
  have h := (h1.add h2).add h3
  have e : (fun m : ℕ => eis3 p r₁ r₂ m / (m : ℝ) ^ 2) = fun m : ℕ =>
      p * ((pointThree ^ m).re / (m : ℝ) ^ 2)
        + r₁ * (if 2 ∣ m then (1 / 3) ^ (m / 2) / (m : ℝ) ^ 2 else 0)
        + r₂ * (if 2 ∣ m then (-1 / 3) ^ (m / 2) / (m : ℝ) ^ 2 else 0) := by
    funext m
    simp only [eis3]
    split_ifs <;> ring
  rw [e]
  convert h using 1
  norm_num

/-- **Vectors of base `3^6` and length 12 from the point `e^(iπ/6)/√3`.** If `a_i = u(i)`
for `u = eis3 p r₁ r₂` (`1 ≤ i ≤ 12`), then
`P(2, 3^6, 12, a) = p Re Li_2(z₃) + r₁ Li_2(1/3)/4 + r₂ Li_2(-1/3)/4`. -/
theorem hasBaileyValueDeg_eis3 (p r₁ r₂ : ℝ) (a : Fin 12 → ℚ)
    (ha : ∀ i : Fin 12, eis3 p r₁ r₂ ((i : ℕ) + 1) = (a i : ℝ)) :
    HasBaileyValueDeg 2 3 6 12 a
      (p * (polylog 2 pointThree).re + r₁ * (polylogReal 2 (1 / 3) / 4)
        + r₂ * (polylogReal 2 (-1 / 3) / 4)) :=
  hasBaileyValueDeg_of_quasiperiodic two_ne_zero (by norm_num) (eis3_add_twelve p r₁ r₂) ha
    (hasSum_eis3 p r₁ r₂)

/-- One step of the recurrence `Re(z₃^(m+2)) = Re(z₃^(m+1)) - Re(z₃^m)/3`. -/
theorem pointThree_re_step {m : ℕ} {a b : ℝ} (ha : (pointThree ^ m).re = a)
    (hb : (pointThree ^ (m + 1)).re = b) : (pointThree ^ (m + 2)).re = b - a / 3 := by
  rw [pointThree_pow_re, ha, hb]

/-- The real parts of `z₃^m` for `m = 1, …, 12`. -/
theorem pointThree_pow_re_table :
    (pointThree ^ 1).re = 1 / 2 ∧ (pointThree ^ 2).re = 1 / 6 ∧ (pointThree ^ 3).re = 0 ∧
    (pointThree ^ 4).re = -1 / 18 ∧ (pointThree ^ 5).re = -1 / 18 ∧
    (pointThree ^ 6).re = -1 / 27 ∧ (pointThree ^ 7).re = -1 / 54 ∧
    (pointThree ^ 8).re = -1 / 162 ∧ (pointThree ^ 9).re = 0 ∧
    (pointThree ^ 10).re = 1 / 486 ∧ (pointThree ^ 11).re = 1 / 486 ∧
    (pointThree ^ 12).re = 1 / 729 := by
  have r0 : (pointThree ^ 0).re = 1 := by simp
  have r1 : (pointThree ^ 1).re = 1 / 2 := by rw [pow_one, pointThree_re]
  have r2 : (pointThree ^ 2).re = 1 / 6 := (pointThree_re_step r0 r1).trans (by norm_num)
  have r3 : (pointThree ^ 3).re = 0 := (pointThree_re_step r1 r2).trans (by norm_num)
  have r4 : (pointThree ^ 4).re = -1 / 18 := (pointThree_re_step r2 r3).trans (by norm_num)
  have r5 : (pointThree ^ 5).re = -1 / 18 := (pointThree_re_step r3 r4).trans (by norm_num)
  have r6 : (pointThree ^ 6).re = -1 / 27 := (pointThree_re_step r4 r5).trans (by norm_num)
  have r7 : (pointThree ^ 7).re = -1 / 54 := (pointThree_re_step r5 r6).trans (by norm_num)
  have r8 : (pointThree ^ 8).re = -1 / 162 := (pointThree_re_step r6 r7).trans (by norm_num)
  have r9 : (pointThree ^ 9).re = 0 := (pointThree_re_step r7 r8).trans (by norm_num)
  have r10 : (pointThree ^ 10).re = 1 / 486 := (pointThree_re_step r8 r9).trans (by norm_num)
  have r11 : (pointThree ^ 11).re = 1 / 486 := (pointThree_re_step r9 r10).trans (by norm_num)
  have r12 : (pointThree ^ 12).re = 1 / 729 := (pointThree_re_step r10 r11).trans (by norm_num)
  exact ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩

/-- **Formula (76)** of the Compendium (page 24):
`π² = 2/27 P(2, 3^6, 12, (243, -405, 0, -81, -27, -72, -9, -9, 0, -5, 1, 0))`. -/
theorem formula_76 : BaileyFormulaDeg (Real.pi ^ 2) (2 / 27) 2 3 6 12
    ![243, -405, 0, -81, -27, -72, -9, -9, 0, -5, 1, 0] := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := pointThree_pow_re_table
  refine (hasBaileyValueDeg_eis3 486 (-972) 486 _ fun i => ?_).formula ?_
  · fin_cases i <;>
      norm_num [eis3, pointThree_re, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12]
  · rw [polylog_two_pointThree_re]
    linear_combination (-9 : ℝ) * polylogReal_two_neg_third_eq

/-- **Formula (77)** of the Compendium (page 24):
`log² 3 = 1/3^6 P(2, 3^6, 12, (4374, -13122, 0, -2106, -486, -1944, -162, -234, 0, -162, 18,
-8))`. -/
theorem formula_77 : BaileyFormulaDeg (Real.log 3 ^ 2) (1 / 3 ^ 6) 2 3 6 12
    ![4374, -13122, 0, -2106, -486, -1944, -162, -234, 0, -162, 18, -8] := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := pointThree_pow_re_table
  refine (hasBaileyValueDeg_eis3 8748 (-29160) 14580 _ fun i => ?_).formula ?_
  · fin_cases i <;>
      norm_num [eis3, pointThree_re, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12]
  · rw [polylog_two_pointThree_re]
    linear_combination (-5 : ℝ) * polylogReal_two_neg_third_eq

end Compendium

end PiFormula
