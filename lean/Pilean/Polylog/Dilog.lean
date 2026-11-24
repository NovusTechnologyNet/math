/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Polylog.Deriv

/-!
# The real dilogarithm: Landen's identity, the reflection formula, special values

`Li_2(x) = polylogReal 2 x = ∑_{k ≥ 1} x^k / k^2` for `-1 ≤ x ≤ 1`.

* `polylogReal_two_landen`: Landen's identity
  `Li_2(x) + Li_2(x / (x - 1)) = -(1/2) log² (1 - x)` for `-1 ≤ x ≤ 1/2`
  (the derivative of the difference vanishes on `(-1, 1/2)`; both sides are continuous on the
  closed interval);
* `polylogReal_two_neg_one`: `Li_2(-1) = -π²/12`;
* `polylogReal_two_half`: `Li_2(1/2) = π²/12 - (log 2)²/2`;
* `polylogReal_two_reflection`: Euler's reflection formula
  `Li_2(x) + Li_2(1 - x) = π²/6 - log x · log (1 - x)` for `0 < x < 1`;
* the ladder: `polylogReal_two_neg_half`, `polylogReal_two_quarter`,
  `polylogReal_two_neg_third`, `polylogReal_two_ninth`, `polylogReal_two_neg_eighth`,
  `polylogReal_two_sixty_fourth` (Landen's identity and duplication at `1/2`, `1/3`, `1/8`),
  and their consequences
  `dilog_ladder_two : 6 Li_2(1/2) - 6 Li_2(1/4) - 2 Li_2(1/8) + Li_2(1/64) = π²/6`,
  `dilog_ladder_three : Li_2(1/9) = 6 Li_2(1/3) - π²/3 + (log 3)²`,
  `polylogReal_two_neg_third_eq : Li_2(-1/3) = 2 Li_2(1/3) - π²/6 + (log 3)²/2`.
-/

@[expose] public section

namespace PiFormula

namespace Polylog

/-- A function with derivative `0` at every point of an open preconnected set is constant on
that set (real or complex variable). -/
theorem const_of_hasDerivAt_zero {𝕜 : Type*} [RCLike 𝕜] {f : 𝕜 → 𝕜} {s : Set 𝕜}
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : ∀ x ∈ s, HasDerivAt f 0 x) {x y : 𝕜}
    (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  hs.is_const_of_deriv_eq_zero hs'
    (fun z hz => (hf z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hf z hz).deriv) hx hy

/-! ## 1. Landen's identity -/

/-- The derivative of `Li_2(t) + Li_2(t/(t-1)) + (1/2) log² (1 - t)` vanishes on
`(-1, 1/2)`. -/
theorem hasDerivAt_landen_aux {x : ℝ} (hx1 : -1 < x) (hx2 : x < 1 / 2) :
    HasDerivAt (fun t : ℝ => polylogReal 2 t + polylogReal 2 (t / (t - 1))
      + 1 / 2 * Real.log (1 - t) ^ 2) 0 x := by
  have hneg : x - 1 < 0 := by linarith
  have hx1' : x - 1 ≠ 0 := hneg.ne
  have h1x : 1 - x ≠ 0 := by
    intro h
    linarith
  have habs : |x| < 1 := abs_lt.2 ⟨hx1, by linarith⟩
  have hy1 : |x / (x - 1)| < 1 := by
    refine abs_lt.2 ⟨?_, ?_⟩
    · rw [lt_div_iff_of_neg hneg]
      linarith
    · rw [div_lt_iff_of_neg hneg]
      linarith
  have hd : HasDerivAt (fun t : ℝ => t / (t - 1)) (-1 / (x - 1) ^ 2) x := by
    have h := (hasDerivAt_id x).fun_div ((hasDerivAt_id x).sub_const 1) hx1'
    refine h.congr_deriv ?_
    simp only [id]
    ring
  have hL : HasDerivAt (fun t : ℝ => 1 / 2 * Real.log (1 - t) ^ 2)
      (-Real.log (1 - x) / (1 - x)) x := by
    have h := ((((hasDerivAt_id x).const_sub 1).log h1x).fun_pow 2).const_mul (1 / 2 : ℝ)
    refine h.congr_deriv ?_
    simp only [id, Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 from rfl, pow_one]
    field_simp
  have hlog : Real.log (1 - x / (x - 1)) = -Real.log (1 - x) := by
    have e : 1 - x / (x - 1) = (1 - x)⁻¹ := by
      field_simp
      ring
    rw [e, Real.log_inv]
  have h1 := hasDerivAt_dilogReal_tsum habs
  have h2 : HasDerivAt (fun t : ℝ => polylogReal 2 (t / (t - 1)))
      ((∑' k : ℕ, (x / (x - 1)) ^ k / ((k : ℝ) + 1) ^ 1) * (-1 / (x - 1) ^ 2)) x :=
    HasDerivAt.comp (h₂ := polylogReal 2) (h := fun t : ℝ => t / (t - 1)) x
      (hasDerivAt_dilogReal_tsum hy1) hd
  refine ((h1.fun_add h2).fun_add hL).congr_deriv ?_
  by_cases hx0 : x = 0
  · rw [hx0, zero_div, tsum_zero_pow_div_real]
    norm_num
  · have hy0 : x / (x - 1) ≠ 0 := div_ne_zero hx0 hx1'
    rw [tsum_pow_div_succ_real habs hx0, tsum_pow_div_succ_real hy1 hy0, hlog]
    field_simp
    ring

/-- **Landen's identity** for the real dilogarithm:
`Li_2(x) + Li_2(x / (x - 1)) = -(1/2) log² (1 - x)` for `-1 ≤ x ≤ 1/2`. -/
theorem polylogReal_two_landen {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1 / 2) :
    polylogReal 2 x + polylogReal 2 (x / (x - 1)) = -(1 / 2) * Real.log (1 - x) ^ 2 := by
  have hopen : Set.EqOn (fun t : ℝ => polylogReal 2 t + polylogReal 2 (t / (t - 1))
      + 1 / 2 * Real.log (1 - t) ^ 2) (fun _ => 0) (Set.Ioo (-1 : ℝ) (1 / 2)) := by
    intro t ht
    have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) (1 / 2) := by
      constructor <;> norm_num
    have hc := const_of_hasDerivAt_zero isOpen_Ioo (convex_Ioo (-1 : ℝ) (1 / 2)).isPreconnected
      (fun y hy => hasDerivAt_landen_aux hy.1 hy.2) ht h0
    change polylogReal 2 t + polylogReal 2 (t / (t - 1)) + 1 / 2 * Real.log (1 - t) ^ 2 = 0
    rw [hc]
    simp [polylogReal_zero]
  have hcont : ContinuousOn (fun t : ℝ => polylogReal 2 t + polylogReal 2 (t / (t - 1))
      + 1 / 2 * Real.log (1 - t) ^ 2) (Set.Icc (-1 : ℝ) (1 / 2)) := by
    have hL := continuousOn_polylogReal (s := 2) le_rfl
    have hsub : Set.Icc (-1 : ℝ) (1 / 2) ⊆ Set.Icc (-1 : ℝ) 1 :=
      Set.Icc_subset_Icc_right (by norm_num)
    have hdiv : ContinuousOn (fun t : ℝ => t / (t - 1)) (Set.Icc (-1 : ℝ) (1 / 2)) := by
      refine continuousOn_id.div (continuousOn_id.sub continuousOn_const) fun t ht h => ?_
      have := ht.2
      have h' : t - 1 = 0 := h
      linarith
    have hmaps : Set.MapsTo (fun t : ℝ => t / (t - 1)) (Set.Icc (-1 : ℝ) (1 / 2))
        (Set.Icc (-1 : ℝ) 1) := by
      intro t ht
      have hneg : t - 1 < 0 := by linarith [ht.2]
      constructor
      · rw [le_div_iff_of_neg hneg]
        linarith [ht.2]
      · rw [div_le_iff_of_neg hneg]
        linarith
    have hlog : ContinuousOn (fun t : ℝ => 1 / 2 * Real.log (1 - t) ^ 2)
        (Set.Icc (-1 : ℝ) (1 / 2)) := by
      refine continuousOn_const.mul (ContinuousOn.pow (ContinuousOn.log
        (continuousOn_const.sub continuousOn_id) fun t ht h => ?_) 2)
      have := ht.2
      have h' : 1 - t = 0 := h
      linarith
    exact ((hL.mono hsub).add (hL.comp hdiv hmaps)).add hlog
  have hall := Set.EqOn.of_subset_closure hopen hcont continuousOn_const
    Set.Ioo_subset_Icc_self (closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1 / 2)).ge
  have h := hall ⟨hx1, hx2⟩
  simp only at h
  linarith

/-! ## 2. The values at `-1` and `1/2` -/

/-- `Li_2(-1) = -π²/12`. -/
theorem polylogReal_two_neg_one : polylogReal 2 (-1) = -(Real.pi ^ 2 / 12) := by
  have h := polylogReal_two_sq (x := 1) (by norm_num)
  rw [one_pow, polylogReal_two_one] at h
  linarith

/-- **`Li_2(1/2) = π²/12 - (log 2)²/2`.** -/
theorem polylogReal_two_half :
    polylogReal 2 (1 / 2) = Real.pi ^ 2 / 12 - Real.log 2 ^ 2 / 2 := by
  have h := polylogReal_two_landen (x := -1) le_rfl (by norm_num)
  have e1 : (-1 : ℝ) / (-1 - 1) = 1 / 2 := by norm_num
  have e2 : (1 : ℝ) - -1 = 2 := by norm_num
  rw [e1, e2, polylogReal_two_neg_one] at h
  linarith

/-! ## 3. The reflection formula -/

/-- The derivative of `Li_2(t) + Li_2(1 - t) + log t · log (1 - t)` vanishes on `(0, 1)`. -/
theorem hasDerivAt_reflection_aux {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    HasDerivAt (fun t : ℝ => polylogReal 2 t + polylogReal 2 (1 - t)
      + Real.log t * Real.log (1 - t)) 0 x := by
  have hx0 : x ≠ 0 := h0.ne'
  have h1x : 1 - x ≠ 0 := by
    intro h
    linarith
  have habs : |x| < 1 := abs_lt.2 ⟨by linarith, h1⟩
  have habs' : |1 - x| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
  have hd : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := (hasDerivAt_id x).const_sub 1
  have e1 := hasDerivAt_dilogReal habs hx0
  have e2 : HasDerivAt (fun t : ℝ => polylogReal 2 (1 - t))
      (-Real.log (1 - (1 - x)) / (1 - x) * -1) x :=
    HasDerivAt.comp (h₂ := polylogReal 2) (h := fun t : ℝ => 1 - t) x
      (hasDerivAt_dilogReal habs' h1x) hd
  have e3 : HasDerivAt (fun t : ℝ => Real.log t * Real.log (1 - t))
      (x⁻¹ * Real.log (1 - x) + Real.log x * (-1 / (1 - x))) x :=
    (Real.hasDerivAt_log hx0).fun_mul (hd.log h1x)
  refine ((e1.fun_add e2).fun_add e3).congr_deriv ?_
  rw [show 1 - (1 - x) = x by ring]
  field_simp
  ring

/-- **Euler's reflection formula** for the dilogarithm:
`Li_2(x) + Li_2(1 - x) = π²/6 - log x · log (1 - x)` for `0 < x < 1`. -/
theorem polylogReal_two_reflection {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    polylogReal 2 x + polylogReal 2 (1 - x) =
      Real.pi ^ 2 / 6 - Real.log x * Real.log (1 - x) := by
  have hmem : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hc := const_of_hasDerivAt_zero isOpen_Ioo (convex_Ioo (0 : ℝ) 1).isPreconnected
    (fun y hy => hasDerivAt_reflection_aux hy.1 hy.2) (show x ∈ Set.Ioo (0 : ℝ) 1 from ⟨h0, h1⟩)
    hmem
  have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have e2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [e, polylogReal_two_half, e2] at hc
  linear_combination hc

/-! ## 4. The ladder at `1/2`, `1/3`, `1/8` -/

/-- `Li_2(-1/2) = -Li_2(1/3) - (log 3 - log 2)²/2` (Landen's identity at `-1/2`). -/
theorem polylogReal_two_neg_half :
    polylogReal 2 (-1 / 2) = -polylogReal 2 (1 / 3) - (Real.log 3 - Real.log 2) ^ 2 / 2 := by
  have h := polylogReal_two_landen (x := -1 / 2) (by norm_num) (by norm_num)
  have e1 : (-1 / 2 : ℝ) / (-1 / 2 - 1) = 1 / 3 := by norm_num
  have e2 : Real.log (1 - -1 / 2 : ℝ) = Real.log 3 - Real.log 2 := by
    rw [show (1 - -1 / 2 : ℝ) = 3 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [e1, e2] at h
  linarith

/-- `Li_2(1/4) = 2 Li_2(1/2) + 2 Li_2(-1/2)` (duplication). -/
theorem polylogReal_two_quarter :
    polylogReal 2 (1 / 4) = 2 * polylogReal 2 (1 / 2) + 2 * polylogReal 2 (-1 / 2) := by
  have h := polylogReal_two_sq (x := 1 / 2) (by rw [abs_of_pos] <;> norm_num)
  rw [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num, show -((1 : ℝ) / 2) = -1 / 2 by norm_num] at h
  linarith

/-- `Li_2(-1/3) = -Li_2(1/4) - (2 log 2 - log 3)²/2` (Landen's identity at `-1/3`). -/
theorem polylogReal_two_neg_third :
    polylogReal 2 (-1 / 3) =
      -polylogReal 2 (1 / 4) - (2 * Real.log 2 - Real.log 3) ^ 2 / 2 := by
  have h := polylogReal_two_landen (x := -1 / 3) (by norm_num) (by norm_num)
  have e1 : (-1 / 3 : ℝ) / (-1 / 3 - 1) = 1 / 4 := by norm_num
  have e2 : Real.log (1 - -1 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
    rw [show (1 - -1 / 3 : ℝ) = 2 ^ 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  rw [e1, e2] at h
  linarith

/-- `Li_2(1/9) = 2 Li_2(1/3) + 2 Li_2(-1/3)` (duplication). -/
theorem polylogReal_two_ninth :
    polylogReal 2 (1 / 9) = 2 * polylogReal 2 (1 / 3) + 2 * polylogReal 2 (-1 / 3) := by
  have h := polylogReal_two_sq (x := 1 / 3) (by rw [abs_of_pos] <;> norm_num)
  rw [show ((1 : ℝ) / 3) ^ 2 = 1 / 9 by norm_num, show -((1 : ℝ) / 3) = -1 / 3 by norm_num] at h
  linarith

/-- `Li_2(-1/8) = -Li_2(1/9) - (2 log 3 - 3 log 2)²/2` (Landen's identity at `-1/8`). -/
theorem polylogReal_two_neg_eighth :
    polylogReal 2 (-1 / 8) =
      -polylogReal 2 (1 / 9) - (2 * Real.log 3 - 3 * Real.log 2) ^ 2 / 2 := by
  have h := polylogReal_two_landen (x := -1 / 8) (by norm_num) (by norm_num)
  have e1 : (-1 / 8 : ℝ) / (-1 / 8 - 1) = 1 / 9 := by norm_num
  have e2 : Real.log (1 - -1 / 8 : ℝ) = 2 * Real.log 3 - 3 * Real.log 2 := by
    rw [show (1 - -1 / 8 : ℝ) = 3 ^ 2 / 2 ^ 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [e1, e2] at h
  linarith

/-- `Li_2(1/64) = 2 Li_2(1/8) + 2 Li_2(-1/8)` (duplication). -/
theorem polylogReal_two_sixty_fourth :
    polylogReal 2 (1 / 64) = 2 * polylogReal 2 (1 / 8) + 2 * polylogReal 2 (-1 / 8) := by
  have h := polylogReal_two_sq (x := 1 / 8) (by rw [abs_of_pos] <;> norm_num)
  rw [show ((1 : ℝ) / 8) ^ 2 = 1 / 64 by norm_num, show -((1 : ℝ) / 8) = -1 / 8 by norm_num] at h
  linarith

/-- **The dilogarithm ladder of base 2**:
`6 Li_2(1/2) - 6 Li_2(1/4) - 2 Li_2(1/8) + Li_2(1/64) = π²/6`. -/
theorem dilog_ladder_two :
    6 * polylogReal 2 (1 / 2) - 6 * polylogReal 2 (1 / 4) - 2 * polylogReal 2 (1 / 8)
      + polylogReal 2 (1 / 64) = Real.pi ^ 2 / 6 := by
  linear_combination polylogReal_two_sixty_fourth + 2 * polylogReal_two_neg_eighth
    - 2 * polylogReal_two_ninth - 4 * polylogReal_two_neg_third - 4 * polylogReal_two_neg_half
    - 2 * polylogReal_two_quarter + 2 * polylogReal_two_half

/-- **The dilogarithm ladder of base 3**: `Li_2(1/9) = 6 Li_2(1/3) - π²/3 + (log 3)²`. -/
theorem dilog_ladder_three :
    polylogReal 2 (1 / 9) = 6 * polylogReal 2 (1 / 3) - Real.pi ^ 2 / 3 + Real.log 3 ^ 2 := by
  linear_combination polylogReal_two_ninth + 2 * polylogReal_two_neg_third
    - 2 * polylogReal_two_quarter - 4 * polylogReal_two_neg_half - 4 * polylogReal_two_half

/-- `Li_2(-1/3) = 2 Li_2(1/3) - π²/6 + (log 3)²/2`. -/
theorem polylogReal_two_neg_third_eq :
    polylogReal 2 (-1 / 3) =
      2 * polylogReal 2 (1 / 3) - Real.pi ^ 2 / 6 + Real.log 3 ^ 2 / 2 := by
  linear_combination polylogReal_two_neg_third - polylogReal_two_quarter
    - 2 * polylogReal_two_neg_half - 2 * polylogReal_two_half

end Polylog

end PiFormula
