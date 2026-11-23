import Pilean.Polylog.Dilog

/-!
# The complex dilogarithm: reflection formula and Landen's identity

`Li_2(z) = polylog 2 z` on the closed unit disc; `log` is the principal branch.

* `polylog_two_reflection`: `Li_2(z) + Li_2(1 - z) = π²/6 - log z · log (1 - z)` on the lens
  `‖z‖ < 1`, `‖1 - z‖ < 1` (the derivative of the difference vanishes on this convex open set;
  the constant is the value at `1/2`, from the real dilogarithm);
* `polylog_two_landen`: `Li_2(z) + Li_2(z / (z - 1)) = -(1/2) log² (1 - z)` for `‖z‖ ≤ 1`,
  `Re z ≤ 1/2` (derivative zero on `‖z‖ < 1`, `Re z < 1/2`; then continuity of `Li_2` on the
  closed disc). The image `z / (z - 1)` lies in the closed unit disc exactly when
  `Re z ≤ 1/2`, and on the unit circle when `Re z = 1/2`;
* on the line `Re z = 1/2`, where `1 - z = conj z`:
  `re_polylog_two_of_re_eq_half : Re Li_2(z) = π²/12 - (log² ‖z‖ + arg² z)/2`,
  `im_polylog_two_of_re_eq_half : Im Li_2(z) = -Im Li_2(z / (z - 1)) + log ‖z‖ · arg z`;
* `arg_eq_arctan_of_re_pos`: `arg z = arctan (Im z / Re z)` for `Re z > 0`.
-/

namespace PiFormula

namespace Polylog

open Complex

/-! ## 1. Elementary facts -/

/-- `‖z‖ < ‖z - 1‖` when `Re z < 1/2`. -/
theorem norm_lt_norm_sub_one {z : ℂ} (h : z.re < 1 / 2) : ‖z‖ < ‖z - 1‖ := by
  refine (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  nlinarith

/-- `‖z‖ ≤ ‖z - 1‖` when `Re z ≤ 1/2`. -/
theorem norm_le_norm_sub_one {z : ℂ} (h : z.re ≤ 1 / 2) : ‖z‖ ≤ ‖z - 1‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  nlinarith

/-- `arg z = arctan (Im z / Re z)` for `Re z > 0`. -/
theorem arg_eq_arctan_of_re_pos {z : ℂ} (h : 0 < z.re) : z.arg = Real.arctan (z.im / z.re) := by
  have h1 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h)
  rw [abs_lt] at h1
  rw [← Complex.tan_arg, Real.arctan_tan h1.1 h1.2]

/-! ## 2. The reflection formula -/

/-- The derivative of `Li_2(w) + Li_2(1 - w) + log w · log (1 - w)` vanishes on the lens
`‖w‖ < 1`, `‖1 - w‖ < 1`. -/
theorem hasDerivAt_reflection_complex_aux {z : ℂ} (hz : ‖z‖ < 1) (hz' : ‖1 - z‖ < 1) :
    HasDerivAt (fun w : ℂ => polylog 2 w + polylog 2 (1 - w)
      + Complex.log w * Complex.log (1 - w)) 0 z := by
  have hre1 : z.re < 1 := lt_of_le_of_lt (Complex.re_le_norm z) hz
  have hre0 : 0 < z.re := by
    have h := lt_of_le_of_lt (Complex.re_le_norm (1 - z)) hz'
    rw [Complex.sub_re, Complex.one_re] at h
    linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre0
    exact lt_irrefl _ hre0
  have h1z : 1 - z ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at h2
    linarith
  have hslit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.2 (Or.inl hre0)
  have hslit' : 1 - z ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hd : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := (hasDerivAt_id z).const_sub 1
  have e1 := hasDerivAt_dilog hz hz0
  have e2 : HasDerivAt (fun w : ℂ => polylog 2 (1 - w))
      (-Complex.log (1 - (1 - z)) / (1 - z) * -1) z :=
    HasDerivAt.comp (h₂ := polylog 2) (h := fun w : ℂ => 1 - w) z
      (hasDerivAt_dilog hz' h1z) hd
  have e3 : HasDerivAt (fun w : ℂ => Complex.log w * Complex.log (1 - w))
      (z⁻¹ * Complex.log (1 - z) + Complex.log z * (-1 / (1 - z))) z :=
    (Complex.hasStrictDerivAt_log hslit).hasDerivAt.fun_mul (hd.clog hslit')
  refine ((e1.fun_add e2).fun_add e3).congr_deriv ?_
  rw [show 1 - (1 - z) = z by ring]
  field_simp
  ring

/-- **The reflection formula** for the complex dilogarithm, on the lens `‖z‖ < 1`,
`‖1 - z‖ < 1`: `Li_2(z) + Li_2(1 - z) = π²/6 - log z · log (1 - z)`. -/
theorem polylog_two_reflection {z : ℂ} (hz : ‖z‖ < 1) (hz' : ‖1 - z‖ < 1) :
    polylog 2 z + polylog 2 (1 - z) =
      ((Real.pi ^ 2 / 6 : ℝ) : ℂ) - Complex.log z * Complex.log (1 - z) := by
  have hopen : IsOpen (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1) :=
    Metric.isOpen_ball.inter Metric.isOpen_ball
  have hconv : Convex ℝ (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).inter (convex_ball (1 : ℂ) 1)
  have hmem : ∀ w : ℂ, ‖w‖ < 1 → ‖1 - w‖ < 1 →
      w ∈ Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1 := by
    intro w hw hw'
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      exact hw
    · rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
      exact hw'
  have hhalf : ‖((1 / 2 : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos] <;> norm_num
  have e12 : (1 : ℂ) - ((1 / 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hhalf' : ‖(1 : ℂ) - ((1 / 2 : ℝ) : ℂ)‖ < 1 := by
    rw [e12]
    exact hhalf
  have hc := const_of_hasDerivAt_zero hopen hconv.isPreconnected
    (fun w hw => hasDerivAt_reflection_complex_aux
      (by simpa [Metric.mem_ball, dist_zero_right] using hw.1)
      (by simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hw.2))
    (hmem z hz hz') (hmem _ hhalf hhalf')
  have e2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [e12, polylog_ofReal, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 1 / 2),
    polylogReal_two_half, e2] at hc
  have e3 : (((Real.pi ^ 2 / 12 - Real.log 2 ^ 2 / 2 : ℝ) : ℂ)
      + ((Real.pi ^ 2 / 12 - Real.log 2 ^ 2 / 2 : ℝ) : ℂ)
      + ((-Real.log 2 : ℝ) : ℂ) * ((-Real.log 2 : ℝ) : ℂ)) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e3] at hc
  linear_combination hc

/-! ## 3. Landen's identity -/

/-- The derivative of `Li_2(w) + Li_2(w/(w-1)) + (1/2) log² (1 - w)` vanishes on the region
`‖w‖ < 1`, `Re w < 1/2`. -/
theorem hasDerivAt_landen_complex_aux {z : ℂ} (hz : ‖z‖ < 1) (hre : z.re < 1 / 2) :
    HasDerivAt (fun w : ℂ => polylog 2 w + polylog 2 (w / (w - 1))
      + 1 / 2 * Complex.log (1 - w) ^ 2) 0 z := by
  have hz1 : z - 1 ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at h2
    linarith
  have h1z : 1 - z ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at h2
    linarith
  have hy1 : ‖z / (z - 1)‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.2 hz1)]
    exact norm_lt_norm_sub_one hre
  have hslit : 1 - z ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hd : HasDerivAt (fun w : ℂ => w / (w - 1)) (-1 / (z - 1) ^ 2) z := by
    have h := (hasDerivAt_id z).fun_div ((hasDerivAt_id z).sub_const 1) hz1
    refine h.congr_deriv ?_
    simp only [id]
    ring
  have hL : HasDerivAt (fun w : ℂ => 1 / 2 * Complex.log (1 - w) ^ 2)
      (-Complex.log (1 - z) / (1 - z)) z := by
    have h := ((((hasDerivAt_id z).const_sub 1).clog hslit).fun_pow 2).const_mul (1 / 2 : ℂ)
    refine h.congr_deriv ?_
    simp only [id, Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 from rfl, pow_one]
    field_simp
  have hlog : Complex.log (1 - z / (z - 1)) = -Complex.log (1 - z) := by
    have e : 1 - z / (z - 1) = (1 - z)⁻¹ := by
      field_simp
      ring
    rw [e, Complex.log_inv _ (Complex.mem_slitPlane_iff_arg.1 hslit).1]
  have h1 := hasDerivAt_dilog_tsum hz
  have h2 : HasDerivAt (fun w : ℂ => polylog 2 (w / (w - 1)))
      ((∑' k : ℕ, (z / (z - 1)) ^ k / ((k : ℂ) + 1) ^ 1) * (-1 / (z - 1) ^ 2)) z :=
    HasDerivAt.comp (h₂ := polylog 2) (h := fun w : ℂ => w / (w - 1)) z
      (hasDerivAt_dilog_tsum hy1) hd
  refine ((h1.fun_add h2).fun_add hL).congr_deriv ?_
  by_cases hz0 : z = 0
  · rw [hz0, zero_div, tsum_zero_pow_div]
    norm_num
  · have hy0 : z / (z - 1) ≠ 0 := div_ne_zero hz0 hz1
    rw [tsum_pow_div_succ hz hz0, tsum_pow_div_succ hy1 hy0, hlog]
    field_simp
    ring

/-- **Landen's identity** for the complex dilogarithm:
`Li_2(z) + Li_2(z / (z - 1)) = -(1/2) log² (1 - z)` for `‖z‖ ≤ 1` and `Re z ≤ 1/2`. -/
theorem polylog_two_landen {z : ℂ} (hz : ‖z‖ ≤ 1) (hre : z.re ≤ 1 / 2) :
    polylog 2 z + polylog 2 (z / (z - 1)) = -(1 / 2) * Complex.log (1 - z) ^ 2 := by
  have hSopen : IsOpen (Metric.ball (0 : ℂ) 1 ∩ {w : ℂ | w.re < 1 / 2}) :=
    Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_re continuous_const)
  have hSconv : Convex ℝ (Metric.ball (0 : ℂ) 1 ∩ {w : ℂ | w.re < 1 / 2}) :=
    (convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_lt (1 / 2))
  have hopen : Set.EqOn (fun w : ℂ => polylog 2 w + polylog 2 (w / (w - 1))
      + 1 / 2 * Complex.log (1 - w) ^ 2) (fun _ => 0)
      (Metric.ball (0 : ℂ) 1 ∩ {w : ℂ | w.re < 1 / 2}) := by
    intro w hw
    have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 ∩ {w : ℂ | w.re < 1 / 2} := by
      refine ⟨Metric.mem_ball_self one_pos, ?_⟩
      change (0 : ℂ).re < 1 / 2
      rw [Complex.zero_re]
      norm_num
    have hc := const_of_hasDerivAt_zero hSopen hSconv.isPreconnected
      (fun y hy => hasDerivAt_landen_complex_aux
        (by simpa [Metric.mem_ball, dist_zero_right] using hy.1) hy.2) hw h0
    change polylog 2 w + polylog 2 (w / (w - 1)) + 1 / 2 * Complex.log (1 - w) ^ 2 = 0
    rw [hc]
    simp [polylog_zero]
  have hne : ∀ w ∈ Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | w.re ≤ 1 / 2}, w - 1 ≠ 0 := by
    intro w hw h
    have h1 : w.re ≤ 1 / 2 := hw.2
    have h2 := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at h2
    linarith
  have hcont : ContinuousOn (fun w : ℂ => polylog 2 w + polylog 2 (w / (w - 1))
      + 1 / 2 * Complex.log (1 - w) ^ 2)
      (Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | w.re ≤ 1 / 2}) := by
    have hL := continuousOn_polylog (s := 2) le_rfl
    have hdiv : ContinuousOn (fun w : ℂ => w / (w - 1))
        (Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | w.re ≤ 1 / 2}) := by
      have h0 : ContinuousOn (fun w : ℂ => w)
          (Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | w.re ≤ 1 / 2}) :=
        continuous_id.continuousOn
      have h1 : ContinuousOn (fun w : ℂ => w - 1)
          (Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | w.re ≤ 1 / 2}) :=
        (continuous_id.sub continuous_const).continuousOn
      exact h0.div₀ h1 hne
    have hmaps : Set.MapsTo (fun w : ℂ => w / (w - 1))
        (Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | w.re ≤ 1 / 2})
        (Metric.closedBall (0 : ℂ) 1) := by
      intro w hw
      have h1 : w.re ≤ 1 / 2 := hw.2
      rw [Metric.mem_closedBall, dist_zero_right, norm_div,
        div_le_one (norm_pos_iff.2 (hne w hw))]
      exact norm_le_norm_sub_one h1
    have hlog : ContinuousOn (fun w : ℂ => 1 / 2 * Complex.log (1 - w) ^ 2)
        (Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | w.re ≤ 1 / 2}) := by
      have h1c : ContinuousOn (fun w : ℂ => 1 - w)
          (Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | w.re ≤ 1 / 2}) :=
        (continuous_const.sub continuous_id).continuousOn
      refine continuousOn_const.mul (ContinuousOn.pow (ContinuousOn.clog h1c fun w hw => ?_) 2)
      have h1 : w.re ≤ 1 / 2 := hw.2
      refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
      rw [Complex.sub_re, Complex.one_re]
      linarith
    exact ((hL.mono Set.inter_subset_left).add (hL.comp hdiv hmaps)).add hlog
  have hsub : Metric.ball (0 : ℂ) 1 ∩ {w : ℂ | w.re < 1 / 2} ⊆
      Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | w.re ≤ 1 / 2} := fun w hw =>
    ⟨Metric.ball_subset_closedBall hw.1, (le_of_lt (show w.re < 1 / 2 from hw.2) : w.re ≤ 1 / 2)⟩
  have hclos : Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | w.re ≤ 1 / 2} ⊆
      closure (Metric.ball (0 : ℂ) 1 ∩ {w : ℂ | w.re < 1 / 2}) := by
    intro w hw
    have hw1 : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hw.1
    have hw2 : w.re ≤ 1 / 2 := hw.2
    have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ) * w) (nhdsWithin 1 (Set.Iio 1)) (nhds w) := by
      have hcts : Continuous fun t : ℝ => (t : ℂ) * w :=
        Complex.continuous_ofReal.mul continuous_const
      have h := (hcts.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
      simpa using h
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with t ht'
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht'.1]
      nlinarith [ht'.1, ht'.2, norm_nonneg w]
    · change ((t : ℂ) * w).re < 1 / 2
      rw [Complex.re_ofReal_mul]
      nlinarith [ht'.1, ht'.2]
  have hall := Set.EqOn.of_subset_closure hopen hcont continuousOn_const hsub hclos
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | w.re ≤ 1 / 2} :=
    ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hz, hre⟩
  have h := hall hzmem
  have h' : polylog 2 z + polylog 2 (z / (z - 1)) + 1 / 2 * Complex.log (1 - z) ^ 2 = 0 := h
  linear_combination h'

/-! ## 4. The line `Re z = 1/2` -/

/-- On the line `Re z = 1/2`: `1 - z = conj z`. -/
theorem one_sub_eq_conj {z : ℂ} (hre : z.re = 1 / 2) : 1 - z = (starRingEnd ℂ) z := by
  apply Complex.ext
  · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, hre]
    norm_num
  · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
    ring

/-- **The real part of `Li_2` on the line `Re z = 1/2`** inside the unit disc:
`Re Li_2(z) = π²/12 - (log² ‖z‖ + arg² z)/2`. -/
theorem re_polylog_two_of_re_eq_half {z : ℂ} (hz : ‖z‖ < 1) (hre : z.re = 1 / 2) :
    (polylog 2 z).re = Real.pi ^ 2 / 12 - (Real.log ‖z‖ ^ 2 + z.arg ^ 2) / 2 := by
  have h1 := one_sub_eq_conj hre
  have hz' : ‖1 - z‖ < 1 := by
    rw [h1, Complex.norm_conj]
    exact hz
  have hslit : z ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    rw [hre]
    norm_num
  have harg : z.arg ≠ Real.pi := (Complex.mem_slitPlane_iff_arg.1 hslit).1
  have h := polylog_two_reflection hz hz'
  rw [h1, polylog_conj, Complex.log_conj z harg] at h
  have h2 := congrArg Complex.re h
  rw [Complex.add_re, Complex.conj_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.log_re, Complex.log_im] at h2
  nlinarith [h2]

/-- **The imaginary part of `Li_2` on the line `Re z = 1/2`** inside the closed unit disc:
`Im Li_2(z) = -Im Li_2(z / (z - 1)) + log ‖z‖ · arg z`; the point `z / (z - 1)` is on the
unit circle. -/
theorem im_polylog_two_of_re_eq_half {z : ℂ} (hz : ‖z‖ ≤ 1) (hre : z.re = 1 / 2) :
    (polylog 2 z).im = -(polylog 2 (z / (z - 1))).im + Real.log ‖z‖ * z.arg := by
  have h1 := one_sub_eq_conj hre
  have hslit : z ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    rw [hre]
    norm_num
  have harg : z.arg ≠ Real.pi := (Complex.mem_slitPlane_iff_arg.1 hslit).1
  have h := polylog_two_landen hz hre.le
  rw [h1, Complex.log_conj z harg] at h
  have h2 := congrArg Complex.im h
  have e : (-(1 / 2) * (starRingEnd ℂ) (Complex.log z) ^ 2).im =
      Real.log ‖z‖ * z.arg := by
    have e1 : (-(1 / 2) * (starRingEnd ℂ) (Complex.log z) ^ 2) =
        ((-(1 / 2) : ℝ) : ℂ) * ((starRingEnd ℂ) (Complex.log z)
          * (starRingEnd ℂ) (Complex.log z)) := by
      push_cast
      ring
    rw [e1, Complex.im_ofReal_mul, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.log_re, Complex.log_im]
    ring
  rw [Complex.add_im, e] at h2
  linarith

end Polylog

end PiFormula
