module

public import Pilean.Polylog.Defs

/-!
# The polylogarithm: derivative on the open unit disc, continuity on the closed disc

* `hasDerivAt_polylog_succ`: for `‖z‖ < 1` the derivative of `Li_(s+1)` at `z` is
  `∑_{k ≥ 0} z^k / (k+1)^s` (term-by-term differentiation, `hasDerivAt_tsum_of_isPreconnected`);
* `mul_tsum_pow_div`: `z · ∑_{k ≥ 0} z^k / (k+1)^s = Li_s(z)`, so the derivative is
  `Li_s(z) / z` for `z ≠ 0` (`hasDerivAt_polylog_succ_of_ne_zero`);
* `polylog_one`: `Li_1(z) = -log (1 - z)` for `‖z‖ < 1`;
* `hasDerivAt_dilog`: the derivative of `Li_2` at `z ≠ 0`, `‖z‖ < 1`, is `-log (1 - z) / z`;
* `continuousOn_polylog`: `Li_s` is continuous on the closed unit disc for `s ≥ 2`;
* the same for the real polylogarithm: `hasDerivAt_polylogReal_succ`,
  `hasDerivAt_dilogReal`, `hasDerivAt_polylogReal_succ_zero` (the derivative at `0` is `1`),
  `continuousOn_polylogReal` (on `[-1, 1]`).
-/

@[expose] public section

namespace PiFormula

namespace Polylog

/-! ## 1. The derivative of the complex polylogarithm -/

/-- **Term-by-term differentiation.** For `‖z‖ < 1` the derivative of `Li_(s+1)` at `z` is
`∑_{k ≥ 0} z^k / (k+1)^s`. -/
theorem hasDerivAt_polylog_succ (s : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (polylog (s + 1)) (∑' k : ℕ, z ^ k / ((k : ℂ) + 1) ^ s) z := by
  obtain ⟨r, hzr, hr1⟩ : ∃ r : ℝ, ‖z‖ < r ∧ r < 1 := exists_between hz
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hzr.le
  have hu : Summable fun k : ℕ => r ^ k := summable_geometric_of_lt_one hr0 hr1
  have hg : ∀ (k : ℕ) (y : ℂ), y ∈ Metric.ball (0 : ℂ) r →
      HasDerivAt (fun y : ℂ => y ^ (k + 1) / ((k : ℂ) + 1) ^ (s + 1))
        (y ^ k / ((k : ℂ) + 1) ^ s) y := by
    intro k y _
    have hk : (k : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero k
    have h := (hasDerivAt_pow (k + 1) y).div_const (((k : ℂ) + 1) ^ (s + 1))
    convert h using 1
    push_cast
    field_simp
    ring
  have hg' : ∀ (k : ℕ) (y : ℂ), y ∈ Metric.ball (0 : ℂ) r →
      ‖y ^ k / ((k : ℂ) + 1) ^ s‖ ≤ r ^ k := by
    intro k y hy
    have hy' : ‖y‖ ≤ r := by
      rw [Metric.mem_ball, dist_zero_right] at hy
      exact hy.le
    have e : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
      rw [← Nat.cast_succ, Complex.norm_natCast, Nat.cast_succ]
    have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ s :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
    rw [norm_div, norm_pow, norm_pow, e]
    exact (div_le_self (pow_nonneg (norm_nonneg y) _) h1).trans
      (pow_le_pow_left₀ (norm_nonneg y) hy' k)
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self (lt_of_le_of_lt
    (norm_nonneg z) hzr)
  have hz' : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hzr
  have hs0 : Summable fun k : ℕ => (0 : ℂ) ^ (k + 1) / ((k : ℂ) + 1) ^ (s + 1) :=
    summable_polylog_term_of_lt (s + 1) (by simp)
  have key : HasDerivAt (fun w : ℂ => ∑' k : ℕ, w ^ (k + 1) / ((k : ℂ) + 1) ^ (s + 1))
      (∑' k : ℕ, z ^ k / ((k : ℂ) + 1) ^ s) z :=
    hasDerivAt_tsum_of_isPreconnected (t := Metric.ball (0 : ℂ) r) (y₀ := 0)
      (g := fun (k : ℕ) (w : ℂ) => w ^ (k + 1) / ((k : ℂ) + 1) ^ (s + 1))
      (g' := fun (k : ℕ) (w : ℂ) => w ^ k / ((k : ℂ) + 1) ^ s) hu Metric.isOpen_ball
      (convex_ball (0 : ℂ) r).isPreconnected hg hg' h0 hs0 hz'
  exact key

/-- `z · ∑_{k ≥ 0} z^k / (k+1)^s = Li_s(z)`. -/
theorem mul_tsum_pow_div (s : ℕ) (z : ℂ) :
    z * ∑' k : ℕ, z ^ k / ((k : ℂ) + 1) ^ s = polylog s z := by
  rw [polylog, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [pow_succ]
  ring

/-- For `0 < ‖z‖ < 1` the derivative of `Li_(s+1)` at `z` is `Li_s(z) / z`. -/
theorem hasDerivAt_polylog_succ_of_ne_zero (s : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasDerivAt (polylog (s + 1)) (polylog s z / z) z := by
  have h := hasDerivAt_polylog_succ s hz
  rwa [← mul_tsum_pow_div s z, mul_div_cancel_left₀ _ hz0]

/-- `Li_1(z) = -log (1 - z)` for `‖z‖ < 1`. -/
theorem polylog_one {z : ℂ} (hz : ‖z‖ < 1) : polylog 1 z = -Complex.log (1 - z) := by
  have h := hasSum_polylog_nat_of_lt (s := 1) one_ne_zero hz
  simp only [pow_one] at h
  exact h.unique (Complex.hasSum_taylorSeries_neg_log hz)

/-- **The derivative of the dilogarithm**: `-log (1 - z) / z`, for `0 < ‖z‖ < 1`. -/
theorem hasDerivAt_dilog {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasDerivAt (polylog 2) (-Complex.log (1 - z) / z) z := by
  have h := hasDerivAt_polylog_succ_of_ne_zero 1 hz hz0
  rwa [polylog_one hz] at h

/-- The derivative series of the dilogarithm: `∑_{k ≥ 0} z^k / (k+1) = -log (1 - z) / z` for
`0 < ‖z‖ < 1`. -/
theorem tsum_pow_div_succ {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    (∑' k : ℕ, z ^ k / ((k : ℂ) + 1) ^ 1) = -Complex.log (1 - z) / z := by
  rw [← polylog_one hz, ← mul_tsum_pow_div 1 z, mul_div_cancel_left₀ _ hz0]

/-- The derivative series at `0` is `1`. -/
theorem tsum_zero_pow_div (s : ℕ) : (∑' k : ℕ, (0 : ℂ) ^ k / ((k : ℂ) + 1) ^ s) = 1 := by
  rw [tsum_eq_single 0 fun k hk => by simp [hk]]
  simp

/-- The derivative of the dilogarithm at any point of the open unit disc, as a series. -/
theorem hasDerivAt_dilog_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (polylog 2) (∑' k : ℕ, z ^ k / ((k : ℂ) + 1) ^ 1) z :=
  hasDerivAt_polylog_succ 1 hz

/-- `Li_s` is continuous on the closed unit disc, for `s ≥ 2`. -/
theorem continuousOn_polylog {s : ℕ} (hs : 2 ≤ s) :
    ContinuousOn (polylog s) (Metric.closedBall (0 : ℂ) 1) := by
  refine continuousOn_tsum (u := fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) (fun k => ?_)
    (summable_one_div_succ_pow hs) fun k z hz => ?_
  · exact ((continuous_pow (k + 1)).div_const _).continuousOn
  · rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact norm_polylog_term_le s hz k

/-! ## 2. The real polylogarithm -/

/-- For `|x| < 1` the derivative of the real `Li_(s+1)` at `x` is `∑_{k ≥ 0} x^k / (k+1)^s`. -/
theorem hasDerivAt_polylogReal_succ (s : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (polylogReal (s + 1)) (∑' k : ℕ, x ^ k / ((k : ℝ) + 1) ^ s) x := by
  have h := (hasDerivAt_polylog_succ s (z := (x : ℂ))
    (by rwa [Complex.norm_real, Real.norm_eq_abs])).real_of_complex
  have e1 : (fun y : ℝ => (polylog (s + 1) (y : ℂ)).re) = polylogReal (s + 1) :=
    funext fun y => (polylogReal_eq_re (s + 1) y).symm
  have e2 : (∑' k : ℕ, (x : ℂ) ^ k / ((k : ℂ) + 1) ^ s) =
      ((∑' k : ℕ, x ^ k / ((k : ℝ) + 1) ^ s : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun k => ?_
    simp
  rwa [e1, e2, Complex.ofReal_re] at h

/-- `x · ∑_{k ≥ 0} x^k / (k+1)^s = Li_s(x)`. -/
theorem mul_tsum_pow_div_real (s : ℕ) (x : ℝ) :
    x * ∑' k : ℕ, x ^ k / ((k : ℝ) + 1) ^ s = polylogReal s x := by
  rw [polylogReal, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [pow_succ]
  ring

/-- The real `Li_1(x) = -log (1 - x)` for `|x| < 1`. -/
theorem polylogReal_one {x : ℝ} (hx : |x| < 1) : polylogReal 1 x = -Real.log (1 - x) := by
  have h := hasSum_polylogReal_of_lt 1 hx
  simp only [pow_one] at h
  exact h.unique (Real.hasSum_pow_div_log_of_abs_lt_one hx)

/-- **The derivative of the real dilogarithm**: `-log (1 - x) / x`, for `0 < |x| < 1`. -/
theorem hasDerivAt_dilogReal {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasDerivAt (polylogReal 2) (-Real.log (1 - x) / x) x := by
  have h := hasDerivAt_polylogReal_succ 1 hx
  rwa [← polylogReal_one hx, ← mul_tsum_pow_div_real 1 x, mul_div_cancel_left₀ _ hx0]

/-- The derivative series of the real dilogarithm: `∑_{k ≥ 0} x^k / (k+1) = -log (1 - x) / x`
for `0 < |x| < 1`. -/
theorem tsum_pow_div_succ_real {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    (∑' k : ℕ, x ^ k / ((k : ℝ) + 1) ^ 1) = -Real.log (1 - x) / x := by
  rw [← polylogReal_one hx, ← mul_tsum_pow_div_real 1 x, mul_div_cancel_left₀ _ hx0]

/-- The real derivative series at `0` is `1`. -/
theorem tsum_zero_pow_div_real (s : ℕ) : (∑' k : ℕ, (0 : ℝ) ^ k / ((k : ℝ) + 1) ^ s) = 1 := by
  rw [tsum_eq_single 0 fun k hk => by simp [hk]]
  simp

/-- The derivative of the real dilogarithm at any point of `(-1, 1)`, as a series. -/
theorem hasDerivAt_dilogReal_tsum {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (polylogReal 2) (∑' k : ℕ, x ^ k / ((k : ℝ) + 1) ^ 1) x :=
  hasDerivAt_polylogReal_succ 1 hx

/-- The derivative of the real `Li_(s+1)` at `0` is `1`. -/
theorem hasDerivAt_polylogReal_succ_zero (s : ℕ) : HasDerivAt (polylogReal (s + 1)) 1 0 := by
  have h := hasDerivAt_polylogReal_succ s (x := 0) (by simp)
  rwa [tsum_zero_pow_div_real] at h

/-- The real `Li_s` is continuous on `[-1, 1]`, for `s ≥ 2`. -/
theorem continuousOn_polylogReal {s : ℕ} (hs : 2 ≤ s) :
    ContinuousOn (polylogReal s) (Set.Icc (-1 : ℝ) 1) := by
  refine continuousOn_tsum (u := fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) (fun k => ?_)
    (summable_one_div_succ_pow hs) fun k x hx => ?_
  · exact ((continuous_pow (k + 1)).div_const _).continuousOn
  · have hx1 : |x| ≤ 1 := abs_le.2 ⟨hx.1, hx.2⟩
    have hp : (0 : ℝ) < ((k : ℝ) + 1) ^ s := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hp]
    exact div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg x) hx1) hp.le

end Polylog

end PiFormula
