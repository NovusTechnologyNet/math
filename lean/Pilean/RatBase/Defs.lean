module

public import Pilean.BaseB.BaileyForm

/-!
# BBP-type series in a rational base: the setting

A degree-1 BBP-type series of the rational base `p/q` is, in Bailey's notation,

  `P(1, (p/q)^B, N, A) = ∑_{j ≥ 0} (q/p)^(Bj) ∑_{i=1}^N a_i / (Nj + i)`.

`baileyBlockRat p q B N a j` is its `j`-th block, written exactly as this double sum; `a i`
(`i : Fin N`) is `a_{i+1}`. For `q = 1` it is `BaseB.baileyBlock` (`baileyBlockRat_one`).

The pattern form: `seriesTermRat p q ρ k = ρ(k) (q/p)^⌊k/2⌋ / k`, the term of the series of a
rational pattern `ρ` with the weights `(q/p)^⌊k/2⌋`. With `x = √(q/p)` this is
`g(k) x^k / k` for the pattern `g(k) = ρ(k) √(p/q)^(k mod 2)` (`seriesTermRat_eq_sqrt`).

Tools:

* `hasSum_im_pow_div`: `∑_{k ≥ 1} Im(w^k) / k = arctan (Im w / (1 - Re w))` for `‖w‖ < 1`
  (the imaginary part of `-Log(1 - w)`);
* `hasSum_baileyBlockRat_of_pattern`: the series of a pattern of period `N = 2B`, cut into
  blocks of length `N`, is `P(1, (p/q)^B, N, A)` with `a_i = ρ(i) (q/p)^⌊i/2⌋`.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace RatBase

/-- Block `j` of a degree-1 BBP-type series of the rational base `p/q`:
`(q/p)^(B j) ∑_{i=1}^{N} a_i / (N j + i)`. -/
noncomputable def baileyBlockRat (p q B N : ℕ) (a : Fin N → ℚ) (j : ℕ) : ℝ :=
  ∑ i : Fin N, (a i : ℝ) * ((q : ℝ) / (p : ℝ)) ^ (B * j) / ((N * j + i + 1 : ℕ) : ℝ)

/-- For `q = 1` this is Bailey's block in the integer base `p`. -/
theorem baileyBlockRat_one (p B N : ℕ) (a : Fin N → ℚ) :
    baileyBlockRat p 1 B N a = BaseB.baileyBlock p B N a := by
  funext j
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_one, one_div, inv_pow, ← div_eq_mul_inv]

/-- The term `ρ(k) (q/p)^⌊k/2⌋ / k` of the series of the pattern `ρ` in the base `p/q`. -/
noncomputable def seriesTermRat (p q : ℕ) (ρ : ℕ → ℚ) (k : ℕ) : ℝ :=
  (ρ k : ℝ) * ((q : ℝ) / (p : ℝ)) ^ (k / 2) / (k : ℝ)

theorem seriesTermRat_at_zero (p q : ℕ) (ρ : ℕ → ℚ) : seriesTermRat p q ρ 0 = 0 := by
  simp [seriesTermRat]

/-- For `q = 1` this is the term of the class `F_p`. -/
theorem seriesTermRat_one (p : ℕ) (ρ : ℕ → ℚ) :
    seriesTermRat p 1 ρ = BaseB.seriesTermBN p 2 ρ := by
  funext k
  rw [seriesTermRat, BaseB.seriesTermBN, Nat.cast_one, one_div, inv_pow, ← div_eq_mul_inv]

/-- With `x = √(q/p)`, the term is `g(k) x^k / k` for the pattern
`g(k) = ρ(k) √(p/q)^(k mod 2)`. -/
theorem seriesTermRat_eq_sqrt {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (ρ : ℕ → ℚ) (k : ℕ) :
    seriesTermRat p q ρ k = (ρ k : ℝ) * Real.sqrt ((p : ℝ) / q) ^ (k % 2) *
      Real.sqrt ((q : ℝ) / p) ^ k / (k : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : Real.sqrt ((q : ℝ) / p) ^ 2 = (q : ℝ) / p := Real.sq_sqrt (by positivity)
  have h2 : Real.sqrt ((p : ℝ) / q) * Real.sqrt ((q : ℝ) / p) = 1 := by
    rw [← Real.sqrt_mul (by positivity), div_mul_div_cancel₀ hq'.ne', div_self hp'.ne',
      Real.sqrt_one]
  have h3 : Real.sqrt ((q : ℝ) / p) ^ k =
      ((q : ℝ) / p) ^ (k / 2) * Real.sqrt ((q : ℝ) / p) ^ (k % 2) := by
    conv_lhs => rw [← Nat.div_add_mod k 2]
    rw [pow_add, pow_mul, h1]
  have h4 : Real.sqrt ((p : ℝ) / q) ^ (k % 2) * Real.sqrt ((q : ℝ) / p) ^ (k % 2) = 1 := by
    rw [← mul_pow, h2, one_pow]
  rw [seriesTermRat, h3]
  linear_combination (-(ρ k : ℝ) * ((q : ℝ) / p) ^ (k / 2) / k) * h4

theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-! ## 1. The imaginary part of the logarithm series -/

/-- `∑_{k ≥ 1} Im(w^k) / k = arctan (Im w / (1 - Re w))` for `‖w‖ < 1`: the imaginary part of
`∑_{k ≥ 1} w^k / k = -Log(1 - w)`. The term at `k = 0` is `0`. -/
theorem hasSum_im_pow_div {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun k : ℕ => (w ^ k).im / (k : ℝ)) (Real.arctan (w.im / (1 - w.re))) := by
  have hre : 0 < (1 - w).re := by
    rw [sub_re, one_re]
    linarith [w.re_le_norm]
  have harg : (1 - w).arg = -Real.arctan (w.im / (1 - w.re)) := by
    have h1 := abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
    rw [abs_lt] at h1
    rw [← Real.arctan_neg, ← Real.arctan_tan h1.1 h1.2, tan_arg, sub_re, sub_im, one_re, one_im,
      zero_sub, neg_div]
  have h := ((Complex.hasSum_iff _ _).1 (hasSum_taylorSeries_neg_log hw)).2
  rw [neg_im, log_im, harg, neg_neg] at h
  refine h.congr_fun fun k => ?_
  rw [div_natCast_im]

/-! ## 2. From the pattern to Bailey's blocks -/

/-- **A pattern series in blocks.** If the rational pattern `ρ` has the even period `N = 2B`,
the series `∑_{k ≥ 1} ρ(k) (q/p)^⌊k/2⌋ / k` is `P(1, (p/q)^B, N, A)` with
`a_i = ρ(i) (q/p)^⌊i/2⌋`. -/
theorem hasSum_baileyBlockRat_of_pattern (p q : ℕ) {B N : ℕ} (hN : N = 2 * B) (hB : 0 < B)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {S : ℝ} (h : HasSum (seriesTermRat p q ρ) S) :
    HasSum (baileyBlockRat p q B N fun i =>
      ρ ((i : ℕ) + 1) * ((q : ℚ) / (p : ℚ)) ^ (((i : ℕ) + 1) / 2)) S := by
  subst hN
  have h' := (hasSum_blocks_iff (Nat.mul_pos two_pos hB) h.summable
    (seriesTermRat_at_zero p q ρ) S).2 h
  refine h'.congr_fun fun j => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : 2 * B * j + (i : ℕ) + 1 = (i : ℕ) + 1 + 2 * B * j := by ring
  have e2 : ρ ((i : ℕ) + 1 + 2 * B * j) = ρ ((i : ℕ) + 1) := periodic_mul hρ j _
  have e3 : ((i : ℕ) + 1 + 2 * B * j) / 2 = ((i : ℕ) + 1) / 2 + B * j := by
    rw [mul_assoc]
    exact Nat.add_mul_div_left _ _ two_pos
  rw [seriesTermRat, e1, e2, e3, pow_add]
  push_cast
  ring

end RatBase

end PiFormula
