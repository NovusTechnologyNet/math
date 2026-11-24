module

public import Pilean.PiFormula.GaloisValue

/-!
# Exact arguments of the 24 numbers `w_j` (milestone M7, part 2)

`garg j = arg w_j = Im Log (1 - ζ^j/t)` for `ζ = ζ_120`. Every one of the 24 arguments
(`j ∈ R0Exps`) is a rational combination of `π`, `garg 60` and `garg 5`:

  `garg j = alpha j · π + beta j · garg 60 + gam j · garg 5`            (`garg_table`).

The inputs are:

* `garg 0 = π/4`, and `|garg j| ≤ π/4`;
* the partner symmetry `garg (30 - j) = -garg j`;
* four signs (`garg 12, garg 84, garg 108 ≥ 0`, `garg 60 ≤ 0`);
* eight of the 13 relations. A relation `∏ w_j^(e_j) = ζ^m` gives
  `∑ e_j garg j = π (m/60 + 2n)` for an integer `n` (`argsum_of_prod`), and the bounds leave a
  single possible `n` (`pin`).

Consequence (`log_exact`): for an integer relation `f` on `R0Exps` whose `beta`- and
`gam`-sums vanish, `∑ f_j Log w_j = (∑ f_j alpha_j) · iπ` exactly. So the exact multiple of
`iπ` of any relation, and of its Galois conjugates, is a finite computation.
-/

@[expose] public section

open Complex ComplexConjugate

namespace PiFormula

/-! ## 1. Arguments: bounds, symmetry, signs -/

/-- `arg w_j = Im Log (1 - ζ^j/t)`. -/
noncomputable def garg (j : ℕ) : ℝ := (Complex.log (wJ j)).im

theorem garg_eq_gfun (j : ℕ) : garg j = gfun (ζ120 ^ j) := rfl

theorem norm_ζ120_pow (j : ℕ) : ‖ζ120 ^ j‖ = 1 := norm_root (isOfFinOrder_ζ120_pow j)

theorem abs_garg_le (j : ℕ) : |garg j| ≤ Real.pi / 4 := abs_gfun_le (norm_ζ120_pow j)

theorem garg_le (j : ℕ) : garg j ≤ Real.pi / 4 := (abs_le.1 (abs_garg_le j)).2

theorem neg_le_garg (j : ℕ) : -(Real.pi / 4) ≤ garg j := (abs_le.1 (abs_garg_le j)).1

/-- The partner `i conj r` has the opposite argument: `garg k = -garg j` when
`j + k ≡ 30 (mod 120)`. -/
theorem garg_partner {j k : ℕ} (h : j + k = 30 ∨ j + k = 150) : garg k = -garg j := by
  have hmul : ζ120 ^ k * ζ120 ^ j = I := by
    rw [← pow_add, add_comm]
    rcases h with h | h
    · rw [h, ζ120_pow_30]
    · rw [h, show 150 = 120 + 30 by norm_num, pow_add, ζ120_prim.pow_eq_one, one_mul,
        ζ120_pow_30]
  have hconj : ζ120 ^ j * conj (ζ120 ^ j) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_ζ120_pow]
    norm_num
  have hk : ζ120 ^ k = I * conj (ζ120 ^ j) := by
    rw [← hmul, mul_assoc, hconj, mul_one]
  rw [garg_eq_gfun, garg_eq_gfun, hk, gfun_partner (norm_ζ120_pow j)]

theorem garg_zero : garg 0 = Real.pi / 4 := by
  have e : wJ 0 = ((1 / 2 : ℝ) : ℂ) * tC := by
    rw [wJ, pow_zero, one_div, tC_inv, tC]
    push_cast
    ring
  rw [garg, Complex.log_im, e, Complex.arg_real_mul _ (by norm_num), arg_tC]

theorem wJ_im (j : ℕ) :
    (wJ j).im = (Real.cos (Real.pi * j / 60) - Real.sin (Real.pi * j / 60)) / 2 := by
  rw [wJ, one_sub_div_tC_im, ζ120_pow_eq, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

theorem garg_nonneg_of {j : ℕ}
    (h : Real.sin (Real.pi * j / 60) ≤ Real.cos (Real.pi * j / 60)) : 0 ≤ garg j := by
  rw [garg, Complex.log_im, Complex.arg_nonneg_iff, wJ_im]
  linarith

theorem garg_neg_of {j : ℕ}
    (h : Real.cos (Real.pi * j / 60) < Real.sin (Real.pi * j / 60)) : garg j < 0 := by
  rw [garg, Complex.log_im, Complex.arg_neg_iff, wJ_im]
  linarith

theorem garg_60_nonpos : garg 60 ≤ 0 := by
  refine (garg_neg_of ?_).le
  rw [show Real.pi * ((60 : ℕ) : ℝ) / 60 = Real.pi by push_cast; ring, Real.cos_pi,
    Real.sin_pi]
  norm_num

/-- `sin x ≤ cos x` for `0 ≤ x ≤ π/4`. -/
theorem sin_le_cos_of_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 4) :
    Real.sin x ≤ Real.cos x := by
  have hpi := Real.pi_pos
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two (x := x) (y := Real.pi / 4)
    (by linarith) (by linarith) h1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (x := x) (y := Real.pi / 4) h0 (by linarith) h1
  rw [Real.sin_pi_div_four] at hs
  rw [Real.cos_pi_div_four] at hc
  linarith

/-- `cos x ≤ sin x` for `π/4 ≤ x ≤ π/2`. -/
theorem cos_le_sin_of_le {x : ℝ} (h0 : Real.pi / 4 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Real.cos x ≤ Real.sin x := by
  have hpi := Real.pi_pos
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 4) (y := x)
    (by linarith) h1 h0
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.pi / 4) (y := x) (by linarith)
    (by linarith) h0
  rw [Real.sin_pi_div_four] at hs
  rw [Real.cos_pi_div_four] at hc
  linarith

theorem garg_12_nonneg : 0 ≤ garg 12 := by
  have hpi := Real.pi_pos
  refine garg_nonneg_of (sin_le_cos_of_le ?_ ?_)
  · positivity
  · push_cast
    linarith

theorem garg_84_nonneg : 0 ≤ garg 84 := by
  have hpi := Real.pi_pos
  refine garg_nonneg_of ?_
  rw [show Real.pi * ((84 : ℕ) : ℝ) / 60 = 2 * Real.pi / 5 + Real.pi by push_cast; ring,
    Real.sin_add_pi, Real.cos_add_pi]
  have h := cos_le_sin_of_le (x := 2 * Real.pi / 5) (by linarith) (by linarith)
  linarith

theorem garg_108_nonneg : 0 ≤ garg 108 := by
  have hpi := Real.pi_pos
  refine garg_nonneg_of ?_
  rw [show Real.pi * ((108 : ℕ) : ℝ) / 60 = 2 * Real.pi - Real.pi / 5 by push_cast; ring,
    Real.sin_two_pi_sub, Real.cos_two_pi_sub]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := Real.pi / 5) (by linarith) (by linarith)
  have hc := Real.cos_nonneg_of_mem_Icc (x := Real.pi / 5) ⟨by linarith, by linarith⟩
  linarith

/-! ## 2. The argument sum of a relation -/

/-- A relation `∏ w_j^(f j) = ζ^m` gives `∑ f_j arg w_j = π (m/60 + 2n)` for an integer `n`. -/
theorem argsum_of_prod {J : Finset ℕ} {f : ℕ → ℤ} {m : ℕ}
    (h : ∏ j ∈ J, wJ j ^ f j = ζ120 ^ m) :
    ∃ n : ℤ, ∑ j ∈ J, (f j : ℝ) * garg j = Real.pi * (m / 60 + 2 * n) := by
  have hexp : Complex.exp (∑ j ∈ J, (f j : ℂ) * Complex.log (wJ j)) =
      Complex.exp ((m : ℂ) * (2 * Real.pi * I / 120)) := by
    rw [Complex.exp_sum, Complex.exp_nat_mul]
    change _ = ζ120 ^ m
    rw [← h]
    exact Finset.prod_congr rfl fun j _ => by
      rw [Complex.exp_int_mul, Complex.exp_log (wJ_ne_zero j)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
  refine ⟨n, ?_⟩
  have e1 : (∑ j ∈ J, (f j : ℂ) * Complex.log (wJ j)).im = ∑ j ∈ J, (f j : ℝ) * garg j := by
    rw [Complex.im_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [garg, ← Complex.ofReal_intCast, Complex.im_ofReal_mul]
  have e2 : (m : ℂ) * (2 * Real.pi * I / 120) + n * (2 * Real.pi * I) =
      ((Real.pi * (m / 60 + 2 * n) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [← e1, hn, e2, mul_comm, Complex.I_mul_im, Complex.ofReal_re]

theorem sumR_add (J : Finset ℕ) (f g : ℕ → ℤ) (F : ℕ → ℝ) :
    ∑ j ∈ J, (((f + g) j : ℤ) : ℝ) * F j =
      ∑ j ∈ J, (f j : ℝ) * F j + ∑ j ∈ J, (g j : ℝ) * F j := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by
    rw [Pi.add_apply]
    push_cast
    ring

theorem sumR_single {J : Finset ℕ} {a : ℕ} (ha : a ∈ J) (c : ℤ) (F : ℕ → ℝ) :
    ∑ j ∈ J, (((Pi.single a c : ℕ → ℤ) j : ℤ) : ℝ) * F j = c * F a := by
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    simp
  · intro h
    exact absurd ha h

/-- Fixing the integer: if `x = π (c + 2n)` lies strictly within `2π` of `π (c + 2n₀)`, then
`n = n₀`. -/
theorem pin {n n₀ : ℤ} {x c : ℝ} (hx : x = Real.pi * (c + 2 * n))
    (h1 : Real.pi * (c + 2 * n₀ - 2) < x) (h2 : x < Real.pi * (c + 2 * n₀ + 2)) :
    x = Real.pi * (c + 2 * n₀) := by
  have hpi := Real.pi_pos
  rw [hx] at h1 h2
  have a1 := lt_of_mul_lt_mul_left h1 hpi.le
  have a2 := lt_of_mul_lt_mul_left h2 hpi.le
  have b1 : n₀ - 1 < n := by exact_mod_cast (by linarith : ((n₀ : ℝ) - 1) < n)
  have b2 : n < n₀ + 1 := by exact_mod_cast (by linarith : (n : ℝ) < n₀ + 1)
  have e : n = n₀ := by omega
  rw [hx, e]

/-! ## 3. Exact arguments -/

theorem garg_20 : garg 20 = -(Real.pi / 6) := by
  have hpi := Real.pi_pos
  obtain ⟨n, hn⟩ := argsum_of_prod rel5_prod
  simp (disch := decide) only [rel5, sumR_add, sumR_single] at hn
  have hp := garg_partner (j := 20) (k := 10) (Or.inl (by norm_num))
  have h := pin (n₀ := 0) hn
    (by push_cast; linarith [garg_le 10, neg_le_garg 10, garg_le 20, neg_le_garg 20])
    (by push_cast; linarith [garg_le 10, neg_le_garg 10, garg_le 20, neg_le_garg 20])
  push_cast at h
  linarith

theorem garg_100 : garg 100 = Real.pi / 6 := by
  have hpi := Real.pi_pos
  obtain ⟨n, hn⟩ := argsum_of_prod rel2_prod
  simp (disch := decide) only [rel2, sumR_add, sumR_single] at hn
  have h0 := garg_zero
  have h := pin (n₀ := -1) hn
    (by push_cast; linarith [garg_le 20, neg_le_garg 20, garg_le 100, neg_le_garg 100])
    (by push_cast; linarith [garg_le 20, neg_le_garg 20, garg_le 100, neg_le_garg 100])
  push_cast at h
  linarith [garg_20]

theorem garg_12 : garg 12 = garg 60 / 4 + 11 * Real.pi / 80 := by
  have hpi := Real.pi_pos
  obtain ⟨n, hn⟩ := argsum_of_prod rel7_prod
  simp (disch := decide) only [rel7, sumR_add, sumR_single] at hn
  have hp18 := garg_partner (j := 12) (k := 18) (Or.inl (by norm_num))
  have hp90 := garg_partner (j := 60) (k := 90) (Or.inr (by norm_num))
  have h := pin (n₀ := -1) hn
    (by push_cast; linarith [garg_12_nonneg, garg_le 12, garg_60_nonpos, neg_le_garg 60])
    (by push_cast; linarith [garg_12_nonneg, garg_le 12, garg_60_nonpos, neg_le_garg 60])
  push_cast at h
  linarith

theorem garg_84 : garg 84 = garg 60 / 4 + 7 * Real.pi / 80 := by
  have hpi := Real.pi_pos
  obtain ⟨n, hn⟩ := argsum_of_prod rel9_prod
  simp (disch := decide) only [rel9, sumR_add, sumR_single] at hn
  have hp66 := garg_partner (j := 84) (k := 66) (Or.inr (by norm_num))
  have hp90 := garg_partner (j := 60) (k := 90) (Or.inr (by norm_num))
  have h := pin (n₀ := -1) hn
    (by push_cast; linarith [garg_84_nonneg, garg_le 84, garg_60_nonpos, neg_le_garg 60])
    (by push_cast; linarith [garg_84_nonneg, garg_le 84, garg_60_nonpos, neg_le_garg 60])
  push_cast at h
  linarith

/-- The relation of `O_10` and `O_2`: `g_12 + g_36 + g_84 + g_108 - g_60 = π/4`. -/
theorem garg_sum_ten : garg 12 + garg 36 - garg 60 + garg 84 + garg 108 = Real.pi / 4 := by
  have hpi := Real.pi_pos
  obtain ⟨n, hn⟩ := argsum_of_prod rel4_prod
  simp (disch := decide) only [rel4, sumR_add, sumR_single] at hn
  have h0 := garg_zero
  have h := pin (n₀ := -1) hn
    (by push_cast; linarith [garg_le 12, neg_le_garg 12, garg_le 36, neg_le_garg 36,
      garg_le 60, neg_le_garg 60, garg_le 84, neg_le_garg 84, garg_le 108, neg_le_garg 108])
    (by push_cast; linarith [garg_le 12, neg_le_garg 12, garg_le 36, neg_le_garg 36,
      garg_le 60, neg_le_garg 60, garg_le 84, neg_le_garg 84, garg_le 108, neg_le_garg 108])
  push_cast at h
  linarith

theorem garg_108 : garg 108 = garg 60 / 4 + 19 * Real.pi / 80 := by
  have hpi := Real.pi_pos
  obtain ⟨n, hn⟩ := argsum_of_prod rel8_prod
  simp (disch := decide) only [rel8, sumR_add, sumR_single] at hn
  have h0 := garg_zero
  have h4 := garg_sum_ten
  have hp42 := garg_partner (j := 108) (k := 42) (Or.inr (by norm_num))
  have hp90 := garg_partner (j := 60) (k := 90) (Or.inr (by norm_num))
  have h := pin (n₀ := -2) hn
    (by push_cast; linarith [garg_108_nonneg, garg_le 108, garg_60_nonpos, neg_le_garg 60])
    (by push_cast; linarith [garg_108_nonneg, garg_le 108, garg_60_nonpos, neg_le_garg 60])
  push_cast at h
  linarith

theorem garg_36 : garg 36 = garg 60 / 4 - 17 * Real.pi / 80 := by
  linarith [garg_sum_ten, garg_12, garg_84, garg_108]

theorem garg_65 : garg 65 = Real.pi / 6 - garg 5 := by
  have hpi := Real.pi_pos
  obtain ⟨n, hn⟩ := argsum_of_prod rel12_prod
  simp (disch := decide) only [rel12, sumR_add, sumR_single] at hn
  have h0 := garg_zero
  have hp105 := garg_partner (j := 45) (k := 105) (Or.inr (by norm_num))
  have h := pin (n₀ := -1) hn
    (by push_cast; linarith [garg_le 5, neg_le_garg 5, garg_le 65, neg_le_garg 65])
    (by push_cast; linarith [garg_le 5, neg_le_garg 5, garg_le 65, neg_le_garg 65])
  push_cast at h
  linarith

theorem garg_45 : garg 45 = 2 * garg 5 - 2 * Real.pi / 3 := by
  have hpi := Real.pi_pos
  obtain ⟨n, hn⟩ := argsum_of_prod rel13_prod
  simp (disch := decide) only [rel13, sumR_add, sumR_single] at hn
  have h0 := garg_zero
  have hp85 := garg_partner (j := 65) (k := 85) (Or.inr (by norm_num))
  have h := pin (n₀ := 0) hn
    (by push_cast; linarith [garg_le 5, neg_le_garg 5, garg_le 45, neg_le_garg 45,
      garg_le 85, neg_le_garg 85])
    (by push_cast; linarith [garg_le 5, neg_le_garg 5, garg_le 45, neg_le_garg 45,
      garg_le 85, neg_le_garg 85])
  push_cast at h
  linarith [garg_65]

/-! ## 4. The table of arguments -/

/-- The coefficient of `π` in `garg j`. -/
def alpha (j : ℕ) : ℚ :=
  if j = 0 then 1 / 4 else if j = 30 then -1 / 4 else if j = 20 then -1 / 6 else
  if j = 100 then 1 / 6 else if j = 45 then -2 / 3 else if j = 105 then 2 / 3 else
  if j = 12 then 11 / 80 else if j = 36 then -17 / 80 else if j = 84 then 7 / 80 else
  if j = 108 then 19 / 80 else if j = 10 then 1 / 6 else if j = 50 then -1 / 6 else
  if j = 18 then -11 / 80 else if j = 42 then -19 / 80 else if j = 66 then -7 / 80 else
  if j = 114 then 17 / 80 else if j = 65 then 1 / 6 else if j = 85 then -1 / 6 else 0

/-- The coefficient of `garg 60` in `garg j`. -/
def beta (j : ℕ) : ℚ :=
  if j = 60 then 1 else if j = 90 then -1 else if j = 12 then 1 / 4 else
  if j = 36 then 1 / 4 else if j = 84 then 1 / 4 else if j = 108 then 1 / 4 else
  if j = 18 then -1 / 4 else if j = 42 then -1 / 4 else if j = 66 then -1 / 4 else
  if j = 114 then -1 / 4 else 0

/-- The coefficient of `garg 5` in `garg j`. -/
def gam (j : ℕ) : ℚ :=
  if j = 45 then 2 else if j = 105 then -2 else if j = 5 then 1 else if j = 25 then -1 else
  if j = 65 then -1 else if j = 85 then 1 else 0

/-- **The table of arguments**: each `arg w_j` in terms of `π`, `arg w_60` and `arg w_5`. -/
theorem garg_table : ∀ j ∈ R0Exps,
    garg j = alpha j * Real.pi + beta j * garg 60 + gam j * garg 5 := by
  intro j hj
  simp only [R0Exps, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show alpha 0 = 1 / 4 from by norm_num [alpha],
      show beta 0 = 0 from by norm_num [beta],
      show gam 0 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_zero]
  · rw [show alpha 60 = 0 from by norm_num [alpha],
      show beta 60 = 1 from by norm_num [beta],
      show gam 60 = 0 from by norm_num [gam]]
    push_cast
    linarith
  · rw [show alpha 30 = -1 / 4 from by norm_num [alpha],
      show beta 30 = 0 from by norm_num [beta],
      show gam 30 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_zero, garg_partner (j := 0) (k := 30) (Or.inl (by norm_num))]
  · rw [show alpha 90 = 0 from by norm_num [alpha],
      show beta 90 = -1 from by norm_num [beta],
      show gam 90 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_partner (j := 60) (k := 90) (Or.inr (by norm_num))]
  · rw [show alpha 20 = -1 / 6 from by norm_num [alpha],
      show beta 20 = 0 from by norm_num [beta],
      show gam 20 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_20]
  · rw [show alpha 100 = 1 / 6 from by norm_num [alpha],
      show beta 100 = 0 from by norm_num [beta],
      show gam 100 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_100]
  · rw [show alpha 15 = 0 from by norm_num [alpha],
      show beta 15 = 0 from by norm_num [beta],
      show gam 15 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_partner (j := 15) (k := 15) (Or.inl (by norm_num))]
  · rw [show alpha 45 = -2 / 3 from by norm_num [alpha],
      show beta 45 = 0 from by norm_num [beta],
      show gam 45 = 2 from by norm_num [gam]]
    push_cast
    linarith [garg_45]
  · rw [show alpha 75 = 0 from by norm_num [alpha],
      show beta 75 = 0 from by norm_num [beta],
      show gam 75 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_partner (j := 75) (k := 75) (Or.inr (by norm_num))]
  · rw [show alpha 105 = 2 / 3 from by norm_num [alpha],
      show beta 105 = 0 from by norm_num [beta],
      show gam 105 = -2 from by norm_num [gam]]
    push_cast
    linarith [garg_45, garg_partner (j := 45) (k := 105) (Or.inr (by norm_num))]
  · rw [show alpha 12 = 11 / 80 from by norm_num [alpha],
      show beta 12 = 1 / 4 from by norm_num [beta],
      show gam 12 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_12]
  · rw [show alpha 36 = -17 / 80 from by norm_num [alpha],
      show beta 36 = 1 / 4 from by norm_num [beta],
      show gam 36 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_36]
  · rw [show alpha 84 = 7 / 80 from by norm_num [alpha],
      show beta 84 = 1 / 4 from by norm_num [beta],
      show gam 84 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_84]
  · rw [show alpha 108 = 19 / 80 from by norm_num [alpha],
      show beta 108 = 1 / 4 from by norm_num [beta],
      show gam 108 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_108]
  · rw [show alpha 10 = 1 / 6 from by norm_num [alpha],
      show beta 10 = 0 from by norm_num [beta],
      show gam 10 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_20, garg_partner (j := 20) (k := 10) (Or.inl (by norm_num))]
  · rw [show alpha 50 = -1 / 6 from by norm_num [alpha],
      show beta 50 = 0 from by norm_num [beta],
      show gam 50 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_100, garg_partner (j := 100) (k := 50) (Or.inr (by norm_num))]
  · rw [show alpha 18 = -11 / 80 from by norm_num [alpha],
      show beta 18 = -1 / 4 from by norm_num [beta],
      show gam 18 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_12, garg_partner (j := 12) (k := 18) (Or.inl (by norm_num))]
  · rw [show alpha 42 = -19 / 80 from by norm_num [alpha],
      show beta 42 = -1 / 4 from by norm_num [beta],
      show gam 42 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_108, garg_partner (j := 108) (k := 42) (Or.inr (by norm_num))]
  · rw [show alpha 66 = -7 / 80 from by norm_num [alpha],
      show beta 66 = -1 / 4 from by norm_num [beta],
      show gam 66 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_84, garg_partner (j := 84) (k := 66) (Or.inr (by norm_num))]
  · rw [show alpha 114 = 17 / 80 from by norm_num [alpha],
      show beta 114 = -1 / 4 from by norm_num [beta],
      show gam 114 = 0 from by norm_num [gam]]
    push_cast
    linarith [garg_36, garg_partner (j := 36) (k := 114) (Or.inr (by norm_num))]
  · rw [show alpha 5 = 0 from by norm_num [alpha],
      show beta 5 = 0 from by norm_num [beta],
      show gam 5 = 1 from by norm_num [gam]]
    push_cast
    linarith
  · rw [show alpha 25 = 0 from by norm_num [alpha],
      show beta 25 = 0 from by norm_num [beta],
      show gam 25 = -1 from by norm_num [gam]]
    push_cast
    linarith [garg_partner (j := 5) (k := 25) (Or.inl (by norm_num))]
  · rw [show alpha 65 = 1 / 6 from by norm_num [alpha],
      show beta 65 = 0 from by norm_num [beta],
      show gam 65 = -1 from by norm_num [gam]]
    push_cast
    linarith [garg_65]
  · rw [show alpha 85 = -1 / 6 from by norm_num [alpha],
      show beta 85 = 0 from by norm_num [beta],
      show gam 85 = 1 from by norm_num [gam]]
    push_cast
    linarith [garg_65, garg_partner (j := 65) (k := 85) (Or.inr (by norm_num))]

/-! ## 5. The exact logarithmic form of a relation -/

/-- **Exact logarithmic form.** For an integer relation `f` on `R0Exps` whose `beta`- and
`gam`-sums vanish, `∑ f_j Log w_j = (∑ f_j alpha_j) · iπ`. -/
theorem log_exact {f : ℕ → ℤ} (hf : IsRelJ R0Exps f)
    (hβ : ∑ j ∈ R0Exps, (f j : ℚ) * beta j = 0) (hγ : ∑ j ∈ R0Exps, (f j : ℚ) * gam j = 0) :
    ∑ j ∈ R0Exps, (f j : ℂ) * Complex.log (wJ j) =
      ((∑ j ∈ R0Exps, (f j : ℚ) * alpha j : ℚ) : ℂ) * (Real.pi * I) := by
  obtain ⟨q, hq⟩ := log_form hf
  have him := congrArg Complex.im hq
  have e1 : (∑ j ∈ R0Exps, (f j : ℂ) * Complex.log (wJ j)).im =
      ∑ j ∈ R0Exps, (f j : ℝ) * garg j := by
    rw [Complex.im_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [garg, ← Complex.ofReal_intCast, Complex.im_ofReal_mul]
  have e2 : ((q : ℂ) * (Real.pi * I)).im = q * Real.pi := by
    rw [show (q : ℂ) * (Real.pi * I) = ((q * Real.pi : ℝ) : ℂ) * I by push_cast; ring,
      mul_comm, Complex.I_mul_im, Complex.ofReal_re]
  rw [e1, e2] at him
  have e3 : ∑ j ∈ R0Exps, (f j : ℝ) * garg j =
      ((∑ j ∈ R0Exps, (f j : ℚ) * alpha j : ℚ) : ℝ) * Real.pi := by
    have t1 : ∑ j ∈ R0Exps, (f j : ℝ) * garg j =
        ∑ j ∈ R0Exps, ((((f j : ℚ) * alpha j : ℚ) : ℝ) * Real.pi
          + (((f j : ℚ) * beta j : ℚ) : ℝ) * garg 60
          + (((f j : ℚ) * gam j : ℚ) : ℝ) * garg 5) :=
      Finset.sum_congr rfl fun j hj => by
        rw [garg_table j hj]
        push_cast
        ring
    rw [t1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Rat.cast_sum, ← Rat.cast_sum, ← Rat.cast_sum,
      hβ, hγ]
    simp
  rw [e3] at him
  have hqv : ((∑ j ∈ R0Exps, (f j : ℚ) * alpha j : ℚ) : ℝ) = q :=
    mul_right_cancel₀ Real.pi_pos.ne' him
  have hq2 : q = ∑ j ∈ R0Exps, (f j : ℚ) * alpha j := by exact_mod_cast hqv.symm
  rw [hq, hq2]

/-! ## 6. Conjugates of a relation -/

theorem wJ_mod (x : ℕ) : wJ (x % 120) = wJ x := by
  rw [wJ, wJ, ζ120_pow_mod]

/-- If `f` is a relation on `R0Exps` and multiplication by `b` permutes `R0Exps` (with inverse
multiplication by `a ≡ 1 (mod 4)`), then `j ↦ f (b j mod 120)` is a relation. -/
theorem isRelJ_comp {f : ℕ → ℤ} (hf : IsRelJ R0Exps f) {a b : ℕ} (ha : Nat.Coprime a 120)
    (ha4 : a % 4 = 1) (hb : ∀ j ∈ R0Exps, b * j % 120 ∈ R0Exps)
    (ha' : ∀ j ∈ R0Exps, a * j % 120 ∈ R0Exps)
    (hab : ∀ j ∈ R0Exps, a * (b * j % 120) % 120 = j)
    (hba : ∀ j ∈ R0Exps, b * (a * j % 120) % 120 = j) :
    IsRelJ R0Exps (fun j => f (b * j % 120)) := by
  obtain ⟨ξ, hξ, hprod⟩ := isRelJ_conj hf ha ha4
  refine ⟨ξ, hξ, ?_⟩
  rw [← hprod]
  refine Finset.prod_nbij' (fun j => b * j % 120) (fun j => a * j % 120) hb ha' hab hba ?_
  intro j hj
  have e : wJ (a * (b * j % 120)) = wJ j := by rw [← wJ_mod, hab j hj]
  change wJ j ^ f (b * j % 120) = wJ (a * (b * j % 120)) ^ f (b * j % 120)
  rw [e]

end PiFormula
