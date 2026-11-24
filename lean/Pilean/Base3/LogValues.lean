/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Base3.Series

/-!
# Base 3: the generators are values

For `n ≥ 1` and a cube root of unity `c`, the number `log |t^n - c|`, `t = √-3`, is the value
of a series of the class F3 (`isF3Value_log_gen`), and so is `log 3` (`isF3Value_log_three`).
This is the base-3 version of `isFValue_log_norm` of `LogYes.lean`.

The proof. The roots `r` of `X^n = c` have `∏ (t - r) = t^n - c`, so
`log |t^n - c| - n log |t| = ∑_r log |1 - r/t| = -∑_k Re(p_k t^(-k)) / k`, where
`p_k = ∑_r r^k` is `n c^(k/n)` if `n ∣ k` and `0` otherwise. Since `t^(-2) = -1/3`,
`t^(-k) = (-1)^⌊k/2⌋ 3^(-⌊k/2⌋) t^(-(k mod 2))`, and for `c = ω^u` the numbers `Re(ω^e)` and
`Re(ω^e / t) = Im(ω^e)/√3` are rational: `1, -1/2, -1/2` and `0, 1/2, -1/2`. So the series
has the form `∑ ρ(k) 3^(-⌊k/2⌋)/k` with `ρ` rational of period `12 n` (`rhoGen`).
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace Base3

/-! ## 1. The cube roots of unity -/

/-- `ω = (-1 + i√3)/2`. -/
noncomputable def w3 : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem sqrt3_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem w3_sq : w3 ^ 2 = ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩ := by
  rw [pow_two]
  apply Complex.ext
  · simp only [Complex.mul_re, w3]
    linear_combination (-1 / 4 : ℝ) * sqrt3_mul_self
  · simp only [Complex.mul_im, w3]
    ring

theorem w3_pow_three : w3 ^ 3 = 1 := by
  rw [pow_succ, w3_sq]
  apply Complex.ext
  · simp only [Complex.mul_re, w3, Complex.one_re]
    linear_combination (1 / 4 : ℝ) * sqrt3_mul_self
  · simp only [Complex.mul_im, w3, Complex.one_im]
    ring

theorem one_add_w3 : 1 + w3 + w3 ^ 2 = 0 := by
  rw [w3_sq]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.one_re, w3, Complex.zero_re]
    ring
  · simp only [Complex.add_im, Complex.one_im, w3, Complex.zero_im]
    ring

theorem w3_pow_mod (e : ℕ) : w3 ^ e = w3 ^ (e % 3) := by
  conv_lhs => rw [← Nat.mod_add_div e 3]
  rw [pow_add, pow_mul, w3_pow_three, one_pow, mul_one]

/-- A cube root of unity is a power of `ω`. -/
theorem eq_w3_pow_of_cube {c : ℂ} (hc : c ^ 3 = 1) : ∃ u : ℕ, c = w3 ^ u := by
  have h : (c - 1) * (c - w3) * (c - w3 ^ 2) = 0 := by
    linear_combination hc + (c - c ^ 2) * one_add_w3 + (c - 1) * w3_pow_three
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact ⟨0, by rw [pow_zero]; exact sub_eq_zero.1 h⟩
    · exact ⟨1, by rw [pow_one]; exact sub_eq_zero.1 h⟩
  · exact ⟨2, sub_eq_zero.1 h⟩

/-- `Re(ω^e)`. -/
def eisRe (e : ℕ) : ℚ := if e % 3 = 0 then 1 else -1 / 2

/-- `Im(ω^e) / √3`. -/
def eisB (e : ℕ) : ℚ := if e % 3 = 0 then 0 else if e % 3 = 1 then 1 / 2 else -1 / 2

theorem eisRe_mod (e : ℕ) : eisRe (e % 3) = eisRe e := by simp [eisRe]

theorem eisB_mod (e : ℕ) : eisB (e % 3) = eisB e := by simp [eisB]

theorem w3_pow_re_im (e : ℕ) :
    (w3 ^ e).re = ((eisRe e : ℚ) : ℝ) ∧ (w3 ^ e).im = Real.sqrt 3 * ((eisB e : ℚ) : ℝ) := by
  rw [w3_pow_mod, ← eisRe_mod, ← eisB_mod]
  have h : e % 3 < 3 := Nat.mod_lt _ (by norm_num)
  obtain ⟨x, hx⟩ : ∃ x, e % 3 = x := ⟨_, rfl⟩
  rw [hx] at h ⊢
  interval_cases x
  · simp [eisRe, eisB]
  · constructor
    · simp [eisRe, w3]
    · simp [eisB, w3]
      ring
  · rw [w3_sq]
    constructor
    · simp [eisRe]
    · simp [eisB]
      ring

/-! ## 2. Powers of `1/t` -/

theorem t3_inv_pow (k : ℕ) :
    t3⁻¹ ^ k = (((-1 : ℝ) ^ (k / 2) / 3 ^ (k / 2) : ℝ) : ℂ) * t3⁻¹ ^ (k % 2) := by
  have h2 : t3⁻¹ ^ 2 = ((-1 / 3 : ℝ) : ℂ) := by
    rw [inv_pow, t3_sq]
    push_cast
    norm_num
  conv_lhs => rw [← Nat.div_add_mod k 2]
  rw [pow_add, pow_mul, h2, ← Complex.ofReal_pow]
  congr 2
  rw [div_pow]

/-- `Re(z / t) = Im(z) / √3`. -/
theorem re_mul_t3_inv (z : ℂ) : (z * t3⁻¹).re = z.im / Real.sqrt 3 := by
  have hs : Real.sqrt 3 ≠ 0 := by
    have := Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)
    exact this.ne'
  have ht : t3⁻¹ = ((-(Real.sqrt 3)⁻¹ : ℝ) : ℂ) * I := by
    rw [t3, mul_inv, Complex.inv_I]
    push_cast
    ring
  rw [ht, ← mul_assoc, Complex.mul_I_re, Complex.im_mul_ofReal]
  field_simp

/-- `Re(ω^x t^(-e))` for `e = 0, 1`. -/
def eisQ (e x : ℕ) : ℚ := if e = 0 then eisRe x else eisB x

theorem re_w3_pow_mul (x : ℕ) {e : ℕ} (he : e < 2) :
    (w3 ^ x * t3⁻¹ ^ e).re = ((eisQ e x : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := w3_pow_re_im x
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)).ne'
  interval_cases e
  · rw [pow_zero, mul_one, h1]
    simp [eisQ]
  · rw [pow_one, re_mul_t3_inv, h2]
    simp only [eisQ, one_ne_zero, ↓reduceIte]
    field_simp

/-! ## 3. The pattern of a generator -/

/-- The pattern of `log |t^n - ω^u| - n log |t|`: `ρ(k) = -n (-1)^⌊k/2⌋ Re(ω^(u k/n) t^(-(k mod
2)))` for `n ∣ k`, and `0` otherwise. -/
def rhoGen (n u : ℕ) (k : ℕ) : ℚ :=
  if n ∣ k then -(n : ℚ) * (-1) ^ (k / 2) * eisQ (k % 2) (u * (k / n)) else 0

theorem eisQ_add (e x m : ℕ) : eisQ e (x + 3 * m) = eisQ e x := by
  have h : (x + 3 * m) % 3 = x % 3 := by omega
  simp [eisQ, eisRe, eisB, h]

theorem rhoGen_periodic {n : ℕ} (hn : 0 < n) (u k : ℕ) :
    rhoGen n u (k + 12 * n) = rhoGen n u k := by
  have h1 : n ∣ k + 12 * n ↔ n ∣ k := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, Nat.add_mul_mod_self_right]
  have h2 : (k + 12 * n) / 2 = k / 2 + 2 * (3 * n) := by omega
  have h3 : (k + 12 * n) % 2 = k % 2 := by omega
  have h4 : (k + 12 * n) / n = k / n + 12 := Nat.add_mul_div_right k 12 hn
  have h5 : u * (k / n + 12) = u * (k / n) + 3 * (4 * u) := by ring
  simp only [rhoGen, h1, h2, h3, h4, h5, eisQ_add, pow_add, pow_mul]
  norm_num

/-- The `k`-th term of the series of a generator. -/
theorem seriesTerm3_rhoGen (n u k : ℕ) :
    seriesTerm3 (rhoGen n u) k =
      -(((if n ∣ k then (n : ℂ) * (w3 ^ u) ^ (k / n) else 0) * t3⁻¹ ^ k).re) / k := by
  rw [seriesTerm3, rhoGen]
  split_ifs with hk
  · have he : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hre : ((n : ℂ) * (w3 ^ u) ^ (k / n) * t3⁻¹ ^ k).re =
        (n : ℝ) * ((-1) ^ (k / 2) / 3 ^ (k / 2)) * ((eisQ (k % 2) (u * (k / n)) : ℚ) : ℝ) := by
      rw [t3_inv_pow k, ← pow_mul]
      have e : (n : ℂ) * w3 ^ (u * (k / n)) *
          ((((-1 : ℝ) ^ (k / 2) / 3 ^ (k / 2) : ℝ) : ℂ) * t3⁻¹ ^ (k % 2)) =
          (((n : ℝ) * ((-1) ^ (k / 2) / 3 ^ (k / 2)) : ℝ) : ℂ) *
            (w3 ^ (u * (k / n)) * t3⁻¹ ^ (k % 2)) := by
        push_cast
        ring
      rw [e, Complex.re_ofReal_mul, re_w3_pow_mul _ he]
    rw [hre]
    push_cast
    ring
  · simp

/-! ## 4. The generators are values -/

theorem prod_sub_nthRoots {n : ℕ} (hn : 0 < n) (c x : ℂ) :
    ((nthRoots n c).map (fun r => x - r)).prod = x ^ n - c := by
  have hm : (X ^ n - C c : ℂ[X]).Monic := monic_X_pow_sub_C c hn.ne'
  have hcard : Multiset.card (X ^ n - C c : ℂ[X]).roots = (X ^ n - C c : ℂ[X]).natDegree := by
    rw [natDegree_X_pow_sub_C]
    exact card_nthRoots_eq hn c
  have h := congrArg (eval x) (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard)
  rw [eval_multiset_prod, Multiset.map_map] at h
  simpa [nthRoots, Function.comp_def] using h

/-- **The series of a generator.** `∑ ρ(k) 3^(-⌊k/2⌋)/k = log |t^n - ω^u| - n log |t|` for the
pattern `rhoGen n u`. -/
theorem hasSum_gen3 {n : ℕ} (hn : 0 < n) (u : ℕ) :
    HasSum (seriesTerm3 (rhoGen n u))
      (Real.log ‖t3 ^ n - w3 ^ u‖ - n * Real.log ‖t3‖) := by
  obtain ⟨ζ, α, hζ, hα, hS⟩ := nthRoots_repr hn (w3 ^ u)
  have hc1 : ‖w3 ^ u‖ = 1 := Complex.norm_eq_one_of_pow_eq_one
    (n := 3) (by rw [← pow_mul, mul_comm, pow_mul, w3_pow_three, one_pow]) (by norm_num)
  have hα1 : ‖α‖ = 1 := by
    have h := congrArg norm hα
    rw [norm_pow, hc1] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h
  have hζ1 : ‖ζ‖ = 1 := hζ.norm'_eq_one hn.ne'
  have hnorm : ∀ j : ℕ, ‖ζ ^ j * α‖ = 1 := fun j => by
    rw [norm_mul, norm_pow, hζ1, one_pow, one_mul, hα1]
  have ht0 : (0 : ℝ) < ‖t3‖ := norm_pos_iff.2 t3_ne_zero
  -- each root
  have hterm : ∀ j ∈ Finset.range n,
      HasSum (fun k : ℕ => ((ζ ^ j * α / t3) ^ k / k).re)
        (-Real.log ‖1 - ζ ^ j * α / t3‖) := by
    intro j _
    have h := Complex.hasSum_re (hasSum_taylorSeries_neg_log (norm_div_t3_lt (hnorm j)))
    rwa [Complex.neg_re, Complex.log_re] at h
  have hsum := hasSum_sum hterm
  -- the value
  have hprod : ∏ j ∈ Finset.range n, (t3 - ζ ^ j * α) = t3 ^ n - w3 ^ u := by
    have h := prod_sub_nthRoots hn (w3 ^ u) t3
    rw [hS, Multiset.map_map] at h
    exact h
  have hne : ∀ j : ℕ, t3 - ζ ^ j * α ≠ 0 := fun j => t3_sub_ne_zero (hnorm j)
  have hval : ∑ j ∈ Finset.range n, -Real.log ‖1 - ζ ^ j * α / t3‖ =
      -(Real.log ‖t3 ^ n - w3 ^ u‖ - n * Real.log ‖t3‖) := by
    have h1 : ∀ j ∈ Finset.range n, -Real.log ‖1 - ζ ^ j * α / t3‖ =
        -Real.log ‖t3 - ζ ^ j * α‖ + Real.log ‖t3‖ := by
      intro j _
      have hw : 1 - ζ ^ j * α / t3 = (t3 - ζ ^ j * α) / t3 := by
        rw [sub_div, div_self t3_ne_zero]
      rw [hw, norm_div, Real.log_div (norm_ne_zero_iff.2 (hne j)) ht0.ne']
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      ← Real.log_prod (fun j _ => norm_ne_zero_iff.2 (hne j)), ← norm_prod, hprod,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  -- the terms
  have hpsum : ∀ k : ℕ, ∑ j ∈ Finset.range n, (ζ ^ j * α) ^ k =
      if n ∣ k then (n : ℂ) * (w3 ^ u) ^ (k / n) else 0 := by
    intro k
    rw [← psum_nthRoots hn (w3 ^ u) k, psum, hS, Multiset.map_map]
    rfl
  have hfun : (fun k : ℕ => ∑ j ∈ Finset.range n, ((ζ ^ j * α / t3) ^ k / k).re) =
      fun k : ℕ => -seriesTerm3 (rhoGen n u) k := by
    funext k
    have e1 : ∑ j ∈ Finset.range n, ((ζ ^ j * α / t3) ^ k / k).re =
        ((∑ j ∈ Finset.range n, (ζ ^ j * α) ^ k) * t3⁻¹ ^ k / k).re := by
      rw [Finset.sum_mul, Finset.sum_div, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e0 : (ζ ^ j * α / t3) ^ k = (ζ ^ j * α) ^ k * t3⁻¹ ^ k := by
        rw [div_eq_mul_inv, mul_pow]
      rw [e0]
    rw [e1, hpsum k, seriesTerm3_rhoGen, Complex.div_natCast_re]
    ring
  rw [hfun, hval] at hsum
  have h := hsum.neg
  simpa using h

theorem isF3Value_gen_sub {n : ℕ} (hn : 0 < n) (u : ℕ) :
    IsF3Value (Real.log ‖t3 ^ n - w3 ^ u‖ - n * Real.log ‖t3‖) :=
  ⟨12 * n, rhoGen n u, by positivity, rhoGen_periodic hn u, hasSum_gen3 hn u⟩

/-- `t - ω = -ω²`, a unit: this is why `log 3` is a value. -/
theorem t3_sub_w3 : t3 - w3 = -w3 ^ 2 := by
  rw [w3_sq]
  apply Complex.ext
  · simp [t3, w3]
  · simp [t3, w3]
    ring

/-- **`log 3` is a value of the class F3.** -/
theorem isF3Value_log_three : IsF3Value (Real.log 3) := by
  have h := isF3Value_gen_sub (n := 1) one_pos 1
  have hn : ‖t3 ^ 1 - w3 ^ 1‖ = 1 := by
    rw [pow_one, pow_one, t3_sub_w3, norm_neg]
    exact Complex.norm_eq_one_of_pow_eq_one (n := 3)
      (by rw [← pow_mul, mul_comm, pow_mul, w3_pow_three, one_pow]) (by norm_num)
  rw [hn, Real.log_one, log_norm_t3] at h
  have h2 := h.const_mul (-2)
  convert h2 using 1
  push_cast
  ring

/-- **`log |t^n - c|` is a value of the class F3**, for `n ≥ 1` and `c^3 = 1`. -/
theorem isF3Value_log_gen {n : ℕ} (hn : 0 < n) {c : ℂ} (hc : c ^ 3 = 1) :
    IsF3Value (Real.log ‖t3 ^ n - c‖) := by
  obtain ⟨u, rfl⟩ := eq_w3_pow_of_cube hc
  have h := (isF3Value_gen_sub hn u).add (isF3Value_log_three.const_mul ((n : ℚ) / 2))
  convert h using 1
  rw [log_norm_t3]
  push_cast
  ring

end Base3

end PiFormula
