/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.BaseB.Defs

/-!
# A general base `b`: the four logarithms at `1, -1, i, -i`

With `t = √b`, the four numbers `1 - r/t` for `r = 1, -1, i, -i` are the ones that the good
primes do not reach. This file proves that there is no multiplicative relation among them.

* **Real part** (`log_indepB`, for `b ≥ 2`). The three real numbers `log(1 - 1/√b)`,
  `log(1 + 1/√b)` and `log(1 + 1/b)` are linearly independent over `ℤ`. With integers
  `z₁, z₂, s` the relation is
  `2 z₁ log(√b - 1) + 2 z₂ log(√b + 1) + s log(b + 1) = (z₁ + z₂ + s) log b`.
  - If `b` is not a square, `((√b + 1)/(√b - 1))^(z₂ - z₁)` is rational, and a non-zero power
    of `(√b + 1)/(√b - 1) = (√b + 1)²/(b - 1)` is irrational (`irrational_unitB_zpow`); so
    `z₁ = z₂`. Then `(b - 1)^(2z) (b + 1)^s = b^(2z + s)`; a prime factor of `b` gives
    `2z + s = 0`, and `((b - 1)/(b + 1))^(2z) = 1` gives `z = 0`.
  - If `b = c²`, then `(c - 1)^(2z₁) (c + 1)^(2z₂) (c² + 1)^s = c^(2(z₁ + z₂ + s))`. A prime
    factor of `c` gives `z₁ + z₂ + s = 0`; an odd prime factor of `c² + 1` (there is one,
    since `c² + 1 > 2` is not divisible by 4) divides none of `c - 1`, `c + 1`, `c` and gives
    `s = 0`; then `((c - 1)/(c + 1))^(2z₁) = 1` gives `z₁ = 0`.
* **Unit circle** (`unitB_zpow_eq_one`, for `b ≥ 4`). The number `w = (t - i)/(t + i)` is not
  a root of unity: `w + 1/w = 2(b - 1)/(b + 1)` is a rational number strictly between 1 and
  2, and for a root of unity it would be an algebraic integer, so an integer.

In base 3 the second statement fails (`2(b - 1)/(b + 1) = 1`, and `w` is a sixth root of
unity): this is where the formulas for `π√3` come from.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace BaseB

/-! ## 1. Logarithms of positive integers and a private prime -/

/-- Four positive integers with `∑ e_i log a_i = 0`, the `e_i` integers: if a prime divides
`a₄` and none of `a₁, a₂, a₃`, then `e₄ = 0`. -/
theorem int_eq_zero_of_log_rel {a₁ a₂ a₃ a₄ : ℕ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) (h₃ : 0 < a₃)
    (h₄ : 0 < a₄) {e₁ e₂ e₃ e₄ : ℤ} {p : ℕ} (hp : p.Prime) (hp₁ : ¬ p ∣ a₁) (hp₂ : ¬ p ∣ a₂)
    (hp₃ : ¬ p ∣ a₃) (hp₄ : p ∣ a₄)
    (h : (e₁ : ℝ) * Real.log a₁ + e₂ * Real.log a₂ + e₃ * Real.log a₃ + e₄ * Real.log a₄ = 0) :
    e₄ = 0 := by
  have hz : ∀ (x : ℝ), 0 < x → ∀ n : ℤ, Real.exp (n * Real.log x) = x ^ n :=
    fun x hx n => by rw [mul_comm, Real.exp_mul, Real.exp_log hx, Real.rpow_intCast]
  have h' := congrArg Real.exp h
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_zero, hz _ (Nat.cast_pos.2 h₁),
    hz _ (Nat.cast_pos.2 h₂), hz _ (Nat.cast_pos.2 h₃), hz _ (Nat.cast_pos.2 h₄)] at h'
  have hq : (a₁ : ℚ) ^ e₁ * (a₂ : ℚ) ^ e₂ * (a₃ : ℚ) ^ e₃ * (a₄ : ℚ) ^ e₄ = 1 := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact h'
  have := Fact.mk hp
  have n₁ : (a₁ : ℚ) ^ e₁ ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 h₁.ne')
  have n₂ : (a₂ : ℚ) ^ e₂ ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 h₂.ne')
  have n₃ : (a₃ : ℚ) ^ e₃ ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 h₃.ne')
  have n₄ : (a₄ : ℚ) ^ e₄ ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 h₄.ne')
  have hv := congrArg (padicValRat p) hq
  rw [padicValRat.mul (mul_ne_zero (mul_ne_zero n₁ n₂) n₃) n₄,
    padicValRat.mul (mul_ne_zero n₁ n₂) n₃, padicValRat.mul n₁ n₂, padicValRat.zpow,
    padicValRat.zpow, padicValRat.zpow, padicValRat.zpow, padicValRat.of_nat,
    padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat,
    multiplicity_eq_zero_of_not_dvd hp₁, multiplicity_eq_zero_of_not_dvd hp₂,
    multiplicity_eq_zero_of_not_dvd hp₃, padicValRat.one] at hv
  have hm : 1 ≤ multiplicity p a₄ := one_le_multiplicity_of_dvd h₄.ne' hp₄
  simp only [Nat.cast_zero, mul_zero, zero_add, mul_eq_zero, Nat.cast_eq_zero] at hv
  rcases hv with hv | hv
  · exact hv
  · omega

private theorem prime_not_dvd_succ {p n : ℕ} (hp : p.Prime) (h : p ∣ n) : ¬ p ∣ n + 1 :=
  fun h' => hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h'))

/-- For `c ≥ 2` the number `c² + 1` has an odd prime factor. -/
theorem exists_odd_prime_dvd_sq_add_one {c : ℕ} (hc : 2 ≤ c) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ c * c + 1 := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (c * c + 1) with ⟨k, hk⟩ | ⟨q, hq, hd, ho⟩
  · exfalso
    have h5 : 5 ≤ c * c + 1 := by nlinarith
    have h4 : (c * c + 1) % 4 ≠ 0 := by
      rcases Nat.even_or_odd' c with ⟨m, rfl | rfl⟩
      · have : 2 * m * (2 * m) + 1 = 4 * (m * m) + 1 := by ring
        omega
      · have : (2 * m + 1) * (2 * m + 1) + 1 = 4 * (m * m + m) + 2 := by ring
        omega
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · rw [pow_zero] at hk
        omega
      · rw [pow_one] at hk
        omega
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have h2 : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
    omega
  · refine ⟨q, hq, ?_, hd⟩
    rintro rfl
    exact absurd ho (by decide)

/-! ## 2. The real part when `b` is a square -/

/-- The case `b = c²`, `c = d + 2`: the relation
`2 z₁ log(c - 1) + 2 z₂ log(c + 1) + s log(c² + 1) = 2 (z₁ + z₂ + s) log c` has only the zero
solution. -/
theorem log_rel_square (d : ℕ) {z₁ z₂ s : ℤ}
    (H : 2 * (z₁ : ℝ) * Real.log ((d + 1 : ℕ) : ℝ) + 2 * z₂ * Real.log ((d + 3 : ℕ) : ℝ) +
        s * Real.log (((d + 2) * (d + 2) + 1 : ℕ) : ℝ) -
        2 * (z₁ + z₂ + s) * Real.log ((d + 2 : ℕ) : ℝ) = 0) : z₁ = 0 ∧ z₂ = 0 ∧ s = 0 := by
  have H' := H
  push_cast at H'
  -- a prime factor of `c`
  have hp := Nat.minFac_prime (show d + 2 ≠ 1 by omega)
  have hpc : (d + 2).minFac ∣ d + 2 := Nat.minFac_dvd _
  have e4 : -(2 * (z₁ + z₂ + s)) = 0 :=
    int_eq_zero_of_log_rel (a₁ := d + 1) (a₂ := d + 3) (a₃ := (d + 2) * (d + 2) + 1)
      (a₄ := d + 2) (e₁ := 2 * z₁) (e₂ := 2 * z₂) (e₃ := s)
      (by omega) (by omega) (by positivity) (by omega) hp
      (fun h => prime_not_dvd_succ hp h hpc) (prime_not_dvd_succ hp hpc)
      (prime_not_dvd_succ hp (hpc.mul_right _)) hpc (by push_cast; linear_combination H')
  -- an odd prime factor of `c² + 1`
  obtain ⟨q, hq, hq2, hqd⟩ := exists_odd_prime_dvd_sq_add_one (c := d + 2) (by omega)
  have hq2' : ¬ q ∣ 2 := fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
  have hprod : (d + 2) * (d + 2) + 1 = (d + 1) * (d + 3) + 2 := by ring
  have hqd' : q ∣ (d + 1) * (d + 3) + 2 := hprod ▸ hqd
  have es : s = 0 :=
    int_eq_zero_of_log_rel (a₁ := d + 1) (a₂ := d + 3) (a₃ := d + 2)
      (a₄ := (d + 2) * (d + 2) + 1) (e₁ := 2 * z₁) (e₂ := 2 * z₂)
      (e₃ := -(2 * (z₁ + z₂ + s)))
      (by omega) (by omega) (by omega) (by positivity) hq
      (fun h => hq2' ((Nat.dvd_add_right (h.mul_right _)).1 hqd'))
      (fun h => hq2' ((Nat.dvd_add_right (h.mul_left _)).1 hqd'))
      (fun h => prime_not_dvd_succ hq (h.mul_right _) hqd) hqd
      (by push_cast; linear_combination H')
  -- what is left is `2 z₁ (log(c - 1) - log(c + 1)) = 0`
  have hz2 : z₂ = -z₁ := by omega
  subst hz2
  subst es
  have hlt : Real.log ((d : ℝ) + 1) < Real.log ((d : ℝ) + 3) :=
    Real.log_lt_log (by positivity) (by linarith)
  have h0 : (z₁ : ℝ) * (Real.log ((d : ℝ) + 1) - Real.log ((d : ℝ) + 3)) = 0 := by
    push_cast at H'
    linear_combination H' / 2
  rcases mul_eq_zero.1 h0 with h | h
  · have hz1 : z₁ = 0 := by exact_mod_cast h
    exact ⟨hz1, by omega, rfl⟩
  · linarith

/-! ## 3. The real part when `b` is not a square -/

theorem one_lt_sqrtB {b : ℕ} (hb : 2 ≤ b) : 1 < Real.sqrt (b : ℝ) := by
  rw [Real.lt_sqrt (by norm_num)]
  have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  linarith

theorem sqrtB_add_one_pow (b n : ℕ) : ∃ x y : ℕ,
    (Real.sqrt (b : ℝ) + 1) ^ n = x + y * Real.sqrt (b : ℝ) ∧ 0 < x ∧ (0 < n → 0 < y) := by
  induction n with
  | zero => exact ⟨1, 0, by simp, by norm_num, by simp⟩
  | succ n ih =>
    obtain ⟨x, y, h, hx, -⟩ := ih
    refine ⟨x + b * y, x + y, ?_, by positivity, fun _ => by omega⟩
    rw [pow_succ, h]
    push_cast
    linear_combination (y : ℝ) * Real.mul_self_sqrt (Nat.cast_nonneg b)

/-- If `b` is not a square, a non-zero integer power of `(√b + 1)/(√b - 1)` is irrational. -/
theorem irrational_unitB_zpow {b : ℕ} (hb : 2 ≤ b) (hsq : ¬ IsSquare b) {C : ℤ} (hC : C ≠ 0) :
    Irrational (((Real.sqrt (b : ℝ) + 1) / (Real.sqrt (b : ℝ) - 1)) ^ C) := by
  have hirr : Irrational (Real.sqrt (b : ℝ)) := irrational_sqrt_natCast_iff.2 hsq
  have ht : Real.sqrt (b : ℝ) * Real.sqrt (b : ℝ) = b := Real.mul_self_sqrt (Nat.cast_nonneg b)
  have ht1 := one_lt_sqrtB hb
  have hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := Nat.cast_pred (by omega)
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have key : ∀ n : ℕ, 0 < n →
      Irrational (((Real.sqrt (b : ℝ) + 1) / (Real.sqrt (b : ℝ) - 1)) ^ n) := by
    intro n hn
    obtain ⟨x, y, h, -, hy⟩ := sqrtB_add_one_pow b (2 * n)
    have e : ((Real.sqrt (b : ℝ) + 1) / (Real.sqrt (b : ℝ) - 1)) ^ n =
        (x + y * Real.sqrt (b : ℝ)) / (((b - 1) ^ n : ℕ) : ℝ) := by
      rw [← h, pow_mul, Nat.cast_pow, hb1, ← div_pow]
      congr 1
      rw [div_eq_div_iff (by linarith) (by linarith)]
      linear_combination (-(Real.sqrt (b : ℝ) + 1)) * ht
    rw [e]
    exact ((hirr.natCast_mul (hy (by omega)).ne').natCast_add x).div_natCast
      (pow_ne_zero n (by omega))
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg C
  · rw [zpow_natCast]
    exact key n (by omega)
  · rw [zpow_neg, zpow_natCast]
    exact (key n (by omega)).inv

/-- The case where `b` is not a square: the relation
`2 z₁ log(√b - 1) + 2 z₂ log(√b + 1) + s log(b + 1) = (z₁ + z₂ + s) log b` has only the zero
solution. -/
theorem log_rel_nonsquare {b : ℕ} (hb : 2 ≤ b) (hsq : ¬ IsSquare b) {z₁ z₂ s : ℤ}
    (H : 2 * (z₁ : ℝ) * Real.log (Real.sqrt (b : ℝ) - 1) +
        2 * z₂ * Real.log (Real.sqrt (b : ℝ) + 1) + s * Real.log ((b : ℝ) + 1) -
        (z₁ + z₂ + s) * Real.log (b : ℝ) = 0) : z₁ = 0 ∧ z₂ = 0 ∧ s = 0 := by
  have ht : Real.sqrt (b : ℝ) * Real.sqrt (b : ℝ) = b := Real.mul_self_sqrt (Nat.cast_nonneg b)
  have ht1 := one_lt_sqrtB hb
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hm : 0 < Real.sqrt (b : ℝ) - 1 := by linarith
  have hp : 0 < Real.sqrt (b : ℝ) + 1 := by linarith
  have hsum : Real.log (Real.sqrt (b : ℝ) - 1) + Real.log (Real.sqrt (b : ℝ) + 1) =
      Real.log ((b : ℝ) - 1) := by
    rw [← Real.log_mul hm.ne' hp.ne']
    congr 1
    linear_combination ht
  have hdiff : Real.log (Real.sqrt (b : ℝ) + 1) - Real.log (Real.sqrt (b : ℝ) - 1) =
      Real.log ((Real.sqrt (b : ℝ) + 1) / (Real.sqrt (b : ℝ) - 1)) :=
    (Real.log_div hp.ne' hm.ne').symm
  have hu : 0 < (Real.sqrt (b : ℝ) + 1) / (Real.sqrt (b : ℝ) - 1) := div_pos hp hm
  -- `z₁ = z₂`, since a non-zero power of `(√b + 1)/(√b - 1)` is irrational
  have key : ((z₁ + z₂ : ℤ) : ℝ) * Real.log ((b : ℝ) - 1) +
      ((z₂ - z₁ : ℤ) : ℝ) * Real.log ((Real.sqrt (b : ℝ) + 1) / (Real.sqrt (b : ℝ) - 1)) +
      (s : ℝ) * Real.log ((b : ℝ) + 1) + ((-(z₁ + z₂ + s) : ℤ) : ℝ) * Real.log (b : ℝ) = 0 := by
    push_cast
    linear_combination H - ((z₁ : ℝ) + z₂) * hsum + ((z₁ : ℝ) - z₂) * hdiff
  have hz : ∀ (x : ℝ), 0 < x → ∀ n : ℤ, Real.exp (n * Real.log x) = x ^ n :=
    fun x hx n => by rw [mul_comm, Real.exp_mul, Real.exp_log hx, Real.rpow_intCast]
  have hexp : ((b : ℝ) - 1) ^ (z₁ + z₂) *
      ((Real.sqrt (b : ℝ) + 1) / (Real.sqrt (b : ℝ) - 1)) ^ (z₂ - z₁) * ((b : ℝ) + 1) ^ s *
      (b : ℝ) ^ (-(z₁ + z₂ + s)) = 1 := by
    have h' := congrArg Real.exp key
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_zero, hz _ (by linarith), hz _ hu,
      hz _ (by linarith), hz _ (by linarith)] at h'
    exact h'
  have h12 : z₂ - z₁ = 0 := by
    by_contra hC
    apply irrational_unitB_zpow hb hsq hC
    refine ⟨(((b : ℚ) - 1) ^ (z₁ + z₂) * ((b : ℚ) + 1) ^ s * (b : ℚ) ^ (-(z₁ + z₂ + s)))⁻¹, ?_⟩
    push_cast
    exact (eq_inv_of_mul_eq_one_left (by linear_combination hexp)).symm
  obtain rfl : z₂ = z₁ := by omega
  -- a prime factor of `b`
  have hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := Nat.cast_pred (by omega)
  have hpr := Nat.minFac_prime (show b ≠ 1 by omega)
  have hpb : b.minFac ∣ b := Nat.minFac_dvd b
  have e4 : -(2 * z₂ + s) = 0 :=
    int_eq_zero_of_log_rel (a₁ := b - 1) (a₂ := b + 1) (a₃ := 1) (a₄ := b) (e₁ := 2 * z₂)
      (e₂ := s) (e₃ := 0) (by omega) (by omega) one_pos (by omega) hpr
      (fun h => prime_not_dvd_succ hpr h (by rwa [Nat.sub_add_cancel (by omega)]))
      (prime_not_dvd_succ hpr hpb) (fun h => hpr.one_lt.ne' (Nat.dvd_one.1 h)) hpb
      (by rw [hb1]; push_cast; linear_combination H - 2 * (z₂ : ℝ) * hsum)
  -- what is left is `2 z (log(b - 1) - log(b + 1)) = 0`
  have hs : s = -(2 * z₂) := by omega
  subst hs
  have hlt : Real.log ((b : ℝ) - 1) < Real.log ((b : ℝ) + 1) :=
    Real.log_lt_log (by linarith) (by linarith)
  have h0 : (z₂ : ℝ) * (Real.log ((b : ℝ) - 1) - Real.log ((b : ℝ) + 1)) = 0 := by
    push_cast at H
    linear_combination H / 2 - (z₂ : ℝ) * hsum
  rcases mul_eq_zero.1 h0 with h | h
  · have hz1 : z₂ = 0 := by exact_mod_cast h
    exact ⟨hz1, hz1, by omega⟩
  · linarith

/-! ## 4. The real part -/

/-- **`log(1 - 1/√b)`, `log(1 + 1/√b)` and `log(1 + 1/b)` are linearly independent over `ℤ`**,
for every integer `b ≥ 2`. (The factors 2 are those of the application: the real part of
`Log(1 ∓ i/√b)` is `log(1 + 1/b)/2`.) -/
theorem log_indepB {b : ℕ} (hb : 2 ≤ b) {z₁ z₂ s : ℤ}
    (h : 2 * (z₁ : ℝ) * Real.log (1 - 1 / Real.sqrt (b : ℝ)) +
        2 * z₂ * Real.log (1 + 1 / Real.sqrt (b : ℝ)) + s * Real.log (1 + 1 / (b : ℝ)) = 0) :
    z₁ = 0 ∧ z₂ = 0 ∧ s = 0 := by
  have ht1 := one_lt_sqrtB hb
  have ht0 : 0 < Real.sqrt (b : ℝ) := by linarith
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hlogt : Real.log (Real.sqrt (b : ℝ)) = Real.log (b : ℝ) / 2 :=
    Real.log_sqrt (Nat.cast_nonneg b)
  have e1 : Real.log (1 - 1 / Real.sqrt (b : ℝ)) =
      Real.log (Real.sqrt (b : ℝ) - 1) - Real.log (b : ℝ) / 2 := by
    rw [← hlogt, ← Real.log_div (by linarith) ht0.ne']
    congr 1
    field_simp
  have e2 : Real.log (1 + 1 / Real.sqrt (b : ℝ)) =
      Real.log (Real.sqrt (b : ℝ) + 1) - Real.log (b : ℝ) / 2 := by
    rw [← hlogt, ← Real.log_div (by linarith) ht0.ne']
    congr 1
    field_simp
  have e3 : Real.log (1 + 1 / (b : ℝ)) = Real.log ((b : ℝ) + 1) - Real.log (b : ℝ) := by
    rw [← Real.log_div (by linarith) hb0.ne']
    congr 1
    field_simp
  have H : 2 * (z₁ : ℝ) * Real.log (Real.sqrt (b : ℝ) - 1) +
      2 * z₂ * Real.log (Real.sqrt (b : ℝ) + 1) + s * Real.log ((b : ℝ) + 1) -
      (z₁ + z₂ + s) * Real.log (b : ℝ) = 0 := by
    rw [e1, e2, e3] at h
    linear_combination h
  by_cases hsq : IsSquare b
  · obtain ⟨c, rfl⟩ := hsq
    have hc : 2 ≤ c := by
      by_contra hlt
      have hc1 : c ≤ 1 := by omega
      nlinarith
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 2 := ⟨c - 2, by omega⟩
    have hsqrt : Real.sqrt (((d + 2) * (d + 2) : ℕ) : ℝ) = ((d + 2 : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      exact Real.sqrt_mul_self (Nat.cast_nonneg _)
    have a1 : ((d + 2 : ℕ) : ℝ) - 1 = ((d + 1 : ℕ) : ℝ) := by push_cast; ring
    have a2 : ((d + 2 : ℕ) : ℝ) + 1 = ((d + 3 : ℕ) : ℝ) := by push_cast; ring
    have a3 : (((d + 2) * (d + 2) : ℕ) : ℝ) + 1 = (((d + 2) * (d + 2) + 1 : ℕ) : ℝ) := by
      push_cast; ring
    have hl : Real.log (((d + 2) * (d + 2) : ℕ) : ℝ) = 2 * Real.log ((d + 2 : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      ring
    rw [hsqrt, a1, a2, a3, hl] at H
    exact log_rel_square d (by linear_combination H)
  · exact log_rel_nonsquare hb hsq H

/-! ## 5. The four numbers `1 - r/t`, `r⁴ = 1` -/

/-- `1 - 1/t` is the positive real number `1 - 1/√b`. -/
theorem log_re_oneB {b : ℕ} (hb : 2 ≤ b) :
    (Complex.log (1 - 1 / tB b)).re = Real.log (1 - 1 / Real.sqrt (b : ℝ)) := by
  have ht1 := one_lt_sqrtB hb
  have hpos : (0 : ℝ) < 1 - 1 / Real.sqrt (b : ℝ) := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact ht1
  have e : (1 - 1 / tB b : ℂ) = ((1 - 1 / Real.sqrt (b : ℝ) : ℝ) : ℂ) := by
    rw [tB]
    push_cast
    rfl
  rw [Complex.log_re, e, Complex.norm_real, Real.norm_of_nonneg hpos.le]

/-- `1 + 1/t` is the positive real number `1 + 1/√b`. -/
theorem log_re_neg_oneB {b : ℕ} (hb : 2 ≤ b) :
    (Complex.log (1 - (-1) / tB b)).re = Real.log (1 + 1 / Real.sqrt (b : ℝ)) := by
  have ht1 := one_lt_sqrtB hb
  have hpos : (0 : ℝ) < 1 + 1 / Real.sqrt (b : ℝ) := by positivity
  have e : (1 - (-1) / tB b : ℂ) = ((1 + 1 / Real.sqrt (b : ℝ) : ℝ) : ℂ) := by
    rw [tB]
    push_cast
    ring
  rw [Complex.log_re, e, Complex.norm_real, Real.norm_of_nonneg hpos.le]

private theorem norm_one_add_mul_I (b : ℕ) (y : ℝ) (hy : y ^ 2 = 1 / (b : ℝ)) :
    Real.log ‖((1 : ℝ) : ℂ) + (y : ℂ) * I‖ = Real.log (1 + 1 / (b : ℝ)) / 2 := by
  rw [Complex.norm_add_mul_I, one_pow, hy, Real.log_sqrt (by positivity)]

/-- `|1 - i/t|² = 1 + 1/b`. -/
theorem log_re_IB (b : ℕ) :
    (Complex.log (1 - I / tB b)).re = Real.log (1 + 1 / (b : ℝ)) / 2 := by
  have e : (1 - I / tB b : ℂ) =
      ((1 : ℝ) : ℂ) + ((-(1 / Real.sqrt (b : ℝ)) : ℝ) : ℂ) * I := by
    rw [tB]
    push_cast
    ring
  rw [Complex.log_re, e]
  refine norm_one_add_mul_I b _ ?_
  rw [neg_sq, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg b)]

/-- `|1 + i/t|² = 1 + 1/b`. -/
theorem log_re_neg_IB (b : ℕ) :
    (Complex.log (1 - (-I) / tB b)).re = Real.log (1 + 1 / (b : ℝ)) / 2 := by
  have e : (1 - (-I) / tB b : ℂ) = ((1 : ℝ) : ℂ) + ((1 / Real.sqrt (b : ℝ) : ℝ) : ℂ) * I := by
    rw [tB]
    push_cast
    ring
  rw [Complex.log_re, e]
  refine norm_one_add_mul_I b _ ?_
  rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg b)]

/-- The roots of `r⁴ = 1` are `1, -1, i, -i`. -/
theorem pow_four_ne_one {r : ℂ} (h1 : r ≠ 1) (h2 : r ≠ -1) (h3 : r ≠ I) (h4 : r ≠ -I) :
    r ^ 4 ≠ 1 := by
  intro h
  have hprod : (r - 1) * (r + 1) * (r - I) * (r + I) = 0 := by
    linear_combination h - (r ^ 2 - 1) * Complex.I_sq
  rcases mul_eq_zero.1 hprod with h' | h'
  · rcases mul_eq_zero.1 h' with h' | h'
    · rcases mul_eq_zero.1 h' with h' | h'
      · exact h1 (sub_eq_zero.1 h')
      · exact h2 (eq_neg_of_add_eq_zero_left h')
    · exact h3 (sub_eq_zero.1 h')
  · exact h4 (eq_neg_of_add_eq_zero_left h')

/-- **`(t - i)/(t + i)` is not a root of unity** for `b ≥ 4`: if
`((1 - i/t)/(1 + i/t))^n = 1` then `n = 0`. The number `w = (t - i)/(t + i)` has
`w + 1/w = 2(b - 1)/(b + 1)`, strictly between 1 and 2. -/
theorem unitB_zpow_eq_one {b : ℕ} (hb : 4 ≤ b) {n : ℤ}
    (h : ((1 - I / tB b) / (1 - (-I) / tB b)) ^ n = 1) : n = 0 := by
  by_contra hn
  have hb2 : 2 ≤ b := by omega
  have ht0 : tB b ≠ 0 := tB_ne_zero hb2
  have h1 : tB b - I ≠ 0 := tB_sub_ne_zero hb2 Complex.norm_I
  have h2 : tB b + I ≠ 0 := by
    have := tB_sub_ne_zero hb2 (r := -I) (by rw [norm_neg, Complex.norm_I])
    rwa [sub_neg_eq_add] at this
  have hw : (1 - I / tB b) / (1 - (-I) / tB b) = (tB b - I) / (tB b + I) := by
    rw [neg_div, sub_neg_eq_add]
    field_simp
  rw [hw] at h
  obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = (tB b - I) / (tB b + I) := ⟨_, rfl⟩
  rw [← hwdef] at h
  have hfin : IsOfFinOrder w := by
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, by omega, ?_⟩
      rwa [zpow_natCast] at h
    · refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, by omega, ?_⟩
      rwa [zpow_neg, zpow_natCast, inv_eq_one] at h
  have hint : IsIntegral ℤ (w + w⁻¹) :=
    (isIntegral_of_finOrder hfin).add (isIntegral_of_finOrder (isOfFinOrder_inv' hfin))
  have hb1 : (b : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero b
  have hval : w + w⁻¹ = algebraMap ℚ ℂ (2 * ((b : ℚ) - 1) / ((b : ℚ) + 1)) := by
    rw [hwdef, inv_div, div_add_div _ _ h2 h1, eq_ratCast]
    push_cast
    rw [div_eq_div_iff (mul_ne_zero h2 h1) hb1]
    linear_combination 4 * tB_sq b + 4 * (b : ℂ) * Complex.I_sq
  rw [hval, isIntegral_algebraMap_iff] at hint
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hbQ : (4 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
  have hk' : (k : ℚ) * ((b : ℚ) + 1) = 2 * ((b : ℚ) - 1) := by
    rw [eq_intCast] at hk
    rw [hk]
    field_simp
  have hk1 : (1 : ℚ) < (k : ℚ) := by
    by_contra hle
    push Not at hle
    nlinarith
  have hk2 : (k : ℚ) < 2 := by
    by_contra hle
    push Not at hle
    nlinarith
  have hk1' : (1 : ℤ) < k := by exact_mod_cast hk1
  have hk2' : k < 2 := by exact_mod_cast hk2
  omega

end BaseB

end PiFormula
