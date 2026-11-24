/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Mathlib

/-!
# The order of 2 modulo a prime, and the norms of the generators

The facts about `orderOf (2 : ZMod p)` that the "largest index" argument of Theorem A
uses (pi_formula_theorem.md, Fact 3), and the norms of the generators:

* `N(2^m + i) = 4^m + 1`, and `N(2^m - 1 + i) = 2 * L(2m - 1)` with
  `L(n) * M(n) = 4^n + 1` (Aurifeuille), `L(n) = 2^n - 2^((n+1)/2) + 1`,
  `M(n) = 2^n + 2^((n+1)/2) + 1` for odd `n`.
* If 2 has order `4n` modulo `p`, then `p ∣ 4^n + 1`, `p ≡ 1 (mod 4)`, and `p ∣ 4^m + 1`
  forces `n ∣ m` with `m / n` odd.
-/

@[expose] public section

namespace PiFormula

section Orders

variable {p : ℕ} [hp : Fact p.Prime]

theorem two_ne_zero_of_orderOf {n : ℕ} (hn : 0 < n) (h : orderOf (2 : ZMod p) = 4 * n) :
    (2 : ZMod p) ≠ 0 := by
  intro h2
  rw [h2, orderOf_eq_zero_iff'.2 (fun k hk => by simp [zero_pow hk.ne'])] at h
  omega

theorem ne_two_of_orderOf {n : ℕ} (hn : 0 < n) (h : orderOf (2 : ZMod p) = 4 * n) : p ≠ 2 := by
  rintro rfl
  exact two_ne_zero_of_orderOf hn h rfl

theorem two_pow_two_mul_eq_neg_one {n : ℕ} (hn : 0 < n) (h : orderOf (2 : ZMod p) = 4 * n) :
    (2 : ZMod p) ^ (2 * n) = -1 := by
  have h1 : (2 : ZMod p) ^ (4 * n) = 1 := h ▸ pow_orderOf_eq_one _
  have h2 : (2 : ZMod p) ^ (2 * n) ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have h3 : (2 : ZMod p) ^ (2 * n) * (2 : ZMod p) ^ (2 * n) = 1 := by
    rw [← pow_add, show 2 * n + 2 * n = 4 * n by ring, h1]
  rcases mul_self_eq_one_iff.1 h3 with h4 | h4
  · exact absurd h4 h2
  · exact h4

/-- If 2 has order `4n` modulo `p`, then `p ∣ 4^n + 1`. -/
theorem dvd_four_pow_add_one_of_orderOf {n : ℕ} (hn : 0 < n)
    (h : orderOf (2 : ZMod p) = 4 * n) : p ∣ 4 ^ n + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [show (4 : ZMod p) ^ n = (2 : ZMod p) ^ (2 * n) by rw [pow_mul]; norm_num,
    two_pow_two_mul_eq_neg_one hn h]
  ring

/-- If 2 has order `4n` modulo `p`, then `p ≡ 1 (mod 4)`. -/
theorem mod_four_eq_one_of_orderOf {n : ℕ} (hn : 0 < n) (h : orderOf (2 : ZMod p) = 4 * n) :
    p % 4 = 1 := by
  have hd := ZMod.orderOf_dvd_card_sub_one (two_ne_zero_of_orderOf hn h)
  rw [h] at hd
  obtain ⟨k, hk⟩ := (Dvd.intro _ rfl : 4 ∣ 4 * n).trans hd
  have := hp.out.two_le
  omega

/-- If 2 has order `4n` modulo `p` and `p ∣ 4^m + 1`, then `n ∣ m` and `m / n` is odd. -/
theorem dvd_and_odd_of_orderOf {n m : ℕ} (hn : 0 < n) (h : orderOf (2 : ZMod p) = 4 * n)
    (hm : p ∣ 4 ^ m + 1) : n ∣ m ∧ Odd (m / n) := by
  have hp2 := ne_two_of_orderOf hn h
  have h2m : (2 : ZMod p) ^ (2 * m) = -1 := by
    have := (ZMod.natCast_eq_zero_iff _ _).2 hm
    push_cast at this
    rw [pow_mul]
    norm_num
    linear_combination this
  have h4m : (2 : ZMod p) ^ (4 * m) = 1 := by
    rw [show 4 * m = 2 * m + 2 * m by ring, pow_add, h2m]
    norm_num
  have hdvd : n ∣ m := by
    have := orderOf_dvd_of_pow_eq_one h4m
    rw [h] at this
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  refine ⟨hdvd, ?_⟩
  obtain ⟨k, rfl⟩ := hdvd
  rw [Nat.mul_div_cancel_left _ hn]
  by_contra hk
  obtain ⟨j, rfl⟩ := Nat.not_odd_iff_even.1 hk
  have h1 : (2 : ZMod p) ^ (4 * n) = 1 := h ▸ pow_orderOf_eq_one _
  have : (2 : ZMod p) ^ (2 * (n * (j + j))) = 1 := by
    rw [show 2 * (n * (j + j)) = 4 * n * j by ring, pow_mul, h1, one_pow]
  rw [h2m] at this
  have hcontr := this
  have : Fact (2 < p) := ⟨by have := hp.out.two_le; omega⟩
  exact ZMod.neg_one_ne_one hcontr

theorem le_of_orderOf {n m : ℕ} (hn : 0 < n) (hm0 : 0 < m) (h : orderOf (2 : ZMod p) = 4 * n)
    (hm : p ∣ 4 ^ m + 1) : n ≤ m :=
  Nat.le_of_dvd hm0 (dvd_and_odd_of_orderOf hn h hm).1

end Orders

section Norms

/-- `L(n) = 2^n - 2^((n+1)/2) + 1` for odd `n`, in ℕ. -/
def Ln (n : ℕ) : ℕ := 2 ^ n - 2 ^ ((n + 1) / 2) + 1

/-- `M(n) = 2^n + 2^((n+1)/2) + 1`. -/
def Mn (n : ℕ) : ℕ := 2 ^ n + 2 ^ ((n + 1) / 2) + 1

theorem two_pow_half_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ ((n + 1) / 2) ≤ 2 ^ n :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Aurifeuille: `L(2m-1) * M(2m-1) = 4^(2m-1) + 1`. -/
theorem Ln_mul_Mn (m : ℕ) (hm : 1 ≤ m) : Ln (2 * m - 1) * Mn (2 * m - 1) = 4 ^ (2 * m - 1) + 1 := by
  have hh : (2 * m - 1 + 1) / 2 = m := by omega
  have hle : 2 ^ m ≤ 2 ^ (2 * m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (2 * m - 1) * 2 = 2 ^ m * 2 ^ m := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  have h4 : (4 : ℕ) ^ (2 * m - 1) = 2 ^ (2 * m - 1) * 2 ^ (2 * m - 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]; congr 1; omega
  have h2' : (2 : ℤ) ^ (2 * m - 1) * 2 = 2 ^ m * 2 ^ m := by exact_mod_cast h2
  unfold Ln Mn
  rw [hh, h4]
  zify [hle]
  linear_combination h2'

/-- `N(2^m - 1 + i) = (2^m - 1)^2 + 1 = 2 * L(2m - 1)`. -/
theorem sq_add_one_eq_two_mul_Ln (m : ℕ) (hm : 1 ≤ m) :
    (2 ^ m - 1) ^ 2 + 1 = 2 * Ln (2 * m - 1) := by
  have hh : (2 * m - 1 + 1) / 2 = m := by omega
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hle : 2 ^ m ≤ 2 ^ (2 * m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (2 * m - 1) * 2 = 2 ^ m * 2 ^ m := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  have h2' : (2 : ℤ) ^ (2 * m - 1) * 2 = 2 ^ m * 2 ^ m := by exact_mod_cast h2
  unfold Ln
  rw [hh]
  zify [h1, hle]
  linear_combination -h2'

theorem Ln_odd (m : ℕ) (hm : 2 ≤ m) : Odd (Ln (2 * m - 1)) := by
  unfold Ln
  have hh : (2 * m - 1 + 1) / 2 = m := by omega
  rw [hh]
  have hle : 2 ^ m ≤ 2 ^ (2 * m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : Even (2 ^ (2 * m - 1)) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have e2 : Even (2 ^ m) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  exact ((Nat.even_sub hle).2 ⟨fun _ => e2, fun _ => e1⟩).add_one

/-- A prime dividing both `L(2m-1)` and `M(2m-1)` does not exist (`m ≥ 2`). -/
theorem not_dvd_Ln_and_Mn (m : ℕ) (hm : 2 ≤ m) {p : ℕ} (hp : p.Prime)
    (hL : p ∣ Ln (2 * m - 1)) (hM : p ∣ Mn (2 * m - 1)) : False := by
  have hh : (2 * m - 1 + 1) / 2 = m := by omega
  have hle : 2 ^ m ≤ 2 ^ (2 * m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdiff : Mn (2 * m - 1) = Ln (2 * m - 1) + 2 ^ (m + 1) := by
    unfold Ln Mn; rw [hh, pow_succ]; omega
  rw [hdiff] at hM
  have h2 : p ∣ 2 ^ (m + 1) := (Nat.dvd_add_right hL).1 hM
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
  subst hp2
  exact (Nat.not_even_iff_odd.2 (Ln_odd m hm)) (even_iff_two_dvd.2 hL)

end Norms

end PiFormula
