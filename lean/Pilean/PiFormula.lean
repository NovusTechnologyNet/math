/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Mathlib

/-!
# Binary Machin-type formulas for π: the first file

Everything in this file is either a complete proof or the *statement* of a claim
(a `def ... : Prop`). Nothing is assumed: there is no `sorry` and no axiom.

Checked here:

* §1: the three formulas R1, R2, R3 and Euler's formula hold;
* §2: every combination allowed by the classification really is a relation;
* §3: Aurifeuille's factorization `L_n * M_n = 4^n + 1` for every odd `n`;
* §4: the Gaussian-integer factorizations used in the finite core;
* §5: the small cases of Lemma 2;
* §6: the linear algebra of Corollary B2 (nothing is faster than 3/2; uniqueness);
* §6b: the value of the cheaper formula of Part III (Euler's plus a series for zero).

Stated here and proved in later files:

* §7: Bang's theorem (`PiFormula.bang`, in `PiFormula/Bang.lean`), Lemma 2 and Theorem A
  (`PiFormula.lemma2`, `PiFormula.theoremA`, in `PiFormula/Lemma2.lean`).

The written proof is in `notes/pi_formula_theorem.md`.
-/

@[expose] public section

open Real

namespace PiFormula

/-! ## §1. The formulas hold -/

theorem R1 : arctan 1 = π / 4 := arctan_one

theorem R2 : arctan (1 / 2) + arctan (1 / 3) = π / 4 := by
  simpa using arctan_inv_2_add_arctan_inv_3

theorem R3 : 2 * arctan (1 / 2) - arctan (1 / 7) = π / 4 := by
  simpa using two_mul_arctan_inv_2_sub_arctan_inv_7

/-- Euler's formula, the fastest one. -/
theorem euler : 2 * arctan (1 / 3) + arctan (1 / 7) = π / 4 := by
  simpa using two_mul_arctan_inv_3_add_arctan_inv_7

/-! ## §2. The "easy direction" of the classification

If the coefficients of arctan(1/2), arctan(1), arctan(1/3), arctan(1/7) satisfy the
one linear condition, the combination is a rational multiple of π. -/

theorem combination_is_relation (b₁ a₁ a₂ a₃ : ℝ) (h : b₁ - a₂ + 2 * a₃ = 0) :
    b₁ * arctan (1 / 2) + a₁ * arctan 1 + a₂ * arctan (1 / 3) + a₃ * arctan (1 / 7)
      = (a₁ + a₂ - a₃) / 4 * π := by
  linear_combination a₁ * R1 + a₂ * R2 - a₃ * R3 + arctan (1 / 2) * h

/-! ## §3. Aurifeuille's factorization -/

/-- For odd n = 2k+1: (2^n - 2^((n+1)/2) + 1) * (2^n + 2^((n+1)/2) + 1) = 4^n + 1. -/
theorem aurifeuille (k : ℕ) :
    ((2 : ℤ) ^ (2 * k + 1) - 2 ^ (k + 1) + 1) * (2 ^ (2 * k + 1) + 2 ^ (k + 1) + 1)
      = 4 ^ (2 * k + 1) + 1 := by
  have hb : ((2 : ℤ) ^ (k + 1)) ^ 2 = 2 * 2 ^ (2 * k + 1) := by ring
  have h4 : (4 : ℤ) ^ (2 * k + 1) = (2 ^ (2 * k + 1)) ^ 2 := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
    exact pow_right_comm 2 2 (2 * k + 1)
  rw [h4]
  linear_combination (-1 : ℤ) * hb

/-! ## §4. Gaussian-integer factorizations in the finite core

`⟨a, b⟩` is the Gaussian integer a + b i. -/

/-- (2 + i)(3 + i) = 5(1 + i): gives arctan(1/2) + arctan(1/3) = π/4. -/
theorem gauss_R2 : (⟨2, 1⟩ : GaussianInt) * ⟨3, 1⟩ = ⟨5, 5⟩ := by decide

/-- (3 + i)^2 (7 + i) = 50(1 + i): gives Euler's formula. -/
theorem gauss_euler : (⟨3, 1⟩ : GaussianInt) ^ 2 * ⟨7, 1⟩ = ⟨50, 50⟩ := by decide

/-- 3 + i = (1 + i)(2 - i). -/
theorem gauss_3 : (⟨3, 1⟩ : GaussianInt) = ⟨1, 1⟩ * ⟨2, -1⟩ := by decide

/-- 7 + i = -i (1 + i)(2 + i)^2. -/
theorem gauss_7 : (⟨7, 1⟩ : GaussianInt) = ⟨0, -1⟩ * ⟨1, 1⟩ * ⟨2, 1⟩ ^ 2 := by decide

/-- 8 + i = (2 - i)(3 + 2i): the prime 13 appears in no other surviving generator. -/
theorem gauss_8 : (⟨8, 1⟩ : GaussianInt) = ⟨2, -1⟩ * ⟨3, 2⟩ := by decide

/-- 32 + i = -i (2 + i)^2 (5 + 4i): the prime 41 appears in no other surviving generator. -/
theorem gauss_32 : (⟨32, 1⟩ : GaussianInt) = ⟨0, -1⟩ * ⟨2, 1⟩ ^ 2 * ⟨5, 4⟩ := by decide

/-- The elementary identity (2^m - 1 + i)(2^m + 1 - i) = 2(2^(2m-1) + i), at m = 4. -/
theorem gauss_trivial_4 : (⟨15, 1⟩ : GaussianInt) * ⟨17, -1⟩ = ⟨2, 0⟩ * ⟨128, 1⟩ := by decide

/-! ## §5. Small cases of Lemma 2 -/

/-- L_n = 2^n - 2^((n+1)/2) + 1. -/
def L (n : ℕ) : ℤ := 2 ^ n - 2 ^ ((n + 1) / 2) + 1

/-- M_n = 2^n + 2^((n+1)/2) + 1. -/
def M (n : ℕ) : ℤ := 2 ^ n + 2 ^ ((n + 1) / 2) + 1

/-- The exceptional values: L_1, L_3, L_5 have no primitive prime factor. -/
theorem L_small : L 1 = 1 ∧ L 3 = 5 ∧ L 5 = 25 := by decide

theorem M_small : M 1 = 5 ∧ M 3 = 13 ∧ M 5 = 41 := by decide

/-- 5 is primitive for 4: the order of 2 modulo 5 is 4. -/
theorem order_two_mod_5 : (2 : ZMod 5) ^ 4 = 1 ∧ (2 : ZMod 5) ^ 2 ≠ 1 := by decide

/-- 13 is primitive for 12. -/
theorem order_two_mod_13 :
    (2 : ZMod 13) ^ 12 = 1 ∧ (2 : ZMod 13) ^ 6 ≠ 1 ∧ (2 : ZMod 13) ^ 4 ≠ 1 := by decide

/-- 41 is primitive for 20. -/
theorem order_two_mod_41 :
    (2 : ZMod 41) ^ 20 = 1 ∧ (2 : ZMod 41) ^ 10 ≠ 1 ∧ (2 : ZMod 41) ^ 4 ≠ 1 := by decide

/-! ## §6. Corollary B2: the speed bound

A cyclotomic-type series for π is α·γ(O₁) + β·γ(O₆) + δ·(γ(O₁₀) - γ(O₂)). Its terms
with gcd(k, 60) = 1, 2, 3 are multiples of the three expressions below. -/

/-- Speed above 3/2 is impossible: the three slow coefficients vanish only for the zero series. -/
theorem no_series_faster_than_three_halves (α β δ : ℚ)
    (h₁ : α + β + 2 * δ = 0) (h₂ : α - β - 2 * δ = 0) (h₃ : α - 2 * β + 2 * δ = 0) :
    α = 0 ∧ β = 0 ∧ δ = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Speed exactly 3/2 forces a multiple of (0, -2, 1), which is Euler's formula. -/
theorem fastest_series_is_unique (α β δ : ℚ)
    (h₁ : α + β + 2 * δ = 0) (h₂ : α - β - 2 * δ = 0) :
    α = 0 ∧ β = -2 * δ := by
  constructor <;> linarith

/-! ## §6b. The cheaper formula of Part III

The new formula is Euler's plus a combination Z of logarithms whose value is zero
(its *series* is not zero term by term, which is the whole point). This section checks the
value; the series itself, `π/4 = ∑ ρ(k) 2^(-⌊k/2⌋) / k` with the 120-periodic `ρ`, is
`new_formula_series` in `PiFormula/NewFormula.lean`. -/

/-- Z = 2 log(1/2) - 2 log(1/2) + log(3/4) - log(3/2) + log 2 = 0. -/
theorem zero_series_value :
    2 * Real.log (1 / 2) - 2 * Real.log (1 / 2) + Real.log (3 / 4) - Real.log (3 / 2)
      + Real.log 2 = 0 := by
  have h1 : Real.log (3 / 4) = Real.log 3 - Real.log 4 :=
    Real.log_div (by norm_num) (by norm_num)
  have h2 : Real.log (3 / 2) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  have h3 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h1, h2, h3]
  ring

/-- The cheaper formula has the value π/4. -/
theorem new_formula :
    2 * arctan (1 / 3) + arctan (1 / 7)
      + (2 * Real.log (1 / 2) - 2 * Real.log (1 / 2) + Real.log (3 / 4) - Real.log (3 / 2)
          + Real.log 2) = π / 4 := by
  rw [zero_series_value, add_zero]
  exact euler

/-! ## §7. Statements proved in later files (`PiFormula/Bang.lean`, `PiFormula/Lemma2.lean`) -/

/-- Bang's theorem (1886): for N ≥ 2, N ≠ 6, some prime p has 2 of order exactly N. -/
def BangTheorem : Prop :=
  ∀ N : ℕ, 2 ≤ N → N ≠ 6 → ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = N

/-- A prime is primitive for 4n if 2 has order exactly 4n modulo it. -/
def IsPrimitiveFor (p n : ℕ) : Prop := p.Prime ∧ orderOf (2 : ZMod p) = 4 * n

/-- Lemma 2: M_n always has a primitive prime factor; L_n does for odd n ≥ 7. -/
def Lemma2 : Prop :=
  (∀ n : ℕ, Odd n → ∃ p : ℕ, IsPrimitiveFor p n ∧ (p : ℤ) ∣ M n) ∧
  (∀ n : ℕ, Odd n → 7 ≤ n → ∃ p : ℕ, IsPrimitiveFor p n ∧ (p : ℤ) ∣ L n)

/-- The value of a formal rational combination of the generators
arctan(1/2^m) (coefficients `b`) and arctan(1/(2^m - 1)) (coefficients `a`). -/
noncomputable def value (b a : ℕ →₀ ℚ) : ℝ :=
  (b.sum fun m c => (c : ℝ) * arctan (1 / (2 : ℝ) ^ m)) +
  (a.sum fun m c => (c : ℝ) * arctan (1 / ((2 : ℝ) ^ m - 1)))

/-- Theorem A. If a rational combination of the generators (indices m ≥ 1) equals q·π,
then only arctan(1/2), arctan(1), arctan(1/3), arctan(1/7) occur, their coefficients
satisfy b₁ - a₂ + 2a₃ = 0, and q = (a₁ + a₂ - a₃)/4. Together with
`combination_is_relation` this is the full classification. -/
def TheoremA : Prop :=
  ∀ (b a : ℕ →₀ ℚ) (q : ℚ), b 0 = 0 → a 0 = 0 → value b a = q * π →
    (∀ m, 2 ≤ m → b m = 0) ∧ (∀ m, 4 ≤ m → a m = 0) ∧
    b 1 - a 2 + 2 * a 3 = 0 ∧ q = (a 1 + a 2 - a 3) / 4

/-- The target of the formalization. -/
def Goal : Prop := BangTheorem → Lemma2 → TheoremA

end PiFormula
