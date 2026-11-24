/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Base3.Halves

/-!
# Base 5: shared definitions

The class F5 is the set of series `∑ ρ(k) 5^(-⌊k/2⌋)/k` with `ρ` rational and periodic. This
file fixes the definitions and statements that the other files of `Pilean/Base5` share, so
that they can be developed independently:

* `t5 = √5`, with `t5² = 5`;
* `seriesTerm5`, `IsF5Value`;
* `HasGoodPrime5 r`: a prime ideal of the algebraic integers contains `t5 - r` and an odd
  rational prime `p ≠ 5` that does not divide the order of `r`;
* `GoodPrimes5`: every root of unity other than `1` and `-1` has a good prime;
* `L5 h`, `M5 h`: the two Aurifeuillian factors of `Φ_5(5^h) = 5^(4h) + 5^(3h) + 5^(2h) + 5^h + 1`
  for odd `h`;
* `PrimitiveHalves5`: for every odd `h`, each of `L5 h`, `M5 h` has a prime factor `p` with
  `ord_p(5) = 5h`.

Nothing is proved here beyond the first properties of `t5`. See Part VI of
`notes/pi_formula_theorem.md` for the mathematics.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace Base5

/-! ## 1. `t = √5` -/

/-- `t = √5`. -/
noncomputable def t5 : ℂ := ((Real.sqrt 5 : ℝ) : ℂ)

theorem t5_sq : t5 ^ 2 = 5 := by
  rw [t5, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem norm_t5 : ‖t5‖ = Real.sqrt 5 := by
  rw [t5, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 5)]

theorem one_lt_norm_t5 : 1 < ‖t5‖ := by
  rw [norm_t5, Real.lt_sqrt (by norm_num)]
  norm_num

theorem t5_ne_zero : t5 ≠ 0 := by
  intro h
  have h1 := one_lt_norm_t5
  rw [h, norm_zero] at h1
  linarith

theorem isAlgebraic_t5 : IsAlgebraic ℚ t5 := by
  refine ⟨X ^ 2 - C 5, ?_, ?_⟩
  · intro h
    have h0 := congrArg (Polynomial.eval 0) h
    simp at h0
  · simp [t5_sq]

theorem isIntegral_t5 : IsIntegral ℤ t5 := by
  refine ⟨X ^ 2 - C 5, monic_X_pow_sub_C 5 (by norm_num), ?_⟩
  simp [t5_sq]

theorem isIntegral_t5_sub {r : ℂ} (hr : IsOfFinOrder r) : IsIntegral ℤ (t5 - r) :=
  isIntegral_t5.sub (isIntegral_of_finOrder hr)

theorem t5_sub_ne_zero {r : ℂ} (hr : ‖r‖ = 1) : t5 - r ≠ 0 := by
  intro h
  have h1 : t5 = r := sub_eq_zero.1 h
  have h2 := one_lt_norm_t5
  rw [h1, hr] at h2
  exact lt_irrefl _ h2

theorem norm_div_t5_lt {r : ℂ} (hr : ‖r‖ = 1) : ‖r / t5‖ < 1 := by
  rw [norm_div, hr]
  exact (div_lt_one (by linarith [one_lt_norm_t5])).2 one_lt_norm_t5

/-! ## 2. The class F5 -/

/-- The term `ρ(k) 5^(-⌊k/2⌋) / k` of the series. -/
noncomputable def seriesTerm5 (ρ : ℕ → ℚ) (k : ℕ) : ℝ := (ρ k : ℝ) / 5 ^ (k / 2) / k

/-- `x` is the value of a series of the class F5. -/
def IsF5Value (x : ℝ) : Prop :=
  ∃ (N : ℕ) (ρ : ℕ → ℚ), 0 < N ∧ (∀ k, ρ (k + N) = ρ k) ∧ HasSum (seriesTerm5 ρ) x

/-! ## 3. Good primes -/

/-- A good prime for the root of unity `r`: a prime ideal `P` of the algebraic integers that
contains `t5 - r` and an odd rational prime `p ≠ 5` not dividing the order of `r`. -/
def HasGoodPrime5 (r : ℂ) : Prop :=
  ∃ P : Ideal Aint, P.IsPrime ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ 5 ∧ ¬ p ∣ orderOf r ∧
    InP P (p : ℂ) ∧ InP P (t5 - r)

/-- Every root of unity other than `1` and `-1` has a good prime. -/
def GoodPrimes5 : Prop := ∀ r : ℂ, IsOfFinOrder r → r ≠ 1 → r ≠ -1 → HasGoodPrime5 r

/-! ## 4. The Aurifeuillian factors of base 5 -/

/-- `L_h = 5^(2h) + 3·5^h + 1 - 5^((h+1)/2) (5^h + 1)`. -/
def L5 (h : ℕ) : ℤ := 5 ^ (2 * h) + 3 * 5 ^ h + 1 - 5 ^ ((h + 1) / 2) * (5 ^ h + 1)

/-- `M_h = 5^(2h) + 3·5^h + 1 + 5^((h+1)/2) (5^h + 1)`. -/
def M5 (h : ℕ) : ℤ := 5 ^ (2 * h) + 3 * 5 ^ h + 1 + 5 ^ ((h + 1) / 2) * (5 ^ h + 1)

/-- `L_h M_h = 5^(4h) + 5^(3h) + 5^(2h) + 5^h + 1` for odd `h`. -/
theorem L5_mul_M5 {h : ℕ} (hh : Odd h) :
    L5 h * M5 h = 5 ^ (4 * h) + 5 ^ (3 * h) + 5 ^ (2 * h) + 5 ^ h + 1 := by
  obtain ⟨k, rfl⟩ := hh
  have e : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h5 : (5 : ℤ) ^ (2 * k + 1) = 5 * (5 ^ k) ^ 2 := by ring
  simp only [L5, M5, e]
  have e2 : (5 : ℤ) ^ (2 * (2 * k + 1)) = (5 ^ (2 * k + 1)) ^ 2 := by ring
  have e3 : (5 : ℤ) ^ (3 * (2 * k + 1)) = (5 ^ (2 * k + 1)) ^ 3 := by ring
  have e4 : (5 : ℤ) ^ (4 * (2 * k + 1)) = (5 ^ (2 * k + 1)) ^ 4 := by ring
  have e1 : (5 : ℤ) ^ (k + 1) = 5 * 5 ^ k := by ring
  rw [e2, e3, e4, e1, h5]
  ring

theorem L5_one : L5 1 = 11 := by decide

theorem M5_one : M5 1 = 71 := by decide

/-- **The lemma on primes for base 5** (a statement; proved in `Base5/Halves.lean`). For every
odd `h`, each of the two Aurifeuillian factors `L_h`, `M_h` has a prime factor `p` with
`ord_p(5) = 5h`. -/
def PrimitiveHalves5 : Prop :=
  ∀ h : ℕ, Odd h →
    (∃ p : ℕ, p.Prime ∧ orderOf (5 : ZMod p) = 5 * h ∧ (p : ℤ) ∣ L5 h) ∧
      (∃ p : ℕ, p.Prime ∧ orderOf (5 : ZMod p) = 5 * h ∧ (p : ℤ) ∣ M5 h)

end Base5

end PiFormula
