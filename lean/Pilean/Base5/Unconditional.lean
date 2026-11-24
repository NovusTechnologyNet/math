/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Base5.Classification
public import Pilean.Base5.GoodPrimes
public import Pilean.Base5.Halves
public import Pilean.PiFormula.Unconditional

/-!
# Base 5: no formula for a multiple of `π`, and no zero relation

F5 is the class of series `S(ρ) = ∑ ρ(k) 5^(-⌊k/2⌋)/k` with `ρ` rational and periodic.

**Theorem C5.** If `S(ρ) = γ π` with `γ` algebraic, then `ρ = 0`. So:

* `π` is not a value of F5, nor is any non-zero algebraic multiple of `π`;
* F5 has no zero relation: `S(ρ) = 0` only for `ρ = 0`;
* a number has at most one formula of this class: two periodic patterns with the same sum are
  equal.

This is the opposite of base 2 (the formulas for `π` form a space of dimension 8) and of base 3
(`π√3` is a value and there are two zero relations).

The proof has the same three parts as in base 3.

* `Halves.lean`, `Zeta5.lean`: for every odd `h`, each of the two Aurifeuillian factors of
  `Φ_5(5^h)` has a prime factor `p` with `ord_p(5) = 5h` (`primitiveHalves5`).
* `GoodPrimes.lean`: hence every root of unity other than `1` and `-1` has a good prime
  (`goodPrimes5_of_halves`).
* `Support.lean`, `Classification.lean`: hence a multiplicative relation among the numbers
  `1 - r/√5` is supported on `1` and `-1`, where there is none (`log_indep5`); Baker's theorem
  then gives the statement.

The theorems of this file in the namespace `PiFormula.Base5` take `BakerTheorem` as a
hypothesis; those in `PiFormula.Base5.Unconditional` use the formal proof of Baker's theorem
in `Baker/` and depend only on Lean's three standard axioms.
-/

@[expose] public section

namespace PiFormula

namespace Base5

/-- Every root of unity other than `1` and `-1` has a good prime (no hypothesis). -/
theorem goodPrimes5 : GoodPrimes5 := goodPrimes5_of_halves primitiveHalves5

/-- **Theorem C5 (from Baker's theorem).** If a series of the class F5 has the value `γ π` with
`γ` algebraic, then all its coefficients are zero. -/
theorem eq_zero_of_hasSum_mul_pi (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTerm5 ρ) (γ * Real.pi)) : ρ = 0 :=
  eq_zero_of_goodPrimes5 hB goodPrimes5 hN hρ hγ h

/-- **No zero relation in base 5** (from Baker's theorem). -/
theorem hasSum_zero_iff (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) : HasSum (seriesTerm5 ρ) 0 ↔ ρ = 0 :=
  hasSum_zero_iff_of_goodPrimes5 hB goodPrimes5 hN hρ

/-- **A number has at most one formula in base 5** (from Baker's theorem). -/
theorem eq_of_hasSum (hB : BakerTheorem) {N N' : ℕ} (hN : 0 < N) (hN' : 0 < N')
    {ρ ρ' : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) (hρ' : ∀ k, ρ' (k + N') = ρ' k) {x : ℝ}
    (h : HasSum (seriesTerm5 ρ) x) (h' : HasSum (seriesTerm5 ρ') x) : ρ = ρ' :=
  eq_of_hasSum_of_goodPrimes5 hB goodPrimes5 hN hN' hρ hρ' h h'

/-- **No non-zero algebraic multiple of `π` is a value of F5** (from Baker's theorem). -/
theorem mul_pi_eq_zero (hB : BakerTheorem) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : IsF5Value (γ * Real.pi)) : γ = 0 :=
  mul_pi_eq_zero_of_goodPrimes5 hB goodPrimes5 hγ h

/-- **`π` is not the value of any series of the class F5** (from Baker's theorem). -/
theorem not_isF5Value_pi (hB : BakerTheorem) : ¬ IsF5Value Real.pi :=
  not_isF5Value_pi_of_goodPrimes5 hB goodPrimes5

namespace Unconditional

/-- **Theorem C5.** If a rational periodic pattern `ρ` has
`∑ ρ(k) 5^(-⌊k/2⌋)/k = γ π` with `γ` algebraic, then `ρ = 0`. -/
theorem eq_zero_of_hasSum_mul_pi {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTerm5 ρ) (γ * Real.pi)) : ρ = 0 :=
  Base5.eq_zero_of_hasSum_mul_pi bakerTheorem hN hρ hγ h

/-- **No zero relation in base 5.** A rational periodic pattern has
`∑ ρ(k) 5^(-⌊k/2⌋)/k = 0` only if it is zero. -/
theorem hasSum_zero_iff {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (seriesTerm5 ρ) 0 ↔ ρ = 0 :=
  Base5.hasSum_zero_iff bakerTheorem hN hρ

/-- **A number has at most one formula in base 5.** Two rational periodic patterns whose
series have the same sum are equal. -/
theorem eq_of_hasSum {N N' : ℕ} (hN : 0 < N) (hN' : 0 < N') {ρ ρ' : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) (hρ' : ∀ k, ρ' (k + N') = ρ' k) {x : ℝ}
    (h : HasSum (seriesTerm5 ρ) x) (h' : HasSum (seriesTerm5 ρ') x) : ρ = ρ' :=
  Base5.eq_of_hasSum bakerTheorem hN hN' hρ hρ' h h'

/-- **No non-zero algebraic multiple of `π` is a value of F5.** -/
theorem mul_pi_eq_zero {γ : ℝ} (hγ : IsAlgebraic ℚ γ) (h : IsF5Value (γ * Real.pi)) : γ = 0 :=
  Base5.mul_pi_eq_zero bakerTheorem hγ h

/-- **`π` is not the value of any series `∑ ρ(k) 5^(-⌊k/2⌋)/k` with `ρ` rational and
periodic.** -/
theorem not_isF5Value_pi : ¬ IsF5Value Real.pi :=
  Base5.not_isF5Value_pi bakerTheorem

end Unconditional

end Base5

end PiFormula
