/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.RatBase.ClassificationR
public import Pilean.RatBase.GoodPrimesR

/-!
# No relation in a rational base `p/q` with `p ≥ 16`

**Theorem** (`Unconditional.eq_zero_of_hasSum_mul_pi`). Let `p > q ≥ 1` be coprime integers
with `p ≥ 16`. If a series `∑ ρ(k) (q/p)^⌊k/2⌋ / k` with `ρ` rational and periodic has the
value `γ π` with `γ` algebraic, then `ρ = 0`. So in the rational base `p/q`: `π` is not a
value, nor is any non-zero algebraic multiple of `π`; there is no zero relation; and a number
has at most one formula.

For `q = 1` this is Theorem G of `BaseB` (there for every `b ≥ 5`). The bound `p ≥ 16` is where
the size condition is proved (`SizeR`); the bases with `p ≤ 15` are not treated here. Five of
them, `2, 3, 4, 3/2, 4/3`, do have relations: see `ThreeHalves` and `FourThirds`.

Baker's theorem is used through the imported proof; there is no hypothesis.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace RatBase

namespace Unconditional

/-- **No relation in a rational base `p/q` with `p ≥ 16`.** -/
theorem eq_zero_of_hasSum_mul_pi {p q : ℕ} (hp : 16 ≤ p) (hq : 0 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k)
    {γ : ℝ} (hγ : IsAlgebraic ℚ γ) (h : HasSum (seriesTermRat p q ρ) (γ * Real.pi)) : ρ = 0 :=
  eq_zero_of_goodPrimesR bakerTheorem hq hqp hcop (fun h31 => by omega)
    (goodPrimesR hp hq hqp hcop) hN hρ hγ h

/-- An algebraic multiple of `π` that is a value of the class of the base `p/q`, `p ≥ 16`, is
zero. -/
theorem mul_pi_eq_zero {p q : ℕ} (hp : 16 ≤ p) (hq : 0 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) {γ : ℝ} (hγ : IsAlgebraic ℚ γ) (h : IsFRValue p q (γ * Real.pi)) :
    γ = 0 :=
  mul_pi_eq_zero_of_goodPrimesR bakerTheorem hq hqp hcop (fun h31 => by omega)
    (goodPrimesR hp hq hqp hcop) hγ h

/-- **`π` is not a value in a rational base `p/q` with `p ≥ 16`.** -/
theorem not_isFRValue_pi {p q : ℕ} (hp : 16 ≤ p) (hq : 0 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) : ¬ IsFRValue p q Real.pi :=
  not_isFRValue_pi_of_goodPrimesR bakerTheorem hq hqp hcop (fun h31 => by omega)
    (goodPrimesR hp hq hqp hcop)

/-- **No zero relation in a rational base `p/q` with `p ≥ 16`.** -/
theorem hasSum_zero_iff {p q : ℕ} (hp : 16 ≤ p) (hq : 0 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (seriesTermRat p q ρ) 0 ↔ ρ = 0 :=
  hasSum_zero_iff_of_goodPrimesR bakerTheorem hq hqp hcop (fun h31 => by omega)
    (goodPrimesR hp hq hqp hcop) hN hρ

end Unconditional

end RatBase

end PiFormula
