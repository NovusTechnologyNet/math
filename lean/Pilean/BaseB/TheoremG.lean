module

public import Pilean.BaseB.Classification
public import Pilean.BaseB.GoodPrimes

/-!
# Theorem G: no algebraic multiple of `π` in any base `b ≥ 5`

For every integer `b ≥ 5`, a series `∑ ρ(k) b^(-⌊k/2⌋)/k` with `ρ` rational and periodic whose
value is an algebraic multiple of `π` has all coefficients zero. In particular `π` is not a
value, there is no zero relation, and a formula of this class is unique.

The proof has three parts, in three files:

* `Size`: the size condition `SizeCond b m` for every `b ≥ 6` and `m ≥ 3`;
* `Reduction`: from the size condition, a good prime for every root of unity `r` with
  `r⁴ ≠ 1` (for `b = 5`, where the size condition fails at `m = 6`, the good primes come from
  the Aurifeuillian factors, file `Base5/GoodPrimes`);
* `Classification`: from the good primes and Baker's theorem, the statement.

The versions in the namespace `Unconditional` use the imported proof of Baker's theorem and
have no hypothesis.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace BaseB

theorem seriesTermB_zero (b : ℕ) : seriesTermB b 0 = fun _ => 0 := by
  funext k
  simp [seriesTermB]

/-- **Theorem G (from Baker's theorem).** In a base `b ≥ 5`, a series of the class `F_b` whose
value is an algebraic multiple of `π` has all coefficients zero. -/
theorem eq_zero_of_hasSum_mul_pi (hB : BakerTheorem) {b : ℕ} (hb : 5 ≤ b) {N : ℕ} (hN : 0 < N)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTermB b ρ) (γ * Real.pi)) : ρ = 0 :=
  eq_zero_of_goodPrimesB hB hb (goodPrimesB hb) hN hρ hγ h

/-- An algebraic multiple of `π` that is a value of the class `F_b`, `b ≥ 5`, is zero. -/
theorem mul_pi_eq_zero (hB : BakerTheorem) {b : ℕ} (hb : 5 ≤ b) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : IsFBValue b (γ * Real.pi)) : γ = 0 := by
  obtain ⟨N, ρ, hN, hρ, hs⟩ := h
  have h0 := eq_zero_of_hasSum_mul_pi hB hb hN hρ hγ hs
  rw [h0, seriesTermB_zero] at hs
  rcases mul_eq_zero.1 (hs.unique hasSum_zero) with h1 | h1
  · exact h1
  · exact absurd h1 Real.pi_ne_zero

namespace Unconditional

/-- **Theorem G.** For every integer `b ≥ 5`: if a series `∑ ρ(k) b^(-⌊k/2⌋)/k` with `ρ`
rational and periodic has the value `γ π` with `γ` algebraic, then `ρ = 0`. -/
theorem eq_zero_of_hasSum_mul_pi {b : ℕ} (hb : 5 ≤ b) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTermB b ρ) (γ * Real.pi)) : ρ = 0 :=
  BaseB.eq_zero_of_hasSum_mul_pi bakerTheorem hb hN hρ hγ h

/-- An algebraic multiple of `π` that is a value of the class `F_b`, `b ≥ 5`, is zero. -/
theorem mul_pi_eq_zero {b : ℕ} (hb : 5 ≤ b) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : IsFBValue b (γ * Real.pi)) : γ = 0 :=
  BaseB.mul_pi_eq_zero bakerTheorem hb hγ h

/-- **`π` is not the value of any series `∑ ρ(k) b^(-⌊k/2⌋)/k`, for every base `b ≥ 5`.** -/
theorem not_isFBValue_pi {b : ℕ} (hb : 5 ≤ b) : ¬ IsFBValue b Real.pi := by
  intro h
  have h1 : IsFBValue b ((1 : ℝ) * Real.pi) := by rwa [one_mul]
  exact one_ne_zero (mul_pi_eq_zero hb isAlgebraic_one h1)

/-- **No zero relation in a base `b ≥ 5`:** a series of the class with sum 0 has all
coefficients zero. -/
theorem eq_zero_of_hasSum_zero {b : ℕ} (hb : 5 ≤ b) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) (h : HasSum (seriesTermB b ρ) 0) : ρ = 0 := by
  have h1 : HasSum (seriesTermB b ρ) ((0 : ℝ) * Real.pi) := by rwa [zero_mul]
  exact eq_zero_of_hasSum_mul_pi hb hN hρ isAlgebraic_zero h1

/-- A series of the class `F_b`, `b ≥ 5`, has sum 0 exactly when all its coefficients are
zero. -/
theorem hasSum_zero_iff {b : ℕ} (hb : 5 ≤ b) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) : HasSum (seriesTermB b ρ) 0 ↔ ρ = 0 :=
  hasSum_zero_iff_of_goodPrimesB bakerTheorem hb (goodPrimesB hb) hN hρ

/-- **A number has at most one formula in a base `b ≥ 5`:** two rational periodic patterns
with the same sum are equal. -/
theorem eq_of_hasSum {b : ℕ} (hb : 5 ≤ b) {N N' : ℕ} (hN : 0 < N) (hN' : 0 < N')
    {ρ ρ' : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) (hρ' : ∀ k, ρ' (k + N') = ρ' k) {x : ℝ}
    (h : HasSum (seriesTermB b ρ) x) (h' : HasSum (seriesTermB b ρ') x) : ρ = ρ' :=
  eq_of_hasSum_of_goodPrimesB bakerTheorem hb (goodPrimesB hb) hN hN' hρ hρ' h h'

/-- **In a base `b ≥ 5` every series of the class with a non-zero pattern has a
transcendental sum.** -/
theorem transcendental_of_hasSum {b : ℕ} (hb : 5 ≤ b) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) (hρ0 : ρ ≠ 0) {x : ℝ} (h : HasSum (seriesTermB b ρ) x) :
    Transcendental ℚ x :=
  transcendental_of_hasSum_of_goodPrimesB bakerTheorem hb (goodPrimesB hb) hN hρ hρ0 h

/-- In every base `b ≥ 2`, a non-zero value of the class `F_b` is transcendental. -/
theorem transcendental_of_isFBValue {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (h : IsFBValue b x)
    (hx : x ≠ 0) : Transcendental ℚ x :=
  BaseB.transcendental_of_isFBValue bakerTheorem hb h hx

end Unconditional

end BaseB

end PiFormula
