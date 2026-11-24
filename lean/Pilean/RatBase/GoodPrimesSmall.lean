module

public import Pilean.RatBase.SmallDefs
public import Pilean.RatBase.ClassificationR

/-!
# Good primes in every rational base outside `2, 3, 4, 3/2, 4/3`, from two statements

`goodPrimesR_of_small`: for coprime `p > q ≥ 1` other than the five bases with relations,
`GoodPrimesR p q` holds, given the two statements `SizeSmall` and `LeftoverGood` of
`SmallDefs.lean`. Four cases: `p ≥ 16` (`goodPrimesR`); `q = 1` and `p ≥ 5` (the good primes of
`Pilean/BaseB`); a triple of the list (`LeftoverGood`); otherwise the size condition
(`SizeSmall`) and the reduction.

The consequences (no relation, `π` is not a value) are stated here from the two statements
and from Baker's theorem as a hypothesis.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace RatBase

/-- A good prime in the integer base `p` is a good prime in the rational base `p/1`. -/
theorem hasGoodPrimeR_one {p : ℕ} {r : ℂ} (h : BaseB.HasGoodPrimeB p r) :
    HasGoodPrimeR p 1 r := by
  obtain ⟨P, hP, ℓ, hℓ, hℓ2, hℓp, hℓr, hℓP, hxP⟩ := h
  refine ⟨P, hP, ℓ, hℓ, hℓ2, ?_, hℓr, hℓP, ?_⟩
  · simpa using hℓp
  · simpa using hxP

/-- **Good primes in every rational base outside the five**, from the two statements. -/
theorem goodPrimesR_of_small (hS : SizeSmall) (hL : LeftoverGood) {p q : ℕ} (hq : 0 < q)
    (hqp : q < p) (hcop : Nat.Coprime p q) (hex : ¬ IsExceptional p q) : GoodPrimesR p q := by
  intro r hr h4
  by_cases hp : 16 ≤ p
  · exact goodPrimesR hp hq hqp hcop r hr h4
  by_cases hq1 : q = 1
  · subst hq1
    have hp5 : 5 ≤ p := by
      unfold IsExceptional at hex
      omega
    exact hasGoodPrimeR_one (BaseB.goodPrimesB hp5 r hr h4)
  have hm := BaseB.three_le_orderOf_sq hr h4
  by_cases hmem : (p, q, orderOf (r ^ 2)) ∈ leftoverTriples
  · exact hL p q _ hmem r hr rfl
  · have h32 : ¬ (p = 3 ∧ q = 2) := fun h => hex (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have h43 : ¬ (p = 4 ∧ q = 3) := fun h => hex (Or.inr (Or.inr (Or.inr (Or.inr h))))
    exact hasGoodPrimeR_of_sizeCondR hq hqp hcop hr h4
      (hS p q _ (by omega) (by omega) hqp hcop h32 h43 hm hmem)

/-- **No relation in a rational base outside the five**, from Baker's theorem and the two
statements. -/
theorem eq_zero_of_small (hB : BakerTheorem) (hS : SizeSmall) (hL : LeftoverGood) {p q : ℕ}
    (hq : 0 < q) (hqp : q < p) (hcop : Nat.Coprime p q) (hex : ¬ IsExceptional p q) {N : ℕ}
    (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTermRat p q ρ) (γ * Real.pi)) : ρ = 0 :=
  eq_zero_of_goodPrimesR hB hq hqp hcop (fun h31 => hex (Or.inr (Or.inl h31)))
    (goodPrimesR_of_small hS hL hq hqp hcop hex) hN hρ hγ h

end RatBase

end PiFormula
