import Pilean.RatBase.GoodPrimesSmall
import Pilean.RatBase.SizeSmall
import Pilean.RatBase.Leftover
import Pilean.RatBase.Four
import Pilean.RatBase.ThreeHalves
import Pilean.Base3.Dimension
import Pilean.PiFormula.Unconditional

/-!
# Theorem R: the rational bases with a relation are exactly `2, 3, 4, 3/2, 4/3`

For coprime integers `p > q ≥ 1`, the class of the rational base `p/q` is the set of series
`∑_{k ≥ 1} ρ(k) (q/p)^⌊k/2⌋ / k` with `ρ` rational and periodic. A *relation* in the base `p/q`
(`HasRelation p q`) is such a series with `ρ ≠ 0` whose value is `γ π` for an algebraic number
`γ`; `γ = 0` (a zero relation) is allowed.

**Theorem R** (`hasRelation_iff`). The base `p/q` has a relation if and only if `p/q` is one of
`2, 3, 4, 3/2, 4/3`.

So in every other rational base (`TheoremR.eq_zero_of_hasSum_mul_pi` and its corollaries): no
series of the class has the value `π` or a non-zero algebraic multiple of `π`, there is no zero
relation, and a number has at most one formula. There is no hypothesis: Baker's theorem is
used through the imported proof.

The proof of "only if": good primes for every root of unity outside `1, -1, i, -i`
(`goodPrimesR_all`), from four cases: `p ≥ 16` (size condition, `SizeR.lean`); `q = 1`, `p ≥ 5`
(the integer bases, `Pilean/BaseB`); `2 ≤ q < p ≤ 15` outside twelve triples (size condition by
an analytic bound and a table, `SizeSmall.lean`); the twelve triples (a primitive prime factor
and a conjugation, `Leftover.lean`). Then the classification from good primes and Baker's
theorem (`ClassificationR.lean`).

"If": a relation in each of the five bases.

| base | pattern | value | theorem |
|---|---|---|---|
| 2 | `namedA1` (the pattern of Bailey, Borwein and Plouffe's formula) | `π/4` | `hasSum_namedA1` |
| 3 | `rhoGregory` | `π√3` | `Base3.hasSum_gregory3` |
| 4 | `(1/2, 1, 0, -1, -1/2, 0)` | `π√3/9` | `hasSum_rhoFour` |
| 3/2 | `rhoTH`, period 24 | `π/4` | `hasSum_rhoTH` |
| 4/3 | `rhoFT`, period 12 | `π√3/9` | `hasSum_rhoFT` |

Not proved here: which of the five bases have a formula for a rational multiple of `π` (bases
2 and 3/2 do, base 3 does not by `Base3`; bases 4 and 4/3 are not classified in Lean), and
Bailey's form with an arbitrary exponent and length for rational bases.
-/

open Complex

namespace PiFormula

namespace RatBase

/-- **Good primes in every rational base outside `2, 3, 4, 3/2, 4/3`.** -/
theorem goodPrimesR_all {p q : ℕ} (hq : 0 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (hex : ¬ IsExceptional p q) : GoodPrimesR p q :=
  goodPrimesR_of_small sizeSmall leftoverGood hq hqp hcop hex

/-- A relation in the rational base `p/q`: a series `∑ ρ(k) (q/p)^⌊k/2⌋ / k` with `ρ` rational,
periodic and not zero, whose value is an algebraic multiple of `π` (possibly `0`). -/
def HasRelation (p q : ℕ) : Prop :=
  ∃ (N : ℕ) (ρ : ℕ → ℚ), 0 < N ∧ (∀ k, ρ (k + N) = ρ k) ∧ ρ ≠ 0 ∧
    ∃ γ : ℝ, IsAlgebraic ℚ γ ∧ HasSum (seriesTermRat p q ρ) (γ * Real.pi)

namespace TheoremR

/-- **No relation in a rational base outside the five.** If a series of the class of the base
`p/q` has the value `γ π` with `γ` algebraic, then all its coefficients are zero. -/
theorem eq_zero_of_hasSum_mul_pi {p q : ℕ} (hq : 0 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (hex : ¬ IsExceptional p q) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k)
    {γ : ℝ} (hγ : IsAlgebraic ℚ γ) (h : HasSum (seriesTermRat p q ρ) (γ * Real.pi)) : ρ = 0 :=
  eq_zero_of_small bakerTheorem sizeSmall leftoverGood hq hqp hcop hex hN hρ hγ h

/-- An algebraic multiple of `π` that is a value of the class of a base outside the five is
zero. -/
theorem mul_pi_eq_zero {p q : ℕ} (hq : 0 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (hex : ¬ IsExceptional p q) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : IsFRValue p q (γ * Real.pi)) : γ = 0 :=
  mul_pi_eq_zero_of_goodPrimesR bakerTheorem hq hqp hcop
    (fun h31 => hex (Or.inr (Or.inl h31))) (goodPrimesR_all hq hqp hcop hex) hγ h

/-- **`π` is not a value in a rational base outside the five.** -/
theorem not_isFRValue_pi {p q : ℕ} (hq : 0 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (hex : ¬ IsExceptional p q) : ¬ IsFRValue p q Real.pi :=
  not_isFRValue_pi_of_goodPrimesR bakerTheorem hq hqp hcop
    (fun h31 => hex (Or.inr (Or.inl h31))) (goodPrimesR_all hq hqp hcop hex)

/-- **No zero relation in a rational base outside the five.** -/
theorem hasSum_zero_iff {p q : ℕ} (hq : 0 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (hex : ¬ IsExceptional p q) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) : HasSum (seriesTermRat p q ρ) 0 ↔ ρ = 0 :=
  hasSum_zero_iff_of_goodPrimesR bakerTheorem hq hqp hcop
    (fun h31 => hex (Or.inr (Or.inl h31))) (goodPrimesR_all hq hqp hcop hex) hN hρ

end TheoremR

/-! ## A relation in each of the five bases -/

/-- A pattern whose series has a non-zero value is not zero. -/
theorem pattern_ne_zero_of_hasSum {p q : ℕ} {ρ : ℕ → ℚ} {x : ℝ}
    (h : HasSum (seriesTermRat p q ρ) x) (hx : x ≠ 0) : ρ ≠ 0 := by
  rintro rfl
  have h0 : seriesTermRat p q 0 = fun _ => 0 := by
    funext k
    simp [seriesTermRat]
  rw [h0] at h
  exact hx (h.unique hasSum_zero)

theorem seriesTermRat_two_one (ρ : ℕ → ℚ) : seriesTermRat 2 1 ρ = seriesTerm ρ := by
  funext k
  simp [seriesTermRat, seriesTerm, div_eq_mul_inv]

theorem seriesTermRat_three_one (ρ : ℕ → ℚ) : seriesTermRat 3 1 ρ = Base3.seriesTerm3 ρ := by
  funext k
  simp [seriesTermRat, Base3.seriesTerm3, div_eq_mul_inv]

theorem sqrt_three_pos' : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

/-- Base 2: the pattern of the formula of Bailey, Borwein and Plouffe, with value `π/4`. -/
theorem hasRelation_two : HasRelation 2 1 := by
  have h : HasSum (seriesTermRat 2 1 namedA1) (((1 / 4 : ℚ) : ℝ) * Real.pi) := by
    rw [seriesTermRat_two_one]
    convert hasSum_namedA1 using 1
    push_cast
    ring
  refine ⟨120, namedA1, by norm_num, fun k => (named_periodic k).1, ?_, _,
    isAlgebraic_ratCast ℚ (A := ℝ) (1 / 4), h⟩
  exact pattern_ne_zero_of_hasSum h (by positivity)

/-- Base 3: the Gregory-type series, with value `π√3`. -/
theorem hasRelation_three : HasRelation 3 1 := by
  have h : HasSum (seriesTermRat 3 1 Base3.rhoGregory) (Real.sqrt 3 * Real.pi) := by
    rw [seriesTermRat_three_one, mul_comm]
    exact Base3.hasSum_gregory3
  refine ⟨4, Base3.rhoGregory, by norm_num, Base3.rhoGregory_periodic, ?_, _,
    Base3.isAlgebraic_sqrt3_real, h⟩
  exact pattern_ne_zero_of_hasSum h (mul_pos sqrt_three_pos' Real.pi_pos).ne'

/-- Base 4: the series of `Four.lean`, with value `π√3/9`. -/
theorem hasRelation_four : HasRelation 4 1 := by
  have h : HasSum (seriesTermRat 4 1 rhoFour) (Real.sqrt 3 * ((1 / 9 : ℚ) : ℝ) * Real.pi) := by
    convert hasSum_rhoFour using 1
    push_cast
    ring
  refine ⟨6, rhoFour, by norm_num, rhoFour_periodic, ?_, _,
    Base3.isAlgebraic_sqrt3_real.mul (isAlgebraic_ratCast ℚ (A := ℝ) (1 / 9)), h⟩
  refine pattern_ne_zero_of_hasSum h ?_
  have := sqrt_three_pos'
  positivity

/-- Base 3/2: the series of `ThreeHalves.lean`, with value `π/4`. -/
theorem hasRelation_three_halves : HasRelation 3 2 := by
  have h : HasSum (seriesTermRat 3 2 rhoTH) (((1 / 4 : ℚ) : ℝ) * Real.pi) := by
    convert hasSum_rhoTH using 1
    push_cast
    ring
  refine ⟨24, rhoTH, by norm_num, rhoTH_periodic, ?_, _,
    isAlgebraic_ratCast ℚ (A := ℝ) (1 / 4), h⟩
  exact pattern_ne_zero_of_hasSum h (by positivity)

/-- Base 4/3: the series of `FourThirds.lean`, with value `π√3/9`. -/
theorem hasRelation_four_thirds : HasRelation 4 3 := by
  have h : HasSum (seriesTermRat 4 3 rhoFT) (Real.sqrt 3 * ((1 / 9 : ℚ) : ℝ) * Real.pi) := by
    convert hasSum_rhoFT using 1
    push_cast
    ring
  refine ⟨12, rhoFT, by norm_num, rhoFT_periodic, ?_, _,
    Base3.isAlgebraic_sqrt3_real.mul (isAlgebraic_ratCast ℚ (A := ℝ) (1 / 9)), h⟩
  refine pattern_ne_zero_of_hasSum h ?_
  have := sqrt_three_pos'
  positivity

/-! ## Theorem R -/

/-- **Theorem R.** For coprime `p > q ≥ 1`, the rational base `p/q` has a relation if and only
if it is one of `2, 3, 4, 3/2, 4/3`. -/
theorem hasRelation_iff {p q : ℕ} (hq : 0 < q) (hqp : q < p) (hcop : Nat.Coprime p q) :
    HasRelation p q ↔ IsExceptional p q := by
  constructor
  · rintro ⟨N, ρ, hN, hρ, hne, γ, hγ, h⟩
    by_contra hex
    exact hne (TheoremR.eq_zero_of_hasSum_mul_pi hq hqp hcop hex hN hρ hγ h)
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hasRelation_two
    · exact hasRelation_three
    · exact hasRelation_four
    · exact hasRelation_three_halves
    · exact hasRelation_four_thirds

end RatBase

end PiFormula
