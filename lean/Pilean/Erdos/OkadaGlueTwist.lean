module

public import Pilean.Erdos.OkadaGlue

/-!
# Okada's criterion: the sum stays `0` when `f` is twisted by a unit

`okadaTwistInvariance_of`: `OkadaTwistInvariance` follows from `OkadaSumZero`,
`OkadaFourierLimit` and `OkadaBakerTwist`.

Proof. Let `S_N(f) → 0`. Then `∑_r f(r) = 0`, so `S_N(f) → -Λ(f^)` with
`Λ(c) = ∑_{a ≠ 0} c(a) Log(1 - ζ^a)`; hence `Λ(f^) = 0`. By `OkadaBakerTwist` (for the unit
`h⁻¹`) `Λ(a ↦ f^(h⁻¹ a)) = 0`. The Fourier transform of `f_h : n ↦ f(h n)` is `a ↦ f^(h⁻¹ a)`
(`fourierCoeff_twistBy`) and `∑_r f_h(r) = ∑_r f(r) = 0`, so `S_N(f_h) → -Λ(f_h^) = 0`.
-/

@[expose] public section

open scoped BigOperators

open Filter

namespace PiFormula

namespace Erdos

namespace Okada

/-- The sum over a period does not change when `f` is twisted by a unit. -/
theorem sum_twistBy (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (h : (ZMod q)ˣ) :
    ∑ r : ZMod q, twistBy q f h r = ∑ r : ZMod q, f r :=
  Fintype.sum_equiv (Units.mulLeft h) _ _ fun _ => rfl

/-- The Fourier transform of `n ↦ f(h n)` is `a ↦ f^(h⁻¹ a)`. -/
theorem fourierCoeff_twistBy (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (h : (ZMod q)ˣ)
    (a : ZMod q) :
    fourierCoeff q (twistBy q f h) a = fourierCoeff q f (((h⁻¹ : (ZMod q)ˣ) : ZMod q) * a) := by
  unfold fourierCoeff
  congr 1
  refine Fintype.sum_equiv (Units.mulLeft h) _ _ fun r => ?_
  have e : a * r = ((h⁻¹ : (ZMod q)ˣ) : ZMod q) * a * ((h : ZMod q) * r) := by
    have h1 : ((h⁻¹ : (ZMod q)ˣ) : ZMod q) * (h : ZMod q) = 1 := h.inv_mul
    linear_combination (-(a * r)) * h1
  simp only [twistBy, Units.mulLeft_apply]
  rw [e]

end Okada

open Okada

/-- **The first half**: if `∑ f(n)/n = 0` then `∑ f(h n)/n = 0` for every unit `h`. -/
theorem okadaTwistInvariance_of (h0 : OkadaSumZero) (h1 : OkadaFourierLimit)
    (h2 : OkadaBakerTwist) : OkadaTwistInvariance := by
  intro q _ hq f hf0 hS h
  have hsum : ∑ r : ZMod q, f r = 0 := h0 q hq f hf0 hS
  have hlim := h1 q hq f hf0 hsum
  have hS' : Tendsto (fun N : ℕ => ((partialSum q f N : ℝ) : ℂ)) atTop (nhds ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp hS
  rw [Complex.ofReal_zero] at hS'
  have hform : logForm q (fourierCoeff q f) = 0 :=
    neg_eq_zero.1 (tendsto_nhds_unique hlim hS')
  have hB := h2 q hq f hf0 hsum hform h⁻¹
  have hsum' : ∑ r : ZMod q, twistBy q f h r = 0 := by rw [sum_twistBy]; exact hsum
  have hlim' := h1 q hq (twistBy q f h) (twistBy_zero q hf0 h) hsum'
  have e : logForm q (fourierCoeff q (twistBy q f h)) = 0 := by
    rw [← hB]
    unfold logForm
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [fourierCoeff_twistBy]
  rw [e, neg_zero] at hlim'
  have hre := (Complex.continuous_re.tendsto 0).comp hlim'
  rw [Complex.zero_re] at hre
  exact hre.congr fun N => Complex.ofReal_re _

end Erdos

end PiFormula
