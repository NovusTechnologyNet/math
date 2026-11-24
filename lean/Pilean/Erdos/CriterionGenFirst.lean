/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.OkadaFourier
public import Pilean.Erdos.OkadaBaker
public import Pilean.Erdos.OkadaGlueTwist
public import Pilean.Erdos.EvenCase

/-!
# Okada's criterion for every `q ≥ 1`: the first half

The statements of `OkadaDefs.lean` carry the hypotheses `Odd q` and `f 0 = 0`, which no proof
uses. This file states and proves the first half of the criterion without them, for every
modulus `q ≥ 1` and every rational function `f` on `ℤ/q`:

* `fourierLimit_gen`: if `∑_r f(r) = 0`, then `∑ f(n)/n = -∑_{a ≠ 0} f^(a) Log(1 - ζ^a)`;
* `bakerTwist_gen`: if `∑_{a ≠ 0} f^(a) Log(1 - ζ^a) = 0`, the same holds with `f^(h a)`,
  for every unit `h` (Baker's theorem and the Galois group of `ℚ(ζ_q)`);
* `twistInvariance_gen`: if `∑ f(n)/n = 0`, then `∑ f(h n)/n = 0` for every unit `h`.

The proofs are those of `okadaFourierLimit` (`OkadaFourier.lean`), `okadaBakerTwist`
(`OkadaBaker.lean`) and `okadaTwistInvariance_of` (`OkadaGlueTwist.lean`), with the lemmas of
these files; only the last lines are repeated. The second half is `CriterionGenSecond.lean`
and the criterion is `okadaCriterionGeneral` (`CriterionGeneral.lean`).
-/

@[expose] public section

open scoped BigOperators

open Filter Finset

namespace PiFormula

namespace Erdos

open Okada

/-- **The value of the series**, for every `q ≥ 1`. If `∑_r f(r) = 0`, the partial sums of
`∑ f(n)/n` tend to `-∑_{a ≠ 0} f^(a) Log(1 - ζ^a)`. -/
theorem fourierLimit_gen (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (hsum : ∑ r : ZMod q, f r = 0) :
    Tendsto (fun N : ℕ => ((partialSum q f N : ℝ) : ℂ)) atTop
      (nhds (-logForm q (Okada.fourierCoeff q f))) := by
  have h0 : Okada.fourierCoeff q f 0 = 0 := by
    unfold Okada.fourierCoeff
    simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
    rw [← Rat.cast_sum, hsum, Rat.cast_zero, mul_zero]
  have hterm : ∀ a : ZMod q, Tendsto (fun N : ℕ => Okada.fourierCoeff q f a *
      ∑ n ∈ range N, (ZMod.stdAddChar a : ℂ) ^ n / (n : ℂ)) atTop
      (nhds (-(if a = 0 then 0 else
        Okada.fourierCoeff q f a * Complex.log (1 - ZMod.stdAddChar a)))) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      simp only [↓reduceIte, h0, zero_mul, neg_zero]
      exact tendsto_const_nhds
    · simp only [ha, ↓reduceIte]
      have hn : ‖(ZMod.stdAddChar a : ℂ)‖ = 1 := by
        rw [ZMod.stdAddChar_apply]
        exact Circle.norm_coe _
      have h1 : (ZMod.stdAddChar a : ℂ) ≠ 1 := fun h =>
        ha (ZMod.injective_stdAddChar (by rw [AddChar.map_zero_eq_one]; exact h))
      have h2 := (tendsto_circle_log hn h1).const_mul (Okada.fourierCoeff q f a)
      rwa [mul_neg] at h2
  have hlim := tendsto_finsetSum (Finset.univ : Finset (ZMod q)) fun a _ => hterm a
  have hval : ∑ a : ZMod q, -(if a = 0 then 0 else
      Okada.fourierCoeff q f a * Complex.log (1 - ZMod.stdAddChar a)) =
      -logForm q (Okada.fourierCoeff q f) := by
    unfold logForm
    rw [Finset.sum_neg_distrib]
  rw [hval] at hlim
  refine hlim.congr fun N => ?_
  unfold partialSum
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← fourier_inversion_zmod q f (n : ZMod q), Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : (ZMod.stdAddChar (a * (n : ZMod q)) : ℂ) = ZMod.stdAddChar a ^ n := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]
  rw [e]
  ring

/-- **Baker's theorem and the Galois group of `ℚ(ζ_q)`**, for every `q ≥ 1`: a vanishing
linear form `∑_{a ≠ 0} f^(a) Log(1 - ζ^a)` still vanishes when `f^(a)` is replaced by
`f^(h a)`, for a unit `h`. -/
theorem bakerTwist_gen (q : ℕ) [NeZero q] (f : ZMod q → ℚ)
    (hform : logForm q (Okada.fourierCoeff q f) = 0) (h : (ZMod q)ˣ) :
    logForm q (fun a => Okada.fourierCoeff q f ((h : ZMod q) * a)) = 0 := by
  classical
  obtain ⟨σ, hσ⟩ := exists_embedding_pow q (ZMod.val_coe_unit_coprime h)
  let T : Finset (ZMod q) := Finset.univ.filter fun a => a ≠ 0
  let lam : ZMod q → ℂ := fun a => Complex.log (1 - ZMod.stdAddChar a)
  let β : ZMod q → ℂ := fun a => if a = 0 then 0 else ((coeffF q f a : fieldQ q) : ℂ)
  have hT0 : ∀ a ∈ T, a ≠ 0 := fun a ha => (Finset.mem_filter.1 ha).2
  have hT : ∀ c : ZMod q → ℂ, logForm q c = ∑ a ∈ T, c a * lam a := by
    intro c
    unfold logForm
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a = 0
    · simp only [ha, ↓reduceIte, ne_eq, not_true_eq_false]
    · simp only [ha, ↓reduceIte, ne_eq, not_false_eq_true, lam]
  have hβ : ∀ a ∈ T, β a = ((coeffF q f a : fieldQ q) : ℂ) := by
    intro a ha
    simp only [β, hT0 a ha, ↓reduceIte]
  have hexp : ∀ a ∈ T, IsAlgebraic ℚ (Complex.exp (lam a)) := by
    intro a ha
    have hne : (1 : ℂ) - ZMod.stdAddChar a ≠ 0 := fun h0 =>
      hT0 a ha (ZMod.injective_stdAddChar (by
        rw [AddChar.map_zero_eq_one]
        exact (sub_eq_zero.1 h0).symm))
    change IsAlgebraic ℚ (Complex.exp (Complex.log (1 - ZMod.stdAddChar a)))
    rw [Complex.exp_log hne, stdAddChar_eq_pow]
    exact isAlgebraic_one.sub ((isIntegral_zetaQ q).isAlgebraic.pow _)
  have hβF : ∀ a ∈ T, β a ∈ fieldQ q := by
    intro a ha
    rw [hβ a ha]
    exact (coeffF q f a).2
  have hβ0 : ∀ a, a ∉ T → β a = 0 := by
    intro a ha
    have ha0 : a = 0 := by
      by_contra hne
      exact ha (Finset.mem_filter.2 ⟨Finset.mem_univ a, hne⟩)
    simp only [β, ha0, ↓reduceIte]
  have hsum : ∑ a ∈ T, β a * lam a = 0 := by
    rw [← hform, hT]
    exact Finset.sum_congr rfl fun a ha => by rw [hβ a ha, coe_coeffF]
  have hspan := baker_descent bakerTheorem (fieldQ q)
    (fun x hx => isAlgebraic_of_mem_fieldQ q hx) lam T hexp β hβF hβ0 hsum
  obtain ⟨-, hconj⟩ := BaseB.conj_relationF σ hspan
  rw [hT, ← hconj]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [hβ a ha, BaseB.extF_coe, sigma_coeffF q f h hσ]

/-- **The first half of Okada's criterion**, for every `q ≥ 1` and every rational `f` on
`ℤ/q`: if `∑ f(n)/n = 0` then `∑ f(h n)/n = 0` for every unit `h` modulo `q`. -/
theorem twistInvariance_gen (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (hS : SumIsZero q f)
    (h : (ZMod q)ˣ) : SumIsZero q (twistBy q f h) := by
  have hsum : ∑ r : ZMod q, f r = 0 := sum_period_eq_zero_of_tendsto q f hS
  have hlim := fourierLimit_gen q f hsum
  have hS' : Tendsto (fun N : ℕ => ((partialSum q f N : ℝ) : ℂ)) atTop (nhds ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp hS
  rw [Complex.ofReal_zero] at hS'
  have hform : logForm q (Okada.fourierCoeff q f) = 0 :=
    neg_eq_zero.1 (tendsto_nhds_unique hlim hS')
  have hB := bakerTwist_gen q f hform h⁻¹
  have hsum' : ∑ r : ZMod q, twistBy q f h r = 0 := by rw [sum_twistBy]; exact hsum
  have hlim' := fourierLimit_gen q (twistBy q f h) hsum'
  have e : logForm q (Okada.fourierCoeff q (twistBy q f h)) = 0 := by
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
