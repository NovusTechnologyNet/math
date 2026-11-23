import Pilean.Erdos.OkadaDefs

/-!
# Okada's criterion, the direction "sum `= 0` implies (a) and (b)": the main deduction

`okadaOnlyIf_of_main`: `OkadaOnlyIf` follows from five of the propositions of `OkadaDefs.lean`:

* `OkadaTwistInvariance`: if `∑ f(n)/n = 0` then `∑ f(h n)/n = 0` for every unit `h`;
* `OkadaUnitReduction`: `S_N(f) - S'_N(g) → -(1/q) ∑_{p ∣ q} ℓ_p log p`;
* `OkadaLayerSum`: `ℓ_p = c_p`;
* `OkadaUnitNonvanishing`: if `S'_N(n ↦ u(h n)) → c` for every unit `h` then `c = 0` and
  `u = 0` on the units;
* `OkadaLogPrimes`: the logarithms of the primes are linearly independent over `ℚ`.

Proof. Let `S_N(f) → 0`. For a unit `h`, `S_N(f_h) → 0`; the function `g` of `f_h` is
`r ↦ g(h r)` (`okadaG_twistBy`) and its `ℓ_p` is that of `f` (`layerSum_twistBy`), so
`S'_N(n ↦ g(h n)) → (1/q) ∑_p ℓ_p log p` for every `h`. Hence `∑_p ℓ_p log p = 0` and `g = 0`
on the units, which is condition (a); and `∑_{p ∣ q} c_p log p = 0` gives `c_p = 0` for all
`p`, which is (b).

The other deductions are in `OkadaGlueTwist.lean` (`OkadaTwistInvariance`),
`OkadaGlueChar.lean` (`OkadaUnitNonvanishing`) and `OkadaGlueWindow.lean`.
-/

open scoped BigOperators

open Filter

namespace PiFormula

namespace Erdos

namespace Okada

/-- The function `g` of `n ↦ f(h n)` is `r ↦ g(h r)`. -/
theorem okadaG_twistBy (q : ℕ) (f : ZMod q → ℚ) (h : (ZMod q)ˣ) (a : ZMod q) :
    okadaG q (twistBy q f h) a = okadaG q f ((h : ZMod q) * a) := by
  simp only [okadaG, twistBy, mul_assoc]

theorem twistBy_zero (q : ℕ) {f : ZMod q → ℚ} (h0 : f 0 = 0) (h : (ZMod q)ˣ) :
    twistBy q f h 0 = 0 := by
  simp only [twistBy, mul_zero, h0]

/-- Multiplication by a unit maps the set of the `r` divisible by `p` and by no other prime
factor of `q` to itself. -/
theorem mem_layer_unit_mul (q : ℕ) [NeZero q] (p : ℕ) (h : (ZMod q)ˣ) (r : ZMod q) :
    r ∈ layer q p ↔ (h : ZMod q) * r ∈ layer q p := by
  simp only [layer, Finset.mem_filter, Finset.mem_univ, true_and, Units.dvd_mul_left]

/-- `ℓ_p` does not change when `f` is twisted by a unit. -/
theorem layerSum_twistBy (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (h : (ZMod q)ˣ) (p : ℕ) :
    layerSum q (twistBy q f h) p = layerSum q f p := by
  unfold layerSum
  refine Finset.sum_equiv (Units.mulLeft h) (fun r => mem_layer_unit_mul q p h r) fun r _ => ?_
  rw [okadaG_twistBy, Units.mulLeft_apply]

end Okada

open Okada

/-- **The main deduction.** -/
theorem okadaOnlyIf_of_main (hT : OkadaTwistInvariance) (hR : OkadaUnitReduction)
    (hL : OkadaLayerSum) (hU : OkadaUnitNonvanishing) (hP : OkadaLogPrimes) :
    OkadaOnlyIf := by
  intro q hq f h0 hS
  have : NeZero q := ⟨hq.pos.ne'⟩
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.pos.ne'
  -- for every unit `h`, the sums of `g(h n)/n` over the `n` prime to `q` tend to the same
  -- number
  have key : ∀ h : (ZMod q)ˣ,
      Tendsto (unitSum q fun n => okadaG q f ((h : ZMod q) * n)) atTop
        (nhds ((∑ p ∈ q.primeFactors, layerSum q f p * Real.log (p : ℝ)) / (q : ℝ))) := by
    intro h
    have h1 : Tendsto (partialSum q (twistBy q f h)) atTop (nhds 0) := hT q hq f h0 hS h
    have h2 := hR q hq (twistBy q f h) (twistBy_zero q h0 h)
    have h3 := h1.sub h2
    simp only [layerSum_twistBy, zero_sub, neg_neg] at h3
    refine h3.congr fun N => ?_
    rw [sub_sub_cancel]
    simp only [unitSum, okadaG_twistBy]
  obtain ⟨hc, hg⟩ := hU q hq (okadaG q f) _ key
  refine ⟨?_, ?_⟩
  · -- condition (a)
    rintro a ⟨u, rfl⟩
    exact hg u
  · -- condition (b)
    have hD : ∑ p ∈ q.primeFactors, layerSum q f p * Real.log (p : ℝ) = 0 := by
      rcases div_eq_zero_iff.1 hc with h | h
      · exact h
      · exact absurd h hqR
    have hsum : ∑ p ∈ q.primeFactors, (okadaC q f p : ℝ) * Real.log (p : ℝ) = 0 := by
      rw [← hD]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := Nat.mem_primeFactors.1 hp
      rw [hL q hq f h0 p hp'.1 hp'.2.1]
    have hall := hP q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
      (fun p => okadaC q f p) hsum
    intro p hp hpq
    exact hall p (Nat.mem_primeFactors.2 ⟨hp, hpq, hq.pos.ne'⟩)

end Erdos

end PiFormula
