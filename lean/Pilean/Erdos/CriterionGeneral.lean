module

public import Pilean.Erdos.CriterionGenFirst
public import Pilean.Erdos.CriterionGenSecond
public import Pilean.Erdos.OkadaGlue
public import Pilean.Erdos.OkadaLogPrimes
public import Pilean.Erdos.Criterion

/-!
# Okada's criterion for every modulus `q ≥ 1` and every rational `f`

**Theorem** (T. Okada, 1982; `okadaCriterionGeneral`). Let `q ≥ 1` and let `f` be a rational
function on `ℤ/q` (no condition on `f(0)`, no condition on the parity of `q`). The partial
sums of `∑_{n ≥ 1} f(n)/n` tend to `0` if and only if

* (a) `g(a) = ∑_{m ∈ M(q)} f(a m)/m = 0` for every unit `a` modulo `q` (`CondA`), and
* (b) `c_p = ∑_{r=1}^{q} f(r) λ(r, p) = 0` for every prime `p ∣ q` (`CondB`; the residue `0`
  is represented by `r = q`, with `λ(q, p) = v_p(q) + 1/(p-1)`).

Moreover (`tendsto_partialSum_of_condA_gen`), under (a) alone the series converges and
`∑_{n ≥ 1} f(n)/n = -(1/q) ∑_{p ∣ q} c_p log p`.

This removes the hypotheses `Odd q` and `f 0 = 0` of `okadaOnlyIf` (`Final.lean`) and of
`okadaCriterion` (`Criterion.lean`). The proof is the same (`okadaOnlyIf_of_main`,
`OkadaGlue.lean`), from the statements for every `q` of `CriterionGenFirst.lean` and
`CriterionGenSecond.lean`.

Example with `f(0) ≠ 0`: `q = 2`, `f(1) = 1`, `f(0) = -1`. Then `g(1) = 1 - ∑_{k ≥ 1} 2^(-k) = 0`
and `c_2 = f(0) λ(2, 2) = -2`, and indeed `∑ (-1)^(n+1)/n = log 2 = -(1/2) c_2 log 2`.
-/

@[expose] public section

open scoped BigOperators

open Filter

namespace PiFormula

namespace Erdos

open Okada

/-- **Okada's criterion, the direction "sum `= 0` implies (a) and (b)"**, for every `q ≥ 1`
and every rational `f` on `ℤ/q`. -/
theorem okadaOnlyIfGeneral (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (hS : SumIsZero q f) :
    CondA q f ∧ CondB q f := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne q)
  -- for every unit `h`, the sums of `g(h n)/n` over the `n` prime to `q` tend to the same
  -- number
  have key : ∀ h : (ZMod q)ˣ,
      Tendsto (unitSum q fun n => okadaG q f ((h : ZMod q) * n)) atTop
        (nhds ((∑ p ∈ q.primeFactors, layerSum q f p * Real.log (p : ℝ)) / (q : ℝ))) := by
    intro h
    have h1 : Tendsto (partialSum q (twistBy q f h)) atTop (nhds 0) :=
      twistInvariance_gen q f hS h
    have h2 := unitReduction_gen q (twistBy q f h)
    have h3 := h1.sub h2
    simp only [layerSum_twistBy, zero_sub, neg_neg] at h3
    refine h3.congr fun N => ?_
    rw [sub_sub_cancel]
    simp only [unitSum, okadaG_twistBy]
  obtain ⟨hc, hg⟩ := unitNonvanishing_gen q (okadaG q f) _ key
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
      rw [layerSum_gen q f hp'.1 hp'.2.1]
    have hall := okadaLogPrimes q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
      (fun p => okadaC q f p) hsum
    intro p hp hpq
    exact hall p (Nat.mem_primeFactors.2 ⟨hp, hpq, NeZero.ne q⟩)

/-- **The value of the series under condition (a)** (Okada), for every `q ≥ 1` and every
rational `f` on `ℤ/q`: if `g` vanishes on the units, the series converges and
`∑_{n ≥ 1} f(n)/n = -(1/q) ∑_{p ∣ q} c_p log p`. -/
theorem tendsto_partialSum_of_condA_gen (q : ℕ) [NeZero q] (f : ZMod q → ℚ)
    (ha : CondA q f) :
    Tendsto (partialSum q f) atTop
      (nhds (-((∑ p ∈ q.primeFactors, (okadaC q f p : ℝ) * Real.log (p : ℝ)) / (q : ℝ)))) := by
  have h := unitReduction_gen q f
  have hsum : ∑ p ∈ q.primeFactors, layerSum q f p * Real.log (p : ℝ) =
      ∑ p ∈ q.primeFactors, (okadaC q f p : ℝ) * Real.log (p : ℝ) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Nat.mem_primeFactors.1 hp
    rw [layerSum_gen q f hp'.1 hp'.2.1]
  rw [hsum] at h
  refine h.congr fun N => ?_
  rw [unitSum_eq_zero_of_condA ha, sub_zero]

/-- **Okada's criterion, the direction "(a) and (b) imply sum `= 0`"**, for every `q ≥ 1` and
every rational `f` on `ℤ/q`. -/
theorem okadaIfGeneral (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (ha : CondA q f)
    (hb : CondB q f) : SumIsZero q f := by
  have h := tendsto_partialSum_of_condA_gen q f ha
  have hsum : ∑ p ∈ q.primeFactors, (okadaC q f p : ℝ) * Real.log (p : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := Nat.mem_primeFactors.1 hp
    rw [hb p hp'.1 hp'.2.1, Rat.cast_zero, zero_mul]
  rw [hsum, zero_div, neg_zero] at h
  exact h

/-- **Okada's criterion** (T. Okada, 1982), for every modulus `q ≥ 1` and every rational
function `f` on `ℤ/q`: the partial sums of `∑_{n ≥ 1} f(n)/n` tend to `0` if and only if
conditions (a) and (b) hold. -/
theorem okadaCriterionGeneral {q : ℕ} (hq : 1 ≤ q) (f : ZMod q → ℚ) :
    SumIsZero q f ↔ CondA q f ∧ CondB q f := by
  have : NeZero q := ⟨by omega⟩
  exact ⟨fun h => okadaOnlyIfGeneral q f h, fun h => okadaIfGeneral q f h.1 h.2⟩

end Erdos

end PiFormula
