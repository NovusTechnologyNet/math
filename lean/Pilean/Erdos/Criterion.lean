module

public import Pilean.Erdos.Final

/-!
# Okada's criterion in both directions (odd `q`)

**Theorem** (T. Okada, 1982; `okadaCriterion`). Let `q` be odd and `f : ℤ/q → ℚ` with
`f(0) = 0`. The partial sums of `∑_{n ≥ 1} f(n)/n` tend to `0` if and only if

* (a) `g(a) = ∑_{m ∈ M(q)} f(a m)/m = 0` for every unit `a` modulo `q` (`CondA`), and
* (b) `c_p = ∑_{r=1}^{q} f(r) λ(r, p) = 0` for every prime `p ∣ q` (`CondB`).

The direction "sum `= 0` implies (a) and (b)" is `okadaOnlyIf` (`Final.lean`; Baker's theorem
and `L(1, χ) ≠ 0`). The direction "(a) and (b) imply sum `= 0`" (`okadaIf`) is elementary: by
`okadaUnitReduction`, `S_N(f) - S'_N(g) → -(1/q) ∑_{p ∣ q} ℓ_p log p`, where `S'_N(g)` is a sum
over the `n` prime to `q`; it is `0` when `g` vanishes on the units, and `ℓ_p = c_p`
(`okadaLayerSum`).

More precisely (`tendsto_partialSum_of_condA`): if (a) holds, the series converges and

  `∑_{n ≥ 1} f(n)/n = -(1/q) ∑_{p ∣ q} c_p log p`.

Both results are known (Okada). `CriterionGeneral.lean` removes the hypotheses `Odd q` and
`f 0 = 0` (`okadaCriterionGeneral`: every modulus `q ≥ 1`, every rational `f`).
-/

@[expose] public section

open scoped BigOperators

open Filter

namespace PiFormula

namespace Erdos

/-- If `g = okadaG q f` vanishes on the units, the sums of `g(n)/n` over the `n` prime to `q`
are `0`. -/
theorem unitSum_eq_zero_of_condA {q : ℕ} {f : ZMod q → ℚ} (ha : CondA q f) (N : ℕ) :
    Okada.unitSum q (okadaG q f) N = 0 := by
  unfold Okada.unitSum
  refine Finset.sum_eq_zero fun n _ => ?_
  by_cases hn : n.Coprime q
  · have hn' : n.Coprime q = True := eq_true hn
    simp only [hn', ↓reduceIte]
    rw [ha (n : ZMod q) ((ZMod.isUnit_iff_coprime n q).2 hn), zero_div]
  · simp only [hn, ↓reduceIte]

/-- **The value of the series under condition (a)** (Okada). For odd `q` and `f(0) = 0`: if
`g` vanishes on the units, then `∑_{n ≥ 1} f(n)/n = -(1/q) ∑_{p ∣ q} c_p log p`. -/
theorem tendsto_partialSum_of_condA {q : ℕ} (hq : Odd q) (f : ZMod q → ℚ) (h0 : f 0 = 0)
    (ha : CondA q f) :
    Tendsto (partialSum q f) atTop
      (nhds (-((∑ p ∈ q.primeFactors, (okadaC q f p : ℝ) * Real.log (p : ℝ)) / (q : ℝ)))) := by
  have : NeZero q := ⟨hq.pos.ne'⟩
  have h := okadaUnitReduction q hq f h0
  have hsum : ∑ p ∈ q.primeFactors, Okada.layerSum q f p * Real.log (p : ℝ) =
      ∑ p ∈ q.primeFactors, (okadaC q f p : ℝ) * Real.log (p : ℝ) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Nat.mem_primeFactors.1 hp
    rw [okadaLayerSum q hq f h0 p hp'.1 hp'.2.1]
  rw [hsum] at h
  refine h.congr fun N => ?_
  rw [unitSum_eq_zero_of_condA ha, sub_zero]

/-- **Okada's criterion, the direction "(a) and (b) imply sum `= 0`"**: for odd `q` and
rational `f` with `f(0) = 0`, if conditions (a) and (b) hold then `∑ f(n)/n = 0`. -/
theorem okadaIf {q : ℕ} (hq : Odd q) (f : ZMod q → ℚ) (h0 : f 0 = 0) (ha : CondA q f)
    (hb : CondB q f) : SumIsZero q f := by
  have h := tendsto_partialSum_of_condA hq f h0 ha
  have hsum : ∑ p ∈ q.primeFactors, (okadaC q f p : ℝ) * Real.log (p : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := Nat.mem_primeFactors.1 hp
    rw [hb p hp'.1 hp'.2.1, Rat.cast_zero, zero_mul]
  rw [hsum, zero_div, neg_zero] at h
  exact h

/-- **Okada's criterion** (T. Okada, 1982), for odd `q` and rational `f` with `f(0) = 0`:
`∑_{n ≥ 1} f(n)/n = 0` if and only if conditions (a) and (b) hold. -/
theorem okadaCriterion {q : ℕ} (hq : Odd q) (f : ZMod q → ℚ) (h0 : f 0 = 0) :
    SumIsZero q f ↔ CondA q f ∧ CondB q f :=
  ⟨fun h => okadaOnlyIf q hq f h0 h, fun h => okadaIf hq f h0 h.1 h.2⟩

end Erdos

end PiFormula
