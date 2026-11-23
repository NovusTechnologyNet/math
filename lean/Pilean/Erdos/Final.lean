import Pilean.Erdos.Plain
import Pilean.Erdos.OkadaStatus
import Pilean.Erdos.OkadaReduction
import Pilean.Erdos.OkadaLayer
import Pilean.Erdos.OkadaLOne

/-!
# Erdős's conjecture on `∑ f(n)/n` for odd `q` that is not a perfect square

**Conjecture** (Erdős). Let `q ≥ 2` and let `f` be periodic modulo `q` with `f(n) = ±1` when
`q ∤ n` and `f(n) = 0` when `q ∣ n`. Then `∑_{n ≥ 1} f(n)/n ≠ 0`.

**Theorem** (`erdos_pm_one_nat`). The conjecture holds for every odd `q` that is not a perfect
square: for such `q` and `f`, the partial sums `∑_{1 ≤ n < N} f(n)/n` do not tend to `0`.
More generally (`erdos_odd_nonsquare`) for `f` with `f(n) = 0` when `q ∣ n` and every other
value a rational number with odd numerator and odd denominator.

There is no hypothesis: the proof is checked by Lean and depends on the three standard axioms
only. Baker's theorem enters through the formal proof in `lean/Baker/` (by M. Karatarakis).

The two parts:

* `okadaOnlyIf`: Okada's criterion (T. Okada, 1982), the direction "if the sum is `0` then
  conditions (a) and (b) hold", for odd `q` and rational `f` with `f(0) = 0`. Files
  `Okada*.lean`: convergence forces `∑_r f(r) = 0`; the sum is a linear form in the logarithms
  `Log(1 - ζ^a)`; Baker's theorem and Galois conjugation make a vanishing sum invariant under
  `n ↦ h n`; the reduction to the units, the coefficient of `log p`, the independence of the
  logarithms of primes, and `L(1, χ) ≠ 0` as a limit of partial sums.
* `theoremC` (`Main.lean`): (a) and (b) with odd values force `q` to be a perfect square.

For odd squares the method cannot work: there are odd-valued `f` with sum `0`. This converse
is `exists_oddValued_sumIsZero` in `Squares.lean`, which also has the equivalence
`exists_oddValued_sumIsZero_iff`: for odd `q > 1`, an odd-valued `f` with `f(0) = 0` and
sum `0` exists if and only if `q` is a perfect square.
-/

namespace PiFormula

namespace Erdos

/-- **Okada's criterion, the direction used**: for odd `q` and rational `f` with `f(0) = 0`, if
`∑ f(n)/n = 0` then conditions (a) and (b) hold. -/
theorem okadaOnlyIf : OkadaOnlyIf :=
  okadaOnlyIf_of_three okadaUnitReduction okadaLayerSum okadaLOne

/-- For odd `q` that is not a perfect square: if `f(0) = 0` and every other value of `f` is a
rational number with odd numerator and odd denominator, then `∑ f(n)/n` is not `0`. -/
theorem erdos_odd_nonsquare {q : ℕ} (hq : Odd q) (hns : ¬ IsSquare q) (f : ZMod q → ℚ)
    (h0 : f 0 = 0) (hodd : ∀ r : ZMod q, r ≠ 0 → IsOddRat (f r)) : ¬ SumIsZero q f :=
  erdos_of_okada okadaOnlyIf hq hns f h0 hodd

/-- **Erdős's conjecture for odd `q` that is not a perfect square** (functions on `ℤ/q`). -/
theorem erdos_pm_one {q : ℕ} (hq : Odd q) (hns : ¬ IsSquare q) (f : ZMod q → ℚ)
    (h0 : f 0 = 0) (hpm : ∀ r : ZMod q, r ≠ 0 → f r = 1 ∨ f r = -1) : ¬ SumIsZero q f :=
  erdos_pm_one_of_okada okadaOnlyIf hq hns f h0 hpm

/-- **Erdős's conjecture for odd `q` that is not a perfect square, in plain terms.** If
`f : ℕ → ℤ` has period `q`, `f(n) = 0` when `q ∣ n` and `f(n) = ±1` otherwise, then the partial
sums `∑_{1 ≤ n < N} f(n)/n` do not tend to `0`. -/
theorem erdos_pm_one_nat {q : ℕ} (hq : Odd q) (hns : ¬ IsSquare q) (f : ℕ → ℤ)
    (hper : ∀ n, f (n + q) = f n) (h0 : ∀ n, q ∣ n → f n = 0)
    (hpm : ∀ n, ¬ q ∣ n → f n = 1 ∨ f n = -1) :
    ¬ Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (f n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) :=
  erdos_pm_one_nat_of okadaOnlyIf hq hns f hper h0 hpm

end Erdos

end PiFormula
