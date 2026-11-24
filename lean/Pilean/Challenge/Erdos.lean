module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Challenge file: the statement of the Erdős case, with Mathlib only

This file is NOT part of the library and is not imported by `Pilean.lean`. It states, with
notions of Mathlib only and no import from this project, the theorem that
`Pilean/Erdos/Final.lean` proves under the same name. The proof here is `sorry` on purpose:
the file is the trusted "challenge" for `lake comparator`, which checks that the theorem
proved in the library is this statement, uses only the permitted axioms, and is accepted by
the kernel. Configuration: `comparator.json` at the top of the repository.

**Statement.** Let `q` be odd and not a perfect square, and let `f : ℕ → ℤ` have period `q`,
with `f(n) = 0` when `q ∣ n` and `f(n) = ±1` otherwise. Then the partial sums
`∑_{n < N} f(n)/n` (the term `n = 0` is `0` in Lean) do not tend to `0`.

This is the case "odd `q` that is not a perfect square" of a conjecture of Erdős on
`∑ f(n)/n`.
-/

@[expose] public section

namespace PiFormula

namespace Erdos

theorem erdos_pm_one_nat {q : ℕ} (hq : Odd q) (hns : ¬ IsSquare q) (f : ℕ → ℤ)
    (hper : ∀ n, f (n + q) = f n) (h0 : ∀ n, q ∣ n → f n = 0)
    (hpm : ∀ n, ¬ q ∣ n → f n = 1 ∨ f n = -1) :
    ¬ Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (f n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

end Erdos

end PiFormula
