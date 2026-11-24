/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Base5.LogExplicit
public import Pilean.Base5.Unconditional

/-!
# Base 5: the criterion for logarithms, with the hypotheses discharged

`Base5/LogConverse.lean` proves the criterion for logarithms from `BakerTheorem : Prop`, and
`Base5/LogNonValues.lean` proves that `log 5` and `log 2` are not values from `BakerTheorem`
and `GoodPrimes5`. Here:

* the theorems in the namespace `PiFormula.Base5` use the proof of `GoodPrimes5`
  (`goodPrimes5` of `Base5/Unconditional.lean`), and keep `BakerTheorem` as a hypothesis;
* the theorems in `PiFormula.Base5.Unconditional` also use the formal proof of Baker's theorem
  in `Baker/` (`PiFormula.bakerTheorem`), and depend only on Lean's three standard axioms.
-/

@[expose] public section

namespace PiFormula

namespace Base5

/-- **`log 5` is not the value of any series of the class F5** (from Baker's theorem). -/
theorem not_isF5Value_log_five (hB : BakerTheorem) : ¬ IsF5Value (Real.log 5) :=
  not_isF5Value_log_five_of_goodPrimes5 hB goodPrimes5

/-- **`log 2` is not the value of any series of the class F5** (from Baker's theorem). -/
theorem not_isF5Value_log_two (hB : BakerTheorem) : ¬ IsF5Value (Real.log 2) :=
  not_isF5Value_log_two_of_goodPrimes5 hB goodPrimes5

/-- **`log 3` is not the value of any series of the class F5** (from Baker's theorem). -/
theorem not_isF5Value_log_three (hB : BakerTheorem) : ¬ IsF5Value (Real.log 3) :=
  not_isF5Value_log_three_of_goodPrimes5 hB goodPrimes5

/-- No power `5^k`, `k ≥ 1`, is a product of integer powers of base numbers (from Baker's
theorem). -/
theorem five_pow_ne_prod (hB : BakerTheorem) {k : ℕ} (hk : 0 < k) {n : ℕ} {g : Fin n → ℚ}
    {e : Fin n → ℤ} (hg : ∀ i, g i ∈ baseNumbers5) : (5 : ℚ) ^ k ≠ ∏ i, g i ^ e i :=
  five_pow_ne_prod_of_goodPrimes5 hB goodPrimes5 hk hg

namespace Unconditional

/-- **The converse in base 5.** If `log (a/b)` is a value of the class F5, then it is a
rational combination of logarithms of base numbers. -/
theorem mem_baseSpan5_of_isF5Value_log {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : IsF5Value (Real.log ((a : ℝ) / b))) : Real.log ((a : ℝ) / b) ∈ baseSpan5 :=
  Base5.mem_baseSpan5_of_isF5Value_log bakerTheorem ha hb h

/-- **The criterion in base 5**, for a positive rational number. -/
theorem isF5Value_log_rat_iff {y : ℚ} (hy : 0 < y) :
    IsF5Value (Real.log (y : ℝ)) ↔ Real.log (y : ℝ) ∈ baseSpan5 :=
  Base5.isF5Value_log_rat_iff bakerTheorem hy

/-- **The criterion for base 5 in elementary terms.** For a positive rational `y`, `log y` is
the value of a series `∑ ρ(k) 5^(-⌊k/2⌋)/k` with `ρ` rational and periodic if and only if
some power `y^k`, `k ≥ 1`, is a product of integer powers of the numbers `(5^m - 1)/5^m`
(`m ≥ 1`), `L_h/5^(2h)` and `M_h/5^(2h)` (`h` odd). -/
theorem isF5Value_log_rat_iff_pow {y : ℚ} (hy : 0 < y) :
    IsF5Value (Real.log (y : ℝ)) ↔
      ∃ k : ℕ, 0 < k ∧ ∃ (n : ℕ) (g : Fin n → ℚ) (e : Fin n → ℤ),
        (∀ i, g i ∈ baseNumbers5) ∧ y ^ k = ∏ i, g i ^ e i :=
  Base5.isF5Value_log_rat_iff_pow bakerTheorem hy

/-- **`log 5` is not the value of any series `∑ ρ(k) 5^(-⌊k/2⌋)/k` with `ρ` rational and
periodic.** -/
theorem not_isF5Value_log_five : ¬ IsF5Value (Real.log 5) :=
  Base5.not_isF5Value_log_five bakerTheorem

/-- **`log 2` is not the value of any series of the class F5.** -/
theorem not_isF5Value_log_two : ¬ IsF5Value (Real.log 2) :=
  Base5.not_isF5Value_log_two bakerTheorem

/-- **`log 3` is not the value of any series of the class F5.** -/
theorem not_isF5Value_log_three : ¬ IsF5Value (Real.log 3) :=
  Base5.not_isF5Value_log_three bakerTheorem

end Unconditional

end Base5

end PiFormula
