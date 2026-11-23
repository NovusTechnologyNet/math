import Pilean.Base3.PiTheorem
import Pilean.PiFormula.Unconditional

/-!
# Base 3: the criterion for logarithms, without a hypothesis

`Base3/LogConverse.lean` and `Base3/LogExplicit.lean` prove the criterion from
`BakerTheorem : Prop`. Here the hypothesis is discharged by the formal proof of Baker's
theorem in `Baker/` (`PiFormula.bakerTheorem`, see `PiFormula/Unconditional.lean`).
-/

namespace PiFormula

namespace Base3

namespace Unconditional

/-- **The converse in base 3.** If `log (a/b)` is a value of the class F3, then it is a
rational combination of `log 3` and the numbers `log |t^n - c|`, `t = √-3`, `c^3 = 1`. -/
theorem mem_logSpan3_of_isF3Value_log {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : IsF3Value (Real.log ((a : ℝ) / b))) : Real.log ((a : ℝ) / b) ∈ logSpan3 :=
  Base3.mem_logSpan3_of_isF3Value_log bakerTheorem ha hb h

/-- **The criterion in base 3**, for a positive rational number. -/
theorem isF3Value_log_rat_iff {y : ℚ} (hy : 0 < y) :
    IsF3Value (Real.log (y : ℝ)) ↔ Real.log (y : ℝ) ∈ logSpan3 :=
  Base3.isF3Value_log_rat_iff bakerTheorem hy

/-- **The criterion for base 3 in elementary terms.** For a positive rational `y`, `log y` is
the value of a series `∑ ρ(k) 3^(-⌊k/2⌋)/k` with `ρ` rational and periodic if and only if
some power `y^k`, `k ≥ 1`, is a product of integer powers of the numbers `3`, `3^m - 1`,
`3^(2j+1) - 3^(j+1) + 1` and `3^(2j+1) + 3^(j+1) + 1`. -/
theorem isF3Value_log_rat_iff_pow {y : ℚ} (hy : 0 < y) :
    IsF3Value (Real.log (y : ℝ)) ↔
      ∃ k : ℕ, 0 < k ∧ ∃ (n : ℕ) (g : Fin n → ℤ) (e : Fin n → ℤ),
        (∀ i, g i ∈ baseNumbers3) ∧ y ^ k = ∏ i, (g i : ℚ) ^ e i :=
  Base3.isF3Value_log_rat_iff_pow bakerTheorem hy

/-- **Which multiples of `π` are values of F3**, from `PrimitiveHalves3` alone: for an
algebraic real `γ`, `γ π` is a value of the class F3 if and only if `γ` is a rational multiple
of `√3`. -/
theorem isF3Value_mul_pi_iff (hH : PrimitiveHalves3) {γ : ℝ} (hγ : IsAlgebraic ℚ γ) :
    IsF3Value (γ * Real.pi) ↔ ∃ q : ℚ, γ = q * Real.sqrt 3 :=
  Base3.isF3Value_mul_pi_iff bakerTheorem hH hγ

/-- **`π` is not the value of any series of the class F3**, from `PrimitiveHalves3` alone. -/
theorem not_isF3Value_pi (hH : PrimitiveHalves3) : ¬ IsF3Value Real.pi :=
  Base3.not_isF3Value_pi bakerTheorem hH

end Unconditional

end Base3

end PiFormula
