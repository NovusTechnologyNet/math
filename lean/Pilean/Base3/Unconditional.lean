module

public import Pilean.Base3.Optimum
public import Pilean.PiFormula.Unconditional

/-!
# Base 3: the theorems without a hypothesis

`Base3/LogConverse.lean`, `Base3/LogExplicit.lean`, `Base3/PiTheorem.lean` and
`Base3/Dimension.lean` prove the criterion for logarithms, the theorem on `π` and the
classification of the formulas from `BakerTheorem : Prop`. Here the
hypothesis is discharged by the formal proof of Baker's theorem in `Baker/`
(`PiFormula.bakerTheorem`, see `PiFormula/Unconditional.lean`). The theorems below depend
only on Lean's three standard axioms.
-/

@[expose] public section

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

/-- **Which multiples of `π` are values of F3.** For an algebraic real `γ`, `γ π` is the value
of a series `∑ ρ(k) 3^(-⌊k/2⌋)/k` with `ρ` rational and periodic if and only if `γ` is a
rational multiple of `√3`. -/
theorem isF3Value_mul_pi_iff {γ : ℝ} (hγ : IsAlgebraic ℚ γ) :
    IsF3Value (γ * Real.pi) ↔ ∃ q : ℚ, γ = q * Real.sqrt 3 :=
  Base3.isF3Value_mul_pi_iff bakerTheorem hγ

/-- **No non-zero rational multiple of `π` is a value of F3.** -/
theorem not_isF3Value_rat_mul_pi {q : ℚ} (h : IsF3Value ((q : ℝ) * Real.pi)) : q = 0 :=
  Base3.not_isF3Value_rat_mul_pi bakerTheorem h

/-- **`π` is not the value of any series `∑ ρ(k) 3^(-⌊k/2⌋)/k` with `ρ` rational and
periodic.** -/
theorem not_isF3Value_pi : ¬ IsF3Value Real.pi :=
  Base3.not_isF3Value_pi bakerTheorem

/-- **Every formula for a multiple of `π` in base 3.** If a rational periodic pattern `ρ` has
`∑ ρ(k) 3^(-⌊k/2⌋)/k = γ π` with `γ` algebraic, then `ρ = a rhoGregory + b Z₁ + c Z₂` with
`a, b, c` rational, and `γ = a √3`. Here, for `k = 1, ..., 12`,
`rhoGregory = (6, 0, -6, 0, 6, 0, -6, 0, 6, 0, -6, 0)`,
`Z₁ = (0, 1, -2, 0, 1, 4, 0, 3, 2, 4, -1, 0)` and
`Z₂ = (1, -3, -4, -3, 1, 0, -1, 3, 4, 3, -1, 0)`. -/
theorem exists_coords3 {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ}
    (hγ : IsAlgebraic ℚ γ) (h : HasSum (seriesTerm3 ρ) (γ * Real.pi)) :
    ∃ a b c : ℚ, ρ = comb3 a b c ∧ γ = a * Real.sqrt 3 :=
  Base3.exists_coords3 bakerTheorem hN hρ hγ h

/-- **Every such series has period 12.** -/
theorem period_twelve {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ}
    (hγ : IsAlgebraic ℚ γ) (h : HasSum (seriesTerm3 ρ) (γ * Real.pi)) (k : ℕ) :
    ρ (k + 12) = ρ k :=
  Base3.period_twelve bakerTheorem hN hρ hγ h k

/-- **The zero relations of base 3.** A rational periodic pattern has
`∑ ρ(k) 3^(-⌊k/2⌋)/k = 0` if and only if `ρ = b Z₁ + c Z₂` with `b, c` rational. -/
theorem hasSum_zero_iff {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (seriesTerm3 ρ) 0 ↔ ∃ b c : ℚ, ρ = comb3 0 b c :=
  Base3.hasSum_zero_iff bakerTheorem hN hρ

/-- **Theorem C3 in full.** Let `N` be a multiple of 12. Among the rational patterns of period
`N`, those whose series `∑ ρ(k) 3^(-⌊k/2⌋)/k` is an algebraic multiple of `π` have period 12
and form a space of dimension exactly 3; those whose series is 0 form a subspace of dimension
exactly 2. -/
theorem theoremC3 {N : ℕ} (hN : 0 < N) (h12 : 12 ∣ N) :
    (∀ ρ ∈ algSpace3 N, ∀ k, ρ (k + 12) = ρ k) ∧
      Module.finrank ℚ (algSpace3 N) = 3 ∧ Module.finrank ℚ (zeroSpace3 N) = 2 :=
  Base3.theoremC3 bakerTheorem hN h12

/-- **Theorem E3: no formula beats the Gregory series.** Let `ρ` be a rational periodic
pattern whose series `∑ ρ(k) 3^(-⌊k/2⌋)/k` is a non-zero algebraic multiple of `π`. Then at
least 6 of its 12 entries per period are non-zero, that is, at least one term per base-3
digit; and exactly 6 are non-zero if and only if `ρ` is a rational multiple of
`rhoGregory = (6, 0, -6, 0, 6, 0, -6, 0, 6, 0, -6, 0)` or of
`rhoSecond = (0, 18, 18, 18, 0, 0, 0, -18, -18, -18, 0, 0)`. -/
theorem theoremE3 {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ}
    (hγ : IsAlgebraic ℚ γ) (hγ0 : γ ≠ 0) (h : HasSum (seriesTerm3 ρ) (γ * Real.pi)) :
    6 ≤ termCount3 ρ ∧
      (termCount3 ρ = 6 ↔ ∃ a : ℚ, ρ = a • rhoGregory ∨ ρ = a • rhoSecond) :=
  Base3.theoremE3 bakerTheorem hN hρ hγ hγ0 h

end Unconditional

end Base3

end PiFormula
