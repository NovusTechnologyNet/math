import Pilean.Base3.Dimension
import Pilean.PiFormula.Transcendence

/-!
# Base 3: the values of the class F3 are 0 or transcendental (from Baker's theorem)

F3 is the class of series `S(ρ) = ∑ ρ(k) 3^(-⌊k/2⌋)/k` with `ρ` rational and periodic.

**Theorem** (from Baker's theorem). Let `S(ρ) = α + γ π` with `α` and `γ` algebraic. Then
`α = 0` (`alg_eq_zero_of_hasSum_add_mul_pi3`). In particular a value of F3 that is an algebraic
number is `0` (`eq_zero_of_isF3Value_of_isAlgebraic`): every value of F3 is `0` or
transcendental (`transcendental_of_isF3Value`).

The proof is the one of base 2 (`PiFormula/Transcendence.lean`): `S(ρ)` is a combination of the
logarithms `Log(1 - r/t)`, `t = √-3`, with algebraic coefficients (`series_eq_logs3`), and
`const_eq_zero_of_sum_logs` applies.

Joined with the classification of `Dimension.lean` this gives every formula of the class F3
for a number `α + γ π` with `α`, `γ` algebraic (`exists_coords3_of_hasSum_add_mul_pi`): then
`α = 0`, `γ` is a rational multiple of `√3`, and the pattern is
`a rhoGregory + b Z₁ + c Z₂`. So `α + γ π` is a value of F3 if and only if `α = 0` and `γ` is a
rational multiple of `√3` (`isF3Value_add_mul_pi_iff`).
-/

open Complex

namespace PiFormula

namespace Base3

theorem isAlgebraic_exp_log_w3 {r : ℂ} (hr : IsOfFinOrder r) :
    IsAlgebraic ℚ (Complex.exp (Complex.log (1 - r / t3))) := by
  rw [Complex.exp_log (w3_ne_zero hr), div_eq_mul_inv]
  exact isAlgebraic_one.sub ((isAlgebraic_root hr).mul isAlgebraic_t3.inv)

/-- The general form, with complex `α` and `γ`: if the real number `S(ρ)` is `α + γ π` with
`α`, `γ` algebraic complex numbers, then `α = 0`. -/
theorem alg_eq_zero_of_hasSum_complex3 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {x : ℝ} (h : HasSum (seriesTerm3 ρ) x) {α γ : ℂ}
    (hα : IsAlgebraic ℚ α) (hγ : IsAlgebraic ℚ γ) (hx : (x : ℂ) = α + γ * Real.pi) :
    α = 0 := by
  -- a period divisible by 4
  have hρ' : ∀ k, ρ (k + 4 * N) = ρ k := fun k => by
    have h4 := periodic_mul hρ 4 k
    rwa [mul_comm] at h4
  have hN' : 0 < 4 * N := by positivity
  have hS : ∀ r ∈ rootsN (4 * N), IsOfFinOrder r := fun r hr =>
    isOfFinOrder_of_mem_rootsN hN' hr
  have h1 := series_eq_logs3 hN' (Dvd.intro N rfl) hρ'
  have e : (fun k : ℕ => (ρ k : ℂ) / 3 ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTerm3 ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTerm3]
  rw [e] at h1
  have h2 := h1.unique (Complex.hasSum_ofReal.2 h)
  exact const_eq_zero_of_sum_logs hB (rootsN (4 * N)) (fun r => Complex.log (1 - r / t3))
    (fun r hr => isAlgebraic_exp_log_w3 (hS r hr)) (fourierD3 (4 * N) ρ)
    (fun r hr => isAlgebraic_fourierD3 (4 * N) ρ (hS r hr)) hα hγ (h2.trans hx)

/-- **The algebraic part is zero** (from Baker's theorem). If a rational periodic pattern `ρ`
has `∑ ρ(k) 3^(-⌊k/2⌋)/k = α + γ π` with `α` and `γ` algebraic, then `α = 0`. -/
theorem alg_eq_zero_of_hasSum_add_mul_pi3 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {α γ : ℝ} (hα : IsAlgebraic ℚ α)
    (hγ : IsAlgebraic ℚ γ) (h : HasSum (seriesTerm3 ρ) (α + γ * Real.pi)) : α = 0 := by
  have hC := alg_eq_zero_of_hasSum_complex3 hB hN hρ h (isAlgebraic_ofReal hα)
    (isAlgebraic_ofReal hγ) (by push_cast; rfl)
  exact_mod_cast hC

/-- **An algebraic value is zero** (from Baker's theorem). If a rational periodic pattern `ρ`
has `∑ ρ(k) 3^(-⌊k/2⌋)/k = x` with `x` algebraic, then `x = 0`. -/
theorem eq_zero_of_hasSum_of_isAlgebraic3 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {x : ℝ} (hx : IsAlgebraic ℚ x)
    (h : HasSum (seriesTerm3 ρ) x) : x = 0 := by
  refine alg_eq_zero_of_hasSum_add_mul_pi3 hB hN hρ hx (γ := 0) isAlgebraic_zero ?_
  rwa [zero_mul, add_zero]

/-- **The values of the class F3 that are algebraic numbers: only `0`** (from Baker's
theorem). -/
theorem eq_zero_of_isF3Value_of_isAlgebraic (hB : BakerTheorem) {x : ℝ} (h : IsF3Value x)
    (hx : IsAlgebraic ℚ x) : x = 0 := by
  obtain ⟨N, ρ, hN, hρ, hs⟩ := h
  exact eq_zero_of_hasSum_of_isAlgebraic3 hB hN hρ hx hs

/-- **Every value of the class F3 is `0` or transcendental** (from Baker's theorem). -/
theorem transcendental_of_isF3Value (hB : BakerTheorem) {x : ℝ} (h : IsF3Value x)
    (hx : x ≠ 0) : Transcendental ℚ x :=
  fun ha => hx (eq_zero_of_isF3Value_of_isAlgebraic hB h ha)

/-- **A value of the class F3 of the form `α + γ π`, `α` and `γ` algebraic, has `α = 0`**
(from Baker's theorem). -/
theorem alg_eq_zero_of_isF3Value_add_mul_pi (hB : BakerTheorem) {α γ : ℝ}
    (hα : IsAlgebraic ℚ α) (hγ : IsAlgebraic ℚ γ) (h : IsF3Value (α + γ * Real.pi)) :
    α = 0 := by
  obtain ⟨N, ρ, hN, hρ, hs⟩ := h
  exact alg_eq_zero_of_hasSum_add_mul_pi3 hB hN hρ hα hγ hs

/-! ## With the classification of base 3 -/

/-- **Every formula for a number `α + γ π` in base 3** (from Baker's theorem). If a rational
periodic pattern `ρ` has `∑ ρ(k) 3^(-⌊k/2⌋)/k = α + γ π` with `α` and `γ` algebraic, then
`α = 0`, the pattern is `a rhoGregory + b Z₁ + c Z₂` with `a, b, c` rational, and
`γ = a √3`. -/
theorem exists_coords3_of_hasSum_add_mul_pi (hB : BakerTheorem) {N : ℕ} (hN : 0 < N)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {α γ : ℝ} (hα : IsAlgebraic ℚ α)
    (hγ : IsAlgebraic ℚ γ) (h : HasSum (seriesTerm3 ρ) (α + γ * Real.pi)) :
    α = 0 ∧ ∃ a b c : ℚ, ρ = comb3 a b c ∧ γ = a * Real.sqrt 3 := by
  have h0 := alg_eq_zero_of_hasSum_add_mul_pi3 hB hN hρ hα hγ h
  rw [h0, zero_add] at h
  exact ⟨h0, exists_coords3 hB hN hρ hγ h⟩

/-- **Every formula for an algebraic number in base 3** (from Baker's theorem). If a rational
periodic pattern `ρ` has `∑ ρ(k) 3^(-⌊k/2⌋)/k = x` with `x` algebraic, then `x = 0` and the
pattern is one of the zero relations `b Z₁ + c Z₂`, with `b, c` rational. -/
theorem exists_coords3_of_hasSum_of_isAlgebraic (hB : BakerTheorem) {N : ℕ} (hN : 0 < N)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {x : ℝ} (hx : IsAlgebraic ℚ x)
    (h : HasSum (seriesTerm3 ρ) x) : x = 0 ∧ ∃ b c : ℚ, ρ = comb3 0 b c := by
  have h0 := eq_zero_of_hasSum_of_isAlgebraic3 hB hN hρ hx h
  rw [h0] at h
  exact ⟨h0, (hasSum_zero_iff hB hN hρ).1 h⟩

/-- **Which numbers `α + γ π` are values of F3** (from Baker's theorem). For algebraic real
numbers `α` and `γ`, `α + γ π` is the value of a series of the class F3 if and only if `α = 0`
and `γ` is a rational multiple of `√3`. -/
theorem isF3Value_add_mul_pi_iff (hB : BakerTheorem) {α γ : ℝ} (hα : IsAlgebraic ℚ α)
    (hγ : IsAlgebraic ℚ γ) :
    IsF3Value (α + γ * Real.pi) ↔ α = 0 ∧ ∃ q : ℚ, γ = q * Real.sqrt 3 := by
  constructor
  · intro h
    have h0 := alg_eq_zero_of_isF3Value_add_mul_pi hB hα hγ h
    rw [h0, zero_add] at h
    exact ⟨h0, (isF3Value_mul_pi_iff hB hγ).1 h⟩
  · rintro ⟨h0, hq⟩
    rw [h0, zero_add]
    exact (isF3Value_mul_pi_iff hB hγ).2 hq

end Base3

end PiFormula
