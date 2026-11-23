import Pilean.Base5.Unconditional
import Pilean.PiFormula.Transcendence

/-!
# Base 5: no formula for any number `α + γ π` (from Baker's theorem)

F5 is the class of series `S(ρ) = ∑ ρ(k) 5^(-⌊k/2⌋)/k` with `ρ` rational and periodic.

**Theorem** (from Baker's theorem). Let `S(ρ) = α + γ π` with `α` and `γ` algebraic. Then
`α = 0` (`alg_eq_zero_of_hasSum_add_mul_pi5`). In particular a value of F5 that is an algebraic
number is `0` (`eq_zero_of_isF5Value_of_isAlgebraic`): every value of F5 is `0` or
transcendental (`transcendental_of_isF5Value`).

The proof is the one of base 2 (`PiFormula/Transcendence.lean`): `S(ρ)` is a combination of the
logarithms `Log(1 - r/t)`, `t = √5`, with algebraic coefficients (`series_eq_logs5`), and
`const_eq_zero_of_sum_logs` applies.

Joined with Theorem C5 (`eq_zero_of_hasSum_mul_pi`: `S(ρ) = γ π` only for `ρ = 0`) this gives
the strongest form (`eq_zero_of_hasSum_add_mul_pi`): if `S(ρ) = α + γ π` with `α` and `γ`
algebraic, then `ρ = 0`. So the only number `α + γ π` that is a value of F5 is `0`
(`eq_zero_of_isF5Value_add_mul_pi`), and a series of F5 with a non-zero pattern has a
transcendental sum (`transcendental_of_hasSum`).
-/

open Complex

namespace PiFormula

namespace Base5

theorem isAlgebraic_exp_log_w5 {r : ℂ} (hr : IsOfFinOrder r) :
    IsAlgebraic ℚ (Complex.exp (Complex.log (1 - r / t5))) := by
  rw [Complex.exp_log (w5_ne_zero hr), div_eq_mul_inv]
  exact isAlgebraic_one.sub ((isAlgebraic_root hr).mul isAlgebraic_t5.inv)

/-- The general form, with complex `α` and `γ`: if the real number `S(ρ)` is `α + γ π` with
`α`, `γ` algebraic complex numbers, then `α = 0`. -/
theorem alg_eq_zero_of_hasSum_complex5 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {x : ℝ} (h : HasSum (seriesTerm5 ρ) x) {α γ : ℂ}
    (hα : IsAlgebraic ℚ α) (hγ : IsAlgebraic ℚ γ) (hx : (x : ℂ) = α + γ * Real.pi) :
    α = 0 := by
  -- an even period
  have hρ' : ∀ k, ρ (k + 2 * N) = ρ k := fun k => by
    have h2 := periodic_mul hρ 2 k
    rwa [mul_comm] at h2
  have hN' : 0 < 2 * N := by positivity
  have hS : ∀ r ∈ rootsN (2 * N), IsOfFinOrder r := fun r hr =>
    isOfFinOrder_of_mem_rootsN hN' hr
  have h2 := (seriesTerm5_hasSum_logs hN' (Dvd.intro N rfl) hρ').unique
    (Complex.hasSum_ofReal.2 h)
  exact const_eq_zero_of_sum_logs hB (rootsN (2 * N)) (fun r => Complex.log (1 - r / t5))
    (fun r hr => isAlgebraic_exp_log_w5 (hS r hr)) (fourierD5 (2 * N) ρ)
    (fun r hr => isAlgebraic_fourierD5 (2 * N) ρ (hS r hr)) hα hγ (h2.trans hx)

/-- **The algebraic part is zero** (from Baker's theorem). If a rational periodic pattern `ρ`
has `∑ ρ(k) 5^(-⌊k/2⌋)/k = α + γ π` with `α` and `γ` algebraic, then `α = 0`. -/
theorem alg_eq_zero_of_hasSum_add_mul_pi5 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {α γ : ℝ} (hα : IsAlgebraic ℚ α)
    (hγ : IsAlgebraic ℚ γ) (h : HasSum (seriesTerm5 ρ) (α + γ * Real.pi)) : α = 0 := by
  have hC := alg_eq_zero_of_hasSum_complex5 hB hN hρ h (isAlgebraic_ofReal hα)
    (isAlgebraic_ofReal hγ) (by push_cast; rfl)
  exact_mod_cast hC

/-- **An algebraic value is zero** (from Baker's theorem). If a rational periodic pattern `ρ`
has `∑ ρ(k) 5^(-⌊k/2⌋)/k = x` with `x` algebraic, then `x = 0`. -/
theorem eq_zero_of_hasSum_of_isAlgebraic5 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {x : ℝ} (hx : IsAlgebraic ℚ x)
    (h : HasSum (seriesTerm5 ρ) x) : x = 0 := by
  refine alg_eq_zero_of_hasSum_add_mul_pi5 hB hN hρ hx (γ := 0) isAlgebraic_zero ?_
  rwa [zero_mul, add_zero]

/-- **The values of the class F5 that are algebraic numbers: only `0`** (from Baker's
theorem). -/
theorem eq_zero_of_isF5Value_of_isAlgebraic (hB : BakerTheorem) {x : ℝ} (h : IsF5Value x)
    (hx : IsAlgebraic ℚ x) : x = 0 := by
  obtain ⟨N, ρ, hN, hρ, hs⟩ := h
  exact eq_zero_of_hasSum_of_isAlgebraic5 hB hN hρ hx hs

/-- **Every value of the class F5 is `0` or transcendental** (from Baker's theorem). -/
theorem transcendental_of_isF5Value (hB : BakerTheorem) {x : ℝ} (h : IsF5Value x)
    (hx : x ≠ 0) : Transcendental ℚ x :=
  fun ha => hx (eq_zero_of_isF5Value_of_isAlgebraic hB h ha)

/-! ## With Theorem C5 -/

/-- **No formula for a number `α + γ π` in base 5** (from Baker's theorem). If a rational
periodic pattern `ρ` has `∑ ρ(k) 5^(-⌊k/2⌋)/k = α + γ π` with `α` and `γ` algebraic, then
`ρ = 0`. -/
theorem eq_zero_of_hasSum_add_mul_pi (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {α γ : ℝ} (hα : IsAlgebraic ℚ α) (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTerm5 ρ) (α + γ * Real.pi)) : ρ = 0 := by
  have h0 := alg_eq_zero_of_hasSum_add_mul_pi5 hB hN hρ hα hγ h
  rw [h0, zero_add] at h
  exact eq_zero_of_hasSum_mul_pi hB hN hρ hγ h

/-- **A series of the class F5 with a non-zero pattern has a transcendental sum** (from
Baker's theorem). -/
theorem transcendental_of_hasSum (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) (hρ0 : ρ ≠ 0) {x : ℝ} (h : HasSum (seriesTerm5 ρ) x) :
    Transcendental ℚ x := by
  intro hx
  refine hρ0 (eq_zero_of_hasSum_add_mul_pi hB hN hρ hx (γ := 0) isAlgebraic_zero ?_)
  rwa [zero_mul, add_zero]

/-- **The only number `α + γ π`, `α` and `γ` algebraic, that is a value of F5 is `0`** (from
Baker's theorem). -/
theorem eq_zero_of_isF5Value_add_mul_pi (hB : BakerTheorem) {α γ : ℝ} (hα : IsAlgebraic ℚ α)
    (hγ : IsAlgebraic ℚ γ) (h : IsF5Value (α + γ * Real.pi)) : α = 0 ∧ γ = 0 := by
  obtain ⟨N, ρ, hN, hρ, hs⟩ := h
  have h0 := alg_eq_zero_of_hasSum_add_mul_pi5 hB hN hρ hα hγ hs
  rw [h0, zero_add] at hs
  exact ⟨h0, mul_pi_eq_zero hB hγ ⟨N, ρ, hN, hρ, hs⟩⟩

end Base5

end PiFormula
