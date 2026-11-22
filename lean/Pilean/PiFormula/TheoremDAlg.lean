import Pilean.PiFormula.SharpD
import Pilean.PiFormula.TheoremC3

/-!
# Theorem D for algebraic multiples of π

`TheoremD.lean` and `SharpD.lean` prove Theorem D for series whose value is a rational
multiple of `π`. With the 13-dimensional space of `TheoremC3.lean` the same holds for
algebraic multiples, which is Theorem D as stated in the note:

* `theoremD_alg_sharp`: a rational pattern whose series is an algebraic multiple of `π` and
  which has no term at `gcd(k, 120) < 4` is a multiple of `zD = -2·namedL8 + 2·namedL10 +
  namedL24`;
* `theoremD_alg`: so its value is 0;
* `exists_slow_term_alg`: a series of the class F whose value is a non-zero algebraic
  multiple of `π` has a non-zero term at some `k` with `gcd(k, 120) ≤ 3`.

All three are from Baker's theorem. The certificate is `coords13_D` (generated, in
`TheoremC3.lean`): twelve positions with `gcd(k, 120) < 4` force the five new coordinates to
vanish and leave the one direction `zD`.
-/

open Complex

namespace PiFormula

/-- **Theorem D, sharp form, for algebraic multiples (from Baker's theorem).** A rational
pattern whose series is an algebraic multiple of `π` and which has no term at
`gcd(k, 120) < 4` is a multiple of `zD`. -/
theorem theoremD_alg_sharp (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N)
    {ρ : ℕ → ℚ} (hρ : ρ ∈ algSpace N) (hsupp : ∀ k, Nat.gcd k 120 < 4 → ρ k = 0) :
    ∃ c : ℚ, ρ = c • zD := by
  obtain ⟨q, p, rfl⟩ := exists_coords13 hB hN h120 hρ
  obtain ⟨h0, h1, h2, h3, h7, h45, h46, p0, p1, p2, p3, p4⟩ := coords13_D q p hsupp
  refine ⟨q 6, ?_⟩
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, comb13, zD, h0, h1, h2, h3, h7, p0, p1, p2, p3, p4]
  linear_combination (namedL8 k - namedL10 k) * h46 + namedL10 k * h45

/-- **Theorem D (from Baker's theorem).** Let `ρ` be a rational pattern of period `N` (a
multiple of 120) whose series `∑ ρ(k) 2^(-⌊k/2⌋)/k` is an algebraic multiple of `π`. If all
its terms sit at `k` with `gcd(k, 120) ≥ 4`, the value is 0. -/
theorem theoremD_alg (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ρ ∈ algSpace N) (hsupp : ∀ k, Nat.gcd k 120 < 4 → ρ k = 0) :
    HasSum (seriesTerm ρ) 0 := by
  obtain ⟨c, rfl⟩ := theoremD_alg_sharp hB hN h120 hρ hsupp
  have h := zD_hasSum.mul_left (c : ℝ)
  rw [mul_zero] at h
  have e : seriesTerm (c • zD) = fun k => (c : ℝ) * seriesTerm zD k :=
    funext (seriesTerm_smul c zD)
  rw [e]
  exact h

/-- Theorem D in contrapositive form: a formula for a non-zero algebraic multiple of `π` has
a non-zero term at some `k` with `gcd(k, 120) ≤ 3`. -/
theorem exists_slow_term_alg (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N)
    {ρ : ℕ → ℚ} (hp : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ) (hγ0 : γ ≠ 0)
    (h : HasSum (seriesTerm ρ) (γ * Real.pi)) : ∃ k, Nat.gcd k 120 < 4 ∧ ρ k ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 := theoremD_alg hB hN h120 ⟨hp, γ, hγ, h⟩ hcon
  have h1 := h.unique h0
  have hpi := Real.pi_pos
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact hγ0 h2
  · linarith

/-- The patterns of `algSpace N` with no term at `gcd(k, 120) < 4` form the line of `zD`. -/
theorem fast_alg_eq (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) :
    algSpace N ⊓ fastSupp = Submodule.span ℚ {zD} := by
  apply le_antisymm
  · rintro ρ ⟨hρ, hs⟩
    obtain ⟨c, rfl⟩ := theoremD_alg_sharp hB hN h120 hρ hs
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self zD)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨ratSpace_le_algSpace N (zD_mem_ratSpace h120), fun k hk => zD_supp k (by omega)⟩

end PiFormula
