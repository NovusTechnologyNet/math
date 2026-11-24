/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula.LogPrimes

/-!
# The values of the class F are 0 or transcendental (from Baker's theorem)

F is the class of series `S(ρ) = ∑ ρ(k) 2^(-⌊k/2⌋)/k` with `ρ` rational and periodic.

**Theorem** (from Baker's theorem). Let `S(ρ) = α + γ π` with `α` and `γ` algebraic. Then
`α = 0` (`alg_eq_zero_of_hasSum_add_mul_pi`). In particular a value of F that is an algebraic
number is `0` (`eq_zero_of_isFValue_of_isAlgebraic`): every value of F is `0` or transcendental
(`transcendental_of_isFValue`).

This is a theorem of Adhikari, Saradha, Shorey and Tijdeman (2001) for series of this kind; it
is proved here from `BakerTheorem`, which includes the constant term `1`.

The proof. Baker's theorem is stated for logarithms that are linearly independent over `ℚ`.
The first section removes this condition for the constant term (`baker_const`): if
`β₀ + ∑ β_i λ_i = 0` with `β₀` and the `β_i` algebraic and the `λ_i` logarithms of algebraic
numbers, independent or not, then `β₀ = 0`. The proof is an induction on the number of
logarithms: if they are dependent over `ℚ`, one of them is a rational combination of the
others, and substituting it gives a relation of the same form with one logarithm less.

The second section adds `iπ`, a logarithm of `-1`, to the family
(`const_eq_zero_of_sum_logs`): if `∑ d_r L_r = α + γ π` then `α = 0`. This is used for the three
bases 2, 3 and 5 (`Base3/Transcendence.lean`, `Base5/Transcendence.lean`).

The third section applies it to `S(ρ) = ∑ d_r Log(1 - r/t)`, `t = 1 + i` (`series_eq_logs`).
-/

@[expose] public section

open Complex

namespace PiFormula

/-! ## 1. Baker's theorem with a constant term, without the independence condition -/

/-- Baker's theorem with its constant term, for a family indexed by a finite set. -/
theorem baker_finset_const (hB : BakerTheorem) {ι : Type*} (T : Finset ι) (lam : ι → ℂ)
    (hlam : ∀ i ∈ T, IsAlgebraic ℚ (Complex.exp (lam i)))
    (hind : ∀ q : ι → ℚ, ∑ i ∈ T, (q i : ℂ) * lam i = 0 → ∀ i ∈ T, q i = 0)
    (β₀ : ℂ) (β : ι → ℂ) (hβ₀ : IsAlgebraic ℚ β₀) (hβ : ∀ i ∈ T, IsAlgebraic ℚ (β i))
    (h : β₀ + ∑ i ∈ T, β i * lam i = 0) : β₀ = 0 ∧ ∀ i ∈ T, β i = 0 := by
  classical
  let e : Fin T.card ≃ T := T.equivFin.symm
  have hsum : ∀ f : ι → ℂ, ∑ k : Fin T.card, f (e k) = ∑ i ∈ T, f i := fun f =>
    (Equiv.sum_comp e (fun i : T => f i)).trans (Finset.sum_coe_sort T f)
  have hind' : ∀ q : Fin T.card → ℚ, ∑ k, (q k : ℂ) * lam (e k) = 0 → ∀ k, q k = 0 := by
    intro q hq k
    let q' : ι → ℚ := fun i => if hi : i ∈ T then q (e.symm ⟨i, hi⟩) else 0
    have hq' : ∀ k, q' (e k) = q k := by
      intro k
      simp only [q', (e k).2, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply]
    have h0 : ∑ i ∈ T, (q' i : ℂ) * lam i = 0 := by
      rw [← hsum fun i => (q' i : ℂ) * lam i]
      simp only [hq']
      exact hq
    have h1 := hind q' h0 (e k) (e k).2
    rwa [hq'] at h1
  have h' : β₀ + ∑ k : Fin T.card, β (e k) * lam (e k) = 0 := by
    rw [hsum fun i => β i * lam i]
    exact h
  have key := hB T.card (fun k => lam (e k)) (fun k => hlam _ (e k).2) hind' β₀
    (fun k => β (e k)) hβ₀ (fun k => hβ _ (e k).2) h'
  refine ⟨key.1, fun i hi => ?_⟩
  have h1 := key.2 (e.symm ⟨i, hi⟩)
  simpa using h1

theorem baker_const_aux (hB : BakerTheorem) {ι : Type*} (lam : ι → ℂ) :
    ∀ (n : ℕ) (T : Finset ι), T.card = n →
      (∀ i ∈ T, IsAlgebraic ℚ (Complex.exp (lam i))) →
      ∀ (β₀ : ℂ) (β : ι → ℂ), IsAlgebraic ℚ β₀ → (∀ i ∈ T, IsAlgebraic ℚ (β i)) →
        β₀ + ∑ i ∈ T, β i * lam i = 0 → β₀ = 0 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hn hlam β₀ β hβ₀ hβ h
    by_cases hind : ∀ q : ι → ℚ, ∑ i ∈ T, (q i : ℂ) * lam i = 0 → ∀ i ∈ T, q i = 0
    · -- independent logarithms: this is Baker's theorem
      exact (baker_finset_const hB T lam hlam hind β₀ β hβ₀ hβ h).1
    · -- a rational relation: remove one logarithm
      push Not at hind
      obtain ⟨q, hq, i₀, hi₀, hne⟩ := hind
      have hqC : (q i₀ : ℂ) ≠ 0 := by exact_mod_cast hne
      obtain ⟨c, hc⟩ : ∃ c : ℂ, c = β i₀ * (q i₀ : ℂ)⁻¹ := ⟨_, rfl⟩
      have hcalg : IsAlgebraic ℚ c := by
        rw [hc]
        exact (hβ i₀ hi₀).mul (isAlgebraic_ratCast ℚ (A := ℂ) (q i₀)).inv
      have h1 : β i₀ - c * q i₀ = 0 := by
        rw [hc, mul_assoc, inv_mul_cancel₀ hqC, mul_one, sub_self]
      -- the new relation, on `T.erase i₀`, has the same constant term
      have hsum' : β₀ + ∑ i ∈ T.erase i₀, (β i - c * q i) * lam i = 0 := by
        rw [Finset.sum_erase T (by rw [h1, zero_mul])]
        have e : ∑ i ∈ T, (β i - c * q i) * lam i =
            ∑ i ∈ T, β i * lam i - c * ∑ i ∈ T, (q i : ℂ) * lam i := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [e, hq, mul_zero, sub_zero]
        exact h
      exact ih (T.erase i₀).card (by rw [← hn]; exact Finset.card_erase_lt_of_mem hi₀)
        (T.erase i₀) rfl (fun i hi => hlam i (Finset.mem_of_mem_erase hi)) β₀ _ hβ₀
        (fun i hi => (hβ i (Finset.mem_of_mem_erase hi)).sub
          (hcalg.mul (isAlgebraic_ratCast ℚ (A := ℂ) (q i)))) hsum'

/-- **Baker's theorem for the constant term, without the independence condition.** Let
`lam i` (`i ∈ T`) be logarithms of algebraic numbers, not assumed independent. If
`β₀ + ∑ β_i lam_i = 0` with `β₀` and the `β_i` algebraic, then `β₀ = 0`. -/
theorem baker_const (hB : BakerTheorem) {ι : Type*} (T : Finset ι) (lam : ι → ℂ)
    (hlam : ∀ i ∈ T, IsAlgebraic ℚ (Complex.exp (lam i))) (β₀ : ℂ) (β : ι → ℂ)
    (hβ₀ : IsAlgebraic ℚ β₀) (hβ : ∀ i ∈ T, IsAlgebraic ℚ (β i))
    (h : β₀ + ∑ i ∈ T, β i * lam i = 0) : β₀ = 0 :=
  baker_const_aux hB lam T.card T rfl hlam β₀ β hβ₀ hβ h

/-! ## 2. With `π` -/

/-- A real algebraic number is algebraic as a complex number. -/
theorem isAlgebraic_ofReal {x : ℝ} (hx : IsAlgebraic ℚ x) : IsAlgebraic ℚ (x : ℂ) :=
  (isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective).2 hx

/-- **A combination of logarithms that is `α + γ π`.** Let `L r` (`r ∈ S`) be logarithms of
algebraic numbers. If `∑ d_r L_r = α + γ π` with the `d_r`, `α` and `γ` algebraic, then
`α = 0`. (`iπ` is a logarithm of `-1`; add it to the family and apply `baker_const`.) -/
theorem const_eq_zero_of_sum_logs (hB : BakerTheorem) {ι : Type*} (S : Finset ι) (L : ι → ℂ)
    (hL : ∀ r ∈ S, IsAlgebraic ℚ (Complex.exp (L r))) (d : ι → ℂ)
    (hd : ∀ r ∈ S, IsAlgebraic ℚ (d r)) {α γ : ℂ} (hα : IsAlgebraic ℚ α)
    (hγ : IsAlgebraic ℚ γ) (h : ∑ r ∈ S, d r * L r = α + γ * Real.pi) : α = 0 := by
  classical
  let lam : Option ι → ℂ := fun o =>
    match o with
    | none => Real.pi * I
    | some r => L r
  let β : Option ι → ℂ := fun o =>
    match o with
    | none => γ * I
    | some r => d r
  refine neg_eq_zero.1
    (baker_const hB (Finset.insertNone S) lam ?_ (-α) β hα.neg ?_ ?_)
  · intro i hi
    rcases i with _ | r
    · change IsAlgebraic ℚ (Complex.exp (Real.pi * I))
      rw [Complex.exp_pi_mul_I]
      exact isAlgebraic_one.neg
    · exact hL r (Finset.some_mem_insertNone.1 hi)
  · intro i hi
    rcases i with _ | r
    · exact hγ.mul isAlgebraic_I
    · exact hd r (Finset.some_mem_insertNone.1 hi)
  · rw [Finset.sum_insertNone]
    change -α + (γ * I * (Real.pi * I) + ∑ r ∈ S, d r * L r) = 0
    rw [h]
    linear_combination γ * Real.pi * Complex.I_sq

/-! ## 3. The class F -/

theorem isAlgebraic_exp_log_w {r : ℂ} (hr : IsOfFinOrder r) :
    IsAlgebraic ℚ (Complex.exp (Complex.log (1 - r / tC))) := by
  rw [Complex.exp_log (w_ne_zero hr), div_eq_mul_inv]
  exact isAlgebraic_one.sub ((isAlgebraic_root hr).mul isAlgebraic_tC.inv)

/-- The general form, with complex `α` and `γ`: if the real number `S(ρ)` is `α + γ π` with
`α`, `γ` algebraic complex numbers, then `α = 0`. -/
theorem alg_eq_zero_of_hasSum_complex (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {x : ℝ} (h : HasSum (seriesTerm ρ) x) {α γ : ℂ}
    (hα : IsAlgebraic ℚ α) (hγ : IsAlgebraic ℚ γ) (hx : (x : ℂ) = α + γ * Real.pi) :
    α = 0 := by
  -- a period divisible by 8
  have hρ' : ∀ k, ρ (k + 8 * N) = ρ k := fun k => by
    have h8 := periodic_mul hρ 8 k
    rwa [mul_comm] at h8
  have hN' : 0 < 8 * N := by positivity
  have hS : ∀ r ∈ rootsN (8 * N), IsOfFinOrder r := fun r hr =>
    isOfFinOrder_of_mem_rootsN hN' hr
  have h1 := series_eq_logs hN' (Dvd.intro N rfl) hρ'
  have e : (fun k : ℕ => (ρ k : ℂ) / 2 ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTerm ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTerm]
  rw [e] at h1
  have h2 := h1.unique (Complex.hasSum_ofReal.2 h)
  exact const_eq_zero_of_sum_logs hB (rootsN (8 * N)) (fun r => Complex.log (1 - r / tC))
    (fun r hr => isAlgebraic_exp_log_w (hS r hr)) (fourierD (8 * N) ρ)
    (fun r hr => isAlgebraic_fourierD (8 * N) ρ (hS r hr)) hα hγ (h2.trans hx)

/-- **The algebraic part is zero** (from Baker's theorem). If a rational periodic pattern `ρ`
has `∑ ρ(k) 2^(-⌊k/2⌋)/k = α + γ π` with `α` and `γ` algebraic, then `α = 0`. -/
theorem alg_eq_zero_of_hasSum_add_mul_pi (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {α γ : ℝ} (hα : IsAlgebraic ℚ α) (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTerm ρ) (α + γ * Real.pi)) : α = 0 := by
  have hC := alg_eq_zero_of_hasSum_complex hB hN hρ h (isAlgebraic_ofReal hα)
    (isAlgebraic_ofReal hγ) (by push_cast; rfl)
  exact_mod_cast hC

/-- **An algebraic value is zero** (from Baker's theorem). If a rational periodic pattern `ρ`
has `∑ ρ(k) 2^(-⌊k/2⌋)/k = x` with `x` algebraic, then `x = 0`. -/
theorem eq_zero_of_hasSum_of_isAlgebraic (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {x : ℝ} (hx : IsAlgebraic ℚ x) (h : HasSum (seriesTerm ρ) x) :
    x = 0 := by
  refine alg_eq_zero_of_hasSum_add_mul_pi hB hN hρ hx (γ := 0) isAlgebraic_zero ?_
  rwa [zero_mul, add_zero]

/-- **The values of the class F that are algebraic numbers: only `0`** (from Baker's
theorem). -/
theorem eq_zero_of_isFValue_of_isAlgebraic (hB : BakerTheorem) {x : ℝ} (h : IsFValue x)
    (hx : IsAlgebraic ℚ x) : x = 0 := by
  obtain ⟨N, ρ, hN, hρ, hs⟩ := h
  exact eq_zero_of_hasSum_of_isAlgebraic hB hN hρ hx hs

/-- **Every value of the class F is `0` or transcendental** (from Baker's theorem). -/
theorem transcendental_of_isFValue (hB : BakerTheorem) {x : ℝ} (h : IsFValue x) (hx : x ≠ 0) :
    Transcendental ℚ x :=
  fun ha => hx (eq_zero_of_isFValue_of_isAlgebraic hB h ha)

/-- **A value of the class F of the form `α + γ π`, `α` and `γ` algebraic, has `α = 0`** (from
Baker's theorem). So such a value is an algebraic multiple of `π`, and Theorem C describes
its formulas. -/
theorem alg_eq_zero_of_isFValue_add_mul_pi (hB : BakerTheorem) {α γ : ℝ}
    (hα : IsAlgebraic ℚ α) (hγ : IsAlgebraic ℚ γ) (h : IsFValue (α + γ * Real.pi)) : α = 0 := by
  obtain ⟨N, ρ, hN, hρ, hs⟩ := h
  exact alg_eq_zero_of_hasSum_add_mul_pi hB hN hρ hα hγ hs

/-- The same in the terms of Theorem C (from Baker's theorem): a rational pattern of period `N`
whose series is `α + γ π`, with `α` and `γ` algebraic, belongs to `algSpace N`, the space of
the patterns whose series is an algebraic multiple of `π`. -/
theorem mem_algSpace_of_hasSum_add_mul_pi (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {α γ : ℝ} (hα : IsAlgebraic ℚ α) (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTerm ρ) (α + γ * Real.pi)) : ρ ∈ algSpace N := by
  have h0 := alg_eq_zero_of_hasSum_add_mul_pi hB hN hρ hα hγ h
  rw [h0, zero_add] at h
  exact ⟨hρ, γ, hγ, h⟩

end PiFormula
