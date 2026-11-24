/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.ArithLemma1Aux

/-!
# Theorem A from the abstract theorem, part 7: Lemma 1

`lemma1 : Lemma1Prop` (the statement is in `ArithDefs.lean`; paper: `02_proof_part_II.md`,
section 2). For odd `q`, logarithm-type characters `χ_p`, `f` with odd values off `0` and a
non-empty set `n` of primes of `q`:

  `g_n = (∏_{p ∈ n} k_p) N_n + 2 e`,  `e` supported on `S_n`, with coefficients in `ℤ_(2)`.

Proof. `e = (1/2) (g_n - ν N_n)`, `ν = ∏_{p ∈ n} k_p`. The coefficient of `σ` in `g_n` is
`o(n)^(-1) ∑ f(r)` over `T = {r : n(r) = n, cl(r) = σ}` (`lem1_coeff_gElt`). `T` is empty
unless `σ ∈ S_n` (`lem1_coeff_gElt_eq_zero`). For `σ ∈ S_n`, `#T ≡ ν` modulo 2
(`lem1_card_zmod`, in `ArithLemma1Aux.lean`), every `f(r)` is `≡ 1` modulo `2 ℤ_(2)`, and
`o(n)` is an odd natural number, so the coefficient is `≡ ν` (`lem1_even2_coeff`).

Complete: no `sorry`, no hypothesis left.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open scoped BigOperators

open AddMonoidAlgebra (single)

namespace PiFormula

namespace Erdos

namespace Arith

variable {q : ℕ} [NeZero q] {χ : ∀ p : Idx q, ZMod p.1 → ZMod (2 ^ sExp q p)}

/-- The coefficient of `σ` in `g_n`. -/
theorem lem1_coeff_gElt (f : ZMod q → ℚ) (n : Finset (Idx q)) (σ : Grp (sExp q)) :
    (gElt q χ f n).coeff σ = (oRat q n)⁻¹ * ∑ r ∈ Finset.univ.filter (fun r : ZMod q =>
      suppPi q (crt q r) = n ∧ clPi q χ (crt q r) = σ), f r := by
  unfold gElt
  rw [coeff_smul', coeff_finset_sum]
  simp only [coeff_single_apply]
  rw [← Finset.sum_filter, Finset.filter_filter]

/-- `g_n` is supported on `S_n`. -/
theorem lem1_coeff_gElt_eq_zero (f : ZMod q → ℚ) (n : Finset (Idx q)) {σ : Grp (sExp q)}
    (hσ : ¬ InSub n σ) : (gElt q χ f n).coeff σ = 0 := by
  have hempty : Finset.univ.filter (fun r : ZMod q =>
      suppPi q (crt q r) = n ∧ clPi q χ (crt q r) = σ) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro r _ ⟨hs, hc⟩
    apply hσ
    rw [← hs, ← hc]
    exact lem1_inSub_clPi (crt q r)
  rw [lem1_coeff_gElt, hempty, Finset.sum_empty, mul_zero]

/-- For `σ ∈ S_n` the coefficient of `σ` in `g_n` is `≡ ∏_{p ∈ n} k_p` modulo `2 ℤ_(2)`. -/
theorem lem1_even2_coeff (hq : Odd q) (hχ : ∀ p, IsLogChar p.1 (sExp q p) (χ p))
    (f : ZMod q → ℚ) (hodd : ∀ r : ZMod q, r ≠ 0 → IsOddRat (f r)) (n : Finset (Idx q))
    (hn : n.Nonempty) {σ : Grp (sExp q)} (hσ : InSub n σ) :
    Even2 ((gElt q χ f n).coeff σ - ((∏ p ∈ n, kExp q p : ℕ) : ℚ)) := by
  rw [lem1_coeff_gElt]
  have hne : ∀ r ∈ Finset.univ.filter (fun r : ZMod q =>
      suppPi q (crt q r) = n ∧ clPi q χ (crt q r) = σ), r ≠ 0 := by
    intro r hr
    rintro rfl
    have h := (Finset.mem_filter.1 hr).2.1
    rw [map_zero] at h
    obtain ⟨p, hp⟩ := hn
    rw [← h] at hp
    exact lem1_mem_suppPi.1 hp rfl
  have hcard := lem1_card_zmod hq hχ n hσ
  generalize Finset.univ.filter (fun r : ZMod q =>
    suppPi q (crt q r) = n ∧ clPi q χ (crt q r) = σ) = T at hne hcard ⊢
  generalize (∏ p ∈ n, kExp q p : ℕ) = ν at hcard ⊢
  have hO : Odd (∏ p ∈ n, lem1_oddPart q p) := lem1_prod_oddPart_odd n
  rw [lem1_oRat_eq]
  generalize (∏ p ∈ n, lem1_oddPart q p : ℕ) = O at hO ⊢
  have h1 : Even2 (∑ r ∈ T, f r - (T.card : ℚ)) := by
    have e : ∑ r ∈ T, f r - (T.card : ℚ) = ∑ r ∈ T, (f r - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [e]
    exact even2_sum _ _ fun r hr => even2_sub_one (hodd r (hne r hr))
  have h2 : Even2 ((T.card : ℚ) - (O : ℚ) * (ν : ℚ)) := by
    have hc : ((T.card : ℕ) : ZMod 2) = ((O * ν : ℕ) : ZMod 2) := by
      rw [Nat.cast_mul, ZMod.natCast_eq_one_iff_odd.2 hO, one_mul]
      exact hcard
    have hmod : T.card % 2 = (O * ν) % 2 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hc
    have hdvd : (2 : ℤ) ∣ (T.card : ℤ) - ((O * ν : ℕ) : ℤ) := by omega
    have h := even2_intCast_sub (even_iff_two_dvd.2 hdvd)
    push_cast at h
    exact h
  have hO0 : (O : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hO.pos.ne'
  have e : (O : ℚ)⁻¹ * ∑ r ∈ T, f r - (ν : ℚ) =
      (O : ℚ)⁻¹ * ((∑ r ∈ T, f r - (T.card : ℚ)) + ((T.card : ℚ) - (O : ℚ) * (ν : ℚ))) := by
    field_simp
    ring
  rw [e]
  exact even2_mul_left (isZ2_inv_natCast hO) (even2_add h1 h2)

/-- The coefficients of `e = (1/2) (g - c N_n)`. -/
theorem lem1_coeff_half (g : GRing (sExp q)) (c : ℚ) (n : Finset (Idx q)) (σ : Grp (sExp q)) :
    ((2 : ℚ)⁻¹ • (g - c • normElt (sExp q) n)).coeff σ =
      2⁻¹ * (g.coeff σ - c * if InSub n σ then 1 else 0) := by
  rw [coeff_smul', AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_smul', coeff_normElt]

/-- **Lemma 1**: `g_n = (∏_{p ∈ n} k_p) N_n + 2 e` with `e ∈ ℤ_(2)[S_n]`. -/
theorem lemma1 : Lemma1Prop := by
  intro q _ hq χ hχ f hodd n hn
  refine ⟨(2 : ℚ)⁻¹ • (gElt q χ f n - ((∏ p ∈ n, kExp q p : ℕ) : ℚ) • normElt (sExp q) n),
    ?_, ?_, ?_⟩
  · intro σ
    rw [lem1_coeff_half]
    by_cases hσ : InSub n σ
    · obtain ⟨z, hz, e⟩ := lem1_even2_coeff hq hχ f hodd n hn hσ
      rw [ite_eq_left hσ, mul_one, e, inv_mul_cancel_left₀ two_ne_zero]
      exact hz
    · rw [ite_eq_right hσ, mul_zero, sub_zero, lem1_coeff_gElt_eq_zero f n hσ, mul_zero]
      exact isZ2_zero
  · intro σ hne
    by_contra hσ
    apply hne
    rw [lem1_coeff_half, ite_eq_right hσ, mul_zero, sub_zero, lem1_coeff_gElt_eq_zero f n hσ,
      mul_zero]
  · rw [smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul, add_sub_cancel]

end Arith

end Erdos

end PiFormula
