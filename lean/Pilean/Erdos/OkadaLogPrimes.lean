import Pilean.Erdos.OkadaDefs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The logarithms of the primes are linearly independent over `ℚ`

`okadaLogPrimes : OkadaLogPrimes`: if `∑_{p ∈ S} c_p log p = 0` for a finite set `S` of primes
and rational numbers `c_p`, then every `c_p` is `0`.

Proof. Clearing denominators gives integers `z_p` with `∑ z_p log p = 0`
(`exists_int_log_relation`). Put `A = ∏ p^(z_p⁺)` and `B = ∏ p^(z_p⁻)`; then
`log A = log B`, so `A = B`, and comparing the exponents of `p` gives `z_p⁺ = z_p⁻`, that is
`z_p = 0` (`int_log_relation`).
-/

open scoped BigOperators

namespace PiFormula

namespace Erdos

namespace Okada

/-- The exponent of `p₀` in a product of powers of distinct primes. -/
theorem factorization_prod_prime_pow (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (k : ℕ → ℕ)
    {p₀ : ℕ} (hp₀ : p₀ ∈ S) : (∏ p ∈ S, p ^ k p).factorization p₀ = k p₀ := by
  rw [Nat.factorization_prod fun p hp => pow_ne_zero _ (hS p hp).ne_zero,
    Finsupp.finsetSum_apply, Finset.sum_eq_single p₀]
  · rw [(hS p₀ hp₀).factorization_pow, Finsupp.single_eq_same]
  · intro p hp hne
    rw [(hS p hp).factorization_pow, Finsupp.single_apply]
    simp only [hne, ↓reduceIte]
  · intro h
    exact absurd hp₀ h

theorem log_prod_prime_pow (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (k : ℕ → ℕ) :
    Real.log ((∏ p ∈ S, p ^ k p : ℕ) : ℝ) = ∑ p ∈ S, (k p : ℝ) * Real.log (p : ℝ) := by
  rw [Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    rw [Nat.cast_pow]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (hS p hp).ne_zero)

/-- An integer relation between the logarithms of distinct primes is trivial. -/
theorem int_log_relation (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (z : ℕ → ℤ)
    (h : ∑ p ∈ S, (z p : ℝ) * Real.log (p : ℝ) = 0) : ∀ p ∈ S, z p = 0 := by
  intro p₀ hp₀
  have hpos : ∀ k : ℕ → ℕ, (0 : ℝ) < ((∏ p ∈ S, p ^ k p : ℕ) : ℝ) := fun k =>
    Nat.cast_pos.2 (Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _)
  have hlog : Real.log ((∏ p ∈ S, p ^ (z p).toNat : ℕ) : ℝ) =
      Real.log ((∏ p ∈ S, p ^ (-z p).toNat : ℕ) : ℝ) := by
    rw [log_prod_prime_pow S hS, log_prod_prime_pow S hS, ← sub_eq_zero, ← h,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e : (((z p).toNat : ℕ) : ℝ) - (((-z p).toNat : ℕ) : ℝ) = (z p : ℝ) := by
      exact_mod_cast Int.toNat_sub_toNat_neg (z p)
    rw [← e]
    ring
  have hAB : (∏ p ∈ S, p ^ (z p).toNat : ℕ) = ∏ p ∈ S, p ^ (-z p).toNat :=
    Nat.cast_injective (R := ℝ)
      (Real.log_injOn_pos (Set.mem_Ioi.2 (hpos _)) (Set.mem_Ioi.2 (hpos _)) hlog)
  have h1 := congrArg (fun n : ℕ => n.factorization p₀) hAB
  simp only [factorization_prod_prime_pow S hS _ hp₀] at h1
  have h2 := Int.toNat_sub_toNat_neg (z p₀)
  rw [h1, sub_self] at h2
  exact h2.symm

/-- A rational relation with a non-zero coefficient gives an integer relation with a non-zero
coefficient at the same place (clear the denominators). -/
theorem exists_int_log_relation (S : Finset ℕ) (c : ℕ → ℚ)
    (h : ∑ p ∈ S, (c p : ℝ) * Real.log (p : ℝ) = 0) {p₀ : ℕ} (hne : c p₀ ≠ 0) :
    ∃ z : ℕ → ℤ, ∑ p ∈ S, (z p : ℝ) * Real.log (p : ℝ) = 0 ∧ z p₀ ≠ 0 := by
  have hden : ∀ r : ℚ, r * (r.den : ℚ) = (r.num : ℚ) := fun r =>
    ((div_eq_iff (by exact_mod_cast r.den_ne_zero)).1 (Rat.num_div_den r)).symm
  have hz : ∀ p ∈ S, (((c p).num * ∏ j ∈ S.erase p, ((c j).den : ℤ) : ℤ) : ℝ) =
      (c p : ℝ) * ((∏ j ∈ S, ((c j).den : ℤ) : ℤ) : ℝ) := by
    intro p hp
    have h1 : (((c p).num * ∏ j ∈ S.erase p, ((c j).den : ℤ) : ℤ) : ℚ) =
        c p * ((∏ j ∈ S, ((c j).den : ℤ) : ℤ) : ℚ) := by
      push_cast
      rw [← Finset.mul_prod_erase S (fun j => ((c j).den : ℚ)) hp, ← mul_assoc, hden]
    have h2 := congrArg (fun x : ℚ => (x : ℝ)) h1
    push_cast at h2 ⊢
    exact h2
  refine ⟨fun p => (c p).num * ∏ j ∈ S.erase p, ((c j).den : ℤ), ?_, ?_⟩
  · have e : ∑ p ∈ S, (((c p).num * ∏ j ∈ S.erase p, ((c j).den : ℤ) : ℤ) : ℝ) *
          Real.log (p : ℝ) =
        ((∏ j ∈ S, ((c j).den : ℤ) : ℤ) : ℝ) * ∑ p ∈ S, (c p : ℝ) * Real.log (p : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [hz p hp]
      ring
    rw [e, h, mul_zero]
  · refine mul_ne_zero (Rat.num_ne_zero.2 hne) (Finset.prod_ne_zero_iff.2 fun j _ => ?_)
    exact_mod_cast (c j).den_ne_zero

end Okada

open Okada

/-- **The logarithms of the primes are linearly independent over `ℚ`.** -/
theorem okadaLogPrimes : OkadaLogPrimes := by
  intro S hS c h p₀ hp₀
  by_contra hne
  obtain ⟨z, hz, hz0⟩ := exists_int_log_relation S c h hne
  exact hz0 (int_log_relation S hS z hz p₀ hp₀)

end Erdos

end PiFormula
