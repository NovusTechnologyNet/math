import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Theorem A from the abstract theorem, part 2: the homomorphisms `χ_p`

For a prime `p` and `2^t ∣ p - 1` there is a surjective homomorphism from `(ℤ/p)^×` onto the
cyclic group `ℤ/2^t` (`exists_isLogChar`), because `(ℤ/p)^×` is cyclic of order `p - 1`. It is
handled as a function `χ : ℤ/p → ℤ/2^t` with `χ (a b) = χ a + χ b` for `a, b ≠ 0`
(`IsLogChar`). Every class of `ℤ/2^t` is the image of exactly `(p - 1)/2^t` non-zero residues
(`IsLogChar.card_fiber`).
-/

open scoped BigOperators

namespace PiFormula

namespace Erdos

namespace Arith

/-- A surjective homomorphism from `(ℤ/p)^×` onto `ℤ/2^t`, written as a function on `ℤ/p`. -/
structure IsLogChar (p t : ℕ) (χ : ZMod p → ZMod (2 ^ t)) : Prop where
  mul : ∀ a b : ZMod p, a ≠ 0 → b ≠ 0 → χ (a * b) = χ a + χ b
  surj : ∀ c : ZMod (2 ^ t), ∃ a : ZMod p, a ≠ 0 ∧ χ a = c

theorem exists_isLogChar (p t : ℕ) [Fact p.Prime] (h : 2 ^ t ∣ p - 1) :
    ∃ χ : ZMod p → ZMod (2 ^ t), IsLogChar p t χ := by
  classical
  have hcyc : IsCyclic (ZMod p)ˣ := inferInstance
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hd : 2 ^ t ∣ Nat.card (ZMod p)ˣ := by
    rw [hcard]
    exact h
  refine ⟨fun a => if ha : a = 0 then 0 else
    ZMod.castHom hd (ZMod (2 ^ t))
      (Multiplicative.toAdd ((zmodCyclicMulEquiv hcyc).symm (Units.mk0 a ha))), ?_, ?_⟩
  · intro a b ha hb
    have hab : a * b ≠ 0 := mul_ne_zero ha hb
    have e : Units.mk0 (a * b) hab = Units.mk0 a ha * Units.mk0 b hb := Units.ext rfl
    simp only [ha, hb, hab, ↓reduceDIte]
    rw [e, map_mul, toAdd_mul, map_add]
  · intro c
    obtain ⟨z, rfl⟩ := ZMod.castHom_surjective hd c
    refine ⟨((zmodCyclicMulEquiv hcyc (Multiplicative.ofAdd z) : (ZMod p)ˣ) : ZMod p),
      Units.ne_zero _, ?_⟩
    have e : Units.mk0 ((zmodCyclicMulEquiv hcyc (Multiplicative.ofAdd z) : (ZMod p)ˣ) : ZMod p)
        (Units.ne_zero _) = zmodCyclicMulEquiv hcyc (Multiplicative.ofAdd z) := Units.ext rfl
    simp only [Units.ne_zero, ↓reduceDIte]
    rw [e, MulEquiv.symm_apply_apply, toAdd_ofAdd]

/-- Every class is the image of exactly `(p - 1)/2^t` non-zero residues. -/
theorem IsLogChar.card_fiber {p t : ℕ} [Fact p.Prime] {χ : ZMod p → ZMod (2 ^ t)}
    (h : IsLogChar p t χ) (c : ZMod (2 ^ t)) :
    2 ^ t * (Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ χ a = c)).card = p - 1 := by
  have heq : ∀ c : ZMod (2 ^ t),
      (Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ χ a = c)).card =
        (Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ χ a = 0)).card := by
    intro c
    obtain ⟨a₀, ha₀, hc⟩ := h.surj c
    symm
    refine Finset.card_bij' (fun a _ => a * a₀) (fun a _ => a * a₀⁻¹) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      refine ⟨mul_ne_zero ha.1 ha₀, ?_⟩
      rw [h.mul a a₀ ha.1 ha₀, ha.2, zero_add, hc]
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      have hne : a * a₀⁻¹ ≠ 0 := mul_ne_zero ha.1 (inv_ne_zero ha₀)
      refine ⟨hne, ?_⟩
      have e := h.mul (a * a₀⁻¹) a₀ hne ha₀
      rw [inv_mul_cancel_right₀ ha₀, ha.2, hc] at e
      exact (add_eq_right.1 e.symm)
    · intro a _
      exact mul_inv_cancel_right₀ ha₀ a
    · intro a _
      exact inv_mul_cancel_right₀ ha₀ a
  have hmaps : Set.MapsTo χ ↑(Finset.univ.filter (fun a : ZMod p => a ≠ 0))
      ↑(Finset.univ : Finset (ZMod (2 ^ t))) := fun a _ => Finset.mem_coe.2 (Finset.mem_univ _)
  have htot : (Finset.univ.filter (fun a : ZMod p => a ≠ 0)).card = p - 1 := by
    rw [Finset.filter_ne' Finset.univ (0 : ZMod p), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
  rw [Finset.card_eq_sum_card_fiberwise hmaps] at htot
  have hfil : ∀ c : ZMod (2 ^ t),
      ((Finset.univ.filter (fun a : ZMod p => a ≠ 0)).filter (fun a => χ a = c)).card =
        (Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ χ a = 0)).card := by
    intro c
    rw [Finset.filter_filter, heq c]
  rw [Finset.sum_congr rfl (fun c _ => hfil c), Finset.sum_const, Finset.card_univ, ZMod.card,
    smul_eq_mul] at htot
  rw [heq c]
  exact htot

end Arith

end Erdos

end PiFormula
