/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.ArithDefs
public import Pilean.Erdos.ArithRing
public import Pilean.Erdos.ArithWeight

/-!
# Theorem A from the abstract theorem, part 7: step 3 (the sum in the conclusion is `ℓ_p`)

`ellProp : EllProp` (the statement is in `ArithDefs.lean`): for every `f : ℤ/q → ℚ` and every
prime `p₀` of `q`,

  `∑_{∅ ≠ n ⊆ P ∖ {p₀}} o(n) ε(g_n) = ℓ_{p₀}`,

where `o(n) = ∏_{p ∈ n} (p - 1)/2^(s_p)`. Paper: `02_proof_part_II.md`, section 6, step 3.

Steps:

* `ell_aug_gElt`: `o(n) ε(g_n) = ∑_{r : n(r) = n} f(r)` (`ε` of `[σ]` is `1`, and `o(n) ≠ 0`);
* `ell_supp_mem_iff`: `n(r)` is non-empty and does not contain `p₀` exactly when `r ≠ 0` and
  the component of `r` at `p₀` is `0`;
* `ell_sum_fibers`: so the left side is the sum of `f(r)` over these `r`;
* `ell_crt_eq_zero_iff`: for a natural number `r`, the component of `r` at `p` is `0` exactly
  when `p^(v_p(q)) ∣ r`;
* `ell_sum_natCast`: the `r ≠ 0` in `ℤ/q` with component `0` at `p₀` are the classes of the
  `1 ≤ r ≤ q - 1` with `p₀^(v_{p₀}(q)) ∣ r`, so the sum is `ell q f p₀`.

Status: complete. Neither `q` odd nor any property of the maps `χ_p` is used.
-/

@[expose] public section

open scoped BigOperators

open AddMonoidAlgebra (single)

namespace PiFormula

namespace Erdos

namespace Arith

section Ell

variable {q : ℕ} [NeZero q]

/-- `o(n) ε(g_n) = ∑_{r : n(r) = n} f(r)`. -/
theorem ell_aug_gElt (χ : ∀ p : Idx q, ZMod p.1 → ZMod (2 ^ sExp q p)) (f : ZMod q → ℚ)
    (n : Finset (Idx q)) :
    oRat q n * aug (gElt q χ f n) =
      ∑ r ∈ Finset.univ.filter (fun r : ZMod q => suppPi q (crt q r) = n), f r := by
  unfold gElt
  rw [aug_smul, aug_sum, ← mul_assoc, mul_inv_cancel₀ (oRat_ne_zero n), one_mul]
  exact Finset.sum_congr rfl fun r _ => aug_single _ _

/-- `n(r)` is not empty exactly when `r ≠ 0`. -/
theorem ell_supp_nonempty_iff (r : ZMod q) : (suppPi q (crt q r)).Nonempty ↔ r ≠ 0 := by
  constructor
  · rintro ⟨p, hp⟩ rfl
    have h : crt q 0 p ≠ 0 := (Finset.mem_filter.1 hp).2
    rw [map_zero] at h
    exact h rfl
  · intro hr
    by_contra hne
    apply hr
    apply (crt q).injective
    rw [map_zero]
    funext p
    by_contra hp
    exact hne ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ p, hp⟩⟩

/-- `p₀ ∉ n(r)` exactly when the component of `r` at `p₀` is `0`. -/
theorem ell_supp_subset_iff (p₀ : Idx q) (r : ZMod q) :
    suppPi q (crt q r) ⊆ (Finset.univ : Finset (Idx q)).erase p₀ ↔ crt q r p₀ = 0 := by
  constructor
  · intro h
    by_contra hp
    have h1 : p₀ ∈ suppPi q (crt q r) := Finset.mem_filter.2 ⟨Finset.mem_univ p₀, hp⟩
    exact (Finset.mem_erase.1 (h h1)).1 rfl
  · intro h p hp
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ p⟩
    rintro rfl
    exact (Finset.mem_filter.1 hp).2 h

/-- `n(r)` is a non-empty subset of `P ∖ {p₀}` exactly when `r ≠ 0` and the component of `r`
at `p₀` is `0`. -/
theorem ell_supp_mem_iff (p₀ : Idx q) (r : ZMod q) :
    suppPi q (crt q r) ∈
        ((Finset.univ : Finset (Idx q)).erase p₀).powerset.filter Finset.Nonempty ↔
      r ≠ 0 ∧ crt q r p₀ = 0 := by
  rw [Finset.mem_filter, Finset.mem_powerset, ell_supp_subset_iff, ell_supp_nonempty_iff]
  exact and_comm

/-- The sum over the non-empty `n ⊆ P ∖ {p₀}` of the sums over `{r : n(r) = n}` is the sum over
the `r ≠ 0` with component `0` at `p₀`. -/
theorem ell_sum_fibers (f : ZMod q → ℚ) (p₀ : Idx q) :
    ∑ n ∈ ((Finset.univ : Finset (Idx q)).erase p₀).powerset.filter Finset.Nonempty,
      ∑ r ∈ Finset.univ.filter (fun r : ZMod q => suppPi q (crt q r) = n), f r =
    ∑ r ∈ Finset.univ.filter (fun r : ZMod q => r ≠ 0 ∧ crt q r p₀ = 0), f r := by
  classical
  have hmaps : ∀ r ∈ Finset.univ.filter (fun r : ZMod q => r ≠ 0 ∧ crt q r p₀ = 0),
      suppPi q (crt q r) ∈
        ((Finset.univ : Finset (Idx q)).erase p₀).powerset.filter Finset.Nonempty :=
    fun r hr => (ell_supp_mem_iff p₀ r).2 (Finset.mem_filter.1 hr).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  refine Finset.sum_congr rfl fun n hn => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨(ell_supp_mem_iff p₀ r).1 ?_, h⟩
    rw [h]
    exact hn
  · exact fun h => h.2

/-- The component at `p` of the class of a natural number `r` is the class of `r`. -/
theorem ell_crt_natCast (p : Idx q) (r : ℕ) : crt q (r : ZMod q) p = (r : LocRing q p) := by
  rw [map_natCast]
  rfl

/-- The component at `p` of the class of `r` is `0` exactly when `p^(v_p(q)) ∣ r`. -/
theorem ell_crt_eq_zero_iff (p : Idx q) (r : ℕ) :
    crt q (r : ZMod q) p = 0 ↔ p.1 ^ padicValNat p.1 q ∣ r := by
  rw [ell_crt_natCast, ZMod.natCast_eq_zero_iff, ← kExp_eq]

/-- The sum of `f(r)` over the `r ≠ 0` in `ℤ/q` with component `0` at `p₀` is `ℓ_{p₀}`. -/
theorem ell_sum_natCast (f : ZMod q → ℚ) (p₀ : Idx q) :
    ∑ r ∈ Finset.univ.filter (fun r : ZMod q => r ≠ 0 ∧ crt q r p₀ = 0), f r =
      ell q f p₀.1 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  unfold ell
  symm
  refine Finset.sum_nbij' (fun r : ℕ => (r : ZMod q)) (fun r : ZMod q => r.val) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_filter.1 hr
    rw [Finset.mem_Icc] at hr1
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, (ell_crt_eq_zero_iff p₀ r).2 hr2⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  · intro r hr
    obtain ⟨hr1, hr2⟩ := (Finset.mem_filter.1 hr).2
    have hlt : r.val < q := ZMod.val_lt r
    have hne : r.val ≠ 0 := fun h => hr1 ((ZMod.val_eq_zero r).1 h)
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
    rw [← ell_crt_eq_zero_iff, ZMod.natCast_zmod_val]
    exact hr2
  · intro r hr
    have hr1 := Finset.mem_Icc.1 (Finset.mem_filter.1 hr).1
    exact ZMod.val_natCast_of_lt (by omega)
  · intro r _
    exact ZMod.natCast_zmod_val r
  · intro r _
    rfl

end Ell

/-- **Step 3 of section 6**: the sum in the conclusion of the abstract theorem is `ℓ_p`. -/
theorem ellProp : EllProp := by
  intro q _ _ χ f p₀
  refine (Finset.sum_congr rfl fun n _ => ell_aug_gElt χ f n).trans ?_
  rw [ell_sum_fibers, ell_sum_natCast]

end Arith

end Erdos

end PiFormula
