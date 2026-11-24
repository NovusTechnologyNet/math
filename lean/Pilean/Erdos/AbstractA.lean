/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.AbstractKL

/-!
# The algebraic core of Theorem A: the proof

`abstractTheoremA : AbstractTheoremA` (the statement is in `AbstractDefs.lean`).

Status: complete, no `sorry`. See `AbstractPlan.lean` for the architecture.

The proof follows section 6 (steps 1 to 5) of
`research/2026-11-23-erdos-pm1/02_proof_part_II.md`. Fix `p₀`, let `m` be the set of the other
indices, `N_0 = N_{p₀}`, `a_0 = a_{p₀}`.

1. (`split_M`) The equation (M) reads `N_0 Z + a_0 B = 0` with
   `Z = ∑_{∅ ≠ n ⊆ m} a_n N_{m ∖ n} g_n` and `B = ∑_{n ⊆ m} a_n N_{m ∖ n} g_{n + p₀}`.
2. `a_0` is not a zero divisor, so `(1 - t_{p₀}) B = 0`.
3. Taking `ε`: `2^(s p₀) ε(Z) + (π p₀ - 1) ε(B) = 0`, and `ε(Z) = 2^(s_m) ℓ`, where `ℓ` is the
   sum in the statement (`aug_Z`).
4. `g_{n + p₀} = ν N_{n + p₀} + 2 e`, so `B = B_ν + 2 B_e` with `ε(B_ν) = c0 |S|`,
   `c0 = k_{p₀} ∏_{p ∈ m} (1 + k_p (π_p - 1))`, which is `k_{p₀}` times an odd integer
   (`aug_Bν`, `c0_parity`), and `(1 - t_{p₀}) B_e = 0`.
5. Lemma KL (`lemmaKL`): `ε(B_e) ∈ |S| ℤ_(2)`. Hence `ℓ = -(π p₀ - 1)(c0 + 2 z₁)`, which is
   `(π p₀ - 1) k_{p₀}` modulo `2^(s p₀ + 1) ℤ_(2)`.

Differences from the paper proof: the projection `pr` and the element `w` with `B = N_0 w` are
not used (the augmentation is applied to `N_0 Z + a_0 B = 0` directly), and Lemma KL is proved
from the dual form of Lemma D without lattice duality. The hypotheses `u p p = 0`,
`¬ 2^(s p + 1) ∣ π p - 1` and `SuppIn n e` of `AbstractTheoremA` are not needed.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open scoped BigOperators

open AddMonoidAlgebra (single)

namespace PiFormula

namespace Erdos

namespace Abs

variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ι → ℕ}

theorem isZ2_natCast (n : ℕ) : IsZ2 (n : ℚ) := by simp [IsZ2]

theorem aug_smul (q : ℚ) (x : GRing s) : aug (q • x) = q * aug x := by
  rw [smul_eq_single_mul, aug_mul, aug_single]

/-- Step 1: the equation (M) split according to `p₀ ∈ n` or not. -/
theorem split_M (π : ι → ℤ) (u : ι → Grp s) (g : Finset ι → GRing s) (p₀ : ι)
    (hM : ∑ n ∈ (Finset.univ : Finset ι).powerset.filter Finset.Nonempty,
      aProd π u n * normElt s nᶜ * g n = 0) :
    nrm ℚ s p₀ * (∑ n ∈ (Finset.univ.erase p₀).powerset,
        if n.Nonempty then aProd π u n * normElt s (Finset.univ.erase p₀ \ n) * g n else 0) +
      aElt π u p₀ * (∑ n ∈ (Finset.univ.erase p₀).powerset,
        aProd π u n * normElt s (Finset.univ.erase p₀ \ n) * g (insert p₀ n)) = 0 := by
  have hp₀ : p₀ ∉ Finset.univ.erase p₀ := Finset.notMem_erase p₀ _
  have huniv : (Finset.univ : Finset ι) = insert p₀ (Finset.univ.erase p₀) :=
    (Finset.insert_erase (Finset.mem_univ p₀)).symm
  rw [Finset.sum_filter] at hM
  have hM' : ∑ n ∈ (insert p₀ (Finset.univ.erase p₀)).powerset,
      (if n.Nonempty then aProd π u n * normElt s nᶜ * g n else 0) = 0 := by
    rw [← huniv]
    exact hM
  rw [Finset.sum_powerset_insert hp₀] at hM'
  refine Eq.trans ?_ hM'
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_powerset.1 hn
    have hcompl : nᶜ = insert p₀ (Finset.univ.erase p₀ \ n) := by
      ext q
      simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_erase,
        Finset.mem_univ, and_true]
      constructor
      · intro hq
        by_cases h : q = p₀
        · exact Or.inl h
        · exact Or.inr ⟨h, hq⟩
      · rintro (rfl | ⟨_, hq⟩)
        · exact fun h => hp₀ (hn' h)
        · exact hq
    have hnot : p₀ ∉ Finset.univ.erase p₀ \ n := fun h => hp₀ (Finset.mem_sdiff.1 h).1
    split_ifs
    · rw [hcompl, normElt_eq_prod, normElt_eq_prod, Finset.prod_insert hnot]
      ring
    · rw [mul_zero]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_powerset.1 hn
    have hp₀n : p₀ ∉ n := fun h => hp₀ (hn' h)
    have hcompl : (insert p₀ n)ᶜ = Finset.univ.erase p₀ \ n := by
      ext q
      simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_erase,
        Finset.mem_univ, and_true, not_or]
    simp only [Finset.insert_nonempty, ↓reduceIte]
    rw [hcompl, aProd, aProd, Finset.prod_insert hp₀n]
    ring

/-- Step 3: the augmentation of `Z`. -/
theorem aug_Z (π : ι → ℤ) (u : ι → Grp s) (g : Finset ι → GRing s) (m : Finset ι) :
    aug (∑ n ∈ m.powerset, if n.Nonempty then aProd π u n * normElt s (m \ n) * g n else 0) =
      (∏ p ∈ m, (2 : ℚ) ^ s p) * ∑ n ∈ m.powerset.filter Finset.Nonempty,
        (∏ p ∈ n, ((π p : ℚ) - 1) / 2 ^ s p) * aug (g n) := by
  rw [← augHom_apply, map_sum, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_powerset.1 hn
  split_ifs
  · rw [augHom_apply, aug_mul, aug_mul, aug_aProd, aug_normElt, ← Finset.prod_sdiff hn',
      Finset.prod_div_distrib]
    have h0 : (∏ p ∈ n, (2 : ℚ) ^ s p) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun p _ => by positivity
    field_simp
  · rw [map_zero]

/-- Step 4: the augmentation of the part of `B` that comes from the norm elements. -/
theorem aug_Bν (π : ι → ℤ) (u : ι → Grp s) (p₀ : ι) (ν : Finset ι → ℚ) :
    aug (∑ n ∈ (Finset.univ.erase p₀).powerset,
        aProd π u n * normElt s (Finset.univ.erase p₀ \ n) * (ν n • normElt s (insert p₀ n))) =
      (∑ n ∈ (Finset.univ.erase p₀).powerset, ν n * ∏ p ∈ n, ((π p : ℚ) - 1)) *
        ∏ p, (2 : ℚ) ^ s p := by
  have hp₀ : p₀ ∉ Finset.univ.erase p₀ := Finset.notMem_erase p₀ _
  rw [← augHom_apply, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_powerset.1 hn
  have hp₀n : p₀ ∉ n := fun h => hp₀ (hn' h)
  rw [augHom_apply, aug_mul, aug_mul, aug_smul, aug_aProd, aug_normElt, aug_normElt,
    Finset.prod_insert hp₀n, ← Finset.mul_prod_erase _ _ (Finset.mem_univ p₀),
    ← Finset.prod_sdiff hn']
  ring

/-- Step 4: `c0 = k_{p₀} ∏_{p ∈ m} (1 + k_p (π_p - 1))` is `k_{p₀}` times an odd integer. -/
theorem c0_parity (s : ι → ℕ) (π : ι → ℤ) (k : ι → ℕ) (hs : ∀ p, 1 ≤ s p)
    (hdiv : ∀ p, (2 : ℤ) ^ s p ∣ π p - 1) (m : Finset ι) (p₀ : ι) (hp₀ : p₀ ∉ m) :
    ∃ j : ℤ, ∑ n ∈ m.powerset, ((∏ p ∈ insert p₀ n, k p : ℕ) : ℚ) * ∏ p ∈ n, ((π p : ℚ) - 1) =
      (k p₀ : ℚ) * (2 * j + 1) := by
  have hodd : Odd (∏ p ∈ m, (1 + (k p : ℤ) * (π p - 1))) := by
    refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun p _ => ?_
    have h2 : (2 : ℤ) ∣ π p - 1 :=
      dvd_trans (dvd_pow_self 2 (by have := hs p; omega)) (hdiv p)
    exact odd_one.add_even ((even_iff_two_dvd.2 h2).mul_left _)
  obtain ⟨j, hj⟩ := hodd
  refine ⟨j, ?_⟩
  have h1 : ∀ n ∈ m.powerset,
      ((∏ p ∈ insert p₀ n, k p : ℕ) : ℚ) * ∏ p ∈ n, ((π p : ℚ) - 1) =
        (k p₀ : ℚ) * ∏ p ∈ n, ((k p : ℚ) * ((π p : ℚ) - 1)) := by
    intro n hn
    have hp₀n : p₀ ∉ n := fun h => hp₀ (Finset.mem_powerset.1 hn h)
    rw [Finset.prod_insert hp₀n, Finset.prod_mul_distrib]
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← Finset.prod_one_add]
  have h2 := congrArg (Int.cast : ℤ → ℚ) hj
  push_cast at h2
  rw [h2]

end Abs

open Abs

/-- **The algebraic core of Theorem A.** -/
theorem abstractTheoremA : AbstractTheoremA := by
  intro ι _ _ s π k u g hs hπ hval _ hg hM p₀
  choose c hc using fun p => (hval p).1
  choose! e he using hg
  have hp₀ : p₀ ∉ Finset.univ.erase p₀ := Finset.notMem_erase p₀ _
  -- Step 1: (M) reads `N_0 Z + a_0 B = 0`.
  have hsplit := split_M π u g p₀ hM
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∑ n ∈ (Finset.univ.erase p₀).powerset,
      if n.Nonempty then aProd π u n * normElt s (Finset.univ.erase p₀ \ n) * g n else 0 :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ n ∈ (Finset.univ.erase p₀).powerset,
      aProd π u n * normElt s (Finset.univ.erase p₀ \ n) * g (insert p₀ n) := ⟨_, rfl⟩
  rw [← hZ, ← hB] at hsplit
  -- Step 4: `B = B_ν + 2 B_e`.
  obtain ⟨Bν, hBν⟩ : ∃ Bν, Bν = ∑ n ∈ (Finset.univ.erase p₀).powerset,
      aProd π u n * normElt s (Finset.univ.erase p₀ \ n) *
        (((∏ p ∈ insert p₀ n, k p : ℕ) : ℚ) • normElt s (insert p₀ n)) := ⟨_, rfl⟩
  obtain ⟨Be, hBe⟩ : ∃ Be, Be = ∑ n ∈ (Finset.univ.erase p₀).powerset,
      aProd π u n * normElt s (Finset.univ.erase p₀ \ n) * e (insert p₀ n) := ⟨_, rfl⟩
  have hBsum : B = Bν + (2 : ℚ) • Be := by
    rw [hB, hBν, hBe, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [(he (insert p₀ n) (Finset.insert_nonempty p₀ n)).2.2, mul_add,
      mul_smul_comm (2 : ℚ)]
  -- Step 2: `B`, `B_ν` and `B_e` are killed by `1 - t_{p₀}`.
  have hdB : del ℚ s p₀ * B = 0 := by
    have h : aProd π u {p₀} * (del ℚ s p₀ * B) = 0 := by
      rw [aProd, Finset.prod_singleton]
      linear_combination (del ℚ s p₀) * hsplit - Z * del_mul_nrm ℚ s p₀
    exact aProd_cancel π u hπ _ h
  have hdBν : del ℚ s p₀ * Bν = 0 := by
    rw [hBν, Finset.mul_sum]
    refine Finset.sum_eq_zero fun n hn => ?_
    have hp₀n : p₀ ∉ n := fun h => hp₀ (Finset.mem_powerset.1 hn h)
    rw [normElt_eq_prod (insert p₀ n), Finset.prod_insert (f := nrm ℚ s) hp₀n,
      smul_eq_single_mul]
    linear_combination (aProd π u n * normElt s (Finset.univ.erase p₀ \ n) *
      single 0 ((∏ p ∈ insert p₀ n, k p : ℕ) : ℚ) * ∏ p ∈ n, nrm ℚ s p) * del_mul_nrm ℚ s p₀
  have hdBe : del ℚ s p₀ * Be = 0 := by
    have h : (2 : ℚ) • (del ℚ s p₀ * Be) = 0 := by
      have h' := hdB
      rw [hBsum, mul_add, hdBν, zero_add, mul_smul_comm] at h'
      exact h'
    exact (smul_eq_zero.1 h).resolve_left two_ne_zero
  -- Step 5: Lemma KL.
  obtain ⟨z₁, hz₁, hKL⟩ := lemmaKL π u hπ c hc p₀ (fun n => e (insert p₀ n))
    (fun n => (he (insert p₀ n) (Finset.insert_nonempty p₀ n)).1) Be hBe hdBe
  -- Step 3: augmentations.
  have haugZ : aug Z = (∏ p ∈ Finset.univ.erase p₀, (2 : ℚ) ^ s p) *
      ∑ n ∈ (Finset.univ.erase p₀).powerset.filter Finset.Nonempty,
        (∏ p ∈ n, ((π p : ℚ) - 1) / 2 ^ s p) * aug (g n) := by
    rw [hZ]
    exact aug_Z π u g _
  obtain ⟨j, hj⟩ := c0_parity s π k hs (fun p => (hval p).1) (Finset.univ.erase p₀) p₀ hp₀
  have haugBν : aug Bν = ((k p₀ : ℚ) * (2 * j + 1)) * ∏ p, (2 : ℚ) ^ s p := by
    rw [hBν, aug_Bν, hj]
  have haugB : aug B = aug Bν + 2 * aug Be := by
    rw [hBsum, aug_add, aug_smul]
  have h0 := congrArg aug hsplit
  rw [aug_add, aug_mul, aug_mul, aug_nrm, aug_aElt, aug_zero, haugZ, haugB, haugBν, hKL,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ p₀)] at h0
  obtain ⟨Em, hEm⟩ : ∃ Em, Em = ∏ p ∈ Finset.univ.erase p₀, (2 : ℚ) ^ s p := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = ∑ n ∈ (Finset.univ.erase p₀).powerset.filter Finset.Nonempty,
      (∏ p ∈ n, ((π p : ℚ) - 1) / 2 ^ s p) * aug (g n) := ⟨_, rfl⟩
  rw [← hEm, ← hℓ] at h0
  rw [← hℓ]
  have hEm0 : Em ≠ 0 := by
    rw [hEm]
    exact Finset.prod_ne_zero_iff.2 fun p _ => by positivity
  have hE0 : (2 : ℚ) ^ s p₀ ≠ 0 := by positivity
  have hπ' : (π p₀ : ℚ) - 1 = 2 ^ s p₀ * c p₀ := by
    have h : ((π p₀ - 1 : ℤ) : ℚ) = ((2 ^ s p₀ * c p₀ : ℤ) : ℚ) := by rw [hc p₀]
    push_cast at h
    exact h
  have h1 : ℓ + ((π p₀ : ℚ) - 1) * ((k p₀ : ℚ) * (2 * j + 1) + 2 * z₁) = 0 := by
    have h : (2 ^ s p₀ * Em) *
        (ℓ + ((π p₀ : ℚ) - 1) * ((k p₀ : ℚ) * (2 * j + 1) + 2 * z₁)) = 0 := by
      linear_combination h0
    exact (mul_eq_zero.1 h).resolve_left (mul_ne_zero hE0 hEm0)
  refine ⟨-(c p₀ : ℚ) * ((k p₀ : ℚ) + k p₀ * j + z₁), ?_, ?_⟩
  · exact isZ2_mul (isZ2_neg (isZ2_intCast _))
      (isZ2_add (isZ2_add (isZ2_natCast _) (isZ2_mul (isZ2_natCast _) (isZ2_intCast _))) hz₁)
  · rw [pow_succ]
    linear_combination h1 - 2 * ((k p₀ : ℚ) + k p₀ * j + z₁) * hπ'

end Erdos

end PiFormula
