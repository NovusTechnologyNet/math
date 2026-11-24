/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Base5.Series

/-!
# Base 5: the support of a multiplicative relation

A multiplicative relation is a product `∏ (1 - r/t)^(e_r)`, `t = √5`, over roots of unity `r`,
that is a root of unity. This file proves, from the existence of good primes (`GoodPrimes5`),
that such a relation only involves the two roots `1` and `-1`
(`support_subset_pm_one`).

It is the base-5 version of `Base3/Support.lean`. The two roots `1` and `-1` are those for
which `t - r` has no odd prime factor: `(t - 1)(t + 1) = 4`.

A good prime for `r` (`HasGoodPrime5`) is a prime ideal of the algebraic integers that
contains `t - r` and an odd rational prime `p ≠ 5` not dividing the order of `r`.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace Base5

/-! ## 1. Relations and the private prime -/

/-- A multiplicative relation: `∏_{r ∈ S} (1 - r/t)^(e_r)` is a root of unity. -/
def IsRelation5 (S : Finset ℂ) (e : ℂ → ℤ) : Prop :=
  ∃ ξ : ℂ, IsOfFinOrder ξ ∧ ∏ r ∈ S, (1 - r / t5) ^ (e r) = ξ

/-- The cleared form `∏ (t - r)^(e⁺) · t^(N⁻) = ξ ∏ (t - r)^(e⁻) · t^(N⁺)`. -/
theorem cleared_of_relation5 {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ}
    (h : IsRelation5 S e) : ∃ ξ : ℂ, IsOfFinOrder ξ ∧
      (∏ r ∈ S, (t5 - r) ^ (e r).toNat) * t5 ^ (∑ r ∈ S, (-e r).toNat) =
        ξ * (∏ r ∈ S, (t5 - r) ^ (-e r).toNat) * t5 ^ (∑ r ∈ S, (e r).toNat) := by
  obtain ⟨ξ, hξ, hrel⟩ := h
  refine ⟨ξ, hξ, ?_⟩
  -- each factor: (1 - r/t)^e (t - r)^(-e)⁺ t^(e⁺) = (t - r)^(e⁺) t^((-e)⁺)
  have hfac : ∀ r ∈ S, (1 - r / t5) ^ (e r) * ((t5 - r) ^ (-e r).toNat * t5 ^ (e r).toNat) =
      (t5 - r) ^ (e r).toNat * t5 ^ (-e r).toNat := by
    intro r hr
    have hne : t5 - r ≠ 0 := t5_sub_ne_zero (norm_root (hS r hr))
    have hz1 : (t5 - r) ^ (e r) = (t5 - r) ^ (e r).toNat / (t5 - r) ^ (-e r).toNat := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hne]
      congr 1
      omega
    have hz2 : t5 ^ (e r) = t5 ^ (e r).toNat / t5 ^ (-e r).toNat := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ t5_ne_zero]
      congr 1
      omega
    have h1 : (t5 - r) ^ (-e r).toNat ≠ 0 := pow_ne_zero _ hne
    have h2 : t5 ^ (-e r).toNat ≠ 0 := pow_ne_zero _ t5_ne_zero
    have h3 : t5 ^ (e r).toNat ≠ 0 := pow_ne_zero _ t5_ne_zero
    rw [w5_eq, div_zpow, hz1, hz2]
    field_simp
  have hprod := Finset.prod_congr rfl hfac
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, hrel] at hprod
  rw [← hprod]
  ring

/-- **The private prime.** If `t - r₀ ∈ P`, `t ∉ P` and `t - r ∉ P` for the other `r ∈ S`, then
`e_{r₀} = 0`. -/
theorem coeff_eq_zero_of_private_ideal5 {P : Ideal Aint} [P.IsPrime] {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} (h : IsRelation5 S e) {r₀ : ℂ} (hr₀ : r₀ ∈ S)
    (ht : ¬ InP P t5) (h0 : InP P (t5 - r₀)) (hpriv : ∀ r ∈ S, r ≠ r₀ → ¬ InP P (t5 - r)) :
    e r₀ = 0 := by
  classical
  obtain ⟨ξ, hξ, hc⟩ := cleared_of_relation5 hS h
  have hint : ∀ r ∈ S, ∀ n : ℕ, IsIntegral ℤ ((t5 - r) ^ n) :=
    fun r hr n => (isIntegral_t5_sub (hS r hr)).pow n
  have hprodI : ∀ f : ℂ → ℕ, IsIntegral ℤ (∏ r ∈ S, (t5 - r) ^ f r) :=
    fun f => IsIntegral.prod _ fun r hr => hint r hr _
  have side : ∀ f g : ℂ → ℕ, 0 < f r₀ → g r₀ = 0 → ∀ a b : ℕ, ∀ c : ℂ, IsOfFinOrder c →
      (∏ r ∈ S, (t5 - r) ^ f r) * t5 ^ a = c * (∏ r ∈ S, (t5 - r) ^ g r) * t5 ^ b → False := by
    intro f g hf hg a b c hc heq
    have hL : InP P ((∏ r ∈ S, (t5 - r) ^ f r) * t5 ^ a) :=
      (inP_prod_of_mem _ (fun r hr => hint r hr _) hr₀ (h0.pow hf)).mul_right
        (isIntegral_t5.pow a)
    rw [heq] at hL
    rcases inP_mul ((isIntegral_of_finOrder hc).mul (hprodI g)) (isIntegral_t5.pow b) hL with
      hL | hL
    · rcases inP_mul (isIntegral_of_finOrder hc) (hprodI g) hL with hL | hL
      · exact not_inP_root hc hL
      · obtain ⟨r, hr, hL⟩ := inP_prod S _ (fun r hr => hint r hr _) hL
        obtain ⟨hpos, hL⟩ := inP_of_pow (isIntegral_t5_sub (hS r hr)) hL
        by_cases hrr : r = r₀
        · rw [hrr, hg] at hpos; exact lt_irrefl 0 hpos
        · exact hpriv r hr hrr hL
    · exact ht (inP_of_pow isIntegral_t5 hL).2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1 : 0 < (-e r₀).toNat := by omega
    have h2 : (e r₀).toNat = 0 := by omega
    have hξ0 : ξ ≠ 0 := ne_zero_of_finOrder hξ
    refine side (fun r => (-e r).toNat) (fun r => (e r).toNat) h1 h2
      (∑ r ∈ S, (e r).toNat) (∑ r ∈ S, (-e r).toNat) ξ⁻¹ (isOfFinOrder_inv' hξ) ?_
    rw [mul_assoc ξ⁻¹, hc]
    field_simp
  · have h1 : 0 < (e r₀).toNat := by omega
    have h2 : (-e r₀).toNat = 0 := by omega
    exact side (fun r => (e r).toNat) (fun r => (-e r).toNat) h1 h2 _ _ ξ hξ hc

/-! ## 2. The support theorem -/

/-- **The support theorem in base 5 (from `GoodPrimes5`).** Every multiplicative relation is
supported on the two roots `1` and `-1`. -/
theorem support_subset_pm_one (hG : GoodPrimes5) {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {e : ℂ → ℤ} (h : IsRelation5 S e) : ∀ r ∈ S, r ≠ 1 → r ≠ -1 → e r = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set S' := S.filter (fun r => e r ≠ 0) with hS'def
  have hS' : ∀ r ∈ S', IsOfFinOrder r := fun r hr => hS r (Finset.mem_filter.1 hr).1
  have h' : IsRelation5 S' e := by
    obtain ⟨ξ, hξ, hrel⟩ := h
    refine ⟨ξ, hξ, ?_⟩
    rw [hS'def, Finset.prod_filter_of_ne (p := fun r => e r ≠ 0)
      (fun r _ hr hc => hr (by simp [hc]))]
    exact hrel
  set T := S'.filter (fun r => r ≠ 1 ∧ r ≠ -1) with hTdef
  have hT : T.Nonempty := by
    obtain ⟨r, hr, hr1, hrn, hre⟩ := hcon
    exact ⟨r, by simp [hTdef, hS'def, hr, hr1, hrn, hre]⟩
  obtain ⟨r, hrT, hmax⟩ := Finset.exists_max_image T orderOf hT
  have hrS' : r ∈ S' := (Finset.mem_filter.1 hrT).1
  have hr1 : r ≠ 1 := (Finset.mem_filter.1 hrT).2.1
  have hrn : r ≠ -1 := (Finset.mem_filter.1 hrT).2.2
  have her : e r ≠ 0 := (Finset.mem_filter.1 hrS').2
  have hr := hS' r hrS'
  obtain ⟨P, hP, p, hp, hp2, hp5, hpr, hpP, htr⟩ := hG r hr hr1 hrn
  -- `t ∉ P`: else `5 = t² ∈ P`, and `p ∈ P` is prime to 5
  have ht : ¬ InP P t5 := by
    intro ht
    have h2 := ht.mul_right isIntegral_t5
    rw [← pow_two, t5_sq] at h2
    have hcop : Nat.Coprime 5 p :=
      (Nat.coprime_primes Nat.prime_five hp).2 (Ne.symm hp5)
    exact not_inP_coprime (a := 5) (b := p) hcop (by exact_mod_cast h2) hpP
  refine her (coeff_eq_zero_of_private_ideal5 hS' h' hrS' ht htr ?_)
  intro r' hr' hne htr'
  have hr'f := hS' r' hr'
  have hr0 : r ≠ 0 := ne_zero_of_finOrder hr
  set u := r' / r with hu
  have hufin : IsOfFinOrder u := isOfFinOrder_div' hr'f hr
  have hu1 : InP P (u - 1) := by
    have hd : InP P (r' - r) := by
      have := htr.sub htr'
      rwa [show t5 - r - (t5 - r') = r' - r by ring] at this
    have hrinv : IsIntegral ℤ r⁻¹ := isIntegral_of_finOrder (isOfFinOrder_inv' hr)
    have := hd.mul_right hrinv
    rwa [show (r' - r) * r⁻¹ = u - 1 by rw [hu]; field_simp] at this
  obtain ⟨a, hord⟩ := orderOf_eq_prime_pow_of_inP hp hpP hufin hu1
  have ha : 0 < a := by
    by_contra h0
    push Not at h0
    rw [Nat.le_zero.1 h0, pow_zero, orderOf_eq_one_iff, hu, div_eq_one_iff_eq hr0] at hord
    exact hne hord
  have hcop : Nat.Coprime (orderOf r) (orderOf u) := by
    rw [hord]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpr).symm
  have hr'eq : r' = r * u := by rw [hu]; field_simp
  have hordr' : orderOf r' = orderOf r * p ^ a := by
    rw [hr'eq, (Commute.all r u).orderOf_mul_eq_mul_orderOf_of_coprime hcop, hord]
  by_cases hr'pm : r' = 1 ∨ r' = -1
  · -- `1` and `-1` have order at most 2, which the odd prime `p` does not divide
    have h2 : orderOf r' ∣ 2 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rcases hr'pm with h1 | h1 <;> rw [h1] <;> norm_num
    have hp2' : p ∣ 2 := by
      refine Dvd.dvd.trans ?_ h2
      rw [hordr']
      exact Dvd.dvd.mul_left (dvd_pow_self p ha.ne') _
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2')
  · push Not at hr'pm
    have hle := hmax r' (Finset.mem_filter.2 ⟨hr', hr'pm⟩)
    rw [hordr'] at hle
    have : orderOf r * 1 < orderOf r * p ^ a :=
      Nat.mul_lt_mul_of_pos_left (Nat.one_lt_pow ha.ne' hp.one_lt) hr.orderOf_pos
    omega

end Base5

end PiFormula
