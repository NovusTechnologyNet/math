module

public import Pilean.RatBase.SeriesR

/-!
# A rational base `p/q`: the support of a multiplicative relation

A multiplicative relation is a product `∏ (1 - r x)^(e_r)`, `x = √(q/p)`, over roots of unity
`r`, that is a root of unity. With `u = √(pq)` one has `1 - r x = (u - q r)/u`, so after
clearing denominators it is a relation among the algebraic integers `u - q r` and `u`.

This file proves, from the existence of good primes (`GoodPrimesR p q`), that such a relation
only involves the four roots `1, -1, i, -i` (`support_subset_fourth_rootsR`). It is the version
for a rational base of `BaseB/Support.lean`. A good prime for `r` is a prime ideal `P` of the
algebraic integers that contains `u - q r` and an odd rational prime `ℓ` dividing neither `p q`
nor the order of `r`. Such a `P`

* does not contain `u` (as `u² = pq` and `ℓ ∤ pq`);
* contains no other `u - q r'` of the relation: else `q (r' - r) ∈ P`, and `ℓ ∤ q` gives
  `r' - r ∈ P`, so the order of `r'/r` is a power of `ℓ`, as for integer bases.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace RatBase

/-! ## 1. Relations and the private prime -/

/-- A multiplicative relation: `∏_{r ∈ S} (1 - r x)^(e_r)` is a root of unity. -/
def IsRelationRat (p q : ℕ) (S : Finset ℂ) (e : ℂ → ℤ) : Prop :=
  ∃ ξ : ℂ, IsOfFinOrder ξ ∧ ∏ r ∈ S, (1 - r * xRat p q) ^ (e r) = ξ

/-- The cleared form of `∏ (a_r/c)^(e_r) = ξ`:
`∏ a_r^(e⁺) · c^(N⁻) = ξ ∏ a_r^(e⁻) · c^(N⁺)`. -/
private theorem cleared_of_prod_div {S : Finset ℂ} {a : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (ha : ∀ r ∈ S, a r ≠ 0) {e : ℂ → ℤ} {ξ : ℂ} (hrel : ∏ r ∈ S, (a r / c) ^ (e r) = ξ) :
    (∏ r ∈ S, a r ^ (e r).toNat) * c ^ (∑ r ∈ S, (-e r).toNat) =
      ξ * (∏ r ∈ S, a r ^ (-e r).toNat) * c ^ (∑ r ∈ S, (e r).toNat) := by
  -- each factor: (a/c)^e a^((-e)⁺) c^(e⁺) = a^(e⁺) c^((-e)⁺)
  have hfac : ∀ r ∈ S, (a r / c) ^ (e r) * (a r ^ (-e r).toNat * c ^ (e r).toNat) =
      a r ^ (e r).toNat * c ^ (-e r).toNat := by
    intro r hr
    have hne : a r ≠ 0 := ha r hr
    have hz1 : a r ^ (e r) = a r ^ (e r).toNat / a r ^ (-e r).toNat := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hne]
      congr 1
      omega
    have hz2 : c ^ (e r) = c ^ (e r).toNat / c ^ (-e r).toNat := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hc]
      congr 1
      omega
    have h1 : a r ^ (-e r).toNat ≠ 0 := pow_ne_zero _ hne
    have h2 : c ^ (-e r).toNat ≠ 0 := pow_ne_zero _ hc
    have h3 : c ^ (e r).toNat ≠ 0 := pow_ne_zero _ hc
    rw [div_zpow, hz1, hz2]
    field_simp
  have hprod := Finset.prod_congr rfl hfac
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, hrel] at hprod
  rw [← hprod]
  ring

/-- **The private prime**, for algebraic integers `a_r` and `c`: if `∏ (a_r/c)^(e_r)` is a root
of unity, `a_{r₀} ∈ P`, `c ∉ P` and `a_r ∉ P` for the other `r ∈ S`, then `e_{r₀} = 0`. -/
private theorem coeff_eq_zero_of_private_prod {P : Ideal Aint} [P.IsPrime] {S : Finset ℂ}
    {a : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) (hcI : IsIntegral ℤ c) (ha : ∀ r ∈ S, a r ≠ 0)
    (haI : ∀ r ∈ S, IsIntegral ℤ (a r)) {e : ℂ → ℤ} {ξ : ℂ} (hξ : IsOfFinOrder ξ)
    (hrel : ∏ r ∈ S, (a r / c) ^ (e r) = ξ) {r₀ : ℂ} (hr₀ : r₀ ∈ S) (ht : ¬ InP P c)
    (h0 : InP P (a r₀)) (hpriv : ∀ r ∈ S, r ≠ r₀ → ¬ InP P (a r)) : e r₀ = 0 := by
  classical
  have hcl := cleared_of_prod_div hc ha hrel
  have hint : ∀ r ∈ S, ∀ n : ℕ, IsIntegral ℤ (a r ^ n) := fun r hr n => (haI r hr).pow n
  have hprodI : ∀ f : ℂ → ℕ, IsIntegral ℤ (∏ r ∈ S, a r ^ f r) :=
    fun f => IsIntegral.prod _ fun r hr => hint r hr _
  have side : ∀ f g : ℂ → ℕ, 0 < f r₀ → g r₀ = 0 → ∀ m n : ℕ, ∀ d : ℂ, IsOfFinOrder d →
      (∏ r ∈ S, a r ^ f r) * c ^ m = d * (∏ r ∈ S, a r ^ g r) * c ^ n → False := by
    intro f g hf hg m n d hd heq
    have hL : InP P ((∏ r ∈ S, a r ^ f r) * c ^ m) :=
      (inP_prod_of_mem _ (fun r hr => hint r hr _) hr₀ (h0.pow hf)).mul_right (hcI.pow m)
    rw [heq] at hL
    rcases inP_mul ((isIntegral_of_finOrder hd).mul (hprodI g)) (hcI.pow n) hL with hL | hL
    · rcases inP_mul (isIntegral_of_finOrder hd) (hprodI g) hL with hL | hL
      · exact not_inP_root hd hL
      · obtain ⟨r, hr, hL⟩ := inP_prod S _ (fun r hr => hint r hr _) hL
        obtain ⟨hpos, hL⟩ := inP_of_pow (haI r hr) hL
        by_cases hrr : r = r₀
        · rw [hrr, hg] at hpos; exact lt_irrefl 0 hpos
        · exact hpriv r hr hrr hL
    · exact ht (inP_of_pow hcI hL).2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1 : 0 < (-e r₀).toNat := by omega
    have h2 : (e r₀).toNat = 0 := by omega
    have hξ0 : ξ ≠ 0 := ne_zero_of_finOrder hξ
    refine side (fun r => (-e r).toNat) (fun r => (e r).toNat) h1 h2
      (∑ r ∈ S, (e r).toNat) (∑ r ∈ S, (-e r).toNat) ξ⁻¹ (isOfFinOrder_inv' hξ) ?_
    rw [mul_assoc ξ⁻¹, hcl]
    field_simp
  · have h1 : 0 < (e r₀).toNat := by omega
    have h2 : (-e r₀).toNat = 0 := by omega
    exact side (fun r => (e r).toNat) (fun r => (-e r).toNat) h1 h2 _ _ ξ hξ hcl

/-- **The private prime in the base `p/q`.** If `u - q r₀ ∈ P`, `u ∉ P` and `u - q r ∉ P` for
the other `r ∈ S`, then `e_{r₀} = 0`. -/
theorem coeff_eq_zero_of_private_idealR {p q : ℕ} (hq : 0 < q) (hqp : q < p) {P : Ideal Aint}
    [P.IsPrime] {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ}
    (h : IsRelationRat p q S e) {r₀ : ℂ} (hr₀ : r₀ ∈ S) (ht : ¬ InP P (BaseB.tB (p * q)))
    (h0 : InP P (BaseB.tB (p * q) - (q : ℂ) * r₀))
    (hpriv : ∀ r ∈ S, r ≠ r₀ → ¬ InP P (BaseB.tB (p * q) - (q : ℂ) * r)) : e r₀ = 0 := by
  obtain ⟨ξ, hξ, hrel⟩ := h
  have hrel' : ∏ r ∈ S, ((BaseB.tB (p * q) - (q : ℂ) * r) / BaseB.tB (p * q)) ^ (e r) = ξ := by
    rw [← hrel]
    exact Finset.prod_congr rfl fun r _ => by rw [wR_eq hq hqp]
  exact coeff_eq_zero_of_private_prod (a := fun r => BaseB.tB (p * q) - (q : ℂ) * r)
    (tB_mul_ne_zero hq hqp) (BaseB.isIntegral_tB _)
    (fun r hr => tB_sub_mul_ne_zero hq hqp (hS r hr))
    (fun r hr => isIntegral_tB_sub_mul p q (hS r hr)) hξ hrel' hr₀ ht h0 hpriv

/-! ## 2. The support theorem -/

/-- **The support theorem in the base `p/q` (from `GoodPrimesR p q`).** Every multiplicative
relation is supported on the four roots `1, -1, i, -i`, that is, on the roots with `r⁴ = 1`. -/
theorem support_subset_fourth_rootsR {p q : ℕ} (hq : 0 < q) (hqp : q < p)
    (hG : GoodPrimesR p q) {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ}
    (h : IsRelationRat p q S e) : ∀ r ∈ S, r ^ 4 ≠ 1 → e r = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set S' := S.filter (fun r => e r ≠ 0) with hS'def
  have hS' : ∀ r ∈ S', IsOfFinOrder r := fun r hr => hS r (Finset.mem_filter.1 hr).1
  have h' : IsRelationRat p q S' e := by
    obtain ⟨ξ, hξ, hrel⟩ := h
    refine ⟨ξ, hξ, ?_⟩
    rw [hS'def, Finset.prod_filter_of_ne (p := fun r => e r ≠ 0)
      (fun r _ hr hc => hr (by simp [hc]))]
    exact hrel
  set T := S'.filter (fun r => r ^ 4 ≠ 1) with hTdef
  have hT : T.Nonempty := by
    obtain ⟨r, hr, hr4, hre⟩ := hcon
    exact ⟨r, by simp [hTdef, hS'def, hr, hr4, hre]⟩
  obtain ⟨r, hrT, hmax⟩ := Finset.exists_max_image T orderOf hT
  have hrS' : r ∈ S' := (Finset.mem_filter.1 hrT).1
  have hr4 : r ^ 4 ≠ 1 := (Finset.mem_filter.1 hrT).2
  have her : e r ≠ 0 := (Finset.mem_filter.1 hrS').2
  have hr := hS' r hrS'
  obtain ⟨P, hP, ℓ, hℓ, hℓ2, hℓpq, hℓr, hℓP, htr⟩ := hG r hr hr4
  -- `u ∉ P`: else `pq = u² ∈ P`, and `ℓ ∈ P` is prime to `pq`
  have ht : ¬ InP P (BaseB.tB (p * q)) := by
    intro ht
    have h2 := ht.mul_right (BaseB.isIntegral_tB (p * q))
    rw [← pow_two, BaseB.tB_sq] at h2
    have hcop : Nat.Coprime (p * q) ℓ := ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓpq).symm
    exact not_inP_coprime hcop h2 hℓP
  refine her (coeff_eq_zero_of_private_idealR hq hqp hS' h' hrS' ht htr ?_)
  intro r' hr' hne htr'
  have hr'f := hS' r' hr'
  have hr0 : r ≠ 0 := ne_zero_of_finOrder hr
  set v := r' / r with hv
  have hvfin : IsOfFinOrder v := isOfFinOrder_div' hr'f hr
  have hrr'I : IsIntegral ℤ (r' - r) :=
    (isIntegral_of_finOrder hr'f).sub (isIntegral_of_finOrder hr)
  -- `q (r' - r) ∈ P`, and `ℓ ∈ P` is prime to `q`: so `r' - r ∈ P`
  have hd : InP P (r' - r) := by
    have hqd : InP P ((q : ℂ) * (r' - r)) := by
      have := htr.sub htr'
      rwa [show BaseB.tB (p * q) - (q : ℂ) * r - (BaseB.tB (p * q) - (q : ℂ) * r') =
        (q : ℂ) * (r' - r) by ring] at this
    have hcop : Nat.Coprime q ℓ :=
      ((Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hd => hℓpq (hd.mul_left p)).symm
    have hg := Nat.gcd_eq_gcd_ab q ℓ
    rw [hcop.gcd_eq_one] at hg
    have h1 : (q : ℂ) * (Nat.gcdA q ℓ : ℂ) + (ℓ : ℂ) * (Nat.gcdB q ℓ : ℂ) = 1 := by
      exact_mod_cast hg.symm
    have e1 : r' - r = (q : ℂ) * (r' - r) * (Nat.gcdA q ℓ : ℂ) +
        (ℓ : ℂ) * ((Nat.gcdB q ℓ : ℂ) * (r' - r)) := by
      linear_combination (-(r' - r)) * h1
    rw [e1]
    exact (hqd.mul_right (isIntegral_intCast _)).add
      (hℓP.mul_right ((isIntegral_intCast _).mul hrr'I))
  have hv1 : InP P (v - 1) := by
    have hrinv : IsIntegral ℤ r⁻¹ := isIntegral_of_finOrder (isOfFinOrder_inv' hr)
    have := hd.mul_right hrinv
    rwa [show (r' - r) * r⁻¹ = v - 1 by rw [hv]; field_simp] at this
  obtain ⟨a, hord⟩ := orderOf_eq_prime_pow_of_inP hℓ hℓP hvfin hv1
  have ha : 0 < a := by
    by_contra h0
    push Not at h0
    rw [Nat.le_zero.1 h0, pow_zero, orderOf_eq_one_iff, hv, div_eq_one_iff_eq hr0] at hord
    exact hne hord
  have hcop : Nat.Coprime (orderOf r) (orderOf v) := by
    rw [hord]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓr).symm
  have hr'eq : r' = r * v := by rw [hv]; field_simp
  have hordr' : orderOf r' = orderOf r * ℓ ^ a := by
    rw [hr'eq, (Commute.all r v).orderOf_mul_eq_mul_orderOf_of_coprime hcop, hord]
  by_cases hr'4 : r' ^ 4 = 1
  · -- a root with `r'⁴ = 1` has order dividing 4, which the odd prime `ℓ` does not divide
    have h4 : orderOf r' ∣ 4 := orderOf_dvd_of_pow_eq_one hr'4
    have hℓ4 : ℓ ∣ 2 ^ 2 := by
      refine Dvd.dvd.trans ?_ h4
      rw [hordr']
      exact Dvd.dvd.mul_left (dvd_pow_self ℓ ha.ne') _
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow hℓ4))
  · have hle := hmax r' (Finset.mem_filter.2 ⟨hr', hr'4⟩)
    rw [hordr'] at hle
    have : orderOf r * 1 < orderOf r * ℓ ^ a :=
      Nat.mul_lt_mul_of_pos_left (Nat.one_lt_pow ha.ne' hℓ.one_lt) hr.orderOf_pos
    omega

end RatBase

end PiFormula
