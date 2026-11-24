module

public import Pilean.Base3.PiSqrt3

/-!
# Base 3: the support of a multiplicative relation

A multiplicative relation is a product `∏ (1 - r/t)^(e_r)`, `t = √-3`, over roots of unity
`r`, that is a root of unity. This file proves, from the existence of good primes
(`GoodPrimes3`), that such a relation only involves the six exceptional roots

  `R03 = {1, -1, i, -i, ω, -ω²}`                           (`support_subset_R03`).

It is the base-3 version of `Support.lean`. The exceptional roots are those for which `t - r`
has no prime factor other than 2 and 3: `t - 1 = 2ω`, `t + 1 = -2ω²`, `(t - i)(t + i) = -2`,
`t - ω = -ω²`, `t + ω² = ω`.

A good prime for `r` (`HasGoodPrime3`) is a prime ideal of the algebraic integers that
contains `t - r` and a rational prime `p ≥ 5` not dividing the order of `r`.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace Base3

/-! ## 1. Integrality -/

theorem isIntegral_sqrt3 : IsIntegral ℤ (((Real.sqrt 3 : ℝ) : ℂ)) := by
  refine ⟨X ^ 2 - C 3, monic_X_pow_sub_C 3 (by norm_num), ?_⟩
  simp [sqrt3_sq]

theorem isIntegral_t3 : IsIntegral ℤ t3 :=
  (isIntegral_of_finOrder isOfFinOrder_I).mul isIntegral_sqrt3

theorem isIntegral_t3_sub {r : ℂ} (hr : IsOfFinOrder r) : IsIntegral ℤ (t3 - r) :=
  isIntegral_t3.sub (isIntegral_of_finOrder hr)

/-! ## 2. Relations and the private prime -/

/-- A multiplicative relation: `∏_{r ∈ S} (1 - r/t)^(e_r)` is a root of unity. -/
def IsRelation3 (S : Finset ℂ) (e : ℂ → ℤ) : Prop :=
  ∃ ξ : ℂ, IsOfFinOrder ξ ∧ ∏ r ∈ S, (1 - r / t3) ^ (e r) = ξ

/-- The cleared form `∏ (t - r)^(e⁺) · t^(N⁻) = ξ ∏ (t - r)^(e⁻) · t^(N⁺)`. -/
theorem cleared_of_relation3 {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ}
    (h : IsRelation3 S e) : ∃ ξ : ℂ, IsOfFinOrder ξ ∧
      (∏ r ∈ S, (t3 - r) ^ (e r).toNat) * t3 ^ (∑ r ∈ S, (-e r).toNat) =
        ξ * (∏ r ∈ S, (t3 - r) ^ (-e r).toNat) * t3 ^ (∑ r ∈ S, (e r).toNat) := by
  obtain ⟨ξ, hξ, hrel⟩ := h
  have h3 : IsRel3 1 1 S e 0 := ⟨ξ, hξ, by rw [hrel]; simp⟩
  obtain ⟨ξ', hξ', hc⟩ := cleared3 one_ne_zero one_ne_zero hS h3
  exact ⟨ξ', hξ', by simpa using hc⟩

/-- **The private prime.** If `t - r₀ ∈ P`, `t ∉ P` and `t - r ∉ P` for the other `r ∈ S`, then
`e_{r₀} = 0`. -/
theorem coeff_eq_zero_of_private_ideal3 {P : Ideal Aint} [P.IsPrime] {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} (h : IsRelation3 S e) {r₀ : ℂ} (hr₀ : r₀ ∈ S)
    (ht : ¬ InP P t3) (h0 : InP P (t3 - r₀)) (hpriv : ∀ r ∈ S, r ≠ r₀ → ¬ InP P (t3 - r)) :
    e r₀ = 0 := by
  classical
  obtain ⟨ξ, hξ, hc⟩ := cleared_of_relation3 hS h
  have hint : ∀ r ∈ S, ∀ n : ℕ, IsIntegral ℤ ((t3 - r) ^ n) :=
    fun r hr n => (isIntegral_t3_sub (hS r hr)).pow n
  have hprodI : ∀ f : ℂ → ℕ, IsIntegral ℤ (∏ r ∈ S, (t3 - r) ^ f r) :=
    fun f => IsIntegral.prod _ fun r hr => hint r hr _
  have side : ∀ f g : ℂ → ℕ, 0 < f r₀ → g r₀ = 0 → ∀ a b : ℕ, ∀ c : ℂ, IsOfFinOrder c →
      (∏ r ∈ S, (t3 - r) ^ f r) * t3 ^ a = c * (∏ r ∈ S, (t3 - r) ^ g r) * t3 ^ b → False := by
    intro f g hf hg a b c hc heq
    have hL : InP P ((∏ r ∈ S, (t3 - r) ^ f r) * t3 ^ a) :=
      (inP_prod_of_mem _ (fun r hr => hint r hr _) hr₀ (h0.pow hf)).mul_right
        (isIntegral_t3.pow a)
    rw [heq] at hL
    rcases inP_mul ((isIntegral_of_finOrder hc).mul (hprodI g)) (isIntegral_t3.pow b) hL with
      hL | hL
    · rcases inP_mul (isIntegral_of_finOrder hc) (hprodI g) hL with hL | hL
      · exact not_inP_root hc hL
      · obtain ⟨r, hr, hL⟩ := inP_prod S _ (fun r hr => hint r hr _) hL
        obtain ⟨hpos, hL⟩ := inP_of_pow (isIntegral_t3_sub (hS r hr)) hL
        by_cases hrr : r = r₀
        · rw [hrr, hg] at hpos; exact lt_irrefl 0 hpos
        · exact hpriv r hr hrr hL
    · exact ht (inP_of_pow isIntegral_t3 hL).2
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

/-! ## 3. The exceptional roots -/

/-- The six exceptional roots of unity. -/
def R03 : Set ℂ := {r | r = 1 ∨ r = -1 ∨ r = I ∨ r = -I ∨ r = w3 ∨ r = -w3 ^ 2}

theorem pow_twelve_of_mem_R03 {r : ℂ} (hr : r ∈ R03) : r ^ 12 = 1 := by
  have hI : (I : ℂ) ^ 12 = 1 := by
    rw [show (12 : ℕ) = 4 * 3 by norm_num, pow_mul, Complex.I_pow_four, one_pow]
  have hw : w3 ^ 12 = 1 := by
    rw [show (12 : ℕ) = 3 * 4 by norm_num, pow_mul, w3_pow_three, one_pow]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_pow 12
  · norm_num
  · exact hI
  · rw [neg_pow, hI]
    norm_num
  · exact hw
  · rw [neg_pow, ← pow_mul, show 2 * 12 = 12 * 2 by norm_num, pow_mul, hw]
    norm_num

/-! ## 4. The support theorem -/

/-- `r` has a good prime: a prime ideal containing `t - r` and a prime `p ≥ 5` with
`p ∤ ord r`. -/
def HasGoodPrime3 (r : ℂ) : Prop :=
  ∃ P : Ideal Aint, P.IsPrime ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ orderOf r ∧
    InP P (p : ℂ) ∧ InP P (t3 - r)

/-- Every root of unity outside `R03` has a good prime. -/
def GoodPrimes3 : Prop := ∀ r : ℂ, IsOfFinOrder r → r ∉ R03 → HasGoodPrime3 r

/-- **The support theorem in base 3 (from `GoodPrimes3`).** Every multiplicative relation is
supported on the six exceptional roots. -/
theorem support_subset_R03 (hG : GoodPrimes3) {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {e : ℂ → ℤ} (h : IsRelation3 S e) : ∀ r ∈ S, r ∉ R03 → e r = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set S' := S.filter (fun r => e r ≠ 0) with hS'def
  have hS' : ∀ r ∈ S', IsOfFinOrder r := fun r hr => hS r (Finset.mem_filter.1 hr).1
  have h' : IsRelation3 S' e := by
    obtain ⟨ξ, hξ, hrel⟩ := h
    refine ⟨ξ, hξ, ?_⟩
    rw [hS'def, Finset.prod_filter_of_ne (p := fun r => e r ≠ 0)
      (fun r _ hr hc => hr (by simp [hc]))]
    exact hrel
  set T := S'.filter (fun r => r ∉ R03) with hTdef
  have hT : T.Nonempty := by
    obtain ⟨r, hr, hr0, hre⟩ := hcon
    exact ⟨r, by simp [hTdef, hS'def, hr, hr0, hre]⟩
  obtain ⟨r, hrT, hmax⟩ := Finset.exists_max_image T orderOf hT
  have hrS' : r ∈ S' := (Finset.mem_filter.1 hrT).1
  have hrR0 : r ∉ R03 := (Finset.mem_filter.1 hrT).2
  have her : e r ≠ 0 := (Finset.mem_filter.1 hrS').2
  have hr := hS' r hrS'
  obtain ⟨P, hP, p, hp, hp5, hpr, hpP, htr⟩ := hG r hr hrR0
  -- `t ∉ P`: else `3 = -t² ∈ P`, and `p ∈ P` is prime to 3
  have ht : ¬ InP P t3 := by
    intro ht
    have h2 := (ht.mul_right isIntegral_t3).neg
    rw [← pow_two, t3_sq, neg_neg] at h2
    have hcop : Nat.Coprime 3 p :=
      (Nat.coprime_primes Nat.prime_three hp).2 (by omega)
    exact not_inP_coprime (a := 3) (b := p) hcop (by exact_mod_cast h2) hpP
  refine her (coeff_eq_zero_of_private_ideal3 hS' h' hrS' ht htr ?_)
  intro r' hr' hne htr'
  have hr'f := hS' r' hr'
  have hr0 : r ≠ 0 := ne_zero_of_finOrder hr
  set u := r' / r with hu
  have hufin : IsOfFinOrder u := isOfFinOrder_div' hr'f hr
  have hu1 : InP P (u - 1) := by
    have hd : InP P (r' - r) := by
      have := htr.sub htr'
      rwa [show t3 - r - (t3 - r') = r' - r by ring] at this
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
  by_cases hr'R0 : r' ∈ R03
  · -- an exceptional root has order dividing 12, which `p ≥ 5` does not divide
    have h12 : orderOf r' ∣ 12 := orderOf_dvd_of_pow_eq_one (pow_twelve_of_mem_R03 hr'R0)
    have hp12 : p ∣ 12 := by
      refine Dvd.dvd.trans ?_ h12
      rw [hordr']
      exact Dvd.dvd.mul_left (dvd_pow_self p ha.ne') _
    have hle := Nat.le_of_dvd (by norm_num) hp12
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  · have hle := hmax r' (Finset.mem_filter.2 ⟨hr', hr'R0⟩)
    rw [hordr'] at hle
    have : orderOf r * 1 < orderOf r * p ^ a :=
      Nat.mul_lt_mul_of_pos_left (Nat.one_lt_pow ha.ne' hp.one_lt) hr.orderOf_pos
    omega

end Base3

end PiFormula
