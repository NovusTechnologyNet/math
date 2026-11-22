import Pilean.PiFormula.LogYes

/-!
# `arctan (2/7)` has no binary BBP-type formula

Bailey's compendium of BBP-type formulas says that it is not known whether `arctan (2/7)`
possesses a binary BBP formula; Borwein, Borwein and Galway (2004, section 2.5) name it as
the first arctangent for which they could find none.

Here (from Baker's theorem): `arctan (2/7)` is not the value of any series of the class F,
`∑ ρ(k) 2^(-⌊k/2⌋)/k` with `ρ` rational and periodic, and no such series is a non-zero
algebraic multiple of it (`not_isFValue_arctan_two_sevenths`, `no_arctan_two_sevenths`). The
same holds for `arctan (5/8)` and `arctan (4/9)`.

The proof is the proof for `log 23` (`Log23.lean`) with a Gaussian number in place of 23.
Write `7 + 2i = a`, `7 - 2i = b`, so `a b = 53` and `exp (2i arctan (2/7)) = a / b`.

* **Multiplicative part** (`no_rel_gaussian`, no Baker). If `∏ (1 - r/t)^(e_r) = ξ (a/b)^m`
  with `ξ` a root of unity, then `m = 0`. Every root of unity outside `R0` has a good prime of
  residue characteristic other than 53 (`good_53`: in the one atom where 53 could be the
  private prime, `Φ_13(1+i)` of norm `53 · 157`, the prime 157 is used). Such a prime contains
  neither `a` nor `b`, so the private-prime argument applies and the relation is supported on
  `R0`. A prime `P` above 53 contains exactly one of `a`, `b` (both would give `14 ∈ P`), and
  no `t - r` with `r ∈ R0`, because `t^120 - r^120 = 2^60 - 1` is prime to 53. Comparing the
  two sides at `P` gives `m = 0`.
* **Baker's theorem** (`baker_no_extra`). A relation `∑ d_r Log(1 - r/t) = q' Λ` with
  `exp Λ = a/b` and algebraic `d_r`, `q'` is a combination of integer relations among the
  `Log(1 - r/t)`, `iπ` and `Λ`, and each of those is a multiplicative relation as above.

The general statement (`not_isFValue_arctan`) is for `arctan (y/x)` with `x^2 + y^2 = ℓ` a
prime to which `Log23.lean` and `LogPrimes.lean` apply. So the three primes `53 = 7^2 + 2^2`,
`89 = 8^2 + 5^2` and `97 = 9^2 + 4^2`, whose logarithms have no formula, give three
arctangents with none.
-/

open Complex Polynomial

namespace PiFormula

/-! ## 1. Relations up to a power of a quotient of two algebraic integers -/

/-- A multiplicative relation among the `1 - r/t` up to a power of `a / b`. -/
def IsRelUpToQ (a b : ℂ) (S : Finset ℂ) (e : ℂ → ℤ) (m : ℤ) : Prop :=
  ∃ ξ : ℂ, IsOfFinOrder ξ ∧ ∏ r ∈ S, (1 - r / tC) ^ (e r) = ξ * (a / b) ^ m

/-- Exchanging `a` and `b` changes the sign of the exponent. -/
theorem IsRelUpToQ.symm {a b : ℂ} {S : Finset ℂ} {e : ℂ → ℤ} {m : ℤ}
    (h : IsRelUpToQ a b S e m) : IsRelUpToQ b a S e (-m) := by
  obtain ⟨ξ, hξ, hrel⟩ := h
  refine ⟨ξ, hξ, ?_⟩
  rw [hrel, zpow_neg, ← inv_zpow, inv_div]

/-- The cleared form of a relation up to a power of `a / b`. -/
theorem cleared_upToQ {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ} (h : IsRelUpToQ a b S e m) :
    ∃ ξ : ℂ, IsOfFinOrder ξ ∧
      (∏ r ∈ S, (tC - r) ^ (e r).toNat) * tC ^ (∑ r ∈ S, (-e r).toNat) *
          (a ^ (-m).toNat * b ^ m.toNat) =
        ξ * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) * tC ^ (∑ r ∈ S, (e r).toNat) *
          (a ^ m.toNat * b ^ (-m).toNat) := by
  obtain ⟨ξ, hξ, hrel⟩ := h
  refine ⟨ξ, hξ, ?_⟩
  have h1 := cleared_general hS e
  rw [hrel] at h1
  have ea : a ^ m * a ^ (-m).toNat = a ^ m.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ha]
    congr 1
    omega
  have eb : b ^ m * b ^ (-m).toNat = b ^ m.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hb]
    congr 1
    omega
  have hbm : b ^ m ≠ 0 := zpow_ne_zero m hb
  have hz : (a / b) ^ m * (a ^ (-m).toNat * b ^ m.toNat) = a ^ m.toNat * b ^ (-m).toNat := by
    rw [div_zpow, div_mul_eq_mul_div, div_eq_iff hbm]
    linear_combination b ^ m.toNat * ea - a ^ m.toNat * eb
  rw [h1]
  linear_combination
    (ξ * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) * tC ^ (∑ r ∈ S, (e r).toNat)) * hz

/-- If a product `∏ (t - r)^(f r) · t^c · a^x b^y` lies in a prime `P`, one of its factors
does. -/
theorem inP_sideQ {P : Ideal Aint} [P.IsPrime] {a b : ℂ} (ha : IsIntegral ℤ a)
    (hb : IsIntegral ℤ b) {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) (f : ℂ → ℕ)
    (c x y : ℕ) (h : InP P ((∏ r ∈ S, (tC - r) ^ f r) * tC ^ c * (a ^ x * b ^ y))) :
    (∃ r ∈ S, 0 < f r ∧ InP P (tC - r)) ∨ InP P tC ∨ (0 < x ∧ InP P a) ∨
      (0 < y ∧ InP P b) := by
  have hint : ∀ r ∈ S, ∀ n : ℕ, IsIntegral ℤ ((tC - r) ^ n) :=
    fun r hr n => (isIntegral_tC_sub (hS r hr)).pow n
  have hprod : IsIntegral ℤ (∏ r ∈ S, (tC - r) ^ f r) :=
    IsIntegral.prod _ fun r hr => hint r hr _
  rcases inP_mul (hprod.mul (isIntegral_tC.pow c)) ((ha.pow x).mul (hb.pow y)) h with h | h
  · rcases inP_mul hprod (isIntegral_tC.pow c) h with h | h
    · obtain ⟨r, hr, h⟩ := inP_prod S _ (fun r hr => hint r hr _) h
      obtain ⟨hpos, h⟩ := inP_of_pow (isIntegral_tC_sub (hS r hr)) h
      exact Or.inl ⟨r, hr, hpos, h⟩
    · exact Or.inr (Or.inl (inP_of_pow isIntegral_tC h).2)
  · rcases inP_mul (ha.pow x) (hb.pow y) h with h | h
    · exact Or.inr (Or.inr (Or.inl (inP_of_pow ha h)))
    · exact Or.inr (Or.inr (Or.inr (inP_of_pow hb h)))

/-- **The private prime, up to a power of `a / b`**, for a prime `P` that contains neither
`a` nor `b`. -/
theorem coeff_eq_zero_upToQ {a b : ℂ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : IsIntegral ℤ a)
    (hb : IsIntegral ℤ b) {P : Ideal Aint} [P.IsPrime] {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ} (h : IsRelUpToQ a b S e m) {r₀ : ℂ}
    (hr₀ : r₀ ∈ S) (ht : ¬ InP P tC) (haP : ¬ InP P a) (hbP : ¬ InP P b)
    (h0 : InP P (tC - r₀)) (hpriv : ∀ r ∈ S, r ≠ r₀ → ¬ InP P (tC - r)) : e r₀ = 0 := by
  classical
  obtain ⟨ξ, hξ, hc⟩ := cleared_upToQ ha0 hb0 hS h
  have hint : ∀ r ∈ S, ∀ n : ℕ, IsIntegral ℤ ((tC - r) ^ n) :=
    fun r hr n => (isIntegral_tC_sub (hS r hr)).pow n
  have hprodI : ∀ f : ℂ → ℕ, IsIntegral ℤ (∏ r ∈ S, (tC - r) ^ f r) :=
    fun f => IsIntegral.prod _ fun r hr => hint r hr _
  have hξI : IsIntegral ℤ ξ := isIntegral_of_finOrder hξ
  have habI : ∀ x y : ℕ, IsIntegral ℤ (a ^ x * b ^ y) := fun x y => (ha.pow x).mul (hb.pow y)
  -- a product in `P` cannot come from the side without `t - r₀`
  have other : ∀ (g : ℂ → ℕ) (c x y : ℕ), g r₀ = 0 →
      ¬ InP P ((∏ r ∈ S, (tC - r) ^ g r) * tC ^ c * (a ^ x * b ^ y)) := by
    intro g c x y hg hin
    rcases inP_sideQ ha hb hS g c x y hin with ⟨r, hr, hpos, hin'⟩ | h1 | ⟨-, h1⟩ | ⟨-, h1⟩
    · by_cases hrr : r = r₀
      · rw [hrr, hg] at hpos
        exact lt_irrefl 0 hpos
      · exact hpriv r hr hrr hin'
    · exact ht h1
    · exact haP h1
    · exact hbP h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1 : 0 < (-e r₀).toNat := by omega
    have h2 : (e r₀).toNat = 0 := by omega
    have hA : InP P (∏ r ∈ S, (tC - r) ^ (-e r).toNat) :=
      inP_prod_of_mem (fun r => (tC - r) ^ (-e r).toNat) (fun r hr => hint r hr _) hr₀
        (h0.pow h1)
    have hR : InP P (ξ * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) * tC ^ (∑ r ∈ S, (e r).toNat) *
        (a ^ m.toNat * b ^ (-m).toNat)) :=
      ((hA.mul_left hξI).mul_right (isIntegral_tC.pow _)).mul_right (habI _ _)
    rw [← hc] at hR
    exact other (fun r => (e r).toNat) (∑ r ∈ S, (-e r).toNat) (-m).toNat m.toNat h2 hR
  · have h1 : 0 < (e r₀).toNat := by omega
    have h2 : (-e r₀).toNat = 0 := by omega
    have hA : InP P (∏ r ∈ S, (tC - r) ^ (e r).toNat) :=
      inP_prod_of_mem (fun r => (tC - r) ^ (e r).toNat) (fun r hr => hint r hr _) hr₀
        (h0.pow h1)
    have hL : InP P ((∏ r ∈ S, (tC - r) ^ (e r).toNat) * tC ^ (∑ r ∈ S, (-e r).toNat) *
        (a ^ (-m).toNat * b ^ m.toNat)) :=
      (hA.mul_right (isIntegral_tC.pow _)).mul_right (habI _ _)
    rw [hc] at hL
    have e1 : ξ * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) * tC ^ (∑ r ∈ S, (e r).toNat) *
        (a ^ m.toNat * b ^ (-m).toNat) = ξ * ((∏ r ∈ S, (tC - r) ^ (-e r).toNat) *
          tC ^ (∑ r ∈ S, (e r).toNat) * (a ^ m.toNat * b ^ (-m).toNat)) := by ring
    rw [e1] at hL
    rcases inP_mul hξI (((hprodI _).mul (isIntegral_tC.pow _)).mul (habI _ _)) hL with hL | hL
    · exact not_inP_root hξ hL
    · exact other (fun r => (-e r).toNat) (∑ r ∈ S, (e r).toNat) m.toNat (-m).toNat h2 hL

/-- **The exponent of `a / b` vanishes** if some prime `P` contains `a` but none of `b`, `t`
and the `t - r`. -/
theorem exponent_eq_zero_upToQ {a b : ℂ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : IsIntegral ℤ a)
    (hb : IsIntegral ℤ b) {P : Ideal Aint} [P.IsPrime] {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ} (h : IsRelUpToQ a b S e m)
    (haP : InP P a) (hbP : ¬ InP P b) (ht : ¬ InP P tC)
    (hnone : ∀ r ∈ S, ¬ InP P (tC - r)) : m = 0 := by
  obtain ⟨ξ, hξ, hc⟩ := cleared_upToQ ha0 hb0 hS h
  have hint : ∀ r ∈ S, ∀ n : ℕ, IsIntegral ℤ ((tC - r) ^ n) :=
    fun r hr n => (isIntegral_tC_sub (hS r hr)).pow n
  have hprodI : ∀ f : ℂ → ℕ, IsIntegral ℤ (∏ r ∈ S, (tC - r) ^ f r) :=
    fun f => IsIntegral.prod _ fun r hr => hint r hr _
  have hξI : IsIntegral ℤ ξ := isIntegral_of_finOrder hξ
  -- a product without a power of `a` is not in `P`
  have other : ∀ (g : ℂ → ℕ) (c y : ℕ),
      ¬ InP P ((∏ r ∈ S, (tC - r) ^ g r) * tC ^ c * (a ^ 0 * b ^ y)) := by
    intro g c y hin
    rcases inP_sideQ ha hb hS g c 0 y hin with ⟨r, hr, -, hin'⟩ | h1 | ⟨hx, -⟩ | ⟨-, h1⟩
    · exact hnone r hr hin'
    · exact ht h1
    · exact lt_irrefl 0 hx
    · exact hbP h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1 : 0 < (-m).toNat := by omega
    have h2 : m.toNat = 0 := by omega
    have hL : InP P ((∏ r ∈ S, (tC - r) ^ (e r).toNat) * tC ^ (∑ r ∈ S, (-e r).toNat) *
        (a ^ (-m).toNat * b ^ m.toNat)) :=
      ((haP.pow h1).mul_right (hb.pow _)).mul_left ((hprodI _).mul (isIntegral_tC.pow _))
    rw [hc, h2] at hL
    have e1 : ξ * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) * tC ^ (∑ r ∈ S, (e r).toNat) *
        (a ^ 0 * b ^ (-m).toNat) = ξ * ((∏ r ∈ S, (tC - r) ^ (-e r).toNat) *
          tC ^ (∑ r ∈ S, (e r).toNat) * (a ^ 0 * b ^ (-m).toNat)) := by ring
    rw [e1] at hL
    rcases inP_mul hξI (((hprodI _).mul (isIntegral_tC.pow _)).mul
      ((ha.pow _).mul (hb.pow _))) hL with hL | hL
    · exact not_inP_root hξ hL
    · exact other (fun r => (-e r).toNat) (∑ r ∈ S, (e r).toNat) (-m).toNat hL
  · have h1 : 0 < m.toNat := by omega
    have h2 : (-m).toNat = 0 := by omega
    have hR : InP P (ξ * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) * tC ^ (∑ r ∈ S, (e r).toNat) *
        (a ^ m.toNat * b ^ (-m).toNat)) :=
      ((haP.pow h1).mul_right (hb.pow _)).mul_left
        ((hξI.mul (hprodI _)).mul (isIntegral_tC.pow _))
    rw [← hc, h2] at hR
    exact other (fun r => (e r).toNat) (∑ r ∈ S, (-e r).toNat) m.toNat hR

/-! ## 2. No multiplicative relation with `a / b` -/

/-- Step 2 of Theorem C for relations up to a power of `a / b`, where `a b = ℓ` is a prime:
the support lies in `R0`, as soon as every root outside `R0` has a good prime of
characteristic other than `ℓ`. -/
theorem support_upToQ {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hG : ∀ r : ℂ, IsOfFinOrder r → r ∉ R0 → ∃ p, p ≠ ℓ ∧ HasGoodPrimeAt r p)
    {a b : ℂ} (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b) (hab : a * b = (ℓ : ℂ))
    {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ}
    (h : IsRelUpToQ a b S e m) : ∀ r ∈ S, r ∉ R0 → e r = 0 := by
  classical
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have ha0 : a ≠ 0 := fun h0 => hℓ0 (by rw [← hab, h0, zero_mul])
  have hb0 : b ≠ 0 := fun h0 => hℓ0 (by rw [← hab, h0, mul_zero])
  by_contra hcon
  push Not at hcon
  set S' := S.filter (fun r => e r ≠ 0) with hS'def
  have hS' : ∀ r ∈ S', IsOfFinOrder r := fun r hr => hS r (Finset.mem_filter.1 hr).1
  have h' : IsRelUpToQ a b S' e m := by
    obtain ⟨ξ, hξ, hrel⟩ := h
    refine ⟨ξ, hξ, ?_⟩
    rw [hS'def, Finset.prod_filter_of_ne (p := fun r => e r ≠ 0)
      (fun r _ hr hc => hr (by simp [hc]))]
    exact hrel
  set T := S'.filter (fun r => r ∉ R0) with hTdef
  have hT : T.Nonempty := by
    obtain ⟨r, hr, hr0, hre⟩ := hcon
    exact ⟨r, by simp [hTdef, hS'def, hr, hr0, hre]⟩
  obtain ⟨r, hrT, hmax⟩ := Finset.exists_max_image T orderOf hT
  have hrS' : r ∈ S' := (Finset.mem_filter.1 hrT).1
  have hrR0 : r ∉ R0 := (Finset.mem_filter.1 hrT).2
  have her : e r ≠ 0 := (Finset.mem_filter.1 hrS').2
  have hr := hS' r hrS'
  obtain ⟨p, hpℓ, P, hP, hp, hp2, hpr, hpP, htr⟩ := hG r hr hrR0
  have ht : ¬ InP P tC := by
    intro ht
    have h2 := ht.mul_right (isIntegral_one.sub (isIntegral_of_finOrder isOfFinOrder_I))
    rw [tC_mul_conj] at h2
    exact not_inP_coprime (a := 2) (b := p)
      ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)) (by exact_mod_cast h2) hpP
  have hℓP : ¬ InP P (ℓ : ℂ) := fun hin =>
    not_inP_coprime (a := ℓ) (b := p) ((Nat.coprime_primes hℓ hp).2 (Ne.symm hpℓ)) hin hpP
  have haP : ¬ InP P a := fun hin => hℓP (by rw [← hab]; exact hin.mul_right hb)
  have hbP : ¬ InP P b := fun hin => hℓP (by rw [← hab]; exact hin.mul_left ha)
  refine her (coeff_eq_zero_upToQ ha0 hb0 ha hb hS' h' hrS' ht haP hbP htr ?_)
  intro r' hr' hne htr'
  have hr'f := hS' r' hr'
  have hr0 : r ≠ 0 := ne_zero_of_finOrder hr
  set u := r' / r with hu
  have hufin : IsOfFinOrder u := isOfFinOrder_div' hr'f hr
  have hu1 : InP P (u - 1) := by
    have hd : InP P (r' - r) := by
      have := htr.sub htr'
      rwa [show tC - r - (tC - r') = r' - r by ring] at this
    have hrinv : IsIntegral ℤ r⁻¹ := isIntegral_of_finOrder (isOfFinOrder_inv' hr)
    have := hd.mul_right hrinv
    rwa [show (r' - r) * r⁻¹ = u - 1 by rw [hu]; field_simp] at this
  obtain ⟨k, hord⟩ := orderOf_eq_prime_pow_of_inP hp hpP hufin hu1
  have hk : 0 < k := by
    by_contra h0
    push Not at h0
    rw [Nat.le_zero.1 h0, pow_zero, orderOf_eq_one_iff, hu, div_eq_one_iff_eq hr0] at hord
    exact hne hord
  have hcop : Nat.Coprime (orderOf r) (orderOf u) := by
    rw [hord]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpr).symm
  have hr'eq : r' = r * u := by rw [hu]; field_simp
  have hordr' : orderOf r' = orderOf r * p ^ k := by
    rw [hr'eq, (Commute.all r u).orderOf_mul_eq_mul_orderOf_of_coprime hcop, hord]
  by_cases hr'R0 : r' ∈ R0
  · exact hrR0 (R0_closed hr'R0 hp hp2 hr hpr (a := k) (by rw [← hu, hord]))
  · have hle := hmax r' (Finset.mem_filter.2 ⟨hr', hr'R0⟩)
    rw [hordr'] at hle
    have : orderOf r * 1 < orderOf r * p ^ k :=
      Nat.mul_lt_mul_of_pos_left (Nat.one_lt_pow hk.ne' hp.one_lt) hr.orderOf_pos
    omega

/-- **No multiplicative relation with `a / b`.** Let `a`, `b` be algebraic integers with
`a b = ℓ`, an odd prime to which the hypotheses of `no_rel_of_goodPrimes` apply, and
`a + b = s` an integer prime to `ℓ`. If `∏ (1 - r/t)^(e_r) = ξ (a/b)^m` with the `r` and `ξ`
roots of unity, then `m = 0`. -/
theorem no_rel_gaussian {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hcop : Nat.Coprime (2 ^ 60 - 1) ℓ)
    (hG : ∀ r : ℂ, IsOfFinOrder r → r ∉ R0 → ∃ p, p ≠ ℓ ∧ HasGoodPrimeAt r p)
    {a b : ℂ} (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b) (hab : a * b = (ℓ : ℂ))
    {s : ℕ} (hs : a + b = (s : ℂ)) (hsℓ : Nat.Coprime s ℓ)
    {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ}
    (h : IsRelUpToQ a b S e m) : m = 0 := by
  classical
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have ha0 : a ≠ 0 := fun h0 => hℓ0 (by rw [← hab, h0, zero_mul])
  have hb0 : b ≠ 0 := fun h0 => hℓ0 (by rw [← hab, h0, mul_zero])
  have hsupp := support_upToQ hℓ hG ha hb hab hS h
  set S' := S.filter (fun r => e r ≠ 0) with hS'def
  have hS' : ∀ r ∈ S', IsOfFinOrder r := fun r hr => hS r (Finset.mem_filter.1 hr).1
  have h' : IsRelUpToQ a b S' e m := by
    obtain ⟨ξ, hξ, hrel⟩ := h
    refine ⟨ξ, hξ, ?_⟩
    rw [hS'def, Finset.prod_filter_of_ne (p := fun r => e r ≠ 0)
      (fun r _ hr hc => hr (by simp [hc]))]
    exact hrel
  have hR0 : ∀ r ∈ S', r ∈ R0 := by
    intro r hr
    by_contra hnot
    exact (Finset.mem_filter.1 hr).2 (hsupp r (Finset.mem_filter.1 hr).1 hnot)
  obtain ⟨P, hP, hin⟩ := exists_prime_above hℓ
  have ht : ¬ InP P tC := by
    intro ht
    have h2 := ht.mul_right (isIntegral_one.sub (isIntegral_of_finOrder isOfFinOrder_I))
    rw [tC_mul_conj] at h2
    exact not_inP_coprime (a := 2) (b := ℓ)
      ((Nat.coprime_primes Nat.prime_two hℓ).2 (Ne.symm hℓ2)) (by exact_mod_cast h2) hin
  have hnone : ∀ r ∈ S', ¬ InP P (tC - r) := fun r hr => not_inP_R0 hcop hin (hR0 r hr)
  -- `P` contains `a b = ℓ`, hence `a` or `b`, and not both
  have hboth : ¬ (InP P a ∧ InP P b) := fun ⟨h1, h2⟩ => by
    have h3 := h1.add h2
    rw [hs] at h3
    exact not_inP_coprime hsℓ h3 hin
  rw [← hab] at hin
  rcases inP_mul ha hb hin with haP | hbP
  · exact exponent_eq_zero_upToQ ha0 hb0 ha hb hS' h' haP (fun hbP => hboth ⟨haP, hbP⟩) ht
      hnone
  · have h0 := exponent_eq_zero_upToQ hb0 ha0 hb ha hS' h'.symm hbP
      (fun haP => hboth ⟨haP, hbP⟩) ht hnone
    omega

/-! ## 3. Baker's theorem with one more logarithm -/

/-- The logarithms: `Λ` at `none`, then those of `lamOf` (`iπ` and the `Log(1 - r/t)`). -/
noncomputable def lamX (Λ : ℂ) : Option (Option ℂ) → ℂ
  | none => Λ
  | some o => lamOf o

/-- An integer relation among `Λ`, `iπ` and the `Log(1 - r/t)`, where `exp Λ = a / b`, is a
multiplicative relation among the `1 - r/t` up to a power of `a / b`. -/
theorem relUpToQ_of_intRel {a b Λ : ℂ} (hΛ : Complex.exp Λ = a / b) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {z : Option (Option ℂ) → ℤ}
    (hz : ∑ i ∈ Finset.insertNone (Finset.insertNone S), (z i : ℂ) * lamX Λ i = 0) :
    IsRelUpToQ a b S (fun r => z (some (some r))) (-z none) := by
  rw [Finset.sum_insertNone, Finset.sum_insertNone] at hz
  have hz' : (z none : ℂ) * Λ + ((z (some none) : ℂ) * (Real.pi * I) +
      ∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / tC)) = 0 := hz
  have h1 : ∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / tC) =
      -(z (some none) : ℂ) * (Real.pi * I) + ((-z none : ℤ) : ℂ) * Λ := by
    rw [Int.cast_neg]
    linear_combination hz'
  have hexp : Complex.exp (∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / tC)) =
      ∏ r ∈ S, (1 - r / tC) ^ (z (some (some r))) := by
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [Complex.exp_int_mul, Complex.exp_log (w_ne_zero (hS r hr))]
  refine ⟨Complex.exp (-(z (some none) : ℂ) * (Real.pi * I)), ?_, ?_⟩
  · refine isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, ?_⟩
    rw [← Complex.exp_nat_mul]
    have e : ((2 : ℕ) : ℂ) * (-(z (some none) : ℂ) * (Real.pi * I)) =
        ((-z (some none) : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  · rw [← hexp, h1, Complex.exp_add, Complex.exp_int_mul Λ (-z none), hΛ]

/-- **Baker's theorem with one more logarithm.** Let `exp Λ = a / b` be algebraic. If no
multiplicative relation among the `1 - r/t` involves a non-zero power of `a / b`, then no
combination of the `Log(1 - r/t)` with algebraic coefficients is a non-zero algebraic multiple
of `Λ`. -/
theorem baker_no_extra (hB : BakerTheorem) {a b Λ : ℂ} (hΛ : Complex.exp Λ = a / b)
    (halg : IsAlgebraic ℚ (a / b))
    (hmul : ∀ S : Finset ℂ, (∀ r ∈ S, IsOfFinOrder r) → ∀ (e : ℂ → ℤ) (m : ℤ),
      IsRelUpToQ a b S e m → m = 0)
    {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {d : ℂ → ℂ}
    (hd : ∀ r ∈ S, IsAlgebraic ℚ (d r)) {q : ℂ} (hq : IsAlgebraic ℚ q)
    (h : ∑ r ∈ S, d r * Complex.log (1 - r / tC) = q * Λ) : q = 0 := by
  classical
  let β : Option (Option ℂ) → ℂ := fun o =>
    match o with
    | none => -q
    | some none => 0
    | some (some r) => if r ∈ S then d r else 0
  have hβS : ∀ r ∈ S, β (some (some r)) = d r := fun r hr => by simp only [β, hr, ↓reduceIte]
  have hF : ∀ x ∈ algebraicClosure ℚ ℂ, IsAlgebraic ℚ x := fun x hx =>
    mem_algebraicClosure_iff.1 hx
  have hspan : SpanIn (algebraicClosure ℚ ℂ)
      (IntRel (Finset.insertNone (Finset.insertNone S)) (lamX Λ)) β := by
    refine baker_descent hB _ hF (lamX Λ) _ ?_ β ?_ ?_ ?_
    · intro i hi
      rcases i with _ | o
      · change IsAlgebraic ℚ (Complex.exp Λ)
        rw [hΛ]
        exact halg
      · exact isAlgebraic_exp_lamOf hS o (Finset.some_mem_insertNone.1 hi)
    · intro i hi
      rcases i with _ | _ | r
      · exact mem_algebraicClosure_iff.2 hq.neg
      · exact mem_algebraicClosure_iff.2 isAlgebraic_zero
      · have hr : r ∈ S := Finset.some_mem_insertNone.1 (Finset.some_mem_insertNone.1 hi)
        rw [hβS r hr]
        exact mem_algebraicClosure_iff.2 (hd r hr)
    · intro i hi
      rcases i with _ | _ | r
      · exact absurd (by simp) hi
      · exact absurd (by simp) hi
      · have hr : r ∉ S := fun hr =>
          hi (Finset.some_mem_insertNone.2 (Finset.some_mem_insertNone.2 hr))
        simp only [β, hr, ↓reduceIte]
    · rw [Finset.sum_insertNone, Finset.sum_insertNone]
      have e : ∑ r ∈ S, β (some (some r)) * lamX Λ (some (some r)) =
          ∑ r ∈ S, d r * Complex.log (1 - r / tC) :=
        Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
      rw [e, h]
      change -q * Λ + (0 * (Real.pi * I) + q * Λ) = 0
      ring
  have key : ∀ v ∈ IntRel (Finset.insertNone (Finset.insertNone S)) (lamX Λ), v none = 0 := by
    rintro v ⟨z, -, hzsum, hv⟩
    have h0 := hmul S hS _ _ (relUpToQ_of_intRel hΛ hS hzsum)
    have h1 : z none = 0 := by omega
    rw [hv, h1, Int.cast_zero]
  have hnone : ∀ β' : Option (Option ℂ) → ℂ,
      SpanIn (algebraicClosure ℚ ℂ)
        (IntRel (Finset.insertNone (Finset.insertNone S)) (lamX Λ)) β' → β' none = 0 := by
    intro β' hβ'
    induction hβ' with
    | zero => rfl
    | step c hc v hv w _ ih =>
      change c * v none + w none = 0
      rw [key v hv, ih, mul_zero, add_zero]
  have h0 : -q = 0 := hnone β hspan
  exact neg_eq_zero.1 h0

/-! ## 4. The arctangent as a logarithm -/

/-- `exp (2i arctan (y/x)) = (x + y i) / (x - y i)` for `x > 0`. -/
theorem exp_two_arctan {x y : ℝ} (hx : 0 < x) :
    Complex.exp (((2 * Real.arctan (y / x) : ℝ) : ℂ) * I) =
      ((x : ℂ) + y * I) / ((x : ℂ) - y * I) := by
  set z : ℂ := (x : ℂ) + y * I with hz
  have hre : z.re = x := by simp [hz]
  have him : z.im = y := by simp [hz]
  have hz0 : z ≠ 0 := fun h => hx.ne' (by rw [← hre, h]; rfl)
  have harg : Real.arctan (y / x) = Complex.arg z := by
    have h := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by rw [hre]; exact hx))
    rw [abs_lt] at h
    rw [← Real.arctan_tan h.1 h.2, Complex.tan_arg, hre, him]
  have hconj : (x : ℂ) - y * I = (starRingEnd ℂ) z := by
    apply Complex.ext <;> simp [hz]
  have hc0 : (starRingEnd ℂ) z ≠ 0 := fun h => hz0 ((map_eq_zero _).1 h)
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
  have h1 : Complex.exp ((Complex.arg z : ℂ) * I) = z / (‖z‖ : ℝ) := by
    rw [eq_div_iff hn, mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I z
  have h2 : Complex.exp (((2 * Real.arctan (y / x) : ℝ) : ℂ) * I) =
      Complex.exp ((Complex.arg z : ℂ) * I) ^ 2 := by
    rw [← Complex.exp_nat_mul, harg]
    congr 1
    push_cast
    ring
  have h3 : z * (starRingEnd ℂ) z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [h2, h1, hconj, div_pow, eq_div_iff hc0, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hn)]
  linear_combination z * h3

/-! ## 5. No formula for `arctan (y/x)` -/

/-- **No series of the class F for `arctan (y/x)`** (from Baker's theorem), where
`x^2 + y^2 = ℓ` is an odd prime, prime to `2^60 - 1`, such that every root of unity outside
`R0` has a good prime of characteristic other than `ℓ`: if `∑ ρ(k) 2^(-⌊k/2⌋)/k =
q arctan (y/x)` with `q` algebraic, then `q = 0`. -/
theorem no_arctan_of_goodPrimes (hB : BakerTheorem) {ℓ x y : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hcop : Nat.Coprime (2 ^ 60 - 1) ℓ)
    (hG : ∀ r : ℂ, IsOfFinOrder r → r ∉ R0 → ∃ p, p ≠ ℓ ∧ HasGoodPrimeAt r p)
    (hx : 0 < x) (hxy : x ^ 2 + y ^ 2 = ℓ)
    {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {q : ℝ}
    (hq : IsAlgebraic ℚ q) (h : HasSum (seriesTerm ρ) (q * Real.arctan (y / x))) : q = 0 := by
  -- the two Gaussian integers
  set a : ℂ := (x : ℂ) + (y : ℂ) * I with ha_def
  set b : ℂ := (x : ℂ) - (y : ℂ) * I with hb_def
  have hI : IsIntegral ℤ I := isIntegral_of_finOrder isOfFinOrder_I
  have ha : IsIntegral ℤ a := (isIntegral_natCast' x).add ((isIntegral_natCast' y).mul hI)
  have hb : IsIntegral ℤ b := (isIntegral_natCast' x).sub ((isIntegral_natCast' y).mul hI)
  have hab : a * b = (ℓ : ℂ) := by
    rw [← hxy]
    push_cast
    linear_combination (-(y : ℂ) ^ 2) * Complex.I_sq
  have hs : a + b = ((2 * x : ℕ) : ℂ) := by
    push_cast
    ring
  have hxlt : x < ℓ := by
    have h1 : x ≤ x ^ 2 := Nat.le_self_pow two_ne_zero x
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · exfalso
      have h2 : x ∣ ℓ := ⟨x, by rw [← hxy]; ring⟩
      rcases (Nat.dvd_prime hℓ).1 h2 with h3 | h3
      · rw [h3] at hxy
        norm_num at hxy
        exact hℓ.one_lt.ne' hxy.symm
      · rw [h3] at hxy
        have h4 : ℓ * ℓ = ℓ * 1 := by rw [mul_one]; nlinarith [hxy]
        exact hℓ.one_lt.ne' (Nat.eq_of_mul_eq_mul_left hℓ.pos h4)
    · have : 0 < y ^ 2 := by positivity
      omega
  have hsℓ : Nat.Coprime (2 * x) ℓ :=
    Nat.Coprime.mul_left ((Nat.coprime_primes Nat.prime_two hℓ).2 (Ne.symm hℓ2))
      (Nat.coprime_of_lt_prime hx.ne' hxlt hℓ).symm
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hb0 : b ≠ 0 := fun h0 => hℓ0 (by rw [← hab, h0, mul_zero])
  -- the extra logarithm
  set θ : ℝ := Real.arctan (y / x) with hθ
  set Λ : ℂ := ((2 * θ : ℝ) : ℂ) * I with hΛ_def
  have hΛ : Complex.exp Λ = a / b := by
    have h0 := exp_two_arctan (x := x) (y := y) (by exact_mod_cast hx)
    rw [hΛ_def, hθ, h0]
    push_cast
    rfl
  have halgab : IsAlgebraic ℚ (a / b) := by
    rw [div_eq_mul_inv]
    exact ((ha.tower_top (A := ℚ)).isAlgebraic).mul ((hb.tower_top (A := ℚ)).isAlgebraic).inv
  -- the series as a combination of logarithms
  have hρ8 : ∀ k, ρ (k + 8 * N) = ρ k := fun k => by
    have h8 := periodic_mul hρ 8 k
    rwa [mul_comm] at h8
  have hN8 : 0 < 8 * N := by positivity
  have h1 := series_eq_logs hN8 (Dvd.intro N rfl) hρ8
  have e : (fun k : ℕ => (ρ k : ℂ) / 2 ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTerm ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTerm]
  rw [e] at h1
  have h2 := h1.unique (Complex.hasSum_ofReal.2 h)
  have hqC : IsAlgebraic ℚ (q : ℂ) :=
    (isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective).2 hq
  have h2alg : IsAlgebraic ℚ (2 : ℂ) := by
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) 2
  have hq' : IsAlgebraic ℚ ((q : ℂ) * (-(I / 2))) := by
    rw [div_eq_mul_inv]
    exact hqC.mul (isAlgebraic_I.mul h2alg.inv).neg
  have h3 : ∑ r ∈ rootsN (8 * N), fourierD (8 * N) ρ r * Complex.log (1 - r / tC) =
      ((q : ℂ) * (-(I / 2))) * Λ := by
    rw [h2, hΛ_def]
    push_cast
    linear_combination ((q : ℂ) * θ) * Complex.I_sq
  have h4 := baker_no_extra hB hΛ halgab
    (fun S hS e m hrel => no_rel_gaussian hℓ hℓ2 hcop hG ha hb hab hs hsℓ hS hrel)
    (fun r hr => isOfFinOrder_of_mem_rootsN hN8 hr)
    (fun r hr => isAlgebraic_fourierD (8 * N) ρ (isOfFinOrder_of_mem_rootsN hN8 hr)) hq' h3
  have hI2 : -(I / 2) ≠ 0 := by
    simp [Complex.I_ne_zero]
  have h5 : (q : ℂ) = 0 := (mul_eq_zero.1 h4).resolve_right hI2
  exact_mod_cast h5

/-- **`arctan (y/x)` is not a value of the class F** (from Baker's theorem), for
`x^2 + y^2 = ℓ` as in `no_arctan_of_goodPrimes`. -/
theorem not_isFValue_arctan (hB : BakerTheorem) {ℓ x y : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hcop : Nat.Coprime (2 ^ 60 - 1) ℓ)
    (hG : ∀ r : ℂ, IsOfFinOrder r → r ∉ R0 → ∃ p, p ≠ ℓ ∧ HasGoodPrimeAt r p)
    (hx : 0 < x) (hxy : x ^ 2 + y ^ 2 = ℓ) : ¬ IsFValue (Real.arctan (y / x)) := by
  rintro ⟨N, ρ, hN, hρ, h⟩
  have h1 : HasSum (seriesTerm ρ) ((1 : ℝ) * Real.arctan (y / x)) := by rwa [one_mul]
  have h0 := no_arctan_of_goodPrimes hB hℓ hℓ2 hcop hG hx hxy hN hρ isAlgebraic_one h1
  exact one_ne_zero h0

/-! ## 6. `arctan (2/7)`, `arctan (5/8)`, `arctan (4/9)` -/

/-- **`arctan (2/7)` has no binary BBP-type formula in the class F** (from Baker's theorem):
if `∑ ρ(k) 2^(-⌊k/2⌋)/k = q arctan (2/7)` with `ρ` rational and periodic and `q` algebraic,
then `q = 0`. Here `7 + 2i` has norm 53. -/
theorem no_arctan_two_sevenths (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {q : ℝ} (hq : IsAlgebraic ℚ q)
    (h : HasSum (seriesTerm ρ) (q * Real.arctan (2 / 7))) : q = 0 := by
  refine no_arctan_of_goodPrimes hB (ℓ := 53) (x := 7) (y := 2) (by norm_num) (by norm_num)
    (by norm_num) good_53 (by norm_num) (by norm_num) hN hρ hq ?_
  simpa using h

/-- **`arctan (2/7)` is not a value of the class F** (from Baker's theorem). -/
theorem not_isFValue_arctan_two_sevenths (hB : BakerTheorem) :
    ¬ IsFValue (Real.arctan (2 / 7)) := by
  have h := not_isFValue_arctan hB (ℓ := 53) (x := 7) (y := 2) (by norm_num) (by norm_num)
    (by norm_num) good_53 (by norm_num) (by norm_num)
  simpa using h

/-- `arctan (5/8)` is not a value of the class F (from Baker's theorem); `8 + 5i` has norm
89. -/
theorem not_isFValue_arctan_five_eighths (hB : BakerTheorem) :
    ¬ IsFValue (Real.arctan (5 / 8)) := by
  have h := not_isFValue_arctan hB (ℓ := 89) (x := 8) (y := 5) (by norm_num) (by norm_num)
    (by norm_num) good_89 (by norm_num) (by norm_num)
  simpa using h

/-- `arctan (4/9)` is not a value of the class F (from Baker's theorem); `9 + 4i` has norm
97. -/
theorem not_isFValue_arctan_four_ninths (hB : BakerTheorem) :
    ¬ IsFValue (Real.arctan (4 / 9)) := by
  have h := not_isFValue_arctan hB (ℓ := 97) (x := 9) (y := 4) (by norm_num) (by norm_num)
    (by norm_num) good_97 (by norm_num) (by norm_num)
  simpa using h

/-- **No binary BBP-type formula `P(1, 2^B, 2B, A)` for `arctan (2/7)`** (from Baker's
theorem): if `∑_j 2^(-Bj) ∑_{i=1}^{2B} a_i/(2Bj + i) = q arctan (2/7)` with rational `a_i` and
algebraic `q`, then `q = 0`. -/
theorem bailey_no_arctan_two_sevenths_F2 (hB : BakerTheorem) {B : ℕ} (hB0 : 0 < B)
    (a : Fin (2 * B) → ℚ) {q : ℝ} (hq : IsAlgebraic ℚ q)
    (h : HasSum (baileyBlock B (2 * B) a) (q * Real.arctan (2 / 7))) : q = 0 := by
  have hn : 0 < 2 * B := Nat.mul_pos two_pos hB0
  have h1 := (hasSum_bailey_F2 hB0 a _).1 h
  exact no_arctan_two_sevenths hB hn (patF2_periodic hn a) hq h1

/-- **No binary BBP-type formula `P(1, 2^B, B, A)` for `arctan (2/7)`** (from Baker's
theorem). -/
theorem bailey_no_arctan_two_sevenths_F1 (hB : BakerTheorem) {B : ℕ} (hB0 : 0 < B)
    (a : Fin B → ℚ) {q : ℝ} (hq : IsAlgebraic ℚ q)
    (h : HasSum (baileyBlock B B a) (q * Real.arctan (2 / 7))) : q = 0 := by
  have h1 := (hasSum_bailey_F1 hB0 a _).1 h
  exact no_arctan_two_sevenths hB (N := 2 * B) (by positivity) (patF1_periodic hB0 a) hq h1


/-! ## 7. The partner: `arctan (2/7) + arctan (6/11)` is a value -/

theorem norm_of_mem_nthRoots {n : ℕ} (hn : 0 < n) {c : GaussianInt} (hc : c ^ 4 = 1) :
    ∀ r ∈ nthRoots n (c : ℂ), ‖r‖ = 1 := by
  have hcn : ‖(c : ℂ)‖ = 1 := by
    have h := congrArg (fun z : GaussianInt => ‖(z : ℂ)‖) hc
    simp only [map_pow, norm_pow, map_one, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h
  intro r hr
  have h := congrArg norm ((mem_nthRoots hn).1 hr)
  rw [norm_pow, hcn] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h

theorem rhoA_PnZ_periodic {n : ℕ} (hn : 0 < n) {c : GaussianInt} (hc : c ^ 4 = 1) (k : ℕ) :
    rhoA (PnZ n c) (k + 8 * n) = rhoA (PnZ n c) k := by
  simp only [rhoA, PnZ_periodic hn hc, UZ_add_eight_mul]

/-- The arctangent-type sum over the roots of `X^n = c` is a value of the class F. -/
theorem isFValue_gamma_gen {n : ℕ} (hn : 0 < n) {c : GaussianInt} (hc : c ^ 4 = 1) :
    IsFValue (gamma (nthRoots n (c : ℂ))) := by
  refine ⟨8 * n, rhoA (PnZ n c), by omega, rhoA_PnZ_periodic hn hc, ?_⟩
  have h := hasSum_gamma (norm_of_mem_nthRoots hn hc)
  convert h using 1
  funext k
  exact (tau_eq_rhoA (psum_PnZ hn c) k).symm

/-- `arctan (im z / re z) = arg z` for `re z > 0`. -/
theorem arctan_eq_arg {z : ℂ} (hz : 0 < z.re) : Real.arctan (z.im / z.re) = Complex.arg z := by
  have h := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  rw [abs_lt] at h
  rw [← Real.arctan_tan h.1 h.2, Complex.tan_arg]

/-- `exp (i g(r))` is a positive multiple of `1 - r/t`. -/
theorem exp_gfun {r : ℂ} (hr : ‖r‖ = 1) :
    ∃ c : ℝ, 0 < c ∧ Complex.exp ((gfun r : ℂ) * I) = (c : ℂ) * (1 - r / tC) := by
  have hw : 1 - r / tC ≠ 0 := by
    rw [show 1 - r / tC = (tC - r) / tC by rw [sub_div, div_self tC_ne_zero]]
    exact div_ne_zero (tC_sub_ne_zero hr) tC_ne_zero
  have hn : 0 < ‖1 - r / tC‖ := norm_pos_iff.2 hw
  refine ⟨‖1 - r / tC‖⁻¹, inv_pos.2 hn, ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I (1 - r / tC)
  have hn' : ((‖1 - r / tC‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [gfun, Complex.log_im, Complex.ofReal_inv, eq_comm, inv_mul_eq_iff_eq_mul₀ hn']
  exact h.symm

/-- `exp (i γ(O))` is a positive multiple of `∏ (1 - r/t) = z_O / t^|O|`. -/
theorem exp_gamma {S : Multiset ℂ} (hS : ∀ r ∈ S, ‖r‖ = 1) :
    ∃ c : ℝ, 0 < c ∧
      Complex.exp ((gamma S : ℂ) * I) = (c : ℂ) * (zO S / tC ^ Multiset.card S) := by
  induction S using Multiset.induction_on with
  | empty => exact ⟨1, one_pos, by simp [gamma, zO]⟩
  | cons r S ih =>
    have hr := hS r (Multiset.mem_cons_self r S)
    obtain ⟨c, hc, h1⟩ := ih fun x hx => hS x (Multiset.mem_cons_of_mem hx)
    obtain ⟨d, hd, h2⟩ := exp_gfun hr
    refine ⟨d * c, mul_pos hd hc, ?_⟩
    have e1 : gamma (r ::ₘ S) = gfun r + gamma S := by simp [gamma]
    have e2 : zO (r ::ₘ S) = (tC - r) * zO S := by simp [zO]
    have ht := tC_ne_zero
    rw [e1, e2, Multiset.card_cons, Complex.ofReal_add, add_mul, Complex.exp_add, h1, h2]
    push_cast
    field_simp
    ring

/-- Two angles whose unit vectors are positive multiples of the same number differ by a
multiple of `2π`. -/
theorem angle_eq_of_pos_mul {α β : ℝ} {v : ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hα : Complex.exp ((α : ℂ) * I) = (c : ℂ) * v)
    (hβ : Complex.exp ((β : ℂ) * I) = (d : ℂ) * v) : ∃ n : ℤ, α = β + n * (2 * Real.pi) := by
  have nα := congrArg norm hα
  have nβ := congrArg norm hβ
  rw [Complex.norm_exp_ofReal_mul_I, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le] at nα
  rw [Complex.norm_exp_ofReal_mul_I, norm_mul, Complex.norm_real, Real.norm_of_nonneg hd.le] at nβ
  have hv : ‖v‖ ≠ 0 := by
    intro h
    rw [h, mul_zero] at nα
    exact one_ne_zero nα
  have hcd : c = d := mul_right_cancel₀ hv (nα.symm.trans nβ)
  have hexp : Complex.exp ((α : ℂ) * I) = Complex.exp ((β : ℂ) * I) := by rw [hα, hβ, hcd]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
  refine ⟨n, ?_⟩
  have h1 : (α : ℂ) * I = ((β + n * (2 * Real.pi) : ℝ) : ℂ) * I := by
    rw [hn]
    push_cast
    ring
  exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h1

theorem isFValue_pi_div_four : IsFValue (Real.pi / 4) :=
  ⟨120, namedA1, by norm_num, fun k => (named_periodic k).1, hasSum_namedA1⟩

theorem tC_pow_13 : tC ^ 13 = -64 - 64 * I := by
  have h2 : tC ^ 2 = 2 * I := by
    unfold tC
    linear_combination Complex.I_sq
  have h6 : I ^ 6 = -1 := by
    calc I ^ 6 = (I ^ 2) ^ 3 := by ring
      _ = -1 := by rw [Complex.I_sq]; norm_num
  calc tC ^ 13 = (tC ^ 2) ^ 6 * tC := by ring
    _ = (2 * I) ^ 6 * (1 + I) := by rw [h2]; rfl
    _ = -64 - 64 * I := by linear_combination (64 * (1 + I)) * h6

/-- **`arctan (1/129)` is a value of the class F** (no Baker). The arctangent-type sum over
the thirteenth roots of unity is `arg ((t^13 - 1)/t^13) = arg (129 - i)`, up to a multiple of
`2π`. -/
theorem isFValue_arctan_inv_129 : IsFValue (Real.arctan (1 / 129)) := by
  have h13 : (0 : ℕ) < 13 := by norm_num
  have hF := isFValue_gamma_gen h13 (c := 1) (one_pow 4)
  obtain ⟨c, hc, hexp⟩ := exp_gamma (norm_of_mem_nthRoots h13 (c := 1) (one_pow 4))
  have e1 : ((1 : GaussianInt) : ℂ) = 1 := map_one _
  rw [zO_nthRoots h13, card_nthRoots_eq h13, e1, tC_pow_13] at hexp
  rw [e1] at hF
  set v : ℂ := 129 - I with hv
  have hre : v.re = 129 := by simp [hv]
  have him : v.im = -1 := by simp [hv]
  have hW : (-64 - 64 * I - 1) / (-64 - 64 * I) = ((1 / 128 : ℝ) : ℂ) * v := by
    have hden : (-64 - 64 * I : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    rw [div_eq_iff hden, hv]
    push_cast
    linear_combination (-(1 / 2 : ℂ)) * Complex.I_sq
  rw [hW, ← mul_assoc, ← Complex.ofReal_mul] at hexp
  -- the angle of `v`
  have hv0 : v ≠ 0 := fun h => by rw [h] at hre; norm_num at hre
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have harg : Complex.arg v = -Real.arctan (1 / 129) := by
    rw [← arctan_eq_arg (by rw [hre]; norm_num), hre, him, ← Real.arctan_neg]
    norm_num
  have hβ : Complex.exp (((-Real.arctan (1 / 129) : ℝ) : ℂ) * I) = ((‖v‖⁻¹ : ℝ) : ℂ) * v := by
    have h := Complex.norm_mul_exp_arg_mul_I v
    have hn' : ((‖v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnv.ne'
    rw [← harg, Complex.ofReal_inv, eq_comm, inv_mul_eq_iff_eq_mul₀ hn']
    exact h.symm
  obtain ⟨n, hn⟩ := angle_eq_of_pos_mul (mul_pos hc (by norm_num)) (inv_pos.2 hnv) hexp hβ
  have h := (hF.const_mul (-1)).add (isFValue_pi_div_four.const_mul (8 * n))
  convert h using 1
  rw [hn]
  push_cast
  ring

/-- **`arctan (2/7) + arctan (6/11)` is a value of the class F** (no Baker), although
`arctan (2/7)` is not (`not_isFValue_arctan_two_sevenths`). Here
`(7 + 2i)(11 + 6i) = 65 + 64i` and `(65 + 64i)(129 + i) = 8321 (1 + i)`, so the sum is
`π/4 - arctan (1/129)`. -/
theorem isFValue_arctan_two_sevenths_add :
    IsFValue (Real.arctan (2 / 7) + Real.arctan (6 / 11)) := by
  have h1 : Real.arctan (2 / 7) + Real.arctan (6 / 11) = Real.arctan (64 / 65) := by
    rw [Real.arctan_add (by norm_num)]
    norm_num
  have h2 : Real.arctan (64 / 65) + Real.arctan (1 / 129) = Real.pi / 4 := by
    rw [Real.arctan_add (by norm_num), ← Real.arctan_one]
    norm_num
  have h3 : Real.arctan (2 / 7) + Real.arctan (6 / 11) =
      Real.pi / 4 - Real.arctan (1 / 129) := by
    rw [h1]
    linarith
  rw [h3]
  exact isFValue_pi_div_four.sub isFValue_arctan_inv_129

end PiFormula
