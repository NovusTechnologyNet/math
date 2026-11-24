module

public import Pilean.PiFormula.BaileySums

/-!
# `log 23` has no binary BBP-type formula

Bailey's compendium of BBP-type formulas lists the primes `p` for which `log p` has a binary
BBP-type formula (2, 3, 5, 7, 11, 13, 17, 19, 29, ...) and says it is unknown whether all
primes have one. The first prime missing is 23; Chamberland (J. Integer Seq. 6, 2003) records
that the case of `log 23` is open. Borwein, Borwein and Galway (2004, Theorem 4) excluded the
non-Aurifeuillian Machin-type formulas.

Here (from Baker's theorem): no series of the class F, `∑ ρ(k) 2^(-⌊k/2⌋)/k` with `ρ`
rational and periodic, has a non-zero algebraic multiple of `log 23` as its value
(`no_log23`). In Bailey's notation: `P(1, 2^B, 2B, A)` and `P(1, 2^B, B, A)` are never a
non-zero algebraic multiple of `log 23` (`bailey_no_log23_F2`, `bailey_no_log23_F1`).

The proof has the shape of Steps 1 and 2 of Theorem C, with one more logarithm.

* **Multiplicative part** (`no_rel_23`, no Baker). If `∏ (1 - r/t)^(e_r) = ξ · 23^m` with `ξ`
  a root of unity, then `m = 0`. Every root `r` outside the 24 roots of `R0` has a good prime
  whose residue characteristic is not 23 (`goodPrimes_ne_23`): the primes of Lemma 3 are
  `≡ 1 (mod 4)`, the primes of Bang's theorem have `ord_p(2) ≠ 11` except for the orbit with
  atom `Φ_11(2) = 2047 = 23 · 89`, where we take 89. So the private-prime argument of
  `Support.lean` goes through and the relation is supported on `R0`. For `r ∈ R0` and a prime
  `P` above 23, `t - r ∉ P`, because `t^120 - r^120 = 2^60 - 1` is prime to 23. Comparing the
  two sides at `P` gives `m = 0`.
* **Baker's theorem** (`baker_no_log`). A relation `∑ d_r Log(1 - r/t) = q log 23` with
  algebraic `d_r`, `q` is a combination of integer relations among the `Log(1 - r/t)`, `iπ`
  and `log 23`; each of these is a multiplicative relation as above, so has no `log 23`.

Not proved here: the same for the other binary families (weights `2^(-⌊k/n⌋)`, `n > 2`),
which the note reduces to F (Part IV, not formalized).
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

/-! ## 1. Relations up to a power of an integer -/

/-- A multiplicative relation among the `1 - r/t` up to a power of the natural number `ℓ`. -/
def IsRelUpTo (ℓ : ℕ) (S : Finset ℂ) (e : ℂ → ℤ) (m : ℤ) : Prop :=
  ∃ ξ : ℂ, IsOfFinOrder ξ ∧ ∏ r ∈ S, (1 - r / tC) ^ (e r) = ξ * (ℓ : ℂ) ^ m

/-- Clearing denominators in a product of the `1 - r/t`. -/
theorem cleared_general {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) (e : ℂ → ℤ) :
    (∏ r ∈ S, (tC - r) ^ (e r).toNat) * tC ^ (∑ r ∈ S, (-e r).toNat) =
      (∏ r ∈ S, (1 - r / tC) ^ (e r)) * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) *
        tC ^ (∑ r ∈ S, (e r).toNat) := by
  obtain ⟨X, hrel⟩ : ∃ X, ∏ r ∈ S, (1 - r / tC) ^ (e r) = X := ⟨_, rfl⟩
  rw [hrel]
  have hw : ∀ r ∈ S, (1 - r / tC) = (tC - r) / tC := fun r _ => by
    rw [sub_div, div_self tC_ne_zero]
  have hw0 : ∀ r ∈ S, (tC - r) / tC ≠ 0 := fun r hr =>
    div_ne_zero (tC_sub_root_ne_zero (hS r hr)) tC_ne_zero
  have hsplit : ∀ r ∈ S, ((tC - r) / tC) ^ (e r) =
      ((tC - r) / tC) ^ (e r).toNat / ((tC - r) / tC) ^ (-e r).toNat := by
    intro r hr
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (hw0 r hr), Int.toNat_sub_toNat_neg]
  rw [Finset.prod_congr rfl (fun r hr => by rw [hw r hr, hsplit r hr]),
    Finset.prod_div_distrib] at hrel
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum] at hrel
  have hP : ∏ r ∈ S, (tC - r) ^ (-e r).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r hr => pow_ne_zero _ (tC_sub_root_ne_zero (hS r hr))
  have ht : ∀ n : ℕ, tC ^ n ≠ 0 := fun n => pow_ne_zero n tC_ne_zero
  field_simp at hrel
  rw [div_eq_iff (ht _)] at hrel
  linear_combination hrel

/-- The cleared form of a relation up to a power of `ℓ`. -/
theorem cleared_upTo {ℓ : ℕ} (hℓ : ℓ ≠ 0) {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {e : ℂ → ℤ} {m : ℤ} (h : IsRelUpTo ℓ S e m) : ∃ ξ : ℂ, IsOfFinOrder ξ ∧
      (∏ r ∈ S, (tC - r) ^ (e r).toNat) * tC ^ (∑ r ∈ S, (-e r).toNat) * (ℓ : ℂ) ^ (-m).toNat =
        ξ * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) * tC ^ (∑ r ∈ S, (e r).toNat) *
          (ℓ : ℂ) ^ m.toNat := by
  obtain ⟨ξ, hξ, hrel⟩ := h
  refine ⟨ξ, hξ, ?_⟩
  have h1 := cleared_general hS e
  rw [hrel] at h1
  have hℓ' : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
  have hz : (ℓ : ℂ) ^ m * (ℓ : ℂ) ^ (-m).toNat = (ℓ : ℂ) ^ m.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hℓ']
    congr 1
    omega
  rw [h1]
  linear_combination
    (ξ * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) * tC ^ (∑ r ∈ S, (e r).toNat)) * hz

/-- If a product `∏ (t - r)^(f r) · t^a · ℓ^x` lies in a prime `P`, one of its factors does. -/
theorem inP_side {P : Ideal Aint} [P.IsPrime] {ℓ : ℕ} {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) (f : ℂ → ℕ) (a x : ℕ)
    (h : InP P ((∏ r ∈ S, (tC - r) ^ f r) * tC ^ a * (ℓ : ℂ) ^ x)) :
    (∃ r ∈ S, 0 < f r ∧ InP P (tC - r)) ∨ InP P tC ∨ (0 < x ∧ InP P (ℓ : ℂ)) := by
  have hint : ∀ r ∈ S, ∀ n : ℕ, IsIntegral ℤ ((tC - r) ^ n) :=
    fun r hr n => (isIntegral_tC_sub (hS r hr)).pow n
  have hprod : IsIntegral ℤ (∏ r ∈ S, (tC - r) ^ f r) :=
    IsIntegral.prod _ fun r hr => hint r hr _
  rcases inP_mul (hprod.mul (isIntegral_tC.pow a)) ((isIntegral_natCast' ℓ).pow x) h with h | h
  · rcases inP_mul hprod (isIntegral_tC.pow a) h with h | h
    · obtain ⟨r, hr, h⟩ := inP_prod S _ (fun r hr => hint r hr _) h
      obtain ⟨hpos, h⟩ := inP_of_pow (isIntegral_tC_sub (hS r hr)) h
      exact Or.inl ⟨r, hr, hpos, h⟩
    · exact Or.inr (Or.inl (inP_of_pow isIntegral_tC h).2)
  · exact Or.inr (Or.inr (inP_of_pow (isIntegral_natCast' ℓ) h))

/-- **The private prime, up to a power of `ℓ`.** As `coeff_eq_zero_of_private_ideal`, for a
prime `P` that does not contain `ℓ`. -/
theorem coeff_eq_zero_upTo {ℓ : ℕ} (hℓ : ℓ ≠ 0) {P : Ideal Aint} [P.IsPrime] {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ} (h : IsRelUpTo ℓ S e m) {r₀ : ℂ}
    (hr₀ : r₀ ∈ S) (ht : ¬ InP P tC) (hℓP : ¬ InP P (ℓ : ℂ)) (h0 : InP P (tC - r₀))
    (hpriv : ∀ r ∈ S, r ≠ r₀ → ¬ InP P (tC - r)) : e r₀ = 0 := by
  classical
  obtain ⟨ξ, hξ, hc⟩ := cleared_upTo hℓ hS h
  have hint : ∀ r ∈ S, ∀ n : ℕ, IsIntegral ℤ ((tC - r) ^ n) :=
    fun r hr n => (isIntegral_tC_sub (hS r hr)).pow n
  have hprodI : ∀ f : ℂ → ℕ, IsIntegral ℤ (∏ r ∈ S, (tC - r) ^ f r) :=
    fun f => IsIntegral.prod _ fun r hr => hint r hr _
  have hξI : IsIntegral ℤ ξ := isIntegral_of_finOrder hξ
  -- a product in `P` cannot come from the side without `t - r₀`
  have other : ∀ (g : ℂ → ℕ) (b y : ℕ), g r₀ = 0 →
      ¬ InP P ((∏ r ∈ S, (tC - r) ^ g r) * tC ^ b * (ℓ : ℂ) ^ y) := by
    intro g b y hg hin
    rcases inP_side hS g b y hin with ⟨r, hr, hpos, hin'⟩ | h1 | ⟨-, h1⟩
    · by_cases hrr : r = r₀
      · rw [hrr, hg] at hpos
        exact lt_irrefl 0 hpos
      · exact hpriv r hr hrr hin'
    · exact ht h1
    · exact hℓP h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1 : 0 < (-e r₀).toNat := by omega
    have h2 : (e r₀).toNat = 0 := by omega
    have hA : InP P (∏ r ∈ S, (tC - r) ^ (-e r).toNat) :=
      inP_prod_of_mem (fun r => (tC - r) ^ (-e r).toNat) (fun r hr => hint r hr _) hr₀
        (h0.pow h1)
    have hR : InP P (ξ * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) * tC ^ (∑ r ∈ S, (e r).toNat) *
        (ℓ : ℂ) ^ m.toNat) :=
      ((hA.mul_left hξI).mul_right (isIntegral_tC.pow _)).mul_right
        ((isIntegral_natCast' ℓ).pow _)
    rw [← hc] at hR
    exact other (fun r => (e r).toNat) (∑ r ∈ S, (-e r).toNat) (-m).toNat h2 hR
  · have h1 : 0 < (e r₀).toNat := by omega
    have h2 : (-e r₀).toNat = 0 := by omega
    have hA : InP P (∏ r ∈ S, (tC - r) ^ (e r).toNat) :=
      inP_prod_of_mem (fun r => (tC - r) ^ (e r).toNat) (fun r hr => hint r hr _) hr₀
        (h0.pow h1)
    have hL : InP P ((∏ r ∈ S, (tC - r) ^ (e r).toNat) * tC ^ (∑ r ∈ S, (-e r).toNat) *
        (ℓ : ℂ) ^ (-m).toNat) :=
      (hA.mul_right (isIntegral_tC.pow _)).mul_right ((isIntegral_natCast' ℓ).pow _)
    rw [hc] at hL
    have e1 : ξ * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) * tC ^ (∑ r ∈ S, (e r).toNat) *
        (ℓ : ℂ) ^ m.toNat = ξ * ((∏ r ∈ S, (tC - r) ^ (-e r).toNat) *
          tC ^ (∑ r ∈ S, (e r).toNat) * (ℓ : ℂ) ^ m.toNat) := by ring
    rw [e1] at hL
    rcases inP_mul hξI (((hprodI _).mul (isIntegral_tC.pow _)).mul
      ((isIntegral_natCast' ℓ).pow _)) hL with hL | hL
    · exact not_inP_root hξ hL
    · exact other (fun r => (-e r).toNat) (∑ r ∈ S, (e r).toNat) m.toNat h2 hL

/-- **The exponent of `ℓ` vanishes** if some prime `P` contains `ℓ` but none of `t` and the
`t - r`. -/
theorem exponent_eq_zero_upTo {ℓ : ℕ} (hℓ : ℓ ≠ 0) {P : Ideal Aint} [P.IsPrime]
    {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ}
    (h : IsRelUpTo ℓ S e m) (hℓP : InP P (ℓ : ℂ)) (ht : ¬ InP P tC)
    (hnone : ∀ r ∈ S, ¬ InP P (tC - r)) : m = 0 := by
  obtain ⟨ξ, hξ, hc⟩ := cleared_upTo hℓ hS h
  have hint : ∀ r ∈ S, ∀ n : ℕ, IsIntegral ℤ ((tC - r) ^ n) :=
    fun r hr n => (isIntegral_tC_sub (hS r hr)).pow n
  have hprodI : ∀ f : ℂ → ℕ, IsIntegral ℤ (∏ r ∈ S, (tC - r) ^ f r) :=
    fun f => IsIntegral.prod _ fun r hr => hint r hr _
  have hξI : IsIntegral ℤ ξ := isIntegral_of_finOrder hξ
  have other : ∀ (g : ℂ → ℕ) (b : ℕ),
      ¬ InP P ((∏ r ∈ S, (tC - r) ^ g r) * tC ^ b * (ℓ : ℂ) ^ 0) := by
    intro g b hin
    rcases inP_side hS g b 0 hin with ⟨r, hr, -, hin'⟩ | h1 | ⟨hx, -⟩
    · exact hnone r hr hin'
    · exact ht h1
    · exact lt_irrefl 0 hx
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1 : 0 < (-m).toNat := by omega
    have h2 : m.toNat = 0 := by omega
    have hL : InP P ((∏ r ∈ S, (tC - r) ^ (e r).toNat) * tC ^ (∑ r ∈ S, (-e r).toNat) *
        (ℓ : ℂ) ^ (-m).toNat) :=
      (hℓP.pow h1).mul_left ((hprodI _).mul (isIntegral_tC.pow _))
    rw [hc, h2] at hL
    have e1 : ξ * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) * tC ^ (∑ r ∈ S, (e r).toNat) *
        (ℓ : ℂ) ^ 0 = ξ * ((∏ r ∈ S, (tC - r) ^ (-e r).toNat) *
          tC ^ (∑ r ∈ S, (e r).toNat) * (ℓ : ℂ) ^ 0) := by ring
    rw [e1] at hL
    rcases inP_mul hξI (((hprodI _).mul (isIntegral_tC.pow _)).mul
      ((isIntegral_natCast' ℓ).pow _)) hL with hL | hL
    · exact not_inP_root hξ hL
    · exact other (fun r => (-e r).toNat) (∑ r ∈ S, (e r).toNat) hL
  · have h1 : 0 < m.toNat := by omega
    have h2 : (-m).toNat = 0 := by omega
    have hR : InP P (ξ * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) * tC ^ (∑ r ∈ S, (e r).toNat) *
        (ℓ : ℂ) ^ m.toNat) :=
      (hℓP.pow h1).mul_left ((hξI.mul (hprodI _)).mul (isIntegral_tC.pow _))
    rw [← hc, h2] at hR
    exact other (fun r => (e r).toNat) (∑ r ∈ S, (-e r).toNat) hR

/-! ## 2. Good primes of a prescribed characteristic -/

/-- A good prime of residue characteristic `p` for the root `r`. -/
def HasGoodPrimeAt (r : ℂ) (p : ℕ) : Prop :=
  ∃ P : Ideal Aint, P.IsPrime ∧ p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ orderOf r ∧ InP P (p : ℂ) ∧
    InP P (tC - r)

/-- `hasGoodPrime_of_dvd`, keeping track of the prime `p`. -/
theorem goodAt_of_dvd {m s : ℕ} (hm : 0 < m) {κ : GaussianInt} (hκ : κ ^ 4 = 1)
    {r : ℂ} (hr : r ∈ (cycPoly m (2 ^ s) (GaussianInt.toComplex κ)).roots)
    (hgal : galOrbit r = (cycPoly m (2 ^ s) (GaussianInt.toComplex κ)).roots)
    {ρ : GaussianInt} (hρ : Prime ρ)
    (hρa : ρ ∣ (cyclotomic m GaussianInt).eval (κ * tG ^ 2 ^ s))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) (hρp : ρ ∣ (p : GaussianInt)) :
    HasGoodPrimeAt r p := by
  have hN : 2 ^ s ≠ 0 := pow_ne_zero s two_ne_zero
  have hκC : (GaussianInt.toComplex κ) ^ 4 = 1 := by rw [← map_pow, hκ, map_one]
  have hκC0 : GaussianInt.toComplex κ ≠ 0 := by intro h; rw [h] at hκC; norm_num at hκC
  have hdeg := natDegree_minpoly_of_galOrbit hκC0 hgal
  have hpow := pow_eq_one_of_mem_roots hm hκC hN hr
  have hfin : IsOfFinOrder r :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨4 * m * 2 ^ s, by positivity, hpow⟩
  obtain ⟨Q, hQ, htr, hmul⟩ := exists_prime_of_kernel (isIntegral_of_finOrder hfin) hρ
    (fun g hg => dvd_eval_of_eval₂_eq_zero hm hN hκ hr hdeg hρa hg)
  refine ⟨Q, hQ, hp, hp2, ?_, ?_, htr⟩
  · intro h
    exact not_dvd_four_mul hp hp2 hpm (h.trans (orderOf_dvd_of_pow_eq_one hpow))
  · have h := hmul _ hρp
    rw [map_natCast] at h
    exact h

theorem goodAt_orbit_of_prime (a : Atom) {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1)
    (hp2 : p ≠ 2) (hpm : ¬ p ∣ mOf a) (hdvd : (p : ℤ) ∣ (atom a).norm) {r : ℂ}
    (hr : r ∈ orbit a) : HasGoodPrimeAt r p := by
  obtain ⟨ρ, hρ, hρp, hρa⟩ := exists_prime_dvd_of_dvd_norm hp h4 hdvd
  obtain ⟨s, hs⟩ := Npow_eq_two_pow a
  have hr1 : r ∈ (cycPoly (mOf a) (2 ^ s) (GaussianInt.toComplex (kappaZ a))).roots := by
    rw [kappaZ_toComplex, ← hs]; exact hr
  have hgal : galOrbit r =
      (cycPoly (mOf a) (2 ^ s) (GaussianInt.toComplex (kappaZ a))).roots := by
    rw [kappaZ_toComplex, ← hs]; exact galOrbit_orbit a hr
  refine goodAt_of_dvd (mOf_odd a).pos (kappaZ_pow_four a) hr1 hgal hρ ?_ hp hp2 hpm
    ⟨star ρ, hρp.symm⟩
  rw [← hs, kappaZ_mul_tG_pow]
  exact hρa

theorem goodAt_partner_of_prime (a : Atom) {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1)
    (hp2 : p ≠ 2) (hpm : ¬ p ∣ mOf a) (hdvd : (p : ℤ) ∣ (atom a).norm) {r : ℂ}
    (hr : r ∈ partner (orbit a)) : HasGoodPrimeAt r p := by
  rw [← Zsqrtd.norm_conj] at hdvd
  obtain ⟨ρ, hρ, hρp, hρa⟩ := exists_prime_dvd_of_dvd_norm hp h4 hdvd
  obtain ⟨s, hs⟩ := Npow_eq_two_pow a
  have hr1 : r ∈ (cycPoly (mOf a) (2 ^ s) (GaussianInt.toComplex (kappaZp a))).roots := by
    rw [kappaZp_toComplex, ← hs, ← partner_orbit_eq]; exact hr
  have hgal : galOrbit r =
      (cycPoly (mOf a) (2 ^ s) (GaussianInt.toComplex (kappaZp a))).roots := by
    rw [kappaZp_toComplex, ← hs, ← partner_orbit_eq]; exact galOrbit_partner a hr
  refine goodAt_of_dvd (mOf_odd a).pos (kappaZp_pow_four a) hr1 hgal hρ ?_ hp hp2 hpm
    ⟨star ρ, hρp.symm⟩
  rw [← hs, kappaZp_mul_tG_pow, ← star_eval_cyclotomic]
  exact hρa

theorem goodAt_selfOrb_of_dvd (k : ℕ) (b : Bool) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqm : ¬ q ∣ 2 * k + 1)
    (hdvd : (q : ℤ) ∣ (cyclotomic (2 * k + 1) ℤ).eval (if b then -2 else 2)) {r : ℂ}
    (hr : r ∈ selfOrb k b) : HasGoodPrimeAt r q := by
  obtain ⟨ρ, hρ, hρq⟩ := exists_gaussian_prime_dvd hq
  have hr1 : r ∈ (cycPoly (2 * k + 1) (2 ^ 1) (GaussianInt.toComplex (kappaSZ b))).roots := by
    rw [kappaSZ_toComplex, pow_one]; exact hr
  have hgal : galOrbit r =
      (cycPoly (2 * k + 1) (2 ^ 1) (GaussianInt.toComplex (kappaSZ b))).roots := by
    rw [kappaSZ_toComplex, pow_one]; exact galOrbit_selfOrb k b hr
  refine goodAt_of_dvd (by omega) (kappaSZ_pow_four b) hr1 hgal hρ ?_ hq hq2 hqm hρq
  rw [pow_one, kappaSZ_mul_tG_sq, ← map_cyclotomic_int (2 * k + 1) GaussianInt, eval_intCast_map]
  have h1 := map_dvd (Int.castRingHom GaussianInt) hdvd
  rw [map_natCast] at h1
  exact hρq.trans h1

theorem orderOf_two_23 : orderOf (2 : ZMod 23) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_two_89 : orderOf (2 : ZMod 89) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- **Every root of unity outside `R0` has a good prime of residue characteristic other
than 23.** -/
theorem goodPrimes_ne_23 (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) :
    ∃ p, p ≠ 23 ∧ HasGoodPrimeAt r p := by
  obtain ⟨n, hn, hrn⟩ := isOfFinOrder_iff_pow_eq_one.1 hr
  rcases exists_explicit_orbit hn hrn with ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨k, b, hkb⟩
  · by_cases hex : a ∈ exceptional
    · exact absurd (orbit_exceptional_R0 hex ha) hR0
    · obtain ⟨p, hp, h4, hp2, hpm, hdvd⟩ := exists_prime_of_atom a hex
      exact ⟨p, by omega, goodAt_orbit_of_prime a hp h4 hp2 hpm hdvd ha⟩
  · by_cases hex : a ∈ exceptional
    · exact absurd (partner_exceptional_R0 hex ha) hR0
    · obtain ⟨p, hp, h4, hp2, hpm, hdvd⟩ := exists_prime_of_atom a hex
      exact ⟨p, by omega, goodAt_partner_of_prime a hp h4 hp2 hpm hdvd ha⟩
  · cases b
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact absurd (selfOrb_zero_false_R0 hkb) hR0
      · by_cases hk5 : k = 5
        · -- the atom is `Φ_11(2) = 23 · 89`: take 89
          subst hk5
          have : Fact (Nat.Prime 89) := ⟨by norm_num⟩
          have hdvd := dvd_cyclotomic_of_orderOf (q := 89) (n := 11) (by norm_num)
            orderOf_two_89
          exact ⟨89, by norm_num, goodAt_selfOrb_of_dvd 5 false (q := 89) (by norm_num)
            (by norm_num) (by norm_num) (by simpa using hdvd) hkb⟩
        · obtain ⟨q, hq, hord⟩ := bang (2 * k + 1) (by omega) (by omega)
          have : Fact q.Prime := ⟨hq⟩
          have hlt := lt_of_orderOf_two (by omega) hord
          have hdvd := dvd_cyclotomic_of_orderOf (by omega) hord
          refine ⟨q, ?_, goodAt_selfOrb_of_dvd k false hq (by omega)
            (Nat.not_dvd_of_pos_of_lt (by omega) hlt) (by simpa using hdvd) hkb⟩
          rintro rfl
          rw [orderOf_two_23] at hord
          omega
    · rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk
      · exact absurd (selfOrb_zero_true_R0 hkb) hR0
      · exact absurd (selfOrb_one_true_R0 hkb) hR0
      · obtain ⟨q, hq, hord⟩ := bang (2 * (2 * k + 1)) (by omega) (by omega)
        have : Fact q.Prime := ⟨hq⟩
        have hlt := lt_of_orderOf_two (by omega) hord
        have hdvd := dvd_cyclotomic_of_orderOf (by omega) hord
        rw [cyclotomic_two_mul_of_odd ⟨k, rfl⟩ (by omega) ℤ, eval_comp, eval_neg, eval_X] at hdvd
        refine ⟨q, ?_, goodAt_selfOrb_of_dvd k true hq (by omega)
          (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) (by simpa using hdvd) hkb⟩
        rintro rfl
        rw [orderOf_two_23] at hord
        omega

/-! ## 3. No multiplicative relation with 23 -/

/-- Step 2 of Theorem C for relations up to a power of a prime `ℓ`: the support lies in
`R0`, as soon as every root outside `R0` has a good prime of characteristic other than `ℓ`. -/
theorem support_upTo {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hG : ∀ r : ℂ, IsOfFinOrder r → r ∉ R0 → ∃ p, p ≠ ℓ ∧ HasGoodPrimeAt r p)
    {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ}
    (h : IsRelUpTo ℓ S e m) : ∀ r ∈ S, r ∉ R0 → e r = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set S' := S.filter (fun r => e r ≠ 0) with hS'def
  have hS' : ∀ r ∈ S', IsOfFinOrder r := fun r hr => hS r (Finset.mem_filter.1 hr).1
  have h' : IsRelUpTo ℓ S' e m := by
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
  refine her (coeff_eq_zero_upTo hℓ.ne_zero hS' h' hrS' ht hℓP htr ?_)
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
  by_cases hr'R0 : r' ∈ R0
  · exact hrR0 (R0_closed hr'R0 hp hp2 hr hpr (a := a) (by rw [← hu, hord]))
  · have hle := hmax r' (Finset.mem_filter.2 ⟨hr', hr'R0⟩)
    rw [hordr'] at hle
    have : orderOf r * 1 < orderOf r * p ^ a :=
      Nat.mul_lt_mul_of_pos_left (Nat.one_lt_pow ha.ne' hp.one_lt) hr.orderOf_pos
    omega

/-- A prime ideal of the algebraic integers above the rational prime `ℓ`. -/
theorem exists_prime_above {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ P : Ideal Aint, P.IsPrime ∧ InP P (ℓ : ℂ) := by
  have hprime : (Ideal.span {(ℓ : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).2 (Nat.prime_iff_prime_int.1 hℓ)
  have : Algebra.IsIntegral ℤ Aint := ⟨fun x => integralClosure.isIntegral x⟩
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (Ideal.span {(ℓ : ℤ)}) (⊥ : Ideal Aint) (by
      intro g hg
      rw [Ideal.mem_under, Ideal.mem_bot] at hg
      have h0 : ((algebraMap ℤ Aint g : Aint) : ℂ) = 0 := by rw [hg]; rfl
      have h1 : (g : ℂ) = 0 := by simpa using h0
      have h2 : g = 0 := by exact_mod_cast h1
      rw [h2]
      exact Ideal.zero_mem _)
  refine ⟨Q, hQ, isIntegral_natCast' ℓ, ?_⟩
  have h1 : (ℓ : ℤ) ∈ Q.under ℤ := by
    rw [hQP]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_under] at h1
  have e : (⟨(ℓ : ℂ), isIntegral_natCast' ℓ⟩ : Aint) = algebraMap ℤ Aint (ℓ : ℤ) :=
    Subtype.ext (by simp)
  rw [e]
  exact h1

theorem tC_pow_120 : tC ^ 120 = (2 : ℂ) ^ 60 := by
  have h2 : tC ^ 2 = 2 * I := by
    unfold tC
    linear_combination Complex.I_sq
  calc tC ^ 120 = (tC ^ 2) ^ 60 := by ring
    _ = (2 * I) ^ 60 := by rw [h2]
    _ = 2 ^ 60 * (I ^ 4) ^ 15 := by ring
    _ = 2 ^ 60 := by rw [Complex.I_pow_four]; ring

/-- For a prime `P` above an integer prime to `2^60 - 1`, no `t - r` with `r ∈ R0` is in `P`. -/
theorem not_inP_R0 {ℓ : ℕ} (hcop : Nat.Coprime (2 ^ 60 - 1) ℓ) {P : Ideal Aint} [P.IsPrime]
    (hℓP : InP P (ℓ : ℂ)) {r : ℂ} (hr : r ∈ R0) : ¬ InP P (tC - r) := by
  intro hin
  obtain ⟨j, -, rfl⟩ := hr
  have hfin : IsOfFinOrder (ζ120 ^ j) := isOfFinOrder_ζ120_pow j
  have h120 : (ζ120 ^ j) ^ 120 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ζ120_prim.pow_eq_one, one_pow]
  have hw : IsIntegral ℤ (∑ i ∈ Finset.range 120, tC ^ i * (ζ120 ^ j) ^ (120 - 1 - i)) :=
    IsIntegral.sum _ fun i _ => (isIntegral_tC.pow i).mul ((isIntegral_of_finOrder hfin).pow _)
  have h1 := hin.mul_left hw
  rw [geom_sum₂_mul, h120, tC_pow_120] at h1
  have e : ((2 : ℂ) ^ 60 - 1) = ((2 ^ 60 - 1 : ℕ) : ℂ) := by norm_num
  rw [e] at h1
  exact not_inP_coprime hcop h1 hℓP

/-- **No multiplicative relation with 23.** If `∏ (1 - r/t)^(e_r) = ξ · 23^m` with the `r`
and `ξ` roots of unity, then `m = 0`. -/
theorem no_rel_23 {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ}
    (h : IsRelUpTo 23 S e m) : m = 0 := by
  classical
  have h23 : Nat.Prime 23 := by norm_num
  have hsupp := support_upTo h23 goodPrimes_ne_23 hS h
  -- restrict to the support, which lies in `R0`
  set S' := S.filter (fun r => e r ≠ 0) with hS'def
  have hS' : ∀ r ∈ S', IsOfFinOrder r := fun r hr => hS r (Finset.mem_filter.1 hr).1
  have h' : IsRelUpTo 23 S' e m := by
    obtain ⟨ξ, hξ, hrel⟩ := h
    refine ⟨ξ, hξ, ?_⟩
    rw [hS'def, Finset.prod_filter_of_ne (p := fun r => e r ≠ 0)
      (fun r _ hr hc => hr (by simp [hc]))]
    exact hrel
  have hR0 : ∀ r ∈ S', r ∈ R0 := by
    intro r hr
    by_contra hnot
    exact (Finset.mem_filter.1 hr).2 (hsupp r (Finset.mem_filter.1 hr).1 hnot)
  obtain ⟨P, hP, hin⟩ := exists_prime_above h23
  have ht : ¬ InP P tC := by
    intro ht
    have h2 := ht.mul_right (isIntegral_one.sub (isIntegral_of_finOrder isOfFinOrder_I))
    rw [tC_mul_conj] at h2
    exact not_inP_coprime (a := 2) (b := 23) (by norm_num) (by exact_mod_cast h2) hin
  exact exponent_eq_zero_upTo (by norm_num) hS' h' hin ht
    fun r hr => not_inP_R0 (by norm_num) hin (hR0 r hr)

/-! ## 4. Baker's theorem with one more logarithm -/

/-- The logarithms: `log ℓ` at `none`, then those of `lamOf` (`iπ` and the `Log(1 - r/t)`). -/
noncomputable def lamL (ℓ : ℕ) : Option (Option ℂ) → ℂ
  | none => (Real.log ℓ : ℂ)
  | some o => lamOf o

/-- An integer relation among `log ℓ`, `iπ` and the `Log(1 - r/t)` is a multiplicative
relation among the `1 - r/t` up to a power of `ℓ`. -/
theorem relUpTo_of_intRel {ℓ : ℕ} (hℓ : 0 < ℓ) {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {z : Option (Option ℂ) → ℤ}
    (hz : ∑ i ∈ Finset.insertNone (Finset.insertNone S), (z i : ℂ) * lamL ℓ i = 0) :
    IsRelUpTo ℓ S (fun r => z (some (some r))) (-z none) := by
  rw [Finset.sum_insertNone, Finset.sum_insertNone] at hz
  have hz' : (z none : ℂ) * (Real.log ℓ : ℂ) + ((z (some none) : ℂ) * (Real.pi * I) +
      ∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / tC)) = 0 := hz
  have h1 : ∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / tC) =
      -(z (some none) : ℂ) * (Real.pi * I) + ((-z none : ℤ) : ℂ) * (Real.log ℓ : ℂ) := by
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
  · have hpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
    rw [← hexp, h1, Complex.exp_add, Complex.exp_int_mul (Real.log ℓ : ℂ) (-z none),
      ← Complex.ofReal_exp, Real.exp_log hpos, Complex.ofReal_natCast]

/-- **Baker's theorem with one more logarithm.** If no multiplicative relation among the
`1 - r/t` involves a non-zero power of `ℓ`, then no combination of the `Log(1 - r/t)` with
algebraic coefficients is a non-zero algebraic multiple of `log ℓ`. -/
theorem baker_no_log (hB : BakerTheorem) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hmul : ∀ S : Finset ℂ, (∀ r ∈ S, IsOfFinOrder r) → ∀ (e : ℂ → ℤ) (m : ℤ),
      IsRelUpTo ℓ S e m → m = 0)
    {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {d : ℂ → ℂ}
    (hd : ∀ r ∈ S, IsAlgebraic ℚ (d r)) {q : ℂ} (hq : IsAlgebraic ℚ q)
    (h : ∑ r ∈ S, d r * Complex.log (1 - r / tC) = q * (Real.log ℓ : ℂ)) : q = 0 := by
  classical
  let β : Option (Option ℂ) → ℂ := fun o =>
    match o with
    | none => -q
    | some none => 0
    | some (some r) => if r ∈ S then d r else 0
  have hβS : ∀ r ∈ S, β (some (some r)) = d r := fun r hr => by simp only [β, hr, ↓reduceIte]
  have hF : ∀ x ∈ algebraicClosure ℚ ℂ, IsAlgebraic ℚ x := fun x hx =>
    mem_algebraicClosure_iff.1 hx
  have hpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hspan : SpanIn (algebraicClosure ℚ ℂ)
      (IntRel (Finset.insertNone (Finset.insertNone S)) (lamL ℓ)) β := by
    refine baker_descent hB _ hF (lamL ℓ) _ ?_ β ?_ ?_ ?_
    · intro i hi
      rcases i with _ | o
      · change IsAlgebraic ℚ (Complex.exp (Real.log ℓ : ℂ))
        rw [← Complex.ofReal_exp, Real.exp_log hpos, Complex.ofReal_natCast]
        have h0 := isAlgebraic_ratCast ℚ (A := ℂ) (ℓ : ℚ)
        simpa using h0
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
      have e : ∑ r ∈ S, β (some (some r)) * lamL ℓ (some (some r)) =
          ∑ r ∈ S, d r * Complex.log (1 - r / tC) :=
        Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
      rw [e, h]
      change -q * (Real.log ℓ : ℂ) + (0 * (Real.pi * I) + q * (Real.log ℓ : ℂ)) = 0
      ring
  have key : ∀ v ∈ IntRel (Finset.insertNone (Finset.insertNone S)) (lamL ℓ), v none = 0 := by
    rintro v ⟨z, -, hzsum, hv⟩
    have h0 := hmul S hS _ _ (relUpTo_of_intRel hℓ hS hzsum)
    have h1 : z none = 0 := by omega
    rw [hv, h1, Int.cast_zero]
  have hnone : ∀ β' : Option (Option ℂ) → ℂ,
      SpanIn (algebraicClosure ℚ ℂ)
        (IntRel (Finset.insertNone (Finset.insertNone S)) (lamL ℓ)) β' → β' none = 0 := by
    intro β' hβ'
    induction hβ' with
    | zero => rfl
    | step c hc v hv w _ ih =>
      change c * v none + w none = 0
      rw [key v hv, ih, mul_zero, add_zero]
  have h0 : -q = 0 := hnone β hspan
  exact neg_eq_zero.1 h0

/-! ## 5. No formula for `log 23` -/

/-- **`log 23` is not a value of the class F (from Baker's theorem).** Let `ρ` be a rational
pattern of period `N` (`8 ∣ N`). If `∑ ρ(k) 2^(-⌊k/2⌋)/k = q log 23` with `q` algebraic, then
`q = 0`. -/
theorem no_log23 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {q : ℝ} (hq : IsAlgebraic ℚ q)
    (h : HasSum (seriesTerm ρ) (q * Real.log 23)) : q = 0 := by
  have h1 := series_eq_logs hN h8 hρ
  have e : (fun k : ℕ => (ρ k : ℂ) / 2 ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTerm ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTerm]
  rw [e] at h1
  have h2 := h1.unique (Complex.hasSum_ofReal.2 h)
  have hqC : IsAlgebraic ℚ (q : ℂ) :=
    (isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective).2 hq
  have h3 : ∑ r ∈ rootsN N, fourierD N ρ r * Complex.log (1 - r / tC) =
      (q : ℂ) * (Real.log ((23 : ℕ) : ℝ) : ℂ) := by
    rw [h2]
    push_cast
    ring
  have h4 := baker_no_log hB (ℓ := 23) (by norm_num) (fun S hS e m hrel => no_rel_23 hS hrel)
    (fun r hr => isOfFinOrder_of_mem_rootsN hN hr)
    (fun r hr => isAlgebraic_fourierD N ρ (isOfFinOrder_of_mem_rootsN hN hr)) hqC h3
  exact_mod_cast h4

/-- **No binary BBP-type formula `P(1, 2^B, 2B, A)` for `log 23`** (from Baker's theorem): if
`∑_j 2^(-Bj) ∑_{i=1}^{2B} a_i/(2Bj + i) = q log 23` with rational `a_i` and algebraic `q`,
then `q = 0`. -/
theorem bailey_no_log23_F2 (hB : BakerTheorem) {B : ℕ} (hB0 : 0 < B) (a : Fin (2 * B) → ℚ)
    {q : ℝ} (hq : IsAlgebraic ℚ q) (h : HasSum (baileyBlock B (2 * B) a) (q * Real.log 23)) :
    q = 0 := by
  have hn : 0 < 2 * B := Nat.mul_pos two_pos hB0
  have h1 := (hasSum_bailey_F2 hB0 a _).1 h
  exact no_log23 hB (N := 2 * B * 8) (by positivity) (Dvd.intro_left _ rfl)
    (fun k => periodic_mul (patF2_periodic hn a) 8 k) hq h1

/-- **No binary BBP-type formula `P(1, 2^B, B, A)` for `log 23`** (from Baker's theorem). -/
theorem bailey_no_log23_F1 (hB : BakerTheorem) {B : ℕ} (hB0 : 0 < B) (a : Fin B → ℚ)
    {q : ℝ} (hq : IsAlgebraic ℚ q) (h : HasSum (baileyBlock B B a) (q * Real.log 23)) :
    q = 0 := by
  have h1 := (hasSum_bailey_F1 hB0 a _).1 h
  exact no_log23 hB (N := 2 * B * 8) (by positivity) (Dvd.intro_left _ rfl)
    (fun k => periodic_mul (patF1_periodic hB0 a) 8 k) hq h1

end PiFormula
