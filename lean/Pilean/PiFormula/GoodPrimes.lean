/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula.Support
public import Pilean.PiFormula.TheoremBGalois
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Part III, Step 2: every root of unity outside `R0` has a good prime (milestone M4.2)

`Support.lean` proves that every multiplicative relation among the `1 - r/t` is supported on
`R0`, from the hypothesis `GoodPrimes`. This file proves `GoodPrimes`, so the support theorem
is unconditional (`support_subset_R0'`).

A good prime for `r` is a prime ideal `P` of the algebraic integers containing `t - r` and an
odd prime `p` not dividing the order of `r`. The construction:

* `r` is a root of `F = Φ_m(κ X^N)` with `κ ∈ {±1, ±i}`, and `F` (made monic) is the minimal
  polynomial of `r` over `ℚ(i)` (the Galois table, `minpoly_eq_of_mem_roots`). So a polynomial
  `g ∈ ℤ[i][X]` with `g(r) = 0` is a multiple of `F` in `ℤ[i][X]` (`dvd_of_eval₂_eq_zero`).
* `F(t) = Φ_m(κ t^N)` is an atom of Theorem B. If a Gaussian prime `ρ` divides it, then
  `g(r) = 0` implies `ρ ∣ g(t)`: the kernel of `ℤ[i][X] → 𝔸, X ↦ r` lies in the prime ideal
  `{g : ρ ∣ g(t)}`. Lying over for the integral extension `ℤ[i][X] → 𝔸` gives a prime `Q` of the
  algebraic integers `𝔸` whose contraction is that ideal (`exists_prime_of_kernel`). It contains
  `t - r` (the image of `t - X`) and every multiple of `ρ` in `ℤ[i]`.
* For a non-exceptional atom, `ρ` lies above a primitive prime `p` of the atom
  (`exists_primitive_atom`); for a self-paired orbit the atom is `Φ_m(∓2)` and Bang's theorem
  gives `p`. In both cases `p` is odd and `p ∤ 4 m N`.
* The orbits left over (`O_1, O_2, O_6, O_10`, their partners, and the self-paired orbits
  `{±ζ_8}`, `{±ζ_8^3}`, `O_24`) make up exactly the 24 roots of `R0`. Some of them have a good
  prime as well (`-1`, `-i`, `±ζ_8^3`), but `GoodPrimes` asks nothing of the roots of `R0`.

No Galois automorphism is needed: the root `r` is fixed from the start, and lying over is applied
to the map `X ↦ r`.
-/

@[expose] public section

open Polynomial Complex ComplexConjugate

namespace PiFormula

/-! ## 1. Gaussian integers inside the algebraic integers and inside `ℚ(i)` -/

theorem isIntegral_toComplex (z : GaussianInt) : IsIntegral ℤ (GaussianInt.toComplex z) := by
  rw [GaussianInt.toComplex_def]
  exact (isIntegral_intCast z.re).add
    ((isIntegral_intCast z.im).mul (isIntegral_of_finOrder isOfFinOrder_I))

/-- `ℤ[i] → 𝔸`. -/
noncomputable def toA : GaussianInt →+* Aint :=
  GaussianInt.toComplex.codRestrict Aint isIntegral_toComplex

theorem toA_coe (z : GaussianInt) : ((toA z : Aint) : ℂ) = GaussianInt.toComplex z := rfl

theorem toComplex_mem_Ki (z : GaussianInt) : GaussianInt.toComplex z ∈ Ki := by
  rw [GaussianInt.toComplex_def]
  exact add_mem (intCast_mem Ki z.re) (mul_mem (intCast_mem Ki z.im) I_mem_Ki)

/-- `ℤ[i] → ℚ(i)`. -/
noncomputable def toKi : GaussianInt →+* Ki :=
  GaussianInt.toComplex.codRestrict Ki toComplex_mem_Ki

theorem toKi_coe (z : GaussianInt) : ((toKi z : Ki) : ℂ) = GaussianInt.toComplex z := rfl

theorem toKi_injective : Function.Injective toKi := by
  intro x y h
  have := congrArg (fun w : Ki => (w : ℂ)) h
  exact GaussianInt.toComplex_inj.1 this

theorem algebraMap_comp_toKi : (algebraMap Ki ℂ).comp toKi = GaussianInt.toComplex :=
  RingHom.ext fun _ => rfl

/-! ## 2. Polynomials over `ℤ[i]` vanishing at `r` -/

/-- `Φ_m(κ X^N)` over `ℤ[i]`. -/
noncomputable def cycPolyZ (m N : ℕ) (κ : GaussianInt) : GaussianInt[X] :=
  (cyclotomic m GaussianInt).comp (C κ * X ^ N)

theorem eval_cycPolyZ (m N : ℕ) (κ w : GaussianInt) :
    (cycPolyZ m N κ).eval w = (cyclotomic m GaussianInt).eval (κ * w ^ N) := by
  simp [cycPolyZ, eval_comp]

/-- A polynomial over `ℤ[i]` vanishing at a root `r` of `Φ_m(κ X^N)` is a multiple of
`Φ_m(κ X^N)` in `ℤ[i][X]`, as soon as `Φ_m(κ X^N)` is the minimal polynomial. -/
theorem dvd_of_eval₂_eq_zero {m N : ℕ} (hm : 0 < m) (hN : N ≠ 0) {κ : GaussianInt}
    (hκ : κ ^ 4 = 1) {r : ℂ} (hr : r ∈ (cycPoly m N (GaussianInt.toComplex κ)).roots)
    (hdeg : m.totient * N ≤ (minpoly Ki r).natDegree)
    {g : GaussianInt[X]} (hg : g.eval₂ GaussianInt.toComplex r = 0) :
    C (κ ^ (3 * m.totient)) * cycPolyZ m N κ ∣ g := by
  have hκC : (GaussianInt.toComplex κ) ^ 4 = 1 := by rw [← map_pow, hκ, map_one]
  have hκ0 : κ ≠ 0 := by intro h; rw [h] at hκ; norm_num at hκ
  have hκC0 : GaussianInt.toComplex κ ≠ 0 := by intro h; rw [h] at hκC; norm_num at hκC
  have hint := isIntegral_of_mem_roots hm hκC hN hr
  have hmin := minpoly_eq_of_mem_roots hN (toComplex_mem_Ki κ) hκC0 hr hint hdeg
  have h4 : κ ^ (3 * m.totient) * κ ^ m.totient = 1 := by
    rw [← pow_add, show 3 * m.totient + m.totient = 4 * m.totient by ring, pow_mul, hκ, one_pow]
  -- the monic polynomial
  have hlead : (cycPolyZ m N κ).leadingCoeff = κ ^ m.totient := by
    rw [cycPolyZ, leadingCoeff_comp (by rw [natDegree_C_mul_X_pow N κ hκ0]; exact hN),
      (cyclotomic.monic m GaussianInt).leadingCoeff, leadingCoeff_C_mul_X_pow,
      natDegree_cyclotomic, one_mul]
  have hmonic : (C (κ ^ (3 * m.totient)) * cycPolyZ m N κ).Monic := by
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, hlead, h4]
  -- its image over `ℚ(i)` is the minimal polynomial
  have hmap : (C (κ ^ (3 * m.totient)) * cycPolyZ m N κ).map toKi = minpoly Ki r := by
    rw [hmin, cycPolyZ, Polynomial.map_mul, map_C, Polynomial.map_comp, map_cyclotomic,
      Polynomial.map_mul, map_C, Polynomial.map_pow, map_X]
    have hinv : toKi (κ ^ (3 * m.totient)) =
        ((⟨GaussianInt.toComplex κ, toComplex_mem_Ki κ⟩ : Ki) ^ m.totient)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have : toKi (κ ^ (3 * m.totient)) * (toKi κ) ^ m.totient = 1 := by
        rw [← map_pow, ← map_mul, h4, map_one]
      exact this
    rw [hinv]
    rfl
  have hdvd : minpoly Ki r ∣ g.map toKi := by
    apply minpoly.dvd
    rw [aeval_def, eval₂_map, algebraMap_comp_toKi]
    exact hg
  rw [← hmap] at hdvd
  exact (Polynomial.map_dvd_map toKi toKi_injective hmonic).1 hdvd

/-- **The kernel condition.** If a Gaussian integer `ρ` divides the atom `Φ_m(κ t^N)`, then
`ρ ∣ g(t)` for every `g ∈ ℤ[i][X]` vanishing at `r`. -/
theorem dvd_eval_of_eval₂_eq_zero {m N : ℕ} (hm : 0 < m) (hN : N ≠ 0) {κ : GaussianInt}
    (hκ : κ ^ 4 = 1) {r : ℂ} (hr : r ∈ (cycPoly m N (GaussianInt.toComplex κ)).roots)
    (hdeg : m.totient * N ≤ (minpoly Ki r).natDegree)
    {ρ : GaussianInt} (hρ : ρ ∣ (cyclotomic m GaussianInt).eval (κ * tG ^ N))
    {g : GaussianInt[X]} (hg : g.eval₂ GaussianInt.toComplex r = 0) : ρ ∣ g.eval tG := by
  obtain ⟨h, rfl⟩ := dvd_of_eval₂_eq_zero hm hN hκ hr hdeg hg
  rw [eval_mul, eval_mul, eval_C, eval_cycPolyZ]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hρ _) _

/-! ## 3. Lying over -/

/-- **Lying over.** If `ρ` is a Gaussian prime and `ρ ∣ g(t)` for every `g ∈ ℤ[i][X]` vanishing at
the algebraic integer `r`, then some prime ideal of the algebraic integers contains `t - r` and
every multiple of `ρ` in `ℤ[i]`. -/
theorem exists_prime_of_kernel {r : ℂ} (hr : IsIntegral ℤ r) {ρ : GaussianInt} (hρ : Prime ρ)
    (hker : ∀ g : GaussianInt[X], g.eval₂ GaussianInt.toComplex r = 0 → ρ ∣ g.eval tG) :
    ∃ Q : Ideal Aint, Q.IsPrime ∧ InP Q (tC - r) ∧
      ∀ z : GaussianInt, ρ ∣ z → InP Q (GaussianInt.toComplex z) := by
  -- the evaluation `X ↦ r`
  let φ : GaussianInt[X] →+* Aint := Polynomial.eval₂RingHom toA ⟨r, hr⟩
  have hφ : ∀ g : GaussianInt[X], ((φ g : Aint) : ℂ) = g.eval₂ GaussianInt.toComplex r := by
    intro g
    exact Polynomial.hom_eval₂ g toA (Aint.val : Aint →+* ℂ) ⟨r, hr⟩
  let _ : Algebra GaussianInt[X] Aint := φ.toAlgebra
  have halg : ∀ g : GaussianInt[X], algebraMap GaussianInt[X] Aint g = φ g := fun _ => rfl
  have : Algebra.IsIntegral GaussianInt[X] Aint := by
    refine ⟨fun x => ?_⟩
    obtain ⟨q, hq, hq0⟩ := integralClosure.isIntegral (R := ℤ) (A := ℂ) x
    refine ⟨q.map (Int.castRingHom GaussianInt[X]), hq.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap GaussianInt[X] Aint).comp (Int.castRingHom GaussianInt[X]) =
        algebraMap ℤ Aint := RingHom.ext_int _ _
    rw [this]
    exact hq0
  -- the prime `{g : ρ ∣ g(t)}` of `ℤ[i][X]`
  have : (Ideal.span {ρ}).IsPrime := (Ideal.span_singleton_prime hρ.ne_zero).2 hρ
  let P : Ideal GaussianInt[X] := Ideal.comap (Polynomial.evalRingHom tG) (Ideal.span {ρ})
  have hP : ∀ g : GaussianInt[X], g ∈ P ↔ ρ ∣ g.eval tG := by
    intro g
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, Polynomial.coe_evalRingHom]
  have : P.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal Aint) (by
    intro g hg
    rw [Ideal.mem_under, Ideal.mem_bot, halg] at hg
    rw [hP]
    apply hker
    rw [← hφ, hg]
    rfl)
  have key : ∀ g : GaussianInt[X], ρ ∣ g.eval tG →
      InP Q (g.eval₂ GaussianInt.toComplex r) := by
    intro g hg
    have hgQ : φ g ∈ Q := by
      have h1 : g ∈ Q.under GaussianInt[X] := by rw [hQP, hP]; exact hg
      rw [Ideal.mem_under, halg] at h1
      exact h1
    have hint : IsIntegral ℤ (g.eval₂ GaussianInt.toComplex r) := by
      rw [← hφ]; exact (φ g).2
    refine ⟨hint, ?_⟩
    have e : (⟨g.eval₂ GaussianInt.toComplex r, hint⟩ : Aint) = φ g := Subtype.ext (hφ g).symm
    rw [e]
    exact hgQ
  refine ⟨Q, hQ, ?_, ?_⟩
  · have h := key (C tG - X) (by simp)
    rw [eval₂_sub, eval₂_C, eval₂_X, tG_toComplex] at h
    exact h
  · intro z hz
    have h := key (C z) (by rw [eval_C]; exact hz)
    rw [eval₂_C] at h
    exact h

/-! ## 4. A good prime from a Gaussian prime dividing the atom -/

theorem not_dvd_four_mul {p m s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) :
    ¬ p ∣ 4 * m * 2 ^ s := by
  intro h
  have h1 : p ∣ 2 ^ (s + 2) * m := by
    have e : 2 ^ (s + 2) * m = 4 * m * 2 ^ s := by ring
    rw [e]; exact h
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
  · exact hpm h2

/-- A root `r` of `Φ_m(κ X^(2^s))` has a good prime as soon as a Gaussian prime `ρ` above an odd
prime `p ∤ m` divides the atom `Φ_m(κ t^(2^s))`. -/
theorem hasGoodPrime_of_dvd {m s : ℕ} (hm : 0 < m) {κ : GaussianInt} (hκ : κ ^ 4 = 1)
    {r : ℂ} (hr : r ∈ (cycPoly m (2 ^ s) (GaussianInt.toComplex κ)).roots)
    (hgal : galOrbit r = (cycPoly m (2 ^ s) (GaussianInt.toComplex κ)).roots)
    {ρ : GaussianInt} (hρ : Prime ρ)
    (hρa : ρ ∣ (cyclotomic m GaussianInt).eval (κ * tG ^ 2 ^ s))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) (hρp : ρ ∣ (p : GaussianInt)) :
    HasGoodPrime r := by
  have hN : 2 ^ s ≠ 0 := pow_ne_zero s two_ne_zero
  have hκC : (GaussianInt.toComplex κ) ^ 4 = 1 := by rw [← map_pow, hκ, map_one]
  have hκC0 : GaussianInt.toComplex κ ≠ 0 := by intro h; rw [h] at hκC; norm_num at hκC
  have hdeg := natDegree_minpoly_of_galOrbit hκC0 hgal
  have hpow := pow_eq_one_of_mem_roots hm hκC hN hr
  have hfin : IsOfFinOrder r :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨4 * m * 2 ^ s, by positivity, hpow⟩
  obtain ⟨Q, hQ, htr, hmul⟩ := exists_prime_of_kernel (isIntegral_of_finOrder hfin) hρ
    (fun g hg => dvd_eval_of_eval₂_eq_zero hm hN hκ hr hdeg hρa hg)
  refine ⟨Q, hQ, p, hp, hp2, ?_, ?_, htr⟩
  · intro h
    exact not_dvd_four_mul hp hp2 hpm (h.trans (orderOf_dvd_of_pow_eq_one hpow))
  · have h := hmul _ hρp
    rw [map_natCast] at h
    exact h

/-! ## 5. The orbits of the atoms and their partners -/

/-- `κ` as a Gaussian integer. -/
def kappaZ : Atom → GaussianInt
  | .P _ => 1
  | .Q _ => -1
  | .R _ e => gI * (-1) ^ 2 ^ e

theorem kappaZ_toComplex (a : Atom) : GaussianInt.toComplex (kappaZ a) = kappa a := by
  rcases a with k | k | ⟨k, e⟩
  · simp [kappaZ, kappa]
  · simp [kappaZ, kappa]
  · simp [kappaZ, kappa, gI_cast]

theorem kappaZ_pow_four (a : Atom) : kappaZ a ^ 4 = 1 := by
  apply GaussianInt.toComplex_inj.1
  rw [map_pow, kappaZ_toComplex, kappa_pow_four, map_one]

theorem kappaZ_mul_tG_pow (a : Atom) : kappaZ a * tG ^ Npow a = base a := by
  apply GaussianInt.toComplex_inj.1
  rw [map_mul, map_pow, kappaZ_toComplex, tG_toComplex, kappa_mul_tC_pow]

theorem Npow_eq_two_pow (a : Atom) : ∃ s, Npow a = 2 ^ s := by
  rcases a with k | k | ⟨k, e⟩
  · exact ⟨0, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨e + 2, rfl⟩

theorem mOf_le_nOf (a : Atom) : mOf a ≤ nOf a := by
  rcases a with k | k | ⟨k, e⟩
  · exact le_rfl
  · exact le_rfl
  · exact Nat.le_mul_of_pos_left _ (by positivity)

/-- A primitive prime of a non-exceptional atom: odd, `≡ 1 (mod 4)`, not dividing `m`. -/
theorem exists_prime_of_atom (a : Atom) (ha : a ∉ exceptional) :
    ∃ p, p.Prime ∧ p % 4 = 1 ∧ p ≠ 2 ∧ ¬ p ∣ mOf a ∧ (p : ℤ) ∣ (atom a).norm := by
  obtain ⟨p, hp, hord, hdvd⟩ := exists_primitive_atom a ha
  have : Fact p.Prime := ⟨hp⟩
  have hge := prime_ge_of_orderOf (nOf_pos a) hord
  have hle := mOf_le_nOf a
  exact ⟨p, hp, mod_four_eq_one_of_orderOf (nOf_pos a) hord, ne_two_of_orderOf (nOf_pos a) hord,
    Nat.not_dvd_of_pos_of_lt (mOf_odd a).pos (by omega), hdvd⟩

/-- Every root in the orbit of an atom has a good prime, given a prime `p ≡ 1 (mod 4)`,
`p ∤ m`, dividing the norm of the atom. -/
theorem hasGoodPrime_orbit_of_prime (a : Atom) {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1)
    (hp2 : p ≠ 2) (hpm : ¬ p ∣ mOf a) (hdvd : (p : ℤ) ∣ (atom a).norm) {r : ℂ}
    (hr : r ∈ orbit a) : HasGoodPrime r := by
  obtain ⟨ρ, hρ, hρp, hρa⟩ := exists_prime_dvd_of_dvd_norm hp h4 hdvd
  obtain ⟨s, hs⟩ := Npow_eq_two_pow a
  have hr1 : r ∈ (cycPoly (mOf a) (2 ^ s) (GaussianInt.toComplex (kappaZ a))).roots := by
    rw [kappaZ_toComplex, ← hs]; exact hr
  have hgal : galOrbit r =
      (cycPoly (mOf a) (2 ^ s) (GaussianInt.toComplex (kappaZ a))).roots := by
    rw [kappaZ_toComplex, ← hs]; exact galOrbit_orbit a hr
  refine hasGoodPrime_of_dvd (mOf_odd a).pos (kappaZ_pow_four a) hr1 hgal hρ ?_ hp hp2 hpm
    ⟨star ρ, hρp.symm⟩
  rw [← hs, kappaZ_mul_tG_pow]
  exact hρa

/-- Every root in the orbit of a non-exceptional atom has a good prime. -/
theorem hasGoodPrime_orbit (a : Atom) (ha : a ∉ exceptional) {r : ℂ} (hr : r ∈ orbit a) :
    HasGoodPrime r := by
  obtain ⟨p, hp, h4, hp2, hpm, hdvd⟩ := exists_prime_of_atom a ha
  exact hasGoodPrime_orbit_of_prime a hp h4 hp2 hpm hdvd hr

/-- The constant of the partner orbit, as a Gaussian integer. -/
def kappaZp (a : Atom) : GaussianInt := star (kappaZ a) * (-gI) ^ Npow a

theorem kappaZp_toComplex (a : Atom) :
    GaussianInt.toComplex (kappaZp a) = conj (kappa a) * (-I) ^ Npow a := by
  rw [kappaZp, map_mul, map_pow, map_neg, GaussianInt.toComplex_star, kappaZ_toComplex, gI_cast]

theorem kappaZp_pow_four (a : Atom) : kappaZp a ^ 4 = 1 := by
  apply GaussianInt.toComplex_inj.1
  rw [map_pow, kappaZp_toComplex, kappa'_pow_four (kappa_pow_four a), map_one]

theorem kappaZp_mul_tG_pow (a : Atom) : kappaZp a * tG ^ Npow a = star (base a) := by
  rw [← kappaZ_mul_tG_pow, star_mul', star_pow, star_tG, kappaZp, mul_assoc, ← mul_pow]

/-- The same for the partner of the orbit of an atom. -/
theorem hasGoodPrime_partner_of_prime (a : Atom) {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1)
    (hp2 : p ≠ 2) (hpm : ¬ p ∣ mOf a) (hdvd : (p : ℤ) ∣ (atom a).norm) {r : ℂ}
    (hr : r ∈ partner (orbit a)) : HasGoodPrime r := by
  rw [← Zsqrtd.norm_conj] at hdvd
  obtain ⟨ρ, hρ, hρp, hρa⟩ := exists_prime_dvd_of_dvd_norm hp h4 hdvd
  obtain ⟨s, hs⟩ := Npow_eq_two_pow a
  have hr1 : r ∈ (cycPoly (mOf a) (2 ^ s) (GaussianInt.toComplex (kappaZp a))).roots := by
    rw [kappaZp_toComplex, ← hs, ← partner_orbit_eq]; exact hr
  have hgal : galOrbit r =
      (cycPoly (mOf a) (2 ^ s) (GaussianInt.toComplex (kappaZp a))).roots := by
    rw [kappaZp_toComplex, ← hs, ← partner_orbit_eq]; exact galOrbit_partner a hr
  refine hasGoodPrime_of_dvd (mOf_odd a).pos (kappaZp_pow_four a) hr1 hgal hρ ?_ hp hp2 hpm
    ⟨star ρ, hρp.symm⟩
  rw [← hs, kappaZp_mul_tG_pow, ← star_eval_cyclotomic]
  exact hρa

/-- Every root in the partner of the orbit of a non-exceptional atom has a good prime. -/
theorem hasGoodPrime_partner (a : Atom) (ha : a ∉ exceptional) {r : ℂ}
    (hr : r ∈ partner (orbit a)) : HasGoodPrime r := by
  obtain ⟨p, hp, h4, hp2, hpm, hdvd⟩ := exists_prime_of_atom a ha
  exact hasGoodPrime_partner_of_prime a hp h4 hp2 hpm hdvd hr

/-! ## 6. The self-paired orbits -/

/-- `κ = ± i` of a self-paired orbit, as a Gaussian integer. -/
def kappaSZ (b : Bool) : GaussianInt := if b then gI else -gI

theorem kappaSZ_toComplex (b : Bool) : GaussianInt.toComplex (kappaSZ b) = kappaS b := by
  cases b <;> simp [kappaSZ, kappaS, gI_cast]

theorem kappaSZ_pow_four (b : Bool) : kappaSZ b ^ 4 = 1 := by
  apply GaussianInt.toComplex_inj.1
  rw [map_pow, kappaSZ_toComplex, kappaS_pow_four, map_one]

/-- The atom of a self-paired orbit is `Φ_m(∓2)`: `± i t² = ∓ 2`. -/
theorem kappaSZ_mul_tG_sq (b : Bool) :
    kappaSZ b * tG ^ 2 = ((if b then -2 else 2 : ℤ) : GaussianInt) := by
  cases b <;> ext <;> simp [kappaSZ, gI, tG_sq]

/-- Some Gaussian prime divides a rational prime. -/
theorem exists_gaussian_prime_dvd {q : ℕ} (hq : q.Prime) :
    ∃ ρ : GaussianInt, Prime ρ ∧ ρ ∣ (q : GaussianInt) := by
  have h0 : (q : GaussianInt) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hu : ¬ IsUnit (q : GaussianInt) := by
    intro h
    have h1 := Zsqrtd.norm_eq_one_iff.2 h
    rw [Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast] at h1
    have := hq.two_le
    nlinarith
  obtain ⟨ρ, hρ, hdvd⟩ := WfDvdMonoid.exists_irreducible_factor hu h0
  exact ⟨ρ, hρ.prime, hdvd⟩

/-- If 2 has order `n` modulo `q`, then `n < q`. -/
theorem lt_of_orderOf_two {q n : ℕ} [hq : Fact q.Prime] (hn : 0 < n)
    (h : orderOf (2 : ZMod q) = n) : n < q := by
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h0
    have h1 : (2 : ZMod q) ^ n = 1 := by rw [← h]; exact pow_orderOf_eq_one _
    rw [h0, zero_pow hn.ne'] at h1
    exact zero_ne_one h1
  have hd := ZMod.orderOf_dvd_card_sub_one h2
  rw [h] at hd
  have := hq.out.two_le
  have := Nat.le_of_dvd (by omega) hd
  omega

/-- If 2 has order `n` modulo `q`, then `q ∣ Φ_n(2)`. -/
theorem dvd_cyclotomic_of_orderOf {q n : ℕ} [Fact q.Prime] (hn : 0 < n)
    (h : orderOf (2 : ZMod q) = n) : (q : ℤ) ∣ (cyclotomic n ℤ).eval 2 := by
  have hprim : IsPrimitiveRoot (2 : ZMod q) n := by rw [← h]; exact IsPrimitiveRoot.orderOf 2
  have hroot := hprim.isRoot_cyclotomic hn
  rw [IsRoot.def, ← map_cyclotomic_int n (ZMod q)] at hroot
  have e := eval_intCast_map (Int.castRingHom (ZMod q)) (cyclotomic n ℤ) 2
  rw [Int.cast_ofNat, hroot] at e
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 e.symm

/-- A self-paired orbit has a good prime as soon as an odd prime `q ∤ m` divides its atom
`Φ_m(∓2)`. -/
theorem hasGoodPrime_selfOrb_of_dvd (k : ℕ) (b : Bool) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqm : ¬ q ∣ 2 * k + 1)
    (hdvd : (q : ℤ) ∣ (cyclotomic (2 * k + 1) ℤ).eval (if b then -2 else 2)) {r : ℂ}
    (hr : r ∈ selfOrb k b) : HasGoodPrime r := by
  obtain ⟨ρ, hρ, hρq⟩ := exists_gaussian_prime_dvd hq
  have hr1 : r ∈ (cycPoly (2 * k + 1) (2 ^ 1) (GaussianInt.toComplex (kappaSZ b))).roots := by
    rw [kappaSZ_toComplex, pow_one]; exact hr
  have hgal : galOrbit r =
      (cycPoly (2 * k + 1) (2 ^ 1) (GaussianInt.toComplex (kappaSZ b))).roots := by
    rw [kappaSZ_toComplex, pow_one]; exact galOrbit_selfOrb k b hr
  refine hasGoodPrime_of_dvd (by omega) (kappaSZ_pow_four b) hr1 hgal hρ ?_ hq hq2 hqm hρq
  rw [pow_one, kappaSZ_mul_tG_sq, ← map_cyclotomic_int (2 * k + 1) GaussianInt, eval_intCast_map]
  have h1 := map_dvd (Int.castRingHom GaussianInt) hdvd
  rw [map_natCast] at h1
  exact hρq.trans h1

/-- `Φ_m(2 i X²)`-type orbits, `κ = -i`: the atom is `Φ_m(2)`, and Bang's theorem gives a prime
for `m ≥ 3`. -/
theorem hasGoodPrime_selfOrb_false {k : ℕ} (hk : 1 ≤ k) {r : ℂ} (hr : r ∈ selfOrb k false) :
    HasGoodPrime r := by
  obtain ⟨q, hq, hord⟩ := bang (2 * k + 1) (by omega) (by omega)
  have : Fact q.Prime := ⟨hq⟩
  have hlt := lt_of_orderOf_two (by omega) hord
  have hdvd := dvd_cyclotomic_of_orderOf (by omega) hord
  exact hasGoodPrime_selfOrb_of_dvd k false hq (by omega)
    (Nat.not_dvd_of_pos_of_lt (by omega) hlt) (by simpa using hdvd) hr

/-- `κ = i`: the atom is `Φ_m(-2) = Φ_{2m}(2)`, and Bang's theorem gives a prime for `m ≥ 5`. -/
theorem hasGoodPrime_selfOrb_true {k : ℕ} (hk : 2 ≤ k) {r : ℂ} (hr : r ∈ selfOrb k true) :
    HasGoodPrime r := by
  obtain ⟨q, hq, hord⟩ := bang (2 * (2 * k + 1)) (by omega) (by omega)
  have : Fact q.Prime := ⟨hq⟩
  have hlt := lt_of_orderOf_two (by omega) hord
  have hdvd := dvd_cyclotomic_of_orderOf (by omega) hord
  rw [cyclotomic_two_mul_of_odd ⟨k, rfl⟩ (by omega) ℤ, eval_comp, eval_neg, eval_X] at hdvd
  exact hasGoodPrime_selfOrb_of_dvd k true hq (by omega)
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) (by simpa using hdvd) hr

/-! ## 7. The remaining orbits lie in `R0` -/

theorem ζ120_pow_60 : ζ120 ^ 60 = -1 := by
  rw [show 60 = 30 * 2 by norm_num, pow_mul, ζ120_pow_30, Complex.I_sq]

theorem ζ120_pow_90 : ζ120 ^ 90 = -I := by
  rw [show 90 = 60 + 30 by norm_num, pow_add, ζ120_pow_60, ζ120_pow_30, neg_one_mul]

/-- The roots of `Φ_m(ζ^c X^N)` are in `R0` when a finite check on exponents passes. -/
theorem mem_R0_of_roots {m N c : ℕ} (hm : 0 < m) (hN : N ≠ 0) (hc : 120 ∣ 4 * c)
    (hdvd : 4 * m * N ∣ 120)
    (hdec : ∀ j < 120, 120 / Nat.gcd 120 (c + N * j) = m → j ∈ R0Exps)
    {r : ℂ} (hr : r ∈ (cycPoly m N (ζ120 ^ c)).roots) : r ∈ R0 := by
  have : NeZero 120 := ⟨by norm_num⟩
  have hκ : (ζ120 ^ c) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm]; exact (ζ120_prim.pow_eq_one_iff_dvd _).2 hc
  have hκ0 : ζ120 ^ c ≠ 0 := by intro h; rw [h] at hκ; norm_num at hκ
  have hpow := pow_eq_one_of_mem_roots hm hκ hN hr
  have h120 : r ^ 120 = 1 := by
    obtain ⟨t, ht⟩ := hdvd
    rw [ht, pow_mul, hpow, one_pow]
  obtain ⟨j, hj, rfl⟩ := ζ120_prim.eq_pow_of_pow_eq_one h120
  have hprim := (mem_roots_cycPoly hm hκ0 hN).1 hr
  have e : ζ120 ^ c * (ζ120 ^ j) ^ N = ζ120 ^ (c + N * j) := by
    rw [← pow_mul, ← pow_add, mul_comm j N]
  rw [e] at hprim
  have hord := hprim.eq_orderOf
  rw [orderOf_ζ120_pow] at hord
  exact ⟨j, hdec j hj hord.symm, rfl⟩

theorem orbit_P_eq (k : ℕ) : orbit (.P k) = (cycPoly (2 * k + 1) 1 (ζ120 ^ 0)).roots := by
  rw [pow_zero]; rfl

theorem orbit_Q_eq (k : ℕ) : orbit (.Q k) = (cycPoly (2 * k + 1) 1 (ζ120 ^ 60)).roots := by
  rw [ζ120_pow_60]; rfl

theorem partner_P_eq (k : ℕ) :
    partner (orbit (.P k)) = (cycPoly (2 * k + 1) 1 (ζ120 ^ 90)).roots := by
  rw [partner_orbit_eq, ζ120_pow_90]
  simp [mOf, Npow, kappa]

theorem partner_Q_eq (k : ℕ) :
    partner (orbit (.Q k)) = (cycPoly (2 * k + 1) 1 (ζ120 ^ 30)).roots := by
  rw [partner_orbit_eq, ζ120_pow_30]
  simp [mOf, Npow, kappa]

theorem selfOrb_false_eq (k : ℕ) :
    selfOrb k false = (cycPoly (2 * k + 1) 2 (ζ120 ^ 90)).roots := by
  rw [selfOrb, ζ120_pow_90]; simp [kappaS]

theorem selfOrb_true_eq (k : ℕ) :
    selfOrb k true = (cycPoly (2 * k + 1) 2 (ζ120 ^ 30)).roots := by
  rw [selfOrb, ζ120_pow_30]; simp [kappaS]

/-- The orbits `O_1, O_2, O_6, O_10` lie in `R0`. -/
theorem orbit_exceptional_R0 {a : Atom} (ha : a ∈ exceptional) {r : ℂ} (hr : r ∈ orbit a) :
    r ∈ R0 := by
  simp only [exceptional, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · rw [orbit_P_eq] at hr
    exact mem_R0_of_roots (by norm_num) one_ne_zero (by decide) (by decide)
      (by decide +kernel) hr
  · rw [orbit_Q_eq] at hr
    exact mem_R0_of_roots (by norm_num) one_ne_zero (by decide) (by decide)
      (by decide +kernel) hr
  · rw [orbit_Q_eq] at hr
    exact mem_R0_of_roots (by norm_num) one_ne_zero (by decide) (by decide)
      (by decide +kernel) hr
  · rw [orbit_Q_eq] at hr
    exact mem_R0_of_roots (by norm_num) one_ne_zero (by decide) (by decide)
      (by decide +kernel) hr

/-- Their partners lie in `R0`. -/
theorem partner_exceptional_R0 {a : Atom} (ha : a ∈ exceptional) {r : ℂ}
    (hr : r ∈ partner (orbit a)) : r ∈ R0 := by
  simp only [exceptional, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · rw [partner_P_eq] at hr
    exact mem_R0_of_roots (by norm_num) one_ne_zero (by decide) (by decide)
      (by decide +kernel) hr
  · rw [partner_Q_eq] at hr
    exact mem_R0_of_roots (by norm_num) one_ne_zero (by decide) (by decide)
      (by decide +kernel) hr
  · rw [partner_Q_eq] at hr
    exact mem_R0_of_roots (by norm_num) one_ne_zero (by decide) (by decide)
      (by decide +kernel) hr
  · rw [partner_Q_eq] at hr
    exact mem_R0_of_roots (by norm_num) one_ne_zero (by decide) (by decide)
      (by decide +kernel) hr

/-- The self-paired orbits `{±ζ_8}` (atom `Φ_1(2) = 1`), `{±ζ_8^3}` (atom `Φ_1(-2) = -3`) and
`O_24` (atom `Φ_3(-2) = 3`) lie in `R0`. -/
theorem selfOrb_zero_false_R0 {r : ℂ} (hr : r ∈ selfOrb 0 false) : r ∈ R0 := by
  rw [selfOrb_false_eq] at hr
  exact mem_R0_of_roots (by norm_num) two_ne_zero (by decide) (by decide) (by decide +kernel) hr

theorem selfOrb_zero_true_R0 {r : ℂ} (hr : r ∈ selfOrb 0 true) : r ∈ R0 := by
  rw [selfOrb_true_eq] at hr
  exact mem_R0_of_roots (by norm_num) two_ne_zero (by decide) (by decide) (by decide +kernel) hr

theorem selfOrb_one_true_R0 {r : ℂ} (hr : r ∈ selfOrb 1 true) : r ∈ R0 := by
  rw [selfOrb_true_eq] at hr
  exact mem_R0_of_roots (by norm_num) two_ne_zero (by decide) (by decide) (by decide +kernel) hr

/-! ## 8. Every root of unity outside `R0` has a good prime -/

/-- **`GoodPrimes` holds** (milestone M4.2). -/
theorem goodPrimes : GoodPrimes := by
  intro r hr hR0
  obtain ⟨n, hn, hrn⟩ := isOfFinOrder_iff_pow_eq_one.1 hr
  rcases exists_explicit_orbit hn hrn with ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨k, b, hkb⟩
  · by_cases hex : a ∈ exceptional
    · exact absurd (orbit_exceptional_R0 hex ha) hR0
    · exact hasGoodPrime_orbit a hex ha
  · by_cases hex : a ∈ exceptional
    · exact absurd (partner_exceptional_R0 hex ha) hR0
    · exact hasGoodPrime_partner a hex ha
  · cases b
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact absurd (selfOrb_zero_false_R0 hkb) hR0
      · exact hasGoodPrime_selfOrb_false hk hkb
    · rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk
      · exact absurd (selfOrb_zero_true_R0 hkb) hR0
      · exact absurd (selfOrb_one_true_R0 hkb) hR0
      · exact hasGoodPrime_selfOrb_true hk hkb

/-- **Step 2 of Theorem C, unconditional.** Every multiplicative relation among the `1 - r/t`
(`r` roots of unity) is supported on the 24 roots of `R0`. -/
theorem support_subset_R0' {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ}
    (h : IsRelation S e) : ∀ r ∈ S, r ∉ R0 → e r = 0 :=
  support_subset_R0 goodPrimes hS h

end PiFormula
