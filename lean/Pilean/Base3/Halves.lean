/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Base3.GoodPrimes
public import Pilean.PiFormula.Lemma2

/-!
# Base 3: each Aurifeuillian factor of `3^(3E) + 1` has a primitive prime

For odd `E ≥ 3` put `L_E = 3^E - 3^((E+1)/2) + 1` and `M_E = 3^E + 3^((E+1)/2) + 1`, so that
`3^(3E) + 1 = (3^E + 1) L_E M_E`. This file proves `PrimitiveHalves3`: each of `L_E`, `M_E` has
a prime factor `p` with `ord_p(3) = 6E`. It is the analogue for base 3 of `Lemma2.lean`.

The proof works in the Eisenstein integers `ℤ[ω]` (`ω² + ω + 1 = 0`), with `t = 1 + 2ω`,
`t² = -3`. Write `E = 3^a m` with `3 ∤ m`, `T = t^(3^a)`, and for `u ∈ {ω, ω²}` let
`h_u = N(Φ_m(u T))`.

1. `h_ω h_{ω²} = Φ_{6E}(3)` (`half_mul_half`). Indeed `Φ_{6E}(3) = Φ_{6m}(3^(3^a))
   = Φ_{3m}(T²) = Φ_{3m}(T) Φ_{3m}(-T) = N(Φ_{3m}(T))`, and
   `N(Φ_{3m}(x)) = N(Φ_m(ωx)) N(Φ_m(ω²x))` (`norm_cyclotomic_mul_three`), which follows from
   `Φ_m(x³) = Φ_{3m}(x) Φ_m(x)` and the Möbius product formula for `N(Φ_m(·))`.
2. `h_u` divides `N((uT)^m - 1) = N(u^m t^E - 1)`, and the two numbers `N(ω t^E - 1)`,
   `N(ω² t^E - 1)` are `L_E` and `M_E` in some order (`norm_w_tE`).
3. `9 h_u ≥ 3^φ(m)` (`half_lower`), from the Möbius product formula: each factor
   `N(z^b - 1)` lies between `(s^b - 1)²` and `(s^b + 1)²`, `s² = N(z)`.
4. A divisor of `Φ_{6E}(3)` that is not `1` and not a prime factor of `6E` has a prime factor
   of order `6E` (`exists_primitive_of_dvd_Phi6`, from the Tau Ceti library).
-/

@[expose] public section

open Polynomial

namespace PiFormula

namespace Base3

/-! ## 1. The reduction -/

/-- `Φ_{6E}(3)`. -/
noncomputable def Phi6 (E : ℕ) : ℤ := (cyclotomic (6 * E) ℤ).eval 3

theorem Phi6_pos {E : ℕ} (hE : 0 < E) : 0 < Phi6 E :=
  cyclotomic_pos (by omega) 3

theorem homogeneous_eq_Phi6 (E : ℕ) :
    TauCeti.homogeneousCyclotomic (6 * E) ((3 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = Phi6 E := by
  rw [Nat.cast_ofNat, Nat.cast_one, TauCeti.homogeneousCyclotomic_one_right]
  rfl

/-- A prime of `Φ_{6E}(3)` whose order is not `6E` divides `6E`, is at least every prime factor
of `6E`, and divides `Φ_{6E}(3)` exactly once. -/
theorem nonprimitive3 {E p : ℕ} (hE : 0 < E) (hp : p.Prime) (hdvd : (p : ℤ) ∣ Phi6 E)
    (hord : orderOf (3 : ZMod p) ≠ 6 * E) :
    p ∣ 6 * E ∧ (∀ q : ℕ, q.Prime → q ∣ 6 * E → q ≤ p) ∧ multiplicity (p : ℤ) (Phi6 E) = 1 := by
  have hdvd' := (homogeneous_eq_Phi6 E).symm ▸ hdvd
  have hb : ¬ (p : ℤ) ∣ ((1 : ℕ) : ℤ) := by
    norm_cast; exact hp.not_dvd_one
  have hiff0 := (hp.dvd_homogeneousCyclotomic_iff_orderOf_eq hb (by omega : 6 * E ≠ 0)).1 hdvd'
  have hiff : orderOf (3 : ZMod p) = ordCompl[p] (6 * E) := by simpa using hiff0
  have hk0 : 0 < orderOf (3 : ZMod p) := hiff ▸ Nat.ordCompl_pos p (by omega)
  have hk4 : orderOf (3 : ZMod p) < 6 * E := lt_of_le_of_ne (hiff ▸ Nat.ordCompl_le _ _) hord
  have hpk : p ∣ 3 ^ orderOf (3 : ZMod p) - 1 ^ orderOf (3 : ZMod p) := by
    rw [one_pow, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)),
      Nat.cast_pow, Nat.cast_ofNat, pow_orderOf_eq_one, Nat.cast_one, sub_self]
  obtain ⟨hpn, hle, hmul⟩ := hp.multiplicity_homogeneousCyclotomic_of_not_primitive
    (by norm_num : Nat.Coprime 3 1) (by norm_num) (by omega : 6 * E ≠ 2) hdvd'
    ⟨_, hk0, hk4, hpk⟩
  exact ⟨hpn, hle, (homogeneous_eq_Phi6 E) ▸ hmul⟩

/-- **The reduction.** A divisor of `Φ_{6E}(3)` that is not `1` and not a prime factor of `6E`
has a prime factor of order `6E`. -/
theorem exists_primitive_of_dvd_Phi6 {E X : ℕ} (hE : 0 < E) (hX : (X : ℤ) ∣ Phi6 E)
    (hX1 : X ≠ 1) (hXp : ¬ (X.Prime ∧ X ∣ 6 * E)) :
    ∃ p, p.Prime ∧ orderOf (3 : ZMod p) = 6 * E ∧ p ∣ X := by
  by_contra hno
  push Not at hno
  have key : ∀ p, p.Prime → p ∣ X → p ∣ 6 * E ∧ (∀ q : ℕ, q.Prime → q ∣ 6 * E → q ≤ p) ∧
      multiplicity (p : ℤ) (Phi6 E) = 1 := fun p hp hpX =>
    nonprimitive3 hE hp ((Int.natCast_dvd_natCast.2 hpX).trans hX) (fun h => hno p hp h hpX)
  obtain ⟨p₀, hp₀, Y, rfl⟩ := Nat.exists_prime_and_dvd hX1
  have k₀ := key p₀ hp₀ (dvd_mul_right _ _)
  by_cases hY : Y = 1
  · subst hY
    rw [mul_one] at hXp
    exact hXp ⟨hp₀, k₀.1⟩
  obtain ⟨p₁, hp₁, hp₁Y⟩ := Nat.exists_prime_and_dvd hY
  have k₁ := key p₁ hp₁ (hp₁Y.trans (dvd_mul_left _ _))
  have heq : p₁ = p₀ := le_antisymm (k₀.2.1 p₁ hp₁ k₁.1) (k₁.2.1 p₀ hp₀ k₀.1)
  rw [heq] at hp₁Y
  have hsq : ((p₀ : ℤ) ^ 2) ∣ Phi6 E := by
    have h1 : p₀ ^ 2 ∣ p₀ * Y := by rw [sq]; exact Nat.mul_dvd_mul_left _ hp₁Y
    have h2 := (Int.natCast_dvd_natCast.2 h1).trans hX
    simpa using h2
  have hfin : FiniteMultiplicity (p₀ : ℤ) (Phi6 E) :=
    FiniteMultiplicity.of_prime_left (Nat.prime_iff_prime_int.1 hp₀) (Phi6_pos hE).ne'
  exact hfin.not_pow_dvd_of_multiplicity_lt (by rw [k₀.2.2]; norm_num) hsq

/-! ## 2. The Eisenstein integers -/

/-- The Eisenstein integers `ℤ[ω]`, `ω² = -1 - ω`. -/
abbrev Eis : Type := QuadraticAlgebra ℤ (-1) (-1)

/-- `ω`. -/
def wE : Eis := ⟨0, 1⟩

/-- `t = 1 + 2ω`, a square root of `-3`. -/
def tE : Eis := ⟨1, 2⟩

theorem eis_norm_eq (z : Eis) : z.norm = z.re ^ 2 - z.re * z.im + z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

theorem eis_norm_nonneg (z : Eis) : 0 ≤ z.norm := by
  rw [eis_norm_eq]; nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]

theorem eis_norm_eq_zero {z : Eis} (h : z.norm = 0) : z = 0 := by
  rw [eis_norm_eq] at h
  have h3 : 3 * z.im ^ 2 ≤ 0 := by nlinarith [sq_nonneg (2 * z.re - z.im)]
  have h4 : z.im ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  have h1 : z.im = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h4
  rw [h1] at h
  have h2 : z.re = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 (by linarith)
  exact QuadraticAlgebra.ext h2 h1

theorem wE_rel : wE ^ 2 + wE + 1 = 0 := by
  ext <;> simp [wE, sq, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem tE_sq : tE ^ 2 = -3 := by
  ext <;> simp [tE, sq]

theorem star_tE : star tE = -tE := by
  ext <;> simp [tE]

theorem norm_wE : wE.norm = 1 := by
  simp [wE, QuadraticAlgebra.norm_def]

theorem norm_tE : tE.norm = 3 := by
  simp [tE, QuadraticAlgebra.norm_def]

theorem cube_eq_one {u : Eis} (hu : u ^ 2 + u + 1 = 0) : u ^ 3 = 1 := by
  linear_combination (u - 1) * hu

theorem wE_cube : wE ^ 3 = 1 := cube_eq_one wE_rel

theorem wE_pow_mod (n : ℕ) : wE ^ n = wE ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, wE_cube, one_pow, one_mul]

/-- `ω` and `ω²` are the two primitive cube roots of unity, of norm 1. -/
theorem wE_pow_facts {i : ℕ} (hi : i = 1 ∨ i = 2) :
    (wE ^ i) ^ 2 + wE ^ i + 1 = 0 ∧ (wE ^ i).norm = 1 := by
  rcases hi with rfl | rfl
  · exact ⟨by rw [pow_one]; exact wE_rel, by rw [pow_one]; exact norm_wE⟩
  · refine ⟨?_, by rw [map_pow, norm_wE, one_pow]⟩
    linear_combination (wE ^ 2 - wE + 1) * wE_rel

/-- `∏_{d ∣ n} N(Φ_d(z)) = N(z^n - 1)`. -/
theorem prod_norm_eval_cyclotomic3 (z : Eis) {n : ℕ} (hn : 0 < n) :
    ∏ i ∈ n.divisors, ((cyclotomic i Eis).eval z).norm = (z ^ n - 1).norm := by
  have h := congrArg (Polynomial.eval z) (prod_cyclotomic_eq_X_pow_sub_one hn Eis)
  rw [Polynomial.eval_prod] at h
  simp only [eval_sub, eval_pow, eval_X, eval_one] at h
  rw [← h]
  exact (map_prod (QuadraticAlgebra.norm (R := ℤ) (a := -1) (b := -1)) _ _).symm

theorem norm_eval_cyclotomic_dvd3 (z : Eis) {n : ℕ} (hn : 0 < n) :
    ((cyclotomic n Eis).eval z).norm ∣ (z ^ n - 1).norm := by
  rw [← prod_norm_eval_cyclotomic3 z hn]
  exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self n hn.ne')

/-- `N(z^n - 1) ≠ 0` when `N(z) > 1` and `n > 0`. -/
theorem norm_pow_sub_one_ne_zero3 {z : Eis} (hz : 1 < z.norm) {n : ℕ} (hn : 0 < n) :
    (z ^ n - 1).norm ≠ 0 := by
  intro h
  have h1 := eis_norm_eq_zero h
  rw [sub_eq_zero] at h1
  have h2 := congrArg QuadraticAlgebra.norm h1
  rw [map_pow, map_one] at h2
  have : (1 : ℤ) < z.norm ^ n := one_lt_pow₀ hz hn.ne'
  omega

theorem norm_eval_cyclotomic_ne_zero3 {z : Eis} (hz : 1 < z.norm) {n : ℕ} (hn : 0 < n) :
    ((cyclotomic n Eis).eval z).norm ≠ 0 := fun h0 =>
  norm_pow_sub_one_ne_zero3 hz hn (zero_dvd_iff.1 (h0 ▸ norm_eval_cyclotomic_dvd3 z hn))

section Moebius

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Möbius inversion: `N(Φ_n(z)) = ∏_{ab = n} N(z^b - 1)^{μ(a)}`, in ℝ. -/
theorem moebius_formula3 {z : Eis} (hz : 1 < z.norm) {n : ℕ} (hn : 0 < n) :
    ∏ x ∈ n.divisorsAntidiagonal, ((z ^ x.2 - 1).norm : ℝ) ^ (μ x.1) =
      (((cyclotomic n Eis).eval z).norm : ℝ) := by
  have hU : ∀ m : ℕ, 0 < m → ((z ^ m - 1).norm : ℝ) ≠ 0 := fun m hm => by
    exact_mod_cast norm_pow_sub_one_ne_zero3 hz hm
  have hA : ∀ m : ℕ, 0 < m → (((cyclotomic m Eis).eval z).norm : ℝ) ≠ 0 := fun m hm => by
    exact_mod_cast norm_eval_cyclotomic_ne_zero3 hz hm
  refine (prod_eq_iff_prod_pow_moebius_eq_of_ne_zero
    (f := fun m => (((cyclotomic m Eis).eval z).norm : ℝ))
    (g := fun m => ((z ^ m - 1).norm : ℝ)) hA hU).1 (fun m hm => ?_) n hn
  exact_mod_cast prod_norm_eval_cyclotomic3 z hm

/-! ## 3. The product of the two halves -/

/-- For a primitive cube root of unity `u` and `3 ∤ b`:
`N(x^(3b) - 1) = N(x^b - 1) N((ux)^b - 1) N((u²x)^b - 1)`. -/
theorem norm_twist {u : Eis} (hu : u ^ 2 + u + 1 = 0) (hNu : u.norm = 1) (x : Eis) {b : ℕ}
    (hb : ¬ 3 ∣ b) :
    (x ^ (3 * b) - 1).norm =
      (x ^ b - 1).norm * (((u * x) ^ b - 1).norm * ((u ^ 2 * x) ^ b - 1).norm) := by
  have hu3 := cube_eq_one hu
  have hpow : u ^ b = u ^ (b % 3) := by
    conv_lhs => rw [← Nat.div_add_mod b 3, pow_add, pow_mul, hu3, one_pow, one_mul]
  have hfac : x ^ (3 * b) - 1 = (x ^ b - 1) * ((x ^ b - u) * (x ^ b - u ^ 2)) := by
    rw [mul_comm 3 b, pow_mul]
    linear_combination (x ^ b - 1) * x ^ b * hu - (x ^ b - 1) * hu3
  have h1 : ((u * x) ^ b - 1).norm * ((u ^ 2 * x) ^ b - 1).norm =
      (x ^ b - u).norm * (x ^ b - u ^ 2).norm := by
    have e0 : (u ^ 2 * x) ^ b = (u ^ b) ^ 2 * x ^ b := by
      rw [mul_pow, ← pow_mul, mul_comm 2 b, pow_mul]
    rw [mul_pow, e0]
    rcases (by omega : b % 3 = 1 ∨ b % 3 = 2) with h | h
    · rw [h, pow_one] at hpow
      rw [hpow]
      have e1 : u * x ^ b - 1 = u * (x ^ b - u ^ 2) := by linear_combination hu3
      have e2 : u ^ 2 * x ^ b - 1 = u ^ 2 * (x ^ b - u) := by linear_combination hu3
      rw [e1, e2, map_mul, map_mul, map_pow, hNu]
      ring
    · rw [h] at hpow
      rw [hpow]
      have e1 : u ^ 2 * x ^ b - 1 = u ^ 2 * (x ^ b - u) := by linear_combination hu3
      have e2 : (u ^ 2) ^ 2 * x ^ b - 1 = u * (x ^ b - u ^ 2) := by
        linear_combination (u * x ^ b + 1) * hu3
      rw [e1, e2, map_mul, map_mul, map_pow, hNu]
      ring
  rw [hfac, map_mul, map_mul, h1]

/-- `N(Φ_{3m}(x)) = N(Φ_m(ux)) N(Φ_m(u²x))` for `3 ∤ m` and a primitive cube root of unity
`u`. -/
theorem norm_cyclotomic_mul_three {u : Eis} (hu : u ^ 2 + u + 1 = 0) (hNu : u.norm = 1)
    {x : Eis} (hx : 1 < x.norm) {m : ℕ} (hm : 0 < m) (h3 : ¬ 3 ∣ m) :
    ((cyclotomic (m * 3) Eis).eval x).norm =
      ((cyclotomic m Eis).eval (u * x)).norm * ((cyclotomic m Eis).eval (u ^ 2 * x)).norm := by
  have hx3 : 1 < (x ^ 3).norm := by rw [map_pow]; exact one_lt_pow₀ hx (by norm_num)
  have hux : 1 < (u * x).norm := by rw [map_mul, hNu, one_mul]; exact hx
  have hu2x : 1 < (u ^ 2 * x).norm := by
    rw [map_mul, map_pow, hNu, one_pow, one_mul]; exact hx
  -- `Φ_m(x³) = Φ_{3m}(x) Φ_m(x)`
  have hexp : (cyclotomic m Eis).eval (x ^ 3) =
      (cyclotomic (m * 3) Eis).eval x * (cyclotomic m Eis).eval x := by
    rw [← expand_eval, cyclotomic_expand_eq_cyclotomic_mul Nat.prime_three h3, eval_mul]
  have hreal : (((cyclotomic m Eis).eval (x ^ 3)).norm : ℝ) =
      (((cyclotomic m Eis).eval x).norm : ℝ) *
        ((((cyclotomic m Eis).eval (u * x)).norm : ℝ) *
          (((cyclotomic m Eis).eval (u ^ 2 * x)).norm : ℝ)) := by
    rw [← moebius_formula3 hx3 hm, ← moebius_formula3 hx hm, ← moebius_formula3 hux hm,
      ← moebius_formula3 hu2x hm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hb : ¬ 3 ∣ p.2 := fun h =>
      h3 (h.trans (Dvd.intro_left _ (Nat.mem_divisorsAntidiagonal.1 hp).1))
    rw [← mul_zpow, ← mul_zpow, ← pow_mul, norm_twist hu hNu x hb]
    simp only [Int.cast_mul]
  have hint : ((cyclotomic m Eis).eval (x ^ 3)).norm =
      ((cyclotomic m Eis).eval x).norm *
        (((cyclotomic m Eis).eval (u * x)).norm * ((cyclotomic m Eis).eval (u ^ 2 * x)).norm) := by
    exact_mod_cast hreal
  rw [hexp, map_mul] at hint
  exact mul_left_cancel₀ (norm_eval_cyclotomic_ne_zero3 hx hm) (by rw [← hint]; ring)

/-- `Φ_n(X^(3^a)) = Φ_{n 3^a}(X)` when `3 ∣ n`. -/
theorem cyclotomic_expand_three_pow {n : ℕ} (h3 : 3 ∣ n) (a : ℕ) (R : Type*) [CommRing R] :
    expand R (3 ^ a) (cyclotomic n R) = cyclotomic (n * 3 ^ a) R := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h : 3 ^ (a + 1) = 3 * 3 ^ a := by ring
    rw [h, expand_mul, ih, cyclotomic_expand_eq_cyclotomic Nat.prime_three
      (h3.trans (dvd_mul_right _ _))]
    congr 1
    ring

theorem tE_pow_sq (a : ℕ) : (tE ^ 3 ^ a) ^ 2 = -(3 : Eis) ^ 3 ^ a := by
  rw [← pow_mul, mul_comm, pow_mul, tE_sq, Odd.neg_pow (Odd.pow (by decide))]

/-- **The two halves multiply to `Φ_{6E}(3)`**, `E = 3^a m`, `m` odd, `3 ∤ m`. -/
theorem half_mul_half {u : Eis} (hu : u ^ 2 + u + 1 = 0) (hNu : u.norm = 1) (a : ℕ) {m : ℕ}
    (hm : Odd m) (h3 : ¬ 3 ∣ m) :
    ((cyclotomic m Eis).eval (u * tE ^ 3 ^ a)).norm *
      ((cyclotomic m Eis).eval (u ^ 2 * tE ^ 3 ^ a)).norm = Phi6 (3 ^ a * m) := by
  have hm0 : 0 < m := hm.pos
  have hNT : (tE ^ 3 ^ a).norm = 3 ^ 3 ^ a := by rw [map_pow, norm_tE]
  have hT1 : 1 < (tE ^ 3 ^ a).norm := by
    rw [hNT]; exact one_lt_pow₀ (by norm_num) (by positivity)
  rw [← norm_cyclotomic_mul_three hu hNu hT1 hm0 h3]
  -- now `N(Φ_{3m}(T)) = Φ_{6E}(3)`
  have hnodd : Odd (m * 3) := hm.mul (by decide)
  have hn1 : 1 < m * 3 := by omega
  have hdiv : ¬ 2 ∣ m * 3 := Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hnodd)
  have E1 : ∀ z : Eis, (cyclotomic (m * 3 * 2) Eis).eval z =
      (cyclotomic (m * 3) Eis).eval (-z) := by
    intro z
    rw [mul_comm (m * 3) 2, cyclotomic_two_mul_of_odd hnodd hn1, eval_comp, eval_neg, eval_X]
  have prodE : ∀ z : Eis, (cyclotomic (m * 3) Eis).eval z * (cyclotomic (m * 3) Eis).eval (-z) =
      (cyclotomic (m * 3) Eis).eval (z ^ 2) := by
    intro z
    rw [← expand_eval, cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two hdiv, eval_mul, E1]
    ring
  have hstar : ∀ w : Eis, star ((cyclotomic (m * 3) Eis).eval w) =
      (cyclotomic (m * 3) Eis).eval (star w) := by
    intro w
    have := Polynomial.eval₂_at_apply (p := cyclotomic (m * 3) Eis) (starRingEnd Eis) w
    rw [← Polynomial.eval_map, map_cyclotomic, starRingEnd_apply, starRingEnd_apply] at this
    exact this.symm
  have hstarT : star (tE ^ 3 ^ a) = -tE ^ 3 ^ a := by
    rw [star_pow, star_tE, Odd.neg_pow (Odd.pow (by decide))]
  -- the norm, read in `ℤ[ω]`
  have hnorm : (algebraMap ℤ Eis) ((cyclotomic (m * 3) Eis).eval (tE ^ 3 ^ a)).norm =
      (cyclotomic (m * 3) Eis).eval (-(3 : Eis) ^ 3 ^ a) := by
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star, hstar, hstarT, prodE, tE_pow_sq]
  -- `Φ_{3m}(-Q) = Φ_{6m}(Q) = Φ_{6E}(3)`
  have h6 : (cyclotomic (m * 3) Eis).eval (-(3 : Eis) ^ 3 ^ a) =
      (cyclotomic (6 * (3 ^ a * m)) Eis).eval 3 := by
    rw [← E1, show 6 * (3 ^ a * m) = m * 3 * 2 * 3 ^ a by ring,
      ← cyclotomic_expand_three_pow (n := m * 3 * 2) ⟨m * 2, by ring⟩ a Eis, expand_eval]
  have hPhi : (algebraMap ℤ Eis) (Phi6 (3 ^ a * m)) =
      (cyclotomic (6 * (3 ^ a * m)) Eis).eval 3 := by
    have := Polynomial.eval₂_at_apply (p := cyclotomic (6 * (3 ^ a * m)) ℤ) (algebraMap ℤ Eis) 3
    rw [← Polynomial.eval_map, map_cyclotomic] at this
    simpa [Phi6] using this.symm
  exact QuadraticAlgebra.algebraMap_injective (hnorm.trans (h6.trans hPhi.symm))

/-! ## 4. The size bound -/

/-- `N(y - 1)` lies between `(s - 1)²` and `(s + 1)²`, where `s² = N(y)`. -/
theorem norm_sub_one_bounds (y : Eis) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ^ 2 = (y.norm : ℝ)) :
    (s - 1) ^ 2 ≤ ((y - 1).norm : ℝ) ∧ ((y - 1).norm : ℝ) ≤ (s + 1) ^ 2 := by
  have h1 : (y - 1).norm = y.norm + 1 - (2 * y.re - y.im) := by
    rw [eis_norm_eq, eis_norm_eq]
    simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one]
    ring
  have h2 : (2 * y.re - y.im) ^ 2 ≤ 4 * y.norm := by
    rw [eis_norm_eq]; nlinarith [sq_nonneg y.im]
  have h2' : ((2 * y.re - y.im : ℤ) : ℝ) ^ 2 ≤ (2 * s) ^ 2 := by
    have h' : ((2 * y.re - y.im : ℤ) : ℝ) ^ 2 ≤ 4 * (y.norm : ℝ) := by exact_mod_cast h2
    nlinarith
  obtain ⟨h3, h4⟩ := abs_le_of_sq_le_sq' h2' (by positivity)
  rw [h1]
  push_cast at h3 h4 ⊢
  constructor <;> nlinarith

/-- One factor of the Möbius product: with `r > 1` and `(r - 1)² ≤ U ≤ (r + 1)²`,
`U^e ≥ (r²)^e (1 - 1/r)²` for `e ∈ {0, 1, -1}`. -/
theorem factor_bound3 {U r : ℝ} {e : ℤ} (he : e = 0 ∨ e = 1 ∨ e = -1) (hr : 1 < r)
    (hlo : (r - 1) ^ 2 ≤ U) (hhi : U ≤ (r + 1) ^ 2) :
    (r ^ 2) ^ e * (1 - r⁻¹) ^ 2 ≤ U ^ e := by
  have hr0 : 0 < r := by linarith
  have hx : 1 - r⁻¹ = (r - 1) / r := by field_simp
  have hU0 : 0 < U := lt_of_lt_of_le (by nlinarith) hlo
  rcases he with rfl | rfl | rfl
  · simp only [zpow_zero, one_mul]
    have h1 : 0 ≤ 1 - r⁻¹ := by rw [hx]; exact div_nonneg (by linarith) hr0.le
    have h2 : 1 - r⁻¹ ≤ 1 := by have := inv_pos.2 hr0; linarith
    exact pow_le_one₀ h1 h2
  · simp only [zpow_one]
    have : r ^ 2 * (1 - r⁻¹) ^ 2 = (r - 1) ^ 2 := by rw [hx]; field_simp
    rw [this]
    exact hlo
  · rw [zpow_neg_one, zpow_neg_one]
    have hinv : ((r + 1) ^ 2)⁻¹ ≤ U⁻¹ := inv_anti₀ hU0 hhi
    refine le_trans ?_ hinv
    have e1 : (r ^ 2)⁻¹ * (1 - r⁻¹) ^ 2 = (r - 1) ^ 2 / (r ^ 2 * r ^ 2) := by
      rw [hx]; field_simp
    rw [e1, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hr2 : 1 < r ^ 2 := by nlinarith
    have e2 : (r - 1) ^ 2 * (r + 1) ^ 2 = r ^ 2 * r ^ 2 - 2 * r ^ 2 + 1 := by ring
    rw [e2]
    linarith

theorem real_zpow_sum {c : ℝ} (hc : c ≠ 0) (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℤ) :
    c ^ (∑ i ∈ s, f i) = ∏ i ∈ s, c ^ f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hc, ih]

/-- **Lower bound.** With `s² = N(z)`, `s > 1`:
`N(Φ_m(z)) ≥ N(z)^φ(m) (∏_{d ∣ m} (1 - s^(-d)))²`. -/
theorem lower_bound3 {z : Eis} {s : ℝ} (hs1 : 1 < s) (hs : s ^ 2 = (z.norm : ℝ)) {m : ℕ}
    (hm : 0 < m) :
    (s ^ 2) ^ m.totient * (∏ d ∈ m.divisors, (1 - (s ^ d)⁻¹)) ^ 2 ≤
      (((cyclotomic m Eis).eval z).norm : ℝ) := by
  have hs0 : 0 < s := by linarith
  have hz : 1 < z.norm := by
    have : (1 : ℝ) < (z.norm : ℝ) := by rw [← hs]; nlinarith
    exact_mod_cast this
  rw [← moebius_formula3 hz hm]
  have hφ : (s ^ 2) ^ m.totient =
      ∏ x ∈ m.divisorsAntidiagonal, (s ^ 2) ^ (μ x.1 * (x.2 : ℤ)) := by
    rw [← real_zpow_sum (by positivity) _ (fun x => μ x.1 * (x.2 : ℤ)),
      sum_moebius_mul_eq_totient hm, zpow_natCast]
  have hd : (∏ d ∈ m.divisors, (1 - (s ^ d)⁻¹)) ^ 2 =
      ∏ x ∈ m.divisorsAntidiagonal, (1 - (s ^ x.2)⁻¹) ^ 2 := by
    rw [← Finset.prod_pow]
    exact (Nat.prod_divisorsAntidiagonal' (f := fun _ b => (1 - (s ^ b)⁻¹) ^ 2)).symm
  rw [hφ, hd, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro x _; positivity
  · intro x hx
    have hb : x.2 ≠ 0 := by
      rintro h0
      have := Nat.mem_divisorsAntidiagonal.1 hx
      rw [h0, mul_zero] at this
      exact this.2 this.1.symm
    have hr : 1 < s ^ x.2 := one_lt_pow₀ hs1 hb
    obtain ⟨hlo, hhi⟩ := norm_sub_one_bounds (z ^ x.2) (s := s ^ x.2) (by positivity)
      (by rw [map_pow, Int.cast_pow, ← hs]; exact pow_right_comm s x.2 2)
    have key := factor_bound3 (moebius_eq_or x.1) hr hlo hhi
    have e : (s ^ 2) ^ (μ x.1 * (x.2 : ℤ)) = ((s ^ x.2) ^ 2) ^ μ x.1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, pow_right_comm]
    rw [e]
    exact key

end Moebius

/-- `∏ (1 - f i) ≥ 1 - ∑ f i` for `0 ≤ f i ≤ 1`. -/
theorem one_sub_sum_le_prod (S : Finset ℕ) (f : ℕ → ℝ) (h0 : ∀ i ∈ S, 0 ≤ f i)
    (h1 : ∀ i ∈ S, f i ≤ 1) : 1 - ∑ i ∈ S, f i ≤ ∏ i ∈ S, (1 - f i) := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons i S hi ih =>
    rw [Finset.sum_cons, Finset.prod_cons]
    have hi0 := h0 i (Finset.mem_cons_self i S)
    have hi1 := h1 i (Finset.mem_cons_self i S)
    have ih' := ih (fun j hj => h0 j (Finset.mem_cons_of_mem hj))
      (fun j hj => h1 j (Finset.mem_cons_of_mem hj))
    have hs0 : 0 ≤ ∑ j ∈ S, f j :=
      Finset.sum_nonneg fun j hj => h0 j (Finset.mem_cons_of_mem hj)
    have h2 := mul_le_mul_of_nonneg_left ih' (by linarith : (0 : ℝ) ≤ 1 - f i)
    nlinarith [mul_nonneg hi0 hs0]

/-- For `m` prime to 6 and `0 ≤ x ≤ 10/17`: `∏_{d ∣ m} (1 - x^d) ≥ 1/3`. The divisors other
than 1 are at least 5, so the product is at least `(1 - x)(1 - x⁵/(1 - x)) = 1 - x - x⁵`. -/
theorem prod_divisors_ge {m : ℕ} (hm : Odd m) (h3 : ¬ 3 ∣ m) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 10 / 17) : 1 / 3 ≤ ∏ d ∈ m.divisors, (1 - x ^ d) := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have h1mem : 1 ∈ m.divisors := Nat.one_mem_divisors.2 hm0
  rw [← Finset.mul_prod_erase _ _ h1mem, pow_one]
  have hx1 : x < 1 := by linarith
  have hsum : ∑ d ∈ m.divisors.erase 1, x ^ d ≤ x ^ 5 / (1 - x) := by
    have hsub : m.divisors.erase 1 ⊆ Finset.Ico 5 (m + 1) := by
      intro d hd
      obtain ⟨hd1, hdm⟩ := Finset.mem_erase.1 hd
      have hdvd := Nat.dvd_of_mem_divisors hdm
      have hle := Nat.le_of_dvd hm.pos hdvd
      have hodd : ¬ 2 ∣ d := fun h =>
        (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 (h.trans hdvd))
      have h3d : ¬ 3 ∣ d := fun h => h3 (h.trans hdvd)
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hdm
      rw [Finset.mem_Ico]
      omega
    calc ∑ d ∈ m.divisors.erase 1, x ^ d ≤ ∑ d ∈ Finset.Ico 5 (m + 1), x ^ d :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg hx0 _
      _ ≤ x ^ 5 / (1 - x) := geom_sum_Ico_le_of_lt_one hx0 hx1
  have hprod := one_sub_sum_le_prod (m.divisors.erase 1) (fun d => x ^ d)
    (fun _ _ => pow_nonneg hx0 _) (fun _ _ => pow_le_one₀ hx0 hx1.le)
  have h5 : x ^ 5 ≤ (10 / 17) ^ 5 := pow_le_pow_left₀ hx0 hx 5
  have hpos : 0 < 1 - x := by linarith
  have h2 : (1 - x) * (1 - x ^ 5 / (1 - x)) ≤
      (1 - x) * ∏ d ∈ m.divisors.erase 1, (1 - x ^ d) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  have h3' : (1 - x) * (1 - x ^ 5 / (1 - x)) = 1 - x - x ^ 5 := by field_simp
  rw [h3'] at h2
  norm_num at h5
  linarith

/-- **Size of a half.** If `N(z) ≥ 3` and `m` is prime to 6, then `9 N(Φ_m(z)) ≥ 3^φ(m)`. -/
theorem half_lower {z : Eis} (hz : 3 ≤ z.norm) {m : ℕ} (hm : Odd m) (h3 : ¬ 3 ∣ m) :
    3 ^ m.totient ≤ 9 * ((cyclotomic m Eis).eval z).norm := by
  have hN3 : (3 : ℝ) ≤ (z.norm : ℝ) := by exact_mod_cast hz
  have hN0 : (0 : ℝ) ≤ (z.norm : ℝ) := by linarith
  set s := Real.sqrt (z.norm : ℝ) with hsdef
  have hs : s ^ 2 = (z.norm : ℝ) := Real.sq_sqrt hN0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs17 : 17 / 10 ≤ s := by
    by_contra h
    push Not at h
    nlinarith
  have hs1 : 1 < s := by linarith
  have hlow := lower_bound3 hs1 hs hm.pos
  have hx : s⁻¹ ≤ 10 / 17 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    norm_num
    linarith
  have hprod := prod_divisors_ge hm h3 (inv_nonneg.2 hs0) hx
  have hrew : ∏ d ∈ m.divisors, (1 - (s ^ d)⁻¹) = ∏ d ∈ m.divisors, (1 - s⁻¹ ^ d) :=
    Finset.prod_congr rfl fun d _ => by rw [inv_pow]
  rw [hrew, hs] at hlow
  have hP2 : (1 : ℝ) / 9 ≤ (∏ d ∈ m.divisors, (1 - s⁻¹ ^ d)) ^ 2 := by nlinarith
  have hpow : (3 : ℝ) ^ m.totient ≤ (z.norm : ℝ) ^ m.totient :=
    pow_le_pow_left₀ (by norm_num) hN3 _
  have hfin : (3 : ℝ) ^ m.totient ≤ 9 * (((cyclotomic m Eis).eval z).norm : ℝ) := by
    have h1 : (z.norm : ℝ) ^ m.totient * (1 / 9) ≤
        (z.norm : ℝ) ^ m.totient * (∏ d ∈ m.divisors, (1 - s⁻¹ ^ d)) ^ 2 :=
      mul_le_mul_of_nonneg_left hP2 (by positivity)
    linarith
  exact_mod_cast hfin

/-- `N(z - 1) > 3` when `N(z) ≥ 27`. -/
theorem three_lt_norm_sub_one {z : Eis} (hz : 27 ≤ z.norm) : 3 < (z - 1).norm := by
  have h1 : (z - 1).norm = z.norm + 1 - (2 * z.re - z.im) := by
    rw [eis_norm_eq, eis_norm_eq]
    simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one]
    ring
  have h2 : (2 * z.re - z.im) ^ 2 ≤ 4 * z.norm := by
    rw [eis_norm_eq]; nlinarith [sq_nonneg z.im]
  rw [h1]
  by_contra h
  push Not at h
  have h3 : z.norm - 2 ≤ 2 * z.re - z.im := by linarith
  have h4 : (z.norm - 2) ^ 2 ≤ (2 * z.re - z.im) ^ 2 :=
    pow_le_pow_left₀ (by linarith) h3 2
  nlinarith

theorem nine_mul_lt_three_pow {s : ℕ} (hs : 4 ≤ s) : 9 * (s + 1) < 3 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih => rw [pow_succ]; omega

/-- A prime factor of `m` is at most `φ(m) + 1`. -/
theorem prime_le_totient_succ {p m : ℕ} (hp : p.Prime) (hpm : p ∣ m) (hm : 0 < m) :
    p ≤ m.totient + 1 := by
  have h1 := Nat.le_of_dvd (Nat.totient_pos.2 hm) (Nat.totient_dvd_of_dvd hpm)
  rw [Nat.totient_prime hp] at h1
  omega

/-- **A half is not small**: it exceeds 3 and every prime factor of `m`. -/
theorem half_not_small {u : Eis} (hNu : u.norm = 1) (a : ℕ) {m : ℕ} (hm : Odd m)
    (h3 : ¬ 3 ∣ m) (hE : 3 ≤ 3 ^ a * m) :
    3 < ((cyclotomic m Eis).eval (u * tE ^ 3 ^ a)).norm ∧
      ∀ p : ℕ, p.Prime → p ∣ m →
        (p : ℤ) < ((cyclotomic m Eis).eval (u * tE ^ 3 ^ a)).norm := by
  have hNz : (u * tE ^ 3 ^ a).norm = 3 ^ 3 ^ a := by
    rw [map_mul, map_pow, hNu, norm_tE, one_mul]
  by_cases hm1 : m = 1
  · subst hm1
    have ha : 1 ≤ a := by
      by_contra h
      have : a = 0 := by omega
      subst this
      norm_num at hE
    have h27 : (27 : ℤ) ≤ (u * tE ^ 3 ^ a).norm := by
      rw [hNz]
      calc (27 : ℤ) = 3 ^ 3 ^ 1 := by norm_num
        _ ≤ 3 ^ 3 ^ a := pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_right (by norm_num) ha)
    rw [cyclotomic_one, eval_sub, eval_X, eval_one]
    refine ⟨three_lt_norm_sub_one h27, fun p hp hp1 => ?_⟩
    exact absurd (Nat.dvd_one.1 hp1) hp.ne_one
  · have hz3 : (3 : ℤ) ≤ (u * tE ^ 3 ^ a).norm := by
      rw [hNz]
      calc (3 : ℤ) = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ 3 ^ a := pow_le_pow_right₀ (by norm_num) (Nat.one_le_pow _ _ (by norm_num))
    have hlow := half_lower hz3 hm h3
    -- a prime factor of `m` is at least 5, so `φ(m) ≥ 4`
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hqm)
    have hq3 : q ≠ 3 := by
      rintro rfl
      exact h3 hqm
    have hq4 : q ≠ 4 := by
      rintro rfl
      exact absurd hq (by norm_num)
    have hq5 : 5 ≤ q := by have := hq.two_le; omega
    have hφ := prime_le_totient_succ hq hqm hm.pos
    have hφ4 : 4 ≤ m.totient := by omega
    have h9 := nine_mul_lt_three_pow hφ4
    have h9' : (9 : ℤ) * ((m.totient : ℤ) + 1) < 3 ^ m.totient := by exact_mod_cast h9
    have hbig : (m.totient : ℤ) + 1 < ((cyclotomic m Eis).eval (u * tE ^ 3 ^ a)).norm := by
      linarith
    refine ⟨by omega, fun p hp hpm => ?_⟩
    have hle := prime_le_totient_succ hp hpm hm.pos
    have hle' : (p : ℤ) ≤ (m.totient : ℤ) + 1 := by exact_mod_cast hle
    linarith

/-! ## 5. The two norms are `L_E` and `M_E` -/

/-- `N(ω t^E - 1)` and `N(ω² t^E - 1)` for `E = 2k + 1`. -/
theorem norm_w_tE (k : ℕ) :
    (wE * tE ^ (2 * k + 1) - 1).norm = 3 * 9 ^ k + 3 * (-3) ^ k + 1 ∧
      (wE ^ 2 * tE ^ (2 * k + 1) - 1).norm = 3 * 9 ^ k - 3 * (-3) ^ k + 1 := by
  have h9 : (9 : ℤ) ^ k = ((-3) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hpow : tE ^ (2 * k + 1) = (((-3 : ℤ) ^ k : ℤ) : Eis) * tE := by
    rw [pow_succ, pow_mul, tE_sq]
    push_cast
    rfl
  generalize (-3 : ℤ) ^ k = c at h9 hpow
  have e1 : wE * tE ^ (2 * k + 1) - 1 = ⟨-2 * c - 1, -c⟩ := by
    rw [hpow]
    ext <;> simp [wE, tE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> ring
  have e2 : wE ^ 2 * tE ^ (2 * k + 1) - 1 = ⟨c - 1, -c⟩ := by
    rw [hpow]
    ext <;> simp [wE, tE, sq, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    ring
  constructor
  · rw [e1, eis_norm_eq, h9]
    ring
  · rw [e2, eis_norm_eq, h9]
    ring

/-! ## 6. The theorem -/

/-- For odd `E ≥ 3` and `j ∈ {1, 2}`: `N(ω^j t^E - 1)` has a prime factor of order `6E`. -/
theorem half_primitive {E : ℕ} (hE : Odd E) (hE3 : 3 ≤ E) {j : ℕ} (hj : j = 1 ∨ j = 2) :
    ∃ p : ℕ, p.Prime ∧ orderOf (3 : ZMod p) = 6 * E ∧
      (p : ℤ) ∣ (wE ^ j * tE ^ E - 1).norm := by
  obtain ⟨a, m, h3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : E ≠ 0) 3 (by norm_num)
  have hm : Odd m := (Nat.odd_mul.1 hE).2
  have hm0 : 0 < m := hm.pos
  have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
  obtain ⟨i, hi, him⟩ : ∃ i, (i = 1 ∨ i = 2) ∧ (i * m) % 3 = j := by
    rcases hj with rfl | rfl <;> rcases hm3 with h | h
    · exact ⟨1, Or.inl rfl, by omega⟩
    · exact ⟨2, Or.inr rfl, by omega⟩
    · exact ⟨2, Or.inr rfl, by omega⟩
    · exact ⟨1, Or.inl rfl, by omega⟩
  obtain ⟨hu, hNu⟩ := wE_pow_facts hi
  have hzm : (wE ^ i * tE ^ 3 ^ a) ^ m = wE ^ j * tE ^ (3 ^ a * m) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, wE_pow_mod (i * m), him]
  have hdvd : ((cyclotomic m Eis).eval (wE ^ i * tE ^ 3 ^ a)).norm ∣
      (wE ^ j * tE ^ (3 ^ a * m) - 1).norm := by
    rw [← hzm]; exact norm_eval_cyclotomic_dvd3 _ hm0
  have hprod := half_mul_half hu hNu a hm h3
  obtain ⟨hbig, hprimes⟩ := half_not_small hNu a hm h3 hE3
  have h0 : 0 ≤ ((cyclotomic m Eis).eval (wE ^ i * tE ^ 3 ^ a)).norm := eis_norm_nonneg _
  obtain ⟨X, hXh⟩ : ∃ X : ℕ, (X : ℤ) = ((cyclotomic m Eis).eval (wE ^ i * tE ^ 3 ^ a)).norm :=
    ⟨_, Int.toNat_of_nonneg h0⟩
  rw [← hXh] at hdvd hprod hbig hprimes
  have hX : (X : ℤ) ∣ Phi6 (3 ^ a * m) := ⟨_, hprod.symm⟩
  have hX3 : 3 < X := by exact_mod_cast hbig
  obtain ⟨p, hp, hord, hpX⟩ := exists_primitive_of_dvd_Phi6 (by omega) hX (by omega) (by
    rintro ⟨hXp, hXd⟩
    rcases (Nat.Prime.dvd_mul hXp).1 hXd with h6 | hr
    · have h6le := Nat.le_of_dvd (by norm_num) h6
      interval_cases X
      · exact absurd hXp (by norm_num)
      · exact absurd h6 (by norm_num)
      · exact absurd hXp (by norm_num)
    · rcases (Nat.Prime.dvd_mul hXp).1 hr with h3a | hXm
      · have := Nat.le_of_dvd (by norm_num) (hXp.dvd_of_dvd_pow h3a)
        omega
      · exact lt_irrefl _ (hprimes X hXp hXm))
  exact ⟨p, hp, hord, (Int.natCast_dvd_natCast.2 hpX).trans hdvd⟩

/-- **Each Aurifeuillian factor of `3^(3E) + 1`, `E ≥ 3` odd, has a prime factor `p` with
`ord_p(3) = 6E`.** -/
theorem primitiveHalves3 : PrimitiveHalves3 := by
  intro k hk
  have hE : Odd (2 * k + 1) := odd_two_mul_add_one k
  obtain ⟨hn1, hn2⟩ := norm_w_tE k
  obtain ⟨p, hp, hpo, hpd⟩ := half_primitive hE (by omega) (j := 1) (Or.inl rfl)
  obtain ⟨q, hq, hqo, hqd⟩ := half_primitive hE (by omega) (j := 2) (Or.inr rfl)
  rw [pow_one, hn1] at hpd
  rw [hn2] at hqd
  have h3 : (3 : ℤ) ^ (2 * k + 1) = 3 * 9 ^ k := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rcases Nat.even_or_odd k with he | ho
  · have hs : (-3 : ℤ) ^ k = 3 ^ k := he.neg_pow 3
    rw [hs] at hpd hqd
    refine ⟨⟨q, hq, hqo, ?_⟩, ⟨p, hp, hpo, ?_⟩⟩
    · rw [h3, pow_succ]; convert hqd using 1; ring
    · rw [h3, pow_succ]; convert hpd using 1; ring
  · have hs : (-3 : ℤ) ^ k = -3 ^ k := ho.neg_pow 3
    rw [hs] at hpd hqd
    refine ⟨⟨p, hp, hpo, ?_⟩, ⟨q, hq, hqo, ?_⟩⟩
    · rw [h3, pow_succ]; convert hpd using 1; ring
    · rw [h3, pow_succ]; convert hqd using 1; ring

/-- Every root of unity outside the six exceptional ones has a good prime (no hypothesis). -/
theorem goodPrimes3 : GoodPrimes3 := goodPrimes3_of_halves primitiveHalves3

end Base3

end PiFormula
