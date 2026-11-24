/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Base5.Zeta5

/-!
# Base 5: each Aurifeuillian factor of `Φ_5(5^h)` has a primitive prime

For odd `h` put `L_h, M_h = 5^(2h) + 3·5^h + 1 ∓ 5^((h+1)/2) (5^h + 1)`, so that
`L_h M_h = 5^(4h) + 5^(3h) + 5^(2h) + 5^h + 1`. This file proves `PrimitiveHalves5`: each of
`L_h`, `M_h` has a prime factor `p` with `ord_p(5) = 5h`. It is the analogue for base 5 of
`Base3/Halves.lean`.

The proof works in `ℤ[ζ]`, `ζ` a primitive fifth root of unity (`Base5/Zeta5.lean`), which
contains `t = √5`. The norm `N` to `ℤ` is taken in two steps, through `ℤ[φ]`. Write
`h = 5^a m` with `5 ∤ m`, `T = t^(5^a)`, and for a primitive fifth root of unity `u` let
`H_u = N(Φ_m(u T))`.

1. `H_u H_{u²} = Φ_{5h}(5)` (`half_mul_half5`). Indeed `N(Φ_{5m}(T)) = Φ_{5h}(5)²`, because
   `Φ_{5m}(T) Φ_{5m}(-T) = Φ_{5m}(T²) = Φ_{5m}(5^(5^a)) = Φ_{5h}(5)`; and
   `N(Φ_{5m}(x)) = ∏_{j=1}^{4} N(Φ_m(u^j x))` (`norm_cyclotomic_mul_five`), where conjugation
   pairs `j` with `5 - j`.
2. `H_u` divides `N((uT)^m - 1) = N(u^m t^h - 1)`, and `N(ζ t^h - 1) = L_h`,
   `N(ζ² t^h - 1) = M_h` (`norm_z_th`).
3. `25 H_u ≥ 25^φ(m)` (`half_lower5`), from the Möbius product formula: each factor
   `N(z^b - 1)` lies between `(s^b - 1)⁴` and `(s^b + 1)⁴`, where `s = (√5)^(5^a)`.
4. A divisor of `Φ_{5h}(5)` that is not `1` and not a prime factor of `5h` has a prime factor
   of order `5h` (`exists_primitive_of_dvd_Phi5`, from the Tau Ceti library).

For `h = 1` the two factors are the primes 11 and 71.
-/

@[expose] public section

open Polynomial

namespace PiFormula

namespace Base5

/-! ## 1. The reduction -/

theorem homogeneous_eq_Phi5 (h : ℕ) :
    TauCeti.homogeneousCyclotomic (5 * h) ((5 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = Phi5 h := by
  rw [Nat.cast_ofNat, Nat.cast_one, TauCeti.homogeneousCyclotomic_one_right]
  rfl

/-- A prime of `Φ_{5h}(5)` whose order is not `5h` divides `5h`, is at least every prime factor
of `5h`, and divides `Φ_{5h}(5)` exactly once. -/
theorem nonprimitive5 {h p : ℕ} (hh : 0 < h) (hp : p.Prime) (hdvd : (p : ℤ) ∣ Phi5 h)
    (hord : orderOf (5 : ZMod p) ≠ 5 * h) :
    p ∣ 5 * h ∧ (∀ q : ℕ, q.Prime → q ∣ 5 * h → q ≤ p) ∧ multiplicity (p : ℤ) (Phi5 h) = 1 := by
  have hdvd' := (homogeneous_eq_Phi5 h).symm ▸ hdvd
  have hb : ¬ (p : ℤ) ∣ ((1 : ℕ) : ℤ) := by
    norm_cast; exact hp.not_dvd_one
  have hiff0 := (hp.dvd_homogeneousCyclotomic_iff_orderOf_eq hb (by omega : 5 * h ≠ 0)).1 hdvd'
  have hiff : orderOf (5 : ZMod p) = ordCompl[p] (5 * h) := by simpa using hiff0
  have hk0 : 0 < orderOf (5 : ZMod p) := hiff ▸ Nat.ordCompl_pos p (by omega)
  have hk4 : orderOf (5 : ZMod p) < 5 * h := lt_of_le_of_ne (hiff ▸ Nat.ordCompl_le _ _) hord
  have hpk : p ∣ 5 ^ orderOf (5 : ZMod p) - 1 ^ orderOf (5 : ZMod p) := by
    rw [one_pow, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)),
      Nat.cast_pow, Nat.cast_ofNat, pow_orderOf_eq_one, Nat.cast_one, sub_self]
  obtain ⟨hpn, hle, hmul⟩ := hp.multiplicity_homogeneousCyclotomic_of_not_primitive
    (by norm_num : Nat.Coprime 5 1) (by norm_num) (by omega : 5 * h ≠ 2) hdvd'
    ⟨_, hk0, hk4, hpk⟩
  exact ⟨hpn, hle, (homogeneous_eq_Phi5 h) ▸ hmul⟩

/-- **The reduction.** A divisor of `Φ_{5h}(5)` that is not `1` and not a prime factor of `5h`
has a prime factor of order `5h`. -/
theorem exists_primitive_of_dvd_Phi5 {h X : ℕ} (hh : 0 < h) (hX : (X : ℤ) ∣ Phi5 h)
    (hX1 : X ≠ 1) (hXp : ¬ (X.Prime ∧ X ∣ 5 * h)) :
    ∃ p, p.Prime ∧ orderOf (5 : ZMod p) = 5 * h ∧ p ∣ X := by
  by_contra hno
  push Not at hno
  have key : ∀ p, p.Prime → p ∣ X → p ∣ 5 * h ∧ (∀ q : ℕ, q.Prime → q ∣ 5 * h → q ≤ p) ∧
      multiplicity (p : ℤ) (Phi5 h) = 1 := fun p hp hpX =>
    nonprimitive5 hh hp ((Int.natCast_dvd_natCast.2 hpX).trans hX) (fun h => hno p hp h hpX)
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
  have hsq : ((p₀ : ℤ) ^ 2) ∣ Phi5 h := by
    have h1 : p₀ ^ 2 ∣ p₀ * Y := by rw [sq]; exact Nat.mul_dvd_mul_left _ hp₁Y
    have h2 := (Int.natCast_dvd_natCast.2 h1).trans hX
    simpa using h2
  have hfin : FiniteMultiplicity (p₀ : ℤ) (Phi5 h) :=
    FiniteMultiplicity.of_prime_left (Nat.prime_iff_prime_int.1 hp₀) (Phi5_pos hh).ne'
  exact hfin.not_pow_dvd_of_multiplicity_lt (by rw [k₀.2.2]; norm_num) hsq

/-! ## 2. The theorem -/

/-- For odd `h ≥ 3` and `j ∈ {1, 2}`: `N(ζ^j t^h - 1)` has a prime factor of order `5h`. -/
theorem half_primitive5 {h : ℕ} (hh : Odd h) (hh3 : 3 ≤ h) {j : ℕ} (hj : j = 1 ∨ j = 2) :
    ∃ p : ℕ, p.Prime ∧ orderOf (5 : ZMod p) = 5 * h ∧
      (p : ℤ) ∣ N5 (zS ^ j * tS ^ h - 1) := by
  obtain ⟨a, m, h5, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : h ≠ 0) 5 (by norm_num)
  have hm : Odd m := (Nat.odd_mul.1 hh).2
  have hm0 : 0 < m := hm.pos
  have hm5 : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
  -- choose `i` with `i m ≡ j (mod 5)`
  obtain ⟨i, hi, him⟩ : ∃ i, ¬ 5 ∣ i ∧ (i * m) % 5 = j := by
    rcases hj with rfl | rfl <;> rcases hm5 with h | h | h | h
    · exact ⟨1, by norm_num, by omega⟩
    · exact ⟨3, by norm_num, by omega⟩
    · exact ⟨2, by norm_num, by omega⟩
    · exact ⟨4, by norm_num, by omega⟩
    · exact ⟨2, by norm_num, by omega⟩
    · exact ⟨1, by norm_num, by omega⟩
    · exact ⟨4, by norm_num, by omega⟩
    · exact ⟨3, by norm_num, by omega⟩
  obtain ⟨hu, hNu⟩ := zS_pow_facts hi
  have hzm : (zS ^ i * tS ^ 5 ^ a) ^ m = zS ^ j * tS ^ (5 ^ a * m) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, pow_mod_five zS_rel (i * m), him]
  have hdvd : N5 ((cyclotomic m Cyc5).eval (zS ^ i * tS ^ 5 ^ a)) ∣
      N5 (zS ^ j * tS ^ (5 ^ a * m) - 1) := by
    rw [← hzm]; exact norm_eval_cyclotomic_dvd5 _ hm0
  have hprod := half_mul_half5 hu hNu a hm h5
  obtain ⟨hbig, hprimes⟩ := half_not_small5 hNu a hm hh3
  have h0 : 0 ≤ N5 ((cyclotomic m Cyc5).eval (zS ^ i * tS ^ 5 ^ a)) := by linarith
  obtain ⟨X, hXh⟩ : ∃ X : ℕ, (X : ℤ) = N5 ((cyclotomic m Cyc5).eval (zS ^ i * tS ^ 5 ^ a)) :=
    ⟨_, Int.toNat_of_nonneg h0⟩
  rw [← hXh] at hdvd hprod hbig hprimes
  have hX : (X : ℤ) ∣ Phi5 (5 ^ a * m) := ⟨_, hprod.symm⟩
  have hX5 : 5 < X := by exact_mod_cast hbig
  obtain ⟨p, hp, hord, hpX⟩ := exists_primitive_of_dvd_Phi5 (by omega) hX (by omega) (by
    rintro ⟨hXp, hXd⟩
    rcases (Nat.Prime.dvd_mul hXp).1 hXd with h5' | hr
    · have := Nat.le_of_dvd (by norm_num) h5'
      omega
    · rcases (Nat.Prime.dvd_mul hXp).1 hr with h5a | hXm
      · have := Nat.le_of_dvd (by norm_num) (hXp.dvd_of_dvd_pow h5a)
        omega
      · exact lt_irrefl _ (hprimes X hXp hXm))
  exact ⟨p, hp, hord, (Int.natCast_dvd_natCast.2 hpX).trans hdvd⟩

theorem orderOf_five_zmod_11 : orderOf (5 : ZMod 11) = 5 * 1 := by
  rw [orderOf_eq_iff (by norm_num)]; exact ⟨by decide, by decide⟩

theorem orderOf_five_zmod_71 : orderOf (5 : ZMod 71) = 5 * 1 := by
  rw [orderOf_eq_iff (by norm_num)]; exact ⟨by decide, by decide⟩

/-- **Each Aurifeuillian factor `L_h`, `M_h` of `Φ_5(5^h)`, `h` odd, has a prime factor `p`
with `ord_p(5) = 5h`.** -/
theorem primitiveHalves5 : PrimitiveHalves5 := by
  intro h hh
  by_cases h1 : h = 1
  · subst h1
    exact ⟨⟨11, by norm_num, orderOf_five_zmod_11, by rw [L5_one]; norm_num⟩,
      ⟨71, by norm_num, orderOf_five_zmod_71, by rw [M5_one]; norm_num⟩⟩
  obtain ⟨k, rfl⟩ := hh
  have h3 : 3 ≤ 2 * k + 1 := by omega
  obtain ⟨hn1, hn2⟩ := norm_z_th k
  obtain ⟨p, hp, hpo, hpd⟩ :=
    half_primitive5 (odd_two_mul_add_one k) h3 (j := 1) (Or.inl rfl)
  obtain ⟨q, hq, hqo, hqd⟩ :=
    half_primitive5 (odd_two_mul_add_one k) h3 (j := 2) (Or.inr rfl)
  rw [pow_one, hn1] at hpd
  rw [hn2] at hqd
  exact ⟨⟨p, hp, hpo, hpd⟩, ⟨q, hq, hqo, hqd⟩⟩

end Base5

end PiFormula
