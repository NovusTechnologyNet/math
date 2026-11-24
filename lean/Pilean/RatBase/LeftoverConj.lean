/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.RatBase.SmallDefs

/-!
# Conjugate pairs in a cyclotomic ring, and square roots as Gauss sums

Tools for the file `Leftover`. Let `ζ` be a primitive `N`-th root of unity and `a` prime to
`N`. The map `ζ ↦ ζ ^ a` is an automorphism of `ℤ[ζ]`; it is used here without being built.

* `ConjPair ζ a z w`: `z = G(ζ)` and `w = G(ζ ^ a)` for one `G ∈ ℤ[X]`. It is closed under the
  ring operations, contains `(ρ, ρ ^ a)` for every `ρ` with `ρ ^ N = 1` (`ConjPair.root`), and
  a prime ideal for `w` gives a prime ideal for `z` (`ConjPair.hasPrime`, from
  `Base3.hasPrime_conj`).
* `SqrtConj ζ a D ε`: some `s ∈ ℤ[ζ]` has `s² = D` and is sent to `ε s`. It is multiplicative
  in `(D, ε)` (`SqrtConj.mul`).
* The square roots, as Gauss sums: `√2 = η + η⁷` (`η` of order 8), `√-1 = η` (order 4),
  `√-3 = η - η²` (order 3), `√5 = η - η² - η³ + η⁴` (order 5),
  `√-7 = η + η² - η³ + η⁴ - η⁵ - η⁶` (order 7), and `√-11 = ∑ (k/11) η^k` (order 11). Each is
  fixed when `a ≡ 1` modulo the order (`sqrtConj_two`, `sqrtConj_neg_one`, `sqrtConj_neg_three`,
  `sqrtConj_neg_seven`, `sqrtConj_neg_eleven`); `√5` changes sign when `a ≡ 2 (mod 5)`
  (`sqrtConj_five_flip`) and `√-7` when `a ≡ 3 (mod 7)` (`sqrtConj_neg_seven_flip`).
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace RatBase

/-- `z` and `w` are the values at `ζ` and at `ζ ^ a` of one polynomial with integer
coefficients. -/
def ConjPair (ζ : ℂ) (a : ℕ) (z w : ℂ) : Prop :=
  ∃ G : ℤ[X], aeval ζ G = z ∧ aeval (ζ ^ a) G = w

namespace ConjPair

variable {ζ : ℂ} {a : ℕ} {z w z' w' : ℂ}

theorem intCast (ζ : ℂ) (a : ℕ) (c : ℤ) : ConjPair ζ a c c :=
  ⟨C c, by simp, by simp⟩

theorem add (h : ConjPair ζ a z w) (h' : ConjPair ζ a z' w') :
    ConjPair ζ a (z + z') (w + w') := by
  obtain ⟨G, rfl, rfl⟩ := h
  obtain ⟨G', rfl, rfl⟩ := h'
  exact ⟨G + G', map_add _ _ _, map_add _ _ _⟩

theorem mul (h : ConjPair ζ a z w) (h' : ConjPair ζ a z' w') :
    ConjPair ζ a (z * z') (w * w') := by
  obtain ⟨G, rfl, rfl⟩ := h
  obtain ⟨G', rfl, rfl⟩ := h'
  exact ⟨G * G', map_mul _ _ _, map_mul _ _ _⟩

theorem neg (h : ConjPair ζ a z w) : ConjPair ζ a (-z) (-w) := by
  obtain ⟨G, rfl, rfl⟩ := h
  exact ⟨-G, map_neg _ _, map_neg _ _⟩

theorem sub (h : ConjPair ζ a z w) (h' : ConjPair ζ a z' w') :
    ConjPair ζ a (z - z') (w - w') := by
  obtain ⟨G, rfl, rfl⟩ := h
  obtain ⟨G', rfl, rfl⟩ := h'
  exact ⟨G - G', map_sub _ _ _, map_sub _ _ _⟩

/-- The values of an integer polynomial at a conjugate pair are a conjugate pair. -/
theorem aeval (h : ConjPair ζ a z w) (g : ℤ[X]) :
    ConjPair ζ a (Polynomial.aeval z g) (Polynomial.aeval w g) := by
  obtain ⟨G, rfl, rfl⟩ := h
  exact ⟨g.comp G, aeval_comp _, aeval_comp _⟩

/-- A root of unity of order dividing `N` and its `a`-th power. -/
theorem root {N : ℕ} (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (a : ℕ) {ρ : ℂ}
    (hρ : ρ ^ N = 1) : ConjPair ζ a ρ (ρ ^ a) := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hρ
  refine ⟨X ^ k, by simp, ?_⟩
  rw [map_pow, aeval_X, ← pow_mul, ← pow_mul, mul_comm]

/-- **Conjugation.** For `a` prime to the order of `ζ`, a prime ideal containing `ℓ` and `w`
gives a prime ideal containing `ℓ` and `z`. -/
theorem hasPrime {N : ℕ} (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (ha : a.Coprime N) {ℓ : ℕ}
    (h : ConjPair ζ a z w) (hw : Base3.HasPrime ℓ w) : Base3.HasPrime ℓ z := by
  obtain ⟨G, rfl, rfl⟩ := h
  exact Base3.hasPrime_conj hN hζ G ha hw

end ConjPair

/-- Some `s ∈ ℤ[ζ]` with `s² = D` is sent to `ε s` by `ζ ↦ ζ ^ a`. -/
def SqrtConj (ζ : ℂ) (a : ℕ) (D ε : ℤ) : Prop :=
  ∃ s : ℂ, s ^ 2 = D ∧ ConjPair ζ a s (ε * s)

variable {ζ : ℂ} {a : ℕ}

theorem SqrtConj.mul {D₁ D₂ ε₁ ε₂ : ℤ} (h₁ : SqrtConj ζ a D₁ ε₁) (h₂ : SqrtConj ζ a D₂ ε₂) :
    SqrtConj ζ a (D₁ * D₂) (ε₁ * ε₂) := by
  obtain ⟨s₁, hs₁, hc₁⟩ := h₁
  obtain ⟨s₂, hs₂, hc₂⟩ := h₂
  refine ⟨s₁ * s₂, by rw [mul_pow, hs₁, hs₂, Int.cast_mul], ?_⟩
  have e : ((ε₁ * ε₂ : ℤ) : ℂ) * (s₁ * s₂) = (ε₁ : ℂ) * s₁ * ((ε₂ : ℂ) * s₂) := by
    push_cast
    ring
  rw [e]
  exact hc₁.mul hc₂

theorem SqrtConj.congr {D D' ε ε' : ℤ} (h : SqrtConj ζ a D ε) (hD : D = D') (hε : ε = ε') :
    SqrtConj ζ a D' ε' := by
  subst hD hε
  exact h

/-- The square root `c` of `c²`. -/
theorem sqrtConj_sq (ζ : ℂ) (a : ℕ) (c : ℤ) : SqrtConj ζ a (c ^ 2) 1 := by
  refine ⟨c, by rw [Int.cast_pow], ?_⟩
  rw [Int.cast_one, one_mul]
  exact ConjPair.intCast ζ a c

/-- `η ^ a = η ^ b` when `η ^ c = 1` and `a ≡ b (mod c)`. -/
theorem pow_eq_pow_of_mod {η : ℂ} {c a b : ℕ} (hη : η ^ c = 1) (ha : a % c = b) :
    η ^ a = η ^ b := by
  rw [← Nat.div_add_mod a c, ha, pow_add, pow_mul, hη, one_pow, one_mul]

/-- `η ^ a = η` when `η ^ c = 1` and `a ≡ 1 (mod c)`. -/
theorem pow_eq_self_of_mod {η : ℂ} {c a : ℕ} (hη : η ^ c = 1) (ha : a % c = 1) : η ^ a = η := by
  rw [pow_eq_pow_of_mod hη ha, pow_one]

/-- A square root given by an integer polynomial `g` in the roots of unity of order `c`,
`c ∣ N`. -/
theorem sqrtConj_of_poly {N : ℕ} (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) {c : ℕ} (hc : c ∣ N)
    (g : ℤ[X]) {D ε : ℤ} (a : ℕ) (hsq : ∀ η : ℂ, IsPrimitiveRoot η c → aeval η g ^ 2 = D)
    (hflip : ∀ η : ℂ, IsPrimitiveRoot η c → aeval (η ^ a) g = ε * aeval η g) :
    SqrtConj ζ a D ε := by
  obtain ⟨M, rfl⟩ := hc
  have hη : IsPrimitiveRoot (ζ ^ M) c := hζ.pow hN (mul_comm c M)
  have h1 : (ζ ^ M) ^ (c * M) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨aeval (ζ ^ M) g, hsq _ hη, ?_⟩
  rw [← hflip _ hη]
  exact (ConjPair.root hN hζ a h1).aeval g

/-- The same when `a ≡ 1 (mod c)`: the square root is fixed. -/
theorem sqrtConj_fix {N : ℕ} (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) {c : ℕ} (hc : c ∣ N)
    (g : ℤ[X]) {D : ℤ} {a : ℕ} (ha : a % c = 1)
    (hsq : ∀ η : ℂ, IsPrimitiveRoot η c → aeval η g ^ 2 = D) : SqrtConj ζ a D 1 :=
  sqrtConj_of_poly hN hζ hc g a hsq fun η hη => by
    rw [pow_eq_self_of_mod hη.pow_eq_one ha, Int.cast_one, one_mul]

/-! ## The square roots -/

section Roots

variable {N : ℕ}

/-- `(η + η⁷)² = 2` for `η` of order 8. -/
theorem sqrtConj_two (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (h8 : 8 ∣ N) (ha : a % 8 = 1) :
    SqrtConj ζ a 2 1 := by
  refine sqrtConj_fix hN hζ h8 (X + X ^ 7) ha fun η hη => ?_
  have h8 : η ^ 8 = 1 := hη.pow_eq_one
  have h4 : η ^ 4 + 1 = 0 := by
    have h : (η ^ 4 - 1) * (η ^ 4 + 1) = 0 := by linear_combination h8
    exact (mul_eq_zero.1 h).resolve_left
      (sub_ne_zero.2 (hη.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)))
  simp only [map_add, map_pow, aeval_X]
  push_cast
  linear_combination (η ^ 10 - η ^ 6 + 2 * η ^ 4 + η ^ 2 - 2) * h4

/-- `η² = -1` for `η` of order 4. -/
theorem sqrtConj_neg_one (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (h4 : 4 ∣ N)
    (ha : a % 4 = 1) : SqrtConj ζ a (-1) 1 := by
  refine sqrtConj_fix hN hζ h4 X ha fun η hη => ?_
  have h4 : η ^ 4 = 1 := hη.pow_eq_one
  have h2 : η ^ 2 + 1 = 0 := by
    have h : (η ^ 2 - 1) * (η ^ 2 + 1) = 0 := by linear_combination h4
    exact (mul_eq_zero.1 h).resolve_left
      (sub_ne_zero.2 (hη.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)))
  simp only [aeval_X]
  push_cast
  linear_combination h2

/-- `(η - η²)² = -3` for `η` of order 3. -/
theorem sqrtConj_neg_three (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (h3 : 3 ∣ N)
    (ha : a % 3 = 1) : SqrtConj ζ a (-3) 1 := by
  refine sqrtConj_fix hN hζ h3 (X - X ^ 2) ha fun η hη => ?_
  have h3 : η ^ 3 = 1 := hη.pow_eq_one
  have hs : η ^ 2 + η + 1 = 0 := by
    have h : (η - 1) * (η ^ 2 + η + 1) = 0 := by linear_combination h3
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 (hη.ne_one (by norm_num)))
  simp only [map_sub, map_pow, aeval_X]
  push_cast
  linear_combination (η ^ 2 - 3 * η + 3) * hs

/-- `(η - η² - η³ + η⁴)² = 5` for `η` of order 5, and `η ↦ η²` changes the sign. -/
theorem sqrtConj_five_flip (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (h5 : 5 ∣ N)
    (ha : a % 5 = 2) : SqrtConj ζ a 5 (-1) := by
  refine sqrtConj_of_poly hN hζ h5 (X - X ^ 2 - X ^ 3 + X ^ 4) a (fun η hη => ?_)
    (fun η hη => ?_)
  · simp only [map_add, map_sub, map_pow, aeval_X]
    push_cast
    exact Base5.gaussSum5_sq hη.pow_eq_one (hη.ne_one (by norm_num))
  · have h5 : η ^ 5 = 1 := hη.pow_eq_one
    rw [pow_eq_pow_of_mod h5 ha]
    simp only [map_add, map_sub, map_pow, aeval_X]
    push_cast
    linear_combination (η ^ 3 - η) * h5

/-- `(η + η² - η³ + η⁴ - η⁵ - η⁶)² = -7` for `η` of order 7. -/
theorem gaussSum7_sq {η : ℂ} (hη : IsPrimitiveRoot η 7) :
    (η + η ^ 2 - η ^ 3 + η ^ 4 - η ^ 5 - η ^ 6) ^ 2 = -7 := by
  have h7 : η ^ 7 = 1 := hη.pow_eq_one
  have hs : η ^ 6 + η ^ 5 + η ^ 4 + η ^ 3 + η ^ 2 + η + 1 = 0 := by
    have h : (η - 1) * (η ^ 6 + η ^ 5 + η ^ 4 + η ^ 3 + η ^ 2 + η + 1) = 0 := by
      linear_combination h7
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 (hη.ne_one (by norm_num)))
  linear_combination (η ^ 6 + η ^ 5 - 3 * η ^ 4 + η ^ 3 + η ^ 2 - 7 * η + 7) * hs

/-- `√-7` is fixed when `a ≡ 1 (mod 7)`. -/
theorem sqrtConj_neg_seven (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (h7 : 7 ∣ N)
    (ha : a % 7 = 1) : SqrtConj ζ a (-7) 1 := by
  refine sqrtConj_fix hN hζ h7 (X + X ^ 2 - X ^ 3 + X ^ 4 - X ^ 5 - X ^ 6) ha fun η hη => ?_
  simp only [map_add, map_sub, map_pow, aeval_X]
  push_cast
  exact gaussSum7_sq hη

/-- `√-7` changes sign when `a ≡ 3 (mod 7)`. -/
theorem sqrtConj_neg_seven_flip (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (h7 : 7 ∣ N)
    (ha : a % 7 = 3) : SqrtConj ζ a (-7) (-1) := by
  refine sqrtConj_of_poly hN hζ h7 (X + X ^ 2 - X ^ 3 + X ^ 4 - X ^ 5 - X ^ 6) a
    (fun η hη => ?_) (fun η hη => ?_)
  · simp only [map_add, map_sub, map_pow, aeval_X]
    push_cast
    exact gaussSum7_sq hη
  · have h7 : η ^ 7 = 1 := hη.pow_eq_one
    rw [pow_eq_pow_of_mod h7 ha]
    simp only [map_add, map_sub, map_pow, aeval_X]
    push_cast
    linear_combination (-η ^ 11 - η ^ 8 + η ^ 5 - η ^ 4 - η ^ 2 - η) * h7

/-- `(∑ (k/11) η^k)² = -11` for `η` of order 11; fixed when `a ≡ 1 (mod 11)`. -/
theorem sqrtConj_neg_eleven (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (h11 : 11 ∣ N)
    (ha : a % 11 = 1) : SqrtConj ζ a (-11) 1 := by
  refine sqrtConj_fix hN hζ h11
    (X - X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 - X ^ 6 - X ^ 7 - X ^ 8 + X ^ 9 - X ^ 10) ha
    fun η hη => ?_
  have h11 : η ^ 11 = 1 := hη.pow_eq_one
  have hs : η ^ 10 + η ^ 9 + η ^ 8 + η ^ 7 + η ^ 6 + η ^ 5 + η ^ 4 + η ^ 3 + η ^ 2 + η + 1
      = 0 := by
    have h : (η - 1) *
        (η ^ 10 + η ^ 9 + η ^ 8 + η ^ 7 + η ^ 6 + η ^ 5 + η ^ 4 + η ^ 3 + η ^ 2 + η + 1) = 0 := by
      linear_combination h11
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 (hη.ne_one (by norm_num)))
  simp only [map_add, map_sub, map_pow, aeval_X]
  push_cast
  linear_combination (η ^ 10 - 3 * η ^ 9 + 5 * η ^ 8 - 3 * η ^ 7 + η ^ 6 - 3 * η ^ 5 +
    5 * η ^ 4 - 3 * η ^ 3 + η ^ 2 - 11 * η + 11) * hs

end Roots

end RatBase

end PiFormula
