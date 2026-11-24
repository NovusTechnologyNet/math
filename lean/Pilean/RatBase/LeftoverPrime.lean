/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.RatBase.LeftoverConj

/-!
# Rational bases: a good prime from a primitive prime factor and a conjugation

`hasGoodPrimeR_of_primitive`: let `r` be a root of unity with `r²` of order `m`, and let `ℓ`
be a primitive prime factor of `p^m - q^m` (it divides `p^m - q^m` and no `p^d - q^d` with
`d ∣ m`, `d < m`), odd, dividing neither `p q` nor `2m`. Suppose that for some `N` divisible
by `2m` and some `a` prime to `N` with `a ≡ 1 (mod 2m)`, the map `ζ ↦ ζ ^ a` of the `N`-th
roots of unity changes the sign of a square root of `p q` (`SqrtConj ζ a (p q) (-1)`). Then
`r` has a good prime in the base `p/q`. No size condition is used.

The proof, with `u = √(pq)`.

1. `hasPrime_natCast_sub_mul_root`: `p^m - q^m = ∏_j (p - q ρ^j)` for `ρ = r²`, so a prime
   ideal above `ℓ` contains some `p - q ρ^j`. Then `ℓ` divides `p^d - q^d` for the order `d` of
   `ρ^j`, so `d = m`, `j` is prime to `m`, and `p - q ρ^j` is conjugate to `p - q ρ`
   (`Base3.hasPrime_conj`).
2. `(u - q r)(u + q r) = q (p - q r²)`: the prime ideal contains `u - q r` or `u + q r`.
3. In the second case, `ζ ↦ ζ ^ a` fixes `r` (because `a ≡ 1 (mod 2m)` and `r^(2m) = 1`) and
   sends `u` to `-u`: it sends `u - q r` to `-(u + q r)` (`ConjPair.hasPrime`).
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace RatBase

/-- **A prime ideal containing `p - q ρ`.** If the prime `ℓ` divides `p^m - q^m` and no
`p^d - q^d` with `d` a proper divisor of `m`, then for every primitive `m`-th root of unity `ρ`
some prime ideal contains `ℓ` and `p - q ρ`. -/
theorem hasPrime_natCast_sub_mul_root {p q m ℓ : ℕ} (hℓ : ℓ.Prime) (hqp : q ≤ p) (hm : 0 < m)
    (hdvd : ℓ ∣ p ^ m - q ^ m) (hnd : ∀ d, d < m → d ∣ m → ¬ ℓ ∣ p ^ d - q ^ d) {ρ : ℂ}
    (hρ : IsPrimitiveRoot ρ m) : Base3.HasPrime ℓ ((p : ℂ) - (q : ℂ) * ρ) := by
  classical
  obtain ⟨Q, hQ, hℓQ⟩ := exists_prime_above hℓ
  have hρi : IsIntegral ℤ ρ := hρ.isIntegral hm
  have hpi := isIntegral_natCast' p
  have hqi := isIntegral_natCast' q
  have hcast : ∀ d : ℕ, ((p ^ d - q ^ d : ℕ) : ℂ) = (p : ℂ) ^ d - (q : ℂ) ^ d := by
    intro d
    rw [Nat.cast_sub (Nat.pow_le_pow_left hqp d)]
    push_cast
    rfl
  -- `p^m - q^m ∈ Q`
  have h1 : InP Q ((p : ℂ) ^ m - (q : ℂ) ^ m) := by
    obtain ⟨k, hk⟩ := hdvd
    rw [← hcast, hk]
    push_cast
    exact hℓQ.mul_right (isIntegral_natCast' k)
  -- `p^m - q^m = ∏ (p - ρ^j q)`
  have hprod : (p : ℂ) ^ m - (q : ℂ) ^ m = ∏ j ∈ Finset.range m, ((p : ℂ) - ρ ^ j * q) := by
    have h := Base3.prod_sub_nthRoots hm ((q : ℂ) ^ m) (p : ℂ)
    rw [hρ.nthRoots_eq rfl, Multiset.map_map] at h
    exact h.symm
  rw [hprod] at h1
  obtain ⟨j, -, hjQ⟩ := inP_prod (Finset.range m) _
    (fun j _ => hpi.sub ((hρi.pow j).mul hqi)) h1
  -- `ρ^j` has order `m`
  have hj2 : orderOf (ρ ^ j) ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_comm, pow_mul, hρ.pow_eq_one, one_pow]
  have hjm : orderOf (ρ ^ j) = m := by
    by_contra hne
    have hlt : orderOf (ρ ^ j) < m := lt_of_le_of_ne (Nat.le_of_dvd hm hj2) hne
    apply hnd _ hlt hj2
    by_contra hndvd
    refine not_inP_coprime ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hndvd).symm ?_ hℓQ
    rw [hcast]
    have e := (Commute.all (p : ℂ) (ρ ^ j * q)).mul_geom_sum₂ (orderOf (ρ ^ j))
    rw [mul_pow, pow_orderOf_eq_one, one_mul] at e
    rw [← e]
    exact hjQ.mul_right (IsIntegral.sum _ fun i _ =>
      (hpi.pow _).mul (((hρi.pow j).mul hqi).pow _))
  have hcop : j.Coprime m := by
    have h : IsPrimitiveRoot (ρ ^ j) m := hjm ▸ IsPrimitiveRoot.orderOf (ρ ^ j)
    exact (hρ.pow_iff_coprime hm j).1 h
  -- conjugate `p - q ρ^j` to `p - q ρ`
  let F : ℤ[X] := C (p : ℤ) - C (q : ℤ) * X
  have hF : ∀ z : ℂ, aeval z F = (p : ℂ) - (q : ℂ) * z := fun z => by simp [F]
  rw [← hF ρ]
  refine Base3.hasPrime_conj hm hρ F hcop ?_
  rw [hF]
  exact ⟨Q, hQ, hℓQ, by rwa [mul_comm]⟩

/-- **A good prime from a primitive prime factor and a conjugation.** -/
theorem hasGoodPrimeR_of_primitive {p q m ℓ N a : ℕ} (hqp : q ≤ p) (hm : 0 < m)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓpq : ¬ ℓ ∣ p * q) (hℓm : ¬ ℓ ∣ 2 * m)
    (hdvd : ℓ ∣ p ^ m - q ^ m) (hnd : ∀ d, d < m → d ∣ m → ¬ ℓ ∣ p ^ d - q ^ d)
    (hN : 0 < N) (hmN : 2 * m ∣ N) (ha : a.Coprime N) (ha1 : a % (2 * m) = 1)
    (hS : ∀ ζ : ℂ, IsPrimitiveRoot ζ N → SqrtConj ζ a ((p * q : ℕ) : ℤ) (-1))
    {r : ℂ} (hr : IsOfFinOrder r) (hord : orderOf (r ^ 2) = m) : HasGoodPrimeR p q r := by
  have hri := isIntegral_of_finOrder hr
  have hui := BaseB.isIntegral_tB (p * q)
  have hqi := isIntegral_natCast' q
  have hr2m : r ^ (2 * m) = 1 := by rw [pow_mul, ← hord, pow_orderOf_eq_one]
  have hρ : IsPrimitiveRoot (r ^ 2) m := hord ▸ IsPrimitiveRoot.orderOf (r ^ 2)
  obtain ⟨Q, hQ, hℓQ, hx⟩ := hasPrime_natCast_sub_mul_root hℓ hqp hm hdvd hnd hρ
  have hu2 : BaseB.tB (p * q) ^ 2 = (p : ℂ) * q := by
    rw [BaseB.tB_sq]
    push_cast
    ring
  obtain ⟨u, hu⟩ : ∃ u : ℂ, BaseB.tB (p * q) = u := ⟨_, rfl⟩
  rw [hu] at hui hu2
  -- the prime ideal contains `u - q r` or `u + q r`
  have hsplit : InP Q (u - (q : ℂ) * r) ∨ InP Q (u + (q : ℂ) * r) := by
    apply inP_mul (hui.sub (hqi.mul hri)) (hui.add (hqi.mul hri))
    have e : (u - (q : ℂ) * r) * (u + (q : ℂ) * r) = (q : ℂ) * ((p : ℂ) - (q : ℂ) * r ^ 2) := by
      linear_combination hu2
    rw [e]
    exact hx.mul_left hqi
  have hfin : Base3.HasPrime ℓ (u - (q : ℂ) * r) := by
    rcases hsplit with h | h
    · exact ⟨Q, hQ, hℓQ, h⟩
    · -- the conjugation `ζ ↦ ζ ^ a` fixes `r` and changes the sign of `u`
      have hζ := zetaN_prim hN
      obtain ⟨s, hs, hc⟩ := hS _ hζ
      have hrN : r ^ N = 1 := by
        obtain ⟨k, rfl⟩ := hmN
        rw [pow_mul, hr2m, one_pow]
      have hra : r ^ a = r := pow_eq_self_of_mod hr2m ha1
      have hcr : ConjPair (zetaN N) a ((q : ℂ) * r) ((q : ℂ) * r) := by
        have h1 := (ConjPair.intCast (zetaN N) a (q : ℤ)).mul (ConjPair.root hN hζ a hrN)
        rw [hra] at h1
        simpa using h1
      have hneg : Base3.HasPrime ℓ (-u - (q : ℂ) * r) := by
        refine ⟨Q, hQ, hℓQ, ?_⟩
        have h2 := h.neg
        rwa [neg_add, ← sub_eq_add_neg] at h2
      have hs' : (s - u) * (s + u) = 0 := by
        push_cast at hs
        linear_combination hs - hu2
      rcases mul_eq_zero.1 hs' with h0 | h0
      · -- `s = u`
        obtain rfl : s = u := sub_eq_zero.1 h0
        have h2 := hc.sub hcr
        refine h2.hasPrime hN hζ ha ?_
        have e : ((-1 : ℤ) : ℂ) * s - (q : ℂ) * r = -s - (q : ℂ) * r := by
          push_cast
          ring
        rw [e]
        exact hneg
      · -- `s = -u`
        obtain rfl : s = -u := eq_neg_of_add_eq_zero_left h0
        have h2 := hc.neg.sub hcr
        have e1 : -(-u) - (q : ℂ) * r = u - (q : ℂ) * r := by ring
        have e2 : -(((-1 : ℤ) : ℂ) * -u) - (q : ℂ) * r = -u - (q : ℂ) * r := by
          push_cast
          ring
        rw [e1, e2] at h2
        exact h2.hasPrime hN hζ ha hneg
  obtain ⟨Q', hQ', hℓQ', hx'⟩ := hfin
  refine ⟨Q', hQ', ℓ, hℓ, hℓ2, hℓpq, ?_, hℓQ', ?_⟩
  · intro hd
    exact hℓm (hd.trans (orderOf_dvd_of_pow_eq_one hr2m))
  · rw [hu]
    exact hx'

end RatBase

end PiFormula
