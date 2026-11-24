/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.BaseB.Symmetrize

/-!
# A general base `b`: the value `Φ_n(√b) Φ_n(-√b)`

Let `r` be a root of unity with `r⁴ ≠ 1`, of order `n`, and let `m ≥ 3` be the order of `r²`
(so `n = m` with `m` odd, or `n = 2m`). With `t = √b`, `cyclo_data` says that

`Φ_n(t) Φ_n(-t) = Φ_m(b)^k` and `φ(n) = k φ(m)`,

where `k = 2` if `4 ∣ n` and `k = 1` otherwise (only `k ≥ 1` is recorded). The three cases:

* `n = m` odd: `Φ_m(X) Φ_m(-X) = Φ_m(X²)` (`aeval_cyclotomic_mul_neg`);
* `n = 2m`, `m` odd: `Φ_{2m}(X) = Φ_m(-X)`, and the same identity;
* `n = 2m`, `m` even: `Φ_{2m}(X) = Φ_m(X²)`.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-- `Φ_k(s) Φ_k(-s) = Φ_k(s²)` for odd `k > 1`. -/
theorem aeval_cyclotomic_mul_neg {k : ℕ} (hk : Odd k) (h1 : 1 < k) (s : ℂ) :
    aeval s (cyclotomic k ℤ) * aeval (-s) (cyclotomic k ℤ) =
      aeval (s ^ 2) (cyclotomic k ℤ) := by
  have e := cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two hk.not_two_dvd_nat ℤ
  rw [mul_comm k 2, cyclotomic_two_mul_of_odd hk h1 ℤ] at e
  have h := congrArg (aeval s) e
  rw [expand_aeval, map_mul, aeval_comp, map_neg, aeval_X] at h
  rw [h]
  ring

/-- `Φ_{2k}(s) = Φ_k(-s)` for odd `k > 1`. -/
theorem aeval_cyclotomic_two_mul_of_odd {k : ℕ} (hk : Odd k) (h1 : 1 < k) (s : ℂ) :
    aeval s (cyclotomic (2 * k) ℤ) = aeval (-s) (cyclotomic k ℤ) := by
  rw [cyclotomic_two_mul_of_odd hk h1 ℤ, aeval_comp, map_neg, aeval_X]

/-- `Φ_{2k}(s) = Φ_k(s²)` for even `k`. -/
theorem aeval_cyclotomic_two_mul_of_even {k : ℕ} (hk : 2 ∣ k) (s : ℂ) :
    aeval s (cyclotomic (2 * k) ℤ) = aeval (s ^ 2) (cyclotomic k ℤ) := by
  rw [mul_comm 2 k, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two hk ℤ, expand_aeval]

/-- The order `m` of `r²` is at least 3 when `r⁴ ≠ 1`, and the order of `r` is `m` (with `m`
odd) or `2m`. -/
theorem orderOf_sq_cases {r : ℂ} (hr : IsOfFinOrder r) (h4 : r ^ 4 ≠ 1) :
    3 ≤ orderOf (r ^ 2) ∧ ((orderOf r = orderOf (r ^ 2) ∧ Odd (orderOf (r ^ 2))) ∨
      orderOf r = 2 * orderOf (r ^ 2)) := by
  have hm0 : 0 < orderOf (r ^ 2) := (hr.pow (n := 2)).orderOf_pos
  have hm1 : orderOf (r ^ 2) ≠ 1 := by
    intro h
    have h2 : r ^ 2 = 1 := orderOf_eq_one_iff.1 h
    exact h4 (by rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, h2, one_pow])
  have hm2 : orderOf (r ^ 2) ≠ 2 := by
    intro h
    have h2 := pow_orderOf_eq_one (r ^ 2)
    rw [h] at h2
    exact h4 (by rw [← h2]; ring)
  refine ⟨by omega, ?_⟩
  have hm : orderOf (r ^ 2) = orderOf r / Nat.gcd (orderOf r) 2 :=
    orderOf_pow' r (by norm_num)
  rcases Nat.even_or_odd (orderOf r) with he | ho
  · right
    have h2 : 2 ∣ orderOf r := even_iff_two_dvd.1 he
    rw [Nat.gcd_eq_right h2] at hm
    rw [hm, Nat.mul_div_cancel' h2]
  · left
    rw [Nat.coprime_two_right.2 ho, Nat.div_one] at hm
    exact ⟨hm.symm, hm ▸ ho⟩

/-- `Φ_m(t²)`, `t = √b`, is the integer `Φ_m(b)`. -/
theorem aeval_tB_sq_cyclotomic (b m : ℕ) :
    aeval (tB b ^ 2) (cyclotomic m ℤ) = (((cyclotomic m ℤ).eval (b : ℤ) : ℤ) : ℂ) := by
  have h := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (b : ℤ) (cyclotomic m ℤ)
  rw [tB_sq]
  simpa using h

/-- **The value `Φ_n(t) Φ_n(-t)`.** For a root of unity `r` with `r⁴ ≠ 1`, of order `n`, with
`m` the order of `r²`: `m ≥ 3`, `n ∣ 2m`, and for some `k ≥ 1`, `φ(n) = k φ(m)` and
`Φ_n(t) Φ_n(-t) = Φ_m(b)^k`. -/
theorem cyclo_data (b : ℕ) {r : ℂ} (hr : IsOfFinOrder r) (h4 : r ^ 4 ≠ 1) :
    3 ≤ orderOf (r ^ 2) ∧ orderOf r ∣ 2 * orderOf (r ^ 2) ∧ ∃ k : ℕ, 0 < k ∧
      (orderOf r).totient = k * (orderOf (r ^ 2)).totient ∧
      aeval (tB b) (cyclotomic (orderOf r) ℤ) * aeval (-tB b) (cyclotomic (orderOf r) ℤ) =
        (((cyclotomic (orderOf (r ^ 2)) ℤ).eval (b : ℤ) : ℤ) : ℂ) ^ k := by
  obtain ⟨hm3, hcases⟩ := orderOf_sq_cases hr h4
  obtain ⟨m, hm⟩ : ∃ m, orderOf (r ^ 2) = m := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, orderOf r = n := ⟨_, rfl⟩
  rw [hm, hn] at hcases
  rw [hm] at hm3
  rw [hm, hn]
  refine ⟨hm3, ?_, ?_⟩
  · rcases hcases with ⟨h, -⟩ | h
    · exact h ▸ dvd_mul_left m 2
    · exact h ▸ dvd_rfl
  rcases hcases with ⟨h, hodd⟩ | h
  · -- `n = m` odd
    refine ⟨1, one_pos, by rw [h, one_mul], ?_⟩
    rw [h, pow_one, aeval_cyclotomic_mul_neg hodd (by omega), aeval_tB_sq_cyclotomic]
  · rcases Nat.even_or_odd m with heven | hodd
    · -- `n = 2m`, `m` even
      have h2 : 2 ∣ m := even_iff_two_dvd.1 heven
      refine ⟨2, by norm_num, by rw [h, Nat.totient_mul_of_dvd h2], ?_⟩
      rw [h, aeval_cyclotomic_two_mul_of_even h2, aeval_cyclotomic_two_mul_of_even h2, neg_sq,
        aeval_tB_sq_cyclotomic, sq]
    · -- `n = 2m`, `m` odd
      refine ⟨1, one_pos, by rw [h, Nat.totient_two_mul_of_odd hodd, one_mul], ?_⟩
      rw [h, pow_one, aeval_cyclotomic_two_mul_of_odd hodd (by omega),
        aeval_cyclotomic_two_mul_of_odd hodd (by omega), neg_neg, mul_comm,
        aeval_cyclotomic_mul_neg hodd (by omega), aeval_tB_sq_cyclotomic]

end BaseB

end PiFormula
