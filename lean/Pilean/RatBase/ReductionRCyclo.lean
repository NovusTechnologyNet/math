import Pilean.RatBase.SymmetrizeR

/-!
# Rational bases: the value `Ψ(u) Ψ(-u) = q^φ(n) Φ_m(p, q)^k`

Let `r` be a root of unity with `r⁴ ≠ 1`, of order `n`, and let `m ≥ 3` be the order of `r²`.

* `cyclo_dataR`: `Φ_n(s) Φ_n(-s) = Φ_m(s²)^k` for every complex `s`, with `φ(n) = k φ(m)` and
  `k ≥ 1` (the statement `BaseB.cyclo_data` at a general point, by the same three cases).
* `cycloScaled_value`: with `u = √(pq)` and `Ψ(Y) = q^φ(n) Φ_n(Y / q)` (`cycloScaled q n`),

  `Ψ(u) Ψ(-u) = q^φ(n) Φ_m(p, q)^k`,

  where `Φ_m(p, q)` is the homogeneous cyclotomic value `cycValR p q m`. Indeed
  `Ψ(±u) = q^φ(n) Φ_n(±u/q)`, `(u/q)² = p/q` and `Φ_m(p/q) q^φ(m) = Φ_m(p, q)`.
-/

open Complex Polynomial

namespace PiFormula

namespace RatBase

/-- **The identity `Φ_n(s) Φ_n(-s) = Φ_m(s²)^k`.** For a root of unity `r` with `r⁴ ≠ 1`, of
order `n`, with `m` the order of `r²`: `m ≥ 3`, `n ∣ 2m`, and for some `k ≥ 1`,
`φ(n) = k φ(m)` and `Φ_n(s) Φ_n(-s) = Φ_m(s²)^k` for every complex `s`. -/
theorem cyclo_dataR {r : ℂ} (hr : IsOfFinOrder r) (h4 : r ^ 4 ≠ 1) :
    3 ≤ orderOf (r ^ 2) ∧ orderOf r ∣ 2 * orderOf (r ^ 2) ∧ ∃ k : ℕ, 0 < k ∧
      (orderOf r).totient = k * (orderOf (r ^ 2)).totient ∧
      ∀ s : ℂ, aeval s (cyclotomic (orderOf r) ℤ) * aeval (-s) (cyclotomic (orderOf r) ℤ) =
        aeval (s ^ 2) (cyclotomic (orderOf (r ^ 2)) ℤ) ^ k := by
  obtain ⟨hm3, hcases⟩ := BaseB.orderOf_sq_cases hr h4
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
    refine ⟨1, one_pos, by rw [h, one_mul], fun s => ?_⟩
    rw [h, pow_one, BaseB.aeval_cyclotomic_mul_neg hodd (by omega)]
  · rcases Nat.even_or_odd m with heven | hodd
    · -- `n = 2m`, `m` even
      have h2 : 2 ∣ m := even_iff_two_dvd.1 heven
      refine ⟨2, by norm_num, by rw [h, Nat.totient_mul_of_dvd h2], fun s => ?_⟩
      rw [h, BaseB.aeval_cyclotomic_two_mul_of_even h2,
        BaseB.aeval_cyclotomic_two_mul_of_even h2, neg_sq]
      exact (sq _).symm
    · -- `n = 2m`, `m` odd
      refine ⟨1, one_pos, by rw [h, Nat.totient_two_mul_of_odd hodd, one_mul], fun s => ?_⟩
      rw [h, pow_one, BaseB.aeval_cyclotomic_two_mul_of_odd hodd (by omega),
        BaseB.aeval_cyclotomic_two_mul_of_odd hodd (by omega), neg_neg, mul_comm,
        BaseB.aeval_cyclotomic_mul_neg hodd (by omega)]

/-- `Φ_m(p/q) q^φ(m)` is the integer `Φ_m(p, q)`. -/
private theorem aeval_div_cyclotomic_mul_pow {q : ℕ} (hq : 0 < q) (p m : ℕ) :
    aeval ((p : ℂ) / q) (cyclotomic m ℤ) * (q : ℂ) ^ m.totient = ((cycValR p q m : ℤ) : ℂ) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  rw [cycValR, Int.cast_homogeneousCyclotomic, Int.cast_natCast, Int.cast_natCast,
    TauCeti.homogeneousCyclotomic_eq_eval_div_mul_pow _ _ hq0, aeval_def, eval₂_eq_eval_map,
    map_cyclotomic]

/-- **The value `Ψ(u) Ψ(-u)`.** For a root of unity `r` with `r⁴ ≠ 1`, of order `n`, with `m`
the order of `r²`: `m ≥ 3`, `n ∣ 2m`, and for some `k ≥ 1`, `φ(n) = k φ(m)` and
`Ψ(u) Ψ(-u) = q^φ(n) Φ_m(p, q)^k`, where `u = √(pq)` and `Ψ = cycloScaled q n`. -/
theorem cycloScaled_value (p : ℕ) {q : ℕ} (hq : 0 < q) {r : ℂ} (hr : IsOfFinOrder r)
    (h4 : r ^ 4 ≠ 1) :
    3 ≤ orderOf (r ^ 2) ∧ orderOf r ∣ 2 * orderOf (r ^ 2) ∧ ∃ k : ℕ, 0 < k ∧
      (orderOf r).totient = k * (orderOf (r ^ 2)).totient ∧
      aeval (BaseB.tB (p * q)) (cycloScaled q (orderOf r)) *
          aeval (-BaseB.tB (p * q)) (cycloScaled q (orderOf r)) =
        (q : ℂ) ^ (orderOf r).totient * ((cycValR p q (orderOf (r ^ 2)) : ℤ) : ℂ) ^ k := by
  obtain ⟨hm3, hnm, k, hk, htot, hD⟩ := cyclo_dataR hr h4
  refine ⟨hm3, hnm, k, hk, htot, ?_⟩
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = BaseB.tB (p * q) / q := ⟨_, rfl⟩
  have e1 : BaseB.tB (p * q) = (q : ℂ) * s := by rw [hs, mul_div_cancel₀ _ hq0]
  have hs2 : s ^ 2 = (p : ℂ) / q := by
    rw [hs, div_pow, BaseB.tB_sq]
    push_cast
    field_simp
  rw [e1, ← mul_neg, aeval_mul_cycloScaled, aeval_mul_cycloScaled, mul_mul_mul_comm, hD s, hs2,
    ← aeval_div_cyclotomic_mul_pow hq p (orderOf (r ^ 2)), mul_pow, ← pow_mul,
    mul_comm (orderOf (r ^ 2)).totient k, ← htot]
  ring

end RatBase

end PiFormula
