import Pilean.BaseB.Defs

/-!
# The size condition for every base `b ≥ 6`

`SizeCond b m` (file `Defs`) says that `Φ_m(b)` exceeds `(√b + 1)^φ(m)`, and exceeds
`q (√b + 1)^φ(m)` for every prime `q` that divides both `m` and `Φ_m(b)`. Here it is proved
for every `b ≥ 6` and `m ≥ 3` (`sizeCond`).

Write `s = √b` and `φ = φ(m)`. Mathlib gives `(b - 1)^φ < Φ_m(b)`, and
`(b - 1)^φ = (s - 1)^φ (s + 1)^φ`.

* First part: `s - 1 ≥ 1`.
* Second part: it is enough that `q ≤ (s - 1)^φ` (`prime_le_sqrt_sub_one_pow`). This holds
  for every prime `q ∣ m`, with six exceptions, by the facts `φ ≥ 2`, `φ ≥ q - 1`, and
  `φ ≥ 2 (q - 1)` when `m ≠ q, 2q`, and the bounds `√b - 1 ≥ 9/5` (`b ≥ 8`), `≥ 8/5` (`b = 7`),
  `≥ 36/25` (`b = 6`).
* The six exceptions are `(b, m, q) = (6, 3, 3), (6, 6, 3), (6, 5, 5), (6, 10, 5), (7, 3, 3),
  (7, 6, 3)`, with `Φ_3(6) = 43`, `Φ_6(6) = 31`, `Φ_5(6) = 1555`, `Φ_10(6) = 1111`,
  `Φ_3(7) = 57`, `Φ_6(7) = 43`. In four of them `q` does not divide `Φ_m(b)`; the other two,
  `(6, 5, 5)` and `(7, 3, 3)`, are checked directly.
-/

open Polynomial

namespace PiFormula

namespace BaseB

/-! ## 1. Facts on the totient -/

theorem two_le_totient {m : ℕ} (hm : 3 ≤ m) : 2 ≤ m.totient := by
  have h1 : 0 < m.totient := Nat.totient_pos.2 (by omega)
  obtain ⟨k, hk⟩ := Nat.totient_even (by omega : 2 < m)
  omega

theorem pred_le_totient {q m : ℕ} (hq : q.Prime) (hm : 0 < m) (hqm : q ∣ m) :
    q - 1 ≤ m.totient := by
  have h := Nat.le_of_dvd (Nat.totient_pos.2 hm) (Nat.totient_dvd_of_dvd hqm)
  rwa [Nat.totient_prime hq] at h

/-- If the prime `q` divides `m` and `m` is neither `q` nor `2q`, then `φ(m) ≥ 2 (q - 1)`. -/
theorem two_mul_pred_le_totient {q m : ℕ} (hq : q.Prime) (hm : 0 < m) (hqm : q ∣ m)
    (h1 : m ≠ q) (h2 : m ≠ 2 * q) : 2 * (q - 1) ≤ m.totient := by
  obtain ⟨k, rfl⟩ := hqm
  have hk : 3 ≤ k := by
    rcases k with _ | _ | _ | k
    · simp at hm
    · simp at h1
    · exact absurd (mul_comm q 2) h2
    · omega
  by_cases hqk : q ∣ k
  · have hd : q ^ 2 ∣ q * k := by
      rw [sq]
      exact mul_dvd_mul_left q hqk
    have h := Nat.le_of_dvd (Nat.totient_pos.2 hm) (Nat.totient_dvd_of_dvd hd)
    rw [Nat.totient_prime_pow hq (by norm_num)] at h
    have h2q : 2 ≤ q := hq.two_le
    have h3 : 2 * (q - 1) ≤ q ^ (2 - 1) * (q - 1) := by
      rw [show 2 - 1 = 1 from rfl, pow_one]
      exact Nat.mul_le_mul_right _ h2q
    exact h3.trans h
  · have hc : q.Coprime k := (Nat.Prime.coprime_iff_not_dvd hq).2 hqk
    rw [Nat.totient_mul hc, Nat.totient_prime hq, mul_comm]
    exact Nat.mul_le_mul_left _ (two_le_totient hk)

/-! ## 2. Powers of a number above 1 -/

/-- If `n₀ + 1 ≤ c ^ n₀` and `(c - 1) (n₀ + 1) ≥ 1`, then `n + 1 ≤ c ^ n` for every `n ≥ n₀`. -/
theorem succ_le_pow {c : ℝ} {n₀ : ℕ} (hc1 : 1 ≤ c) (h0 : (n₀ : ℝ) + 1 ≤ c ^ n₀)
    (hc : 1 ≤ (c - 1) * ((n₀ : ℝ) + 1)) : ∀ n : ℕ, n₀ ≤ n → (n : ℝ) + 1 ≤ c ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h0
  | succ n hn ih =>
    rw [pow_succ]
    push_cast
    have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : ((n : ℝ) + 1) * c ≤ c ^ n * c := mul_le_mul_of_nonneg_right ih (by linarith)
    have h4 : (c - 1) * ((n₀ : ℝ) + 1) ≤ (c - 1) * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith

/-- From a lower bound `d` for `c`, an exponent `k ≤ n` and `x ≤ d ^ k`, get `x ≤ c ^ n`. -/
theorem le_pow_of_le {c d x : ℝ} {k n : ℕ} (hd : 1 ≤ d) (hdc : d ≤ c) (hkn : k ≤ n)
    (hx : x ≤ d ^ k) : x ≤ c ^ n :=
  hx.trans ((pow_le_pow_left₀ (by linarith) hdc k).trans
    (pow_le_pow_right₀ (hd.trans hdc) hkn))

/-! ## 3. The criterion `q ≤ (√b - 1)^φ(m)` -/

/-- Outside six exceptional cases, a prime `q` that divides `m` is at most `(√b - 1)^φ(m)`. -/
theorem prime_le_sqrt_sub_one_pow {b m q : ℕ} (hb : 6 ≤ b) (hm : 3 ≤ m) (hq : q.Prime)
    (hqm : q ∣ m) (h63 : ¬ (b = 6 ∧ q = 3 ∧ (m = 3 ∨ m = 6)))
    (h65 : ¬ (b = 6 ∧ q = 5 ∧ (m = 5 ∨ m = 10)))
    (h73 : ¬ (b = 7 ∧ q = 3 ∧ (m = 3 ∨ m = 6))) :
    (q : ℝ) ≤ (Real.sqrt (b : ℝ) - 1) ^ m.totient := by
  have hm0 : 0 < m := by omega
  have hφ2 : 2 ≤ m.totient := two_le_totient hm
  have hφq : q - 1 ≤ m.totient := pred_le_totient hq hm0 hqm
  have hq2 : 2 ≤ q := hq.two_le
  have hqcast : (q : ℝ) = ((q - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  by_cases hb8 : 8 ≤ b
  · -- `b ≥ 8`: `√b - 1 ≥ 9/5`
    have hd : (9 / 5 : ℝ) ≤ Real.sqrt (b : ℝ) - 1 := by
      have h8 : (8 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb8
      have : (14 / 5 : ℝ) ≤ Real.sqrt (b : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
      linarith
    by_cases hq3 : 3 ≤ q
    · refine le_pow_of_le (by norm_num) hd hφq ?_
      rw [hqcast]
      exact succ_le_pow (n₀ := 2) (by norm_num) (by norm_num) (by norm_num) _ (by omega)
    · obtain rfl : q = 2 := by omega
      exact le_pow_of_le (by norm_num) hd hφ2 (by norm_num)
  by_cases hb7 : b = 7
  · -- `b = 7`: `√7 - 1 ≥ 8/5`
    subst hb7
    have hd : (8 / 5 : ℝ) ≤ Real.sqrt ((7 : ℕ) : ℝ) - 1 := by
      have : (13 / 5 : ℝ) ≤ Real.sqrt ((7 : ℕ) : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
      linarith
    by_cases hq4 : 4 ≤ q
    · refine le_pow_of_le (by norm_num) hd hφq ?_
      rw [hqcast]
      exact succ_le_pow (n₀ := 3) (by norm_num) (by norm_num) (by norm_num) _ (by omega)
    · have hq' : q = 2 ∨ q = 3 := by omega
      rcases hq' with rfl | rfl
      · exact le_pow_of_le (by norm_num) hd hφ2 (by norm_num)
      · have hφ4 : 2 * (3 - 1) ≤ m.totient :=
          two_mul_pred_le_totient hq hm0 hqm (fun h => h73 ⟨rfl, rfl, Or.inl h⟩)
            (fun h => h73 ⟨rfl, rfl, Or.inr h⟩)
        exact le_pow_of_le (by norm_num) hd hφ4 (by norm_num)
  · -- `b = 6`: `√6 - 1 ≥ 36/25`
    obtain rfl : b = 6 := by omega
    have hd : (36 / 25 : ℝ) ≤ Real.sqrt ((6 : ℕ) : ℝ) - 1 := by
      have : (61 / 25 : ℝ) ≤ Real.sqrt ((6 : ℕ) : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
      linarith
    by_cases hq7 : 7 ≤ q
    · refine le_pow_of_le (by norm_num) hd hφq ?_
      rw [hqcast]
      exact succ_le_pow (n₀ := 6) (by norm_num) (by norm_num) (by norm_num) _ (by omega)
    · have hq' : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 := by omega
      rcases hq' with rfl | rfl | rfl | rfl | rfl
      · exact le_pow_of_le (by norm_num) hd hφ2 (by norm_num)
      · have hφ4 : 2 * (3 - 1) ≤ m.totient :=
          two_mul_pred_le_totient hq hm0 hqm (fun h => h63 ⟨rfl, rfl, Or.inl h⟩)
            (fun h => h63 ⟨rfl, rfl, Or.inr h⟩)
        exact le_pow_of_le (by norm_num) hd hφ4 (by norm_num)
      · exact absurd hq (by norm_num)
      · have hφ8 : 2 * (5 - 1) ≤ m.totient :=
          two_mul_pred_le_totient hq hm0 hqm (fun h => h65 ⟨rfl, rfl, Or.inl h⟩)
            (fun h => h65 ⟨rfl, rfl, Or.inr h⟩)
        exact le_pow_of_le (by norm_num) hd hφ8 (by norm_num)
      · exact absurd hq (by norm_num)

/-! ## 4. Values of the cyclotomic polynomials -/

theorem cast_eval_cyclotomic (b m : ℕ) :
    (((cyclotomic m ℤ).eval (b : ℤ) : ℤ) : ℝ) = (cyclotomic m ℝ).eval (b : ℝ) := by
  have h := eval_intCast_map (Int.castRingHom ℝ) (cyclotomic m ℤ) (b : ℤ)
  rw [map_cyclotomic] at h
  simpa using h.symm

/-- `(b - 1)^φ(m) < Φ_m(b)`, from Mathlib. -/
theorem sub_one_pow_lt_eval {b m : ℕ} (hb : 2 ≤ b) (hm : 2 ≤ m) :
    ((b : ℝ) - 1) ^ m.totient < (((cyclotomic m ℤ).eval (b : ℤ) : ℤ) : ℝ) := by
  rw [cast_eval_cyclotomic]
  exact sub_one_pow_totient_lt_cyclotomic_eval hm (by exact_mod_cast hb)

theorem eval_cyclotomic_three (x : ℤ) : (cyclotomic 3 ℤ).eval x = x ^ 2 + x + 1 := by
  simp [cyclotomic_three]

theorem eval_cyclotomic_six (x : ℤ) : (cyclotomic 6 ℤ).eval x = x ^ 2 - x + 1 := by
  simp [cyclotomic_six]

theorem eval_cyclotomic_five (x : ℤ) :
    (cyclotomic 5 ℤ).eval x = x ^ 4 + x ^ 3 + x ^ 2 + x + 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, eval_add, eval_pow, eval_X,
    eval_zero]
  ring

theorem eval_cyclotomic_ten (x : ℤ) :
    (cyclotomic 10 ℤ).eval x = x ^ 4 - x ^ 3 + x ^ 2 - x + 1 := by
  have h : cyclotomic (2 * 5) ℤ = (cyclotomic 5 ℤ).comp (-X) :=
    cyclotomic_two_mul_of_odd (by decide) (by norm_num) ℤ
  rw [show (10 : ℕ) = 2 * 5 from rfl, h, eval_comp, eval_cyclotomic_five]
  simp only [eval_neg, eval_X]
  ring

/-! ## 5. The size condition -/

/-- The size condition holds for every base `b ≥ 6` and every `m ≥ 3`. -/
theorem sizeCond {b m : ℕ} (hb : 6 ≤ b) (hm : 3 ≤ m) : SizeCond b m := by
  have hlt := sub_one_pow_lt_eval (b := b) (m := m) (by omega) (by omega)
  have hs2 : Real.sqrt (b : ℝ) ^ 2 = b := Real.sq_sqrt (Nat.cast_nonneg b)
  have hs : (2 : ℝ) ≤ Real.sqrt (b : ℝ) := by
    have h4 : (4 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : 4 ≤ b)
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hfac : ((b : ℝ) - 1) ^ m.totient =
      (Real.sqrt (b : ℝ) - 1) ^ m.totient * (Real.sqrt (b : ℝ) + 1) ^ m.totient := by
    rw [← mul_pow]
    congr 1
    linear_combination -hs2
  have hpos : 0 < (Real.sqrt (b : ℝ) + 1) ^ m.totient := by positivity
  rw [hfac] at hlt
  refine ⟨?_, ?_⟩
  · have h1 : 1 ≤ (Real.sqrt (b : ℝ) - 1) ^ m.totient := one_le_pow₀ (by linarith)
    nlinarith
  · intro q hq hqm hqΦ
    by_cases h63 : b = 6 ∧ q = 3 ∧ (m = 3 ∨ m = 6)
    · exfalso
      obtain ⟨rfl, rfl, rfl | rfl⟩ := h63
      · rw [eval_cyclotomic_three] at hqΦ
        norm_num at hqΦ
      · rw [eval_cyclotomic_six] at hqΦ
        norm_num at hqΦ
    by_cases h65 : b = 6 ∧ q = 5 ∧ (m = 5 ∨ m = 10)
    · obtain ⟨rfl, rfl, rfl | rfl⟩ := h65
      · -- `5 (√6 + 1)⁴ < 1555`
        rw [eval_cyclotomic_five, Nat.totient_prime Nat.prime_five]
        have h6 : Real.sqrt ((6 : ℕ) : ℝ) < 5 / 2 :=
          (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
        have h0 : (0 : ℝ) ≤ Real.sqrt ((6 : ℕ) : ℝ) + 1 := by linarith
        have h4 : (Real.sqrt ((6 : ℕ) : ℝ) + 1) ^ (5 - 1) ≤ (7 / 2 : ℝ) ^ (5 - 1) :=
          pow_le_pow_left₀ h0 (by linarith) _
        norm_num at h4 ⊢
        linarith
      · exfalso
        rw [eval_cyclotomic_ten] at hqΦ
        norm_num at hqΦ
    by_cases h73 : b = 7 ∧ q = 3 ∧ (m = 3 ∨ m = 6)
    · obtain ⟨rfl, rfl, rfl | rfl⟩ := h73
      · -- `3 (√7 + 1)² < 57`
        rw [eval_cyclotomic_three, Nat.totient_prime Nat.prime_three]
        have h7 : Real.sqrt ((7 : ℕ) : ℝ) < 3 :=
          (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
        have h0 : (0 : ℝ) ≤ Real.sqrt ((7 : ℕ) : ℝ) + 1 := by linarith
        have h4 : (Real.sqrt ((7 : ℕ) : ℝ) + 1) ^ (3 - 1) ≤ (4 : ℝ) ^ (3 - 1) :=
          pow_le_pow_left₀ h0 (by linarith) _
        norm_num at h4 ⊢
        linarith
      · exfalso
        rw [eval_cyclotomic_six] at hqΦ
        norm_num at hqΦ
    · have hle := prime_le_sqrt_sub_one_pow hb hm hq hqm h63 h65 h73
      calc (q : ℝ) * (Real.sqrt (b : ℝ) + 1) ^ m.totient
          ≤ (Real.sqrt (b : ℝ) - 1) ^ m.totient * (Real.sqrt (b : ℝ) + 1) ^ m.totient :=
            mul_le_mul_of_nonneg_right hle hpos.le
        _ < _ := hlt

end BaseB

end PiFormula
