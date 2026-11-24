module

public import Pilean.BaseB.TheoremG

/-!
# A general base `b`: relations that involve the logarithm of a rational number (auxiliary)

Two ingredients for `Pilean/BaseB/LogNonValue.lean`. Let `t = √b` and let `y` be a positive
rational number all of whose prime factors divide `b`.

* **The real part** (`log_rat_indepB`, for `b ≥ 5`, `b ≠ 9`, `y ≠ 1`). In a relation
  `2 m log y + 2 z₁ log(1 - 1/√b) + 2 z₂ log(1 + 1/√b) + s log(1 + 1/b) = 0`
  with integers `m, z₁, z₂, s`, one has `m = 0`. The relation is
  `2 m log y + 2 z₁ log(√b - 1) + 2 z₂ log(√b + 1) + s log(b + 1) = (z₁ + z₂ + s) log b`.
  - If `b` is not a square, `((√b + 1)/(√b - 1))^(z₂ - z₁)` is rational, so `z₁ = z₂`, and
    `y^(2m) (b - 1)^(2z) (b + 1)^s = b^(2z + s)`. At a prime that does not divide `b` the
    numbers `y` and `b` are units, so `2z v(b - 1) + s v(b + 1) = 0` for every such prime.
  - If `b = c²` (so `c ≥ 4`), `y^(2m) (c - 1)^(2z₁) (c + 1)^(2z₂) (c² + 1)^s` is a power of
    `c`. An odd prime factor of `c² + 1` divides none of `c - 1`, `c + 1`, `c`: `s = 0`. Then
    `2z₁ v(c - 1) + 2z₂ v(c + 1) = 0` at every prime that does not divide `c`.
  In both cases `eq_zero_of_multiplicity_rel` applies: for `n ≥ 4` the number
  `(n - 1)(n + 1)` has an odd prime factor (it is a power of 2 only for `n = 3`), which
  divides exactly one of `n - 1`, `n + 1` and kills one exponent; any prime factor of the
  other number kills the other. So `z₁ = z₂ = s = 0`, and `m log y = 0` with `y ≠ 1`.
  The case `n = 3` is the base `b = 9`, where `log 3 = -2 log(1 - 1/3) + log(1 + 1/3)`.
* **The support** (`support_subset_fourth_roots_nat`, from `GoodPrimesB b`). A relation
  `u ∏ (1 - r/t)^(e_r) = ξ v`, with `ξ` a root of unity and `u`, `v` integers all of whose
  prime factors divide `b`, is supported on the four roots `1, -1, i, -i`. This is
  `support_subset_fourth_roots` with the two integers: a good prime `P` lies over a rational
  prime that does not divide `b`, so `u` and `v` are not in `P`.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace BaseB

/-! ## 1. Valuations of a relation between logarithms -/

/-- A relation `m log y + ∑ e_i log a_i = 0`, with `y` a positive rational number and the `a_i`
positive integers, holds for the `p`-adic valuations. -/
theorem padicVal_of_log_rel {y : ℚ} (hy : 0 < y) {a₁ a₂ a₃ a₄ : ℕ} (h₁ : 0 < a₁) (h₂ : 0 < a₂)
    (h₃ : 0 < a₃) (h₄ : 0 < a₄) {m e₁ e₂ e₃ e₄ : ℤ}
    (h : (m : ℝ) * Real.log y + e₁ * Real.log a₁ + e₂ * Real.log a₂ + e₃ * Real.log a₃ +
      e₄ * Real.log a₄ = 0) {p : ℕ} (hp : p.Prime) :
    m * padicValRat p y + e₁ * (multiplicity p a₁ : ℤ) + e₂ * (multiplicity p a₂ : ℤ) +
      e₃ * (multiplicity p a₃ : ℤ) + e₄ * (multiplicity p a₄ : ℤ) = 0 := by
  have hz : ∀ (x : ℝ), 0 < x → ∀ n : ℤ, Real.exp (n * Real.log x) = x ^ n :=
    fun x hx n => by rw [mul_comm, Real.exp_mul, Real.exp_log hx, Real.rpow_intCast]
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have h' := congrArg Real.exp h
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_zero, hz _ hyR,
    hz _ (Nat.cast_pos.2 h₁), hz _ (Nat.cast_pos.2 h₂), hz _ (Nat.cast_pos.2 h₃),
    hz _ (Nat.cast_pos.2 h₄)] at h'
  have hq : y ^ m * (a₁ : ℚ) ^ e₁ * (a₂ : ℚ) ^ e₂ * (a₃ : ℚ) ^ e₃ * (a₄ : ℚ) ^ e₄ = 1 := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact h'
  have := Fact.mk hp
  have n₀ : y ^ m ≠ 0 := zpow_ne_zero _ hy.ne'
  have n₁ : (a₁ : ℚ) ^ e₁ ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 h₁.ne')
  have n₂ : (a₂ : ℚ) ^ e₂ ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 h₂.ne')
  have n₃ : (a₃ : ℚ) ^ e₃ ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 h₃.ne')
  have n₄ : (a₄ : ℚ) ^ e₄ ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 h₄.ne')
  have hv := congrArg (padicValRat p) hq
  rw [padicValRat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero n₀ n₁) n₂) n₃) n₄,
    padicValRat.mul (mul_ne_zero (mul_ne_zero n₀ n₁) n₂) n₃,
    padicValRat.mul (mul_ne_zero n₀ n₁) n₂, padicValRat.mul n₀ n₁, padicValRat.zpow,
    padicValRat.zpow, padicValRat.zpow, padicValRat.zpow, padicValRat.zpow, padicValRat.of_nat,
    padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat, padicValRat.one] at hv
  exact hv

private theorem int_eq_zero_of_mul_multiplicity {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hpn : p ∣ n) {e : ℤ} (h : e * (multiplicity p n : ℤ) = 0) : e = 0 := by
  have := Fact.mk hp
  have h1 : 1 ≤ multiplicity p n := one_le_multiplicity_of_dvd hn hpn
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · omega

/-- For `d ≥ 3` the number `d (d + 2)` has an odd prime factor. (For `d = 2` it is `8`.) -/
theorem exists_odd_prime_dvd_mul_add_two {d : ℕ} (hd : 3 ≤ d) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ d * (d + 2) := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (d * (d + 2)) with
    ⟨k, hk⟩ | ⟨p, hp, hpd, ho⟩
  · exfalso
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hk)
    have hi2 : 2 ≤ i := by
      by_contra hlt
      have h01 : i = 0 ∨ i = 1 := by omega
      rcases h01 with rfl | rfl
      · rw [pow_zero] at hi
        omega
      · rw [pow_one] at hi
        omega
    have hj2 : 2 ≤ j := by
      by_contra hlt
      have h01 : j = 0 ∨ j = 1 := by omega
      rcases h01 with rfl | rfl
      · rw [pow_zero] at hj
        omega
      · rw [pow_one] at hj
        omega
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
    have e1 : 2 ^ (i' + 2) = 4 * 2 ^ i' := by ring
    have e2 : 2 ^ (j' + 2) = 4 * 2 ^ j' := by ring
    omega
  · refine ⟨p, hp, ?_, hpd⟩
    rintro rfl
    exact absurd ho (by decide)

/-- Let `n ≥ 4`. If `e₁ v_p(n - 1) + e₂ v_p(n + 1) = 0` for every prime `p` that does not
divide `n`, then `e₁ = e₂ = 0`. (False for `n = 3`: there `n - 1 = 2`, `n + 1 = 4`.) -/
theorem eq_zero_of_multiplicity_rel {n : ℕ} (hn : 4 ≤ n) {e₁ e₂ : ℤ}
    (hV : ∀ p : ℕ, p.Prime → ¬ p ∣ n →
      e₁ * (multiplicity p (n - 1) : ℤ) + e₂ * (multiplicity p (n + 1) : ℤ) = 0) :
    e₁ = 0 ∧ e₂ = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  have hV' : ∀ p : ℕ, p.Prime → ¬ p ∣ d + 1 →
      e₁ * (multiplicity p d : ℤ) + e₂ * (multiplicity p (d + 2) : ℤ) = 0 := by
    intro p hp hpn
    have h := hV p hp hpn
    rwa [Nat.add_sub_cancel] at h
  obtain ⟨p, hp, hp2, hpd⟩ := exists_odd_prime_dvd_mul_add_two (d := d) (by omega)
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  -- a prime factor of `d` or of `d + 2` does not divide `d + 1`
  have hn1 : ∀ q : ℕ, q.Prime → q ∣ d → ¬ q ∣ d + 1 := fun q hq h h' =>
    hq.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h'))
  have hn2 : ∀ q : ℕ, q.Prime → q ∣ d + 2 → ¬ q ∣ d + 1 := fun q hq h h' =>
    hq.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right (b := d + 1) (c := 1) h').1 h))
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
  · -- `p` divides `d` and not `d + 2`
    have h2 : ¬ p ∣ d + 2 := fun h' => hp2' ((Nat.dvd_add_right h).1 h')
    have hv := hV' p hp (hn1 p hp h)
    rw [multiplicity_eq_zero_of_not_dvd h2, Nat.cast_zero, mul_zero, add_zero] at hv
    have he₁ := int_eq_zero_of_mul_multiplicity hp (by omega) h hv
    have hq := Nat.minFac_prime (show d + 2 ≠ 1 by omega)
    have hqd := Nat.minFac_dvd (d + 2)
    have hv' := hV' _ hq (hn2 _ hq hqd)
    rw [he₁, zero_mul, zero_add] at hv'
    exact ⟨he₁, int_eq_zero_of_mul_multiplicity hq (by omega) hqd hv'⟩
  · -- `p` divides `d + 2` and not `d`
    have h2 : ¬ p ∣ d := fun h' => hp2' ((Nat.dvd_add_right h').1 h)
    have hv := hV' p hp (hn2 p hp h)
    rw [multiplicity_eq_zero_of_not_dvd h2, Nat.cast_zero, mul_zero, zero_add] at hv
    have he₂ := int_eq_zero_of_mul_multiplicity hp (by omega) h hv
    have hq := Nat.minFac_prime (show d ≠ 1 by omega)
    have hqd := Nat.minFac_dvd d
    have hv' := hV' _ hq (hn1 _ hq hqd)
    rw [he₂, zero_mul, add_zero] at hv'
    exact ⟨int_eq_zero_of_mul_multiplicity hq (by omega) hqd hv', he₂⟩

/-! ## 2. The real part -/

/-- **The real part of a relation with `log y`.** Let `b ≥ 5`, `b ≠ 9`, and let `y ≠ 1` be a
positive rational number all of whose prime factors divide `b`. In a relation
`2 m log y + 2 z₁ log(1 - 1/√b) + 2 z₂ log(1 + 1/√b) + s log(1 + 1/b) = 0` with integer
coefficients, `m = 0`. -/
theorem log_rat_indepB {b : ℕ} (hb : 5 ≤ b) (hb9 : b ≠ 9) {y : ℚ} (hy : 0 < y) (hy1 : y ≠ 1)
    (hp : ∀ p : ℕ, p.Prime → padicValRat p y ≠ 0 → p ∣ b) {m z₁ z₂ s : ℤ}
    (h : 2 * (m : ℝ) * Real.log y + 2 * (z₁ : ℝ) * Real.log (1 - 1 / Real.sqrt (b : ℝ)) +
        2 * z₂ * Real.log (1 + 1 / Real.sqrt (b : ℝ)) + s * Real.log (1 + 1 / (b : ℝ)) = 0) :
    m = 0 := by
  have hb2 : 2 ≤ b := by omega
  have ht1 := one_lt_sqrtB hb2
  have ht0 : 0 < Real.sqrt (b : ℝ) := by linarith
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hlogt : Real.log (Real.sqrt (b : ℝ)) = Real.log (b : ℝ) / 2 :=
    Real.log_sqrt (Nat.cast_nonneg b)
  have e1 : Real.log (1 - 1 / Real.sqrt (b : ℝ)) =
      Real.log (Real.sqrt (b : ℝ) - 1) - Real.log (b : ℝ) / 2 := by
    rw [← hlogt, ← Real.log_div (by linarith) ht0.ne']
    congr 1
    field_simp
  have e2 : Real.log (1 + 1 / Real.sqrt (b : ℝ)) =
      Real.log (Real.sqrt (b : ℝ) + 1) - Real.log (b : ℝ) / 2 := by
    rw [← hlogt, ← Real.log_div (by linarith) ht0.ne']
    congr 1
    field_simp
  have e3 : Real.log (1 + 1 / (b : ℝ)) = Real.log ((b : ℝ) + 1) - Real.log (b : ℝ) := by
    rw [← Real.log_div (by linarith) hb0.ne']
    congr 1
    field_simp
  have H : 2 * (m : ℝ) * Real.log y + 2 * (z₁ : ℝ) * Real.log (Real.sqrt (b : ℝ) - 1) +
      2 * z₂ * Real.log (Real.sqrt (b : ℝ) + 1) + s * Real.log ((b : ℝ) + 1) -
      (z₁ + z₂ + s) * Real.log (b : ℝ) = 0 := by
    rw [e1, e2, e3] at h
    linear_combination h
  -- `y` is a unit at the primes that do not divide `b`
  have hy0 : ∀ p : ℕ, p.Prime → ¬ p ∣ b → padicValRat p y = 0 := fun p hpp hpb => by
    by_contra h0
    exact hpb (hp p hpp h0)
  have hlogy : Real.log (y : ℝ) ≠ 0 := by
    intro h0
    have h1 : (y : ℝ) = 1 := Real.eq_one_of_pos_of_log_eq_zero hyR h0
    exact hy1 (by exact_mod_cast h1)
  -- it is enough to prove `z₁ = z₂ = s = 0`
  suffices hz : z₁ = 0 ∧ z₂ = 0 ∧ s = 0 by
    obtain ⟨rfl, rfl, rfl⟩ := hz
    have h0 : (m : ℝ) * Real.log y = 0 := by
      rw [Int.cast_zero] at H
      linear_combination H / 2
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hlogy
  by_cases hsq : IsSquare b
  · -- `b = c²` with `c ≥ 4`
    obtain ⟨c, rfl⟩ := hsq
    have hc : 4 ≤ c := by
      by_contra hlt
      have hc3 : c ≤ 3 := by omega
      interval_cases c <;> omega
    have hsqrt : Real.sqrt ((c * c : ℕ) : ℝ) = (c : ℝ) := by
      rw [Nat.cast_mul]
      exact Real.sqrt_mul_self (Nat.cast_nonneg _)
    have a1 : (c : ℝ) - 1 = ((c - 1 : ℕ) : ℝ) := (Nat.cast_pred (by omega)).symm
    have a2 : (c : ℝ) + 1 = ((c + 1 : ℕ) : ℝ) := by push_cast; ring
    have a3 : ((c * c : ℕ) : ℝ) + 1 = ((c * c + 1 : ℕ) : ℝ) := by push_cast; ring
    have hl : Real.log ((c * c : ℕ) : ℝ) = 2 * Real.log (c : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      ring
    rw [hsqrt, a1, a2, a3, hl] at H
    have hrel : ((2 * m : ℤ) : ℝ) * Real.log y + ((2 * z₁ : ℤ) : ℝ) * Real.log ((c - 1 : ℕ) : ℝ) +
        ((2 * z₂ : ℤ) : ℝ) * Real.log ((c + 1 : ℕ) : ℝ) +
        ((-(2 * (z₁ + z₂ + s)) : ℤ) : ℝ) * Real.log (c : ℝ) +
        (s : ℝ) * Real.log ((c * c + 1 : ℕ) : ℝ) = 0 := by
      simp only [Int.cast_mul, Int.cast_add, Int.cast_neg, Int.cast_ofNat]
      linear_combination H
    have hval : ∀ p : ℕ, p.Prime → ¬ p ∣ c →
        2 * z₁ * (multiplicity p (c - 1) : ℤ) + 2 * z₂ * (multiplicity p (c + 1) : ℤ) +
          s * (multiplicity p (c * c + 1) : ℤ) = 0 := by
      intro p hpp hpc
      have hpb : ¬ p ∣ c * c := fun h => hpc (((Nat.Prime.dvd_mul hpp).1 h).elim id id)
      have hv := padicVal_of_log_rel hy (a₁ := c - 1) (a₂ := c + 1) (a₃ := c)
        (a₄ := c * c + 1) (by omega) (by omega) (by omega) (by positivity) hrel hpp
      rw [hy0 p hpp hpb, multiplicity_eq_zero_of_not_dvd hpc] at hv
      simp only [mul_zero, zero_add, Nat.cast_zero, add_zero] at hv
      exact hv
    -- an odd prime factor of `c² + 1`
    obtain ⟨q, hq, hq2, hqd⟩ := exists_odd_prime_dvd_sq_add_one (c := c) (by omega)
    have hq2' : ¬ q ∣ 2 := fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
    have hqc : ¬ q ∣ c := fun h =>
      hq.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right (h.mul_right c)).1 hqd))
    have hprod : c * c + 1 = (c - 1) * (c + 1) + 2 := by
      obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      ring
    have hqd' : q ∣ (c - 1) * (c + 1) + 2 := hprod ▸ hqd
    have hqm : ¬ q ∣ c - 1 := fun h => hq2' ((Nat.dvd_add_right (h.mul_right _)).1 hqd')
    have hqp : ¬ q ∣ c + 1 := fun h => hq2' ((Nat.dvd_add_right (h.mul_left _)).1 hqd')
    have hs : s = 0 := by
      have hv := hval q hq hqc
      rw [multiplicity_eq_zero_of_not_dvd hqm, multiplicity_eq_zero_of_not_dvd hqp,
        Nat.cast_zero, mul_zero, mul_zero, zero_add, zero_add] at hv
      exact int_eq_zero_of_mul_multiplicity hq (by positivity) hqd hv
    subst hs
    have hval' : ∀ p : ℕ, p.Prime → ¬ p ∣ c →
        2 * z₁ * (multiplicity p (c - 1) : ℤ) + 2 * z₂ * (multiplicity p (c + 1) : ℤ) = 0 := by
      intro p hpp hpc
      have hv := hval p hpp hpc
      rwa [zero_mul, add_zero] at hv
    obtain ⟨h1, h2⟩ := eq_zero_of_multiplicity_rel hc hval'
    exact ⟨by omega, by omega, rfl⟩
  · -- `b` is not a square
    have ht : Real.sqrt (b : ℝ) * Real.sqrt (b : ℝ) = b :=
      Real.mul_self_sqrt (Nat.cast_nonneg b)
    have hbR : (5 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hm : 0 < Real.sqrt (b : ℝ) - 1 := by linarith
    have hpl : 0 < Real.sqrt (b : ℝ) + 1 := by linarith
    have hsum : Real.log (Real.sqrt (b : ℝ) - 1) + Real.log (Real.sqrt (b : ℝ) + 1) =
        Real.log ((b : ℝ) - 1) := by
      rw [← Real.log_mul hm.ne' hpl.ne']
      congr 1
      linear_combination ht
    have hdiff : Real.log (Real.sqrt (b : ℝ) + 1) - Real.log (Real.sqrt (b : ℝ) - 1) =
        Real.log ((Real.sqrt (b : ℝ) + 1) / (Real.sqrt (b : ℝ) - 1)) :=
      (Real.log_div hpl.ne' hm.ne').symm
    have hu : 0 < (Real.sqrt (b : ℝ) + 1) / (Real.sqrt (b : ℝ) - 1) := div_pos hpl hm
    -- `z₁ = z₂`, since a non-zero power of `(√b + 1)/(√b - 1)` is irrational
    have key : ((z₁ + z₂ : ℤ) : ℝ) * Real.log ((b : ℝ) - 1) +
        ((z₂ - z₁ : ℤ) : ℝ) * Real.log ((Real.sqrt (b : ℝ) + 1) / (Real.sqrt (b : ℝ) - 1)) +
        (s : ℝ) * Real.log ((b : ℝ) + 1) + ((-(z₁ + z₂ + s) : ℤ) : ℝ) * Real.log (b : ℝ) +
        ((2 * m : ℤ) : ℝ) * Real.log y = 0 := by
      push_cast
      linear_combination H - ((z₁ : ℝ) + z₂) * hsum + ((z₁ : ℝ) - z₂) * hdiff
    have hz : ∀ (x : ℝ), 0 < x → ∀ n : ℤ, Real.exp (n * Real.log x) = x ^ n :=
      fun x hx n => by rw [mul_comm, Real.exp_mul, Real.exp_log hx, Real.rpow_intCast]
    have hexp : ((b : ℝ) - 1) ^ (z₁ + z₂) *
        ((Real.sqrt (b : ℝ) + 1) / (Real.sqrt (b : ℝ) - 1)) ^ (z₂ - z₁) * ((b : ℝ) + 1) ^ s *
        (b : ℝ) ^ (-(z₁ + z₂ + s)) * (y : ℝ) ^ (2 * m) = 1 := by
      have h' := congrArg Real.exp key
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_zero,
        hz _ (by linarith), hz _ hu, hz _ (by linarith), hz _ (by linarith), hz _ hyR] at h'
      exact h'
    have h12 : z₂ - z₁ = 0 := by
      by_contra hC
      apply irrational_unitB_zpow hb2 hsq hC
      refine ⟨(((b : ℚ) - 1) ^ (z₁ + z₂) * ((b : ℚ) + 1) ^ s * (b : ℚ) ^ (-(z₁ + z₂ + s)) *
        y ^ (2 * m))⁻¹, ?_⟩
      push_cast
      exact (eq_inv_of_mul_eq_one_left (by linear_combination hexp)).symm
    obtain rfl : z₂ = z₁ := by omega
    -- valuations at the primes that do not divide `b`
    have hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := Nat.cast_pred (by omega)
    have hrel : ((2 * m : ℤ) : ℝ) * Real.log y + ((2 * z₂ : ℤ) : ℝ) * Real.log ((b - 1 : ℕ) : ℝ) +
        (s : ℝ) * Real.log ((b + 1 : ℕ) : ℝ) + ((-(2 * z₂ + s) : ℤ) : ℝ) * Real.log (b : ℝ) +
        ((0 : ℤ) : ℝ) * Real.log ((1 : ℕ) : ℝ) = 0 := by
      rw [hb1]
      push_cast
      linear_combination H - 2 * (z₂ : ℝ) * hsum
    have hval : ∀ p : ℕ, p.Prime → ¬ p ∣ b →
        2 * z₂ * (multiplicity p (b - 1) : ℤ) + s * (multiplicity p (b + 1) : ℤ) = 0 := by
      intro p hpp hpb
      have hv := padicVal_of_log_rel hy (a₁ := b - 1) (a₂ := b + 1) (a₃ := b) (a₄ := 1)
        (by omega) (by omega) (by omega) one_pos hrel hpp
      rw [hy0 p hpp hpb, multiplicity_eq_zero_of_not_dvd hpb] at hv
      simp only [mul_zero, zero_add, Nat.cast_zero, add_zero, zero_mul] at hv
      exact hv
    obtain ⟨h1, h2⟩ := eq_zero_of_multiplicity_rel (by omega) hval
    exact ⟨by omega, by omega, h2⟩

/-! ## 3. Relations up to two integers, and the private prime -/

/-- A multiplicative relation up to two integers: `u ∏_{r ∈ S} (1 - r/t)^(e_r) = ξ v` with
`ξ` a root of unity. -/
def IsRelationNatB (b u v : ℕ) (S : Finset ℂ) (e : ℂ → ℤ) : Prop :=
  ∃ ξ : ℂ, IsOfFinOrder ξ ∧ (∏ r ∈ S, (1 - r / tB b) ^ (e r)) * (u : ℂ) = ξ * (v : ℂ)

/-- The cleared form `∏ (t - r)^(e⁺) · t^(N⁻) · u = ξ ∏ (t - r)^(e⁻) · t^(N⁺) · v`. -/
theorem cleared_of_relationNatB {b : ℕ} (hb : 2 ≤ b) {u v : ℕ} {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} (h : IsRelationNatB b u v S e) :
    ∃ ξ : ℂ, IsOfFinOrder ξ ∧
      (∏ r ∈ S, (tB b - r) ^ (e r).toNat) * tB b ^ (∑ r ∈ S, (-e r).toNat) * (u : ℂ) =
        ξ * (∏ r ∈ S, (tB b - r) ^ (-e r).toNat) * tB b ^ (∑ r ∈ S, (e r).toNat) * (v : ℂ) := by
  obtain ⟨ξ, hξ, hrel⟩ := h
  refine ⟨ξ, hξ, ?_⟩
  have ht0 : tB b ≠ 0 := tB_ne_zero hb
  -- each factor: (1 - r/t)^e (t - r)^(-e)⁺ t^(e⁺) = (t - r)^(e⁺) t^((-e)⁺)
  have hfac : ∀ r ∈ S,
      (1 - r / tB b) ^ (e r) * ((tB b - r) ^ (-e r).toNat * tB b ^ (e r).toNat) =
        (tB b - r) ^ (e r).toNat * tB b ^ (-e r).toNat := by
    intro r hr
    have hne : tB b - r ≠ 0 := tB_sub_ne_zero hb (norm_root (hS r hr))
    have hz1 : (tB b - r) ^ (e r) = (tB b - r) ^ (e r).toNat / (tB b - r) ^ (-e r).toNat := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hne]
      congr 1
      omega
    have hz2 : tB b ^ (e r) = tB b ^ (e r).toNat / tB b ^ (-e r).toNat := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ ht0]
      congr 1
      omega
    have h1 : (tB b - r) ^ (-e r).toNat ≠ 0 := pow_ne_zero _ hne
    have h2 : tB b ^ (-e r).toNat ≠ 0 := pow_ne_zero _ ht0
    have h3 : tB b ^ (e r).toNat ≠ 0 := pow_ne_zero _ ht0
    rw [wB_eq hb, div_zpow, hz1, hz2]
    field_simp
  have hprod := Finset.prod_congr rfl hfac
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum] at hprod
  rw [← hprod]
  linear_combination
    ((∏ r ∈ S, (tB b - r) ^ (-e r).toNat) * tB b ^ (∑ r ∈ S, (e r).toNat)) * hrel

/-- **The private prime, up to two integers.** In a relation `u ∏ (1 - r/t)^(e_r) = ξ v`: if
`t - r₀ ∈ P`, while `t`, `u`, `v` and the other `t - r` are not in `P`, then `e_{r₀} = 0`. -/
theorem coeff_eq_zero_of_private_idealNatB {b : ℕ} (hb : 2 ≤ b) {P : Ideal Aint} [P.IsPrime]
    {u v : ℕ} {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ}
    (h : IsRelationNatB b u v S e) {r₀ : ℂ} (hr₀ : r₀ ∈ S) (ht : ¬ InP P (tB b))
    (hu : ¬ InP P (u : ℂ)) (hv : ¬ InP P (v : ℂ)) (h0 : InP P (tB b - r₀))
    (hpriv : ∀ r ∈ S, r ≠ r₀ → ¬ InP P (tB b - r)) : e r₀ = 0 := by
  classical
  obtain ⟨ξ, hξ, hc⟩ := cleared_of_relationNatB hb hS h
  have hint : ∀ r ∈ S, ∀ n : ℕ, IsIntegral ℤ ((tB b - r) ^ n) :=
    fun r hr n => (isIntegral_tB_sub b (hS r hr)).pow n
  have hprodI : ∀ f : ℂ → ℕ, IsIntegral ℤ (∏ r ∈ S, (tB b - r) ^ f r) :=
    fun f => IsIntegral.prod _ fun r hr => hint r hr _
  have side : ∀ f g : ℂ → ℕ, 0 < f r₀ → g r₀ = 0 → ∀ (m n x x' : ℕ) (c : ℂ),
      IsOfFinOrder c → ¬ InP P (x' : ℂ) →
      (∏ r ∈ S, (tB b - r) ^ f r) * tB b ^ m * (x : ℂ) =
        c * (∏ r ∈ S, (tB b - r) ^ g r) * tB b ^ n * (x' : ℂ) → False := by
    intro f g hf hg m n x x' c hc hx' heq
    have hL : InP P ((∏ r ∈ S, (tB b - r) ^ f r) * tB b ^ m * (x : ℂ)) :=
      ((inP_prod_of_mem _ (fun r hr => hint r hr _) hr₀ (h0.pow hf)).mul_right
        ((isIntegral_tB b).pow m)).mul_right (isIntegral_natCast' x)
    rw [heq] at hL
    rcases inP_mul (((isIntegral_of_finOrder hc).mul (hprodI g)).mul ((isIntegral_tB b).pow n))
      (isIntegral_natCast' x') hL with hL | hL
    · rcases inP_mul ((isIntegral_of_finOrder hc).mul (hprodI g)) ((isIntegral_tB b).pow n) hL
        with hL | hL
      · rcases inP_mul (isIntegral_of_finOrder hc) (hprodI g) hL with hL | hL
        · exact not_inP_root hc hL
        · obtain ⟨r, hr, hL⟩ := inP_prod S _ (fun r hr => hint r hr _) hL
          obtain ⟨hpos, hL⟩ := inP_of_pow (isIntegral_tB_sub b (hS r hr)) hL
          by_cases hrr : r = r₀
          · rw [hrr, hg] at hpos
            exact lt_irrefl 0 hpos
          · exact hpriv r hr hrr hL
      · exact ht (inP_of_pow (isIntegral_tB b) hL).2
    · exact hx' hL
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1 : 0 < (-e r₀).toNat := by omega
    have h2 : (e r₀).toNat = 0 := by omega
    have hξ0 : ξ ≠ 0 := ne_zero_of_finOrder hξ
    refine side (fun r => (-e r).toNat) (fun r => (e r).toNat) h1 h2
      (∑ r ∈ S, (e r).toNat) (∑ r ∈ S, (-e r).toNat) v u ξ⁻¹ (isOfFinOrder_inv' hξ) hu ?_
    rw [mul_assoc ξ⁻¹, mul_assoc ξ⁻¹, hc]
    field_simp
  · have h1 : 0 < (e r₀).toNat := by omega
    have h2 : (-e r₀).toNat = 0 := by omega
    exact side (fun r => (e r).toNat) (fun r => (-e r).toNat) h1 h2 _ _ u v ξ hξ hv hc

/-! ## 4. The support theorem -/

/-- **The support theorem, up to two integers** (from `GoodPrimesB b`). If every prime factor
of `u` and of `v` divides `b`, a relation `u ∏ (1 - r/t)^(e_r) = ξ v` is supported on the four
roots `1, -1, i, -i`. -/
theorem support_subset_fourth_roots_nat {b : ℕ} (hb : 2 ≤ b) (hG : GoodPrimesB b) {u v : ℕ}
    (hu : ∀ p : ℕ, p.Prime → p ∣ u → p ∣ b) (hv : ∀ p : ℕ, p.Prime → p ∣ v → p ∣ b)
    {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ}
    (h : IsRelationNatB b u v S e) : ∀ r ∈ S, r ^ 4 ≠ 1 → e r = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set S' := S.filter (fun r => e r ≠ 0) with hS'def
  have hS' : ∀ r ∈ S', IsOfFinOrder r := fun r hr => hS r (Finset.mem_filter.1 hr).1
  have h' : IsRelationNatB b u v S' e := by
    obtain ⟨ξ, hξ, hrel⟩ := h
    refine ⟨ξ, hξ, ?_⟩
    rw [hS'def, Finset.prod_filter_of_ne (p := fun r => e r ≠ 0)
      (fun r _ hr hc => hr (by simp [hc]))]
    exact hrel
  set T := S'.filter (fun r => r ^ 4 ≠ 1) with hTdef
  have hT : T.Nonempty := by
    obtain ⟨r, hr, hr4, hre⟩ := hcon
    exact ⟨r, by simp [hTdef, hS'def, hr, hr4, hre]⟩
  obtain ⟨r, hrT, hmax⟩ := Finset.exists_max_image T orderOf hT
  have hrS' : r ∈ S' := (Finset.mem_filter.1 hrT).1
  have hr4 : r ^ 4 ≠ 1 := (Finset.mem_filter.1 hrT).2
  have her : e r ≠ 0 := (Finset.mem_filter.1 hrS').2
  have hr := hS' r hrS'
  obtain ⟨P, hP, p, hp, hp2, hpb, hpr, hpP, htr⟩ := hG r hr hr4
  -- `t ∉ P`: else `b = t² ∈ P`, and `p ∈ P` is prime to `b`
  have ht : ¬ InP P (tB b) := by
    intro ht
    have h2 := ht.mul_right (isIntegral_tB b)
    rw [← pow_two, tB_sq] at h2
    have hcop : Nat.Coprime b p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpb).symm
    exact not_inP_coprime hcop h2 hpP
  -- `u, v ∉ P`: their prime factors divide `b`, and `p` does not
  have hPu : ¬ InP P (u : ℂ) := fun hin =>
    not_inP_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => hpb (hu p hp hd)).symm
      hin hpP
  have hPv : ¬ InP P (v : ℂ) := fun hin =>
    not_inP_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => hpb (hv p hp hd)).symm
      hin hpP
  refine her (coeff_eq_zero_of_private_idealNatB hb hS' h' hrS' ht hPu hPv htr ?_)
  intro r' hr' hne htr'
  have hr'f := hS' r' hr'
  have hr0 : r ≠ 0 := ne_zero_of_finOrder hr
  set w := r' / r with hw
  have hwfin : IsOfFinOrder w := isOfFinOrder_div' hr'f hr
  have hw1 : InP P (w - 1) := by
    have hd : InP P (r' - r) := by
      have := htr.sub htr'
      rwa [show tB b - r - (tB b - r') = r' - r by ring] at this
    have hrinv : IsIntegral ℤ r⁻¹ := isIntegral_of_finOrder (isOfFinOrder_inv' hr)
    have := hd.mul_right hrinv
    rwa [show (r' - r) * r⁻¹ = w - 1 by rw [hw]; field_simp] at this
  obtain ⟨a, hord⟩ := orderOf_eq_prime_pow_of_inP hp hpP hwfin hw1
  have ha : 0 < a := by
    by_contra h0
    push Not at h0
    rw [Nat.le_zero.1 h0, pow_zero, orderOf_eq_one_iff, hw, div_eq_one_iff_eq hr0] at hord
    exact hne hord
  have hcop : Nat.Coprime (orderOf r) (orderOf w) := by
    rw [hord]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpr).symm
  have hr'eq : r' = r * w := by rw [hw]; field_simp
  have hordr' : orderOf r' = orderOf r * p ^ a := by
    rw [hr'eq, (Commute.all r w).orderOf_mul_eq_mul_orderOf_of_coprime hcop, hord]
  by_cases hr'4 : r' ^ 4 = 1
  · -- a root with `r'⁴ = 1` has order dividing 4, which the odd prime `p` does not divide
    have h4 : orderOf r' ∣ 4 := orderOf_dvd_of_pow_eq_one hr'4
    have hp4 : p ∣ 2 ^ 2 := by
      refine Dvd.dvd.trans ?_ h4
      rw [hordr']
      exact Dvd.dvd.mul_left (dvd_pow_self p ha.ne') _
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hp4))
  · have hle := hmax r' (Finset.mem_filter.2 ⟨hr', hr'4⟩)
    rw [hordr'] at hle
    have : orderOf r * 1 < orderOf r * p ^ a :=
      Nat.mul_lt_mul_of_pos_left (Nat.one_lt_pow ha.ne' hp.one_lt) hr.orderOf_pos
    omega

end BaseB

end PiFormula
