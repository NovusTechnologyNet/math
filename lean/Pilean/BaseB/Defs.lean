import Pilean.Base5.Unconditional

/-!
# A general base `b`: shared definitions

For an integer `b ≥ 2`, the class `F_b` is the set of series `∑ ρ(k) b^(-⌊k/2⌋)/k` with `ρ`
rational and periodic. This file fixes the definitions and statements that the files of
`Pilean/BaseB` share, so that they can be developed independently:

* `tB b = √b` (a real number, seen in `ℂ`), with `(tB b)² = b`;
* `seriesTermB b`, `IsFBValue b`;
* `HasGoodPrimeB b r`: a prime ideal of the algebraic integers contains `tB b - r` and an odd
  rational prime `p` that divides neither `b` nor the order of `r`;
* `GoodPrimesB b`: every root of unity `r` with `r⁴ ≠ 1` has a good prime.

The aim (Statement G of `notes/pi_formula_theorem.md`, Part VI): for every `b ≥ 5`, a series
of `F_b` whose value is an algebraic multiple of `π` has all coefficients zero. The plan:

* `GoodPrimesB b` for every `b ≥ 6`, by a size argument on norms (and for `b = 5` from
  `Base5`);
* from `GoodPrimesB b`, a multiplicative relation among the numbers `1 - r/√b` is supported
  on the four roots `1, -1, i, -i`, where there is none for `b ≥ 5`; then Baker's theorem.

Nothing is proved here beyond the first properties of `tB`.
-/

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-! ## 1. `t = √b` -/

/-- `t = √b`. -/
noncomputable def tB (b : ℕ) : ℂ := ((Real.sqrt (b : ℝ) : ℝ) : ℂ)

theorem tB_sq (b : ℕ) : tB b ^ 2 = b := by
  rw [tB, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg b)]
  simp

theorem norm_tB (b : ℕ) : ‖tB b‖ = Real.sqrt (b : ℝ) := by
  rw [tB, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

theorem one_lt_norm_tB {b : ℕ} (hb : 2 ≤ b) : 1 < ‖tB b‖ := by
  rw [norm_tB, Real.lt_sqrt (by norm_num)]
  have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  linarith

theorem tB_ne_zero {b : ℕ} (hb : 2 ≤ b) : tB b ≠ 0 := by
  intro h
  have h1 := one_lt_norm_tB hb
  rw [h, norm_zero] at h1
  linarith

theorem isIntegral_tB (b : ℕ) : IsIntegral ℤ (tB b) := by
  refine ⟨X ^ 2 - C (b : ℤ), monic_X_pow_sub_C _ (by norm_num), ?_⟩
  simp [tB_sq]

theorem isAlgebraic_tB (b : ℕ) : IsAlgebraic ℚ (tB b) := by
  refine ⟨X ^ 2 - C (b : ℚ), ?_, ?_⟩
  · intro h
    have h2 := congrArg (fun P : ℚ[X] => P.coeff 2) h
    simp [coeff_X_pow] at h2
  · simp [tB_sq]

theorem isIntegral_tB_sub (b : ℕ) {r : ℂ} (hr : IsOfFinOrder r) : IsIntegral ℤ (tB b - r) :=
  (isIntegral_tB b).sub (isIntegral_of_finOrder hr)

theorem tB_sub_ne_zero {b : ℕ} (hb : 2 ≤ b) {r : ℂ} (hr : ‖r‖ = 1) : tB b - r ≠ 0 := by
  intro h
  have h1 : tB b = r := sub_eq_zero.1 h
  have h2 := one_lt_norm_tB hb
  rw [h1, hr] at h2
  exact lt_irrefl _ h2

theorem norm_div_tB_lt {b : ℕ} (hb : 2 ≤ b) {r : ℂ} (hr : ‖r‖ = 1) : ‖r / tB b‖ < 1 := by
  rw [norm_div, hr]
  exact (div_lt_one (by linarith [one_lt_norm_tB hb])).2 (one_lt_norm_tB hb)

/-- For `b = 5` this is the `t5` of `Base5`. -/
theorem tB_five : tB 5 = Base5.t5 := by
  simp [tB, Base5.t5]

/-! ## 2. The class `F_b` -/

/-- The term `ρ(k) b^(-⌊k/2⌋) / k` of the series. -/
noncomputable def seriesTermB (b : ℕ) (ρ : ℕ → ℚ) (k : ℕ) : ℝ :=
  (ρ k : ℝ) / (b : ℝ) ^ (k / 2) / k

/-- `x` is the value of a series of the class `F_b`. -/
def IsFBValue (b : ℕ) (x : ℝ) : Prop :=
  ∃ (N : ℕ) (ρ : ℕ → ℚ), 0 < N ∧ (∀ k, ρ (k + N) = ρ k) ∧ HasSum (seriesTermB b ρ) x

/-! ## 3. Good primes -/

/-- A good prime for the root of unity `r` in base `b`: a prime ideal `P` of the algebraic
integers that contains `√b - r` and an odd rational prime `p` dividing neither `b` nor the
order of `r`. -/
def HasGoodPrimeB (b : ℕ) (r : ℂ) : Prop :=
  ∃ P : Ideal Aint, P.IsPrime ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ b ∧ ¬ p ∣ orderOf r ∧
    InP P (p : ℂ) ∧ InP P (tB b - r)

/-- Every root of unity other than `1, -1, i, -i` has a good prime in base `b`. -/
def GoodPrimesB (b : ℕ) : Prop :=
  ∀ r : ℂ, IsOfFinOrder r → r ^ 4 ≠ 1 → HasGoodPrimeB b r

/-- In base 5 the good primes of `Base5` are good primes in the present sense. -/
theorem goodPrimesB_five : GoodPrimesB 5 := by
  intro r hr h4
  have h1 : r ≠ 1 := fun h => h4 (by rw [h, one_pow])
  have h2 : r ≠ -1 := fun h => h4 (by rw [h]; norm_num)
  obtain ⟨P, hP, p, hp, hp2, hp5, hpr, hpP, hxP⟩ := Base5.goodPrimes5 r hr h1 h2
  refine ⟨P, hP, p, hp, hp2, ?_, hpr, hpP, ?_⟩
  · intro h
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
  · rw [tB_five]
    exact hxP

/-! ## 4. The size condition -/

/-- The size condition at `(b, m)`: the value `Φ_m(b)` of the `m`-th cyclotomic polynomial
exceeds `(√b + 1)^φ(m)`, and it exceeds `q (√b + 1)^φ(m)` for every prime `q` that divides
both `m` and `Φ_m(b)`.

It holds for every `b ≥ 6` and `m ≥ 3` (file `Size`), and it fails at `(b, m) = (5, 6)`,
where `Φ_6(5) = 21 = 3 · 7` and `3 (√5 + 1)² ≈ 31.4`. For a root of unity `r` with
`m = orderOf (r ^ 2) ≥ 3` it gives a good prime for `r` (file `Reduction`). -/
def SizeCond (b m : ℕ) : Prop :=
  (Real.sqrt (b : ℝ) + 1) ^ m.totient < (((cyclotomic m ℤ).eval (b : ℤ) : ℤ) : ℝ) ∧
    ∀ q : ℕ, q.Prime → q ∣ m → (q : ℤ) ∣ (cyclotomic m ℤ).eval (b : ℤ) →
      (q : ℝ) * (Real.sqrt (b : ℝ) + 1) ^ m.totient <
        (((cyclotomic m ℤ).eval (b : ℤ) : ℤ) : ℝ)

end BaseB

end PiFormula
