module

public import Pilean.RatBase.SeriesR

/-!
# A rational base `p/q`: the four logarithms at `1, -1, i, -i`

With `x = √(q/p) = q/√(pq)`, the four numbers `1 - r x` for `r = 1, -1, i, -i` are the ones
that the good primes do not reach. This file proves that there is no multiplicative relation
among them, for coprime `p > q ≥ 1` other than `(p, q) = (3, 1)`.

* **Real part** (`log_indepR`). The three real numbers `log(1 - x)`, `log(1 + x)` and
  `log(1 + q/p)` are linearly independent over `ℤ`. With `u = √(pq)` and integers `z₁, z₂, s`
  the relation is
  `2 z₁ log(u - q) + 2 z₂ log(u + q) + s log(p + q) = (z₁ + z₂ + s) log p + (z₁ + z₂) log q`.
  - If `pq` is not a square, `((u + q)/(u - q))^(z₂ - z₁)` is rational, and a non-zero power
    of `(u + q)/(u - q) = (u + q)²/(q (p - q))` is irrational (`irrational_unitR_zpow`); so
    `z₁ = z₂ = z`. Then `(p - q)^(2z) (p + q)^s = p^(2z + s)`; a prime factor of `p` divides
    neither `p - q` nor `p + q` and gives `2z + s = 0`, and `((p - q)/(p + q))^(2z) = 1` gives
    `z = 0`.
  - If `pq` is a square, then `p = c²` and `q = d²` with `c > d ≥ 1` coprime, and the relation
    is `(c - d)^(2z₁) (c + d)^(2z₂) (c² + d²)^s = c^(2(z₁ + z₂ + s))`. A prime factor of `c`
    gives `z₁ + z₂ + s = 0`; an odd prime factor of `c² + d²` (there is one, since
    `c² + d² ≥ 5` is not divisible by 4) divides none of `c - d`, `c + d`, `c` and gives
    `s = 0`; then `((c - d)/(c + d))^(2z₁) = 1` gives `z₁ = 0`.
* **Unit circle** (`unitR_zpow_eq_one`). The number `w = (1 - i x)/(1 + i x)` is not a root of
  unity unless `(p, q) = (3, 1)`: `w + 1/w = 2(p - q)/(p + q)` is a rational number strictly
  between 0 and 2, and for a root of unity it would be an integer, so `p + q = 2(p - q)`,
  `p = 3q`, and `q = 1` as `p`, `q` are coprime.

In base 3 the second statement fails (`w` is a sixth root of unity): this is where the formulas
for `π√3` come from. For `q = 1` this file is `BaseB/ClassificationAux.lean`.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace RatBase

/-! ## 1. The real part when `pq` is a square -/

/-- For coprime `c > d ≥ 1` the number `c² + d²` has an odd prime factor. -/
theorem exists_odd_prime_dvd_sq_add_sq {c d : ℕ} (hd : 0 < d) (hdc : d < c)
    (hcop : Nat.Coprime c d) : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∣ c * c + d * d := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (c * c + d * d) with
    ⟨k, hk⟩ | ⟨ℓ, hℓ, hdv, ho⟩
  · exfalso
    have h5 : 5 ≤ c * c + d * d := by
      have h1 : 2 * 2 ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
      have h2 : 1 * 1 ≤ d * d := Nat.mul_le_mul hd hd
      omega
    have h4 : (c * c + d * d) % 4 ≠ 0 := by
      rcases Nat.even_or_odd' c with ⟨m, rfl | rfl⟩ <;>
        rcases Nat.even_or_odd' d with ⟨n, rfl | rfl⟩
      · exfalso
        have h2 : 2 ∣ Nat.gcd (2 * m) (2 * n) := Nat.dvd_gcd (Dvd.intro m rfl) (Dvd.intro n rfl)
        rw [hcop.gcd_eq_one] at h2
        omega
      · have : 2 * m * (2 * m) + (2 * n + 1) * (2 * n + 1) = 4 * (m * m + n * n + n) + 1 := by
          ring
        omega
      · have : (2 * m + 1) * (2 * m + 1) + 2 * n * (2 * n) = 4 * (m * m + m + n * n) + 1 := by
          ring
        omega
      · have : (2 * m + 1) * (2 * m + 1) + (2 * n + 1) * (2 * n + 1) =
            4 * (m * m + m + n * n + n) + 2 := by ring
        omega
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · rw [pow_zero] at hk
        omega
      · rw [pow_one] at hk
        omega
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have h2 : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
    omega
  · refine ⟨ℓ, hℓ, ?_, hdv⟩
    rintro rfl
    exact absurd ho (by decide)

/-- The case `p = c²`, `q = d²`, with `c = d + e`: the relation
`2 z₁ log(c - d) + 2 z₂ log(c + d) + s log(c² + d²) = 2 (z₁ + z₂ + s) log c` has only the zero
solution. -/
theorem log_rel_squareR {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hcop : Nat.Coprime (d + e) d)
    {z₁ z₂ s : ℤ}
    (H : 2 * (z₁ : ℝ) * Real.log (e : ℝ) + 2 * z₂ * Real.log ((d + e + d : ℕ) : ℝ) +
        s * Real.log (((d + e) * (d + e) + d * d : ℕ) : ℝ) -
        2 * (z₁ + z₂ + s) * Real.log ((d + e : ℕ) : ℝ) = 0) : z₁ = 0 ∧ z₂ = 0 ∧ s = 0 := by
  have H' := H
  push_cast at H'
  have hnd : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ d + e → ¬ ℓ ∣ d := fun ℓ hℓ h1 h2 =>
    hℓ.one_lt.ne' (Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))
  have hmul : ∀ ℓ : ℕ, ℓ.Prime → ∀ a : ℕ, ℓ ∣ a * a → ℓ ∣ a := fun ℓ hℓ a h =>
    (hℓ.dvd_mul.1 h).elim id id
  -- a prime factor of `c`
  have hp := Nat.minFac_prime (show d + e ≠ 1 by omega)
  have hpc : (d + e).minFac ∣ d + e := Nat.minFac_dvd _
  have e4 : -(2 * (z₁ + z₂ + s)) = 0 :=
    BaseB.int_eq_zero_of_log_rel (a₁ := e) (a₂ := d + e + d)
      (a₃ := (d + e) * (d + e) + d * d) (a₄ := d + e) (e₁ := 2 * z₁) (e₂ := 2 * z₂) (e₃ := s)
      he (by omega) (by positivity) (by omega) hp
      (fun h => hnd _ hp hpc ((Nat.dvd_add_left h).1 hpc))
      (fun h => hnd _ hp hpc ((Nat.dvd_add_right hpc).1 h))
      (fun h => hnd _ hp hpc (hmul _ hp d ((Nat.dvd_add_right (hpc.mul_right _)).1 h)))
      hpc (by push_cast; linear_combination H')
  -- an odd prime factor of `c² + d²`
  obtain ⟨ℓ, hℓ, hℓ2, hℓd⟩ := exists_odd_prime_dvd_sq_add_sq (c := d + e) hd (by omega) hcop
  have hℓ2' : ¬ ℓ ∣ 2 := fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h)
  have hℓc : ¬ ℓ ∣ d + e := fun h =>
    hnd ℓ hℓ h (hmul ℓ hℓ d ((Nat.dvd_add_right (h.mul_right _)).1 hℓd))
  have hℓnd : ¬ ℓ ∣ d := fun h =>
    hℓc (hmul ℓ hℓ (d + e) ((Nat.dvd_add_left (h.mul_right _)).1 hℓd))
  have hkey : ¬ ℓ ∣ e * (d + e + d) := fun h => by
    have hid : (d + e) * (d + e) + d * d = e * (d + e + d) + 2 * (d * d) := by ring
    have h1 := hℓd
    rw [hid] at h1
    rcases hℓ.dvd_mul.1 ((Nat.dvd_add_right h).1 h1) with h2 | h2
    · exact hℓ2' h2
    · exact hℓnd (hmul ℓ hℓ d h2)
  have es : s = 0 :=
    BaseB.int_eq_zero_of_log_rel (a₁ := e) (a₂ := d + e + d) (a₃ := d + e)
      (a₄ := (d + e) * (d + e) + d * d) (e₁ := 2 * z₁) (e₂ := 2 * z₂)
      (e₃ := -(2 * (z₁ + z₂ + s)))
      he (by omega) (by omega) (by positivity) hℓ
      (fun h => hkey (h.mul_right _)) (fun h => hkey (h.mul_left _)) hℓc hℓd
      (by push_cast; linear_combination H')
  -- what is left is `2 z₁ (log(c - d) - log(c + d)) = 0`
  have hz2 : z₂ = -z₁ := by omega
  subst hz2
  subst es
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hlt : Real.log (e : ℝ) < Real.log ((d : ℝ) + e + d) :=
    Real.log_lt_log he' (by linarith)
  have h0 : (z₁ : ℝ) * (Real.log (e : ℝ) - Real.log ((d : ℝ) + e + d)) = 0 := by
    push_cast at H'
    linear_combination H' / 2
  rcases mul_eq_zero.1 h0 with h | h
  · have hz1 : z₁ = 0 := by exact_mod_cast h
    exact ⟨hz1, by omega, rfl⟩
  · linarith

/-! ## 2. The real part when `pq` is not a square -/

theorem sqrt_add_nat_pow {m q : ℕ} (hq : 0 < q) (n : ℕ) : ∃ x y : ℕ,
    (Real.sqrt (m : ℝ) + q) ^ n = x + y * Real.sqrt (m : ℝ) ∧ 0 < x ∧ (0 < n → 0 < y) := by
  induction n with
  | zero => exact ⟨1, 0, by simp, by norm_num, by simp⟩
  | succ n ih =>
    obtain ⟨x, y, h, hx, -⟩ := ih
    refine ⟨x * q + m * y, x + y * q, ?_, by positivity, fun _ => by omega⟩
    rw [pow_succ, h]
    push_cast
    linear_combination (y : ℝ) * Real.mul_self_sqrt (Nat.cast_nonneg m)

/-- `q < √(pq)` for `0 < q < p`. -/
theorem natCast_lt_sqrt_mul {p q : ℕ} (hq : 0 < q) (hqp : q < p) :
    (q : ℝ) < Real.sqrt ((p * q : ℕ) : ℝ) := by
  rw [Real.lt_sqrt (Nat.cast_nonneg q)]
  exact_mod_cast (by nlinarith : q ^ 2 < p * q)

/-- If `pq` is not a square, a non-zero integer power of `(√(pq) + q)/(√(pq) - q)` is
irrational. -/
theorem irrational_unitR_zpow {p q : ℕ} (hq : 0 < q) (hqp : q < p) (hsq : ¬ IsSquare (p * q))
    {C : ℤ} (hC : C ≠ 0) :
    Irrational (((Real.sqrt ((p * q : ℕ) : ℝ) + q) / (Real.sqrt ((p * q : ℕ) : ℝ) - q)) ^ C) := by
  have hirr : Irrational (Real.sqrt ((p * q : ℕ) : ℝ)) := irrational_sqrt_natCast_iff.2 hsq
  have hqU := natCast_lt_sqrt_mul hq hqp
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = Real.sqrt ((p * q : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hU] at hirr hqU ⊢
  have ht : U * U = (p : ℝ) * q := by
    rw [hU, Real.mul_self_sqrt (Nat.cast_nonneg _), Nat.cast_mul]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqp' : (q : ℝ) < p := by exact_mod_cast hqp
  have hpq1 : ((q * (p - q) : ℕ) : ℝ) = (q : ℝ) * ((p : ℝ) - q) := by
    rw [Nat.cast_mul, Nat.cast_sub hqp.le]
  have key : ∀ n : ℕ, 0 < n → Irrational (((U + q) / (U - q)) ^ n) := by
    intro n hn
    obtain ⟨x, y, h, -, hy⟩ := sqrt_add_nat_pow (m := p * q) hq (2 * n)
    rw [← hU] at h
    have e : ((U + q) / (U - q)) ^ n = (x + y * U) / (((q * (p - q)) ^ n : ℕ) : ℝ) := by
      rw [← h, pow_mul, Nat.cast_pow, hpq1, ← div_pow]
      congr 1
      rw [div_eq_div_iff (by linarith) (mul_pos hq' (by linarith)).ne']
      linear_combination (-(U + q)) * ht
    rw [e]
    exact ((hirr.natCast_mul (hy (by omega)).ne').natCast_add x).div_natCast
      (pow_ne_zero n (Nat.mul_pos hq (Nat.sub_pos_of_lt hqp)).ne')
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg C
  · rw [zpow_natCast]
    exact key n (by omega)
  · rw [zpow_neg, zpow_natCast]
    exact (key n (by omega)).inv

/-- The case where `pq` is not a square: the relation
`2 z₁ log(u - q) + 2 z₂ log(u + q) + s log(p + q) = (z₁ + z₂ + s) log p + (z₁ + z₂) log q`,
`u = √(pq)`, has only the zero solution. -/
theorem log_rel_nonsquareR {p q : ℕ} (hq : 0 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (hsq : ¬ IsSquare (p * q)) {z₁ z₂ s : ℤ}
    (H : 2 * (z₁ : ℝ) * Real.log (Real.sqrt ((p * q : ℕ) : ℝ) - q) +
        2 * z₂ * Real.log (Real.sqrt ((p * q : ℕ) : ℝ) + q) + s * Real.log ((p : ℝ) + q) -
        (z₁ + z₂ + s) * Real.log (p : ℝ) - (z₁ + z₂) * Real.log (q : ℝ) = 0) :
    z₁ = 0 ∧ z₂ = 0 ∧ s = 0 := by
  have hqU := natCast_lt_sqrt_mul hq hqp
  have hirr : ∀ C : ℤ, C ≠ 0 → Irrational (((Real.sqrt ((p * q : ℕ) : ℝ) + q) /
      (Real.sqrt ((p * q : ℕ) : ℝ) - q)) ^ C) := fun C hC => irrational_unitR_zpow hq hqp hsq hC
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = Real.sqrt ((p * q : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hU] at H hqU hirr
  have ht : U * U = (p : ℝ) * q := by
    rw [hU, Real.mul_self_sqrt (Nat.cast_nonneg _), Nat.cast_mul]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqp' : (q : ℝ) < p := by exact_mod_cast hqp
  have hm : 0 < U - q := by linarith
  have hp : 0 < U + q := by linarith
  have hsum : Real.log (U - q) + Real.log (U + q) =
      Real.log (q : ℝ) + Real.log ((p : ℝ) - q) := by
    rw [← Real.log_mul hm.ne' hp.ne', ← Real.log_mul hq'.ne' (sub_pos.2 hqp').ne']
    congr 1
    linear_combination ht
  have hdiff : Real.log (U + q) - Real.log (U - q) = Real.log ((U + q) / (U - q)) :=
    (Real.log_div hp.ne' hm.ne').symm
  have hu : 0 < (U + q) / (U - q) := div_pos hp hm
  -- `z₁ = z₂`, since a non-zero power of `(u + q)/(u - q)` is irrational
  have key : ((z₁ + z₂ : ℤ) : ℝ) * Real.log ((p : ℝ) - q) +
      ((z₂ - z₁ : ℤ) : ℝ) * Real.log ((U + q) / (U - q)) +
      (s : ℝ) * Real.log ((p : ℝ) + q) + ((-(z₁ + z₂ + s) : ℤ) : ℝ) * Real.log (p : ℝ) = 0 := by
    push_cast
    linear_combination H - ((z₁ : ℝ) + z₂) * hsum + ((z₁ : ℝ) - z₂) * hdiff
  have hz : ∀ (x : ℝ), 0 < x → ∀ n : ℤ, Real.exp (n * Real.log x) = x ^ n :=
    fun x hx n => by rw [mul_comm, Real.exp_mul, Real.exp_log hx, Real.rpow_intCast]
  have hexp : ((p : ℝ) - q) ^ (z₁ + z₂) * ((U + q) / (U - q)) ^ (z₂ - z₁) *
      ((p : ℝ) + q) ^ s * (p : ℝ) ^ (-(z₁ + z₂ + s)) = 1 := by
    have h' := congrArg Real.exp key
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_zero, hz _ (by linarith), hz _ hu,
      hz _ (by linarith), hz _ (by linarith)] at h'
    exact h'
  have h12 : z₂ - z₁ = 0 := by
    by_contra hC
    apply hirr _ hC
    refine ⟨(((p : ℚ) - q) ^ (z₁ + z₂) * ((p : ℚ) + q) ^ s *
      (p : ℚ) ^ (-(z₁ + z₂ + s)))⁻¹, ?_⟩
    push_cast
    exact (eq_inv_of_mul_eq_one_left (by linear_combination hexp)).symm
  obtain rfl : z₂ = z₁ := by omega
  -- a prime factor of `p`
  have hpq1 : ((p - q : ℕ) : ℝ) = (p : ℝ) - q := Nat.cast_sub hqp.le
  have hpr := Nat.minFac_prime (show p ≠ 1 by omega)
  have hpp : p.minFac ∣ p := Nat.minFac_dvd p
  have hnq : ¬ p.minFac ∣ q := fun h =>
    hpr.one_lt.ne' (Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpp h))
  have e4 : -(2 * z₂ + s) = 0 :=
    BaseB.int_eq_zero_of_log_rel (a₁ := p - q) (a₂ := p + q) (a₃ := 1) (a₄ := p) (e₁ := 2 * z₂)
      (e₂ := s) (e₃ := 0) (by omega) (by omega) one_pos (by omega) hpr
      (fun h => hnq (by
        have h1 := Nat.dvd_sub hpp h
        rwa [Nat.sub_sub_self hqp.le] at h1))
      (fun h => hnq ((Nat.dvd_add_right hpp).1 h)) (fun h => hpr.one_lt.ne' (Nat.dvd_one.1 h))
      hpp (by rw [hpq1]; push_cast; linear_combination H - 2 * (z₂ : ℝ) * hsum)
  -- what is left is `2 z (log(p - q) - log(p + q)) = 0`
  have hs : s = -(2 * z₂) := by omega
  subst hs
  have hlt : Real.log ((p : ℝ) - q) < Real.log ((p : ℝ) + q) :=
    Real.log_lt_log (by linarith) (by linarith)
  have h0 : (z₂ : ℝ) * (Real.log ((p : ℝ) - q) - Real.log ((p : ℝ) + q)) = 0 := by
    push_cast at H
    linear_combination H / 2 - (z₂ : ℝ) * hsum
  rcases mul_eq_zero.1 h0 with h | h
  · have hz1 : z₂ = 0 := by exact_mod_cast h
    exact ⟨hz1, hz1, by omega⟩
  · linarith

/-! ## 3. The real part -/

/-- **`log(1 - x)`, `log(1 + x)` and `log(1 + q/p)`, `x = √(q/p) = q/√(pq)`, are linearly
independent over `ℤ`**, for coprime `p > q ≥ 1`. (The factors 2 are those of the application:
the real part of `Log(1 ∓ i x)` is `log(1 + q/p)/2`.) -/
theorem log_indepR {p q : ℕ} (hq : 0 < q) (hqp : q < p) (hcop : Nat.Coprime p q) {z₁ z₂ s : ℤ}
    (h : 2 * (z₁ : ℝ) * Real.log (1 - q / Real.sqrt ((p * q : ℕ) : ℝ)) +
        2 * z₂ * Real.log (1 + q / Real.sqrt ((p * q : ℕ) : ℝ)) +
        s * Real.log (1 + (q : ℝ) / p) = 0) : z₁ = 0 ∧ z₂ = 0 ∧ s = 0 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hp' : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  by_cases hsq : IsSquare (p * q)
  · -- `p = c²`, `q = d²`, `c = d + e`
    obtain ⟨m, hm⟩ := hsq
    have hunit : IsUnit (gcd p q) := Nat.isUnit_iff.2 hcop
    have hunit' : IsUnit (gcd q p) := Nat.isUnit_iff.2 hcop.symm
    obtain ⟨c, hc⟩ : ∃ c, p = c ^ 2 :=
      exists_eq_pow_of_mul_eq_pow hunit (by rw [hm]; ring : p * q = m ^ 2)
    obtain ⟨d, hd⟩ : ∃ d, q = d ^ 2 :=
      exists_eq_pow_of_mul_eq_pow hunit' (by rw [mul_comm, hm]; ring : q * p = m ^ 2)
    have hdpos : 0 < d := Nat.pos_of_ne_zero fun h0 => by
      rw [hd, h0] at hq
      exact absurd hq (by norm_num)
    have hdc : d < c := by
      rw [hc, hd] at hqp
      exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le c) hqp
    obtain ⟨e, he⟩ : ∃ e, c = d + e := ⟨c - d, by omega⟩
    have hepos : 0 < e := by omega
    have hcop' : Nat.Coprime (d + e) d := by
      rw [hc, hd, he] at hcop
      exact Nat.Coprime.coprime_dvd_left (dvd_pow_self _ two_ne_zero)
        (Nat.Coprime.coprime_dvd_right (dvd_pow_self _ two_ne_zero) hcop)
    have hd' : (0 : ℝ) < d := by exact_mod_cast hdpos
    have he' : (0 : ℝ) < e := by exact_mod_cast hepos
    have hc0 : (0 : ℝ) < (d : ℝ) + e := by linarith
    have hpR : (p : ℝ) = ((d : ℝ) + e) ^ 2 := by
      rw [hc, he]
      push_cast
      ring
    have hqR : (q : ℝ) = (d : ℝ) ^ 2 := by
      rw [hd]
      push_cast
      ring
    have hUR : Real.sqrt ((p * q : ℕ) : ℝ) = ((d : ℝ) + e) * d := by
      rw [Nat.cast_mul, hpR, hqR, ← mul_pow]
      exact Real.sqrt_sq (by positivity)
    rw [hUR, hqR, hpR] at h
    have l1 : Real.log (1 - (d : ℝ) ^ 2 / (((d : ℝ) + e) * d)) =
        Real.log (e : ℝ) - Real.log ((d : ℝ) + e) := by
      rw [← Real.log_div he'.ne' hc0.ne']
      congr 1
      field_simp
      ring
    have l2 : Real.log (1 + (d : ℝ) ^ 2 / (((d : ℝ) + e) * d)) =
        Real.log ((d : ℝ) + e + d) - Real.log ((d : ℝ) + e) := by
      rw [← Real.log_div (by linarith) hc0.ne']
      congr 1
      field_simp
    have l3 : Real.log (1 + (d : ℝ) ^ 2 / ((d : ℝ) + e) ^ 2) =
        Real.log (((d : ℝ) + e) * ((d : ℝ) + e) + d * d) - 2 * Real.log ((d : ℝ) + e) := by
      have h2 : 2 * Real.log ((d : ℝ) + e) = Real.log (((d : ℝ) + e) ^ 2) := by
        rw [Real.log_pow]
        push_cast
        ring
      rw [h2, ← Real.log_div (by positivity) (by positivity)]
      congr 1
      field_simp
    rw [l1, l2, l3] at h
    exact log_rel_squareR hdpos hepos hcop' (by push_cast; linear_combination h)
  · have hqU := natCast_lt_sqrt_mul hq hqp
    have hlogU : Real.log (Real.sqrt ((p * q : ℕ) : ℝ)) =
        (Real.log (p : ℝ) + Real.log (q : ℝ)) / 2 := by
      rw [Real.log_sqrt (Nat.cast_nonneg _), Nat.cast_mul, Real.log_mul hp'.ne' hq'.ne']
    have hU0 : 0 < Real.sqrt ((p * q : ℕ) : ℝ) := by linarith
    have e1 : Real.log (1 - q / Real.sqrt ((p * q : ℕ) : ℝ)) =
        Real.log (Real.sqrt ((p * q : ℕ) : ℝ) - q) -
          (Real.log (p : ℝ) + Real.log (q : ℝ)) / 2 := by
      rw [← hlogU, ← Real.log_div (by linarith) hU0.ne']
      congr 1
      field_simp
    have e2 : Real.log (1 + q / Real.sqrt ((p * q : ℕ) : ℝ)) =
        Real.log (Real.sqrt ((p * q : ℕ) : ℝ) + q) -
          (Real.log (p : ℝ) + Real.log (q : ℝ)) / 2 := by
      rw [← hlogU, ← Real.log_div (by linarith) hU0.ne']
      congr 1
      field_simp
    have e3 : Real.log (1 + (q : ℝ) / p) = Real.log ((p : ℝ) + q) - Real.log (p : ℝ) := by
      rw [← Real.log_div (by linarith) hp'.ne']
      congr 1
      field_simp
    rw [e1, e2, e3] at h
    exact log_rel_nonsquareR hq hqp hcop hsq (by linear_combination h)

/-! ## 4. The four numbers `1 - r x`, `r⁴ = 1` -/

theorem xRat_eq_ofReal (p q : ℕ) :
    xRat p q = (((q : ℝ) / Real.sqrt ((p * q : ℕ) : ℝ) : ℝ) : ℂ) := by
  rw [xRat, BaseB.tB]
  push_cast
  rfl

/-- `1 - x` is the positive real number `1 - q/√(pq)`. -/
theorem log_re_oneR {p q : ℕ} (hq : 0 < q) (hqp : q < p) :
    (Complex.log (1 - 1 * xRat p q)).re = Real.log (1 - q / Real.sqrt ((p * q : ℕ) : ℝ)) := by
  have hqU := natCast_lt_sqrt_mul hq hqp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hpos : (0 : ℝ) < 1 - q / Real.sqrt ((p * q : ℕ) : ℝ) := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hqU
  have e : (1 - 1 * xRat p q : ℂ) = ((1 - q / Real.sqrt ((p * q : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [xRat_eq_ofReal]
    push_cast
    ring
  rw [Complex.log_re, e, Complex.norm_real, Real.norm_of_nonneg hpos.le]

/-- `1 + x` is the positive real number `1 + q/√(pq)`. -/
theorem log_re_neg_oneR (p q : ℕ) :
    (Complex.log (1 - (-1) * xRat p q)).re =
      Real.log (1 + q / Real.sqrt ((p * q : ℕ) : ℝ)) := by
  have hpos : (0 : ℝ) < 1 + q / Real.sqrt ((p * q : ℕ) : ℝ) := by positivity
  have e : (1 - (-1) * xRat p q : ℂ) = ((1 + q / Real.sqrt ((p * q : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [xRat_eq_ofReal]
    push_cast
    ring
  rw [Complex.log_re, e, Complex.norm_real, Real.norm_of_nonneg hpos.le]

private theorem sq_div_sqrt_mul {p q : ℕ} (hq : 0 < q) (hqp : q < p) :
    ((q : ℝ) / Real.sqrt ((p * q : ℕ) : ℝ)) ^ 2 = (q : ℝ) / p := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_mul]
  field_simp

private theorem norm_one_add_mul_I_R {p q : ℕ} (y : ℝ) (hy : y ^ 2 = (q : ℝ) / p) :
    Real.log ‖((1 : ℝ) : ℂ) + (y : ℂ) * I‖ = Real.log (1 + (q : ℝ) / p) / 2 := by
  rw [Complex.norm_add_mul_I, one_pow, hy, Real.log_sqrt (by positivity)]

/-- `|1 - i x|² = 1 + q/p`. -/
theorem log_re_IR {p q : ℕ} (hq : 0 < q) (hqp : q < p) :
    (Complex.log (1 - I * xRat p q)).re = Real.log (1 + (q : ℝ) / p) / 2 := by
  have e : (1 - I * xRat p q : ℂ) =
      ((1 : ℝ) : ℂ) + ((-((q : ℝ) / Real.sqrt ((p * q : ℕ) : ℝ)) : ℝ) : ℂ) * I := by
    rw [xRat_eq_ofReal]
    push_cast
    ring
  rw [Complex.log_re, e]
  refine norm_one_add_mul_I_R _ ?_
  rw [neg_sq, sq_div_sqrt_mul hq hqp]

/-- `|1 + i x|² = 1 + q/p`. -/
theorem log_re_neg_IR {p q : ℕ} (hq : 0 < q) (hqp : q < p) :
    (Complex.log (1 - (-I) * xRat p q)).re = Real.log (1 + (q : ℝ) / p) / 2 := by
  have e : (1 - (-I) * xRat p q : ℂ) =
      ((1 : ℝ) : ℂ) + (((q : ℝ) / Real.sqrt ((p * q : ℕ) : ℝ) : ℝ) : ℂ) * I := by
    rw [xRat_eq_ofReal]
    push_cast
    ring
  rw [Complex.log_re, e]
  exact norm_one_add_mul_I_R _ (sq_div_sqrt_mul hq hqp)

/-- **`(1 - i x)/(1 + i x)` is not a root of unity** unless `(p, q) = (3, 1)`: if
`((1 - i x)/(1 + i x))^n = 1` then `n = 0`. The number `w = (1 - i x)/(1 + i x)` has
`w + 1/w = 2(p - q)/(p + q)`, strictly between 0 and 2; if it is an integer then `p = 3q`. -/
theorem unitR_zpow_eq_one {p q : ℕ} (hq : 0 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (h31 : ¬ (p = 3 ∧ q = 1)) {n : ℤ}
    (h : ((1 - I * xRat p q) / (1 - (-I) * xRat p q)) ^ n = 1) : n = 0 := by
  by_contra hn
  have hnI : IsOfFinOrder (-I) := by
    rw [← Complex.inv_I]
    exact isOfFinOrder_inv' isOfFinOrder_I
  have h1 : 1 - I * xRat p q ≠ 0 := wR_ne_zero hq hqp isOfFinOrder_I
  have h2 : 1 - (-I) * xRat p q ≠ 0 := wR_ne_zero hq hqp hnI
  obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = (1 - I * xRat p q) / (1 - (-I) * xRat p q) := ⟨_, rfl⟩
  rw [← hwdef] at h
  have hfin : IsOfFinOrder w := by
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, by omega, ?_⟩
      rwa [zpow_natCast] at h
    · refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, by omega, ?_⟩
      rwa [zpow_neg, zpow_natCast, inv_eq_one] at h
  have hint : IsIntegral ℤ (w + w⁻¹) :=
    (isIntegral_of_finOrder hfin).add (isIntegral_of_finOrder (isOfFinOrder_inv' hfin))
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpq0 : (p : ℂ) + q ≠ 0 := by exact_mod_cast (by omega : p + q ≠ 0)
  have hx : (p : ℂ) * xRat p q ^ 2 = q := by
    rw [xRat_sq hq hqp]
    field_simp
  have hval : w + w⁻¹ = algebraMap ℚ ℂ (2 * ((p : ℚ) - q) / ((p : ℚ) + q)) := by
    rw [hwdef, inv_div, div_add_div _ _ h2 h1, eq_ratCast]
    push_cast
    rw [div_eq_div_iff (mul_ne_zero h2 h1) hpq0]
    linear_combination (-4) * hx + 4 * (p : ℂ) * xRat p q ^ 2 * Complex.I_sq
  rw [hval, isIntegral_algebraMap_iff] at hint
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hqpQ : (q : ℚ) < (p : ℚ) := by exact_mod_cast hqp
  have hk' : (k : ℚ) * ((p : ℚ) + q) = 2 * ((p : ℚ) - q) := by
    rw [eq_intCast] at hk
    rw [hk, div_mul_cancel₀ _ (by linarith : (p : ℚ) + q ≠ 0)]
  have hk1 : (0 : ℚ) < (k : ℚ) := by
    by_contra hle
    push Not at hle
    nlinarith
  have hk2 : (k : ℚ) < 2 := by
    by_contra hle
    push Not at hle
    nlinarith
  have hk1' : (0 : ℤ) < k := by exact_mod_cast hk1
  have hk2' : k < 2 := by exact_mod_cast hk2
  obtain rfl : k = 1 := by omega
  have hp3 : p = 3 * q := by
    have h3 : (p : ℚ) = 3 * q := by
      push_cast at hk'
      linarith
    exact_mod_cast h3
  have hq1 : q = 1 := by
    have hdvd : q ∣ Nat.gcd p q := Nat.dvd_gcd ⟨3, by omega⟩ dvd_rfl
    rw [hcop.gcd_eq_one] at hdvd
    exact Nat.dvd_one.1 hdvd
  exact h31 ⟨by omega, hq1⟩

end RatBase

end PiFormula
