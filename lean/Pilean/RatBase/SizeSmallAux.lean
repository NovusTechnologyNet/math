/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.RatBase.SmallDefs

/-!
# The size condition for small rational bases: the analytic part

Three results, used by `SizeSmallAuxCert.lean` and `SizeSmall.lean`.

* **Lemma (M)** (`pow_totient_le_sq_cycValR`): for `p > q ≥ 1` and `m ≥ 3`,
  `(p² - p q + q²)^φ(m) ≤ Φ_m(p, q)²`. For a primitive `m`-th root of unity `μ` and `x = p/q`,
  `|x - μ|² = (x - 1)² + x |1 - μ|²`, and by the weighted inequality of the means
  `A + B y ≥ (A + B) y^(B/(A + B))`, so `|x - μ|² ≥ (x² - x + 1) (|1 - μ|²)^w` with
  `w = x/(x² - x + 1)`. The product over `μ` of the `|1 - μ|` is `Φ_m(1) ≥ 1`.

* **A bound for `m` from `φ(m)`** (`mul_prod_pred_le_of_totient_le`): if `φ(m) ≤ F` and
  `F + 2 ≤ 400`, then `m ∏ (ℓ - 1) ≤ F ∏ ℓ`, the products over the primes `ℓ < F + 2`. Indeed
  every prime factor `ℓ` of `m` has `ℓ - 1 ≤ φ(m)`, and `m ∏_{ℓ ∣ m} (ℓ - 1) = φ(m) ∏_{ℓ ∣ m} ℓ`.

* **The size condition for `φ(m) > F`** (`sizeCondR_of_lt_totient`): let `a/b ≥ √(p q)`,
  `s = b (p + q) + 2 a` (so `(√p + √q)² ≤ s/b`) and `D = (p² + q² - p q) b`. If
  `(F + 2)² s^(F+1) < D^(F+1)` and `(F + 3)² s ≤ (F + 2)² D`, then `(n + 1)² s^n < D^n` for every
  `n > F`, and so, by Lemma (M) and `ℓ ≤ φ(m) + 1` for a prime `ℓ ∣ m`, the size condition holds
  at every `m ≥ 3` with `φ(m) > F`. The hypothesis `ℓ ∣ Φ_m(p, q)` is not used here.
-/

@[expose] public section

open Polynomial

namespace PiFormula

namespace RatBase

/-! ## 1. Lemma (M) -/

/-- For a complex number `μ` of absolute value 1 and a real `x`:
`|x - μ|² = (x - 1)² + x |1 - μ|²`. -/
theorem sq_norm_ofReal_sub_eq {μ : ℂ} (x : ℝ) (hμ : ‖μ‖ = 1) :
    ‖(x : ℂ) - μ‖ ^ 2 = (x - 1) ^ 2 + x * ‖((1 : ℝ) : ℂ) - μ‖ ^ 2 := by
  have h1 : μ.re * μ.re + μ.im * μ.im = 1 := by
    have h := Complex.sq_norm μ
    rw [hμ, Complex.normSq_apply] at h
    linarith
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (1 - x) * h1

/-- The weighted inequality of the means, in the form `(A + B) y^(B/(A + B)) ≤ A + B y`. -/
theorem add_mul_rpow_le_add_mul {A B y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
    (hy : 0 ≤ y) : (A + B) * y ^ (B / (A + B)) ≤ A + B * y := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := A / (A + B)) (w₂ := B / (A + B))
    (p₁ := 1) (p₂ := y) (div_nonneg hA hAB.le) (div_nonneg hB hAB.le) zero_le_one hy
    (by field_simp)
  rw [Real.one_rpow, one_mul] at h
  calc (A + B) * y ^ (B / (A + B))
      ≤ (A + B) * (A / (A + B) * 1 + B / (A + B) * y) := mul_le_mul_of_nonneg_left h hAB.le
    _ = A + B * y := by field_simp

/-- `Φ_m(y) = ∏ (y - μ)` over the primitive `m`-th roots of unity `μ`. -/
theorem eval_cyclotomic_eq_prod_primitiveRoots {m : ℕ} (hm : m ≠ 0) (y : ℂ) :
    (cyclotomic m ℂ).eval y = ∏ μ ∈ primitiveRoots m ℂ, (y - μ) := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp m hm), eval_prod]
  simp

/-- For `m ≥ 3`, the absolute value of `Φ_m` at a real point, computed in `ℂ`, is its value. -/
theorem norm_eval_cyclotomic_ofReal_eq {m : ℕ} (hm : 3 ≤ m) (x : ℝ) :
    ‖(cyclotomic m ℂ).eval (x : ℂ)‖ = (cyclotomic m ℝ).eval x := by
  have h := (cyclotomic m ℝ).eval₂_at_apply Complex.ofRealHom x
  rw [← eval_map, map_cyclotomic] at h
  rw [Complex.ofRealHom_eq_coe, Complex.ofRealHom_eq_coe] at h
  rw [h, Complex.norm_real, Real.norm_of_nonneg (cyclotomic_pos (by omega) x).le]

/-- `Φ_m(1) ≥ 1` for `m ≥ 3`. -/
theorem one_le_eval_cyclotomic_one {m : ℕ} (hm : 3 ≤ m) :
    1 ≤ (cyclotomic m ℝ).eval 1 := by
  have h0 : (1 : ℤ) ≤ (cyclotomic m ℤ).eval 1 :=
    cyclotomic_pos (n := m) (by omega) (1 : ℤ)
  have h := eval_intCast_map (Int.castRingHom ℝ) (cyclotomic m ℤ) 1
  rw [map_cyclotomic, Int.cast_one, eq_intCast] at h
  rw [h]
  exact_mod_cast h0

/-- **Lemma (M) for the cyclotomic polynomial**: `(x² - x + 1)^φ(m) ≤ Φ_m(x)²` for a real
`x > 1` and `m ≥ 3`. -/
theorem pow_totient_le_sq_eval_cyclotomic {m : ℕ} {x : ℝ} (hm : 3 ≤ m) (hx : 1 < x) :
    (x ^ 2 - x + 1) ^ m.totient ≤ (cyclotomic m ℝ).eval x ^ 2 := by
  have hm0 : m ≠ 0 := by omega
  have hmpos : 0 < m := by omega
  have hEpos : 0 < x ^ 2 - x + 1 := by nlinarith
  have hw : 0 ≤ x / (x ^ 2 - x + 1) := div_nonneg (by linarith) hEpos.le
  have key : ∀ μ ∈ primitiveRoots m ℂ,
      (x ^ 2 - x + 1) * (‖((1 : ℝ) : ℂ) - μ‖ ^ 2) ^ (x / (x ^ 2 - x + 1)) ≤
        ‖(x : ℂ) - μ‖ ^ 2 := by
    intro μ hμ
    have hn := ((mem_primitiveRoots hmpos).1 hμ).norm'_eq_one hm0
    rw [sq_norm_ofReal_sub_eq x hn]
    have h := add_mul_rpow_le_add_mul (A := (x - 1) ^ 2) (B := x)
      (y := ‖((1 : ℝ) : ℂ) - μ‖ ^ 2) (sq_nonneg _) (by linarith) (by nlinarith) (sq_nonneg _)
    have e : (x - 1) ^ 2 + x = x ^ 2 - x + 1 := by ring
    rwa [e] at h
  have hprod := Finset.prod_le_prod₀ (s := primitiveRoots m ℂ)
    (fun μ _ => mul_nonneg hEpos.le (Real.rpow_nonneg (sq_nonneg _) _)) key
  rw [Finset.prod_mul_distrib, Finset.prod_const, Complex.card_primitiveRoots,
    Real.finsetProd_rpow _ _ (fun μ _ => sq_nonneg _), Finset.prod_pow, Finset.prod_pow,
    ← norm_prod, ← norm_prod, ← eval_cyclotomic_eq_prod_primitiveRoots hm0,
    ← eval_cyclotomic_eq_prod_primitiveRoots hm0, norm_eval_cyclotomic_ofReal_eq hm,
    norm_eval_cyclotomic_ofReal_eq hm] at hprod
  have h1 : (1 : ℝ) ≤ ((cyclotomic m ℝ).eval 1 ^ 2) ^ (x / (x ^ 2 - x + 1)) :=
    Real.one_le_rpow (one_le_pow₀ (one_le_eval_cyclotomic_one hm)) hw
  exact (le_mul_of_one_le_right (pow_nonneg hEpos.le _) h1).trans hprod

/-- `Φ_m(p, q) = Φ_m(p/q) q^φ(m)`, in the real numbers. -/
theorem cast_cycValR_eq_eval_div {p q : ℕ} (m : ℕ) (hq : 0 < q) :
    ((cycValR p q m : ℤ) : ℝ) =
      (cyclotomic m ℝ).eval ((p : ℝ) / q) * (q : ℝ) ^ m.totient := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← TauCeti.homogeneousCyclotomic_eq_eval_div_mul_pow m (p : ℝ) hq']
  simp [cycValR]

/-- **Lemma (M)**: `(p² - p q + q²)^φ(m) ≤ Φ_m(p, q)²` for `p > q ≥ 1` and `m ≥ 3`. -/
theorem pow_totient_le_sq_cycValR {p q m : ℕ} (hq : 0 < q) (hqp : q < p) (hm : 3 ≤ m) :
    ((p : ℝ) ^ 2 - p * q + (q : ℝ) ^ 2) ^ m.totient ≤ ((cycValR p q m : ℤ) : ℝ) ^ 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hx : 1 < (p : ℝ) / q := by
    rw [one_lt_div hq']
    exact_mod_cast hqp
  have h := pow_totient_le_sq_eval_cyclotomic hm hx
  have e : (p : ℝ) ^ 2 - p * q + (q : ℝ) ^ 2 =
      (((p : ℝ) / q) ^ 2 - (p : ℝ) / q + 1) * (q : ℝ) ^ 2 := by
    field_simp
  rw [cast_cycValR_eq_eval_div m hq, e, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
    mul_comm 2 m.totient]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- `Φ_m(p, q) > 0` for `p > q`. -/
theorem cast_cycValR_pos {p q : ℕ} (hqp : q < p) (m : ℕ) : (0 : ℝ) < ((cycValR p q m : ℤ) : ℝ) := by
  have h : 0 < cycValR p q m :=
    TauCeti.homogeneousCyclotomic_pos (Int.natCast_nonneg q) (by exact_mod_cast hqp) m
  exact_mod_cast h

/-! ## 2. A bound for `m` from `φ(m)` -/

/-- The primes below 400. -/
def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
    311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397]

theorem forall_mem_smallPrimes_prime : ∀ ℓ ∈ smallPrimes, ℓ.Prime := by
  simp only [smallPrimes, List.forall_mem_cons]
  norm_num

/-- Every member of `smallPrimes` is prime. -/
theorem prime_of_mem_smallPrimes {ℓ : ℕ} (h : ℓ ∈ smallPrimes) : ℓ.Prime :=
  forall_mem_smallPrimes_prime ℓ h

/-- Every prime below 400 is in `smallPrimes`. -/
theorem mem_smallPrimes_of_prime {ℓ : ℕ} (h : ℓ.Prime) (hlt : ℓ < 400) : ℓ ∈ smallPrimes := by
  interval_cases ℓ <;> first | decide | exact absurd h (by norm_num)

/-- The primes below `n`, for `n ≤ 400`. -/
def primesLt (n : ℕ) : List ℕ :=
  smallPrimes.filter (· < n)

/-- If `φ(m) ≤ F` then `m ∏ (ℓ - 1) ≤ F ∏ ℓ`, the products over the primes `ℓ < F + 2`. -/
theorem mul_prod_pred_le_of_totient_le {F m : ℕ} (hF : F + 2 ≤ 400) (hm : 0 < m)
    (h : m.totient ≤ F) :
    m * ((primesLt (F + 2)).map (· - 1)).prod ≤ F * (primesLt (F + 2)).prod := by
  have hnd : (primesLt (F + 2)).Nodup := List.Nodup.filter _ (by decide)
  have hsub : m.primeFactors ⊆ (primesLt (F + 2)).toFinset := by
    intro ℓ hℓ
    have hp := Nat.prime_of_mem_primeFactors hℓ
    have hd := Nat.dvd_of_mem_primeFactors hℓ
    have h1 := BaseB.pred_le_totient hp hm hd
    have h2 : ℓ < F + 2 := by omega
    rw [List.mem_toFinset, primesLt, List.mem_filter]
    exact ⟨mem_smallPrimes_of_prime hp (by omega), by simpa using h2⟩
  have hA : ((primesLt (F + 2)).map (· - 1)).prod =
      ∏ ℓ ∈ (primesLt (F + 2)).toFinset, (ℓ - 1) :=
    (List.prod_toFinset _ hnd).symm
  have hB : (primesLt (F + 2)).prod = ∏ ℓ ∈ (primesLt (F + 2)).toFinset, ℓ := by
    rw [List.prod_toFinset _ hnd]
    simp
  rw [hA, hB, ← Finset.prod_sdiff hsub, ← Finset.prod_sdiff hsub]
  calc m * ((∏ ℓ ∈ (primesLt (F + 2)).toFinset \ m.primeFactors, (ℓ - 1)) *
        ∏ ℓ ∈ m.primeFactors, (ℓ - 1))
      = (∏ ℓ ∈ (primesLt (F + 2)).toFinset \ m.primeFactors, (ℓ - 1)) *
          (m.totient * ∏ ℓ ∈ m.primeFactors, ℓ) := by
        rw [Nat.totient_mul_prod_primeFactors]
        ring
    _ ≤ (∏ ℓ ∈ (primesLt (F + 2)).toFinset \ m.primeFactors, ℓ) *
          (F * ∏ ℓ ∈ m.primeFactors, ℓ) :=
        Nat.mul_le_mul (Finset.prod_le_prod fun ℓ _ => Nat.sub_le ℓ 1)
          (Nat.mul_le_mul_right _ h)
    _ = F * ((∏ ℓ ∈ (primesLt (F + 2)).toFinset \ m.primeFactors, ℓ) *
          ∏ ℓ ∈ m.primeFactors, ℓ) := by
        ring

/-! ## 3. The size condition for `φ(m) > F` -/

/-- `(n + 1)² s^n < D^n` for every `n > F`, from the case `n = F + 1` and
`(F + 3)² s ≤ (F + 2)² D`. -/
theorem succ_sq_mul_pow_lt_pow {s D F : ℕ} (hbase : (F + 2) ^ 2 * s ^ (F + 1) < D ^ (F + 1))
    (hstep : (F + 3) ^ 2 * s ≤ (F + 2) ^ 2 * D) :
    ∀ n : ℕ, F + 1 ≤ n → (n + 1) ^ 2 * s ^ n < D ^ n := by
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with rfl | h
    · simp at hbase
    · exact h
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    have e1 : (n + 2) * (F + 2) = n * F + 2 * n + 2 * F + 4 := by ring
    have e2 : (n + 1) * (F + 3) = n * F + 3 * n + F + 3 := by ring
    have h1 : (n + 2) * (F + 2) ≤ (n + 1) * (F + 3) := by omega
    have h3 : ((n + 2) * (F + 2)) ^ 2 ≤ ((n + 1) * (F + 3)) ^ 2 := Nat.pow_le_pow_left h1 2
    have h4 : (F + 2) ^ 2 * ((n + 2) ^ 2 * s) ≤ (F + 2) ^ 2 * ((n + 1) ^ 2 * D) := by
      calc (F + 2) ^ 2 * ((n + 2) ^ 2 * s) = ((n + 2) * (F + 2)) ^ 2 * s := by ring
        _ ≤ ((n + 1) * (F + 3)) ^ 2 * s := Nat.mul_le_mul_right _ h3
        _ = (n + 1) ^ 2 * ((F + 3) ^ 2 * s) := by ring
        _ ≤ (n + 1) ^ 2 * ((F + 2) ^ 2 * D) := Nat.mul_le_mul_left _ hstep
        _ = (F + 2) ^ 2 * ((n + 1) ^ 2 * D) := by ring
    have h2 : (n + 2) ^ 2 * s ≤ (n + 1) ^ 2 * D :=
      Nat.le_of_mul_le_mul_left h4 (by positivity)
    calc (n + 1 + 1) ^ 2 * s ^ (n + 1) = ((n + 2) ^ 2 * s) * s ^ n := by ring
      _ ≤ ((n + 1) ^ 2 * D) * s ^ n := Nat.mul_le_mul_right _ h2
      _ = D * ((n + 1) ^ 2 * s ^ n) := by ring
      _ < D * D ^ n := mul_lt_mul_of_pos_left ih hD
      _ = D ^ (n + 1) := by ring

/-- `(√p + √q)² ≤ (b (p + q) + 2 a)/b` when `a/b ≥ √(p q)`, that is `p q b² ≤ a²`. -/
theorem sqrt_add_sqrt_sq_le {p q a b : ℕ} (hb : 0 < b) (hab : p * q * b ^ 2 ≤ a ^ 2) :
    (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ 2 ≤ ((b * (p + q) + 2 * a : ℕ) : ℝ) / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab' : (p : ℝ) * q * (b : ℝ) ^ 2 ≤ (a : ℝ) ^ 2 := by exact_mod_cast hab
  have hp2 : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  have hq2 : Real.sqrt (q : ℝ) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  have h1 : Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) ≤ (a : ℝ) / b := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg p), Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    exact hab'
  rw [le_div_iff₀ hb'] at h1 ⊢
  push_cast
  nlinarith

/-- For `φ(m) > F` and a real `0 ≤ L ≤ φ(m) + 1`: `L (√p + √q)^φ(m) < Φ_m(p, q)`. Here
`a/b ≥ √(p q)`, and `F` satisfies the two numerical conditions. -/
theorem mul_sqrt_add_sqrt_pow_lt_cycValR_of_lt_totient {p q a b F m : ℕ} {L : ℝ} (hq : 0 < q)
    (hqp : q < p) (hb : 0 < b) (hab : p * q * b ^ 2 ≤ a ^ 2)
    (hbase : (F + 2) ^ 2 * (b * (p + q) + 2 * a) ^ (F + 1) <
      ((p ^ 2 + q ^ 2 - p * q) * b) ^ (F + 1))
    (hstep : (F + 3) ^ 2 * (b * (p + q) + 2 * a) ≤ (F + 2) ^ 2 * ((p ^ 2 + q ^ 2 - p * q) * b))
    (hm : 3 ≤ m) (hF : F < m.totient) (hL0 : 0 ≤ L) (hL : L ≤ (m.totient : ℝ) + 1) :
    L * (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ m.totient < ((cycValR p q m : ℤ) : ℝ) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hkey := succ_sq_mul_pow_lt_pow hbase hstep m.totient hF
  have hkey' : ((m.totient : ℝ) + 1) ^ 2 * ((b * (p + q) + 2 * a : ℕ) : ℝ) ^ m.totient <
      (((p ^ 2 + q ^ 2 - p * q : ℕ) : ℝ) * b) ^ m.totient := by
    exact_mod_cast hkey
  have hD : ((p ^ 2 + q ^ 2 - p * q : ℕ) : ℝ) = (p : ℝ) ^ 2 - p * q + (q : ℝ) ^ 2 := by
    have hle : p * q ≤ p ^ 2 + q ^ 2 :=
      calc p * q ≤ p * p := Nat.mul_le_mul_left p hqp.le
        _ = p ^ 2 := (sq p).symm
        _ ≤ p ^ 2 + q ^ 2 := Nat.le_add_right _ _
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hS := sqrt_add_sqrt_sq_le (p := p) (q := q) hb hab
  have hM := pow_totient_le_sq_cycValR hq hqp hm
  have hΦ := cast_cycValR_pos hqp m
  refine lt_of_pow_lt_pow_left₀ 2 hΦ.le ?_
  rw [hD] at hkey'
  generalize ((b * (p + q) + 2 * a : ℕ) : ℝ) = s at hkey' hS
  have hX : 0 ≤ (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ 2 := sq_nonneg _
  calc (L * (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ m.totient) ^ 2
      = L ^ 2 * ((Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ 2) ^ m.totient := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m.totient 2]
    _ ≤ ((m.totient : ℝ) + 1) ^ 2 * (s / b) ^ m.totient :=
        mul_le_mul (pow_le_pow_left₀ hL0 hL 2) (pow_le_pow_left₀ hX hS _)
          (pow_nonneg hX _) (sq_nonneg _)
    _ < ((p : ℝ) ^ 2 - p * q + (q : ℝ) ^ 2) ^ m.totient := by
        rw [div_pow, ← mul_div_assoc, div_lt_iff₀ (pow_pos hb' _), ← mul_pow]
        exact hkey'
    _ ≤ ((cycValR p q m : ℤ) : ℝ) ^ 2 := hM

/-- **The size condition for `φ(m) > F`**, where `a/b ≥ √(p q)` and `F` satisfies the two
numerical conditions. -/
theorem sizeCondR_of_lt_totient {p q a b F m : ℕ} (hq : 0 < q) (hqp : q < p) (hb : 0 < b)
    (hab : p * q * b ^ 2 ≤ a ^ 2)
    (hbase : (F + 2) ^ 2 * (b * (p + q) + 2 * a) ^ (F + 1) <
      ((p ^ 2 + q ^ 2 - p * q) * b) ^ (F + 1))
    (hstep : (F + 3) ^ 2 * (b * (p + q) + 2 * a) ≤ (F + 2) ^ 2 * ((p ^ 2 + q ^ 2 - p * q) * b))
    (hm : 3 ≤ m) (hF : F < m.totient) : SizeCondR p q m := by
  refine ⟨?_, ?_⟩
  · have h := mul_sqrt_add_sqrt_pow_lt_cycValR_of_lt_totient (L := 1) hq hqp hb hab hbase hstep
      hm hF zero_le_one (by linarith [Nat.cast_nonneg (α := ℝ) m.totient])
    rwa [one_mul] at h
  · intro ℓ hℓ hℓm _
    refine mul_sqrt_add_sqrt_pow_lt_cycValR_of_lt_totient hq hqp hb hab hbase hstep hm hF
      (Nat.cast_nonneg ℓ) ?_
    have h1 := BaseB.pred_le_totient hℓ (by omega) hℓm
    have h2 : ℓ ≤ m.totient + 1 := by omega
    exact_mod_cast h2

end RatBase

end PiFormula
