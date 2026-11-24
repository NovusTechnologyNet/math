/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Base5.Defs

/-!
# Base 5: the ring `ℤ[ζ]` of fifth roots of unity, with its norm to `ℤ`

This file prepares `Base5/Halves.lean`. It is the analogue for base 5 of the part of
`Base3/Halves.lean` that works in the Eisenstein integers.

* `Gold = ℤ[φ]`, `φ² = 1 + φ`, with `tR = 2φ - 1`, `tR² = 5`, and `cR = φ - 1`.
* `Cyc5 = ℤ[φ][ζ]`, `ζ² = cR ζ - 1`: the ring `ℤ[ζ]` for a primitive fifth root of unity
  `ζ` (`zS`), which contains `t = √5` (`tS`).
* `N5 : Cyc5 →* ℤ`: the norm, taken in two steps.

Main results, for `u` a primitive fifth root of unity of norm 1 in `Cyc5`:

1. `norm_twist5`: `N(x^(5b) - 1) = ∏_{j<5} N((u^j x)^b - 1)` for `5 ∤ b`.
2. `norm_cyclotomic_mul_five`: `N(Φ_{5m}(x)) = ∏_{j=1}^{4} N(Φ_m(u^j x))` for `5 ∤ m`.
3. `norm_sub_one_bounds5`: if the norm of `y` to `ℤ[φ]` is the integer `s²`, then
   `(s - 1)⁴ ≤ N(y - 1) ≤ (s + 1)⁴`. This uses the two real embeddings of `ℤ[φ]`.
4. `lower_bound5`, `half_lower5`: `25 N(Φ_m(z)) ≥ 25^φ(m)` for odd `m`.
5. `norm_z_th`: `N(ζ t^h - 1) = L5 h` and `N(ζ² t^h - 1) = M5 h` for odd `h`.
-/

@[expose] public section

open Polynomial

namespace PiFormula

namespace Base5

/-! ## 1. The rings -/

/-- `ℤ[φ]`, where `φ² = 1 + φ` (the golden ratio). -/
abbrev Gold : Type := QuadraticAlgebra ℤ 1 1

/-- `t = 2φ - 1`, a square root of 5 in `ℤ[φ]`. -/
def tR : Gold := ⟨-1, 2⟩

/-- `c = φ - 1`; in `ℤ[ζ]` it is `ζ + ζ⁻¹`. -/
def cR : Gold := ⟨-1, 1⟩

/-- `ℤ[ζ]` for a primitive fifth root of unity `ζ`, as `ℤ[φ][ζ]` with `ζ² = cζ - 1`. -/
abbrev Cyc5 : Type := QuadraticAlgebra Gold (-1) cR

/-- `ζ`. -/
def zS : Cyc5 := ⟨0, 1⟩

/-- `t = √5` in `ℤ[ζ]`. -/
def tS : Cyc5 := algebraMap Gold Cyc5 tR

/-- The norm from `ℤ[ζ]` to `ℤ`, taken in two steps. -/
def N5 : Cyc5 →* ℤ :=
  (QuadraticAlgebra.norm (R := ℤ) (a := 1) (b := 1)).comp
    (QuadraticAlgebra.norm (R := Gold) (a := -1) (b := cR))

theorem N5_apply (x : Cyc5) : N5 x = (QuadraticAlgebra.norm x).norm := rfl

theorem N5_star (x : Cyc5) : N5 (star x) = N5 x := by
  rw [N5_apply, N5_apply, QuadraticAlgebra.norm_star]

theorem gold_norm_eq (r : Gold) : r.norm = r.re ^ 2 + r.re * r.im - r.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

theorem tR_sq : tR ^ 2 = 5 := by
  ext <;> simp [tR, sq]

theorem star_tR : star tR = -tR := by
  ext <;> simp [tR]

theorem zS_sq : zS ^ 2 = ⟨-1, cR⟩ := by
  ext <;> simp [zS, sq]

theorem zS_rel : zS ^ 4 + zS ^ 3 + zS ^ 2 + zS + 1 = 0 := by decide

theorem norm_zS : zS.norm = 1 := by
  simp [zS, QuadraticAlgebra.norm_def]

theorem tS_sq : tS ^ 2 = 5 := by
  rw [tS, ← map_pow, tR_sq, map_ofNat]

theorem norm_tS : tS.norm = 5 := by
  rw [tS, QuadraticAlgebra.norm_algebraMap, tR_sq]

theorem star_tS : star tS = tS := by
  ext <;> simp [tS]

/-! ## 2. Fifth roots of unity -/

theorem pow_five_eq_one {u : Cyc5} (hu : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 = 0) : u ^ 5 = 1 := by
  linear_combination (u - 1) * hu

theorem pow_mod_five {u : Cyc5} (hu : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 = 0) (n : ℕ) :
    u ^ n = u ^ (n % 5) := by
  conv_lhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, pow_five_eq_one hu, one_pow, one_mul]

/-- A power `u^b`, `5 ∤ b`, of a primitive fifth root of unity is one. -/
theorem prim_pow {u : Cyc5} (hu : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 = 0) {b : ℕ} (hb : ¬ 5 ∣ b) :
    (u ^ b) ^ 4 + (u ^ b) ^ 3 + (u ^ b) ^ 2 + u ^ b + 1 = 0 := by
  rw [pow_mod_five hu b]
  have hb5 : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by omega
  rcases hb5 with h | h | h | h <;> rw [h]
  · linear_combination hu
  · linear_combination (u ^ 4 - u ^ 3 + u ^ 2 - u + 1) * hu
  · linear_combination (u ^ 8 - u ^ 7 + u ^ 5 - u ^ 4 + u ^ 3 - u + 1) * hu
  · linear_combination (u ^ 12 - u ^ 11 + u ^ 8 - u ^ 6 + u ^ 4 - u + 1) * hu

/-- `ζ^i`, `5 ∤ i`, is a primitive fifth root of unity, of norm 1. -/
theorem zS_pow_facts {i : ℕ} (hi : ¬ 5 ∣ i) :
    (zS ^ i) ^ 4 + (zS ^ i) ^ 3 + (zS ^ i) ^ 2 + zS ^ i + 1 = 0 ∧ (zS ^ i).norm = 1 :=
  ⟨prim_pow zS_rel hi, by rw [map_pow, norm_zS, one_pow]⟩

/-- The conjugate of a fifth root of unity of norm 1 is its inverse `u⁴`. -/
theorem star_eq_pow_four {u : Cyc5} (hu : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 = 0)
    (hNu : u.norm = 1) : star u = u ^ 4 := by
  have h1 : u * star u = 1 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hNu, map_one]
  have h5 := pow_five_eq_one hu
  linear_combination (u ^ 4) * h1 - (star u) * h5

/-- For a primitive fifth root of unity `u` of norm 1 and `5 ∤ b`:
`N(x^(5b) - 1) = ∏_{j < 5} N((u^j x)^b - 1)`. -/
theorem norm_twist5 {u : Cyc5} (hu : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 = 0) (hNu : u.norm = 1)
    (x : Cyc5) {b : ℕ} (hb : ¬ 5 ∣ b) :
    N5 (x ^ (5 * b) - 1) =
      N5 (x ^ b - 1) * (N5 ((u * x) ^ b - 1) * N5 ((u ^ 2 * x) ^ b - 1) *
        N5 ((u ^ 3 * x) ^ b - 1) * N5 ((u ^ 4 * x) ^ b - 1)) := by
  have hv := prim_pow hu hb
  have hv5 := pow_five_eq_one hv
  have hNv : N5 (u ^ b) = 1 := by rw [N5_apply, map_pow, hNu, one_pow, map_one]
  have e1 : (u * x) ^ b = u ^ b * x ^ b := mul_pow _ _ _
  have e2 : (u ^ 2 * x) ^ b = (u ^ b) ^ 2 * x ^ b := by
    rw [mul_pow, ← pow_mul, mul_comm 2 b, pow_mul]
  have e3 : (u ^ 3 * x) ^ b = (u ^ b) ^ 3 * x ^ b := by
    rw [mul_pow, ← pow_mul, mul_comm 3 b, pow_mul]
  have e4 : (u ^ 4 * x) ^ b = (u ^ b) ^ 4 * x ^ b := by
    rw [mul_pow, ← pow_mul, mul_comm 4 b, pow_mul]
  rw [e1, e2, e3, e4, mul_comm 5 b, pow_mul]
  generalize u ^ b = v at hv hv5 hNv
  generalize x ^ b = y
  have hfac : y ^ 5 - 1 = (y - 1) * ((y - v ^ 4) * (y - v ^ 3) * (y - v ^ 2) * (y - v)) := by
    linear_combination (y ^ 4 + v ^ 6 * (1 - y) + v ^ 5 * (y ^ 2 - 1) + v ^ 3 * (y ^ 2 - y ^ 3) +
      v * (1 - y ^ 3) - 1) * hv
  have f1 : v * y - 1 = v * (y - v ^ 4) := by linear_combination hv5
  have f2 : v ^ 2 * y - 1 = v ^ 2 * (y - v ^ 3) := by linear_combination hv5
  have f3 : v ^ 3 * y - 1 = v ^ 3 * (y - v ^ 2) := by linear_combination hv5
  have f4 : v ^ 4 * y - 1 = v ^ 4 * (y - v) := by linear_combination hv5
  rw [hfac, f1, f2, f3, f4]
  simp only [map_mul, map_pow, hNv, one_pow, one_mul]

/-! ## 3. The two norms `L5 h` and `M5 h` -/

theorem zS_mul_sub_one (d : Gold) : zS * algebraMap Gold Cyc5 d - 1 = ⟨-1, d⟩ := by
  ext1 <;> simp [zS, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem zS_sq_mul_sub_one (d : Gold) :
    zS ^ 2 * algebraMap Gold Cyc5 d - 1 = ⟨-d - 1, cR * d⟩ := by
  rw [zS_sq]
  ext1 <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- `N(ζ t^h - 1) = L5 h` and `N(ζ² t^h - 1) = M5 h` for `h = 2k + 1`. -/
theorem norm_z_th (k : ℕ) :
    N5 (zS * tS ^ (2 * k + 1) - 1) = L5 (2 * k + 1) ∧
      N5 (zS ^ 2 * tS ^ (2 * k + 1) - 1) = M5 (2 * k + 1) := by
  have hpow : tS ^ (2 * k + 1) = algebraMap Gold Cyc5 ((((5 : ℤ) ^ k : ℤ) : Gold) * tR) := by
    rw [pow_succ, pow_mul, tS_sq, map_mul, ← tS]
    rw [Int.cast_pow, map_pow, Int.cast_ofNat, map_ofNat]
  have hL : L5 (2 * k + 1) =
      25 * (5 ^ k) ^ 4 - 25 * (5 ^ k) ^ 3 + 15 * (5 ^ k) ^ 2 - 5 * 5 ^ k + 1 := by
    unfold L5
    rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega]
    ring
  have hM : M5 (2 * k + 1) =
      25 * (5 ^ k) ^ 4 + 25 * (5 ^ k) ^ 3 + 15 * (5 ^ k) ^ 2 + 5 * 5 ^ k + 1 := by
    unfold M5
    rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega]
    ring
  rw [hpow, hL, hM, zS_mul_sub_one, zS_sq_mul_sub_one]
  generalize (5 : ℤ) ^ k = c
  have n1 : (⟨-1, (c : Gold) * tR⟩ : Cyc5).norm = ⟨5 * c ^ 2 - 3 * c + 1, c⟩ := by
    rw [QuadraticAlgebra.norm_def]
    ext <;> simp [tR, cR, sq, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> ring
  have n2 : (⟨-((c : Gold) * tR) - 1, cR * ((c : Gold) * tR)⟩ : Cyc5).norm =
      ⟨5 * c ^ 2 + 2 * c + 1, c⟩ := by
    rw [QuadraticAlgebra.norm_def]
    ext <;> simp [tR, cR, sq, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> ring
  rw [N5_apply, N5_apply, n1, n2, gold_norm_eq, gold_norm_eq]
  constructor <;> ring

/-! ## 4. The two real embeddings of `ℤ[φ]`, and the size of `N(y - 1)` -/

/-- The real embedding of `ℤ[φ]` that sends `φ` to a root `g` of `g² = g + 1`. -/
noncomputable def rho (g : ℝ) (hg : g ^ 2 = g + 1) : Gold →+* ℝ where
  toFun r := r.re + r.im * g
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    push_cast
    linear_combination (-(x.im * y.im : ℝ)) * hg
  map_zero' := by simp
  map_add' x y := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    push_cast
    ring

theorem rho_apply (g : ℝ) (hg : g ^ 2 = g + 1) (r : Gold) : rho g hg r = r.re + r.im * g := rfl

/-- The norm of `ℤ[φ]` is the product of the two real embeddings. -/
theorem gold_norm_eq_rho (r : Gold) :
    (r.norm : ℝ) = rho _ Real.goldenRatio_sq r * rho _ Real.goldenConj_sq r := by
  rw [gold_norm_eq, rho_apply, rho_apply]
  push_cast
  linear_combination (-(r.re * r.im : ℝ)) * Real.goldenRatio_add_goldenConj -
    (r.im : ℝ) ^ 2 * Real.goldenRatio_mul_goldenConj

/-- If the norm of `y` to `ℤ[φ]` is the integer `n = s²`, then `N(y - 1)` lies between
`(s - 1)⁴` and `(s + 1)⁴`. Under each real embedding of `ℤ[φ]` the norm form of `ℤ[ζ]` is
positive definite, so the trace of `y` has absolute value at most `2s`. -/
theorem norm_sub_one_bounds5 (y : Cyc5) {n : ℤ} (hy : y.norm = (n : Gold)) {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ^ 2 = (n : ℝ)) :
    (s - 1) ^ 4 ≤ (N5 (y - 1) : ℝ) ∧ (N5 (y - 1) : ℝ) ≤ (s + 1) ^ 4 := by
  have h1 : (y - 1).norm = (n : Gold) + 1 - (2 * y.re + cR * y.im) := by
    rw [← hy, QuadraticAlgebra.norm_def, QuadraticAlgebra.norm_def]
    simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one]
    ring
  have h2 : (2 * y.re + cR * y.im) ^ 2 + (4 - cR ^ 2) * y.im ^ 2 = 4 * (n : Gold) := by
    rw [← hy, QuadraticAlgebra.norm_def]
    ring
  have key : ∀ (g : ℝ) (hg : g ^ 2 = g + 1), -2 ≤ g →
      (s - 1) ^ 2 ≤ rho g hg (y - 1).norm ∧ rho g hg (y - 1).norm ≤ (s + 1) ^ 2 := by
    intro g hg hg2
    have hc : rho g hg cR = g - 1 := by
      change ((-1 : ℤ) : ℝ) + ((1 : ℤ) : ℝ) * g = g - 1
      push_cast
      ring
    have h3 := congrArg (rho g hg) h2
    simp only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_intCast, hc] at h3
    have e : 4 - (g - 1) ^ 2 = 2 + g := by linear_combination (-1 : ℝ) * hg
    rw [e] at h3
    have hB : 0 ≤ (2 + g) * rho g hg y.im ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have h4 : (2 * rho g hg y.re + (g - 1) * rho g hg y.im) ^ 2 ≤ (2 * s) ^ 2 := by
      have : (2 * s) ^ 2 = 4 * (n : ℝ) := by rw [mul_pow, hs]; norm_num
      linarith
    obtain ⟨h5, h6⟩ := abs_le_of_sq_le_sq' h4 (by positivity)
    rw [h1]
    simp only [map_sub, map_add, map_mul, map_one, map_ofNat, map_intCast, hc]
    constructor <;> nlinarith
  obtain ⟨a1, a2⟩ := key _ Real.goldenRatio_sq (by linarith [Real.goldenRatio_pos])
  obtain ⟨b1, b2⟩ := key _ Real.goldenConj_sq (by linarith [Real.neg_one_lt_goldenConj])
  rw [N5_apply, gold_norm_eq_rho]
  constructor
  · calc (s - 1) ^ 4 = (s - 1) ^ 2 * (s - 1) ^ 2 := by ring
      _ ≤ _ := mul_le_mul a1 b1 (sq_nonneg _) (le_trans (sq_nonneg _) a1)
  · calc _ ≤ (s + 1) ^ 2 * (s + 1) ^ 2 :=
          mul_le_mul a2 b2 (le_trans (sq_nonneg _) b1) (sq_nonneg _)
      _ = (s + 1) ^ 4 := by ring

/-- `N(z^b - 1) > 0` when the norm of `z` to `ℤ[φ]` is an integer `n > 1` and `b > 0`. -/
theorem N5_pow_sub_one_pos {z : Cyc5} {n : ℤ} (hn : 1 < n) (hz : z.norm = (n : Gold)) {b : ℕ}
    (hb : 0 < b) : 0 < N5 (z ^ b - 1) := by
  have hnb : (1 : ℝ) < ((n ^ b : ℤ) : ℝ) := by
    exact_mod_cast one_lt_pow₀ hn hb.ne'
  have hzb : (z ^ b).norm = ((n ^ b : ℤ) : Gold) := by rw [map_pow, hz, Int.cast_pow]
  have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ ((n ^ b : ℤ) : ℝ))
  have hs1 : 1 < Real.sqrt ((n ^ b : ℤ) : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using hnb
  obtain ⟨hlo, -⟩ := norm_sub_one_bounds5 (z ^ b) hzb (Real.sqrt_nonneg _) hs
  have : (0 : ℝ) < (N5 (z ^ b - 1) : ℝ) := lt_of_lt_of_le (pow_pos (sub_pos.2 hs1) 4) hlo
  exact_mod_cast this

/-! ## 5. Norms of cyclotomic values -/

/-- `∏_{d ∣ n} N(Φ_d(z)) = N(z^n - 1)`. -/
theorem prod_norm_eval_cyclotomic5 (z : Cyc5) {n : ℕ} (hn : 0 < n) :
    ∏ i ∈ n.divisors, N5 ((cyclotomic i Cyc5).eval z) = N5 (z ^ n - 1) := by
  have h := congrArg (Polynomial.eval z) (prod_cyclotomic_eq_X_pow_sub_one hn Cyc5)
  rw [Polynomial.eval_prod] at h
  simp only [eval_sub, eval_pow, eval_X, eval_one] at h
  rw [← h]
  exact (map_prod N5 _ _).symm

theorem norm_eval_cyclotomic_dvd5 (z : Cyc5) {n : ℕ} (hn : 0 < n) :
    N5 ((cyclotomic n Cyc5).eval z) ∣ N5 (z ^ n - 1) := by
  rw [← prod_norm_eval_cyclotomic5 z hn]
  exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self n hn.ne')

theorem norm_eval_cyclotomic_ne_zero5 {z : Cyc5} {n : ℤ} (hn : 1 < n)
    (hz : z.norm = (n : Gold)) {m : ℕ} (hm : 0 < m) :
    N5 ((cyclotomic m Cyc5).eval z) ≠ 0 := fun h0 =>
  (N5_pow_sub_one_pos hn hz hm).ne' (zero_dvd_iff.1 (h0 ▸ norm_eval_cyclotomic_dvd5 z hm))

section Moebius

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Möbius inversion: `N(Φ_m(z)) = ∏_{ab = m} N(z^b - 1)^{μ(a)}`, in ℝ. -/
theorem moebius_formula5 {z : Cyc5} {n : ℤ} (hn : 1 < n) (hz : z.norm = (n : Gold)) {m : ℕ}
    (hm : 0 < m) :
    ∏ x ∈ m.divisorsAntidiagonal, (N5 (z ^ x.2 - 1) : ℝ) ^ (μ x.1) =
      (N5 ((cyclotomic m Cyc5).eval z) : ℝ) := by
  have hU : ∀ k : ℕ, 0 < k → (N5 (z ^ k - 1) : ℝ) ≠ 0 := fun k hk => by
    exact_mod_cast (N5_pow_sub_one_pos hn hz hk).ne'
  have hA : ∀ k : ℕ, 0 < k → (N5 ((cyclotomic k Cyc5).eval z) : ℝ) ≠ 0 := fun k hk => by
    exact_mod_cast norm_eval_cyclotomic_ne_zero5 hn hz hk
  refine (prod_eq_iff_prod_pow_moebius_eq_of_ne_zero
    (f := fun k => (N5 ((cyclotomic k Cyc5).eval z) : ℝ))
    (g := fun k => (N5 (z ^ k - 1) : ℝ)) hA hU).1 (fun k hk => ?_) m hm
  exact_mod_cast prod_norm_eval_cyclotomic5 z hk

/-! ## 6. The product formula -/

/-- `N(Φ_{5m}(x)) = ∏_{j=1}^{4} N(Φ_m(u^j x))` for `5 ∤ m` and a primitive fifth root of unity
`u` of norm 1. -/
theorem norm_cyclotomic_mul_five {u : Cyc5} (hu : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 = 0)
    (hNu : u.norm = 1) {x : Cyc5} {n : ℤ} (hn : 1 < n) (hx : x.norm = (n : Gold)) {m : ℕ}
    (hm : 0 < m) (h5 : ¬ 5 ∣ m) :
    N5 ((cyclotomic (m * 5) Cyc5).eval x) =
      N5 ((cyclotomic m Cyc5).eval (u * x)) * N5 ((cyclotomic m Cyc5).eval (u ^ 2 * x)) *
        N5 ((cyclotomic m Cyc5).eval (u ^ 3 * x)) *
        N5 ((cyclotomic m Cyc5).eval (u ^ 4 * x)) := by
  have hx5 : (x ^ 5).norm = ((n ^ 5 : ℤ) : Gold) := by rw [map_pow, hx, Int.cast_pow]
  have hn5 : 1 < n ^ 5 := one_lt_pow₀ hn (by norm_num)
  have hux : ∀ j : ℕ, (u ^ j * x).norm = (n : Gold) := fun j => by
    rw [map_mul, map_pow, hNu, one_pow, one_mul, hx]
  have hux1 : (u * x).norm = (n : Gold) := by rw [map_mul, hNu, one_mul, hx]
  -- `Φ_m(x⁵) = Φ_{5m}(x) Φ_m(x)`
  have hexp : (cyclotomic m Cyc5).eval (x ^ 5) =
      (cyclotomic (m * 5) Cyc5).eval x * (cyclotomic m Cyc5).eval x := by
    rw [← expand_eval, cyclotomic_expand_eq_cyclotomic_mul Nat.prime_five h5, eval_mul]
  have hreal : (N5 ((cyclotomic m Cyc5).eval (x ^ 5)) : ℝ) =
      (N5 ((cyclotomic m Cyc5).eval x) : ℝ) *
        ((N5 ((cyclotomic m Cyc5).eval (u * x)) : ℝ) *
          (N5 ((cyclotomic m Cyc5).eval (u ^ 2 * x)) : ℝ) *
          (N5 ((cyclotomic m Cyc5).eval (u ^ 3 * x)) : ℝ) *
          (N5 ((cyclotomic m Cyc5).eval (u ^ 4 * x)) : ℝ)) := by
    rw [← moebius_formula5 hn5 hx5 hm, ← moebius_formula5 hn hx hm,
      ← moebius_formula5 hn hux1 hm, ← moebius_formula5 hn (hux 2) hm,
      ← moebius_formula5 hn (hux 3) hm, ← moebius_formula5 hn (hux 4) hm,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hb : ¬ 5 ∣ p.2 := fun h =>
      h5 (h.trans (Dvd.intro_left _ (Nat.mem_divisorsAntidiagonal.1 hp).1))
    rw [← pow_mul, norm_twist5 hu hNu x hb]
    push_cast
    simp only [mul_zpow]
  have hint : N5 ((cyclotomic m Cyc5).eval (x ^ 5)) =
      N5 ((cyclotomic m Cyc5).eval x) *
        (N5 ((cyclotomic m Cyc5).eval (u * x)) * N5 ((cyclotomic m Cyc5).eval (u ^ 2 * x)) *
          N5 ((cyclotomic m Cyc5).eval (u ^ 3 * x)) *
          N5 ((cyclotomic m Cyc5).eval (u ^ 4 * x))) := by
    exact_mod_cast hreal
  rw [hexp, map_mul] at hint
  exact mul_left_cancel₀ (norm_eval_cyclotomic_ne_zero5 hn hx hm) (by rw [← hint]; ring)

/-! ## 7. The size bound -/

/-- One factor of the Möbius product: with `r > 1` and `(r - 1)⁴ ≤ U ≤ (r + 1)⁴`,
`U^e ≥ (r⁴)^e (1 - 1/r)⁴` for `e ∈ {0, 1, -1}`. -/
theorem factor_bound5 {U r : ℝ} {e : ℤ} (he : e = 0 ∨ e = 1 ∨ e = -1) (hr : 1 < r)
    (hlo : (r - 1) ^ 4 ≤ U) (hhi : U ≤ (r + 1) ^ 4) :
    (r ^ 4) ^ e * (1 - r⁻¹) ^ 4 ≤ U ^ e := by
  have hr0 : 0 < r := by linarith
  have hx : 1 - r⁻¹ = (r - 1) / r := by field_simp
  have hU0 : 0 < U := lt_of_lt_of_le (pow_pos (by linarith) 4) hlo
  rcases he with rfl | rfl | rfl
  · simp only [zpow_zero, one_mul]
    have h1 : 0 ≤ 1 - r⁻¹ := by rw [hx]; exact div_nonneg (by linarith) hr0.le
    have h2 : 1 - r⁻¹ ≤ 1 := by have := inv_pos.2 hr0; linarith
    exact pow_le_one₀ h1 h2
  · simp only [zpow_one]
    have : r ^ 4 * (1 - r⁻¹) ^ 4 = (r - 1) ^ 4 := by rw [hx]; field_simp
    rw [this]
    exact hlo
  · rw [zpow_neg_one, zpow_neg_one]
    have hinv : ((r + 1) ^ 4)⁻¹ ≤ U⁻¹ := inv_anti₀ hU0 hhi
    refine le_trans ?_ hinv
    have e1 : (r ^ 4)⁻¹ * (1 - r⁻¹) ^ 4 = (r - 1) ^ 4 / (r ^ 4 * r ^ 4) := by
      rw [hx]; field_simp
    rw [e1, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have e2 : (r - 1) ^ 4 * (r + 1) ^ 4 = (r ^ 2 - 1) ^ 4 := by ring
    have e3 : r ^ 4 * r ^ 4 = (r ^ 2) ^ 4 := by ring
    rw [e2, one_mul, e3]
    exact pow_le_pow_left₀ (by nlinarith) (by linarith) 4

/-- **Lower bound.** If the norm of `z` to `ℤ[φ]` is the integer `s²`, `s > 1`:
`N(Φ_m(z)) ≥ s^(4φ(m)) (∏_{d ∣ m} (1 - s^(-d)))⁴`. -/
theorem lower_bound5 {z : Cyc5} {n : ℤ} (hz : z.norm = (n : Gold)) {s : ℝ} (hs1 : 1 < s)
    (hs : s ^ 2 = (n : ℝ)) {m : ℕ} (hm : 0 < m) :
    (s ^ 4) ^ m.totient * (∏ d ∈ m.divisors, (1 - (s ^ d)⁻¹)) ^ 4 ≤
      (N5 ((cyclotomic m Cyc5).eval z) : ℝ) := by
  have hs0 : 0 < s := by linarith
  have hn : 1 < n := by
    have : (1 : ℝ) < (n : ℝ) := by rw [← hs]; nlinarith
    exact_mod_cast this
  rw [← moebius_formula5 hn hz hm]
  have hφ : (s ^ 4) ^ m.totient =
      ∏ x ∈ m.divisorsAntidiagonal, (s ^ 4) ^ (μ x.1 * (x.2 : ℤ)) := by
    rw [← Base3.real_zpow_sum (by positivity) _ (fun x => μ x.1 * (x.2 : ℤ)),
      sum_moebius_mul_eq_totient hm, zpow_natCast]
  have hd : (∏ d ∈ m.divisors, (1 - (s ^ d)⁻¹)) ^ 4 =
      ∏ x ∈ m.divisorsAntidiagonal, (1 - (s ^ x.2)⁻¹) ^ 4 := by
    rw [← Finset.prod_pow]
    exact (Nat.prod_divisorsAntidiagonal' (f := fun _ b => (1 - (s ^ b)⁻¹) ^ 4)).symm
  rw [hφ, hd, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro x _; positivity
  · intro x hx
    have hb : x.2 ≠ 0 := by
      rintro h0
      have := Nat.mem_divisorsAntidiagonal.1 hx
      rw [h0, mul_zero] at this
      exact this.2 this.1.symm
    have hr : 1 < s ^ x.2 := one_lt_pow₀ hs1 hb
    obtain ⟨hlo, hhi⟩ := norm_sub_one_bounds5 (z ^ x.2) (n := n ^ x.2) (s := s ^ x.2)
      (by rw [map_pow, hz, Int.cast_pow]) (by positivity)
      (by rw [Int.cast_pow, ← hs]; exact pow_right_comm s x.2 2)
    have key := factor_bound5 (moebius_eq_or x.1) hr hlo hhi
    have e : (s ^ 4) ^ (μ x.1 * (x.2 : ℤ)) = ((s ^ x.2) ^ 4) ^ μ x.1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, pow_right_comm]
    rw [e]
    exact key

end Moebius

/-- For odd `m` and `0 ≤ x ≤ 5/11`: `∏_{d ∣ m} (1 - x^d) ≥ 9/20`. The divisors other than
1 are at least 3, so the product is at least `(1 - x)(1 - x³/(1 - x)) = 1 - x - x³`. -/
theorem prod_divisors_ge5 {m : ℕ} (hm : Odd m) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 5 / 11) :
    9 / 20 ≤ ∏ d ∈ m.divisors, (1 - x ^ d) := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have h1mem : 1 ∈ m.divisors := Nat.one_mem_divisors.2 hm0
  rw [← Finset.mul_prod_erase _ _ h1mem, pow_one]
  have hx1 : x < 1 := by linarith
  have hsum : ∑ d ∈ m.divisors.erase 1, x ^ d ≤ x ^ 3 / (1 - x) := by
    have hsub : m.divisors.erase 1 ⊆ Finset.Ico 3 (m + 1) := by
      intro d hd
      obtain ⟨hd1, hdm⟩ := Finset.mem_erase.1 hd
      have hdvd := Nat.dvd_of_mem_divisors hdm
      have hle := Nat.le_of_dvd hm.pos hdvd
      have hodd : ¬ 2 ∣ d := fun h =>
        (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 (h.trans hdvd))
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hdm
      rw [Finset.mem_Ico]
      omega
    calc ∑ d ∈ m.divisors.erase 1, x ^ d ≤ ∑ d ∈ Finset.Ico 3 (m + 1), x ^ d :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg hx0 _
      _ ≤ x ^ 3 / (1 - x) := geom_sum_Ico_le_of_lt_one hx0 hx1
  have hprod := Base3.one_sub_sum_le_prod (m.divisors.erase 1) (fun d => x ^ d)
    (fun _ _ => pow_nonneg hx0 _) (fun _ _ => pow_le_one₀ hx0 hx1.le)
  have h3 : x ^ 3 ≤ (5 / 11) ^ 3 := pow_le_pow_left₀ hx0 hx 3
  have hpos : 0 < 1 - x := by linarith
  have h2 : (1 - x) * (1 - x ^ 3 / (1 - x)) ≤
      (1 - x) * ∏ d ∈ m.divisors.erase 1, (1 - x ^ d) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  have h3' : (1 - x) * (1 - x ^ 3 / (1 - x)) = 1 - x - x ^ 3 := by field_simp
  rw [h3'] at h2
  norm_num at h3
  linarith

/-- **Size of a half.** If the norm of `z` to `ℤ[φ]` is an integer `n ≥ 5` and `m` is odd,
then `25 N(Φ_m(z)) ≥ 25^φ(m)`. -/
theorem half_lower5 {z : Cyc5} {n : ℤ} (hn : 5 ≤ n) (hz : z.norm = (n : Gold)) {m : ℕ}
    (hm : Odd m) : 25 ^ m.totient ≤ 25 * N5 ((cyclotomic m Cyc5).eval z) := by
  have hN5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  set s := Real.sqrt (n : ℝ) with hsdef
  have hs : s ^ 2 = (n : ℝ) := Real.sq_sqrt hN0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs11 : 11 / 5 ≤ s := by
    by_contra h
    push Not at h
    nlinarith
  have hs1 : 1 < s := by linarith
  have hlow := lower_bound5 hz hs1 hs hm.pos
  have hx : s⁻¹ ≤ 5 / 11 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    norm_num
    linarith
  have hprod := prod_divisors_ge5 hm (inv_nonneg.2 hs0) hx
  have hrew : ∏ d ∈ m.divisors, (1 - (s ^ d)⁻¹) = ∏ d ∈ m.divisors, (1 - s⁻¹ ^ d) :=
    Finset.prod_congr rfl fun d _ => by rw [inv_pow]
  rw [hrew] at hlow
  have hP4 : (1 : ℝ) / 25 ≤ (∏ d ∈ m.divisors, (1 - s⁻¹ ^ d)) ^ 4 := by
    have h1 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 20) hprod 4
    have h2 : (1 : ℝ) / 25 ≤ (9 / 20) ^ 4 := by norm_num
    linarith
  have hs4 : s ^ 4 = (n : ℝ) ^ 2 := by rw [← hs]; ring
  have hpow : (25 : ℝ) ^ m.totient ≤ (s ^ 4) ^ m.totient :=
    pow_le_pow_left₀ (by norm_num) (by rw [hs4]; nlinarith) _
  have hfin : (25 : ℝ) ^ m.totient ≤ 25 * (N5 ((cyclotomic m Cyc5).eval z) : ℝ) := by
    have h1 : (s ^ 4) ^ m.totient * (1 / 25) ≤
        (s ^ 4) ^ m.totient * (∏ d ∈ m.divisors, (1 - s⁻¹ ^ d)) ^ 4 :=
      mul_le_mul_of_nonneg_left hP4 (by positivity)
    linarith
  exact_mod_cast hfin

/-! ## 8. The two halves of `Φ_{5h}(5)` -/

/-- `Φ_{5h}(5)`. -/
noncomputable def Phi5 (h : ℕ) : ℤ := (cyclotomic (5 * h) ℤ).eval 5

theorem Phi5_pos {h : ℕ} (hh : 0 < h) : 0 < Phi5 h :=
  cyclotomic_pos (by omega) 5

/-- `Φ_n(X^(5^a)) = Φ_{n 5^a}(X)` when `5 ∣ n`. -/
theorem cyclotomic_expand_five_pow {n : ℕ} (h5 : 5 ∣ n) (a : ℕ) (R : Type*) [CommRing R] :
    expand R (5 ^ a) (cyclotomic n R) = cyclotomic (n * 5 ^ a) R := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h : 5 ^ (a + 1) = 5 * 5 ^ a := by ring
    rw [h, expand_mul, ih, cyclotomic_expand_eq_cyclotomic Nat.prime_five
      (h5.trans (dvd_mul_right _ _))]
    congr 1
    ring

theorem tR_pow_sq (a : ℕ) : (tR ^ 5 ^ a) ^ 2 = (5 : Gold) ^ 5 ^ a := by
  rw [← pow_mul, mul_comm, pow_mul, tR_sq]

/-- In `ℤ[φ]`: the norm of `Φ_{5m}(t^(5^a))` is `Φ_{5h}(5)`, where `h = 5^a m` and `m` is odd.
Indeed `Φ_{5m}(T) Φ_{5m}(-T) = Φ_{5m}(T²)` and `T² = 5^(5^a)`. -/
theorem gold_norm_cyclotomic (a : ℕ) {m : ℕ} (hm : Odd m) :
    ((cyclotomic (m * 5) Gold).eval (tR ^ 5 ^ a)).norm = Phi5 (5 ^ a * m) := by
  have hnodd : Odd (m * 5) := hm.mul (by decide)
  have hn1 : 1 < m * 5 := by have := hm.pos; omega
  have hdiv : ¬ 2 ∣ m * 5 := Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hnodd)
  have E1 : ∀ z : Gold, (cyclotomic (m * 5 * 2) Gold).eval z =
      (cyclotomic (m * 5) Gold).eval (-z) := by
    intro z
    rw [mul_comm (m * 5) 2, cyclotomic_two_mul_of_odd hnodd hn1, eval_comp, eval_neg, eval_X]
  have prodE : ∀ z : Gold,
      (cyclotomic (m * 5) Gold).eval z * (cyclotomic (m * 5) Gold).eval (-z) =
        (cyclotomic (m * 5) Gold).eval (z ^ 2) := by
    intro z
    rw [← expand_eval, cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two hdiv, eval_mul, E1]
    ring
  have hstar : ∀ w : Gold, star ((cyclotomic (m * 5) Gold).eval w) =
      (cyclotomic (m * 5) Gold).eval (star w) := by
    intro w
    have := Polynomial.eval₂_at_apply (p := cyclotomic (m * 5) Gold) (starRingEnd Gold) w
    rw [← Polynomial.eval_map, map_cyclotomic, starRingEnd_apply, starRingEnd_apply] at this
    exact this.symm
  have hstarT : star (tR ^ 5 ^ a) = -tR ^ 5 ^ a := by
    rw [star_pow, star_tR, Odd.neg_pow (Odd.pow (by decide))]
  have hnorm : (algebraMap ℤ Gold) ((cyclotomic (m * 5) Gold).eval (tR ^ 5 ^ a)).norm =
      (cyclotomic (m * 5) Gold).eval ((5 : Gold) ^ 5 ^ a) := by
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star, hstar, hstarT, prodE, tR_pow_sq]
  have h6 : (cyclotomic (m * 5) Gold).eval ((5 : Gold) ^ 5 ^ a) =
      (cyclotomic (5 * (5 ^ a * m)) Gold).eval 5 := by
    rw [show 5 * (5 ^ a * m) = m * 5 * 5 ^ a by ring,
      ← cyclotomic_expand_five_pow (n := m * 5) ⟨m, by ring⟩ a Gold, expand_eval]
  have hPhi : (algebraMap ℤ Gold) (Phi5 (5 ^ a * m)) =
      (cyclotomic (5 * (5 ^ a * m)) Gold).eval 5 := by
    have := Polynomial.eval₂_at_apply (p := cyclotomic (5 * (5 ^ a * m)) ℤ)
      (algebraMap ℤ Gold) 5
    rw [← Polynomial.eval_map, map_cyclotomic] at this
    simpa [Phi5] using this.symm
  exact QuadraticAlgebra.algebraMap_injective (hnorm.trans (h6.trans hPhi.symm))

theorem norm_u_T {u : Cyc5} (hNu : u.norm = 1) (a : ℕ) :
    (u * tS ^ 5 ^ a).norm = (((5 : ℤ) ^ 5 ^ a : ℤ) : Gold) := by
  rw [map_mul, map_pow, hNu, norm_tS, one_mul, Int.cast_pow, Int.cast_ofNat]

theorem five_le_pow (a : ℕ) : (5 : ℤ) ≤ 5 ^ 5 ^ a := by
  calc (5 : ℤ) = 5 ^ 1 := by norm_num
    _ ≤ 5 ^ 5 ^ a := pow_le_pow_right₀ (by norm_num) (Nat.one_le_pow _ _ (by norm_num))

/-- **The two halves multiply to `Φ_{5h}(5)`**, `h = 5^a m`, `m` odd, `5 ∤ m`. The norm of
`Φ_{5m}(T)` is `Φ_{5h}(5)²`; it is also the product of the four numbers `N(Φ_m(u^j T))`,
`j = 1, 2, 3, 4`, and conjugation pairs `j` with `5 - j`. -/
theorem half_mul_half5 {u : Cyc5} (hu : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 = 0) (hNu : u.norm = 1)
    (a : ℕ) {m : ℕ} (hm : Odd m) (h5 : ¬ 5 ∣ m) :
    N5 ((cyclotomic m Cyc5).eval (u * tS ^ 5 ^ a)) *
      N5 ((cyclotomic m Cyc5).eval (u ^ 2 * tS ^ 5 ^ a)) = Phi5 (5 ^ a * m) := by
  have hm0 : 0 < m := hm.pos
  have hNT : (tS ^ 5 ^ a).norm = (((5 : ℤ) ^ 5 ^ a : ℤ) : Gold) := by
    rw [map_pow, norm_tS, Int.cast_pow, Int.cast_ofNat]
  have h5a := five_le_pow a
  have hprod := norm_cyclotomic_mul_five hu hNu (by omega : (1 : ℤ) < 5 ^ 5 ^ a) hNT hm0 h5
  -- conjugation
  have hstar : ∀ w : Cyc5, star ((cyclotomic m Cyc5).eval w) =
      (cyclotomic m Cyc5).eval (star w) := by
    intro w
    have := Polynomial.eval₂_at_apply (p := cyclotomic m Cyc5) (starRingEnd Cyc5) w
    rw [← Polynomial.eval_map, map_cyclotomic, starRingEnd_apply, starRingEnd_apply] at this
    exact this.symm
  have hsu : star u = u ^ 4 := star_eq_pow_four hu hNu
  have hsT : star (tS ^ 5 ^ a) = tS ^ 5 ^ a := by rw [star_pow, star_tS]
  have hu5 := pow_five_eq_one hu
  have h4 : N5 ((cyclotomic m Cyc5).eval (u ^ 4 * tS ^ 5 ^ a)) =
      N5 ((cyclotomic m Cyc5).eval (u * tS ^ 5 ^ a)) := by
    rw [← N5_star ((cyclotomic m Cyc5).eval (u * tS ^ 5 ^ a)), hstar, star_mul', hsu, hsT]
  have h3 : N5 ((cyclotomic m Cyc5).eval (u ^ 3 * tS ^ 5 ^ a)) =
      N5 ((cyclotomic m Cyc5).eval (u ^ 2 * tS ^ 5 ^ a)) := by
    rw [← N5_star ((cyclotomic m Cyc5).eval (u ^ 2 * tS ^ 5 ^ a)), hstar, star_mul', star_pow,
      hsu, hsT]
    have : (u ^ 4) ^ 2 = u ^ 3 := by linear_combination (u ^ 3) * hu5
    rw [this]
  -- the norm of `Φ_{5m}(T)`
  have hT : N5 ((cyclotomic (m * 5) Cyc5).eval (tS ^ 5 ^ a)) = Phi5 (5 ^ a * m) ^ 2 := by
    have := Polynomial.eval₂_at_apply (p := cyclotomic (m * 5) Gold) (algebraMap Gold Cyc5)
      (tR ^ 5 ^ a)
    rw [← Polynomial.eval_map, map_cyclotomic, map_pow, ← tS] at this
    rw [this, N5_apply, QuadraticAlgebra.norm_algebraMap, map_pow, gold_norm_cyclotomic a hm]
  rw [h3, h4, hT] at hprod
  -- both sides are positive
  have hpos1 : 0 < N5 ((cyclotomic m Cyc5).eval (u * tS ^ 5 ^ a)) := by
    have h := half_lower5 h5a (norm_u_T hNu a) hm
    have : (0 : ℤ) < 25 ^ m.totient := by positivity
    linarith
  have hpos2 : 0 < N5 ((cyclotomic m Cyc5).eval (u ^ 2 * tS ^ 5 ^ a)) := by
    have h := half_lower5 h5a (norm_u_T (u := u ^ 2) (by rw [map_pow, hNu, one_pow]) a) hm
    have : (0 : ℤ) < 25 ^ m.totient := by positivity
    linarith
  have hP := Phi5_pos (h := 5 ^ a * m) (by positivity)
  refine (sq_eq_sq₀ (mul_pos hpos1 hpos2).le hP.le).1 ?_
  rw [hprod]
  ring

theorem twentyfive_mul_lt_pow {s : ℕ} (hs : 2 ≤ s) : 25 * (s + 1) < 25 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih => rw [pow_succ]; omega

/-- **A half is not small**: it exceeds 5 and every prime factor of `m`. -/
theorem half_not_small5 {u : Cyc5} (hNu : u.norm = 1) (a : ℕ) {m : ℕ} (hm : Odd m)
    (hh : 3 ≤ 5 ^ a * m) :
    5 < N5 ((cyclotomic m Cyc5).eval (u * tS ^ 5 ^ a)) ∧
      ∀ p : ℕ, p.Prime → p ∣ m →
        (p : ℤ) < N5 ((cyclotomic m Cyc5).eval (u * tS ^ 5 ^ a)) := by
  have hNz := norm_u_T hNu a
  by_cases hm1 : m = 1
  · subst hm1
    have ha : 1 ≤ a := by
      by_contra h
      have : a = 0 := by omega
      subst this
      norm_num at hh
    have h9 : (9 : ℤ) ≤ 5 ^ 5 ^ a := by
      calc (9 : ℤ) ≤ 5 ^ 5 ^ 1 := by norm_num
        _ ≤ 5 ^ 5 ^ a := pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_right (by norm_num) ha)
    rw [cyclotomic_one, eval_sub, eval_X, eval_one]
    refine ⟨?_, fun p hp hp1 => absurd (Nat.dvd_one.1 hp1) hp.ne_one⟩
    have h9' : (9 : ℝ) ≤ (((5 : ℤ) ^ 5 ^ a : ℤ) : ℝ) := by exact_mod_cast h9
    set s := Real.sqrt (((5 : ℤ) ^ 5 ^ a : ℤ) : ℝ) with hsdef
    have hs : s ^ 2 = (((5 : ℤ) ^ 5 ^ a : ℤ) : ℝ) := Real.sq_sqrt (by linarith)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs3 : 3 ≤ s := by
      by_contra h
      push Not at h
      nlinarith
    obtain ⟨hlo, -⟩ := norm_sub_one_bounds5 _ hNz hs0 hs
    have h16 : (16 : ℝ) ≤ (s - 1) ^ 4 := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ (s - 1) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    have : (5 : ℝ) < (N5 (u * tS ^ 5 ^ a - 1) : ℝ) := by linarith
    exact_mod_cast this
  · have hlow := half_lower5 (five_le_pow a) hNz hm
    -- a prime factor of `m` is at least 3, so `φ(m) ≥ 2`
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hqm)
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    have hφ := Base3.prime_le_totient_succ hq hqm hm.pos
    have hφ2 : 2 ≤ m.totient := by omega
    have h25 := twentyfive_mul_lt_pow hφ2
    have h25' : (25 : ℤ) * ((m.totient : ℤ) + 1) < 25 ^ m.totient := by exact_mod_cast h25
    have hbig : (m.totient : ℤ) + 1 < N5 ((cyclotomic m Cyc5).eval (u * tS ^ 5 ^ a)) := by
      linarith
    have h625 : (25 : ℤ) ^ 2 ≤ 25 ^ m.totient := pow_le_pow_right₀ (by norm_num) hφ2
    refine ⟨by linarith, fun p hp hpm => ?_⟩
    have hle := Base3.prime_le_totient_succ hp hpm hm.pos
    have hle' : (p : ℤ) ≤ (m.totient : ℤ) + 1 := by exact_mod_cast hle
    linarith

end Base5

end PiFormula
