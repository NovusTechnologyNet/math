/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Base5.Classification
public import Pilean.Base3.LogExplicit

/-!
# Base 5: the base numbers, and their logarithms as values

The base numbers of base 5 are the rational numbers

  `(5^m - 1)/5^m` (`m ≥ 1`),   `L_h/5^(2h)` and `M_h/5^(2h)` (`h` odd),

where `L_h`, `M_h` are the two Aurifeuillian factors of `5^(4h) + 5^(3h) + 5^(2h) + 5^h + 1`
(`L5`, `M5` of `Base5/Defs.lean`). This file proves, with no hypothesis:

* `isF5Value_log_pow_sub_one`, `isF5Value_log_L5`, `isF5Value_log_M5`: the logarithm of a base
  number is the value of a series of the class F5;
* `f5Values`: the values of F5 form a vector space over `ℚ`;
* `baseSpan5_le_f5Values`: every rational combination of logarithms of base numbers is a
  value;
* `isF5Value_log_of_pow`: if a power `y^k`, `k ≥ 1`, of a positive rational `y` is a product
  of integer powers of base numbers, then `log y` is a value.

Unlike bases 2 and 3, the number `5` itself is not among the base numbers: no `√5 - r` is a
unit, and `log 5` is not expected to be a value.

The proofs. `log(1 - 5^(-m)) = -∑_j 5^(-mj)/j` is a series of F5 of period `2m`. For the two
other families take a fifth root of unity `v ≠ 1` with Gauss sum `v - v² - v³ + v⁴ = √5`. The
four numbers `v, -v², -v³, v⁴` have
`(1 - vy)(1 + v²y)(1 + v³y)(1 - v⁴y) = 1 - √5 y + 3y² - √5 y³ + y⁴` (`four_factors`), which is
`L_h/5^(2h)` at `y = 5^(-h/2)` and `M_h/5^(2h)` at `y = -5^(-h/2)`; and the sum of their
`k`-th powers is `4` or `-1` for even `k` and `(k/5) √5` for odd `k` (`psum_five`). So the
logarithm is `-∑_j D(j) (√5)^(j mod 2) y^j / j` with `D` rational of period 10 (`aurD`), a
series of F5 of period `10h`.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace Base5

/-! ## 1. The values of F5 form a vector space over `ℚ` -/

theorem IsF5Value.add {x y : ℝ} (hx : IsF5Value x) (hy : IsF5Value y) : IsF5Value (x + y) := by
  obtain ⟨N, f, hN, hf, hfs⟩ := hx
  obtain ⟨M, g, hM, hg, hgs⟩ := hy
  refine ⟨N * M, f + g, Nat.mul_pos hN hM, fun k => ?_, ?_⟩
  · simp only [Pi.add_apply]
    rw [periodic_mul hf M k, Nat.mul_comm N M, periodic_mul hg N k]
  · have h := hfs.add hgs
    convert h using 1
    funext k
    exact seriesTerm5_add f g k

theorem IsF5Value.const_mul (c : ℚ) {x : ℝ} (hx : IsF5Value x) : IsF5Value (c * x) := by
  obtain ⟨N, f, hN, hf, hfs⟩ := hx
  refine ⟨N, c • f, hN, fun k => by simp only [Pi.smul_apply, hf], ?_⟩
  have h := hfs.mul_left (c : ℝ)
  convert h using 1
  funext k
  exact seriesTerm5_smul c f k

theorem IsF5Value.sub {x y : ℝ} (hx : IsF5Value x) (hy : IsF5Value y) : IsF5Value (x - y) := by
  have h := hx.add (hy.const_mul (-1))
  convert h using 1
  push_cast
  ring

/-- The values of the class F5, as a subspace of `ℝ` over `ℚ`. -/
def f5Values : Submodule ℚ ℝ where
  carrier := {x | IsF5Value x}
  add_mem' := fun hx hy => hx.add hy
  zero_mem' := isF5Value_zero
  smul_mem' := fun c x hx => by
    have h : IsF5Value ((c : ℝ) * x) := IsF5Value.const_mul c hx
    simpa [Rat.smul_def] using h

theorem mem_f5Values {x : ℝ} : x ∈ f5Values ↔ IsF5Value x := Iff.rfl

/-! ## 2. Two tools on series -/

/-- A series supported on the multiples of `d`. -/
theorem hasSum_dvd_iff {d : ℕ} (hd : 0 < d) (g : ℕ → ℝ) (a : ℝ) :
    HasSum (fun k : ℕ => if d ∣ k then g (k / d) else 0) a ↔ HasSum g a := by
  have hinj : Function.Injective (fun j : ℕ => d * j) := fun i j h =>
    Nat.eq_of_mul_eq_mul_left hd h
  have h0 : ∀ k, k ∉ Set.range (fun j : ℕ => d * j) →
      (fun k : ℕ => if d ∣ k then g (k / d) else 0) k = 0 := by
    intro k hk
    have hnd : ¬ d ∣ k := fun ⟨j, hj⟩ => hk ⟨j, hj.symm⟩
    simp only [hnd, ↓reduceIte]
  rw [← hinj.hasSum_iff h0]
  have e : (fun k : ℕ => if d ∣ k then g (k / d) else 0) ∘ (fun j : ℕ => d * j) = g := by
    funext j
    simp only [Function.comp_apply, Nat.dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left j hd]
  rw [e]

/-- `log |1 - w x| = -∑_k Re(w^k) x^k / k` for `|w| = 1` and a real `x` with `|x| < 1`. -/
theorem hasSum_log_norm_one_sub {w : ℂ} (hw : ‖w‖ = 1) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => (w ^ k).re * x ^ k / k) (-Real.log ‖1 - w * (x : ℂ)‖) := by
  have hz : ‖w * (x : ℂ)‖ < 1 := by
    rw [norm_mul, hw, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have h := Complex.hasSum_re (hasSum_taylorSeries_neg_log hz)
  rw [Complex.neg_re, Complex.log_re] at h
  convert h using 1
  funext k
  rw [mul_pow, ← Complex.ofReal_pow, Complex.div_natCast_re, Complex.re_mul_ofReal]

/-! ## 3. `log (1 - 5^(-m))` -/

/-- The pattern of `log (1 - 5^(-m))`: `-2m` at the multiples of `2m`, and `0` elsewhere. -/
def rhoPow (m : ℕ) (k : ℕ) : ℚ := if 2 * m ∣ k then -(2 * m : ℚ) else 0

theorem rhoPow_periodic (m k : ℕ) : rhoPow m (k + 2 * m) = rhoPow m k := by
  simp only [rhoPow, Nat.dvd_add_self_right]

/-- `∑ ρ(k) 5^(-⌊k/2⌋)/k = log (1 - 5^(-m))` for the pattern `rhoPow m`. -/
theorem hasSum_rhoPow {m : ℕ} (hm : 0 < m) :
    HasSum (seriesTerm5 (rhoPow m)) (Real.log (1 - 1 / 5 ^ m)) := by
  have hx0 : (0 : ℝ) < 1 / 5 ^ m := by positivity
  have hx1 : (1 : ℝ) / 5 ^ m < 1 := by
    rw [div_lt_one (by positivity)]
    exact one_lt_pow₀ (by norm_num) hm.ne'
  have habs : |(1 : ℝ) / 5 ^ m| < 1 := by
    rw [abs_of_pos hx0]
    exact hx1
  have h := (hasSum_log_norm_one_sub (w := 1) (by simp) habs).neg
  have hval : - -Real.log ‖(1 : ℂ) - 1 * ((1 / 5 ^ m : ℝ) : ℂ)‖ = Real.log (1 - 1 / 5 ^ m) := by
    have e : (1 : ℂ) - 1 * ((1 / 5 ^ m : ℝ) : ℂ) = ((1 - 1 / 5 ^ m : ℝ) : ℂ) := by
      push_cast
      ring
    rw [neg_neg, e, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
  rw [hval] at h
  have h2 := (hasSum_dvd_iff (d := 2 * m) (by omega) _ _).2 h
  convert h2 using 1
  funext k
  simp only [seriesTerm5, rhoPow]
  split_ifs with hk
  · obtain ⟨j, rfl⟩ := hk
    have e1 : 2 * m * j / 2 = m * j := by
      rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [Nat.mul_div_cancel_left j (by omega : 0 < 2 * m), e1, one_pow, Complex.one_re, one_mul]
    by_cases hj : j = 0
    · subst hj
      simp
    · have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      rw [div_pow, one_pow, pow_mul]
      field_simp
  · simp

/-- **`log ((5^m - 1)/5^m)` is a value of the class F5**, for `m ≥ 1`. -/
theorem isF5Value_log_pow_sub_one {m : ℕ} (hm : 0 < m) :
    IsF5Value (Real.log (((5 : ℝ) ^ m - 1) / 5 ^ m)) := by
  have e : ((5 : ℝ) ^ m - 1) / 5 ^ m = 1 - 1 / 5 ^ m := by
    field_simp
  rw [e]
  exact ⟨2 * m, rhoPow m, by omega, rhoPow_periodic m, hasSum_rhoPow hm⟩

/-! ## 4. Fifth roots of unity and the Gauss sum -/

/-- The Gauss sum `v - v² - v³ + v⁴` of a fifth root of unity `v`. -/
def gs5 (v : ℂ) : ℂ := v - v ^ 2 - v ^ 3 + v ^ 4

theorem sum_pow_five {v : ℂ} (h5 : v ^ 5 = 1) (h1 : v ≠ 1) :
    1 + v + v ^ 2 + v ^ 3 + v ^ 4 = 0 := by
  have h : (v - 1) * (1 + v + v ^ 2 + v ^ 3 + v ^ 4) = 0 := by linear_combination h5
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) h1
  · exact h

/-- The square of the Gauss sum is `5`. -/
theorem gs5_sq {v : ℂ} (h5 : v ^ 5 = 1) (h1 : v ≠ 1) : gs5 v ^ 2 = 5 := by
  have hs := sum_pow_five h5 h1
  rw [gs5]
  linear_combination (v ^ 3 - 2 * v ^ 2 - v + 4) * h5 - hs

/-- The Gauss sum is `√5` or `-√5`. -/
theorem gs5_eq {v : ℂ} (h5 : v ^ 5 = 1) (h1 : v ≠ 1) : gs5 v = t5 ∨ gs5 v = -t5 := by
  have h : (gs5 v - t5) * (gs5 v + t5) = 0 := by linear_combination gs5_sq h5 h1 - t5_sq
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- The Legendre symbol modulo 5. -/
def leg5 (a : ℕ) : ℤ := if a % 5 = 0 then 0 else if a % 5 = 1 ∨ a % 5 = 4 then 1 else -1

theorem leg5_mod (a : ℕ) : leg5 (a % 5) = leg5 a := by simp [leg5]

theorem leg5_mul (a b : ℕ) : leg5 (a * b) = leg5 a * leg5 b := by
  have ha : a % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hb : b % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h : (a * b) % 5 = ((a % 5) * (b % 5)) % 5 := Nat.mul_mod a b 5
  simp only [leg5, h]
  generalize a % 5 = x at ha ⊢
  generalize b % 5 = y at hb ⊢
  interval_cases x <;> interval_cases y <;> decide

theorem leg5_eq_or {a : ℕ} (ha : a % 5 ≠ 0) : leg5 a = 1 ∨ leg5 a = -1 := by
  simp only [leg5, ha, ↓reduceIte]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem leg5_of_dvd {a : ℕ} (ha : 5 ∣ a) : leg5 a = 0 := by
  simp [leg5, Nat.mod_eq_zero_of_dvd ha]

/-- The Gauss sum of `v^a` is `(a/5)` times the Gauss sum of `v`. -/
theorem gs5_pow {v : ℂ} (h5 : v ^ 5 = 1) (a : ℕ) : gs5 (v ^ a) = (leg5 a : ℂ) * gs5 v := by
  have hmod : v ^ a = v ^ (a % 5) := by
    conv_lhs => rw [← Nat.mod_add_div a 5]
    rw [pow_add, pow_mul, h5, one_pow, mul_one]
  have hlt : a % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have e2 : gs5 (v ^ 2) = -gs5 v := by
    simp only [gs5]
    linear_combination (v ^ 3 - v) * h5
  have e3 : gs5 (v ^ 3) = -gs5 v := by
    simp only [gs5]
    linear_combination (-v - v ^ 4 + v ^ 2 * (v ^ 5 + 1)) * h5
  have e4 : gs5 (v ^ 4) = gs5 v := by
    simp only [gs5]
    linear_combination (-v ^ 3 - v ^ 2 * (v ^ 5 + 1) + v * (v ^ 10 + v ^ 5 + 1)) * h5
  have key : ∀ x < 5, gs5 (v ^ x) = (leg5 x : ℂ) * gs5 v := by
    intro x hx
    interval_cases x
    · simp [gs5, leg5]
    · simp [leg5]
    · rw [e2]
      simp [leg5]
    · rw [e3]
      simp [leg5]
    · rw [e4]
      simp [leg5]
  rw [hmod, ← leg5_mod a]
  exact key _ hlt

theorem orderOf_eq_five {v : ℂ} (h5 : v ^ 5 = 1) (h1 : v ≠ 1) : orderOf v = 5 := by
  rcases (Nat.dvd_prime Nat.prime_five).1 (orderOf_dvd_of_pow_eq_one h5) with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) h1
  · exact h

theorem pow_eq_one_iff_five {v : ℂ} (h5 : v ^ 5 = 1) (h1 : v ≠ 1) (k : ℕ) :
    v ^ k = 1 ↔ 5 ∣ k := by
  rw [← orderOf_eq_five h5 h1]
  exact orderOf_dvd_iff_pow_eq_one.symm

/-- There is a fifth root of unity whose Gauss sum is `√5`. -/
theorem exists_gs5_eq_t5 : ∃ v : ℂ, v ^ 5 = 1 ∧ v ≠ 1 ∧ gs5 v = t5 := by
  have hζ := zetaN_prim (N := 5) (by norm_num)
  have h5 : zetaN 5 ^ 5 = 1 := hζ.pow_eq_one
  have h1 : zetaN 5 ≠ 1 := hζ.ne_one (by norm_num)
  rcases gs5_eq h5 h1 with h | h
  · exact ⟨_, h5, h1, h⟩
  · refine ⟨zetaN 5 ^ 2, by rw [← pow_mul, mul_comm, pow_mul, h5, one_pow], fun h2 => h1 ?_, ?_⟩
    · linear_combination h5 - (zetaN 5 ^ 3 + zetaN 5) * h2
    · rw [gs5_pow h5, h]
      simp [leg5]

/-- `(1 - vy)(1 + v²y)(1 + v³y)(1 - v⁴y) = 1 - g y + 3y² - g y³ + y⁴`, `g` the Gauss sum. -/
theorem four_factors {v : ℂ} (h5 : v ^ 5 = 1) (h1 : v ≠ 1) (y : ℂ) :
    (1 - v * y) * (1 + v ^ 2 * y) * (1 + v ^ 3 * y) * (1 - v ^ 4 * y) =
      1 - gs5 v * y + 3 * y ^ 2 - gs5 v * y ^ 3 + y ^ 4 := by
  have hs := sum_pow_five h5 h1
  rw [gs5]
  linear_combination ((2 - v - v ^ 2) * y ^ 2 + (v ^ 2 + v ^ 3 - v - v ^ 4) * y ^ 3 +
    (v ^ 5 + 1) * y ^ 4) * h5 - y ^ 2 * hs

/-- `(1 - vy)(1 - v²y)(1 - v³y)(1 - v⁴y) = 1 + y + y² + y³ + y⁴`. -/
theorem four_factors_plain {v : ℂ} (h5 : v ^ 5 = 1) (h1 : v ≠ 1) (y : ℂ) :
    (1 - v * y) * (1 - v ^ 2 * y) * (1 - v ^ 3 * y) * (1 - v ^ 4 * y) =
      1 + y + y ^ 2 + y ^ 3 + y ^ 4 := by
  have hs := sum_pow_five h5 h1
  linear_combination ((2 + v + v ^ 2) * y ^ 2 - (v + v ^ 2 + v ^ 3 + v ^ 4) * y ^ 3 +
    (v ^ 5 + 1) * y ^ 4) * h5 + (-y + y ^ 2 - y ^ 3) * hs

/-- The numbers `4, 1, -1, -1, -1, 0, -1, -1, -1, 1`, of period 10: `4` or `-1` at an even
`k` (according as 5 divides `k` or not), and the Legendre symbol `(k/5)` at an odd `k`. -/
def aurD (k : ℕ) : ℚ := if k % 2 = 0 then (if k % 5 = 0 then 4 else -1) else (leg5 k : ℚ)

theorem aurD_periodic (k : ℕ) : aurD (k + 10) = aurD k := by
  have h2 : (k + 10) % 2 = k % 2 := by omega
  have h5 : (k + 10) % 5 = k % 5 := by omega
  simp only [aurD, leg5, h2, h5]

/-- The sums of the `k`-th powers of `v, -v², -v³, v⁴`. -/
theorem psum_five {v : ℂ} (h5 : v ^ 5 = 1) (h1 : v ≠ 1) (k : ℕ) :
    v ^ k + (-v ^ 2) ^ k + (-v ^ 3) ^ k + (v ^ 4) ^ k = (aurD k : ℂ) * gs5 v ^ (k % 2) := by
  rcases Nat.even_or_odd k with he | ho
  · have hk2 : k % 2 = 0 := Nat.even_iff.1 he
    have hu5 : (v ^ k) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h5, one_pow]
    have e : v ^ k + (-v ^ 2) ^ k + (-v ^ 3) ^ k + (v ^ 4) ^ k =
        v ^ k + (v ^ k) ^ 2 + (v ^ k) ^ 3 + (v ^ k) ^ 4 := by
      rw [he.neg_pow, he.neg_pow]
      ring
    rw [e, hk2, pow_zero, mul_one]
    by_cases hk5 : k % 5 = 0
    · have h1' : v ^ k = 1 := (pow_eq_one_iff_five h5 h1 k).2 (Nat.dvd_of_mod_eq_zero hk5)
      rw [h1']
      simp only [aurD, hk2, hk5, ↓reduceIte]
      norm_num
    · have hne : v ^ k ≠ 1 := fun h =>
        hk5 (Nat.mod_eq_zero_of_dvd ((pow_eq_one_iff_five h5 h1 k).1 h))
      have hs := sum_pow_five hu5 hne
      simp only [aurD, hk2, hk5, ↓reduceIte]
      push_cast
      linear_combination hs
  · have hk2 : k % 2 = 1 := Nat.odd_iff.1 ho
    have e : v ^ k + (-v ^ 2) ^ k + (-v ^ 3) ^ k + (v ^ 4) ^ k = gs5 (v ^ k) := by
      rw [ho.neg_pow, ho.neg_pow, gs5]
      ring
    rw [e, gs5_pow h5, hk2, pow_one]
    simp only [aurD, hk2, one_ne_zero, ↓reduceIte]
    push_cast
    rfl

/-! ## 5. The series of `log (1 - √5 y + 3y² - √5 y³ + y⁴)` -/

/-- `-log (1 - √5 y + 3y² - √5 y³ + y⁴) = ∑_k D(k) (√5)^(k mod 2) y^k / k` for a real `y`
with `|y| < 1`. -/
theorem hasSum_aur {y : ℝ} (hy : |y| < 1) :
    HasSum (fun k : ℕ => (aurD k : ℝ) * Real.sqrt 5 ^ (k % 2) * y ^ k / k)
      (-Real.log (1 - Real.sqrt 5 * y + 3 * y ^ 2 - Real.sqrt 5 * y ^ 3 + y ^ 4)) := by
  obtain ⟨v, h5, h1, hg⟩ := exists_gs5_eq_t5
  have hv : ‖v‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h5 (by norm_num)
  have n2 : ‖-v ^ 2‖ = 1 := by rw [norm_neg, norm_pow, hv, one_pow]
  have n3 : ‖-v ^ 3‖ = 1 := by rw [norm_neg, norm_pow, hv, one_pow]
  have n4 : ‖v ^ 4‖ = 1 := by rw [norm_pow, hv, one_pow]
  have h := (((hasSum_log_norm_one_sub hv hy).add (hasSum_log_norm_one_sub n2 hy)).add
    (hasSum_log_norm_one_sub n3 hy)).add (hasSum_log_norm_one_sub n4 hy)
  have hne : ∀ w : ℂ, ‖w‖ = 1 → ‖1 - w * (y : ℂ)‖ ≠ 0 := by
    intro w hw h0
    have h1' : w * (y : ℂ) = 1 := (sub_eq_zero.1 (norm_eq_zero.1 h0)).symm
    have h2 := congrArg norm h1'
    rw [norm_mul, hw, one_mul, Complex.norm_real, Real.norm_eq_abs, norm_one] at h2
    linarith
  have hval : -Real.log ‖1 - v * (y : ℂ)‖ + -Real.log ‖1 - -v ^ 2 * (y : ℂ)‖ +
      -Real.log ‖1 - -v ^ 3 * (y : ℂ)‖ + -Real.log ‖1 - v ^ 4 * (y : ℂ)‖ =
        -Real.log (1 - Real.sqrt 5 * y + 3 * y ^ 2 - Real.sqrt 5 * y ^ 3 + y ^ 4) := by
    have hprod : (1 - v * (y : ℂ)) * (1 - -v ^ 2 * (y : ℂ)) * (1 - -v ^ 3 * (y : ℂ)) *
        (1 - v ^ 4 * (y : ℂ)) =
          ((1 - Real.sqrt 5 * y + 3 * y ^ 2 - Real.sqrt 5 * y ^ 3 + y ^ 4 : ℝ) : ℂ) := by
      have h4 := four_factors h5 h1 (y : ℂ)
      rw [hg, t5] at h4
      push_cast
      rw [← h4]
      ring
    rw [← neg_add, ← neg_add, ← neg_add, neg_inj,
      ← Real.log_mul (hne v hv) (hne _ n2),
      ← Real.log_mul (mul_ne_zero (hne v hv) (hne _ n2)) (hne _ n3),
      ← Real.log_mul (mul_ne_zero (mul_ne_zero (hne v hv) (hne _ n2)) (hne _ n3)) (hne _ n4),
      ← norm_mul, ← norm_mul, ← norm_mul, hprod, Complex.norm_real, Real.norm_eq_abs,
      Real.log_abs]
  rw [hval] at h
  convert h using 1
  funext k
  have hp := congrArg Complex.re (psum_five h5 h1 k)
  have e : ((aurD k : ℂ) * gs5 v ^ (k % 2)).re = (aurD k : ℝ) * Real.sqrt 5 ^ (k % 2) := by
    have e' : (aurD k : ℂ) * gs5 v ^ (k % 2) =
        (((aurD k : ℝ) * Real.sqrt 5 ^ (k % 2) : ℝ) : ℂ) := by
      rw [hg, t5]
      push_cast
      rfl
    rw [e', Complex.ofReal_re]
  rw [e] at hp
  simp only [Complex.add_re] at hp
  rw [← hp]
  ring

/-! ## 6. The Aurifeuillian factors -/

theorem t5_pow_four (h : ℕ) : (t5 ^ h) ^ 4 = 5 ^ (2 * h) := by
  rw [← pow_mul, mul_comm h 4, show 4 * h = 2 * (2 * h) by ring, pow_mul, t5_sq]

/-- `L_h = T⁴ - √5 T³ + 3T² - √5 T + 1` with `T = (√5)^h`, `h` odd. -/
theorem L5_cast {h : ℕ} (hh : Odd h) :
    ((L5 h : ℤ) : ℂ) =
      (t5 ^ h) ^ 4 - t5 * (t5 ^ h) ^ 3 + 3 * (t5 ^ h) ^ 2 - t5 * t5 ^ h + 1 := by
  obtain ⟨k, rfl⟩ := hh
  have e : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h5 : t5 ^ (2 * k + 1) = 5 ^ k * t5 := by rw [pow_succ, pow_mul, t5_sq]
  simp only [L5, e]
  push_cast
  rw [h5]
  linear_combination (-(((5 : ℂ) ^ k) ^ 4 - ((5 : ℂ) ^ k) ^ 3) * (t5 ^ 2 + 5) -
    3 * ((5 : ℂ) ^ k) ^ 2 + (5 : ℂ) ^ k) * t5_sq

/-- `M_h = T⁴ + √5 T³ + 3T² + √5 T + 1` with `T = (√5)^h`, `h` odd. -/
theorem M5_cast {h : ℕ} (hh : Odd h) :
    ((M5 h : ℤ) : ℂ) =
      (t5 ^ h) ^ 4 + t5 * (t5 ^ h) ^ 3 + 3 * (t5 ^ h) ^ 2 + t5 * t5 ^ h + 1 := by
  obtain ⟨k, rfl⟩ := hh
  have e : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h5 : t5 ^ (2 * k + 1) = 5 ^ k * t5 := by rw [pow_succ, pow_mul, t5_sq]
  simp only [M5, e]
  push_cast
  rw [h5]
  linear_combination (-(((5 : ℂ) ^ k) ^ 4 + ((5 : ℂ) ^ k) ^ 3) * (t5 ^ 2 + 5) -
    3 * ((5 : ℂ) ^ k) ^ 2 - (5 : ℂ) ^ k) * t5_sq

theorem L5_real {h : ℕ} (hh : Odd h) :
    (L5 h : ℝ) = (Real.sqrt 5 ^ h) ^ 4 - Real.sqrt 5 * (Real.sqrt 5 ^ h) ^ 3 +
      3 * (Real.sqrt 5 ^ h) ^ 2 - Real.sqrt 5 * Real.sqrt 5 ^ h + 1 := by
  have h1 := L5_cast hh
  rw [t5] at h1
  exact_mod_cast h1

theorem M5_real {h : ℕ} (hh : Odd h) :
    (M5 h : ℝ) = (Real.sqrt 5 ^ h) ^ 4 + Real.sqrt 5 * (Real.sqrt 5 ^ h) ^ 3 +
      3 * (Real.sqrt 5 ^ h) ^ 2 + Real.sqrt 5 * Real.sqrt 5 ^ h + 1 := by
  have h1 := M5_cast hh
  rw [t5] at h1
  exact_mod_cast h1

theorem sqrt5_pow_four (h : ℕ) : (Real.sqrt 5 ^ h) ^ 4 = (5 : ℝ) ^ (2 * h) := by
  have h1 := t5_pow_four h
  rw [t5] at h1
  exact_mod_cast h1

theorem L5_pos (h : ℕ) : 0 < L5 h := by
  have h1 : (1 : ℤ) ≤ 5 ^ h := one_le_pow₀ (by norm_num)
  have h2 : (5 : ℤ) ^ ((h + 1) / 2) ≤ 5 ^ h :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (5 : ℤ) ^ ((h + 1) / 2) * (5 ^ h + 1) ≤ 5 ^ h * (5 ^ h + 1) :=
    mul_le_mul_of_nonneg_right h2 (by linarith)
  have e : (5 : ℤ) ^ (2 * h) = 5 ^ h * 5 ^ h := by ring
  rw [L5, e]
  nlinarith

theorem M5_pos (h : ℕ) : 0 < M5 h := by
  rw [M5]
  positivity

/-- The pattern of `log (L_h/5^(2h))` (`s = 1`) and of `log (M_h/5^(2h))` (`s = -1`): at
`k = h j` it is `-h s^j D(j)`, and `0` elsewhere. -/
def rhoAur (s : ℚ) (h : ℕ) (k : ℕ) : ℚ :=
  if h ∣ k then -(h : ℚ) * s ^ (k / h) * aurD (k / h) else 0

theorem rhoAur_periodic {s : ℚ} (hs : s = 1 ∨ s = -1) {h : ℕ} (hh : 0 < h) (k : ℕ) :
    rhoAur s h (k + 10 * h) = rhoAur s h k := by
  have h1 : h ∣ k + 10 * h ↔ h ∣ k := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, Nat.add_mul_mod_self_right]
  have h2 : (k + 10 * h) / h = k / h + 10 := Nat.add_mul_div_right k 10 hh
  have h3 : s ^ 10 = 1 := by rcases hs with rfl | rfl <;> norm_num
  simp only [rhoAur, h1, h2, aurD_periodic, pow_add, h3, mul_one]

theorem sqrt5_pow_eq (n : ℕ) :
    Real.sqrt 5 ^ n = (5 : ℝ) ^ (n / 2) * Real.sqrt 5 ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2]
  rw [pow_add, pow_mul, Real.sq_sqrt (by norm_num)]

/-- The series of the pattern `rhoAur s h`, for `h` odd and `s = ±1`. -/
theorem hasSum_rhoAur {h : ℕ} (hh : Odd h) {s : ℚ} (hs : s = 1 ∨ s = -1) :
    HasSum (seriesTerm5 (rhoAur s h))
      (Real.log (1 - Real.sqrt 5 * ((s : ℝ) / Real.sqrt 5 ^ h) +
        3 * ((s : ℝ) / Real.sqrt 5 ^ h) ^ 2 - Real.sqrt 5 * ((s : ℝ) / Real.sqrt 5 ^ h) ^ 3 +
        ((s : ℝ) / Real.sqrt 5 ^ h) ^ 4)) := by
  have hpos : 0 < h := hh.pos
  have hT : 1 < Real.sqrt 5 ^ h := one_lt_pow₀ one_lt_sqrt5 hpos.ne'
  have hT0 : (0 : ℝ) < Real.sqrt 5 ^ h := by linarith
  have hsabs : |(s : ℝ)| = 1 := by rcases hs with rfl | rfl <;> simp
  have hy : |(s : ℝ) / Real.sqrt 5 ^ h| < 1 := by
    rw [abs_div, abs_of_pos hT0, hsabs, div_lt_one hT0]
    exact hT
  have h1 := (hasSum_aur hy).neg
  rw [neg_neg] at h1
  have h2 := (hasSum_dvd_iff hpos _ _).2 h1
  convert h2 using 1
  funext k
  simp only [seriesTerm5, rhoAur]
  split_ifs with hk
  · obtain ⟨j, rfl⟩ := hk
    rw [Nat.mul_div_cancel_left j hpos]
    by_cases hj : j = 0
    · subst hj
      simp
    · have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      have hmod : (h * j) % 2 = j % 2 := by
        rw [Nat.mul_mod, Nat.odd_iff.1 hh, one_mul, Nat.mod_mod]
      have hr : Real.sqrt 5 ^ (j % 2) ≠ 0 := pow_ne_zero _ sqrt5_pos.ne'
      have hpow : (Real.sqrt 5 ^ h) ^ j = (5 : ℝ) ^ (h * j / 2) * Real.sqrt 5 ^ (j % 2) := by
        rw [← pow_mul, sqrt5_pow_eq (h * j), hmod]
      push_cast
      rw [div_pow, hpow]
      field_simp
  · simp

/-- **`log (L_h/5^(2h))` is a value of the class F5**, for `h` odd. -/
theorem isF5Value_log_L5 {h : ℕ} (hh : Odd h) :
    IsF5Value (Real.log ((L5 h : ℝ) / 5 ^ (2 * h))) := by
  have hT0 : (0 : ℝ) < Real.sqrt 5 ^ h := pow_pos sqrt5_pos h
  have e : (L5 h : ℝ) / 5 ^ (2 * h) = 1 - Real.sqrt 5 * (((1 : ℚ) : ℝ) / Real.sqrt 5 ^ h) +
      3 * (((1 : ℚ) : ℝ) / Real.sqrt 5 ^ h) ^ 2 -
      Real.sqrt 5 * (((1 : ℚ) : ℝ) / Real.sqrt 5 ^ h) ^ 3 +
      (((1 : ℚ) : ℝ) / Real.sqrt 5 ^ h) ^ 4 := by
    rw [L5_real hh, ← sqrt5_pow_four]
    push_cast
    field_simp
  rw [e]
  exact ⟨10 * h, rhoAur 1 h, by have := hh.pos; omega, rhoAur_periodic (Or.inl rfl) hh.pos,
    hasSum_rhoAur hh (Or.inl rfl)⟩

/-- **`log (M_h/5^(2h))` is a value of the class F5**, for `h` odd. -/
theorem isF5Value_log_M5 {h : ℕ} (hh : Odd h) :
    IsF5Value (Real.log ((M5 h : ℝ) / 5 ^ (2 * h))) := by
  have hT0 : (0 : ℝ) < Real.sqrt 5 ^ h := pow_pos sqrt5_pos h
  have e : (M5 h : ℝ) / 5 ^ (2 * h) = 1 - Real.sqrt 5 * (((-1 : ℚ) : ℝ) / Real.sqrt 5 ^ h) +
      3 * (((-1 : ℚ) : ℝ) / Real.sqrt 5 ^ h) ^ 2 -
      Real.sqrt 5 * (((-1 : ℚ) : ℝ) / Real.sqrt 5 ^ h) ^ 3 +
      (((-1 : ℚ) : ℝ) / Real.sqrt 5 ^ h) ^ 4 := by
    rw [M5_real hh, ← sqrt5_pow_four]
    push_cast
    field_simp
    ring
  rw [e]
  exact ⟨10 * h, rhoAur (-1) h, by have := hh.pos; omega, rhoAur_periodic (Or.inr rfl) hh.pos,
    hasSum_rhoAur hh (Or.inr rfl)⟩

/-! ## 7. The base numbers and their span -/

/-- The base numbers of base 5: `(5^m - 1)/5^m` for `m ≥ 1`, and `L_h/5^(2h)`, `M_h/5^(2h)`
for odd `h`. -/
def baseNumbers5 : Set ℚ :=
  {g | (∃ m : ℕ, 0 < m ∧ g = (5 ^ m - 1) / 5 ^ m) ∨
       (∃ h : ℕ, Odd h ∧ (g = (L5 h : ℚ) / 5 ^ (2 * h) ∨ g = (M5 h : ℚ) / 5 ^ (2 * h)))}

theorem baseNumbers5_pos {g : ℚ} (hg : g ∈ baseNumbers5) : 0 < g := by
  rcases hg with ⟨m, hm, rfl⟩ | ⟨h, -, rfl | rfl⟩
  · have h1 : (1 : ℚ) < 5 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
    exact div_pos (by linarith) (by positivity)
  · have h1 : (0 : ℚ) < (L5 h : ℚ) := by exact_mod_cast L5_pos h
    positivity
  · have h1 : (0 : ℚ) < (M5 h : ℚ) := by exact_mod_cast M5_pos h
    positivity

/-- The rational combinations of the logarithms of the base numbers. -/
noncomputable def baseSpan5 : Submodule ℚ ℝ :=
  Submodule.span ℚ ((fun g : ℚ => Real.log (g : ℝ)) '' baseNumbers5)

theorem log_mem_baseSpan5 {g : ℚ} (hg : g ∈ baseNumbers5) : Real.log (g : ℝ) ∈ baseSpan5 :=
  Submodule.subset_span ⟨g, hg, rfl⟩

theorem rat_mul_mem_baseSpan5 {x : ℝ} (hx : x ∈ baseSpan5) (q : ℚ) :
    (q : ℝ) * x ∈ baseSpan5 := by
  have h := baseSpan5.smul_mem q hx
  rwa [Rat.smul_def] at h

/-- `log (1 - 5^(-m))` is in the span. -/
theorem log_one_sub_mem_baseSpan5 {m : ℕ} (hm : 0 < m) :
    Real.log (1 - 1 / (5 : ℝ) ^ m) ∈ baseSpan5 := by
  have h := log_mem_baseSpan5 (g := (5 ^ m - 1) / 5 ^ m) (Or.inl ⟨m, hm, rfl⟩)
  have e : (((5 ^ m - 1) / 5 ^ m : ℚ) : ℝ) = 1 - 1 / (5 : ℝ) ^ m := by
    push_cast
    field_simp
  rwa [e] at h

theorem log_L5_mem_baseSpan5 {h : ℕ} (hh : Odd h) :
    Real.log ((L5 h : ℝ) / 5 ^ (2 * h)) ∈ baseSpan5 := by
  have h1 := log_mem_baseSpan5 (g := (L5 h : ℚ) / 5 ^ (2 * h)) (Or.inr ⟨h, hh, Or.inl rfl⟩)
  have e : (((L5 h : ℚ) / 5 ^ (2 * h) : ℚ) : ℝ) = (L5 h : ℝ) / 5 ^ (2 * h) := by push_cast; rfl
  rwa [e] at h1

theorem log_M5_mem_baseSpan5 {h : ℕ} (hh : Odd h) :
    Real.log ((M5 h : ℝ) / 5 ^ (2 * h)) ∈ baseSpan5 := by
  have h1 := log_mem_baseSpan5 (g := (M5 h : ℚ) / 5 ^ (2 * h)) (Or.inr ⟨h, hh, Or.inr rfl⟩)
  have e : (((M5 h : ℚ) / 5 ^ (2 * h) : ℚ) : ℝ) = (M5 h : ℝ) / 5 ^ (2 * h) := by push_cast; rfl
  rwa [e] at h1

/-- **The half of the criterion that needs no Baker.** Every rational combination of
logarithms of base numbers is the value of a series of the class F5. -/
theorem baseSpan5_le_f5Values : baseSpan5 ≤ f5Values := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨g, hg, rfl⟩
  change IsF5Value (Real.log (g : ℝ))
  rcases hg with ⟨m, hm, rfl⟩ | ⟨h, hh, rfl | rfl⟩
  · have h1 := isF5Value_log_pow_sub_one hm
    have e : (((5 ^ m - 1) / 5 ^ m : ℚ) : ℝ) = ((5 : ℝ) ^ m - 1) / 5 ^ m := by push_cast; rfl
    rwa [e]
  · have h1 := isF5Value_log_L5 hh
    have e : (((L5 h : ℚ) / 5 ^ (2 * h) : ℚ) : ℝ) = (L5 h : ℝ) / 5 ^ (2 * h) := by
      push_cast; rfl
    rwa [e]
  · have h1 := isF5Value_log_M5 hh
    have e : (((M5 h : ℚ) / 5 ^ (2 * h) : ℚ) : ℝ) = (M5 h : ℝ) / 5 ^ (2 * h) := by
      push_cast; rfl
    rwa [e]

theorem isF5Value_of_mem_baseSpan5 {x : ℝ} (hx : x ∈ baseSpan5) : IsF5Value x :=
  baseSpan5_le_f5Values hx

/-! ## 8. Rational combinations of logarithms and powers -/

/-- For positive rational numbers `Γ` and a positive rational `y`: `log y` is a rational
combination of the `log g`, `g ∈ Γ`, if and only if some power `y^k`, `k ≥ 1`, is a product of
integer powers of elements of `Γ`. (The version of `log_mem_span_iff_pow` for a set of
rational numbers.) -/
theorem log_mem_span_iff_pow_rat {Γ : Set ℚ} (hΓ : ∀ g ∈ Γ, 0 < g) {y : ℚ} (hy : 0 < y) :
    Real.log (y : ℝ) ∈ Submodule.span ℚ ((fun g : ℚ => Real.log (g : ℝ)) '' Γ) ↔
      ∃ k : ℕ, 0 < k ∧ ∃ (n : ℕ) (g : Fin n → ℚ) (e : Fin n → ℤ),
        (∀ i, g i ∈ Γ) ∧ y ^ k = ∏ i, g i ^ e i := by
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  constructor
  · intro h
    obtain ⟨n, f, g', hsum⟩ := Submodule.mem_span_set'.1 h
    have hex : ∀ i, ∃ γ : ℚ, γ ∈ Γ ∧ Real.log (γ : ℝ) = (g' i : ℝ) := fun i => (g' i).2
    choose γ hγΓ hγ using hex
    set D : ℕ := ∏ i, (f i).den with hD
    have hDpos : 0 < D := Finset.prod_pos fun i _ => (f i).den_pos
    let e : Fin n → ℤ := fun i => (f i).num * ((D / (f i).den : ℕ) : ℤ)
    have he : ∀ i, ((e i : ℤ) : ℝ) = (D : ℝ) * ((f i : ℚ) : ℝ) := by
      intro i
      obtain ⟨q, hq⟩ : (f i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have hdiv : D / (f i).den = q := by
        rw [hq]
        exact Nat.mul_div_cancel_left q (f i).den_pos
      have hden : ((f i).den : ℝ) ≠ 0 := by exact_mod_cast (f i).den_pos.ne'
      have hfi : ((f i : ℚ) : ℝ) = ((f i).num : ℝ) / ((f i).den : ℝ) := Rat.cast_def _
      simp only [e, hdiv]
      rw [hfi, hq]
      push_cast
      field_simp
    have hγpos : ∀ i, (0 : ℝ) < ((γ i : ℚ) : ℝ) := fun i => by
      exact_mod_cast hΓ _ (hγΓ i)
    refine ⟨D, hDpos, n, γ, e, hγΓ, ?_⟩
    have h1 : Real.log ((y : ℝ) ^ D) = Real.log (∏ i, ((γ i : ℚ) : ℝ) ^ e i) := by
      rw [Real.log_pow, Real.log_prod (fun i _ => (zpow_pos (hγpos i) _).ne'), ← hsum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.log_zpow, he, hγ, Rat.smul_def]
      ring
    have h2 : (y : ℝ) ^ D = ∏ i, ((γ i : ℚ) : ℝ) ^ e i :=
      Real.log_injOn_pos (Set.mem_Ioi.2 (pow_pos hyR D))
        (Set.mem_Ioi.2 (Finset.prod_pos fun i _ => zpow_pos (hγpos i) _)) h1
    have h3 : ((y ^ D : ℚ) : ℝ) = ((∏ i, γ i ^ e i : ℚ) : ℝ) := by
      simp only [Rat.cast_pow, Rat.cast_prod, Rat.cast_zpow]
      exact h2
    exact Rat.cast_injective h3
  · rintro ⟨k, hk, n, g, e, hg, hprod⟩
    have hgpos : ∀ i, (0 : ℝ) < ((g i : ℚ) : ℝ) := fun i => by exact_mod_cast hΓ _ (hg i)
    have h1 : (y : ℝ) ^ k = ∏ i, ((g i : ℚ) : ℝ) ^ e i := by
      have h0 := congrArg (fun q : ℚ => (q : ℝ)) hprod
      simp only [Rat.cast_pow, Rat.cast_prod, Rat.cast_zpow] at h0
      exact h0
    have h2 := congrArg Real.log h1
    rw [Real.log_pow, Real.log_prod (fun i _ => (zpow_pos (hgpos i) _).ne')] at h2
    simp only [Real.log_zpow] at h2
    have hmem : (k : ℝ) * Real.log (y : ℝ) ∈
        Submodule.span ℚ ((fun g : ℚ => Real.log (g : ℝ)) '' Γ) := by
      rw [h2]
      refine Submodule.sum_mem _ fun i _ => ?_
      have h3 := Submodule.smul_mem (Submodule.span ℚ ((fun g : ℚ => Real.log (g : ℝ)) '' Γ))
        (e i : ℚ) (Submodule.subset_span ⟨g i, hg i, rfl⟩)
      rw [Rat.smul_def] at h3
      exact_mod_cast h3
    have h4 := Submodule.smul_mem _ ((k : ℚ)⁻¹) hmem
    rw [Rat.smul_def] at h4
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have e2 : (((k : ℚ)⁻¹ : ℚ) : ℝ) * ((k : ℝ) * Real.log (y : ℝ)) = Real.log (y : ℝ) := by
      push_cast
      field_simp
    rw [e2] at h4
    exact h4

/-- `log y` is in the span of the logarithms of the base numbers if and only if some power of
`y` is a product of integer powers of base numbers. -/
theorem log_mem_baseSpan5_iff_pow {y : ℚ} (hy : 0 < y) :
    Real.log (y : ℝ) ∈ baseSpan5 ↔
      ∃ k : ℕ, 0 < k ∧ ∃ (n : ℕ) (g : Fin n → ℚ) (e : Fin n → ℤ),
        (∀ i, g i ∈ baseNumbers5) ∧ y ^ k = ∏ i, g i ^ e i :=
  log_mem_span_iff_pow_rat (fun _ hg => baseNumbers5_pos hg) hy

/-- **The "if" half, without Baker.** If some power `y^k`, `k ≥ 1`, of a positive rational
`y` is a product of integer powers of base numbers, then `log y` is the value of a series of
the class F5. -/
theorem isF5Value_log_of_pow {y : ℚ} (hy : 0 < y) {k : ℕ} (hk : 0 < k) {n : ℕ}
    {g : Fin n → ℚ} {e : Fin n → ℤ} (hg : ∀ i, g i ∈ baseNumbers5)
    (h : y ^ k = ∏ i, g i ^ e i) : IsF5Value (Real.log (y : ℝ)) :=
  isF5Value_of_mem_baseSpan5 ((log_mem_baseSpan5_iff_pow hy).2 ⟨k, hk, n, g, e, hg, h⟩)

end Base5

end PiFormula
