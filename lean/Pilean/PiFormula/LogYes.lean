/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula.LogPrimes

/-!
# Primes below 100 whose logarithm has a binary BBP-type formula, and the classification

`LogPrimes.lean` shows that ten primes below 100 have no formula in the class F. This file
proves the other direction, without Baker's theorem: the remaining fifteen primes have one.

The formulas come from one family. For `n ≥ 1` and a unit `c` of `ℤ[i]`, the roots `r` of
`X^n = c` satisfy `∏ (t - r) = t^n - c` (with `t = 1 + i`), so

    ∑_r log |1 - r/t|  =  log |t^n - c| - n log |t|  =  (1/2) log N(t^n - c) - (n/2) log 2,

and the left side is a series of the class F of period `8n` (`isFValue_gen`). So `log M` is a
value of F whenever `M` is the norm of some `t^n - c` (`isFValue_log_of_gen`), and the values
of F are closed under sums and rational multiples (`IsFValue.add`, `IsFValue.const_mul`).

| prime | `n` | `c` | `N(t^n - c)` |
|---|---|---|---|
| 2 | 1 | 1 | 1 |
| 5 | 1 | -1 | 5 |
| 3 | 2 | -i | 3² |
| 13 | 3 | 1 | 13 |
| 17 | 4 | i | 17 |
| 41 | 5 | 1 | 41 |
| 7 | 6 | -i | 7² |
| 29 | 7 | -1 | 5 · 29 |
| 37 | 9 | 1 | 13 · 37 |
| 11 | 10 | -i | (3 · 11)² |
| 31 | 10 | i | 31² |
| 43 | 14 | i | (3 · 43)² |
| 61 | 15 | 1 | 13 · 41 · 61 |
| 19 | 18 | -i | (3³ · 19)² |
| 73 | 18 | i | (7 · 73)² |

`log_primes_below_100` (from Baker's theorem): for a prime `p < 100`, `log p` is a value of
the class F if and only if `p` is one of these fifteen. `isFValue_log_23_add_log_89`:
`log 23 + log 89` is a value, although neither `log 23` nor `log 89` is.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

/-! ## 1. The values of the class F form a rational vector space -/

theorem IsFValue.add {x y : ℝ} (hx : IsFValue x) (hy : IsFValue y) : IsFValue (x + y) := by
  obtain ⟨N, f, hN, hf, hfs⟩ := hx
  obtain ⟨M, g, hM, hg, hgs⟩ := hy
  refine ⟨N * M, f + g, Nat.mul_pos hN hM, fun k => ?_, ?_⟩
  · simp only [Pi.add_apply]
    rw [periodic_mul hf M k, Nat.mul_comm N M, periodic_mul hg N k]
  · have h := hfs.add hgs
    convert h using 1
    funext k
    exact seriesTerm_add f g k

theorem IsFValue.const_mul (c : ℚ) {x : ℝ} (hx : IsFValue x) : IsFValue (c * x) := by
  obtain ⟨N, f, hN, hf, hfs⟩ := hx
  refine ⟨N, c • f, hN, fun k => by simp only [Pi.smul_apply, hf], ?_⟩
  have h := hfs.mul_left (c : ℝ)
  convert h using 1
  funext k
  exact seriesTerm_smul c f k

theorem IsFValue.sub {x y : ℝ} (hx : IsFValue x) (hy : IsFValue y) : IsFValue (x - y) := by
  have h := hx.add (hy.const_mul (-1))
  convert h using 1
  push_cast
  ring

/-! ## 2. The roots of `X^n = c` -/

theorem nthRoots_repr {n : ℕ} (hn : 0 < n) (c : ℂ) :
    ∃ ζ α : ℂ, IsPrimitiveRoot ζ n ∧ α ^ n = c ∧
      nthRoots n c = (Multiset.range n).map (ζ ^ · * α) := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq c hn
  exact ⟨_, α, Complex.isPrimitiveRoot_exp n hn.ne', hα,
    (Complex.isPrimitiveRoot_exp n hn.ne').nthRoots_eq hα⟩

theorem card_nthRoots_eq {n : ℕ} (hn : 0 < n) (c : ℂ) : Multiset.card (nthRoots n c) = n := by
  obtain ⟨ζ, α, -, -, hS⟩ := nthRoots_repr hn c
  rw [hS, Multiset.card_map, Multiset.card_range]

/-- The power sums of the roots of `X^n = c`: `n c^(k/n)` if `n ∣ k`, and `0` otherwise. -/
theorem psum_nthRoots {n : ℕ} (hn : 0 < n) (c : ℂ) (k : ℕ) :
    psum (nthRoots n c) k = if n ∣ k then (n : ℂ) * c ^ (k / n) else 0 := by
  obtain ⟨ζ, α, hζ, hα, hS⟩ := nthRoots_repr hn c
  have e : psum (nthRoots n c) k = α ^ k * ∑ j ∈ Finset.range n, (ζ ^ k) ^ j := by
    rw [hS, psum, Multiset.map_map, Finset.mul_sum, Finset.sum_eq_multiset_sum,
      Finset.range_val]
    congr 1
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [Function.comp_apply]
    ring
  rw [e]
  split_ifs with hk
  · obtain ⟨m, rfl⟩ := hk
    have h1 : ζ ^ (n * m) = 1 := by rw [pow_mul, hζ.pow_eq_one, one_pow]
    rw [h1, Nat.mul_div_cancel_left m hn, pow_mul, hα]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  · have h1 : ζ ^ k ≠ 1 := fun h => hk ((hζ.pow_eq_one_iff_dvd k).1 h)
    have h2 : (ζ ^ k) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have h3 := geom_sum_mul (ζ ^ k) n
    rw [h2, sub_self] at h3
    rw [(mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 h1), mul_zero]

/-- `∏ (t - r) = t^n - c` over the roots `r` of `X^n = c`. -/
theorem zO_nthRoots {n : ℕ} (hn : 0 < n) (c : ℂ) : zO (nthRoots n c) = tC ^ n - c := by
  have hm : (X ^ n - C c : ℂ[X]).Monic := monic_X_pow_sub_C c hn.ne'
  have hcard : Multiset.card (X ^ n - C c : ℂ[X]).roots = (X ^ n - C c : ℂ[X]).natDegree := by
    rw [natDegree_X_pow_sub_C]
    exact card_nthRoots_eq hn c
  have h := congrArg (eval tC) (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard)
  rw [eval_multiset_prod, Multiset.map_map] at h
  simpa [zO, nthRoots, Function.comp_def] using h

/-! ## 3. The generators: `log N(t^n - c)` is a value of the class F -/

/-- The power sums of the roots of `X^n = c`, in `ℤ[i]`. -/
def PnZ (n : ℕ) (c : GaussianInt) (k : ℕ) : GaussianInt :=
  if n ∣ k then (n : GaussianInt) * c ^ (k / n) else 0

theorem psum_PnZ {n : ℕ} (hn : 0 < n) (c : GaussianInt) (k : ℕ) :
    psum (nthRoots n (c : ℂ)) k = ((PnZ n c k : GaussianInt) : ℂ) := by
  rw [psum_nthRoots hn, PnZ]
  split_ifs <;> simp

theorem UZ_add_eight_mul (k m : ℕ) : UZ (k + 8 * m) = UZ k := by
  have h2 : 2 ∣ k + 8 * m ↔ 2 ∣ k := by omega
  have e2 : (k + 8 * m) / 2 = k / 2 + 4 * m := by omega
  simp only [UZ, h2, e2, pow_add_four_mul negI_pow_four]

theorem PnZ_periodic {n : ℕ} (hn : 0 < n) {c : GaussianInt} (hc : c ^ 4 = 1) (k : ℕ) :
    PnZ n c (k + 8 * n) = PnZ n c k := by
  have h1 : n ∣ k + 8 * n ↔ n ∣ k := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, Nat.add_mul_mod_self_right]
  have e : (k + 8 * n) / n = k / n + 4 * 2 := Nat.add_mul_div_right k 8 hn
  simp only [PnZ, h1, e, pow_add_four_mul hc]

theorem rhoL_PnZ_periodic {n : ℕ} (hn : 0 < n) {c : GaussianInt} (hc : c ^ 4 = 1) (k : ℕ) :
    rhoL (PnZ n c) (k + 8 * n) = rhoL (PnZ n c) k := by
  simp only [rhoL, PnZ_periodic hn hc, UZ_add_eight_mul]

theorem log_norm_tC : Real.log ‖tC‖ = Real.log 2 / 2 := by
  have h := congrArg Real.log norm_tC_sq
  rw [Real.log_pow] at h
  push_cast at h
  linarith

theorem log_norm_toComplex (z : GaussianInt) :
    Real.log ‖(z : ℂ)‖ = Real.log ((z.norm : ℤ) : ℝ) / 2 := by
  rw [GaussianInt.intCast_real_norm, ← Complex.sq_norm, Real.log_pow]
  push_cast
  ring

/-- The series of the roots of `X^n = c`. -/
theorem hasSum_gen {n : ℕ} (hn : 0 < n) {c : GaussianInt} (hc : c ^ 4 = 1) :
    HasSum (seriesTerm (rhoL (PnZ n c)))
      (Real.log (((tG ^ n - c).norm : ℤ) : ℝ) / 2 - n * (Real.log 2 / 2)) := by
  have hcn : ‖(c : ℂ)‖ = 1 := by
    have h := congrArg (fun z : GaussianInt => ‖(z : ℂ)‖) hc
    simp only [map_pow, norm_pow, map_one, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h
  have hS : ∀ r ∈ nthRoots n (c : ℂ), ‖r‖ = 1 := by
    intro r hr
    have h := congrArg norm ((mem_nthRoots hn).1 hr)
    rw [norm_pow, hcn] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h
  have e : ((tG ^ n - c : GaussianInt) : ℂ) = tC ^ n - (c : ℂ) := by
    rw [map_sub, map_pow, tG_toComplex]
  have h := hasSum_LOG hS
  rw [LOG_eq hS, zO_nthRoots hn, card_nthRoots_eq hn, ← e, log_norm_toComplex, log_norm_tC] at h
  convert h using 1
  funext k
  exact (tauL_eq_rhoL (psum_PnZ hn c) k).symm

/-- **The generators.** `(1/2) log N(t^n - c) - (n/2) log 2` is a value of the class F. -/
theorem isFValue_gen {n : ℕ} (hn : 0 < n) {c : GaussianInt} (hc : c ^ 4 = 1) :
    IsFValue (Real.log (((tG ^ n - c).norm : ℤ) : ℝ) / 2 - n * (Real.log 2 / 2)) :=
  ⟨8 * n, rhoL (PnZ n c), by omega, rhoL_PnZ_periodic hn hc, hasSum_gen hn hc⟩

/-- `log 2` is a value: `n = 1`, `c = 1`, and `t - 1 = i`. -/
theorem isFValue_log_2 : IsFValue (Real.log 2) := by
  have h := isFValue_gen (n := 1) one_pos (c := 1) (one_pow 4)
  have e : (tG ^ 1 - 1 : GaussianInt).norm = 1 := by decide
  rw [e] at h
  have h2 := h.const_mul (-2)
  convert h2 using 1
  simp only [Int.cast_one, Real.log_one]
  push_cast
  ring

/-- If `x` is the norm of `t^n - c`, then `log x` is a value of the class F. -/
theorem isFValue_log_of_gen {n : ℕ} (hn : 0 < n) {c : GaussianInt} (hc : c ^ 4 = 1) {M : ℤ}
    (hM : (tG ^ n - c).norm = M) {x : ℝ} (hx : (M : ℝ) = x) : IsFValue (Real.log x) := by
  have h := isFValue_gen hn hc
  rw [hM, hx] at h
  have h2 := (h.add (isFValue_log_2.const_mul ((n : ℚ) / 2))).const_mul 2
  convert h2 using 1
  push_cast
  ring

theorem IsFValue.log_of_sq {a : ℝ} (h : IsFValue (Real.log (a ^ 2))) : IsFValue (Real.log a) := by
  have h2 := h.const_mul (1 / 2)
  convert h2 using 1
  rw [Real.log_pow]
  push_cast
  ring

theorem IsFValue.log_of_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : IsFValue (Real.log (a * b))) (h' : IsFValue (Real.log a)) : IsFValue (Real.log b) := by
  have h2 := h.sub h'
  convert h2 using 1
  rw [Real.log_mul ha.ne' hb.ne']
  ring

/-! ## 4. The fifteen primes -/

theorem neg_one_pow_four : (-1 : GaussianInt) ^ 4 = 1 := by decide

theorem isFValue_log_5 : IsFValue (Real.log 5) :=
  isFValue_log_of_gen (n := 1) (by norm_num) neg_one_pow_four (M := 5) (by decide)
    (by norm_num)

theorem isFValue_log_3 : IsFValue (Real.log 3) :=
  (isFValue_log_of_gen (n := 2) (by norm_num) negI_pow_four (M := 9) (by decide)
    (x := 3 ^ 2) (by norm_num)).log_of_sq

theorem isFValue_log_13 : IsFValue (Real.log 13) :=
  isFValue_log_of_gen (n := 3) (by norm_num) (one_pow 4) (M := 13) (by decide) (by norm_num)

theorem isFValue_log_17 : IsFValue (Real.log 17) :=
  isFValue_log_of_gen (n := 4) (by norm_num) gI_pow_four (M := 17) (by decide) (by norm_num)

theorem isFValue_log_41 : IsFValue (Real.log 41) :=
  isFValue_log_of_gen (n := 5) (by norm_num) (one_pow 4) (M := 41) (by decide) (by norm_num)

theorem isFValue_log_7 : IsFValue (Real.log 7) :=
  (isFValue_log_of_gen (n := 6) (by norm_num) negI_pow_four (M := 49) (by decide)
    (x := 7 ^ 2) (by norm_num)).log_of_sq

theorem isFValue_log_29 : IsFValue (Real.log 29) :=
  (isFValue_log_of_gen (n := 7) (by norm_num) neg_one_pow_four (M := 145) (by decide)
    (x := 5 * 29) (by norm_num)).log_of_mul (by norm_num) (by norm_num) isFValue_log_5

theorem isFValue_log_37 : IsFValue (Real.log 37) :=
  (isFValue_log_of_gen (n := 9) (by norm_num) (one_pow 4) (M := 481) (by decide)
    (x := 13 * 37) (by norm_num)).log_of_mul (by norm_num) (by norm_num) isFValue_log_13

theorem isFValue_log_11 : IsFValue (Real.log 11) :=
  (isFValue_log_of_gen (n := 10) (by norm_num) negI_pow_four (M := 1089) (by decide)
    (x := (3 * 11) ^ 2) (by norm_num)).log_of_sq.log_of_mul (by norm_num) (by norm_num)
    isFValue_log_3

theorem isFValue_log_31 : IsFValue (Real.log 31) :=
  (isFValue_log_of_gen (n := 10) (by norm_num) gI_pow_four (M := 961) (by decide)
    (x := 31 ^ 2) (by norm_num)).log_of_sq

theorem isFValue_log_43 : IsFValue (Real.log 43) :=
  (isFValue_log_of_gen (n := 14) (by norm_num) gI_pow_four (M := 16641) (by decide)
    (x := (3 * 43) ^ 2) (by norm_num)).log_of_sq.log_of_mul (by norm_num) (by norm_num)
    isFValue_log_3

theorem isFValue_log_61 : IsFValue (Real.log 61) :=
  ((isFValue_log_of_gen (n := 15) (by norm_num) (one_pow 4) (M := 32513) (by decide)
    (x := 13 * (41 * 61)) (by norm_num)).log_of_mul (by norm_num) (by norm_num)
    isFValue_log_13).log_of_mul (by norm_num) (by norm_num) isFValue_log_41

theorem isFValue_log_19 : IsFValue (Real.log 19) :=
  (((isFValue_log_of_gen (n := 18) (by norm_num) negI_pow_four (M := 263169) (by decide)
    (x := (3 * (3 * (3 * 19))) ^ 2) (by norm_num)).log_of_sq.log_of_mul (by norm_num)
    (by norm_num) isFValue_log_3).log_of_mul (by norm_num) (by norm_num)
    isFValue_log_3).log_of_mul (by norm_num) (by norm_num) isFValue_log_3

theorem isFValue_log_73 : IsFValue (Real.log 73) :=
  (isFValue_log_of_gen (n := 18) (by norm_num) gI_pow_four (M := 261121) (by decide)
    (x := (7 * 73) ^ 2) (by norm_num)).log_of_sq.log_of_mul (by norm_num) (by norm_num)
    isFValue_log_7

/-- `log 23 + log 89 = log (2^11 - 1)` is a value of the class F (`n = 22`, `c = -i`), although
neither `log 23` nor `log 89` is (`not_isFValue_log_of_mem`). -/
theorem isFValue_log_23_add_log_89 : IsFValue (Real.log 23 + Real.log 89) := by
  have h := (isFValue_log_of_gen (n := 22) (by norm_num) negI_pow_four (M := 4190209)
    (by decide) (x := (23 * 89) ^ 2) (by norm_num)).log_of_sq
  rwa [Real.log_mul (by norm_num) (by norm_num)] at h

/-! ## 5. The classification below 100 -/

/-- The fifteen primes below 100 whose logarithm has a formula in the class F. -/
def logPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73}

/-- **Fifteen primes with a formula (no Baker).** -/
theorem isFValue_log_of_mem {p : ℕ} (hp : p ∈ logPrimes) : IsFValue (Real.log p) := by
  simp only [logPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact_mod_cast isFValue_log_2
  · exact_mod_cast isFValue_log_3
  · exact_mod_cast isFValue_log_5
  · exact_mod_cast isFValue_log_7
  · exact_mod_cast isFValue_log_11
  · exact_mod_cast isFValue_log_13
  · exact_mod_cast isFValue_log_17
  · exact_mod_cast isFValue_log_19
  · exact_mod_cast isFValue_log_29
  · exact_mod_cast isFValue_log_31
  · exact_mod_cast isFValue_log_37
  · exact_mod_cast isFValue_log_41
  · exact_mod_cast isFValue_log_43
  · exact_mod_cast isFValue_log_61
  · exact_mod_cast isFValue_log_73

/-- Every prime below 100 is in one of the two lists. -/
theorem prime_lt_100 {p : ℕ} (hp : p.Prime) (h100 : p < 100) :
    p ∈ logPrimes ∨ p ∈ noLogPrimes := by
  interval_cases p <;> first | decide | (exfalso; norm_num at hp)

/-- **Logarithms of the primes below 100 (from Baker's theorem).** For a prime `p < 100`,
`log p` is the value of a series `∑ ρ(k) 2^(-⌊k/2⌋)/k` with `ρ` rational and periodic if and
only if `p` is one of `2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73`. -/
theorem log_primes_below_100 (hB : BakerTheorem) {p : ℕ} (hp : p.Prime) (h100 : p < 100) :
    IsFValue (Real.log p) ↔ p ∈ logPrimes := by
  refine ⟨fun h => ?_, isFValue_log_of_mem⟩
  rcases prime_lt_100 hp h100 with h1 | h2
  · exact h1
  · exact absurd h (not_isFValue_log_of_mem hB h2)

end PiFormula
