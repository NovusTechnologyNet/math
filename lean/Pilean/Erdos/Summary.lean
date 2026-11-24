/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.CriterionGeneral
public import Pilean.Erdos.EvenCase
public import Pilean.Erdos.SizeCase

/-!
# Erdős's conjecture on `∑ f(n)/n`: the cases that are proved, in plain terms

**Conjecture** (Erdős). Let `q ≥ 2` and let `f : ℕ → ℤ` have period `q`, with `f(n) = 0` when
`q ∣ n` and `f(n) = ±1` otherwise. Then `∑_{n ≥ 1} f(n)/n ≠ 0`.

Here "the sum is not `0`" means: the partial sums `∑_{1 ≤ n < N} f(n)/n` do not tend to `0`
(the series converges only conditionally, or not at all).

**Theorem** (`erdos_pm_one_of_cases`). The conjecture holds for `q ≥ 2` in each of the cases

* `q` is even (the series diverges; elementary and classical; `EvenCase.lean`);
* `q` is not a perfect square (for odd `q` this is `erdos_pm_one_nat`, `Final.lean`; it
  contains the case `q ≡ 3 mod 4` of M. R. Murty and N. Saradha, 2010:
  `erdos_three_mod_four_nat`);
* `∏_{p ∣ q} p/(p-1) ≤ 2`, i.e. `q ≤ 2 φ(q)` (T. Okada, 1982; `SizeCase.lean`; it contains
  the prime powers, and for prime `q` the theorem of Baker, Birch and Wirsing, 1973; see also
  T. Chatterjee and M. R. Murty, 2015).

**Corollary** (`erdos_pm_one_lt_11025`). The conjecture holds for every `q` with
`2 ≤ q < 11025`.

The bound is the right one for these three cases: `11025 = 105² = 3² 5² 7²` is odd, a perfect
square, and `∏_{p ∣ q} p/(p-1) = 35/16 > 2` (`not_cases_11025`). An odd `q < 11025` that is a
square is `n²` with `n < 105` odd, and then `n ≤ 2 φ(n)` (`small_totient`, a finite check).

The cases of odd `q` rest on Okada's criterion (the direction `okadaOnlyIf`), hence on Baker's
theorem (`lean/Baker/`); the three standard axioms only.

Status (23 November 2026): complete, no hypothesis left. The files of this extension:

* `Criterion.lean`: Okada's criterion in both directions for odd `q` and `f(0) = 0`
  (`okadaCriterion`), and the value of the series under condition (a);
* `CriterionGenFirst.lean`, `CriterionGenSecond.lean`, `CriterionGeneral.lean`: the same for
  every modulus `q ≥ 1` and every rational `f` (`okadaCriterionGeneral`);
* `EvenCase.lean`: even `q` (`erdos_even_nat`);
* `SizeCase.lean`: the size condition (`erdos_size_nat`, `abs_okadaG_sub_le`);
* this file.

Not covered: the odd squares `q` with `∏_{p ∣ q} p/(p-1) > 2` (the first is `11025`).
-/

@[expose] public section

open scoped BigOperators

open Filter

namespace PiFormula

namespace Erdos

/-! ## 1. The combined statement -/

/-- **Erdős's conjecture for even `q`, for `q` not a perfect square, and for
`∏_{p ∣ q} p/(p-1) ≤ 2`**, for functions on `ℤ/q`. -/
theorem erdos_pm_one_zmod_of_cases {q : ℕ} (hq : 2 ≤ q)
    (hcase : Even q ∨ ¬ IsSquare q ∨ ∏ p ∈ q.primeFactors, (p : ℚ) / ((p : ℚ) - 1) ≤ 2)
    (f : ZMod q → ℚ) (h0 : f 0 = 0) (hpm : ∀ r : ZMod q, r ≠ 0 → f r = 1 ∨ f r = -1) :
    ¬ SumIsZero q f := by
  have : NeZero q := ⟨by omega⟩
  rcases hcase with he | hns | hP
  · exact erdos_even he f h0 hpm
  · rcases Nat.even_or_odd q with he | ho
    · exact erdos_even he f h0 hpm
    · exact erdos_pm_one ho hns f h0 hpm
  · exact erdos_size hq hP f h0 hpm

/-- **Erdős's conjecture, the cases that are proved, in plain terms.** Let `q ≥ 2` be even,
or not a perfect square, or such that `∏_{p ∣ q} p/(p-1) ≤ 2`. If `f : ℕ → ℤ` has period `q`,
`f(n) = 0` when `q ∣ n` and `f(n) = ±1` otherwise, then the partial sums
`∑_{1 ≤ n < N} f(n)/n` do not tend to `0`. -/
theorem erdos_pm_one_of_cases {q : ℕ} (hq : 2 ≤ q)
    (hcase : Even q ∨ ¬ IsSquare q ∨ ∏ p ∈ q.primeFactors, (p : ℚ) / ((p : ℚ) - 1) ≤ 2)
    (f : ℕ → ℤ) (hper : ∀ n, f (n + q) = f n) (h0 : ∀ n, q ∣ n → f n = 0)
    (hpm : ∀ n, ¬ q ∣ n → f n = 1 ∨ f n = -1) :
    ¬ Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (f n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have : NeZero q := ⟨by omega⟩
  have key := erdos_pm_one_zmod_of_cases hq hcase (zmodLift q f) (zmodLift_zero f h0)
    (zmodLift_pm f hpm)
  unfold SumIsZero at key
  rw [partialSum_zmodLift f hper] at key
  exact key

/-- The same with the size condition written as `q ≤ 2 φ(q)` (Okada: `2 φ(q) + 1 > q`). -/
theorem erdos_pm_one_of_cases_totient {q : ℕ} (hq : 2 ≤ q)
    (hcase : Even q ∨ ¬ IsSquare q ∨ q ≤ 2 * q.totient)
    (f : ℕ → ℤ) (hper : ∀ n, f (n + q) = f n) (h0 : ∀ n, q ∣ n → f n = 0)
    (hpm : ∀ n, ¬ q ∣ n → f n = 1 ∨ f n = -1) :
    ¬ Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (f n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  refine erdos_pm_one_of_cases hq ?_ f hper h0 hpm
  rcases hcase with he | hns | hP
  · exact Or.inl he
  · exact Or.inr (Or.inl hns)
  · exact Or.inr (Or.inr ((sizeProd_le_two_iff q (by omega)).2 hP))

/-- A number `≡ 3 mod 4` is not a perfect square. -/
theorem not_isSquare_of_mod_four {q : ℕ} (hq : q % 4 = 3) : ¬ IsSquare q := by
  rintro ⟨n, rfl⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have e : 2 * k * (2 * k) = 4 * (k * k) := by ring
    omega
  · have e : (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 := by ring
    omega

/-- **The case `q ≡ 3 mod 4`** (M. R. Murty and N. Saradha, 2010), a special case of "`q` is
not a perfect square". -/
theorem erdos_three_mod_four_nat {q : ℕ} (hq : q % 4 = 3) (f : ℕ → ℤ)
    (hper : ∀ n, f (n + q) = f n) (h0 : ∀ n, q ∣ n → f n = 0)
    (hpm : ∀ n, ¬ q ∣ n → f n = 1 ∨ f n = -1) :
    ¬ Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (f n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
  erdos_pm_one_of_cases (by omega) (Or.inr (Or.inl (not_isSquare_of_mod_four hq))) f hper h0
    hpm

/-! ## 2. Every `q < 11025` -/

/-- A finite check: every odd `n < 105` has `n ≤ 2 φ(n)`. (`105 = 3 · 5 · 7` is the smallest
odd number with three prime factors, and `φ(105) = 48`.) -/
theorem small_totient : ∀ n < 105, n % 2 = 1 → n ≤ 2 * n.totient := by decide +kernel

/-- An odd perfect square `q < 11025` satisfies the size condition. -/
theorem sizeProd_le_two_of_lt {q : ℕ} (hq : q < 11025) (hodd : Odd q) (hsq : IsSquare q) :
    sizeProd q ≤ 2 := by
  obtain ⟨n, rfl⟩ := hsq
  have hn : n < 105 := by
    by_contra h
    have h' : 105 ≤ n := by omega
    have h2 := Nat.mul_le_mul h' h'
    omega
  have hnodd : n % 2 = 1 := Nat.odd_iff.1 (Nat.odd_mul.1 hodd).1
  have hn0 : n ≠ 0 := by
    rintro rfl
    omega
  rw [← pow_two, sizeProd_pow n two_ne_zero, sizeProd_le_two_iff n hn0]
  exact small_totient n hn hnodd

/-- Three odd squares that satisfy the size condition: `225 = 15²`, `441 = 21²`,
`1225 = 35²`. -/
theorem sizeProd_examples : sizeProd 225 ≤ 2 ∧ sizeProd 441 ≤ 2 ∧ sizeProd 1225 ≤ 2 :=
  ⟨sizeProd_le_two_of_lt (by norm_num) (by decide) ⟨15, by norm_num⟩,
    sizeProd_le_two_of_lt (by norm_num) (by decide) ⟨21, by norm_num⟩,
    sizeProd_le_two_of_lt (by norm_num) (by decide) ⟨35, by norm_num⟩⟩

/-- Every `q < 11025` is even, or not a perfect square, or has `∏_{p ∣ q} p/(p-1) ≤ 2`. -/
theorem cases_of_lt_11025 {q : ℕ} (hq : q < 11025) :
    Even q ∨ ¬ IsSquare q ∨ ∏ p ∈ q.primeFactors, (p : ℚ) / ((p : ℚ) - 1) ≤ 2 := by
  rcases Nat.even_or_odd q with he | ho
  · exact Or.inl he
  · by_cases hsq : IsSquare q
    · exact Or.inr (Or.inr (sizeProd_le_two_of_lt hq ho hsq))
    · exact Or.inr (Or.inl hsq)

/-- `∏_{p ∣ 11025} p/(p-1) = (3/2)(5/4)(7/6) = 35/16`. -/
theorem sizeProd_11025 : sizeProd 11025 = 35 / 16 := by
  have e : (11025 : ℕ) = 105 ^ 2 := by norm_num
  rw [e, sizeProd_pow 105 two_ne_zero]
  unfold sizeProd
  rw [← Nat.toFinset_factors]
  simp only [Nat.primeFactorsList_ofNat]
  norm_num [Finset.prod_insert]

/-- `q = 11025 = 105²` is in none of the three cases: the bound of `erdos_pm_one_lt_11025` is
the right one for them. -/
theorem not_cases_11025 :
    ¬ (Even 11025 ∨ ¬ IsSquare 11025 ∨
      ∏ p ∈ Nat.primeFactors 11025, (p : ℚ) / ((p : ℚ) - 1) ≤ 2) := by
  rintro (h | h | h)
  · exact absurd h (by decide)
  · exact h ⟨105, by norm_num⟩
  · have h' : sizeProd 11025 ≤ 2 := h
    rw [sizeProd_11025] at h'
    norm_num at h'

/-- **Erdős's conjecture for every `q` with `2 ≤ q < 11025`, in plain terms.** If
`f : ℕ → ℤ` has period `q`, `f(n) = 0` when `q ∣ n` and `f(n) = ±1` otherwise, then the
partial sums `∑_{1 ≤ n < N} f(n)/n` do not tend to `0`. -/
theorem erdos_pm_one_lt_11025 {q : ℕ} (hq : 2 ≤ q) (hlt : q < 11025) (f : ℕ → ℤ)
    (hper : ∀ n, f (n + q) = f n) (h0 : ∀ n, q ∣ n → f n = 0)
    (hpm : ∀ n, ¬ q ∣ n → f n = 1 ∨ f n = -1) :
    ¬ Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (f n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
  erdos_pm_one_of_cases hq (cases_of_lt_11025 hlt) f hper h0 hpm

end Erdos

end PiFormula
