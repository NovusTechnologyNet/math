/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula.Arctan

/-!
# Which logarithms are values of the class F: the general families, and 38737

The note states a criterion (Theorem K): for a positive rational `y`, `log y` is the value
of a series of the class F if and only if `log y` is a rational combination of `log 2` and
the numbers `log N((1+i)^n - c)`, `n ≥ 1`, `c ∈ {1, -1, i, -i}`. Up to squares these norms
are the numbers `2^m - 1` and the two factors `2^n ∓ 2^((n+1)/2) + 1` of `4^n + 1`, `n` odd.

This file proves the half that needs no Baker, in general:

* `fValues`: the values of the class F form a vector space over `ℚ`;
* `logSpan_le_fValues`: every rational combination of `log 2` and the `log N((1+i)^n - c)`
  is a value of F;
* `isFValue_log_two_pow_sub_one`: `log (2^m - 1)` is a value, for every `m ≥ 1`;
* `isFValue_log_L`, `isFValue_log_M`: `log (2^n - 2^((n+1)/2) + 1)` and
  `log (2^n + 2^((n+1)/2) + 1)` are values, for every odd `n`.

The other half (no other logarithm of a rational is a value) is proved from Baker's theorem
in `LogConverse.lean`, and `LogExplicit.lean` states the criterion in elementary terms. The
finite test for a prime is not formal in general; it is formal prime by prime:
`LogPrimes.lean` for the ten primes below 100, and here for the pair 433, 38737.

**38737.** The list A104885 of the OEIS ("primes whose logarithms are known to possess binary
BBP formulas", from Borwein and Bailey's book of 2004) contains 38737. Here
(`not_isFValue_log_38737`, from Baker's theorem): `log 38737` is not a value of the class F.
The reason is the one for 23: `Φ_72(2) = 2^24 - 2^12 + 1 = 433 · 38737`, and the two primes
always occur together. `isFValue_log_433_add_log_38737`: the sum `log 433 + log 38737` is a
value. Bailey's compendium of 2023 does not list 38737.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

/-! ## 1. The values of F as a vector space -/

theorem isFValue_zero : IsFValue 0 :=
  ⟨1, 0, one_pos, fun _ => rfl, by rw [seriesTerm_zero]; exact hasSum_zero⟩

/-- The values of the class F, as a subspace of `ℝ` over `ℚ`. -/
def fValues : Submodule ℚ ℝ where
  carrier := {x | IsFValue x}
  add_mem' := fun hx hy => hx.add hy
  zero_mem' := isFValue_zero
  smul_mem' := fun c x hx => by
    have h : IsFValue ((c : ℝ) * x) := IsFValue.const_mul c hx
    simpa [Rat.smul_def] using h

theorem mem_fValues {x : ℝ} : x ∈ fValues ↔ IsFValue x := Iff.rfl

/-- `log N((1+i)^n - c)` is a value of the class F, for `n ≥ 1` and a unit `c` of `ℤ[i]`. -/
theorem isFValue_log_norm {n : ℕ} (hn : 0 < n) {c : GaussianInt} (hc : c ^ 4 = 1) :
    IsFValue (Real.log (((tG ^ n - c).norm : ℤ) : ℝ)) :=
  isFValue_log_of_gen hn hc rfl rfl

/-- The generators: `log 2` and the numbers `log N((1+i)^n - c)`. -/
def logGenerators : Set ℝ :=
  {x | x = Real.log 2 ∨ ∃ (n : ℕ) (c : GaussianInt), 0 < n ∧ c ^ 4 = 1 ∧
    x = Real.log (((tG ^ n - c).norm : ℤ) : ℝ)}

/-- The rational combinations of `log 2` and the `log N((1+i)^n - c)`. -/
noncomputable def logSpan : Submodule ℚ ℝ := Submodule.span ℚ logGenerators

/-- **The half of the criterion that needs no Baker.** Every rational combination of `log 2`
and the numbers `log N((1+i)^n - c)` is the value of a series of the class F. -/
theorem logSpan_le_fValues : logSpan ≤ fValues := by
  refine Submodule.span_le.2 ?_
  rintro x (rfl | ⟨n, c, hn, hc, rfl⟩)
  · exact isFValue_log_2
  · exact isFValue_log_norm hn hc

theorem isFValue_of_mem_logSpan {x : ℝ} (hx : x ∈ logSpan) : IsFValue x :=
  logSpan_le_fValues hx

/-! ## 2. The Mersenne family and the two factors of `4^n + 1` -/

theorem norm_gI : gI.norm = 1 := by decide

theorem gI_pow_pow_four (m : ℕ) : (gI ^ m) ^ 4 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, gI_pow_four, one_pow]

theorem norm_gI_pow (m : ℕ) : (gI ^ m).norm = 1 := by
  induction m with
  | zero => rw [pow_zero, Zsqrtd.norm_one]
  | succ m ih => rw [pow_succ, Zsqrtd.norm_mul, ih, norm_gI, one_mul]

/-- `N((1+i)^(2m) - i^m) = (2^m - 1)^2`. -/
theorem norm_tG_pow_two_mul (m : ℕ) : (tG ^ (2 * m) - gI ^ m).norm = (2 ^ m - 1) ^ 2 := by
  have h2 : tG ^ 2 = (2 : GaussianInt) * gI := by
    rw [tG_sq]
    ext <;> simp [gI]
  have e : tG ^ (2 * m) - gI ^ m = (((2 : ℤ) ^ m - 1 : ℤ) : GaussianInt) * gI ^ m := by
    rw [pow_mul, h2, mul_pow]
    push_cast
    ring
  rw [e, Zsqrtd.norm_mul, Zsqrtd.norm_intCast]
  rw [norm_gI_pow]
  ring

/-- **`log (2^m - 1)` is a value of the class F**, for every `m ≥ 1`. -/
theorem isFValue_log_two_pow_sub_one {m : ℕ} (hm : 0 < m) :
    IsFValue (Real.log ((2 : ℝ) ^ m - 1)) := by
  have h := isFValue_log_of_gen (n := 2 * m) (by omega) (gI_pow_pow_four m)
    (norm_tG_pow_two_mul m) (x := ((2 : ℝ) ^ m - 1) ^ 2) (by push_cast; ring)
  exact h.log_of_sq

/-- `(-tG)^n - 1` and `tG^n + 1` have the same norm for odd `n`. -/
theorem Uminus_odd (k : ℕ) : Uminus (2 * k + 1) = (tG ^ (2 * k + 1) - (-1)).norm := by
  unfold Uminus
  have e : (-tG) ^ (2 * k + 1) - 1 = -(tG ^ (2 * k + 1) - (-1)) := by
    rw [Odd.neg_pow ⟨k, rfl⟩]
    ring
  rw [e, Zsqrtd.norm_neg]

theorem neg_one_pow_four' : (-1 : GaussianInt) ^ 4 = 1 := by decide

/-- **`log (2^n - 2^((n+1)/2) + 1)` is a value of the class F**, for every odd `n`. -/
theorem isFValue_log_L (k : ℕ) : IsFValue (Real.log ((L (2 * k + 1) : ℤ) : ℝ)) := by
  rcases Uplus_Uminus_odd k with ⟨h, -⟩ | ⟨-, h⟩
  · exact isFValue_log_of_gen (n := 2 * k + 1) (by omega) (one_pow 4) (by rw [← h]; rfl) rfl
  · exact isFValue_log_of_gen (n := 2 * k + 1) (by omega) neg_one_pow_four'
      (by rw [← h, Uminus_odd]) rfl

/-- **`log (2^n + 2^((n+1)/2) + 1)` is a value of the class F**, for every odd `n`. -/
theorem isFValue_log_M (k : ℕ) : IsFValue (Real.log ((M (2 * k + 1) : ℤ) : ℝ)) := by
  rcases Uplus_Uminus_odd k with ⟨-, h⟩ | ⟨h, -⟩
  · exact isFValue_log_of_gen (n := 2 * k + 1) (by omega) neg_one_pow_four'
      (by rw [← h, Uminus_odd]) rfl
  · exact isFValue_log_of_gen (n := 2 * k + 1) (by omega) (one_pow 4) (by rw [← h]; rfl) rfl

/-! ## 3. The pair 433, 38737 -/

theorem ord_two_433 : orderOf (2 : ZMod 433) = 72 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem ord_two_38737 : orderOf (2 : ZMod 38737) = 72 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

/-- The atom `Φ_9(4i) = -4095 - 64i`, of norm `Φ_72(2) = 16773121 = 433 · 38737`. -/
theorem atom_R40 : atom (.R 4 0) = ⟨-4095, -64⟩ := by
  simp only [atom, mOf, base]
  rw [show 2 * 4 + 1 = 3 ^ (1 + 1) by rfl,
    cyclotomic_prime_pow_eq_geom_sum (by norm_num : Nat.Prime 3), eval_finsetSum]
  simp only [eval_pow, eval_X]
  decide +kernel

/-- The atoms of index 72: only `R 4 0`. -/
theorem atoms_of_index_72 {a : Atom} (h : 4 * nOf a = 72) : a = .R 4 0 := by
  rcases a with k | k | ⟨k, e⟩
  · exfalso
    simp only [nOf] at h
    omega
  · exfalso
    simp only [nOf] at h
    omega
  · simp only [nOf] at h
    rcases e with _ | e
    · obtain rfl : k = 4 := by
        norm_num at h
        omega
      rfl
    · exfalso
      have h4 : 4 ∣ 2 ^ (e + 1 + 1) * (2 * k + 1) := by
        refine Dvd.dvd.mul_right ?_ _
        rw [show e + 1 + 1 = 2 + e by ring, pow_add]
        exact Dvd.intro _ rfl
      omega

theorem good_38737 (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) :
    ∃ p, p ≠ 38737 ∧ HasGoodPrimeAt r p := by
  refine goodPrimes_ne ord_two_38737 (fun a _ h => ?_) (fun k _ h => by omega)
    (fun k _ h => by omega) r hr hR0
  obtain rfl := atoms_of_index_72 h
  refine ⟨433, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num [mOf], ?_⟩
  rw [atom_R40]
  decide

theorem good_433 (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) :
    ∃ p, p ≠ 433 ∧ HasGoodPrimeAt r p := by
  refine goodPrimes_ne ord_two_433 (fun a _ h => ?_) (fun k _ h => by omega)
    (fun k _ h => by omega) r hr hR0
  obtain rfl := atoms_of_index_72 h
  refine ⟨38737, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num [mOf], ?_⟩
  rw [atom_R40]
  decide

/-- **`log 38737` is not a value of the class F** (from Baker's theorem), although 38737 is
on the list A104885 of the OEIS. -/
theorem not_isFValue_log_38737 (hB : BakerTheorem) : ¬ IsFValue (Real.log 38737) := by
  have h := not_isFValue_log hB (ℓ := 38737) (by norm_num) (by norm_num) (by norm_num)
    good_38737
  simpa using h

/-- `log 433` is not a value of the class F (from Baker's theorem). -/
theorem not_isFValue_log_433 (hB : BakerTheorem) : ¬ IsFValue (Real.log 433) := by
  have h := not_isFValue_log hB (ℓ := 433) (by norm_num) (by norm_num) (by norm_num) good_433
  simpa using h

/-- **`log 433 + log 38737` is a value of the class F** (no Baker):
`433 · 38737 = 2^24 - 2^12 + 1 = (2^36 + 1)/(2^12 + 1)`, and `2^36 + 1`, `2^12 + 1` are the
norms of `(1+i)^36 - i` and `(1+i)^12 - i`. -/
theorem isFValue_log_433_add_log_38737 : IsFValue (Real.log 433 + Real.log 38737) := by
  have h1 : IsFValue (Real.log 68719476737) :=
    isFValue_log_of_gen (n := 36) (by norm_num) gI_pow_four (M := 68719476737)
      (by decide +kernel) (by norm_num)
  have h2 : IsFValue (Real.log 4097) :=
    isFValue_log_of_gen (n := 12) (by norm_num) gI_pow_four (M := 4097) (by decide +kernel)
      (by norm_num)
  have h3 := h1.sub h2
  convert h3 using 1
  rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_div (by norm_num) (by norm_num)]
  norm_num

end PiFormula
