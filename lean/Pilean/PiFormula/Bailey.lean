/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula.TheoremD

/-!
# Bailey's table: the zero relations at each period (milestone M8)

A *zero relation* is a rational pattern `ρ` with `∑ ρ(k) 2^(-⌊k/2⌋)/k = 0`.
`zeroSpace n` is the space of zero relations of period `n`, and `zeroSpaceEven n` the subspace
of those supported on even `k`. From Baker's theorem:

* `zeroSpace_gcd`: `zeroSpace n = zeroSpace (gcd n 120)` for every `n ≥ 1`. Only
  `gcd(n, 120)` matters.
* `finrank_zeroSpace`: for every `n ≥ 1` the number of independent zero relations of period
  `n` is `zeroCount (gcd n 120)`, which is `1, 1, 5, 3, 1, 7` at `8, 12, 24, 40, 60, 120` and
  `0` at the other ten divisors of 120. Each space is given with an explicit basis
  (`zeroSpace_8`, ..., `zeroSpace_120`).
* `finrank_zeroSpaceEven`: with support on even `k`, there is exactly one zero relation when
  `12 ∣ gcd(n, 120)`: `namedL24 - namedL8`.

**Bailey's table** (compendium of 8 April 2023, Table 1, binary degree-1 rows) lists the
number of zero relations `0 = ∑_{i=1}^n a_i ∑_j 2^(-Bj)/(nj + i)` for 27 pairs `(B, n)`.
With `k = nj + i`, a row with `n = 2B` is `zeroSpace n` (take `ρ(k) = a_i 2^⌊i/2⌋`), and a row
with `n = B` is `zeroSpaceEven (2n)` (take `ρ(2k) = 2^(i+1) a_i`). `bailey_F2` and
`bailey_F1` give the 27 counts for these spaces. The re-indexing between Bailey's sums and
the patterns is elementary and is not formalized here.
-/

@[expose] public section

open Complex

namespace PiFormula

/-! ## 1. The spaces -/

/-- The patterns of period `n`. -/
def periodSpace (n : ℕ) : Submodule ℚ (ℕ → ℚ) where
  carrier := {ρ | ∀ k, ρ (k + n) = ρ k}
  add_mem' := fun {ρ ρ'} h h' k => by simp only [Pi.add_apply, h k, h' k]
  zero_mem' := fun _ => rfl
  smul_mem' := fun c ρ h k => by simp only [Pi.smul_apply, h k]

/-- The zero relations: rational patterns whose series is 0. -/
def zeroAll : Submodule ℚ (ℕ → ℚ) where
  carrier := {ρ | HasSum (seriesTerm ρ) 0}
  add_mem' := by
    intro ρ ρ' h h'
    have h2 := HasSum.add h h'
    rw [add_zero] at h2
    have e : seriesTerm (ρ + ρ') = fun k => seriesTerm ρ k + seriesTerm ρ' k :=
      funext (seriesTerm_add ρ ρ')
    change HasSum (seriesTerm (ρ + ρ')) 0
    rw [e]
    exact h2
  zero_mem' := by
    change HasSum (seriesTerm 0) 0
    rw [seriesTerm_zero]
    exact hasSum_zero
  smul_mem' := by
    intro c ρ h
    have h2 := HasSum.mul_left (c : ℝ) h
    rw [mul_zero] at h2
    have e : seriesTerm (c • ρ) = fun k => (c : ℝ) * seriesTerm ρ k :=
      funext (seriesTerm_smul c ρ)
    change HasSum (seriesTerm (c • ρ)) 0
    rw [e]
    exact h2

/-- The patterns supported on even `k`. -/
def evenSupp : Submodule ℚ (ℕ → ℚ) where
  carrier := {ρ | ∀ k, k % 2 = 1 → ρ k = 0}
  add_mem' := fun {ρ ρ'} h h' k hk => by simp only [Pi.add_apply, h k hk, h' k hk, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c ρ h k hk => by simp only [Pi.smul_apply, h k hk, smul_zero]

/-- The zero relations of period `n`. -/
def zeroSpace (n : ℕ) : Submodule ℚ (ℕ → ℚ) := periodSpace n ⊓ zeroAll

/-- The zero relations of period `n` supported on even `k`. -/
def zeroSpaceEven (n : ℕ) : Submodule ℚ (ℕ → ℚ) := zeroSpace n ⊓ evenSupp

/-! ## 2. Periods -/

theorem periodic_mul {f : ℕ → ℚ} {a : ℕ} (h : ∀ k, f (k + a) = f k) (m k : ℕ) :
    f (k + a * m) = f k := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, ← add_assoc, h, ih]

theorem periodSpace_mono {a b : ℕ} (h : a ∣ b) : periodSpace a ≤ periodSpace b := by
  obtain ⟨m, rfl⟩ := h
  intro ρ hρ k
  exact periodic_mul hρ m k

/-- Two periods give their greatest common divisor as a period. -/
theorem periodic_gcd {f : ℕ → ℚ} {a b : ℕ} (hb : 0 < b) (h1 : ∀ k, f (k + a) = f k)
    (h2 : ∀ k, f (k + b) = f k) (k : ℕ) : f (k + Nat.gcd a b) = f k := by
  by_cases hlt : Nat.gcd a b < b
  · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd hlt
    have e : a * m = Nat.gcd a b + b * (a * m / b) := by
      rw [← hm]
      exact (Nat.mod_add_div _ _).symm
    have h3 := periodic_mul h1 m k
    rw [e, ← add_assoc, periodic_mul h2] at h3
    exact h3
  · have e : Nat.gcd a b = b :=
      le_antisymm (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) (not_lt.1 hlt)
    rw [e]
    exact h2 k

theorem mod_120 {f : ℕ → ℚ} (h : ∀ k, f (k + 120) = f k) (k : ℕ) : f (k % 120) = f k := by
  have h2 := periodic_mul h (k / 120) (k % 120)
  rw [Nat.mod_add_div] at h2
  exact h2.symm

/-- A pattern of period 120 has period `g` as soon as a table of 120 values says so. -/
theorem periodic_of_table {f : ℕ → ℚ} (h : ∀ k, f (k + 120) = f k) {g : ℕ}
    (htab : ∀ r < 120, f ((r + g) % 120) = f r) (k : ℕ) : f (k + g) = f k := by
  have h1 := htab (k % 120) (Nat.mod_lt k (by norm_num))
  rw [Nat.mod_add_mod, mod_120 h, mod_120 h] at h1
  exact h1

/-! ## 3. The basis patterns: periods and values -/

/-- `namedA10 - namedA1`: the zero relation of arctangent type, of period 40. -/
def zA : ℕ → ℚ := fun k => namedA10 k - namedA1 k

/-- `namedL24 - namedL8`: the zero relation of period 12, supported on even `k`. -/
def zL : ℕ → ℚ := fun k => namedL24 k - namedL8 k

theorem zA_periodic (k : ℕ) : zA (k + 120) = zA k := by
  simp only [zA, (named_periodic k).1, (named_periodic k).2.2.1]

theorem zL_periodic (k : ℕ) : zL (k + 120) = zL k := by
  simp only [zL, (named_periodic k).2.2.2.2.1, (named_periodic k).2.2.2.2.2.2.1]

theorem namedL8_period : ∀ k, namedL8 (k + 8) = namedL8 k :=
  periodic_of_table (fun k => (named_periodic k).2.2.2.2.1) (by decide +kernel)

theorem namedA6_period : ∀ k, namedA6 (k + 24) = namedA6 k :=
  periodic_of_table (fun k => (named_periodic k).2.1) (by decide +kernel)

theorem namedL6_period : ∀ k, namedL6 (k + 24) = namedL6 k :=
  periodic_of_table (fun k => (named_periodic k).2.2.2.1) (by decide +kernel)

theorem namedL24_period : ∀ k, namedL24 (k + 24) = namedL24 k :=
  periodic_of_table (fun k => (named_periodic k).2.2.2.2.2.2.1) (by decide +kernel)

theorem namedTW_period : ∀ k, namedTW (k + 24) = namedTW k :=
  periodic_of_table (fun k => (named_periodic k).2.2.2.2.2.2.2) (by decide +kernel)

theorem namedL10_period : ∀ k, namedL10 (k + 40) = namedL10 k :=
  periodic_of_table (fun k => (named_periodic k).2.2.2.2.2.1) (by decide +kernel)

theorem zA_period : ∀ k, zA (k + 40) = zA k :=
  periodic_of_table zA_periodic (by decide +kernel)

theorem zL_period : ∀ k, zL (k + 12) = zL k :=
  periodic_of_table zL_periodic (by decide +kernel)

theorem zL_even : zL ∈ evenSupp := by
  intro k hk
  have htab : ∀ r < 120, r % 2 = 1 → zL r = 0 := by decide +kernel
  rw [← mod_120 zL_periodic k]
  exact htab (k % 120) (Nat.mod_lt k (by norm_num)) (by omega)

theorem zA_zero : zA ∈ zeroAll := by
  have h := hasSum_namedA10.sub hasSum_namedA1
  rw [sub_self] at h
  have e : seriesTerm zA = fun k => seriesTerm namedA10 k - seriesTerm namedA1 k := by
    funext k
    simp only [seriesTerm, zA]
    push_cast
    ring
  change HasSum (seriesTerm zA) 0
  rw [e]
  exact h

theorem zL_zero : zL ∈ zeroAll := by
  have h := hasSum_namedL24.sub hasSum_namedL8
  rw [sub_self] at h
  have e : seriesTerm zL = fun k => seriesTerm namedL24 k - seriesTerm namedL8 k := by
    funext k
    simp only [seriesTerm, zL]
    push_cast
    ring
  change HasSum (seriesTerm zL) 0
  rw [e]
  exact h

theorem zL_values : zL 2 = -2 ∧ zL 6 = 4 ∧ zL 8 = 6 := by decide +kernel

theorem zL_ne_zero : zL ≠ 0 := by
  intro h
  have h2 := congrFun h 2
  rw [zL_values.1] at h2
  norm_num at h2

theorem namedL8_ne_zero : namedL8 ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  have h2 : namedL8 1 = 1 := by decide +kernel
  rw [h2] at h1
  norm_num at h1

/-! ## 4. Coordinates of a zero relation -/

/-- A zero relation of period dividing 120 is a combination of the eight named patterns. -/
theorem coords_of_zero (hB : BakerTheorem) {g : ℕ} (hg : g ∣ 120) {ρ : ℕ → ℚ}
    (hper : ρ ∈ periodSpace g) (hzero : ρ ∈ zeroAll) : ∃ q : Fin 8 → ℚ, ρ = namedComb q := by
  have hρ : ρ ∈ ratSpace 120 :=
    ⟨periodSpace_mono hg hper, 0, by rw [Rat.cast_zero, zero_mul]; exact hzero⟩
  exact exists_coords hB (N := 120) (by norm_num) dvd_rfl hρ

theorem namedComb_eq_zero {q : Fin 8 → ℚ} (h : namedComb q = 0) : q = 0 := by
  have hLI := named_linearIndependent
  rw [Fintype.linearIndependent_iff] at hLI
  funext i
  refine hLI q ?_ i
  funext k
  have hk := congrFun h k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply]
  exact hk

/-! ## 5. The zero relations at periods 8, 12, 24, 40, 60, 120 -/

theorem zeroSpace_8 (hB : BakerTheorem) : zeroSpace 8 = Submodule.span ℚ {namedL8} := by
  apply le_antisymm
  · rintro ρ ⟨hper, hzero⟩
    obtain ⟨q, rfl⟩ := coords_of_zero hB (by norm_num) hper hzero
    obtain ⟨h0, h1, h2, h3, h5, h6, h7⟩ := coords_p8 q (coords_zero hzero) hper
    rw [Submodule.mem_span_singleton]
    refine ⟨q 4, ?_⟩
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, namedComb, h0, h1, h2, h3, h5, h6, h7]
    ring
  · rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨namedL8_period, hasSum_namedL8⟩

/-- With the coordinates of `coords_p12`, the pattern is a multiple of `zL`. -/
theorem mem_span_zL {q : Fin 8 → ℚ}
    (h : q 0 = 0 ∧ q 1 = 0 ∧ q 2 = 0 ∧ q 3 = 0 ∧ q 5 = 0 ∧ q 7 = 0 ∧ q 4 + q 6 = 0) :
    namedComb q ∈ Submodule.span ℚ {zL} := by
  obtain ⟨h0, h1, h2, h3, h5, h7, h46⟩ := h
  rw [Submodule.mem_span_singleton]
  refine ⟨q 6, ?_⟩
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, namedComb, zL, h0, h1, h2, h3, h5, h7]
  linear_combination (-namedL8 k) * h46

theorem zeroSpace_12 (hB : BakerTheorem) : zeroSpace 12 = Submodule.span ℚ {zL} := by
  apply le_antisymm
  · rintro ρ ⟨hper, hzero⟩
    obtain ⟨q, rfl⟩ := coords_of_zero hB (by norm_num) hper hzero
    exact mem_span_zL (coords_p12 q (coords_zero hzero) hper)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨zL_period, zL_zero⟩

theorem zeroSpace_60 (hB : BakerTheorem) : zeroSpace 60 = Submodule.span ℚ {zL} := by
  apply le_antisymm
  · rintro ρ ⟨hper, hzero⟩
    obtain ⟨q, rfl⟩ := coords_of_zero hB (by norm_num) hper hzero
    exact mem_span_zL (coords_p60 q (coords_zero hzero) hper)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨periodSpace_mono (by norm_num : 12 ∣ 60) zL_period, zL_zero⟩

/-- The five zero relations of period 24. -/
def fam24 : Fin 5 → ℕ → ℚ := ![namedA6, namedL6, namedL8, namedL24, namedTW]

theorem zeroSpace_24 (hB : BakerTheorem) :
    zeroSpace 24 = Submodule.span ℚ (Set.range fam24) := by
  apply le_antisymm
  · rintro ρ ⟨hper, hzero⟩
    obtain ⟨q, rfl⟩ := coords_of_zero hB (by norm_num) hper hzero
    obtain ⟨h0, h2, h5⟩ := coords_p24 q (coords_zero hzero) hper
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![q 1, q 3, q 4, q 6, q 7], ?_⟩
    funext k
    simp only [fam24, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_five,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, namedComb, h0, h2, h5]
    ring
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h8 : (8 : ℕ) ∣ 24 := by norm_num
    fin_cases i
    · exact ⟨namedA6_period, hasSum_namedA6⟩
    · exact ⟨namedL6_period, hasSum_namedL6⟩
    · exact ⟨periodSpace_mono h8 namedL8_period, hasSum_namedL8⟩
    · exact ⟨namedL24_period, hasSum_namedL24⟩
    · exact ⟨namedTW_period, hasSum_namedTW⟩

/-- The three zero relations of period 40. -/
def fam40 : Fin 3 → ℕ → ℚ := ![zA, namedL8, namedL10]

theorem zeroSpace_40 (hB : BakerTheorem) :
    zeroSpace 40 = Submodule.span ℚ (Set.range fam40) := by
  apply le_antisymm
  · rintro ρ ⟨hper, hzero⟩
    obtain ⟨q, rfl⟩ := coords_of_zero hB (by norm_num) hper hzero
    have hv := coords_zero hzero
    obtain ⟨h1, h3, h6, h7⟩ := coords_p40 q hv hper
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![q 2, q 4, q 5], ?_⟩
    funext k
    simp only [fam40, zA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, namedComb, h1, h3, h6, h7]
    linear_combination (-namedA1 k) * hv
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h8 : (8 : ℕ) ∣ 40 := by norm_num
    fin_cases i
    · exact ⟨zA_period, zA_zero⟩
    · exact ⟨periodSpace_mono h8 namedL8_period, hasSum_namedL8⟩
    · exact ⟨namedL10_period, hasSum_namedL10⟩

/-- The seven zero relations of period 120. -/
def fam120 : Fin 7 → ℕ → ℚ :=
  ![namedA6, zA, namedL6, namedL8, namedL10, namedL24, namedTW]

theorem zeroSpace_120 (hB : BakerTheorem) :
    zeroSpace 120 = Submodule.span ℚ (Set.range fam120) := by
  apply le_antisymm
  · rintro ρ ⟨hper, hzero⟩
    obtain ⟨q, rfl⟩ := coords_of_zero hB dvd_rfl hper hzero
    have hv := coords_zero hzero
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![q 1, q 2, q 3, q 4, q 5, q 6, q 7], ?_⟩
    funext k
    simp only [fam120, zA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_seven,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, namedComb]
    linear_combination (-namedA1 k) * hv
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨fun k => (named_periodic k).2.1, hasSum_namedA6⟩
    · exact ⟨zA_periodic, zA_zero⟩
    · exact ⟨fun k => (named_periodic k).2.2.2.1, hasSum_namedL6⟩
    · exact ⟨fun k => (named_periodic k).2.2.2.2.1, hasSum_namedL8⟩
    · exact ⟨fun k => (named_periodic k).2.2.2.2.2.1, hasSum_namedL10⟩
    · exact ⟨fun k => (named_periodic k).2.2.2.2.2.2.1, hasSum_namedL24⟩
    · exact ⟨fun k => (named_periodic k).2.2.2.2.2.2.2, hasSum_namedTW⟩

/-! ## 6. Linear independence of the bases -/

theorem fam24_li : LinearIndependent ℚ fam24 := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hq : namedComb ![0, c 0, 0, c 1, c 2, 0, c 3, c 4] = 0 := by
    funext k
    have hk := congrFun hc k
    simp only [fam24, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_five,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at hk
    simp only [namedComb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Pi.zero_apply]
    linear_combination hk
  have h0 := namedComb_eq_zero hq
  have e0 : c 0 = 0 := by simpa using congrFun h0 1
  have e1 : c 1 = 0 := by simpa using congrFun h0 3
  have e2 : c 2 = 0 := by simpa using congrFun h0 4
  have e3 : c 3 = 0 := by simpa using congrFun h0 6
  have e4 : c 4 = 0 := by simpa using congrFun h0 7
  intro i
  fin_cases i
  exacts [e0, e1, e2, e3, e4]

theorem fam40_li : LinearIndependent ℚ fam40 := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hq : namedComb ![-c 0, 0, c 0, 0, c 1, c 2, 0, 0] = 0 := by
    funext k
    have hk := congrFun hc k
    simp only [fam40, zA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at hk
    simp only [namedComb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Pi.zero_apply]
    linear_combination hk
  have h0 := namedComb_eq_zero hq
  have e0 : c 0 = 0 := by simpa using congrFun h0 2
  have e1 : c 1 = 0 := by simpa using congrFun h0 4
  have e2 : c 2 = 0 := by simpa using congrFun h0 5
  intro i
  fin_cases i
  exacts [e0, e1, e2]

theorem fam120_li : LinearIndependent ℚ fam120 := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hq : namedComb ![-c 1, c 0, c 1, c 2, c 3, c 4, c 5, c 6] = 0 := by
    funext k
    have hk := congrFun hc k
    simp only [fam120, zA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_seven,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at hk
    simp only [namedComb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Pi.zero_apply]
    linear_combination hk
  have h0 := namedComb_eq_zero hq
  have e0 : c 0 = 0 := by simpa using congrFun h0 1
  have e1 : c 1 = 0 := by simpa using congrFun h0 2
  have e2 : c 2 = 0 := by simpa using congrFun h0 3
  have e3 : c 3 = 0 := by simpa using congrFun h0 4
  have e4 : c 4 = 0 := by simpa using congrFun h0 5
  have e5 : c 5 = 0 := by simpa using congrFun h0 6
  have e6 : c 6 = 0 := by simpa using congrFun h0 7
  intro i
  fin_cases i
  exacts [e0, e1, e2, e3, e4, e5, e6]

/-! ## 7. Only `gcd(n, 120)` matters -/

/-- **Only `gcd(n, 120)` matters (from Baker's theorem).** A zero relation of period `n` has
period `gcd(n, 120)`. -/
theorem zeroSpace_gcd (hB : BakerTheorem) {n : ℕ} (hn : 0 < n) :
    zeroSpace n = zeroSpace (Nat.gcd n 120) := by
  apply le_antisymm
  · rintro ρ ⟨hper, hzero⟩
    have hN : 0 < n * 120 := by positivity
    have h8 : 8 ∣ n * 120 := Dvd.dvd.mul_left (by norm_num) n
    have hρ : ρ ∈ ratSpace (n * 120) :=
      ⟨fun k => periodic_mul hper 120 k, 0, by rw [Rat.cast_zero, zero_mul]; exact hzero⟩
    have h120 := period_120 hB hN h8 (ratSpace_le_algSpace _ hρ)
    exact ⟨periodic_gcd (by norm_num) hper h120, hzero⟩
  · exact inf_le_inf_right _ (periodSpace_mono (Nat.gcd_dvd_left n 120))

theorem zeroSpaceEven_gcd (hB : BakerTheorem) {n : ℕ} (hn : 0 < n) :
    zeroSpaceEven n = zeroSpaceEven (Nat.gcd n 120) := by
  rw [zeroSpaceEven, zeroSpaceEven, zeroSpace_gcd hB hn]

/-! ## 8. No zero relation at the other divisors of 120 -/

/-- At a period `g ∣ 60` with `gcd(g, 12)` dividing 4 or 6 there is no zero relation:
the only candidate `zL` has period 12 but neither 4 nor 6. -/
theorem zeroSpace_eq_bot (hB : BakerTheorem) {g : ℕ} (h60 : g ∣ 60)
    (hbad : Nat.gcd g 12 ∣ 4 ∨ Nat.gcd g 12 ∣ 6) : zeroSpace g = ⊥ := by
  rw [eq_bot_iff]
  rintro ρ ⟨hper, hzero⟩
  have h1 : ρ ∈ zeroSpace 60 := ⟨periodSpace_mono h60 hper, hzero⟩
  rw [zeroSpace_60 hB, Submodule.mem_span_singleton] at h1
  obtain ⟨c, rfl⟩ := h1
  by_cases hc : c = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · exfalso
    have hzg : ∀ k, zL (k + g) = zL k := by
      intro k
      have h2 := hper k
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      exact mul_left_cancel₀ hc h2
    have hd := periodic_gcd (by norm_num) hzg zL_period
    obtain ⟨v2, v6, v8⟩ := zL_values
    rcases hbad with h4 | h6
    · have h := periodSpace_mono h4 hd 2
      have h' : zL 6 = zL 2 := h
      rw [v2, v6] at h'
      norm_num at h'
    · have h := periodSpace_mono h6 hd 2
      have h' : zL 8 = zL 2 := h
      rw [v2, v8] at h'
      norm_num at h'

/-! ## 9. The table -/

/-- The number of independent zero relations of period `g`, for `g` a divisor of 120. -/
def zeroCount (g : ℕ) : ℕ :=
  if g = 8 then 1 else if g = 12 then 1 else if g = 24 then 5 else if g = 40 then 3 else
  if g = 60 then 1 else if g = 120 then 7 else 0

theorem finrank_zeroSpace_8 (hB : BakerTheorem) : Module.finrank ℚ (zeroSpace 8) = 1 := by
  rw [zeroSpace_8 hB]
  exact finrank_span_singleton namedL8_ne_zero

theorem finrank_zeroSpace_12 (hB : BakerTheorem) : Module.finrank ℚ (zeroSpace 12) = 1 := by
  rw [zeroSpace_12 hB]
  exact finrank_span_singleton zL_ne_zero

theorem finrank_zeroSpace_60 (hB : BakerTheorem) : Module.finrank ℚ (zeroSpace 60) = 1 := by
  rw [zeroSpace_60 hB]
  exact finrank_span_singleton zL_ne_zero

theorem finrank_zeroSpace_24 (hB : BakerTheorem) : Module.finrank ℚ (zeroSpace 24) = 5 := by
  rw [zeroSpace_24 hB, finrank_span_eq_card fam24_li]
  rfl

theorem finrank_zeroSpace_40 (hB : BakerTheorem) : Module.finrank ℚ (zeroSpace 40) = 3 := by
  rw [zeroSpace_40 hB, finrank_span_eq_card fam40_li]
  rfl

theorem finrank_zeroSpace_120 (hB : BakerTheorem) :
    Module.finrank ℚ (zeroSpace 120) = 7 := by
  rw [zeroSpace_120 hB, finrank_span_eq_card fam120_li]
  rfl

theorem finrank_zeroSpace_bot (hB : BakerTheorem) {g : ℕ} (h60 : g ∣ 60)
    (hbad : Nat.gcd g 12 ∣ 4 ∨ Nat.gcd g 12 ∣ 6) : Module.finrank ℚ (zeroSpace g) = 0 := by
  rw [zeroSpace_eq_bot hB h60 hbad]
  exact finrank_bot ℚ (ℕ → ℚ)

/-- **The number of zero relations at every period (from Baker's theorem).** For every
`n ≥ 1`, the rational patterns of period `n` whose series is 0 form a space of dimension
`zeroCount (gcd n 120)`: `1, 1, 5, 3, 1, 7` when the gcd is `8, 12, 24, 40, 60, 120`, and `0`
otherwise. -/
theorem finrank_zeroSpace (hB : BakerTheorem) {n : ℕ} (hn : 0 < n) :
    Module.finrank ℚ (zeroSpace n) = zeroCount (Nat.gcd n 120) := by
  rw [zeroSpace_gcd hB hn]
  have hdiv : Nat.gcd n 120 ∈ Nat.divisors 120 :=
    Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right n 120, by norm_num⟩
  generalize Nat.gcd n 120 = g at hdiv
  have hlist : Nat.divisors 120 =
      {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120} := by decide +kernel
  rw [hlist] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  rcases hdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl
  · exact finrank_zeroSpace_bot hB (by norm_num) (Or.inl (by decide))
  · exact finrank_zeroSpace_bot hB (by norm_num) (Or.inl (by decide))
  · exact finrank_zeroSpace_bot hB (by norm_num) (Or.inr (by decide))
  · exact finrank_zeroSpace_bot hB (by norm_num) (Or.inl (by decide))
  · exact finrank_zeroSpace_bot hB (by norm_num) (Or.inl (by decide))
  · exact finrank_zeroSpace_bot hB (by norm_num) (Or.inr (by decide))
  · exact finrank_zeroSpace_8 hB
  · exact finrank_zeroSpace_bot hB (by norm_num) (Or.inl (by decide))
  · exact finrank_zeroSpace_12 hB
  · exact finrank_zeroSpace_bot hB (by norm_num) (Or.inr (by decide))
  · exact finrank_zeroSpace_bot hB (by norm_num) (Or.inl (by decide))
  · exact finrank_zeroSpace_24 hB
  · exact finrank_zeroSpace_bot hB (by norm_num) (Or.inr (by decide))
  · exact finrank_zeroSpace_40 hB
  · exact finrank_zeroSpace_60 hB
  · exact finrank_zeroSpace_120 hB

/-! ## 10. Zero relations supported on even `k` -/

theorem zeroSpaceEven_eq (hB : BakerTheorem) {g : ℕ} (hg : g ∣ 120) (h12 : 12 ∣ g) :
    zeroSpaceEven g = Submodule.span ℚ {zL} := by
  apply le_antisymm
  · rintro ρ ⟨⟨hper, hzero⟩, hev⟩
    obtain ⟨q, rfl⟩ := coords_of_zero hB hg hper hzero
    exact mem_span_zL (coords_even q (coords_zero hzero) hev)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨⟨periodSpace_mono h12 zL_period, zL_zero⟩, zL_even⟩

/-- **Zero relations supported on even `k` (from Baker's theorem).** If `12 ∣ gcd(n, 120)`
there is exactly one, up to scaling: `namedL24 - namedL8`. -/
theorem finrank_zeroSpaceEven (hB : BakerTheorem) {n : ℕ} (hn : 0 < n)
    (h12 : 12 ∣ Nat.gcd n 120) : Module.finrank ℚ (zeroSpaceEven n) = 1 := by
  rw [zeroSpaceEven_gcd hB hn, zeroSpaceEven_eq hB (Nat.gcd_dvd_right n 120) h12]
  exact finrank_span_singleton zL_ne_zero

/-! ## 11. Bailey's 27 rows -/

/-- **Bailey's table, the 17 rows with `n = 2B`** (from Baker's theorem). Each pair is
`(n, count)`: the zero relations of period `n` form a space of that dimension. -/
theorem bailey_F2 (hB : BakerTheorem) :
    ∀ p ∈ ([(8, 1), (16, 1), (24, 5), (32, 1), (40, 3), (48, 5), (56, 1), (60, 1), (64, 1),
      (72, 5), (80, 3), (84, 1), (88, 1), (96, 5), (104, 1), (112, 1), (120, 7)] :
        List (ℕ × ℕ)),
      Module.finrank ℚ (zeroSpace p.1) = p.2 := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl <;>
  exact (finrank_zeroSpace hB (by norm_num)).trans (by decide)

/-- **Bailey's table, the 10 rows with `n = B`** (from Baker's theorem). For each listed `n`
the zero relations of period `2n` supported on even `k` form a space of dimension 1. -/
theorem bailey_F1 (hB : BakerTheorem) :
    ∀ n ∈ ([6, 12, 18, 24, 30, 36, 42, 48, 54, 60] : List ℕ),
      Module.finrank ℚ (zeroSpaceEven (2 * n)) = 1 := by
  intro n hn
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  exact finrank_zeroSpaceEven hB (by norm_num) (by decide)

end PiFormula
