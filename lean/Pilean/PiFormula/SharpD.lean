/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula.Bailey

/-!
# The sharp form of Theorem D, and its sharpness (milestone M8, addition)

Theorem D says: a series of the class F with a rational value (in units of `π`) and no term
at `gcd(k, 120) < 4` has value 0. Two sharper statements:

* **Sharp form** (`theoremD_sharp`, `fast_eq`, `finrank_fast`; from Baker's theorem). Such a
  series is a multiple of one series, `zD = -2·namedL8 + 2·namedL10 + namedL24`. So the
  "uniformly fast" series with a rational value form a line, and that line is a zero
  relation. `zD` has no term at `gcd(k, 120) < 5` either (`zD_supp`), and it has one at
  `k = 5` (`zD_at_5`).
* **Best possible** (`theoremD_best_possible`; no Baker). For each two of the three classes
  `gcd(k, 120) = 1, 2, 3` there is a formula for a non-zero multiple of `π` with no term in
  those two classes: `namedA10 - 2·namedA6`, `2·namedA1 - namedA10` and
  `6·namedA1 + 4·namedA6 + namedA10`. Only all three classes together cannot be avoided.

The certificate `coords_Dall` (generated, in `TheoremD.lean`) uses the seven positions
`k = 1, 2, 3, 7, 9, 11, 14` only.
-/

@[expose] public section

open Complex

namespace PiFormula

/-! ## 1. Helpers -/

theorem gcd_mod_120 (k : ℕ) : Nat.gcd (k % 120) 120 = Nat.gcd k 120 :=
  (Nat.gcd_rec 120 k).symm.trans (Nat.gcd_comm 120 k)

/-- The series of an explicit combination of the eight named patterns. -/
theorem hasSum_of_coords {f : ℕ → ℚ} (q : Fin 8 → ℚ) (hf : ∀ k, f k = namedComb q k) {c : ℚ}
    (hc : q 0 + q 2 = c) : HasSum (seriesTerm f) ((c : ℝ) * (Real.pi / 4)) := by
  have e : f = namedComb q := funext hf
  rw [e, ← hc]
  exact hasSum_namedComb q

/-- A statement about residues modulo 120 lifts to every `k`. -/
theorem zero_of_table {f : ℕ → ℚ} (hper : ∀ k, f (k + 120) = f k) {P : ℕ → Prop}
    (htab : ∀ r < 120, P (Nat.gcd r 120) → f r = 0) (k : ℕ) (hk : P (Nat.gcd k 120)) :
    f k = 0 := by
  rw [← mod_120 hper k]
  refine htab (k % 120) (Nat.mod_lt k (by norm_num)) ?_
  rw [gcd_mod_120]
  exact hk

/-! ## 2. The one uniformly fast series -/

/-- `-2·namedL8 + 2·namedL10 + namedL24`: the zero relation with no term at
`gcd(k, 120) < 5`. -/
def zD : ℕ → ℚ := fun k => -2 * namedL8 k + 2 * namedL10 k + namedL24 k

theorem zD_periodic (k : ℕ) : zD (k + 120) = zD k := by
  simp only [zD, (named_periodic k).2.2.2.2.1, (named_periodic k).2.2.2.2.2.1,
    (named_periodic k).2.2.2.2.2.2.1]

/-- `zD` has no term at `gcd(k, 120) < 5`. -/
theorem zD_supp (k : ℕ) (hk : Nat.gcd k 120 < 5) : zD k = 0 := by
  have htab : ∀ r < 120, Nat.gcd r 120 < 5 → zD r = 0 := by decide +kernel
  exact zero_of_table (P := fun g => g < 5) zD_periodic htab k hk

/-- `zD` has a term at `k = 5`. -/
theorem zD_at_5 : zD 5 = -5 := by decide +kernel

theorem zD_ne_zero : zD ≠ 0 := by
  intro h
  have h5 := congrFun h 5
  rw [zD_at_5] at h5
  norm_num at h5

theorem zD_hasSum : HasSum (seriesTerm zD) 0 := by
  have h := hasSum_of_coords (f := zD) ![0, 0, 0, 0, -2, 2, 1, 0]
    (fun k => by
      simp only [zD, namedComb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring) (c := 0) (by simp)
  rw [Rat.cast_zero, zero_mul] at h
  exact h

theorem zD_mem_ratSpace {N : ℕ} (h120 : 120 ∣ N) : zD ∈ ratSpace N :=
  ⟨periodic_of_dvd zD_periodic h120, 0, by rw [Rat.cast_zero, zero_mul]; exact zD_hasSum⟩

/-- **Theorem D, sharp form (from Baker's theorem).** A rational pattern whose series is a
rational multiple of `π` and which has no term at `gcd(k, 120) < 4` is a multiple of `zD`. -/
theorem theoremD_sharp (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ρ ∈ ratSpace N) (hsupp : ∀ k, Nat.gcd k 120 < 4 → ρ k = 0) :
    ∃ c : ℚ, ρ = c • zD := by
  obtain ⟨q, rfl⟩ := exists_coords hB hN h120 hρ
  obtain ⟨h0, h1, h2, h3, h7, h45, h46⟩ := coords_Dall q hsupp
  refine ⟨q 6, ?_⟩
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, namedComb, zD, h0, h1, h2, h3, h7]
  linear_combination (namedL8 k - namedL10 k) * h46 + namedL10 k * h45

/-- The patterns with no term at `gcd(k, 120) < 4`. -/
def fastSupp : Submodule ℚ (ℕ → ℚ) where
  carrier := {ρ | ∀ k, Nat.gcd k 120 < 4 → ρ k = 0}
  add_mem' := fun {ρ ρ'} h h' k hk => by simp only [Pi.add_apply, h k hk, h' k hk, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c ρ h k hk => by simp only [Pi.smul_apply, h k hk, smul_zero]

/-- **The uniformly fast series form a line (from Baker's theorem).** -/
theorem fast_eq (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) :
    ratSpace N ⊓ fastSupp = Submodule.span ℚ {zD} := by
  apply le_antisymm
  · rintro ρ ⟨hρ, hs⟩
    obtain ⟨c, rfl⟩ := theoremD_sharp hB hN h120 hρ hs
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self zD)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨zD_mem_ratSpace h120, fun k hk => zD_supp k (by omega)⟩

theorem finrank_fast (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) :
    Module.finrank ℚ (ratSpace N ⊓ fastSupp : Submodule ℚ (ℕ → ℚ)) = 1 := by
  rw [fast_eq hB hN h120]
  exact finrank_span_singleton zD_ne_zero

/-! ## 3. Theorem D is best possible -/

/-- `namedA10 - 2·namedA6`: a formula for `π/4` with no term at `gcd(k, 120) = 1, 2`. -/
def sAvoid12 : ℕ → ℚ := fun k => namedA10 k - 2 * namedA6 k

/-- `2·namedA1 - namedA10`: a formula for `π/4` with no term at `gcd(k, 120) = 1, 3`. -/
def sAvoid13 : ℕ → ℚ := fun k => 2 * namedA1 k - namedA10 k

/-- `6·namedA1 + 4·namedA6 + namedA10`: a formula for `7π/4` with no term at
`gcd(k, 120) = 2, 3`. -/
def sAvoid23 : ℕ → ℚ := fun k => 6 * namedA1 k + 4 * namedA6 k + namedA10 k

theorem sAvoid12_periodic (k : ℕ) : sAvoid12 (k + 120) = sAvoid12 k := by
  simp only [sAvoid12, (named_periodic k).2.1, (named_periodic k).2.2.1]

theorem sAvoid13_periodic (k : ℕ) : sAvoid13 (k + 120) = sAvoid13 k := by
  simp only [sAvoid13, (named_periodic k).1, (named_periodic k).2.2.1]

theorem sAvoid23_periodic (k : ℕ) : sAvoid23 (k + 120) = sAvoid23 k := by
  simp only [sAvoid23, (named_periodic k).1, (named_periodic k).2.1, (named_periodic k).2.2.1]

theorem sAvoid12_supp (k : ℕ) (hk : Nat.gcd k 120 = 1 ∨ Nat.gcd k 120 = 2) :
    sAvoid12 k = 0 := by
  have htab : ∀ r < 120, Nat.gcd r 120 = 1 ∨ Nat.gcd r 120 = 2 → sAvoid12 r = 0 := by
    decide +kernel
  exact zero_of_table (P := fun g => g = 1 ∨ g = 2) sAvoid12_periodic htab k hk

theorem sAvoid13_supp (k : ℕ) (hk : Nat.gcd k 120 = 1 ∨ Nat.gcd k 120 = 3) :
    sAvoid13 k = 0 := by
  have htab : ∀ r < 120, Nat.gcd r 120 = 1 ∨ Nat.gcd r 120 = 3 → sAvoid13 r = 0 := by
    decide +kernel
  exact zero_of_table (P := fun g => g = 1 ∨ g = 3) sAvoid13_periodic htab k hk

theorem sAvoid23_supp (k : ℕ) (hk : Nat.gcd k 120 = 2 ∨ Nat.gcd k 120 = 3) :
    sAvoid23 k = 0 := by
  have htab : ∀ r < 120, Nat.gcd r 120 = 2 ∨ Nat.gcd r 120 = 3 → sAvoid23 r = 0 := by
    decide +kernel
  exact zero_of_table (P := fun g => g = 2 ∨ g = 3) sAvoid23_periodic htab k hk

theorem sAvoid12_hasSum : HasSum (seriesTerm sAvoid12) (Real.pi / 4) := by
  have h := hasSum_of_coords (f := sAvoid12) ![0, -2, 1, 0, 0, 0, 0, 0]
    (fun k => by
      simp only [sAvoid12, namedComb, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      ring) (c := 1) (by simp)
  rw [Rat.cast_one, one_mul] at h
  exact h

theorem sAvoid13_hasSum : HasSum (seriesTerm sAvoid13) (Real.pi / 4) := by
  have h := hasSum_of_coords (f := sAvoid13) ![2, 0, -1, 0, 0, 0, 0, 0]
    (fun k => by
      simp only [sAvoid13, namedComb, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      ring) (c := 1) (by norm_num)
  rw [Rat.cast_one, one_mul] at h
  exact h

theorem sAvoid23_hasSum : HasSum (seriesTerm sAvoid23) (7 * (Real.pi / 4)) := by
  have h := hasSum_of_coords (f := sAvoid23) ![6, 4, 1, 0, 0, 0, 0, 0]
    (fun k => by
      simp only [sAvoid23, namedComb, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      ring) (c := 7) (by norm_num)
  rw [Rat.cast_ofNat] at h
  exact h

/-- **Theorem D is best possible.** For each two of the three classes
`gcd(k, 120) = 1, 2, 3` there is a rational pattern of period 120 with no term in those two
classes whose series is a non-zero rational multiple of `π`. By Theorem D, no such pattern
avoids all three. -/
theorem theoremD_best_possible :
    (∃ ρ : ℕ → ℚ, (∀ k, ρ (k + 120) = ρ k) ∧
      (∀ k, Nat.gcd k 120 = 1 ∨ Nat.gcd k 120 = 2 → ρ k = 0) ∧
      HasSum (seriesTerm ρ) (Real.pi / 4)) ∧
    (∃ ρ : ℕ → ℚ, (∀ k, ρ (k + 120) = ρ k) ∧
      (∀ k, Nat.gcd k 120 = 1 ∨ Nat.gcd k 120 = 3 → ρ k = 0) ∧
      HasSum (seriesTerm ρ) (Real.pi / 4)) ∧
    (∃ ρ : ℕ → ℚ, (∀ k, ρ (k + 120) = ρ k) ∧
      (∀ k, Nat.gcd k 120 = 2 ∨ Nat.gcd k 120 = 3 → ρ k = 0) ∧
      HasSum (seriesTerm ρ) (7 * (Real.pi / 4))) :=
  ⟨⟨sAvoid12, sAvoid12_periodic, sAvoid12_supp, sAvoid12_hasSum⟩,
    ⟨sAvoid13, sAvoid13_periodic, sAvoid13_supp, sAvoid13_hasSum⟩,
    ⟨sAvoid23, sAvoid23_periodic, sAvoid23_supp, sAvoid23_hasSum⟩⟩

end PiFormula
