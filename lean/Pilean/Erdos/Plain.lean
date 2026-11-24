/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.Main

/-!
# The statement in plain terms

`erdos_pm_one_nat_of`: the case of Erdős's conjecture treated here, stated for a function
`f : ℕ → ℤ` with no reference to `ZMod`: if `f` has period `q` (odd, not a perfect square),
`f(n) = 0` when `q ∣ n` and `f(n) = ±1` otherwise, then the partial sums
`∑_{1 ≤ n < N} f(n)/n` do not tend to `0`. In this file it still takes Okada's criterion as a
hypothesis (`OkadaOnlyIf`); `Final.lean` removes it.
-/

@[expose] public section

namespace PiFormula

namespace Erdos

/-- A function of period `q` depends only on `n % q`. -/
theorem periodic_mod_eq {q : ℕ} (f : ℕ → ℤ) (hper : ∀ n, f (n + q) = f n) (n : ℕ) :
    f (n % q) = f n := by
  have h : ∀ k m : ℕ, f (m + k * q) = f m := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      rw [Nat.succ_mul, ← Nat.add_assoc, hper, ih]
  have h1 := h (n / q) (n % q)
  rw [Nat.mul_comm (n / q) q, Nat.mod_add_div] at h1
  exact h1.symm

/-- **Erdős's conjecture for odd `q` that is not a perfect square, in plain terms, given
Okada's criterion.** -/
theorem erdos_pm_one_nat_of (hO : OkadaOnlyIf) {q : ℕ} (hq : Odd q) (hns : ¬ IsSquare q)
    (f : ℕ → ℤ) (hper : ∀ n, f (n + q) = f n) (h0 : ∀ n, q ∣ n → f n = 0)
    (hpm : ∀ n, ¬ q ∣ n → f n = 1 ∨ f n = -1) :
    ¬ Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (f n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact (by decide : ¬ Odd 0) hq
  have : NeZero q := ⟨hq0⟩
  let F : ZMod q → ℚ := fun r => (f r.val : ℚ)
  have hF : ∀ n : ℕ, F (n : ZMod q) = (f n : ℚ) := by
    intro n
    simp only [F, ZMod.val_natCast]
    rw [periodic_mod_eq f hper n]
  have hF0 : F 0 = 0 := by
    have h := hF 0
    rw [Nat.cast_zero] at h
    rw [h, h0 0 (dvd_zero q)]
    simp
  have hFpm : ∀ r : ZMod q, r ≠ 0 → F r = 1 ∨ F r = -1 := by
    intro r hr
    have hnd : ¬ q ∣ r.val := by
      intro hd
      apply hr
      have h := (ZMod.natCast_eq_zero_iff r.val q).2 hd
      rwa [ZMod.natCast_zmod_val] at h
    rcases hpm r.val hnd with h | h
    · left
      simp [F, h]
    · right
      simp [F, h]
  have key := erdos_pm_one_of_okada hO hq hns F hF0 hFpm
  intro hT
  apply key
  have hfun : partialSum q F =
      fun N : ℕ => ∑ n ∈ Finset.range N, (f n : ℝ) / (n : ℝ) := by
    funext N
    unfold partialSum
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hF n]
    simp
  unfold SumIsZero
  rw [hfun]
  exact hT

end Erdos

end PiFormula
