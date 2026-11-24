/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.OkadaWindow
public import Pilean.Erdos.OkadaGlueWindow
public import Pilean.Erdos.Plain

/-!
# Erdős's conjecture for even `q`: the series diverges

**Theorem** (`erdos_even_nat`). Let `q ≥ 2` be even and let `f : ℕ → ℤ` have period `q`, with
`f(n) = 0` when `q ∣ n` and `f(n) = ±1` otherwise. Then the partial sums
`∑_{1 ≤ n < N} f(n)/n` have no limit; in particular they do not tend to `0`
(`erdos_even_nat_zero`).

This case is elementary and well known: the series `∑ f(n)/n` of a periodic `f` converges
only if the sum of `f` over a period is `0`, and for even `q` that sum is a sum of `q - 1` odd
numbers, hence odd.

The steps, all for every `q ≥ 1` (the statements `OkadaWindow` and `OkadaSumZero` of
`OkadaDefs.lean` carry the hypothesis `Odd q`, which their proofs do not use; they are proved
again here without it):

* `tendsto_windowSum`: `∑_{N ≤ n < cN, n ≡ r mod q} 1/n → (log c)/q`;
* `sum_period_eq_zero_of_tendsto`: if the partial sums of `∑ f(n)/n` have a limit, then
  `∑_r f(r) = 0`;
* `sum_pm_one_ne_zero`: for even `q`, `f(0) = 0` and `f(r) = ±1` otherwise, `∑_r f(r) ≠ 0`.

The file also contains the passage from a periodic `f : ℕ → ℤ` to a function on `ℤ/q`
(`zmodLift`), used again in `Summary.lean`.
-/

@[expose] public section

open scoped BigOperators

open Filter Finset

namespace PiFormula

namespace Erdos

/-! ## 1. The window sums, for every `q ≥ 1` -/

/-- **The window sums**, for every modulus `q ≥ 1`:
`∑_{N ≤ n < cN, n ≡ r mod q} 1/n → (log c)/q`. -/
theorem tendsto_windowSum (q : ℕ) [NeZero q] {c : ℕ} (hc : 0 < c) (r : ZMod q) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Ico N (c * N), if (n : ZMod q) = r then 1 / (n : ℝ) else 0)
      atTop (nhds (Real.log (c : ℝ) / (q : ℝ))) := by
  obtain ⟨l, hl⟩ := Okada.exists_limit_classSum q r
  have hcN : Tendsto (fun N : ℕ => c * N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hc) tendsto_id
  have hD : Tendsto (fun N : ℕ => ∑ i ∈ range (c * N), Okada.classTerm q r i -
      ∑ i ∈ range N, Okada.classTerm q r i) atTop (nhds (l - l)) := (hl.comp hcN).sub hl
  rw [sub_self] at hD
  have hsplit : ∀ N : ℕ, 1 ≤ N →
      (∑ i ∈ range (c * N), Okada.classTerm q r i - ∑ i ∈ range N, Okada.classTerm q r i) +
        1 / (q : ℝ) * ∑ n ∈ Ico N (c * N), 1 / (n : ℝ) =
      ∑ n ∈ Ico N (c * N), if (n : ZMod q) = r then 1 / (n : ℝ) else 0 := by
    intro N hN
    rw [← Finset.sum_Ico_eq_sub _ (Nat.le_mul_of_pos_left N hc), Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hN (mem_Ico.1 hn).1
    unfold Okada.classTerm
    rw [max_eq_left hn1]
    split_ifs
    · ring
    · ring
  have hsum := hD.add ((Okada.tendsto_sum_Ico_inv hc).const_mul (1 / (q : ℝ)))
  have hval : (0 : ℝ) + 1 / (q : ℝ) * Real.log (c : ℝ) = Real.log (c : ℝ) / (q : ℝ) := by ring
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN using hsplit N hN

/-- The sum of `v(n)/n` over `N ≤ n < cN` tends to `(log c / q) ∑_r v(r)`, for every `q ≥ 1`
and every real function `v` on `ℤ/q`. -/
theorem tendsto_windowSum_mul (q : ℕ) [NeZero q] {c : ℕ} (hc : 0 < c) (v : ZMod q → ℝ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Ico N (c * N), v (n : ZMod q) / (n : ℝ)) atTop
      (nhds ((∑ r : ZMod q, v r) * Real.log (c : ℝ) / (q : ℝ))) := by
  have h : ∀ N : ℕ, ∑ r : ZMod q, v r *
      (∑ n ∈ Ico N (c * N), if (n : ZMod q) = r then 1 / (n : ℝ) else 0) =
      ∑ n ∈ Ico N (c * N), v (n : ZMod q) / (n : ℝ) :=
    fun N => (Okada.sum_Ico_eq_sum_window q v N (c * N)).symm
  rw [mul_div_assoc, Finset.sum_mul]
  refine Tendsto.congr h ?_
  exact tendsto_finsetSum _ fun r _ => (tendsto_windowSum q hc r).const_mul _

/-! ## 2. Convergence forces the sum over a period to be `0` -/

/-- For every `q ≥ 1` and every rational `f` on `ℤ/q`: if the partial sums of `∑ f(n)/n` have
a limit, then `∑_r f(r) = 0`. -/
theorem sum_period_eq_zero_of_tendsto (q : ℕ) [NeZero q] (f : ZMod q → ℚ) {l : ℝ}
    (hS : Tendsto (partialSum q f) atTop (nhds l)) : ∑ r : ZMod q, f r = 0 := by
  have h2 : Tendsto (fun N : ℕ => partialSum q f (2 * N) - partialSum q f N) atTop
      (nhds (l - l)) := (hS.comp Okada.tendsto_two_mul_atTop).sub hS
  rw [sub_self] at h2
  have h4 : ∀ N : ℕ, ∑ n ∈ Ico N (2 * N), (f (n : ZMod q) : ℝ) / (n : ℝ) =
      partialSum q f (2 * N) - partialSum q f N := by
    intro N
    unfold partialSum
    rw [← Finset.sum_Ico_eq_sub _ (show N ≤ 2 * N by omega)]
  have h3 := (tendsto_windowSum_mul q (show 0 < 2 by norm_num)
    (fun r => (f r : ℝ))).congr h4
  have h5 := tendsto_nhds_unique h3 h2
  rw [mul_div_assoc] at h5
  have h6 : ∑ r : ZMod q, (f r : ℝ) = 0 :=
    (mul_eq_zero.1 h5).resolve_right (Okada.log_two_div_pos q).ne'
  exact_mod_cast h6

/-! ## 3. Even `q`: the sum over a period is odd -/

/-- For even `q`, a function on `ℤ/q` with `f(0) = 0` and `f(r) = ±1` otherwise has a non-zero
sum: it is a sum of `q - 1` odd numbers. -/
theorem sum_pm_one_ne_zero {q : ℕ} [NeZero q] (hq : Even q) (f : ZMod q → ℚ) (h0 : f 0 = 0)
    (hpm : ∀ r : ZMod q, r ≠ 0 → f r = 1 ∨ f r = -1) : ∑ r : ZMod q, f r ≠ 0 := by
  classical
  intro hsum
  have h1 : ∑ r : ZMod q, f r = ∑ r ∈ Finset.univ.erase (0 : ZMod q), f r := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q)), h0, zero_add]
  have h2 : ∀ r ∈ Finset.univ.erase (0 : ZMod q),
      f r = 1 - 2 * (if f r = -1 then 1 else 0) := by
    intro r hr
    rcases hpm r (Finset.ne_of_mem_erase hr) with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ZMod.card, nsmul_eq_mul, mul_one, sub_eq_zero] at hsum
  have h3 : q - 1 = 2 * ((Finset.univ.erase (0 : ZMod q)).filter fun r => f r = -1).card := by
    exact_mod_cast hsum
  have hq0 : q ≠ 0 := NeZero.ne q
  obtain ⟨k, hk⟩ := hq
  omega

/-- **Even `q`, functions on `ℤ/q`.** For even `q ≥ 2`, `f(0) = 0` and `f(r) = ±1` otherwise,
the partial sums of `∑ f(n)/n` have no limit. -/
theorem erdos_even_diverges {q : ℕ} [NeZero q] (hq : Even q) (f : ZMod q → ℚ) (h0 : f 0 = 0)
    (hpm : ∀ r : ZMod q, r ≠ 0 → f r = 1 ∨ f r = -1) :
    ¬ ∃ l : ℝ, Tendsto (partialSum q f) atTop (nhds l) := by
  rintro ⟨l, hl⟩
  exact sum_pm_one_ne_zero hq f h0 hpm (sum_period_eq_zero_of_tendsto q f hl)

/-- **Erdős's conjecture for even `q`** (functions on `ℤ/q`): the sum is not `0`. -/
theorem erdos_even {q : ℕ} [NeZero q] (hq : Even q) (f : ZMod q → ℚ) (h0 : f 0 = 0)
    (hpm : ∀ r : ZMod q, r ≠ 0 → f r = 1 ∨ f r = -1) : ¬ SumIsZero q f := fun h =>
  erdos_even_diverges hq f h0 hpm ⟨0, h⟩

/-! ## 4. From a periodic function on `ℕ` to a function on `ℤ/q` -/

/-- The function on `ℤ/q` attached to `f : ℕ → ℤ`: `r ↦ f(r.val)`. -/
def zmodLift (q : ℕ) (f : ℕ → ℤ) : ZMod q → ℚ := fun r => (f r.val : ℚ)

theorem zmodLift_natCast {q : ℕ} [NeZero q] (f : ℕ → ℤ) (hper : ∀ n, f (n + q) = f n)
    (n : ℕ) : zmodLift q f (n : ZMod q) = (f n : ℚ) := by
  simp only [zmodLift, ZMod.val_natCast]
  rw [periodic_mod_eq f hper n]

theorem zmodLift_zero {q : ℕ} [NeZero q] (f : ℕ → ℤ) (h0 : ∀ n, q ∣ n → f n = 0) :
    zmodLift q f 0 = 0 := by
  simp only [zmodLift, ZMod.val_zero]
  rw [h0 0 (dvd_zero q)]
  simp

theorem zmodLift_pm {q : ℕ} [NeZero q] (f : ℕ → ℤ)
    (hpm : ∀ n, ¬ q ∣ n → f n = 1 ∨ f n = -1) (r : ZMod q) (hr : r ≠ 0) :
    zmodLift q f r = 1 ∨ zmodLift q f r = -1 := by
  have hnd : ¬ q ∣ r.val := by
    intro hd
    apply hr
    have h := (ZMod.natCast_eq_zero_iff r.val q).2 hd
    rwa [ZMod.natCast_zmod_val] at h
  rcases hpm r.val hnd with h | h
  · left
    simp [zmodLift, h]
  · right
    simp [zmodLift, h]

/-- The partial sums of `∑ f(n)/n` are those of the function on `ℤ/q`. -/
theorem partialSum_zmodLift {q : ℕ} [NeZero q] (f : ℕ → ℤ) (hper : ∀ n, f (n + q) = f n) :
    partialSum q (zmodLift q f) = fun N : ℕ => ∑ n ∈ Finset.range N, (f n : ℝ) / (n : ℝ) := by
  funext N
  unfold partialSum
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [zmodLift_natCast f hper n]
  simp

/-! ## 5. The statement in plain terms -/

/-- **Erdős's conjecture for even `q`, in plain terms; the series diverges.** If `f : ℕ → ℤ`
has even period `q ≥ 2`, `f(n) = 0` when `q ∣ n` and `f(n) = ±1` otherwise, then the partial
sums `∑_{1 ≤ n < N} f(n)/n` have no limit. -/
theorem erdos_even_nat {q : ℕ} (hq0 : q ≠ 0) (hq : Even q) (f : ℕ → ℤ)
    (hper : ∀ n, f (n + q) = f n) (h0 : ∀ n, q ∣ n → f n = 0)
    (hpm : ∀ n, ¬ q ∣ n → f n = 1 ∨ f n = -1) :
    ¬ ∃ l : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (f n : ℝ) / (n : ℝ))
      atTop (nhds l) := by
  have : NeZero q := ⟨hq0⟩
  have key := erdos_even_diverges hq (zmodLift q f) (zmodLift_zero f h0) (zmodLift_pm f hpm)
  rw [partialSum_zmodLift f hper] at key
  exact key

/-- **Erdős's conjecture for even `q`, in plain terms**: the partial sums do not tend to
`0`. -/
theorem erdos_even_nat_zero {q : ℕ} (hq0 : q ≠ 0) (hq : Even q) (f : ℕ → ℤ)
    (hper : ∀ n, f (n + q) = f n) (h0 : ∀ n, q ∣ n → f n = 0)
    (hpm : ∀ n, ¬ q ∣ n → f n = 1 ∨ f n = -1) :
    ¬ Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (f n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
  fun h => erdos_even_nat hq0 hq f hper h0 hpm ⟨0, h⟩

end Erdos

end PiFormula
