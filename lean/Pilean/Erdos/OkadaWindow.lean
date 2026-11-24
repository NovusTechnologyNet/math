/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.OkadaDefs
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The window sums of `1/n` in a residue class

`okadaWindow : OkadaWindow`: for an integer `c ≥ 1` and a residue `r` modulo `q`,

  `∑_{N ≤ n < cN, n ≡ r mod q} 1/n → (log c)/q`   as `N → ∞`.

Proof. Put `z(n) = [n ≡ r] - 1/q`. The partial sums of `z` are bounded by `1`
(`abs_classCount_sub_le`, from the exact count `Nat.count_modEq_card`), so by Dirichlet's
test the series `∑ z(n)/n` converges (`exists_limit_classSum`), and its sum over `N ≤ n < cN`
tends to `0`. What is left is `(1/q) ∑_{N ≤ n < cN} 1/n`, and
`log c ≤ ∑_{N ≤ n < cN} 1/n ≤ log c + 1/(N-1)` (`log_le_sum_Ico`, `sum_Ico_le_log`).
-/

@[expose] public section

open scoped BigOperators

open Filter Finset

namespace PiFormula

namespace Erdos

namespace Okada

/-! ## 1. The harmonic sum over `N ≤ n < cN` -/

theorem log_le_sum_Ico {c N : ℕ} (hc : 0 < c) (hN : 0 < N) :
    Real.log (c : ℝ) ≤ ∑ n ∈ Ico N (c * N), 1 / (n : ℝ) := by
  have h1 : ∀ n ∈ Ico N (c * N),
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    intro n hn
    have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (lt_of_lt_of_le hN (mem_Ico.1 hn).1)
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.2 n.succ_pos
    rw [← Real.log_div hn1.ne' hnR.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hn1 hnR)
    have e : ((n + 1 : ℕ) : ℝ) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
      push_cast
      field_simp
      ring
    linarith
  have h2 := Finset.sum_le_sum h1
  have h3 := Finset.sum_Ico_sub (fun n : ℕ => Real.log (n : ℝ)) (Nat.le_mul_of_pos_left N hc)
  beta_reduce at h3
  have hcR : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e : Real.log ((c * N : ℕ) : ℝ) - Real.log (N : ℝ) = Real.log (c : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hcR hNR]
    ring
  linarith

theorem sum_Ico_le_log {c N : ℕ} (hc : 0 < c) (hN : 2 ≤ N) :
    ∑ n ∈ Ico N (c * N), 1 / (n : ℝ) ≤ Real.log (c : ℝ) + 1 / ((N : ℝ) - 1) := by
  have h1 : ∀ n ∈ Ico N (c * N),
      1 / (n : ℝ) ≤ Real.log (((n + 1 : ℕ) : ℝ) - 1) - Real.log ((n : ℝ) - 1) := by
    intro n hn
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hN (mem_Ico.1 hn).1
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have e1 : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by
      push_cast
      ring
    rw [e1, ← Real.log_div hn0.ne' hn1.ne']
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hn1)
    have e2 : 1 - ((n : ℝ) / ((n : ℝ) - 1))⁻¹ = 1 / (n : ℝ) := by
      field_simp
      ring
    linarith
  have h2 := Finset.sum_le_sum h1
  have h3 := Finset.sum_Ico_sub (fun n : ℕ => Real.log ((n : ℝ) - 1))
    (Nat.le_mul_of_pos_left N hc)
  beta_reduce at h3
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have h4 : Real.log (((c * N : ℕ) : ℝ) - 1) ≤ Real.log (c : ℝ) + Real.log (N : ℝ) := by
    rw [← Real.log_mul (by linarith) hN0.ne']
    refine Real.log_le_log ?_ ?_
    · push_cast
      nlinarith
    · push_cast
      linarith
  have h5 : Real.log (N : ℝ) - Real.log ((N : ℝ) - 1) ≤ 1 / ((N : ℝ) - 1) := by
    rw [← Real.log_div hN0.ne' hN1.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hN0 hN1)
    have e : (N : ℝ) / ((N : ℝ) - 1) - 1 = 1 / ((N : ℝ) - 1) := by
      field_simp
      ring
    linarith
  linarith

theorem tendsto_sum_Ico_inv {c : ℕ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => ∑ n ∈ Ico N (c * N), 1 / (n : ℝ)) atTop (nhds (Real.log (c : ℝ))) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) - 1) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [sub_eq_add_neg] using h
  have h2 : Tendsto (fun N : ℕ => Real.log (c : ℝ) + 1 / ((N : ℝ) - 1)) atTop
      (nhds (Real.log (c : ℝ) + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop h1)
  rw [add_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN using log_le_sum_Ico hc hN
  · filter_upwards [eventually_ge_atTop 2] with N hN using sum_Ico_le_log hc hN

/-! ## 2. The class `n ≡ r` against its mean `1/q` -/

/-- The number of `i < M` with `i ≡ r` differs from `M/q` by at most `1`. -/
theorem abs_classCount_sub_le (q : ℕ) [NeZero q] (r : ZMod q) (M : ℕ) :
    |∑ i ∈ range M, ((if (i : ZMod q) = r then (1 : ℝ) else 0) - 1 / (q : ℝ))| ≤ 1 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.2 hq
  have hcount : ((range M).filter fun i : ℕ => (i : ZMod q) = r).card =
      Nat.count (· ≡ r.val [MOD q]) M := by
    rw [Nat.count_eq_card_filter_range]
    refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, card_range, nsmul_eq_mul,
    mul_one_div, hcount, Nat.count_modEq_card M hq]
  have h1 : ((M / q : ℕ) : ℝ) ≤ (M : ℝ) / (q : ℝ) := Nat.cast_div_le
  have h2 : (M : ℝ) / (q : ℝ) < ((M / q : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hqR]
    have h3 : (M : ℝ) < ((M / q : ℕ) : ℝ) * (q : ℝ) + (q : ℝ) := by
      exact_mod_cast Nat.lt_div_mul_add (a := M) hq
    linarith
  rw [abs_le]
  split_ifs
  · push_cast
    constructor <;> linarith
  · push_cast
    constructor <;> linarith

/-- The terms of the series `∑ ([n ≡ r] - 1/q)/n`, with `1/max(n, 1)` for `1/n`. -/
noncomputable def classTerm (q : ℕ) (r : ZMod q) (i : ℕ) : ℝ :=
  1 / max (i : ℝ) 1 * ((if (i : ZMod q) = r then (1 : ℝ) else 0) - 1 / (q : ℝ))

/-- Dirichlet's test: the series `∑ ([n ≡ r] - 1/q)/n` converges. -/
theorem exists_limit_classSum (q : ℕ) [NeZero q] (r : ZMod q) :
    ∃ l : ℝ, Tendsto (fun M : ℕ => ∑ i ∈ range M, classTerm q r i) atTop (nhds l) := by
  have hanti : Antitone (fun i : ℕ => 1 / max (i : ℝ) 1) := by
    intro i j hij
    exact one_div_le_one_div_of_le (lt_max_of_lt_right one_pos)
      (max_le_max (Nat.cast_le.2 hij) le_rfl)
  have hzero : Tendsto (fun i : ℕ => 1 / max (i : ℝ) 1) atTop (nhds 0) := by
    refine (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with i hi
    rw [max_eq_left (by exact_mod_cast hi)]
  have hb : ∀ M : ℕ,
      ‖∑ i ∈ range M, ((if (i : ZMod q) = r then (1 : ℝ) else 0) - 1 / (q : ℝ))‖ ≤ 1 :=
    fun M => by
      rw [Real.norm_eq_abs]
      exact abs_classCount_sub_le q r M
  have hC := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero hb
  simp only [smul_eq_mul] at hC
  exact cauchySeq_tendsto_of_complete hC

end Okada

open Okada

/-! ## 3. The window sums -/

/-- **The window sums**: `∑_{N ≤ n < cN, n ≡ r mod q} 1/n → (log c)/q`. -/
theorem okadaWindow : OkadaWindow := by
  intro q _ _ c hc r
  obtain ⟨l, hl⟩ := exists_limit_classSum q r
  have hcN : Tendsto (fun N : ℕ => c * N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hc) tendsto_id
  -- the part with mean `0` tends to `0`
  have hD : Tendsto (fun N : ℕ => ∑ i ∈ range (c * N), classTerm q r i -
      ∑ i ∈ range N, classTerm q r i) atTop (nhds (l - l)) := (hl.comp hcN).sub hl
  rw [sub_self] at hD
  -- the window sum is the sum of the two parts
  have hsplit : ∀ N : ℕ, 1 ≤ N →
      (∑ i ∈ range (c * N), classTerm q r i - ∑ i ∈ range N, classTerm q r i) +
        1 / (q : ℝ) * ∑ n ∈ Ico N (c * N), 1 / (n : ℝ) =
      ∑ n ∈ Ico N (c * N), if (n : ZMod q) = r then 1 / (n : ℝ) else 0 := by
    intro N hN
    rw [← Finset.sum_Ico_eq_sub _ (Nat.le_mul_of_pos_left N hc), Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hN (mem_Ico.1 hn).1
    unfold classTerm
    rw [max_eq_left hn1]
    split_ifs
    · ring
    · ring
  have hsum := hD.add ((tendsto_sum_Ico_inv hc).const_mul (1 / (q : ℝ)))
  have hval : (0 : ℝ) + 1 / (q : ℝ) * Real.log (c : ℝ) = Real.log (c : ℝ) / (q : ℝ) := by ring
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN using hsplit N hN

end Erdos

end PiFormula
