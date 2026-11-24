module

public import Pilean.Erdos.OkadaDefs
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Okada's criterion: two consequences of the window sums

From `OkadaWindow` (`∑_{N ≤ n < cN, n ≡ r mod q} 1/n → (log c)/q`), with `c = 2`:

* `okadaSumZero_of_window`: if the partial sums `S_N(f)` of `∑ f(n)/n` tend to `0`, then
  `∑_r f(r) = 0`. Indeed `S_{2N}(f) - S_N(f) = ∑_r f(r) W_N(r)` with `W_N(r)` the window sum,
  which tends to `(log 2 / q) ∑_r f(r)`, and it tends to `0`.
* `okadaHarmonicDiverges_of_window`: the sum of `1/n` over the `n` prime to `q` diverges.
  Its partial sums `T_N` increase, and `T_{2N} - T_N ≥ W_N(1) → (log 2)/q > 0`.
-/

@[expose] public section

open scoped BigOperators

open Filter

namespace PiFormula

namespace Erdos

namespace Okada

/-- A sum of `F(n)/n` over an interval, sorted by the residue of `n` modulo `q`. -/
theorem sum_Ico_eq_sum_window (q : ℕ) [NeZero q] (F : ZMod q → ℝ) (a b : ℕ) :
    ∑ n ∈ Finset.Ico a b, F (n : ZMod q) / (n : ℝ) =
      ∑ r : ZMod q, F r *
        ∑ n ∈ Finset.Ico a b, if (n : ZMod q) = r then 1 / (n : ℝ) else 0 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  ring

theorem tendsto_two_mul_atTop : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
  tendsto_atTop_mono (fun N => show N ≤ 2 * N by omega) tendsto_id

theorem log_two_div_pos (q : ℕ) [NeZero q] : 0 < Real.log ((2 : ℕ) : ℝ) / (q : ℝ) := by
  have h2 : (1 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
  have hq : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  exact div_pos (Real.log_pos h2) hq

end Okada

open Okada

/-- If the partial sums of `∑ f(n)/n` tend to `0`, then `∑_r f(r) = 0`. -/
theorem okadaSumZero_of_window (hW : OkadaWindow) : OkadaSumZero := by
  intro q _ hq f _ hS
  have hS' : Tendsto (partialSum q f) atTop (nhds 0) := hS
  -- `S_{2N} - S_N → 0`
  have h2 : Tendsto (fun N : ℕ => partialSum q f (2 * N) - partialSum q f N) atTop
      (nhds (0 - 0)) := (hS'.comp tendsto_two_mul_atTop).sub hS'
  rw [sub_zero] at h2
  -- `S_{2N} - S_N → (log 2 / q) ∑ f`
  have h4 : ∀ N : ℕ, partialSum q f (2 * N) - partialSum q f N =
      ∑ r : ZMod q, (f r : ℝ) *
        ∑ n ∈ Finset.Ico N (2 * N), if (n : ZMod q) = r then 1 / (n : ℝ) else 0 := by
    intro N
    unfold partialSum
    rw [← Finset.sum_Ico_eq_sub _ (show N ≤ 2 * N by omega)]
    exact sum_Ico_eq_sum_window q (fun r => (f r : ℝ)) N (2 * N)
  have h3 : Tendsto (fun N : ℕ => partialSum q f (2 * N) - partialSum q f N) atTop
      (nhds (∑ r : ZMod q, (f r : ℝ) * (Real.log ((2 : ℕ) : ℝ) / (q : ℝ)))) := by
    refine Tendsto.congr (fun N => (h4 N).symm) ?_
    exact tendsto_finsetSum _ fun r _ => (hW q hq 2 (by norm_num) r).const_mul _
  have h5 := tendsto_nhds_unique h3 h2
  rw [← Finset.sum_mul] at h5
  have h6 : ∑ r : ZMod q, (f r : ℝ) = 0 :=
    (mul_eq_zero.1 h5).resolve_right (log_two_div_pos q).ne'
  exact_mod_cast h6

/-- The sum of `1/n` over the `n` prime to `q` diverges. -/
theorem okadaHarmonicDiverges_of_window (hW : OkadaWindow) : OkadaHarmonicDiverges := by
  intro q _ hq
  have hmono : Monotone (unitSum q fun _ => (1 : ℝ)) := by
    refine monotone_nat_of_le_succ fun N => ?_
    unfold unitSum
    rw [Finset.sum_range_succ]
    refine le_add_of_nonneg_right ?_
    split_ifs
    · positivity
    · exact le_rfl
  rcases tendsto_atTop_of_monotone hmono with h | ⟨l, hl⟩
  · exact h
  · exfalso
    have h2 : Tendsto (fun N : ℕ => unitSum q (fun _ => (1 : ℝ)) (2 * N) -
        unitSum q (fun _ => (1 : ℝ)) N) atTop (nhds (l - l)) :=
      (hl.comp tendsto_two_mul_atTop).sub hl
    rw [sub_self] at h2
    have h3 : ∀ N : ℕ,
        (∑ n ∈ Finset.Ico N (2 * N), if (n : ZMod q) = 1 then 1 / (n : ℝ) else 0) ≤
          unitSum q (fun _ => (1 : ℝ)) (2 * N) - unitSum q (fun _ => (1 : ℝ)) N := by
      intro N
      unfold unitSum
      rw [← Finset.sum_Ico_eq_sub _ (show N ≤ 2 * N by omega)]
      refine Finset.sum_le_sum fun n _ => ?_
      by_cases hn : (n : ZMod q) = 1
      · have hc : n.Coprime q := (ZMod.isUnit_iff_coprime n q).1 (hn ▸ isUnit_one)
        simp only [hn, ↓reduceIte]
        split_ifs
        exact le_rfl
      · simp only [hn, ↓reduceIte]
        split_ifs
        · positivity
        · exact le_rfl
    have h5 := le_of_tendsto_of_tendsto' (hW q hq 2 (by norm_num) 1) h2 h3
    exact absurd h5 (not_le.2 (log_two_div_pos q))

end Erdos

end PiFormula
