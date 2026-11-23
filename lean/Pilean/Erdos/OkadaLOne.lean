import Pilean.Erdos.OkadaDefs
import Mathlib.Algebra.BigOperators.Module
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# `L(1, χ)` is the limit of the partial sums of `∑ χ(n)/n`

`okadaLOne : OkadaLOne`: for a non-principal Dirichlet character `χ` modulo `q`, the partial
sums `∑_{n < N} χ(n)/n` tend to `DirichletCharacter.LFunction χ 1`, which is not `0`
(`DirichletCharacter.LFunction_apply_one_ne_zero`, in Mathlib). Status: complete, no
hypothesis. The oddness of `q` is not used.

What Mathlib does not have is the link between the value at `1` of the analytic continuation
and the conditionally convergent series. The proof here uses no integral:

* `lone_norm_sum_range_le`: the partial sums of `χ` are bounded by `q` (the sum over a full
  period is `0`).
* `lone_abel_bound`: Abel's inequality. If the partial sums of `g` are bounded by `C` and `f`
  is non-negative and non-increasing from `m` on, then `‖∑_{m ≤ i < n} f(i) g(i)‖ ≤ 2 C f(m)`
  (summation by parts, `Finset.sum_Ico_by_parts`).
* `lone_tail_bound`: so `‖∑_{M ≤ n < N} χ(n) n^(-s)‖ ≤ 2q/M` for every real `s ≥ 1`: the
  Dirichlet series converges uniformly on `[1, ∞)`.
* `lone_norm_sub_le_of_one_lt`: for real `s > 1` the series converges absolutely to
  `LFunction χ s`, so `‖LFunction χ s - ∑_{n < M} χ(n) n^(-s)‖ ≤ 2q/M`.
* `lone_norm_sub_le_one`: both sides are continuous in `s`, so the same bound holds at
  `s = 1` (limit `s → 1⁺`).
* `lone_tendsto`: let `M → ∞`.
-/

open scoped BigOperators

open Filter Finset

namespace PiFormula

namespace Erdos

namespace Okada

/-! ## 1. The partial sums of a non-principal character are bounded -/

/-- A sum over `0 ≤ x < q` of a function of the residue of `x` is the sum over `ℤ/q`. -/
theorem lone_sum_range_zmod (q : ℕ) [NeZero q] (g : ZMod q → ℂ) :
    ∑ x ∈ range q, g (x : ZMod q) = ∑ a : ZMod q, g a := by
  refine Finset.sum_nbij' (fun x : ℕ => (x : ZMod q)) ZMod.val ?_ ?_ ?_ ?_ ?_
  · intro x _
    exact mem_univ _
  · intro a _
    exact mem_range.2 (ZMod.val_lt a)
  · intro x hx
    exact ZMod.val_cast_of_lt (mem_range.1 hx)
  · intro a _
    exact ZMod.natCast_zmod_val a
  · intro x _
    rfl

/-- The sum of a non-principal character over `q` consecutive integers is `0`. -/
theorem lone_sum_range_add_period (q : ℕ) [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (n : ℕ) :
    ∑ i ∈ range (n + q), χ (i : ZMod q) = ∑ i ∈ range n, χ (i : ZMod q) := by
  rw [Finset.sum_range_add]
  have h : ∑ x ∈ range q, χ ((n + x : ℕ) : ZMod q) = 0 := by
    have h1 : ∑ x ∈ range q, χ ((n : ZMod q) + (x : ZMod q)) =
        ∑ a : ZMod q, χ ((n : ZMod q) + a) :=
      lone_sum_range_zmod q fun a => χ ((n : ZMod q) + a)
    simp only [Nat.cast_add]
    rw [h1, Fintype.sum_equiv (Equiv.addLeft (n : ZMod q)) (fun a => χ ((n : ZMod q) + a))
      (fun a => χ a) (fun a => rfl)]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  rw [h, add_zero]

/-- The partial sums of a non-principal character modulo `q` are bounded by `q`. -/
theorem lone_norm_sum_range_le (q : ℕ) [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (n : ℕ) : ‖∑ i ∈ range n, χ (i : ZMod q)‖ ≤ (q : ℝ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n q with h | h
    · calc ‖∑ i ∈ range n, χ (i : ZMod q)‖ ≤ ∑ i ∈ range n, ‖χ (i : ZMod q)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _i ∈ range n, (1 : ℝ) := Finset.sum_le_sum fun i _ => χ.norm_le_one _
        _ = (n : ℝ) := by simp
        _ ≤ (q : ℝ) := by exact_mod_cast h.le
    · have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      have e : n = (n - q) + q := (Nat.sub_add_cancel h).symm
      rw [e, lone_sum_range_add_period q hχ]
      exact ih (n - q) (by omega)

/-! ## 2. Abel's inequality -/

/-- **Abel's inequality.** If the partial sums of `g` are bounded by `C`, and `f` is
non-negative and non-increasing from `m` on, then `‖∑_{m ≤ i < n} f(i) g(i)‖ ≤ 2 C f(m)`. -/
theorem lone_abel_bound (f : ℕ → ℝ) (g : ℕ → ℂ) (C : ℝ)
    (hC : ∀ n, ‖∑ i ∈ range n, g i‖ ≤ C) {m n : ℕ} (hmn : m ≤ n)
    (hf : ∀ i, m ≤ i → f (i + 1) ≤ f i) (hf0 : ∀ i, m ≤ i → 0 ≤ f i) :
    ‖∑ i ∈ Ico m n, f i • g i‖ ≤ 2 * C * f m := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  rcases hmn.eq_or_lt with rfl | hlt
  · rw [Finset.Ico_self, Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hC0) (hf0 m le_rfl)
  · rw [Finset.sum_Ico_by_parts f g hlt]
    have hn1 : 0 ≤ f (n - 1) := hf0 _ (by omega)
    have h1 : ‖f (n - 1) • ∑ i ∈ range n, g i‖ ≤ f (n - 1) * C := by
      rw [norm_smul, Real.norm_of_nonneg hn1]
      exact mul_le_mul_of_nonneg_left (hC n) hn1
    have h2 : ‖f m • ∑ i ∈ range m, g i‖ ≤ f m * C := by
      rw [norm_smul, Real.norm_of_nonneg (hf0 _ le_rfl)]
      exact mul_le_mul_of_nonneg_left (hC m) (hf0 _ le_rfl)
    have h3 : ‖∑ i ∈ Ico m (n - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖ ≤
        (f m - f (n - 1)) * C := by
      calc ‖∑ i ∈ Ico m (n - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖
          ≤ ∑ i ∈ Ico m (n - 1), ‖(f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i ∈ Ico m (n - 1), -(f (i + 1) - f i) * C := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' : f (i + 1) ≤ f i := hf i (Finset.mem_Ico.1 hi).1
            rw [norm_smul, Real.norm_of_nonpos (sub_nonpos.2 hi')]
            exact mul_le_mul_of_nonneg_left (hC (i + 1)) (by linarith)
        _ = (f m - f (n - 1)) * C := by
            rw [← Finset.sum_mul, Finset.sum_neg_distrib, Finset.sum_Ico_sub f (by omega)]
            ring
    calc ‖f (n - 1) • ∑ i ∈ range n, g i - f m • ∑ i ∈ range m, g i -
          ∑ i ∈ Ico m (n - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖
        ≤ ‖f (n - 1) • ∑ i ∈ range n, g i‖ + ‖f m • ∑ i ∈ range m, g i‖ +
          ‖∑ i ∈ Ico m (n - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ f (n - 1) * C + f m * C + (f m - f (n - 1)) * C := add_le_add (add_le_add h1 h2) h3
      _ = 2 * C * f m := by ring

/-! ## 3. The Dirichlet series of `χ` on `[1, ∞)` -/

/-- The term `f(n)/n^s` of an L-series at a real `s`, with a real power. -/
theorem lone_term_eq (f : ℕ → ℂ) (s : ℝ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term f (s : ℂ) n = ((n : ℝ) ^ (-s)) • f n := by
  rw [LSeries.term_of_ne_zero hn, Complex.real_smul, Complex.ofReal_cpow (Nat.cast_nonneg n),
    Complex.ofReal_neg, Complex.ofReal_natCast, Complex.cpow_neg]
  ring

/-- The tails of `∑ χ(n) n^(-s)` are small uniformly in the real number `s ≥ 1`. -/
theorem lone_tail_bound (q : ℕ) [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℝ}
    (hs : 1 ≤ s) {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    ‖∑ n ∈ Ico M N, LSeries.term (fun n : ℕ => χ (n : ZMod q)) (s : ℂ) n‖ ≤
      2 * (q : ℝ) / (M : ℝ) := by
  have e : ∑ n ∈ Ico M N, LSeries.term (fun n : ℕ => χ (n : ZMod q)) (s : ℂ) n =
      ∑ n ∈ Ico M N, ((n : ℝ) ^ (-s)) • χ (n : ZMod q) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : M ≤ n := (Finset.mem_Ico.1 hn).1
    exact lone_term_eq _ s (by omega)
  rw [e]
  have hanti : ∀ i : ℕ, M ≤ i → ((i + 1 : ℕ) : ℝ) ^ (-s) ≤ (i : ℝ) ^ (-s) := by
    intro i hi
    have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hM.trans hi
    exact Real.rpow_le_rpow_of_nonpos hi0 (by push_cast; linarith) (by linarith)
  have hnn : ∀ i : ℕ, M ≤ i → 0 ≤ (i : ℝ) ^ (-s) := fun i _ =>
    Real.rpow_nonneg (Nat.cast_nonneg i) _
  refine (lone_abel_bound (fun n : ℕ => (n : ℝ) ^ (-s)) (fun n : ℕ => χ (n : ZMod q)) (q : ℝ)
    (lone_norm_sum_range_le q hχ) hMN hanti hnn).trans ?_
  have hpow : (M : ℝ) ^ (-s) ≤ (M : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM) (by linarith)
  calc 2 * (q : ℝ) * (M : ℝ) ^ (-s) ≤ 2 * (q : ℝ) * (M : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 2 * (q : ℝ) / (M : ℝ) := by rw [div_eq_mul_inv]

/-- For real `s > 1` the partial sums of `∑ χ(n) n^(-s)` tend to `LFunction χ s`. -/
theorem lone_tendsto_of_one_lt (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℝ}
    (hs : 1 < s) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, LSeries.term (fun n : ℕ => χ (n : ZMod q)) (s : ℂ) n)
      atTop (nhds (DirichletCharacter.LFunction χ (s : ℂ))) := by
  have hs' : 1 < ((s : ℂ)).re := by
    rw [Complex.ofReal_re]
    exact hs
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs']
  exact HasSum.tendsto_sum_nat
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs').LSeriesHasSum

/-- For real `s > 1`: `‖LFunction χ s - ∑_{n < M} χ(n) n^(-s)‖ ≤ 2q/M`. -/
theorem lone_norm_sub_le_of_one_lt (q : ℕ) [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℝ} (hs : 1 < s) {M : ℕ} (hM : 1 ≤ M) :
    ‖DirichletCharacter.LFunction χ (s : ℂ) -
      ∑ n ∈ range M, LSeries.term (fun n : ℕ => χ (n : ZMod q)) (s : ℂ) n‖ ≤
      2 * (q : ℝ) / (M : ℝ) := by
  have h := ((lone_tendsto_of_one_lt q χ hs).sub_const
    (∑ n ∈ range M, LSeries.term (fun n : ℕ => χ (n : ZMod q)) (s : ℂ) n)).norm
  refine le_of_tendsto h (eventually_atTop.2 ⟨M, fun N hN => ?_⟩)
  have h2 := lone_tail_bound q hχ hs.le hM hN
  rw [Finset.sum_Ico_eq_sub _ hN] at h2
  exact h2

/-- The same bound at `s = 1`, by continuity:
`‖LFunction χ 1 - ∑_{n < M} χ(n)/n‖ ≤ 2q/M`. -/
theorem lone_norm_sub_le_one (q : ℕ) [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {M : ℕ} (hM : 1 ≤ M) :
    ‖DirichletCharacter.LFunction χ 1 -
      ∑ n ∈ range M, LSeries.term (fun n : ℕ => χ (n : ZMod q)) 1 n‖ ≤
      2 * (q : ℝ) / (M : ℝ) := by
  have hc : ContinuousAt (fun z : ℂ => DirichletCharacter.LFunction χ z -
      ∑ n ∈ range M, LSeries.term (fun n : ℕ => χ (n : ZMod q)) z n) ((1 : ℝ) : ℂ) := by
    refine ((DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt).sub ?_
    exact tendsto_finsetSum _ fun n _ =>
      (LSeries.hasDerivAt_term (fun n : ℕ => χ (n : ZMod q)) n _).continuousAt
  have ht : Tendsto (fun x : ℝ => ‖DirichletCharacter.LFunction χ (x : ℂ) -
      ∑ n ∈ range M, LSeries.term (fun n : ℕ => χ (n : ZMod q)) (x : ℂ) n‖)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ‖DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ) -
        ∑ n ∈ range M, LSeries.term (fun n : ℕ => χ (n : ZMod q)) ((1 : ℝ) : ℂ) n‖) :=
    ((hc.comp (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ)))).norm.tendsto).mono_left
      nhdsWithin_le_nhds
  rw [Complex.ofReal_one] at ht
  refine le_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact lone_norm_sub_le_of_one_lt q hχ hx hM

/-! ## 4. The limit of the partial sums -/

/-- For a non-principal Dirichlet character `χ`, the partial sums of `∑ χ(n)/n` tend to
`LFunction χ 1`. -/
theorem lone_tendsto (q : ℕ) [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, χ (n : ZMod q) / (n : ℂ)) atTop
      (nhds (DirichletCharacter.LFunction χ 1)) := by
  have hterm : ∀ n : ℕ,
      LSeries.term (fun n : ℕ => χ (n : ZMod q)) 1 n = χ (n : ZMod q) / (n : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, Complex.cpow_one]
  have h0 : Tendsto (fun N : ℕ => (∑ n ∈ range N, χ (n : ZMod q) / (n : ℂ)) -
      DirichletCharacter.LFunction χ 1) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (2 * (q : ℝ)))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have e : ∑ n ∈ range N, χ (n : ZMod q) / (n : ℂ) =
        ∑ n ∈ range N, LSeries.term (fun n : ℕ => χ (n : ZMod q)) 1 n :=
      Finset.sum_congr rfl fun n _ => (hterm n).symm
    rw [e, norm_sub_rev]
    exact lone_norm_sub_le_one q hχ hN
  exact tendsto_sub_nhds_zero_iff.1 h0

end Okada

/-- **`L(1, χ) ≠ 0` as a statement on partial sums.** For a non-principal Dirichlet character
`χ` modulo `q`, the partial sums `∑_{n < N} χ(n)/n` have a limit, namely
`DirichletCharacter.LFunction χ 1`, and it is not `0`. -/
theorem okadaLOne : OkadaLOne := by
  intro q _ _ χ hχ
  exact ⟨DirichletCharacter.LFunction χ 1, DirichletCharacter.LFunction_apply_one_ne_zero hχ,
    Okada.lone_tendsto q hχ⟩

end Erdos

end PiFormula
