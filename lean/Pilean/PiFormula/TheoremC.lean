module

public import Pilean.PiFormula.Fourier
public import Pilean.PiFormula.VSeries

/-!
# Theorem C, first part: period 120 and the dimension bounds (milestone M7, part 1)

For a period `N`, two spaces of rational patterns `ρ : ℕ → ℚ` (subspaces of `ℕ → ℚ` over `ℚ`):

* `algSpace N`: period `N`, and `S(ρ) = ∑ ρ(k) 2^(-⌊k/2⌋)/k` is an algebraic multiple of `π`;
* `ratSpace N`: period `N`, and `S(ρ)` is a rational multiple of `π` (possibly 0).

Proved here, **from Baker's theorem** (`theoremC_bounds`), for `N` a multiple of 120:

* every pattern of `algSpace N` has period 120 (`period_120`);
* `algSpace N` has dimension at most 13 (`rank_algSpace_le`, `finrank_algSpace_le`);
* `ratSpace N` has dimension at least 8 and at most 13.

The lower bound 8 is the family of `VSeries.lean` and needs no Baker (`le_rank_ratSpace`).

The upper bound: by `series_step1_real`, the coefficients `d_r` of a pattern of `algSpace N`
vanish outside `R0` and are a combination of the 13 relations on `R0`, with a coefficient
vector in `ℂ^13`. Fourteen such vectors are linearly dependent over `ℂ`; by Fourier inversion
(`twist_eq_sum`) so are the fourteen patterns, as complex vectors; and a complex dependence
among rational vectors gives a rational one (`rat_dependence`).

Not proved yet: that the dimensions are exactly 13 and exactly 8 (Theorem C in full). See
lean/PART3_PLAN.md.
-/

@[expose] public section

open Complex

namespace PiFormula

/-! ## 1. The two spaces of patterns -/

theorem seriesTerm_add (ρ ρ' : ℕ → ℚ) (k : ℕ) :
    seriesTerm (ρ + ρ') k = seriesTerm ρ k + seriesTerm ρ' k := by
  simp only [seriesTerm, Pi.add_apply]
  push_cast
  ring

theorem seriesTerm_smul (q : ℚ) (ρ : ℕ → ℚ) (k : ℕ) :
    seriesTerm (q • ρ) k = q * seriesTerm ρ k := by
  simp only [seriesTerm, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem seriesTerm_zero : seriesTerm 0 = fun _ => 0 := by
  funext k
  simp [seriesTerm]

/-- The rational patterns of period `N` whose series is an algebraic multiple of `π`. -/
def algSpace (N : ℕ) : Submodule ℚ (ℕ → ℚ) where
  carrier := {ρ | (∀ k, ρ (k + N) = ρ k) ∧
    ∃ γ : ℝ, IsAlgebraic ℚ γ ∧ HasSum (seriesTerm ρ) (γ * Real.pi)}
  add_mem' := by
    rintro ρ ρ' ⟨hp, γ, hγ, h⟩ ⟨hp', γ', hγ', h'⟩
    refine ⟨fun k => by simp only [Pi.add_apply, hp k, hp' k], γ + γ', hγ.add hγ', ?_⟩
    have h2 := h.add h'
    rw [← add_mul] at h2
    have e : seriesTerm (ρ + ρ') = fun k => seriesTerm ρ k + seriesTerm ρ' k :=
      funext (seriesTerm_add ρ ρ')
    rw [e]
    exact h2
  zero_mem' := by
    refine ⟨fun _ => rfl, 0, isAlgebraic_zero, ?_⟩
    rw [zero_mul, seriesTerm_zero]
    exact hasSum_zero
  smul_mem' := by
    rintro q ρ ⟨hp, γ, hγ, h⟩
    refine ⟨fun k => by simp only [Pi.smul_apply, hp k], q * γ,
      IsAlgebraic.mul (isAlgebraic_ratCast ℚ (A := ℝ) q) hγ, ?_⟩
    have h2 := h.mul_left (q : ℝ)
    rw [← mul_assoc] at h2
    have e : seriesTerm (q • ρ) = fun k => (q : ℝ) * seriesTerm ρ k :=
      funext (seriesTerm_smul q ρ)
    rw [e]
    exact h2

/-- The rational patterns of period `N` whose series is a rational multiple of `π`. -/
def ratSpace (N : ℕ) : Submodule ℚ (ℕ → ℚ) where
  carrier := {ρ | (∀ k, ρ (k + N) = ρ k) ∧ ∃ q : ℚ, HasSum (seriesTerm ρ) (q * Real.pi)}
  add_mem' := by
    rintro ρ ρ' ⟨hp, q, h⟩ ⟨hp', q', h'⟩
    refine ⟨fun k => by simp only [Pi.add_apply, hp k, hp' k], q + q', ?_⟩
    have h2 := h.add h'
    rw [← add_mul] at h2
    have e : seriesTerm (ρ + ρ') = fun k => seriesTerm ρ k + seriesTerm ρ' k :=
      funext (seriesTerm_add ρ ρ')
    rw [e]
    push_cast
    exact h2
  zero_mem' := by
    refine ⟨fun _ => rfl, 0, ?_⟩
    rw [Rat.cast_zero, zero_mul, seriesTerm_zero]
    exact hasSum_zero
  smul_mem' := by
    rintro c ρ ⟨hp, q, h⟩
    refine ⟨fun k => by simp only [Pi.smul_apply, hp k], c * q, ?_⟩
    have h2 := h.mul_left (c : ℝ)
    rw [← mul_assoc] at h2
    have e : seriesTerm (c • ρ) = fun k => (c : ℝ) * seriesTerm ρ k :=
      funext (seriesTerm_smul c ρ)
    rw [e]
    push_cast
    exact h2

theorem ratSpace_le_algSpace (N : ℕ) : ratSpace N ≤ algSpace N := by
  rintro ρ ⟨hp, q, h⟩
  exact ⟨hp, q, isAlgebraic_ratCast ℚ (A := ℝ) q, h⟩

/-- Step 1 for a pattern of `algSpace N`. -/
theorem inSpan13_of_mem (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ρ ∈ algSpace N) : InSpan13 (rootsN N) (fourierD N ρ) := by
  obtain ⟨hp, γ, hγ, h⟩ := hρ
  exact series_step1_real hB hN h8 hp hγ h

/-! ## 2. The pattern is recovered from its coefficients -/

/-- The twisting factor `t^(k mod 2) i^⌊k/2⌋`. -/
noncomputable def uTw (k : ℕ) : ℂ := tC ^ (k % 2) * I ^ (k / 2)

theorem uTw_ne_zero (k : ℕ) : uTw k ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ tC_ne_zero) (pow_ne_zero _ Complex.I_ne_zero)

theorem twist_eq (ρ : ℕ → ℚ) (k : ℕ) : twist ρ k = (ρ k : ℂ) * uTw k := rfl

theorem uTw_add_120 (k : ℕ) : uTw (k + 120) = uTw k := by
  have h1 : (k + 120) % 2 = k % 2 := by omega
  have h2 : (k + 120) / 2 = k / 2 + 4 * 15 := by omega
  rw [uTw, uTw, h1, h2, pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

/-- **Fourier inversion for the series**: `ρ(k) t^(k mod 2) i^⌊k/2⌋ = -∑_r d_r r^k`. -/
theorem twist_eq_sum {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) (k : ℕ) :
    twist ρ k = -∑ r ∈ rootsN N, fourierD N ρ r * r ^ k := by
  rw [sum_rootsN hN (fun r => fourierD N ρ r * r ^ k)]
  have h := fourier_inversion hN (twist_periodic h8 hρ) k
  rw [← h, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fourierD]
  ring

theorem pow_add_120_of_mem_R0 {r : ℂ} (hr : r ∈ R0) (k : ℕ) : r ^ (k + 120) = r ^ k := by
  obtain ⟨j, -, rfl⟩ := hr
  have h : (ζ120 ^ j) ^ 120 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ζ120_prim.pow_eq_one, one_pow]
  rw [pow_add, h, mul_one]

/-- A pattern whose coefficients vanish outside `R0` has period 120. -/
theorem period_120_of_inSpan13 {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) (h : InSpan13 (rootsN N) (fourierD N ρ)) (k : ℕ) :
    ρ (k + 120) = ρ k := by
  have h1 : twist ρ (k + 120) = twist ρ k := by
    rw [twist_eq_sum hN h8 hρ, twist_eq_sum hN h8 hρ]
    refine congrArg (fun x : ℂ => -x) (Finset.sum_congr rfl fun r hr => ?_)
    by_cases hR : r ∈ R0
    · rw [pow_add_120_of_mem_R0 hR]
    · rw [h.1 r hr hR, zero_mul, zero_mul]
  rw [twist_eq, twist_eq, uTw_add_120] at h1
  have h2 := mul_right_cancel₀ (uTw_ne_zero k) h1
  exact_mod_cast h2

/-- **Period 120 (from Baker's theorem).** A rational pattern of any period `N` (`8 ∣ N`) whose
series is an algebraic multiple of `π` has period 120. -/
theorem period_120 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ρ ∈ algSpace N) (k : ℕ) : ρ (k + 120) = ρ k :=
  period_120_of_inSpan13 hN h8 hρ.1 (inSpan13_of_mem hB hN h8 hρ) k

/-! ## 3. Dimension at most 13 -/

theorem combC_lin (a : ℂ) (c c' : Fin 13 → ℂ) (j : ℕ) :
    combC (fun k => a * c k + c' k) j = a * combC c j + combC c' j := by
  simp only [combC]
  ring

theorem combC_zero (j : ℕ) : combC (fun _ => 0) j = 0 := by
  simp [combC]

theorem combC_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (c : ι → Fin 13 → ℂ) (j : ℕ) :
    ∑ i ∈ s, a i * combC (c i) j = combC (fun k => ∑ i ∈ s, a i * c i k) j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [combC_zero]
  | insert i s hi ih =>
    have e : (fun k => ∑ x ∈ insert i s, a x * c x k) =
        fun k => a i * c i k + ∑ x ∈ s, a x * c x k := by
      funext k
      rw [Finset.sum_insert hi]
    rw [Finset.sum_insert hi, ih, e, combC_lin]

/-- A complex dependence among the coefficient vectors gives a complex dependence among the
patterns. -/
theorem sum_pattern_eq_zero {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N) {ι : Type*} [Fintype ι]
    (ρ : ι → ℕ → ℚ) (hρ : ∀ i k, ρ i (k + N) = ρ i k) (c : ι → Fin 13 → ℂ)
    (hzero : ∀ i, ∀ r ∈ rootsN N, r ∉ R0 → fourierD N (ρ i) r = 0)
    (hcomb : ∀ i, ∀ j ∈ R0Exps, ζ120 ^ j ∈ rootsN N →
      fourierD N (ρ i) (ζ120 ^ j) = combC (c i) j)
    (a : ι → ℂ) (ha : ∀ k, ∑ i, a i * c i k = 0) (k : ℕ) :
    ∑ i, a i * (ρ i k : ℂ) = 0 := by
  have hD : ∀ r ∈ rootsN N, ∑ i, a i * fourierD N (ρ i) r = 0 := by
    intro r hr
    by_cases hR : r ∈ R0
    · obtain ⟨j, hj, rfl⟩ := hR
      rw [Finset.sum_congr rfl fun i _ => by rw [hcomb i j hj hr], combC_sum]
      have e : (fun k => ∑ i, a i * c i k) = fun _ => 0 := funext ha
      rw [e, combC_zero]
    · exact Finset.sum_eq_zero fun i _ => by rw [hzero i r hr hR, mul_zero]
  have h1 : ∑ i, a i * twist (ρ i) k = 0 := by
    calc ∑ i, a i * twist (ρ i) k
        = ∑ i, -∑ r ∈ rootsN N, a i * (fourierD N (ρ i) r * r ^ k) :=
          Finset.sum_congr rfl fun i _ => by
            rw [twist_eq_sum hN h8 (hρ i), mul_neg, Finset.mul_sum]
      _ = -∑ r ∈ rootsN N, ∑ i, a i * (fourierD N (ρ i) r * r ^ k) := by
          rw [Finset.sum_neg_distrib, Finset.sum_comm]
      _ = -∑ r ∈ rootsN N, (∑ i, a i * fourierD N (ρ i) r) * r ^ k := by
          refine congrArg (fun x : ℂ => -x) (Finset.sum_congr rfl fun r _ => ?_)
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by
          rw [Finset.sum_eq_zero fun r hr => by rw [hD r hr, zero_mul], neg_zero]
  have h2 : (∑ i, a i * (ρ i k : ℂ)) * uTw k = 0 := by
    rw [Finset.sum_mul, ← h1]
    exact Finset.sum_congr rfl fun i _ => by rw [twist_eq]; ring
  exact (mul_eq_zero.1 h2).resolve_right (uTw_ne_zero k)

/-- A complex linear dependence among rational vectors gives a rational one: apply a
`ℚ`-linear form `ℂ → ℚ` that does not vanish on one of the coefficients. -/
theorem rat_dependence {ι : Type*} [Fintype ι] {κ : Type*} (v : ι → κ → ℚ) (a : ι → ℂ)
    {i₀ : ι} (hi₀ : a i₀ ≠ 0) (h : ∀ k, ∑ i, a i * (v i k : ℂ) = 0) :
    ∃ q : ι → ℚ, q i₀ ≠ 0 ∧ ∀ k, ∑ i, q i * v i k = 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℚ ℂ, φ (a i₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hi₀ ((Module.forall_dual_apply_eq_zero_iff ℚ (a i₀)).1 hcon)
  refine ⟨fun i => φ (a i), hφ, fun k => ?_⟩
  have h1 := congrArg φ (h k)
  rw [map_sum, map_zero] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : a i * (v i k : ℂ) = (v i k : ℚ) • a i := by rw [Rat.smul_def, mul_comm]
  rw [e, map_smul, smul_eq_mul, mul_comm]

/-- More than 13 patterns of `algSpace N` are linearly dependent over `ℚ`. -/
theorem not_linearIndependent_of_card (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N)
    {ι : Type*} [Fintype ι] (hcard : 13 < Fintype.card ι) (ρ : ι → ℕ → ℚ)
    (hmem : ∀ i, ρ i ∈ algSpace N) : ¬ LinearIndependent ℚ ρ := by
  intro hLI
  have hspan := fun i => inSpan13_of_mem hB hN h8 (hmem i)
  choose c hc using fun i => (hspan i).2
  -- more than 13 vectors of `ℂ^13` are dependent
  have hnot : ¬ LinearIndependent ℂ c := fun hc' => by
    have h1 := hc'.fintype_card_le_finrank
    rw [Module.finrank_fin_fun] at h1
    omega
  rw [Fintype.linearIndependent_iff] at hnot
  push Not at hnot
  obtain ⟨a, ha, i₀, hi₀⟩ := hnot
  have ha' : ∀ k, ∑ i, a i * c i k = 0 := fun k => by
    have h1 := congrFun ha k
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h1
  have hdep := fun k => sum_pattern_eq_zero hN h8 ρ (fun i => (hmem i).1) c
    (fun i => (hspan i).1)
    (fun i j hj hjS => by
      have h1 := (hc i).2 j hj
      simp only [hjS, ↓reduceIte] at h1
      exact h1) a ha' k
  obtain ⟨q, hq, hsum⟩ := rat_dependence ρ a hi₀ hdep
  rw [Fintype.linearIndependent_iff] at hLI
  refine hq (hLI q ?_ i₀)
  funext k
  simpa [Finset.sum_apply] using hsum k

/-- **Dimension at most 13 (from Baker's theorem).** -/
theorem rank_algSpace_le (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N) :
    Module.rank ℚ (algSpace N) ≤ (13 : ℕ) := by
  refine rank_le fun s hs => ?_
  by_contra hcard
  push Not at hcard
  have hLI : LinearIndependent ℚ (fun i : s => ((i : algSpace N) : ℕ → ℚ)) :=
    hs.map' (algSpace N).subtype (Submodule.ker_subtype _)
  exact not_linearIndependent_of_card hB hN h8 (ι := s) (by simpa using hcard)
    (fun i : s => ((i : algSpace N) : ℕ → ℚ)) (fun i => (i : algSpace N).2) hLI

theorem finite_algSpace (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N) :
    Module.Finite ℚ (algSpace N) :=
  Module.rank_lt_aleph0_iff.1 ((rank_algSpace_le hB hN h8).trans_lt Cardinal.natCast_lt_aleph0)

theorem finrank_algSpace_le (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N) :
    Module.finrank ℚ (algSpace N) ≤ 13 :=
  Module.finrank_le_of_rank_le (rank_algSpace_le hB hN h8)

/-! ## 4. Dimension at least 8 for the rational multiples -/

theorem periodic_of_dvd {f : ℕ → ℚ} (h : ∀ k, f (k + 120) = f k) {N : ℕ} (hN : 120 ∣ N)
    (k : ℕ) : f (k + N) = f k := by
  obtain ⟨m, rfl⟩ := hN
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, ← add_assoc, h, ih]

theorem mem_ratSpace_of {f : ℕ → ℚ} (hp : ∀ k, f (k + 120) = f k) {q : ℚ}
    (h : HasSum (seriesTerm f) (q * Real.pi)) {N : ℕ} (hN : 120 ∣ N) : f ∈ ratSpace N :=
  ⟨periodic_of_dvd hp hN, q, h⟩

theorem quarter_pi : ((1 / 4 : ℚ) : ℝ) * Real.pi = Real.pi / 4 := by
  push_cast
  ring

theorem zero_pi : ((0 : ℚ) : ℝ) * Real.pi = 0 := by
  rw [Rat.cast_zero, zero_mul]

/-- The eight named patterns, as elements of `ratSpace N`. -/
noncomputable def namedFam {N : ℕ} (hN : 120 ∣ N) : Fin 8 → ratSpace N :=
  ![⟨namedA1, mem_ratSpace_of (q := 1 / 4) (fun k => (named_periodic k).1)
      (by rw [quarter_pi]; exact hasSum_namedA1) hN⟩,
    ⟨namedA6, mem_ratSpace_of (q := 0) (fun k => (named_periodic k).2.1)
      (by rw [zero_pi]; exact hasSum_namedA6) hN⟩,
    ⟨namedA10, mem_ratSpace_of (q := 1 / 4) (fun k => (named_periodic k).2.2.1)
      (by rw [quarter_pi]; exact hasSum_namedA10) hN⟩,
    ⟨namedL6, mem_ratSpace_of (q := 0) (fun k => (named_periodic k).2.2.2.1)
      (by rw [zero_pi]; exact hasSum_namedL6) hN⟩,
    ⟨namedL8, mem_ratSpace_of (q := 0) (fun k => (named_periodic k).2.2.2.2.1)
      (by rw [zero_pi]; exact hasSum_namedL8) hN⟩,
    ⟨namedL10, mem_ratSpace_of (q := 0) (fun k => (named_periodic k).2.2.2.2.2.1)
      (by rw [zero_pi]; exact hasSum_namedL10) hN⟩,
    ⟨namedL24, mem_ratSpace_of (q := 0) (fun k => (named_periodic k).2.2.2.2.2.2.1)
      (by rw [zero_pi]; exact hasSum_namedL24) hN⟩,
    ⟨namedTW, mem_ratSpace_of (q := 0) (fun k => (named_periodic k).2.2.2.2.2.2.2)
      (by rw [zero_pi]; exact hasSum_namedTW) hN⟩]

theorem namedFam_linearIndependent {N : ℕ} (hN : 120 ∣ N) :
    LinearIndependent ℚ (namedFam hN) := by
  refine LinearIndependent.of_comp (ratSpace N).subtype ?_
  have e : (ratSpace N).subtype ∘ namedFam hN =
      ![namedA1, namedA6, namedA10, namedL6, namedL8, namedL10, namedL24, namedTW] := by
    funext i
    fin_cases i <;> rfl
  rw [e]
  exact named_linearIndependent

/-- **Dimension at least 8** (no Baker's theorem): the eight named patterns. -/
theorem le_rank_ratSpace {N : ℕ} (hN : 120 ∣ N) :
    ((8 : ℕ) : Cardinal) ≤ Module.rank ℚ (ratSpace N) := by
  have h := (namedFam_linearIndependent hN).cardinal_le_rank
  simpa using h

/-! ## 5. Theorem C, first part -/

/-- **Theorem C, first part (from Baker's theorem).** Let `N` be a multiple of 120.
* Every rational pattern of period `N` whose series is an algebraic multiple of `π` has period
  120.
* These patterns form a space of dimension at most 13.
* Those whose series is a rational multiple of `π` form a subspace of dimension at least 8
  (and at most 13).

The full Theorem C says that the dimensions are exactly 13 and 8. -/
theorem theoremC_bounds (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) :
    (∀ ρ ∈ algSpace N, ∀ k, ρ (k + 120) = ρ k) ∧
      Module.finrank ℚ (algSpace N) ≤ 13 ∧
      8 ≤ Module.finrank ℚ (ratSpace N) ∧
      Module.finrank ℚ (ratSpace N) ≤ Module.finrank ℚ (algSpace N) := by
  have h8 : 8 ∣ N := Dvd.dvd.trans (by norm_num) h120
  have hfin := finite_algSpace hB hN h8
  have hfin' : Module.Finite ℚ (ratSpace N) :=
    Module.Finite.of_injective (Submodule.inclusion (ratSpace_le_algSpace N))
      (Submodule.inclusion_injective _)
  refine ⟨fun ρ hρ k => period_120 hB hN h8 hρ k, finrank_algSpace_le hB hN h8, ?_,
    Submodule.finrank_mono (ratSpace_le_algSpace N)⟩
  have h := (namedFam_linearIndependent h120).fintype_card_le_finrank
  simpa using h

end PiFormula
