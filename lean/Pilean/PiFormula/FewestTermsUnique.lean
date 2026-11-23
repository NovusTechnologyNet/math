import Pilean.PiFormula.TheoremE
import Pilean.PiFormula.FewestTermsUniqueCert
import Pilean.PiFormula.Unconditional

/-!
# Theorem E, the standard measure: the optimum is attained only by Huvent's two formulas

`termCount_ge` says that a series of the class F whose value is a non-zero rational multiple
of `π` has at least 40 non-zero entries per period of 120, and `termCount_rhoHuvent1`,
`termCount_rhoHuvent2` say that Huvent's two formulas have exactly 40. This file proves that
they are the only ones:

* `termCount_eq_forty_iff` (from Baker's theorem): a rational pattern whose series is a
  non-zero rational multiple of `π` has exactly 40 non-zero entries per 120 if and only if it
  is a non-zero rational multiple of `rhoHuvent1` or of `rhoHuvent2`;
* `termCount_ge_forty_one` (from Baker's theorem): every other such pattern has at least 41;
* `Unconditional.termCount_eq_forty_iff`, `Unconditional.termCount_ge_forty_one`: the same
  with no hypothesis (Baker's theorem is proved in `Baker/`).

The proof is a case tree on the 35 classes of zero conditions, as for the bound 40
(`FewestTerms.lean`), with the bound 41 and one new kind of leaf: at two places of the tree
seven independent classes vanish and the bound 41 fails; there the seven conditions leave a
line of the 8-dimensional space `V`, and the line is the one through Huvent's first (second)
pattern (`huvS1_line`, `huvS2_line`). The tree is in `FewestTermsUniqueCert.lean`; here the
checker is proved sound (`checkU_sound`).
-/

namespace PiFormula

/-! ## 1. Huvent's two lines -/

/-- The coordinates of Huvent's first pattern in the eight named series, divided by 256. -/
def huvQ1 : Fin 8 → ℚ := ![2, -2, 0, -2, 0, 0, 1, 0]

/-- The coordinates of Huvent's second pattern in the eight named series, divided by -512. -/
def huvQ2 : Fin 8 → ℚ := ![-2, 2, 0, -2, 0, 0, 1, 0]

theorem namedComb_smul (a : ℚ) (q : Fin 8 → ℚ) : namedComb (a • q) = a • namedComb q := by
  funext k
  simp only [namedComb, Pi.smul_apply, smul_eq_mul]
  ring

theorem rhoHuvent1_eq_smul : rhoHuvent1 = (256 : ℚ) • namedComb huvQ1 := by
  funext k
  rw [rhoHuvent1_eq, ← namedComb_smul]
  congr 1
  funext i
  fin_cases i <;> simp [huvQ1] <;> norm_num

theorem rhoHuvent2_eq_smul : rhoHuvent2 = (-512 : ℚ) • namedComb huvQ2 := by
  funext k
  rw [rhoHuvent2_eq, ← namedComb_smul]
  congr 1
  funext i
  fin_cases i <;> simp [huvQ2] <;> norm_num

/-- Scaling a pattern by a non-zero number does not change its number of non-zero entries. -/
theorem termCount_smul {a : ℚ} (ha : a ≠ 0) (f : ℕ → ℚ) : termCount (a • f) = termCount f := by
  unfold termCount
  congr 1
  funext k
  simp [ha]

/-- The seven conditions of `huvS1` leave the line through Huvent's first pattern. -/
theorem huvS1_line {q : Fin 8 → ℚ} (h : ∀ z ∈ huvS1, clsForm z q = 0) : q = q 6 • huvQ1 := by
  simp only [huvS1, List.mem_cons, List.not_mem_nil, or_false, clsForm, vecZ, vecTab,
    Int.reduceNeg, List.getD_eq_getElem?_getD, Fin.isValue, forall_eq_or_imp, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
    List.getElem_cons_zero, Option.getD_some, Int.cast_one, one_mul, Nat.one_lt_ofNat,
    List.getElem_cons_succ, Nat.reduceLT, Int.cast_ofNat, Nat.lt_add_one, Int.cast_neg, neg_mul,
    Int.cast_zero, zero_mul, add_zero, forall_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  funext c
  fin_cases c <;> simp [huvQ1] <;> linarith

/-- The seven conditions of `huvS2` leave the line through Huvent's second pattern. -/
theorem huvS2_line {q : Fin 8 → ℚ} (h : ∀ z ∈ huvS2, clsForm z q = 0) : q = q 6 • huvQ2 := by
  simp only [huvS2, List.mem_cons, List.not_mem_nil, or_false, clsForm, vecZ, vecTab,
    Int.reduceNeg, List.getD_eq_getElem?_getD, Fin.isValue, forall_eq_or_imp, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
    List.getElem_cons_zero, Option.getD_some, Int.cast_one, one_mul, Nat.one_lt_ofNat,
    List.getElem_cons_succ, Nat.reduceLT, Int.cast_ofNat, Nat.lt_add_one, Int.cast_neg, neg_mul,
    Int.cast_zero, zero_mul, add_zero, forall_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  funext c
  fin_cases c <;> simp [huvQ2] <;> linarith

/-! ## 2. Soundness of the checker -/

/-- **The checker is sound.** If a certificate passes, every pattern of `V` with non-zero
value, whose classes in `Z` vanish and whose classes in `D` do not, has at least 41 non-zero
entries per period, or the seven classes of `huvS1` vanish, or those of `huvS2`. -/
theorem checkU_sound (q : Fin 8 → ℚ) (hV : q 0 + q 2 ≠ 0) : ∀ (c : UCert) (Z D : List ℕ),
    checkU Z D c = true → (∀ z ∈ Z, clsForm z q = 0) → (∀ e ∈ D, clsForm e q ≠ 0) →
    41 ≤ termCount (namedComb q) ∨ (∀ z ∈ huvS1, clsForm z q = 0) ∨
      ∀ z ∈ huvS2, clsForm z q = 0 := by
  intro c
  induction c with
  | done =>
    intro Z D h _ hD
    left
    have h1 : 41 ≤ clsIdxTab.countP fun i => D.contains i := of_decide_eq_true h
    rw [clsIdxTab_eq, List.countP_map] at h1
    refine h1.trans (List.countP_mono_left fun k _ hk => ?_)
    have hmem : clsIdx k ∈ D := List.elem_iff.1 hk
    have hne : namedComb q k ≠ 0 := fun h0 => hD _ hmem ((namedComb_eq_zero_iff q k).1 h0)
    exact decide_eq_true hne
  | huv second =>
    intro Z D h hZ _
    right
    cases second with
    | false => exact Or.inl fun z hz => hZ z (List.elem_iff.1 (List.all_eq_true.1 h z hz))
    | true => exact Or.inr fun z hz => hZ z (List.elem_iff.1 (List.all_eq_true.1 h z hz))
  | derive j tgt d cs rest ih =>
    intro Z D h hZ hD
    simp only [checkU, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hd, htgt⟩, hcs⟩, heq⟩, hrest⟩ := h
    have hd' : (d : ℚ) ≠ 0 := by
      have h0 : d ≠ 0 := by simpa using hd
      exact_mod_cast h0
    have hj : clsForm j q ≠ 0 := by
      intro hj0
      have hsum : (cs.map fun p => (p.2 : ℚ) * clsForm p.1 q).sum = 0 := by
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        have hp1 := List.all_eq_true.1 hcs p hp
        have hp0 : clsForm p.1 q = 0 := by
          rcases Bool.or_eq_true_iff.1 hp1 with h1 | h1
          · rw [eq_of_beq h1]
            exact hj0
          · exact hZ _ (List.elem_iff.1 h1)
        rw [hp0, mul_zero]
      have h2 := certEq_sound heq q
      rw [hsum] at h2
      have h3 : tgtForm tgt q = 0 := by
        rcases mul_eq_zero.1 h2 with h3 | h3
        · exact absurd h3 hd'
        · exact h3
      rcases Bool.or_eq_true_iff.1 htgt with h4 | h4
      · have e : tgt = 35 := eq_of_beq h4
        rw [e, tgtForm_35] at h3
        exact hV h3
      · have hmem : tgt ∈ D := List.elem_iff.1 h4
        by_cases e : tgt = 35
        · rw [e, tgtForm_35] at h3
          exact hV h3
        · rw [tgtForm_of_ne e] at h3
          exact hD _ hmem h3
    refine ih Z (j :: D) hrest hZ fun e he => ?_
    rcases List.mem_cons.1 he with rfl | he
    · exact hj
    · exact hD e he
  | branch i t0 t1 ih0 ih1 =>
    intro Z D h hZ hD
    simp only [checkU, Bool.and_eq_true] at h
    obtain ⟨h0, h1⟩ := h
    by_cases hi : clsForm i q = 0
    · refine ih0 (i :: Z) D h0 (fun z hz => ?_) hD
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hi
      · exact hZ z hz
    · refine ih1 Z (i :: D) h1 hZ fun e he => ?_
      rcases List.mem_cons.1 he with rfl | he
      · exact hi
      · exact hD e he

/-! ## 3. Uniqueness in the space `V` -/

/-- A pattern of `V` with non-zero value has at least 41 non-zero entries per period, or its
coordinates are on one of Huvent's two lines. -/
theorem termCount_namedComb_ge_or (q : Fin 8 → ℚ) (hV : q 0 + q 2 ≠ 0) :
    41 ≤ termCount (namedComb q) ∨ q = q 6 • huvQ1 ∨ q = q 6 • huvQ2 := by
  rcases checkU_sound q hV theUCert [] [] theUCert_ok (fun z hz => by simp at hz)
    (fun e he => by simp at he) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (huvS1_line h))
  · exact Or.inr (Or.inr (huvS2_line h))

/-- A pattern of `V` with non-zero value has exactly 40 non-zero entries per period if and
only if it is a non-zero multiple of Huvent's first or second pattern. -/
theorem termCount_namedComb_eq_forty_iff (q : Fin 8 → ℚ) (hV : q 0 + q 2 ≠ 0) :
    termCount (namedComb q) = 40 ↔
      ∃ a : ℚ, a ≠ 0 ∧ (namedComb q = a • rhoHuvent1 ∨ namedComb q = a • rhoHuvent2) := by
  constructor
  · intro h40
    have h6 : ∀ v : Fin 8 → ℚ, q = q 6 • v → q 6 ≠ 0 := by
      intro v h h6
      rw [h, h6] at hV
      simp at hV
    rcases termCount_namedComb_ge_or q hV with h41 | h | h
    · omega
    · refine ⟨q 6 / 256, div_ne_zero (h6 _ h) (by norm_num), Or.inl ?_⟩
      rw [rhoHuvent1_eq_smul, smul_smul, ← namedComb_smul, div_mul_cancel₀ _ (by norm_num), ← h]
    · refine ⟨q 6 / (-512), div_ne_zero (h6 _ h) (by norm_num), Or.inr ?_⟩
      rw [rhoHuvent2_eq_smul, smul_smul, ← namedComb_smul, div_mul_cancel₀ _ (by norm_num), ← h]
  · rintro ⟨a, ha, h | h⟩
    · rw [h, termCount_smul ha, termCount_rhoHuvent1]
    · rw [h, termCount_smul ha, termCount_rhoHuvent2]

/-! ## 4. The theorem -/

/-- **The optimum 2/3 is attained only by Huvent's two formulas (from Baker's theorem).** A
rational pattern of period `N` (a multiple of 120) whose series `∑ ρ(k) 2^(-⌊k/2⌋)/k` is a
non-zero rational multiple of `π` has exactly 40 non-zero entries per 120 if and only if it
is a non-zero rational multiple of `rhoHuvent1` or of `rhoHuvent2`. -/
theorem termCount_eq_forty_iff (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N)
    {ρ : ℕ → ℚ} (hp : ∀ k, ρ (k + N) = ρ k) {r : ℚ} (hr : r ≠ 0)
    (h : HasSum (seriesTerm ρ) (r * Real.pi)) :
    termCount ρ = 40 ↔ ∃ a : ℚ, a ≠ 0 ∧ (ρ = a • rhoHuvent1 ∨ ρ = a • rhoHuvent2) := by
  obtain ⟨q, rfl⟩ := exists_coords hB hN h120 ⟨hp, r, h⟩
  exact termCount_namedComb_eq_forty_iff q (value_ne_zero hr h)

/-- **Every other formula has at least 41 terms per 120 (from Baker's theorem).** A rational
pattern of period `N` (a multiple of 120) whose series is a non-zero rational multiple of `π`,
and which is not a rational multiple of `rhoHuvent1` or of `rhoHuvent2`, has at least 41
non-zero entries per 120. -/
theorem termCount_ge_forty_one (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N)
    {ρ : ℕ → ℚ} (hp : ∀ k, ρ (k + N) = ρ k) {r : ℚ} (hr : r ≠ 0)
    (h : HasSum (seriesTerm ρ) (r * Real.pi))
    (hne : ∀ a : ℚ, ρ ≠ a • rhoHuvent1 ∧ ρ ≠ a • rhoHuvent2) : 41 ≤ termCount ρ := by
  have h40 := termCount_ge hB hN h120 hp hr h
  have hiff := termCount_eq_forty_iff hB hN h120 hp hr h
  by_contra hlt
  obtain ⟨a, -, ha | ha⟩ := hiff.1 (by omega)
  · exact (hne a).1 ha
  · exact (hne a).2 ha

namespace Unconditional

/-- **The optimum 2/3 is attained only by Huvent's two formulas.** A rational pattern of
period `N` (a multiple of 120) whose series `∑ ρ(k) 2^(-⌊k/2⌋)/k` is a non-zero rational
multiple of `π` has exactly 40 non-zero entries per 120 if and only if it is a non-zero
rational multiple of `rhoHuvent1` or of `rhoHuvent2`. -/
theorem termCount_eq_forty_iff {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N)
    {ρ : ℕ → ℚ} (hp : ∀ k, ρ (k + N) = ρ k) {r : ℚ} (hr : r ≠ 0)
    (h : HasSum (seriesTerm ρ) (r * Real.pi)) :
    termCount ρ = 40 ↔ ∃ a : ℚ, a ≠ 0 ∧ (ρ = a • rhoHuvent1 ∨ ρ = a • rhoHuvent2) :=
  _root_.PiFormula.termCount_eq_forty_iff bakerTheorem hN h120 hp hr h

/-- **Every other formula has at least 41 terms per 120.** A rational pattern of period `N`
(a multiple of 120) whose series is a non-zero rational multiple of `π`, and which is not a
rational multiple of `rhoHuvent1` or of `rhoHuvent2`, has at least 41 non-zero entries per
120. -/
theorem termCount_ge_forty_one {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N)
    {ρ : ℕ → ℚ} (hp : ∀ k, ρ (k + N) = ρ k) {r : ℚ} (hr : r ≠ 0)
    (h : HasSum (seriesTerm ρ) (r * Real.pi))
    (hne : ∀ a : ℚ, ρ ≠ a • rhoHuvent1 ∧ ρ ≠ a • rhoHuvent2) : 41 ≤ termCount ρ :=
  _root_.PiFormula.termCount_ge_forty_one bakerTheorem hN h120 hp hr h hne

end Unconditional

end PiFormula
