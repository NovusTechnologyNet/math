/-! ## 3. Thirteen independent patterns -/

/-- The thirteen patterns: the eight named ones and the five of `FiveSeries.lean`. -/
def fam13 : Fin 8 ⊕ Fin 5 → ℕ → ℚ :=
  Sum.elim ![namedA1, namedA6, namedA10, namedL6, namedL8, namedL10, namedL24, namedTW]
    ![extraS3, extraS2, extraS5, extraT1, extraT2]

theorem sum_fam13 (g : Fin 8 ⊕ Fin 5 → ℚ) (k : ℕ) :
    (∑ i, g i • fam13 i) k = comb13 (fun i => g (Sum.inl i)) (fun j => g (Sum.inr j)) k := by
  simp only [Fintype.sum_sum_type, fam13, Sum.elim_inl, Sum.elim_inr, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight, Fin.sum_univ_five, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, comb13]
  ring

/-- **The thirteen patterns are linearly independent over `ℚ`** (no Baker's theorem). -/
theorem fam13_linearIndependent : LinearIndependent ℚ fam13 := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h : ∀ k, comb13 (fun i => g (Sum.inl i)) (fun j => g (Sum.inr j)) k = 0 := by
    intro k
    rw [← sum_fam13, hg]
    rfl
  obtain ⟨hq, hp⟩ := comb13_eq_zero _ _ h
  rintro (i | j)
  · exact hq i
  · exact hp j

theorem fam13_mem {N : ℕ} (hN : 120 ∣ N) : ∀ i, fam13 i ∈ algSpace N := by
  rintro (i | j)
  · have h := ratSpace_le_algSpace N (namedFam hN i).2
    have e : ((namedFam hN i : ratSpace N) : ℕ → ℚ) = fam13 (Sum.inl i) := by
      fin_cases i <;> rfl
    rw [← e]
    exact h
  · fin_cases j
    · exact extraS3_mem hN
    · exact extraS2_mem hN
    · exact extraS5_mem hN
    · exact extraT1_mem hN
    · exact extraT2_mem hN

/-- The thirteen patterns, as elements of `algSpace N`. -/
noncomputable def algFam {N : ℕ} (hN : 120 ∣ N) : Fin 8 ⊕ Fin 5 → algSpace N :=
  fun i => ⟨fam13 i, fam13_mem hN i⟩

theorem algFam_linearIndependent {N : ℕ} (hN : 120 ∣ N) :
    LinearIndependent ℚ (algFam hN) := by
  refine LinearIndependent.of_comp (algSpace N).subtype ?_
  have e : (algSpace N).subtype ∘ algFam hN = fam13 := rfl
  rw [e]
  exact fam13_linearIndependent

/-! ## 4. Dimension exactly 13 -/

/-- **Dimension exactly 13 (from Baker's theorem).** For every `N` divisible by 120, the
rational patterns of period `N` whose series `∑ ρ(k) 2^(-⌊k/2⌋)/k` is an algebraic multiple
of `π` form a space of dimension 13. -/
theorem finrank_algSpace (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) :
    Module.finrank ℚ (algSpace N) = 13 := by
  have h8 : 8 ∣ N := Dvd.dvd.trans (by norm_num) h120
  have hfin := finite_algSpace hB hN h8
  refine le_antisymm (finrank_algSpace_le hB hN h8) ?_
  have h := (algFam_linearIndependent h120).fintype_card_le_finrank
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  exact h

/-- **The thirteen patterns span (from Baker's theorem).** -/
theorem span_algFam (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) :
    Submodule.span ℚ (Set.range (algFam h120)) = ⊤ := by
  have h8 : 8 ∣ N := Dvd.dvd.trans (by norm_num) h120
  have hfin := finite_algSpace hB hN h8
  exact (algFam_linearIndependent h120).span_eq_top_of_card_eq_finrank'
    (by rw [finrank_algSpace hB hN h120, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin])

/-- **Coordinates (from Baker's theorem).** Every rational pattern of period `N` (a multiple
of 120) whose series is an algebraic multiple of `π` is a combination of the thirteen
patterns. -/
theorem exists_coords13 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N)
    {ρ : ℕ → ℚ} (hρ : ρ ∈ algSpace N) :
    ∃ (q : Fin 8 → ℚ) (p : Fin 5 → ℚ), ρ = comb13 q p := by
  have hmem : (⟨ρ, hρ⟩ : algSpace N) ∈ Submodule.span ℚ (Set.range (algFam h120)) := by
    rw [span_algFam hB hN h120]
    exact Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hmem
  refine ⟨fun i => g (Sum.inl i), fun j => g (Sum.inr j), ?_⟩
  have h1 := congrArg (algSpace N).subtype hg
  rw [map_sum] at h1
  simp only [map_smul] at h1
  have h2 : ∑ i, g i • fam13 i = ρ := h1
  funext k
  rw [← sum_fam13, h2]

/-- **Theorem C (from Baker's theorem).** Let `N` be a multiple of 120. Among the rational
patterns `ρ` of period `N`:
* those whose series `∑ ρ(k) 2^(-⌊k/2⌋)/k` is an algebraic multiple of `π` have period 120
  and form a space of dimension exactly 13;
* those whose series is a rational multiple of `π` form a subspace of dimension exactly 8. -/
theorem theoremC (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) :
    (∀ ρ ∈ algSpace N, ∀ k, ρ (k + 120) = ρ k) ∧
      Module.finrank ℚ (algSpace N) = 13 ∧ Module.finrank ℚ (ratSpace N) = 8 :=
  ⟨fun _ hρ k => period_120 hB hN (Dvd.dvd.trans (by norm_num) h120) hρ k,
    finrank_algSpace hB hN h120, finrank_ratSpace hB hN h120⟩

end PiFormula
