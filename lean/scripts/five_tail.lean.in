/-! ## 4. The five patterns and their values -/

theorem garg_105 : garg 105 = -garg 45 := garg_partner (j := 45) (k := 105) (Or.inr rfl)

theorem garg_25 : garg 25 = -garg 5 := garg_partner (j := 5) (k := 25) (Or.inl rfl)

theorem garg_85 : garg 85 = -garg 65 := garg_partner (j := 65) (k := 85) (Or.inr rfl)

theorem garg_18 : garg 18 = -garg 12 := garg_partner (j := 12) (k := 18) (Or.inl rfl)

theorem garg_42 : garg 42 = -garg 108 := garg_partner (j := 108) (k := 42) (Or.inr rfl)

theorem garg_66 : garg 66 = -garg 84 := garg_partner (j := 84) (k := 66) (Or.inr rfl)

theorem garg_114 : garg 114 = -garg 36 := garg_partner (j := 36) (k := 114) (Or.inr rfl)

/-- The `√3`-twisted pattern (roots of order 6). -/
def extraS3 : ℕ → ℚ := rhoA PS3Z

/-- The `√2`-twisted pattern (roots of order 8 and 24). -/
def extraS2 : ℕ → ℚ := rhoA PS2Z

/-- The `√5`-twisted pattern (roots of order 10 and 20). -/
def extraS5 : ℕ → ℚ := rhoA PS5Z

/-- The first pattern twisted by `2cos(π/10)` and `2cos(3π/10)`. -/
def extraT1 : ℕ → ℚ := rhoA PT1Z

/-- The second pattern twisted by `2cos(π/10)` and `2cos(3π/10)`. -/
def extraT2 : ℕ → ℚ := rhoA PT2Z

/-- **The `√3`-twisted series**: `√3 (arg w_{ζ_6} - arg w_{ζ_6^5}) = -π/√3`. -/
theorem hasSum_extraS3 : HasSum (seriesTerm extraS3) (-(Real.sqrt 3 / 3) * Real.pi) := by
  have h := hasSum_rhoA_of_lsum (L := LS3) (P := PS3Z) (fun k => by rw [lsum_LS3, psS3_eq])
  have e : lval LS3 = -(Real.sqrt 3 / 3) * Real.pi := by
    simp only [lval, LS3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, garg_20,
      garg_100]
    ring
  rw [e] at h
  exact h

/-- **The `√2`-twisted series**: value `-√2 π`. -/
theorem hasSum_extraS2 : HasSum (seriesTerm extraS2) (-Real.sqrt 2 * Real.pi) := by
  have h := hasSum_rhoA_of_lsum (L := LS2) (P := PS2Z) (fun k => by rw [lsum_LS2, psS2_eq])
  have e : lval LS2 = -Real.sqrt 2 * Real.pi := by
    simp only [lval, LS2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, garg_105,
      garg_25, garg_85, garg_65, garg_45]
    ring
  rw [e] at h
  exact h

/-- **The `√5`-twisted series**: value `-√5 π`. -/
theorem hasSum_extraS5 : HasSum (seriesTerm extraS5) (-Real.sqrt 5 * Real.pi) := by
  have h := hasSum_rhoA_of_lsum (L := LS5) (P := PS5Z) (fun k => by rw [lsum_LS5, psS5_eq])
  have e : lval LS5 = -Real.sqrt 5 * Real.pi := by
    simp only [lval, LS5, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, garg_18,
      garg_42, garg_66, garg_114, garg_12, garg_108, garg_84, garg_36]
    ring
  rw [e] at h
  exact h

/-- **The first `θ`-twisted series**: value `(θ₁ - 3θ₃) π/5`. -/
theorem hasSum_extraT1 : HasSum (seriesTerm extraT1) ((th1 - 3 * th3) / 5 * Real.pi) := by
  have h := hasSum_rhoA_of_lsum (L := LT1) (P := PT1Z) (fun k => by rw [lsum_LT1, psT1_eq])
  have e : lval LT1 = (th1 - 3 * th3) / 5 * Real.pi := by
    simp only [lval, LT1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, garg_18,
      garg_42, garg_66, garg_114, garg_12, garg_108, garg_84, garg_36]
    ring
  rw [e] at h
  exact h

/-- **The second `θ`-twisted series**: value `(3θ₁ + θ₃) π/5`. -/
theorem hasSum_extraT2 : HasSum (seriesTerm extraT2) ((3 * th1 + th3) / 5 * Real.pi) := by
  have h := hasSum_rhoA_of_lsum (L := LT2) (P := PT2Z) (fun k => by rw [lsum_LT2, psT2_eq])
  have e : lval LT2 = (3 * th1 + th3) / 5 * Real.pi := by
    simp only [lval, LT2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, garg_18,
      garg_42, garg_66, garg_114, garg_12, garg_108, garg_84, garg_36]
    ring
  rw [e] at h
  exact h

theorem extra_periodic (k : ℕ) :
    extraS3 (k + 120) = extraS3 k ∧ extraS2 (k + 120) = extraS2 k ∧
      extraS5 (k + 120) = extraS5 k ∧ extraT1 (k + 120) = extraT1 k ∧
      extraT2 (k + 120) = extraT2 k := by
  have e24 : ∀ k, (k + 120) % 24 = k % 24 := fun k => by omega
  have e20 : ∀ k, (k + 120) % 20 = k % 20 := fun k => by omega
  exact ⟨rhoA_add_120 (fun k => by simp only [PS3Z, e24]) k,
    rhoA_add_120 (fun k => by simp only [PS2Z, e24]) k,
    rhoA_add_120 (fun k => by simp only [PS5Z, e20]) k,
    rhoA_add_120 (fun k => by simp only [PT1Z, e20]) k,
    rhoA_add_120 (fun k => by simp only [PT2Z, e20]) k⟩

/-! ## 5. The values are algebraic multiples of `π` -/

theorem isAlgebraic_of_ofReal {x : ℝ} (h : IsAlgebraic ℚ (x : ℂ)) : IsAlgebraic ℚ x :=
  (isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective).1 h

theorem isAlgebraic_ζ120_pow (j : ℕ) : IsAlgebraic ℚ (ζ120 ^ j) :=
  isAlgebraic_root (isOfFinOrder_ζ120_pow j)

theorem isAlgebraic_z24_pow (a : ℕ) : IsAlgebraic ℚ (z24 ^ a) := by
  rw [z24, ← pow_mul]
  exact isAlgebraic_ζ120_pow _

theorem isAlgebraic_z20_pow (a : ℕ) : IsAlgebraic ℚ (z20 ^ a) := by
  rw [z20, ← pow_mul]
  exact isAlgebraic_ζ120_pow _

theorem isAlgebraic_sqrt3 : IsAlgebraic ℚ (Real.sqrt 3) := by
  refine isAlgebraic_of_ofReal ?_
  rw [sqrt3_eq]
  exact (isAlgebraic_z24_pow 2).sub (isAlgebraic_z24_pow 10)

theorem isAlgebraic_sqrt2 : IsAlgebraic ℚ (Real.sqrt 2) := by
  refine isAlgebraic_of_ofReal ?_
  rw [sqrt2_eq]
  exact (isAlgebraic_z24_pow 3).add (isAlgebraic_z24_pow 21)

theorem isAlgebraic_sqrt5 : IsAlgebraic ℚ (Real.sqrt 5) := by
  refine isAlgebraic_of_ofReal ?_
  rw [sqrt5_eq]
  exact (((isAlgebraic_z20_pow 4).sub (isAlgebraic_z20_pow 8)).sub
    (isAlgebraic_z20_pow 12)).add (isAlgebraic_z20_pow 16)

theorem isAlgebraic_th1 : IsAlgebraic ℚ th1 := by
  refine isAlgebraic_of_ofReal ?_
  rw [th1_eq]
  have h := (isAlgebraic_z20_pow 1).add (isAlgebraic_z20_pow 19)
  rwa [pow_one] at h

theorem isAlgebraic_th3 : IsAlgebraic ℚ th3 := by
  refine isAlgebraic_of_ofReal ?_
  rw [th3_eq]
  exact (isAlgebraic_z20_pow 3).add (isAlgebraic_z20_pow 17)

theorem isAlgebraic_rat_mul (q : ℚ) {x : ℝ} (h : IsAlgebraic ℚ x) :
    IsAlgebraic ℚ ((q : ℝ) * x) :=
  (isAlgebraic_ratCast ℚ (A := ℝ) q).mul h

theorem mem_algSpace_of {f : ℕ → ℚ} (hp : ∀ k, f (k + 120) = f k) {γ : ℝ}
    (hγ : IsAlgebraic ℚ γ) (h : HasSum (seriesTerm f) (γ * Real.pi)) {N : ℕ} (hN : 120 ∣ N) :
    f ∈ algSpace N :=
  ⟨periodic_of_dvd hp hN, γ, hγ, h⟩

theorem extraS3_mem {N : ℕ} (hN : 120 ∣ N) : extraS3 ∈ algSpace N := by
  refine mem_algSpace_of (fun k => (extra_periodic k).1) (γ := -(Real.sqrt 3 / 3)) ?_
    hasSum_extraS3 hN
  have h := isAlgebraic_rat_mul (-1 / 3) isAlgebraic_sqrt3
  convert h using 1
  push_cast
  ring

theorem extraS2_mem {N : ℕ} (hN : 120 ∣ N) : extraS2 ∈ algSpace N := by
  refine mem_algSpace_of (fun k => (extra_periodic k).2.1) (γ := -Real.sqrt 2) ?_
    hasSum_extraS2 hN
  have h := isAlgebraic_rat_mul (-1) isAlgebraic_sqrt2
  convert h using 1
  push_cast
  ring

theorem extraS5_mem {N : ℕ} (hN : 120 ∣ N) : extraS5 ∈ algSpace N := by
  refine mem_algSpace_of (fun k => (extra_periodic k).2.2.1) (γ := -Real.sqrt 5) ?_
    hasSum_extraS5 hN
  have h := isAlgebraic_rat_mul (-1) isAlgebraic_sqrt5
  convert h using 1
  push_cast
  ring

theorem extraT1_mem {N : ℕ} (hN : 120 ∣ N) : extraT1 ∈ algSpace N := by
  refine mem_algSpace_of (fun k => (extra_periodic k).2.2.2.1) (γ := (th1 - 3 * th3) / 5) ?_
    hasSum_extraT1 hN
  have h := (isAlgebraic_rat_mul (1 / 5) isAlgebraic_th1).add
    (isAlgebraic_rat_mul (-3 / 5) isAlgebraic_th3)
  convert h using 1
  push_cast
  ring

theorem extraT2_mem {N : ℕ} (hN : 120 ∣ N) : extraT2 ∈ algSpace N := by
  refine mem_algSpace_of (fun k => (extra_periodic k).2.2.2.2) (γ := (3 * th1 + th3) / 5) ?_
    hasSum_extraT2 hN
  have h := (isAlgebraic_rat_mul (3 / 5) isAlgebraic_th1).add
    (isAlgebraic_rat_mul (1 / 5) isAlgebraic_th3)
  convert h using 1
  push_cast
  ring

end PiFormula
