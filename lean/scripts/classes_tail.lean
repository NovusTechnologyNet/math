/-! ## 2. Classes -/

/-- The class of the condition `ρ(k) = 0`. -/
def clsIdx (k : ℕ) : ℕ := clsIdxTab.getD (k % 120) 35

/-- The factor of `k`. -/
def mu (k : ℕ) : ℚ := muTab.getD (k % 120) 0

/-- The `t`-th coordinate of the vector of class `i`. -/
def vecZ (i t : ℕ) : ℤ := (vecTab.getD i []).getD t 0

/-- The linear form of class `i`. -/
def clsForm (i : ℕ) (q : Fin 8 → ℚ) : ℚ :=
  (vecZ i 0 : ℚ) * q 0 + vecZ i 1 * q 1 + vecZ i 2 * q 2 + vecZ i 3 * q 3 + vecZ i 4 * q 4
    + vecZ i 5 * q 5 + vecZ i 6 * q 6 + vecZ i 7 * q 7

/-- **The class table.** At every `k < 120` the values of the eight named patterns are `mu k`
times the vector of the class of `k`. -/
theorem class_table : ∀ k < 120,
    namedA1 k = mu k * (vecZ (clsIdx k) 0 : ℚ) ∧ namedA6 k = mu k * (vecZ (clsIdx k) 1 : ℚ) ∧
      namedA10 k = mu k * (vecZ (clsIdx k) 2 : ℚ) ∧ namedL6 k = mu k * (vecZ (clsIdx k) 3 : ℚ) ∧
      namedL8 k = mu k * (vecZ (clsIdx k) 4 : ℚ) ∧ namedL10 k = mu k * (vecZ (clsIdx k) 5 : ℚ) ∧
      namedL24 k = mu k * (vecZ (clsIdx k) 6 : ℚ) ∧ namedTW k = mu k * (vecZ (clsIdx k) 7 : ℚ) := by
  decide +kernel

theorem mu_ne_zero : ∀ k < 120, k ≠ 0 → mu k ≠ 0 := by decide +kernel

theorem namedComb_periodic (q : Fin 8 → ℚ) (k : ℕ) :
    namedComb q (k + 120) = namedComb q k := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := named_periodic k
  simp only [namedComb, h1, h2, h3, h4, h5, h6, h7, h8]

/-- The value at `k` is a non-zero multiple of the form of the class of `k`. -/
theorem namedComb_class (q : Fin 8 → ℚ) (k : ℕ) :
    namedComb q k = mu k * clsForm (clsIdx k) q := by
  have hk : k % 120 < 120 := Nat.mod_lt _ (by norm_num)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := class_table (k % 120) hk
  have e1 : mu (k % 120) = mu k := by simp only [mu, Nat.mod_mod]
  have e2 : clsIdx (k % 120) = clsIdx k := by simp only [clsIdx, Nat.mod_mod]
  rw [← mod_120 (namedComb_periodic q) k]
  simp only [namedComb, clsForm, h1, h2, h3, h4, h5, h6, h7, h8, e1, e2]
  ring

theorem clsForm_35 (q : Fin 8 → ℚ) : clsForm 35 q = 0 := by
  have h : vecZ 35 0 = 0 ∧ vecZ 35 1 = 0 ∧ vecZ 35 2 = 0 ∧ vecZ 35 3 = 0 ∧ vecZ 35 4 = 0 ∧
      vecZ 35 5 = 0 ∧ vecZ 35 6 = 0 ∧ vecZ 35 7 = 0 := by decide
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [clsForm, h0, h1, h2, h3, h4, h5, h6, h7, Int.cast_zero, zero_mul, add_zero]

/-- **`ρ(k) = 0` exactly when the form of the class of `k` vanishes.** -/
theorem namedComb_eq_zero_iff (q : Fin 8 → ℚ) (k : ℕ) :
    namedComb q k = 0 ↔ clsForm (clsIdx k) q = 0 := by
  rw [namedComb_class]
  by_cases hk : k % 120 = 0
  · have e : clsIdx k = 35 := by
      simp only [clsIdx, hk]
      decide
    rw [e, clsForm_35, mul_zero]
  · have hmu : mu k ≠ 0 := by
      have h := mu_ne_zero (k % 120) (Nat.mod_lt _ (by norm_num)) hk
      have e1 : mu (k % 120) = mu k := by simp only [mu, Nat.mod_mod]
      rwa [e1] at h
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h hmu
      · exact h
    · intro h
      rw [h, mul_zero]

/-! ## 3. The four types of units -/

/-- The 32 units modulo 120. -/
def unitsList : List ℕ := (List.range 120).filter fun c => Nat.gcd c 120 == 1

/-- The type of a unit: one of `1, 7, 11, 17`, by `c mod 12`. -/
def typeRep (c : ℕ) : ℕ :=
  if c % 12 = 1 then 1 else if c % 12 = 7 then 7 else if c % 12 = 11 then 11 else 17

theorem unitsList_typeRep : unitsList.map typeRep = unitTypes := by decide +kernel

/-- **The type table.** For a unit `c`, the conditions along `c, 2c, 3c, ...` are those along
`c₀, 2c₀, 3c₀, ...` for its type `c₀`. -/
theorem type_table : ∀ c < 120, Nat.gcd c 120 = 1 → ∀ s < 121,
    clsIdx (s * c) = clsIdx (s * typeRep c) := by decide +kernel

theorem mem_unitsList {c : ℕ} (hc : c ∈ unitsList) : c < 120 ∧ Nat.gcd c 120 = 1 := by
  simp only [unitsList, List.mem_filter, List.mem_range, beq_iff_eq] at hc
  exact hc

/-- For a unit `c` and `s ≤ 120`, `ρ(s c) = 0` exactly when `ρ(s c₀) = 0`. -/
theorem namedComb_type (q : Fin 8 → ℚ) {c : ℕ} (hc : c ∈ unitsList) {s : ℕ} (hs : s ≤ 120) :
    namedComb q (s * c) = 0 ↔ namedComb q (s * typeRep c) = 0 := by
  obtain ⟨h1, h2⟩ := mem_unitsList hc
  rw [namedComb_eq_zero_iff, namedComb_eq_zero_iff, type_table c h1 h2 s (by omega)]

/-- A pattern of `V` whose series is a non-zero rational multiple of `π` has `q 0 + q 2 ≠ 0`. -/
theorem value_ne_zero {q : Fin 8 → ℚ} {r : ℚ} (hr : r ≠ 0)
    (h : HasSum (seriesTerm (namedComb q)) (r * Real.pi)) : q 0 + q 2 ≠ 0 := by
  intro h0
  have h1 := hasSum_namedComb q
  rw [h0, Rat.cast_zero, zero_mul] at h1
  have h2 := h.unique h1
  have hpi := Real.pi_pos
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact hr (by exact_mod_cast h3)
  · linarith

end PiFormula
