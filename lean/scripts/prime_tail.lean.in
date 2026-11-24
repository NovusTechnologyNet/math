/-! ## 3. The bound 7/24 -/

/-- Along each of the four chains a term is non-zero within the first eight positions. -/
theorem chain_bounds (q : Fin 8 → ℚ) (hV : q 0 + q 2 ≠ 0) :
    (1 / 8 : ℚ) ≤ 1 / (firstNZ (namedComb q) 1 : ℚ) ∧
      (1 / 8 : ℚ) ≤ 1 / (firstNZ (namedComb q) 7 : ℚ) ∧
      (1 / 8 : ℚ) ≤ 1 / (firstNZ (namedComb q) 11 : ℚ) ∧
      (1 / 8 : ℚ) ≤ 1 / (firstNZ (namedComb q) 17 : ℚ) := by
  have key : ∀ c : ℕ, (¬ ∀ t, 1 ≤ t → t ≤ 8 → namedComb q (t * c) = 0) →
      (1 / 8 : ℚ) ≤ 1 / (firstNZ (namedComb q) c : ℚ) := by
    intro c h
    push Not at h
    obtain ⟨t, h1, h8, hnz⟩ := h
    exact inv_firstNZ_ge 8 h1 h8 (by norm_num) hnz (by norm_num)
  refine ⟨key 1 fun h => ?_, key 7 fun h => ?_, key 11 fun h => ?_, key 17 fun h => ?_⟩
  · exact hV (blk1 q (h 1 (by norm_num) (by norm_num)) (h 2 (by norm_num) (by norm_num))
      (h 3 (by norm_num) (by norm_num)) (h 4 (by norm_num) (by norm_num))
      (h 5 (by norm_num) (by norm_num)) (h 6 (by norm_num) (by norm_num))
      (h 7 (by norm_num) (by norm_num)) (h 8 (by norm_num) (by norm_num)))
  · exact hV (blk7 q (h 1 (by norm_num) (by norm_num)) (h 2 (by norm_num) (by norm_num))
      (h 3 (by norm_num) (by norm_num)) (h 4 (by norm_num) (by norm_num))
      (h 5 (by norm_num) (by norm_num)) (h 6 (by norm_num) (by norm_num))
      (h 7 (by norm_num) (by norm_num)) (h 8 (by norm_num) (by norm_num)))
  · exact hV (blk11 q (h 1 (by norm_num) (by norm_num)) (h 2 (by norm_num) (by norm_num))
      (h 3 (by norm_num) (by norm_num)) (h 4 (by norm_num) (by norm_num))
      (h 5 (by norm_num) (by norm_num)) (h 6 (by norm_num) (by norm_num))
      (h 7 (by norm_num) (by norm_num)) (h 8 (by norm_num) (by norm_num)))
  · exact hV (blk17 q (h 1 (by norm_num) (by norm_num)) (h 2 (by norm_num) (by norm_num))
      (h 3 (by norm_num) (by norm_num)) (h 4 (by norm_num) (by norm_num))
      (h 5 (by norm_num) (by norm_num)) (h 6 (by norm_num) (by norm_num))
      (h 7 (by norm_num) (by norm_num)) (h 8 (by norm_num) (by norm_num)))

/-- **The 13-case tree.** For a pattern of `V` with non-zero value, the four numbers `1/s`
add up to at least `7/6`. -/
theorem prime_sum_ge (q : Fin 8 → ℚ) (hV : q 0 + q 2 ≠ 0) :
    (7 / 6 : ℚ) ≤ 1 / (firstNZ (namedComb q) 1 : ℚ) + 1 / (firstNZ (namedComb q) 7 : ℚ)
      + 1 / (firstNZ (namedComb q) 11 : ℚ) + 1 / (firstNZ (namedComb q) 17 : ℚ) := by
  obtain ⟨b1, b7, b11, b17⟩ := chain_bounds q hV
  have p1 : (0 : ℚ) ≤ 1 / (firstNZ (namedComb q) 1 : ℚ) := by positivity
  have p7 : (0 : ℚ) ≤ 1 / (firstNZ (namedComb q) 7 : ℚ) := by positivity
  have p11 : (0 : ℚ) ≤ 1 / (firstNZ (namedComb q) 11 : ℚ) := by positivity
  have p17 : (0 : ℚ) ≤ 1 / (firstNZ (namedComb q) 17 : ℚ) := by positivity
  -- a term at a unit of type 17, 11 or 7
  by_cases h17 : namedComb q 17 = 0
  swap
  · have a := inv_firstNZ_ge (ρ := namedComb q) (c := 17) (t := 1) 1 le_rfl le_rfl
      (by norm_num) h17 (b := 1) (by norm_num)
    linarith
  by_cases h11 : namedComb q 11 = 0
  swap
  · have a := inv_firstNZ_ge (ρ := namedComb q) (c := 11) (t := 1) 1 le_rfl le_rfl
      (by norm_num) h11 (b := 1) (by norm_num)
    linarith
  by_cases h7 : namedComb q 7 = 0
  swap
  · have a := inv_firstNZ_ge (ρ := namedComb q) (c := 7) (t := 1) 1 le_rfl le_rfl
      (by norm_num) h7 (b := 1) (by norm_num)
    linarith
  -- no term at any unit
  have h1 : namedComb q 1 = 0 := fc1 q h7 h11 h17
  by_cases h34 : namedComb q 34 = 0
  swap
  · have a17 := inv_firstNZ_ge (ρ := namedComb q) (c := 17) (t := 2) 2 (by norm_num) le_rfl
      (by norm_num) h34 (b := 1 / 2) (by norm_num)
    have h2 : namedComb q 2 ≠ 0 := fun h2 => h34 (fc2 q h1 h7 h11 h17 h2)
    have a1 := inv_firstNZ_ge (ρ := namedComb q) (c := 1) (t := 2) 2 (by norm_num) le_rfl
      (by norm_num) h2 (b := 1 / 2) (by norm_num)
    linarith
  have h2 : namedComb q 2 = 0 := fc3 q h1 h7 h11 h17 h34
  by_cases h22 : namedComb q 22 = 0
  swap
  · have a11 := inv_firstNZ_ge (ρ := namedComb q) (c := 11) (t := 2) 2 (by norm_num) le_rfl
      (by norm_num) h22 (b := 1 / 2) (by norm_num)
    have h14 : namedComb q 14 ≠ 0 := fun h14 => h22 (fc4 q h1 h7 h11 h17 h2 h34 h14)
    have a7 := inv_firstNZ_ge (ρ := namedComb q) (c := 7) (t := 2) 2 (by norm_num) le_rfl
      (by norm_num) h14 (b := 1 / 2) (by norm_num)
    linarith
  -- no term at gcd(k, 120) ≤ 2
  have h14 : namedComb q 14 = 0 := fc5 q h1 h7 h11 h17 h2 h34 h22
  by_cases h21 : namedComb q 21 = 0
  swap
  · -- terms at 3·7 and 3·11: two classes of type 1/3, two of type at least 1/4
    have a7 := inv_firstNZ_ge (ρ := namedComb q) (c := 7) (t := 3) 3 (by norm_num) le_rfl
      (by norm_num) h21 (b := 1 / 3) (by norm_num)
    have h33 : namedComb q 33 ≠ 0 := fun h33 => h21 (fe1 q h33)
    have a11 := inv_firstNZ_ge (ρ := namedComb q) (c := 11) (t := 3) 3 (by norm_num) le_rfl
      (by norm_num) h33 (b := 1 / 3) (by norm_num)
    have a1 : (1 / 4 : ℚ) ≤ 1 / (firstNZ (namedComb q) 1 : ℚ) := by
      by_cases h3 : namedComb q 3 = 0
      · have h4 : namedComb q 4 ≠ 0 := fun h4 =>
          hV (ff1 q h1 h7 h11 h17 h2 h34 h22 h14 h3 h4)
        exact inv_firstNZ_ge (ρ := namedComb q) (c := 1) (t := 4) 4 (by norm_num) le_rfl
          (by norm_num) h4 (by norm_num)
      · exact inv_firstNZ_ge (ρ := namedComb q) (c := 1) (t := 3) 4 (by norm_num)
          (by norm_num) (by norm_num) h3 (by norm_num)
    have a17 : (1 / 4 : ℚ) ≤ 1 / (firstNZ (namedComb q) 17 : ℚ) := by
      by_cases h51 : namedComb q 51 = 0
      · have h68 : namedComb q 68 ≠ 0 := fun h68 =>
          hV (ff2 q h1 h7 h11 h17 h2 h34 h22 h14 h51 h68)
        exact inv_firstNZ_ge (ρ := namedComb q) (c := 17) (t := 4) 4 (by norm_num) le_rfl
          (by norm_num) h68 (by norm_num)
      · exact inv_firstNZ_ge (ρ := namedComb q) (c := 17) (t := 3) 4 (by norm_num)
          (by norm_num) (by norm_num) h51 (by norm_num)
    linarith
  · -- no term at 3·7 or 3·11: two classes of type 1/4, two of type 1/3
    have h33 : namedComb q 33 = 0 := fe2 q h21
    have h28 : namedComb q 28 ≠ 0 := fun h28 =>
      hV (fg1 q h1 h7 h11 h17 h2 h34 h22 h14 h21 h28)
    have a7 := inv_firstNZ_ge (ρ := namedComb q) (c := 7) (t := 4) 4 (by norm_num) le_rfl
      (by norm_num) h28 (b := 1 / 4) (by norm_num)
    have h44 : namedComb q 44 ≠ 0 := fun h44 =>
      hV (fg2 q h1 h7 h11 h17 h2 h34 h22 h14 h33 h44)
    have a11 := inv_firstNZ_ge (ρ := namedComb q) (c := 11) (t := 4) 4 (by norm_num) le_rfl
      (by norm_num) h44 (b := 1 / 4) (by norm_num)
    have h3 : namedComb q 3 ≠ 0 := fun h3 =>
      hV (fg3 q h1 h7 h11 h17 h2 h34 h22 h14 h21 h3)
    have a1 := inv_firstNZ_ge (ρ := namedComb q) (c := 1) (t := 3) 3 (by norm_num) le_rfl
      (by norm_num) h3 (b := 1 / 3) (by norm_num)
    have h51 : namedComb q 51 ≠ 0 := fun h51 =>
      hV (fg4 q h1 h7 h11 h17 h2 h34 h22 h14 h21 h51)
    have a17 := inv_firstNZ_ge (ρ := namedComb q) (c := 17) (t := 3) 3 (by norm_num) le_rfl
      (by norm_num) h51 (b := 1 / 3) (by norm_num)
    linarith

/-- **Theorem E, prime measure (from Baker's theorem).** Let `ρ` be a rational pattern of
period `N` (a multiple of 120) whose series `∑ ρ(k) 2^(-⌊k/2⌋)/k` is a non-zero rational
multiple of `π`. Then the mean of `1/s` over the 32 classes of primes modulo 120 is at least
`7/24`. -/
theorem primeCost_ge (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) {ρ : ℕ → ℚ}
    (hp : ∀ k, ρ (k + N) = ρ k) {r : ℚ} (hr : r ≠ 0)
    (h : HasSum (seriesTerm ρ) (r * Real.pi)) : 7 / 24 ≤ primeCost ρ := by
  obtain ⟨q, rfl⟩ := exists_coords hB hN h120 ⟨hp, r, h⟩
  have hV : q 0 + q 2 ≠ 0 := value_ne_zero hr h
  rw [primeCost_namedComb]
  have h4 := prime_sum_ge q hV
  linarith

/-- **The new formula attains the optimum**: its mean of `1/s` is exactly `7/24`. -/
theorem primeCost_rhoNew : primeCost rhoNew = 7 / 24 := by decide +kernel

end PiFormula
