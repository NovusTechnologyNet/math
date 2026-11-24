/-! ## 4. Theorem D -/

/-- **Theorem D, for rational multiples of `π` (from Baker's theorem).** Let `ρ` be a rational
pattern of period `N` (a multiple of 120) whose series `∑ ρ(k) 2^(-⌊k/2⌋)/k` is a rational
multiple of `π`. If all its terms sit at `k` with `gcd(k, 120) ≥ 4`, the value is 0. -/
theorem theoremD (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ρ ∈ ratSpace N) (hsupp : ∀ k, Nat.gcd k 120 < 4 → ρ k = 0) :
    HasSum (seriesTerm ρ) 0 := by
  obtain ⟨q, rfl⟩ := exists_coords hB hN h120 hρ
  have hq := coords_D q hsupp
  have h := hasSum_namedComb q
  rw [hq, Rat.cast_zero, zero_mul] at h
  exact h

/-- The value of a combination, read off from six of its terms. -/
theorem coords_value (q : Fin 8 → ℚ) :
    q 0 + q 2 = 7 / 12 * namedComb q 1 + 1 / 8 * namedComb q 2 + 1 / 6 * namedComb q 3
      - 7 / 12 * namedComb q 7 + 1 / 6 * namedComb q 9 - 1 / 8 * namedComb q 14 := by
  rw [namedComb_at_1, namedComb_at_2, namedComb_at_3, namedComb_at_7, namedComb_at_9,
    namedComb_at_14]
  ring

/-- **The value formula (from Baker's theorem).** If the series of a rational pattern `ρ`
(of period a multiple of 120) is a rational multiple of `π`, that multiple is read off from
six terms:
`∑ ρ(k) 2^(-⌊k/2⌋)/k = (7ρ(1)/12 + ρ(2)/8 + ρ(3)/6 - 7ρ(7)/12 + ρ(9)/6 - ρ(14)/8) · π/4`.
All six positions have `gcd(k, 120) ≤ 3`, so Theorem D follows at once. -/
theorem value_formula (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ρ ∈ ratSpace N) :
    HasSum (seriesTerm ρ)
      (((7 / 12 * ρ 1 + 1 / 8 * ρ 2 + 1 / 6 * ρ 3 - 7 / 12 * ρ 7 + 1 / 6 * ρ 9
        - 1 / 8 * ρ 14 : ℚ) : ℝ) * (Real.pi / 4)) := by
  obtain ⟨q, rfl⟩ := exists_coords hB hN h120 hρ
  rw [← coords_value q]
  exact hasSum_namedComb q

/-- Theorem D in contrapositive form: a formula for a non-zero rational multiple of `π` has a
non-zero term at some `k` with `gcd(k, 120) ≤ 3`. -/
theorem exists_slow_term (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N)
    {ρ : ℕ → ℚ} (hp : ∀ k, ρ (k + N) = ρ k) {r : ℚ} (hr : r ≠ 0)
    (h : HasSum (seriesTerm ρ) (r * Real.pi)) : ∃ k, Nat.gcd k 120 < 4 ∧ ρ k ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 := theoremD hB hN h120 ⟨hp, r, h⟩ hcon
  have h1 := h.unique h0
  have hpi := Real.pi_pos
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact hr (by exact_mod_cast h2)
  · linarith

end PiFormula
