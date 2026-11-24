/-! ## 4. The bound -/

/-- The certificate passes the checker (kernel computation). -/
theorem theCert_ok : checkCert [] [] theCert = true := by decide +kernel

/-- For a pattern of `V` with non-zero value, at least 40 entries per period are non-zero. -/
theorem termCount_namedComb_ge (q : Fin 8 → ℚ) (hV : q 0 + q 2 ≠ 0) :
    40 ≤ termCount (namedComb q) :=
  checkCert_sound q hV theCert [] [] theCert_ok (fun z hz => by simp at hz)
    (fun e he => by simp at he)

/-- **Theorem E, standard measure (from Baker's theorem).** Let `ρ` be a rational pattern of
period `N` (a multiple of 120) whose series `∑ ρ(k) 2^(-⌊k/2⌋)/k` is a non-zero rational
multiple of `π`. Then at least 40 of its 120 entries per period are non-zero: the series has
at least `2/3` terms per bit. -/
theorem termCount_ge (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) {ρ : ℕ → ℚ}
    (hp : ∀ k, ρ (k + N) = ρ k) {r : ℚ} (hr : r ≠ 0)
    (h : HasSum (seriesTerm ρ) (r * Real.pi)) : 40 ≤ termCount ρ := by
  obtain ⟨q, rfl⟩ := exists_coords hB hN h120 ⟨hp, r, h⟩
  exact termCount_namedComb_ge q (value_ne_zero hr h)

end PiFormula
