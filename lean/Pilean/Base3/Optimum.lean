import Pilean.Base3.Dimension

/-!
# Base 3: no formula beats the Gregory series

For a rational periodic pattern `ρ`, let `termCount3 ρ` be the number of non-zero entries in
one period of 12, that is, the number of terms of the series `∑ ρ(k) 3^(-⌊k/2⌋)/k` per six
base-3 digits.

`theoremE3` (from Baker's theorem): if the series is a non-zero algebraic multiple of `π`,
then `termCount3 ρ ≥ 6`, one term per base-3 digit, and equality holds exactly for the rational
multiples of two patterns (written for `k = 1, ..., 12`):

* `rhoGregory = (6, 0, -6, 0, 6, 0, -6, 0, 6, 0, -6, 0)`, the Gregory series;
* `rhoSecond = (0, 18, 18, 18, 0, 0, 0, -18, -18, -18, 0, 0)`.

Both have the value `π√3`.

The proof. By `exists_coords3` the pattern is `a G + b Z₁ + c Z₂` with `a ≠ 0`. Its entries at
`k = 1, ..., 11` are

    6a + c,  b - 3c,  -(6a + 2b + 4c),  -3c,  6a + b + c,  4b,
    -(6a + c),  3(b + c),  6a + 2b + 4c,  4b + 3c,  -(6a + b + c).

The three forms `6a + c`, `6a + 2b + 4c`, `6a + b + c` occur twice each and cannot vanish
together. The five forms `b - 3c`, `c`, `b`, `b + c`, `4b + 3c` vanish together when
`b = c = 0`, and otherwise at most one of them vanishes. So there are at least 6 non-zero
entries, and equality forces `b = c = 0` or `b = 0, c = -6a`.
-/

namespace PiFormula

namespace Base3

/-- The number of non-zero entries of a pattern in one period of 12. -/
def termCount3 (ρ : ℕ → ℚ) : ℕ := ((Finset.range 12).filter fun k => ρ k ≠ 0).card

/-- `1` if `x ≠ 0`, and `0` if `x = 0`. -/
def ind (x : ℚ) : ℕ := if x = 0 then 0 else 1

theorem ind_of_ne {x : ℚ} (h : x ≠ 0) : ind x = 1 := by simp [ind, h]

theorem ind_of_eq {x : ℚ} (h : x = 0) : ind x = 0 := by simp [ind, h]

theorem eq_zero_of_ind {x : ℚ} (h : ind x = 0) : x = 0 := by
  by_contra hx
  rw [ind_of_ne hx] at h
  omega

theorem ind_eq_of_iff {x y : ℚ} (h : x = 0 ↔ y = 0) : ind x = ind y := by
  simp [ind, h]

theorem one_le_ind_add {x y : ℚ} (h : x = 0 → y = 0 → False) : 1 ≤ ind x + ind y := by
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · exact (h hx hy).elim
    · rw [ind_of_ne hy]
      omega
  · rw [ind_of_ne hx]
    omega

theorem termCount3_eq (ρ : ℕ → ℚ) :
    termCount3 ρ = ind (ρ 0) + ind (ρ 1) + ind (ρ 2) + ind (ρ 3) + ind (ρ 4) + ind (ρ 5) +
      ind (ρ 6) + ind (ρ 7) + ind (ρ 8) + ind (ρ 9) + ind (ρ 10) + ind (ρ 11) := by
  simp only [termCount3, Finset.card_filter, ind, ite_not, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]

theorem termCount3_smul {a : ℚ} (ha : a ≠ 0) (ρ : ℕ → ℚ) :
    termCount3 (a • ρ) = termCount3 ρ := by
  simp [termCount3, ha]

/-- The entries of `a G + b Z₁ + c Z₂` at `k = 0, ..., 11`. -/
theorem comb3_values (a b c : ℚ) :
    comb3 a b c 0 = 0 ∧ comb3 a b c 1 = 6 * a + c ∧ comb3 a b c 2 = b - 3 * c ∧
      comb3 a b c 3 = -(6 * a + 2 * b + 4 * c) ∧ comb3 a b c 4 = -3 * c ∧
      comb3 a b c 5 = 6 * a + b + c ∧ comb3 a b c 6 = 4 * b ∧ comb3 a b c 7 = -(6 * a + c) ∧
      comb3 a b c 8 = 3 * (b + c) ∧ comb3 a b c 9 = 6 * a + 2 * b + 4 * c ∧
      comb3 a b c 10 = 4 * b + 3 * c ∧ comb3 a b c 11 = -(6 * a + b + c) := by
  have hG : rhoGregory 0 = 0 ∧ rhoGregory 1 = 6 ∧ rhoGregory 2 = 0 ∧ rhoGregory 3 = -6 ∧
      rhoGregory 4 = 0 ∧ rhoGregory 5 = 6 ∧ rhoGregory 6 = 0 ∧ rhoGregory 7 = -6 ∧
      rhoGregory 8 = 0 ∧ rhoGregory 9 = 6 ∧ rhoGregory 10 = 0 ∧ rhoGregory 11 = -6 := by
    decide +kernel
  have h1 : rhoZ1 0 = 0 ∧ rhoZ1 1 = 0 ∧ rhoZ1 2 = 1 ∧ rhoZ1 3 = -2 ∧ rhoZ1 4 = 0 ∧
      rhoZ1 5 = 1 ∧ rhoZ1 6 = 4 ∧ rhoZ1 7 = 0 ∧ rhoZ1 8 = 3 ∧ rhoZ1 9 = 2 ∧ rhoZ1 10 = 4 ∧
      rhoZ1 11 = -1 := by
    decide +kernel
  have h2 : rhoZ2 0 = 0 ∧ rhoZ2 1 = 1 ∧ rhoZ2 2 = -3 ∧ rhoZ2 3 = -4 ∧ rhoZ2 4 = -3 ∧
      rhoZ2 5 = 1 ∧ rhoZ2 6 = 0 ∧ rhoZ2 7 = -1 ∧ rhoZ2 8 = 3 ∧ rhoZ2 9 = 4 ∧ rhoZ2 10 = 3 ∧
      rhoZ2 11 = -1 := by
    decide +kernel
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := hG
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11⟩ := h1
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11⟩ := h2
  simp only [comb3, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, y0, y1, y2, y3, y4, y5,
    y6, y7, y8, y9, y10, y11, z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring,
    by ring, by ring, by ring⟩

/-- The number of non-zero entries of `a G + b Z₁ + c Z₂`, in terms of eight linear forms. -/
theorem termCount3_comb3 (a b c : ℚ) :
    termCount3 (comb3 a b c) =
      2 * ind (6 * a + c) + 2 * ind (6 * a + 2 * b + 4 * c) + 2 * ind (6 * a + b + c) +
        (ind (b - 3 * c) + ind c + ind b + ind (b + c) + ind (4 * b + 3 * c)) := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11⟩ := comb3_values a b c
  rw [termCount3_eq, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
  have e0 : ind (0 : ℚ) = 0 := ind_of_eq rfl
  have e3 : ind (-(6 * a + 2 * b + 4 * c)) = ind (6 * a + 2 * b + 4 * c) :=
    ind_eq_of_iff neg_eq_zero
  have e4 : ind (-3 * c) = ind c := ind_eq_of_iff ⟨fun h => by linarith, fun h => by linarith⟩
  have e6 : ind (4 * b) = ind b := ind_eq_of_iff ⟨fun h => by linarith, fun h => by linarith⟩
  have e7 : ind (-(6 * a + c)) = ind (6 * a + c) := ind_eq_of_iff neg_eq_zero
  have e8 : ind (3 * (b + c)) = ind (b + c) :=
    ind_eq_of_iff ⟨fun h => by linarith, fun h => by linarith⟩
  have e11 : ind (-(6 * a + b + c)) = ind (6 * a + b + c) := ind_eq_of_iff neg_eq_zero
  rw [e0, e3, e4, e6, e7, e8, e11]
  ring

/-- The three forms that occur twice cannot all vanish. -/
theorem one_le_ind_three {a : ℚ} (ha : a ≠ 0) (b c : ℚ) :
    1 ≤ ind (6 * a + c) + ind (6 * a + 2 * b + 4 * c) + ind (6 * a + b + c) := by
  by_contra hcon
  have e1 := eq_zero_of_ind (by omega : ind (6 * a + c) = 0)
  have e2 := eq_zero_of_ind (by omega : ind (6 * a + 2 * b + 4 * c) = 0)
  have e3 := eq_zero_of_ind (by omega : ind (6 * a + b + c) = 0)
  apply ha
  linarith

/-- Unless `b = c = 0`, at most one of the five forms through the origin vanishes. -/
theorem four_le_ind_five {b c : ℚ} (hbc : ¬ (b = 0 ∧ c = 0)) :
    4 ≤ ind (b - 3 * c) + ind c + ind b + ind (b + c) + ind (4 * b + 3 * c) := by
  have key : ∀ {x y : ℚ}, (x = 0 → y = 0 → b = 0 ∧ c = 0) → 1 ≤ ind x + ind y :=
    fun h => one_le_ind_add fun hx hy => hbc (h hx hy)
  have p1 := key (x := b - 3 * c) (y := c) fun h1 h2 => ⟨by linarith, by linarith⟩
  have p2 := key (x := b - 3 * c) (y := b) fun h1 h2 => ⟨by linarith, by linarith⟩
  have p3 := key (x := b - 3 * c) (y := b + c) fun h1 h2 => ⟨by linarith, by linarith⟩
  have p4 := key (x := b - 3 * c) (y := 4 * b + 3 * c) fun h1 h2 => ⟨by linarith, by linarith⟩
  have p5 := key (x := c) (y := b) fun h1 h2 => ⟨by linarith, by linarith⟩
  have p6 := key (x := c) (y := b + c) fun h1 h2 => ⟨by linarith, by linarith⟩
  have p7 := key (x := c) (y := 4 * b + 3 * c) fun h1 h2 => ⟨by linarith, by linarith⟩
  have p8 := key (x := b) (y := b + c) fun h1 h2 => ⟨by linarith, by linarith⟩
  have p9 := key (x := b) (y := 4 * b + 3 * c) fun h1 h2 => ⟨by linarith, by linarith⟩
  have p10 := key (x := b + c) (y := 4 * b + 3 * c) fun h1 h2 => ⟨by linarith, by linarith⟩
  omega

/-- **At least 6 terms.** -/
theorem six_le_termCount3_comb3 {a : ℚ} (ha : a ≠ 0) (b c : ℚ) :
    6 ≤ termCount3 (comb3 a b c) := by
  rw [termCount3_comb3]
  by_cases hbc : b = 0 ∧ c = 0
  · obtain ⟨rfl, rfl⟩ := hbc
    have h1 : ind (6 * a + 0) = 1 := ind_of_ne fun h => ha (by linarith)
    have h2 : ind (6 * a + 2 * 0 + 4 * 0) = 1 := ind_of_ne fun h => ha (by linarith)
    have h3 : ind (6 * a + 0 + 0) = 1 := ind_of_ne fun h => ha (by linarith)
    omega
  · have h3 := one_le_ind_three ha b c
    have h5 := four_le_ind_five hbc
    omega

/-- **Exactly 6 terms** happens for `b = c = 0` and for `b = 0`, `c = -6a` only. -/
theorem termCount3_comb3_eq_six_iff {a : ℚ} (ha : a ≠ 0) (b c : ℚ) :
    termCount3 (comb3 a b c) = 6 ↔ (b = 0 ∧ c = 0) ∨ (b = 0 ∧ c = -6 * a) := by
  rw [termCount3_comb3]
  constructor
  · intro h6
    by_cases hbc : b = 0 ∧ c = 0
    · exact Or.inl hbc
    right
    have h3 := one_le_ind_three ha b c
    have h5 := four_le_ind_five hbc
    by_cases h1 : 6 * a + c = 0
    · have i1 := ind_of_eq h1
      by_cases h2 : 6 * a + 2 * b + 4 * c = 0
      · -- then `c = -6a`, `b = 9a`, and none of the five forms vanishes
        have i2 := ind_of_eq h2
        have hc : c = -6 * a := by linarith
        have hb : b = 9 * a := by linarith
        have n1 : ind (b - 3 * c) = 1 := ind_of_ne fun h => ha (by rw [hb, hc] at h; linarith)
        have n2 : ind c = 1 := ind_of_ne fun h => ha (by rw [hc] at h; linarith)
        have n3 : ind b = 1 := ind_of_ne fun h => ha (by rw [hb] at h; linarith)
        have n4 : ind (b + c) = 1 := ind_of_ne fun h => ha (by rw [hb, hc] at h; linarith)
        have n5 : ind (4 * b + 3 * c) = 1 :=
          ind_of_ne fun h => ha (by rw [hb, hc] at h; linarith)
        omega
      · have i2 := ind_of_ne h2
        have i3 : ind (6 * a + b + c) = 0 := by omega
        have e3 := eq_zero_of_ind i3
        exact ⟨by linarith, by linarith⟩
    · -- then `6a + 2b + 4c = 6a + b + c = 0`, so `c = 3a`, `b = -9a`: none of the five vanishes
      have i1 := ind_of_ne h1
      have i2 : ind (6 * a + 2 * b + 4 * c) = 0 := by omega
      have i3 : ind (6 * a + b + c) = 0 := by omega
      have e2 := eq_zero_of_ind i2
      have e3 := eq_zero_of_ind i3
      have hc : c = 3 * a := by linarith
      have hb : b = -9 * a := by linarith
      have n1 : ind (b - 3 * c) = 1 := ind_of_ne fun h => ha (by rw [hb, hc] at h; linarith)
      have n2 : ind c = 1 := ind_of_ne fun h => ha (by rw [hc] at h; linarith)
      have n3 : ind b = 1 := ind_of_ne fun h => ha (by rw [hb] at h; linarith)
      have n4 : ind (b + c) = 1 := ind_of_ne fun h => ha (by rw [hb, hc] at h; linarith)
      have n5 : ind (4 * b + 3 * c) = 1 :=
        ind_of_ne fun h => ha (by rw [hb, hc] at h; linarith)
      omega
  · rintro (⟨hb, hc⟩ | ⟨hb, hc⟩)
    · have t1 : ind (6 * a + c) = 1 := ind_of_ne fun h => ha (by rw [hc] at h; linarith)
      have t2 : ind (6 * a + 2 * b + 4 * c) = 1 :=
        ind_of_ne fun h => ha (by rw [hb, hc] at h; linarith)
      have t3 : ind (6 * a + b + c) = 1 :=
        ind_of_ne fun h => ha (by rw [hb, hc] at h; linarith)
      have n1 : ind (b - 3 * c) = 0 := ind_of_eq (by rw [hb, hc]; ring)
      have n2 : ind c = 0 := ind_of_eq hc
      have n3 : ind b = 0 := ind_of_eq hb
      have n4 : ind (b + c) = 0 := ind_of_eq (by rw [hb, hc]; ring)
      have n5 : ind (4 * b + 3 * c) = 0 := ind_of_eq (by rw [hb, hc]; ring)
      omega
    · have t1 : ind (6 * a + c) = 0 := ind_of_eq (by rw [hc]; ring)
      have t2 : ind (6 * a + 2 * b + 4 * c) = 1 :=
        ind_of_ne fun h => ha (by rw [hb, hc] at h; linarith)
      have t3 : ind (6 * a + b + c) = 0 := ind_of_eq (by rw [hb, hc]; ring)
      have n1 : ind (b - 3 * c) = 1 := ind_of_ne fun h => ha (by rw [hb, hc] at h; linarith)
      have n2 : ind c = 1 := ind_of_ne fun h => ha (by rw [hc] at h; linarith)
      have n3 : ind b = 0 := ind_of_eq hb
      have n4 : ind (b + c) = 1 := ind_of_ne fun h => ha (by rw [hb, hc] at h; linarith)
      have n5 : ind (4 * b + 3 * c) = 1 :=
        ind_of_ne fun h => ha (by rw [hb, hc] at h; linarith)
      omega

/-! ## The two formulas with 6 terms -/

/-- The second formula with 6 terms per period:
`(0, 18, 18, 18, 0, 0, 0, -18, -18, -18, 0, 0)` for `k = 1, ..., 12`. -/
def rhoSecond (k : ℕ) : ℚ :=
  match k % 12 with
  | 2 => 18 | 3 => 18 | 4 => 18 | 8 => -18 | 9 => -18 | 10 => -18 | _ => 0

theorem rhoSecond_periodic (k : ℕ) : rhoSecond (k + 12) = rhoSecond k := by simp [rhoSecond]

/-- `rhoSecond = G - 6 Z₂`. -/
theorem rhoSecond_eq : rhoSecond = comb3 1 0 (-6) := by
  funext k
  exact eq_of_lt_twelve rhoSecond_periodic (comb3_periodic 1 0 (-6)) (by decide +kernel) k

/-- `π√3 = ∑ ρ(k) 3^(-⌊k/2⌋)/k` for `ρ = (0, 18, 18, 18, 0, 0, 0, -18, -18, -18, 0, 0)`. -/
theorem hasSum_rhoSecond : HasSum (seriesTerm3 rhoSecond) (Real.pi * Real.sqrt 3) := by
  rw [rhoSecond_eq]
  have h := hasSum_comb3 1 0 (-6)
  simpa using h

theorem termCount3_rhoGregory : termCount3 rhoGregory = 6 := by decide +kernel

theorem termCount3_rhoSecond : termCount3 rhoSecond = 6 := by decide +kernel

theorem comb3_gregory (a : ℚ) : comb3 a 0 0 = a • rhoGregory := by
  funext k
  simp [comb3]

theorem comb3_second (a : ℚ) : comb3 a 0 (-6 * a) = a • rhoSecond := by
  funext k
  rw [rhoSecond_eq]
  simp only [comb3, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Theorem E3 (from Baker's theorem).** Let `ρ` be a rational periodic pattern whose series
`∑ ρ(k) 3^(-⌊k/2⌋)/k` is a non-zero algebraic multiple of `π`. Then at least 6 of its 12
entries per period are non-zero (at least one term per base-3 digit), and exactly 6 are
non-zero if and only if `ρ` is a rational multiple of the Gregory pattern or of
`rhoSecond`. -/
theorem theoremE3 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ) (hγ0 : γ ≠ 0)
    (h : HasSum (seriesTerm3 ρ) (γ * Real.pi)) :
    6 ≤ termCount3 ρ ∧
      (termCount3 ρ = 6 ↔ ∃ a : ℚ, ρ = a • rhoGregory ∨ ρ = a • rhoSecond) := by
  obtain ⟨a, b, c, rfl, hγa⟩ := exists_coords3 hB hN hρ hγ h
  have ha : a ≠ 0 := by
    rintro rfl
    apply hγ0
    rw [hγa]
    simp
  refine ⟨six_le_termCount3_comb3 ha b c, ?_⟩
  rw [termCount3_comb3_eq_six_iff ha]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨a, Or.inl (comb3_gregory a)⟩
    · exact ⟨a, Or.inr (comb3_second a)⟩
  · rintro ⟨a', h' | h'⟩
    · rw [← comb3_gregory] at h'
      have hz : ∀ k, comb3 (a - a') b c k = 0 := fun k => by
        have := congrFun h' k
        simp only [comb3] at this ⊢
        linarith
      obtain ⟨-, hb, hc⟩ := comb3_eq_zero hz
      exact Or.inl ⟨hb, hc⟩
    · rw [← comb3_second] at h'
      have hz : ∀ k, comb3 (a - a') b (c + 6 * a') k = 0 := fun k => by
        have := congrFun h' k
        simp only [comb3] at this ⊢
        linarith
      obtain ⟨ha', hb, hc⟩ := comb3_eq_zero hz
      refine Or.inr ⟨hb, ?_⟩
      linarith

end Base3

end PiFormula
