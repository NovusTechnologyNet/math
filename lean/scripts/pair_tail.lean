/-! ## 5. The bound -/

-- The kernel evaluates the checker on the whole certificate, which takes several minutes and
-- far more than the default heartbeat budget.
set_option maxHeartbeats 0 in
/-- The certificate passes the checker (kernel computation). -/
theorem pairCert_ok : checkPair [] [] [] [] pairCert = true := by decide +kernel

/-- For a zero relation `namedComb w ≠ 0` and a pattern `namedComb q` of non-zero value, the
cost is at least 60. -/
theorem zCost_namedComb_ge (w q : Fin 8 → ℚ) (hw0 : w 0 + w 2 = 0)
    (hw : ∃ k, namedComb w k ≠ 0) (hq : q 0 + q 2 ≠ 0) :
    60 ≤ zCost (namedComb w) (namedComb q) :=
  checkPair_sound w q hw0 hw hq pairCert [] [] [] [] pairCert_ok (fun z hz => by simp at hz)
    (fun e he => by simp at he) (fun z hz => by simp at hz) (fun e he => by simp at he)

theorem namedComb_sub (q₁ q₂ : Fin 8 → ℚ) (k : ℕ) :
    namedComb (fun i => q₁ i - q₂ i) k = namedComb q₁ k - namedComb q₂ k := by
  simp only [namedComb]
  ring

/-- **The cheapest checked computation (from Baker's theorem).** Let `ρ₁ ≠ ρ₂` be rational
patterns of period `N` (a multiple of 120) whose series `∑ ρ(k) 2^(-⌊k/2⌋)/k` have the same
value `r π`, `r ≠ 0` rational. Then `60 ≤ pairCost ρ₁ ρ₂`: computing with one and checking
with the other costs at least 60 terms per 60 bits. -/
theorem pairCost_ge (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) {ρ₁ ρ₂ : ℕ → ℚ}
    (hp₁ : ∀ k, ρ₁ (k + N) = ρ₁ k) (hp₂ : ∀ k, ρ₂ (k + N) = ρ₂ k) {r : ℚ} (hr : r ≠ 0)
    (h₁ : HasSum (seriesTerm ρ₁) (r * Real.pi)) (h₂ : HasSum (seriesTerm ρ₂) (r * Real.pi))
    (hne : ρ₁ ≠ ρ₂) : 60 ≤ pairCost ρ₁ ρ₂ := by
  obtain ⟨q₁, rfl⟩ := exists_coords hB hN h120 ⟨hp₁, r, h₁⟩
  obtain ⟨q₂, rfl⟩ := exists_coords hB hN h120 ⟨hp₂, r, h₂⟩
  have hv₁ : q₁ 0 + q₁ 2 ≠ 0 := value_ne_zero hr h₁
  -- the two values agree
  have hval : q₁ 0 + q₁ 2 = q₂ 0 + q₂ 2 := by
    have e₁ := (hasSum_namedComb q₁).unique h₁
    have e₂ := (hasSum_namedComb q₂).unique h₂
    have hpi : Real.pi / 4 ≠ 0 := by positivity
    have e := e₁.trans e₂.symm
    exact_mod_cast mul_right_cancel₀ hpi e
  set w : Fin 8 → ℚ := fun i => q₁ i - q₂ i with hw_def
  have hw0 : w 0 + w 2 = 0 := by
    simp only [hw_def]
    linarith
  have hw : ∃ k, namedComb w k ≠ 0 := by
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    exact ⟨k, by rw [namedComb_sub]; exact sub_ne_zero.2 hk⟩
  rw [pairCost_eq_zCost]
  have h := zCost_namedComb_ge w q₁ hw0 hw hv₁
  have e : (fun k => namedComb q₁ k - namedComb q₂ k) = namedComb w := by
    funext k
    exact (namedComb_sub q₁ q₂ k).symm
  rw [e]
  exact h

/-! ## 6. Takahashi's pair, and Huvent's -/

theorem pos60 : 0 < 60 := by norm_num

-- TAKAHASHI_TABLES

/-- Takahashi's first formula (his formula (23), Bellard's formula expanded three times), as
`P(1, 2^60, 120, A)`: the coefficients `a_1, ..., a_120`. His series
`S(m, j) = ∑_k (-1)^k / (2^(30k) (mk + j))` with coefficient `c` contributes `c · 60/m` at
`i = 60j/m` and `-c · 60/m · 2^(-30)` at `i = 60 + 60j/m`. -/
def takahashi1 : Fin (2 * 60) → ℚ := fun i =>
  (tak1Num.getD i.val 0 : ℚ) / 2 ^ 57

/-- Takahashi's second formula (his formula (26)), as `P(1, 2^60, 120, A)`. -/
def takahashi2 : Fin (2 * 60) → ℚ := fun i =>
  (tak2Num.getD i.val 0 : ℚ) / 2 ^ 57

/-- The pattern of Takahashi's first formula. -/
def rhoTak1 : ℕ → ℚ := patF2 (Nat.mul_pos two_pos pos60) takahashi1

/-- The pattern of Takahashi's second formula. -/
def rhoTak2 : ℕ → ℚ := patF2 (Nat.mul_pos two_pos pos60) takahashi2

theorem rhoTak1_periodic (k : ℕ) : rhoTak1 (k + 120) = rhoTak1 k :=
  patF2_periodic _ takahashi1 k

theorem rhoTak2_periodic (k : ℕ) : rhoTak2 (k + 120) = rhoTak2 k :=
  patF2_periodic _ takahashi2 k

/-- Takahashi's first pattern in the eight named series: `8 A1 - 4 A10`. -/
theorem rhoTak1_eq (k : ℕ) : rhoTak1 k = namedComb ![8, 0, -4, 0, 0, 0, 0, 0] k := by
  have htab : ∀ r < 120, rhoTak1 r = namedComb ![8, 0, -4, 0, 0, 0, 0, 0] r := by
    decide +kernel
  have h1 := mod_120 rhoTak1_periodic k
  have h2 := mod_120 (namedComb_periodic ![8, 0, -4, 0, 0, 0, 0, 0]) k
  rw [← h1, ← h2]
  exact htab (k % 120) (Nat.mod_lt _ (by norm_num))

/-- Takahashi's second pattern in the eight named series: `4 A1 - 4 A6`. -/
theorem rhoTak2_eq (k : ℕ) : rhoTak2 k = namedComb ![4, -4, 0, 0, 0, 0, 0, 0] k := by
  have htab : ∀ r < 120, rhoTak2 r = namedComb ![4, -4, 0, 0, 0, 0, 0, 0] r := by
    decide +kernel
  have h1 := mod_120 rhoTak2_periodic k
  have h2 := mod_120 (namedComb_periodic ![4, -4, 0, 0, 0, 0, 0, 0]) k
  rw [← h1, ← h2]
  exact htab (k % 120) (Nat.mod_lt _ (by norm_num))

theorem hasSum_rhoTak1 : HasSum (seriesTerm rhoTak1) Real.pi := by
  have h := hasSum_of_coords (f := rhoTak1) ![8, 0, -4, 0, 0, 0, 0, 0] rhoTak1_eq (c := 4)
    (by norm_num)
  convert h using 1
  push_cast
  ring

theorem hasSum_rhoTak2 : HasSum (seriesTerm rhoTak2) Real.pi := by
  have h := hasSum_of_coords (f := rhoTak2) ![4, -4, 0, 0, 0, 0, 0, 0] rhoTak2_eq (c := 4)
    (by norm_num)
  convert h using 1
  push_cast
  ring

/-- **Takahashi's first formula**, in Bailey's notation: `P(1, 2^60, 120, A) = π`. -/
theorem takahashi1_formula : HasSum (baileyBlock 60 (2 * 60) takahashi1) Real.pi :=
  (hasSum_bailey_F2 pos60 takahashi1 _).2 hasSum_rhoTak1

/-- **Takahashi's second formula**, in Bailey's notation: `P(1, 2^60, 120, A) = π`. -/
theorem takahashi2_formula : HasSum (baileyBlock 60 (2 * 60) takahashi2) Real.pi :=
  (hasSum_bailey_F2 pos60 takahashi2 _).2 hasSum_rhoTak2

/-- **Takahashi's pair attains the bound**: computing with one of his formulas and checking
with the other costs exactly 60 terms per 60 bits. -/
theorem pairCost_takahashi : pairCost rhoTak1 rhoTak2 = 60 := by decide +kernel

/-- The two formulas have 42 and 50 terms per period, and agree at two positions. -/
theorem termCount_takahashi : termCount rhoTak1 = 42 ∧ termCount rhoTak2 = 50 := by
  constructor <;> decide +kernel

/-- Huvent's two formulas, scaled to the same value `π/4`, used as a pair: 65 terms per 60
bits. -/
theorem pairCost_huvent :
    pairCost (fun k => rhoHuvent1 k / 512) (fun k => rhoHuvent2 k / 1024) = 65 := by
  decide +kernel

/-- **The checked pair, both statements (from Baker's theorem).** Any two different formulas
of the class F with the same non-zero rational multiple of `π` as value cost at least 60, and
Takahashi's two formulas (both of value `π`) cost exactly 60. -/
theorem checkedPair (hB : BakerTheorem) :
    (∀ {N : ℕ}, 0 < N → 120 ∣ N → ∀ {ρ₁ ρ₂ : ℕ → ℚ}, (∀ k, ρ₁ (k + N) = ρ₁ k) →
      (∀ k, ρ₂ (k + N) = ρ₂ k) → ∀ {r : ℚ}, r ≠ 0 → HasSum (seriesTerm ρ₁) (r * Real.pi) →
      HasSum (seriesTerm ρ₂) (r * Real.pi) → ρ₁ ≠ ρ₂ → 60 ≤ pairCost ρ₁ ρ₂) ∧
    HasSum (seriesTerm rhoTak1) Real.pi ∧ HasSum (seriesTerm rhoTak2) Real.pi ∧
      pairCost rhoTak1 rhoTak2 = 60 :=
  ⟨fun hN h120 => fun hp₁ hp₂ => fun hr h₁ h₂ hne =>
      pairCost_ge hB hN h120 hp₁ hp₂ hr h₁ h₂ hne,
    hasSum_rhoTak1, hasSum_rhoTak2, pairCost_takahashi⟩

end PiFormula
