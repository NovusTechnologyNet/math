import Pilean.PiFormula.PrimeMeasure
import Pilean.PiFormula.FewestTerms
import Pilean.PiFormula.BaileySums
import Pilean.PiFormula.SharpD

/-!
# Theorem E: the optima in both cost measures

For a series of the class F with a non-zero rational value (in units of `π`):

* **standard measure** (terms per bit, the cost of the classical BBP algorithm): at least 40
  of the 120 entries per period are non-zero, that is, at least `2/3` terms per bit;
* **prime measure** (the mean of `1/s` over the 32 classes of primes modulo 120, the cost of
  the window algorithm): at least `7/24`.

`theoremE` states both bounds (from Baker's theorem). Both are attained:

* `huvent1_formula`, `huvent2_formula`: Huvent's two formulas of 2001, in Bailey's notation
  `P(1, 2^12, 24, A)`, with values `512 · π/4` and `1024 · π/4`; each has exactly 40 non-zero
  entries per period (`termCount_rhoHuvent1`, `termCount_rhoHuvent2`). So the rate `2/3`,
  which y-cruncher's digit extractor uses, cannot be improved by any formula of this kind.
  This answers the question Bellard left open in 1997.
* `primeCost_rhoNew`: the new formula has `mean(1/s) = 7/24`.

The table of the note is reproduced by `cost_table`.

Not proved here: that the two optima are attained *only* by these formulas (two formulas for
`2/3`, two families for `7/24`), and the list of non-dominated pairs.
-/

open Complex

namespace PiFormula

/-! ## 1. Huvent's two formulas -/

theorem pos12 : 0 < 12 := by norm_num

/-- The coefficients `a_1, ..., a_24` of Huvent's first formula
`π/4 = (1/512) ∑_j 2^(-12j) [768/(24j+3) + 512/(24j+4) + 128/(24j+6) - 16/(24j+12)
- 16/(24j+14) - 12/(24j+15) + 2/(24j+20) - 1/(24j+22)]`. -/
def huvent1 : Fin (2 * 12) → ℚ :=
  ![0, 0, 768, 512, 0, 128, 0, 0, 0, 0, 0, -16, 0, -16, -12, 0, 0, 0, 0, 2, 0, -1, 0, 0]

/-- The coefficients `a_1, ..., a_24` of Huvent's second formula
`π/4 = (1/1024) ∑_j 2^(-12j) [2048/(24j+2) - 1024/(24j+4) + 192/(24j+9) + 128/(24j+10)
+ 32/(24j+12) - 4/(24j+18) - 4/(24j+20) - 3/(24j+21)]`. -/
def huvent2 : Fin (2 * 12) → ℚ :=
  ![0, 2048, 0, -1024, 0, 0, 0, 0, 192, 128, 0, 32, 0, 0, 0, 0, 0, -4, 0, -4, -3, 0, 0, 0]

/-- The pattern of Huvent's first formula. -/
def rhoHuvent1 : ℕ → ℚ := patF2 (Nat.mul_pos two_pos pos12) huvent1

/-- The pattern of Huvent's second formula. -/
def rhoHuvent2 : ℕ → ℚ := patF2 (Nat.mul_pos two_pos pos12) huvent2

theorem rhoHuvent1_periodic (k : ℕ) : rhoHuvent1 (k + 120) = rhoHuvent1 k :=
  periodic_mul (f := rhoHuvent1) (a := 2 * 12) (patF2_periodic _ huvent1) 5 k

theorem rhoHuvent2_periodic (k : ℕ) : rhoHuvent2 (k + 120) = rhoHuvent2 k :=
  periodic_mul (f := rhoHuvent2) (a := 2 * 12) (patF2_periodic _ huvent2) 5 k

/-- Huvent's first pattern in the eight named series: `512 (A1 - A6 - L6) + 256 L24`. -/
theorem rhoHuvent1_eq (k : ℕ) :
    rhoHuvent1 k = namedComb ![512, -512, 0, -512, 0, 0, 256, 0] k := by
  have htab : ∀ r < 120, rhoHuvent1 r = namedComb ![512, -512, 0, -512, 0, 0, 256, 0] r := by
    decide +kernel
  have h1 := mod_120 rhoHuvent1_periodic k
  have h2 := mod_120 (namedComb_periodic ![512, -512, 0, -512, 0, 0, 256, 0]) k
  rw [← h1, ← h2]
  exact htab (k % 120) (Nat.mod_lt _ (by norm_num))

/-- Huvent's second pattern in the eight named series: `1024 (A1 - A6 + L6) - 512 L24`. -/
theorem rhoHuvent2_eq (k : ℕ) :
    rhoHuvent2 k = namedComb ![1024, -1024, 0, 1024, 0, 0, -512, 0] k := by
  have htab : ∀ r < 120,
      rhoHuvent2 r = namedComb ![1024, -1024, 0, 1024, 0, 0, -512, 0] r := by
    decide +kernel
  have h1 := mod_120 rhoHuvent2_periodic k
  have h2 := mod_120 (namedComb_periodic ![1024, -1024, 0, 1024, 0, 0, -512, 0]) k
  rw [← h1, ← h2]
  exact htab (k % 120) (Nat.mod_lt _ (by norm_num))

theorem hasSum_rhoHuvent1 : HasSum (seriesTerm rhoHuvent1) (512 * (Real.pi / 4)) := by
  have h := hasSum_of_coords (f := rhoHuvent1) ![512, -512, 0, -512, 0, 0, 256, 0]
    rhoHuvent1_eq (c := 512) (by norm_num)
  rw [Rat.cast_ofNat] at h
  exact h

theorem hasSum_rhoHuvent2 : HasSum (seriesTerm rhoHuvent2) (1024 * (Real.pi / 4)) := by
  have h := hasSum_of_coords (f := rhoHuvent2) ![1024, -1024, 0, 1024, 0, 0, -512, 0]
    rhoHuvent2_eq (c := 1024) (by norm_num)
  rw [Rat.cast_ofNat] at h
  exact h

/-- **Huvent's first formula**, in Bailey's notation: `P(1, 2^12, 24, A) = 512 · π/4`. -/
theorem huvent1_formula : HasSum (baileyBlock 12 (2 * 12) huvent1) (512 * (Real.pi / 4)) :=
  (hasSum_bailey_F2 pos12 huvent1 _).2 hasSum_rhoHuvent1

/-- **Huvent's second formula**, in Bailey's notation: `P(1, 2^12, 24, A) = 1024 · π/4`. -/
theorem huvent2_formula : HasSum (baileyBlock 12 (2 * 12) huvent2) (1024 * (Real.pi / 4)) :=
  (hasSum_bailey_F2 pos12 huvent2 _).2 hasSum_rhoHuvent2

/-- Huvent's first formula has exactly 40 non-zero entries per period: `2/3` terms per bit. -/
theorem termCount_rhoHuvent1 : termCount rhoHuvent1 = 40 := by decide +kernel

/-- Huvent's second formula has exactly 40 non-zero entries per period. -/
theorem termCount_rhoHuvent2 : termCount rhoHuvent2 = 40 := by decide +kernel

/-! ## 2. The table of the note -/

/-- **The two costs of the known formulas** (non-zero entries per period of 120, and the mean
of `1/s`): Huvent's two formulas `(40, 5/12)`, Euler's formula `2 arctan(1/3) + arctan(1/7)`
`(42, 1/3)`, and the new formula `(55, 7/24)`. Divide the first number by 60 for terms per
bit: `2/3`, `7/10` and `11/12`. -/
theorem cost_table :
    (termCount rhoHuvent1 = 40 ∧ primeCost rhoHuvent1 = 5 / 12) ∧
      (termCount rhoHuvent2 = 40 ∧ primeCost rhoHuvent2 = 5 / 12) ∧
      (termCount sAvoid12 = 42 ∧ primeCost sAvoid12 = 1 / 3) ∧
      (termCount rhoNew = 55 ∧ primeCost rhoNew = 7 / 24) := by
  refine ⟨⟨termCount_rhoHuvent1, ?_⟩, ⟨termCount_rhoHuvent2, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, primeCost_rhoNew⟩⟩ <;> decide +kernel

/-! ## 3. Theorem E -/

/-- **Theorem E, the two bounds (from Baker's theorem).** Let `ρ` be a rational pattern of
period `N` (a multiple of 120) whose series `∑ ρ(k) 2^(-⌊k/2⌋)/k` is a non-zero rational
multiple of `π`. Then
* at least 40 of its 120 entries per period are non-zero (at least `2/3` terms per bit), and
* the mean of `1/s` over the 32 classes of primes modulo 120 is at least `7/24`.

Both bounds are attained: by Huvent's formulas (`termCount_rhoHuvent1`) and by the new formula
(`primeCost_rhoNew`). -/
theorem theoremE (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) {ρ : ℕ → ℚ}
    (hp : ∀ k, ρ (k + N) = ρ k) {r : ℚ} (hr : r ≠ 0)
    (h : HasSum (seriesTerm ρ) (r * Real.pi)) : 40 ≤ termCount ρ ∧ 7 / 24 ≤ primeCost ρ :=
  ⟨termCount_ge hB hN h120 hp hr h, primeCost_ge hB hN h120 hp hr h⟩

end PiFormula
