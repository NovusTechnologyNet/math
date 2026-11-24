module

public import Pilean.Base3.LogExplicit

/-!
# Base 3: `π√3` is a value

`π√3 = 6 ∑_{j ≥ 0} (-1)^j 3^(-j) / (2j + 1)`: the Gregory series for `arctan (1/√3) = π/6`.
In the class F3 it is the pattern `(6, 0, -6, 0)` of period 4 (`rhoGregory`).

According to the note (Part V), this is one of exactly two formulas for `π√3` in the class
F3 with one term per base-3 digit, and no formula has fewer; that statement is computed, not
yet proved in Lean. Here only: `π√3` is a value (`isF3Value_pi_sqrt3`).
-/

@[expose] public section

namespace PiFormula

namespace Base3

/-- The pattern `(6, 0, -6, 0)` of the Gregory series. -/
def rhoGregory (k : ℕ) : ℚ := if k % 2 = 1 then 6 * (-1) ^ (k / 2) else 0

theorem rhoGregory_periodic (k : ℕ) : rhoGregory (k + 4) = rhoGregory k := by
  have h1 : (k + 4) % 2 = k % 2 := by omega
  have h2 : (k + 4) / 2 = k / 2 + 2 := by omega
  simp only [rhoGregory, h1, h2, pow_add]
  norm_num

/-- `∑ ρ(k) 3^(-⌊k/2⌋)/k = π√3` for `ρ = (6, 0, -6, 0)`. -/
theorem hasSum_gregory3 : HasSum (seriesTerm3 rhoGregory) (Real.pi * Real.sqrt 3) := by
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs1 : (1 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hx : ‖(Real.sqrt 3)⁻¹‖ < 1 := by
    rw [norm_inv, Real.norm_of_nonneg hs.le]
    exact inv_lt_one_of_one_lt₀ hs1
  have h := Real.hasSum_arctan hx
  rw [Real.arctan_inv_sqrt_three] at h
  have h2 := h.mul_left (6 * Real.sqrt 3)
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := fun a b hab => by
    simpa using hab
  have hzero : ∀ k, k ∉ Set.range (fun n : ℕ => 2 * n + 1) →
      seriesTerm3 rhoGregory k = 0 := by
    intro k hk
    have h1 : k % 2 ≠ 1 := fun h1 => hk ⟨k / 2, by simp only; omega⟩
    simp [seriesTerm3, rhoGregory, h1]
  rw [← hinj.hasSum_iff hzero]
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  convert h2 using 1
  · funext n
    have h1 : (2 * n + 1) % 2 = 1 := by omega
    have h3 : (2 * n + 1) / 2 = n := by omega
    have hpow : (Real.sqrt 3)⁻¹ ^ (2 * n + 1) = (Real.sqrt 3)⁻¹ / 3 ^ n := by
      rw [pow_succ, pow_mul, inv_pow, hsq, inv_pow]
      ring
    simp only [Function.comp_apply, seriesTerm3, rhoGregory, h1, h3, ↓reduceIte]
    rw [hpow]
    push_cast
    field_simp
  · field_simp

/-- **`π√3` is a value of the class F3.** -/
theorem isF3Value_pi_sqrt3 : IsF3Value (Real.pi * Real.sqrt 3) :=
  ⟨4, rhoGregory, by norm_num, rhoGregory_periodic, hasSum_gregory3⟩

end Base3

end PiFormula
