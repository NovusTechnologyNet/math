module

public import Pilean.BaseB.Defs

/-!
# A general base `b` and a general step `n`: shared definitions

The degree-1 BBP-type series of base `b` are the series

  `∑ ρ(k) b^(-⌊k/n⌋) / k`,   `ρ` rational and periodic,

for some `n ≥ 1`: a formula `∑_j b^(-Bj) ∑_i a_i / (Nj + i)` is of this kind with
`n = N / gcd(B, N)`. The class `F_b` of `Defs` is the case `n = 2`.

This file fixes the definitions and the two statements that the files of `Pilean/BaseB` on
the general step share (Part IV of `notes/pi_formula_theorem.md`, for a general base):

* `cB b n = b^(1/n)`, the positive real `n`-th root of `b`, seen in `ℂ`;
* `seriesTermBN b n`, the term of the series;
* `halfIfEven n`: `n/2` for even `n`, and `n` for odd `n`;
* `KummerHom b n`: for every `M` and every root of unity `η` with `η^(halfIfEven n) = 1`, a
  field homomorphism `ℚ(ζ_M, c) → ℂ` sends `c = b^(1/n)` to `η c` and fixes `ζ_M`. It holds
  when `b` is not a perfect power (file `Kummer`): `X^(n₁) - c^(n₁)` is irreducible over every
  cyclotomic field.

From `KummerHom b n` and Baker's theorem: if a series of step `n` is a rational multiple
`q π` of `π`, then its sub-series over the `k` divisible by `halfIfEven n` is already `q π`
(file `Subseries`). That sub-series is a series of the class `F_b`.

Nothing is proved here.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-- `c = b^(1/n)`, the positive real `n`-th root of `b`, seen in `ℂ`. -/
noncomputable def cB (b n : ℕ) : ℂ := (((b : ℝ) ^ ((1 : ℝ) / (n : ℝ)) : ℝ) : ℂ)

/-- The term `ρ(k) b^(-⌊k/n⌋) / k` of the series of step `n`. -/
noncomputable def seriesTermBN (b n : ℕ) (ρ : ℕ → ℚ) (k : ℕ) : ℝ :=
  (ρ k : ℝ) / (b : ℝ) ^ (k / n) / k

/-- For `n = 2` this is the term of the class `F_b`. -/
theorem seriesTermBN_two (b : ℕ) (ρ : ℕ → ℚ) : seriesTermBN b 2 ρ = seriesTermB b ρ := rfl

/-- `n/2` for even `n`, and `n` for odd `n`. -/
def halfIfEven (n : ℕ) : ℕ := if Even n then n / 2 else n

/-- **The Kummer homomorphisms.** For every `M ≥ 1` and every `η` with `η^(halfIfEven n) = 1`,
some field homomorphism `ℚ(ζ_M, c) → ℂ` sends `c = b^(1/n)` to `η c` and fixes `ζ_M`. -/
def KummerHom (b n : ℕ) : Prop :=
  ∀ M : ℕ, 0 < M → ∀ η : ℂ, η ^ halfIfEven n = 1 →
    ∃ σ : (IntermediateField.adjoin ℚ ({zetaN M, cB b n} : Set ℂ)) →ₐ[ℚ] ℂ,
      (∀ x : IntermediateField.adjoin ℚ ({zetaN M, cB b n} : Set ℂ),
        (x : ℂ) = cB b n → σ x = η * cB b n) ∧
      (∀ x : IntermediateField.adjoin ℚ ({zetaN M, cB b n} : Set ℂ),
        (x : ℂ) = zetaN M → σ x = zetaN M)

/-- `b` is not a perfect power: it is not `a^k` with `k ≥ 2`. -/
def NotPerfectPower (b : ℕ) : Prop := ∀ a k : ℕ, 2 ≤ k → a ^ k ≠ b

end BaseB

end PiFormula
