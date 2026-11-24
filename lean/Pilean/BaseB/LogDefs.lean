module

public import Pilean.BaseB.TheoremG

/-!
# Logarithms in a general base: shared definitions

The values of the class `F_b` that are logarithms of rational numbers are described by the
rational numbers

  `ν(r)² = c₀(r)² / b^(d(r))`,

where `c₀(r)` is the constant term and `d(r)` the degree of the minimal polynomial of
`√b - r` over `ℤ`, for `r` a root of unity (`ν(r)` is, up to sign, the product of
`1 - s/√b` over the conjugates; the square avoids the parity of the degree).

This file fixes the definitions and statements shared by the files on logarithms
(research note `research/2026-11-22-log-primes/00_summary.md`):

* `nuSq b r`;
* `InBaseSpan b y`: some power `y^k`, `k ≥ 1`, is a product of integer powers of the `ν(r)²`;
* `PosWeight b`: a map `L : ℚ → ℚ` that is additive on products, positive on every integer
  `n ≥ 2`, and zero on every `ν(r)²`.

The plan: from Baker's theorem, if `q π + q' log y` (`q' ≠ 0`) is a value of `F_b` then
`InBaseSpan b y` (file `LogSpan`); for `b ≥ 5` not a square there is a positive weight (file
`LogWeight`); hence no `q π + q' log n` with `n ≥ 2` an integer is a value.

Nothing is proved here.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-- `ν(r)² = c₀(r)² / b^(d(r))`, with `c₀(r)` the constant term and `d(r)` the degree of the
minimal polynomial of `√b - r` over `ℤ`. -/
noncomputable def nuSq (b : ℕ) (r : ℂ) : ℚ :=
  (((minpoly ℤ (tB b - r)).eval 0 : ℤ) : ℚ) ^ 2 / (b : ℚ) ^ (minpoly ℤ (tB b - r)).natDegree

/-- Some power `y^k`, `k ≥ 1`, is a product of integer powers of the numbers `ν(r)²`, `r` over
finitely many roots of unity. -/
def InBaseSpan (b : ℕ) (y : ℚ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ (S : Finset ℂ) (e : ℂ → ℤ), (∀ r ∈ S, IsOfFinOrder r) ∧
    y ^ k = ∏ r ∈ S, nuSq b r ^ e r

/-- A positive weight for the base `b`: a map on the rationals that is additive on products,
positive on every integer `n ≥ 2`, and zero on every `ν(r)²`. -/
def PosWeight (b : ℕ) : Prop :=
  ∃ L : ℚ → ℚ, (∀ x y : ℚ, x ≠ 0 → y ≠ 0 → L (x * y) = L x + L y) ∧
    (∀ n : ℕ, 2 ≤ n → 0 < L (n : ℚ)) ∧ ∀ r : ℂ, IsOfFinOrder r → L (nuSq b r) = 0

end BaseB

end PiFormula
