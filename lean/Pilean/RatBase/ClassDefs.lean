/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.RatBase.Defs
public import Pilean.BaseB.TheoremG

/-!
# Rational bases: shared definitions for the classification

For a rational base `p/q > 1` (`p > q ≥ 1` coprime integers) the class `F_(p/q)` is the set of
series `∑ ρ(k) (q/p)^⌊k/2⌋ / k` with `ρ` rational and periodic (`seriesTermRat` of `Defs`).
With `t = √(p/q)` and `u = √(pq)`,

  `∑ ρ(k) (q/p)^⌊k/2⌋ / k = - ∑_r D_r Log(1 - r/t)`,   `1 - r/t = (u - q r) / u`,

`r` over roots of unity. So everything is said in terms of the algebraic integers `u - q r`,
`u = tB (p * q)`, with `(u - q r)(u + q r) = q (p - q r²)`, whose conjugates multiply to a
power of the homogeneous cyclotomic value `Φ_m(p, q)` (`m` the order of `r²`) times a power
of `q`.

This file fixes the definitions and statements shared by the files of `Pilean/RatBase` on
the classification (research note `research/2026-11-22-rational-bases/00_summary.md`):

* `IsFRValue p q x`: `x` is a value of the class;
* `HasGoodPrimeR p q r`: a prime ideal of the algebraic integers contains `u - q r` and an odd
  rational prime that divides neither `p q` nor the order of `r`;
* `GoodPrimesR p q`: every root of unity `r` with `r⁴ ≠ 1` has a good prime;
* `SizeCondR p q m`: `Φ_m(p, q) > (√p + √q)^φ(m)`, and `> ℓ (√p + √q)^φ(m)` for every prime `ℓ`
  dividing both `m` and `Φ_m(p, q)`.

The plan, as for integer bases (`Pilean/BaseB`): the size condition for large `p` (file
`SizeR`); from the size condition, a good prime (file `ReductionR`); from the good primes and
Baker's theorem, no relation (file `ClassificationR`). For `q = 1` these are the notions of
`BaseB`. The five bases `2, 3, 4, 3/2, 4/3` have relations and fail `GoodPrimesR`.

Nothing is proved here.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace RatBase

/-- `x` is the value of a series of the class of the rational base `p/q`. -/
def IsFRValue (p q : ℕ) (x : ℝ) : Prop :=
  ∃ (N : ℕ) (ρ : ℕ → ℚ), 0 < N ∧ (∀ k, ρ (k + N) = ρ k) ∧ HasSum (seriesTermRat p q ρ) x

/-- The homogeneous cyclotomic value `Φ_m(p, q)`, an integer. -/
noncomputable def cycValR (p q m : ℕ) : ℤ :=
  TauCeti.homogeneousCyclotomic m (p : ℤ) (q : ℤ)

/-- A good prime for the root of unity `r` in the base `p/q`: a prime ideal of the algebraic
integers that contains `√(pq) - q r` and an odd rational prime dividing neither `p q` nor the
order of `r`. -/
def HasGoodPrimeR (p q : ℕ) (r : ℂ) : Prop :=
  ∃ P : Ideal Aint, P.IsPrime ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ¬ ℓ ∣ p * q ∧ ¬ ℓ ∣ orderOf r ∧
    InP P (ℓ : ℂ) ∧ InP P (BaseB.tB (p * q) - (q : ℂ) * r)

/-- Every root of unity other than `1, -1, i, -i` has a good prime in the base `p/q`. -/
def GoodPrimesR (p q : ℕ) : Prop :=
  ∀ r : ℂ, IsOfFinOrder r → r ^ 4 ≠ 1 → HasGoodPrimeR p q r

/-- The size condition at `(p, q, m)`. -/
def SizeCondR (p q m : ℕ) : Prop :=
  (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ m.totient < ((cycValR p q m : ℤ) : ℝ) ∧
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → (ℓ : ℤ) ∣ cycValR p q m →
      (ℓ : ℝ) * (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ m.totient < ((cycValR p q m : ℤ) : ℝ)

end RatBase

end PiFormula
