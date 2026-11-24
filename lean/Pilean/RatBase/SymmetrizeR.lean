/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.RatBase.ClassDefs

/-!
# Rational bases: symmetrization, and the scaled cyclotomic polynomial

Two tools for the file `ReductionR`, with `u = √(pq)` (the number `BaseB.tB (p * q)`).

* `exists_symmetrizeR`: for every `G ∈ ℤ[X]` there is `S ∈ ℤ[X]` with
  `S(z) = G(u - q z) G(-u - q z)` for every complex `z`. It is the symmetrization of
  `BaseB.exists_symmetrize` in base `pq`, composed with `z ↦ q z`.
* `cycloScaled q n`: the integer polynomial `Ψ(Y) = q^φ(n) Φ_n(Y / q)`, the homogeneous
  cyclotomic polynomial `Φ_n(Y, q)`. It is monic, its roots are the numbers `q r'`, `r'` over
  the primitive `n`-th roots of unity (`aeval_cycloScaled_eq_prod`).

The symmetrization of `Ψ` in base `pq` is then the polynomial
`F(z) = Ψ(u - z) Ψ(-u - z) = ∏ ((z + q r')² - pq)` of the research note
(`research/2026-11-22-rational-bases/00_summary.md`, section 3.3), which vanishes at `u - q r`.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace RatBase

/-- **Symmetrization.** For `G ∈ ℤ[X]` there is `S ∈ ℤ[X]` with
`S(z) = G(u - q z) G(-u - q z)` for every complex `z`, where `u = √(pq)`. -/
theorem exists_symmetrizeR (p q : ℕ) (G : ℤ[X]) : ∃ S : ℤ[X], ∀ z : ℂ,
    aeval z S = aeval (BaseB.tB (p * q) - (q : ℂ) * z) G *
      aeval (-BaseB.tB (p * q) - (q : ℂ) * z) G := by
  obtain ⟨S, hS⟩ := BaseB.exists_symmetrize (p * q) G
  refine ⟨S.comp (C (q : ℤ) * X), fun z => ?_⟩
  rw [aeval_comp, ← hS]
  simp

/-- The scaled cyclotomic polynomial `Ψ(Y) = q^φ(n) Φ_n(Y / q)`, in `ℤ[Y]`. -/
noncomputable def cycloScaled (q n : ℕ) : ℤ[X] := (cyclotomic n ℤ).scaleRoots (q : ℤ)

/-- `Ψ(q w) = q^φ(n) Φ_n(w)`. -/
theorem aeval_mul_cycloScaled (q n : ℕ) (w : ℂ) :
    aeval ((q : ℂ) * w) (cycloScaled q n) = (q : ℂ) ^ n.totient * aeval w (cyclotomic n ℤ) := by
  have h := scaleRoots_eval₂_mul (p := cyclotomic n ℤ) (algebraMap ℤ ℂ) w (q : ℤ)
  rw [natDegree_cyclotomic] at h
  simpa [cycloScaled, aeval_def] using h

/-- `Φ_n(w)` is the product of the `w - r'` over the primitive `n`-th roots `r'`. -/
private theorem aeval_cyclotomic_eq_prod {n : ℕ} (hn : 0 < n) (w : ℂ) :
    aeval w (cyclotomic n ℤ) = ∏ r' ∈ primitiveRoots n ℂ, (w - r') := by
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic,
    cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp n hn.ne'), eval_prod]
  simp

/-- `Ψ(y)` is the product of the `y - q r'` over the primitive `n`-th roots `r'`. -/
theorem aeval_cycloScaled_eq_prod {q n : ℕ} (hq : 0 < q) (hn : 0 < n) (y : ℂ) :
    aeval y (cycloScaled q n) = ∏ r' ∈ primitiveRoots n ℂ, (y - (q : ℂ) * r') := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have h := aeval_mul_cycloScaled q n (y / q)
  rw [mul_div_cancel₀ y hq0, aeval_cyclotomic_eq_prod hn] at h
  rw [h, ← Complex.card_primitiveRoots n, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r' _ => ?_
  field_simp

end RatBase

end PiFormula
