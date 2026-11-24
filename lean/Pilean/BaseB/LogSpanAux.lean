/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.BaseB.LogDefs

/-!
# The norm of `1 - r/√b` and the numbers `ν(r)²` (auxiliary)

For the file `LogSpan`. Let `L` be a field that is an algebra over `ℚ`. (No finiteness is
assumed: if `L` is not finite over `ℚ` the norm is `1` and the degrees are `0`.)

* `norm_sq_eq_eval_zero_pow` (private): for an algebraic integer `x` of `L`, with `c₀` the
  constant term of its minimal polynomial over `ℤ`, `Norm_{L/ℚ}(x)² = c₀^(2 [L : ℚ(x)])`. (The
  norm is `((-1)^d c₀)^[L : ℚ(x)]`, by the norm in the tower `ℚ ⊆ ℚ(x) ⊆ L` and the norm of the
  generator of a power basis; the square removes the sign.)
* `norm_one_sub_div_sq`: if `t² = b` and `t - r` is an algebraic integer, then
  `Norm_{L/ℚ}(1 - r/t)² = (c₀² / b^d)^[L : ℚ(t - r)]`, with `c₀` and `d` the constant term and
  the degree of the minimal polynomial of `t - r` over `ℤ` (`Norm(t)² = b^[L : ℚ]` and the tower
  law `d [L : ℚ(t - r)] = [L : ℚ]`).
* `norm_one_sub_div_sq_eq_nuSq`: the same when `L` has an embedding `φ` in `ℂ` with
  `φ(t) = √b` and `φ(s) = r`: `Norm_{L/ℚ}(1 - s/t)² = ν(r)²^m` for some natural number `m`.
-/

@[expose] public section

open Polynomial Module IntermediateField

namespace PiFormula

namespace BaseB

section Generic

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The norm of an algebraic element `x`, from the constant term `c₀` and the degree `d` of its
minimal polynomial: `Norm_{L/K}(x) = ((-1)^d c₀)^[L : K(x)]`. -/
private theorem norm_eq_coeff_zero_pow {x : L} (hx : IsIntegral K x) :
    Algebra.norm K x =
      ((-1) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0) ^ finrank K⟮x⟯ L := by
  have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (adjoin.powerBasis hx)
  rw [adjoin.powerBasis_gen, adjoin.powerBasis_dim, minpoly_gen] at h
  rw [Algebra.norm_eq_norm_adjoin K x, h]

/-- The tower law for `K ⊆ K(x) ⊆ L`. -/
private theorem natDegree_minpoly_mul_finrank_adjoin {x : L} (hx : IsIntegral K x) :
    (minpoly K x).natDegree * finrank K⟮x⟯ L = finrank K L := by
  rw [← adjoin.finrank hx]
  exact Module.finrank_mul_finrank K K⟮x⟯ L

end Generic

section Norm

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The square of the norm of an algebraic integer `x` is a power of the square of the constant
term of its minimal polynomial over `ℤ`. -/
private theorem norm_sq_eq_eval_zero_pow {x : L} (hx : IsIntegral ℤ x) :
    Algebra.norm ℚ x ^ 2 = (((minpoly ℤ x).eval 0 : ℤ) : ℚ) ^ (2 * finrank ℚ⟮x⟯ L) := by
  have hmin : minpoly ℚ x = (minpoly ℤ x).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx
  have hc : (minpoly ℚ x).coeff 0 = (((minpoly ℤ x).eval 0 : ℤ) : ℚ) := by
    rw [hmin, coeff_map, coeff_zero_eq_eval_zero]
    rfl
  rw [norm_eq_coeff_zero_pow hx.tower_top, hc, ← pow_mul, mul_comm _ 2, pow_mul, mul_pow,
    ← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow, one_mul, ← pow_mul]

/-- The tower law for `ℚ ⊆ ℚ(x) ⊆ L`, with the degree of the minimal polynomial over `ℤ`. -/
private theorem natDegree_minpoly_mul_finrank {x : L} (hx : IsIntegral ℤ x) :
    (minpoly ℤ x).natDegree * finrank ℚ⟮x⟯ L = finrank ℚ L := by
  have hmin : minpoly ℚ x = (minpoly ℤ x).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx
  rw [← (minpoly.monic hx).natDegree_map (algebraMap ℤ ℚ), ← hmin]
  exact natDegree_minpoly_mul_finrank_adjoin hx.tower_top

/-- **The norm of `1 - r/t`.** If `t² = b` and `t - r` is an algebraic integer, with minimal
polynomial over `ℤ` of degree `d` and constant term `c₀`, then
`Norm_{L/ℚ}(1 - r/t)² = (c₀² / b^d)^[L : ℚ(t - r)]`. -/
theorem norm_one_sub_div_sq {b : ℕ} (hb : b ≠ 0) {t r : L} (ht : t ^ 2 = (b : L))
    (hx : IsIntegral ℤ (t - r)) :
    Algebra.norm ℚ (1 - r / t) ^ 2 =
      ((((minpoly ℤ (t - r)).eval 0 : ℤ) : ℚ) ^ 2 /
        (b : ℚ) ^ (minpoly ℤ (t - r)).natDegree) ^ finrank ℚ⟮t - r⟯ L := by
  have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb
  have hbL : (b : L) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ L) b]
    exact (map_ne_zero (algebraMap ℚ L)).2 hbQ
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0] at ht
    exact hbL (by rw [← ht]; ring)
  have hnt : Algebra.norm ℚ t ^ 2 = (b : ℚ) ^ finrank ℚ L := by
    rw [← MonoidHom.map_pow, ht, ← Algebra.norm_algebraMap (S := L) (b : ℚ),
      map_natCast (algebraMap ℚ L) b]
  have hmul : Algebra.norm ℚ (1 - r / t) * Algebra.norm ℚ t = Algebra.norm ℚ (t - r) := by
    rw [← map_mul]
    congr 1
    field_simp
  rw [div_pow, ← pow_mul, ← pow_mul, natDegree_minpoly_mul_finrank hx, ← hnt,
    ← norm_sq_eq_eval_zero_pow hx, ← hmul, mul_pow,
    mul_div_cancel_right₀ _ (by rw [hnt]; exact pow_ne_zero _ hbQ)]

end Norm

/-- **The norm of `1 - r/√b` is, up to a power and a square, the number `ν(r)²`.** Let `L` be
a field, finite or not over `ℚ`, with an embedding `φ` in `ℂ`, and let `t`, `s` be elements of
`L` with images `√b` and `r`, where `√b - r` is an algebraic integer. Then
`Norm_{L/ℚ}(1 - s/t)² = ν(r)²^m` for some natural number `m`. -/
theorem norm_one_sub_div_sq_eq_nuSq {L : Type*} [Field L] [Algebra ℚ L] (φ : L →+* ℂ) {b : ℕ}
    (hb : 2 ≤ b) {t s : L} (ht : φ t = tB b) {r : ℂ} (hs : φ s = r)
    (hx : IsIntegral ℤ (tB b - r)) :
    ∃ m : ℕ, Algebra.norm ℚ (1 - s / t) ^ 2 = nuSq b r ^ m := by
  have hφ : Function.Injective φ := φ.injective
  have hsq : t ^ 2 = (b : L) := hφ (by rw [map_pow, ht, tB_sq, map_natCast])
  have himg : φ.toIntAlgHom (t - s) = tB b - r := by
    change φ (t - s) = tB b - r
    rw [map_sub, ht, hs]
  have hmin : minpoly ℤ (t - s) = minpoly ℤ (tB b - r) := by
    rw [← himg]
    exact (minpoly.algHom_eq φ.toIntAlgHom hφ _).symm
  have hx' : IsIntegral ℤ (t - s) := by
    rw [← himg] at hx
    exact (isIntegral_algHom_iff φ.toIntAlgHom hφ).1 hx
  refine ⟨finrank ℚ⟮t - s⟯ L, ?_⟩
  rw [norm_one_sub_div_sq (by omega) hsq hx', hmin]
  rfl

end BaseB

end PiFormula
