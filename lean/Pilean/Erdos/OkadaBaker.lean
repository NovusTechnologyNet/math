module

public import Pilean.Erdos.OkadaDefs
public import Pilean.PiFormula.Unconditional
public import Pilean.BaseB.SubseriesAux

/-!
# Okada's criterion: Baker's theorem and the Galois group of `ℚ(ζ_q)`

`okadaBakerTwist : OkadaBakerTwist`: for `f : ℤ/q → ℚ` with Fourier transform `f^`, if

  `∑_{a ≠ 0} f^(a) Log(1 - ζ^a) = 0`,   `ζ = e^(2πi/q)`,

then `∑_{a ≠ 0} f^(h a) Log(1 - ζ^a) = 0` for every unit `h` modulo `q`.

Proof. The numbers `Log(1 - ζ^a)` are logarithms of algebraic numbers and the coefficients
`f^(a) = (1/q) ∑_r f(r) ζ^(-ar)` lie in `F = ℚ(ζ)` (`coeffF`, `coe_coeffF`). By Baker's
theorem in the form `baker_descent`, the relation is a combination with coefficients in `F`
of integer relations among the logarithms; so it remains true when an embedding `σ` of `F`
is applied to the coefficients (`BaseB.conj_relationF`). For `σ : ζ ↦ ζ^h`
(`exists_embedding_pow`; the cyclotomic polynomial is irreducible over `ℚ`),
`σ(f^(a)) = f^(h a)` because the values of `f` are rational.

This is the only place where Baker's theorem is used in the proof of Okada's criterion.
-/

@[expose] public section

open scoped BigOperators

open Polynomial IntermediateField

namespace PiFormula

namespace Erdos

namespace Okada

/-! ## 1. The root of unity `ζ = e^(2πi/q)` and the field `ℚ(ζ)` -/

/-- `ζ = e^(2πi/q)`, as the value at `1` of the standard additive character of `ℤ/q`. -/
noncomputable def zetaQ (q : ℕ) [NeZero q] : ℂ := ZMod.stdAddChar (1 : ZMod q)

theorem stdAddChar_natCast (q : ℕ) [NeZero q] (n : ℕ) :
    ZMod.stdAddChar ((n : ℕ) : ZMod q) = zetaQ q ^ n := by
  rw [zetaQ, ← nsmul_one n, AddChar.map_nsmul_eq_pow]

theorem stdAddChar_eq_pow (q : ℕ) [NeZero q] (x : ZMod q) :
    ZMod.stdAddChar x = zetaQ q ^ x.val := by
  rw [← stdAddChar_natCast, ZMod.natCast_zmod_val]

theorem zetaQ_prim (q : ℕ) [NeZero q] : IsPrimitiveRoot (zetaQ q) q := by
  have h := ZMod.stdAddChar_coe (N := q) 1
  have e : zetaQ q = Complex.exp (2 * Real.pi * Complex.I / q) := by
    rw [zetaQ]
    simpa using h
  rw [e]
  exact Complex.isPrimitiveRoot_exp q (NeZero.ne q)

theorem isIntegral_zetaQ (q : ℕ) [NeZero q] : IsIntegral ℚ (zetaQ q) :=
  ((zetaQ_prim q).isIntegral (Nat.pos_of_ne_zero (NeZero.ne q))).tower_top

/-- `F = ℚ(ζ)` inside `ℂ`. -/
noncomputable abbrev fieldQ (q : ℕ) [NeZero q] : IntermediateField ℚ ℂ := ℚ⟮zetaQ q⟯

/-- The generator `ζ` as an element of `F`. -/
noncomputable abbrev genQ (q : ℕ) [NeZero q] : fieldQ q := AdjoinSimple.gen ℚ (zetaQ q)

theorem isAlgebraic_of_mem_fieldQ (q : ℕ) [NeZero q] {x : ℂ} (hx : x ∈ fieldQ q) :
    IsAlgebraic ℚ x := by
  have : Algebra.IsAlgebraic ℚ (fieldQ q) := isAlgebraic_adjoin_simple (isIntegral_zetaQ q)
  have h1 : IsAlgebraic ℚ (algebraMap (fieldQ q) ℂ ⟨x, hx⟩) :=
    (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : fieldQ q)).algebraMap
  exact h1

/-- For `b` prime to `q` there is an embedding of `ℚ(ζ)` with `ζ ↦ ζ^b`. -/
theorem exists_embedding_pow (q : ℕ) [NeZero q] {b : ℕ} (hb : Nat.Coprime b q) :
    ∃ σ : fieldQ q →ₐ[ℚ] ℂ, σ (genQ q) = zetaQ q ^ b := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hmin : minpoly ℚ (zetaQ q) = cyclotomic q ℚ :=
    (cyclotomic_eq_minpoly_rat (zetaQ_prim q) hq).symm
  have hroot : zetaQ q ^ b ∈ (minpoly ℚ (zetaQ q)).aroots ℂ := by
    rw [mem_aroots, hmin]
    refine ⟨cyclotomic_ne_zero q ℚ, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact ((zetaQ_prim q).pow_of_coprime b hb).isRoot_cyclotomic hq
  exact ⟨(algHomAdjoinIntegralEquiv ℚ (isIntegral_zetaQ q)).symm ⟨zetaQ q ^ b, hroot⟩,
    algHomAdjoinIntegralEquiv_symm_apply_gen ℚ (isIntegral_zetaQ q) _⟩

/-! ## 2. The Fourier coefficients as elements of `ℚ(ζ)` -/

/-- The Fourier coefficient `f^(a)` as an element of `F = ℚ(ζ)`. -/
noncomputable def coeffF (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (a : ZMod q) : fieldQ q :=
  ((q : ℕ) : fieldQ q)⁻¹ * ∑ r : ZMod q, ((f r : ℚ) : fieldQ q) * genQ q ^ (-(a * r)).val

theorem algHom_coeffF (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (τ : fieldQ q →ₐ[ℚ] ℂ)
    (a : ZMod q) :
    τ (coeffF q f a) =
      (q : ℂ)⁻¹ * ∑ r : ZMod q, (f r : ℂ) * τ (genQ q) ^ (-(a * r)).val := by
  simp only [coeffF, map_mul, map_inv₀, map_sum, map_pow, map_natCast, map_ratCast]

theorem coe_coeffF (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (a : ZMod q) :
    ((coeffF q f a : fieldQ q) : ℂ) = fourierCoeff q f a := by
  have h := algHom_coeffF q f (fieldQ q).val a
  have hg : (fieldQ q).val (genQ q) = zetaQ q := AdjoinSimple.coe_gen ℚ (zetaQ q)
  rw [hg] at h
  unfold fourierCoeff
  simp only [stdAddChar_eq_pow]
  exact h

/-- The embedding `ζ ↦ ζ^h` sends `f^(a)` to `f^(h a)`. -/
theorem sigma_coeffF (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (h : (ZMod q)ˣ)
    {σ : fieldQ q →ₐ[ℚ] ℂ} (hσ : σ (genQ q) = zetaQ q ^ (h : ZMod q).val) (a : ZMod q) :
    σ (coeffF q f a) = fourierCoeff q f ((h : ZMod q) * a) := by
  rw [algHom_coeffF, hσ]
  unfold fourierCoeff
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  rw [← pow_mul, ← stdAddChar_natCast, Nat.cast_mul, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]
  congr 1
  ring

end Okada

open Okada

/-! ## 3. The theorem -/

/-- **Baker's theorem and the Galois group of `ℚ(ζ_q)`**: a vanishing linear form
`∑_{a ≠ 0} f^(a) Log(1 - ζ^a)` still vanishes when `f^(a)` is replaced by `f^(h a)`. -/
theorem okadaBakerTwist : OkadaBakerTwist := by
  intro q _ _ f _ _ hform h
  classical
  obtain ⟨σ, hσ⟩ := exists_embedding_pow q (ZMod.val_coe_unit_coprime h)
  let T : Finset (ZMod q) := Finset.univ.filter fun a => a ≠ 0
  let lam : ZMod q → ℂ := fun a => Complex.log (1 - ZMod.stdAddChar a)
  let β : ZMod q → ℂ := fun a => if a = 0 then 0 else ((coeffF q f a : fieldQ q) : ℂ)
  have hT0 : ∀ a ∈ T, a ≠ 0 := fun a ha => (Finset.mem_filter.1 ha).2
  have hT : ∀ c : ZMod q → ℂ, logForm q c = ∑ a ∈ T, c a * lam a := by
    intro c
    unfold logForm
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a = 0
    · simp only [ha, ↓reduceIte, ne_eq, not_true_eq_false]
    · simp only [ha, ↓reduceIte, ne_eq, not_false_eq_true, lam]
  have hβ : ∀ a ∈ T, β a = ((coeffF q f a : fieldQ q) : ℂ) := by
    intro a ha
    simp only [β, hT0 a ha, ↓reduceIte]
  have hexp : ∀ a ∈ T, IsAlgebraic ℚ (Complex.exp (lam a)) := by
    intro a ha
    have hne : (1 : ℂ) - ZMod.stdAddChar a ≠ 0 := fun h0 =>
      hT0 a ha (ZMod.injective_stdAddChar (by
        rw [AddChar.map_zero_eq_one]
        exact (sub_eq_zero.1 h0).symm))
    change IsAlgebraic ℚ (Complex.exp (Complex.log (1 - ZMod.stdAddChar a)))
    rw [Complex.exp_log hne, stdAddChar_eq_pow]
    exact isAlgebraic_one.sub ((isIntegral_zetaQ q).isAlgebraic.pow _)
  have hβF : ∀ a ∈ T, β a ∈ fieldQ q := by
    intro a ha
    rw [hβ a ha]
    exact (coeffF q f a).2
  have hβ0 : ∀ a, a ∉ T → β a = 0 := by
    intro a ha
    have ha0 : a = 0 := by
      by_contra hne
      exact ha (Finset.mem_filter.2 ⟨Finset.mem_univ a, hne⟩)
    simp only [β, ha0, ↓reduceIte]
  have hsum : ∑ a ∈ T, β a * lam a = 0 := by
    rw [← hform, hT]
    exact Finset.sum_congr rfl fun a ha => by rw [hβ a ha, coe_coeffF]
  have hspan := baker_descent bakerTheorem (fieldQ q)
    (fun x hx => isAlgebraic_of_mem_fieldQ q hx) lam T hexp β hβF hβ0 hsum
  obtain ⟨-, hconj⟩ := BaseB.conj_relationF σ hspan
  rw [hT, ← hconj]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [hβ a ha, BaseB.extF_coe, sigma_coeffF q f h hσ]

end Erdos

end PiFormula
