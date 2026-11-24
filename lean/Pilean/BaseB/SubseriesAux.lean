module

public import Pilean.BaseB.GeneralDefs

/-!
# Tools for the sub-series lemma

Three tools that do not depend on the base, used by `Subseries`:

* `hasSum_periodic_logs`: for a complex pattern `g` of period `P` and `‖x‖ < 1`,

    `∑_{k ≥ 1} g(k) x^k / k = -∑_{r^P = 1} D_r Log(1 - r x)`,   `D_r = coeffAt P g r`

  (finite Fourier inversion, as in `Fourier.lean`, for any pattern and any point);
* `extF`, `conj_relationF`: an embedding `σ` of a subfield `F` of `ℂ`, applied to the
  coefficients of a combination of integer relations, gives again a relation (as `ext0` and
  `conj_relation` of `GaloisValue.lean`, for any `F`);
* `baker_galoisF`: from Baker's theorem, if `∑ d_r L_r = q π` with `q` rational, the `L_r`
  logarithms of algebraic numbers and the `d_r` in a field `F` of algebraic numbers that
  contains `i`, then `∑ σ(d_r) L_r = q π` for every embedding `σ` of `F` that fixes `i`.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace BaseB

/-! ## 1. A periodic power series as a combination of logarithms -/

/-- For a complex pattern `g` of period `P` and a point `x` with `‖x‖ < 1`,
`∑_k g(k) x^k / k = -∑_{r^P = 1} D_r Log(1 - r x)` with `D_r = coeffAt P g r`. -/
theorem hasSum_periodic_logs {P : ℕ} (hP : 0 < P) {g : ℕ → ℂ} (hg : ∀ k, g (k + P) = g k)
    {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ => g k * x ^ k / k)
      (∑ r ∈ rootsN P, -coeffAt P g r * Complex.log (1 - r * x)) := by
  rw [sum_rootsN hP]
  have hterm : ∀ a ∈ Finset.range P,
      HasSum (fun k : ℕ => -coeffAt P g (zetaN P ^ a) * -((zetaN P ^ a * x) ^ k / k))
        (-coeffAt P g (zetaN P ^ a) * Complex.log (1 - zetaN P ^ a * x)) := by
    intro a _
    have hr : ‖zetaN P ^ a‖ = 1 := norm_root (isOfFinOrder_zetaN_pow hP a)
    have hrx : ‖zetaN P ^ a * x‖ < 1 := by rwa [norm_mul, hr, one_mul]
    have h := (hasSum_taylorSeries_neg_log hrx).neg
    rw [neg_neg] at h
    exact h.mul_left _
  have hfun : (fun k : ℕ => g k * x ^ k / k) = fun k : ℕ =>
      ∑ a ∈ Finset.range P, -coeffAt P g (zetaN P ^ a) * -((zetaN P ^ a * x) ^ k / k) := by
    funext k
    have e : ∑ a ∈ Finset.range P, -coeffAt P g (zetaN P ^ a) * -((zetaN P ^ a * x) ^ k / k) =
        (∑ a ∈ Finset.range P, coeffAt P g (zetaN P ^ a) * (zetaN P ^ a) ^ k) * x ^ k / k := by
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [e, fourier_inversion hP hg k]
  rw [hfun]
  exact hasSum_sum hterm

/-! ## 2. An embedding of a subfield, extended by zero -/

open Classical in
/-- An embedding `σ` of a subfield `F` of `ℂ`, extended by zero to all of `ℂ`. -/
noncomputable def extF {F : IntermediateField ℚ ℂ} (σ : F →ₐ[ℚ] ℂ) (x : ℂ) : ℂ :=
  if h : x ∈ F then σ ⟨x, h⟩ else 0

section ext

variable {F : IntermediateField ℚ ℂ} (σ : F →ₐ[ℚ] ℂ)

theorem extF_of_mem {x : ℂ} (h : x ∈ F) : extF σ x = σ ⟨x, h⟩ := by
  simp only [extF, h, ↓reduceDIte]

theorem extF_coe (y : F) : extF σ (y : ℂ) = σ y := extF_of_mem σ y.2

theorem extF_zero : extF σ 0 = 0 := by
  have h := extF_coe σ 0
  rwa [map_zero] at h

theorem extF_add {x y : ℂ} (hx : x ∈ F) (hy : y ∈ F) :
    extF σ (x + y) = extF σ x + extF σ y := by
  have h := extF_coe σ ((⟨x, hx⟩ : F) + ⟨y, hy⟩)
  rw [map_add] at h
  rw [extF_of_mem σ hx, extF_of_mem σ hy, ← h]
  rfl

theorem extF_mul {x y : ℂ} (hx : x ∈ F) (hy : y ∈ F) :
    extF σ (x * y) = extF σ x * extF σ y := by
  have h := extF_coe σ ((⟨x, hx⟩ : F) * ⟨y, hy⟩)
  rw [map_mul] at h
  rw [extF_of_mem σ hx, extF_of_mem σ hy, ← h]
  rfl

theorem extF_intCast (n : ℤ) : extF σ (n : ℂ) = n := by
  have h := extF_coe σ ((n : ℤ) : F)
  rw [map_intCast] at h
  exact_mod_cast h

theorem extF_ratCast (q : ℚ) : extF σ (q : ℂ) = q := by
  have h := extF_coe σ ((q : ℚ) : F)
  rw [map_ratCast] at h
  exact_mod_cast h

/-- A combination of integer relations with coefficients in `F` has its values in `F`, and
remains a relation when the coefficients are conjugated. -/
theorem conj_relationF {ι : Type*} {T : Finset ι} {lam : ι → ℂ} {β : ι → ℂ}
    (h : SpanIn F (IntRel T lam) β) :
    (∀ i, β i ∈ F) ∧ ∑ i ∈ T, extF σ (β i) * lam i = 0 := by
  induction h with
  | zero =>
    refine ⟨fun i => F.zero_mem, ?_⟩
    simp only [Pi.zero_apply, extF_zero, zero_mul, Finset.sum_const_zero]
  | step c hc v hv w _ ih =>
    obtain ⟨z, -, hzsum, hvz⟩ := hv
    obtain ⟨hwF, hwsum⟩ := ih
    have hvF : ∀ i, v i ∈ F := fun i => by rw [hvz]; exact F.intCast_mem _
    refine ⟨fun i => F.add_mem (F.mul_mem hc (hvF i)) (hwF i), ?_⟩
    have e : ∀ i, extF σ (c * v i + w i) * lam i =
        extF σ c * ((z i : ℂ) * lam i) + extF σ (w i) * lam i := fun i => by
      rw [extF_add σ (F.mul_mem hc (hvF i)) (hwF i), extF_mul σ hc (hvF i), hvz,
        extF_intCast]
      ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hzsum, hwsum, mul_zero, add_zero]

end ext

/-! ## 3. Baker's theorem and Galois conjugation, over any field of algebraic numbers -/

/-- The logarithms: `iπ` at `none`, and `L r` at `some r`. -/
noncomputable def lamL (L : ℂ → ℂ) : Option ℂ → ℂ
  | none => Real.pi * I
  | some r => L r

/-- **Baker's theorem and Galois conjugation.** Let `∑ d_r L_r = q π` with `q` rational, the
`L_r` logarithms of algebraic numbers, and the `d_r` in a field `F` of algebraic numbers that
contains `i`. If `σ` is an embedding of `F` fixing `i`, the identity remains true with `σ(d_r)`
in place of `d_r`. -/
theorem baker_galoisF (hB : BakerTheorem) {F : IntermediateField ℚ ℂ}
    (hF : ∀ x ∈ F, IsAlgebraic ℚ x) (hI : I ∈ F) {S : Finset ℂ} {L : ℂ → ℂ}
    (hL : ∀ r ∈ S, IsAlgebraic ℚ (Complex.exp (L r))) {d : ℂ → ℂ} (hd : ∀ r ∈ S, d r ∈ F)
    {q : ℚ} (σ : F →ₐ[ℚ] ℂ) (hσI : extF σ I = I)
    (h : ∑ r ∈ S, d r * L r = q * Real.pi) :
    ∑ r ∈ S, extF σ (d r) * L r = q * Real.pi := by
  classical
  let β : Option ℂ → ℂ := fun o =>
    match o with
    | none => q * I
    | some r => if r ∈ S then d r else 0
  have hβS : ∀ r ∈ S, β (some r) = d r := fun r hr => by simp only [β, hr, ↓reduceIte]
  have hqF : (q : ℂ) ∈ F := by
    have h1 := F.algebraMap_mem q
    rwa [eq_ratCast] at h1
  have hexp : ∀ i ∈ Finset.insertNone S, IsAlgebraic ℚ (Complex.exp (lamL L i)) := by
    intro i hi
    rcases i with _ | r
    · change IsAlgebraic ℚ (Complex.exp (Real.pi * I))
      rw [Complex.exp_pi_mul_I]
      exact isAlgebraic_one.neg
    · exact hL r (Finset.some_mem_insertNone.1 hi)
  have hspan : SpanIn F (IntRel (Finset.insertNone S) (lamL L)) β := by
    refine baker_descent hB F hF (lamL L) _ hexp β ?_ ?_ ?_
    · intro i hi
      rcases i with _ | r
      · exact F.mul_mem hqF hI
      · rw [hβS r (Finset.some_mem_insertNone.1 hi)]
        exact hd r (Finset.some_mem_insertNone.1 hi)
    · intro i hi
      rcases i with _ | r
      · exact absurd (by simp) hi
      · have hr : r ∉ S := fun hr => hi (Finset.some_mem_insertNone.2 hr)
        simp only [β, hr, ↓reduceIte]
    · rw [Finset.sum_insertNone]
      have e : ∑ r ∈ S, β (some r) * lamL L (some r) = ∑ r ∈ S, d r * L r :=
        Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
      rw [e, h]
      change (q : ℂ) * I * (Real.pi * I) + q * Real.pi = 0
      linear_combination (q : ℂ) * Real.pi * Complex.I_sq
  obtain ⟨-, hsum⟩ := conj_relationF σ hspan
  rw [Finset.sum_insertNone] at hsum
  have e1 : extF σ (β none) * lamL L none = (q : ℂ) * I * (Real.pi * I) := by
    change extF σ ((q : ℂ) * I) * (Real.pi * I) = _
    rw [extF_mul σ hqF hI, extF_ratCast, hσI]
  have e2 : ∑ r ∈ S, extF σ (β (some r)) * lamL L (some r) = ∑ r ∈ S, extF σ (d r) * L r :=
    Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
  rw [e1, e2] at hsum
  linear_combination hsum - (q : ℂ) * Real.pi * Complex.I_sq

end BaseB

end PiFormula
