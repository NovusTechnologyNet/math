/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula.TheoremC

/-!
# Rational values are Galois invariant (milestone M7, part 2, first half)

Let `ρ` be a rational pattern of period 120 with `S(ρ) = q π`, `q` rational, and let
`d_r` be its coefficients, so that `S(ρ) = ∑ d_r Log(1 - r/t)`. The `d_r` lie in
`K = ℚ(ζ_120)`. This file proves, from Baker's theorem, that for every `b` prime to 120 with
`b ≡ 1 (mod 4)`

  `∑_a d(ζ^(ba)) Log(1 - ζ^a/t) = q π`                                (`conj_value`).

The proof:

* `baker_descent` over the field `K`: the relation `(q i)(iπ) + ∑ d_r Log(1 - r/t) = 0` is a
  combination, with coefficients in `K`, of integer relations among `iπ` and the logarithms;
* an embedding `σ : K → ℂ` applied to the coefficients of such a combination gives again a
  relation (`conj_relation`), because the integer relations do not move;
* for `σ(ζ) = ζ^b` with `b ≡ 1 (mod 4)`: `σ(i) = i`, and `σ(d(ζ^a)) = d(ζ^(ba))` since `ρ` is
  rational (`sigma_coeffK`).

The second half (`ExactArgs.lean`, `TheoremC2.lean`) turns these identities into five linear
constraints on the coefficient vector and concludes that the patterns with a rational
multiple of `π` form a space of dimension 8.
-/

@[expose] public section

open Complex Polynomial IntermediateField

namespace PiFormula

/-! ## 1. The field `ℚ(ζ_120)` and its embeddings -/

/-- `K = ℚ(ζ_120)` inside `ℂ`. -/
noncomputable abbrev K120 : IntermediateField ℚ ℂ := ℚ⟮ζ120⟯

/-- The generator `ζ_120` as an element of `K`. -/
noncomputable abbrev gK : K120 := AdjoinSimple.gen ℚ ζ120

theorem coe_gK : ((gK : K120) : ℂ) = ζ120 := AdjoinSimple.coe_gen ℚ ζ120

theorem isIntegral_ζ120 : IsIntegral ℚ ζ120 := (ζ120_prim.isIntegral (by norm_num)).tower_top

theorem isAlgebraic_of_mem_K120 {x : ℂ} (hx : x ∈ K120) : IsAlgebraic ℚ x := by
  have : Algebra.IsAlgebraic ℚ K120 := isAlgebraic_adjoin_simple isIntegral_ζ120
  have h1 : IsAlgebraic ℚ (algebraMap K120 ℂ ⟨x, hx⟩) :=
    (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : K120)).algebraMap
  exact h1

theorem ζ120_mem_K120 : ζ120 ∈ K120 := mem_adjoin_simple_self ℚ ζ120

theorem I_mem_K120 : I ∈ K120 := by
  rw [← ζ120_pow_30]
  exact K120.pow_mem ζ120_mem_K120 30

/-- For `b` prime to 120 there is an embedding of `ℚ(ζ_120)` with `ζ ↦ ζ^b`. -/
theorem exists_embedding {b : ℕ} (hb : Nat.Coprime b 120) :
    ∃ σ : K120 →ₐ[ℚ] ℂ, σ gK = ζ120 ^ b := by
  have hmin : minpoly ℚ ζ120 = cyclotomic 120 ℚ :=
    (cyclotomic_eq_minpoly_rat ζ120_prim (by norm_num)).symm
  have hroot : ζ120 ^ b ∈ (minpoly ℚ ζ120).aroots ℂ := by
    rw [mem_aroots, hmin]
    refine ⟨cyclotomic_ne_zero 120 ℚ, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (ζ120_prim.pow_of_coprime b hb).isRoot_cyclotomic (by norm_num)
  exact ⟨(algHomAdjoinIntegralEquiv ℚ isIntegral_ζ120).symm ⟨ζ120 ^ b, hroot⟩,
    algHomAdjoinIntegralEquiv_symm_apply_gen ℚ isIntegral_ζ120 _⟩

open Classical in
/-- An embedding `σ` of `K`, extended by zero to all of `ℂ`. -/
noncomputable def ext0 (σ : K120 →ₐ[ℚ] ℂ) (x : ℂ) : ℂ := if h : x ∈ K120 then σ ⟨x, h⟩ else 0

theorem ext0_of_mem (σ : K120 →ₐ[ℚ] ℂ) {x : ℂ} (h : x ∈ K120) : ext0 σ x = σ ⟨x, h⟩ := by
  simp only [ext0, h, ↓reduceDIte]

theorem ext0_coe (σ : K120 →ₐ[ℚ] ℂ) (y : K120) : ext0 σ (y : ℂ) = σ y :=
  ext0_of_mem σ y.2

theorem ext0_zero (σ : K120 →ₐ[ℚ] ℂ) : ext0 σ 0 = 0 := by
  have h := ext0_coe σ 0
  rwa [map_zero] at h

theorem ext0_add (σ : K120 →ₐ[ℚ] ℂ) {x y : ℂ} (hx : x ∈ K120) (hy : y ∈ K120) :
    ext0 σ (x + y) = ext0 σ x + ext0 σ y := by
  have h := ext0_coe σ ((⟨x, hx⟩ : K120) + ⟨y, hy⟩)
  rw [map_add] at h
  rw [ext0_of_mem σ hx, ext0_of_mem σ hy, ← h]
  rfl

theorem ext0_mul (σ : K120 →ₐ[ℚ] ℂ) {x y : ℂ} (hx : x ∈ K120) (hy : y ∈ K120) :
    ext0 σ (x * y) = ext0 σ x * ext0 σ y := by
  have h := ext0_coe σ ((⟨x, hx⟩ : K120) * ⟨y, hy⟩)
  rw [map_mul] at h
  rw [ext0_of_mem σ hx, ext0_of_mem σ hy, ← h]
  rfl

theorem ext0_intCast (σ : K120 →ₐ[ℚ] ℂ) (n : ℤ) : ext0 σ (n : ℂ) = n := by
  have h := ext0_coe σ ((n : ℤ) : K120)
  rw [map_intCast] at h
  exact_mod_cast h

theorem ext0_ratCast (σ : K120 →ₐ[ℚ] ℂ) (q : ℚ) : ext0 σ (q : ℂ) = q := by
  have h := ext0_coe σ ((q : ℚ) : K120)
  rw [map_ratCast] at h
  exact_mod_cast h

/-- If `σ(ζ) = ζ^b` with `b ≡ 1 (mod 4)`, then `σ(i) = i`. -/
theorem ext0_I {σ : K120 →ₐ[ℚ] ℂ} {b : ℕ} (hσ : σ gK = ζ120 ^ b) (hb4 : b % 4 = 1) :
    ext0 σ I = I := by
  have h := ext0_coe σ (gK ^ 30)
  rw [map_pow, hσ, ← pow_mul, mul_comm, pow_mul, ζ120_pow_30, I_pow_of_mod_four hb4] at h
  have e : ((gK ^ 30 : K120) : ℂ) = I := by
    rw [IntermediateField.coe_pow, coe_gK, ζ120_pow_30]
  rw [e] at h
  exact h

/-! ## 2. Conjugating the coefficients of a relation among logarithms -/

/-- A combination of integer relations with coefficients in `K` has its values in `K`, and
remains a relation when the coefficients are conjugated. -/
theorem conj_relation (σ : K120 →ₐ[ℚ] ℂ) {ι : Type*} {T : Finset ι} {lam : ι → ℂ}
    {β : ι → ℂ} (h : SpanIn K120 (IntRel T lam) β) :
    (∀ i, β i ∈ K120) ∧ ∑ i ∈ T, ext0 σ (β i) * lam i = 0 := by
  induction h with
  | zero =>
    refine ⟨fun i => K120.zero_mem, ?_⟩
    simp only [Pi.zero_apply, ext0_zero, zero_mul, Finset.sum_const_zero]
  | step c hc v hv w _ ih =>
    obtain ⟨z, -, hzsum, hvz⟩ := hv
    obtain ⟨hwK, hwsum⟩ := ih
    have hvK : ∀ i, v i ∈ K120 := fun i => by rw [hvz]; exact K120.intCast_mem _
    refine ⟨fun i => K120.add_mem (K120.mul_mem hc (hvK i)) (hwK i), ?_⟩
    have e : ∀ i, ext0 σ (c * v i + w i) * lam i =
        ext0 σ c * ((z i : ℂ) * lam i) + ext0 σ (w i) * lam i := fun i => by
      rw [ext0_add σ (K120.mul_mem hc (hvK i)) (hwK i), ext0_mul σ hc (hvK i), hvz,
        ext0_intCast]
      ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hzsum, hwsum, mul_zero, add_zero]

/-- **Baker's theorem and Galois conjugation.** Let `∑ d_r Log(1 - r/t) = q π` with `q`
rational and the `d_r` in `K = ℚ(ζ_120)`. If `σ` is an embedding of `K` fixing `i`, the identity
remains true with `σ(d_r)` in place of `d_r`. -/
theorem baker_galois (hB : BakerTheorem) {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {d : ℂ → ℂ} (hd : ∀ r ∈ S, d r ∈ K120) {q : ℚ} (σ : K120 →ₐ[ℚ] ℂ) (hσI : ext0 σ I = I)
    (h : ∑ r ∈ S, d r * Complex.log (1 - r / tC) = q * Real.pi) :
    ∑ r ∈ S, ext0 σ (d r) * Complex.log (1 - r / tC) = q * Real.pi := by
  classical
  let β : Option ℂ → ℂ := fun o =>
    match o with
    | none => q * I
    | some r => if r ∈ S then d r else 0
  have hβS : ∀ r ∈ S, β (some r) = d r := fun r hr => by simp only [β, hr, ↓reduceIte]
  have hqK : (q : ℂ) ∈ K120 := by
    have h1 := K120.algebraMap_mem q
    rwa [eq_ratCast] at h1
  have hspan : SpanIn K120 (IntRel (Finset.insertNone S) lamOf) β := by
    refine baker_descent hB K120 (fun x hx => isAlgebraic_of_mem_K120 hx) lamOf _
      (isAlgebraic_exp_lamOf hS) β ?_ ?_ ?_
    · intro i hi
      rcases i with _ | r
      · exact K120.mul_mem hqK I_mem_K120
      · rw [hβS r (Finset.some_mem_insertNone.1 hi)]
        exact hd r (Finset.some_mem_insertNone.1 hi)
    · intro i hi
      rcases i with _ | r
      · exact absurd (by simp) hi
      · have hr : r ∉ S := fun hr => hi (Finset.some_mem_insertNone.2 hr)
        simp only [β, hr, ↓reduceIte]
    · rw [Finset.sum_insertNone]
      have e : ∑ r ∈ S, β (some r) * lamOf (some r) =
          ∑ r ∈ S, d r * Complex.log (1 - r / tC) :=
        Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
      rw [e, h]
      change (q : ℂ) * I * (Real.pi * I) + q * Real.pi = 0
      linear_combination (q : ℂ) * Real.pi * Complex.I_sq
  obtain ⟨-, hsum⟩ := conj_relation σ hspan
  rw [Finset.sum_insertNone] at hsum
  have e1 : ext0 σ (β none) * lamOf none = (q : ℂ) * I * (Real.pi * I) := by
    change ext0 σ ((q : ℂ) * I) * (Real.pi * I) = _
    rw [ext0_mul σ hqK I_mem_K120, ext0_ratCast, hσI]
  have e2 : ∑ r ∈ S, ext0 σ (β (some r)) * lamOf (some r) =
      ∑ r ∈ S, ext0 σ (d r) * Complex.log (1 - r / tC) :=
    Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
  rw [e1, e2] at hsum
  linear_combination hsum - (q : ℂ) * Real.pi * Complex.I_sq

/-! ## 3. The coefficients of a rational pattern lie in `K` -/

/-- The coefficient `d(ζ^a)` of a rational pattern of period 120, as an element of `K`. -/
noncomputable def coeffK (ρ : ℕ → ℚ) (a : ℕ) : K120 :=
  -(1 / ((120 : ℕ) : K120) * ∑ m ∈ Finset.range 120,
    (((ρ m : ℚ) : K120) * ((1 + gK ^ 30) ^ (m % 2) * (gK ^ 30) ^ (m / 2))) * ((gK ^ a)⁻¹) ^ m)

theorem coe_coeffK (ρ : ℕ → ℚ) (a : ℕ) :
    ((coeffK ρ a : K120) : ℂ) = fourierD 120 ρ (ζ120 ^ a) := by
  have hι : algebraMap K120 ℂ gK = ζ120 := coe_gK
  change algebraMap K120 ℂ (coeffK ρ a) = _
  simp only [coeffK, map_neg, map_mul, map_div₀, map_one, map_natCast, map_sum, map_ratCast,
    map_pow, map_inv₀, map_add, hι, ζ120_pow_30]
  rfl

theorem sigma_coeffK {σ : K120 →ₐ[ℚ] ℂ} {b : ℕ} (hσ : σ gK = ζ120 ^ b) (hb4 : b % 4 = 1)
    (ρ : ℕ → ℚ) (a : ℕ) : σ (coeffK ρ a) = fourierD 120 ρ (ζ120 ^ (b * a)) := by
  have h30 : (ζ120 ^ b) ^ 30 = I := by
    rw [← pow_mul, mul_comm, pow_mul, ζ120_pow_30, I_pow_of_mod_four hb4]
  simp only [coeffK, map_neg, map_mul, map_div₀, map_one, map_natCast, map_sum, map_ratCast,
    map_pow, map_inv₀, map_add, hσ, h30]
  rw [← pow_mul]
  rfl

theorem fourierD_mem_K120 (ρ : ℕ → ℚ) (a : ℕ) : fourierD 120 ρ (ζ120 ^ a) ∈ K120 := by
  rw [← coe_coeffK]
  exact (coeffK ρ a).2

/-! ## 4. Rational values are Galois invariant -/

theorem zetaN_120 : zetaN 120 = ζ120 := by
  rw [zetaN, ζ120]
  norm_num

/-- **Rational values are Galois invariant (from Baker's theorem).** If the series of a rational
pattern `ρ` of period 120 is `q π` with `q` rational, then for every `b` prime to 120 with
`b ≡ 1 (mod 4)` the conjugated sum `∑_a d(ζ^(ba)) Log(1 - ζ^a/t)` is `q π` too. -/
theorem conj_value (hB : BakerTheorem) {ρ : ℕ → ℚ} (hp : ∀ k, ρ (k + 120) = ρ k) {q : ℚ}
    (h : HasSum (seriesTerm ρ) (q * Real.pi)) {b : ℕ} (hb : Nat.Coprime b 120)
    (hb4 : b % 4 = 1) :
    ∑ a ∈ Finset.range 120, fourierD 120 ρ (ζ120 ^ (b * a)) * Complex.log (wJ a) =
      q * Real.pi := by
  have hC : HasSum (fun k : ℕ => (ρ k : ℂ) / 2 ^ (k / 2) / k) ((q : ℂ) * Real.pi) := by
    have h2 := Complex.hasSum_ofReal.2 h
    simp only [seriesTerm] at h2
    push_cast at h2
    exact h2
  have h1 := (series_eq_logs (N := 120) (by norm_num) (by norm_num) hp).unique hC
  obtain ⟨σ, hσ⟩ := exists_embedding hb
  have hmem : ∀ r ∈ rootsN 120, fourierD 120 ρ r ∈ K120 := by
    intro r hr
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hr
    rw [zetaN_120]
    exact fourierD_mem_K120 ρ a
  have h2 := baker_galois hB (fun r hr => isOfFinOrder_of_mem_rootsN (by norm_num) hr) hmem σ
    (ext0_I hσ hb4) h1
  rw [sum_rootsN (by norm_num), zetaN_120] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← coe_coeffK ρ a, ext0_coe, sigma_coeffK hσ hb4]
  rfl

end PiFormula
