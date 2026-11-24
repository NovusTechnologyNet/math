/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.BaseB.LogWeightFacts

/-!
# The minimal polynomial of `√b - r`: degree, and the non-primitive primes

Notation of `LogWeightFacts`: `t = √b`, `r` a root of unity of order `n`, `m` the order of
`r²`, `c₀(r)` and `d(r)` the constant term and the degree of the minimal polynomial `μ_r` of
`t - r` over `ℤ`.

* `natDegree_minpoly_le`: `d(r) ≤ 2 φ(n)`, and in case of equality `c₀(r) = Φ_n(t) Φ_n(-t)`
  (then `μ_r` is the symmetrization of `Φ_n`).
* `two_mul_totient_le_natDegree`: `d(r) ≥ 2 φ(n)` when `A(r) + t B(r) = 0` with `A, B ∈ ℤ[X]`
  forces `A(r) = B(r) = 0`.
* `low_data`: for a non-square `b` and `r⁴ = 1`: `m = 1`, `|c₀| = b - 1`, `d = 2` (`r = ±1`), or
  `m = 2`, `|c₀| = (b + 1)²`, `d = 4` (`r = ±i`).
* **F2** (`high_data`): for `r⁴ ≠ 1` there is `k ∈ {1, 2}` with `k φ(m) ≤ d(r) ≤ 2 k φ(m)`; a
  prime `q ∣ m` divides `c₀(r)` at most `k` times; and if `d(r) = 2 k φ(m)` then every prime of
  `c₀(r)` divides it at least `k` times (`c₀(r) = Φ_m(b)^k`).
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace BaseB

theorem cAbs_ne_zero {b : ℕ} (hb : 2 ≤ b) {r : ℂ} (hr : IsOfFinOrder r) : cAbs b r ≠ 0 := by
  have hx := isIntegral_tB_sub b hr
  have h0 : tB b - r ≠ 0 := tB_sub_ne_zero hb (norm_root hr)
  have h1 := minpoly.coeff_zero_ne_zero (A := ℚ) hx.tower_top h0
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx, coeff_map] at h1
  intro h
  apply h1
  rw [cAbs, Int.natAbs_eq_zero] at h
  rw [coeff_zero_eq_eval_zero, h, map_zero]

/-! ## 1. The degree is at most `2 φ(n)` -/

/-- `d(r) ≤ 2 φ(n)`; in case of equality, `c₀(r) = Φ_n(√b) Φ_n(-√b)`. -/
theorem natDegree_minpoly_le (b : ℕ) {r : ℂ} (hr : IsOfFinOrder r) :
    (minpoly ℤ (tB b - r)).natDegree ≤ 2 * (orderOf r).totient ∧
      ((minpoly ℤ (tB b - r)).natDegree = 2 * (orderOf r).totient →
        (((minpoly ℤ (tB b - r)).eval 0 : ℤ) : ℂ) =
          aeval (tB b) (cyclotomic (orderOf r) ℤ) * aeval (-tB b) (cyclotomic (orderOf r) ℤ)) := by
  classical
  obtain ⟨n, hndef⟩ : ∃ n, orderOf r = n := ⟨_, rfl⟩
  rw [hndef]
  have hn : 0 < n := hndef ▸ hr.orderOf_pos
  have hprim : IsPrimitiveRoot r n := hndef ▸ IsPrimitiveRoot.orderOf r
  have hx := isIntegral_tB_sub b hr
  have hμ := minpoly.monic hx
  obtain ⟨F, hF⟩ := exists_symmetrize b (cyclotomic n ℤ)
  have hFx : aeval (tB b - r) F = 0 := by
    rw [hF, sub_sub_cancel, aeval_cyclotomic_eq_zero hprim hn, zero_mul]
  have hdvd := minpoly.isIntegrallyClosed_dvd hx hFx
  -- over `ℂ`: `F = ∏ (X - (t - r')) ∏ (X - (-t - r'))`
  have hΦ : ∀ w : ℂ, aeval w (cyclotomic n ℤ) = ∏ r' ∈ primitiveRoots n ℂ, (w - r') := by
    intro w
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic,
      cyclotomic_eq_prod_X_sub_primitiveRoots hprim, eval_prod]
    simp
  have hFc : F.map (algebraMap ℤ ℂ) = (∏ r' ∈ primitiveRoots n ℂ, (X - C (tB b - r'))) *
      ∏ r' ∈ primitiveRoots n ℂ, (X - C (-tB b - r')) := by
    apply Polynomial.funext
    intro z
    rw [eval_map_algebraMap, hF z, hΦ, hΦ, eval_mul, eval_prod, eval_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r' _ => ?_
    simp only [eval_sub, eval_X, eval_C]
    ring
  have hmon1 : (∏ r' ∈ primitiveRoots n ℂ, (X - C (tB b - r'))).Monic :=
    monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hmon2 : (∏ r' ∈ primitiveRoots n ℂ, (X - C (-tB b - r'))).Monic :=
    monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hinj : Function.Injective (algebraMap ℤ ℂ) := (algebraMap ℤ ℂ).injective_int
  have hmonF : F.Monic := monic_of_injective hinj (hFc ▸ hmon1.mul hmon2)
  have hdegF : F.natDegree = 2 * n.totient := by
    rw [← natDegree_map_eq_of_injective hinj, hFc, hmon1.natDegree_mul hmon2,
      natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _,
      natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
      Complex.card_primitiveRoots]
    ring
  constructor
  · rw [← hdegF]
    exact natDegree_le_of_dvd hdvd hmonF.ne_zero
  · intro hdeg
    have hFμ : F = minpoly ℤ (tB b - r) :=
      eq_of_monic_of_dvd_of_natDegree_le hμ hmonF hdvd (by rw [hdegF, hdeg])
    have h0 := hF 0
    rw [sub_zero, sub_zero, hFμ, aeval_zero_int] at h0
    exact h0

/-! ## 2. The degree is `2 φ(n)` when `√b` is independent of `r` -/

/-- If `A(r) + √b B(r) = 0` with `A, B ∈ ℤ[X]` forces `A(r) = B(r) = 0`, then
`d(r) ≥ 2 φ(n)`. -/
theorem two_mul_totient_le_natDegree {b : ℕ} (hb : 2 ≤ b) {r : ℂ} (hr : IsOfFinOrder r)
    (hind : ∀ A B : ℤ[X], aeval r A + tB b * aeval r B = 0 → aeval r A = 0 ∧ aeval r B = 0) :
    2 * (orderOf r).totient ≤ (minpoly ℤ (tB b - r)).natDegree := by
  classical
  obtain ⟨n, hndef⟩ : ∃ n, orderOf r = n := ⟨_, rfl⟩
  rw [hndef]
  have hn : 0 < n := hndef ▸ hr.orderOf_pos
  have hprim : IsPrimitiveRoot r n := hndef ▸ IsPrimitiveRoot.orderOf r
  have hμ := minpoly.monic (isIntegral_tB_sub b hr)
  obtain ⟨μ, hμdef⟩ : ∃ μ, minpoly ℤ (tB b - r) = μ := ⟨_, rfl⟩
  rw [hμdef] at hμ ⊢
  have hμx : aeval (tB b - r) μ = 0 := hμdef ▸ minpoly.aeval ℤ _
  obtain ⟨A, B, hAB⟩ := exists_split b μ
  obtain ⟨hA, hB⟩ := hind A B (by rw [← (hAB r).1, hμx])
  have hmin := cyclotomic_eq_minpoly hprim hn
  obtain ⟨WA, hWA⟩ : cyclotomic n ℤ ∣ A :=
    hmin ▸ minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hn) hA
  obtain ⟨WB, hWB⟩ : cyclotomic n ℤ ∣ B :=
    hmin ▸ minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hn) hB
  have hroot : ∀ r' ∈ primitiveRoots n ℂ,
      aeval (tB b - r') μ = 0 ∧ aeval (-tB b - r') μ = 0 := by
    intro r' hr'
    have h1 := aeval_cyclotomic_eq_zero ((mem_primitiveRoots hn).1 hr') hn
    have hA' : aeval r' A = 0 := by rw [hWA, map_mul, h1, zero_mul]
    have hB' : aeval r' B = 0 := by rw [hWB, map_mul, h1, zero_mul]
    rw [(hAB r').1, (hAB r').2, hA', hB']
    simp
  have hμc0 : μ.map (algebraMap ℤ ℂ) ≠ 0 := (hμ.map _).ne_zero
  have hnorm : ∀ r' ∈ primitiveRoots n ℂ, ‖r'‖ = 1 := fun r' hr' =>
    ((mem_primitiveRoots hn).1 hr').norm'_eq_one hn.ne'
  have hdisj : Disjoint ((primitiveRoots n ℂ).image fun r' => tB b - r')
      ((primitiveRoots n ℂ).image fun r' => -tB b - r') := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨v, hv, hv'⟩ := Finset.mem_image.1 h2
    have h2 : (2 : ℂ) * tB b = u - v := by linear_combination -hv'
    have h3 : ‖(2 : ℂ) * tB b‖ ≤ 2 := by
      rw [h2]
      calc ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le _ _
        _ = 2 := by rw [hnorm u hu, hnorm v hv]; norm_num
    rw [norm_mul, Complex.norm_ofNat] at h3
    have := one_lt_norm_tB hb
    linarith
  have hcard₁ : ((primitiveRoots n ℂ).image fun r' => tB b - r').card = n.totient := by
    rw [Finset.card_image_of_injective _ sub_right_injective, Complex.card_primitiveRoots]
  have hcard₂ : ((primitiveRoots n ℂ).image fun r' => -tB b - r').card = n.totient := by
    rw [Finset.card_image_of_injective _ sub_right_injective, Complex.card_primitiveRoots]
  have hsub : ((primitiveRoots n ℂ).image fun r' => tB b - r') ∪
      ((primitiveRoots n ℂ).image fun r' => -tB b - r') ⊆
        (μ.map (algebraMap ℤ ℂ)).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots hμc0, IsRoot.def, eval_map_algebraMap]
    rcases Finset.mem_union.1 hz with h | h
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
      exact (hroot u hu).1
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
      exact (hroot u hu).2
  calc 2 * n.totient = (((primitiveRoots n ℂ).image fun r' => tB b - r') ∪
        ((primitiveRoots n ℂ).image fun r' => -tB b - r')).card := by
        rw [Finset.card_union_of_disjoint hdisj, hcard₁, hcard₂]
        ring
    _ ≤ (μ.map (algebraMap ℤ ℂ)).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (μ.map (algebraMap ℤ ℂ)).roots := Multiset.toFinset_card_le _
    _ ≤ (μ.map (algebraMap ℤ ℂ)).natDegree := card_roots' _
    _ = μ.natDegree := hμ.natDegree_map _

/-- For a non-square `b`: `a + √b c = 0` with integers `a, c` forces `a = c = 0`. -/
theorem int_add_sqrt_mul_int {b : ℕ} (hsq : ¬ IsSquare b) {a c : ℤ}
    (h : (a : ℝ) + Real.sqrt (b : ℝ) * c = 0) : a = 0 ∧ c = 0 := by
  have hirr := irrational_sqrt_natCast_iff.2 hsq
  have hc : c = 0 := by
    by_contra hc
    apply hirr
    refine ⟨-a / c, ?_⟩
    have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    push_cast
    field_simp
    linarith
  subst hc
  simp only [Int.cast_zero, mul_zero, add_zero] at h
  exact ⟨by exact_mod_cast h, rfl⟩

/-- The independence hypothesis of `two_mul_totient_le_natDegree` at `r = ±1`. -/
theorem indep_intCast {b : ℕ} (hsq : ¬ IsSquare b) (ε : ℤ) (A B : ℤ[X])
    (h : aeval (ε : ℂ) A + tB b * aeval (ε : ℂ) B = 0) :
    aeval (ε : ℂ) A = 0 ∧ aeval (ε : ℂ) B = 0 := by
  have hA : aeval (ε : ℂ) A = ((A.eval ε : ℤ) : ℂ) := by
    have := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) ε A
    simpa using this
  have hB : aeval (ε : ℂ) B = ((B.eval ε : ℤ) : ℂ) := by
    have := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) ε B
    simpa using this
  rw [hA, hB] at h ⊢
  have h' : ((A.eval ε : ℤ) : ℝ) + Real.sqrt (b : ℝ) * ((B.eval ε : ℤ) : ℝ) = 0 := by
    have := congrArg Complex.re h
    simpa [tB] using this
  obtain ⟨h1, h2⟩ := int_add_sqrt_mul_int hsq h'
  rw [h1, h2]
  simp

/-- Values of integer polynomials at a square root of `-1` are Gaussian integers. -/
theorem aeval_gauss {r : ℂ} (hr : r ^ 2 = -1) (A : ℤ[X]) : ∃ u v : ℤ, aeval r A = u + v * r := by
  induction A using Polynomial.induction_on with
  | C a => exact ⟨a, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨u₁, v₁, h₁⟩ := hp
    obtain ⟨u₂, v₂, h₂⟩ := hq
    exact ⟨u₁ + u₂, v₁ + v₂, by rw [map_add, h₁, h₂]; push_cast; ring⟩
  | monomial n a h =>
    obtain ⟨u, v, h⟩ := h
    refine ⟨-v, u, ?_⟩
    have e : (C a * X ^ (n + 1) : ℤ[X]) = C a * X ^ n * X := by ring
    rw [e, map_mul, h, aeval_X]
    push_cast
    linear_combination (v : ℂ) * hr

/-- The independence hypothesis of `two_mul_totient_le_natDegree` at `r = ±i`. -/
theorem indep_I {b : ℕ} (hsq : ¬ IsSquare b) {r : ℂ} (hr : r = I ∨ r = -I) (A B : ℤ[X])
    (h : aeval r A + tB b * aeval r B = 0) : aeval r A = 0 ∧ aeval r B = 0 := by
  have hr2 : r ^ 2 = -1 := by rcases hr with rfl | rfl <;> simp
  obtain ⟨u, v, hA⟩ := aeval_gauss hr2 A
  obtain ⟨u', v', hB⟩ := aeval_gauss hr2 B
  rw [hA, hB] at h ⊢
  have hre : (u : ℝ) + Real.sqrt (b : ℝ) * u' = 0 := by
    have := congrArg Complex.re h
    rcases hr with rfl | rfl <;> simpa [tB] using this
  have him : (v : ℝ) + Real.sqrt (b : ℝ) * v' = 0 := by
    have := congrArg Complex.im h
    rcases hr with rfl | rfl <;> simp [tB] at this <;> linarith
  obtain ⟨h1, h2⟩ := int_add_sqrt_mul_int hsq hre
  obtain ⟨h3, h4⟩ := int_add_sqrt_mul_int hsq him
  rw [h1, h2, h3, h4]
  simp

/-- Under the independence hypothesis: `d(r) = 2 φ(n)` and `c₀(r) = Φ_n(√b) Φ_n(-√b)`. -/
theorem data_of_indep {b : ℕ} (hb : 2 ≤ b) {r : ℂ} (hr : IsOfFinOrder r)
    (hind : ∀ A B : ℤ[X], aeval r A + tB b * aeval r B = 0 → aeval r A = 0 ∧ aeval r B = 0) :
    cDeg b r = 2 * (orderOf r).totient ∧ (((minpoly ℤ (tB b - r)).eval 0 : ℤ) : ℂ) =
      aeval (tB b) (cyclotomic (orderOf r) ℤ) * aeval (-tB b) (cyclotomic (orderOf r) ℤ) := by
  obtain ⟨h1, h2⟩ := natDegree_minpoly_le b hr
  have h3 := le_antisymm h1 (two_mul_totient_le_natDegree hb hr hind)
  exact ⟨h3, h2 h3⟩

/-! ## 3. The four roots with `r⁴ = 1` -/

theorem orderOf_neg_one_complex : orderOf (-1 : ℂ) = 2 := by
  simp

/-- For `r = ±1` and a non-square `b`: `|c₀| = b - 1`, `d = 2`. -/
theorem data_of_sq_eq_one {b : ℕ} (hb : 2 ≤ b) (hsq : ¬ IsSquare b) {r : ℂ} (h : r ^ 2 = 1) :
    cAbs b r = b - 1 ∧ cDeg b r = 2 := by
  have hr : IsOfFinOrder r := isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, h⟩
  have hcases : r = 1 ∨ r = -1 := by
    have h0 : (r - 1) * (r + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact Or.inl (sub_eq_zero.1 h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
  have key : cDeg b r = 2 ∧ (minpoly ℤ (tB b - r)).eval 0 = 1 - (b : ℤ) := by
    rcases hcases with rfl | rfl
    · obtain ⟨h1, h2⟩ := data_of_indep hb hr (by
        have := indep_intCast hsq 1
        simpa using this)
      rw [orderOf_one] at h1 h2
      refine ⟨by simpa using h1, ?_⟩
      have h3 : (((minpoly ℤ (tB b - 1)).eval 0 : ℤ) : ℂ) = ((1 - (b : ℤ) : ℤ) : ℂ) := by
        rw [h2, cyclotomic_one]
        simp only [map_sub, aeval_X, map_one]
        push_cast
        linear_combination -tB_sq b
      exact_mod_cast h3
    · obtain ⟨h1, h2⟩ := data_of_indep hb hr (by
        have := indep_intCast hsq (-1)
        simpa using this)
      rw [orderOf_neg_one_complex] at h1 h2
      refine ⟨by simpa using h1, ?_⟩
      have h3 : (((minpoly ℤ (tB b - -1)).eval 0 : ℤ) : ℂ) = ((1 - (b : ℤ) : ℤ) : ℂ) := by
        rw [h2, cyclotomic_two]
        simp only [map_add, aeval_X, map_one]
        push_cast
        linear_combination -tB_sq b
      exact_mod_cast h3
  refine ⟨?_, key.1⟩
  rw [cAbs, key.2]
  omega

/-- For `r = ±i` and a non-square `b`: `|c₀| = (b + 1)²`, `d = 4`. -/
theorem data_of_sq_eq_neg_one {b : ℕ} (hb : 2 ≤ b) (hsq : ¬ IsSquare b) {r : ℂ}
    (h : r ^ 2 = -1) : cAbs b r = (b + 1) ^ 2 ∧ cDeg b r = 4 := by
  have h4 : r ^ 4 = 1 := by rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, h]; norm_num
  have hr : IsOfFinOrder r := isOfFinOrder_iff_pow_eq_one.2 ⟨4, by norm_num, h4⟩
  have hcases : r = I ∨ r = -I := by
    have h0 : (r - I) * (r + I) = 0 := by linear_combination h - Complex.I_sq
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact Or.inl (sub_eq_zero.1 h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
  have hord : orderOf r = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h' := orderOf_eq_prime_pow (x := r) (p := 2) (n := 1) (by rw [pow_one, h]; norm_num)
      (by norm_num; exact h4)
    simpa using h'
  obtain ⟨h1, h2⟩ := data_of_indep hb hr (indep_I hsq hcases)
  rw [hord] at h1 h2
  have hφ : Nat.totient 4 = 2 := by decide
  refine ⟨?_, by rw [h1, hφ]⟩
  have h3 : (((minpoly ℤ (tB b - r)).eval 0 : ℤ) : ℂ) = ((((b : ℤ) + 1) ^ 2 : ℤ) : ℂ) := by
    rw [h2, show (4 : ℕ) = 2 * 2 from rfl, aeval_cyclotomic_two_mul_of_even (dvd_refl 2),
      aeval_cyclotomic_two_mul_of_even (dvd_refl 2), cyclotomic_two]
    simp only [map_add, aeval_X, map_one, neg_sq, tB_sq]
    push_cast
    ring
  have h5 : (minpoly ℤ (tB b - r)).eval 0 = ((b : ℤ) + 1) ^ 2 := by exact_mod_cast h3
  rw [cAbs, h5, Int.natAbs_pow]
  norm_cast

/-- **The four roots with `r⁴ = 1`**, for a non-square `b`: `m = 1`, `|c₀| = b - 1`, `d = 2`,
or `m = 2`, `|c₀| = (b + 1)²`, `d = 4`. -/
theorem low_data {b : ℕ} (hb : 2 ≤ b) (hsq : ¬ IsSquare b) {r : ℂ} (h4 : r ^ 4 = 1) :
    (orderOf (r ^ 2) = 1 ∧ cAbs b r = b - 1 ∧ cDeg b r = 2) ∨
      (orderOf (r ^ 2) = 2 ∧ cAbs b r = (b + 1) ^ 2 ∧ cDeg b r = 4) := by
  have h0 : (r ^ 2 - 1) * (r ^ 2 + 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.1 h0 with h | h
  · have h1 : r ^ 2 = 1 := sub_eq_zero.1 h
    exact Or.inl ⟨by rw [h1, orderOf_one], data_of_sq_eq_one hb hsq h1⟩
  · have h1 : r ^ 2 = -1 := eq_neg_of_add_eq_zero_left h
    exact Or.inr ⟨by rw [h1, orderOf_neg_one_complex], data_of_sq_eq_neg_one hb hsq h1⟩

/-! ## 4. F2: the roots with `r⁴ ≠ 1` -/

theorem totient_two_mul_le (m : ℕ) : (2 * m).totient ≤ 2 * m.totient := by
  rcases Nat.even_or_odd m with h | h
  · rw [Nat.totient_mul_of_dvd (even_iff_two_dvd.1 h)]
  · rw [Nat.totient_two_mul_of_odd h]
    omega

/-- **F2.** For a root of unity `r` with `r⁴ ≠ 1`, `m` the order of `r²`: there is
`k ∈ {1, 2}` with `k φ(m) ≤ d(r) ≤ 2 k φ(m)`; a prime `q ∣ m` divides `c₀(r)` at most `k`
times; and if `d(r) = 2 k φ(m)`, every prime factor of `c₀(r)` divides it at least `k` times. -/
theorem high_data {b : ℕ} (hb : 2 ≤ b) {r : ℂ} (hr : IsOfFinOrder r) (h4 : r ^ 4 ≠ 1) :
    ∃ k : ℕ, 0 < k ∧ k ≤ 2 ∧ k * (orderOf (r ^ 2)).totient ≤ cDeg b r ∧
      cDeg b r ≤ 2 * k * (orderOf (r ^ 2)).totient ∧
      (∀ q : ℕ, q.Prime → q ∣ orderOf (r ^ 2) → q ∣ cAbs b r →
        (cAbs b r).factorization q ≤ k) ∧
      (cDeg b r = 2 * k * (orderOf (r ^ 2)).totient → ∀ p : ℕ, p.Prime → p ∣ cAbs b r →
        k ≤ (cAbs b r).factorization p) := by
  obtain ⟨hm3, hnm, k, hk, htot, hD⟩ := cyclo_data b hr h4
  obtain ⟨h, hch, -⟩ := exists_cofactor hb hr
  rw [hD] at hch
  have hch' : (minpoly ℤ (tB b - r)).eval 0 * h =
      (cyclotomic (orderOf (r ^ 2)) ℤ).eval (b : ℤ) ^ k := by exact_mod_cast hch
  have hc0 : cAbs b r ≠ 0 := cAbs_ne_zero hb hr
  have hφ : 0 < (orderOf (r ^ 2)).totient := Nat.totient_pos.2 (by omega)
  obtain ⟨hle, heq⟩ := natDegree_minpoly_le b hr
  rw [htot] at hle
  refine ⟨k, hk, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (orderOf r).totient ≤ (2 * orderOf (r ^ 2)).totient :=
      Nat.le_of_dvd (Nat.totient_pos.2 (by omega)) (Nat.totient_dvd_of_dvd hnm)
    have h2 := totient_two_mul_le (orderOf (r ^ 2))
    rw [htot] at h1
    nlinarith
  · have := totient_le_natDegree_minpoly hb hr
    rw [htot] at this
    exact this
  · rw [mul_assoc]
    exact hle
  · intro q hq hqm hqc
    have hqc' : (q : ℤ) ∣ (minpoly ℤ (tB b - r)).eval 0 := dvd_cAbs_iff.1 hqc
    have hqΦ : (q : ℤ) ∣ (cyclotomic (orderOf (r ^ 2)) ℤ).eval (b : ℤ) :=
      (Nat.prime_iff_prime_int.1 hq).dvd_of_dvd_pow (hch' ▸ Dvd.dvd.mul_right hqc' h)
    obtain ⟨-, hsq⟩ := nonprimitive_facts hb hm3 hq hqΦ hqm
    by_contra hlt
    push Not at hlt
    apply not_pow_succ_dvd_pow hq hsq k
    have h1 : q ^ (k + 1) ∣ cAbs b r := (hq.pow_dvd_iff_le_factorization hc0).2 hlt
    have h2 : (q : ℤ) ^ (k + 1) ∣ (minpoly ℤ (tB b - r)).eval 0 := by
      have := dvd_cAbs_iff.1 h1
      simpa using this
    rw [← hch']
    exact h2.mul_right h
  · intro hdeg p hp hpc
    have hc : (minpoly ℤ (tB b - r)).eval 0 =
        (cyclotomic (orderOf (r ^ 2)) ℤ).eval (b : ℤ) ^ k := by
      have := heq (by rw [htot, ← mul_assoc]; exact hdeg)
      rw [hD] at this
      exact_mod_cast this
    have hpc' : (p : ℤ) ∣ (minpoly ℤ (tB b - r)).eval 0 := dvd_cAbs_iff.1 hpc
    have hpΦ : (p : ℤ) ∣ (cyclotomic (orderOf (r ^ 2)) ℤ).eval (b : ℤ) :=
      (Nat.prime_iff_prime_int.1 hp).dvd_of_dvd_pow (hc ▸ hpc')
    have h1 : (p : ℤ) ^ k ∣ (minpoly ℤ (tB b - r)).eval 0 := hc ▸ pow_dvd_pow_of_dvd hpΦ k
    have h2 : p ^ k ∣ cAbs b r := dvd_cAbs_iff.2 (by simpa using h1)
    exact (hp.pow_dvd_iff_le_factorization hc0).1 h2

end BaseB

end PiFormula
