module

public import Pilean.BaseB.Symmetrize

/-!
# A general base `b`: the cofactor of the minimal polynomial of `√b - r`

Let `t = √b`, `b ≥ 2`, let `r` be a root of unity of order `n`, and let `μ` be the minimal
polynomial over `ℤ` of `x = t - r`.

* `totient_le_natDegree_minpoly`: `deg μ ≥ φ(n)`. The symmetrization `Q` of `μ` vanishes at
  `r`, so `Φ_n` divides `Q`, and for every primitive `n`-th root `r'` one of `t - r'`,
  `-t - r'` is a root of `μ`. This is an injection from the primitive `n`-th roots into the
  roots of `μ`, because `t - r' = -t - r''` would give `|2t| ≤ 2`.
* `exists_cofactor`: there is an integer `h` with `μ(0) h = Φ_n(t) Φ_n(-t)` and
  `|h| ≤ (√b + 1)^φ(n)`. The symmetrization `F` of `Φ_n` vanishes at `x`, so `F = μ H`, and
  `h = H(0)`. Over `ℂ`, `F = ∏ (X - (t - r')) ∏ (X - (-t - r'))` (products over the primitive
  `n`-th roots `r'`), monic of degree `2 φ(n)`; so `H` is monic of degree at most `φ(n)`, and
  each of its roots has absolute value at most `√b + 1`.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-- The value at `0` of an integer polynomial, seen in `ℂ`. -/
theorem aeval_zero_int (P : ℤ[X]) : aeval (0 : ℂ) P = ((P.eval 0 : ℤ) : ℂ) := by
  have h := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (0 : ℤ) P
  simpa using h

/-- A product of complex numbers of absolute value at most `c` is at most `c^(number)`. -/
theorem norm_multiset_prod_le_pow (s : Multiset ℂ) {c : ℝ} (h : ∀ z ∈ s, ‖z‖ ≤ c) :
    ‖s.prod‖ ≤ c ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := h a (Multiset.mem_cons_self a s)
    have hs := ih fun z hz => h z (Multiset.mem_cons_of_mem hz)
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ']
    exact mul_le_mul ha hs (norm_nonneg _) ((norm_nonneg a).trans ha)

/-- `Φ_n` vanishes at a primitive `n`-th root of unity. -/
theorem aeval_cyclotomic_eq_zero {n : ℕ} {r : ℂ} (hr : IsPrimitiveRoot r n) (hn : 0 < n) :
    aeval r (cyclotomic n ℤ) = 0 := by
  rw [cyclotomic_eq_minpoly hr hn]
  exact minpoly.aeval ℤ r

/-- **The degree of the minimal polynomial of `√b - r`** is at least `φ(ord r)`. -/
theorem totient_le_natDegree_minpoly {b : ℕ} (hb : 2 ≤ b) {r : ℂ} (hr : IsOfFinOrder r) :
    (orderOf r).totient ≤ (minpoly ℤ (tB b - r)).natDegree := by
  classical
  obtain ⟨n, hndef⟩ : ∃ n, orderOf r = n := ⟨_, rfl⟩
  rw [hndef]
  have hn : 0 < n := hndef ▸ hr.orderOf_pos
  have hprim : IsPrimitiveRoot r n := hndef ▸ IsPrimitiveRoot.orderOf r
  have hx := isIntegral_tB_sub b hr
  have hμ := minpoly.monic hx
  obtain ⟨μ, hμdef⟩ : ∃ μ, minpoly ℤ (tB b - r) = μ := ⟨_, rfl⟩
  rw [hμdef] at hμ ⊢
  have hμx : aeval (tB b - r) μ = 0 := hμdef ▸ minpoly.aeval ℤ _
  obtain ⟨Q, hQ⟩ := exists_symmetrize b μ
  have hQr : aeval r Q = 0 := by rw [hQ, hμx, zero_mul]
  have hdvd : cyclotomic n ℤ ∣ Q := by
    rw [cyclotomic_eq_minpoly hprim hn]
    exact minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hn) hQr
  -- for each primitive root `r'`, one of `t - r'`, `-t - r'` is a root of `μ`
  have hroot : ∀ r' ∈ primitiveRoots n ℂ,
      aeval (tB b - r') μ = 0 ∨ aeval (-tB b - r') μ = 0 := by
    intro r' hr'
    have h1 := aeval_cyclotomic_eq_zero ((mem_primitiveRoots hn).1 hr') hn
    obtain ⟨W, hW⟩ := hdvd
    have h2 : aeval r' Q = 0 := by rw [hW, map_mul, h1, zero_mul]
    rw [hQ] at h2
    exact mul_eq_zero.1 h2
  let g : ℂ → ℂ := fun r' => if aeval (tB b - r') μ = 0 then tB b - r' else -tB b - r'
  have hμc0 : μ.map (algebraMap ℤ ℂ) ≠ 0 := (hμ.map _).ne_zero
  have hmaps : ∀ r' ∈ primitiveRoots n ℂ, g r' ∈ (μ.map (algebraMap ℤ ℂ)).roots.toFinset := by
    intro r' hr'
    rw [Multiset.mem_toFinset, mem_roots hμc0, IsRoot.def, eval_map_algebraMap]
    simp only [g]
    split_ifs with h
    · exact h
    · exact (hroot r' hr').resolve_left h
  have hnorm : ∀ r' ∈ primitiveRoots n ℂ, ‖r'‖ = 1 := fun r' hr' =>
    ((mem_primitiveRoots hn).1 hr').norm'_eq_one hn.ne'
  have hbad : ∀ u v : ℂ, ‖u‖ = 1 → ‖v‖ = 1 → tB b - u ≠ -tB b - v := by
    intro u v hu hv h
    have h2 : (2 : ℂ) * tB b = u - v := by linear_combination h
    have h3 : ‖(2 : ℂ) * tB b‖ ≤ 2 := by
      rw [h2]
      calc ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le _ _
        _ = 2 := by rw [hu, hv]; norm_num
    rw [norm_mul, Complex.norm_ofNat] at h3
    have := one_lt_norm_tB hb
    linarith
  have hinj : Set.InjOn g (primitiveRoots n ℂ) := by
    intro r₁ h₁ r₂ h₂ h
    simp only [g] at h
    split_ifs at h with ha hb'
    · exact sub_right_injective h
    · exact absurd h (hbad r₁ r₂ (hnorm r₁ h₁) (hnorm r₂ h₂))
    · exact absurd h.symm (hbad r₂ r₁ (hnorm r₂ h₂) (hnorm r₁ h₁))
    · exact sub_right_injective h
  calc n.totient = (primitiveRoots n ℂ).card := (Complex.card_primitiveRoots n).symm
    _ ≤ (μ.map (algebraMap ℤ ℂ)).roots.toFinset.card :=
        Finset.card_le_card_of_injOn g hmaps hinj
    _ ≤ Multiset.card (μ.map (algebraMap ℤ ℂ)).roots := Multiset.toFinset_card_le _
    _ ≤ (μ.map (algebraMap ℤ ℂ)).natDegree := card_roots' _
    _ = μ.natDegree := hμ.natDegree_map _

/-- **The cofactor.** With `μ` the minimal polynomial of `√b - r` over `ℤ` and `n = ord r`:
an integer `h` with `μ(0) h = Φ_n(√b) Φ_n(-√b)` and `|h| ≤ (√b + 1)^φ(n)`. -/
theorem exists_cofactor {b : ℕ} (hb : 2 ≤ b) {r : ℂ} (hr : IsOfFinOrder r) :
    ∃ h : ℤ, (((minpoly ℤ (tB b - r)).eval 0 * h : ℤ) : ℂ) =
        aeval (tB b) (cyclotomic (orderOf r) ℤ) * aeval (-tB b) (cyclotomic (orderOf r) ℤ) ∧
      |(h : ℝ)| ≤ (Real.sqrt (b : ℝ) + 1) ^ (orderOf r).totient := by
  classical
  have hdeg := totient_le_natDegree_minpoly hb hr
  obtain ⟨n, hndef⟩ : ∃ n, orderOf r = n := ⟨_, rfl⟩
  rw [hndef] at hdeg ⊢
  have hn : 0 < n := hndef ▸ hr.orderOf_pos
  have hprim : IsPrimitiveRoot r n := hndef ▸ IsPrimitiveRoot.orderOf r
  have hx := isIntegral_tB_sub b hr
  have hμ := minpoly.monic hx
  obtain ⟨F, hF⟩ := exists_symmetrize b (cyclotomic n ℤ)
  have hFx : aeval (tB b - r) F = 0 := by
    rw [hF, sub_sub_cancel, aeval_cyclotomic_eq_zero hprim hn, zero_mul]
  obtain ⟨H, hH⟩ := minpoly.isIntegrallyClosed_dvd hx hFx
  obtain ⟨μ, hμdef⟩ : ∃ μ, minpoly ℤ (tB b - r) = μ := ⟨_, rfl⟩
  rw [hμdef] at hμ hH hdeg ⊢
  refine ⟨H.eval 0, ?_, ?_⟩
  · have h0 := hF 0
    rw [sub_zero, sub_zero, hH, aeval_zero_int, eval_mul] at h0
    exact h0
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
  have hmonF : (F.map (algebraMap ℤ ℂ)).Monic := hFc ▸ hmon1.mul hmon2
  have hdegF : (F.map (algebraMap ℤ ℂ)).natDegree = 2 * n.totient := by
    rw [hFc, hmon1.natDegree_mul hmon2,
      natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _,
      natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
      Complex.card_primitiveRoots]
    ring
  have hmap : F.map (algebraMap ℤ ℂ) = μ.map (algebraMap ℤ ℂ) * H.map (algebraMap ℤ ℂ) := by
    rw [hH, Polynomial.map_mul]
  have hmonμ : (μ.map (algebraMap ℤ ℂ)).Monic := hμ.map _
  have hmonH : (H.map (algebraMap ℤ ℂ)).Monic := hmonμ.of_mul_monic_left (hmap ▸ hmonF)
  have hdegH : (H.map (algebraMap ℤ ℂ)).natDegree ≤ n.totient := by
    have h1 := hmonμ.natDegree_mul hmonH
    rw [← hmap, hdegF, hμ.natDegree_map] at h1
    omega
  -- the roots of `H` are bounded by `√b + 1`
  have hnorm : ∀ r' ∈ primitiveRoots n ℂ, ‖r'‖ = 1 := fun r' hr' =>
    ((mem_primitiveRoots hn).1 hr').norm'_eq_one hn.ne'
  have hroots : ∀ z ∈ (H.map (algebraMap ℤ ℂ)).roots, ‖z‖ ≤ Real.sqrt (b : ℝ) + 1 := by
    intro z hz
    have hz' : z ∈ (F.map (algebraMap ℤ ℂ)).roots :=
      Multiset.mem_of_le (roots.le_of_dvd hmonF.ne_zero (Dvd.intro_left _ hmap.symm)) hz
    rw [mem_roots hmonF.ne_zero, IsRoot.def, hFc, eval_mul, eval_prod, eval_prod] at hz'
    rcases mul_eq_zero.1 hz' with h | h
    · obtain ⟨r', hr', h⟩ := Finset.prod_eq_zero_iff.1 h
      simp only [eval_sub, eval_X, eval_C] at h
      rw [sub_eq_zero.1 h]
      calc ‖tB b - r'‖ ≤ ‖tB b‖ + ‖r'‖ := norm_sub_le _ _
        _ = Real.sqrt (b : ℝ) + 1 := by rw [norm_tB, hnorm r' hr']
    · obtain ⟨r', hr', h⟩ := Finset.prod_eq_zero_iff.1 h
      simp only [eval_sub, eval_X, eval_C] at h
      rw [sub_eq_zero.1 h]
      calc ‖-tB b - r'‖ ≤ ‖-tB b‖ + ‖r'‖ := norm_sub_le _ _
        _ = Real.sqrt (b : ℝ) + 1 := by rw [norm_neg, norm_tB, hnorm r' hr']
  have hsplit : (H.map (algebraMap ℤ ℂ)).Splits := IsAlgClosed.splits _
  have hc0 : ((H.eval 0 : ℤ) : ℂ) =
      (-1) ^ (H.map (algebraMap ℤ ℂ)).natDegree * (H.map (algebraMap ℤ ℂ)).roots.prod := by
    rw [← hsplit.coeff_zero_eq_prod_roots_of_monic hmonH, coeff_zero_eq_eval_zero,
      eval_map_algebraMap, aeval_zero_int]
  have h1 : (1 : ℝ) ≤ Real.sqrt (b : ℝ) + 1 := by
    have := Real.sqrt_nonneg (b : ℝ)
    linarith
  calc |((H.eval 0 : ℤ) : ℝ)| = ‖((H.eval 0 : ℤ) : ℂ)‖ := (Complex.norm_intCast _).symm
    _ = ‖(H.map (algebraMap ℤ ℂ)).roots.prod‖ := by
        rw [hc0, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ ≤ (Real.sqrt (b : ℝ) + 1) ^ Multiset.card (H.map (algebraMap ℤ ℂ)).roots :=
        norm_multiset_prod_le_pow _ hroots
    _ = (Real.sqrt (b : ℝ) + 1) ^ (H.map (algebraMap ℤ ℂ)).natDegree := by
        rw [hsplit.natDegree_eq_card_roots]
    _ ≤ (Real.sqrt (b : ℝ) + 1) ^ n.totient := pow_le_pow_right₀ h1 hdegH

end BaseB

end PiFormula
