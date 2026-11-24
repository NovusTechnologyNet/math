module

public import Pilean.RatBase.SymmetrizeR

/-!
# Rational bases: the cofactor of the minimal polynomial of `√(pq) - q r`

Let `p > q ≥ 1`, `u = √(pq)`, let `r` be a root of unity of order `n`, and let `μ` be the
minimal polynomial over `ℤ` of `x = u - q r`.

* `totient_le_natDegree_minpolyR`: `deg μ ≥ φ(n)`. The symmetrization `Q` of `μ` vanishes at
  `r`, so `Φ_n` divides `Q`, and for every primitive `n`-th root `r'` one of `u - q r'`,
  `-u - q r'` is a root of `μ`. This is an injection from the primitive `n`-th roots into the
  roots of `μ`, because `u - q r' = -u - q r''` would give `2 √(pq) ≤ 2 q`.
* `pow_dvd_eval_zero_sq`: **the powers of `q`.** If the square of every complex root of a monic
  `P ∈ ℤ[X]` is `q` times an algebraic integer, then `q^(deg P)` divides `P(0)²`. (The quotient
  is a rational number and an algebraic integer.) The numbers `z = ±u - q r'` have this
  property: `z² = q (p ∓ 2 u r' + q r'²)`. No square root of `q` is used.
* `exists_cofactorR`: there are integers `C`, `C'` with `C ∣ μ(0)²`,
  `q^(2 φ(n)) C C' = (Ψ(u) Ψ(-u))²` and `|C'| ≤ ((√p + √q)²)^φ(n)`, where `Ψ = cycloScaled q n`.
  The symmetrization `F` of `Ψ` in base `pq` vanishes at `x`, so `F = μ H`. Over `ℂ`,
  `F = ∏ (X - (u - q r')) ∏ (X - (-u - q r'))`, monic of degree `2 φ(n)`. Then
  `C = μ(0)² / q^(deg μ)` and `C' = H(0)² / q^(deg H)`; `H` has degree at most `φ(n)` and each
  of its roots `z` has `|z|² ≤ (√(pq) + q)² = q (√p + √q)²`.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace RatBase

/-- `√(pq) - q r` is an algebraic integer. -/
theorem isIntegral_tB_sub_natCast_mul (p q : ℕ) {r : ℂ} (hr : IsOfFinOrder r) :
    IsIntegral ℤ (BaseB.tB (p * q) - (q : ℂ) * r) :=
  (BaseB.isIntegral_tB (p * q)).sub ((isIntegral_natCast' q).mul (isIntegral_of_finOrder hr))

/-- `q < √(pq)` for `p > q ≥ 1`. -/
private theorem lt_norm_tB_mul {p q : ℕ} (hq : 0 < q) (hqp : q < p) :
    (q : ℝ) < ‖BaseB.tB (p * q)‖ := by
  rw [BaseB.norm_tB, Real.lt_sqrt (Nat.cast_nonneg q)]
  have h : q ^ 2 < p * q := by nlinarith
  exact_mod_cast h

/-- **The degree of the minimal polynomial of `√(pq) - q r`** is at least `φ(ord r)`. -/
theorem totient_le_natDegree_minpolyR {p q : ℕ} (hq : 0 < q) (hqp : q < p) {r : ℂ}
    (hr : IsOfFinOrder r) :
    (orderOf r).totient ≤ (minpoly ℤ (BaseB.tB (p * q) - (q : ℂ) * r)).natDegree := by
  classical
  obtain ⟨n, hndef⟩ : ∃ n, orderOf r = n := ⟨_, rfl⟩
  rw [hndef]
  have hn : 0 < n := hndef ▸ hr.orderOf_pos
  have hprim : IsPrimitiveRoot r n := hndef ▸ IsPrimitiveRoot.orderOf r
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hx := isIntegral_tB_sub_natCast_mul p q hr
  have hμ := minpoly.monic hx
  obtain ⟨u, hu⟩ : ∃ u : ℂ, BaseB.tB (p * q) = u := ⟨_, rfl⟩
  have hqu : (q : ℝ) < ‖u‖ := hu ▸ lt_norm_tB_mul hq hqp
  obtain ⟨Q, hQ⟩ := exists_symmetrizeR p q (minpoly ℤ (BaseB.tB (p * q) - (q : ℂ) * r))
  have hμx : aeval (BaseB.tB (p * q) - (q : ℂ) * r)
      (minpoly ℤ (BaseB.tB (p * q) - (q : ℂ) * r)) = 0 := minpoly.aeval ℤ _
  obtain ⟨μ, hμdef⟩ : ∃ μ, minpoly ℤ (BaseB.tB (p * q) - (q : ℂ) * r) = μ := ⟨_, rfl⟩
  rw [hμdef] at hμ hQ hμx ⊢
  rw [hu] at hQ hμx
  have hQr : aeval r Q = 0 := by rw [hQ, hμx, zero_mul]
  have hdvd : cyclotomic n ℤ ∣ Q := by
    rw [cyclotomic_eq_minpoly hprim hn]
    exact minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hn) hQr
  -- for each primitive root `r'`, one of `u - q r'`, `-u - q r'` is a root of `μ`
  have hroot : ∀ r' ∈ primitiveRoots n ℂ,
      aeval (u - (q : ℂ) * r') μ = 0 ∨ aeval (-u - (q : ℂ) * r') μ = 0 := by
    intro r' hr'
    have h1 := BaseB.aeval_cyclotomic_eq_zero ((mem_primitiveRoots hn).1 hr') hn
    obtain ⟨W, hW⟩ := hdvd
    have h2 : aeval r' Q = 0 := by rw [hW, map_mul, h1, zero_mul]
    rw [hQ] at h2
    exact mul_eq_zero.1 h2
  let g : ℂ → ℂ := fun r' =>
    if aeval (u - (q : ℂ) * r') μ = 0 then u - (q : ℂ) * r' else -u - (q : ℂ) * r'
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
  have hbad : ∀ a b : ℂ, ‖a‖ = 1 → ‖b‖ = 1 → u - (q : ℂ) * a ≠ -u - (q : ℂ) * b := by
    intro a b ha hb h
    have h2 : (2 : ℂ) * u = (q : ℂ) * (a - b) := by linear_combination h
    have h3 : ‖(2 : ℂ) * u‖ ≤ 2 * (q : ℝ) := by
      rw [h2, norm_mul, Complex.norm_natCast]
      have h4 : ‖a - b‖ ≤ 2 := by
        calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
          _ = 2 := by rw [ha, hb]; norm_num
      nlinarith [Nat.cast_nonneg (α := ℝ) q]
    rw [norm_mul, Complex.norm_ofNat] at h3
    linarith
  have hinj : Set.InjOn g (primitiveRoots n ℂ) := by
    intro r₁ h₁ r₂ h₂ h
    simp only [g] at h
    split_ifs at h with ha hb'
    · exact mul_left_cancel₀ hq0 (sub_right_injective h)
    · exact absurd h (hbad r₁ r₂ (hnorm r₁ h₁) (hnorm r₂ h₂))
    · exact absurd h.symm (hbad r₂ r₁ (hnorm r₂ h₂) (hnorm r₁ h₁))
    · exact mul_left_cancel₀ hq0 (sub_right_injective h)
  calc n.totient = (primitiveRoots n ℂ).card := (Complex.card_primitiveRoots n).symm
    _ ≤ (μ.map (algebraMap ℤ ℂ)).roots.toFinset.card :=
        Finset.card_le_card_of_injOn g hmaps hinj
    _ ≤ Multiset.card (μ.map (algebraMap ℤ ℂ)).roots := Multiset.toFinset_card_le _
    _ ≤ (μ.map (algebraMap ℤ ℂ)).natDegree := card_roots' _
    _ = μ.natDegree := hμ.natDegree_map _

/-! ## The powers of `q` -/

/-- A rational integer that is `N` times an algebraic integer is divisible by `N`. -/
private theorem natCast_dvd_of_eq_mul_isIntegral {a : ℤ} {N : ℕ} (hN : 0 < N) {W : ℂ}
    (hW : IsIntegral ℤ W) (h : (a : ℂ) = (N : ℂ) * W) : (N : ℤ) ∣ a := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hWq : W = (((a : ℚ) / N : ℚ) : ℂ) := by
    push_cast
    rw [h, mul_div_cancel_left₀ _ hN0]
  rw [hWq] at hW
  have h1 : IsIntegral ℤ ((a : ℚ) / N) := isIntegral_ratCast_iff.1 hW
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  refine ⟨y, ?_⟩
  have h2 : (a : ℚ) = (N : ℚ) * (y : ℚ) := by
    have h3 : ((y : ℤ) : ℚ) = (a : ℚ) / N := hy
    rw [h3, mul_div_cancel₀ _ hNq]
  exact_mod_cast h2

/-- If the square of every element of `s` is `q` times an algebraic integer, the square of the
product of `s` is `q^(card s)` times an algebraic integer. -/
private theorem exists_isIntegral_prod_sq {q : ℕ} (s : Multiset ℂ)
    (h : ∀ z ∈ s, ∃ w : ℂ, IsIntegral ℤ w ∧ z ^ 2 = (q : ℂ) * w) :
    ∃ W : ℂ, IsIntegral ℤ W ∧ s.prod ^ 2 = (q : ℂ) ^ Multiset.card s * W := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, isIntegral_one, by simp⟩
  | cons a s ih =>
    obtain ⟨w, hw, hz⟩ := h a (Multiset.mem_cons_self a s)
    obtain ⟨W, hW, hs⟩ := ih fun z hz => h z (Multiset.mem_cons_of_mem hz)
    refine ⟨w * W, hw.mul hW, ?_⟩
    rw [Multiset.prod_cons, Multiset.card_cons, mul_pow, hz, hs]
    ring

/-- **The powers of `q`.** If `P ∈ ℤ[X]` is monic and the square of every complex root of `P`
is `q` times an algebraic integer, then `q^(deg P)` divides `P(0)²`. -/
theorem pow_dvd_eval_zero_sq {q : ℕ} (hq : 0 < q) {P : ℤ[X]}
    (hP : (P.map (algebraMap ℤ ℂ)).Monic)
    (h : ∀ z ∈ (P.map (algebraMap ℤ ℂ)).roots, ∃ w : ℂ, IsIntegral ℤ w ∧ z ^ 2 = (q : ℂ) * w) :
    (q : ℤ) ^ (P.map (algebraMap ℤ ℂ)).natDegree ∣ P.eval 0 ^ 2 := by
  have hsplit : (P.map (algebraMap ℤ ℂ)).Splits := IsAlgClosed.splits _
  have hc0 : ((P.eval 0 : ℤ) : ℂ) =
      (-1) ^ (P.map (algebraMap ℤ ℂ)).natDegree * (P.map (algebraMap ℤ ℂ)).roots.prod := by
    rw [← hsplit.coeff_zero_eq_prod_roots_of_monic hP, coeff_zero_eq_eval_zero,
      eval_map_algebraMap, BaseB.aeval_zero_int]
  obtain ⟨W, hW, hWs⟩ := exists_isIntegral_prod_sq _ h
  rw [← hsplit.natDegree_eq_card_roots] at hWs
  have key := natCast_dvd_of_eq_mul_isIntegral (a := P.eval 0 ^ 2)
    (N := q ^ (P.map (algebraMap ℤ ℂ)).natDegree) (pow_pos hq _) hW (by
      push_cast
      rw [hc0, mul_pow, hWs, ← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow, one_mul])
  exact_mod_cast key

/-! ## The cofactor -/

/-- **The cofactor.** With `μ` the minimal polynomial of `x = √(pq) - q r` over `ℤ`, `n = ord r`
and `Ψ = cycloScaled q n`: integers `C`, `C'` with `C ∣ μ(0)²`,
`q^(2 φ(n)) C C' = (Ψ(u) Ψ(-u))²` and `|C'| ≤ ((√p + √q)²)^φ(n)`. -/
theorem exists_cofactorR {p q : ℕ} (hq : 0 < q) (hqp : q < p) {r : ℂ} (hr : IsOfFinOrder r) :
    ∃ C C' : ℤ, C ∣ (minpoly ℤ (BaseB.tB (p * q) - (q : ℂ) * r)).eval 0 ^ 2 ∧
      (((q : ℤ) ^ (2 * (orderOf r).totient) * (C * C') : ℤ) : ℂ) =
        (aeval (BaseB.tB (p * q)) (cycloScaled q (orderOf r)) *
          aeval (-BaseB.tB (p * q)) (cycloScaled q (orderOf r))) ^ 2 ∧
      |(C' : ℝ)| ≤ ((Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ 2) ^ (orderOf r).totient := by
  classical
  have hdeg := totient_le_natDegree_minpolyR hq hqp hr
  obtain ⟨n, hndef⟩ : ∃ n, orderOf r = n := ⟨_, rfl⟩
  rw [hndef] at hdeg ⊢
  have hn : 0 < n := hndef ▸ hr.orderOf_pos
  have hprim : IsPrimitiveRoot r n := hndef ▸ IsPrimitiveRoot.orderOf r
  have hx := isIntegral_tB_sub_natCast_mul p q hr
  have hμ := minpoly.monic hx
  have hu2 : BaseB.tB (p * q) ^ 2 = (p : ℂ) * q := by
    rw [BaseB.tB_sq]
    push_cast
    ring
  have hunorm : ‖BaseB.tB (p * q)‖ = Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) := by
    rw [BaseB.norm_tB, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p)]
  have huint := BaseB.isIntegral_tB (p * q)
  obtain ⟨F, hF⟩ := BaseB.exists_symmetrize (p * q) (cycloScaled q n)
  have hFx : aeval (BaseB.tB (p * q) - (q : ℂ) * r) F = 0 := by
    rw [hF, sub_sub_cancel, aeval_mul_cycloScaled, BaseB.aeval_cyclotomic_eq_zero hprim hn,
      mul_zero, zero_mul]
  obtain ⟨H, hH⟩ := minpoly.isIntegrallyClosed_dvd hx hFx
  obtain ⟨μ, hμdef⟩ : ∃ μ, minpoly ℤ (BaseB.tB (p * q) - (q : ℂ) * r) = μ := ⟨_, rfl⟩
  rw [hμdef] at hμ hH hdeg ⊢
  obtain ⟨u, hu⟩ : ∃ u : ℂ, BaseB.tB (p * q) = u := ⟨_, rfl⟩
  rw [hu] at hF hu2 hunorm huint ⊢
  -- over `ℂ`: `F = ∏ (X - (u - q r')) ∏ (X - (-u - q r'))`
  have hFc : F.map (algebraMap ℤ ℂ) = (∏ r' ∈ primitiveRoots n ℂ, (X - C (u - (q : ℂ) * r'))) *
      ∏ r' ∈ primitiveRoots n ℂ, (X - C (-u - (q : ℂ) * r')) := by
    apply Polynomial.funext
    intro z
    rw [eval_map_algebraMap, hF z, aeval_cycloScaled_eq_prod hq hn,
      aeval_cycloScaled_eq_prod hq hn, eval_mul, eval_prod, eval_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r' _ => ?_
    simp only [eval_sub, eval_X, eval_C]
    ring
  have hmon1 : (∏ r' ∈ primitiveRoots n ℂ, (X - C (u - (q : ℂ) * r'))).Monic :=
    monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hmon2 : (∏ r' ∈ primitiveRoots n ℂ, (X - C (-u - (q : ℂ) * r'))).Monic :=
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
  obtain ⟨δ, hδ⟩ : ∃ δ, (μ.map (algebraMap ℤ ℂ)).natDegree = δ := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε, (H.map (algebraMap ℤ ℂ)).natDegree = ε := ⟨_, rfl⟩
  have hsum : δ + ε = 2 * n.totient := by
    rw [← hδ, ← hε, ← hmonμ.natDegree_mul hmonH, ← hmap, hdegF]
  have hεle : ε ≤ n.totient := by
    rw [hμ.natDegree_map] at hδ
    omega
  -- the roots of `F` are the numbers `±u - q r'`
  have hnorm : ∀ r' ∈ primitiveRoots n ℂ, ‖r'‖ = 1 := fun r' hr' =>
    ((mem_primitiveRoots hn).1 hr').norm'_eq_one hn.ne'
  have hrootsF : ∀ z ∈ (F.map (algebraMap ℤ ℂ)).roots, ∃ r' ∈ primitiveRoots n ℂ,
      z = u - (q : ℂ) * r' ∨ z = -u - (q : ℂ) * r' := by
    intro z hz
    rw [mem_roots hmonF.ne_zero, IsRoot.def, hFc, eval_mul, eval_prod, eval_prod] at hz
    rcases mul_eq_zero.1 hz with h | h
    · obtain ⟨r', hr', h⟩ := Finset.prod_eq_zero_iff.1 h
      simp only [eval_sub, eval_X, eval_C] at h
      exact ⟨r', hr', Or.inl (sub_eq_zero.1 h)⟩
    · obtain ⟨r', hr', h⟩ := Finset.prod_eq_zero_iff.1 h
      simp only [eval_sub, eval_X, eval_C] at h
      exact ⟨r', hr', Or.inr (sub_eq_zero.1 h)⟩
  have hintr : ∀ r' ∈ primitiveRoots n ℂ, IsIntegral ℤ r' := fun r' hr' =>
    ((mem_primitiveRoots hn).1 hr').isIntegral hn
  -- the square of a root is `q` times an algebraic integer
  have hsq : ∀ z ∈ (F.map (algebraMap ℤ ℂ)).roots,
      ∃ w : ℂ, IsIntegral ℤ w ∧ z ^ 2 = (q : ℂ) * w := by
    intro z hz
    obtain ⟨r', hr', h | h⟩ := hrootsF z hz
    · refine ⟨(p : ℂ) - 2 * u * r' + (q : ℂ) * r' ^ 2, ?_, ?_⟩
      · exact ((isIntegral_natCast' p).sub (((isIntegral_natCast' 2).mul huint).mul
          (hintr r' hr'))).add ((isIntegral_natCast' q).mul ((hintr r' hr').pow 2))
      · rw [h]
        linear_combination hu2
    · refine ⟨(p : ℂ) + 2 * u * r' + (q : ℂ) * r' ^ 2, ?_, ?_⟩
      · exact ((isIntegral_natCast' p).add (((isIntegral_natCast' 2).mul huint).mul
          (hintr r' hr'))).add ((isIntegral_natCast' q).mul ((hintr r' hr').pow 2))
      · rw [h]
        linear_combination hu2
  have hsubμ : ∀ z ∈ (μ.map (algebraMap ℤ ℂ)).roots, z ∈ (F.map (algebraMap ℤ ℂ)).roots :=
    fun z hz => Multiset.mem_of_le
      (roots.le_of_dvd hmonF.ne_zero (Dvd.intro _ hmap.symm)) hz
  have hsubH : ∀ z ∈ (H.map (algebraMap ℤ ℂ)).roots, z ∈ (F.map (algebraMap ℤ ℂ)).roots :=
    fun z hz => Multiset.mem_of_le
      (roots.le_of_dvd hmonF.ne_zero (Dvd.intro_left _ hmap.symm)) hz
  obtain ⟨C, hC⟩ := pow_dvd_eval_zero_sq hq hmonμ fun z hz => hsq z (hsubμ z hz)
  obtain ⟨C', hC'⟩ := pow_dvd_eval_zero_sq hq hmonH fun z hz => hsq z (hsubH z hz)
  rw [hδ] at hC
  rw [hε] at hC'
  refine ⟨C, C', ⟨(q : ℤ) ^ δ, by rw [hC, mul_comm]⟩, ?_, ?_⟩
  · -- the product
    have h0 := hF 0
    rw [sub_zero, sub_zero, hH, BaseB.aeval_zero_int, eval_mul] at h0
    rw [← h0, ← Int.cast_pow, mul_pow, hC, hC', ← hsum, pow_add]
    congr 1
    ring
  -- the size of `C'`
  obtain ⟨B, hB⟩ : ∃ B : ℝ, (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ 2 = B := ⟨_, rfl⟩
  rw [hB]
  have hsp := Real.sqrt_nonneg (p : ℝ)
  have hsq0 := Real.sqrt_nonneg (q : ℝ)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hsqq : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) := Real.sq_sqrt (Nat.cast_nonneg q)
  have hB1 : 1 ≤ B := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.2 hp1
    rw [← hB]
    nlinarith
  have hroots : ∀ z ∈ (H.map (algebraMap ℤ ℂ)).roots,
      ‖z‖ ≤ Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) + (q : ℝ) := by
    intro z hz
    obtain ⟨r', hr', h | h⟩ := hrootsF z (hsubH z hz)
    · rw [h]
      calc ‖u - (q : ℂ) * r'‖ ≤ ‖u‖ + ‖(q : ℂ) * r'‖ := norm_sub_le _ _
        _ = Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) + (q : ℝ) := by
          rw [hunorm, norm_mul, hnorm r' hr', Complex.norm_natCast, mul_one]
    · rw [h]
      calc ‖-u - (q : ℂ) * r'‖ ≤ ‖-u‖ + ‖(q : ℂ) * r'‖ := norm_sub_le _ _
        _ = Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) + (q : ℝ) := by
          rw [norm_neg, hunorm, norm_mul, hnorm r' hr', Complex.norm_natCast, mul_one]
  have hsplit : (H.map (algebraMap ℤ ℂ)).Splits := IsAlgClosed.splits _
  have hc0 : ((H.eval 0 : ℤ) : ℂ) =
      (-1) ^ (H.map (algebraMap ℤ ℂ)).natDegree * (H.map (algebraMap ℤ ℂ)).roots.prod := by
    rw [← hsplit.coeff_zero_eq_prod_roots_of_monic hmonH, coeff_zero_eq_eval_zero,
      eval_map_algebraMap, BaseB.aeval_zero_int]
  have habs : |((H.eval 0 : ℤ) : ℝ)| ≤
      (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) + (q : ℝ)) ^ ε := by
    calc |((H.eval 0 : ℤ) : ℝ)| = ‖((H.eval 0 : ℤ) : ℂ)‖ := (Complex.norm_intCast _).symm
      _ = ‖(H.map (algebraMap ℤ ℂ)).roots.prod‖ := by
          rw [hc0, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      _ ≤ (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) + (q : ℝ)) ^
            Multiset.card (H.map (algebraMap ℤ ℂ)).roots :=
          BaseB.norm_multiset_prod_le_pow _ hroots
      _ = (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) + (q : ℝ)) ^ ε := by
          rw [← hsplit.natDegree_eq_card_roots, hε]
  have hqB : (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) + (q : ℝ)) ^ 2 = (q : ℝ) * B := by
    rw [← hB]
    linear_combination (Real.sqrt (p : ℝ) ^ 2 - (q : ℝ)) * hsqq
  have hh2 : ((H.eval 0 : ℤ) : ℝ) ^ 2 ≤ (q : ℝ) ^ ε * B ^ ε := by
    rw [← mul_pow, ← hqB, ← pow_mul, mul_comm 2 ε, pow_mul, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hqε : (0 : ℝ) < (q : ℝ) ^ ε := by positivity
  have hC'R : ((H.eval 0 : ℤ) : ℝ) ^ 2 = (q : ℝ) ^ ε * |(C' : ℝ)| := by
    have h1 : ((H.eval 0 : ℤ) : ℝ) ^ 2 = (q : ℝ) ^ ε * (C' : ℝ) := by exact_mod_cast hC'
    have h2 : (0 : ℝ) ≤ (C' : ℝ) := by
      by_contra hneg
      push Not at hneg
      nlinarith [sq_nonneg ((H.eval 0 : ℤ) : ℝ)]
    rw [h1, abs_of_nonneg h2]
  rw [hC'R] at hh2
  calc |(C' : ℝ)| ≤ B ^ ε := le_of_mul_le_mul_left hh2 hqε
    _ ≤ B ^ n.totient := pow_le_pow_right₀ hB1 hεle

end RatBase

end PiFormula
