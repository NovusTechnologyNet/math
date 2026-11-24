module

public import Pilean.BaseB.KummerAux

/-!
# The Kummer homomorphisms

`kummerHom`: if `b ≥ 2` is not a perfect power and `n ≥ 1`, then `KummerHom b n` holds: for
every `M ≥ 1` and every `η` with `η^(n₁) = 1`, `n₁ = halfIfEven n`, a field homomorphism
`ℚ(ζ_M, c) → ℂ` sends `c = b^(1/n)` to `η c` and fixes `ζ_M`.

Proof. Let `L = ℚ(ζ_N)` with `N = M n`, let `f` be the minimal polynomial of `c` over `L` and
`d` its degree.

* The roots of `f` in `ℂ` are roots of `X^n - b`, so their product `P` has `P^n = b^d =
  (c^d)^n`; and `± P` is the constant term of `f`. Since `L` contains the `n`-th roots of
  unity, `c^d ∈ L` (`cB_pow_natDegree_mem`).
* `c^d` is a positive real number of the abelian field `L` and its `n`-th power is rational, so
  `c^(2d)` is a rational number `r` (`real_sq_mem_rat`). From `r^n = b^(2d)`, and `b` not a
  perfect power, `n ∣ 2d` (`dvd_of_rat_pow_eq`); hence `n₁ ∣ d`.
* So `f = X^d - c^d`, of which `η c` is a root, as `η^d = 1`. This gives a homomorphism
  `L(c) → ℂ` over `L` with `c ↦ η c`; restrict it to `ℚ(ζ_M, c)`.

Mathlib's criterion for the irreducibility of `X^n - a` covers odd `n` only; the proof above
does not use it.
-/

@[expose] public section

open Complex Polynomial IntermediateField

namespace PiFormula

namespace BaseB

/-! ## 1. The real root `c = b^(1/n)` -/

theorem rpow_one_div_pow (b : ℕ) {n : ℕ} (hn : 0 < n) :
    ((b : ℝ) ^ ((1 : ℝ) / (n : ℝ))) ^ n = b := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg b),
    one_div_mul_cancel (Nat.cast_ne_zero.2 hn.ne'), Real.rpow_one]

theorem cB_pow_eq (b : ℕ) {n : ℕ} (hn : 0 < n) : cB b n ^ n = b := by
  rw [cB, ← Complex.ofReal_pow, rpow_one_div_pow b hn]
  simp

theorem cB_ne_zero_of_pos {b : ℕ} (hb : 0 < b) (n : ℕ) : cB b n ≠ 0 := by
  rw [cB]
  exact_mod_cast (Real.rpow_pos_of_pos (Nat.cast_pos.2 hb) _).ne'

theorem cB_isIntegral (b : ℕ) {n : ℕ} (hn : 0 < n) (L : IntermediateField ℚ ℂ) :
    IsIntegral L (cB b n) := by
  refine IsIntegral.of_pow hn ?_
  rw [cB_pow_eq b hn]
  exact (isIntegral_algebraMap (R := L) (A := ℂ) (x := (b : L)))

/-! ## 2. `c^d ∈ ℚ(ζ_N)`, where `d` is the degree of `c` over `ℚ(ζ_N)` -/

theorem prod_pow_eq_of_forall {n : ℕ} {B : ℂ} (s : Multiset ℂ) (h : ∀ r ∈ s, r ^ n = B) :
    s.prod ^ n = B ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, mul_pow, Multiset.card_cons, pow_succ,
      ih (fun r hr => h r (Multiset.mem_cons_of_mem hr)), h a (Multiset.mem_cons_self a s),
      mul_comm]

/-- If `n ∣ N`, then `c^d ∈ ℚ(ζ_N)`, where `d` is the degree of the minimal polynomial of
`c = b^(1/n)` over `ℚ(ζ_N)`. -/
theorem cB_pow_natDegree_mem {b n N : ℕ} (hb : 0 < b) (hn : 0 < n) (hN : 0 < N)
    (hnN : n ∣ N) :
    cB b n ^ (minpoly (cycField N) (cB b n)).natDegree ∈ cycField N := by
  have hcn : cB b n ^ n = (b : ℂ) := cB_pow_eq b hn
  have hb0 : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  have hint : IsIntegral (cycField N) (cB b n) := cB_isIntegral b hn _
  have hdvd : minpoly (cycField N) (cB b n) ∣ X ^ n - C ((b : ℕ) : cycField N) :=
    minpoly.dvd _ _ (by simp [hcn])
  have hmonic := minpoly.monic hint
  obtain ⟨g, hg⟩ : ∃ g : ℂ[X],
      g = (minpoly (cycField N) (cB b n)).map (algebraMap (cycField N) ℂ) := ⟨_, rfl⟩
  have hgm : g.Monic := hg ▸ hmonic.map _
  have hgs : g.Splits := IsAlgClosed.splits g
  have hgd : g.natDegree = (minpoly (cycField N) (cB b n)).natDegree := by
    rw [hg, natDegree_map]
  have hroots : ∀ r ∈ g.roots, r ^ n = (b : ℂ) := by
    intro r hr
    have h1 : IsRoot g r := (mem_roots hgm.ne_zero).1 hr
    have h2 : g ∣ X ^ n - C (b : ℂ) := by
      have h := Polynomial.map_dvd (algebraMap (cycField N) ℂ) hdvd
      rw [← hg] at h
      simpa using h
    have h3 := h1.dvd h2
    simpa [sub_eq_zero] using h3
  have hprod : g.roots.prod ^ n = (b : ℂ) ^ (minpoly (cycField N) (cB b n)).natDegree := by
    rw [prod_pow_eq_of_forall _ hroots, ← hgs.natDegree_eq_card_roots, hgd]
  have hP0 : g.roots.prod ≠ 0 := fun h0 => by
    rw [h0, zero_pow hn.ne'] at hprod
    exact pow_ne_zero _ hb0 hprod.symm
  have hPmem : g.roots.prod ∈ cycField N := by
    have h1 : g.coeff 0 = (-1) ^ g.natDegree * g.roots.prod :=
      hgs.coeff_zero_eq_prod_roots_of_monic hgm
    have h2 : g.roots.prod = (-1) ^ g.natDegree * g.coeff 0 := by
      rw [h1, ← mul_assoc, ← mul_pow]
      simp
    rw [h2, hg, coeff_map]
    exact mul_mem (pow_mem (neg_mem (one_mem _)) _) (SetLike.coe_mem _)
  have hq : (g.roots.prod / cB b n ^ (minpoly (cycField N) (cB b n)).natDegree) ^ N = 1 := by
    obtain ⟨j, rfl⟩ := hnN
    rw [pow_mul, div_pow, hprod, ← pow_mul, mul_comm _ n, pow_mul, hcn,
      div_self (pow_ne_zero _ hb0), one_pow]
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := (zetaN_prim hN).eq_pow_of_pow_eq_one hq
  have hz : zetaN N ∈ cycField N := subset_adjoin ℚ _ (Set.mem_singleton _)
  have hc : cB b n ^ (minpoly (cycField N) (cB b n)).natDegree =
      g.roots.prod / zetaN N ^ i := by
    rw [hi, div_div_cancel₀ hP0]
  rw [hc]
  exact div_mem hPmem (pow_mem hz i)

/-! ## 3. The main theorem -/

/-- `ζ_M ∈ ℚ(ζ_N)` when `M ∣ N`. -/
theorem zetaN_mem_cycField {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (hMN : M ∣ N) :
    zetaN M ∈ cycField N := by
  have h1 : zetaN M ^ N = 1 := by
    obtain ⟨j, rfl⟩ := hMN
    rw [pow_mul, (zetaN_prim hM).pow_eq_one, one_pow]
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := (zetaN_prim hN).eq_pow_of_pow_eq_one h1
  rw [← hi]
  exact pow_mem (subset_adjoin ℚ _ (Set.mem_singleton _)) i

/-- `halfIfEven n` divides `d` when `n ∣ 2 d`. -/
theorem halfIfEven_dvd_of_dvd_two_mul {n d : ℕ} (h : n ∣ 2 * d) : halfIfEven n ∣ d := by
  unfold halfIfEven
  split_ifs with he
  · obtain ⟨j, hj⟩ := he
    have h1 : n / 2 = j := by omega
    have h2 : 2 * j ∣ 2 * d := by rwa [show 2 * j = n by omega]
    rw [h1]
    exact (Nat.mul_dvd_mul_iff_left two_pos).1 h2
  · have hodd : Odd n := Nat.not_even_iff_odd.1 he
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.2 hodd)) h

/-- **The Kummer homomorphisms.** If `b ≥ 2` is not a perfect power and `n ≥ 1`, then for
every `M ≥ 1` and every `η` with `η^(halfIfEven n) = 1`, some field homomorphism
`ℚ(ζ_M, c) → ℂ` sends `c = b^(1/n)` to `η c` and fixes `ζ_M`. -/
theorem kummerHom {b n : ℕ} (hb : 2 ≤ b) (hpp : NotPerfectPower b) (hn : 0 < n) :
    KummerHom b n := by
  intro M hM η hη
  have hb0 : 0 < b := by omega
  have hN : 0 < M * n := Nat.mul_pos hM hn
  have hint : IsIntegral (cycField (M * n)) (cB b n) := cB_isIntegral b hn _
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = (minpoly (cycField (M * n)) (cB b n)).natDegree := ⟨_, rfl⟩
  have hd0 : 0 < d := hd ▸ minpoly.natDegree_pos hint
  have hmem : cB b n ^ d ∈ cycField (M * n) :=
    hd ▸ cB_pow_natDegree_mem hb0 hn hN (Dvd.intro_left M rfl)
  -- `halfIfEven n ∣ d`
  have hcr0 : (0 : ℝ) < (b : ℝ) ^ ((1 : ℝ) / (n : ℝ)) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.2 hb0) _
  have hreal : cB b n ^ d = ((((b : ℝ) ^ ((1 : ℝ) / (n : ℝ))) ^ d : ℝ) : ℂ) := by
    rw [cB, Complex.ofReal_pow]
  obtain ⟨r, hr⟩ := real_sq_mem_rat hN (pow_pos hcr0 d) (hreal ▸ hmem) hn (q := (b : ℚ) ^ d)
    (by rw [← pow_mul, mul_comm, pow_mul, rpow_one_div_pow b hn]; simp)
  have hr0 : 0 < r := by
    have h1 : (0 : ℝ) < r := by rw [hr]; exact pow_pos (pow_pos hcr0 d) 2
    exact_mod_cast h1
  have hrn : r ^ n = (b : ℚ) ^ (2 * d) := by
    have h1 : ((r ^ n : ℚ) : ℝ) = (((b : ℚ) ^ (2 * d) : ℚ) : ℝ) := by
      have e : ((((b : ℝ) ^ ((1 : ℝ) / (n : ℝ))) ^ d) ^ 2) ^ n =
          (((b : ℝ) ^ ((1 : ℝ) / (n : ℝ))) ^ n) ^ (2 * d) := by ring
      push_cast
      rw [hr, e, rpow_one_div_pow b hn]
    exact_mod_cast h1
  have hn1 : halfIfEven n ∣ d := halfIfEven_dvd_of_dvd_two_mul (dvd_of_rat_pow_eq hpp hr0 hn hrn)
  have hηd : η ^ d = 1 := by
    obtain ⟨j, hj⟩ := hn1
    rw [hj, pow_mul, hη, one_pow]
  -- the minimal polynomial is `X^d - c^d`
  obtain ⟨γ, hγ⟩ : ∃ γ : cycField (M * n), (γ : ℂ) = cB b n ^ d := ⟨⟨_, hmem⟩, rfl⟩
  have hf : minpoly (cycField (M * n)) (cB b n) = X ^ d - C γ := by
    have hdvd : minpoly (cycField (M * n)) (cB b n) ∣ X ^ d - C γ :=
      minpoly.dvd _ _ (by simp [hγ])
    exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (monic_X_pow_sub_C γ hd0.ne') hdvd (by rw [natDegree_X_pow_sub_C, hd])).symm
  have hroot : η * cB b n ∈ (minpoly (cycField (M * n)) (cB b n)).aroots ℂ := by
    rw [mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [hf]
    simp [hγ, mul_pow, hηd]
  -- the homomorphism over `ℚ(ζ_N)`
  obtain ⟨φ, hφ⟩ : ∃ φ : (cycField (M * n))⟮cB b n⟯ →ₐ[cycField (M * n)] ℂ,
      φ (AdjoinSimple.gen (cycField (M * n)) (cB b n)) = η * cB b n :=
    ⟨(algHomAdjoinIntegralEquiv (cycField (M * n)) hint).symm ⟨η * cB b n, hroot⟩,
      algHomAdjoinIntegralEquiv_symm_apply_gen (cycField (M * n)) hint _⟩
  have hζM : zetaN M ∈ cycField (M * n) := zetaN_mem_cycField hM hN (Dvd.intro n rfl)
  have hle : IntermediateField.adjoin ℚ ({zetaN M, cB b n} : Set ℂ) ≤
      ((cycField (M * n))⟮cB b n⟯).restrictScalars ℚ := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | rfl)
    · exact IntermediateField.algebraMap_mem _ (⟨zetaN M, hζM⟩ : cycField (M * n))
    · exact mem_adjoin_simple_self _ _
  let ι : (IntermediateField.adjoin ℚ ({zetaN M, cB b n} : Set ℂ)) →ₐ[ℚ]
      (cycField (M * n))⟮cB b n⟯ :=
    { toFun := fun x => ⟨x.1, hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  refine ⟨(φ.restrictScalars ℚ).comp ι, ?_, ?_⟩
  · intro x hx
    have h1 : ι x = AdjoinSimple.gen (cycField (M * n)) (cB b n) := Subtype.ext hx
    change φ (ι x) = _
    rw [h1, hφ]
  · intro x hx
    have h1 : ι x = algebraMap (cycField (M * n)) (cycField (M * n))⟮cB b n⟯
        (⟨zetaN M, hζM⟩ : cycField (M * n)) := Subtype.ext hx
    change φ (ι x) = _
    rw [h1, φ.commutes]
    rfl

end BaseB

end PiFormula
