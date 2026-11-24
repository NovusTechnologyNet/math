module

public import Pilean.BaseB.GeneralDefs

/-!
# Two lemmas for the Kummer homomorphisms

* `dvd_of_rat_pow_eq`: if `b` is not a perfect power and `r^n = b^m` for a positive rational
  `r`, then `n ∣ m`.
* `real_sq_mem_rat`: if a positive real `β` lies in a cyclotomic field `ℚ(ζ_N) ⊆ ℂ` and some
  power `β^k`, `k ≥ 1`, is rational, then `β²` is rational. The Galois group of `ℚ(ζ_N)` is
  abelian, so every automorphism `τ` commutes with complex conjugation; hence `τ β` is real,
  and `(τ β)^k = β^k` gives `τ β = ± β`. So `β²` is fixed by the whole Galois group.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-! ## 1. Arithmetic -/

/-- A positive rational whose `k`-th power is a natural number is a natural number. -/
theorem exists_nat_of_rat_pow {s : ℚ} (hs : 0 < s) {k b : ℕ} (hk : 0 < k)
    (h : s ^ k = b) : ∃ a : ℕ, s = a := by
  have hx : (s : ℝ) ^ k = ((b : ℤ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h
    simpa using this
  by_cases hv : ∃ y : ℤ, (s : ℝ) = y
  · obtain ⟨y, hy⟩ := hv
    have hy' : s = y := by exact_mod_cast hy
    have hy0 : 0 < y := by rw [hy'] at hs; exact_mod_cast hs
    refine ⟨y.toNat, ?_⟩
    rw [hy']
    exact_mod_cast (Int.toNat_of_nonneg hy0.le).symm
  · exact absurd (irrational_nrt_of_notint_nrt k b hx hv hk) (Rat.not_irrational s)

/-- If `b` is not a perfect power and `r^n = b^m` with `r` a positive rational and `n ≥ 1`,
then `n ∣ m`. -/
theorem dvd_of_rat_pow_eq {b : ℕ} (hpp : NotPerfectPower b) {r : ℚ} (hr : 0 < r) {n m : ℕ}
    (hn : 0 < n) (h : r ^ n = (b : ℚ) ^ m) : n ∣ m := by
  have hb0 : (0 : ℚ) < b := by
    have : b ≠ 0 := fun h0 => hpp 0 2 le_rfl (by rw [h0]; rfl)
    exact_mod_cast Nat.pos_of_ne_zero this
  have he0 : 0 < Nat.gcd n m := Nat.gcd_pos_of_pos_left m hn
  obtain ⟨n', hn'⟩ := Nat.gcd_dvd_left n m
  obtain ⟨m', hm'⟩ := Nat.gcd_dvd_right n m
  have hn'0 : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h0 | h0
    · rw [h0, mul_zero] at hn'; omega
    · exact h0
  have hcop : Nat.Coprime n' m' := by
    have h1 := Nat.coprime_div_gcd_div_gcd he0
    have e1 : n / Nat.gcd n m = n' := Nat.div_eq_of_eq_mul_right he0 hn'
    have e2 : m / Nat.gcd n m = m' := Nat.div_eq_of_eq_mul_right he0 hm'
    rwa [e1, e2] at h1
  have h1 : r ^ n' = (b : ℚ) ^ m' := by
    have h2 : (r ^ n') ^ Nat.gcd n m = ((b : ℚ) ^ m') ^ Nat.gcd n m := by
      rw [← pow_mul, ← pow_mul, mul_comm n', mul_comm m', ← hn', ← hm', h]
    exact (pow_left_inj₀ (pow_pos hr _).le (pow_pos hb0 _).le he0.ne').1 h2
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * n' + v * m' = 1 := Nat.isCoprime_iff_coprime.2 hcop
  have e1 : ((b : ℚ) ^ u) ^ n' = (b : ℚ) ^ (u * n') := by rw [zpow_mul, zpow_natCast]
  have e2 : (r ^ v) ^ n' = (r ^ n') ^ v := by
    rw [← zpow_natCast (r ^ v), ← zpow_mul, mul_comm v, zpow_mul, zpow_natCast]
  have e3 : ((b : ℚ) ^ m') ^ v = (b : ℚ) ^ (v * m') := by
    rw [← zpow_natCast (b : ℚ) m', ← zpow_mul, mul_comm v]
  have hs : ((b : ℚ) ^ u * r ^ v) ^ n' = b := by
    rw [mul_pow, e1, e2, h1, e3, ← zpow_add₀ hb0.ne', huv, zpow_one]
  obtain ⟨a, ha⟩ := exists_nat_of_rat_pow
    (mul_pos (zpow_pos hb0 u) (zpow_pos hr v)) hn'0 hs
  have hab : a ^ n' = b := by
    rw [ha] at hs
    exact_mod_cast hs
  have hn'1 : n' = 1 := by
    by_contra hne
    exact hpp a n' (by omega) hab
  rw [hn', hn'1, mul_one]
  exact Nat.gcd_dvd_right n m

/-! ## 2. Real elements of a cyclotomic field -/

/-- The cyclotomic field `ℚ(ζ_N)` inside `ℂ`. -/
noncomputable abbrev cycField (N : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {zetaN N}

/-- If a positive real `β` lies in `ℚ(ζ_N)` and `β^k` is rational for some `k ≥ 1`, then `β²`
is rational. -/
theorem real_sq_mem_rat {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 0 < β)
    (hmem : (β : ℂ) ∈ cycField N) {k : ℕ} (hk : 0 < k) {q : ℚ} (hq : β ^ k = q) :
    ∃ r : ℚ, (r : ℝ) = β ^ 2 := by
  have : NeZero N := ⟨hN.ne'⟩
  have : IsCyclotomicExtension {N} ℚ (cycField N) :=
    (zetaN_prim hN).intermediateField_adjoin_isCyclotomicExtension ℚ
  have : IsAbelianGalois ℚ (cycField N) := IsCyclotomicExtension.isAbelianGalois {N} ℚ _
  have : FiniteDimensional ℚ (cycField N) := IsCyclotomicExtension.finiteDimensional {N} ℚ _
  -- complex conjugation on `ℚ(ζ_N)`
  let κ : (cycField N) ≃ₐ[ℚ] (cycField N) :=
    (Complex.conjAe.restrictScalars ℚ).restrictNormal (cycField N)
  have hκ : ∀ y : cycField N, ((κ y : cycField N) : ℂ) = (starRingEnd ℂ) (y : ℂ) := fun y =>
    AlgEquiv.restrictNormal_commutes (Complex.conjAe.restrictScalars ℚ) (cycField N) y
  obtain ⟨x, hxβ⟩ : ∃ x : cycField N, (x : ℂ) = (β : ℂ) := ⟨⟨β, hmem⟩, rfl⟩
  have hκx : κ x = x := Subtype.ext (by rw [hκ, hxβ]; exact Complex.conj_ofReal β)
  have hxk : x ^ k = algebraMap ℚ (cycField N) q := by
    apply Subtype.ext
    have : ((β : ℂ)) ^ k = (q : ℂ) := by exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hq
    simpa [hxβ] using this
  have hfix : ∀ τ : (cycField N) ≃ₐ[ℚ] (cycField N), τ (x ^ 2) = x ^ 2 := by
    intro τ
    have h1 : κ (τ x) = τ x := by
      have h0 : (κ * τ) x = (τ * κ) x := by rw [mul_comm' κ τ]
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hκx] at h0
      exact h0
    have h2 : (starRingEnd ℂ) ((τ x : cycField N) : ℂ) = ((τ x : cycField N) : ℂ) := by
      rw [← hκ, h1]
    obtain ⟨y, hy⟩ := Complex.conj_eq_iff_real.1 h2
    have h3 : y ^ k = β ^ k := by
      have h4 : (τ x) ^ k = x ^ k := by rw [← map_pow, hxk, AlgEquiv.commutes]
      have h5 := congrArg (fun z : cycField N => (z : ℂ)) h4
      simp only [IntermediateField.coe_pow, hy, hxβ] at h5
      exact_mod_cast h5
    have h4 : y ^ 2 = β ^ 2 := by
      have h5 : |y| = β := by
        have h6 : |y| ^ k = β ^ k := by rw [← abs_pow, h3, abs_of_pos (pow_pos hβ k)]
        exact (pow_left_inj₀ (abs_nonneg y) hβ.le hk.ne').1 h6
      rw [← sq_abs, h5]
    apply Subtype.ext
    rw [map_pow]
    simp only [IntermediateField.coe_pow, hy, hxβ]
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) h4
  obtain ⟨r, hr⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (x ^ 2)).2 hfix
  refine ⟨r, ?_⟩
  have h7 := congrArg (fun z : cycField N => (z : ℂ)) hr
  simp only [IntermediateField.coe_pow, hxβ] at h7
  have h8 : ((r : ℝ) : ℂ) = ((β ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]
    simpa using h7
  exact_mod_cast h8

end BaseB

end PiFormula
