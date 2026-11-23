import Pilean.Base5.LogValues

/-!
# Base 5: which logarithms are values (the criterion)

`baseSpan5` is the set of rational combinations of the logarithms of the base numbers
`(5^m - 1)/5^m`, `L_h/5^(2h)`, `M_h/5^(2h)` (`Base5/LogValues.lean`, where it is proved that
every element of `baseSpan5` is a value of the class F5).

* `mem_baseSpan5_of_isF5Value_log` (from Baker's theorem): if `log (a/b)` is a value of F5, it
  lies in `baseSpan5`.
* `isF5Value_log_iff`, `isF5Value_log_rat_iff`: the criterion, in terms of the span.
* `isF5Value_log_rat_iff_pow`: **for a positive rational number `y`, `log y` is the value of a
  series `∑ ρ(k) 5^(-⌊k/2⌋)/k` with `ρ` rational and periodic if and only if some power `y^k`,
  `k ≥ 1`, is a product of integer powers of base numbers.**

The proof of the converse follows `Base3/LogConverse.lean`, with two changes.

1. A cleared relation is an integer polynomial identity at `ζ = exp(2πi/N)`, `N = 5K`, with
   `√5 = ±(η - η² - η³ + η⁴)`, `η = ζ^K` (the Gauss sum). It holds at `ζ^a` for every `a` prime
   to `N`, but no `a` other than those with `(a/5) = 1` fixes `√5`: the substitution sends `t`
   to `(a/5) t` and `t - r` to `(a/5) t - r^a = (a/5) (t - (a/5) r^a)` (`cleared_conj5`). So
   one adds the logarithms of absolute values over all `a` prime to `N`, with the action
   `r ↦ (a/5) r^a` on the roots.
2. `log 5` is not available, so the relation is kept in the normalized form: the factors are
   the `1 - r/t`, and the powers of `t` on the two sides cancel because the relation has
   degree 0 (`hdeg` in `log_sub_mem_baseSpan5_of_cleared`).

Sorting the terms by Möbius inversion leaves, for a fifth root of unity `v` and `T = t^M`,
the four-term products `∏_{ρ=1..4} (1 - (±(ρ/5))^M v^ρ / T)`. For even `M` these are
`(1 - 1/T)^4` or `(1 - T^(-5))/(1 - 1/T)`; for odd `M` they are `(1 - 1/T²)²` or one of the two
Aurifeuillian numbers `L_M/5^(2M)`, `M_M/5^(2M)` (`prod_even_mem`, `prod_odd_mem`).
-/

open Complex Polynomial

namespace PiFormula

namespace Base5

/-! ## 1. Relations up to a power of a rational number, and Baker's theorem -/

/-- A multiplicative relation among the `1 - r/t` up to a power of `a / b`. -/
def IsRel5 (a b : ℂ) (S : Finset ℂ) (e : ℂ → ℤ) (m : ℤ) : Prop :=
  ∃ ξ : ℂ, IsOfFinOrder ξ ∧ ∏ r ∈ S, (1 - r / t5) ^ (e r) = ξ * (a / b) ^ m

/-- The cleared form of a relation: no denominators and no negative exponents. -/
theorem cleared5 {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ} (h : IsRel5 a b S e m) :
    ∃ ξ : ℂ, IsOfFinOrder ξ ∧
      (∏ r ∈ S, (t5 - r) ^ (e r).toNat) * t5 ^ (∑ r ∈ S, (-e r).toNat) *
          (a ^ (-m).toNat * b ^ m.toNat) =
        ξ * (∏ r ∈ S, (t5 - r) ^ (-e r).toNat) * t5 ^ (∑ r ∈ S, (e r).toNat) *
          (a ^ m.toNat * b ^ (-m).toNat) := by
  obtain ⟨ξ, hξ, hrel⟩ := h
  refine ⟨ξ, hξ, ?_⟩
  -- each factor: (1 - r/t)^e (t - r)^(-e)⁺ t^(e⁺) = (t - r)^(e⁺) t^((-e)⁺)
  have hfac : ∀ r ∈ S, (1 - r / t5) ^ (e r) * ((t5 - r) ^ (-e r).toNat * t5 ^ (e r).toNat) =
      (t5 - r) ^ (e r).toNat * t5 ^ (-e r).toNat := by
    intro r hr
    have hne : t5 - r ≠ 0 := t5_sub_ne_zero (norm_root (hS r hr))
    have hz1 : (t5 - r) ^ (e r) = (t5 - r) ^ (e r).toNat / (t5 - r) ^ (-e r).toNat := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hne]
      congr 1
      omega
    have hz2 : t5 ^ (e r) = t5 ^ (e r).toNat / t5 ^ (-e r).toNat := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ t5_ne_zero]
      congr 1
      omega
    have h1 : (t5 - r) ^ (-e r).toNat ≠ 0 := pow_ne_zero _ hne
    have h2 : t5 ^ (-e r).toNat ≠ 0 := pow_ne_zero _ t5_ne_zero
    have h3 : t5 ^ (e r).toNat ≠ 0 := pow_ne_zero _ t5_ne_zero
    rw [w5_eq, div_zpow, hz1, hz2]
    field_simp
  have hprod := Finset.prod_congr rfl hfac
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, hrel] at hprod
  have ea : a ^ m * a ^ (-m).toNat = a ^ m.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ha]
    congr 1
    omega
  have eb : b ^ m * b ^ (-m).toNat = b ^ m.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hb]
    congr 1
    omega
  have hbm : b ^ m ≠ 0 := zpow_ne_zero m hb
  have hz : (a / b) ^ m * (a ^ (-m).toNat * b ^ m.toNat) = a ^ m.toNat * b ^ (-m).toNat := by
    rw [div_zpow, div_mul_eq_mul_div, div_eq_iff hbm]
    calc a ^ m * (a ^ (-m).toNat * b ^ m.toNat) = (a ^ m * a ^ (-m).toNat) * b ^ m.toNat := by
          ring
      _ = a ^ m.toNat * (b ^ m * b ^ (-m).toNat) := by rw [ea, eb]
      _ = a ^ m.toNat * b ^ (-m).toNat * b ^ m := by ring
  calc (∏ r ∈ S, (t5 - r) ^ (e r).toNat) * t5 ^ (∑ r ∈ S, (-e r).toNat) *
        (a ^ (-m).toNat * b ^ m.toNat)
      = (ξ * (a / b) ^ m * ((∏ r ∈ S, (t5 - r) ^ (-e r).toNat) *
          t5 ^ (∑ r ∈ S, (e r).toNat))) * (a ^ (-m).toNat * b ^ m.toNat) := by rw [hprod]
    _ = ξ * (∏ r ∈ S, (t5 - r) ^ (-e r).toNat) * t5 ^ (∑ r ∈ S, (e r).toNat) *
          ((a / b) ^ m * (a ^ (-m).toNat * b ^ m.toNat)) := by ring
    _ = ξ * (∏ r ∈ S, (t5 - r) ^ (-e r).toNat) * t5 ^ (∑ r ∈ S, (e r).toNat) *
          (a ^ m.toNat * b ^ (-m).toNat) := by rw [hz]

/-- The logarithms: `Λ` at `none`, `iπ` at `some none`, and the `Log(1 - r/t)`. -/
noncomputable def lam5 (Λ : ℂ) : Option (Option ℂ) → ℂ
  | none => Λ
  | some none => Real.pi * I
  | some (some r) => Complex.log (1 - r / t5)

/-- An integer relation among `Λ`, `iπ` and the `Log(1 - r/t)`, where `exp Λ = a / b`, is a
multiplicative relation among the `1 - r/t` up to a power of `a / b`. -/
theorem rel5_of_intRel {a b Λ : ℂ} (hΛ : Complex.exp Λ = a / b) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {z : Option (Option ℂ) → ℤ}
    (hz : ∑ i ∈ Finset.insertNone (Finset.insertNone S), (z i : ℂ) * lam5 Λ i = 0) :
    IsRel5 a b S (fun r => z (some (some r))) (-z none) := by
  rw [Finset.sum_insertNone, Finset.sum_insertNone] at hz
  have hz' : (z none : ℂ) * Λ + ((z (some none) : ℂ) * (Real.pi * I) +
      ∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / t5)) = 0 := hz
  have h1 : ∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / t5) =
      -(z (some none) : ℂ) * (Real.pi * I) + ((-z none : ℤ) : ℂ) * Λ := by
    rw [Int.cast_neg]
    linear_combination hz'
  have hexp : Complex.exp (∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / t5)) =
      ∏ r ∈ S, (1 - r / t5) ^ (z (some (some r))) := by
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [Complex.exp_int_mul, Complex.exp_log (w5_ne_zero (hS r hr))]
  refine ⟨Complex.exp (-(z (some none) : ℂ) * (Real.pi * I)), ?_, ?_⟩
  · refine isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, ?_⟩
    rw [← Complex.exp_nat_mul]
    have e : ((2 : ℕ) : ℂ) * (-(z (some none) : ℂ) * (Real.pi * I)) =
        ((-z (some none) : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  · rw [← hexp, h1, Complex.exp_add, Complex.exp_int_mul Λ (-z none), hΛ]

/-- **Baker's theorem with one more logarithm, in base 5.** Let `exp Λ = a / b` be algebraic.
If no multiplicative relation among the `1 - r/t` involves a non-zero power of `a / b`, then
no combination of the `Log(1 - r/t)` with algebraic coefficients is a non-zero algebraic
multiple of `Λ`. -/
theorem baker_no_extra5 (hB : BakerTheorem) {a b Λ : ℂ} (hΛ : Complex.exp Λ = a / b)
    (halg : IsAlgebraic ℚ (a / b))
    (hmul : ∀ S : Finset ℂ, (∀ r ∈ S, IsOfFinOrder r) → ∀ (e : ℂ → ℤ) (m : ℤ),
      IsRel5 a b S e m → m = 0)
    {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {d : ℂ → ℂ}
    (hd : ∀ r ∈ S, IsAlgebraic ℚ (d r)) {q : ℂ} (hq : IsAlgebraic ℚ q)
    (h : ∑ r ∈ S, d r * Complex.log (1 - r / t5) = q * Λ) : q = 0 := by
  classical
  let β : Option (Option ℂ) → ℂ := fun o =>
    match o with
    | none => -q
    | some none => 0
    | some (some r) => if r ∈ S then d r else 0
  have hβS : ∀ r ∈ S, β (some (some r)) = d r := fun r hr => by simp only [β, hr, ↓reduceIte]
  have hF : ∀ x ∈ algebraicClosure ℚ ℂ, IsAlgebraic ℚ x := fun x hx =>
    mem_algebraicClosure_iff.1 hx
  have hspan : SpanIn (algebraicClosure ℚ ℂ)
      (IntRel (Finset.insertNone (Finset.insertNone S)) (lam5 Λ)) β := by
    refine baker_descent hB _ hF (lam5 Λ) _ ?_ β ?_ ?_ ?_
    · intro i hi
      rcases i with _ | _ | r
      · change IsAlgebraic ℚ (Complex.exp Λ)
        rw [hΛ]
        exact halg
      · change IsAlgebraic ℚ (Complex.exp (Real.pi * I))
        rw [Complex.exp_pi_mul_I]
        exact isAlgebraic_one.neg
      · have hr : r ∈ S := Finset.some_mem_insertNone.1 (Finset.some_mem_insertNone.1 hi)
        change IsAlgebraic ℚ (Complex.exp (Complex.log (1 - r / t5)))
        rw [Complex.exp_log (w5_ne_zero (hS r hr)), div_eq_mul_inv]
        exact isAlgebraic_one.sub ((isAlgebraic_root (hS r hr)).mul isAlgebraic_t5.inv)
    · intro i hi
      rcases i with _ | _ | r
      · exact mem_algebraicClosure_iff.2 hq.neg
      · exact mem_algebraicClosure_iff.2 isAlgebraic_zero
      · have hr : r ∈ S := Finset.some_mem_insertNone.1 (Finset.some_mem_insertNone.1 hi)
        rw [hβS r hr]
        exact mem_algebraicClosure_iff.2 (hd r hr)
    · intro i hi
      rcases i with _ | _ | r
      · exact absurd (by simp) hi
      · exact absurd (by simp) hi
      · have hr : r ∉ S := fun hr =>
          hi (Finset.some_mem_insertNone.2 (Finset.some_mem_insertNone.2 hr))
        simp only [β, hr, ↓reduceIte]
    · rw [Finset.sum_insertNone, Finset.sum_insertNone]
      have e : ∑ r ∈ S, β (some (some r)) * lam5 Λ (some (some r)) =
          ∑ r ∈ S, d r * Complex.log (1 - r / t5) :=
        Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
      rw [e, h]
      change -q * Λ + (0 * (Real.pi * I) + q * Λ) = 0
      ring
  have key : ∀ v ∈ IntRel (Finset.insertNone (Finset.insertNone S)) (lam5 Λ), v none = 0 := by
    rintro v ⟨z, -, hzsum, hv⟩
    have h0 := hmul S hS _ _ (rel5_of_intRel hΛ hS hzsum)
    have h1 : z none = 0 := by omega
    rw [hv, h1, Int.cast_zero]
  have hnone : ∀ β' : Option (Option ℂ) → ℂ,
      SpanIn (algebraicClosure ℚ ℂ)
        (IntRel (Finset.insertNone (Finset.insertNone S)) (lam5 Λ)) β' → β' none = 0 := by
    intro β' hβ'
    induction hβ' with
    | zero => rfl
    | step c hc v hv w _ ih =>
      change c * v none + w none = 0
      rw [key v hv, ih, mul_zero, add_zero]
  have h0 : -q = 0 := hnone β hspan
  exact neg_eq_zero.1 h0

/-! ## 2. Conjugating an identity between roots of unity -/

/-- **Conjugating a cleared relation.** An identity between products of the `t - r` (`r` roots
of unity), powers of `t = √5` and integers, up to a root of unity `ξ`, stays true when every
`r` and `ξ` are raised to a power `a` prime to their orders and `t` is replaced by `(a/5) t`.
(Here `5K` is a common multiple of the orders.) -/
theorem cleared_conj5 {S : Finset ℂ} {ξ : ℂ} (p n : ℂ → ℕ) (A B c₁ c₂ : ℕ) {K : ℕ}
    (hK : 0 < K) (hSK : ∀ r ∈ S, r ^ (5 * K) = 1) (hξK : ξ ^ (5 * K) = 1)
    (h : (∏ r ∈ S, (t5 - r) ^ p r) * t5 ^ A * (c₁ : ℂ) =
      ξ * (∏ r ∈ S, (t5 - r) ^ n r) * t5 ^ B * (c₂ : ℂ))
    {a : ℕ} (ha : a.Coprime (5 * K)) :
    (∏ r ∈ S, ((leg5 a : ℂ) * t5 - r ^ a) ^ p r) * ((leg5 a : ℂ) * t5) ^ A * (c₁ : ℂ) =
      ξ ^ a * (∏ r ∈ S, ((leg5 a : ℂ) * t5 - r ^ a) ^ n r) * ((leg5 a : ℂ) * t5) ^ B *
        (c₂ : ℂ) := by
  classical
  have hN0 : 0 < 5 * K := by omega
  have : NeZero (5 * K) := ⟨hN0.ne'⟩
  set ζ := zetaN (5 * K) with hζdef
  have hζ : IsPrimitiveRoot ζ (5 * K) := zetaN_prim hN0
  -- `η = ζ^K` is a fifth root of unity other than 1, and `κ (η - η² - η³ + η⁴) = t`, `κ = ±1`
  have hη5 : (ζ ^ K) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm]
    exact hζ.pow_eq_one
  have hη1 : ζ ^ K ≠ 1 := by
    intro h1
    have h2 := Nat.le_of_dvd hK (hζ.dvd_of_pow_eq_one K h1)
    omega
  obtain ⟨κ, hκ⟩ : ∃ κ : ℤ, (κ : ℂ) * gs5 (ζ ^ K) = t5 := by
    rcases gs5_eq hη5 hη1 with h | h
    · exact ⟨1, by rw [h]; simp⟩
    · exact ⟨-1, by rw [h]; simp⟩
  obtain ⟨τ, hτev⟩ : ∃ τ : ℤ[X], ∀ z : ℂ, aeval z τ = (κ : ℂ) * gs5 (z ^ K) := by
    refine ⟨(κ : ℤ[X]) * (X ^ K - X ^ (2 * K) - X ^ (3 * K) + X ^ (4 * K)), fun z => ?_⟩
    simp only [map_mul, map_sub, map_add, map_pow, aeval_X, map_intCast, gs5]
    ring
  have hex : ∀ r ∈ S, ∃ k : ℕ, ζ ^ k = r := fun r hr => by
    obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (hSK r hr)
    exact ⟨k, hk⟩
  choose! kf hkf using hex
  obtain ⟨b, -, hb⟩ := hζ.eq_pow_of_pow_eq_one hξK
  let F : ℤ[X] := (∏ r ∈ S, (τ - X ^ kf r) ^ p r) * τ ^ A * (c₁ : ℤ[X]) -
    X ^ b * (∏ r ∈ S, (τ - X ^ kf r) ^ n r) * τ ^ B * (c₂ : ℤ[X])
  have hev : ∀ z : ℂ, aeval z F =
      (∏ r ∈ S, ((κ : ℂ) * gs5 (z ^ K) - z ^ kf r) ^ p r) * ((κ : ℂ) * gs5 (z ^ K)) ^ A *
          (c₁ : ℂ) -
        z ^ b * (∏ r ∈ S, ((κ : ℂ) * gs5 (z ^ K) - z ^ kf r) ^ n r) *
          ((κ : ℂ) * gs5 (z ^ K)) ^ B * (c₂ : ℂ) :=
    fun z => by
      simp only [F, map_sub, map_mul, map_prod, map_pow, aeval_X, map_natCast, hτev]
  have h0 : aeval ζ F = 0 := by
    rw [hev, hκ, sub_eq_zero]
    have e : ∀ q : ℂ → ℕ, ∏ r ∈ S, (t5 - ζ ^ kf r) ^ q r = ∏ r ∈ S, (t5 - r) ^ q r :=
      fun q => Finset.prod_congr rfl fun r hr => by rw [hkf r hr]
    rw [e, e, hb]
    exact h
  have h1 := aeval_pow_of_coprime hN0 hζ h0 ha
  have hI : (κ : ℂ) * gs5 ((ζ ^ a) ^ K) = (leg5 a : ℂ) * t5 := by
    rw [← pow_mul, mul_comm a K, pow_mul, gs5_pow hη5, ← hκ]
    ring
  rw [hev, hI, sub_eq_zero] at h1
  have e : ∀ q : ℂ → ℕ,
      ∏ r ∈ S, ((leg5 a : ℂ) * t5 - (ζ ^ a) ^ kf r) ^ q r =
        ∏ r ∈ S, ((leg5 a : ℂ) * t5 - r ^ a) ^ q r :=
    fun q => Finset.prod_congr rfl fun r hr => by
      rw [← pow_mul, mul_comm a (kf r), pow_mul, hkf r hr]
  rw [e, e, ← pow_mul, mul_comm a b, pow_mul, hb] at h1
  exact h1

/-! ## 3. Sums of `log |1 - r/t|` over a coset of roots of unity -/

theorem one_sub_div_t5_ne_zero {w : ℂ} (hw : ‖w‖ = 1) : 1 - w / t5 ≠ 0 := by
  rw [w5_eq]
  exact div_ne_zero (t5_sub_ne_zero hw) t5_ne_zero

theorem one_sub_div_t5_pow_ne_zero {w : ℂ} (hw : ‖w‖ = 1) {M : ℕ} (hM : 0 < M) :
    1 - w / t5 ^ M ≠ 0 := by
  intro h
  have h1 : w / t5 ^ M = 1 := (sub_eq_zero.1 h).symm
  have h2 := congrArg norm h1
  have h3 : 1 < ‖t5‖ ^ M := one_lt_pow₀ one_lt_norm_t5 hM.ne'
  rw [norm_div, hw, norm_pow, norm_one, div_eq_one_iff_eq (by linarith)] at h2
  linarith

theorem log_norm_ofReal (x : ℝ) : Real.log ‖(x : ℂ)‖ = Real.log x := by
  rw [Complex.norm_real, Real.norm_eq_abs, Real.log_abs]

/-- **A full coset.** `∑_{c < L} log |1 - u^c y / t|` is `L/M` times `log |1 - y^M / t^M|`,
`M` the order of `u`: the `u^c y` are the roots of `X^M = y^M`, each `L/M` times. -/
theorem sum_log_coset5 {u y : ℂ} {L : ℕ} (hL : 0 < L) (hu : u ^ L = 1) (hy : ‖y‖ = 1) :
    ∑ c ∈ Finset.range L, Real.log ‖1 - u ^ c * y / t5‖ =
      (L / orderOf u) • Real.log ‖1 - y ^ orderOf u / t5 ^ orderOf u‖ := by
  have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.2 ⟨L, hL, hu⟩
  have hM0 : 0 < orderOf u := hfin.orderOf_pos
  have hprim : IsPrimitiveRoot u (orderOf u) := IsPrimitiveRoot.orderOf u
  obtain ⟨k, rfl⟩ : orderOf u ∣ L := orderOf_dvd_of_pow_eq_one hu
  have hun : ‖u‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hu hL.ne'
  have hn1 : ∀ c : ℕ, ‖u ^ c * y‖ = 1 := fun c => by
    rw [norm_mul, norm_pow, hun, one_pow, one_mul, hy]
  have hone : ∑ c ∈ Finset.range (orderOf u), Real.log ‖1 - u ^ c * y / t5‖ =
      Real.log ‖1 - y ^ orderOf u / t5 ^ orderOf u‖ := by
    have h1 := Base3.prod_sub_nthRoots hM0 (y ^ orderOf u) t5
    rw [hprim.nthRoots_eq rfl, Multiset.map_map] at h1
    have h2 : ∏ c ∈ Finset.range (orderOf u), (t5 - u ^ c * y) =
        t5 ^ orderOf u - y ^ orderOf u := by
      rw [← h1, Finset.prod_eq_multiset_prod, Finset.range_val]
      rfl
    have h3 : ∏ c ∈ Finset.range (orderOf u), (1 - u ^ c * y / t5) =
        1 - y ^ orderOf u / t5 ^ orderOf u := by
      have e : ∀ c ∈ Finset.range (orderOf u),
          1 - u ^ c * y / t5 = (t5 - u ^ c * y) / t5 := fun c _ => w5_eq _
      rw [Finset.prod_congr rfl e, Finset.prod_div_distrib, Finset.prod_const,
        Finset.card_range, h2, sub_div, div_self (pow_ne_zero _ t5_ne_zero)]
    rw [← h3, norm_prod, Real.log_prod]
    intro c _
    exact norm_ne_zero_iff.2 (one_sub_div_t5_ne_zero (hn1 c))
  have hper : ∀ j c : ℕ, u ^ (orderOf u * j + c) = u ^ c := fun j c => by
    rw [pow_add, pow_mul, pow_orderOf_eq_one, one_pow, one_mul]
  have hsum : ∀ j : ℕ, ∑ c ∈ Finset.range (orderOf u * j), Real.log ‖1 - u ^ c * y / t5‖ =
      j • Real.log ‖1 - y ^ orderOf u / t5 ^ orderOf u‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul, ← hone]
      congr 1
      exact Finset.sum_congr rfl fun c _ => by rw [hper]
  rw [hsum, Nat.mul_div_cancel_left k hM0]

/-! ## 4. The four-term products -/

/-- Even exponent: the product over the four classes is `(1 - 1/T)^4` or
`(1 - T^(-5))/(1 - 1/T)`, with `T = t^M = 5^(M/2)`. -/
theorem prod_even_mem {M : ℕ} (hM : 0 < M) (he : Even M) {v : ℂ} (hv : v ^ 5 = 1) :
    Real.log ‖(1 - v / t5 ^ M) * (1 - v ^ 2 / t5 ^ M) * (1 - v ^ 3 / t5 ^ M) *
      (1 - v ^ 4 / t5 ^ M)‖ ∈ baseSpan5 := by
  obtain ⟨m, rfl⟩ := he
  have hm : 0 < m := by omega
  have hT : t5 ^ (m + m) = (((5 : ℝ) ^ m : ℝ) : ℂ) := by
    rw [← two_mul, pow_mul, t5_sq]
    push_cast
    rfl
  have h1lt : (1 : ℝ) < 5 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
  have h5pos : (0 : ℝ) < 5 ^ m := by positivity
  rw [hT]
  by_cases h1 : v = 1
  · have e : (1 - v / (((5 : ℝ) ^ m : ℝ) : ℂ)) * (1 - v ^ 2 / (((5 : ℝ) ^ m : ℝ) : ℂ)) *
        (1 - v ^ 3 / (((5 : ℝ) ^ m : ℝ) : ℂ)) * (1 - v ^ 4 / (((5 : ℝ) ^ m : ℝ) : ℂ)) =
          (((1 - 1 / (5 : ℝ) ^ m) ^ 4 : ℝ) : ℂ) := by
      rw [h1]
      push_cast
      ring
    rw [e, log_norm_ofReal, Real.log_pow]
    exact_mod_cast rat_mul_mem_baseSpan5 (log_one_sub_mem_baseSpan5 hm) 4
  · have h4 := four_factors_plain hv h1 (((1 / (5 : ℝ) ^ m : ℝ)) : ℂ)
    have e : (1 - v / (((5 : ℝ) ^ m : ℝ) : ℂ)) * (1 - v ^ 2 / (((5 : ℝ) ^ m : ℝ) : ℂ)) *
        (1 - v ^ 3 / (((5 : ℝ) ^ m : ℝ) : ℂ)) * (1 - v ^ 4 / (((5 : ℝ) ^ m : ℝ) : ℂ)) =
          ((1 + 1 / (5 : ℝ) ^ m + (1 / (5 : ℝ) ^ m) ^ 2 + (1 / (5 : ℝ) ^ m) ^ 3 +
            (1 / (5 : ℝ) ^ m) ^ 4 : ℝ) : ℂ) := by
      push_cast
      push_cast at h4
      rw [← h4]
      ring
    have hY : (1 + 1 / (5 : ℝ) ^ m + (1 / (5 : ℝ) ^ m) ^ 2 + (1 / (5 : ℝ) ^ m) ^ 3 +
        (1 / (5 : ℝ) ^ m) ^ 4) * (1 - 1 / (5 : ℝ) ^ m) = 1 - 1 / (5 : ℝ) ^ (5 * m) := by
      rw [show (5 : ℝ) ^ (5 * m) = ((5 : ℝ) ^ m) ^ 5 by rw [← pow_mul, mul_comm]]
      field_simp
      ring
    have hpos : (0 : ℝ) < 1 + 1 / (5 : ℝ) ^ m + (1 / (5 : ℝ) ^ m) ^ 2 +
        (1 / (5 : ℝ) ^ m) ^ 3 + (1 / (5 : ℝ) ^ m) ^ 4 := by positivity
    have h1Y : (0 : ℝ) < 1 - 1 / (5 : ℝ) ^ m := by
      rw [sub_pos, div_lt_one h5pos]
      exact h1lt
    have hlog : Real.log (1 + 1 / (5 : ℝ) ^ m + (1 / (5 : ℝ) ^ m) ^ 2 +
        (1 / (5 : ℝ) ^ m) ^ 3 + (1 / (5 : ℝ) ^ m) ^ 4) =
          Real.log (1 - 1 / (5 : ℝ) ^ (5 * m)) - Real.log (1 - 1 / (5 : ℝ) ^ m) := by
      rw [← hY, Real.log_mul hpos.ne' h1Y.ne']
      ring
    rw [e, log_norm_ofReal, hlog]
    exact sub_mem (log_one_sub_mem_baseSpan5 (by omega)) (log_one_sub_mem_baseSpan5 hm)

/-- `1 - √5/T + 3/T² - √5/T³ + 1/T⁴ = L_M/5^(2M)` for `T = (√5)^M`, `M` odd. -/
theorem aur_value_L {M : ℕ} (hM : Odd M) :
    1 - t5 * (1 / t5 ^ M) + 3 * (1 / t5 ^ M) ^ 2 - t5 * (1 / t5 ^ M) ^ 3 + (1 / t5 ^ M) ^ 4 =
      (((L5 M : ℝ) / 5 ^ (2 * M) : ℝ) : ℂ) := by
  have hT : t5 ^ M ≠ 0 := pow_ne_zero _ t5_ne_zero
  push_cast
  rw [L5_cast hM, ← t5_pow_four]
  field_simp

/-- `1 + √5/T + 3/T² + √5/T³ + 1/T⁴ = M_M/5^(2M)` for `T = (√5)^M`, `M` odd. -/
theorem aur_value_M {M : ℕ} (hM : Odd M) :
    1 + t5 * (1 / t5 ^ M) + 3 * (1 / t5 ^ M) ^ 2 + t5 * (1 / t5 ^ M) ^ 3 + (1 / t5 ^ M) ^ 4 =
      (((M5 M : ℝ) / 5 ^ (2 * M) : ℝ) : ℂ) := by
  have hT : t5 ^ M ≠ 0 := pow_ne_zero _ t5_ne_zero
  push_cast
  rw [M5_cast hM, ← t5_pow_four]
  field_simp

/-- Odd exponent: the product over the four classes is `(1 - 1/T²)²`, `L_M/5^(2M)` or
`M_M/5^(2M)`, with `T = t^M`. -/
theorem prod_odd_mem {M : ℕ} (hM : Odd M) {v : ℂ} (hv : v ^ 5 = 1) {δ : ℂ}
    (hδ : δ = 1 ∨ δ = -1) :
    Real.log ‖(1 - δ * v / t5 ^ M) * (1 - -δ * v ^ 2 / t5 ^ M) * (1 - -δ * v ^ 3 / t5 ^ M) *
      (1 - δ * v ^ 4 / t5 ^ M)‖ ∈ baseSpan5 := by
  have hpos : 0 < M := hM.pos
  have hT : t5 ^ M ≠ 0 := pow_ne_zero _ t5_ne_zero
  by_cases h1 : v = 1
  · have hT2 : (5 : ℂ) ^ M = (t5 ^ M) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, t5_sq]
    have e : (1 - δ * v / t5 ^ M) * (1 - -δ * v ^ 2 / t5 ^ M) * (1 - -δ * v ^ 3 / t5 ^ M) *
        (1 - δ * v ^ 4 / t5 ^ M) = (((1 - 1 / (5 : ℝ) ^ M) ^ 2 : ℝ) : ℂ) := by
      rw [h1]
      push_cast
      rw [hT2]
      rcases hδ with rfl | rfl <;> field_simp <;> ring
    rw [e, log_norm_ofReal, Real.log_pow]
    exact_mod_cast rat_mul_mem_baseSpan5 (log_one_sub_mem_baseSpan5 hpos) 2
  · have h4 := four_factors hv h1 (δ / t5 ^ M)
    have e0 : (1 - δ * v / t5 ^ M) * (1 - -δ * v ^ 2 / t5 ^ M) * (1 - -δ * v ^ 3 / t5 ^ M) *
        (1 - δ * v ^ 4 / t5 ^ M) =
          1 - gs5 v * (δ / t5 ^ M) + 3 * (δ / t5 ^ M) ^ 2 - gs5 v * (δ / t5 ^ M) ^ 3 +
            (δ / t5 ^ M) ^ 4 := by
      rw [← h4]
      ring
    rw [e0]
    have hL := aur_value_L hM
    have hMv := aur_value_M hM
    rcases hδ with rfl | rfl <;> rcases gs5_eq hv h1 with hg | hg
    · have e : 1 - gs5 v * (1 / t5 ^ M) + 3 * (1 / t5 ^ M) ^ 2 - gs5 v * (1 / t5 ^ M) ^ 3 +
          (1 / t5 ^ M) ^ 4 = (((L5 M : ℝ) / 5 ^ (2 * M) : ℝ) : ℂ) := by
        rw [← hL, hg]
      rw [e, log_norm_ofReal]
      exact log_L5_mem_baseSpan5 hM
    · have e : 1 - gs5 v * (1 / t5 ^ M) + 3 * (1 / t5 ^ M) ^ 2 - gs5 v * (1 / t5 ^ M) ^ 3 +
          (1 / t5 ^ M) ^ 4 = (((M5 M : ℝ) / 5 ^ (2 * M) : ℝ) : ℂ) := by
        rw [← hMv, hg]
        ring
      rw [e, log_norm_ofReal]
      exact log_M5_mem_baseSpan5 hM
    · have e : 1 - gs5 v * (-1 / t5 ^ M) + 3 * (-1 / t5 ^ M) ^ 2 -
          gs5 v * (-1 / t5 ^ M) ^ 3 + (-1 / t5 ^ M) ^ 4 =
            (((M5 M : ℝ) / 5 ^ (2 * M) : ℝ) : ℂ) := by
        rw [← hMv, hg]
        ring
      rw [e, log_norm_ofReal]
      exact log_M5_mem_baseSpan5 hM
    · have e : 1 - gs5 v * (-1 / t5 ^ M) + 3 * (-1 / t5 ^ M) ^ 2 -
          gs5 v * (-1 / t5 ^ M) ^ 3 + (-1 / t5 ^ M) ^ 4 =
            (((L5 M : ℝ) / 5 ^ (2 * M) : ℝ) : ℂ) := by
        rw [← hL, hg]
        ring
      rw [e, log_norm_ofReal]
      exact log_L5_mem_baseSpan5 hM

/-- **The four classes together.** For `s^M` a fifth root of unity and `δ = ±1`, the sum over
`ρ = 1, 2, 3, 4` of `log |1 - (δ (ρ/5) s^ρ)^M / t^M|` is in the span. -/
theorem four_terms_mem {M : ℕ} (hM : 0 < M) {s : ℂ} (hs : (s ^ M) ^ 5 = 1) {δ : ℂ}
    (hδ : δ = 1 ∨ δ = -1) :
    Real.log ‖1 - (δ * (leg5 1 : ℂ) * s ^ 1) ^ M / t5 ^ M‖ +
      Real.log ‖1 - (δ * (leg5 2 : ℂ) * s ^ 2) ^ M / t5 ^ M‖ +
      Real.log ‖1 - (δ * (leg5 3 : ℂ) * s ^ 3) ^ M / t5 ^ M‖ +
      Real.log ‖1 - (δ * (leg5 4 : ℂ) * s ^ 4) ^ M / t5 ^ M‖ ∈ baseSpan5 := by
  have hvn : ‖s ^ M‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hs (by norm_num)
  have hδn : ‖δ‖ = 1 := by rcases hδ with rfl | rfl <;> simp
  have l1 : ((leg5 1 : ℤ) : ℂ) = 1 := by norm_num [leg5]
  have l2 : ((leg5 2 : ℤ) : ℂ) = -1 := by norm_num [leg5]
  have l3 : ((leg5 3 : ℤ) : ℂ) = -1 := by norm_num [leg5]
  have l4 : ((leg5 4 : ℤ) : ℂ) = 1 := by norm_num [leg5]
  have e1 : (δ * 1 * s ^ 1) ^ M = δ ^ M * s ^ M := by ring
  have e2 : (δ * -1 * s ^ 2) ^ M = (-δ) ^ M * (s ^ M) ^ 2 := by ring
  have e3 : (δ * -1 * s ^ 3) ^ M = (-δ) ^ M * (s ^ M) ^ 3 := by ring
  have e4 : (δ * 1 * s ^ 4) ^ M = δ ^ M * (s ^ M) ^ 4 := by ring
  rw [l1, l2, l3, l4, e1, e2, e3, e4]
  have n1 : ‖δ ^ M * s ^ M‖ = 1 := by rw [norm_mul, norm_pow, hδn, one_pow, one_mul, hvn]
  have n2 : ‖(-δ) ^ M * (s ^ M) ^ 2‖ = 1 := by
    rw [norm_mul, norm_pow, norm_neg, hδn, one_pow, one_mul, norm_pow, hvn, one_pow]
  have n3 : ‖(-δ) ^ M * (s ^ M) ^ 3‖ = 1 := by
    rw [norm_mul, norm_pow, norm_neg, hδn, one_pow, one_mul, norm_pow, hvn, one_pow]
  have n4 : ‖δ ^ M * (s ^ M) ^ 4‖ = 1 := by
    rw [norm_mul, norm_pow, hδn, one_pow, one_mul, norm_pow, hvn, one_pow]
  have z1 := norm_ne_zero_iff.2 (one_sub_div_t5_pow_ne_zero n1 hM)
  have z2 := norm_ne_zero_iff.2 (one_sub_div_t5_pow_ne_zero n2 hM)
  have z3 := norm_ne_zero_iff.2 (one_sub_div_t5_pow_ne_zero n3 hM)
  have z4 := norm_ne_zero_iff.2 (one_sub_div_t5_pow_ne_zero n4 hM)
  rw [← Real.log_mul z1 z2, ← Real.log_mul (mul_ne_zero z1 z2) z3,
    ← Real.log_mul (mul_ne_zero (mul_ne_zero z1 z2) z3) z4, ← norm_mul, ← norm_mul, ← norm_mul]
  rcases Nat.even_or_odd M with he | ho
  · have hδM : δ ^ M = 1 := by
      rcases hδ with rfl | rfl
      · exact one_pow _
      · exact he.neg_one_pow
    have hδM' : (-δ) ^ M = 1 := by rw [he.neg_pow, hδM]
    rw [hδM, hδM', one_mul, one_mul, one_mul, one_mul]
    exact prod_even_mem hM he hs
  · have hδM : δ ^ M = δ := by
      rcases hδ with rfl | rfl
      · exact one_pow _
      · exact ho.neg_one_pow
    have hδM' : (-δ) ^ M = -δ := by rw [ho.neg_pow, hδM]
    rw [hδM, hδM']
    exact prod_odd_mem ho hs hδ

/-! ## 5. The orbit of a root of unity -/

/-- **All exponents below `5K`.** `∑_{b < 5K} log |1 - δ (b/5) s^b / t|` is in the span, when
`s^(5K) = 1` and `δ = ±1`. (The terms with `5 ∣ b` are zero.) -/
theorem sum_log_five_mem {s : ℂ} {K : ℕ} (hK : 0 < K) (hs : s ^ (5 * K) = 1) {δ : ℂ}
    (hδ : δ = 1 ∨ δ = -1) :
    ∑ b ∈ Finset.range (5 * K), Real.log ‖1 - δ * (leg5 b : ℂ) * s ^ b / t5‖ ∈ baseSpan5 := by
  have hsn : ‖s‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hs (by omega)
  have hδn : ‖δ‖ = 1 := by rcases hδ with rfl | rfl <;> simp
  have huK : (s ^ 5) ^ K = 1 := by
    rw [← pow_mul]
    exact hs
  have hM0 : 0 < orderOf (s ^ 5) :=
    (isOfFinOrder_iff_pow_eq_one.2 ⟨K, hK, huK⟩).orderOf_pos
  -- one class modulo 5
  have hclass : ∀ ρ < 5,
      ∑ b ∈ (Finset.range (5 * K)).filter (fun b => b % 5 = ρ),
        Real.log ‖1 - δ * (leg5 b : ℂ) * s ^ b / t5‖ =
      ∑ c ∈ Finset.range K, Real.log ‖1 - (s ^ 5) ^ c * (δ * (leg5 ρ : ℂ) * s ^ ρ) / t5‖ := by
    intro ρ hρ
    refine Finset.sum_nbij' (fun b => b / 5) (fun c => 5 * c + ρ) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
      omega
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_range] at hc ⊢
      omega
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      omega
    · intro c _
      omega
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      have hsb : s ^ b = (s ^ 5) ^ (b / 5) * s ^ ρ := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      have hl : leg5 b = leg5 ρ := by rw [← leg5_mod b, hb.2]
      have e : δ * (leg5 ρ : ℂ) * ((s ^ 5) ^ (b / 5) * s ^ ρ) =
          (s ^ 5) ^ (b / 5) * (δ * (leg5 ρ : ℂ) * s ^ ρ) := by ring
      rw [hsb, hl, e]
  -- the class of 0 contributes nothing; each of the others is a full coset
  have h0 : ∑ c ∈ Finset.range K,
      Real.log ‖1 - (s ^ 5) ^ c * (δ * (leg5 0 : ℂ) * s ^ 0) / t5‖ = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    simp [leg5]
  have hcos : ∀ ρ : ℕ, ρ % 5 ≠ 0 →
      ∑ c ∈ Finset.range K, Real.log ‖1 - (s ^ 5) ^ c * (δ * (leg5 ρ : ℂ) * s ^ ρ) / t5‖ =
        (K / orderOf (s ^ 5)) • Real.log ‖1 - (δ * (leg5 ρ : ℂ) * s ^ ρ) ^ orderOf (s ^ 5) /
          t5 ^ orderOf (s ^ 5)‖ := by
    intro ρ hρ
    refine sum_log_coset5 hK huK ?_
    have hl : ‖((leg5 ρ : ℤ) : ℂ)‖ = 1 := by
      rcases leg5_eq_or hρ with h | h <;> rw [h] <;> simp
    rw [norm_mul, norm_mul, hδn, hl, norm_pow, hsn, one_pow, one_mul, one_mul]
  have hsplit := Finset.sum_fiberwise_of_maps_to (s := Finset.range (5 * K))
    (t := Finset.range 5) (g := fun b => b % 5)
    (fun b _ => Finset.mem_range.2 (Nat.mod_lt b (by norm_num)))
    (fun b => Real.log ‖1 - δ * (leg5 b : ℂ) * s ^ b / t5‖)
  rw [← hsplit, Finset.sum_congr rfl fun ρ hρ => hclass ρ (Finset.mem_range.1 hρ)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one, h0, zero_add, hcos 1 (by norm_num),
    hcos 2 (by norm_num), hcos 3 (by norm_num), hcos 4 (by norm_num), ← nsmul_add,
    ← nsmul_add, ← nsmul_add]
  refine nsmul_mem (four_terms_mem hM0 ?_ hδ) _
  rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one]

/-- **The orbit of a root of unity.** `∑ log |1 - (a/5) r^a / t|` over the `a < 5K` prime to
`5K` is in the span, when `r^(5K) = 1`. -/
theorem sum_log_coprime_mem5 {r : ℂ} {K : ℕ} (hK : 0 < K) (hr : r ^ (5 * K) = 1) :
    ∑ a ∈ (Finset.range (5 * K)).filter (fun a => a.Coprime (5 * K)),
      Real.log ‖1 - (leg5 a : ℂ) * r ^ a / t5‖ ∈ baseSpan5 := by
  have hN : 0 < 5 * K := by omega
  rw [sum_filter_coprime hN]
  refine Submodule.sum_mem _ fun d hd => zsmul_mem ?_ _
  have hdN : d ∣ 5 * K := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  by_cases h5 : 5 ∣ d
  · -- every multiple of `d` is a multiple of 5, and its term is zero
    have hz : ∀ a ∈ (Finset.range (5 * K)).filter (fun a => d ∣ a),
        Real.log ‖1 - (leg5 a : ℂ) * r ^ a / t5‖ = 0 := by
      intro a ha
      rw [leg5_of_dvd (h5.trans (Finset.mem_filter.1 ha).2)]
      simp
    rw [Finset.sum_eq_zero hz]
    exact zero_mem _
  · have hcop : Nat.Coprime d 5 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5).symm
    obtain ⟨K', rfl⟩ : d ∣ K := hcop.dvd_of_dvd_mul_left hdN
    have hK' : 0 < K' := Nat.pos_of_mul_pos_left hK
    have hd5 : d % 5 ≠ 0 := fun h => h5 (Nat.dvd_of_mod_eq_zero h)
    have e : ∑ a ∈ (Finset.range (5 * (d * K'))).filter (fun a => d ∣ a),
          Real.log ‖1 - (leg5 a : ℂ) * r ^ a / t5‖ =
        ∑ b ∈ Finset.range (5 * K'),
          Real.log ‖1 - (leg5 d : ℂ) * (leg5 b : ℂ) * (r ^ d) ^ b / t5‖ := by
      refine Finset.sum_nbij' (fun a => a / d) (fun b => d * b) ?_ ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
        obtain ⟨ha1, b, rfl⟩ := ha
        rw [Nat.mul_div_cancel_left b hd0]
        have h4 : d * b < d * (5 * K') := by
          rw [show d * (5 * K') = 5 * (d * K') by ring]
          exact ha1
        exact Nat.lt_of_mul_lt_mul_left h4
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
        refine ⟨?_, Dvd.intro b rfl⟩
        rw [show 5 * (d * K') = d * (5 * K') by ring]
        exact Nat.mul_lt_mul_of_pos_left hb hd0
      · intro a ha
        simp only [Finset.mem_filter] at ha
        exact Nat.mul_div_cancel' ha.2
      · intro b _
        exact Nat.mul_div_cancel_left b hd0
      · intro a ha
        simp only [Finset.mem_filter] at ha
        obtain ⟨b, rfl⟩ := ha.2
        rw [Nat.mul_div_cancel_left b hd0, leg5_mul, ← pow_mul]
        push_cast
        rfl
    rw [e]
    refine sum_log_five_mem hK' ?_ ?_
    · rw [← pow_mul, show d * (5 * K') = 5 * (d * K') by ring]
      exact hr
    · rcases leg5_eq_or hd5 with h | h <;> rw [h] <;> simp

/-! ## 6. From a cleared relation to the span -/

/-- **The key lemma in base 5.** From an identity
`∏ (t - r)^(p_r) · t^A · c₁ = ξ · ∏ (t - r)^(n_r) · t^B · c₂` of degree 0 in `t` (`hdeg`),
between roots of unity `r`, `ξ` and positive integers `c₁`, `c₂`, the number
`log c₁ - log c₂` is in `baseSpan5`. -/
theorem log_sub_mem_baseSpan5_of_cleared {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {ξ : ℂ} (hξ : IsOfFinOrder ξ) (p n : ℂ → ℕ) (A B : ℕ) {c₁ c₂ : ℕ} (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂) (hdeg : ∑ r ∈ S, p r + A = ∑ r ∈ S, n r + B)
    (h : (∏ r ∈ S, (t5 - r) ^ p r) * t5 ^ A * (c₁ : ℂ) =
      ξ * (∏ r ∈ S, (t5 - r) ^ n r) * t5 ^ B * (c₂ : ℂ)) :
    Real.log c₁ - Real.log c₂ ∈ baseSpan5 := by
  classical
  set K := (∏ r ∈ S, orderOf r) * orderOf ξ with hKdef
  have hK : 0 < K :=
    Nat.mul_pos (Finset.prod_pos fun r hr => (hS r hr).orderOf_pos) hξ.orderOf_pos
  have hSK : ∀ r ∈ S, r ^ (5 * K) = 1 := fun r hr =>
    orderOf_dvd_iff_pow_eq_one.1
      (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hr) _) 5)
  have hξK : ξ ^ (5 * K) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Dvd.dvd.mul_left (Dvd.intro_left _ rfl) 5)
  have hξn : ‖ξ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hξK (by omega)
  set G := (Finset.range (5 * K)).filter (fun a => a.Coprime (5 * K)) with hG
  have h1G : 1 ∈ G := by
    rw [hG, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.coprime_one_left _⟩
  have hT : 0 < ‖t5‖ := norm_pos_iff.2 t5_ne_zero
  have hdegR : ∑ r ∈ S, ((n r : ℝ) - p r) + ((B : ℝ) - A) = 0 := by
    have h0 : ((∑ r ∈ S, p r + A : ℕ) : ℝ) = ((∑ r ∈ S, n r + B : ℕ) : ℝ) := by rw [hdeg]
    push_cast at h0
    rw [Finset.sum_sub_distrib]
    linarith
  -- the identity for every conjugate, in logarithms
  have hlog : ∀ a ∈ G, Real.log c₁ - Real.log c₂ =
      ∑ r ∈ S, ((n r : ℝ) - p r) * Real.log ‖1 - (leg5 a : ℂ) * r ^ a / t5‖ := by
    intro a ha
    obtain ⟨-, hac⟩ := Finset.mem_filter.1 ha
    have ha5 : a % 5 ≠ 0 := by
      intro h5
      have h5' : 5 ∣ Nat.gcd a (5 * K) :=
        Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h5) (Dvd.intro K rfl)
      rw [Nat.Coprime] at hac
      rw [hac] at h5'
      omega
    have hε2 : ((leg5 a : ℤ) : ℂ) ^ 2 = 1 := by
      rcases leg5_eq_or ha5 with h | h <;> rw [h] <;> norm_num
    have hεn : ‖((leg5 a : ℤ) : ℂ)‖ = 1 := by
      rcases leg5_eq_or ha5 with h | h <;> rw [h] <;> simp
    have h2 := cleared_conj5 p n A B c₁ c₂ hK hSK hξK h hac
    have h3 := congrArg norm h2
    simp only [norm_mul, norm_pow, norm_prod, Complex.norm_natCast, hξn, hεn, one_pow,
      one_mul] at h3
    have hrn : ∀ r ∈ S, ‖(leg5 a : ℂ) * r ^ a‖ = 1 := fun r hr => by
      rw [norm_mul, hεn, one_mul, norm_pow,
        Complex.norm_eq_one_of_pow_eq_one (hSK r hr) (by omega), one_pow]
    have hfac : ∀ r ∈ S, (leg5 a : ℂ) * t5 - r ^ a =
        (leg5 a : ℂ) * t5 * (1 - (leg5 a : ℂ) * r ^ a / t5) := by
      intro r _
      have e : (leg5 a : ℂ) * t5 * ((leg5 a : ℂ) * r ^ a / t5) =
          (leg5 a : ℂ) ^ 2 * r ^ a := by
        field_simp [t5_ne_zero]
      rw [mul_sub, mul_one, e, hε2, one_mul]
    have hnorm : ∀ r ∈ S, ‖(leg5 a : ℂ) * t5 - r ^ a‖ =
        ‖t5‖ * ‖1 - (leg5 a : ℂ) * r ^ a / t5‖ := by
      intro r hr
      rw [hfac r hr, norm_mul, norm_mul, hεn, one_mul]
    have hw : ∀ r ∈ S, 0 < ‖1 - (leg5 a : ℂ) * r ^ a / t5‖ := fun r hr =>
      norm_pos_iff.2 (one_sub_div_t5_ne_zero (hrn r hr))
    have h4 := log_identity_of_prod_eq (x := fun r => ‖(leg5 a : ℂ) * t5 - r ^ a‖)
      (fun r hr => by rw [hnorm r hr]; exact mul_pos hT (hw r hr)) hT p n A B
      (by exact_mod_cast hc₁) (by exact_mod_cast hc₂) h3
    have h5 : ∀ r ∈ S, ((n r : ℝ) - p r) * Real.log ‖(leg5 a : ℂ) * t5 - r ^ a‖ =
        ((n r : ℝ) - p r) * Real.log ‖t5‖ +
          ((n r : ℝ) - p r) * Real.log ‖1 - (leg5 a : ℂ) * r ^ a / t5‖ := by
      intro r hr
      rw [hnorm r hr, Real.log_mul hT.ne' (hw r hr).ne', mul_add]
    rw [h4, Finset.sum_congr rfl h5, Finset.sum_add_distrib, ← Finset.sum_mul]
    linear_combination Real.log ‖t5‖ * hdegR
  -- adding over the conjugates
  have hsum : (G.card : ℝ) * (Real.log c₁ - Real.log c₂) =
      ∑ r ∈ S, ((n r : ℝ) - p r) * ∑ a ∈ G, Real.log ‖1 - (leg5 a : ℂ) * r ^ a / t5‖ := by
    have h4 := Finset.sum_congr (rfl : G = G) hlog
    rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_comm] at h4
    rw [h4]
    simp only [Finset.mul_sum]
  have hmem : (G.card : ℝ) * (Real.log c₁ - Real.log c₂) ∈ baseSpan5 := by
    rw [hsum]
    refine Submodule.sum_mem _ fun r hr => ?_
    have h5 := rat_mul_mem_baseSpan5 (sum_log_coprime_mem5 hK (hSK r hr)) ((n r : ℚ) - p r)
    have e : (((n r : ℚ) - p r : ℚ) : ℝ) = (n r : ℝ) - p r := by push_cast; ring
    rw [e] at h5
    exact h5
  have hcard : (G.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨1, h1G⟩).ne'
  have h6 := rat_mul_mem_baseSpan5 hmem ((G.card : ℚ)⁻¹)
  have e : (((G.card : ℚ)⁻¹ : ℚ) : ℝ) * ((G.card : ℝ) * (Real.log c₁ - Real.log c₂)) =
      Real.log c₁ - Real.log c₂ := by
    push_cast
    field_simp
  rw [e] at h6
  exact h6

/-! ## 7. The criterion -/

/-- **Baker's theorem for the logarithm of a rational number.** If `log (a/b)` is the value of
a series of the class F5, then some multiplicative relation among the `1 - r/t` involves a
non-zero power of `a/b`. -/
theorem exists_rel5_of_isF5Value_log (hB : BakerTheorem) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : IsF5Value (Real.log ((a : ℝ) / b))) :
    ∃ S : Finset ℂ, (∀ r ∈ S, IsOfFinOrder r) ∧ ∃ (e : ℂ → ℤ) (m : ℤ),
      m ≠ 0 ∧ IsRel5 (a : ℂ) (b : ℂ) S e m := by
  classical
  by_contra hnot
  have hmul : ∀ S : Finset ℂ, (∀ r ∈ S, IsOfFinOrder r) → ∀ (e : ℂ → ℤ) (m : ℤ),
      IsRel5 (a : ℂ) (b : ℂ) S e m → m = 0 := by
    intro S hS e m hrel
    by_contra hm
    exact hnot ⟨S, hS, e, m, hm, hrel⟩
  obtain ⟨N, ρ, hN, hρ, hsum⟩ := h
  have hpos : (0 : ℝ) < (a : ℝ) / b := by positivity
  set Λ : ℂ := ((Real.log ((a : ℝ) / b) : ℝ) : ℂ) with hΛdef
  have hΛ : Complex.exp Λ = (a : ℂ) / b := by
    rw [hΛdef, ← Complex.ofReal_exp, Real.exp_log hpos]
    push_cast
    rfl
  have halg : IsAlgebraic ℚ ((a : ℂ) / b) := by
    have h0 := isAlgebraic_algebraMap (R := ℚ) (A := ℂ) ((a : ℚ) / b)
    simpa using h0
  -- the series as a combination of logarithms
  have hρ2 : ∀ k, ρ (k + 2 * N) = ρ k := fun k => by
    have h2 := periodic_mul hρ 2 k
    rwa [mul_comm] at h2
  have hN2 : 0 < 2 * N := by positivity
  have h1 := seriesTerm5_hasSum_logs hN2 (Dvd.intro N rfl) hρ2
  have h2 := h1.unique (Complex.hasSum_ofReal.2 hsum)
  have h3 : ∑ r ∈ rootsN (2 * N), fourierD5 (2 * N) ρ r * Complex.log (1 - r / t5) =
      (1 : ℂ) * Λ := by
    rw [h2, one_mul]
  have h4 := baker_no_extra5 hB hΛ halg hmul
    (fun r hr => isOfFinOrder_of_mem_rootsN hN2 hr)
    (fun r hr => isAlgebraic_fourierD5 (2 * N) ρ (isOfFinOrder_of_mem_rootsN hN2 hr))
    isAlgebraic_one h3
  exact one_ne_zero h4

/-- **The converse in base 5** (from Baker's theorem). If `log (a/b)` is the value of a series
of the class F5, then it is a rational combination of logarithms of base numbers. -/
theorem mem_baseSpan5_of_isF5Value_log (hB : BakerTheorem) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : IsF5Value (Real.log ((a : ℝ) / b))) : Real.log ((a : ℝ) / b) ∈ baseSpan5 := by
  classical
  obtain ⟨S, hS, e, m, hm, hrel⟩ := exists_rel5_of_isF5Value_log hB ha hb h
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  -- the relation, cleared and conjugated, puts `m log (a/b)` in the span
  obtain ⟨ξ, hξ, hcl⟩ := cleared5 haC hbC hS hrel
  have key := log_sub_mem_baseSpan5_of_cleared hS hξ (fun r => (e r).toNat)
    (fun r => (-e r).toNat) (∑ r ∈ S, (-e r).toNat) (∑ r ∈ S, (e r).toNat)
    (c₁ := a ^ (-m).toNat * b ^ m.toNat) (c₂ := a ^ m.toNat * b ^ (-m).toNat)
    (by positivity) (by positivity) (add_comm _ _) (by push_cast; exact hcl)
  have hu : ((m.toNat : ℕ) : ℝ) - (((-m).toNat : ℕ) : ℝ) = (m : ℝ) := by
    have h0 : ((m.toNat : ℕ) : ℤ) - (((-m).toNat : ℕ) : ℤ) = m := by omega
    exact_mod_cast h0
  have e1 : Real.log ((a ^ (-m).toNat * b ^ m.toNat : ℕ) : ℝ) -
      Real.log ((a ^ m.toNat * b ^ (-m).toNat : ℕ) : ℝ) =
        (-(m : ℝ)) * Real.log ((a : ℝ) / b) := by
    push_cast
    rw [Real.log_mul (pow_ne_zero _ haR) (pow_ne_zero _ hbR),
      Real.log_mul (pow_ne_zero _ haR) (pow_ne_zero _ hbR), Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_pow, Real.log_div haR hbR]
    linear_combination (Real.log b - Real.log a) * hu
  rw [e1] at key
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have h5 := rat_mul_mem_baseSpan5 key ((-(m : ℚ))⁻¹)
  have e2 : (((-(m : ℚ))⁻¹ : ℚ) : ℝ) * (-(m : ℝ) * Real.log ((a : ℝ) / b)) =
      Real.log ((a : ℝ) / b) := by
    push_cast
    field_simp
  rw [e2] at h5
  exact h5

/-- **The criterion in base 5, for a quotient of positive integers** (from Baker's theorem):
`log (a/b)` is the value of a series of the class F5 if and only if it is a rational
combination of logarithms of base numbers. -/
theorem isF5Value_log_iff (hB : BakerTheorem) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    IsF5Value (Real.log ((a : ℝ) / b)) ↔ Real.log ((a : ℝ) / b) ∈ baseSpan5 :=
  ⟨mem_baseSpan5_of_isF5Value_log hB ha hb, isF5Value_of_mem_baseSpan5⟩

theorem isF5Value_log_rat_iff (hB : BakerTheorem) {y : ℚ} (hy : 0 < y) :
    IsF5Value (Real.log (y : ℝ)) ↔ Real.log (y : ℝ) ∈ baseSpan5 := by
  have hnum : 0 < y.num := Rat.num_pos.2 hy
  have e : (y : ℝ) = ((y.num.toNat : ℕ) : ℝ) / ((y.den : ℕ) : ℝ) := by
    have h1 : ((y.num.toNat : ℕ) : ℤ) = y.num := Int.toNat_of_nonneg hnum.le
    have h2 : ((y.num.toNat : ℕ) : ℝ) = ((y.num : ℤ) : ℝ) := by exact_mod_cast h1
    rw [h2, Rat.cast_def]
  rw [e]
  exact isF5Value_log_iff hB (by omega) y.den_pos

/-- **The criterion for base 5 in elementary terms** (from Baker's theorem). For a positive
rational number `y`, `log y` is the value of a series `∑ ρ(k) 5^(-⌊k/2⌋)/k` with `ρ` rational
and periodic if and only if some power `y^k`, `k ≥ 1`, is a product of integer powers of the
numbers `(5^m - 1)/5^m` (`m ≥ 1`), `L_h/5^(2h)` and `M_h/5^(2h)` (`h` odd). -/
theorem isF5Value_log_rat_iff_pow (hB : BakerTheorem) {y : ℚ} (hy : 0 < y) :
    IsF5Value (Real.log (y : ℝ)) ↔
      ∃ k : ℕ, 0 < k ∧ ∃ (n : ℕ) (g : Fin n → ℚ) (e : Fin n → ℤ),
        (∀ i, g i ∈ baseNumbers5) ∧ y ^ k = ∏ i, g i ^ e i := by
  rw [isF5Value_log_rat_iff hB hy]
  exact log_mem_baseSpan5_iff_pow hy

end Base5

end PiFormula
