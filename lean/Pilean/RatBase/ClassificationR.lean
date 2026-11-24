module

public import Pilean.RatBase.SupportR
public import Pilean.RatBase.ClassificationRAux

/-!
# A rational base `p/q`: no algebraic multiple of `π` is a value, and no zero relation

`F_(p/q)` is the class of series `S(ρ) = ∑ ρ(k) (q/p)^⌊k/2⌋/k` with `ρ` rational and periodic,
for coprime integers `p > q ≥ 1`.

**Theorem** (`eq_zero_of_goodPrimesR`, from Baker's theorem and `GoodPrimesR p q`, for
`(p, q) ≠ (3, 1)`). If a series of the class `F_(p/q)` has value `γ π` with `γ` algebraic, then
all its coefficients are zero.

So, from the same hypotheses:

* a series of `F_(p/q)` has sum `0` only if its pattern is `0`
  (`hasSum_zero_iff_of_goodPrimesR`);
* a number has at most one formula of the class `F_(p/q)` (`eq_of_hasSum_of_goodPrimesR`);
* a non-zero algebraic multiple of `π` is not a value of `F_(p/q)`
  (`mul_pi_eq_zero_of_goodPrimesR`), and in particular `π` is not
  (`not_isFRValue_pi_of_goodPrimesR`).

The proof is that of `BaseB/Classification.lean`. Write `S(ρ) = ∑ d_r Log(1 - r x)`,
`x = √(q/p)` (`seriesTermRat_hasSum_logs`). By Baker's theorem the vector `(iγ; d_r)` is a
combination, with algebraic coefficients, of integer relations among `iπ` and the
`Log(1 - r x)` (`baker_descent`). But there is no integer relation other than zero
(`intRel_eq_zeroR`):

* its coefficient at a root `r` with `r⁴ ≠ 1` is zero (`support_subset_fourth_rootsR`);
* the real part of what is left is
  `z₁ log(1 - x) + z₋₁ log(1 + x) + (z_i + z₋ᵢ) log(1 + q/p)/2 = 0`, and these three logarithms
  are independent over `ℤ` (`log_indepR`);
* then `((1 - i x)/(1 + i x))^(2 z_i) = 1`, and `(1 - i x)/(1 + i x)` is not a root of unity
  (`unitR_zpow_eq_one`); this is the step that fails for `(p, q) = (3, 1)`;
* what is left is `z₀ iπ = 0`.

So every `d_r` is zero, and by Fourier inversion the pattern is zero.

The hypothesis `GoodPrimesR p q` fails for the five bases `2, 3, 4, 3/2, 4/3`, which have
relations; for `q = 1` the theorem is `BaseB.eq_zero_of_goodPrimesB`.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace RatBase

/-! ## 1. Integer relations -/

/-- The logarithms: `iπ` at `none`, and the `Log(1 - r x)`, `x = √(q/p)`. -/
noncomputable def lamOfR (p q : ℕ) : Option ℂ → ℂ
  | none => Real.pi * I
  | some r => Complex.log (1 - r * xRat p q)

theorem isAlgebraic_exp_log_wR {p q : ℕ} (hq : 0 < q) (hqp : q < p) {r : ℂ}
    (hr : IsOfFinOrder r) : IsAlgebraic ℚ (Complex.exp (Complex.log (1 - r * xRat p q))) := by
  rw [Complex.exp_log (wR_ne_zero hq hqp hr)]
  exact isAlgebraic_one.sub ((isAlgebraic_root hr).mul (isAlgebraic_xRat p q))

theorem isAlgebraic_exp_lamOfR {p q : ℕ} (hq : 0 < q) (hqp : q < p) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) :
    ∀ i ∈ Finset.insertNone S, IsAlgebraic ℚ (Complex.exp (lamOfR p q i)) := by
  intro i hi
  rcases i with _ | r
  · change IsAlgebraic ℚ (Complex.exp (Real.pi * I))
    rw [Complex.exp_pi_mul_I]
    exact isAlgebraic_one.neg
  · exact isAlgebraic_exp_log_wR hq hqp (hS r (Finset.some_mem_insertNone.1 hi))

/-- An integer relation among `iπ` and the `Log(1 - r x)` is a multiplicative relation. -/
theorem relationRat_of_intRel {p q : ℕ} (hq : 0 < q) (hqp : q < p) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {z : Option ℂ → ℤ}
    (hz : ∑ i ∈ Finset.insertNone S, (z i : ℂ) * lamOfR p q i = 0) :
    IsRelationRat p q S (fun r => z (some r)) := by
  rw [Finset.sum_insertNone] at hz
  have hz' : (z none : ℂ) * (Real.pi * I) +
      ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r * xRat p q) = 0 := hz
  have h1 : ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r * xRat p q) =
      -(z none : ℂ) * (Real.pi * I) := by linear_combination hz'
  have hexp : Complex.exp (∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r * xRat p q)) =
      ∏ r ∈ S, (1 - r * xRat p q) ^ (z (some r)) := by
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [Complex.exp_int_mul, Complex.exp_log (wR_ne_zero hq hqp (hS r hr))]
  refine ⟨Complex.exp (-(z none : ℂ) * (Real.pi * I)), ?_, ?_⟩
  · refine isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, ?_⟩
    rw [← Complex.exp_nat_mul]
    have e : ((2 : ℕ) : ℂ) * (-(z none : ℂ) * (Real.pi * I)) =
        ((-z none : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  · rw [← hexp, h1]

/-- **No integer relation** (from `GoodPrimesR p q`, for coprime `p > q ≥ 1` other than
`(3, 1)`). An integer relation among `iπ` and the `Log(1 - r x)`, `r` in a finite set of roots
of unity, is the zero vector. -/
theorem intRel_eq_zeroR {p q : ℕ} (hq : 0 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (h31 : ¬ (p = 3 ∧ q = 1)) (hG : GoodPrimesR p q) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {v : Option ℂ → ℂ}
    (hv : v ∈ IntRel (Finset.insertNone S) (lamOfR p q)) (i : Option ℂ) : v i = 0 := by
  classical
  obtain ⟨z, hz0, hzsum, hvz⟩ := hv
  -- the coefficients vanish outside `S`, and at every root with `r⁴ ≠ 1`
  have hout : ∀ r, r ∉ S → z (some r) = 0 := fun r hr =>
    hz0 (some r) (fun hmem => hr (Finset.some_mem_insertNone.1 hmem))
  have hsupp : ∀ r, r ^ 4 ≠ 1 → z (some r) = 0 := by
    intro r hr4
    by_cases hr : r ∈ S
    · exact support_subset_fourth_rootsR hq hqp hG hS (relationRat_of_intRel hq hqp hS hzsum)
        r hr hr4
    · exact hout r hr
  rw [Finset.sum_insertNone] at hzsum
  have hzsum' : (z none : ℂ) * (Real.pi * I) +
      ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r * xRat p q) = 0 := hzsum
  -- the sum over `S` reduces to the four roots `1, -1, i, -i`
  obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ,
      f = fun r => (z (some r) : ℂ) * Complex.log (1 - r * xRat p q) := ⟨_, rfl⟩
  have hsum : ∑ r ∈ S, f r = f 1 + f (-1) + f I + f (-I) := by
    have h1 : (1 : ℂ) ∉ ({-1, I, -I} : Finset ℂ) := by norm_num [Complex.ext_iff]
    have h2 : (-1 : ℂ) ∉ ({I, -I} : Finset ℂ) := by norm_num [Complex.ext_iff]
    have h3 : (I : ℂ) ≠ -I := by norm_num [Complex.ext_iff]
    have hA : ∑ r ∈ S, f r = ∑ r ∈ S ∪ {1, -1, I, -I}, f r :=
      Finset.sum_subset Finset.subset_union_left fun r _ hr => by
        rw [hf]
        simp only [hout r hr, Int.cast_zero, zero_mul]
    have hB : ∑ r ∈ ({1, -1, I, -I} : Finset ℂ), f r = ∑ r ∈ S ∪ {1, -1, I, -I}, f r :=
      Finset.sum_subset Finset.subset_union_right fun r _ hr => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
        rw [hf]
        simp only [hsupp r (BaseB.pow_four_ne_one hr.1 hr.2.1 hr.2.2.1 hr.2.2.2), Int.cast_zero,
          zero_mul]
    rw [hA, ← hB, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_pair h3]
    ring
  have hsum' : ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r * xRat p q) =
      (z (some 1) : ℂ) * Complex.log (1 - 1 * xRat p q) +
        (z (some (-1)) : ℂ) * Complex.log (1 - (-1) * xRat p q) +
        (z (some I) : ℂ) * Complex.log (1 - I * xRat p q) +
        (z (some (-I)) : ℂ) * Complex.log (1 - (-I) * xRat p q) := by
    have := hsum
    rw [hf] at this
    exact this
  rw [hsum'] at hzsum'
  -- real parts
  have hre := congrArg Complex.re hzsum'
  have e1 : ((z none : ℂ) * (Real.pi * I)).re = 0 := by simp
  simp only [Complex.add_re, e1, Base5.re_intCast_mul5, log_re_oneR hq hqp, log_re_neg_oneR,
    log_re_IR hq hqp, log_re_neg_IR hq hqp, Complex.zero_re, zero_add] at hre
  obtain ⟨h1, hn, hs⟩ := log_indepR hq hqp hcop (z₁ := z (some 1)) (z₂ := z (some (-1)))
    (s := z (some I) + z (some (-I))) (by rw [Int.cast_add]; linear_combination 2 * hre)
  have c1 : (z (some 1) : ℂ) = 0 := by rw [h1, Int.cast_zero]
  have cn : (z (some (-1)) : ℂ) = 0 := by rw [hn, Int.cast_zero]
  have hz4 : z (some (-I)) = -z (some I) := by omega
  have c4 : (z (some (-I)) : ℂ) = -(z (some I) : ℂ) := by rw [hz4, Int.cast_neg]
  -- `((1 - i x)/(1 + i x))^(2 z_i) = 1`
  have hnI : IsOfFinOrder (-I) := by
    rw [← Complex.inv_I]
    exact isOfFinOrder_inv' isOfFinOrder_I
  have hunit : ((1 - I * xRat p q) / (1 - (-I) * xRat p q)) ^ (2 * z (some I)) = 1 := by
    have e : ((2 * z (some I) : ℤ) : ℂ) *
        (Complex.log (1 - I * xRat p q) - Complex.log (1 - (-I) * xRat p q)) =
        ((-z none : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast
      linear_combination 2 * hzsum' - 2 * Complex.log (1 - (-I) * xRat p q) * c4 -
        2 * Complex.log (1 - 1 * xRat p q) * c1 - 2 * Complex.log (1 - (-1) * xRat p q) * cn
    have key := congrArg Complex.exp e
    rwa [Complex.exp_int_mul, Complex.exp_sub,
      Complex.exp_log (wR_ne_zero hq hqp isOfFinOrder_I),
      Complex.exp_log (wR_ne_zero hq hqp hnI), Complex.exp_int_mul_two_pi_mul_I] at key
  have h3 : z (some I) = 0 := by
    have := unitR_zpow_eq_one hq hqp hcop h31 hunit
    omega
  have h4 : z (some (-I)) = 0 := by omega
  have c3 : (z (some I) : ℂ) = 0 := by rw [h3, Int.cast_zero]
  have c4' : (z (some (-I)) : ℂ) = 0 := by rw [h4, Int.cast_zero]
  -- what is left is `z₀ iπ = 0`
  have hlast : (z none : ℂ) * (Real.pi * I) = 0 := by
    linear_combination hzsum' - Complex.log (1 - 1 * xRat p q) * c1 -
      Complex.log (1 - (-1) * xRat p q) * cn - Complex.log (1 - I * xRat p q) * c3 -
      Complex.log (1 - (-I) * xRat p q) * c4'
  have hpiI : (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have h0 : z none = 0 := by
    rcases mul_eq_zero.1 hlast with h0 | h0
    · exact_mod_cast h0
    · exact absurd h0 hpiI
  rw [hvz]
  rcases i with _ | r
  · rw [h0, Int.cast_zero]
  · by_cases hr1 : r = 1
    · rw [hr1, h1, Int.cast_zero]
    · by_cases hrn : r = -1
      · rw [hrn, hn, Int.cast_zero]
      · by_cases hrI : r = I
        · rw [hrI, h3, Int.cast_zero]
        · by_cases hrnI : r = -I
          · rw [hrnI, h4, Int.cast_zero]
          · rw [hsupp r (BaseB.pow_four_ne_one hr1 hrn hrI hrnI), Int.cast_zero]

/-! ## 2. Baker's theorem: the coefficients lie in the span of the integer relations -/

/-- For a series of value `γ π` (`γ` algebraic), the vector `(iγ; d_r)` is a combination, with
algebraic coefficients, of integer relations among `iπ` and the `Log(1 - r x)`. -/
theorem coeffs_spanInR (hB : BakerTheorem) {p q : ℕ} (hq : 0 < q) (hqp : q < p) {N : ℕ}
    (hN : 0 < N) (h2 : 2 ∣ N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ}
    (hγ : IsAlgebraic ℚ γ) (h : HasSum (seriesTermRat p q ρ) (γ * Real.pi)) :
    ∃ β : Option ℂ → ℂ, (∀ r ∈ rootsN N, β (some r) = fourierDRat p q N ρ r) ∧
      SpanIn (algebraicClosure ℚ ℂ) (IntRel (Finset.insertNone (rootsN N)) (lamOfR p q)) β := by
  classical
  have hS : ∀ r ∈ rootsN N, IsOfFinOrder r := fun r hr => isOfFinOrder_of_mem_rootsN hN hr
  have h1 := (seriesTermRat_hasSum_logs hq hqp hN h2 hρ).unique (Complex.hasSum_ofReal.2 h)
  have hγC : IsAlgebraic ℚ (γ : ℂ) := isAlgebraic_ofReal hγ
  let β : Option ℂ → ℂ := fun o =>
    match o with
    | none => I * γ
    | some r => if r ∈ rootsN N then fourierDRat p q N ρ r else 0
  have hβS : ∀ r ∈ rootsN N, β (some r) = fourierDRat p q N ρ r := fun r hr => by
    simp only [β, hr, ↓reduceIte]
  have hF : ∀ x ∈ algebraicClosure ℚ ℂ, IsAlgebraic ℚ x := fun x hx =>
    mem_algebraicClosure_iff.1 hx
  refine ⟨β, hβS, ?_⟩
  refine baker_descent hB _ hF (lamOfR p q) _ (isAlgebraic_exp_lamOfR hq hqp hS) β ?_ ?_ ?_
  · intro i hi
    rcases i with _ | r
    · exact mem_algebraicClosure_iff.2 (isAlgebraic_I.mul hγC)
    · have hr : r ∈ rootsN N := Finset.some_mem_insertNone.1 hi
      rw [hβS r hr]
      exact mem_algebraicClosure_iff.2 (isAlgebraic_fourierDRat p q N ρ (hS r hr))
  · intro i hi
    rcases i with _ | r
    · exact absurd (by simp) hi
    · have hr : r ∉ rootsN N := fun hr => hi (Finset.some_mem_insertNone.2 hr)
      simp only [β, hr, ↓reduceIte]
  · rw [Finset.sum_insertNone]
    have e2 : ∑ r ∈ rootsN N, β (some r) * lamOfR p q (some r) =
        ∑ r ∈ rootsN N, fourierDRat p q N ρ r * Complex.log (1 - r * xRat p q) :=
      Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
    rw [e2, h1]
    change I * γ * (Real.pi * I) + ((γ * Real.pi : ℝ) : ℂ) = 0
    push_cast
    linear_combination ((γ : ℂ) * Real.pi) * Complex.I_sq

/-! ## 3. The theorem -/

private theorem seriesTermRat_zero_pattern (p q : ℕ) : seriesTermRat p q 0 = fun _ => 0 := by
  funext k
  simp [seriesTermRat]

private theorem seriesTermRat_sub_pattern (p q : ℕ) (ρ ρ' : ℕ → ℚ) (k : ℕ) :
    seriesTermRat p q (ρ - ρ') k = seriesTermRat p q ρ k - seriesTermRat p q ρ' k := by
  simp only [seriesTermRat, Pi.sub_apply]
  push_cast
  ring

/-- **No algebraic multiple of `π` in a rational base `p/q`** (from Baker's theorem and good
primes), for coprime `p > q ≥ 1` other than `(p, q) = (3, 1)`. If a series of the class
`F_(p/q)` has value `γ π` with `γ` algebraic, then all its coefficients are zero. -/
theorem eq_zero_of_goodPrimesR (hB : BakerTheorem) {p q : ℕ} (hq : 0 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (h31 : ¬ (p = 3 ∧ q = 1)) (hG : GoodPrimesR p q) {N : ℕ}
    (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTermRat p q ρ) (γ * Real.pi)) : ρ = 0 := by
  classical
  -- an even period
  have hρ' : ∀ k, ρ (k + 2 * N) = ρ k := fun k => by
    have h2 := periodic_mul hρ 2 k
    rwa [mul_comm] at h2
  have hN' : 0 < 2 * N := by positivity
  obtain ⟨N', hN'def⟩ : ∃ N', N' = 2 * N := ⟨_, rfl⟩
  rw [← hN'def] at hρ' hN'
  have h2 : 2 ∣ N' := ⟨N, hN'def⟩
  obtain ⟨β, hβS, hspan⟩ := coeffs_spanInR hB hq hqp hN' h2 hρ' hγ h
  have hS : ∀ r ∈ rootsN N', IsOfFinOrder r := fun r hr => isOfFinOrder_of_mem_rootsN hN' hr
  -- every Fourier coefficient of the twisted pattern is zero
  have hd : ∀ r ∈ rootsN N', coeffAt N' (twistRat p q ρ) r = 0 := by
    intro r hr
    have h0 := Base3.spanIn_linear (fun v : Option ℂ → ℂ => v (some r)) rfl (fun _ _ _ => rfl)
      (fun v hv => intRel_eq_zeroR hq hqp hcop h31 hG hS hv (some r)) hspan
    have h0' : β (some r) = 0 := h0
    rw [hβS r hr, fourierDRat, neg_eq_zero] at h0'
    exact h0'
  -- Fourier inversion: the twisted pattern is zero
  have hc := twistRat_periodic p q h2 hρ'
  funext k
  have hinv := fourier_inversion hN' hc k
  have hz : ∑ a ∈ Finset.range N',
      coeffAt N' (twistRat p q ρ) (zetaN N' ^ a) * (zetaN N' ^ a) ^ k = 0 :=
    Finset.sum_eq_zero fun a ha => by
      rw [hd _ (Finset.mem_image.2 ⟨a, ha, rfl⟩), zero_mul]
  rw [hz] at hinv
  have hk : (ρ k : ℂ) * (xRat p q)⁻¹ ^ (k % 2) = 0 := hinv.symm
  rcases mul_eq_zero.1 hk with h0 | h0
  · exact_mod_cast h0
  · exact absurd h0 (pow_ne_zero _ (inv_ne_zero (xRat_ne_zero hq hqp)))

/-- **The class `F_(p/q)` has no zero relation** (from Baker's theorem and good primes): a
rational periodic pattern has `S(ρ) = 0` if and only if `ρ = 0`. -/
theorem hasSum_zero_iff_of_goodPrimesR (hB : BakerTheorem) {p q : ℕ} (hq : 0 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (h31 : ¬ (p = 3 ∧ q = 1)) (hG : GoodPrimesR p q) {N : ℕ}
    (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (seriesTermRat p q ρ) 0 ↔ ρ = 0 := by
  constructor
  · intro h
    have h' : HasSum (seriesTermRat p q ρ) ((0 : ℝ) * Real.pi) := by rwa [zero_mul]
    exact eq_zero_of_goodPrimesR hB hq hqp hcop h31 hG hN hρ isAlgebraic_zero h'
  · rintro rfl
    rw [seriesTermRat_zero_pattern]
    exact hasSum_zero

/-- **At most one formula** (from Baker's theorem and good primes): two rational periodic
patterns, of periods `N` and `N'`, whose series in the base `p/q` have the same sum are
equal. -/
theorem eq_of_hasSum_of_goodPrimesR (hB : BakerTheorem) {p q : ℕ} (hq : 0 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (h31 : ¬ (p = 3 ∧ q = 1)) (hG : GoodPrimesR p q) {N N' : ℕ}
    (hN : 0 < N) (hN' : 0 < N') {ρ ρ' : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k)
    (hρ' : ∀ k, ρ' (k + N') = ρ' k) {x : ℝ} (h : HasSum (seriesTermRat p q ρ) x)
    (h' : HasSum (seriesTermRat p q ρ') x) : ρ = ρ' := by
  have hper : ∀ k, (ρ - ρ') (k + N * N') = (ρ - ρ') k := fun k => by
    simp only [Pi.sub_apply]
    rw [periodic_mul hρ N' k, Nat.mul_comm N N', periodic_mul hρ' N k]
  have hs : HasSum (seriesTermRat p q (ρ - ρ')) 0 := by
    have h0 := h.sub h'
    rw [sub_self] at h0
    convert h0 using 1
    funext k
    exact seriesTermRat_sub_pattern p q ρ ρ' k
  exact sub_eq_zero.1
    ((hasSum_zero_iff_of_goodPrimesR hB hq hqp hcop h31 hG (Nat.mul_pos hN hN') hper).1 hs)

/-- **No algebraic multiple of `π` is a value of `F_(p/q)`, except 0** (from Baker's theorem
and good primes). -/
theorem mul_pi_eq_zero_of_goodPrimesR (hB : BakerTheorem) {p q : ℕ} (hq : 0 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (h31 : ¬ (p = 3 ∧ q = 1)) (hG : GoodPrimesR p q) {γ : ℝ}
    (hγ : IsAlgebraic ℚ γ) (h : IsFRValue p q (γ * Real.pi)) : γ = 0 := by
  obtain ⟨N, ρ, hN, hρ, hs⟩ := h
  have h0 := eq_zero_of_goodPrimesR hB hq hqp hcop h31 hG hN hρ hγ hs
  rw [h0, seriesTermRat_zero_pattern] at hs
  rcases mul_eq_zero.1 (hs.unique hasSum_zero) with h1 | h1
  · exact h1
  · exact absurd h1 Real.pi_ne_zero

/-- **`π` is not the value of any series of the class `F_(p/q)`** (from Baker's theorem and
good primes). -/
theorem not_isFRValue_pi_of_goodPrimesR (hB : BakerTheorem) {p q : ℕ} (hq : 0 < q)
    (hqp : q < p) (hcop : Nat.Coprime p q) (h31 : ¬ (p = 3 ∧ q = 1)) (hG : GoodPrimesR p q) :
    ¬ IsFRValue p q Real.pi := by
  intro h
  have h1 : IsFRValue p q ((1 : ℝ) * Real.pi) := by rwa [one_mul]
  exact one_ne_zero (mul_pi_eq_zero_of_goodPrimesR hB hq hqp hcop h31 hG isAlgebraic_one h1)

/-! ## 4. The case `q = 1` -/

/-- For `q = 1` the good primes are those of `BaseB`. -/
theorem goodPrimesR_one_iff_goodPrimesB (b : ℕ) : GoodPrimesR b 1 ↔ BaseB.GoodPrimesB b := by
  simp [GoodPrimesR, HasGoodPrimeR, BaseB.GoodPrimesB, BaseB.HasGoodPrimeB]

/-- **The case `q = 1`**: the theorem for an integer base `b ≥ 2` other than 3
(`BaseB.eq_zero_of_goodPrimesB`, stated there for `b ≥ 5`). -/
theorem eq_zero_of_goodPrimesB_of_ne_three (hB : BakerTheorem) {b : ℕ} (hb : 2 ≤ b)
    (hb3 : b ≠ 3) (hG : BaseB.GoodPrimesB b) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (BaseB.seriesTermB b ρ) (γ * Real.pi)) : ρ = 0 := by
  have e : seriesTermRat b 1 ρ = BaseB.seriesTermB b ρ := by
    funext k
    rw [seriesTermRat, BaseB.seriesTermB, Nat.cast_one, one_div, inv_pow, ← div_eq_mul_inv]
  refine eq_zero_of_goodPrimesR hB one_pos (by omega) (Nat.coprime_one_right b)
    (fun h3 => hb3 h3.1) ((goodPrimesR_one_iff_goodPrimesB b).2 hG) hN hρ hγ ?_
  rwa [e]

end RatBase

end PiFormula
