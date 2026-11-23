import Pilean.BaseB.Support
import Pilean.BaseB.ClassificationAux
import Pilean.PiFormula.Transcendence

/-!
# A general base `b ≥ 5`: no algebraic multiple of `π` is a value, and no zero relation

`F_b` is the class of series `S(ρ) = ∑ ρ(k) b^(-⌊k/2⌋)/k` with `ρ` rational and periodic.

**Theorem** (`eq_zero_of_goodPrimesB`, from Baker's theorem and `GoodPrimesB b`, for `b ≥ 5`).
If a series of the class `F_b` has value `γ π` with `γ` algebraic, then all its coefficients
are zero.

So, from the same hypotheses:

* a series of `F_b` has sum `0` only if its pattern is `0` (`hasSum_zero_iff_of_goodPrimesB`);
* a number has at most one formula of the class `F_b` (`eq_of_hasSum_of_goodPrimesB`);
* a non-zero algebraic multiple of `π` is not a value of `F_b`
  (`mul_pi_eq_zero_of_goodPrimesB`), and in particular `π` is not
  (`not_isFBValue_pi_of_goodPrimesB`);
* a series with a non-zero pattern has a transcendental sum
  (`transcendental_of_hasSum_of_goodPrimesB`).

The proof. Write `S(ρ) = ∑ d_r Log(1 - r/t)`, `t = √b` (`series_eq_logsB`). By Baker's theorem
the vector `(iγ; d_r)` is a combination, with algebraic coefficients, of integer relations
among `iπ` and the `Log(1 - r/t)` (`baker_descent`). But there is no integer relation other
than zero (`intRel_eq_zeroB`):

* its coefficient at a root `r` with `r⁴ ≠ 1` is zero (`support_subset_fourth_roots`);
* the real part of what is left is
  `z₁ log(1 - 1/√b) + z₋₁ log(1 + 1/√b) + (z_i + z₋ᵢ) log(1 + 1/b)/2 = 0`, and these three
  logarithms are independent over `ℤ` (`log_indepB`);
* then `((t - i)/(t + i))^(2 z_i) = 1`, and `(t - i)/(t + i)` is not a root of unity
  (`unitB_zpow_eq_one`); this is the step that fails in base 3;
* what is left is `z₀ iπ = 0`.

So every `d_r` is zero, and by Fourier inversion the pattern is zero.

The last section is the analogue of `Base5/Transcendence.lean`: from Baker's theorem alone,
for every `b ≥ 2`, a value of `F_b` that is `α + γ π` with `α`, `γ` algebraic has `α = 0`.
-/

open Complex

namespace PiFormula

namespace BaseB

/-! ## 1. Integer relations -/

/-- The logarithms: `iπ` at `none`, and the `Log(1 - r/t)`. -/
noncomputable def lamOfB (b : ℕ) : Option ℂ → ℂ
  | none => Real.pi * I
  | some r => Complex.log (1 - r / tB b)

theorem isAlgebraic_exp_log_wB {b : ℕ} (hb : 2 ≤ b) {r : ℂ} (hr : IsOfFinOrder r) :
    IsAlgebraic ℚ (Complex.exp (Complex.log (1 - r / tB b))) := by
  rw [Complex.exp_log (wB_ne_zero hb hr), div_eq_mul_inv]
  exact isAlgebraic_one.sub ((isAlgebraic_root hr).mul (isAlgebraic_tB b).inv)

theorem isAlgebraic_exp_lamOfB {b : ℕ} (hb : 2 ≤ b) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) :
    ∀ i ∈ Finset.insertNone S, IsAlgebraic ℚ (Complex.exp (lamOfB b i)) := by
  intro i hi
  rcases i with _ | r
  · change IsAlgebraic ℚ (Complex.exp (Real.pi * I))
    rw [Complex.exp_pi_mul_I]
    exact isAlgebraic_one.neg
  · exact isAlgebraic_exp_log_wB hb (hS r (Finset.some_mem_insertNone.1 hi))

/-- An integer relation among `iπ` and the `Log(1 - r/t)` is a multiplicative relation. -/
theorem relationB_of_intRel {b : ℕ} (hb : 2 ≤ b) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {z : Option ℂ → ℤ}
    (hz : ∑ i ∈ Finset.insertNone S, (z i : ℂ) * lamOfB b i = 0) :
    IsRelationB b S (fun r => z (some r)) := by
  rw [Finset.sum_insertNone] at hz
  have hz' : (z none : ℂ) * (Real.pi * I) +
      ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / tB b) = 0 := hz
  have h1 : ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / tB b) =
      -(z none : ℂ) * (Real.pi * I) := by linear_combination hz'
  have hexp : Complex.exp (∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / tB b)) =
      ∏ r ∈ S, (1 - r / tB b) ^ (z (some r)) := by
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [Complex.exp_int_mul, Complex.exp_log (wB_ne_zero hb (hS r hr))]
  refine ⟨Complex.exp (-(z none : ℂ) * (Real.pi * I)), ?_, ?_⟩
  · refine isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, ?_⟩
    rw [← Complex.exp_nat_mul]
    have e : ((2 : ℕ) : ℂ) * (-(z none : ℂ) * (Real.pi * I)) =
        ((-z none : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  · rw [← hexp, h1]

/-- **No integer relation** (from `GoodPrimesB b`, `b ≥ 5`). An integer relation among `iπ`
and the `Log(1 - r/t)`, `r` in a finite set of roots of unity, is the zero vector. -/
theorem intRel_eq_zeroB {b : ℕ} (hb : 5 ≤ b) (hG : GoodPrimesB b) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {v : Option ℂ → ℂ}
    (hv : v ∈ IntRel (Finset.insertNone S) (lamOfB b)) (i : Option ℂ) : v i = 0 := by
  classical
  have hb2 : 2 ≤ b := by omega
  obtain ⟨z, hz0, hzsum, hvz⟩ := hv
  -- the coefficients vanish outside `S`, and at every root with `r⁴ ≠ 1`
  have hout : ∀ r, r ∉ S → z (some r) = 0 := fun r hr =>
    hz0 (some r) (fun hmem => hr (Finset.some_mem_insertNone.1 hmem))
  have hsupp : ∀ r, r ^ 4 ≠ 1 → z (some r) = 0 := by
    intro r hr4
    by_cases hr : r ∈ S
    · exact support_subset_fourth_roots hb2 hG hS (relationB_of_intRel hb2 hS hzsum) r hr hr4
    · exact hout r hr
  rw [Finset.sum_insertNone] at hzsum
  have hzsum' : (z none : ℂ) * (Real.pi * I) +
      ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / tB b) = 0 := hzsum
  -- the sum over `S` reduces to the four roots `1, -1, i, -i`
  obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ, f = fun r => (z (some r) : ℂ) * Complex.log (1 - r / tB b) :=
    ⟨_, rfl⟩
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
        simp only [hsupp r (pow_four_ne_one hr.1 hr.2.1 hr.2.2.1 hr.2.2.2), Int.cast_zero,
          zero_mul]
    rw [hA, ← hB, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_pair h3]
    ring
  have hsum' : ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / tB b) =
      (z (some 1) : ℂ) * Complex.log (1 - 1 / tB b) +
        (z (some (-1)) : ℂ) * Complex.log (1 - (-1) / tB b) +
        (z (some I) : ℂ) * Complex.log (1 - I / tB b) +
        (z (some (-I)) : ℂ) * Complex.log (1 - (-I) / tB b) := by
    have := hsum
    rw [hf] at this
    exact this
  rw [hsum'] at hzsum'
  -- real parts
  have hre := congrArg Complex.re hzsum'
  have e1 : ((z none : ℂ) * (Real.pi * I)).re = 0 := by simp
  simp only [Complex.add_re, e1, Base5.re_intCast_mul5, log_re_oneB hb2, log_re_neg_oneB hb2,
    log_re_IB, log_re_neg_IB, Complex.zero_re, zero_add] at hre
  obtain ⟨h1, hn, hs⟩ := log_indepB hb2 (z₁ := z (some 1)) (z₂ := z (some (-1)))
    (s := z (some I) + z (some (-I))) (by push_cast; linear_combination 2 * hre)
  have c1 : (z (some 1) : ℂ) = 0 := by rw [h1, Int.cast_zero]
  have cn : (z (some (-1)) : ℂ) = 0 := by rw [hn, Int.cast_zero]
  have hz4 : z (some (-I)) = -z (some I) := by omega
  have c4 : (z (some (-I)) : ℂ) = -(z (some I) : ℂ) := by rw [hz4, Int.cast_neg]
  -- `((t - i)/(t + i))^(2 z_i) = 1`
  have hnI : IsOfFinOrder (-I) := by
    rw [← Complex.inv_I]
    exact isOfFinOrder_inv' isOfFinOrder_I
  have hunit : ((1 - I / tB b) / (1 - (-I) / tB b)) ^ (2 * z (some I)) = 1 := by
    have e : ((2 * z (some I) : ℤ) : ℂ) *
        (Complex.log (1 - I / tB b) - Complex.log (1 - (-I) / tB b)) =
        ((-z none : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast
      linear_combination 2 * hzsum' - 2 * Complex.log (1 - (-I) / tB b) * c4 -
        2 * Complex.log (1 - 1 / tB b) * c1 - 2 * Complex.log (1 - (-1) / tB b) * cn
    have key := congrArg Complex.exp e
    rwa [Complex.exp_int_mul, Complex.exp_sub, Complex.exp_log (wB_ne_zero hb2 isOfFinOrder_I),
      Complex.exp_log (wB_ne_zero hb2 hnI), Complex.exp_int_mul_two_pi_mul_I] at key
  have h3 : z (some I) = 0 := by
    have := unitB_zpow_eq_one (by omega : 4 ≤ b) hunit
    omega
  have h4 : z (some (-I)) = 0 := by omega
  have c3 : (z (some I) : ℂ) = 0 := by rw [h3, Int.cast_zero]
  have c4' : (z (some (-I)) : ℂ) = 0 := by rw [h4, Int.cast_zero]
  -- what is left is `z₀ iπ = 0`
  have hlast : (z none : ℂ) * (Real.pi * I) = 0 := by
    linear_combination hzsum' - Complex.log (1 - 1 / tB b) * c1 -
      Complex.log (1 - (-1) / tB b) * cn - Complex.log (1 - I / tB b) * c3 -
      Complex.log (1 - (-I) / tB b) * c4'
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
          · rw [hsupp r (pow_four_ne_one hr1 hrn hrI hrnI), Int.cast_zero]

/-! ## 2. Baker's theorem: the coefficients lie in the span of the integer relations -/

/-- For a series of value `γ π` (`γ` algebraic), the vector `(iγ; d_r)` is a combination, with
algebraic coefficients, of integer relations among `iπ` and the `Log(1 - r/t)`. -/
theorem coeffs_spanInB (hB : BakerTheorem) {b : ℕ} (hb : 2 ≤ b) {N : ℕ} (hN : 0 < N)
    (h2 : 2 ∣ N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTermB b ρ) (γ * Real.pi)) :
    ∃ β : Option ℂ → ℂ, (∀ r ∈ rootsN N, β (some r) = fourierDB b N ρ r) ∧
      SpanIn (algebraicClosure ℚ ℂ) (IntRel (Finset.insertNone (rootsN N)) (lamOfB b)) β := by
  classical
  have hS : ∀ r ∈ rootsN N, IsOfFinOrder r := fun r hr => isOfFinOrder_of_mem_rootsN hN hr
  have h1 := (seriesTermB_hasSum_logs hb hN h2 hρ).unique (Complex.hasSum_ofReal.2 h)
  have hγC : IsAlgebraic ℚ (γ : ℂ) := isAlgebraic_ofReal hγ
  let β : Option ℂ → ℂ := fun o =>
    match o with
    | none => I * γ
    | some r => if r ∈ rootsN N then fourierDB b N ρ r else 0
  have hβS : ∀ r ∈ rootsN N, β (some r) = fourierDB b N ρ r := fun r hr => by
    simp only [β, hr, ↓reduceIte]
  have hF : ∀ x ∈ algebraicClosure ℚ ℂ, IsAlgebraic ℚ x := fun x hx =>
    mem_algebraicClosure_iff.1 hx
  refine ⟨β, hβS, ?_⟩
  refine baker_descent hB _ hF (lamOfB b) _ (isAlgebraic_exp_lamOfB hb hS) β ?_ ?_ ?_
  · intro i hi
    rcases i with _ | r
    · exact mem_algebraicClosure_iff.2 (isAlgebraic_I.mul hγC)
    · have hr : r ∈ rootsN N := Finset.some_mem_insertNone.1 hi
      rw [hβS r hr]
      exact mem_algebraicClosure_iff.2 (isAlgebraic_fourierDB b N ρ (hS r hr))
  · intro i hi
    rcases i with _ | r
    · exact absurd (by simp) hi
    · have hr : r ∉ rootsN N := fun hr => hi (Finset.some_mem_insertNone.2 hr)
      simp only [β, hr, ↓reduceIte]
  · rw [Finset.sum_insertNone]
    have e2 : ∑ r ∈ rootsN N, β (some r) * lamOfB b (some r) =
        ∑ r ∈ rootsN N, fourierDB b N ρ r * Complex.log (1 - r / tB b) :=
      Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
    rw [e2, h1]
    change I * γ * (Real.pi * I) + ((γ * Real.pi : ℝ) : ℂ) = 0
    push_cast
    linear_combination ((γ : ℂ) * Real.pi) * Complex.I_sq

/-! ## 3. The theorem -/

private theorem seriesTermB_zero_pattern (b : ℕ) : seriesTermB b 0 = fun _ => 0 := by
  funext k
  simp [seriesTermB]

private theorem seriesTermB_sub_pattern (b : ℕ) (ρ ρ' : ℕ → ℚ) (k : ℕ) :
    seriesTermB b (ρ - ρ') k = seriesTermB b ρ k - seriesTermB b ρ' k := by
  simp only [seriesTermB, Pi.sub_apply]
  push_cast
  ring

/-- **No algebraic multiple of `π` in a base `b ≥ 5`** (from Baker's theorem and good primes).
If a series of the class `F_b` has value `γ π` with `γ` algebraic, then all its coefficients
are zero. -/
theorem eq_zero_of_goodPrimesB (hB : BakerTheorem) {b : ℕ} (hb : 5 ≤ b) (hG : GoodPrimesB b)
    {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ}
    (hγ : IsAlgebraic ℚ γ) (h : HasSum (seriesTermB b ρ) (γ * Real.pi)) : ρ = 0 := by
  classical
  have hb2 : 2 ≤ b := by omega
  -- an even period
  have hρ' : ∀ k, ρ (k + 2 * N) = ρ k := fun k => by
    have h2 := periodic_mul hρ 2 k
    rwa [mul_comm] at h2
  have hN' : 0 < 2 * N := by positivity
  obtain ⟨N', hN'def⟩ : ∃ N', N' = 2 * N := ⟨_, rfl⟩
  rw [← hN'def] at hρ' hN'
  have h2 : 2 ∣ N' := ⟨N, hN'def⟩
  obtain ⟨β, hβS, hspan⟩ := coeffs_spanInB hB hb2 hN' h2 hρ' hγ h
  have hS : ∀ r ∈ rootsN N', IsOfFinOrder r := fun r hr => isOfFinOrder_of_mem_rootsN hN' hr
  -- every Fourier coefficient of the twisted pattern is zero
  have hd : ∀ r ∈ rootsN N', coeffAt N' (twistB b ρ) r = 0 := by
    intro r hr
    have h0 := Base3.spanIn_linear (fun v : Option ℂ → ℂ => v (some r)) rfl (fun _ _ _ => rfl)
      (fun v hv => intRel_eq_zeroB hb hG hS hv (some r)) hspan
    have h0' : β (some r) = 0 := h0
    rw [hβS r hr, fourierDB, neg_eq_zero] at h0'
    exact h0'
  -- Fourier inversion: the twisted pattern is zero
  have hc := twistB_periodic b h2 hρ'
  funext k
  have hinv := fourier_inversion hN' hc k
  have hz : ∑ a ∈ Finset.range N',
      coeffAt N' (twistB b ρ) (zetaN N' ^ a) * (zetaN N' ^ a) ^ k = 0 :=
    Finset.sum_eq_zero fun a ha => by
      rw [hd _ (Finset.mem_image.2 ⟨a, ha, rfl⟩), zero_mul]
  rw [hz] at hinv
  have hk : (ρ k : ℂ) * tB b ^ (k % 2) = 0 := hinv.symm
  rcases mul_eq_zero.1 hk with h0 | h0
  · exact_mod_cast h0
  · exact absurd h0 (pow_ne_zero _ (tB_ne_zero hb2))

/-- **The class `F_b`, `b ≥ 5`, has no zero relation** (from Baker's theorem and good primes):
a rational periodic pattern has `S(ρ) = 0` if and only if `ρ = 0`. -/
theorem hasSum_zero_iff_of_goodPrimesB (hB : BakerTheorem) {b : ℕ} (hb : 5 ≤ b)
    (hG : GoodPrimesB b) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (seriesTermB b ρ) 0 ↔ ρ = 0 := by
  constructor
  · intro h
    have h' : HasSum (seriesTermB b ρ) ((0 : ℝ) * Real.pi) := by rwa [zero_mul]
    exact eq_zero_of_goodPrimesB hB hb hG hN hρ isAlgebraic_zero h'
  · rintro rfl
    rw [seriesTermB_zero_pattern]
    exact hasSum_zero

/-- **At most one formula** (from Baker's theorem and good primes): two rational periodic
patterns, of periods `N` and `N'`, whose series in a base `b ≥ 5` have the same sum are
equal. -/
theorem eq_of_hasSum_of_goodPrimesB (hB : BakerTheorem) {b : ℕ} (hb : 5 ≤ b)
    (hG : GoodPrimesB b) {N N' : ℕ} (hN : 0 < N) (hN' : 0 < N') {ρ ρ' : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) (hρ' : ∀ k, ρ' (k + N') = ρ' k) {x : ℝ}
    (h : HasSum (seriesTermB b ρ) x) (h' : HasSum (seriesTermB b ρ') x) : ρ = ρ' := by
  have hper : ∀ k, (ρ - ρ') (k + N * N') = (ρ - ρ') k := fun k => by
    simp only [Pi.sub_apply]
    rw [periodic_mul hρ N' k, Nat.mul_comm N N', periodic_mul hρ' N k]
  have hs : HasSum (seriesTermB b (ρ - ρ')) 0 := by
    have h0 := h.sub h'
    rw [sub_self] at h0
    convert h0 using 1
    funext k
    exact seriesTermB_sub_pattern b ρ ρ' k
  exact sub_eq_zero.1
    ((hasSum_zero_iff_of_goodPrimesB hB hb hG (Nat.mul_pos hN hN') hper).1 hs)

/-- **No algebraic multiple of `π` is a value of `F_b`, `b ≥ 5`, except 0** (from Baker's
theorem and good primes). -/
theorem mul_pi_eq_zero_of_goodPrimesB (hB : BakerTheorem) {b : ℕ} (hb : 5 ≤ b)
    (hG : GoodPrimesB b) {γ : ℝ} (hγ : IsAlgebraic ℚ γ) (h : IsFBValue b (γ * Real.pi)) :
    γ = 0 := by
  obtain ⟨N, ρ, hN, hρ, hs⟩ := h
  have h0 := eq_zero_of_goodPrimesB hB hb hG hN hρ hγ hs
  rw [h0, seriesTermB_zero_pattern] at hs
  rcases mul_eq_zero.1 (hs.unique hasSum_zero) with h1 | h1
  · exact h1
  · exact absurd h1 Real.pi_ne_zero

/-- **`π` is not the value of any series of the class `F_b`, `b ≥ 5`** (from Baker's theorem
and good primes). -/
theorem not_isFBValue_pi_of_goodPrimesB (hB : BakerTheorem) {b : ℕ} (hb : 5 ≤ b)
    (hG : GoodPrimesB b) : ¬ IsFBValue b Real.pi := by
  intro h
  have h1 : IsFBValue b ((1 : ℝ) * Real.pi) := by rwa [one_mul]
  exact one_ne_zero (mul_pi_eq_zero_of_goodPrimesB hB hb hG isAlgebraic_one h1)

/-! ## 4. Transcendence -/

/-- The general form, with complex `α` and `γ`: if the real number `S(ρ)` is `α + γ π` with
`α`, `γ` algebraic complex numbers, then `α = 0`. For every base `b ≥ 2`. -/
theorem alg_eq_zero_of_hasSum_complexB (hB : BakerTheorem) {b : ℕ} (hb : 2 ≤ b) {N : ℕ}
    (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {x : ℝ}
    (h : HasSum (seriesTermB b ρ) x) {α γ : ℂ} (hα : IsAlgebraic ℚ α) (hγ : IsAlgebraic ℚ γ)
    (hx : (x : ℂ) = α + γ * Real.pi) : α = 0 := by
  -- an even period
  have hρ' : ∀ k, ρ (k + 2 * N) = ρ k := fun k => by
    have h2 := periodic_mul hρ 2 k
    rwa [mul_comm] at h2
  have hN' : 0 < 2 * N := by positivity
  have hS : ∀ r ∈ rootsN (2 * N), IsOfFinOrder r := fun r hr =>
    isOfFinOrder_of_mem_rootsN hN' hr
  have h2 := (seriesTermB_hasSum_logs hb hN' (Dvd.intro N rfl) hρ').unique
    (Complex.hasSum_ofReal.2 h)
  exact const_eq_zero_of_sum_logs hB (rootsN (2 * N)) (fun r => Complex.log (1 - r / tB b))
    (fun r hr => isAlgebraic_exp_log_wB hb (hS r hr)) (fourierDB b (2 * N) ρ)
    (fun r hr => isAlgebraic_fourierDB b (2 * N) ρ (hS r hr)) hα hγ (h2.trans hx)

/-- **The algebraic part is zero** (from Baker's theorem), in every base `b ≥ 2`. If a rational
periodic pattern `ρ` has `∑ ρ(k) b^(-⌊k/2⌋)/k = α + γ π` with `α` and `γ` algebraic, then
`α = 0`. -/
theorem alg_eq_zero_of_hasSum_add_mul_piB (hB : BakerTheorem) {b : ℕ} (hb : 2 ≤ b) {N : ℕ}
    (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {α γ : ℝ} (hα : IsAlgebraic ℚ α)
    (hγ : IsAlgebraic ℚ γ) (h : HasSum (seriesTermB b ρ) (α + γ * Real.pi)) : α = 0 := by
  have hC := alg_eq_zero_of_hasSum_complexB hB hb hN hρ h (isAlgebraic_ofReal hα)
    (isAlgebraic_ofReal hγ) (by push_cast; rfl)
  exact_mod_cast hC

/-- **An algebraic value is zero** (from Baker's theorem), in every base `b ≥ 2`. -/
theorem eq_zero_of_hasSum_of_isAlgebraicB (hB : BakerTheorem) {b : ℕ} (hb : 2 ≤ b) {N : ℕ}
    (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {x : ℝ} (hx : IsAlgebraic ℚ x)
    (h : HasSum (seriesTermB b ρ) x) : x = 0 := by
  refine alg_eq_zero_of_hasSum_add_mul_piB hB hb hN hρ hx (γ := 0) isAlgebraic_zero ?_
  rwa [zero_mul, add_zero]

/-- **The values of the class `F_b` that are algebraic numbers: only `0`** (from Baker's
theorem), in every base `b ≥ 2`. -/
theorem eq_zero_of_isFBValue_of_isAlgebraic (hB : BakerTheorem) {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (h : IsFBValue b x) (hx : IsAlgebraic ℚ x) : x = 0 := by
  obtain ⟨N, ρ, hN, hρ, hs⟩ := h
  exact eq_zero_of_hasSum_of_isAlgebraicB hB hb hN hρ hx hs

/-- **Every value of the class `F_b` is `0` or transcendental** (from Baker's theorem), in
every base `b ≥ 2`. -/
theorem transcendental_of_isFBValue (hB : BakerTheorem) {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (h : IsFBValue b x) (hx : x ≠ 0) : Transcendental ℚ x :=
  fun ha => hx (eq_zero_of_isFBValue_of_isAlgebraic hB hb h ha)

/-- **No formula for a number `α + γ π` in a base `b ≥ 5`** (from Baker's theorem and good
primes). If a rational periodic pattern `ρ` has `∑ ρ(k) b^(-⌊k/2⌋)/k = α + γ π` with `α` and
`γ` algebraic, then `ρ = 0`. -/
theorem eq_zero_of_hasSum_add_mul_pi_of_goodPrimesB (hB : BakerTheorem) {b : ℕ} (hb : 5 ≤ b)
    (hG : GoodPrimesB b) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k)
    {α γ : ℝ} (hα : IsAlgebraic ℚ α) (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTermB b ρ) (α + γ * Real.pi)) : ρ = 0 := by
  have h0 := alg_eq_zero_of_hasSum_add_mul_piB hB (by omega) hN hρ hα hγ h
  rw [h0, zero_add] at h
  exact eq_zero_of_goodPrimesB hB hb hG hN hρ hγ h

/-- **A series of the class `F_b`, `b ≥ 5`, with a non-zero pattern has a transcendental sum**
(from Baker's theorem and good primes). -/
theorem transcendental_of_hasSum_of_goodPrimesB (hB : BakerTheorem) {b : ℕ} (hb : 5 ≤ b)
    (hG : GoodPrimesB b) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k)
    (hρ0 : ρ ≠ 0) {x : ℝ} (h : HasSum (seriesTermB b ρ) x) : Transcendental ℚ x := by
  intro hx
  refine hρ0 (eq_zero_of_hasSum_add_mul_pi_of_goodPrimesB hB hb hG hN hρ hx (γ := 0)
    isAlgebraic_zero ?_)
  rwa [zero_mul, add_zero]

/-- **The only number `α + γ π`, `α` and `γ` algebraic, that is a value of `F_b`, `b ≥ 5`, is
`0`** (from Baker's theorem and good primes). -/
theorem eq_zero_of_isFBValue_add_mul_pi_of_goodPrimesB (hB : BakerTheorem) {b : ℕ}
    (hb : 5 ≤ b) (hG : GoodPrimesB b) {α γ : ℝ} (hα : IsAlgebraic ℚ α) (hγ : IsAlgebraic ℚ γ)
    (h : IsFBValue b (α + γ * Real.pi)) : α = 0 ∧ γ = 0 := by
  obtain ⟨N, ρ, hN, hρ, hs⟩ := h
  have h0 := alg_eq_zero_of_hasSum_add_mul_piB hB (by omega) hN hρ hα hγ hs
  rw [h0, zero_add] at hs
  exact ⟨h0, mul_pi_eq_zero_of_goodPrimesB hB hb hG hγ ⟨N, ρ, hN, hρ, hs⟩⟩

end BaseB

end PiFormula
