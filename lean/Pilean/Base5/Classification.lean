import Pilean.Base5.Support

/-!
# Base 5: no algebraic multiple of `π` is a value, and there is no zero relation

**Theorem** (`eq_zero_of_goodPrimes5`, from Baker's theorem and `GoodPrimes5`). If a series of
the class F5 has value `γ π` with `γ` algebraic, then all its coefficients are zero.

So, from the same two hypotheses:

* a series of F5 has sum `0` only if its pattern is `0` (`hasSum_zero_iff_of_goodPrimes5`):
  the class F5 has no zero relation;
* a number has at most one formula of the class F5 (`eq_of_hasSum_of_goodPrimes5`);
* a non-zero algebraic multiple of `π` is not a value of F5 (`mul_pi_eq_zero_of_goodPrimes5`),
  and in particular `π` is not (`not_isF5Value_pi_of_goodPrimes5`).

The proof. Write `S(ρ) = ∑ d_r Log(1 - r/t)`, `t = √5` (`series_eq_logs5`). By Baker's theorem
the vector `(iγ; d_r)` is a combination, with algebraic coefficients, of integer relations
among `iπ` and the `Log(1 - r/t)` (`baker_descent`). But there is no integer relation other
than zero (`intRel_eq_zero`):

* its coefficient at a root `r ≠ ±1` is zero (`support_subset_pm_one`);
* its real part is then `z₁ log(1 - 1/√5) + z₋₁ log(1 + 1/√5) = 0`, and these two logarithms
  are independent over `ℤ` (`log_indep5`): their sum is `log(4/5)` and their difference is the
  logarithm of `(3 + √5)/2`, the square of the golden ratio;
* what is left is `z₀ iπ = 0`.

So every `d_r` is zero, and by Fourier inversion the pattern is zero.
-/

open Complex

namespace PiFormula

namespace Base5

/-! ## 1. `log(1 - 1/√5)` and `log(1 + 1/√5)` are independent over `ℤ` -/

theorem sqrt5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)

theorem sqrt5_mul_self : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)

theorem one_lt_sqrt5 : 1 < Real.sqrt 5 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

theorem one_sub_inv_sqrt5_pos : (0 : ℝ) < 1 - 1 / Real.sqrt 5 := by
  rw [sub_pos, div_lt_one sqrt5_pos]
  exact one_lt_sqrt5

theorem one_add_inv_sqrt5_pos : (0 : ℝ) < 1 + 1 / Real.sqrt 5 := by
  have := sqrt5_pos
  positivity

theorem phiSq_pos : (0 : ℝ) < (3 + Real.sqrt 5) / 2 := by
  have := sqrt5_pos
  positivity

theorem three_add_sqrt5_pow (n : ℕ) :
    ∃ x y : ℕ, (3 + Real.sqrt 5) ^ n = x + y * Real.sqrt 5 ∧ 0 < x ∧ (0 < n → 0 < y) := by
  induction n with
  | zero => exact ⟨1, 0, by simp, by norm_num, by simp⟩
  | succ n ih =>
    obtain ⟨x, y, h, hx, hy⟩ := ih
    refine ⟨3 * x + 5 * y, x + 3 * y, ?_, by omega, fun _ => by omega⟩
    rw [pow_succ, h]
    push_cast
    linear_combination (y : ℝ) * sqrt5_mul_self

/-- A non-zero integer power of `(3 + √5)/2`, the square of the golden ratio, is irrational. -/
theorem irrational_phiSq_zpow {C : ℤ} (hC : C ≠ 0) :
    Irrational (((3 + Real.sqrt 5) / 2) ^ C) := by
  have hirr : Irrational (Real.sqrt 5) := Nat.Prime.irrational_sqrt Nat.prime_five
  have key : ∀ n : ℕ, 0 < n → Irrational (((3 + Real.sqrt 5) / 2) ^ n) := by
    intro n hn
    obtain ⟨x, y, h, -, hy⟩ := three_add_sqrt5_pow n
    have h2 : (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by push_cast; rfl
    rw [div_pow, h, h2]
    exact ((hirr.natCast_mul (hy hn).ne').natCast_add x).div_natCast (pow_ne_zero n (by norm_num))
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg C
  · rw [zpow_natCast]
    exact key n (by omega)
  · rw [zpow_neg, zpow_natCast]
    exact (key n (by omega)).inv

/-- `log(1 + 1/√5) = log(1 - 1/√5) + log((3 + √5)/2)`. -/
theorem log_one_add_inv_sqrt5 : Real.log (1 + 1 / Real.sqrt 5) =
    Real.log (1 - 1 / Real.sqrt 5) + Real.log ((3 + Real.sqrt 5) / 2) := by
  have hs := sqrt5_pos
  have h := sqrt5_mul_self
  rw [← Real.log_mul one_sub_inv_sqrt5_pos.ne' phiSq_pos.ne']
  congr 1
  field_simp
  nlinarith

/-- `log(1 - 1/√5) + log(1 + 1/√5) = log(4/5)`. -/
theorem log_one_sub_add_log_one_add : Real.log (1 - 1 / Real.sqrt 5) +
    Real.log (1 + 1 / Real.sqrt 5) = Real.log (4 / 5) := by
  have hs := sqrt5_pos
  have h := sqrt5_mul_self
  rw [← Real.log_mul one_sub_inv_sqrt5_pos.ne' one_add_inv_sqrt5_pos.ne']
  congr 1
  field_simp
  nlinarith

/-- **`log(1 - 1/√5)` and `log(1 + 1/√5)` are linearly independent over `ℤ`.** Their sum is
`log(4/5)` and their difference is `log((3 + √5)/2)`, twice the logarithm of the golden
ratio. -/
theorem log_indep5 {a b : ℤ}
    (h : (a : ℝ) * Real.log (1 - 1 / Real.sqrt 5) + b * Real.log (1 + 1 / Real.sqrt 5) = 0) :
    a = 0 ∧ b = 0 := by
  have hu := phiSq_pos
  have key : ((a + b : ℤ) : ℝ) * Real.log (4 / 5) +
      ((b - a : ℤ) : ℝ) * Real.log ((3 + Real.sqrt 5) / 2) = 0 := by
    push_cast
    linear_combination 2 * h - ((a : ℝ) + b) * log_one_sub_add_log_one_add -
      ((b : ℝ) - a) * log_one_add_inv_sqrt5
  have hexp : (4 / 5 : ℝ) ^ (a + b) * ((3 + Real.sqrt 5) / 2) ^ (b - a) = 1 := by
    have hz : ∀ (x : ℝ), 0 < x → ∀ n : ℤ, Real.exp (n * Real.log x) = x ^ n :=
      fun x hx n => by rw [mul_comm, Real.exp_mul, Real.exp_log hx, Real.rpow_intCast]
    have h' := congrArg Real.exp key
    rw [Real.exp_add, Real.exp_zero, hz _ (by norm_num), hz _ hu] at h'
    exact h'
  have hC : b - a = 0 := by
    by_contra hC
    apply irrational_phiSq_zpow hC
    refine ⟨(4 / 5 : ℚ) ^ (-(a + b)), ?_⟩
    have h45 : (4 / 5 : ℝ) ^ (a + b) ≠ 0 := zpow_ne_zero _ (by norm_num)
    push_cast
    rw [zpow_neg]
    field_simp
    linarith
  have hC' : ((b - a : ℤ) : ℝ) = 0 := by rw [hC, Int.cast_zero]
  rw [hC', zero_mul, add_zero] at key
  have hL : Real.log (4 / 5) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hab : a + b = 0 := by
    rcases mul_eq_zero.1 key with h0 | h0
    · exact_mod_cast h0
    · exact absurd h0 hL
  exact ⟨by omega, by omega⟩

/-! ## 2. Integer relations -/

/-- The logarithms: `iπ` at `none`, and the `Log(1 - r/t)`. -/
noncomputable def lamOf5 : Option ℂ → ℂ
  | none => Real.pi * I
  | some r => Complex.log (1 - r / t5)

theorem isAlgebraic_exp_lamOf5 {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) :
    ∀ i ∈ Finset.insertNone S, IsAlgebraic ℚ (Complex.exp (lamOf5 i)) := by
  intro i hi
  rcases i with _ | r
  · change IsAlgebraic ℚ (Complex.exp (Real.pi * I))
    rw [Complex.exp_pi_mul_I]
    exact isAlgebraic_one.neg
  · have hr := hS r (Finset.some_mem_insertNone.1 hi)
    change IsAlgebraic ℚ (Complex.exp (Complex.log (1 - r / t5)))
    rw [Complex.exp_log (w5_ne_zero hr), div_eq_mul_inv]
    exact isAlgebraic_one.sub ((isAlgebraic_root hr).mul isAlgebraic_t5.inv)

/-- An integer relation among `iπ` and the `Log(1 - r/t)` is a multiplicative relation. -/
theorem relation5_of_intRel {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {z : Option ℂ → ℤ}
    (hz : ∑ i ∈ Finset.insertNone S, (z i : ℂ) * lamOf5 i = 0) :
    IsRelation5 S (fun r => z (some r)) := by
  rw [Finset.sum_insertNone] at hz
  have hz' : (z none : ℂ) * (Real.pi * I) +
      ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / t5) = 0 := hz
  have h1 : ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / t5) =
      -(z none : ℂ) * (Real.pi * I) := by linear_combination hz'
  have hexp : Complex.exp (∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / t5)) =
      ∏ r ∈ S, (1 - r / t5) ^ (z (some r)) := by
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [Complex.exp_int_mul, Complex.exp_log (w5_ne_zero (hS r hr))]
  refine ⟨Complex.exp (-(z none : ℂ) * (Real.pi * I)), ?_, ?_⟩
  · refine isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, ?_⟩
    rw [← Complex.exp_nat_mul]
    have e : ((2 : ℕ) : ℂ) * (-(z none : ℂ) * (Real.pi * I)) =
        ((-z none : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  · rw [← hexp, h1]

theorem re_intCast_mul5 (n : ℤ) (w : ℂ) : ((n : ℂ) * w).re = n * w.re := by
  rw [← Complex.ofReal_intCast, Complex.re_ofReal_mul]

/-- `1 - 1/t` is the positive real number `1 - 1/√5`. -/
theorem log_re_one5 : (Complex.log (1 - 1 / t5)).re = Real.log (1 - 1 / Real.sqrt 5) := by
  have e : (1 - 1 / t5 : ℂ) = ((1 - 1 / Real.sqrt 5 : ℝ) : ℂ) := by
    rw [t5]
    push_cast
    rfl
  rw [Complex.log_re, e, Complex.norm_real, Real.norm_of_nonneg one_sub_inv_sqrt5_pos.le]

/-- `1 + 1/t` is the positive real number `1 + 1/√5`. -/
theorem log_re_neg_one5 :
    (Complex.log (1 - (-1) / t5)).re = Real.log (1 + 1 / Real.sqrt 5) := by
  have e : (1 - (-1) / t5 : ℂ) = ((1 + 1 / Real.sqrt 5 : ℝ) : ℂ) := by
    rw [t5]
    push_cast
    ring
  rw [Complex.log_re, e, Complex.norm_real, Real.norm_of_nonneg one_add_inv_sqrt5_pos.le]

/-- **No integer relation** (from `GoodPrimes5`). An integer relation among `iπ` and the
`Log(1 - r/t)`, `r` in a finite set of roots of unity, is the zero vector. -/
theorem intRel_eq_zero (hG : GoodPrimes5) {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {v : Option ℂ → ℂ} (hv : v ∈ IntRel (Finset.insertNone S) lamOf5) (i : Option ℂ) :
    v i = 0 := by
  classical
  obtain ⟨z, hz0, hzsum, hvz⟩ := hv
  -- the coefficients vanish outside `S`, and at every root other than `1` and `-1`
  have hout : ∀ r, r ∉ S → z (some r) = 0 := fun r hr =>
    hz0 (some r) (fun hmem => hr (Finset.some_mem_insertNone.1 hmem))
  have hsupp : ∀ r, r ≠ 1 → r ≠ -1 → z (some r) = 0 := by
    intro r hr1 hrn
    by_cases hr : r ∈ S
    · exact support_subset_pm_one hG hS (relation5_of_intRel hS hzsum) r hr hr1 hrn
    · exact hout r hr
  rw [Finset.sum_insertNone] at hzsum
  have hzsum' : (z none : ℂ) * (Real.pi * I) +
      ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / t5) = 0 := hzsum
  -- the sum over `S` reduces to the two roots `1` and `-1`
  obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ, f = fun r => (z (some r) : ℂ) * Complex.log (1 - r / t5) :=
    ⟨_, rfl⟩
  have hsum : ∑ r ∈ S, f r = f 1 + f (-1) := by
    have h1n : (1 : ℂ) ≠ -1 := by norm_num
    have hA : ∑ r ∈ S, f r = ∑ r ∈ S ∪ {1, -1}, f r :=
      Finset.sum_subset Finset.subset_union_left fun r _ hr => by
        rw [hf]
        simp only [hout r hr, Int.cast_zero, zero_mul]
    have hB : ∑ r ∈ ({1, -1} : Finset ℂ), f r = ∑ r ∈ S ∪ {1, -1}, f r :=
      Finset.sum_subset Finset.subset_union_right fun r _ hr => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
        rw [hf]
        simp only [hsupp r hr.1 hr.2, Int.cast_zero, zero_mul]
    rw [hA, ← hB, Finset.sum_pair h1n]
  have hsum' : ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / t5) =
      (z (some 1) : ℂ) * Complex.log (1 - 1 / t5) +
        (z (some (-1)) : ℂ) * Complex.log (1 - (-1) / t5) := by
    have := hsum
    rw [hf] at this
    exact this
  rw [hsum'] at hzsum'
  -- real parts
  have hre := congrArg Complex.re hzsum'
  have e1 : ((z none : ℂ) * (Real.pi * I)).re = 0 := by simp
  rw [Complex.add_re, Complex.add_re, e1, re_intCast_mul5, re_intCast_mul5, log_re_one5,
    log_re_neg_one5, Complex.zero_re, zero_add] at hre
  obtain ⟨h1, hn⟩ := log_indep5 hre
  -- what is left is `z₀ iπ = 0`
  rw [h1, hn, Int.cast_zero, zero_mul, zero_mul, add_zero, add_zero] at hzsum'
  have hpiI : (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have h0 : z none = 0 := by
    rcases mul_eq_zero.1 hzsum' with h0 | h0
    · exact_mod_cast h0
    · exact absurd h0 hpiI
  rw [hvz]
  rcases i with _ | r
  · rw [h0, Int.cast_zero]
  · by_cases hr1 : r = 1
    · rw [hr1, h1, Int.cast_zero]
    · by_cases hrn : r = -1
      · rw [hrn, hn, Int.cast_zero]
      · rw [hsupp r hr1 hrn, Int.cast_zero]

/-! ## 3. Baker's theorem: the coefficients lie in the span of the integer relations -/

/-- For a series of value `γ π` (`γ` algebraic), the vector `(iγ; d_r)` is a combination, with
algebraic coefficients, of integer relations among `iπ` and the `Log(1 - r/t)`. -/
theorem coeffs_spanIn5 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h2 : 2 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTerm5 ρ) (γ * Real.pi)) :
    ∃ β : Option ℂ → ℂ, (∀ r ∈ rootsN N, β (some r) = fourierD5 N ρ r) ∧
      SpanIn (algebraicClosure ℚ ℂ) (IntRel (Finset.insertNone (rootsN N)) lamOf5) β := by
  classical
  have hS : ∀ r ∈ rootsN N, IsOfFinOrder r := fun r hr => isOfFinOrder_of_mem_rootsN hN hr
  have h1 := (seriesTerm5_hasSum_logs hN h2 hρ).unique (Complex.hasSum_ofReal.2 h)
  have hγC : IsAlgebraic ℚ (γ : ℂ) :=
    (isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective).2 hγ
  let β : Option ℂ → ℂ := fun o =>
    match o with
    | none => I * γ
    | some r => if r ∈ rootsN N then fourierD5 N ρ r else 0
  have hβS : ∀ r ∈ rootsN N, β (some r) = fourierD5 N ρ r := fun r hr => by
    simp only [β, hr, ↓reduceIte]
  have hF : ∀ x ∈ algebraicClosure ℚ ℂ, IsAlgebraic ℚ x := fun x hx =>
    mem_algebraicClosure_iff.1 hx
  refine ⟨β, hβS, ?_⟩
  refine baker_descent hB _ hF lamOf5 _ (isAlgebraic_exp_lamOf5 hS) β ?_ ?_ ?_
  · intro i hi
    rcases i with _ | r
    · exact mem_algebraicClosure_iff.2 (isAlgebraic_I.mul hγC)
    · have hr : r ∈ rootsN N := Finset.some_mem_insertNone.1 hi
      rw [hβS r hr]
      exact mem_algebraicClosure_iff.2 (isAlgebraic_fourierD5 N ρ (hS r hr))
  · intro i hi
    rcases i with _ | r
    · exact absurd (by simp) hi
    · have hr : r ∉ rootsN N := fun hr => hi (Finset.some_mem_insertNone.2 hr)
      simp only [β, hr, ↓reduceIte]
  · rw [Finset.sum_insertNone]
    have e2 : ∑ r ∈ rootsN N, β (some r) * lamOf5 (some r) =
        ∑ r ∈ rootsN N, fourierD5 N ρ r * Complex.log (1 - r / t5) :=
      Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
    rw [e2, h1]
    change I * γ * (Real.pi * I) + ((γ * Real.pi : ℝ) : ℂ) = 0
    push_cast
    linear_combination ((γ : ℂ) * Real.pi) * Complex.I_sq

/-! ## 4. The theorem -/

/-- **No algebraic multiple of `π` in base 5** (from Baker's theorem and good primes). If a
series of the class F5 has value `γ π` with `γ` algebraic, then all its coefficients are
zero. -/
theorem eq_zero_of_goodPrimes5 (hB : BakerTheorem) (hG : GoodPrimes5) {N : ℕ} (hN : 0 < N)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTerm5 ρ) (γ * Real.pi)) : ρ = 0 := by
  classical
  -- an even period
  have hρ' : ∀ k, ρ (k + 2 * N) = ρ k := fun k => by
    have h2 := periodic_mul hρ 2 k
    rwa [mul_comm] at h2
  have hN' : 0 < 2 * N := by positivity
  obtain ⟨N', hN'def⟩ : ∃ N', N' = 2 * N := ⟨_, rfl⟩
  rw [← hN'def] at hρ' hN'
  have h2 : 2 ∣ N' := ⟨N, hN'def⟩
  obtain ⟨β, hβS, hspan⟩ := coeffs_spanIn5 hB hN' h2 hρ' hγ h
  have hS : ∀ r ∈ rootsN N', IsOfFinOrder r := fun r hr => isOfFinOrder_of_mem_rootsN hN' hr
  -- every Fourier coefficient of the twisted pattern is zero
  have hd : ∀ r ∈ rootsN N', coeffAt N' (twist5 ρ) r = 0 := by
    intro r hr
    have h0 := Base3.spanIn_linear (fun v : Option ℂ → ℂ => v (some r)) rfl (fun _ _ _ => rfl)
      (fun v hv => intRel_eq_zero hG hS hv (some r)) hspan
    have h0' : β (some r) = 0 := h0
    rw [hβS r hr, fourierD5, neg_eq_zero] at h0'
    exact h0'
  -- Fourier inversion: the twisted pattern is zero
  have hc := twist5_periodic h2 hρ'
  funext k
  have hinv := fourier_inversion hN' hc k
  have hz : ∑ a ∈ Finset.range N',
      coeffAt N' (twist5 ρ) (zetaN N' ^ a) * (zetaN N' ^ a) ^ k = 0 :=
    Finset.sum_eq_zero fun a ha => by
      rw [hd _ (Finset.mem_image.2 ⟨a, ha, rfl⟩), zero_mul]
  rw [hz] at hinv
  have hk : (ρ k : ℂ) * t5 ^ (k % 2) = 0 := hinv.symm
  rcases mul_eq_zero.1 hk with h0 | h0
  · exact_mod_cast h0
  · exact absurd h0 (pow_ne_zero _ t5_ne_zero)

/-- **The class F5 has no zero relation** (from Baker's theorem and good primes): a rational
periodic pattern has `S(ρ) = 0` if and only if `ρ = 0`. -/
theorem hasSum_zero_iff_of_goodPrimes5 (hB : BakerTheorem) (hG : GoodPrimes5) {N : ℕ}
    (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (seriesTerm5 ρ) 0 ↔ ρ = 0 := by
  constructor
  · intro h
    have h' : HasSum (seriesTerm5 ρ) ((0 : ℝ) * Real.pi) := by rwa [zero_mul]
    exact eq_zero_of_goodPrimes5 hB hG hN hρ isAlgebraic_zero h'
  · rintro rfl
    rw [seriesTerm5_zero]
    exact hasSum_zero

/-- **At most one formula** (from Baker's theorem and good primes): two rational periodic
patterns, of periods `N` and `N'`, whose series have the same sum are equal. -/
theorem eq_of_hasSum_of_goodPrimes5 (hB : BakerTheorem) (hG : GoodPrimes5) {N N' : ℕ}
    (hN : 0 < N) (hN' : 0 < N') {ρ ρ' : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k)
    (hρ' : ∀ k, ρ' (k + N') = ρ' k) {x : ℝ} (h : HasSum (seriesTerm5 ρ) x)
    (h' : HasSum (seriesTerm5 ρ') x) : ρ = ρ' := by
  have hper : ∀ k, (ρ - ρ') (k + N * N') = (ρ - ρ') k := fun k => by
    simp only [Pi.sub_apply]
    rw [periodic_mul hρ N' k, Nat.mul_comm N N', periodic_mul hρ' N k]
  have hs : HasSum (seriesTerm5 (ρ - ρ')) 0 := by
    have h0 := h.sub h'
    rw [sub_self] at h0
    convert h0 using 1
    funext k
    exact seriesTerm5_sub ρ ρ' k
  exact sub_eq_zero.1
    ((hasSum_zero_iff_of_goodPrimes5 hB hG (Nat.mul_pos hN hN') hper).1 hs)

/-- **No algebraic multiple of `π` is a value of F5, except 0** (from Baker's theorem and good
primes). -/
theorem mul_pi_eq_zero_of_goodPrimes5 (hB : BakerTheorem) (hG : GoodPrimes5) {γ : ℝ}
    (hγ : IsAlgebraic ℚ γ) (h : IsF5Value (γ * Real.pi)) : γ = 0 := by
  obtain ⟨N, ρ, hN, hρ, hs⟩ := h
  have h0 := eq_zero_of_goodPrimes5 hB hG hN hρ hγ hs
  rw [h0, seriesTerm5_zero] at hs
  rcases mul_eq_zero.1 (hs.unique hasSum_zero) with h1 | h1
  · exact h1
  · exact absurd h1 Real.pi_ne_zero

/-- **`π` is not the value of any series of the class F5** (from Baker's theorem and good
primes). -/
theorem not_isF5Value_pi_of_goodPrimes5 (hB : BakerTheorem) (hG : GoodPrimes5) :
    ¬ IsF5Value Real.pi := by
  intro h
  have h1 : IsF5Value ((1 : ℝ) * Real.pi) := by rwa [one_mul]
  exact one_ne_zero (mul_pi_eq_zero_of_goodPrimes5 hB hG isAlgebraic_one h1)

end Base5

end PiFormula
