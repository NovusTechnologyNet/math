module

public import Pilean.BaseB.LogNonValueAux

/-!
# A general base `b ≥ 5`, `b ≠ 9`: logarithms of numbers built from the primes of the base

`F_b` is the class of series `∑ ρ(k) b^(-⌊k/2⌋)/k` with `ρ` rational and periodic.

**Theorem** (`not_isFBValue_mul_pi_add_log`, from Baker's theorem). Let `b ≥ 5`, `b ≠ 9`, and
let `y ≠ 1` be a positive rational number all of whose prime factors (of the numerator and of
the denominator) divide `b`. Then no number `q π + q' log y` with `q, q'` rational, `q' ≠ 0`,
is a value of the class `F_b`.

Examples: `log b` itself (`not_isFBValue_log_self`); the logarithm of an integer `n ≥ 2` all of
whose prime factors divide `b` (`not_isFBValue_log_nat`); `log 2`, `log 5` and `log 10` in
base 10. The versions in the namespace `Unconditional` use the imported proof of Baker's
theorem and have no hypothesis.

The base 9 is a true exception: `log 3 = -2 log(1 - 1/3) + log(1 + 1/3)` is a value of `F_9`.

The proof. Let `t = √b` and `S(ρ) = ∑ d_r Log(1 - r/t) = q π + q' log y` (`series_eq_logsB`).
By Baker's theorem the vector `(-q'; i q; d_r)` is a combination, with algebraic coefficients,
of integer relations among `log y`, `iπ` and the `Log(1 - r/t)` (`baker_descent`). In such a
relation `m log y + z₀ iπ + ∑ z_r Log(1 - r/t) = 0` the coefficient `m` is zero
(`intRel_none_eq_zeroB`):

* exponentiating, `u ∏ (1 - r/t)^(z_r) = ± v` with `v / u = y^(-m)`, and every prime factor of
  `u` and `v` divides `b` (`relationNatB_of_intRel`);
* so `z_r = 0` at every root with `r⁴ ≠ 1` (`support_subset_fourth_roots_nat`): a good prime
  lies over a rational prime that does not divide `b`;
* the real part of what is left is
  `m log y + z₁ log(1 - 1/√b) + z₋₁ log(1 + 1/√b) + (z_i + z₋ᵢ) log(1 + 1/b)/2 = 0`,
  and there `m = 0` (`log_rat_indepB`); this is the step that needs `b ≠ 9`.

So the coefficient `-q'` of `log y` is zero.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace BaseB

/-! ## 1. Integer relations with one more logarithm -/

/-- The logarithms: `Λ` at `none`, `iπ` at `some none`, and the `Log(1 - r/t)`. -/
noncomputable def lamOfBY (b : ℕ) (Λ : ℂ) : Option (Option ℂ) → ℂ
  | none => Λ
  | some none => Real.pi * I
  | some (some r) => Complex.log (1 - r / tB b)

/-- A positive rational number is a quotient `v / u` of positive integers, and the primes that
divide `u` or `v` are those at which its valuation is not zero. -/
private theorem exists_nat_quot {w : ℚ} (hw : 0 < w) :
    ∃ u v : ℕ, w * (u : ℚ) = (v : ℚ) ∧ (∀ p : ℕ, p.Prime → p ∣ u → padicValRat p w ≠ 0) ∧
      (∀ p : ℕ, p.Prime → p ∣ v → padicValRat p w ≠ 0) := by
  have hnum : 0 < w.num := Rat.num_pos.2 hw
  have hcop : Nat.Coprime w.num.natAbs w.den := w.reduced
  have hnd : ∀ p : ℕ, p.Prime → p ∣ w.num.natAbs → p ∣ w.den → False := by
    intro p hp h1 h2
    have h3 := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
  refine ⟨w.den, w.num.natAbs, ?_, ?_, ?_⟩
  · have h1 : ((w.num.natAbs : ℤ) : ℚ) = (w.num : ℚ) := by
      rw [Int.natAbs_of_nonneg hnum.le]
    rw [Rat.mul_den_eq_num, ← h1, Int.cast_natCast]
  · intro p hp hpd h0
    have := Fact.mk hp
    have h1 : 1 ≤ multiplicity p w.den := one_le_multiplicity_of_dvd w.den_ne_zero hpd
    rw [padicValRat_def, padicValInt,
      multiplicity_eq_zero_of_not_dvd fun h => hnd p hp h hpd] at h0
    omega
  · intro p hp hpn h0
    have := Fact.mk hp
    have h1 : 1 ≤ multiplicity p w.num.natAbs :=
      one_le_multiplicity_of_dvd (Int.natAbs_ne_zero.2 hnum.ne') hpn
    rw [padicValRat_def, padicValInt,
      multiplicity_eq_zero_of_not_dvd fun h => hnd p hp hpn h] at h0
    omega

/-- An integer relation among `log y`, `iπ` and the `Log(1 - r/t)` is a multiplicative relation
among the `1 - r/t` up to two integers, whose prime factors are those of `y`. -/
theorem relationNatB_of_intRel {b : ℕ} (hb : 2 ≤ b) {y : ℚ} (hy : 0 < y)
    (hp : ∀ p : ℕ, p.Prime → padicValRat p y ≠ 0 → p ∣ b) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {z : Option (Option ℂ) → ℤ}
    (hz : (z none : ℂ) * ((Real.log (y : ℝ) : ℝ) : ℂ) + ((z (some none) : ℂ) * (Real.pi * I) +
      ∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / tB b)) = 0) :
    ∃ u v : ℕ, (∀ p : ℕ, p.Prime → p ∣ u → p ∣ b) ∧ (∀ p : ℕ, p.Prime → p ∣ v → p ∣ b) ∧
      IsRelationNatB b u v S (fun r => z (some (some r))) := by
  have hΛ : Complex.exp ((Real.log (y : ℝ) : ℝ) : ℂ) = (y : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hy)]
    push_cast
    rfl
  have h1 : ∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / tB b) =
      -(z (some none) : ℂ) * (Real.pi * I) +
        ((-z none : ℤ) : ℂ) * ((Real.log (y : ℝ) : ℝ) : ℂ) := by
    rw [Int.cast_neg]
    linear_combination hz
  have hexp : Complex.exp (∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / tB b)) =
      ∏ r ∈ S, (1 - r / tB b) ^ (z (some (some r))) := by
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [Complex.exp_int_mul, Complex.exp_log (wB_ne_zero hb (hS r hr))]
  -- the power of `y` as a quotient of integers
  obtain ⟨u, v, huv, hu, hv⟩ := exists_nat_quot (w := y ^ (-z none)) (zpow_pos hy _)
  have hval : ∀ p : ℕ, p.Prime → padicValRat p (y ^ (-z none)) ≠ 0 → p ∣ b := by
    intro p hpp hne
    have := Fact.mk hpp
    refine hp p hpp fun h0 => hne ?_
    rw [padicValRat.zpow, h0, mul_zero]
  have huv' : (y : ℂ) ^ (-z none) * (u : ℂ) = (v : ℂ) := by exact_mod_cast huv
  refine ⟨u, v, fun p hpp h => hval p hpp (hu p hpp h), fun p hpp h => hval p hpp (hv p hpp h),
    Complex.exp (-(z (some none) : ℂ) * (Real.pi * I)), ?_, ?_⟩
  · refine isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, ?_⟩
    rw [← Complex.exp_nat_mul]
    have e : ((2 : ℕ) : ℂ) * (-(z (some none) : ℂ) * (Real.pi * I)) =
        ((-z (some none) : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  · rw [← hexp, h1, Complex.exp_add, Complex.exp_int_mul _ (-z none), hΛ, mul_assoc, huv']

/-- **No integer relation involves `log y`** (for `b ≥ 5`, `b ≠ 9`, and `y ≠ 1` a positive
rational number all of whose prime factors divide `b`). In an integer relation among `log y`,
`iπ` and the `Log(1 - r/t)`, `r` in a finite set of roots of unity, the coefficient of `log y`
is zero. -/
theorem intRel_none_eq_zeroB {b : ℕ} (hb : 5 ≤ b) (hb9 : b ≠ 9) {y : ℚ} (hy : 0 < y)
    (hy1 : y ≠ 1) (hp : ∀ p : ℕ, p.Prime → padicValRat p y ≠ 0 → p ∣ b) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {v : Option (Option ℂ) → ℂ}
    (hv : v ∈ IntRel (Finset.insertNone (Finset.insertNone S))
      (lamOfBY b ((Real.log (y : ℝ) : ℝ) : ℂ))) : v none = 0 := by
  classical
  have hb2 : 2 ≤ b := by omega
  obtain ⟨z, hz0, hzsum, hvz⟩ := hv
  rw [Finset.sum_insertNone, Finset.sum_insertNone] at hzsum
  have hzsum' : (z none : ℂ) * ((Real.log (y : ℝ) : ℝ) : ℂ) +
      ((z (some none) : ℂ) * (Real.pi * I) +
        ∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / tB b)) = 0 := hzsum
  -- the coefficients vanish outside `S`, and at every root with `r⁴ ≠ 1`
  have hout : ∀ r, r ∉ S → z (some (some r)) = 0 := fun r hr =>
    hz0 _ fun hmem => hr (Finset.some_mem_insertNone.1 (Finset.some_mem_insertNone.1 hmem))
  have hsupp : ∀ r, r ^ 4 ≠ 1 → z (some (some r)) = 0 := by
    intro r hr4
    by_cases hr : r ∈ S
    · obtain ⟨u, w, hu, hw, hrel⟩ := relationNatB_of_intRel hb2 hy hp hS hzsum'
      exact support_subset_fourth_roots_nat hb2 (goodPrimesB hb) hu hw hS hrel r hr hr4
    · exact hout r hr
  -- the sum over `S` reduces to the four roots `1, -1, i, -i`
  obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ,
      f = fun r => (z (some (some r)) : ℂ) * Complex.log (1 - r / tB b) := ⟨_, rfl⟩
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
  have hsum' : ∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / tB b) =
      (z (some (some 1)) : ℂ) * Complex.log (1 - 1 / tB b) +
        (z (some (some (-1))) : ℂ) * Complex.log (1 - (-1) / tB b) +
        (z (some (some I)) : ℂ) * Complex.log (1 - I / tB b) +
        (z (some (some (-I))) : ℂ) * Complex.log (1 - (-I) / tB b) := by
    have := hsum
    rw [hf] at this
    exact this
  rw [hsum'] at hzsum'
  -- real parts
  have hre := congrArg Complex.re hzsum'
  have e1 : ((z (some none) : ℂ) * (Real.pi * I)).re = 0 := by simp
  simp only [Complex.add_re, e1, Base5.re_intCast_mul5, Complex.ofReal_re, log_re_oneB hb2,
    log_re_neg_oneB hb2, log_re_IB, log_re_neg_IB, Complex.zero_re, zero_add] at hre
  have key := log_rat_indepB hb hb9 hy hy1 hp (m := z none) (z₁ := z (some (some 1)))
    (z₂ := z (some (some (-1)))) (s := z (some (some I)) + z (some (some (-I))))
    (by push_cast; linear_combination 2 * hre)
  rw [hvz, key, Int.cast_zero]

/-! ## 2. The theorem -/

/-- **Logarithms of numbers built from the primes of the base** (from Baker's theorem). In a
base `b ≥ 5`, `b ≠ 9`, let `y ≠ 1` be a positive rational number all of whose prime factors
(numerator and denominator) divide `b`. Then `q π + q' log y`, with `q, q'` rational and
`q' ≠ 0`, is not a value of the class `F_b`. -/
theorem not_isFBValue_mul_pi_add_log (hB : BakerTheorem) {b : ℕ} (hb : 5 ≤ b) (hb9 : b ≠ 9)
    {q q' : ℚ} (hq' : q' ≠ 0) {y : ℚ} (hy : 0 < y) (hy1 : y ≠ 1)
    (hp : ∀ p : ℕ, p.Prime → padicValRat p y ≠ 0 → p ∣ b) :
    ¬ IsFBValue b (q * Real.pi + q' * Real.log y) := by
  classical
  rintro ⟨N, ρ, hN, hρ, hsum⟩
  have hb2 : 2 ≤ b := by omega
  -- an even period, and the series as a combination of logarithms
  have hρ2 : ∀ k, ρ (k + 2 * N) = ρ k := fun k => by
    have h2 := periodic_mul hρ 2 k
    rwa [mul_comm] at h2
  have hN2 : 0 < 2 * N := by positivity
  have hS : ∀ r ∈ rootsN (2 * N), IsOfFinOrder r := fun r hr =>
    isOfFinOrder_of_mem_rootsN hN2 hr
  have h1 := (seriesTermB_hasSum_logs hb2 hN2 (Dvd.intro N rfl) hρ2).unique
    (Complex.hasSum_ofReal.2 hsum)
  have hΛ : Complex.exp ((Real.log (y : ℝ) : ℝ) : ℂ) = (y : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hy)]
    push_cast
    rfl
  -- the coefficient vector
  let β : Option (Option ℂ) → ℂ := fun o =>
    match o with
    | none => -(q' : ℂ)
    | some none => I * q
    | some (some r) => if r ∈ rootsN (2 * N) then fourierDB b (2 * N) ρ r else 0
  have hβS : ∀ r ∈ rootsN (2 * N), β (some (some r)) = fourierDB b (2 * N) ρ r :=
    fun r hr => by simp only [β, hr, ↓reduceIte]
  have hF : ∀ x ∈ algebraicClosure ℚ ℂ, IsAlgebraic ℚ x := fun x hx =>
    mem_algebraicClosure_iff.1 hx
  have hspan : SpanIn (algebraicClosure ℚ ℂ)
      (IntRel (Finset.insertNone (Finset.insertNone (rootsN (2 * N))))
        (lamOfBY b ((Real.log (y : ℝ) : ℝ) : ℂ))) β := by
    refine baker_descent hB _ hF (lamOfBY b ((Real.log (y : ℝ) : ℝ) : ℂ)) _ ?_ β ?_ ?_ ?_
    · intro i hi
      rcases i with _ | _ | r
      · change IsAlgebraic ℚ (Complex.exp ((Real.log (y : ℝ) : ℝ) : ℂ))
        rw [hΛ]
        exact isAlgebraic_ratCast ℚ (A := ℂ) y
      · change IsAlgebraic ℚ (Complex.exp (Real.pi * I))
        rw [Complex.exp_pi_mul_I]
        exact isAlgebraic_one.neg
      · exact isAlgebraic_exp_log_wB hb2
          (hS r (Finset.some_mem_insertNone.1 (Finset.some_mem_insertNone.1 hi)))
    · intro i hi
      rcases i with _ | _ | r
      · exact mem_algebraicClosure_iff.2 (isAlgebraic_ratCast ℚ (A := ℂ) q').neg
      · exact mem_algebraicClosure_iff.2 (isAlgebraic_I.mul (isAlgebraic_ratCast ℚ (A := ℂ) q))
      · have hr : r ∈ rootsN (2 * N) :=
          Finset.some_mem_insertNone.1 (Finset.some_mem_insertNone.1 hi)
        rw [hβS r hr]
        exact mem_algebraicClosure_iff.2 (isAlgebraic_fourierDB b (2 * N) ρ (hS r hr))
    · intro i hi
      rcases i with _ | _ | r
      · exact absurd (by simp) hi
      · exact absurd (by simp) hi
      · have hr : r ∉ rootsN (2 * N) := fun hr =>
          hi (Finset.some_mem_insertNone.2 (Finset.some_mem_insertNone.2 hr))
        simp only [β, hr, ↓reduceIte]
    · rw [Finset.sum_insertNone, Finset.sum_insertNone]
      have e : ∑ r ∈ rootsN (2 * N), β (some (some r)) *
          lamOfBY b ((Real.log (y : ℝ) : ℝ) : ℂ) (some (some r)) =
          ∑ r ∈ rootsN (2 * N), fourierDB b (2 * N) ρ r * Complex.log (1 - r / tB b) :=
        Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
      rw [e, h1]
      change -(q' : ℂ) * ((Real.log (y : ℝ) : ℝ) : ℂ) + (I * q * (Real.pi * I) +
        (((q : ℝ) * Real.pi + (q' : ℝ) * Real.log (y : ℝ) : ℝ) : ℂ)) = 0
      push_cast
      linear_combination ((q : ℂ) * Real.pi) * Complex.I_sq
  -- no integer relation involves `log y`, so the coefficient `-q'` is zero
  have h0 := Base3.spanIn_linear (fun v : Option (Option ℂ) → ℂ => v none) rfl
    (fun _ _ _ => rfl) (fun v hv => intRel_none_eq_zeroB hb hb9 hy hy1 hp hS hv) hspan
  have h0' : -(q' : ℂ) = 0 := h0
  exact hq' (by exact_mod_cast neg_eq_zero.1 h0')

/-! ## 3. Corollaries -/

/-- **The logarithm of an integer built from the primes of the base** (from Baker's theorem).
In a base `b ≥ 5`, `b ≠ 9`, if `n ≥ 2` is an integer all of whose prime factors divide `b`,
then `log n` is not a value of the class `F_b`. -/
theorem not_isFBValue_log_nat (hB : BakerTheorem) {b : ℕ} (hb : 5 ≤ b) (hb9 : b ≠ 9) {n : ℕ}
    (hn : 2 ≤ n) (hnb : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ b) : ¬ IsFBValue b (Real.log n) := by
  intro h
  have hy : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
  have hy1 : (n : ℚ) ≠ 1 := by exact_mod_cast (by omega : n ≠ 1)
  refine not_isFBValue_mul_pi_add_log hB hb hb9 (q := 0) (q' := 1) one_ne_zero hy hy1
    (fun p hpp hv => hnb p hpp ?_) ?_
  · by_contra hnd
    apply hv
    rw [padicValRat.of_nat, multiplicity_eq_zero_of_not_dvd hnd, Nat.cast_zero]
  · have e : ((0 : ℚ) : ℝ) * Real.pi + ((1 : ℚ) : ℝ) * Real.log ((n : ℚ) : ℝ) =
        Real.log (n : ℝ) := by
      push_cast
      ring
    rw [e]
    exact h

/-- **`log b` is not a value of the class `F_b`**, for `b ≥ 5`, `b ≠ 9` (from Baker's
theorem). -/
theorem not_isFBValue_log_self (hB : BakerTheorem) {b : ℕ} (hb : 5 ≤ b) (hb9 : b ≠ 9) :
    ¬ IsFBValue b (Real.log b) :=
  not_isFBValue_log_nat hB hb hb9 (by omega) fun _ _ h => h

namespace Unconditional

/-- **Logarithms of numbers built from the primes of the base.** In a base `b ≥ 5`, `b ≠ 9`,
let `y ≠ 1` be a positive rational number all of whose prime factors (numerator and
denominator) divide `b`. Then `q π + q' log y`, with `q, q'` rational and `q' ≠ 0`, is not the
value of any series `∑ ρ(k) b^(-⌊k/2⌋)/k` with `ρ` rational and periodic. -/
theorem not_isFBValue_mul_pi_add_log {b : ℕ} (hb : 5 ≤ b) (hb9 : b ≠ 9) {q q' : ℚ}
    (hq' : q' ≠ 0) {y : ℚ} (hy : 0 < y) (hy1 : y ≠ 1)
    (hp : ∀ p : ℕ, p.Prime → padicValRat p y ≠ 0 → p ∣ b) :
    ¬ IsFBValue b (q * Real.pi + q' * Real.log y) :=
  BaseB.not_isFBValue_mul_pi_add_log bakerTheorem hb hb9 hq' hy hy1 hp

/-- In a base `b ≥ 5`, `b ≠ 9`, if `n ≥ 2` is an integer all of whose prime factors divide
`b`, then `log n` is not a value of the class `F_b`. -/
theorem not_isFBValue_log_nat {b : ℕ} (hb : 5 ≤ b) (hb9 : b ≠ 9) {n : ℕ} (hn : 2 ≤ n)
    (hnb : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ b) : ¬ IsFBValue b (Real.log n) :=
  BaseB.not_isFBValue_log_nat bakerTheorem hb hb9 hn hnb

/-- **`log b` is not the value of any series `∑ ρ(k) b^(-⌊k/2⌋)/k`**, for `b ≥ 5`, `b ≠ 9`. -/
theorem not_isFBValue_log_self {b : ℕ} (hb : 5 ≤ b) (hb9 : b ≠ 9) :
    ¬ IsFBValue b (Real.log b) :=
  BaseB.not_isFBValue_log_self bakerTheorem hb hb9

/-- **Base 10: `log 2` is not a value of the class `F_10`.** -/
theorem not_isFBValue_ten_log_two : ¬ IsFBValue 10 (Real.log 2) := by
  have h := not_isFBValue_log_nat (b := 10) (by norm_num) (by norm_num) (n := 2) le_rfl
    fun p hp h => by
      rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h]
      norm_num
  exact_mod_cast h

/-- **Base 10: `log 5` is not a value of the class `F_10`.** -/
theorem not_isFBValue_ten_log_five : ¬ IsFBValue 10 (Real.log 5) := by
  have h := not_isFBValue_log_nat (b := 10) (by norm_num) (by norm_num) (n := 5)
    (by norm_num) fun p hp h => by
      rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h]
      norm_num
  exact_mod_cast h

/-- **Base 10: `log 10` is not a value of the class `F_10`.** -/
theorem not_isFBValue_ten_log_ten : ¬ IsFBValue 10 (Real.log 10) := by
  have h := not_isFBValue_log_self (b := 10) (by norm_num) (by norm_num)
  exact_mod_cast h

end Unconditional

end BaseB

end PiFormula
