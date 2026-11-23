import Pilean.Base3.Support

/-!
# Base 3: which multiples of `π` are values (from good primes)

**Theorem** (`pi_multiple_of_goodPrimes3`, from Baker's theorem and `GoodPrimes3`). If a
series of the class F3 has value `γ π` with `γ` algebraic, then `γ` is a rational multiple of
`√3`. In particular `π` is not the value of any series of F3
(`not_isF3Value_pi_of_goodPrimes3`).

The proof. Write `S(ρ) = ∑ d_r Log(1 - r/t)`, `t = √-3` (`series_eq_logs3`). By Baker's theorem
the vector `(iγ; d_r)` is a combination, with algebraic coefficients, of integer relations
among `iπ` and the `Log(1 - r/t)` (`baker_descent`). Two linear forms vanish on every integer
relation, hence on that vector:

* the coordinate at a root `r` outside the six exceptional ones (`support_subset_R03`), so
  `d_r = 0` there;
* the imaginary part `v₀ π + ∑ v_r arg(1 - r/t)` (`intRel_im`).

The arguments at the exceptional roots are `π/6, -π/6, 0, 0, -π/6, π/6` for
`1, -1, i, -i, ω, -ω²` (`theta3_one`, ...). So
`γ = (i/6) (d_1 - d_{-1} - d_ω + d_{-ω²})`, and for a rational pattern this is a rational
multiple of `√3` (`fourier_pi_combination`).
-/

open Complex

namespace PiFormula

namespace Base3

/-! ## 1. Integer relations -/

/-- The logarithms: `iπ` at `none`, and the `Log(1 - r/t)`. -/
noncomputable def lamOf3 : Option ℂ → ℂ
  | none => Real.pi * I
  | some r => Complex.log (1 - r / t3)

theorem isAlgebraic_exp_lamOf3 {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) :
    ∀ i ∈ Finset.insertNone S, IsAlgebraic ℚ (Complex.exp (lamOf3 i)) := by
  intro i hi
  rcases i with _ | r
  · change IsAlgebraic ℚ (Complex.exp (Real.pi * I))
    rw [Complex.exp_pi_mul_I]
    exact isAlgebraic_one.neg
  · have hr := hS r (Finset.some_mem_insertNone.1 hi)
    change IsAlgebraic ℚ (Complex.exp (Complex.log (1 - r / t3)))
    rw [Complex.exp_log (w3_ne_zero hr), div_eq_mul_inv]
    exact isAlgebraic_one.sub ((isAlgebraic_root hr).mul isAlgebraic_t3.inv)

/-- An integer relation among `iπ` and the `Log(1 - r/t)` is a multiplicative relation. -/
theorem relation3_of_intRel {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {z : Option ℂ → ℤ}
    (hz : ∑ i ∈ Finset.insertNone S, (z i : ℂ) * lamOf3 i = 0) :
    IsRelation3 S (fun r => z (some r)) := by
  rw [Finset.sum_insertNone] at hz
  have hz' : (z none : ℂ) * (Real.pi * I) +
      ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / t3) = 0 := hz
  have h1 : ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / t3) =
      -(z none : ℂ) * (Real.pi * I) := by linear_combination hz'
  have hexp : Complex.exp (∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / t3)) =
      ∏ r ∈ S, (1 - r / t3) ^ (z (some r)) := by
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [Complex.exp_int_mul, Complex.exp_log (w3_ne_zero (hS r hr))]
  refine ⟨Complex.exp (-(z none : ℂ) * (Real.pi * I)), ?_, ?_⟩
  · refine isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, ?_⟩
    rw [← Complex.exp_nat_mul]
    have e : ((2 : ℕ) : ℂ) * (-(z none : ℂ) * (Real.pi * I)) =
        ((-z none : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  · rw [← hexp, h1]

/-- **Support.** An integer relation vanishes at every root outside the six exceptional
ones. -/
theorem intRel_support (hG : GoodPrimes3) {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {v : Option ℂ → ℂ} (hv : v ∈ IntRel (Finset.insertNone S) lamOf3) {r : ℂ} (hr : r ∈ S)
    (hr0 : r ∉ R03) : v (some r) = 0 := by
  obtain ⟨z, -, hzsum, hvz⟩ := hv
  have h := support_subset_R03 hG hS (relation3_of_intRel hS hzsum) r hr hr0
  have h' : z (some r) = 0 := h
  rw [hvz, h', Int.cast_zero]

/-- The argument of `1 - r/t`. -/
noncomputable def theta3 (r : ℂ) : ℝ := (Complex.log (1 - r / t3)).im

theorem im_intCast_mul (n : ℤ) (w : ℂ) : ((n : ℂ) * w).im = n * w.im := by
  rw [← Complex.ofReal_intCast, Complex.im_ofReal_mul]

/-- **Imaginary parts.** On an integer relation, `v₀ π + ∑ v_r arg(1 - r/t) = 0`. -/
theorem intRel_im {S : Finset ℂ} {v : Option ℂ → ℂ}
    (hv : v ∈ IntRel (Finset.insertNone S) lamOf3) :
    v none * (Real.pi : ℂ) + ∑ r ∈ S, v (some r) * ((theta3 r : ℝ) : ℂ) = 0 := by
  obtain ⟨z, -, hzsum, hvz⟩ := hv
  rw [Finset.sum_insertNone] at hzsum
  have hzsum' : (z none : ℂ) * (Real.pi * I) +
      ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / t3) = 0 := hzsum
  have him := congrArg Complex.im hzsum'
  rw [Complex.add_im, Complex.im_sum, im_intCast_mul, Complex.zero_im] at him
  have e1 : (↑Real.pi * I).im = Real.pi := by simp
  have e2 : ∑ r ∈ S, ((z (some r) : ℂ) * Complex.log (1 - r / t3)).im =
      ∑ r ∈ S, (z (some r) : ℝ) * theta3 r :=
    Finset.sum_congr rfl fun r _ => by rw [im_intCast_mul]; rfl
  rw [e1, e2] at him
  have hC := congrArg (fun x : ℝ => (x : ℂ)) him
  simp only [hvz]
  push_cast at hC
  exact hC

/-- A linear form that vanishes on a set vanishes on its span. -/
theorem spanIn_linear {ι : Type*} {F : IntermediateField ℚ ℂ} {G : Set (ι → ℂ)}
    (φ : (ι → ℂ) → ℂ) (h0 : φ 0 = 0)
    (hlin : ∀ (c : ℂ) (v w : ι → ℂ), φ (fun i => c * v i + w i) = c * φ v + φ w)
    (hG : ∀ v ∈ G, φ v = 0) {β : ι → ℂ} (hβ : SpanIn F G β) : φ β = 0 := by
  induction hβ with
  | zero => exact h0
  | step c hc v hv w _ ih => rw [hlin, hG v hv, ih, mul_zero, add_zero]

/-! ## 2. The arguments at the exceptional roots -/

theorem arg_eq_arctan {z : ℂ} (h : 0 < z.re) : Complex.arg z = Real.arctan (z.im / z.re) := by
  have h1 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h)
  rw [abs_lt] at h1
  rw [← Real.arctan_tan h1.1 h1.2, Complex.tan_arg]

theorem sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

theorem t3_inv : t3⁻¹ = ((-(Real.sqrt 3)⁻¹ : ℝ) : ℂ) * I := by
  rw [t3, mul_inv, Complex.inv_I]
  push_cast
  ring

theorem w_re (r : ℂ) : (1 - r / t3).re = 1 - r.im / Real.sqrt 3 := by
  rw [div_eq_mul_inv, t3_inv, ← mul_assoc, Complex.sub_re, Complex.one_re, Complex.mul_I_re,
    Complex.im_mul_ofReal]
  field_simp

theorem w_im (r : ℂ) : (1 - r / t3).im = r.re / Real.sqrt 3 := by
  rw [div_eq_mul_inv, t3_inv, ← mul_assoc, Complex.sub_im, Complex.one_im, Complex.mul_I_im,
    Complex.re_mul_ofReal]
  field_simp
  ring

/-- `arg(1 - r/t) = arctan((Re r/√3) / (1 - Im r/√3))` when the denominator is positive. -/
theorem theta3_eq {r : ℂ} (h : 0 < 1 - r.im / Real.sqrt 3) :
    theta3 r = Real.arctan (r.re / Real.sqrt 3 / (1 - r.im / Real.sqrt 3)) := by
  rw [theta3, Complex.log_im, arg_eq_arctan (by rw [w_re]; exact h), w_re, w_im]

theorem inv_sqrt3_lt_one : (Real.sqrt 3)⁻¹ < 1 := by
  have h : (1 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  exact inv_lt_one_of_one_lt₀ h

theorem theta3_one : theta3 1 = Real.pi / 6 := by
  rw [theta3_eq (by simp), ← Real.arctan_inv_sqrt_three]
  simp

theorem theta3_neg_one : theta3 (-1) = -(Real.pi / 6) := by
  rw [theta3_eq (by simp), ← Real.arctan_inv_sqrt_three, ← Real.arctan_neg]
  congr 1
  simp
  ring

theorem theta3_I : theta3 I = 0 := by
  have h : (0 : ℝ) < 1 - I.im / Real.sqrt 3 := by
    have := inv_sqrt3_lt_one
    simp only [Complex.I_im, one_div]
    linarith
  rw [theta3_eq h]
  simp

theorem theta3_neg_I : theta3 (-I) = 0 := by
  have h : (0 : ℝ) < 1 - (-I).im / Real.sqrt 3 := by
    have := sqrt3_pos
    simp only [Complex.neg_im, Complex.I_im, neg_div, sub_neg_eq_add, one_div]
    positivity
  rw [theta3_eq h]
  simp

theorem theta3_w3 : theta3 w3 = -(Real.pi / 6) := by
  have hs := sqrt3_pos
  have him : w3.im / Real.sqrt 3 = 1 / 2 := by
    simp only [w3]
    field_simp
  rw [theta3_eq (by rw [him]; norm_num), him, ← Real.arctan_inv_sqrt_three, ← Real.arctan_neg]
  congr 1
  simp only [w3]
  field_simp
  ring

theorem neg_w3_sq_eq : -w3 ^ 2 = ⟨1 / 2, Real.sqrt 3 / 2⟩ := by
  rw [w3_sq]
  apply Complex.ext
  · simp
    norm_num
  · simp

theorem theta3_neg_w3_sq : theta3 (-w3 ^ 2) = Real.pi / 6 := by
  have hs := sqrt3_pos
  rw [neg_w3_sq_eq]
  have him : (⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ).im / Real.sqrt 3 = 1 / 2 := by
    simp only
    field_simp
  rw [theta3_eq (by rw [him]; norm_num), him, ← Real.arctan_inv_sqrt_three]
  congr 1
  simp only
  field_simp
  ring

/-! ## 3. The Fourier coefficients at the four roots that carry `π` -/

theorem eisRe_two_mul (m : ℕ) : eisRe (2 * m) = eisRe m := by
  have h : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have h2 : (2 * m) % 3 = 0 ↔ m % 3 = 0 := by omega
  simp [eisRe, h2]

theorem eisB_two_mul (m : ℕ) : eisB (2 * m) = -eisB m := by
  have h : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rcases (show m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 by omega) with h1 | h1 | h1
  · have h2 : (2 * m) % 3 = 0 := by omega
    simp [eisB, h1, h2]
  · have h2 : (2 * m) % 3 = 2 := by omega
    simp [eisB, h1, h2]
    norm_num
  · have h2 : (2 * m) % 3 = 1 := by omega
    simp [eisB, h1, h2]
    norm_num

theorem w3_pow_eq (e : ℕ) :
    w3 ^ e = ((eisRe e : ℚ) : ℂ) + ((Real.sqrt 3 : ℝ) : ℂ) * ((eisB e : ℚ) : ℂ) * I := by
  obtain ⟨h1, h2⟩ := w3_pow_re_im e
  apply Complex.ext
  · simp [h1]
  · simp [h2]

/-- The rational number `q_m` with `i c(m) (1 - (-1)^m - ω^(2m) + (-1)^m ω^m) = √3 q_m ρ(m)`. -/
def piCoef (m : ℕ) : ℚ :=
  if m % 2 = 0 then -2 * (-1) ^ (m / 2) * eisB m else -(-1) ^ (m / 2) * (2 - 2 * eisRe m)

theorem twist_bracket (m : ℕ) :
    I * (t3 ^ (m % 2) * (-1) ^ (m / 2)) *
        (1 - (-1) ^ m - w3 ^ (2 * m) + (-1) ^ m * w3 ^ m) =
      ((Real.sqrt 3 : ℝ) : ℂ) * ((piCoef m : ℚ) : ℂ) := by
  rw [w3_pow_eq (2 * m), w3_pow_eq m, eisRe_two_mul, eisB_two_mul]
  rcases Nat.even_or_odd m with he | ho
  · have h1 : m % 2 = 0 := Nat.even_iff.1 he
    have hpc : piCoef m = -2 * (-1) ^ (m / 2) * eisB m := by simp [piCoef, h1]
    rw [h1, pow_zero, he.neg_one_pow, hpc]
    push_cast
    linear_combination
      (2 * (-1 : ℂ) ^ (m / 2) * ((Real.sqrt 3 : ℝ) : ℂ) * ((eisB m : ℚ) : ℂ)) * Complex.I_sq
  · have h1 : m % 2 = 1 := Nat.odd_iff.1 ho
    have hpc : piCoef m = -(-1) ^ (m / 2) * (2 - 2 * eisRe m) := by simp [piCoef, h1]
    rw [h1, pow_one, ho.neg_one_pow, hpc, t3]
    push_cast
    linear_combination
      (((Real.sqrt 3 : ℝ) : ℂ) * (-1 : ℂ) ^ (m / 2) * (2 - 2 * ((eisRe m : ℚ) : ℂ))) *
        Complex.I_sq

theorem w3_inv : w3⁻¹ = w3 ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', w3_pow_three]

theorem neg_w3_sq_inv : (-w3 ^ 2)⁻¹ = -w3 := by
  apply inv_eq_of_mul_eq_one_right
  have h := w3_pow_three
  linear_combination h

/-- **The combination that carries `π`.** For a rational pattern,
`i (d_1 - d_{-1} - d_ω + d_{-ω²})` is a rational multiple of `√3`. -/
theorem fourier_pi_combination (N : ℕ) (ρ : ℕ → ℚ) :
    I * (fourierD3 N ρ 1 - fourierD3 N ρ (-1) - fourierD3 N ρ w3 + fourierD3 N ρ (-w3 ^ 2)) =
      ((Real.sqrt 3 : ℝ) : ℂ) *
        (((-(1 / (N : ℚ)) * ∑ m ∈ Finset.range N, ρ m * piCoef m : ℚ)) : ℂ) := by
  have key : ∀ m : ℕ, I * (twist3 ρ m * (1 : ℂ)⁻¹ ^ m - twist3 ρ m * (-1 : ℂ)⁻¹ ^ m -
      twist3 ρ m * w3⁻¹ ^ m + twist3 ρ m * (-w3 ^ 2)⁻¹ ^ m) =
        ((Real.sqrt 3 : ℝ) : ℂ) * ((ρ m * piCoef m : ℚ) : ℂ) := by
    intro m
    have h := twist_bracket m
    rw [inv_one, one_pow, show (-1 : ℂ)⁻¹ = -1 by norm_num, w3_inv, neg_w3_sq_inv, ← pow_mul,
      neg_pow w3 m, twist3]
    push_cast
    linear_combination (ρ m : ℂ) * h
  have e : I * (fourierD3 N ρ 1 - fourierD3 N ρ (-1) - fourierD3 N ρ w3 +
      fourierD3 N ρ (-w3 ^ 2)) =
      -(1 / (N : ℂ)) * ∑ m ∈ Finset.range N, I * (twist3 ρ m * (1 : ℂ)⁻¹ ^ m -
        twist3 ρ m * (-1 : ℂ)⁻¹ ^ m - twist3 ρ m * w3⁻¹ ^ m +
        twist3 ρ m * (-w3 ^ 2)⁻¹ ^ m) := by
    simp only [fourierD3, coeffAt]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
    ring
  rw [e, Finset.sum_congr rfl (fun m _ => key m), ← Finset.mul_sum]
  push_cast
  ring

/-! ## 4. The theorem -/

theorem w3_re : w3.re = -1 / 2 := rfl

theorem neg_w3_sq_re : (-w3 ^ 2).re = 1 / 2 := by rw [neg_w3_sq_eq]

/-- **Which multiples of `π` are values of F3** (from Baker's theorem and good primes). If a
series of the class F3 has value `γ π` with `γ` algebraic, then `γ` is a rational multiple of
`√3`. -/
theorem pi_multiple_of_goodPrimes3 (hB : BakerTheorem) (hG : GoodPrimes3) {N : ℕ} (hN : 0 < N)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTerm3 ρ) (γ * Real.pi)) : ∃ q : ℚ, γ = q * Real.sqrt 3 := by
  classical
  -- a period divisible by 12
  have hρ' : ∀ k, ρ (k + 12 * N) = ρ k := fun k => by
    have h12 := periodic_mul hρ 12 k
    rwa [mul_comm] at h12
  have hN' : 0 < 12 * N := by positivity
  obtain ⟨N', hN'def⟩ : ∃ N', N' = 12 * N := ⟨_, rfl⟩
  rw [← hN'def] at hρ' hN'
  have h4 : 4 ∣ N' := ⟨3 * N, by rw [hN'def]; ring⟩
  set S := rootsN N' with hSdef
  have hS : ∀ r ∈ S, IsOfFinOrder r := fun r hr => isOfFinOrder_of_mem_rootsN hN' hr
  have h1 := series_eq_logs3 hN' h4 hρ'
  have e : (fun k : ℕ => (ρ k : ℂ) / 3 ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTerm3 ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTerm3]
  rw [e] at h1
  have h2 := h1.unique (Complex.hasSum_ofReal.2 h)
  set d := fourierD3 N' ρ with hd
  have hγC : IsAlgebraic ℚ (γ : ℂ) :=
    (isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective).2 hγ
  -- the vector of coefficients
  let β : Option ℂ → ℂ := fun o =>
    match o with
    | none => I * γ
    | some r => if r ∈ S then d r else 0
  have hβS : ∀ r ∈ S, β (some r) = d r := fun r hr => by simp only [β, hr, ↓reduceIte]
  have hF : ∀ x ∈ algebraicClosure ℚ ℂ, IsAlgebraic ℚ x := fun x hx =>
    mem_algebraicClosure_iff.1 hx
  have hspan : SpanIn (algebraicClosure ℚ ℂ) (IntRel (Finset.insertNone S) lamOf3) β := by
    refine baker_descent hB _ hF lamOf3 _ (isAlgebraic_exp_lamOf3 hS) β ?_ ?_ ?_
    · intro i hi
      rcases i with _ | r
      · exact mem_algebraicClosure_iff.2 (isAlgebraic_I.mul hγC)
      · have hr : r ∈ S := Finset.some_mem_insertNone.1 hi
        rw [hβS r hr]
        exact mem_algebraicClosure_iff.2 (isAlgebraic_fourierD3 N' ρ (hS r hr))
    · intro i hi
      rcases i with _ | r
      · exact absurd (by simp) hi
      · have hr : r ∉ S := fun hr => hi (Finset.some_mem_insertNone.2 hr)
        simp only [β, hr, ↓reduceIte]
    · rw [Finset.sum_insertNone]
      have e2 : ∑ r ∈ S, β (some r) * lamOf3 (some r) =
          ∑ r ∈ S, d r * Complex.log (1 - r / t3) :=
        Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
      rw [e2, h2]
      change I * γ * (Real.pi * I) + ((γ * Real.pi : ℝ) : ℂ) = 0
      push_cast
      linear_combination ((γ : ℂ) * Real.pi) * Complex.I_sq
  -- the coefficients vanish outside the exceptional roots
  have hsupp : ∀ r ∈ S, r ∉ R03 → d r = 0 := by
    intro r hr hr0
    have h0 := spanIn_linear (fun v : Option ℂ → ℂ => v (some r)) rfl (fun _ _ _ => rfl)
      (fun v hv => intRel_support hG hS hv hr hr0) hspan
    have h0' : β (some r) = 0 := h0
    rwa [hβS r hr] at h0'
  -- imaginary parts
  have him := spanIn_linear
    (fun v : Option ℂ → ℂ => v none * (Real.pi : ℂ) + ∑ r ∈ S, v (some r) * ((theta3 r : ℝ) : ℂ))
    (by simp)
    (fun c v w => by
      have e3 : ∑ r ∈ S, (c * v (some r) + w (some r)) * ((theta3 r : ℝ) : ℂ) =
          c * ∑ r ∈ S, v (some r) * ((theta3 r : ℝ) : ℂ) +
            ∑ r ∈ S, w (some r) * ((theta3 r : ℝ) : ℂ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring
      simp only [e3]
      ring)
    (fun v hv => intRel_im hv) hspan
  have him' : I * γ * (Real.pi : ℂ) + ∑ r ∈ S, β (some r) * ((theta3 r : ℝ) : ℂ) = 0 := him
  -- the sum over the roots reduces to four terms
  have h1n : (1 : ℂ) ≠ -1 := by norm_num
  have h1w : (1 : ℂ) ≠ w3 := fun h0 => by
    have := congrArg Complex.re h0
    rw [w3_re] at this
    norm_num at this
  have h1v : (1 : ℂ) ≠ -w3 ^ 2 := fun h0 => by
    have := congrArg Complex.re h0
    rw [neg_w3_sq_re] at this
    norm_num at this
  have hnw : (-1 : ℂ) ≠ w3 := fun h0 => by
    have := congrArg Complex.re h0
    rw [w3_re] at this
    norm_num at this
  have hnv : (-1 : ℂ) ≠ -w3 ^ 2 := fun h0 => by
    have := congrArg Complex.re h0
    rw [neg_w3_sq_re] at this
    norm_num at this
  have hwv : w3 ≠ -w3 ^ 2 := fun h0 => by
    have := congrArg Complex.re h0
    rw [neg_w3_sq_re, w3_re] at this
    norm_num at this
  let R4 : Finset ℂ := {1, -1, w3, -w3 ^ 2}
  have hR4S : R4 ⊆ S := by
    intro x hx
    have hx0 : x ∈ R03 := by
      simp only [R4, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    rw [hSdef, mem_rootsN hN', hN'def, pow_mul, pow_twelve_of_mem_R03 hx0, one_pow]
  have hzero : ∀ x ∈ S, x ∉ R4 → β (some x) * ((theta3 x : ℝ) : ℂ) = 0 := by
    intro x hx hx4
    by_cases hx0 : x ∈ R03
    · have hxI : x = I ∨ x = -I := by
        simp only [R4, Finset.mem_insert, Finset.mem_singleton] at hx4
        rcases hx0 with h0 | h0 | h0 | h0 | h0 | h0
        · exact absurd (Or.inl h0) hx4
        · exact absurd (Or.inr (Or.inl h0)) hx4
        · exact Or.inl h0
        · exact Or.inr h0
        · exact absurd (Or.inr (Or.inr (Or.inl h0))) hx4
        · exact absurd (Or.inr (Or.inr (Or.inr h0))) hx4
      rcases hxI with rfl | rfl
      · rw [theta3_I]; simp
      · rw [theta3_neg_I]; simp
    · rw [hβS x hx, hsupp x hx hx0, zero_mul]
  have hsum4 : ∑ r ∈ S, β (some r) * ((theta3 r : ℝ) : ℂ) =
      (Real.pi / 6 : ℂ) * (d 1 - d (-1) - d w3 + d (-w3 ^ 2)) := by
    rw [← Finset.sum_subset hR4S hzero]
    have hm1 : (1 : ℂ) ∉ ({-1, w3, -w3 ^ 2} : Finset ℂ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h0 | h0 | h0)
      · exact h1n h0
      · exact h1w h0
      · exact h1v h0
    have hm2 : (-1 : ℂ) ∉ ({w3, -w3 ^ 2} : Finset ℂ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h0 | h0)
      · exact hnw h0
      · exact hnv h0
    have hm3 : w3 ∉ ({-w3 ^ 2} : Finset ℂ) := by
      simp only [Finset.mem_singleton]
      exact hwv
    rw [show R4 = insert 1 (insert (-1) (insert w3 {-w3 ^ 2})) from rfl,
      Finset.sum_insert hm1, Finset.sum_insert hm2, Finset.sum_insert hm3,
      Finset.sum_singleton, hβS 1 (hR4S (by simp [R4])), hβS (-1) (hR4S (by simp [R4])),
      hβS w3 (hR4S (by simp [R4])), hβS (-w3 ^ 2) (hR4S (by simp [R4])), theta3_one,
      theta3_neg_one, theta3_w3, theta3_neg_w3_sq]
    push_cast
    ring
  rw [hsum4] at him'
  -- conclude
  have hF4 := fourier_pi_combination N' ρ
  obtain ⟨Q, hQ⟩ : ∃ Q : ℚ, Q = -(1 / (N' : ℚ)) * ∑ m ∈ Finset.range N', ρ m * piCoef m :=
    ⟨_, rfl⟩
  rw [← hQ] at hF4
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hγeq : (γ : ℂ) = ((Q / 6 : ℚ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) := by
    have h5 : (γ : ℂ) * (Real.pi : ℂ) =
        (((Q / 6 : ℚ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ)) * (Real.pi : ℂ) := by
      push_cast
      linear_combination (-I) * him' + ((γ : ℂ) * Real.pi) * Complex.I_sq +
        (Real.pi / 6 : ℂ) * hF4
    exact mul_right_cancel₀ hpi h5
  refine ⟨Q / 6, ?_⟩
  exact_mod_cast hγeq

/-- **`π` is not the value of any series of the class F3** (from Baker's theorem and good
primes). More generally a rational multiple `q π` is a value only for `q = 0`. -/
theorem rat_mul_pi_of_goodPrimes3 (hB : BakerTheorem) (hG : GoodPrimes3) {q : ℚ}
    (h : IsF3Value ((q : ℝ) * Real.pi)) : q = 0 := by
  obtain ⟨N, ρ, hN, hρ, hs⟩ := h
  have halg : IsAlgebraic ℚ ((q : ℝ)) := by
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) q
  obtain ⟨q', hq'⟩ := pi_multiple_of_goodPrimes3 hB hG hN hρ halg hs
  by_contra hq0
  have hirr : Irrational (Real.sqrt 3) := Nat.Prime.irrational_sqrt Nat.prime_three
  have hq'0 : q' ≠ 0 := by
    rintro rfl
    rw [Rat.cast_zero, zero_mul] at hq'
    exact hq0 (by exact_mod_cast hq')
  apply hirr
  refine ⟨q / q', ?_⟩
  have hq'R : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'0
  push_cast
  rw [hq']
  field_simp

theorem not_isF3Value_pi_of_goodPrimes3 (hB : BakerTheorem) (hG : GoodPrimes3) :
    ¬ IsF3Value Real.pi := by
  intro h
  have h1 : IsF3Value (((1 : ℚ) : ℝ) * Real.pi) := by simpa using h
  exact one_ne_zero (rat_mul_pi_of_goodPrimes3 hB hG h1)

end Base3

end PiFormula
