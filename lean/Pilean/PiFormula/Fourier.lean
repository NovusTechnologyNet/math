import Pilean.PiFormula.Baker

/-!
# Part III, the setting: `S(ρ)` as a combination of logarithms (milestone M6, second half)

For a rational pattern `ρ` of period `N` (with `8 ∣ N`), the series of the class F is

  `S(ρ) = ∑_{k ≥ 1} ρ(k) 2^(-⌊k/2⌋) / k = ∑_{r^N = 1} d_r Log(1 - r/t)`      (`series_eq_logs`),

where `t = 1 + i` and `d_r = -(1/N) ∑_{m < N} c(m) r^(-m)` is, up to sign, the finite Fourier
transform of the twisted pattern `c(k) = ρ(k) t^(k mod 2) i^⌊k/2⌋` (`fourierD`). The proof:

* `ρ(k) 2^(-⌊k/2⌋) = c(k) t^(-k)` (`twist_mul`), and `c` has period `N` (`twist_periodic`);
* Fourier inversion `c(k) = ∑_r coeff(r) r^k` over the `N`-th roots of unity
  (`fourier_inversion`);
* `∑_k (r/t)^k / k = -Log(1 - r/t)` for each root `r`.

Joined with `baker_step1` this gives **Step 1 of Theorem C for the series themselves**
(`series_step1`, `series_step1_real`): from Baker's theorem, if `S(ρ)` is an algebraic multiple
of `π`, then the coefficients `d_r` vanish outside the 24 roots of `R0`, and on `R0` they are a
combination of the 13 relations with algebraic coefficients.
-/

open Complex

namespace PiFormula

/-! ## 1. The twisted pattern -/

/-- `c(k) = ρ(k) t^(k mod 2) i^⌊k/2⌋`, so that `ρ(k) 2^(-⌊k/2⌋) = c(k) t^(-k)`. -/
noncomputable def twist (ρ : ℕ → ℚ) (k : ℕ) : ℂ := (ρ k : ℂ) * (tC ^ (k % 2) * I ^ (k / 2))

theorem tC_inv_pow_mul (m e : ℕ) : tC⁻¹ ^ (2 * m + e) * (tC ^ e * I ^ m) = 1 / 2 ^ m := by
  have h1 : tC⁻¹ ^ e * tC ^ e = 1 := by rw [← mul_pow, inv_mul_cancel₀ tC_ne_zero, one_pow]
  have h2 : tC⁻¹ ^ 2 * I = 1 / 2 := by
    rw [tC_inv_sq]; linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  calc tC⁻¹ ^ (2 * m + e) * (tC ^ e * I ^ m)
      = (tC⁻¹ ^ 2 * I) ^ m * (tC⁻¹ ^ e * tC ^ e) := by rw [pow_add, pow_mul, mul_pow]; ring
    _ = 1 / 2 ^ m := by rw [h1, h2, mul_one, div_pow, one_pow]

theorem twist_mul (ρ : ℕ → ℚ) (k : ℕ) : twist ρ k * tC⁻¹ ^ k = (ρ k : ℂ) / 2 ^ (k / 2) := by
  have h := tC_inv_pow_mul (k / 2) (k % 2)
  rw [Nat.div_add_mod] at h
  rw [twist, mul_assoc, mul_comm (tC ^ (k % 2) * I ^ (k / 2)), h]
  ring

theorem twist_periodic {N : ℕ} (h8 : 8 ∣ N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) (k : ℕ) :
    twist ρ (k + N) = twist ρ k := by
  obtain ⟨n, rfl⟩ := h8
  have h1 : (k + 8 * n) % 2 = k % 2 := by omega
  have h2 : (k + 8 * n) / 2 = k / 2 + 4 * n := by omega
  rw [twist, twist, hρ, h1, h2, pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

theorem periodic_mod {N : ℕ} {c : ℕ → ℂ} (hc : ∀ k, c (k + N) = c k) (k : ℕ) :
    c (k % N) = c k := by
  have h : ∀ q j, c (j + N * q) = c j := by
    intro q
    induction q with
    | zero => intro j; simp
    | succ q ih => intro j; rw [Nat.mul_succ, ← add_assoc, hc, ih]
  have h2 := h (k / N) (k % N)
  rw [Nat.mod_add_div] at h2
  exact h2.symm

/-! ## 2. Finite Fourier inversion -/

/-- `ζ_N = exp(2πi/N)`. -/
noncomputable def zetaN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / N)

theorem zetaN_prim {N : ℕ} (hN : 0 < N) : IsPrimitiveRoot (zetaN N) N :=
  Complex.isPrimitiveRoot_exp N hN.ne'

/-- The Fourier coefficient of a pattern `c` of period `N` at the root of unity `r`. -/
noncomputable def coeffAt (N : ℕ) (c : ℕ → ℂ) (r : ℂ) : ℂ :=
  1 / N * ∑ m ∈ Finset.range N, c m * r⁻¹ ^ m

theorem geom_sum_root {N : ℕ} {u : ℂ} (hu : u ^ N = 1) :
    ∑ a ∈ Finset.range N, u ^ a = if u = 1 then (N : ℂ) else 0 := by
  split_ifs with h
  · rw [h]; simp
  · rw [geom_sum_eq h, hu, sub_self, zero_div]

/-- **Fourier inversion** on `ℤ/N`: `c(k) = ∑_{a < N} coeff(ζ^a) (ζ^a)^k`. -/
theorem fourier_inversion {N : ℕ} (hN : 0 < N) {c : ℕ → ℂ} (hc : ∀ k, c (k + N) = c k)
    (k : ℕ) :
    ∑ a ∈ Finset.range N, coeffAt N c (zetaN N ^ a) * (zetaN N ^ a) ^ k = c k := by
  have hζ := zetaN_prim hN
  have hζ0 : zetaN N ≠ 0 := hζ.ne_zero hN.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hmod : ∀ k, zetaN N ^ (k % N) = zetaN N ^ k := fun k => by
    have h := pow_mod_orderOf (zetaN N) k
    rwa [← hζ.eq_orderOf] at h
  -- swap the two sums
  have e1 : ∑ a ∈ Finset.range N, coeffAt N c (zetaN N ^ a) * (zetaN N ^ a) ^ k =
      1 / N * ∑ m ∈ Finset.range N,
        c m * ∑ a ∈ Finset.range N, (zetaN N ^ k * (zetaN N)⁻¹ ^ m) ^ a := by
    simp only [coeffAt, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  -- the inner sum is `N` at `m = k mod N` and `0` elsewhere
  have e2 : ∀ m ∈ Finset.range N,
      ∑ a ∈ Finset.range N, (zetaN N ^ k * (zetaN N)⁻¹ ^ m) ^ a =
        if m = k % N then (N : ℂ) else 0 := by
    intro m hm
    have hu : (zetaN N ^ k * (zetaN N)⁻¹ ^ m) ^ N = 1 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k N, mul_comm m N, pow_mul, pow_mul, inv_pow,
        hζ.pow_eq_one, inv_one, one_pow, one_pow, one_mul]
    have hiff : zetaN N ^ k * (zetaN N)⁻¹ ^ m = 1 ↔ m = k % N := by
      constructor
      · intro h
        have h1 : zetaN N ^ k = zetaN N ^ m := by
          have h' := congrArg (· * zetaN N ^ m) h
          simp only [one_mul] at h'
          rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hζ0, one_pow, mul_one] at h'
          exact h'
        rw [← hmod k] at h1
        exact (hζ.pow_inj (Nat.mod_lt k hN) (Finset.mem_range.1 hm) h1).symm
      · rintro rfl
        rw [← hmod k, ← mul_pow, mul_inv_cancel₀ hζ0, one_pow]
    rw [geom_sum_root hu]
    simp only [hiff]
  rw [e1, Finset.sum_congr rfl fun m hm => by rw [e2 m hm]]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range, Nat.mod_lt k hN,
    ↓reduceIte]
  rw [periodic_mod hc]
  field_simp

/-! ## 3. The series as a combination of logarithms -/

/-- The coefficient `d_r` of `Log (1 - r/t)` in `S(ρ)`. -/
noncomputable def fourierD (N : ℕ) (ρ : ℕ → ℚ) (r : ℂ) : ℂ := -coeffAt N (twist ρ) r

/-- The `N`-th roots of unity, as the powers of `ζ_N`. -/
noncomputable def rootsN (N : ℕ) : Finset ℂ := (Finset.range N).image fun a => zetaN N ^ a

theorem sum_rootsN {N : ℕ} (hN : 0 < N) (f : ℂ → ℂ) :
    ∑ r ∈ rootsN N, f r = ∑ a ∈ Finset.range N, f (zetaN N ^ a) := by
  rw [rootsN, Finset.sum_image]
  intro i hi j hj h
  exact (zetaN_prim hN).pow_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h

theorem isOfFinOrder_zetaN_pow {N : ℕ} (hN : 0 < N) (a : ℕ) : IsOfFinOrder (zetaN N ^ a) :=
  isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, by
    rw [← pow_mul, mul_comm, pow_mul, (zetaN_prim hN).pow_eq_one, one_pow]⟩

theorem isOfFinOrder_of_mem_rootsN {N : ℕ} (hN : 0 < N) {r : ℂ} (hr : r ∈ rootsN N) :
    IsOfFinOrder r := by
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hr
  exact isOfFinOrder_zetaN_pow hN a

/-- `r ∈ rootsN N` iff `r^N = 1`. -/
theorem mem_rootsN {N : ℕ} (hN : 0 < N) {r : ℂ} : r ∈ rootsN N ↔ r ^ N = 1 := by
  have : NeZero N := ⟨hN.ne'⟩
  constructor
  · intro hr
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hr
    rw [← pow_mul, mul_comm, pow_mul, (zetaN_prim hN).pow_eq_one, one_pow]
  · intro hr
    obtain ⟨a, ha, rfl⟩ := (zetaN_prim hN).eq_pow_of_pow_eq_one hr
    exact Finset.mem_image.2 ⟨a, Finset.mem_range.2 ha, rfl⟩

/-- **The setting of Part III.** For a rational pattern `ρ` of period `N` (`8 ∣ N`),
`S(ρ) = ∑_k ρ(k) 2^(-⌊k/2⌋) / k = ∑_{r^N = 1} d_r Log(1 - r/t)`. -/
theorem series_eq_logs {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (fun k : ℕ => (ρ k : ℂ) / 2 ^ (k / 2) / k)
      (∑ r ∈ rootsN N, fourierD N ρ r * Complex.log (1 - r / tC)) := by
  rw [sum_rootsN hN]
  have hc := twist_periodic h8 hρ
  have hterm : ∀ a ∈ Finset.range N,
      HasSum (fun k : ℕ => fourierD N ρ (zetaN N ^ a) * -((zetaN N ^ a / tC) ^ k / k))
        (fourierD N ρ (zetaN N ^ a) * Complex.log (1 - zetaN N ^ a / tC)) := by
    intro a _
    have hr : ‖zetaN N ^ a‖ = 1 := norm_root (isOfFinOrder_zetaN_pow hN a)
    have h := (hasSum_taylorSeries_neg_log (norm_div_tC_lt hr)).neg
    rw [neg_neg] at h
    exact h.mul_left _
  have hfun : (fun k : ℕ => (ρ k : ℂ) / 2 ^ (k / 2) / k) = fun k : ℕ =>
      ∑ a ∈ Finset.range N, fourierD N ρ (zetaN N ^ a) * -((zetaN N ^ a / tC) ^ k / k) := by
    funext k
    have e : ∑ a ∈ Finset.range N, fourierD N ρ (zetaN N ^ a) * -((zetaN N ^ a / tC) ^ k / k) =
        (∑ a ∈ Finset.range N, coeffAt N (twist ρ) (zetaN N ^ a) * (zetaN N ^ a) ^ k)
          * tC⁻¹ ^ k / k := by
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [fourierD]
      ring
    rw [e, fourier_inversion hN hc k, twist_mul]
  rw [hfun]
  exact hasSum_sum hterm

/-! ## 4. Step 1 for the series -/

theorem isAlgebraic_sum' {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, IsAlgebraic ℚ (f i)) : IsAlgebraic ℚ (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun x => IsAlgebraic ℚ x) (fun _ _ ha hb => ha.add hb)
    isAlgebraic_zero h

/-- The coefficients `d_r` are algebraic numbers. -/
theorem isAlgebraic_fourierD (N : ℕ) (ρ : ℕ → ℚ) {r : ℂ} (hr : IsOfFinOrder r) :
    IsAlgebraic ℚ (fourierD N ρ r) := by
  rw [fourierD, coeffAt]
  refine IsAlgebraic.neg (IsAlgebraic.mul ?_ (isAlgebraic_sum' _ _ fun m _ => ?_))
  · rw [one_div]
    exact (isAlgebraic_natCast N).inv
  · refine IsAlgebraic.mul ?_ ((isAlgebraic_root hr).inv.pow m)
    rw [twist]
    exact IsAlgebraic.mul (isAlgebraic_ratCast ℚ (A := ℂ) (ρ m))
      ((isAlgebraic_tC.pow _).mul (isAlgebraic_I.pow _))

/-- **Step 1 of Theorem C for the series (from Baker's theorem).** Let `ρ` be a rational pattern
of period `N` (`8 ∣ N`) whose series `∑ ρ(k) 2^(-⌊k/2⌋)/k` is `γ π` with `γ` algebraic. Then its
coefficients `d_r` vanish outside the 24 roots of `R0`, and on `R0` they are a combination of
the 13 relations with algebraic coefficients. -/
theorem series_step1 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℂ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (fun k : ℕ => (ρ k : ℂ) / 2 ^ (k / 2) / k) (γ * Real.pi)) :
    InSpan13 (rootsN N) (fourierD N ρ) :=
  baker_step1 hB (fun _ hr => isOfFinOrder_of_mem_rootsN hN hr)
    (fun _ hr => isAlgebraic_fourierD N ρ (isOfFinOrder_of_mem_rootsN hN hr)) hγ
    ((series_eq_logs hN h8 hρ).unique h)

/-- The same for the real series, in the form of `new_formula_series`. -/
theorem series_step1_real (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (fun k : ℕ => (ρ k : ℝ) / 2 ^ (k / 2) / k) (γ * Real.pi)) :
    InSpan13 (rootsN N) (fourierD N ρ) := by
  refine series_step1 hB hN h8 hρ (γ := (γ : ℂ)) ?_ ?_
  · have h1 : IsAlgebraic ℚ (algebraMap ℝ ℂ γ) := hγ.algebraMap
    exact h1
  · have h2 := Complex.hasSum_ofReal.2 h
    push_cast at h2
    exact h2

theorem rhoNew_periodic (k : ℕ) : rhoNew (k + 120) = rhoNew k := by
  simp only [rhoNew, Nat.add_mod_right]

/-- An instance: the new 7/24 formula. From Baker's theorem, its coefficients `d_r` are a
combination of the 13 relations (and vanish at the other 96 roots of unity of order dividing
120). -/
theorem new_formula_step1 (hB : BakerTheorem) :
    InSpan13 (rootsN 120) (fourierD 120 rhoNew) := by
  refine series_step1_real hB (by norm_num) (by norm_num) rhoNew_periodic
    (γ := ((1 / 4 : ℚ) : ℝ)) (isAlgebraic_ratCast ℚ (A := ℝ) _) ?_
  have e : ((1 / 4 : ℚ) : ℝ) * Real.pi = Real.pi / 4 := by push_cast; ring
  rw [e]
  exact new_formula_series

end PiFormula
