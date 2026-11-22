import Pilean.PiFormula.LogConverse

/-!
# Base 3: the class F3 and its series as combinations of logarithms

The class F3 is the set of series

  `S(ρ) = ∑_{k ≥ 1} ρ(k) 3^(-⌊k/2⌋) / k`,   `ρ` rational and periodic.

With `t = √-3` one has `t² = -3`, so `ρ(k) 3^(-⌊k/2⌋) = c(k) t^(-k)` for the twisted pattern
`c(k) = ρ(k) t^(k mod 2) (-1)^⌊k/2⌋`, of period `lcm(N, 4)`. As in base 2
(`Fourier.lean`, where `t = 1 + i` and `t² = 2i`), finite Fourier inversion gives

  `S(ρ) = ∑_{r^N = 1} d_r Log(1 - r/t)`                      (`series_eq_logs3`).

This file also proves that the values of F3 form a vector space over `ℚ` (`f3Values`), and
the form of Baker's theorem used for logarithms (`baker_no_extra3`), which is `baker_no_extra`
of `Arctan.lean` with `√-3` in place of `1 + i`.
-/

open Complex

namespace PiFormula

namespace Base3

/-! ## 1. `t = √-3` -/

/-- `t = √-3 = i√3`. -/
noncomputable def t3 : ℂ := I * ((Real.sqrt 3 : ℝ) : ℂ)

theorem sqrt3_sq : (((Real.sqrt 3 : ℝ) : ℂ)) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem t3_sq : t3 ^ 2 = -3 := by
  rw [t3, mul_pow, Complex.I_sq, sqrt3_sq]
  ring

theorem norm_t3 : ‖t3‖ = Real.sqrt 3 := by
  rw [t3, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg 3)]

theorem one_lt_norm_t3 : 1 < ‖t3‖ := by
  rw [norm_t3, Real.lt_sqrt (by norm_num)]
  norm_num

theorem t3_ne_zero : t3 ≠ 0 := by
  intro h
  have h1 := one_lt_norm_t3
  rw [h, norm_zero] at h1
  linarith

theorem log_norm_t3 : Real.log ‖t3‖ = Real.log 3 / 2 := by
  rw [norm_t3, Real.log_sqrt (by norm_num)]

theorem isAlgebraic_sqrt3 : IsAlgebraic ℚ (((Real.sqrt 3 : ℝ) : ℂ)) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C 3, ?_, ?_⟩
  · intro h
    have h0 := congrArg (Polynomial.eval 0) h
    simp at h0
  · simp [sqrt3_sq]

theorem isAlgebraic_t3 : IsAlgebraic ℚ t3 := isAlgebraic_I.mul isAlgebraic_sqrt3

theorem t3_sub_ne_zero {r : ℂ} (hr : ‖r‖ = 1) : t3 - r ≠ 0 := by
  intro h
  have h1 : t3 = r := sub_eq_zero.1 h
  have h2 := one_lt_norm_t3
  rw [h1, hr] at h2
  exact lt_irrefl _ h2

theorem norm_div_t3_lt {r : ℂ} (hr : ‖r‖ = 1) : ‖r / t3‖ < 1 := by
  rw [norm_div, hr]
  exact (div_lt_one (by linarith [one_lt_norm_t3])).2 one_lt_norm_t3

theorem w3_ne_zero {r : ℂ} (hr : IsOfFinOrder r) : 1 - r / t3 ≠ 0 := by
  rw [show 1 - r / t3 = (t3 - r) / t3 by rw [sub_div, div_self t3_ne_zero]]
  exact div_ne_zero (t3_sub_ne_zero (norm_root hr)) t3_ne_zero

/-! ## 2. The class F3 -/

/-- The `k`-th term of the series of the class F3. -/
noncomputable def seriesTerm3 (ρ : ℕ → ℚ) (k : ℕ) : ℝ := (ρ k : ℝ) / 3 ^ (k / 2) / k

/-- `x` is the value of a series of the class F3: `x = ∑ ρ(k) 3^(-⌊k/2⌋)/k` for some rational
periodic pattern `ρ`. -/
def IsF3Value (x : ℝ) : Prop :=
  ∃ (N : ℕ) (ρ : ℕ → ℚ), 0 < N ∧ (∀ k, ρ (k + N) = ρ k) ∧ HasSum (seriesTerm3 ρ) x

theorem seriesTerm3_add (ρ ρ' : ℕ → ℚ) (k : ℕ) :
    seriesTerm3 (ρ + ρ') k = seriesTerm3 ρ k + seriesTerm3 ρ' k := by
  simp only [seriesTerm3, Pi.add_apply]
  push_cast
  ring

theorem seriesTerm3_smul (q : ℚ) (ρ : ℕ → ℚ) (k : ℕ) :
    seriesTerm3 (q • ρ) k = q * seriesTerm3 ρ k := by
  simp only [seriesTerm3, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem isF3Value_zero : IsF3Value 0 := by
  refine ⟨1, 0, one_pos, fun _ => rfl, ?_⟩
  have e : seriesTerm3 0 = fun _ => 0 := by
    funext k
    simp [seriesTerm3]
  rw [e]
  exact hasSum_zero

theorem IsF3Value.add {x y : ℝ} (hx : IsF3Value x) (hy : IsF3Value y) : IsF3Value (x + y) := by
  obtain ⟨N, f, hN, hf, hfs⟩ := hx
  obtain ⟨M, g, hM, hg, hgs⟩ := hy
  refine ⟨N * M, f + g, Nat.mul_pos hN hM, fun k => ?_, ?_⟩
  · simp only [Pi.add_apply]
    rw [periodic_mul hf M k, Nat.mul_comm N M, periodic_mul hg N k]
  · have h := hfs.add hgs
    convert h using 1
    funext k
    exact seriesTerm3_add f g k

theorem IsF3Value.const_mul (c : ℚ) {x : ℝ} (hx : IsF3Value x) : IsF3Value (c * x) := by
  obtain ⟨N, f, hN, hf, hfs⟩ := hx
  refine ⟨N, c • f, hN, fun k => by simp only [Pi.smul_apply, hf], ?_⟩
  have h := hfs.mul_left (c : ℝ)
  convert h using 1
  funext k
  exact seriesTerm3_smul c f k

theorem IsF3Value.sub {x y : ℝ} (hx : IsF3Value x) (hy : IsF3Value y) : IsF3Value (x - y) := by
  have h := hx.add (hy.const_mul (-1))
  convert h using 1
  push_cast
  ring

/-- The values of the class F3, as a subspace of `ℝ` over `ℚ`. -/
def f3Values : Submodule ℚ ℝ where
  carrier := {x | IsF3Value x}
  add_mem' := fun hx hy => hx.add hy
  zero_mem' := isF3Value_zero
  smul_mem' := fun c x hx => by
    have h : IsF3Value ((c : ℝ) * x) := IsF3Value.const_mul c hx
    simpa [Rat.smul_def] using h

theorem mem_f3Values {x : ℝ} : x ∈ f3Values ↔ IsF3Value x := Iff.rfl

/-! ## 3. The twisted pattern and the series as a combination of logarithms -/

/-- `c(k) = ρ(k) t^(k mod 2) (-1)^⌊k/2⌋`, so that `ρ(k) 3^(-⌊k/2⌋) = c(k) t^(-k)`. -/
noncomputable def twist3 (ρ : ℕ → ℚ) (k : ℕ) : ℂ := (ρ k : ℂ) * (t3 ^ (k % 2) * (-1) ^ (k / 2))

theorem t3_inv_pow_mul (m e : ℕ) : t3⁻¹ ^ (2 * m + e) * (t3 ^ e * (-1) ^ m) = 1 / 3 ^ m := by
  have h1 : t3⁻¹ ^ e * t3 ^ e = 1 := by rw [← mul_pow, inv_mul_cancel₀ t3_ne_zero, one_pow]
  have h2 : t3⁻¹ ^ 2 * (-1) = 1 / 3 := by
    rw [inv_pow, t3_sq]
    norm_num
  calc t3⁻¹ ^ (2 * m + e) * (t3 ^ e * (-1) ^ m)
      = (t3⁻¹ ^ 2 * (-1)) ^ m * (t3⁻¹ ^ e * t3 ^ e) := by rw [pow_add, pow_mul, mul_pow]; ring
    _ = 1 / 3 ^ m := by rw [h1, h2, mul_one, div_pow, one_pow]

theorem twist3_mul (ρ : ℕ → ℚ) (k : ℕ) : twist3 ρ k * t3⁻¹ ^ k = (ρ k : ℂ) / 3 ^ (k / 2) := by
  have h := t3_inv_pow_mul (k / 2) (k % 2)
  rw [Nat.div_add_mod] at h
  rw [twist3, mul_assoc, mul_comm (t3 ^ (k % 2) * (-1) ^ (k / 2)), h]
  ring

theorem twist3_periodic {N : ℕ} (h4 : 4 ∣ N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) (k : ℕ) :
    twist3 ρ (k + N) = twist3 ρ k := by
  obtain ⟨n, rfl⟩ := h4
  have h1 : (k + 4 * n) % 2 = k % 2 := by omega
  have h2 : (k + 4 * n) / 2 = k / 2 + 2 * n := by omega
  rw [twist3, twist3, hρ, h1, h2, pow_add, pow_mul]
  norm_num

/-- The coefficient `d_r` of `Log (1 - r/t)` in `S(ρ)`. -/
noncomputable def fourierD3 (N : ℕ) (ρ : ℕ → ℚ) (r : ℂ) : ℂ := -coeffAt N (twist3 ρ) r

/-- **The setting in base 3.** For a rational pattern `ρ` of period `N` (`4 ∣ N`),
`S(ρ) = ∑_k ρ(k) 3^(-⌊k/2⌋) / k = ∑_{r^N = 1} d_r Log(1 - r/t)`, `t = √-3`. -/
theorem series_eq_logs3 {N : ℕ} (hN : 0 < N) (h4 : 4 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (fun k : ℕ => (ρ k : ℂ) / 3 ^ (k / 2) / k)
      (∑ r ∈ rootsN N, fourierD3 N ρ r * Complex.log (1 - r / t3)) := by
  rw [sum_rootsN hN]
  have hc := twist3_periodic h4 hρ
  have hterm : ∀ a ∈ Finset.range N,
      HasSum (fun k : ℕ => fourierD3 N ρ (zetaN N ^ a) * -((zetaN N ^ a / t3) ^ k / k))
        (fourierD3 N ρ (zetaN N ^ a) * Complex.log (1 - zetaN N ^ a / t3)) := by
    intro a _
    have hr : ‖zetaN N ^ a‖ = 1 := norm_root (isOfFinOrder_zetaN_pow hN a)
    have h := (hasSum_taylorSeries_neg_log (norm_div_t3_lt hr)).neg
    rw [neg_neg] at h
    exact h.mul_left _
  have hfun : (fun k : ℕ => (ρ k : ℂ) / 3 ^ (k / 2) / k) = fun k : ℕ =>
      ∑ a ∈ Finset.range N, fourierD3 N ρ (zetaN N ^ a) * -((zetaN N ^ a / t3) ^ k / k) := by
    funext k
    have e : ∑ a ∈ Finset.range N,
        fourierD3 N ρ (zetaN N ^ a) * -((zetaN N ^ a / t3) ^ k / k) =
        (∑ a ∈ Finset.range N, coeffAt N (twist3 ρ) (zetaN N ^ a) * (zetaN N ^ a) ^ k)
          * t3⁻¹ ^ k / k := by
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [fourierD3]
      ring
    rw [e, fourier_inversion hN hc k, twist3_mul]
  rw [hfun]
  exact hasSum_sum hterm

/-- The coefficients `d_r` are algebraic numbers. -/
theorem isAlgebraic_fourierD3 (N : ℕ) (ρ : ℕ → ℚ) {r : ℂ} (hr : IsOfFinOrder r) :
    IsAlgebraic ℚ (fourierD3 N ρ r) := by
  rw [fourierD3, coeffAt]
  refine IsAlgebraic.neg (IsAlgebraic.mul ?_ (isAlgebraic_sum' _ _ fun m _ => ?_))
  · rw [one_div]
    exact (isAlgebraic_natCast N).inv
  · refine IsAlgebraic.mul ?_ ((isAlgebraic_root hr).inv.pow m)
    rw [twist3]
    exact IsAlgebraic.mul (isAlgebraic_ratCast ℚ (A := ℂ) (ρ m))
      ((isAlgebraic_t3.pow _).mul ((isAlgebraic_one.neg).pow _))

/-! ## 4. Relations up to a power of a rational number, and Baker's theorem -/

/-- A multiplicative relation among the `1 - r/t` up to a power of `a / b`. -/
def IsRel3 (a b : ℂ) (S : Finset ℂ) (e : ℂ → ℤ) (m : ℤ) : Prop :=
  ∃ ξ : ℂ, IsOfFinOrder ξ ∧ ∏ r ∈ S, (1 - r / t3) ^ (e r) = ξ * (a / b) ^ m

/-- The cleared form of a relation: no denominators and no negative exponents. -/
theorem cleared3 {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ} (h : IsRel3 a b S e m) :
    ∃ ξ : ℂ, IsOfFinOrder ξ ∧
      (∏ r ∈ S, (t3 - r) ^ (e r).toNat) * t3 ^ (∑ r ∈ S, (-e r).toNat) *
          (a ^ (-m).toNat * b ^ m.toNat) =
        ξ * (∏ r ∈ S, (t3 - r) ^ (-e r).toNat) * t3 ^ (∑ r ∈ S, (e r).toNat) *
          (a ^ m.toNat * b ^ (-m).toNat) := by
  obtain ⟨ξ, hξ, hrel⟩ := h
  refine ⟨ξ, hξ, ?_⟩
  -- each factor: (1 - r/t)^e (t - r)^(-e)⁺ t^(e⁺) = (t - r)^(e⁺) t^((-e)⁺)
  have hfac : ∀ r ∈ S, (1 - r / t3) ^ (e r) * ((t3 - r) ^ (-e r).toNat * t3 ^ (e r).toNat) =
      (t3 - r) ^ (e r).toNat * t3 ^ (-e r).toNat := by
    intro r hr
    have hne : t3 - r ≠ 0 := t3_sub_ne_zero (norm_root (hS r hr))
    have hw : 1 - r / t3 = (t3 - r) / t3 := by rw [sub_div, div_self t3_ne_zero]
    have hz1 : (t3 - r) ^ (e r) = (t3 - r) ^ (e r).toNat / (t3 - r) ^ (-e r).toNat := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hne]
      congr 1
      omega
    have hz2 : t3 ^ (e r) = t3 ^ (e r).toNat / t3 ^ (-e r).toNat := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ t3_ne_zero]
      congr 1
      omega
    have h1 : (t3 - r) ^ (-e r).toNat ≠ 0 := pow_ne_zero _ hne
    have h2 : t3 ^ (-e r).toNat ≠ 0 := pow_ne_zero _ t3_ne_zero
    have h3 : t3 ^ (e r).toNat ≠ 0 := pow_ne_zero _ t3_ne_zero
    rw [hw, div_zpow, hz1, hz2]
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
  calc (∏ r ∈ S, (t3 - r) ^ (e r).toNat) * t3 ^ (∑ r ∈ S, (-e r).toNat) *
        (a ^ (-m).toNat * b ^ m.toNat)
      = (ξ * (a / b) ^ m * ((∏ r ∈ S, (t3 - r) ^ (-e r).toNat) *
          t3 ^ (∑ r ∈ S, (e r).toNat))) * (a ^ (-m).toNat * b ^ m.toNat) := by rw [hprod]
    _ = ξ * (∏ r ∈ S, (t3 - r) ^ (-e r).toNat) * t3 ^ (∑ r ∈ S, (e r).toNat) *
          ((a / b) ^ m * (a ^ (-m).toNat * b ^ m.toNat)) := by ring
    _ = ξ * (∏ r ∈ S, (t3 - r) ^ (-e r).toNat) * t3 ^ (∑ r ∈ S, (e r).toNat) *
          (a ^ m.toNat * b ^ (-m).toNat) := by rw [hz]

/-- The logarithms: `Λ` at `none`, `iπ` at `some none`, and the `Log(1 - r/t)`. -/
noncomputable def lam3 (Λ : ℂ) : Option (Option ℂ) → ℂ
  | none => Λ
  | some none => Real.pi * I
  | some (some r) => Complex.log (1 - r / t3)

/-- An integer relation among `Λ`, `iπ` and the `Log(1 - r/t)`, where `exp Λ = a / b`, is a
multiplicative relation among the `1 - r/t` up to a power of `a / b`. -/
theorem rel3_of_intRel {a b Λ : ℂ} (hΛ : Complex.exp Λ = a / b) {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {z : Option (Option ℂ) → ℤ}
    (hz : ∑ i ∈ Finset.insertNone (Finset.insertNone S), (z i : ℂ) * lam3 Λ i = 0) :
    IsRel3 a b S (fun r => z (some (some r))) (-z none) := by
  rw [Finset.sum_insertNone, Finset.sum_insertNone] at hz
  have hz' : (z none : ℂ) * Λ + ((z (some none) : ℂ) * (Real.pi * I) +
      ∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / t3)) = 0 := hz
  have h1 : ∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / t3) =
      -(z (some none) : ℂ) * (Real.pi * I) + ((-z none : ℤ) : ℂ) * Λ := by
    rw [Int.cast_neg]
    linear_combination hz'
  have hexp : Complex.exp (∑ r ∈ S, (z (some (some r)) : ℂ) * Complex.log (1 - r / t3)) =
      ∏ r ∈ S, (1 - r / t3) ^ (z (some (some r))) := by
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [Complex.exp_int_mul, Complex.exp_log (w3_ne_zero (hS r hr))]
  refine ⟨Complex.exp (-(z (some none) : ℂ) * (Real.pi * I)), ?_, ?_⟩
  · refine isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, ?_⟩
    rw [← Complex.exp_nat_mul]
    have e : ((2 : ℕ) : ℂ) * (-(z (some none) : ℂ) * (Real.pi * I)) =
        ((-z (some none) : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  · rw [← hexp, h1, Complex.exp_add, Complex.exp_int_mul Λ (-z none), hΛ]

/-- **Baker's theorem with one more logarithm, in base 3.** Let `exp Λ = a / b` be algebraic.
If no multiplicative relation among the `1 - r/t` involves a non-zero power of `a / b`, then
no combination of the `Log(1 - r/t)` with algebraic coefficients is a non-zero algebraic
multiple of `Λ`. -/
theorem baker_no_extra3 (hB : BakerTheorem) {a b Λ : ℂ} (hΛ : Complex.exp Λ = a / b)
    (halg : IsAlgebraic ℚ (a / b))
    (hmul : ∀ S : Finset ℂ, (∀ r ∈ S, IsOfFinOrder r) → ∀ (e : ℂ → ℤ) (m : ℤ),
      IsRel3 a b S e m → m = 0)
    {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {d : ℂ → ℂ}
    (hd : ∀ r ∈ S, IsAlgebraic ℚ (d r)) {q : ℂ} (hq : IsAlgebraic ℚ q)
    (h : ∑ r ∈ S, d r * Complex.log (1 - r / t3) = q * Λ) : q = 0 := by
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
      (IntRel (Finset.insertNone (Finset.insertNone S)) (lam3 Λ)) β := by
    refine baker_descent hB _ hF (lam3 Λ) _ ?_ β ?_ ?_ ?_
    · intro i hi
      rcases i with _ | _ | r
      · change IsAlgebraic ℚ (Complex.exp Λ)
        rw [hΛ]
        exact halg
      · change IsAlgebraic ℚ (Complex.exp (Real.pi * I))
        rw [Complex.exp_pi_mul_I]
        exact isAlgebraic_one.neg
      · have hr : r ∈ S := Finset.some_mem_insertNone.1 (Finset.some_mem_insertNone.1 hi)
        change IsAlgebraic ℚ (Complex.exp (Complex.log (1 - r / t3)))
        rw [Complex.exp_log (w3_ne_zero (hS r hr)), div_eq_mul_inv]
        exact isAlgebraic_one.sub ((isAlgebraic_root (hS r hr)).mul isAlgebraic_t3.inv)
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
      have e : ∑ r ∈ S, β (some (some r)) * lam3 Λ (some (some r)) =
          ∑ r ∈ S, d r * Complex.log (1 - r / t3) :=
        Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
      rw [e, h]
      change -q * Λ + (0 * (Real.pi * I) + q * Λ) = 0
      ring
  have key : ∀ v ∈ IntRel (Finset.insertNone (Finset.insertNone S)) (lam3 Λ), v none = 0 := by
    rintro v ⟨z, -, hzsum, hv⟩
    have h0 := hmul S hS _ _ (rel3_of_intRel hΛ hS hzsum)
    have h1 : z none = 0 := by omega
    rw [hv, h1, Int.cast_zero]
  have hnone : ∀ β' : Option (Option ℂ) → ℂ,
      SpanIn (algebraicClosure ℚ ℂ)
        (IntRel (Finset.insertNone (Finset.insertNone S)) (lam3 Λ)) β' → β' none = 0 := by
    intro β' hβ'
    induction hβ' with
    | zero => rfl
    | step c hc v hv w _ ih =>
      change c * v none + w none = 0
      rw [key v hv, ih, mul_zero, add_zero]
  have h0 : -q = 0 := hnone β hspan
  exact neg_eq_zero.1 h0

end Base3

end PiFormula
