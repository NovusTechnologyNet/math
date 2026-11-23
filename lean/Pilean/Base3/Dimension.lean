import Pilean.Base3.PiTheorem

/-!
# Base 3: every formula for a multiple of `π` is known

F3 is the class of series `S(ρ) = ∑ ρ(k) 3^(-⌊k/2⌋)/k`, `ρ` rational and periodic. This file
classifies the patterns `ρ` whose series is an algebraic multiple of `π`.

Three patterns of period 12 (written for `k = 1, ..., 12`):

* `rhoGregory = (6, 0, -6, 0, 6, 0, -6, 0, 6, 0, -6, 0)`, with `S = π√3`;
* `rhoZ1 = (0, 1, -2, 0, 1, 4, 0, 3, 2, 4, -1, 0)`, with `S = 0`;
* `rhoZ2 = (1, -3, -4, -3, 1, 0, -1, 3, 4, 3, -1, 0)`, with `S = 0`.

Results (from Baker's theorem):

* `exists_coords3`: if `S(ρ) = γ π` with `γ` algebraic, then
  `ρ = a rhoGregory + b rhoZ1 + c rhoZ2` for rational `a, b, c`.
* `hasSum_comb3`: conversely `S(a rhoGregory + b rhoZ1 + c rhoZ2) = a π√3`.
* `theoremC3`: for every `N` divisible by 12, the patterns of period `N` whose series is an
  algebraic multiple of `π` have period 12 and form a space of dimension exactly 3; the zero
  relations form a subspace of dimension exactly 2.

The proof. By Baker's theorem the coefficients `d_r` of `S(ρ) = ∑ d_r Log(1 - r/t)` are a
combination of integer relations among `iπ` and the `Log(1 - r/t)`. Such a relation `z` is
supported on the six exceptional roots `1, -1, i, -i, ω, -ω²` (`support_subset_R03`), and its
real part reads

    A log 2 + B log 3 + C log(2 + √3) = 0,
    A = 2(z_1 + z_{-1}) + z_i + z_{-i},  B = -(z_1 + z_{-1} + z_i + z_{-i} + z_ω + z_{-ω²}),
    C = z_{-i} - z_i,

so `A = B = C = 0` (`log_indep`): `z_i = z_{-i}` and `z_1 + z_{-1} = z_ω + z_{-ω²} = -z_i`.
These three linear conditions pass to the `d_r`, and Fourier inversion turns them into
`ρ = A G + B H + C F` for three explicit rational patterns.
-/

open Complex

namespace PiFormula

namespace Base3

/-! ## 1. The six exceptional roots as a finite set -/

/-- The six exceptional roots. -/
noncomputable def R03fin : Finset ℂ := {1, -1, I, -I, w3, -w3 ^ 2}

theorem mem_R03fin {r : ℂ} : r ∈ R03fin ↔ r ∈ R03 := by
  simp [R03fin, R03]

theorem sum_R03fin {M : Type*} [AddCommMonoid M] (f : ℂ → M) :
    ∑ r ∈ R03fin, f r = f 1 + (f (-1) + (f I + (f (-I) + (f w3 + f (-w3 ^ 2))))) := by
  have hre : ∀ {a b : ℂ}, a.re ≠ b.re → a ≠ b := fun h h' => h (congrArg Complex.re h')
  have him : ∀ {a b : ℂ}, a.im ≠ b.im → a ≠ b := fun h h' => h (congrArg Complex.im h')
  have h1 : (1 : ℂ) ∉ ({-1, I, -I, w3, -w3 ^ 2} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hre (by norm_num), hre (by norm_num), hre (by norm_num),
      hre (by rw [w3_re]; norm_num), hre (by rw [neg_w3_sq_re]; norm_num)⟩
  have h2 : (-1 : ℂ) ∉ ({I, -I, w3, -w3 ^ 2} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hre (by norm_num), hre (by norm_num), hre (by rw [w3_re]; norm_num),
      hre (by rw [neg_w3_sq_re]; norm_num)⟩
  have h3 : I ∉ ({-I, w3, -w3 ^ 2} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨him (by norm_num), hre (by rw [w3_re]; norm_num),
      hre (by rw [neg_w3_sq_re]; norm_num)⟩
  have h4 : -I ∉ ({w3, -w3 ^ 2} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hre (by rw [w3_re]; norm_num), hre (by rw [neg_w3_sq_re]; norm_num)⟩
  have h5 : w3 ∉ ({-w3 ^ 2} : Finset ℂ) := by
    simp only [Finset.mem_singleton]
    exact hre (by rw [w3_re, neg_w3_sq_re]; norm_num)
  rw [R03fin, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
    Finset.sum_insert h4, Finset.sum_insert h5, Finset.sum_singleton]

theorem R03fin_subset_rootsN {N : ℕ} (hN : 0 < N) (h12 : 12 ∣ N) : R03fin ⊆ rootsN N := by
  intro r hr
  obtain ⟨m, rfl⟩ := h12
  rw [mem_rootsN hN, pow_mul, pow_twelve_of_mem_R03 (mem_R03fin.1 hr), one_pow]

/-- A sum over the `N`-th roots of unity of a function that vanishes outside the six
exceptional roots. -/
theorem sum_rootsN_R03 {M : Type*} [AddCommMonoid M] {N : ℕ} (hN : 0 < N) (h12 : 12 ∣ N)
    (f : ℂ → M) (h0 : ∀ r ∈ rootsN N, r ∉ R03 → f r = 0) :
    ∑ r ∈ rootsN N, f r = f 1 + (f (-1) + (f I + (f (-I) + (f w3 + f (-w3 ^ 2))))) := by
  rw [← sum_R03fin]
  exact (Finset.sum_subset (R03fin_subset_rootsN hN h12)
    fun r hr hr' => h0 r hr fun h => hr' (mem_R03fin.2 h)).symm

/-! ## 2. The numbers `log |1 - r/t|` at the six roots -/

/-- `ℓ(r) = log |1 - r/t|`. -/
noncomputable def ell3 (r : ℂ) : ℝ := Real.log ‖1 - r / t3‖

theorem log_eq_ell3_theta3 (r : ℂ) :
    Complex.log (1 - r / t3) = (ell3 r : ℂ) + (theta3 r : ℂ) * I := by
  apply Complex.ext
  · simp [ell3, Complex.log_re]
  · simp [theta3]

theorem two_mul_ell3 (r : ℂ) :
    2 * ell3 r = Real.log ((1 - r.im / Real.sqrt 3) * (1 - r.im / Real.sqrt 3) +
      r.re / Real.sqrt 3 * (r.re / Real.sqrt 3)) := by
  rw [ell3, ← w_re r, ← w_im r, ← Complex.normSq_apply, ← Complex.sq_norm, Real.log_pow]
  push_cast
  ring

theorem inv_sqrt3 : 1 / Real.sqrt 3 = Real.sqrt 3 / 3 := by
  have h := sqrt3_mul_self
  have hs := sqrt3_pos
  field_simp
  linarith

theorem log_four_thirds : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
  rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

theorem two_ell3_one : 2 * ell3 1 = 2 * Real.log 2 - Real.log 3 := by
  rw [two_mul_ell3, ← log_four_thirds]
  congr 1
  have h := sqrt3_mul_self
  have hi := inv_sqrt3
  simp only [Complex.one_im, Complex.one_re, zero_div, sub_zero, mul_one]
  rw [hi]
  nlinarith

theorem two_ell3_neg_one : 2 * ell3 (-1) = 2 * Real.log 2 - Real.log 3 := by
  rw [two_mul_ell3, ← log_four_thirds]
  congr 1
  have h := sqrt3_mul_self
  have hi := inv_sqrt3
  simp only [Complex.neg_im, Complex.one_im, Complex.neg_re, Complex.one_re, neg_zero, zero_div,
    sub_zero, mul_one, neg_div, neg_mul_neg]
  rw [hi]
  nlinarith

theorem two_ell3_w3 : 2 * ell3 w3 = -Real.log 3 := by
  rw [two_mul_ell3, ← Real.log_inv]
  congr 1
  have h := sqrt3_mul_self
  have hs := sqrt3_pos
  have him : w3.im = Real.sqrt 3 / 2 := rfl
  rw [w3_re, him]
  field_simp
  nlinarith

theorem two_ell3_neg_w3_sq : 2 * ell3 (-w3 ^ 2) = -Real.log 3 := by
  rw [two_mul_ell3, ← Real.log_inv]
  congr 1
  have h := sqrt3_mul_self
  have hs := sqrt3_pos
  have him : (-w3 ^ 2).im = Real.sqrt 3 / 2 := by rw [neg_w3_sq_eq]
  rw [neg_w3_sq_re, him]
  field_simp
  nlinarith

theorem two_add_sqrt3_pos : (0 : ℝ) < 2 + Real.sqrt 3 := by
  have := sqrt3_pos
  linarith

theorem two_ell3_I :
    2 * ell3 I = Real.log 2 - Real.log 3 - Real.log (2 + Real.sqrt 3) := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hi := inv_sqrt3
  have hp := two_add_sqrt3_pos
  rw [two_mul_ell3, ← Real.log_div (by norm_num) (by norm_num),
    ← Real.log_div (by norm_num) hp.ne']
  congr 1
  simp only [Complex.I_im, Complex.I_re, zero_div, mul_zero, add_zero]
  rw [eq_div_iff hp.ne', hi]
  linear_combination (Real.sqrt 3 / 9 - 4 / 9) * h

theorem two_ell3_neg_I :
    2 * ell3 (-I) = Real.log 2 - Real.log 3 + Real.log (2 + Real.sqrt 3) := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hi := inv_sqrt3
  have hp := two_add_sqrt3_pos
  rw [two_mul_ell3, ← Real.log_div (by norm_num) (by norm_num),
    ← Real.log_mul (by norm_num) hp.ne']
  congr 1
  simp only [Complex.neg_im, Complex.I_im, Complex.neg_re, Complex.I_re, neg_zero, zero_div,
    mul_zero, add_zero, neg_div, sub_neg_eq_add]
  rw [hi]
  linear_combination (1 / 9 : ℝ) * h

/-! ## 3. `log 2`, `log 3` and `log(2 + √3)` are independent over `ℤ` -/

theorem two_add_sqrt3_pow (n : ℕ) :
    ∃ x y : ℕ, (2 + Real.sqrt 3) ^ n = x + y * Real.sqrt 3 ∧ 0 < x ∧ (0 < n → 0 < y) := by
  induction n with
  | zero => exact ⟨1, 0, by simp, by norm_num, by simp⟩
  | succ n ih =>
    obtain ⟨x, y, h, hx, hy⟩ := ih
    refine ⟨2 * x + 3 * y, x + 2 * y, ?_, by omega, fun _ => by omega⟩
    rw [pow_succ, h]
    push_cast
    linear_combination (y : ℝ) * sqrt3_mul_self

theorem irrational_two_add_sqrt3_zpow {C : ℤ} (hC : C ≠ 0) :
    Irrational ((2 + Real.sqrt 3) ^ C) := by
  have hirr : Irrational (Real.sqrt 3) := Nat.Prime.irrational_sqrt Nat.prime_three
  have key : ∀ n : ℕ, 0 < n → Irrational ((2 + Real.sqrt 3) ^ n) := by
    intro n hn
    obtain ⟨x, y, h, -, hy⟩ := two_add_sqrt3_pow n
    rw [h]
    exact (hirr.natCast_mul (hy hn).ne').natCast_add x
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg C
  · rw [zpow_natCast]
    exact key n (by omega)
  · rw [zpow_neg, zpow_natCast]
    exact (key n (by omega)).inv

theorem two_pow_eq_three_pow {a b : ℕ} (h : 2 ^ a = 3 ^ b) : a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    by_contra ha
    have h2 : 2 ∣ 3 ^ b := h ▸ dvd_pow_self 2 ha
    have := Nat.prime_two.dvd_of_dvd_pow h2
    omega
  subst ha
  refine ⟨rfl, ?_⟩
  by_contra hb
  have : 1 < 3 ^ b := Nat.one_lt_pow hb (by norm_num)
  omega

theorem two_zpow_mul_three_zpow {A B : ℤ} (h : (2 : ℝ) ^ A * 3 ^ B = 1) : A = 0 ∧ B = 0 := by
  have h2 : ∀ n : ℕ, (0 : ℝ) < 2 ^ n := fun n => by positivity
  have h3 : ∀ n : ℕ, (0 : ℝ) < 3 ^ n := fun n => by positivity
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg A <;> obtain ⟨b, rfl | rfl⟩ := Int.eq_nat_or_neg B
  · rw [zpow_natCast, zpow_natCast] at h
    have h' : 2 ^ a * 3 ^ b = 1 := by exact_mod_cast h
    have ha : 2 ^ a = 1 := Nat.eq_one_of_mul_eq_one_right h'
    have hb : 3 ^ b = 1 := Nat.eq_one_of_mul_eq_one_left h'
    obtain ⟨ha', hb'⟩ := two_pow_eq_three_pow (ha.trans hb.symm)
    exact ⟨by simp [ha'], by simp [hb']⟩
  · rw [zpow_natCast, zpow_neg, zpow_natCast, mul_inv_eq_one₀ (h3 b).ne'] at h
    have h' : 2 ^ a = 3 ^ b := by exact_mod_cast h
    obtain ⟨ha', hb'⟩ := two_pow_eq_three_pow h'
    exact ⟨by simp [ha'], by simp [hb']⟩
  · rw [zpow_neg, zpow_natCast, zpow_natCast, inv_mul_eq_one₀ (h2 a).ne'] at h
    have h' : 2 ^ a = 3 ^ b := by exact_mod_cast h
    obtain ⟨ha', hb'⟩ := two_pow_eq_three_pow h'
    exact ⟨by simp [ha'], by simp [hb']⟩
  · rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, ← mul_inv, inv_eq_one] at h
    have h' : 2 ^ a * 3 ^ b = 1 := by exact_mod_cast h
    have ha : 2 ^ a = 1 := Nat.eq_one_of_mul_eq_one_right h'
    have hb : 3 ^ b = 1 := Nat.eq_one_of_mul_eq_one_left h'
    obtain ⟨ha', hb'⟩ := two_pow_eq_three_pow (ha.trans hb.symm)
    exact ⟨by simp [ha'], by simp [hb']⟩

/-- **`log 2`, `log 3` and `log(2 + √3)` are linearly independent over `ℤ`.** -/
theorem log_indep {A B C : ℤ}
    (h : (A : ℝ) * Real.log 2 + B * Real.log 3 + C * Real.log (2 + Real.sqrt 3) = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  have hp := two_add_sqrt3_pos
  have hexp : (2 : ℝ) ^ A * 3 ^ B * (2 + Real.sqrt 3) ^ C = 1 := by
    have hz : ∀ (x : ℝ), 0 < x → ∀ n : ℤ, Real.exp (n * Real.log x) = x ^ n :=
      fun x hx n => by rw [mul_comm, Real.exp_mul, Real.exp_log hx, Real.rpow_intCast]
    have h' := congrArg Real.exp h
    rw [Real.exp_add, Real.exp_add, Real.exp_zero, hz 2 (by norm_num), hz 3 (by norm_num),
      hz _ hp] at h'
    exact h'
  have h2 : (2 : ℝ) ^ A ≠ 0 := zpow_ne_zero _ (by norm_num)
  have h3 : (3 : ℝ) ^ B ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hC : C = 0 := by
    by_contra hC
    apply irrational_two_add_sqrt3_zpow hC
    refine ⟨(2 : ℚ) ^ (-A) * 3 ^ (-B), ?_⟩
    push_cast
    rw [zpow_neg, zpow_neg]
    field_simp
    linarith
  subst hC
  rw [zpow_zero, mul_one] at hexp
  obtain ⟨hA, hB⟩ := two_zpow_mul_three_zpow hexp
  exact ⟨hA, hB, rfl⟩

/-! ## 4. The real part of an integer relation -/

theorem re_intCast_mul (n : ℤ) (w : ℂ) : ((n : ℂ) * w).re = n * w.re := by
  rw [← Complex.ofReal_intCast, Complex.re_ofReal_mul]

/-- **Real parts.** An integer relation among `iπ` and the `Log(1 - r/t)`, `r^N = 1`, has
equal coefficients at `i` and `-i`, and the sums of its coefficients at `1, -1` and at
`ω, -ω²` are both the negative of the coefficient at `i`. -/
theorem intRel_re (hG : GoodPrimes3) {N : ℕ} (hN : 0 < N) (h12 : 12 ∣ N) {v : Option ℂ → ℂ}
    (hv : v ∈ IntRel (Finset.insertNone (rootsN N)) lamOf3) :
    v (some I) = v (some (-I)) ∧ v (some 1) + v (some (-1)) + v (some I) = 0 ∧
      v (some w3) + v (some (-w3 ^ 2)) + v (some I) = 0 := by
  obtain ⟨z, -, hzsum, hvz⟩ := hv
  have hS : ∀ r ∈ rootsN N, IsOfFinOrder r := fun r hr => isOfFinOrder_of_mem_rootsN hN hr
  have hsupp : ∀ r ∈ rootsN N, r ∉ R03 → z (some r) = 0 := fun r hr hr0 =>
    support_subset_R03 hG hS (relation3_of_intRel hS hzsum) r hr hr0
  rw [Finset.sum_insertNone] at hzsum
  have hzsum' : (z none : ℂ) * (Real.pi * I) +
      ∑ r ∈ rootsN N, (z (some r) : ℂ) * Complex.log (1 - r / t3) = 0 := hzsum
  have hre := congrArg Complex.re hzsum'
  rw [Complex.add_re, Complex.re_sum, Complex.zero_re] at hre
  have e1 : ((z none : ℂ) * (Real.pi * I)).re = 0 := by simp
  have e2 : ∑ r ∈ rootsN N, ((z (some r) : ℂ) * Complex.log (1 - r / t3)).re =
      ∑ r ∈ rootsN N, (z (some r) : ℝ) * ell3 r :=
    Finset.sum_congr rfl fun r _ => by rw [re_intCast_mul, Complex.log_re]; rfl
  rw [e1, e2, zero_add, sum_rootsN_R03 hN h12 _
    (fun r hr hr0 => by rw [hsupp r hr hr0]; simp)] at hre
  have key : ((2 * (z (some 1) + z (some (-1))) + z (some I) + z (some (-I)) : ℤ) : ℝ) *
        Real.log 2 +
      ((-(z (some 1) + z (some (-1))) - z (some I) - z (some (-I)) -
        (z (some w3) + z (some (-w3 ^ 2))) : ℤ) : ℝ) * Real.log 3 +
      ((z (some (-I)) - z (some I) : ℤ) : ℝ) * Real.log (2 + Real.sqrt 3) = 0 := by
    push_cast
    linear_combination 2 * hre - (z (some 1) : ℝ) * two_ell3_one -
      (z (some (-1)) : ℝ) * two_ell3_neg_one - (z (some I) : ℝ) * two_ell3_I -
      (z (some (-I)) : ℝ) * two_ell3_neg_I - (z (some w3) : ℝ) * two_ell3_w3 -
      (z (some (-w3 ^ 2)) : ℝ) * two_ell3_neg_w3_sq
  obtain ⟨hA, hB, hC⟩ := log_indep key
  have h1 : z (some I) = z (some (-I)) := by omega
  have h2 : z (some 1) + z (some (-1)) + z (some I) = 0 := by omega
  have h3 : z (some w3) + z (some (-w3 ^ 2)) + z (some I) = 0 := by omega
  simp only [hvz]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

/-! ## 5. A series from the expansion of its twisted pattern -/

/-- If the twisted pattern is `∑ e_i r_i^k` for finitely many numbers `r_i` of absolute
value 1, then `S(ρ) = -∑ e_i Log(1 - r_i/t)`. -/
theorem hasSum_of_twist3 {ρ : ℕ → ℚ} {n : ℕ} (r e : Fin n → ℂ) (hr : ∀ i, ‖r i‖ = 1)
    (h : ∀ k, twist3 ρ k = ∑ i, e i * r i ^ k) :
    HasSum (fun k : ℕ => (ρ k : ℂ) / 3 ^ (k / 2) / k)
      (-∑ i, e i * Complex.log (1 - r i / t3)) := by
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasSum (fun k : ℕ => e i * ((r i / t3) ^ k / k))
        (e i * -Complex.log (1 - r i / t3)) := by
    intro i _
    exact (hasSum_taylorSeries_neg_log (norm_div_t3_lt (hr i))).mul_left _
  have hfun : (fun k : ℕ => (ρ k : ℂ) / 3 ^ (k / 2) / k) =
      fun k : ℕ => ∑ i, e i * ((r i / t3) ^ k / k) := by
    funext k
    rw [← twist3_mul, h k, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow, inv_pow]
    ring
  rw [hfun]
  convert hasSum_sum hterm using 1
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The real form of `hasSum_of_twist3`. -/
theorem hasSum_real_of_twist3 {ρ : ℕ → ℚ} {n : ℕ} (r e : Fin n → ℂ) (hr : ∀ i, ‖r i‖ = 1)
    (h : ∀ k, twist3 ρ k = ∑ i, e i * r i ^ k) {x : ℝ}
    (hx : -∑ i, e i * Complex.log (1 - r i / t3) = (x : ℂ)) : HasSum (seriesTerm3 ρ) x := by
  have h1 := hasSum_of_twist3 r e hr h
  rw [hx] at h1
  have e' : (fun k : ℕ => (ρ k : ℂ) / 3 ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTerm3 ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTerm3]
  rw [e'] at h1
  exact Complex.hasSum_ofReal.1 h1

/-! ## 6. Three patterns and their twisted forms -/

/-- `H = (1, 3, 2, 3, 1, 0, -1, -3, -2, -3, -1, 0)` (for `k = 1, ..., 12`), in closed form. -/
def rhoH (k : ℕ) : ℚ :=
  (-1) ^ (k / 2) * (if k % 2 = 0 then 6 * eisB k else -2 * eisRe k)

/-- `F = (1, -5, 0, -3, -1, -8, -1, -3, 0, -5, 1, 0)` (for `k = 1, ..., 12`), in closed
form. -/
def rhoF (k : ℕ) : ℚ :=
  if k % 2 = 0 then (-1) ^ (k / 2) * (2 + 2 * eisRe k) - 4 else (-1) ^ (k / 2) * (2 * eisB k)

theorem neg_one_pow_half_sq (k : ℕ) : ((-1 : ℂ) ^ (k / 2)) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

theorem t3_def : t3 = I * ((Real.sqrt 3 : ℝ) : ℂ) := rfl

theorem I_pow_split (k : ℕ) : I ^ k = I ^ (k % 2) * (-1) ^ (k / 2) := by
  conv_lhs => rw [← Nat.mod_add_div k 2, pow_add, pow_mul, Complex.I_sq]

/-- `c(k) = 3t (1 - (-1)^k)` for the Gregory pattern. -/
theorem twist3_rhoGregory (k : ℕ) :
    twist3 rhoGregory k = 3 * t3 * 1 ^ k + -(3 * t3) * (-1) ^ k := by
  have hsq := neg_one_pow_half_sq k
  rcases Nat.even_or_odd k with he | ho
  · have h2 : k % 2 ≠ 1 := by have := Nat.even_iff.1 he; omega
    simp [twist3, rhoGregory, h2, he.neg_one_pow]
  · have h1 : k % 2 = 1 := Nat.odd_iff.1 ho
    simp only [twist3, rhoGregory, h1, ↓reduceIte, ho.neg_one_pow, one_pow, pow_one]
    push_cast
    linear_combination (6 * t3) * hsq

/-- `c(k) = -t ω^k + t (-ω²)^k` for `H`. -/
theorem twist3_rhoH (k : ℕ) : twist3 rhoH k = -t3 * w3 ^ k + t3 * (-w3 ^ 2) ^ k := by
  have hsq := neg_one_pow_half_sq k
  have hs := sqrt3_sq
  rw [neg_pow (w3 ^ 2), ← pow_mul, w3_pow_eq (2 * k), w3_pow_eq k, eisRe_two_mul, eisB_two_mul]
  rcases Nat.even_or_odd k with he | ho
  · have h1 : k % 2 = 0 := Nat.even_iff.1 he
    simp only [twist3, rhoH, h1, ↓reduceIte, he.neg_one_pow, pow_zero, one_mul]
    rw [t3_def]
    push_cast
    linear_combination (6 * ((eisB k : ℚ) : ℂ)) * hsq - (2 * ((eisB k : ℚ) : ℂ)) * hs +
      (2 * ((eisB k : ℚ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) ^ 2) * Complex.I_sq
  · have h1 : k % 2 = 1 := Nat.odd_iff.1 ho
    simp only [twist3, rhoH, ho.neg_one_pow, h1, pow_one]
    push_cast
    linear_combination (-2 * ((eisRe k : ℚ) : ℂ) * t3) * hsq

/-- `c(k) = 1 + (-1)^k - 2 i^k - 2 (-i)^k + ω^k + (-ω²)^k` for `F`. -/
theorem twist3_rhoF (k : ℕ) :
    twist3 rhoF k =
      1 * 1 ^ k + 1 * (-1) ^ k + -2 * I ^ k + -2 * (-I) ^ k + 1 * w3 ^ k +
        1 * (-w3 ^ 2) ^ k := by
  have hsq := neg_one_pow_half_sq k
  rw [neg_pow (w3 ^ 2), ← pow_mul, w3_pow_eq (2 * k), w3_pow_eq k, eisRe_two_mul, eisB_two_mul,
    neg_pow I, I_pow_split k]
  rcases Nat.even_or_odd k with he | ho
  · have h1 : k % 2 = 0 := Nat.even_iff.1 he
    simp only [twist3, rhoF, h1, ↓reduceIte, he.neg_one_pow, pow_zero, one_mul, one_pow]
    push_cast
    linear_combination (2 + 2 * ((eisRe k : ℚ) : ℂ)) * hsq
  · have h1 : k % 2 = 1 := Nat.odd_iff.1 ho
    simp only [twist3, rhoF, ho.neg_one_pow, h1, pow_one, one_pow]
    push_cast
    linear_combination (2 * ((eisB k : ℚ) : ℂ) * t3) * hsq +
      (2 * ((eisB k : ℚ) : ℂ)) * t3_def

/-! ## 7. The values of the three series -/

theorem norm_w3 : ‖w3‖ = 1 :=
  norm_root (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, w3_pow_three⟩)

theorem norm_neg_w3_sq : ‖-w3 ^ 2‖ = 1 := by
  rw [norm_neg, norm_pow, norm_w3, one_pow]

/-- `S(H) = π√3 / 3`. -/
theorem hasSum_rhoH : HasSum (seriesTerm3 rhoH) (Real.pi * Real.sqrt 3 / 3) := by
  refine hasSum_real_of_twist3 ![w3, -w3 ^ 2] ![-t3, t3] ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact norm_w3
    · exact norm_neg_w3_sq
  · intro k
    rw [twist3_rhoH, Fin.sum_univ_two]
    rfl
  · have hl : ell3 w3 = ell3 (-w3 ^ 2) := by
      linarith [two_ell3_w3, two_ell3_neg_w3_sq]
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [log_eq_ell3_theta3, log_eq_ell3_theta3, theta3_w3, theta3_neg_w3_sq, hl, t3_def]
    push_cast
    linear_combination (-(Real.pi * ((Real.sqrt 3 : ℝ) : ℂ) / 3)) * Complex.I_sq

/-- `S(F) = 0`. -/
theorem hasSum_rhoF : HasSum (seriesTerm3 rhoF) 0 := by
  refine hasSum_real_of_twist3 ![1, -1, I, -I, w3, -w3 ^ 2] ![1, 1, -2, -2, 1, 1] ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact norm_one
    · simp
    · exact Complex.norm_I
    · simp
    · exact norm_w3
    · exact norm_neg_w3_sq
  · intro k
    rw [twist3_rhoF, Fin.sum_univ_six]
    rfl
  · have hre : ell3 1 + ell3 (-1) - 2 * ell3 I - 2 * ell3 (-I) + ell3 w3 + ell3 (-w3 ^ 2) = 0 := by
      linarith [two_ell3_one, two_ell3_neg_one, two_ell3_I, two_ell3_neg_I, two_ell3_w3,
        two_ell3_neg_w3_sq]
    have hreC : ((ell3 1 : ℝ) : ℂ) + ((ell3 (-1) : ℝ) : ℂ) - 2 * ((ell3 I : ℝ) : ℂ) -
        2 * ((ell3 (-I) : ℝ) : ℂ) + ((ell3 w3 : ℝ) : ℂ) + ((ell3 (-w3 ^ 2) : ℝ) : ℂ) = 0 := by
      exact_mod_cast hre
    rw [Fin.sum_univ_six]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [log_eq_ell3_theta3 1, log_eq_ell3_theta3 (-1), log_eq_ell3_theta3 I,
      log_eq_ell3_theta3 (-I), log_eq_ell3_theta3 w3, log_eq_ell3_theta3 (-w3 ^ 2), theta3_one,
      theta3_neg_one, theta3_I, theta3_neg_I, theta3_w3, theta3_neg_w3_sq]
    push_cast
    linear_combination (-1 : ℂ) * hreC

/-! ## 8. Baker's theorem: the coefficients lie in the span of the integer relations -/

/-- For a series of value `γ π` (`γ` algebraic), the vector `(iγ; d_r)` is a combination, with
algebraic coefficients, of integer relations among `iπ` and the `Log(1 - r/t)`. -/
theorem coeffs_spanIn (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h4 : 4 ∣ N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTerm3 ρ) (γ * Real.pi)) :
    ∃ β : Option ℂ → ℂ, (∀ r ∈ rootsN N, β (some r) = fourierD3 N ρ r) ∧
      SpanIn (algebraicClosure ℚ ℂ) (IntRel (Finset.insertNone (rootsN N)) lamOf3) β := by
  classical
  have hS : ∀ r ∈ rootsN N, IsOfFinOrder r := fun r hr => isOfFinOrder_of_mem_rootsN hN hr
  have h1 := series_eq_logs3 hN h4 hρ
  have e : (fun k : ℕ => (ρ k : ℂ) / 3 ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTerm3 ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTerm3]
  rw [e] at h1
  have h2 := h1.unique (Complex.hasSum_ofReal.2 h)
  have hγC : IsAlgebraic ℚ (γ : ℂ) :=
    (isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective).2 hγ
  let β : Option ℂ → ℂ := fun o =>
    match o with
    | none => I * γ
    | some r => if r ∈ rootsN N then fourierD3 N ρ r else 0
  have hβS : ∀ r ∈ rootsN N, β (some r) = fourierD3 N ρ r := fun r hr => by
    simp only [β, hr, ↓reduceIte]
  have hF : ∀ x ∈ algebraicClosure ℚ ℂ, IsAlgebraic ℚ x := fun x hx =>
    mem_algebraicClosure_iff.1 hx
  refine ⟨β, hβS, ?_⟩
  refine baker_descent hB _ hF lamOf3 _ (isAlgebraic_exp_lamOf3 hS) β ?_ ?_ ?_
  · intro i hi
    rcases i with _ | r
    · exact mem_algebraicClosure_iff.2 (isAlgebraic_I.mul hγC)
    · have hr : r ∈ rootsN N := Finset.some_mem_insertNone.1 hi
      rw [hβS r hr]
      exact mem_algebraicClosure_iff.2 (isAlgebraic_fourierD3 N ρ (hS r hr))
  · intro i hi
    rcases i with _ | r
    · exact absurd (by simp) hi
    · have hr : r ∉ rootsN N := fun hr => hi (Finset.some_mem_insertNone.2 hr)
      simp only [β, hr, ↓reduceIte]
  · rw [Finset.sum_insertNone]
    have e2 : ∑ r ∈ rootsN N, β (some r) * lamOf3 (some r) =
        ∑ r ∈ rootsN N, fourierD3 N ρ r * Complex.log (1 - r / t3) :=
      Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
    rw [e2, h2]
    change I * γ * (Real.pi * I) + ((γ * Real.pi : ℝ) : ℂ) = 0
    push_cast
    linear_combination ((γ : ℂ) * Real.pi) * Complex.I_sq

/-! ## 9. The classification -/

/-- **Coordinates** (from Baker's theorem). If a series of the class F3 has value `γ π` with
`γ` algebraic, its pattern is a rational combination of `rhoGregory`, `H` and `F`. -/
theorem exists_coords_GHF (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTerm3 ρ) (γ * Real.pi)) :
    ∃ a b c : ℚ, ∀ k, ρ k = a * rhoGregory k + b * rhoH k + c * rhoF k := by
  classical
  have hG := goodPrimes3
  -- a period divisible by 12
  have hρ' : ∀ k, ρ (k + 12 * N) = ρ k := fun k => by
    have h12 := periodic_mul hρ 12 k
    rwa [mul_comm] at h12
  have hN' : 0 < 12 * N := by positivity
  obtain ⟨N', hN'def⟩ : ∃ N', N' = 12 * N := ⟨_, rfl⟩
  rw [← hN'def] at hρ' hN'
  have h4 : 4 ∣ N' := ⟨3 * N, by rw [hN'def]; ring⟩
  have h12 : 12 ∣ N' := ⟨N, hN'def⟩
  obtain ⟨β, hβS, hspan⟩ := coeffs_spanIn hB hN' h4 hρ' hγ h
  have hS : ∀ r ∈ rootsN N', IsOfFinOrder r := fun r hr => isOfFinOrder_of_mem_rootsN hN' hr
  have hmem : ∀ r ∈ R03, r ∈ rootsN N' := fun r hr =>
    R03fin_subset_rootsN hN' h12 (mem_R03fin.2 hr)
  have m1 : (1 : ℂ) ∈ R03 := Or.inl rfl
  have mn : (-1 : ℂ) ∈ R03 := Or.inr (Or.inl rfl)
  have mI : I ∈ R03 := Or.inr (Or.inr (Or.inl rfl))
  have mJ : -I ∈ R03 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have mw : w3 ∈ R03 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have me : -w3 ^ 2 ∈ R03 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  -- the Fourier coefficients of the twisted pattern
  obtain ⟨cc, hcc⟩ : ∃ cc : ℂ → ℂ, cc = coeffAt N' (twist3 ρ) := ⟨_, rfl⟩
  have hd : ∀ r, fourierD3 N' ρ r = -cc r := fun r => by rw [hcc]; rfl
  -- they vanish outside the six exceptional roots
  have hsupp : ∀ r ∈ rootsN N', r ∉ R03 → cc r = 0 := by
    intro r hr hr0
    have h0 := spanIn_linear (fun v : Option ℂ → ℂ => v (some r)) rfl (fun _ _ _ => rfl)
      (fun v hv => intRel_support hG hS hv hr hr0) hspan
    have h0' : β (some r) = 0 := h0
    rw [hβS r hr, hd, neg_eq_zero] at h0'
    exact h0'
  -- three linear conditions on the six that remain
  have k1 : cc I - cc (-I) = 0 := by
    have h0 := spanIn_linear (fun v : Option ℂ → ℂ => v (some I) - v (some (-I))) (by simp)
      (fun c v w => by dsimp only; ring)
      (fun v hv => sub_eq_zero.2 (intRel_re hG hN' h12 hv).1) hspan
    have h0' : β (some I) - β (some (-I)) = 0 := h0
    rw [hβS _ (hmem _ mI), hβS _ (hmem _ mJ), hd, hd] at h0'
    linear_combination -h0'
  have k2 : cc 1 + cc (-1) + cc I = 0 := by
    have h0 := spanIn_linear
      (fun v : Option ℂ → ℂ => v (some 1) + v (some (-1)) + v (some I)) (by simp)
      (fun c v w => by dsimp only; ring)
      (fun v hv => (intRel_re hG hN' h12 hv).2.1) hspan
    have h0' : β (some 1) + β (some (-1)) + β (some I) = 0 := h0
    rw [hβS _ (hmem _ m1), hβS _ (hmem _ mn), hβS _ (hmem _ mI), hd, hd, hd] at h0'
    linear_combination -h0'
  have k3 : cc w3 + cc (-w3 ^ 2) + cc I = 0 := by
    have h0 := spanIn_linear
      (fun v : Option ℂ → ℂ => v (some w3) + v (some (-w3 ^ 2)) + v (some I)) (by simp)
      (fun c v w => by dsimp only; ring)
      (fun v hv => (intRel_re hG hN' h12 hv).2.2) hspan
    have h0' : β (some w3) + β (some (-w3 ^ 2)) + β (some I) = 0 := h0
    rw [hβS _ (hmem _ mw), hβS _ (hmem _ me), hβS _ (hmem _ mI), hd, hd, hd] at h0'
    linear_combination -h0'
  -- Fourier inversion, reduced to the six roots
  have hc := twist3_periodic h4 hρ'
  have hk : ∀ k, twist3 ρ k = cc 1 * 1 ^ k + (cc (-1) * (-1) ^ k + (cc I * I ^ k +
      (cc (-I) * (-I) ^ k + (cc w3 * w3 ^ k + cc (-w3 ^ 2) * (-w3 ^ 2) ^ k)))) := by
    intro k
    have hinv : ∑ r ∈ rootsN N', cc r * r ^ k = twist3 ρ k := by
      rw [sum_rootsN hN', hcc]
      exact fourier_inversion hN' hc k
    rw [← hinv]
    exact sum_rootsN_R03 hN' h12 _ fun r hr hr0 => by rw [hsupp r hr hr0, zero_mul]
  -- complex coordinates
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A * (3 * t3) = (cc 1 - cc (-1)) / 2 :=
    ⟨(cc 1 - cc (-1)) / 2 / (3 * t3),
      div_mul_cancel₀ _ (mul_ne_zero (by norm_num) t3_ne_zero)⟩
  obtain ⟨B, hB'⟩ : ∃ B : ℂ, B * t3 = (cc (-w3 ^ 2) - cc w3) / 2 :=
    ⟨(cc (-w3 ^ 2) - cc w3) / 2 / t3, div_mul_cancel₀ _ t3_ne_zero⟩
  have hcoord : ∀ k, (ρ k : ℂ) =
      A * (rhoGregory k : ℂ) + B * (rhoH k : ℂ) + -(cc I) / 2 * (rhoF k : ℂ) := by
    intro k
    have key : twist3 ρ k = A * twist3 rhoGregory k + B * twist3 rhoH k +
        -(cc I) / 2 * twist3 rhoF k := by
      rw [twist3_rhoGregory, twist3_rhoH, twist3_rhoF]
      linear_combination hk k + ((1 : ℂ) ^ k + (-1) ^ k) / 2 * k2 - (-I) ^ k * k1 +
        (w3 ^ k + (-w3 ^ 2) ^ k) / 2 * k3 - ((1 : ℂ) ^ k - (-1) ^ k) * hA -
        ((-w3 ^ 2) ^ k - w3 ^ k) * hB'
    have hτ : t3 ^ (k % 2) * (-1 : ℂ) ^ (k / 2) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ t3_ne_zero) (pow_ne_zero _ (by norm_num))
    simp only [twist3] at key
    exact mul_right_cancel₀ hτ (by rw [key]; ring)
  -- the coordinates are rational
  have hv : rhoGregory 1 = 6 ∧ rhoH 1 = 1 ∧ rhoF 1 = 1 ∧ rhoGregory 2 = 0 ∧ rhoH 2 = 3 ∧
      rhoF 2 = -5 ∧ rhoGregory 3 = -6 ∧ rhoH 3 = 2 ∧ rhoF 3 = 0 := by decide +kernel
  obtain ⟨g1, e1, f1, g2, e2, f2, g3, e3, f3⟩ := hv
  have q1 := hcoord 1
  have q2 := hcoord 2
  have q3 := hcoord 3
  rw [g1, e1, f1] at q1
  rw [g2, e2, f2] at q2
  rw [g3, e3, f3] at q3
  push_cast at q1 q2 q3
  have hBq : B = (((ρ 2 + 5 * ρ 1 + 5 * ρ 3) / 18 : ℚ) : ℂ) := by
    push_cast
    linear_combination (-1 / 18 : ℂ) * q2 - (5 / 18 : ℂ) * q1 - (5 / 18 : ℂ) * q3
  have hAq : A = (((2 * ((ρ 2 + 5 * ρ 1 + 5 * ρ 3) / 18) - ρ 3) / 6 : ℚ) : ℂ) := by
    push_cast at hBq ⊢
    linear_combination (1 / 6 : ℂ) * q3 + (1 / 3 : ℂ) * hBq
  have hCq : -(cc I) / 2 = ((ρ 1 + ρ 3 - 3 * ((ρ 2 + 5 * ρ 1 + 5 * ρ 3) / 18) : ℚ) : ℂ) := by
    push_cast at hBq ⊢
    linear_combination (-1 : ℂ) * q1 - q3 - 3 * hBq
  refine ⟨(2 * ((ρ 2 + 5 * ρ 1 + 5 * ρ 3) / 18) - ρ 3) / 6, (ρ 2 + 5 * ρ 1 + 5 * ρ 3) / 18,
    ρ 1 + ρ 3 - 3 * ((ρ 2 + 5 * ρ 1 + 5 * ρ 3) / 18), fun k => ?_⟩
  have hk' := hcoord k
  rw [hAq, hBq, hCq] at hk'
  exact_mod_cast hk'

/-! ## 10. The Gregory pattern and two zero relations -/

/-- `Z₁ = (0, 1, -2, 0, 1, 4, 0, 3, 2, 4, -1, 0)` (for `k = 1, ..., 12`), a zero relation. -/
def rhoZ1 (k : ℕ) : ℚ :=
  match k % 12 with
  | 2 => 1 | 3 => -2 | 5 => 1 | 6 => 4 | 8 => 3 | 9 => 2 | 10 => 4 | 11 => -1 | _ => 0

/-- `Z₂ = (1, -3, -4, -3, 1, 0, -1, 3, 4, 3, -1, 0)` (for `k = 1, ..., 12`), a zero
relation. -/
def rhoZ2 (k : ℕ) : ℚ :=
  match k % 12 with
  | 1 => 1 | 2 => -3 | 3 => -4 | 4 => -3 | 5 => 1 | 7 => -1 | 8 => 3 | 9 => 4 | 10 => 3
  | 11 => -1 | _ => 0

theorem rhoZ1_periodic (k : ℕ) : rhoZ1 (k + 12) = rhoZ1 k := by simp [rhoZ1]

theorem rhoZ2_periodic (k : ℕ) : rhoZ2 (k + 12) = rhoZ2 k := by simp [rhoZ2]

theorem rhoGregory_periodic12 (k : ℕ) : rhoGregory (k + 12) = rhoGregory k :=
  periodic_mul rhoGregory_periodic 3 k

theorem rhoH_periodic (k : ℕ) : rhoH (k + 12) = rhoH k := by
  have e1 : (k + 12) / 2 = k / 2 + 6 := by omega
  have e2 : (k + 12) % 2 = k % 2 := by omega
  have e3 : (k + 12) % 3 = k % 3 := by omega
  simp only [rhoH, eisB, eisRe, e1, e2, e3, pow_add]
  norm_num

theorem rhoF_periodic (k : ℕ) : rhoF (k + 12) = rhoF k := by
  have e1 : (k + 12) / 2 = k / 2 + 6 := by omega
  have e2 : (k + 12) % 2 = k % 2 := by omega
  have e3 : (k + 12) % 3 = k % 3 := by omega
  simp only [rhoF, eisB, eisRe, e1, e2, e3, pow_add]
  norm_num

/-- Two patterns of period 12 that agree on `0, ..., 11` are equal. -/
theorem eq_of_lt_twelve {f g : ℕ → ℚ} (hf : ∀ k, f (k + 12) = f k) (hg : ∀ k, g (k + 12) = g k)
    (h : ∀ j < 12, f j = g j) (k : ℕ) : f k = g k := by
  have h1 := periodic_mul hf (k / 12) (k % 12)
  have h2 := periodic_mul hg (k / 12) (k % 12)
  rw [Nat.mod_add_div] at h1 h2
  rw [h1, h2]
  exact h _ (Nat.mod_lt _ (by norm_num))

/-- `H = rhoGregory / 3 - Z₂`. -/
theorem rhoH_eq (k : ℕ) : rhoH k = rhoGregory k / 3 - rhoZ2 k :=
  eq_of_lt_twelve (g := fun k => rhoGregory k / 3 - rhoZ2 k) rhoH_periodic
    (fun k => by simp only [rhoGregory_periodic12 k, rhoZ2_periodic k]) (by decide +kernel) k

/-- `F = Z₂ - 2 Z₁`. -/
theorem rhoF_eq (k : ℕ) : rhoF k = rhoZ2 k - 2 * rhoZ1 k :=
  eq_of_lt_twelve (g := fun k => rhoZ2 k - 2 * rhoZ1 k) rhoF_periodic
    (fun k => by simp only [rhoZ1_periodic k, rhoZ2_periodic k]) (by decide +kernel) k

/-- The combination `a rhoGregory + b Z₁ + c Z₂`. -/
def comb3 (a b c : ℚ) (k : ℕ) : ℚ := a * rhoGregory k + b * rhoZ1 k + c * rhoZ2 k

theorem comb3_periodic (a b c : ℚ) (k : ℕ) : comb3 a b c (k + 12) = comb3 a b c k := by
  simp only [comb3, rhoGregory_periodic12 k, rhoZ1_periodic k, rhoZ2_periodic k]

/-- A rational combination of two patterns. -/
theorem hasSum_lin {ρ σ : ℕ → ℚ} {x y : ℝ} (hx : HasSum (seriesTerm3 ρ) x)
    (hy : HasSum (seriesTerm3 σ) y) (a b : ℚ) :
    HasSum (seriesTerm3 fun k => a * ρ k + b * σ k) (a * x + b * y) := by
  have h := (hx.mul_left (a : ℝ)).add (hy.mul_left (b : ℝ))
  convert h using 1
  funext k
  simp only [seriesTerm3]
  push_cast
  ring

/-- `S(Z₂) = 0`. -/
theorem hasSum_rhoZ2 : HasSum (seriesTerm3 rhoZ2) 0 := by
  have h := hasSum_lin hasSum_gregory3 hasSum_rhoH (1 / 3) (-1)
  have e : (fun k => (1 / 3 : ℚ) * rhoGregory k + (-1 : ℚ) * rhoH k) = rhoZ2 := by
    funext k
    rw [rhoH_eq]
    ring
  rw [e] at h
  convert h using 1
  push_cast
  ring

/-- `S(Z₁) = 0`. -/
theorem hasSum_rhoZ1 : HasSum (seriesTerm3 rhoZ1) 0 := by
  have h := hasSum_lin hasSum_rhoZ2 hasSum_rhoF (1 / 2) (-1 / 2)
  have e : (fun k => (1 / 2 : ℚ) * rhoZ2 k + (-1 / 2 : ℚ) * rhoF k) = rhoZ1 := by
    funext k
    rw [rhoF_eq]
    ring
  rw [e] at h
  convert h using 1
  simp

/-- **The value.** `S(a rhoGregory + b Z₁ + c Z₂) = a π√3`. -/
theorem hasSum_comb3 (a b c : ℚ) :
    HasSum (seriesTerm3 (comb3 a b c)) (a * (Real.pi * Real.sqrt 3)) := by
  have h1 := hasSum_lin hasSum_gregory3 hasSum_rhoZ1 a b
  have h2 := hasSum_lin h1 hasSum_rhoZ2 1 c
  have e : (fun k => (1 : ℚ) * (a * rhoGregory k + b * rhoZ1 k) + c * rhoZ2 k) =
      comb3 a b c := by
    funext k
    simp only [comb3]
    ring
  rw [e] at h2
  convert h2 using 1
  push_cast
  ring

/-- **Every formula for a multiple of `π` in base 3** (from Baker's theorem). If a series of
the class F3 has value `γ π` with `γ` algebraic, then its pattern is
`a rhoGregory + b Z₁ + c Z₂` with `a, b, c` rational, and `γ = a √3`. -/
theorem exists_coords3 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTerm3 ρ) (γ * Real.pi)) :
    ∃ a b c : ℚ, ρ = comb3 a b c ∧ γ = a * Real.sqrt 3 := by
  obtain ⟨a, b, c, hk⟩ := exists_coords_GHF hB hN hρ hγ h
  have hρeq : ρ = comb3 (a + b / 3) (-2 * c) (c - b) := by
    funext k
    rw [hk k, rhoH_eq, rhoF_eq, comb3]
    ring
  refine ⟨a + b / 3, -2 * c, c - b, hρeq, ?_⟩
  have h2 := hasSum_comb3 (a + b / 3) (-2 * c) (c - b)
  rw [← hρeq] at h2
  have h3 := h.unique h2
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h4 : γ * Real.pi = ((a + b / 3 : ℚ) : ℝ) * Real.sqrt 3 * Real.pi := by
    rw [h3]
    ring
  exact mul_right_cancel₀ hpi h4

/-- **Period 12** (from Baker's theorem). -/
theorem period_twelve (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {γ : ℝ} (hγ : IsAlgebraic ℚ γ)
    (h : HasSum (seriesTerm3 ρ) (γ * Real.pi)) (k : ℕ) : ρ (k + 12) = ρ k := by
  obtain ⟨a, b, c, rfl, -⟩ := exists_coords3 hB hN hρ hγ h
  exact comb3_periodic a b c k

/-- **The zero relations of base 3** (from Baker's theorem): a rational periodic pattern has
`S(ρ) = 0` if and only if `ρ = b Z₁ + c Z₂`. -/
theorem hasSum_zero_iff (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) :
    HasSum (seriesTerm3 ρ) 0 ↔ ∃ b c : ℚ, ρ = comb3 0 b c := by
  constructor
  · intro h
    have h' : HasSum (seriesTerm3 ρ) ((0 : ℝ) * Real.pi) := by rwa [zero_mul]
    obtain ⟨a, b, c, hρeq, ha⟩ := exists_coords3 hB hN hρ isAlgebraic_zero h'
    have ha0 : a = 0 := by
      have hs : Real.sqrt 3 ≠ 0 := sqrt3_pos.ne'
      have : (a : ℝ) = 0 := by
        rcases mul_eq_zero.1 ha.symm with h0 | h0
        · exact h0
        · exact absurd h0 hs
      exact_mod_cast this
    exact ⟨b, c, by rw [hρeq, ha0]⟩
  · rintro ⟨b, c, rfl⟩
    have h := hasSum_comb3 0 b c
    simpa using h

/-! ## 11. Dimensions -/

theorem seriesTerm3_zero : seriesTerm3 0 = fun _ => 0 := by
  funext k
  simp [seriesTerm3]

/-- The rational patterns of period `N` whose series is an algebraic multiple of `π`. -/
def algSpace3 (N : ℕ) : Submodule ℚ (ℕ → ℚ) where
  carrier := {ρ | (∀ k, ρ (k + N) = ρ k) ∧
    ∃ γ : ℝ, IsAlgebraic ℚ γ ∧ HasSum (seriesTerm3 ρ) (γ * Real.pi)}
  add_mem' := by
    rintro ρ ρ' ⟨hp, γ, hγ, h⟩ ⟨hp', γ', hγ', h'⟩
    refine ⟨fun k => by simp only [Pi.add_apply, hp k, hp' k], γ + γ', hγ.add hγ', ?_⟩
    have h2 := h.add h'
    rw [← add_mul] at h2
    have e : seriesTerm3 (ρ + ρ') = fun k => seriesTerm3 ρ k + seriesTerm3 ρ' k :=
      funext (seriesTerm3_add ρ ρ')
    rw [e]
    exact h2
  zero_mem' := by
    refine ⟨fun _ => rfl, 0, isAlgebraic_zero, ?_⟩
    rw [zero_mul, seriesTerm3_zero]
    exact hasSum_zero
  smul_mem' := by
    rintro q ρ ⟨hp, γ, hγ, h⟩
    refine ⟨fun k => by simp only [Pi.smul_apply, hp k], q * γ,
      IsAlgebraic.mul (isAlgebraic_ratCast ℚ (A := ℝ) q) hγ, ?_⟩
    have h2 := h.mul_left (q : ℝ)
    rw [← mul_assoc] at h2
    have e : seriesTerm3 (q • ρ) = fun k => (q : ℝ) * seriesTerm3 ρ k :=
      funext (seriesTerm3_smul q ρ)
    rw [e]
    exact h2

/-- The zero relations of period `N`: the rational patterns of period `N` whose series is 0. -/
def zeroSpace3 (N : ℕ) : Submodule ℚ (ℕ → ℚ) where
  carrier := {ρ | (∀ k, ρ (k + N) = ρ k) ∧ HasSum (seriesTerm3 ρ) 0}
  add_mem' := by
    rintro ρ ρ' ⟨hp, h⟩ ⟨hp', h'⟩
    refine ⟨fun k => by simp only [Pi.add_apply, hp k, hp' k], ?_⟩
    have h2 := h.add h'
    rw [add_zero] at h2
    have e : seriesTerm3 (ρ + ρ') = fun k => seriesTerm3 ρ k + seriesTerm3 ρ' k :=
      funext (seriesTerm3_add ρ ρ')
    rw [e]
    exact h2
  zero_mem' := by
    refine ⟨fun _ => rfl, ?_⟩
    rw [seriesTerm3_zero]
    exact hasSum_zero
  smul_mem' := by
    rintro q ρ ⟨hp, h⟩
    refine ⟨fun k => by simp only [Pi.smul_apply, hp k], ?_⟩
    have h2 := h.mul_left (q : ℝ)
    rw [mul_zero] at h2
    have e : seriesTerm3 (q • ρ) = fun k => (q : ℝ) * seriesTerm3 ρ k :=
      funext (seriesTerm3_smul q ρ)
    rw [e]
    exact h2

/-- The three patterns. -/
def fam3 : Fin 3 → ℕ → ℚ := ![rhoGregory, rhoZ1, rhoZ2]

/-- The two zero relations. -/
def famZ : Fin 2 → ℕ → ℚ := ![rhoZ1, rhoZ2]

theorem sum_fam3 (g : Fin 3 → ℚ) : ∑ i, g i • fam3 i = comb3 (g 0) (g 1) (g 2) := by
  funext k
  simp only [fam3, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, comb3]

theorem sum_famZ (g : Fin 2 → ℚ) : ∑ i, g i • famZ i = comb3 0 (g 0) (g 1) := by
  funext k
  simp only [famZ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, comb3]
  ring

theorem comb3_eq_zero {a b c : ℚ} (h : ∀ k, comb3 a b c k = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hv : rhoGregory 1 = 6 ∧ rhoZ1 1 = 0 ∧ rhoZ2 1 = 1 ∧ rhoGregory 2 = 0 ∧ rhoZ1 2 = 1 ∧
      rhoZ2 2 = -3 ∧ rhoGregory 3 = -6 ∧ rhoZ1 3 = -2 ∧ rhoZ2 3 = -4 := by decide +kernel
  obtain ⟨g1, e1, f1, g2, e2, f2, g3, e3, f3⟩ := hv
  have q1 := h 1
  have q2 := h 2
  have q3 := h 3
  simp only [comb3, g1, e1, f1] at q1
  simp only [comb3, g2, e2, f2] at q2
  simp only [comb3, g3, e3, f3] at q3
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **The three patterns are linearly independent over `ℚ`.** -/
theorem fam3_linearIndependent : LinearIndependent ℚ fam3 := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h : ∀ k, comb3 (g 0) (g 1) (g 2) k = 0 := fun k => by
    rw [← sum_fam3, hg]
    rfl
  obtain ⟨h0, h1, h2⟩ := comb3_eq_zero h
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **The two zero relations are linearly independent over `ℚ`.** -/
theorem famZ_linearIndependent : LinearIndependent ℚ famZ := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h : ∀ k, comb3 0 (g 0) (g 1) k = 0 := fun k => by
    rw [← sum_famZ, hg]
    rfl
  obtain ⟨-, h1, h2⟩ := comb3_eq_zero h
  intro i
  fin_cases i
  · exact h1
  · exact h2

theorem isAlgebraic_sqrt3_real : IsAlgebraic ℚ (Real.sqrt 3) :=
  (isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective).1 isAlgebraic_sqrt3

theorem comb3_mem_algSpace3 {N : ℕ} (h12 : 12 ∣ N) (a b c : ℚ) : comb3 a b c ∈ algSpace3 N := by
  refine ⟨fun k => ?_, a * Real.sqrt 3,
    (isAlgebraic_ratCast ℚ (A := ℝ) a).mul isAlgebraic_sqrt3_real, ?_⟩
  · obtain ⟨m, rfl⟩ := h12
    exact periodic_mul (comb3_periodic a b c) m k
  · have h := hasSum_comb3 a b c
    convert h using 1
    ring

theorem comb3_mem_zeroSpace3 {N : ℕ} (h12 : 12 ∣ N) (b c : ℚ) :
    comb3 0 b c ∈ zeroSpace3 N := by
  refine ⟨fun k => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := h12
    exact periodic_mul (comb3_periodic 0 b c) m k
  · have h := hasSum_comb3 0 b c
    simpa using h

/-- The space of the formulas is spanned by the three patterns (from Baker's theorem). -/
theorem algSpace3_eq (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h12 : 12 ∣ N) :
    algSpace3 N = Submodule.span ℚ (Set.range fam3) := by
  apply le_antisymm
  · rintro ρ ⟨hp, γ, hγ, h⟩
    obtain ⟨a, b, c, rfl, -⟩ := exists_coords3 hB hN hp hγ h
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![a, b, c], ?_⟩
    rw [sum_fam3]
    rfl
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h : ∑ j, (Pi.single i (1 : ℚ) : Fin 3 → ℚ) j • fam3 j ∈ algSpace3 N := by
      rw [sum_fam3]
      exact comb3_mem_algSpace3 h12 _ _ _
    simpa [Pi.single_apply] using h

/-- The space of the zero relations is spanned by `Z₁` and `Z₂` (from Baker's theorem). -/
theorem zeroSpace3_eq (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h12 : 12 ∣ N) :
    zeroSpace3 N = Submodule.span ℚ (Set.range famZ) := by
  apply le_antisymm
  · rintro ρ ⟨hp, h⟩
    obtain ⟨b, c, rfl⟩ := (hasSum_zero_iff hB hN hp).1 h
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![b, c], ?_⟩
    rw [sum_famZ]
    rfl
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h : ∑ j, (Pi.single i (1 : ℚ) : Fin 2 → ℚ) j • famZ j ∈ zeroSpace3 N := by
      rw [sum_famZ]
      exact comb3_mem_zeroSpace3 h12 _ _
    simpa [Pi.single_apply] using h

/-- **Dimension exactly 3** (from Baker's theorem). -/
theorem finrank_algSpace3 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h12 : 12 ∣ N) :
    Module.finrank ℚ (algSpace3 N) = 3 := by
  rw [algSpace3_eq hB hN h12, finrank_span_eq_card fam3_linearIndependent, Fintype.card_fin]

/-- **The zero relations have dimension exactly 2** (from Baker's theorem). -/
theorem finrank_zeroSpace3 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h12 : 12 ∣ N) :
    Module.finrank ℚ (zeroSpace3 N) = 2 := by
  rw [zeroSpace3_eq hB hN h12, finrank_span_eq_card famZ_linearIndependent, Fintype.card_fin]

/-- **Theorem C3 in full (from Baker's theorem).** Let `N` be a multiple of 12. Among the
rational patterns `ρ` of period `N`:
* those whose series `∑ ρ(k) 3^(-⌊k/2⌋)/k` is an algebraic multiple of `π` have period 12
  and form a space of dimension exactly 3;
* those whose series is 0 form a subspace of dimension exactly 2. -/
theorem theoremC3 (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h12 : 12 ∣ N) :
    (∀ ρ ∈ algSpace3 N, ∀ k, ρ (k + 12) = ρ k) ∧
      Module.finrank ℚ (algSpace3 N) = 3 ∧ Module.finrank ℚ (zeroSpace3 N) = 2 :=
  ⟨fun _ ⟨hp, _, hγ, h⟩ k => period_twelve hB hN hp hγ h k, finrank_algSpace3 hB hN h12,
    finrank_zeroSpace3 hB hN h12⟩

end Base3

end PiFormula
