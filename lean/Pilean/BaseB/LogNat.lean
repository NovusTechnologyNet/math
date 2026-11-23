import Pilean.BaseB.LogWeight
import Pilean.BaseB.LogSpan
import Pilean.BaseB.LogBase

/-!
# Theorem N: no logarithm of an integer in a base that is not a power of 2 or 3

**Theorem** (`no_log_nat_bailey`). Let `b ≥ 2` be an integer that is neither a power of 2 nor a
power of 3, and `n ≥ 2` an integer. No degree-1 BBP-type series of base `b`,

  `∑_{j ≥ 0} b^(-B j) ∑_{i=1}^{N} c_i / (N j + i)`,   `c_i` rational,

equals `q π + q' log n` with `q, q'` rational and `q' ≠ 0`. In particular `log n` has no such
formula: for example no `log n` has a degree-1 BBP-type formula of base 10.

For the class `F_b` of a base `b ≥ 5` that is not a square this is
`not_isFBValue_mul_pi_add_log_nat`.

The proof has two halves, in two files:

* `LogSpan` (from Baker's theorem): if `q π + q' log y` is a value of `F_b`, some power of `y`
  is a product of integer powers of the rational numbers `ν(r)²`;
* `LogWeight`: for `b ≥ 5` not a square there is a weight on the rationals, additive on
  products and positive on every integer `n ≥ 2`, that vanishes on every `ν(r)²`.

So a power of `n` would have weight zero, which is impossible. The passage from a series of
any step to the class `F_a` is as for Theorem L (`SubseriesLog`, `Kummer`, `Reindex`).

Baker's theorem is used through the imported proof; there is no hypothesis.
-/

open Complex Polynomial

namespace PiFormula

namespace BaseB

theorem nuSq_ne_zero {b : ℕ} (hb : 2 ≤ b) {r : ℂ} (hr : IsOfFinOrder r) : nuSq b r ≠ 0 := by
  have h0 : (minpoly ℤ (tB b - r)).eval 0 ≠ 0 := by
    intro h
    exact cAbs_ne_zero hb hr (by simp [cAbs, h])
  have hb0 : (b : ℚ) ≠ 0 := by
    have : 0 < b := by omega
    positivity
  unfold nuSq
  exact div_ne_zero (pow_ne_zero 2 (by exact_mod_cast h0)) (pow_ne_zero _ hb0)

/-! ## Maps on the rationals that are additive on products -/

theorem weight_one {L : ℚ → ℚ} (hL : ∀ x y : ℚ, x ≠ 0 → y ≠ 0 → L (x * y) = L x + L y) :
    L 1 = 0 := by
  have h := hL 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  linarith

theorem weight_inv {L : ℚ → ℚ} (hL : ∀ x y : ℚ, x ≠ 0 → y ≠ 0 → L (x * y) = L x + L y) {x : ℚ}
    (hx : x ≠ 0) : L x⁻¹ = -L x := by
  have h := hL x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, weight_one hL] at h
  linarith

theorem weight_pow {L : ℚ → ℚ} (hL : ∀ x y : ℚ, x ≠ 0 → y ≠ 0 → L (x * y) = L x + L y) {x : ℚ}
    (hx : x ≠ 0) (k : ℕ) : L (x ^ k) = k * L x := by
  induction k with
  | zero => simp [weight_one hL]
  | succ k ih =>
    rw [pow_succ, hL _ _ (pow_ne_zero k hx) hx, ih]
    push_cast
    ring

theorem weight_zpow {L : ℚ → ℚ} (hL : ∀ x y : ℚ, x ≠ 0 → y ≠ 0 → L (x * y) = L x + L y) {x : ℚ}
    (hx : x ≠ 0) (e : ℤ) : L (x ^ e) = e * L x := by
  obtain ⟨k, rfl | rfl⟩ := e.eq_nat_or_neg
  · rw [zpow_natCast, weight_pow hL hx]
    push_cast
    ring
  · rw [zpow_neg, zpow_natCast, weight_inv hL (pow_ne_zero k hx), weight_pow hL hx]
    push_cast
    ring

theorem weight_prod {L : ℚ → ℚ} (hL : ∀ x y : ℚ, x ≠ 0 → y ≠ 0 → L (x * y) = L x + L y)
    {ι : Type*} (S : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ S, f i ≠ 0) :
    L (∏ i ∈ S, f i) = ∑ i ∈ S, L (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [weight_one hL]
  | insert a S ha ih =>
    have hS : ∀ i ∈ S, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      hL _ _ (hf a (Finset.mem_insert_self a S)) (Finset.prod_ne_zero_iff.2 hS), ih hS]

/-! ## Theorem N -/

/-- No power of an integer `n ≥ 2` is a product of powers of the numbers `ν(r)²`, in a base
`b ≥ 5` that is not a square. -/
theorem not_inBaseSpan_nat {b : ℕ} (hb : 5 ≤ b) (hsq : ¬ IsSquare b) {n : ℕ} (hn : 2 ≤ n) :
    ¬ InBaseSpan b (n : ℚ) := by
  rintro ⟨k, hk, S, e, hS, hprod⟩
  obtain ⟨L, hL, hpos, hzero⟩ := posWeight hb hsq
  have hb2 : 2 ≤ b := by omega
  have hn0 : (n : ℚ) ≠ 0 := by
    have : 0 < n := by omega
    positivity
  have h1 : L ((n : ℚ) ^ k) = k * L n := weight_pow hL hn0 k
  have h2 : L (∏ r ∈ S, nuSq b r ^ e r) = 0 := by
    rw [weight_prod hL S _ fun r hr => zpow_ne_zero _ (nuSq_ne_zero hb2 (hS r hr))]
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [weight_zpow hL (nuSq_ne_zero hb2 (hS r hr)), hzero r (hS r hr), mul_zero]
  rw [hprod, h2] at h1
  have h3 := hpos n hn
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  have h4 := mul_pos hk' h3
  linarith

/-- **Theorem N for the class `F_b`** (from Baker's theorem). In a base `b ≥ 5` that is not a
square, no number `q π + q' log n`, with `n ≥ 2` an integer, `q, q'` rational and `q' ≠ 0`, is
the value of a series `∑ ρ(k) b^(-⌊k/2⌋)/k` with `ρ` rational and periodic. -/
theorem not_isFBValue_mul_pi_add_log_nat (hB : BakerTheorem) {b : ℕ} (hb : 5 ≤ b)
    (hsq : ¬ IsSquare b) {q q' : ℚ} (hq' : q' ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsFBValue b (q * Real.pi + q' * Real.log n) := by
  intro h
  have hy : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
  have h' : IsFBValue b (q * Real.pi + q' * Real.log ((n : ℚ) : ℝ)) := by simpa using h
  exact not_inBaseSpan_nat hb hsq hn (inBaseSpan_of_isFBValue hB (by omega) hq' hy h')

theorem not_isSquare_of_notPerfectPower {a : ℕ} (hpp : NotPerfectPower a) : ¬ IsSquare a := by
  rintro ⟨r, hr⟩
  exact hpp r 2 le_rfl (by rw [hr, pow_two])

/-- **Every step.** Let `b ≥ 5` be an integer that is not a perfect power and `n ≥ 2` an
integer. No series `∑ ρ(k) b^(-⌊k/s⌋)/k`, with `ρ` rational and periodic and any step `s`,
equals `q π + q' log n` with `q, q'` rational, `q' ≠ 0`. -/
theorem no_log_nat_step {b s : ℕ} (hb : 5 ≤ b) (hpp : NotPerfectPower b) (hs : 0 < s) {N : ℕ}
    (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {q q' : ℚ} (hq' : q' ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) : ¬ HasSum (seriesTermBN b s ρ) (q * Real.pi + q' * Real.log n) := by
  intro h
  have hb2 : 2 ≤ b := by omega
  have hy : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
  have h' : HasSum (seriesTermBN b s ρ) (q * Real.pi + q' * Real.log ((n : ℚ) : ℝ)) := by
    simpa using h
  have hsub := subseries_log_of_kummerHom bakerTheorem hb2 hs (kummerHom hb2 hpp hs) hN hρ hy h'
  have hF := isFBValue_of_hasSum_subseries hb2 hs hN hρ hsub
  exact not_isFBValue_mul_pi_add_log_nat bakerTheorem hb (not_isSquare_of_notPerfectPower hpp)
    hq' hn (by simpa using hF)

/-- **Theorem N.** Let `b ≥ 2` be an integer that is neither a power of 2 nor a power of 3,
and `n ≥ 2` an integer. No series `∑_j b^(-B j) ∑_{i=1}^{N} c_i / (N j + i)` with rational
`c_i` equals `q π + q' log n` with `q, q'` rational, `q' ≠ 0`. -/
theorem no_log_nat_bailey {b B N : ℕ} (hb : 2 ≤ b) (h2 : ∀ k : ℕ, b ≠ 2 ^ k)
    (h3 : ∀ k : ℕ, b ≠ 3 ^ k) (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) {q q' : ℚ}
    (hq' : q' ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    ¬ HasSum (baileyBlock b B N c) (q * Real.pi + q' * Real.log n) := by
  intro h
  obtain ⟨a, j, ha, hj, hpp, rfl⟩ := exists_root_notPerfectPower hb
  have ha5 : 5 ≤ a := by
    have h2' : a ≠ 2 := fun h => h2 j (by rw [h])
    have h3' : a ≠ 3 := fun h => h3 j (by rw [h])
    have h4 : a ≠ 4 := fun h => hpp 2 2 le_rfl (by rw [h]; norm_num)
    omega
  rw [baileyBlock_pow] at h
  obtain ⟨P, ρ, hP, hρ, hs⟩ := exists_step_of_bailey ha (Nat.mul_pos hj hB) hN c h
  have hstep : 0 < N / Nat.gcd (j * B) N :=
    Nat.div_pos (Nat.le_of_dvd hN (Nat.gcd_dvd_right _ _)) (Nat.gcd_pos_of_pos_right _ hN)
  exact no_log_nat_step ha5 hpp hstep hP hρ hq' hn hs

/-- **No logarithm of an integer has a degree-1 BBP-type formula of a base that is not a power
of 2 or 3.** -/
theorem no_log_nat_formula {b B N : ℕ} (hb : 2 ≤ b) (h2 : ∀ k : ℕ, b ≠ 2 ^ k)
    (h3 : ∀ k : ℕ, b ≠ 3 ^ k) (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) {n : ℕ} (hn : 2 ≤ n) :
    ¬ HasSum (baileyBlock b B N c) (Real.log n) := by
  intro h
  refine no_log_nat_bailey hb h2 h3 hB hN c (q := 0) (q' := 1) one_ne_zero hn ?_
  have e : ((0 : ℚ) : ℝ) * Real.pi + ((1 : ℚ) : ℝ) * Real.log (n : ℝ) = Real.log (n : ℝ) := by
    push_cast
    ring
  rw [e]
  exact h

/-- **Base 10.** No `log n`, `n ≥ 2` an integer, has a degree-1 BBP-type formula of base 10. -/
theorem no_log_nat_formula_ten {B N : ℕ} (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) {n : ℕ}
    (hn : 2 ≤ n) : ¬ HasSum (baileyBlock 10 B N c) (Real.log n) := by
  have h2 : ∀ k : ℕ, (10 : ℕ) ≠ 2 ^ k := fun k hk => by
    have h5 : (5 : ℕ) ∣ 2 ^ k := hk ▸ (by norm_num : (5 : ℕ) ∣ 10)
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5
    omega
  have h3 : ∀ k : ℕ, (10 : ℕ) ≠ 3 ^ k := fun k hk => by
    have h5 : (5 : ℕ) ∣ 3 ^ k := hk ▸ (by norm_num : (5 : ℕ) ∣ 10)
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5
    omega
  exact no_log_nat_formula (by norm_num) h2 h3 hB hN c hn

end BaseB

end PiFormula
