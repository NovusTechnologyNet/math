module

public import Pilean.Base5.LogConverse

/-!
# Base 5: `log 5` and `log 2` are not values (from Baker's theorem and good primes)

`not_isF5Value_log_five_of_goodPrimes5` and `not_isF5Value_log_two_of_goodPrimes5`: from
Baker's theorem and the existence of good primes (`GoodPrimes5`), neither `log 5` nor `log 2`
is the value of a series of the class F5. (Their combination `2 log 2 - log 5 = log (4/5)` is
a value.)

The criterion of `Base5/LogConverse.lean` reduces the question to arithmetic: is a power of
`5` a product of powers of base numbers? Answering it needs the primitive prime factors of the
numbers `5^m - 1`, `L_h`, `M_h`, which is what `GoodPrimes5` provides. So the proof goes
through the relations directly, as in `Base5/Classification.lean`.

The proof. By Baker's theorem (`exists_rel5_of_isF5Value_log`), a formula for `log y` gives a
relation `∏ (1 - r/t)^(e_r) = ξ y^m` with `m ≠ 0`. For `y = 5` or `y = 2` a good prime, which
is odd and different from 5, does not divide `y`, so the private-prime argument of
`Base5/Support.lean` still applies (`support_subset_pm_one_rel5`): `e_r = 0` except at
`r = 1, -1`. Taking absolute values, `(1 - 1/√5)^a (1 + 1/√5)^b = y^m`. The product of the two
numbers is `4/5` and their quotient is the square of the golden ratio, whose non-zero powers
are irrational; so `a = b` and `(4/5)^(2a) = y^(2m)` (`rel5_reduce`), which is impossible
for `y = 5` and for `y = 2` unless `m = 0`, since `4^x = 5^y` only for `x = y = 0`.
-/

@[expose] public section

open Complex

namespace PiFormula

namespace Base5

/-! ## 1. The private prime, for a relation up to a power of a rational number -/

/-- **The private prime.** In a relation `∏ (1 - r/t)^(e_r) = ξ (a/b)^m`: if `t - r₀ ∈ P`,
while `t`, `a`, `b` and the other `t - r` are not in `P`, then `e_{r₀} = 0`. -/
theorem coeff_eq_zero_of_private_ideal_rel5 {P : Ideal Aint} [P.IsPrime] {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ}
    {m : ℤ} (h : IsRel5 (a : ℂ) (b : ℂ) S e m) {r₀ : ℂ} (hr₀ : r₀ ∈ S) (ht : ¬ InP P t5)
    (hPa : ¬ InP P (a : ℂ)) (hPb : ¬ InP P (b : ℂ)) (h0 : InP P (t5 - r₀))
    (hpriv : ∀ r ∈ S, r ≠ r₀ → ¬ InP P (t5 - r)) : e r₀ = 0 := by
  classical
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  obtain ⟨ξ, hξ, hc⟩ := cleared5 haC hbC hS h
  have hint : ∀ r ∈ S, ∀ n : ℕ, IsIntegral ℤ ((t5 - r) ^ n) :=
    fun r hr n => (isIntegral_t5_sub (hS r hr)).pow n
  have hprodI : ∀ f : ℂ → ℕ, IsIntegral ℤ (∏ r ∈ S, (t5 - r) ^ f r) :=
    fun f => IsIntegral.prod _ fun r hr => hint r hr _
  have hcI : ∀ x y : ℕ, IsIntegral ℤ ((a : ℂ) ^ x * (b : ℂ) ^ y) := fun x y =>
    ((isIntegral_natCast' a).pow x).mul ((isIntegral_natCast' b).pow y)
  have hcP : ∀ x y : ℕ, ¬ InP P ((a : ℂ) ^ x * (b : ℂ) ^ y) := by
    intro x y hin
    rcases inP_mul ((isIntegral_natCast' a).pow x) ((isIntegral_natCast' b).pow y) hin with
      h1 | h1
    · exact hPa (inP_of_pow (isIntegral_natCast' a) h1).2
    · exact hPb (inP_of_pow (isIntegral_natCast' b) h1).2
  have side : ∀ f g : ℂ → ℕ, 0 < f r₀ → g r₀ = 0 → ∀ A B x y x' y' : ℕ, ∀ c : ℂ,
      IsOfFinOrder c →
      (∏ r ∈ S, (t5 - r) ^ f r) * t5 ^ A * ((a : ℂ) ^ x * (b : ℂ) ^ y) =
        c * (∏ r ∈ S, (t5 - r) ^ g r) * t5 ^ B * ((a : ℂ) ^ x' * (b : ℂ) ^ y') → False := by
    intro f g hf hg A B x y x' y' c hc heq
    have hL : InP P ((∏ r ∈ S, (t5 - r) ^ f r) * t5 ^ A * ((a : ℂ) ^ x * (b : ℂ) ^ y)) :=
      ((inP_prod_of_mem _ (fun r hr => hint r hr _) hr₀ (h0.pow hf)).mul_right
        (isIntegral_t5.pow A)).mul_right (hcI x y)
    rw [heq] at hL
    rcases inP_mul (((isIntegral_of_finOrder hc).mul (hprodI g)).mul (isIntegral_t5.pow B))
      (hcI x' y') hL with hL | hL
    · rcases inP_mul ((isIntegral_of_finOrder hc).mul (hprodI g)) (isIntegral_t5.pow B) hL with
        hL | hL
      · rcases inP_mul (isIntegral_of_finOrder hc) (hprodI g) hL with hL | hL
        · exact not_inP_root hc hL
        · obtain ⟨r, hr, hL⟩ := inP_prod S _ (fun r hr => hint r hr _) hL
          obtain ⟨hpos, hL⟩ := inP_of_pow (isIntegral_t5_sub (hS r hr)) hL
          by_cases hrr : r = r₀
          · rw [hrr, hg] at hpos
            exact lt_irrefl 0 hpos
          · exact hpriv r hr hrr hL
      · exact ht (inP_of_pow isIntegral_t5 hL).2
    · exact hcP x' y' hL
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1 : 0 < (-e r₀).toNat := by omega
    have h2 : (e r₀).toNat = 0 := by omega
    have hξ0 : ξ ≠ 0 := ne_zero_of_finOrder hξ
    refine side (fun r => (-e r).toNat) (fun r => (e r).toNat) h1 h2
      (∑ r ∈ S, (e r).toNat) (∑ r ∈ S, (-e r).toNat) m.toNat (-m).toNat (-m).toNat m.toNat
      ξ⁻¹ (isOfFinOrder_inv' hξ) ?_
    rw [mul_assoc ξ⁻¹, mul_assoc ξ⁻¹, hc]
    field_simp
  · have h1 : 0 < (e r₀).toNat := by omega
    have h2 : (-e r₀).toNat = 0 := by omega
    exact side (fun r => (e r).toNat) (fun r => (-e r).toNat) h1 h2 _ _ _ _ _ _ ξ hξ hc

/-! ## 2. The support theorem -/

/-- **The support theorem for a relation up to a power of `a/b`** (from `GoodPrimes5`). If no
prime other than 2 and 5 divides `a` or `b`, a relation `∏ (1 - r/t)^(e_r) = ξ (a/b)^m` is
supported on the two roots `1` and `-1`. -/
theorem support_subset_pm_one_rel5 (hG : GoodPrimes5) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 → Nat.Coprime a p ∧ Nat.Coprime b p)
    {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ}
    (h : IsRel5 (a : ℂ) (b : ℂ) S e m) : ∀ r ∈ S, r ≠ 1 → r ≠ -1 → e r = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set S' := S.filter (fun r => e r ≠ 0) with hS'def
  have hS' : ∀ r ∈ S', IsOfFinOrder r := fun r hr => hS r (Finset.mem_filter.1 hr).1
  have h' : IsRel5 (a : ℂ) (b : ℂ) S' e m := by
    obtain ⟨ξ, hξ, hrel⟩ := h
    refine ⟨ξ, hξ, ?_⟩
    rw [hS'def, Finset.prod_filter_of_ne (p := fun r => e r ≠ 0)
      (fun r _ hr hc => hr (by simp [hc]))]
    exact hrel
  set T := S'.filter (fun r => r ≠ 1 ∧ r ≠ -1) with hTdef
  have hT : T.Nonempty := by
    obtain ⟨r, hr, hr1, hrn, hre⟩ := hcon
    exact ⟨r, by simp [hTdef, hS'def, hr, hr1, hrn, hre]⟩
  obtain ⟨r, hrT, hmax⟩ := Finset.exists_max_image T orderOf hT
  have hrS' : r ∈ S' := (Finset.mem_filter.1 hrT).1
  have hr1 : r ≠ 1 := (Finset.mem_filter.1 hrT).2.1
  have hrn : r ≠ -1 := (Finset.mem_filter.1 hrT).2.2
  have her : e r ≠ 0 := (Finset.mem_filter.1 hrS').2
  have hr := hS' r hrS'
  obtain ⟨P, hP, p, hp, hp2, hp5, hpr, hpP, htr⟩ := hG r hr hr1 hrn
  -- `t ∉ P`: else `5 = t² ∈ P`, and `p ∈ P` is prime to 5
  have ht : ¬ InP P t5 := by
    intro ht
    have h2 := ht.mul_right isIntegral_t5
    rw [← pow_two, t5_sq] at h2
    have hcop : Nat.Coprime 5 p :=
      (Nat.coprime_primes Nat.prime_five hp).2 (Ne.symm hp5)
    exact not_inP_coprime (a := 5) (b := p) hcop (by exact_mod_cast h2) hpP
  have hPa : ¬ InP P (a : ℂ) := fun hin => not_inP_coprime (hab p hp hp2 hp5).1 hin hpP
  have hPb : ¬ InP P (b : ℂ) := fun hin => not_inP_coprime (hab p hp hp2 hp5).2 hin hpP
  refine her (coeff_eq_zero_of_private_ideal_rel5 ha hb hS' h' hrS' ht hPa hPb htr ?_)
  intro r' hr' hne htr'
  have hr'f := hS' r' hr'
  have hr0 : r ≠ 0 := ne_zero_of_finOrder hr
  set u := r' / r with hu
  have hufin : IsOfFinOrder u := isOfFinOrder_div' hr'f hr
  have hu1 : InP P (u - 1) := by
    have hd : InP P (r' - r) := by
      have := htr.sub htr'
      rwa [show t5 - r - (t5 - r') = r' - r by ring] at this
    have hrinv : IsIntegral ℤ r⁻¹ := isIntegral_of_finOrder (isOfFinOrder_inv' hr)
    have := hd.mul_right hrinv
    rwa [show (r' - r) * r⁻¹ = u - 1 by rw [hu]; field_simp] at this
  obtain ⟨k, hord⟩ := orderOf_eq_prime_pow_of_inP hp hpP hufin hu1
  have hk : 0 < k := by
    by_contra h0
    push Not at h0
    rw [Nat.le_zero.1 h0, pow_zero, orderOf_eq_one_iff, hu, div_eq_one_iff_eq hr0] at hord
    exact hne hord
  have hcop : Nat.Coprime (orderOf r) (orderOf u) := by
    rw [hord]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpr).symm
  have hr'eq : r' = r * u := by rw [hu]; field_simp
  have hordr' : orderOf r' = orderOf r * p ^ k := by
    rw [hr'eq, (Commute.all r u).orderOf_mul_eq_mul_orderOf_of_coprime hcop, hord]
  by_cases hr'pm : r' = 1 ∨ r' = -1
  · -- `1` and `-1` have order at most 2, which the odd prime `p` does not divide
    have h2 : orderOf r' ∣ 2 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rcases hr'pm with h1 | h1 <;> rw [h1] <;> norm_num
    have hp2' : p ∣ 2 := by
      refine Dvd.dvd.trans ?_ h2
      rw [hordr']
      exact Dvd.dvd.mul_left (dvd_pow_self p hk.ne') _
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2')
  · push Not at hr'pm
    have hle := hmax r' (Finset.mem_filter.2 ⟨hr', hr'pm⟩)
    rw [hordr'] at hle
    have : orderOf r * 1 < orderOf r * p ^ k :=
      Nat.mul_lt_mul_of_pos_left (Nat.one_lt_pow hk.ne' hp.one_lt) hr.orderOf_pos
    omega

/-! ## 3. The two roots `1` and `-1` -/

theorem norm_one_sub_inv_t5 : ‖1 - 1 / t5‖ = 1 - 1 / Real.sqrt 5 := by
  have e : (1 - 1 / t5 : ℂ) = ((1 - 1 / Real.sqrt 5 : ℝ) : ℂ) := by
    rw [t5]
    push_cast
    rfl
  rw [e, Complex.norm_real, Real.norm_of_nonneg one_sub_inv_sqrt5_pos.le]

theorem norm_one_add_inv_t5 : ‖1 - (-1) / t5‖ = 1 + 1 / Real.sqrt 5 := by
  have e : (1 - (-1) / t5 : ℂ) = ((1 + 1 / Real.sqrt 5 : ℝ) : ℂ) := by
    rw [t5]
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_of_nonneg one_add_inv_sqrt5_pos.le]

/-- **The reduction** (from `GoodPrimes5`). If no prime other than 2 and 5 divides `a` or
`b`, a relation `∏ (1 - r/t)^(e_r) = ξ (a/b)^m` gives `(4/5)^s = (a/b)^(2m)` for some integer
`s`. -/
theorem rel5_reduce (hG : GoodPrimes5) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 → Nat.Coprime a p ∧ Nat.Coprime b p)
    {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ}
    (h : IsRel5 (a : ℂ) (b : ℂ) S e m) :
    ∃ s : ℤ, (4 / 5 : ℝ) ^ s = ((a : ℝ) / b) ^ (2 * m) := by
  classical
  have hsupp := support_subset_pm_one_rel5 hG ha hb hab hS h
  obtain ⟨ξ, hξ, hrel⟩ := h
  have hq : (0 : ℝ) < (a : ℝ) / b := by positivity
  -- absolute values
  have h1 := congrArg norm hrel
  rw [norm_prod] at h1
  simp only [norm_zpow, norm_mul, norm_div, Complex.norm_natCast, norm_root hξ, one_mul] at h1
  -- only the two roots `1` and `-1` are left
  obtain ⟨E, hEdef⟩ : ∃ E : ℂ → ℤ, E = fun r => if r ∈ S then e r else 0 := ⟨_, rfl⟩
  have hEin : ∀ r ∈ S, E r = e r := fun r hr => by rw [hEdef]; simp [hr]
  have hEout : ∀ r, r ∉ S → E r = 0 := fun r hr => by rw [hEdef]; simp [hr]
  have hE0 : ∀ r, r ≠ 1 → r ≠ -1 → E r = 0 := by
    intro r hr1 hrn
    by_cases hr : r ∈ S
    · rw [hEin r hr]
      exact hsupp r hr hr1 hrn
    · exact hEout r hr
  have hA : ∏ r ∈ S, ‖1 - r / t5‖ ^ e r = ∏ r ∈ S ∪ {1, -1}, ‖1 - r / t5‖ ^ E r := by
    rw [← Finset.prod_subset Finset.subset_union_left
      (f := fun r => ‖1 - r / t5‖ ^ E r) (fun r _ hr => by rw [hEout r hr, zpow_zero])]
    exact Finset.prod_congr rfl fun r hr => by rw [hEin r hr]
  have hB : ∏ r ∈ ({1, -1} : Finset ℂ), ‖1 - r / t5‖ ^ E r =
      ∏ r ∈ S ∪ {1, -1}, ‖1 - r / t5‖ ^ E r :=
    Finset.prod_subset Finset.subset_union_right fun r _ hr => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
      rw [hE0 r hr.1 hr.2, zpow_zero]
  have h1n : (1 : ℂ) ≠ -1 := by norm_num
  rw [hA, ← hB, Finset.prod_pair h1n, norm_one_sub_inv_t5, norm_one_add_inv_t5] at h1
  -- logarithms
  have hx1 := one_sub_inv_sqrt5_pos
  have hx2 := one_add_inv_sqrt5_pos
  have hl := congrArg Real.log h1
  rw [Real.log_mul (zpow_ne_zero _ hx1.ne') (zpow_ne_zero _ hx2.ne'), Real.log_zpow,
    Real.log_zpow, Real.log_zpow] at hl
  have key : ((E 1 + E (-1) : ℤ) : ℝ) * Real.log (4 / 5) +
      ((E (-1) - E 1 : ℤ) : ℝ) * Real.log ((3 + Real.sqrt 5) / 2) =
        ((2 * m : ℤ) : ℝ) * Real.log ((a : ℝ) / b) := by
    push_cast
    linear_combination 2 * hl - ((E 1 : ℝ) + E (-1)) * log_one_sub_add_log_one_add -
      ((E (-1) : ℝ) - E 1) * log_one_add_inv_sqrt5
  have hz : ∀ (x : ℝ), 0 < x → ∀ n : ℤ, Real.exp (n * Real.log x) = x ^ n :=
    fun x hx n => by rw [mul_comm, Real.exp_mul, Real.exp_log hx, Real.rpow_intCast]
  have hexp : (4 / 5 : ℝ) ^ (E 1 + E (-1)) * ((3 + Real.sqrt 5) / 2) ^ (E (-1) - E 1) =
      ((a : ℝ) / b) ^ (2 * m) := by
    have h' := congrArg Real.exp key
    rw [Real.exp_add, hz _ (by norm_num), hz _ phiSq_pos, hz _ hq] at h'
    exact h'
  -- the power of the golden ratio is rational, so its exponent is zero
  have hC : E (-1) - E 1 = 0 := by
    by_contra hC
    apply irrational_phiSq_zpow hC
    refine ⟨((a : ℚ) / b) ^ (2 * m) * (4 / 5 : ℚ) ^ (-(E 1 + E (-1))), ?_⟩
    have h45 : (4 / 5 : ℝ) ^ (E 1 + E (-1)) ≠ 0 := zpow_ne_zero _ (by norm_num)
    push_cast
    rw [zpow_neg, ← hexp]
    field_simp
  rw [hC, zpow_zero, mul_one] at hexp
  exact ⟨_, hexp⟩

/-! ## 4. `4^x = 5^y` only for `x = y = 0` -/

theorem four_pow_ne_five_pow {x y : ℕ} (hx : 0 < x) : (4 : ℕ) ^ x ≠ 5 ^ y := by
  intro h
  have h2 : 2 ∣ (4 : ℕ) ^ x := dvd_pow (by norm_num) hx.ne'
  rw [h] at h2
  have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
  omega

theorem four_zpow_eq_five_zpow {x y : ℤ} (h : (4 : ℝ) ^ x = 5 ^ y) : x = 0 ∧ y = 0 := by
  have key : ∀ n k : ℕ, (4 : ℝ) ^ n = 5 ^ k → n = 0 ∧ k = 0 := by
    intro n k hnk
    have h' : (4 : ℕ) ^ n = 5 ^ k := by exact_mod_cast hnk
    have hn : n = 0 := by
      by_contra hn
      exact four_pow_ne_five_pow (Nat.pos_of_ne_zero hn) h'
    subst hn
    refine ⟨rfl, ?_⟩
    by_contra hk
    have h1 : 1 < 5 ^ k := Nat.one_lt_pow hk (by norm_num)
    rw [pow_zero] at h'
    omega
  have key2 : ∀ n k : ℕ, (4 : ℝ) ^ n * 5 ^ k = 1 → n = 0 ∧ k = 0 := by
    intro n k hnk
    have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    have h5 : (1 : ℝ) ≤ 5 ^ k := one_le_pow₀ (by norm_num)
    constructor
    · by_contra hn
      have h4' : (1 : ℝ) < 4 ^ n := one_lt_pow₀ (by norm_num) hn
      nlinarith
    · by_contra hk
      have h5' : (1 : ℝ) < 5 ^ k := one_lt_pow₀ (by norm_num) hk
      nlinarith
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg x <;> obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · rw [zpow_natCast, zpow_natCast] at h
    obtain ⟨h1, h2⟩ := key n k h
    omega
  · rw [zpow_natCast, zpow_neg, zpow_natCast] at h
    have h' : (4 : ℝ) ^ n * 5 ^ k = 1 := by
      rw [h]
      exact inv_mul_cancel₀ (by positivity)
    obtain ⟨h1, h2⟩ := key2 n k h'
    omega
  · rw [zpow_neg, zpow_natCast, zpow_natCast] at h
    have h' : (4 : ℝ) ^ n * 5 ^ k = 1 := by
      rw [← h]
      exact mul_inv_cancel₀ (by positivity)
    obtain ⟨h1, h2⟩ := key2 n k h'
    omega
  · rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, inv_inj] at h
    obtain ⟨h1, h2⟩ := key n k h
    omega

/-! ## 5. `log 5` and `log 2` are not values -/

/-- **`log 5` is not the value of any series of the class F5** (from Baker's theorem and good
primes). -/
theorem not_isF5Value_log_five_of_goodPrimes5 (hB : BakerTheorem) (hG : GoodPrimes5) :
    ¬ IsF5Value (Real.log 5) := by
  intro h
  have h' : IsF5Value (Real.log (((5 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) := by
    have e : (((5 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) = 5 := by norm_num
    rwa [e]
  obtain ⟨S, hS, e, m, hm, hrel⟩ :=
    exists_rel5_of_isF5Value_log hB (by norm_num) one_pos h'
  have hab : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 → Nat.Coprime 5 p ∧ Nat.Coprime 1 p :=
    fun p hp _ hp5 =>
      ⟨(Nat.coprime_primes Nat.prime_five hp).2 (Ne.symm hp5), Nat.coprime_one_left p⟩
  obtain ⟨s, hs⟩ := rel5_reduce hG (by norm_num) one_pos hab hS hrel
  -- `(4/5)^s = 5^(2m)`, so `4^s = 5^(2m + s)`
  have h4 : (4 : ℝ) ^ s = 5 ^ (2 * m + s) := by
    rw [zpow_add₀ (by norm_num : (5 : ℝ) ≠ 0)]
    have h5 : (5 : ℝ) ^ s ≠ 0 := zpow_ne_zero _ (by norm_num)
    rw [div_zpow, div_eq_iff h5] at hs
    rw [hs]
    norm_num
  obtain ⟨h1, h2⟩ := four_zpow_eq_five_zpow h4
  omega

/-- **`log 2` is not the value of any series of the class F5** (from Baker's theorem and good
primes). -/
theorem not_isF5Value_log_two_of_goodPrimes5 (hB : BakerTheorem) (hG : GoodPrimes5) :
    ¬ IsF5Value (Real.log 2) := by
  intro h
  have h' : IsF5Value (Real.log (((2 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) := by
    have e : (((2 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) = 2 := by norm_num
    rwa [e]
  obtain ⟨S, hS, e, m, hm, hrel⟩ :=
    exists_rel5_of_isF5Value_log hB (by norm_num) one_pos h'
  have hab : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 → Nat.Coprime 2 p ∧ Nat.Coprime 1 p :=
    fun p hp hp2 _ =>
      ⟨(Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2), Nat.coprime_one_left p⟩
  obtain ⟨s, hs⟩ := rel5_reduce hG (by norm_num) one_pos hab hS hrel
  -- `(4/5)^s = 2^(2m) = 4^m`, so `4^(s - m) = 5^s`
  have h4 : (4 : ℝ) ^ (s - m) = 5 ^ s := by
    have h5 : (5 : ℝ) ^ s ≠ 0 := zpow_ne_zero _ (by norm_num)
    have h4m : (4 : ℝ) ^ m ≠ 0 := zpow_ne_zero _ (by norm_num)
    have e2 : (((2 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ (2 * m) = (4 : ℝ) ^ m := by
      rw [zpow_mul]
      norm_num
    rw [e2, div_zpow, div_eq_iff h5] at hs
    rw [zpow_sub₀ (by norm_num : (4 : ℝ) ≠ 0), hs]
    field_simp
  obtain ⟨h1, h2⟩ := four_zpow_eq_five_zpow h4
  omega

end Base5

end PiFormula
