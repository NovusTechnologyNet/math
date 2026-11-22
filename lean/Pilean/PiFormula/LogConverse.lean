import Pilean.PiFormula.LogCriterion

/-!
# Which logarithms are values of the class F: the converse (Theorem K, second half)

`LogCriterion.lean` proves that every rational combination of `log 2` and the numbers
`log N((1+i)^n - c)` is a value of the class F (`logSpan_le_fValues`). This file proves the
converse for logarithms of rational numbers, from Baker's theorem:

* `mem_logSpan_of_isFValue_log`: if `log (a/b)` is a value of the class F, then it is such a
  rational combination;
* `isFValue_log_iff`, `isFValue_log_rat_iff`, `isFValue_log_nat_iff`: the criterion.

The proof. By Baker's theorem (`baker_no_extra`), a formula for `log (a/b)` forces a
multiplicative relation `∏ (1 - r/t)^(e_r) = ξ (a/b)^m` with `m ≠ 0`, over roots of unity
`r`, with `ξ` a root of unity and `t = 1 + i`. Cleared of denominators it is an identity
between two products of the `t - r`, of powers of `t` and of integers (`cleared_upToQ`).

Such an identity is the value at `ζ = exp(2πi/N)` of an identity between polynomials with
integer coefficients (`i = ζ^(N/4)`), so it stays true when `ζ` is replaced by `ζ^a` with `a`
prime to `N` (`aeval_pow_of_coprime`): the two have the same minimal polynomial. For
`a ≡ 1 (mod 4)` this fixes `i`, hence `t`, and sends every `r` to `r^a` (`cleared_conj`).

Taking logarithms of absolute values and adding over all such `a`, the number
`m log (a/b)` becomes a combination with integer coefficients of `log 2` and the sums
`∑_a log |t - r^a|`. Each of these sums is a combination of numbers `log |t^M - c|` with
`c^4 = 1`: by Möbius inversion over the condition "`a` prime to `N`" it is a combination of
sums over full cosets `{u^j x}`, and such a coset is the set of roots of `X^M = x^M`
(`sum_log_coset_mem`, `sum_log_mod_four_mem`, `sum_log_coprime_mem`).
-/

open Complex Polynomial

namespace PiFormula

/-! ## 1. Conjugating an identity between roots of unity -/

/-- A polynomial with integer coefficients that vanishes at a primitive `N`-th root of unity
`ζ` vanishes at `ζ^a` for every `a` prime to `N`. -/
theorem aeval_pow_of_coprime {ζ : ℂ} {N : ℕ} (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N)
    {F : ℤ[X]} (hF : aeval ζ F = 0) {a : ℕ} (ha : a.Coprime N) : aeval (ζ ^ a) F = 0 := by
  obtain ⟨G, rfl⟩ := minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hN) hF
  rw [map_mul, hζ.minpoly_eq_pow_coprime ha, minpoly.aeval, zero_mul]

/-- `ζ_{4K}^K = i`. -/
theorem zetaN_pow_quarter {K : ℕ} (hK : 0 < K) : zetaN (4 * K) ^ K = I := by
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have e : (K : ℂ) * (2 * Real.pi * I / ((4 * K : ℕ) : ℂ)) = (Real.pi / 2 : ℂ) * I := by
    push_cast
    field_simp
    ring
  rw [zetaN, ← Complex.exp_nat_mul, e, Complex.exp_mul_I, Complex.cos_pi_div_two,
    Complex.sin_pi_div_two, zero_add, one_mul]

/-- **Conjugating a cleared relation.** An identity between products of the `t - r` (`r` roots
of unity), powers of `t = 1 + i` and integers, up to a root of unity `ξ`, stays true when
every `r` and `ξ` are raised to a power `a` prime to their orders with `a ≡ 1 (mod 4)`. -/
theorem cleared_conj {S : Finset ℂ} {ξ : ℂ} (p n : ℂ → ℕ) (A B c₁ c₂ : ℕ) {K : ℕ}
    (hK : 0 < K) (hSK : ∀ r ∈ S, r ^ (4 * K) = 1) (hξK : ξ ^ (4 * K) = 1)
    (h : (∏ r ∈ S, (tC - r) ^ p r) * tC ^ A * (c₁ : ℂ) =
      ξ * (∏ r ∈ S, (tC - r) ^ n r) * tC ^ B * (c₂ : ℂ))
    {a : ℕ} (ha : a.Coprime (4 * K)) (ha4 : a % 4 = 1) :
    (∏ r ∈ S, (tC - r ^ a) ^ p r) * tC ^ A * (c₁ : ℂ) =
      ξ ^ a * (∏ r ∈ S, (tC - r ^ a) ^ n r) * tC ^ B * (c₂ : ℂ) := by
  classical
  have hN0 : 0 < 4 * K := by omega
  have : NeZero (4 * K) := ⟨hN0.ne'⟩
  set ζ := zetaN (4 * K) with hζdef
  have hζ : IsPrimitiveRoot ζ (4 * K) := zetaN_prim hN0
  have hζK : ζ ^ K = I := zetaN_pow_quarter hK
  have hex : ∀ r ∈ S, ∃ k : ℕ, ζ ^ k = r := fun r hr => by
    obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (hSK r hr)
    exact ⟨k, hk⟩
  choose! kf hkf using hex
  obtain ⟨b, -, hb⟩ := hζ.eq_pow_of_pow_eq_one hξK
  let τ : ℤ[X] := 1 + X ^ K
  let F : ℤ[X] := (∏ r ∈ S, (τ - X ^ kf r) ^ p r) * τ ^ A * (c₁ : ℤ[X]) -
    X ^ b * (∏ r ∈ S, (τ - X ^ kf r) ^ n r) * τ ^ B * (c₂ : ℤ[X])
  have hev : ∀ z : ℂ, aeval z F =
      (∏ r ∈ S, ((1 + z ^ K) - z ^ kf r) ^ p r) * (1 + z ^ K) ^ A * (c₁ : ℂ) -
        z ^ b * (∏ r ∈ S, ((1 + z ^ K) - z ^ kf r) ^ n r) * (1 + z ^ K) ^ B * (c₂ : ℂ) :=
    fun z => by
      simp only [F, τ, map_sub, map_mul, map_prod, map_pow, map_add, map_one, aeval_X,
        map_natCast]
  have h0 : aeval ζ F = 0 := by
    rw [hev, hζK, sub_eq_zero]
    have e : ∀ q : ℂ → ℕ, ∏ r ∈ S, ((1 + I) - ζ ^ kf r) ^ q r = ∏ r ∈ S, (tC - r) ^ q r :=
      fun q => Finset.prod_congr rfl fun r hr => by rw [hkf r hr]; rfl
    rw [e, e, hb]
    exact h
  have h1 := aeval_pow_of_coprime hN0 hζ h0 ha
  have hI : (ζ ^ a) ^ K = I := by
    rw [← pow_mul, mul_comm, pow_mul, hζK, I_pow_of_mod_four ha4]
  rw [hev, sub_eq_zero, hI] at h1
  have e : ∀ q : ℂ → ℕ,
      ∏ r ∈ S, ((1 + I) - (ζ ^ a) ^ kf r) ^ q r = ∏ r ∈ S, (tC - r ^ a) ^ q r :=
    fun q => Finset.prod_congr rfl fun r hr => by
      rw [← pow_mul, mul_comm, pow_mul, hkf r hr]; rfl
  rw [e, e, ← pow_mul, mul_comm a b, pow_mul, hb] at h1
  exact h1

/-! ## 2. Sums of `log |t - r|` over a coset of roots of unity -/

theorem rat_mul_mem_logSpan {x : ℝ} (hx : x ∈ logSpan) (q : ℚ) : (q : ℝ) * x ∈ logSpan := by
  have h := logSpan.smul_mem q hx
  rwa [Rat.smul_def] at h

theorem log_two_mem_logSpan : Real.log 2 ∈ logSpan := Submodule.subset_span (Or.inl rfl)

theorem log_norm_tC_mem_logSpan : Real.log ‖tC‖ ∈ logSpan := by
  have h := rat_mul_mem_logSpan log_two_mem_logSpan (1 / 2)
  rw [log_norm_tC]
  convert h using 1
  push_cast
  ring

/-- A fourth root of unity is a unit of `ℤ[i]`. -/
theorem exists_gaussian_of_pow_four {w : ℂ} (hw : w ^ 4 = 1) :
    ∃ c : GaussianInt, c ^ 4 = 1 ∧ (c : ℂ) = w := by
  have h : (w - 1) * (w + 1) * (w - I) * (w + I) = 0 := by
    linear_combination hw - (w ^ 2 - 1) * Complex.I_sq
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact ⟨1, one_pow 4, by rw [map_one]; exact (sub_eq_zero.1 h).symm⟩
      · exact ⟨-1, neg_one_pow_four', by
          rw [map_neg, map_one]; exact (eq_neg_of_add_eq_zero_left h).symm⟩
    · exact ⟨gI, gI_pow_four, by rw [gI_cast]; exact (sub_eq_zero.1 h).symm⟩
  · exact ⟨-gI, negI_pow_four, by
      rw [map_neg, gI_cast]; exact (eq_neg_of_add_eq_zero_left h).symm⟩

/-- `log |t^n - w|` is in the span, for `n ≥ 1` and `w^4 = 1`. -/
theorem log_norm_tC_pow_sub_mem {n : ℕ} (hn : 0 < n) {w : ℂ} (hw : w ^ 4 = 1) :
    Real.log ‖tC ^ n - w‖ ∈ logSpan := by
  obtain ⟨c, hc, rfl⟩ := exists_gaussian_of_pow_four hw
  have e : tC ^ n - (c : ℂ) = ((tG ^ n - c : GaussianInt) : ℂ) := by
    rw [map_sub, map_pow, tG_toComplex]
  have hg : Real.log (((tG ^ n - c).norm : ℤ) : ℝ) ∈ logSpan :=
    Submodule.subset_span (Or.inr ⟨n, c, hn, hc, rfl⟩)
  have h := rat_mul_mem_logSpan hg (1 / 2)
  rw [e, log_norm_toComplex]
  convert h using 1
  push_cast
  ring

/-- **A full coset.** `∑_{c < L} log |t - u^c x|` is in the span when `u^L = 1` and `x^M` is a
fourth root of unity, `M` the order of `u`: the `u^c x` are the roots of `X^M = x^M`, each
`L/M` times. -/
theorem sum_log_coset_mem {u x₀ : ℂ} {L : ℕ} (hL : 0 < L) (hu : u ^ L = 1) (hx : ‖x₀‖ = 1)
    (hx4 : (x₀ ^ orderOf u) ^ 4 = 1) :
    ∑ c ∈ Finset.range L, Real.log ‖tC - u ^ c * x₀‖ ∈ logSpan := by
  have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.2 ⟨L, hL, hu⟩
  have hM0 : 0 < orderOf u := hfin.orderOf_pos
  have hprim : IsPrimitiveRoot u (orderOf u) := IsPrimitiveRoot.orderOf u
  obtain ⟨k, rfl⟩ : orderOf u ∣ L := orderOf_dvd_of_pow_eq_one hu
  have hun : ‖u‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hu hL.ne'
  have hne : ∀ c : ℕ, tC - u ^ c * x₀ ≠ 0 := fun c =>
    tC_sub_ne_zero (by rw [norm_mul, norm_pow, hun, one_pow, one_mul, hx])
  have hone : ∑ c ∈ Finset.range (orderOf u), Real.log ‖tC - u ^ c * x₀‖ =
      Real.log ‖tC ^ orderOf u - x₀ ^ orderOf u‖ := by
    have h1 := zO_nthRoots hM0 (x₀ ^ orderOf u)
    rw [hprim.nthRoots_eq rfl, zO, Multiset.map_map] at h1
    rw [← h1, ← Finset.range_val, ← Finset.prod_eq_multiset_prod, norm_prod, Real.log_prod]
    · rfl
    · intro c _
      exact norm_ne_zero_iff.2 (hne c)
  have hper : ∀ j c : ℕ, u ^ (orderOf u * j + c) = u ^ c := fun j c => by
    rw [pow_add, pow_mul, pow_orderOf_eq_one, one_pow, one_mul]
  have hsum : ∀ j : ℕ, ∑ c ∈ Finset.range (orderOf u * j), Real.log ‖tC - u ^ c * x₀‖ =
      j • Real.log ‖tC ^ orderOf u - x₀ ^ orderOf u‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul, ← hone]
      congr 1
      exact Finset.sum_congr rfl fun c _ => by rw [hper]
  rw [hsum]
  exact nsmul_mem (log_norm_tC_pow_sub_mem hM0 hx4) k

/-- **Exponents in one class modulo 4.** `∑ log |t - s^b|` over the `b < 4K` with
`b ≡ ρ₀ (mod 4)` is in the span, when `s^(4K) = 1`. -/
theorem sum_log_mod_four_mem {s : ℂ} {K : ℕ} (hK : 0 < K) (hs : s ^ (4 * K) = 1) {ρ₀ : ℕ}
    (hρ₀ : ρ₀ < 4) :
    ∑ b ∈ (Finset.range (4 * K)).filter (fun b => b % 4 = ρ₀), Real.log ‖tC - s ^ b‖ ∈
      logSpan := by
  have hsn : ‖s‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hs (by omega)
  have e : ∑ b ∈ (Finset.range (4 * K)).filter (fun b => b % 4 = ρ₀), Real.log ‖tC - s ^ b‖ =
      ∑ c ∈ Finset.range K, Real.log ‖tC - (s ^ 4) ^ c * s ^ ρ₀‖ := by
    refine Finset.sum_nbij' (fun b => b / 4) (fun c => 4 * c + ρ₀) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
      omega
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_range] at hc ⊢
      omega
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      omega
    · intro c _
      omega
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      have hsb : s ^ b = (s ^ 4) ^ (b / 4) * s ^ ρ₀ := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [hsb]
  rw [e]
  refine sum_log_coset_mem hK (by rw [← pow_mul]; exact hs) (by rw [norm_pow, hsn, one_pow]) ?_
  have h1 : ((s ^ ρ₀) ^ orderOf (s ^ 4)) ^ 4 = ((s ^ 4) ^ orderOf (s ^ 4)) ^ ρ₀ := by ring
  rw [h1, pow_orderOf_eq_one, one_pow]

/-! ## 3. Exponents prime to `N`: Möbius inversion -/

/-- `∑_{d ∣ N, d ∣ a} μ(d)` is 1 if `a` is prime to `N`, and 0 otherwise. -/
theorem sum_moebius_dvd {N : ℕ} (hN : 0 < N) (a : ℕ) :
    (∑ d ∈ N.divisors, if d ∣ a then ArithmeticFunction.moebius d else 0) =
      if a.Coprime N then 1 else 0 := by
  have h1 : ∑ d ∈ (Nat.gcd a N).divisors, ArithmeticFunction.moebius d =
      if Nat.gcd a N = 1 then 1 else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply]
  have h2 : (Nat.gcd a N).divisors = N.divisors.filter (fun d => d ∣ a) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff, ne_eq,
      Nat.gcd_eq_zero_iff, hN.ne', and_false, not_false_eq_true, and_true]
    tauto
  rw [← Finset.sum_filter, ← h2, h1]

/-- A sum over the elements prime to `N`, as a combination of the sums over the multiples of
the divisors `d` of `N`. -/
theorem sum_filter_coprime {N : ℕ} (hN : 0 < N) (P : Finset ℕ) (g : ℕ → ℝ) :
    ∑ a ∈ P.filter (fun a => a.Coprime N), g a =
      ∑ d ∈ N.divisors,
        ArithmeticFunction.moebius d • ∑ a ∈ P.filter (fun a => d ∣ a), g a := by
  calc ∑ a ∈ P.filter (fun a => a.Coprime N), g a
      = ∑ a ∈ P, (if a.Coprime N then (1 : ℤ) else 0) • g a := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        split_ifs <;> simp
    _ = ∑ a ∈ P, ∑ d ∈ N.divisors,
          (if d ∣ a then ArithmeticFunction.moebius d else 0) • g a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← sum_moebius_dvd hN a, Finset.sum_smul]
    _ = ∑ d ∈ N.divisors, ∑ a ∈ P,
          (if d ∣ a then ArithmeticFunction.moebius d else 0) • g a := Finset.sum_comm
    _ = ∑ d ∈ N.divisors,
          ArithmeticFunction.moebius d • ∑ a ∈ P.filter (fun a => d ∣ a), g a := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.smul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        split_ifs <;> simp

theorem mul_mod_four_eq_one {d b : ℕ} (hd : d % 2 = 1) : d * b % 4 = 1 ↔ b % 4 = d % 4 := by
  rw [Nat.mul_mod]
  have h1 : d % 4 = 1 ∨ d % 4 = 3 := by omega
  have h2 : b % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize b % 4 = x at h2 ⊢
  rcases h1 with h | h <;> rw [h] <;> interval_cases x <;> simp

/-- **The orbit of a root of unity.** `∑ log |t - r^a|` over the `a < 4K` prime to `4K` with
`a ≡ 1 (mod 4)` is in the span, when `r^(4K) = 1`. -/
theorem sum_log_coprime_mem {r : ℂ} {K : ℕ} (hK : 0 < K) (hr : r ^ (4 * K) = 1) :
    ∑ a ∈ (Finset.range (4 * K)).filter (fun a => a % 4 = 1 ∧ a.Coprime (4 * K)),
      Real.log ‖tC - r ^ a‖ ∈ logSpan := by
  have hN : 0 < 4 * K := by omega
  rw [← Finset.filter_filter, sum_filter_coprime hN]
  refine Submodule.sum_mem _ fun d hd => zsmul_mem ?_ _
  have hdN : d ∣ 4 * K := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rcases Nat.even_or_odd d with he | ho
  · -- an even `d` has no multiple `≡ 1 (mod 4)`
    have hempty : ((Finset.range (4 * K)).filter (fun a => a % 4 = 1)).filter
        (fun a => d ∣ a) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun a ha hda => ?_
      have h2 : 2 ∣ a := (even_iff_two_dvd.1 he).trans hda
      have h4 := (Finset.mem_filter.1 ha).2
      omega
    rw [hempty, Finset.sum_empty]
    exact zero_mem _
  · have hd2 : d % 2 = 1 := Nat.odd_iff.1 ho
    have hcop : Nat.Coprime d 4 :=
      Nat.Coprime.mul_right (Nat.coprime_two_right.2 ho) (Nat.coprime_two_right.2 ho)
    obtain ⟨K', rfl⟩ : d ∣ K := hcop.dvd_of_dvd_mul_left hdN
    have hK' : 0 < K' := Nat.pos_of_mul_pos_left hK
    have e : ∑ a ∈ ((Finset.range (4 * (d * K'))).filter (fun a => a % 4 = 1)).filter
          (fun a => d ∣ a), Real.log ‖tC - r ^ a‖ =
        ∑ b ∈ (Finset.range (4 * K')).filter (fun b => b % 4 = d % 4),
          Real.log ‖tC - (r ^ d) ^ b‖ := by
      refine Finset.sum_nbij' (fun a => a / d) (fun b => d * b) ?_ ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
        obtain ⟨⟨ha1, ha2⟩, b, rfl⟩ := ha
        rw [Nat.mul_div_cancel_left b hd0]
        refine ⟨?_, (mul_mod_four_eq_one hd2).1 ha2⟩
        have h3 : d * b < d * (4 * K') := by
          rw [show d * (4 * K') = 4 * (d * K') by ring]
          exact ha1
        exact Nat.lt_of_mul_lt_mul_left h3
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
        refine ⟨⟨?_, (mul_mod_four_eq_one hd2).2 hb.2⟩, Dvd.intro b rfl⟩
        rw [show 4 * (d * K') = d * (4 * K') by ring]
        exact Nat.mul_lt_mul_of_pos_left hb.1 hd0
      · intro a ha
        simp only [Finset.mem_filter] at ha
        exact Nat.mul_div_cancel' ha.2
      · intro b _
        exact Nat.mul_div_cancel_left b hd0
      · intro a ha
        simp only [Finset.mem_filter] at ha
        rw [← pow_mul, Nat.mul_div_cancel' ha.2]
    rw [e]
    refine sum_log_mod_four_mem hK' ?_ (Nat.mod_lt _ (by norm_num))
    rw [← pow_mul, show d * (4 * K') = 4 * (d * K') by ring]
    exact hr

/-! ## 4. From a cleared relation to the span -/

/-- Logarithms of an identity between products of positive numbers. -/
theorem log_identity_of_prod_eq {S : Finset ℂ} {x : ℂ → ℝ} (hx : ∀ r ∈ S, 0 < x r) {T : ℝ}
    (hT : 0 < T) (p n : ℂ → ℕ) (A B : ℕ) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h : (∏ r ∈ S, x r ^ p r) * T ^ A * c₁ = (∏ r ∈ S, x r ^ n r) * T ^ B * c₂) :
    Real.log c₁ - Real.log c₂ =
      ∑ r ∈ S, ((n r : ℝ) - p r) * Real.log (x r) + ((B : ℝ) - A) * Real.log T := by
  have hP1 : 0 < ∏ r ∈ S, x r ^ p r := Finset.prod_pos fun r hr => pow_pos (hx r hr) _
  have hP2 : 0 < ∏ r ∈ S, x r ^ n r := Finset.prod_pos fun r hr => pow_pos (hx r hr) _
  have hl := congrArg Real.log h
  rw [Real.log_mul (mul_pos hP1 (pow_pos hT A)).ne' hc₁.ne',
    Real.log_mul hP1.ne' (pow_pos hT A).ne',
    Real.log_mul (mul_pos hP2 (pow_pos hT B)).ne' hc₂.ne',
    Real.log_mul hP2.ne' (pow_pos hT B).ne',
    Real.log_prod (fun r hr => (pow_pos (hx r hr) _).ne'),
    Real.log_prod (fun r hr => (pow_pos (hx r hr) _).ne'), Real.log_pow, Real.log_pow] at hl
  simp only [Real.log_pow] at hl
  simp only [sub_mul, Finset.sum_sub_distrib]
  linarith

/-- **The key lemma.** From an identity
`∏ (t - r)^(p_r) · t^A · c₁ = ξ · ∏ (t - r)^(n_r) · t^B · c₂` between roots of unity `r`, `ξ`
and positive integers `c₁`, `c₂`, the number `log c₁ - log c₂` is a rational combination of
`log 2` and the numbers `log N((1+i)^n - c)`. -/
theorem log_sub_mem_logSpan_of_cleared {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {ξ : ℂ} (hξ : IsOfFinOrder ξ) (p n : ℂ → ℕ) (A B : ℕ) {c₁ c₂ : ℕ} (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂)
    (h : (∏ r ∈ S, (tC - r) ^ p r) * tC ^ A * (c₁ : ℂ) =
      ξ * (∏ r ∈ S, (tC - r) ^ n r) * tC ^ B * (c₂ : ℂ)) :
    Real.log c₁ - Real.log c₂ ∈ logSpan := by
  classical
  -- a common multiple `4K` of the orders
  set K := (∏ r ∈ S, orderOf r) * orderOf ξ with hKdef
  have hK : 0 < K :=
    Nat.mul_pos (Finset.prod_pos fun r hr => (hS r hr).orderOf_pos) hξ.orderOf_pos
  have hSK : ∀ r ∈ S, r ^ (4 * K) = 1 := fun r hr =>
    orderOf_dvd_iff_pow_eq_one.1
      (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hr) _) 4)
  have hξK : ξ ^ (4 * K) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Dvd.dvd.mul_left (Dvd.intro_left _ rfl) 4)
  have hξn : ‖ξ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hξK (by omega)
  set G := (Finset.range (4 * K)).filter (fun a => a % 4 = 1 ∧ a.Coprime (4 * K)) with hG
  have h1G : 1 ∈ G := by
    rw [hG, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, rfl, Nat.coprime_one_left _⟩
  have hT : 0 < ‖tC‖ := norm_pos_iff.2 tC_ne_zero
  -- the identity for every conjugate, in logarithms
  have hlog : ∀ a ∈ G, Real.log c₁ - Real.log c₂ =
      ∑ r ∈ S, ((n r : ℝ) - p r) * Real.log ‖tC - r ^ a‖ +
        ((B : ℝ) - A) * Real.log ‖tC‖ := by
    intro a ha
    obtain ⟨-, ha4, hac⟩ := Finset.mem_filter.1 ha
    have h2 := cleared_conj p n A B c₁ c₂ hK hSK hξK h hac ha4
    have h3 := congrArg norm h2
    simp only [norm_mul, norm_pow, norm_prod, Complex.norm_natCast, hξn, one_pow,
      one_mul] at h3
    refine log_identity_of_prod_eq (x := fun r => ‖tC - r ^ a‖) (fun r hr => ?_) hT p n A B
      (by exact_mod_cast hc₁) (by exact_mod_cast hc₂) h3
    refine norm_pos_iff.2 (tC_sub_ne_zero ?_)
    rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one (hSK r hr) (by omega), one_pow]
  -- adding over the conjugates
  have hsum : (G.card : ℝ) * (Real.log c₁ - Real.log c₂) =
      ∑ r ∈ S, ((n r : ℝ) - p r) * ∑ a ∈ G, Real.log ‖tC - r ^ a‖ +
        (G.card : ℝ) * (((B : ℝ) - A) * Real.log ‖tC‖) := by
    have h4 := Finset.sum_congr (rfl : G = G) hlog
    rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib, Finset.sum_comm,
      Finset.sum_const, nsmul_eq_mul] at h4
    rw [h4]
    simp only [Finset.mul_sum]
  have hmem : (G.card : ℝ) * (Real.log c₁ - Real.log c₂) ∈ logSpan := by
    rw [hsum]
    refine add_mem (Submodule.sum_mem _ fun r hr => ?_) ?_
    · have h5 := rat_mul_mem_logSpan (sum_log_coprime_mem hK (hSK r hr)) ((n r : ℚ) - p r)
      have e : (((n r : ℚ) - p r : ℚ) : ℝ) = (n r : ℝ) - p r := by push_cast; ring
      rw [e] at h5
      exact h5
    · have h5 := rat_mul_mem_logSpan
        (rat_mul_mem_logSpan log_norm_tC_mem_logSpan ((B : ℚ) - A)) (G.card : ℚ)
      have e : (((B : ℚ) - A : ℚ) : ℝ) = (B : ℝ) - A := by push_cast; ring
      rw [e] at h5
      exact_mod_cast h5
  have hcard : (G.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨1, h1G⟩).ne'
  have h6 := rat_mul_mem_logSpan hmem ((G.card : ℚ)⁻¹)
  have e : (((G.card : ℚ)⁻¹ : ℚ) : ℝ) * ((G.card : ℝ) * (Real.log c₁ - Real.log c₂)) =
      Real.log c₁ - Real.log c₂ := by
    push_cast
    field_simp
  rw [e] at h6
  exact h6

/-! ## 5. The criterion -/

/-- **The converse** (from Baker's theorem). If `log (a/b)` is the value of a series of the
class F, then it is a rational combination of `log 2` and the numbers
`log N((1+i)^n - c)`. -/
theorem mem_logSpan_of_isFValue_log (hB : BakerTheorem) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : IsFValue (Real.log ((a : ℝ) / b))) : Real.log ((a : ℝ) / b) ∈ logSpan := by
  classical
  by_contra hnot
  obtain ⟨N, ρ, hN, hρ, hsum⟩ := h
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hpos : (0 : ℝ) < (a : ℝ) / b := by positivity
  set Λ : ℂ := ((Real.log ((a : ℝ) / b) : ℝ) : ℂ) with hΛdef
  have hΛ : Complex.exp Λ = (a : ℂ) / b := by
    rw [hΛdef, ← Complex.ofReal_exp, Real.exp_log hpos]
    push_cast
    rfl
  have halg : IsAlgebraic ℚ ((a : ℂ) / b) := by
    have h0 := isAlgebraic_algebraMap (R := ℚ) (A := ℂ) ((a : ℚ) / b)
    simpa using h0
  -- a relation with a non-zero power of `a/b` would put `log (a/b)` in the span
  have hmul : ∀ S : Finset ℂ, (∀ r ∈ S, IsOfFinOrder r) → ∀ (e : ℂ → ℤ) (m : ℤ),
      IsRelUpToQ (a : ℂ) (b : ℂ) S e m → m = 0 := by
    intro S hS e m hrel
    by_contra hm
    obtain ⟨ξ, hξ, hcl⟩ := cleared_upToQ haC hbC hS hrel
    have key := log_sub_mem_logSpan_of_cleared hS hξ (fun r => (e r).toNat)
      (fun r => (-e r).toNat) (∑ r ∈ S, (-e r).toNat) (∑ r ∈ S, (e r).toNat)
      (c₁ := a ^ (-m).toNat * b ^ m.toNat) (c₂ := a ^ m.toNat * b ^ (-m).toNat)
      (by positivity) (by positivity) (by push_cast; exact hcl)
    have hu : ((m.toNat : ℕ) : ℝ) - (((-m).toNat : ℕ) : ℝ) = (m : ℝ) := by
      have h0 : ((m.toNat : ℕ) : ℤ) - (((-m).toNat : ℕ) : ℤ) = m := by omega
      exact_mod_cast h0
    have e1 : Real.log ((a ^ (-m).toNat * b ^ m.toNat : ℕ) : ℝ) -
        Real.log ((a ^ m.toNat * b ^ (-m).toNat : ℕ) : ℝ) =
          (-(m : ℝ)) * Real.log ((a : ℝ) / b) := by
      push_cast
      rw [Real.log_mul (pow_ne_zero _ haR) (pow_ne_zero _ hbR),
        Real.log_mul (pow_ne_zero _ haR) (pow_ne_zero _ hbR), Real.log_pow, Real.log_pow,
        Real.log_pow, Real.log_pow, Real.log_div haR hbR]
      linear_combination (Real.log b - Real.log a) * hu
    rw [e1] at key
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have h5 := rat_mul_mem_logSpan key ((-(m : ℚ))⁻¹)
    have e2 : (((-(m : ℚ))⁻¹ : ℚ) : ℝ) * (-(m : ℝ) * Real.log ((a : ℝ) / b)) =
        Real.log ((a : ℝ) / b) := by
      push_cast
      field_simp
    rw [e2] at h5
    exact hnot h5
  -- the series as a combination of logarithms
  have hρ8 : ∀ k, ρ (k + 8 * N) = ρ k := fun k => by
    have h8 := periodic_mul hρ 8 k
    rwa [mul_comm] at h8
  have hN8 : 0 < 8 * N := by positivity
  have h1 := series_eq_logs hN8 (Dvd.intro N rfl) hρ8
  have e : (fun k : ℕ => (ρ k : ℂ) / 2 ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTerm ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTerm]
  rw [e] at h1
  have h2 := h1.unique (Complex.hasSum_ofReal.2 hsum)
  have h3 : ∑ r ∈ rootsN (8 * N), fourierD (8 * N) ρ r * Complex.log (1 - r / tC) =
      (1 : ℂ) * Λ := by
    rw [h2, one_mul]
  have h4 := baker_no_extra hB hΛ halg hmul
    (fun r hr => isOfFinOrder_of_mem_rootsN hN8 hr)
    (fun r hr => isAlgebraic_fourierD (8 * N) ρ (isOfFinOrder_of_mem_rootsN hN8 hr))
    isAlgebraic_one h3
  exact one_ne_zero h4

/-- **Theorem K, the criterion** (from Baker's theorem). For positive integers `a`, `b`:
`log (a/b)` is the value of a series of the class F if and only if it is a rational
combination of `log 2` and the numbers `log N((1+i)^n - c)`, `n ≥ 1`, `c ∈ {1, -1, i, -i}`. -/
theorem isFValue_log_iff (hB : BakerTheorem) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    IsFValue (Real.log ((a : ℝ) / b)) ↔ Real.log ((a : ℝ) / b) ∈ logSpan :=
  ⟨mem_logSpan_of_isFValue_log hB ha hb, isFValue_of_mem_logSpan⟩

/-- **Theorem K** for a positive integer. -/
theorem isFValue_log_nat_iff (hB : BakerTheorem) {n : ℕ} (hn : 0 < n) :
    IsFValue (Real.log (n : ℝ)) ↔ Real.log (n : ℝ) ∈ logSpan := by
  have h := isFValue_log_iff hB hn one_pos
  simpa using h

/-- **Theorem K** for a positive rational number. -/
theorem isFValue_log_rat_iff (hB : BakerTheorem) {y : ℚ} (hy : 0 < y) :
    IsFValue (Real.log (y : ℝ)) ↔ Real.log (y : ℝ) ∈ logSpan := by
  have hnum : 0 < y.num := Rat.num_pos.2 hy
  have e : (y : ℝ) = ((y.num.toNat : ℕ) : ℝ) / ((y.den : ℕ) : ℝ) := by
    have h1 : ((y.num.toNat : ℕ) : ℤ) = y.num := Int.toNat_of_nonneg hnum.le
    have h2 : ((y.num.toNat : ℕ) : ℝ) = ((y.num : ℤ) : ℝ) := by exact_mod_cast h1
    rw [h2, Rat.cast_def]
  rw [e]
  exact isFValue_log_iff hB (by omega) y.den_pos

end PiFormula
