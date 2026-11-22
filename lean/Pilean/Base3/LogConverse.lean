import Pilean.Base3.LogValues

/-!
# Base 3: which logarithms are values (the criterion)

`logSpan3` is the set of rational combinations of `log 3` and the numbers `log |t^n - c|`,
`t = √-3`, `n ≥ 1`, `c^3 = 1`.

* `logSpan3_le_f3Values` (no Baker): every element of `logSpan3` is a value of the class F3.
* `mem_logSpan3_of_isF3Value_log` (from Baker's theorem): if `log (a/b)` is a value of F3,
  it lies in `logSpan3`.
* `isF3Value_log_iff`, `isF3Value_log_nat_iff`, `isF3Value_log_rat_iff`: the criterion.

The proof of the converse is the one of `LogConverse.lean` with `ω` in place of `i`: a
cleared relation is an integer polynomial identity at `ζ = exp(2πi/N)`, `N = 3K`, with
`ω = ζ^K` and `t = ω - ω²`; it holds at `ζ^a` for `a` prime to `N`, and `a ≡ 1 (mod 3)` fixes
`ω` and `t`. Adding the logarithms of absolute values over these `a` and sorting the terms by
Möbius inversion leaves the numbers `log |t^M - c|` with `c^3 = 1`.
-/

open Complex Polynomial

namespace PiFormula

namespace Base3

/-! ## 1. The span, and the half that needs no Baker -/

/-- The generators: `log 3` and the numbers `log |t^n - c|`, `c^3 = 1`. -/
def logGenerators3 : Set ℝ :=
  {x | x = Real.log 3 ∨ ∃ (n : ℕ) (c : ℂ), 0 < n ∧ c ^ 3 = 1 ∧ x = Real.log ‖t3 ^ n - c‖}

/-- The rational combinations of `log 3` and the `log |t^n - c|`. -/
noncomputable def logSpan3 : Submodule ℚ ℝ := Submodule.span ℚ logGenerators3

/-- **The half of the criterion that needs no Baker.** Every rational combination of `log 3`
and the numbers `log |t^n - c|` is the value of a series of the class F3. -/
theorem logSpan3_le_f3Values : logSpan3 ≤ f3Values := by
  refine Submodule.span_le.2 ?_
  rintro x (rfl | ⟨n, c, hn, hc, rfl⟩)
  · exact isF3Value_log_three
  · exact isF3Value_log_gen hn hc

theorem isF3Value_of_mem_logSpan3 {x : ℝ} (hx : x ∈ logSpan3) : IsF3Value x :=
  logSpan3_le_f3Values hx

theorem rat_mul_mem_logSpan3 {x : ℝ} (hx : x ∈ logSpan3) (q : ℚ) : (q : ℝ) * x ∈ logSpan3 := by
  have h := logSpan3.smul_mem q hx
  rwa [Rat.smul_def] at h

theorem log_three_mem_logSpan3 : Real.log 3 ∈ logSpan3 := Submodule.subset_span (Or.inl rfl)

theorem log_norm_t3_mem_logSpan3 : Real.log ‖t3‖ ∈ logSpan3 := by
  have h := rat_mul_mem_logSpan3 log_three_mem_logSpan3 (1 / 2)
  rw [log_norm_t3]
  convert h using 1
  push_cast
  ring

theorem log_norm_t3_pow_sub_mem {n : ℕ} (hn : 0 < n) {w : ℂ} (hw : w ^ 3 = 1) :
    Real.log ‖t3 ^ n - w‖ ∈ logSpan3 :=
  Submodule.subset_span (Or.inr ⟨n, w, hn, hw, rfl⟩)

/-! ## 2. Conjugating an identity between roots of unity -/

/-- `t = ω - ω²`. -/
theorem t3_eq : t3 = w3 - w3 ^ 2 := by
  rw [w3_sq]
  apply Complex.ext
  · simp [t3, w3]
  · simp [t3, w3]

/-- `ζ_{3K}^K = ω`. -/
theorem zetaN_pow_third {K : ℕ} (hK : 0 < K) : zetaN (3 * K) ^ K = w3 := by
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have e : (K : ℂ) * (2 * Real.pi * I / ((3 * K : ℕ) : ℂ)) =
      ((Real.pi - Real.pi / 3 : ℝ) : ℂ) * I := by
    push_cast
    field_simp
    ring
  rw [zetaN, ← Complex.exp_nat_mul, e]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_sub, Real.cos_pi_div_three]
    simp [w3]
    norm_num
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_sub, Real.sin_pi_div_three]
    simp [w3]

theorem w3_pow_of_mod_three {a : ℕ} (ha : a % 3 = 1) : w3 ^ a = w3 := by
  rw [w3_pow_mod, ha, pow_one]

/-- **Conjugating a cleared relation.** An identity between products of the `t - r` (`r` roots
of unity), powers of `t = √-3` and integers, up to a root of unity `ξ`, stays true when every
`r` and `ξ` are raised to a power `a` prime to their orders with `a ≡ 1 (mod 3)`. -/
theorem cleared_conj3 {S : Finset ℂ} {ξ : ℂ} (p n : ℂ → ℕ) (A B c₁ c₂ : ℕ) {K : ℕ}
    (hK : 0 < K) (hSK : ∀ r ∈ S, r ^ (3 * K) = 1) (hξK : ξ ^ (3 * K) = 1)
    (h : (∏ r ∈ S, (t3 - r) ^ p r) * t3 ^ A * (c₁ : ℂ) =
      ξ * (∏ r ∈ S, (t3 - r) ^ n r) * t3 ^ B * (c₂ : ℂ))
    {a : ℕ} (ha : a.Coprime (3 * K)) (ha3 : a % 3 = 1) :
    (∏ r ∈ S, (t3 - r ^ a) ^ p r) * t3 ^ A * (c₁ : ℂ) =
      ξ ^ a * (∏ r ∈ S, (t3 - r ^ a) ^ n r) * t3 ^ B * (c₂ : ℂ) := by
  classical
  have hN0 : 0 < 3 * K := by omega
  have : NeZero (3 * K) := ⟨hN0.ne'⟩
  set ζ := zetaN (3 * K) with hζdef
  have hζ : IsPrimitiveRoot ζ (3 * K) := zetaN_prim hN0
  have hζK : ζ ^ K = w3 := zetaN_pow_third hK
  have hτ : ∀ z : ℂ, z ^ K = w3 → z ^ K - z ^ (2 * K) = t3 := fun z hz => by
    rw [mul_comm, pow_mul, hz, ← t3_eq]
  have hex : ∀ r ∈ S, ∃ k : ℕ, ζ ^ k = r := fun r hr => by
    obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (hSK r hr)
    exact ⟨k, hk⟩
  choose! kf hkf using hex
  obtain ⟨b, -, hb⟩ := hζ.eq_pow_of_pow_eq_one hξK
  let τ : ℤ[X] := X ^ K - X ^ (2 * K)
  let F : ℤ[X] := (∏ r ∈ S, (τ - X ^ kf r) ^ p r) * τ ^ A * (c₁ : ℤ[X]) -
    X ^ b * (∏ r ∈ S, (τ - X ^ kf r) ^ n r) * τ ^ B * (c₂ : ℤ[X])
  have hev : ∀ z : ℂ, aeval z F =
      (∏ r ∈ S, ((z ^ K - z ^ (2 * K)) - z ^ kf r) ^ p r) * (z ^ K - z ^ (2 * K)) ^ A *
          (c₁ : ℂ) -
        z ^ b * (∏ r ∈ S, ((z ^ K - z ^ (2 * K)) - z ^ kf r) ^ n r) *
          (z ^ K - z ^ (2 * K)) ^ B * (c₂ : ℂ) :=
    fun z => by
      simp only [F, τ, map_sub, map_mul, map_prod, map_pow, aeval_X, map_natCast]
  have h0 : aeval ζ F = 0 := by
    rw [hev, hτ ζ hζK, sub_eq_zero]
    have e : ∀ q : ℂ → ℕ, ∏ r ∈ S, (t3 - ζ ^ kf r) ^ q r = ∏ r ∈ S, (t3 - r) ^ q r :=
      fun q => Finset.prod_congr rfl fun r hr => by rw [hkf r hr]
    rw [e, e, hb]
    exact h
  have h1 := aeval_pow_of_coprime hN0 hζ h0 ha
  have hI : (ζ ^ a) ^ K = w3 := by
    rw [← pow_mul, mul_comm, pow_mul, hζK, w3_pow_of_mod_three ha3]
  rw [hev, hτ _ hI, sub_eq_zero] at h1
  have e : ∀ q : ℂ → ℕ,
      ∏ r ∈ S, (t3 - (ζ ^ a) ^ kf r) ^ q r = ∏ r ∈ S, (t3 - r ^ a) ^ q r :=
    fun q => Finset.prod_congr rfl fun r hr => by
      rw [← pow_mul, mul_comm, pow_mul, hkf r hr]
  rw [e, e, ← pow_mul, mul_comm a b, pow_mul, hb] at h1
  exact h1

/-! ## 3. Sums of `log |t - r|` over a coset of roots of unity -/

/-- **A full coset.** `∑_{c < L} log |t - u^c x|` is in the span when `u^L = 1` and `x^M` is a
cube root of unity, `M` the order of `u`. -/
theorem sum_log_coset_mem3 {u x₀ : ℂ} {L : ℕ} (hL : 0 < L) (hu : u ^ L = 1) (hx : ‖x₀‖ = 1)
    (hx3 : (x₀ ^ orderOf u) ^ 3 = 1) :
    ∑ c ∈ Finset.range L, Real.log ‖t3 - u ^ c * x₀‖ ∈ logSpan3 := by
  have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.2 ⟨L, hL, hu⟩
  have hM0 : 0 < orderOf u := hfin.orderOf_pos
  have hprim : IsPrimitiveRoot u (orderOf u) := IsPrimitiveRoot.orderOf u
  obtain ⟨k, rfl⟩ : orderOf u ∣ L := orderOf_dvd_of_pow_eq_one hu
  have hun : ‖u‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hu hL.ne'
  have hne : ∀ c : ℕ, t3 - u ^ c * x₀ ≠ 0 := fun c =>
    t3_sub_ne_zero (by rw [norm_mul, norm_pow, hun, one_pow, one_mul, hx])
  have hone : ∑ c ∈ Finset.range (orderOf u), Real.log ‖t3 - u ^ c * x₀‖ =
      Real.log ‖t3 ^ orderOf u - x₀ ^ orderOf u‖ := by
    have h1 := prod_sub_nthRoots hM0 (x₀ ^ orderOf u) t3
    rw [hprim.nthRoots_eq rfl, Multiset.map_map] at h1
    rw [← h1, ← Finset.range_val, ← Finset.prod_eq_multiset_prod, norm_prod, Real.log_prod]
    · rfl
    · intro c _
      exact norm_ne_zero_iff.2 (hne c)
  have hper : ∀ j c : ℕ, u ^ (orderOf u * j + c) = u ^ c := fun j c => by
    rw [pow_add, pow_mul, pow_orderOf_eq_one, one_pow, one_mul]
  have hsum : ∀ j : ℕ, ∑ c ∈ Finset.range (orderOf u * j), Real.log ‖t3 - u ^ c * x₀‖ =
      j • Real.log ‖t3 ^ orderOf u - x₀ ^ orderOf u‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul, ← hone]
      congr 1
      exact Finset.sum_congr rfl fun c _ => by rw [hper]
  rw [hsum]
  exact nsmul_mem (log_norm_t3_pow_sub_mem hM0 hx3) k

/-- **Exponents in one class modulo 3.** -/
theorem sum_log_mod_three_mem {s : ℂ} {K : ℕ} (hK : 0 < K) (hs : s ^ (3 * K) = 1) {ρ₀ : ℕ}
    (hρ₀ : ρ₀ < 3) :
    ∑ b ∈ (Finset.range (3 * K)).filter (fun b => b % 3 = ρ₀), Real.log ‖t3 - s ^ b‖ ∈
      logSpan3 := by
  have hsn : ‖s‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hs (by omega)
  have e : ∑ b ∈ (Finset.range (3 * K)).filter (fun b => b % 3 = ρ₀), Real.log ‖t3 - s ^ b‖ =
      ∑ c ∈ Finset.range K, Real.log ‖t3 - (s ^ 3) ^ c * s ^ ρ₀‖ := by
    refine Finset.sum_nbij' (fun b => b / 3) (fun c => 3 * c + ρ₀) ?_ ?_ ?_ ?_ ?_
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
      have hsb : s ^ b = (s ^ 3) ^ (b / 3) * s ^ ρ₀ := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [hsb]
  rw [e]
  refine sum_log_coset_mem3 hK (by rw [← pow_mul]; exact hs)
    (by rw [norm_pow, hsn, one_pow]) ?_
  have h1 : ((s ^ ρ₀) ^ orderOf (s ^ 3)) ^ 3 = ((s ^ 3) ^ orderOf (s ^ 3)) ^ ρ₀ := by ring
  rw [h1, pow_orderOf_eq_one, one_pow]

theorem mul_mod_three_eq_one {d b : ℕ} (hd : d % 3 ≠ 0) : d * b % 3 = 1 ↔ b % 3 = d % 3 := by
  rw [Nat.mul_mod]
  have h1 : d % 3 = 1 ∨ d % 3 = 2 := by omega
  have h2 : b % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize b % 3 = x at h2 ⊢
  rcases h1 with h | h <;> rw [h] <;> interval_cases x <;> simp

/-- **The orbit of a root of unity.** `∑ log |t - r^a|` over the `a < 3K` prime to `3K` with
`a ≡ 1 (mod 3)` is in the span, when `r^(3K) = 1`. -/
theorem sum_log_coprime_mem3 {r : ℂ} {K : ℕ} (hK : 0 < K) (hr : r ^ (3 * K) = 1) :
    ∑ a ∈ (Finset.range (3 * K)).filter (fun a => a % 3 = 1 ∧ a.Coprime (3 * K)),
      Real.log ‖t3 - r ^ a‖ ∈ logSpan3 := by
  have hN : 0 < 3 * K := by omega
  rw [← Finset.filter_filter, sum_filter_coprime hN]
  refine Submodule.sum_mem _ fun d hd => zsmul_mem ?_ _
  have hdN : d ∣ 3 * K := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  by_cases h3 : 3 ∣ d
  · -- a multiple of 3 has no multiple `≡ 1 (mod 3)`
    have hempty : ((Finset.range (3 * K)).filter (fun a => a % 3 = 1)).filter
        (fun a => d ∣ a) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun a ha hda => ?_
      have h2 : 3 ∣ a := h3.trans hda
      have h4 := (Finset.mem_filter.1 ha).2
      omega
    rw [hempty, Finset.sum_empty]
    exact zero_mem _
  · have hd3 : d % 3 ≠ 0 := fun h => h3 (Nat.dvd_of_mod_eq_zero h)
    have hcop : Nat.Coprime d 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
    obtain ⟨K', rfl⟩ : d ∣ K := hcop.dvd_of_dvd_mul_left hdN
    have hK' : 0 < K' := Nat.pos_of_mul_pos_left hK
    have e : ∑ a ∈ ((Finset.range (3 * (d * K'))).filter (fun a => a % 3 = 1)).filter
          (fun a => d ∣ a), Real.log ‖t3 - r ^ a‖ =
        ∑ b ∈ (Finset.range (3 * K')).filter (fun b => b % 3 = d % 3),
          Real.log ‖t3 - (r ^ d) ^ b‖ := by
      refine Finset.sum_nbij' (fun a => a / d) (fun b => d * b) ?_ ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
        obtain ⟨⟨ha1, ha2⟩, b, rfl⟩ := ha
        rw [Nat.mul_div_cancel_left b hd0]
        refine ⟨?_, (mul_mod_three_eq_one hd3).1 ha2⟩
        have h4 : d * b < d * (3 * K') := by
          rw [show d * (3 * K') = 3 * (d * K') by ring]
          exact ha1
        exact Nat.lt_of_mul_lt_mul_left h4
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
        refine ⟨⟨?_, (mul_mod_three_eq_one hd3).2 hb.2⟩, Dvd.intro b rfl⟩
        rw [show 3 * (d * K') = d * (3 * K') by ring]
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
    refine sum_log_mod_three_mem hK' ?_ (Nat.mod_lt _ (by norm_num))
    rw [← pow_mul, show d * (3 * K') = 3 * (d * K') by ring]
    exact hr

/-! ## 4. From a cleared relation to the span -/

/-- **The key lemma in base 3.** From an identity
`∏ (t - r)^(p_r) · t^A · c₁ = ξ · ∏ (t - r)^(n_r) · t^B · c₂` between roots of unity `r`, `ξ`
and positive integers `c₁`, `c₂`, the number `log c₁ - log c₂` is in `logSpan3`. -/
theorem log_sub_mem_logSpan3_of_cleared {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {ξ : ℂ} (hξ : IsOfFinOrder ξ) (p n : ℂ → ℕ) (A B : ℕ) {c₁ c₂ : ℕ} (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂)
    (h : (∏ r ∈ S, (t3 - r) ^ p r) * t3 ^ A * (c₁ : ℂ) =
      ξ * (∏ r ∈ S, (t3 - r) ^ n r) * t3 ^ B * (c₂ : ℂ)) :
    Real.log c₁ - Real.log c₂ ∈ logSpan3 := by
  classical
  set K := (∏ r ∈ S, orderOf r) * orderOf ξ with hKdef
  have hK : 0 < K :=
    Nat.mul_pos (Finset.prod_pos fun r hr => (hS r hr).orderOf_pos) hξ.orderOf_pos
  have hSK : ∀ r ∈ S, r ^ (3 * K) = 1 := fun r hr =>
    orderOf_dvd_iff_pow_eq_one.1
      (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hr) _) 3)
  have hξK : ξ ^ (3 * K) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Dvd.dvd.mul_left (Dvd.intro_left _ rfl) 3)
  have hξn : ‖ξ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hξK (by omega)
  set G := (Finset.range (3 * K)).filter (fun a => a % 3 = 1 ∧ a.Coprime (3 * K)) with hG
  have h1G : 1 ∈ G := by
    rw [hG, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, rfl, Nat.coprime_one_left _⟩
  have hT : 0 < ‖t3‖ := norm_pos_iff.2 t3_ne_zero
  have hlog : ∀ a ∈ G, Real.log c₁ - Real.log c₂ =
      ∑ r ∈ S, ((n r : ℝ) - p r) * Real.log ‖t3 - r ^ a‖ +
        ((B : ℝ) - A) * Real.log ‖t3‖ := by
    intro a ha
    obtain ⟨-, ha3, hac⟩ := Finset.mem_filter.1 ha
    have h2 := cleared_conj3 p n A B c₁ c₂ hK hSK hξK h hac ha3
    have h3 := congrArg norm h2
    simp only [norm_mul, norm_pow, norm_prod, Complex.norm_natCast, hξn, one_pow,
      one_mul] at h3
    refine log_identity_of_prod_eq (x := fun r => ‖t3 - r ^ a‖) (fun r hr => ?_) hT p n A B
      (by exact_mod_cast hc₁) (by exact_mod_cast hc₂) h3
    refine norm_pos_iff.2 (t3_sub_ne_zero ?_)
    rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one (hSK r hr) (by omega), one_pow]
  have hsum : (G.card : ℝ) * (Real.log c₁ - Real.log c₂) =
      ∑ r ∈ S, ((n r : ℝ) - p r) * ∑ a ∈ G, Real.log ‖t3 - r ^ a‖ +
        (G.card : ℝ) * (((B : ℝ) - A) * Real.log ‖t3‖) := by
    have h4 := Finset.sum_congr (rfl : G = G) hlog
    rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib, Finset.sum_comm,
      Finset.sum_const, nsmul_eq_mul] at h4
    rw [h4]
    simp only [Finset.mul_sum]
  have hmem : (G.card : ℝ) * (Real.log c₁ - Real.log c₂) ∈ logSpan3 := by
    rw [hsum]
    refine add_mem (Submodule.sum_mem _ fun r hr => ?_) ?_
    · have h5 := rat_mul_mem_logSpan3 (sum_log_coprime_mem3 hK (hSK r hr)) ((n r : ℚ) - p r)
      have e : (((n r : ℚ) - p r : ℚ) : ℝ) = (n r : ℝ) - p r := by push_cast; ring
      rw [e] at h5
      exact h5
    · have h5 := rat_mul_mem_logSpan3
        (rat_mul_mem_logSpan3 log_norm_t3_mem_logSpan3 ((B : ℚ) - A)) (G.card : ℚ)
      have e : (((B : ℚ) - A : ℚ) : ℝ) = (B : ℝ) - A := by push_cast; ring
      rw [e] at h5
      exact_mod_cast h5
  have hcard : (G.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨1, h1G⟩).ne'
  have h6 := rat_mul_mem_logSpan3 hmem ((G.card : ℚ)⁻¹)
  have e : (((G.card : ℚ)⁻¹ : ℚ) : ℝ) * ((G.card : ℝ) * (Real.log c₁ - Real.log c₂)) =
      Real.log c₁ - Real.log c₂ := by
    push_cast
    field_simp
  rw [e] at h6
  exact h6

/-! ## 5. The criterion -/

/-- **The converse in base 3** (from Baker's theorem). If `log (a/b)` is the value of a series
of the class F3, then it is a rational combination of `log 3` and the numbers
`log |t^n - c|`. -/
theorem mem_logSpan3_of_isF3Value_log (hB : BakerTheorem) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : IsF3Value (Real.log ((a : ℝ) / b))) : Real.log ((a : ℝ) / b) ∈ logSpan3 := by
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
  have hmul : ∀ S : Finset ℂ, (∀ r ∈ S, IsOfFinOrder r) → ∀ (e : ℂ → ℤ) (m : ℤ),
      IsRel3 (a : ℂ) (b : ℂ) S e m → m = 0 := by
    intro S hS e m hrel
    by_contra hm
    obtain ⟨ξ, hξ, hcl⟩ := cleared3 haC hbC hS hrel
    have key := log_sub_mem_logSpan3_of_cleared hS hξ (fun r => (e r).toNat)
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
    have h5 := rat_mul_mem_logSpan3 key ((-(m : ℚ))⁻¹)
    have e2 : (((-(m : ℚ))⁻¹ : ℚ) : ℝ) * (-(m : ℝ) * Real.log ((a : ℝ) / b)) =
        Real.log ((a : ℝ) / b) := by
      push_cast
      field_simp
    rw [e2] at h5
    exact hnot h5
  have hρ4 : ∀ k, ρ (k + 4 * N) = ρ k := fun k => by
    have h4 := periodic_mul hρ 4 k
    rwa [mul_comm] at h4
  have hN4 : 0 < 4 * N := by positivity
  have h1 := series_eq_logs3 hN4 (Dvd.intro N rfl) hρ4
  have e : (fun k : ℕ => (ρ k : ℂ) / 3 ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTerm3 ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTerm3]
  rw [e] at h1
  have h2 := h1.unique (Complex.hasSum_ofReal.2 hsum)
  have h3 : ∑ r ∈ rootsN (4 * N), fourierD3 (4 * N) ρ r * Complex.log (1 - r / t3) =
      (1 : ℂ) * Λ := by
    rw [h2, one_mul]
  have h4 := baker_no_extra3 hB hΛ halg hmul
    (fun r hr => isOfFinOrder_of_mem_rootsN hN4 hr)
    (fun r hr => isAlgebraic_fourierD3 (4 * N) ρ (isOfFinOrder_of_mem_rootsN hN4 hr))
    isAlgebraic_one h3
  exact one_ne_zero h4

/-- **The criterion in base 3** (from Baker's theorem). For positive integers `a`, `b`:
`log (a/b)` is the value of a series of the class F3 if and only if it is a rational
combination of `log 3` and the numbers `log |t^n - c|`, `t = √-3`, `n ≥ 1`, `c^3 = 1`. -/
theorem isF3Value_log_iff (hB : BakerTheorem) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    IsF3Value (Real.log ((a : ℝ) / b)) ↔ Real.log ((a : ℝ) / b) ∈ logSpan3 :=
  ⟨mem_logSpan3_of_isF3Value_log hB ha hb, isF3Value_of_mem_logSpan3⟩

theorem isF3Value_log_nat_iff (hB : BakerTheorem) {n : ℕ} (hn : 0 < n) :
    IsF3Value (Real.log (n : ℝ)) ↔ Real.log (n : ℝ) ∈ logSpan3 := by
  have h := isF3Value_log_iff hB hn one_pos
  simpa using h

theorem isF3Value_log_rat_iff (hB : BakerTheorem) {y : ℚ} (hy : 0 < y) :
    IsF3Value (Real.log (y : ℝ)) ↔ Real.log (y : ℝ) ∈ logSpan3 := by
  have hnum : 0 < y.num := Rat.num_pos.2 hy
  have e : (y : ℝ) = ((y.num.toNat : ℕ) : ℝ) / ((y.den : ℕ) : ℝ) := by
    have h1 : ((y.num.toNat : ℕ) : ℤ) = y.num := Int.toNat_of_nonneg hnum.le
    have h2 : ((y.num.toNat : ℕ) : ℝ) = ((y.num : ℤ) : ℝ) := by exact_mod_cast h1
    rw [h2, Rat.cast_def]
  rw [e]
  exact isF3Value_log_iff hB (by omega) y.den_pos

end Base3

end PiFormula
