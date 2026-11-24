/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.BaseB.LogWeightDefs

/-!
# A positive weight for every non-square base `b ≥ 5`

`posWeight`: for a base `b ≥ 5` that is not a square there is a map `L : ℚ → ℚ`, additive on
products and positive on every integer `n ≥ 2`, that vanishes on every `ν(r)²`, `r` a root of
unity (`PosWeight b`, file `LogDefs`). With the criterion of the file `LogSpan` this gives
Theorem N of the research note `research/2026-11-22-log-primes/00_summary.md`: no `log n`,
`n ≥ 2` an integer, is a value of the class `F_b`.

`L(x) = ∑_p λ_p v_p(x)` with the weight `λ = lam b` of the file `LogWeightDefs`. Write `c`, `d`
for `|c₀(r)|` and `d(r)`, `m` for the order of `r²`, and call a prime `p ∣ c` primitive if
`p ∤ 2m`. The steps:

* `lam_bounds` (strong induction on the prime `p ∤ b`): `0 < λ_p < β_p`, with `β_p = 1` for
  `p ≤ 3` and `β_p = 2 φ(ord_p(b))` otherwise. For the home root `r` of `p`:
  - `m ≥ 3` (`omegaOf_pos_high`): at most one prime `q` of `c` divides `2m`; it is the largest
    prime factor of `m`, `v_q(c) ≤ k`, `d ≥ k φ(m)` and `β_q ≤ φ(m)/2`; so
    `ω ≥ k (φ(m)/2 - λ_q) > 0`. The upper bound uses `d ≤ 2 k φ(m)`, with `v_p(c) ≥ k` in case
    of equality.
  - `m ≤ 2`: `c = e^m`, `d = 2m` with `e = b - 1` or `b + 1`, and
    `λ_p = (1 - λ_2 v_2(e)) / Ω_odd(e)` (`kappa_facts`).
* `wtOf_cAbs`, the identity (W): `∑_p λ_p v_p(c) = d/2`. Every primitive prime of `c` has
  weight `ω / N` (`lam_eq_of_dvd`, from F3), and there is a primitive prime: by F4 for `m ≥ 3`,
  and for `m ≤ 2` unless `e` is a power of 2, where `λ_2 v_2(e) = 1`.
* `L(ν(r)²) = 2 · d/2 - d · L(b) = 0`, since `L(b) = 1`.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-! ## 1. The indices 1 and 2 -/

/-- The number of odd prime factors of `e`, with multiplicity. -/
def oddCount (e : ℕ) : ℕ := ∑ q ∈ e.primeFactors.filter (· ≠ 2), e.factorization q

theorem le_oddCount {e p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpe : p ∣ e) (he : e ≠ 0) :
    e.factorization p ≤ oddCount e :=
  Finset.single_le_sum (f := fun q => e.factorization q) (fun _ _ => Nat.zero_le _)
    (Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp, hpe, he⟩, hp2⟩)

theorem oddCount_pos {e p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpe : p ∣ e) (he : e ≠ 0) :
    0 < oddCount e :=
  (hp.factorization_pos_of_dvd he hpe).trans_le (le_oddCount hp hp2 hpe he)

theorem eq_two_pow_of_oddCount_eq_zero {e : ℕ} (he : e ≠ 0) (h : oddCount e = 0) :
    e = 2 ^ e.factorization 2 := by
  have huniq : ∀ {d : ℕ}, d.Prime → d ∣ e → d = 2 := by
    intro d hd hde
    by_contra hne
    have := oddCount_pos hd hne hde he
    omega
  obtain ⟨j, hj⟩ : ∃ j, e = 2 ^ j := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd he huniq⟩
  have hfac : e.factorization 2 = j := by
    rw [hj, Nat.prime_two.factorization_pow]
    simp
  rw [hfac]
  exact hj

theorem oddCount_two_pow (j : ℕ) : oddCount (2 ^ j) = 0 := by
  unfold oddCount
  apply Finset.sum_eq_zero
  intro q hq
  rw [Finset.mem_filter, Nat.mem_primeFactors] at hq
  exact absurd ((Nat.prime_dvd_prime_iff_eq hq.1.1 Nat.prime_two).1
    (hq.1.1.dvd_of_dvd_pow hq.1.2.1)) hq.2

/-- An odd multiple of 3 larger than 3 has at least two prime factors, with multiplicity. -/
theorem two_le_oddCount {e : ℕ} (h2 : ¬ 2 ∣ e) (h3 : 3 ∣ e) (he : 3 < e) : 2 ≤ oddCount e := by
  have he0 : e ≠ 0 := by omega
  obtain ⟨x, rfl⟩ := h3
  have hx : x ≠ 1 := by omega
  obtain ⟨q, hq, hqx⟩ := Nat.exists_prime_and_dvd hx
  have hqe : q ∣ 3 * x := hqx.mul_left 3
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact h2 hqe
  by_cases hq3 : q = 3
  · subst hq3
    have h9 : 3 ^ 2 ∣ 3 * x := by
      rw [sq]
      exact mul_dvd_mul_left 3 hqx
    exact ((Nat.prime_three.pow_dvd_iff_le_factorization he0).1 h9).trans
      (le_oddCount Nat.prime_three (by norm_num) (dvd_mul_right 3 x) he0)
  · have hsub : ({3, q} : Finset ℕ) ⊆ (3 * x).primeFactors.filter (· ≠ 2) := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_filter.2
          ⟨Nat.mem_primeFactors.2 ⟨Nat.prime_three, dvd_mul_right 3 x, he0⟩, by norm_num⟩
      · exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hq, hqe, he0⟩, hq2⟩
    have h1 := Finset.sum_le_sum_of_subset (f := fun y => (3 * x).factorization y) hsub
    rw [Finset.sum_pair (Ne.symm hq3)] at h1
    have h3' := Nat.prime_three.factorization_pos_of_dvd he0 (dvd_mul_right 3 x)
    have hq' := hq.factorization_pos_of_dvd he0 hqe
    unfold oddCount
    omega

theorem dvd_two_mul_low {m : ℕ} (hm : m = 1 ∨ m = 2) {q : ℕ} (hq : q.Prime) :
    q ∣ 2 * m ↔ q = 2 := by
  constructor
  · intro h
    have h4 : q ∣ 2 ^ 2 := h.trans (by rcases hm with rfl | rfl <;> norm_num)
    exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h4)
  · rintro rfl
    exact dvd_mul_right 2 m

/-- `ω` for the data `(e^m, 2m, m)`, `m ≤ 2`. -/
theorem omegaOf_low (f : ℕ → ℚ) {m : ℕ} (hm : m = 1 ∨ m = 2) {e : ℕ} (he : e ≠ 0) :
    omegaOf f (e ^ m) (2 * m) m = m * (1 - f 2 * e.factorization 2) := by
  have hm0 : m ≠ 0 := by rcases hm with rfl | rfl <;> norm_num
  have hfilter : (e ^ m).primeFactors.filter (· ∣ 2 * m) = e.primeFactors.filter (· = 2) := by
    rw [Nat.primeFactors_pow e hm0]
    exact Finset.filter_congr fun q hq => dvd_two_mul_low hm (Nat.mem_primeFactors.1 hq).1
  rw [omegaOf, hfilter, Finset.sum_filter, Finset.sum_ite_eq']
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases h2 : 2 ∈ e.primeFactors
  · rw [ite_eq_left h2]
    push_cast
    ring
  · rw [ite_eq_right h2]
    have h0 : e.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hd =>
        h2 (Nat.mem_primeFactors.2 ⟨Nat.prime_two, hd, he⟩)
    rw [h0]
    push_cast
    ring

/-- `N` for the data `(e^m, 2m, m)`, `m ≤ 2`. -/
theorem countOf_low {m : ℕ} (hm : m = 1 ∨ m = 2) (e : ℕ) :
    countOf (e ^ m) m = m * oddCount e := by
  have hm0 : m ≠ 0 := by rcases hm with rfl | rfl <;> norm_num
  have hfilter : (e ^ m).primeFactors.filter (fun q => ¬ q ∣ 2 * m) =
      e.primeFactors.filter (· ≠ 2) := by
    rw [Nat.primeFactors_pow e hm0]
    exact Finset.filter_congr fun q hq =>
      not_congr (dvd_two_mul_low hm (Nat.mem_primeFactors.1 hq).1)
  rw [countOf, hfilter, oddCount, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

/-- The data of a root with `r⁴ = 1`, in one statement: `(e^m, 2m, m)` with `(m, e) = (1, b - 1)`
or `(2, b + 1)`. -/
theorem low_data' {b : ℕ} (hb : 2 ≤ b) (hsq : ¬ IsSquare b) {r : ℂ} (h4 : r ^ 4 = 1) :
    ∃ m e : ℕ, (m = 1 ∨ m = 2) ∧ (e = b - 1 ∨ e = b + 1) ∧ orderOf (r ^ 2) = m ∧
      cAbs b r = e ^ m ∧ cDeg b r = 2 * m := by
  rcases low_data hb hsq h4 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨1, b - 1, Or.inl rfl, Or.inl rfl, h1, by rw [h2, pow_one], h3⟩
  · exact ⟨2, b + 1, Or.inr rfl, Or.inr rfl, h1, h2, h3⟩

/-- The contribution `λ_2 v_2(e)` of the prime 2 to `e = b - 1` or `b + 1`: it is in `[0, 1]`,
equal to 1 exactly when `e` is a power of 2; and if `3 ∣ e`, it is positive or `e` has two odd
prime factors. -/
theorem kappa_facts {b : ℕ} (hb : 5 ≤ b) {e : ℕ} (he : e = b - 1 ∨ e = b + 1) :
    0 ≤ lam b 2 * e.factorization 2 ∧ (oddCount e ≠ 0 → lam b 2 * e.factorization 2 < 1) ∧
      (oddCount e = 0 → lam b 2 * e.factorization 2 = 1) ∧
      (3 ∣ e → 0 < lam b 2 * e.factorization 2 ∨ 2 ≤ oddCount e) := by
  have he0 : e ≠ 0 := by omega
  have he4 : 3 < e := by omega
  by_cases h2 : 2 ∣ b
  · have h2e : ¬ 2 ∣ e := by omega
    have hfac : e.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2e
    rw [hfac, Nat.cast_zero, mul_zero]
    refine ⟨le_rfl, fun _ => one_pos, fun h => ?_, fun h3 => Or.inr (two_le_oddCount h2e h3 he4)⟩
    have := eq_two_pow_of_oddCount_eq_zero he0 h
    rw [hfac, pow_zero] at this
    omega
  · obtain ⟨hpos, -, hspec⟩ := lamTwo_spec hb h2
    obtain ⟨h1, h2'⟩ := hspec e he
    rw [lam_two h2]
    have hv : 0 < e.factorization 2 :=
      Nat.prime_two.factorization_pos_of_dvd he0 (by omega)
    have hv' : (0 : ℚ) < (e.factorization 2 : ℚ) := by exact_mod_cast hv
    have hκ : 0 < lamTwo b * e.factorization 2 := mul_pos hpos hv'
    refine ⟨hκ.le, fun h => h2' fun heq => h ?_,
      fun h => h1 (eq_two_pow_of_oddCount_eq_zero he0 h), fun _ => Or.inl hκ⟩
    rw [heq]
    exact oddCount_two_pow _

/-! ## 2. The indices `m ≥ 3`: `ω > 0` -/

/-- The bound on the weight of a prime `q ∤ b`: `1` for `q ≤ 3`, and `2 φ(ord_q(b))`
otherwise. -/
noncomputable def lamBound (b q : ℕ) : ℚ :=
  if q ≤ 3 then 1 else 2 * ((orderOf ((b : ℕ) : ZMod q)).totient : ℚ)

/-- **`ω > 0` at an index `m ≥ 3`**, for weights `f` that are positive and below `lamBound` on
the primes dividing `m`. -/
theorem omegaOf_pos_high {b : ℕ} (hb : 2 ≤ b) {r : ℂ} (hr : IsOfFinOrder r) (h4 : r ^ 4 ≠ 1)
    (f : ℕ → ℚ) (hf : ∀ q : ℕ, q.Prime → ¬ q ∣ b → q ∣ orderOf (r ^ 2) →
      0 < f q ∧ f q < lamBound b q) :
    0 < omegaOf f (cAbs b r) (cDeg b r) (orderOf (r ^ 2)) := by
  classical
  obtain ⟨k, hk, -, hlow, -, hnon, -⟩ := high_data hb hr h4
  have hm3 := three_le_orderOf_sq hr h4
  have hφ2 : 2 ≤ (orderOf (r ^ 2)).totient := two_le_totient hm3
  have hφ2' : (2 : ℚ) ≤ ((orderOf (r ^ 2)).totient : ℚ) := by exact_mod_cast hφ2
  have hk' : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hlow' : (k : ℚ) * ((orderOf (r ^ 2)).totient : ℚ) ≤ (cDeg b r : ℚ) := by
    exact_mod_cast hlow
  have hS : ∀ q ∈ (cAbs b r).primeFactors.filter (· ∣ 2 * orderOf (r ^ 2)),
      q.Prime ∧ ¬ q ∣ b ∧ q ∣ orderOf (r ^ 2) ∧ q ∣ cAbs b r ∧
      (∀ q' : ℕ, q'.Prime → q' ∣ orderOf (r ^ 2) → q' ≤ q) ∧
      lamBound b q ≤ ((orderOf (r ^ 2)).totient : ℚ) / 2 := by
    intro q hq
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hq
    obtain ⟨⟨hqp, hqc, -⟩, hq2m⟩ := hq
    obtain ⟨hqb, a, ha⟩ := order_facts_of_dvd hqp hr (dvd_cAbs_iff.1 hqc)
    have he := orderOf_zmod_dvd_pred hqp hqb
    have hqm : q ∣ orderOf (r ^ 2) := by
      rcases (Nat.Prime.dvd_mul hqp).1 hq2m with h | h
      · obtain rfl : q = 2 := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1 h
        have he1 : orderOf ((b : ℕ) : ZMod 2) = 1 := Nat.dvd_one.1 he
        rw [he1, one_mul] at ha
        have ha0 : a ≠ 0 := by
          rintro rfl
          rw [pow_zero] at ha
          omega
        rw [ha]
        exact dvd_pow_self 2 ha0
      · exact h
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at ha
      have h1 : q ∣ q - 1 := (ha ▸ hqm).trans he
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hqp.one_lt) h1
      have := hqp.two_le
      omega
    refine ⟨hqp, hqb, hqm, hqc,
      fun q' hq' hq'm => le_of_prime_dvd_mul_pow hqp he hq' (ha ▸ hq'm), ?_⟩
    rw [lamBound]
    split_ifs with h3
    · linarith
    · have hq5 : 5 ≤ q := by
        have h4' : q ≠ 4 := by
          rintro rfl
          norm_num at hqp
        omega
      have h1 := totient_mul_pred_le hqp he ha0
      rw [← ha] at h1
      have h2 : (orderOf ((b : ℕ) : ZMod q)).totient * 4 ≤ (orderOf (r ^ 2)).totient :=
        (Nat.mul_le_mul_left _ (by omega)).trans h1
      have h2' : ((orderOf ((b : ℕ) : ZMod q)).totient : ℚ) * 4 ≤
          ((orderOf (r ^ 2)).totient : ℚ) := by exact_mod_cast h2
      linarith
  rcases ((cAbs b r).primeFactors.filter (· ∣ 2 * orderOf (r ^ 2))).eq_empty_or_nonempty with
    hemp | ⟨q, hq⟩
  · rw [omegaOf, hemp, Finset.sum_empty, sub_zero]
    have : (0 : ℚ) < (k : ℚ) * ((orderOf (r ^ 2)).totient : ℚ) := by positivity
    linarith
  · obtain ⟨hqp, hqb, hqm, hqc, hmax, hbd⟩ := hS q hq
    have hsing : (cAbs b r).primeFactors.filter (· ∣ 2 * orderOf (r ^ 2)) = {q} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hq, fun q' hq' => ?_⟩
      obtain ⟨hq'p, -, hq'm, -, hmax', -⟩ := hS q' hq'
      exact le_antisymm (hmax q' hq'p hq'm) (hmax' q hqp hqm)
    obtain ⟨hfpos, hflt⟩ := hf q hqp hqb hqm
    have hv : (((cAbs b r).factorization q : ℕ) : ℚ) ≤ (k : ℚ) := by
      exact_mod_cast hnon q hqp hqm hqc
    rw [omegaOf, hsing, Finset.sum_singleton]
    have h1 : f q * ((cAbs b r).factorization q : ℚ) ≤ f q * k :=
      mul_le_mul_of_nonneg_left hv hfpos.le
    have h2 : f q * k < ((orderOf (r ^ 2)).totient : ℚ) / 2 * k :=
      mul_lt_mul_of_pos_right (hflt.trans_le hbd) hk'
    linarith

/-! ## 3. The weights are positive and bounded -/

/-- **The weights of the primes not dividing `b`**: `0 < λ_p < lamBound b p`. -/
theorem lam_bounds {b : ℕ} (hb : 5 ≤ b) (hsq : ¬ IsSquare b) :
    ∀ p : ℕ, p.Prime → ¬ p ∣ b → 0 < lam b p ∧ lam b p < lamBound b p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  intro hp hpb
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨h1, h2, -⟩ := lamTwo_spec hb hpb
    rw [lam_two hpb, lamBound, ite_eq_left (by norm_num)]
    exact ⟨h1, by linarith⟩
  obtain ⟨r, hr, hord, hd, hlam⟩ := lam_home hp hp2 hpb
  have he := orderOf_zmod_dvd_pred hp hpb
  rw [← hord] at he
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hc0 : cAbs b r ≠ 0 := cAbs_ne_zero (by omega) hr
  have hpc : p ∣ cAbs b r := dvd_cAbs_iff.2 hd
  have hm0 : 0 < orderOf (r ^ 2) := (hr.pow (n := 2)).orderOf_pos
  have hmle : orderOf (r ^ 2) ≤ p - 1 := Nat.le_of_dvd (by omega) he
  have hpm : ¬ p ∣ 2 * orderOf (r ^ 2) := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    · have := Nat.le_of_dvd hm0 h
      omega
  have hvp : 0 < (cAbs b r).factorization p := hp.factorization_pos_of_dvd hc0 hpc
  have hN := le_countOf hp hpc hc0 hpm
  have hN1 : (1 : ℚ) ≤ (countOf (cAbs b r) (orderOf (r ^ 2)) : ℚ) := by
    exact_mod_cast hvp.trans_le hN
  have hsmall : ∀ q ∈ (cAbs b r).primeFactors, q ∣ 2 * orderOf (r ^ 2) →
      q.Prime ∧ ¬ q ∣ b ∧ q < p := by
    intro q hq hq2m
    have hq' := Nat.mem_primeFactors.1 hq
    refine ⟨hq'.1, (order_facts_of_dvd hq'.1 hr (dvd_cAbs_iff.1 hq'.2.1)).1, ?_⟩
    rcases (Nat.Prime.dvd_mul hq'.1).1 hq2m with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hq'.1 Nat.prime_two).1 h
      omega
    · have := Nat.le_of_dvd hm0 h
      omega
  have hωle : omegaOf (lam b) (cAbs b r) (cDeg b r) (orderOf (r ^ 2)) ≤ (cDeg b r : ℚ) / 2 :=
    omegaOf_le _ fun q hq h => by
      obtain ⟨h1, h2, h3⟩ := hsmall q hq h
      exact (ih q h3 h1 h2).1.le
  by_cases h4 : r ^ 4 = 1
  · -- the indices 1 and 2
    obtain ⟨m, e, hm, he', hmm, hce, hde⟩ := low_data' (by omega) hsq h4
    have he0 : e ≠ 0 := by omega
    rw [hmm, hce, hde, omegaOf_low _ hm he0, countOf_low hm] at hlam
    rw [hce] at hpc
    have hpe : p ∣ e := hp.dvd_of_dvd_pow hpc
    have hodd := oddCount_pos hp hp2 hpe he0
    obtain ⟨hκ0, hκ1, -, hκ3⟩ := kappa_facts hb he'
    have hκlt := hκ1 hodd.ne'
    have hmQ : (0 : ℚ) < (m : ℚ) := by rcases hm with rfl | rfl <;> norm_num
    have hoQ : (1 : ℚ) ≤ (oddCount e : ℚ) := by exact_mod_cast hodd
    have hlam' : lam b p = (1 - lam b 2 * e.factorization 2) / oddCount e := by
      rw [hlam]
      push_cast
      field_simp
    rw [hlam']
    refine ⟨div_pos (by linarith) (by linarith), ?_⟩
    rw [lamBound]
    split_ifs with h3
    · -- `p = 3`
      obtain rfl : p = 3 := by omega
      rw [div_lt_one (by linarith)]
      rcases hκ3 hpe with h | h
      · linarith
      · have : (2 : ℚ) ≤ (oddCount e : ℚ) := by exact_mod_cast h
        linarith
    · have hφ : (orderOf ((b : ℕ) : ZMod p)).totient = 1 := by
        rw [← hord, hmm]
        rcases hm with rfl | rfl <;> simp
      rw [hφ, div_lt_iff₀ (by linarith)]
      push_cast
      nlinarith
  · -- the indices `m ≥ 3`
    have hpos := omegaOf_pos_high (by omega) hr h4 (lam b) fun q hq hqb hqm =>
      ih q (by have := Nat.le_of_dvd hm0 hqm; omega) hq hqb
    rw [hlam]
    refine ⟨div_pos hpos (by linarith), ?_⟩
    have hp4 : ¬ p ≤ 3 := by
      intro h
      obtain rfl : p = 3 := by omega
      apply h4
      have h2 : (r ^ 2) ^ 2 = 1 := by
        have hcases : orderOf (r ^ 2) = 1 ∨ orderOf (r ^ 2) = 2 := by omega
        rcases hcases with h | h
        · rw [orderOf_eq_one_iff.1 h, one_pow]
        · have h' := pow_orderOf_eq_one (r ^ 2)
          rwa [h] at h'
      calc r ^ 4 = (r ^ 2) ^ 2 := by ring
        _ = 1 := h2
    rw [lamBound, ite_eq_right hp4, ← hord, div_lt_iff₀ (by linarith)]
    obtain ⟨k, hk, hk2, -, hup, -, heqc⟩ := high_data (b := b) (by omega) hr h4
    have hφ : 0 < (orderOf (r ^ 2)).totient := Nat.totient_pos.2 hm0
    have hφ' : (0 : ℚ) < ((orderOf (r ^ 2)).totient : ℚ) := by exact_mod_cast hφ
    have hNφ : 2 * ((orderOf (r ^ 2)).totient : ℚ) ≤
        2 * ((orderOf (r ^ 2)).totient : ℚ) * (countOf (cAbs b r) (orderOf (r ^ 2)) : ℚ) := by
      have := mul_le_mul_of_nonneg_left hN1 (by positivity :
        (0 : ℚ) ≤ 2 * ((orderOf (r ^ 2)).totient : ℚ))
      linarith
    by_cases hdeq : cDeg b r = 2 * k * (orderOf (r ^ 2)).totient
    · have hkN : (k : ℚ) ≤ (countOf (cAbs b r) (orderOf (r ^ 2)) : ℚ) := by
        exact_mod_cast (heqc hdeq p hp hpc).trans hN
      have hd' : (cDeg b r : ℚ) = 2 * k * ((orderOf (r ^ 2)).totient : ℚ) := by
        exact_mod_cast hdeq
      have h1 := mul_le_mul_of_nonneg_right hkN hφ'.le
      have h2 : (0 : ℚ) < (countOf (cAbs b r) (orderOf (r ^ 2)) : ℚ) *
          ((orderOf (r ^ 2)).totient : ℚ) := by positivity
      linarith
    · have hlt : cDeg b r < 2 * k * (orderOf (r ^ 2)).totient := lt_of_le_of_ne hup hdeq
      have hlt2 : cDeg b r < 4 * (orderOf (r ^ 2)).totient := by nlinarith
      have hlt' : (cDeg b r : ℚ) < 4 * ((orderOf (r ^ 2)).totient : ℚ) := by
        exact_mod_cast hlt2
      linarith

/-! ## 4. The identity (W) -/

/-- **The identity (W).** For a non-square base `b ≥ 5` and a root of unity `r`:
`∑_p λ_p v_p(c₀(r)) = d(r) / 2`. -/
theorem wtOf_cAbs {b : ℕ} (hb : 5 ≤ b) (hsq : ¬ IsSquare b) {r : ℂ} (hr : IsOfFinOrder r) :
    wtOf (lam b) (cAbs b r) = (cDeg b r : ℚ) / 2 := by
  have hc0 : cAbs b r ≠ 0 := cAbs_ne_zero (by omega) hr
  obtain ⟨N, hN⟩ : ∃ N, countOf (cAbs b r) (orderOf (r ^ 2)) = N := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω, omegaOf (lam b) (cAbs b r) (cDeg b r) (orderOf (r ^ 2)) = ω := ⟨_, rfl⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not (cAbs b r).primeFactors
    (· ∣ 2 * orderOf (r ^ 2)) (fun p => lam b p * ((cAbs b r).factorization p : ℚ))
  have hNsum : (N : ℚ) = ∑ p ∈ (cAbs b r).primeFactors.filter
      (fun q => ¬ q ∣ 2 * orderOf (r ^ 2)), ((cAbs b r).factorization p : ℚ) := by
    rw [← hN, countOf, Nat.cast_sum]
  have hprim : ∑ p ∈ (cAbs b r).primeFactors.filter (fun q => ¬ q ∣ 2 * orderOf (r ^ 2)),
      lam b p * ((cAbs b r).factorization p : ℚ) = ω / N * N := by
    rw [hNsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
    rw [lam_eq_of_dvd hr hp.1.1 hp.1.2.1 hp.2, hN, hω, ← hNsum]
  have hnon : ∑ p ∈ (cAbs b r).primeFactors.filter (· ∣ 2 * orderOf (r ^ 2)),
      lam b p * ((cAbs b r).factorization p : ℚ) = (cDeg b r : ℚ) / 2 - ω := by
    rw [← hω, omegaOf]
    ring
  rw [wtOf, ← hsplit, hprim, hnon]
  by_cases hN0 : N = 0
  · -- no primitive prime: `r⁴ = 1` and `c₀(r)` is a power of 2
    have hω0 : ω = 0 := by
      by_cases h4 : r ^ 4 = 1
      · obtain ⟨m, e, hm, he', hmm, hce, hde⟩ := low_data' (by omega) hsq h4
        have he0 : e ≠ 0 := by omega
        rw [hmm, hce, countOf_low hm, hN0] at hN
        have hm0 : m ≠ 0 := by rcases hm with rfl | rfl <;> norm_num
        have hodd : oddCount e = 0 := by
          rcases Nat.mul_eq_zero.1 hN with h | h
          · exact absurd h hm0
          · exact h
        rw [← hω, hmm, hce, hde, omegaOf_low _ hm he0, (kappa_facts hb he').2.2.1 hodd]
        ring
      · exfalso
        obtain ⟨p, hp, hpc, hpm⟩ := exists_primitive_prime hb hr h4
        have h1 := le_countOf hp (dvd_cAbs_iff.2 hpc) hc0 hpm
        have h2 := hp.factorization_pos_of_dvd hc0 (dvd_cAbs_iff.2 hpc)
        omega
    rw [hN0, hω0]
    simp
  · have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
    rw [div_mul_cancel₀ _ hN']
    ring

/-! ## 5. The theorem -/

/-- The weight of the base is 1. -/
theorem wtOf_base {b : ℕ} (hb : 2 ≤ b) : wtOf (lam b) b = 1 := by
  have hne : b.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
  have hcard : (0 : ℚ) < (b.primeFactors.card : ℚ) := by exact_mod_cast Finset.card_pos.2 hne
  have hterm : ∀ p ∈ b.primeFactors,
      lam b p * (b.factorization p : ℚ) = 1 / (b.primeFactors.card : ℚ) := by
    intro p hp
    have hp' := Nat.mem_primeFactors.1 hp
    have hv : (0 : ℚ) < (b.factorization p : ℚ) := by
      exact_mod_cast hp'.1.factorization_pos_of_dvd hp'.2.2 hp'.2.1
    rw [lam_of_dvd hp'.2.1]
    field_simp
  rw [wtOf, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- Every prime has a positive weight. -/
theorem lam_pos {b : ℕ} (hb : 5 ≤ b) (hsq : ¬ IsSquare b) {p : ℕ} (hp : p.Prime) :
    0 < lam b p := by
  by_cases hpb : p ∣ b
  · rw [lam_of_dvd hpb]
    have h1 : 0 < b.primeFactors.card :=
      Finset.card_pos.2 ⟨p, Nat.mem_primeFactors.2 ⟨hp, hpb, by omega⟩⟩
    have h2 : 0 < b.factorization p := hp.factorization_pos_of_dvd (by omega) hpb
    have h1' : (0 : ℚ) < (b.primeFactors.card : ℚ) := by exact_mod_cast h1
    have h2' : (0 : ℚ) < (b.factorization p : ℚ) := by exact_mod_cast h2
    positivity
  · exact (lam_bounds hb hsq p hp hpb).1

/-- **A positive weight.** For a base `b ≥ 5` that is not a square there is a map on the
rationals, additive on products and positive on every integer `n ≥ 2`, that vanishes on every
`ν(r)²`, `r` a root of unity. -/
theorem posWeight {b : ℕ} (hb : 5 ≤ b) (hsq : ¬ IsSquare b) : PosWeight b := by
  have hb0 : b ≠ 0 := by omega
  obtain ⟨L, hL⟩ : ∃ L : ℚ → ℚ,
      L = fun x => wtOf (lam b) x.num.natAbs - wtOf (lam b) x.den := ⟨_, rfl⟩
  have hmul : ∀ x y : ℚ, x ≠ 0 → y ≠ 0 → L (x * y) = L x + L y := by
    intro x y hx hy
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    have h' : (x * y).num.natAbs * x.den * y.den =
        x.num.natAbs * y.num.natAbs * (x * y).den := by
      have := congrArg Int.natAbs (Rat.mul_num_den' x y)
      simpa [Int.natAbs_mul] using this
    have hn : ∀ z : ℚ, z ≠ 0 → z.num.natAbs ≠ 0 := fun z hz =>
      Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hz)
    have h'' := congrArg (wtOf (lam b)) h'
    rw [wtOf_mul _ (mul_ne_zero (hn _ hxy) x.den_ne_zero) y.den_ne_zero,
      wtOf_mul _ (hn _ hxy) x.den_ne_zero,
      wtOf_mul _ (mul_ne_zero (hn _ hx) (hn _ hy)) (x * y).den_ne_zero,
      wtOf_mul _ (hn _ hx) (hn _ hy)] at h''
    simp only [hL]
    linarith
  have hnat : ∀ n : ℕ, L (n : ℚ) = wtOf (lam b) n := by
    intro n
    simp [hL, wtOf_one]
  have hint : ∀ a : ℤ, L (a : ℚ) = wtOf (lam b) a.natAbs := by
    intro a
    simp [hL, wtOf_one]
  refine ⟨L, hmul, fun n hn => ?_, fun r hr => ?_⟩
  · rw [hnat]
    exact wtOf_pos (fun p hp => lam_pos hb hsq hp) hn
  · have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
    have hc0 := cAbs_ne_zero (by omega : 2 ≤ b) hr
    have hc0' : (minpoly ℤ (tB b - r)).eval 0 ≠ 0 := Int.natAbs_ne_zero.1 hc0
    have hx : nuSq b r ≠ 0 := by
      rw [nuSq]
      exact div_ne_zero (pow_ne_zero 2 (by exact_mod_cast hc0')) (pow_ne_zero _ hbQ)
    have hprod : nuSq b r * ((b ^ cDeg b r : ℕ) : ℚ) =
        ((((minpoly ℤ (tB b - r)).eval 0) ^ 2 : ℤ) : ℚ) := by
      rw [nuSq, cDeg]
      push_cast
      field_simp
    have hcabs : (((minpoly ℤ (tB b - r)).eval 0) ^ 2).natAbs = cAbs b r ^ 2 := by
      rw [Int.natAbs_pow, cAbs]
    have h1 := hmul (nuSq b r) ((b ^ cDeg b r : ℕ) : ℚ) hx
      (by exact_mod_cast pow_ne_zero _ hb0)
    rw [hprod, hint, hnat, hcabs, wtOf_pow _ hc0, wtOf_pow _ hb0, wtOf_base (by omega),
      wtOf_cAbs hb hsq hr] at h1
    push_cast at h1
    linarith

end BaseB

end PiFormula
