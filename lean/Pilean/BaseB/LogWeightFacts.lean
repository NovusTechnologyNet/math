/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.BaseB.GoodPrimes
public import Pilean.BaseB.LogDefs

/-!
# The constant term of the minimal polynomial of `√b - r`: its primes

Let `t = √b`, let `r` be a root of unity, `μ_r` the minimal polynomial of `t - r` over `ℤ`,
`c₀(r) = μ_r(0)` and `d(r) = deg μ_r` (`cAbs b r = |c₀(r)|`, `cDeg b r = d(r)`). This file
proves the facts about the primes of `c₀(r)` used by the file `LogWeight` (research note
`research/2026-11-22-log-primes/00_summary.md`, section 4). All proofs work with prime ideals of
the algebraic integers, as in `Support`; there is no Galois theory.

* `dvd_minpoly_eval_zero_of_inP`: a prime `p` with `p, x ∈ P` divides the constant term of the
  minimal polynomial of `x` (the converse of `hasPrime_of_dvd_minpoly_eval_zero`).
* **F1** (`order_facts_of_dvd`): a prime `p ∣ c₀(r)` does not divide `b`, and the order `m` of
  `r²` is `ord_p(b) · p^a`.
* `exists_home_root`: every prime `p ∤ b` divides `c₀(r)` for some `r` with `r²` of order
  `ord_p(b)`.
* **F3** (`data_eq_of_common_prime`, `nuSq_eq_of_common_prime`): if `r^(2m) = r'^(2m) = 1` and a
  prime `p ∤ 2m` divides `c₀(r)` and `c₀(r')`, then `μ_{r'}` is the minimal polynomial of
  `t - r` or of `-(t - r)`; so `d(r') = d(r)`, `|c₀(r')| = |c₀(r)|` and `ν(r')² = ν(r)²`.
* **F4** (`exists_primitive_prime`): for `b ≥ 5` and `r⁴ ≠ 1`, `c₀(r)` has a prime factor that
  does not divide `2m` (from `goodPrimesB`).
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-- `|c₀(r)|`: the absolute value of the constant term of the minimal polynomial of `√b - r`
over `ℤ`. -/
noncomputable def cAbs (b : ℕ) (r : ℂ) : ℕ := ((minpoly ℤ (tB b - r)).eval 0).natAbs

/-- `d(r)`: the degree of the minimal polynomial of `√b - r` over `ℤ`. -/
noncomputable def cDeg (b : ℕ) (r : ℂ) : ℕ := (minpoly ℤ (tB b - r)).natDegree

theorem dvd_cAbs_iff {b : ℕ} {r : ℂ} {p : ℕ} :
    p ∣ cAbs b r ↔ (p : ℤ) ∣ (minpoly ℤ (tB b - r)).eval 0 :=
  Int.natCast_dvd.symm

/-! ## 1. Prime ideals and constant terms -/

theorem inP_zero (P : Ideal Aint) : InP P 0 :=
  ⟨isIntegral_zero, P.zero_mem⟩

/-- The constant term of the minimal polynomial of `x` is a multiple of `x`. -/
theorem inP_minpoly_eval_zero {P : Ideal Aint} {x : ℂ} (h : InP P x) :
    InP P (((minpoly ℤ x).eval 0 : ℤ) : ℂ) := by
  have hx := h.isIntegral
  have e : (((minpoly ℤ x).eval 0 : ℤ) : ℂ) = -(aeval x (minpoly ℤ x).divX * x) := by
    have h1 := congrArg (aeval x) (divX_mul_X_add (minpoly ℤ x))
    rw [minpoly.aeval, map_add, map_mul, aeval_X, aeval_C, coeff_zero_eq_eval_zero] at h1
    have h2 : (algebraMap ℤ ℂ) ((minpoly ℤ x).eval 0) = (((minpoly ℤ x).eval 0 : ℤ) : ℂ) := rfl
    rw [h2] at h1
    linear_combination h1
  rw [e]
  exact (h.mul_left (Base3.isIntegral_aeval hx _)).neg

theorem inP_intCast_of_dvd {P : Ideal Aint} {p : ℕ} (hpP : InP P (p : ℂ)) {a : ℤ}
    (h : (p : ℤ) ∣ a) : InP P (a : ℂ) := by
  obtain ⟨k, rfl⟩ := h
  have := hpP.mul_right (isIntegral_intCast k)
  simpa using this

/-- An integer in a prime ideal that contains the prime `p` is a multiple of `p`. -/
theorem dvd_of_inP_intCast {P : Ideal Aint} [P.IsPrime] {p : ℕ} (hp : p.Prime)
    (hpP : InP P (p : ℂ)) {a : ℤ} (h : InP P (a : ℂ)) : (p : ℤ) ∣ a := by
  by_contra hnd
  have hcop : Nat.Coprime a.natAbs p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h' => hnd (Int.natCast_dvd.2 h')).symm
  have hna : InP P ((a.natAbs : ℕ) : ℂ) := by
    rcases Int.natAbs_eq a with h' | h'
    · have e : ((a.natAbs : ℕ) : ℂ) = (a : ℂ) := by
        conv_rhs => rw [h']
        simp
      rw [e]
      exact h
    · have e : ((a.natAbs : ℕ) : ℂ) = -(a : ℂ) := by
        conv_rhs => rw [h']
        simp
      rw [e]
      exact h.neg
  exact not_inP_coprime hcop hna hpP

/-- **Primes of the constant term, converse.** If a prime ideal contains the prime `p` and
`x`, then `p` divides the constant term of the minimal polynomial of `x`. -/
theorem dvd_minpoly_eval_zero_of_inP {P : Ideal Aint} [P.IsPrime] {p : ℕ} (hp : p.Prime)
    (hpP : InP P (p : ℂ)) {x : ℂ} (hx : InP P x) : (p : ℤ) ∣ (minpoly ℤ x).eval 0 :=
  dvd_of_inP_intCast hp hpP (inP_minpoly_eval_zero hx)

/-- Some prime ideal of the algebraic integers contains the prime `p`. -/
theorem exists_prime_ideal {p : ℕ} (hp : p.Prime) :
    ∃ P : Ideal Aint, P.IsPrime ∧ InP P (p : ℂ) := by
  have key : ∀ U V : ℤ[X], aeval (0 : ℂ) (U * C (p : ℤ) + V * X) ≠ 1 := by
    intro U V h
    rw [aeval_zero_int] at h
    simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, add_zero] at h
    have h1 : U.eval 0 * (p : ℤ) = 1 := by exact_mod_cast h
    exact hp.not_dvd_one (Int.natCast_dvd_natCast.1 ⟨U.eval 0, by
      rw [Nat.cast_one, ← h1, mul_comm]⟩)
  obtain ⟨P, hP, hpP, -⟩ := Base3.hasPrime_of_not_unit isIntegral_zero p X key
  exact ⟨P, hP, hpP⟩

theorem inP_pow_sub_pow {P : Ideal Aint} {u v : ℂ} (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v)
    (h : InP P (u - v)) (k : ℕ) : InP P (u ^ k - v ^ k) := by
  induction k with
  | zero => simpa using inP_zero P
  | succ k ih =>
    have e : u ^ (k + 1) - v ^ (k + 1) = u * (u ^ k - v ^ k) + (u - v) * v ^ k := by ring
    rw [e]
    exact (ih.mul_left hu).add (h.mul_right (hv.pow k))

theorem inP_multiset_prod {P : Ideal Aint} [P.IsPrime] (s : Multiset ℂ)
    (hs : ∀ z ∈ s, IsIntegral ℤ z) (h : InP P s.prod) : ∃ z ∈ s, InP P z := by
  induction s using Multiset.induction_on with
  | empty => exact absurd (by simpa using h) not_inP_one
  | cons a s ih =>
    rw [Multiset.prod_cons] at h
    have hs' : ∀ z ∈ s, IsIntegral ℤ z := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    rcases inP_mul (hs a (Multiset.mem_cons_self a s)) (IsIntegral.multiset_prod hs') h with
      h | h
    · exact ⟨a, Multiset.mem_cons_self a s, h⟩
    · obtain ⟨z, hz, h⟩ := ih hs' h
      exact ⟨z, Multiset.mem_cons_of_mem hz, h⟩

/-! ## 2. F1: the order of `b` modulo a prime of `c₀(r)` -/

/-- With `p, √b - r ∈ P`: `b^k ≡ 1 (mod p)` if and only if `r^(2k) - 1 ∈ P`. -/
theorem natCast_pow_eq_one_iff_inP {b : ℕ} {P : Ideal Aint} [P.IsPrime] {p : ℕ}
    (hp : p.Prime) (hpP : InP P (p : ℂ)) {r : ℂ} (hr : IsOfFinOrder r)
    (hx : InP P (tB b - r)) (k : ℕ) :
    ((b : ℕ) : ZMod p) ^ k = 1 ↔ InP P ((r ^ 2) ^ k - 1) := by
  have:= Fact.mk hp
  have hri := isIntegral_of_finOrder hr
  have hsq : InP P (tB b ^ 2 - r ^ 2) := by
    have := hx.mul_right ((isIntegral_tB b).add hri)
    rwa [show (tB b - r) * (tB b + r) = tB b ^ 2 - r ^ 2 by ring] at this
  have hk : InP P ((b : ℂ) ^ k - (r ^ 2) ^ k) := by
    have := inP_pow_sub_pow ((isIntegral_tB b).pow 2) (hri.pow 2) hsq k
    rwa [tB_sq] at this
  have hcast : ((((b : ℤ) ^ k - 1 : ℤ)) : ℂ) = (b : ℂ) ^ k - 1 := by push_cast; ring
  have hz : ((b : ℕ) : ZMod p) ^ k = 1 ↔ (p : ℤ) ∣ (b : ℤ) ^ k - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero.symm
  rw [hz]
  constructor
  · intro h
    have h1 := inP_intCast_of_dvd hpP h
    rw [hcast] at h1
    have := h1.sub hk
    rwa [show (b : ℂ) ^ k - 1 - ((b : ℂ) ^ k - (r ^ 2) ^ k) = (r ^ 2) ^ k - 1 by ring] at this
  · intro h
    apply dvd_of_inP_intCast hp hpP
    rw [hcast]
    have := h.add hk
    rwa [show (r ^ 2) ^ k - 1 + ((b : ℂ) ^ k - (r ^ 2) ^ k) = (b : ℂ) ^ k - 1 by ring] at this

/-- **F1, with ideals.** If a prime ideal contains the prime `p` and `√b - r`, then `p` does
not divide `b`, and the order of `r²` is the order of `b` modulo `p` times a power of `p`. -/
theorem order_facts_of_inP {b : ℕ} {P : Ideal Aint} [P.IsPrime] {p : ℕ} (hp : p.Prime)
    (hpP : InP P (p : ℂ)) {r : ℂ} (hr : IsOfFinOrder r) (hx : InP P (tB b - r)) :
    ¬ p ∣ b ∧ ∃ a, orderOf (r ^ 2) = orderOf ((b : ℕ) : ZMod p) * p ^ a := by
  have hpb : ¬ p ∣ b := by
    rintro ⟨k, rfl⟩
    have h1 : InP P (tB (p * k) ^ 2) := by
      rw [tB_sq]
      push_cast
      exact hpP.mul_right (isIntegral_natCast' k)
    have h3 := (inP_of_pow (isIntegral_tB _) h1).2.sub hx
    rw [sub_sub_cancel] at h3
    exact not_inP_root hr h3
  refine ⟨hpb, ?_⟩
  have hr2 : IsOfFinOrder (r ^ 2) := hr.pow
  have hm0 : 0 < orderOf (r ^ 2) := hr2.orderOf_pos
  have h1 : ((b : ℕ) : ZMod p) ^ orderOf (r ^ 2) = 1 := by
    rw [natCast_pow_eq_one_iff_inP hp hpP hr hx, pow_orderOf_eq_one, sub_self]
    exact inP_zero P
  have hdvd : orderOf ((b : ℕ) : ZMod p) ∣ orderOf (r ^ 2) := orderOf_dvd_of_pow_eq_one h1
  have he0 : orderOf ((b : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hdvd
    omega
  have h2 := (natCast_pow_eq_one_iff_inP hp hpP hr hx _).1
    (pow_orderOf_eq_one ((b : ℕ) : ZMod p))
  obtain ⟨a, ha⟩ := orderOf_eq_prime_pow_of_inP hp hpP hr2.pow h2
  rw [orderOf_pow' _ he0, Nat.gcd_eq_right hdvd] at ha
  exact ⟨a, by rw [← ha, Nat.mul_div_cancel' hdvd]⟩

/-- **F1.** A prime `p` that divides `c₀(r)` does not divide `b`, and the order of `r²` is the
order of `b` modulo `p` times a power of `p`. -/
theorem order_facts_of_dvd {b : ℕ} {p : ℕ} (hp : p.Prime) {r : ℂ} (hr : IsOfFinOrder r)
    (hdvd : (p : ℤ) ∣ (minpoly ℤ (tB b - r)).eval 0) :
    ¬ p ∣ b ∧ ∃ a, orderOf (r ^ 2) = orderOf ((b : ℕ) : ZMod p) * p ^ a := by
  obtain ⟨P, hP, hpP, hxP⟩ :=
    hasPrime_of_dvd_minpoly_eval_zero (isIntegral_tB_sub b hr) hp hdvd
  have:= hP
  exact order_facts_of_inP hp hpP hr hxP

/-- The order of `b` modulo a prime `p ∤ b` divides `p - 1`. -/
theorem orderOf_zmod_dvd_pred {b p : ℕ} (hp : p.Prime) (hpb : ¬ p ∣ b) :
    orderOf ((b : ℕ) : ZMod p) ∣ p - 1 := by
  have:= Fact.mk hp
  exact ZMod.orderOf_dvd_card_sub_one fun h => hpb ((ZMod.natCast_eq_zero_iff b p).1 h)

/-- A prime factor of `e p^a`, `e ∣ p - 1`, is at most `p`. -/
theorem le_of_prime_dvd_mul_pow {e p a q : ℕ} (hp : p.Prime) (he : e ∣ p - 1) (hq : q.Prime)
    (h : q ∣ e * p ^ a) : q ≤ p := by
  rcases (Nat.Prime.dvd_mul hq).1 h with h1 | h1
  · have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) (h1.trans he)
    omega
  · exact Nat.le_of_dvd hp.pos (hq.dvd_of_dvd_pow h1)

/-- `φ(e p^a) ≥ φ(e) (p - 1)` for `e ∣ p - 1` and `a ≥ 1`. -/
theorem totient_mul_pred_le {e p a : ℕ} (hp : p.Prime) (he : e ∣ p - 1) (ha : a ≠ 0) :
    e.totient * (p - 1) ≤ (e * p ^ a).totient := by
  have h1 : Nat.Coprime (p - 1) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2
      (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt) (by have := hp.pos; omega))).symm
  have hcop : Nat.Coprime e (p ^ a) := Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_left he h1)
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow hp (Nat.pos_of_ne_zero ha)]
  exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (pow_pos hp.pos _))

/-! ## 3. The home of a prime -/

/-- **A home for every prime.** A prime `p ∤ b` divides `c₀(r)` for some root of unity `r`
whose square has order `ord_p(b)`. -/
theorem exists_home_root {b p : ℕ} (hp : p.Prime) (hpb : ¬ p ∣ b) :
    ∃ r : ℂ, IsOfFinOrder r ∧ orderOf (r ^ 2) = orderOf ((b : ℕ) : ZMod p) ∧
      (p : ℤ) ∣ (minpoly ℤ (tB b - r)).eval 0 := by
  classical
  have:= Fact.mk hp
  obtain ⟨P, hP, hpP⟩ := exists_prime_ideal hp
  have:= hP
  obtain ⟨e, he⟩ : ∃ e, orderOf ((b : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  have he0 : 0 < e :=
    Nat.pos_of_dvd_of_pos (he ▸ orderOf_zmod_dvd_pred hp hpb) (Nat.sub_pos_of_lt hp.one_lt)
  have h1 : ((b : ℕ) : ZMod p) ^ e = 1 := he ▸ pow_orderOf_eq_one _
  have h2 : InP P ((b : ℂ) ^ e - 1) := by
    have hd : (p : ℤ) ∣ (b : ℤ) ^ e - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [h1, sub_self]
    have := inP_intCast_of_dvd hpP hd
    rwa [show ((((b : ℤ) ^ e - 1 : ℤ)) : ℂ) = (b : ℂ) ^ e - 1 by push_cast; ring] at this
  have hfac : (b : ℂ) ^ e - 1 = ∏ ζ ∈ nthRootsFinset (2 * e) (1 : ℂ), (tB b - ζ) := by
    have h := congrArg (Polynomial.eval (tB b)) (X_pow_sub_one_eq_prod (by omega : 0 < 2 * e)
      (Complex.isPrimitiveRoot_exp (2 * e) (by omega)))
    rw [eval_prod] at h
    simp only [eval_sub, eval_pow, eval_X, eval_one, eval_C] at h
    rw [← h, pow_mul, tB_sq]
  rw [hfac] at h2
  have hroot : ∀ ζ ∈ nthRootsFinset (2 * e) (1 : ℂ), IsOfFinOrder ζ := fun ζ hζ =>
    isOfFinOrder_iff_pow_eq_one.2 ⟨2 * e, by omega, (mem_nthRootsFinset (by omega) 1).1 hζ⟩
  obtain ⟨ζ, hζmem, hζ⟩ :=
    inP_prod _ _ (fun ζ hζ => isIntegral_tB_sub b (hroot ζ hζ)) h2
  have hζfin := hroot ζ hζmem
  refine ⟨ζ, hζfin, ?_, dvd_minpoly_eval_zero_of_inP hp hpP hζ⟩
  obtain ⟨-, a, ha⟩ := order_facts_of_inP hp hpP hζfin hζ
  rw [he] at ha ⊢
  have hdvd : orderOf (ζ ^ 2) ∣ e := orderOf_dvd_of_pow_eq_one (by
    rw [← pow_mul]
    exact (mem_nthRootsFinset (by omega) 1).1 hζmem)
  rw [ha] at hdvd ⊢
  have hle := Nat.le_of_dvd he0 hdvd
  have hpa : p ^ a = 1 := by
    have h0 : 0 < p ^ a := pow_pos hp.pos a
    nlinarith
  rw [hpa, mul_one]

/-! ## 4. F3: a common prime not dividing `2m` -/

theorem aeval_cyclotomic_eq_zero_iff {n : ℕ} (hn : 0 < n) (s : ℂ) :
    aeval s (cyclotomic n ℤ) = 0 ↔ IsPrimitiveRoot s n := by
  have: NeZero ((n : ℕ) : ℂ) := ⟨by exact_mod_cast hn.ne'⟩
  rw [← isRoot_cyclotomic_iff (R := ℂ), IsRoot.def, ← map_cyclotomic n (algebraMap ℤ ℂ),
    eval_map_algebraMap]

/-- A root of the minimal polynomial of `√b - r` is `√b - s` or `-√b - s`, with `s` a root of
unity of the same order as `r`. -/
theorem root_form {b : ℕ} {r : ℂ} (hr : IsOfFinOrder r) {z : ℂ}
    (hz : aeval z (minpoly ℤ (tB b - r)) = 0) :
    ∃ s : ℂ, IsPrimitiveRoot s (orderOf r) ∧ (z = tB b - s ∨ z = -tB b - s) := by
  have hn := hr.orderOf_pos
  obtain ⟨F, hF⟩ := exists_symmetrize b (cyclotomic (orderOf r) ℤ)
  have hFx : aeval (tB b - r) F = 0 := by
    rw [hF, sub_sub_cancel, aeval_cyclotomic_eq_zero (IsPrimitiveRoot.orderOf r) hn, zero_mul]
  obtain ⟨H, hH⟩ := minpoly.isIntegrallyClosed_dvd (isIntegral_tB_sub b hr) hFx
  have hFz : aeval z F = 0 := by rw [hH, map_mul, hz, zero_mul]
  rw [hF] at hFz
  rcases mul_eq_zero.1 hFz with h | h
  · exact ⟨tB b - z, (aeval_cyclotomic_eq_zero_iff hn _).1 h, Or.inl (by ring)⟩
  · exact ⟨-tB b - z, (aeval_cyclotomic_eq_zero_iff hn _).1 h, Or.inr (by ring)⟩

/-- If the constant term of the minimal polynomial of `x` lies in a prime ideal, so does a
root of this polynomial. -/
theorem exists_root_inP {P : Ideal Aint} [P.IsPrime] {x : ℂ} (hx : IsIntegral ℤ x)
    (h : InP P (((minpoly ℤ x).eval 0 : ℤ) : ℂ)) :
    ∃ z : ℂ, aeval z (minpoly ℤ x) = 0 ∧ InP P z := by
  obtain ⟨μ, hμdef⟩ : ∃ μ, minpoly ℤ x = μ := ⟨_, rfl⟩
  have hμ : μ.Monic := hμdef ▸ minpoly.monic hx
  rw [hμdef] at h ⊢
  have hmon : (μ.map (algebraMap ℤ ℂ)).Monic := hμ.map _
  have hsplit : (μ.map (algebraMap ℤ ℂ)).Splits := IsAlgClosed.splits _
  have hc0 : ((μ.eval 0 : ℤ) : ℂ) =
      (-1) ^ (μ.map (algebraMap ℤ ℂ)).natDegree * (μ.map (algebraMap ℤ ℂ)).roots.prod := by
    rw [← hsplit.coeff_zero_eq_prod_roots_of_monic hmon, coeff_zero_eq_eval_zero,
      eval_map_algebraMap, aeval_zero_int]
  have hroot : ∀ z ∈ (μ.map (algebraMap ℤ ℂ)).roots, aeval z μ = 0 := by
    intro z hz
    rw [mem_roots hmon.ne_zero, IsRoot.def, eval_map_algebraMap] at hz
    exact hz
  have hint : ∀ z ∈ (μ.map (algebraMap ℤ ℂ)).roots, IsIntegral ℤ z :=
    fun z hz => ⟨μ, hμ, hroot z hz⟩
  have hprod : InP P (μ.map (algebraMap ℤ ℂ)).roots.prod := by
    have := h.mul_left (isIntegral_one.neg.pow (μ.map (algebraMap ℤ ℂ)).natDegree)
    rw [hc0, ← mul_assoc, ← mul_pow] at this
    simpa using this
  obtain ⟨z, hz, hzP⟩ := inP_multiset_prod _ hint hprod
  exact ⟨z, hroot z hz, hzP⟩

/-- A root `z` of the minimal polynomial of `y` over `ℤ` has the same minimal polynomial. -/
theorem minpoly_eq_of_root {y z : ℂ} (hy : IsIntegral ℤ y) (hz : aeval z (minpoly ℤ y) = 0) :
    minpoly ℤ z = minpoly ℤ y := by
  have hzi : IsIntegral ℤ z := ⟨minpoly ℤ y, minpoly.monic hy, hz⟩
  exact eq_of_monic_of_associated (minpoly.monic hzi) (minpoly.monic hy)
    ((minpoly.irreducible hzi).associated_of_dvd (minpoly.irreducible hy)
      (minpoly.isIntegrallyClosed_dvd hzi hz))

/-- The minimal polynomials of `y` and `-y` over `ℤ` have the same degree, and constant terms
equal up to sign. -/
theorem minpoly_neg_data {y : ℂ} (hy : IsIntegral ℤ y) :
    (minpoly ℤ (-y)).natDegree = (minpoly ℤ y).natDegree ∧
      ((minpoly ℤ (-y)).eval 0).natAbs = ((minpoly ℤ y).eval 0).natAbs := by
  have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hy
  have h2 := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hy.neg
  have h3 := minpoly.neg (A := ℚ) y
  rw [h1, h2] at h3
  have h4 : minpoly ℤ (-y) = (-1) ^ (minpoly ℤ y).natDegree * (minpoly ℤ y).comp (-X) := by
    apply map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
    rw [h3, (minpoly.monic hy).natDegree_map]
    simp [Polynomial.map_comp]
  rw [h4]
  constructor
  · rcases neg_one_pow_eq_or ℤ[X] (minpoly ℤ y).natDegree with h | h <;> rw [h] <;>
      simp [natDegree_comp]
  · simp [eval_comp, Int.natAbs_mul, Int.natAbs_pow]

/-- **F3.** Let `r, r'` be roots of unity with `r^(2m) = r'^(2m) = 1`, and let `p` be a prime
not dividing `2m` that divides `c₀(r)` and `c₀(r')`. Then the minimal polynomial of `√b - r'`
is that of `√b - r` or of `-(√b - r)`. -/
theorem minpoly_eq_of_common_prime {b : ℕ} {r r' : ℂ} (hr : IsOfFinOrder r)
    (hr' : IsOfFinOrder r') {m : ℕ} (hm : r ^ (2 * m) = 1) (hm' : r' ^ (2 * m) = 1) {p : ℕ}
    (hp : p.Prime) (hpm : ¬ p ∣ 2 * m) (hd : (p : ℤ) ∣ (minpoly ℤ (tB b - r)).eval 0)
    (hd' : (p : ℤ) ∣ (minpoly ℤ (tB b - r')).eval 0) :
    minpoly ℤ (tB b - r') = minpoly ℤ (tB b - r) ∨
      minpoly ℤ (tB b - r') = minpoly ℤ (-(tB b - r)) := by
  obtain ⟨P, hP, hpP, hxP⟩ := hasPrime_of_dvd_minpoly_eval_zero (isIntegral_tB_sub b hr) hp hd
  have:= hP
  have hx' := isIntegral_tB_sub b hr'
  obtain ⟨z, hz, hzP⟩ := exists_root_inP hx' (inP_intCast_of_dvd hpP hd')
  obtain ⟨s, hs, hzs⟩ := root_form hr' hz
  have hm0 : 0 < 2 * m := Nat.pos_of_ne_zero fun h => hpm (h ▸ dvd_zero p)
  have hs2 : s ^ (2 * m) = 1 := by
    obtain ⟨k, hk⟩ := orderOf_dvd_of_pow_eq_one hm'
    rw [hk, pow_mul, hs.pow_eq_one, one_pow]
  have hr0 := ne_zero_of_finOrder hr
  have hrinv : IsIntegral ℤ r⁻¹ := isIntegral_of_finOrder (isOfFinOrder_inv' hr)
  -- a root of unity `v` with `v^(2m) = 1` and `t - v ∈ P` is `r`
  have key : ∀ v : ℂ, v ^ (2 * m) = 1 → InP P (tB b - v) → v = r := by
    intro v hv hvP
    have hvfin : IsOfFinOrder v := isOfFinOrder_iff_pow_eq_one.2 ⟨2 * m, hm0, hv⟩
    have hu1 : InP P (v / r - 1) := by
      have hd := hxP.sub hvP
      rw [show tB b - r - (tB b - v) = v - r by ring] at hd
      have := hd.mul_right hrinv
      rwa [show (v - r) * r⁻¹ = v / r - 1 by field_simp] at this
    obtain ⟨a, ha⟩ := orderOf_eq_prime_pow_of_inP hp hpP (isOfFinOrder_div' hvfin hr) hu1
    have hdvd : orderOf (v / r) ∣ 2 * m :=
      orderOf_dvd_of_pow_eq_one (by rw [div_pow, hv, hm, div_one])
    have ha0 : a = 0 := by
      by_contra h0
      exact hpm ((dvd_pow_self p h0).trans (ha ▸ hdvd))
    rw [ha0, pow_zero, orderOf_eq_one_iff, div_eq_one_iff_eq hr0] at ha
    exact ha
  rcases hzs with h | h
  · left
    have hsr : s = r := key s hs2 (h ▸ hzP)
    rw [← minpoly_eq_of_root hx' hz, h, hsr]
  · right
    have hns : (-s) ^ (2 * m) = 1 := by rw [pow_mul, neg_sq, ← pow_mul, hs2]
    have hP' : InP P (tB b - -s) := by
      have := hzP.neg
      rwa [h, show -(-tB b - s) = tB b - -s by ring] at this
    have hsr : -s = r := key (-s) hns hP'
    rw [← minpoly_eq_of_root hx' hz, h, ← hsr]
    congr 1
    ring

/-- **F3, the data.** In the situation of `minpoly_eq_of_common_prime`, `d(r') = d(r)` and
`|c₀(r')| = |c₀(r)|`. -/
theorem data_eq_of_common_prime {b : ℕ} {r r' : ℂ} (hr : IsOfFinOrder r)
    (hr' : IsOfFinOrder r') {m : ℕ} (hm : r ^ (2 * m) = 1) (hm' : r' ^ (2 * m) = 1) {p : ℕ}
    (hp : p.Prime) (hpm : ¬ p ∣ 2 * m) (hd : (p : ℤ) ∣ (minpoly ℤ (tB b - r)).eval 0)
    (hd' : (p : ℤ) ∣ (minpoly ℤ (tB b - r')).eval 0) :
    cDeg b r' = cDeg b r ∧ cAbs b r' = cAbs b r := by
  rcases minpoly_eq_of_common_prime hr hr' hm hm' hp hpm hd hd' with h | h
  · simp only [cDeg, cAbs, h, and_self]
  · obtain ⟨h1, h2⟩ := minpoly_neg_data (isIntegral_tB_sub b hr)
    simp only [cDeg, cAbs, h]
    exact ⟨h1, h2⟩

/-- **F3, for `ν²`.** If `r²` and `r'²` have the same order `m`, and a prime not dividing `2m`
divides `c₀(r)` and `c₀(r')`, then `ν(r)² = ν(r')²`. -/
theorem nuSq_eq_of_common_prime {b : ℕ} {r r' : ℂ} (hr : IsOfFinOrder r)
    (hr' : IsOfFinOrder r') (hord : orderOf (r' ^ 2) = orderOf (r ^ 2)) {p : ℕ} (hp : p.Prime)
    (hpm : ¬ p ∣ 2 * orderOf (r ^ 2)) (hd : (p : ℤ) ∣ (minpoly ℤ (tB b - r)).eval 0)
    (hd' : (p : ℤ) ∣ (minpoly ℤ (tB b - r')).eval 0) : nuSq b r = nuSq b r' := by
  have hm : r ^ (2 * orderOf (r ^ 2)) = 1 := by rw [pow_mul, pow_orderOf_eq_one]
  have hm' : r' ^ (2 * orderOf (r ^ 2)) = 1 := by rw [pow_mul, ← hord, pow_orderOf_eq_one]
  obtain ⟨h1, h2⟩ := data_eq_of_common_prime hr hr' hm hm' hp hpm hd hd'
  simp only [cDeg, cAbs] at h1 h2
  have h3 : ((minpoly ℤ (tB b - r')).eval 0) ^ 2 = ((minpoly ℤ (tB b - r)).eval 0) ^ 2 := by
    rw [← Int.natAbs_sq, h2, Int.natAbs_sq]
  have h4 : (((minpoly ℤ (tB b - r')).eval 0 : ℤ) : ℚ) ^ 2 =
      (((minpoly ℤ (tB b - r)).eval 0 : ℤ) : ℚ) ^ 2 := by exact_mod_cast h3
  rw [nuSq, nuSq, h1, h4]

/-! ## 5. F4: a primitive prime -/

/-- **F4.** For `b ≥ 5` and a root of unity `r` with `r⁴ ≠ 1`, some prime factor of `c₀(r)`
does not divide `2m`, `m` the order of `r²`. -/
theorem exists_primitive_prime {b : ℕ} (hb : 5 ≤ b) {r : ℂ} (hr : IsOfFinOrder r)
    (h4 : r ^ 4 ≠ 1) : ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ (minpoly ℤ (tB b - r)).eval 0 ∧
      ¬ p ∣ 2 * orderOf (r ^ 2) := by
  obtain ⟨P, hP, p, hp, hp2, -, hpr, hpP, hxP⟩ := goodPrimesB hb r hr h4
  have:= hP
  refine ⟨p, hp, dvd_minpoly_eval_zero_of_inP hp hpP hxP, ?_⟩
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  · exact hpr (h.trans (orderOf_pow_dvd 2))

end BaseB

end PiFormula
