/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula.Relations

/-!
# Step 2 of Part III: every multiplicative relation lives on `R0`

With `t = 1 + i` and `w_r = 1 - r/t`, a *multiplicative relation* is a finite family of
integers `e_r` (`r` roots of unity) with `∏ w_r^(e_r)` a root of unity (`IsRelation`). Step 2
of the note says that every relation, at every period, is supported on the 24 roots
`R0 = {ζ_120^j}` of order dividing 120.

The argument works with prime ideals `P` of the ring of algebraic integers of `ℂ`; `InP P z`
says that the algebraic integer `z` lies in `P`.

* **Residue lemma** (`orderOf_eq_prime_pow_of_inP`): if `p ∈ P` and `u - 1 ∈ P` for a root of
  unity `u`, then `ord u` is a power of `p`. (For a prime `ℓ ≠ p` dividing `ord u`,
  `ℓ = ∏ (1 - μ)` over the primitive `ℓ`-th roots `μ`, a product in `P`.)
* **Private prime** (`coeff_eq_zero_of_private_ideal`): if `t - r₀ ∈ P` but `t ∉ P` and
  `t - r ∉ P` for the other `r`, then `e_{r₀} = 0`.
* **Closure** (`R0_closed`): for every odd prime `p`, `R0` contains the `p'`-part of each of
  its elements (a finite check, by `decide`).
* **Support** (`support_subset_R0`): the review's largest-order argument. Take `r ∉ R0` with
  `e_r ≠ 0` of largest order, and a prime `P ∋ p, t - r` with `p` odd, `p ∤ ord r`. If also
  `t - r' ∈ P`, then `r'/r` has order `p^a`, `a ≥ 1`, so `ord r' = ord r · p^a`: `r'` is in
  `R0` (largest order), and then `r`, its `p'`-part, is in `R0` (closure). So `P` is private
  to `r`, and `e_r = 0`.

The one arithmetic input is `GoodPrimes`: every root of unity outside `R0` has such a prime.
It comes from Lemma 3, Bang's theorem and the Galois table (milestone M4.2 of
lean/PART3_PLAN.md, not yet in Lean), so `support_subset_R0` is stated as `GoodPrimes → ...`.
-/

@[expose] public section

open Complex

namespace PiFormula

/-! ## 1. Algebraic integers and membership in a prime ideal -/

/-- The algebraic integers of `ℂ`. -/
abbrev Aint : Subalgebra ℤ ℂ := integralClosure ℤ ℂ

theorem isIntegral_of_finOrder {r : ℂ} (h : IsOfFinOrder r) : IsIntegral ℤ r :=
  IsIntegral.of_pow h.orderOf_pos (by rw [pow_orderOf_eq_one]; exact isIntegral_one)

theorem isOfFinOrder_I : IsOfFinOrder I :=
  isOfFinOrder_iff_pow_eq_one.2 ⟨4, by norm_num, Complex.I_pow_four⟩

theorem isIntegral_tC : IsIntegral ℤ tC :=
  isIntegral_one.add (isIntegral_of_finOrder isOfFinOrder_I)

theorem isIntegral_intCast (a : ℤ) : IsIntegral ℤ (a : ℂ) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := a)

theorem isIntegral_natCast' (a : ℕ) : IsIntegral ℤ (a : ℂ) := by
  simpa using isIntegral_intCast a

theorem ne_zero_of_finOrder {z : ℂ} (h : IsOfFinOrder z) : z ≠ 0 := by
  intro h0
  subst h0
  have := pow_orderOf_eq_one (0 : ℂ)
  rw [zero_pow h.orderOf_pos.ne'] at this
  exact zero_ne_one this

theorem isOfFinOrder_inv' {z : ℂ} (h : IsOfFinOrder z) : IsOfFinOrder z⁻¹ :=
  isOfFinOrder_iff_pow_eq_one.2 ⟨orderOf z, h.orderOf_pos, by
    rw [inv_pow, pow_orderOf_eq_one, inv_one]⟩

theorem isOfFinOrder_div' {a b : ℂ} (ha : IsOfFinOrder a) (hb : IsOfFinOrder b) :
    IsOfFinOrder (a / b) :=
  isOfFinOrder_iff_pow_eq_one.2 ⟨orderOf a * orderOf b, Nat.mul_pos ha.orderOf_pos hb.orderOf_pos,
    by rw [div_pow, pow_mul, pow_orderOf_eq_one, one_pow, mul_comm, pow_mul, pow_orderOf_eq_one,
      one_pow, div_one]⟩

section InP

variable {P : Ideal Aint}

/-- The algebraic integer `z` lies in `P`. -/
def InP (P : Ideal Aint) (z : ℂ) : Prop := ∃ h : IsIntegral ℤ z, (⟨z, h⟩ : Aint) ∈ P

theorem InP.isIntegral {z : ℂ} (h : InP P z) : IsIntegral ℤ z := h.1

theorem InP.mul_left {z w : ℂ} (hz : InP P z) (hw : IsIntegral ℤ w) : InP P (w * z) := by
  obtain ⟨h, hm⟩ := hz
  exact ⟨hw.mul h, P.mul_mem_left (⟨w, hw⟩ : Aint) hm⟩

theorem InP.mul_right {z w : ℂ} (hz : InP P z) (hw : IsIntegral ℤ w) : InP P (z * w) := by
  rw [mul_comm]; exact hz.mul_left hw

theorem InP.add {z w : ℂ} (hz : InP P z) (hw : InP P w) : InP P (z + w) := by
  obtain ⟨h, hm⟩ := hz
  obtain ⟨h', hm'⟩ := hw
  exact ⟨h.add h', P.add_mem hm hm'⟩

theorem InP.neg {z : ℂ} (hz : InP P z) : InP P (-z) := by
  obtain ⟨h, hm⟩ := hz
  exact ⟨h.neg, P.neg_mem_iff.2 hm⟩

theorem InP.sub {z w : ℂ} (hz : InP P z) (hw : InP P w) : InP P (z - w) := by
  rw [sub_eq_add_neg]; exact hz.add hw.neg

theorem inP_mul [hP : P.IsPrime] {z w : ℂ} (hz : IsIntegral ℤ z) (hw : IsIntegral ℤ w)
    (h : InP P (z * w)) : InP P z ∨ InP P w := by
  obtain ⟨_, hm⟩ := h
  rcases hP.mem_or_mem (show (⟨z, hz⟩ : Aint) * ⟨w, hw⟩ ∈ P from hm) with h | h
  · exact Or.inl ⟨hz, h⟩
  · exact Or.inr ⟨hw, h⟩

theorem not_inP_one [hP : P.IsPrime] : ¬ InP P 1 := by
  rintro ⟨_, h⟩
  exact hP.ne_top ((Ideal.eq_top_iff_one P).2 h)

theorem inP_of_pow [P.IsPrime] {z : ℂ} (hz : IsIntegral ℤ z) {n : ℕ} (h : InP P (z ^ n)) :
    0 < n ∧ InP P z := by
  induction n with
  | zero => exact absurd (by simpa using h) not_inP_one
  | succ n ih =>
    refine ⟨n.succ_pos, ?_⟩
    rw [pow_succ] at h
    rcases inP_mul (hz.pow n) hz h with h' | h'
    · exact (ih h').2
    · exact h'

theorem InP.pow {z : ℂ} (hz : InP P z) {n : ℕ} (hn : 0 < n) : InP P (z ^ n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ]
  exact hz.mul_left (hz.isIntegral.pow k)

theorem not_inP_root [P.IsPrime] {u : ℂ} (hu : IsOfFinOrder u) : ¬ InP P u := by
  intro h
  have := h.mul_left ((isIntegral_of_finOrder hu).pow (orderOf u - 1))
  rw [← pow_succ, Nat.sub_add_cancel hu.orderOf_pos, pow_orderOf_eq_one] at this
  exact not_inP_one this

theorem inP_prod [P.IsPrime] {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, IsIntegral ℤ (f i)) (h : InP P (∏ i ∈ s, f i)) : ∃ i ∈ s, InP P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd (by simpa using h) not_inP_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h
    rcases inP_mul (hf a (Finset.mem_insert_self a s))
      (IsIntegral.prod _ fun i hi => hf i (Finset.mem_insert_of_mem hi)) h with h | h
    · exact ⟨a, Finset.mem_insert_self a s, h⟩
    · obtain ⟨i, hi, h⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) h
      exact ⟨i, Finset.mem_insert_of_mem hi, h⟩

theorem inP_prod_of_mem {ι : Type*} {s : Finset ι} (f : ι → ℂ)
    (hf : ∀ i ∈ s, IsIntegral ℤ (f i)) {a : ι} (ha : a ∈ s) (h : InP P (f a)) :
    InP P (∏ i ∈ s, f i) := by
  classical
  rw [← Finset.mul_prod_erase s f ha]
  exact h.mul_right (IsIntegral.prod _ fun i hi => hf i (Finset.mem_of_mem_erase hi))

/-- Two coprime integers cannot both lie in `P`. -/
theorem not_inP_coprime [P.IsPrime] {a b : ℕ} (hab : Nat.Coprime a b) (ha : InP P (a : ℂ))
    (hb : InP P (b : ℂ)) : False := by
  have hg := Nat.gcd_eq_gcd_ab a b
  rw [hab] at hg
  have h1 : InP P ((a : ℂ) * (Nat.gcdA a b : ℂ) + (b : ℂ) * (Nat.gcdB a b : ℂ)) :=
    (ha.mul_right (isIntegral_intCast _)).add (hb.mul_right (isIntegral_intCast _))
  have h2 : ((a : ℂ) * (Nat.gcdA a b : ℂ) + (b : ℂ) * (Nat.gcdB a b : ℂ)) = 1 := by
    exact_mod_cast hg.symm
  rw [h2] at h1
  exact not_inP_one h1

end InP

/-! ## 2. The residue lemma -/

theorem inP_pow_sub_one {P : Ideal Aint} {u : ℂ} (hu : IsIntegral ℤ u) (h : InP P (u - 1))
    (k : ℕ) : InP P (u ^ k - 1) := by
  have e : u ^ k - 1 = (∑ i ∈ Finset.range k, u ^ i) * (u - 1) := (geom_sum_mul u k).symm
  rw [e]
  exact h.mul_left (IsIntegral.sum _ fun i _ => hu.pow i)

/-- **Residue lemma.** If `p ∈ P` and `u - 1 ∈ P` for a root of unity `u`, then `ord u` is a
power of `p`. -/
theorem orderOf_eq_prime_pow_of_inP {P : Ideal Aint} [P.IsPrime] {p : ℕ} (hp : p.Prime)
    (hpP : InP P (p : ℂ)) {u : ℂ} (hu : IsOfFinOrder u) (h1 : InP P (u - 1)) :
    ∃ a, orderOf u = p ^ a := by
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hu.orderOf_pos.ne' ?_⟩
  intro ℓ hℓ hdvd
  by_contra hne
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hint := isIntegral_of_finOrder hu
  set v := u ^ (orderOf u / ℓ) with hv
  have hprim : IsPrimitiveRoot v ℓ :=
    (IsPrimitiveRoot.orderOf u).pow hu.orderOf_pos (Nat.div_mul_cancel hdvd).symm
  -- every primitive `ℓ`-th root `μ = v^j` has `μ - 1 ∈ P`
  have hμ : ∀ μ ∈ primitiveRoots ℓ ℂ, InP P (1 - μ) := by
    intro μ hμ
    have hμℓ : μ ^ ℓ = 1 := ((mem_primitiveRoots hℓ.pos).1 hμ).pow_eq_one
    obtain ⟨j, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hμℓ
    have := inP_pow_sub_one hint h1 (orderOf u / ℓ * j)
    rw [pow_mul] at this
    simpa using this.neg
  -- `ℓ = Φ_ℓ(1) = ∏ (1 - μ)`
  have hΦ : ((ℓ : ℕ) : ℂ) = ∏ μ ∈ primitiveRoots ℓ ℂ, (1 - μ) := by
    have h := Polynomial.eval_one_cyclotomic_prime (R := ℂ) (p := ℓ)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hprim, Polynomial.eval_prod] at h
    simpa using h.symm
  have hvmem : v ∈ primitiveRoots ℓ ℂ := (mem_primitiveRoots hℓ.pos).2 hprim
  have hℓP : InP P ((ℓ : ℕ) : ℂ) := by
    rw [hΦ]
    classical
    exact inP_prod_of_mem _ (fun μ hμ' => isIntegral_one.sub
      (isIntegral_of_finOrder (((mem_primitiveRoots hℓ.pos).1 hμ').isOfFinOrder hℓ.ne_zero)))
      hvmem (hμ v hvmem)
  exact not_inP_coprime ((Nat.coprime_primes hℓ hp).2 hne) hℓP hpP

/-! ## 3. Relations and the private prime -/

/-- A multiplicative relation: `∏_{r ∈ S} (1 - r/t)^(e_r)` is a root of unity. -/
def IsRelation (S : Finset ℂ) (e : ℂ → ℤ) : Prop :=
  ∃ ξ : ℂ, IsOfFinOrder ξ ∧ ∏ r ∈ S, (1 - r / tC) ^ (e r) = ξ

theorem norm_root {r : ℂ} (hr : IsOfFinOrder r) : ‖r‖ = 1 := by
  have h := (IsPrimitiveRoot.orderOf r).norm'_eq_one hr.orderOf_pos.ne'
  exact h

theorem tC_sub_root_ne_zero {r : ℂ} (hr : IsOfFinOrder r) : tC - r ≠ 0 :=
  tC_sub_ne_zero (norm_root hr)

/-- The cleared form `∏ (t - r)^(e⁺) · t^(N⁻) = ξ ∏ (t - r)^(e⁻) · t^(N⁺)`. -/
theorem cleared_of_relation {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ}
    (h : IsRelation S e) : ∃ ξ : ℂ, IsOfFinOrder ξ ∧
      (∏ r ∈ S, (tC - r) ^ (e r).toNat) * tC ^ (∑ r ∈ S, (-e r).toNat) =
        ξ * (∏ r ∈ S, (tC - r) ^ (-e r).toNat) * tC ^ (∑ r ∈ S, (e r).toNat) := by
  obtain ⟨ξ, hξ, hrel⟩ := h
  refine ⟨ξ, hξ, ?_⟩
  have hw : ∀ r ∈ S, (1 - r / tC) = (tC - r) / tC := fun r _ => by
    rw [sub_div, div_self tC_ne_zero]
  have hw0 : ∀ r ∈ S, (tC - r) / tC ≠ 0 := fun r hr =>
    div_ne_zero (tC_sub_root_ne_zero (hS r hr)) tC_ne_zero
  have hsplit : ∀ r ∈ S, ((tC - r) / tC) ^ (e r) =
      ((tC - r) / tC) ^ (e r).toNat / ((tC - r) / tC) ^ (-e r).toNat := by
    intro r hr
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (hw0 r hr), Int.toNat_sub_toNat_neg]
  rw [Finset.prod_congr rfl (fun r hr => by rw [hw r hr, hsplit r hr]),
    Finset.prod_div_distrib] at hrel
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum] at hrel
  have hP : ∏ r ∈ S, (tC - r) ^ (-e r).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r hr => pow_ne_zero _ (tC_sub_root_ne_zero (hS r hr))
  have ht : ∀ n : ℕ, tC ^ n ≠ 0 := fun n => pow_ne_zero n tC_ne_zero
  field_simp at hrel
  rw [div_eq_iff (ht _)] at hrel
  linear_combination hrel

theorem isIntegral_tC_sub {r : ℂ} (hr : IsOfFinOrder r) : IsIntegral ℤ (tC - r) :=
  isIntegral_tC.sub (isIntegral_of_finOrder hr)

/-- **The private prime.** If `t - r₀ ∈ P`, `t ∉ P` and `t - r ∉ P` for the other `r ∈ S`, then
`e_{r₀} = 0`. -/
theorem coeff_eq_zero_of_private_ideal {P : Ideal Aint} [P.IsPrime] {S : Finset ℂ}
    (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} (h : IsRelation S e) {r₀ : ℂ} (hr₀ : r₀ ∈ S)
    (ht : ¬ InP P tC) (h0 : InP P (tC - r₀)) (hpriv : ∀ r ∈ S, r ≠ r₀ → ¬ InP P (tC - r)) :
    e r₀ = 0 := by
  classical
  obtain ⟨ξ, hξ, hc⟩ := cleared_of_relation hS h
  have hint : ∀ r ∈ S, ∀ n : ℕ, IsIntegral ℤ ((tC - r) ^ n) :=
    fun r hr n => (isIntegral_tC_sub (hS r hr)).pow n
  have hprodI : ∀ f : ℂ → ℕ, IsIntegral ℤ (∏ r ∈ S, (tC - r) ^ f r) :=
    fun f => IsIntegral.prod _ fun r hr => hint r hr _
  -- the side containing `t - r₀` is in `P`; the other side is not
  have side : ∀ f g : ℂ → ℕ, 0 < f r₀ → g r₀ = 0 → ∀ a b : ℕ, ∀ c : ℂ, IsOfFinOrder c →
      (∏ r ∈ S, (tC - r) ^ f r) * tC ^ a = c * (∏ r ∈ S, (tC - r) ^ g r) * tC ^ b → False := by
    intro f g hf hg a b c hc heq
    have hL : InP P ((∏ r ∈ S, (tC - r) ^ f r) * tC ^ a) :=
      (inP_prod_of_mem _ (fun r hr => hint r hr _) hr₀ (h0.pow hf)).mul_right
        (isIntegral_tC.pow a)
    rw [heq] at hL
    rcases inP_mul ((isIntegral_of_finOrder hc).mul (hprodI g)) (isIntegral_tC.pow b) hL with
      hL | hL
    · rcases inP_mul (isIntegral_of_finOrder hc) (hprodI g) hL with hL | hL
      · exact not_inP_root hc hL
      · obtain ⟨r, hr, hL⟩ := inP_prod S _ (fun r hr => hint r hr _) hL
        obtain ⟨hpos, hL⟩ := inP_of_pow (isIntegral_tC_sub (hS r hr)) hL
        by_cases hrr : r = r₀
        · rw [hrr, hg] at hpos; exact lt_irrefl 0 hpos
        · exact hpriv r hr hrr hL
    · exact ht (inP_of_pow isIntegral_tC hL).2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1 : 0 < (-e r₀).toNat := by omega
    have h2 : (e r₀).toNat = 0 := by omega
    have hξ0 : ξ ≠ 0 := ne_zero_of_finOrder hξ
    refine side (fun r => (-e r).toNat) (fun r => (e r).toNat) h1 h2
      (∑ r ∈ S, (e r).toNat) (∑ r ∈ S, (-e r).toNat) ξ⁻¹ (isOfFinOrder_inv' hξ) ?_
    rw [mul_assoc ξ⁻¹, hc]
    field_simp
  · have h1 : 0 < (e r₀).toNat := by omega
    have h2 : (-e r₀).toNat = 0 := by omega
    exact side (fun r => (e r).toNat) (fun r => (-e r).toNat) h1 h2 _ _ ξ hξ hc

/-! ## 4. The set `R0` and its closure under `p'`-parts -/

/-- The 24 exponents `j` of `R0 = {ζ_120^j}`. -/
def R0Exps : Finset ℕ :=
  {0, 60, 30, 90, 20, 100, 15, 45, 75, 105, 12, 36, 84, 108, 10, 50, 18, 42, 66, 114, 5, 25, 65,
    85}

/-- `R0`: the exceptional roots and their `p'`-parts. -/
def R0 : Set ℂ := {z | ∃ j ∈ R0Exps, z = ζ120 ^ j}

theorem orderOf_ζ120_pow (k : ℕ) : orderOf (ζ120 ^ k) = 120 / Nat.gcd 120 k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [orderOf_pow' _ hk.ne', ← ζ120_prim.eq_orderOf]

set_option maxRecDepth 100000 in
/-- The finite check behind `R0_closed`. -/
theorem R0_closed_check : ∀ j ∈ R0Exps, ∀ k < 120, ∀ p ∈ ({3, 5} : Finset ℕ),
    ¬ p ∣ 120 / Nat.gcd 120 k → (∃ a < 8, 120 / Nat.gcd 120 ((j + 120 - k) % 120) = p ^ a) →
      k ∈ R0Exps := by decide +kernel

/-- **`R0` is closed under `p'`-parts** (`p` an odd prime): if `r' ∈ R0`, `p ∤ ord q` and
`ord (r'/q)` is a power of `p`, then `q ∈ R0`. -/
theorem R0_closed {r' : ℂ} (hr' : r' ∈ R0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q : ℂ}
    (hq : IsOfFinOrder q) (hpq : ¬ p ∣ orderOf q) {a : ℕ} (ha : orderOf (r' / q) = p ^ a) :
    q ∈ R0 := by
  obtain ⟨j, hj, rfl⟩ := hr'
  have hq0 : q ≠ 0 := ne_zero_of_finOrder hq
  set u := ζ120 ^ j / q with hu
  have hqu : ζ120 ^ j = q * u := by rw [hu]; field_simp
  have hcop : Nat.Coprime (orderOf q) (orderOf u) := by
    rw [ha]; exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq).symm
  have hord : orderOf (ζ120 ^ j) = orderOf q * p ^ a := by
    rw [hqu, (Commute.all q u).orderOf_mul_eq_mul_orderOf_of_coprime hcop, ha]
  have h120 : orderOf (ζ120 ^ j) ∣ 120 :=
    orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, ζ120_prim.pow_eq_one, one_pow])
  -- `q` is a 120th root of unity, `q = ζ^k`
  have hq120 : q ^ 120 = 1 := orderOf_dvd_iff_pow_eq_one.1
    ((Dvd.intro _ hord.symm).trans h120)
  obtain ⟨k, hk, rfl⟩ := ζ120_prim.eq_pow_of_pow_eq_one hq120
  have hpa : p ^ a ∣ 120 := (Dvd.intro_left _ hord.symm).trans h120
  -- `r'/q = ζ^((j + 120 - k) % 120)`
  have hjk : ζ120 ^ j / ζ120 ^ k = ζ120 ^ ((j + 120 - k) % 120) := by
    have hk0 : ζ120 ^ k ≠ 0 := pow_ne_zero _ (ζ120_prim.ne_zero (by norm_num))
    rw [div_eq_iff hk0, ← pow_add]
    have e : (j + 120 - k) % 120 + k = j + 120 * (1 - (j + 120 - k) / 120) := by
      have hj120 : j < 120 := by
        simp only [R0Exps, Finset.mem_insert, Finset.mem_singleton] at hj; omega
      omega
    rw [e, pow_add, pow_mul, ζ120_prim.pow_eq_one, one_pow, mul_one]
  by_cases hp120 : p ∣ 120
  · have hp35 : p ∈ ({3, 5} : Finset ℕ) := by
      have : p ∣ 2 ^ 3 * 3 * 5 := by norm_num; exact hp120
      rcases (Nat.Prime.dvd_mul hp).1 this with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
        · simp [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h]
      · simp [(Nat.prime_dvd_prime_iff_eq hp (by norm_num : (5 : ℕ).Prime)).1 h]
    have ha8 : a < 8 := by
      by_contra h8
      have : p ^ 8 ≤ p ^ a := Nat.pow_le_pow_right hp.pos (by omega)
      have := Nat.le_of_dvd (by norm_num) hpa
      have : 2 ^ 8 ≤ p ^ 8 := Nat.pow_le_pow_left hp.two_le 8
      omega
    refine ⟨k, R0_closed_check j hj k hk p hp35 ?_ ⟨a, ha8, ?_⟩, rfl⟩
    · rwa [← orderOf_ζ120_pow]
    · rw [← orderOf_ζ120_pow, ← hjk, ← ha]
  · -- `p ∤ 120`: then `a = 0`, `r'/q = 1`, `q = r'`
    have ha0 : a = 0 := by
      by_contra h0
      exact hp120 ((dvd_pow_self p h0).trans hpa)
    rw [ha0, pow_zero, orderOf_eq_one_iff] at ha
    have : ζ120 ^ k = ζ120 ^ j := by
      rw [div_eq_one_iff_eq (pow_ne_zero _ (ζ120_prim.ne_zero (by norm_num)))] at ha
      exact ha.symm
    exact ⟨j, hj, this⟩

/-! ## 5. The support theorem -/

/-- `r` has a good prime: a prime ideal containing `t - r` and an odd prime `p ∤ ord r`. -/
def HasGoodPrime (r : ℂ) : Prop :=
  ∃ P : Ideal Aint, P.IsPrime ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ orderOf r ∧
    InP P (p : ℂ) ∧ InP P (tC - r)

/-- Every root of unity outside `R0` has a good prime (milestone M4.2). -/
def GoodPrimes : Prop := ∀ r : ℂ, IsOfFinOrder r → r ∉ R0 → HasGoodPrime r

theorem tC_mul_conj : tC * (1 - I) = 2 := by
  unfold tC; linear_combination (-1 : ℂ) * Complex.I_sq

/-- **Step 2 (from `GoodPrimes`).** Every multiplicative relation is supported on `R0`. -/
theorem support_subset_R0 (hG : GoodPrimes) {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {e : ℂ → ℤ} (h : IsRelation S e) : ∀ r ∈ S, r ∉ R0 → e r = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  -- drop the zero exponents
  set S' := S.filter (fun r => e r ≠ 0) with hS'def
  have hS' : ∀ r ∈ S', IsOfFinOrder r := fun r hr => hS r (Finset.mem_filter.1 hr).1
  have h' : IsRelation S' e := by
    obtain ⟨ξ, hξ, hrel⟩ := h
    refine ⟨ξ, hξ, ?_⟩
    rw [hS'def, Finset.prod_filter_of_ne (p := fun r => e r ≠ 0)
      (fun r _ hr hc => hr (by simp [hc]))]
    exact hrel
  set T := S'.filter (fun r => r ∉ R0) with hTdef
  have hT : T.Nonempty := by
    obtain ⟨r, hr, hr0, hre⟩ := hcon
    exact ⟨r, by simp [hTdef, hS'def, hr, hr0, hre]⟩
  obtain ⟨r, hrT, hmax⟩ := Finset.exists_max_image T orderOf hT
  have hrS' : r ∈ S' := (Finset.mem_filter.1 hrT).1
  have hrR0 : r ∉ R0 := (Finset.mem_filter.1 hrT).2
  have her : e r ≠ 0 := (Finset.mem_filter.1 hrS').2
  have hr := hS' r hrS'
  obtain ⟨P, hP, p, hp, hp2, hpr, hpP, htr⟩ := hG r hr hrR0
  -- `t ∉ P`: else `2 = t (1 - i) ∈ P`, and `p ∈ P` is odd
  have ht : ¬ InP P tC := by
    intro ht
    have h2 := ht.mul_right (isIntegral_one.sub (isIntegral_of_finOrder isOfFinOrder_I))
    rw [tC_mul_conj] at h2
    exact not_inP_coprime (a := 2) (b := p)
      ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)) (by exact_mod_cast h2) hpP
  refine her (coeff_eq_zero_of_private_ideal hS' h' hrS' ht htr ?_)
  -- the prime is private to `r`
  intro r' hr' hne htr'
  have hr'f := hS' r' hr'
  have hr0 : r ≠ 0 := ne_zero_of_finOrder hr
  set u := r' / r with hu
  have hufin : IsOfFinOrder u := isOfFinOrder_div' hr'f hr
  have hu1 : InP P (u - 1) := by
    have hd : InP P (r' - r) := by
      have := htr.sub htr'
      rwa [show tC - r - (tC - r') = r' - r by ring] at this
    have hrinv : IsIntegral ℤ r⁻¹ := isIntegral_of_finOrder (isOfFinOrder_inv' hr)
    have := hd.mul_right hrinv
    rwa [show (r' - r) * r⁻¹ = u - 1 by rw [hu]; field_simp] at this
  obtain ⟨a, hord⟩ := orderOf_eq_prime_pow_of_inP hp hpP hufin hu1
  have ha : 0 < a := by
    by_contra h0
    push Not at h0
    rw [Nat.le_zero.1 h0, pow_zero, orderOf_eq_one_iff, hu, div_eq_one_iff_eq hr0] at hord
    exact hne hord
  have hcop : Nat.Coprime (orderOf r) (orderOf u) := by
    rw [hord]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpr).symm
  have hr'eq : r' = r * u := by rw [hu]; field_simp
  have hordr' : orderOf r' = orderOf r * p ^ a := by
    rw [hr'eq, (Commute.all r u).orderOf_mul_eq_mul_orderOf_of_coprime hcop, hord]
  by_cases hr'R0 : r' ∈ R0
  · -- `r` is the `p'`-part of `r'`
    exact hrR0 (R0_closed hr'R0 hp hp2 hr hpr (a := a) (by rw [← hu, hord]))
  · -- `r'` would have larger order
    have hle := hmax r' (Finset.mem_filter.2 ⟨hr', hr'R0⟩)
    rw [hordr'] at hle
    have : orderOf r * 1 < orderOf r * p ^ a :=
      Nat.mul_lt_mul_of_pos_left (Nat.one_lt_pow ha.ne' hp.one_lt) hr.orderOf_pos
    omega

end PiFormula
