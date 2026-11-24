/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.Defs
public import Pilean.Erdos.AbstractGroupRing
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Theorem B of the Erdős `±1` programme: the lemmas

Helper lemmas for `theoremB` (`Pilean/Erdos/TheoremB.lean`) and `theoremC_of`
(`Pilean/Erdos/TheoremC.lean`). The paper proof is section 2 of
`research/2026-11-23-erdos-pm1/02_proof_part_II.md`.

* `thmB_isZ2_natCast`, `thmB_isZ2_inv_of_odd`, `thmB_isZ2_half_sub_one`: three facts about
  `ℤ_(2)`; the last one says that an odd rational number is `≡ 1` modulo `2 ℤ_(2)`.
* `thmB_sum_val_dvd`: if `p` is prime and `p^k ∣ q`, then the sum of `v_p(r)` over the
  `1 ≤ r ≤ q` with `p^k ∤ r` is a multiple of `p - 1` (the count of the paper).
* `thmB_okadaC_eq`: `c_p = ℓ_p (k + 1/(p-1)) + ∑_{p^k ∤ r} f(r) v_p(r)` when `f(0) = 0`.
-/

@[expose] public section

open Finset

namespace PiFormula

namespace Erdos

/-! ### Three facts about `ℤ_(2)` -/

theorem thmB_isZ2_natCast (n : ℕ) : IsZ2 (n : ℚ) := by simp [IsZ2]

/-- The inverse of an odd natural number lies in `ℤ_(2)`. -/
theorem thmB_isZ2_inv_of_odd {n : ℕ} (hn : Odd n) : IsZ2 ((n : ℚ)⁻¹) := by
  unfold IsZ2
  rw [Rat.inv_natCast_den_of_pos hn.pos]
  exact hn

/-- An odd rational number is `1 + 2 e` with `e ∈ ℤ_(2)`. -/
theorem thmB_isZ2_half_sub_one {x : ℚ} (hx : IsOddRat x) : IsZ2 ((x - 1) / 2) := by
  obtain ⟨hn, hd⟩ := hx
  have hdZ : Odd (x.den : ℤ) := by exact_mod_cast hd
  obtain ⟨t, ht⟩ := Odd.sub_odd hn hdZ
  have hd0 : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have ht' : (x.num : ℚ) - (x.den : ℚ) = (t : ℚ) + (t : ℚ) := by exact_mod_cast ht
  have hxe : (x - 1) / 2 = (t : ℚ) * (x.den : ℚ)⁻¹ := by
    have hnum : x * (x.den : ℚ) = (x.num : ℚ) := Rat.mul_den_eq_num x
    apply mul_right_cancel₀ hd0
    rw [mul_assoc, inv_mul_cancel₀ hd0, mul_one]
    linear_combination (1 / 2 : ℚ) * hnum + (1 / 2 : ℚ) * ht'
  rw [hxe]
  exact Abs.isZ2_mul (Abs.isZ2_intCast t) (thmB_isZ2_inv_of_odd hd)

/-! ### The count -/

/-- Exactly `n / d` of the numbers `1, …, n` are multiples of `d`. -/
theorem thmB_card_dvd (n d : ℕ) : #{r ∈ Icc 1 n | d ∣ r} = n / d := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div n d, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

/-- For `j ≤ k` and `p^k ∣ q`, the number of `1 ≤ r ≤ q` with `p^j ∣ r` and `p^k ∤ r` is a
multiple of `p - 1`. -/
theorem thmB_card_layer {p k j q : ℕ} (hp : 1 ≤ p) (hjk : j ≤ k) (hq : p ^ k ∣ q) :
    p - 1 ∣ #{r ∈ (Icc 1 q).filter (fun r => ¬ p ^ k ∣ r) | p ^ j ∣ r} := by
  obtain ⟨m, rfl⟩ := hq
  have hpk : 0 < p ^ k := Nat.pow_pos hp
  have hpj : 0 < p ^ j := Nat.pow_pos hp
  have h1 : #{r ∈ Icc 1 (p ^ k * m) | p ^ j ∣ r} = p ^ (k - j) * m := by
    rw [thmB_card_dvd]
    have e : p ^ k * m = p ^ j * (p ^ (k - j) * m) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hjk]
    rw [e, Nat.mul_div_cancel_left _ hpj]
  have h2 : #{r ∈ Icc 1 (p ^ k * m) | p ^ k ∣ r} = m := by
    rw [thmB_card_dvd, Nat.mul_div_cancel_left _ hpk]
  have h3 := Finset.card_filter_add_card_filter_not
    (s := {r ∈ Icc 1 (p ^ k * m) | p ^ j ∣ r}) (fun r => p ^ k ∣ r)
  have h4 : {r ∈ {r ∈ Icc 1 (p ^ k * m) | p ^ j ∣ r} | p ^ k ∣ r}
      = {r ∈ Icc 1 (p ^ k * m) | p ^ k ∣ r} := by
    ext r
    simp only [mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, (pow_dvd_pow p hjk).trans h.2⟩, h.2⟩⟩
  rw [h4, h2, h1, Finset.filter_comm] at h3
  obtain ⟨c, hc⟩ := Nat.sub_one_dvd_pow_sub_one p (k - j)
  have hpos : 0 < p ^ (k - j) := Nat.pow_pos hp
  have e : p ^ (k - j) = (p - 1) * c + 1 := by omega
  rw [e] at h3
  refine ⟨c * m, ?_⟩
  have e2 : ((p - 1) * c + 1) * m = (p - 1) * (c * m) + m := by ring
  omega

/-- If `p` is prime and `p^k ∣ q`, the sum of `v_p(r)` over the `1 ≤ r ≤ q` with `p^k ∤ r` is
a multiple of `p - 1`. -/
theorem thmB_sum_val_dvd {p q : ℕ} (hp : p.Prime) (k : ℕ) (hq : p ^ k ∣ q) :
    p - 1 ∣ ∑ r ∈ (Icc 1 q).filter (fun r => ¬ p ^ k ∣ r), padicValNat p r := by
  have key : ∀ r ∈ (Icc 1 q).filter (fun r => ¬ p ^ k ∣ r),
      padicValNat p r = ∑ j ∈ Ico 1 k, if p ^ j ∣ r then 1 else 0 := by
    intro r hr
    rw [mem_filter, mem_Icc] at hr
    obtain ⟨⟨hr1, -⟩, hrk⟩ := hr
    have hr0 : r ≠ 0 := by omega
    rw [Nat.pow_dvd_iff_le_multiplicity hp.ne_one hr0, not_le] at hrk
    rw [Nat.padicValNat_def, ← Finset.card_filter]
    have hset : (Ico 1 k).filter (fun j => p ^ j ∣ r) = Ico 1 (multiplicity p r + 1) := by
      ext j
      rw [mem_filter, mem_Ico, mem_Ico, Nat.pow_dvd_iff_le_multiplicity hp.ne_one hr0]
      omega
    rw [hset, Nat.card_Ico]
    omega
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  apply Finset.dvd_sum
  intro j hj
  rw [← Finset.card_filter]
  exact thmB_card_layer hp.one_le (mem_Ico.mp hj).2.le hq

/-! ### The number `c_p` -/

/-- With `k = v_p(q)`: `c_p = ℓ_p (k + 1/(p-1)) + ∑_{1 ≤ r ≤ q, p^k ∤ r} f(r) v_p(r)`, when
`f(0) = 0`. -/
theorem thmB_okadaC_eq {q : ℕ} (f : ZMod q → ℚ) (h0 : f 0 = 0) {p : ℕ} (hp : p.Prime) :
    okadaC q f p = ell q f p * ((padicValNat p q : ℚ) + 1 / ((p : ℚ) - 1)) +
      ∑ r ∈ (Icc 1 q).filter (fun r => ¬ p ^ padicValNat p q ∣ r),
        f (r : ZMod q) * (padicValNat p r : ℚ) := by
  unfold okadaC
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 q) (fun r => p ^ padicValNat p q ∣ r)]
  congr 1
  · have h1 : ∀ r ∈ (Icc 1 q).filter (fun r => p ^ padicValNat p q ∣ r),
        f (r : ZMod q) * lam q r p
          = f (r : ZMod q) * ((padicValNat p q : ℚ) + 1 / ((p : ℚ) - 1)) := by
      intro r hr
      rw [mem_filter, mem_Icc] at hr
      have hlt : ¬ padicValNat p r < padicValNat p q := by
        rw [not_lt, Nat.padicValNat_def (n := r),
          ← Nat.pow_dvd_iff_le_multiplicity hp.ne_one (by omega)]
        exact hr.2
      rw [lam, ite_eq_right hlt]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
    congr 1
    unfold ell
    symm
    apply Finset.sum_subset
    · intro r hr
      rw [mem_filter, mem_Icc] at hr ⊢
      exact ⟨⟨hr.1.1, by omega⟩, hr.2⟩
    · intro r hr hr'
      rw [mem_filter, mem_Icc] at hr
      rw [mem_filter, mem_Icc] at hr'
      have hrq : r = q := by
        by_contra hne
        exact hr' ⟨⟨hr.1.1, by omega⟩, hr.2⟩
      rw [hrq, ZMod.natCast_self, h0]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [mem_filter, mem_Icc] at hr
    have hlt : padicValNat p r < padicValNat p q := by
      rw [← not_le, Nat.padicValNat_def (n := r),
        ← Nat.pow_dvd_iff_le_multiplicity hp.ne_one (by omega)]
      exact hr.2
    rw [lam, ite_eq_left hlt]

end Erdos

end PiFormula
