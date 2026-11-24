/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.TheoremBAux

/-!
# Theorem B of the Erdős `±1` programme

`theoremB : TheoremB`: let `q` be odd, `f : ℤ/q → ℚ` with `f(0) = 0` and every other value a
rational number with odd numerator and odd denominator, and `p` a prime dividing `q` with
`c_p = 0`. Then `ℓ_p ∈ 2^(v_2(p-1)+1) ℤ_(2)`.

The proof is section 2 of `research/2026-11-23-erdos-pm1/02_proof_part_II.md`. With
`k = v_p(q)`, `P = p - 1 = 2^s m` (`s ≥ 1`) and `N = {1 ≤ r ≤ q : p^k ∤ r}`:

* `c_p = ℓ_p (k + 1/P) + ∑_{r ∈ N} f(r) v_p(r)` (`thmB_okadaC_eq`; the term `r = q` is `0`);
* `∑_{r ∈ N} f(r) v_p(r) = T + 2 E` with `E ∈ ℤ_(2)` and `T = ∑_{r ∈ N} v_p(r)`
  (`thmB_sum_split`; `f(r) ≡ 1` modulo `2`);
* `T = P T'` for a natural number `T'` (`thmB_sum_val_dvd`, the count);
* so `ℓ_p (P k + 1) = -(P² T' + 2 P E) = 2^(s+1) · (-(2^(s-1) m² T' + m E))`, and `P k + 1` is
  an odd natural number, a unit of `ℤ_(2)`.
-/

@[expose] public section

open Finset

namespace PiFormula

namespace Erdos

/-- If the values of `f` off `0` are odd and `p^k ∣ q`, then
`∑_{1 ≤ r ≤ q, p^k ∤ r} f(r) v_p(r) = ∑_{1 ≤ r ≤ q, p^k ∤ r} v_p(r) + 2 E` with `E ∈ ℤ_(2)`. -/
theorem thmB_sum_split {q : ℕ} (f : ZMod q → ℚ)
    (hodd : ∀ r : ZMod q, r ≠ 0 → IsOddRat (f r)) (p k : ℕ) (hk : p ^ k ∣ q) :
    ∃ E : ℚ, IsZ2 E ∧
      ∑ r ∈ (Icc 1 q).filter (fun r => ¬ p ^ k ∣ r), f (r : ZMod q) * (padicValNat p r : ℚ)
        = ((∑ r ∈ (Icc 1 q).filter (fun r => ¬ p ^ k ∣ r), padicValNat p r : ℕ) : ℚ)
          + 2 * E := by
  refine ⟨∑ r ∈ (Icc 1 q).filter (fun r => ¬ p ^ k ∣ r),
    (f (r : ZMod q) - 1) / 2 * (padicValNat p r : ℚ), ?_, ?_⟩
  · apply Abs.isZ2_sum
    intro r hr
    rw [mem_filter] at hr
    have hr0 : (r : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => hr.2 (hk.trans h)
    exact Abs.isZ2_mul (thmB_isZ2_half_sub_one (hodd _ hr0)) (thmB_isZ2_natCast _)
  · rw [Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring

/-- **Theorem B**: `c_p = 0` with odd values gives `ℓ_p ≡ 0` modulo `2^(v_2(p-1)+1) ℤ_(2)`. -/
theorem theoremB : TheoremB := by
  intro q hq f h0 hodd p hp hpq hc
  have hpk : p ^ padicValNat p q ∣ q := by
    rw [Nat.padicValNat_def]
    exact pow_multiplicity_dvd p q
  -- `p - 1 = 2^(s'+1) m` with `s' + 1 = v_2(p - 1)`
  have hpodd : Odd p := hq.of_dvd_nat hpq
  have hp1 : p - 1 ≠ 0 := by
    have := hp.two_le
    omega
  have h2 : 2 ∣ p - 1 := by
    obtain ⟨t, ht⟩ := hpodd
    exact ⟨t, by omega⟩
  have hs1 : 1 ≤ padicValNat 2 (p - 1) := by
    rw [Nat.padicValNat_def, ← Nat.pow_dvd_iff_le_multiplicity (by norm_num) hp1, pow_one]
    exact h2
  obtain ⟨s', hs'⟩ : ∃ s', padicValNat 2 (p - 1) = s' + 1 :=
    ⟨padicValNat 2 (p - 1) - 1, by omega⟩
  obtain ⟨m, hm⟩ : 2 ^ (s' + 1) ∣ p - 1 := by
    rw [← hs', Nat.padicValNat_def]
    exact pow_multiplicity_dvd 2 (p - 1)
  -- the count, and the values modulo `2`
  obtain ⟨T', hT'⟩ := thmB_sum_val_dvd hp (padicValNat p q) hpk
  obtain ⟨E, hE, hsum⟩ := thmB_sum_split f hodd p (padicValNat p q) hpk
  have hc' := thmB_okadaC_eq f h0 hp
  have hP : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := Nat.cast_pred hp.pos
  rw [hc, hsum, hT', Nat.cast_mul, hP] at hc'
  have hPm : (p : ℚ) - 1 = 2 ^ (s' + 1) * (m : ℚ) := by
    rw [← hP, hm]
    push_cast
    ring
  have hP0 : (p : ℚ) - 1 ≠ 0 := by
    rw [← hP]
    exact_mod_cast hp1
  -- multiply `c_p = 0` by `p - 1`
  have hinv : 1 / ((p : ℚ) - 1) * ((p : ℚ) - 1) = 1 := one_div_mul_cancel hP0
  have h1 : ell q f p * (((p : ℚ) - 1) * (padicValNat p q : ℚ) + 1)
      + ((p : ℚ) - 1) * (((p : ℚ) - 1) * (T' : ℚ) + 2 * E) = 0 := by
    linear_combination (-((p : ℚ) - 1)) * hc' - ell q f p * hinv
  -- the unit `(p - 1) k + 1`
  have hU : Odd ((p - 1) * padicValNat p q + 1) :=
    ((even_iff_two_dvd.mpr h2).mul_right _).add_one
  have hUc : (((p - 1) * padicValNat p q + 1 : ℕ) : ℚ)
      = ((p : ℚ) - 1) * (padicValNat p q : ℚ) + 1 := by
    rw [Nat.cast_add, Nat.cast_mul, hP, Nat.cast_one]
  have hU0 : ((p : ℚ) - 1) * (padicValNat p q : ℚ) + 1 ≠ 0 := by
    rw [← hUc]
    exact_mod_cast hU.pos.ne'
  refine ⟨-(((2 ^ s' * m ^ 2 * T' : ℕ) : ℚ) + (m : ℚ) * E)
    * (((p - 1) * padicValNat p q + 1 : ℕ) : ℚ)⁻¹, ?_, ?_⟩
  · exact Abs.isZ2_mul (Abs.isZ2_neg (Abs.isZ2_add (thmB_isZ2_natCast _)
      (Abs.isZ2_mul (thmB_isZ2_natCast _) hE))) (thmB_isZ2_inv_of_odd hU)
  · rw [hs', hUc]
    have h3 : ell q f p * (((p : ℚ) - 1) * (padicValNat p q : ℚ) + 1)
        = 2 ^ (s' + 1 + 1) * -(((2 ^ s' * m ^ 2 * T' : ℕ) : ℚ) + (m : ℚ) * E) := by
      push_cast
      linear_combination h1
        - ((((p : ℚ) - 1) + 2 ^ (s' + 1) * (m : ℚ)) * (T' : ℚ) + 2 * E) * hPm
    calc ell q f p
        = ell q f p * (((p : ℚ) - 1) * (padicValNat p q : ℚ) + 1)
          * (((p : ℚ) - 1) * (padicValNat p q : ℚ) + 1)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hU0, mul_one]
      _ = _ := by rw [h3, mul_assoc]

end Erdos

end PiFormula
