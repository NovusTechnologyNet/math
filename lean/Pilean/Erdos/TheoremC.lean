module

public import Pilean.Erdos.Defs
public import Pilean.Erdos.AbstractGroupRing
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Theorem C of the Erdős `±1` programme, from Theorems A and B

`theoremC_of : TheoremA → TheoremB → TheoremC`. For a prime `p ∣ q`, Theorem A gives
`ℓ_p ≡ (p-1) v_p(q)` and Theorem B gives `ℓ_p ≡ 0` modulo `2^(s+1) ℤ_(2)`, `s = v_2(p-1)`.
So `(p-1) v_p(q) ∈ 2^(s+1) ℤ_(2)`; as `2^s` is the exact power of `2` in `p - 1`, `v_p(q)` is
even (`thmC_even_of_eq`). All exponents even means that `q` is a square.

The paper proof is section 0 of `research/2026-11-23-erdos-pm1/02_proof_part_II.md`.
-/

@[expose] public section

namespace PiFormula

namespace Erdos

/-- If `n ≠ 0` and `n k ∈ 2^(v_2(n)+1) ℤ_(2)`, then `k` is even. -/
theorem thmC_even_of_eq {n k : ℕ} (hn : n ≠ 0) {z : ℚ} (hz : IsZ2 z)
    (h : (n : ℚ) * (k : ℚ) = 2 ^ (padicValNat 2 n + 1) * z) : Even k := by
  rw [Nat.padicValNat_def] at h
  have hdvd : 2 ^ multiplicity 2 n ∣ n := pow_multiplicity_dvd 2 n
  have hndvd : ¬ 2 ^ (multiplicity 2 n + 1) ∣ n := pow_succ_multiplicity_not_dvd hn
  generalize multiplicity 2 n = s at h hdvd hndvd
  obtain ⟨m, rfl⟩ := hdvd
  have hmodd : ¬ Even m := by
    rintro ⟨t, rfl⟩
    exact hndvd ⟨t, by ring⟩
  have h2s : (2 : ℚ) ^ s ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2 : (m : ℚ) * (k : ℚ) = 2 * z := by
    apply mul_left_cancel₀ h2s
    push_cast at h
    linear_combination h
  have h3 : (m : ℚ) * (k : ℚ) * (z.den : ℚ) = 2 * (z.num : ℚ) := by
    rw [h2, mul_assoc, Rat.mul_den_eq_num]
  have h4 : (m : ℤ) * (k : ℤ) * (z.den : ℤ) = 2 * z.num := by exact_mod_cast h3
  have h5 : Even ((m : ℤ) * (k : ℤ) * (z.den : ℤ)) := ⟨z.num, by rw [h4]; ring⟩
  rw [Int.even_mul, Int.even_mul, Int.even_natCast, Int.even_natCast, Int.even_natCast] at h5
  rcases h5 with (h | h) | h
  · exact absurd h hmodd
  · exact h
  · exact absurd h (Nat.not_even_iff_odd.mpr hz)

/-- **Theorem C from Theorems A and B**: (a) and (b) with odd values force `q` to be a perfect
square. -/
theorem theoremC_of (hA : TheoremA) (hB : TheoremB) : TheoremC := by
  intro q hq f h0 hodd ha hb
  rw [Nat.isSquare_iff_even_factorization]
  intro p hp
  rw [Nat.factorization_def q hp]
  by_cases hpq : p ∣ q
  · obtain ⟨z1, hz1, e1⟩ := hA q hq f h0 hodd ha p hp hpq
    obtain ⟨z2, hz2, e2⟩ := hB q hq f h0 hodd p hp hpq (hb p hp hpq)
    have hp1 : p - 1 ≠ 0 := by
      have := hp.two_le
      omega
    have hz : IsZ2 (z2 + -z1) := Abs.isZ2_add hz2 (Abs.isZ2_neg hz1)
    rw [← Nat.padicValNat_def]
    refine thmC_even_of_eq hp1 hz ?_
    rw [Nat.cast_pred hp.pos]
    linear_combination e2 - e1
  · rw [multiplicity_eq_zero_of_not_dvd hpq]
    exact Even.zero

end Erdos

end PiFormula
