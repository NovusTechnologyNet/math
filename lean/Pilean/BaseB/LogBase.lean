import Pilean.BaseB.NoPi
import Pilean.BaseB.SubseriesLog
import Pilean.BaseB.LogNonValue
import Pilean.BaseB.LogSelf

/-!
# The logarithm of the base

**Theorem** (`bailey_log_self_iff`). For an integer `b ≥ 2`, the number `log b` has a degree-1
BBP-type formula of base `b`,

  `log b = ∑_{j ≥ 0} b^(-B j) ∑_{i=1}^{N} c_i / (N j + i)`,   `c_i` rational,

if and only if `b` is a power of 2 or a power of 3.

More generally (`no_log_bailey`): if `b` is neither a power of 2 nor a power of 3 and `y ≠ 1`
is a positive rational all of whose prime factors divide `b`, then no such series equals
`q π + q' log y` with `q, q'` rational, `q' ≠ 0`. For example `log 2`, `log 5` and `log 10`
have no degree-1 BBP-type formula of base 10.

The proof: the base is `a^j` with `a ≥ 5` not a perfect power; the series is a series of some
step `n` in base `a` (`BaileyForm`); its sub-series over the multiples of `n/2` (or `n`) has
the same value (`SubseriesLog`, `Kummer`); that sub-series is a series of the class `F_a`
(`Reindex`); and in `F_a` the number `q π + q' log y` is not a value (`LogNonValue`).
The formulas for the powers of 2 and 3 are in `LogSelf`.

Baker's theorem is used through the imported proof; there is no hypothesis.
-/

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-- **Every step.** Let `b ≥ 5` be an integer that is not a perfect power and `y ≠ 1` a positive
rational all of whose prime factors divide `b`. No series `∑ ρ(k) b^(-⌊k/n⌋)/k` with `ρ`
rational and periodic equals `q π + q' log y` with `q, q'` rational, `q' ≠ 0`. -/
theorem no_log_step {b n : ℕ} (hb : 5 ≤ b) (hpp : NotPerfectPower b) (hn : 0 < n) {N : ℕ}
    (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {q q' : ℚ} (hq' : q' ≠ 0) {y : ℚ}
    (hy : 0 < y) (hy1 : y ≠ 1) (hp : ∀ p : ℕ, p.Prime → padicValRat p y ≠ 0 → p ∣ b) :
    ¬ HasSum (seriesTermBN b n ρ) (q * Real.pi + q' * Real.log y) := by
  intro h
  have hb2 : 2 ≤ b := by omega
  have hb9 : b ≠ 9 := fun h9 => hpp 3 2 le_rfl (by rw [h9]; norm_num)
  have hsub := subseries_log_of_kummerHom bakerTheorem hb2 hn (kummerHom hb2 hpp hn) hN hρ hy h
  exact not_isFBValue_mul_pi_add_log bakerTheorem hb hb9 hq' hy hy1 hp
    (isFBValue_of_hasSum_subseries hb2 hn hN hρ hsub)

/-- **Logarithms of numbers built from the primes of the base.** Let `b ≥ 2` be an integer
that is neither a power of 2 nor a power of 3, and `y ≠ 1` a positive rational all of whose
prime factors divide `b`. No series `∑_j b^(-B j) ∑_{i=1}^{N} c_i / (N j + i)` with rational
`c_i` equals `q π + q' log y` with `q, q'` rational, `q' ≠ 0`. -/
theorem no_log_bailey {b B N : ℕ} (hb : 2 ≤ b) (h2 : ∀ k : ℕ, b ≠ 2 ^ k) (h3 : ∀ k : ℕ, b ≠ 3 ^ k)
    (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) {q q' : ℚ} (hq' : q' ≠ 0) {y : ℚ} (hy : 0 < y)
    (hy1 : y ≠ 1) (hp : ∀ p : ℕ, p.Prime → padicValRat p y ≠ 0 → p ∣ b) :
    ¬ HasSum (baileyBlock b B N c) (q * Real.pi + q' * Real.log y) := by
  intro h
  obtain ⟨a, j, ha, hj, hpp, rfl⟩ := exists_root_notPerfectPower hb
  have ha5 : 5 ≤ a := by
    have h2' : a ≠ 2 := fun h => h2 j (by rw [h])
    have h3' : a ≠ 3 := fun h => h3 j (by rw [h])
    have h4 : a ≠ 4 := fun h => hpp 2 2 le_rfl (by rw [h]; norm_num)
    omega
  rw [baileyBlock_pow] at h
  obtain ⟨P, ρ, hP, hρ, hs⟩ := exists_step_of_bailey ha (Nat.mul_pos hj hB) hN c h
  have hn : 0 < N / Nat.gcd (j * B) N :=
    Nat.div_pos (Nat.le_of_dvd hN (Nat.gcd_dvd_right _ _)) (Nat.gcd_pos_of_pos_right _ hN)
  exact no_log_step ha5 hpp hn hP hρ hq' hy hy1
    (fun p hpr hv => hpr.dvd_of_dvd_pow (hp p hpr hv)) hs

/-- The prime factors of the rational number `b` divide `b`. -/
theorem dvd_of_padicValRat_natCast_ne_zero {b p : ℕ} (h : padicValRat p (b : ℚ) ≠ 0) : p ∣ b := by
  by_contra hnd
  apply h
  rw [padicValRat.of_nat, multiplicity_eq_zero_of_not_dvd hnd, Nat.cast_zero]

/-- **The logarithm of the base.** If `b ≥ 2` is neither a power of 2 nor a power of 3, no
series `∑_j b^(-B j) ∑_{i=1}^{N} c_i / (N j + i)` with rational `c_i` equals `log b`. -/
theorem no_log_self_bailey {b B N : ℕ} (hb : 2 ≤ b) (h2 : ∀ k : ℕ, b ≠ 2 ^ k)
    (h3 : ∀ k : ℕ, b ≠ 3 ^ k) (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) :
    ¬ HasSum (baileyBlock b B N c) (Real.log (b : ℝ)) := by
  intro h
  have hy : (0 : ℚ) < (b : ℚ) := by exact_mod_cast (by omega : 0 < b)
  have hy1 : (b : ℚ) ≠ 1 := by exact_mod_cast (by omega : b ≠ 1)
  refine no_log_bailey hb h2 h3 hB hN c (q := 0) (q' := 1) one_ne_zero hy hy1
    (fun p _ hv => dvd_of_padicValRat_natCast_ne_zero hv) ?_
  have e : ((0 : ℚ) : ℝ) * Real.pi + ((1 : ℚ) : ℝ) * Real.log (((b : ℚ) : ℝ)) =
      Real.log (b : ℝ) := by
    push_cast
    ring
  rw [e]
  exact h

/-- **`log b` has a degree-1 BBP-type formula of base `b` exactly when `b` is a power of 2 or
a power of 3.** -/
theorem bailey_log_self_iff {b : ℕ} (hb : 2 ≤ b) :
    (∃ (B N : ℕ) (c : Fin N → ℚ), 0 < B ∧ 0 < N ∧
      HasSum (baileyBlock b B N c) (Real.log (b : ℝ))) ↔
      (∃ e : ℕ, b = 2 ^ e) ∨ ∃ e : ℕ, b = 3 ^ e := by
  constructor
  · rintro ⟨B, N, c, hB, hN, h⟩
    by_contra hne
    push Not at hne
    exact no_log_self_bailey hb (fun k hk => hne.1 k hk) (fun k hk => hne.2 k hk) hB hN c h
  · rintro (⟨e, rfl⟩ | ⟨e, rfl⟩)
    · have he : 0 < e := by
        rcases Nat.eq_zero_or_pos e with h0 | h0
        · rw [h0] at hb
          norm_num at hb
        · exact h0
      exact exists_bailey_log_two_pow he
    · have he : 0 < e := by
        rcases Nat.eq_zero_or_pos e with h0 | h0
        · rw [h0] at hb
          norm_num at hb
        · exact h0
      exact exists_bailey_log_three_pow he

/-- **Base 10.** None of `log 2`, `log 5`, `log 10` has a degree-1 BBP-type formula of base
10. -/
theorem no_log_bailey_ten {B N : ℕ} (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) :
    ¬ HasSum (baileyBlock 10 B N c) (Real.log 2) ∧
      ¬ HasSum (baileyBlock 10 B N c) (Real.log 5) ∧
      ¬ HasSum (baileyBlock 10 B N c) (Real.log 10) := by
  have h2 : ∀ k : ℕ, (10 : ℕ) ≠ 2 ^ k := fun k hk => by
    have h5 : (5 : ℕ) ∣ 2 ^ k := hk ▸ (by norm_num : (5 : ℕ) ∣ 10)
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5
    omega
  have h3 : ∀ k : ℕ, (10 : ℕ) ≠ 3 ^ k := fun k hk => by
    have h5 : (5 : ℕ) ∣ 3 ^ k := hk ▸ (by norm_num : (5 : ℕ) ∣ 10)
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5
    omega
  have key : ∀ m : ℕ, 2 ≤ m → m ∣ 10 → ¬ HasSum (baileyBlock 10 B N c) (Real.log (m : ℝ)) := by
    intro m hm hdvd h
    have hy : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
    have hy1 : (m : ℚ) ≠ 1 := by exact_mod_cast (by omega : m ≠ 1)
    refine no_log_bailey (by norm_num) h2 h3 hB hN c (q := 0) (q' := 1) one_ne_zero hy hy1
      (fun p _ hv => (dvd_of_padicValRat_natCast_ne_zero hv).trans hdvd) ?_
    have e : ((0 : ℚ) : ℝ) * Real.pi + ((1 : ℚ) : ℝ) * Real.log (((m : ℚ) : ℝ)) =
        Real.log (m : ℝ) := by
      push_cast
      ring
    rw [e]
    exact h
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast key 2 (by norm_num) (by norm_num)
  · exact_mod_cast key 5 (by norm_num) (by norm_num)
  · exact_mod_cast key 10 (by norm_num) (by norm_num)

end BaseB

end PiFormula
