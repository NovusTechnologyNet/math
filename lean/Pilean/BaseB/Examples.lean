import Pilean.BaseB.LogBase

/-!
# Named cases: base 26 and base 36

The bases of the alphabet (26 letters) and of letters with digits (36 symbols). Neither is a
power of 2, so by `no_pi_bailey` there is no degree-1 BBP-type formula for `π` in these bases;
neither is a power of 2 or of 3, so by `no_log_self_bailey` the logarithm of the base has none
either. (Base 16, base 32 and base 64 are powers of 2 and do have formulas for `π`:
`bailey_pi_iff`.)
-/

namespace PiFormula

namespace BaseB

theorem twentySix_ne_two_pow (k : ℕ) : (26 : ℕ) ≠ 2 ^ k := fun hk => by
  have h13 : (13 : ℕ) ∣ 2 ^ k := hk ▸ (by norm_num : (13 : ℕ) ∣ 26)
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 13) h13
  omega

theorem twentySix_ne_three_pow (k : ℕ) : (26 : ℕ) ≠ 3 ^ k := fun hk => by
  have h13 : (13 : ℕ) ∣ 3 ^ k := hk ▸ (by norm_num : (13 : ℕ) ∣ 26)
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 13) h13
  omega

theorem thirtySix_ne_two_pow (k : ℕ) : (36 : ℕ) ≠ 2 ^ k := fun hk => by
  have h3 : (3 : ℕ) ∣ 2 ^ k := hk ▸ (by norm_num : (3 : ℕ) ∣ 36)
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3
  omega

theorem thirtySix_ne_three_pow (k : ℕ) : (36 : ℕ) ≠ 3 ^ k := fun hk => by
  have h2 : (2 : ℕ) ∣ 3 ^ k := hk ▸ (by norm_num : (2 : ℕ) ∣ 36)
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 2) h2
  omega

/-- **Base 26.** No series `∑_j 26^(-B j) ∑_{i=1}^{N} c_i / (N j + i)` with rational `c_i` is
a non-zero rational multiple of `π`. -/
theorem no_pi_bailey_26 {B N : ℕ} (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) {q : ℚ}
    (h : HasSum (baileyBlock 26 B N c) ((q : ℝ) * Real.pi)) : q = 0 :=
  no_pi_bailey (by norm_num) twentySix_ne_two_pow hB hN c h

/-- **Base 36.** No series `∑_j 36^(-B j) ∑_{i=1}^{N} c_i / (N j + i)` with rational `c_i` is
a non-zero rational multiple of `π`. -/
theorem no_pi_bailey_36 {B N : ℕ} (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) {q : ℚ}
    (h : HasSum (baileyBlock 36 B N c) ((q : ℝ) * Real.pi)) : q = 0 :=
  no_pi_bailey (by norm_num) thirtySix_ne_two_pow hB hN c h

/-- **Base 26.** No series `∑_j 26^(-B j) ∑_{i=1}^{N} c_i / (N j + i)` with rational `c_i`
equals `log 26`. -/
theorem no_log_self_bailey_26 {B N : ℕ} (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) :
    ¬ HasSum (baileyBlock 26 B N c) (Real.log 26) := by
  have h := no_log_self_bailey (b := 26) (by norm_num) twentySix_ne_two_pow
    twentySix_ne_three_pow hB hN c
  exact_mod_cast h

/-- **Base 36.** No series `∑_j 36^(-B j) ∑_{i=1}^{N} c_i / (N j + i)` with rational `c_i`
equals `log 36`. -/
theorem no_log_self_bailey_36 {B N : ℕ} (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) :
    ¬ HasSum (baileyBlock 36 B N c) (Real.log 36) := by
  have h := no_log_self_bailey (b := 36) (by norm_num) thirtySix_ne_two_pow
    thirtySix_ne_three_pow hB hN c
  exact_mod_cast h

end BaseB

end PiFormula
