module

public import Pilean.BaseB.TheoremG
public import Pilean.BaseB.Kummer
public import Pilean.BaseB.Subseries
public import Pilean.BaseB.Reindex
public import Pilean.BaseB.BaileyForm
public import Pilean.Base3.Unconditional

/-!
# Degree-1 BBP-type formulas for `π` exist only in bases that are powers of 2

A degree-1 BBP-type formula of base `b` is a series (Bailey's `P(1, b^B, N, a)`)

  `∑_{j ≥ 0} b^(-B j) ∑_{i=1}^{N} a_i / (N j + i)`,   `a_i` rational.

**Theorem** (`no_pi_bailey`). Let `b ≥ 2` be an integer that is not a power of 2. If such a
series has the value `q π` with `q` rational, then `q = 0`.

For powers of 2 there are such formulas (Bailey, Borwein and Plouffe, 1995). The statement
concerns formulas of degree 1 with rational coefficients; it says nothing about formulas of
higher degree (polylogarithmic), and it is not a statement about computing digits.

The proof assembles five files:

* `BaileyForm`: the series is a series `∑ ρ(k) a^(-⌊k/n⌋)/k` of some step `n`, in the base
  `a` that is not a perfect power and has `b` as a power;
* `Kummer` and `Subseries`: its sub-series over the multiples of `n/2` (or `n`, for odd `n`)
  has the same value `q π`;
* `Reindex`: that sub-series is a series of the class `F_a` (step 2);
* `TheoremG` (`a ≥ 5`) and `Base3` (`a = 3`): in the class `F_a` a rational multiple of `π`
  is zero.

Baker's theorem is used through the imported proof (`bakerTheorem`); there is no hypothesis.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-- For `b = 3` the class `F_b` is the class F3 of `Base3`. -/
theorem isFBValue_three_iff {x : ℝ} : IsFBValue 3 x ↔ Base3.IsF3Value x := by
  have e : ∀ ρ : ℕ → ℚ, seriesTermB 3 ρ = Base3.seriesTerm3 ρ := fun ρ => by
    funext k
    simp [seriesTermB, Base3.seriesTerm3]
  constructor
  · rintro ⟨N, ρ, hN, hρ, h⟩
    exact ⟨N, ρ, hN, hρ, by rwa [← e]⟩
  · rintro ⟨N, ρ, hN, hρ, h⟩
    exact ⟨N, ρ, hN, hρ, by rwa [e]⟩

/-- In the class `F_b` with `b = 3` or `b ≥ 5`, a rational multiple of `π` is zero. -/
theorem rat_mul_pi_FB {b : ℕ} (hb : b = 3 ∨ 5 ≤ b) {q : ℚ}
    (h : IsFBValue b ((q : ℝ) * Real.pi)) : q = 0 := by
  rcases hb with rfl | hb
  · exact Base3.Unconditional.not_isF3Value_rat_mul_pi (isFBValue_three_iff.1 h)
  · have hq : IsAlgebraic ℚ (q : ℝ) := isAlgebraic_ratCast ℚ (A := ℝ) q
    have h0 := Unconditional.mul_pi_eq_zero hb hq h
    exact_mod_cast h0

/-- **Every step.** Let `b = 3` or `b ≥ 5`, not a perfect power. If a series
`∑ ρ(k) b^(-⌊k/n⌋)/k` with `ρ` rational and periodic has the value `q π` with `q` rational,
then `q = 0`. -/
theorem rat_mul_pi_step {b n : ℕ} (hb : b = 3 ∨ 5 ≤ b) (hpp : NotPerfectPower b) (hn : 0 < n)
    {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {q : ℚ}
    (h : HasSum (seriesTermBN b n ρ) ((q : ℝ) * Real.pi)) : q = 0 := by
  have hb2 : 2 ≤ b := by
    rcases hb with rfl | hb <;> omega
  have hsub := subseries_of_kummerHom bakerTheorem hb2 hn (kummerHom hb2 hpp hn) hN hρ h
  exact rat_mul_pi_FB hb (isFBValue_of_hasSum_subseries hb2 hn hN hρ hsub)

/-- Bailey's series in base `a^j` with exponent `B` is the series in base `a` with exponent
`j B`. -/
theorem baileyBlock_pow (a j B N : ℕ) (c : Fin N → ℚ) :
    baileyBlock (a ^ j) B N c = baileyBlock a (j * B) N c := by
  funext i
  simp only [baileyBlock, Nat.cast_pow, ← pow_mul, mul_assoc]

/-- Every integer `b ≥ 2` is a power of an integer `a ≥ 2` that is not a perfect power. -/
theorem exists_root_notPerfectPower {b : ℕ} (hb : 2 ≤ b) :
    ∃ a j : ℕ, 2 ≤ a ∧ 0 < j ∧ NotPerfectPower a ∧ a ^ j = b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    by_cases hpp : NotPerfectPower b
    · exact ⟨b, 1, hb, one_pos, hpp, pow_one b⟩
    · unfold NotPerfectPower at hpp
      push Not at hpp
      obtain ⟨a, k, hk, hak⟩ := hpp
      have ha2 : 2 ≤ a := by
        by_contra hlt
        have ha : a = 0 ∨ a = 1 := by omega
        rcases ha with rfl | rfl
        · rw [zero_pow (by omega)] at hak
          omega
        · rw [one_pow] at hak
          omega
      have hab : a < b := by
        rw [← hak]
        exact lt_self_pow₀ (by omega) (by omega)
      obtain ⟨a', j', ha', hj', hpp', h'⟩ := ih a hab ha2
      exact ⟨a', j' * k, ha', Nat.mul_pos hj' (by omega), hpp', by rw [pow_mul, h', hak]⟩

/-- **Degree-1 BBP-type formulas for `π` exist only in bases that are powers of 2.** Let
`b ≥ 2` be an integer that is not a power of 2, `B, N ≥ 1`, and `c_1, …, c_N` rational. If

  `∑_{j ≥ 0} b^(-B j) ∑_{i=1}^{N} c_i / (N j + i) = q π`

with `q` rational, then `q = 0`. -/
theorem no_pi_bailey {b B N : ℕ} (hb : 2 ≤ b) (h2 : ∀ k : ℕ, b ≠ 2 ^ k) (hB : 0 < B)
    (hN : 0 < N) (c : Fin N → ℚ) {q : ℚ}
    (h : HasSum (baileyBlock b B N c) ((q : ℝ) * Real.pi)) : q = 0 := by
  obtain ⟨a, j, ha, hj, hpp, rfl⟩ := exists_root_notPerfectPower hb
  have ha3 : a = 3 ∨ 5 ≤ a := by
    have h2' : a ≠ 2 := fun h => h2 j (by rw [h])
    have h4 : a ≠ 4 := fun h => hpp 2 2 le_rfl (by rw [h]; norm_num)
    omega
  rw [baileyBlock_pow] at h
  obtain ⟨P, ρ, hP, hρ, hs⟩ := exists_step_of_bailey ha (Nat.mul_pos hj hB) hN c h
  have hn : 0 < N / Nat.gcd (j * B) N :=
    Nat.div_pos (Nat.le_of_dvd hN (Nat.gcd_dvd_right _ _)) (Nat.gcd_pos_of_pos_right _ hN)
  exact rat_mul_pi_step ha3 hpp hn hP hρ hs

/-- **Base 10.** No series `∑_j 10^(-B j) ∑_{i=1}^{N} c_i / (N j + i)` with rational `c_i`
is a non-zero rational multiple of `π`. -/
theorem no_pi_bailey_ten {B N : ℕ} (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) {q : ℚ}
    (h : HasSum (baileyBlock 10 B N c) ((q : ℝ) * Real.pi)) : q = 0 := by
  refine no_pi_bailey (by norm_num) (fun k hk => ?_) hB hN c h
  have h5 : (5 : ℕ) ∣ 2 ^ k := hk ▸ (by norm_num : (5 : ℕ) ∣ 10)
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5)
  omega

end BaseB

end PiFormula
