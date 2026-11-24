module

public import Pilean.BaseB.Sharpness
public import Pilean.PiFormula.TheoremE
public import Pilean.PiFormula.Unconditional

/-!
# No degree-1 BBP-type formula for `π` uses fewer than `2/3` terms per bit

A degree-1 BBP-type formula of base `b` is a series (Bailey's `P(1, b^B, N, c)`)

  `∑_{j ≥ 0} b^(-B j) ∑_{i=1}^{N} c_i / (N j + i)`,   `c_i` rational.

If its value is a non-zero rational multiple of `π`, then `b = 2^e` (`bailey_pi_iff`), and one
block of `N` terms gains `e B` bits. The cost of the digit-extraction algorithm is the number of
non-zero `c_i` divided by `e B`: the terms per bit.

**Theorem** (`terms_per_bit`). The number of non-zero `c_i` is at least `(2/3) e B`.

`PiFormula/TheoremE.lean` has this bound for the series `∑ ρ(k) 2^(-⌊k/2⌋)/k` (the class F,
that is, `N = 2 e B`). The statement here is for every block length `N` and every base. It is
attained by Huvent's formula `P(1, 2^12, 24, c)` with 8 non-zero coefficients
(`terms_per_bit_attained`).

The proof. In base 2 with the exponent `B₀ = e B`:

* the series is the series of step `N` of the pattern `stepPat 2 B₀ N c`, of period `B₀ N`, with
  one non-zero entry per period for each non-zero `c_i` (`nzCount_stepPat_le`);
* a series of step `n` whose value is `q π` has the same value on the multiples of `n/2` (even
  `n`) or of `n` (odd `n`), and this sub-series is a series of the class F whose pattern has
  period `2 B₀` and no more non-zero entries per period (`nzCount_step_ge`);
* a pattern of the class F with the value `q π`, `q ≠ 0`, has period 120 and at least 40
  non-zero entries among 120 (`termCount_ge`); so a period `L` holds at least `L/3` non-zero
  entries (`nzCount_ge_two`).

Baker's theorem is used through the imported proof (`bakerTheorem`); there is no hypothesis.
-/

@[expose] public section

namespace PiFormula

namespace BaseB

/-! ## 1. Counting the non-zero entries of a pattern -/

/-- The number of non-zero entries of a pattern among the indices `0, …, L - 1`. -/
def nzCount (ρ : ℕ → ℚ) (L : ℕ) : ℕ := Nat.count (fun k => ρ k ≠ 0) L

theorem nzCount_eq_card (ρ : ℕ → ℚ) (L : ℕ) :
    nzCount ρ L = ((Finset.range L).filter fun k => ρ k ≠ 0).card :=
  Nat.count_eq_card_filter_range _ _

/-- For `L = 120` this is the `termCount` of `PiFormula/FewestTerms.lean`. -/
theorem nzCount_120 (ρ : ℕ → ℚ) : nzCount ρ 120 = termCount ρ := rfl

/-- A pattern of period `P` has `m` times as many non-zero entries in `P m` consecutive indices
as in one period. -/
theorem nzCount_mul {ρ : ℕ → ℚ} {P : ℕ} (hρ : ∀ k, ρ (k + P) = ρ k) (m : ℕ) :
    nzCount ρ (P * m) = m * nzCount ρ P := by
  induction m with
  | zero => simp [nzCount]
  | succ m ih =>
    have e : ∀ k, ρ (P * m + k) = ρ k := fun k => by rw [add_comm, periodic_mul hρ m k]
    have h1 : nzCount ρ (P * m + P) = nzCount ρ (P * m) + nzCount ρ P := by
      simp only [nzCount, Nat.count_add, e]
    rw [Nat.mul_succ, h1, ih]
    ring

/-- An injection of the non-zero entries of `ρ` below `L` into those of `σ` below `M`. -/
theorem nzCount_le_of_injOn {ρ σ : ℕ → ℚ} {L M : ℕ} (f : ℕ → ℕ)
    (hf : ∀ k < L, ρ k ≠ 0 → f k < M ∧ σ (f k) ≠ 0)
    (hinj : ∀ k₁ < L, ρ k₁ ≠ 0 → ∀ k₂ < L, ρ k₂ ≠ 0 → f k₁ = f k₂ → k₁ = k₂) :
    nzCount ρ L ≤ nzCount σ M := by
  rw [nzCount_eq_card, nzCount_eq_card]
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
    obtain ⟨h1, h2⟩ := hf k (Finset.mem_range.1 hk1) hk2
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2⟩
  · intro k₁ hk₁ k₂ hk₂ h12
    obtain ⟨h11, h12'⟩ := Finset.mem_filter.1 hk₁
    obtain ⟨h21, h22⟩ := Finset.mem_filter.1 hk₂
    exact hinj k₁ (Finset.mem_range.1 h11) h12' k₂ (Finset.mem_range.1 h21) h22 h12

/-! ## 2. The class F: at least `L/3` non-zero entries in a period `L` -/

private theorem seriesTermB_two_eq (ρ : ℕ → ℚ) : seriesTermB 2 ρ = seriesTerm ρ := by
  funext k
  simp only [seriesTermB, seriesTerm, Nat.cast_ofNat]

/-- **The class F.** A rational pattern of period `L` whose series `∑ ρ(k) 2^(-⌊k/2⌋)/k` is a
non-zero rational multiple of `π` has at least `L/3` non-zero entries per period. (It has period
120 and at least 40 non-zero entries among 120.) -/
theorem nzCount_ge_two {L : ℕ} (hL : 0 < L) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + L) = ρ k) {q : ℚ}
    (hq : q ≠ 0) (h : HasSum (seriesTerm ρ) ((q : ℝ) * Real.pi)) : L ≤ 3 * nzCount ρ L := by
  have hP : 0 < L * 120 := by positivity
  have h120 : 120 ∣ L * 120 := Dvd.intro_left L rfl
  have hper : ∀ k, ρ (k + L * 120) = ρ k := periodic_mul hρ 120
  have h40 : 40 ≤ termCount ρ := termCount_ge bakerTheorem hP h120 hper hq h
  obtain ⟨c, hc⟩ := exists_coords bakerTheorem hP h120 ⟨hper, q, h⟩
  have hρ120 : ∀ k, ρ (k + 120) = ρ k := fun k => by
    rw [hc]
    exact namedComb_periodic c k
  have e1 : nzCount ρ (L * 120) = 120 * nzCount ρ L := nzCount_mul hρ 120
  have e2 : nzCount ρ (120 * L) = L * nzCount ρ 120 := nzCount_mul hρ120 L
  rw [mul_comm, e2, nzCount_120] at e1
  have h3 : L * 40 ≤ L * termCount ρ := Nat.mul_le_mul_left L h40
  omega

/-! ## 3. A series of step `n` in base 2 -/

private theorem notPerfectPower_two : NotPerfectPower 2 := by
  intro a k hk h
  have ha : 2 ≤ a := by
    by_contra hlt
    have ha : a = 0 ∨ a = 1 := by omega
    rcases ha with rfl | rfl
    · rw [zero_pow (by omega)] at h
      omega
    · rw [one_pow] at h
      omega
  have h1 : a ^ 2 ≤ a ^ k := Nat.pow_le_pow_right (by omega) hk
  nlinarith

private theorem subPatOdd_ne_zero {n : ℕ} {ρ : ℕ → ℚ} {k : ℕ} (h : subPatOdd n ρ k ≠ 0) :
    2 ∣ k ∧ ρ (n * (k / 2)) ≠ 0 := by
  by_cases hd : 2 ∣ k
  · refine ⟨hd, fun h0 => h ?_⟩
    rw [subPatOdd, ite_eq_left hd, h0, mul_zero, zero_div]
  · exact absurd (ite_eq_right hd) h

/-- **Every step, base 2.** Let `ρ` be a rational pattern of period `L n` (one period of the
series of step `n` gains `L` bits). If `∑ ρ(k) 2^(-⌊k/n⌋)/k = q π` with `q ≠ 0` rational, then
`ρ` has at least `(2/3) L` non-zero entries per period. -/
theorem nzCount_step_ge {n L : ℕ} (hn : 0 < n) (hL : 0 < L) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + L * n) = ρ k) {q : ℚ} (hq : q ≠ 0)
    (h : HasSum (seriesTermBN 2 n ρ) ((q : ℝ) * Real.pi)) :
    2 * L ≤ 3 * nzCount ρ (L * n) := by
  have hsub := subseries_of_kummerHom bakerTheorem le_rfl hn
    (kummerHom le_rfl notPerfectPower_two hn) (Nat.mul_pos hL hn) hρ h
  have h2L : 0 < 2 * L := by positivity
  by_cases he : Even n
  · obtain ⟨m, hm⟩ := he
    have hm0 : 0 < m := by omega
    have hh : halfIfEven n = m := by
      rw [halfIfEven, ite_eq_left ⟨m, hm⟩]
      omega
    have hn2 : n = m * 2 := by omega
    rw [hh] at hsub
    subst hn2
    have h2 := (hasSum_subseries_even 2 hm0 ρ _).1 hsub
    rw [seriesTermB_two_eq] at h2
    have hper : ∀ k, subPatEven m ρ (k + 2 * L) = subPatEven m ρ k := fun k => by
      rw [subPatEven, subPatEven, mul_add, show m * (2 * L) = L * (m * 2) by ring, hρ]
    have hge := nzCount_ge_two h2L hper hq h2
    have hle : nzCount (subPatEven m ρ) (2 * L) ≤ nzCount ρ (L * (m * 2)) := by
      refine nzCount_le_of_injOn (fun k => m * k) ?_ ?_
      · intro k hk hne
        refine ⟨by nlinarith, fun h0 => hne ?_⟩
        rw [subPatEven, h0, zero_div]
      · intro k₁ _ _ k₂ _ _ h12
        exact Nat.eq_of_mul_eq_mul_left hm0 h12
    omega
  · rw [halfIfEven, ite_eq_right he] at hsub
    have h2 := (hasSum_subseries_odd 2 hn ρ _).1 hsub
    rw [seriesTermB_two_eq] at h2
    have hper : ∀ k, subPatOdd n ρ (k + 2 * L) = subPatOdd n ρ k := fun k => by
      have e1 : 2 ∣ k + 2 * L ↔ 2 ∣ k := (Nat.dvd_add_iff_left (Dvd.intro L rfl)).symm
      have e2 : (k + 2 * L) / 2 = k / 2 + L := Nat.add_mul_div_left k L (by norm_num)
      simp only [subPatOdd, e1, e2, mul_add, mul_comm n L, hρ]
    have hge := nzCount_ge_two h2L hper hq h2
    have hle : nzCount (subPatOdd n ρ) (2 * L) ≤ nzCount ρ (L * n) := by
      refine nzCount_le_of_injOn (fun k => n * (k / 2)) ?_ ?_
      · intro k hk hne
        obtain ⟨_, h0⟩ := subPatOdd_ne_zero hne
        have hk2 : k / 2 < L := by omega
        exact ⟨by nlinarith, h0⟩
      · intro k₁ _ h₁ k₂ _ h₂ h12
        obtain ⟨d1, _⟩ := subPatOdd_ne_zero h₁
        obtain ⟨d2, _⟩ := subPatOdd_ne_zero h₂
        have h3 : k₁ / 2 = k₂ / 2 := Nat.eq_of_mul_eq_mul_left hn h12
        omega
    omega

/-! ## 4. Bailey's sums -/

private theorem stepPat_ne_zero {b B' n N : ℕ} {hN : 0 < N} {c : Fin N → ℚ} {m : ℕ}
    (h : stepPat b B' n hN c m ≠ 0) : B' ∣ m ∧ c (bIdx hN (m / B')) ≠ 0 := by
  by_cases hd : B' ∣ m
  · refine ⟨hd, fun h0 => h ?_⟩
    rw [stepPat, ite_eq_left hd, h0, zero_mul]
  · exact absurd (stepPat_of_not_dvd b n hN c hd) h

/-- The pattern of a coefficient vector has at most one non-zero entry per period `B' N` for
each non-zero coefficient. -/
theorem nzCount_stepPat_le (b n B' : ℕ) {N : ℕ} (hN : 0 < N) (c : Fin N → ℚ) :
    nzCount (stepPat b B' n hN c) (B' * N) ≤ (Finset.univ.filter fun i => c i ≠ 0).card := by
  rw [nzCount_eq_card]
  have hlt : ∀ k ∈ (Finset.range (B' * N)).filter fun k => stepPat b B' n hN c k ≠ 0,
      B' ∣ k ∧ k / B' < N ∧ c (bIdx hN (k / B')) ≠ 0 := fun k hk => by
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
    obtain ⟨hd, hc⟩ := stepPat_ne_zero hk2
    exact ⟨hd, Nat.div_lt_of_lt_mul (Finset.mem_range.1 hk1), hc⟩
  refine Finset.card_le_card_of_injOn (fun k => bIdx hN (k / B')) ?_ ?_
  · intro k hk
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hlt k hk).2.2⟩
  · intro k₁ hk₁ k₂ hk₂ h12
    obtain ⟨d1, l1, _⟩ := hlt k₁ hk₁
    obtain ⟨d2, l2, _⟩ := hlt k₂ hk₂
    have h3 : bIdx hN (k₁ / B') = bIdx hN (k₂ / B') := h12
    have e1 := bIdx_mod hN (k₁ / B')
    have e2 := bIdx_mod hN (k₂ / B')
    rw [h3, e2, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at e1
    rw [← Nat.mul_div_cancel' d1, ← Nat.mul_div_cancel' d2, e1]

/-- The bound in base 2: `P(1, 2^B, N, c) = q π` with `q ≠ 0` needs at least `(2/3) B` non-zero
coefficients. -/
theorem terms_per_bit_two {B N : ℕ} (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) {q : ℚ}
    (hq : q ≠ 0) (h : HasSum (baileyBlock 2 B N c) ((q : ℝ) * Real.pi)) :
    2 * B ≤ 3 * (Finset.univ.filter fun i => c i ≠ 0).card := by
  have h1 := (hasSum_bailey_iff (b := 2) (B := B) (B' := B) (n := N) le_rfl hB hN hN rfl c
    _).1 h
  have h2 := nzCount_step_ge hN hB (stepPat_periodic 2 N hB hN c) hq h1
  have h3 := nzCount_stepPat_le 2 N B hN c
  omega

/-! ## 5. The theorem -/

/-- **No degree-1 BBP-type formula for π uses fewer than 2/3 terms per bit.** If
`∑_j b^(-B j) ∑_{i=1}^{N} c_i/(N j + i) = q π` with `q ≠ 0` rational, then `b = 2^e` and the
number of non-zero `c_i` is at least `(2/3) e B` (the block of `N` terms gains `e B` bits). -/
theorem terms_per_bit {b B N : ℕ} (hb : 2 ≤ b) (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) {q : ℚ}
    (hq : q ≠ 0) (h : HasSum (baileyBlock b B N c) ((q : ℝ) * Real.pi)) :
    ∃ e : ℕ, b = 2 ^ e ∧ 2 * (e * B) ≤ 3 * (Finset.univ.filter fun i => c i ≠ 0).card := by
  obtain ⟨e, rfl⟩ := (bailey_pi_iff hb).1 ⟨B, N, c, q, hB, hN, hq, h⟩
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · norm_num at hb
    · exact he
  rw [baileyBlock_pow] at h
  exact ⟨e, rfl, terms_per_bit_two (Nat.mul_pos he hB) hN c hq h⟩

/-- **The bound is attained**: Huvent's first formula `P(1, 2^12, 24, c) = 128 π` has 8
non-zero coefficients, and `2 · 12 = 3 · 8`. -/
theorem terms_per_bit_attained :
    ∃ (c : Fin 24 → ℚ) (q : ℚ), q ≠ 0 ∧ HasSum (baileyBlock 2 12 24 c) ((q : ℝ) * Real.pi) ∧
      (Finset.univ.filter fun i => c i ≠ 0).card = 8 := by
  refine ⟨huvent1, 128, by norm_num, ?_, by decide +kernel⟩
  have h := huvent1_formula
  rw [← baileyBlock_two] at h
  have e : (512 : ℝ) * (Real.pi / 4) = ((128 : ℚ) : ℝ) * Real.pi := by
    push_cast
    ring
  rw [← e]
  exact h

end BaseB

end PiFormula
