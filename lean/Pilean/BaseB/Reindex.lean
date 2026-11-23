import Pilean.BaseB.GeneralDefs

/-!
# The sub-series over the multiples of `halfIfEven n` is a series of the class `F_b`

A series of step `n` is `∑ ρ(k) b^(-⌊k/n⌋) / k` with `ρ` rational and periodic
(`seriesTermBN b n ρ`). Put `n₁ = halfIfEven n`: `n/2` for even `n`, and `n` for odd `n`. The
sub-series over the `k` divisible by `n₁` has its non-zero terms at `k = n₁ k'`.

* If `n` is even, `n = 2 n₁` and `⌊n₁ k'/n⌋ = ⌊k'/2⌋`: the sub-series is the series of the
  class `F_b` with the pattern `ρ'(k') = ρ(n₁ k') / n₁` (`subPatEven`), of the same period.
* If `n` is odd, `n₁ = n` and `⌊n k'/n⌋ = k'`: the sub-series is `∑ ρ(n k') b^(-k') / (n k')`,
  the series of the class `F_b` with the pattern `ρ''(2k') = 2 ρ(n k') / n`, `ρ''(odd) = 0`
  (`subPatOdd`), of twice the period.

Main statements:

* `hasSum_mul_left_iff`: a series supported on the multiples of `m`, re-indexed by `k ↦ m k`;
* `hasSum_subseries_even`, `hasSum_subseries_odd`: the two cases, with the patterns;
* `isFBValue_of_hasSum_subseries`: the value of the sub-series is a value of the class `F_b`.

All of this is a re-indexing of the series. It holds for every `b`; no convergence is used.
-/

namespace PiFormula

namespace BaseB

/-! ## 1. `halfIfEven` -/

private theorem halfIfEven_pos' {n : ℕ} (hn : 0 < n) : 0 < halfIfEven n := by
  unfold halfIfEven
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    omega
  · exact hn

private theorem halfIfEven_of_even' {n : ℕ} (h : Even n) : n = halfIfEven n * 2 := by
  rw [halfIfEven, ite_eq_left h]
  obtain ⟨m, rfl⟩ := h
  omega

private theorem halfIfEven_of_not_even' {n : ℕ} (h : ¬ Even n) : halfIfEven n = n := ite_eq_right h

/-! ## 2. Series supported on the multiples of `m` -/

/-- A series supported on the multiples of `m`, re-indexed by `k ↦ m k`. -/
theorem hasSum_mul_left_iff {m : ℕ} (hm : 0 < m) {f : ℕ → ℝ} (hf : ∀ k, ¬ m ∣ k → f k = 0)
    (x : ℝ) : HasSum (fun k : ℕ => f (m * k)) x ↔ HasSum f x := by
  have hinj : Function.Injective fun k : ℕ => m * k := fun _ _ h =>
    Nat.eq_of_mul_eq_mul_left hm h
  have hoff : ∀ k ∉ Set.range (fun k : ℕ => m * k), f k = 0 := fun k hk =>
    hf k fun ⟨c, hc⟩ => hk ⟨c, hc.symm⟩
  exact hinj.hasSum_iff hoff

/-- The terms of the sub-series vanish off the multiples of `m`. -/
theorem seriesTermBN_sub_of_not_dvd (b n : ℕ) (ρ : ℕ → ℚ) {m k : ℕ} (h : ¬ m ∣ k) :
    seriesTermBN b n (fun k => if m ∣ k then ρ k else 0) k = 0 := by
  simp [seriesTermBN, h]

/-- The term of the sub-series at a multiple of `m`. -/
theorem seriesTermBN_sub_mul (b n : ℕ) (ρ : ℕ → ℚ) (m k : ℕ) :
    seriesTermBN b n (fun k => if m ∣ k then ρ k else 0) (m * k) =
      (ρ (m * k) : ℝ) / (b : ℝ) ^ (m * k / n) / ((m * k : ℕ) : ℝ) := by
  rw [seriesTermBN, ite_eq_left (Dvd.intro k rfl)]

/-! ## 3. Even `n` -/

/-- The pattern of the sub-series for `n = 2 n₁`: `ρ'(k) = ρ(n₁ k) / n₁`. -/
def subPatEven (m : ℕ) (ρ : ℕ → ℚ) (k : ℕ) : ℚ := ρ (m * k) / m

theorem subPatEven_periodic (m : ℕ) {N : ℕ} {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) (k : ℕ) :
    subPatEven m ρ (k + N) = subPatEven m ρ k := by
  have h := periodic_mul hρ m (m * k)
  rw [subPatEven, subPatEven, mul_add, mul_comm m N, h]

/-- **The sub-series for `n = 2 n₁`** is the series of the class `F_b` with the pattern
`ρ'(k) = ρ(n₁ k) / n₁`. -/
theorem hasSum_subseries_even (b : ℕ) {m : ℕ} (hm : 0 < m) (ρ : ℕ → ℚ) (x : ℝ) :
    HasSum (seriesTermBN b (m * 2) (fun k => if m ∣ k then ρ k else 0)) x ↔
      HasSum (seriesTermB b (subPatEven m ρ)) x := by
  rw [← hasSum_mul_left_iff hm (fun k hk => seriesTermBN_sub_of_not_dvd b (m * 2) ρ hk)]
  have e : (fun k : ℕ => seriesTermBN b (m * 2) (fun k => if m ∣ k then ρ k else 0) (m * k)) =
      seriesTermB b (subPatEven m ρ) := by
    funext k
    rw [seriesTermBN_sub_mul, Nat.mul_div_mul_left k 2 hm, seriesTermB, subPatEven]
    push_cast
    ring
  rw [e]

/-! ## 4. Odd `n` -/

/-- The pattern of the sub-series for odd `n`: `ρ''(2k) = 2 ρ(n k) / n` and `ρ''(odd) = 0`. -/
def subPatOdd (n : ℕ) (ρ : ℕ → ℚ) (k : ℕ) : ℚ :=
  if 2 ∣ k then 2 * ρ (n * (k / 2)) / n else 0

theorem subPatOdd_two_mul (n : ℕ) (ρ : ℕ → ℚ) (k : ℕ) :
    subPatOdd n ρ (2 * k) = 2 * ρ (n * k) / n := by
  rw [subPatOdd, ite_eq_left (Dvd.intro k rfl), Nat.mul_div_cancel_left k (by norm_num)]

theorem subPatOdd_periodic (n : ℕ) {N : ℕ} {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) (k : ℕ) :
    subPatOdd n ρ (k + 2 * N) = subPatOdd n ρ k := by
  have e1 : 2 ∣ k + 2 * N ↔ 2 ∣ k := (Nat.dvd_add_iff_left (Dvd.intro N rfl)).symm
  have e2 : (k + 2 * N) / 2 = k / 2 + N := Nat.add_mul_div_left k N (by norm_num)
  have h := periodic_mul hρ n (n * (k / 2))
  simp only [subPatOdd, e1, e2, mul_add, mul_comm n N, h]

/-- **The sub-series for `n₁ = n`** is the series of the class `F_b` with the pattern
`ρ''(2k) = 2 ρ(n k) / n`, `ρ''(odd) = 0`. -/
theorem hasSum_subseries_odd (b : ℕ) {n : ℕ} (hn : 0 < n) (ρ : ℕ → ℚ) (x : ℝ) :
    HasSum (seriesTermBN b n (fun k => if n ∣ k then ρ k else 0)) x ↔
      HasSum (seriesTermB b (subPatOdd n ρ)) x := by
  have hoff : ∀ k, ¬ 2 ∣ k → seriesTermB b (subPatOdd n ρ) k = 0 := fun k hk => by
    simp [seriesTermB, subPatOdd, hk]
  rw [← hasSum_mul_left_iff hn (fun k hk => seriesTermBN_sub_of_not_dvd b n ρ hk),
    ← hasSum_mul_left_iff two_pos hoff]
  have e : (fun k : ℕ => seriesTermBN b n (fun k => if n ∣ k then ρ k else 0) (n * k)) =
      fun k : ℕ => seriesTermB b (subPatOdd n ρ) (2 * k) := by
    funext k
    rw [seriesTermBN_sub_mul, Nat.mul_div_cancel_left k hn, seriesTermB, subPatOdd_two_mul,
      Nat.mul_div_cancel_left k (by norm_num)]
    push_cast
    ring
  rw [e]

/-! ## 5. The sub-series is a series of the class `F_b` -/

/-- The value of the sub-series over the multiples of `halfIfEven n` is a value of the class
`F_b`, for every `b`. -/
theorem isFBValue_subseries (b : ℕ) {n : ℕ} (hn : 0 < n) {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + N) = ρ k) {x : ℝ}
    (h : HasSum (seriesTermBN b n (fun k => if halfIfEven n ∣ k then ρ k else 0)) x) :
    IsFBValue b x := by
  by_cases he : Even n
  · have h' : HasSum (seriesTermBN b (halfIfEven n * 2)
        (fun k => if halfIfEven n ∣ k then ρ k else 0)) x := by
      rw [← halfIfEven_of_even' he]
      exact h
    exact ⟨N, subPatEven (halfIfEven n) ρ, hN, subPatEven_periodic _ hρ,
      (hasSum_subseries_even b (halfIfEven_pos' hn) ρ x).1 h'⟩
  · rw [halfIfEven_of_not_even' he] at h
    exact ⟨2 * N, subPatOdd n ρ, Nat.mul_pos two_pos hN, subPatOdd_periodic n hρ,
      (hasSum_subseries_odd b hn ρ x).1 h⟩

set_option linter.unusedVariables false in
/-- **The sub-series over the multiples of `n₁ = halfIfEven n` is a series of the class
`F_b`.** If `ρ` is rational and periodic, the value of
`∑_{n₁ ∣ k} ρ(k) b^(-⌊k/n⌋) / k` is the value of a series `∑ ρ'(k) b^(-⌊k/2⌋) / k` with `ρ'`
rational and periodic. (The hypothesis `2 ≤ b` is not used: see `isFBValue_subseries`.) -/
theorem isFBValue_of_hasSum_subseries {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) {N : ℕ} (hN : 0 < N)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {x : ℝ}
    (h : HasSum (seriesTermBN b n (fun k => if halfIfEven n ∣ k then ρ k else 0)) x) :
    IsFBValue b x :=
  isFBValue_subseries b hn hN hρ h

end BaseB

end PiFormula
