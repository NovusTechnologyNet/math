import Pilean.BaseB.Reindex

/-!
# Bailey's notation in a general base: every `P(1, b^B, N, A)` is a series of step `n`

Bailey's notation is `P(s, β, N, A) = ∑_{j ≥ 0} β^(-j) ∑_{i=1}^N a_i / (Nj + i)^s`. Here
`s = 1` and `β = b^B`. `baileyBlock b B N a j` is the `j`-th block, written exactly as
Bailey's double sum; `a i` (`i : Fin N`) is Bailey's `a_{i+1}`.

Let `g = gcd(B, N)`, `n = N / g` and `B' = B / g`, so that `B' N = B n`. For
`k = Nj + i + 1` put `k' = B' k`. Then `⌊k'/n⌋ = Bj + ⌊B'(i+1)/n⌋`, so

  `a_i b^(-Bj) / k = ρ(k') b^(-⌊k'/n⌋) / k'`   with   `ρ(k') = B' b^⌊B'(i+1)/n⌋ a_i`,

and `ρ = 0` off the multiples of `B'`. The pattern `ρ` (`stepPat`) is rational, of period
`B' N`.

Main statements:

* `summable_seriesTermBN`: for `b ≥ 2`, the series of step `n` of a periodic rational
  pattern converges absolutely;
* `hasSum_bailey_iff`: if `B' N = B n`, Bailey's sum `P(1, b^B, N, A)` is the series of step
  `n` of the pattern `stepPat b B' n A`;
* `exists_step_of_bailey`: every `P(1, b^B, N, A)` is a series of step `n = N / gcd(B, N)`.
-/

namespace PiFormula

namespace BaseB

/-! ## 1. Convergence -/

/-- `∑ r^⌊k/n⌋` converges for `0 ≤ r < 1`. -/
theorem summable_pow_div {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {n : ℕ} (hn : 0 < n) :
    Summable fun k : ℕ => r ^ (k / n) := by
  have : NeZero n := ⟨hn.ne'⟩
  have hg : Summable fun _ : Fin n => (1 : ℝ) := (hasSum_fintype _).summable
  have h1 : Summable fun p : ℕ × Fin n => r ^ p.1 * (1 : ℝ) :=
    Summable.mul_of_nonneg (f := fun k : ℕ => r ^ k) (g := fun _ : Fin n => (1 : ℝ))
      (summable_geometric_of_lt_one hr0 hr1) hg (fun k => pow_nonneg hr0 k)
      (fun _ => zero_le_one)
  rw [← (Nat.divModEquiv n).symm.summable_iff]
  refine h1.congr fun p => ?_
  change r ^ p.1 * 1 = r ^ ((p.1 * n + (p.2 : ℕ)) / n)
  rw [mul_one, mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt p.2.2, add_zero]

/-- A periodic pattern is bounded. -/
theorem abs_le_sum_of_periodic {P : ℕ} (hP : 0 < P) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + P) = ρ k)
    (k : ℕ) : |(ρ k : ℝ)| ≤ ∑ i ∈ Finset.range P, |(ρ i : ℝ)| := by
  rw [← period_mod hρ k]
  exact Finset.single_le_sum (f := fun i => |(ρ i : ℝ)|) (fun i _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.mod_lt k hP))

/-- **The series of step `n` of a periodic rational pattern converges**, for `b ≥ 2`. -/
theorem summable_seriesTermBN {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) {P : ℕ} (hP : 0 < P)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + P) = ρ k) : Summable (seriesTermBN b n ρ) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hgeo : Summable fun k : ℕ =>
      (∑ i ∈ Finset.range P, |(ρ i : ℝ)|) * ((b : ℝ)⁻¹) ^ (k / n) :=
    (summable_pow_div (inv_nonneg.2 hb0.le) (inv_lt_one_of_one_lt₀ (by linarith)) hn).mul_left _
  refine Summable.of_norm_bounded hgeo fun k => ?_
  have hp : 0 < (b : ℝ) ^ (k / n) := pow_pos hb0 _
  have h1 : |(ρ k : ℝ)| / (b : ℝ) ^ (k / n) ≤
      (∑ i ∈ Finset.range P, |(ρ i : ℝ)|) / (b : ℝ) ^ (k / n) :=
    div_le_div_of_nonneg_right (abs_le_sum_of_periodic hP hρ k) hp.le
  have h0 : 0 ≤ |(ρ k : ℝ)| / (b : ℝ) ^ (k / n) := div_nonneg (abs_nonneg _) hp.le
  rw [seriesTermBN, Real.norm_eq_abs, abs_div, abs_div, abs_of_pos hp, Nat.abs_cast, inv_pow,
    ← div_eq_mul_inv]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.cast_zero, div_zero]
    exact h0.trans h1
  · exact (div_le_self h0 (by exact_mod_cast hk)).trans h1

theorem seriesTermBN_at_zero (b n : ℕ) (ρ : ℕ → ℚ) : seriesTermBN b n ρ 0 = 0 := by
  simp [seriesTermBN]

/-! ## 2. Bailey's sums and their patterns -/

/-- The block `j` of Bailey's `P(1, b^B, N, a)`: `b^(-B j) ∑_{i=1}^{N} a_i / (N j + i)`. -/
noncomputable def baileyBlock (b B N : ℕ) (a : Fin N → ℚ) (j : ℕ) : ℝ :=
  ∑ i : Fin N, (a i : ℝ) / (b : ℝ) ^ (B * j) / ((N * j + i + 1 : ℕ) : ℝ)

/-- The pattern of a coefficient vector, for the step `n` and the factor `B'` (with
`B' N = B n`): `ρ(B' k) = B' b^⌊B'(i+1)/n⌋ a_i` for `k = Nj + i + 1`, and `ρ = 0` off the
multiples of `B'`. -/
def stepPat (b B' n : ℕ) {N : ℕ} (hN : 0 < N) (a : Fin N → ℚ) (m : ℕ) : ℚ :=
  if B' ∣ m then
    a (bIdx hN (m / B')) * (B' * (b : ℚ) ^ (B' * ((bIdx hN (m / B') : ℕ) + 1) / n))
  else 0

theorem stepPat_mul (b n : ℕ) {B' : ℕ} (hB' : 0 < B') {N : ℕ} (hN : 0 < N) (a : Fin N → ℚ)
    (k : ℕ) :
    stepPat b B' n hN a (B' * k) =
      a (bIdx hN k) * (B' * (b : ℚ) ^ (B' * ((bIdx hN k : ℕ) + 1) / n)) := by
  rw [stepPat, ite_eq_left (Dvd.intro k rfl), Nat.mul_div_cancel_left k hB']

theorem stepPat_of_not_dvd (b n : ℕ) {B' : ℕ} {N : ℕ} (hN : 0 < N) (a : Fin N → ℚ) {m : ℕ}
    (h : ¬ B' ∣ m) : stepPat b B' n hN a m = 0 :=
  ite_eq_right h

/-- The pattern has period `B' N`. -/
theorem stepPat_periodic (b n : ℕ) {B' : ℕ} (hB' : 0 < B') {N : ℕ} (hN : 0 < N)
    (a : Fin N → ℚ) (m : ℕ) : stepPat b B' n hN a (m + B' * N) = stepPat b B' n hN a m := by
  have e1 : B' ∣ m + B' * N ↔ B' ∣ m := (Nat.dvd_add_iff_left (Dvd.intro N rfl)).symm
  have e2 : (m + B' * N) / B' = m / B' + N := Nat.add_mul_div_left m N hB'
  simp only [stepPat, e1, e2, bIdx_add]

/-- The term of the pattern at `k' = B' (Nj + i + 1)` is Bailey's term. -/
theorem seriesTermBN_stepPat {b B B' N n : ℕ} (hb : 2 ≤ b) (hB' : 0 < B') (hn : 0 < n)
    (hN : 0 < N) (hBN : B' * N = B * n) (a : Fin N → ℚ) (j : ℕ) (i : Fin N) :
    seriesTermBN b n (stepPat b B' n hN a) (B' * (N * j + i + 1)) =
      (a i : ℝ) / (b : ℝ) ^ (B * j) / ((N * j + i + 1 : ℕ) : ℝ) := by
  have e : B' * (N * j + (i : ℕ) + 1) / n = B * j + B' * ((i : ℕ) + 1) / n := by
    have e1 : B' * (N * j + (i : ℕ) + 1) = n * (B * j) + B' * ((i : ℕ) + 1) := by
      rw [add_assoc, mul_add, ← mul_assoc, hBN]
      ring
    rw [e1]
    exact Nat.mul_add_div hn _ _
  have hb0 : (b : ℝ) ≠ 0 := by
    have : 0 < b := by omega
    positivity
  have hB0 : (B' : ℝ) ≠ 0 := by positivity
  have hk0 : ((N * j + (i : ℕ) + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [seriesTermBN, stepPat_mul b n hB' hN, bIdx_block, e, pow_add]
  push_cast
  field_simp

/-- **Bailey's sum `P(1, b^B, N, A)` is the series of step `n` of the pattern**, whenever
`B' N = B n`. -/
theorem hasSum_bailey_iff {b B B' N n : ℕ} (hb : 2 ≤ b) (hB' : 0 < B') (hn : 0 < n)
    (hN : 0 < N) (hBN : B' * N = B * n) (a : Fin N → ℚ) (x : ℝ) :
    HasSum (baileyBlock b B N a) x ↔ HasSum (seriesTermBN b n (stepPat b B' n hN a)) x := by
  have hs : Summable (seriesTermBN b n (stepPat b B' n hN a)) :=
    summable_seriesTermBN hb hn (Nat.mul_pos hB' hN) (stepPat_periodic b n hB' hN a)
  have hoff : ∀ k, ¬ B' ∣ k → seriesTermBN b n (stepPat b B' n hN a) k = 0 := fun k hk => by
    rw [seriesTermBN, stepPat_of_not_dvd b n hN a hk]
    simp
  have hs' : Summable fun k : ℕ => seriesTermBN b n (stepPat b B' n hN a) (B' * k) :=
    hs.comp_injective (mul_right_injective₀ hB'.ne')
  have h0 : (fun k : ℕ => seriesTermBN b n (stepPat b B' n hN a) (B' * k)) 0 = 0 := by
    change seriesTermBN b n (stepPat b B' n hN a) (B' * 0) = 0
    rw [mul_zero, seriesTermBN_at_zero]
  rw [← hasSum_mul_left_iff hB' hoff, ← hasSum_blocks_iff hN hs' h0 x]
  have e : baileyBlock b B N a = fun j : ℕ => ∑ i : Fin N,
      (fun k : ℕ => seriesTermBN b n (stepPat b B' n hN a) (B' * k)) (N * j + i + 1) := by
    funext j
    exact Finset.sum_congr rfl fun i _ => (seriesTermBN_stepPat hb hB' hn hN hBN a j i).symm
  rw [e]

/-! ## 3. Every Bailey sum is a series of step `N / gcd(B, N)` -/

/-- **Every `P(1, b^B, N, A)` is a series of step `n = N / gcd(B, N)`**: its value is the
value of `∑ ρ(k) b^(-⌊k/n⌋) / k` for a rational periodic pattern `ρ` (of period
`(B / gcd(B, N)) N`, given by `stepPat`). -/
theorem exists_step_of_bailey {b B N : ℕ} (hb : 2 ≤ b) (hB : 0 < B) (hN : 0 < N)
    (a : Fin N → ℚ) {x : ℝ} (h : HasSum (baileyBlock b B N a) x) :
    ∃ (P : ℕ) (ρ : ℕ → ℚ), 0 < P ∧ (∀ k, ρ (k + P) = ρ k) ∧
      HasSum (seriesTermBN b (N / Nat.gcd B N) ρ) x := by
  have hg : 0 < Nat.gcd B N := Nat.gcd_pos_of_pos_right B hN
  have e1 : B / Nat.gcd B N * Nat.gcd B N = B := Nat.div_mul_cancel (Nat.gcd_dvd_left B N)
  have e2 : N / Nat.gcd B N * Nat.gcd B N = N := Nat.div_mul_cancel (Nat.gcd_dvd_right B N)
  have hB' : 0 < B / Nat.gcd B N :=
    Nat.div_pos (Nat.le_of_dvd hB (Nat.gcd_dvd_left B N)) hg
  have hn : 0 < N / Nat.gcd B N :=
    Nat.div_pos (Nat.le_of_dvd hN (Nat.gcd_dvd_right B N)) hg
  have hBN : B / Nat.gcd B N * N = B * (N / Nat.gcd B N) := by
    apply Nat.eq_of_mul_eq_mul_right hg
    rw [mul_right_comm, e1, mul_assoc, e2]
  exact ⟨B / Nat.gcd B N * N, stepPat b (B / Nat.gcd B N) (N / Nat.gcd B N) hN a,
    Nat.mul_pos hB' hN, stepPat_periodic b _ hB' hN a,
    (hasSum_bailey_iff hb hB' hn hN hBN a x).1 h⟩

end BaseB

end PiFormula
