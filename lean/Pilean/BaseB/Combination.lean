import Pilean.BaseB.LogBase

/-!
# Combinations of degree-1 BBP-type series of one base

Borwein, Borwein and Galway (2004, Comment 10) ask whether `π` can be a rational linear
combination of the series `L(1, b^m, n, j) = ∑_k b^(-m k) / (n k + j)` with several exponents
`m` and several lengths `n` at once. `no_pi_bailey` covers one series
`P(1, b^B, N, c) = ∑_j b^(-B j) ∑_{i=1}^{N} c_i / (N j + i)`. Here: finitely many such series
of the same base `b`, with arbitrary exponents and lengths, regroup into one. So the theorem
holds for combinations.

The regrouping goes through the series of step `n`, `∑ ρ(k) b^(-⌊k/n⌋) / k` with `ρ` rational
and periodic (`seriesTermBN`):

* every `P(1, b^B, N, c)` is a series of some step (`exists_step_of_bailey`);
* a series of step `n` is a series of step `n d`: replace `k` by `d k`, with the pattern
  `ρ'(d k) = d ρ(k)` and `ρ' = 0` off the multiples of `d`; `⌊d k / (n d)⌋ = ⌊k / n⌋`
  (`hasSum_seriesTermBN_step_mul`);
* two series of the same step add: add the patterns (`seriesTermBN_add`);
* a series of step `n` with a pattern of period `P` is `P(1, b^P, P n, a)` with
  `a_i = ρ(i) b^(-⌊i/n⌋)` (`exists_bailey_of_step`).

Main statements:

* `baileyBlock_smul`, `hasSum_baileyBlock_smul`: a rational factor of a series goes into its
  coefficient vector, so the rational coefficients of a combination are absorbed;
* `exists_bailey_add`, `exists_bailey_of_sum`: a finite sum of degree-1 BBP-type series of
  base `b` is one such series;
* `no_pi_bailey_sum`, `no_pi_bailey_comb`: if `b` is not a power of 2, no rational
  combination of such series is a non-zero rational multiple of `π`;
* `no_pi_L_comb`: the same for the series `L(1, b^m, n, j)`, `1 ≤ j ≤ n`;
* `no_log_bailey_sum`: the corollary of `no_log_bailey` for combinations.
-/

namespace PiFormula

namespace BaseB

/-! ## 1. Bailey's block is linear in the coefficient vector -/

private theorem baileyBlock_zero (b B N : ℕ) : baileyBlock b B N 0 = fun _ => 0 := by
  funext j
  simp [baileyBlock]

/-- Bailey's block is linear in the coefficient vector: a rational factor comes out. -/
theorem baileyBlock_smul (b B N : ℕ) (r : ℚ) (a : Fin N → ℚ) (j : ℕ) :
    baileyBlock b B N (r • a) j = (r : ℝ) * baileyBlock b B N a j := by
  simp only [baileyBlock, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- A rational multiple of a degree-1 BBP-type series: multiply the coefficients. -/
theorem hasSum_baileyBlock_smul {b B N : ℕ} (r : ℚ) {a : Fin N → ℚ} {x : ℝ}
    (h : HasSum (baileyBlock b B N a) x) : HasSum (baileyBlock b B N (r • a)) ((r : ℝ) * x) := by
  have e : baileyBlock b B N (r • a) = fun j => (r : ℝ) * baileyBlock b B N a j :=
    funext fun j => baileyBlock_smul b B N r a j
  rw [e]
  exact h.mul_left _

/-! ## 2. A series of step `n` is a series of step `n d` -/

/-- The pattern of step `n d` of a pattern of step `n`: `ρ'(d k) = d ρ(k)`, and `ρ' = 0` off
the multiples of `d`. -/
def stepMulPat (d : ℕ) (ρ : ℕ → ℚ) (k : ℕ) : ℚ := if d ∣ k then d * ρ (k / d) else 0

theorem stepMulPat_mul {d : ℕ} (hd : 0 < d) (ρ : ℕ → ℚ) (k : ℕ) :
    stepMulPat d ρ (d * k) = d * ρ k := by
  rw [stepMulPat, ite_eq_left (Dvd.intro k rfl), Nat.mul_div_cancel_left k hd]

/-- The pattern has period `d P`. -/
theorem stepMulPat_periodic {d : ℕ} (hd : 0 < d) {P : ℕ} {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + P) = ρ k) (k : ℕ) : stepMulPat d ρ (k + d * P) = stepMulPat d ρ k := by
  have e1 : d ∣ k + d * P ↔ d ∣ k := (Nat.dvd_add_iff_left (Dvd.intro P rfl)).symm
  have e2 : (k + d * P) / d = k / d + P := Nat.add_mul_div_left k P hd
  simp only [stepMulPat, e1, e2, hρ]

/-- **A series of step `n` is a series of step `n d`.** -/
theorem hasSum_seriesTermBN_step_mul (b n : ℕ) {d : ℕ} (hd : 0 < d) (ρ : ℕ → ℚ) (x : ℝ) :
    HasSum (seriesTermBN b (n * d) (stepMulPat d ρ)) x ↔ HasSum (seriesTermBN b n ρ) x := by
  have hoff : ∀ k, ¬ d ∣ k → seriesTermBN b (n * d) (stepMulPat d ρ) k = 0 := fun k hk => by
    simp [seriesTermBN, stepMulPat, hk]
  rw [← hasSum_mul_left_iff hd hoff]
  have e : (fun k : ℕ => seriesTermBN b (n * d) (stepMulPat d ρ) (d * k)) =
      seriesTermBN b n ρ := by
    funext k
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    rw [seriesTermBN, seriesTermBN, stepMulPat_mul hd, mul_comm n d, Nat.mul_div_mul_left k n hd]
    push_cast
    field_simp
  rw [e]

/-! ## 3. Series of the same step add -/

theorem seriesTermBN_add (b n : ℕ) (ρ σ : ℕ → ℚ) :
    seriesTermBN b n (ρ + σ) = fun k => seriesTermBN b n ρ k + seriesTermBN b n σ k := by
  funext k
  simp only [seriesTermBN, Pi.add_apply]
  push_cast
  ring

/-! ## 4. A series of step `n` is one of Bailey's series -/

/-- **A series of step `n` is one of Bailey's series**: for a pattern `ρ` of period `P` it is
`P(1, b^P, P n, a)` with `a_i = ρ(i) b^(-⌊i/n⌋)`. This is the converse of
`exists_step_of_bailey`. -/
theorem exists_bailey_of_step {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) {P : ℕ} (hP : 0 < P)
    {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + P) = ρ k) {x : ℝ} (h : HasSum (seriesTermBN b n ρ) x) :
    ∃ c : Fin (P * n) → ℚ, HasSum (baileyBlock b P (P * n) c) x := by
  have hN : 0 < P * n := Nat.mul_pos hP hn
  have hb0 : (b : ℚ) ≠ 0 := by
    have : 0 < b := by omega
    positivity
  refine ⟨fun i => ρ ((i : ℕ) + 1) / (b : ℚ) ^ (((i : ℕ) + 1) / n), ?_⟩
  rw [hasSum_bailey_iff hb one_pos hn hN (one_mul _)]
  have e : stepPat b 1 n hN (fun i => ρ ((i : ℕ) + 1) / (b : ℚ) ^ (((i : ℕ) + 1) / n)) = ρ := by
    funext m
    simp only [stepPat, one_dvd, ite_true, Nat.div_one, one_mul, Nat.cast_one]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hb0)]
    exact period_bIdx hN (fun k => periodic_mul hρ n k) m
  rw [e]
  exact h

/-! ## 5. Sums of Bailey's series -/

/-- **The sum of two degree-1 BBP-type series of base `b` is one such series.** -/
theorem exists_bailey_add {b : ℕ} (hb : 2 ≤ b) {B₁ N₁ B₂ N₂ : ℕ} (hB₁ : 0 < B₁) (hN₁ : 0 < N₁)
    (hB₂ : 0 < B₂) (hN₂ : 0 < N₂) (c₁ : Fin N₁ → ℚ) (c₂ : Fin N₂ → ℚ) {x₁ x₂ : ℝ}
    (h₁ : HasSum (baileyBlock b B₁ N₁ c₁) x₁) (h₂ : HasSum (baileyBlock b B₂ N₂ c₂) x₂) :
    ∃ (B' N' : ℕ) (c' : Fin N' → ℚ), 0 < B' ∧ 0 < N' ∧
      HasSum (baileyBlock b B' N' c') (x₁ + x₂) := by
  obtain ⟨P₁, ρ₁, hP₁, hρ₁, hs₁⟩ := exists_step_of_bailey hb hB₁ hN₁ c₁ h₁
  obtain ⟨P₂, ρ₂, hP₂, hρ₂, hs₂⟩ := exists_step_of_bailey hb hB₂ hN₂ c₂ h₂
  have hn₁ : 0 < N₁ / Nat.gcd B₁ N₁ :=
    Nat.div_pos (Nat.le_of_dvd hN₁ (Nat.gcd_dvd_right _ _)) (Nat.gcd_pos_of_pos_right _ hN₁)
  have hn₂ : 0 < N₂ / Nat.gcd B₂ N₂ :=
    Nat.div_pos (Nat.le_of_dvd hN₂ (Nat.gcd_dvd_right _ _)) (Nat.gcd_pos_of_pos_right _ hN₂)
  generalize N₁ / Nat.gcd B₁ N₁ = n₁ at hs₁ hn₁
  generalize N₂ / Nat.gcd B₂ N₂ = n₂ at hs₂ hn₂
  have hs₁' : HasSum (seriesTermBN b (n₁ * n₂) (stepMulPat n₂ ρ₁)) x₁ :=
    (hasSum_seriesTermBN_step_mul b n₁ hn₂ ρ₁ x₁).2 hs₁
  have hs₂' : HasSum (seriesTermBN b (n₁ * n₂) (stepMulPat n₁ ρ₂)) x₂ := by
    rw [mul_comm]
    exact (hasSum_seriesTermBN_step_mul b n₂ hn₁ ρ₂ x₂).2 hs₂
  have hsum := hs₁'.add hs₂'
  rw [← seriesTermBN_add] at hsum
  have hper : ∀ k, (stepMulPat n₂ ρ₁ + stepMulPat n₁ ρ₂) (k + n₂ * P₁ * (n₁ * P₂)) =
      (stepMulPat n₂ ρ₁ + stepMulPat n₁ ρ₂) k := by
    intro k
    have e₁ := periodic_mul (stepMulPat_periodic hn₂ hρ₁) (n₁ * P₂) k
    have e₂ := periodic_mul (stepMulPat_periodic hn₁ hρ₂) (n₂ * P₁) k
    rw [mul_comm (n₁ * P₂) (n₂ * P₁)] at e₂
    simp only [Pi.add_apply, e₁, e₂]
  have hP : 0 < n₂ * P₁ * (n₁ * P₂) := by positivity
  obtain ⟨c', hc'⟩ := exists_bailey_of_step hb (Nat.mul_pos hn₁ hn₂) hP hper hsum
  exact ⟨_, _, c', hP, Nat.mul_pos hP (Nat.mul_pos hn₁ hn₂), hc'⟩

/-- **A finite sum of degree-1 BBP-type series of base `b` is one such series.** -/
theorem exists_bailey_of_sum {b : ℕ} (hb : 2 ≤ b) {ι : Type*} (s : Finset ι) (B N : ι → ℕ)
    (hB : ∀ i ∈ s, 0 < B i) (hN : ∀ i ∈ s, 0 < N i) (c : ∀ i, Fin (N i) → ℚ) (x : ι → ℝ)
    (hx : ∀ i ∈ s, HasSum (baileyBlock b (B i) (N i) (c i)) (x i)) :
    ∃ (B' N' : ℕ) (c' : Fin N' → ℚ), 0 < B' ∧ 0 < N' ∧
      HasSum (baileyBlock b B' N' c') (∑ i ∈ s, x i) := by
  refine Finset.sum_induction x (fun y => ∃ (B' N' : ℕ) (c' : Fin N' → ℚ), 0 < B' ∧ 0 < N' ∧
    HasSum (baileyBlock b B' N' c') y) ?_ ?_ ?_
  · rintro y z ⟨B₁, N₁, c₁, hB₁, hN₁, h₁⟩ ⟨B₂, N₂, c₂, hB₂, hN₂, h₂⟩
    exact exists_bailey_add hb hB₁ hN₁ hB₂ hN₂ c₁ c₂ h₁ h₂
  · refine ⟨1, 1, 0, one_pos, one_pos, ?_⟩
    rw [baileyBlock_zero]
    exact hasSum_zero
  · exact fun i hi => ⟨B i, N i, c i, hB i hi, hN i hi, hx i hi⟩

/-! ## 6. No combination is a rational multiple of `π` -/

/-- **No combination of degree-1 BBP-type series of a base that is not a power of 2 is a
non-zero rational multiple of `π`.** -/
theorem no_pi_bailey_sum {b : ℕ} (hb : 2 ≤ b) (h2 : ∀ k : ℕ, b ≠ 2 ^ k) {ι : Type*}
    (s : Finset ι) (B N : ι → ℕ) (hB : ∀ i ∈ s, 0 < B i) (hN : ∀ i ∈ s, 0 < N i)
    (c : ∀ i, Fin (N i) → ℚ) (x : ι → ℝ)
    (hx : ∀ i ∈ s, HasSum (baileyBlock b (B i) (N i) (c i)) (x i)) {q : ℚ}
    (h : ∑ i ∈ s, x i = (q : ℝ) * Real.pi) : q = 0 := by
  obtain ⟨B', N', c', hB', hN', h'⟩ := exists_bailey_of_sum hb s B N hB hN c x hx
  rw [h] at h'
  exact no_pi_bailey hb h2 hB' hN' c' h'

/-- The same with the rational coefficients `r i` of the combination written out. -/
theorem no_pi_bailey_comb {b : ℕ} (hb : 2 ≤ b) (h2 : ∀ k : ℕ, b ≠ 2 ^ k) {ι : Type*}
    (s : Finset ι) (B N : ι → ℕ) (hB : ∀ i ∈ s, 0 < B i) (hN : ∀ i ∈ s, 0 < N i)
    (c : ∀ i, Fin (N i) → ℚ) (x : ι → ℝ)
    (hx : ∀ i ∈ s, HasSum (baileyBlock b (B i) (N i) (c i)) (x i)) (r : ι → ℚ) {q : ℚ}
    (h : ∑ i ∈ s, (r i : ℝ) * x i = (q : ℝ) * Real.pi) : q = 0 :=
  no_pi_bailey_sum hb h2 s B N hB hN (fun i => r i • c i) (fun i => (r i : ℝ) * x i)
    (fun i hi => hasSum_baileyBlock_smul (r i) (hx i hi)) h

/-- The series `L(1, b^m, n, j) = ∑_k b^(-m k) / (n k + j)` with `1 ≤ j ≤ n` is Bailey's
series `P(1, b^m, n, e_j)`: the coefficient vector is 1 at the place `j` and 0 elsewhere. -/
theorem baileyBlock_unit (b m : ℕ) {n j : ℕ} (hj : 0 < j) (hjn : j ≤ n) (k : ℕ) :
    baileyBlock b m n (fun t => if (t : ℕ) + 1 = j then 1 else 0) k =
      1 / (b : ℝ) ^ (m * k) / ((n * k + j : ℕ) : ℝ) := by
  have e1 : j - 1 + 1 = j := by omega
  rw [baileyBlock, Finset.sum_eq_single (⟨j - 1, by omega⟩ : Fin n)]
  · simp [e1, add_assoc]
  · intro t _ hne
    have hne' : (t : ℕ) + 1 ≠ j := fun h => hne (Fin.ext (by simp only; omega))
    simp [hne']
  · exact fun h => absurd (Finset.mem_univ _) h

/-- **The question of Borwein, Borwein and Galway (2004, Comment 10), for the bases that are
not powers of 2.** Let `b ≥ 2` be an integer that is not a power of 2. No rational linear
combination of series `L(1, b^m, n, j) = ∑_k b^(-m k) / (n k + j)`, with any exponents
`m ≥ 1`, any lengths `n` and any `1 ≤ j ≤ n`, is a non-zero rational multiple of `π`. -/
theorem no_pi_L_comb {b : ℕ} (hb : 2 ≤ b) (h2 : ∀ k : ℕ, b ≠ 2 ^ k) {ι : Type*} (s : Finset ι)
    (m n j : ι → ℕ) (hm : ∀ i ∈ s, 0 < m i) (hj : ∀ i ∈ s, 0 < j i) (hjn : ∀ i ∈ s, j i ≤ n i)
    (r : ι → ℚ) (x : ι → ℝ)
    (hx : ∀ i ∈ s,
      HasSum (fun k : ℕ => 1 / (b : ℝ) ^ (m i * k) / ((n i * k + j i : ℕ) : ℝ)) (x i))
    {q : ℚ} (h : ∑ i ∈ s, (r i : ℝ) * x i = (q : ℝ) * Real.pi) : q = 0 := by
  refine no_pi_bailey_comb hb h2 s m n hm (fun i hi => (hj i hi).trans_le (hjn i hi))
    (fun i t => if (t : ℕ) + 1 = j i then 1 else 0) x (fun i hi => ?_) r h
  have e : baileyBlock b (m i) (n i) (fun t => if (t : ℕ) + 1 = j i then 1 else 0) =
      fun k : ℕ => 1 / (b : ℝ) ^ (m i * k) / ((n i * k + j i : ℕ) : ℝ) :=
    funext fun k => baileyBlock_unit b (m i) (hj i hi) (hjn i hi) k
  rw [e]
  exact hx i hi

/-- **Logarithms of numbers built from the primes of the base, for combinations.** Let `b ≥ 2`
be neither a power of 2 nor a power of 3, and `y ≠ 1` a positive rational all of whose prime
factors divide `b`. No finite sum of degree-1 BBP-type series of base `b` equals
`q π + q' log y` with `q, q'` rational, `q' ≠ 0`. -/
theorem no_log_bailey_sum {b : ℕ} (hb : 2 ≤ b) (h2 : ∀ k : ℕ, b ≠ 2 ^ k)
    (h3 : ∀ k : ℕ, b ≠ 3 ^ k) {ι : Type*} (s : Finset ι) (B N : ι → ℕ)
    (hB : ∀ i ∈ s, 0 < B i) (hN : ∀ i ∈ s, 0 < N i) (c : ∀ i, Fin (N i) → ℚ) (x : ι → ℝ)
    (hx : ∀ i ∈ s, HasSum (baileyBlock b (B i) (N i) (c i)) (x i)) {q q' : ℚ} (hq' : q' ≠ 0)
    {y : ℚ} (hy : 0 < y) (hy1 : y ≠ 1) (hp : ∀ p : ℕ, p.Prime → padicValRat p y ≠ 0 → p ∣ b) :
    ∑ i ∈ s, x i ≠ q * Real.pi + q' * Real.log y := by
  intro h
  obtain ⟨B', N', c', hB', hN', h'⟩ := exists_bailey_of_sum hb s B N hB hN c x hx
  rw [h] at h'
  exact no_log_bailey hb h2 h3 hB' hN' c' hq' hy hy1 hp h'

end BaseB

end PiFormula
