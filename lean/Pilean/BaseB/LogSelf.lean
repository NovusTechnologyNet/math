import Pilean.BaseB.BaileyForm

/-!
# The logarithm of the base, in a base that is a power of 2 or of 3

In a base `b = 2^e` or `b = 3^e` (`e ≥ 1`) the number `log b` has a degree-1 BBP-type formula
in Bailey's notation, `log b = P(1, b^B, N, c) = ∑_{j ≥ 0} b^(-Bj) ∑_{i=1}^N c_i / (Nj + i)`
with rational `c_i`.

The two formulas of the bases 2 and 3:

* `hasSum_log_two`: `log 2 = ∑_j 2^(-j) (1/2) / (j + 1)`, that is `log 2 = ∑_{k ≥ 1} 2^(-k) / k`;
* `hasSum_log_three`: `log 3 = ∑_j 9^(-j) (1 / (2j + 1) + (1/9) / (2j + 2))`. It comes from
  `log 3 = 3 log (3/2) - log (9/8) = 3 ∑_{k ≥ 1} 3^(-k) / k - ∑_{k ≥ 1} 9^(-k) / k`, which is
  the series of step 1 `∑_{k ≥ 1} g(k) 3^(-k) / k` with `g(k) = 3` for odd `k` and `g(k) = 1`
  for even `k`.

Both are series of step 1, `∑_{k ≥ 1} g(k) a^(-k) / k` with `g` periodic. Such a series can be
cut into blocks of any length `N` that is a period of `g`
(`hasSum_baileyBlock_step_one`): block `j` is `a^(-Nj) ∑_{i=1}^N g(i) a^(-i) / (Nj + i)`. With
`N = e` in base 2 and `N = 2e` in base 3, and all coefficients multiplied by `e`:

* `hasSum_log_two_pow`: `log (2^e) = P(1, 2^e, e, c)` with `c_i = e / 2^i`;
* `hasSum_log_three_pow`: `log (3^e) = P(1, (3^e)^2, 2e, c)` with `c_i = 3e / 3^i` for odd `i`
  and `c_i = e / 3^i` for even `i`;
* `exists_bailey_log_two_pow`, `exists_bailey_log_three_pow`: the two existence statements.
-/

namespace PiFormula

namespace BaseB

/-! ## 1. Series of step 1, cut into blocks -/

/-- `∑_{k ≥ 1} x^k / k = -log (1 - x)` for `|x| < 1`; the term at `k = 0` is `0`. -/
private theorem hasSum_pow_div_nat {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => x ^ k / (k : ℝ)) (-Real.log (1 - x)) := by
  rw [← hasSum_nat_add_iff' 1]
  simpa using Real.hasSum_pow_div_log_of_abs_lt_one hx

/-- Bailey's series in base `a^e` with exponent `B` is the series in base `a` with exponent
`e B`. -/
private theorem baileyBlock_base_pow (a e B N : ℕ) (c : Fin N → ℚ) :
    baileyBlock (a ^ e) B N c = baileyBlock a (e * B) N c := by
  funext j
  simp only [baileyBlock, Nat.cast_pow, ← pow_mul, mul_assoc]

/-- **A series of step 1 in blocks.** If `g` has period `N`, the series
`∑_{k ≥ 1} g(k) a^(-k) / k` is Bailey's `P(1, a^N, N, c)` with `c_i = g(i) a^(-i)`. -/
theorem hasSum_baileyBlock_step_one (a : ℕ) {N : ℕ} (hN : 0 < N) {g : ℕ → ℚ}
    (hg : ∀ k, g (k + N) = g k) {S : ℝ}
    (h : HasSum (fun k : ℕ => (g k : ℝ) / (a : ℝ) ^ k / (k : ℝ)) S) :
    HasSum (baileyBlock a N N fun i => g ((i : ℕ) + 1) / (a : ℚ) ^ ((i : ℕ) + 1)) S := by
  have h' := (hasSum_blocks_iff hN h.summable (by simp) S).2 h
  have e : (baileyBlock a N N fun i => g ((i : ℕ) + 1) / (a : ℚ) ^ ((i : ℕ) + 1)) =
      fun j : ℕ => ∑ i : Fin N,
        (fun k : ℕ => (g k : ℝ) / (a : ℝ) ^ k / (k : ℝ)) (N * j + i + 1) := by
    funext j
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : N * j + (i : ℕ) + 1 = (i : ℕ) + 1 + N * j := by ring
    have e2 : g ((i : ℕ) + 1 + N * j) = g ((i : ℕ) + 1) := periodic_mul hg j _
    change _ = (g (N * j + (i : ℕ) + 1) : ℝ) / (a : ℝ) ^ (N * j + (i : ℕ) + 1) / _
    rw [e1, e2, pow_add, ← div_div]
    push_cast
    rfl
  rw [e]
  exact h'

/-! ## 2. Base 2 -/

/-- `e log 2 = P(1, 2^e, e, c)` with `c_i = e / 2^i`. -/
theorem hasSum_log_two_mul {e : ℕ} (he : 0 < e) :
    HasSum (baileyBlock 2 e e fun i => (e : ℚ) / 2 ^ ((i : ℕ) + 1)) (e * Real.log 2) := by
  have h2 : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ k / (k : ℝ)) (Real.log 2) := by
    have h := hasSum_pow_div_nat (x := 1 / 2) (by rw [abs_of_pos] <;> norm_num)
    have e1 : -Real.log (1 - 1 / 2) = Real.log 2 := by
      rw [← Real.log_inv]
      norm_num
    rwa [e1] at h
  have h3 : HasSum (fun k : ℕ => (((fun _ : ℕ => (e : ℚ)) k : ℚ) : ℝ) / ((2 : ℕ) : ℝ) ^ k /
      (k : ℝ)) (e * Real.log 2) := by
    have e1 : (fun k : ℕ => (((fun _ : ℕ => (e : ℚ)) k : ℚ) : ℝ) / ((2 : ℕ) : ℝ) ^ k /
        (k : ℝ)) = fun k : ℕ => (e : ℝ) * ((1 / 2 : ℝ) ^ k / (k : ℝ)) := by
      funext k
      rw [one_div_pow]
      push_cast
      ring
    rw [e1]
    exact h2.mul_left _
  have h4 := hasSum_baileyBlock_step_one 2 he (g := fun _ => (e : ℚ)) (fun _ => rfl) h3
  simpa only [Nat.cast_ofNat] using h4

/-- **The logarithm of the base `2^e`**: `log (2^e) = ∑_j (2^e)^(-j) ∑_{i=1}^e c_i / (ej + i)`
with `c_i = e / 2^i`. -/
theorem hasSum_log_two_pow {e : ℕ} (he : 0 < e) :
    HasSum (baileyBlock (2 ^ e) 1 e fun i => (e : ℚ) / 2 ^ ((i : ℕ) + 1))
      (Real.log ((2 ^ e : ℕ) : ℝ)) := by
  rw [baileyBlock_base_pow, mul_one, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  exact hasSum_log_two_mul he

/-- **`log 2 = ∑_{j ≥ 0} 2^(-j) (1/2) / (j + 1)`**, that is `log 2 = ∑_{k ≥ 1} 2^(-k) / k`. -/
theorem hasSum_log_two : HasSum (baileyBlock 2 1 1 ![1 / 2]) (Real.log 2) := by
  have h := hasSum_log_two_mul one_pos
  have e : (fun i : Fin 1 => ((1 : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1)) = ![1 / 2] := by
    funext i
    fin_cases i
    norm_num
  rwa [e, Nat.cast_one, one_mul] at h

/-! ## 3. Base 3 -/

/-- `log 3 = ∑_{k ≥ 1} g(k) 3^(-k) / k` with `g(k) = 1` for even `k` and `g(k) = 3` for odd
`k`: this is `3 log (3/2) - log (9/8)`. -/
private theorem hasSum_log_three_step_one :
    HasSum (fun k : ℕ => (if Even k then 1 else 3 : ℝ) * ((1 / 3 : ℝ) ^ k / (k : ℝ)))
      (Real.log 3) := by
  have hA := (hasSum_pow_div_nat (x := 1 / 3) (by rw [abs_of_pos] <;> norm_num)).mul_left 3
  have hC := hasSum_pow_div_nat (x := 1 / 9) (by rw [abs_of_pos] <;> norm_num)
  have hG : HasSum (fun k : ℕ => if 2 ∣ k then 2 * ((1 / 3 : ℝ) ^ k / (k : ℝ)) else 0)
      (-Real.log (1 - 1 / 9)) := by
    rw [← hasSum_mul_left_iff two_pos (fun k hk => ite_eq_right hk)]
    have e : (fun k : ℕ => if 2 ∣ 2 * k then 2 * ((1 / 3 : ℝ) ^ (2 * k) / ((2 * k : ℕ) : ℝ))
        else 0) = fun k : ℕ => (1 / 9 : ℝ) ^ k / (k : ℝ) := by
      funext k
      have e9 : (1 / 3 : ℝ) ^ 2 = 1 / 9 := by norm_num
      rw [ite_eq_left (dvd_mul_right 2 k), pow_mul, e9]
      push_cast
      ring
    rw [e]
    exact hC
  have hv : 3 * -Real.log (1 - 1 / 3) - -Real.log (1 - 1 / 9) = Real.log 3 := by
    have e1 : (1 - 1 / 3 : ℝ) = 2 / 3 := by norm_num
    have e2 : (1 - 1 / 9 : ℝ) = 2 ^ 3 / 3 ^ 2 := by norm_num
    rw [e1, e2, Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h := hA.sub hG
  rw [hv] at h
  refine h.congr_fun fun k => ?_
  by_cases hk : Even k
  · rw [ite_eq_left hk, ite_eq_left (even_iff_two_dvd.1 hk)]
    ring
  · rw [ite_eq_right hk, ite_eq_right fun h2 => hk (even_iff_two_dvd.2 h2)]
    ring

/-- `e log 3 = P(1, 3^(2e), 2e, c)` with `c_i = 3e / 3^i` for odd `i` and `c_i = e / 3^i` for
even `i`. -/
theorem hasSum_log_three_mul {e : ℕ} (he : 0 < e) :
    HasSum (baileyBlock 3 (2 * e) (2 * e) fun i =>
      (e : ℚ) * (if Even ((i : ℕ) + 1) then 1 else 3) / 3 ^ ((i : ℕ) + 1))
      (e * Real.log 3) := by
  have hg : ∀ k : ℕ, (fun k : ℕ => (e : ℚ) * (if Even k then 1 else 3)) (k + 2 * e) =
      (fun k : ℕ => (e : ℚ) * (if Even k then 1 else 3)) k := fun k => by
    simp only [Nat.even_add, even_two_mul, iff_true]
  have h3 : HasSum (fun k : ℕ => (((fun k : ℕ => (e : ℚ) * (if Even k then 1 else 3)) k : ℚ) : ℝ)
      / ((3 : ℕ) : ℝ) ^ k / (k : ℝ)) (e * Real.log 3) := by
    have e1 : (fun k : ℕ => (((fun k : ℕ => (e : ℚ) * (if Even k then 1 else 3)) k : ℚ) : ℝ)
        / ((3 : ℕ) : ℝ) ^ k / (k : ℝ)) = fun k : ℕ =>
        (e : ℝ) * ((if Even k then 1 else 3 : ℝ) * ((1 / 3 : ℝ) ^ k / (k : ℝ))) := by
      funext k
      rw [one_div_pow]
      beta_reduce
      split_ifs <;> push_cast <;> ring
    rw [e1]
    exact hasSum_log_three_step_one.mul_left _
  have h4 := hasSum_baileyBlock_step_one 3 (Nat.mul_pos two_pos he) hg h3
  simpa only [Nat.cast_ofNat] using h4

/-- **The logarithm of the base `3^e`**:
`log (3^e) = ∑_j (3^e)^(-2j) ∑_{i=1}^{2e} c_i / (2ej + i)` with `c_i = 3e / 3^i` for odd `i`
and `c_i = e / 3^i` for even `i`. -/
theorem hasSum_log_three_pow {e : ℕ} (he : 0 < e) :
    HasSum (baileyBlock (3 ^ e) 2 (2 * e) fun i =>
      (e : ℚ) * (if Even ((i : ℕ) + 1) then 1 else 3) / 3 ^ ((i : ℕ) + 1))
      (Real.log ((3 ^ e : ℕ) : ℝ)) := by
  rw [baileyBlock_base_pow, mul_comm e 2, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  exact hasSum_log_three_mul he

/-- **`log 3 = ∑_{j ≥ 0} 9^(-j) (1 / (2j + 1) + (1/9) / (2j + 2))`.** -/
theorem hasSum_log_three : HasSum (baileyBlock 3 2 2 ![1, 1 / 9]) (Real.log 3) := by
  have h := hasSum_log_three_mul one_pos
  have e : (fun i : Fin (2 * 1) =>
      ((1 : ℕ) : ℚ) * (if Even ((i : ℕ) + 1) then 1 else 3) / 3 ^ ((i : ℕ) + 1)) =
      ![1, 1 / 9] := by
    funext i
    fin_cases i <;> norm_num
  rwa [e, Nat.cast_one, one_mul] at h

/-! ## 4. The existence statements -/

/-- **In a base `2^e`, `e ≥ 1`, the logarithm of the base has a degree-1 BBP-type formula.** -/
theorem exists_bailey_log_two_pow {e : ℕ} (he : 0 < e) :
    ∃ (B N : ℕ) (c : Fin N → ℚ), 0 < B ∧ 0 < N ∧
      HasSum (baileyBlock (2 ^ e) B N c) (Real.log ((2 ^ e : ℕ) : ℝ)) :=
  ⟨1, e, _, one_pos, he, hasSum_log_two_pow he⟩

/-- **In a base `3^e`, `e ≥ 1`, the logarithm of the base has a degree-1 BBP-type formula.** -/
theorem exists_bailey_log_three_pow {e : ℕ} (he : 0 < e) :
    ∃ (B N : ℕ) (c : Fin N → ℚ), 0 < B ∧ 0 < N ∧
      HasSum (baileyBlock (3 ^ e) B N c) (Real.log ((3 ^ e : ℕ) : ℝ)) :=
  ⟨2, 2 * e, _, two_pos, Nat.mul_pos two_pos he, hasSum_log_three_pow he⟩

end BaseB

end PiFormula
