/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Base3.Optimum
public import Pilean.PiFormula.BaileySums

/-!
# Base 3 in Bailey's notation

Bailey's notation is `P(s, b, n, A) = ∑_{j ≥ 0} b^(-j) ∑_{i=1}^n a_i / (nj + i)^s`. Here `s = 1`
and `b = 3^B`. This file restates the results of `Dimension.lean` and `Optimum.lean` in that
notation, as `PiFormula/BaileySums.lean` does for base 2, so that they can be compared with
the formulas in print.

**The bridge** (no Baker's theorem). `baileyBlock3 B n a j` is the `j`-th block of
`P(1, 3^B, n, A)`, written exactly as Bailey's double sum; `a i` (`i : Fin n`) is Bailey's
`a_{i+1}`. With `k = nj + i + 1`:

* if `n = 2B`, the vector `a` corresponds to the pattern `ρ(k) = a_i 3^⌊(i+1)/2⌋` of period
  `n` (`pat3F2`), and Bailey's sum is the series of `ρ` (`hasSum_bailey3_F2`);
* if `n = B`, it corresponds to the pattern supported on even `k` with
  `ρ(2k) = 2 a_i 3^(i+1)`, of period `2n` (`pat3F1`, `hasSum_bailey3_F1`).

**The identities in print**, with no hypothesis. The coefficient vectors and their numbers
in Bailey's compendium are taken from the note (Part V); the sources were not read again for
this file. With `G`, `Z₁`, `Z₂` the three patterns of `Dimension.lean`:

* `relation130`: `P(1, 729, 12, (0, 81, -162, 0, 27, 36, 0, 9, 6, 4, -1, 0)) = 0`
  (pattern `243 Z₁`);
* `relation131`: `P(1, 729, 12, (243, -324, -162, -81, 0, -36, -9, 0, 6, -1, 0, 0)) = 0`
  (pattern `243 (Z₂ - Z₁)`);
* `relation_adegoke`: `P(1, 729, 12, (243, -243, -324, -81, 27, 0, -9, 9, 12, 3, -1, 0)) = 0`
  (pattern `243 Z₂`); its vector is the sum of the two above (`relAdegoke_eq`);
* `broadhurst_formula` (formula 69):
  `P(1, 729, 12, (81, -54, 0, -9, 0, -12, -3, -2, 0, -1, 0, 0)) = 9 π√3`
  (pattern `9 (G - 9 Z₁ + 3 Z₂)`);
* `gregory_formula`, `gregory729_formula`: the Gregory series, as
  `P(1, 9, 4, (6, 0, -2, 0)) = π√3` and as
  `P(1, 729, 12, (486, 0, -162, 0, 54, 0, -18, 0, 6, 0, -2, 0)) = 81 π√3`;
* `second_formula`: `P(1, 729, 12, (0, 162, 162, 54, 0, 0, 0, -6, -6, -2, 0, 0)) = 27 π√3`,
  the second formula with 6 terms (pattern `27 rhoSecond`); its vector is 3 times that of
  formula 69 minus that of relation 131 (`second729_eq`).

**From Baker's theorem:**

* `bailey3_count_F2`: `P(1, 3^B, 2B, ·)` has 2 independent zero relations if `6 ∣ B`, and
  none otherwise, for every `B ≥ 1`;
* `bailey3_count_F1`: `P(1, 3^B, B, ·)` has no zero relation, for every `B ≥ 1`; more is
  true: `P(1, 3^B, B, A)` is an algebraic multiple of `π` only for `A = 0`
  (`bailey3_F1_eq_zero`);
* `bailey3_729_coords`, `bailey3_729_zero_iff`: every `A` with `P(1, 729, 12, A)` an algebraic
  multiple of `π` is a rational combination of formula 69 and relations 130 and 131, and the
  zero relations are exactly the combinations of relations 130 and 131;
* `bailey3_pi_F2`: for every `B ≥ 1`, if `P(1, 3^B, 2B, A) = γ π` with `γ` algebraic, then
  `γ` is a rational multiple of `√3`, and if `γ ≠ 0` at least `B` of the `2B` entries of `A`
  are non-zero. The Gregory series and the second formula have exactly 6 of 12, and
  Broadhurst's formula has 7 (`entryCount_printed`).

The theorems of the second list take `BakerTheorem` as a hypothesis, as `Dimension.lean` does;
`PiFormula.bakerTheorem` (`PiFormula/Unconditional.lean`) discharges it.
-/

@[expose] public section

namespace PiFormula

namespace Base3

/-! ## 1. Convergence -/

/-- The series of a periodic rational pattern converges. -/
theorem summable_seriesTerm3 {n : ℕ} (hn : 0 < n) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + n) = ρ k) :
    Summable (seriesTerm3 ρ) := by
  have h4 : ∀ k, ρ (k + 4 * n) = ρ k := fun k => by
    have h := periodic_mul hρ 4 k
    rwa [mul_comm] at h
  have h := (series_eq_logs3 (N := 4 * n) (by positivity) (Dvd.intro n rfl) h4).summable
  have e : (fun k : ℕ => (ρ k : ℂ) / 3 ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTerm3 ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTerm3]
  rw [e] at h
  exact Complex.summable_ofReal.1 h

theorem seriesTerm3_at_zero (ρ : ℕ → ℚ) : seriesTerm3 ρ 0 = 0 := by simp [seriesTerm3]

/-- Two patterns of period `n` that agree on `0, ..., n - 1` are equal. -/
theorem eq_of_lt_period {n : ℕ} (hn : 0 < n) {f g : ℕ → ℚ} (hf : ∀ k, f (k + n) = f k)
    (hg : ∀ k, g (k + n) = g k) (h : ∀ j < n, f j = g j) (k : ℕ) : f k = g k := by
  rw [← period_mod hf k, ← period_mod hg k]
  exact h _ (Nat.mod_lt _ hn)

/-! ## 2. Bailey's sums -/

/-- The `j`-th block of Bailey's sum `P(1, 3^B, n, A) = ∑_j 3^(-Bj) ∑_{i=1}^n a_i / (nj + i)`.
Here `a i` (`i : Fin n`, so `i = 0, ..., n-1`) is Bailey's `a_{i+1}`. -/
noncomputable def baileyBlock3 (B n : ℕ) (a : Fin n → ℚ) (j : ℕ) : ℝ :=
  ∑ i : Fin n, (a i : ℝ) / 3 ^ (B * j) / ((n * j + i + 1 : ℕ) : ℝ)

theorem baileyBlock3_add (B n : ℕ) (a b : Fin n → ℚ) :
    baileyBlock3 B n (a + b) = fun j => baileyBlock3 B n a j + baileyBlock3 B n b j := by
  funext j
  simp only [baileyBlock3, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

theorem baileyBlock3_smul (B n : ℕ) (c : ℚ) (a : Fin n → ℚ) :
    baileyBlock3 B n (c • a) = fun j => (c : ℝ) * baileyBlock3 B n a j := by
  funext j
  simp only [baileyBlock3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- **Bailey's zero relations in base 3**: the coefficient vectors `A` with
`P(1, 3^B, n, A) = 0`. -/
def baileyZero3 (B n : ℕ) : Submodule ℚ (Fin n → ℚ) where
  carrier := {a | HasSum (baileyBlock3 B n a) 0}
  add_mem' := by
    intro a b ha hb
    have h := HasSum.add ha hb
    rw [add_zero] at h
    change HasSum (baileyBlock3 B n (a + b)) 0
    rw [baileyBlock3_add]
    exact h
  zero_mem' := by
    have e : baileyBlock3 B n 0 = fun _ => 0 := by
      funext j
      simp [baileyBlock3]
    change HasSum (baileyBlock3 B n 0) 0
    rw [e]
    exact hasSum_zero
  smul_mem' := by
    intro c a ha
    have h := HasSum.mul_left (c : ℝ) ha
    rw [mul_zero] at h
    change HasSum (baileyBlock3 B n (c • a)) 0
    rw [baileyBlock3_smul]
    exact h

/-! ## 3. The sums with `n = 2B` -/

/-- The pattern of a coefficient vector, for `n = 2B`: `ρ(nj + i + 1) = a_i 3^⌊(i+1)/2⌋`. -/
def pat3F2 {n : ℕ} (hn : 0 < n) : (Fin n → ℚ) →ₗ[ℚ] (ℕ → ℚ) where
  toFun a k := a (bIdx hn k) * 3 ^ (((bIdx hn k : ℕ) + 1) / 2)
  map_add' a b := by
    funext k
    simp only [Pi.add_apply]
    ring
  map_smul' c a := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem pat3F2_apply {n : ℕ} (hn : 0 < n) (a : Fin n → ℚ) (k : ℕ) :
    pat3F2 hn a k = a (bIdx hn k) * 3 ^ (((bIdx hn k : ℕ) + 1) / 2) := rfl

theorem pat3F2_periodic {n : ℕ} (hn : 0 < n) (a : Fin n → ℚ) (k : ℕ) :
    pat3F2 hn a (k + n) = pat3F2 hn a k := by
  simp only [pat3F2_apply, bIdx_add]

theorem pat3F2_injective {n : ℕ} (hn : 0 < n) : Function.Injective (pat3F2 hn) := by
  intro a b hab
  funext i
  have h := congrFun hab ((i : ℕ) + 1)
  simp only [pat3F2_apply, bIdx_succ] at h
  exact mul_right_cancel₀ (pow_ne_zero _ (by norm_num)) h

theorem range_pat3F2 {n : ℕ} (hn : 0 < n) : LinearMap.range (pat3F2 hn) = periodSpace n := by
  apply le_antisymm
  · intro ρ hρ
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.1 hρ
    exact fun k => pat3F2_periodic hn a k
  · intro ρ hρ
    refine LinearMap.mem_range.2
      ⟨fun i => ρ ((i : ℕ) + 1) / 3 ^ (((i : ℕ) + 1) / 2), ?_⟩
    funext k
    have h3 : (3 : ℚ) ^ (((bIdx hn k : ℕ) + 1) / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
    simp only [pat3F2_apply]
    rw [div_mul_cancel₀ _ h3]
    exact period_bIdx hn hρ k

/-- The term of the pattern at `k = 2Bj + i + 1` is Bailey's term. -/
theorem seriesTerm3_pat3F2 {B : ℕ} (hB : 0 < B) (a : Fin (2 * B) → ℚ) (j : ℕ)
    (i : Fin (2 * B)) :
    seriesTerm3 (pat3F2 (Nat.mul_pos two_pos hB) a) (2 * B * j + i + 1) =
      (a i : ℝ) / 3 ^ (B * j) / ((2 * B * j + i + 1 : ℕ) : ℝ) := by
  have e : (2 * B * j + (i : ℕ) + 1) / 2 = B * j + ((i : ℕ) + 1) / 2 := by
    rw [show 2 * B * j + (i : ℕ) + 1 = 2 * (B * j) + ((i : ℕ) + 1) by ring]
    exact Nat.mul_add_div (by norm_num) _ _
  rw [seriesTerm3, pat3F2_apply, bIdx_block, e, pow_add]
  have h3 : (3 : ℝ) ^ (((i : ℕ) + 1) / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast
  rw [mul_div_mul_right _ _ h3]

/-- **Bailey's sum `P(1, 3^B, 2B, A)` is the series of the pattern.** -/
theorem hasSum_bailey3_F2 {B : ℕ} (hB : 0 < B) (a : Fin (2 * B) → ℚ) (S : ℝ) :
    HasSum (baileyBlock3 B (2 * B) a) S ↔
      HasSum (seriesTerm3 (pat3F2 (Nat.mul_pos two_pos hB) a)) S := by
  have hn : 0 < 2 * B := Nat.mul_pos two_pos hB
  have hs := summable_seriesTerm3 hn (pat3F2_periodic hn a)
  rw [← hasSum_blocks_iff hn hs (seriesTerm3_at_zero _) S]
  have e : baileyBlock3 B (2 * B) a =
      fun j : ℕ => ∑ i : Fin (2 * B), seriesTerm3 (pat3F2 hn a) (2 * B * j + i + 1) := by
    funext j
    exact Finset.sum_congr rfl fun i _ => (seriesTerm3_pat3F2 hB a j i).symm
  rw [e]

/-- Bailey's zero relations with `n = 2B` are the zero relations of period `2B`. -/
theorem baileyZero3_F2 {B : ℕ} (hB : 0 < B) :
    baileyZero3 B (2 * B) = (zeroSpace3 (2 * B)).comap (pat3F2 (Nat.mul_pos two_pos hB)) := by
  have hn : 0 < 2 * B := Nat.mul_pos two_pos hB
  ext a
  rw [Submodule.mem_comap]
  constructor
  · intro h
    exact ⟨fun k => pat3F2_periodic hn a k, (hasSum_bailey3_F2 hB a 0).1 h⟩
  · intro h
    exact (hasSum_bailey3_F2 hB a 0).2 h.2

/-- The number of Bailey's zero relations with `n = 2B` (no Baker's theorem). -/
theorem finrank_baileyZero3_F2 {B : ℕ} (hB : 0 < B) :
    Module.finrank ℚ (baileyZero3 B (2 * B)) = Module.finrank ℚ (zeroSpace3 (2 * B)) := by
  have hn : 0 < 2 * B := Nat.mul_pos two_pos hB
  rw [baileyZero3_F2 hB]
  refine finrank_comap_of_le _ (pat3F2_injective hn) ?_
  rw [range_pat3F2 hn]
  exact fun ρ h => h.1

/-! ## 4. The sums with `n = B` -/

/-- The pattern of a coefficient vector, for `n = B`: supported on even `k`, with
`ρ(2(nj + i + 1)) = 2 a_i 3^(i+1)`. -/
def pat3F1 {n : ℕ} (hn : 0 < n) : (Fin n → ℚ) →ₗ[ℚ] (ℕ → ℚ) where
  toFun a k :=
    if k % 2 = 0 then a (bIdx hn (k / 2)) * (2 * 3 ^ ((bIdx hn (k / 2) : ℕ) + 1)) else 0
  map_add' a b := by
    funext k
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c a := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem pat3F1_apply {n : ℕ} (hn : 0 < n) (a : Fin n → ℚ) (k : ℕ) :
    pat3F1 hn a k =
      if k % 2 = 0 then a (bIdx hn (k / 2)) * (2 * 3 ^ ((bIdx hn (k / 2) : ℕ) + 1)) else 0 :=
  rfl

theorem pat3F1_two_mul {n : ℕ} (hn : 0 < n) (a : Fin n → ℚ) (m : ℕ) :
    pat3F1 hn a (2 * m) = a (bIdx hn m) * (2 * 3 ^ ((bIdx hn m : ℕ) + 1)) := by
  rw [pat3F1_apply, ite_eq_left_of_eq_true _ _ (eq_true (Nat.mul_mod_right 2 m)),
    Nat.mul_div_cancel_left m (by norm_num)]

theorem pat3F1_periodic {n : ℕ} (hn : 0 < n) (a : Fin n → ℚ) (k : ℕ) :
    pat3F1 hn a (k + 2 * n) = pat3F1 hn a k := by
  have e1 : (k + 2 * n) % 2 = k % 2 := Nat.add_mul_mod_self_left k 2 n
  have e2 : (k + 2 * n) / 2 = k / 2 + n := Nat.add_mul_div_left k n (by norm_num)
  simp only [pat3F1_apply, e1, e2, bIdx_add]

theorem pat3F1_even {n : ℕ} (hn : 0 < n) (a : Fin n → ℚ) : pat3F1 hn a ∈ evenSupp :=
  fun k hk => ite_eq_right_of_eq_false _ _ (eq_false (by omega))

theorem pat3F1_injective {n : ℕ} (hn : 0 < n) : Function.Injective (pat3F1 hn) := by
  intro a b hab
  funext i
  have h := congrFun hab (2 * ((i : ℕ) + 1))
  simp only [pat3F1_two_mul, bIdx_succ] at h
  exact mul_right_cancel₀ (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))) h

/-- The term of the pattern at `k = 2(Bj + i + 1)` is Bailey's term. -/
theorem seriesTerm3_pat3F1 {B : ℕ} (hB : 0 < B) (a : Fin B → ℚ) (j : ℕ) (i : Fin B) :
    seriesTerm3 (pat3F1 hB a) (2 * (B * j + i + 1)) =
      (a i : ℝ) / 3 ^ (B * j) / ((B * j + i + 1 : ℕ) : ℝ) := by
  have e2 : 2 * (B * j + (i : ℕ) + 1) / 2 = B * j + i + 1 :=
    Nat.mul_div_cancel_left _ (by norm_num)
  rw [seriesTerm3, pat3F1_two_mul, bIdx_block, e2]
  have hD : ((B : ℝ) * j + (i : ℕ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Bailey's sum `P(1, 3^B, B, A)` is the series of the pattern.** -/
theorem hasSum_bailey3_F1 {B : ℕ} (hB : 0 < B) (a : Fin B → ℚ) (S : ℝ) :
    HasSum (baileyBlock3 B B a) S ↔ HasSum (seriesTerm3 (pat3F1 hB a)) S := by
  have hper : ∀ k, pat3F1 hB a (k + 2 * B) = pat3F1 hB a k := pat3F1_periodic hB a
  have hs := summable_seriesTerm3 (Nat.mul_pos two_pos hB) hper
  have hinj : Function.Injective fun m : ℕ => 2 * m := fun x y h => by
    have h' : 2 * x = 2 * y := h
    omega
  have hoff : ∀ x ∉ Set.range (fun m : ℕ => 2 * m), seriesTerm3 (pat3F1 hB a) x = 0 := by
    intro x hx
    have hodd : x % 2 = 1 := by
      by_contra hne
      exact hx ⟨x / 2, by change 2 * (x / 2) = x; omega⟩
    rw [seriesTerm3, pat3F1_even hB a x hodd]
    simp
  rw [← hinj.hasSum_iff hoff]
  have hs' : Summable (seriesTerm3 (pat3F1 hB a) ∘ fun m : ℕ => 2 * m) :=
    (hinj.summable_iff hoff).2 hs
  have h0 : (seriesTerm3 (pat3F1 hB a) ∘ fun m : ℕ => 2 * m) 0 = 0 := seriesTerm3_at_zero _
  rw [← hasSum_blocks_iff hB hs' h0 S]
  have e : baileyBlock3 B B a = fun j : ℕ =>
      ∑ i : Fin B, (seriesTerm3 (pat3F1 hB a) ∘ fun m : ℕ => 2 * m) (B * j + i + 1) := by
    funext j
    exact Finset.sum_congr rfl fun i _ => (seriesTerm3_pat3F1 hB a j i).symm
  rw [e]

/-! ## 5. The two zero relations: periods and support -/

/-- A combination `b Z₁ + c Z₂` of period 4 is zero. -/
theorem comb3_zero_of_period_four {b c : ℚ}
    (h : ∀ k, comb3 0 b c (k + 4) = comb3 0 b c k) : b = 0 ∧ c = 0 := by
  obtain ⟨v0, -, -, -, v4, -, -, -, v8, -, -, -⟩ := comb3_values 0 b c
  have h0 : comb3 0 b c 4 = comb3 0 b c 0 := h 0
  have h4 : comb3 0 b c 8 = comb3 0 b c 4 := h 4
  rw [v4, v0] at h0
  rw [v8, v4] at h4
  exact ⟨by linarith, by linarith⟩

/-- A combination `b Z₁ + c Z₂` of period 6 is zero. -/
theorem comb3_zero_of_period_six {b c : ℚ}
    (h : ∀ k, comb3 0 b c (k + 6) = comb3 0 b c k) : b = 0 ∧ c = 0 := by
  obtain ⟨v0, v1, -, -, -, -, v6, v7, -, -, -, -⟩ := comb3_values 0 b c
  have h0 : comb3 0 b c 6 = comb3 0 b c 0 := h 0
  have h1 : comb3 0 b c 7 = comb3 0 b c 1 := h 1
  rw [v6, v0] at h0
  rw [v7, v1] at h1
  exact ⟨by linarith, by linarith⟩

/-- A combination `a G + b Z₁ + c Z₂` supported on even `k` is zero. -/
theorem comb3_zero_of_even {a b c : ℚ} (h : comb3 a b c ∈ evenSupp) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨-, v1, -, v3, -, v5, -, -, -, -, -, -⟩ := comb3_values a b c
  have h1 : comb3 a b c 1 = 0 := h 1 (by norm_num)
  have h3 : comb3 a b c 3 = 0 := h 3 (by norm_num)
  have h5 : comb3 a b c 5 = 0 := h 5 (by norm_num)
  rw [v1] at h1
  rw [v3] at h3
  rw [v5] at h5
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **No zero relation unless 12 divides the period** (from Baker's theorem). -/
theorem zeroSpace3_eq_bot (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h12 : ¬ 12 ∣ N) :
    zeroSpace3 N = ⊥ := by
  rw [eq_bot_iff]
  rintro ρ ⟨hp, h⟩
  obtain ⟨b, c, rfl⟩ := (hasSum_zero_iff hB hN hp).1 h
  have hd := periodic_gcd (by norm_num : 0 < 12) hp (comb3_periodic 0 b c)
  have key : ∀ d ≤ 12, d ∣ 12 → d ≠ 12 → d ∣ 4 ∨ d ∣ 6 := by decide
  have hdvd : Nat.gcd N 12 ∣ 12 := Nat.gcd_dvd_right N 12
  have hne : Nat.gcd N 12 ≠ 12 := fun h => h12 (h ▸ Nat.gcd_dvd_left N 12)
  have hbc : b = 0 ∧ c = 0 := by
    rcases key _ (Nat.le_of_dvd (by norm_num) hdvd) hdvd hne with h4 | h6
    · exact comb3_zero_of_period_four (periodSpace_mono h4 hd)
    · exact comb3_zero_of_period_six (periodSpace_mono h6 hd)
  obtain ⟨rfl, rfl⟩ := hbc
  rw [Submodule.mem_bot]
  funext k
  simp [comb3]

/-- **The number of zero relations at every period (from Baker's theorem).** For every
`N ≥ 1`, the rational patterns of period `N` whose series `∑ ρ(k) 3^(-⌊k/2⌋)/k` is 0 form a
space of dimension 2 if `12 ∣ N`, and 0 otherwise. -/
theorem finrank_zeroSpace3_all (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) :
    Module.finrank ℚ (zeroSpace3 N) = if 12 ∣ N then 2 else 0 := by
  split_ifs with h12
  · exact finrank_zeroSpace3 hB hN h12
  · rw [zeroSpace3_eq_bot hB hN h12]
    exact finrank_bot ℚ (ℕ → ℚ)

/-! ## 6. The counts in Bailey's notation -/

/-- **Bailey's zero relations for `P(1, 3^B, 2B, ·)` (from Baker's theorem)**: for every
`B ≥ 1` there are two independent ones if `6 ∣ B`, and none otherwise. -/
theorem bailey3_count_F2 (hB : BakerTheorem) {B : ℕ} (hB0 : 0 < B) :
    Module.finrank ℚ (baileyZero3 B (2 * B)) = if 6 ∣ B then 2 else 0 := by
  rw [finrank_baileyZero3_F2 hB0, finrank_zeroSpace3_all hB (Nat.mul_pos two_pos hB0)]
  have hiff : 12 ∣ 2 * B ↔ 6 ∣ B := by
    constructor <;> intro h <;> omega
  simp only [hiff]

/-- **No formula `P(1, 3^B, B, A)` for a multiple of `π`** (from Baker's theorem). If
`P(1, 3^B, B, A) = γ π` with `γ` algebraic, then `A = 0` (and so `γ = 0`). -/
theorem bailey3_F1_eq_zero (hB : BakerTheorem) {B : ℕ} (hB0 : 0 < B) (a : Fin B → ℚ) {γ : ℝ}
    (hγ : IsAlgebraic ℚ γ) (h : HasSum (baileyBlock3 B B a) (γ * Real.pi)) : a = 0 := by
  rw [hasSum_bailey3_F1 hB0] at h
  obtain ⟨α, β, δ, hρ, -⟩ :=
    exists_coords3 hB (Nat.mul_pos two_pos hB0) (pat3F1_periodic hB0 a) hγ h
  have hev := pat3F1_even hB0 a
  rw [hρ] at hev
  obtain ⟨rfl, rfl, rfl⟩ := comb3_zero_of_even hev
  apply pat3F1_injective hB0
  rw [hρ, map_zero]
  funext k
  simp [comb3]

theorem baileyZero3_F1 (hB : BakerTheorem) {B : ℕ} (hB0 : 0 < B) : baileyZero3 B B = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have h' : HasSum (baileyBlock3 B B a) ((0 : ℝ) * Real.pi) := by
    rw [zero_mul]
    exact ha
  rw [Submodule.mem_bot]
  exact bailey3_F1_eq_zero hB hB0 a isAlgebraic_zero h'

/-- **Bailey's zero relations for `P(1, 3^B, B, ·)` (from Baker's theorem)**: for every
`B ≥ 1` there is none. -/
theorem bailey3_count_F1 (hB : BakerTheorem) {B : ℕ} (hB0 : 0 < B) :
    Module.finrank ℚ (baileyZero3 B B) = 0 := by
  rw [baileyZero3_F1 hB hB0]
  exact finrank_bot ℚ (Fin B → ℚ)

/-! ## 7. The identities in print -/

theorem twoPos : 0 < 2 := by norm_num

theorem sixPos : 0 < 6 := by norm_num

/-- A coefficient vector of `P(1, 729, 12, ·)` whose pattern is `a G + b Z₁ + c Z₂` on
`0, ..., 11` has the value `a π√3`. -/
theorem hasSum_bailey3_729 {v : Fin (2 * 6) → ℚ} {a b c : ℚ}
    (h : ∀ j < 12, pat3F2 (Nat.mul_pos two_pos sixPos) v j = comb3 a b c j) :
    pat3F2 (Nat.mul_pos two_pos sixPos) v = comb3 a b c ∧
      HasSum (baileyBlock3 6 (2 * 6) v) (a * (Real.pi * Real.sqrt 3)) := by
  have e : pat3F2 (Nat.mul_pos two_pos sixPos) v = comb3 a b c := by
    funext k
    exact eq_of_lt_twelve (pat3F2_periodic _ v) (comb3_periodic a b c) h k
  refine ⟨e, ?_⟩
  rw [hasSum_bailey3_F2 sixPos, e]
  exact hasSum_comb3 a b c

/-- The coefficients `a_1, ..., a_12` of relation 130 of Bailey's compendium. -/
def rel130 : Fin (2 * 6) → ℚ := ![0, 81, -162, 0, 27, 36, 0, 9, 6, 4, -1, 0]

/-- The coefficients `a_1, ..., a_12` of relation 131 of Bailey's compendium. -/
def rel131 : Fin (2 * 6) → ℚ := ![243, -324, -162, -81, 0, -36, -9, 0, 6, -1, 0, 0]

/-- The coefficients `a_1, ..., a_12` of Adegoke's zero relation. -/
def relAdegoke : Fin (2 * 6) → ℚ := ![243, -243, -324, -81, 27, 0, -9, 9, 12, 3, -1, 0]

/-- The coefficients `a_1, ..., a_12` of Broadhurst's formula (formula 69 of the compendium). -/
def broadhurst : Fin (2 * 6) → ℚ := ![81, -54, 0, -9, 0, -12, -3, -2, 0, -1, 0, 0]

/-- The coefficients `a_1, ..., a_4` of the Gregory series, as `P(1, 9, 4, ·)`. -/
def gregory9 : Fin (2 * 2) → ℚ := ![6, 0, -2, 0]

/-- The coefficients `a_1, ..., a_12` of the Gregory series, as `P(1, 729, 12, ·)`. -/
def gregory729 : Fin (2 * 6) → ℚ := ![486, 0, -162, 0, 54, 0, -18, 0, 6, 0, -2, 0]

/-- The coefficients `a_1, ..., a_12` of the second formula with 6 terms. -/
def second729 : Fin (2 * 6) → ℚ := ![0, 162, 162, 54, 0, 0, 0, -6, -6, -2, 0, 0]

/-- The pattern of relation 130 is `243 Z₁`. -/
theorem pat_rel130 : pat3F2 (Nat.mul_pos two_pos sixPos) rel130 = comb3 0 243 0 :=
  (hasSum_bailey3_729 (by decide +kernel)).1

/-- The pattern of relation 131 is `243 (Z₂ - Z₁)`. -/
theorem pat_rel131 : pat3F2 (Nat.mul_pos two_pos sixPos) rel131 = comb3 0 (-243) 243 :=
  (hasSum_bailey3_729 (by decide +kernel)).1

/-- The pattern of Adegoke's relation is `243 Z₂`. -/
theorem pat_relAdegoke : pat3F2 (Nat.mul_pos two_pos sixPos) relAdegoke = comb3 0 0 243 :=
  (hasSum_bailey3_729 (by decide +kernel)).1

/-- The pattern of Broadhurst's formula is `9 (G - 9 Z₁ + 3 Z₂)`. -/
theorem pat_broadhurst : pat3F2 (Nat.mul_pos two_pos sixPos) broadhurst = comb3 9 (-81) 27 :=
  (hasSum_bailey3_729 (by decide +kernel)).1

/-- The pattern of `gregory729` is `81 G`. -/
theorem pat_gregory729 : pat3F2 (Nat.mul_pos two_pos sixPos) gregory729 = comb3 81 0 0 :=
  (hasSum_bailey3_729 (by decide +kernel)).1

/-- The pattern of `second729` is `27 rhoSecond = 27 (G - 6 Z₂)`. -/
theorem pat_second729 : pat3F2 (Nat.mul_pos two_pos sixPos) second729 = comb3 27 0 (-162) :=
  (hasSum_bailey3_729 (by decide +kernel)).1

/-- **Relation 130 of the compendium**:
`P(1, 729, 12, (0, 81, -162, 0, 27, 36, 0, 9, 6, 4, -1, 0)) = 0`. -/
theorem relation130 : HasSum (baileyBlock3 6 (2 * 6) rel130) 0 := by
  have h := (hasSum_bailey3_729 (v := rel130) (a := 0) (b := 243) (c := 0)
    (by decide +kernel)).2
  rw [Rat.cast_zero, zero_mul] at h
  exact h

/-- **Relation 131 of the compendium**:
`P(1, 729, 12, (243, -324, -162, -81, 0, -36, -9, 0, 6, -1, 0, 0)) = 0`. -/
theorem relation131 : HasSum (baileyBlock3 6 (2 * 6) rel131) 0 := by
  have h := (hasSum_bailey3_729 (v := rel131) (a := 0) (b := -243) (c := 243)
    (by decide +kernel)).2
  rw [Rat.cast_zero, zero_mul] at h
  exact h

/-- **Adegoke's relation**:
`P(1, 729, 12, (243, -243, -324, -81, 27, 0, -9, 9, 12, 3, -1, 0)) = 0`. -/
theorem relation_adegoke : HasSum (baileyBlock3 6 (2 * 6) relAdegoke) 0 := by
  have h := (hasSum_bailey3_729 (v := relAdegoke) (a := 0) (b := 0) (c := 243)
    (by decide +kernel)).2
  rw [Rat.cast_zero, zero_mul] at h
  exact h

/-- Adegoke's relation is the sum of relations 130 and 131. -/
theorem relAdegoke_eq : relAdegoke = rel130 + rel131 := by decide +kernel

/-- **Broadhurst's formula** (formula 69 of the compendium):
`P(1, 729, 12, (81, -54, 0, -9, 0, -12, -3, -2, 0, -1, 0, 0)) = 9 π√3`. -/
theorem broadhurst_formula :
    HasSum (baileyBlock3 6 (2 * 6) broadhurst) (9 * (Real.pi * Real.sqrt 3)) := by
  have h := (hasSum_bailey3_729 (v := broadhurst) (a := 9) (b := -81) (c := 27)
    (by decide +kernel)).2
  rw [Rat.cast_ofNat] at h
  exact h

/-- **The Gregory series** in Bailey's notation: `P(1, 9, 4, (6, 0, -2, 0)) = π√3`. -/
theorem gregory_formula :
    HasSum (baileyBlock3 2 (2 * 2) gregory9) (Real.pi * Real.sqrt 3) := by
  have htab : ∀ j < 4, pat3F2 (Nat.mul_pos two_pos twoPos) gregory9 j = rhoGregory j := by
    decide +kernel
  have e : pat3F2 (Nat.mul_pos two_pos twoPos) gregory9 = rhoGregory := by
    funext k
    exact eq_of_lt_period (by norm_num) (pat3F2_periodic _ gregory9) rhoGregory_periodic htab k
  rw [hasSum_bailey3_F2 twoPos, e]
  exact hasSum_gregory3

/-- **The Gregory series** with period 12:
`P(1, 729, 12, (486, 0, -162, 0, 54, 0, -18, 0, 6, 0, -2, 0)) = 81 π√3`. -/
theorem gregory729_formula :
    HasSum (baileyBlock3 6 (2 * 6) gregory729) (81 * (Real.pi * Real.sqrt 3)) := by
  have h := (hasSum_bailey3_729 (v := gregory729) (a := 81) (b := 0) (c := 0)
    (by decide +kernel)).2
  rw [Rat.cast_ofNat] at h
  exact h

/-- **The second formula with 6 terms** in Bailey's notation:
`P(1, 729, 12, (0, 162, 162, 54, 0, 0, 0, -6, -6, -2, 0, 0)) = 27 π√3`. -/
theorem second_formula :
    HasSum (baileyBlock3 6 (2 * 6) second729) (27 * (Real.pi * Real.sqrt 3)) := by
  have h := (hasSum_bailey3_729 (v := second729) (a := 27) (b := 0) (c := -162)
    (by decide +kernel)).2
  rw [Rat.cast_ofNat] at h
  exact h

/-- The pattern of `second729` is `27 rhoSecond`. -/
theorem pat_second729_rhoSecond :
    pat3F2 (Nat.mul_pos two_pos sixPos) second729 = (27 : ℚ) • rhoSecond := by
  rw [pat_second729, rhoSecond_eq]
  funext k
  simp only [comb3, Pi.smul_apply, smul_eq_mul]
  ring

/-- The second formula is 3 times formula 69 minus relation 131. -/
theorem second729_eq : second729 = (3 : ℚ) • broadhurst - rel131 := by decide +kernel

/-! ## 8. Every formula `P(1, 729, 12, A)` -/

/-- The pattern of a combination of formula 69 and relations 130 and 131. -/
theorem pat_comb729 (x y z : ℚ) :
    pat3F2 (Nat.mul_pos two_pos sixPos) (x • broadhurst + y • rel130 + z • rel131) =
      comb3 (9 * x) (-81 * x + 243 * y - 243 * z) (27 * x + 243 * z) := by
  rw [map_add, map_add, map_smul, map_smul, map_smul, pat_broadhurst, pat_rel130, pat_rel131]
  funext k
  simp only [comb3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The value of a combination** of formula 69 and relations 130 and 131:
`P(1, 729, 12, x A₆₉ + y A₁₃₀ + z A₁₃₁) = 9x π√3`. -/
theorem hasSum_bailey3_729_comb (x y z : ℚ) :
    HasSum (baileyBlock3 6 (2 * 6) (x • broadhurst + y • rel130 + z • rel131))
      (9 * x * (Real.pi * Real.sqrt 3)) := by
  rw [hasSum_bailey3_F2 sixPos, pat_comb729]
  have h := hasSum_comb3 (9 * x) (-81 * x + 243 * y - 243 * z) (27 * x + 243 * z)
  convert h using 1
  push_cast
  ring

/-- **Every formula `P(1, 729, 12, A)` for a multiple of `π`** (from Baker's theorem). If
`P(1, 729, 12, A) = γ π` with `γ` algebraic, then `A` is a rational combination
`x A₆₉ + y A₁₃₀ + z A₁₃₁` of the vectors of formula 69 and of relations 130 and 131 of the
compendium, and `γ = 9x √3`. -/
theorem bailey3_729_coords (hB : BakerTheorem) (a : Fin (2 * 6) → ℚ) {γ : ℝ}
    (hγ : IsAlgebraic ℚ γ) (h : HasSum (baileyBlock3 6 (2 * 6) a) (γ * Real.pi)) :
    ∃ x y z : ℚ, a = x • broadhurst + y • rel130 + z • rel131 ∧ γ = 9 * x * Real.sqrt 3 := by
  rw [hasSum_bailey3_F2 sixPos] at h
  obtain ⟨α, β, δ, hρ, hγα⟩ :=
    exists_coords3 hB (Nat.mul_pos two_pos sixPos) (pat3F2_periodic _ a) hγ h
  refine ⟨α / 9, (β + 6 * α + δ) / 243, (δ - 3 * α) / 243, ?_, ?_⟩
  · apply pat3F2_injective (Nat.mul_pos two_pos sixPos)
    rw [hρ, pat_comb729]
    funext k
    simp only [comb3]
    ring
  · rw [hγα]
    push_cast
    ring

/-- **The zero relations of `P(1, 729, 12, ·)`** (from Baker's theorem) are exactly the
rational combinations of relations 130 and 131 of the compendium. -/
theorem bailey3_729_zero_iff (hB : BakerTheorem) (a : Fin (2 * 6) → ℚ) :
    HasSum (baileyBlock3 6 (2 * 6) a) 0 ↔ ∃ y z : ℚ, a = y • rel130 + z • rel131 := by
  constructor
  · intro h
    have h' : HasSum (baileyBlock3 6 (2 * 6) a) ((0 : ℝ) * Real.pi) := by
      rw [zero_mul]
      exact h
    obtain ⟨x, y, z, ha, hx⟩ := bailey3_729_coords hB a isAlgebraic_zero h'
    have hx0 : x = 0 := by
      have hs : Real.sqrt 3 ≠ 0 := sqrt3_pos.ne'
      have h9 : (9 : ℝ) * x = 0 := by
        rcases mul_eq_zero.1 hx.symm with h0 | h0
        · exact h0
        · exact absurd h0 hs
      have hx' : (x : ℝ) = 0 := by linarith
      exact_mod_cast hx'
    exact ⟨y, z, by rw [ha, hx0, zero_smul, zero_add]⟩
  · rintro ⟨y, z, rfl⟩
    have h := hasSum_bailey3_729_comb 0 y z
    rw [zero_smul, zero_add, Rat.cast_zero, mul_zero, zero_mul] at h
    exact h

/-! ## 9. At least `B` of the `2B` entries are non-zero -/

/-- The number of non-zero entries of a coefficient vector. -/
def entryCount {n : ℕ} (a : Fin n → ℚ) : ℕ := (Finset.univ.filter fun i => a i ≠ 0).card

/-- The number of non-zero values of a pattern of period `n` on `m` periods. -/
theorem card_filter_range_mul {f : ℕ → ℚ} {n : ℕ} (hf : ∀ k, f (k + n) = f k) (m : ℕ) :
    ((Finset.range (n * m)).filter fun k => f k ≠ 0).card =
      m * ((Finset.range n).filter fun k => f k ≠ 0).card := by
  simp only [Finset.card_filter]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.succ_mul]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.add_comm (n * m) x, periodic_mul hf m x]

/-- The non-zero entries of `A` are the non-zero values of its pattern on one period. -/
theorem entryCount_eq {n : ℕ} (hn : 0 < n) (a : Fin n → ℚ) :
    entryCount a = ((Finset.range n).filter fun k => pat3F2 hn a k ≠ 0).card := by
  have hg : ∀ i : Fin n, (if a i ≠ 0 then 1 else 0 : ℕ) =
      (if pat3F2 hn a ((i : ℕ) + 1) ≠ 0 then 1 else 0 : ℕ) := by
    intro i
    have h3 : (3 : ℚ) ^ (((i : ℕ) + 1) / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
    simp only [pat3F2_apply, bIdx_succ, ne_eq, mul_eq_zero, h3, or_false]
  have h1 := Finset.sum_range_succ' (fun k : ℕ => (if pat3F2 hn a k ≠ 0 then 1 else 0 : ℕ)) n
  have h2 := Finset.sum_range_succ (fun k : ℕ => (if pat3F2 hn a k ≠ 0 then 1 else 0 : ℕ)) n
  have h3 : pat3F2 hn a n = pat3F2 hn a 0 := by
    have h := pat3F2_periodic hn a 0
    rwa [zero_add] at h
  have h4 := h1.symm.trans h2
  rw [h3] at h4
  rw [entryCount, Finset.card_filter, Finset.card_filter]
  calc ∑ i : Fin n, (if a i ≠ 0 then 1 else 0 : ℕ)
      = ∑ i : Fin n, (if pat3F2 hn a ((i : ℕ) + 1) ≠ 0 then 1 else 0 : ℕ) :=
        Finset.sum_congr rfl fun i _ => hg i
    _ = ∑ k ∈ Finset.range n, (if pat3F2 hn a (k + 1) ≠ 0 then 1 else 0 : ℕ) :=
        Fin.sum_univ_eq_sum_range
          (fun k : ℕ => (if pat3F2 hn a (k + 1) ≠ 0 then 1 else 0 : ℕ)) n
    _ = ∑ k ∈ Finset.range n, (if pat3F2 hn a k ≠ 0 then 1 else 0 : ℕ) :=
        Nat.add_right_cancel h4

/-- **The formulas `P(1, 3^B, 2B, A)` for a multiple of `π`** (from Baker's theorem). If
`P(1, 3^B, 2B, A) = γ π` with `γ` algebraic, then `γ` is a rational multiple of `√3`, and if
`γ ≠ 0` at least `B` of the `2B` entries of `A` are non-zero: at least one term per base-3
digit. -/
theorem bailey3_pi_F2 (hB : BakerTheorem) {B : ℕ} (hB0 : 0 < B) (a : Fin (2 * B) → ℚ) {γ : ℝ}
    (hγ : IsAlgebraic ℚ γ) (h : HasSum (baileyBlock3 B (2 * B) a) (γ * Real.pi)) :
    (∃ q : ℚ, γ = q * Real.sqrt 3) ∧ (γ ≠ 0 → B ≤ entryCount a) := by
  have hn : 0 < 2 * B := Nat.mul_pos two_pos hB0
  rw [hasSum_bailey3_F2 hB0] at h
  have hper := pat3F2_periodic hn a
  obtain ⟨α, β, δ, hρ, hγα⟩ := exists_coords3 hB hn hper hγ h
  refine ⟨⟨α, hγα⟩, fun hγ0 => ?_⟩
  have hα : α ≠ 0 := by
    rintro rfl
    apply hγ0
    rw [hγα]
    simp
  have h6 := six_le_termCount3_comb3 hα β δ
  rw [← hρ, termCount3] at h6
  have h12 : ∀ k, pat3F2 hn a (k + 12) = pat3F2 hn a k := by
    rw [hρ]
    exact comb3_periodic α β δ
  have c1 := card_filter_range_mul hper 12
  have c2 := card_filter_range_mul h12 (2 * B)
  rw [← entryCount_eq hn a] at c1
  rw [Nat.mul_comm 12 (2 * B), c1] at c2
  have h7 := Nat.mul_le_mul_left (2 * B) h6
  rw [← c2] at h7
  omega

/-- The numbers of non-zero entries of the formulas in print: 6 of 12 for the Gregory series
and for the second formula, 7 of 12 for Broadhurst's formula. -/
theorem entryCount_printed :
    entryCount gregory729 = 6 ∧ entryCount second729 = 6 ∧ entryCount broadhurst = 7 := by
  decide +kernel

end Base3

end PiFormula
