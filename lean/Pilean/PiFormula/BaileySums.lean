module

public import Pilean.PiFormula.Bailey

/-!
# Bailey's sums and the patterns: the re-indexing (milestone M8)

Bailey's notation is `P(s, b, n, A) = ∑_{j ≥ 0} b^(-j) ∑_{i=1}^n a_i / (nj + i)^s`. Table 1 of
his compendium lists, for 27 pairs `(B, n)` with `s = 1` and `b = 2^B`, the number of
independent *zero relations*: coefficient vectors `A = (a_1, ..., a_n)` with
`P(1, 2^B, n, A) = 0`.

`Bailey.lean` counts spaces of patterns. This file connects the two. `baileyZero B n` is the
space of coefficient vectors `a : Fin n → ℚ` (here `a i` is Bailey's `a_{i+1}`) with
`∑_j ∑_i a_i 2^(-Bj) / (nj + i + 1) = 0`, written exactly as Bailey's double sum
(`baileyBlock`). With `k = nj + i + 1`:

* if `n = 2B`, the vector `a` corresponds to the pattern `ρ(k) = a_i 2^⌊(i+1)/2⌋` of period
  `n` (`patF2`), and Bailey's sum is the series of `ρ` (`hasSum_bailey_F2`). So
  `baileyZero B (2B)` is `zeroSpace (2B)` (`baileyZero_F2`, `finrank_baileyZero_F2`);
* if `n = B`, it corresponds to the pattern supported on even `k` with
  `ρ(2k) = a_i 2^(i+2)`, of period `2n` (`patF1`), and `baileyZero B B` is
  `zeroSpaceEven (2B)` (`baileyZero_F1`, `finrank_baileyZero_F1`).

None of this uses Baker's theorem. With it:

* `bailey_count_F2`: `P(1, 2^B, 2B, ·)` has `zeroCount (gcd(2B, 120))` independent zero
  relations, for every `B ≥ 1`;
* `bailey_count_F1`: `P(1, 2^B, B, ·)` has one zero relation if `6 ∣ B`, and none otherwise;
* `bailey_table`: the 27 rows of Bailey's Table 1 (binary, degree 1), as stated by Bailey.
-/

@[expose] public section

open Complex

namespace PiFormula

/-! ## 1. Convergence, and grouping into blocks -/

/-- The series of a periodic rational pattern converges. -/
theorem summable_seriesTerm {n : ℕ} (hn : 0 < n) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + n) = ρ k) :
    Summable (seriesTerm ρ) := by
  have h8 : ∀ k, ρ (k + 8 * n) = ρ k := fun k => by
    have h := periodic_mul hρ 8 k
    rwa [mul_comm] at h
  have h := (series_eq_logs (N := 8 * n) (by positivity) (Dvd.intro n rfl) h8).summable
  have e : (fun k : ℕ => (ρ k : ℂ) / 2 ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTerm ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTerm]
  rw [e] at h
  exact Complex.summable_ofReal.1 h

theorem seriesTerm_at_zero (ρ : ℕ → ℚ) : seriesTerm ρ 0 = 0 := by simp [seriesTerm]

/-- A convergent series with `h 0 = 0`, grouped into blocks `k = nj + i + 1` (`i < n`). -/
theorem hasSum_blocks_iff {n : ℕ} (hn : 0 < n) {h : ℕ → ℝ} (hs : Summable h) (h0 : h 0 = 0)
    (S : ℝ) : HasSum (fun j : ℕ => ∑ i : Fin n, h (n * j + i + 1)) S ↔ HasSum h S := by
  have : NeZero n := ⟨hn.ne'⟩
  have key : ∀ T, HasSum h T → HasSum (fun j : ℕ => ∑ i : Fin n, h (n * j + i + 1)) T := by
    intro T hT
    have h1 : HasSum (fun m : ℕ => h (m + 1)) T := by
      have h' := (hasSum_nat_add_iff' (f := h) (g := T) 1).2 hT
      simpa [h0] using h'
    have h2 : HasSum ((fun m : ℕ => h (m + 1)) ∘ (Nat.divModEquiv n).symm) T :=
      (Equiv.hasSum_iff (Nat.divModEquiv n).symm).2 h1
    refine h2.prod_fiberwise fun j => ?_
    have e : (∑ i : Fin n, h (n * j + i + 1)) =
        ∑ i : Fin n, ((fun m : ℕ => h (m + 1)) ∘ (Nat.divModEquiv n).symm) (j, i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      change h (n * j + i + 1) = h (j * n + i + 1)
      rw [mul_comm]
    rw [e]
    exact hasSum_fintype _
  constructor
  · intro hS
    obtain ⟨T, hT⟩ := hs
    have hTS := (key T hT).unique hS
    rw [← hTS]
    exact hT
  · exact key S

/-! ## 2. Positions inside a block -/

/-- The index of `k` in its block: `k = nj + i + 1` with `i < n`. -/
def bIdx {n : ℕ} (hn : 0 < n) (k : ℕ) : Fin n := ⟨(k + (n - 1)) % n, Nat.mod_lt _ hn⟩

theorem bIdx_block {n : ℕ} (hn : 0 < n) (j : ℕ) (i : Fin n) : bIdx hn (n * j + i + 1) = i := by
  apply Fin.ext
  change (n * j + i + 1 + (n - 1)) % n = i
  have e : n * j + i + 1 + (n - 1) = i + n * (j + 1) := by
    rw [mul_add, mul_one]
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.2]

theorem bIdx_succ {n : ℕ} (hn : 0 < n) (i : Fin n) : bIdx hn ((i : ℕ) + 1) = i := by
  have h := bIdx_block hn 0 i
  simpa using h

theorem bIdx_add {n : ℕ} (hn : 0 < n) (k : ℕ) : bIdx hn (k + n) = bIdx hn k := by
  apply Fin.ext
  change (k + n + (n - 1)) % n = (k + (n - 1)) % n
  rw [show k + n + (n - 1) = k + (n - 1) + n by omega, Nat.add_mod_right]

/-- `k ≡ bIdx k + 1 (mod n)`. -/
theorem bIdx_mod {n : ℕ} (hn : 0 < n) (k : ℕ) : ((bIdx hn k : ℕ) + 1) % n = k % n := by
  change ((k + (n - 1)) % n + 1) % n = k % n
  rw [Nat.mod_add_mod, show k + (n - 1) + 1 = k + n by omega, Nat.add_mod_right]

theorem period_mod {f : ℕ → ℚ} {n : ℕ} (h : ∀ k, f (k + n) = f k) (k : ℕ) :
    f (k % n) = f k := by
  have h2 := periodic_mul h (k / n) (k % n)
  rw [Nat.mod_add_div] at h2
  exact h2.symm

/-- A periodic pattern takes the same value at `k` and at `bIdx k + 1`. -/
theorem period_bIdx {f : ℕ → ℚ} {n : ℕ} (hn : 0 < n) (h : ∀ k, f (k + n) = f k) (k : ℕ) :
    f ((bIdx hn k : ℕ) + 1) = f k := by
  have e1 := period_mod h ((bIdx hn k : ℕ) + 1)
  rw [bIdx_mod, period_mod h] at e1
  exact e1.symm

/-! ## 3. Bailey's sums -/

/-- The `j`-th block of Bailey's sum `P(1, 2^B, n, A) = ∑_j 2^(-Bj) ∑_{i=1}^n a_i / (nj + i)`.
Here `a i` (`i : Fin n`, so `i = 0, ..., n-1`) is Bailey's `a_{i+1}`. -/
noncomputable def baileyBlock (B n : ℕ) (a : Fin n → ℚ) (j : ℕ) : ℝ :=
  ∑ i : Fin n, (a i : ℝ) / 2 ^ (B * j) / ((n * j + i + 1 : ℕ) : ℝ)

/-- **Bailey's zero relations**: the coefficient vectors `A` with `P(1, 2^B, n, A) = 0`. -/
def baileyZero (B n : ℕ) : Submodule ℚ (Fin n → ℚ) where
  carrier := {a | HasSum (baileyBlock B n a) 0}
  add_mem' := by
    intro a b ha hb
    have h := HasSum.add ha hb
    rw [add_zero] at h
    have e : baileyBlock B n (a + b) = fun j => baileyBlock B n a j + baileyBlock B n b j := by
      funext j
      simp only [baileyBlock, Pi.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    change HasSum (baileyBlock B n (a + b)) 0
    rw [e]
    exact h
  zero_mem' := by
    have e : baileyBlock B n 0 = fun _ => 0 := by
      funext j
      simp [baileyBlock]
    change HasSum (baileyBlock B n 0) 0
    rw [e]
    exact hasSum_zero
  smul_mem' := by
    intro c a ha
    have h := HasSum.mul_left (c : ℝ) ha
    rw [mul_zero] at h
    have e : baileyBlock B n (c • a) = fun j => (c : ℝ) * baileyBlock B n a j := by
      funext j
      simp only [baileyBlock, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    change HasSum (baileyBlock B n (c • a)) 0
    rw [e]
    exact h

/-- Pulling a subspace back along an injective map whose range contains it keeps the
dimension. -/
theorem finrank_comap_of_le {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (f : V →ₗ[ℚ] W) (hf : Function.Injective f) {S : Submodule ℚ W}
    (hS : S ≤ LinearMap.range f) : Module.finrank ℚ (S.comap f) = Module.finrank ℚ S := by
  have e := (Submodule.equivMapOfInjective f hf (S.comap f)).finrank_eq
  rw [Submodule.map_comap_eq_self hS] at e
  exact e

/-! ## 4. The rows with `n = 2B` -/

/-- The pattern of a coefficient vector, for `n = 2B`: `ρ(nj + i + 1) = a_i 2^⌊(i+1)/2⌋`. -/
def patF2 {n : ℕ} (hn : 0 < n) : (Fin n → ℚ) →ₗ[ℚ] (ℕ → ℚ) where
  toFun a k := a (bIdx hn k) * 2 ^ (((bIdx hn k : ℕ) + 1) / 2)
  map_add' a b := by
    funext k
    simp only [Pi.add_apply]
    ring
  map_smul' c a := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem patF2_apply {n : ℕ} (hn : 0 < n) (a : Fin n → ℚ) (k : ℕ) :
    patF2 hn a k = a (bIdx hn k) * 2 ^ (((bIdx hn k : ℕ) + 1) / 2) := rfl

theorem patF2_periodic {n : ℕ} (hn : 0 < n) (a : Fin n → ℚ) (k : ℕ) :
    patF2 hn a (k + n) = patF2 hn a k := by
  simp only [patF2_apply, bIdx_add]

theorem patF2_injective {n : ℕ} (hn : 0 < n) : Function.Injective (patF2 hn) := by
  intro a b hab
  funext i
  have h := congrFun hab ((i : ℕ) + 1)
  simp only [patF2_apply, bIdx_succ] at h
  exact mul_right_cancel₀ (pow_ne_zero _ (by norm_num)) h

theorem range_patF2 {n : ℕ} (hn : 0 < n) : LinearMap.range (patF2 hn) = periodSpace n := by
  apply le_antisymm
  · intro ρ hρ
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.1 hρ
    exact fun k => patF2_periodic hn a k
  · intro ρ hρ
    refine LinearMap.mem_range.2
      ⟨fun i => ρ ((i : ℕ) + 1) / 2 ^ (((i : ℕ) + 1) / 2), ?_⟩
    funext k
    have h2 : (2 : ℚ) ^ (((bIdx hn k : ℕ) + 1) / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
    simp only [patF2_apply]
    rw [div_mul_cancel₀ _ h2]
    exact period_bIdx hn hρ k

/-- The term of the pattern at `k = 2Bj + i + 1` is Bailey's term. -/
theorem seriesTerm_patF2 {B : ℕ} (hB : 0 < B) (a : Fin (2 * B) → ℚ) (j : ℕ)
    (i : Fin (2 * B)) :
    seriesTerm (patF2 (Nat.mul_pos two_pos hB) a) (2 * B * j + i + 1) =
      (a i : ℝ) / 2 ^ (B * j) / ((2 * B * j + i + 1 : ℕ) : ℝ) := by
  have e : (2 * B * j + (i : ℕ) + 1) / 2 = B * j + ((i : ℕ) + 1) / 2 := by
    rw [show 2 * B * j + (i : ℕ) + 1 = 2 * (B * j) + ((i : ℕ) + 1) by ring]
    exact Nat.mul_add_div (by norm_num) _ _
  rw [seriesTerm, patF2_apply, bIdx_block, e, pow_add]
  have h2 : (2 : ℝ) ^ (((i : ℕ) + 1) / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast
  rw [mul_div_mul_right _ _ h2]

/-- **Bailey's sum with `n = 2B` is the series of the pattern.** -/
theorem hasSum_bailey_F2 {B : ℕ} (hB : 0 < B) (a : Fin (2 * B) → ℚ) (S : ℝ) :
    HasSum (baileyBlock B (2 * B) a) S ↔
      HasSum (seriesTerm (patF2 (Nat.mul_pos two_pos hB) a)) S := by
  have hn : 0 < 2 * B := Nat.mul_pos two_pos hB
  have hs := summable_seriesTerm hn (patF2_periodic hn a)
  rw [← hasSum_blocks_iff hn hs (seriesTerm_at_zero _) S]
  have e : baileyBlock B (2 * B) a =
      fun j : ℕ => ∑ i : Fin (2 * B), seriesTerm (patF2 hn a) (2 * B * j + i + 1) := by
    funext j
    exact Finset.sum_congr rfl fun i _ => (seriesTerm_patF2 hB a j i).symm
  rw [e]

/-- Bailey's zero relations with `n = 2B` are the zero relations of period `2B`. -/
theorem baileyZero_F2 {B : ℕ} (hB : 0 < B) :
    baileyZero B (2 * B) = (zeroSpace (2 * B)).comap (patF2 (Nat.mul_pos two_pos hB)) := by
  have hn : 0 < 2 * B := Nat.mul_pos two_pos hB
  ext a
  rw [Submodule.mem_comap]
  constructor
  · intro h
    exact ⟨fun k => patF2_periodic hn a k, (hasSum_bailey_F2 hB a 0).1 h⟩
  · intro h
    exact (hasSum_bailey_F2 hB a 0).2 h.2

/-- The number of Bailey's zero relations with `n = 2B` (no Baker's theorem). -/
theorem finrank_baileyZero_F2 {B : ℕ} (hB : 0 < B) :
    Module.finrank ℚ (baileyZero B (2 * B)) = Module.finrank ℚ (zeroSpace (2 * B)) := by
  have hn : 0 < 2 * B := Nat.mul_pos two_pos hB
  rw [baileyZero_F2 hB]
  refine finrank_comap_of_le _ (patF2_injective hn) ?_
  rw [range_patF2 hn]
  exact inf_le_left

/-! ## 5. The rows with `n = B` -/

/-- The pattern of a coefficient vector, for `n = B`: supported on even `k`, with
`ρ(2(nj + i + 1)) = a_i 2^(i+2)`. -/
def patF1 {n : ℕ} (hn : 0 < n) : (Fin n → ℚ) →ₗ[ℚ] (ℕ → ℚ) where
  toFun a k := if k % 2 = 0 then a (bIdx hn (k / 2)) * 2 ^ ((bIdx hn (k / 2) : ℕ) + 2) else 0
  map_add' a b := by
    funext k
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c a := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem patF1_apply {n : ℕ} (hn : 0 < n) (a : Fin n → ℚ) (k : ℕ) :
    patF1 hn a k =
      if k % 2 = 0 then a (bIdx hn (k / 2)) * 2 ^ ((bIdx hn (k / 2) : ℕ) + 2) else 0 := rfl

theorem patF1_two_mul {n : ℕ} (hn : 0 < n) (a : Fin n → ℚ) (m : ℕ) :
    patF1 hn a (2 * m) = a (bIdx hn m) * 2 ^ ((bIdx hn m : ℕ) + 2) := by
  rw [patF1_apply, ite_eq_left_of_eq_true _ _ (eq_true (Nat.mul_mod_right 2 m)),
    Nat.mul_div_cancel_left m (by norm_num)]

theorem patF1_periodic {n : ℕ} (hn : 0 < n) (a : Fin n → ℚ) (k : ℕ) :
    patF1 hn a (k + 2 * n) = patF1 hn a k := by
  have e1 : (k + 2 * n) % 2 = k % 2 := Nat.add_mul_mod_self_left k 2 n
  have e2 : (k + 2 * n) / 2 = k / 2 + n := Nat.add_mul_div_left k n (by norm_num)
  simp only [patF1_apply, e1, e2, bIdx_add]

theorem patF1_even {n : ℕ} (hn : 0 < n) (a : Fin n → ℚ) : patF1 hn a ∈ evenSupp :=
  fun k hk => ite_eq_right_of_eq_false _ _ (eq_false (by omega))

theorem patF1_injective {n : ℕ} (hn : 0 < n) : Function.Injective (patF1 hn) := by
  intro a b hab
  funext i
  have h := congrFun hab (2 * ((i : ℕ) + 1))
  simp only [patF1_two_mul, bIdx_succ] at h
  exact mul_right_cancel₀ (pow_ne_zero _ (by norm_num)) h

theorem range_patF1 {n : ℕ} (hn : 0 < n) :
    LinearMap.range (patF1 hn) = periodSpace (2 * n) ⊓ evenSupp := by
  apply le_antisymm
  · intro ρ hρ
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.1 hρ
    exact ⟨fun k => patF1_periodic hn a k, patF1_even hn a⟩
  · rintro ρ ⟨hper, hev⟩
    refine LinearMap.mem_range.2 ⟨fun i => ρ (2 * ((i : ℕ) + 1)) / 2 ^ ((i : ℕ) + 2), ?_⟩
    funext k
    by_cases hk : k % 2 = 0
    · have hf : ∀ m, ρ (2 * (m + n)) = ρ (2 * m) := by
        intro m
        rw [mul_add]
        exact hper (2 * m)
      have h1 : ρ (2 * ((bIdx hn (k / 2) : ℕ) + 1)) = ρ (2 * (k / 2)) :=
        period_bIdx (f := fun m : ℕ => ρ (2 * m)) hn hf (k / 2)
      have h2 : (2 : ℚ) ^ ((bIdx hn (k / 2) : ℕ) + 2) ≠ 0 := pow_ne_zero _ (by norm_num)
      have e : 2 * (k / 2) = k := by omega
      rw [patF1_apply, ite_eq_left_of_eq_true _ _ (eq_true hk)]
      rw [div_mul_cancel₀ _ h2, h1, e]
    · rw [patF1_apply, ite_eq_right_of_eq_false _ _ (eq_false hk)]
      exact (hev k (by omega)).symm

/-- The term of the pattern at `k = 2(Bj + i + 1)` is Bailey's term. -/
theorem seriesTerm_patF1 {B : ℕ} (hB : 0 < B) (a : Fin B → ℚ) (j : ℕ) (i : Fin B) :
    seriesTerm (patF1 hB a) (2 * (B * j + i + 1)) =
      (a i : ℝ) / 2 ^ (B * j) / ((B * j + i + 1 : ℕ) : ℝ) := by
  have e2 : 2 * (B * j + (i : ℕ) + 1) / 2 = B * j + i + 1 :=
    Nat.mul_div_cancel_left _ (by norm_num)
  rw [seriesTerm, patF1_two_mul, bIdx_block, e2]
  have hD : ((B : ℝ) * j + (i : ℕ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Bailey's sum with `n = B` is the series of the pattern.** -/
theorem hasSum_bailey_F1 {B : ℕ} (hB : 0 < B) (a : Fin B → ℚ) (S : ℝ) :
    HasSum (baileyBlock B B a) S ↔ HasSum (seriesTerm (patF1 hB a)) S := by
  have hper : ∀ k, patF1 hB a (k + 2 * B) = patF1 hB a k := patF1_periodic hB a
  have hs := summable_seriesTerm (Nat.mul_pos two_pos hB) hper
  have hinj : Function.Injective fun m : ℕ => 2 * m := fun x y h => by
    have h' : 2 * x = 2 * y := h
    omega
  have hoff : ∀ x ∉ Set.range (fun m : ℕ => 2 * m), seriesTerm (patF1 hB a) x = 0 := by
    intro x hx
    have hodd : x % 2 = 1 := by
      by_contra hne
      exact hx ⟨x / 2, by change 2 * (x / 2) = x; omega⟩
    rw [seriesTerm, patF1_even hB a x hodd]
    simp
  rw [← hinj.hasSum_iff hoff]
  have hs' : Summable (seriesTerm (patF1 hB a) ∘ fun m : ℕ => 2 * m) :=
    (hinj.summable_iff hoff).2 hs
  have h0 : (seriesTerm (patF1 hB a) ∘ fun m : ℕ => 2 * m) 0 = 0 := seriesTerm_at_zero _
  rw [← hasSum_blocks_iff hB hs' h0 S]
  have e : baileyBlock B B a = fun j : ℕ =>
      ∑ i : Fin B, (seriesTerm (patF1 hB a) ∘ fun m : ℕ => 2 * m) (B * j + i + 1) := by
    funext j
    exact Finset.sum_congr rfl fun i _ => (seriesTerm_patF1 hB a j i).symm
  rw [e]

/-- Bailey's zero relations with `n = B` are the zero relations of period `2B` supported on
even `k`. -/
theorem baileyZero_F1 {B : ℕ} (hB : 0 < B) :
    baileyZero B B = (zeroSpaceEven (2 * B)).comap (patF1 hB) := by
  ext a
  rw [Submodule.mem_comap]
  constructor
  · intro h
    exact ⟨⟨fun k => patF1_periodic hB a k, (hasSum_bailey_F1 hB a 0).1 h⟩, patF1_even hB a⟩
  · intro h
    exact (hasSum_bailey_F1 hB a 0).2 h.1.2

/-- The number of Bailey's zero relations with `n = B` (no Baker's theorem). -/
theorem finrank_baileyZero_F1 {B : ℕ} (hB : 0 < B) :
    Module.finrank ℚ (baileyZero B B) = Module.finrank ℚ (zeroSpaceEven (2 * B)) := by
  rw [baileyZero_F1 hB]
  refine finrank_comap_of_le _ (patF1_injective hB) ?_
  rw [range_patF1 hB]
  rintro ρ ⟨⟨hper, -⟩, hev⟩
  exact ⟨hper, hev⟩

/-! ## 6. No even-supported zero relation unless `12 ∣ gcd(n, 120)` -/

theorem zeroSpaceEven_eq_bot (hB : BakerTheorem) {g : ℕ} (hg : g ∣ 120) (h12 : ¬ 12 ∣ g) :
    zeroSpaceEven g = ⊥ := by
  rw [eq_bot_iff]
  rintro ρ ⟨⟨hper, hzero⟩, hev⟩
  obtain ⟨q, rfl⟩ := coords_of_zero hB hg hper hzero
  have hmem := mem_span_zL (coords_even q (coords_zero hzero) hev)
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  rw [← hc] at hper ⊢
  by_cases hc0 : c = 0
  · rw [hc0, zero_smul]
    exact Submodule.zero_mem _
  · exfalso
    have hzg : ∀ k, zL (k + g) = zL k := by
      intro k
      have h2 := hper k
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      exact mul_left_cancel₀ hc0 h2
    have hd := periodic_gcd (by norm_num) hzg zL_period
    have key : ∀ d ≤ 12, d ∣ 12 → d ≠ 12 → d ∣ 4 ∨ d ∣ 6 := by decide
    have hdvd : Nat.gcd g 12 ∣ 12 := Nat.gcd_dvd_right g 12
    have hne : Nat.gcd g 12 ≠ 12 := fun h => h12 (h ▸ Nat.gcd_dvd_left g 12)
    obtain ⟨v2, v6, v8⟩ := zL_values
    rcases key _ (Nat.le_of_dvd (by norm_num) hdvd) hdvd hne with h4 | h6
    · have h := periodSpace_mono h4 hd 2
      have h' : zL 6 = zL 2 := h
      rw [v2, v6] at h'
      norm_num at h'
    · have h := periodSpace_mono h6 hd 2
      have h' : zL 8 = zL 2 := h
      rw [v2, v8] at h'
      norm_num at h'

/-- **Zero relations supported on even `k`, at every period (from Baker's theorem)**: one if
`12 ∣ gcd(n, 120)`, none otherwise. -/
theorem finrank_zeroSpaceEven' (hB : BakerTheorem) {n : ℕ} (hn : 0 < n) :
    Module.finrank ℚ (zeroSpaceEven n) = if 12 ∣ Nat.gcd n 120 then 1 else 0 := by
  split_ifs with h12
  · exact finrank_zeroSpaceEven hB hn h12
  · rw [zeroSpaceEven_gcd hB hn, zeroSpaceEven_eq_bot hB (Nat.gcd_dvd_right n 120) h12]
    exact finrank_bot ℚ (ℕ → ℚ)

/-! ## 7. Bailey's table -/

/-- **Bailey's zero relations for `P(1, 2^B, 2B, ·)` (from Baker's theorem)**: for every
`B ≥ 1` there are `zeroCount (gcd(2B, 120))` independent ones. -/
theorem bailey_count_F2 (hB : BakerTheorem) {B : ℕ} (hB0 : 0 < B) :
    Module.finrank ℚ (baileyZero B (2 * B)) = zeroCount (Nat.gcd (2 * B) 120) := by
  rw [finrank_baileyZero_F2 hB0]
  exact finrank_zeroSpace hB (Nat.mul_pos two_pos hB0)

/-- **Bailey's zero relations for `P(1, 2^B, B, ·)` (from Baker's theorem)**: for every
`B ≥ 1` there is one if `6 ∣ B`, and none otherwise. -/
theorem bailey_count_F1 (hB : BakerTheorem) {B : ℕ} (hB0 : 0 < B) :
    Module.finrank ℚ (baileyZero B B) = if 6 ∣ B then 1 else 0 := by
  rw [finrank_baileyZero_F1 hB0, finrank_zeroSpaceEven' hB (Nat.mul_pos two_pos hB0)]
  have hiff : 12 ∣ Nat.gcd (2 * B) 120 ↔ 6 ∣ B := by
    constructor
    · intro h
      have h1 : 12 ∣ 2 * B := h.trans (Nat.gcd_dvd_left _ _)
      omega
    · intro h
      exact Nat.dvd_gcd (by omega) (by norm_num)
  simp only [hiff]

/-- **Bailey's Table 1, the 27 binary rows of degree 1 (from Baker's theorem).** Each triple
is `(B, n, count)`: the coefficient vectors `A` with `P(1, 2^B, n, A) = 0` form a space of
that dimension. -/
theorem bailey_table (hB : BakerTheorem) :
    ∀ r ∈ ([(4, 8, 1), (6, 6, 1), (8, 16, 1), (12, 12, 1), (12, 24, 5), (16, 32, 1),
      (18, 18, 1), (20, 40, 3), (24, 24, 1), (24, 48, 5), (28, 56, 1), (30, 30, 1), (30, 60, 1),
      (32, 64, 1), (36, 36, 1), (36, 72, 5), (40, 80, 3), (42, 42, 1), (42, 84, 1), (44, 88, 1),
      (48, 48, 1), (48, 96, 5), (52, 104, 1), (54, 54, 1), (56, 112, 1), (60, 60, 1),
      (60, 120, 7)] : List (ℕ × ℕ × ℕ)),
      Module.finrank ℚ (baileyZero r.1 r.2.1) = r.2.2 := by
  intro r hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (bailey_count_F2 hB (B := 4) (by norm_num)).trans (by decide)
  · exact (bailey_count_F1 hB (B := 6) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 8) (by norm_num)).trans (by decide)
  · exact (bailey_count_F1 hB (B := 12) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 12) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 16) (by norm_num)).trans (by decide)
  · exact (bailey_count_F1 hB (B := 18) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 20) (by norm_num)).trans (by decide)
  · exact (bailey_count_F1 hB (B := 24) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 24) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 28) (by norm_num)).trans (by decide)
  · exact (bailey_count_F1 hB (B := 30) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 30) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 32) (by norm_num)).trans (by decide)
  · exact (bailey_count_F1 hB (B := 36) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 36) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 40) (by norm_num)).trans (by decide)
  · exact (bailey_count_F1 hB (B := 42) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 42) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 44) (by norm_num)).trans (by decide)
  · exact (bailey_count_F1 hB (B := 48) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 48) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 52) (by norm_num)).trans (by decide)
  · exact (bailey_count_F1 hB (B := 54) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 56) (by norm_num)).trans (by decide)
  · exact (bailey_count_F1 hB (B := 60) (by norm_num)).trans (by decide)
  · exact (bailey_count_F2 hB (B := 60) (by norm_num)).trans (by decide)

end PiFormula
