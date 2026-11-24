module

public import Pilean.Base3.LogExplicit
public import Pilean.Base3.Halves

/-!
# Base 3: two primes in one primitive part exclude each other

This file is the half of the finite test for a prime (`LogPrimeTest.lean`) that needs Baker's
theorem. It works with the base numbers themselves: `3`, the numbers `3^m - 1`, of *index*
`m`, and the two Aurifeuillian factors `L_k = 3^(2k+1) - 3^(k+1) + 1` and
`M_k = 3^(2k+1) + 3^(k+1) + 1` (`L3`, `M3`), of index `6 (2k+1)`.

**The statement** (`not_isF3Value_log_of_same_part`, from Baker's theorem). Let `p ≠ 3` and
`q ≠ p` be primes at which 3 has the same order `n`; if `n = 6 (2j+1)`, let `p` and `q` divide
the same one of `L_j`, `M_j`. Then `log p` is not a value of the class F3.

**The proof.** By the criterion (`isF3Value_log_rat_iff_pow`) a formula for `log p` gives a
relation `p^k = ∏ g_i^(e_i)` between base numbers. We build a function `f : ℚ → ℚ` with
`f (x y) = f x + f y` (`LogLike`) that is zero on every base number of index at most `N`
(`Kills f N`), for `N` as large as we like, and has `f p = 1`; this contradicts the relation.
The function is a rational combination of valuations at primes, built index by index.

* Start with the valuation at `p`. It is zero on the base numbers of index below `n`.
* At the index `n` subtract a multiple of the valuation at `q`, so that the new function is
  zero on `3^n - 1` (on the one of `L_j`, `M_j` that `p` and `q` divide, if `n = 6 (2j+1)`).
* At an index `D > n` that is not 6 modulo 12, take a prime `r` at which 3 has order `D`
  (Zsigmondy's theorem; there is none for `D = 2`, and none is needed since
  `3^2 - 1 = (3 - 1)^3`) and subtract a multiple of the valuation at `r`, so that the new
  function is zero on `3^D - 1`. The valuation at `r` is zero on the base numbers of smaller
  index and at `p`.
* At an index `D = 6 (2j+1) > n` do this twice, with a prime of order `D` in `L_j` and one in
  `M_j` (`primitiveHalves3`; for `j = 0` the numbers are `1` and `7`). The first prime does
  not divide `M_j`, nor the second `L_j`, since a common prime factor of `L_j` and `M_j` could
  only be 2 or 3. Then the function is zero on `3^D - 1` as well, because
  `(3^D - 1) (3^E - 1) = (3^(3E) - 1) (3^(2E) - 1) L_j M_j` with `E = 2j + 1`.
-/

@[expose] public section

open Polynomial

namespace PiFormula

namespace Base3

/-! ## 1. Functions that turn products into sums -/

/-- A function `f : ℚ → ℚ` with `f (x y) = f x + f y` for non-zero `x`, `y`. The valuations at
the primes and their rational combinations are of this kind. -/
def LogLike (f : ℚ → ℚ) : Prop := ∀ x y : ℚ, x ≠ 0 → y ≠ 0 → f (x * y) = f x + f y

theorem LogLike.map_one {f : ℚ → ℚ} (hf : LogLike f) : f 1 = 0 := by
  have h := hf 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  linarith

theorem LogLike.map_inv {f : ℚ → ℚ} (hf : LogLike f) {x : ℚ} (hx : x ≠ 0) : f x⁻¹ = -f x := by
  have h := hf x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, hf.map_one] at h
  linarith

theorem LogLike.map_pow {f : ℚ → ℚ} (hf : LogLike f) {x : ℚ} (hx : x ≠ 0) (n : ℕ) :
    f (x ^ n) = n * f x := by
  induction n with
  | zero => simp [hf.map_one]
  | succ n ih =>
    rw [pow_succ, hf _ _ (pow_ne_zero n hx) hx, ih]
    push_cast
    ring

theorem LogLike.map_zpow {f : ℚ → ℚ} (hf : LogLike f) {x : ℚ} (hx : x ≠ 0) (e : ℤ) :
    f (x ^ e) = e * f x := by
  cases e with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, hf.map_pow hx, Int.cast_natCast]
  | negSucc n =>
    rw [zpow_negSucc, hf.map_inv (pow_ne_zero _ hx), hf.map_pow hx, Int.cast_negSucc]
    ring

theorem LogLike.map_prod {f : ℚ → ℚ} (hf : LogLike f) {n : ℕ} (x : Fin n → ℚ)
    (hx : ∀ i, x i ≠ 0) (e : Fin n → ℤ) :
    f (∏ i, x i ^ e i) = ∑ i, (e i : ℚ) * f (x i) := by
  have key : ∀ s : Finset (Fin n),
      f (∏ i ∈ s, x i ^ e i) = ∑ i ∈ s, (e i : ℚ) * f (x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [hf.map_one]
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        hf _ _ (zpow_ne_zero _ (hx i))
          (Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ (hx j)),
        ih, hf.map_zpow (hx i)]
  exact key Finset.univ

theorem LogLike.map_int_mul {f : ℚ → ℚ} (hf : LogLike f) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    f ((a * b : ℤ) : ℚ) = f (a : ℚ) + f (b : ℚ) := by
  rw [Int.cast_mul]
  exact hf _ _ (Int.cast_ne_zero.2 ha) (Int.cast_ne_zero.2 hb)

/-- The valuation at `r`, as a function `ℚ → ℚ`. -/
noncomputable def val (r : ℕ) (x : ℚ) : ℚ := (padicValRat r x : ℚ)

theorem logLike_val {r : ℕ} (hr : r.Prime) : LogLike (val r) := by
  have := Fact.mk hr
  intro x y hx hy
  rw [val, val, val, padicValRat.mul hx hy, Int.cast_add]

theorem val_of_not_dvd {r : ℕ} {z : ℤ} (h : ¬ (r : ℤ) ∣ z) : val r (z : ℚ) = 0 := by
  rw [val, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd h]
  rfl

theorem val_ne_zero {r : ℕ} (hr : r.Prime) {z : ℤ} (hz : z ≠ 0) (h : (r : ℤ) ∣ z) :
    val r (z : ℚ) ≠ 0 := by
  have := Fact.mk hr
  rw [val, padicValRat.of_int]
  have h1 : (r : ℤ) ^ 1 ∣ z := by simpa using h
  rcases (padicValInt_dvd_iff 1 z).1 h1 with h0 | h0
  · exact absurd h0 hz
  · have h2 : padicValInt r z ≠ 0 := by omega
    exact_mod_cast h2

theorem val_self {r : ℕ} (hr : r.Prime) : val r (r : ℚ) = 1 := by
  rw [val, padicValRat.self hr.one_lt]
  rfl

/-- **One prime, one number.** If the prime `r` divides `z ≠ 0`, subtracting a multiple of the
valuation at `r` from `f` gives a function that is zero at `z` and agrees with `f` at every
integer prime to `r`. If `f z = 0` already, nothing changes. -/
theorem kill_one {f : ℚ → ℚ} (hf : LogLike f) {r : ℕ} (hr : r.Prime) {z : ℤ} (hz : z ≠ 0)
    (hrz : (r : ℤ) ∣ z) :
    ∃ f' : ℚ → ℚ, LogLike f' ∧ f' (z : ℚ) = 0 ∧
      ∀ w : ℤ, f (z : ℚ) = 0 ∨ ¬ (r : ℤ) ∣ w → f' (w : ℚ) = f (w : ℚ) := by
  have hv := val_ne_zero hr hz hrz
  refine ⟨fun x => f x - f (z : ℚ) / val r (z : ℚ) * val r x, ?_, ?_, ?_⟩
  · intro x y hx hy
    change f (x * y) - f (z : ℚ) / val r (z : ℚ) * val r (x * y) =
      f x - f (z : ℚ) / val r (z : ℚ) * val r x + (f y - f (z : ℚ) / val r (z : ℚ) * val r y)
    rw [hf x y hx hy, logLike_val hr x y hx hy]
    ring
  · change f (z : ℚ) - f (z : ℚ) / val r (z : ℚ) * val r (z : ℚ) = 0
    rw [div_mul_cancel₀ _ hv, sub_self]
  · intro w hw
    change f (w : ℚ) - f (z : ℚ) / val r (z : ℚ) * val r (w : ℚ) = f (w : ℚ)
    rcases hw with h0 | hw
    · rw [h0]
      ring
    · rw [val_of_not_dvd hw]
      ring

/-! ## 2. The order of 3 and the base numbers -/

/-- `L_k = 3^(2k+1) - 3^(k+1) + 1`, the first Aurifeuillian factor of `3^(3(2k+1)) + 1`. -/
def L3 (k : ℕ) : ℤ := 3 ^ (2 * k + 1) - 3 ^ (k + 1) + 1

/-- `M_k = 3^(2k+1) + 3^(k+1) + 1`, the second Aurifeuillian factor of `3^(3(2k+1)) + 1`. -/
def M3 (k : ℕ) : ℤ := 3 ^ (2 * k + 1) + 3 ^ (k + 1) + 1

theorem L3_mem (k : ℕ) : L3 k ∈ baseNumbers3 := Or.inr (Or.inr (Or.inl ⟨k, rfl⟩))

theorem M3_mem (k : ℕ) : M3 k ∈ baseNumbers3 := Or.inr (Or.inr (Or.inr ⟨k, rfl⟩))

theorem L3_pos (k : ℕ) : 0 < L3 k := baseNumbers3_pos (L3_mem k)

theorem M3_pos (k : ℕ) : 0 < M3 k := baseNumbers3_pos (M3_mem k)

theorem three_pow_sub_one_ne_zero {m : ℕ} (hm : 0 < m) : (3 : ℤ) ^ m - 1 ≠ 0 := by
  have h : (1 : ℤ) < 3 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
  omega

/-- `3^(6E) - 1 = (3^(3E) - 1) (3^E + 1) L M`, `E = 2k + 1`. -/
theorem pow_six_sub_one (k : ℕ) : (3 : ℤ) ^ (6 * (2 * k + 1)) - 1 =
    (3 ^ (3 * (2 * k + 1)) - 1) * (3 ^ (2 * k + 1) + 1) * (L3 k * M3 k) := by
  unfold L3 M3
  ring

/-- `(3^(6E) - 1) (3^E - 1) = (3^(3E) - 1) (3^(2E) - 1) L M`, `E = 2k + 1`. -/
theorem pow_six_sub_one_mul (k : ℕ) :
    ((3 : ℤ) ^ (6 * (2 * k + 1)) - 1) * (3 ^ (2 * k + 1) - 1) =
      (3 ^ (3 * (2 * k + 1)) - 1) * (3 ^ (2 * (2 * k + 1)) - 1) * (L3 k * M3 k) := by
  unfold L3 M3
  ring

/-- `r` divides `3^m - 1` if and only if the order of 3 modulo `r` divides `m`. -/
theorem dvd_pow_sub_one_iff (r m : ℕ) :
    (r : ℤ) ∣ 3 ^ m - 1 ↔ orderOf (3 : ZMod r) ∣ m := by
  rw [orderOf_dvd_iff_pow_eq_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact sub_eq_zero

theorem orderOf_dvd_of_dvd_L3 {r k : ℕ} (h : (r : ℤ) ∣ L3 k) :
    orderOf (3 : ZMod r) ∣ 6 * (2 * k + 1) := by
  rw [← dvd_pow_sub_one_iff, pow_six_sub_one]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h _) _

theorem orderOf_dvd_of_dvd_M3 {r k : ℕ} (h : (r : ℤ) ∣ M3 k) :
    orderOf (3 : ZMod r) ∣ 6 * (2 * k + 1) := by
  rw [← dvd_pow_sub_one_iff, pow_six_sub_one]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h _) _

theorem orderOf_three_zmod_two : orderOf (3 : ZMod 2) = 1 := by
  have h : (3 : ZMod 2) = 1 := by decide
  rw [h, orderOf_one]

theorem orderOf_three_zmod_three : orderOf (3 : ZMod 3) = 0 := by
  have h : (3 : ZMod 3) = 0 := by decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [h, orderOf_zero]

/-- The order of 3 modulo a prime other than 3 is positive. -/
theorem orderOf_three_pos {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    0 < orderOf (3 : ZMod p) := by
  have := Fact.mk hp
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have h1 : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      ((ZMod.natCast_eq_zero_iff 3 p).1 h1))
  have hp1 := hp.two_le
  exact orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨p - 1, by omega, ZMod.pow_card_sub_one_eq_one h3⟩)

/-- A common prime factor of `L_k` and `M_k` is 2 or 3 (in fact there is none). -/
theorem eq_two_or_three_of_dvd {r k : ℕ} (hr : r.Prime) (hL : (r : ℤ) ∣ L3 k)
    (hM : (r : ℤ) ∣ M3 k) : r = 2 ∨ r = 3 := by
  have h1 : (r : ℤ) ∣ 2 * 3 ^ (k + 1) := by
    have h2 := dvd_sub hM hL
    have e : M3 k - L3 k = 2 * 3 ^ (k + 1) := by
      unfold L3 M3
      ring
    rwa [e] at h2
  have h3 : r ∣ 2 * 3 ^ (k + 1) := by exact_mod_cast h1
  rcases (Nat.Prime.dvd_mul hr).1 h3 with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow h))

/-- A prime at which 3 has order at least 2 does not divide both `L_k` and `M_k`. -/
theorem not_dvd_L3_M3 {r k : ℕ} (hr : r.Prime) (hord : 1 < orderOf (3 : ZMod r))
    (hL : (r : ℤ) ∣ L3 k) (hM : (r : ℤ) ∣ M3 k) : False := by
  rcases eq_two_or_three_of_dvd hr hL hM with rfl | rfl
  · rw [orderOf_three_zmod_two] at hord
    omega
  · rw [orderOf_three_zmod_three] at hord
    omega

/-- The base numbers of index at most `N`: `3`, the numbers `3^m - 1` with `1 ≤ m ≤ N`, and
`L_k`, `M_k` with `6 (2k+1) ≤ N`. -/
def baseUpTo (N : ℕ) : Set ℤ :=
  {g | g = 3 ∨ (∃ m : ℕ, 0 < m ∧ m ≤ N ∧ g = 3 ^ m - 1) ∨
    (∃ k : ℕ, 6 * (2 * k + 1) ≤ N ∧ g = L3 k) ∨ ∃ k : ℕ, 6 * (2 * k + 1) ≤ N ∧ g = M3 k}

theorem baseUpTo_mono {N N' : ℕ} (h : N ≤ N') : baseUpTo N ⊆ baseUpTo N' := by
  rintro g (rfl | ⟨m, hm, hmN, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨m, hm, by omega, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨k, by omega, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨k, by omega, rfl⟩))

/-- Every base number has an index. -/
theorem exists_baseUpTo {g : ℤ} (hg : g ∈ baseNumbers3) : ∃ N, g ∈ baseUpTo N := by
  rcases hg with rfl | ⟨m, hm, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨0, Or.inl rfl⟩
  · exact ⟨m, Or.inr (Or.inl ⟨m, hm, le_rfl, rfl⟩)⟩
  · exact ⟨6 * (2 * k + 1), Or.inr (Or.inr (Or.inl ⟨k, le_rfl, rfl⟩))⟩
  · exact ⟨6 * (2 * k + 1), Or.inr (Or.inr (Or.inr ⟨k, le_rfl, rfl⟩))⟩

/-- A prime at which 3 has order greater than `N` divides no base number of index at most
`N`. -/
theorem not_dvd_baseUpTo {r : ℕ} (hr : r.Prime) {N : ℕ} (hN : N < orderOf (3 : ZMod r))
    {g : ℤ} (hg : g ∈ baseUpTo N) : ¬ (r : ℤ) ∣ g := by
  rcases hg with rfl | ⟨m, hm, hmN, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · intro h
    have h1 : r ∣ 3 := by exact_mod_cast h
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h1
    rw [orderOf_three_zmod_three] at hN
    omega
  · intro h
    have := Nat.le_of_dvd hm ((dvd_pow_sub_one_iff r m).1 h)
    omega
  · intro h
    have := Nat.le_of_dvd (by omega) (orderOf_dvd_of_dvd_L3 h)
    omega
  · intro h
    have := Nat.le_of_dvd (by omega) (orderOf_dvd_of_dvd_M3 h)
    omega

/-! ## 3. Killing the base numbers, index by index -/

/-- `f` is zero on every base number of index at most `N`. -/
def Kills (f : ℚ → ℚ) (N : ℕ) : Prop := ∀ g ∈ baseUpTo N, f (g : ℚ) = 0

/-- **One step.** Let `f` be zero on the base numbers of index at most `N`, and let `f z = 0`
or let `z` be divisible by a prime `r` at which 3 has order greater than `N`. Then some `f'`
is zero on these base numbers and at `z`, and agrees with `f` at the integers prime to
`r`. -/
theorem kill_or {f : ℚ → ℚ} (hf : LogLike f) {N : ℕ} (hK : Kills f N) {r : ℕ} (hr : r.Prime)
    {z : ℤ} (hz : z ≠ 0)
    (h : f (z : ℚ) = 0 ∨ (N < orderOf (3 : ZMod r) ∧ (r : ℤ) ∣ z)) :
    ∃ f' : ℚ → ℚ, LogLike f' ∧ Kills f' N ∧ f' (z : ℚ) = 0 ∧
      ∀ w : ℤ, f (z : ℚ) = 0 ∨ ¬ (r : ℤ) ∣ w → f' (w : ℚ) = f (w : ℚ) := by
  rcases h with h0 | ⟨hord, hrz⟩
  · exact ⟨f, hf, hK, h0, fun _ _ => rfl⟩
  · obtain ⟨f', hf', hz', hw⟩ := kill_one hf hr hz hrz
    refine ⟨f', hf', fun g hg => ?_, hz', hw⟩
    rw [hw g (Or.inr (not_dvd_baseUpTo hr hord hg))]
    exact hK g hg

/-- The index 2 needs no prime: `3^2 - 1 = (3 - 1)^3`. -/
theorem kills_two {f : ℚ → ℚ} (hf : LogLike f) (hK : Kills f 1) : Kills f 2 := by
  intro g hg
  rcases hg with rfl | ⟨m, hm, hm2, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact hK 3 (Or.inl rfl)
  · have h1 : f (((3 : ℤ) ^ 1 - 1 : ℤ) : ℚ) = 0 :=
      hK _ (Or.inr (Or.inl ⟨1, one_pos, le_rfl, rfl⟩))
    rcases (by omega : m = 1 ∨ m = 2) with rfl | rfl
    · exact h1
    · have e : (((3 : ℤ) ^ 2 - 1 : ℤ) : ℚ) = (((3 : ℤ) ^ 1 - 1 : ℤ) : ℚ) ^ 3 := by norm_num
      rw [e, hf.map_pow (by norm_num), h1, mul_zero]
  · omega
  · omega

/-- **An index that is not 6 modulo 12.** A prime `r` at which 3 has order `N + 1` takes care
of `3^(N+1) - 1`. -/
theorem step_full {f : ℚ → ℚ} (hf : LogLike f) {N : ℕ} (hK : Kills f N)
    (h12 : (N + 1) % 12 ≠ 6) {r : ℕ} (hr : r.Prime) (hord : orderOf (3 : ZMod r) = N + 1) :
    ∃ f' : ℚ → ℚ, LogLike f' ∧ Kills f' (N + 1) ∧
      ∀ w : ℤ, ¬ (r : ℤ) ∣ w → f' (w : ℚ) = f (w : ℚ) := by
  have hrz : (r : ℤ) ∣ 3 ^ (N + 1) - 1 := (dvd_pow_sub_one_iff r (N + 1)).2 (by rw [hord])
  obtain ⟨f', hf', hK', hz', hw⟩ := kill_or hf hK hr
    (three_pow_sub_one_ne_zero (Nat.succ_pos N)) (Or.inr ⟨by omega, hrz⟩)
  refine ⟨f', hf', ?_, fun w hw' => hw w (Or.inr hw')⟩
  intro g hg
  rcases hg with rfl | ⟨m, hm, hmN, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact hK' 3 (Or.inl rfl)
  · rcases Nat.lt_or_ge m (N + 1) with h | h
    · exact hK' _ (Or.inr (Or.inl ⟨m, hm, by omega, rfl⟩))
    · obtain rfl : m = N + 1 := by omega
      exact hz'
  · exact hK' _ (Or.inr (Or.inr (Or.inl ⟨k, by omega, rfl⟩)))
  · exact hK' _ (Or.inr (Or.inr (Or.inr ⟨k, by omega, rfl⟩)))

/-- **An index `N + 1 = 6 (2j+1)`.** For each of `L_j`, `M_j`: either `f` is zero there, or a
prime at which 3 has order `N + 1` divides it. Then some `f'` is zero on the base numbers of
index at most `N + 1`, and agrees with `f` at the integers prime to the two primes. -/
theorem step_half {f : ℚ → ℚ} (hf : LogLike f) {N j : ℕ} (hK : Kills f N)
    (hN : N + 1 = 6 * (2 * j + 1)) {rL rM : ℕ} (hrL : rL.Prime) (hrM : rM.Prime)
    (hL : f (L3 j : ℚ) = 0 ∨ (orderOf (3 : ZMod rL) = N + 1 ∧ (rL : ℤ) ∣ L3 j))
    (hM : f (M3 j : ℚ) = 0 ∨ (orderOf (3 : ZMod rM) = N + 1 ∧ (rM : ℤ) ∣ M3 j)) :
    ∃ f' : ℚ → ℚ, LogLike f' ∧ Kills f' (N + 1) ∧
      ∀ w : ℤ, ¬ (rL : ℤ) ∣ w → ¬ (rM : ℤ) ∣ w → f' (w : ℚ) = f (w : ℚ) := by
  -- `L_j`
  obtain ⟨f₁, hf₁, hK₁, hL₁, hw₁⟩ := kill_or hf hK hrL (L3_pos j).ne'
    (hL.imp_right fun h => ⟨by omega, h.2⟩)
  have hML : f (L3 j : ℚ) = 0 ∨ ¬ (rL : ℤ) ∣ M3 j := by
    rcases hL with h | ⟨ho, hd⟩
    · exact Or.inl h
    · exact Or.inr fun hdM => not_dvd_L3_M3 hrL (by omega) hd hdM
  have hM₁ : f₁ (M3 j : ℚ) = 0 ∨ (N < orderOf (3 : ZMod rM) ∧ (rM : ℤ) ∣ M3 j) := by
    rcases hM with h | ⟨ho, hd⟩
    · left
      rw [hw₁ _ hML]
      exact h
    · exact Or.inr ⟨by omega, hd⟩
  -- `M_j`
  obtain ⟨f₂, hf₂, hK₂, hM₂, hw₂⟩ := kill_or hf₁ hK₁ hrM (M3_pos j).ne' hM₁
  have hL₂ : f₂ (L3 j : ℚ) = 0 := by
    have h : f₁ (M3 j : ℚ) = 0 ∨ ¬ (rM : ℤ) ∣ L3 j := by
      rcases hM with h | ⟨ho, hd⟩
      · left
        rw [hw₁ _ hML]
        exact h
      · exact Or.inr fun hdL => not_dvd_L3_M3 hrM (by omega) hdL hd
    rw [hw₂ _ h]
    exact hL₁
  refine ⟨f₂, hf₂, ?_, fun w h1 h2 => by rw [hw₂ w (Or.inr h2), hw₁ w (Or.inr h1)]⟩
  -- `3^(N+1) - 1`
  have hA : f₂ (((3 : ℤ) ^ (N + 1) - 1 : ℤ) : ℚ) = 0 := by
    have hE : f₂ (((3 : ℤ) ^ (2 * j + 1) - 1 : ℤ) : ℚ) = 0 :=
      hK₂ _ (Or.inr (Or.inl ⟨2 * j + 1, by omega, by omega, rfl⟩))
    have h2E : f₂ (((3 : ℤ) ^ (2 * (2 * j + 1)) - 1 : ℤ) : ℚ) = 0 :=
      hK₂ _ (Or.inr (Or.inl ⟨2 * (2 * j + 1), by omega, by omega, rfl⟩))
    have h3E : f₂ (((3 : ℤ) ^ (3 * (2 * j + 1)) - 1 : ℤ) : ℚ) = 0 :=
      hK₂ _ (Or.inr (Or.inl ⟨3 * (2 * j + 1), by omega, by omega, rfl⟩))
    have e := congrArg (fun z : ℤ => f₂ (z : ℚ)) (pow_six_sub_one_mul j)
    rw [hf₂.map_int_mul (three_pow_sub_one_ne_zero (by omega))
        (three_pow_sub_one_ne_zero (by omega)),
      hf₂.map_int_mul (mul_ne_zero (three_pow_sub_one_ne_zero (by omega))
        (three_pow_sub_one_ne_zero (by omega))) (mul_ne_zero (L3_pos j).ne' (M3_pos j).ne'),
      hf₂.map_int_mul (three_pow_sub_one_ne_zero (by omega))
        (three_pow_sub_one_ne_zero (by omega)),
      hf₂.map_int_mul (L3_pos j).ne' (M3_pos j).ne', hE, h2E, h3E, hL₂, hM₂] at e
    rw [hN]
    linarith
  intro g hg
  rcases hg with rfl | ⟨m, hm, hmN, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact hK₂ 3 (Or.inl rfl)
  · rcases Nat.lt_or_ge m (N + 1) with h | h
    · exact hK₂ _ (Or.inr (Or.inl ⟨m, hm, by omega, rfl⟩))
    · obtain rfl : m = N + 1 := by omega
      exact hA
  · rcases Nat.lt_or_ge (6 * (2 * k + 1)) (N + 1) with h | h
    · exact hK₂ _ (Or.inr (Or.inr (Or.inl ⟨k, by omega, rfl⟩)))
    · obtain rfl : k = j := by omega
      exact hL₂
  · rcases Nat.lt_or_ge (6 * (2 * k + 1)) (N + 1) with h | h
    · exact hK₂ _ (Or.inr (Or.inr (Or.inr ⟨k, by omega, rfl⟩)))
    · obtain rfl : k = j := by omega
      exact hM₂

/-- **All the larger indices.** A function that is zero on the base numbers of index at most
`n` can be changed, without changing its value at a prime `p` at which 3 has order at most
`n`, into one that is zero on the base numbers of index at most `N`. -/
theorem exists_kills_above {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n)
    (hpn : orderOf (3 : ZMod p) ≤ n) {f : ℚ → ℚ} (hf : LogLike f) (hK : Kills f n) (N : ℕ)
    (hN : n ≤ N) :
    ∃ f' : ℚ → ℚ, LogLike f' ∧ Kills f' N ∧ f' (p : ℚ) = f (p : ℚ) := by
  induction N, hN using Nat.le_induction with
  | base => exact ⟨f, hf, hK, rfl⟩
  | succ N hN ih =>
    obtain ⟨f₁, hf₁, hK₁, hp₁⟩ := ih
    -- a prime at which 3 has order `N + 1` is not `p`
    have hne : ∀ r : ℕ, r.Prime → orderOf (3 : ZMod r) = N + 1 → ¬ (r : ℤ) ∣ (p : ℤ) := by
      intro r hr hord hdvd
      have h1 : r ∣ p := by exact_mod_cast hdvd
      rw [(Nat.prime_dvd_prime_iff_eq hr hp).1 h1] at hord
      omega
    have hcast : ∀ h : ℚ → ℚ, h ((p : ℤ) : ℚ) = h (p : ℚ) := fun h => by rw [Int.cast_natCast]
    by_cases h12 : (N + 1) % 12 = 6
    · obtain ⟨j, hj⟩ : ∃ j, N + 1 = 6 * (2 * j + 1) := ⟨(N + 1) / 12, by omega⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · -- the index 6: `L = 1` and `M = 7`
        have h7 : Nat.Prime 7 := by norm_num
        have ho7 : orderOf (3 : ZMod 7) = N + 1 := by rw [orderOf_three_zmod_seven]; omega
        have hL1 : f₁ ((L3 0 : ℤ) : ℚ) = 0 := by
          have e : L3 0 = 1 := by norm_num [L3]
          rw [e, Int.cast_one]
          exact hf₁.map_one
        obtain ⟨f₂, hf₂, hK₂, hw⟩ := step_half hf₁ hK₁ hj h7 h7 (Or.inl hL1)
          (Or.inr ⟨ho7, by norm_num [M3]⟩)
        refine ⟨f₂, hf₂, hK₂, ?_⟩
        rw [← hp₁, ← hcast f₂, ← hcast f₁]
        exact hw p (hne 7 h7 ho7) (hne 7 h7 ho7)
      · obtain ⟨⟨rL, hrL, hoL, hdL⟩, ⟨rM, hrM, hoM, hdM⟩⟩ := primitiveHalves3 j hj0
        obtain ⟨f₂, hf₂, hK₂, hw⟩ := step_half hf₁ hK₁ hj hrL hrM
          (Or.inr ⟨hoL.trans hj.symm, hdL⟩) (Or.inr ⟨hoM.trans hj.symm, hdM⟩)
        refine ⟨f₂, hf₂, hK₂, ?_⟩
        rw [← hp₁, ← hcast f₂, ← hcast f₁]
        exact hw p (hne rL hrL (hoL.trans hj.symm)) (hne rM hrM (hoM.trans hj.symm))
    · rcases Nat.lt_or_ge (N + 1) 3 with hlt | hge
      · -- the index 2
        obtain rfl : N = 1 := by omega
        exact ⟨f₁, hf₁, kills_two hf₁ hK₁, hp₁⟩
      · obtain ⟨r, hr, hord⟩ := exists_prime_order_three hge
        obtain ⟨f₂, hf₂, hK₂, hw⟩ := step_full hf₁ hK₁ h12 hr hord
        refine ⟨f₂, hf₂, hK₂, ?_⟩
        rw [← hp₁, ← hcast f₂, ← hcast f₁]
        exact hw p (hne r hr hord)

/-! ## 4. Two primes in one primitive part -/

/-- **The function.** Let `p ≠ 3` and `q ≠ p` be primes at which 3 has the same order `n`; if
`n = 6 (2j+1)`, let them divide the same one of `L_j`, `M_j`. Then for every `N` there is a
function `f` with `f (x y) = f x + f y` that is zero on the base numbers of index at most `N`
and not at `p`. -/
theorem exists_logLike_of_partner {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (hp3 : p ≠ 3) (hord : orderOf (3 : ZMod q) = orderOf (3 : ZMod p))
    (hhalf : ∀ j : ℕ, orderOf (3 : ZMod p) = 6 * (2 * j + 1) →
      ((p : ℤ) ∣ L3 j ∧ (q : ℤ) ∣ L3 j) ∨ ((p : ℤ) ∣ M3 j ∧ (q : ℤ) ∣ M3 j)) (N : ℕ) :
    ∃ f : ℚ → ℚ, LogLike f ∧ Kills f N ∧ f (p : ℚ) ≠ 0 := by
  obtain ⟨n, hn⟩ : ∃ n, orderOf (3 : ZMod p) = n := ⟨_, rfl⟩
  have hn0 : 0 < n := hn ▸ orderOf_three_pos hp hp3
  obtain ⟨N₀, rfl⟩ : ∃ N₀, n = N₀ + 1 := ⟨n - 1, by omega⟩
  have hf₀ : LogLike (val p) := logLike_val hp
  have hK₀ : Kills (val p) N₀ := fun g hg =>
    val_of_not_dvd (not_dvd_baseUpTo hp (by omega) hg)
  have hqp' : ¬ (q : ℤ) ∣ (p : ℤ) := by
    intro h
    have h1 : q ∣ p := by exact_mod_cast h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 h1)
  have hcast : ∀ h : ℚ → ℚ, h ((p : ℤ) : ℚ) = h (p : ℚ) := fun h => by rw [Int.cast_natCast]
  -- the index `n`, with the prime `q`
  obtain ⟨f₁, hf₁, hK₁, hp₁⟩ :
      ∃ f₁ : ℚ → ℚ, LogLike f₁ ∧ Kills f₁ (N₀ + 1) ∧ f₁ (p : ℚ) = 1 := by
    by_cases h12 : (N₀ + 1) % 12 = 6
    · obtain ⟨j, hj⟩ : ∃ j, N₀ + 1 = 6 * (2 * j + 1) := ⟨(N₀ + 1) / 12, by omega⟩
      have h1 : 1 < orderOf (3 : ZMod p) := by omega
      rcases hhalf j (hn.trans hj) with ⟨hpL, hqL⟩ | ⟨hpM, hqM⟩
      · obtain ⟨f₁, hf₁, hK₁, hw⟩ := step_half hf₀ hK₀ hj hq hq
          (Or.inr ⟨hord.trans hn, hqL⟩)
          (Or.inl (val_of_not_dvd fun hpM => not_dvd_L3_M3 hp h1 hpL hpM))
        refine ⟨f₁, hf₁, hK₁, ?_⟩
        rw [← val_self hp, ← hcast f₁, ← hcast (val p)]
        exact hw p hqp' hqp'
      · obtain ⟨f₁, hf₁, hK₁, hw⟩ := step_half hf₀ hK₀ hj hq hq
          (Or.inl (val_of_not_dvd fun hpL => not_dvd_L3_M3 hp h1 hpL hpM))
          (Or.inr ⟨hord.trans hn, hqM⟩)
        refine ⟨f₁, hf₁, hK₁, ?_⟩
        rw [← val_self hp, ← hcast f₁, ← hcast (val p)]
        exact hw p hqp' hqp'
    · obtain ⟨f₁, hf₁, hK₁, hw⟩ := step_full hf₀ hK₀ h12 hq (hord.trans hn)
      refine ⟨f₁, hf₁, hK₁, ?_⟩
      rw [← val_self hp, ← hcast f₁, ← hcast (val p)]
      exact hw p hqp'
  -- the larger indices
  obtain ⟨f₂, hf₂, hK₂, hp₂⟩ := exists_kills_above hp (Nat.succ_pos N₀) hn.le hf₁ hK₁
    (max N (N₀ + 1)) (le_max_right _ _)
  refine ⟨f₂, hf₂, fun g hg => hK₂ g (baseUpTo_mono (le_max_left _ _) hg), ?_⟩
  rw [hp₂, hp₁]
  exact one_ne_zero

/-- **No relation.** Under the same hypotheses, no power `p^k`, `k ≥ 1`, is a product of
integer powers of base numbers. -/
theorem no_power_of_partner {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (hp3 : p ≠ 3) (hord : orderOf (3 : ZMod q) = orderOf (3 : ZMod p))
    (hhalf : ∀ j : ℕ, orderOf (3 : ZMod p) = 6 * (2 * j + 1) →
      ((p : ℤ) ∣ L3 j ∧ (q : ℤ) ∣ L3 j) ∨ ((p : ℤ) ∣ M3 j ∧ (q : ℤ) ∣ M3 j))
    {k : ℕ} (hk : 0 < k) {m : ℕ} {g e : Fin m → ℤ} (hg : ∀ i, g i ∈ baseNumbers3) :
    (p : ℚ) ^ k ≠ ∏ i, (g i : ℚ) ^ e i := by
  intro h
  choose Ni hNi using fun i => exists_baseUpTo (hg i)
  obtain ⟨f, hf, hK, hfp⟩ := exists_logLike_of_partner hp hq hqp hp3 hord hhalf (∑ i, Ni i)
  have h1 : f ((p : ℚ) ^ k) = k * f (p : ℚ) :=
    hf.map_pow (by exact_mod_cast hp.ne_zero) k
  have h2 : f (∏ i, (g i : ℚ) ^ e i) = 0 := by
    rw [hf.map_prod _ (fun i => by exact_mod_cast (baseNumbers3_pos (hg i)).ne') e]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hK (g i) (baseUpTo_mono
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (hNi i)),
      mul_zero]
  rw [h, h2] at h1
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  exact mul_ne_zero hk' hfp h1.symm

/-- **Two primes in one primitive part exclude each other** (from Baker's theorem). Let
`p ≠ 3` and `q ≠ p` be primes at which 3 has the same order `n`; if `n = 6 (2j+1)`, let `p`
and `q` divide the same one of `L_j = 3^(2j+1) - 3^(j+1) + 1`, `M_j = 3^(2j+1) + 3^(j+1) + 1`.
Then `log p` is not a value of the class F3. -/
theorem not_isF3Value_log_of_same_part (hB : BakerTheorem) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hqp : q ≠ p) (hp3 : p ≠ 3)
    (hord : orderOf (3 : ZMod q) = orderOf (3 : ZMod p))
    (hhalf : ∀ j : ℕ, orderOf (3 : ZMod p) = 6 * (2 * j + 1) →
      ((p : ℤ) ∣ L3 j ∧ (q : ℤ) ∣ L3 j) ∨ ((p : ℤ) ∣ M3 j ∧ (q : ℤ) ∣ M3 j)) :
    ¬ IsF3Value (Real.log p) := by
  intro hval
  have hy : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
  have hval' : IsF3Value (Real.log ((p : ℚ) : ℝ)) := by
    rw [Rat.cast_natCast]
    exact hval
  obtain ⟨k, hk, m, g, e, hg, hrel⟩ := (isF3Value_log_rat_iff_pow hB hy).1 hval'
  exact no_power_of_partner hp hq hqp hp3 hord hhalf hk hg hrel

end Base3

end PiFormula
