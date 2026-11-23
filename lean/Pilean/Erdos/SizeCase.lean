import Pilean.Erdos.Final
import Pilean.Erdos.EvenCase

/-!
# Erdős's conjecture when `∏_{p ∣ q} p/(p-1) ≤ 2` (Okada's size condition)

Let `P(q) = ∏_{p ∣ q} p/(p-1) = q/φ(q)` (`sizeProd`, a rational number; `sizeProd_eq_div`).

**Theorem** (`erdos_size_nat`; T. Okada, 1982; the condition is usually quoted as
`2 φ(q) + 1 > q`). Let `q ≥ 2` with `P(q) ≤ 2`, i.e. `q ≤ 2 φ(q)` (`sizeProd_le_two_iff`), and
let `f : ℕ → ℤ` have period `q`, with `f(n) = 0` when `q ∣ n` and `f(n) = ±1` otherwise. Then
the partial sums `∑_{1 ≤ n < N} f(n)/n` do not tend to `0`.

This covers every prime power (`sizeProd_prime_pow_le`, `erdos_prime_pow_nat`; for prime `q`
the conjecture is due to Baker, Birch and Wirsing, 1973) and, for example,
`q = 225, 441, 1225`: every odd square below `11025 = 105²` (`sizeProd_le_two_of_lt` in
`Summary.lean`). Other forms of the size condition are in T. Chatterjee and M. R. Murty
(2015).

Proof. The sum of `1/m` over `m ∈ M(q)` (the `m ≥ 1` all of whose prime factors divide `q`)
is `P(q)` (`hasSum_inv_inM`, an Euler product). In `g(a) = ∑_{m ∈ M(q)} f(a m)/m` the term
`m = 1` is `f(a)` and the term `m = q` is `0`, so for `|f| ≤ 1` with `f(0) = 0`

  `|g(a) - f(a)| ≤ P(q) - 1 - 1/q`   (`abs_okadaG_sub_le`).

If `f(a) = ±1` and `P(q) ≤ 2` this gives `g(a) ≠ 0` (`okadaG_ne_zero_of_sizeProd_le`), so
condition (a) of Okada's criterion fails at `a = 1` (`not_condA_of_sizeProd_le`), and the sum
is not `0` by `okadaOnlyIf` (odd `q`) or by divergence (even `q`, `erdos_even`).
-/

open scoped BigOperators

open Filter

namespace PiFormula

namespace Erdos

/-! ## 1. The Euler product `∑_{m ∈ M(q)} 1/m = ∏_{p ∣ q} p/(p-1)` -/

/-- `P(q) = ∏_{p ∣ q} p/(p-1)`, the sum of `1/m` over the `m ≥ 1` all of whose prime factors
divide `q`. It is equal to `q/φ(q)`. -/
def sizeProd (q : ℕ) : ℚ := ∏ p ∈ q.primeFactors, (p : ℚ) / ((p : ℚ) - 1)

/-- The monoid homomorphism `j ↦ 1/j` from `ℕ` to `ℝ`. -/
noncomputable def invHom : ℕ →* ℝ where
  toFun := fun j => ((j : ℝ))⁻¹
  map_one' := by simp
  map_mul' := by
    intro a b
    simp [mul_comm]

theorem inM_iff_mem_factoredNumbers (q j : ℕ) :
    InM q j ↔ j ∈ Nat.factoredNumbers q.primeFactors :=
  Nat.mem_factoredNumbers_iff_primeFactors_subset.symm

theorem sizeProd_cast (q : ℕ) :
    ∏ p ∈ q.primeFactors, (1 - ((p : ℝ))⁻¹)⁻¹ = ((sizeProd q : ℚ) : ℝ) := by
  unfold sizeProd
  rw [Rat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have h1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (ne_of_gt hp1)
  have h2 : (p : ℝ) ≠ 0 := by linarith
  push_cast
  field_simp

/-- **The Euler product.** The sum of `1/m` over `m ∈ M(q)` is `∏_{p ∣ q} p/(p-1)`. -/
theorem hasSum_inv_inM (q : ℕ) :
    HasSum (fun m : ℕ => if InM q m then ((m : ℝ))⁻¹ else 0) ((sizeProd q : ℚ) : ℝ) := by
  have hφ : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    change ‖((p : ℝ))⁻¹‖ < 1
    rw [norm_inv, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    hφ q.primeFactors).2
  have hfilter : q.primeFactors.filter (fun p => p.Prime) = q.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [hfilter] at h
  have h' : HasSum ((fun j : ℕ => ((j : ℝ))⁻¹) ∘
      (Subtype.val : Nat.factoredNumbers q.primeFactors → ℕ))
      (∏ p ∈ q.primeFactors, (1 - ((p : ℝ))⁻¹)⁻¹) := h
  rw [hasSum_subtype_iff_indicator, sizeProd_cast] at h'
  have e : (fun m : ℕ => if InM q m then ((m : ℝ))⁻¹ else 0) =
      (Nat.factoredNumbers q.primeFactors : Set ℕ).indicator (fun j : ℕ => ((j : ℝ))⁻¹) := by
    funext m
    by_cases hm : InM q m
    · rw [Set.indicator_of_mem ((inM_iff_mem_factoredNumbers q m).1 hm)]
      simp only [hm, ↓reduceIte]
    · rw [Set.indicator_of_notMem (mt (inM_iff_mem_factoredNumbers q m).2 hm)]
      simp only [hm, ↓reduceIte]
  rw [e]
  exact h'

/-- `P(q) = q/φ(q)`. -/
theorem sizeProd_eq_div (q : ℕ) (hq : q ≠ 0) : sizeProd q = (q : ℚ) / (q.totient : ℚ) := by
  have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hne : ∀ p ∈ q.primeFactors, (1 - ((p : ℚ))⁻¹) ≠ 0 := by
    intro p hp
    have hp1 : (1 : ℚ) < (p : ℚ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have h := inv_lt_one_of_one_lt₀ hp1
    exact sub_ne_zero.2 (ne_of_gt h)
  have h1 : sizeProd q = (∏ p ∈ q.primeFactors, (1 - ((p : ℚ))⁻¹))⁻¹ := by
    unfold sizeProd
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : (1 : ℚ) < (p : ℚ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have h1 : (p : ℚ) - 1 ≠ 0 := sub_ne_zero.2 (ne_of_gt hp1)
    have h2 : (p : ℚ) ≠ 0 := by linarith
    field_simp
  have hprod : (∏ p ∈ q.primeFactors, (1 - ((p : ℚ))⁻¹)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 hne
  rw [h1, Nat.totient_eq_mul_prod_factors q]
  field_simp

/-- The size condition `P(q) ≤ 2` says `q ≤ 2 φ(q)` (Okada's `2 φ(q) + 1 > q`). -/
theorem sizeProd_le_two_iff (q : ℕ) (hq : q ≠ 0) : sizeProd q ≤ 2 ↔ q ≤ 2 * q.totient := by
  have hφ : (0 : ℚ) < (q.totient : ℚ) := Nat.cast_pos.2 (Nat.totient_pos.2 (by omega))
  rw [sizeProd_eq_div q hq, div_le_iff₀ hφ]
  exact_mod_cast Iff.rfl

/-! ## 2. The bound on `g(a) - f(a)` -/

/-- The series `g(a) = ∑_{m ∈ M(q)} f(a m)/m`, as a `HasSum`. -/
theorem hasSum_okadaG {q : ℕ} [NeZero q] (f : ZMod q → ℚ) (a : ZMod q) :
    HasSum (fun m : ℕ => if InM q m then (f (a * (m : ZMod q)) : ℝ) / (m : ℝ) else 0)
      (okadaG q f a) := by
  have hsum : Summable (fun m : ℕ =>
      if InM q m then (f (a * (m : ZMod q)) : ℝ) / (m : ℝ) else 0) := by
    refine (Arith.summable_serH f q.primeFactors (fun j => a * (j : ZMod q))).congr fun j => ?_
    by_cases h : InM q j
    · simp only [h, (inM_iff_mem_factoredNumbers q j).1 h, ↓reduceIte]
    · simp only [h, mt (inM_iff_mem_factoredNumbers q j).2 h, ↓reduceIte]
  exact hsum.hasSum

/-- The two terms `m = 1` and `m = q` of `∑_{m ∈ M(q)} (1 + s f(a m))/m`, for `s = ±1`. -/
theorem size_key {q : ℕ} (hq : 2 ≤ q) (f : ZMod q → ℚ) (h0 : f 0 = 0)
    (hbd : ∀ r : ZMod q, |f r| ≤ 1) (a : ZMod q) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    1 + s * (f a : ℝ) + 1 / (q : ℝ) ≤ ((sizeProd q : ℚ) : ℝ) + s * okadaG q f a := by
  have : NeZero q := ⟨by omega⟩
  have hD := (hasSum_inv_inM q).add ((hasSum_okadaG f a).mul_left s)
  have hbdR : ∀ r : ZMod q, |(f r : ℝ)| ≤ 1 := by
    intro r
    have h := hbd r
    exact_mod_cast h
  have hnn : ∀ m : ℕ, 0 ≤ (if InM q m then ((m : ℝ))⁻¹ else 0) +
      s * (if InM q m then (f (a * (m : ZMod q)) : ℝ) / (m : ℝ) else 0) := by
    intro m
    by_cases hm : InM q m
    · simp only [hm, ↓reduceIte]
      have h1 := abs_le.1 (hbdR (a * (m : ZMod q)))
      have hm0 : (0 : ℝ) ≤ ((m : ℝ))⁻¹ := inv_nonneg.2 (Nat.cast_nonneg m)
      have e : ((m : ℝ))⁻¹ + s * ((f (a * (m : ZMod q)) : ℝ) / (m : ℝ)) =
          (1 + s * (f (a * (m : ZMod q)) : ℝ)) * ((m : ℝ))⁻¹ := by ring
      rw [e]
      refine mul_nonneg ?_ hm0
      rcases hs with rfl | rfl <;> linarith [h1.1, h1.2]
    · simp only [hm, ↓reduceIte, mul_zero, add_zero, le_refl]
  have hle := sum_le_hasSum ({1, q} : Finset ℕ) (fun m _ => hnn m) hD
  have h1q : (1 : ℕ) ≠ q := by omega
  have hM1 : InM q 1 := ⟨one_ne_zero, by simp⟩
  have hMq : InM q q := ⟨by omega, subset_rfl⟩
  rw [Finset.sum_pair h1q] at hle
  simp only [hM1, hMq, ↓reduceIte, Nat.cast_one, mul_one, inv_one, div_one, ZMod.natCast_self,
    mul_zero, h0, Rat.cast_zero, zero_div, add_zero] at hle
  rw [one_div]
  linarith

/-- **The size bound.** For `q ≥ 2` and `f` on `ℤ/q` with `f(0) = 0` and `|f| ≤ 1`:
`|g(a) - f(a)| ≤ P(q) - 1 - 1/q`, where `g(a) - f(a) = ∑_{m ∈ M(q), m > 1} f(a m)/m`. -/
theorem abs_okadaG_sub_le {q : ℕ} (hq : 2 ≤ q) (f : ZMod q → ℚ) (h0 : f 0 = 0)
    (hbd : ∀ r : ZMod q, |f r| ≤ 1) (a : ZMod q) :
    |okadaG q f a - (f a : ℝ)| ≤ ((sizeProd q : ℚ) : ℝ) - 1 - 1 / (q : ℝ) := by
  have h1 := size_key hq f h0 hbd a (s := 1) (Or.inl rfl)
  have h2 := size_key hq f h0 hbd a (s := -1) (Or.inr rfl)
  rw [abs_le]
  constructor <;> linarith

/-- If `P(q) ≤ 2`, `f(0) = 0` and `f(r) = ±1` otherwise, then `g(a) ≠ 0` for every `a ≠ 0`. -/
theorem okadaG_ne_zero_of_sizeProd_le {q : ℕ} (hq : 2 ≤ q) (f : ZMod q → ℚ) (h0 : f 0 = 0)
    (hpm : ∀ r : ZMod q, r ≠ 0 → f r = 1 ∨ f r = -1) (hP : sizeProd q ≤ 2) (a : ZMod q)
    (ha : a ≠ 0) : okadaG q f a ≠ 0 := by
  have hbd : ∀ r : ZMod q, |f r| ≤ 1 := by
    intro r
    by_cases hr : r = 0
    · rw [hr, h0]
      norm_num
    · rcases hpm r hr with h | h <;> rw [h] <;> norm_num
  have h := abs_okadaG_sub_le hq f h0 hbd a
  have hPR : ((sizeProd q : ℚ) : ℝ) ≤ 2 := by exact_mod_cast hP
  have hqpos : (0 : ℝ) < 1 / (q : ℝ) := one_div_pos.2 (Nat.cast_pos.2 (by omega))
  intro hg
  rw [hg, zero_sub, abs_neg] at h
  have hfa : |(f a : ℝ)| = 1 := by
    rcases hpm a ha with h' | h' <;> rw [h'] <;> norm_num
  rw [hfa] at h
  linarith

/-- **Condition (a) fails under the size condition.** For `q ≥ 2` with `P(q) ≤ 2`, `f(0) = 0`
and `f(r) = ±1` otherwise, `g(1) ≠ 0`. -/
theorem not_condA_of_sizeProd_le {q : ℕ} (hq : 2 ≤ q) (f : ZMod q → ℚ) (h0 : f 0 = 0)
    (hpm : ∀ r : ZMod q, r ≠ 0 → f r = 1 ∨ f r = -1) (hP : sizeProd q ≤ 2) : ¬ CondA q f := by
  intro ha
  have : Fact (1 < q) := ⟨by omega⟩
  exact okadaG_ne_zero_of_sizeProd_le hq f h0 hpm hP 1 one_ne_zero (ha 1 isUnit_one)

/-! ## 3. The series -/

/-- **Erdős's conjecture under the size condition** (Okada, 1982), for functions on `ℤ/q`:
if `q ≥ 2`, `P(q) = ∏_{p ∣ q} p/(p-1) ≤ 2`, `f(0) = 0` and `f(r) = ±1` otherwise, then
`∑ f(n)/n` is not `0`. -/
theorem erdos_size {q : ℕ} (hq : 2 ≤ q) (hP : sizeProd q ≤ 2) (f : ZMod q → ℚ) (h0 : f 0 = 0)
    (hpm : ∀ r : ZMod q, r ≠ 0 → f r = 1 ∨ f r = -1) : ¬ SumIsZero q f := by
  have : NeZero q := ⟨by omega⟩
  rcases Nat.even_or_odd q with he | ho
  · exact erdos_even he f h0 hpm
  · intro h
    exact not_condA_of_sizeProd_le hq f h0 hpm hP (okadaOnlyIf q ho f h0 h).1

/-- **Erdős's conjecture under the size condition, in plain terms.** If `q ≥ 2`,
`∏_{p ∣ q} p/(p-1) ≤ 2`, and `f : ℕ → ℤ` has period `q`, `f(n) = 0` when `q ∣ n` and
`f(n) = ±1` otherwise, then the partial sums `∑_{1 ≤ n < N} f(n)/n` do not tend to `0`. -/
theorem erdos_size_nat {q : ℕ} (hq : 2 ≤ q) (hP : sizeProd q ≤ 2) (f : ℕ → ℤ)
    (hper : ∀ n, f (n + q) = f n) (h0 : ∀ n, q ∣ n → f n = 0)
    (hpm : ∀ n, ¬ q ∣ n → f n = 1 ∨ f n = -1) :
    ¬ Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (f n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have : NeZero q := ⟨by omega⟩
  have key := erdos_size hq hP (zmodLift q f) (zmodLift_zero f h0) (zmodLift_pm f hpm)
  unfold SumIsZero at key
  rw [partialSum_zmodLift f hper] at key
  exact key

/-! ## 4. Which `q` satisfy the size condition -/

/-- `P(q)` depends only on the set of prime factors of `q`. -/
theorem sizeProd_congr {q q' : ℕ} (h : q.primeFactors = q'.primeFactors) :
    sizeProd q = sizeProd q' := by
  unfold sizeProd
  rw [h]

theorem sizeProd_pow (n : ℕ) {k : ℕ} (hk : k ≠ 0) : sizeProd (n ^ k) = sizeProd n :=
  sizeProd_congr (Nat.primeFactors_pow n hk)

/-- For a prime `p`: `p/(p-1) ≤ 2`, and `p/(p-1) ≤ c/(c-1)` when `p ≥ c > 1`. -/
theorem prime_ratio_le {p c : ℕ} (hc : 1 < c) (hp : c ≤ p) :
    (p : ℚ) / ((p : ℚ) - 1) ≤ (c : ℚ) / ((c : ℚ) - 1) := by
  have hc1 : (1 : ℚ) < (c : ℚ) := by exact_mod_cast hc
  have hpc : (c : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Every prime power satisfies the size condition. -/
theorem sizeProd_prime_pow_le {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : sizeProd (p ^ k) ≤ 2 := by
  unfold sizeProd
  rw [Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton]
  have h := prime_ratio_le (c := 2) (by norm_num) hp.two_le
  norm_num at h
  exact h

/-- **Erdős's conjecture for prime powers** (for primes: Baker, Birch and Wirsing, 1973; for
prime powers: Okada, 1982), in plain terms. -/
theorem erdos_prime_pow_nat {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (f : ℕ → ℤ)
    (hper : ∀ n, f (n + p ^ k) = f n) (h0 : ∀ n, p ^ k ∣ n → f n = 0)
    (hpm : ∀ n, ¬ p ^ k ∣ n → f n = 1 ∨ f n = -1) :
    ¬ Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (f n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have h2 : 2 ≤ p ^ k :=
    le_trans hp.two_le (Nat.le_self_pow hk p)
  exact erdos_size_nat h2 (sizeProd_prime_pow_le hp hk) f hper h0 hpm

end Erdos

end PiFormula
