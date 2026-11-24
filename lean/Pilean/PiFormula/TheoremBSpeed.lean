/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula.TheoremBGamma

/-!
# Corollaries B1 and B2 (Part II of pi_formula_theorem.md): series and speed

For a multiset `O` of roots of unity, `log (1 - r/t) = -∑ (r/t)^k / k` gives the series
`γ(O) = ∑_k τ_k(O)`, `τ_k(O) = -Im(p_k(O) t^(-k)) / k`, `p_k(O) = ∑_{r ∈ O} r^k`
(`hasSum_gamma`).

**Corollary B2.** For the three-parameter family `α γ(O_1) + β γ(O_6) + δ (γ(O_10) - γ(O_2))`
the `k`-th term is `T(k) = -E(k) Im(t^(-k)) / k` (`termB_eq`), with
`E(k) = α + β c_6(k) + δ (c_10(k) - c_2(k))` and Ramanujan sums `c_n(k) = p_k(primitive n-th
roots)` (`ramanujan_two`, `ramanujan_six`, `ramanujan_ten`). `E(k)` depends only on
`gcd(k, 30)` (`Ek_gcd`; table `Ek_table`), and `Im(t^(-k)) = 0` iff `4 ∣ k`
(`im_tC_inv_pow_eq_zero_iff`). The note defines the speed as `s/2`, `s` the least
`gcd(k, 60)` over the non-zero terms (`speed`). Then (`speed_le_three_halves`,
`speed_eq_three_halves_iff`): a non-zero series has speed at most `3/2`, and speed exactly `3/2`
holds iff `(α, β, δ)` is a non-zero multiple of `(0, -2, 1)`, whose value is `δ π/4`
(`value_of_fastest`), the value of Euler's `2 arctan (1/3) + arctan (1/7)`.

**Corollary B1, series form** (`series_of_relation`): in any rational relation among `π` and
the `γ` of all orbits (as in `theoremBgamma`), the series of the combination coincides term by
term with that of the three-parameter family, with `α`, `β`, `δ` the net coefficients of
`O_1`, `O_6`, `O_10`. (Partner series cancel term by term, `tau_partner`, and self-paired
series vanish, `tau_selfOrb`.)

`corollaryB2` puts these together for every series for `π` in the class: a relation with value
`q π`, `q ≠ 0`, has the series of the family with `α, β, δ` its net coefficients, speed at most
`3/2`, and speed `3/2` exactly for Euler's formula up to scaling.

That the speed so defined measures the bits gained per unit of denominator is the note's
convention, not a theorem here.
-/

@[expose] public section

open Polynomial Complex ComplexConjugate

namespace PiFormula

/-! ## 1. The series of `γ` -/

/-- `p_k(O) = ∑_{r ∈ O} r^k`. -/
noncomputable def psum (S : Multiset ℂ) (k : ℕ) : ℂ := (S.map (· ^ k)).sum

/-- The `k`-th term of the series of `γ(O)`. -/
noncomputable def tau (S : Multiset ℂ) (k : ℕ) : ℝ := -((psum S k * tC⁻¹ ^ k).im / k)

theorem norm_tC_sq : ‖tC‖ ^ 2 = 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [tC]
  norm_num

theorem norm_div_tC_lt {r : ℂ} (hr : ‖r‖ = 1) : ‖r / tC‖ < 1 := by
  have h := norm_tC_sq
  have h1 : 1 < ‖tC‖ := by nlinarith [norm_nonneg tC]
  rw [norm_div, hr]
  exact (div_lt_one (by linarith)).2 h1

theorem hasSum_gfun {r : ℂ} (hr : ‖r‖ = 1) :
    HasSum (fun k : ℕ => -((r ^ k * tC⁻¹ ^ k).im / k)) (gfun r) := by
  have h := Complex.imCLM.hasSum (hasSum_taylorSeries_neg_log (norm_div_tC_lt hr))
  simp only [Complex.imCLM_apply, Complex.neg_im] at h
  have h2 := h.neg
  rw [neg_neg] at h2
  have e : gfun r = (Complex.log (1 - r / tC)).im := rfl
  rw [e]
  convert h2 using 2 with k
  rw [div_pow, div_eq_mul_inv (r ^ k), ← inv_pow, Complex.div_natCast_im]

theorem hasSum_gamma {S : Multiset ℂ} (hS : ∀ r ∈ S, ‖r‖ = 1) : HasSum (tau S) (gamma S) := by
  induction S using Multiset.induction_on with
  | empty =>
    have : tau 0 = fun _ => 0 := by funext k; simp [tau, psum]
    rw [this]
    simp [gamma]
  | cons r S ih =>
    have hr := hS r (Multiset.mem_cons_self r S)
    have hS' : ∀ x ∈ S, ‖x‖ = 1 := fun x hx => hS x (Multiset.mem_cons_of_mem hx)
    have := (hasSum_gfun hr).add (ih hS')
    convert this using 1
    · funext k
      simp only [tau, psum, Multiset.map_cons, Multiset.sum_cons, add_mul, Complex.add_im]
      ring
    · simp [gamma]

/-! ## 2. Ramanujan sums -/

/-- The Ramanujan sum `c_n(k) = ∑_{r primitive n-th root} r^k`. -/
noncomputable def ramanujan (n k : ℕ) : ℂ := ∑ r ∈ primitiveRoots n ℂ, r ^ k

/-- `∑_{r^n = 1} r^k`. -/
noncomputable def powSum (n k : ℕ) : ℂ := ∑ r ∈ nthRootsFinset n (1 : ℂ), r ^ k

theorem powSum_eq {n : ℕ} (hn : 0 < n) (k : ℕ) : powSum n k = if n ∣ k then (n : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  set ζ := Complex.exp (2 * Real.pi * I / n) with hζdef
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn.ne'
  split_ifs with hdvd
  · have : ∀ r ∈ nthRootsFinset n (1 : ℂ), r ^ k = 1 := by
      intro r hr
      obtain ⟨j, rfl⟩ := hdvd
      rw [pow_mul, (mem_nthRootsFinset hn 1).1 hr, one_pow]
    rw [powSum, Finset.sum_congr rfl this, Finset.sum_const, hζ.card_nthRootsFinset]
    simp
  · have hζk : ζ ^ k ≠ 1 := fun h => hdvd ((hζ.pow_eq_one_iff_dvd k).1 h)
    have hrot : ∑ r ∈ nthRootsFinset n (1 : ℂ), (ζ * r) ^ k = powSum n k := by
      refine Finset.sum_nbij' (fun r => ζ * r) (fun r => ζ⁻¹ * r) ?_ ?_ ?_ ?_ ?_
      · intro r hr
        rw [mem_nthRootsFinset hn] at hr ⊢
        rw [mul_pow, hζ.pow_eq_one, hr, one_mul]
      · intro r hr
        rw [mem_nthRootsFinset hn] at hr ⊢
        rw [mul_pow, inv_pow, hζ.pow_eq_one, hr, inv_one, one_mul]
      · intro r _; simp [hζ0]
      · intro r _; simp [hζ0]
      · intro r _; rfl
    have : ζ ^ k * powSum n k = powSum n k := by
      conv_rhs => rw [← hrot]
      rw [powSum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by rw [mul_pow]
    have h2 : (ζ ^ k - 1) * powSum n k = 0 := by linear_combination this
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hζk)

/-- `∑_{r^n = 1} r^k = ∑_{d ∣ n} c_d(k)`. -/
theorem powSum_eq_sum_ramanujan (n k : ℕ) :
    powSum n k = ∑ d ∈ n.divisors, ramanujan d k := by
  classical
  rw [powSum, IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
    Finset.sum_biUnion (fun i _ j _ hij => IsPrimitiveRoot.disjoint hij)]
  rfl

theorem ramanujan_one (k : ℕ) : ramanujan 1 k = 1 := by
  simp [ramanujan, IsPrimitiveRoot.primitiveRoots_one]

theorem ramanujan_two (k : ℕ) : ramanujan 2 k = (if 2 ∣ k then 2 else 0) - 1 := by
  have h2 := powSum_eq_sum_ramanujan 2 k
  rw [show (2 : ℕ).divisors = {1, 2} by decide, Finset.sum_pair (by norm_num),
    ramanujan_one, powSum_eq (by norm_num)] at h2
  push_cast at h2
  linear_combination -h2

theorem ramanujan_six (k : ℕ) :
    ramanujan 6 k = (if 6 ∣ k then 6 else 0) - (if 3 ∣ k then 3 else 0) -
      (if 2 ∣ k then 2 else 0) + 1 := by
  have h6 := powSum_eq_sum_ramanujan 6 k
  have h3 := powSum_eq_sum_ramanujan 3 k
  have h2 := powSum_eq_sum_ramanujan 2 k
  rw [show (6 : ℕ).divisors = {1, 2, 3, 6} by decide] at h6
  rw [show (3 : ℕ).divisors = {1, 3} by decide] at h3
  rw [show (2 : ℕ).divisors = {1, 2} by decide] at h2
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3, 6} : Finset ℕ) by decide),
    Finset.sum_insert (show (2 : ℕ) ∉ ({3, 6} : Finset ℕ) by decide),
    Finset.sum_pair (show (3 : ℕ) ≠ 6 by decide), Finset.sum_pair (show (1 : ℕ) ≠ 3 by decide),
    Finset.sum_pair (show (1 : ℕ) ≠ 2 by decide), ramanujan_one] at h6 h3 h2
  rw [powSum_eq (by norm_num)] at h6 h3 h2
  push_cast at h6 h3 h2
  linear_combination -h6 + h3 + h2

theorem ramanujan_ten (k : ℕ) :
    ramanujan 10 k = (if 10 ∣ k then 10 else 0) - (if 5 ∣ k then 5 else 0) -
      (if 2 ∣ k then 2 else 0) + 1 := by
  have h10 := powSum_eq_sum_ramanujan 10 k
  have h5 := powSum_eq_sum_ramanujan 5 k
  have h2 := powSum_eq_sum_ramanujan 2 k
  rw [show (10 : ℕ).divisors = {1, 2, 5, 10} by decide] at h10
  rw [show (5 : ℕ).divisors = {1, 5} by decide] at h5
  rw [show (2 : ℕ).divisors = {1, 2} by decide] at h2
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 5, 10} : Finset ℕ) by decide),
    Finset.sum_insert (show (2 : ℕ) ∉ ({5, 10} : Finset ℕ) by decide),
    Finset.sum_pair (show (5 : ℕ) ≠ 10 by decide), Finset.sum_pair (show (1 : ℕ) ≠ 5 by decide),
    Finset.sum_pair (show (1 : ℕ) ≠ 2 by decide), ramanujan_one] at h10 h5 h2
  rw [powSum_eq (by norm_num)] at h10 h5 h2
  push_cast at h10 h5 h2
  linear_combination -h10 + h5 + h2

/-! ## 3. `Im(t^(-k)) = 0` iff `4 ∣ k` -/

theorem tC_inv : tC⁻¹ = (1 - I) / 2 := by
  refine inv_eq_of_mul_eq_one_right ?_
  unfold tC
  linear_combination (-1 / 2 : ℂ) * Complex.I_sq

theorem tC_inv_pow_four : tC⁻¹ ^ 4 = ((-1 / 4 : ℝ) : ℂ) := by
  rw [inv_pow, tC_pow_four]; push_cast; norm_num

theorem im_tC_inv_pow (q j : ℕ) :
    (tC⁻¹ ^ (4 * q + j)).im = (-1 / 4 : ℝ) ^ q * (tC⁻¹ ^ j).im := by
  rw [pow_add, pow_mul, tC_inv_pow_four, ← Complex.ofReal_pow, Complex.im_ofReal_mul]

theorem im_tC_inv_pow_small :
    (tC⁻¹ ^ 0).im = 0 ∧ (tC⁻¹ ^ 1).im = -1 / 2 ∧ (tC⁻¹ ^ 2).im = -1 / 2 ∧
      (tC⁻¹ ^ 3).im = -1 / 4 := by
  rw [tC_inv]
  refine ⟨by simp, by simp, ?_, ?_⟩
  · rw [show ((1 - I) / 2) ^ 2 = -I / 2 by linear_combination (1 / 4 : ℂ) * Complex.I_sq]
    simp
  · rw [show ((1 - I) / 2) ^ 3 = (-1 - I) / 4 by
      linear_combination ((3 - I) / 8) * Complex.I_sq]
    simp

theorem im_tC_inv_pow_eq_zero_iff (k : ℕ) : (tC⁻¹ ^ k).im = 0 ↔ 4 ∣ k := by
  obtain ⟨h0, h1, h2, h3⟩ := im_tC_inv_pow_small
  rw [← Nat.div_add_mod k 4, im_tC_inv_pow, Nat.dvd_add_right (dvd_mul_right 4 _)]
  have hq : ((-1 / 4 : ℝ)) ^ (k / 4) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [mul_eq_zero, or_iff_right hq]
  have hlt := Nat.mod_lt k (show 4 > 0 by norm_num)
  interval_cases (k % 4) <;> simp_all

/-! ## 4. Corollary B2: the three-parameter family -/

/-- `c_6(k)`, as a rational. -/
def c6 (k : ℕ) : ℚ :=
  (if 6 ∣ k then 6 else 0) - (if 3 ∣ k then 3 else 0) - (if 2 ∣ k then 2 else 0) + 1

/-- `c_10(k)`, as a rational. -/
def c10 (k : ℕ) : ℚ :=
  (if 10 ∣ k then 10 else 0) - (if 5 ∣ k then 5 else 0) - (if 2 ∣ k then 2 else 0) + 1

/-- `c_2(k) = (-1)^k`, as a rational. -/
def c2 (k : ℕ) : ℚ := (if 2 ∣ k then 2 else 0) - 1

/-- `E(k) = α + β c_6(k) + δ (c_10(k) - c_2(k))`. -/
def Ek (α β δ : ℚ) (k : ℕ) : ℚ := α + β * c6 k + δ * (c10 k - c2 k)

theorem psum_O1 (k : ℕ) : psum (orbit (.P 0)) k = 1 := by
  rw [psum, orbit_P, ← Finset.sum_eq_multiset_sum]
  exact ramanujan_one k

theorem psum_O2 (k : ℕ) : psum (orbit (.Q 0)) k = (c2 k : ℂ) := by
  rw [psum, orbit_Q, ← Finset.sum_eq_multiset_sum]
  change ramanujan 2 k = _
  rw [ramanujan_two, c2]
  split_ifs <;> norm_num

theorem psum_O6 (k : ℕ) : psum (orbit (.Q 1)) k = (c6 k : ℂ) := by
  rw [psum, orbit_Q, ← Finset.sum_eq_multiset_sum]
  change ramanujan 6 k = _
  rw [ramanujan_six, c6]
  split_ifs <;> norm_num

theorem psum_O10 (k : ℕ) : psum (orbit (.Q 2)) k = (c10 k : ℂ) := by
  rw [psum, orbit_Q, ← Finset.sum_eq_multiset_sum]
  change ramanujan 10 k = _
  rw [ramanujan_ten, c10]
  split_ifs <;> norm_num

/-- The `k`-th term of the series of `α γ(O_1) + β γ(O_6) + δ (γ(O_10) - γ(O_2))`. -/
noncomputable def termB (α β δ : ℚ) (k : ℕ) : ℝ :=
  α * tau (orbit (.P 0)) k + β * tau (orbit (.Q 1)) k +
    δ * (tau (orbit (.Q 2)) k - tau (orbit (.Q 0)) k)

theorem hasSum_termB (α β δ : ℚ) :
    HasSum (termB α β δ) (α * gamma (orbit (.P 0)) + β * gamma (orbit (.Q 1)) +
      δ * (gamma (orbit (.Q 2)) - gamma (orbit (.Q 0)))) := by
  have h := fun a => hasSum_gamma (fun r hr => norm_of_mem_orbit (a := a) hr)
  exact (((h _).mul_left _).add ((h _).mul_left _)).add (((h _).sub (h _)).mul_left _)

theorem im_ratCast_mul (q : ℚ) (w : ℂ) : ((q : ℂ) * w).im = q * w.im := by
  rw [← Complex.ofReal_ratCast, Complex.im_ofReal_mul]

/-- **The terms.** `T(k) = -E(k) Im(t^(-k)) / k`. -/
theorem termB_eq (α β δ : ℚ) (k : ℕ) :
    termB α β δ k = -((Ek α β δ k : ℝ) * (tC⁻¹ ^ k).im) / k := by
  simp only [termB, tau, psum_O1, psum_O6, psum_O10, psum_O2, one_mul, im_ratCast_mul, Ek]
  push_cast
  ring

/-- `E(k)` depends only on `gcd(k, 30)`. -/
theorem Ek_gcd (α β δ : ℚ) (k : ℕ) : Ek α β δ k = Ek α β δ (Nat.gcd k 30) := by
  have h : ∀ d, d ∣ 30 → (d ∣ Nat.gcd k 30 ↔ d ∣ k) := fun d hd =>
    ⟨fun h => h.trans (Nat.gcd_dvd_left _ _), fun h => Nat.dvd_gcd h hd⟩
  simp only [Ek, c6, c10, c2, h 6 (by norm_num), h 3 (by norm_num), h 2 (by norm_num),
    h 10 (by norm_num), h 5 (by norm_num)]

/-- The table of the note: `E` at `gcd(k, 30) = 1, 2, 3, 5, 6, 10, 15, 30`. -/
theorem Ek_table (a b d : ℚ) :
    Ek a b d 1 = a + b + 2 * d ∧ Ek a b d 2 = a - b - 2 * d ∧ Ek a b d 3 = a - 2 * b + 2 * d ∧
      Ek a b d 5 = a + b - 3 * d ∧ Ek a b d 6 = a + 2 * b - 2 * d ∧
      Ek a b d 10 = a - b + 3 * d ∧ Ek a b d 15 = a - 2 * b - 3 * d ∧
      Ek a b d 30 = a + 2 * b + 3 * d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [Ek, c6, c10, c2] <;> ring

/-- The terms with `gcd(k, 60) ∈ {1, 2}` (that is, `gcd(k, 15) = 1`) have
`E(k) = α + β + 2δ` or `α - β - 2δ`; for `(α, β, δ) = δ (0, -2, 1)` both vanish. -/
theorem Ek_euler_of_coprime (δ : ℚ) {k : ℕ} (h3 : ¬ 3 ∣ k) (h5 : ¬ 5 ∣ k) :
    Ek 0 (-2 * δ) δ k = 0 := by
  have h6 : ¬ 6 ∣ k := fun h => h3 ((show 3 ∣ 6 by norm_num).trans h)
  have h10 : ¬ 10 ∣ k := fun h => h5 ((show 5 ∣ 10 by norm_num).trans h)
  simp only [Ek, c6, c10, c2, h3, h5, h6, h10, ↓reduceIte]
  split_ifs <;> ring

/-! ### Speed -/

/-- The least `gcd(k, 60)` over the non-zero terms. -/
noncomputable def speedGcd (α β δ : ℚ) : ℕ :=
  sInf {g : ℕ | ∃ k, 0 < k ∧ Nat.gcd k 60 = g ∧ termB α β δ k ≠ 0}

/-- **The speed** (the note's definition): `s/2`, `s` the least `gcd(k, 60)` over the
non-zero terms. -/
noncomputable def speed (α β δ : ℚ) : ℚ := (speedGcd α β δ : ℚ) / 2

theorem termB_ne_zero_iff (α β δ : ℚ) {k : ℕ} (hk : 0 < k) :
    termB α β δ k ≠ 0 ↔ Ek α β δ k ≠ 0 ∧ ¬ 4 ∣ k := by
  rw [termB_eq, ← im_tC_inv_pow_eq_zero_iff]
  have hk' : (k : ℝ) ≠ 0 := by positivity
  constructor
  · intro h
    refine ⟨fun hE => h ?_, fun hI => h ?_⟩
    · rw [hE]; simp
    · rw [hI]; simp
  · rintro ⟨hE, hI⟩ h
    rw [neg_div, neg_eq_zero, div_eq_zero_iff, mul_eq_zero] at h
    rcases h with (h | h) | h
    · exact hE (by exact_mod_cast h)
    · exact hI h
    · exact hk' h

theorem mem_speedSet {α β δ : ℚ} {k : ℕ} (hk : 0 < k) (hE : Ek α β δ k ≠ 0) (h4 : ¬ 4 ∣ k) :
    Nat.gcd k 60 ∈ {g : ℕ | ∃ k, 0 < k ∧ Nat.gcd k 60 = g ∧ termB α β δ k ≠ 0} :=
  ⟨k, hk, rfl, (termB_ne_zero_iff α β δ hk).2 ⟨hE, h4⟩⟩

/-- **Corollary B2, first part.** A non-zero series of the family has speed at most `3/2`. -/
theorem speed_le_three_halves {α β δ : ℚ} (h : ¬ (α = 0 ∧ β = 0 ∧ δ = 0)) :
    speed α β δ ≤ 3 / 2 := by
  obtain ⟨e1, e2, e3, -⟩ := Ek_table α β δ
  have hmem : ∃ g ≤ 3,
      g ∈ {g : ℕ | ∃ k, 0 < k ∧ Nat.gcd k 60 = g ∧ termB α β δ k ≠ 0} := by
    by_cases h1 : Ek α β δ 1 = 0
    · by_cases h2 : Ek α β δ 2 = 0
      · by_cases h3 : Ek α β δ 3 = 0
        · exact absurd (no_series_faster_than_three_halves α β δ (e1 ▸ h1) (e2 ▸ h2) (e3 ▸ h3)) h
        · exact ⟨_, by norm_num, mem_speedSet (k := 3) (by norm_num) h3 (by norm_num)⟩
      · exact ⟨_, by norm_num, mem_speedSet (k := 2) (by norm_num) h2 (by norm_num)⟩
    · exact ⟨_, by norm_num, mem_speedSet (k := 1) (by norm_num) h1 (by norm_num)⟩
  obtain ⟨g, hg3, hg⟩ := hmem
  have hle : speedGcd α β δ ≤ 3 := (Nat.sInf_le hg).trans hg3
  unfold speed
  have : (speedGcd α β δ : ℚ) ≤ 3 := by exact_mod_cast hle
  linarith

/-- **Corollary B2, second part.** Speed exactly `3/2` holds iff `(α, β, δ)` is a non-zero
multiple of `(0, -2, 1)`. -/
theorem speed_eq_three_halves_iff (α β δ : ℚ) :
    speed α β δ = 3 / 2 ↔ α = 0 ∧ β = -2 * δ ∧ δ ≠ 0 := by
  obtain ⟨e1, e2, e3, -⟩ := Ek_table α β δ
  have hset : ∀ k, 0 < k → Ek α β δ k ≠ 0 → ¬ 4 ∣ k → speedGcd α β δ ≤ Nat.gcd k 60 :=
    fun k hk hE h4 => Nat.sInf_le (mem_speedSet hk hE h4)
  constructor
  · intro h
    have hs : speedGcd α β δ = 3 := by
      unfold speed at h
      have : (speedGcd α β δ : ℚ) = 3 := by linarith
      exact_mod_cast this
    have h1 : Ek α β δ 1 = 0 := by
      by_contra hne
      have := hset 1 (by norm_num) hne (by norm_num)
      norm_num at this; omega
    have h2 : Ek α β δ 2 = 0 := by
      by_contra hne
      have := hset 2 (by norm_num) hne (by norm_num)
      norm_num at this; omega
    obtain ⟨hα, hβ⟩ := fastest_series_is_unique α β δ (e1 ▸ h1) (e2 ▸ h2)
    refine ⟨hα, hβ, fun hδ => ?_⟩
    -- the zero series has no non-zero term, so `speedGcd = 0`
    have hempty : {g : ℕ | ∃ k, 0 < k ∧ Nat.gcd k 60 = g ∧ termB α β δ k ≠ 0} = ∅ := by
      ext g
      constructor
      · rintro ⟨k, -, -, hT⟩
        apply hT
        rw [termB_eq, show Ek α β δ k = 0 by simp [Ek, hα, hβ, hδ]]
        simp
      · intro hg
        exact hg.elim
    unfold speedGcd at hs
    rw [hempty, Nat.sInf_empty] at hs
    omega
  · rintro ⟨rfl, rfl, hδ⟩
    have h3mem := mem_speedSet (α := 0) (β := -2 * δ) (δ := δ) (k := 3) (by norm_num)
      (by rw [e3]; intro h; apply hδ; linarith) (by norm_num)
    have hs : speedGcd 0 (-2 * δ) δ = 3 := by
      apply le_antisymm
      · exact Nat.sInf_le h3mem
      · apply le_csInf ⟨_, h3mem⟩
        rintro g ⟨k, hk, rfl, hT⟩
        obtain ⟨hE, -⟩ := (termB_ne_zero_iff _ _ _ hk).1 hT
        by_contra hlt
        push Not at hlt
        have hg0 : 0 < Nat.gcd k 60 := Nat.gcd_pos_of_pos_left _ hk
        have h3 : ¬ 3 ∣ k := fun h => by
          have := Nat.le_of_dvd hg0 (Nat.dvd_gcd h (by norm_num)); omega
        have h5 : ¬ 5 ∣ k := fun h => by
          have := Nat.le_of_dvd hg0 (Nat.dvd_gcd h (by norm_num)); omega
        exact hE (Ek_euler_of_coprime δ h3 h5)
    unfold speed
    rw [hs]
    norm_num

/-- The fastest series, `δ (γ(O_10) - γ(O_2) - 2 γ(O_6))`, has the value `δ π/4`, the value of
Euler's formula `2 arctan (1/3) + arctan (1/7)`. -/
theorem value_of_fastest (δ : ℚ) :
    ((0 : ℚ) : ℝ) * gamma (orbit (.P 0)) + ((-2 * δ : ℚ) : ℝ) * gamma (orbit (.Q 1)) +
        (δ : ℝ) * (gamma (orbit (.Q 2)) - gamma (orbit (.Q 0))) =
      δ * (2 * Real.arctan (1 / 3) + Real.arctan (1 / 7)) := by
  rw [euler, gamma_orbit_Q1, gamma_orbit_Q2, gamma_orbit_Q0]
  push_cast
  ring

/-! ## 5. Corollary B1, series form -/

theorem I_conj_mul_tC_inv (r : ℂ) : I * conj r * tC⁻¹ = conj (r * tC⁻¹) := by
  have h := one_sub_partner r
  rw [map_sub, map_one, map_div₀] at h
  rw [map_mul, map_inv₀, ← div_eq_mul_inv, ← div_eq_mul_inv]
  linear_combination -h

/-- Partner series cancel term by term. -/
theorem tau_partner (S : Multiset ℂ) (k : ℕ) : tau (partner S) k = -tau S k := by
  have key : psum (partner S) k * tC⁻¹ ^ k = conj (psum S k * tC⁻¹ ^ k) := by
    simp only [psum, partner, Multiset.map_map, Function.comp_def]
    rw [← Multiset.sum_map_mul_right, ← Multiset.sum_map_mul_right, map_multiset_sum,
      Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun r _ => ?_
    simp only [Function.comp_apply]
    rw [← mul_pow, I_conj_mul_tC_inv, ← map_pow, mul_pow]
  rw [tau, tau, key, Complex.conj_im]
  ring

theorem tau_selfOrb (k : ℕ) (b : Bool) (j : ℕ) : tau (selfOrb k b) j = 0 := by
  have := tau_partner (selfOrb k b) j
  rw [partner_selfOrb] at this
  linarith

/-- The `k`-th term of the series of `∑ c_a γ(orbit a) + ∑ d_a γ(partner (orbit a)) +
∑ e_s γ(selfOrb s)`. -/
noncomputable def seriesOf (c d : Atom →₀ ℚ) (e : (ℕ × Bool) →₀ ℚ) (k : ℕ) : ℝ :=
  (c.sum fun a x => (x : ℝ) * tau (orbit a) k) +
    (d.sum fun a x => (x : ℝ) * tau (partner (orbit a)) k) +
    (e.sum fun s x => (x : ℝ) * tau (selfOrb s.1 s.2) k)

/-- The series converges to the combination. -/
theorem hasSum_seriesOf (c d : Atom →₀ ℚ) (e : (ℕ × Bool) →₀ ℚ) :
    HasSum (seriesOf c d e)
      ((c.sum fun a x => (x : ℝ) * gamma (orbit a)) +
        (d.sum fun a x => (x : ℝ) * gamma (partner (orbit a))) +
        (e.sum fun s x => (x : ℝ) * gamma (selfOrb s.1 s.2))) := by
  have ho : ∀ a, HasSum (tau (orbit a)) (gamma (orbit a)) := fun a =>
    hasSum_gamma fun r hr => norm_of_mem_orbit hr
  have hp : ∀ a, HasSum (tau (partner (orbit a))) (gamma (partner (orbit a))) := fun a =>
    hasSum_gamma fun r hr => by
      obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hr
      exact norm_partner_elt (norm_of_mem_orbit hs)
  have hs : ∀ s : ℕ × Bool, HasSum (tau (selfOrb s.1 s.2)) (gamma (selfOrb s.1 s.2)) := fun s =>
    hasSum_gamma fun r hr =>
      norm_of_mem_roots_cycPoly (by omega) (norm_eq_one_of_pow_four (kappaS_pow_four s.2))
        (by norm_num) hr
  unfold seriesOf Finsupp.sum
  exact ((hasSum_sum fun a _ => (ho a).mul_left _).add
    (hasSum_sum fun a _ => (hp a).mul_left _)).add (hasSum_sum fun s _ => (hs s).mul_left _)

/-- **Corollary B1, series form.** If a rational combination of the `γ` of all orbits is
`q π`, its series coincides term by term with that of the three-parameter family, with
`α`, `β`, `δ` the net coefficients of `O_1`, `O_6` and `O_10`. -/
theorem series_of_relation (c d : Atom →₀ ℚ) (e : (ℕ × Bool) →₀ ℚ) (q : ℚ)
    (h : (c.sum fun a x => (x : ℝ) * gamma (orbit a)) +
      (d.sum fun a x => (x : ℝ) * gamma (partner (orbit a))) +
      (e.sum fun s x => (x : ℝ) * gamma (selfOrb s.1 s.2)) = q * Real.pi) (k : ℕ) :
    seriesOf c d e k =
      termB (c (.P 0) - d (.P 0)) (c (.Q 1) - d (.Q 1)) (c (.Q 2) - d (.Q 2)) k := by
  classical
  obtain ⟨h1, h2, -⟩ := theoremBgamma c d e q h
  set c' := c - d with hc'
  have hcd : ∀ a, c' a = c a - d a := fun a => by simp [hc']
  have he : (e.sum fun s x => (x : ℝ) * tau (selfOrb s.1 s.2) k) = 0 := by
    simp [Finsupp.sum, tau_selfOrb]
  have hd : (d.sum fun a x => (x : ℝ) * tau (partner (orbit a)) k) =
      -(d.sum fun a x => (x : ℝ) * tau (orbit a) k) := by
    simp only [Finsupp.sum, tau_partner, mul_neg, Finset.sum_neg_distrib]
  have hsum : seriesOf c d e k = c'.sum fun a x => (x : ℝ) * tau (orbit a) k := by
    rw [seriesOf, he, hd, hc', Finsupp.sum_sub_index (fun a b₁ b₂ => by push_cast; ring)]
    ring
  have hsupp : c'.support ⊆ exceptional := by
    intro a ha
    by_contra hn
    have := h1 a hn
    exact (Finsupp.mem_support_iff.1 ha) (by rw [hcd, this, sub_self])
  rw [hsum, Finsupp.sum_of_support_subset c' hsupp _ (fun _ _ => by simp), exceptional,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, termB]
  have hQ : (c' (.Q 0) : ℝ) = -((c (.Q 2) - d (.Q 2) : ℚ) : ℝ) := by
    have : c' (.Q 0) = -(c (.Q 2) - d (.Q 2)) := by rw [hcd]; linarith
    exact_mod_cast this
  rw [hQ]
  simp only [hcd]
  push_cast
  ring

/-- **Corollary B2** (headline). Let a rational combination of the `γ` of all orbits be
`q π` with `q ≠ 0`, and let `α, β, δ` be the net coefficients of `O_1, O_6, O_10`. Then its
series is that of the three-parameter family, its speed is at most `3/2`, and it is exactly
`3/2` iff `α = 0` and `β = -2δ` (Euler's formula, up to scaling). -/
theorem corollaryB2 (c d : Atom →₀ ℚ) (e : (ℕ × Bool) →₀ ℚ) (q : ℚ)
    (h : (c.sum fun a x => (x : ℝ) * gamma (orbit a)) +
      (d.sum fun a x => (x : ℝ) * gamma (partner (orbit a))) +
      (e.sum fun s x => (x : ℝ) * gamma (selfOrb s.1 s.2)) = q * Real.pi) (hq : q ≠ 0) :
    seriesOf c d e = termB (c (.P 0) - d (.P 0)) (c (.Q 1) - d (.Q 1)) (c (.Q 2) - d (.Q 2)) ∧
      speed (c (.P 0) - d (.P 0)) (c (.Q 1) - d (.Q 1)) (c (.Q 2) - d (.Q 2)) ≤ 3 / 2 ∧
      (speed (c (.P 0) - d (.P 0)) (c (.Q 1) - d (.Q 1)) (c (.Q 2) - d (.Q 2)) = 3 / 2 ↔
        c (.P 0) - d (.P 0) = 0 ∧ c (.Q 1) - d (.Q 1) = -2 * (c (.Q 2) - d (.Q 2))) := by
  obtain ⟨-, h2, h3⟩ := theoremBgamma c d e q h
  -- `q = (α + δ)/4`
  have hqv : q = ((c (.P 0) - d (.P 0)) + (c (.Q 2) - d (.Q 2))) / 4 := by
    rw [h3]; linarith
  refine ⟨funext (series_of_relation c d e q h), speed_le_three_halves ?_, ?_⟩
  · rintro ⟨hα, -, hδ⟩
    apply hq
    rw [hqv, hα, hδ]
    norm_num
  · rw [speed_eq_three_halves_iff]
    constructor
    · rintro ⟨hα, hβ, -⟩
      exact ⟨hα, hβ⟩
    · rintro ⟨hα, hβ⟩
      refine ⟨hα, hβ, fun hδ => hq ?_⟩
      rw [hqv, hα, hδ]
      norm_num

end PiFormula
