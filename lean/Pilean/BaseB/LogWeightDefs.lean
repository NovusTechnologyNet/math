module

public import Pilean.BaseB.LogWeightDegree

/-!
# The weight `λ` on the primes: definition and first properties

For a base `b`, the weight `lam b : ℕ → ℚ` on the primes (research note
`research/2026-11-22-log-primes/00_summary.md`, section 4), in terms of the constant term
`c₀(r)` and the degree `d(r)` of the minimal polynomial of `√b - r` only.

* On a prime `p ∣ b`: `1 / (ω(b) v_p(b))`, so that the weight of `b` is `1`.
* On `2`, for odd `b`: `lamTwo b` (`1/a` if `b - 1 = 2^a`, `1/u` if `b + 1 = 2^u`, else
  `1/(a + u)`, with `a = v_2(b - 1)` and `u = v_2(b + 1)`).
* On an odd prime `p ∤ b`, by recursion on `p`: let `r` be a root of unity with `r²` of order
  `m = ord_p(b)` and `p ∣ c₀(r)` (`homeRoot b p`), and `c = |c₀(r)|`, `d = d(r)`. Then
  `λ_p = ω / N`, where `ω = d/2 - ∑ λ_q v_q(c)` over the primes `q ∣ c` with `q ∣ 2m` (all
  smaller than `p`), and `N = ∑ v_q(c)` over the primes `q ∣ c` with `q ∤ 2m`
  (`omegaOf`, `countOf`).

`wtOf f n = ∑_p f(p) v_p(n)` is the weight of a positive integer; it is additive on products.
By F3 (`data_eq_of_common_prime`) the weight of a prime `p ∣ c₀(r)` with `p ∤ 2m` is computed
from the data of `r` itself (`lam_eq_of_dvd`).
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-! ## 1. The weight of a positive integer -/

/-- `∑_p f(p) v_p(n)`. -/
def wtOf (f : ℕ → ℚ) (n : ℕ) : ℚ := ∑ p ∈ n.primeFactors, f p * n.factorization p

theorem wtOf_one (f : ℕ → ℚ) : wtOf f 1 = 0 := by simp [wtOf]

theorem wtOf_mul (f : ℕ → ℚ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    wtOf f (m * n) = wtOf f m + wtOf f n := by
  have key : ∀ k : ℕ, wtOf f k = k.factorization.sum fun p e => f p * e := by
    intro k
    rw [Finsupp.sum, Nat.support_factorization]
    rfl
  rw [key, key, key, Nat.factorization_mul hm hn,
    Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring)]

theorem wtOf_pow (f : ℕ → ℚ) {n : ℕ} (hn : n ≠ 0) (k : ℕ) : wtOf f (n ^ k) = k * wtOf f n := by
  induction k with
  | zero => simp [wtOf_one]
  | succ k ih =>
    rw [pow_succ, wtOf_mul f (pow_ne_zero k hn) hn, ih]
    push_cast
    ring

theorem wtOf_pos {f : ℕ → ℚ} (hf : ∀ p : ℕ, p.Prime → 0 < f p) {n : ℕ} (hn : 2 ≤ n) :
    0 < wtOf f n := by
  apply Finset.sum_pos
  · intro p hp
    have hp' := Nat.mem_primeFactors.1 hp
    have h1 : 0 < n.factorization p := hp'.1.factorization_pos_of_dvd hp'.2.2 hp'.2.1
    have h2 : (0 : ℚ) < (n.factorization p : ℚ) := by exact_mod_cast h1
    exact mul_pos (hf p hp'.1) h2
  · exact Nat.nonempty_primeFactors.2 (by omega)

/-! ## 2. The weight of 2 -/

/-- The weight of the prime 2 for an odd base. -/
noncomputable def lamTwo (b : ℕ) : ℚ :=
  if b - 1 = 2 ^ (b - 1).factorization 2 then 1 / ((b - 1).factorization 2 : ℚ)
  else if b + 1 = 2 ^ (b + 1).factorization 2 then 1 / ((b + 1).factorization 2 : ℚ)
  else 1 / (((b - 1).factorization 2 : ℚ) + (b + 1).factorization 2)

/-- For an odd base `b ≥ 5`: `0 < λ_2 ≤ 1/2`, and for `e = b - 1` or `b + 1`,
`λ_2 v_2(e) = 1` if `e` is a power of 2 and `λ_2 v_2(e) < 1` otherwise. -/
theorem lamTwo_spec {b : ℕ} (hb : 5 ≤ b) (hodd : ¬ 2 ∣ b) :
    0 < lamTwo b ∧ lamTwo b ≤ 1 / 2 ∧ ∀ e : ℕ, e = b - 1 ∨ e = b + 1 →
      (e = 2 ^ e.factorization 2 → lamTwo b * e.factorization 2 = 1) ∧
        (e ≠ 2 ^ e.factorization 2 → lamTwo b * e.factorization 2 < 1) := by
  obtain ⟨a, ha⟩ : ∃ a, (b - 1).factorization 2 = a := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, (b + 1).factorization 2 = u := ⟨_, rfl⟩
  have hda : 2 ^ a ∣ b - 1 := ha ▸ Nat.ordProj_dvd (b - 1) 2
  have hdu : 2 ^ u ∣ b + 1 := hu ▸ Nat.ordProj_dvd (b + 1) 2
  have ha1 : 1 ≤ a := by
    rw [← ha]
    exact Nat.prime_two.factorization_pos_of_dvd (by omega) (by omega)
  have hu1 : 1 ≤ u := by
    rw [← hu]
    exact Nat.prime_two.factorization_pos_of_dvd (by omega) (by omega)
  have ha0 : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha1
  have hu0 : (0 : ℚ) < (u : ℚ) := by exact_mod_cast hu1
  rw [lamTwo, ha, hu]
  by_cases hA : b - 1 = 2 ^ a
  · -- `b - 1 = 2^a`: then `a ≥ 2` and `u = 1`
    rw [ite_eq_left hA]
    have ha2 : 2 ≤ a := by
      by_contra hlt
      obtain rfl : a = 1 := by omega
      omega
    have h4a : 4 ∣ b - 1 := by
      rw [hA]
      exact pow_dvd_pow 2 ha2
    have hu' : u = 1 := by
      by_contra hne
      have h4u : 4 ∣ b + 1 := (pow_dvd_pow 2 (by omega : 2 ≤ u)).trans hdu
      omega
    have ha2' : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha2
    refine ⟨by positivity, one_div_le_one_div_of_le (by norm_num) ha2', ?_⟩
    rintro e (rfl | rfl)
    · rw [ha]
      exact ⟨fun _ => one_div_mul_cancel ha0.ne', fun h => absurd hA h⟩
    · rw [hu, hu']
      refine ⟨fun h => by omega, fun _ => ?_⟩
      rw [Nat.cast_one, mul_one, div_lt_one ha0]
      linarith
  · rw [ite_eq_right hA]
    by_cases hU : b + 1 = 2 ^ u
    · -- `b + 1 = 2^u`: then `u ≥ 3` and `a < u`
      rw [ite_eq_left hU]
      have hu3 : 3 ≤ u := by
        by_contra hlt
        have h1 : 2 ^ u ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hau : a < u := by
        have h1 : 2 ^ a ≤ b - 1 := Nat.le_of_dvd (by omega) hda
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (by omega)
      have hu3' : (2 : ℚ) ≤ (u : ℚ) := by exact_mod_cast (by omega : 2 ≤ u)
      refine ⟨by positivity, one_div_le_one_div_of_le (by norm_num) hu3', ?_⟩
      rintro e (rfl | rfl)
      · rw [ha]
        refine ⟨fun h => absurd h hA, fun _ => ?_⟩
        rw [one_div_mul_eq_div, div_lt_one hu0]
        exact_mod_cast hau
      · rw [hu]
        exact ⟨fun _ => one_div_mul_cancel hu0.ne', fun h => absurd hU h⟩
    · rw [ite_eq_right hU]
      have hsum : (2 : ℚ) ≤ (a : ℚ) + u := by exact_mod_cast (by omega : 2 ≤ a + u)
      refine ⟨by positivity, one_div_le_one_div_of_le (by norm_num) hsum, ?_⟩
      rintro e (rfl | rfl)
      · rw [ha]
        refine ⟨fun h => absurd h hA, fun _ => ?_⟩
        rw [one_div_mul_eq_div, div_lt_one (by positivity)]
        linarith
      · rw [hu]
        refine ⟨fun h => absurd h hU, fun _ => ?_⟩
        rw [one_div_mul_eq_div, div_lt_one (by positivity)]
        linarith

/-! ## 3. The recursion -/

/-- `ω = d/2 - ∑ f(q) v_q(c)` over the primes `q ∣ c` with `q ∣ 2m`. -/
def omegaOf (f : ℕ → ℚ) (c d m : ℕ) : ℚ :=
  (d : ℚ) / 2 - ∑ q ∈ c.primeFactors.filter (· ∣ 2 * m), f q * c.factorization q

/-- `N = ∑ v_q(c)` over the primes `q ∣ c` with `q ∤ 2m`. -/
def countOf (c m : ℕ) : ℕ := ∑ q ∈ c.primeFactors.filter (fun q => ¬ q ∣ 2 * m), c.factorization q

theorem omegaOf_congr {f g : ℕ → ℚ} {c m : ℕ} (d : ℕ)
    (h : ∀ q ∈ c.primeFactors, q ∣ 2 * m → f q = g q) : omegaOf f c d m = omegaOf g c d m := by
  unfold omegaOf
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_filter] at hq
  rw [h q hq.1 hq.2]

theorem omegaOf_le {f : ℕ → ℚ} {c m : ℕ} (d : ℕ)
    (h : ∀ q ∈ c.primeFactors, q ∣ 2 * m → 0 ≤ f q) : omegaOf f c d m ≤ (d : ℚ) / 2 := by
  unfold omegaOf
  have : 0 ≤ ∑ q ∈ c.primeFactors.filter (· ∣ 2 * m), f q * c.factorization q := by
    refine Finset.sum_nonneg fun q hq => ?_
    rw [Finset.mem_filter] at hq
    exact mul_nonneg (h q hq.1 hq.2) (Nat.cast_nonneg _)
  linarith

theorem le_countOf {c m p : ℕ} (hp : p.Prime) (hpc : p ∣ c) (hc : c ≠ 0)
    (hpm : ¬ p ∣ 2 * m) : c.factorization p ≤ countOf c m := by
  unfold countOf
  exact Finset.single_le_sum (f := fun q => c.factorization q) (fun _ _ => Nat.zero_le _)
    (Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp, hpc, hc⟩, hpm⟩)

/-- The home root of the prime `p`: a root of unity `r` with `r²` of order `ord_p(b)` and
`p ∣ c₀(r)`. -/
noncomputable def homeRoot (b p : ℕ) : ℂ :=
  open Classical in
  if h : ∃ r : ℂ, IsOfFinOrder r ∧ orderOf (r ^ 2) = orderOf ((b : ℕ) : ZMod p) ∧
      (p : ℤ) ∣ (minpoly ℤ (tB b - r)).eval 0 then h.choose else 1

theorem homeRoot_spec {b p : ℕ} (hp : p.Prime) (hpb : ¬ p ∣ b) :
    IsOfFinOrder (homeRoot b p) ∧
      orderOf (homeRoot b p ^ 2) = orderOf ((b : ℕ) : ZMod p) ∧
      (p : ℤ) ∣ (minpoly ℤ (tB b - homeRoot b p)).eval 0 := by
  have h := exists_home_root hp hpb
  rw [homeRoot, dite_eq_left h]
  exact h.choose_spec

/-- One step of the recursion: the weight of `p` from the weights `f` of the smaller primes. -/
noncomputable def lamStep (b : ℕ) (f : ℕ → ℚ) (p : ℕ) : ℚ :=
  if p ∣ b then 1 / ((b.primeFactors.card : ℚ) * b.factorization p)
  else if p = 2 then lamTwo b
  else omegaOf f (cAbs b (homeRoot b p)) (cDeg b (homeRoot b p)) (orderOf (homeRoot b p ^ 2)) /
    countOf (cAbs b (homeRoot b p)) (orderOf (homeRoot b p ^ 2))

/-- **The weight `λ_p`.** -/
noncomputable def lam (b : ℕ) (p : ℕ) : ℚ :=
  lamStep b (fun q => if _h : q < p then lam b q else 0) p
termination_by p

theorem lam_of_dvd {b p : ℕ} (h : p ∣ b) :
    lam b p = 1 / ((b.primeFactors.card : ℚ) * b.factorization p) := by
  rw [lam, lamStep, ite_eq_left h]

theorem lam_two {b : ℕ} (h : ¬ 2 ∣ b) : lam b 2 = lamTwo b := by
  rw [lam, lamStep, ite_eq_right h, ite_eq_left rfl]

/-- The weight of an odd prime `p ∤ b`, from the data of a root `r` with `r²` of order
`ord_p(b)` and `p ∣ c₀(r)`. -/
theorem lam_home {b p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpb : ¬ p ∣ b) :
    ∃ r : ℂ, IsOfFinOrder r ∧ orderOf (r ^ 2) = orderOf ((b : ℕ) : ZMod p) ∧
      (p : ℤ) ∣ (minpoly ℤ (tB b - r)).eval 0 ∧
      lam b p = omegaOf (lam b) (cAbs b r) (cDeg b r) (orderOf (r ^ 2)) /
        countOf (cAbs b r) (orderOf (r ^ 2)) := by
  obtain ⟨hr, hord, hd⟩ := homeRoot_spec hp hpb
  refine ⟨homeRoot b p, hr, hord, hd, ?_⟩
  rw [lam, lamStep, ite_eq_right hpb, ite_eq_right hp2]
  congr 1
  refine omegaOf_congr _ fun q hq hq2m => ?_
  have hq' := (Nat.mem_primeFactors.1 hq).1
  have he := orderOf_zmod_dvd_pred hp hpb
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hlt : q < p := by
    rcases (Nat.Prime.dvd_mul hq').1 hq2m with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hq' Nat.prime_two).1 h
      omega
    · rw [hord] at h
      have := Nat.le_of_dvd (by omega) (h.trans he)
      omega
  rw [dite_eq_left hlt]

/-- **The weight of a primitive prime.** If the prime `p` divides `c₀(r)` and not `2m`, `m` the
order of `r²`, then `λ_p = ω / N`, computed from `|c₀(r)|`, `d(r)` and `m`. -/
theorem lam_eq_of_dvd {b p : ℕ} {r : ℂ} (hr : IsOfFinOrder r) (hp : p.Prime)
    (hd : p ∣ cAbs b r) (hpm : ¬ p ∣ 2 * orderOf (r ^ 2)) :
    lam b p = omegaOf (lam b) (cAbs b r) (cDeg b r) (orderOf (r ^ 2)) /
      countOf (cAbs b r) (orderOf (r ^ 2)) := by
  have hd' := dvd_cAbs_iff.1 hd
  obtain ⟨hpb, a, ha⟩ := order_facts_of_dvd hp hr hd'
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpm (dvd_mul_right 2 _)
  have ha0 : a = 0 := by
    by_contra h0
    exact hpm ((dvd_pow_self p h0).trans ((Dvd.intro_left _ ha.symm).trans (dvd_mul_left _ 2)))
  rw [ha0, pow_zero, mul_one] at ha
  obtain ⟨r', hr', hord', hd'', hlam⟩ := lam_home hp hp2 hpb
  rw [← ha] at hord'
  have hm : r ^ (2 * orderOf (r ^ 2)) = 1 := by rw [pow_mul, pow_orderOf_eq_one]
  have hm' : r' ^ (2 * orderOf (r ^ 2)) = 1 := by rw [pow_mul, ← hord', pow_orderOf_eq_one]
  obtain ⟨h1, h2⟩ := data_eq_of_common_prime hr hr' hm hm' hp hpm hd' hd''
  rw [hlam, hord', h1, h2]

end BaseB

end PiFormula
