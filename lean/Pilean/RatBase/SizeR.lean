module

public import Pilean.RatBase.ClassDefs

/-!
# The size condition for every rational base `p/q` with `p ≥ 16`

`SizeCondR p q m` (file `ClassDefs`) says that `Φ_m(p, q)` exceeds `(√p + √q)^φ(m)`, and exceeds
`ℓ (√p + √q)^φ(m)` for every prime `ℓ` that divides both `m` and `Φ_m(p, q)`. Here it is proved
for all `p > q ≥ 1` with `p ≥ 16` and every `m ≥ 3` (`sizeCondR_of_sixteen_le`; `sizeCondR` is
the same statement for `p ≥ 20`). The numbers `p`, `q` need not be coprime, and the hypothesis
`ℓ ∣ Φ_m(p, q)` is not used.

Write `a = √p`, `b = √q`, `φ = φ(m)`. Two lower bounds for `Φ_m(p, q) = q^φ Φ_m(p/q)`:

* `(p - q)^φ < Φ_m(p, q)` (`sub_pow_lt_cycValR`), from Mathlib's `(x - 1)^φ < Φ_m(x)`;
* `(a b)^φ < Φ_m(p, q)` (`sqrt_mul_sqrt_pow_lt_cycValR`), from `√x^φ Φ_m(1) < Φ_m(x)` for
  `x > 1` (`sqrt_pow_totient_mul_eval_one_lt_cyclotomic_eval`): for a root of unity `μ ≠ 1`,
  `|x - μ|² = (x - 1)² + x |1 - μ|²`, the product of the `|1 - μ|` over the primitive `m`-th
  roots is `Φ_m(1)`, and `Φ_m(1) ≥ 1`. This bound does not degenerate when `q` is close to `p`.

Since `p - q = (a - b)(a + b)`, the quotient of the larger bound by `(a + b)^φ` is
`max(a - b, a b / (a + b))^φ`, and for `a ≥ 4` the maximum is at least `3/2`: if `a - b < 3/2`
then `a b - (3/2)(a + b) > (a - 3/2)² - (3/2) a = (a - 4)(a - 1/2) + 1/4 > 0`. So it is enough
that `ℓ ≤ (3/2)^φ`. This holds for every prime `ℓ ∣ m` (by `φ ≥ 2`, `φ ≥ ℓ - 1`, and `φ ≥ 4`
when `3 ∣ m` and `m ≠ 3, 6`), except for `ℓ = 3` and `m = 3, 6`, where the values
`Φ_3(p, q) = p² + p q + q²` and `Φ_6(p, q) = p² - p q + q²` exceed `6 (p + q) ≥ 3 (a + b)²`.
-/

@[expose] public section

open Polynomial

namespace PiFormula

namespace RatBase

/-! ## 1. A lower bound for the cyclotomic polynomials that is good near 1 -/

/-- For a complex number `μ` of absolute value 1 and a real `x > 1`: `√x |1 - μ| < |x - μ|`,
because `|x - μ|² = (x - 1)² + x |1 - μ|²`. -/
private theorem sqrt_mul_norm_one_sub_lt {μ : ℂ} {x : ℝ} (hμ : ‖μ‖ = 1) (hx : 1 < x) :
    Real.sqrt x * ‖1 - μ‖ < ‖(x : ℂ) - μ‖ := by
  refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
  have h1 : μ.re * μ.re + μ.im * μ.im = 1 := by
    have h := Complex.sq_norm μ
    rw [hμ, Complex.normSq_apply] at h
    linarith
  rw [mul_pow, Real.sq_sqrt (by linarith), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
    Complex.ofReal_im]
  have h2 : (x - μ.re) * (x - μ.re) + (0 - μ.im) * (0 - μ.im) -
      x * ((1 - μ.re) * (1 - μ.re) + (0 - μ.im) * (0 - μ.im)) = (x - 1) ^ 2 := by
    linear_combination (1 - x) * h1
  have h3 : 0 < (x - 1) ^ 2 := pow_pos (sub_pos.2 hx) 2
  linarith

/-- `Φ_m(y) = ∏ (y - μ)` over the primitive `m`-th roots of unity `μ`. -/
private theorem eval_cyclotomic_eq_prod {m : ℕ} (hm : m ≠ 0) (y : ℂ) :
    (cyclotomic m ℂ).eval y = ∏ μ ∈ primitiveRoots m ℂ, (y - μ) := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp m hm), eval_prod]
  simp

/-- For `m ≥ 3`, the absolute value of `Φ_m` at a real point, computed in `ℂ`, is its value. -/
private theorem norm_eval_cyclotomic_ofReal {m : ℕ} (hm : 3 ≤ m) (x : ℝ) :
    ‖(cyclotomic m ℂ).eval (x : ℂ)‖ = (cyclotomic m ℝ).eval x := by
  have h := (cyclotomic m ℝ).eval₂_at_apply Complex.ofRealHom x
  rw [← eval_map, map_cyclotomic] at h
  rw [Complex.ofRealHom_eq_coe, Complex.ofRealHom_eq_coe] at h
  rw [h, Complex.norm_real, Real.norm_of_nonneg (cyclotomic_pos (by omega) x).le]

/-- `√x ^ φ(m) Φ_m(1) < Φ_m(x)` for a real `x > 1` and `m ≥ 3`. -/
theorem sqrt_pow_totient_mul_eval_one_lt_cyclotomic_eval {m : ℕ} {x : ℝ} (hm : 3 ≤ m)
    (hx : 1 < x) :
    Real.sqrt x ^ m.totient * (cyclotomic m ℝ).eval 1 < (cyclotomic m ℝ).eval x := by
  have hm0 : m ≠ 0 := by omega
  have hmpos : 0 < m := by omega
  rw [← norm_eval_cyclotomic_ofReal hm 1, ← norm_eval_cyclotomic_ofReal hm x,
    eval_cyclotomic_eq_prod hm0, eval_cyclotomic_eq_prod hm0, norm_prod, norm_prod,
    ← Complex.card_primitiveRoots m, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_lt_prod_of_nonempty₀ ?_ ?_ ?_
  · intro μ hμ
    have hμ' : μ ≠ 1 := ((mem_primitiveRoots hmpos).1 hμ).ne_one (by omega)
    have h1 : 0 < ‖((1 : ℝ) : ℂ) - μ‖ := by
      rw [norm_pos_iff, Complex.ofReal_one, sub_ne_zero]
      exact hμ'.symm
    have h2 : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    exact mul_pos h2 h1
  · intro μ hμ
    have h := sqrt_mul_norm_one_sub_lt (((mem_primitiveRoots hmpos).1 hμ).norm'_eq_one hm0) hx
    rwa [Complex.ofReal_one]
  · exact ⟨_, (mem_primitiveRoots hmpos).2 (Complex.isPrimitiveRoot_exp m hm0)⟩

/-- `Φ_m(1) ≥ 1` for `m ≥ 3`. -/
private theorem one_le_eval_one_cyclotomic {m : ℕ} (hm : 3 ≤ m) :
    1 ≤ (cyclotomic m ℝ).eval 1 := by
  have h0 : (1 : ℤ) ≤ (cyclotomic m ℤ).eval 1 :=
    cyclotomic_pos (n := m) (by omega) (1 : ℤ)
  have h := eval_intCast_map (Int.castRingHom ℝ) (cyclotomic m ℤ) 1
  rw [map_cyclotomic, Int.cast_one, eq_intCast] at h
  rw [h]
  exact_mod_cast h0

/-! ## 2. Two lower bounds for `Φ_m(p, q)` -/

/-- `Φ_m(p, q) = Φ_m(p/q) q^φ(m)`, in the real numbers. -/
private theorem cast_cycValR_eq_eval {p q : ℕ} (m : ℕ) (hq : 0 < q) :
    ((cycValR p q m : ℤ) : ℝ) =
      (cyclotomic m ℝ).eval ((p : ℝ) / q) * (q : ℝ) ^ m.totient := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← TauCeti.homogeneousCyclotomic_eq_eval_div_mul_pow m (p : ℝ) hq']
  simp [cycValR]

private theorem one_lt_cast_div {p q : ℕ} (hq : 0 < q) (hqp : q < p) : 1 < (p : ℝ) / q := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [one_lt_div hq']
  exact_mod_cast hqp

/-- `(p - q)^φ(m) < Φ_m(p, q)` for `p > q ≥ 1` and `m ≥ 2`. -/
theorem sub_pow_lt_cycValR {p q m : ℕ} (hq : 0 < q) (hqp : q < p) (hm : 2 ≤ m) :
    ((p : ℝ) - q) ^ m.totient < ((cycValR p q m : ℤ) : ℝ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h := sub_one_pow_totient_lt_cyclotomic_eval hm (one_lt_cast_div hq hqp)
  have he : ((p : ℝ) - q) ^ m.totient =
      ((p : ℝ) / q - 1) ^ m.totient * (q : ℝ) ^ m.totient := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [cast_cycValR_eq_eval m hq, he]
  exact mul_lt_mul_of_pos_right h (by positivity)

/-- `(√p √q)^φ(m) < Φ_m(p, q)` for `p > q ≥ 1` and `m ≥ 3`. -/
theorem sqrt_mul_sqrt_pow_lt_cycValR {p q m : ℕ} (hq : 0 < q) (hqp : q < p) (hm : 3 ≤ m) :
    (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) ^ m.totient < ((cycValR p q m : ℤ) : ℝ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h := sqrt_pow_totient_mul_eval_one_lt_cyclotomic_eval hm (one_lt_cast_div hq hqp)
  have h1 := one_le_eval_one_cyclotomic hm
  have hsq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hq'
  have he : (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) ^ m.totient =
      Real.sqrt ((p : ℝ) / q) ^ m.totient * (q : ℝ) ^ m.totient := by
    rw [← mul_pow]
    congr 1
    rw [Real.sqrt_div (Nat.cast_nonneg p)]
    nth_rewrite 3 [← Real.mul_self_sqrt hq'.le]
    field_simp
  rw [cast_cycValR_eq_eval m hq, he]
  refine mul_lt_mul_of_pos_right (lt_of_le_of_lt ?_ h) (by positivity)
  exact le_mul_of_one_le_right (by positivity) h1

/-! ## 3. The criterion `ℓ ≤ (3/2)^φ(m)` -/

/-- For `p ≥ 16`: if `L ≤ (3/2)^k` with `k ≤ φ(m)`, then `L (√p + √q)^φ(m) < Φ_m(p, q)`. -/
theorem mul_sqrt_add_sqrt_pow_lt_cycValR {p q m k : ℕ} {L : ℝ} (hp : 16 ≤ p) (hq : 0 < q)
    (hqp : q < p) (hm : 3 ≤ m) (hk : k ≤ m.totient) (hL : L ≤ (3 / 2 : ℝ) ^ k) :
    L * (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ m.totient < ((cycValR p q m : ℤ) : ℝ) := by
  have ha2 : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  have hb2 : Real.sqrt (q : ℝ) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  have hA := sub_pow_lt_cycValR hq hqp (by omega : 2 ≤ m)
  have hB := sqrt_mul_sqrt_pow_lt_cycValR hq hqp hm
  have ha : (4 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    have h16 : (16 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hb : (1 : ℝ) ≤ Real.sqrt (q : ℝ) := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    exact Real.le_sqrt_of_sq_le (by linarith)
  generalize Real.sqrt (p : ℝ) = a at *
  generalize Real.sqrt (q : ℝ) = b at *
  have hpos : 0 < (a + b) ^ m.totient := by positivity
  have hL' : L * (a + b) ^ m.totient ≤ (3 / 2 * (a + b)) ^ m.totient := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      (hL.trans (pow_le_pow_right₀ (by norm_num) hk)) hpos.le
  by_cases hab : 3 / 2 ≤ a - b
  · -- `q` small: use `(p - q)^φ`
    have h1 : 3 / 2 * (a + b) ≤ (p : ℝ) - q := by nlinarith
    exact (hL'.trans (pow_le_pow_left₀ (by positivity) h1 _)).trans_lt hA
  · -- `q` close to `p`: use `(√p √q)^φ`
    have h1 : 3 / 2 * (a + b) ≤ a * b := by
      have h2 : 0 < (b - (a - 3 / 2)) * (a - 3 / 2) :=
        mul_pos (by linarith) (by linarith)
      have h3 : 0 ≤ (a - 4) * (a - 1 / 2) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    exact (hL'.trans (pow_le_pow_left₀ (by positivity) h1 _)).trans_lt hB

/-- A prime `ℓ` that divides `m ≥ 3` is at most `(3/2)^k` for some `k ≤ φ(m)`, unless `ℓ = 3`
and `m` is `3` or `6`. -/
private theorem exists_le_totient_le_pow {ℓ m : ℕ} (hm : 3 ≤ m) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (h3 : ¬ (ℓ = 3 ∧ (m = 3 ∨ m = 6))) :
    ∃ k, k ≤ m.totient ∧ (ℓ : ℝ) ≤ (3 / 2 : ℝ) ^ k := by
  have hm0 : 0 < m := by omega
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  by_cases h5 : 5 ≤ ℓ
  · refine ⟨ℓ - 1, BaseB.pred_le_totient hℓ hm0 hℓm, ?_⟩
    have hcast : (ℓ : ℝ) = ((ℓ - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [hcast]
    exact BaseB.succ_le_pow (n₀ := 4) (by norm_num) (by norm_num) (by norm_num) _ (by omega)
  · have hℓ' : ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 4 := by omega
    rcases hℓ' with rfl | rfl | rfl
    · exact ⟨2, BaseB.two_le_totient hm, by norm_num⟩
    · have h4 : 2 * (3 - 1) ≤ m.totient :=
        BaseB.two_mul_pred_le_totient hℓ hm0 hℓm (fun h => h3 ⟨rfl, Or.inl h⟩)
          (fun h => h3 ⟨rfl, Or.inr h⟩)
      exact ⟨4, h4, by norm_num⟩
    · exact absurd hℓ (by norm_num)

/-! ## 4. The size condition -/

/-- The size condition holds for all `p > q ≥ 1` with `p ≥ 16` and every `m ≥ 3`. -/
theorem sizeCondR_of_sixteen_le {p q m : ℕ} (hp : 16 ≤ p) (hq : 0 < q) (hqp : q < p)
    (hm : 3 ≤ m) : SizeCondR p q m := by
  refine ⟨?_, ?_⟩
  · have h := mul_sqrt_add_sqrt_pow_lt_cycValR (k := 0) (L := 1) hp hq hqp hm (Nat.zero_le _)
      (by norm_num)
    rwa [one_mul] at h
  · intro ℓ hℓ hℓm _
    by_cases h3 : ℓ = 3 ∧ (m = 3 ∨ m = 6)
    · have ha2 : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
      have hb2 : Real.sqrt (q : ℝ) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
      have hp' : (16 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have hq' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hqp' : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqp
      have hs : (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ 2 ≤ 2 * ((p : ℝ) + q) := by
        nlinarith [sq_nonneg (Real.sqrt (p : ℝ) - Real.sqrt (q : ℝ))]
      obtain ⟨rfl, rfl | rfl⟩ := h3
      · -- `3 (√p + √q)² ≤ 6 (p + q) < p² + p q + q²`
        have ht : Nat.totient 3 = 2 := by decide
        rw [ht, cycValR, TauCeti.homogeneousCyclotomic_three]
        push_cast
        nlinarith [mul_nonneg (sub_nonneg.2 hp') (by linarith : (0 : ℝ) ≤ (p : ℝ)),
          mul_nonneg (sub_nonneg.2 hp') (by linarith : (0 : ℝ) ≤ (q : ℝ))]
      · -- `3 (√p + √q)² ≤ 6 (p + q) < p² - p q + q²`
        have ht : Nat.totient 6 = 2 := by decide
        rw [ht, cycValR, TauCeti.homogeneousCyclotomic_six]
        push_cast
        nlinarith [mul_nonneg (sub_nonneg.2 hp') (by linarith : (0 : ℝ) ≤ (p : ℝ)),
          sq_nonneg (2 * (q : ℝ) - p - 6)]
    · obtain ⟨k, hk, hℓk⟩ := exists_le_totient_le_pow hm hℓ hℓm h3
      exact mul_sqrt_add_sqrt_pow_lt_cycValR hp hq hqp hm hk hℓk

/-- The size condition holds for all `p > q ≥ 1` with `p ≥ 20` and every `m ≥ 3`. -/
theorem sizeCondR {p q m : ℕ} (hp : 20 ≤ p) (hq : 0 < q) (hqp : q < p) (hm : 3 ≤ m) :
    SizeCondR p q m :=
  sizeCondR_of_sixteen_le (by omega) hq hqp hm

end RatBase

end PiFormula
