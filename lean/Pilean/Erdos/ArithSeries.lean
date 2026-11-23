import Pilean.Erdos.Defs
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Theorem A from the abstract theorem, part 4: the series of condition (a)

This file contains all the analysis of the proof of Lemma 2 (paper: section 3). The result is
`sum_eq_zero_of_harmonic`:

Let `w : ℤ/q → ℝ` satisfy `∑_{r : p r = r'} w(r) = p w(r')` for every prime `p ∣ q` and every
`r'` divisible by `p`. If `f` satisfies condition (a), then `∑_r f(r) w(r) = 0`.

Proof. For a finite set `m` of primes put `h_m(r) = ∑_j f(r j)/j`, the sum over the `j ≥ 1` all
of whose prime factors lie in `m` (`serH`; absolutely convergent). Then `h_∅ = f`, and
`h_m(r) = h_{m ∪ p}(r) - h_{m ∪ p}(p r)/p` for a prime `p ∉ m` (`serH_insert`: split the `j`
according to `p ∣ j`). Hence the sum `θ(m)` of `h_m(r) w(r)` over the `r` divisible by no prime
of `m` does not depend on `m` (`theta_insert`). `θ(∅) = ∑_r f(r) w(r)`, and `θ` of the set of
all primes dividing `q` is a sum over the units of `g(a) w(a)`, which is `0` by (a).
-/

open scoped BigOperators

namespace PiFormula

namespace Erdos

namespace Arith

variable {q : ℕ}

/-- `h_m(r) = ∑_j f(r j)/j` over the `j ≥ 1` all of whose prime factors lie in `m`. -/
noncomputable def serH (q : ℕ) (f : ZMod q → ℚ) (m : Finset ℕ) (r : ZMod q) : ℝ :=
  ∑' j : ℕ, if j ∈ Nat.factoredNumbers m then (f (r * (j : ZMod q)) : ℝ) / (j : ℝ) else 0

theorem summable_inv_factored (m : Finset ℕ) :
    Summable (fun j : ℕ => if j ∈ Nat.factoredNumbers m then ((j : ℝ))⁻¹ else 0) := by
  let φ : ℕ →* ℝ :=
    { toFun := fun j => ((j : ℝ))⁻¹
      map_one' := by simp
      map_mul' := by
        intro a b
        simp [mul_comm] }
  have hφ : ∀ {p : ℕ}, p.Prime → ‖φ p‖ < 1 := by
    intro p hp
    change ‖((p : ℝ))⁻¹‖ < 1
    rw [norm_inv, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    hφ m).1
  have h' : Summable ((fun j : ℕ => ((j : ℝ))⁻¹) ∘
      (Subtype.val : Nat.factoredNumbers m → ℕ)) := by
    refine h.congr fun j => ?_
    change ‖(((j : ℕ) : ℝ))⁻¹‖ = ((j : ℕ) : ℝ)⁻¹
    rw [norm_inv, Real.norm_natCast]
  rw [summable_subtype_iff_indicator] at h'
  refine h'.congr fun j => ?_
  simp [Set.indicator_apply]

theorem summable_serH [NeZero q] (f : ZMod q → ℚ) (m : Finset ℕ) (c : ℕ → ZMod q) :
    Summable (fun j : ℕ =>
      if j ∈ Nat.factoredNumbers m then (f (c j) : ℝ) / (j : ℝ) else 0) := by
  have hC : ∀ x : ZMod q, |(f x : ℝ)| ≤ ∑ x : ZMod q, |(f x : ℝ)| := fun x =>
    Finset.single_le_sum (f := fun x : ZMod q => |(f x : ℝ)|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ x)
  refine Summable.of_norm_bounded
    ((summable_inv_factored m).mul_left (∑ x : ZMod q, |(f x : ℝ)|)) ?_
  intro j
  split_ifs with h
  · rw [Real.norm_eq_abs, abs_div, Nat.abs_cast, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hC _) (inv_nonneg.2 (Nat.cast_nonneg j))
  · simp

theorem serH_empty (f : ZMod q → ℚ) (r : ZMod q) : serH q f ∅ r = (f r : ℝ) := by
  unfold serH
  rw [tsum_eq_single 1]
  · simp
  · intro j hj
    simp [hj]

/-- `h_m(r) = h_{m ∪ p}(r) - h_{m ∪ p}(p r)/p`. -/
theorem serH_insert [NeZero q] (f : ZMod q → ℚ) {m : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hpm : p ∉ m) (r : ZMod q) :
    serH q f (insert p m) r - serH q f (insert p m) ((p : ZMod q) * r) / p = serH q f m r := by
  have hm1 : ∀ j : ℕ, p ∣ j → j ∉ Nat.factoredNumbers m := by
    intro j hpj hj
    exact hpm (Nat.mem_factoredNumbers'.1 hj p hp hpj)
  have hm2 : ∀ j : ℕ, ¬ p ∣ j →
      (j ∈ Nat.factoredNumbers (insert p m) ↔ j ∈ Nat.factoredNumbers m) := by
    intro j hpj
    rw [Nat.mem_factoredNumbers', Nat.mem_factoredNumbers']
    constructor
    · intro h l hl hlj
      rcases Finset.mem_insert.1 (h l hl hlj) with e | e
      · exact absurd (e ▸ hlj) hpj
      · exact e
    · intro h l hl hlj
      exact Finset.mem_insert_of_mem (h l hl hlj)
  have hm3 : ∀ i : ℕ,
      (p * i ∈ Nat.factoredNumbers (insert p m) ↔ i ∈ Nat.factoredNumbers (insert p m)) := by
    intro i
    constructor
    · intro h
      exact Nat.mem_factoredNumbers_of_dvd h (dvd_mul_left i p)
    · intro h
      have hpF : p ∈ Nat.factoredNumbers (insert p m) := by
        rw [Nat.mem_factoredNumbers']
        intro l hl hlp
        rw [(Nat.prime_dvd_prime_iff_eq hl hp).1 hlp]
        exact Finset.mem_insert_self p m
      exact Nat.mul_mem_factoredNumbers hpF h
  have hA : Summable (fun j : ℕ => if j ∈ Nat.factoredNumbers (insert p m) then
      (f (r * (j : ZMod q)) : ℝ) / (j : ℝ) else 0) := summable_serH f _ _
  have hB : Summable (fun j : ℕ => if j ∈ Nat.factoredNumbers m then
      (f (r * (j : ZMod q)) : ℝ) / (j : ℝ) else 0) := summable_serH f _ _
  have hsplit : ∀ j : ℕ, (if j ∈ Nat.factoredNumbers (insert p m) then
      (f (r * (j : ZMod q)) : ℝ) / (j : ℝ) else 0) =
      (if j ∈ Nat.factoredNumbers m then (f (r * (j : ZMod q)) : ℝ) / (j : ℝ) else 0) +
      (if p ∣ j then (if j ∈ Nat.factoredNumbers (insert p m) then
        (f (r * (j : ZMod q)) : ℝ) / (j : ℝ) else 0) else 0) := by
    intro j
    by_cases hpj : p ∣ j
    · simp only [hpj, hm1 j hpj, ↓reduceIte, zero_add]
    · by_cases hj : j ∈ Nat.factoredNumbers m
      · simp only [hpj, hj, (hm2 j hpj).2 hj, ↓reduceIte, add_zero]
      · simp only [hpj, hj, mt (hm2 j hpj).1 hj, ↓reduceIte, add_zero]
  have hG : Summable (fun j : ℕ => if p ∣ j then
      (if j ∈ Nat.factoredNumbers (insert p m) then
        (f (r * (j : ZMod q)) : ℝ) / (j : ℝ) else 0) else 0) := by
    refine (hA.sub hB).congr fun j => ?_
    exact sub_eq_of_eq_add' (hsplit j)
  have h1 : serH q f (insert p m) r = serH q f m r +
      ∑' j : ℕ, (if p ∣ j then (if j ∈ Nat.factoredNumbers (insert p m) then
        (f (r * (j : ZMod q)) : ℝ) / (j : ℝ) else 0) else 0) := by
    unfold serH
    rw [← hB.tsum_add hG]
    exact tsum_congr hsplit
  have h2 : ∑' j : ℕ, (if p ∣ j then (if j ∈ Nat.factoredNumbers (insert p m) then
        (f (r * (j : ZMod q)) : ℝ) / (j : ℝ) else 0) else 0) =
      ∑' i : ℕ, (if p ∣ p * i then (if p * i ∈ Nat.factoredNumbers (insert p m) then
        (f (r * ((p * i : ℕ) : ZMod q)) : ℝ) / ((p * i : ℕ) : ℝ) else 0) else 0) := by
    symm
    refine (mul_right_injective₀ hp.ne_zero).tsum_eq
      (f := fun j : ℕ => if p ∣ j then (if j ∈ Nat.factoredNumbers (insert p m) then
        (f (r * (j : ZMod q)) : ℝ) / (j : ℝ) else 0) else 0) ?_
    intro j hj
    by_cases hpj : p ∣ j
    · obtain ⟨i, rfl⟩ := hpj
      exact ⟨i, rfl⟩
    · exfalso
      apply hj
      simp only [hpj, ↓reduceIte]
  have h3 : serH q f (insert p m) ((p : ZMod q) * r) / p =
      ∑' i : ℕ, (if p ∣ p * i then (if p * i ∈ Nat.factoredNumbers (insert p m) then
        (f (r * ((p * i : ℕ) : ZMod q)) : ℝ) / ((p * i : ℕ) : ℝ) else 0) else 0) := by
    unfold serH
    rw [← tsum_div_const]
    refine tsum_congr fun i => ?_
    have e : (p : ZMod q) * r * (i : ZMod q) = r * ((p * i : ℕ) : ZMod q) := by
      push_cast
      ring
    by_cases hi : i ∈ Nat.factoredNumbers (insert p m)
    · simp only [hi, (hm3 i).2 hi, dvd_mul_right, ↓reduceIte]
      rw [e, div_div]
      push_cast
      rw [mul_comm (i : ℝ) (p : ℝ)]
    · simp only [hi, mt (hm3 i).1 hi, ↓reduceIte, ite_self, zero_div]
  rw [h1, h2, h3]
  ring

/-- If `l ≠ p` are primes and `l` divides `p r` in `ℤ/q`, then `l` divides `r`. -/
theorem dvd_of_dvd_prime_mul {l p : ℕ} (hl : l.Prime) (hp : p.Prime) (hne : l ≠ p)
    {r : ZMod q} (h : (l : ZMod q) ∣ (p : ZMod q) * r) : (l : ZMod q) ∣ r := by
  have hc : IsCoprime (l : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hl hp).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : ZMod q) * (l : ZMod q) + (b : ZMod q) * (p : ZMod q) = 1 := by
    have h0 := congrArg (Int.cast : ℤ → ZMod q) hab
    push_cast at h0
    exact h0
  have h2 : r = (l : ZMod q) * ((a : ZMod q) * r) + (b : ZMod q) * ((p : ZMod q) * r) := by
    linear_combination (-r) * h1
  rw [h2]
  exact dvd_add (dvd_mul_right _ _) (Dvd.dvd.mul_left h _)

open Classical in
/-- The sum of `h_m(r) w(r)` over the `r` divisible by no prime of `m`. -/
noncomputable def theta (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (w : ZMod q → ℝ) (m : Finset ℕ) :
    ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r), serH q f m r * w r

theorem theta_empty [NeZero q] (f : ZMod q → ℚ) (w : ZMod q → ℝ) :
    theta q f w ∅ = ∑ r : ZMod q, (f r : ℝ) * w r := by
  unfold theta
  simp [serH_empty]

theorem theta_insert [NeZero q] (f : ZMod q → ℚ) (w : ZMod q → ℝ)
    (hw : ∀ p : ℕ, p.Prime → p ∣ q → ∀ r' : ZMod q, (p : ZMod q) ∣ r' →
      ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (p : ZMod q) * r = r'), w r = (p : ℝ) * w r')
    {m : Finset ℕ} {p : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hpm : p ∉ m)
    (hm : ∀ l ∈ m, l.Prime) : theta q f w (insert p m) = theta q f w m := by
  classical
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hUins : Finset.univ.filter (fun r : ZMod q => ∀ l ∈ insert p m, ¬ (l : ZMod q) ∣ r) =
      (Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r)).filter
        (fun r => ¬ (p : ZMod q) ∣ r) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, forall_eq_or_imp]
    exact and_comm
  have hmaps : ∀ r ∈ Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r),
      (p : ZMod q) * r ∈ (Finset.univ.filter
        (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r)).filter
          (fun r' => (p : ZMod q) ∣ r') := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact ⟨fun l hl hdiv => hr l hl (dvd_of_dvd_prime_mul (hm l hl) hp
      (ne_of_mem_of_not_mem hl hpm) hdiv), dvd_mul_right _ _⟩
  have hfib : ∑ r ∈ Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r),
      serH q f (insert p m) ((p : ZMod q) * r) * w r =
      ∑ r' ∈ (Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r)).filter
        (fun r' => (p : ZMod q) ∣ r'), serH q f (insert p m) r' * ((p : ℝ) * w r') := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun r' hr' => ?_
    have hr'1 := Finset.mem_filter.1 hr'
    have hr'2 : ∀ l ∈ m, ¬ (l : ZMod q) ∣ r' := by
      have := hr'1.1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hset : (Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r)).filter
        (fun r => (p : ZMod q) * r = r') =
        Finset.univ.filter (fun r : ZMod q => (p : ZMod q) * r = r') := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨fun l hl hdiv => ?_, h⟩
        apply hr'2 l hl
        rw [← h]
        exact Dvd.dvd.mul_left hdiv _
    rw [hset, ← hw p hp hpq r' hr'1.2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [(Finset.mem_filter.1 hr).2]
  have hsub : ∑ r ∈ Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r),
      serH q f m r * w r =
      ∑ r ∈ Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r),
        serH q f (insert p m) r * w r -
      (∑ r ∈ Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r),
        serH q f (insert p m) ((p : ZMod q) * r) * w r) / p := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← serH_insert f hp hpm r]
    ring
  have hdiv : (∑ r' ∈ (Finset.univ.filter
      (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r)).filter
        (fun r' => (p : ZMod q) ∣ r'), serH q f (insert p m) r' * ((p : ℝ) * w r')) / p =
      ∑ r' ∈ (Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r)).filter
        (fun r' => (p : ZMod q) ∣ r'), serH q f (insert p m) r' * w r' := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
  unfold theta
  rw [hUins, hsub, hfib, hdiv, ← Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r))
    (fun r => (p : ZMod q) ∣ r) (fun r => serH q f (insert p m) r * w r)]
  ring

/-- **The analytic step of Lemma 2.** If `∑_{r : p r = r'} w(r) = p w(r')` for every prime
`p ∣ q` and every `r'` divisible by `p`, and `f` satisfies condition (a), then
`∑_r f(r) w(r) = 0`. -/
theorem sum_eq_zero_of_harmonic [NeZero q] (f : ZMod q → ℚ) (w : ZMod q → ℝ)
    (hw : ∀ p : ℕ, p.Prime → p ∣ q → ∀ r' : ZMod q, (p : ZMod q) ∣ r' →
      ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (p : ZMod q) * r = r'), w r = (p : ℝ) * w r')
    (ha : CondA q f) : ∑ r : ZMod q, (f r : ℝ) * w r = 0 := by
  classical
  have hind : ∀ m : Finset ℕ, m ⊆ q.primeFactors → theta q f w m = theta q f w ∅ := by
    intro m
    induction m using Finset.induction_on with
    | empty => exact fun _ => rfl
    | insert p m hpm ih =>
      intro hsub
      have hp := Nat.mem_primeFactors.1 (hsub (Finset.mem_insert_self p m))
      rw [theta_insert f w hw hp.1 hp.2.1 hpm
        (fun l hl => (Nat.mem_primeFactors.1 (hsub (Finset.mem_insert_of_mem hl))).1),
        ih (fun l hl => hsub (Finset.mem_insert_of_mem hl))]
  rw [← theta_empty, ← hind q.primeFactors subset_rfl]
  unfold theta
  refine Finset.sum_eq_zero fun r hr => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
  have hunit : IsUnit r := by
    rw [← ZMod.natCast_zmod_val r, ZMod.isUnit_iff_coprime]
    by_contra hcop
    obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.1 hcop
    apply hr p (Nat.mem_primeFactors.2 ⟨hp, hp2, NeZero.ne q⟩)
    rw [← ZMod.natCast_zmod_val r]
    exact Nat.cast_dvd_cast hp1
  have hG : serH q f q.primeFactors r = okadaG q f r := by
    unfold serH okadaG
    refine tsum_congr fun j => ?_
    have hiff : j ∈ Nat.factoredNumbers q.primeFactors ↔ InM q j :=
      Nat.mem_factoredNumbers_iff_primeFactors_subset
    by_cases h : InM q j
    · simp only [h, hiff.2 h, ↓reduceIte]
    · simp only [h, mt hiff.1 h, ↓reduceIte]
  rw [hG, ha r hunit, zero_mul]

end Arith

end Erdos

end PiFormula
