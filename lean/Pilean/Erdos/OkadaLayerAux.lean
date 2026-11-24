/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.OkadaDefs
public import Pilean.Erdos.ArithSeries

/-!
# The coefficient of `log p` (`OkadaLayerSum`), part 1: the general lemmas

`OkadaLayerSum` says `ℓ_p = c_p`: the sum of `g = okadaG q f` over the residues divisible by
`p` and by no other prime factor of `q` is `c_p = ∑_{r=1}^{q} f(r) λ(r, p)`. This file has the
part of the proof that does not depend on the weight `λ`; the weight and the theorem are in
`OkadaLayer.lean`.

* `lay_natCast_dvd_iff`: for `d ∣ q`, divisibility by `d` in `ℤ/q` is divisibility of
  representatives.
* `lay_card_fiber`: for `l ∣ q` and `r'` divisible by `l`, the equation `l r = r'` has exactly
  `l` solutions in `ℤ/q`.
* `lay_sum_Icc`: a sum over `1 ≤ r ≤ q` of a function of the class of `r` is a sum over `ℤ/q`.
* `lay_step`: one prime `p ∉ m`. If `∑_{r : p r = r'} w(r) = p w'(r')` for every `r'` divisible
  by `p`, then, with `A_m` the residues divisible by no prime of `m` and `h_m = Arith.serH`,
  `∑_{A_m} h_m w = ∑_{A_m} h_{m ∪ p} w - ∑_{A_m, p ∣ r} h_{m ∪ p} w'`. With `w' = w` this is
  `Arith.theta_insert`, with the condition on the weight at the inserted prime only
  (`lay_theta_insert`).
* `lay_main`: if `w` is harmonic at every prime `l ≠ p` of `q`, satisfies
  `∑_{r : p r = r'} w(r) = p (w(r') - 1)` for `p ∣ r'`, and vanishes off the multiples of `p`,
  then `ℓ_p = ∑_r f(r) w(r)`.
-/

@[expose] public section

open scoped BigOperators

namespace PiFormula

namespace Erdos

namespace Okada

variable {q : ℕ}

/-! ### Divisibility and counting in `ℤ/q` -/

/-- For `d ∣ q`, the class of `r` in `ℤ/q` is divisible by `d` exactly when `d ∣ r`. -/
theorem lay_natCast_dvd_iff [NeZero q] {d : ℕ} (hd : d ∣ q) (r : ℕ) :
    (d : ZMod q) ∣ (r : ZMod q) ↔ d ∣ r := by
  constructor
  · rintro ⟨y, hy⟩
    have h1 : ((d * y.val : ℕ) : ZMod q) = (r : ZMod q) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, hy]
    have h2 : d * y.val ≡ r [MOD q] := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
    exact (h2.dvd_iff hd).1 (dvd_mul_right _ _)
  · intro h
    exact Nat.cast_dvd_cast h

/-- If `a` and `b` are coprime and `a` divides `b r` in `ℤ/q`, then `a` divides `r`. -/
theorem lay_dvd_of_coprime_mul {a b : ℕ} (hab : a.Coprime b) {r : ZMod q}
    (h : (a : ZMod q) ∣ (b : ZMod q) * r) : (a : ZMod q) ∣ r := by
  have hc : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.2 hab
  obtain ⟨u, v, huv⟩ := hc
  have h1 : (u : ZMod q) * (a : ZMod q) + (v : ZMod q) * (b : ZMod q) = 1 := by
    have h0 := congrArg (Int.cast : ℤ → ZMod q) huv
    push_cast at h0
    exact h0
  have h2 : r = (a : ZMod q) * ((u : ZMod q) * r) + (v : ZMod q) * ((b : ZMod q) * r) := by
    linear_combination (-r) * h1
  rw [h2]
  exact dvd_add (dvd_mul_right _ _) (Dvd.dvd.mul_left h _)

/-- For `l ∣ q` and `r'` divisible by `l`, the equation `l r = r'` has exactly `l` solutions
in `ℤ/q`. -/
theorem lay_card_fiber [NeZero q] {l : ℕ} (hl : l ∣ q) {r' : ZMod q}
    (h : (l : ZMod q) ∣ r') :
    (Finset.univ.filter (fun r : ZMod q => (l : ZMod q) * r = r')).card = l := by
  classical
  obtain ⟨r0, rfl⟩ := h
  obtain ⟨n, rfl⟩ := hl
  have hq : l * n ≠ 0 := NeZero.ne (l * n)
  have hl0 : 0 < l := Nat.pos_of_ne_zero (left_ne_zero_of_mul hq)
  have hn0 : 0 < n := Nat.pos_of_ne_zero (right_ne_zero_of_mul hq)
  have hz : (l : ZMod (l * n)) * (n : ZMod (l * n)) = 0 := by
    rw [← Nat.cast_mul]
    exact ZMod.natCast_self (l * n)
  have hset : Finset.univ.filter
      (fun r : ZMod (l * n) => (l : ZMod (l * n)) * r = (l : ZMod (l * n)) * r0) =
      (Finset.range l).image (fun j : ℕ => r0 + ((n * j : ℕ) : ZMod (l * n))) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_range]
    constructor
    · intro h
      have h1 : ((l * (r - r0).val : ℕ) : ZMod (l * n)) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_sub, h, sub_self]
      have h2 : l * n ∣ l * (r - r0).val := (ZMod.natCast_eq_zero_iff _ _).1 h1
      obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_left hl0 h2
      have hlt : (r - r0).val < l * n := ZMod.val_lt _
      have hjl : j < l := by
        have h3 : n * j < n * l := by
          rw [← hj, mul_comm n l]
          exact hlt
        exact lt_of_mul_lt_mul_left h3 (Nat.zero_le n)
      refine ⟨j, hjl, ?_⟩
      rw [← hj, ZMod.natCast_zmod_val]
      ring
    · rintro ⟨j, -, rfl⟩
      push_cast
      linear_combination (j : ZMod (l * n)) * hz
  rw [hset, Finset.card_image_of_injOn, Finset.card_range]
  intro j hj j' hj' hjj'
  rw [Finset.mem_coe, Finset.mem_range] at hj hj'
  have h1 : ((n * j : ℕ) : ZMod (l * n)) = ((n * j' : ℕ) : ZMod (l * n)) :=
    add_left_cancel hjj'
  have h2 : n * j < l * n := by
    rw [mul_comm l n]
    exact Nat.mul_lt_mul_of_pos_left hj hn0
  have h3 : n * j' < l * n := by
    rw [mul_comm l n]
    exact Nat.mul_lt_mul_of_pos_left hj' hn0
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3] at h1
  exact Nat.eq_of_mul_eq_mul_left hn0 h1

/-- A sum over `1 ≤ r ≤ q` of a function of the class of `r` modulo `q` is a sum over
`ℤ/q` (the class `0` is represented by `q`). -/
theorem lay_sum_Icc [NeZero q] {M : Type*} [AddCommMonoid M] (F : ZMod q → M) :
    ∑ r ∈ Finset.Icc 1 q, F (r : ZMod q) = ∑ x : ZMod q, F x := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  refine Finset.sum_nbij' (fun r : ℕ => (r : ZMod q))
    (fun x : ZMod q => if x = 0 then q else x.val) ?_ ?_ ?_ ?_ ?_
  · intro r _
    exact Finset.mem_univ _
  · intro x _
    have hlt : x.val < q := ZMod.val_lt x
    by_cases hx : x = 0
    · simp only [hx, ↓reduceIte, Finset.mem_Icc]
      omega
    · have hne : x.val ≠ 0 := fun h => hx ((ZMod.val_eq_zero x).1 h)
      simp only [hx, ↓reduceIte, Finset.mem_Icc]
      omega
  · intro r hr
    rw [Finset.mem_Icc] at hr
    by_cases h : (r : ZMod q) = 0
    · have hd : q ∣ r := (ZMod.natCast_eq_zero_iff r q).1 h
      have hle : q ≤ r := Nat.le_of_dvd (by omega) hd
      simp only [h, ↓reduceIte]
      omega
    · have hlt : r < q := by
        rcases Nat.lt_or_ge r q with h1 | h1
        · exact h1
        · exfalso
          apply h
          have hrq : r = q := by omega
          rw [hrq]
          exact ZMod.natCast_self q
      simp only [h, ↓reduceIte]
      rw [ZMod.val_natCast]
      exact Nat.mod_eq_of_lt hlt
  · intro x _
    by_cases hx : x = 0
    · simp only [hx, ↓reduceIte]
      exact ZMod.natCast_self q
    · simp only [hx, ↓reduceIte]
      exact ZMod.natCast_zmod_val x
  · intro r _
    rfl

/-! ### The series -/

/-- The series over the numbers all of whose prime factors divide `q` is `okadaG`. -/
theorem lay_serH_primeFactors (f : ZMod q → ℚ) (r : ZMod q) :
    Arith.serH q f q.primeFactors r = okadaG q f r := by
  unfold Arith.serH okadaG
  refine tsum_congr fun j => ?_
  have hiff : j ∈ Nat.factoredNumbers q.primeFactors ↔ InM q j :=
    Nat.mem_factoredNumbers_iff_primeFactors_subset
  by_cases h : InM q j
  · simp only [h, hiff.2 h, ↓reduceIte]
  · simp only [h, mt hiff.1 h, ↓reduceIte]

open Classical in
/-- **One prime.** Let `p ∉ m` be a prime and let `w`, `w'` satisfy
`∑_{r : p r = r'} w(r) = p w'(r')` for every `r'` divisible by `p`. Then the sum of `h_m w`
over the residues divisible by no prime of `m` is the sum of `h_{m ∪ p} w` over the same
residues minus the sum of `h_{m ∪ p} w'` over those of them that are divisible by `p`. -/
theorem lay_step [NeZero q] (f : ZMod q → ℚ) (w w' : ZMod q → ℝ) {m : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpm : p ∉ m) (hm : ∀ l ∈ m, l.Prime)
    (hw : ∀ r' : ZMod q, (p : ZMod q) ∣ r' →
      ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (p : ZMod q) * r = r'), w r =
        (p : ℝ) * w' r') :
    ∑ r ∈ Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r),
        Arith.serH q f m r * w r =
      ∑ r ∈ Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r),
        Arith.serH q f (insert p m) r * w r -
      ∑ r ∈ (Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r)).filter
        (fun r => (p : ZMod q) ∣ r), Arith.serH q f (insert p m) r * w' r := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hmaps : ∀ r ∈ Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r),
      (p : ZMod q) * r ∈ (Finset.univ.filter
        (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r)).filter
          (fun r' => (p : ZMod q) ∣ r') := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact ⟨fun l hl hdiv => hr l hl (Arith.dvd_of_dvd_prime_mul (hm l hl) hp
      (ne_of_mem_of_not_mem hl hpm) hdiv), dvd_mul_right _ _⟩
  have hfib : ∑ r ∈ Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r),
      Arith.serH q f (insert p m) ((p : ZMod q) * r) * w r =
      ∑ r' ∈ (Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r)).filter
        (fun r' => (p : ZMod q) ∣ r'), Arith.serH q f (insert p m) r' * ((p : ℝ) * w' r') := by
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
    rw [hset, ← hw r' hr'1.2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [(Finset.mem_filter.1 hr).2]
  have hsub : ∑ r ∈ Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r),
      Arith.serH q f m r * w r =
      ∑ r ∈ Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r),
        Arith.serH q f (insert p m) r * w r -
      (∑ r ∈ Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r),
        Arith.serH q f (insert p m) ((p : ZMod q) * r) * w r) / p := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Arith.serH_insert f hp hpm r]
    ring
  have hdiv : (∑ r' ∈ (Finset.univ.filter
      (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r)).filter
        (fun r' => (p : ZMod q) ∣ r'),
          Arith.serH q f (insert p m) r' * ((p : ℝ) * w' r')) / p =
      ∑ r' ∈ (Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r)).filter
        (fun r' => (p : ZMod q) ∣ r'), Arith.serH q f (insert p m) r' * w' r' := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
  rw [hsub, hfib, hdiv]

open Classical in
/-- `Arith.theta_insert` with the condition on the weight at the inserted prime only. -/
theorem lay_theta_insert [NeZero q] (f : ZMod q → ℚ) (w : ZMod q → ℝ) {m : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpm : p ∉ m) (hm : ∀ l ∈ m, l.Prime)
    (hw : ∀ r' : ZMod q, (p : ZMod q) ∣ r' →
      ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (p : ZMod q) * r = r'), w r =
        (p : ℝ) * w r') :
    Arith.theta q f w (insert p m) = Arith.theta q f w m := by
  have hUins : Finset.univ.filter (fun r : ZMod q => ∀ l ∈ insert p m, ¬ (l : ZMod q) ∣ r) =
      (Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r)).filter
        (fun r => ¬ (p : ZMod q) ∣ r) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, forall_eq_or_imp]
    exact and_comm
  unfold Arith.theta
  rw [hUins, lay_step f w w hp hpm hm hw, ← Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun r : ZMod q => ∀ l ∈ m, ¬ (l : ZMod q) ∣ r))
    (fun r => (p : ZMod q) ∣ r) (fun r => Arith.serH q f (insert p m) r * w r)]
  ring

open Classical in
/-- **The layer sum as a weighted sum of `f`.** Let `p ∣ q` be a prime and let `w` be a
weight on `ℤ/q` such that `∑_{r : l r = r'} w(r) = l w(r')` for every prime `l ≠ p` of `q` and
every `r'` divisible by `l`; `∑_{r : p r = r'} w(r) = p (w(r') - 1)` for every `r'` divisible
by `p`; and `w(r) = 0` when `p ∤ r`. Then `ℓ_p = ∑_r f(r) w(r)`. -/
theorem lay_main [NeZero q] (f : ZMod q → ℚ) {p : ℕ} (hp : p.Prime) (hpq : p ∣ q)
    (w : ZMod q → ℝ)
    (hw1 : ∀ l : ℕ, l.Prime → l ∣ q → l ≠ p → ∀ r' : ZMod q, (l : ZMod q) ∣ r' →
      ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (l : ZMod q) * r = r'), w r =
        (l : ℝ) * w r')
    (hw2 : ∀ r' : ZMod q, (p : ZMod q) ∣ r' →
      ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (p : ZMod q) * r = r'), w r =
        (p : ℝ) * (w r' - 1))
    (hw3 : ∀ r : ZMod q, ¬ (p : ZMod q) ∣ r → w r = 0) :
    layerSum q f p = ∑ r : ZMod q, (f r : ℝ) * w r := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hind : ∀ m : Finset ℕ, m ⊆ q.primeFactors.erase p →
      Arith.theta q f w m = Arith.theta q f w ∅ := by
    intro m
    induction m using Finset.induction_on with
    | empty => exact fun _ => rfl
    | insert l m hlm ih =>
      intro hsub
      have hl := Finset.mem_erase.1 (hsub (Finset.mem_insert_self l m))
      have hl' := Nat.mem_primeFactors.1 hl.2
      rw [lay_theta_insert f w hl'.1 hlm
        (fun l' hl'' => (Nat.mem_primeFactors.1
          (Finset.mem_of_mem_erase (hsub (Finset.mem_insert_of_mem hl'')))).1)
        (hw1 l hl'.1 hl'.2.1 hl.1),
        ih (fun l' hl'' => hsub (Finset.mem_insert_of_mem hl''))]
  have hlayer : layer q p =
      (Finset.univ.filter
        (fun r : ZMod q => ∀ l ∈ q.primeFactors.erase p, ¬ (l : ZMod q) ∣ r)).filter
          (fun r => (p : ZMod q) ∣ r) := by
    ext r
    simp only [layer, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun l hl => h2 l hl.2 hl.1, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun l hl hne => h1 l ⟨hne, hl⟩⟩
  have hins : insert p (q.primeFactors.erase p) = q.primeFactors :=
    Finset.insert_erase (Nat.mem_primeFactors.2 ⟨hp, hpq, hq0⟩)
  have hstep := lay_step f w (fun r => w r - 1) hp (Finset.notMem_erase p q.primeFactors)
    (fun l hl => (Nat.mem_primeFactors.1 (Finset.mem_of_mem_erase hl)).1) hw2
  rw [hins] at hstep
  have h0 : ∑ r ∈ (Finset.univ.filter
      (fun r : ZMod q => ∀ l ∈ q.primeFactors.erase p, ¬ (l : ZMod q) ∣ r)).filter
        (fun r => ¬ (p : ZMod q) ∣ r), Arith.serH q f q.primeFactors r * w r = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [hw3 r (Finset.mem_filter.1 hr).2, mul_zero]
  rw [← Arith.theta_empty, ← hind _ subset_rfl]
  unfold Arith.theta
  rw [hstep, ← Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter
      (fun r : ZMod q => ∀ l ∈ q.primeFactors.erase p, ¬ (l : ZMod q) ∣ r))
    (fun r => (p : ZMod q) ∣ r) (fun r => Arith.serH q f q.primeFactors r * w r),
    h0, add_zero, ← Finset.sum_sub_distrib]
  unfold layerSum
  rw [hlayer]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [lay_serH_primeFactors]
  ring

end Okada

end Erdos

end PiFormula
