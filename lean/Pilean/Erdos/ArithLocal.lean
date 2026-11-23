import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Theorem A from the abstract theorem, part 1: the ring `ℤ/p^k`

For a prime `p` and `k ≥ 1`, every `x ≠ 0` in `ℤ/p^k` is `p^j u` with `j < k` and `u` prime to
`p`. This file defines

* `locV p k x`: the exponent `j` (and `k` for `x = 0`);
* `locR p k x`: the residue of `u` modulo `p`;
* `locT p k t = p^(k-1) t` for `t ∈ ℤ/p`: a bijection from `ℤ/p` to the kernel of
  multiplication by `p`,

and proves how they behave under multiplication by `p` (`loc_p_mul`) and by an integer prime to
`p` (`loc_natCast_mul`), what the fibres of multiplication by `p` are (`sum_fiber_p_mul`), and
how many `x` have a given exponent and a residue with a given property (`card_locV_locR`).
-/

open scoped BigOperators

namespace PiFormula

namespace Erdos

namespace Arith

/-- The exponent of `p` in `x ∈ ℤ/p^k` (and `k` for `x = 0`). -/
noncomputable def locV (p k : ℕ) (x : ZMod (p ^ k)) : ℕ :=
  if x = 0 then k else multiplicity p x.val

/-- The residue modulo `p` of `x / p^j`, where `j` is the exponent of `p` in `x`. -/
noncomputable def locR (p k : ℕ) (x : ZMod (p ^ k)) : ZMod p :=
  ((x.val / p ^ multiplicity p x.val : ℕ) : ZMod p)

/-- `t ↦ p^(k-1) t`, from `ℤ/p` to `ℤ/p^k`. -/
def locT (p k : ℕ) (t : ZMod p) : ZMod (p ^ k) := ((p ^ (k - 1) * t.val : ℕ) : ZMod (p ^ k))

variable {p k : ℕ} [hp : Fact p.Prime]

omit hp in
theorem locV_zero : locV p k 0 = k := by simp [locV]

/-- The exponent and the residue can be read off any representative. -/
theorem loc_rep {a j : ℕ} (hj : j < k) (h1 : p ^ j ∣ a) (h2 : ¬ p ^ (j + 1) ∣ a) :
    (a : ZMod (p ^ k)) ≠ 0 ∧ locV p k (a : ZMod (p ^ k)) = j ∧
      locR p k (a : ZMod (p ^ k)) = ((a / p ^ j : ℕ) : ZMod p) := by
  have hp0 : 0 < p := hp.out.pos
  obtain ⟨b, rfl⟩ := h1
  have hb : ¬ p ∣ b := by
    intro h
    apply h2
    rw [pow_succ]
    exact mul_dvd_mul_left _ h
  have hk : p ^ k = p ^ j * p ^ (k - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hval : ((p ^ j * b : ℕ) : ZMod (p ^ k)).val = p ^ j * (b % p ^ (k - j)) := by
    rw [ZMod.val_natCast, hk, Nat.mul_mod_mul_left]
  have hmod : b % p ^ (k - j) % p = b % p :=
    Nat.mod_mod_of_dvd b (dvd_pow_self p (by omega))
  have hb' : ¬ p ∣ b % p ^ (k - j) := by
    intro h
    apply hb
    rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
    rw [← hmod, h]
  have hm : multiplicity p (p ^ j * (b % p ^ (k - j))) = j := by
    refine multiplicity_eq_of_dvd_of_not_dvd (dvd_mul_right _ _) ?_
    intro h
    apply hb'
    rw [pow_succ] at h
    exact (Nat.mul_dvd_mul_iff_left (pow_pos hp0 j)).1 h
  have hne : ((p ^ j * b : ℕ) : ZMod (p ^ k)) ≠ 0 := by
    intro h
    rw [h, ZMod.val_zero] at hval
    apply hb'
    have h0 : b % p ^ (k - j) = 0 := by
      rcases Nat.mul_eq_zero.1 hval.symm with h | h
      · exact absurd h (pow_pos hp0 j).ne'
      · exact h
    rw [h0]
    exact dvd_zero p
  refine ⟨hne, ?_, ?_⟩
  · have e : locV p k ((p ^ j * b : ℕ) : ZMod (p ^ k)) =
        multiplicity p ((p ^ j * b : ℕ) : ZMod (p ^ k)).val := by
      unfold locV
      split_ifs with h0
      · exact absurd h0 hne
      · rfl
    rw [e, hval, hm]
  · rw [locR, hval, hm, Nat.mul_div_cancel_left _ (pow_pos hp0 j),
      Nat.mul_div_cancel_left _ (pow_pos hp0 j), ZMod.natCast_eq_natCast_iff', hmod]

/-- Every non-zero element has a representative in standard form. -/
theorem loc_std {x : ZMod (p ^ k)} (hx : x ≠ 0) :
    ∃ a j : ℕ, j < k ∧ p ^ j ∣ a ∧ ¬ p ^ (j + 1) ∣ a ∧ (a : ZMod (p ^ k)) = x := by
  have hv : x.val ≠ 0 := by
    intro h
    exact hx ((ZMod.val_eq_zero x).1 h)
  have hd : p ^ multiplicity p x.val ∣ x.val := pow_multiplicity_dvd p x.val
  refine ⟨x.val, multiplicity p x.val, ?_, hd, pow_succ_multiplicity_not_dvd hv,
    ZMod.natCast_zmod_val x⟩
  have h1 : p ^ multiplicity p x.val ≤ x.val := Nat.le_of_dvd (Nat.pos_of_ne_zero hv) hd
  have h2 : x.val < p ^ k := ZMod.val_lt x
  exact (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 (lt_of_le_of_lt h1 h2)

theorem locV_lt {x : ZMod (p ^ k)} (hx : x ≠ 0) : locV p k x < k := by
  obtain ⟨a, j, hj, h1, h2, rfl⟩ := loc_std hx
  rw [(loc_rep hj h1 h2).2.1]
  exact hj

theorem locV_eq_iff {x : ZMod (p ^ k)} : locV p k x = k ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact absurd h (locV_lt hx).ne
  · rintro rfl
    exact locV_zero

theorem locR_ne_zero {x : ZMod (p ^ k)} (hx : x ≠ 0) : locR p k x ≠ 0 := by
  obtain ⟨a, j, hj, h1, h2, rfl⟩ := loc_std hx
  rw [(loc_rep hj h1 h2).2.2]
  intro h
  apply h2
  rw [ZMod.natCast_eq_zero_iff] at h
  obtain ⟨b, rfl⟩ := h1
  rw [Nat.mul_div_cancel_left _ (pow_pos hp.out.pos j)] at h
  rw [pow_succ]
  exact mul_dvd_mul_left _ h

/-- Multiplication by an integer prime to `p`. -/
theorem loc_natCast_mul {c : ℕ} (hc : ¬ p ∣ c) {x : ZMod (p ^ k)} (hx : x ≠ 0) :
    (c : ZMod (p ^ k)) * x ≠ 0 ∧ locV p k ((c : ZMod (p ^ k)) * x) = locV p k x ∧
      locR p k ((c : ZMod (p ^ k)) * x) = (c : ZMod p) * locR p k x := by
  obtain ⟨a, j, hj, h1, h2, rfl⟩ := loc_std hx
  have hcop : Nat.Coprime (p ^ (j + 1)) c :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hc)
  have h2' : ¬ p ^ (j + 1) ∣ c * a := fun h => h2 (hcop.dvd_of_dvd_mul_left h)
  have h := loc_rep (k := k) hj (Dvd.dvd.mul_left h1 c) h2'
  have h' := loc_rep (k := k) hj h1 h2
  rw [Nat.cast_mul] at h
  refine ⟨h.1, ?_, ?_⟩
  · rw [h.2.1, h'.2.1]
  · rw [h.2.2, h'.2.2, Nat.mul_div_assoc c h1, Nat.cast_mul]

/-- Multiplication by `p`, when the product is not zero. -/
theorem loc_p_mul {x : ZMod (p ^ k)} (h : (p : ZMod (p ^ k)) * x ≠ 0) :
    x ≠ 0 ∧ locV p k ((p : ZMod (p ^ k)) * x) = locV p k x + 1 ∧
      locR p k ((p : ZMod (p ^ k)) * x) = locR p k x := by
  have hx : x ≠ 0 := by
    rintro rfl
    exact h (mul_zero _)
  refine ⟨hx, ?_⟩
  obtain ⟨a, j, hj, h1, h2, rfl⟩ := loc_std hx
  rw [← Nat.cast_mul] at h ⊢
  have hj' : j + 1 < k := by
    by_contra hcon
    apply h
    rw [ZMod.natCast_eq_zero_iff]
    refine (pow_dvd_pow p (by omega : k ≤ j + 1)).trans ?_
    rw [pow_succ']
    exact mul_dvd_mul_left p h1
  have h1' : p ^ (j + 1) ∣ p * a := by
    rw [pow_succ']
    exact mul_dvd_mul_left p h1
  have h2' : ¬ p ^ (j + 1 + 1) ∣ p * a := by
    intro hd
    apply h2
    rw [pow_succ'] at hd
    exact (Nat.mul_dvd_mul_iff_left hp.out.pos).1 hd
  have e := loc_rep (k := k) hj' h1' h2'
  have e' := loc_rep (k := k) hj h1 h2
  refine ⟨?_, ?_⟩
  · rw [e.2.1, e'.2.1]
  · rw [e.2.2, e'.2.2, pow_succ', Nat.mul_div_mul_left _ _ hp.out.pos]

/-- A non-zero element with positive exponent is a multiple of `p`. -/
theorem exists_p_mul_of_locV {x : ZMod (p ^ k)} (h : locV p k x ≠ 0) :
    ∃ x₀ : ZMod (p ^ k), x = (p : ZMod (p ^ k)) * x₀ := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, mul_zero]⟩
  · obtain ⟨a, j, hj, h1, h2, rfl⟩ := loc_std hx
    rw [(loc_rep hj h1 h2).2.1] at h
    have hpa : p ∣ a := (dvd_pow_self p h).trans h1
    obtain ⟨b, rfl⟩ := hpa
    exact ⟨(b : ZMod (p ^ k)), by rw [Nat.cast_mul]⟩

/-! ### The kernel of multiplication by `p` -/

omit hp in
theorem locT_zero : locT p k 0 = 0 := by
  simp [locT]

omit hp in
theorem p_mul_locT (hk : k ≠ 0) (t : ZMod p) : (p : ZMod (p ^ k)) * locT p k t = 0 := by
  rw [locT, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ← mul_assoc, ← pow_succ']
  have e : k - 1 + 1 = k := by omega
  rw [e]
  exact dvd_mul_right _ _

theorem loc_locT (hk : k ≠ 0) {t : ZMod p} (ht : t ≠ 0) :
    locT p k t ≠ 0 ∧ locV p k (locT p k t) = k - 1 ∧ locR p k (locT p k t) = t := by
  have h2 : ¬ p ^ (k - 1 + 1) ∣ p ^ (k - 1) * t.val := by
    intro h
    rw [pow_succ] at h
    have h3 : p ∣ t.val := (Nat.mul_dvd_mul_iff_left (pow_pos hp.out.pos _)).1 h
    have h4 : t.val < p := ZMod.val_lt t
    have h5 : t.val = 0 := Nat.eq_zero_of_dvd_of_lt h3 h4
    exact ht ((ZMod.val_eq_zero t).1 h5)
  have e := loc_rep (k := k) (by omega : k - 1 < k) (dvd_mul_right (p ^ (k - 1)) t.val) h2
  refine ⟨e.1, e.2.1, ?_⟩
  rw [locT, e.2.2, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos _), ZMod.natCast_zmod_val]

theorem locT_injective (hk : k ≠ 0) : Function.Injective (locT p k) := by
  intro t t' h
  have hpk : p ^ k = p ^ (k - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have hlt : ∀ t : ZMod p, p ^ (k - 1) * t.val < p ^ k := by
    intro t
    rw [hpk]
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt t) (pow_pos hp.out.pos _)
  unfold locT at h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt t), Nat.mod_eq_of_lt (hlt t')] at h
  exact ZMod.val_injective p (Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos _) h)

theorem exists_locT (hk : k ≠ 0) {x : ZMod (p ^ k)} (h : (p : ZMod (p ^ k)) * x = 0) :
    ∃ t : ZMod p, locT p k t = x := by
  have hpk : p ^ k = p * p ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h0 : p ^ k ∣ p * x.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val]
    exact h
  have h1 : p * p ^ (k - 1) ∣ p * x.val := (dvd_of_eq hpk.symm).trans h0
  obtain ⟨m, hm⟩ := (Nat.mul_dvd_mul_iff_left hp.out.pos).1 h1
  have hlt : m < p := by
    have h2 : x.val < p ^ k := ZMod.val_lt x
    have h3 : p ^ (k - 1) * m < p ^ (k - 1) * p := by
      rw [← hm, mul_comm (p ^ (k - 1)) p, ← hpk]
      exact h2
    exact lt_of_mul_lt_mul_left h3 (Nat.zero_le _)
  refine ⟨(m : ZMod p), ?_⟩
  rw [locT, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ← hm, ZMod.natCast_zmod_val]

/-- The fibres of multiplication by `p`. -/
theorem sum_fiber_p_mul (hk : k ≠ 0) {M : Type*} [AddCommMonoid M] (F : ZMod (p ^ k) → M)
    (x₀ : ZMod (p ^ k)) :
    ∑ x ∈ Finset.univ.filter (fun x : ZMod (p ^ k) => (p : ZMod (p ^ k)) * x =
      (p : ZMod (p ^ k)) * x₀), F x = ∑ t : ZMod p, F (x₀ + locT p k t) := by
  have himg : Finset.univ.filter (fun x : ZMod (p ^ k) => (p : ZMod (p ^ k)) * x =
      (p : ZMod (p ^ k)) * x₀) = Finset.univ.image (fun t : ZMod p => x₀ + locT p k t) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      have h0 : (p : ZMod (p ^ k)) * (x - x₀) = 0 := by rw [mul_sub, h, sub_self]
      obtain ⟨t, ht⟩ := exists_locT hk h0
      exact ⟨t, by rw [ht]; ring⟩
    · rintro ⟨t, rfl⟩
      rw [mul_add, p_mul_locT hk, add_zero]
  rw [himg, Finset.sum_image]
  intro t _ t' _ h
  exact locT_injective hk (add_left_cancel h)

theorem card_fiber_p_mul (hk : k ≠ 0) (x₀ : ZMod (p ^ k)) :
    (Finset.univ.filter (fun x : ZMod (p ^ k) => (p : ZMod (p ^ k)) * x =
      (p : ZMod (p ^ k)) * x₀)).card = p := by
  rw [Finset.card_eq_sum_ones, sum_fiber_p_mul hk (fun _ => 1) x₀]
  simp [ZMod.card]

/-! ### Counting -/

theorem card_locV_eq :
    (Finset.univ.filter (fun x : ZMod (p ^ k) => locV p k x = k)).card = 1 := by
  have h : Finset.univ.filter (fun x : ZMod (p ^ k) => locV p k x = k) = {0} := by
    ext x
    simp [locV_eq_iff]
  rw [h, Finset.card_singleton]

/-- The number of `x` with exponent `j < k` whose residue has the property `P`. -/
theorem card_locV_locR (hk : k ≠ 0) (P : ZMod p → Prop) [DecidablePred P] :
    ∀ (d j : ℕ), j + d + 1 = k →
      (Finset.univ.filter (fun x : ZMod (p ^ k) => locV p k x = j ∧ P (locR p k x))).card =
        p ^ d * (Finset.univ.filter (fun t : ZMod p => t ≠ 0 ∧ P t)).card := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hjk : j = k - 1 := by omega
    have himg : Finset.univ.filter (fun x : ZMod (p ^ k) => locV p k x = j ∧ P (locR p k x)) =
        (Finset.univ.filter (fun t : ZMod p => t ≠ 0 ∧ P t)).image (locT p k) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨h1, h2⟩
        have hx : x ≠ 0 := by
          rintro rfl
          rw [locV_zero] at h1
          omega
        have hpx : (p : ZMod (p ^ k)) * x = 0 := by
          by_contra hne
          have h3 := (loc_p_mul hne).2.1
          have h4 := locV_lt hne
          omega
        obtain ⟨t, rfl⟩ := exists_locT hk hpx
        have ht : t ≠ 0 := by
          rintro rfl
          exact hx locT_zero
        rw [(loc_locT hk ht).2.2] at h2
        exact ⟨t, ⟨ht, h2⟩, rfl⟩
      · rintro ⟨t, ⟨ht, h2⟩, rfl⟩
        rw [(loc_locT hk ht).2.1, (loc_locT hk ht).2.2]
        exact ⟨hjk.symm, h2⟩
    rw [himg, Finset.card_image_of_injective _ (locT_injective hk), pow_zero, one_mul]
  | succ d ih =>
    intro j hj
    have hmaps : Set.MapsTo (fun x : ZMod (p ^ k) => (p : ZMod (p ^ k)) * x)
        ↑(Finset.univ.filter (fun x : ZMod (p ^ k) => locV p k x = j ∧ P (locR p k x)))
        ↑(Finset.univ.filter (fun x : ZMod (p ^ k) => locV p k x = j + 1 ∧ P (locR p k x))) := by
      intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [locV_zero] at hx
        omega
      have hne : (p : ZMod (p ^ k)) * x ≠ 0 := by
        intro h0
        obtain ⟨t, rfl⟩ := exists_locT hk h0
        have ht : t ≠ 0 := by
          rintro rfl
          exact hx0 locT_zero
        rw [(loc_locT hk ht).2.1] at hx
        omega
      rw [(loc_p_mul hne).2.1, (loc_p_mul hne).2.2]
      exact ⟨by rw [hx.1], hx.2⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfib : ∀ y ∈ Finset.univ.filter
        (fun x : ZMod (p ^ k) => locV p k x = j + 1 ∧ P (locR p k x)),
        ((Finset.univ.filter (fun x : ZMod (p ^ k) => locV p k x = j ∧ P (locR p k x))).filter
          (fun x => (p : ZMod (p ^ k)) * x = y)).card = p := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨x₀, rfl⟩ := exists_p_mul_of_locV (x := y) (by rw [hy.1]; omega)
      have hy0 : (p : ZMod (p ^ k)) * x₀ ≠ 0 := by
        intro h0
        rw [h0, locV_zero] at hy
        omega
      refine Eq.trans ?_ (card_fiber_p_mul hk x₀)
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        have hne : (p : ZMod (p ^ k)) * x ≠ 0 := by rw [h]; exact hy0
        have e1 := (loc_p_mul hne).2.1
        have e2 := (loc_p_mul hne).2.2
        rw [h] at e1 e2
        refine ⟨by omega, ?_⟩
        rw [← e2]
        exact hy.2
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, ih (j + 1) (by omega)]
    ring

end Arith

end Erdos

end PiFormula
