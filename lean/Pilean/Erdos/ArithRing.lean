import Pilean.Erdos.AbstractDefs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Theorem A from the abstract theorem, part 5: identities in the group ring `ℚ[S]`

`S = ∏_p ℤ/2^(s p)` (`Grp s`). Facts about the norm elements `normElt s n` (coefficients,
`N_n = ∏_{p ∈ n} N_p`, `[z] N_n = N_n` for `z ∈ S_n`), about `ε` (`aug`), and the arithmetic of
`ℤ_(2)` (`IsZ2`) that the proof of Lemma 1 needs.

(Some of these statements are also proved, for a general coefficient ring, in
`AbstractGroupRing.lean`; they are repeated here so that the two parts of the proof of Theorem A
do not depend on each other.)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open scoped BigOperators

open AddMonoidAlgebra (single)

namespace PiFormula

namespace Erdos

namespace Arith

variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ι → ℕ}

/-! ### Coefficients -/

theorem ext_coeff {x y : GRing s} (h : ∀ g, x.coeff g = y.coeff g) : x = y :=
  AddMonoidAlgebra.ext (Finsupp.ext h)

theorem coeff_finset_sum {κ : Type*} (t : Finset κ) (F : κ → GRing s) (g : Grp s) :
    (∑ i ∈ t, F i).coeff g = ∑ i ∈ t, (F i).coeff g := by
  rw [AddMonoidAlgebra.coeff_sum, Finset.sum_apply']

theorem coeff_single_apply (x g : Grp s) (a : ℚ) :
    (single x a : GRing s).coeff g = if x = g then a else 0 := by
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem coeff_sum_single (f : Grp s → ℚ) (g : Grp s) :
    (∑ x : Grp s, single x (f x)).coeff g = f g := by
  rw [coeff_finset_sum]
  simp only [coeff_single_apply]
  rw [Finset.sum_eq_single g]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ g) h

theorem coeff_normElt (n : Finset ι) (g : Grp s) :
    (normElt s n).coeff g = if InSub n g then 1 else 0 := by
  have h : normElt s n = ∑ x : Grp s, single x (if InSub n x then (1 : ℚ) else 0) := by
    unfold normElt
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [h, coeff_sum_single]

theorem coeff_smul' (c : ℚ) (y : GRing s) (g : Grp s) : (c • y).coeff g = c * y.coeff g := rfl

theorem smul_eq_single_mul (c : ℚ) (y : GRing s) : c • y = single 0 c * y := by
  refine ext_coeff fun g => ?_
  rw [AddMonoidAlgebra.coeff_single_zero_mul]
  rfl

theorem single_zero_mul_cancel {c : ℚ} (hc : c ≠ 0) {y : GRing s}
    (h : single (0 : Grp s) c * y = 0) : y = 0 := by
  refine ext_coeff fun g => ?_
  have h1 := congrArg (fun z : GRing s => z.coeff g) h
  simp only [AddMonoidAlgebra.coeff_single_zero_mul] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd h2 hc
  · rw [h2]
    rfl

/-! ### Norm elements -/

theorem single_mul_normElt {n : Finset ι} {z : Grp s} (hz : InSub n z) :
    single z (1 : ℚ) * normElt s n = normElt s n := by
  refine ext_coeff fun g => ?_
  rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, coeff_normElt, coeff_normElt]
  have h : InSub n (-z + g) ↔ InSub n g := by
    constructor
    · intro h p hp
      have h1 := h p hp
      have h2 := hz p hp
      simp only [Pi.add_apply, Pi.neg_apply, h2, neg_zero, zero_add] at h1
      exact h1
    · intro h p hp
      simp only [Pi.add_apply, Pi.neg_apply, hz p hp, h p hp, neg_zero, zero_add]
  simp only [h]

theorem normElt_singleton (p : ι) :
    normElt s {p} = ∑ c : ZMod (2 ^ s p), single (Pi.single p c : Grp s) (1 : ℚ) := by
  refine ext_coeff fun g => ?_
  rw [coeff_normElt, coeff_finset_sum]
  simp only [coeff_single_apply]
  have key : ∀ c : ZMod (2 ^ s p), (Pi.single p c : Grp s) = g ↔ (c = g p ∧ InSub {p} g) := by
    intro c
    constructor
    · rintro rfl
      refine ⟨by simp, fun r hr => ?_⟩
      have hrp : r ≠ p := fun e => hr (e ▸ Finset.mem_singleton_self p)
      simp [Pi.single_eq_of_ne hrp]
    · rintro ⟨rfl, h⟩
      ext r
      by_cases hrp : r = p
      · subst hrp
        simp
      · rw [Pi.single_eq_of_ne hrp, h r (by simpa using hrp)]
  simp only [key]
  by_cases hg : InSub {p} g
  · simp [hg]
  · simp [hg]

theorem coeff_normElt_singleton_mul (p : ι) (x : GRing s) (g : Grp s) :
    (normElt s {p} * x).coeff g = ∑ c : ZMod (2 ^ s p), x.coeff (-(Pi.single p c) + g) := by
  rw [normElt_singleton, Finset.sum_mul, coeff_finset_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul]

/-- `N_n` is the product of the `N_p`, `p ∈ n`. -/
theorem normElt_eq_prod (n : Finset ι) : normElt s n = ∏ p ∈ n, normElt s {p} := by
  induction n using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    refine ext_coeff fun g => ?_
    rw [coeff_normElt, AddMonoidAlgebra.one_def, coeff_single_apply]
    have h : InSub (∅ : Finset ι) g ↔ 0 = g := by
      constructor
      · intro h
        ext p
        exact (h p (Finset.notMem_empty p)).symm
      · rintro rfl p _
        rfl
    simp only [h]
  | insert p n hp ih =>
    rw [Finset.prod_insert hp, ← ih]
    refine ext_coeff fun g => ?_
    rw [coeff_normElt_singleton_mul, coeff_normElt]
    simp only [coeff_normElt]
    have key : ∀ c : ZMod (2 ^ s p),
        InSub n (-(Pi.single p c : Grp s) + g) ↔ (g p = c ∧ InSub (insert p n) g) := by
      intro c
      constructor
      · intro h
        have h1 : g p = c := by
          have := h p hp
          simp only [Pi.add_apply, Pi.neg_apply, Pi.single_eq_same] at this
          linear_combination this
        refine ⟨h1, fun r hr => ?_⟩
        have hrp : r ≠ p := fun e => hr (e ▸ Finset.mem_insert_self p n)
        have hrn : r ∉ n := fun e => hr (Finset.mem_insert_of_mem e)
        have := h r hrn
        simpa [Pi.single_eq_of_ne hrp] using this
      · rintro ⟨h1, h2⟩ r hr
        by_cases hrp : r = p
        · subst hrp
          simp [h1]
        · have := h2 r (fun e => (Finset.mem_insert.1 e).elim hrp hr)
          simp [Pi.single_eq_of_ne hrp, this]
    simp only [key]
    by_cases hg : InSub (insert p n) g
    · simp [hg]
    · simp [hg]

/-! ### The augmentation -/

theorem aug_zero : aug (0 : GRing s) = 0 := by simp [aug]

theorem aug_add (x y : GRing s) : aug (x + y) = aug x + aug y := by
  simp [aug, Finset.sum_add_distrib]

theorem aug_single (g : Grp s) (r : ℚ) : aug (single g r) = r := by
  simp [aug, Finsupp.single_apply]

theorem aug_smul (c : ℚ) (x : GRing s) : aug (c • x) = c * aug x := by
  unfold aug
  rw [Finset.mul_sum]
  rfl

theorem aug_sum {κ : Type*} (t : Finset κ) (F : κ → GRing s) :
    aug (∑ i ∈ t, F i) = ∑ i ∈ t, aug (F i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [aug_zero]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, aug_add, ih]

/-! ### Arithmetic of `ℤ_(2)` -/

theorem isZ2_zero : IsZ2 0 := by simp [IsZ2]

theorem isZ2_intCast (n : ℤ) : IsZ2 (n : ℚ) := by simp [IsZ2]

theorem isZ2_natCast (n : ℕ) : IsZ2 (n : ℚ) := by simp [IsZ2]

theorem isZ2_add {a b : ℚ} (ha : IsZ2 a) (hb : IsZ2 b) : IsZ2 (a + b) :=
  Odd.of_dvd_nat (Odd.mul ha hb) (Rat.add_den_dvd a b)

theorem isZ2_mul {a b : ℚ} (ha : IsZ2 a) (hb : IsZ2 b) : IsZ2 (a * b) :=
  Odd.of_dvd_nat (Odd.mul ha hb) (Rat.mul_den_dvd a b)

theorem isZ2_neg {a : ℚ} (ha : IsZ2 a) : IsZ2 (-a) := by
  unfold IsZ2 at *
  rwa [Rat.neg_den]

theorem isZ2_sub {a b : ℚ} (ha : IsZ2 a) (hb : IsZ2 b) : IsZ2 (a - b) := by
  rw [sub_eq_add_neg]
  exact isZ2_add ha (isZ2_neg hb)

theorem isZ2_sum {κ : Type*} (t : Finset κ) (f : κ → ℚ) (h : ∀ i ∈ t, IsZ2 (f i)) :
    IsZ2 (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isZ2_zero
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact isZ2_add (h i (Finset.mem_insert_self i t))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The inverse of an odd natural number lies in `ℤ_(2)`. -/
theorem isZ2_inv_natCast {n : ℕ} (hn : Odd n) : IsZ2 ((n : ℚ)⁻¹) := by
  have hpos : 0 < n := hn.pos
  unfold IsZ2
  rw [Rat.inv_natCast_den_of_pos hpos]
  exact hn

/-- `x ∈ 2 ℤ_(2)`. -/
def Even2 (x : ℚ) : Prop := ∃ z : ℚ, IsZ2 z ∧ x = 2 * z

theorem even2_zero : Even2 0 := ⟨0, isZ2_zero, by ring⟩

theorem even2_add {a b : ℚ} (ha : Even2 a) (hb : Even2 b) : Even2 (a + b) := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact ⟨x + y, isZ2_add hx hy, by ring⟩

theorem even2_sub {a b : ℚ} (ha : Even2 a) (hb : Even2 b) : Even2 (a - b) := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact ⟨x - y, isZ2_sub hx hy, by ring⟩

theorem even2_mul_left {c a : ℚ} (hc : IsZ2 c) (ha : Even2 a) : Even2 (c * a) := by
  obtain ⟨x, hx, rfl⟩ := ha
  exact ⟨c * x, isZ2_mul hc hx, by ring⟩

theorem even2_sum {κ : Type*} (t : Finset κ) (f : κ → ℚ) (h : ∀ i ∈ t, Even2 (f i)) :
    Even2 (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using even2_zero
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact even2_add (h i (Finset.mem_insert_self i t))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The difference of two integers of the same parity lies in `2 ℤ_(2)`. -/
theorem even2_intCast_sub {a b : ℤ} (h : Even (a - b)) : Even2 ((a : ℚ) - (b : ℚ)) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨(m : ℚ), isZ2_intCast m, ?_⟩
  have : ((a - b : ℤ) : ℚ) = ((m + m : ℤ) : ℚ) := by rw [hm]
  push_cast at this
  linear_combination this

/-- An odd rational number is `1` modulo `2 ℤ_(2)`. -/
theorem even2_sub_one {x : ℚ} (hx : IsOddRat x) : Even2 (x - 1) := by
  obtain ⟨h1, h2⟩ := hx
  have hev : Even (x.num - (x.den : ℤ)) := by
    have h2' : Odd (x.den : ℤ) := by exact_mod_cast h2
    exact Odd.sub_odd h1 h2'
  have hden : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 x.den_nz
  have e : x - 1 = (x.den : ℚ)⁻¹ * ((x.num : ℚ) - (x.den : ℚ)) := by
    rw [← Rat.mul_den_eq_num x, mul_sub, ← mul_assoc, mul_comm _ x, mul_assoc,
      inv_mul_cancel₀ hden, mul_one]
  rw [e]
  exact even2_mul_left (isZ2_inv_natCast h2) (even2_intCast_sub hev)

end Arith

end Erdos

end PiFormula
