/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.AbstractDefs
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# The algebraic core of Theorem A, part 2: identities in the group ring `R[S]`

`S = ∏_p ℤ/2^(s p)` (`Grp s`), `R` a commutative ring. Elements of `R[S]`:

* `nrm R s p`: the sum of the elements of the factor `C_p` (the paper's `N_p`);
* `del R s p = 1 - t_p`, where `t_p` is the generator of `C_p`;
* `aR R s π u p = π p - [u p]` (for `R = ℚ` this is `aElt π u p`);
* `nrmSet R s n`: the sum of the elements of `S_n` (for `R = ℚ` this is `normElt s n`); it is the
  product of the `nrm R s p`, `p ∈ n` (`nrmSet_eq_prod`).

For `R = ℚ`: `aug` is a ring homomorphism (`augHom`), `x * N_S = ε(x) N_S`
(`mul_normElt_univ`), and the elements with coefficients in `ℤ_(2)` are closed under the ring
operations and contain the image of `ℤ[S]` (`toQ`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open scoped BigOperators

open AddMonoidAlgebra (single)

namespace PiFormula

namespace Erdos

namespace Abs

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Any coefficient ring -/

section Generic

variable (R : Type*) [CommRing R] (s : ι → ℕ)

/-- The group ring `R[S]`. -/
abbrev GR : Type _ := AddMonoidAlgebra R (Grp s)

/-- `N_p`: the sum of the elements of the factor `C_p`. -/
noncomputable def nrm (p : ι) : GR R s :=
  ∑ c : ZMod (2 ^ s p), single (Pi.single p c : Grp s) (1 : R)

/-- `1 - t_p`. -/
noncomputable def del (p : ι) : GR R s := 1 - single (Pi.single p 1 : Grp s) (1 : R)

/-- `π p - [u p]`. -/
noncomputable def aR (π : ι → ℤ) (u : ι → Grp s) (p : ι) : GR R s :=
  single (0 : Grp s) (π p : R) - single (u p) (1 : R)

/-- The sum of the elements of `S_n`. -/
noncomputable def nrmSet (n : Finset ι) : GR R s :=
  ∑ x : Grp s, if InSub n x then single x (1 : R) else 0

variable {R s}

theorem ext_coeff {x y : GR R s} (h : ∀ g, x.coeff g = y.coeff g) : x = y :=
  AddMonoidAlgebra.ext (Finsupp.ext h)

theorem coeff_sum_single (f : Grp s → R) (g : Grp s) :
    (∑ x : Grp s, single x (f x)).coeff g = f g := by
  rw [AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp only [AddMonoidAlgebra.coeff_single]
  rw [Finset.sum_eq_single g]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ g) h

theorem coeff_nrmSet (n : Finset ι) (g : Grp s) :
    (nrmSet R s n).coeff g = if InSub n g then 1 else 0 := by
  have h : nrmSet R s n = ∑ x : Grp s, single x (if InSub n x then (1 : R) else 0) := by
    unfold nrmSet
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [h, coeff_sum_single]

variable (R s)

theorem single_mul_nrm (p : ι) (c : ZMod (2 ^ s p)) :
    single (Pi.single p c : Grp s) (1 : R) * nrm R s p = nrm R s p := by
  unfold nrm
  rw [Finset.mul_sum]
  simp only [AddMonoidAlgebra.single_mul_single, mul_one, ← Pi.single_add]
  exact Fintype.sum_equiv (Equiv.addLeft c) _ _ (fun x => rfl)

theorem del_mul_nrm (p : ι) : del R s p * nrm R s p = 0 := by
  unfold del
  rw [sub_mul, one_mul, single_mul_nrm, sub_self]

theorem nrm_mul_nrm (p : ι) : nrm R s p * nrm R s p = (2 : GR R s) ^ s p * nrm R s p := by
  have h : nrm R s p * nrm R s p =
      ∑ c : ZMod (2 ^ s p), single (Pi.single p c : Grp s) (1 : R) * nrm R s p := by
    rw [← Finset.sum_mul]
    rfl
  rw [h]
  simp only [single_mul_nrm]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  push_cast
  rfl

theorem single_natCast (p : ι) (j : ℕ) :
    single (Pi.single p (j : ZMod (2 ^ s p)) : Grp s) (1 : R) =
      single (Pi.single p 1 : Grp s) (1 : R) ^ j := by
  rw [AddMonoidAlgebra.single_pow, one_pow]
  congr 1
  ext q
  by_cases h : q = p
  · subst h
    simp
  · simp [h]

theorem exists_single_sub_one (p : ι) (c : ZMod (2 ^ s p)) :
    ∃ h : GR R s, single (Pi.single p c : Grp s) (1 : R) - 1 = del R s p * h := by
  refine ⟨-∑ i ∈ Finset.range c.val, single (Pi.single p 1 : Grp s) (1 : R) ^ i, ?_⟩
  rw [mul_neg, del, mul_neg_geom_sum, ← single_natCast, ZMod.natCast_zmod_val]
  ring

/-- If `(1 - t_p) y = 0` then `N_p y = 2^(s p) y`. -/
theorem nrm_mul_of_del_mul {p : ι} {y : GR R s} (h : del R s p * y = 0) :
    nrm R s p * y = (2 : GR R s) ^ s p * y := by
  have h1 : ∀ c : ZMod (2 ^ s p), single (Pi.single p c : Grp s) (1 : R) * y = y := by
    intro c
    obtain ⟨w, hw⟩ := exists_single_sub_one R s p c
    linear_combination y * hw + w * h
  unfold nrm
  rw [Finset.sum_mul]
  simp only [h1]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  push_cast
  rfl

theorem coeff_nrm_mul (p : ι) (x : GR R s) (g : Grp s) :
    (nrm R s p * x).coeff g = ∑ c : ZMod (2 ^ s p), x.coeff (-(Pi.single p c) + g) := by
  unfold nrm
  rw [Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul]

/-- The sum of the elements of `S_n` is the product of the `N_p`, `p ∈ n`. -/
theorem nrmSet_eq_prod (n : Finset ι) : nrmSet R s n = ∏ p ∈ n, nrm R s p := by
  induction n using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    refine ext_coeff fun g => ?_
    rw [coeff_nrmSet, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
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
    rw [coeff_nrm_mul, coeff_nrmSet]
    simp only [coeff_nrmSet]
    have key : ∀ c : ZMod (2 ^ s p),
        InSub n (-(Pi.single p c : Grp s) + g) ↔ (g p = c ∧ InSub (insert p n) g) := by
      intro c
      constructor
      · intro h
        have h1 : g p = c := by
          have := h p hp
          simp only [Pi.add_apply, Pi.neg_apply, Pi.single_eq_same] at this
          linear_combination this
        refine ⟨h1, fun q hq => ?_⟩
        have hqp : q ≠ p := fun e => hq (e ▸ Finset.mem_insert_self p n)
        have hqn : q ∉ n := fun e => hq (Finset.mem_insert_of_mem e)
        have := h q hqn
        simpa [Pi.single_eq_of_ne hqp] using this
      · rintro ⟨h1, h2⟩ q hq
        by_cases hqp : q = p
        · subst hqp
          simp [h1]
        · have := h2 q (fun e => (Finset.mem_insert.1 e).elim hqp hq)
          simp [Pi.single_eq_of_ne hqp, this]
    simp only [key]
    by_cases hg : InSub (insert p n) g
    · simp [hg]
    · simp [hg]

/-- `a p` divides a non-zero integer. -/
theorem aR_dvd (π : ι → ℤ) (u : ι → Grp s) (p : ι) :
    ∃ b : GR R s, aR R s π u p * b = ((π p ^ Fintype.card (Grp s) - 1 : ℤ) : GR R s) := by
  obtain ⟨b, hb⟩ := sub_dvd_pow_sub_pow (single (0 : Grp s) (π p : R)) (single (u p) (1 : R))
    (Fintype.card (Grp s))
  refine ⟨b, ?_⟩
  rw [aR, ← hb, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_pow, nsmul_zero,
    card_nsmul_eq_zero, one_pow, AddMonoidAlgebra.intCast_def]
  push_cast
  rw [AddMonoidAlgebra.single_sub]

theorem intCast_mul_eq_zero [CharZero R] [NoZeroDivisors R] {k : ℤ} (hk : k ≠ 0) {x : GR R s}
    (h : (k : GR R s) * x = 0) : x = 0 := by
  refine ext_coeff fun g => ?_
  have h1 := congrArg (fun y : GR R s => y.coeff g) h
  simp only [AddMonoidAlgebra.intCast_def, AddMonoidAlgebra.coeff_single_zero_mul] at h1
  have hk' : (k : R) ≠ 0 := Int.cast_ne_zero.2 hk
  simpa [hk'] using h1

/-- `[u] N_m = N_m` modulo `1 - t_{p₀}`, where `m` is the set of all indices except `p₀`. -/
theorem single_mul_prod_nrm (p₀ : ι) (u : Grp s) :
    ∃ w : GR R s, single u (1 : R) * ∏ p ∈ Finset.univ.erase p₀, nrm R s p =
      ∏ p ∈ Finset.univ.erase p₀, nrm R s p + del R s p₀ * w := by
  obtain ⟨h, hh⟩ := exists_single_sub_one R s p₀ (u p₀)
  refine ⟨h * ∏ p ∈ Finset.univ.erase p₀, nrm R s p, ?_⟩
  have hu : u = Pi.single p₀ (u p₀) + ∑ p ∈ Finset.univ.erase p₀, (Pi.single p (u p) : Grp s) :=
    ((Finset.add_sum_erase Finset.univ (fun p => (Pi.single p (u p) : Grp s))
      (Finset.mem_univ p₀)).trans (Finset.univ_sum_single u)).symm
  have h1 : single u (1 : R) = single (Pi.single p₀ (u p₀) : Grp s) (1 : R) *
      ∏ p ∈ Finset.univ.erase p₀, single (Pi.single p (u p) : Grp s) (1 : R) := by
    rw [AddMonoidAlgebra.prod_single, AddMonoidAlgebra.single_mul_single, Finset.prod_const_one,
      mul_one, ← hu]
  have h2 : (∏ p ∈ Finset.univ.erase p₀, single (Pi.single p (u p) : Grp s) (1 : R)) *
      ∏ p ∈ Finset.univ.erase p₀, nrm R s p = ∏ p ∈ Finset.univ.erase p₀, nrm R s p := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => single_mul_nrm R s p (u p)
  rw [h1, mul_assoc, h2]
  linear_combination (∏ p ∈ Finset.univ.erase p₀, nrm R s p) * hh

end Generic

/-! ### Rational coefficients -/

section Rat

variable {s : ι → ℕ}

theorem normElt_eq_prod (n : Finset ι) : normElt s n = ∏ p ∈ n, nrm ℚ s p :=
  nrmSet_eq_prod ℚ s n

theorem smul_eq_single_mul (q : ℚ) (y : GRing s) : q • y = single 0 q * y := by
  refine ext_coeff fun g => ?_
  rw [AddMonoidAlgebra.coeff_single_zero_mul]
  rfl

theorem aug_zero : aug (0 : GRing s) = 0 := by simp [aug]

theorem aug_add (x y : GRing s) : aug (x + y) = aug x + aug y := by
  simp [aug, Finset.sum_add_distrib]

theorem aug_single (g : Grp s) (r : ℚ) : aug (single g r) = r := by
  simp [aug, Finsupp.single_apply]

theorem aug_mul (x y : GRing s) : aug (x * y) = aug x * aug y := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp [aug_zero]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, aug_add, aug_add, h₁, h₂, add_mul]
  | single g a =>
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => simp [aug_zero]
    | add y₁ y₂ h₁ h₂ => rw [mul_add, aug_add, aug_add, h₁, h₂, mul_add]
    | single h b => rw [AddMonoidAlgebra.single_mul_single, aug_single, aug_single, aug_single]

/-- `ε` as a ring homomorphism. -/
noncomputable def augHom (s : ι → ℕ) : GRing s →+* ℚ where
  toFun := aug
  map_one' := by rw [AddMonoidAlgebra.one_def]; exact aug_single _ _
  map_mul' := aug_mul
  map_zero' := aug_zero
  map_add' := aug_add

theorem augHom_apply (y : GRing s) : augHom s y = aug y := rfl

theorem aug_nrm (p : ι) : aug (nrm ℚ s p) = (2 : ℚ) ^ s p := by
  rw [← augHom_apply, nrm, map_sum]
  simp [augHom_apply, aug_single, ZMod.card]

theorem aug_normElt (n : Finset ι) : aug (normElt s n) = ∏ p ∈ n, (2 : ℚ) ^ s p := by
  rw [normElt_eq_prod, ← augHom_apply, map_prod]
  exact Finset.prod_congr rfl fun p _ => aug_nrm p

theorem aug_aElt (π : ι → ℤ) (u : ι → Grp s) (p : ι) : aug (aElt π u p) = (π p : ℚ) - 1 := by
  rw [← augHom_apply, aElt, map_sub, augHom_apply, augHom_apply, aug_single, aug_single]

theorem aug_aProd (π : ι → ℤ) (u : ι → Grp s) (n : Finset ι) :
    aug (aProd π u n) = ∏ p ∈ n, ((π p : ℚ) - 1) := by
  rw [← augHom_apply, aProd, map_prod]
  exact Finset.prod_congr rfl fun p _ => aug_aElt π u p

theorem normElt_univ : normElt s Finset.univ = ∑ g : Grp s, single g (1 : ℚ) := by
  unfold normElt
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : InSub (Finset.univ : Finset ι) x := fun p hp => absurd (Finset.mem_univ p) hp
  simp [h]

/-- `x N_S = ε(x) N_S`. -/
theorem mul_normElt_univ (x : GRing s) :
    x * normElt s Finset.univ = single 0 (aug x) * normElt s Finset.univ := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp [aug_zero]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, aug_add, AddMonoidAlgebra.single_add, add_mul, h₁, h₂]
  | single g a =>
    rw [aug_single, normElt_univ, Finset.mul_sum, Finset.mul_sum]
    simp only [AddMonoidAlgebra.single_mul_single, mul_one, zero_add]
    exact Fintype.sum_equiv (Equiv.addLeft g) _ _ (fun x => rfl)

theorem coeff_normElt_univ (g : Grp s) : (normElt s Finset.univ).coeff g = 1 := by
  rw [normElt_univ, coeff_sum_single]

/-! ### Coefficients in `ℤ_(2)` -/

theorem isZ2_zero : IsZ2 0 := by simp [IsZ2]

theorem isZ2_intCast (n : ℤ) : IsZ2 (n : ℚ) := by simp [IsZ2]

theorem isZ2_add {a b : ℚ} (ha : IsZ2 a) (hb : IsZ2 b) : IsZ2 (a + b) :=
  Odd.of_dvd_nat (Odd.mul ha hb) (Rat.add_den_dvd a b)

theorem isZ2_mul {a b : ℚ} (ha : IsZ2 a) (hb : IsZ2 b) : IsZ2 (a * b) :=
  Odd.of_dvd_nat (Odd.mul ha hb) (Rat.mul_den_dvd a b)

theorem isZ2_neg {a : ℚ} (ha : IsZ2 a) : IsZ2 (-a) := by
  unfold IsZ2 at *
  rwa [Rat.neg_den]

theorem isZ2_sum {κ : Type*} (t : Finset κ) (f : κ → ℚ) (h : ∀ i ∈ t, IsZ2 (f i)) :
    IsZ2 (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isZ2_zero
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact isZ2_add (h i (Finset.mem_insert_self i t))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem integral2_zero : Integral2 (0 : GRing s) := fun _ => by simpa using isZ2_zero

theorem integral2_add {x y : GRing s} (hx : Integral2 x) (hy : Integral2 y) :
    Integral2 (x + y) := fun g => by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact isZ2_add (hx g) (hy g)

theorem integral2_mul {x y : GRing s} (hx : Integral2 x) (hy : Integral2 y) :
    Integral2 (x * y) := fun g => by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  exact isZ2_sum _ _ fun h _ => isZ2_mul (hx h) (hy _)

theorem integral2_sum {κ : Type*} (t : Finset κ) (f : κ → GRing s)
    (h : ∀ i ∈ t, Integral2 (f i)) : Integral2 (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using integral2_zero
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact integral2_add (h i (Finset.mem_insert_self i t))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The ring homomorphism `ℤ[S] → ℚ[S]`. -/
noncomputable def toQ (s : ι → ℕ) : GR ℤ s →+* GRing s :=
  AddMonoidAlgebra.mapRingHom (Grp s) (Int.castRingHom ℚ)

theorem integral2_toQ (x : GR ℤ s) : Integral2 (toQ s x) := fun g => by
  rw [toQ, AddMonoidAlgebra.coeff_mapRingHom]
  exact isZ2_intCast _

theorem toQ_single (g : Grp s) (a : ℤ) : toQ s (single g a) = single g (a : ℚ) := by
  rw [toQ, AddMonoidAlgebra.mapRingHom_single]
  rfl

theorem toQ_nrm (p : ι) : toQ s (nrm ℤ s p) = nrm ℚ s p := by
  rw [nrm, map_sum]
  simp [toQ_single, nrm]

theorem toQ_del (p : ι) : toQ s (del ℤ s p) = del ℚ s p := by
  rw [del, map_sub, map_one, toQ_single]
  simp [del]

theorem toQ_aR (π : ι → ℤ) (u : ι → Grp s) (p : ι) : toQ s (aR ℤ s π u p) = aElt π u p := by
  rw [aR, map_sub, toQ_single, toQ_single]
  simp [aElt]

end Rat

end Abs

end Erdos

end PiFormula
