module

public import Pilean.PiFormula.Rank

/-!
# Part III, Step 1: from Baker's theorem to the 13 relations (milestone M6)

Baker's theorem is not in Mathlib. It is stated here as a proposition `BakerTheorem`, and
every result that uses it carries it as an explicit hypothesis.

**Baker's theorem** (A. Baker, 1966-67; Theorem 2.1 of his *Transcendental Number Theory*):
if `λ_1, ..., λ_n` are logarithms of algebraic numbers and are linearly independent over `ℚ`,
then `1, λ_1, ..., λ_n` are linearly independent over the field of algebraic numbers.

What is proved from it:

* `baker_descent`: for logarithms of algebraic numbers `λ_i` (not assumed independent), a linear
  relation `∑ β_i λ_i = 0` with algebraic coefficients is a combination, with algebraic
  coefficients, of integer relations. The proof is an induction that removes one dependent
  logarithm at a time; no basis is chosen. It works over any field `F` of algebraic numbers:
  coefficients in `F` give a combination with coefficients in `F` (`SpanIn F`). The case
  `F = ℚ(ζ_120)` is what `GaloisValue.lean` conjugates.
* `baker_step1`, **Step 1 of Theorem C**: if `∑_{r ∈ S} d_r Log(1 - r/t) = γ π` with `S` a
  finite set of roots of unity and `d_r`, `γ` algebraic, then `d` vanishes outside the 24 roots
  of `R0`, and on `R0` it is a combination of the 13 relations with algebraic coefficients.
  (An integer relation among the `Log(1 - r/t)` and `iπ` is a multiplicative relation among
  the `1 - r/t`; then `relations_classified` applies.)

The converse needs no Baker (`step1_converse`): every combination of the 13 relations with
algebraic coefficients gives an algebraic multiple of `π`. For this each relation is put in
logarithmic form, `∑ e_j Log w_j ∈ ℚ · iπ` (`log_form`).
-/

@[expose] public section

open Complex

namespace PiFormula

/-! ## 1. Baker's theorem -/

/-- **Baker's theorem** (not proved here; used only as a hypothesis). Let `lam 0, ...,
lam (n-1)` be logarithms of algebraic numbers (that is, each `exp (lam i)` is algebraic), linearly
independent over `ℚ`. Then `1, lam 0, ..., lam (n-1)` are linearly independent over the algebraic
numbers. -/
def BakerTheorem : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℂ),
    (∀ i, IsAlgebraic ℚ (Complex.exp (lam i))) →
    (∀ q : Fin n → ℚ, ∑ i, (q i : ℂ) * lam i = 0 → ∀ i, q i = 0) →
    ∀ (β₀ : ℂ) (β : Fin n → ℂ), IsAlgebraic ℚ β₀ → (∀ i, IsAlgebraic ℚ (β i)) →
      β₀ + ∑ i, β i * lam i = 0 → β₀ = 0 ∧ ∀ i, β i = 0

/-- Baker's theorem (homogeneous part) for a family indexed by a finite set. -/
theorem baker_finset (hB : BakerTheorem) {ι : Type*} (T : Finset ι) (lam : ι → ℂ)
    (hlam : ∀ i ∈ T, IsAlgebraic ℚ (Complex.exp (lam i)))
    (hind : ∀ q : ι → ℚ, ∑ i ∈ T, (q i : ℂ) * lam i = 0 → ∀ i ∈ T, q i = 0)
    (β : ι → ℂ) (hβ : ∀ i ∈ T, IsAlgebraic ℚ (β i)) (h : ∑ i ∈ T, β i * lam i = 0) :
    ∀ i ∈ T, β i = 0 := by
  classical
  let e : Fin T.card ≃ T := T.equivFin.symm
  have hsum : ∀ f : ι → ℂ, ∑ k : Fin T.card, f (e k) = ∑ i ∈ T, f i := fun f =>
    (Equiv.sum_comp e (fun i : T => f i)).trans (Finset.sum_coe_sort T f)
  have hind' : ∀ q : Fin T.card → ℚ, ∑ k, (q k : ℂ) * lam (e k) = 0 → ∀ k, q k = 0 := by
    intro q hq k
    let q' : ι → ℚ := fun i => if hi : i ∈ T then q (e.symm ⟨i, hi⟩) else 0
    have hq' : ∀ k, q' (e k) = q k := by
      intro k
      simp only [q', (e k).2, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply]
    have h0 : ∑ i ∈ T, (q' i : ℂ) * lam i = 0 := by
      rw [← hsum fun i => (q' i : ℂ) * lam i]
      simp only [hq']
      exact hq
    have h1 := hind q' h0 (e k) (e k).2
    rwa [hq'] at h1
  have key := hB T.card (fun k => lam (e k)) (fun k => hlam _ (e k).2) hind' 0
    (fun k => β (e k)) isAlgebraic_zero (fun k => hβ _ (e k).2)
    (by rw [zero_add]; exact (hsum fun i => β i * lam i).trans h)
  intro i hi
  have h1 := key.2 (e.symm ⟨i, hi⟩)
  simpa using h1

/-! ## 2. Descent: algebraic relations come from integer relations -/

/-- The span over a subfield `F` of `ℂ`: `SpanIn F G β` says that `β` is a finite linear
combination of elements of `G` with coefficients in `F`. For `F` the field of algebraic numbers
this is the span over the algebraic numbers. -/
inductive SpanIn {ι : Type*} (F : IntermediateField ℚ ℂ) (G : Set (ι → ℂ)) : (ι → ℂ) → Prop
  | zero : SpanIn F G 0
  | step (c : ℂ) (hc : c ∈ F) (v : ι → ℂ) (hv : v ∈ G) (w : ι → ℂ)
      (hw : SpanIn F G w) : SpanIn F G (fun i => c * v i + w i)

theorem SpanIn.mono {ι : Type*} {F : IntermediateField ℚ ℂ} {G G' : Set (ι → ℂ)} (h : G ⊆ G')
    {β : ι → ℂ} (hβ : SpanIn F G β) : SpanIn F G' β := by
  induction hβ with
  | zero => exact SpanIn.zero
  | step c hc v hv w _ ih => exact SpanIn.step c hc v (h hv) w ih

/-- The integer relations among the numbers `lam i`, `i ∈ T`: integer vectors `z` supported on
`T` with `∑ z_i lam_i = 0`, seen as complex vectors. -/
def IntRel {ι : Type*} (T : Finset ι) (lam : ι → ℂ) : Set (ι → ℂ) :=
  {v | ∃ z : ι → ℤ, (∀ i, i ∉ T → z i = 0) ∧ ∑ i ∈ T, (z i : ℂ) * lam i = 0 ∧ ∀ i, v i = z i}

theorem rat_mul_den (q : ℚ) : q * (q.den : ℚ) = (q.num : ℚ) :=
  ((div_eq_iff (by exact_mod_cast q.den_ne_zero)).1 (Rat.num_div_den q)).symm

/-- A rational relation with a non-zero coefficient gives an integer relation with a non-zero
coefficient at the same place (clear the denominators). -/
theorem exists_int_relation {ι : Type*} (T : Finset ι) (lam : ι → ℂ)
    (q : ι → ℚ) (hq : ∑ i ∈ T, (q i : ℂ) * lam i = 0) {i₀ : ι} (hi₀ : i₀ ∈ T)
    (hne : q i₀ ≠ 0) :
    ∃ z : ι → ℤ, (∀ i, i ∉ T → z i = 0) ∧ ∑ i ∈ T, (z i : ℂ) * lam i = 0 ∧ z i₀ ≠ 0 := by
  classical
  let D : ℤ := ∏ j ∈ T, ((q j).den : ℤ)
  let z : ι → ℤ := fun i =>
    if i ∈ T then (q i).num * ∏ j ∈ T.erase i, ((q j).den : ℤ) else 0
  have hz : ∀ i ∈ T, (z i : ℚ) = q i * D := by
    intro i hi
    simp only [z, hi, ↓reduceIte, D]
    push_cast
    rw [← Finset.mul_prod_erase T (fun j => ((q j).den : ℚ)) hi, ← mul_assoc, rat_mul_den]
  have hzC : ∀ i ∈ T, (z i : ℂ) = (q i : ℂ) * (D : ℂ) := by
    intro i hi
    have h1 : ((z i : ℚ) : ℂ) = ((q i * D : ℚ) : ℂ) := by rw [hz i hi]
    push_cast at h1
    exact h1
  refine ⟨z, fun i hi => by simp only [z, hi, ↓reduceIte], ?_, ?_⟩
  · have e : ∑ i ∈ T, (z i : ℂ) * lam i = (D : ℂ) * ∑ i ∈ T, (q i : ℂ) * lam i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hzC i hi]; ring
    rw [e, hq, mul_zero]
  · intro h0
    have h1 := hz i₀ hi₀
    rw [h0, Int.cast_zero] at h1
    have hD : (D : ℚ) ≠ 0 := by
      simp only [D]
      push_cast
      exact Finset.prod_ne_zero_iff.2 fun j _ => by exact_mod_cast (q j).den_ne_zero
    exact hne ((mul_eq_zero.1 h1.symm).resolve_right hD)

theorem baker_descent_aux (hB : BakerTheorem) (F : IntermediateField ℚ ℂ)
    (hF : ∀ x ∈ F, IsAlgebraic ℚ x) {ι : Type*} (lam : ι → ℂ) :
    ∀ (n : ℕ) (T : Finset ι), T.card = n →
      (∀ i ∈ T, IsAlgebraic ℚ (Complex.exp (lam i))) →
      ∀ β : ι → ℂ, (∀ i ∈ T, β i ∈ F) → (∀ i, i ∉ T → β i = 0) →
        ∑ i ∈ T, β i * lam i = 0 → SpanIn F (IntRel T lam) β := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hn hlam β hβ hβ0 h
    by_cases hind : ∀ q : ι → ℚ, ∑ i ∈ T, (q i : ℂ) * lam i = 0 → ∀ i ∈ T, q i = 0
    · -- independent logarithms: Baker gives `β = 0`
      have hz := baker_finset hB T lam hlam hind β (fun i hi => hF _ (hβ i hi)) h
      have e : β = 0 := by
        funext i
        by_cases hi : i ∈ T
        · exact hz i hi
        · exact hβ0 i hi
      rw [e]
      exact SpanIn.zero
    · -- a rational relation: remove one logarithm
      push Not at hind
      obtain ⟨q, hq, i₀, hi₀, hne⟩ := hind
      obtain ⟨z, hz0, hzsum, hzne⟩ := exists_int_relation T lam q hq hi₀ hne
      have hzC : (z i₀ : ℂ) ≠ 0 := by exact_mod_cast hzne
      have hcalg : β i₀ * (z i₀ : ℂ)⁻¹ ∈ F :=
        F.mul_mem (hβ i₀ hi₀) (F.inv_mem (F.intCast_mem (z i₀)))
      have h1 : β i₀ - β i₀ * (z i₀ : ℂ)⁻¹ * z i₀ = 0 := by
        rw [mul_assoc, inv_mul_cancel₀ hzC, mul_one, sub_self]
      -- the new coefficient vector, supported on `T.erase i₀`
      have hβ'alg : ∀ i ∈ T.erase i₀, β i - β i₀ * (z i₀ : ℂ)⁻¹ * z i ∈ F :=
        fun i hi => F.sub_mem (hβ i (Finset.mem_of_mem_erase hi))
          (F.mul_mem hcalg (F.intCast_mem (z i)))
      have hβ'0 : ∀ i, i ∉ T.erase i₀ → β i - β i₀ * (z i₀ : ℂ)⁻¹ * z i = 0 := by
        intro i hi
        by_cases hi0 : i = i₀
        · rw [hi0]; exact h1
        · have hiT : i ∉ T := fun hiT => hi (Finset.mem_erase.2 ⟨hi0, hiT⟩)
          rw [hβ0 i hiT, hz0 i hiT]
          simp
      have hsum' : ∑ i ∈ T.erase i₀, (β i - β i₀ * (z i₀ : ℂ)⁻¹ * z i) * lam i = 0 := by
        rw [Finset.sum_erase T (by rw [h1, zero_mul])]
        have e : ∑ i ∈ T, (β i - β i₀ * (z i₀ : ℂ)⁻¹ * z i) * lam i =
            ∑ i ∈ T, β i * lam i - β i₀ * (z i₀ : ℂ)⁻¹ * ∑ i ∈ T, (z i : ℂ) * lam i := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [e, h, hzsum]
        ring
      have hspan := ih (T.erase i₀).card (by rw [← hn]; exact Finset.card_erase_lt_of_mem hi₀)
        (T.erase i₀) rfl (fun i hi => hlam i (Finset.mem_of_mem_erase hi)) _ hβ'alg hβ'0 hsum'
      -- integer relations on `T.erase i₀` are integer relations on `T`
      have hmono : IntRel (T.erase i₀) lam ⊆ IntRel T lam := by
        rintro v ⟨y, hy0, hysum, hvy⟩
        refine ⟨y, fun i hi => hy0 i (fun hi' => hi (Finset.mem_of_mem_erase hi')), ?_, hvy⟩
        rw [← Finset.sum_erase T (a := i₀)
          (by rw [hy0 i₀ (Finset.notMem_erase i₀ T), Int.cast_zero, zero_mul])]
        exact hysum
      have hv : (fun i => (z i : ℂ)) ∈ IntRel T lam := ⟨z, hz0, hzsum, fun _ => rfl⟩
      have hstep := SpanIn.step (β i₀ * (z i₀ : ℂ)⁻¹) hcalg (fun i => (z i : ℂ)) hv _
        (hspan.mono hmono)
      have e : β = fun i => β i₀ * (z i₀ : ℂ)⁻¹ * (z i : ℂ) +
          (β i - β i₀ * (z i₀ : ℂ)⁻¹ * z i) := by
        funext i; ring
      rw [e]
      exact hstep

/-- **Baker's theorem, in the form used here.** Let `lam i` (`i ∈ T`) be logarithms of algebraic
numbers, not assumed independent, and let `F` be a field of algebraic numbers. A linear
relation `∑ β_i lam_i = 0` with coefficients in `F` is a combination, with coefficients in `F`,
of integer relations. -/
theorem baker_descent (hB : BakerTheorem) (F : IntermediateField ℚ ℂ)
    (hF : ∀ x ∈ F, IsAlgebraic ℚ x) {ι : Type*} (lam : ι → ℂ) (T : Finset ι)
    (hlam : ∀ i ∈ T, IsAlgebraic ℚ (Complex.exp (lam i))) (β : ι → ℂ)
    (hβ : ∀ i ∈ T, β i ∈ F) (hβ0 : ∀ i, i ∉ T → β i = 0)
    (h : ∑ i ∈ T, β i * lam i = 0) : SpanIn F (IntRel T lam) β :=
  baker_descent_aux hB F hF lam T.card T rfl hlam β hβ hβ0 h

/-! ## 3. The logarithms `Log (1 - r/t)` and `iπ` -/

/-- The logarithms: `iπ` at `none`, `Log (1 - r/t)` at `some r`. -/
noncomputable def lamOf : Option ℂ → ℂ
  | none => Real.pi * I
  | some r => Complex.log (1 - r / tC)

theorem isAlgebraic_root {r : ℂ} (hr : IsOfFinOrder r) : IsAlgebraic ℚ r :=
  ((isIntegral_of_finOrder hr).tower_top (A := ℚ)).isAlgebraic

theorem isAlgebraic_I : IsAlgebraic ℚ I := isAlgebraic_root isOfFinOrder_I

theorem isAlgebraic_tC : IsAlgebraic ℚ tC := (isIntegral_tC.tower_top (A := ℚ)).isAlgebraic

theorem w_ne_zero {r : ℂ} (hr : IsOfFinOrder r) : 1 - r / tC ≠ 0 := by
  rw [show 1 - r / tC = (tC - r) / tC by rw [sub_div, div_self tC_ne_zero]]
  exact div_ne_zero (tC_sub_root_ne_zero hr) tC_ne_zero

theorem isAlgebraic_exp_lamOf {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) :
    ∀ i ∈ Finset.insertNone S, IsAlgebraic ℚ (Complex.exp (lamOf i)) := by
  intro i hi
  rcases i with _ | r
  · change IsAlgebraic ℚ (Complex.exp (Real.pi * I))
    rw [Complex.exp_pi_mul_I]
    exact isAlgebraic_one.neg
  · have hr := hS r (Finset.some_mem_insertNone.1 hi)
    change IsAlgebraic ℚ (Complex.exp (Complex.log (1 - r / tC)))
    rw [Complex.exp_log (w_ne_zero hr), div_eq_mul_inv]
    exact isAlgebraic_one.sub ((isAlgebraic_root hr).mul isAlgebraic_tC.inv)

/-- An integer relation among `iπ` and the `Log (1 - r/t)` is a multiplicative relation among
the `1 - r/t`. -/
theorem isRelation_of_intRel {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {z : Option ℂ → ℤ} (hz : ∑ i ∈ Finset.insertNone S, (z i : ℂ) * lamOf i = 0) :
    IsRelation S (fun r => z (some r)) := by
  rw [Finset.sum_insertNone] at hz
  have h1 : ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / tC) =
      -(z none : ℂ) * (Real.pi * I) := by
    have hz' : (z none : ℂ) * (Real.pi * I) +
        ∑ r ∈ S, (z (some r) : ℂ) * Complex.log (1 - r / tC) = 0 := hz
    linear_combination hz'
  refine ⟨Complex.exp (-(z none : ℂ) * (Real.pi * I)), ?_, ?_⟩
  · refine isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, ?_⟩
    rw [← Complex.exp_nat_mul]
    have e : ((2 : ℕ) : ℂ) * (-(z none : ℂ) * (Real.pi * I)) =
        ((-z none : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  · rw [← h1, Complex.exp_sum]
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [Complex.exp_int_mul, Complex.exp_log (w_ne_zero (hS r hr))]

/-! ## 4. Step 1 of Theorem C -/

/-- The combination `∑ c_k · rel_k` of the 13 relations, with complex coefficients. -/
def combC (c : Fin 13 → ℂ) (j : ℕ) : ℂ :=
  c 0 * rel1 j + c 1 * rel2 j + c 2 * rel3 j + c 3 * rel4 j + c 4 * rel5 j + c 5 * rel6 j
    + c 6 * rel7 j + c 7 * rel8 j + c 8 * rel9 j + c 9 * rel10 j + c 10 * rel11 j
    + c 11 * rel12 j + c 12 * rel13 j

theorem combC_cast (c : Fin 13 → ℤ) (j : ℕ) :
    combC (fun k => (c k : ℂ)) j = ((comb c j : ℤ) : ℂ) := by
  simp only [combC, comb]
  push_cast
  ring

open Classical in
/-- The conclusion of Step 1 for a coefficient vector `d` on a finite set `S` of roots of unity:
`d` vanishes outside `R0`, and on `R0` it is a combination of the 13 relations with algebraic
coefficients. -/
def InSpan13 (S : Finset ℂ) (d : ℂ → ℂ) : Prop :=
  (∀ r ∈ S, r ∉ R0 → d r = 0) ∧
    ∃ c : Fin 13 → ℂ, (∀ k, IsAlgebraic ℚ (c k)) ∧
      ∀ j ∈ R0Exps, (if ζ120 ^ j ∈ S then d (ζ120 ^ j) else 0) = combC c j

open Classical in
theorem inSpan13_of_spanIn {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {F : IntermediateField ℚ ℂ} (hF : ∀ x ∈ F, IsAlgebraic ℚ x)
    {β : Option ℂ → ℂ} (h : SpanIn F (IntRel (Finset.insertNone S) lamOf) β) :
    InSpan13 S (fun r => β (some r)) := by
  induction h with
  | zero =>
    exact ⟨fun _ _ _ => rfl, fun _ => 0, fun _ => isAlgebraic_zero, fun j _ => by
      simp [combC]⟩
  | step a ha v hv w _ ih =>
    obtain ⟨z, -, hzsum, hvz⟩ := hv
    obtain ⟨hz0, c₀, hc₀⟩ := relations_classified hS (isRelation_of_intRel hS hzsum)
    obtain ⟨hw0', cw, hcw, hw'⟩ := ih
    have hw0 : ∀ r ∈ S, r ∉ R0 → w (some r) = 0 := hw0'
    have hw : ∀ j ∈ R0Exps, (if ζ120 ^ j ∈ S then w (some (ζ120 ^ j)) else 0) = combC cw j :=
      hw'
    refine ⟨fun r hr hR => ?_, fun k => a * (((c₀ k : ℚ) / 4 : ℚ) : ℂ) + cw k, fun k => ?_,
      fun j hj => ?_⟩
    · change a * v (some r) + w (some r) = 0
      rw [hvz, hz0 r hr hR, hw0 r hr hR]
      simp
    · exact ((hF a ha).mul (isAlgebraic_ratCast ℚ _)).add (hcw k)
    · have h1 := hc₀ j hj
      have h2 := hw j hj
      have e : combC (fun k => a * (((c₀ k : ℚ) / 4 : ℚ) : ℂ) + cw k) j =
          a / 4 * combC (fun k => (c₀ k : ℂ)) j + combC cw j := by
        simp only [combC]
        push_cast
        ring
      rw [e, combC_cast, ← h1, ← h2]
      by_cases hjS : ζ120 ^ j ∈ S
      · simp only [hjS, ↓reduceIte, hvz]
        push_cast
        ring
      · simp only [hjS, ↓reduceIte]
        push_cast
        ring

/-- **Step 1 of Theorem C, from Baker's theorem.** Let `S` be a finite set of roots of unity,
and let `d_r` (`r ∈ S`) and `γ` be algebraic numbers with `∑ d_r Log(1 - r/t) = γ π`. Then `d`
vanishes outside the 24 roots of `R0`, and on `R0` it is a combination of the 13 relations
with algebraic coefficients. -/
theorem baker_step1 (hB : BakerTheorem) {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r)
    {d : ℂ → ℂ} (hd : ∀ r ∈ S, IsAlgebraic ℚ (d r)) {γ : ℂ} (hγ : IsAlgebraic ℚ γ)
    (h : ∑ r ∈ S, d r * Complex.log (1 - r / tC) = γ * Real.pi) : InSpan13 S d := by
  classical
  let β : Option ℂ → ℂ := fun o =>
    match o with
    | none => γ * I
    | some r => if r ∈ S then d r else 0
  have hβS : ∀ r ∈ S, β (some r) = d r := fun r hr => by simp only [β, hr, ↓reduceIte]
  have hF : ∀ x ∈ algebraicClosure ℚ ℂ, IsAlgebraic ℚ x := fun x hx =>
    mem_algebraicClosure_iff.1 hx
  have hspan : SpanIn (algebraicClosure ℚ ℂ) (IntRel (Finset.insertNone S) lamOf) β := by
    refine baker_descent hB _ hF lamOf _ (isAlgebraic_exp_lamOf hS) β ?_ ?_ ?_
    · intro i hi
      rcases i with _ | r
      · exact mem_algebraicClosure_iff.2 (hγ.mul isAlgebraic_I)
      · rw [hβS r (Finset.some_mem_insertNone.1 hi)]
        exact mem_algebraicClosure_iff.2 (hd r (Finset.some_mem_insertNone.1 hi))
    · intro i hi
      rcases i with _ | r
      · exact absurd (by simp) hi
      · have hr : r ∉ S := fun hr => hi (Finset.some_mem_insertNone.2 hr)
        simp only [β, hr, ↓reduceIte]
    · rw [Finset.sum_insertNone]
      have e : ∑ r ∈ S, β (some r) * lamOf (some r) =
          ∑ r ∈ S, d r * Complex.log (1 - r / tC) :=
        Finset.sum_congr rfl fun r hr => by rw [hβS r hr]; rfl
      rw [e, h]
      change γ * I * (Real.pi * I) + γ * Real.pi = 0
      linear_combination γ * Real.pi * Complex.I_sq
  obtain ⟨h0, c, hc, hcomb⟩ := inSpan13_of_spanIn hS hF hspan
  refine ⟨fun r hr hR => ?_, c, hc, fun j hj => ?_⟩
  · have h1 : β (some r) = 0 := h0 r hr hR
    rwa [hβS r hr] at h1
  · have h1 : (if ζ120 ^ j ∈ S then β (some (ζ120 ^ j)) else 0) = combC c j := hcomb j hj
    by_cases hjS : ζ120 ^ j ∈ S
    · simp only [hjS, ↓reduceIte] at h1 ⊢
      rwa [hβS _ hjS] at h1
    · simp only [hjS, ↓reduceIte] at h1 ⊢
      exact h1

/-! ## 5. The converse, without Baker's theorem -/

/-- **Logarithmic form of a relation.** If `∏ w_j^(f j)` is a root of unity, then
`∑ f_j Log w_j` is a rational multiple of `iπ`. -/
theorem log_form {J : Finset ℕ} {f : ℕ → ℤ} (h : IsRelJ J f) :
    ∃ q : ℚ, ∑ j ∈ J, (f j : ℂ) * Complex.log (wJ j) = q * (Real.pi * I) := by
  obtain ⟨ξ, hξ, hprod⟩ := h
  have hexp : Complex.exp (∑ j ∈ J, (f j : ℂ) * Complex.log (wJ j)) = ξ := by
    rw [Complex.exp_sum, ← hprod]
    exact Finset.prod_congr rfl fun j _ => by
      rw [Complex.exp_int_mul, Complex.exp_log (wJ_ne_zero j)]
  have hn : Complex.exp ((orderOf ξ : ℂ) * ∑ j ∈ J, (f j : ℂ) * Complex.log (wJ j)) = 1 := by
    rw [Complex.exp_nat_mul, hexp, pow_orderOf_eq_one]
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hn
  have hpos : ((orderOf ξ : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hξ.orderOf_pos.ne'
  refine ⟨2 * m / orderOf ξ, ?_⟩
  push_cast
  field_simp
  linear_combination hm

theorem sum_combC (c : Fin 13 → ℂ) (J : Finset ℕ) (L : ℕ → ℂ) :
    ∑ j ∈ J, combC c j * L j =
      c 0 * ∑ j ∈ J, (rel1 j : ℂ) * L j + c 1 * ∑ j ∈ J, (rel2 j : ℂ) * L j
        + c 2 * ∑ j ∈ J, (rel3 j : ℂ) * L j + c 3 * ∑ j ∈ J, (rel4 j : ℂ) * L j
        + c 4 * ∑ j ∈ J, (rel5 j : ℂ) * L j + c 5 * ∑ j ∈ J, (rel6 j : ℂ) * L j
        + c 6 * ∑ j ∈ J, (rel7 j : ℂ) * L j + c 7 * ∑ j ∈ J, (rel8 j : ℂ) * L j
        + c 8 * ∑ j ∈ J, (rel9 j : ℂ) * L j + c 9 * ∑ j ∈ J, (rel10 j : ℂ) * L j
        + c 10 * ∑ j ∈ J, (rel11 j : ℂ) * L j + c 11 * ∑ j ∈ J, (rel12 j : ℂ) * L j
        + c 12 * ∑ j ∈ J, (rel13 j : ℂ) * L j := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp only [combC]; ring

/-- **The converse of Step 1** (no Baker's theorem): a combination of the 13 relations with
algebraic coefficients `c_k` gives an algebraic multiple of `π`. -/
theorem step1_converse (c : Fin 13 → ℂ) (hc : ∀ k, IsAlgebraic ℚ (c k)) :
    ∃ γ : ℂ, IsAlgebraic ℚ γ ∧
      ∑ j ∈ R0Exps, combC c j * Complex.log (wJ j) = γ * Real.pi := by
  obtain ⟨q1, h1⟩ := log_form rel1_isRel
  obtain ⟨q2, h2⟩ := log_form rel2_isRel
  obtain ⟨q3, h3⟩ := log_form rel3_isRel
  obtain ⟨q4, h4⟩ := log_form rel4_isRel
  obtain ⟨q5, h5⟩ := log_form rel5_isRel
  obtain ⟨q6, h6⟩ := log_form rel6_isRel
  obtain ⟨q7, h7⟩ := log_form rel7_isRel
  obtain ⟨q8, h8⟩ := log_form rel8_isRel
  obtain ⟨q9, h9⟩ := log_form rel9_isRel
  obtain ⟨q10, h10⟩ := log_form rel10_isRel
  obtain ⟨q11, h11⟩ := log_form rel11_isRel
  obtain ⟨q12, h12⟩ := log_form rel12_isRel
  obtain ⟨q13, h13⟩ := log_form rel13_isRel
  have ha : ∀ (k : Fin 13) (q : ℚ), IsAlgebraic ℚ (c k * (q : ℂ)) := fun k q =>
    (hc k).mul (isAlgebraic_ratCast ℚ q)
  refine ⟨(c 0 * q1 + c 1 * q2 + c 2 * q3 + c 3 * q4 + c 4 * q5 + c 5 * q6 + c 6 * q7
    + c 7 * q8 + c 8 * q9 + c 9 * q10 + c 10 * q11 + c 11 * q12 + c 12 * q13) * I, ?_, ?_⟩
  · have a1 := (ha 0 q1).add (ha 1 q2)
    have a2 := a1.add (ha 2 q3)
    have a3 := a2.add (ha 3 q4)
    have a4 := a3.add (ha 4 q5)
    have a5 := a4.add (ha 5 q6)
    have a6 := a5.add (ha 6 q7)
    have a7 := a6.add (ha 7 q8)
    have a8 := a7.add (ha 8 q9)
    have a9 := a8.add (ha 9 q10)
    have a10 := a9.add (ha 10 q11)
    have a11 := a10.add (ha 11 q12)
    have a12 := a11.add (ha 12 q13)
    exact a12.mul isAlgebraic_I
  · rw [sum_combC, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
    ring

end PiFormula
