import Pilean.PiFormula.LogForms

/-!
# Theorem C, the rational part: dimension exactly 8 (milestone M7, part 2)

`ratSpace N` is the space of rational patterns of period `N` whose series
`∑ ρ(k) 2^(-⌊k/2⌋)/k` is a rational multiple of `π` (possibly 0). For `N` a multiple of 120,
**from Baker's theorem**:

* `finrank_ratSpace`: `ratSpace N` has dimension exactly 8;
* `span_namedFam`: it is spanned by the eight named series of `VSeries.lean`.

The proof of the upper bound. Let `ρ` be in `ratSpace 120`, with value `q π` and coefficient
vector `c ∈ ℂ^13` (its coefficients `d` are `∑ c_k rel_k` on `R0`, by Step 1).

* For `b ≡ 1 (mod 4)` prime to 120, `∑_j d(ζ^(bj)) Log w_j = q π` (`conj_value`: rational
  values are Galois invariant).
* The left side is `(∑_l c_l ν_l) · iπ`, where `ν_l` is the exact multiple of `iπ` of the
  relation `rel_l` conjugated by `b` (`conjlog_b`, from the table of exact arguments).
* Comparing `b = 41, 49, 61, 73, 97` with `b = 1` gives five independent linear constraints
  on `c` (`coeff_mem_constraintSpace`): `c` lies in a subspace of `ℂ^13` of dimension 8.
* So nine patterns have linearly dependent coefficient vectors, hence are linearly dependent
  (`dependent_of_coeffs`).
-/

open Complex

namespace PiFormula

/-! ## 1. The conjugated value in terms of the coefficient vector -/

theorem ζ120_pow_mem_R0_iff (x : ℕ) : ζ120 ^ x ∈ R0 ↔ x % 120 ∈ R0Exps := by
  constructor
  · rintro ⟨j, hj, h⟩
    have hlt : ∀ j ∈ R0Exps, j < 120 := by decide
    rw [← ζ120_pow_mod] at h
    have e := ζ120_prim.pow_inj (Nat.mod_lt x (by norm_num)) (hlt j hj) h
    rw [e]
    exact hj
  · intro h
    exact ⟨x % 120, h, (ζ120_pow_mod x).symm⟩

theorem ζ120_pow_mem_rootsN (x : ℕ) : ζ120 ^ x ∈ rootsN 120 := by
  rw [mem_rootsN (by norm_num), ← pow_mul, mul_comm, pow_mul, ζ120_prim.pow_eq_one, one_pow]

/-- The Galois-conjugated value, written with the coefficient vector `c`. -/
theorem conj_value_coeff (hB : BakerTheorem) {ρ : ℕ → ℚ} (hp : ∀ k, ρ (k + 120) = ρ k)
    {q : ℚ} (h : HasSum (seriesTerm ρ) (q * Real.pi)) {c : Fin 13 → ℂ}
    (hzero : ∀ r ∈ rootsN 120, r ∉ R0 → fourierD 120 ρ r = 0)
    (hcomb : ∀ j ∈ R0Exps, fourierD 120 ρ (ζ120 ^ j) = combC c j)
    {b : ℕ} (hb : Nat.Coprime b 120) (hb4 : b % 4 = 1)
    (hmaps : ∀ j ∈ R0Exps, b * j % 120 ∈ R0Exps)
    (hoff : ∀ x ∈ Finset.range 120, x ∉ R0Exps → b * x % 120 ∉ R0Exps) :
    ∑ j ∈ R0Exps, combC c (b * j % 120) * Complex.log (wJ j) = q * Real.pi := by
  rw [← conj_value hB hp h hb hb4]
  have hsub : R0Exps ⊆ Finset.range 120 := by decide
  have e := Finset.sum_subset hsub
    (f := fun a => fourierD 120 ρ (ζ120 ^ (b * a)) * Complex.log (wJ a))
    (fun x hx hxn => by
      have hR : ζ120 ^ (b * x) ∉ R0 := fun hR =>
        hoff x hx hxn ((ζ120_pow_mem_R0_iff _).1 hR)
      change fourierD 120 ρ (ζ120 ^ (b * x)) * Complex.log (wJ x) = 0
      rw [hzero _ (ζ120_pow_mem_rootsN _) hR, zero_mul])
  rw [← e]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← ζ120_pow_mod (b * j), hcomb _ (hmaps j hj)]

/-! ## 2. The five constraints -/

/-- The coefficient vectors allowed for a rational multiple of `π`: a subspace of `ℂ^13` cut
out by five equations. -/
def constraintSpace : Submodule ℂ (Fin 13 → ℂ) where
  carrier := {c | c 11 = c 5 - c 4 + c 10 ∧ c 12 = 2 * c 10 ∧ c 6 = c 9 ∧ c 7 = c 9 ∧
    c 8 = c 9}
  add_mem' := by
    rintro c c' ⟨h1, h2, h3, h4, h5⟩ ⟨k1, k2, k3, k4, k5⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Pi.add_apply, h1, h2, h3, h4, h5, k1, k2, k3, k4, k5] <;> ring
  zero_mem' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp
  smul_mem' := by
    rintro a c ⟨h1, h2, h3, h4, h5⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Pi.smul_apply, smul_eq_mul, h1, h2, h3, h4, h5] <;> ring

theorem mem_constraintSpace {c : Fin 13 → ℂ} : c ∈ constraintSpace ↔
    (c 11 = c 5 - c 4 + c 10 ∧ c 12 = 2 * c 10 ∧ c 6 = c 9 ∧ c 7 = c 9 ∧ c 8 = c 9) :=
  Iff.rfl

/-- The constraint space has dimension at most 8: the coordinates `0, ..., 5, 9, 10`
determine the vector. -/
theorem finrank_constraintSpace_le : Module.finrank ℂ constraintSpace ≤ 8 := by
  let e : Fin 8 → Fin 13 := ![0, 1, 2, 3, 4, 5, 9, 10]
  let f : constraintSpace →ₗ[ℂ] (Fin 8 → ℂ) :=
    (LinearMap.funLeft ℂ ℂ e) ∘ₗ constraintSpace.subtype
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨c, h1, h2, h3, h4, h5⟩ hc
    have v : ∀ i : Fin 8, c (e i) = 0 := fun i => congrFun hc i
    have c0 : c 0 = 0 := v 0
    have c1 : c 1 = 0 := v 1
    have c2 : c 2 = 0 := v 2
    have c3 : c 3 = 0 := v 3
    have c4 : c 4 = 0 := v 4
    have c5 : c 5 = 0 := v 5
    have c9 : c 9 = 0 := v 6
    have c10 : c 10 = 0 := v 7
    have c6 : c 6 = 0 := h3.trans c9
    have c7 : c 7 = 0 := h4.trans c9
    have c8 : c 8 = 0 := h5.trans c9
    have c11 : c 11 = 0 := by rw [h1, c5, c4, c10]; ring
    have c12 : c 12 = 0 := by rw [h2, c10, mul_zero]
    apply Subtype.ext
    funext k
    fin_cases k
    exacts [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12]
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fin_fun] at h

/-- **The five constraints.** The coefficient vector of a pattern with a rational multiple of
`π` lies in the constraint space. -/
theorem coeff_mem_constraintSpace (hB : BakerTheorem) {ρ : ℕ → ℚ}
    (hp : ∀ k, ρ (k + 120) = ρ k) {q : ℚ} (h : HasSum (seriesTerm ρ) (q * Real.pi))
    {c : Fin 13 → ℂ} (hzero : ∀ r ∈ rootsN 120, r ∉ R0 → fourierD 120 ρ r = 0)
    (hcomb : ∀ j ∈ R0Exps, fourierD 120 ρ (ζ120 ^ j) = combC c j) :
    c ∈ constraintSpace := by
  have hpiI : (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_pos.ne') Complex.I_ne_zero
  have E1 := conj_value_coeff hB hp h hzero hcomb (b := 1) (by norm_num) (by norm_num)
    maps_1 off_1
  have E41 := conj_value_coeff hB hp h hzero hcomb (b := 41) (by norm_num) (by norm_num)
    maps_41 off_41
  have E49 := conj_value_coeff hB hp h hzero hcomb (b := 49) (by norm_num) (by norm_num)
    maps_49 off_49
  have E61 := conj_value_coeff hB hp h hzero hcomb (b := 61) (by norm_num) (by norm_num)
    maps_61 off_61
  have E73 := conj_value_coeff hB hp h hzero hcomb (b := 73) (by norm_num) (by norm_num)
    maps_73 off_73
  have E97 := conj_value_coeff hB hp h hzero hcomb (b := 97) (by norm_num) (by norm_num)
    maps_97 off_97
  rw [conjlog_1] at E1
  rw [conjlog_41] at E41
  rw [conjlog_49] at E49
  rw [conjlog_61] at E61
  rw [conjlog_73] at E73
  rw [conjlog_97] at E97
  have D41 := mul_right_cancel₀ hpiI (E41.trans E1.symm)
  have D49 := mul_right_cancel₀ hpiI (E49.trans E1.symm)
  have D61 := mul_right_cancel₀ hpiI (E61.trans E1.symm)
  have D73 := mul_right_cancel₀ hpiI (E73.trans E1.symm)
  have D97 := mul_right_cancel₀ hpiI (E97.trans E1.symm)
  rw [mem_constraintSpace]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (-3 / 2 : ℂ) * D41
  · linear_combination (-1 : ℂ) * D61
  · linear_combination (-1 / 8 : ℂ) * D73 + (3 / 8 : ℂ) * D97
  · linear_combination (1 / 8 : ℂ) * D49 + (1 / 4 : ℂ) * D73
  · linear_combination (3 / 8 : ℂ) * D49 - (1 / 8 : ℂ) * D73 + (1 / 8 : ℂ) * D97

/-! ## 3. Dimension exactly 8 -/

/-- If the coefficient vectors of some patterns lie in a subspace of `ℂ^13` of dimension
smaller than their number, the patterns are linearly dependent over `ℚ`. -/
theorem dependent_of_coeffs {N : ℕ} (hN : 0 < N) (h8 : 8 ∣ N) {ι : Type*} [Fintype ι]
    (ρ : ι → ℕ → ℚ) (hρ : ∀ i k, ρ i (k + N) = ρ i k) (c : ι → Fin 13 → ℂ)
    (hzero : ∀ i, ∀ r ∈ rootsN N, r ∉ R0 → fourierD N (ρ i) r = 0)
    (hcomb : ∀ i, ∀ j ∈ R0Exps, ζ120 ^ j ∈ rootsN N →
      fourierD N (ρ i) (ζ120 ^ j) = combC (c i) j)
    (P : Submodule ℂ (Fin 13 → ℂ)) (hP : ∀ i, c i ∈ P)
    (hcard : Module.finrank ℂ P < Fintype.card ι) : ¬ LinearIndependent ℚ ρ := by
  intro hLI
  have hnot : ¬ LinearIndependent ℂ c := fun hc' => by
    have h1 : LinearIndependent ℂ (fun i => (⟨c i, hP i⟩ : P)) :=
      LinearIndependent.of_comp P.subtype hc'
    have h2 := h1.fintype_card_le_finrank
    omega
  rw [Fintype.linearIndependent_iff] at hnot
  push Not at hnot
  obtain ⟨a, ha, i₀, hi₀⟩ := hnot
  have ha' : ∀ k, ∑ i, a i * c i k = 0 := fun k => by
    have h1 := congrFun ha k
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h1
  have hdep := fun k => sum_pattern_eq_zero hN h8 ρ hρ c hzero hcomb a ha' k
  obtain ⟨q, hq, hsum⟩ := rat_dependence ρ a hi₀ hdep
  rw [Fintype.linearIndependent_iff] at hLI
  refine hq (hLI q ?_ i₀)
  funext k
  simpa [Finset.sum_apply] using hsum k

/-- More than 8 patterns of `ratSpace 120` are linearly dependent over `ℚ`. -/
theorem not_linearIndependent_rat (hB : BakerTheorem) {ι : Type*} [Fintype ι]
    (hcard : 8 < Fintype.card ι) (ρ : ι → ℕ → ℚ) (hmem : ∀ i, ρ i ∈ ratSpace 120) :
    ¬ LinearIndependent ℚ ρ := by
  have hspan := fun i => inSpan13_of_mem hB (N := 120) (by norm_num) (by norm_num)
    (ratSpace_le_algSpace 120 (hmem i))
  choose c hc using fun i => (hspan i).2
  have hcomb : ∀ i, ∀ j ∈ R0Exps, fourierD 120 (ρ i) (ζ120 ^ j) = combC (c i) j :=
    fun i j hj => by
      have h1 := (hc i).2 j hj
      simp only [ζ120_pow_mem_rootsN j, ↓reduceIte] at h1
      exact h1
  have hP : ∀ i, c i ∈ constraintSpace := fun i => by
    obtain ⟨hp, q, h⟩ := hmem i
    exact coeff_mem_constraintSpace hB hp h (hspan i).1 (hcomb i)
  exact dependent_of_coeffs (N := 120) (by norm_num) (by norm_num) ρ (fun i => (hmem i).1) c
    (fun i => (hspan i).1) (fun i j hj _ => hcomb i j hj) constraintSpace hP
    (lt_of_le_of_lt finrank_constraintSpace_le hcard)

/-- For `N` a multiple of 120, the patterns of period `N` with a rational multiple of `π` are
those of period 120 (from Baker's theorem). -/
theorem ratSpace_eq (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) :
    ratSpace N = ratSpace 120 := by
  have h8 : 8 ∣ N := Dvd.dvd.trans (by norm_num) h120
  ext ρ
  constructor
  · intro h
    exact ⟨fun k => period_120 hB hN h8 (ratSpace_le_algSpace N h) k, h.2⟩
  · rintro ⟨hp, hq⟩
    exact ⟨periodic_of_dvd hp h120, hq⟩

theorem rank_ratSpace_le (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) :
    Module.rank ℚ (ratSpace N) ≤ (8 : ℕ) := by
  rw [ratSpace_eq hB hN h120]
  refine rank_le fun s hs => ?_
  by_contra hcard
  push Not at hcard
  have hLI : LinearIndependent ℚ (fun i : s => ((i : ratSpace 120) : ℕ → ℚ)) :=
    hs.map' (ratSpace 120).subtype (Submodule.ker_subtype _)
  exact not_linearIndependent_rat hB (ι := s) (by simpa using hcard)
    (fun i : s => ((i : ratSpace 120) : ℕ → ℚ)) (fun i => (i : ratSpace 120).2) hLI

/-- **Theorem C, the rational part (from Baker's theorem).** For `N` a multiple of 120, the
rational patterns of period `N` whose series is a rational multiple of `π` form a space of
dimension exactly 8. -/
theorem finrank_ratSpace (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) :
    Module.finrank ℚ (ratSpace N) = 8 :=
  le_antisymm (Module.finrank_le_of_rank_le (rank_ratSpace_le hB hN h120))
    (theoremC_bounds hB hN h120).2.2.1

/-- **The eight named series span** (from Baker's theorem): every rational pattern of period
`N` whose series is a rational multiple of `π` is a rational combination of the eight named
patterns of `VSeries.lean`. -/
theorem span_namedFam (hB : BakerTheorem) {N : ℕ} (hN : 0 < N) (h120 : 120 ∣ N) :
    Submodule.span ℚ (Set.range (namedFam h120)) = ⊤ := by
  have h8 : 8 ∣ N := Dvd.dvd.trans (by norm_num) h120
  have hfin := finite_algSpace hB hN h8
  have hfin' : Module.Finite ℚ (ratSpace N) :=
    Module.Finite.of_injective (Submodule.inclusion (ratSpace_le_algSpace N))
      (Submodule.inclusion_injective _)
  exact (namedFam_linearIndependent h120).span_eq_top_of_card_eq_finrank'
    (by rw [finrank_ratSpace hB hN h120]; rfl)

end PiFormula
