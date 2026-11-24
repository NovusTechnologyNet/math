module

public import Pilean.PiFormula.GoodPrimes

/-!
# Part III, Step 3 (upper half): the 13 relations are all of them (milestone M5)

`Relations.lean` proves 13 multiplicative relations among the 24 numbers `w_j = 1 - ζ^j / t`
(`ζ = ζ_120`, `j ∈ R0Exps`). This file proves that there are no others: every relation among
the 24 numbers is a rational combination of the 13 (`relations_span`), and the 13 are linearly
independent (`rel_independent`). So the 24 numbers generate a group of rank `24 - 13 = 11`.
`relations_classified` joins this with Step 2 (`GoodPrimes.lean`): it describes the relations
on an arbitrary finite set of roots of unity.

The core is `basis_independent`: the 11 numbers `w_j`, `j ∈ B11`, satisfy no relation.
The proof uses no numerical computation:

* **Galois conjugation** (`isRelJ_conj`). If `∏ w_j^(f j)` is a root of unity and `a` is prime
  to 120 with `a ≡ 1 (mod 4)`, then `∏ w_{aj}^(f j)` is a root of unity. (The embedding
  `ℚ(ζ) → ℂ`, `ζ ↦ ζ^a`, fixes `i`, hence `t`.)
* **Absolute values** (`sum_ell_eq_zero`). So `∑ f j · log |w_{aj}| = 0` for each such `a`.
  Taking `a ≡ 1 (mod 20)` moves only the roots of order 6, 8, 12, 24, and taking
  `a ≡ 1 (mod 24)` moves only those of order 10 and 20. The differences of these equations,
  with `|w_{30 - j}| = |w_j|`, kill the coefficients of the six roots that carry units. All
  that is needed about the numbers `log |w_j|` is that a few of them differ, which comes from
  `|t - r|² = 3 - 2 cos θ - 2 sin θ` and the signs of `cos` and `sin`.
* **Private primes.** The four remaining roots `ζ_8^3, ζ_8^7, -1, -i` each have a prime ideal
  of the algebraic integers containing `t - r` and no other `t - r'` (above 3, 3, 5, 5).
* The last coefficient, of `w_30 = 1/t`, vanishes because `|1/t| ≠ 1`.
-/

@[expose] public section

open Complex Polynomial IntermediateField

namespace PiFormula

/-! ## 1. Relations indexed by exponents -/

/-- `w_j = 1 - ζ^j / t`, with `ζ = ζ_120`. -/
noncomputable def wJ (j : ℕ) : ℂ := 1 - ζ120 ^ j / tC

theorem isOfFinOrder_ζ120_pow (j : ℕ) : IsOfFinOrder (ζ120 ^ j) :=
  isOfFinOrder_iff_pow_eq_one.2 ⟨120, by norm_num, by
    rw [← pow_mul, mul_comm, pow_mul, ζ120_prim.pow_eq_one, one_pow]⟩

theorem wJ_eq (j : ℕ) : wJ j = (tC - ζ120 ^ j) / tC := by
  rw [wJ, sub_div, div_self tC_ne_zero]

theorem wJ_ne_zero (j : ℕ) : wJ j ≠ 0 := by
  rw [wJ_eq]
  exact div_ne_zero (tC_sub_root_ne_zero (isOfFinOrder_ζ120_pow j)) tC_ne_zero

/-- `f` is a multiplicative relation among the `w_j`, `j ∈ J`: the product `∏ w_j^(f j)` is a
root of unity. -/
def IsRelJ (J : Finset ℕ) (f : ℕ → ℤ) : Prop :=
  ∃ ξ : ℂ, IsOfFinOrder ξ ∧ ∏ j ∈ J, wJ j ^ f j = ξ

theorem isOfFinOrder_mul' {a b : ℂ} (ha : IsOfFinOrder a) (hb : IsOfFinOrder b) :
    IsOfFinOrder (a * b) :=
  isOfFinOrder_iff_pow_eq_one.2 ⟨orderOf a * orderOf b,
    Nat.mul_pos ha.orderOf_pos hb.orderOf_pos, by
    rw [mul_pow, pow_mul, pow_orderOf_eq_one, one_pow, one_mul, mul_comm (orderOf a), pow_mul,
      pow_orderOf_eq_one, one_pow]⟩

theorem isOfFinOrder_zpow' {a : ℂ} (ha : IsOfFinOrder a) (c : ℤ) : IsOfFinOrder (a ^ c) :=
  isOfFinOrder_iff_pow_eq_one.2 ⟨orderOf a, ha.orderOf_pos, by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
      one_zpow]⟩

theorem IsRelJ.add {J : Finset ℕ} {f g : ℕ → ℤ} (hf : IsRelJ J f) (hg : IsRelJ J g) :
    IsRelJ J (fun j => f j + g j) := by
  obtain ⟨ξ, hξ, h1⟩ := hf
  obtain ⟨η, hη, h2⟩ := hg
  refine ⟨ξ * η, isOfFinOrder_mul' hξ hη, ?_⟩
  rw [← h1, ← h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => zpow_add₀ (wJ_ne_zero j) _ _

theorem IsRelJ.zsmul {J : Finset ℕ} {f : ℕ → ℤ} (hf : IsRelJ J f) (c : ℤ) :
    IsRelJ J (fun j => c * f j) := by
  obtain ⟨ξ, hξ, h1⟩ := hf
  refine ⟨ξ ^ c, isOfFinOrder_zpow' hξ c, ?_⟩
  rw [← h1, ← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun j _ => by
    show wJ j ^ (c * f j) = (wJ j ^ f j) ^ c
    rw [mul_comm, zpow_mul]

theorem IsRelJ.congr {J : Finset ℕ} {f g : ℕ → ℤ} (hf : IsRelJ J f)
    (h : ∀ j ∈ J, f j = g j) : IsRelJ J g := by
  obtain ⟨ξ, hξ, h1⟩ := hf
  refine ⟨ξ, hξ, ?_⟩
  rw [← h1]
  exact Finset.prod_congr rfl fun j hj => by rw [h j hj]

/-- A relation that vanishes outside `J'` is a relation on `J'`. -/
theorem IsRelJ.restrict {J J' : Finset ℕ} {f : ℕ → ℤ} (hf : IsRelJ J f) (hsub : J' ⊆ J)
    (hzero : ∀ j ∈ J, j ∉ J' → f j = 0) : IsRelJ J' f := by
  obtain ⟨ξ, hξ, h1⟩ := hf
  refine ⟨ξ, hξ, ?_⟩
  rw [← h1]
  exact Finset.prod_subset hsub fun j hj hnj => by rw [hzero j hj hnj, zpow_zero]

open Classical in
/-- The exponent `j < 120` of a 120th root of unity `ζ^j`. -/
noncomputable def idx (r : ℂ) : ℕ :=
  if h : ∃ j < 120, ζ120 ^ j = r then Classical.choose h else 0

theorem idx_pow {j : ℕ} (hj : j < 120) : idx (ζ120 ^ j) = j := by
  have h : ∃ k < 120, ζ120 ^ k = ζ120 ^ j := ⟨j, hj, rfl⟩
  have e : idx (ζ120 ^ j) = Classical.choose h := by simp only [idx, h, ↓reduceDIte]
  rw [e]
  exact ζ120_prim.pow_inj (Classical.choose_spec h).1 hj (Classical.choose_spec h).2

/-- An indexed relation is a relation in the sense of `Support.lean`. -/
theorem isRelation_of_isRelJ {J : Finset ℕ} (hJ : ∀ j ∈ J, j < 120) {f : ℕ → ℤ}
    (h : IsRelJ J f) : IsRelation (J.image fun j => ζ120 ^ j) (fun r => f (idx r)) := by
  obtain ⟨ξ, hξ, h1⟩ := h
  refine ⟨ξ, hξ, ?_⟩
  rw [Finset.prod_image (fun i hi j hj hij => ζ120_prim.pow_inj (hJ i hi) (hJ j hj) hij), ← h1]
  exact Finset.prod_congr rfl fun j hj => by
    show (1 - ζ120 ^ j / tC) ^ f (idx (ζ120 ^ j)) = wJ j ^ f j
    rw [idx_pow (hJ j hj)]
    rfl

/-- **The private prime**, for indexed relations. -/
theorem coeff_eq_zero_of_private_J {P : Ideal Aint} [P.IsPrime] {J : Finset ℕ}
    (hJ : ∀ j ∈ J, j < 120) {f : ℕ → ℤ} (h : IsRelJ J f) {j₀ : ℕ} (hj₀ : j₀ ∈ J)
    (ht : ¬ InP P tC) (h0 : InP P (tC - ζ120 ^ j₀))
    (hpriv : ∀ j ∈ J, j ≠ j₀ → ¬ InP P (tC - ζ120 ^ j)) : f j₀ = 0 := by
  have hrel := isRelation_of_isRelJ hJ h
  have key := coeff_eq_zero_of_private_ideal (P := P) (S := J.image fun j => ζ120 ^ j)
    (fun r hr => by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hr
      exact isOfFinOrder_ζ120_pow j) hrel (Finset.mem_image_of_mem _ hj₀) ht h0
    (fun r hr hne => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hr
      exact hpriv j hj (fun e => hne (by rw [e])))
  simp only [idx_pow (hJ j₀ hj₀)] at key
  exact key

/-! ## 2. Galois conjugates of a relation, and absolute values -/

theorem I_pow_of_mod_four {a : ℕ} (ha : a % 4 = 1) : I ^ a = I := by
  obtain ⟨q, rfl⟩ : ∃ q, a = 4 * q + 1 := ⟨a / 4, by omega⟩
  rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul, pow_one]

/-- **Galois conjugation.** If `f` is a relation among the `w_j` and `a` is prime to 120 with
`a ≡ 1 (mod 4)`, then `f` is also a relation among the `w_{aj}`. -/
theorem isRelJ_conj {J : Finset ℕ} {f : ℕ → ℤ} (h : IsRelJ J f) {a : ℕ}
    (ha : Nat.Coprime a 120) (ha4 : a % 4 = 1) :
    ∃ ξ : ℂ, IsOfFinOrder ξ ∧ ∏ j ∈ J, wJ (a * j) ^ f j = ξ := by
  obtain ⟨ξ, hξ, hprod⟩ := h
  have hint : IsIntegral ℚ ζ120 := (ζ120_prim.isIntegral (by norm_num)).tower_top
  have hmin : minpoly ℚ ζ120 = cyclotomic 120 ℚ :=
    (cyclotomic_eq_minpoly_rat ζ120_prim (by norm_num)).symm
  have hroot : ζ120 ^ a ∈ (minpoly ℚ ζ120).aroots ℂ := by
    rw [mem_aroots, hmin]
    refine ⟨cyclotomic_ne_zero 120 ℚ, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (ζ120_prim.pow_of_coprime a ha).isRoot_cyclotomic (by norm_num)
  -- the embedding `ζ ↦ ζ^a` of `ℚ(ζ)`
  let σ : ℚ⟮ζ120⟯ →ₐ[ℚ] ℂ :=
    (algHomAdjoinIntegralEquiv ℚ hint).symm ⟨ζ120 ^ a, hroot⟩
  let ι : ℚ⟮ζ120⟯ →+* ℂ := algebraMap ℚ⟮ζ120⟯ ℂ
  let g : ℚ⟮ζ120⟯ := AdjoinSimple.gen ℚ ζ120
  have hσ : σ g = ζ120 ^ a := algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hint _
  have hι : ι g = ζ120 := AdjoinSimple.algebraMap_gen ℚ ζ120
  -- the relation inside `ℚ(ζ)`
  let w' : ℕ → ℚ⟮ζ120⟯ := fun j => 1 - g ^ j / (1 + g ^ 30)
  have hw' : ∀ j, ι (w' j) = wJ j := by
    intro j
    simp only [w', map_sub, map_one, map_div₀, map_pow, map_add, hι, ζ120_pow_30]
    rfl
  have h30 : (ζ120 ^ a) ^ 30 = I := by
    rw [← pow_mul, mul_comm, pow_mul, ζ120_pow_30, I_pow_of_mod_four ha4]
  have hσw : ∀ j, σ (w' j) = wJ (a * j) := by
    intro j
    simp only [w', map_sub, map_one, map_div₀, map_pow, map_add, hσ, h30]
    rw [← pow_mul]
    rfl
  let ξ' : ℚ⟮ζ120⟯ := ∏ j ∈ J, w' j ^ f j
  have hιξ : ι ξ' = ξ := by
    rw [← hprod]
    simp only [ξ', map_prod]
    exact Finset.prod_congr rfl fun j _ => by rw [map_zpow₀, hw']
  have hn : ξ' ^ orderOf ξ = 1 := by
    apply ι.injective
    rw [map_pow, hιξ, pow_orderOf_eq_one, map_one]
  refine ⟨σ ξ', isOfFinOrder_iff_pow_eq_one.2 ⟨orderOf ξ, hξ.orderOf_pos, by
    rw [← map_pow, hn, map_one]⟩, ?_⟩
  simp only [ξ', map_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [map_zpow₀, hσw]

/-- `log |w_j|`. -/
noncomputable def ell (j : ℕ) : ℝ := Real.log ‖wJ j‖

/-- **The archimedean equations.** A relation `f` satisfies `∑ f j · log |w_{aj}| = 0` for
every `a` prime to 120 with `a ≡ 1 (mod 4)`. -/
theorem sum_ell_eq_zero {J : Finset ℕ} {f : ℕ → ℤ} (h : IsRelJ J f) {a : ℕ}
    (ha : Nat.Coprime a 120) (ha4 : a % 4 = 1) : ∑ j ∈ J, (f j : ℝ) * ell (a * j) = 0 := by
  obtain ⟨ξ, hξ, hprod⟩ := isRelJ_conj h ha ha4
  have h1 := congrArg (fun z : ℂ => Real.log ‖z‖) hprod
  simp only [norm_prod, norm_zpow, norm_root hξ, Real.log_one] at h1
  rw [Real.log_prod (fun j _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (wJ_ne_zero _)))] at h1
  rw [← h1]
  exact Finset.sum_congr rfl fun j _ => by rw [Real.log_zpow, ell]

theorem ζ120_pow_mod (j : ℕ) : ζ120 ^ (j % 120) = ζ120 ^ j := by
  have h := pow_mod_orderOf ζ120 j
  rwa [← ζ120_prim.eq_orderOf] at h

theorem ell_mod (j : ℕ) : ell j = ell (j % 120) := by
  rw [ell, ell, wJ, wJ, ζ120_pow_mod]

/-! ## 3. The sizes `|t - ζ^j|²` -/

/-- `|t - ζ^j|²`. -/
noncomputable def nsq (j : ℕ) : ℝ := Complex.normSq (tC - ζ120 ^ j)

theorem ζ120_pow_eq (j : ℕ) : ζ120 ^ j = Complex.exp ((Real.pi * j / 60 : ℝ) * I) := by
  rw [ζ120, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem nsq_pos (j : ℕ) : 0 < nsq j :=
  Complex.normSq_pos.2 (tC_sub_root_ne_zero (isOfFinOrder_ζ120_pow j))

/-- `|t - e^(iθ)|² = 3 - 2 cos θ - 2 sin θ`. -/
theorem nsq_eq (j : ℕ) :
    nsq j = 3 - 2 * Real.cos (Real.pi * j / 60) - 2 * Real.sin (Real.pi * j / 60) := by
  have h := Real.cos_sq_add_sin_sq (Real.pi * j / 60)
  rw [nsq, ζ120_pow_eq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp only [tC, Complex.add_re, Complex.one_re, Complex.I_re, Complex.add_im, Complex.one_im,
    Complex.I_im]
  linear_combination h

theorem two_mul_ell (j : ℕ) : 2 * ell j = Real.log (nsq j) - Real.log 2 := by
  have hn : Real.log (nsq j) = 2 * Real.log ‖tC - ζ120 ^ j‖ := by
    rw [nsq, ← Complex.sq_norm, Real.log_pow]; norm_num
  have ht : Real.log 2 = 2 * Real.log ‖tC‖ := by
    have h2 : Complex.normSq tC = 2 := by
      simp only [tC, Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.I_re,
        Complex.add_im, Complex.one_im, Complex.I_im]
      norm_num
    have h3 := Real.log_pow ‖tC‖ 2
    rw [Complex.sq_norm, h2] at h3
    rw [h3]; norm_num
  rw [ell, wJ_eq, norm_div, Real.log_div
    (norm_ne_zero_iff.2 (tC_sub_root_ne_zero (isOfFinOrder_ζ120_pow j)))
    (norm_ne_zero_iff.2 tC_ne_zero), hn, ht]
  ring

theorem ell_eq_of_nsq_eq {j k : ℕ} (h : nsq j = nsq k) : ell j = ell k := by
  have h1 := two_mul_ell j
  have h2 := two_mul_ell k
  rw [h] at h1
  linarith

theorem ell_ne_of_nsq_ne {j k : ℕ} (h : nsq j ≠ nsq k) : ell j ≠ ell k := by
  intro he
  have h1 := two_mul_ell j
  have h2 := two_mul_ell k
  rw [he] at h1
  exact h (Real.log_injOn_pos (Set.mem_Ioi.2 (nsq_pos j)) (Set.mem_Ioi.2 (nsq_pos k))
    (by linarith))

theorem angle_pos {j : ℕ} (hj : 0 < j) : 0 < Real.pi * j / 60 :=
  div_pos (mul_pos Real.pi_pos (by exact_mod_cast hj)) (by norm_num)

theorem angle_lt {j : ℕ} {c : ℝ} (hj : (j : ℝ) < c) :
    Real.pi * j / 60 < Real.pi * c / 60 := by
  have := mul_lt_mul_of_pos_left hj Real.pi_pos
  linarith

theorem nsq_add_sixty (j : ℕ) : nsq (j + 60) =
    3 + 2 * Real.cos (Real.pi * j / 60) + 2 * Real.sin (Real.pi * j / 60) := by
  rw [nsq_eq, show Real.pi * ((j + 60 : ℕ) : ℝ) / 60 = Real.pi * j / 60 + Real.pi by
    push_cast; ring, Real.cos_add_pi, Real.sin_add_pi]
  ring

/-- `|t - r| ≠ |t + r|` for `r` in the open first quadrant. -/
theorem nsq_ne_add_sixty {j : ℕ} (hj : 0 < j) (hj' : j < 30) : nsq j ≠ nsq (j + 60) := by
  have h0 := angle_pos hj
  have h1 := angle_lt (c := 30) (by exact_mod_cast hj')
  have hpi := Real.pi_pos
  have hc := Real.cos_pos_of_mem_Ioo (x := Real.pi * j / 60) ⟨by linarith, by linarith⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  rw [nsq_add_sixty, nsq_eq]
  intro h
  linarith

theorem nsq_conj {j k : ℕ} (h : j + k = 120) : nsq k =
    3 - 2 * Real.cos (Real.pi * j / 60) + 2 * Real.sin (Real.pi * j / 60) := by
  have hk : (k : ℝ) = 120 - j := by
    have h' : ((j + k : ℕ) : ℝ) = 120 := by rw [h]; norm_num
    push_cast at h'; linarith
  rw [nsq_eq, show Real.pi * (k : ℝ) / 60 = 2 * Real.pi - Real.pi * j / 60 by rw [hk]; ring,
    Real.cos_two_pi_sub, Real.sin_two_pi_sub]
  ring

/-- `|t - r| ≠ |t - conj r|` for `r` in the open upper half plane. -/
theorem nsq_ne_conj {j k : ℕ} (h : j + k = 120) (hj : 0 < j) (hj' : j < 60) :
    nsq j ≠ nsq k := by
  have h0 := angle_pos hj
  have h1 := angle_lt (c := 60) (by exact_mod_cast hj')
  have hs := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  rw [nsq_conj h, nsq_eq]
  intro e
  linarith

theorem nsq_mul_conj {j k : ℕ} (h : j + k = 120) : nsq j * nsq k =
    5 - 12 * Real.cos (Real.pi * j / 60) + 8 * Real.cos (Real.pi * j / 60) ^ 2 := by
  have hcs := Real.cos_sq_add_sin_sq (Real.pi * j / 60)
  rw [nsq_conj h, nsq_eq]
  linear_combination (-4) * hcs

/-- `|t - r|² |t - conj r|²` differs for `r = e^(iπ/5)` and `r = e^(3iπ/5)` (the values are
`5 - 2√5` and `5 + 2√5`). -/
theorem nsq_prod_ne : nsq 12 * nsq 108 ≠ nsq 36 * nsq 84 := by
  rw [nsq_mul_conj (show 12 + 108 = 120 by norm_num),
    nsq_mul_conj (show 36 + 84 = 120 by norm_num)]
  have hpi := Real.pi_pos
  have h1 : 0 < Real.cos (Real.pi * ((12 : ℕ) : ℝ) / 60) :=
    Real.cos_pos_of_mem_Ioo ⟨by push_cast; linarith, by push_cast; linarith⟩
  have h2 : Real.cos (Real.pi * ((36 : ℕ) : ℝ) / 60) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by push_cast; linarith) (by push_cast; linarith)
  have h3 := Real.cos_le_one (Real.pi * ((12 : ℕ) : ℝ) / 60)
  intro e
  have hp := mul_pos (sub_pos.2 (h2.trans h1))
    (show 0 < 12 - 8 * (Real.cos (Real.pi * ((12 : ℕ) : ℝ) / 60) +
      Real.cos (Real.pi * ((36 : ℕ) : ℝ) / 60)) by linarith)
  nlinarith [hp]

/-- `|t - i conj r| = |t - r|`: the partner has the same size. -/
theorem nsq_partner {j k : ℕ} (h : j + k = 30 ∨ j + k = 150) : nsq k = nsq j := by
  rw [nsq_eq, nsq_eq]
  rcases h with h | h
  · have hk : (k : ℝ) = 30 - j := by
      have h' : ((j + k : ℕ) : ℝ) = 30 := by rw [h]; norm_num
      push_cast at h'; linarith
    rw [show Real.pi * (k : ℝ) / 60 = Real.pi / 2 - Real.pi * j / 60 by rw [hk]; ring,
      Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    ring
  · have hk : (k : ℝ) = 150 - j := by
      have h' : ((j + k : ℕ) : ℝ) = 150 := by rw [h]; norm_num
      push_cast at h'; linarith
    rw [show Real.pi * (k : ℝ) / 60 = Real.pi / 2 - Real.pi * j / 60 + 2 * Real.pi by
      rw [hk]; ring, Real.cos_add_two_pi, Real.sin_add_two_pi, Real.cos_pi_div_two_sub,
      Real.sin_pi_div_two_sub]
    ring

theorem ell_thirty_ne_zero : ell 30 ≠ 0 := by
  have h := two_mul_ell 30
  have hn : nsq 30 = 1 := by
    rw [nsq, ζ120_pow_30, tC, add_sub_cancel_right, map_one]
  rw [hn, Real.log_one] at h
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  intro e
  rw [e] at h
  linarith

/- From here on `nsq` is opaque: otherwise elaborating `nsq_pos 108 : 0 < nsq 108` makes Lean
evaluate `ζ^108` by unfolding the power. -/
attribute [irreducible] nsq

theorem ell_sum_ne : ell 12 + ell 108 ≠ ell 36 + ell 84 := by
  intro e
  have h12 := two_mul_ell 12
  have h108 := two_mul_ell 108
  have h36 := two_mul_ell 36
  have h84 := two_mul_ell 84
  have hlog : Real.log (nsq 12 * nsq 108) = Real.log (nsq 36 * nsq 84) := by
    rw [Real.log_mul (nsq_pos 12).ne' (nsq_pos 108).ne',
      Real.log_mul (nsq_pos 36).ne' (nsq_pos 84).ne']
    linarith
  exact nsq_prod_ne (Real.log_injOn_pos (Set.mem_Ioi.2 (mul_pos (nsq_pos 12) (nsq_pos 108)))
    (Set.mem_Ioi.2 (mul_pos (nsq_pos 36) (nsq_pos 84))) hlog)

/-! ## 4. Prime ideals for the last four roots -/

theorem isIntegral_I : IsIntegral ℤ I := isIntegral_of_finOrder isOfFinOrder_I

theorem ζ120_ne_zero : ζ120 ≠ 0 := by
  have h := ne_zero_of_finOrder (isOfFinOrder_ζ120_pow 1)
  rwa [pow_one] at h

theorem inP_two_of_tC {P : Ideal Aint} (h : InP P tC) : InP P ((2 : ℕ) : ℂ) := by
  have h1 := h.mul_right (isIntegral_one.sub isIntegral_I)
  rw [tC_mul_conj] at h1
  rw [Nat.cast_ofNat]
  exact h1

/-- If `r² = -i` (`r = ±ζ_8^3`), a prime containing `t - r` contains 3. -/
theorem inP_three_of_sq {P : Ideal Aint} {r : ℂ} (hr : IsOfFinOrder r) (h2 : r ^ 2 = -I)
    (h : InP P (tC - r)) : InP P ((3 : ℕ) : ℂ) := by
  have hint : IsIntegral ℤ ((tC + r) * -I) :=
    (isIntegral_tC.add (isIntegral_of_finOrder hr)).mul isIntegral_I.neg
  have h1 := h.mul_right hint
  have e : (tC - r) * ((tC + r) * -I) = ((3 : ℕ) : ℂ) := by
    push_cast
    linear_combination (-I) * tC_sq + I * h2 - 3 * Complex.I_sq
  rw [e] at h1
  exact h1

theorem ζ120_pow_45_sq : (ζ120 ^ 45) ^ 2 = -I := by
  rw [← pow_mul]; exact ζ120_pow_90

theorem ζ120_pow_105_sq : (ζ120 ^ 105) ^ 2 = -I := by
  rw [← pow_mul, show 105 * 2 = 120 + 90 by norm_num, pow_add, ζ120_prim.pow_eq_one, one_mul,
    ζ120_pow_90]

theorem ζ120_pow_105 : ζ120 ^ 105 = -ζ120 ^ 45 := by
  rw [show 105 = 60 + 45 by norm_num, pow_add, ζ120_pow_60, neg_one_mul]

theorem inP_five_of_60 {P : Ideal Aint} (h : InP P (tC - ζ120 ^ 60)) :
    InP P ((5 : ℕ) : ℂ) := by
  have h1 := h.mul_right ((isIntegral_intCast 2).sub isIntegral_I)
  have e : (tC - ζ120 ^ 60) * (((2 : ℤ) : ℂ) - I) = ((5 : ℕ) : ℂ) := by
    rw [ζ120_pow_60, tC]
    push_cast
    linear_combination (-1) * Complex.I_sq
  rw [e] at h1
  exact h1

theorem inP_five_of_90 {P : Ideal Aint} (h : InP P (tC - ζ120 ^ 90)) :
    InP P ((5 : ℕ) : ℂ) := by
  have h1 := h.mul_right ((isIntegral_intCast 1).sub ((isIntegral_intCast 2).mul isIntegral_I))
  have e : (tC - ζ120 ^ 90) * (((1 : ℤ) : ℂ) - ((2 : ℤ) : ℂ) * I) = ((5 : ℕ) : ℂ) := by
    rw [ζ120_pow_90, tC]
    push_cast
    linear_combination (-4) * Complex.I_sq
  rw [e] at h1
  exact h1

theorem not_inP_30 {P : Ideal Aint} [P.IsPrime] : ¬ InP P (tC - ζ120 ^ 30) := by
  rw [ζ120_pow_30, tC, add_sub_cancel_right]
  exact not_inP_one

theorem not_inP_45_105 {P : Ideal Aint} [P.IsPrime] (h1 : InP P (tC - ζ120 ^ 45))
    (h2 : InP P (tC - ζ120 ^ 105)) : False := by
  have h3 := inP_three_of_sq (isOfFinOrder_ζ120_pow 45) ζ120_pow_45_sq h1
  have hs := (h1.add h2).mul_right (isIntegral_one.sub isIntegral_I)
  have e : ((tC - ζ120 ^ 45) + (tC - ζ120 ^ 105)) * (1 - I) = ((4 : ℕ) : ℂ) := by
    rw [ζ120_pow_105]
    push_cast
    linear_combination 2 * tC_mul_conj
  rw [e] at hs
  exact not_inP_coprime (by norm_num) h3 hs

theorem not_inP_60_90 {P : Ideal Aint} [P.IsPrime] (h1 : InP P (tC - ζ120 ^ 60))
    (h2 : InP P (tC - ζ120 ^ 90)) : False := by
  have h5 := inP_five_of_60 h1
  have hs := h2.sub (h1.mul_left isIntegral_I)
  have e : (tC - ζ120 ^ 90) - I * (tC - ζ120 ^ 60) = ((2 : ℕ) : ℂ) := by
    rw [ζ120_pow_90, ζ120_pow_60, tC]
    push_cast
    linear_combination (-1) * Complex.I_sq
  rw [e] at hs
  exact not_inP_coprime (by norm_num) hs h5

theorem exists_prime_45 : ∃ P : Ideal Aint, P.IsPrime ∧ InP P (tC - ζ120 ^ 45) := by
  have hr : ζ120 ^ 45 ∈ selfOrb 0 true := by
    rw [selfOrb_true_eq, mem_roots_cycPoly (by norm_num) (pow_ne_zero _ ζ120_ne_zero)
      two_ne_zero]
    have e : ζ120 ^ 30 * (ζ120 ^ 45) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_add]; exact ζ120_prim.pow_eq_one
    rw [e]
    exact IsPrimitiveRoot.one
  obtain ⟨P, hP, -, -, -, -, -, h⟩ := hasGoodPrime_selfOrb_of_dvd 0 true Nat.prime_three
    (by decide) (by decide) (by norm_num [cyclotomic_one]) hr
  exact ⟨P, hP, h⟩

theorem exists_prime_105 : ∃ P : Ideal Aint, P.IsPrime ∧ InP P (tC - ζ120 ^ 105) := by
  have hr : ζ120 ^ 105 ∈ selfOrb 0 true := by
    rw [selfOrb_true_eq, mem_roots_cycPoly (by norm_num) (pow_ne_zero _ ζ120_ne_zero)
      two_ne_zero]
    have e : ζ120 ^ 30 * (ζ120 ^ 105) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_add, show 30 + 105 * 2 = 120 * 2 by norm_num, pow_mul,
        ζ120_prim.pow_eq_one, one_pow]
    rw [e]
    exact IsPrimitiveRoot.one
  obtain ⟨P, hP, -, -, -, -, -, h⟩ := hasGoodPrime_selfOrb_of_dvd 0 true Nat.prime_three
    (by decide) (by decide) (by norm_num [cyclotomic_one]) hr
  exact ⟨P, hP, h⟩

theorem exists_prime_60 : ∃ P : Ideal Aint, P.IsPrime ∧ InP P (tC - ζ120 ^ 60) := by
  have hr : ζ120 ^ 60 ∈ orbit (.Q 0) := by
    rw [orbit_Q_eq, mem_roots_cycPoly (by norm_num) (pow_ne_zero _ ζ120_ne_zero) one_ne_zero]
    have e : ζ120 ^ 60 * (ζ120 ^ 60) ^ 1 = 1 := by
      rw [pow_one, ← pow_add]; exact ζ120_prim.pow_eq_one
    rw [e]
    exact IsPrimitiveRoot.one
  obtain ⟨P, hP, -, -, -, -, -, h⟩ := hasGoodPrime_orbit_of_prime (.Q 0) (p := 5)
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by rw [atom_Q0]; decide) hr
  exact ⟨P, hP, h⟩

theorem exists_prime_90 : ∃ P : Ideal Aint, P.IsPrime ∧ InP P (tC - ζ120 ^ 90) := by
  have hr : ζ120 ^ 90 ∈ partner (orbit (.Q 0)) := by
    rw [partner_Q_eq, mem_roots_cycPoly (by norm_num) (pow_ne_zero _ ζ120_ne_zero)
      one_ne_zero]
    have e : ζ120 ^ 30 * (ζ120 ^ 90) ^ 1 = 1 := by
      rw [pow_one, ← pow_add]; exact ζ120_prim.pow_eq_one
    rw [e]
    exact IsPrimitiveRoot.one
  obtain ⟨P, hP, -, -, -, -, -, h⟩ := hasGoodPrime_partner_of_prime (.Q 0) (p := 5)
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by rw [atom_Q0]; decide) hr
  exact ⟨P, hP, h⟩

/-! ## 5. The 11 basis roots are independent -/

/-- The exponents of the 11 basis roots: `i`, `ζ_8`, `ζ_6`, `ζ_8^3`, `ζ_8^7`, `ζ_24`, `-1`,
`-i` and three roots of order 10. -/
def B11 : Finset ℕ := {30, 15, 20, 45, 105, 5, 60, 90, 12, 36, 84}

/-- The four roots handled by private primes, and `i`. -/
def S5 : Finset ℕ := {30, 45, 105, 60, 90}

theorem sum_B11 (g : ℕ → ℝ) : ∑ j ∈ B11, g j =
    g 30 + g 15 + g 20 + g 45 + g 105 + g 5 + g 60 + g 90 + g 12 + g 36 + g 84 := by
  simp [B11]
  ring

/-- The archimedean equation of a relation on `B11`, written out. -/
theorem arch_B11 {f : ℕ → ℤ} (h : IsRelJ B11 f) {a : ℕ} (ha : Nat.Coprime a 120)
    (ha4 : a % 4 = 1) :
    (f 30 : ℝ) * ell (a * 30 % 120) + f 15 * ell (a * 15 % 120) + f 20 * ell (a * 20 % 120)
      + f 45 * ell (a * 45 % 120) + f 105 * ell (a * 105 % 120) + f 5 * ell (a * 5 % 120)
      + f 60 * ell (a * 60 % 120) + f 90 * ell (a * 90 % 120) + f 12 * ell (a * 12 % 120)
      + f 36 * ell (a * 36 % 120) + f 84 * ell (a * 84 % 120) = 0 := by
  have h1 := sum_ell_eq_zero h ha ha4
  rw [sum_B11] at h1
  rw [← h1]
  simp only [← ell_mod]

theorem cast_eq_zero_of_mul {x : ℤ} {c : ℝ} (hc : c ≠ 0) (h : (x : ℝ) * c = 0) : x = 0 := by
  rcases mul_eq_zero.1 h with h | h
  · exact_mod_cast h
  · exact absurd h hc

theorem ell_105 : ell 105 = ell 45 :=
  ell_eq_of_nsq_eq (nsq_partner (j := 45) (k := 105) (Or.inr (by norm_num)))

theorem ell_25 : ell 25 = ell 5 :=
  ell_eq_of_nsq_eq (nsq_partner (j := 5) (k := 25) (Or.inl (by norm_num)))

theorem ell_85 : ell 85 = ell 65 :=
  ell_eq_of_nsq_eq (nsq_partner (j := 65) (k := 85) (Or.inr (by norm_num)))

/-- The roots of order 24, 6 and 8 that carry the units of `ℚ(ζ_24)`: their coefficients
vanish, by conjugation with `a ≡ 1 (mod 20)`. -/
theorem basis_units {f : ℕ → ℤ} (h : IsRelJ B11 f) : f 5 = 0 ∧ f 20 = 0 ∧ f 15 = 0 := by
  have h1 := arch_B11 h (a := 1) (by norm_num) (by norm_num)
  have h41 := arch_B11 h (a := 41) (by norm_num) (by norm_num)
  have h61 := arch_B11 h (a := 61) (by norm_num) (by norm_num)
  have h101 := arch_B11 h (a := 101) (by norm_num) (by norm_num)
  simp only [Nat.reduceMul, Nat.reduceMod] at h1 h41 h61 h101
  rw [ell_105] at h1 h41 h61 h101
  rw [ell_25] at h101
  rw [ell_85] at h41
  have hZ : (f 5 : ℝ) * (ell 5 - ell 65) = 0 := by
    linear_combination (1 / 2 : ℝ) * h1 - (1 / 2 : ℝ) * h41 - (1 / 2 : ℝ) * h61
      + (1 / 2 : ℝ) * h101
  have hY : (f 20 : ℝ) * (ell 20 - ell 100) = 0 := by
    linear_combination (1 / 2 : ℝ) * h1 - (1 / 2 : ℝ) * h41 + (1 / 2 : ℝ) * h61
      - (1 / 2 : ℝ) * h101
  have hX : (f 15 : ℝ) * (ell 15 - ell 75) = 0 := by
    linear_combination (1 / 2 : ℝ) * h1 + (1 / 2 : ℝ) * h41 - (1 / 2 : ℝ) * h61
      - (1 / 2 : ℝ) * h101
  refine ⟨?_, ?_, ?_⟩
  · exact cast_eq_zero_of_mul (sub_ne_zero.2 (ell_ne_of_nsq_ne
      (nsq_ne_add_sixty (j := 5) (by norm_num) (by norm_num)))) hZ
  · exact cast_eq_zero_of_mul (sub_ne_zero.2 (ell_ne_of_nsq_ne
      (nsq_ne_conj (j := 20) (k := 100) (by norm_num) (by norm_num) (by norm_num)))) hY
  · exact cast_eq_zero_of_mul (sub_ne_zero.2 (ell_ne_of_nsq_ne
      (nsq_ne_add_sixty (j := 15) (by norm_num) (by norm_num)))) hX

/-- Pure algebra for the roots of order 10: a circulant system. -/
theorem circulant_zero {p q s d0 d1 D : ℝ} (hd0 : d0 ≠ 0) (hD : D ≠ 0)
    (hA : p * d0 + (q - s) * d1 = 0) (hB : p * d1 - (q - s) * d0 = 0)
    (hC : (p - q - s) * D = 0) : p = 0 ∧ q = 0 ∧ s = 0 := by
  have hsq : (p ^ 2 + (q - s) ^ 2) * d0 = 0 := by
    linear_combination p * hA - (q - s) * hB
  have hsq0 : p ^ 2 + (q - s) ^ 2 = 0 := by
    rcases mul_eq_zero.1 hsq with h | h
    · exact h
    · exact absurd h hd0
  have h2 := (add_eq_zero_iff_of_nonneg (sq_nonneg p) (sq_nonneg (q - s))).1 hsq0
  have hp : p = 0 := (pow_eq_zero_iff two_ne_zero).1 h2.1
  have hqs : q - s = 0 := (pow_eq_zero_iff two_ne_zero).1 h2.2
  have hpqs : p - q - s = 0 := by
    rcases mul_eq_zero.1 hC with h | h
    · exact h
    · exact absurd h hD
  refine ⟨hp, ?_, ?_⟩
  · linear_combination (1 / 2 : ℝ) * hqs - (1 / 2 : ℝ) * hpqs + (1 / 2 : ℝ) * hp
  · linear_combination (-1 / 2 : ℝ) * hqs - (1 / 2 : ℝ) * hpqs + (1 / 2 : ℝ) * hp

/-- The three roots of order 10: their coefficients vanish, by conjugation with
`a ≡ 1 (mod 24)`, which permutes the four roots of order 10 cyclically. -/
theorem basis_tens {f : ℕ → ℤ} (h : IsRelJ B11 f) : f 12 = 0 ∧ f 36 = 0 ∧ f 84 = 0 := by
  have h1 := arch_B11 h (a := 1) (by norm_num) (by norm_num)
  have h73 := arch_B11 h (a := 73) (by norm_num) (by norm_num)
  have h49 := arch_B11 h (a := 49) (by norm_num) (by norm_num)
  have h97 := arch_B11 h (a := 97) (by norm_num) (by norm_num)
  simp only [Nat.reduceMul, Nat.reduceMod] at h1 h73 h49 h97
  have hA : (f 12 : ℝ) * (ell 12 - ell 108) + ((f 36 : ℝ) - f 84) * (ell 36 - ell 84) = 0 := by
    linear_combination h1 - h49
  have hB : (f 12 : ℝ) * (ell 36 - ell 84) - ((f 36 : ℝ) - f 84) * (ell 12 - ell 108) = 0 := by
    linear_combination h73 - h97
  have hC : ((f 12 : ℝ) - f 36 - f 84) * (ell 12 + ell 108 - (ell 36 + ell 84)) = 0 := by
    linear_combination h1 - h73 + h49 - h97
  have hd0 : ell 12 - ell 108 ≠ 0 := sub_ne_zero.2 (ell_ne_of_nsq_ne
    (nsq_ne_conj (j := 12) (k := 108) (by norm_num) (by norm_num) (by norm_num)))
  obtain ⟨hp, hq, hs⟩ := circulant_zero hd0 (sub_ne_zero.2 ell_sum_ne) hA hB hC
  exact ⟨by exact_mod_cast hp, by exact_mod_cast hq, by exact_mod_cast hs⟩

theorem S5_lt : ∀ j ∈ S5, j < 120 := by decide

theorem private_45 {f : ℕ → ℤ} (h : IsRelJ S5 f) : f 45 = 0 := by
  obtain ⟨P, hP, h45⟩ := exists_prime_45
  have h3 := inP_three_of_sq (isOfFinOrder_ζ120_pow 45) ζ120_pow_45_sq h45
  refine coeff_eq_zero_of_private_J S5_lt h (j₀ := 45) (by decide)
    (fun ht => not_inP_coprime (by norm_num) (inP_two_of_tC ht) h3) h45 ?_
  intro j hj hne hin
  simp only [S5, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact not_inP_30 hin
  · exact hne rfl
  · exact not_inP_45_105 h45 hin
  · exact not_inP_coprime (by norm_num) h3 (inP_five_of_60 hin)
  · exact not_inP_coprime (by norm_num) h3 (inP_five_of_90 hin)

theorem private_105 {f : ℕ → ℤ} (h : IsRelJ S5 f) : f 105 = 0 := by
  obtain ⟨P, hP, h105⟩ := exists_prime_105
  have h3 := inP_three_of_sq (isOfFinOrder_ζ120_pow 105) ζ120_pow_105_sq h105
  refine coeff_eq_zero_of_private_J S5_lt h (j₀ := 105) (by decide)
    (fun ht => not_inP_coprime (by norm_num) (inP_two_of_tC ht) h3) h105 ?_
  intro j hj hne hin
  simp only [S5, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact not_inP_30 hin
  · exact not_inP_45_105 hin h105
  · exact hne rfl
  · exact not_inP_coprime (by norm_num) h3 (inP_five_of_60 hin)
  · exact not_inP_coprime (by norm_num) h3 (inP_five_of_90 hin)

theorem private_60 {f : ℕ → ℤ} (h : IsRelJ S5 f) : f 60 = 0 := by
  obtain ⟨P, hP, h60⟩ := exists_prime_60
  have h5 := inP_five_of_60 h60
  refine coeff_eq_zero_of_private_J S5_lt h (j₀ := 60) (by decide)
    (fun ht => not_inP_coprime (by norm_num) (inP_two_of_tC ht) h5) h60 ?_
  intro j hj hne hin
  simp only [S5, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact not_inP_30 hin
  · exact not_inP_coprime (by norm_num)
      (inP_three_of_sq (isOfFinOrder_ζ120_pow 45) ζ120_pow_45_sq hin) h5
  · exact not_inP_coprime (by norm_num)
      (inP_three_of_sq (isOfFinOrder_ζ120_pow 105) ζ120_pow_105_sq hin) h5
  · exact hne rfl
  · exact not_inP_60_90 h60 hin

theorem private_90 {f : ℕ → ℤ} (h : IsRelJ S5 f) : f 90 = 0 := by
  obtain ⟨P, hP, h90⟩ := exists_prime_90
  have h5 := inP_five_of_90 h90
  refine coeff_eq_zero_of_private_J S5_lt h (j₀ := 90) (by decide)
    (fun ht => not_inP_coprime (by norm_num) (inP_two_of_tC ht) h5) h90 ?_
  intro j hj hne hin
  simp only [S5, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact not_inP_30 hin
  · exact not_inP_coprime (by norm_num)
      (inP_three_of_sq (isOfFinOrder_ζ120_pow 45) ζ120_pow_45_sq hin) h5
  · exact not_inP_coprime (by norm_num)
      (inP_three_of_sq (isOfFinOrder_ζ120_pow 105) ζ120_pow_105_sq hin) h5
  · exact not_inP_60_90 hin h90
  · exact hne rfl

/-- The last coefficient: `|w_30| = |1/t| ≠ 1`. -/
theorem basis_thirty {f : ℕ → ℤ} (h : IsRelJ B11 f) (h15 : f 15 = 0) (h20 : f 20 = 0)
    (h45 : f 45 = 0) (h105 : f 105 = 0) (h5 : f 5 = 0) (h60 : f 60 = 0) (h90 : f 90 = 0)
    (h12 : f 12 = 0) (h36 : f 36 = 0) (h84 : f 84 = 0) : f 30 = 0 := by
  have h1 := arch_B11 h (a := 1) (by norm_num) (by norm_num)
  simp only [Nat.reduceMul, Nat.reduceMod] at h1
  rw [h15, h20, h45, h105, h5, h60, h90, h12, h36, h84] at h1
  simp only [Int.cast_zero, zero_mul, add_zero] at h1
  exact cast_eq_zero_of_mul ell_thirty_ne_zero h1

/-- **The 11 basis numbers satisfy no relation.** -/
theorem basis_independent {f : ℕ → ℤ} (h : IsRelJ B11 f) : ∀ j ∈ B11, f j = 0 := by
  obtain ⟨hf5, hf20, hf15⟩ := basis_units h
  obtain ⟨hf12, hf36, hf84⟩ := basis_tens h
  have hS5 : IsRelJ S5 f := by
    refine h.restrict (by decide) ?_
    intro j hj hnj
    simp only [B11, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by decide) hnj
    · exact hf15
    · exact hf20
    · exact absurd (by decide) hnj
    · exact absurd (by decide) hnj
    · exact hf5
    · exact absurd (by decide) hnj
    · exact absurd (by decide) hnj
    · exact hf12
    · exact hf36
    · exact hf84
  have hf45 := private_45 hS5
  have hf105 := private_105 hS5
  have hf60 := private_60 hS5
  have hf90 := private_90 hS5
  have hf30 := basis_thirty h hf15 hf20 hf45 hf105 hf5 hf60 hf90 hf12 hf36 hf84
  intro j hj
  simp only [B11, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hf30, hf15, hf20, hf45, hf105, hf5, hf60, hf90, hf12, hf36, hf84]

/-! ## 6. The 13 relations, as exponent vectors -/

theorem prodW_add (J : Finset ℕ) (f g : ℕ → ℤ) :
    ∏ j ∈ J, wJ j ^ (f + g) j = (∏ j ∈ J, wJ j ^ f j) * ∏ j ∈ J, wJ j ^ g j := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => zpow_add₀ (wJ_ne_zero j) _ _

theorem prod_single {J : Finset ℕ} {a : ℕ} (ha : a ∈ J) (c : ℤ) :
    ∏ j ∈ J, wJ j ^ (Pi.single a c : ℕ → ℤ) j = wJ a ^ c := by
  rw [Finset.prod_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, zpow_zero]
  · intro h; exact absurd ha h

theorem aJ_ne (j : ℕ) : tC - ζ120 ^ j ≠ 0 :=
  tC_sub_root_ne_zero (isOfFinOrder_ζ120_pow j)

theorem aJ_zero_ne : tC - 1 ≠ 0 := by
  have h := aJ_ne 0
  rwa [pow_zero] at h

/-- Exponents of relation 1: `-1[0] +1[30]`. -/
def rel1 : ℕ → ℤ := Pi.single 0 (-1) + Pi.single 30 1

theorem rel1_prod : ∏ j ∈ R0Exps, wJ j ^ rel1 j = ζ120 ^ 90 := by
  simp (disch := decide) only [rel1, prodW_add, prod_single]
  simp only [wJ_eq, zpow_neg, zpow_ofNat]
  have ht := tC_ne_zero
  have h0 := aJ_zero_ne
  have h30 := aJ_ne 30
  field_simp
  linear_combination relation_1

theorem rel1_isRel : IsRelJ R0Exps rel1 :=
  ⟨_, isOfFinOrder_ζ120_pow 90, rel1_prod⟩

/-- Exponents of relation 2: `-2[0] +1[20] +1[100]`. -/
def rel2 : ℕ → ℤ := Pi.single 0 (-2) + Pi.single 20 1 + Pi.single 100 1

theorem rel2_prod : ∏ j ∈ R0Exps, wJ j ^ rel2 j = ζ120 ^ 90 := by
  simp (disch := decide) only [rel2, prodW_add, prod_single]
  simp only [wJ_eq, zpow_neg, zpow_ofNat]
  have ht := tC_ne_zero
  have h0 := aJ_zero_ne
  have h20 := aJ_ne 20
  have h100 := aJ_ne 100
  field_simp
  linear_combination relation_2

theorem rel2_isRel : IsRelJ R0Exps rel2 :=
  ⟨_, isOfFinOrder_ζ120_pow 90, rel2_prod⟩

/-- Exponents of relation 3: `-2[0] +1[15] +1[75]`. -/
def rel3 : ℕ → ℤ := Pi.single 0 (-2) + Pi.single 15 1 + Pi.single 75 1

theorem rel3_prod : ∏ j ∈ R0Exps, wJ j ^ rel3 j = ζ120 ^ 90 := by
  simp (disch := decide) only [rel3, prodW_add, prod_single]
  simp only [wJ_eq, zpow_neg, zpow_ofNat]
  have ht := tC_ne_zero
  have h0 := aJ_zero_ne
  have h15 := aJ_ne 15
  have h75 := aJ_ne 75
  field_simp
  linear_combination relation_3

theorem rel3_isRel : IsRelJ R0Exps rel3 :=
  ⟨_, isOfFinOrder_ζ120_pow 90, rel3_prod⟩

/-- Exponents of relation 4: `-3[0] +1[12] +1[36] -1[60] +1[84] +1[108]`. -/
def rel4 : ℕ → ℤ :=
  Pi.single 0 (-3) + Pi.single 12 1 + Pi.single 36 1 + Pi.single 60 (-1)
    + Pi.single 84 1 + Pi.single 108 1

theorem rel4_prod : ∏ j ∈ R0Exps, wJ j ^ rel4 j = ζ120 ^ 90 := by
  simp (disch := decide) only [rel4, prodW_add, prod_single]
  simp only [wJ_eq, zpow_neg, zpow_ofNat]
  have ht := tC_ne_zero
  have h0 := aJ_zero_ne
  have h12 := aJ_ne 12
  have h36 := aJ_ne 36
  have h60 := aJ_ne 60
  have h84 := aJ_ne 84
  have h108 := aJ_ne 108
  field_simp
  linear_combination relation_4

theorem rel4_isRel : IsRelJ R0Exps rel4 :=
  ⟨_, isOfFinOrder_ζ120_pow 90, rel4_prod⟩

/-- Exponents of relation 5: `+1[10] -1[20]`. -/
def rel5 : ℕ → ℤ := Pi.single 10 1 + Pi.single 20 (-1)

theorem rel5_prod : ∏ j ∈ R0Exps, wJ j ^ rel5 j = ζ120 ^ 20 := by
  simp (disch := decide) only [rel5, prodW_add, prod_single]
  simp only [wJ_eq, zpow_neg, zpow_ofNat]
  have ht := tC_ne_zero
  have h10 := aJ_ne 10
  have h20 := aJ_ne 20
  field_simp
  linear_combination relation_5

theorem rel5_isRel : IsRelJ R0Exps rel5 :=
  ⟨_, isOfFinOrder_ζ120_pow 20, rel5_prod⟩

/-- Exponents of relation 6: `-2[0] +1[20] +1[50]`. -/
def rel6 : ℕ → ℤ := Pi.single 0 (-2) + Pi.single 20 1 + Pi.single 50 1

theorem rel6_prod : ∏ j ∈ R0Exps, wJ j ^ rel6 j = ζ120 ^ 70 := by
  simp (disch := decide) only [rel6, prodW_add, prod_single]
  simp only [wJ_eq, zpow_neg, zpow_ofNat]
  have ht := tC_ne_zero
  have h0 := aJ_zero_ne
  have h20 := aJ_ne 20
  have h50 := aJ_ne 50
  field_simp
  linear_combination relation_6

theorem rel6_isRel : IsRelJ R0Exps rel6 :=
  ⟨_, isOfFinOrder_ζ120_pow 70, rel6_prod⟩

/-- Exponents of relation 7: `-4[12] +4[18] +1[60] -1[90]`. -/
def rel7 : ℕ → ℤ := Pi.single 12 (-4) + Pi.single 18 4 + Pi.single 60 1 + Pi.single 90 (-1)

theorem rel7_prod : ∏ j ∈ R0Exps, wJ j ^ rel7 j = ζ120 ^ 54 := by
  simp (disch := decide) only [rel7, prodW_add, prod_single]
  simp only [wJ_eq, zpow_neg, zpow_ofNat]
  have ht := tC_ne_zero
  have h12 := aJ_ne 12
  have h18 := aJ_ne 18
  have h60 := aJ_ne 60
  have h90 := aJ_ne 90
  field_simp
  linear_combination relation_7

theorem rel7_isRel : IsRelJ R0Exps rel7 :=
  ⟨_, isOfFinOrder_ζ120_pow 54, rel7_prod⟩

/-- Exponents of relation 8: `-12[0] +4[12] +4[36] +4[42] -3[60] +4[84] -1[90]`. -/
def rel8 : ℕ → ℤ :=
  Pi.single 0 (-12) + Pi.single 12 4 + Pi.single 36 4 + Pi.single 42 4
    + Pi.single 60 (-3) + Pi.single 84 4 + Pi.single 90 (-1)

theorem rel8_prod : ∏ j ∈ R0Exps, wJ j ^ rel8 j = ζ120 ^ 6 := by
  simp (disch := decide) only [rel8, prodW_add, prod_single]
  simp only [wJ_eq, zpow_neg, zpow_ofNat]
  have ht := tC_ne_zero
  have h0 := aJ_zero_ne
  have h12 := aJ_ne 12
  have h36 := aJ_ne 36
  have h42 := aJ_ne 42
  have h60 := aJ_ne 60
  have h84 := aJ_ne 84
  have h90 := aJ_ne 90
  field_simp
  linear_combination relation_8

theorem rel8_isRel : IsRelJ R0Exps rel8 :=
  ⟨_, isOfFinOrder_ζ120_pow 6, rel8_prod⟩

/-- Exponents of relation 9: `+1[60] +4[66] -4[84] -1[90]`. -/
def rel9 : ℕ → ℤ := Pi.single 60 1 + Pi.single 66 4 + Pi.single 84 (-4) + Pi.single 90 (-1)

theorem rel9_prod : ∏ j ∈ R0Exps, wJ j ^ rel9 j = ζ120 ^ 78 := by
  simp (disch := decide) only [rel9, prodW_add, prod_single]
  simp only [wJ_eq, zpow_neg, zpow_ofNat]
  have ht := tC_ne_zero
  have h60 := aJ_ne 60
  have h66 := aJ_ne 66
  have h84 := aJ_ne 84
  have h90 := aJ_ne 90
  field_simp
  linear_combination relation_9

theorem rel9_isRel : IsRelJ R0Exps rel9 :=
  ⟨_, isOfFinOrder_ζ120_pow 78, rel9_prod⟩

/-- Exponents of relation 10: `-4[36] +1[60] -1[90] +4[114]`. -/
def rel10 : ℕ → ℤ := Pi.single 36 (-4) + Pi.single 60 1 + Pi.single 90 (-1) + Pi.single 114 4

theorem rel10_prod : ∏ j ∈ R0Exps, wJ j ^ rel10 j = ζ120 ^ 102 := by
  simp (disch := decide) only [rel10, prodW_add, prod_single]
  simp only [wJ_eq, zpow_neg, zpow_ofNat]
  have ht := tC_ne_zero
  have h36 := aJ_ne 36
  have h60 := aJ_ne 60
  have h90 := aJ_ne 90
  have h114 := aJ_ne 114
  field_simp
  linear_combination relation_10

theorem rel10_isRel : IsRelJ R0Exps rel10 :=
  ⟨_, isOfFinOrder_ζ120_pow 102, rel10_prod⟩

/-- Exponents of relation 11: `-2[5] +2[25] +1[45] -1[105]`. -/
def rel11 : ℕ → ℤ := Pi.single 5 (-2) + Pi.single 25 2 + Pi.single 45 1 + Pi.single 105 (-1)

theorem rel11_prod : ∏ j ∈ R0Exps, wJ j ^ rel11 j = ζ120 ^ 40 := by
  simp (disch := decide) only [rel11, prodW_add, prod_single]
  simp only [wJ_eq, zpow_neg, zpow_ofNat]
  have ht := tC_ne_zero
  have h5 := aJ_ne 5
  have h25 := aJ_ne 25
  have h45 := aJ_ne 45
  have h105 := aJ_ne 105
  field_simp
  linear_combination relation_11

theorem rel11_isRel : IsRelJ R0Exps rel11 :=
  ⟨_, isOfFinOrder_ζ120_pow 40, rel11_prod⟩

/-- Exponents of relation 12: `-2[0] +2[5] -1[45] +2[65] -1[105]`. -/
def rel12 : ℕ → ℤ :=
  Pi.single 0 (-2) + Pi.single 5 2 + Pi.single 45 (-1) + Pi.single 65 2
    + Pi.single 105 (-1)

theorem rel12_prod : ∏ j ∈ R0Exps, wJ j ^ rel12 j = ζ120 ^ 110 := by
  simp (disch := decide) only [rel12, prodW_add, prod_single]
  simp only [wJ_eq, zpow_neg, zpow_ofNat]
  have ht := tC_ne_zero
  have h0 := aJ_zero_ne
  have h5 := aJ_ne 5
  have h45 := aJ_ne 45
  have h65 := aJ_ne 65
  have h105 := aJ_ne 105
  field_simp
  linear_combination relation_12

theorem rel12_isRel : IsRelJ R0Exps rel12 :=
  ⟨_, isOfFinOrder_ζ120_pow 110, rel12_prod⟩

/-- Exponents of relation 13: `-1[0] +1[5] -1[45] +1[85]`. -/
def rel13 : ℕ → ℤ := Pi.single 0 (-1) + Pi.single 5 1 + Pi.single 45 (-1) + Pi.single 85 1

theorem rel13_prod : ∏ j ∈ R0Exps, wJ j ^ rel13 j = ζ120 ^ 15 := by
  simp (disch := decide) only [rel13, prodW_add, prod_single]
  simp only [wJ_eq, zpow_neg, zpow_ofNat]
  have ht := tC_ne_zero
  have h0 := aJ_zero_ne
  have h5 := aJ_ne 5
  have h45 := aJ_ne 45
  have h85 := aJ_ne 85
  field_simp
  linear_combination relation_13

theorem rel13_isRel : IsRelJ R0Exps rel13 :=
  ⟨_, isOfFinOrder_ζ120_pow 15, rel13_prod⟩

/-- The integer combination `∑ c_k · rel_k` of the 13 relations. -/
def comb (c : Fin 13 → ℤ) (j : ℕ) : ℤ :=
  c 0 * rel1 j + c 1 * rel2 j + c 2 * rel3 j + c 3 * rel4 j + c 4 * rel5 j + c 5 * rel6 j
    + c 6 * rel7 j + c 7 * rel8 j + c 8 * rel9 j + c 9 * rel10 j + c 10 * rel11 j
    + c 11 * rel12 j + c 12 * rel13 j

/-- Every integer combination of the 13 relations is a relation. -/
theorem comb_isRel (c : Fin 13 → ℤ) : IsRelJ R0Exps (comb c) :=
  ((((((((((((rel1_isRel.zsmul (c 0)).add
    (rel2_isRel.zsmul (c 1))).add
    (rel3_isRel.zsmul (c 2))).add
    (rel4_isRel.zsmul (c 3))).add
    (rel5_isRel.zsmul (c 4))).add
    (rel6_isRel.zsmul (c 5))).add
    (rel7_isRel.zsmul (c 6))).add
    (rel8_isRel.zsmul (c 7))).add
    (rel9_isRel.zsmul (c 8))).add
    (rel10_isRel.zsmul (c 9))).add
    (rel11_isRel.zsmul (c 10))).add
    (rel12_isRel.zsmul (c 11))).add
    (rel13_isRel.zsmul (c 12))

theorem comb_at_0 (c : Fin 13 → ℤ) :
    comb c 0 = (-1) * c 0 + (-2) * c 1 + (-2) * c 2 + (-3) * c 3 + (-2) * c 5
      + (-12) * c 7 + (-2) * c 11 + (-1) * c 12 := by
  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,
    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]
  ring

theorem comb_at_100 (c : Fin 13 → ℤ) :
    comb c 100 = 1 * c 1 := by
  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,
    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]
  ring

theorem comb_at_75 (c : Fin 13 → ℤ) :
    comb c 75 = 1 * c 2 := by
  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,
    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]
  ring

theorem comb_at_108 (c : Fin 13 → ℤ) :
    comb c 108 = 1 * c 3 := by
  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,
    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]
  ring

theorem comb_at_10 (c : Fin 13 → ℤ) :
    comb c 10 = 1 * c 4 := by
  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,
    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]
  ring

theorem comb_at_50 (c : Fin 13 → ℤ) :
    comb c 50 = 1 * c 5 := by
  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,
    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]
  ring

theorem comb_at_18 (c : Fin 13 → ℤ) :
    comb c 18 = 4 * c 6 := by
  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,
    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]
  ring

theorem comb_at_42 (c : Fin 13 → ℤ) :
    comb c 42 = 4 * c 7 := by
  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,
    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]
  ring

theorem comb_at_66 (c : Fin 13 → ℤ) :
    comb c 66 = 4 * c 8 := by
  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,
    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]
  ring

theorem comb_at_114 (c : Fin 13 → ℤ) :
    comb c 114 = 4 * c 9 := by
  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,
    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]
  ring

theorem comb_at_25 (c : Fin 13 → ℤ) :
    comb c 25 = 2 * c 10 := by
  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,
    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]
  ring

theorem comb_at_65 (c : Fin 13 → ℤ) :
    comb c 65 = 2 * c 11 := by
  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,
    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]
  ring

theorem comb_at_85 (c : Fin 13 → ℤ) :
    comb c 85 = 1 * c 12 := by
  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,
    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]
  ring

/-- The coefficients that express `4 f` by the 13 relations. -/
def spanCoeff (f : ℕ → ℤ) : Fin 13 → ℤ :=
  ![-(4 * f 0 + 8 * f 100 + 8 * f 75 + 12 * f 108 + 8 * f 50
      + 12 * f 42 + 4 * f 65 + 4 * f 85),
    4 * f 100, 4 * f 75, 4 * f 108, 4 * f 10, 4 * f 50, f 18,
    f 42, f 66, f 114, 2 * f 25, 2 * f 65, 4 * f 85]

theorem spanCoeff_0 (f : ℕ → ℤ) :
    spanCoeff f 0 = -(4 * f 0 + 8 * f 100 + 8 * f 75 + 12 * f 108 + 8 * f 50
      + 12 * f 42 + 4 * f 65 + 4 * f 85) := rfl

theorem spanCoeff_1 (f : ℕ → ℤ) :
    spanCoeff f 1 = 4 * f 100 := rfl

theorem spanCoeff_2 (f : ℕ → ℤ) :
    spanCoeff f 2 = 4 * f 75 := rfl

theorem spanCoeff_3 (f : ℕ → ℤ) :
    spanCoeff f 3 = 4 * f 108 := rfl

theorem spanCoeff_4 (f : ℕ → ℤ) :
    spanCoeff f 4 = 4 * f 10 := rfl

theorem spanCoeff_5 (f : ℕ → ℤ) :
    spanCoeff f 5 = 4 * f 50 := rfl

theorem spanCoeff_6 (f : ℕ → ℤ) :
    spanCoeff f 6 = f 18 := rfl

theorem spanCoeff_7 (f : ℕ → ℤ) :
    spanCoeff f 7 = f 42 := rfl

theorem spanCoeff_8 (f : ℕ → ℤ) :
    spanCoeff f 8 = f 66 := rfl

theorem spanCoeff_9 (f : ℕ → ℤ) :
    spanCoeff f 9 = f 114 := rfl

theorem spanCoeff_10 (f : ℕ → ℤ) :
    spanCoeff f 10 = 2 * f 25 := rfl

theorem spanCoeff_11 (f : ℕ → ℤ) :
    spanCoeff f 11 = 2 * f 65 := rfl

theorem spanCoeff_12 (f : ℕ → ℤ) :
    spanCoeff f 12 = 4 * f 85 := rfl

/-- `4 f - comb (spanCoeff f)` vanishes at the 13 pivot exponents. -/
theorem span_pivots (f : ℕ → ℤ) : ∀ j ∈ R0Exps, j ∉ B11 →
    4 * f j + -1 * comb (spanCoeff f) j = 0 := by
  intro j hj hnj
  simp only [R0Exps, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [comb_at_0]
    simp only [spanCoeff_0, spanCoeff_1, spanCoeff_2, spanCoeff_3, spanCoeff_5,
      spanCoeff_7, spanCoeff_11, spanCoeff_12]
    ring
  · exact absurd (by decide) hnj
  · exact absurd (by decide) hnj
  · exact absurd (by decide) hnj
  · exact absurd (by decide) hnj
  · rw [comb_at_100]
    simp only [spanCoeff_1]
    ring
  · exact absurd (by decide) hnj
  · exact absurd (by decide) hnj
  · rw [comb_at_75]
    simp only [spanCoeff_2]
    ring
  · exact absurd (by decide) hnj
  · exact absurd (by decide) hnj
  · exact absurd (by decide) hnj
  · exact absurd (by decide) hnj
  · rw [comb_at_108]
    simp only [spanCoeff_3]
    ring
  · rw [comb_at_10]
    simp only [spanCoeff_4]
    ring
  · rw [comb_at_50]
    simp only [spanCoeff_5]
    ring
  · rw [comb_at_18]
    simp only [spanCoeff_6]
    ring
  · rw [comb_at_42]
    simp only [spanCoeff_7]
    ring
  · rw [comb_at_66]
    simp only [spanCoeff_8]
    ring
  · rw [comb_at_114]
    simp only [spanCoeff_9]
    ring
  · exact absurd (by decide) hnj
  · rw [comb_at_25]
    simp only [spanCoeff_10]
    ring
  · rw [comb_at_65]
    simp only [spanCoeff_11]
    ring
  · rw [comb_at_85]
    simp only [spanCoeff_12]
    ring

/-- **Every relation among the 24 numbers is a rational combination of the 13.**
If `f` is a relation on `R0Exps`, then `4 f` is an integer combination of `rel1, ..., rel13`. -/
theorem relations_span {f : ℕ → ℤ} (h : IsRelJ R0Exps f) :
    ∃ c : Fin 13 → ℤ, ∀ j ∈ R0Exps, 4 * f j = comb c j := by
  refine ⟨spanCoeff f, ?_⟩
  have hg : IsRelJ R0Exps (fun j => 4 * f j + -1 * comb (spanCoeff f) j) :=
    (h.zsmul 4).add ((comb_isRel (spanCoeff f)).zsmul (-1))
  have hpiv := span_pivots f
  have hB := basis_independent (hg.restrict (by decide) hpiv)
  intro j hj
  by_cases hjB : j ∈ B11
  · have h0 := hB j hjB
    omega
  · have h0 := hpiv j hj hjB
    omega

/-- **The 13 relations are linearly independent.** -/
theorem rel_independent {c : Fin 13 → ℤ} (h : ∀ j ∈ R0Exps, comb c j = 0) :
    ∀ k, c k = 0 := by
  have h0 := h 0 (by decide)
  rw [comb_at_0] at h0
  have h100 := h 100 (by decide)
  rw [comb_at_100] at h100
  have h75 := h 75 (by decide)
  rw [comb_at_75] at h75
  have h108 := h 108 (by decide)
  rw [comb_at_108] at h108
  have h10 := h 10 (by decide)
  rw [comb_at_10] at h10
  have h50 := h 50 (by decide)
  rw [comb_at_50] at h50
  have h18 := h 18 (by decide)
  rw [comb_at_18] at h18
  have h42 := h 42 (by decide)
  rw [comb_at_42] at h42
  have h66 := h 66 (by decide)
  rw [comb_at_66] at h66
  have h114 := h 114 (by decide)
  rw [comb_at_114] at h114
  have h25 := h 25 (by decide)
  rw [comb_at_25] at h25
  have h65 := h 65 (by decide)
  rw [comb_at_65] at h65
  have h85 := h 85 (by decide)
  rw [comb_at_85] at h85
  intro k
  fin_cases k
  · show c 0 = 0
    omega
  · show c 1 = 0
    omega
  · show c 2 = 0
    omega
  · show c 3 = 0
    omega
  · show c 4 = 0
    omega
  · show c 5 = 0
    omega
  · show c 6 = 0
    omega
  · show c 7 = 0
    omega
  · show c 8 = 0
    omega
  · show c 9 = 0
    omega
  · show c 10 = 0
    omega
  · show c 11 = 0
    omega
  · show c 12 = 0
    omega

/-! ## 7. All relations among the `1 - r/t`, for arbitrary roots of unity `r` -/

open Classical in
/-- **Steps 2 and 3 of Theorem C together.** Let `S` be a finite set of roots of unity and `e`
a multiplicative relation among the `1 - r/t`, `r ∈ S`. Then `e` vanishes outside the 24 roots
of `R0`, and four times its restriction to `R0` is an integer combination of the 13
relations. -/
theorem relations_classified {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ}
    (h : IsRelation S e) :
    (∀ r ∈ S, r ∉ R0 → e r = 0) ∧
      ∃ c : Fin 13 → ℤ, ∀ j ∈ R0Exps,
        4 * (if ζ120 ^ j ∈ S then e (ζ120 ^ j) else 0) = comb c j := by
  have hsupp := support_subset_R0' hS h
  refine ⟨hsupp, ?_⟩
  have hlt : ∀ j ∈ R0Exps, j < 120 := by decide
  have hrel : IsRelJ R0Exps (fun j => if ζ120 ^ j ∈ S then e (ζ120 ^ j) else 0) := by
    obtain ⟨ξ, hξ, hprod⟩ := h
    refine ⟨ξ, hξ, ?_⟩
    rw [← hprod]
    -- both sides are the product over the roots of `S` that lie in `R0`
    have h1 : ∏ r ∈ S, (1 - r / tC) ^ e r =
        ∏ r ∈ S.filter (fun r => r ∈ R0), (1 - r / tC) ^ e r := by
      refine (Finset.prod_filter_of_ne fun r hr hne => ?_).symm
      by_contra hR
      exact hne (by rw [hsupp r hr hR, zpow_zero])
    have h2 : ∏ j ∈ R0Exps, wJ j ^ (if ζ120 ^ j ∈ S then e (ζ120 ^ j) else 0) =
        ∏ j ∈ R0Exps.filter (fun j => ζ120 ^ j ∈ S), wJ j ^ e (ζ120 ^ j) := by
      rw [Finset.prod_filter]
      refine Finset.prod_congr rfl fun j _ => ?_
      split_ifs
      · rfl
      · exact zpow_zero _
    have h3 : S.filter (fun r => r ∈ R0) =
        (R0Exps.filter (fun j => ζ120 ^ j ∈ S)).image (fun j => ζ120 ^ j) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hrS, j, hj, rfl⟩
        exact ⟨j, ⟨hj, hrS⟩, rfl⟩
      · rintro ⟨j, ⟨hj, hjS⟩, rfl⟩
        exact ⟨hjS, j, hj, rfl⟩
    rw [h1, h2, h3, Finset.prod_image]
    · rfl
    · intro i hi j hj hij
      exact ζ120_prim.pow_inj (hlt i (Finset.mem_filter.1 hi).1)
        (hlt j (Finset.mem_filter.1 hj).1) hij
  exact relations_span hrel

end PiFormula
