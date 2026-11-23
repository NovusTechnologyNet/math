import Pilean.Erdos.AbstractSetting
import Mathlib.Tactic.FieldSimp

/-!
# The algebraic core of Theorem A, part 4: Lemma KL

`p₀` is an index, `m` the set of all other indices, `c p = (π p - 1)/2^(s p)`.

* `cN_mem_KS`: the element `(∏_{p ∈ m} c p) N_m` of `R[S]` lies in `K^# m` relative to the ideal
  `(1 - t_{p₀})`.
* `exists_K_decomp`: hence, by Lemma D (`DSetting.lemmaD`) in `ℤ[S]`, it is `X + (1 - t_{p₀}) μ`
  with `X` in `K m = ∏_{p ∈ m} (1 - t_p, a_p)`.
* `K_transfer`: if `X ∈ K m` and `y = ∑_{k ⊆ m} a_k N_{m ∖ k} l_k` with the `l_k` integral at 2,
  then `X y = a_m W` with `W` integral at 2.
* `lemmaKL`: if moreover `(1 - t_{p₀}) y = 0`, then `ε(y) ∈ |S| ℤ_(2)`. (The paper's Lemma KL,
  for `y = N_0 w`.)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open scoped BigOperators

open AddMonoidAlgebra (single)

namespace PiFormula

namespace Erdos

namespace Abs

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The element `c N_m` lies in `K^# m` modulo `1 - t_{p₀}` -/

section Generic

variable (R : Type*) [CommRing R] (s : ι → ℕ)

theorem prod_nrm_mul_self (n : Finset ι) :
    (∏ p ∈ n, nrm R s p) * ∏ p ∈ n, nrm R s p =
      ((∏ p ∈ n, (2 : ℤ) ^ s p : ℤ) : GR R s) * ∏ p ∈ n, nrm R s p := by
  rw [← Finset.prod_mul_distrib]
  push_cast
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => nrm_mul_nrm R s p

theorem prod_nrm_mul_prod_nrm {n m : Finset ι} (hn : n ⊆ m) :
    (∏ p ∈ m, nrm R s p) * ∏ p ∈ n, nrm R s p =
      ((∏ p ∈ n, (2 : ℤ) ^ s p : ℤ) : GR R s) * ∏ p ∈ m, nrm R s p := by
  rw [← Finset.prod_sdiff hn, mul_assoc, prod_nrm_mul_self]
  ring

theorem aR_mul_prod_nrm (π : ι → ℤ) (u : ι → Grp s) (p₀ p : ι) :
    ∃ w : GR R s, aR R s π u p * ∏ q ∈ Finset.univ.erase p₀, nrm R s q =
      ((π p - 1 : ℤ) : GR R s) * ∏ q ∈ Finset.univ.erase p₀, nrm R s q + del R s p₀ * w := by
  obtain ⟨w, hw⟩ := single_mul_prod_nrm R s p₀ (u p)
  refine ⟨-w, ?_⟩
  have h : (single (0 : Grp s) (π p : R) : GR R s) = ((π p : ℤ) : GR R s) :=
    (AddMonoidAlgebra.intCast_def _).symm
  rw [aR, h]
  push_cast
  linear_combination -hw

theorem prod_aR_mul_prod_nrm (π : ι → ℤ) (u : ι → Grp s) (p₀ : ι) (n : Finset ι) :
    ∃ w : GR R s, (∏ p ∈ n, aR R s π u p) * ∏ q ∈ Finset.univ.erase p₀, nrm R s q =
      ((∏ p ∈ n, (π p - 1) : ℤ) : GR R s) * ∏ q ∈ Finset.univ.erase p₀, nrm R s q +
        del R s p₀ * w := by
  induction n using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert p n hp ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨w', hw'⟩ := aR_mul_prod_nrm R s π u p₀ p
    refine ⟨((∏ p ∈ n, (π p - 1) : ℤ) : GR R s) * w' + aR R s π u p * w, ?_⟩
    rw [Finset.prod_insert hp, Finset.prod_insert hp]
    push_cast at hw hw' ⊢
    linear_combination (aR R s π u p) * hw + (∏ p ∈ n, ((π p : GR R s) - 1)) * hw'

variable [CharZero R] [NoZeroDivisors R]

theorem cN_mem_KS (π : ι → ℤ) (u : ι → Grp s) (hπ : ∀ p, 1 < π p) (c : ι → ℤ)
    (hc : ∀ p, π p - 1 = 2 ^ s p * c p) (p₀ : ι) :
    ((∏ p ∈ Finset.univ.erase p₀, c p : ℤ) : GR R s) *
        (gSetting R s π u hπ).NP (Finset.univ.erase p₀) ∈
      (gSetting R s π u hπ).KS (Finset.univ.erase p₀) {p₀} ∅ := by
  intro n hn
  obtain ⟨w, hw⟩ := prod_aR_mul_prod_nrm R s π u p₀ n
  have hNP := prod_nrm_mul_prod_nrm R s hn
  refine ⟨((∏ p ∈ Finset.univ.erase p₀ \ n, c p : ℤ) : GR R s) *
    (gSetting R s π u hπ).NP (Finset.univ.erase p₀), ?_⟩
  have hI : (∏ p ∈ Finset.univ.erase p₀, c p) * ∏ p ∈ n, (2 : ℤ) ^ s p =
      (∏ p ∈ Finset.univ.erase p₀ \ n, c p) * ∏ p ∈ n, (π p - 1) := by
    rw [← Finset.prod_sdiff hn, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_congr rfl fun p _ => by rw [hc p]; ring
  have hI' : ((∏ p ∈ Finset.univ.erase p₀, c p : ℤ) : GR R s) *
        ((∏ p ∈ n, (2 : ℤ) ^ s p : ℤ) : GR R s) =
      ((∏ p ∈ Finset.univ.erase p₀ \ n, c p : ℤ) : GR R s) *
        ((∏ p ∈ n, (π p - 1) : ℤ) : GR R s) := by
    rw [← Int.cast_mul, ← Int.cast_mul, hI]
  have hmem : del R s p₀ ∈ (gSetting R s π u hπ).Q {p₀} ∅ :=
    mem_qIdeal_left _ _ ∅ (Finset.mem_singleton_self p₀)
  have h : ((∏ p ∈ Finset.univ.erase p₀, c p : ℤ) : GR R s) *
        (gSetting R s π u hπ).NP (Finset.univ.erase p₀) * (gSetting R s π u hπ).NP n -
      (gSetting R s π u hπ).aP n * (((∏ p ∈ Finset.univ.erase p₀ \ n, c p : ℤ) : GR R s) *
        (gSetting R s π u hπ).NP (Finset.univ.erase p₀)) =
      -(((∏ p ∈ Finset.univ.erase p₀ \ n, c p : ℤ) : GR R s) * w) * del R s p₀ := by
    change ((∏ p ∈ Finset.univ.erase p₀, c p : ℤ) : GR R s) *
        (∏ q ∈ Finset.univ.erase p₀, nrm R s q) * (∏ q ∈ n, nrm R s q) -
      (∏ q ∈ n, aR R s π u q) * (((∏ p ∈ Finset.univ.erase p₀ \ n, c p : ℤ) : GR R s) *
        ∏ q ∈ Finset.univ.erase p₀, nrm R s q) =
      -(((∏ p ∈ Finset.univ.erase p₀ \ n, c p : ℤ) : GR R s) * w) * del R s p₀
    linear_combination ((∏ p ∈ Finset.univ.erase p₀, c p : ℤ) : GR R s) * hNP -
      ((∏ p ∈ Finset.univ.erase p₀ \ n, c p : ℤ) : GR R s) * hw +
      (∏ q ∈ Finset.univ.erase p₀, nrm R s q) * hI'
  rw [h]
  exact Ideal.mul_mem_left _ _ hmem

end Generic

variable {s : ι → ℕ}

/-- By Lemma D: `c N_m = X + (1 - t_{p₀}) μ` with `X ∈ K m`, in `ℤ[S]`. -/
theorem exists_K_decomp (π : ι → ℤ) (u : ι → Grp s) (hπ : ∀ p, 1 < π p) (c : ι → ℤ)
    (hc : ∀ p, π p - 1 = 2 ^ s p * c p) (p₀ : ι) :
    ∃ X ∈ (gSetting ℤ s π u hπ).K (Finset.univ.erase p₀), ∃ μ : GR ℤ s,
      ((∏ p ∈ Finset.univ.erase p₀, c p : ℤ) : GR ℤ s) *
        (gSetting ℤ s π u hπ).NP (Finset.univ.erase p₀) = X + del ℤ s p₀ * μ := by
  have hdis : Disjoint (Finset.univ.erase p₀) ({p₀} : Finset ι) := by
    rw [Finset.disjoint_singleton_right]
    exact Finset.notMem_erase p₀ _
  have h := (gSetting ℤ s π u hπ).lemmaD (Finset.univ.erase p₀) {p₀} ∅ hdis
    (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _)
    (cN_mem_KS ℤ s π u hπ c hc p₀)
  obtain ⟨X, hX, q, hq, hXq⟩ := Submodule.mem_sup.1 h
  have hQ : (gSetting ℤ s π u hπ).Q {p₀} ∅ = Ideal.span {del ℤ s p₀} := by
    have h1 := (gSetting ℤ s π u hπ).Q_insert_left ∅ ∅ p₀
    have h2 : (gSetting ℤ s π u hπ).Q ∅ ∅ = ⊥ := qIdeal_empty _ _
    rw [h2, bot_sup_eq] at h1
    exact h1
  rw [hQ] at hq
  obtain ⟨μ, rfl⟩ := Ideal.mem_span_singleton'.1 hq
  exact ⟨X, hX, μ, by rw [← hXq, mul_comm μ]⟩

/-! ### Transfer to `ℚ[S]` -/

theorem toQ_NP (π : ι → ℤ) (u : ι → Grp s) (hπ : ∀ p, 1 < π p) (t : Finset ι) :
    toQ s ((gSetting ℤ s π u hπ).NP t) = normElt s t := by
  rw [normElt_eq_prod, DSetting.NP, map_prod]
  exact Finset.prod_congr rfl fun p _ => toQ_nrm p

theorem toQ_aP (π : ι → ℤ) (u : ι → Grp s) (hπ : ∀ p, 1 < π p) (t : Finset ι) :
    toQ s ((gSetting ℤ s π u hπ).aP t) = aProd π u t := by
  rw [aProd, DSetting.aP, map_prod]
  exact Finset.prod_congr rfl fun p _ => toQ_aR π u p

/-- `a_n` is not a zero divisor in `ℚ[S]`. -/
theorem aProd_cancel (π : ι → ℤ) (u : ι → Grp s) (hπ : ∀ p, 1 < π p) (n : Finset ι)
    {x : GRing s} (h : aProd π u n * x = 0) : x = 0 := by
  have h0 : (gSetting ℚ s π u hπ).Q ∅ ∅ = ⊥ := qIdeal_empty _ _
  have h1 : (gSetting ℚ s π u hπ).aP n * x ∈ (gSetting ℚ s π u hπ).Q ∅ ∅ := by
    rw [h0]
    exact Ideal.mem_bot.2 h
  have h2 := (gSetting ℚ s π u hπ).h1' (Finset.disjoint_empty_left ∅) n h1
  rw [h0] at h2
  exact Ideal.mem_bot.1 h2

/-- If `X ∈ K m` and `y = ∑_{k ⊆ m} a_k N_{m ∖ k} l_k` with integral `l_k`, then `X y = a_m W`
with `W` integral. -/
theorem K_transfer (π : ι → ℤ) (u : ι → Grp s) (hπ : ∀ p, 1 < π p) (m : Finset ι)
    (l : Finset ι → GRing s) (hl : ∀ n, Integral2 (l n)) {X : GR ℤ s}
    (hX : X ∈ (gSetting ℤ s π u hπ).K m) :
    ∃ W : GRing s, Integral2 W ∧
      toQ s X * (∑ k ∈ m.powerset, aProd π u k * normElt s (m \ k) * l k) =
        aProd π u m * W := by
  unfold DSetting.K at hX
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨n, hn, rfl⟩ := hX
    refine ⟨∑ k ∈ m.powerset, if n ⊆ k then
      toQ s ((gSetting ℤ s π u hπ).dP n * (gSetting ℤ s π u hπ).aP (k \ n) *
        (gSetting ℤ s π u hπ).NP (m \ k)) * l k else 0, ?_, ?_⟩
    · refine integral2_sum _ _ fun k _ => ?_
      split_ifs
      · exact integral2_mul (integral2_toQ _) (hl k)
      · exact integral2_zero
    · rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ⊆ m := Finset.mem_powerset.1 hk
      split_ifs with hnk
      · have e1 : (m \ n) \ (k \ n) = m \ k := by
          ext p
          simp only [Finset.mem_sdiff]
          constructor
          · rintro ⟨⟨hpm, hpn⟩, h⟩
            exact ⟨hpm, fun hpk => h ⟨hpk, hpn⟩⟩
          · rintro ⟨hpm, hpk⟩
            exact ⟨⟨hpm, fun hpn => hpk (hnk hpn)⟩, fun h => hpk h.1⟩
        have e2 : aProd π u (m \ k) * aProd π u (k \ n) = aProd π u (m \ n) := by
          have h := Finset.prod_sdiff (f := aElt π u)
            (Finset.sdiff_subset_sdiff hk' (subset_refl n))
          rwa [e1] at h
        have e3 : aProd π u (m \ k) * aProd π u k = aProd π u m := Finset.prod_sdiff hk'
        rw [map_mul, map_mul, map_mul, toQ_aP, toQ_aP, toQ_NP, ← e2, ← e3]
        ring
      · obtain ⟨p, hpn, hpk⟩ := Finset.not_subset.1 hnk
        have hz : (gSetting ℤ s π u hπ).dP n * (gSetting ℤ s π u hπ).NP (m \ k) = 0 :=
          (gSetting ℤ s π u hπ).dP_mul_NP_eq_zero hpn (Finset.mem_sdiff.2 ⟨hn hpn, hpk⟩)
        have hz' := congrArg (toQ s) hz
        rw [map_mul, map_zero, toQ_NP] at hz'
        rw [mul_zero, map_mul]
        linear_combination
          (toQ s ((gSetting ℤ s π u hπ).aP (m \ n)) * aProd π u k * l k) * hz'
  | zero => exact ⟨0, integral2_zero, by simp⟩
  | add X Y _ _ hX hY =>
    obtain ⟨W, hW, hWe⟩ := hX
    obtain ⟨V, hV, hVe⟩ := hY
    exact ⟨W + V, integral2_add hW hV, by rw [map_add, add_mul, hWe, hVe, mul_add]⟩
  | smul c X _ hX =>
    obtain ⟨W, hW, hWe⟩ := hX
    refine ⟨toQ s c * W, integral2_mul (integral2_toQ c) hW, ?_⟩
    rw [smul_eq_mul, map_mul, mul_assoc, hWe]
    ring

/-! ### Lemma KL -/

theorem single_zero_mul_mul (a b : ℚ) (x : GRing s) :
    single 0 a * (single 0 b * x) = single 0 (a * b) * x := by
  rw [← mul_assoc, AddMonoidAlgebra.single_mul_single, add_zero]

/-- **Lemma KL** (in the form used). `m` is the set of all indices except `p₀`. If
`y = ∑_{n ⊆ m} a_n N_{m ∖ n} l_n` with the `l_n` integral at 2 and `(1 - t_{p₀}) y = 0`, then
`ε(y) ∈ |S| ℤ_(2)`. -/
theorem lemmaKL (π : ι → ℤ) (u : ι → Grp s) (hπ : ∀ p, 1 < π p) (c : ι → ℤ)
    (hc : ∀ p, π p - 1 = 2 ^ s p * c p) (p₀ : ι) (l : Finset ι → GRing s)
    (hl : ∀ n, Integral2 (l n)) (y : GRing s)
    (hy : y = ∑ n ∈ (Finset.univ.erase p₀).powerset,
      aProd π u n * normElt s (Finset.univ.erase p₀ \ n) * l n)
    (hinv : del ℚ s p₀ * y = 0) :
    ∃ z : ℚ, IsZ2 z ∧ aug y = (∏ p, (2 : ℚ) ^ s p) * z := by
  obtain ⟨X, hX, μ, hXμ⟩ := exists_K_decomp π u hπ c hc p₀
  obtain ⟨W, hW, hWy⟩ := K_transfer π u hπ (Finset.univ.erase p₀) l hl hX
  rw [← hy] at hWy
  -- the image of `c N_m = X + (1 - t_{p₀}) μ` in `ℚ[S]`
  have h1 : single 0 ((∏ p ∈ Finset.univ.erase p₀, c p : ℤ) : ℚ) *
      normElt s (Finset.univ.erase p₀) = toQ s X + del ℚ s p₀ * toQ s μ := by
    have h := congrArg (toQ s) hXμ
    rw [map_mul, map_add, map_mul, toQ_del, toQ_NP, map_intCast,
      AddMonoidAlgebra.intCast_def] at h
    exact h
  have h2 : single 0 ((∏ p ∈ Finset.univ.erase p₀, c p : ℤ) : ℚ) *
      (normElt s (Finset.univ.erase p₀) * y) = aProd π u (Finset.univ.erase p₀) * W := by
    linear_combination y * h1 + toQ s μ * hinv + hWy
  -- `N_m y` is a multiple of `N_S`
  have h3 : normElt s (Finset.univ.erase p₀) * y =
      single 0 (aug y / 2 ^ s p₀) * normElt s Finset.univ := by
    have hn := nrm_mul_of_del_mul ℚ s hinv
    have hu : normElt s Finset.univ = nrm ℚ s p₀ * normElt s (Finset.univ.erase p₀) := by
      rw [normElt_eq_prod, normElt_eq_prod, Finset.mul_prod_erase _ _ (Finset.mem_univ p₀)]
    have h2' : (2 : GRing s) ^ s p₀ = single 0 ((2 : ℚ) ^ s p₀) := by
      rw [AddMonoidAlgebra.ofNat_def, AddMonoidAlgebra.single_pow, nsmul_zero]
    rw [h2'] at hn
    have h4 : single 0 ((2 : ℚ) ^ s p₀) * (normElt s (Finset.univ.erase p₀) * y) =
        single 0 (aug y) * normElt s Finset.univ := by
      rw [← mul_normElt_univ, hu]
      linear_combination (-(normElt s (Finset.univ.erase p₀))) * hn
    have h5 := congrArg (fun t => single (0 : Grp s) (1 / (2 : ℚ) ^ s p₀) * t) h4
    simp only [single_zero_mul_mul] at h5
    have h6 : 1 / (2 : ℚ) ^ s p₀ * 2 ^ s p₀ = 1 := by field_simp
    have h7 : 1 / (2 : ℚ) ^ s p₀ * aug y = aug y / 2 ^ s p₀ := by ring
    rw [h6, h7, ← AddMonoidAlgebra.one_def, one_mul] at h5
    exact h5
  have h4 : aProd π u (Finset.univ.erase p₀) * normElt s Finset.univ =
      single 0 (∏ p ∈ Finset.univ.erase p₀, ((π p : ℚ) - 1)) * normElt s Finset.univ := by
    rw [mul_normElt_univ, aug_aProd]
  have hT : (∏ p, (2 : ℚ) ^ s p) = 2 ^ s p₀ * ∏ p ∈ Finset.univ.erase p₀, (2 : ℚ) ^ s p :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ p₀)).symm
  have hP : ∏ p ∈ Finset.univ.erase p₀, ((π p : ℚ) - 1) =
      (∏ p ∈ Finset.univ.erase p₀, (2 : ℚ) ^ s p) *
        ((∏ p ∈ Finset.univ.erase p₀, c p : ℤ) : ℚ) := by
    push_cast
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    have h := hc p
    have h' : ((π p - 1 : ℤ) : ℚ) = ((2 ^ s p * c p : ℤ) : ℚ) := by rw [h]
    push_cast at h'
    exact h'
  have hT0 : (∏ p, (2 : ℚ) ^ s p) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => by positivity
  have hE0 : (∏ p ∈ Finset.univ.erase p₀, (2 : ℚ) ^ s p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p _ => by positivity
  have hWeq : W = single 0 (aug y / ∏ p, (2 : ℚ) ^ s p) * normElt s Finset.univ := by
    have e1 : aProd π u (Finset.univ.erase p₀) * W =
        single 0 (((∏ p ∈ Finset.univ.erase p₀, c p : ℤ) : ℚ) * (aug y / 2 ^ s p₀)) *
          normElt s Finset.univ := by
      rw [← h2, h3, single_zero_mul_mul]
    have e2 : aProd π u (Finset.univ.erase p₀) *
        (single 0 (aug y / ∏ p, (2 : ℚ) ^ s p) * normElt s Finset.univ) =
        single 0 (aug y / (∏ p, (2 : ℚ) ^ s p) *
          ∏ p ∈ Finset.univ.erase p₀, ((π p : ℚ) - 1)) * normElt s Finset.univ := by
      rw [mul_left_comm, h4, single_zero_mul_mul]
    have e3 : ((∏ p ∈ Finset.univ.erase p₀, c p : ℤ) : ℚ) * (aug y / 2 ^ s p₀) =
        aug y / (∏ p, (2 : ℚ) ^ s p) * ∏ p ∈ Finset.univ.erase p₀, ((π p : ℚ) - 1) := by
      rw [hT, hP]
      field_simp
    have e4 : aProd π u (Finset.univ.erase p₀) *
        (W - single 0 (aug y / ∏ p, (2 : ℚ) ^ s p) * normElt s Finset.univ) = 0 := by
      rw [mul_sub, e1, e2, e3, sub_self]
    exact sub_eq_zero.1 (aProd_cancel π u hπ _ e4)
  have hcoeff : W.coeff 0 = aug y / ∏ p, (2 : ℚ) ^ s p := by
    rw [hWeq, AddMonoidAlgebra.coeff_single_zero_mul, coeff_normElt_univ, mul_one]
  refine ⟨aug y / ∏ p, (2 : ℚ) ^ s p, ?_, ?_⟩
  · rw [← hcoeff]
    exact hW 0
  · field_simp

end Abs

end Erdos

end PiFormula
