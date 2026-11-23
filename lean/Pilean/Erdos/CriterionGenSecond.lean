import Pilean.Erdos.OkadaReduction
import Pilean.Erdos.OkadaLayer
import Pilean.Erdos.OkadaLOne
import Pilean.Erdos.OkadaGlueChar
import Pilean.Erdos.EvenCase

/-!
# Okada's criterion for every `q ≥ 1`: the second half

The second half of the criterion without the hypotheses `Odd q` and `f 0 = 0` of
`OkadaDefs.lean` (which no proof uses), for every modulus `q ≥ 1` and every rational `f` on
`ℤ/q`:

* `harmonicDiverges_gen`: the sum of `1/n` over the `n` prime to `q` diverges;
* `unitReduction_gen`: `S_N(f) - S'_N(g) → -(1/q) ∑_{p ∣ q} ℓ_p log p`, with `g = okadaG q f`,
  `S'_N` the sum over the `n` prime to `q`, and `ℓ_p = Okada.layerSum q f p`;
* `layerSum_gen`: `ℓ_p = c_p` (`okadaC`);
* `unitNonvanishing_gen`: if the sums of `u(h n)/n` over the `n` prime to `q` tend to the same
  number `c` for every unit `h`, then `c = 0` and `u = 0` on the units (`L(1, χ) ≠ 0`).

The proofs are those of `OkadaGlueWindow.lean`, `OkadaReduction.lean`, `OkadaLayer.lean` and
`OkadaGlueChar.lean`, with the lemmas of these files and the window sums for every `q`
(`tendsto_windowSum`, `EvenCase.lean`); only the steps that mention `Odd q` are repeated.
-/

open scoped BigOperators

open Filter Finset

namespace PiFormula

namespace Erdos

open Okada

/-! ## 1. The harmonic sum over the `n` prime to `q` -/

/-- The sum of `1/n` over the `n` prime to `q` diverges, for every `q ≥ 1`. -/
theorem harmonicDiverges_gen (q : ℕ) [NeZero q] :
    Tendsto (unitSum q fun _ => 1) atTop atTop := by
  have hmono : Monotone (unitSum q fun _ => (1 : ℝ)) := by
    refine monotone_nat_of_le_succ fun N => ?_
    unfold unitSum
    rw [Finset.sum_range_succ]
    refine le_add_of_nonneg_right ?_
    split_ifs
    · positivity
    · exact le_rfl
  rcases tendsto_atTop_of_monotone hmono with h | ⟨l, hl⟩
  · exact h
  · exfalso
    have h2 : Tendsto (fun N : ℕ => unitSum q (fun _ => (1 : ℝ)) (2 * N) -
        unitSum q (fun _ => (1 : ℝ)) N) atTop (nhds (l - l)) :=
      (hl.comp tendsto_two_mul_atTop).sub hl
    rw [sub_self] at h2
    have h3 : ∀ N : ℕ,
        (∑ n ∈ Finset.Ico N (2 * N), if (n : ZMod q) = 1 then 1 / (n : ℝ) else 0) ≤
          unitSum q (fun _ => (1 : ℝ)) (2 * N) - unitSum q (fun _ => (1 : ℝ)) N := by
      intro N
      unfold unitSum
      rw [← Finset.sum_Ico_eq_sub _ (show N ≤ 2 * N by omega)]
      refine Finset.sum_le_sum fun n _ => ?_
      by_cases hn : (n : ZMod q) = 1
      · have hc : n.Coprime q := (ZMod.isUnit_iff_coprime n q).1 (hn ▸ isUnit_one)
        simp only [hn, ↓reduceIte]
        split_ifs
        exact le_rfl
      · simp only [hn, ↓reduceIte]
        split_ifs
        · positivity
        · exact le_rfl
    have h5 := le_of_tendsto_of_tendsto'
      (tendsto_windowSum q (show 0 < 2 by norm_num) 1) h2 h3
    exact absurd h5 (not_le.2 (log_two_div_pos q))

/-! ## 2. Reduction to the units -/

/-- **One prime**, for every `q ≥ 1`: `R_m(N) - R_M(N) → -(log p / q) κ(M, p)` for
`M = m ∪ {p}` (notation of `OkadaReduction.lean`). -/
theorem red_step_gen {q : ℕ} [NeZero q] (f : ZMod q → ℚ) {m : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ q) (hpm : p ∉ m) (hm : ∀ l ∈ m, l.Prime) :
    Tendsto (fun N : ℕ => red_R q f m N - red_R q f (insert p m) N) atTop
      (nhds (-(red_kappa q f (insert p m) p * Real.log (p : ℝ) / (q : ℝ)))) := by
  have hv : ∀ r : ZMod q, ¬ (p : ZMod q) ∣ r → red_v q f (insert p m) p r = 0 := by
    intro r hr
    simp only [red_v, hr, false_and, ↓reduceIte]
  have h : ∀ N : ℕ, -∑ n ∈ Ico N (p * N), red_v q f (insert p m) p (n : ZMod q) / (n : ℝ) =
      red_R q f m N - red_R q f (insert p m) N := by
    intro N
    rw [← red_sum_shift hp.pos hpq (red_v q f (insert p m) p) hv N]
    unfold red_R
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← sub_div, red_u_sub f hp hpm hm]
  refine Tendsto.congr h ?_
  exact (tendsto_windowSum_mul q hp.pos (red_v q f (insert p m) p)).neg

/-- `R_∅(N) - R_m(N) → -(1/q) ∑_{p ∈ m} κ(m, p) log p` for a set `m` of primes dividing `q`,
for every `q ≥ 1`. -/
theorem red_tendsto_sub_gen {q : ℕ} [NeZero q] (f : ZMod q → ℚ) :
    ∀ m : Finset ℕ, m ⊆ q.primeFactors →
      Tendsto (fun N : ℕ => red_R q f ∅ N - red_R q f m N) atTop
        (nhds (-((∑ p ∈ m, red_kappa q f m p * Real.log (p : ℝ)) / (q : ℝ)))) := by
  classical
  intro m
  induction m using Finset.induction_on with
  | empty =>
    intro _
    simp only [sub_self, Finset.sum_empty, zero_div, neg_zero]
    exact tendsto_const_nhds
  | insert p m hpm ih =>
    intro hsub
    have hp := Nat.mem_primeFactors.1 (hsub (mem_insert_self p m))
    have hm' : m ⊆ q.primeFactors := fun l hl => hsub (mem_insert_of_mem hl)
    have hmP : ∀ l ∈ m, l.Prime := fun l hl => (Nat.mem_primeFactors.1 (hm' hl)).1
    have h1 := ih hm'
    have h2 := red_step_gen f hp.1 hp.2.1 hpm hmP
    have hsum : ∑ p' ∈ insert p m, red_kappa q f (insert p m) p' * Real.log (p' : ℝ) =
        red_kappa q f (insert p m) p * Real.log (p : ℝ) +
          ∑ p' ∈ m, red_kappa q f m p' * Real.log (p' : ℝ) := by
      rw [Finset.sum_insert hpm]
      congr 1
      refine Finset.sum_congr rfl fun p' hp' => ?_
      rw [red_kappa_insert f (hmP p' hp') hp.1 hp.2.1 hp' hpm hmP]
    have hlim : -((red_kappa q f (insert p m) p * Real.log (p : ℝ) +
        ∑ p' ∈ m, red_kappa q f m p' * Real.log (p' : ℝ)) / (q : ℝ)) =
        -((∑ p' ∈ m, red_kappa q f m p' * Real.log (p' : ℝ)) / (q : ℝ)) +
          -(red_kappa q f (insert p m) p * Real.log (p : ℝ) / (q : ℝ)) := by
      ring
    rw [hsum, hlim]
    refine Tendsto.congr (fun N => ?_) (h1.add h2)
    ring

/-- **Reduction to the units**, for every `q ≥ 1` and every rational `f` on `ℤ/q`:
`S_N(f) - S'_N(g) → -(1/q) ∑_{p ∣ q} ℓ_p log p`, with `g = okadaG q f` and
`ℓ_p = Okada.layerSum q f p`. -/
theorem unitReduction_gen (q : ℕ) [NeZero q] (f : ZMod q → ℚ) :
    Tendsto (fun N : ℕ => partialSum q f N - unitSum q (okadaG q f) N) atTop
      (nhds (-((∑ p ∈ q.primeFactors, layerSum q f p * Real.log (p : ℝ)) / (q : ℝ)))) := by
  have h := red_tendsto_sub_gen f q.primeFactors subset_rfl
  have hsum : ∑ p ∈ q.primeFactors, red_kappa q f q.primeFactors p * Real.log (p : ℝ) =
      ∑ p ∈ q.primeFactors, layerSum q f p * Real.log (p : ℝ) :=
    Finset.sum_congr rfl fun p _ => by rw [red_kappa_primeFactors]
  rw [hsum] at h
  refine h.congr fun N => ?_
  rw [red_R_empty, red_R_primeFactors]

/-- **The coefficient of `log p`**, for every `q ≥ 1`: `ℓ_p = c_p` for a prime `p ∣ q`. -/
theorem layerSum_gen (q : ℕ) [NeZero q] (f : ZMod q → ℚ) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ q) : layerSum q f p = (okadaC q f p : ℝ) := by
  rw [lay_okadaC f hp]
  exact lay_main f hp hpq (lay_w q p)
    (fun l hl hlq hne r' hr' => lay_w_fiber_ne hp hl hlq hne hr')
    (fun r' hr' => lay_w_fiber_self hp hpq hr')
    (fun r hr => lay_w_eq_zero hp hpq hr)

/-! ## 3. A function on the units is determined by its twisted sums -/

/-- For every `q ≥ 1`: if the sums of `u(h n)/n` over the `n` prime to `q` tend to the same
number `c` for every unit `h`, then `c = 0` and `u = 0` on the units. -/
theorem unitNonvanishing_gen (q : ℕ) [NeZero q] (u : ZMod q → ℝ) (c : ℝ)
    (hyp : ∀ h : (ZMod q)ˣ, Tendsto (unitSum q fun n => u ((h : ZMod q) * n))
      atTop (nhds c)) :
    c = 0 ∧ ∀ a : (ZMod q)ˣ, u (a : ZMod q) = 0 := by
  -- Step 1: `∑_b u(b) = 0` and `c = 0`
  have hlim1 : Tendsto (fun N : ℕ => (∑ b : (ZMod q)ˣ, u (b : ZMod q)) *
      unitSum q (fun _ => 1) N) atTop (nhds (∑ _h : (ZMod q)ˣ, c)) :=
    Tendsto.congr (sum_unitSum_twist u) (tendsto_finsetSum _ fun h _ => hyp h)
  have hs0 : ∑ b : (ZMod q)ˣ, u (b : ZMod q) = 0 := by
    by_contra hne
    have h1 : Tendsto (fun N : ℕ => unitSum q (fun _ => (1 : ℝ)) N) atTop
        (nhds ((∑ _h : (ZMod q)ˣ, c) / ∑ b : (ZMod q)ˣ, u (b : ZMod q))) := by
      refine (hlim1.div_const _).congr fun N => ?_
      rw [mul_div_assoc, mul_comm, div_mul_cancel₀ _ hne]
    exact not_tendsto_atTop_of_tendsto_nhds h1 (harmonicDiverges_gen q)
  have hc0 : c = 0 := by
    rw [hs0] at hlim1
    simp only [zero_mul] at hlim1
    have h2 := tendsto_nhds_unique hlim1 tendsto_const_nhds
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    have hcard : (Fintype.card (ZMod q)ˣ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    exact (mul_eq_zero.1 h2).resolve_left hcard
  refine ⟨hc0, ?_⟩
  -- Step 2: `∑_b χ(b) u(b) = 0` for every character `χ`
  have hchar : ∀ χ : DirichletCharacter ℂ q,
      ∑ b : (ZMod q)ˣ, χ (b : ZMod q) * (u (b : ZMod q) : ℂ) = 0 := by
    intro χ
    by_cases hχ : χ = 1
    · subst hχ
      simp only [MulChar.one_apply_coe, one_mul]
      rw [← Complex.ofReal_sum, hs0, Complex.ofReal_zero]
    · have hL0 : DirichletCharacter.LFunction χ⁻¹ 1 ≠ 0 :=
        DirichletCharacter.LFunction_apply_one_ne_zero (inv_ne_one.2 hχ)
      have hL := lone_tendsto q (inv_ne_one.2 hχ)
      have h1 : Tendsto (fun N : ℕ => ∑ h : (ZMod q)ˣ, χ (h : ZMod q) *
          ((unitSum q (fun n => u ((h : ZMod q) * n)) N : ℝ) : ℂ)) atTop
          (nhds (∑ h : (ZMod q)ˣ, χ (h : ZMod q) * ((c : ℝ) : ℂ))) :=
        tendsto_finsetSum _ fun h _ =>
          ((Complex.continuous_ofReal.tendsto c).comp (hyp h)).const_mul _
      simp only [sum_char_mul_unitSum, hc0, Complex.ofReal_zero, mul_zero,
        Finset.sum_const_zero] at h1
      have h2 := hL.const_mul (∑ b : (ZMod q)ˣ, χ (b : ZMod q) * (u (b : ZMod q) : ℂ))
      exact (mul_eq_zero.1 (tendsto_nhds_unique h2 h1)).resolve_right hL0
  -- Step 3: orthogonality of the characters
  intro a
  have hb : ∀ b : (ZMod q)ˣ,
      ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) * (χ (b : ZMod q) * (u (b : ZMod q) : ℂ)) =
        (if (a : ZMod q) = (b : ZMod q) then (q.totient : ℂ) else 0) * (u (b : ZMod q) : ℂ) := by
    intro b
    rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit (b : ZMod q), Finset.sum_mul]
    exact Finset.sum_congr rfl fun χ _ => by ring
  have hsum : ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) *
      ∑ b : (ZMod q)ˣ, χ (b : ZMod q) * (u (b : ZMod q) : ℂ) =
      (q.totient : ℂ) * (u (a : ZMod q) : ℂ) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [hb]
    rw [Finset.sum_eq_single a]
    · simp only [↓reduceIte]
    · intro b _ hba
      have hne : (a : ZMod q) ≠ (b : ZMod q) := fun h => hba (Units.ext h).symm
      simp only [hne, ↓reduceIte, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  have hzero : (q.totient : ℂ) * (u (a : ZMod q) : ℂ) = 0 := by
    rw [← hsum]
    exact Finset.sum_eq_zero fun χ _ => by rw [hchar χ, mul_zero]
  have hφ : (q.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have hu := (mul_eq_zero.1 hzero).resolve_left hφ
  exact_mod_cast hu

end Erdos

end PiFormula
