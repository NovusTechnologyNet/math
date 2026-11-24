/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.OkadaDefs
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Okada's criterion: a function on the units is determined by its twisted sums

`okadaUnitNonvanishing_of`: `OkadaUnitNonvanishing` follows from `OkadaHarmonicDiverges` and
`OkadaLOne`.

Let `u` be a real function on `ℤ/q`, `U = (ℤ/q)ˣ`, and `S'_N(v) = ∑_{n < N, gcd(n,q) = 1} v(n)/n`.
Assume `S'_N(n ↦ u(h n)) → c` for every `h ∈ U`.

1. Summing over `h`: `(∑_{b ∈ U} u(b)) S'_N(1) → |U| c`. As `S'_N(1) → ∞`, `∑_b u(b) = 0`, and
   then `c = 0`.
2. For a Dirichlet character `χ` modulo `q` (`sum_char_mul_unitSum`):
   `∑_h χ(h) S'_N(n ↦ u(h n)) = (∑_b χ(b) u(b)) ∑_{n < N} χ⁻¹(n)/n`.
   The left side tends to `0`; for `χ ≠ 1` the last factor tends to a non-zero number
   (`OkadaLOne` for `χ⁻¹`). So `∑_b χ(b) u(b) = 0` for every `χ` (for `χ = 1` by step 1).
3. By the orthogonality of the characters, `u(a) = 0` for every `a ∈ U`.
-/

@[expose] public section

open scoped BigOperators

open Filter

namespace PiFormula

namespace Erdos

namespace Okada

/-- For `n` prime to `q`, `∑_h χ(h) u(h n) = χ⁻¹(n) ∑_b χ(b) u(b)`. -/
theorem sum_char_mul_twist {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : ZMod q → ℝ)
    {n : ℕ} (hn : n.Coprime q) :
    ∑ h : (ZMod q)ˣ, χ (h : ZMod q) * (u ((h : ZMod q) * (n : ZMod q)) : ℂ) =
      χ⁻¹ (n : ZMod q) * ∑ b : (ZMod q)ˣ, χ (b : ZMod q) * (u (b : ZMod q) : ℂ) := by
  have hun : ((ZMod.unitOfCoprime n hn : (ZMod q)ˣ) : ZMod q) = (n : ZMod q) :=
    ZMod.coe_unitOfCoprime n hn
  have hχn : χ (n : ZMod q) ≠ 0 := by
    rw [← hun]
    exact ((ZMod.unitOfCoprime n hn).isUnit.map χ).ne_zero
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight (ZMod.unitOfCoprime n hn)) _ _ fun h => ?_
  simp only [Equiv.coe_mulRight, Units.val_mul, hun, map_mul, MulChar.inv_apply_eq_inv']
  field_simp

/-- `∑_h χ(h) S'_N(n ↦ u(h n)) = (∑_b χ(b) u(b)) ∑_{n < N} χ⁻¹(n)/n`. -/
theorem sum_char_mul_unitSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : ZMod q → ℝ)
    (N : ℕ) :
    ∑ h : (ZMod q)ˣ, χ (h : ZMod q) *
        ((unitSum q (fun n => u ((h : ZMod q) * n)) N : ℝ) : ℂ) =
      (∑ b : (ZMod q)ˣ, χ (b : ZMod q) * (u (b : ZMod q) : ℂ)) *
        ∑ n ∈ Finset.range N, χ⁻¹ (n : ZMod q) / (n : ℂ) := by
  unfold unitSum
  simp only [Complex.ofReal_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n.Coprime q
  · have hn' : n.Coprime q = True := eq_true hn
    have e : ∑ h : (ZMod q)ˣ, χ (h : ZMod q) *
          (((if n.Coprime q then u ((h : ZMod q) * (n : ZMod q)) / (n : ℝ) else 0 : ℝ)) : ℂ) =
        (∑ h : (ZMod q)ˣ, χ (h : ZMod q) * (u ((h : ZMod q) * (n : ZMod q)) : ℂ)) / (n : ℂ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [hn', ↓reduceIte, Complex.ofReal_div, Complex.ofReal_natCast]
      ring
    rw [e, sum_char_mul_twist χ u hn]
    ring
  · have h0 : χ⁻¹ (n : ZMod q) = 0 :=
      MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
    simp only [hn, ↓reduceIte, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero, h0,
      zero_div]

/-- The real case `χ = 1`: `∑_h S'_N(n ↦ u(h n)) = (∑_b u(b)) S'_N(1)`. -/
theorem sum_unitSum_twist {q : ℕ} [NeZero q] (u : ZMod q → ℝ) (N : ℕ) :
    ∑ h : (ZMod q)ˣ, unitSum q (fun n => u ((h : ZMod q) * n)) N =
      (∑ b : (ZMod q)ˣ, u (b : ZMod q)) * unitSum q (fun _ => 1) N := by
  unfold unitSum
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n.Coprime q
  · have e : ∑ h : (ZMod q)ˣ, u ((h : ZMod q) * (n : ZMod q)) =
        ∑ b : (ZMod q)ˣ, u (b : ZMod q) :=
      Fintype.sum_equiv (Equiv.mulRight (ZMod.unitOfCoprime n hn)) _ _ fun h => by
        simp only [Equiv.coe_mulRight, Units.val_mul, ZMod.coe_unitOfCoprime]
    have hn' : n.Coprime q = True := eq_true hn
    simp only [hn', ↓reduceIte]
    rw [← Finset.sum_div, e]
    ring
  · simp only [hn, ↓reduceIte, Finset.sum_const_zero, mul_zero]

end Okada

open Okada

/-- **The second half, the part on the units.** If the sums of `u(h n)/n` over the `n` prime
to `q` tend to the same number `c` for every unit `h`, then `c = 0` and `u = 0` on the units. -/
theorem okadaUnitNonvanishing_of (hH : OkadaHarmonicDiverges) (hX : OkadaLOne) :
    OkadaUnitNonvanishing := by
  intro q _ hq u c hyp
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
    exact not_tendsto_atTop_of_tendsto_nhds h1 (hH q hq)
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
    · obtain ⟨L, hL0, hL⟩ := hX q hq χ⁻¹ (inv_ne_one.2 hχ)
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
