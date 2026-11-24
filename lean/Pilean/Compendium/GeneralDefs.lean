/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Compendium.Defs

/-!
# Bailey's Compendium, general bases: the statements with a real parameter

Section 11 of the Compendium ("General bases", formulas 90 to 110) lists identities in a
parameter `b`: the base and the coefficients of `P(1, β, N, A)` are polynomials in `b`. The paper
does not say what `b` is in that section; its definition (5) of `P(s, b, n, A)` says that `s`,
`b` and `n` are integers and `A` a vector of integers. The identities hold for real `b`, so they
are stated here with a real base and real coefficients:

* `baileyBlockReal β N a j = β^(-j) ∑_{i=1}^{N} a_i / (N j + i)`, block `j` of `P(1, β, N, a)`;
* `HasBaileyValueReal β N a x`: the series `P(1, β, N, a)` converges to `x`;
* `BaileyFormulaReal x c β N a`: `x = c · P(1, β, N, a)`.

For an integer base and rational coefficients these are the statements of `Defs.lean`
(`baileyFormulaReal_natCast`, `baileyFormulaReal_intCast`; `BaileyFormulaReal.to_nat` and
`BaileyFormulaReal.to_int` are the forms used to specialise a formula to a natural `b`).

The toolbox:

* linearity (`HasBaileyValueReal.smul`, `.add`, `.sub`, `.of_eq`);
* `hasBaileyValueReal_of_quasiperiodic`: a series `∑_{n ≥ 1} u(n) / n` with
  `u(n + N) = u(n) / β` is `P(1, β, N, (u(1), …, u(N)))`;
* `hasSum_pow_im_div`, `hasSum_pow_re_div`: the imaginary and real parts of
  `∑_{n ≥ 1} z^n / n = -log (1 - z)` for `‖z‖ < 1`, with the values `arctan (Im z / (1 - Re z))`
  and `-(1/2) log ((1 - Re z)² + (Im z)²)`;
* `hasBaileyValueReal_im`, `hasBaileyValueReal_re`: for a complex number `c` with `c^N = ρ` real
  and a real `v`, the series `∑ v^n Im(c^n) / n` and `∑ v^n Re(c^n) / n` are
  `P(1, β, N, ·)` with `β = 1 / (ρ v^N)`.
-/

@[expose] public section

namespace PiFormula

namespace Compendium

open BaseB

/-! ## 1. The statements -/

/-- Block `j` of Bailey's series `P(1, β, N, a)` for a real base `β` and real coefficients:
`β^(-j) ∑_{i=1}^{N} a_i / (N j + i)`; `a i` (`i : Fin N`) is `a_(i+1)`. -/
noncomputable def baileyBlockReal (β : ℝ) (N : ℕ) (a : Fin N → ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin N, a i / β ^ j / ((N * j + i + 1 : ℕ) : ℝ)

/-- Bailey's series `P(1, β, N, a)`, with a real base and real coefficients, converges to
`x`. -/
def HasBaileyValueReal (β : ℝ) (N : ℕ) (a : Fin N → ℝ) (x : ℝ) : Prop :=
  HasSum (baileyBlockReal β N a) x

/-- A formula with a real base and real coefficients: `x = c · P(1, β, N, a)`. The series
converges, and `c` times its sum is `x`. -/
def BaileyFormulaReal (x c β : ℝ) (N : ℕ) (a : Fin N → ℝ) : Prop :=
  ∃ S : ℝ, HasBaileyValueReal β N a S ∧ x = c * S

theorem HasBaileyValueReal.formula {β : ℝ} {N : ℕ} {a : Fin N → ℝ} {S : ℝ}
    (h : HasBaileyValueReal β N a S) {x c : ℝ} (e : x = c * S) : BaileyFormulaReal x c β N a :=
  ⟨S, h, e⟩

/-- A formula as one convergent series: `∑_j c · (block j) = x`. -/
theorem BaileyFormulaReal.hasSum {x c β : ℝ} {N : ℕ} {a : Fin N → ℝ}
    (h : BaileyFormulaReal x c β N a) : HasSum (fun j => c * baileyBlockReal β N a j) x := by
  obtain ⟨S, hS, rfl⟩ := h
  exact HasSum.mul_left c hS

/-! ## 2. The bridge to an integer base and rational coefficients -/

/-- For a base `b^B` with `b` natural and rational coefficients, `baileyBlockReal` is
`BaseB.baileyBlock`. -/
theorem baileyBlockReal_natCast (b B N : ℕ) (a : Fin N → ℚ) :
    baileyBlockReal ((b : ℝ) ^ B) N (fun i => (a i : ℝ)) = BaseB.baileyBlock b B N a := by
  funext j
  simp only [baileyBlockReal, BaseB.baileyBlock, ← pow_mul]

/-- For a base `β^B` with `β` an integer and rational coefficients, `baileyBlockReal` is
`BaseB.baileyBlockInt`. -/
theorem baileyBlockReal_intCast (β : ℤ) (B N : ℕ) (a : Fin N → ℚ) :
    baileyBlockReal ((β : ℝ) ^ B) N (fun i => (a i : ℝ)) = baileyBlockInt β B N a := by
  funext j
  simp only [baileyBlockReal, baileyBlockInt, ← pow_mul]

theorem hasBaileyValueReal_natCast {b B N : ℕ} {a : Fin N → ℚ} {x : ℝ} :
    HasBaileyValueReal ((b : ℝ) ^ B) N (fun i => (a i : ℝ)) x ↔ HasBaileyValue b B N a x := by
  rw [HasBaileyValueReal, baileyBlockReal_natCast, HasBaileyValue]

theorem hasBaileyValueReal_intCast {β : ℤ} {B N : ℕ} {a : Fin N → ℚ} {x : ℝ} :
    HasBaileyValueReal ((β : ℝ) ^ B) N (fun i => (a i : ℝ)) x ↔ HasBaileyValueInt β B N a x := by
  rw [HasBaileyValueReal, baileyBlockReal_intCast, HasBaileyValueInt]

/-- **The bridge, natural base.** With the base `b^B` (`b` natural) and rational coefficients,
`BaileyFormulaReal` is `BaileyFormula`. -/
theorem baileyFormulaReal_natCast {x c : ℝ} {b B N : ℕ} {a : Fin N → ℚ} :
    BaileyFormulaReal x c ((b : ℝ) ^ B) N (fun i => (a i : ℝ)) ↔ BaileyFormula x c b B N a := by
  simp only [BaileyFormulaReal, BaileyFormula, hasBaileyValueReal_natCast]

/-- **The bridge, integer base.** With the base `β^B` (`β` an integer, possibly negative) and
rational coefficients, `BaileyFormulaReal` is `BaileyFormulaInt`. -/
theorem baileyFormulaReal_intCast {x c : ℝ} {β : ℤ} {B N : ℕ} {a : Fin N → ℚ} :
    BaileyFormulaReal x c ((β : ℝ) ^ B) N (fun i => (a i : ℝ)) ↔
      BaileyFormulaInt x c β B N a := by
  simp only [BaileyFormulaReal, BaileyFormulaInt, hasBaileyValueReal_intCast]

/-- A real formula whose base is `b^B` and whose coefficients are rational is a formula in the
sense of `BaileyFormula`. -/
theorem BaileyFormulaReal.to_nat {x c β : ℝ} {N : ℕ} {a' : Fin N → ℝ}
    (h : BaileyFormulaReal x c β N a') {b B : ℕ} {a : Fin N → ℚ} (hβ : β = (b : ℝ) ^ B)
    (ha : ∀ i, a' i = (a i : ℝ)) : BaileyFormula x c b B N a := by
  have e : a' = fun i => (a i : ℝ) := funext ha
  rw [hβ, e] at h
  exact baileyFormulaReal_natCast.1 h

/-- A real formula whose base is `γ^B`, `γ` an integer, and whose coefficients are rational is
a formula in the sense of `BaileyFormulaInt`. -/
theorem BaileyFormulaReal.to_int {x c β : ℝ} {N : ℕ} {a' : Fin N → ℝ}
    (h : BaileyFormulaReal x c β N a') {γ : ℤ} {B : ℕ} {a : Fin N → ℚ} (hβ : β = (γ : ℝ) ^ B)
    (ha : ∀ i, a' i = (a i : ℝ)) : BaileyFormulaInt x c γ B N a := by
  have e : a' = fun i => (a i : ℝ) := funext ha
  rw [hβ, e] at h
  exact baileyFormulaReal_intCast.1 h

/-! ## 3. Linearity -/

theorem baileyBlockReal_smul (β : ℝ) (N : ℕ) (r : ℝ) (a : Fin N → ℝ) (j : ℕ) :
    baileyBlockReal β N (r • a) j = r * baileyBlockReal β N a j := by
  simp only [baileyBlockReal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem baileyBlockReal_add (β : ℝ) (N : ℕ) (a a' : Fin N → ℝ) (j : ℕ) :
    baileyBlockReal β N (a + a') j = baileyBlockReal β N a j + baileyBlockReal β N a' j := by
  simp only [baileyBlockReal, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem HasBaileyValueReal.of_eq {β β' : ℝ} {N : ℕ} {a a' : Fin N → ℝ} {x x' : ℝ}
    (h : HasBaileyValueReal β N a x) (eβ : β' = β) (ea : a' = a) (ex : x' = x) :
    HasBaileyValueReal β' N a' x' := by
  rw [eβ, ea, ex]
  exact h

theorem HasBaileyValueReal.smul {β : ℝ} {N : ℕ} {a : Fin N → ℝ} {x : ℝ} (r : ℝ)
    (h : HasBaileyValueReal β N a x) : HasBaileyValueReal β N (r • a) (r * x) := by
  have e : baileyBlockReal β N (r • a) = fun j => r * baileyBlockReal β N a j :=
    funext fun j => baileyBlockReal_smul β N r a j
  rw [HasBaileyValueReal, e]
  exact HasSum.mul_left r h

theorem HasBaileyValueReal.add {β : ℝ} {N : ℕ} {a a' : Fin N → ℝ} {x x' : ℝ}
    (h : HasBaileyValueReal β N a x) (h' : HasBaileyValueReal β N a' x') :
    HasBaileyValueReal β N (a + a') (x + x') := by
  have e : baileyBlockReal β N (a + a') =
      fun j => baileyBlockReal β N a j + baileyBlockReal β N a' j :=
    funext fun j => baileyBlockReal_add β N a a' j
  rw [HasBaileyValueReal, e]
  exact HasSum.add h h'

theorem HasBaileyValueReal.sub {β : ℝ} {N : ℕ} {a a' : Fin N → ℝ} {x x' : ℝ}
    (h : HasBaileyValueReal β N a x) (h' : HasBaileyValueReal β N a' x') :
    HasBaileyValueReal β N (a - a') (x - x') := by
  refine (h.add (h'.smul (-1))).of_eq rfl ?_ ?_
  · rw [neg_one_smul, sub_eq_add_neg]
  · ring

/-! ## 4. Regrouping a series `∑ u(n) / n` with `u(n + N) = u(n) / β` -/

theorem quasiperiodic_mul {N : ℕ} {u : ℕ → ℝ} {β : ℝ} (hu : ∀ n, u (n + N) = u n / β)
    (n j : ℕ) : u (n + N * j) = u n / β ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.mul_succ, ← add_assoc, hu, ih, pow_succ, div_div]

/-- **Regrouping.** If `u(n + N) = u(n) / β` for every `n` and `∑_{n ≥ 1} u(n) / n = S`, then
`P(1, β, N, (u(1), …, u(N))) = S`: block `j` is the sum of the terms `N j + 1, …, N j + N`. -/
theorem hasBaileyValueReal_of_quasiperiodic {N : ℕ} (hN : 0 < N) {u : ℕ → ℝ} {β : ℝ}
    (hu : ∀ n, u (n + N) = u n / β) {S : ℝ} (h : HasSum (fun n : ℕ => u n / (n : ℝ)) S) :
    HasBaileyValueReal β N (fun i => u ((i : ℕ) + 1)) S := by
  have h' := (hasSum_blocks_iff hN h.summable (by simp) S).2 h
  refine h'.congr_fun fun j => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : N * j + (i : ℕ) + 1 = (i : ℕ) + 1 + N * j := by ring
  have e2 : u (N * j + (i : ℕ) + 1) = u ((i : ℕ) + 1) / β ^ j := by
    rw [e1, quasiperiodic_mul hu]
  rw [e2]

/-! ## 5. The real and imaginary parts of `∑ z^n / n = -log (1 - z)` -/

/-- `∑_{n ≥ 1} Im(z^n) / n = arctan (Im z / (1 - Re z))` for `‖z‖ < 1`: the imaginary part of
the series of `-log (1 - z)`. The term at `n = 0` is `0`. -/
theorem hasSum_pow_im_div {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (z ^ n).im / (n : ℝ)) (Real.arctan (z.im / (1 - z.re))) := by
  have hre : 0 < (1 - z).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith [z.re_le_norm]
  have harg : (1 - z).arg = -Real.arctan (z.im / (1 - z.re)) := by
    have h1 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
    rw [abs_lt] at h1
    rw [← Real.arctan_neg, ← Real.arctan_tan h1.1 h1.2, Complex.tan_arg, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub, neg_div]
  have h := Complex.hasSum_im (Complex.hasSum_taylorSeries_neg_log hz)
  rw [Complex.neg_im, Complex.log_im, harg, neg_neg] at h
  refine h.congr_fun fun n => ?_
  rw [Complex.div_natCast_im]

/-- `∑_{n ≥ 1} Re(z^n) / n = -(1/2) log ((1 - Re z)² + (Im z)²)` for `‖z‖ < 1`: the real part
of the series of `-log (1 - z)`. The term at `n = 0` is `1 / 0 = 0`. -/
theorem hasSum_pow_re_div {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (z ^ n).re / (n : ℝ))
      (-(1 / 2) * Real.log ((1 - z.re) ^ 2 + z.im ^ 2)) := by
  have hnorm : ‖1 - z‖ ^ 2 = (1 - z.re) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im]
    ring
  have hlog : Real.log ‖1 - z‖ = 1 / 2 * Real.log (‖1 - z‖ ^ 2) := by
    rw [Real.log_pow]
    push_cast
    ring
  have h := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz)
  rw [Complex.neg_re, Complex.log_re, hlog, hnorm] at h
  have e : -(1 / 2 * Real.log ((1 - z.re) ^ 2 + z.im ^ 2)) =
      -(1 / 2) * Real.log ((1 - z.re) ^ 2 + z.im ^ 2) := by ring
  rw [e] at h
  refine h.congr_fun fun n => ?_
  rw [Complex.div_natCast_re]

/-! ## 6. Patterns `v^n Im(c^n)` and `v^n Re(c^n)` with `c^N` real -/

theorem smul_pow_im (v : ℝ) (c : ℂ) (n : ℕ) : (((v : ℂ) * c) ^ n).im = v ^ n * (c ^ n).im := by
  rw [mul_pow, ← Complex.ofReal_pow, Complex.im_ofReal_mul]

theorem smul_pow_re (v : ℝ) (c : ℂ) (n : ℕ) : (((v : ℂ) * c) ^ n).re = v ^ n * (c ^ n).re := by
  rw [mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

/-- `‖v c‖ < 1` when `v² |c|² < 1`. -/
theorem norm_smul_lt_one {v : ℝ} {c : ℂ} (h : v ^ 2 * Complex.normSq c < 1) :
    ‖(v : ℂ) * c‖ < 1 := by
  have e : ‖(v : ℂ) * c‖ ^ 2 = v ^ 2 * Complex.normSq c := by
    rw [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  rw [← e] at h
  exact (sq_lt_one_iff₀ (norm_nonneg _)).1 h

/-- **The pattern `v^n Im(c^n)`.** Let `c^N = ρ` be real, `v` real with `v² |c|² < 1`, and
`β ρ v^N = 1`. Then `P(1, β, N, a) = arctan (v Im c / (1 - v Re c))` with
`a_i = v^i Im(c^i)`. -/
theorem hasBaileyValueReal_im {c : ℂ} {ρ : ℝ} {N : ℕ} (hN : 0 < N) (hc : c ^ N = (ρ : ℂ))
    {v β : ℝ} (hβ : v ^ N * ρ * β = 1) (hz : v ^ 2 * Complex.normSq c < 1) :
    HasBaileyValueReal β N (fun i => v ^ ((i : ℕ) + 1) * (c ^ ((i : ℕ) + 1)).im)
      (Real.arctan (v * c.im / (1 - v * c.re))) := by
  have hβ0 : β ≠ 0 := fun h0 => by simp [h0] at hβ
  have hu : ∀ n : ℕ, v ^ (n + N) * (c ^ (n + N)).im = v ^ n * (c ^ n).im / β := by
    intro n
    rw [pow_add c, hc, Complex.im_mul_ofReal, pow_add v, eq_div_iff hβ0]
    linear_combination (v ^ n * (c ^ n).im) * hβ
  have h := hasSum_pow_im_div (norm_smul_lt_one hz)
  rw [Complex.im_ofReal_mul, Complex.re_ofReal_mul] at h
  have h2 : HasSum (fun n : ℕ => v ^ n * (c ^ n).im / (n : ℝ))
      (Real.arctan (v * c.im / (1 - v * c.re))) :=
    h.congr_fun fun n => by rw [smul_pow_im]
  exact hasBaileyValueReal_of_quasiperiodic (u := fun n => v ^ n * (c ^ n).im) hN hu h2

/-- **The pattern `v^n Re(c^n)`.** Let `c^N = ρ` be real, `v` real with `v² |c|² < 1`, and
`β ρ v^N = 1`. Then `P(1, β, N, a) = -(1/2) log ((1 - v Re c)² + (v Im c)²)` with
`a_i = v^i Re(c^i)`. -/
theorem hasBaileyValueReal_re {c : ℂ} {ρ : ℝ} {N : ℕ} (hN : 0 < N) (hc : c ^ N = (ρ : ℂ))
    {v β : ℝ} (hβ : v ^ N * ρ * β = 1) (hz : v ^ 2 * Complex.normSq c < 1) :
    HasBaileyValueReal β N (fun i => v ^ ((i : ℕ) + 1) * (c ^ ((i : ℕ) + 1)).re)
      (-(1 / 2) * Real.log ((1 - v * c.re) ^ 2 + (v * c.im) ^ 2)) := by
  have hβ0 : β ≠ 0 := fun h0 => by simp [h0] at hβ
  have hu : ∀ n : ℕ, v ^ (n + N) * (c ^ (n + N)).re = v ^ n * (c ^ n).re / β := by
    intro n
    rw [pow_add c, hc, Complex.re_mul_ofReal, pow_add v, eq_div_iff hβ0]
    linear_combination (v ^ n * (c ^ n).re) * hβ
  have h := hasSum_pow_re_div (norm_smul_lt_one hz)
  rw [Complex.im_ofReal_mul, Complex.re_ofReal_mul] at h
  have h2 : HasSum (fun n : ℕ => v ^ n * (c ^ n).re / (n : ℝ))
      (-(1 / 2) * Real.log ((1 - v * c.re) ^ 2 + (v * c.im) ^ 2)) :=
    h.congr_fun fun n => by rw [smul_pow_re]
  exact hasBaileyValueReal_of_quasiperiodic (u := fun n => v ^ n * (c ^ n).re) hN hu h2

end Compendium

end PiFormula
