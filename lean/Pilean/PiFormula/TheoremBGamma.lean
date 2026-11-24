/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula.TheoremB

/-!
# Theorem B for the numbers `γ(O)` (Part II of pi_formula_theorem.md)

The note defines, with `t = 1 + i`, `g(r) = Im Log(1 - r/t)` for a root of unity `r`, and
`γ(O) = ∑_{r ∈ O} g(r)` for an orbit `O`. This file proves the two facts that connect `γ` with
the atoms of `TheoremB.lean`, and Theorem B in its `γ` form.

* `gamma_angle`: `γ(O) ≡ arg z_O - |O| π/4 (mod 2π)`, `z_O = ∏_{r ∈ O} (t - r)`;
* `gamma_partner`: `γ(O*) = -γ(O)`, `O* = { i conj r }`; so `γ(O) = 0` when `O* = O`;
* `abs_gfun_le`: `|g(r)| ≤ π/4` (used to pin down the exact values below).

The orbits are explicit: for an atom `a` with `m = mOf a`, `orbit a` is the multiset of roots
of `Φ_m(κ X^N)`, that is the `r` with `κ r^N` a primitive `m`-th root of unity, where
`(κ, N) = (1, 1)`, `(-1, 1)`, `(± i, 2^(e+2))` for `P k`, `Q k`, `R k e`. So `orbit (P k)` is
the set of primitive `m`-th roots (`orbit_P`), `orbit (Q k)` the primitive `2m`-th roots
(`orbit_Q`), and `orbit (R k e)` an orbit of order `2^(e+4) m`. Each is a set (`orbit_nodup`)
of roots of unity, and `κ^φ(m) z_O = atom a` (`zO_orbit`), with `κ^4 = 1`. The self-paired
orbits of order `8m` are `selfOrb k b`, the roots of `Φ_m(± i X²)`.

`theoremBgamma`: in a rational relation among `π`, the `γ(orbit a)`, the `γ(partner (orbit a))`
and the `γ(selfOrb k b)`, the coefficients of `orbit a` and its partner agree for every
non-exceptional `a`, the net coefficients of `O_2 = orbit (Q 0)` and `O_10 = orbit (Q 2)` add
to zero, and `q` is a quarter of the net coefficient of `O_1` minus that of `O_2`. With the
exact values `γ(O_1) = π/4`, `γ(O_6) = 0`, `γ(O_2) = arctan (1/2) - π/4`,
`γ(O_10) = arctan (1/2)`, `γ(O*) = -γ(O)` and `γ(selfOrb) = 0` (the converse), the relations
are spanned by the note's list.

That these multisets are exactly the orbits of `Gal(ℚ̄/ℚ(i))` on the roots of unity (the
irreducibility over `ℚ(i)` of `Φ_m(κ X^N)`), and that every orbit is one of them, is proved in
`TheoremBGalois.lean` (`galois_table`).
-/

@[expose] public section

open Polynomial Complex ComplexConjugate

namespace PiFormula

/-! ## 1. `γ`, `z_O` and the angle identity -/

/-- `t = 1 + i` in `ℂ`. -/
noncomputable def tC : ℂ := 1 + I

/-- `g(r) = Im Log(1 - r/t)`. -/
noncomputable def gfun (r : ℂ) : ℝ := (Complex.log (1 - r / tC)).im

/-- `γ(O) = ∑_{r ∈ O} g(r)`. -/
noncomputable def gamma (S : Multiset ℂ) : ℝ := (S.map gfun).sum

/-- `z_O = ∏_{r ∈ O} (t - r)`. -/
noncomputable def zO (S : Multiset ℂ) : ℂ := (S.map (fun r => tC - r)).prod

/-- The partner `O* = { i conj r : r ∈ O }`. -/
noncomputable def partner (S : Multiset ℂ) : Multiset ℂ := S.map (fun r => I * conj r)

theorem tC_ne_zero : tC ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [tC] at this

theorem arg_tC : arg tC = Real.pi / 4 := by
  have h := arctan_inv_eq_arg (x := 1) one_pos
  rw [div_one, Real.arctan_one, Complex.ofReal_one] at h
  exact h.symm

theorem tG_toComplex : ((tG : GaussianInt) : ℂ) = tC := by
  simp [tG, tC, GaussianInt.toComplex_def']

theorem gfun_eq_arg (r : ℂ) : gfun r = arg (1 - r / tC) := Complex.log_im _

theorem one_sub_div_tC_re (r : ℂ) : (1 - r / tC).re = 1 - (r.re + r.im) / 2 := by
  simp [tC, Complex.div_re, Complex.normSq_apply]
  ring

theorem one_sub_div_tC_im (r : ℂ) : (1 - r / tC).im = (r.re - r.im) / 2 := by
  simp [tC, Complex.div_im, Complex.normSq_apply]
  ring

theorem re_sq_add_im_sq {r : ℂ} (hr : ‖r‖ = 1) : r.re ^ 2 + r.im ^ 2 = 1 := by
  have := Complex.normSq_eq_norm_sq r
  rw [hr, Complex.normSq_apply] at this
  nlinarith

theorem ne_tC {r : ℂ} (hr : ‖r‖ = 1) : r ≠ tC := by
  rintro rfl
  have := re_sq_add_im_sq hr
  simp [tC] at this

theorem tC_sub_ne_zero {r : ℂ} (hr : ‖r‖ = 1) : tC - r ≠ 0 := sub_ne_zero.2 (ne_tC hr).symm

/-- For `|r| = 1`, `w = 1 - r/t` has `Re w > 0` and `|Im w| ≤ Re w`. -/
theorem w_bounds {r : ℂ} (hr : ‖r‖ = 1) :
    0 < (1 - r / tC).re ∧ |(1 - r / tC).im| ≤ (1 - r / tC).re := by
  have h := re_sq_add_im_sq hr
  rw [one_sub_div_tC_re, one_sub_div_tC_im]
  have hx : r.re ≤ 1 := by nlinarith [sq_nonneg r.im, sq_nonneg (r.re - 1)]
  have hy : r.im ≤ 1 := by nlinarith [sq_nonneg r.re, sq_nonneg (r.im - 1)]
  constructor
  · nlinarith [sq_nonneg (r.re - r.im)]
  · rw [abs_le]; constructor <;> linarith

/-- `|arg w| ≤ π/4` when `Re w > 0` and `|Im w| ≤ Re w`. -/
theorem abs_arg_le_pi_div_four {w : ℂ} (hre : 0 < w.re) (him : |w.im| ≤ w.re) :
    |arg w| ≤ Real.pi / 4 := by
  obtain ⟨h1, h2⟩ := abs_lt.1 ((Complex.abs_arg_lt_pi_div_two_iff).2 (Or.inl hre))
  have harg : arg w = Real.arctan (w.im / w.re) := by
    rw [← Complex.tan_arg, Real.arctan_tan h1 h2]
  have hq : |w.im / w.re| ≤ 1 := by
    rw [abs_div, abs_of_pos hre]
    exact (div_le_one hre).2 him
  rw [abs_le] at hq
  rw [harg, abs_le, ← Real.arctan_one]
  constructor
  · rw [← Real.arctan_neg]; exact Real.arctan_le_arctan_iff.2 hq.1
  · exact Real.arctan_le_arctan_iff.2 hq.2

/-- `|g(r)| ≤ π/4` for `|r| = 1`. -/
theorem abs_gfun_le {r : ℂ} (hr : ‖r‖ = 1) : |gfun r| ≤ Real.pi / 4 := by
  rw [gfun_eq_arg]
  exact abs_arg_le_pi_div_four (w_bounds hr).1 (w_bounds hr).2

theorem abs_gamma_le {S : Multiset ℂ} (hS : ∀ r ∈ S, ‖r‖ = 1) :
    |gamma S| ≤ Multiset.card S * (Real.pi / 4) := by
  induction S using Multiset.induction_on with
  | empty => simp [gamma]
  | cons r S ih =>
    have hr := hS r (Multiset.mem_cons_self r S)
    have hS' : ∀ x ∈ S, ‖x‖ = 1 := fun x hx => hS x (Multiset.mem_cons_of_mem hx)
    have e1 : gamma (r ::ₘ S) = gfun r + gamma S := by simp [gamma]
    rw [e1, Multiset.card_cons]
    push_cast
    calc |gfun r + gamma S| ≤ |gfun r| + |gamma S| := abs_add_le _ _
      _ ≤ Real.pi / 4 + Multiset.card S * (Real.pi / 4) := add_le_add (abs_gfun_le hr) (ih hS')
      _ = (Multiset.card S + 1) * (Real.pi / 4) := by ring

theorem zO_ne_zero {S : Multiset ℂ} (hS : ∀ r ∈ S, ‖r‖ = 1) : zO S ≠ 0 := by
  unfold zO
  rw [Ne, Multiset.prod_eq_zero_iff]
  simp only [Multiset.mem_map, not_exists, not_and]
  intro r hr h
  exact tC_sub_ne_zero (hS r hr) h

/-- **The angle identity.** `γ(O) ≡ arg z_O - |O| π/4 (mod 2π)`. -/
theorem gamma_angle {S : Multiset ℂ} (hS : ∀ r ∈ S, ‖r‖ = 1) :
    (gamma S : Real.Angle) =
      (arg (zO S) : Real.Angle) - (Multiset.card S) • ((Real.pi / 4 : ℝ) : Real.Angle) := by
  induction S using Multiset.induction_on with
  | empty => simp [gamma, zO]
  | cons r S ih =>
    have hr := hS r (Multiset.mem_cons_self r S)
    have hS' : ∀ x ∈ S, ‖x‖ = 1 := fun x hx => hS x (Multiset.mem_cons_of_mem hx)
    have e1 : gamma (r ::ₘ S) = gfun r + gamma S := by simp [gamma]
    have e2 : zO (r ::ₘ S) = (tC - r) * zO S := by simp [zO]
    have e3 : 1 - r / tC = (tC - r) / tC := by rw [sub_div, div_self tC_ne_zero]
    rw [e1, e2, Real.Angle.coe_add, ih hS', arg_mul_coe_angle (tC_sub_ne_zero hr) (zO_ne_zero hS'),
      Multiset.card_cons, gfun_eq_arg, e3, arg_div_coe_angle (tC_sub_ne_zero hr) tC_ne_zero,
      arg_tC, succ_nsmul]
    abel

/-! ## 2. The pairing -/

theorem one_sub_partner (r : ℂ) : 1 - I * conj r / tC = conj (1 - r / tC) := by
  have hc : conj tC = 1 - I := by simp [tC, sub_eq_add_neg]
  have h1 : (1 : ℂ) - I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  rw [map_sub, map_one, map_div₀, hc]
  congr 1
  rw [div_eq_div_iff tC_ne_zero h1]
  unfold tC
  linear_combination (-conj r) * Complex.I_sq

theorem gfun_partner {r : ℂ} (hr : ‖r‖ = 1) : gfun (I * conj r) = -gfun r := by
  have hne : arg (1 - r / tC) ≠ Real.pi := by
    intro h
    have := (w_bounds hr).1
    have h2 := (Complex.arg_eq_pi_iff.1 h).1
    linarith
  rw [gfun_eq_arg, gfun_eq_arg, one_sub_partner, arg_conj]
  simp [hne]

theorem norm_partner_elt {r : ℂ} (hr : ‖r‖ = 1) : ‖I * conj r‖ = 1 := by
  rw [norm_mul, Complex.norm_I, Complex.norm_conj, hr, one_mul]

/-- **The pairing.** `γ(O*) = -γ(O)`. -/
theorem gamma_partner {S : Multiset ℂ} (hS : ∀ r ∈ S, ‖r‖ = 1) :
    gamma (partner S) = -gamma S := by
  unfold gamma partner
  have : (S.map (fun r => I * conj r)).map gfun = S.map (fun r => -gfun r) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun r hr => gfun_partner (hS r hr)
  rw [this, Multiset.sum_map_neg]

/-! ## 3. Roots of `Φ_m(κ X^N)` -/

section Roots

variable {m N : ℕ} {κ : ℂ}

/-- `Φ_m(κ X^N)`. -/
noncomputable def cycPoly (m N : ℕ) (κ : ℂ) : ℂ[X] := (cyclotomic m ℂ).comp (C κ * X ^ N)

theorem norm_eq_one_of_pow_four {u : ℂ} (hu : u ^ 4 = 1) : ‖u‖ = 1 := by
  have h : ‖u‖ ^ 4 = 1 := by rw [← norm_pow, hu, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg u) (by norm_num)).1 h

theorem natDegree_cycPoly (hκ : κ ≠ 0) : (cycPoly m N κ).natDegree = m.totient * N := by
  rw [cycPoly, natDegree_comp, natDegree_cyclotomic, natDegree_C_mul_X_pow N κ hκ]

theorem leadingCoeff_cycPoly (hκ : κ ≠ 0) (hN : N ≠ 0) :
    (cycPoly m N κ).leadingCoeff = κ ^ m.totient := by
  rw [cycPoly, leadingCoeff_comp (by rw [natDegree_C_mul_X_pow N κ hκ]; exact hN),
    (cyclotomic.monic m ℂ).leadingCoeff, leadingCoeff_C_mul_X_pow, natDegree_cyclotomic, one_mul]

theorem cycPoly_ne_zero (hκ : κ ≠ 0) (hN : N ≠ 0) : cycPoly m N κ ≠ 0 := by
  intro h
  have := leadingCoeff_cycPoly (m := m) hκ hN
  rw [h, leadingCoeff_zero] at this
  exact pow_ne_zero _ hκ this.symm

theorem mem_roots_cycPoly (hm : 0 < m) (hκ : κ ≠ 0) (hN : N ≠ 0) {r : ℂ} :
    r ∈ (cycPoly m N κ).roots ↔ IsPrimitiveRoot (κ * r ^ N) m := by
  have : NeZero (m : ℂ) := ⟨by exact_mod_cast hm.ne'⟩
  rw [mem_roots (cycPoly_ne_zero hκ hN), IsRoot, cycPoly, eval_comp]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  exact isRoot_cyclotomic_iff

theorem norm_of_mem_roots_cycPoly (hm : 0 < m) (hκ : ‖κ‖ = 1) (hN : N ≠ 0) {r : ℂ}
    (hr : r ∈ (cycPoly m N κ).roots) : ‖r‖ = 1 := by
  have hκ0 : κ ≠ 0 := by intro h; rw [h, norm_zero] at hκ; exact zero_ne_one hκ
  have hp := (mem_roots_cycPoly hm hκ0 hN).1 hr
  have h1 := hp.norm'_eq_one hm.ne'
  rw [norm_mul, hκ, one_mul, norm_pow] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg r) hN).1 h1

theorem card_roots_cycPoly (hκ : κ ≠ 0) : Multiset.card (cycPoly m N κ).roots = m.totient * N := by
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_cycPoly hκ]

/-- `κ^φ(m) ∏_{r} (t - r) = Φ_m(κ t^N)`. -/
theorem zO_cycPoly (hκ : κ ≠ 0) (hN : N ≠ 0) :
    κ ^ m.totient * zO (cycPoly m N κ).roots = (cyclotomic m ℂ).eval (κ * tC ^ N) := by
  have h := (IsAlgClosed.splits (cycPoly m N κ)).eval_eq_prod_roots tC
  rw [leadingCoeff_cycPoly hκ hN] at h
  rw [zO, ← h, cycPoly, eval_comp]
  simp

/-- The roots of `Φ_m(κ X^N)` are distinct (for `κ^4 = 1`, `m, N > 0`). -/
theorem nodup_roots_cycPoly (hm : 0 < m) (hκ : κ ^ 4 = 1) (hN : 0 < N) :
    (cycPoly m N κ).roots.Nodup := by
  have hκ0 : κ ≠ 0 := by intro h; rw [h] at hκ; norm_num at hκ
  apply nodup_roots
  -- `Φ_m(κ X^N) ∣ (κ X^N)^m - 1 ∣ ((κ X^N)^m)^4 - 1 = X^(4 N m) - 1`
  set q : ℂ[X] := C κ * X ^ N with hq
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one m ℂ
  have d1 : cycPoly m N κ ∣ q ^ m - 1 := by
    refine ⟨g.comp q, ?_⟩
    have := congrArg (fun p => p.comp q) hg
    simpa [cycPoly, mul_comp, sub_comp, pow_comp] using this
  have d2 : q ^ m - 1 ∣ (q ^ m) ^ 4 - 1 :=
    Dvd.intro_left _ (geom_sum_mul (q ^ m) 4)
  have e : (q ^ m) ^ 4 - 1 = X ^ (N * m * 4) - 1 := by
    rw [hq, ← pow_mul, mul_pow, ← C_pow, ← pow_mul, mul_comm m 4, pow_mul, hκ, one_pow, C_1,
      one_mul]
    ring
  rw [e] at d2
  refine Separable.of_dvd ?_ (d1.trans d2)
  rw [X_pow_sub_one_separable_iff]
  exact_mod_cast (by positivity : N * m * 4 ≠ 0)

end Roots

/-! ## 4. The orbits of the atoms -/

/-- The constant `κ` (with `κ^4 = 1`). -/
noncomputable def kappa : Atom → ℂ
  | .P _ => 1
  | .Q _ => -1
  | .R _ e => I * (-1) ^ 2 ^ e

/-- The exponent `N`. -/
def Npow : Atom → ℕ
  | .P _ => 1
  | .Q _ => 1
  | .R _ e => 2 ^ (e + 2)

/-- The orbit of an atom: the roots of `Φ_m(κ X^N)`. -/
noncomputable def orbit (a : Atom) : Multiset ℂ := (cycPoly (mOf a) (Npow a) (kappa a)).roots

theorem kappa_pow_four (a : Atom) : kappa a ^ 4 = 1 := by
  rcases a with k | k | ⟨k, e⟩
  · norm_num [kappa]
  · norm_num [kappa]
  · simp only [kappa]
    rw [mul_pow, Complex.I_pow_four, one_mul, ← pow_mul]
    exact Even.neg_one_pow ⟨2 ^ e * 2, by ring⟩

theorem kappa_ne_zero (a : Atom) : kappa a ≠ 0 := by
  intro h; have := kappa_pow_four a; rw [h] at this; norm_num at this

theorem Npow_pos (a : Atom) : 0 < Npow a := by cases a <;> simp [Npow]

theorem tC_pow_four : tC ^ 4 = -4 := by
  unfold tC
  linear_combination (I ^ 2 + 4 * I + 5) * Complex.I_sq

/-- `κ t^N = base a` (as complex numbers). -/
theorem kappa_mul_tC_pow (a : Atom) : kappa a * tC ^ Npow a = ((base a : GaussianInt) : ℂ) := by
  rcases a with k | k | ⟨k, e⟩
  · simp [kappa, Npow, base, tG_toComplex]
  · simp [kappa, Npow, base, tG_toComplex]
  · simp only [kappa, Npow, base, xR]
    rw [show 2 ^ (e + 2) = 4 * 2 ^ e by ring, pow_mul, tC_pow_four]
    simp only [GaussianInt.toComplex_def', Int.cast_zero, Int.cast_pow, Int.cast_ofNat, zero_add]
    rw [mul_assoc, ← mul_pow, show (-1 : ℂ) * -4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ']
    ring

/-- `Φ_m(base)` in `ℂ` is the atom. -/
theorem eval_cyclotomic_base (a : Atom) :
    (cyclotomic (mOf a) ℂ).eval ((base a : GaussianInt) : ℂ) = ((atom a : GaussianInt) : ℂ) := by
  have := Polynomial.eval₂_at_apply (p := cyclotomic (mOf a) GaussianInt) GaussianInt.toComplex
    (base a)
  rw [← Polynomial.eval_map, map_cyclotomic] at this
  exact this

/-- `κ^φ(m) z_O = atom a`. -/
theorem zO_orbit (a : Atom) :
    kappa a ^ (mOf a).totient * zO (orbit a) = ((atom a : GaussianInt) : ℂ) := by
  rw [orbit, zO_cycPoly (kappa_ne_zero a) (Npow_pos a).ne', kappa_mul_tC_pow, eval_cyclotomic_base]

theorem norm_of_mem_orbit {a : Atom} {r : ℂ} (hr : r ∈ orbit a) : ‖r‖ = 1 :=
  norm_of_mem_roots_cycPoly (mOf_odd a).pos (norm_eq_one_of_pow_four (kappa_pow_four a))
    (Npow_pos a).ne' hr

theorem card_orbit (a : Atom) : Multiset.card (orbit a) = (mOf a).totient * Npow a :=
  card_roots_cycPoly (kappa_ne_zero a)

theorem mem_orbit_iff {a : Atom} {r : ℂ} :
    r ∈ orbit a ↔ IsPrimitiveRoot (kappa a * r ^ Npow a) (mOf a) :=
  mem_roots_cycPoly (mOf_odd a).pos (kappa_ne_zero a) (Npow_pos a).ne'

/-- Each orbit is a set. -/
theorem orbit_nodup (a : Atom) : (orbit a).Nodup :=
  nodup_roots_cycPoly (mOf_odd a).pos (kappa_pow_four a) (Npow_pos a)

/-- `orbit (P k)` is the set of primitive `m`-th roots of unity (the note's `O_m`). -/
theorem orbit_P (k : ℕ) : orbit (.P k) = (primitiveRoots (2 * k + 1) ℂ).val := by
  have : NeZero ((2 * k + 1 : ℕ) : ℂ) := ⟨by exact_mod_cast (by omega : 2 * k + 1 ≠ 0)⟩
  simp only [orbit, cycPoly, kappa, Npow, mOf, C_1, one_mul, pow_one, comp_X]
  exact cyclotomic.roots_eq_primitiveRoots_val

/-- `orbit (Q k)` is the set of primitive `2m`-th roots of unity (the note's `O_2m`). -/
theorem orbit_Q (k : ℕ) : orbit (.Q k) = (primitiveRoots (2 * (2 * k + 1)) ℂ).val := by
  have : NeZero ((2 * (2 * k + 1) : ℕ) : ℂ) := ⟨by exact_mod_cast (by omega : 2 * (2 * k + 1) ≠ 0)⟩
  simp only [orbit, cycPoly, kappa, Npow, mOf, pow_one]
  rw [show (C (-1) * X : ℂ[X]) = -X by simp]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [cyclotomic_one, sub_comp, X_comp, one_comp,
      show (-X - 1 : ℂ[X]) = -(cyclotomic 2 ℂ) by rw [cyclotomic_two]; ring, roots_neg]
    exact cyclotomic.roots_eq_primitiveRoots_val
  · rw [← cyclotomic_two_mul_of_odd ⟨k, rfl⟩ (by omega)]
    exact cyclotomic.roots_eq_primitiveRoots_val

/-! ## 5. Partners and the self-paired orbits -/

theorem gamma_partner_orbit (a : Atom) : gamma (partner (orbit a)) = -gamma (orbit a) :=
  gamma_partner fun _ hr => norm_of_mem_orbit hr

/-- `κ = ± i` for the self-paired orbits. -/
noncomputable def kappaS (b : Bool) : ℂ := if b then I else -I

/-- The self-paired orbits of order `8m` (`m = 2k + 1`): the roots of `Φ_m(± i X²)`. -/
noncomputable def selfOrb (k : ℕ) (b : Bool) : Multiset ℂ :=
  (cycPoly (2 * k + 1) 2 (kappaS b)).roots

theorem kappaS_pow_four (b : Bool) : kappaS b ^ 4 = 1 := by
  cases b
  · simp only [kappaS, Bool.false_eq_true, ↓reduceIte]
    rw [neg_pow, Complex.I_pow_four]; norm_num
  · simp [kappaS]

theorem conj_kappaS (b : Bool) : conj (kappaS b) = -kappaS b := by
  cases b <;> simp [kappaS]

/-- `I conj (I conj r) = r`. -/
theorem partner_fun_involutive : Function.Involutive (fun r : ℂ => I * conj r) := by
  intro r
  simp only [map_mul, Complex.conj_I, Complex.conj_conj]
  rw [← mul_assoc, show I * -I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], one_mul]

/-- A self-paired orbit is its own partner. -/
theorem partner_selfOrb (k : ℕ) (b : Bool) : partner (selfOrb k b) = selfOrb k b := by
  have hm : 0 < 2 * k + 1 := by omega
  have hκ0 : kappaS b ≠ 0 := by
    intro h; have := kappaS_pow_four b; rw [h] at this; norm_num at this
  have hnd : (selfOrb k b).Nodup := nodup_roots_cycPoly hm (kappaS_pow_four b) (by norm_num)
  have hinv := partner_fun_involutive
  rw [partner, Multiset.Nodup.ext (hnd.map hinv.injective) hnd]
  have hconj : ∀ z : ℂ, IsPrimitiveRoot (conj z) (2 * k + 1) ↔ IsPrimitiveRoot z (2 * k + 1) :=
    fun z => ⟨fun h => by
      simpa using h.map_of_injective (f := starRingEnd ℂ) (RingHom.injective _),
      fun h => h.map_of_injective (RingHom.injective _)⟩
  have hkey : ∀ s : ℂ, kappaS b * (I * conj s) ^ 2 = conj (kappaS b * s ^ 2) := fun s => by
    rw [map_mul, conj_kappaS, map_pow, mul_pow, Complex.I_sq]
    ring
  have hmem : ∀ s : ℂ, (I * conj s) ∈ selfOrb k b ↔ s ∈ selfOrb k b := fun s => by
    rw [selfOrb, mem_roots_cycPoly hm hκ0 (by norm_num), mem_roots_cycPoly hm hκ0 (by norm_num),
      hkey, hconj]
  intro s
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (hmem r).2 hr
  · intro hs
    exact ⟨I * conj s, (hmem s).2 hs, hinv s⟩

/-- `γ = 0` for the self-paired orbits. -/
theorem gamma_selfOrb (k : ℕ) (b : Bool) : gamma (selfOrb k b) = 0 := by
  have hS : ∀ r ∈ selfOrb k b, ‖r‖ = 1 := fun r hr =>
    norm_of_mem_roots_cycPoly (by omega) (norm_eq_one_of_pow_four (kappaS_pow_four b))
      (by norm_num) hr
  have := gamma_partner hS
  rw [partner_selfOrb] at this
  linarith

/-! ## 6. The exceptional orbits, exactly -/

theorem eq_of_coe_angle_eq {x y : ℝ} (h : (x : Real.Angle) = y) (hb : |x - y| < 2 * Real.pi) :
    x = y := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h
  have hpi := Real.pi_pos
  rw [hk] at hb
  obtain ⟨h1, h2⟩ := abs_lt.1 hb
  have hk0 : k = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      nlinarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      nlinarith
  rw [hk0] at hk
  simp at hk
  linarith

theorem arctan_half_bounds : 0 < Real.arctan (1 / 2) ∧ Real.arctan (1 / 2) < Real.pi / 4 := by
  refine ⟨Real.arctan_pos.2 (by norm_num), ?_⟩
  rw [← Real.arctan_one]
  exact Real.arctan_lt_arctan_iff.2 (by norm_num)

theorem nsmul_pi_div_four (n : ℕ) :
    n • ((Real.pi / 4 : ℝ) : Real.Angle) = ((n * (Real.pi / 4) : ℝ) : Real.Angle) := by
  rw [← Real.Angle.coe_nsmul, nsmul_eq_mul]

theorem totient_three : Nat.totient 3 = 2 := Nat.totient_prime Nat.prime_three

theorem totient_five : Nat.totient 5 = 4 := Nat.totient_prime (by norm_num)

/-- `γ(O_1) = π/4`. -/
theorem gamma_orbit_P0 : gamma (orbit (.P 0)) = Real.pi / 4 := by
  have hS : ∀ r ∈ orbit (.P 0), ‖r‖ = 1 := fun r hr => norm_of_mem_orbit hr
  have hz : zO (orbit (.P 0)) = I := by
    have := zO_orbit (.P 0)
    rw [atom_P0] at this
    simpa [kappa, gI, GaussianInt.toComplex_def'] using this
  have hcard : Multiset.card (orbit (.P 0)) = 1 := by rw [card_orbit]; simp [mOf, Npow]
  have hang := gamma_angle hS
  rw [hz, hcard, arg_I, nsmul_pi_div_four, ← Real.Angle.coe_sub] at hang
  have hb := abs_gamma_le hS
  rw [hcard] at hb
  have e := eq_of_coe_angle_eq hang (by
    obtain ⟨h1, h2⟩ := abs_le.1 hb
    have := Real.pi_pos
    rw [abs_lt]; constructor <;> push_cast at h1 h2 ⊢ <;> linarith)
  rw [e]; push_cast; ring

/-- `γ(O_6) = 0`. -/
theorem gamma_orbit_Q1 : gamma (orbit (.Q 1)) = 0 := by
  have hS : ∀ r ∈ orbit (.Q 1), ‖r‖ = 1 := fun r hr => norm_of_mem_orbit hr
  have hz : zO (orbit (.Q 1)) = I := by
    have := zO_orbit (.Q 1)
    rw [atom_Q1, show mOf (.Q 1) = 3 from rfl, totient_three] at this
    simpa [kappa, gI, GaussianInt.toComplex_def'] using this
  have hcard : Multiset.card (orbit (.Q 1)) = 2 := by
    rw [card_orbit, show mOf (.Q 1) = 3 from rfl, totient_three]; rfl
  have hang := gamma_angle hS
  rw [hz, hcard, arg_I, nsmul_pi_div_four, ← Real.Angle.coe_sub] at hang
  have hb := abs_gamma_le hS
  rw [hcard] at hb
  have e := eq_of_coe_angle_eq hang (by
    obtain ⟨h1, h2⟩ := abs_le.1 hb
    have := Real.pi_pos
    rw [abs_lt]; constructor <;> push_cast at h1 h2 ⊢ <;> linarith)
  rw [e]; push_cast; ring

/-- `γ(O_2) = arctan (1/2) - π/4`. -/
theorem gamma_orbit_Q0 : gamma (orbit (.Q 0)) = Real.arctan (1 / 2) - Real.pi / 4 := by
  have hS : ∀ r ∈ orbit (.Q 0), ‖r‖ = 1 := fun r hr => norm_of_mem_orbit hr
  have hz : zO (orbit (.Q 0)) = 2 + I := by
    have := zO_orbit (.Q 0)
    rw [atom_Q0] at this
    simp [kappa, mOf, GaussianInt.toComplex_def'] at this
    linear_combination -this
  have hcard : Multiset.card (orbit (.Q 0)) = 1 := by rw [card_orbit]; simp [mOf, Npow]
  have harg : arg (2 + I) = Real.arctan (1 / 2) := by
    have := arctan_inv_eq_arg (x := 2) (by norm_num)
    push_cast at this
    exact this.symm
  have hang := gamma_angle hS
  rw [hz, hcard, harg, nsmul_pi_div_four, ← Real.Angle.coe_sub] at hang
  have hb := abs_gamma_le hS
  rw [hcard] at hb
  have e := eq_of_coe_angle_eq hang (by
    obtain ⟨h1, h2⟩ := abs_le.1 hb
    obtain ⟨h3, h4⟩ := arctan_half_bounds
    have := Real.pi_pos
    rw [abs_lt]; constructor <;> push_cast at h1 h2 ⊢ <;> linarith)
  rw [e]; push_cast; ring

/-- `γ(O_10) = arctan (1/2)`. -/
theorem gamma_orbit_Q2 : gamma (orbit (.Q 2)) = Real.arctan (1 / 2) := by
  have hS : ∀ r ∈ orbit (.Q 2), ‖r‖ = 1 := fun r hr => norm_of_mem_orbit hr
  have hz : zO (orbit (.Q 2)) = ((⟨-2, -1⟩ : GaussianInt) : ℂ) := by
    have := zO_orbit (.Q 2)
    rw [atom_Q2, show mOf (.Q 2) = 5 from rfl, totient_five, kappa_pow_four, one_mul] at this
    exact this
  have hcard : Multiset.card (orbit (.Q 2)) = 4 := by
    rw [card_orbit, show mOf (.Q 2) = 5 from rfl, totient_five]; rfl
  have hang := gamma_angle hS
  rw [hz, hcard, arg_m2mi, nsmul_pi_div_four, ← Real.Angle.coe_sub] at hang
  have hang' : (gamma (orbit (.Q 2)) : Real.Angle) = (Real.arctan (1 / 2) : Real.Angle) := by
    rw [hang, show Real.arctan (1 / 2) - Real.pi - (4 : ℕ) * (Real.pi / 4) =
      Real.arctan (1 / 2) - 2 * Real.pi by push_cast; ring, Real.Angle.coe_sub,
      Real.Angle.coe_two_pi, sub_zero]
  have hb := abs_gamma_le hS
  rw [hcard] at hb
  exact eq_of_coe_angle_eq hang' (by
    obtain ⟨h1, h2⟩ := abs_le.1 hb
    obtain ⟨h3, h4⟩ := arctan_half_bounds
    have := Real.pi_pos
    rw [abs_lt]; constructor <;> push_cast at h1 h2 ⊢ <;> linarith)

/-! ## 7. Theorem B, `γ` form -/

/-- An element `u` with `u^4 = 1` has argument a rational multiple of `π`. -/
theorem arg_of_pow_four {u : ℂ} (hu : u ^ 4 = 1) : ∃ s : ℚ, arg u = s * Real.pi := by
  have h : (u - 1) * (u + 1) * (u - I) * (u + I) = 0 := by
    linear_combination hu + (1 - u ^ 2) * Complex.I_sq
  rcases mul_eq_zero.1 h with h | h4
  · rcases mul_eq_zero.1 h with h | h3
    · rcases mul_eq_zero.1 h with h1 | h2
      · exact ⟨0, by rw [sub_eq_zero.1 h1, arg_one]; simp⟩
      · exact ⟨1, by rw [eq_neg_of_add_eq_zero_left h2, arg_neg_one]; simp⟩
    · exact ⟨1 / 2, by rw [sub_eq_zero.1 h3, arg_I]; push_cast; ring⟩
  · exact ⟨-1 / 2, by rw [eq_neg_of_add_eq_zero_left h4, arg_neg_I]; push_cast; ring⟩

/-- `γ(orbit a) = arg (atom a) + s π` for a rational `s`. -/
theorem gamma_orbit_eq (a : Atom) :
    ∃ s : ℚ, gamma (orbit a) = arg ((atom a : GaussianInt) : ℂ) + s * Real.pi := by
  have hS : ∀ r ∈ orbit a, ‖r‖ = 1 := fun r hr => norm_of_mem_orbit hr
  have hlead4 : (kappa a ^ (mOf a).totient) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, kappa_pow_four, one_pow]
  have hlead0 : kappa a ^ (mOf a).totient ≠ 0 := pow_ne_zero _ (kappa_ne_zero a)
  obtain ⟨s, hs⟩ := arg_of_pow_four hlead4
  have hatom : (arg ((atom a : GaussianInt) : ℂ) : Real.Angle) =
      (arg (kappa a ^ (mOf a).totient) : Real.Angle) + arg (zO (orbit a)) := by
    rw [← zO_orbit a, arg_mul_coe_angle hlead0 (zO_ne_zero hS)]
  have key : (gamma (orbit a) : Real.Angle) = ((arg ((atom a : GaussianInt) : ℂ) - s * Real.pi -
      Multiset.card (orbit a) * (Real.pi / 4) : ℝ) : Real.Angle) := by
    rw [gamma_angle hS, Real.Angle.coe_sub, Real.Angle.coe_sub, hatom, hs, nsmul_pi_div_four]
    abel
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 key
  refine ⟨-s - (Multiset.card (orbit a) : ℚ) / 4 + 2 * k, ?_⟩
  push_cast
  linear_combination hk

/-- **Theorem B, `γ` form.** A rational relation among `π`, the `γ(orbit a)`, the
`γ(partner (orbit a))` and the `γ(selfOrb k b)`: the coefficients of each non-exceptional orbit
and of its partner agree; the net coefficients of `O_2 = orbit (Q 0)` and `O_10 = orbit (Q 2)`
add to zero; and `q` is a quarter of (net coefficient of `O_1`) minus (net coefficient of `O_2`).
-/
def TheoremBgamma : Prop :=
  ∀ (c d : Atom →₀ ℚ) (e : (ℕ × Bool) →₀ ℚ) (q : ℚ),
    (c.sum fun a x => (x : ℝ) * gamma (orbit a)) +
      (d.sum fun a x => (x : ℝ) * gamma (partner (orbit a))) +
      (e.sum fun s x => (x : ℝ) * gamma (selfOrb s.1 s.2)) = q * Real.pi →
    (∀ a, a ∉ exceptional → c a = d a) ∧
      (c (.Q 0) - d (.Q 0)) + (c (.Q 2) - d (.Q 2)) = 0 ∧
      q = ((c (.P 0) - d (.P 0)) - (c (.Q 0) - d (.Q 0))) / 4

theorem theoremBgamma : TheoremBgamma := by
  intro c d e q h
  classical
  have he : (e.sum fun s x => (x : ℝ) * gamma (selfOrb s.1 s.2)) = 0 := by
    simp [Finsupp.sum, gamma_selfOrb]
  have hd : (d.sum fun a x => (x : ℝ) * gamma (partner (orbit a))) =
      -(d.sum fun a x => (x : ℝ) * gamma (orbit a)) := by
    simp only [Finsupp.sum, gamma_partner_orbit, mul_neg, Finset.sum_neg_distrib]
  set c' := c - d with hc'
  have hcd : ∀ a, c' a = c a - d a := fun a => by simp [hc']
  have hsum : (c'.sum fun a x => (x : ℝ) * gamma (orbit a)) = q * Real.pi := by
    rw [hc', Finsupp.sum_sub_index (fun a b₁ b₂ => by push_cast; ring), ← h, he, hd]
    ring
  -- `γ(orbit a) = arg (atom a) + s_a π`, so this is a relation among the atoms
  choose s hs using gamma_orbit_eq
  have e1 : (c'.sum fun a x => (x : ℝ) * gamma (orbit a)) =
      valueB c' + ((∑ a ∈ c'.support, c' a * s a : ℚ) : ℝ) * Real.pi := by
    unfold valueB Finsupp.sum
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [hs a]; ring
  have hval : valueB c' = ((q - ∑ a ∈ c'.support, c' a * s a : ℚ) : ℝ) * Real.pi := by
    rw [e1] at hsum
    push_cast at hsum ⊢
    linarith
  obtain ⟨h1, h2, -⟩ := theoremB c' _ hval
  refine ⟨fun a ha => by have := h1 a ha; rw [hcd] at this; linarith, by
    rw [hcd, hcd] at h2; exact h2, ?_⟩
  -- `q` from the exact values of the four exceptional orbits
  have hsupp : c'.support ⊆ exceptional := by
    intro a ha
    by_contra hn
    exact (Finsupp.mem_support_iff.1 ha) (h1 a hn)
  rw [Finsupp.sum_of_support_subset c' hsupp _ (fun _ _ => by simp)] at hsum
  have hsum' : (c' (.P 0) : ℝ) * (Real.pi / 4) +
      ((c' (.Q 0) : ℝ) * (Real.arctan (1 / 2) - Real.pi / 4) +
        ((c' (.Q 1) : ℝ) * 0 + (c' (.Q 2) : ℝ) * Real.arctan (1 / 2))) = q * Real.pi := by
    rw [← hsum, exceptional, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton, gamma_orbit_P0, gamma_orbit_Q0,
      gamma_orbit_Q1, gamma_orbit_Q2]
  have hQR : (c' (.Q 0) : ℝ) + c' (.Q 2) = 0 := by exact_mod_cast h2
  have hpi := Real.pi_pos
  have hmul : ((q : ℝ) - ((c' (.P 0) : ℝ) - c' (.Q 0)) / 4) * Real.pi = 0 := by
    linear_combination -hsum' + Real.arctan (1 / 2) * hQR
  have hqR : (q : ℝ) = ((c' (.P 0) : ℝ) - c' (.Q 0)) / 4 := by
    have := (mul_eq_zero.1 hmul).resolve_right hpi.ne'
    linarith
  have hq : q = (c' (.P 0) - c' (.Q 0)) / 4 := by exact_mod_cast hqR
  rw [hq, hcd, hcd]

/-- The converse: the relations of the note hold. -/
theorem theoremBgamma_relations :
    (∀ a, gamma (orbit a) + gamma (partner (orbit a)) = 0) ∧
      (∀ k b, gamma (selfOrb k b) = 0) ∧
      gamma (orbit (.P 0)) = Real.pi / 4 ∧ gamma (orbit (.Q 1)) = 0 ∧
      gamma (orbit (.Q 2)) - gamma (orbit (.Q 0)) = Real.pi / 4 := by
  refine ⟨fun a => by rw [gamma_partner_orbit]; ring, gamma_selfOrb, gamma_orbit_P0,
    gamma_orbit_Q1, by rw [gamma_orbit_Q2, gamma_orbit_Q0]; ring⟩

end PiFormula
