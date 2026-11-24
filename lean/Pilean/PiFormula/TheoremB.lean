/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula.Lemma2

/-!
# Theorem B (Part II of pi_formula_theorem.md)

Let `t = 1 + i`. For a root of unity `r` put `g(r) = Im Log(1 - r/t)`, and for an orbit `O` of
roots of unity under `Gal(ℚ̄/ℚ(i))` put `γ(O) = ∑_{r ∈ O} g(r)` and `z_O = ∏_{r ∈ O} (t - r)`, a
Gaussian integer. Then `γ(O) ≡ arg z_O - |O| π/4 (mod 2π)`, `γ(O*) = -γ(O)` for the partner
orbit `O* = { i conj r }`, and a set of representatives of the pairs `{O, O*}` with `O* ≠ O`
has the atoms (the table in Part II, `m = 2k + 1` odd)

* `P k = Φ_m(t)` (the orbit of order `m`; index `4m`),
* `Q k = Φ_m(-t)` (order `2m`; index `4m`),
* `R k e = Φ_m(i 2^(2^(e+1)))` (one of the two orbits of order `2^(e+4) m`, up to a unit;
  index `2^(e+3) m`),

the self-paired orbits (order `8m`) having `γ = 0`. So a rational relation among `π` and the
`γ(O)` is the same thing as a rational relation among `π` and the arguments of these atoms.

**Theorem B** (`theoremB`), in this form: if `∑ c_a arg (atom a) = q π` with rational `c`, then
`c_a = 0` except for the four exceptional atoms `P 0 = i`, `Q 1 = i`, `Q 0 = Q 2 = -2 - i`
(the orbits `O_1`, `O_6`, `O_2`, `O_10` of the note); `c(Q 0) + c(Q 2) = 0`; and
`q = (c(P 0) + c(Q 1)) / 2`. `theoremB_converse` is the converse.

The proof is the note's: Lemma 3 gives every non-exceptional atom a Gaussian prime `ρ` above
a prime `p` of order `4 n` (index `4 n`), dividing it but not its conjugate, and dividing no
other atom of index at most `4 n` (nor its conjugate); the atom of largest index with a
non-zero coefficient then has coefficient 0 (the private-prime argument of Part I, here for
arbitrary Gaussian integers). Existence of `p`: Lemma 2 (`size_bound`) for `P k`, `Q k`
with `m ≥ 7`; direct values for `m = 3, 5`; Bang's theorem for `R k e`. Privacy: a prime of
order `4 n` dividing `N(atom b) ∣ 4^(n_b) + 1` forces `n ∣ n_b`; between `P k` and `Q k`
(and between an atom and its conjugate), `ρ ∣ Φ_m(x)` and `ρ ∣ Φ_m(u x)` for a unit `u ≠ 1`
would give `ρ ∣ u^m - 1`, which divides 2.

The relation `γ(O) ≡ arg z_O - |O| π/4`, the pairing and the `γ` form of Theorem B are in
`TheoremBGamma.lean`; the identification of the Galois orbits over `ℚ(i)` with the explicit
orbits used there (the table) is in `TheoremBGalois.lean`.
-/

@[expose] public section

open Polynomial Complex

namespace PiFormula

/-! ## 1. The bridge and the private prime, for arbitrary Gaussian integers -/

section General

variable {ι : Type*}

/-- `∏ z_n^{c_n}`, with conjugates for negative exponents. -/
def Wz (s : Finset ι) (z : ι → GaussianInt) (c : ι → ℤ) : GaussianInt :=
  ∏ n ∈ s, spow (z n) (c n)

theorem arg_Wz (s : Finset ι) (z : ι → GaussianInt) (hz : ∀ n ∈ s, z n ≠ 0) (c : ι → ℤ) :
    (arg ((Wz s z c : GaussianInt) : ℂ) : Real.Angle) =
      ((∑ n ∈ s, (c n : ℝ) * arg (z n : ℂ) : ℝ) : Real.Angle) := by
  unfold Wz
  rw [map_prod, arg_prod_coe_angle _ _ fun n hn => by
      rw [Ne, GaussianInt.toComplex_eq_zero]; exact spow_ne_zero (hz n hn) (c n)]
  rw [show ((∑ n ∈ s, (c n : ℝ) * arg (z n : ℂ) : ℝ) : Real.Angle) =
      ∑ n ∈ s, (((c n : ℝ) * arg (z n : ℂ) : ℝ) : Real.Angle) from
    map_sum Real.Angle.coeHom _ _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [arg_spow, ← zsmul_eq_mul, Real.Angle.coe_zsmul]

/-- **The bridge.** If `∑ c_n arg z_n = q π` with `q` rational, then `Wz ^ (den q)` is real. -/
theorem star_pow_Wz_eq (s : Finset ι) (z : ι → GaussianInt) (hz : ∀ n ∈ s, z n ≠ 0)
    (c : ι → ℤ) (q : ℚ) (h : ∑ n ∈ s, (c n : ℝ) * arg (z n : ℂ) = q * Real.pi) :
    star (Wz s z c ^ q.den) = Wz s z c ^ q.den := by
  set w : ℂ := ((Wz s z c ^ q.den : GaussianInt) : ℂ) with hw
  have hangle : (arg w : Real.Angle) = ((q.num * Real.pi : ℝ) : Real.Angle) := by
    rw [hw, map_pow, Complex.arg_pow_coe_angle, arg_Wz s z hz c, h, ← Real.Angle.coe_nsmul,
      nsmul_eq_mul]
    congr 1
    have : (q.den : ℝ) * q = q.num := by exact_mod_cast Rat.den_mul_eq_num q
    rw [← mul_assoc, this]
  have him : w.im = 0 := im_eq_zero_of_arg_coe_angle hangle
  have him' : (Wz s z c ^ q.den).im = 0 := by
    have := GaussianInt.intCast_im (Wz s z c ^ q.den)
    rw [← hw, him] at this
    exact_mod_cast this
  ext
  · exact Zsqrtd.re_star _
  · rw [Zsqrtd.im_star, him', neg_zero]

theorem star_Wz (s : Finset ι) (z : ι → GaussianInt) (c : ι → ℤ) :
    star (Wz s z c) = ∏ n ∈ s, spow (star (z n)) (c n) := by
  unfold Wz
  rw [← starRingEnd_apply, map_prod]
  exact Finset.prod_congr rfl fun n _ => by rw [starRingEnd_apply, star_spow]

/-- **Fact 1, general form.** If `Wz ^ N` is real (`N > 0`), then for every Gaussian prime `ρ`,
`∑ c_n (μ_ρ(z_n) - μ_ρ(conj z_n)) = 0`. -/
theorem sum_mul_mult_diff_eq_zero_gen {ρ : GaussianInt} (hρ : Prime ρ) (s : Finset ι)
    (z : ι → GaussianInt) (hz : ∀ n ∈ s, z n ≠ 0) (c : ι → ℤ) {N : ℕ} (hN : 0 < N)
    (hstar : star (Wz s z c ^ N) = Wz s z c ^ N) :
    ∑ n ∈ s, c n * ((multiplicity ρ (z n) : ℤ) - multiplicity ρ (star (z n))) = 0 := by
  have hz' : ∀ n ∈ s, star (z n) ≠ 0 := fun n hn => by simpa using hz n hn
  have hA : multiplicity ρ (Wz s z c ^ N) =
      N * ∑ n ∈ s, ((c n).toNat * multiplicity ρ (z n) +
        (-c n).toNat * multiplicity ρ (star (z n))) := by
    rw [multiplicity_pow hρ, Wz, mult_prod hρ _ _ fun n hn => spow_ne_zero (hz n hn) _]
    simp only [mult_spow hρ]
  have hB : multiplicity ρ (star (Wz s z c ^ N)) =
      N * ∑ n ∈ s, ((c n).toNat * multiplicity ρ (star (z n)) +
        (-c n).toNat * multiplicity ρ (z n)) := by
    rw [star_pow, multiplicity_pow hρ, star_Wz,
      mult_prod hρ _ _ fun n hn => spow_ne_zero (hz' n hn) _]
    simp only [mult_spow hρ, star_star]
  have hAB : (multiplicity ρ (Wz s z c ^ N) : ℤ) = multiplicity ρ (star (Wz s z c ^ N)) := by
    rw [hstar]
  rw [hA, hB] at hAB
  push_cast at hAB
  have key : (N : ℤ) * ∑ n ∈ s, c n * ((multiplicity ρ (z n) : ℤ) -
      multiplicity ρ (star (z n))) = 0 := by
    rw [← sub_eq_zero] at hAB
    rw [← hAB, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    linear_combination ((multiplicity ρ (star (z n)) : ℤ) - multiplicity ρ (z n)) *
      Int.toNat_sub_toNat_neg (c n)
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h (by exact_mod_cast hN.ne')
  · exact h

/-- **The private prime, general form.** In a relation `∑ c_n arg z_n = q π`, if a Gaussian
prime `ρ` divides `z_{n₀}` but not its conjugate, and divides neither `z_n` nor its conjugate
for the other `n`, then `c_{n₀} = 0`. -/
theorem coeff_eq_zero_of_private_prime_gen {s : Finset ι} {z : ι → GaussianInt}
    (hz : ∀ n ∈ s, z n ≠ 0) {c : ι → ℤ} {q : ℚ}
    (h : ∑ n ∈ s, (c n : ℝ) * arg (z n : ℂ) = q * Real.pi)
    {ρ : GaussianInt} (hρ : Prime ρ) {n₀ : ι} (hn₀ : n₀ ∈ s)
    (hdiv : ρ ∣ z n₀) (hndiv : ¬ ρ ∣ star (z n₀))
    (hpriv : ∀ n ∈ s, n ≠ n₀ → ¬ ρ ∣ z n ∧ ¬ ρ ∣ star (z n)) : c n₀ = 0 := by
  have hsum := sum_mul_mult_diff_eq_zero_gen hρ s z hz c q.den_pos
    (star_pow_Wz_eq s z hz c q h)
  rw [Finset.sum_eq_single n₀ (fun n hn hne => by
      rw [multiplicity_eq_zero_of_not_dvd (hpriv n hn hne).1,
        multiplicity_eq_zero_of_not_dvd (hpriv n hn hne).2]; simp)
      (fun h => absurd hn₀ h)] at hsum
  have hfin := FiniteMultiplicity.of_prime_left hρ (hz n₀ hn₀)
  have hpos := (dvd_iff_multiplicity_pos hfin).2 hdiv
  rw [multiplicity_eq_zero_of_not_dvd hndiv] at hsum
  rcases mul_eq_zero.1 hsum with h0 | h0
  · exact h0
  · exfalso
    push_cast at h0
    omega

end General

/-! ## 2. Gaussian primes and units -/

/-- `i` as a Gaussian integer. -/
def gI : GaussianInt := ⟨0, 1⟩

/-- A prime `p ≡ 1 (mod 4)` dividing `N(z)`: some Gaussian prime above `p` divides `z`. -/
theorem exists_prime_dvd_of_dvd_norm {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) {z : GaussianInt}
    (hz : (p : ℤ) ∣ z.norm) :
    ∃ ρ : GaussianInt, Prime ρ ∧ ρ * star ρ = (p : GaussianInt) ∧ ρ ∣ z := by
  obtain ⟨ρ, hρ, hpi⟩ := exists_gaussian_prime_above hp h4
  have hpz : (p : GaussianInt) ∣ z * star z := by
    rw [← Zsqrtd.norm_eq_mul_conj]
    have := map_dvd (Int.castRingHom GaussianInt) hz
    simpa using this
  rcases hρ.dvd_or_dvd ((Dvd.intro _ hpi).trans hpz) with h | h
  · exact ⟨ρ, hρ, hpi, h⟩
  · refine ⟨star ρ, ?_, ?_, ?_⟩
    · have := (MulEquiv.prime_iff (starRingAut : GaussianInt ≃+* GaussianInt) (p := ρ)).2 hρ
      simpa [starRingAut_apply] using this
    · rw [star_star, mul_comm, hpi]
    · obtain ⟨w, hw⟩ := h
      refine ⟨star w, ?_⟩
      rw [← star_star z, hw, star_mul', mul_comm]

/-- `star` commutes with evaluating `Φ_n`. -/
theorem star_eval_cyclotomic (n : ℕ) (w : GaussianInt) :
    star ((cyclotomic n GaussianInt).eval w) = (cyclotomic n GaussianInt).eval (star w) := by
  have := Polynomial.eval₂_at_apply (p := cyclotomic n GaussianInt) (starRingEnd GaussianInt) w
  rw [← Polynomial.eval_map, map_cyclotomic, starRingEnd_apply, starRingEnd_apply] at this
  exact this.symm

/-- If `ρ` (above an odd prime) divides `Φ_m(x)` and `Φ_m(u x)`, then `ρ ∣ u^m - 1`; so this is
impossible when `N(u^m - 1) ∣ 4`. -/
theorem not_dvd_cyc_both {ρ : GaussianInt} {p : ℕ} (hpi : ρ * star ρ = (p : GaussianInt))
    (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} {x u : GaussianInt} (hu : (u ^ m - 1).norm ∣ 4)
    (h1 : ρ ∣ (cyclotomic m GaussianInt).eval x)
    (h2 : ρ ∣ (cyclotomic m GaussianInt).eval (u * x)) : False := by
  have d1 : ρ ∣ x ^ m - 1 :=
    h1.trans (by simpa using eval_dvd (x := x) (cyclotomic.dvd_X_pow_sub_one m GaussianInt))
  have d2 : ρ ∣ (u * x) ^ m - 1 :=
    h2.trans (by simpa using eval_dvd (x := u * x) (cyclotomic.dvd_X_pow_sub_one m GaussianInt))
  have d3 : ρ ∣ u ^ m - 1 := by
    have e : u ^ m - 1 = ((u * x) ^ m - 1) - u ^ m * (x ^ m - 1) := by ring
    rw [e]
    exact dvd_sub d2 (dvd_mul_of_dvd_right d1 _)
  have h4 := (natCast_dvd_norm hpi d3).trans hu
  have h5 : p ∣ 2 ^ 2 := by exact_mod_cast h4
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h5))

/-- `(⟨0, a⟩)^(2k+1) = ⟨0, (-1)^k a^(2k+1)⟩`. -/
theorem imag_pow_odd (a : ℤ) (k : ℕ) :
    (⟨0, a⟩ : GaussianInt) ^ (2 * k + 1) = ⟨0, (-1) ^ k * a ^ (2 * k + 1)⟩ := by
  induction k with
  | zero => ext <;> simp
  | succ k ih =>
    have h2 : (⟨0, a⟩ : GaussianInt) ^ 2 = ⟨-(a * a), 0⟩ := by ext <;> simp [sq]
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, ih, h2]
    ext
    · simp
    · simp [pow_succ]; ring

/-- For odd `m`, `N(u^m - 1) ∣ 4` for `u = -1, i, -i`. -/
theorem norm_unit_pow_sub_one {m : ℕ} (hm : Odd m) :
    (((-1 : GaussianInt) ^ m - 1).norm ∣ 4) ∧ ((gI ^ m - 1).norm ∣ 4) ∧
      (((-gI) ^ m - 1).norm ∣ 4) := by
  obtain ⟨k, rfl⟩ := hm
  have hI : gI ^ (2 * k + 1) = ⟨0, (-1) ^ k⟩ := by
    rw [gI, imag_pow_odd]; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [Odd.neg_one_pow ⟨k, rfl⟩]; decide
  · rw [hI]
    rcases neg_one_pow_eq_or ℤ k with h | h <;> rw [h] <;> decide
  · rw [Odd.neg_pow ⟨k, rfl⟩, hI]
    rcases neg_one_pow_eq_or ℤ k with h | h <;> rw [h] <;> decide

/-! ## 3. The atoms -/

/-- The representative atoms, with `m = 2k + 1`: `P k = Φ_m(t)`, `Q k = Φ_m(-t)`,
`R k e = Φ_m(i 2^(2^(e+1)))`. -/
inductive Atom
  | P (k : ℕ)
  | Q (k : ℕ)
  | R (k e : ℕ)
  deriving DecidableEq

/-- `i 2^(2^(e+1))`. -/
def xR (e : ℕ) : GaussianInt := ⟨0, 2 ^ 2 ^ (e + 1)⟩

/-- The point at which `Φ_m` is evaluated. -/
def base : Atom → GaussianInt
  | .P _ => tG
  | .Q _ => -tG
  | .R _ e => xR e

/-- The odd number `m`. -/
def mOf : Atom → ℕ
  | .P k => 2 * k + 1
  | .Q k => 2 * k + 1
  | .R k _ => 2 * k + 1

/-- A quarter of the index: the index is `4 n`. -/
def nOf : Atom → ℕ
  | .P k => 2 * k + 1
  | .Q k => 2 * k + 1
  | .R k e => 2 ^ (e + 1) * (2 * k + 1)

/-- The atom `Φ_m(base)`. -/
noncomputable def atom (a : Atom) : GaussianInt := (cyclotomic (mOf a) GaussianInt).eval (base a)

/-- The four exceptional atoms (orbits `O_1`, `O_2`, `O_6`, `O_10` of the note). -/
def exceptional : Finset Atom := {.P 0, .Q 0, .Q 1, .Q 2}

theorem mOf_odd (a : Atom) : Odd (mOf a) := by cases a <;> exact ⟨_, rfl⟩

theorem nOf_pos (a : Atom) : 0 < nOf a := by cases a <;> simp [nOf]

/-- `N(x_R^(2k+1) - 1) = 4^(2^(e+1) (2k+1)) + 1`. -/
theorem norm_xR_pow_sub_one (e k : ℕ) :
    (xR e ^ (2 * k + 1) - 1).norm = 4 ^ (2 ^ (e + 1) * (2 * k + 1)) + 1 := by
  rw [xR, imag_pow_odd, Zsqrtd.norm_def]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
  have h4 : (4 : ℤ) ^ (2 ^ (e + 1) * (2 * k + 1)) =
      ((2 : ℤ) ^ 2 ^ (e + 1)) ^ (2 * k + 1) * ((2 : ℤ) ^ 2 ^ (e + 1)) ^ (2 * k + 1) := by
    have e1 : ((2 : ℤ) ^ 2 ^ (e + 1)) ^ (2 * k + 1) * ((2 : ℤ) ^ 2 ^ (e + 1)) ^ (2 * k + 1) =
        (2 : ℤ) ^ (2 ^ (e + 1) * (2 * (2 * k + 1))) := by
      rw [← mul_pow, ← sq, ← pow_mul, ← pow_mul]
    have e2 : (4 : ℤ) ^ (2 ^ (e + 1) * (2 * k + 1)) =
        (2 : ℤ) ^ (2 * (2 ^ (e + 1) * (2 * k + 1))) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [e1, e2]
    congr 1
    ring
  rw [h4]
  have : ((-1 : ℤ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination (((2 : ℤ) ^ 2 ^ (e + 1)) ^ (2 * k + 1)) ^ 2 * this

/-- `N(base^m - 1)` divides `4^n + 1`. -/
theorem norm_base_pow_sub_one_dvd (a : Atom) : ((base a) ^ (mOf a) - 1).norm ∣ 4 ^ nOf a + 1 := by
  rcases a with k | k | ⟨k, e⟩
  · have hLM := (LM_facts (b := 2 * k + 1) ⟨k, rfl⟩).2.2.1
    change Uplus (2 * k + 1) ∣ 4 ^ (2 * k + 1) + 1
    rw [← hLM]
    rcases Uplus_LM (b := 2 * k + 1) ⟨k, rfl⟩ with h | h <;> rw [h]
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  · have hLM := (LM_facts (b := 2 * k + 1) ⟨k, rfl⟩).2.2.1
    change Uminus (2 * k + 1) ∣ 4 ^ (2 * k + 1) + 1
    rw [← hLM]
    rcases Uminus_LM (b := 2 * k + 1) ⟨k, rfl⟩ with h | h <;> rw [h]
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  · exact (norm_xR_pow_sub_one e k).dvd

/-- `N(atom) ∣ 4^n + 1`. -/
theorem norm_atom_dvd (a : Atom) : (atom a).norm ∣ 4 ^ nOf a + 1 :=
  (norm_eval_cyclotomic_dvd (base a) (mOf_odd a).pos).trans (norm_base_pow_sub_one_dvd a)

theorem atom_ne_zero (a : Atom) : atom a ≠ 0 := by
  intro h
  have := norm_atom_dvd a
  rw [h, Zsqrtd.norm_zero, zero_dvd_iff] at this
  have : (0 : ℤ) < 4 ^ nOf a + 1 := by positivity
  omega

/-! ### Values of the small atoms -/

theorem atom_P0 : atom (.P 0) = gI := by
  simp only [atom, mOf, base]
  rw [show 2 * 0 + 1 = 1 by rfl, cyclotomic_one]
  simp only [eval_sub, eval_X, eval_one]
  decide

theorem atom_Q0 : atom (.Q 0) = ⟨-2, -1⟩ := by
  simp only [atom, mOf, base]
  rw [show 2 * 0 + 1 = 1 by rfl, cyclotomic_one]
  simp only [eval_sub, eval_X, eval_one]
  decide

theorem atom_P1 : atom (.P 1) = ⟨2, 3⟩ := by
  simp only [atom, mOf, base]
  rw [show 2 * 1 + 1 = 3 by rfl, cyclotomic_three]
  simp only [eval_add, eval_pow, eval_X, eval_one]
  decide

theorem atom_Q1 : atom (.Q 1) = gI := by
  simp only [atom, mOf, base]
  rw [show 2 * 1 + 1 = 3 by rfl, cyclotomic_three]
  simp only [eval_add, eval_pow, eval_X, eval_one]
  decide

theorem atom_P2 : atom (.P 2) = ⟨-4, 5⟩ := by
  have := Fact.mk (show Nat.Prime 5 by norm_num)
  simp only [atom, mOf, base]
  rw [show 2 * 2 + 1 = 5 by rfl, cyclotomic_prime, eval_finsetSum]
  simp only [eval_pow, eval_X]
  decide

theorem atom_Q2 : atom (.Q 2) = ⟨-2, -1⟩ := by
  have := Fact.mk (show Nat.Prime 5 by norm_num)
  simp only [atom, mOf, base]
  rw [show 2 * 2 + 1 = 5 by rfl, cyclotomic_prime, eval_finsetSum]
  simp only [eval_pow, eval_X]
  decide

/-! ## 4. Lemma 3: private primes -/

theorem nOf_eq_one {a : Atom} (h : nOf a = 1) : a = .P 0 ∨ a = .Q 0 := by
  rcases a with k | k | ⟨k, e⟩
  · left; simp only [nOf] at h; rw [show k = 0 by omega]
  · right; simp only [nOf] at h; rw [show k = 0 by omega]
  · exfalso
    have h2 : 2 ≤ 2 ^ (e + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ≤ 2 ^ (e + 1) * (2 * k + 1) := le_trans h2 (Nat.le_mul_of_pos_right _ (by omega))
    simp only [nOf] at h
    omega

theorem two_pow_mul_odd_inj {a b u v : ℕ} (h : 2 ^ a * (2 * u + 1) = 2 ^ b * (2 * v + 1)) :
    a = b ∧ u = v := by
  wlog hab : a ≤ b generalizing a b u v
  · obtain ⟨h1, h2⟩ := this h.symm (by omega)
    exact ⟨h1.symm, h2.symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, mul_assoc] at h
  have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
  rcases d with _ | d
  · simp at h'; omega
  · exfalso
    have : 2 ∣ 2 * u + 1 := ⟨2 ^ d * (2 * v + 1), by rw [h', pow_succ]; ring⟩
    omega

/-- Atoms with the same index are equal or are `P k` and `Q k`. -/
theorem nOf_eq {a b : Atom} (h : nOf a = nOf b) :
    a = b ∨ (∃ k, a = .P k ∧ b = .Q k) ∨ (∃ k, a = .Q k ∧ b = .P k) := by
  have hev : ∀ k e : ℕ, Even (2 ^ (e + 1) * (2 * k + 1)) := fun k e =>
    (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right _
  rcases a with k | k | ⟨k, e⟩ <;> rcases b with l | l | ⟨l, f⟩ <;> simp only [nOf] at h
  · left; rw [show k = l by omega]
  · right; left; exact ⟨k, rfl, by rw [show l = k by omega]⟩
  · exfalso; obtain ⟨r, hr⟩ := hev l f; omega
  · right; right; exact ⟨k, rfl, by rw [show l = k by omega]⟩
  · left; rw [show k = l by omega]
  · exfalso; obtain ⟨r, hr⟩ := hev l f; omega
  · exfalso; obtain ⟨r, hr⟩ := hev k e; omega
  · exfalso; obtain ⟨r, hr⟩ := hev k e; omega
  · left
    obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj h
    rw [show e = f by omega, h2]

/-- **Lemma 3, existence.** Every non-exceptional atom has a prime factor `p` of its norm with
`orderOf 2 = 4 n` (its index). -/
theorem exists_primitive_atom (a : Atom) (ha : a ∉ exceptional) :
    ∃ p, p.Prime ∧ orderOf (2 : ZMod p) = 4 * nOf a ∧ (p : ℤ) ∣ (atom a).norm := by
  rcases a with k | k | ⟨k, e⟩
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk
    · exact absurd (by simp [exceptional]) ha
    · refine ⟨13, by norm_num, orderOf_two_zmod_13, ?_⟩
      rw [atom_P1]; decide
    · refine ⟨41, by norm_num, orderOf_two_zmod_41, ?_⟩
      rw [atom_P2]; decide
    · have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
      obtain ⟨p, ⟨hp, hord⟩, hdvd⟩ := primitive_of_A (n := 2 * k + 1) (by omega)
        (Aplus_nonneg _) ⟨_, (Aplus_mul_Aminus hodd).symm⟩ (size_bound hodd (by omega)).1
      exact ⟨p, hp, hord, hdvd⟩
  · rcases (show k ≤ 2 ∨ 3 ≤ k by omega) with hk | hk
    · exfalso; apply ha; interval_cases k <;> simp [exceptional]
    · have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
      obtain ⟨p, ⟨hp, hord⟩, hdvd⟩ := primitive_of_A (n := 2 * k + 1) (by omega)
        (Aminus_nonneg _)
        ⟨Aplus (2 * k + 1), (Aplus_mul_Aminus hodd).symm.trans (mul_comm _ _)⟩
        (size_bound hodd (by omega)).2
      exact ⟨p, hp, hord, hdvd⟩
  · have h2 : 2 ≤ 2 ^ (e + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hn2 : 2 ≤ 2 ^ (e + 1) * (2 * k + 1) := le_trans h2 (Nat.le_mul_of_pos_right _ (by omega))
    have hn0 : 0 < 2 ^ (e + 1) * (2 * k + 1) := by omega
    obtain ⟨p, hp, hord⟩ := bang (4 * (2 ^ (e + 1) * (2 * k + 1))) (by omega) (by omega)
    have := Fact.mk hp
    have h4 : p ∣ 4 ^ (2 ^ (e + 1) * (2 * k + 1)) + 1 := dvd_four_pow_add_one_of_orderOf hn0 hord
    refine ⟨p, hp, hord, ?_⟩
    have hprod := prod_norm_eval_cyclotomic (xR e) (n := 2 * k + 1) (by omega)
    rw [norm_xR_pow_sub_one] at hprod
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    have hdv : (p : ℤ) ∣ ∏ d ∈ (2 * k + 1).divisors,
        ((cyclotomic d GaussianInt).eval (xR e)).norm := by
      rw [hprod]; exact_mod_cast h4
    obtain ⟨d, hd, hpd⟩ := (hpZ.dvd_finsetProd_iff _).1 hdv
    have hdm : d ∣ 2 * k + 1 := Nat.dvd_of_mem_divisors hd
    obtain ⟨l, rfl⟩ : Odd d := (odd_two_mul_add_one k).of_dvd_nat hdm
    have h5 : (p : ℤ) ∣ 4 ^ (2 ^ (e + 1) * (2 * l + 1)) + 1 := by
      have := hpd.trans (norm_eval_cyclotomic_dvd (xR e) (n := 2 * l + 1) (by omega))
      rwa [norm_xR_pow_sub_one] at this
    have h6 : p ∣ 4 ^ (2 ^ (e + 1) * (2 * l + 1)) + 1 := by exact_mod_cast h5
    have h7 := (dvd_and_odd_of_orderOf hn0 hord h6).1
    have hmd : 2 * k + 1 ∣ 2 * l + 1 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h7
    have heq : 2 * l + 1 = 2 * k + 1 := Nat.dvd_antisymm hdm hmd
    rw [heq] at hpd
    exact hpd

theorem star_tG : star tG = -gI * tG := by ext <;> simp [tG, gI]

theorem star_neg_tG : star (-tG) = gI * tG := by ext <;> simp [tG, gI]

theorem star_xR (e : ℕ) : star (xR e) = -1 * xR e := by ext <;> simp [xR]

/-- **Lemma 3, `e_p ≠ 0`.** A Gaussian prime above an odd prime that divides an atom does
not divide its conjugate. -/
theorem not_dvd_star_atom {ρ : GaussianInt} {p : ℕ} (hpi : ρ * star ρ = (p : GaussianInt))
    (hp : p.Prime) (hp2 : p ≠ 2) (a : Atom) (h : ρ ∣ atom a) : ¬ ρ ∣ star (atom a) := by
  obtain ⟨u1, -, u3⟩ := norm_unit_pow_sub_one (mOf_odd a)
  intro h'
  simp only [atom] at h h'
  rw [star_eval_cyclotomic] at h'
  rcases a with k | k | ⟨k, e⟩ <;> simp only [base, mOf] at h h' u1 u3
  · rw [star_tG] at h'
    exact not_dvd_cyc_both hpi hp hp2 u3 h h'
  · rw [star_neg_tG, show gI * tG = -gI * -tG by ring] at h'
    exact not_dvd_cyc_both hpi hp hp2 u3 h h'
  · rw [star_xR] at h'
    exact not_dvd_cyc_both hpi hp hp2 u1 h h'

/-- **Lemma 3, privacy within an index.** If `ρ` divides `P k`, it divides neither `Q k` nor its
conjugate, and vice versa. -/
theorem not_dvd_pair {ρ : GaussianInt} {p : ℕ} (hpi : ρ * star ρ = (p : GaussianInt))
    (hp : p.Prime) (hp2 : p ≠ 2) {a b : Atom} (hab : nOf a = nOf b) (hne : b ≠ a)
    (h : ρ ∣ atom a) : ¬ ρ ∣ atom b ∧ ¬ ρ ∣ star (atom b) := by
  rcases nOf_eq hab with heq | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · exact absurd heq.symm hne
  · obtain ⟨u1, u2, -⟩ := norm_unit_pow_sub_one (m := 2 * k + 1) ⟨k, rfl⟩
    simp only [atom, base, mOf] at h ⊢
    rw [star_eval_cyclotomic, star_neg_tG]
    refine ⟨fun h' => ?_, fun h' => not_dvd_cyc_both hpi hp hp2 u2 h h'⟩
    rw [show -tG = -1 * tG by ring] at h'
    exact not_dvd_cyc_both hpi hp hp2 u1 h h'
  · obtain ⟨u1, u2, -⟩ := norm_unit_pow_sub_one (m := 2 * k + 1) ⟨k, rfl⟩
    simp only [atom, base, mOf] at h ⊢
    rw [star_eval_cyclotomic, star_tG]
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · rw [show tG = -1 * -tG by ring] at h'
      exact not_dvd_cyc_both hpi hp hp2 u1 h h'
    · rw [show -gI * tG = gI * -tG by ring] at h'
      exact not_dvd_cyc_both hpi hp hp2 u2 h h'

theorem norm_exceptional_dvd {b : Atom} (hb : b ∈ exceptional) : (atom b).norm ∣ 5 := by
  simp only [exceptional, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · rw [atom_P0]; decide
  · rw [atom_Q0]; decide
  · rw [atom_Q1]; decide
  · rw [atom_Q2]; decide

/-- **Lemma 3, privacy.** Let `a` be non-exceptional, `p` a prime of order `4 n_a` and `ρ` a
Gaussian prime above `p` dividing `atom a`. Then `ρ` divides neither `atom b` nor its conjugate,
for every other atom `b` that is exceptional or has index at most that of `a`. -/
theorem private_of_max {p : ℕ} (hp : p.Prime) {a : Atom} (ha : a ∉ exceptional)
    (hord : orderOf (2 : ZMod p) = 4 * nOf a) {ρ : GaussianInt}
    (hpi : ρ * star ρ = (p : GaussianInt)) (hρa : ρ ∣ atom a) {b : Atom} (hb : b ≠ a)
    (hle : b ∉ exceptional → nOf b ≤ nOf a) : ¬ ρ ∣ atom b ∧ ¬ ρ ∣ star (atom b) := by
  have := Fact.mk hp
  have hp2 : p ≠ 2 := ne_two_of_orderOf (nOf_pos a) hord
  have hnorm : (ρ ∣ atom b ∨ ρ ∣ star (atom b)) → (p : ℤ) ∣ (atom b).norm := by
    rintro (h | h)
    · exact natCast_dvd_norm hpi h
    · simpa [Zsqrtd.norm_conj] using natCast_dvd_norm hpi h
  by_cases hbe : b ∈ exceptional
  · have hno : ¬ (ρ ∣ atom b ∨ ρ ∣ star (atom b)) := by
      intro h
      have h5 : p ∣ 5 := by exact_mod_cast (hnorm h).trans (norm_exceptional_dvd hbe)
      have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5
      subst hp5
      rw [orderOf_two_zmod_5] at hord
      rcases nOf_eq_one (by omega : nOf a = 1) with rfl | rfl <;> exact ha (by simp [exceptional])
    exact ⟨fun h => hno (Or.inl h), fun h => hno (Or.inr h)⟩
  · by_contra hcon
    have hor : ρ ∣ atom b ∨ ρ ∣ star (atom b) := by tauto
    have h4 : p ∣ 4 ^ nOf b + 1 := by exact_mod_cast (hnorm hor).trans (norm_atom_dvd b)
    have heq : nOf a = nOf b :=
      le_antisymm (le_of_orderOf (nOf_pos a) (nOf_pos b) hord h4) (hle hbe)
    exact hcon (not_dvd_pair hpi hp hp2 heq hb hρa)

/-! ## 5. Theorem B -/

/-- **Core of Theorem B**: in an integer relation `∑ c_a arg (atom a) = q π`, only exceptional
atoms have non-zero coefficients. A non-exceptional atom of largest index with `c_a ≠ 0` would
have a private prime. -/
theorem coeff_eq_zero_of_not_exceptional (s : Finset Atom) (c : Atom → ℤ) (q : ℚ)
    (h : ∑ a ∈ s, (c a : ℝ) * arg (atom a : ℂ) = q * Real.pi) :
    ∀ a ∈ s, a ∉ exceptional → c a = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set s₁ := s.filter (fun x => c x ≠ 0) with hs₁def
  set T := s₁.filter (fun x => x ∉ exceptional) with hTdef
  have hT : T.Nonempty := by
    obtain ⟨x, hx, hxs, hcx⟩ := hcon
    exact ⟨x, by simp [hTdef, hs₁def, hx, hxs, hcx]⟩
  obtain ⟨g, hgT, hgmax⟩ := Finset.exists_max_image T nOf hT
  have hgs₁ : g ∈ s₁ := (Finset.mem_filter.1 hgT).1
  have hgex : g ∉ exceptional := (Finset.mem_filter.1 hgT).2
  have hcg : c g ≠ 0 := (Finset.mem_filter.1 hgs₁).2
  have h₁ : ∑ x ∈ s₁, (c x : ℝ) * arg (atom x : ℂ) = q * Real.pi := by
    rw [hs₁def, Finset.sum_filter_of_ne (p := fun x => c x ≠ 0)
      (fun x _ hx hc => hx (by simp [hc]))]
    exact h
  obtain ⟨p, hp, hord, hpdvd⟩ := exists_primitive_atom g hgex
  have := Fact.mk hp
  obtain ⟨ρ, hρ, hpi, hρg⟩ :=
    exists_prime_dvd_of_dvd_norm hp (mod_four_eq_one_of_orderOf (nOf_pos g) hord) hpdvd
  have hp2 : p ≠ 2 := ne_two_of_orderOf (nOf_pos g) hord
  exact hcg (coeff_eq_zero_of_private_prime_gen (fun x _ => atom_ne_zero x) h₁ hρ hgs₁ hρg
    (not_dvd_star_atom hpi hp hp2 g hρg)
    (fun x hx hxg => private_of_max hp hgex hord hpi hρg hxg
      (fun hxe => hgmax x (Finset.mem_filter.2 ⟨hx, hxe⟩))))

theorem arg_gI : arg (gI : ℂ) = Real.pi / 2 := by
  rw [show ((gI : GaussianInt) : ℂ) = I by simp [gI, GaussianInt.toComplex_def']]
  exact arg_I

theorem arg_m2mi : arg (((⟨-2, -1⟩ : GaussianInt)) : ℂ) = Real.arctan (1 / 2) - Real.pi := by
  have e : (((⟨-2, -1⟩ : GaussianInt)) : ℂ) = -(((2 : ℝ) : ℂ) + I) := by
    simp [GaussianInt.toComplex_def']
    ring
  rw [e, arg_neg_eq_arg_sub_pi_of_im_pos (by simp), ← arctan_inv_eq_arg (by norm_num)]

/-- The value `∑ c_a arg (atom a)` of a rational combination of atoms. -/
noncomputable def valueB (c : Atom →₀ ℚ) : ℝ := c.sum fun a x => (x : ℝ) * arg (atom a : ℂ)

/-- **Theorem B** (on representatives). If a rational combination of the arguments of the atoms
is `q π`, then only the exceptional atoms `P 0 = i`, `Q 0 = -2 - i`, `Q 1 = i`, `Q 2 = -2 - i`
occur, `c(Q 0) + c(Q 2) = 0`, and `q = (c(P 0) + c(Q 1)) / 2`. -/
def TheoremB : Prop :=
  ∀ (c : Atom →₀ ℚ) (q : ℚ), valueB c = q * Real.pi →
    (∀ a, a ∉ exceptional → c a = 0) ∧ c (.Q 0) + c (.Q 2) = 0 ∧ q = (c (.P 0) + c (.Q 1)) / 2

theorem theoremB : TheoremB := by
  intro coeff q hval
  classical
  set s := coeff.support with hsdef
  have hval' : ∑ x ∈ s, (coeff x : ℝ) * arg (atom x : ℂ) = q * Real.pi := by
    rw [← hval]; rfl
  have hzero : ∀ x, x ∉ s → coeff x = 0 := fun x hx => by simpa [hsdef] using hx
  -- clear denominators
  obtain ⟨D, hD, hden⟩ : ∃ D : ℕ, 0 < D ∧ ∀ x, (coeff x).den ∣ D := by
    refine ⟨∏ x ∈ s, (coeff x).den, Finset.prod_pos fun x _ => (coeff x).den_pos, fun x => ?_⟩
    by_cases hx : x ∈ s
    · exact Finset.dvd_prod_of_mem _ hx
    · rw [hzero x hx]; simp
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  obtain ⟨c, hc⟩ : ∃ c : Atom → ℤ, ∀ x, (c x : ℚ) = D * coeff x := by
    refine ⟨fun x => ((D / (coeff x).den : ℕ) : ℤ) * (coeff x).num, fun x => ?_⟩
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div (hden x) (by exact_mod_cast (coeff x).den_ne_zero)]
    conv_rhs => rw [← Rat.num_div_den (coeff x)]
    field_simp
  have hcR : ∀ x, (c x : ℝ) = (D : ℝ) * coeff x := fun x => by exact_mod_cast hc x
  have hrel : ∑ x ∈ s, (c x : ℝ) * arg (atom x : ℂ) = ((D * q : ℚ) : ℝ) * Real.pi := by
    calc ∑ x ∈ s, (c x : ℝ) * arg (atom x : ℂ)
        = ∑ x ∈ s, (D : ℝ) * ((coeff x : ℝ) * arg (atom x : ℂ)) :=
          Finset.sum_congr rfl fun x _ => by rw [hcR x]; ring
      _ = (D : ℝ) * (q * Real.pi) := by rw [← Finset.mul_sum, hval']
      _ = ((D * q : ℚ) : ℝ) * Real.pi := by push_cast; ring
  -- the core: only exceptional atoms survive
  have hcore := coeff_eq_zero_of_not_exceptional s c (D * q) hrel
  have hcz : ∀ x, x ∉ exceptional → coeff x = 0 := by
    intro x hxs
    by_cases hx : x ∈ s
    · have h2 := hc x
      rw [hcore x hx hxs] at h2
      push_cast at h2
      exact (mul_eq_zero.1 h2.symm).resolve_left hDq
    · exact hzero x hx
  have hc0 : ∀ x, coeff x = 0 → c x = 0 := fun x h0 => by
    have := hc x
    rw [h0, mul_zero] at this
    exact_mod_cast this
  have hspec : ∑ x ∈ s, (c x : ℝ) * arg (atom x : ℂ) =
      ∑ x ∈ exceptional, (c x : ℝ) * arg (atom x : ℂ) := by
    calc ∑ x ∈ s, (c x : ℝ) * arg (atom x : ℂ)
        = ∑ x ∈ s ∩ exceptional, (c x : ℝ) * arg (atom x : ℂ) :=
          (Finset.sum_subset Finset.inter_subset_left fun x hxs hxn => by
            have : x ∉ exceptional := fun h => hxn (Finset.mem_inter.2 ⟨hxs, h⟩)
            simp [hc0 x (hcz x this)]).symm
      _ = ∑ x ∈ exceptional, (c x : ℝ) * arg (atom x : ℂ) :=
          Finset.sum_subset Finset.inter_subset_right fun x hxsp hxn => by
            have : x ∉ s := fun h => hxn (Finset.mem_inter.2 ⟨h, hxsp⟩)
            simp [hc0 x (hzero x this)]
  -- the four exceptional atoms
  have h4 : (c (.P 0) : ℝ) * (Real.pi / 2) + c (.Q 0) * (Real.arctan (1 / 2) - Real.pi) +
      c (.Q 1) * (Real.pi / 2) + c (.Q 2) * (Real.arctan (1 / 2) - Real.pi) =
      ((D * q : ℚ) : ℝ) * Real.pi := by
    rw [← hrel, hspec]
    simp [exceptional, atom_P0, atom_Q0, atom_Q1, atom_Q2, arg_gI, arg_m2mi]
    ring
  have key : ((c (.Q 0) + c (.Q 2) : ℤ) : ℝ) * Real.arctan (1 / 2) =
      ((D * q - (c (.P 0) + c (.Q 1)) / 2 + (c (.Q 0) + c (.Q 2)) : ℚ) : ℝ) * Real.pi := by
    push_cast at h4 ⊢
    linear_combination h4
  have hK := int_mul_arctan_half_eq_zero _ _ key
  rw [hK] at key
  have hq : ((D * q - (c (.P 0) + c (.Q 1)) / 2 + (c (.Q 0) + c (.Q 2)) : ℚ) : ℝ) = 0 := by
    have := Real.pi_pos
    push_cast at key ⊢
    nlinarith [key]
  have hq2 : (D * q - (c (.P 0) + c (.Q 1)) / 2 + (c (.Q 0) + c (.Q 2)) : ℚ) = 0 := by
    exact_mod_cast hq
  have hK2 : ((c (.Q 0) + c (.Q 2) : ℤ) : ℚ) = 0 := by exact_mod_cast hK
  push_cast at hK2
  simp only [hc] at hq2 hK2
  refine ⟨hcz, ?_, ?_⟩
  · have : (D : ℚ) * (coeff (.Q 0) + coeff (.Q 2)) = 0 := by linear_combination hK2
    exact (mul_eq_zero.1 this).resolve_left hDq
  · have : (D : ℚ) * (q - (coeff (.P 0) + coeff (.Q 1)) / 2) = 0 := by
      linear_combination hq2 - hK2
    linarith [(mul_eq_zero.1 this).resolve_left hDq]

/-- The converse: the exceptional relations hold. -/
theorem theoremB_converse (α β δ : ℚ) :
    (α : ℝ) * arg (atom (.P 0) : ℂ) + β * arg (atom (.Q 1) : ℂ) +
      δ * (arg (atom (.Q 0) : ℂ) - arg (atom (.Q 2) : ℂ)) = ((α + β) / 2 : ℚ) * Real.pi := by
  rw [atom_P0, atom_Q1, atom_Q0, atom_Q2, arg_gI]
  push_cast
  ring

end PiFormula
