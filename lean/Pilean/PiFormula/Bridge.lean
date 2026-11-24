module

public import Mathlib

/-!
# From arctangent relations to Gaussian integers

The first step of the proof of Theorem A (pi_formula_theorem.md): an arctangent
relation `∑ c_n arctan (1/n) = q π` with integer coefficients says that a product of
the Gaussian integers `n + i` (with `n + i` replaced by its conjugate where `c_n < 0`)
has an argument that is a rational multiple of `π`, so a power of it is real.

Main result: `PiFormula.star_pow_W_eq`.
-/

@[expose] public section

open Complex Real

namespace PiFormula

/-- The Gaussian integer `n + i`. -/
def gz (n : ℕ) : GaussianInt := ⟨n, 1⟩

theorem gz_toComplex (n : ℕ) : ((gz n : GaussianInt) : ℂ) = (n : ℂ) + I := by
  simp [gz, GaussianInt.toComplex_def']

theorem gz_ne_zero (n : ℕ) : gz n ≠ 0 := by
  intro h
  have := congrArg Zsqrtd.im h
  simp [gz] at this

/-- `arctan (1/x) = arg (x + i)` for `x > 0`. -/
theorem arctan_inv_eq_arg {x : ℝ} (hx : 0 < x) :
    Real.arctan (1 / x) = Complex.arg ((x : ℂ) + I) := by
  have hre : 0 < ((x : ℂ) + I).re := by simp [hx]
  obtain ⟨h1, h2⟩ := abs_lt.1 ((Complex.abs_arg_lt_pi_div_two_iff).2 (Or.inl hre))
  rw [← Real.arctan_tan h1 h2, Complex.tan_arg]
  simp

/-- `z ^ c` for `c ≥ 0` and `(conj z) ^ (-c)` for `c < 0`: a Gaussian integer whose argument
is `c` times that of `z`. -/
def spow (z : GaussianInt) (c : ℤ) : GaussianInt :=
  if 0 ≤ c then z ^ c.toNat else (star z) ^ (-c).toNat

theorem spow_ne_zero {z : GaussianInt} (hz : z ≠ 0) (c : ℤ) : spow z c ≠ 0 := by
  unfold spow
  split_ifs
  · exact pow_ne_zero _ hz
  · exact pow_ne_zero _ (by simpa using hz)

theorem arg_spow {z : GaussianInt} (c : ℤ) :
    (arg ((spow z c : GaussianInt) : ℂ) : Real.Angle) = c • (arg (z : ℂ) : Real.Angle) := by
  unfold spow
  split_ifs with hc
  · rw [map_pow, Complex.arg_pow_coe_angle]
    conv_rhs => rw [← Int.toNat_of_nonneg hc]
    rw [natCast_zsmul]
  · rw [map_pow, Complex.arg_pow_coe_angle, GaussianInt.toComplex_star,
      Complex.arg_conj_coe_angle]
    have : ((-c).toNat : ℤ) = -c := Int.toNat_of_nonneg (by omega)
    rw [smul_neg, ← natCast_zsmul, this, neg_zsmul, neg_neg]

theorem arg_prod_coe_angle {ι : Type*} (s : Finset ι) (f : ι → ℂ) (hf : ∀ n ∈ s, f n ≠ 0) :
    (arg (∏ n ∈ s, f n) : Real.Angle) = ∑ n ∈ s, (arg (f n) : Real.Angle) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Complex.arg_mul_coe_angle (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun n hn => hf n (Finset.mem_insert_of_mem hn)),
      ih fun n hn => hf n (Finset.mem_insert_of_mem hn)]

/-- The product `∏ (f i + i)^{c_i}` (conjugates for negative exponents), over an index set
`s` with a map `f` to the positive integers. -/
def W {ι : Type*} (s : Finset ι) (f : ι → ℕ) (c : ι → ℤ) : GaussianInt :=
  ∏ n ∈ s, spow (gz (f n)) (c n)

theorem W_ne_zero {ι : Type*} (s : Finset ι) (f : ι → ℕ) (c : ι → ℤ) : W s f c ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun n _ => spow_ne_zero (gz_ne_zero (f n)) (c n)

theorem arg_W {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hs : ∀ n ∈ s, 0 < f n) (c : ι → ℤ) :
    (arg ((W s f c : GaussianInt) : ℂ) : Real.Angle) =
      ((∑ n ∈ s, (c n : ℝ) * Real.arctan (1 / f n) : ℝ) : Real.Angle) := by
  unfold W
  rw [map_prod, arg_prod_coe_angle _ _ fun n _ => by
      rw [Ne, GaussianInt.toComplex_eq_zero]; exact spow_ne_zero (gz_ne_zero (f n)) (c n)]
  rw [show ((∑ n ∈ s, (c n : ℝ) * Real.arctan (1 / f n) : ℝ) : Real.Angle) =
      ∑ n ∈ s, (((c n : ℝ) * Real.arctan (1 / f n) : ℝ) : Real.Angle) from
    map_sum Real.Angle.coeHom _ _]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [arg_spow, gz_toComplex, arctan_inv_eq_arg (by exact_mod_cast hs n hn),
    Complex.ofReal_natCast, ← zsmul_eq_mul, Real.Angle.coe_zsmul]

/-- A complex number whose argument is an integer multiple of `π` (as an angle) is real. -/
theorem im_eq_zero_of_arg_coe_angle {w : ℂ} {a : ℤ}
    (h : (arg w : Real.Angle) = ((a * π : ℝ) : Real.Angle)) : w.im = 0 := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h
  have hpos := Complex.neg_pi_lt_arg w
  have hle := Complex.arg_le_pi w
  have harg : arg w = (a + 2 * k : ℤ) * π := by push_cast; linarith
  have hm1 : -1 < (a + 2 * k : ℤ) := by
    have : -π < ((a + 2 * k : ℤ) : ℝ) * π := harg ▸ hpos
    have : (-1 : ℝ) < (a + 2 * k : ℤ) := by nlinarith [Real.pi_pos]
    exact_mod_cast this
  have hm2 : (a + 2 * k : ℤ) ≤ 1 := by
    have : ((a + 2 * k : ℤ) : ℝ) * π ≤ π := harg ▸ hle
    have : ((a + 2 * k : ℤ) : ℝ) ≤ 1 := by nlinarith [Real.pi_pos]
    exact_mod_cast this
  rcases (show (a + 2 * k : ℤ) = 0 ∨ (a + 2 * k : ℤ) = 1 by omega) with h0 | h1
  · rw [h0] at harg
    exact (Complex.arg_eq_zero_iff.1 (by simpa using harg)).2
  · rw [h1] at harg
    exact (Complex.arg_eq_pi_iff.1 (by simpa using harg)).2

/-- **The bridge.** If `∑ c_n arctan (1/n) = q π` with `q` rational, then `W ^ (den q)` is real,
that is, fixed by complex conjugation. -/
theorem star_pow_W_eq {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hs : ∀ n ∈ s, 0 < f n)
    (c : ι → ℤ) (q : ℚ) (h : ∑ n ∈ s, (c n : ℝ) * Real.arctan (1 / f n) = q * π) :
    star (W s f c ^ q.den) = W s f c ^ q.den := by
  set w : ℂ := ((W s f c ^ q.den : GaussianInt) : ℂ) with hw
  have hangle : (arg w : Real.Angle) = ((q.num * π : ℝ) : Real.Angle) := by
    rw [hw, map_pow, Complex.arg_pow_coe_angle, arg_W s f hs c, h, ← Real.Angle.coe_nsmul,
      nsmul_eq_mul]
    congr 1
    have : (q.den : ℝ) * q = q.num := by exact_mod_cast Rat.den_mul_eq_num q
    rw [← mul_assoc, this]
  have him : w.im = 0 := im_eq_zero_of_arg_coe_angle hangle
  have him' : (W s f c ^ q.den).im = 0 := by
    have := GaussianInt.intCast_im (W s f c ^ q.den)
    rw [← hw, him] at this
    exact_mod_cast this
  ext
  · exact Zsqrtd.re_star _
  · rw [Zsqrtd.im_star, him', neg_zero]

end PiFormula
