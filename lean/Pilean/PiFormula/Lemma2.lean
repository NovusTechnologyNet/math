import Pilean.PiFormula
import Pilean.PiFormula.Orders
import Pilean.PiFormula.TheoremA
import TauCeti.NumberTheory.PrimitivePrimeDivisors.Cyclotomic

/-!
# Lemma 2: primitive primes in both Aurifeuillian factors of `4^n + 1`

`Lemma2` (statement in `PiFormula.lean`): for odd `n`, `M_n` has a prime `p` with
`orderOf (2 : ZMod p) = 4n`, and so does `L_n` when `n ≥ 7`.

The proof (pi_formula_theorem.md, Lemma 2), with `t = 1 + i`:

1. **Reduction** (`exists_primitive_of_dvd_Phi4`, proved): a divisor `X > n` of `Φ_{4n}(2)` has
   a prime factor of order `4n`. A non-primitive prime of `Φ_{4n}(2)` divides `n`, is the
   largest prime factor of `4n`, and divides `Φ_{4n}(2)` once (Tau Ceti), so a divisor
   without primitive primes is `1` or that prime, hence `≤ n`.
2. **Gaussian factorization**: `A_n = N(Φ_n(t))` divides `N(t^n - 1)` and `A'_n = N(Φ_n(-t))`
   divides `N((-t)^n - 1) = N(t^n + 1)` (`Aplus_dvd_Uplus`, `Aminus_dvd_Uminus`, proved);
   for odd `n` these two norms are `L_n` and `M_n` in some order (`Uplus_Uminus_odd`,
   proved); and `A_n * A'_n = Φ_{4n}(2)` (`Aplus_mul_Aminus`, proved, via
   `Φ_{2n}(X) = Φ_n(-X)` for odd `n > 1`, `cyclotomic_two_mul_of_odd`, which is not in
   Mathlib and is proved here from the roots of unity in ℂ).
3. **Size bound** (`size_bound`, proved): `A_n > n` and `A'_n > n` for odd `n ≥ 7`, by Möbius
   inversion, a uniform bound for `n ≥ 82` and a kernel check of the odd `n` from 7 to 81.
4. **Small cases** `M_1 = 5`, `M_3 = 13`, `M_5 = 41` (proved) and the assembly (`lemma2`,
   proved from 1-3).
-/

open Polynomial

namespace PiFormula

/-! ## 1. The reduction to a size bound -/

/-- `Φ_{4n}(2)`. -/
noncomputable def Phi4 (n : ℕ) : ℤ := (cyclotomic (4 * n) ℤ).eval 2

theorem Phi4_pos {n : ℕ} (hn : 0 < n) : 0 < Phi4 n :=
  cyclotomic_pos (by omega) 2

theorem homogeneous_eq_Phi4 (n : ℕ) :
    TauCeti.homogeneousCyclotomic (4 * n) ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = Phi4 n := by
  rw [Nat.cast_ofNat, Nat.cast_one, TauCeti.homogeneousCyclotomic_one_right]
  rfl

/-- A prime of `Φ_{4n}(2)` whose order is not `4n` divides `n`, is at least every prime factor
of `4n`, and divides `Φ_{4n}(2)` exactly once. -/
theorem nonprimitive {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hdvd : (p : ℤ) ∣ Phi4 n)
    (hord : orderOf (2 : ZMod p) ≠ 4 * n) :
    p ∣ n ∧ (∀ q : ℕ, q.Prime → q ∣ 4 * n → q ≤ p) ∧ multiplicity (p : ℤ) (Phi4 n) = 1 := by
  have hdvd' := (homogeneous_eq_Phi4 n).symm ▸ hdvd
  have hp2 : ¬ p ∣ 2 * 1 :=
    Nat.Coprime.not_dvd_mul_of_dvd_homogeneousCyclotomic (by norm_num) hp hdvd'
  have hb : ¬ (p : ℤ) ∣ ((1 : ℕ) : ℤ) := by
    norm_cast; exact hp.not_dvd_one
  have hiff0 := (hp.dvd_homogeneousCyclotomic_iff_orderOf_eq hb (by omega : 4 * n ≠ 0)).1 hdvd'
  have hiff : orderOf (2 : ZMod p) = ordCompl[p] (4 * n) := by simpa using hiff0
  have hk0 : 0 < orderOf (2 : ZMod p) := hiff ▸ Nat.ordCompl_pos p (by omega)
  have hk4 : orderOf (2 : ZMod p) < 4 * n := lt_of_le_of_ne (hiff ▸ Nat.ordCompl_le _ _) hord
  have hpk : p ∣ 2 ^ orderOf (2 : ZMod p) - 1 ^ orderOf (2 : ZMod p) := by
    rw [one_pow, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow,
      Nat.cast_ofNat, pow_orderOf_eq_one, Nat.cast_one, sub_self]
  obtain ⟨hpn, hle, hmul⟩ := hp.multiplicity_homogeneousCyclotomic_of_not_primitive
    (by norm_num : Nat.Coprime 2 1) (by norm_num) (by omega : 4 * n ≠ 2) hdvd'
    ⟨_, hk0, hk4, hpk⟩
  refine ⟨?_, hle, (homogeneous_eq_Phi4 n) ▸ hmul⟩
  have hp2' : ¬ p ∣ 2 := by simpa using hp2
  have hcop : Nat.Coprime p 4 := (Nat.Prime.coprime_iff_not_dvd hp).2 fun h4 =>
    hp2' (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4))
  exact hcop.dvd_of_dvd_mul_left hpn

/-- **The reduction.** A divisor `X > n` of `Φ_{4n}(2)` has a prime factor of order `4n`. -/
theorem exists_primitive_of_dvd_Phi4 {n X : ℕ} (hn : 0 < n) (hX : (X : ℤ) ∣ Phi4 n)
    (hXn : n < X) : ∃ p, p.Prime ∧ orderOf (2 : ZMod p) = 4 * n ∧ p ∣ X := by
  by_contra hno
  push Not at hno
  have key : ∀ p, p.Prime → p ∣ X → p ∣ n ∧ (∀ q : ℕ, q.Prime → q ∣ 4 * n → q ≤ p) ∧
      multiplicity (p : ℤ) (Phi4 n) = 1 := fun p hp hpX =>
    nonprimitive hn hp ((Int.natCast_dvd_natCast.2 hpX).trans hX) (fun h => hno p hp h hpX)
  obtain ⟨p₀, hp₀, Y, rfl⟩ := Nat.exists_prime_and_dvd (show X ≠ 1 by omega)
  have k₀ := key p₀ hp₀ (dvd_mul_right _ _)
  by_cases hY : Y = 1
  · subst hY
    have := Nat.le_of_dvd hn k₀.1
    omega
  obtain ⟨p₁, hp₁, hp₁Y⟩ := Nat.exists_prime_and_dvd hY
  have k₁ := key p₁ hp₁ (hp₁Y.trans (dvd_mul_left _ _))
  have heq : p₁ = p₀ := le_antisymm (k₀.2.1 p₁ hp₁ (k₁.1.trans (dvd_mul_left _ _)))
    (k₁.2.1 p₀ hp₀ (k₀.1.trans (dvd_mul_left _ _)))
  rw [heq] at hp₁Y
  have hsq : ((p₀ : ℤ) ^ 2) ∣ Phi4 n := by
    have h1 : p₀ ^ 2 ∣ p₀ * Y := by rw [sq]; exact Nat.mul_dvd_mul_left _ hp₁Y
    have h2 := (Int.natCast_dvd_natCast.2 h1).trans hX
    simpa using h2
  have hfin : FiniteMultiplicity (p₀ : ℤ) (Phi4 n) :=
    FiniteMultiplicity.of_prime_left (Nat.prime_iff_prime_int.1 hp₀) (Phi4_pos hn).ne'
  exact hfin.not_pow_dvd_of_multiplicity_lt (by rw [k₀.2.2]; norm_num) hsq

/-! ## 2. The Gaussian factorization -/

/-- `t = 1 + i`. -/
def tG : GaussianInt := ⟨1, 1⟩

/-- `A_n = N(Φ_n(t))`. -/
noncomputable def Aplus (n : ℕ) : ℤ := ((cyclotomic n GaussianInt).eval tG).norm

/-- `A'_n = N(Φ_n(-t))`. -/
noncomputable def Aminus (n : ℕ) : ℤ := ((cyclotomic n GaussianInt).eval (-tG)).norm

/-- `N(t^n - 1)`. -/
def Uplus (n : ℕ) : ℤ := (tG ^ n - 1).norm

/-- `N((-t)^n - 1)`, which is `N(t^n + 1)` for odd `n`. -/
def Uminus (n : ℕ) : ℤ := ((-tG) ^ n - 1).norm

/-- `∏_{d ∣ n} N(Φ_d(z)) = N(z^n - 1)`. -/
theorem prod_norm_eval_cyclotomic (z : GaussianInt) {n : ℕ} (hn : 0 < n) :
    ∏ i ∈ n.divisors, ((cyclotomic i GaussianInt).eval z).norm = (z ^ n - 1).norm := by
  have h := congrArg (Polynomial.eval z) (prod_cyclotomic_eq_X_pow_sub_one hn GaussianInt)
  rw [Polynomial.eval_prod] at h
  simp only [eval_sub, eval_pow, eval_X, eval_one] at h
  rw [← h]
  exact (map_prod Zsqrtd.normMonoidHom _ _).symm

theorem norm_eval_cyclotomic_dvd (z : GaussianInt) {n : ℕ} (hn : 0 < n) :
    ((cyclotomic n GaussianInt).eval z).norm ∣ (z ^ n - 1).norm := by
  rw [← prod_norm_eval_cyclotomic z hn]
  exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self n hn.ne')

theorem Aplus_dvd_Uplus {n : ℕ} (hn : 0 < n) : Aplus n ∣ Uplus n :=
  norm_eval_cyclotomic_dvd tG hn

theorem Aminus_dvd_Uminus {n : ℕ} (hn : 0 < n) : Aminus n ∣ Uminus n :=
  norm_eval_cyclotomic_dvd (-tG) hn

theorem Aplus_nonneg (n : ℕ) : 0 ≤ Aplus n := GaussianInt.norm_nonneg _

theorem Aminus_nonneg (n : ℕ) : 0 ≤ Aminus n := GaussianInt.norm_nonneg _

/-- `t^(2k+1) = ±2^k ± 2^k i`. -/
theorem tG_pow_odd (k : ℕ) :
    (tG ^ (2 * k + 1)).re ^ 2 = 4 ^ k ∧ (tG ^ (2 * k + 1)).im ^ 2 = 4 ^ k := by
  induction k with
  | zero => simp [tG]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have ht2 : tG ^ 2 = ⟨0, 2⟩ := by ext <;> simp [tG, sq]
    have hpow : tG ^ (2 * (k + 1) + 1) = tG ^ (2 * k + 1) * ⟨0, 2⟩ := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, ht2]
    rw [hpow]
    constructor
    · simp only [Zsqrtd.re_mul]
      linear_combination 4 * h2
    · simp only [Zsqrtd.im_mul]
      linear_combination 4 * h1

/-- For odd `n`, the norms of `t^n - 1` and `t^n + 1` are `L_n` and `M_n` in some order. -/
theorem Uplus_Uminus_odd (k : ℕ) :
    (Uplus (2 * k + 1) = L (2 * k + 1) ∧ Uminus (2 * k + 1) = M (2 * k + 1)) ∨
      (Uplus (2 * k + 1) = M (2 * k + 1) ∧ Uminus (2 * k + 1) = L (2 * k + 1)) := by
  obtain ⟨hre, him⟩ := tG_pow_odd k
  set a := (tG ^ (2 * k + 1)).re with ha
  set b := (tG ^ (2 * k + 1)).im with hb
  have hU : Uplus (2 * k + 1) = 2 * 4 ^ k + 1 - 2 * a := by
    unfold Uplus
    rw [Zsqrtd.norm_def]
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one, ← ha, ← hb]
    linear_combination hre + him
  have hV : Uminus (2 * k + 1) = 2 * 4 ^ k + 1 + 2 * a := by
    unfold Uminus
    rw [Odd.neg_pow ⟨k, rfl⟩, Zsqrtd.norm_def]
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_neg, Zsqrtd.im_neg, Zsqrtd.re_one,
      Zsqrtd.im_one, ← ha, ← hb]
    linear_combination hre + him
  have h4 : (4 : ℤ) ^ k = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hL : L (2 * k + 1) = 2 * 4 ^ k - 2 * 2 ^ k + 1 := by
    unfold L
    rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, h4]
    ring
  have hM : M (2 * k + 1) = 2 * 4 ^ k + 2 * 2 ^ k + 1 := by
    unfold M
    rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, h4]
    ring
  rcases eq_or_eq_neg_of_sq_eq_sq a (2 ^ k) (by rw [hre, h4]) with h | h
  · left
    exact ⟨by rw [hU, hL, h]; ring, by rw [hV, hM, h]; ring⟩
  · right
    exact ⟨by rw [hU, hM, h]; ring, by rw [hV, hL, h]; ring⟩

/-! ### `Φ_{2n}(X) = Φ_n(-X)` for odd `n > 1` -/

/-- Over ℂ: negation maps the primitive `n`-th roots of unity bijectively onto the primitive
`2n`-th roots (`n` odd), and `φ(n)` is even, so
`Φ_n(-X) = ∏ (-X - μ) = ∏ (X - (-μ)) = Φ_{2n}(X)`. -/
theorem cyclotomic_two_mul_complex {n : ℕ} (hn : Odd n) (h1 : 1 < n) :
    cyclotomic (2 * n) ℂ = (cyclotomic n ℂ).comp (-X) := by
  have hn0 : n ≠ 0 := by omega
  have h3 : 2 < n := by obtain ⟨k, hk⟩ := hn; omega
  have hcop : Nat.Coprime 2 n :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hn))
  have hneg : ∀ μ : ℂ, IsPrimitiveRoot μ n → IsPrimitiveRoot (-μ) (2 * n) := by
    intro μ hμ
    have h2 : orderOf (-1 : ℂ) = 2 := by rw [orderOf_neg_one, ringChar.eq_zero]; norm_num
    have hord : orderOf (-μ) = 2 * n := by
      rw [neg_eq_neg_one_mul, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime
        (by rw [h2, ← hμ.eq_orderOf]; exact hcop), h2, ← hμ.eq_orderOf]
    exact hord ▸ IsPrimitiveRoot.orderOf (-μ)
  have hζ := Complex.isPrimitiveRoot_exp n hn0
  have himage : primitiveRoots (2 * n) ℂ = (primitiveRoots n ℂ).image (fun μ => -μ) := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro ν hν
      obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.1 hν
      exact (mem_primitiveRoots (by omega)).2 (hneg μ ((mem_primitiveRoots (by omega)).1 hμ))
    · rw [Finset.card_image_of_injective _ neg_injective, Complex.card_primitiveRoots,
        Complex.card_primitiveRoots, Nat.totient_mul hcop, Nat.totient_two, one_mul]
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, cyclotomic_eq_prod_X_sub_primitiveRoots
    (hneg _ hζ), himage, Finset.prod_image (fun x _ y _ h => neg_injective h),
    ← coe_compRingHom_apply, map_prod]
  simp only [coe_compRingHom_apply, sub_comp, X_comp, C_comp]
  have hterm : ∀ μ : ℂ, (-X - C μ : ℂ[X]) = (-1) * (X - C (-μ)) := fun μ => by
    rw [C_neg]; ring
  simp only [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Complex.card_primitiveRoots,
    (Nat.totient_even h3).neg_one_pow, one_mul]

/-- `Φ_{2n}(X) = Φ_n(-X)` for odd `n > 1`, over any commutative ring. -/
theorem cyclotomic_two_mul_of_odd {n : ℕ} (hn : Odd n) (h1 : 1 < n) (R : Type*) [CommRing R] :
    cyclotomic (2 * n) R = (cyclotomic n R).comp (-X) := by
  have hZ : cyclotomic (2 * n) ℤ = (cyclotomic n ℤ).comp (-X) := by
    apply Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
    rw [map_cyclotomic, Polynomial.map_comp, map_cyclotomic, Polynomial.map_neg, Polynomial.map_X]
    exact cyclotomic_two_mul_complex hn h1
  rw [← map_cyclotomic_int (2 * n) R, hZ, Polynomial.map_comp, Polynomial.map_neg,
    Polynomial.map_X, map_cyclotomic_int]

theorem tG_sq : tG ^ 2 = ⟨0, 2⟩ := by ext <;> simp [tG, sq]

/-- `A_n * A'_n = Φ_{4n}(2)` for odd `n`: `A_n A'_n = N(Φ_n(t) Φ_n(-t)) = N(Φ_n(t²)) = N(Φ_n(2i))`,
and `N(Φ_n(2i)) = Φ_n(2i) Φ_n(-2i) = Φ_n(-4) = Φ_{2n}(4) = Φ_{4n}(2)`. -/
theorem Aplus_mul_Aminus {n : ℕ} (hn : Odd n) : Aplus n * Aminus n = Phi4 n := by
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · have hdiv : ¬ 2 ∣ n := Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hn)
    set Φ := cyclotomic n GaussianInt with hΦ
    -- Φ_n(z²) = Φ_{2n}(z) Φ_n(z) and Φ_{2n}(z) = Φ_n(-z)
    have E1 : ∀ z : GaussianInt, (cyclotomic (n * 2) GaussianInt).eval z = Φ.eval (-z) := by
      intro z
      rw [mul_comm, cyclotomic_two_mul_of_odd hn h1, eval_comp, eval_neg, eval_X]
    have prodE : ∀ z : GaussianInt, Φ.eval z * Φ.eval (-z) = Φ.eval (z ^ 2) := by
      intro z
      rw [← expand_eval, cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two hdiv, eval_mul, E1]
      ring
    -- conjugation commutes with evaluation
    have hstar : ∀ w : GaussianInt, star (Φ.eval w) = Φ.eval (star w) := by
      intro w
      have := Polynomial.eval₂_at_apply (p := Φ) (starRingEnd GaussianInt) w
      rw [← Polynomial.eval_map, hΦ, map_cyclotomic, starRingEnd_apply, starRingEnd_apply] at this
      rw [hΦ]
      exact this.symm
    have hw1 : star (tG ^ 2) = -(tG ^ 2) := by rw [tG_sq]; ext <;> simp
    have hw2 : (tG ^ 2) ^ 2 = -4 := by rw [tG_sq]; ext <;> simp [sq]
    -- the norm, read in ℤ[i]
    have hnorm : ((Φ.eval (tG ^ 2)).norm : GaussianInt) = Φ.eval (-4) := by
      rw [Zsqrtd.norm_eq_mul_conj, hstar, hw1, prodE, hw2]
    -- Φ_n(-4) = Φ_{2n}(4) = Φ_{4n}(2)
    have h4 : Φ.eval (-4) = (cyclotomic (4 * n) GaussianInt).eval 2 := by
      rw [← E1, show 4 * n = n * 2 * 2 by ring, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two
        (dvd_mul_left 2 n), expand_eval]
      norm_num
    have hPhi : ((Phi4 n : ℤ) : GaussianInt) = (cyclotomic (4 * n) GaussianInt).eval 2 := by
      have := Polynomial.eval₂_at_apply (p := cyclotomic (4 * n) ℤ) (Int.castRingHom GaussianInt) 2
      rw [← Polynomial.eval_map, map_cyclotomic_int] at this
      simpa [Phi4] using this.symm
    have hprod : Aplus n * Aminus n = (Φ.eval (tG ^ 2)).norm := by
      unfold Aplus Aminus
      rw [← Zsqrtd.norm_mul, ← hΦ, prodE]
    have hcast : ((Aplus n * Aminus n : ℤ) : GaussianInt) = ((Phi4 n : ℤ) : GaussianInt) := by
      rw [hprod, hnorm, h4, hPhi]
    have := congrArg Zsqrtd.re hcast
    simpa using this
  · -- n = 1: A_1 = N(i) = 1, A'_1 = N(-2 - i) = 5, Φ_4(2) = 5
    obtain rfl : n = 1 := by obtain ⟨k, hk⟩ := hn; omega
    have hP : Phi4 1 = 5 := by
      unfold Phi4
      rw [show 4 * 1 = 2 * 2 by norm_num, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two
        (dvd_refl 2), expand_eval, cyclotomic_two]
      norm_num
    rw [hP]
    unfold Aplus Aminus
    rw [cyclotomic_one]
    simp [tG, Zsqrtd.norm_def]

/-! ### The size bound

`A_n = ∏_{ab = n} U_b^{μ(a)}` (Möbius inversion of `∏_{d ∣ n} A_d = U_n`), with `U_b ∈ {L_b, M_b}`
for odd `b`. Each factor is at least `2^{μ(a) b} 2^b / M_b`, so
`A_n ∏_{d ∣ n} M_d ≥ 2^φ(n) ∏_{d ∣ n} 2^d` (`lower_bound`). Then `A_n > n` follows from the
arithmetic criterion `n ∏ M_d < 2^φ(n) ∏ 2^d` (`Crit`): for odd `n ≥ 82` from
`∏_{d ∣ n} M_d ≤ 9 ∏_{d ∣ n} 2^d`, `φ(n)² ≥ n` and `9 s² < 2^s` (`s ≥ 10`); for the odd `n` from
7 to 81 by a kernel computation. -/

section SizeBound

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

theorem norm_tG : tG.norm = 2 := by simp [tG, Zsqrtd.norm_def]

theorem norm_neg_tG : (-tG).norm = 2 := by simp [tG, Zsqrtd.norm_def]

/-- `N(z^n - 1) ≠ 0` when `N(z) = 2` and `n > 0`. -/
theorem norm_pow_sub_one_ne_zero {z : GaussianInt} (hz : z.norm = 2) {n : ℕ} (hn : 0 < n) :
    (z ^ n - 1).norm ≠ 0 := by
  intro h
  rw [GaussianInt.norm_eq_zero, sub_eq_zero] at h
  have h2 := congrArg Zsqrtd.norm h
  rw [show (z ^ n).norm = z.norm ^ n from map_pow Zsqrtd.normMonoidHom z n, hz,
    Zsqrtd.norm_one] at h2
  have : (1 : ℤ) < 2 ^ n := one_lt_pow₀ (by norm_num) hn.ne'
  omega

/-- Möbius inversion: `N(Φ_n(z)) = ∏_{ab = n} N(z^b - 1)^{μ(a)}`, in ℝ. -/
theorem moebius_formula {z : GaussianInt} (hz : z.norm = 2) {n : ℕ} (hn : 0 < n) :
    ∏ x ∈ n.divisorsAntidiagonal, ((z ^ x.2 - 1).norm : ℝ) ^ (μ x.1) =
      (((cyclotomic n GaussianInt).eval z).norm : ℝ) := by
  have hU : ∀ m : ℕ, 0 < m → ((z ^ m - 1).norm : ℝ) ≠ 0 := fun m hm => by
    exact_mod_cast norm_pow_sub_one_ne_zero hz hm
  have hA : ∀ m : ℕ, 0 < m → (((cyclotomic m GaussianInt).eval z).norm : ℝ) ≠ 0 := by
    intro m hm h
    have h0 : ((cyclotomic m GaussianInt).eval z).norm = 0 := by exact_mod_cast h
    exact norm_pow_sub_one_ne_zero hz hm (zero_dvd_iff.1 (h0 ▸ norm_eval_cyclotomic_dvd z hm))
  refine (prod_eq_iff_prod_pow_moebius_eq_of_ne_zero
    (f := fun m => (((cyclotomic m GaussianInt).eval z).norm : ℝ))
    (g := fun m => ((z ^ m - 1).norm : ℝ)) hA hU).1 (fun m hm => ?_) n hn
  exact_mod_cast prod_norm_eval_cyclotomic z hm

/-- `∑_{ab = n} μ(a) b = φ(n)`. -/
theorem sum_moebius_mul_eq_totient {n : ℕ} (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * (x.2 : ℤ) = n.totient := by
  have := (sum_eq_iff_sum_mul_moebius_eq (R := ℤ) (f := fun m => (m.totient : ℤ))
    (g := fun m => (m : ℤ))).1 (fun m _ => by exact_mod_cast Nat.sum_totient m) n hn
  simpa using this

theorem two_zpow_sum (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℤ) :
    (2 : ℝ) ^ (∑ i ∈ s, f i) = ∏ i ∈ s, (2 : ℝ) ^ f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ two_ne_zero, ih]

/-- One factor of the Möbius product: if `L ≤ U ≤ M`, `L M = 4^b + 1` and `2^b ≤ M`, then
`U^m M ≥ 2^{mb} 2^b` for `m ∈ {0, 1, -1}`. -/
theorem factor_bound {U Lb Mb : ℝ} (b : ℕ) {m : ℤ} (hm : m = 0 ∨ m = 1 ∨ m = -1)
    (hL0 : 0 < Lb) (hLU : Lb ≤ U) (hUM : U ≤ Mb) (hLM : Lb * Mb = 4 ^ b + 1)
    (hM : 2 ^ b ≤ Mb) :
    (2 : ℝ) ^ (m * b) * 2 ^ b ≤ U ^ m * Mb := by
  have hMb : 0 ≤ Mb := le_trans (by positivity) hM
  rcases hm with rfl | rfl | rfl
  · simpa using hM
  · have h4 : (2 : ℝ) ^ b * 2 ^ b = 4 ^ b := by rw [← mul_pow]; norm_num
    simp only [one_mul, zpow_one, zpow_natCast]
    rw [h4]
    have := mul_le_mul_of_nonneg_right hLU hMb
    linarith
  · have hU0 : 0 < U := lt_of_lt_of_le hL0 hLU
    have h2 : (2 : ℝ) ^ ((-1 : ℤ) * b) * 2 ^ b = 1 := by
      rw [neg_one_mul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]
    rw [h2, zpow_neg_one, inv_mul_eq_div, one_le_div hU0]
    exact hUM

/-- For odd `b`: `0 < L_b ≤ M_b`, `L_b M_b = 4^b + 1`, `2^b ≤ M_b`. -/
theorem LM_facts {b : ℕ} (hb : Odd b) :
    0 < L b ∧ L b ≤ M b ∧ L b * M b = 4 ^ b + 1 ∧ 2 ^ b ≤ M b := by
  obtain ⟨k, rfl⟩ := hb
  unfold L M
  rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega]
  have h1 : (2 : ℤ) ^ (k + 1) ≤ 2 ^ (2 * k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (0 : ℤ) < 2 ^ (k + 1) := by positivity
  exact ⟨by linarith, by linarith, aurifeuille k, by linarith⟩

/-- **Lower bound.** If `N(z) = 2` and `N(z^b - 1) ∈ {L_b, M_b}` for odd `b`, then for odd `n`,
`N(Φ_n(z)) ∏_{d ∣ n} M_d ≥ 2^φ(n) ∏_{d ∣ n} 2^d`. -/
theorem lower_bound {z : GaussianInt} (hz : z.norm = 2)
    (hU : ∀ b, Odd b → (z ^ b - 1).norm = L b ∨ (z ^ b - 1).norm = M b) {n : ℕ} (hn : Odd n) :
    (2 : ℝ) ^ n.totient * ∏ d ∈ n.divisors, (2 : ℝ) ^ d ≤
      (((cyclotomic n GaussianInt).eval z).norm : ℝ) * ∏ d ∈ n.divisors, (M d : ℝ) := by
  have hn0 : 0 < n := hn.pos
  rw [← moebius_formula hz hn0]
  have hφ : (2 : ℝ) ^ n.totient =
      ∏ x ∈ n.divisorsAntidiagonal, (2 : ℝ) ^ (μ x.1 * (x.2 : ℤ)) := by
    rw [← two_zpow_sum _ (fun x => μ x.1 * (x.2 : ℤ)), sum_moebius_mul_eq_totient hn0,
      zpow_natCast]
  have h2 : ∏ d ∈ n.divisors, (2 : ℝ) ^ d = ∏ x ∈ n.divisorsAntidiagonal, (2 : ℝ) ^ x.2 :=
    (Nat.prod_divisorsAntidiagonal' (f := fun _ b => (2 : ℝ) ^ b)).symm
  have hM : ∏ d ∈ n.divisors, (M d : ℝ) = ∏ x ∈ n.divisorsAntidiagonal, (M x.2 : ℝ) :=
    (Nat.prod_divisorsAntidiagonal' (f := fun _ b => (M b : ℝ))).symm
  rw [hφ, h2, hM, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro x _; positivity
  · intro x hx
    have hb : Odd x.2 := hn.of_dvd_nat (Dvd.intro_left _ (Nat.mem_divisorsAntidiagonal.1 hx).1)
    obtain ⟨hL0, hLM, hprod, h2M⟩ := LM_facts hb
    have hUL : L x.2 ≤ (z ^ x.2 - 1).norm ∧ (z ^ x.2 - 1).norm ≤ M x.2 := by
      rcases hU x.2 hb with h | h <;> rw [h] <;> constructor <;> linarith
    exact factor_bound (Lb := (L x.2 : ℝ)) x.2 (moebius_eq_or x.1) (by exact_mod_cast hL0)
      (by exact_mod_cast hUL.1)
      (by exact_mod_cast hUL.2) (by exact_mod_cast hprod) (by exact_mod_cast h2M)

/-! ### The arithmetic criterion -/

/-- The criterion `n ∏_{d ∣ n} M_d < 2^φ(n) ∏_{d ∣ n} 2^d`, which with `lower_bound` gives
`N(Φ_n(z)) > n`. -/
def Crit (n : ℕ) : Prop := n * ∏ d ∈ n.divisors, Mn d < 2 ^ n.totient * ∏ d ∈ n.divisors, 2 ^ d

instance : DecidablePred Crit := fun n => by unfold Crit; infer_instance

set_option maxRecDepth 100000 in
/-- The odd `n` from 7 to 81, checked by the kernel. -/
theorem crit_small : ∀ n < 82, 7 ≤ n → n % 2 = 1 → Crit n := by decide +kernel

theorem le_Mn (b : ℕ) : 2 ^ b ≤ Mn b := (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

/-- `∏_{j ≤ J} M_{2j+1} ≤ 9 ∏_{j ≤ J} 2^{2j+1}` (the infinite product is about 8.1). -/
theorem prod_Mn_odd_le (J : ℕ) :
    ∏ j ∈ Finset.range (J + 1), Mn (2 * j + 1) ≤
      9 * ∏ j ∈ Finset.range (J + 1), 2 ^ (2 * j + 1) := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · decide
  -- the invariant `16 P 2^J + 130 Q ≤ 130 2^J Q` for `J ≥ 1`
  have inv : ∀ J ≥ 1, 16 * (∏ j ∈ Finset.range (J + 1), Mn (2 * j + 1)) * 2 ^ J +
      130 * ∏ j ∈ Finset.range (J + 1), 2 ^ (2 * j + 1) ≤
      130 * 2 ^ J * ∏ j ∈ Finset.range (J + 1), 2 ^ (2 * j + 1) := by
    intro J hJ
    induction J, hJ using Nat.le_induction with
    | base => decide
    | succ J hJ ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ (fun j => 2 ^ (2 * j + 1))]
      set P := ∏ j ∈ Finset.range (J + 1), Mn (2 * j + 1)
      set Q := ∏ j ∈ Finset.range (J + 1), 2 ^ (2 * j + 1)
      have hMn : Mn (2 * (J + 1) + 1) = 8 * 2 ^ J * 2 ^ J + 4 * 2 ^ J + 1 := by
        unfold Mn; rw [show (2 * (J + 1) + 1 + 1) / 2 = J + 2 by omega]; ring
      have h2 : 2 ^ (2 * (J + 1) + 1) = 8 * 2 ^ J * 2 ^ J := by ring
      rw [hMn, h2, pow_succ]
      set y := 2 ^ J
      nlinarith [Nat.mul_le_mul_right (2 * (8 * y * y + 4 * y + 1)) ih, Nat.zero_le (Q * y),
        Nat.zero_le Q]
  have h := inv J hJ
  set P := ∏ j ∈ Finset.range (J + 1), Mn (2 * j + 1)
  set Q := ∏ j ∈ Finset.range (J + 1), 2 ^ (2 * j + 1)
  have hy : 0 < 2 ^ J := by positivity
  have h1 : 16 * P * 2 ^ J ≤ 130 * Q * 2 ^ J := by nlinarith
  have h3 := Nat.le_of_mul_le_mul_right h1 hy
  omega

/-- For odd `n`: `∏_{d ∣ n} M_d ≤ 9 ∏_{d ∣ n} 2^d`. -/
theorem prod_Mn_divisors_le {n : ℕ} (hn : Odd n) :
    ∏ d ∈ n.divisors, Mn d ≤ 9 * ∏ d ∈ n.divisors, 2 ^ d := by
  obtain ⟨J, rfl⟩ := hn
  set S := (Finset.range (J + 1)).image (fun j => 2 * j + 1) with hSdef
  have hS : ∀ f : ℕ → ℕ, ∏ b ∈ S, f b = ∏ j ∈ Finset.range (J + 1), f (2 * j + 1) := fun f =>
    Finset.prod_image (fun a _ b _ h => by omega)
  have hsub : (2 * J + 1).divisors ⊆ S := by
    intro d hd
    have hdn := Nat.dvd_of_mem_divisors hd
    have hodd : Odd d := (odd_two_mul_add_one J).of_dvd_nat hdn
    have hle := Nat.le_of_dvd (by omega) hdn
    obtain ⟨j, rfl⟩ := hodd
    exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩
  have hall : ∏ b ∈ S, Mn b ≤ 9 * ∏ b ∈ S, 2 ^ b := by
    rw [hS Mn, hS (fun b => 2 ^ b)]; exact prod_Mn_odd_le J
  have hMS := Finset.prod_sdiff hsub (f := Mn)
  have h2S := Finset.prod_sdiff hsub (f := fun b => 2 ^ b)
  have hle : ∏ b ∈ S \ (2 * J + 1).divisors, 2 ^ b ≤ ∏ b ∈ S \ (2 * J + 1).divisors, Mn b :=
    Finset.prod_le_prod fun b _ => le_Mn b
  have hpos : 0 < ∏ b ∈ S \ (2 * J + 1).divisors, 2 ^ b := Finset.prod_pos fun b _ => by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc (∏ b ∈ S \ (2 * J + 1).divisors, 2 ^ b) * ∏ d ∈ (2 * J + 1).divisors, Mn d
      ≤ (∏ b ∈ S \ (2 * J + 1).divisors, Mn b) * ∏ d ∈ (2 * J + 1).divisors, Mn d :=
        Nat.mul_le_mul_right _ hle
    _ = ∏ b ∈ S, Mn b := hMS
    _ ≤ 9 * ∏ b ∈ S, 2 ^ b := hall
    _ = (∏ b ∈ S \ (2 * J + 1).divisors, 2 ^ b) * (9 * ∏ d ∈ (2 * J + 1).divisors, 2 ^ d) := by
        rw [← h2S]; ring

/-- `φ(n)² ≥ n` for odd `n`: `φ(n) ∏ p = n ∏ (p - 1)`, `(p - 1)² ≥ p` for odd `p`, and
`∏ p ≤ n`. -/
theorem le_totient_sq {n : ℕ} (hn : Odd n) : n ≤ n.totient ^ 2 := by
  have hn0 : 0 < n := hn.pos
  have key := Nat.totient_mul_prod_primeFactors n
  set R := ∏ p ∈ n.primeFactors, p
  set T := ∏ p ∈ n.primeFactors, (p - 1)
  have hRT : R ≤ T ^ 2 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_le_prod
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := hn.ne_two_of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have hp3 : 3 ≤ p := by have := hpp.two_le; omega
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
    rw [show q + 3 - 1 = q + 2 by omega]
    nlinarith
  have hR0 : 0 < R := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hRn : R ≤ n := Nat.le_of_dvd hn0 (Nat.prod_primeFactors_dvd n)
  have h1 : n ^ 2 * R ≤ (n.totient * R) ^ 2 := by
    rw [key, mul_pow]; exact Nat.mul_le_mul_left _ hRT
  have h2 : n ^ 2 ≤ n.totient ^ 2 * R := by
    have : n ^ 2 * R ≤ (n.totient ^ 2 * R) * R := by
      calc n ^ 2 * R ≤ (n.totient * R) ^ 2 := h1
        _ = (n.totient ^ 2 * R) * R := by ring
    exact Nat.le_of_mul_le_mul_right this hR0
  have h3 : n * n ≤ n.totient ^ 2 * n := by
    calc n * n = n ^ 2 := by ring
      _ ≤ n.totient ^ 2 * R := h2
      _ ≤ n.totient ^ 2 * n := Nat.mul_le_mul_left _ hRn
  exact Nat.le_of_mul_le_mul_right h3 hn0

theorem nine_sq_lt_two_pow {s : ℕ} (hs : 10 ≤ s) : 9 * s ^ 2 < 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih => rw [pow_succ 2 s]; nlinarith

/-- The criterion for odd `n ≥ 82`, from `∏ M_d ≤ 9 ∏ 2^d`, `φ(n)² ≥ n` and `9 s² < 2^s`. -/
theorem crit_large {n : ℕ} (hn : Odd n) (h82 : 82 ≤ n) : Crit n := by
  have hφ := le_totient_sq hn
  have hφ10 : 10 ≤ n.totient := by
    by_contra h
    push Not at h
    have : n.totient ^ 2 ≤ 9 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have h9 : 9 * n < 2 ^ n.totient :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 9 hφ) (nine_sq_lt_two_pow hφ10)
  have hP := prod_Mn_divisors_le hn
  have hB : 0 < ∏ d ∈ n.divisors, 2 ^ d := Finset.prod_pos fun d _ => by positivity
  unfold Crit
  calc n * ∏ d ∈ n.divisors, Mn d ≤ n * (9 * ∏ d ∈ n.divisors, 2 ^ d) := Nat.mul_le_mul_left n hP
    _ = (9 * n) * ∏ d ∈ n.divisors, 2 ^ d := by ring
    _ < 2 ^ n.totient * ∏ d ∈ n.divisors, 2 ^ d := Nat.mul_lt_mul_of_pos_right h9 hB

theorem crit {n : ℕ} (hn : Odd n) (h7 : 7 ≤ n) : Crit n := by
  rcases Nat.lt_or_ge n 82 with h | h
  · exact crit_small n h h7 (Nat.odd_iff.1 hn)
  · exact crit_large hn h

theorem M_eq_Mn (d : ℕ) : M d = Mn d := by unfold M Mn; push_cast; ring

/-- `N(Φ_n(z)) > n` for odd `n ≥ 7`, under the hypotheses of `lower_bound`. -/
theorem size_bound_of {z : GaussianInt} (hz : z.norm = 2)
    (hU : ∀ b, Odd b → (z ^ b - 1).norm = L b ∨ (z ^ b - 1).norm = M b) {n : ℕ} (hn : Odd n)
    (h7 : 7 ≤ n) : (n : ℤ) < ((cyclotomic n GaussianInt).eval z).norm := by
  have hlow := lower_bound hz hU hn
  have hc : ((n * ∏ d ∈ n.divisors, Mn d : ℕ) : ℝ) <
      ((2 ^ n.totient * ∏ d ∈ n.divisors, 2 ^ d : ℕ) : ℝ) := by exact_mod_cast crit hn h7
  push_cast at hc
  have hMM : ∏ d ∈ n.divisors, (M d : ℝ) = ∏ d ∈ n.divisors, (Mn d : ℝ) :=
    Finset.prod_congr rfl fun d _ => by rw [M_eq_Mn]; push_cast; rfl
  rw [hMM] at hlow
  have hpos : 0 < ∏ d ∈ n.divisors, (Mn d : ℝ) :=
    Finset.prod_pos fun d _ => Nat.cast_pos.2 (by unfold Mn; positivity)
  have : (n : ℝ) < (((cyclotomic n GaussianInt).eval z).norm : ℝ) := by
    by_contra hcon
    push Not at hcon
    have := mul_le_mul_of_nonneg_right hcon hpos.le
    linarith
  exact_mod_cast this

theorem Uplus_LM {b : ℕ} (hb : Odd b) : Uplus b = L b ∨ Uplus b = M b := by
  obtain ⟨k, rfl⟩ := hb
  rcases Uplus_Uminus_odd k with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

theorem Uminus_LM {b : ℕ} (hb : Odd b) : Uminus b = L b ∨ Uminus b = M b := by
  obtain ⟨k, rfl⟩ := hb
  rcases Uplus_Uminus_odd k with ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inr h
  · exact Or.inl h

/-- **Size bound**: `A_n > n` and `A'_n > n` for odd `n ≥ 7`. -/
theorem size_bound {n : ℕ} (hn : Odd n) (h7 : 7 ≤ n) : (n : ℤ) < Aplus n ∧ (n : ℤ) < Aminus n :=
  ⟨size_bound_of norm_tG (fun _ hb => Uplus_LM hb) hn h7,
    size_bound_of norm_neg_tG (fun _ hb => Uminus_LM hb) hn h7⟩

end SizeBound

/-! ## 3. Small cases and assembly -/

theorem orderOf_two_zmod_5 : orderOf (2 : ZMod 5) = 4 * 1 := by
  rw [orderOf_eq_iff (by norm_num)]; exact ⟨by decide, by decide⟩

theorem orderOf_two_zmod_13 : orderOf (2 : ZMod 13) = 4 * 3 := by
  rw [orderOf_eq_iff (by norm_num)]; exact ⟨by decide, by decide⟩

theorem orderOf_two_zmod_41 : orderOf (2 : ZMod 41) = 4 * 5 := by
  rw [orderOf_eq_iff (by norm_num)]; exact ⟨by decide, by decide⟩

/-- A divisor of `Φ_{4n}(2)` of the form `A_n` or `A'_n`, larger than `n`, gives a primitive
prime dividing it. -/
theorem primitive_of_A {n : ℕ} (hn : 0 < n) {A : ℤ} (hA0 : 0 ≤ A) (hAdvd : A ∣ Phi4 n)
    (hAn : (n : ℤ) < A) : ∃ p, IsPrimitiveFor p n ∧ (p : ℤ) ∣ A := by
  obtain ⟨p, hp, hord, hpX⟩ := exists_primitive_of_dvd_Phi4 (X := A.toNat) hn
    (by rwa [Int.toNat_of_nonneg hA0]) (by omega)
  refine ⟨p, ⟨hp, hord⟩, ?_⟩
  have := Int.natCast_dvd_natCast.2 hpX
  rwa [Int.toNat_of_nonneg hA0] at this

/-- For odd `n ≥ 7`, both `L_n` and `M_n` have a primitive prime (from parts 1-3). -/
theorem both_primitive {n : ℕ} (hn : Odd n) (h7 : 7 ≤ n) :
    (∃ p, IsPrimitiveFor p n ∧ (p : ℤ) ∣ L n) ∧ (∃ p, IsPrimitiveFor p n ∧ (p : ℤ) ∣ M n) := by
  have hn0 : 0 < n := by omega
  obtain ⟨hA, hA'⟩ := size_bound hn h7
  have hprod := Aplus_mul_Aminus hn
  obtain ⟨p, hp, hpA⟩ := primitive_of_A hn0 (Aplus_nonneg n) ⟨_, hprod.symm⟩ hA
  obtain ⟨q, hq, hqA⟩ := primitive_of_A hn0 (Aminus_nonneg n)
    ⟨_, by rw [← hprod, mul_comm]⟩ hA'
  have hpU := hpA.trans (Aplus_dvd_Uplus hn0)
  have hqV := hqA.trans (Aminus_dvd_Uminus hn0)
  obtain ⟨k, rfl⟩ := hn
  rcases Uplus_Uminus_odd k with ⟨hU, hV⟩ | ⟨hU, hV⟩
  · exact ⟨⟨p, hp, hU ▸ hpU⟩, ⟨q, hq, hV ▸ hqV⟩⟩
  · exact ⟨⟨q, hq, hV ▸ hqV⟩, ⟨p, hp, hU ▸ hpU⟩⟩

/-- **Lemma 2.** -/
theorem lemma2 : Lemma2 := by
  refine ⟨fun n hn => ?_, fun n hn h7 => (both_primitive hn h7).1⟩
  by_cases h7 : 7 ≤ n
  · exact (both_primitive hn h7).2
  obtain ⟨k, rfl⟩ := hn
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  obtain ⟨hM1, hM3, hM5⟩ := M_small
  rcases hk with rfl | rfl | rfl
  · exact ⟨5, ⟨by norm_num, orderOf_two_zmod_5⟩, by norm_num [hM1]⟩
  · exact ⟨13, ⟨by norm_num, orderOf_two_zmod_13⟩, by norm_num [hM3]⟩
  · exact ⟨41, ⟨by norm_num, orderOf_two_zmod_41⟩, by norm_num [hM5]⟩

/-- **Theorem A**, unconditionally. -/
theorem theoremA : TheoremA := theoremA_of_lemma2 lemma2

end PiFormula
