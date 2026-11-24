module

public import Pilean.BaseB.Defs

/-!
# A general base `b`: symmetrization, and the primes of a constant term

Two tools for the file `Reduction`, with `t = √b` (which may be rational).

* `exists_symmetrize`: for every `G ∈ ℤ[X]` there is `S ∈ ℤ[X]` with
  `S(z) = G(t - z) G(-t - z)` for every complex `z`. It replaces the norm from `ℚ(√b)` to
  `ℚ`: no field norm and no Galois theory is used. (Write `G(t - z) = A(z) + t B(z)` and
  `G(-t - z) = A(z) - t B(z)` with `A, B ∈ ℤ[X]`, by induction on `G`; then
  `S = A² - b B²`.)
* `hasPrime_of_dvd_minpoly_eval_zero`: if the prime `p` divides the constant term of the
  minimal polynomial over `ℤ` of the algebraic integer `x`, then a prime ideal of the
  algebraic integers contains `p` and `x`.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-- For `G ∈ ℤ[X]` there are `A, B ∈ ℤ[X]` with `G(t - z) = A(z) + t B(z)` and
`G(-t - z) = A(z) - t B(z)`, where `t = √b`. -/
theorem exists_split (b : ℕ) (G : ℤ[X]) : ∃ A B : ℤ[X], ∀ z : ℂ,
    aeval (tB b - z) G = aeval z A + tB b * aeval z B ∧
      aeval (-tB b - z) G = aeval z A - tB b * aeval z B := by
  induction G using Polynomial.induction_on with
  | C a => exact ⟨C a, 0, fun z => by simp⟩
  | add p q hp hq =>
    obtain ⟨A₁, B₁, h₁⟩ := hp
    obtain ⟨A₂, B₂, h₂⟩ := hq
    refine ⟨A₁ + A₂, B₁ + B₂, fun z => ?_⟩
    simp only [map_add, (h₁ z).1, (h₁ z).2, (h₂ z).1, (h₂ z).2]
    constructor <;> ring
  | monomial n a h =>
    obtain ⟨A, B, h⟩ := h
    refine ⟨C (b : ℤ) * B - X * A, A - X * B, fun z => ?_⟩
    have e : (C a * X ^ (n + 1) : ℤ[X]) = C a * X ^ n * X := by ring
    rw [e, map_mul (aeval (tB b - z)), map_mul (aeval (-tB b - z)), (h z).1, (h z).2]
    simp only [aeval_X, map_sub, map_mul, map_natCast]
    constructor
    · linear_combination (aeval z B) * tB_sq b
    · linear_combination (aeval z B) * tB_sq b

/-- **Symmetrization.** For `G ∈ ℤ[X]` there is `S ∈ ℤ[X]` with `S(z) = G(t - z) G(-t - z)`
for every complex `z`, where `t = √b`. -/
theorem exists_symmetrize (b : ℕ) (G : ℤ[X]) : ∃ S : ℤ[X], ∀ z : ℂ,
    aeval z S = aeval (tB b - z) G * aeval (-tB b - z) G := by
  obtain ⟨A, B, h⟩ := exists_split b G
  refine ⟨A ^ 2 - C (b : ℤ) * B ^ 2, fun z => ?_⟩
  rw [(h z).1, (h z).2]
  simp only [map_sub, map_mul, map_pow, map_natCast]
  linear_combination (aeval z B) ^ 2 * tB_sq b

/-- **Primes of the constant term.** If the prime `p` divides the constant term of the minimal
polynomial over `ℤ` of the algebraic integer `x`, some prime ideal of the algebraic integers
contains `p` and `x`. -/
theorem hasPrime_of_dvd_minpoly_eval_zero {x : ℂ} (hx : IsIntegral ℤ x) {p : ℕ} (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ (minpoly ℤ x).eval 0) : Base3.HasPrime p x := by
  have key : ∀ U V : ℤ[X], aeval x (U * C (p : ℤ) + V * X) ≠ 1 := by
    intro U V hUV
    have h0 : aeval x (U * C (p : ℤ) + V * X - 1) = 0 := by
      rw [map_sub, hUV, map_one, sub_self]
    obtain ⟨W, hW⟩ := minpoly.isIntegrallyClosed_dvd hx h0
    have he := congrArg (Polynomial.eval 0) hW
    simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, mul_zero, add_zero, eval_one] at he
    obtain ⟨k, hk⟩ := hdvd
    have h1 : (p : ℤ) ∣ 1 := ⟨U.eval 0 - k * W.eval 0, by rw [hk] at he; linear_combination -he⟩
    exact hp.not_dvd_one (Int.natCast_dvd_natCast.1 (by simpa using h1))
  have h := Base3.hasPrime_of_not_unit hx p X key
  rwa [aeval_X] at h

end BaseB

end PiFormula
