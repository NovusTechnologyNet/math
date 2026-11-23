import Pilean.Base3.GoodPrimes

/-!
# Base 3: `π` is not a value of the class F3

The theorems of `PiValue.lean` with the good primes supplied by `GoodPrimes.lean`. They
depend on two statements that are not proved in this folder:

* `BakerTheorem`: Baker's theorem on linear forms in logarithms. A formal proof is in
  `Baker/`, and `Base3/Unconditional.lean` uses it.
* `PrimitiveHalves3`: for every odd `E ≥ 3`, each of the two Aurifeuillian factors
  `3^E ∓ 3^((E+1)/2) + 1` of `3^(3E) + 1` has a prime factor `p` with `ord_p(3) = 6E`. This is
  a classical kind of statement (Schinzel 1962, on primitive prime factors of Aurifeuillian
  parts). It is **not proved here**; `python/base3_halves_check.py` checks it for small `E`.

Results (`t = √-3`, F3 the class of series `∑ ρ(k) 3^(-⌊k/2⌋)/k` with `ρ` rational and
periodic):

* `isF3Value_mul_pi_iff`: for an algebraic real number `γ`, `γ π` is a value of F3 if and
  only if `γ` is a rational multiple of `√3`.
* `not_isF3Value_pi`: `π` is not a value of F3.
* `not_isF3Value_rat_mul_pi`: no non-zero rational multiple of `π` is a value of F3.
-/

namespace PiFormula

namespace Base3

/-- Every rational multiple of `π√3` is a value of the class F3 (no hypothesis). -/
theorem isF3Value_rat_mul_pi_sqrt3 (q : ℚ) : IsF3Value ((q : ℝ) * Real.sqrt 3 * Real.pi) := by
  have h := isF3Value_pi_sqrt3.const_mul q
  convert h using 1
  ring

/-- **Which multiples of `π` are values of F3** (from Baker's theorem and
`PrimitiveHalves3`). For an algebraic real `γ`: `γ π` is the value of a series of the class F3
if and only if `γ` is a rational multiple of `√3`. -/
theorem isF3Value_mul_pi_iff (hB : BakerTheorem) (hH : PrimitiveHalves3) {γ : ℝ}
    (hγ : IsAlgebraic ℚ γ) : IsF3Value (γ * Real.pi) ↔ ∃ q : ℚ, γ = q * Real.sqrt 3 := by
  constructor
  · rintro ⟨N, ρ, hN, hρ, h⟩
    exact pi_multiple_of_goodPrimes3 hB (goodPrimes3_of_halves hH) hN hρ hγ h
  · rintro ⟨q, rfl⟩
    exact isF3Value_rat_mul_pi_sqrt3 q

/-- **No non-zero rational multiple of `π` is a value of F3** (from Baker's theorem and
`PrimitiveHalves3`). -/
theorem not_isF3Value_rat_mul_pi (hB : BakerTheorem) (hH : PrimitiveHalves3) {q : ℚ}
    (h : IsF3Value ((q : ℝ) * Real.pi)) : q = 0 :=
  rat_mul_pi_of_goodPrimes3 hB (goodPrimes3_of_halves hH) h

/-- **`π` is not the value of any series of the class F3** (from Baker's theorem and
`PrimitiveHalves3`). -/
theorem not_isF3Value_pi (hB : BakerTheorem) (hH : PrimitiveHalves3) : ¬ IsF3Value Real.pi :=
  not_isF3Value_pi_of_goodPrimes3 hB (goodPrimes3_of_halves hH)

end Base3

end PiFormula
