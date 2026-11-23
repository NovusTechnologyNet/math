import Pilean.Erdos.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Okada's criterion, the direction "sum `= 0` implies (a) and (b)": statements

The aim is `OkadaOnlyIf` of `Defs.lean` with no hypothesis. This file contains the
definitions and the statements of the steps, as named propositions; nothing is proved here.
The deductions are in `OkadaGlue.lean`, `OkadaGlueTwist.lean`, `OkadaGlueChar.lean` and
`OkadaGlueWindow.lean`. The plan, with the Mathlib declarations each step uses, is
`research/2026-11-23-erdos-pm1/03_okada_lean_plan.md`.

Notation: `q` odd, `f : ℤ/q → ℚ` with `f(0) = 0`, `S_N(f) = ∑_{1 ≤ n < N} f(n)/n`
(`partialSum`), `U = (ℤ/q)ˣ`, `f_h(n) = f(h n)` for `h ∈ U` (`Okada.twistBy`), and for a real
function `u` on `ℤ/q`, `S'_N(u) = ∑_{1 ≤ n < N, gcd(n, q) = 1} u(n)/n` (`Okada.unitSum`).
`g = okadaG q f` is defined on all of `ℤ/q`: `g(r) = ∑_{m ∈ M(q)} f(r m)/m`.

The propositions to prove (the leaves):

* `OkadaWindow`: `∑_{N ≤ n < cN, n ≡ r mod q} 1/n → (log c)/q`.
* `OkadaFourierLimit`: if `∑_r f(r) = 0` then `S_N(f) → -∑_{a ≠ 0} f^(a) Log(1 - ζ^a)`, with
  `ζ = e^(2πi/q)` and `f^` the finite Fourier transform (Abel's limit theorem and
  Dirichlet's test).
* `OkadaBakerTwist`: if `∑_{a ≠ 0} f^(a) Log(1 - ζ^a) = 0` then
  `∑_{a ≠ 0} f^(h a) Log(1 - ζ^a) = 0` for every unit `h` (Baker's theorem and the Galois
  group of `ℚ(ζ)`).
* `OkadaUnitReduction`: `S_N(f) - S'_N(g) → -(1/q) ∑_{p ∣ q} ℓ_p log p`, where `ℓ_p` is the
  sum of `g(r)` over the `r` divisible by `p` and by no other prime factor of `q`
  (`Okada.layerSum`). No infinite sum is exchanged with a limit: `f = ∏_p (1 - T_p/p) g`
  with `(T_p g)(r) = g(p r)` is a finite identity.
* `OkadaLayerSum`: `ℓ_p = c_p` (`okadaC`), a finite identity.
* `OkadaLOne`: for a non-principal Dirichlet character `χ` modulo `q` the partial sums
  `∑_{n < N} χ(n)/n` have a limit, and it is not `0` (this is `L(1, χ) ≠ 0`).
* `OkadaLogPrimes`: the logarithms of the primes are linearly independent over `ℚ`.

The intermediate propositions, deduced in the glue files:

* `OkadaSumZero` (from `OkadaWindow`): if `S_N(f) → 0` then `∑_r f(r) = 0`.
* `OkadaHarmonicDiverges` (from `OkadaWindow`): `S'_N(1) → ∞`.
* `OkadaTwistInvariance` (from `OkadaSumZero`, `OkadaFourierLimit`, `OkadaBakerTwist`):
  `S_N(f) → 0` implies `S_N(f_h) → 0` for every unit `h`.
* `OkadaUnitNonvanishing` (from `OkadaHarmonicDiverges`, `OkadaLOne`): if
  `S'_N(n ↦ u(h n)) → c` for every `h ∈ U`, with the same `c`, then `c = 0` and `u = 0` on
  `U`.

The main deduction (`okadaOnlyIf_of_main`): by `OkadaTwistInvariance` and
`OkadaUnitReduction` applied to `f_h` (whose `g` is `r ↦ g(h r)`, with the same `ℓ_p`),
`S'_N(n ↦ g(h n)) → (1/q) ∑_p ℓ_p log p` for every `h`; by `OkadaUnitNonvanishing` this
number is `0` and `g = 0` on `U`, which is (a); by `OkadaLayerSum` and `OkadaLogPrimes`
every `c_p` is `0`, which is (b).

Every proposition is stated for odd `q` and `f(0) = 0` only, because that is all the glue
needs; none of them needs these two hypotheses to be true (see the plan).
-/

open scoped BigOperators

namespace PiFormula

namespace Erdos

namespace Okada

/-! ## 1. Definitions -/

/-- The function `n ↦ f(h n)`, for a unit `h` modulo `q`. -/
def twistBy (q : ℕ) (f : ZMod q → ℚ) (h : (ZMod q)ˣ) : ZMod q → ℚ :=
  fun n => f ((h : ZMod q) * n)

/-- The partial sums `∑_{1 ≤ n < N, gcd(n, q) = 1} u(n)/n` of a real function `u` on `ℤ/q`. -/
noncomputable def unitSum (q : ℕ) (u : ZMod q → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, if n.Coprime q then u (n : ZMod q) / (n : ℝ) else 0

open Classical in
/-- The residues `r` modulo `q` that are divisible by `p` and by no other prime factor of
`q`. For `p ∣ q` these are the `r` with `gcd(r, q) = p^i`, `1 ≤ i ≤ v_p(q)`; the residue `0`
belongs to it exactly when `q` is a power of `p`. -/
noncomputable def layer (q : ℕ) [NeZero q] (p : ℕ) : Finset (ZMod q) :=
  Finset.univ.filter fun r : ZMod q =>
    (p : ZMod q) ∣ r ∧ ∀ l ∈ q.primeFactors, l ≠ p → ¬ (l : ZMod q) ∣ r

/-- `ℓ_p`: the sum of `g(r) = okadaG q f r` over the `r` divisible by `p` and by no other
prime factor of `q`. It is equal to `c_p` (`OkadaLayerSum`). -/
noncomputable def layerSum (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (p : ℕ) : ℝ :=
  ∑ r ∈ layer q p, okadaG q f r

/-- The finite Fourier transform `f^(a) = (1/q) ∑_r f(r) e^(-2πi a r/q)`, so that
`f(n) = ∑_a f^(a) e^(2πi a n/q)`. -/
noncomputable def fourierCoeff (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (a : ZMod q) : ℂ :=
  (q : ℂ)⁻¹ * ∑ r : ZMod q, (f r : ℂ) * ZMod.stdAddChar (-(a * r))

/-- The linear form `∑_{a ≠ 0} c(a) Log(1 - e^(2πi a/q))` in the logarithms of the algebraic
numbers `1 - ζ^a` (principal branch). -/
noncomputable def logForm (q : ℕ) [NeZero q] (c : ZMod q → ℂ) : ℂ :=
  ∑ a : ZMod q, if a = 0 then 0 else c a * Complex.log (1 - ZMod.stdAddChar a)

end Okada

/-! ## 2. Elementary analysis -/

/-- **The window sums.** For an integer `c ≥ 1` and a residue `r` modulo `q`,
`∑_{N ≤ n < cN, n ≡ r mod q} 1/n → (log c)/q` as `N → ∞`. -/
def OkadaWindow : Prop :=
  ∀ (q : ℕ) [NeZero q], Odd q → ∀ c : ℕ, 0 < c → ∀ r : ZMod q,
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Ico N (c * N), if (n : ZMod q) = r then 1 / (n : ℝ) else 0)
      Filter.atTop (nhds (Real.log (c : ℝ) / (q : ℝ)))

/-- If the partial sums of `∑ f(n)/n` tend to `0`, then `∑_r f(r) = 0`. -/
def OkadaSumZero : Prop :=
  ∀ (q : ℕ) [NeZero q], Odd q → ∀ f : ZMod q → ℚ, f 0 = 0 → SumIsZero q f →
    ∑ r : ZMod q, f r = 0

/-- The sum of `1/n` over the `n` prime to `q` diverges. -/
def OkadaHarmonicDiverges : Prop :=
  ∀ (q : ℕ) [NeZero q], Odd q →
    Filter.Tendsto (Okada.unitSum q fun _ => 1) Filter.atTop Filter.atTop

/-! ## 3. The first half: the sum stays `0` when `f` is twisted by a unit -/

/-- **The value of the series.** If `∑_r f(r) = 0`, the partial sums of `∑ f(n)/n` tend to
`-∑_{a ≠ 0} f^(a) Log(1 - ζ^a)`. -/
def OkadaFourierLimit : Prop :=
  ∀ (q : ℕ) [NeZero q], Odd q → ∀ f : ZMod q → ℚ, f 0 = 0 → ∑ r : ZMod q, f r = 0 →
    Filter.Tendsto (fun N : ℕ => ((partialSum q f N : ℝ) : ℂ)) Filter.atTop
      (nhds (-Okada.logForm q (Okada.fourierCoeff q f)))

/-- **Baker's theorem and the Galois group of `ℚ(ζ_q)`.** If
`∑_{a ≠ 0} f^(a) Log(1 - ζ^a) = 0` then `∑_{a ≠ 0} f^(h a) Log(1 - ζ^a) = 0` for every unit
`h`: the coefficients `f^(a)` lie in `ℚ(ζ_q)`, and the automorphism `ζ ↦ ζ^h` sends `f^(a)` to
`f^(h a)`. -/
def OkadaBakerTwist : Prop :=
  ∀ (q : ℕ) [NeZero q], Odd q → ∀ f : ZMod q → ℚ, f 0 = 0 → ∑ r : ZMod q, f r = 0 →
    Okada.logForm q (Okada.fourierCoeff q f) = 0 →
    ∀ h : (ZMod q)ˣ, Okada.logForm q (fun a => Okada.fourierCoeff q f ((h : ZMod q) * a)) = 0

/-- If `∑ f(n)/n = 0` then `∑ f(h n)/n = 0` for every unit `h`. -/
def OkadaTwistInvariance : Prop :=
  ∀ (q : ℕ) [NeZero q], Odd q → ∀ f : ZMod q → ℚ, f 0 = 0 → SumIsZero q f →
    ∀ h : (ZMod q)ˣ, SumIsZero q (Okada.twistBy q f h)

/-! ## 4. The second half: reduction to the units -/

/-- **Reduction to the units.** `S_N(f) - S'_N(g) → -(1/q) ∑_{p ∣ q} ℓ_p log p`, with
`g = okadaG q f` and `ℓ_p = Okada.layerSum q f p`. No condition on `∑_r f(r)`: the two
divergent parts cancel. -/
def OkadaUnitReduction : Prop :=
  ∀ (q : ℕ) [NeZero q], Odd q → ∀ f : ZMod q → ℚ, f 0 = 0 →
    Filter.Tendsto (fun N : ℕ => partialSum q f N - Okada.unitSum q (okadaG q f) N)
      Filter.atTop
      (nhds (-((∑ p ∈ q.primeFactors, Okada.layerSum q f p * Real.log (p : ℝ)) / (q : ℝ))))

/-- **The coefficient of `log p`.** `ℓ_p = c_p` for every prime `p ∣ q`. -/
def OkadaLayerSum : Prop :=
  ∀ (q : ℕ) [NeZero q], Odd q → ∀ f : ZMod q → ℚ, f 0 = 0 → ∀ p : ℕ, p.Prime → p ∣ q →
    Okada.layerSum q f p = (okadaC q f p : ℝ)

/-- **`L(1, χ) ≠ 0`.** For a non-principal Dirichlet character `χ` modulo `q`, the partial
sums `∑_{n < N} χ(n)/n` have a limit, and the limit is not `0`. -/
def OkadaLOne : Prop :=
  ∀ (q : ℕ) [NeZero q], Odd q → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
    ∃ L : ℂ, L ≠ 0 ∧ Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, χ (n : ZMod q) / (n : ℂ)) Filter.atTop (nhds L)

/-- Let `u` be a real function on `ℤ/q`. If the partial sums of `∑_{gcd(n, q) = 1} u(h n)/n`
tend to the same number `c` for every unit `h`, then `c = 0` and `u` vanishes on the units. -/
def OkadaUnitNonvanishing : Prop :=
  ∀ (q : ℕ) [NeZero q], Odd q → ∀ (u : ZMod q → ℝ) (c : ℝ),
    (∀ h : (ZMod q)ˣ, Filter.Tendsto (Okada.unitSum q fun n => u ((h : ZMod q) * n))
      Filter.atTop (nhds c)) →
    c = 0 ∧ ∀ a : (ZMod q)ˣ, u (a : ZMod q) = 0

/-- The logarithms of the primes are linearly independent over `ℚ`. -/
def OkadaLogPrimes : Prop :=
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∀ c : ℕ → ℚ,
    ∑ p ∈ S, (c p : ℝ) * Real.log (p : ℝ) = 0 → ∀ p ∈ S, c p = 0

end Erdos

end PiFormula
