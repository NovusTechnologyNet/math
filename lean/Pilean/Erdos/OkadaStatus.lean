import Pilean.Erdos.OkadaGlueAll
import Pilean.Erdos.OkadaWindow
import Pilean.Erdos.OkadaLogPrimes
import Pilean.Erdos.OkadaFourier
import Pilean.Erdos.OkadaBaker

/-!
# Okada's criterion, the direction "sum `= 0` implies (a) and (b)": what is proved so far

Of the seven statements of `okadaOnlyIf_of` (`OkadaGlueAll.lean`), four are proved:
`okadaWindow` (`OkadaWindow.lean`), `okadaLogPrimes` (`OkadaLogPrimes.lean`),
`okadaFourierLimit` (`OkadaFourier.lean`) and `okadaBakerTwist` (`OkadaBaker.lean`, with
Baker's theorem). Hence:

* `okadaTwistInvariance`, **the first half, with no hypothesis**: for odd `q` and rational `f`
  with `f(0) = 0`, if the partial sums of `∑ f(n)/n` tend to `0`, then so do the partial sums
  of `∑ f(h n)/n` for every unit `h` modulo `q`.
* `okadaOnlyIf_of_three`: `OkadaOnlyIf` follows from the three statements that are left,
  all in the second half:
  - `OkadaUnitReduction` (reduction of `∑ f(n)/n` to a sum over the `n` prime to `q`),
  - `OkadaLayerSum` (the coefficient of `log p` is `c_p`),
  - `OkadaLOne` (`L(1, χ) ≠ 0` for the conditionally convergent series).

When these are proved, replace this file by `Okada.lean` with
`theorem okadaOnlyIf : OkadaOnlyIf`.
-/

namespace PiFormula

namespace Erdos

/-- If the partial sums of `∑ f(n)/n` tend to `0`, then `∑_r f(r) = 0`. -/
theorem okadaSumZero : OkadaSumZero := okadaSumZero_of_window okadaWindow

/-- The sum of `1/n` over the `n` prime to `q` diverges. -/
theorem okadaHarmonicDiverges : OkadaHarmonicDiverges :=
  okadaHarmonicDiverges_of_window okadaWindow

/-- **The first half.** For odd `q` and rational `f` with `f(0) = 0`: if `∑ f(n)/n = 0`, then
`∑ f(h n)/n = 0` for every unit `h` modulo `q`. (Baker's theorem.) -/
theorem okadaTwistInvariance : OkadaTwistInvariance :=
  okadaTwistInvariance_of okadaSumZero okadaFourierLimit okadaBakerTwist

/-- The part of the second half on the units, from `L(1, χ) ≠ 0`. -/
theorem okadaUnitNonvanishing_of_lOne (hX : OkadaLOne) : OkadaUnitNonvanishing :=
  okadaUnitNonvanishing_of okadaHarmonicDiverges hX

/-- **Okada's criterion, the direction used, from the three statements that are left.** -/
theorem okadaOnlyIf_of_three (hR : OkadaUnitReduction) (hL : OkadaLayerSum)
    (hX : OkadaLOne) : OkadaOnlyIf :=
  okadaOnlyIf_of okadaWindow okadaFourierLimit okadaBakerTwist hR hL hX okadaLogPrimes

end Erdos

end PiFormula
