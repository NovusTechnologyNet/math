/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.OkadaGlue
public import Pilean.Erdos.OkadaGlueTwist
public import Pilean.Erdos.OkadaGlueChar
public import Pilean.Erdos.OkadaGlueWindow

/-!
# Okada's criterion, the direction "sum `= 0` implies (a) and (b)", from seven statements

`okadaOnlyIf_of`: `OkadaOnlyIf` (the hypothesis of `erdos_pm_one_of_okada` in `Main.lean`)
follows from the seven propositions

* `OkadaWindow` (window sums of `1/n` in a residue class),
* `OkadaFourierLimit` (the value of `∑ f(n)/n` as a linear form in the `Log(1 - ζ^a)`),
* `OkadaBakerTwist` (Baker's theorem and the Galois group of `ℚ(ζ_q)`),
* `OkadaUnitReduction` (reduction of `∑ f(n)/n` to a sum over the `n` prime to `q`),
* `OkadaLayerSum` (the coefficient of `log p` is `c_p`),
* `OkadaLOne` (`L(1, χ) ≠ 0` for the conditionally convergent series),
* `OkadaLogPrimes` (the logarithms of the primes are independent over `ℚ`),

all stated in `OkadaDefs.lean`. The deductions are in `OkadaGlue.lean`,
`OkadaGlueTwist.lean`, `OkadaGlueChar.lean` and `OkadaGlueWindow.lean`.
-/

@[expose] public section

namespace PiFormula

namespace Erdos

/-- **Okada's criterion, the direction used, from the seven statements.** -/
theorem okadaOnlyIf_of (hW : OkadaWindow) (hF : OkadaFourierLimit) (hB : OkadaBakerTwist)
    (hR : OkadaUnitReduction) (hL : OkadaLayerSum) (hX : OkadaLOne) (hP : OkadaLogPrimes) :
    OkadaOnlyIf :=
  okadaOnlyIf_of_main (okadaTwistInvariance_of (okadaSumZero_of_window hW) hF hB) hR hL
    (okadaUnitNonvanishing_of (okadaHarmonicDiverges_of_window hW) hX) hP

end Erdos

end PiFormula
