import Pilean.Erdos.AbstractA
import Pilean.Erdos.ArithA
import Pilean.Erdos.ArithEll
import Pilean.Erdos.ArithLemma1
import Pilean.Erdos.TheoremB
import Pilean.Erdos.TheoremC

/-!
# Erdős's conjecture on `∑ f(n)/n`: the algebraic part, complete

**Theorem C** (`theoremC`, `isSquare_of_condA_condB`). Let `q` be odd and `f : ℤ/q → ℚ` with
`f(0) = 0` and every other value a rational number with odd numerator and odd denominator.
If conditions (a) and (b) of Okada's criterion hold (`CondA`, `CondB` in `Defs.lean`), then `q`
is a perfect square.

This is proved here with no hypothesis and the three standard axioms. The pieces:

* `abstractTheoremA` (`AbstractA.lean`): the group-ring core (Lemmas D and KL of the paper
  proof);
* `Arith.mainEq`, `Arith.lemma1`, `Arith.ellProp` (`ArithWeight.lean`, `ArithLemma1.lean`,
  `ArithEll.lean`): the arithmetic that feeds the core (Lemma 2, Lemma 1, and the
  identification of `ℓ_p`);
* `theoremA`: (a) with odd values gives `ℓ_p ≡ (p-1) v_p(q)` modulo `2^(v_2(p-1)+1)`;
* `theoremB` (`TheoremB.lean`): `c_p = 0` with odd values gives `ℓ_p ≡ 0`;
* `theoremC_of` (`TheoremC.lean`): the two congruences force every `v_p(q)` to be even.

**What is still a hypothesis.** The statement about the series itself (`erdos_of_okada`,
`erdos_pm_one_of_okada`: for odd `q` that is not a square the partial sums of `∑ f(n)/n` do not
tend to `0`) is deduced from `OkadaOnlyIf`, the direction "sum `= 0` implies (a) and (b)" of
Okada's criterion (T. Okada, 1982). That criterion is a published theorem resting on Baker's
theorem and on `L(1, χ) ≠ 0`; it is NOT formalized here, so these two theorems carry it as an
explicit hypothesis.

Paper proof and referee report: `research/2026-11-23-erdos-pm1/`.
-/

namespace PiFormula

namespace Erdos

/-- Theorem A from the algebraic core. -/
theorem theoremA_of_abstract : AbstractTheoremA → TheoremA :=
  theoremA_of_lemma1_ell Arith.lemma1 Arith.ellProp

/-- **Theorem A.** -/
theorem theoremA : TheoremA := theoremA_of_abstract abstractTheoremA

/-- **Theorem C.** -/
theorem theoremC : TheoremC := theoremC_of theoremA theoremB

/-- **Theorem C, spelled out**: for odd `q`, if `f(0) = 0`, every other value of `f` is a
rational number with odd numerator and odd denominator, and conditions (a) and (b) hold, then
`q` is a perfect square. -/
theorem isSquare_of_condA_condB {q : ℕ} (hq : Odd q) (f : ZMod q → ℚ) (h0 : f 0 = 0)
    (hodd : ∀ r : ZMod q, r ≠ 0 → IsOddRat (f r)) (ha : CondA q f) (hb : CondB q f) :
    IsSquare q :=
  theoremC q hq f h0 hodd ha hb

/-- **The series, given Okada's criterion**: for odd `q` that is not a perfect square, if
`f(0) = 0` and every other value of `f` is a rational number with odd numerator and odd
denominator, then `∑ f(n)/n` is not `0`. -/
theorem erdos_of_okada (hO : OkadaOnlyIf) {q : ℕ} (hq : Odd q) (hns : ¬ IsSquare q)
    (f : ZMod q → ℚ) (h0 : f 0 = 0) (hodd : ∀ r : ZMod q, r ≠ 0 → IsOddRat (f r)) :
    ¬ SumIsZero q f :=
  erdos_of theoremC hO hq hns f h0 hodd

/-- **Erdős's conjecture for odd `q` that is not a perfect square, given Okada's criterion**:
values `±1` off the multiples of `q`. -/
theorem erdos_pm_one_of_okada (hO : OkadaOnlyIf) {q : ℕ} (hq : Odd q) (hns : ¬ IsSquare q)
    (f : ZMod q → ℚ) (h0 : f 0 = 0) (hpm : ∀ r : ZMod q, r ≠ 0 → f r = 1 ∨ f r = -1) :
    ¬ SumIsZero q f :=
  erdos_pm_one_of theoremC hO hq hns f h0 hpm

end Erdos

end PiFormula
