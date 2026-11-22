import Pilean.PiFormula.Baker

/-!
# From a standard statement of Baker's theorem to `BakerTheorem`

Every result of Part III takes `BakerTheorem : Prop` as a hypothesis. This file shows that the
hypothesis follows from Baker's theorem in the form in which a library would state it: for a
finite family `l` of logarithms of algebraic numbers that is linearly independent over `ℚ`
(`LinearIndependent ℚ l`), a relation `β₀ + ∑ β i * l i = 0` with algebraic coefficients is
trivial.

So a formal proof of Baker's theorem in that form turns every theorem here that starts with
`(hB : BakerTheorem)` into an unconditional one, with no other change. No such proof is used
or imported here: the statement is a hypothesis of `bakerTheorem_of_linearIndependent`.
-/

open Complex

namespace PiFormula

/-- **The bridge.** Baker's theorem, stated with `LinearIndependent ℚ l` for families indexed
by a finite type, gives `BakerTheorem`. -/
theorem bakerTheorem_of_linearIndependent
    (baker : ∀ {ι : Type} [Fintype ι] {l : ι → ℂ}, (∀ i, IsAlgebraic ℚ (exp (l i))) →
      LinearIndependent ℚ l → ∀ {β₀ : ℂ} {β : ι → ℂ}, IsAlgebraic ℚ β₀ →
      (∀ i, IsAlgebraic ℚ (β i)) → β₀ + ∑ i, β i * l i = 0 → β₀ = 0 ∧ ∀ i, β i = 0) :
    BakerTheorem := by
  intro n lam hlam hind β₀ β hβ₀ hβ hrel
  refine baker hlam ?_ hβ₀ hβ hrel
  rw [Fintype.linearIndependent_iff]
  intro q hq
  refine hind q ?_
  simpa [Rat.smul_def] using hq

end PiFormula
