module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Nat.PrimeFin

/-!
# Erdős's conjecture on `∑ f(n)/n` for periodic `f` with values `±1`: statements

**The conjecture** (Erdős; see Livingston 1965). Let `q ≥ 2` and let `f` be periodic modulo `q`
with `f(n) = ±1` when `q ∤ n` and `f(n) = 0` when `q ∣ n`. Then `∑_{n ≥ 1} f(n)/n ≠ 0`.

**The statement aimed at here** (`erdos_of`, from two statements that are stated in this file
and proved elsewhere or not yet). Let `q` be odd and not a perfect square, and let `f` be
periodic modulo `q` with `f(n) = 0` for `q ∣ n` and `f(n)` a rational number with odd numerator
and odd denominator otherwise. Then the partial sums of `∑ f(n)/n` do not tend to `0`.

The series converges only conditionally, so "the sum is 0" is said with partial sums
(`SumIsZero`), not with `HasSum`.

The two statements:

* `OkadaOnlyIf`: the direction "sum `= 0` implies (a) and (b)" of Okada's criterion (T. Okada,
  1982; it rests on Baker's theorem and on `L(1, χ) ≠ 0`). Here, for a function `f` on `ℤ/q`:
  (a) `g(a) = ∑_{m ∈ M(q)} f(a m)/m = 0` for every unit `a`, where `M(q)` is the set of positive
      integers all of whose prime factors divide `q` (`okadaG`, `CondA`);
  (b) `c_p = ∑_{r=1}^{q} f(r) λ(r, p) = 0` for every prime `p ∣ q`, where `λ(r, p) = v_p(r)` if
      `v_p(r) < v_p(q)` and `v_p(q) + 1/(p-1)` otherwise (`okadaC`, `CondB`).
* `TheoremC`: for odd `q`, if `f(0) = 0`, every other value of `f` is a rational number with
  odd numerator and odd denominator, and (a) and (b) hold, then `q` is a perfect square. This
  is pure algebra (2-adic), the new part.

Nothing is proved in this file except the deduction `erdos_of` and its corollaries.
The paper proof is in `research/2026-11-23-erdos-pm1/` (`00_summary.md`, the referee's
`01_referee_report.md` and `02_proof_part_II.md`).
-/

@[expose] public section

namespace PiFormula

namespace Erdos

/-! ## 1. The numbers of Okada's criterion -/

/-- A unit of `ℤ_(2)`: a rational number with odd numerator and odd denominator. -/
def IsOddRat (x : ℚ) : Prop := Odd x.num ∧ Odd x.den

/-- An element of `ℤ_(2)`: a rational number with odd denominator. -/
def IsZ2 (x : ℚ) : Prop := Odd x.den

/-- `m ∈ M(q)`: `m ≥ 1` and every prime factor of `m` divides `q`. -/
def InM (q m : ℕ) : Prop := m ≠ 0 ∧ m.primeFactors ⊆ q.primeFactors

instance (q m : ℕ) : Decidable (InM q m) := inferInstanceAs (Decidable (_ ∧ _))

/-- `g(a) = ∑_{m ∈ M(q)} f(a m)/m`, an absolutely convergent series. -/
noncomputable def okadaG (q : ℕ) (f : ZMod q → ℚ) (a : ZMod q) : ℝ :=
  ∑' m : ℕ, if InM q m then (f (a * (m : ZMod q)) : ℝ) / (m : ℝ) else 0

/-- `λ(r, p)` for `1 ≤ r ≤ q`: `v_p(r)` if `v_p(r) < v_p(q)`, and `v_p(q) + 1/(p-1)` otherwise. -/
def lam (q r p : ℕ) : ℚ :=
  if padicValNat p r < padicValNat p q then (padicValNat p r : ℚ)
  else (padicValNat p q : ℚ) + 1 / ((p : ℚ) - 1)

/-- `c_p = ∑_{r=1}^{q} f(r) λ(r, p)`. -/
def okadaC (q : ℕ) (f : ZMod q → ℚ) (p : ℕ) : ℚ :=
  ∑ r ∈ Finset.Icc 1 q, f (r : ZMod q) * lam q r p

/-- Condition (a): `g(a) = 0` for every unit `a` modulo `q`. -/
def CondA (q : ℕ) (f : ZMod q → ℚ) : Prop := ∀ a : ZMod q, IsUnit a → okadaG q f a = 0

/-- Condition (b): `c_p = 0` for every prime `p` dividing `q`. -/
def CondB (q : ℕ) (f : ZMod q → ℚ) : Prop := ∀ p : ℕ, p.Prime → p ∣ q → okadaC q f p = 0

/-- `ℓ_p`: the sum of `f(r)` over the `r ≠ 0` in `ℤ/q` with `p^(v_p(q)) ∣ r`. -/
def ell (q : ℕ) (f : ZMod q → ℚ) (p : ℕ) : ℚ :=
  ∑ r ∈ (Finset.Icc 1 (q - 1)).filter (fun r => p ^ padicValNat p q ∣ r), f (r : ZMod q)

/-! ## 2. The series -/

/-- The partial sums `∑_{1 ≤ n < N} f(n)/n` (the term `n = 0` is `0`). -/
noncomputable def partialSum (q : ℕ) (f : ZMod q → ℚ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (f (n : ZMod q) : ℝ) / (n : ℝ)

/-- The series `∑_{n ≥ 1} f(n)/n` converges and its sum is `0`. -/
def SumIsZero (q : ℕ) (f : ZMod q → ℚ) : Prop :=
  Filter.Tendsto (partialSum q f) Filter.atTop (nhds 0)

/-! ## 3. The statements -/

/-- **Okada's criterion, the direction used**: for odd `q` and rational `f` with `f(0) = 0`, if
`∑ f(n)/n = 0` then (a) and (b) hold. -/
def OkadaOnlyIf : Prop :=
  ∀ q : ℕ, Odd q → ∀ f : ZMod q → ℚ, f 0 = 0 → SumIsZero q f → CondA q f ∧ CondB q f

/-- **Theorem A**: (a) with odd values gives `ℓ_p ≡ (p-1) v_p(q)` modulo `2^(v_2(p-1)+1)`. -/
def TheoremA : Prop :=
  ∀ q : ℕ, Odd q → ∀ f : ZMod q → ℚ, f 0 = 0 → (∀ r : ZMod q, r ≠ 0 → IsOddRat (f r)) →
    CondA q f → ∀ p : ℕ, p.Prime → p ∣ q → ∃ z : ℚ, IsZ2 z ∧
      ell q f p = ((p : ℚ) - 1) * padicValNat p q + 2 ^ (padicValNat 2 (p - 1) + 1) * z

/-- **Theorem B**: `c_p = 0` with odd values gives `ℓ_p ≡ 0` modulo `2^(v_2(p-1)+1)`. -/
def TheoremB : Prop :=
  ∀ q : ℕ, Odd q → ∀ f : ZMod q → ℚ, f 0 = 0 → (∀ r : ZMod q, r ≠ 0 → IsOddRat (f r)) →
    ∀ p : ℕ, p.Prime → p ∣ q → okadaC q f p = 0 → ∃ z : ℚ, IsZ2 z ∧
      ell q f p = 2 ^ (padicValNat 2 (p - 1) + 1) * z

/-- **Theorem C**: (a) and (b) with odd values force `q` to be a perfect square. -/
def TheoremC : Prop :=
  ∀ q : ℕ, Odd q → ∀ f : ZMod q → ℚ, f 0 = 0 → (∀ r : ZMod q, r ≠ 0 → IsOddRat (f r)) →
    CondA q f → CondB q f → IsSquare q

/-! ## 4. The deduction -/

/-- **Erdős's conjecture for odd `q` that is not a square**, from Theorem C and Okada's
criterion: if `f(0) = 0` and every other value of `f` is a rational number with odd numerator
and odd denominator, then `∑ f(n)/n` is not `0`. -/
theorem erdos_of (hC : TheoremC) (hO : OkadaOnlyIf) {q : ℕ} (hq : Odd q) (hns : ¬ IsSquare q)
    (f : ZMod q → ℚ) (h0 : f 0 = 0) (hodd : ∀ r : ZMod q, r ≠ 0 → IsOddRat (f r)) :
    ¬ SumIsZero q f := fun h =>
  hns (hC q hq f h0 hodd (hO q hq f h0 h).1 (hO q hq f h0 h).2)

theorem isOddRat_one : IsOddRat 1 := ⟨by decide, by decide⟩

theorem isOddRat_neg_one : IsOddRat (-1) := ⟨by decide, by decide⟩

/-- The case of the conjecture: values `±1` off the multiples of `q`. -/
theorem erdos_pm_one_of (hC : TheoremC) (hO : OkadaOnlyIf) {q : ℕ} (hq : Odd q)
    (hns : ¬ IsSquare q) (f : ZMod q → ℚ) (h0 : f 0 = 0)
    (hpm : ∀ r : ZMod q, r ≠ 0 → f r = 1 ∨ f r = -1) : ¬ SumIsZero q f :=
  erdos_of hC hO hq hns f h0 fun r hr => by
    rcases hpm r hr with h | h <;> rw [h]
    · exact isOddRat_one
    · exact isOddRat_neg_one

end Erdos

end PiFormula
