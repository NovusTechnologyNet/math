import Pilean.RatBase.GoodPrimesR

/-!
# Rational bases `p/q` with `p ≤ 15`: shared statements

`GoodPrimesR p q` is proved for `p ≥ 16` (`GoodPrimesR.lean`) from the size condition. For
`p ≤ 15` the size condition `SizeCondR p q m` still holds for all `m ≥ 3`, except in the bases
`2, 3, 4, 3/2, 4/3` (which have relations) and at finitely many other triples `(p, q, m)`.
For `q = 1` and `p ≥ 5` the good primes are those of `Pilean/BaseB`. For `q ≥ 2`, outside the
bases `3/2` and `4/3`, the triples where the size condition fails are the twelve of
`leftoverTriples` (computed twice, by `python/ratbase_explore.py` and independently).

This file fixes the two statements that remain, each proved in its own file:

* `SizeSmall` (file `SizeSmall.lean`): the size condition for `2 ≤ q < p ≤ 15`, outside the
  two bases and the twelve triples;
* `LeftoverGood` (file `Leftover.lean`): at each of the twelve triples, every root of unity
  `r` with `r²` of order `m` has a good prime.

`GoodPrimesSmall.lean` assembles them. Nothing is proved here.
-/

namespace PiFormula

namespace RatBase

/-- The triples `(p, q, m)` with `2 ≤ q < p ≤ 15`, `p, q` coprime, `(p, q) ≠ (3, 2), (4, 3)`,
`m ≥ 3`, at which the size condition `SizeCondR p q m` fails. -/
def leftoverTriples : List (ℕ × ℕ × ℕ) :=
  [(5, 2, 3), (5, 2, 14), (5, 4, 6), (5, 4, 18), (6, 5, 22), (7, 2, 6), (7, 3, 10), (7, 5, 6),
    (8, 7, 6), (8, 7, 10), (11, 7, 6), (11, 10, 6)]

/-- The size condition for the small bases, outside the list. -/
def SizeSmall : Prop :=
  ∀ p q m : ℕ, p ≤ 15 → 2 ≤ q → q < p → Nat.Coprime p q → ¬ (p = 3 ∧ q = 2) →
    ¬ (p = 4 ∧ q = 3) → 3 ≤ m → (p, q, m) ∉ leftoverTriples → SizeCondR p q m

/-- A good prime at each triple of the list, for every root of unity `r` with `r²` of order
`m`. -/
def LeftoverGood : Prop :=
  ∀ p q m : ℕ, (p, q, m) ∈ leftoverTriples → ∀ r : ℂ, IsOfFinOrder r → orderOf (r ^ 2) = m →
    HasGoodPrimeR p q r

/-- The five rational bases that have relations: `2, 3, 4, 3/2, 4/3`. -/
def IsExceptional (p q : ℕ) : Prop :=
  (p = 2 ∧ q = 1) ∨ (p = 3 ∧ q = 1) ∨ (p = 4 ∧ q = 1) ∨ (p = 3 ∧ q = 2) ∨ (p = 4 ∧ q = 3)

end RatBase

end PiFormula
