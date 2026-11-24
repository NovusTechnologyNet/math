module

public import Pilean.RatBase.ReductionR
public import Pilean.RatBase.SizeR
public import Pilean.BaseB.GoodPrimes

/-!
# Good primes in every rational base `p/q` with `p ≥ 16`

For coprime integers `p > q ≥ 1` with `p ≥ 16`, every root of unity `r` with `r⁴ ≠ 1` has a
good prime in the base `p/q`: a prime ideal of the algebraic integers contains `√(pq) - q r`
and an odd rational prime that divides neither `p q` nor the order of `r`. From the size
condition (`SizeR`) and the reduction (`ReductionR`).
-/

@[expose] public section

namespace PiFormula

namespace RatBase

/-- **Good primes in a rational base `p/q` with `p ≥ 16`.** -/
theorem goodPrimesR {p q : ℕ} (hp : 16 ≤ p) (hq : 0 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) : GoodPrimesR p q := fun _ hr h4 =>
  hasGoodPrimeR_of_sizeCondR hq hqp hcop hr h4
    (sizeCondR_of_sixteen_le hp hq hqp (BaseB.three_le_orderOf_sq hr h4))

end RatBase

end PiFormula
