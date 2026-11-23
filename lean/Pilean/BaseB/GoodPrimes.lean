import Pilean.BaseB.Reduction
import Pilean.BaseB.Size

/-!
# Good primes in every base `b ≥ 5`

For every integer `b ≥ 5` and every root of unity `r` other than `1, -1, i, -i`, some prime
ideal of the algebraic integers contains `√b - r` and an odd rational prime `p` that divides
neither `b` nor the order of `r` (`goodPrimesB`).

* For `b ≥ 6`: the size condition (`Size`) and the reduction (`Reduction`). The integer
  `c₀`, the constant term of the minimal polynomial of `√b - r`, divides a power of `Φ_m(b)`
  (`m` the order of `r²`) with a cofactor at most `(√b + 1)^φ`, and every prime factor of `c₀`
  lies under a prime ideal containing `√b - r`.
* For `b = 5` the size condition fails at `m = 6`; there the good primes come from the
  Aurifeuillian factors (`Base5/GoodPrimes`, through `goodPrimesB_five`).
-/

open Complex Polynomial

namespace PiFormula

namespace BaseB

theorem three_le_orderOf_sq {r : ℂ} (hr : IsOfFinOrder r) (h4 : r ^ 4 ≠ 1) :
    3 ≤ orderOf (r ^ 2) := by
  have h0 : 0 < orderOf (r ^ 2) := (hr.pow (n := 2)).orderOf_pos
  have h1 := pow_orderOf_eq_one (r ^ 2)
  by_contra hlt
  apply h4
  have hcases : orderOf (r ^ 2) = 1 ∨ orderOf (r ^ 2) = 2 := by omega
  rcases hcases with h | h
  · rw [h, pow_one] at h1
    calc r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = 1 := by rw [h1, one_pow]
  · rw [h] at h1
    calc r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = 1 := h1

/-- **Good primes in every base `b ≥ 5`.** Every root of unity other than `1, -1, i, -i` has a
good prime. -/
theorem goodPrimesB {b : ℕ} (hb : 5 ≤ b) : GoodPrimesB b := by
  rcases Nat.lt_or_ge b 6 with h | h
  · obtain rfl : b = 5 := by omega
    exact goodPrimesB_five
  · intro r hr h4
    exact hasGoodPrimeB_of_sizeCond (by omega) hr h4 (sizeCond h (three_le_orderOf_sq hr h4))

end BaseB

end PiFormula
