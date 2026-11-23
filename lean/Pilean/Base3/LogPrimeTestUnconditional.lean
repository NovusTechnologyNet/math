import Pilean.Base3.LogPrimeTest
import Pilean.PiFormula.Unconditional

/-!
# Base 3: the test for a prime, without a hypothesis

`Base3/LogPrimeTest.lean` proves the finite test for a prime from `BakerTheorem : Prop`. Here
the hypothesis is discharged by the formal proof of Baker's theorem
(`PiFormula.bakerTheorem`, see `PiFormula/Unconditional.lean`). The theorems below depend only
on Lean's three standard axioms.
-/

open Polynomial

namespace PiFormula

namespace Base3

namespace Unconditional

/-- **Two primes in one primitive part exclude each other.** Let `p ≠ 3` and `q ≠ p` be primes
at which 3 has the same order `n`; if `n = 6 (2j+1)`, let `p` and `q` divide the same one of
`L_j = 3^(2j+1) - 3^(j+1) + 1`, `M_j = 3^(2j+1) + 3^(j+1) + 1`. Then `log p` is not a value of
the class F3. -/
theorem not_isF3Value_log_of_same_part {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (hp3 : p ≠ 3) (hord : orderOf (3 : ZMod q) = orderOf (3 : ZMod p))
    (hhalf : ∀ j : ℕ, orderOf (3 : ZMod p) = 6 * (2 * j + 1) →
      ((p : ℤ) ∣ L3 j ∧ (q : ℤ) ∣ L3 j) ∨ ((p : ℤ) ∣ M3 j ∧ (q : ℤ) ∣ M3 j)) :
    ¬ IsF3Value (Real.log p) :=
  Base3.not_isF3Value_log_of_same_part bakerTheorem hp hq hqp hp3 hord hhalf

/-- **A partner excludes `p`.** Let `p ≠ 3` be a prime and `n` the order of 3 modulo `p`. If a
prime `q ≠ p` that does not divide `n` divides the primitive part that contains `p`, then
`log p` is not a value of the class F3. -/
theorem not_isF3Value_log_of_partner {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) (hqg : (q : ℤ) ∣ primPart3 p)
    (hqn : ¬ q ∣ orderOf (3 : ZMod p)) : ¬ IsF3Value (Real.log p) :=
  Base3.not_isF3Value_log_of_partner bakerTheorem hp hp3 hq hqp hqg hqn

/-- **The finite test for a prime in base 3.** Let `p ≠ 3` be a prime and `n` the order of 3
modulo `p`. Then `log p` is the value of a series `∑ ρ(k) 3^(-⌊k/2⌋)/k` with `ρ` rational and
periodic if and only if every prime `q ≠ p` dividing the primitive part that contains `p`
divides `n` and has `log q` a value of such a series. -/
theorem isF3Value_log_prime_iff {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    IsF3Value (Real.log p) ↔ ∀ q : ℕ, q.Prime → (q : ℤ) ∣ primPart3 p → q ≠ p →
      q ∣ orderOf (3 : ZMod p) ∧ IsF3Value (Real.log q) :=
  Base3.isF3Value_log_prime_iff bakerTheorem hp hp3

/-- **The test in the form of the note.** For a prime `p ≠ 3`, with `n` the order of 3 modulo
`p`: `log p` is a value of the class F3 if and only if the primitive part that contains `p` is
a power of `p`, or a power of `p` times one prime `q` that divides `n` and has `log q` a value
of the class F3. -/
theorem isF3Value_log_prime_iff_explicit {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    IsF3Value (Real.log p) ↔ (∃ x : ℕ, primPart3 p = (p : ℤ) ^ x) ∨
      ∃ x q : ℕ, q.Prime ∧ q ∣ orderOf (3 : ZMod p) ∧ primPart3 p = (p : ℤ) ^ x * q ∧
        IsF3Value (Real.log q) :=
  Base3.isF3Value_log_prime_iff_explicit bakerTheorem hp hp3

/-- **The classification of the primes in base 3.** For a prime `p`, `log p` is a value of the
class F3 if and only if `p = 3` or `p` passes the test. -/
theorem isF3Value_log_prime_classification {p : ℕ} (hp : p.Prime) :
    IsF3Value (Real.log p) ↔ p = 3 ∨
      ∀ q : ℕ, q.Prime → (q : ℤ) ∣ primPart3 p → q ≠ p →
        q ∣ orderOf (3 : ZMod p) ∧ IsF3Value (Real.log q) :=
  Base3.isF3Value_log_prime_classification bakerTheorem hp

/-- **`log 17` is not the value of any series `∑ ρ(k) 3^(-⌊k/2⌋)/k` with `ρ` rational and
periodic.** -/
theorem not_isF3Value_log_17 : ¬ IsF3Value (Real.log 17) :=
  Base3.not_isF3Value_log_17 bakerTheorem

/-- **`log 23` is not the value of any series `∑ ρ(k) 3^(-⌊k/2⌋)/k` with `ρ` rational and
periodic.** -/
theorem not_isF3Value_log_23 : ¬ IsF3Value (Real.log 23) :=
  Base3.not_isF3Value_log_23 bakerTheorem

end Unconditional

end Base3

end PiFormula
