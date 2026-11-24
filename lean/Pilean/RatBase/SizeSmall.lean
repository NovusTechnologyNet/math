/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.RatBase.SizeSmallTable

/-!
# The size condition for the rational bases `p/q` with `2 ≤ q < p ≤ 15`

`sizeSmall : SizeSmall` (statement in `SmallDefs.lean`): for coprime `2 ≤ q < p ≤ 15` other
than `3/2` and `4/3`, the size condition `SizeCondR p q m` holds at every `m ≥ 3`, except at the
twelve triples of `leftoverTriples`. With the notation `Φ = Φ_m(p, q)`, `φ = φ(m)`:

  `(√p + √q)^φ < Φ`, and `ℓ (√p + √q)^φ < Φ` for every prime `ℓ` dividing both `m` and `Φ`.

The proof, for one pair `(p, q)` (55 pairs):

1. **Lemma (M)** (`pow_totient_le_sq_cycValR`, file `SizeSmallAux.lean`):
   `Φ² ≥ (p² - p q + q²)^φ`. With `a/b ≥ √(p q)` and `s = b (p + q) + 2 a`,
   `(√p + √q)² ≤ s/b`. A prime `ℓ ∣ m` is at most `φ + 1`. So the size condition holds as soon as
   `(φ + 1)² s^φ < ((p² - p q + q²) b)^φ`, and this holds for every `φ > F`, for an explicit `F`
   (`sizeCondR_of_lt_totient`). Here `F ≤ 50`; the largest are `F = 50` for `5/4`, `39` for
   `5/3`, `16` for `6/5`, `15` for `5/2`.
2. **Bound for `m`** (`mul_prod_pred_le_of_totient_le`): `φ(m) ≤ F` forces `m ≤ M`, with
   `M = ⌊F ∏ ℓ/(ℓ - 1)⌋`, the product over the primes `ℓ < F + 2`; `M ≤ 360`.
3. **The rows `3 ≤ m ≤ M`** (`SizeSmallAuxCert.lean`, table in `SizeSmallTable.lean`): each `m`
   comes with its factored form, from which `φ(m)` and `Φ_m(p, q)` are computed. Either
   `φ(m) > F`, or the two inequalities are checked on the integers (with `s/b` in place of
   `(√p + √q)²`, `b = 1000`), or `(p, q, m)` is one of the twelve triples. The check is a kernel
   computation (`smallCerts_ok`).

The table is written by `python/ratbase_size_tables.py`.
-/

@[expose] public section

namespace PiFormula

namespace RatBase

/-- **The size condition for the small rational bases**, outside the twelve triples. -/
theorem sizeSmall : SizeSmall := by
  intro p q m hp hq hqp hcop h32 h43 hm hmem
  obtain ⟨c, hc, rfl, rfl⟩ :=
    exists_smallCert p (by omega) q hqp ⟨hq, hcop, h32, h43⟩
  exact sizeCondR_of_certOK (smallCerts_ok c hc) hm hmem

end RatBase

end PiFormula
