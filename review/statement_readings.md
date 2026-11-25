# Statement readings

Each headline statement is read by someone who did not write it and has not seen its proof or
our description of it (`PRACTICES.md`, section 2). This file records the outcome. The reader's
full text and the exact text the reader was given are kept in `review/readings/`.

A reading by an AI agent removes the author's blind spot. It is not the judgment of a
specialist: for the theorems we would claim as new, a person who knows the field should still
read the statement.

## Batch 1: 25 November 2026

- **Reader:** an AI agent (Claude Opus) in a fresh session. It was given one file, the output of
  `scripts/statement_view.py` for the nine theorems, and was allowed to look up Mathlib
  definitions. It was told not to open the repository, the README, the notes or the Lean
  sources, and it did not run Lean.
- **Text read:** `review/readings/2026-11-25-batch1-view.txt` (made from the Lean sources of commit `013827a`).
- **Reader's report:** `review/readings/2026-11-25-batch1-reading.md`.
- **Outcome:** nine statements read, each with confidence "high"; none is vacuous; no convention
  of Lean (division by zero, floor division, where sums start) changes what any of them means.
  The Lean statements needed no change. Three sentences of the README were looser than the
  Lean and were tightened the same day.

| Theorem | What the reader says it states | Compared with our description |
|---|---|---|
| `PiFormula.theoremA` | If a finite rational combination of the angles arctan(1/2^m) and arctan(1/(2^m - 1)), m >= 1, equals q pi with q rational, then only arctan(1/2), arctan 1, arctan(1/3), arctan(1/7) occur, with b1 - a2 + 2 a3 = 0 and q = (a1 + a2 - a3)/4. | Agrees. The converse (every such combination is a relation) is a separate theorem, `combination_is_relation`. |
| `PiFormula.Unconditional.theoremC` | For N > 0 divisible by 120: every N-periodic rational pattern whose series is an algebraic multiple of pi has period 120; those patterns form a space of dimension 13, and the ones with a rational multiple a space of dimension 8. The multiple 0 is allowed in both. | **Wording tightened.** The README said "the formulas for pi form a space of dimension 8"; the space also holds the zero relations. It now says so. |
| `PiFormula.BaseB.no_pi_bailey` | For b >= 2 not a power of 2, B >= 1, N >= 1: if sum_j b^(-Bj) sum_{i=1..N} c_i/(Nj+i) = q pi with rational c_i and q, then q = 0. | Agrees with the "only if" half of Theorem L for positive bases. The "if" half and negative bases are other theorems (`bailey_pi_iff`, `bailey_int_pi_iff`), not read in this batch. |
| `PiFormula.RatBase.hasRelation_iff` | For coprime 0 < q < p: a non-zero periodic rational pattern whose series sum rho(k) (q/p)^floor(k/2)/k is an algebraic multiple of pi, zero allowed, exists if and only if (p, q) is (2,1), (3,1), (4,1), (3,2) or (4,3). | Agrees. The reader's caution, that "has a relation" does not mean "has a formula for pi", is what the README already says: it defines a relation with "0 allowed" and lists separately which bases have formulas. |
| `PiFormula.Compendium.formula_29` | pi^2 = sum_j 16^(-j) [16/(8j+1)^2 - 16/(8j+2)^2 - 8/(8j+3)^2 - 16/(8j+4)^2 - 4/(8j+5)^2 - 4/(8j+6)^2 + 2/(8j+7)^2]. The reader checked the first two blocks numerically: 9.8699 against 9.8696. | Agrees. |
| `PiFormula.Erdos.erdos_pm_one_nat` | For odd q that is not a perfect square: no f with period q, f = 0 on the multiples of q and f = +-1 elsewhere, has partial sums sum_{n<N} f(n)/n tending to 0. This includes the case where the partial sums diverge. | Agrees. |
| `PiFormula.Erdos.erdos_pm_one_lt_11025` | The same for every q with 2 <= q < 11025, squares and even numbers included. The reader notes that q = 1 has to be excluded, as it is. | Agrees. |
| `PiFormula.Erdos.okadaCriterionGeneral` | For q >= 1 and a rational-valued f on the residues mod q: the partial sums of sum f(n)/n tend to 0 if and only if (A) for every unit a, the sum of f(am)/m over the m >= 1 all of whose primes divide q is 0, and (B) for every prime p dividing q, sum_{r=1..q} f(r) lambda_p(r) = 0, with lambda_p(r) = v_p(r) if v_p(r) < v_p(q) and v_p(q) + 1/(p-1) otherwise. The reader checked q = 1 and q = 2 by hand, and that the infinite sum in (A) converges, so Lean's convention for divergent sums plays no part. | **Wording tightened.** The README did not say that the values are rational; it now does. |
| `PiFormula.Erdos.exists_oddValued_sumIsZero_iff` | For odd q > 1: an f with f(0) = 0, every other value a rational with odd numerator and odd denominator, and partial sums tending to 0, exists if and only if q is a perfect square. "Odd-valued" does not mean +-1 and does not mean an odd function. | **Wording tightened.** The README said "odd-valued f"; it now spells out the values and says that this is not a counterexample to the conjecture. |

Conventions the reader checked and found harmless: the terms with index 0 vanish because Lean
sets x/0 = 0, and periodicity still ties rho(0) to rho(N); arctan(1/(2^0 - 1)) = arctan 0 = 0;
in Theorem A the hypothesis b(0) = 0 is essential (arctan 1 = pi/4) and a(0) = 0 only fixes a
coefficient that the sum never sees; condition (B) sums over r = 1, ..., q, so the valuation of
0 never occurs.

## Not read yet

Every other row of the README's table: Theorems B, D, E, G, H, I, J, K, F, the base-3 and base-5
theorems, Theorems G (every base), M, N, the two-way forms of Theorem L, the rest of the Compendium
formulas, and `erdos_pm_one_of_cases`.
