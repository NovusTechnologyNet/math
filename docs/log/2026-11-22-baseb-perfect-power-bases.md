# State the results for a general base b, perfect powers included

- Date: 2026-11-22
- Written: 2026-11-27, from the note; the checks of that day were not kept as commands
- Area: `notes/pi_formula_theorem.md` (Part IV and the theorems on a general base),
  `lean/Pilean/BaseB/`
- Starting point: not recorded
- Outcome: partly
- Supersedes: none

## Goal
Statements about series of base b that hold for every integer b >= 2, so that Theorems L, M and
N need no case distinction.

## Attempts

### 1. The sub-series lemma for every base
- Tried: the lemma of Part IV as first written, with the base b itself.
- Expected: the argument for b = 2 carries over.
- Result: false when b is a perfect power: it fails for b = 9, n = 4 and for b = 8, n = 3.
  [code] `notes/pi_formula_theorem.md` at `3a5271c` ("Two remarks from the same check").
- Verdict: failed
- Why: [code] the same passage: for b = a^j the right modulus is n1 / gcd(n1, j), not n1.
- Reopen if: n/a. Theorem L avoids it by passing to the root a of the base.

### 2. "The logarithm of a root of the base is never a value"
- Tried: the expected statement for bases that are not powers of 2 or 3.
- Result: false for base 9: log 3 = -2 log(1 - 1/3) + log(1 + 1/3) is a value of the step-2
  class of base 9, because 3 - 1 and 3 + 1 are powers of 2. [code] the same note at `3a5271c`
  ("Base 9 is a true exception").
- Verdict: failed
- Why: [code] as stated there. Theorem M is not affected: it goes through the root of the base.
- Reopen if: n/a.

### 3. The step-2 class of a perfect-power base as "the formulas of that base"
- Tried: reading Theorem G (every base b >= 5) as a statement about all formulas of base 16.
- Result: wrong reading. The class of base b has the weights b^(-floor(k/2)); the formula of
  Bailey, Borwein and Plouffe, of base 16, has the weights of the class of base 2.
  [inferred] from the definitions; an independent reader raised it
  (`review/readings/2026-11-25-batch3-reading.md` at `3a5271c`).
- Verdict: failed, as wording
- Why: [inferred] for b = a^j the class of b is a proper part of the class of a.
- Reopen if: n/a. The README row for Theorem G now says so.

## Result
Theorems L, M and N are stated and proved through the root of the base
(`lean/Pilean/BaseB/NoPi.lean`, `LogBase.lean`, `LogNat.lean`). Theorem G is about the step-2
class only.

## Lessons
- Test any statement "for every base" at 4, 8, 9 and 16 before proving it.
- Say "the class with weights b^(-floor(k/2))", not "formulas of base b".

## Follow-ups
- The criterion for logarithms in a general base (Theorem K for base b) is on paper only.
