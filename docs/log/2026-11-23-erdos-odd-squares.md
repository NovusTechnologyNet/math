# Extend the Erdos theorem from odd non-squares to odd squares

- Date: 2026-11-23
- Written: 2026-11-27, from the Lean files and commits of that day
- Area: `lean/Pilean/Erdos/` (`Main.lean`, `Squares.lean`, `Summary.lean`)
- Starting point: `main` at `d24d1d3`
- Outcome: failed
- Supersedes: none

## Goal
Erdos's conjecture for every odd q: if f has period q, f = 0 on the multiples of q and f = +-1
elsewhere, then sum f(n)/n is not 0. `erdos_pm_one_nat` has it for odd q that are not perfect
squares. Done would be the same statement without "not a perfect square".

## Attempts

### 1. The same 2-adic argument
- Tried: the argument behind `isSquare_of_condA_condB`. It takes Okada's conditions (a) and (b)
  and uses one property of f: its non-zero values are rationals with odd numerator and odd
  denominator.
- Expected: perhaps a sharper count would also exclude squares.
- Result: it cannot. For every odd square q > 1 there is an f with exactly that property and
  sum 0. [code] `lean/Pilean/Erdos/Squares.lean` at `ec13b60`: `exists_oddValued_sumIsZero_iff`
  (for odd q > 1, such an f exists if and only if q is a perfect square); the library builds at
  `013827a` ([measured] `LEAN_NUM_THREADS=4 lake build ...`, 18,803 jobs).
- Verdict: failed
- Why: [code] the same file gives the function for q = s^2: f(n) = -E(n)/s + [s | n] E(n/s), with
  E(n) = (-1)^(n mod s) off the multiples of s. Its values are +-1/s and +-1, all odd, and its sum
  is 0. So no argument that sees only "the values are odd" can exclude a square.
- Reopen if: the argument uses that the values are exactly +-1 (the function above takes the
  values +-1/s, so it is not a counterexample to the conjecture), or uses the size of the values
  and not only their parity.

### 2. The known size condition
- Tried: the case q <= 2 phi(q) (Okada; Chatterjee-Murty), formalized as `erdos_size_nat`.
- Expected: it covers the small squares.
- Result: it covers every odd square below 11025 = 105^2. [code]
  `lean/Pilean/Erdos/Summary.lean` at `d24d1d3`: `erdos_pm_one_lt_11025`, `not_cases_11025`
  (11025 has q/phi(q) = 35/16 > 2).
- Verdict: partly
- Why: [inferred] q/phi(q) depends only on the primes of q, and 3/2 * 5/4 * 7/6 = 35/16; the
  smallest odd square with the primes 3, 5 and 7 is 105^2.
- Reopen if: a stronger size condition is proved or found in print.

## Result
`ec13b60` (the converse for odd squares), `d24d1d3` (every q < 11025). Open: odd squares with
q > 2 phi(q), the first being 11025.

## Lessons
- Before pushing a method further, look for an object that satisfies everything the method uses.
  Here it exists and is explicit.
- "Odd-valued" means odd numerator and odd denominator. Spell it out: a reader took it for +-1.

## Follow-ups
- Is the existence of such an f for odd squares in print? Not searched (`review/novelty.md`).
- The conjecture for q = 11025.
