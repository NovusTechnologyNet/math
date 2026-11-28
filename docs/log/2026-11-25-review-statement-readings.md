# Have every headline statement read by a reader who did not write it

- Date: 2026-11-25
- Written: 2026-11-27, from the commands and reports of that day
- Area: `scripts/statement_view.py`, `review/statement_readings.md`, `README.md`
- Starting point: `main` at `095c5ca`
- Outcome: worked
- Supersedes: none

## Goal
For each row of the README's table, a reader who has seen neither the proof nor our prose says in
plain words what the Lean statement states; we compare, and fix whichever side is wrong. Done when
every row has a reading on record. The readers were AI agents (Claude Opus), one fresh session
per batch.

## Attempts

### 1. What to give the reader: the source files
- Tried: considered, not done.
- Why not: [inferred] the sources carry our docstrings and comments, which say what we think the
  statement means. A reader who sees them is no longer independent.
- Verdict: abandoned
- Reopen if: never for this purpose.

### 2. A statement view printed from the compiled library
- Tried: a Lean program, written out and run by `scripts/statement_view.py`, that prints each
  theorem's type and, in order of first use, every definition of the project that the types
  reach, with `pp.funBinderTypes` and `pp.coercions.types` on.
- Expected: exact text with no prose of ours.
- Result: nine theorems and 22 definitions in 242 lines; the first reader read all nine with
  confidence "high". [measured] `python scripts/statement_view.py ...` at `095c5ca`; landed as
  `856da32`.
- Verdict: partly, see attempt 3.

### 3. The same view for the remaining 47 statements
- Tried: three batches, three readers in parallel.
- Result: for three statements the readers could not decide a type. `5 ^ (1 / 4)` in
  `formula_88` and `formula_132`: a real power, or the natural-number power `5 ^ 0`?
  `orderOf 2` in `isFValue_log_prime_classification`: modulo l, or in the naturals, where the
  order is 0? [code] `review/readings/2026-11-25-batch2-reading.md` and `...-batch4-reading.md`
  at `3a5271c`.
- Verdict: VOID for those three statements; worked for the other 44.
- Why: [measured] the view printed numerals without their types. With `pp.numericTypes` the
  output reads `(5 : ℝ) ^ (1 / 4 : ℝ)` and `orderOf (2 : ZMod ℓ)`:
  `review/readings/2026-11-25-typed-check-view.txt` at `3a5271c`. The sources were right.
- Reopen if: n/a. The tool now prints every numeral with its type.

### 4. Compare the readings with the README
- Tried: row by row.
- Result: no Lean statement had to change. Five passages of the README did: three were looser
  than the Lean (Theorem C's space contains the zero relations; Okada's criterion is for rational
  values; "odd-valued" is not +-1), one overstated (the defining series of Catalan's constant
  was counted as a proved formula of degree 2), one was stale (the relation in base 4 was still
  called "computed"). [code] the diffs of `856da32` and `3a5271c`.
- Verdict: worked

## Result
`856da32`, `3a5271c`. 56 statements read. Not covered: 95 of the 104 Compendium theorems, the
companion theorems listed in `review/statement_readings.md`, and any reading by a specialist.

## Lessons
- Give the reader compiled statements, not sources, and print the type of every numeral.
- Ask the reader of a concrete series to compute its first terms. That catches a wrong factor,
  sign or index, and it showed that one "formula" was a definition.
- The README drifts: a row can stay "computed" after its theorem is proved. Check the row when
  the result behind it changes.
- Three readers in parallel work; about 80,000 to 115,000 tokens each for 9 to 17 statements.

## Follow-ups
- Read the remaining Compendium theorems, in batches by file.
- A person who knows the field should read the statements we would claim as new.
