# Clear the compiler warnings of the library

- Date: 2026-11-24
- Written: 2026-11-27, from the commands of that day
- Area: `lean/Baker/`, `lean/Pilean/PiFormula/`, `lean/Pilean/Base3/GoodPrimes.lean`
- Starting point: `main` at `af549c8`
- Outcome: worked
- Supersedes: none

## Goal
`lake build` prints no warning except the intended `sorry` of the challenge file.
`LEAN_NUM_THREADS=4 lake build --no-build <targets>` replays every stored warning without
rebuilding; that is the measure.

## Attempts

### 1. Deprecated names, taken from the warning text
- Tried: `enorm_eq_nnnorm` to `eNorm_eq_nnNorm`, `coe_nnnorm` to `coe_nnNorm` (seven places in
  four Baker files), and `Polynomial.coeff_smul` to `AddMonoidAlgebra.coeff_smul_apply` inside a
  `simp_rw`.
- Expected: the first two are renames. The third is marked "type changed" in Mathlib, so the
  rewrite might not fire on a polynomial coefficient.
- Result: all build. [measured] full build at `69d6152`.
- Verdict: worked
- Why: [code] Mathlib's own proof of the deprecated lemma is `coeff_smul_apply ..`, so the two
  agree up to unfolding.

### 2. `show` that changes the goal, to `change`
- Tried: fifteen lines of `PiFormula/Rank.lean`, replaced by line number.
- Result: builds. [measured] at `69d6152`. The generator `rankgen.py` emitted the same `show`;
  it was corrected one commit later (`013827a`).
- Verdict: worked

### 3. The linter's advice on `<;>`
- Tried: in `neg_three_pow_sq`, `rcases h with h | h <;> rw [h] <;> ring` became
  `... <;> (rw [h]; ring)`, as the linter suggests ("`<;>` can be replaced with `;`").
- Expected: the same proof.
- Result: `lean/Pilean/Base3/GoodPrimes.lean:171:55: No goals to be solved`.
  [measured] `LEAN_NUM_THREADS=4 lake build ...` on `af549c8` with this edit.
- Verdict: failed
- Why: [code] in the first case `rw [h]` already closes the goal by reflexivity, so `ring` has
  nothing to do; with `<;>` it ran on zero goals, with `;` it runs on none and fails.
- Reopen if: never. The proof is now two explicit cases, `rw [h]` and `rw [h, neg_sq]`.

### 4. A hypothesis the statement does not use
- Tried: `inP_prod_of_mem` took `[DecidableEq ι]` only for its proof; removed from the statement,
  `classical` added to the proof.
- Result: builds, and no caller passed the instance by hand. [measured] at `69d6152`.
- Verdict: worked

### 5. Lines over 100 characters
- Tried: a script that rewraps `linear_combination` terms and lemma lists, breaking only after
  `, `, ` + ` or ` - `, so that a continued line ends in a comma or an operator.
- Expected: Lean reads a trailing operator as "continues on the next line".
- Result: 38 lines rewrapped in `Relations.lean` and `VSeries.lean`, three more by hand; builds.
  [measured] at `69d6152`.
- Verdict: worked
- Why not the generators: [inferred] their inputs are no longer in the repository, so the two
  files were edited directly. They no longer come out of their scripts unchanged.

### 6. The header linter
- Tried: reading why 48 files warned about their header ("Copyright too short") and the other
  184 did not.
- Result: Mathlib's header linter checks only files imported directly by the library's root
  file. [code] `Mathlib/Tactic/Linter/Header.lean` in Mathlib v4.36.0 (`isInLibraryRoot`).
- Verdict: worked, in the next commit: the header needs a name, which is the owner's choice.
  Added to all 232 files of the project in `013827a`.

## Result
`69d6152` and `013827a`. [measured] at `013827a`: the replay shows one warning, the challenge
file's `sorry`; `#print axioms` of the headline theorems is unchanged.

## Lessons
- A linter suggestion is not a proof step. Rebuild after each kind of change.
- `tac1 <;> tac2` is not `(tac1; tac2)` when `tac1` can close the goal.
- A file that warns nothing may simply not be linted: the header linter skips files that the
  root file does not import.
- Fix the generator with the generated file.

## Follow-ups
- `python scripts/check_format.py` now checks headers and line length in every file, linted or
  not.
