# Baker's theorem (other people's code)

The 19 Lean files in this folder are a formal proof of Baker's theorem on linear forms in
logarithms, by **Michail Karatarakis**. They are not our work.

- Source: the branch `baker` of https://github.com/mkaratarakis/mathlib4, folder
  `Mathlib/NumberTheory/Transcendental/Baker/`.
- Commit: `1d51891b5be7ceeca95b4583cad39e0681c5e453` (24 September 2026), fetched on
  22 November 2026. The branch was 76 commits ahead of Mathlib commit `a0e13008` and added
  only these 19 files, their lines in `Mathlib.lean` and entries in `docs/references.bib`.
- License: Apache License 2.0, copyright (c) 2026 Michail Karatarakis; each file keeps its
  header, and the license text is in `LICENSE` here.
- Status upstream when fetched: not merged into Mathlib and, as far as we could find, not
  announced. It was written for Lean 4.35.0-rc2.

## What it proves

`Transcendental.baker` (`Basic.lean`): if the complex numbers `l i` are linearly independent
over `ℚ` and every `exp (l i)` is algebraic, then a relation `β₀ + ∑ β i * l i = 0` with
algebraic `β₀`, `β i` forces `β₀ = 0` and every `β i = 0`. This is Theorem 2.1 of Baker's
*Transcendental Number Theory* (1975). The proof follows Chapter 4 of Waldschmidt's
*Diophantine Approximation on Linear Algebraic Groups* (2000). The file also derives the
Gelfond-Schneider theorem and the transcendence of `π`.

## How it was checked here

1. Before compiling, every file was scanned for code that runs at build time (`#eval`,
   `run_cmd`, `initialize`, `IO`, `elab`, `macro`, `syntax`, `extern`, `unsafe`) and for
   `sorry`, `axiom`, `native_decide`, `opaque` and `set_option`: there are none. The files
   import only Mathlib modules and each other.
2. All 19 files compile with Lean 4.36.0 and Mathlib v4.36.0 (`lake build Baker`).
3. `#print axioms Transcendental.baker` gives `propext`, `Classical.choice`, `Quot.sound`:
   the three standard axioms and nothing else.

What this does and does not establish: Lean's kernel has checked the proof, so the statement
above is proved. Nobody here has read the proof for understanding, and it has not been
through Mathlib's review.

## Changes made to the files

Module names: the import lines `Mathlib.NumberTheory.Transcendental.Baker.X` became
`Baker.X` (20 lines), because the files live in this project and not inside Mathlib.

Three one-line adjustments for Mathlib v4.36.0, which is about two months newer than the
version the proof was written for:

| File | Change | Reason |
|---|---|---|
| `ExpIndep.lean` | added `public import Mathlib.Algebra.Polynomial.Degree.Lemmas` | `natDegree_C_mul_le` is no longer imported indirectly |
| `TaylorCoeff.lean` | added `public import Mathlib.Analysis.Analytic.Constructions` | `AnalyticAt.add`, `AnalyticAt.sub` and two more lemmas are no longer imported indirectly |
| `SchwarzProduct.lean`, line 544 | `coeff_smul` became `Polynomial.coeff_smul` | that lemma is now `protected` |

Nothing else was changed.

## How it is used

`Pilean/PiFormula/Unconditional.lean` turns `Transcendental.baker` into `BakerTheorem`, the
hypothesis of Part III, and restates the main theorems without it.
