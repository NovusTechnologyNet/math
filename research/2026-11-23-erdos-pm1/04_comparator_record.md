# Verification record: `erdos_pm_one_nat` through `lake comparator` (23 November 2026)

This records what was run, on what, and what it does and does not establish. The four tests
are those of K. Buzzard's post "...and the proof is checked in Lean" (Xena blog, 12 November
2026), the standard the Lean FRO and the Mathlib Initiative applied to the Lean proof of the
Riemann Hypothesis on 21 November 2026.

## The theorem

`PiFormula.Erdos.erdos_pm_one_nat` (`lean/Pilean/Erdos/Final.lean`): if `f : ℕ → ℤ` has odd
period `q` that is not a perfect square, `f(n) = 0` when `q ∣ n` and `f(n) = ±1` otherwise,
then the partial sums of `∑ f(n)/n` do not tend to `0`.

## The four tests

| Test | Status |
|---|---|
| 1. The Lean statement matches the informal one | The statement uses notions of Mathlib only (`Odd`, `IsSquare`, `Finset.sum`, `Filter.Tendsto`); the trusted copy is `lean/Pilean/Challenge/Erdos.lean`, which imports three Mathlib modules and nothing from this project. Read by the project only; no outside reader yet |
| 2. The code compiles | Yes on the development machine (full build, 18,779 jobs). On a clean Linux machine building from the public repository: everything except one file, `Pilean/PiFormula/CheckedPair.lean`, which needs more than 22 GB of memory (killed by the kernel at 22 GB resident) and is in the import cone of the theorem although the proof does not use it. Being fixed |
| 3. The code proves the theorem as stated (`lake comparator`) | **Accepted**, on exports (see below) |
| 4. Independent kernels (`lake comparator --paranoid`) | **Accepted by all six** (see below) |

## What was run

- Toolchain: Lean 4.36.0, Lake 5.0.0, exporter lean4export 3.1.0 (bundled `leanexport`).
- Configuration: `comparator.json` at the top of the repository (challenge
  `Pilean.Challenge.Erdos`, solution `Pilean.Erdos.Final`, theorem
  `PiFormula.Erdos.erdos_pm_one_nat`, permitted axioms `propext`, `Quot.sound`,
  `Classical.choice`).
- Exports: made on the development machine (Windows) from the build of commit `8545da0`, with
  the argument list that `lake comparator` itself passes to `leanexport` (the theorem, the
  three axioms, `Quot` and its three constants, and the kernel's built-in names):

      lake env leanexport Pilean.Challenge.Erdos -- <targets> > challenge_erdos.ndjson
      lake env leanexport Pilean.Erdos.Final     -- <targets> > solution_erdos.ndjson

  SHA-256: challenge `8040f343e5f76ca65580208d5301bceab65b974f9f998d56c9cc3f4cdc61ad02`
  (32,099,430 bytes), solution `16703a272a854839f4bf2ca1165f44181f890ac5f297eb1bd0b41e675c24cacb`
  (589,342,922 bytes). The files are not in the repository (size); anyone can regenerate them.
- Judge: Ubuntu 26.04.1 (kernel 7.0) in a virtual machine, a fresh clone of the public
  repository at the same commit, with the `bwrap` sandbox active (no
  `--inadvisably-no-sandbox`):

      lake comparator --challenge-from-export challenge_erdos.ndjson \
                      --solution-from-export solution_erdos.ndjson
      lake comparator --paranoid --challenge-from-export ... --solution-from-export ...

## Results

Normal mode (1 min 29 s): "Lean default kernel accepts the solution", "Your solution is okay!",
exit code 0.

Paranoid mode (7 min 1 s), exit code 0, each line as printed:

- Lean paranoid kernel accepts the solution
- lean4lean kernel accepts the solution (checked 73,382 declarations)
- nanoda kernel accepts the solution
- con-leche kernel accepts the solution (accepted 73,381 declarations, `--verified`)
- con-ron kernel accepts the solution (accepted 73,381 declarations, `--verified`)
- Lean default kernel accepts the solution

## What this establishes, and what it does not

Established: the exported proof of `PiFormula.Erdos.erdos_pm_one_nat` has exactly the
statement of the trusted challenge file, uses only the three permitted axioms, and is accepted
by Lean's kernel and by five independent checkers, two of which are themselves formally
verified.

Not established by this run:

- That the exports come from this repository. The tool says so itself for the
  `--*-from-export` options: the build and the export were done outside the sandbox, on the
  development machine. The full pipeline (build and export inside the sandbox from the public
  repository) could not run on the 22 GB judge machine because of the one memory-heavy file.
  Anyone with a larger Linux machine can run plain `lake comparator` in a clone.
- That the statement is the right formalization of the conjecture (test 1 needs human
  readers).
- That the result is new (see `E1_priority_check.md`, `E2_wide_priority_search.md`).

A first attempt with exports made by `leanexport <module> -- <theorem>` alone was rejected
("Const not found in challenge 'semiOutParam'"): the comparator also requires the kernel's
built-in names in the challenge export. The argument list above is the one from the tool's
source (`Lake/CLI/Check.lean`, `compareIt`).
