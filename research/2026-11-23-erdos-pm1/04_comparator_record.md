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
| 2. The code compiles | Yes, twice: on the development machine, and on a clean Linux machine from a fresh clone of the public repository at commit `0ed6ebf` (full build, 18,795 jobs, 1 min 55 s on 12 cores, peak memory about 10 GB). An earlier attempt at commit `8545da0` failed on one file that needed more than 22 GB; that file was restructured in `0ed6ebf` |
| 3. The code proves the theorem as stated (`lake comparator`) | **Accepted**, with the build and the export done inside the sandbox (second run below); earlier also on exports |
| 4. Independent kernels (`lake comparator --paranoid`) | **Accepted by all six**, in both runs |

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

## Second run: the full pipeline, build inside the sandbox (same day, commit `0ed6ebf`)

After the memory-heavy file was restructured (`0ed6ebf`: its certificate is checked in 156
pieces, largest Lean process about 4 GB, and it is no longer in the import cone of the
theorem), the judge machine could run the tool as intended. In the fresh clone, updated to
`0ed6ebf`, the project's build products were deleted first (`rm -rf .lake/build`; the compiled
Mathlib from `lake exe cache get` was kept), then, with the sandbox active and no export
options:

    lake comparator
    lake comparator --paranoid

- Normal mode (5 min 21 s): the tool built the challenge and the solution inside the sandbox
  ("Build completed successfully (18543 jobs)"), exported them, and printed "Lean default
  kernel accepts the solution", "Your solution is okay!"; exit code 0.
- Paranoid mode (7 min 2 s), exit code 0: Lean paranoid kernel, lean4lean (73,382
  declarations), nanoda, con-leche (73,381 declarations, `--verified`), con-ron (73,381,
  `--verified`) and the Lean default kernel all accept; "Your solution is okay!".
- Then `lake build` of the whole library: "Build completed successfully (18795 jobs)".

This closes the gap of the first run: nothing came from outside the sandbox except the
public repository and the compiled Mathlib cache.

## What this establishes, and what it does not

Established: the exported proof of `PiFormula.Erdos.erdos_pm_one_nat` has exactly the
statement of the trusted challenge file, uses only the three permitted axioms, and is accepted
by Lean's kernel and by five independent checkers, two of which are themselves formally
verified.

Not established by this run:

- (First run only: that the exports came from this repository. The second run removes this
  reservation.) The judge machine is the project's own virtual machine; an independent party
  repeating `lake comparator` in a clone would add to it. The compiled Mathlib was taken from
  the community cache, as in any Mathlib project.
- That the statement is the right formalization of the conjecture (test 1 needs human
  readers).
- That the result is new (see `E1_priority_check.md`, `E2_wide_priority_search.md`).

A first attempt with exports made by `leanexport <module> -- <theorem>` alone was rejected
("Const not found in challenge 'semiOutParam'"): the comparator also requires the kernel's
built-in names in the challenge export. The argument list above is the one from the tool's
source (`Lake/CLI/Check.lean`, `compareIt`).

## Status after 24 November 2026

Everything above was run at commit `0ed6ebf`. On 24 November 2026 the sources changed in four
commits: every file was ported to Lean's module system (`6460e75`), the vendored Tau Ceti files
were refreshed from upstream (`af549c8`), compiler warnings were cleared (`69d6152`), and every
file of the project got a copyright header (`013827a`). The statement of `erdos_pm_one_nat` is
textually unchanged in `Final.lean` and in the challenge file, the library builds, and
`#print axioms` still gives the three standard axioms; but tests 3 and 4 have **not** been rerun
on these commits. `scripts/run_comparator.sh` reruns them on a Linux machine in one command; the
result will be added here.
