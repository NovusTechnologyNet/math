# Refresh the vendored Tau Ceti files from upstream

- Date: 2026-11-24
- Written: 2026-11-27, from the commands of that day
- Area: `lean/TauCeti/`
- Starting point: `main` at `6460e75`
- Outcome: worked
- Supersedes: none

## Goal
The 25 vendored modules equal upstream's current ones, the library still builds on Lean 4.36.0
and Mathlib v4.36.0, and the headline theorems keep the three standard axioms.

## Attempts

### 1. Wait for the stable Lean 4.37.0
- Tried: nothing; this was the plan.
- Expected: upstream had moved to Lean v4.37.0-rc1, so its files would not build on v4.36.0.
- Result: the owner asked for the refresh now. Attempt 4 shows the expectation was wrong.
- Verdict: abandoned
- Why: [inferred] a newer toolchain upstream was taken for an incompatibility, untested.
- Reopen if: a refreshed file fails to build on our pinned Mathlib.

### 2. List the changed files with GitHub's compare API
- Tried: `gh api repos/TauCetiProject/TauCeti/compare/b608709...4db9502`.
- Expected: the files changed between the two commits.
- Result: 300 files, with `ahead_by` 3,529; none of our 25 among them.
- Verdict: VOID
- Why: [measured] the API returns at most 300 files, and upstream had about 3,500 commits in
  three days. An empty intersection says nothing.
- Reopen if: never for a comparison this large.

### 3. Compare each file by content hash
- Tried: for each of our 25 paths, `gh api .../contents/<path>?ref=4db9502 --jq .sha` against
  `git rev-parse HEAD:lean/<path>`.
- Expected: an exact answer per file.
- Result: 10 changed, 15 the same, none missing. [measured] at `6460e75`.
- Verdict: partly
- Why: [measured] it compares our list of files, not upstream's import closure. Recomputing the
  closure from the two entry modules gave 25 modules again, but not the same 25:
  `GroupTheory/OrderOfElement/Cauchy.lean` is new, and our `PrimitivePrimeDivisors/Multiplicity.lean`
  is imported by nothing.
- Reopen if: n/a; do both, hash and closure.

### 4. Build the new files in an isolated workspace
- Tried: a git-ignored folder with our `lakefile.toml`, manifest and toolchain, a copy of the
  built Mathlib packages, and the 25 new files. Then
  `LEAN_NUM_THREADS=4 lake build TauCeti.NumberTheory.PrimitivePrimeDivisors.Zsigmondy
  TauCeti.NumberTheory.PrimitivePrimeDivisors.Cyclotomic`.
- Expected: errors from the newer Mathlib that upstream targets.
- Result: 25 modules built, no error, no warning; `#print axioms` of
  `TauCeti.exists_prime_orderOf_two_eq` and `exists_prime_orderOf_eq` gives the three standard
  axioms. [measured] configuration of `6460e75` with upstream's files at `4db9502`.
- Verdict: worked
- Why: [measured] every Mathlib module the new files import exists in Mathlib v4.36.0, and none
  of the seven declarations upstream removed or renamed is used by our library.

### 5. Apply and rebuild everything
- Tried: copy the files in, `git add`, compare the staged blob hashes with upstream's, full build.
- Result: 25 of 25 hashes equal; `LEAN_NUM_THREADS=4 lake build`: 18,797 jobs, 231 modules
  rebuilt, none failed. [measured] at `af549c8`.
- Verdict: worked

## Result
`af549c8`. Not covered: the sandboxed check was not rerun.

## Lessons
- A newer upstream toolchain does not mean the files will not build here. Test in isolation.
- Compare by content hash, and recompute the import closure; a file list goes stale.
- The compare API is useless for a fast-moving repository.
- Scan before compiling: commands that run at build time, `axiom`, `sorry`, `native_decide`,
  hidden control characters.

## Follow-ups
- Refresh again with the upgrade to the stable 4.37.0.
