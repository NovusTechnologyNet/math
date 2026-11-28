# Port the whole library to Lean's module system

- Date: 2026-11-24
- Written: 2026-11-27, from the commit, the agent's report and the checks of that day
- Area: every `.lean` file under `lean/Pilean`, `lean/scripts/`, the generators in `python/`
- Starting point: `main` at `4da27ca`
- Outcome: worked
- Supersedes: none

## Goal
Every `.lean` file is a module (`module`, `public import`, `@[expose] public section`), the
library builds, the statement of `erdos_pm_one_nat` is unchanged, and the axioms stay the three
standard ones. Done by an AI agent (Claude Fable); checked by the main session before the commit.

## Attempts

### 1. Change the header lines only
- Tried: in each file, `module`, every import made `public import`, the body in
  `@[expose] public section`. Import-only files get no section.
- Expected: no proof changes, since everything stays public and exposed.
- Result: 229 of 232 files needed nothing else. [code] the diff of `6460e75`.
- Verdict: partly
- Why: see attempts 2 and 3 for the three that did.

### 2. `namedFam`: a `by` block that used to fill an implicit argument
- Tried: the unchanged definition, in `PiFormula/TheoremC.lean`.
- Result: it no longer elaborates; the argument `q` of `mem_ratSpace_of` has to be given, as
  `(q := 1 / 4)` or `(q := 0)`.
- Verdict: failed, then fixed
- Why: [inferred] from the agent's report: inside the body of an exposed definition a `by` block
  can no longer assign an implicit argument that the surrounding term left open. Not tested apart.
- Reopen if: n/a. Give the argument explicitly.

### 3. `rhoBBP`: an exposed definition that used a private lemma
- Tried: the unchanged definition, in `BaseB/Sharpness.lean`, which used the private `pos4`.
- Result: refused; replaced by an inline proof `(by norm_num : 0 < 4)`.
- Verdict: failed, then fixed
- Why: [inferred] from the agent's report: an exposed body may not refer to a private declaration.
- Reopen if: n/a.

### 4. The fragments in `lean/scripts/`
- Tried: keeping the 16 head and tail pieces of generated files as `*.lean`.
- Result: they are not modules and cannot be: a head has no end, a tail no header.
- Verdict: abandoned
- Why: [inferred] a rule that every `.lean` file is a module cannot hold for a fragment.
  Renamed to `*.lean.in`; the scripts that glue them follow.

### 5. An uncapped build
- Tried: `lake build`, Lake's default number of parallel jobs.
- Result: seven Lean workers at about 4.5 GB each at the same moment, on the certificate files
  of Theorem J. [measured] the process list during the build of `6460e75`.
- Verdict: failed
- Why: [measured] Lake starts as many jobs as there are cores, and the six certificate files
  become ready together.
- Reopen if: the certificate files are made lighter. Until then build with
  `LEAN_NUM_THREADS=4 lake build` (Lake 5.0.0 has no `-j`; this variable caps its job pool).

## Result
`6460e75`. [measured] at that commit: `LEAN_NUM_THREADS=4 lake build --no-build` reports all
18,795 jobs up to date; all 276 `.lean` files start with `module`; `#print axioms` of ten headline
theorems gives the three standard axioms; the statement of `erdos_pm_one_nat` is textually the
same in `Final.lean` and in the challenge file as at `4da27ca`. Not covered: `lake comparator`
was not rerun.

## Lessons
- The port is almost entirely header lines; expect a handful of definitions with proofs inside.
- Cap parallel jobs. The certificate files decide the peak memory, not the rest of the library.
- A generated file needs its generator updated in the same commit, or it stops reproducing.

## Follow-ups
- `VSeries.lean` does not reproduce from `assemble.py`; the agent reports that its head fragment
  already differed before the port. Not looked into.
