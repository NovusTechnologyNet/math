# Run `lake comparator` on the Erdos theorem so that the verdict counts

- Date: 2026-11-23
- Written: 2026-11-27, from the record and the commits of that day
- Area: `comparator.json`, `lean/Pilean/Challenge/Erdos.lean`, `lean/Pilean/PiFormula/CheckedPair*.lean`
- Starting point: `main` at `3450143`
- Outcome: worked
- Supersedes: none

## Goal
`lake comparator` and its paranoid mode accept `PiFormula.Erdos.erdos_pm_one_nat` against the
challenge file, with the sandbox active and the build done inside it from a fresh clone. Done when
both commands exit 0 on a commit that is on GitHub.

## Attempts

### 1. Run it on the development machine (Windows) with the sandbox switched off
- Tried: `lake comparator` with `--inadvisably-no-sandbox`.
- Expected: a first verdict without setting up Linux.
- Result: not run. The comparator's sandbox is `bwrap`, which is Linux only; a verdict without it
  is not the one the four tests ask for.
- Verdict: abandoned
- Why: [inferred] the flag removes the protection that makes the verdict worth citing.
- Reopen if: never, for a result we mean to cite.

### 2. WSL 1 on the same machine
- Tried: `bwrap` under WSL 1.
- Expected: a Linux userland would be enough.
- Result: `bwrap` cannot start; WSL 1 has no user namespaces (`unshare -U` fails).
- Verdict: failed
- Why: [inferred] from notes kept at the time; the output was not saved.
- Reopen if: the machine runs WSL 2, or any Linux with unprivileged user namespaces.

### 3. A Linux virtual machine, proof exported on Windows
- Tried: `lake env leanexport` on Windows, then `lake comparator --challenge-from-export
  --solution-from-export` in the VM.
- Expected: no build needed in the VM.
- Result: first rejected with "Const not found in challenge 'semiOutParam'". After exporting with
  the comparator's own list of targets (read in `Lake/CLI/Check.lean`: the theorem, the three
  axioms, `Quot` and its constants, and the kernel's primitive names) both modes passed.
  [code] `research/2026-11-23-erdos-pm1/04_comparator_record.md` at `3a5271c`; landed as `8ca40c2`.
- Verdict: partly
- Why: [code] the comparator requires the primitives the kernel treats specially to be present in
  the export; the default export of one theorem leaves them out. It is "partly" because the build
  was not done inside the sandbox.
- Reopen if: a machine cannot build the library; the export route still gives the kernel checks.

### 4. The full pipeline in the VM, build inside the sandbox
- Tried: `lake comparator` from a fresh clone.
- Expected: a slow but complete run.
- Result: the build was killed three times at about 22 GB, in `CheckedPair.lean`.
- Verdict: failed
- Why: [code] header of `lean/scripts/pairgen.py` at `0ed6ebf`: one `decide +kernel` on the whole
  certificate of Theorem J (26,204 nodes); the kernel frees nothing until the declaration ends.
- Reopen if: never as one declaration. See attempt 5.

### 5. Cut the certificate into pieces and take it out of the common imports
- Tried: `pairgen.py` writes 156 closed pieces of at most 250 nodes in six files, each with its
  own `decide +kernel`; the theorems that need the certificate moved to `UnconditionalPair.lean`,
  so the Erdos theorem no longer imports it (`0ed6ebf`).
- Expected: a few GB per file.
- Result: about 4 GB per file. `lake comparator` and `lake comparator --paranoid` both exit 0 from
  a fresh clone at `0ed6ebf`, build inside the sandbox; six kernels accept the proof.
  [code] the record named above; landed as `f9b39dc`.
- Verdict: worked
- Why: [code] each piece is its own declaration, so the kernel returns the memory after each.

## Result
`0ed6ebf` (the split), `f9b39dc` (the record). The check covers `erdos_pm_one_nat` at `0ed6ebf`
only. It does not cover any later commit: the port to the module system (`6460e75`), the Tau Ceti
refresh (`af549c8`), the warning cleanup (`69d6152`) and the headers (`013827a`) came after.

## Lessons
- The comparator needs Linux with unprivileged user namespaces. Check that first.
- A certificate checked by `decide +kernel` must be cut into declarations of bounded size.
- Keep heavy certificate files out of the import cone of the theorems you want to check.
- Read `Lake/CLI/Check.lean` for what the comparator expects before exporting by hand.

## Follow-ups
- Rerun on the current commit with `scripts/run_comparator.sh`; add the result to the record.
- Challenge files for the other headline theorems: their statements use project definitions, so
  each challenge has to restate them.
