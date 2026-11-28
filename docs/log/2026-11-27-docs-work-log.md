# Start a work log in this repository

- Date: 2026-11-27
- Area: `docs/log/`, `PRACTICES.md`, `review/refuted_and_abandoned.md`
- Starting point: `main` at `3a5271c`
- Outcome: worked
- Supersedes: none

## Goal
The repository records what was tried and what failed, with evidence, in a form the next session
or agent will read before it starts. The owner supplied the method: one file per piece of work,
attempts with a verdict and a "Reopen if" condition, three evidence labels, append-only entries
that land with the work. Done when the format is in `docs/log/README.md`, the dead ends that are
likely to be retried have entries, and the practices point to the log. Done by an AI agent
(Claude Fable), at the owner's request.

## Attempts

### 1. Keep the table `review/refuted_and_abandoned.md` as the record
- Tried: considered against the owner's method.
- Result: the table, two days old, has one line per dead end, no evidence label, no condition
  for reopening, and is one shared file that parallel work would conflict over.
- Verdict: abandoned
- Why: [code] the table at `3a5271c` against `docs/log/README.md`.
- Reopen if: never. The table is closed and kept as history, with pointers to the entries.

### 2. A rule against naming an AI as author
- Tried: the draft of the method listed "no AI or assistant attribution" among the things a log
  must not carry. Read against this repository's own rules.
- Result: it does not fit here. This repository says how its work is made: the README states it,
  the commits carry a co-author line, and the statement readings name their AI readers.
- Verdict: abandoned for this repository
- Why: [code] `README.md` ("How this work was made") and `review/statement_readings.md` at
  `3a5271c`. The version of the rules merged here (`9bf12ed`) forbids only what "a rule of this
  repository forbids naming", so there is no conflict left.
- Reopen if: the owner decides otherwise for this repository.

### 3. Give every old dead end an entry
- Tried: considered.
- Result: not done. Seven entries were written after the fact, for the dead ends that someone is
  likely to walk into again; each is marked `Written: 2026-11-27`.
- Verdict: abandoned
- Why: [inferred] an entry reconstructed long after the work has weak evidence; where the command
  was not kept, those seven say [inferred] or cite the file that recorded it.
- Reopen if: an older dead end turns out to be live. Then write its entry.

### 4. The format file, the entries, the pointers
- Tried: `docs/log/README.md` (the owner's template with a section for this repository), seven
  entries, section 4 of `PRACTICES.md`, a row in the README's folder table.
- Result: [measured] `python scripts/check_format.py` at this commit: 276 Lean files, no
  problem; no Lean file changed.
- Verdict: worked

### 5. Push it
- Tried: `git push origin main` with a `docs/log/README.md` written from the draft.
- Expected: a fast-forward.
- Result: refused. The owner's pull request #1 had added `docs/log/README.md` to `main` a few
  minutes earlier (`9bf12ed`, merged as `8c1a9d3`), in a later and fuller wording than the draft.
  [measured] `git fetch origin` and `git diff 3a5271c origin/main --stat`: one file, 65 lines.
- Verdict: failed, then fixed
- Why: [measured] two pieces of work added the same file. The local commit was replayed on top of
  `8c1a9d3`; the merged README is kept word for word and the section "In this repository" is
  appended to it.
- Reopen if: n/a. Fetch before starting work that someone else may be rolling out.

## Result
This commit. Not covered: the rule block for the owner's own agent settings is the owner's to
add; until then `PRACTICES.md`, section 4, carries the rules for anyone working here.

## Lessons
- Write the entry while the work is going on. Four of the seven backfilled entries could label
  their main results [measured] only because the commands were still at hand two days later;
  the other three rest on files that recorded the work.
- Label what an agent reported and nobody reran as [inferred].

## Follow-ups
- Lean pitfalls met in earlier work are known to the sessions that met them and are written
  nowhere in the repository. They should enter the log with the next piece of work in each area,
  not in bulk.
