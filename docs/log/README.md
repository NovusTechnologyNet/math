# Work log

One file per piece of work: what was tried, what happened, how we know, and why. The code is the
result. This folder is how we got there, including the routes that failed.

## Rules

- **Read first.** Search this folder for the area before starting work in it. If an entry says an
  approach failed, do not retry it unless its "Reopen if" condition now holds.
- **Write as you go.** Record each attempt when its result is known, before starting the next.
- **Log every failure**, every choice between real alternatives and every measurement. Typo fixes
  and mechanical changes need no entry.
- **Name the evidence**: [measured] (the command and the commit SHA), [code] (what was read, at
  which SHA) or [inferred] (reasoning). A check that could not tell either way is VOID, not a pass.
- **Append-only.** A correction or a reversal is a new entry with `Supersedes:`. An old entry only
  ever gains a `Superseded-by:` line.
- **Land the entry with the work**, in the same commit or pull request. Abandoned work lands its
  entry on its own, so the failure outlives the branch.
- **Link both ways.** Where code deliberately avoids the obvious approach, its comment names the
  entry. A decision record cites the entry that led to it.
- **Nothing that must not be committed**: no secrets or key material, no host data, nothing a rule
  of this repository forbids naming.

## Naming

`YYYY-MM-DD-<area>-<slug>.md`, for example `2026-11-27-parser-single-pass.md`. Each piece of work
gets its own file, so parallel branches never conflict over a shared log. Find entries with
`git grep -i <term> -- docs/log`, or by area in the file name.

## Template

```markdown
# <What we were trying to do, in one line>

- Date: YYYY-MM-DD
- Area: <crate, subsystem or files>
- Starting point: <branch> at <SHA>
- Outcome: worked | partly | failed | abandoned | open
- Supersedes: <entry, or none>

## Goal
The problem, what "done" looks like, and how we would know it worked.

## Attempts

### 1. <the approach, named>
- Tried: what was done, concretely.
- Expected: what we thought would happen, and why.
- Result: what happened. [measured] `<command>` at `<SHA>`: <figure or output>.
- Verdict: worked | failed | partly | VOID
- Why: the cause, labelled [measured], [code] or [inferred].
- Reopen if: what would make this approach worth trying again. Required for a failure.

### 2. <the next approach>
...

## Result
What landed (commits and pull request), what it measured, and what it does not cover.

## Lessons
What the next person working in this area should know before starting. One line each.

## Follow-ups
Open questions and deferred work.
```

## In this repository

- **Evidence for Lean work.** [measured] is a command run at a commit: `lake build`,
  `#print axioms`, `python scripts/check_format.py`, `lake comparator`, or a program in
  `python/`. A Lean theorem that settles a point is cited by name and file, with the commit at
  which the library builds. [code] is a reading of a named file at a commit. Everything else is
  [inferred], including what an agent reported and nobody reran.
- **Evidence about the literature** keeps its own labels, in `research/`: what was read, what was
  seen only in a search result, what was inferred. The log points there instead of repeating it.
- **Who did the work is said**, an AI agent included. This repository discloses how its work is
  made (`README.md`), and its log does the same.
- **It is a public repository.** No secrets, no personal details, no machine names, addresses or
  local paths.
- **Entries written after the fact** carry a `Written:` line under `Date:`. The log started on
  27 November 2026; older dead ends are in `review/refuted_and_abandoned.md`, and only those that
  someone is likely to try again were given an entry here.
- **Where the rest lives.** What a result says and whether it is new: `review/`. How we check:
  `PRACTICES.md`. The mathematics: `notes/`.
