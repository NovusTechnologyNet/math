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
