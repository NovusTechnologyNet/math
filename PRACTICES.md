# How we work: the checks around the proofs

Lean's kernel checks proofs. It does not check that a statement says what we say it says, that
a result is new, or that our prose matches the Lean. The practices below cover those gaps.
Several are modeled on the public rules of the pequalnp.com project (read on 25 November 2026)
and on the four tests in K. Buzzard's post "...and the proof is checked in Lean" (Xena blog,
12 November 2026).

## 1. What "Lean" means in this repository

A result is marked "Lean" only if all of this holds.

- `lake build` passes on the pinned Lean and Mathlib, and `#print axioms` of the theorem shows
  `propext`, `Classical.choice`, `Quot.sound` and nothing else.
- `python scripts/check_format.py` reports no problem. It reads every `.lean` file and refuses
  proof gaps and escape hatches (`sorry`, `native_decide`, `axiom`, `unsafe`, `opaque`, ...),
  anything that runs code while a file compiles or changes how later text is read (`#eval`,
  `macro`, `syntax`, `elab`, `notation`, ...), a missing `module` line, and, in our own files,
  a missing copyright header, a plain `import` or a line over 100 characters. Its one listed
  exception is the challenge file. Run it before every commit that touches a Lean file.
- For a theorem with a challenge file, `scripts/run_comparator.sh` reruns `lake comparator`
  and its paranoid mode in a Linux sandbox. The record
  (`research/2026-11-23-erdos-pm1/04_comparator_record.md`) names the commit that was checked;
  a later commit is not covered until the check is run again.

## 2. A statement is read by someone who did not write it

A machine-checked proof of the wrong statement proves the wrong thing. So each headline
statement gets a reader who has seen neither the proof nor our description of it.

1. `python scripts/statement_view.py OUT.txt Full.Theorem.Name ...` prints the statement and
   every project definition it rests on, as Lean prints them from the compiled library: no
   comments, no docstrings, no proofs.
2. The reader gets that text and Mathlib, nothing else, and writes in plain language what the
   statement says, which conventions matter (division by zero, where indices start, kind of
   convergence), what happens in degenerate cases, and what the statement does not say.
3. We compare the reading with what the README and the notes claim. If they differ, the prose
   is corrected, or the statement is, and the difference is recorded.

The readings are in `review/statement_readings.md`, each with its date and its reader. So far
the readers are AI agents in a fresh session. That removes the author's blind spot; it is not
a specialist's judgment, and the record says which kind of reader it was.

## 3. Is it new?

In this order, before any claim that a result is new.

1. Search the literature: surveys, the papers we build on, the papers that cite them. The
   searches and their dates are kept in `research/`.
2. Ask specialists, in the open. A letter is the repository owner's decision and is written in
   the owner's words; the ledger records whether one was sent.
3. Only then the label "not found in print as far as we can find (searched DATE)".
4. When prior work turns up, credit it at once, with a dated note. The Lean proof stays what it
   is: Lean checked it either way.

`review/novelty.md` is the ledger, one row per result, with one of these labels: *known*;
*stated as known, proof not found in print*; *not found in print (searched DATE)*; *prior work
found (DATE)*; *not searched*. "New" and "first" are not used without the qualifiers.

## 4. Refuted and abandoned

A claim that turned out false, a guess that failed and an approach that cannot work are kept,
with the date and the reason, in `review/refuted_and_abandoned.md`. Where possible the reason
is a Lean theorem. A counterexample has the same standing as a proof.

## 5. Notes and papers

- The README and the notes describe statements that are already checked. Where prose and Lean
  differ, the Lean is right and the prose is corrected.
- When a Lean statement is narrower than, or different from, the classical theorem of the same
  name, the text says so next to the name ("differs from the classical statement: ...").
- Corrections are made in the open: the git history keeps every earlier version.
- A paper is the owner's own text, with the use of AI disclosed.

## 6. Other people's code and results

- Vendored code is scanned before it is compiled, copied unchanged where possible, and its
  source, commit, license and every local change are written down (`lean/TauCeti/VENDORED.md`,
  `lean/Baker/README.md`).
- A known result that we formalize is cited; a published list or formula that we find to be
  wrong is recorded with the evidence, and telling its author is the owner's decision.
