# math

Theorems about pi and the primes: written up, machine-checked in Lean, and backed by exact
computer checks. The current subject is BBP-type formulas, the series that give a
hexadecimal digit of pi without computing the digits before it.

## Layout

| Folder | What it holds |
|---|---|
| `notes/` | The mathematics, written up. Start with `pi_formula_theorem.md`. |
| `lean/` | The Lean 4 library, on Mathlib. Every result marked "Lean" below is proved there. |
| `python/` | Exact computer checks, searches and experiments cited in the notes. |
| `engine/` | The fast digit program (Rust and CUDA) that runs the formulas. |
| `research/` | Literature research: what is known, what is open, where results could go. |
| `papers/` | Downloaded papers. Kept on disk only, not in git. |

## Results

The class F is the set of series `sum over k >= 1 of rho(k) 2^(-floor(k/2)) / k` with `rho`
rational and periodic. It contains the original BBP formula, Bellard's formula, Huvent's
formulas and every `P(1, 2^B, n, A)` of Bailey's compendium with `n = B` or `n = 2B`.

| Result | Statement | Status |
|---|---|---|
| Theorem A | Every rational relation between pi and the angles arctan(1/2^m), arctan(1/(2^m - 1)) comes from three classical ones | Lean, unconditional |
| Theorem B | The same for the wider cyclotomic family | Lean, unconditional |
| Theorem C | The formulas for pi in F form a space of dimension exactly 8 (13 for algebraic multiples of pi); every zero relation is known | Lean, from Baker's theorem |
| Theorem D | No formula for pi in F avoids the slowly converging terms | Lean, from Baker's theorem |
| Bailey's table | The number of independent zero relations of `P(1, 2^B, 2B, .)` and `P(1, 2^B, B, .)`, for every B | Lean, from Baker's theorem |
| Theorem E | A formula for pi in F needs at least 2/3 of a term per bit; Huvent's formulas attain it. For a second cost measure the least value is 7/24, attained by a new formula | Lean, from Baker's theorem; the uniqueness statements are not formal |
| Theorem G | log 23 is not the value of any series of F | Lean, from Baker's theorem |
| Theorem H | For a prime p below 100, log p is a value of F exactly for 2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73 | Lean; the fifteen formulas unconditional, the ten exclusions from Baker's theorem |
| Checked pair | The least cost of computing pi with a check by a second formula is 60 terms per 60 bits, attained only by Takahashi's pair | Computed exactly (`python/verify_pair_optimum.py`); not in Lean |
| Theorem F | The other binary families (Part IV of the note) | Written; not formal |

"From Baker's theorem" means that the Lean statement takes Baker's theorem on linear forms
in logarithms (1966) as an explicit hypothesis, `BakerTheorem`. It is a proved theorem, not
a conjecture; it is a hypothesis here because it is not in Mathlib. `lean/README.md` says
what is imported and what is assumed.

## Building and running

- Lean: `lean/README.md`. In short, `lake exe cache get` once, then `lake build`, inside
  `lean/`. Lean 4.36.0, Mathlib v4.36.0.
- Python: Python 3 with `sympy` and `mpmath` (a few scripts need `python-flint`). Run the
  scripts inside `python/`; each one says at the top what it checks.
- Engine: `engine/build.ps1` (Rust; the CUDA toolkit is needed only to rebuild the kernel).

## Other people's code

- `lean/TauCeti/`: 25 modules of the Tau Ceti library (Bang's theorem), Apache License 2.0.
  See `lean/TauCeti/VENDORED.md`.

## Status

A private working repository. No license has been chosen yet for the original work. The
mathematics was worked out with an AI assistant; every Lean proof is checked by Lean's
kernel and depends only on the three standard axioms.
