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
| Theorem C | The formulas for pi in F form a space of dimension exactly 8 (13 for algebraic multiples of pi); every zero relation is known | Lean |
| Theorem D | No formula for pi in F avoids the slowly converging terms | Lean |
| Bailey's table | The number of independent zero relations of `P(1, 2^B, 2B, .)` and `P(1, 2^B, B, .)`, for every B | Lean |
| Theorem E | A formula for pi in F needs at least 2/3 of a term per bit; Huvent's formulas attain it. For a second cost measure the least value is 7/24, attained by a new formula | Lean; the uniqueness statements are not formal |
| Theorem G | log 23 is not the value of any series of F | Lean |
| Theorem H | For a prime p below 100, log p is a value of F exactly for 2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73 | Lean |
| Theorem I | arctan(2/7) is not the value of any series of F (a question left open in Bailey's compendium), nor are arctan(5/8) and arctan(4/9); arctan(2/7) + arctan(6/11) is a value | Lean |
| Theorem J | Computing pi with one formula and checking it with a second costs at least 60 terms per 60 bits; Takahashi's pair attains it. (One formula twice costs at least 80.) | Lean; that his pair is the only one at 60 is computed, not formal |
| Theorem K | The criterion: log y (y rational) is a value of F exactly when a power of y is a product of powers of 2, the numbers 2^m - 1 and the two factors of 4^n + 1 (n odd). For a prime this is a finite test (`python/log_prime_criterion.py`): 51 primes below 10^7. The OEIS list A104885 passes except for 38737 | Lean: the criterion in full, both halves, for every positive rational y (`isFValue_log_rat_iff_pow`), and the finite test for a prime (`isFValue_log_prime_classification`). The list of 51 primes is the test run by a program, not a Lean proof prime by prime |
| Theorem F | The other binary families (Part IV of the note) | Written; not formal |
| Theorem K3 (base 3) | The same criterion in base 3: log y is the value of a series sum rho(k) 3^(-floor(k/2))/k exactly when a power of y is a product of powers of 3, the numbers 3^m - 1 and the two Aurifeuillian factors 3^n -+ 3^((n+1)/2) + 1 (n odd). 31 primes below 10^6 (`python/base3_criterion.py`); only 2, 3, 5, 7, 11, 13 are in print | Lean (`Pilean/Base3`, `isF3Value_log_rat_iff_pow`); the list of primes is computed |
| Theorem C3 (base 3) | pi is not the value of any base-3 series of this class: gamma pi (gamma algebraic) is a value exactly when gamma is a rational multiple of sqrt(3) | Lean, unconditional (`PiFormula.Base3.Unconditional.not_isF3Value_pi`, `isF3Value_mul_pi_iff`). The proof includes a lemma on primes: each Aurifeuillian factor of 3^(3E) + 1 (E odd, at least 3) has a prime factor p with ord_p(3) = 6E (`primitiveHalves3`) |
| Theorem C3 in full (base 3) | Every base-3 series of this class whose value is an algebraic multiple of pi is a G + b Z1 + c Z2, with value a pi sqrt(3): G is the Gregory series and Z1, Z2 are two explicit zero relations. So these series have period 12 and form a space of dimension exactly 3, and the zero relations have dimension exactly 2 | Lean, unconditional (`PiFormula.Base3.Unconditional.theoremC3`, `exists_coords3`, `hasSum_zero_iff`) |
| Base 3, further | Nothing beats the Gregory series (one term per base-3 digit); two formulas attain it | Computed (`python/base3_probe.py`); not proved. Part V of the note |

Theorems C to K, K3 and C3 rest on Baker's theorem on linear forms in logarithms (1966). The library
has each of them in two forms. Our own files prove them from Baker's theorem as an explicit
hypothesis, `BakerTheorem`, because Baker's theorem is not in Mathlib. `lean/Baker/` holds a
formal proof of Baker's theorem by Michail Karatarakis, and
`lean/Pilean/PiFormula/Unconditional.lean` uses it to restate the theorems with no
hypothesis (`PiFormula.Unconditional.*`). Those depend only on Lean's three standard axioms.

## Building and running

- Lean: `lean/README.md`. In short, `lake exe cache get` once, then `lake build`, inside
  `lean/`. Lean 4.36.0, Mathlib v4.36.0.
- Python: Python 3 with `sympy` and `mpmath` (a few scripts need `python-flint`). Run the
  scripts inside `python/`; each one says at the top what it checks.
- Engine: `engine/build.ps1` (Rust; the CUDA toolkit is needed only to rebuild the kernel).

## Other people's code

- `lean/TauCeti/`: 25 modules of the Tau Ceti library (Bang's theorem), Apache License 2.0.
  See `lean/TauCeti/VENDORED.md`.
- `lean/Baker/`: Baker's theorem, 19 files by Michail Karatarakis, Apache License 2.0.
  See `lean/Baker/README.md`.

## Status

A private working repository. No license has been chosen yet for the original work. The
mathematics was worked out with an AI assistant; every Lean proof is checked by Lean's
kernel and depends only on the three standard axioms.
