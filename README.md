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
| Theorem E | A formula for pi in F needs at least 2/3 of a term per bit; Huvent's formulas attain it. For a second cost measure the least value is 7/24, attained by a new formula | Lean; the uniqueness for 2/3 is formal too (`termCount_eq_forty_iff`: only Huvent's two formulas attain it); the uniqueness statement for 7/24 is not formal |
| Theorem G | log 23 is not the value of any series of F | Lean |
| Theorem H | For a prime p below 100, log p is a value of F exactly for 2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73 | Lean |
| Theorem I | arctan(2/7) is not the value of any series of F (a question left open in Bailey's compendium), nor are arctan(5/8) and arctan(4/9); arctan(2/7) + arctan(6/11) is a value | Lean |
| Theorem J | Computing pi with one formula and checking it with a second costs at least 60 terms per 60 bits; Takahashi's pair attains it. (One formula twice costs at least 80.) | Lean; that his pair is the only one at 60 is computed, not formal |
| Theorem K | The criterion: log y (y rational) is a value of F exactly when a power of y is a product of powers of 2, the numbers 2^m - 1 and the two factors of 4^n + 1 (n odd). For a prime this is a finite test (`python/log_prime_criterion.py`): 51 primes below 10^7. The OEIS list A104885 passes except for 38737 | Lean: the criterion in full, both halves, for every positive rational y (`isFValue_log_rat_iff_pow`), and the finite test for a prime (`isFValue_log_prime_classification`). The list of 51 primes is the test run by a program, not a Lean proof prime by prime |
| Theorem F | The other binary families (Part IV of the note). Terms per bit: if sum_j b^(-Bj) sum_{i=1..N} c_i/(Nj+i) = q pi with q a non-zero rational, then b = 2^e and at least (2/3) e B of the c_i are non-zero; so no degree-1 BBP-type formula for pi, in any base b >= 2 and of any length, beats Huvent's 2/3 terms per bit | Sub-series lemma and the terms-per-bit bound: Lean, unconditional (`PiFormula.BaseB.subseries_of_kummerHom`, `terms_per_bit`, `terms_per_bit_attained`). The bound on the prime measure for all steps: written, not formal |
| Theorem K3 (base 3) | The same criterion in base 3: log y is the value of a series sum rho(k) 3^(-floor(k/2))/k exactly when a power of y is a product of powers of 3, the numbers 3^m - 1 and the two Aurifeuillian factors 3^n -+ 3^((n+1)/2) + 1 (n odd). 31 primes below 10^6 (`python/base3_criterion.py`); only 2, 3, 5, 7, 11, 13 are in print | Lean (`Pilean/Base3`, `isF3Value_log_rat_iff_pow`), and the finite test for a prime (`isF3Value_log_prime_iff_explicit`, for every prime other than 3). The list of 31 primes is the test run by a program, not a Lean proof prime by prime |
| Theorem C3 (base 3) | pi is not the value of any base-3 series of this class: gamma pi (gamma algebraic) is a value exactly when gamma is a rational multiple of sqrt(3) | Lean, unconditional (`PiFormula.Base3.Unconditional.not_isF3Value_pi`, `isF3Value_mul_pi_iff`). The proof includes a lemma on primes: each Aurifeuillian factor of 3^(3E) + 1 (E odd, at least 3) has a prime factor p with ord_p(3) = 6E (`primitiveHalves3`) |
| Theorem C3 in full (base 3) | Every base-3 series of this class whose value is an algebraic multiple of pi is a G + b Z1 + c Z2, with value a pi sqrt(3): G is the Gregory series and Z1, Z2 are two explicit zero relations. So these series have period 12 and form a space of dimension exactly 3, and the zero relations have dimension exactly 2 | Lean, unconditional (`PiFormula.Base3.Unconditional.theoremC3`, `exists_coords3`, `hasSum_zero_iff`) |
| Theorem E3 (base 3) | A base-3 series of this class with a non-zero multiple of pi as value needs at least one term per base-3 digit (6 of the 12 entries per period). Exactly two formulas attain this: the Gregory series and pi sqrt(3) = S(0, 18, 18, 18, 0, 0, 0, -18, -18, -18, 0, 0) | Lean, unconditional (`PiFormula.Base3.Unconditional.theoremE3`), including the uniqueness |

| Base 3 in Bailey's notation | The printed identities (the compendium's relations 130 and 131, Adegoke's zero relation, Broadhurst's formula 69) and, for every B, the number of independent zero relations of P(1, 3^B, 2B, .) (2 if 6 divides B, else 0) and of P(1, 3^B, B, .) (0) | Lean (`Pilean/Base3/Bailey.lean`); the counts from Baker's theorem |
| Theorem C5 (base 5) | A base-5 series of this class whose value is an algebraic multiple of pi has all coefficients zero. So pi is not a value, there is no zero relation, and a number has at most one formula | Lean, unconditional (`PiFormula.Base5.Unconditional.eq_zero_of_hasSum_mul_pi`, `not_isF5Value_pi`, `hasSum_zero_iff`, `eq_of_hasSum`). Part VI of the note |
| Theorem K5 (base 5) | For a positive rational y, log y is a value of the base-5 class exactly when a power of y is a product of powers of the numbers (5^m - 1)/5^m and the two normalized Aurifeuillian factors. So log(3/2), log(4/5), log(11/25) are values, and log 5, log 2, log 3 are not | Lean, unconditional (`PiFormula.Base5.Unconditional.isF5Value_log_rat_iff_pow`, `not_isF5Value_log_five`) |
| Values are 0 or transcendental (bases 2, 3, 5) | A value of one of these classes that is an algebraic number is 0; more generally a value alpha + gamma pi with alpha, gamma algebraic has alpha = 0. In base 5 such a value forces all coefficients to be zero. Known in print (Adhikari, Saradha, Shorey, Tijdeman, 2001); here derived from Baker's theorem | Lean (`Pilean/PiFormula/Transcendence.lean`, `Pilean/Base3/Transcendence.lean`, `Pilean/Base5/Transcendence.lean`), from `BakerTheorem` |
| Theorem G (every base b >= 5) | A series sum rho(k) b^(-floor(k/2))/k with rho rational and periodic whose value is an algebraic multiple of pi has all coefficients zero, for every integer b >= 5. So pi is not a value, there is no zero relation, a number has at most one formula, and non-zero values are transcendental. A relation exists for b = 2, 3 (Parts III, V) and b = 4 (computed), and for no other base | Lean, unconditional (`PiFormula.BaseB.Unconditional.eq_zero_of_hasSum_mul_pi`, `not_isFBValue_pi`, `eq_zero_of_hasSum_zero`, `eq_of_hasSum`, `transcendental_of_hasSum`; `Pilean/BaseB/TheoremG.lean`). Before the proof: computed for b up to 40 (`python/baseb_explore.py`) |
| Theorem L (every integer base) | For an integer base beta with |beta| >= 2: a series sum_j beta^(-Bj) sum_{i=1..N} a_i/(Nj+i) with rational a_i (Bailey's P(1, beta^B, N, a)) that is a non-zero rational multiple of pi exists, for some B and N, if and only if |beta| is a power of 2 (the exponent B is free: the literal bases 2, 4, 8 with B = 1 have none, by computation). In particular there is none in base 10, for any B and N. Degree 1 only: nothing is said about formulas of higher degree, non-integer bases, or other ways of computing digits. In print the statement is given as known (Bailey's Compendium), but the paper cited for it proves the Machin-type case and asks the general question | Lean, unconditional (`PiFormula.BaseB.no_pi_bailey`, `no_pi_bailey_ten`, `no_pi_bailey_26`, `no_pi_bailey_36`, `no_pi_L_comb` (combinations of several series), `bailey_pi_iff`, `bbp_formula`, `no_pi_bailey_int`, `bailey_int_pi_iff`; `Pilean/BaseB/NoPi.lean`, `Sharpness.lean`, `NegativeBase.lean`) |
| Theorem M (the logarithm of the base) | log b has a degree-1 BBP-type formula of base b if and only if b is a power of 2 or of 3. More generally, in a base that is neither, no such series equals q pi + q' log y (q' != 0) when y != 1 is a positive rational whose prime factors all divide the base: log 2, log 5 and log 10 have no formula of base 10 | Lean, unconditional (`PiFormula.BaseB.bailey_log_self_iff`, `no_log_bailey`, `no_log_bailey_ten`; `Pilean/BaseB/LogBase.lean`) |
| Rational bases (begun) | A degree-1 formula with rational coefficients for pi in the rational base 3/2: pi/4 = sum rho(k) (2/3)^(floor(k/2))/k with rho of period 24; and one for pi sqrt(3) in base 4/3 (that one is in print in an equivalent form). So "only powers of 2" holds for integer bases, not for rational ones. Which rational bases admit formulas is open (conjecture: 2, 3, 4, 3/2, 4/3 and their powers) | The two formulas: Lean (`PiFormula.RatBase.pi_base_three_halves`, `sqrt_three_pi_base_four_thirds`). The classification: not proved |

Theorems C to M, K3, C3, E3, C5 and K5 rest on Baker's theorem on linear forms in logarithms (1966). The library
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
