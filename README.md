# math

Theorems about pi and the primes: written up, machine-checked in Lean, and backed by exact
computer checks. The current subject is BBP-type formulas, the series that give a
hexadecimal digit of pi without computing the digits before it.

## Layout

| Folder | What it holds |
|---|---|
| `notes/` | The mathematics, written up. Start with `pi_formula_theorem.md`. |
| `lean/` | The Lean 4 library, on Mathlib. Every result marked "Lean" below is proved there. The package files (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) are at the top level, so Lake commands run from the top folder. |
| `python/` | Exact computer checks, searches and experiments cited in the notes. |
| `engine/` | The fast digit program (Rust and CUDA) that runs the formulas. |
| `research/` | Literature research: what is known, what is open, where results could go. |
| `review/` | The checks around the proofs: independent readings of the statements, the novelty ledger (what is known, what was searched, who was asked), and the record of refuted claims and abandoned approaches. The rules are in `PRACTICES.md`. |
| `scripts/` | Tools: the form check for Lean files, the statement view given to an independent reader, the sandboxed verification. |
| `docs/log/` | The work log: one file per piece of work, with what was tried, what failed, the evidence, and when a dead end is worth trying again. Read it before working in an area. |
| `papers/` | Downloaded papers. Kept on disk only, not in git. |

## Results

The class F is the set of series `sum over k >= 1 of rho(k) 2^(-floor(k/2)) / k` with `rho`
rational and periodic. It contains the original BBP formula, Bellard's formula, Huvent's
formulas and every `P(1, 2^B, n, A)` of Bailey's compendium with `n = B` or `n = 2B`.

| Result | Statement | Status |
|---|---|---|
| Theorem A | Every rational relation between pi and the angles arctan(1/2^m), arctan(1/(2^m - 1)) comes from three classical ones | Lean, unconditional |
| Theorem B | The same for the wider cyclotomic family | Lean, unconditional |
| Theorem C | The series of F whose value is a rational multiple of pi (the multiple 0 included, so the zero relations are counted) form a space of dimension exactly 8 (13 for algebraic multiples of pi), and all have period 120; every zero relation is known | Lean |
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
| Theorem G (every base b >= 5) | A series sum rho(k) b^(-floor(k/2))/k with rho rational and periodic whose value is an algebraic multiple of pi has all coefficients zero, for every integer b >= 5. So pi is not a value, there is no zero relation, a number has at most one formula, and non-zero values are transcendental. A relation exists for b = 2, 3 (Parts III, V) and b = 4 (`RatBase.hasSum_rhoFour`), and for no other base. For a base that is a perfect power this class is smaller than the set of formulas of that base: the Bailey-Borwein-Plouffe formula, of base 16, lies in the class of base 2, not of base 16 | Lean, unconditional (`PiFormula.BaseB.Unconditional.eq_zero_of_hasSum_mul_pi`, `not_isFBValue_pi`, `eq_zero_of_hasSum_zero`, `eq_of_hasSum`, `transcendental_of_hasSum`; `Pilean/BaseB/TheoremG.lean`). Before the proof: computed for b up to 40 (`python/baseb_explore.py`) |
| Theorem L (every integer base) | For an integer base beta with |beta| >= 2: a series sum_j beta^(-Bj) sum_{i=1..N} a_i/(Nj+i) with rational a_i (Bailey's P(1, beta^B, N, a)) that is a non-zero rational multiple of pi exists, for some B and N, if and only if |beta| is a power of 2 (the exponent B is free: the literal bases 2, 4, 8 with B = 1 have none, by computation). In particular there is none in base 10, for any B and N. Degree 1 only: nothing is said about formulas of higher degree, non-integer bases, or other ways of computing digits. In print the statement is given as known (Bailey's Compendium), but the paper cited for it proves the Machin-type case and asks the general question | Lean, unconditional (`PiFormula.BaseB.no_pi_bailey`, `no_pi_bailey_ten`, `no_pi_bailey_26`, `no_pi_bailey_36`, `no_pi_L_comb` (combinations of several series), `bailey_pi_iff`, `bbp_formula`, `no_pi_bailey_int`, `bailey_int_pi_iff`; `Pilean/BaseB/NoPi.lean`, `Sharpness.lean`, `NegativeBase.lean`) |
| Theorem M (the logarithm of the base) | log b has a degree-1 BBP-type formula of base b if and only if b is a power of 2 or of 3. More generally, in a base that is neither, no such series equals q pi + q' log y (q' != 0) when y != 1 is a positive rational whose prime factors all divide the base: log 2, log 5 and log 10 have no formula of base 10 | Lean, unconditional (`PiFormula.BaseB.bailey_log_self_iff`, `no_log_bailey`, `no_log_bailey_ten`; `Pilean/BaseB/LogBase.lean`) |
| Theorem N (no logarithm of an integer) | In a base that is neither a power of 2 nor of 3, no degree-1 BBP-type series equals q pi + q' log n with n >= 2 an integer and q' != 0. So no log n has a degree-1 BBP-type formula of base 10. The proof assigns positive weights to the primes so that every building block of the base has weight zero | Lean, unconditional (`PiFormula.BaseB.no_log_nat_bailey`, `no_log_nat_formula_ten`, `posWeight`, `inBaseSpan_of_isFBValue`; `Pilean/BaseB/LogNat.lean`) |
| Rational bases: Theorem R | For coprime p > q >= 1, call a relation a series sum rho(k) (q/p)^(floor(k/2))/k with rho rational, periodic, not zero, and value an algebraic multiple of pi (0 allowed). **The base p/q has a relation if and only if it is one of 2, 3, 4, 3/2, 4/3.** In every other rational base: pi is not a value, nor any algebraic multiple of pi; no zero relation; at most one formula for a number. Among the five: pi/4 has a formula in base 3/2 (period 24), so "only powers of 2" holds for integer bases, not for rational ones; pi sqrt(3) has formulas in bases 3, 4, 4/3 (the one in base 4/3 is in print in an equivalent form). On paper only: pi itself has a formula in a rational base iff the base is a power of 2 or of 3/2 | Lean, no hypothesis: `PiFormula.RatBase.hasRelation_iff`, `TheoremR.eq_zero_of_hasSum_mul_pi`, `pi_base_three_halves`, `sqrt_three_pi_base_four_thirds`, `hasSum_rhoFour` (`Pilean/RatBase/`). The statement about pi itself: not machine-checked |
| Verification of a paper: Bailey's Compendium of BBP-type formulas (2023 version) | Every claim of the paper is recorded in a ledger (542 entries: 139 formulas, the 41 rows of its Table 1, 284 list entries, 78 assertions in prose). All 138 formulas with numerical content agree to 90 digits. **All 80 formulas of degree 1 are Lean theorems stated as printed** (the 23 with a parameter b for real b in a stated range and for natural b >= 2). Of the 55 formulas of degree 2 and higher, 7 of degree 2 are Lean theorems (29 to 33, 76, 77; for example pi^2 = P(2, 16, 8, (16, -16, -8, -16, -4, -4, 2, 0))), proved on a dilogarithm library written for this (`lean/Pilean/Polylog/`, since Mathlib has no polylogarithms). An eighth Lean statement, the paper's defining series for Catalan's constant, says only that this series converges, because the constant is defined as its sum. The other 47 are checked numerically only. Plan for the rest: `literature/bailey-compendium/DEGREE2_PLAN.md`. Small errors in the paper (a sign, a count, duplicates in a list, references) and one overstated attribution are listed with page numbers | Ledger and checks: `literature/bailey-compendium/`, `python/compendium_check.py`. Lean: `Pilean/Compendium/` (`formula_1`, ..., 104 theorems), status table `literature/bailey-compendium/LEAN_STATUS.md` |
| Erdos's conjecture on sum f(n)/n | Conjecture (Erdos): if q >= 2 and f is periodic mod q with f(n) = +-1 for q not dividing n and f(n) = 0 for q dividing n, then sum f(n)/n is not 0. **Theorem: the conjecture holds for every q that is even, or is not a perfect square, or satisfies q <= 2 phi(q); in particular for every q < 11025.** The case "odd, not a perfect square" is the one not found in print (more generally: f(n) = 0 when q divides n and odd rational values otherwise). Ingredients: Okada's criterion (1982; from Baker's theorem and L(1, chi) != 0), here in both directions, for every q and for rational values: the sum is 0 exactly when two explicit conditions (a), (b) hold; Theorem C, a 2-adic argument: for odd q, (a) and (b) with odd values force q to be a perfect square; the even case (the series diverges); and the size condition (known: Okada; Chatterjee-Murty). Not covered: odd squares with q > 2 phi(q), the first being 11025 = 105^2; for every odd square there is an f with sum 0 whose non-zero values are rationals with odd numerator and odd denominator (also machine-checked: for odd q > 1 such an f exists if and only if q is a perfect square). Its values are not +-1, so this is not a counterexample to the conjecture; it shows that the 2-adic method, which uses only that the values are odd, stops there | **Lean, no hypothesis, standard axioms only** (`lean/Pilean/Erdos/`): `erdos_pm_one_lt_11025`, `erdos_pm_one_of_cases`, `erdos_pm_one_nat` (odd non-square q), `erdos_even_nat`, `erdos_size_nat`, `okadaCriterionGeneral`, `isSquare_of_condA_condB`, `exists_oddValued_sumIsZero_iff`. Baker's theorem enters through the formal proof in `lean/Baker/`. `lake comparator` accepts `erdos_pm_one_nat` against a statement file that uses Mathlib only (`lean/Pilean/Challenge/Erdos.lean`, `comparator.json`), in a Linux sandbox, and in paranoid mode six kernels accept the proof (Lean's two, lean4lean, nanoda, con-leche, con-ron); with the build done inside the sandbox from a fresh clone of this repository at commit `0ed6ebf` (23 November 2026; since then every file was ported to Lean's module system and given a copyright header, and the vendored Tau Ceti files were refreshed, and the check has not been rerun on the new sources yet); record, with what it does and does not establish: `research/2026-11-23-erdos-pm1/04_comparator_record.md`. Paper proof, an independent AI referee report and exact computations: `research/2026-11-23-erdos-pm1/`. **Whether the odd non-square case is new is not settled**: searches found it nowhere in print and the papers that state the status call q = 1 mod 4 open, but a submitted paper by specialists on the conjecture could not be seen. No specialist has read this work. Known before: q prime (Baker-Birch-Wirsing), q = 3 mod 4 (Murty-Saradha 2010), even q, the size conditions |

Theorems C to N, K3, C3, E3, C5 and K5 rest on Baker's theorem on linear forms in logarithms (1966). The library
has each of them in two forms. Our own files prove them from Baker's theorem as an explicit
hypothesis, `BakerTheorem`, because Baker's theorem is not in Mathlib. `lean/Baker/` holds a
formal proof of Baker's theorem by Michail Karatarakis, and
`lean/Pilean/PiFormula/Unconditional.lean` uses it to restate the theorems with no
hypothesis (`PiFormula.Unconditional.*`). Those depend only on Lean's three standard axioms.

## Building and running

- Lean: `lean/README.md`. In short, `lake exe cache get` once, then `lake build`, in the
  top folder of the repository. Lean 4.36.0, Mathlib v4.36.0.
- Python: Python 3 with `sympy` and `mpmath` (a few scripts need `python-flint`). Run the
  scripts inside `python/`; each one says at the top what it checks.
- Engine: `engine/build.ps1` (Rust; the CUDA toolkit is needed only to rebuild the kernel).

## Other people's code

- `lean/TauCeti/`: 25 modules of the Tau Ceti library (Bang's theorem), Apache License 2.0.
  See `lean/TauCeti/VENDORED.md`.
- `lean/Baker/`: Baker's theorem, 19 files by Michail Karatarakis, Apache License 2.0.
  See `lean/Baker/README.md`.

## License

Apache License 2.0: see `LICENSE` and `NOTICE`. Everything here may be used, changed and
passed on by anyone for any purpose, on the terms of that license. That includes moving
lemmas or proofs into Mathlib or any other library: no permission is needed. The two folders
of other people's code above keep their own notices.

## How this work was made

The mathematics, the Lean proofs, the programs and the notes were written by AI models
(Anthropic's Claude, running as coding agents), directed by the owner of this repository,
who chose the questions and the direction of the work. What that means for a reader:

- **Lean.** Every statement marked "Lean" is checked by Lean's kernel, with no `sorry`, no
  `native_decide` and no axioms beyond the three standard ones (`propext`,
  `Classical.choice`, `Quot.sound`). `lake build` in the top folder re-checks all of it. What a
  theorem says is still worth reading with care: the statements and definitions were also
  written by AI.
- **Everything else** (proofs on paper, computations, claims about what is known) is
  labeled as such where it appears and carries no such guarantee.
- **Research reports** in `research/` are summaries written by AI helpers from sources they
  read. They mark what was read and what was inferred, and they can be wrong. "Not found
  in the literature" means that searches found nothing; it is weak evidence of novelty.
- **Statements.** A proof of the wrong statement proves the wrong thing. Headline statements are read by a
  reader who has not seen the proof or our description (`review/statement_readings.md`); so far
  the readers are AI agents, and 56 statements have been read, among them every row of the table
  above (for the Compendium, a sample of nine of its 104 theorems).
- **What is new.** `review/novelty.md` says for each result what the searches found. No specialist
  has been asked yet.
- Nothing here has been peer reviewed. Corrections are welcome: open an issue.

## Using the Lean library

Lean 4.36.0 and Mathlib v4.36.0. To depend on it from another Lake project:

```toml
[[require]]
name = "pilean"
git = "https://github.com/NovusTechnologyNet/math"
rev = "main"
```

The library is one package with three parts: `Pilean` (this project), and the vendored
`TauCeti` and `Baker`. Names and file layout may still change.

Every `.lean` file uses Lean's module system, as Mathlib does: it starts with `module`, and
its declarations are public and exposed, so a file that imports the library can use and
unfold everything as before. Both kinds of project can import it: one that uses modules
(`public import Pilean`) and one that does not (`import Pilean`).
