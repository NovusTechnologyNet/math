# Base 3: plan for the Lean development

Part V of `notes/pi_formula_theorem.md` gives the mathematics and says what is proved and
what is only computed. This file is the plan for `Pilean/Base3`.

## Done (22 November 2026): the criterion for logarithms

Theorem K3, with no private primes and no hypothesis:

- `Series.lean`: `t3 = √-3`, the class F3, `series_eq_logs3`, `baker_no_extra3`.
- `LogValues.lean`: `log |t^n - c|` (`c^3 = 1`) and `log 3` are values.
- `LogConverse.lean`: the converse, by conjugating a cleared relation (`cleared_conj3`) and
  Möbius inversion (`sum_log_coprime_mem3`).
- `LogExplicit.lean`: the base numbers and `isF3Value_log_rat_iff_pow`.
- `PiSqrt3.lean`: `π√3` is a value.
- `Unconditional.lean`: no hypothesis.

How the port went: the files of base 2 are tied to `tC = 1 + i` and to `GaussianInt`, so they
were copied and adapted rather than generalized. What was reused unchanged: `coeffAt`,
`fourier_inversion`, `rootsN` (`Fourier.lean`); `BakerTheorem`, `baker_descent`, `IntRel`,
`SpanIn` (`Baker.lean`); `aeval_pow_of_coprime`, `sum_filter_coprime`,
`log_identity_of_prod_eq` (`LogConverse.lean`); `nthRoots_repr`, `psum_nthRoots`
(`LogYes.lean`); `log_mem_span_iff_pow` (`LogExplicit.lean`). Base 3 avoids a ring of
Eisenstein integers: the generators are written with complex norms `‖t3^n - c‖`.

## Done (23 November 2026): `π` is not a value

`Unconditional.not_isF3Value_pi : ¬ IsF3Value Real.pi`, with no hypothesis, and
`isF3Value_mul_pi_iff`: for `γ` algebraic, `γ π` is a value exactly when `γ ∈ ℚ√3`.

- `Support.lean`: `IsRelation3`, the six exceptional roots `R03 = {1, -1, i, -i, ω, -ω²}`,
  `HasGoodPrime3`, `GoodPrimes3`, and `support_subset_R03` (a relation among the `1 - r/t`
  has exponent zero outside `R03`).
- `PiValue.lean`: from Baker's theorem and `GoodPrimes3` to the value. Two linear forms
  vanish on every integer relation: a coordinate outside `R03`, and the imaginary part
  `v₀ π + ∑ v_r arg(1 - r/t)`. The six arguments are computed (`theta3_one`, ...), and
  `fourier_pi_combination` shows the resulting coefficient lies in `ℚ√3`.
- `HasPrime.lean`: prime ideals without automorphisms. `HasPrime p x` (a prime ideal of the
  algebraic integers contains `p` and `x`); `hasPrime_conj` (the negation is a polynomial
  identity `U p + V F = 1` at `ζ`, which passes to `ζ^a`); `hasPrime_of_dvd_norm`;
  `goodPrime_of_coset` (the reduction: `E = M / gcd(M, 6)`, a prime `p` dividing
  `|t^E - r^E|²` with `ord_p(3) · h = 2M`, `h ∣ 8`, gives a good prime for `r`).
- `GoodPrimes.lean`: the case analysis by `gcd(M, 6)` and `r^E` (table in the docstring),
  with primes from Tau Ceti's `exists_prime_orderOf_eq` (Zsigmondy for every base) and, for
  the Aurifeuillian cases, from `PrimitiveHalves3`.
- `Halves.lean`: `primitiveHalves3`, the statement `PrimitiveHalves3` as a theorem (for odd
  `E ≥ 3`, each of `3^E ∓ 3^((E+1)/2) + 1` has a prime `p` with `ord_p(3) = 6E`). How it
  went:
  - The ring is Mathlib's `QuadraticAlgebra ℤ (-1) (-1)` (`Eis`), with its multiplicative
    norm and conjugation; `t = 1 + 2ω`. This made the file a close copy of `Lemma2.lean`
    (which uses `GaussianInt`), and no integrality lemma was needed.
  - Write `E = 3^a m`, `3 ∤ m`, `T = t^(3^a)`; the halves are `N(Φ_m(ωT))`, `N(Φ_m(ω²T))`.
  - `moebius_formula3`: `N(Φ_n(z)) = ∏_{ab = n} N(z^b - 1)^{μ(a)}`. It is used twice: for the
    size bound, and to prove `N(Φ_{3m}(x)) = N(Φ_m(ωx)) N(Φ_m(ω²x))`
    (`norm_cyclotomic_mul_three`) without touching roots of unity, from
    `N(x^(3b) - 1) = N(x^b - 1) N((ωx)^b - 1) N((ω²x)^b - 1)` (`norm_twist`).
  - Size (`half_lower`): `9 N(Φ_m(z)) ≥ 3^φ(m)`, uniformly in `a`, by real analysis
    (`(s^b - 1)² ≤ N(z^b - 1) ≤ (s^b + 1)²`, a Weierstrass product bound, and a geometric
    series), instead of the integer criterion plus `decide` of base 2. Comparing with the
    prime factors of `m` needs only `p ≤ φ(m) + 1`, so no lower bound for `φ(m)` in terms
    of `m` is needed.
- `PiTheorem.lean`, `Unconditional.lean`: the statements.

No orbit bookkeeping (`Atom`, `base`, `nOf` of base 2) was needed: the reduction lemma
replaces it. `python/base3_halves_check.py` remains as an independent numerical check of
`primitiveHalves3` (`E ≤ 3001`).

## Done: every formula (period 12, dimension 3)

`Dimension.lean`. `exists_coords3`: a pattern whose series is `γ π` (`γ` algebraic) is
`a rhoGregory + b Z₁ + c Z₂`, and `γ = a √3`. `hasSum_comb3`: the converse, with the value
`a π√3`. `theoremC3`: period 12, dimension exactly 3, zero relations of dimension exactly 2.
`hasSum_zero_iff`: the zero relations are the `b Z₁ + c Z₂`.

How it went, compared with base 2 (`Rank.lean`, `TheoremC2.lean`, `TheoremC3.lean`, about
2000 lines): one file of 1000 lines, because only six roots carry coefficients.

- The relations among the six logarithms are found from their real parts alone: a relation
  becomes `A log 2 + B log 3 + C log(2 + √3) = 0`, and `log_indep` (elementary: irrationality
  of powers of `2 + √3`, and `2^A 3^B = 1`) gives three linear conditions (`intRel_re`). No
  prime ideals are needed at this step.
- The patterns `H` and `F` of the proof are defined by closed formulas in `eisRe`, `eisB`
  (the coordinates of `ω^k`), so that their twisted forms are proved by one symbolic
  computation each (`twist3_rhoH`, `twist3_rhoF`), not by twelve cases. The tables `Z₁`, `Z₂`
  are compared with them by `decide +kernel` on one period (`rhoH_eq`, `rhoF_eq`).
- `hasSum_of_twist3`: a series whose twisted pattern is `∑ e_i r_i^k` has the value
  `-∑ e_i Log(1 - r_i/t)`. With the arguments (`theta3_*`) and norms (`two_ell3_*`) at the
  six roots this gives `S(H) = π√3/3` and `S(F) = 0`.
- `coeffs_spanIn` isolates the use of Baker's theorem (it repeats the first half of
  `pi_multiple_of_goodPrimes3`, which could now be rewritten to call it).

## Done: the optimum

`Optimum.lean`. `theoremE3`: a pattern whose series is a non-zero algebraic multiple of `π`
has at least 6 non-zero entries per period of 12, and exactly 6 only for the multiples of
`rhoGregory` and of `rhoSecond = (0, 18, 18, 18, 0, 0, 0, -18, -18, -18, 0, 0)`. Unlike
base 2 (`FewestTerms.lean`, 5000 lines, uniqueness not formal), this is 300 lines and
includes the uniqueness: the count is written as a sum of indicators of eight linear forms
in `(a, b, c)` (`termCount3_comb3`), the facts about the forms are proved by `linarith`, and
`omega` does the counting.

## Next

- Bailey's notation `P(1, 3^B, n, A)` for the two formulas with 6 terms.
- **The test for a prime in base 3** (as `LogPrimeTest.lean`).
- Base 5 and other bases: the criterion of Theorem K only needs a root of unity `ε` and a
  number `t` in `ℚ(ε)` with `t² = ±b·(unit)`; for which bases this exists, and what replaces
  it otherwise, is not worked out.
