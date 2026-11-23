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

## Done (23 November 2026): `π` is not a value, from one hypothesis

`Unconditional.not_isF3Value_pi : PrimitiveHalves3 → ¬ IsF3Value Real.pi`, and
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
  the Aurifeuillian cases, from the hypothesis `PrimitiveHalves3`.
- `PiTheorem.lean`, `Unconditional.lean`: the statements.

No ring `ℤ[ω]` was needed, and no orbit bookkeeping (`Atom`, `base`, `nOf` of base 2): the
reduction lemma replaces it.

## Next: prove `PrimitiveHalves3`

The statement: for odd `E ≥ 3`, each of `L_E = 3^E - 3^((E+1)/2) + 1` and
`M_E = 3^E + 3^((E+1)/2) + 1` has a prime `p` with `ord_p(3) = 6E`.
`python/base3_halves_check.py` checks it for `E ≤ 3001`. It is of the kind proved by Schinzel
(1962); we have not matched it against his statement.

Plan (the analogue of `Lemma2.lean` for base 2).

1. **The halves of `Φ_{6E}(3)`.** With `z = ω t` (so `z² = -3ω²`, `|z|² = 3`):
   `L_E M_E = 3^(2E) - 3^E + 1 = Φ_6(3^E)`, which `Φ_{6E}(3)` divides, so
   `Φ_{6E}(3) = H₁ H₂` with `H₁ ∣ L_E`, `H₂ ∣ M_E`. Concretely `H = |Φ_m(z)|²` for a suitable `m` and the two choices
   `z = ω t`, `z = ω² t`; the identity `Φ_m(ωx) Φ_m(ω²x) = Φ_{3m}(x)` (for `3 ∤ m`) and
   Mathlib's `cyclotomic_expand_eq_cyclotomic(_mul)`, `cyclotomic_two_mul_of_odd` give the
   product.
2. **Möbius product.** `|Φ_m(z)| = ∏_{ab = m} |z^b - 1|^{μ(a)}`, from
   `prod_eq_iff_prod_pow_moebius_eq_of_ne_zero` (as `moebius_formula` in `Lemma2.lean`).
3. **Size.** `|Φ_m(z)|² ≥ s^{2φ(m)} ∏_{b ∣ m} (1 - s^{-b})²` with `s = |z| = √3`; the product
   is bounded below by an absolute constant (about 0.128), so each half exceeds the largest
   prime factor of `6E` once `E` is past a small bound; small `E` by `decide`. A bound
   without Möbius fails only for `E` with very many prime factors, so step 2 is needed for
   all `E`.
4. **Integrality.** `|aeval ω F|²` is an integer for `F ∈ ℤ[X]` (reduce modulo
   `X² + X + 1`).
5. **Conclude.** A prime factor of `Φ_n(3)` that is not of order `n` is the largest prime
   factor of `n` and divides `Φ_n(3)` once (Tau Ceti:
   `le_of_dvd_homogeneousCyclotomic_of_prime_of_dvd`,
   `multiplicity_homogeneousCyclotomic_eq_one`). So a half larger than that prime has a
   prime of order `6E`.

## After that

- **Period 12 and dimension 3.** `support_subset_R03` says the `d_r` vanish outside six roots
  of order dividing 12. State and prove: every series of F3 with value in `ℚ̄ π` has
  period 12, and these series form a space of dimension 3 (linear algebra at period 12, as
  `TheoremC2.lean` and `TheoremC3.lean` but much smaller).
- **The optimum**: 6 terms per period 12, with its two formulas; Bailey's notation
  `P(1, 3^B, n, A)`.
- **The test for a prime in base 3** (as `LogPrimeTest.lean`).
- Base 5 and other bases: the criterion of Theorem K only needs a root of unity `ε` and a
  number `t` in `ℚ(ε)` with `t² = ±b·(unit)`; for which bases this exists, and what replaces
  it otherwise, is not worked out.
