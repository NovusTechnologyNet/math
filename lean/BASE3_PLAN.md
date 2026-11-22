# Base 3: plan for the Lean development

Part V of `notes/pi_formula_theorem.md` gives the mathematics and says what is proved and
what is only computed. This file is the plan for `Pilean/Base3`.

## Done (22 November 2026)

The criterion for logarithms in base 3 (Theorem K3), with no private primes:

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
Eisenstein integers so far: the generators are written with complex norms `‖t3^n - c‖`.

## Next: statement C3 (π in base 3)

Target: every series of F3 whose value is an algebraic multiple of `π` has period 12, these
form a space of dimension 3, and the value is a rational multiple of `π√3`; so `π` is not a
value.

Steps, following Part III for base 2.

1. **Private primes** (the analogue of `Lemma2.lean`, `TheoremB.lean` section 4,
   `GoodPrimes.lean`). For every root of unity `r` outside
   `R0_3 = {1, -1, i, -i, ω, -ω²}`, a prime ideal that contains `t - r` and no other
   `t - r'`. Needs:
   - Zsigmondy for base 3: `Φ_n(3)` has a prime of order `n` for `n ≥ 3`. Tau Ceti's
     `PrimitivePrimeDivisors` is stated for general bases; check that it covers 3.
   - the two Aurifeuillian halves of `Φ_n(3)`, `n ≡ 6 (mod 12)`, `n ≥ 18`, each have a prime
     of order `n`: a size bound (each half exceeds `n`), as `crit` and `size_bound` in
     `Lemma2.lean`, plus small cases by `decide`.
   - a ring for `Z[ω]`: either Mathlib's `Zsqrtd`-style structure does not fit (`ω` is not a
     square root of an integer), so use `ℤ[X]/(X² + X + 1)`, or work in `𝓞 ℚ(ζ₃)` from
     `Mathlib.NumberTheory.Cyclotomic.Three`, or keep everything inside `Aint` (the algebraic
     integers of `ℂ`, already used by `GoodPrimes.lean`) and avoid a named ring. The last
     looks cheapest: `hasGoodPrime_of_dvd` only needs a prime of `Aint` above `p`.
   - the orbits over `ℚ(ω)`: orders `m`, `2m` (`3 ∤ m`, `m` odd) give `Φ_m(±t)`, of norm
     `Φ_{2m}(3)`; orders divisible by 4 and prime to 3 give rational atoms `Φ_n(±3)`; orders
     divisible by 3 give the halves. Write the analogue of `Atom`, `base`, `nOf`.
2. **Support.** A relation `∏ (1 - r/t)^(e_r) = ξ` is supported on `R0_3`
   (as `support_subset_R0'`).
3. **The relations on `R0_3`.** Rank 3, written out; the values of the three relations.
4. **Linear algebra at period 12**: the space of rational `ρ` whose `d_r` lie in the span of
   the relations has dimension 3 and its values are `ℚ π√3` (as `TheoremC2.lean`,
   `TheoremC3.lean`, but 12 instead of 120, so much smaller).
5. Corollaries: `π` is not a value; the optimum (6 terms per period 12) with its two
   formulas; Bailey's notation `P(1, 3^B, n, A)`.

## Later

- The test for a prime in base 3 (as `LogPrimeTest.lean`), after step 1.
- Base 5 and other bases: the criterion of Theorem K only needs a root of unity `ε` and a
  number `t` in `ℚ(ε)` with `t² = ±b·(unit)`; for which bases this exists, and what replaces
  it otherwise, is not worked out.
